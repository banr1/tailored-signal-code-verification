/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPt
public import LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedRepr
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Drop.Unchunked
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Drop Glue for `spqr::v1::chunked::*`

**Checked by Lean.**

Proves subroutine contracts for the five `spqr::v1::chunked` state drop-glue functions:
- `core::ptr::drop_glue::<spqr::v1::chunked::send_ct::Ct2Sampled>` (`0x4c78c`, Block `274`)
- `core::ptr::drop_glue::<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>` (`0x4c7d4`, Block `275`)
- `core::ptr::drop_glue::<spqr::v1::chunked::send_ek::Ct1Received>` (`0x4c8bc`, Block `277`)
- `core::ptr::drop_glue::<spqr::v1::chunked::send_ek::EkSentCt1Received>` (`0x4c92c`, Block `278`)
- `core::ptr::drop_glue::<spqr::v1::chunked::send_ek::HeaderSent>` (`0x4c858`, Block `276`)
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Drop

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L15

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option hygiene false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Representation Predicates and Flat-Offset Deallocation Helpers -/

/-- Byte size of `spqr::v1::chunked::send_ct::Ct2Sampled` (`400 + 56 = 456` bytes). -/
abbrev chunkedCt2SampledSize : Nat := 456
/-- Byte size of `spqr::v1::chunked::send_ct::EkReceivedCt1Sampled` (`400 + 128 = 528` bytes). -/
abbrev chunkedEkReceivedCt1SampledSize : Nat := 528
/-- Byte size of `spqr::v1::chunked::send_ek::Ct1Received` (`400 + 104 = 504` bytes). -/
abbrev chunkedCt1ReceivedSize : Nat := 504
/-- Byte size of `spqr::v1::chunked::send_ek::EkSentCt1Received` (`104 + 400 = 504` bytes). -/
abbrev chunkedEkSentCt1ReceivedSize : Nat := 504
/-- Byte size of `spqr::v1::chunked::send_ek::HeaderSent` (`400 + 80 + 400 = 880` bytes). -/
abbrev chunkedHeaderSentSize : Nat := 880

/-- Stack budget of `drop_glue::<chunked::send_ek::HeaderSent>` (`32` B own frame + `dropStack32`). -/
abbrev dropStackPoly64 : Nat := dropStack32 + 32

theorem stackAt_dropStackPoly64_split (sp : BitVec 64) :
    stackAt sp dropStackPoly64 =
      stackAt (sp - 32#64) dropStack32 ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp dropStack32 4 (by decide)

theorem stackAt_dropStackPoly64_split_bottom (sp : BitVec 64) :
    stackAt sp dropStackPoly64 =
      memRegion (sp - 4160#64) 32 ∗ stackAt sp dropStack32 :=
  stackAt_split_bottom sp dropStack32 32 (by decide)

theorem stack_restore_64_dropStack32 (sp fp lr x20 x19 : BitVec 64) :
    stackAt (sp - 32#64) dropStack32 ∗
      (((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    stackAt sp dropStackPoly64 := by
  rw [stackAt_dropStackPoly64_split sp]
  exact sepConj_mono_right (cells4_sub32_entails sp fp lr x20 x19)

/-- Memory layout of `spqr::v1::chunked::send_ct::Ct2Sampled` (`456` bytes) at `a`:
    - `+0..+400`: `sending_ct2: PolyEncoder`
    - `+400..+456`: `uc: Unchunked.SendCt.Ct2Sent` -/
def chunkedCt2SampledAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) : SepProp :=
  polyEncoderAt A a st.sending_ct2 ∗
    unchunkedCt2SentAt A (a + 400#64) st.uc

/-- Memory layout of `spqr::v1::chunked::send_ct::EkReceivedCt1Sampled` (`528` bytes) at `a`:
    - `+0..+400`: `sending_ct1: PolyEncoder`
    - `+400..+528`: `uc: Unchunked.SendCt.Ct1SentEkReceived` -/
def chunkedEkReceivedCt1SampledAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) : SepProp :=
  polyEncoderAt A a st.sending_ct1 ∗
    unchunkedCt1SentEkReceivedAt A (a + 400#64) st.uc

/-- Memory layout of `spqr::v1::chunked::send_ek::Ct1Received` (`504` bytes) at `a`:
    - `+0..+400`: `sending_ek: PolyEncoder`
    - `+400..+504`: `uc: Unchunked.SendEk.EkSentCt1Received` -/
def chunkedCt1ReceivedAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)) : SepProp :=
  polyEncoderAt A a st.sending_ek ∗
    unchunkedEkSentCt1ReceivedAt A (a + 400#64) st.uc

/-- Memory layout of `spqr::v1::chunked::send_ek::EkSentCt1Received` (`504` bytes) at `a`:
    - `+0..+104`: `uc: Unchunked.SendEk.EkSentCt1Received`
    - `+104..+504`: `receiving_ct2: PolyDecoder` -/
def chunkedEkSentCt1ReceivedAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) : SepProp :=
  unchunkedEkSentCt1ReceivedAt A a st.uc ∗
    polyDecoderAt A (a + 104#64) st.receiving_ct2

/-- Memory layout of `spqr::v1::chunked::send_ek::HeaderSent` (`880` bytes) at `a`:
    - `+0..+400`: `sending_ek: PolyEncoder`
    - `+400..+480`: `uc: Unchunked.SendEk.EkSent`
    - `+480..+880`: `receiving_ct1: PolyDecoder` -/
def chunkedHeaderSentAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) : SepProp :=
  polyEncoderAt A a st.sending_ek ∗
    unchunkedEkSentAt A (a + 400#64) st.uc ∗
    polyDecoderAt A (a + 480#64) st.receiving_ct1

/-- Flat-offset 2-Vec headers at `a + 400#64` (`56` bytes). -/
def twoVec400HeadersAt (a : BitVec 64) (g : TwoVecGhost) : SepProp :=
  ((a + 400#64) ↦₆₄ g.v1.cap) ∗ ((a + 408#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 416#64) 8 ∗
  ((a + 424#64) ↦₆₄ g.v2.cap) ∗ ((a + 432#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 440#64) 16

theorem twoVec56HeadersAt_400_eq (a : BitVec 64) (g : TwoVecGhost) :
    twoVec56HeadersAt (a + 400#64) g = twoVec400HeadersAt a g := by
  unfold twoVec56HeadersAt twoVec400HeadersAt
  have h1 : (a + 400#64) + 8#64 = a + 408#64 := by bv_omega
  have h2 : (a + 400#64) + 16#64 = a + 416#64 := by bv_omega
  have h3 : (a + 400#64) + 24#64 = a + 424#64 := by bv_omega
  have h4 : (a + 400#64) + 32#64 = a + 432#64 := by bv_omega
  have h5 : (a + 400#64) + 40#64 = a + 440#64 := by bv_omega
  simp only [h1, h2, h3, h4, h5]

theorem unchunkedCt2Sent400_entails_dealloc (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)) :
    unchunkedCt2SentAt A (a + 400#64) st ⊢
      ∃∗ g : TwoVecGhost,
        twoVec400HeadersAt a g ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr := by
  refine Entails.trans (unchunkedCt2SentAt_entails_dealloc A (a + 400#64) st) ?_
  apply Entails.sepExists_elim; intro g
  refine Entails.sepExists_right g ?_
  rw [twoVec56HeadersAt_400_eq]
  exact Entails.refl _

theorem twoVec400HeadersAt_entails_memRegion_56 (a : BitVec 64) (g : TwoVecGhost) :
    twoVec400HeadersAt a g ⊢ memRegion (a + 400#64) 56 := by
  rw [← twoVec56HeadersAt_400_eq]
  exact twoVec56HeadersAt_entails_memRegion_56 (a + 400#64) g

/-- Flat-offset 3-Vec headers at `a + 400#64` (`80` bytes). -/
def threeVec400HeadersAt (a : BitVec 64) (g : ThreeVecGhost) : SepProp :=
  ((a + 400#64) ↦₆₄ g.v1.cap) ∗ ((a + 408#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 416#64) 8 ∗
  ((a + 424#64) ↦₆₄ g.v2.cap) ∗ ((a + 432#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 440#64) 8 ∗
  ((a + 448#64) ↦₆₄ g.v3.cap) ∗ ((a + 456#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 464#64) 16

theorem threeVec80HeadersAt_400_eq (a : BitVec 64) (g : ThreeVecGhost) :
    threeVec80HeadersAt (a + 400#64) g = threeVec400HeadersAt a g := by
  unfold threeVec80HeadersAt threeVec400HeadersAt
  have h1 : (a + 400#64) + 8#64 = a + 408#64 := by bv_omega
  have h2 : (a + 400#64) + 16#64 = a + 416#64 := by bv_omega
  have h3 : (a + 400#64) + 24#64 = a + 424#64 := by bv_omega
  have h4 : (a + 400#64) + 32#64 = a + 432#64 := by bv_omega
  have h5 : (a + 400#64) + 40#64 = a + 440#64 := by bv_omega
  have h6 : (a + 400#64) + 48#64 = a + 448#64 := by bv_omega
  have h7 : (a + 400#64) + 56#64 = a + 456#64 := by bv_omega
  have h8 : (a + 400#64) + 64#64 = a + 464#64 := by bv_omega
  simp only [h1, h2, h3, h4, h5, h6, h7, h8]

theorem unchunkedEkSent400_entails_dealloc (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendEk.EkSent (spqrAuthApi F)) :
    unchunkedEkSentAt A (a + 400#64) st ⊢
      ∃∗ g : ThreeVecGhost,
        threeVec400HeadersAt a g ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr := by
  refine Entails.trans (unchunkedEkSentAt_entails_dealloc A (a + 400#64) st) ?_
  apply Entails.sepExists_elim; intro g
  refine Entails.sepExists_right g ?_
  rw [threeVec80HeadersAt_400_eq]
  exact Entails.refl _

theorem threeVec400HeadersAt_entails_memRegion_80 (a : BitVec 64) (g : ThreeVecGhost) :
    threeVec400HeadersAt a g ⊢ memRegion (a + 400#64) 80 := by
  rw [← threeVec80HeadersAt_400_eq]
  exact threeVec80HeadersAt_entails_memRegion_80 (a + 400#64) g

/-- Flat-offset 4-Vec headers at `a + 400#64` (`104` bytes). -/
def fourVec400HeadersAt (a : BitVec 64) (g : FourVecGhost) : SepProp :=
  ((a + 400#64) ↦₆₄ g.v1.cap) ∗ ((a + 408#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 416#64) 8 ∗
  ((a + 424#64) ↦₆₄ g.v2.cap) ∗ ((a + 432#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 440#64) 8 ∗
  ((a + 448#64) ↦₆₄ g.v3.cap) ∗ ((a + 456#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 464#64) 8 ∗
  ((a + 472#64) ↦₆₄ g.v4.cap) ∗ ((a + 480#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 488#64) 16

theorem fourVec104HeadersAt_400_eq (a : BitVec 64) (g : FourVecGhost) :
    fourVec104HeadersAt (a + 400#64) g = fourVec400HeadersAt a g := by
  unfold fourVec104HeadersAt fourVec400HeadersAt
  rw [BitVec.add_assoc a 400#64 8#64, BitVec.add_assoc a 400#64 16#64,
      BitVec.add_assoc a 400#64 24#64, BitVec.add_assoc a 400#64 32#64,
      BitVec.add_assoc a 400#64 40#64, BitVec.add_assoc a 400#64 48#64,
      BitVec.add_assoc a 400#64 56#64, BitVec.add_assoc a 400#64 64#64,
      BitVec.add_assoc a 400#64 72#64, BitVec.add_assoc a 400#64 80#64,
      BitVec.add_assoc a 400#64 88#64]
  rfl

theorem unchunkedEkSentCt1Received400_entails_dealloc (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) :
    unchunkedEkSentCt1ReceivedAt A (a + 400#64) st ⊢
      ∃∗ g : FourVecGhost,
        fourVec400HeadersAt a g ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
        vecCapPtrDealloc A g.v4.cap g.v4.ptr := by
  refine Entails.trans (unchunkedEkSentCt1ReceivedAt_entails_dealloc A (a + 400#64) st) ?_
  apply Entails.sepExists_elim; intro g
  refine Entails.sepExists_right g ?_
  rw [fourVec104HeadersAt_400_eq]
  exact Entails.refl _

theorem fourVec400HeadersAt_entails_memRegion_104 (a : BitVec 64) (g : FourVecGhost) :
    fourVec400HeadersAt a g ⊢ memRegion (a + 400#64) 104 := by
  rw [← fourVec104HeadersAt_400_eq]
  exact fourVec104HeadersAt_entails_memRegion_104 (a + 400#64) g

/-- Flat-offset 5-Vec headers at `a + 400#64` (`128` bytes). -/
def fiveVec400HeadersAt (a : BitVec 64) (g : FiveVecGhost) : SepProp :=
  ((a + 400#64) ↦₆₄ g.v1.cap) ∗ ((a + 408#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 416#64) 8 ∗
  ((a + 424#64) ↦₆₄ g.v2.cap) ∗ ((a + 432#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 440#64) 8 ∗
  ((a + 448#64) ↦₆₄ g.v3.cap) ∗ ((a + 456#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 464#64) 8 ∗
  ((a + 472#64) ↦₆₄ g.v4.cap) ∗ ((a + 480#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 488#64) 8 ∗
  ((a + 496#64) ↦₆₄ g.v5.cap) ∗ ((a + 504#64) ↦₆₄ g.v5.ptr) ∗ memRegion (a + 512#64) 16

theorem fiveVec128HeadersAt_400_eq (a : BitVec 64) (g : FiveVecGhost) :
    fiveVec128HeadersAt (a + 400#64) g = fiveVec400HeadersAt a g := by
  unfold fiveVec128HeadersAt fiveVec400HeadersAt
  rw [BitVec.add_assoc a 400#64 8#64, BitVec.add_assoc a 400#64 16#64,
      BitVec.add_assoc a 400#64 24#64, BitVec.add_assoc a 400#64 32#64,
      BitVec.add_assoc a 400#64 40#64, BitVec.add_assoc a 400#64 48#64,
      BitVec.add_assoc a 400#64 56#64, BitVec.add_assoc a 400#64 64#64,
      BitVec.add_assoc a 400#64 72#64, BitVec.add_assoc a 400#64 80#64,
      BitVec.add_assoc a 400#64 88#64, BitVec.add_assoc a 400#64 96#64,
      BitVec.add_assoc a 400#64 104#64, BitVec.add_assoc a 400#64 112#64]
  rfl

theorem unchunkedCt1SentEkReceived400_entails_dealloc (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)) :
    unchunkedCt1SentEkReceivedAt A (a + 400#64) st ⊢
      ∃∗ g : FiveVecGhost,
        fiveVec400HeadersAt a g ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
        vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
        vecCapPtrDealloc A g.v5.cap g.v5.ptr := by
  refine Entails.trans (unchunkedCt1SentEkReceivedAt_entails_dealloc A (a + 400#64) st) ?_
  apply Entails.sepExists_elim; intro g
  refine Entails.sepExists_right g ?_
  rw [fiveVec128HeadersAt_400_eq]
  exact Entails.refl _

theorem fiveVec400HeadersAt_entails_memRegion_128 (a : BitVec 64) (g : FiveVecGhost) :
    fiveVec400HeadersAt a g ⊢ memRegion (a + 400#64) 128 := by
  rw [← fiveVec128HeadersAt_400_eq]
  exact fiveVec128HeadersAt_entails_memRegion_128 (a + 400#64) g

theorem polyDecoderTail_entails_memRegion_16 (decA : BitVec 64) (ptsNeeded : Nat) (isComplete : Bool) :
    ((decA + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 ptsNeeded) ∗
      ((decA + polyDecoderIsCompleteOff) ↦₈ boolByte isComplete) ∗
      memRegion (decA + polyDecoderPadOff) polyDecoderPadSize ⊢
    memRegion (decA + 384#64) 16 := by
  unfold polyDecoderPtsNeededOff polyDecoderIsCompleteOff polyDecoderPadOff polyDecoderPadSize
  rw [show (384#64 : BitVec 64) = 0x180#64 from rfl,
      ProofLib.memRegion_split' (b := decA + 0x180#64) (n := 8) (k := 8)
        (b' := decA + 0x188#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := decA + 0x188#64) (n := 1) (k := 7)
        (b' := decA + 0x189#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo8_entails_memRegion _ _))

/-- Decompose `polyDecoderAt A decA dec` (`400` bytes) into `vecPtListOf A decA vecs` (`384` bytes)
    and `memRegion (decA + 384#64) 16`. -/
theorem polyDecoderAt_entails_vecs_tail (A : RustAlloc) (decA : BitVec 64) (dec : PolyDecoder) :
    polyDecoderAt A decA dec ⊢
      ∃∗ vecs : List (List Pt),
        ⌜vecs.length = NUM_POLYS⌝ ∗
        vecPtListOf A decA vecs ∗
        memRegion (decA + 384#64) 16 := by
  unfold polyDecoderAt
  rw [sortedSetPtListOf_eq_vecPtListOf]
  refine Entails.sepExists_right (dec.pts.map SortedSetPt.vec) ?_
  refine Entails.pure_left fun ⟨hpts_len, _⟩ => ?_
  have hvecs_len : (dec.pts.map SortedSetPt.vec).length = NUM_POLYS := by simp [hpts_len]
  refine Entails.pure_right hvecs_len ?_
  exact sepConj_mono_right (polyDecoderTail_entails_memRegion_16 decA dec.ptsNeeded dec.isComplete)

theorem polyDecoder_post_join (decA : BitVec 64) :
    memRegion decA polyArrayBytes ∗ memRegion (decA + 384#64) 16 ⊢
    memRegion decA polyDecoderSize := by
  rw [show polyDecoderSize = polyArrayBytes + 16 from rfl,
      ProofLib.memRegion_split decA polyArrayBytes 16 (by decide)]
  exact Entails.refl _

theorem chunked_400_join (a : BitVec 64) (tag : BitVec 64) (k total : Nat)
    (htotal : 400 + k = total) (hbound : total ≤ 2 ^ 64) :
    (a ↦₆₄ tag) ∗ memRegion (a + 8#64) polyArrayBytes ∗ memRegion (a + 392#64) 8 ∗
      memRegion (a + 400#64) k ⊢
    memRegion a total := by
  rw [← htotal, ProofLib.memRegion_split a 400 k (by omega)]
  refine Entails.trans
    (Entails.of_eq (show _ =
      ((a ↦₆₄ tag) ∗ memRegion (a + 8#64) polyArrayBytes ∗ memRegion (a + 392#64) 8) ∗
      memRegion (a + 400#64) k by ac_rfl))
    (sepConj_mono_left (polyEncoder_local2_post_join a tag))

theorem chunked_104_400_join (a : BitVec 64) :
    memRegion a 104 ∗ memRegion (a + 104#64) polyArrayBytes ∗ memRegion (a + 488#64) 16 ⊢
    memRegion a 504 := by
  have h488 : a + 488#64 = (a + 104#64) + 384#64 := by bv_omega
  rw [h488, show (504 : Nat) = 104 + polyDecoderSize from rfl,
      ProofLib.memRegion_split a 104 polyDecoderSize (by decide)]
  exact sepConj_mono_right (polyDecoder_post_join (a + 104#64))

theorem chunked_880_join (a : BitVec 64) :
    memRegion a 480 ∗ memRegion (a + 480#64) polyArrayBytes ∗ memRegion (a + 864#64) 16 ⊢
    memRegion a 880 := by
  have h864 : a + 864#64 = (a + 480#64) + 384#64 := by bv_omega
  rw [h864, show (880 : Nat) = 480 + polyDecoderSize from rfl,
      ProofLib.memRegion_split a 480 polyDecoderSize (by decide)]
  exact sepConj_mono_right (polyDecoder_post_join (a + 480#64))

/-! ## Specifications -/

structure DropChunkedCt2SampledGhost (F : ShaCompress) where
  a : BitVec 64
  st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)

def dropChunkedCt2SampledSpec (A : RustAlloc) (F : ShaCompress) :
    Spec (DropChunkedCt2SampledGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      chunkedCt2SampledAt A x.a x.st ∗
      A.pool ∗ stackAt s.sp dropStack32
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a chunkedCt2SampledSize ∗
      A.pool ∗ stackAt s0.sp dropStack32

structure DropChunkedEkReceivedCt1SampledGhost (F : ShaCompress) where
  a : BitVec 64
  st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)

def dropChunkedEkReceivedCt1SampledSpec (A : RustAlloc) (F : ShaCompress) :
    Spec (DropChunkedEkReceivedCt1SampledGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      chunkedEkReceivedCt1SampledAt A x.a x.st ∗
      A.pool ∗ stackAt s.sp dropStack32
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a chunkedEkReceivedCt1SampledSize ∗
      A.pool ∗ stackAt s0.sp dropStack32

structure DropChunkedCt1ReceivedGhost (F : ShaCompress) where
  a : BitVec 64
  st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)

def dropChunkedCt1ReceivedSpec (A : RustAlloc) (F : ShaCompress) :
    Spec (DropChunkedCt1ReceivedGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      chunkedCt1ReceivedAt A x.a x.st ∗
      A.pool ∗ stackAt s.sp dropStack32
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a chunkedCt1ReceivedSize ∗
      A.pool ∗ stackAt s0.sp dropStack32

structure DropChunkedEkSentCt1ReceivedGhost (F : ShaCompress) where
  a : BitVec 64
  st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)

def dropChunkedEkSentCt1ReceivedSpec (A : RustAlloc) (F : ShaCompress) :
    Spec (DropChunkedEkSentCt1ReceivedGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      chunkedEkSentCt1ReceivedAt A x.a x.st ∗
      A.pool ∗ stackAt s.sp dropStack32
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a chunkedEkSentCt1ReceivedSize ∗
      A.pool ∗ stackAt s0.sp dropStack32

structure DropChunkedHeaderSentGhost (F : ShaCompress) where
  a : BitVec 64
  st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)

def dropChunkedHeaderSentSpec (A : RustAlloc) (F : ShaCompress) :
    Spec (DropChunkedHeaderSentGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      chunkedHeaderSentAt A x.a x.st ∗
      A.pool ∗ stackAt s.sp dropStackPoly64
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a chunkedHeaderSentSize ∗
      A.pool ∗ stackAt s0.sp dropStackPoly64

/-! ## `drop_glue::<chunked::send_ct::Ct2Sampled>` (`0x4c78c`) -/

local macro "chunked_ct2_sampled_steps " prog:term:max entry:term:max : tactic => `(tactic| (
  wp_init x s0; rcases x with ⟨a, st⟩; have hx0 : s0.readReg64 .x0 = a := h
  dsimp only [DropChunkedCt2SampledGhost.a, DropChunkedCt2SampledGhost.st, chunkedCt2SampledAt] at *
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack32_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i fp_old lr_old x19_old w3_old
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (unchunkedCt2Sent400_entails_dealloc A a st.uc))) ?_
  wp_pull_exists; rename_i g
  refine seq_clean (mid := $entry + 36#64)
    (P_mid := (polyEncoderAt A a st.sending_ct2 ∗
      (twoVec400HeadersAt a g ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr)) ∗
      A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
  · dsimp only [twoVec400HeadersAt, vecCapPtrDealloc]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
    · wp_steps; wp_apply; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean (mid := $entry + 56#64)
      (P_mid := (polyEncoderAt A a st.sending_ct2 ∗ memRegion (a + 400#64) 56) ∗
        A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
    · have hstep2 : SepWP $prog ($entry + 56#64) s1
          ((polyEncoderAt A a st.sending_ct2 ∗ (twoVec400HeadersAt a g ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr)) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
          (fun sm Pm =>
            (Pm ⊢ (polyEncoderAt A a st.sending_ct2 ∗ twoVec400HeadersAt a g) ∗
              A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
              (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old))) ∧
            Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) := by
        dsimp only [twoVec400HeadersAt, vecCapPtrDealloc]
        by_cases hc2 : (g.v2.cap == 0#64) = true <;>
          simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
      exact SepWP.strengthen_entails_const
        (sepConj_mono_left (sepConj_mono_right (twoVec400HeadersAt_entails_memRegion_56 a g))) hstep2
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine SepWP.weaken_pre
        (sepConj_mono_left (sepConj_mono_left (polyEncoderAt_entails_tag_vecs_tail A a st.sending_ct2))) ?_
      rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply SepWP.exists_left; intro tag
      rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply SepWP.exists_left; intro vecs
      wp_focus_pure; intro hvecs_len; wp_steps
      refine SepWP.focus_weaken
        (stack_restore_32_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) w3_old)
        (by sep_focus) ?_
      wp_call hpoly16_raw ⟨a + 8#64, vecs⟩
      refine SepWP.weaken_pre
        (Entails.trans
          (Entails.of_eq (show _ = ((a ↦₆₄ tag) ∗ memRegion (a + 8#64) polyArrayBytes ∗
            memRegion (a + 392#64) 8 ∗ memRegion (a + 400#64) 56) ∗
            A.pool ∗ stackAt s0.sp dropGluePoly16Stack by ac_rfl))
          (sepConj_mono_left (chunked_400_join a tag 56 456 rfl (by decide)))) ?_
      wp_done))

theorem drop_chunked_ct2_sampled_ok_ext {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedCt2SampledName)
      (dropChunkedCt2SampledSpec A F) := by
  simp only [dropChunkedCt2SampledSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedCt2SampledName + bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::Ct2Sampled>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::Ct2Sampled>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::Ct2Sampled>") (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have hpoly16_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedCt2SampledName + bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::Ct2Sampled>"))
      (dropGluePoly16Spec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropChunkedCt2SampledName =
        (dropProgAtExt b ext).fnAddr dropPoly16Name + bv% (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::Ct2Sampled>") :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::Ct2Sampled>")) (b := b) (X := Rust.withPanics ext)
        (ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>") (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::Ct2Sampled>") (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_poly16_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches_sym libsignalSessionCode spqrDropChainEpochBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::Ct2Sampled>" 72
  dsimp only [dropProgAtExt, dropChunkedCt2SampledName, chunkedCt2SampledSize,
    BitVec.ofNat_eq_ofNat] at hdealloc_raw hpoly16_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::Ct2Sampled>" = entry
  examples_hide_fetches
  chunked_ct2_sampled_steps (libsignalSessionCode.rebase b (Rust.withPanics ext)) entry

theorem drop_chunked_ct2_sampled_placed_ok [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_274).rebase (blkPl_274).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hpoly16_raw : subroutine_ok ((blkPC_274).rebase (blkPl_274).base H)
      (lsmpl.base 265) (dropGluePoly16Spec A)) :
    subroutine_ok ((blkPC_274).rebase (blkPl_274).base H) (blkPl_274).base
      (dropChunkedCt2SampledSpec A F) := by
  simp only [dropChunkedCt2SampledSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [chunkedCt2SampledSize] at *
  chunked_ct2_sampled_steps ((blkPC_274).rebase (blkPl_274).base H) (blkPl_274).base

/-! ## `drop_glue::<chunked::send_ct::EkReceivedCt1Sampled>` (`0x4c7d4`) -/

local macro "chunked_ek_received_ct1_sampled_steps " prog:term:max entry:term:max : tactic => `(tactic| (
  wp_init x s0; rcases x with ⟨a, st⟩; have hx0 : s0.readReg64 .x0 = a := h
  dsimp only [DropChunkedEkReceivedCt1SampledGhost.a,
    DropChunkedEkReceivedCt1SampledGhost.st, chunkedEkReceivedCt1SampledAt] at *
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack32_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i fp_old lr_old x19_old w3_old
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (unchunkedCt1SentEkReceived400_entails_dealloc A a st.uc))) ?_
  wp_pull_exists; rename_i g
  refine seq_clean (mid := $entry + 36#64)
    (P_mid := (polyEncoderAt A a st.sending_ct1 ∗
      (fiveVec400HeadersAt a g ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
       vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗ vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
       vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
      A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
  · dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
    · wp_steps; wp_apply; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean (mid := $entry + 56#64)
      (P_mid := (polyEncoderAt A a st.sending_ct1 ∗
        (fiveVec400HeadersAt a g ∗ vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
         vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗ vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
        A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
    · dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine seq_clean (mid := $entry + 76#64)
        (P_mid := (polyEncoderAt A a st.sending_ct1 ∗
          (fiveVec400HeadersAt a g ∗ vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
           vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
          A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
      · dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc]
        by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        refine seq_clean (mid := $entry + 96#64)
          (P_mid := (polyEncoderAt A a st.sending_ct1 ∗
            (fiveVec400HeadersAt a g ∗ vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
          (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
        · dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc]
          by_cases hc4 : (g.v4.cap == 0#64) = true <;>
            simp only [hc4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine align_pre (by rw [hsp_3]; ac_rfl) ?_; wp_done
        · intro s4 hpc4 hrun4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩
          refine seq_clean (mid := $entry + 116#64)
            (P_mid := (polyEncoderAt A a st.sending_ct1 ∗ memRegion (a + 400#64) 128) ∗
              A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
              (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
            (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
          · have hstep5 : SepWP $prog ($entry + 116#64) s4
                ((polyEncoderAt A a st.sending_ct1 ∗ (fiveVec400HeadersAt a g ∗ vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
                  A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
                  (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                   ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
                (fun sm Pm =>
                  (Pm ⊢ (polyEncoderAt A a st.sending_ct1 ∗ fiveVec400HeadersAt a g) ∗
                    A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
                    (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                     ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old))) ∧
                  Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) := by
              dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc]
              by_cases hc5 : (g.v5.cap == 0#64) = true <;>
                simp only [hc5, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
              · wp_steps; wp_done
              · wp_steps; wp_apply; refine align_pre (by rw [hsp_4]; ac_rfl) ?_; wp_done
            exact SepWP.strengthen_entails_const
              (sepConj_mono_left (sepConj_mono_right (fiveVec400HeadersAt_entails_memRegion_128 a g))) hstep5
          · intro s5 hpc5 hrun5 ⟨⟨hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩, hx19_5⟩
            refine SepWP.weaken_pre
              (sepConj_mono_left (sepConj_mono_left (polyEncoderAt_entails_tag_vecs_tail A a st.sending_ct1))) ?_
            rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply SepWP.exists_left; intro tag
            rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply SepWP.exists_left; intro vecs
            wp_focus_pure; intro hvecs_len; wp_steps
            refine SepWP.focus_weaken
              (stack_restore_32_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) w3_old)
              (by sep_focus) ?_
            wp_call hpoly16_raw ⟨a + 8#64, vecs⟩
            refine SepWP.weaken_pre
              (Entails.trans
                (Entails.of_eq (show _ = ((a ↦₆₄ tag) ∗ memRegion (a + 8#64) polyArrayBytes ∗
                  memRegion (a + 392#64) 8 ∗ memRegion (a + 400#64) 128) ∗
                  A.pool ∗ stackAt s0.sp dropGluePoly16Stack by ac_rfl))
                (sepConj_mono_left (chunked_400_join a tag 128 528 rfl (by decide)))) ?_
            wp_done))

theorem drop_chunked_ek_received_ct1_sampled_ok_ext {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedEkReceivedCt1SampledName)
      (dropChunkedEkReceivedCt1SampledSpec A F) := by
  simp only [dropChunkedEkReceivedCt1SampledSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedEkReceivedCt1SampledName + bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>") (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have hpoly16_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedEkReceivedCt1SampledName + bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>"))
      (dropGluePoly16Spec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropChunkedEkReceivedCt1SampledName =
        (dropProgAtExt b ext).fnAddr dropPoly16Name + bv% (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>") :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>")) (b := b) (X := Rust.withPanics ext)
        (ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>") (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>") (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_poly16_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches_sym libsignalSessionCode spqrDropChainEpochBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>" 132
  dsimp only [dropProgAtExt, dropChunkedEkReceivedCt1SampledName,
    chunkedEkReceivedCt1SampledSize, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpoly16_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>" = entry
  examples_hide_fetches
  chunked_ek_received_ct1_sampled_steps (libsignalSessionCode.rebase b (Rust.withPanics ext)) entry

theorem drop_chunked_ek_received_ct1_sampled_placed_ok [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_275).rebase (blkPl_275).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hpoly16_raw : subroutine_ok ((blkPC_275).rebase (blkPl_275).base H)
      (lsmpl.base 265) (dropGluePoly16Spec A)) :
    subroutine_ok ((blkPC_275).rebase (blkPl_275).base H) (blkPl_275).base
      (dropChunkedEkReceivedCt1SampledSpec A F) := by
  simp only [dropChunkedEkReceivedCt1SampledSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [chunkedEkReceivedCt1SampledSize] at *
  chunked_ek_received_ct1_sampled_steps ((blkPC_275).rebase (blkPl_275).base H) (blkPl_275).base

/-! ## `drop_glue::<chunked::send_ek::Ct1Received>` (`0x4c8bc`) -/

local macro "chunked_ct1_received_steps " prog:term:max entry:term:max : tactic => `(tactic| (
  wp_init x s0; rcases x with ⟨a, st⟩; have hx0 : s0.readReg64 .x0 = a := h
  dsimp only [DropChunkedCt1ReceivedGhost.a, DropChunkedCt1ReceivedGhost.st, chunkedCt1ReceivedAt] at *
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack32_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i fp_old lr_old x19_old w3_old
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (unchunkedEkSentCt1Received400_entails_dealloc A a st.uc))) ?_
  wp_pull_exists; rename_i g
  refine seq_clean (mid := $entry + 36#64)
    (P_mid := (polyEncoderAt A a st.sending_ek ∗
      (fourVec400HeadersAt a g ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
       vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗ vecCapPtrDealloc A g.v4.cap g.v4.ptr)) ∗
      A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
  · dsimp only [fourVec400HeadersAt, vecCapPtrDealloc]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
    · wp_steps; wp_apply; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean (mid := $entry + 56#64)
      (P_mid := (polyEncoderAt A a st.sending_ek ∗
        (fourVec400HeadersAt a g ∗ vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
         vecCapPtrDealloc A g.v4.cap g.v4.ptr)) ∗
        A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
    · dsimp only [fourVec400HeadersAt, vecCapPtrDealloc]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine seq_clean (mid := $entry + 76#64)
        (P_mid := (polyEncoderAt A a st.sending_ek ∗
          (fourVec400HeadersAt a g ∗ vecCapPtrDealloc A g.v4.cap g.v4.ptr)) ∗
          A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
      · dsimp only [fourVec400HeadersAt, vecCapPtrDealloc]
        by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        refine seq_clean (mid := $entry + 96#64)
          (P_mid := (polyEncoderAt A a st.sending_ek ∗ memRegion (a + 400#64) 104) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
          (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
        · have hstep4 : SepWP $prog ($entry + 96#64) s3
              ((polyEncoderAt A a st.sending_ek ∗ (fourVec400HeadersAt a g ∗ vecCapPtrDealloc A g.v4.cap g.v4.ptr)) ∗
                A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
                (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
              (fun sm Pm =>
                (Pm ⊢ (polyEncoderAt A a st.sending_ek ∗ fourVec400HeadersAt a g) ∗
                  A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
                  (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                   ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old))) ∧
                Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) := by
            dsimp only [fourVec400HeadersAt, vecCapPtrDealloc]
            by_cases hc4 : (g.v4.cap == 0#64) = true <;>
              simp only [hc4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; wp_done
            · wp_steps; wp_apply; refine align_pre (by rw [hsp_3]; ac_rfl) ?_; wp_done
          exact SepWP.strengthen_entails_const
            (sepConj_mono_left (sepConj_mono_right (fourVec400HeadersAt_entails_memRegion_104 a g))) hstep4
        · intro s4 hpc4 hrun4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩
          refine SepWP.weaken_pre
            (sepConj_mono_left (sepConj_mono_left (polyEncoderAt_entails_tag_vecs_tail A a st.sending_ek))) ?_
          rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply SepWP.exists_left; intro tag
          rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply SepWP.exists_left; intro vecs
          wp_focus_pure; intro hvecs_len; wp_steps
          refine SepWP.focus_weaken
            (stack_restore_32_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) w3_old)
            (by sep_focus) ?_
          wp_call hpoly16_raw ⟨a + 8#64, vecs⟩
          refine SepWP.weaken_pre
            (Entails.trans
              (Entails.of_eq (show _ = ((a ↦₆₄ tag) ∗ memRegion (a + 8#64) polyArrayBytes ∗
                memRegion (a + 392#64) 8 ∗ memRegion (a + 400#64) 104) ∗
                A.pool ∗ stackAt s0.sp dropGluePoly16Stack by ac_rfl))
              (sepConj_mono_left (chunked_400_join a tag 104 504 rfl (by decide)))) ?_
          wp_done))

theorem drop_chunked_ct1_received_ok_ext {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedCt1ReceivedName)
      (dropChunkedCt1ReceivedSpec A F) := by
  simp only [dropChunkedCt1ReceivedSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedCt1ReceivedName + bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::Ct1Received>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::Ct1Received>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::Ct1Received>") (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have hpoly16_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedCt1ReceivedName + bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::Ct1Received>"))
      (dropGluePoly16Spec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropChunkedCt1ReceivedName =
        (dropProgAtExt b ext).fnAddr dropPoly16Name + bv% (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::Ct1Received>") :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::Ct1Received>")) (b := b) (X := Rust.withPanics ext)
        (ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>") (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::Ct1Received>") (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_poly16_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches_sym libsignalSessionCode spqrDropChainEpochBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::Ct1Received>" 112
  dsimp only [dropProgAtExt, dropChunkedCt1ReceivedName, chunkedCt1ReceivedSize,
    BitVec.ofNat_eq_ofNat] at hdealloc_raw hpoly16_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::Ct1Received>" = entry
  examples_hide_fetches
  chunked_ct1_received_steps (libsignalSessionCode.rebase b (Rust.withPanics ext)) entry

theorem drop_chunked_ct1_received_placed_ok [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_277).rebase (blkPl_277).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hpoly16_raw : subroutine_ok ((blkPC_277).rebase (blkPl_277).base H)
      (lsmpl.base 265) (dropGluePoly16Spec A)) :
    subroutine_ok ((blkPC_277).rebase (blkPl_277).base H) (blkPl_277).base
      (dropChunkedCt1ReceivedSpec A F) := by
  simp only [dropChunkedCt1ReceivedSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [chunkedCt1ReceivedSize] at *
  chunked_ct1_received_steps ((blkPC_277).rebase (blkPl_277).base H) (blkPl_277).base

/-! ## `drop_glue::<chunked::send_ek::EkSentCt1Received>` (`0x4c92c`) -/

local macro "chunked_ek_sent_ct1_received_steps " prog:term:max entry:term:max : tactic => `(tactic| (
  wp_init x s0; rcases x with ⟨a, st⟩; have hx0 : s0.readReg64 .x0 = a := h
  dsimp only [DropChunkedEkSentCt1ReceivedGhost.a,
    DropChunkedEkSentCt1ReceivedGhost.st, chunkedEkSentCt1ReceivedAt] at *
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack32_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i fp_old lr_old x19_old w3_old
  refine SepWP.weaken_pre
    (sepConj_mono_left (unchunkedEkSentCt1ReceivedAt_entails_dealloc A a st.uc)) ?_
  wp_pull_exists; rename_i g
  refine seq_clean (mid := $entry + 36#64)
    (P_mid := ((fourVec104HeadersAt a g ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
       vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗ vecCapPtrDealloc A g.v4.cap g.v4.ptr) ∗
      polyDecoderAt A (a + 104#64) st.receiving_ct2) ∗
      A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
  · dsimp only [fourVec104HeadersAt, vecCapPtrDealloc]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
    · wp_steps; wp_apply; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean (mid := $entry + 56#64)
      (P_mid := ((fourVec104HeadersAt a g ∗ vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
         vecCapPtrDealloc A g.v4.cap g.v4.ptr) ∗
        polyDecoderAt A (a + 104#64) st.receiving_ct2) ∗
        A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
    · dsimp only [fourVec104HeadersAt, vecCapPtrDealloc]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine seq_clean (mid := $entry + 76#64)
        (P_mid := ((fourVec104HeadersAt a g ∗ vecCapPtrDealloc A g.v4.cap g.v4.ptr) ∗
          polyDecoderAt A (a + 104#64) st.receiving_ct2) ∗
          A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
      · dsimp only [fourVec104HeadersAt, vecCapPtrDealloc]
        by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        refine seq_clean (mid := $entry + 96#64)
          (P_mid := (memRegion a 104 ∗ polyDecoderAt A (a + 104#64) st.receiving_ct2) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
          (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
        · have hstep4 : SepWP $prog ($entry + 96#64) s3
              (((fourVec104HeadersAt a g ∗ vecCapPtrDealloc A g.v4.cap g.v4.ptr) ∗
                polyDecoderAt A (a + 104#64) st.receiving_ct2) ∗
                A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
                (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
              (fun sm Pm =>
                (Pm ⊢ (fourVec104HeadersAt a g ∗ polyDecoderAt A (a + 104#64) st.receiving_ct2) ∗
                  A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
                  (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                   ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old))) ∧
                Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) := by
            dsimp only [fourVec104HeadersAt, vecCapPtrDealloc]
            by_cases hc4 : (g.v4.cap == 0#64) = true <;>
              simp only [hc4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; wp_done
            · wp_steps; wp_apply; refine align_pre (by rw [hsp_3]; ac_rfl) ?_; wp_done
          exact SepWP.strengthen_entails_const
            (sepConj_mono_left (sepConj_mono_left (fourVec104HeadersAt_entails_memRegion_104 a g))) hstep4
        · intro s4 hpc4 hrun4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩
          refine SepWP.weaken_pre
            (sepConj_mono_left (sepConj_mono_right (polyDecoderAt_entails_vecs_tail A (a + 104#64) st.receiving_ct2))) ?_
          rw [sepExists_sepConj_right, sepExists_sepConj_left]; apply SepWP.exists_left; intro vecs
          have h488 : (a + 104#64) + 384#64 = a + 488#64 := by bv_omega
          rw [h488]; wp_focus_pure; intro hvecs_len; wp_steps
          refine SepWP.focus_weaken
            (stack_restore_32_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) w3_old)
            (by sep_focus) ?_
          wp_call hpt16_raw ⟨a + 104#64, vecs⟩
          refine SepWP.weaken_pre
            (Entails.trans
              (Entails.of_eq (show _ = (memRegion a 104 ∗ memRegion (a + 104#64) polyArrayBytes ∗
                memRegion (a + 488#64) 16) ∗ A.pool ∗ stackAt s0.sp dropGluePoly16Stack by ac_rfl))
              (sepConj_mono_left (chunked_104_400_join a))) ?_
          wp_done))

theorem drop_chunked_ek_sent_ct1_received_ok_ext {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedEkSentCt1ReceivedName)
      (dropChunkedEkSentCt1ReceivedSpec A F) := by
  simp only [dropChunkedEkSentCt1ReceivedSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedEkSentCt1ReceivedName + bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::EkSentCt1Received>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::EkSentCt1Received>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::EkSentCt1Received>") (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have hpt16_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedEkSentCt1ReceivedName + bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::EkSentCt1Received>"))
      (dropGlueSortedSetPt16Spec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropChunkedEkSentCt1ReceivedName =
        (dropProgAtExt b ext).fnAddr dropSortedSetPt16Name + bv% (ls_rel% "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::EkSentCt1Received>") :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::EkSentCt1Received>")) (b := b) (X := Rust.withPanics ext)
        (ls_lemma% fnOff "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>") (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::EkSentCt1Received>") (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_sorted_set_pt16_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches_sym libsignalSessionCode spqrDropChainEpochBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::EkSentCt1Received>" 112
  dsimp only [dropProgAtExt, dropChunkedEkSentCt1ReceivedName,
    chunkedEkSentCt1ReceivedSize, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpt16_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::EkSentCt1Received>" = entry
  examples_hide_fetches
  chunked_ek_sent_ct1_received_steps (libsignalSessionCode.rebase b (Rust.withPanics ext)) entry

theorem drop_chunked_ek_sent_ct1_received_placed_ok [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_278).rebase (blkPl_278).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hpt16_raw : subroutine_ok ((blkPC_278).rebase (blkPl_278).base H)
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec A)) :
    subroutine_ok ((blkPC_278).rebase (blkPl_278).base H) (blkPl_278).base
      (dropChunkedEkSentCt1ReceivedSpec A F) := by
  simp only [dropChunkedEkSentCt1ReceivedSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [chunkedEkSentCt1ReceivedSize] at *
  chunked_ek_sent_ct1_received_steps ((blkPC_278).rebase (blkPl_278).base H) (blkPl_278).base

/-! ## `drop_glue::<chunked::send_ek::HeaderSent>` (`0x4c858`) -/

local macro "chunked_header_sent_steps " prog:term:max entry:term:max : tactic => `(tactic| (
  wp_init x s0; rcases x with ⟨a, st⟩; have hx0 : s0.readReg64 .x0 = a := h
  dsimp only [DropChunkedHeaderSentGhost.a, DropChunkedHeaderSentGhost.st, chunkedHeaderSentAt] at *
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  have hsub_4160 : (s0.sp - 32#64) - 4128#64 = s0.sp - 4160#64 := by bv_omega
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]
  nth_rw 1 [stackAt_dropStack32_split_bottom (s0.sp - 32#64)]
  rw [hsub_4160]; cells_unfold; wp_pull_exists; rename_i fp_old lr_old x19_old w3_old
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (unchunkedEkSent400_entails_dealloc A a st.uc))) ?_
  wp_pull_exists; rename_i g
  refine seq_clean (mid := $entry + 36#64)
    (P_mid := (polyEncoderAt A a st.sending_ek ∗
      (threeVec400HeadersAt a g ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
       vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
      polyDecoderAt A (a + 480#64) st.receiving_ct1) ∗ A.pool ∗
      (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
  · dsimp only [threeVec400HeadersAt, vecCapPtrDealloc]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
    · wp_steps; wp_apply; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean (mid := $entry + 56#64)
      (P_mid := (polyEncoderAt A a st.sending_ek ∗
        (threeVec400HeadersAt a g ∗ vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
        polyDecoderAt A (a + 480#64) st.receiving_ct1) ∗ A.pool ∗
        (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
    · dsimp only [threeVec400HeadersAt, vecCapPtrDealloc]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine seq_clean (mid := $entry + 76#64)
        (P_mid := (polyEncoderAt A a st.sending_ek ∗ memRegion (a + 400#64) 80 ∗
          polyDecoderAt A (a + 480#64) st.receiving_ct1) ∗
          A.pool ∗ stackAt (s0.sp - 32#64) dropGluePoly16Stack ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
      · have hstep3 : SepWP $prog ($entry + 76#64) s2
            ((polyEncoderAt A a st.sending_ek ∗ (threeVec400HeadersAt a g ∗ vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
              polyDecoderAt A (a + 480#64) st.receiving_ct1) ∗ A.pool ∗
              (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
              (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
            (fun sm Pm =>
              (Pm ⊢ (polyEncoderAt A a st.sending_ek ∗ threeVec400HeadersAt a g ∗
                polyDecoderAt A (a + 480#64) st.receiving_ct1) ∗ A.pool ∗
                (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
                (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old))) ∧
              Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) := by
          dsimp only [threeVec400HeadersAt, vecCapPtrDealloc]
          by_cases hc3 : (g.v3.cap == 0#64) = true <;>
            simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine align_pre (by rw [hsp_2]; dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
        have hstack_join : memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack ⊢
            stackAt (s0.sp - 32#64) dropGluePoly16Stack := by
          rw [← hsub_4160]; exact Entails.of_eq (stackAt_dropStack32_split_bottom (s0.sp - 32#64)).symm
        exact SepWP.strengthen_entails_const
          (sepConj_mono
            (sepConj_mono_right (sepConj_mono_left (threeVec400HeadersAt_entails_memRegion_80 a g)))
            (sepConj_mono_right (sepConj_mono_left hstack_join))) hstep3
      · intro s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        refine seq_clean (mid := $entry + 84#64)
          (P_mid := (memRegion a 480 ∗ polyDecoderAt A (a + 480#64) st.receiving_ct1) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) dropGluePoly16Stack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
          (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
        · refine SepWP.weaken_pre
            (sepConj_mono_left (sepConj_mono_left (polyEncoderAt_entails_tag_vecs_tail A a st.sending_ek))) ?_
          rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply SepWP.exists_left; intro tag
          rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply SepWP.exists_left; intro vecs
          wp_focus_pure; intro hvecs_len; wp_steps
          wp_call hpoly16_raw ⟨a + 8#64, vecs⟩
          refine SepWP.weaken_pre
            (Entails.trans
              (Entails.of_eq (show _ = (((a ↦₆₄ tag) ∗ memRegion (a + 8#64) polyArrayBytes ∗
                memRegion (a + 392#64) 8 ∗ memRegion (a + 400#64) 80) ∗
                polyDecoderAt A (a + 480#64) st.receiving_ct1) ∗ A.pool ∗
                stackAt (s0.sp - 32#64) dropGluePoly16Stack ∗
                (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)) by
                rw [hsp_3]; ac_rfl))
              (sepConj_mono_left (sepConj_mono_left (chunked_400_join a tag 80 480 rfl (by decide))))) ?_
          wp_done
        · intro s4 hpc4 hrun4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩
          refine SepWP.weaken_pre
            (sepConj_mono_left (sepConj_mono_right (polyDecoderAt_entails_vecs_tail A (a + 480#64) st.receiving_ct1))) ?_
          rw [sepExists_sepConj_right, sepExists_sepConj_left]; apply SepWP.exists_left; intro vecs
          have h864 : (a + 480#64) + 384#64 = a + 864#64 := by bv_omega
          rw [h864]; wp_focus_pure; intro hvecs_len; wp_steps
          refine SepWP.focus_weaken
            (Entails.trans
              (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) w3_old)
              (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)))
            (by sep_focus) ?_
          wp_call hpt16_raw ⟨a + 480#64, vecs⟩
          have hstack64_join : memRegion (s0.sp - 4160#64) 32 ∗ stackAt s0.sp dropGluePoly16Stack ⊢
              stackAt s0.sp dropStackPoly64 :=
            Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm
          refine SepWP.weaken_pre
            (Entails.trans
              (Entails.of_eq (show _ = (memRegion a 480 ∗ memRegion (a + 480#64) polyArrayBytes ∗
                memRegion (a + 864#64) 16) ∗ A.pool ∗
                (memRegion (s0.sp - 4160#64) 32 ∗ stackAt s0.sp dropGluePoly16Stack) by ac_rfl))
              (sepConj_mono (chunked_880_join a) (sepConj_mono_right hstack64_join))) ?_
          wp_done))

theorem drop_chunked_header_sent_ok_ext {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedHeaderSentName)
      (dropChunkedHeaderSentSpec A F) := by
  simp only [dropChunkedHeaderSentSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedHeaderSentName + bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::HeaderSent>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::HeaderSent>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::HeaderSent>") (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have hpoly16_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedHeaderSentName + bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::HeaderSent>"))
      (dropGluePoly16Spec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropChunkedHeaderSentName =
        (dropProgAtExt b ext).fnAddr dropPoly16Name + bv% (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::HeaderSent>") :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::HeaderSent>")) (b := b) (X := Rust.withPanics ext)
        (ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>") (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::HeaderSent>") (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_poly16_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  have hpt16_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedHeaderSentName + bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::HeaderSent>"))
      (dropGlueSortedSetPt16Spec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropChunkedHeaderSentName =
        (dropProgAtExt b ext).fnAddr dropSortedSetPt16Name + bv% (ls_rel% "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::HeaderSent>") :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::HeaderSent>")) (b := b) (X := Rust.withPanics ext)
        (ls_lemma% fnOff "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>") (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::HeaderSent>") (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_sorted_set_pt16_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches_sym libsignalSessionCode spqrDropChainEpochBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::HeaderSent>" 100
  dsimp only [dropProgAtExt, dropChunkedHeaderSentName,
    chunkedHeaderSentSize, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpoly16_raw hpt16_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::HeaderSent>" = entry
  examples_hide_fetches
  chunked_header_sent_steps (libsignalSessionCode.rebase b (Rust.withPanics ext)) entry

theorem drop_chunked_header_sent_placed_ok [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_276).rebase (blkPl_276).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hpoly16_raw : subroutine_ok ((blkPC_276).rebase (blkPl_276).base H)
      (lsmpl.base 265) (dropGluePoly16Spec A))
    (hpt16_raw : subroutine_ok ((blkPC_276).rebase (blkPl_276).base H)
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec A)) :
    subroutine_ok ((blkPC_276).rebase (blkPl_276).base H) (blkPl_276).base
      (dropChunkedHeaderSentSpec A F) := by
  simp only [dropChunkedHeaderSentSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [chunkedHeaderSentSize] at *
  chunked_header_sent_steps ((blkPC_276).rebase (blkPl_276).base H) (blkPl_276).base

end CryptoVerification.SpqrV1.Drop
