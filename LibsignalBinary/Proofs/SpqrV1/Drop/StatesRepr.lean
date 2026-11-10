/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.Chunked
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder

/-!
# Shared Representation Predicates and Helpers for `chunked::states::States`

**Checked by Lean.**

Defines the 928-byte representation predicate `chunkedStatesAt` for
`spqr::v1::chunked::states::States` and flat-offset deallocation/region helpers shared by
`States [local#1]` (`0x35a6c`) and `States [local#2]` (`0x4c5d8`).
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
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## Representation Predicates for `spqr::v1::chunked::states::States` (`928` B) -/

abbrev chunkedStatesSize : Nat := 928

/-- `spqr::v1::unchunked::send_ek::KeysUnsampled` at `a` (`56` bytes = `0x38`):
    - `+0..+48`: `auth: Authenticator`
    - `+48..+56`: `epoch: u64` -/
def unchunkedKeysUnsampledAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendEk.KeysUnsampled (spqrAuthApi F)) : SepProp :=
  authenticatorAt A a st.auth ∗
    ((a + 48#64) ↦₆₄ st.epoch)

/-- `spqr::v1::unchunked::send_ct::NoHeaderReceived` at `a` (`56` bytes = `0x38`):
    - `+0..+48`: `auth: Authenticator`
    - `+48..+56`: `epoch: u64` -/
def unchunkedNoHeaderReceivedAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendCt.NoHeaderReceived (spqrAuthApi F)) : SepProp :=
  authenticatorAt A a st.auth ∗
    ((a + 48#64) ↦₆₄ st.epoch)

/-- `spqr::v1::unchunked::send_ct::HeaderReceived` at `a` (`80` bytes = `0x50`):
    - `+0..+48`: `auth: Authenticator`
    - `+48..+72`: `hdr: Vec<u8>`
    - `+72..+80`: `epoch: u64` -/
def unchunkedHeaderReceivedAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendCt.HeaderReceived (spqrAuthApi F)) : SepProp :=
  authenticatorAt A a st.auth ∗
    vecU8 A (a + 48#64) st.hdr ∗
    ((a + 72#64) ↦₆₄ st.epoch)

/-- `spqr::v1::unchunked::send_ek::HeaderSent` at `a` (`104` bytes = `0x68`):
    - `+0..+48`: `auth: Authenticator`
    - `+48..+72`: `ek: Vec<u8>`
    - `+72..+96`: `dk: Vec<u8>`
    - `+96..+104`: `epoch: u64` -/
def unchunkedHeaderSentAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendEk.HeaderSent (spqrAuthApi F)) : SepProp :=
  authenticatorAt A a st.auth ∗
    vecU8 A (a + 48#64) st.ek ∗
    vecU8 A (a + 72#64) st.dk ∗
    ((a + 96#64) ↦₆₄ st.epoch)

/-- `spqr::v1::chunked::send_ek::KeysUnsampled` at `a` (`56` bytes = `0x38`). -/
def chunkedKeysUnsampledAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) : SepProp :=
  unchunkedKeysUnsampledAt A a st.uc

/-- `spqr::v1::chunked::send_ek::KeysSampled` at `a` (`504` bytes = `0x1f8`):
    - `+0..+400`: `sending_hdr: PolyEncoder`
    - `+400..+504`: `uc: Unchunked.SendEk.HeaderSent` -/
def chunkedKeysSampledAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) : SepProp :=
  polyEncoderAt A a st.sending_hdr ∗
    unchunkedHeaderSentAt A (a + 400#64) st.uc

/-- `spqr::v1::chunked::send_ct::NoHeaderReceived` at `a` (`456` bytes = `0x1c8`):
    - `+0..+56`: `uc: Unchunked.SendCt.NoHeaderReceived`
    - `+56..+456`: `receiving_hdr: PolyDecoder` -/
def chunkedNoHeaderReceivedAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) : SepProp :=
  unchunkedNoHeaderReceivedAt A a st.uc ∗
    polyDecoderAt A (a + 56#64) st.receiving_hdr

/-- `spqr::v1::chunked::send_ct::HeaderReceived` at `a` (`480` bytes = `0x1e0`):
    - `+0..+80`: `uc: Unchunked.SendCt.HeaderReceived`
    - `+80..+480`: `receiving_ek: PolyDecoder` -/
def chunkedHeaderReceivedAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) : SepProp :=
  unchunkedHeaderReceivedAt A a st.uc ∗
    polyDecoderAt A (a + 80#64) st.receiving_ek

/-- `spqr::v1::chunked::send_ct::Ct1Sampled` at `a` (`928` bytes = `0x3a0`):
    - `+0..+400`: `sending_ct1: PolyEncoder` (`EncoderState` tag `0` or `1` at `a + 0`)
    - `+400..+528`: `uc: Unchunked.SendCt.Ct1Sent` (`128`B)
    - `+528..+928`: `receiving_ek: PolyDecoder` (`400`B) -/
def chunkedCt1SampledAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) : SepProp :=
  polyEncoderAt A a st.sending_ct1 ∗
    unchunkedCt1SentAt A (a + 400#64) st.uc ∗
    polyDecoderAt A (a + 528#64) st.receiving_ek

/-- `spqr::v1::chunked::send_ct::Ct1Acknowledged` at `a` (`528` bytes = `0x210`):
    - `+0..+128`: `uc: Unchunked.SendCt.Ct1Sent`
    - `+128..+528`: `receiving_ek: PolyDecoder` -/
def chunkedCt1AcknowledgedAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) : SepProp :=
  unchunkedCt1SentAt A a st.uc ∗
    polyDecoderAt A (a + 128#64) st.receiving_ek

/-- Representation predicate for `spqr::v1::chunked::states::States` (`928` bytes = `0x3a0`, align `8`). -/
def chunkedStatesAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64) :
    States spqrPolyApi (spqrAuthApi F) → SepProp
  | .keysUnsampled s =>
      (a ↦₆₄ 2#64) ∗ chunkedKeysUnsampledAt A (a + 8#64) s ∗ memRegion (a + 64#64) 864
  | .keysSampled s =>
      (a ↦₆₄ 3#64) ∗ chunkedKeysSampledAt A (a + 8#64) s ∗ memRegion (a + 512#64) 416
  | .headerSent s =>
      (a ↦₆₄ 4#64) ∗ chunkedHeaderSentAt A (a + 8#64) s ∗ memRegion (a + 888#64) 40
  | .ct1Received s =>
      (a ↦₆₄ 5#64) ∗ chunkedCt1ReceivedAt A (a + 8#64) s ∗ memRegion (a + 512#64) 416
  | .ekSentCt1Received s =>
      (a ↦₆₄ 6#64) ∗ chunkedEkSentCt1ReceivedAt A (a + 8#64) s ∗ memRegion (a + 512#64) 416
  | .noHeaderReceived s =>
      (a ↦₆₄ 7#64) ∗ chunkedNoHeaderReceivedAt A (a + 8#64) s ∗ memRegion (a + 464#64) 464
  | .headerReceived s =>
      (a ↦₆₄ 8#64) ∗ chunkedHeaderReceivedAt A (a + 8#64) s ∗ memRegion (a + 488#64) 440
  | .ct1Sampled s =>
      chunkedCt1SampledAt A a s
  | .ekReceivedCt1Sampled s =>
      (a ↦₆₄ 10#64) ∗ chunkedEkReceivedCt1SampledAt A (a + 8#64) s ∗ memRegion (a + 536#64) 392
  | .ct1Acknowledged s =>
      (a ↦₆₄ 11#64) ∗ chunkedCt1AcknowledgedAt A (a + 8#64) s ∗ memRegion (a + 536#64) 392
  | .ct2Sampled s =>
      (a ↦₆₄ 12#64) ∗ chunkedCt2SampledAt A (a + 8#64) s ∗ memRegion (a + 464#64) 464

structure DropChunkedStatesGhost (F : ShaCompress) where
  a : BitVec 64
  st : States spqrPolyApi (spqrAuthApi F)

/-! ## Layout Equivalence and Stack/Region Helpers -/

theorem stackAt_dropStack32_split_sub32 (sp : BitVec 64) :
    stackAt (sp - 32#64) dropStack32 =
      memRegion (sp - 4160#64) 32 ∗ stackAt (sp - 32#64) allocHookStack := by
  have h : (sp - 32#64) - 4128#64 = sp - 4160#64 := by bv_omega
  rw [stackAt_dropStack32_split_bottom (sp - 32#64), h]

def unchunkedHeaderSentToEkSentCt1Received {F : ShaCompress}
    (u : Unchunked.SendEk.HeaderSent (spqrAuthApi F)) :
    Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F) :=
  { epoch := u.epoch, auth := u.auth, dk := u.ek, ct1 := u.dk }

def chunkedKeysSampledToCt1Received {F : ShaCompress}
    (s : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) :
    Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F) :=
  { uc := unchunkedHeaderSentToEkSentCt1Received s.uc, sending_ek := s.sending_hdr }

theorem chunkedKeysSampledAt_eq_ct1ReceivedAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (s : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) :
    chunkedKeysSampledAt A a s =
      chunkedCt1ReceivedAt A a (chunkedKeysSampledToCt1Received s) := rfl

theorem unchunkedKeysUnsampledAt_eq_ct2SentAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    unchunkedKeysUnsampledAt A a st =
      unchunkedCt2SentAt A a { epoch := st.epoch, auth := st.auth } := rfl

theorem unchunkedNoHeaderReceivedAt_eq_ct2SentAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendCt.NoHeaderReceived (spqrAuthApi F)) :
    unchunkedNoHeaderReceivedAt A a st =
      unchunkedCt2SentAt A a { epoch := st.epoch, auth := st.auth } := rfl

theorem unchunkedHeaderReceivedAt_eq_ekSentAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendCt.HeaderReceived (spqrAuthApi F)) :
    unchunkedHeaderReceivedAt A a st =
      unchunkedEkSentAt A a { epoch := st.epoch, auth := st.auth, dk := st.hdr } := rfl

/-! ## Flat-Offset Deallocation Helpers (`+8` and `+408`) -/

/-- Flat-offset 2-Vec headers at `a + 8#64` (`56` bytes). -/
def twoVec8HeadersAt (a : BitVec 64) (g : TwoVecGhost) : SepProp :=
  ((a + 8#64) ↦₆₄ g.v1.cap) ∗ ((a + 16#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 24#64) 8 ∗
  ((a + 32#64) ↦₆₄ g.v2.cap) ∗ ((a + 40#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 48#64) 16

theorem twoVec56HeadersAt_8_eq (a : BitVec 64) (g : TwoVecGhost) :
    twoVec56HeadersAt (a + 8#64) g = twoVec8HeadersAt a g := by
  unfold twoVec56HeadersAt twoVec8HeadersAt
  rw [BitVec.add_assoc a 8#64 8#64, BitVec.add_assoc a 8#64 16#64,
      BitVec.add_assoc a 8#64 24#64, BitVec.add_assoc a 8#64 32#64,
      BitVec.add_assoc a 8#64 40#64]
  rfl

theorem unchunkedCt2Sent8_entails_dealloc (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)) :
    unchunkedCt2SentAt A (a + 8#64) st ⊢
      ∃∗ g : TwoVecGhost,
        twoVec8HeadersAt a g ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr := by
  refine Entails.trans (unchunkedCt2SentAt_entails_dealloc A (a + 8#64) st) ?_
  apply Entails.sepExists_elim; intro g
  refine Entails.sepExists_right g ?_
  rw [twoVec56HeadersAt_8_eq]
  exact Entails.refl _

theorem twoVec8HeadersAt_entails_memRegion_56 (a : BitVec 64) (g : TwoVecGhost) :
    twoVec8HeadersAt a g ⊢ memRegion (a + 8#64) 56 := by
  rw [← twoVec56HeadersAt_8_eq]
  exact twoVec56HeadersAt_entails_memRegion_56 (a + 8#64) g

/-- Flat-offset 2-Vec headers at `a + 408#64` (`56` bytes). -/
def twoVec408HeadersAt (a : BitVec 64) (g : TwoVecGhost) : SepProp :=
  ((a + 408#64) ↦₆₄ g.v1.cap) ∗ ((a + 416#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 424#64) 8 ∗
  ((a + 432#64) ↦₆₄ g.v2.cap) ∗ ((a + 440#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 448#64) 16

theorem twoVec56HeadersAt_408_eq (a : BitVec 64) (g : TwoVecGhost) :
    twoVec56HeadersAt (a + 408#64) g = twoVec408HeadersAt a g := by
  unfold twoVec56HeadersAt twoVec408HeadersAt
  rw [BitVec.add_assoc a 408#64 8#64, BitVec.add_assoc a 408#64 16#64,
      BitVec.add_assoc a 408#64 24#64, BitVec.add_assoc a 408#64 32#64,
      BitVec.add_assoc a 408#64 40#64]
  rfl

theorem unchunkedCt2Sent408_entails_dealloc (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)) :
    unchunkedCt2SentAt A (a + 408#64) st ⊢
      ∃∗ g : TwoVecGhost,
        twoVec408HeadersAt a g ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr := by
  refine Entails.trans (unchunkedCt2SentAt_entails_dealloc A (a + 408#64) st) ?_
  apply Entails.sepExists_elim; intro g
  refine Entails.sepExists_right g ?_
  rw [twoVec56HeadersAt_408_eq]
  exact Entails.refl _

theorem twoVec408HeadersAt_entails_memRegion_56 (a : BitVec 64) (g : TwoVecGhost) :
    twoVec408HeadersAt a g ⊢ memRegion (a + 408#64) 56 := by
  rw [← twoVec56HeadersAt_408_eq]
  exact twoVec56HeadersAt_entails_memRegion_56 (a + 408#64) g

/-- Flat-offset 3-Vec headers at `a + 8#64` (`80` bytes). -/
def threeVec8HeadersAt (a : BitVec 64) (g : ThreeVecGhost) : SepProp :=
  ((a + 8#64) ↦₆₄ g.v1.cap) ∗ ((a + 16#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 24#64) 8 ∗
  ((a + 32#64) ↦₆₄ g.v2.cap) ∗ ((a + 40#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 48#64) 8 ∗
  ((a + 56#64) ↦₆₄ g.v3.cap) ∗ ((a + 64#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 72#64) 16

theorem threeVec80HeadersAt_8_eq (a : BitVec 64) (g : ThreeVecGhost) :
    threeVec80HeadersAt (a + 8#64) g = threeVec8HeadersAt a g := by
  unfold threeVec80HeadersAt threeVec8HeadersAt
  rw [BitVec.add_assoc a 8#64 8#64, BitVec.add_assoc a 8#64 16#64,
      BitVec.add_assoc a 8#64 24#64, BitVec.add_assoc a 8#64 32#64,
      BitVec.add_assoc a 8#64 40#64, BitVec.add_assoc a 8#64 48#64,
      BitVec.add_assoc a 8#64 56#64, BitVec.add_assoc a 8#64 64#64]
  rfl

theorem unchunkedEkSent8_entails_dealloc (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendEk.EkSent (spqrAuthApi F)) :
    unchunkedEkSentAt A (a + 8#64) st ⊢
      ∃∗ g : ThreeVecGhost,
        threeVec8HeadersAt a g ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr := by
  refine Entails.trans (unchunkedEkSentAt_entails_dealloc A (a + 8#64) st) ?_
  apply Entails.sepExists_elim; intro g
  refine Entails.sepExists_right g ?_
  rw [threeVec80HeadersAt_8_eq]
  exact Entails.refl _

theorem threeVec8HeadersAt_entails_memRegion_80 (a : BitVec 64) (g : ThreeVecGhost) :
    threeVec8HeadersAt a g ⊢ memRegion (a + 8#64) 80 := by
  rw [← threeVec80HeadersAt_8_eq]
  exact threeVec80HeadersAt_entails_memRegion_80 (a + 8#64) g

/-- Flat-offset 3-Vec headers at `a + 408#64` (`80` bytes). -/
def threeVec408HeadersAt (a : BitVec 64) (g : ThreeVecGhost) : SepProp :=
  ((a + 408#64) ↦₆₄ g.v1.cap) ∗ ((a + 416#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 424#64) 8 ∗
  ((a + 432#64) ↦₆₄ g.v2.cap) ∗ ((a + 440#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 448#64) 8 ∗
  ((a + 456#64) ↦₆₄ g.v3.cap) ∗ ((a + 464#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 472#64) 16

theorem threeVec80HeadersAt_408_eq (a : BitVec 64) (g : ThreeVecGhost) :
    threeVec80HeadersAt (a + 408#64) g = threeVec408HeadersAt a g := by
  unfold threeVec80HeadersAt threeVec408HeadersAt
  rw [BitVec.add_assoc a 408#64 8#64, BitVec.add_assoc a 408#64 16#64,
      BitVec.add_assoc a 408#64 24#64, BitVec.add_assoc a 408#64 32#64,
      BitVec.add_assoc a 408#64 40#64, BitVec.add_assoc a 408#64 48#64,
      BitVec.add_assoc a 408#64 56#64, BitVec.add_assoc a 408#64 64#64]
  rfl

theorem unchunkedEkSent408_entails_dealloc (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendEk.EkSent (spqrAuthApi F)) :
    unchunkedEkSentAt A (a + 408#64) st ⊢
      ∃∗ g : ThreeVecGhost,
        threeVec408HeadersAt a g ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr := by
  refine Entails.trans (unchunkedEkSentAt_entails_dealloc A (a + 408#64) st) ?_
  apply Entails.sepExists_elim; intro g
  refine Entails.sepExists_right g ?_
  rw [threeVec80HeadersAt_408_eq]
  exact Entails.refl _

theorem threeVec408HeadersAt_entails_memRegion_80 (a : BitVec 64) (g : ThreeVecGhost) :
    threeVec408HeadersAt a g ⊢ memRegion (a + 408#64) 80 := by
  rw [← threeVec80HeadersAt_408_eq]
  exact threeVec80HeadersAt_entails_memRegion_80 (a + 408#64) g

/-- Flat-offset 4-Vec headers at `a + 8#64` (`104` bytes). -/
def fourVec8HeadersAt (a : BitVec 64) (g : FourVecGhost) : SepProp :=
  ((a + 8#64) ↦₆₄ g.v1.cap) ∗ ((a + 16#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 24#64) 8 ∗
  ((a + 32#64) ↦₆₄ g.v2.cap) ∗ ((a + 40#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 48#64) 8 ∗
  ((a + 56#64) ↦₆₄ g.v3.cap) ∗ ((a + 64#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 72#64) 8 ∗
  ((a + 80#64) ↦₆₄ g.v4.cap) ∗ ((a + 88#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 96#64) 16

theorem fourVec104HeadersAt_8_eq (a : BitVec 64) (g : FourVecGhost) :
    fourVec104HeadersAt (a + 8#64) g = fourVec8HeadersAt a g := by
  unfold fourVec104HeadersAt fourVec8HeadersAt
  rw [BitVec.add_assoc a 8#64 8#64, BitVec.add_assoc a 8#64 16#64,
      BitVec.add_assoc a 8#64 24#64, BitVec.add_assoc a 8#64 32#64,
      BitVec.add_assoc a 8#64 40#64, BitVec.add_assoc a 8#64 48#64,
      BitVec.add_assoc a 8#64 56#64, BitVec.add_assoc a 8#64 64#64,
      BitVec.add_assoc a 8#64 72#64, BitVec.add_assoc a 8#64 80#64,
      BitVec.add_assoc a 8#64 88#64]
  rfl

theorem unchunkedEkSentCt1Received8_entails_dealloc (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) :
    unchunkedEkSentCt1ReceivedAt A (a + 8#64) st ⊢
      ∃∗ g : FourVecGhost,
        fourVec8HeadersAt a g ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
        vecCapPtrDealloc A g.v4.cap g.v4.ptr := by
  refine Entails.trans (unchunkedEkSentCt1ReceivedAt_entails_dealloc A (a + 8#64) st) ?_
  apply Entails.sepExists_elim; intro g
  refine Entails.sepExists_right g ?_
  rw [fourVec104HeadersAt_8_eq]
  exact Entails.refl _

theorem fourVec8HeadersAt_entails_memRegion_104 (a : BitVec 64) (g : FourVecGhost) :
    fourVec8HeadersAt a g ⊢ memRegion (a + 8#64) 104 := by
  rw [← fourVec104HeadersAt_8_eq]
  exact fourVec104HeadersAt_entails_memRegion_104 (a + 8#64) g

/-- Flat-offset 4-Vec headers at `a + 408#64` (`104` bytes). -/
def fourVec408HeadersAt (a : BitVec 64) (g : FourVecGhost) : SepProp :=
  ((a + 408#64) ↦₆₄ g.v1.cap) ∗ ((a + 416#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 424#64) 8 ∗
  ((a + 432#64) ↦₆₄ g.v2.cap) ∗ ((a + 440#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 448#64) 8 ∗
  ((a + 456#64) ↦₆₄ g.v3.cap) ∗ ((a + 464#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 472#64) 8 ∗
  ((a + 480#64) ↦₆₄ g.v4.cap) ∗ ((a + 488#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 496#64) 16

theorem fourVec104HeadersAt_408_eq (a : BitVec 64) (g : FourVecGhost) :
    fourVec104HeadersAt (a + 408#64) g = fourVec408HeadersAt a g := by
  unfold fourVec104HeadersAt fourVec408HeadersAt
  rw [BitVec.add_assoc a 408#64 8#64, BitVec.add_assoc a 408#64 16#64,
      BitVec.add_assoc a 408#64 24#64, BitVec.add_assoc a 408#64 32#64,
      BitVec.add_assoc a 408#64 40#64, BitVec.add_assoc a 408#64 48#64,
      BitVec.add_assoc a 408#64 56#64, BitVec.add_assoc a 408#64 64#64,
      BitVec.add_assoc a 408#64 72#64, BitVec.add_assoc a 408#64 80#64,
      BitVec.add_assoc a 408#64 88#64]
  rfl

theorem unchunkedEkSentCt1Received408_entails_dealloc (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) :
    unchunkedEkSentCt1ReceivedAt A (a + 408#64) st ⊢
      ∃∗ g : FourVecGhost,
        fourVec408HeadersAt a g ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
        vecCapPtrDealloc A g.v4.cap g.v4.ptr := by
  refine Entails.trans (unchunkedEkSentCt1ReceivedAt_entails_dealloc A (a + 408#64) st) ?_
  apply Entails.sepExists_elim; intro g
  refine Entails.sepExists_right g ?_
  rw [fourVec104HeadersAt_408_eq]
  exact Entails.refl _

theorem fourVec408HeadersAt_entails_memRegion_104 (a : BitVec 64) (g : FourVecGhost) :
    fourVec408HeadersAt a g ⊢ memRegion (a + 408#64) 104 := by
  rw [← fourVec104HeadersAt_408_eq]
  exact fourVec104HeadersAt_entails_memRegion_104 (a + 408#64) g

/-- Flat-offset 5-Vec headers at `a + 408#64` (`128` bytes). -/
def fiveVec408HeadersAt (a : BitVec 64) (g : FiveVecGhost) : SepProp :=
  ((a + 408#64) ↦₆₄ g.v1.cap) ∗ ((a + 416#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 424#64) 8 ∗
  ((a + 432#64) ↦₆₄ g.v2.cap) ∗ ((a + 440#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 448#64) 8 ∗
  ((a + 456#64) ↦₆₄ g.v3.cap) ∗ ((a + 464#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 472#64) 8 ∗
  ((a + 480#64) ↦₆₄ g.v4.cap) ∗ ((a + 488#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 496#64) 8 ∗
  ((a + 504#64) ↦₆₄ g.v5.cap) ∗ ((a + 512#64) ↦₆₄ g.v5.ptr) ∗ memRegion (a + 520#64) 16

theorem fiveVec128HeadersAt_408_eq (a : BitVec 64) (g : FiveVecGhost) :
    fiveVec128HeadersAt (a + 408#64) g = fiveVec408HeadersAt a g := by
  unfold fiveVec128HeadersAt fiveVec408HeadersAt
  rw [BitVec.add_assoc a 408#64 8#64, BitVec.add_assoc a 408#64 16#64,
      BitVec.add_assoc a 408#64 24#64, BitVec.add_assoc a 408#64 32#64,
      BitVec.add_assoc a 408#64 40#64, BitVec.add_assoc a 408#64 48#64,
      BitVec.add_assoc a 408#64 56#64, BitVec.add_assoc a 408#64 64#64,
      BitVec.add_assoc a 408#64 72#64, BitVec.add_assoc a 408#64 80#64,
      BitVec.add_assoc a 408#64 88#64, BitVec.add_assoc a 408#64 96#64,
      BitVec.add_assoc a 408#64 104#64, BitVec.add_assoc a 408#64 112#64]
  rfl

theorem unchunkedCt1Sent408_entails_dealloc (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) :
    unchunkedCt1SentAt A (a + 408#64) st ⊢
      ∃∗ g : FiveVecGhost,
        fiveVec408HeadersAt a g ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
        vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
        vecCapPtrDealloc A g.v5.cap g.v5.ptr := by
  refine Entails.trans (unchunkedCt1SentAt_entails_dealloc A (a + 408#64) st) ?_
  apply Entails.sepExists_elim; intro g
  refine Entails.sepExists_right g ?_
  rw [fiveVec128HeadersAt_408_eq]
  exact Entails.refl _

theorem fiveVec408HeadersAt_entails_memRegion_128 (a : BitVec 64) (g : FiveVecGhost) :
    fiveVec408HeadersAt a g ⊢ memRegion (a + 408#64) 128 := by
  rw [← fiveVec128HeadersAt_408_eq]
  exact fiveVec128HeadersAt_entails_memRegion_128 (a + 408#64) g

/-! ## Region Join and `PolyEncoder` / `PolyDecoder` Helpers -/

theorem tag_and_two_regions_entails_928 (a tag : BitVec 64) (sz pad : Nat) (off : BitVec 64)
    (hoff : a + off = (a + 8#64) + BitVec.ofNat 64 sz)
    (hsum : sz + pad = 920) :
    (a ↦₆₄ tag) ∗ memRegion (a + 8#64) sz ∗ memRegion (a + off) pad ⊢
      memRegion a 928 := by
  have h1 : memRegion (a + 8#64) sz ∗ memRegion (a + off) pad ⊢ memRegion (a + 8#64) 920 := by
    rw [hoff, ← hsum, ProofLib.memRegion_split (a + 8#64) sz pad (by omega)]
    exact Entails.refl _
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 920) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion a tag) h1

theorem polyDecoder64_entails_vecs_tail (A : RustAlloc) (a : BitVec 64) (dec : PolyDecoder) :
    polyDecoderAt A (a + 64#64) dec ⊢
      ∃∗ vecs : List (List Pt),
        ⌜vecs.length = NUM_POLYS⌝ ∗
        vecPtListOf A (a + 64#64) vecs ∗
        memRegion (a + 448#64) 16 := by
  refine Entails.trans (polyDecoderAt_entails_vecs_tail A (a + 64#64) dec) ?_
  apply Entails.sepExists_elim; intro vecs
  refine Entails.sepExists_right vecs ?_
  rw [BitVec.add_assoc a 64#64 384#64]
  exact Entails.refl _

theorem polyDecoder64_post_join (a : BitVec 64) :
    memRegion (a + 64#64) polyArrayBytes ∗ memRegion (a + 448#64) 16 ⊢
      memRegion (a + 64#64) polyDecoderSize := by
  have h448 : a + 448#64 = (a + 64#64) + 384#64 := (BitVec.add_assoc a 64#64 384#64).symm
  rw [h448]
  exact polyDecoder_post_join (a + 64#64)

theorem polyDecoder88_entails_vecs_tail (A : RustAlloc) (a : BitVec 64) (dec : PolyDecoder) :
    polyDecoderAt A (a + 88#64) dec ⊢
      ∃∗ vecs : List (List Pt),
        ⌜vecs.length = NUM_POLYS⌝ ∗
        vecPtListOf A (a + 88#64) vecs ∗
        memRegion (a + 472#64) 16 := by
  refine Entails.trans (polyDecoderAt_entails_vecs_tail A (a + 88#64) dec) ?_
  apply Entails.sepExists_elim; intro vecs
  refine Entails.sepExists_right vecs ?_
  rw [BitVec.add_assoc a 88#64 384#64]
  exact Entails.refl _

theorem polyDecoder88_post_join (a : BitVec 64) :
    memRegion (a + 88#64) polyArrayBytes ∗ memRegion (a + 472#64) 16 ⊢
      memRegion (a + 88#64) polyDecoderSize := by
  have h472 : a + 472#64 = (a + 88#64) + 384#64 := (BitVec.add_assoc a 88#64 384#64).symm
  rw [h472]
  exact polyDecoder_post_join (a + 88#64)

theorem polyEncoder8_entails_tag_vecs_tail (A : RustAlloc) (a : BitVec 64) (enc : PolyEncoder) :
    polyEncoderAt A (a + 8#64) enc ⊢
      ∃∗ tag : BitVec 64, ∃∗ vecs : List (List GF16),
        ⌜vecs.length = NUM_POLYS⌝ ∗
        ((a + 8#64) ↦₆₄ tag) ∗
        vecGF16ListOf A (a + 16#64) vecs ∗
        memRegion (a + 400#64) 8 := by
  refine Entails.trans (polyEncoderAt_entails_tag_vecs_tail A (a + 8#64) enc) ?_
  apply Entails.sepExists_elim; intro tag
  apply Entails.sepExists_elim; intro vecs
  refine Entails.sepExists_right tag (Entails.sepExists_right vecs ?_)
  rw [BitVec.add_assoc a 8#64 8#64, BitVec.add_assoc a 8#64 392#64]
  exact Entails.refl _

theorem polyEncoder_local2_8_post_join (a tag : BitVec 64) :
    ((a + 8#64) ↦₆₄ tag) ∗ memRegion (a + 16#64) polyArrayBytes ∗ memRegion (a + 400#64) 8 ⊢
    memRegion (a + 8#64) 400 := by
  have h16 : a + 16#64 = (a + 8#64) + 8#64 := (BitVec.add_assoc a 8#64 8#64).symm
  have h400 : a + 400#64 = (a + 8#64) + 392#64 := (BitVec.add_assoc a 8#64 392#64).symm
  rw [h16, h400]
  exact polyEncoder_local2_post_join (a + 8#64) tag

/-- Expose the tag (`0#64` or `1#64`) of `polyEncoderAt A a enc` while keeping `polyEncoderAt`
    reconstructible for either `0#64` or `1#64`. -/
def polyEncoderTaggedRest (A : RustAlloc) (a w : BitVec 64) (enc : PolyEncoder) : SepProp :=
  ∃∗ P : SepProp, ⌜(a ↦₆₄ w) ∗ P ⊢ polyEncoderAt A a enc⌝ ∗ P

theorem polyEncoderAt_expose_tag (A : RustAlloc) (a : BitVec 64) (enc : PolyEncoder) :
    polyEncoderAt A a enc ⊢
      ∃∗ w : BitVec 64,
        ⌜w = 0#64 ∨ w = 1#64⌝ ∗
        (a ↦₆₄ w) ∗
        polyEncoderTaggedRest A a w enc := by
  unfold polyEncoderAt encoderStateAt polyEncoderPointsTag polyEncoderPolysTag
  cases hs : enc.s with
  | points pts =>
    dsimp only
    let P := pointListOf A (a + polyEncoderVecsOff) pts ∗
      ((a + polyEncoderIdxOff) ↦₃₂ enc.idx) ∗
      memRegion (a + polyEncoderPadOff) polyEncoderPadSize
    have heq : (⌜pts.length = NUM_POLYS ∧ (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)⌝ ∗ (a ↦₆₄ 0#64) ∗
        pointListOf A (a + polyEncoderVecsOff) pts) ∗
        ((a + polyEncoderIdxOff) ↦₃₂ enc.idx) ∗
        memRegion (a + polyEncoderPadOff) polyEncoderPadSize =
        ⌜pts.length = NUM_POLYS ∧ (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)⌝ ∗ (a ↦₆₄ 0#64) ∗ P := by
      dsimp only [P]; ac_rfl
    rw [heq]
    apply Entails.pure_left; intro hlen
    refine Entails.sepExists_right 0#64 ?_
    refine Entails.pure_right (Or.inl rfl) ?_
    refine sepConj_mono_right ?_
    have hun : (a ↦₆₄ 0#64) ∗ P ⊢ polyEncoderAt A a enc := by
      unfold polyEncoderAt encoderStateAt polyEncoderPointsTag
      rw [hs]; dsimp only
      rw [heq]
      exact Entails.pure_right hlen (Entails.refl _)
    unfold polyEncoderTaggedRest
    exact Entails.sepExists_right P (Entails.pure_right hun (Entails.refl P))
  | polys ps =>
    dsimp only
    let P := polyListOf A (a + polyEncoderVecsOff) ps ∗
      ((a + polyEncoderIdxOff) ↦₃₂ enc.idx) ∗
      memRegion (a + polyEncoderPadOff) polyEncoderPadSize
    have heq : (⌜ps.length = NUM_POLYS⌝ ∗ (a ↦₆₄ 1#64) ∗
        polyListOf A (a + polyEncoderVecsOff) ps) ∗
        ((a + polyEncoderIdxOff) ↦₃₂ enc.idx) ∗
        memRegion (a + polyEncoderPadOff) polyEncoderPadSize =
        ⌜ps.length = NUM_POLYS⌝ ∗ (a ↦₆₄ 1#64) ∗ P := by
      dsimp only [P]; ac_rfl
    rw [heq]
    apply Entails.pure_left; intro hlen
    refine Entails.sepExists_right 1#64 ?_
    refine Entails.pure_right (Or.inr rfl) ?_
    refine sepConj_mono_right ?_
    have hun : (a ↦₆₄ 1#64) ∗ P ⊢ polyEncoderAt A a enc := by
      unfold polyEncoderAt encoderStateAt polyEncoderPolysTag
      rw [hs]; dsimp only
      rw [heq]
      exact Entails.pure_right hlen (Entails.refl _)
    unfold polyEncoderTaggedRest
    exact Entails.sepExists_right P (Entails.pure_right hun (Entails.refl P))

theorem polyEncoderAt_unexpose_tag (A : RustAlloc) (a w : BitVec 64) (enc : PolyEncoder) :
    (a ↦₆₄ w) ∗ polyEncoderTaggedRest A a w enc ⊢ polyEncoderAt A a enc := by
  unfold polyEncoderTaggedRest
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro P
  rw [sepConj_left_comm]
  apply Entails.pure_left; intro hun
  exact hun

end CryptoVerification.SpqrV1.Drop
