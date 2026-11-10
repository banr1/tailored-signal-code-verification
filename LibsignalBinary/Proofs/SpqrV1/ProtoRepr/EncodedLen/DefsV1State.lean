/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1
import Arm64.Legacy.Spec.Library
import ProofLib.VCGen

/-!
# Representation Predicates and `encoded_len` Specifications for `V1State`

Defines the `.rodata` jump table, `V1State` (`224` B) separation-logic representation predicate,
pure `v1StatePBEncodedLen` model, equivalence bridge to `V1State.encodedLen`, and Hoare contracts
for `V1State::encoded_len [local#1, #2]`.
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

/-! ## 1. `.rodata` Jump Table and `.inImage` Helper -/

/-- The 11-byte jump table in `.rodata` (`0x7e53a` for `local#1`, `0x8245a` for `local#2`)
    mapping `V1State.InnerState` discriminant index `0..10` to `((target - (entry + 80)) / 4)`. -/
def v1StateJumpTableBytes : List (BitVec 8) :=
  [0x00#8, 0x7c#8, 0x49#8, 0x4c#8, 0x05#8, 0x9e#8, 0xa3#8, 0x6e#8, 0xca#8, 0x27#8, 0xc5#8]

@[simp] theorem v1StateJumpTableBytes_length :
    v1StateJumpTableBytes.length = 11 := by decide

/-- Introduce one `.rodata` slice into a `subroutine_ok` proof for `spec.inImage img`. -/
theorem subroutine_ok_inImage_rodata1_keep {α : Type} {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {roAddr : BitVec 64} {roBytes : List (BitVec 8)}
    {spec : Spec α}
    (hro : ∀ {s : State} (_ : img.FrozenLoaded s) {P : SepProp},
      (s.mem ⊨ P) → (s.mem ⊨ (roAddr ↦ᵣ roBytes) ∗ P))
    (h : subroutine_ok prog entry
      { spec with
        pre := fun x s =>
          (roAddr ↦ᵣ roBytes) ∗ spec.pre x s
        post := fun x s0 sf =>
          (roAddr ↦ᵣ roBytes) ∗ spec.post x s0 sf }) :
    subroutine_ok prog entry (spec.inImage img) := by
  refine subroutine_ok_mono h (fun x R s0 hpre => ?_) (fun x R s0 sf hq => ?_)
  · simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rw [sepConj_assoc]
    exact hro hpre.1.1 hpre.2
  · dsimp only [Spec.inImage] at hq ⊢
    rw [sepConj_assoc] at hq
    exact Satisfies.of_sep_right hq

/-! ## 2. Optional Unchunked Sub-Message Representation Predicates -/

/-- Niche value `0xfffffffffffffffe` (`usize::MAX - 1`) used for `Option` of structs whose first
    field is already `Option<Vec<u8>>` / `Option<AuthenticatorPB>` (which uses `noneCap = 0xffffffffffffffff`). -/
abbrev noneCap2 : BitVec 64 := 0xfffffffffffffffe#64

/-- `Option<Unchunked.KeysUnsampled>` (`56` bytes = `0x38`, align `8`):
    - `none`: niche `noneCap2 = 0xfffffffffffffffe#64` at `a + 0`, `48` bytes of padding at `a + 8..56`.
    - `some u`: `keysUnsampledPBPinnedAt A g a u`. -/
def optKeysUnsampledPBPinnedAt (A : RustAlloc) (g : Unchunked2PBGhost) (a : BitVec 64) :
    Option V1State.Unchunked.KeysUnsampled → SepProp
  | none => (a ↦₆₄ noneCap2) ∗ memRegion (a + 8#64) 48
  | some u => keysUnsampledPBPinnedAt A g a u

def optKeysUnsampledPBAt (A : RustAlloc) (a : BitVec 64) :
    Option V1State.Unchunked.KeysUnsampled → SepProp
  | none => (a ↦₆₄ noneCap2) ∗ memRegion (a + 8#64) 48
  | some u => keysUnsampledPBAt A a u

/-- `Option<Unchunked.HeaderSent>` (`104` bytes = `0x68`, align `8`):
    - `none`: niche `noneCap = 0xffffffffffffffff#64` at `a + 0`, `96` bytes of padding at `a + 8..104`.
    - `some u`: `headerSentPBPinnedAt A g a u`. -/
def optHeaderSentPBPinnedAt (A : RustAlloc) (g : Unchunked4PBGhost) (a : BitVec 64) :
    Option V1State.Unchunked.HeaderSent → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 96
  | some u => headerSentPBPinnedAt A g a u

def optHeaderSentPBAt (A : RustAlloc) (a : BitVec 64) :
    Option V1State.Unchunked.HeaderSent → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 96
  | some u => headerSentPBAt A a u

/-- `Option<Unchunked.EkSentCt1Received>` (`104` bytes = `0x68`, align `8`):
    - `none`: niche `noneCap = 0xffffffffffffffff#64` at `a + 0`, `96` bytes of padding at `a + 8..104`.
    - `some u`: `ekSentCt1ReceivedPBPinnedAt A g a u`. -/
def optEkSentCt1ReceivedPBPinnedAt (A : RustAlloc) (g : Unchunked4PBGhost) (a : BitVec 64) :
    Option V1State.Unchunked.EkSentCt1Received → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 96
  | some u => ekSentCt1ReceivedPBPinnedAt A g a u

def optEkSentCt1ReceivedPBAt (A : RustAlloc) (a : BitVec 64) :
    Option V1State.Unchunked.EkSentCt1Received → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 96
  | some u => ekSentCt1ReceivedPBAt A a u

/-- `Option<Unchunked.NoHeaderReceived>` (`56` bytes = `0x38`, align `8`):
    - `none`: niche `noneCap2 = 0xfffffffffffffffe#64` at `a + 0`, `48` bytes of padding at `a + 8..56`.
    - `some u`: `noHeaderReceivedPBPinnedAt A g a u`. -/
def optNoHeaderReceivedPBPinnedAt (A : RustAlloc) (g : Unchunked2PBGhost) (a : BitVec 64) :
    Option V1State.Unchunked.NoHeaderReceived → SepProp
  | none => (a ↦₆₄ noneCap2) ∗ memRegion (a + 8#64) 48
  | some u => noHeaderReceivedPBPinnedAt A g a u

def optNoHeaderReceivedPBAt (A : RustAlloc) (a : BitVec 64) :
    Option V1State.Unchunked.NoHeaderReceived → SepProp
  | none => (a ↦₆₄ noneCap2) ∗ memRegion (a + 8#64) 48
  | some u => noHeaderReceivedPBAt A a u

/-- `Option<Unchunked.HeaderReceived>` (`80` bytes = `0x50`, align `8`):
    - `none`: niche `noneCap = 0xffffffffffffffff#64` at `a + 0`, `72` bytes of padding at `a + 8..80`.
    - `some u`: `headerReceivedPBPinnedAt A g a u`. -/
def optHeaderReceivedPBPinnedAt (A : RustAlloc) (g : Unchunked3PBGhost) (a : BitVec 64) :
    Option V1State.Unchunked.HeaderReceived → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 72
  | some u => headerReceivedPBPinnedAt A g a u

def optHeaderReceivedPBAt (A : RustAlloc) (a : BitVec 64) :
    Option V1State.Unchunked.HeaderReceived → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 72
  | some u => headerReceivedPBAt A a u

/-- `Option<Unchunked.Ct1SentEkReceived>` (`128` bytes = `0x80`, align `8`):
    - `none`: niche `noneCap = 0xffffffffffffffff#64` at `a + 0`, `120` bytes of padding at `a + 8..128`.
    - `some u`: `ct1SentEkReceivedPBPinnedAt A g a u`. -/
def optCt1SentEkReceivedPBPinnedAt (A : RustAlloc) (g : Unchunked5PBGhost) (a : BitVec 64) :
    Option V1State.Unchunked.Ct1SentEkReceived → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 120
  | some u => ct1SentEkReceivedPBPinnedAt A g a u

def optCt1SentEkReceivedPBAt (A : RustAlloc) (a : BitVec 64) :
    Option V1State.Unchunked.Ct1SentEkReceived → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 120
  | some u => ct1SentEkReceivedPBAt A a u

/-- `Option<Unchunked.Ct2Sent>` (`56` bytes = `0x38`, align `8`):
    - `none`: niche `noneCap2 = 0xfffffffffffffffe#64` at `a + 0`, `48` bytes of padding at `a + 8..56`.
    - `some u`: `ct2SentPBPinnedAt A g a u`. -/
def optCt2SentPBPinnedAt (A : RustAlloc) (g : Unchunked2PBGhost) (a : BitVec 64) :
    Option V1State.Unchunked.Ct2Sent → SepProp
  | none => (a ↦₆₄ noneCap2) ∗ memRegion (a + 8#64) 48
  | some u => ct2SentPBPinnedAt A g a u

def optCt2SentPBAt (A : RustAlloc) (a : BitVec 64) :
    Option V1State.Unchunked.Ct2Sent → SepProp
  | none => (a ↦₆₄ noneCap2) ∗ memRegion (a + 8#64) 48
  | some u => ct2SentPBAt A a u

/-! ## 3. `V1State` Representation Predicate (`224` bytes = `0xe0`, align `8`) -/

deriving instance Inhabited for
  VecPin, AuthenticatorPBGhost,
  Unchunked3PBGhost, Unchunked4PBGhost, Unchunked5PBGhost,
  PolynomialEncoderPBGhost, PolynomialDecoderPBGhost,
  ChunkedCt1SampledPBGhost, ChunkedHeaderSentPBGhost

/-- First 6 variants of pinned ghost state for `V1State`. -/
structure V1StatePBGhostA where
  gKeysUnsampled : Unchunked2PBGhost
  gKeysSampled : Unchunked4PBGhost × PolynomialEncoderPBGhost
  gHeaderSent : ChunkedHeaderSentPBGhost
  gCt1Received : Unchunked4PBGhost × PolynomialEncoderPBGhost
  gEkSentCt1Received : Unchunked4PBGhost × PolynomialDecoderPBGhost
  gNoHeaderReceived : PolynomialDecoderPBGhost × Unchunked2PBGhost
  deriving Inhabited

/-- Remaining 5 variants of pinned ghost state for `V1State`. -/
structure V1StatePBGhostB where
  gHeaderReceived : Unchunked3PBGhost × PolynomialDecoderPBGhost
  gCt1Sampled : ChunkedCt1SampledPBGhost
  gEkReceivedCt1Sampled : Unchunked5PBGhost × PolynomialEncoderPBGhost
  gCt1Acknowledged : Unchunked5PBGhost × PolynomialDecoderPBGhost
  gCt2Sampled : PolynomialEncoderPBGhost × Unchunked2PBGhost
  deriving Inhabited

/-- Pinned ghost state for `V1State` (`224` bytes = `0xe0`). -/
structure V1StatePBGhost where
  a : V1StatePBGhostA
  b : V1StatePBGhostB
  deriving Inhabited

/-- Layout of the `Some(is)` cases of `spqr::proto::pq_ratchet::V1State` (`224` bytes = `0xe0`, align `8`). -/
def v1StateInnerPBPinnedAt (A : RustAlloc) (g : V1StatePBGhost) (a : BitVec 64) :
    V1State.InnerState → SepProp
  | .keysUnsampled v =>
    (a ↦₆₄ 0x8000000000000000#64) ∗
      optKeysUnsampledPBPinnedAt A g.a.gKeysUnsampled (a + 8#64) v.uc ∗
      memRegion (a + 64#64) 160
  | .keysSampled v =>
    (a ↦₆₄ 0x8000000000000001#64) ∗
      optHeaderSentPBPinnedAt A g.a.gKeysSampled.1 (a + 8#64) v.uc ∗
      optPolynomialEncoderPBPinnedAt A g.a.gKeysSampled.2 (a + 112#64) v.sendingHdr ∗
      memRegion (a + 168#64) 56
  | .headerSent v =>
    (a ↦₆₄ 0x8000000000000002#64) ∗
      chunkedHeaderSentPBPinnedAt A g.a.gHeaderSent (a + 8#64) v ∗
      memRegion (a + 184#64) 40
  | .ct1Received v =>
    (a ↦₆₄ 0x8000000000000003#64) ∗
      optEkSentCt1ReceivedPBPinnedAt A g.a.gCt1Received.1 (a + 8#64) v.uc ∗
      optPolynomialEncoderPBPinnedAt A g.a.gCt1Received.2 (a + 112#64) v.sendingEk ∗
      memRegion (a + 168#64) 56
  | .ekSentCt1Received v =>
    (a ↦₆₄ 0x8000000000000004#64) ∗
      optEkSentCt1ReceivedPBPinnedAt A g.a.gEkSentCt1Received.1 (a + 8#64) v.uc ∗
      optPolynomialDecoderPBPinnedAt A g.a.gEkSentCt1Received.2 (a + 112#64) v.receivingCt2 ∗
      memRegion (a + 152#64) 72
  | .noHeaderReceived v =>
    (a ↦₆₄ 0x8000000000000005#64) ∗
      optPolynomialDecoderPBPinnedAt A g.a.gNoHeaderReceived.1 (a + 8#64) v.receivingHdr ∗
      optNoHeaderReceivedPBPinnedAt A g.a.gNoHeaderReceived.2 (a + 48#64) v.uc ∗
      memRegion (a + 104#64) 120
  | .headerReceived v =>
    (a ↦₆₄ 0x8000000000000006#64) ∗
      optHeaderReceivedPBPinnedAt A g.b.gHeaderReceived.1 (a + 8#64) v.uc ∗
      optPolynomialDecoderPBPinnedAt A g.b.gHeaderReceived.2 (a + 88#64) v.receivingEk ∗
      memRegion (a + 128#64) 96
  | .ct1Sampled v =>
    chunkedCt1SampledPBPinnedAt A g.b.gCt1Sampled a v
  | .ekReceivedCt1Sampled v =>
    (a ↦₆₄ 0x8000000000000008#64) ∗
      optCt1SentEkReceivedPBPinnedAt A g.b.gEkReceivedCt1Sampled.1 (a + 8#64) v.uc ∗
      optPolynomialEncoderPBPinnedAt A g.b.gEkReceivedCt1Sampled.2 (a + 136#64) v.sendingCt1 ∗
      memRegion (a + 192#64) 32
  | .ct1Acknowledged v =>
    (a ↦₆₄ 0x8000000000000009#64) ∗
      optCt1SentPBPinnedAt A g.b.gCt1Acknowledged.1 (a + 8#64) v.uc ∗
      optPolynomialDecoderPBPinnedAt A g.b.gCt1Acknowledged.2 (a + 136#64) v.receivingEk ∗
      memRegion (a + 176#64) 48
  | .ct2Sampled v =>
    (a ↦₆₄ 0x800000000000000a#64) ∗
      optPolynomialEncoderPBPinnedAt A g.b.gCt2Sampled.1 (a + 8#64) v.sendingCt2 ∗
      optCt2SentPBPinnedAt A g.b.gCt2Sampled.2 (a + 64#64) v.uc ∗
      memRegion (a + 120#64) 104

/-- Niche-optimized layout of `spqr::proto::pq_ratchet::V1State` (`224` bytes = `0xe0`, align `8`). -/
def v1StatePBPinnedAt (A : RustAlloc) (g : V1StatePBGhost) (a : BitVec 64) (m : V1State) : SepProp :=
  match m.innerState with
  | none => (a ↦₆₄ noneCap2) ∗ memRegion (a + 8#64) 216
  | some is => v1StateInnerPBPinnedAt A g a is

/-- Existentially-quantified `V1State` representation predicate (`224` bytes = `0xe0`, align `8`). -/
def v1StatePBAt (A : RustAlloc) (a : BitVec 64) (m : V1State) : SepProp :=
  ∃∗ g : V1StatePBGhost, v1StatePBPinnedAt A g a m

theorem v1StatePBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64) (m : V1State) :
    v1StatePBAt A a m = ∃∗ g : V1StatePBGhost, v1StatePBPinnedAt A g a m := rfl

/-! ## 4. Pure `encodedLen` Models and Bridges to `LibsignalSpqrV1.Proto` -/

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

/-- Encoded length of an optional `Unchunked.KeysUnsampled` field with a 1-byte tag (`tag ∈ 1..15`). -/
def optKeysUnsampledPBFieldEncodedLen : Option V1State.Unchunked.KeysUnsampled → Nat
  | none => 0
  | some u =>
    let len := keysUnsampledPBEncodedLen u
    1 + varintLen (BitVec.ofNat 64 len) + len

theorem optKeysUnsampledPBFieldEncodedLen_eq_proto (tag : BitVec 32)
    (opt : Option V1State.Unchunked.KeysUnsampled) (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeOptMessage V1State.Unchunked.KeysUnsampled.encodeRaw tag opt).length =
      optKeysUnsampledPBFieldEncodedLen opt := by
  cases opt with
  | none => rfl
  | some u =>
    unfold Proto.encodeOptMessage Proto.encodeMessage optKeysUnsampledPBFieldEncodedLen
    simp only [List.length_append, protoEncodeKey_len_one tag .lengthDelimited htag,
      ← keysUnsampledPBEncodedLen_eq_proto, V1State.Unchunked.KeysUnsampled.encodedLen,
      ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]

/-- Encoded length of an optional `Unchunked.HeaderSent` field with a 1-byte tag (`tag ∈ 1..15`). -/
def optHeaderSentPBFieldEncodedLen : Option V1State.Unchunked.HeaderSent → Nat
  | none => 0
  | some u =>
    let len := headerSentPBEncodedLen u
    1 + varintLen (BitVec.ofNat 64 len) + len

theorem optHeaderSentPBFieldEncodedLen_eq_proto (tag : BitVec 32)
    (opt : Option V1State.Unchunked.HeaderSent) (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeOptMessage V1State.Unchunked.HeaderSent.encodeRaw tag opt).length =
      optHeaderSentPBFieldEncodedLen opt := by
  cases opt with
  | none => rfl
  | some u =>
    unfold Proto.encodeOptMessage Proto.encodeMessage optHeaderSentPBFieldEncodedLen
    simp only [List.length_append, protoEncodeKey_len_one tag .lengthDelimited htag,
      ← headerSentPBEncodedLen_eq_proto, V1State.Unchunked.HeaderSent.encodedLen,
      ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]

/-- Encoded length of an optional `Unchunked.EkSentCt1Received` field with a 1-byte tag (`tag ∈ 1..15`). -/
def optEkSentCt1ReceivedPBFieldEncodedLen : Option V1State.Unchunked.EkSentCt1Received → Nat
  | none => 0
  | some u =>
    let len := ekSentCt1ReceivedPBEncodedLen u
    1 + varintLen (BitVec.ofNat 64 len) + len

theorem optEkSentCt1ReceivedPBFieldEncodedLen_eq_proto (tag : BitVec 32)
    (opt : Option V1State.Unchunked.EkSentCt1Received) (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeOptMessage V1State.Unchunked.EkSentCt1Received.encodeRaw tag opt).length =
      optEkSentCt1ReceivedPBFieldEncodedLen opt := by
  cases opt with
  | none => rfl
  | some u =>
    unfold Proto.encodeOptMessage Proto.encodeMessage optEkSentCt1ReceivedPBFieldEncodedLen
    simp only [List.length_append, protoEncodeKey_len_one tag .lengthDelimited htag,
      ← ekSentCt1ReceivedPBEncodedLen_eq_proto, V1State.Unchunked.EkSentCt1Received.encodedLen,
      ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]

/-- Encoded length of an optional `Unchunked.NoHeaderReceived` field with a 1-byte tag (`tag ∈ 1..15`). -/
def optNoHeaderReceivedPBFieldEncodedLen : Option V1State.Unchunked.NoHeaderReceived → Nat
  | none => 0
  | some u =>
    let len := noHeaderReceivedPBEncodedLen u
    1 + varintLen (BitVec.ofNat 64 len) + len

theorem optNoHeaderReceivedPBFieldEncodedLen_eq_proto (tag : BitVec 32)
    (opt : Option V1State.Unchunked.NoHeaderReceived) (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeOptMessage V1State.Unchunked.NoHeaderReceived.encodeRaw tag opt).length =
      optNoHeaderReceivedPBFieldEncodedLen opt := by
  cases opt with
  | none => rfl
  | some u =>
    unfold Proto.encodeOptMessage Proto.encodeMessage optNoHeaderReceivedPBFieldEncodedLen
    simp only [List.length_append, protoEncodeKey_len_one tag .lengthDelimited htag,
      ← noHeaderReceivedPBEncodedLen_eq_proto, V1State.Unchunked.NoHeaderReceived.encodedLen,
      ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]

/-- Encoded length of an optional `Unchunked.HeaderReceived` field with a 1-byte tag (`tag ∈ 1..15`). -/
def optHeaderReceivedPBFieldEncodedLen : Option V1State.Unchunked.HeaderReceived → Nat
  | none => 0
  | some u =>
    let len := headerReceivedPBEncodedLen u
    1 + varintLen (BitVec.ofNat 64 len) + len

theorem optHeaderReceivedPBFieldEncodedLen_eq_proto (tag : BitVec 32)
    (opt : Option V1State.Unchunked.HeaderReceived) (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw tag opt).length =
      optHeaderReceivedPBFieldEncodedLen opt := by
  cases opt with
  | none => rfl
  | some u =>
    unfold Proto.encodeOptMessage Proto.encodeMessage optHeaderReceivedPBFieldEncodedLen
    simp only [List.length_append, protoEncodeKey_len_one tag .lengthDelimited htag,
      ← headerReceivedPBEncodedLen_eq_proto, V1State.Unchunked.HeaderReceived.encodedLen,
      ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]

/-- Encoded length of an optional `Unchunked.Ct1SentEkReceived` field with a 1-byte tag (`tag ∈ 1..15`). -/
def optCt1SentEkReceivedPBFieldEncodedLen : Option V1State.Unchunked.Ct1SentEkReceived → Nat
  | none => 0
  | some u =>
    let len := ct1SentEkReceivedPBEncodedLen u
    1 + varintLen (BitVec.ofNat 64 len) + len

theorem optCt1SentEkReceivedPBFieldEncodedLen_eq_proto (tag : BitVec 32)
    (opt : Option V1State.Unchunked.Ct1SentEkReceived) (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeOptMessage V1State.Unchunked.Ct1SentEkReceived.encodeRaw tag opt).length =
      optCt1SentEkReceivedPBFieldEncodedLen opt := by
  cases opt with
  | none => rfl
  | some u =>
    unfold Proto.encodeOptMessage Proto.encodeMessage optCt1SentEkReceivedPBFieldEncodedLen
    simp only [List.length_append, protoEncodeKey_len_one tag .lengthDelimited htag,
      ← ct1SentEkReceivedPBEncodedLen_eq_proto, V1State.Unchunked.Ct1SentEkReceived.encodedLen,
      ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]

/-- Encoded length of an optional `Unchunked.Ct2Sent` field with a 1-byte tag (`tag ∈ 1..15`). -/
def optCt2SentPBFieldEncodedLen : Option V1State.Unchunked.Ct2Sent → Nat
  | none => 0
  | some u =>
    let len := ct2SentPBEncodedLen u
    1 + varintLen (BitVec.ofNat 64 len) + len

theorem optCt2SentPBFieldEncodedLen_eq_proto (tag : BitVec 32)
    (opt : Option V1State.Unchunked.Ct2Sent) (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeOptMessage V1State.Unchunked.Ct2Sent.encodeRaw tag opt).length =
      optCt2SentPBFieldEncodedLen opt := by
  cases opt with
  | none => rfl
  | some u =>
    unfold Proto.encodeOptMessage Proto.encodeMessage optCt2SentPBFieldEncodedLen
    simp only [List.length_append, protoEncodeKey_len_one tag .lengthDelimited htag,
      ← ct2SentPBEncodedLen_eq_proto, V1State.Unchunked.Ct2Sent.encodedLen,
      ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]

/-- Inner encoded length of each `V1State.InnerState` variant (before the outer 1-byte tag + varint prefix). -/
def v1StateInnerPayloadEncodedLen : V1State.InnerState → Nat
  | .keysUnsampled v =>
    optKeysUnsampledPBFieldEncodedLen v.uc
  | .keysSampled v =>
    optHeaderSentPBFieldEncodedLen v.uc +
      optPolynomialEncoderPBFieldEncodedLen v.sendingHdr
  | .headerSent v =>
    chunkedHeaderSentPBEncodedLen v
  | .ct1Received v =>
    optEkSentCt1ReceivedPBFieldEncodedLen v.uc +
      optPolynomialEncoderPBFieldEncodedLen v.sendingEk
  | .ekSentCt1Received v =>
    optEkSentCt1ReceivedPBFieldEncodedLen v.uc +
      optPolynomialDecoderPBFieldEncodedLen v.receivingCt2
  | .noHeaderReceived v =>
    optNoHeaderReceivedPBFieldEncodedLen v.uc +
      optPolynomialDecoderPBFieldEncodedLen v.receivingHdr
  | .headerReceived v =>
    optHeaderReceivedPBFieldEncodedLen v.uc +
      optPolynomialDecoderPBFieldEncodedLen v.receivingEk
  | .ct1Sampled v =>
    chunkedCt1SampledPBEncodedLen v
  | .ekReceivedCt1Sampled v =>
    optCt1SentEkReceivedPBFieldEncodedLen v.uc +
      optPolynomialEncoderPBFieldEncodedLen v.sendingCt1
  | .ct1Acknowledged v =>
    optCt1SentPBFieldEncodedLen v.uc +
      optPolynomialDecoderPBFieldEncodedLen v.receivingEk
  | .ct2Sampled v =>
    optCt2SentPBFieldEncodedLen v.uc +
      optPolynomialEncoderPBFieldEncodedLen v.sendingCt2

/-- Encoded length of `V1State`: `0` when `innerState = none`, and
    `1 + varintLen (BitVec.ofNat 64 len) + len` when `innerState = some is`. -/
def v1StatePBEncodedLen (m : V1State) : Nat :=
  match m.innerState with
  | none => 0
  | some is =>
    let len := v1StateInnerPayloadEncodedLen is
    1 + varintLen (BitVec.ofNat 64 len) + len

theorem v1StatePBEncodedLen_eq_proto (m : V1State) :
    V1State.encodedLen m = v1StatePBEncodedLen m := by
  unfold V1State.encodedLen V1State.encodeRaw v1StatePBEncodedLen
  cases m.innerState with
  | none => rfl
  | some is =>
    cases is with
    | keysUnsampled v =>
      unfold V1State.InnerState.encode Proto.encodeMessage V1State.Chunked.KeysUnsampled.encodeRaw
        v1StateInnerPayloadEncodedLen
      simp only [List.length_append,
        protoEncodeKey_len_one 1#32 .lengthDelimited ⟨by decide, by decide⟩,
        optKeysUnsampledPBFieldEncodedLen_eq_proto 1#32 v.uc ⟨by decide, by decide⟩,
        ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]
    | keysSampled v =>
      unfold V1State.InnerState.encode Proto.encodeMessage V1State.Chunked.KeysSampled.encodeRaw
        v1StateInnerPayloadEncodedLen
      simp only [List.length_append,
        protoEncodeKey_len_one 2#32 .lengthDelimited ⟨by decide, by decide⟩,
        optHeaderSentPBFieldEncodedLen_eq_proto 1#32 v.uc ⟨by decide, by decide⟩,
        optPolynomialEncoderPBFieldEncodedLen_eq_proto 2#32 v.sendingHdr ⟨by decide, by decide⟩,
        ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]
    | headerSent v =>
      unfold V1State.InnerState.encode Proto.encodeMessage v1StateInnerPayloadEncodedLen
      simp only [List.length_append,
        protoEncodeKey_len_one 3#32 .lengthDelimited ⟨by decide, by decide⟩,
        ← chunkedHeaderSentPBEncodedLen_eq_proto v, V1State.Chunked.HeaderSent.encodedLen,
        ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]
    | ct1Received v =>
      unfold V1State.InnerState.encode Proto.encodeMessage V1State.Chunked.Ct1Received.encodeRaw
        v1StateInnerPayloadEncodedLen
      simp only [List.length_append,
        protoEncodeKey_len_one 4#32 .lengthDelimited ⟨by decide, by decide⟩,
        optEkSentCt1ReceivedPBFieldEncodedLen_eq_proto 1#32 v.uc ⟨by decide, by decide⟩,
        optPolynomialEncoderPBFieldEncodedLen_eq_proto 2#32 v.sendingEk ⟨by decide, by decide⟩,
        ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]
    | ekSentCt1Received v =>
      unfold V1State.InnerState.encode Proto.encodeMessage V1State.Chunked.EkSentCt1Received.encodeRaw
        v1StateInnerPayloadEncodedLen
      simp only [List.length_append,
        protoEncodeKey_len_one 5#32 .lengthDelimited ⟨by decide, by decide⟩,
        optEkSentCt1ReceivedPBFieldEncodedLen_eq_proto 1#32 v.uc ⟨by decide, by decide⟩,
        optPolynomialDecoderPBFieldEncodedLen_eq_proto 3#32 v.receivingCt2 ⟨by decide, by decide⟩,
        ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]
    | noHeaderReceived v =>
      unfold V1State.InnerState.encode Proto.encodeMessage V1State.Chunked.NoHeaderReceived.encodeRaw
        v1StateInnerPayloadEncodedLen
      simp only [List.length_append,
        protoEncodeKey_len_one 6#32 .lengthDelimited ⟨by decide, by decide⟩,
        optNoHeaderReceivedPBFieldEncodedLen_eq_proto 1#32 v.uc ⟨by decide, by decide⟩,
        optPolynomialDecoderPBFieldEncodedLen_eq_proto 2#32 v.receivingHdr ⟨by decide, by decide⟩,
        ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]
    | headerReceived v =>
      unfold V1State.InnerState.encode Proto.encodeMessage V1State.Chunked.HeaderReceived.encodeRaw
        v1StateInnerPayloadEncodedLen
      simp only [List.length_append,
        protoEncodeKey_len_one 7#32 .lengthDelimited ⟨by decide, by decide⟩,
        optHeaderReceivedPBFieldEncodedLen_eq_proto 1#32 v.uc ⟨by decide, by decide⟩,
        optPolynomialDecoderPBFieldEncodedLen_eq_proto 2#32 v.receivingEk ⟨by decide, by decide⟩,
        ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]
    | ct1Sampled v =>
      unfold V1State.InnerState.encode Proto.encodeMessage v1StateInnerPayloadEncodedLen
      simp only [List.length_append,
        protoEncodeKey_len_one 8#32 .lengthDelimited ⟨by decide, by decide⟩,
        ← chunkedCt1SampledPBEncodedLen_eq_proto v, V1State.Chunked.Ct1Sampled.encodedLen,
        ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]
    | ekReceivedCt1Sampled v =>
      unfold V1State.InnerState.encode Proto.encodeMessage V1State.Chunked.EkReceivedCt1Sampled.encodeRaw
        v1StateInnerPayloadEncodedLen
      simp only [List.length_append,
        protoEncodeKey_len_one 9#32 .lengthDelimited ⟨by decide, by decide⟩,
        optCt1SentEkReceivedPBFieldEncodedLen_eq_proto 1#32 v.uc ⟨by decide, by decide⟩,
        optPolynomialEncoderPBFieldEncodedLen_eq_proto 2#32 v.sendingCt1 ⟨by decide, by decide⟩,
        ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]
    | ct1Acknowledged v =>
      unfold V1State.InnerState.encode Proto.encodeMessage V1State.Chunked.Ct1Acknowledged.encodeRaw
        v1StateInnerPayloadEncodedLen
      simp only [List.length_append,
        protoEncodeKey_len_one 10#32 .lengthDelimited ⟨by decide, by decide⟩,
        optCt1SentPBFieldEncodedLen_eq_proto 1#32 v.uc ⟨by decide, by decide⟩,
        optPolynomialDecoderPBFieldEncodedLen_eq_proto 2#32 v.receivingEk ⟨by decide, by decide⟩,
        ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]
    | ct2Sampled v =>
      unfold V1State.InnerState.encode Proto.encodeMessage V1State.Chunked.Ct2Sampled.encodeRaw
        v1StateInnerPayloadEncodedLen
      simp only [List.length_append,
        protoEncodeKey_len_one 11#32 .lengthDelimited ⟨by decide, by decide⟩,
        optCt2SentPBFieldEncodedLen_eq_proto 1#32 v.uc ⟨by decide, by decide⟩,
        optPolynomialEncoderPBFieldEncodedLen_eq_proto 2#32 v.sendingCt2 ⟨by decide, by decide⟩,
        ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]

/-! ## 5. Symbol Names, Stack Budgets, and Hoare `Spec`s -/

abbrev v1StateEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#1]"
abbrev v1StateEncodedLenLocal2Name : String :=
  "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#2]"

/-- Own stack frame of `V1State::encoded_len` (`0x20` bytes = `32` bytes). -/
abbrev v1StateEncodedLenFrame : Nat := 0x20

/-- Total stack budget for `V1State::encoded_len`:
    own `0x20`-byte frame plus `0x30` bytes for `chunked::*` callees (`0x50` bytes = `80` bytes). -/
abbrev v1StateEncodedLenStack : Nat := v1StateEncodedLenFrame + chunkedEncodedLenStack

abbrev V1StateEncodedLenPinnedGhost := PinnedEncLenGhost V1StatePBGhost V1State
abbrev V1StateEncodedLenGhost := UnpinnedEncLenGhost V1State

/-- Pinned Hoare specification for `V1State::encoded_len` with explicit `.rodata` jump table at `roBase`. -/
def v1StateEncodedLenRoPinnedSpec (A : RustAlloc) (roBase : BitVec 64) :
    Spec V1StateEncodedLenPinnedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ v1StatePBEncodedLen x.m < 2 ^ 64⌝ ∗
      (roBase ↦ᵣ v1StateJumpTableBytes) ∗
      v1StatePBPinnedAt A x.g x.a x.m ∗ stackAt s.sp v1StateEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen x.m) ∧ sf.trace = s0.trace⌝ ∗
      (roBase ↦ᵣ v1StateJumpTableBytes) ∗
      v1StatePBPinnedAt A x.g x.a x.m ∗ stackAt s0.sp v1StateEncodedLenStack

/-- Existentially-quantified Hoare specification for `V1State::encoded_len` with explicit `.rodata` jump table at `roBase`. -/
def v1StateEncodedLenRoSpec (A : RustAlloc) (roBase : BitVec 64) :
    Spec V1StateEncodedLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ v1StatePBEncodedLen x.m < 2 ^ 64⌝ ∗
      (roBase ↦ᵣ v1StateJumpTableBytes) ∗
      v1StatePBAt A x.a x.m ∗ stackAt s.sp v1StateEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen x.m) ∧ sf.trace = s0.trace⌝ ∗
      (roBase ↦ᵣ v1StateJumpTableBytes) ∗
      v1StatePBAt A x.a x.m ∗ stackAt s0.sp v1StateEncodedLenStack

/-- Pinned Hoare specification for `V1State::encoded_len` (without explicit `.rodata` atom, for `.inImage img`). -/
def v1StateEncodedLenPinnedSpec (A : RustAlloc) : Spec V1StateEncodedLenPinnedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ v1StatePBEncodedLen x.m < 2 ^ 64⌝ ∗
      v1StatePBPinnedAt A x.g x.a x.m ∗ stackAt s.sp v1StateEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen x.m) ∧ sf.trace = s0.trace⌝ ∗
      v1StatePBPinnedAt A x.g x.a x.m ∗ stackAt s0.sp v1StateEncodedLenStack

/-- Existentially-quantified Hoare specification for `V1State::encoded_len` (without explicit `.rodata` atom, for `.inImage img`). -/
def v1StateEncodedLenSpec (A : RustAlloc) : Spec V1StateEncodedLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ v1StatePBEncodedLen x.m < 2 ^ 64⌝ ∗
      v1StatePBAt A x.a x.m ∗ stackAt s.sp v1StateEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen x.m) ∧ sf.trace = s0.trace⌝ ∗
      v1StatePBAt A x.a x.m ∗ stackAt s0.sp v1StateEncodedLenStack

end CryptoVerification.SpqrV1.ProtoRepr
