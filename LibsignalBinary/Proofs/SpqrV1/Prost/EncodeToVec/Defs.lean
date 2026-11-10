/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1State
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
public import LibsignalBinary.Proofs.CodeLayout
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# `PqRatchetState::encode_to_vec`: Representation Predicates and Specifications

Memory layouts and `Option` niche encodings (`noneCap3 = usize::MAX - 2`) for `PqRatchetState`,
pure `encodedLen` characterizations, `.rodata` jump-table decomposition, stack-frame layouts, and
Hoare specifications for `PqRatchetState::encode_to_vec` (`0x6d010`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

noncomputable abbrev spqrProgAtExt (b : BitVec 64)
    (ext : String → Option (State → State)) : Program :=
  libsignalSessionCode.rebase b (Rust.withPanics ext)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

abbrev spqrEncodeToVecName : String :=
  "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"

@[simp, arm64_norm] theorem spqrEncodeToVec_fnOff :
    libsignalSessionCode.fnOff spqrEncodeToVecName = 0x67c18 :=
  libsignalSessionCode_fnOff_0x67c18

/-- The 22-byte (`11 × u16`) jump table in `.rodata` at `0x82480` mapping `V1State.InnerState`
discriminant index `0..10` to `(target - (entry + 0x768)) / 4`. -/
def encodeToVecJumpTableBytes : List (BitVec 8) :=
  [0x00#8, 0x00#8, 0xd5#8, 0x00#8, 0x46#8, 0x00#8, 0x9c#8, 0x00#8,
   0x14#8, 0x00#8, 0xee#8, 0x00#8, 0xfd#8, 0x00#8, 0xb5#8, 0x00#8,
   0x25#8, 0x01#8, 0x2d#8, 0x00#8, 0x16#8, 0x01#8]

@[simp] theorem encodeToVecJumpTableBytes_length :
    encodeToVecJumpTableBytes.length = 22 := by decide

/-- Niche value `0xfffffffffffffffd` (`usize::MAX - 2`) used for `Option<pq_ratchet_state::Inner>::None`. -/
abbrev noneCap3 : BitVec 64 := 0xfffffffffffffffd#64

/-- Pinned representation predicate for `Option<spqr::proto::pq_ratchet::pq_ratchet_state::Inner>`
at `a` (`224` bytes = `0xe0`, align `8`):
- `none`: `(a ↦₆₄ noneCap3) ∗ memRegion (a + 8#64) 216`
- `some (.v1 v1)`: `v1StatePBPinnedAt A g a v1` -/
def optPqRatchetInnerPBPinnedAt (A : RustAlloc) (g : V1StatePBGhost) (a : BitVec 64) :
    Option PqRatchetState.Inner → SepProp
  | none => (a ↦₆₄ noneCap3) ∗ memRegion (a + 8#64) 216
  | some (.v1 v1) => v1StatePBPinnedAt A g a v1

/-- Unpinned representation predicate for `Option<spqr::proto::pq_ratchet::pq_ratchet_state::Inner>`
at `a` (`224` bytes = `0xe0`, align `8`). -/
def optPqRatchetInnerPBAt (A : RustAlloc) (a : BitVec 64) :
    Option PqRatchetState.Inner → SepProp
  | none => (a ↦₆₄ noneCap3) ∗ memRegion (a + 8#64) 216
  | some (.v1 v1) => v1StatePBAt A a v1

deriving instance Inhabited for VersionNegotiationPBGhost, ChainPBGhost

/-- Pinned ghost state for `spqr::proto::pq_ratchet::PqRatchetState` (`352` bytes = `0x160`, align `8`). -/
structure PqRatchetStatePBGhost where
  vn : VersionNegotiationPBGhost
  chain : ChainPBGhost
  inner : V1StatePBGhost
  deriving Inhabited

/-- Pinned representation predicate for `spqr::proto::pq_ratchet::PqRatchetState` at `a`
(`352` bytes = `0x160`, align `8`):
- `a + 0x00` (`0..48`): `version_negotiation: Option<VersionNegotiation>` (tag 1, `48`B)
- `a + 0x30` (`48..128`): `chain: Option<Chain>` (tag 2, `80`B)
- `a + 0x80` (`128..352`): `inner: Option<pq_ratchet_state::Inner>` (tag 3, `224`B) -/
def pqRatchetStatePBPinnedAt (A : RustAlloc) (g : PqRatchetStatePBGhost)
    (a : BitVec 64) (st : PqRatchetState) : SepProp :=
  optVersionNegotiationPBPinnedAt A g.vn a st.versionNegotiation ∗
    optChainPBPinnedAt A g.chain (a + 48#64) st.chain ∗
    optPqRatchetInnerPBPinnedAt A g.inner (a + 128#64) st.inner

/-- Unpinned representation predicate for `spqr::proto::pq_ratchet::PqRatchetState` at `a`
(`352` bytes = `0x160`, align `8`). -/
def pqRatchetStatePBAt (A : RustAlloc) (a : BitVec 64) (st : PqRatchetState) : SepProp :=
  optVersionNegotiationPBAt A a st.versionNegotiation ∗
    optChainPBAt A (a + 48#64) st.chain ∗
    optPqRatchetInnerPBAt A (a + 128#64) st.inner

theorem optVersionNegotiationPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option VersionNegotiationPB) :
    optVersionNegotiationPBAt A a opt =
      ∃∗ g : VersionNegotiationPBGhost, optVersionNegotiationPBPinnedAt A g a opt := by
  cases opt with
  | none =>
    unfold optVersionNegotiationPBAt optVersionNegotiationPBPinnedAt
    exact sepProp_eq_of_entails
      (Entails.sepExists_right default (Entails.refl _))
      (Entails.sepExists_elim fun _ => Entails.refl _)
  | some vn =>
    exact versionNegotiationPBAt_eq_exists_pinned A a vn

theorem optChainPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option ChainPB) :
    optChainPBAt A a opt =
      ∃∗ g : ChainPBGhost, optChainPBPinnedAt A g a opt := by
  cases opt with
  | none =>
    unfold optChainPBAt optChainPBPinnedAt
    exact sepProp_eq_of_entails
      (Entails.sepExists_right default (Entails.refl _))
      (Entails.sepExists_elim fun _ => Entails.refl _)
  | some ch =>
    exact chainPBAt_eq_exists_pinned A a ch

theorem optPqRatchetInnerPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option PqRatchetState.Inner) :
    optPqRatchetInnerPBAt A a opt = ∃∗ g : V1StatePBGhost, optPqRatchetInnerPBPinnedAt A g a opt := by
  cases opt with
  | none =>
    unfold optPqRatchetInnerPBAt optPqRatchetInnerPBPinnedAt
    exact sepProp_eq_of_entails
      (Entails.sepExists_right default (Entails.refl _))
      (Entails.sepExists_elim fun _ => Entails.refl _)
  | some i =>
    cases i with
    | v1 v1 => rfl

theorem pqRatchetStatePBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64) (st : PqRatchetState) :
    pqRatchetStatePBAt A a st = ∃∗ g : PqRatchetStatePBGhost, pqRatchetStatePBPinnedAt A g a st := by
  unfold pqRatchetStatePBAt pqRatchetStatePBPinnedAt
  rw [optVersionNegotiationPBAt_eq_exists_pinned, optChainPBAt_eq_exists_pinned,
    optPqRatchetInnerPBAt_eq_exists_pinned]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun g3 => Entails.sepExists_elim fun g2 =>
      Entails.sepExists_elim fun g1 => Entails.sepExists_right ⟨g1, g2, g3⟩ (Entails.refl _)
  · exact Entails.sepExists_elim fun ⟨g1, g2, g3⟩ =>
      Entails.sepExists_right g3 (Entails.sepExists_right g2 (Entails.sepExists_right g1 (Entails.refl _)))

/-! ## Pure `encodedLen` Models and Bridges for `PqRatchetState` -/

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

/-- Encoded length of an optional `VersionNegotiation` field with a 1-byte tag (`tag = 1`). -/
def optVersionNegotiationPBFieldEncodedLen : Option VersionNegotiationPB → Nat
  | none => 0
  | some vn =>
    let len := versionNegotiationPBEncodedLen vn
    1 + varintLen (BitVec.ofNat 64 len) + len

theorem optVersionNegotiationPBFieldEncodedLen_eq_proto (tag : BitVec 32)
    (opt : Option VersionNegotiationPB) (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw tag opt).length =
      optVersionNegotiationPBFieldEncodedLen opt := by
  cases opt with
  | none => rfl
  | some vn =>
    unfold Proto.encodeOptMessage Proto.encodeMessage optVersionNegotiationPBFieldEncodedLen
    simp only [List.length_append, protoEncodeKey_len_one tag .lengthDelimited htag,
      ← versionNegotiationPBEncodedLen_eq_proto, VersionNegotiationPB.encodedLen,
      ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]

/-- Encoded length of an optional `Chain` field with a 1-byte tag (`tag = 2`). -/
def optChainPBFieldEncodedLen : Option ChainPB → Nat
  | none => 0
  | some ch =>
    let len := chainPBEncodedLen ch
    1 + varintLen (BitVec.ofNat 64 len) + len

theorem optChainPBFieldEncodedLen_eq_proto (tag : BitVec 32)
    (opt : Option ChainPB) (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeOptMessage ChainPB.encodeRaw tag opt).length =
      optChainPBFieldEncodedLen opt := by
  cases opt with
  | none => rfl
  | some ch =>
    unfold Proto.encodeOptMessage Proto.encodeMessage optChainPBFieldEncodedLen
    simp only [List.length_append, protoEncodeKey_len_one tag .lengthDelimited htag,
      ← chainPBEncodedLen_eq_proto, ChainPB.encodedLen,
      ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]

/-- Encoded length of `Option<PqRatchetState.Inner>` (`tag = 3`). -/
def optPqRatchetInnerPBFieldEncodedLen : Option PqRatchetState.Inner → Nat
  | none => 0
  | some (.v1 v1) =>
    let len := v1StatePBEncodedLen v1
    1 + varintLen (BitVec.ofNat 64 len) + len

/-- Total encoded length of `PqRatchetState`. -/
def pqRatchetStatePBEncodedLen (st : PqRatchetState) : Nat :=
  optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
    optChainPBFieldEncodedLen st.chain +
    optPqRatchetInnerPBFieldEncodedLen st.inner

theorem pqRatchetStatePBEncodedLen_eq_proto (st : PqRatchetState) :
    (PqRatchetState.encodeRaw st).length = pqRatchetStatePBEncodedLen st := by
  unfold PqRatchetState.encodeRaw pqRatchetStatePBEncodedLen
  rw [List.length_append, List.length_append,
    optVersionNegotiationPBFieldEncodedLen_eq_proto 1#32 st.versionNegotiation ⟨by decide, by decide⟩,
    optChainPBFieldEncodedLen_eq_proto 2#32 st.chain ⟨by decide, by decide⟩]
  congr 1
  cases st.inner with
  | none => rfl
  | some i =>
    cases i with
    | v1 v1 =>
      unfold PqRatchetState.Inner.encode Proto.encodeMessage optPqRatchetInnerPBFieldEncodedLen
      simp only [List.length_append,
        protoEncodeKey_len_one 3#32 .lengthDelimited ⟨by decide, by decide⟩,
        ← v1StatePBEncodedLen_eq_proto, V1State.encodedLen,
        ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]

/-! ## `.rodata` Jump-Table Decomposition (`0x82480`) -/

/-- Unpacked 11-entry (`22`-byte) `.rodata` half-word jump table at `roBase` (`b + 0xa1480#64`). -/
def encodeToVecJumpTableBytesAt (roBase : BitVec 64) : SepProp :=
  (roBase ↦₁₆ᵣ 0x0000#16) ∗ ((roBase + 2#64) ↦₁₆ᵣ 0x00d5#16) ∗
  ((roBase + 4#64) ↦₁₆ᵣ 0x0046#16) ∗ ((roBase + 6#64) ↦₁₆ᵣ 0x009c#16) ∗
  ((roBase + 8#64) ↦₁₆ᵣ 0x0014#16) ∗ ((roBase + 10#64) ↦₁₆ᵣ 0x00ee#16) ∗
  ((roBase + 12#64) ↦₁₆ᵣ 0x00fd#16) ∗ ((roBase + 14#64) ↦₁₆ᵣ 0x00b5#16) ∗
  ((roBase + 16#64) ↦₁₆ᵣ 0x0125#16) ∗ ((roBase + 18#64) ↦₁₆ᵣ 0x002d#16) ∗
  ((roBase + 20#64) ↦₁₆ᵣ 0x0116#16)

theorem encodeToVecJumpTableBytes_eq (roBase : BitVec 64) :
    (roBase ↦ᵣ encodeToVecJumpTableBytes) = encodeToVecJumpTableBytesAt roBase := by
  have h0000 : ((0x0000#16).extractLsb' 0 8 = 0x00#8) ∧ ((0x0000#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h00d5 : ((0x00d5#16).extractLsb' 0 8 = 0xd5#8) ∧ ((0x00d5#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h0046 : ((0x0046#16).extractLsb' 0 8 = 0x46#8) ∧ ((0x0046#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h009c : ((0x009c#16).extractLsb' 0 8 = 0x9c#8) ∧ ((0x009c#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h0014 : ((0x0014#16).extractLsb' 0 8 = 0x14#8) ∧ ((0x0014#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h00ee : ((0x00ee#16).extractLsb' 0 8 = 0xee#8) ∧ ((0x00ee#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h00fd : ((0x00fd#16).extractLsb' 0 8 = 0xfd#8) ∧ ((0x00fd#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h00b5 : ((0x00b5#16).extractLsb' 0 8 = 0xb5#8) ∧ ((0x00b5#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h0125 : ((0x0125#16).extractLsb' 0 8 = 0x25#8) ∧ ((0x0125#16).extractLsb' 8 8 = 0x01#8) := ⟨by decide, by decide⟩
  have h002d : ((0x002d#16).extractLsb' 0 8 = 0x2d#8) ∧ ((0x002d#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h0116 : ((0x0116#16).extractLsb' 0 8 = 0x16#8) ∧ ((0x0116#16).extractLsb' 8 8 = 0x01#8) := ⟨by decide, by decide⟩
  unfold encodeToVecJumpTableBytes encodeToVecJumpTableBytesAt pointsTo16RO
  simp only [pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp,
    h0000.1, h0000.2, h00d5.1, h00d5.2, h0046.1, h0046.2, h009c.1, h009c.2,
    h0014.1, h0014.2, h00ee.1, h00ee.2, h00fd.1, h00fd.2, h00b5.1, h00b5.2,
    h0125.1, h0125.2, h002d.1, h002d.2, h0116.1, h0116.2,
    sepConj_assoc, arm64_norm]

/-! ## Niche Arithmetic for `Option<PqRatchetState.Inner>` (`noneCap3 = 0xfffffffffffffffd`) -/

@[simp] theorem noneCap3_add_three_beq_zero :
    (0xfffffffffffffffd#64 + 3#64 == 0#64) = true := by decide

@[simp] theorem noneCap3_add_three_bne_zero :
    (0xfffffffffffffffd#64 + 3#64 != 0#64) = false := by decide

@[simp] theorem noneCap2_add_three_beq_zero :
    (0xfffffffffffffffe#64 + 3#64 == 0#64) = false := by decide

@[simp] theorem noneCap2_add_three_bne_zero :
    (0xfffffffffffffffe#64 + 3#64 != 0#64) = true := by decide

@[simp] theorem noneCap_add_three_beq_zero :
    (0xffffffffffffffff#64 + 3#64 == 0#64) = false := by decide

@[simp] theorem noneCap_add_three_bne_zero :
    (0xffffffffffffffff#64 + 3#64 != 0#64) = true := by decide

theorem cap_add_three_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 3#64 == 0#64) = false := by
  have h1 : cap < 0x8000000000000000#64 := (BitVec.lt_def).2 h
  clear h; bv_bits

theorem cap_add_three_bne_zero_true {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 3#64 != 0#64) = true := by
  rw [bne_iff_ne, ne_eq, ← beq_iff_eq, cap_add_three_beq_zero_false h]
  decide

def optCt1SentCap (g : Unchunked5PBGhost) : Option V1State.Unchunked.Ct1Sent → BitVec 64
  | none => noneCap
  | some _ => g.f3.cap

def optCt1SentRest (A : RustAlloc) (g : Unchunked5PBGhost) (p : BitVec 64) :
    Option V1State.Unchunked.Ct1Sent → SepProp
  | none => memRegion (p + 8#64) 120
  | some u =>
    ((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr u.hdr ∗
      vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.es ∗
      vecU8At A (p + 0x30#64) g.f5.cap g.f5.ptr u.ct1 ∗
      optAuthenticatorPBPinnedAt A g.auth (p + 0x48#64) u.auth ∗
      ((p + 0x78#64) ↦₆₄ u.epoch)

theorem optCt1SentPBPinnedAt_eq (A : RustAlloc) (g : Unchunked5PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.Ct1Sent) :
    optCt1SentPBPinnedAt A g p opt =
      (p ↦₆₄ optCt1SentCap g opt) ∗ optCt1SentRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optCt1SentPBPinnedAt, ct1SentPBPinnedAt, unchunked5PinnedAt,
      optCt1SentCap, optCt1SentRest, vecU8At_eq_header_sep_buf A p, vecHeader, sepConj_assoc]

/-- First word (`[a]`) of `v1StateInnerPBPinnedAt A g a is`. -/
def v1StateInnerCap (g : V1StatePBGhost) : V1State.InnerState → BitVec 64
  | .keysUnsampled _ => 0x8000000000000000#64
  | .keysSampled _ => 0x8000000000000001#64
  | .headerSent _ => 0x8000000000000002#64
  | .ct1Received _ => 0x8000000000000003#64
  | .ekSentCt1Received _ => 0x8000000000000004#64
  | .noHeaderReceived _ => 0x8000000000000005#64
  | .headerReceived _ => 0x8000000000000006#64
  | .ct1Sampled v => optCt1SentCap g.b.gCt1Sampled.uc v.uc
  | .ekReceivedCt1Sampled _ => 0x8000000000000008#64
  | .ct1Acknowledged _ => 0x8000000000000009#64
  | .ct2Sampled _ => 0x800000000000000a#64

/-- Remainder of `v1StateInnerPBPinnedAt A g p is` after splitting off `(p ↦₆₄ v1StateInnerCap g is)`. -/
def v1StateInnerRest (A : RustAlloc) (g : V1StatePBGhost) (p : BitVec 64) :
    V1State.InnerState → SepProp
  | .keysUnsampled v =>
    optKeysUnsampledPBPinnedAt A g.a.gKeysUnsampled (p + 8#64) v.uc ∗ memRegion (p + 64#64) 160
  | .keysSampled v =>
    optHeaderSentPBPinnedAt A g.a.gKeysSampled.1 (p + 8#64) v.uc ∗
      optPolynomialEncoderPBPinnedAt A g.a.gKeysSampled.2 (p + 112#64) v.sendingHdr ∗
      memRegion (p + 168#64) 56
  | .headerSent v =>
    chunkedHeaderSentPBPinnedAt A g.a.gHeaderSent (p + 8#64) v ∗ memRegion (p + 184#64) 40
  | .ct1Received v =>
    optEkSentCt1ReceivedPBPinnedAt A g.a.gCt1Received.1 (p + 8#64) v.uc ∗
      optPolynomialEncoderPBPinnedAt A g.a.gCt1Received.2 (p + 112#64) v.sendingEk ∗
      memRegion (p + 168#64) 56
  | .ekSentCt1Received v =>
    optEkSentCt1ReceivedPBPinnedAt A g.a.gEkSentCt1Received.1 (p + 8#64) v.uc ∗
      optPolynomialDecoderPBPinnedAt A g.a.gEkSentCt1Received.2 (p + 112#64) v.receivingCt2 ∗
      memRegion (p + 152#64) 72
  | .noHeaderReceived v =>
    optPolynomialDecoderPBPinnedAt A g.a.gNoHeaderReceived.1 (p + 8#64) v.receivingHdr ∗
      optNoHeaderReceivedPBPinnedAt A g.a.gNoHeaderReceived.2 (p + 48#64) v.uc ∗
      memRegion (p + 104#64) 120
  | .headerReceived v =>
    optHeaderReceivedPBPinnedAt A g.b.gHeaderReceived.1 (p + 8#64) v.uc ∗
      optPolynomialDecoderPBPinnedAt A g.b.gHeaderReceived.2 (p + 88#64) v.receivingEk ∗
      memRegion (p + 128#64) 96
  | .ct1Sampled v =>
    optCt1SentRest A g.b.gCt1Sampled.uc p v.uc ∗
      optPolynomialEncoderPBPinnedAt A g.b.gCt1Sampled.sendingCt1 (p + 128#64) v.sendingCt1 ∗
      optPolynomialDecoderPBPinnedAt A g.b.gCt1Sampled.receivingEk (p + 184#64) v.receivingEk
  | .ekReceivedCt1Sampled v =>
    optCt1SentEkReceivedPBPinnedAt A g.b.gEkReceivedCt1Sampled.1 (p + 8#64) v.uc ∗
      optPolynomialEncoderPBPinnedAt A g.b.gEkReceivedCt1Sampled.2 (p + 136#64) v.sendingCt1 ∗
      memRegion (p + 192#64) 32
  | .ct1Acknowledged v =>
    optCt1SentPBPinnedAt A g.b.gCt1Acknowledged.1 (p + 8#64) v.uc ∗
      optPolynomialDecoderPBPinnedAt A g.b.gCt1Acknowledged.2 (p + 136#64) v.receivingEk ∗
      memRegion (p + 176#64) 48
  | .ct2Sampled v =>
    optPolynomialEncoderPBPinnedAt A g.b.gCt2Sampled.1 (p + 8#64) v.sendingCt2 ∗
      optCt2SentPBPinnedAt A g.b.gCt2Sampled.2 (p + 64#64) v.uc ∗
      memRegion (p + 120#64) 104

theorem v1StateInnerPBPinnedAt_eq (A : RustAlloc) (g : V1StatePBGhost) (p : BitVec 64)
    (is : V1State.InnerState) :
    v1StateInnerPBPinnedAt A g p is =
      (p ↦₆₄ v1StateInnerCap g is) ∗ v1StateInnerRest A g p is := by
  cases is with
  | keysUnsampled _ | keysSampled _ | headerSent _ | ct1Received _
  | ekSentCt1Received _ | noHeaderReceived _ | headerReceived _
  | ekReceivedCt1Sampled _ | ct1Acknowledged _ | ct2Sampled _ =>
    dsimp only [v1StateInnerPBPinnedAt, v1StateInnerCap, v1StateInnerRest]
  | ct1Sampled v =>
    dsimp only [v1StateInnerPBPinnedAt, chunkedCt1SampledPBPinnedAt,
      v1StateInnerCap, v1StateInnerRest]
    rw [optCt1SentPBPinnedAt_eq A g.b.gCt1Sampled.uc p v.uc]
    simp only [sepConj_assoc]

/-- First word (`[a + 128#64]`) of `optPqRatchetInnerPBPinnedAt A g (a + 128#64) opt`. -/
def optPqRatchetInnerCap (g : V1StatePBGhost) : Option PqRatchetState.Inner → BitVec 64
  | none => noneCap3
  | some (.v1 v1) =>
    match v1.innerState with
    | none => noneCap2
    | some is => v1StateInnerCap g is

/-- Remainder (`216` bytes at `p + 8#64`) of `optPqRatchetInnerPBPinnedAt A g p opt` after
splitting off `(p ↦₆₄ optPqRatchetInnerCap g opt)`. -/
def optPqRatchetInnerRest (A : RustAlloc) (g : V1StatePBGhost) (p : BitVec 64) :
    Option PqRatchetState.Inner → SepProp
  | none => memRegion (p + 8#64) 216
  | some (.v1 v1) =>
    match v1.innerState with
    | none => memRegion (p + 8#64) 216
    | some is => v1StateInnerRest A g p is

theorem optPqRatchetInnerPBPinnedAt_eq (A : RustAlloc) (g : V1StatePBGhost) (p : BitVec 64)
    (opt : Option PqRatchetState.Inner) :
    optPqRatchetInnerPBPinnedAt A g p opt =
      (p ↦₆₄ optPqRatchetInnerCap g opt) ∗ optPqRatchetInnerRest A g p opt := by
  cases opt with
  | none => rfl
  | some i =>
    cases i with
    | v1 v1 =>
      rcases v1 with ⟨inner⟩
      cases inner with
      | none => rfl
      | some is =>
        exact v1StateInnerPBPinnedAt_eq A g p is

theorem optPqRatchetInnerRest_cap_bounds {A : RustAlloc} {g : V1StatePBGhost} {p : BitVec 64}
    {opt : Option PqRatchetState.Inner} {R : SepProp} {m : Memory}
    (hm : m ⊨ optPqRatchetInnerRest A g p opt ∗ R) :
    (optPqRatchetInnerCap g opt + 3#64 == 0#64) = !opt.isSome ∧
      (optPqRatchetInnerCap g opt + 3#64 != 0#64) = opt.isSome := by
  cases opt with
  | none =>
    dsimp only [optPqRatchetInnerCap, Option.isSome_none, Bool.not_false]
    exact ⟨by decide, by decide⟩
  | some i =>
    cases i with
    | v1 v1 =>
      rcases v1 with ⟨inner⟩
      cases inner with
      | none =>
        dsimp only [optPqRatchetInnerCap, Option.isSome_some, Bool.not_true]
        exact ⟨by decide, by decide⟩
      | some is =>
        cases is with
        | keysUnsampled _ | keysSampled _ | headerSent _ | ct1Received _
        | ekSentCt1Received _ | noHeaderReceived _ | headerReceived _
        | ekReceivedCt1Sampled _ | ct1Acknowledged _ | ct2Sampled _ =>
          dsimp only [optPqRatchetInnerCap, v1StateInnerCap, Option.isSome_some, Bool.not_true]
          exact ⟨by decide, by decide⟩
        | ct1Sampled v =>
          cases huc : v.uc with
          | none =>
            dsimp only [optPqRatchetInnerCap, v1StateInnerCap, Option.isSome_some, Bool.not_true]
            rw [huc]
            dsimp only [optCt1SentCap]
            exact ⟨by decide, by decide⟩
          | some u =>
            simp only [optPqRatchetInnerRest, v1StateInnerRest, huc, optCt1SentRest] at hm
            have hbuf : m ⊨ EncodedLen.vecU8Buf A g.b.gCt1Sampled.uc.f3.cap g.b.gCt1Sampled.uc.f3.ptr u.hdr ∗
                (((p + 8#64) ↦₆₄ g.b.gCt1Sampled.uc.f3.ptr) ∗
                 ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗
                 vecU8At A (p + 0x18#64) g.b.gCt1Sampled.uc.f4.cap g.b.gCt1Sampled.uc.f4.ptr u.es ∗
                 vecU8At A (p + 0x30#64) g.b.gCt1Sampled.uc.f5.cap g.b.gCt1Sampled.uc.f5.ptr u.ct1 ∗
                 optAuthenticatorPBPinnedAt A g.b.gCt1Sampled.uc.auth (p + 0x48#64) u.auth ∗
                 ((p + 0x78#64) ↦₆₄ u.epoch) ∗
                 optPolynomialEncoderPBPinnedAt A g.b.gCt1Sampled.sendingCt1 (p + 128#64) v.sendingCt1 ∗
                 optPolynomialDecoderPBPinnedAt A g.b.gCt1Sampled.receivingEk (p + 184#64) v.receivingEk ∗ R) := by
              convert hm using 1; ac_rfl
            have ⟨_, hcap⟩ := EncodedLen.vecU8Buf_bounds hbuf
            simp only [optPqRatchetInnerCap, v1StateInnerCap, huc, optCt1SentCap, Option.isSome_some, Bool.not_true]
            exact ⟨cap_add_three_beq_zero_false hcap, cap_add_three_bne_zero_true hcap⟩

theorem optPqRatchetInnerPBPinnedAt_cap_bounds {A : RustAlloc} {g : V1StatePBGhost} {p : BitVec 64}
    {opt : Option PqRatchetState.Inner} {R : SepProp} {m : Memory}
    (hm : m ⊨ optPqRatchetInnerPBPinnedAt A g p opt ∗ R) :
    (optPqRatchetInnerCap g opt + 3#64 == 0#64) = !opt.isSome ∧
      (optPqRatchetInnerCap g opt + 3#64 != 0#64) = opt.isSome := by
  rw [optPqRatchetInnerPBPinnedAt_eq, sepConj_assoc] at hm
  exact optPqRatchetInnerRest_cap_bounds (Satisfies.of_sep_right hm)

/-! ## Stack Frame and Hoare Specifications for `PqRatchetState::encode_to_vec` (`0x6d010`) -/

/-- Callee stack budget below `sp - 144#64`: `176 + resStack`
(which equals `unchunkedMsgEncodeStackOf resStack = msgEnc48RepeatedStackOf resStack = 176 + resStack`
and exceeds all other callees). -/
abbrev encodeToVecCalleeStackOf (resStack : Nat) : Nat :=
  176 + resStack

/-- Total stack budget for `PqRatchetState::encode_to_vec` (`144`B own frame + `176 + resStack` callee frame). -/
abbrev encodeToVecStackOf (resStack : Nat) : Nat :=
  144 + encodeToVecCalleeStackOf resStack

abbrev encodeToVecStack : Nat := encodeToVecStackOf 0x40
abbrev encodeToVecStackX : Nat := encodeToVecStackOf doReserveStackX

/-- Saved callee-saved registers (`fp, lr, x28..x19`) at `[sp - 96#64, sp)` (`[s.sp + 0x30, s.sp + 0x90)`). -/
def encodeToVecSavedRegs (sp : BitVec 64) (s0 : State) : SepProp :=
  ((sp - 96#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 88#64) ↦₆₄ s0.readReg64 .lr) ∗
  ((sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗ ((sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
  ((sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗ ((sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
  ((sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗ ((sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
  ((sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
  ((sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

/-- Pinned ghost arguments for `PqRatchetState::encode_to_vec` (`0x6d010`):
- `sret`: pointer to output `Vec<u8>` header (`x8`, `24` bytes),
- `a`: pointer to `&PqRatchetState` (`x0`, `352` bytes),
- `g`: pinned `(cap, ptr)` ghost state of `PqRatchetState`,
- `st`: pure `PqRatchetState` value. -/
structure PqRatchetStateEncodeToVecPinnedGhost where
  sret : BitVec 64
  a : BitVec 64
  g : PqRatchetStatePBGhost
  st : PqRatchetState

/-- Unpinned ghost arguments for `PqRatchetState::encode_to_vec` (`0x6d010`). -/
structure PqRatchetStateEncodeToVecGhost where
  sret : BitVec 64
  a : BitVec 64
  st : PqRatchetState

/-- Pinned specification of `PqRatchetState::encode_to_vec` (`0x6d010`) with explicit `.rodata`
jump tables at `b + 0xa145a` (11 bytes, for `V1State::encoded_len`) and `b + 0xa1480` (22 bytes,
for `V1State` variant dispatch in `encode_to_vec`).
Precondition bound `(PqRatchetState.encodeRaw x.st).length < 2 ^ 63`: discharged by callers
`spqr::send` and `spqr::recv` via `send_state_len_lt` / `recv_state_len_lt` in `StateSize.lean`. -/
def pqRatchetStateEncodeToVecRoPinnedSpecOf (resStack : Nat) (b : BitVec 64) (A : RustAlloc) :
    Spec PqRatchetStateEncodeToVecPinnedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.sret ∧
      s.readReg64 .x1 = x.a ∧
      (PqRatchetState.encodeRaw x.st).length < 2 ^ 63⌝ ∗
      memRegion x.sret 24 ∗
      pqRatchetStatePBPinnedAt A x.g x.a x.st ∗
      ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
      ((b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) ↦ᵣ encodeToVecJumpTableBytes) ∗
      A.pool ∗ stackAt s.sp (encodeToVecStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8 A x.sret (PqRatchetState.encodeRaw x.st) ∗
      pqRatchetStatePBPinnedAt A x.g x.a x.st ∗
      ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
      ((b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) ↦ᵣ encodeToVecJumpTableBytes) ∗
      A.pool ∗ stackAt s0.sp (encodeToVecStackOf resStack)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Pinned specification of `PqRatchetState::encode_to_vec` (`0x6d010`) without `.rodata`
in the footprint (for `_ok_ext_x` after discharging `.rodata` via `of_rodata_loads`). -/
def pqRatchetStateEncodeToVecPinnedSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec PqRatchetStateEncodeToVecPinnedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.sret ∧
      s.readReg64 .x1 = x.a ∧
      (PqRatchetState.encodeRaw x.st).length < 2 ^ 63⌝ ∗
      memRegion x.sret 24 ∗
      pqRatchetStatePBPinnedAt A x.g x.a x.st ∗
      A.pool ∗ stackAt s.sp (encodeToVecStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8 A x.sret (PqRatchetState.encodeRaw x.st) ∗
      pqRatchetStatePBPinnedAt A x.g x.a x.st ∗
      A.pool ∗ stackAt s0.sp (encodeToVecStackOf resStack)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Unpinned specification of `PqRatchetState::encode_to_vec` (`0x6d010`) with `.rodata`. -/
def pqRatchetStateEncodeToVecRoSpecOf (resStack : Nat) (b : BitVec 64) (A : RustAlloc) :
    Spec PqRatchetStateEncodeToVecGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.sret ∧
      s.readReg64 .x1 = x.a ∧
      (PqRatchetState.encodeRaw x.st).length < 2 ^ 63⌝ ∗
      memRegion x.sret 24 ∗
      pqRatchetStatePBAt A x.a x.st ∗
      ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
      ((b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) ↦ᵣ encodeToVecJumpTableBytes) ∗
      A.pool ∗ stackAt s.sp (encodeToVecStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8 A x.sret (PqRatchetState.encodeRaw x.st) ∗
      pqRatchetStatePBAt A x.a x.st ∗
      ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
      ((b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) ↦ᵣ encodeToVecJumpTableBytes) ∗
      A.pool ∗ stackAt s0.sp (encodeToVecStackOf resStack)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Unpinned specification of `PqRatchetState::encode_to_vec` (`0x6d010`) without `.rodata`
(for `_ok_ext_x` in `inImage libsignalSessionCode`). -/
def pqRatchetStateEncodeToVecSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec PqRatchetStateEncodeToVecGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.sret ∧
      s.readReg64 .x1 = x.a ∧
      (PqRatchetState.encodeRaw x.st).length < 2 ^ 63⌝ ∗
      memRegion x.sret 24 ∗
      pqRatchetStatePBAt A x.a x.st ∗
      A.pool ∗ stackAt s.sp (encodeToVecStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8 A x.sret (PqRatchetState.encodeRaw x.st) ∗
      pqRatchetStatePBAt A x.a x.st ∗
      A.pool ∗ stackAt s0.sp (encodeToVecStackOf resStack)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev pqRatchetStateEncodeToVecRoPinnedSpec (b : BitVec 64) (A : RustAlloc) :
    Spec PqRatchetStateEncodeToVecPinnedGhost :=
  pqRatchetStateEncodeToVecRoPinnedSpecOf 0x40 b A

abbrev pqRatchetStateEncodeToVecRoPinnedSpecX (b : BitVec 64) (A : RustAlloc) :
    Spec PqRatchetStateEncodeToVecPinnedGhost :=
  pqRatchetStateEncodeToVecRoPinnedSpecOf doReserveStackX b A

abbrev pqRatchetStateEncodeToVecPinnedSpecX (A : RustAlloc) :
    Spec PqRatchetStateEncodeToVecPinnedGhost :=
  pqRatchetStateEncodeToVecPinnedSpecOf doReserveStackX A

abbrev pqRatchetStateEncodeToVecRoSpec (b : BitVec 64) (A : RustAlloc) :
    Spec PqRatchetStateEncodeToVecGhost :=
  pqRatchetStateEncodeToVecRoSpecOf 0x40 b A

abbrev pqRatchetStateEncodeToVecRoSpecX (b : BitVec 64) (A : RustAlloc) :
    Spec PqRatchetStateEncodeToVecGhost :=
  pqRatchetStateEncodeToVecRoSpecOf doReserveStackX b A

abbrev pqRatchetStateEncodeToVecSpecX (A : RustAlloc) :
    Spec PqRatchetStateEncodeToVecGhost :=
  pqRatchetStateEncodeToVecSpecOf doReserveStackX A

def PqRatchetStateEncodeToVecRoPinnedOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrProgAtExt b ext)
    ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName)
    (pqRatchetStateEncodeToVecRoPinnedSpec b A)

def PqRatchetStateEncodeToVecRoOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrProgAtExt b ext)
    ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName)
    (pqRatchetStateEncodeToVecRoSpec b A)

def PqRatchetStateEncodeToVecPinnedOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrProgAtExt img.base ext)
    ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName)
    ((pqRatchetStateEncodeToVecPinnedSpecX A).inImage img)

def PqRatchetStateEncodeToVecOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrProgAtExt img.base ext)
    ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName)
    ((pqRatchetStateEncodeToVecSpecX A).inImage img)

/-! ## Local Stack Slots and Frame Splitting Helpers -/

/-- The 6 local 64-bit stack slots at `[sp - 144#64, sp - 96#64)` (`[s.sp, s.sp + 0x30)`). -/
def encodeToVecLocalSlots (sp v0 v1 v2 v3 v4 v5 : BitVec 64) : SepProp :=
  ((sp - 144#64) ↦₆₄ v0) ∗ ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗
  ((sp - 120#64) ↦₆₄ v3) ∗ ((sp - 112#64) ↦₆₄ v4) ∗ ((sp - 104#64) ↦₆₄ v5)

theorem sp_sub_144_aligned {sp : BitVec 64} (h : sp &&& 15#64 = 0#64) :
    (sp - 144#64) &&& 15#64 = 0#64 := by
  revert h; bv_bits

theorem stackAt_encodeToVec_split {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp (encodeToVecStackOf resStack) =
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
         ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
          encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5) ∗
        cells (sp - 96#64) 12 := by
  have h1 := ProofLib.stackAt_split_cells sp (encodeToVecCalleeStackOf resStack + 48) 12
    (by dsimp [encodeToVecCalleeStackOf]; omega)
  have heq1 : (encodeToVecCalleeStackOf resStack + 48) + 8 * 12 = encodeToVecStackOf resStack := by
    dsimp [encodeToVecStackOf, encodeToVecCalleeStackOf]; omega
  rw [heq1] at h1
  have h2 := ProofLib.stackAt_split_cells (sp - 96#64) (encodeToVecCalleeStackOf resStack) 6
    (by dsimp [encodeToVecCalleeStackOf]; omega)
  have heq2 : encodeToVecCalleeStackOf resStack + 8 * 6 = encodeToVecCalleeStackOf resStack + 48 := by omega
  have hsp144 : sp - 96#64 - 48#64 = sp - 144#64 := by bv_omega
  rw [heq2, hsp144] at h2
  have hc6 : cells (sp - 144#64) 6 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
       ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5) := by
    unfold encodeToVecLocalSlots
    cells_unfold
  rw [h1, h2, hc6, sepConj_assoc]

theorem cells_12_sub_96_eq (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      (∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, ∃∗ r2 : BitVec 64, ∃∗ r3 : BitVec 64,
       ∃∗ r4 : BitVec 64, ∃∗ r5 : BitVec 64, ∃∗ r6 : BitVec 64, ∃∗ r7 : BitVec 64,
       ∃∗ r8 : BitVec 64, ∃∗ r9 : BitVec 64, ∃∗ r10 : BitVec 64, ∃∗ r11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ r0) ∗ ((sp - 88#64) ↦₆₄ r1) ∗ ((sp - 80#64) ↦₆₄ r2) ∗
        ((sp - 72#64) ↦₆₄ r3) ∗ ((sp - 64#64) ↦₆₄ r4) ∗ ((sp - 56#64) ↦₆₄ r5) ∗
        ((sp - 48#64) ↦₆₄ r6) ∗ ((sp - 40#64) ↦₆₄ r7) ∗ ((sp - 32#64) ↦₆₄ r8) ∗
        ((sp - 24#64) ↦₆₄ r9) ∗ ((sp - 16#64) ↦₆₄ r10) ∗ ((sp - 8#64) ↦₆₄ r11)) := by
  cells_unfold

theorem encodeToVecSavedRegs_entails_cells (sp : BitVec 64) (s0 : State) :
    encodeToVecSavedRegs sp s0 ⊢ cells (sp - 96#64) 12 := by
  rw [cells_12_sub_96_eq]
  unfold encodeToVecSavedRegs
  exact Entails.sepExists_right (s0.readReg64 .fp)
    (Entails.sepExists_right (s0.readReg64 .lr)
    (Entails.sepExists_right (s0.readReg64 (Reg.gpr 28#5))
    (Entails.sepExists_right (s0.readReg64 (Reg.gpr 27#5))
    (Entails.sepExists_right (s0.readReg64 (Reg.gpr 26#5))
    (Entails.sepExists_right (s0.readReg64 (Reg.gpr 25#5))
    (Entails.sepExists_right (s0.readReg64 (Reg.gpr 24#5))
    (Entails.sepExists_right (s0.readReg64 (Reg.gpr 23#5))
    (Entails.sepExists_right (s0.readReg64 (Reg.gpr 22#5))
    (Entails.sepExists_right (s0.readReg64 (Reg.gpr 21#5))
    (Entails.sepExists_right (s0.readReg64 (Reg.gpr 20#5))
    (Entails.sepExists_right (s0.readReg64 (Reg.gpr 19#5)) (Entails.refl _))))))))))))

theorem encodeToVecLocalSlots_entails_exists (sp v0 v1 v2 v3 v4 v5 : BitVec 64) :
    encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ⊢
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
       ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        encodeToVecLocalSlots sp w0 w1 w2 w3 w4 w5) :=
  Entails.sepExists_right v0
    (Entails.sepExists_right v1
    (Entails.sepExists_right v2
    (Entails.sepExists_right v3
    (Entails.sepExists_right v4
    (Entails.sepExists_right v5 (Entails.refl _))))))

theorem stackAt_encodeToVec_recombine {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (sp v0 v1 v2 v3 v4 v5 : BitVec 64) (s0 : State) :
    stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
      encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
      encodeToVecSavedRegs sp s0 ⊢
      stackAt sp (encodeToVecStackOf resStack) := by
  rw [stackAt_encodeToVec_split hres sp]
  exact sepConj_mono_right
    (sepConj_mono (encodeToVecLocalSlots_entails_exists sp v0 v1 v2 v3 v4 v5)
      (encodeToVecSavedRegs_entails_cells sp s0))

theorem stackAt_callee_eq_encodeRepeated {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (sp1 : BitVec 64) :
    stackAt sp1 (encodeToVecCalleeStackOf resStack) =
      memRegion (sp1 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) 48 ∗
        stackAt sp1 (0x80 + resStack) := by
  have h := ProofLib.stackAt_split_bottom sp1 (0x80 + resStack) 48 (by omega)
  have heq : (0x80 + resStack) + 48 = encodeToVecCalleeStackOf resStack := by
    dsimp [encodeToVecCalleeStackOf]; omega
  simpa only [heq] using h

theorem stackAt_callee_eq_authEncode {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (sp1 : BitVec 64) :
    stackAt sp1 (encodeToVecCalleeStackOf resStack) =
      memRegion (sp1 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) 64 ∗
        stackAt sp1 (0x70 + resStack) := by
  have h := ProofLib.stackAt_split_bottom sp1 (0x70 + resStack) 64 (by omega)
  have heq : (0x70 + resStack) + 64 = encodeToVecCalleeStackOf resStack := by
    dsimp [encodeToVecCalleeStackOf]; omega
  simpa only [heq] using h

theorem stackAt_callee_eq_msgEnc48Varint {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (sp1 : BitVec 64) :
    stackAt sp1 (encodeToVecCalleeStackOf resStack) =
      memRegion (sp1 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) 80 ∗
        stackAt sp1 (48 + (0x30 + resStack)) := by
  have h := ProofLib.stackAt_split_bottom sp1 (48 + (0x30 + resStack)) 80 (by omega)
  have heq : (48 + (0x30 + resStack)) + 80 = encodeToVecCalleeStackOf resStack := by
    dsimp [encodeToVecCalleeStackOf]; omega
  simpa only [heq] using h

theorem stackAt_callee_eq_encodeVarint {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (sp1 : BitVec 64) :
    stackAt sp1 (encodeToVecCalleeStackOf resStack) =
      memRegion (sp1 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) 128 ∗
        stackAt sp1 (0x30 + resStack) := by
  have h := ProofLib.stackAt_split_bottom sp1 (0x30 + resStack) 128 (by omega)
  have heq : (0x30 + resStack) + 128 = encodeToVecCalleeStackOf resStack := by
    dsimp [encodeToVecCalleeStackOf]; omega
  simpa only [heq] using h

theorem stackAt_callee_eq_resStack {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (sp1 : BitVec 64) :
    stackAt sp1 (encodeToVecCalleeStackOf resStack) =
      memRegion (sp1 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) 176 ∗
        stackAt sp1 resStack := by
  have h := ProofLib.stackAt_split_bottom sp1 resStack 176 (by omega)
  have heq : resStack + 176 = encodeToVecCalleeStackOf resStack := by
    dsimp [encodeToVecCalleeStackOf]; omega
  simpa only [heq] using h

theorem stackAt_callee_eq_v1StateEncodedLen {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (sp1 : BitVec 64) :
    stackAt sp1 (encodeToVecCalleeStackOf resStack) =
      memRegion (sp1 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (96 + resStack) ∗
        stackAt sp1 v1StateEncodedLenStack := by
  have h80 : v1StateEncodedLenStack = 80 := rfl
  have h := ProofLib.stackAt_split_bottom sp1 v1StateEncodedLenStack (96 + resStack)
    (by rw [h80]; omega)
  have heq : v1StateEncodedLenStack + (96 + resStack) = encodeToVecCalleeStackOf resStack := by
    rw [h80]; dsimp [encodeToVecCalleeStackOf]; omega
  simpa only [heq] using h

theorem stackAt_callee_eq_chainEncodedLen {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (sp1 : BitVec 64) :
    stackAt sp1 (encodeToVecCalleeStackOf resStack) =
      memRegion (sp1 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (80 + resStack) ∗
        stackAt sp1 0x60 := by
  have h := ProofLib.stackAt_split_bottom sp1 0x60 (80 + resStack) (by omega)
  have heq : 0x60 + (80 + resStack) = encodeToVecCalleeStackOf resStack := by
    dsimp [encodeToVecCalleeStackOf]; omega
  simpa only [heq] using h

theorem stackAt_callee_eq_unchunkedEncodedLen {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (sp1 : BitVec 64) :
    stackAt sp1 (encodeToVecCalleeStackOf resStack) =
      memRegion (sp1 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (160 + resStack) ∗
        stackAt sp1 unchunkedEncodedLenStack := by
  have h16 : unchunkedEncodedLenStack = 16 := rfl
  have h := ProofLib.stackAt_split_bottom sp1 unchunkedEncodedLenStack (160 + resStack)
    (by rw [h16]; omega)
  have heq : unchunkedEncodedLenStack + (160 + resStack) = encodeToVecCalleeStackOf resStack := by
    rw [h16]; dsimp [encodeToVecCalleeStackOf]; omega
  simpa only [heq] using h

/-! ## Shared `SepWPp` & Option Representation Helpers -/

/-- Extract a pure fact `φ` from `s.mem ⊨ P ∗ R` inside `SepWPp`. -/
theorem sepWPp_extract_pure {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} (φ : Prop)
    (hφ : ∀ R : SepProp, s.mem ⊨ P ∗ R → φ)
    (hnext : φ → SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q Qp :=
  fun R hm hL => hnext (hφ R hm) R hm hL

class VRegsAt (s0 s : State) : Prop where
  eq : calleeSavedVRegs s = calleeSavedVRegs s0

theorem calleeSavedVRegs_applyWriteback (s : State) (wb : Option (Reg × BitVec 64)) :
    calleeSavedVRegs (ProofLib.applyWriteback s wb) = calleeSavedVRegs s := by
  cases wb with
  | none => rfl
  | some p => exact calleeSavedVRegs_writeReg64 s p.1 p.2

instance (s : State) : VRegsAt s s := ⟨rfl⟩
instance (priority := 100) {s0 sm : State} [hv : VRegsAt s0 sm] : VRegsAt s0.advancePC sm :=
  ⟨hv.eq.trans (calleeSavedVRegs_advancePC s0).symm⟩
instance (priority := 100) {s0 sm : State} (pc : BitVec 64) [hv : VRegsAt s0 sm] :
    VRegsAt (s0.setPC pc) sm :=
  ⟨hv.eq.trans (calleeSavedVRegs_setPC s0 pc).symm⟩
instance (priority := 100) {s0 sm : State} (m : Memory) [hv : VRegsAt s0 sm] :
    VRegsAt (s0.setMem m) sm :=
  ⟨hv.eq.trans (calleeSavedVRegs_setMem s0 m).symm⟩
instance (priority := 100) {s0 sm : State} (ps : PState) [hv : VRegsAt s0 sm] :
    VRegsAt (s0.setPState ps) sm :=
  ⟨hv.eq.trans (calleeSavedVRegs_setPState s0 ps).symm⟩
instance (priority := 100) {s0 sm : State} (r : Reg) (val : BitVec 64) [hv : VRegsAt s0 sm] :
    VRegsAt (s0.writeReg64 r val) sm :=
  ⟨hv.eq.trans (calleeSavedVRegs_writeReg64 s0 r val).symm⟩
instance (priority := 100) {s0 sm : State} (r : Reg) (val : BitVec 32) [hv : VRegsAt s0 sm] :
    VRegsAt (s0.writeReg32 r val) sm :=
  ⟨hv.eq.trans (calleeSavedVRegs_writeReg32 s0 r val).symm⟩
instance {s0 s : State} [hv : VRegsAt s0 s] : VRegsAt s0 s.advancePC :=
  ⟨(calleeSavedVRegs_advancePC s).trans hv.eq⟩
instance {s0 s : State} (pc : BitVec 64) [hv : VRegsAt s0 s] : VRegsAt s0 (s.setPC pc) :=
  ⟨(calleeSavedVRegs_setPC s pc).trans hv.eq⟩
instance {s0 s : State} (m : Memory) [hv : VRegsAt s0 s] : VRegsAt s0 (s.setMem m) :=
  ⟨(calleeSavedVRegs_setMem s m).trans hv.eq⟩
instance {s0 s : State} (ps : PState) [hv : VRegsAt s0 s] : VRegsAt s0 (s.setPState ps) :=
  ⟨(calleeSavedVRegs_setPState s ps).trans hv.eq⟩
instance {s0 s : State} (r : Reg) (val : BitVec 64) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeReg64 r val) :=
  ⟨(calleeSavedVRegs_writeReg64 s r val).trans hv.eq⟩
instance {s0 s : State} (r : Reg) (val : BitVec 32) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeReg32 r val) :=
  ⟨(calleeSavedVRegs_writeReg32 s r val).trans hv.eq⟩
instance {s0 s : State} (w : Width) (r : Reg) (val : BitVec 64) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeReg w r val) :=
  ⟨(calleeSavedVRegs_writeReg s w r val).trans hv.eq⟩
instance {s0 s : State} (wb : Option (Reg × BitVec 64)) [hv : VRegsAt s0 s] :
    VRegsAt s0 (ProofLib.applyWriteback s wb) :=
  ⟨(calleeSavedVRegs_applyWriteback s wb).trans hv.eq⟩
instance {s0 s : State} (val : BitVec 128) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg128 0#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg128 s 0#5 val rfl).trans hv.eq⟩
instance {s0 s : State} (val : BitVec 128) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg128 1#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg128 s 1#5 val rfl).trans hv.eq⟩
instance {s0 s : State} (val : BitVec 128) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg128 2#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg128 s 2#5 val rfl).trans hv.eq⟩
instance {s0 s : State} (val : BitVec 128) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg128 3#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg128 s 3#5 val rfl).trans hv.eq⟩
instance {s0 s : State} (val : BitVec 128) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg128 4#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg128 s 4#5 val rfl).trans hv.eq⟩
instance {s0 s : State} (val : BitVec 128) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg128 5#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg128 s 5#5 val rfl).trans hv.eq⟩
instance {s0 s : State} (val : BitVec 128) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg128 6#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg128 s 6#5 val rfl).trans hv.eq⟩
instance {s0 s : State} (val : BitVec 128) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg128 7#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg128 s 7#5 val rfl).trans hv.eq⟩
instance {s0 s : State} (val : BitVec 64) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg64 0#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg64 s 0#5 val rfl).trans hv.eq⟩
instance {s0 s : State} (val : BitVec 64) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg64 1#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg64 s 1#5 val rfl).trans hv.eq⟩
instance {s0 s : State} (val : BitVec 64) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg64 2#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg64 s 2#5 val rfl).trans hv.eq⟩
instance {s0 s : State} (val : BitVec 64) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg64 3#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg64 s 3#5 val rfl).trans hv.eq⟩
instance {s0 s : State} (val : BitVec 64) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg64 4#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg64 s 4#5 val rfl).trans hv.eq⟩
instance {s0 s : State} (val : BitVec 64) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg64 5#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg64 s 5#5 val rfl).trans hv.eq⟩
instance {s0 s : State} (val : BitVec 64) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg64 6#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg64 s 6#5 val rfl).trans hv.eq⟩
instance {s0 s : State} (val : BitVec 64) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg64 7#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg64 s 7#5 val rfl).trans hv.eq⟩
instance {s0 s : State} (val : BitVec 32) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg32 0#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg32 s 0#5 val rfl).trans hv.eq⟩
instance {s0 s : State} (val : BitVec 32) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg32 1#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg32 s 1#5 val rfl).trans hv.eq⟩
instance {s0 s : State} (val : BitVec 32) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg32 2#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg32 s 2#5 val rfl).trans hv.eq⟩
instance {s0 s : State} (val : BitVec 32) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg32 3#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg32 s 3#5 val rfl).trans hv.eq⟩
instance {s0 s : State} (val : BitVec 32) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg32 4#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg32 s 4#5 val rfl).trans hv.eq⟩
instance {s0 s : State} (val : BitVec 32) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg32 5#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg32 s 5#5 val rfl).trans hv.eq⟩
instance {s0 s : State} (val : BitVec 32) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg32 6#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg32 s 6#5 val rfl).trans hv.eq⟩
instance {s0 s : State} (val : BitVec 32) [hv : VRegsAt s0 s] :
    VRegsAt s0 (s.writeVReg32 7#5 val) :=
  ⟨(calleeSavedVRegs_writeVReg32 s 7#5 val rfl).trans hv.eq⟩

class SepWPDonePost (s : State) (P : SepProp) (post : State → SepProp → Prop) (G : outParam Prop) : Prop where
  toPost : G → post s P

instance (priority := 1000) {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    [hv : VRegsAt s0 s] :
    SepWPDonePost s P (fun sf Pf => VRegsAt s0 sf ∧ Q sf Pf) (Q s P) :=
  ⟨fun h => ⟨hv, h⟩⟩

instance (priority := 100) {s : State} {P : SepProp} {post : State → SepProp → Prop} :
    SepWPDonePost s P post (post s P) :=
  ⟨id⟩

theorem SepWP.done {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop} {G : Prop}
    [hd : SepWPDonePost s P post G]
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (hpost : G) :
    ProofLib.SepWP prog target_pc s P post :=
  ProofLib.SepWP.done hpc hrun (hd.toPost hpost)

abbrev StepInv (s s' : State) : Prop :=
  (∀ img : Obj.Image, img.FrozenLoaded s → img.FrozenLoaded s') ∧ s'.symtab = s.symtab ∧
    calleeSavedVRegs s' = calleeSavedVRegs s

theorem StepInv.refl (s : State) : StepInv s s :=
  ⟨fun _ h => h, rfl, rfl⟩

theorem StepInv.trans {s0 s1 s2 : State} (h1 : StepInv s0 s1) (h2 : StepInv s1 s2) :
    StepInv s0 s2 :=
  ⟨fun img h => h2.1 img (h1.1 img h), h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem StepInv.of_steps {prog : Program} {s s' : State} (hs : Steps prog s s')
    (hv : calleeSavedVRegs s' = calleeSavedVRegs s) : StepInv s s' :=
  ⟨fun _ h => h.of_keepsFrozen hs.keepsFrozen, hs.symtab_eq, hv⟩

theorem SepWPp.of_sepWP_cs {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ProofLib.SepWP prog mid s P (fun sm Pm =>
      VRegsAt s sm ∧ (StepInv s sm → SepWPp prog ret sm Pm Q Qp))) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hv, hnext⟩ | ⟨hoom, hfalse⟩⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ := hnext (StepInv.of_steps hsteps hv.eq) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom, hfalse⟩)⟩

theorem SepWPp.call_cs {α : Type} {prog : Program} {entry ret ret_pc : BitVec 64}
    {spec : Spec α} {x : α} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R, s.mem ⊨ P ∗ R → s.mem ⊨ spec.pre x s ∗ (F ∗ R))
    (hexit : ∀ sf code R, sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R) → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running → sm.sp = s.sp →
      CalleeSavedPreserved s sm → StepInv s sm →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun (hpre R hm) hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpan_mem⟩ | ⟨code, hex, hex_mem⟩ | ⟨hoom_sm, hoom_mem⟩
  · rw [hlr] at hpcm
    rw [← sepConj_assoc] at hpost
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (StepInv.of_steps hsteps hcsm.2.2.2.2.2.2.2.2.2.2.2) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpan_mem
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpan_mem, hpanic sm hpan⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hex_mem).elim
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_sm, hoom sm R hoom_sm hoom_mem⟩)⟩

namespace DoReserveNorm

@[simp, arm64_norm] theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := rfl

end DoReserveNorm

theorem allowPanic_not_exited {m : Memory} {R : SepProp}
    (hm : m ⊨ ⌜False⌝ ∗ R) : False := by
  rw [satisfies_pure_sepConj] at hm
  exact hm.1

/-- Wrap a `Spec α` with `⌜StepInv s0 s⌝` in the precondition so `_x` (`inImage img`) callers
can discharge the image invariant at `s` from `s0` and `StepInv s0 s`. -/
def withStepInv {α : Type} (s0 : State) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜StepInv s0 s⌝ ∗ spec.pre x s }

theorem subroutine_ok_withStepInv {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (s0 : State) (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withStepInv s0 spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s hpc hrun hpre hsp
  rw [withStepInv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact (h.to_outcome x R s hpc hrun hpre.2 hsp).mono_outcome (fun _ hout => hout)

theorem encodeToVec_chainEncodedLen_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry) :
    entry + 18446744073709533056#64 =
      (spqrProgAtExt b ext).fnAddr chainEncodedLenLocal2Name := by
  subst hfn
  have h1 := libsignalSessionCode_fnOff_0x67c18
  have h2 := libsignalSessionCode_fnOff_0x63398
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVecName, chainEncodedLenLocal2Name, h1, h2]
  bv_omega

theorem encodeToVec_v1StateEncodedLen_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry) :
    entry + 18446744073709530600#64 =
      (spqrProgAtExt b ext).fnAddr v1StateEncodedLenLocal2Name := by
  subst hfn
  have h1 := libsignalSessionCode_fnOff_0x67c18
  have h2 := libsignalSessionCode_fnOff_0x62a00
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVecName, v1StateEncodedLenLocal2Name, h1, h2]
  bv_omega

/-- First word (`[a]`) of `optVersionNegotiationPBPinnedAt A g a opt`. -/
def optVersionNegCap (g : VersionNegotiationPBGhost) : Option VersionNegotiationPB → BitVec 64
  | none => noneCap
  | some _ => g.authKey.cap

/-- Remainder (`40` bytes at `a + 8#64`) of `versionNegotiationPBPinnedAt A g a vn` after
splitting off `(a ↦₆₄ g.authKey.cap)`. -/
def versionNegotiationRest (A : RustAlloc) (g : VersionNegotiationPBGhost) (a : BitVec 64)
    (vn : VersionNegotiationPB) : SepProp :=
  ((a + 8#64) ↦₆₄ g.authKey.ptr) ∗
    ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
    EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey ∗
    optChainParamsPBAt (a + 24#64) vn.chainParams ∗
    ((a + 36#64) ↦₃₂ vn.direction) ∗
    ((a + 40#64) ↦₃₂ vn.minVersion) ∗
    memRegion (a + 44#64) 4

/-- Remainder of `optVersionNegotiationPBPinnedAt A g a opt` after splitting off `(a ↦₆₄ optVersionNegCap g opt)`. -/
def optVersionNegRest (A : RustAlloc) (g : VersionNegotiationPBGhost) (a : BitVec 64) :
    Option VersionNegotiationPB → SepProp
  | none => memRegion (a + 8#64) 40
  | some vn => versionNegotiationRest A g a vn

theorem optVersionNegotiationPBPinnedAt_eq (A : RustAlloc) (g : VersionNegotiationPBGhost)
    (a : BitVec 64) (opt : Option VersionNegotiationPB) :
    optVersionNegotiationPBPinnedAt A g a opt =
      (a ↦₆₄ optVersionNegCap g opt) ∗ optVersionNegRest A g a opt := by
  cases opt with
  | none => rfl
  | some vn =>
    dsimp only [optVersionNegotiationPBPinnedAt, versionNegotiationPBPinnedAt,
      optVersionNegCap, optVersionNegRest, versionNegotiationRest]
    rw [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]
    ac_rfl

theorem optVersionNegRest_cap_bounds {A : RustAlloc} {g : VersionNegotiationPBGhost} {p : BitVec 64}
    {opt : Option VersionNegotiationPB} {R : SepProp} {m : Memory}
    (hm : m ⊨ optVersionNegRest A g p opt ∗ R) :
    (optVersionNegCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optVersionNegCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none =>
    dsimp only [optVersionNegCap, Option.isSome_none, Bool.not_false]
    exact ⟨by decide, by decide⟩
  | some vn =>
    simp only [optVersionNegRest, versionNegotiationRest] at hm
    have hbuf : m ⊨ EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey ∗
        (((p + 8#64) ↦₆₄ g.authKey.ptr) ∗
         ((p + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
         optChainParamsPBAt (p + 24#64) vn.chainParams ∗
         ((p + 36#64) ↦₃₂ vn.direction) ∗
         ((p + 40#64) ↦₃₂ vn.minVersion) ∗
         memRegion (p + 44#64) 4 ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := EncodedLen.vecU8Buf_bounds hbuf
    dsimp only [optVersionNegCap, Option.isSome_some, Bool.not_true]
    exact ⟨EncodedLen.cap_add_one_beq_zero_false hcap, EncodedLen.cap_add_one_bne_zero_true hcap⟩

/-- First word (`[a]`) of `optChainPBPinnedAt A g a opt`. -/
def optChainCap (g : ChainPBGhost) : Option ChainPB → BitVec 64
  | none => noneCap
  | some _ => g.links.cap

/-- Heap buffer of `Vec<ChainEpochPB>` (element stride `112`, align `8`) detached from its 24-byte `vecHeader`. -/
def vecEpochBuf (A : RustAlloc) (cap ptr : BitVec 64) (links : List ChainEpochPB) : SepProp :=
  vecBuf A chainEpochPBSize 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr links

theorem vecEpochBuf_eq_of_ne_zero {A : RustAlloc} {cap ptr : BitVec 64} {links : List ChainEpochPB}
    (hcap : cap ≠ 0) :
    vecEpochBuf A cap ptr links =
      arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr links ∗
        (⌜links.length ≤ cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          A.live ptr (cap.toNat * 112) 8 ∗
          memRegion (ptr + BitVec.ofNat 64 (links.length * 112)) ((cap.toNat - links.length) * 112)) := by
  unfold vecEpochBuf vecBuf chainEpochPBSize
  simp only [hcap, ↓reduceIte]
  ac_rfl

/-- Remainder of `chainLinksVecPinnedAt A pin v links` after splitting off `(v ↦₆₄ pin.cap)`. -/
def chainLinksVecBuf (A : RustAlloc) (pin : VecPin) (v : BitVec 64)
    (links : List ChainEpochPB) : SepProp :=
  ((v + 8#64) ↦₆₄ pin.ptr) ∗
    ((v + 16#64) ↦₆₄ BitVec.ofNat 64 links.length) ∗
    vecEpochBuf A pin.cap pin.ptr links

/-- Remainder (`72` bytes at `a + 8#64`) of `chainPBPinnedAt A g a ch` after splitting off `(a ↦₆₄ g.links.cap)`. -/
def chainRest (A : RustAlloc) (g : ChainPBGhost) (a : BitVec 64) (ch : ChainPB) : SepProp :=
  chainLinksVecBuf A g.links a ch.links ∗
    vecU8At A (a + 0x18#64) g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
    ((a + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
    ((a + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
    optChainParamsPBAt (a + 0x40#64) ch.params ∗
    ((a + 0x4c#64) ↦₃₂ ch.direction)

/-- Remainder of `optChainPBPinnedAt A g a opt` after splitting off `(a ↦₆₄ optChainCap g opt)`. -/
def optChainRest (A : RustAlloc) (g : ChainPBGhost) (a : BitVec 64) :
    Option ChainPB → SepProp
  | none => memRegion (a + 8#64) 72
  | some ch => chainRest A g a ch

theorem optChainPBPinnedAt_eq (A : RustAlloc) (g : ChainPBGhost) (a : BitVec 64)
    (opt : Option ChainPB) :
    optChainPBPinnedAt A g a opt =
      (a ↦₆₄ optChainCap g opt) ∗ optChainRest A g a opt := by
  cases opt with
  | none => rfl
  | some ch =>
    dsimp only [optChainPBPinnedAt, chainPBPinnedAt, chainLinksVecPinnedAt, chainEpochPBSize,
      vecAt, vecHeader, optChainCap, optChainRest, chainRest, chainLinksVecBuf, vecEpochBuf]
    ac_rfl

theorem optChainRest_cap_bounds {A : RustAlloc} {g : ChainPBGhost} {p : BitVec 64}
    {opt : Option ChainPB} {R : SepProp} {m : Memory}
    (hm : m ⊨ optChainRest A g p opt ∗ R) :
    (optChainCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optChainCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none =>
    dsimp only [optChainCap, Option.isSome_none, Bool.not_false]
    exact ⟨by decide, by decide⟩
  | some ch =>
    have hcap : g.links.cap.toNat < 2 ^ 63 := by
      by_cases hc0 : g.links.cap = 0
      · rw [hc0]; decide
      · dsimp only [optChainRest, chainRest, chainLinksVecBuf] at hm
        rw [vecEpochBuf_eq_of_ne_zero hc0] at hm
        have hpure : m ⊨ ⌜ch.links.length ≤ g.links.cap.toNat ∧
            g.links.cap.toNat * 112 < 2 ^ 63 ∧
            g.links.ptr ≠ 0⌝ ∗
            (((p + 8#64) ↦₆₄ g.links.ptr) ∗
             ((p + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
             arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 g.links.ptr ch.links ∗
             A.live g.links.ptr (g.links.cap.toNat * 112) 8 ∗
             memRegion (g.links.ptr + BitVec.ofNat 64 (ch.links.length * 112))
               ((g.links.cap.toNat - ch.links.length) * 112) ∗
             vecU8At A (p + 0x18#64) g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
             ((p + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
             ((p + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
             optChainParamsPBAt (p + 0x40#64) ch.params ∗
             ((p + 0x4c#64) ↦₃₂ ch.direction) ∗ R) := by
          convert hm using 1; ac_rfl
        rw [satisfies_pure_sepConj] at hpure
        have hmul := hpure.1.2.1
        omega
    dsimp only [optChainCap, Option.isSome_some, Bool.not_true]
    exact ⟨EncodedLen.cap_add_one_beq_zero_false hcap, EncodedLen.cap_add_one_bne_zero_true hcap⟩

/-! ## Arithmetic Helpers for `VersionNegotiation::encoded_len` (`i32` / `ChainParams`) -/

@[simp, arm64_norm]
theorem sext64_truncate32 (v : BitVec 32) :
    (BitVec.signExtend 64 v).truncate 32 = v := by bv_bits

@[simp, arm64_norm]
theorem sext64_beq_zero32 (v : BitVec 32) :
    (BitVec.signExtend 64 v == 0#64) = (v == 0#32) := by bv_bits

@[simp, arm64_norm]
theorem sext64_bne_zero32 (v : BitVec 32) :
    (BitVec.signExtend 64 v != 0#64) = (v != 0#32) := by
  simp only [bne, sext64_beq_zero32]

theorem bv_i32VarintField_nonzero {v : BitVec 32} (hv : v ≠ 0#32) :
    BitVec.ofNat 64 (ProtoRepr.varintLen (v.signExtend 64)) + 1#64 =
      BitVec.ofNat 64 (i32VarintFieldEncodedLen v) := by
  unfold i32VarintFieldEncodedLen
  simp only [hv, ↓reduceIte, ← BitVec.ofNat_add, Nat.add_comm]

theorem bv_chainParams_maxJump_nonzero {v : BitVec 32} (hv : v ≠ 0#32) :
    BitVec.ofNat 64 (ProtoRepr.varintLen (v.zeroExtend 64)) + 3#64 =
      BitVec.ofNat 64 (2 + u32VarintFieldEncodedLen v) := by
  unfold u32VarintFieldEncodedLen
  simp only [hv, ↓reduceIte, ← BitVec.ofNat_add]
  congr 1; omega

theorem bv_optChainParams_some_combine (cp : ChainParamsPB) :
    BitVec.ofNat 64 (u32VarintFieldEncodedLen cp.maxOooKeys) +
      BitVec.ofNat 64 (2 + u32VarintFieldEncodedLen cp.maxJump) =
      BitVec.ofNat 64 (optChainParamsPBFieldEncodedLen (some cp)) := by
  rw [optChainParamsPBFieldEncodedLen_some, chainParamsPBEncodedLen, ← BitVec.ofNat_add]
  congr 1; omega

theorem bv_vn_sum_eq (vn : VersionNegotiationPB) :
    BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction) +
      BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey) +
      (BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion) +
        BitVec.ofNat 64 (optChainParamsPBFieldEncodedLen vn.chainParams)) =
      BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn) := by
  unfold versionNegotiationPBEncodedLen
  simp only [← BitVec.ofNat_add]
  congr 1; omega

theorem bv_optVN_some_eq (vn : VersionNegotiationPB) :
    BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn) +
      BitVec.ofNat 64 (ProtoRepr.varintLen (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn))) + 1#64 =
      BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen (some vn)) := by
  dsimp only [optVersionNegotiationPBFieldEncodedLen]
  simp only [← BitVec.ofNat_add]
  congr 1; omega

theorem bv_optChain_some_eq (ch : ChainPB) :
    BitVec.ofNat 64 (chainPBEncodedLen ch) +
      BitVec.ofNat 64 (ProtoRepr.varintLen (BitVec.ofNat 64 (chainPBEncodedLen ch))) + 1#64 =
      BitVec.ofNat 64 (optChainPBFieldEncodedLen (some ch)) := by
  dsimp only [optChainPBFieldEncodedLen]
  simp only [← BitVec.ofNat_add]
  congr 1; omega

theorem bv_optInner_some_eq (v1 : V1State) :
    BitVec.ofNat 64 (v1StatePBEncodedLen v1) +
      BitVec.ofNat 64 (ProtoRepr.varintLen (BitVec.ofNat 64 (v1StatePBEncodedLen v1))) + 1#64 =
      BitVec.ofNat 64 (optPqRatchetInnerPBFieldEncodedLen (some (.v1 v1))) := by
  dsimp only [optPqRatchetInnerPBFieldEncodedLen]
  simp only [← BitVec.ofNat_add]
  congr 1; omega

theorem chainPBEncodedLen_lt_of_state {st : PqRatchetState} {ch : ChainPB}
    (hch : st.chain = some ch) (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) :
    chainPBEncodedLen ch < 2 ^ 64 ∧
      optChainPBFieldEncodedLen (some ch) < 2 ^ 64 ∧
      ProtoRepr.varintLen (BitVec.ofNat 64 (chainPBEncodedLen ch)) < optChainPBFieldEncodedLen (some ch) := by
  unfold pqRatchetStatePBEncodedLen at hlen
  rw [hch] at hlen
  dsimp only [optChainPBFieldEncodedLen] at hlen ⊢
  omega

theorem v1StatePBEncodedLen_lt_of_state {st : PqRatchetState} {v1 : V1State}
    (hin : st.inner = some (.v1 v1)) (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) :
    v1StatePBEncodedLen v1 < 2 ^ 64 ∧
      optPqRatchetInnerPBFieldEncodedLen (some (.v1 v1)) < 2 ^ 64 ∧
      ProtoRepr.varintLen (BitVec.ofNat 64 (v1StatePBEncodedLen v1)) <
        optPqRatchetInnerPBFieldEncodedLen (some (.v1 v1)) := by
  unfold pqRatchetStatePBEncodedLen at hlen
  rw [hin] at hlen
  dsimp only [optPqRatchetInnerPBFieldEncodedLen] at hlen ⊢
  omega

theorem vn_authKey_len_lt_of_state {st : PqRatchetState} {vn : VersionNegotiationPB}
    (hvn : st.versionNegotiation = some vn) (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) :
    vn.authKey.length < 2 ^ 64 := by
  unfold pqRatchetStatePBEncodedLen at hlen
  rw [hvn] at hlen
  dsimp only [optVersionNegotiationPBFieldEncodedLen, versionNegotiationPBEncodedLen,
    bytesFieldEncodedLen] at hlen
  by_cases hemp : vn.authKey.isEmpty
  · cases h : vn.authKey with
    | nil => decide
    | cons _ _ => rw [h] at hemp; cases hemp
  · simp only [hemp, Bool.false_eq_true, ↓reduceIte] at hlen
    omega

end CryptoVerification.SpqrV1.Prost.EncodeToVec
