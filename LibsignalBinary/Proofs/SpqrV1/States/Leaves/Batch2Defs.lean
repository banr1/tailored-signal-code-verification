/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Defs
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Defs
public import LibsignalBinary.Proofs.SpqrV1.Drop.StatesRepr
public import LibsignalBinary.Proofs.SpqrV1.GF.Mul2U16
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# SPQR V1 Chunked Braid Leaf Transitions — Receiver & Encoder Specifications

**Checked by Lean.**

Symbol names, `fnOff` lemmas, `Option<Vec<u8>>` representation (`optVecU8At`), callee contracts
(`decoded_message`, `<unchunked::Ct1SentEkReceived>::send_ct2`), and separation-logic specifications
for `send_ct2_encoder`, `<unchunked::Ct1Sent>::recv_ek`, `<EkReceivedCt1Sampled>::recv_ct1_ack`,
`<Ct1Received>::recv_ct2_chunk`, `<HeaderSent>::recv_ct1_chunk`, `<KeysSampled>::recv_ct1_chunk`,
and `<Ct1Acknowledged>::recv_ek_chunk`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## 1. Symbol Names and Offsets -/

abbrev sendCt2EncoderName : String :=
  "spqr::v1::chunked::send_ct::send_ct2_encoder"

abbrev unchunkedCt1SentRecvEkName : String :=
  "<spqr::v1::unchunked::send_ct::Ct1Sent>::recv_ek"

abbrev ekReceivedCt1SampledRecvCt1AckName : String :=
  "<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>::recv_ct1_ack"

abbrev ct1ReceivedRecvCt2ChunkName : String :=
  "<spqr::v1::chunked::send_ek::Ct1Received>::recv_ct2_chunk"

abbrev headerSentRecvCt1ChunkName : String :=
  "<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk"

abbrev keysSampledRecvCt1ChunkName : String :=
  "<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk"

abbrev ct1AcknowledgedRecvEkChunkName : String :=
  "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk"

abbrev unchunkedCt1SentEkReceivedSendCt2Name : String :=
  "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"

abbrev polyDecoderDecodedMessageName : String :=
  "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"

@[simp, arm64_norm] theorem sendCt2Encoder_fnOff :
    libsignalSessionCode.fnOff sendCt2EncoderName = 0x5e730 :=
  libsignalSessionCode_fnOff_0x5e730

@[simp, arm64_norm] theorem unchunkedCt1SentRecvEk_fnOff :
    libsignalSessionCode.fnOff unchunkedCt1SentRecvEkName = 0x586c8 :=
  libsignalSessionCode_fnOff_0x586c8

@[simp, arm64_norm] theorem ekReceivedCt1SampledRecvCt1Ack_fnOff :
    libsignalSessionCode.fnOff ekReceivedCt1SampledRecvCt1AckName = 0x58d04 :=
  libsignalSessionCode_fnOff_0x58d04

@[simp, arm64_norm] theorem ct1ReceivedRecvCt2Chunk_fnOff :
    libsignalSessionCode.fnOff ct1ReceivedRecvCt2ChunkName = 0x58efc :=
  libsignalSessionCode_fnOff_0x58efc

@[simp, arm64_norm] theorem headerSentRecvCt1Chunk_fnOff :
    libsignalSessionCode.fnOff headerSentRecvCt1ChunkName = 0x58504 :=
  libsignalSessionCode_fnOff_0x58504

@[simp, arm64_norm] theorem keysSampledRecvCt1Chunk_fnOff :
    libsignalSessionCode.fnOff keysSampledRecvCt1ChunkName = 0x5c370 :=
  libsignalSessionCode_fnOff_0x5c370

@[simp, arm64_norm] theorem ct1AcknowledgedRecvEkChunk_fnOff :
    libsignalSessionCode.fnOff ct1AcknowledgedRecvEkChunkName = 0x595d0 :=
  libsignalSessionCode_fnOff_0x595d0

@[simp, arm64_norm] theorem unchunkedCt1SentEkReceivedSendCt2_fnOff :
    libsignalSessionCode.fnOff unchunkedCt1SentEkReceivedSendCt2Name = 0x59008 :=
  libsignalSessionCode_fnOff_0x59008

@[simp, arm64_norm] theorem polyDecoderDecodedMessage_fnOff :
    libsignalSessionCode.fnOff polyDecoderDecodedMessageName = 0x66788 :=
  libsignalSessionCode_fnOff_0x66788

/-! ## 2. `Option<Vec<u8>>` Representation (`24`B) & Callee Specifications -/

/-- `Option<Vec<u8>>` at `a` (`24` bytes = `0x18`, align `8`):
    - `none`: `(a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 16` (`cap = -1` niche)
    - `some bs`: `vecU8 A a bs` (with `cap < 2^63`, so `cap + 1 ≠ 0`) -/
def optVecU8At (A : RustAlloc) (a : BitVec 64) : Option Bytes → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 16
  | some bs => vecU8 A a bs

@[simp]
theorem optVecU8At_none (A : RustAlloc) (a : BitVec 64) :
    optVecU8At A a none = ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 16) := rfl

@[simp]
theorem optVecU8At_some (A : RustAlloc) (a : BitVec 64) (bs : Bytes) :
    optVecU8At A a (some bs) = vecU8 A a bs := rfl

theorem optVecU8At_none_entails_memRegion_24 (A : RustAlloc) (a : BitVec 64) :
    optVecU8At A a none ⊢ memRegion a 24 := by
  unfold optVecU8At
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 16) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion a noneCap)

/-- Stack budget for `<PolyDecoder as Decoder>::decoded_message` (`0x6bb80`):
    canonical `decodedMessageStack = 672 + extHookStack`. -/
abbrev polyDecoderDecodedMessageStack : Nat := 672 + extHookStack

/-- Ghost arguments for `<PolyDecoder as Decoder>::decoded_message` (`0x6bb80`). -/
structure PolyDecoderDecodedMessageGhost where
  outA : BitVec 64
  decA : BitVec 64
  dec : PolyDecoder
  outMsg : Option Bytes

/-- Specification of `<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message` (`0x6bb80`):
    - `x8 = outA` (`24`B `Option<Vec<u8>>` sret), `x0 = decA` (`&PolyDecoder`, `400`B).
    - Preserves `polyDecoderAt A decA dec` and writes `optVecU8At A outA x.outMsg` where
      `spqrPolyApi.decoded_message x.dec = .ok x.outMsg`.
    - Panics only on OOM (`allocFailedIn s0 sf`). -/
def polyDecoderDecodedMessageSpec (A : RustAlloc) (b : BitVec 64) :
    Spec PolyDecoderDecodedMessageGhost where
  pre := fun x s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.decA ∧
      PolyDecoderStrictSorted x.dec ∧
      spqrPolyApi.decoded_message x.dec = .ok x.outMsg⌝ ∗
      memRegion x.outA 24 ∗
      polyDecoderAt A x.decA x.dec ∗
      tokenInitAt b ∗ reduceTableAt b ∗
      A.pool ∗ stackAt s.sp polyDecoderDecodedMessageStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      optVecU8At A x.outA x.outMsg ∗
      polyDecoderAt A x.decA x.dec ∗
      tokenInitAt b ∗ reduceTableAt b ∗
      A.pool ∗ stackAt s0.sp polyDecoderDecodedMessageStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Duplicate the pure fact `dec.pts.length = 16` from `polyDecoderAt A a dec`. -/
theorem polyDecoderAt_dup_pts_len (A : RustAlloc) (a : BitVec 64) (dec : PolyDecoder) :
    polyDecoderAt A a dec ⊢ ⌜dec.pts.length = 16⌝ ∗ polyDecoderAt A a dec := by
  rw [polyDecoderAt]
  refine Entails.pure_left (fun ⟨hlen, hneed⟩ => ?_)
  exact Entails.pure_right hlen (Entails.pure_right ⟨hlen, hneed⟩ (Entails.refl _))

theorem frame_polyDecoderAt_dup_pts_len (A : RustAlloc) (a : BitVec 64) (dec : PolyDecoder)
    (P R : SepProp) :
    P ∗ polyDecoderAt A a dec ∗ R ⊢ ⌜dec.pts.length = 16⌝ ∗ (P ∗ polyDecoderAt A a dec ∗ R) := by
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left (polyDecoderAt_dup_pts_len A a dec))) ?_
  rw [sepConj_assoc (⌜dec.pts.length = 16⌝), sepConj_pure_left_comm]
  exact Entails.refl _

/-- Stack budget for `<Unchunked.SendCt.Ct1SentEkReceived>::send_ct2` (`0x5e400`). -/
abbrev unchunkedSendCt2Stack : Nat := 336 + extHookStack

/-- Read-only `.rodata` + `MAX_LOG_LEVEL_FILTER` bundle required by
    `<Unchunked.SendCt.Ct1SentEkReceived>::send_ct2` (`0x5e400`). -/
def unchunkedSendCt2RoAt (b : BitVec 64) : SepProp :=
  ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ ((b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel)

/-- Ghost arguments for `<Unchunked.SendCt.Ct1SentEkReceived>::send_ct2` (`0x5e400`). -/
structure UnchunkedSendCt2Ghost (F : ShaCompress) where
  outA : BitVec 64
  stA : BitVec 64
  st : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)
  outUc : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)
  ct2 : Bytes
  mac : Mac

/-- Specification of `<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2` (`0x5e400`):
    - `x0 = outA` (`104`B `(Ct2Sent, Vec<u8>, Vec<u8>)` output: `Ct2Sent` at `+0..+56`,
      `ct2: Vec<u8>` at `+56..+80`, `mac: Vec<u8>` at `+80..+104`),
    - `x1 = stA` (`128`B `Unchunked.SendCt.Ct1SentEkReceived`, consumed by value into `memRegion stA 128`).
    - Panics only on OOM (`allocFailedIn s0 sf`). -/
def unchunkedCt1SentEkReceivedSendCt2Spec (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (b : BitVec 64) :
    Spec (UnchunkedSendCt2Ghost F) where
  pre := fun x s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x0 = x.outA ∧ s.readReg64 .x1 = x.stA ∧
      x.st.send_ct2 K = .ok (x.outUc, x.ct2, x.mac)⌝ ∗
      memRegion x.outA 104 ∗
      unchunkedCt1SentEkReceivedAt A x.stA x.st ∗
      unchunkedSendCt2RoAt b ∗
      A.pool ∗ stackAt s.sp unchunkedSendCt2Stack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      unchunkedCt2SentAt A x.outA x.outUc ∗
      vecU8 A (x.outA + 56#64) x.ct2 ∗
      vecU8 A (x.outA + 80#64) x.mac ∗
      memRegion x.stA 128 ∗
      unchunkedSendCt2RoAt b ∗
      A.pool ∗ stackAt s0.sp unchunkedSendCt2Stack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## 3. Target Specifications -/

/-- If `encodeBytesResult msg = .ok enc`, then `msg.length ≤ 1048576` (and `% 2 = 0`). -/
theorem length_le_of_encodeBytesResult_ok {msg : Bytes} {enc : PolyEncoder}
    (h : encodeBytesResult msg = .ok enc) :
    msg.length ≤ 1048576 ∧ msg.length % 2 = 0 := by
  unfold encodeBytesResult at h
  split_ifs at h with h1 h2
  simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at h1
  simp only [NUM_POLYS, CHUNK_SIZE, gt_iff_lt, not_lt] at h2
  exact ⟨h2, h1⟩

/-- If `expectEncodeBytes spqrPolyApi site msg = .ok enc`, then `encodeBytesResult msg = .ok enc`
    and `msg.length ≤ 1048576`. -/
theorem encodeBytesResult_of_expectEncodeBytes_ok {site : String} {msg : Bytes} {enc : PolyEncoder}
    (h : expectEncodeBytes spqrPolyApi site msg = .ok enc) :
    encodeBytesResult msg = .ok enc ∧ msg.length ≤ 1048576 := by
  unfold expectEncodeBytes spqrPolyApi at h
  dsimp only at h
  rw [encodeBytes_eq_ok msg] at h
  simp only [Except.mapError, Bind.bind, Except.bind, liftM, monadLift, MonadLift.monadLift,
    liftSpqrPanic] at h
  cases hres : encodeBytesResult msg with
  | error e => simp [hres] at h
  | ok enc' =>
    simp only [hres, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, (length_le_of_encodeBytesResult_ok hres).1⟩

/-- Stack budget for `spqr::v1::chunked::send_ct::send_ct2_encoder` (`0x63b28`, 85 insns):
    own frame `512`B (`80 + 432`) + `encodeBytesStackX` (since it also calls `memcpy` / `do_reserve_and_handle`). -/
abbrev sendCt2EncoderStack : Nat := 512 + encodeBytesStackX

/-- Ghost arguments for `spqr::v1::chunked::send_ct::send_ct2_encoder` (`0x63b28`, 85 insns). -/
structure SendCt2EncoderGhost where
  outA : BitVec 64
  ct2Ptr : BitVec 64
  ct2 : Bytes
  macPtr : BitVec 64
  mac : Bytes
  outEnc : PolyEncoder

/-- Specification of `spqr::v1::chunked::send_ct::send_ct2_encoder` (`0x63b28`, 85 insns):
    - `x0 = outA` (`400`B `PolyEncoder` output),
    - `x1 = ct2Ptr`, `x2 = ct2.length` (`ct2: &[u8]`),
    - `x3 = macPtr`, `x4 = mac.length` (`mac: &[u8]`).
    - Concatenates `ct2 ++ mac` into a temporary `Vec<u8>`, encodes it with `PolyEncoder.encode_bytes (ct2 ++ mac)`,
      deallocates the temporary `Vec<u8>`, and writes `polyEncoderAt A outA x.outEnc`.
    - Panics only on OOM (`allocFailedIn s0 sf`). -/
def sendCt2EncoderSpec (A : RustAlloc) :
    Spec SendCt2EncoderGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.ct2Ptr ∧ s.readReg64 .x2 = BitVec.ofNat 64 x.ct2.length ∧
      s.readReg64 .x3 = x.macPtr ∧ s.readReg64 .x4 = BitVec.ofNat 64 x.mac.length ∧
      x.ct2Ptr ≠ 0#64 ∧ x.macPtr ≠ 0#64 ∧
      Chunked.SendCt.send_ct2_encoder spqrPolyApi x.ct2 x.mac = .ok x.outEnc⌝ ∗
      memRegion x.outA 400 ∗
      (x.ct2Ptr ↦ₛ x.ct2) ∗
      (x.macPtr ↦ₛ x.mac) ∗
      A.pool ∗ stackAt s.sp sendCt2EncoderStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      polyEncoderAt A x.outA x.outEnc ∗
      (x.ct2Ptr ↦ₛ x.ct2) ∗
      (x.macPtr ↦ₛ x.mac) ∗
      A.pool ∗ stackAt s0.sp sendCt2EncoderStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Result representation for `<spqr::v1::unchunked::send_ct::Ct1Sent>::recv_ek` (`128`B at `a`):
    - `.ok outSt`: `unchunkedCt1SentEkReceivedAt A a outSt` (`128`B, with niche `cap ≠ noneCap` at `+0`)
    - `.error _`: `(a ↦₆₄ noneCap) ∗ ((a + 8#64) ↦₈ 12#8) ∗ memRegion (a + 9#64) 119`
      (`Error::ErroneousDataReceived` discriminant `12`) -/
def unchunkedCt1SentRecvEkResAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64) :
    Except Error (Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)) → SepProp
  | .ok outSt => unchunkedCt1SentEkReceivedAt A a outSt
  | .error _ => (a ↦₆₄ noneCap) ∗ ((a + 8#64) ↦₈ 12#8) ∗ memRegion (a + 9#64) 119

/-- Stack budget for `<spqr::v1::unchunked::send_ct::Ct1Sent>::recv_ek` (`0x5dac0`, 99 insns):
    own frame `208`B + `extHookStack`. -/
abbrev unchunkedRecvEkStack : Nat := 208 + extHookStack

/-- Ghost arguments for `<spqr::v1::unchunked::send_ct::Ct1Sent>::recv_ek` (`0x5dac0`, 99 insns). -/
structure UnchunkedCt1SentRecvEkGhost (F : ShaCompress) where
  outA : BitVec 64
  stA : BitVec 64
  ekA : BitVec 64
  st : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)
  ek : Bytes
  res : Except Error (Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))

/-- Specification of `<spqr::v1::unchunked::send_ct::Ct1Sent>::recv_ek` (`0x5dac0`, 99 insns):
    - `x0 = outA` (`128`B `Result<Ct1SentEkReceived, Error>` output),
    - `x1 = stA` (`128`B `Unchunked.SendCt.Ct1Sent`, consumed by value into `memRegion stA 128`),
    - `x2 = st.epoch`,
    - `x3 = ekA` (`24`B `Vec<u8>`, consumed by value into `memRegion ekA 24`). -/
def unchunkedCt1SentRecvEkSpec (A : RustAlloc) (F : ShaCompress) (K : MlKem) :
    Spec (UnchunkedCt1SentRecvEkGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.stA ∧
      s.readReg64 .x2 = x.st.epoch ∧
      s.readReg64 .x3 = x.ekA ∧
      x.st.recv_ek K x.st.epoch x.ek = StatesResult.ofError x.res⌝ ∗
      memRegion x.outA 128 ∗
      unchunkedCt1SentAt A x.stA x.st ∗
      vecU8 A x.ekA x.ek ∗
      A.pool ∗ stackAt s.sp unchunkedRecvEkStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      unchunkedCt1SentRecvEkResAt A x.outA x.res ∗
      memRegion x.stA 128 ∗
      memRegion x.ekA 24 ∗
      A.pool ∗ stackAt s0.sp unchunkedRecvEkStack

/-- Stack budget for `<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>::recv_ct1_ack` (`0x5e0fc`, 53 insns):
    own frame `176`B + `sendCt2EncoderStack`. -/
abbrev ekReceivedCt1SampledRecvCt1AckStack : Nat := 176 + sendCt2EncoderStack

/-- Ghost arguments for `<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>::recv_ct1_ack` (`0x5e0fc`, 53 insns). -/
structure EkReceivedCt1SampledRecvCt1AckGhost (F : ShaCompress) where
  outA : BitVec 64
  stA : BitVec 64
  st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)
  outSt : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)

/-- Specification of `<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>::recv_ct1_ack` (`0x5e0fc`, 53 insns):
    - `x0 = outA` (`456`B `Ct2Sampled` output),
    - `x1 = stA` (`528`B `EkReceivedCt1Sampled` input, consumed by value into `memRegion stA 528`),
    - `x2 = st.uc.epoch`.
    - Panics only on OOM (`allocFailedIn s0 sf`). -/
def ekReceivedCt1SampledRecvCt1AckSpec (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (b : BitVec 64) :
    Spec (EkReceivedCt1SampledRecvCt1AckGhost F) where
  pre := fun x s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.stA ∧
      s.readReg64 .x2 = x.st.uc.epoch ∧
      x.st.recv_ct1_ack K x.st.uc.epoch = .ok x.outSt⌝ ∗
      memRegion x.outA chunkedCt2SampledSize ∗
      chunkedEkReceivedCt1SampledAt A x.stA x.st ∗
      unchunkedSendCt2RoAt b ∗
      A.pool ∗ stackAt s.sp ekReceivedCt1SampledRecvCt1AckStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chunkedCt2SampledAt A x.outA x.outSt ∗
      memRegion x.stA chunkedEkReceivedCt1SampledSize ∗
      unchunkedSendCt2RoAt b ∗
      A.pool ∗ stackAt s0.sp ekReceivedCt1SampledRecvCt1AckStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Stack budget for `<spqr::v1::chunked::send_ek::Ct1Received>::recv_ct2_chunk` (`0x5e2f4`, 67 insns):
    own frame `448`B + `addChunkStackX` (since it also calls `memcpy`). -/
abbrev ct1ReceivedRecvCt2ChunkStack : Nat := 448 + (144 + extHookStack)

/-- Ghost arguments for `<spqr::v1::chunked::send_ek::Ct1Received>::recv_ct2_chunk` (`0x5e2f4`, 67 insns). -/
structure Ct1ReceivedRecvCt2ChunkGhost (F : ShaCompress) where
  outA : BitVec 64
  stA : BitVec 64
  chunkA : BitVec 64
  st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)
  chunk : Chunk
  outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)

/-- Specification of `<spqr::v1::chunked::send_ek::Ct1Received>::recv_ct2_chunk` (`0x5e2f4`, 67 insns):
    - `x0 = outA` (`504`B `EkSentCt1Received` output),
    - `x1 = stA` (`504`B `Ct1Received` input, consumed by value into `memRegion stA 504`),
    - `x2 = st.uc.epoch`,
    - `x3 = chunkA` (`34`B `&Chunk`, preserved).
    - Panics only on OOM (`allocFailedIn s0 sf`). -/
def ct1ReceivedRecvCt2ChunkSpec (A : RustAlloc) (F : ShaCompress) :
    Spec (Ct1ReceivedRecvCt2ChunkGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.stA ∧
      s.readReg64 .x2 = x.st.uc.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      x.st.recv_ct2_chunk x.st.uc.epoch x.chunk = .ok x.outSt⌝ ∗
      memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
      chunkedCt1ReceivedAt A x.stA x.st ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool ∗ stackAt s.sp ct1ReceivedRecvCt2ChunkStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chunkedEkSentCt1ReceivedAt A x.outA x.outSt ∗
      memRegion x.stA chunkedCt1ReceivedSize ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool ∗ stackAt s0.sp ct1ReceivedRecvCt2ChunkStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Representation predicate for `spqr::v1::chunked::send_ek::HeaderSentRecvChunk` (`880`B at `a`):
    - `.stillReceiving s`: `chunkedHeaderSentAt A a s` (`880`B, with `PolyEncoder` tag `0` or `1` at `a + 0`)
    - `.done s`: `(a ↦₆₄ 2#64) ∗ chunkedCt1ReceivedAt A (a + 8#64) s ∗ memRegion (outA + 512) 368` -/
def headerSentRecvChunkAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64) :
    Chunked.SendEk.HeaderSentRecvChunk spqrPolyApi (spqrAuthApi F) → SepProp
  | .stillReceiving s => chunkedHeaderSentAt A a s
  | .done s => (a ↦₆₄ 2#64) ∗ chunkedCt1ReceivedAt A (a + 8#64) s ∗ memRegion (a + 512#64) 368

/-- Stack budget for `<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk` (`0x5d8fc`, 113 insns):
    own frame `1568`B (`64 + 1504`) + `polyDecoderDecodedMessageStack`. -/
abbrev headerSentRecvCt1ChunkStack : Nat := 1568 + polyDecoderDecodedMessageStack

/-- Ghost arguments for `<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk` (`0x5d8fc`, 113 insns). -/
structure HeaderSentRecvCt1ChunkGhost (F : ShaCompress) where
  outA : BitVec 64
  stA : BitVec 64
  chunkA : BitVec 64
  st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)
  chunk : Chunk
  outRes : Chunked.SendEk.HeaderSentRecvChunk spqrPolyApi (spqrAuthApi F)

/-- Specification of `<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk` (`0x5d8fc`, 113 insns):
    - `x0 = outA` (`880`B `HeaderSentRecvChunk` output),
    - `x1 = stA` (`880`B `HeaderSent` input, consumed by value into `memRegion stA 880`),
    - `x2 = st.uc.epoch`,
    - `x3 = chunkA` (`34`B `&Chunk`, preserved).
    - Panics only on OOM (`allocFailedIn s0 sf`). -/
def headerSentRecvCt1ChunkSpec (A : RustAlloc) (F : ShaCompress) (b : BitVec 64) :
    Spec (HeaderSentRecvCt1ChunkGhost F) where
  pre := fun x s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.stA ∧
      s.readReg64 .x2 = x.st.uc.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      PolyDecoderStrictSorted x.st.receiving_ct1 ∧
      x.st.recv_ct1_chunk x.st.uc.epoch x.chunk = .ok x.outRes⌝ ∗
      memRegion x.outA chunkedHeaderSentSize ∗
      chunkedHeaderSentAt A x.stA x.st ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitAt b ∗ reduceTableAt b ∗
      A.pool ∗ stackAt s.sp headerSentRecvCt1ChunkStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      headerSentRecvChunkAt A x.outA x.outRes ∗
      memRegion x.stA chunkedHeaderSentSize ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitAt b ∗ reduceTableAt b ∗
      A.pool ∗ stackAt s0.sp headerSentRecvCt1ChunkStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Stack budget for `<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk` (`0x61768`, 107 insns):
    own frame `976`B (`80 + 896`) + `encodeBytesStackX`. -/
abbrev keysSampledRecvCt1ChunkStack : Nat := 976 + encodeBytesStackX

/-- Ghost arguments for `<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk` (`0x61768`, 107 insns). -/
structure KeysSampledRecvCt1ChunkGhost (F : ShaCompress) where
  outA : BitVec 64
  stA : BitVec 64
  chunkA : BitVec 64
  st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)
  chunk : Chunk
  outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)

/-- Specification of `<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk` (`0x61768`, 107 insns):
    - `x0 = outA` (`880`B `HeaderSent` output),
    - `x1 = stA` (`504`B `KeysSampled` input, consumed by value into `memRegion stA 504`),
    - `x2 = st.uc.epoch`,
    - `x3 = chunkA` (`34`B `&Chunk`, preserved).
    - Panics only on OOM (`allocFailedIn s0 sf`). -/
def keysSampledRecvCt1ChunkSpec (A : RustAlloc) (F : ShaCompress) :
    Spec (KeysSampledRecvCt1ChunkGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.stA ∧
      s.readReg64 .x2 = x.st.uc.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      x.st.recv_ct1_chunk x.st.uc.epoch x.chunk = .ok x.outSt⌝ ∗
      memRegion x.outA chunkedHeaderSentSize ∗
      chunkedKeysSampledAt A x.stA x.st ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool ∗ stackAt s.sp keysSampledRecvCt1ChunkStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chunkedHeaderSentAt A x.outA x.outSt ∗
      memRegion x.stA 504 ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool ∗ stackAt s0.sp keysSampledRecvCt1ChunkStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Representation predicate for `Result<Ct1AcknowledgedRecvChunk, Error>` (`528`B at `a`):
    - `.ok (.stillReceiving s)`: `chunkedCt1AcknowledgedAt A a s` (`528`B, niche `cap < 2^63` at `+0`)
    - `.ok (.done s)`: `(a ↦₆₄ noneCap) ∗ chunkedCt2SampledAt A (a + 8#64) s ∗ memRegion (a + 464#64) 64`
    - `.error _`: `(a ↦₆₄ 0xfffffffffffffffe#64) ∗ ((a + 8#64) ↦₈ 12#8) ∗ memRegion (a + 9#64) 519` -/
def ct1AcknowledgedRecvEkChunkResAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64) :
    Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)) → SepProp
  | .ok (.stillReceiving s) => chunkedCt1AcknowledgedAt A a s
  | .ok (.done s) =>
      (a ↦₆₄ noneCap) ∗ chunkedCt2SampledAt A (a + 8#64) s ∗ memRegion (a + 464#64) 64
  | .error _ =>
      (a ↦₆₄ 0xfffffffffffffffe#64) ∗ ((a + 8#64) ↦₈ 12#8) ∗ memRegion (a + 9#64) 519

/-- Stack budget for `<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk` (`0x5e9c8`, 153 insns):
    own frame `1760`B (`64 + 1696`) + `sendCt2EncoderStack`. -/
abbrev ct1AcknowledgedRecvEkChunkStack : Nat := 1760 + sendCt2EncoderStack

/-- Ghost arguments for `<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk` (`0x5e9c8`, 153 insns). -/
structure Ct1AcknowledgedRecvEkChunkGhost (F : ShaCompress) where
  outA : BitVec 64
  stA : BitVec 64
  chunkA : BitVec 64
  st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)
  chunk : Chunk
  res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F))

/-- Specification of `<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk` (`0x5e9c8`, 153 insns):
    - `x0 = outA` (`528`B `Result<Ct1AcknowledgedRecvChunk, Error>` output),
    - `x1 = stA` (`528`B `Ct1Acknowledged` input, consumed by value into `memRegion stA 528`),
    - `x2 = st.uc.epoch`,
    - `x3 = chunkA` (`34`B `&Chunk`, preserved).
    - Panics only on OOM (`allocFailedIn s0 sf`). -/
def ct1AcknowledgedRecvEkChunkSpec (A : RustAlloc) (F : ShaCompress) (K : MlKem) (b : BitVec 64) :
    Spec (Ct1AcknowledgedRecvEkChunkGhost F) where
  pre := fun x s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.stA ∧
      s.readReg64 .x2 = x.st.uc.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      PolyDecoderStrictSorted x.st.receiving_ek ∧
      x.st.recv_ek_chunk K x.st.uc.epoch x.chunk = StatesResult.ofError x.res⌝ ∗
      memRegion x.outA 528 ∗
      chunkedCt1AcknowledgedAt A x.stA x.st ∗
      chunkAt x.chunkA x.chunk ∗
      unchunkedSendCt2RoAt b ∗
      tokenInitAt b ∗ reduceTableAt b ∗
      A.pool ∗ stackAt s.sp ct1AcknowledgedRecvEkChunkStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ct1AcknowledgedRecvEkChunkResAt A x.outA x.res ∗
      memRegion x.stA 528 ∗
      chunkAt x.chunkA x.chunk ∗
      unchunkedSendCt2RoAt b ∗
      tokenInitAt b ∗ reduceTableAt b ∗
      A.pool ∗ stackAt s0.sp ct1AcknowledgedRecvEkChunkStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

end CryptoVerification.SpqrV1.States.Leaves
