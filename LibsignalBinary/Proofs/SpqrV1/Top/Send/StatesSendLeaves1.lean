/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# `spqr::send::<HookRng>`: Inlined `States::send` Immediate Arms and Join-Point Helpers

**Checked by Lean.**

Defines the post-arm join-state invariant `SpqrSendJoinState` at `0x31458` (`+3068`),
relocation/call combinators, and verifies the three immediate arms (`.ekSentCt1Received`,
`.noHeaderReceived`, `.ct1Acknowledged`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

theorem Relocatable.of_chunkedKeysUnsampledAt (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    Relocatable 56 (fun a => chunkedKeysUnsampledAt A a st) :=
  Relocatable.of_unchunkedCt2SentAt A { epoch := st.uc.epoch, auth := st.uc.auth }

theorem Relocatable.of_unchunkedHeaderReceivedAt (A : RustAlloc) {F : ShaCompress}
    (st : Unchunked.SendCt.HeaderReceived (spqrAuthApi F)) :
    Relocatable 80 (fun a => unchunkedHeaderReceivedAt A a st) :=
  Relocatable.of_unchunkedEkSentAt A { auth := st.auth, dk := st.hdr, epoch := st.epoch }

theorem Relocatable.of_chunkedHeaderReceivedAt (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    Relocatable 480 (fun a => chunkedHeaderReceivedAt A a st) :=
  Relocatable.sepConj (off := 80#64) (m := 480) rfl rfl
    (Relocatable.of_unchunkedHeaderReceivedAt A st.uc) (Relocatable.of_polyDecoderAt A st.receiving_ek)

theorem Relocatable.of_chunkedKeysSampledAt (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) :
    Relocatable 504 (fun a => chunkedKeysSampledAt A a st) :=
  Relocatable.of_chunkedCt1ReceivedAt A (chunkedKeysSampledToCt1Received st)

theorem Relocatable.of_chunkedEkSentCt1ReceivedAt (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    Relocatable 504 (fun a => chunkedEkSentCt1ReceivedAt A a st) :=
  Relocatable.sepConj (off := 104#64) (m := 504) rfl rfl
    (Relocatable.of_unchunkedEkSentCt1ReceivedAt A st.uc) (Relocatable.of_polyDecoderAt A st.receiving_ct2)

theorem Relocatable.of_chunkedNoHeaderReceivedAt (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    Relocatable 456 (fun a => chunkedNoHeaderReceivedAt A a st) :=
  Relocatable.sepConj (off := 56#64) (m := 456) rfl rfl
    (Relocatable.of_unchunkedCt2SentAt A { epoch := st.uc.epoch, auth := st.uc.auth })
    (Relocatable.of_polyDecoderAt A st.receiving_hdr)

theorem Relocatable.of_chunkedCt1AcknowledgedAt (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    Relocatable 528 (fun a => chunkedCt1AcknowledgedAt A a st) :=
  Relocatable.sepConj (off := 128#64) (m := 528) rfl rfl
    (Relocatable.of_unchunkedCt1SentAt A st.uc) (Relocatable.of_polyDecoderAt A st.receiving_ek)

theorem Relocatable.withPad {n k m : Nat} {off : BitVec 64} {F : BitVec 64 → SepProp}
    (hoff : off = BitVec.ofNat 64 n) (hm : n + k = m) (hk : k ≤ 2 ^ 64 := by decide)
    (hF : Relocatable n F) : Relocatable m (fun a => F a ∗ memRegion (a + off) k) :=
  Relocatable.sepConj hoff hm hF (Relocatable.of_memRegion k hk)

/-- Tag word at offset `+0` of `PolyEncoder` (`0#64` for `.points`, `1#64` for `.polys`). -/
def polyEncoderTagVal : EncoderState → BitVec 64
  | .points _ => polyEncoderPointsTag
  | .polys _ => polyEncoderPolysTag

/-- The 384-byte `Vec` array at offset `+8` of `EncoderState`. -/
def encoderStateVecsAt (A : RustAlloc) (a : BitVec 64) : EncoderState → SepProp
  | .points pts =>
    ⌜pts.length = NUM_POLYS ∧ (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)⌝ ∗
      pointListOf A a pts
  | .polys ps => ⌜ps.length = NUM_POLYS⌝ ∗ polyListOf A a ps

/-- The 392-byte tail of `PolyEncoder` starting at `encA + 8#64`. -/
def polyEncoderTail392At (A : RustAlloc) (a : BitVec 64) (enc : PolyEncoder) : SepProp :=
  encoderStateVecsAt A a enc.s ∗ ((a + 384#64) ↦₃₂ enc.idx) ∗ memRegion (a + 388#64) 4

theorem polyEncoderAt_eq_tag_tail392 (A : RustAlloc) (a : BitVec 64) (enc : PolyEncoder) :
    polyEncoderAt A a enc =
      (a ↦₆₄ polyEncoderTagVal enc.s) ∗ polyEncoderTail392At A (a + 8#64) enc := by
  unfold polyEncoderAt polyEncoderTail392At polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize
  rw [show (a + 8#64) + 384#64 = a + 0x188#64 by bv_omega,
      show (a + 8#64) + 388#64 = a + 0x18c#64 by bv_omega]
  cases enc.s <;>
    (dsimp only [encoderStateAt, polyEncoderTagVal, encoderStateVecsAt, polyEncoderVecsOff]; ac_rfl)

theorem Relocatable.of_polyEncoderTail392At (A : RustAlloc) (enc : PolyEncoder) :
    Relocatable 392 (fun a => polyEncoderTail392At A a enc) := by
  have hvecs : Relocatable 384 (fun a => encoderStateVecsAt A a enc.s) := by
    cases hs : enc.s with
    | points pts =>
      dsimp only [encoderStateVecsAt]
      exact Relocatable.pure_left
        (pts.length = NUM_POLYS ∧ (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555))
        fun ⟨hlen, _⟩ =>
          Relocatable.arrayAt (elem := fun pt addr => pointOf A addr pt)
            (fun pt => Relocatable.vecOf A gf16Stride gf16Align gf16At pt.value) pts 384 (by rw [hlen]; rfl)
    | polys ps =>
      dsimp only [encoderStateVecsAt]
      exact Relocatable.pure_left (ps.length = NUM_POLYS) fun hlen =>
        Relocatable.arrayAt (elem := fun p addr => polyOf A addr p)
          (fun p => Relocatable.vecOf A gf16Stride gf16Align gf16At p.coefficients) ps 384 (by rw [hlen]; rfl)
  refine Relocatable.congr rfl (fun a => ?_)
    (Relocatable.sepConj (off := 384#64) (m := 392) rfl rfl hvecs
      (Relocatable.sepConj (off := 4#64) (m := 8) rfl rfl
        (Relocatable.pointsTo32 enc.idx) (Relocatable.of_memRegion 4)))
  unfold polyEncoderTail392At
  rw [show (a + 384#64) + 4#64 = a + 388#64 by bv_omega]

/-- The 920-byte tail of `chunkedCt1SampledAt` starting at `a` (`stA + 8#64`). -/
def chunkedCt1SampledTail920At (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) : SepProp :=
  polyEncoderTail392At A a st.sending_ct1 ∗
    unchunkedCt1SentAt A (a + 392#64) st.uc ∗ polyDecoderAt A (a + 520#64) st.receiving_ek

theorem chunkedCt1SampledAt_eq_tag_tail920 (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) :
    chunkedCt1SampledAt A a st =
      (a ↦₆₄ polyEncoderTagVal st.sending_ct1.s) ∗ chunkedCt1SampledTail920At A (a + 8#64) st := by
  unfold chunkedCt1SampledAt chunkedCt1SampledTail920At
  rw [polyEncoderAt_eq_tag_tail392 A a st.sending_ct1,
      show (a + 8#64) + 392#64 = a + 400#64 by bv_omega,
      show (a + 8#64) + 520#64 = a + 528#64 by bv_omega, sepConj_assoc]

theorem Relocatable.of_chunkedCt1SampledTail920At (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) :
    Relocatable 920 (fun a => chunkedCt1SampledTail920At A a st) := by
  refine Relocatable.congr rfl (fun a => ?_)
    (Relocatable.sepConj (off := 392#64) (m := 920) rfl rfl
      (Relocatable.of_polyEncoderTail392At A st.sending_ct1)
      (Relocatable.sepConj (off := 128#64) (m := 528) rfl rfl
        (Relocatable.of_unchunkedCt1SentAt A st.uc) (Relocatable.of_polyDecoderAt A st.receiving_ek)))
  unfold chunkedCt1SampledTail920At
  rw [show (a + 392#64) + 128#64 = a + 520#64 by bv_omega]

/-- Word 0 (`x20`) of `chunkedStatesAt A a st`. -/
def chunkedStatesWord0 {F : ShaCompress} : States spqrPolyApi (spqrAuthApi F) → BitVec 64
  | .keysUnsampled _ => 2#64 | .keysSampled _ => 3#64 | .headerSent _ => 4#64
  | .ct1Received _ => 5#64 | .ekSentCt1Received _ => 6#64 | .noHeaderReceived _ => 7#64
  | .headerReceived _ => 8#64 | .ct1Sampled s => polyEncoderTagVal s.sending_ct1.s
  | .ekReceivedCt1Sampled _ => 10#64 | .ct1Acknowledged _ => 11#64 | .ct2Sampled _ => 12#64

/-- The 920-byte tail of `chunkedStatesAt` (bytes `8..928`, stored at `sp + 0x590..0x928` at `0x31458`). -/
def chunkedStatesTail920At (A : RustAlloc) {F : ShaCompress} (a : BitVec 64) :
    States spqrPolyApi (spqrAuthApi F) → SepProp
  | .keysUnsampled s => chunkedKeysUnsampledAt A a s ∗ memRegion (a + 56#64) 864
  | .keysSampled s => chunkedKeysSampledAt A a s ∗ memRegion (a + 504#64) 416
  | .headerSent s => chunkedHeaderSentAt A a s ∗ memRegion (a + 880#64) 40
  | .ct1Received s => chunkedCt1ReceivedAt A a s ∗ memRegion (a + 504#64) 416
  | .ekSentCt1Received s => chunkedEkSentCt1ReceivedAt A a s ∗ memRegion (a + 504#64) 416
  | .noHeaderReceived s => chunkedNoHeaderReceivedAt A a s ∗ memRegion (a + 456#64) 464
  | .headerReceived s => chunkedHeaderReceivedAt A a s ∗ memRegion (a + 480#64) 440
  | .ct1Sampled s => chunkedCt1SampledTail920At A a s
  | .ekReceivedCt1Sampled s => chunkedEkReceivedCt1SampledAt A a s ∗ memRegion (a + 528#64) 392
  | .ct1Acknowledged s => chunkedCt1AcknowledgedAt A a s ∗ memRegion (a + 528#64) 392
  | .ct2Sampled s => chunkedCt2SampledAt A a s ∗ memRegion (a + 456#64) 464

theorem chunkedStatesAt_eq_word0_tail920 (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : States spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A a st =
      (a ↦₆₄ chunkedStatesWord0 st) ∗ chunkedStatesTail920At A (a + 8#64) st := by
  cases st with
  | keysUnsampled _ => dsimp only [chunkedStatesAt, chunkedStatesWord0, chunkedStatesTail920At]; rw [show (a + 8#64) + 56#64 = a + 64#64 by bv_omega]
  | keysSampled _ | ct1Received _ | ekSentCt1Received _ =>
    dsimp only [chunkedStatesAt, chunkedStatesWord0, chunkedStatesTail920At]; rw [show (a + 8#64) + 504#64 = a + 512#64 by bv_omega]
  | headerSent _ => dsimp only [chunkedStatesAt, chunkedStatesWord0, chunkedStatesTail920At]; rw [show (a + 8#64) + 880#64 = a + 888#64 by bv_omega]
  | noHeaderReceived _ | ct2Sampled _ =>
    dsimp only [chunkedStatesAt, chunkedStatesWord0, chunkedStatesTail920At]; rw [show (a + 8#64) + 456#64 = a + 464#64 by bv_omega]
  | headerReceived _ => dsimp only [chunkedStatesAt, chunkedStatesWord0, chunkedStatesTail920At]; rw [show (a + 8#64) + 480#64 = a + 488#64 by bv_omega]
  | ct1Sampled s => exact chunkedCt1SampledAt_eq_tag_tail920 A a s
  | ekReceivedCt1Sampled _ | ct1Acknowledged _ =>
    dsimp only [chunkedStatesAt, chunkedStatesWord0, chunkedStatesTail920At]; rw [show (a + 8#64) + 528#64 = a + 536#64 by bv_omega]

theorem Relocatable.of_chunkedStatesTail920At (A : RustAlloc) {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) :
    Relocatable 920 (fun a => chunkedStatesTail920At A a st) := by
  cases st with
  | keysUnsampled s => exact Relocatable.withPad rfl rfl (by decide) (Relocatable.of_chunkedKeysUnsampledAt A s)
  | keysSampled s => exact Relocatable.withPad rfl rfl (by decide) (Relocatable.of_chunkedKeysSampledAt A s)
  | headerSent s => exact Relocatable.withPad rfl rfl (by decide) (Relocatable.of_chunkedHeaderSentAt A s)
  | ct1Received s => exact Relocatable.withPad rfl rfl (by decide) (Relocatable.of_chunkedCt1ReceivedAt A s)
  | ekSentCt1Received s => exact Relocatable.withPad rfl rfl (by decide) (Relocatable.of_chunkedEkSentCt1ReceivedAt A s)
  | noHeaderReceived s => exact Relocatable.withPad rfl rfl (by decide) (Relocatable.of_chunkedNoHeaderReceivedAt A s)
  | headerReceived s => exact Relocatable.withPad rfl rfl (by decide) (Relocatable.of_chunkedHeaderReceivedAt A s)
  | ct1Sampled s => exact Relocatable.of_chunkedCt1SampledTail920At A s
  | ekReceivedCt1Sampled s => exact Relocatable.withPad rfl rfl (by decide) (Relocatable.of_chunkedEkReceivedCt1SampledAt A s)
  | ct1Acknowledged s => exact Relocatable.withPad rfl rfl (by decide) (Relocatable.of_chunkedCt1AcknowledgedAt A s)
  | ct2Sampled s => exact Relocatable.withPad rfl rfl (by decide) (Relocatable.of_chunkedCt2SampledAt A s)

theorem polyEncoderTagVal_add_one_ne_zero (es : EncoderState) : polyEncoderTagVal es + 1#64 ≠ 0#64 := by
  cases es <;> (dsimp only [polyEncoderTagVal]; decide)

@[simp, arm64_norm, wp_norm]
theorem polyEncoderTagVal_add_one_beq_zero (es : EncoderState) :
    (polyEncoderTagVal es + 1#64 == 0#64) = false := by cases es <;> rfl

/-- Representation of `v1send.msg.payload` at `0x31458` in `w24` and `sp + 0x550..0x576`. -/
def spqrSendPayloadSlotAt (sp : BitVec 64) (w24 : BitVec 8) (p : MessagePayload spqrPolyApi) : SepProp :=
  match p with
  | .none => ⌜w24 = 0#8⌝ ∗ memRegion (sp + 0x550#64) 38
  | .hdr c => ⌜w24 = 1#8⌝ ∗ chunkAt (sp + 0x550#64) c ∗ memRegion (sp + 0x572#64) 4
  | .ek c => ⌜w24 = 2#8⌝ ∗ chunkAt (sp + 0x550#64) c ∗ memRegion (sp + 0x572#64) 4
  | .ekCt1Ack c => ⌜w24 = 3#8⌝ ∗ chunkAt (sp + 0x550#64) c ∗ memRegion (sp + 0x572#64) 4
  | .ct1Ack _ => ⌜w24 = 4#8⌝ ∗ memRegion (sp + 0x550#64) 38
  | .ct1 c => ⌜w24 = 5#8⌝ ∗ chunkAt (sp + 0x550#64) c ∗ memRegion (sp + 0x572#64) 4
  | .ct2 c => ⌜w24 = 6#8⌝ ∗ chunkAt (sp + 0x550#64) c ∗ memRegion (sp + 0x572#64) 4

/-- Representation of `v1send.key : Option EpochSecret` at `0x31458` in `(x21, x27)` and `sp + 0x580..0x590`. -/
def spqrSendKeySlotAt (A : RustAlloc) (sp x21 x27 : BitVec 64) : Option EpochSecret → SepProp
  | none => ⌜x21 = noneCap⌝ ∗ memRegion (sp + 0x580#64) 16
  | some es =>
    ⌜x21.toNat < 2 ^ 63⌝ ∗ vecU8Buf A x21 x27 es.secret ∗
      ((sp + 0x580#64) ↦₆₄ BitVec.ofNat 64 es.secret.length) ∗ ((sp + 0x588#64) ↦₆₄ es.epoch)

/-! ## Epoch Exposure Lemmas -/

private theorem expose_4 (A B C E : SepProp) : A ∗ B ∗ C ∗ E = E ∗ (A ∗ B ∗ C) := by ac_rfl
private theorem expose_5 (A B C D E : SepProp) : A ∗ B ∗ C ∗ D ∗ E = E ∗ (A ∗ B ∗ C ∗ D) := by ac_rfl
private theorem expose_first (E R1 R2 : SepProp) : (E ∗ R1) ∗ R2 = E ∗ (R1 ∗ R2) := by ac_rfl
private theorem expose_middle (R0 E R1 R2 : SepProp) : R0 ∗ (E ∗ R1) ∗ R2 = E ∗ (R0 ∗ R1 ∗ R2) := by ac_rfl
private theorem expose_tail_2 (A E R1 R2 : SepProp) : ((A ∗ E) ∗ R1) ∗ R2 = E ∗ (A ∗ R1 ∗ R2) := by ac_rfl
private theorem expose_hdrSent (A B C D E : SepProp) : A ∗ (B ∗ C ∗ E) ∗ D = E ∗ (A ∗ B ∗ C ∗ D) := by ac_rfl
private theorem expose_ct1Recv (A B C D E : SepProp) : A ∗ (B ∗ C ∗ D ∗ E) = E ∗ (A ∗ B ∗ C ∗ D) := by ac_rfl
private theorem expose_ct2Samp (A B E : SepProp) : A ∗ (B ∗ E) = E ∗ (A ∗ B) := by ac_rfl
private theorem expose_ekRecvCt1Samp (A B C D F E : SepProp) :
    A ∗ (B ∗ C ∗ D ∗ F ∗ E) = E ∗ (A ∗ B ∗ C ∗ D ∗ F) := by ac_rfl

theorem expose_epoch_ekSentCt1Received (A : RustAlloc) {F : ShaCompress} (sp : BitVec 64)
    (s : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    ∃ R : SepProp, chunkedStatesTail920At A (sp + 0x958#64) (.ekSentCt1Received s) =
      ((sp + 2488#64) ↦₆₄ s.uc.epoch) ∗ R := by
  dsimp only [chunkedStatesTail920At, chunkedEkSentCt1ReceivedAt, unchunkedEkSentCt1ReceivedAt]
  rw [show (sp + 0x958#64) + 96#64 = sp + 2488#64 by bv_omega, expose_4, expose_first, expose_first]
  exact ⟨_, rfl⟩

theorem expose_epoch_noHeaderReceived (A : RustAlloc) {F : ShaCompress} (sp : BitVec 64)
    (s : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    ∃ R : SepProp, chunkedStatesTail920At A (sp + 0x958#64) (.noHeaderReceived s) =
      ((sp + 2440#64) ↦₆₄ s.uc.epoch) ∗ R := by
  dsimp only [chunkedStatesTail920At, chunkedNoHeaderReceivedAt, unchunkedNoHeaderReceivedAt]
  rw [show (sp + 0x958#64) + 48#64 = sp + 2440#64 by bv_omega, expose_tail_2]; exact ⟨_, rfl⟩

theorem expose_epoch_ct1Acknowledged (A : RustAlloc) {F : ShaCompress} (sp : BitVec 64)
    (s : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    ∃ R : SepProp, chunkedStatesTail920At A (sp + 0x958#64) (.ct1Acknowledged s) =
      ((sp + 2512#64) ↦₆₄ s.uc.epoch) ∗ R := by
  dsimp only [chunkedStatesTail920At, chunkedCt1AcknowledgedAt, unchunkedCt1SentAt]
  rw [show (sp + 0x958#64) + 120#64 = sp + 2512#64 by bv_omega, expose_5, expose_first, expose_first]
  exact ⟨_, rfl⟩

theorem expose_epoch_headerSent (A : RustAlloc) {F : ShaCompress} (sp : BitVec 64)
    (s : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) :
    ∃ R : SepProp, chunkedHeaderSentAt A (sp + 0x958#64) s =
      ((sp + 2864#64) ↦₆₄ s.uc.epoch) ∗ R := by
  dsimp only [chunkedHeaderSentAt, unchunkedEkSentAt]
  rw [show ((sp + 0x958#64) + 400#64) + 72#64 = sp + 2864#64 by bv_omega, expose_hdrSent]; exact ⟨_, rfl⟩

theorem expose_epoch_ct1Received (A : RustAlloc) {F : ShaCompress} (sp : BitVec 64)
    (s : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)) :
    ∃ R : SepProp, chunkedCt1ReceivedAt A (sp + 0x958#64) s =
      ((sp + 2888#64) ↦₆₄ s.uc.epoch) ∗ R := by
  dsimp only [chunkedCt1ReceivedAt, unchunkedEkSentCt1ReceivedAt]
  rw [show ((sp + 0x958#64) + 400#64) + 96#64 = sp + 2888#64 by bv_omega, expose_ct1Recv]; exact ⟨_, rfl⟩

theorem expose_epoch_ct1Sampled (A : RustAlloc) {F : ShaCompress} (sp : BitVec 64)
    (s : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) :
    ∃ R : SepProp, chunkedCt1SampledAt A (sp + 0x950#64) s =
      ((sp + 2904#64) ↦₆₄ s.uc.epoch) ∗ R := by
  dsimp only [chunkedCt1SampledAt, unchunkedCt1SentAt]
  rw [show ((sp + 0x950#64) + 400#64) + 120#64 = sp + 2904#64 by bv_omega, expose_5, expose_middle]
  exact ⟨_, rfl⟩

theorem expose_epoch_ct2Sampled (A : RustAlloc) {F : ShaCompress} (sp : BitVec 64)
    (s : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    ∃ R : SepProp, chunkedCt2SampledAt A (sp + 0x958#64) s =
      ((sp + 2840#64) ↦₆₄ s.uc.epoch) ∗ R := by
  dsimp only [chunkedCt2SampledAt, unchunkedCt2SentAt]
  rw [show ((sp + 0x958#64) + 400#64) + 48#64 = sp + 2840#64 by bv_omega, expose_ct2Samp]; exact ⟨_, rfl⟩

theorem expose_epoch_ekReceivedCt1Sampled (A : RustAlloc) {F : ShaCompress} (sp : BitVec 64)
    (s : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    ∃ R : SepProp, chunkedEkReceivedCt1SampledAt A (sp + 0x958#64) s =
      ((sp + 2912#64) ↦₆₄ s.uc.epoch) ∗ R := by
  dsimp only [chunkedEkReceivedCt1SampledAt, unchunkedCt1SentEkReceivedAt]
  rw [show ((sp + 0x958#64) + 400#64) + 120#64 = sp + 2912#64 by bv_omega, expose_ekRecvCt1Samp]
  exact ⟨_, rfl⟩

/-! ## Chunk Slot Extraction and Recomposition -/

theorem chunkAt_extract_words (c : Chunk) :
    ∃ w0 w1 w2 w3 : BitVec 64, ∀ a : BitVec 64, chunkAt a c =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₁₆ c.index) := by
  obtain ⟨w0, w1, w2, w3, hw⟩ :=
    CryptoVerification.SpqrV1.Top.MessageSerialize.list_eq_unpack64_4_of_len32
      c.data.toList (List.Vector.toList_length c.data)
  refine ⟨w0, w1, w2, w3, fun a => ?_⟩; unfold chunkAt chunkIndexOff
  rw [hw, CryptoVerification.SpqrV1.Top.MessageSerialize.pointsToBytes_unpack64_4_eq]; ac_rfl

theorem chunkAt_entails_memRegion (a : BitVec 64) (c : Chunk) :
    chunkAt a c ⊢ memRegion a 34 := by
  unfold chunkAt chunkIndexOff
  have h1 : (a ↦ₛ c.data.toList) ⊢ memRegion a 32 := by
    have hm := pointsToBytes_entails_memRegion a c.data.toList
    rwa [List.Vector.toList_length c.data] at hm
  have h2 : ((a + 32#64) ↦₁₆ c.index) ⊢ memRegion (a + 32#64) 2 := by
    rw [pointsTo16_eq_pointsToBytes, ← unpack16_length c.index]; exact pointsToBytes_entails_memRegion _ _
  refine Entails.trans (sepConj_mono h1 h2) ?_
  rw [ProofLib.memRegion_split' (b := a) (n := 32) (k := 2) (b' := a + 32#64) rfl rfl (by decide)]
  exact Entails.refl _

theorem memRegion_38_eq_chunk_slot (sp : BitVec 64) :
    memRegion (sp + 0x550#64) 38 =
      (∃∗ d0 : BitVec 64, (sp + 0x550#64) ↦₆₄ d0) ∗ (∃∗ d1 : BitVec 64, (sp + 0x558#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp + 0x560#64) ↦₆₄ d2) ∗ (∃∗ d3 : BitVec 64, (sp + 0x568#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 16, (sp + 0x570#64) ↦₁₆ d4) ∗ memRegion (sp + 0x572#64) 4 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x550#64) (n := 8) (k := 30) (b' := sp + 0x558#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x558#64) (n := 8) (k := 22) (b' := sp + 0x560#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x560#64) (n := 8) (k := 14) (b' := sp + 0x568#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x568#64) (n := 8) (k := 6) (b' := sp + 0x570#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x570#64) (n := 2) (k := 4) (b' := sp + 0x572#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0x550#64), ProofLib.memRegion_eight (sp + 0x558#64),
      ProofLib.memRegion_eight (sp + 0x560#64), ProofLib.memRegion_eight (sp + 0x568#64),
      ProofLib.memRegion_two (sp + 0x570#64)]

theorem word0_tail920_entails_memRegion_928 (sp w : BitVec 64) :
    ((sp + 0x950#64) ↦₆₄ w) ∗ memRegion (sp + 0x958#64) 920 ⊢ memRegion (sp + 0x950#64) 928 := by
  have h8 : ((sp + 0x950#64) ↦₆₄ w) ⊢ memRegion (sp + 0x950#64) 8 := by
    rw [pointsTo64_eq_pointsToBytes, ← unpack64_length w]; exact pointsToBytes_entails_memRegion _ _
  refine Entails.trans (sepConj_mono_left h8) ?_
  rw [ProofLib.memRegion_split' (b := sp + 0x950#64) (n := 8) (k := 920) (b' := sp + 0x958#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

/-! ## Relocation Helper (`call_memcpy_relocate`) and Join State -/

open CryptoVerification.CodeLayout in
theorem libsignalSessionCode_fnOff_memcpy : libsignalSessionCode.fnOff "memcpy" = num% (ls_off% "memcpy") := ls_stub% "memcpy"

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

open CryptoVerification.CodeLayout in
theorem spqrSend_memcpy_ok {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "memcpy")) sessionMemcpyRegionSpec :=
  hA.session_memcpy_region_ok_at spqrSendName (num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "memcpy"))

theorem relocate_pre_entails {n : Nat} {F : BitVec 64 → SepProp}
    (hrel : Relocatable n F) (dst src : BitVec 64) (Rest : SepProp) :
    (memRegion dst n ∗ F src) ∗ Rest ⊢
      ∃∗ bs : List (BitVec 8), ⌜bs.length = n⌝ ∗
        ((memRegion dst n ∗ (src ↦ₛ bs)) ∗ (relocatedHeap F bs ∗ Rest)) := by
  refine Entails.trans (sepConj_mono_left (sepConj_mono_right (hrel src))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply ProofLib.Entails.sepExists_elim; intro bs
  exact Entails.sepExists_right bs (Entails.of_eq (by ac_rfl))

theorem relocate_post_entails {n : Nat} {F : BitVec 64 → SepProp}
    (dst src : BitVec 64) {bs : List (BitVec 8)} (hlen : bs.length = n) (Rest : SepProp) :
    ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ (relocatedHeap F bs ∗ Rest) ⊢ (F dst ∗ memRegion src n) ∗ Rest := by
  have hrearrange :
      ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ (relocatedHeap F bs ∗ Rest) =
      (((dst ↦ₛ bs) ∗ relocatedHeap F bs) ∗ (src ↦ₛ bs)) ∗ Rest := by ac_rfl
  rw [hrearrange]
  refine sepConj_mono_left (sepConj_mono (relocatedHeap_recompose F bs dst) ?_)
  have hm := pointsToBytes_entails_memRegion src bs; rwa [hlen] at hm

/-- Framed `memcpy` call rule that relocates any `Relocatable n F` predicate from `src` to `dst`. -/
theorem call_memcpy_relocate {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionSpec)
    {n : Nat} {F : BitVec 64 → SepProp} (hrel : Relocatable n F) (dst src : BitVec 64)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = dst) (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n) (hsplit : P = (memRegion dst n ∗ F src) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call → sf.trace = s0.trace →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP prog target_pc sf ((F dst ∗ memRegion src n) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.fold (relocate_pre_entails hrel dst src Frame) (sepConj_emp _).symm ?_
  rw [sepConj_emp]; wp_pull_exists; rename_i bs
  refine SepWP.pure_elim fun hlen => ?_
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs)) (F := relocatedHeap F bs ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [sessionMemcpyRegionSpec]; rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    refine SepWP.fold (relocate_post_entails dst src hlen Frame) (sepConj_emp _).symm ?_; rw [sepConj_emp]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) (htr.trans htrace)
      hcs_sf.1 hcs_sf.2.1 hcs_sf.2.2.1 hcs_sf.2.2.2.1 hcs_sf.2.2.2.2.1
      hcs_sf.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.1
      hcs_sf.2.2.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.2.2.2.2

/-- Register and state conditions at the post-`States::send` join point `0x31458` (`entry + 3068#64`). -/
structure SpqrSendJoinState {F : ShaCompress} (b sp : BitVec 64)
    (ext : String → Option (State → State)) (s0 sf : State) (msg : Message spqrPolyApi)
    (st1 : States spqrPolyApi (spqrAuthApi F)) : Prop where
  pc : sf.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 3068#64
  run : sf.status = .Running
  sp_eq : sf.sp = sp
  trace : sf.trace = s0.trace
  x19 : sf.readReg64 .x19 = s0.readReg64 .x19
  x20 : sf.readReg64 .x20 = chunkedStatesWord0 st1
  x22 : sf.readReg64 .x22 = msg.epoch
  x25 : sf.readReg64 .x25 = sp + 0x550#64
  x26 : sf.readReg64 .x26 = sp + 0x1260#64
  x28 : sf.readReg64 .x28 = s0.readReg64 .x28
  vregs : calleeSavedVRegs sf = calleeSavedVRegs s0

/-! ## Immediate Arms (`.ekSentCt1Received`, `.noHeaderReceived`, `.ct1Acknowledged`) -/

theorem imm_arm_post_entails {F : ShaCompress} (A : RustAlloc) (sp w0 x21 x27 : BitVec 64)
    (tag : BitVec 8) (pay : MessagePayload spqrPolyApi) (st1 : States spqrPolyApi (spqrAuthApi F))
    (Frame : SepProp) (hx21 : x21 = noneCap) (hpay : spqrSendPayloadSlotAt sp tag pay = memRegion (sp + 0x550#64) 38) :
    (chunkedStatesTail920At A (sp + 0x590#64) st1 ∗ memRegion (sp + 0x958#64) 920) ∗
      ((sp + 0x950#64) ↦₆₄ w0) ∗ memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ Frame ⊢
    (memRegion (sp + 0x950#64) 928 ∗ spqrSendPayloadSlotAt sp tag pay ∗
      spqrSendKeySlotAt A sp x21 x27 none ∗ chunkedStatesTail920At A (sp + 0x590#64) st1) ∗ Frame := by
  rw [hpay, hx21]; dsimp only [spqrSendKeySlotAt]
  have hrearr :
      (chunkedStatesTail920At A (sp + 0x590#64) st1 ∗ memRegion (sp + 0x958#64) 920) ∗
        ((sp + 0x950#64) ↦₆₄ w0) ∗ memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ Frame =
      (((sp + 0x950#64) ↦₆₄ w0) ∗ memRegion (sp + 0x958#64) 920) ∗
        (memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗
          chunkedStatesTail920At A (sp + 0x590#64) st1 ∗ Frame) := by ac_rfl
  rw [hrearr]; refine Entails.trans (sepConj_mono_left (word0_tail920_entails_memRegion_928 sp w0)) ?_
  have hgoal :
      ((memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x550#64) 38 ∗
        (⌜noneCap = noneCap⌝ ∗ memRegion (sp + 0x580#64) 16) ∗
        chunkedStatesTail920At A (sp + 0x590#64) st1) ∗ Frame) =
      ⌜noneCap = noneCap⌝ ∗ (memRegion (sp + 0x950#64) 928 ∗
        (memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗
          chunkedStatesTail920At A (sp + 0x590#64) st1 ∗ Frame)) := by ac_rfl
  rw [hgoal]; exact Entails.pure_right rfl (Entails.refl _)

theorem finish_sepWP {prog : Program} {ret : BitVec 64} {s : State} {P Q : SepProp}
    {post : State → SepProp → Prop} (hnext : SepWP prog ret s Q post) (hent : P ⊢ Q) :
    SepWP prog ret s P post := by
  refine SepWP.fold hent (sepConj_emp _).symm ?_; rw [sepConj_emp]; exact hnext

/-- Immediate arm 1: `.ekSentCt1Received s` (`0x30bf8 -> 0x31454 -> 0x31458`). -/
theorem step_send_arm_ekSentCt1Received {F : ShaCompress}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContracts b A ext) {s0 s : State} (sp : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 924#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = 6#64) (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx25 : s.readReg64 .x25 = sp + 0x550#64) (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (chunkedStatesAt A (sp + 0x950#64) (.ekSentCt1Received st) ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920) ∗ Frame)
    (hnext : ∀ sf : State, SpqrSendJoinState b sp ext s0 sf
        { epoch := st.uc.epoch, payload := .ct1Ack true } (.ekSentCt1Received st) →
      SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 3068#64) sf
        ((memRegion (sp + 0x950#64) 928 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct1Ack true) ∗
          spqrSendKeySlotAt A sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A (sp + 0x590#64) (.ekSentCt1Received st)) ∗ Frame) post) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 3068#64) s P post := by
  have hmemcpy := spqrSend_memcpy_ok hA
  spqr_send_fetches_range b (Rust.withPanics ext) 924 28
  spqr_send_fetches_range b (Rust.withPanics ext) 3064 4
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr spqrSendName = entry
  examples_hide_fetches; subst hP
  rw [chunkedStatesAt_eq_word0_tail920 A (sp + 0x950#64) (.ekSentCt1Received st),
      show (sp + 0x950#64) + 8#64 = sp + 0x958#64 by bv_omega]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_ekSentCt1Received A sp st; rw [h_ep]; wp_steps; rw [← h_ep]
  refine call_memcpy_relocate hmemcpy (Relocatable.of_chunkedStatesTail920At A (.ekSentCt1Received st))
    (sp + 0x590#64) (sp + 0x958#64) (s0 := s0) (sp_call := sp)
    (Frame := ((sp + 0x950#64) ↦₆₄ 6#64) ∗ memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := entry + 944#64) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by dsimp only [chunkedStatesWord0]; ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf; wp_steps
  refine finish_sepWP
    (hnext _ ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, chunkedStatesWord0, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *]⟩)
    (imm_arm_post_entails A sp 6#64 _ _ _ (.ct1Ack true) (.ekSentCt1Received st) Frame
      (by simp only [arm64_norm]; rfl) (by dsimp only [spqrSendPayloadSlotAt]; simp only [arm64_norm]))

/-- Immediate arm 2: `.noHeaderReceived s` (`0x30d60 -> 0x31454 -> 0x31458`). -/
theorem step_send_arm_noHeaderReceived {F : ShaCompress}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContracts b A ext) {s0 s : State} (sp : BitVec 64)
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 1284#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = 7#64) (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx25 : s.readReg64 .x25 = sp + 0x550#64) (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (chunkedStatesAt A (sp + 0x950#64) (.noHeaderReceived st) ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920) ∗ Frame)
    (hnext : ∀ sf : State, SpqrSendJoinState b sp ext s0 sf
        { epoch := st.uc.epoch, payload := .none } (.noHeaderReceived st) →
      SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 3068#64) sf
        ((memRegion (sp + 0x950#64) 928 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) .none ∗
          spqrSendKeySlotAt A sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A (sp + 0x590#64) (.noHeaderReceived st)) ∗ Frame) post) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 3068#64) s P post := by
  have hmemcpy := spqrSend_memcpy_ok hA
  spqr_send_fetches_range b (Rust.withPanics ext) 1284 28
  spqr_send_fetches_range b (Rust.withPanics ext) 3064 4
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr spqrSendName = entry
  examples_hide_fetches; subst hP
  rw [chunkedStatesAt_eq_word0_tail920 A (sp + 0x950#64) (.noHeaderReceived st),
      show (sp + 0x950#64) + 8#64 = sp + 0x958#64 by bv_omega]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_noHeaderReceived A sp st; rw [h_ep]; wp_steps; rw [← h_ep]
  refine call_memcpy_relocate hmemcpy (Relocatable.of_chunkedStatesTail920At A (.noHeaderReceived st))
    (sp + 0x590#64) (sp + 0x958#64) (s0 := s0) (sp_call := sp)
    (Frame := ((sp + 0x950#64) ↦₆₄ 7#64) ∗ memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := entry + 1304#64) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by dsimp only [chunkedStatesWord0]; ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf; wp_steps
  refine finish_sepWP
    (hnext _ ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, chunkedStatesWord0, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *]⟩)
    (imm_arm_post_entails A sp 7#64 _ _ _ .none (.noHeaderReceived st) Frame
      (by simp only [arm64_norm]; rfl) (by dsimp only [spqrSendPayloadSlotAt]; simp only [arm64_norm]))

/-- Immediate arm 3: `.ct1Acknowledged s` (`0x30c14 -> 0x30d64 -> 0x31454 -> 0x31458`). -/
theorem step_send_arm_ct1Acknowledged {F : ShaCompress}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContracts b A ext) {s0 s : State} (sp : BitVec 64)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 952#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = 11#64) (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx25 : s.readReg64 .x25 = sp + 0x550#64) (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (chunkedStatesAt A (sp + 0x950#64) (.ct1Acknowledged st) ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920) ∗ Frame)
    (hnext : ∀ sf : State, SpqrSendJoinState b sp ext s0 sf
        { epoch := st.uc.epoch, payload := .none } (.ct1Acknowledged st) →
      SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 3068#64) sf
        ((memRegion (sp + 0x950#64) 928 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) .none ∗
          spqrSendKeySlotAt A sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A (sp + 0x590#64) (.ct1Acknowledged st)) ∗ Frame) post) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 3068#64) s P post := by
  have hmemcpy := spqrSend_memcpy_ok hA
  spqr_send_fetches_range b (Rust.withPanics ext) 952 8
  spqr_send_fetches_range b (Rust.withPanics ext) 1288 24
  spqr_send_fetches_range b (Rust.withPanics ext) 3064 4
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr spqrSendName = entry
  examples_hide_fetches; subst hP
  rw [chunkedStatesAt_eq_word0_tail920 A (sp + 0x950#64) (.ct1Acknowledged st),
      show (sp + 0x950#64) + 8#64 = sp + 0x958#64 by bv_omega]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_ct1Acknowledged A sp st; rw [h_ep]; wp_steps; rw [← h_ep]
  refine call_memcpy_relocate hmemcpy (Relocatable.of_chunkedStatesTail920At A (.ct1Acknowledged st))
    (sp + 0x590#64) (sp + 0x958#64) (s0 := s0) (sp_call := sp)
    (Frame := ((sp + 0x950#64) ↦₆₄ 11#64) ∗ memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := entry + 1304#64) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by dsimp only [chunkedStatesWord0]; ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf; wp_steps
  refine finish_sepWP
    (hnext _ ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, chunkedStatesWord0, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *]⟩)
    (imm_arm_post_entails A sp 11#64 _ _ _ .none (.ct1Acknowledged st) Frame
      (by simp only [arm64_norm]; rfl) (by dsimp only [spqrSendPayloadSlotAt]; simp only [arm64_norm]))

/-! ## Leaf-Call Combinators -/

theorem stackAt_spqrSendCallee_split (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ stackAt sp n := by
  have hle' : n ≤ 123008 := hle
  have hbd : n + (spqrSendCalleeStack - n) ≤ 2 ^ 64 := by change n + (123008 - n) ≤ 2 ^ 64; omega
  have h := ProofLib.stackAt_split_bottom sp n (spqrSendCalleeStack - n) hbd
  rwa [Nat.add_sub_of_le hle] at h

/-- Run a non-panicking `SepWP` segment to `mid`, propagating `ImgCallInv img` to the continuation. -/
theorem of_sepWP_inImage {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} (img : Obj.Image) (hinv : ImgCallInv img s)
    (h : SepWP prog mid s P (fun sm Pm => ImgCallInv img sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL; obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | hoom⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ := hnext ⟨hsteps.frozenLoaded hinv.1, hsteps.symtab_eq.trans hinv.2⟩ R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

/-- Call a panic-capable subroutine (`(spec.inImage img)`) that uses `n ≤ spqrSendCalleeStack` bytes of stack. -/
theorem call_inImage_calleeStack {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide)
    {P T_pre : SepProp} {T_post : State → SepProp} {Q : State → SepProp → Prop} {Fr F : SepProp}
    {φ_pre : Prop} {φ_post : State → Prop}
    (hcall : subroutine_ok prog entry (spec.inImage img)) (hinv : ImgCallInv img s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec_pre : spec.pre x s = (⌜φ_pre⌝ ∗ T_pre ∗ stackAt s.sp n)) (hφ : φ_pre)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ T_pre) ∗ F)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap))
    (hspec_post : ∀ sf, spec.post x s sf = (⌜φ_post sf⌝ ∗ T_post sf ∗ stackAt s.sp n))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      φ_post sf → ImgCallInv img sf →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp prog ret sf ((stackAt sp spqrSendCalleeStack ∗ T_post sf) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  let F_ext := memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F
  have hsp_al : s.spAligned = true := by unfold State.spAligned; rw [hsp]; exact hsp_align
  refine ProofLib.SepWPp.call_wpp_frozen (x := x) (F := F_ext) hcall hinv.1 hinv.2 hpc hrun hsp_al hlr
    (fun R' hm => by
      change s.mem ⊨ (⌜ImgCallInv img s⌝ ∗ spec.pre x s) ∗ (F_ext ∗ R')
      rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hinv, ?_⟩
      rw [hspec_pre, hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hφ, ?_⟩
      rw [hP, stackAt_spqrSendCallee_split sp n hle] at hm
      exact Satisfies.mono (Entails.of_eq (by dsimp only [F_ext]; ac_rfl)) hm)
    (fun sm code R' _ hpost => by
      change sm.mem ⊨ spec.onExit x code s sm ∗ R' at hpost; rw [hexit_eq code sm] at hpost
      exact allowPanic_not_exited hpost)
    (fun sm _ _ hmFr => by
      change sm.mem ⊨ (spec.onPanic x s sm ∗ F_ext) ∗ Fr at hmFr; rw [hpan_eq sm] at hmFr
      refine allowPanic_frame ?_ hmFr
      rintro ⟨haf, hpr⟩; unfold allocFailedIn at haf ⊢; rw [htr] at haf hpr; exact ⟨haf, hpr⟩)
    (fun sm hpcm hrunm hspm hcsm hfzm hsymm R' hpost hLm => by
      change sm.mem ⊨ (spec.post x s sm ∗ F_ext) ∗ R' at hpost
      rw [sepConj_assoc, hspec_post sm, hsp] at hpost
      have hpost' : sm.mem ⊨ ⌜φ_post sm⌝ ∗ (((stackAt sp spqrSendCalleeStack ∗ T_post sm) ∗ F) ∗ R') := by
        rw [stackAt_spqrSendCallee_split sp n hle]
        exact Satisfies.mono (Entails.of_eq (by dsimp only [F_ext]; ac_rfl)) hpost
      rw [satisfies_pure_sepConj] at hpost'; rcases hpost' with ⟨hφ_post, hpost_mem⟩
      rw [hsp] at hspm
      rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, _, hvregs⟩
      exact hnext sm hpcm hrunm hspm hφ_post ⟨hfzm, hsymm⟩
        hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs R' hpost_mem hLm)
    (fun sm R' _ hpost => by
      change sm.mem ⊨ spec.onOom x s sm ∗ (F_ext ∗ R') at hpost; rw [hoom_eq sm] at hpost
      exact (allowPanic_not_exited hpost).elim)

@[simp, arm64_norm, wp_norm]
theorem setWidth_16_zeroExtend_64 (v : BitVec 16) : (v.zeroExtend 64).setWidth 16 = v := by bv_kernel

@[simp, arm64_norm, wp_norm]
theorem setWidth_16_zeroExtend_32_64 (v : BitVec 16) :
    ((v.zeroExtend 32).zeroExtend 64).setWidth 16 = v := by bv_kernel

theorem scratch_and_chunk_entails_memRegion (sp : BitVec 64) (sz : Nat) (chunk : Chunk)
    (hsz : sz ≤ 928 := by decide) :
    memRegion (sp + 0x1260#64) sz ∗ chunkAt ((sp + 0x1260#64) + BitVec.ofNat 64 sz) chunk ⊢
      memRegion (sp + 0x1260#64) (sz + chunkSize) := by
  refine Entails.trans (sepConj_mono_right (chunkAt_entails_memRegion _ chunk)) ?_
  have hle : sz + 34 ≤ 2 ^ 64 := by omega
  rw [← ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := sz) (k := 34)
      (b' := (sp + 0x1260#64) + BitVec.ofNat 64 sz) rfl rfl hle]; exact Entails.refl _

theorem word0_sz_pad_entails_memRegion_928 (sp w : BitVec 64) (sz : Nat) (hsz : sz ≤ 920 := by decide) :
    ((sp + 0x950#64) ↦₆₄ w) ∗ memRegion (sp + 0x958#64) sz ∗
      memRegion ((sp + 0x958#64) + BitVec.ofNat 64 sz) (920 - sz) ⊢ memRegion (sp + 0x950#64) 928 := by
  have hle : sz + (920 - sz) ≤ 2 ^ 64 := by omega
  have hsplit := ProofLib.memRegion_split' (b := sp + 0x958#64) (n := sz) (k := 920 - sz)
    (b' := (sp + 0x958#64) + BitVec.ofNat 64 sz) rfl rfl hle
  rw [Nat.add_sub_of_le hsz] at hsplit; rw [← hsplit]; exact word0_tail920_entails_memRegion_928 sp w

theorem chunkAt_sp_add_eq (sp off off8 off16 off24 off32 : BitVec 64) (c : Chunk)
    (w0 w1 w2 w3 : BitVec 64)
    (hw : ∀ a : BitVec 64, chunkAt a c =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₁₆ c.index))
    (h8 : (sp + off) + 8#64 = sp + off8 := by rw [BitVec.add_assoc]; rfl)
    (h16 : (sp + off) + 16#64 = sp + off16 := by rw [BitVec.add_assoc]; rfl)
    (h24 : (sp + off) + 24#64 = sp + off24 := by rw [BitVec.add_assoc]; rfl)
    (h32 : (sp + off) + 32#64 = sp + off32 := by rw [BitVec.add_assoc]; rfl) :
    chunkAt (sp + off) c =
      ((sp + off) ↦₆₄ w0) ∗ ((sp + off8) ↦₆₄ w1) ∗ ((sp + off16) ↦₆₄ w2) ∗
      ((sp + off24) ↦₆₄ w3) ∗ ((sp + off32) ↦₁₆ c.index) := by
  rw [hw (sp + off), h8, h16, h24, h32]

theorem finish_sepWP_inImage {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q onPanic : State → SepProp → Prop} {img : Obj.Image}
    (hpc : s.pc = mid) (hrun : s.status = .Running)
    (hnext : ImgCallInv img s → SepWPp prog ret s P' Q onPanic) (hent : P ⊢ P') :
    SepWP prog mid s P (fun sm Pm => ImgCallInv img sm → SepWPp prog ret sm Pm Q onPanic) := by
  refine SepWP.fold hent (sepConj_emp _).symm ?_; rw [sepConj_emp]; exact SepWP.done hpc hrun hnext

theorem leaf_arm_post_entails {F : ShaCompress} (b : BitVec 64) (A : RustAlloc)
    (sp w0 x21 x27 : BitVec 64) (x24_8 : BitVec 8) (sz : Nat)
    (P F_out : SepProp) (chunk : Chunk)
    (pay : MessagePayload spqrPolyApi) (nextSt : States spqrPolyApi (spqrAuthApi F))
    (Frame : SepProp) (hsz : sz ≤ 920 := by decide) (hx21 : x21 = LibsignalTripleRatchetRepr.noneCap)
    (hpay : chunkAt (sp + 0x550#64) chunk ∗ memRegion (sp + 0x572#64) 4 ⊢ spqrSendPayloadSlotAt sp x24_8 pay)
    (htail : F_out ∗ memRegion ((sp + 0x590#64) + BitVec.ofNat 64 sz) (920 - sz) =
      chunkedStatesTail920At A (sp + 0x590#64) nextSt)
    (hP_eq : P = (stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitAt b ∗ reduceTableAt b ∗
        (((sp + 0x950#64) ↦₆₄ w0) ∗ memRegion (sp + 0x958#64) sz ∗
          memRegion ((sp + 0x958#64) + BitVec.ofNat 64 sz) (920 - sz)) ∗
        (memRegion (sp + 0x1260#64) sz ∗ chunkAt ((sp + 0x1260#64) + BitVec.ofNat 64 sz) chunk) ∗
        (chunkAt (sp + 0x550#64) chunk ∗ memRegion (sp + 0x572#64) 4) ∗ memRegion (sp + 0x580#64) 16 ∗
        (F_out ∗ memRegion ((sp + 0x590#64) + BitVec.ofNat 64 sz) (920 - sz))) ∗ Frame) :
    P ⊢ (stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitAt b ∗ reduceTableAt b ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (sz + chunkSize) ∗
        spqrSendPayloadSlotAt sp x24_8 pay ∗ spqrSendKeySlotAt A sp x21 x27 none ∗
        chunkedStatesTail920At A (sp + 0x590#64) nextSt) ∗ Frame := by
  have hkey : memRegion (sp + 0x580#64) 16 ⊢ spqrSendKeySlotAt A sp x21 x27 none := by
    dsimp only [spqrSendKeySlotAt]; exact Entails.pure_right hx21 (Entails.refl _)
  have h1 := word0_sz_pad_entails_memRegion_928 sp w0 sz hsz
  have h2 := scratch_and_chunk_entails_memRegion sp sz chunk (by omega)
  rw [hP_eq, htail]
  exact sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono hpay (sepConj_mono_left hkey))))))))


end CryptoVerification.SpqrV1.Top.Send
