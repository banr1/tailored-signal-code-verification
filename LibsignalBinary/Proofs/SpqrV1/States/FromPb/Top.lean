/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbProof
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Proof
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Proof
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10d
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4e
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Top-Level Assembly (`0x5a0a4`)

**Checked by Lean.**

Discharges `<PolyEncoder>::from_pb` (`0x62188`), `<PolyDecoder>::from_pb` (`0x62b1c`), and all 12
`Option V1State.InnerState` branches (`none` plus Variants `0..10`) to prove `StatesFromPbOkExt` and
`StatesFromPbOkX` unconditionally from `AllocContracts`.
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
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## 1. Complete `subroutine_ok` Wrappers for Variants 1, 4, 5, 6, 8, 10 -/

/-- Variant 1 (`InnerState.keysSampled`, `+1104`) of `<States>::from_pb`. -/
theorem states_from_pb_keysSampled_ok_ext
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (henc : EncoderFromPbOkExt b A ext)
    (s : V1State.Chunked.KeysSampled) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName)
      (statesFromPbVariantSpec A F b { innerState := some (.keysSampled s) }) :=
  sfpProof_tagged_ok_of_step TaggedVariantDispatch.keysSampled
    (Tail := fun pbA => protoChunkedKeysSampledAt A (pbA + 8#64) s ∗ memRegion (pbA + 168#64) 56)
    (fun _ => rfl)
    (states_from_pb_keysSampled_1104 hA henc s)

/-- Variant 4 (`InnerState.ekSentCt1Received`, `+248`) of `<States>::from_pb`. -/
theorem states_from_pb_ekSentCt1Received_ok_ext
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (hdec : DecoderFromPbOkExt b A ext)
    (s : V1State.Chunked.EkSentCt1Received) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName)
      (statesFromPbVariantSpec A F b { innerState := some (.ekSentCt1Received s) }) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨out, pbA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [statesFromPbVariantSpec, v1StatePtsBound, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hb_align, _⟩, hmem⟩
  refine ⟨stackAt s0.sp statesFromPbStack ∗
      (memRegion out chunkedStatesSize ∗
       optProtoInnerStateAt A pbA (some (.ekSentCt1Received s)) ∗
       statesFromPbJumpTableAt b ∗
       A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  have hpro := states_from_pb_prologue (b := b) (ext := ext) s0 out pbA
    (memRegion out chunkedStatesSize ∗
     optProtoInnerStateAt A pbA (some (.ekSentCt1Received s)) ∗
     statesFromPbJumpTableAt b ∗
     A.pool)
    hsp0_align hpc0 hrun0 hx8 hx0
  refine sepWPp_seq_clean hpro ?_
  intro s1 hpc1 hrun1 ⟨hsp1, _, hx8_1, hx0_1, htr1⟩
  have htag_eq : optProtoInnerStateAt A pbA (some (.ekSentCt1Received s)) =
      (pbA ↦₆₄ 0x8000000000000004#64) ∗
      (protoChunkedEkSentCt1ReceivedAt A (pbA + 8#64) s ∗
       memRegion (pbA + 152#64) 72) := rfl
  have hfsp := cell0_2296_entails_memRegion_2304 (s0.sp - 2400#64) 0#64
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
    (((s0.sp - 2400#64) ↦₆₄ 0#64) ∗ memRegion ((s0.sp - 2400#64) + 8#64) 2296) ∗
    ((pbA ↦₆₄ 0x8000000000000004#64) ∗
     statesFromPbJumpTableAt b ∗
     (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      (protoChunkedEkSentCt1ReceivedAt A (pbA + 8#64) s ∗
       memRegion (pbA + 152#64) 72) ∗
      A.pool)) by rw [htag_eq]; ac_rfl))
    (sepConj_mono_left hfsp)) ?_
  refine sepWPp_seq_clean
    (states_from_pb_dispatch_tagged s0 s1 out pbA 0x8000000000000004#64 248#64
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 2304 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       (protoChunkedEkSentCt1ReceivedAt A (pbA + 8#64) s ∗
        memRegion (pbA + 152#64) 72) ∗
       A.pool)
      TaggedVariantDispatch.ekSentCt1Received hb_align hpc1 hrun1 hsp1 hx8_1 hx0_1 htr1 |>
      SepWP.weaken_pre (Entails.of_eq (by ac_rfl))) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx27_2, _, _, _, hx13_2, _, htr2⟩
  have hx13_2' : s2.readReg64 .x13 = (s0.sp - 2400#64) + 1264#64 := by
    rw [hx13_2]; bv_omega
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    optProtoInnerStateAt A pbA (some (.ekSentCt1Received s)) ∗
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
    memRegion (s0.sp - 2400#64) 2304 ∗
    statesFromPbSavedCells s0 ∗
    memRegion out chunkedStatesSize ∗
    statesFromPbJumpTableAt b ∗
    A.pool by rw [htag_eq]; ac_rfl)) ?_
  exact sfpProof_sepWPp_of_states_body s0 s2 out pbA { innerState := some (.ekSentCt1Received s) } _ R
    (states_from_pb_ekSentCt1Received_248 hA hdec s s0 s2 out pbA R
      hsp0_align hpc2 hrun2 hsp2 hx13_2' hx19_2 hx27_2 htr2)

/-- Variant 5 (`InnerState.noHeaderReceived`, `+1344`) of `<States>::from_pb`. -/
theorem states_from_pb_noHeaderReceived_ok_ext
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (hdec : DecoderFromPbOkExt b A ext)
    (s : V1State.Chunked.NoHeaderReceived) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName)
      (statesFromPbVariantSpec A F b { innerState := some (.noHeaderReceived s) }) :=
  sfpProof_tagged_ok_of_step TaggedVariantDispatch.noHeaderReceived
    (Tail := fun pbA => protoChunkedNoHeaderReceivedAt A (pbA + 8#64) s ∗ memRegion (pbA + 104#64) 120)
    (fun _ => rfl)
    (fun _ => states_from_pb_noHeaderReceived_1344 hA hdec s)

/-- Variant 6 (`InnerState.headerReceived`, `+1464`) of `<States>::from_pb`. -/
theorem states_from_pb_headerReceived_ok_ext
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (hdec : DecoderFromPbOkExt b A ext)
    (s : V1State.Chunked.HeaderReceived) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName)
      (statesFromPbVariantSpec A F b { innerState := some (.headerReceived s) }) :=
  sfpProof_tagged_ok_of_step TaggedVariantDispatch.headerReceived
    (Tail := fun pbA => protoChunkedHeaderReceivedAt A (pbA + 8#64) s ∗ memRegion (pbA + 128#64) 96)
    (fun _ => rfl)
    (fun _ => states_from_pb_headerReceived_1464 hA hdec s)

/-- Variant 8 (`InnerState.ekReceivedCt1Sampled`, `+1764`) of `<States>::from_pb`. -/
theorem states_from_pb_ekReceivedCt1Sampled_ok_ext
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (henc : EncoderFromPbOkExt b A ext)
    (s : V1State.Chunked.EkReceivedCt1Sampled) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName)
      (statesFromPbVariantSpec A F b { innerState := some (.ekReceivedCt1Sampled s) }) :=
  sfpProof_tagged_ok_of_step TaggedVariantDispatch.ekReceivedCt1Sampled
    (Tail := fun pbA => protoChunkedEkReceivedCt1SampledAt A (pbA + 8#64) s ∗ memRegion (pbA + 192#64) 32)
    (fun _ => rfl)
    (states_from_pb_ekReceivedCt1Sampled_1764 hA henc s)

/-- Variant 10 (`InnerState.ct2Sampled`, `+1632`) of `<States>::from_pb`. -/
theorem states_from_pb_ct2Sampled_ok_ext
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (henc : EncoderFromPbOkExt b A ext)
    (s : V1State.Chunked.Ct2Sampled) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName)
      (statesFromPbVariantSpec A F b { innerState := some (.ct2Sampled s) }) :=
  sfpProof_tagged_ok_of_step TaggedVariantDispatch.ct2Sampled
    (Tail := fun pbA => protoChunkedCt2SampledAt A (pbA + 8#64) s ∗ memRegion (pbA + 120#64) 104)
    (fun _ => rfl)
    (fun hpts s0 s1 out pbA R hsp0_align hpc1 hrun1 hsp1 hx19_1 _hx23_1 hx27_1 htr1 =>
      states_from_pb_ct2Sampled_1632 hA henc s0 s1 out pbA s R hpts
        hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1)

/-! ## 2. Unconditional Top-Level `<States>::from_pb` Theorems -/

/-- Per-variant `subroutine_ok` for `<States>::from_pb` across all 12 `Option V1State.InnerState`
    branches, proven unconditionally from `AllocContracts b A ext`. -/
theorem states_from_pb_branch_proof
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (pb : V1State) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName)
      (statesFromPbVariantSpec A F b pb) := by
  have henc : EncoderFromPbOkExt b A ext := encoder_from_pb_ok_ext hA
  have hdec : DecoderFromPbOkExt b A ext := decoder_from_pb_ok_ext hA
  rcases pb with ⟨inner⟩
  cases inner with
  | none => exact states_from_pb_none_ok_ext (b := b) (A := A) (F := F) (ext := ext)
  | some st =>
    cases st with
    | keysUnsampled s => exact states_from_pb_keysUnsampled_ok_ext hA s
    | keysSampled s => exact states_from_pb_keysSampled_ok_ext hA henc s
    | headerSent s => exact states_from_pb_headerSent_ok_ext hA henc hdec s
    | ct1Received s => exact states_from_pb_ct1Received_ok_ext hA henc s
    | ekSentCt1Received s => exact states_from_pb_ekSentCt1Received_ok_ext hA hdec s
    | noHeaderReceived s => exact states_from_pb_noHeaderReceived_ok_ext hA hdec s
    | headerReceived s => exact states_from_pb_headerReceived_ok_ext hA hdec s
    | ct1Sampled s => exact states_from_pb_ct1Sampled_ok_ext hA henc hdec s
    | ekReceivedCt1Sampled s => exact states_from_pb_ekReceivedCt1Sampled_ok_ext hA henc s
    | ct1Acknowledged s => exact states_from_pb_ct1Acknowledged_ok_ext hA hdec s
    | ct2Sampled s => exact states_from_pb_ct2Sampled_ok_ext hA henc s

/-- `<States>::from_pb` (`0x5a0a4`) satisfies `StatesFromPbOkExt b A F ext` unconditionally
    from `AllocContracts b A ext`. -/
theorem states_from_pb_ok_ext
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    StatesFromPbOkExt b A F ext :=
  states_from_pb_ok_of_forall_pb (states_from_pb_branch_proof hA)

theorem states_from_pb_ok
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    StatesFromPbOkExt b A F ext :=
  states_from_pb_ok_ext hA

/-- `<States>::from_pb` (`0x5a0a4`) satisfies `StatesFromPbOkX img A F ext` unconditionally
    from `AllocContracts img.base A ext`. -/
theorem states_from_pb_ok_x
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext) :
    StatesFromPbOkX img A F ext :=
  states_from_pb_okX_of_ok_ext (states_from_pb_ok_ext hA)

end CryptoVerification.SpqrV1.States.FromPb
