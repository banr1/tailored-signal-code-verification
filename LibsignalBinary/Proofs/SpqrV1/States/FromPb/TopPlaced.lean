/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DecoderFromPbClPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EncoderFromPbProofClPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.ProofPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10dPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4ePlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9Placed

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Closed Relocatable Top-Level Proof (Block `333`)

Discharges `<PolyEncoder>::from_pb` (Block `374`), `<PolyDecoder>::from_pb` (Block `376`), and all
12 `Option V1State.InnerState` branches on Block `333` (`2,911` instructions) to prove
`StatesFromPbPlacedOkExt` and `StatesFromPbPlacedOkX` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.FromPb

/-! ## 1. Closed `<PolyEncoder>::from_pb`, `<PolyDecoder>::from_pb`, and `.rodata` Helpers -/

theorem encoder_from_pb_ok_of_alloc_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : FromPbAllocHooks A ext) :
    Variant2aPlaced.EncoderFromPbPlacedOkExt A ext :=
  encoder_from_pb_on_333_placed_ok_ext hA.panic_ok hA.shim hA.alloc hA.dealloc hA.memcpy

theorem decoder_from_pb_ok_of_alloc_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : FromPbAllocHooks A ext)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec 0)) :
    DecoderFromPbPlacedOkExt A ext :=
  decoder_from_pb_on_333_placed_ok_ext hA.alloc hA.shim hA.dealloc hA.memcpy hmemmove hA.panic_ok

/-- Extract `statesFromPbJumpTablePlacedAt` (`22` bytes) from `LibsignalRoLoaded lsmpl m`. -/
theorem rodata_statesFromPbJumpTable_placed [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ statesFromPbJumpTablePlacedAt ∗ P :=
  rodata_statesFromPbJumpTablePlacedAt hro hP

/-! ## 2. Per-Variant `subroutine_ok` Wrappers via `sfpProof_tagged_ok_of_step_placed` -/

/-- Variant 1 (`InnerState.keysSampled`, `+1104`) of `<States>::from_pb`. -/
theorem states_from_pb_keysSampled_ok_ext_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (henc : Variant2aPlaced.EncoderFromPbPlacedOkExt A ext)
    (s : V1State.Chunked.KeysSampled) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (statesFromPbVariantPlacedSpec A F { innerState := some (.keysSampled s) })) :=
  sfpProof_tagged_ok_of_step_placed TaggedVariantDispatch.keysSampled
    (Tail := fun pbA => protoChunkedKeysSampledAt A (pbA + 8#64) s ∗ memRegion (pbA + 168#64) 56)
    (fun _ => rfl)
    (fun hpts s0 s1 out pbA R hcl1 =>
      states_from_pb_keysSampled_1104_placed (F := F) hA henc s hpts s0 s1 hcl1 out pbA R)

/-- Variant 5 (`InnerState.noHeaderReceived`, `+1344`) of `<States>::from_pb`. -/
theorem states_from_pb_noHeaderReceived_ok_ext_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (hdec : DecoderFromPbPlacedOkExt A ext)
    (s : V1State.Chunked.NoHeaderReceived) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (statesFromPbVariantPlacedSpec A F { innerState := some (.noHeaderReceived s) })) :=
  sfpProof_tagged_ok_of_step_placed TaggedVariantDispatch.noHeaderReceived
    (Tail := fun pbA => protoChunkedNoHeaderReceivedAt A (pbA + 8#64) s ∗ memRegion (pbA + 104#64) 120)
    (fun _ => rfl)
    (fun _ s0 s1 out pbA R hcl1 =>
      states_from_pb_noHeaderReceived_1344_placed (F := F) hA hdec s s0 s1 hcl1 out pbA R)

/-- Variant 6 (`InnerState.headerReceived`, `+1464`) of `<States>::from_pb`. -/
theorem states_from_pb_headerReceived_ok_ext_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (hdec : DecoderFromPbPlacedOkExt A ext)
    (s : V1State.Chunked.HeaderReceived) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (statesFromPbVariantPlacedSpec A F { innerState := some (.headerReceived s) })) :=
  sfpProof_tagged_ok_of_step_placed TaggedVariantDispatch.headerReceived
    (Tail := fun pbA => protoChunkedHeaderReceivedAt A (pbA + 8#64) s ∗ memRegion (pbA + 128#64) 96)
    (fun _ => rfl)
    (fun _ s0 s1 out pbA R hcl1 =>
      states_from_pb_headerReceived_1464_placed (F := F) hA hdec s s0 s1 hcl1 out pbA R)

/-- Variant 8 (`InnerState.ekReceivedCt1Sampled`, `+1764`) of `<States>::from_pb`. -/
theorem states_from_pb_ekReceivedCt1Sampled_ok_ext_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (henc : Variant2aPlaced.EncoderFromPbPlacedOkExt A ext)
    (s : V1State.Chunked.EkReceivedCt1Sampled) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (statesFromPbVariantPlacedSpec A F { innerState := some (.ekReceivedCt1Sampled s) })) :=
  sfpProof_tagged_ok_of_step_placed TaggedVariantDispatch.ekReceivedCt1Sampled
    (Tail := fun pbA => protoChunkedEkReceivedCt1SampledAt A (pbA + 8#64) s ∗ memRegion (pbA + 192#64) 32)
    (fun _ => rfl)
    (fun hpts s0 s1 out pbA R hcl1 =>
      states_from_pb_ekReceivedCt1Sampled_1764_placed (F := F) hA henc s hpts s0 s1 hcl1 out pbA R)

/-! ## 3. Unconditional Top-Level `<States>::from_pb` Theorems (`[LibsignalPlacement]`) -/

/-- Per-variant `subroutine_ok` for `<States>::from_pb` across all 12 `Option V1State.InnerState`
    branches under `[LibsignalPlacement]`, proven unconditionally from `FromPbAllocHooks A ext`
    and `HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec 0)`. -/
theorem states_from_pb_branch_proof_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec 0))
    (pb : V1State) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpec A F pb)) := by
  have henc : Variant2aPlaced.EncoderFromPbPlacedOkExt A ext := encoder_from_pb_ok_of_alloc_placed hA
  have hdec : DecoderFromPbPlacedOkExt A ext := decoder_from_pb_ok_of_alloc_placed hA hmemmove
  rcases pb with ⟨inner⟩
  cases inner with
  | none => exact states_from_pb_none_placed_ok_ext (A := A) (F := F) (ext := ext)
  | some st =>
    cases st with
    | keysUnsampled s => exact states_from_pb_keysUnsampled_ok_ext_placed hA s
    | keysSampled s => exact states_from_pb_keysSampled_ok_ext_placed hA henc s
    | headerSent s => exact states_from_pb_headerSent_ok_ext_placed hA henc hdec s
    | ct1Received s => exact states_from_pb_ct1Received_ok_ext_placed hA henc s
    | ekSentCt1Received s => exact states_from_pb_ekSentCt1Received_ok_ext_placed hA hdec s
    | noHeaderReceived s => exact states_from_pb_noHeaderReceived_ok_ext_placed hA hdec s
    | headerReceived s => exact states_from_pb_headerReceived_ok_ext_placed hA hdec s
    | ct1Sampled s => exact states_from_pb_ct1Sampled_ok_ext_placed hA henc hdec s
    | ekReceivedCt1Sampled s => exact states_from_pb_ekReceivedCt1Sampled_ok_ext_placed hA henc s
    | ct1Acknowledged s => exact states_from_pb_ct1Acknowledged_ok_ext_placed hA hdec s
    | ct2Sampled s => exact states_from_pb_ct2Sampled_ok_ext_placed hA henc s

/-- `<States>::from_pb` (Block `333`) satisfies `StatesFromPbPlacedOkExt A F ext` unconditionally
    from `FromPbAllocHooks A ext` and `hmemmove`. -/
theorem states_from_pb_ok_ext_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec 0)) :
    StatesFromPbPlacedOkExt A F ext :=
  states_from_pb_ok_of_forall_pb_placed (states_from_pb_branch_proof_placed hA hmemmove)

theorem states_from_pb_ok_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec 0)) :
    StatesFromPbPlacedOkExt A F ext :=
  states_from_pb_ok_ext_placed hA hmemmove

/-- `<States>::from_pb` (Block `333`) satisfies `StatesFromPbPlacedOkX A F ext` (`withLsCodeRoLoaded`)
    unconditionally from `FromPbAllocHooks A ext` and `hmemmove`. -/
theorem states_from_pb_ok_x_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec 0)) :
    StatesFromPbPlacedOkX A F ext :=
  states_from_pb_okX_of_ok_ext_placed (states_from_pb_ok_ext_placed hA hmemmove)

end LibsignalBinary.Proofs.SpqrV1.States.FromPb

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb (
  encoder_from_pb_ok_of_alloc_placed
  decoder_from_pb_ok_of_alloc_placed
  rodata_statesFromPbJumpTable_placed
  states_from_pb_keysSampled_ok_ext_placed
  states_from_pb_noHeaderReceived_ok_ext_placed
  states_from_pb_headerReceived_ok_ext_placed
  states_from_pb_ekReceivedCt1Sampled_ok_ext_placed
  states_from_pb_branch_proof_placed
  states_from_pb_ok_ext_placed
  states_from_pb_ok_placed
  states_from_pb_ok_x_placed
)

end CryptoVerification.SpqrV1.States.FromPb
