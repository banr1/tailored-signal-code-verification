/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5Placed
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2Placed
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3Placed
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cPlaced
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4dPlaced
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cPlaced
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5ePlaced

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`): Top-Level Relocatable Proof

Combines all 11 arms of `<spqr::v1::chunked::states::States>::into_pb` (Block `334`,
615 instructions, 2,460 bytes) under `[LibsignalPlacement]` to prove per-variant, raw,
`withLsCodeLoaded`, and `withLsCodeRoLoaded` top-level contracts.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.IntoPb

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.IntoPb.Placed

set_option maxRecDepth 200000
attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff

/-- Per-variant correctness of `<spqr::v1::chunked::states::States>::into_pb` (Block `334`)
    across all 11 `States` constructors under `[LibsignalPlacement]`. -/
theorem states_into_pb_variant_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlaced A ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec A))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec A))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec)
    (st : States spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpec A F st) := by
  cases st with
  | keysUnsampled s => exact states_into_pb_keysUnsampled_placed s
  | keysSampled s => exact states_into_pb_keysSampled_placed henc_raw s
  | headerSent s => exact states_into_pb_headerSent_placed henc_raw hdec_raw hmemcpy_raw s
  | ct1Received s => exact states_into_pb_ct1Received_placed henc_raw s
  | ekSentCt1Received s => exact states_into_pb_ekSentCt1Received_placed hdec_raw hmemcpy_raw s
  | noHeaderReceived s => exact states_into_pb_noHeaderReceived_placed hdec_raw hmemcpy_raw s
  | headerReceived s => exact states_into_pb_headerReceived_placed hdec_raw hmemcpy_raw s
  | ct1Sampled s => exact states_into_pb_ct1Sampled_placed hA henc_raw hdec_raw s
  | ekReceivedCt1Sampled s => exact states_into_pb_ekReceivedCt1Sampled_placed hA henc_raw s
  | ct1Acknowledged s => exact states_into_pb_ct1Acknowledged_placed hA hdec_raw hmemcpy_raw s
  | ct2Sampled s => exact states_into_pb_ct2Sampled_placed henc_raw s

/-- `<spqr::v1::chunked::states::States>::into_pb` (Block `334`, 615 instructions)
    satisfies `statesIntoPbPlacedSpec A F` on `(blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)`. -/
theorem states_into_pb_placed_raw [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlaced A ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec A))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec A))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbPlacedSpec A F) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  exact ((states_into_pb_variant_placed hA henc_raw hdec_raw hmemcpy_raw x.st).to_outcome
    ⟨x.out, x.stA⟩ R s0 hpc hrun hpre hal).mono_outcome (fun _ hout => hout)

/-- `<spqr::v1::chunked::states::States>::into_pb` (Block `334`, 615 instructions)
    satisfies `StatesIntoPbPlacedOkExt A F ext` (`withLsCodeLoaded lsmpl (statesIntoPbPlacedSpec A F)`). -/
theorem states_into_pb_placed_ok_ext [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlaced A ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec A))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec A))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec) :
    StatesIntoPbPlacedOkExt A F ext :=
  subroutine_ok_mono (states_into_pb_placed_raw hA henc_raw hdec_raw hmemcpy_raw)
    (fun _ _ _ hp => (extract_withLsCodeLoaded hp).2) (fun _ _ _ _ hq => hq)

/-- `<spqr::v1::chunked::states::States>::into_pb` (Block `334`, 615 instructions)
    satisfies `statesIntoPbPlacedRoSpecX A F` on `(blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)`. -/
theorem states_into_pb_placed_ro_ok_x [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlaced A ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec A))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec A))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbPlacedRoSpecX A F) :=
  statesIntoPbPlacedRoSpecX_of_statesIntoPbPlacedSpec
    (states_into_pb_placed_raw hA henc_raw hdec_raw hmemcpy_raw)

/-- `<spqr::v1::chunked::states::States>::into_pb` (Block `334`, 615 instructions)
    satisfies `StatesIntoPbPlacedOkX A F ext` (`withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecX A F)`). -/
theorem states_into_pb_placed_ok_x [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlaced A ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec A))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec A))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec) :
    StatesIntoPbPlacedOkX A F ext := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  obtain ⟨hfr, hpre⟩ := CryptoVerification.LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
  have hpre' : s0.mem ⊨ (statesIntoPbPlacedRoSpecX A F).pre x s0 ∗ R := by
    have hro := lsro_statesIntoPbJumpTablePlacedAt hfr.2 hpre
    dsimp only [statesIntoPbPlacedSpecX, statesIntoPbPlacedRoSpecX] at hro ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hro
  refine ((states_into_pb_placed_ro_ok_x hA henc_raw hdec_raw hmemcpy_raw).to_outcome
    x R s0 hpc hrun hpre' hal).mono_outcome (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      statesIntoPbPlacedSpecX, statesIntoPbPlacedRoSpecX] at hq ⊢
    have hq' : sf.mem ⊨ statesIntoPbJumpTablePlacedAt ∗
        ((⌜sf.trace = s0.trace⌝ ∗
          optProtoInnerStateAt A x.out x.st.into_pb.innerState ∗
          memRegion x.stA chunkedStatesSize ∗
          A.pool ∗ stackAt s0.sp statesIntoPbStackX) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hq
    exact Satisfies.of_sep_right hq'
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr hoom))

end CryptoVerification.SpqrV1.States.IntoPb
