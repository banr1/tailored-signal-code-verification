/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5Placed
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1ClPlaced
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2ClPlaced
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3ClPlaced
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3bClPlaced
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.NoHeaderReceivedClPlaced
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4bClPlaced
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cClPlaced
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4dClPlaced
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aClPlaced
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cClPlaced
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5eClPlaced

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`): Top-Level `withLsCodeLoaded` Proof

Combines all 11 arms of `<spqr::v1::chunked::states::States>::into_pb` (Block `334`,
615 instructions) under `[LibsignalPlacement]` with `withLsCodeLoaded` cross-block callee
contracts (`375` and `377`), lifting to `statesIntoPbPlacedRoSpecX` and `withLsCodeRoLoaded`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.IntoPb

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
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
    across all 11 `States` constructors with `withLsCodeLoaded` cross-block contracts. -/
theorem states_into_pb_variant_cl_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlaced A ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec A)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec A)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec)
    (st : States spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpec A F st)) := by
  cases st with
  | keysUnsampled s => exact states_into_pb_keysUnsampled_cl_placed s
  | keysSampled s => exact states_into_pb_keysSampled_cl_placed henc_cl s
  | headerSent s => exact states_into_pb_headerSent_cl_placed henc_cl hdec_cl hmemcpy_raw s
  | ct1Received s => exact states_into_pb_ct1Received_cl_placed henc_cl s
  | ekSentCt1Received s => exact states_into_pb_ekSentCt1Received_cl_placed hdec_cl hmemcpy_raw s
  | noHeaderReceived s => exact states_into_pb_noHeaderReceived_cl_placed hdec_cl hmemcpy_raw s
  | headerReceived s => exact states_into_pb_headerReceived_cl_placed hdec_cl hmemcpy_raw s
  | ct1Sampled s => exact states_into_pb_ct1Sampled_cl_placed hA henc_cl hdec_cl s
  | ekReceivedCt1Sampled s => exact states_into_pb_ekReceivedCt1Sampled_cl_placed hA henc_cl s
  | ct1Acknowledged s => exact states_into_pb_ct1Acknowledged_cl_placed hA hdec_cl hmemcpy_raw s
  | ct2Sampled s => exact states_into_pb_ct2Sampled_cl_placed henc_cl s

/-- `<spqr::v1::chunked::states::States>::into_pb` (Block `334`, 615 instructions)
    satisfies `StatesIntoPbPlacedOkExt A F ext` (`withLsCodeLoaded lsmpl (statesIntoPbPlacedSpec A F)`). -/
theorem states_into_pb_cl_placed_ok_ext [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlaced A ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec A)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec A)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec) :
    StatesIntoPbPlacedOkExt A F ext := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  exact ((states_into_pb_variant_cl_placed hA henc_cl hdec_cl hmemcpy_raw x.st).to_outcome
    ⟨x.out, x.stA⟩ R s0 hpc hrun hpre hal).mono_outcome (fun _ hout => hout)

private theorem satisfies_anyHeap_frame_cl {m : Memory} {P Fr R : SepProp}
    (h : m ⊨ (P ∗ anyHeap) ∗ Fr ∗ R) :
    m ⊨ (P ∗ anyHeap) ∗ R := by
  have h1 : (P ∗ anyHeap) ∗ Fr ∗ R ⊢ (P ∗ anyHeap) ∗ R := by
    rw [sepConj_assoc P anyHeap (Fr ∗ R), ← sepConj_assoc anyHeap Fr R, sepConj_assoc P anyHeap R]
    exact sepConj_mono_right (sepConj_mono_left (entails_anyHeap (anyHeap ∗ Fr)))
  exact Satisfies.mono h1 h

/-- Frame the unused bottom stack region on `withLsCodeLoaded lsmpl (statesIntoPbPlacedSpec A F)`
    to obtain `withLsCodeLoaded lsmpl (statesIntoPbPlacedRoSpecX A F)`. -/
theorem statesIntoPbPlacedRoSpecX_cl_of_statesIntoPbPlacedSpec [LibsignalPlacement]
    {P : Program} {addr : BitVec 64} {A : RustAlloc} {F : ShaCompress}
    (h : subroutine_ok P addr (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpec A F))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (statesIntoPbPlacedRoSpecX A F)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  have hle : statesIntoPbStack ≤ statesIntoPbStackX := by decide
  have hsplit : stackAt s0.sp statesIntoPbStackX =
      memRegion (s0.sp - BitVec.ofNat 64 statesIntoPbStackX)
        (statesIntoPbStackX - statesIntoPbStack) ∗
        stackAt s0.sp statesIntoPbStack := by
    have h1 := stackAt_split_bottom s0.sp statesIntoPbStack
      (statesIntoPbStackX - statesIntoPbStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 statesIntoPbStackX)
      (statesIntoPbStackX - statesIntoPbStack) ∗ R
  have hpre0 : s0.mem ⊨ (statesIntoPbPlacedSpec A F).pre x s0 ∗ R' := by
    dsimp only [statesIntoPbPlacedRoSpecX, statesIntoPbPlacedSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpec A F)).pre x s0 ∗ R' := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl0, hpre0⟩
  refine h.mono_outcome x R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, statesIntoPbPlacedRoSpecX, statesIntoPbPlacedSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact Or.inr (Or.inl ⟨hpan, satisfies_anyHeap_frame_cl hpost⟩)
  · dsimp only [withLsCodeLoaded, statesIntoPbPlacedSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-- `<States>::into_pb` (Block `334`) satisfies `withLsCodeLoaded lsmpl (statesIntoPbPlacedRoSpecX A F)`. -/
theorem states_into_pb_cl_placed_ro_ok_x [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlaced A ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec A)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec A)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl (statesIntoPbPlacedRoSpecX A F)) :=
  statesIntoPbPlacedRoSpecX_cl_of_statesIntoPbPlacedSpec
    (states_into_pb_cl_placed_ok_ext hA henc_cl hdec_cl hmemcpy_raw)

/-- `<States>::into_pb` (Block `334`) satisfies `withLsCodeRoLoaded lsmpl (statesIntoPbPlacedRoSpecX A F)`. -/
theorem states_into_pb_cl_placed_ro_cro_ok_x [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlaced A ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec A)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec A)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (statesIntoPbPlacedRoSpecX A F)) := by
  refine subroutine_ok_mono (states_into_pb_cl_placed_ro_ok_x hA henc_cl hdec_cl hmemcpy_raw)
    (fun _ _ s0 hp => ?_) (fun _ _ _ _ hq => hq)
  obtain ⟨hfr, hpre⟩ := CryptoVerification.LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hp
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hfr.1, hpre⟩

/-- `<States>::into_pb` (Block `334`) satisfies `StatesIntoPbPlacedOkX A F ext`
    (`withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecX A F)`). -/
theorem states_into_pb_cl_placed_ok_x [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlaced A ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec A)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec A)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec) :
    StatesIntoPbPlacedOkX A F ext := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  obtain ⟨hfr, hpre⟩ := CryptoVerification.LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
  have hpre0 : s0.mem ⊨ (statesIntoPbPlacedRoSpecX A F).pre x s0 ∗ R := by
    have hro := lsro_statesIntoPbJumpTablePlacedAt hfr.2 hpre
    dsimp only [statesIntoPbPlacedSpecX, statesIntoPbPlacedRoSpecX] at hro ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hro
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (statesIntoPbPlacedRoSpecX A F)).pre x s0 ∗ R := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hfr.1, hpre0⟩
  refine ((states_into_pb_cl_placed_ro_ok_x hA henc_cl hdec_cl hmemcpy_raw).to_outcome
    x R s0 hpc hrun hpre' hal).mono_outcome (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      withLsCodeLoaded, statesIntoPbPlacedSpecX, statesIntoPbPlacedRoSpecX] at hq ⊢
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
