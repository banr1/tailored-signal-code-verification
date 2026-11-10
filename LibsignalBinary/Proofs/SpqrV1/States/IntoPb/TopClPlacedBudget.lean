/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.NoHeaderReceivedClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3bClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4bClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4dClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5eClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`): Top-Level `withLsCodeLoaded` `RustCliAllocBudget` Proof

Defines `StatesIntoPbVariantExactEnv` / `StatesIntoPbExactEnv` with constructive non-vacuity
witnesses, and combines all 11 arms of `<spqr::v1::chunked::states::States>::into_pb` (Block `334`)
under `[LibsignalPlacement]` and `RustCliAllocBudget M` with `withLsCodeLoaded` /
`withLsCodeRoLoaded` contracts on `(blkPC_334).rebase` and `libsignalSessionLib.blockProgram lsmpl 334`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement libsignalSessionCode libsignalSessionLib
   lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (extract_withLsCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (States spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget
  (decoderIntoPbAllocEvents decoderIntoPbAllocEnv_imp_decoderIntoPbEnv decoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget
  (encoderIntoPbAllocEvents encoderIntoPbAllocEnv_imp_encoderIntoPbEnv encoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
  (StatesIntoPbAllocPlacedBudget statesIntoPbPlacedRoFreeSpecXOfEnv
   statesIntoPbPlacedRoFreeSpecXOfEnv_of_placedSpecXOfEnv
   statesIntoPbPlacedRoSpecXOfEnv statesIntoPbPlacedSpecOfEnv
   statesIntoPbPlacedSpecXOfEnv statesIntoPbVariantPlacedSpecOfEnv
   withLsCodeLoaded_statesIntoPbPlacedSpecXOfEnv_of_statesIntoPbPlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.NoHeaderReceivedClPlacedBudget
  (NoHeaderReceivedEnv states_into_pb_noHeaderReceived_of_env_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget (KeysUnsampledEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1PlacedBudget
  (states_into_pb_keysUnsampled_of_env_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2ClPlacedBudget
  (Ct2SampledEnv states_into_pb_ct2Sampled_of_env_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3ClPlacedBudget
  (KeysSampledEnv states_into_pb_keysSampled_of_env_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3bClPlacedBudget
  (Ct1ReceivedEnv states_into_pb_ct1Received_of_env_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4bClPlacedBudget
  (HeaderReceivedEnv states_into_pb_headerReceived_of_env_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cClPlacedBudget
  (EkSentCt1ReceivedEnv states_into_pb_ekSentCt1Received_of_env_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4dClPlacedBudget
  (HeaderSentEnv headerSentEnv_of_parts states_into_pb_headerSent_of_env_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5PlacedBudget
  (sessionMemcpyRegion_ok_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aClPlacedBudget
  (EkReceivedCt1SampledEnv ekReceivedCt1SampledEnv_of_parts
   states_into_pb_ekReceivedCt1Sampled_of_env_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget (ct1CloneEvents)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cClPlacedBudget
  (Ct1AcknowledgedEnv states_into_pb_ct1Acknowledged_of_env_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5eClPlacedBudget
  (Ct1SampledEnv ct1SampledEnv_of_parts states_into_pb_ct1Sampled_of_env_cl_placed)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff

/-! ## 1. Exact Per-Variant Event Envelope & Non-Vacuity Witnesses -/

/-- Exact binary allocation event envelope for `<spqr::v1::chunked::states::States>::into_pb`
    (Block `334`), dispatching to the tight arm envelope of each of the 11 `States` variants. -/
def StatesIntoPbVariantExactEnv {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) : List AllocEvent → Prop :=
  match st with
  | .keysUnsampled _ => KeysUnsampledEnv
  | .keysSampled s => KeysSampledEnv s
  | .headerSent s => HeaderSentEnv s
  | .ct1Received s => Ct1ReceivedEnv s
  | .ekSentCt1Received s => EkSentCt1ReceivedEnv s
  | .noHeaderReceived s => NoHeaderReceivedEnv s
  | .headerReceived s => HeaderReceivedEnv s
  | .ct1Sampled s => Ct1SampledEnv s
  | .ekReceivedCt1Sampled s => EkReceivedCt1SampledEnv s
  | .ct1Acknowledged s => Ct1AcknowledgedEnv s
  | .ct2Sampled s => Ct2SampledEnv s

/-- Exact ghost-indexed allocation event envelope for `<States>::into_pb` (Block `334`). -/
def StatesIntoPbExactEnv {F : ShaCompress}
    (x : StatesIntoPbGhost F) : List AllocEvent → Prop :=
  StatesIntoPbVariantExactEnv x.st

/-- Constructive non-vacuity witness for `StatesIntoPbVariantExactEnv` on every `States` variant. -/
theorem statesIntoPbVariantExactEnv_nonempty {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) :
    ∃ evs : List AllocEvent, StatesIntoPbVariantExactEnv st evs := by
  cases st with
  | keysUnsampled _ =>
    exact ⟨[], rfl⟩
  | keysSampled s =>
    exact ⟨encoderIntoPbAllocEvents s.sending_hdr,
      encoderIntoPbAllocEnv_imp_encoderIntoPbEnv rfl⟩
  | headerSent s =>
    exact ⟨encoderIntoPbAllocEvents s.sending_ek ++ decoderIntoPbAllocEvents s.receiving_ct1,
      headerSentEnv_of_parts
        (encoderIntoPbAllocEnv_imp_encoderIntoPbEnv rfl)
        (decoderIntoPbAllocEnv_imp_decoderIntoPbEnv rfl)⟩
  | ct1Received s =>
    exact ⟨encoderIntoPbAllocEvents s.sending_ek,
      encoderIntoPbAllocEnv_imp_encoderIntoPbEnv rfl⟩
  | ekSentCt1Received s =>
    exact ⟨decoderIntoPbAllocEvents s.receiving_ct2,
      decoderIntoPbAllocEnv_imp_decoderIntoPbEnv rfl⟩
  | noHeaderReceived s =>
    exact ⟨decoderIntoPbAllocEvents s.receiving_hdr,
      decoderIntoPbAllocEnv_imp_decoderIntoPbEnv rfl⟩
  | headerReceived s =>
    exact ⟨decoderIntoPbAllocEvents s.receiving_ek,
      decoderIntoPbAllocEnv_imp_decoderIntoPbEnv rfl⟩
  | ct1Sampled s =>
    exact ⟨(ct1CloneEvents s.uc.ct1 ++ []) ++
        (encoderIntoPbAllocEvents s.sending_ct1 ++ decoderIntoPbAllocEvents s.receiving_ek),
      ct1SampledEnv_of_parts
        (SeqEnv.append rfl FreeOnlyEvs.nil)
        (encoderIntoPbAllocEnv_imp_encoderIntoPbEnv rfl)
        (decoderIntoPbAllocEnv_imp_decoderIntoPbEnv rfl)⟩
  | ekReceivedCt1Sampled s =>
    exact ⟨(ct1CloneEvents s.uc.ct1 ++ []) ++ encoderIntoPbAllocEvents s.sending_ct1,
      ekReceivedCt1SampledEnv_of_parts
        (SeqEnv.append rfl FreeOnlyEvs.nil)
        (encoderIntoPbAllocEnv_imp_encoderIntoPbEnv rfl)⟩
  | ct1Acknowledged s =>
    exact ⟨(ct1CloneEvents s.uc.ct1 ++ []) ++ decoderIntoPbAllocEvents s.receiving_ek,
      ⟨[], decoderIntoPbAllocEvents s.receiving_ek, rfl, FreeOnlyEvs.nil,
        decoderIntoPbAllocEnv_imp_decoderIntoPbEnv rfl⟩⟩
  | ct2Sampled s =>
    exact ⟨encoderIntoPbAllocEvents s.sending_ct2,
      encoderIntoPbAllocEnv_imp_encoderIntoPbEnv rfl⟩

/-- Constructive non-vacuity witness for `StatesIntoPbExactEnv`. -/
theorem statesIntoPbExactEnv_nonempty {F : ShaCompress} (x : StatesIntoPbGhost F) :
    ∃ evs : List AllocEvent, StatesIntoPbExactEnv x evs :=
  statesIntoPbVariantExactEnv_nonempty x.st

abbrev statesIntoPbVariantExactPlacedSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (st : States spqrPolyApi (spqrAuthApi F)) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) :=
  statesIntoPbVariantPlacedSpecOfEnv M A lim F st (StatesIntoPbVariantExactEnv st)

abbrev statesIntoPbExactPlacedSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (StatesIntoPbGhost F × M.σ) :=
  statesIntoPbPlacedSpecOfEnv M A lim F StatesIntoPbExactEnv

/-- Tight extended-stack relocatable budget specification of `<States>::into_pb` (Block `334`)
    with explicit `statesIntoPbJumpTablePlacedAt`. -/
abbrev statesIntoPbExactPlacedRoSpecX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (StatesIntoPbGhost F × M.σ) :=
  statesIntoPbPlacedRoSpecXOfEnv M A lim F StatesIntoPbExactEnv

/-- Tight `.rodata`-free extended-stack relocatable budget specification of `<States>::into_pb`
    (Block `334`). -/
abbrev statesIntoPbExactPlacedRoFreeSpecX (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (StatesIntoPbGhost F × M.σ) :=
  statesIntoPbPlacedRoFreeSpecXOfEnv M A lim F StatesIntoPbExactEnv

/-- `<States>::into_pb` (Block `334`) meets `withLsCodeLoaded lsmpl` of
    `statesIntoPbPlacedSpecOfEnv M A lim F Env` on `(blkPC_334).rebase`. -/
def StatesIntoPbPlacedOkExtOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : StatesIntoPbGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
    (blkPl_334).base
    (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecOfEnv M A lim F Env))

/-- `<States>::into_pb` (Block `334`) meets `withLsCodeRoLoaded lsmpl` of
    `statesIntoPbPlacedRoFreeSpecXOfEnv M A lim F Env` on `(blkPC_334).rebase`. -/
def StatesIntoPbPlacedRoFreeOkXOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : StatesIntoPbGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
    (blkPl_334).base
    (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedRoFreeSpecXOfEnv M A lim F Env))

/-- `<States>::into_pb` (Block `334`) meets `withLsCodeLoaded lsmpl` of
    `statesIntoPbPlacedSpecXOfEnv M A lim F Env` on `libsignalSessionLib.blockProgram lsmpl 334`. -/
def StatesIntoPbPlacedOkXOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : StatesIntoPbGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 334 (Rust.withPanics ext))
    (lsmpl.base 334)
    (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv M A lim F Env))

/-! ## 2. Per-Variant `withLsCodeLoaded` Dispatch Across All 11 `States` Constructors -/

/-- Envelope-parametric per-variant correctness of `<spqr::v1::chunked::states::States>::into_pb`
    (Block `334`) across all 11 `States` constructors with `withLsCodeLoaded` cross-block
    contracts (`375` and `377`). -/
theorem states_into_pb_variant_of_env_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (st : States spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, StatesIntoPbVariantExactEnv st evs → Env evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpecOfEnv M A lim F st Env)) := by
  cases st with
  | keysUnsampled s =>
    exact states_into_pb_keysUnsampled_of_env_cl_placed s (hEnv [] rfl)
  | keysSampled s =>
    exact states_into_pb_keysSampled_of_env_cl_placed henc_cl s hEnv
  | headerSent s =>
    exact states_into_pb_headerSent_of_env_cl_placed henc_cl hdec_cl hmemcpy_raw s hEnv
  | ct1Received s =>
    exact states_into_pb_ct1Received_of_env_cl_placed henc_cl s hEnv
  | ekSentCt1Received s =>
    exact states_into_pb_ekSentCt1Received_of_env_cl_placed hdec_cl hmemcpy_raw s hEnv
  | noHeaderReceived s =>
    exact states_into_pb_noHeaderReceived_of_env_cl_placed hdec_cl hmemcpy_raw s hEnv
  | headerReceived s =>
    exact states_into_pb_headerReceived_of_env_cl_placed hdec_cl hmemcpy_raw s hEnv
  | ct1Sampled s =>
    exact states_into_pb_ct1Sampled_of_env_cl_placed hA henc_cl hdec_cl s hEnv
  | ekReceivedCt1Sampled s =>
    exact states_into_pb_ekReceivedCt1Sampled_of_env_cl_placed hA henc_cl s hEnv
  | ct1Acknowledged s =>
    exact states_into_pb_ct1Acknowledged_of_env_cl_placed hA hdec_cl hmemcpy_raw s hEnv
  | ct2Sampled s =>
    exact states_into_pb_ct2Sampled_of_env_cl_placed henc_cl s hEnv

theorem states_into_pb_variant_of_env_of_alloc_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (st : States spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, StatesIntoPbVariantExactEnv st evs → Env evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpecOfEnv M A lim F st Env)) :=
  states_into_pb_variant_of_env_cl_placed hA henc_cl hdec_cl (sessionMemcpyRegion_ok_placed hA)
    st hEnv

/-- Tight per-variant correctness of `<spqr::v1::chunked::states::States>::into_pb` (Block `334`)
    across all 11 `States` constructors under `StatesIntoPbVariantExactEnv`. -/
theorem states_into_pb_variant_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (st : States spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl (statesIntoPbVariantExactPlacedSpec M A lim F st)) :=
  states_into_pb_variant_of_env_cl_placed hA henc_cl hdec_cl hmemcpy_raw st (fun _ h => h)

theorem states_into_pb_variant_of_alloc_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (st : States spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl (statesIntoPbVariantExactPlacedSpec M A lim F st)) :=
  states_into_pb_variant_cl_placed hA henc_cl hdec_cl (sessionMemcpyRegion_ok_placed hA) st

/-! ## 3. Ghost-Indexed, Extended-Stack, and `withLsCodeRoLoaded` Top-Level Contracts -/

/-- Envelope-parametric `StatesIntoPbPlacedOkExtOfEnv` for `<States>::into_pb` (Block `334`). -/
theorem states_into_pb_cl_placed_ok_ext_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (hEnv : ∀ x evs, StatesIntoPbExactEnv x evs → Env x evs) :
    StatesIntoPbPlacedOkExtOfEnv M A lim F Env ext := by
  apply subroutine_ok_outcome_intro
  intro ⟨x, st⟩ R s0 hpc hrun hpre hal
  exact ((states_into_pb_variant_of_env_cl_placed hA henc_cl hdec_cl hmemcpy_raw x.st
    (hEnv x)).to_outcome (⟨x.out, x.stA⟩, st) R s0 hpc hrun hpre hal).mono_outcome
    (fun _ hout => hout)

theorem states_into_pb_cl_placed_ok_ext_of_env_of_alloc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (hEnv : ∀ x evs, StatesIntoPbExactEnv x evs → Env x evs) :
    StatesIntoPbPlacedOkExtOfEnv M A lim F Env ext :=
  states_into_pb_cl_placed_ok_ext_of_env hA henc_cl hdec_cl (sessionMemcpyRegion_ok_placed hA) hEnv

/-- `<spqr::v1::chunked::states::States>::into_pb` (Block `334`, 615 instructions) satisfies
    `StatesIntoPbPlacedOkExtOfEnv M A lim F StatesIntoPbExactEnv ext`. -/
theorem states_into_pb_cl_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec) :
    StatesIntoPbPlacedOkExtOfEnv M A lim F StatesIntoPbExactEnv ext :=
  states_into_pb_cl_placed_ok_ext_of_env hA henc_cl hdec_cl hmemcpy_raw (fun _ _ h => h)

theorem states_into_pb_cl_placed_ok_ext_of_alloc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim))) :
    StatesIntoPbPlacedOkExtOfEnv M A lim F StatesIntoPbExactEnv ext :=
  states_into_pb_cl_placed_ok_ext hA henc_cl hdec_cl (sessionMemcpyRegion_ok_placed hA)

theorem statesIntoPbPlacedRoSpecX_cl_of_statesIntoPbPlacedSpecOfEnv [LibsignalPlacement]
    {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : StatesIntoPbGhost F → List AllocEvent → Prop}
    (h : subroutine_ok P addr (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecOfEnv M A lim F Env))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (statesIntoPbPlacedRoSpecXOfEnv M A lim F Env)) :=
  withLsCodeLoaded_statesIntoPbPlacedSpecXOfEnv_of_statesIntoPbPlacedSpecOfEnv h

/-- Envelope-parametric `<States>::into_pb` (Block `334`) contract on
    `withLsCodeLoaded lsmpl (statesIntoPbPlacedRoSpecXOfEnv M A lim F Env)`. -/
theorem states_into_pb_cl_placed_ro_ok_x_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (hEnv : ∀ x evs, StatesIntoPbExactEnv x evs → Env x evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl (statesIntoPbPlacedRoSpecXOfEnv M A lim F Env)) :=
  statesIntoPbPlacedRoSpecX_cl_of_statesIntoPbPlacedSpecOfEnv
    (states_into_pb_cl_placed_ok_ext_of_env hA henc_cl hdec_cl hmemcpy_raw hEnv)

/-- Tight `StatesIntoPbExactEnv` `<States>::into_pb` (Block `334`) contract on
    `withLsCodeLoaded lsmpl (statesIntoPbExactPlacedRoSpecX M A lim F)`. -/
theorem states_into_pb_cl_placed_ro_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl (statesIntoPbExactPlacedRoSpecX M A lim F)) :=
  states_into_pb_cl_placed_ro_ok_x_of_env hA henc_cl hdec_cl hmemcpy_raw (fun _ _ h => h)

theorem states_into_pb_cl_placed_ro_ok_x_of_alloc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim))) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl (statesIntoPbExactPlacedRoSpecX M A lim F)) :=
  states_into_pb_cl_placed_ro_ok_x hA henc_cl hdec_cl (sessionMemcpyRegion_ok_placed hA)

/-- Lift any `withLsCodeLoaded lsmpl (statesIntoPbPlacedRoSpecXOfEnv M A lim F Env)` contract to
    `withLsCodeRoLoaded lsmpl (statesIntoPbPlacedRoSpecXOfEnv M A lim F Env)`. -/
theorem withLsCodeRoLoaded_of_withLsCodeLoaded_statesIntoPbPlacedRoSpecXOfEnv [LibsignalPlacement]
    {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : StatesIntoPbGhost F → List AllocEvent → Prop}
    (h : subroutine_ok P addr (withLsCodeLoaded lsmpl (statesIntoPbPlacedRoSpecXOfEnv M A lim F Env))) :
    subroutine_ok P addr (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedRoSpecXOfEnv M A lim F Env)) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => ?_) (fun _ _ _ _ hq => hq)
  obtain ⟨hfr, hpre⟩ := extract_withLsCodeRoLoaded hp
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hfr.1, hpre⟩

/-- Envelope-parametric `<States>::into_pb` (Block `334`) contract on
    `withLsCodeRoLoaded lsmpl (statesIntoPbPlacedRoSpecXOfEnv M A lim F Env)`. -/
theorem states_into_pb_cl_placed_ro_cro_ok_x_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (hEnv : ∀ x evs, StatesIntoPbExactEnv x evs → Env x evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedRoSpecXOfEnv M A lim F Env)) :=
  withLsCodeRoLoaded_of_withLsCodeLoaded_statesIntoPbPlacedRoSpecXOfEnv
    (states_into_pb_cl_placed_ro_ok_x_of_env hA henc_cl hdec_cl hmemcpy_raw hEnv)

/-- Tight `StatesIntoPbExactEnv` `<States>::into_pb` (Block `334`) contract on
    `withLsCodeRoLoaded lsmpl (statesIntoPbExactPlacedRoSpecX M A lim F)`. -/
theorem states_into_pb_cl_placed_ro_cro_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeRoLoaded lsmpl (statesIntoPbExactPlacedRoSpecX M A lim F)) :=
  states_into_pb_cl_placed_ro_cro_ok_x_of_env hA henc_cl hdec_cl hmemcpy_raw (fun _ _ h => h)

theorem states_into_pb_cl_placed_ro_cro_ok_x_of_alloc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim))) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeRoLoaded lsmpl (statesIntoPbExactPlacedRoSpecX M A lim F)) :=
  states_into_pb_cl_placed_ro_cro_ok_x hA henc_cl hdec_cl (sessionMemcpyRegion_ok_placed hA)

/-- Envelope-parametric `.rodata`-free `<States>::into_pb` (Block `334`) contract on
    `withLsCodeRoLoaded lsmpl (statesIntoPbPlacedRoFreeSpecXOfEnv M A lim F Env)`. -/
theorem states_into_pb_cl_placed_ro_free_ok_x_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (hEnv : ∀ x evs, StatesIntoPbExactEnv x evs → Env x evs) :
    StatesIntoPbPlacedRoFreeOkXOfEnv M A lim F Env ext :=
  statesIntoPbPlacedRoFreeSpecXOfEnv_of_placedSpecXOfEnv
    (states_into_pb_cl_placed_ro_ok_x_of_env hA henc_cl hdec_cl hmemcpy_raw hEnv)

theorem states_into_pb_cl_placed_ok_x_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (hEnv : ∀ x evs, StatesIntoPbExactEnv x evs → Env x evs) :
    StatesIntoPbPlacedRoFreeOkXOfEnv M A lim F Env ext :=
  states_into_pb_cl_placed_ro_free_ok_x_of_env hA henc_cl hdec_cl hmemcpy_raw hEnv

/-- `<States>::into_pb` (Block `334`) satisfies
    `StatesIntoPbPlacedRoFreeOkXOfEnv M A lim F StatesIntoPbExactEnv ext`
    (`withLsCodeRoLoaded lsmpl (statesIntoPbExactPlacedRoFreeSpecX M A lim F)`). -/
theorem states_into_pb_cl_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec) :
    StatesIntoPbPlacedRoFreeOkXOfEnv M A lim F StatesIntoPbExactEnv ext :=
  states_into_pb_cl_placed_ro_free_ok_x_of_env hA henc_cl hdec_cl hmemcpy_raw (fun _ _ h => h)

theorem states_into_pb_cl_placed_ok_x_of_alloc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim))) :
    StatesIntoPbPlacedRoFreeOkXOfEnv M A lim F StatesIntoPbExactEnv ext :=
  states_into_pb_cl_placed_ok_x hA henc_cl hdec_cl (sessionMemcpyRegion_ok_placed hA)

/-! ## 4. `libsignalSessionLib.blockProgram lsmpl 334` Lifts -/

/-- Envelope-parametric `StatesIntoPbPlacedOkXOfEnv` on `libsignalSessionLib.blockProgram lsmpl 334`. -/
theorem states_into_pb_cl_placed_blockProgram_ok_x_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (hEnv : ∀ x evs, StatesIntoPbExactEnv x evs → Env x evs) :
    StatesIntoPbPlacedOkXOfEnv M A lim F Env ext := by
  have h1 := states_into_pb_cl_placed_ro_ok_x_of_env hA henc_cl hdec_cl hmemcpy_raw hEnv
  have hprog : (blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext) =
      libsignalSessionLib.blockProgram lsmpl 334 (Rust.withPanics ext) :=
    (inferInstance : IsLsBlockProg
      ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      334 (Rust.withPanics ext)).eq_blockProgram
  have hbase : (blkPl_334).base = lsmpl.base 334 := rfl
  rw [hprog, hbase] at h1
  exact h1

/-- Tight `StatesIntoPbExactEnv` `StatesIntoPbPlacedOkXOfEnv` on
    `libsignalSessionLib.blockProgram lsmpl 334`, projecting `memcpy` from `hA`. -/
theorem states_into_pb_cl_placed_blockProgram_ok_x_of_alloc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim))) :
    StatesIntoPbPlacedOkXOfEnv M A lim F StatesIntoPbExactEnv ext :=
  states_into_pb_cl_placed_blockProgram_ok_x_of_env hA henc_cl hdec_cl
    (sessionMemcpyRegion_ok_placed hA) (fun _ _ h => h)

/-- Envelope-parametric `withLsCodeRoLoaded` contract on `libsignalSessionLib.blockProgram lsmpl 334`
    matching `SpqrRecvPlacedContractsOfEnv.statesIntoPb_ok`'s callee specification. -/
theorem states_into_pb_cl_placed_blockProgram_ro_cro_ok_x_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (hEnv : ∀ x evs, StatesIntoPbExactEnv x evs → Env x evs) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 334 (Rust.withPanics ext))
      (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv M A lim F Env)) :=
  withLsCodeRoLoaded_of_withLsCodeLoaded_statesIntoPbPlacedRoSpecXOfEnv
    (states_into_pb_cl_placed_blockProgram_ok_x_of_env hA henc_cl hdec_cl hmemcpy_raw hEnv)

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget
