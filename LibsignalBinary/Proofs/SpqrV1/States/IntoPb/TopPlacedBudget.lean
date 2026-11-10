/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3bPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4bPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5ePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopPlaced

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`): Top-Level Relocatable `RustCliAllocBudget` Proof

Defines `StatesIntoPbExactVariantEnv` / `StatesIntoPbExactEnv` and `StatesIntoPbBounded` /
`StatesIntoPbWellSized` bounds bridges, and combines all 11 arms of
`<spqr::v1::chunked::states::States>::into_pb` (Block `334`, 615 instructions) under
`[LibsignalPlacement]` and `RustCliAllocBudget M` across raw, `withLsCodeLoaded`,
`withLsCodeRoLoaded`, and `libsignalSessionLib.blockProgram lsmpl 334` contracts.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement libsignalSessionLib lsmpl lsρ
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (States V1State spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (HeaderReceived NoHeaderReceived)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk
  (EkSentCt1Received HeaderSent KeysUnsampled)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget (decoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget
  (encoderIntoPbSpec encoderIntoPbVecs)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
  (SpqrBoundedEvs StatesIntoPbAllocPlacedBudget StatesIntoPbEnv
   statesIntoPbPlacedRoFreeSpecXOfEnv
   statesIntoPbPlacedRoFreeSpecXOfEnv_of_placedSpecXOfEnv
   statesIntoPbPlacedRoSpecXOfEnv
   statesIntoPbPlacedSpecOfEnv statesIntoPbPlacedSpecXOfEnv
   statesIntoPbPlacedSpecXOfEnv_of_statesIntoPbPlacedSpecOfEnv
   statesIntoPbVariantPlacedSpec statesIntoPbVariantPlacedSpecOfEnv
   withLsCodeLoaded_statesIntoPbPlacedSpecXOfEnv_of_statesIntoPbPlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1PlacedBudget
  (KeysUnsampledEnv states_into_pb_keysUnsampled_of_env_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2PlacedBudget
  (Ct2SampledEnv ct2SampledEnv_imp_spqrBoundedEvs
   states_into_pb_ct2Sampled_of_env_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3PlacedBudget
  (KeysSampledEnv keysSampledEnv_imp_spqrBoundedEvs
   states_into_pb_keysSampled_of_env_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3bPlacedBudget
  (Ct1ReceivedEnv ct1ReceivedEnv_imp_spqrBoundedEvs
   states_into_pb_ct1Received_of_env_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aPlacedBudget
  (NoHeaderReceivedEnv states_into_pb_noHeaderReceived_of_env_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4bPlacedBudget
  (HeaderReceivedEnv states_into_pb_headerReceived_of_env_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cPlacedBudget
  (EkSentCt1ReceivedEnv states_into_pb_ekSentCt1Received_of_env_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4dPlacedBudget
  (HeaderSentEnv states_into_pb_headerSent_of_env_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5PlacedBudget
  (sessionMemcpyRegion_ok_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aPlacedBudget
  (EkReceivedCt1SampledEnv ekReceivedCt1SampledEnv_imp_spqrBoundedEvs
   encoderIntoPbEnv_imp_spqrBoundedEvs
   states_into_pb_ekReceivedCt1Sampled_of_env_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cBudget
  (ct1AcknowledgedEnv_imp_spqrBoundedEvs)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cPlacedBudget
  (Ct1AcknowledgedEnv states_into_pb_ct1Acknowledged_of_env_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5ePlacedBudget
  (Ct1SampledEnv ct1SampledEnv_imp_spqrBoundedEvs
   decoderIntoPbEnv_imp_spqrBoundedEvs
   states_into_pb_ct1Sampled_of_env_placed)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)

/-! ## 1. Exact Binary Allocator Envelopes Across All 11 `States` Constructors -/

/-- Exact binary allocator event envelope of `<spqr::v1::chunked::states::States>::into_pb`
    (Block `334`) dispatched by `States` constructor. -/
def StatesIntoPbExactVariantEnv {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) (evs : List AllocEvent) : Prop :=
  match st with
  | .keysUnsampled _ => KeysUnsampledEnv evs
  | .keysSampled s => KeysSampledEnv s evs
  | .headerSent s => HeaderSentEnv s evs
  | .ct1Received s => Ct1ReceivedEnv s evs
  | .ekSentCt1Received s => EkSentCt1ReceivedEnv s evs
  | .noHeaderReceived s => NoHeaderReceivedEnv s evs
  | .headerReceived s => HeaderReceivedEnv s evs
  | .ct1Sampled s => Ct1SampledEnv s evs
  | .ekReceivedCt1Sampled s => EkReceivedCt1SampledEnv s evs
  | .ct1Acknowledged s => Ct1AcknowledgedEnv s evs
  | .ct2Sampled s => Ct2SampledEnv s evs

/-- Exact binary allocator event envelope of `<spqr::v1::chunked::states::States>::into_pb`
    (Block `334`) on `StatesIntoPbGhost F`. -/
def StatesIntoPbExactEnv {F : ShaCompress}
    (x : StatesIntoPbGhost F) (evs : List AllocEvent) : Prop :=
  StatesIntoPbExactVariantEnv x.st evs

/-- `<States>::into_pb` (`Block 334`) meets
    `withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecOfEnv M A lim F StatesIntoPbExactEnv)`
    on `(blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)`. -/
def StatesIntoPbExactPlacedOkExt [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
    (blkPl_334).base
    (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecOfEnv M A lim F StatesIntoPbExactEnv))

/-- `<States>::into_pb` (`Block 334`) meets
    `withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv M A lim F StatesIntoPbExactEnv)`
    on `libsignalSessionLib.blockProgram lsmpl 334 (Rust.withPanics ext)` at `lsmpl.base 334`. -/
def StatesIntoPbExactPlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 334 (Rust.withPanics ext))
    (lsmpl.base 334)
    (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv M A lim F StatesIntoPbExactEnv))

/-- `<States>::into_pb` (`Block 334`) meets
    `withLsCodeRoLoaded lsmpl (statesIntoPbPlacedRoFreeSpecXOfEnv M A lim F StatesIntoPbExactEnv)`
    on `(blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)`. -/
def StatesIntoPbExactPlacedRoFreeOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
    (blkPl_334).base
    (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedRoFreeSpecXOfEnv M A lim F StatesIntoPbExactEnv))

/-! ## 2. `SpqrBoundedEvs` Bridges for Arms `Part4a`–`Part4d` & Unified `StatesIntoPbBounded` -/

theorem noHeaderReceivedEnv_imp_spqrBoundedEvs {F : ShaCompress}
    {s : NoHeaderReceived spqrPolyApi (spqrAuthApi F)}
    {maxAllocs maxReq : Nat} {evs : List AllocEvent}
    (hcnt : 1 + s.receiving_hdr.pts.length ≤ maxAllocs)
    (h384 : 384 ≤ maxReq)
    (hpts : ∀ sl ∈ s.receiving_hdr.pts,
      4 * sl.vec.length ≤ MallocngMaxAllocSize ∧ 4 * sl.vec.length ≤ maxReq)
    (henv : NoHeaderReceivedEnv s evs) :
    SpqrBoundedEvs maxAllocs maxReq evs :=
  decoderIntoPbEnv_imp_spqrBoundedEvs hcnt h384 hpts henv

theorem headerReceivedEnv_imp_spqrBoundedEvs {F : ShaCompress}
    {s : HeaderReceived spqrPolyApi (spqrAuthApi F)}
    {maxAllocs maxReq : Nat} {evs : List AllocEvent}
    (hcnt : 1 + s.receiving_ek.pts.length ≤ maxAllocs)
    (h384 : 384 ≤ maxReq)
    (hpts : ∀ sl ∈ s.receiving_ek.pts,
      4 * sl.vec.length ≤ MallocngMaxAllocSize ∧ 4 * sl.vec.length ≤ maxReq)
    (henv : HeaderReceivedEnv s evs) :
    SpqrBoundedEvs maxAllocs maxReq evs :=
  decoderIntoPbEnv_imp_spqrBoundedEvs hcnt h384 hpts henv

theorem ekSentCt1ReceivedEnv_imp_spqrBoundedEvs {F : ShaCompress}
    {s : EkSentCt1Received spqrPolyApi (spqrAuthApi F)}
    {maxAllocs maxReq : Nat} {evs : List AllocEvent}
    (hcnt : 1 + s.receiving_ct2.pts.length ≤ maxAllocs)
    (h384 : 384 ≤ maxReq)
    (hpts : ∀ sl ∈ s.receiving_ct2.pts,
      4 * sl.vec.length ≤ MallocngMaxAllocSize ∧ 4 * sl.vec.length ≤ maxReq)
    (henv : EkSentCt1ReceivedEnv s evs) :
    SpqrBoundedEvs maxAllocs maxReq evs :=
  decoderIntoPbEnv_imp_spqrBoundedEvs hcnt h384 hpts henv

theorem headerSentEnv_imp_spqrBoundedEvs {F : ShaCompress}
    {s : HeaderSent spqrPolyApi (spqrAuthApi F)}
    {maxAllocs maxReq : Nat} {evs : List AllocEvent}
    (hcnt : 3 + (encoderIntoPbVecs s.sending_ek).length + s.receiving_ct1.pts.length ≤ maxAllocs)
    (h384 : 384 ≤ maxReq)
    (hslots : ∀ cs ∈ encoderIntoPbVecs s.sending_ek,
      2 * cs.length ≤ MallocngMaxAllocSize ∧ 2 * cs.length ≤ maxReq)
    (hpts : ∀ sl ∈ s.receiving_ct1.pts,
      4 * sl.vec.length ≤ MallocngMaxAllocSize ∧ 4 * sl.vec.length ≤ maxReq)
    (henv : HeaderSentEnv s evs) :
    SpqrBoundedEvs maxAllocs maxReq evs := by
  rcases henv with henc | ⟨evs_enc, evs_dec, rfl, henc, hdec⟩
  · have h1 := encoderIntoPbEnv_imp_spqrBoundedEvs (Nat.le_refl _) h384 hslots henc
    exact SpqrBoundedEvs.mono (by omega) (Nat.le_refl _) h1
  · have h1 := encoderIntoPbEnv_imp_spqrBoundedEvs (Nat.le_refl _) h384 hslots henc
    have h2 := decoderIntoPbEnv_imp_spqrBoundedEvs (Nat.le_refl _) h384 hpts hdec
    exact SpqrBoundedEvs.mono (by omega) (by omega) (SpqrBoundedEvs.append h1 h2)

/-- Sufficient allocation-count and per-slot byte-length bounds on `st` ensuring
    `StatesIntoPbExactVariantEnv st evs → SpqrBoundedEvs maxAllocs maxReq evs`. -/
def StatesIntoPbBounded {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) (maxAllocs maxReq : Nat) : Prop :=
  match st with
  | .keysUnsampled _ => True
  | .keysSampled s =>
      2 + (encoderIntoPbVecs s.sending_hdr).length ≤ maxAllocs ∧
      384 ≤ maxReq ∧
      (∀ cs ∈ encoderIntoPbVecs s.sending_hdr,
        2 * cs.length ≤ MallocngMaxAllocSize ∧ 2 * cs.length ≤ maxReq)
  | .headerSent s =>
      3 + (encoderIntoPbVecs s.sending_ek).length + s.receiving_ct1.pts.length ≤ maxAllocs ∧
      384 ≤ maxReq ∧
      (∀ cs ∈ encoderIntoPbVecs s.sending_ek,
        2 * cs.length ≤ MallocngMaxAllocSize ∧ 2 * cs.length ≤ maxReq) ∧
      (∀ sl ∈ s.receiving_ct1.pts,
        4 * sl.vec.length ≤ MallocngMaxAllocSize ∧ 4 * sl.vec.length ≤ maxReq)
  | .ct1Received s =>
      2 + (encoderIntoPbVecs s.sending_ek).length ≤ maxAllocs ∧
      384 ≤ maxReq ∧
      (∀ cs ∈ encoderIntoPbVecs s.sending_ek,
        2 * cs.length ≤ MallocngMaxAllocSize ∧ 2 * cs.length ≤ maxReq)
  | .ekSentCt1Received s =>
      1 + s.receiving_ct2.pts.length ≤ maxAllocs ∧
      384 ≤ maxReq ∧
      (∀ sl ∈ s.receiving_ct2.pts,
        4 * sl.vec.length ≤ MallocngMaxAllocSize ∧ 4 * sl.vec.length ≤ maxReq)
  | .noHeaderReceived s =>
      1 + s.receiving_hdr.pts.length ≤ maxAllocs ∧
      384 ≤ maxReq ∧
      (∀ sl ∈ s.receiving_hdr.pts,
        4 * sl.vec.length ≤ MallocngMaxAllocSize ∧ 4 * sl.vec.length ≤ maxReq)
  | .headerReceived s =>
      1 + s.receiving_ek.pts.length ≤ maxAllocs ∧
      384 ≤ maxReq ∧
      (∀ sl ∈ s.receiving_ek.pts,
        4 * sl.vec.length ≤ MallocngMaxAllocSize ∧ 4 * sl.vec.length ≤ maxReq)
  | .ct1Sampled s =>
      4 + (encoderIntoPbVecs s.sending_ct1).length + s.receiving_ek.pts.length ≤ maxAllocs ∧
      384 ≤ maxReq ∧
      s.uc.ct1.length ≤ MallocngMaxAllocSize ∧
      s.uc.ct1.length ≤ maxReq ∧
      (∀ cs ∈ encoderIntoPbVecs s.sending_ct1,
        2 * cs.length ≤ MallocngMaxAllocSize ∧ 2 * cs.length ≤ maxReq) ∧
      (∀ sl ∈ s.receiving_ek.pts,
        4 * sl.vec.length ≤ MallocngMaxAllocSize ∧ 4 * sl.vec.length ≤ maxReq)
  | .ekReceivedCt1Sampled s =>
      3 + (encoderIntoPbVecs s.sending_ct1).length ≤ maxAllocs ∧
      384 ≤ maxReq ∧
      s.uc.ct1.length ≤ MallocngMaxAllocSize ∧
      s.uc.ct1.length ≤ maxReq ∧
      (∀ cs ∈ encoderIntoPbVecs s.sending_ct1,
        2 * cs.length ≤ MallocngMaxAllocSize ∧ 2 * cs.length ≤ maxReq)
  | .ct1Acknowledged s =>
      2 + s.receiving_ek.pts.length ≤ maxAllocs ∧
      384 ≤ maxReq ∧
      s.uc.ct1.length ≤ MallocngMaxAllocSize ∧
      s.uc.ct1.length ≤ maxReq ∧
      (∀ sl ∈ s.receiving_ek.pts,
        4 * sl.vec.length ≤ MallocngMaxAllocSize ∧ 4 * sl.vec.length ≤ maxReq)
  | .ct2Sampled s =>
      2 + (encoderIntoPbVecs s.sending_ct2).length ≤ maxAllocs ∧
      384 ≤ maxReq ∧
      (∀ cs ∈ encoderIntoPbVecs s.sending_ct2,
        2 * cs.length ≤ MallocngMaxAllocSize ∧ 2 * cs.length ≤ maxReq)

/-- Specialization of `StatesIntoPbBounded` to the `StatesIntoPbEnv` (`64`-alloc, linear-in-`encodeRaw`)
    parameters. -/
def StatesIntoPbWellSized {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) : Prop :=
  StatesIntoPbBounded st 64 (2 * (V1State.encodeRaw st.into_pb).length + 1024)

theorem statesIntoPbExactVariantEnv_imp_spqrBoundedEvs {F : ShaCompress}
    {st : States spqrPolyApi (spqrAuthApi F)}
    {maxAllocs maxReq : Nat} {evs : List AllocEvent}
    (hbnd : StatesIntoPbBounded st maxAllocs maxReq)
    (henv : StatesIntoPbExactVariantEnv st evs) :
    SpqrBoundedEvs maxAllocs maxReq evs := by
  cases st with
  | keysUnsampled s =>
    change evs = [] at henv
    subst henv
    exact SpqrBoundedEvs.nil maxAllocs maxReq
  | keysSampled s =>
    rcases hbnd with ⟨hcnt, h384, hslots⟩
    exact keysSampledEnv_imp_spqrBoundedEvs hcnt h384 hslots henv
  | headerSent s =>
    rcases hbnd with ⟨hcnt, h384, hslots, hpts⟩
    exact headerSentEnv_imp_spqrBoundedEvs hcnt h384 hslots hpts henv
  | ct1Received s =>
    rcases hbnd with ⟨hcnt, h384, hslots⟩
    exact ct1ReceivedEnv_imp_spqrBoundedEvs hcnt h384 hslots henv
  | ekSentCt1Received s =>
    rcases hbnd with ⟨hcnt, h384, hpts⟩
    exact ekSentCt1ReceivedEnv_imp_spqrBoundedEvs hcnt h384 hpts henv
  | noHeaderReceived s =>
    rcases hbnd with ⟨hcnt, h384, hpts⟩
    exact noHeaderReceivedEnv_imp_spqrBoundedEvs hcnt h384 hpts henv
  | headerReceived s =>
    rcases hbnd with ⟨hcnt, h384, hpts⟩
    exact headerReceivedEnv_imp_spqrBoundedEvs hcnt h384 hpts henv
  | ct1Sampled s =>
    rcases hbnd with ⟨hcnt, h384, hct1_max, hct1_req, hslots, hpts⟩
    exact ct1SampledEnv_imp_spqrBoundedEvs hcnt h384 hct1_max hct1_req hslots hpts henv
  | ekReceivedCt1Sampled s =>
    rcases hbnd with ⟨hcnt, h384, hct1_max, hct1_req, hslots⟩
    exact ekReceivedCt1SampledEnv_imp_spqrBoundedEvs hcnt h384 hct1_max hct1_req hslots henv
  | ct1Acknowledged s =>
    rcases hbnd with ⟨hcnt, h384, hct1_max, hct1_req, hpts⟩
    exact ct1AcknowledgedEnv_imp_spqrBoundedEvs hcnt h384 hct1_max hct1_req hpts henv
  | ct2Sampled s =>
    rcases hbnd with ⟨hcnt, h384, hslots⟩
    exact ct2SampledEnv_imp_spqrBoundedEvs hcnt h384 hslots henv

theorem statesIntoPbExactVariantEnv_imp_default {F : ShaCompress}
    {st : States spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (hws : StatesIntoPbWellSized st)
    (henv : StatesIntoPbExactVariantEnv st evs) :
    SpqrBoundedEvs 64 (2 * (V1State.encodeRaw st.into_pb).length + 1024) evs :=
  statesIntoPbExactVariantEnv_imp_spqrBoundedEvs hws henv

theorem statesIntoPbWellSized_keysUnsampled {F : ShaCompress}
    (s : KeysUnsampled (spqrAuthApi F)) :
    StatesIntoPbWellSized (States.keysUnsampled (P := spqrPolyApi) s) :=
  trivial

theorem statesIntoPbWellSized_noHeaderReceived_of_pts_nil {F : ShaCompress}
    (s : NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (hpts : s.receiving_hdr.pts = []) :
    StatesIntoPbWellSized (.noHeaderReceived s) := by
  dsimp only [StatesIntoPbWellSized, StatesIntoPbBounded]
  rw [hpts]
  exact ⟨by decide, by omega, fun _ h => nomatch h⟩

/-! ## 3. Relocatable `[LibsignalPlacement]` Block-`334` Verification Theorems -/

/-- Envelope-parametric per-variant correctness of `<spqr::v1::chunked::states::States>::into_pb`
    (Block `334`) across all 11 `States` constructors under `[LibsignalPlacement]`. -/
theorem states_into_pb_variant_of_env_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (st : States spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, StatesIntoPbExactVariantEnv st evs → Env evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpecOfEnv M A lim F st Env) := by
  cases st with
  | keysUnsampled s =>
    exact states_into_pb_keysUnsampled_of_env_placed s (hEnv [] rfl)
  | keysSampled s =>
    exact states_into_pb_keysSampled_of_env_placed henc_raw s hEnv
  | headerSent s =>
    exact states_into_pb_headerSent_of_env_placed henc_raw hdec_raw hmemcpy_raw s hEnv
  | ct1Received s =>
    exact states_into_pb_ct1Received_of_env_placed henc_raw s hEnv
  | ekSentCt1Received s =>
    exact states_into_pb_ekSentCt1Received_of_env_placed hdec_raw hmemcpy_raw s hEnv
  | noHeaderReceived s =>
    exact states_into_pb_noHeaderReceived_of_env_placed hdec_raw hmemcpy_raw s hEnv
  | headerReceived s =>
    exact states_into_pb_headerReceived_of_env_placed hdec_raw hmemcpy_raw s hEnv
  | ct1Sampled s =>
    exact states_into_pb_ct1Sampled_of_env_placed hA henc_raw hdec_raw s hEnv
  | ekReceivedCt1Sampled s =>
    exact states_into_pb_ekReceivedCt1Sampled_of_env_placed hA henc_raw s hEnv
  | ct1Acknowledged s =>
    exact states_into_pb_ct1Acknowledged_of_env_placed hA hdec_raw hmemcpy_raw s hEnv
  | ct2Sampled s =>
    exact states_into_pb_ct2Sampled_of_env_placed henc_raw s hEnv

/-- Exact-envelope per-variant correctness of `<spqr::v1::chunked::states::States>::into_pb`
    (Block `334`) across all 11 `States` constructors under `[LibsignalPlacement]`. -/
theorem states_into_pb_variant_env_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (st : States spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpecOfEnv M A lim F st
        (StatesIntoPbExactVariantEnv st)) :=
  states_into_pb_variant_of_env_placed hA henc_raw hdec_raw hmemcpy_raw st (fun _ h => h)

/-- Exact-envelope per-variant correctness deriving `hmemcpy_raw` from `hA`. -/
theorem states_into_pb_variant_env_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (st : States spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpecOfEnv M A lim F st
        (StatesIntoPbExactVariantEnv st)) :=
  states_into_pb_variant_env_placed hA henc_raw hdec_raw (sessionMemcpyRegion_ok_placed hA) st

theorem states_into_pb_variant_of_env_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (st : States spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, StatesIntoPbExactVariantEnv st evs → Env evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbVariantPlacedSpecOfEnv M A lim F st Env)) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (states_into_pb_variant_of_env_placed hA henc_raw hdec_raw hmemcpy_raw st hEnv)

theorem states_into_pb_variant_env_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (st : States spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbVariantPlacedSpecOfEnv M A lim F st
          (StatesIntoPbExactVariantEnv st))) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (states_into_pb_variant_env_placed hA henc_raw hdec_raw hmemcpy_raw st)

/-- Per-variant `statesIntoPbVariantPlacedSpec` (`SpqrBoundedEvs 64 ...`) under
    `StatesIntoPbWellSized st`. -/
theorem states_into_pb_variant_of_bounds_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (st : States spqrPolyApi (spqrAuthApi F))
    (hws : StatesIntoPbWellSized st) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpec M A lim F st) :=
  states_into_pb_variant_of_env_placed hA henc_raw hdec_raw hmemcpy_raw st
    (fun _ => statesIntoPbExactVariantEnv_imp_default hws)

theorem states_into_pb_variant_of_bounds_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (st : States spqrPolyApi (spqrAuthApi F))
    (hws : StatesIntoPbWellSized st) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbVariantPlacedSpec M A lim F st)) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (states_into_pb_variant_of_bounds_placed hA henc_raw hdec_raw hmemcpy_raw st hws)

/-- Per-variant `statesIntoPbVariantPlacedSpec` deriving `hmemcpy_raw` from `hA`. -/
theorem states_into_pb_variant_of_bounds_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (st : States spqrPolyApi (spqrAuthApi F))
    (hws : StatesIntoPbWellSized st) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpec M A lim F st) :=
  states_into_pb_variant_of_bounds_placed hA henc_raw hdec_raw
    (sessionMemcpyRegion_ok_placed hA) st hws

theorem states_into_pb_variant_of_bounds_of_alloc_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (st : States spqrPolyApi (spqrAuthApi F))
    (hws : StatesIntoPbWellSized st) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbVariantPlacedSpec M A lim F st)) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (states_into_pb_variant_of_bounds_of_alloc_placed hA henc_raw hdec_raw st hws)

/-- `<spqr::v1::chunked::states::States>::into_pb` (Block `334`, 615 instructions)
    satisfies `statesIntoPbPlacedSpecOfEnv M A lim F Env` on
    `(blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)` whenever `Env` subsumes
    `StatesIntoPbExactEnv`. -/
theorem states_into_pb_placed_of_env_raw [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (hEnv : ∀ x evs, StatesIntoPbExactEnv x evs → Env x evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbPlacedSpecOfEnv M A lim F Env) := by
  apply subroutine_ok_outcome_intro
  intro ⟨x, st⟩ R s0 hpc hrun hpre hal
  exact ((states_into_pb_variant_of_env_placed hA henc_raw hdec_raw hmemcpy_raw x.st
    (hEnv x)).to_outcome ((x.out, x.stA), st) R s0 hpc hrun hpre hal).mono_outcome
    (fun _ hout => hout)

/-- `<spqr::v1::chunked::states::States>::into_pb` (Block `334`, 615 instructions)
    satisfies `statesIntoPbPlacedSpecOfEnv M A lim F StatesIntoPbExactEnv` on
    `(blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)`. -/
theorem states_into_pb_placed_env_raw [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbPlacedSpecOfEnv M A lim F StatesIntoPbExactEnv) :=
  states_into_pb_placed_of_env_raw hA henc_raw hdec_raw hmemcpy_raw (fun _ _ h => h)

theorem states_into_pb_placed_env_of_alloc_raw [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbPlacedSpecOfEnv M A lim F StatesIntoPbExactEnv) :=
  states_into_pb_placed_env_raw hA henc_raw hdec_raw (sessionMemcpyRegion_ok_placed hA)

/-- `<spqr::v1::chunked::states::States>::into_pb` (Block `334`, 615 instructions)
    satisfies `withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecOfEnv M A lim F Env)`. -/
theorem states_into_pb_placed_of_env_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (hEnv : ∀ x evs, StatesIntoPbExactEnv x evs → Env x evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecOfEnv M A lim F Env)) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (states_into_pb_placed_of_env_raw hA henc_raw hdec_raw hmemcpy_raw hEnv)

/-- `<spqr::v1::chunked::states::States>::into_pb` (Block `334`, 615 instructions)
    satisfies `StatesIntoPbExactPlacedOkExt M A lim F ext`. -/
theorem states_into_pb_placed_env_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec) :
    StatesIntoPbExactPlacedOkExt M A lim F ext :=
  states_into_pb_placed_of_env_ok_ext hA henc_raw hdec_raw hmemcpy_raw (fun _ _ h => h)

theorem states_into_pb_placed_env_of_alloc_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim)) :
    StatesIntoPbExactPlacedOkExt M A lim F ext :=
  states_into_pb_placed_env_ok_ext hA henc_raw hdec_raw (sessionMemcpyRegion_ok_placed hA)

/-- `<spqr::v1::chunked::states::States>::into_pb` (Block `334`, 615 instructions)
    satisfies `statesIntoPbPlacedRoSpecXOfEnv M A lim F Env` (`statesIntoPbStackX`, explicit
    `statesIntoPbJumpTablePlacedAt`) on `(blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)`. -/
theorem states_into_pb_placed_of_env_ro_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (hEnv : ∀ x evs, StatesIntoPbExactEnv x evs → Env x evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbPlacedRoSpecXOfEnv M A lim F Env) :=
  statesIntoPbPlacedSpecXOfEnv_of_statesIntoPbPlacedSpecOfEnv
    (states_into_pb_placed_of_env_raw hA henc_raw hdec_raw hmemcpy_raw hEnv)

theorem states_into_pb_placed_env_ro_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbPlacedRoSpecXOfEnv M A lim F StatesIntoPbExactEnv) :=
  states_into_pb_placed_of_env_ro_ok_x hA henc_raw hdec_raw hmemcpy_raw (fun _ _ h => h)

/-- `<spqr::v1::chunked::states::States>::into_pb` (Block `334`, 615 instructions)
    satisfies `withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv M A lim F Env)`. -/
theorem states_into_pb_placed_of_env_cl_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (hEnv : ∀ x evs, StatesIntoPbExactEnv x evs → Env x evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv M A lim F Env)) :=
  withLsCodeLoaded_statesIntoPbPlacedSpecXOfEnv_of_statesIntoPbPlacedSpecOfEnv
    (states_into_pb_placed_of_env_ok_ext hA henc_raw hdec_raw hmemcpy_raw hEnv)

theorem states_into_pb_placed_env_cl_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv M A lim F StatesIntoPbExactEnv)) :=
  states_into_pb_placed_of_env_cl_ok_x hA henc_raw hdec_raw hmemcpy_raw (fun _ _ h => h)

/-- `<spqr::v1::chunked::states::States>::into_pb` (Block `334`, 615 instructions)
    satisfies `withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv M A lim F Env)` on
    `libsignalSessionLib.blockProgram lsmpl 334 (Rust.withPanics ext)` at `lsmpl.base 334`. -/
theorem states_into_pb_placed_of_env_ok_x_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (hEnv : ∀ x evs, StatesIntoPbExactEnv x evs → Env x evs) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 334 (Rust.withPanics ext))
      (lsmpl.base 334)
      (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv M A lim F Env)) := by
  have h1 := states_into_pb_placed_of_env_cl_ok_x hA henc_raw hdec_raw hmemcpy_raw hEnv
  have hprog : (blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext) =
      libsignalSessionLib.blockProgram lsmpl 334 (Rust.withPanics ext) :=
    (inferInstance : IsLsBlockProg
      ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      334 (Rust.withPanics ext)).eq_blockProgram
  have hbase : (blkPl_334).base = lsmpl.base 334 := rfl
  rw [hprog, hbase] at h1
  exact h1

/-- `<spqr::v1::chunked::states::States>::into_pb` (Block `334`, 615 instructions)
    satisfies `StatesIntoPbExactPlacedOkX M A lim F ext`. -/
theorem states_into_pb_placed_env_ok_x_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec) :
    StatesIntoPbExactPlacedOkX M A lim F ext :=
  states_into_pb_placed_of_env_ok_x_blockProgram hA henc_raw hdec_raw hmemcpy_raw (fun _ _ h => h)

theorem states_into_pb_placed_env_of_alloc_ok_x_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim)) :
    StatesIntoPbExactPlacedOkX M A lim F ext :=
  states_into_pb_placed_env_ok_x_blockProgram hA henc_raw hdec_raw (sessionMemcpyRegion_ok_placed hA)

/-- `<spqr::v1::chunked::states::States>::into_pb` (Block `334`, 615 instructions)
    satisfies `withLsCodeRoLoaded lsmpl (statesIntoPbPlacedRoFreeSpecXOfEnv M A lim F Env)`
    (mirroring `TopPlaced.states_into_pb_placed_ok_x` with `.rodata` jump table discharged). -/
theorem states_into_pb_placed_of_env_ro_free_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (hEnv : ∀ x evs, StatesIntoPbExactEnv x evs → Env x evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedRoFreeSpecXOfEnv M A lim F Env)) :=
  statesIntoPbPlacedRoFreeSpecXOfEnv_of_placedSpecXOfEnv
    (states_into_pb_placed_of_env_cl_ok_x hA henc_raw hdec_raw hmemcpy_raw hEnv)

/-- `<spqr::v1::chunked::states::States>::into_pb` (Block `334`, 615 instructions)
    satisfies `StatesIntoPbExactPlacedRoFreeOkX M A lim F ext`. -/
theorem states_into_pb_placed_env_ro_free_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec) :
    StatesIntoPbExactPlacedRoFreeOkX M A lim F ext :=
  states_into_pb_placed_of_env_ro_free_ok_x hA henc_raw hdec_raw hmemcpy_raw (fun _ _ h => h)

theorem states_into_pb_placed_env_of_alloc_ro_free_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim)) :
    StatesIntoPbExactPlacedRoFreeOkX M A lim F ext :=
  states_into_pb_placed_env_ro_free_ok_x hA henc_raw hdec_raw (sessionMemcpyRegion_ok_placed hA)

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopPlacedBudget
