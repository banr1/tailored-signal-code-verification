/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.SpqrV1.Auth.MergeClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB300PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB301PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB302PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB303PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightU311PlacedBudgetR2
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedClPlacedBudget

/-!
# Guarded-Tight Placed Budget Contracts for Blocks `300`–`303` and `311`–`312`

Exports the `[LibsignalPlacement]` guarded-tight `SpqrTightEvs` contracts (`tlb_*PlacedTightOkOf`)
for `Chunked.Ct1Sampled::merge` (Block `300`: `731,332` B, `maxReq = 2,560` B, `ucOps + encOps + decOps ≤ maxOps`),
`Unchunked.EkSentCt1Received::merge` (Block `311`: `42,108` B, `authOps + 4 ≤ maxOps`),
`Unchunked.Ct1Sent::merge` (Block `312`: `46,102` B, `authOps + 6 ≤ maxOps`),
`Chunked.Ct2Sampled::merge` (Block `301`: `345,567` B, `authOps + encOps ≤ maxOps`),
`Chunked.HeaderSent::merge` (Block `302`: `707,760` B, `authOps + 2 + encOps + decOps ≤ maxOps`),
and `Chunked.Ct1Received::merge` (Block `303`: `384,723` B, `ucOps + encOps ≤ maxOps`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeTightPlacedBudgetA

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalPlacement libsignalSessionLib lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalProtoCodec (mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB300PlacedBudget
  (e2ka_b300_chunkedCt1SampledMerge_placed_tight_ok_of)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB301PlacedBudget
  (e2b301_chunkedCt2Sampled_merge_placed_tight_ok_of)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB302PlacedBudget
  (e2b302_chunkedHeaderSentMerge_placed_tight_ok_of)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB303PlacedBudget
  (e2b303_chunkedCt1Received_merge_placed_tight_ok_of)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightU311PlacedBudgetR2
  (e2u311_ucCt1Sent_merge_placed_tight_ok_of
   e2u311_ucEkSentCt1Received_merge_placed_tight_ok_of)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_AuthMergePlacedTightOkOf
   tlb_ChunkedCt1ReceivedMergePlacedTightOk tlb_ChunkedCt1ReceivedMergePlacedTightOkOf
   tlb_ChunkedCt1SampledMergePlacedTightOk tlb_ChunkedCt1SampledMergePlacedTightOkOf
   tlb_ChunkedCt1SampledTightEnvOf
   tlb_ChunkedCt2SampledMergePlacedTightOk tlb_ChunkedCt2SampledMergePlacedTightOkOf
   tlb_ChunkedHeaderSentMergePlacedTightOk tlb_ChunkedHeaderSentMergePlacedTightOkOf
   tlb_PolyDecoderMergePlacedTightOkOf tlb_PolyDecoderTightEnvOf
   tlb_PolyEncoderMergePlacedTightOkOf tlb_PolyEncoderTightEnvOf
   tlb_UcCt1SentMergePlacedTightOk tlb_UcCt1SentMergePlacedTightOkOf
   tlb_UcCt1SentTightEnvOf
   tlb_UcEkSentCt1ReceivedMergePlacedTightOk tlb_UcEkSentCt1ReceivedMergePlacedTightOkOf)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget (bytesMerge3RawBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (authMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (decodeErrorPushMergeBudgetSpec unchunkedCt1SentMergeSpec unchunkedEkSentCt1ReceivedMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (polyDecoderMergeSpec polyEncoderMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

/-! ## 1. Pure Tight-Envelope Composition for Block `300` (`Chunked.Ct1Sampled::merge`) -/

/-- Combining optional `Unchunked.Ct1Sent` (`46,102` B), `PolynomialEncoder` (`342,615` B), and
`PolynomialDecoder` (`342,615` B) tight traces yields `tlb_ChunkedCt1SampledTightEnvOf maxOps`
(`731,332` B, `maxReq = 2,560` B) whenever `ucOps + encOps + decOps ≤ maxOps`. -/
theorem e2ka_chunkedCt1SampledTightEnv_combine {ucOps encOps decOps maxOps : Nat}
    {evsUc evsEnc evsDec : List AllocEvent}
    (hOps : ucOps + encOps + decOps ≤ maxOps)
    (hUc : tlb_UcCt1SentTightEnvOf ucOps evsUc)
    (hEnc : tlb_PolyEncoderTightEnvOf encOps evsEnc)
    (hDec : tlb_PolyDecoderTightEnvOf decOps evsDec) :
    tlb_ChunkedCt1SampledTightEnvOf maxOps (evsUc ++ evsEnc ++ evsDec) := by
  have h12 : SpqrTightEvs (ucOps + encOps) (46102 + 342615) (max 2560 2560) (evsUc ++ evsEnc) :=
    SpqrTightEvs.append hUc hEnc
  have h123 : SpqrTightEvs (ucOps + encOps + decOps) (46102 + 342615 + 342615)
      (max (max 2560 2560) 2560) (evsUc ++ evsEnc ++ evsDec) :=
    SpqrTightEvs.append h12 hDec
  exact h123.mono hOps (by decide) (by decide)

theorem e2ka_ucCt1SentTightEnv_nil (ucOps : Nat) :
    tlb_UcCt1SentTightEnvOf ucOps [] :=
  SpqrTightEvs.nil ucOps 46102 2560

theorem e2ka_polyEncoderTightEnv_nil (encOps : Nat) :
    tlb_PolyEncoderTightEnvOf encOps [] :=
  SpqrTightEvs.nil encOps 342615 2560

theorem e2ka_polyDecoderTightEnv_nil (decOps : Nat) :
    tlb_PolyDecoderTightEnvOf decOps [] :=
  SpqrTightEvs.nil decOps 342615 2560

/-! ## 2. Block `300` (`Chunked.Ct1Sampled::merge`) -/

/-- **Block `300` (`Chunked.Ct1Sampled::merge`, `maxOps`-parametric):**
Satisfies `tlb_ChunkedCt1SampledMergePlacedTightOkOf A lim maxOps ext` whenever
`ucOps + encOps + decOps ≤ maxOps`, consuming `tlb_UcCt1SentMergePlacedTightOkOf` (`312`),
`tlb_PolyEncoderMergePlacedTightOkOf` (`297`), and `tlb_PolyDecoderMergePlacedTightOkOf` (`296`),
plus the untightened callee contracts for the `¬ Dom` fallback. -/
theorem e2ka_chunkedCt1SampledMerge_placed_tight_ok_of [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ucOps encOps decOps maxOps : Nat} {ext : String → Option (State → State)}
    (hOps : ucOps + encOps + decOps ≤ maxOps)
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hUcBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 312 (Rust.withPanics ext))
      (lsmpl.base 312) (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)))
    (hPolyEncBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hPolyDecBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    (hUcTight : tlb_UcCt1SentMergePlacedTightOkOf A lim ucOps ext)
    (hPolyEncTight : tlb_PolyEncoderMergePlacedTightOkOf A lim encOps ext)
    (hPolyDecTight : tlb_PolyDecoderMergePlacedTightOkOf A lim decOps ext) :
    tlb_ChunkedCt1SampledMergePlacedTightOkOf A lim maxOps ext :=
  e2ka_b300_chunkedCt1SampledMerge_placed_tight_ok_of hOps
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hFrom)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hPush)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hVarint)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hSkip)
    hUcBase hPolyEncBase hPolyDecBase hUcTight hPolyEncTight hPolyDecTight

/-- Default `80`-op specialization (`10 + 35 + 35 = 80`) of Block `300`. -/
theorem e2ka_chunkedCt1SampledMerge_placed_tight_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hUcBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 312 (Rust.withPanics ext))
      (lsmpl.base 312) (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)))
    (hPolyEncBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hPolyDecBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    (hUcTight : tlb_UcCt1SentMergePlacedTightOkOf A lim 10 ext)
    (hPolyEncTight : tlb_PolyEncoderMergePlacedTightOkOf A lim 35 ext)
    (hPolyDecTight : tlb_PolyDecoderMergePlacedTightOkOf A lim 35 ext) :
    tlb_ChunkedCt1SampledMergePlacedTightOk A lim ext :=
  e2ka_chunkedCt1SampledMerge_placed_tight_ok_of (by decide)
    hFrom hPush hVarint hSkip hUcBase hPolyEncBase hPolyDecBase
    hUcTight hPolyEncTight hPolyDecTight

/-! ## 3. Tight Contracts for Blocks `311`, `312`, and `301`–`303` -/

private theorem e2ka_bytesMerge3_poly_of_signed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program}
    {entry : BitVec 64}
    (h : subroutine_ok P entry
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.bytesMerge3RawBudgetSpec M A lim))) :
    subroutine_ok P entry
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget.bytesMerge3RawBudgetSpec
          A lim)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.bytesMerge3RawBudgetSpec M A lim)).pre
          x s0 ∗ R := hpre
  refine h.mono_outcome x R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨h1, hq⟩ | ⟨h1, h2, hq⟩ | ⟨h1, hq⟩)
  · refine Or.inl ⟨hret, hcc, Satisfies.mono ?_ hq⟩
    dsimp only [withLsCodeRoLoaded,
      LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.bytesMerge3RawBudgetSpec,
      LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget.bytesMerge3RawBudgetSpec]
    refine sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
    cases mergeBytes x.1.wt x.1.bs with
    | none => exact Entails.refl _
    | some vr =>
      rcases vr with ⟨v, rest⟩
      dsimp only
      refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_))
      refine Entails.sepExists_elim fun cap' => Entails.sepExists_right cap' ?_
      refine Entails.sepExists_elim fun ptr' => Entails.sepExists_right ptr' ?_
      exact Entails.pure_left fun hp => Entails.pure_right hp.1 (Entails.refl _)
  · exact Or.inr (Or.inl ⟨h1, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, hq⟩))

/-- Guarded-tight contract for Block `311` (`Unchunked.EkSentCt1Received::merge`) within `SpqrTightEvs maxOps 42108 2560` (`authOps + 4 ≤ maxOps`). -/
theorem e2ka_ucEkSentCt1ReceivedMerge_placed_tight_ok_of [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {authOps maxOps : Nat} {ext : String → Option (State → State)}
    (hOps : authOps + 4 ≤ maxOps)
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim)))
    (hAuthBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim authOps ext) :
    tlb_UcEkSentCt1ReceivedMergePlacedTightOkOf A lim maxOps ext :=
  e2u311_ucEkSentCt1Received_merge_placed_tight_ok_of hOps
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hFrom)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hPush)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hVarint)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hSkip)
    (e2ka_bytesMerge3_poly_of_signed hBytes)
    hAuthBase hAuthTight

/-- Guarded-tight contract for Block `312` (`Unchunked.Ct1Sent::merge`) within `SpqrTightEvs maxOps 46102 2560` (`authOps + 6 ≤ maxOps`). -/
theorem e2ka_ucCt1SentMerge_placed_tight_ok_of [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {authOps maxOps : Nat} {ext : String → Option (State → State)}
    (hOps : authOps + 6 ≤ maxOps)
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim)))
    (hAuthBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim authOps ext) :
    tlb_UcCt1SentMergePlacedTightOkOf A lim maxOps ext :=
  e2u311_ucCt1Sent_merge_placed_tight_ok_of hOps
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hFrom)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hPush)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hVarint)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hSkip)
    (e2ka_bytesMerge3_poly_of_signed hBytes)
    hAuthBase hAuthTight

/-- Guarded-tight contract for Block `301` (`Chunked.Ct2Sampled::merge`) within `SpqrTightEvs maxOps 345567 2560` (`authOps + encOps ≤ maxOps`). -/
theorem e2ka_chunkedCt2SampledMerge_placed_tight_ok_of [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {authOps encOps maxOps : Nat} {ext : String → Option (State → State)}
    (hOps : authOps + encOps ≤ maxOps)
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hAuthBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hPolyEncBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim authOps ext)
    (hPolyEncTight : tlb_PolyEncoderMergePlacedTightOkOf A lim encOps ext) :
    tlb_ChunkedCt2SampledMergePlacedTightOkOf A lim maxOps ext :=
  e2b301_chunkedCt2Sampled_merge_placed_tight_ok_of hOps
    hFrom hPush hVarint hSkip hAuthBase hPolyEncBase hAuthTight hPolyEncTight

/-- Guarded-tight contract for Block `302` (`Chunked.HeaderSent::merge`) within `SpqrTightEvs maxOps 707760 2560` (`authOps + 2 + encOps + decOps ≤ maxOps`). -/
theorem e2ka_chunkedHeaderSentMerge_placed_tight_ok_of [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {authOps encOps decOps maxOps : Nat} {ext : String → Option (State → State)}
    (hOps : authOps + 2 + encOps + decOps ≤ maxOps)
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim)))
    (hAuthBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hPolyEncBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hPolyDecBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim authOps ext)
    (hPolyEncTight : tlb_PolyEncoderMergePlacedTightOkOf A lim encOps ext)
    (hPolyDecTight : tlb_PolyDecoderMergePlacedTightOkOf A lim decOps ext) :
    tlb_ChunkedHeaderSentMergePlacedTightOkOf A lim maxOps ext :=
  e2b302_chunkedHeaderSentMerge_placed_tight_ok_of hOps
    hFrom hPush hVarint hSkip hBytes
    hAuthBase hPolyEncBase hPolyDecBase
    hAuthTight hPolyEncTight hPolyDecTight

/-- Guarded-tight contract for Block `303` (`Chunked.Ct1Received::merge`) within `SpqrTightEvs maxOps 384723 2560` (`ucOps + encOps ≤ maxOps`). -/
theorem e2ka_chunkedCt1ReceivedMerge_placed_tight_ok_of [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ucOps encOps maxOps : Nat} {ext : String → Option (State → State)}
    (hOps : ucOps + encOps ≤ maxOps)
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hUcBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 311 (Rust.withPanics ext))
      (lsmpl.base 311) (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hPolyEncBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hUcTight : tlb_UcEkSentCt1ReceivedMergePlacedTightOkOf A lim ucOps ext)
    (hPolyEncTight : tlb_PolyEncoderMergePlacedTightOkOf A lim encOps ext) :
    tlb_ChunkedCt1ReceivedMergePlacedTightOkOf A lim maxOps ext :=
  e2b303_chunkedCt1Received_merge_placed_tight_ok_of hOps
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hFrom)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hPush)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hVarint)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hSkip)
    hUcBase hPolyEncBase hUcTight hPolyEncTight

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeTightPlacedBudgetA
