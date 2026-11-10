/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1AcknowledgedClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceivedClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysUnsampledClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB304PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB305PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB306RPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB307PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget
import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
import LibsignalBinary.Proofs.SpqrV1.Auth.AuthEncodeMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.BytesMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergePart2CodeSym
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.SpqrV1.Varint.VarintCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym

/-!
# Guarded-Tight Placed Budget Contracts for Blocks `304`–`307`

Exports the `[LibsignalPlacement]` guarded-tight `SpqrTightEvs` contracts (`tlb_*PlacedTightOkOf`)
for `Chunked.KeysSampled::merge` (Block `304`: `384,723` B, `maxReq = 2,560` B, `authOps + 4 + encOps ≤ maxOps`),
`Chunked.KeysUnsampled::merge` (Block `305`: `2,952` B, `maxReq = 32` B, `authOps ≤ maxOps`),
`Chunked.HeaderReceived::merge` (Block `306`: `349,561` B, `maxReq = 2,560` B, `authOps + 2 + decOps ≤ maxOps`),
and `Chunked.Ct1Acknowledged::merge` (Block `307`: `388,717` B, `maxReq = 2,560` B, `ucOps + decOps ≤ maxOps`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeTightPlacedBudgetB

open Arm64 ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement instIsLsBlockProg_261 instIsLsBlockProg_263
   instIsLsBlockProg_290 instIsLsBlockProg_291 instIsLsBlockProg_295 instIsLsBlockProg_312
   libsignalMutatedBlocks libsignalSessionExterns libsignalSessionLib ls_blockPlacement_base
   ls_externAt?_blockProgram_eq_of_externs_eq lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchet
  (extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
   withLsCodeRoLoaded)
open CryptoVerification.RecordCodecs.Placed (instIsLsBlockProg_257)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (instIsLsBlockProg_296 instIsLsBlockProg_297 instIsLsBlockProg_306)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2
  (instIsLsBlockProg_304 instIsLsBlockProg_305 instIsLsBlockProg_307)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_AuthMergePlacedTightOk tlb_AuthMergePlacedTightOkOf
   tlb_ChunkedCt1AcknowledgedMergePlacedTightOk tlb_ChunkedCt1AcknowledgedMergePlacedTightOkOf
   tlb_ChunkedHeaderReceivedMergePlacedTightOk tlb_ChunkedHeaderReceivedMergePlacedTightOkOf
   tlb_ChunkedKeysSampledMergePlacedTightOk tlb_ChunkedKeysSampledMergePlacedTightOkOf
   tlb_ChunkedKeysUnsampledMergePlacedTightOk tlb_ChunkedKeysUnsampledMergePlacedTightOkOf
   tlb_PolyDecoderMergePlacedTightOk tlb_PolyDecoderMergePlacedTightOkOf
   tlb_PolyEncoderMergePlacedTightOk tlb_PolyEncoderMergePlacedTightOkOf
   tlb_UcCt1SentMergePlacedTightOk tlb_UcCt1SentMergePlacedTightOkOf)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (authMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1AcknowledgedClPlacedBudget
  (chunked_ct1_acknowledged_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (chunkedCt1AcknowledgedMergeSpec decodeErrorPushMergeBudgetSpec unchunkedCt1SentMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceivedClPlacedBudget
  (chunked_header_received_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (chunkedHeaderReceivedMergeSpec chunkedKeysSampledMergeSpec chunkedKeysUnsampledMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledClPlacedBudget
  (chunked_keys_sampled_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysUnsampledClPlacedBudget
  (chunked_keys_unsampled_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (bytesMerge3RawBudgetSpec polyDecoderMergeSpec polyEncoderMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

/-! ## 1. Own-Block ↔ Caller-Block Transfer Helpers (`e2kb_`) -/

private class e2kb_IsLsValidBlock [LibsignalPlacement] (j : Nat) : Prop where
  lt_blocks : j < 624
  not_mutated : (j ∈ libsignalMutatedBlocks) = false
  externs_eq : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns

private instance [LibsignalPlacement] : e2kb_IsLsValidBlock 257 :=
  ⟨by decide, by decide, (instIsLsBlockProg_257 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2kb_IsLsValidBlock 261 :=
  ⟨by decide, by decide, (instIsLsBlockProg_261 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2kb_IsLsValidBlock 263 :=
  ⟨by decide, by decide, (instIsLsBlockProg_263 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2kb_IsLsValidBlock 290 :=
  ⟨by decide, by decide, (instIsLsBlockProg_290 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2kb_IsLsValidBlock 291 :=
  ⟨by decide, by decide, (instIsLsBlockProg_291 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2kb_IsLsValidBlock 295 :=
  ⟨by decide, by decide, (instIsLsBlockProg_295 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2kb_IsLsValidBlock 296 :=
  ⟨by decide, by decide, (instIsLsBlockProg_296 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2kb_IsLsValidBlock 297 :=
  ⟨by decide, by decide, (instIsLsBlockProg_297 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2kb_IsLsValidBlock 304 :=
  ⟨by decide, by decide, (instIsLsBlockProg_304 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2kb_IsLsValidBlock 305 :=
  ⟨by decide, by decide, (instIsLsBlockProg_305 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2kb_IsLsValidBlock 306 :=
  ⟨by decide, by decide, (instIsLsBlockProg_306 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2kb_IsLsValidBlock 307 :=
  ⟨by decide, by decide, (instIsLsBlockProg_307 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2kb_IsLsValidBlock 312 :=
  ⟨by decide, by decide, (instIsLsBlockProg_312 (fun _ => none)).externs_eq⟩

private theorem e2kb_lift_cro_of_own [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hj : e2kb_IsLsValidBlock j] {spec : Spec α}
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j)
      (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok callerProg (lsmpl.base j) (withLsCodeRoLoaded lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hfr0, _⟩ := extract_withLsCodeRoLoaded hpre
  have hQL : (libsignalSessionLib.blockProgram lsmpl j H).CodeLoaded s0.mem :=
    hfr0.1 j hj.lt_blocks hj.not_mutated H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc,
      (libsignalSessionLib.blockProgram lsmpl j H).externAt? pc = callerProg.externAt? pc :=
    fun pc => by
      rw [hcaller.eq_blockProgram,
        ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
          (hj.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : (libsignalSessionLib.blockProgram lsmpl j H).svc = callerProg.svc := by
    rw [hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

private theorem e2kb_lift_cl_of_own [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [e2kb_IsLsValidBlock j] {spec : Spec α}
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j)
      (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok callerProg (lsmpl.base j) (withLsCodeRoLoaded lsmpl spec) :=
  e2kb_lift_cro_of_own (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hcallee)

private theorem e2kb_own_of_blk_cro [LibsignalPlacement] {α : Type}
    {blkProg : Program} {i : Nat} {H : LibsignalHooks}
    [hprog : IsLsBlockProg blkProg i H] {spec : Spec α}
    (h : subroutine_ok blkProg (libsignalSessionLib.blockPlacement lsmpl i).base
      (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl i H) (lsmpl.base i)
      (withLsCodeRoLoaded lsmpl spec) := by
  rw [← hprog.eq_blockProgram, ← ls_blockPlacement_base lsmpl i]
  exact h

/-! ## 2. Block `304` (`Chunked.KeysSampled::merge`) -/

/-- Parametric guarded-tight contract for Block `304` (`Chunked.KeysSampled::merge`) within `SpqrTightEvs maxOps 384723 2560` (`authOps + 4 + encOps ≤ maxOps`). -/
theorem e2kb_chunkedKeysSampled_merge_placed_tight_ok_of_fallback [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {authOps encOps maxOps : Nat} (hOps : authOps + 4 + encOps ≤ maxOps)
    {ext : String → Option (State → State)}
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim authOps ext)
    (hEncTight : tlb_PolyEncoderMergePlacedTightOkOf A lim encOps ext)
    (hFallback : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim))) :
    tlb_ChunkedKeysSampledMergePlacedTightOkOf A lim maxOps ext := by
  exact E2aTightB304PlacedBudget.e2b304_chunkedKeysSampledMerge_placed_tight_ok_of_fallback
    A lim hOps hVarint hBytes hAuthTight hEncTight hFallback

/-- Full contract-based corollary for Block `304` (`Chunked.KeysSampled::merge`) deriving the
`¬ tlb_ChunkedKeysSampledDom` fallback from `chunked_keys_sampled_merge_cl_placed_ok_of_contracts`. -/
theorem e2kb_chunkedKeysSampled_merge_placed_tight_ok_of [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {authOps encOps maxOps : Nat} (hOps : authOps + 4 + encOps ≤ maxOps)
    {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hPolyEncBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim authOps ext)
    (hEncTight : tlb_PolyEncoderMergePlacedTightOkOf A lim encOps ext) :
    tlb_ChunkedKeysSampledMergePlacedTightOkOf A lim maxOps ext :=
  e2kb_chunkedKeysSampled_merge_placed_tight_ok_of_fallback A lim hOps hVarint hBytes
    hAuthTight hEncTight
    (e2kb_own_of_blk_cro (chunked_keys_sampled_merge_cl_placed_ok_of_contracts
      (e2kb_lift_cl_of_own hFrom) (e2kb_lift_cl_of_own hPush)
      (e2kb_lift_cl_of_own hVarint) (e2kb_lift_cl_of_own hSkip)
      (e2kb_lift_cro_of_own hBytes) (e2kb_lift_cro_of_own hAuthBase)
      (e2kb_lift_cro_of_own hPolyEncBase)))

/-- Default `43`-op instantiation (`4 + 4 + 35 = 43`) for Block `304`. -/
theorem e2kb_chunkedKeysSampled_merge_placed_tight_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hPolyEncBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOk A lim ext)
    (hEncTight : tlb_PolyEncoderMergePlacedTightOk A lim ext) :
    tlb_ChunkedKeysSampledMergePlacedTightOk A lim ext :=
  e2kb_chunkedKeysSampled_merge_placed_tight_ok_of A lim (by decide : 4 + 4 + 35 ≤ 43)
    hFrom hPush hVarint hSkip hBytes hAuthBase hPolyEncBase hAuthTight hEncTight

/-! ## 3. Block `305` (`Chunked.KeysUnsampled::merge`) -/

/-- Parametric guarded-tight contract for Block `305` (`Chunked.KeysUnsampled::merge`) within `SpqrTightEvs maxOps 2952 32` (`authOps ≤ maxOps`). -/
theorem e2kb_chunkedKeysUnsampled_merge_placed_tight_ok_of_fallback [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {authOps maxOps : Nat} (hOps : authOps ≤ maxOps)
    {ext : String → Option (State → State)}
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim authOps ext)
    (hFallback : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim))) :
    tlb_ChunkedKeysUnsampledMergePlacedTightOkOf A lim maxOps ext := by
  exact E2aTightB305PlacedBudget.e2b305_chunkedKeysUnsampled_merge_placed_tight_of_fallback
    hOps hVarint hAuthTight hFallback

/-- Full contract-based corollary for Block `305` (`Chunked.KeysUnsampled::merge`). -/
theorem e2kb_chunkedKeysUnsampled_merge_placed_tight_ok_of [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {authOps maxOps : Nat} (hOps : authOps ≤ maxOps)
    {ext : String → Option (State → State)}
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
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim authOps ext) :
    tlb_ChunkedKeysUnsampledMergePlacedTightOkOf A lim maxOps ext :=
  e2kb_chunkedKeysUnsampled_merge_placed_tight_ok_of_fallback A lim hOps hVarint hAuthTight
    (e2kb_own_of_blk_cro (chunked_keys_unsampled_merge_cl_placed_ok_of_contracts
      (e2kb_lift_cl_of_own hFrom) (e2kb_lift_cl_of_own hPush)
      (e2kb_lift_cl_of_own hVarint) (e2kb_lift_cl_of_own hSkip)
      (e2kb_lift_cro_of_own hAuthBase)))

/-- Default `4`-op instantiation for Block `305`. -/
theorem e2kb_chunkedKeysUnsampled_merge_placed_tight_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ext : String → Option (State → State)}
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
    (hAuthTight : tlb_AuthMergePlacedTightOk A lim ext) :
    tlb_ChunkedKeysUnsampledMergePlacedTightOk A lim ext :=
  e2kb_chunkedKeysUnsampled_merge_placed_tight_ok_of A lim (Nat.le_refl 4)
    hFrom hPush hVarint hSkip hAuthBase hAuthTight

/-! ## 4. Block `306` (`Chunked.HeaderReceived::merge`) -/

/-- Parametric guarded-tight contract for Block `306` (`Chunked.HeaderReceived::merge`) within `SpqrTightEvs maxOps 349561 2560` (`authOps + 2 + decOps ≤ maxOps`). -/
theorem e2kb_chunkedHeaderReceived_merge_placed_tight_ok_of_fallback [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {authOps decOps maxOps : Nat} (hOps : authOps + 2 + decOps ≤ maxOps)
    {ext : String → Option (State → State)}
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim authOps ext)
    (hDecTight : tlb_PolyDecoderMergePlacedTightOkOf A lim decOps ext)
    (hFallback : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext))
      (lsmpl.base 306) (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim))) :
    tlb_ChunkedHeaderReceivedMergePlacedTightOkOf A lim maxOps ext := by
  exact E2aTightB306RPlacedBudget.e2b306r_chunkedHeaderReceivedMerge_placed_tight_ok_of_fallback
    hOps hAuthTight hDecTight hVarint hBytes hFallback

/-- Full contract-based corollary for Block `306` (`Chunked.HeaderReceived::merge`). -/
theorem e2kb_chunkedHeaderReceived_merge_placed_tight_ok_of [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {authOps decOps maxOps : Nat} (hOps : authOps + 2 + decOps ≤ maxOps)
    {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hPolyDecBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim authOps ext)
    (hDecTight : tlb_PolyDecoderMergePlacedTightOkOf A lim decOps ext) :
    tlb_ChunkedHeaderReceivedMergePlacedTightOkOf A lim maxOps ext :=
  e2kb_chunkedHeaderReceived_merge_placed_tight_ok_of_fallback A lim hOps hVarint hBytes
    hAuthTight hDecTight
    (e2kb_own_of_blk_cro (chunked_header_received_merge_cl_placed_ok_of_contracts
      (e2kb_lift_cl_of_own hFrom) (e2kb_lift_cl_of_own hPush)
      (e2kb_lift_cl_of_own hVarint) (e2kb_lift_cl_of_own hSkip)
      (e2kb_lift_cro_of_own hAuthBase) (e2kb_lift_cro_of_own hBytes)
      (e2kb_lift_cro_of_own hPolyDecBase)))

/-- Default `41`-op instantiation (`4 + 2 + 35 = 41`) for Block `306`. -/
theorem e2kb_chunkedHeaderReceived_merge_placed_tight_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hPolyDecBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOk A lim ext)
    (hDecTight : tlb_PolyDecoderMergePlacedTightOk A lim ext) :
    tlb_ChunkedHeaderReceivedMergePlacedTightOk A lim ext :=
  e2kb_chunkedHeaderReceived_merge_placed_tight_ok_of A lim (by decide : 4 + 2 + 35 ≤ 41)
    hFrom hPush hVarint hSkip hBytes hAuthBase hPolyDecBase hAuthTight hDecTight

/-! ## 5. Block `307` (`Chunked.Ct1Acknowledged::merge`) -/

/-- Parametric guarded-tight contract for Block `307` (`Chunked.Ct1Acknowledged::merge`) within `SpqrTightEvs maxOps 388717 2560` (`ucOps + decOps ≤ maxOps`). -/
theorem e2kb_chunkedCt1Acknowledged_merge_placed_tight_ok_of_fallback [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ucOps decOps maxOps : Nat} (hOps : ucOps + decOps ≤ maxOps)
    {ext : String → Option (State → State)}
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hUcTight : tlb_UcCt1SentMergePlacedTightOkOf A lim ucOps ext)
    (hDecTight : tlb_PolyDecoderMergePlacedTightOkOf A lim decOps ext)
    (hFallback : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim))) :
    tlb_ChunkedCt1AcknowledgedMergePlacedTightOkOf A lim maxOps ext := by
  exact E2aTightB307PlacedBudget.e2b307_chunkedCt1AcknowledgedMerge_placed_tight_ok_of_fallback
    A lim hOps hVarint hUcTight hDecTight hFallback

/-- Full contract-based corollary for Block `307` (`Chunked.Ct1Acknowledged::merge`). -/
theorem e2kb_chunkedCt1Acknowledged_merge_placed_tight_ok_of [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ucOps decOps maxOps : Nat} (hOps : ucOps + decOps ≤ maxOps)
    {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hUc312Base : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 312 (Rust.withPanics ext))
      (lsmpl.base 312) (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)))
    (hPolyDecBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    (hUcTight : tlb_UcCt1SentMergePlacedTightOkOf A lim ucOps ext)
    (hDecTight : tlb_PolyDecoderMergePlacedTightOkOf A lim decOps ext) :
    tlb_ChunkedCt1AcknowledgedMergePlacedTightOkOf A lim maxOps ext :=
  e2kb_chunkedCt1Acknowledged_merge_placed_tight_ok_of_fallback A lim hOps hVarint
    hUcTight hDecTight
    (e2kb_own_of_blk_cro (chunked_ct1_acknowledged_merge_cl_placed_ok_of_contracts
      (e2kb_lift_cl_of_own hFrom) (e2kb_lift_cl_of_own hPush)
      (e2kb_lift_cl_of_own hVarint) (e2kb_lift_cl_of_own hSkip)
      (e2kb_lift_cro_of_own hUc312Base) (e2kb_lift_cro_of_own hPolyDecBase)))

/-- Default `45`-op instantiation (`10 + 35 = 45`) for Block `307`. -/
theorem e2kb_chunkedCt1Acknowledged_merge_placed_tight_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hUc312Base : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 312 (Rust.withPanics ext))
      (lsmpl.base 312) (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)))
    (hPolyDecBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    (hUcTight : tlb_UcCt1SentMergePlacedTightOk A lim ext)
    (hDecTight : tlb_PolyDecoderMergePlacedTightOk A lim ext) :
    tlb_ChunkedCt1AcknowledgedMergePlacedTightOk A lim ext :=
  e2kb_chunkedCt1Acknowledged_merge_placed_tight_ok_of A lim (by decide : 10 + 35 ≤ 45)
    hFrom hPush hVarint hSkip hUc312Base hPolyDecBase hUcTight hDecTight

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeTightPlacedBudgetB
