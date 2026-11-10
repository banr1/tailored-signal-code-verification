/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrMessageMergeLeavesPlacedInstBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1AcknowledgedClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1SampledClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkSentCt1ReceivedClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceivedClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysUnsampledClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedNoHeaderReceivedClPlacedBudget
import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
import LibsignalBinary.Proofs.SpqrV1.Auth.AuthEncodeMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.BytesMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergePart2CodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderClPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderClPlaced
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.SpqrV1.Varint.VarintCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym

/-!
# Budget-Threaded Placed Chunked `MessageMerge` & Closed `decode_state`

Closed code-and-rodata-loaded budget contracts for the 11 `V1State::Chunked` protobuf `merge`
blocks (Blocks 300..310), `V1State::merge` (Block 298), and `spqr::decode_state` (Block 325) under
`CliGhostAllocHooks M A lim gh`, lifted to `spqrSendPlacedProg` and `spqrRecvPlacedProg`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInstBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement extract_withLsCodeLoaded
   instIsLsBlockProg_261 instIsLsBlockProg_263 instIsLsBlockProg_290 instIsLsBlockProg_291
   instIsLsBlockProg_295 instIsLsBlockProg_311 instIsLsBlockProg_312
   libsignalMutatedBlocks libsignalSessionExterns libsignalSessionLib
   ls_blockPlacement_base ls_externAt?_blockProgram_eq_of_externs_eq lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchet
  (extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
   withLsCodeRoLoaded)
open CryptoVerification.RecordCodecs.Placed (instIsLsBlockProg_257)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots (lsRngFillSym trTrapExternsPlaced)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (instIsLsBlockProg_296 instIsLsBlockProg_297
   instIsLsBlockProg_302 instIsLsBlockProg_306 instIsLsBlockProg_308)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2
  (instIsLsBlockProg_300 instIsLsBlockProg_301 instIsLsBlockProg_303
   instIsLsBlockProg_304 instIsLsBlockProg_305 instIsLsBlockProg_307
   instIsLsBlockProg_309 instIsLsBlockProg_310)
open CryptoVerification.SpqrV1.Top.DecodeState (canonicalV1InnerHeap)
open CryptoVerification.SpqrV1.Top.Recv (spqrRecvPlacedProg)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget (spqrSendPlacedProg)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudget
  (cliSpqrDecodeState_of_chunked_cl cliSpqrDecodeState_recv_of_chunked_ok
   cliSpqrDecodeState_recv_trTrap_of_chunked_ok cliSpqrSend_decodeState_of_chunked_ok
   cliV1StateMerge_of_chunked_cl)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudgetAux
  (cliBytes_290_cl cliDrop_267_cl cliDrop_281_cl cliDrop_282_cl
   cliFrom_261_cl cliPushMerge_257_cl cliSkip_263_cl cliVarint_291_cl)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrMessageMergeLeavesPlacedInstBudget
  (cliAuthMergeBase_blockProgram_cro cliBytesExact_290_cro cliPolyDecoderMerge_296_cro
   cliPolyEncoderMerge_297_cro cliUnchunkedCt1SentMerge_312_cro
   cliUnchunkedEkSentCt1ReceivedMerge_311_cro)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (authMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1AcknowledgedClPlacedBudget
  (chunkedCt1Acknowledged_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedClPlacedBudget
  (chunkedCt1Received_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledClPlacedBudget
  (chunkedCt1Sampled_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledClPlacedBudget
  (chunked_ct2_sampled_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (chunkedCt1AcknowledgedMergeSpec chunkedCt1ReceivedMergeSpec chunkedCt1SampledMergeSpec
   chunkedEkSentCt1ReceivedMergeSpec decodeErrorPushMergeBudgetSpec
   unchunkedCt1SentMergeSpec unchunkedEkSentCt1ReceivedMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1SampledClPlacedBudget
  (chunked_ek_received_ct1_sampled_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkSentCt1ReceivedClPlacedBudget
  (chunkedEkSentCt1Received_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceivedClPlacedBudget
  (chunked_header_received_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentClPlacedBudget
  (chunked_header_sent_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (chunkedCt2SampledMergeSpec chunkedEkReceivedCt1SampledMergeSpec chunkedHeaderReceivedMergeSpec
   chunkedHeaderSentMergeSpec chunkedKeysSampledMergeSpec chunkedKeysUnsampledMergeSpec
   chunkedNoHeaderReceivedMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledClPlacedBudget
  (chunked_keys_sampled_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysUnsampledClPlacedBudget
  (chunked_keys_unsampled_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedNoHeaderReceivedClPlacedBudget
  (chunked_no_header_received_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (bytesMerge3RawBudgetSpec polyDecoderMergeSpec polyEncoderMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget (v1StateMergePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (decodeStatePlacedSpecX spqrDecodeStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

/-! ### Private Own-Block ↔ Caller-Block Transfer Helpers -/

private class IsLsValidBlock [LibsignalPlacement] (j : Nat) : Prop where
  lt_blocks : j < 624
  not_mutated : (j ∈ libsignalMutatedBlocks) = false
  externs_eq : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns

private instance [LibsignalPlacement] : IsLsValidBlock 257 :=
  ⟨by decide, by decide, (instIsLsBlockProg_257 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : IsLsValidBlock 261 :=
  ⟨by decide, by decide, (instIsLsBlockProg_261 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : IsLsValidBlock 263 :=
  ⟨by decide, by decide, (instIsLsBlockProg_263 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : IsLsValidBlock 290 :=
  ⟨by decide, by decide, (instIsLsBlockProg_290 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : IsLsValidBlock 291 :=
  ⟨by decide, by decide, (instIsLsBlockProg_291 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : IsLsValidBlock 295 :=
  ⟨by decide, by decide, (instIsLsBlockProg_295 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : IsLsValidBlock 296 :=
  ⟨by decide, by decide, (instIsLsBlockProg_296 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : IsLsValidBlock 297 :=
  ⟨by decide, by decide, (instIsLsBlockProg_297 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : IsLsValidBlock 300 :=
  ⟨by decide, by decide, (instIsLsBlockProg_300 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : IsLsValidBlock 301 :=
  ⟨by decide, by decide, (instIsLsBlockProg_301 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : IsLsValidBlock 302 :=
  ⟨by decide, by decide, (instIsLsBlockProg_302 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : IsLsValidBlock 303 :=
  ⟨by decide, by decide, (instIsLsBlockProg_303 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : IsLsValidBlock 304 :=
  ⟨by decide, by decide, (instIsLsBlockProg_304 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : IsLsValidBlock 305 :=
  ⟨by decide, by decide, (instIsLsBlockProg_305 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : IsLsValidBlock 306 :=
  ⟨by decide, by decide, (instIsLsBlockProg_306 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : IsLsValidBlock 307 :=
  ⟨by decide, by decide, (instIsLsBlockProg_307 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : IsLsValidBlock 308 :=
  ⟨by decide, by decide, (instIsLsBlockProg_308 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : IsLsValidBlock 309 :=
  ⟨by decide, by decide, (instIsLsBlockProg_309 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : IsLsValidBlock 310 :=
  ⟨by decide, by decide, (instIsLsBlockProg_310 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : IsLsValidBlock 311 :=
  ⟨by decide, by decide, (instIsLsBlockProg_311 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : IsLsValidBlock 312 :=
  ⟨by decide, by decide, (instIsLsBlockProg_312 (fun _ => none)).externs_eq⟩

private theorem lift_cro_of_own [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hj : IsLsValidBlock j] {spec : Spec α}
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j)
      (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok callerProg (lsmpl.base j) (withLsCodeRoLoaded lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hfr0, _⟩ := extract_withLsCodeRoLoaded hpre
  have hQL : (libsignalSessionLib.blockProgram lsmpl j H).CodeLoaded s0.mem :=
    hfr0.1 j hj.lt_blocks hj.not_mutated H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, (libsignalSessionLib.blockProgram lsmpl j H).externAt? pc = callerProg.externAt? pc :=
    fun pc => by
      rw [hcaller.eq_blockProgram,
        ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
          (hj.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : (libsignalSessionLib.blockProgram lsmpl j H).svc = callerProg.svc := by
    rw [hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

private theorem lift_cl_to_cl [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hj : IsLsValidBlock j] {spec : Spec α}
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j)
      (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok callerProg (lsmpl.base j) (withLsCodeLoaded lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcl0, _⟩ := extract_withLsCodeLoaded hpre
  have hQL : (libsignalSessionLib.blockProgram lsmpl j H).CodeLoaded s0.mem :=
    hcl0 j hj.lt_blocks hj.not_mutated H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, (libsignalSessionLib.blockProgram lsmpl j H).externAt? pc = callerProg.externAt? pc :=
    fun pc => by
      rw [hcaller.eq_blockProgram,
        ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
          (hj.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : (libsignalSessionLib.blockProgram lsmpl j H).svc = callerProg.svc := by
    rw [hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

private theorem lift_cl_to_cro [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hj : IsLsValidBlock j] {spec : Spec α}
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j)
      (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok callerProg (lsmpl.base j) (withLsCodeRoLoaded lsmpl spec) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded (lift_cl_to_cl hcallee)

private theorem own_of_blk_cro [LibsignalPlacement] {α : Type}
    {blkProg : Program} {i : Nat} {H : LibsignalHooks}
    [hprog : IsLsBlockProg blkProg i H] {spec : Spec α}
    (h : subroutine_ok blkProg (libsignalSessionLib.blockPlacement lsmpl i).base
      (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl i H) (lsmpl.base i)
      (withLsCodeRoLoaded lsmpl spec) := by
  rw [← hprog.eq_blockProgram, ← ls_blockPlacement_base lsmpl i]
  exact h

/-! ### 1. Closed Own-Block `withLsCodeRoLoaded` Contracts (`Blocks 300..310`) -/

theorem cliChunkedCt1SampledMerge_300_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics ext))
      (lsmpl.base 300) (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)) :=
  own_of_blk_cro (chunkedCt1Sampled_merge_cl_placed_ok_of_contracts
    (lift_cl_to_cro (cliFrom_261_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliPushMerge_257_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliVarint_291_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliSkip_263_cl mmpl gh W hA hExt))
    (lift_cro_of_own (cliUnchunkedCt1SentMerge_312_cro mmpl gh W hA hExt))
    (lift_cro_of_own (cliPolyEncoderMerge_297_cro mmpl gh W hA hExt))
    (lift_cro_of_own (cliPolyDecoderMerge_296_cro mmpl gh W hA hExt)))

theorem cliChunkedCt2SampledMerge_301_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics ext))
      (lsmpl.base 301) (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A lim)) :=
  own_of_blk_cro (chunked_ct2_sampled_merge_cl_placed_ok_of_contracts
    (lift_cl_to_cro (cliFrom_261_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliPushMerge_257_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliVarint_291_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliSkip_263_cl mmpl gh W hA hExt))
    (lift_cro_of_own (cliAuthMergeBase_blockProgram_cro mmpl gh W hA hExt))
    (lift_cro_of_own (cliPolyEncoderMerge_297_cro mmpl gh W hA hExt)))

theorem cliChunkedHeaderSentMerge_302_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics ext))
      (lsmpl.base 302) (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)) :=
  own_of_blk_cro (chunked_header_sent_merge_cl_placed_ok_of_contracts
    (lift_cl_to_cro (cliFrom_261_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliPushMerge_257_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliVarint_291_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliSkip_263_cl mmpl gh W hA hExt))
    (lift_cro_of_own (cliBytes_290_cl mmpl gh W hA hExt))
    (lift_cro_of_own (cliAuthMergeBase_blockProgram_cro mmpl gh W hA hExt))
    (lift_cro_of_own (cliPolyEncoderMerge_297_cro mmpl gh W hA hExt))
    (lift_cro_of_own (cliPolyDecoderMerge_296_cro mmpl gh W hA hExt)))

theorem cliChunkedCt1ReceivedMerge_303_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics ext))
      (lsmpl.base 303) (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)) :=
  own_of_blk_cro (chunkedCt1Received_merge_cl_placed_ok_of_contracts
    (lift_cl_to_cro (cliFrom_261_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliPushMerge_257_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliVarint_291_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliSkip_263_cl mmpl gh W hA hExt))
    (lift_cro_of_own (cliUnchunkedEkSentCt1ReceivedMerge_311_cro mmpl gh W hA hExt))
    (lift_cro_of_own (cliPolyEncoderMerge_297_cro mmpl gh W hA hExt)))

theorem cliChunkedKeysSampledMerge_304_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim)) :=
  own_of_blk_cro (chunked_keys_sampled_merge_cl_placed_ok_of_contracts
    (lift_cl_to_cro (cliFrom_261_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliPushMerge_257_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliVarint_291_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliSkip_263_cl mmpl gh W hA hExt))
    (lift_cro_of_own (cliBytes_290_cl mmpl gh W hA hExt))
    (lift_cro_of_own (cliAuthMergeBase_blockProgram_cro mmpl gh W hA hExt))
    (lift_cro_of_own (cliPolyEncoderMerge_297_cro mmpl gh W hA hExt)))

theorem cliChunkedKeysUnsampledMerge_305_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)) :=
  own_of_blk_cro (chunked_keys_unsampled_merge_cl_placed_ok_of_contracts
    (lift_cl_to_cro (cliFrom_261_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliPushMerge_257_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliVarint_291_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliSkip_263_cl mmpl gh W hA hExt))
    (lift_cro_of_own (cliAuthMergeBase_blockProgram_cro mmpl gh W hA hExt)))

theorem cliChunkedHeaderReceivedMerge_306_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext))
      (lsmpl.base 306) (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim)) :=
  own_of_blk_cro (chunked_header_received_merge_cl_placed_ok_of_contracts
    (lift_cl_to_cro (cliFrom_261_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliPushMerge_257_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliVarint_291_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliSkip_263_cl mmpl gh W hA hExt))
    (lift_cro_of_own (cliAuthMergeBase_blockProgram_cro mmpl gh W hA hExt))
    (lift_cro_of_own (cliBytes_290_cl mmpl gh W hA hExt))
    (lift_cro_of_own (cliPolyDecoderMerge_296_cro mmpl gh W hA hExt)))

theorem cliChunkedCt1AcknowledgedMerge_307_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)) :=
  own_of_blk_cro (chunkedCt1Acknowledged_merge_cl_placed_ok_of_contracts
    (lift_cl_to_cro (cliFrom_261_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliPushMerge_257_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliVarint_291_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliSkip_263_cl mmpl gh W hA hExt))
    (lift_cro_of_own (cliUnchunkedCt1SentMerge_312_cro mmpl gh W hA hExt))
    (lift_cro_of_own (cliPolyDecoderMerge_296_cro mmpl gh W hA hExt)))

theorem cliChunkedNoHeaderReceivedMerge_308_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics ext))
      (lsmpl.base 308) (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A lim)) :=
  own_of_blk_cro (chunked_no_header_received_merge_cl_placed_ok_of_contracts
    (lift_cl_to_cro (cliFrom_261_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliPushMerge_257_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliVarint_291_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliSkip_263_cl mmpl gh W hA hExt))
    (lift_cro_of_own (cliAuthMergeBase_blockProgram_cro mmpl gh W hA hExt))
    (lift_cro_of_own (cliPolyDecoderMerge_296_cro mmpl gh W hA hExt)))

theorem cliChunkedEkSentCt1ReceivedMerge_309_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics ext))
      (lsmpl.base 309) (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)) :=
  own_of_blk_cro (chunkedEkSentCt1Received_merge_cl_placed_ok_of_contracts
    (lift_cl_to_cro (cliFrom_261_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliPushMerge_257_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliVarint_291_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliSkip_263_cl mmpl gh W hA hExt))
    (lift_cro_of_own (cliUnchunkedEkSentCt1ReceivedMerge_311_cro mmpl gh W hA hExt))
    (lift_cro_of_own (cliPolyDecoderMerge_296_cro mmpl gh W hA hExt)))

theorem cliChunkedEkReceivedCt1SampledMerge_310_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics ext))
      (lsmpl.base 310) (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim)) :=
  own_of_blk_cro (chunked_ek_received_ct1_sampled_merge_cl_placed_ok_of_contracts
    (lift_cl_to_cro (cliFrom_261_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliPushMerge_257_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliVarint_291_cl mmpl gh W hA hExt))
    (lift_cl_to_cro (cliSkip_263_cl mmpl gh W hA hExt))
    (lift_cro_of_own (cliBytes_290_cl mmpl gh W hA hExt))
    (lift_cro_of_own (cliAuthMergeBase_blockProgram_cro mmpl gh W hA hExt))
    (lift_cro_of_own (cliPolyEncoderMerge_297_cro mmpl gh W hA hExt)))

/-! ### 2. Closed `V1State::merge` (`Block 298`) & `spqr::decode_state` (`Block 325`) -/

/-- Closed own-block `V1State::merge` (`Block 298`) contract under explicit 2-placement `hExt`. -/
theorem cliV1StateMerge_closed_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext))
      (lsmpl.base 298) (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec A lim)) :=
  cliV1StateMerge_of_chunked_cl mmpl gh W hA hExt
    (cliChunkedCt1SampledMerge_300_cl mmpl gh W hA hExt)
    (cliChunkedCt2SampledMerge_301_cl mmpl gh W hA hExt)
    (cliChunkedHeaderSentMerge_302_cl mmpl gh W hA hExt)
    (cliChunkedCt1ReceivedMerge_303_cl mmpl gh W hA hExt)
    (cliChunkedKeysSampledMerge_304_cl mmpl gh W hA hExt)
    (cliChunkedKeysUnsampledMerge_305_cl mmpl gh W hA hExt)
    (cliChunkedHeaderReceivedMerge_306_cl mmpl gh W hA hExt)
    (cliChunkedCt1AcknowledgedMerge_307_cl mmpl gh W hA hExt)
    (cliChunkedNoHeaderReceivedMerge_308_cl mmpl gh W hA hExt)
    (cliChunkedEkSentCt1ReceivedMerge_309_cl mmpl gh W hA hExt)
    (cliChunkedEkReceivedCt1SampledMerge_310_cl mmpl gh W hA hExt)

/-- Closed own-block `spqr::decode_state` (`Block 325`) contract under explicit 2-placement `hExt`. -/
theorem cliSpqrDecodeState_closed_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 325 (Rust.withPanics ext))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (decodeStatePlacedSpecX canonicalV1InnerHeap A lim)) :=
  cliSpqrDecodeState_of_chunked_cl mmpl gh W hA hExt
    (cliBytesExact_290_cro mmpl gh W hA hExt)
    (cliChunkedCt1SampledMerge_300_cl mmpl gh W hA hExt)
    (cliChunkedCt2SampledMerge_301_cl mmpl gh W hA hExt)
    (cliChunkedHeaderSentMerge_302_cl mmpl gh W hA hExt)
    (cliChunkedCt1ReceivedMerge_303_cl mmpl gh W hA hExt)
    (cliChunkedKeysSampledMerge_304_cl mmpl gh W hA hExt)
    (cliChunkedKeysUnsampledMerge_305_cl mmpl gh W hA hExt)
    (cliChunkedHeaderReceivedMerge_306_cl mmpl gh W hA hExt)
    (cliChunkedCt1AcknowledgedMerge_307_cl mmpl gh W hA hExt)
    (cliChunkedNoHeaderReceivedMerge_308_cl mmpl gh W hA hExt)
    (cliChunkedEkSentCt1ReceivedMerge_309_cl mmpl gh W hA hExt)
    (cliChunkedEkReceivedCt1SampledMerge_310_cl mmpl gh W hA hExt)

/-- Closed `spqrSendPlacedProg ext` `decodeState_ok` contract under explicit 2-placement `hExt`. -/
theorem cliSpqrSend_decodeState_closed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (spqrDecodeStatePlacedSpec canonicalV1InnerHeap A lim)) :=
  cliSpqrSend_decodeState_of_chunked_ok mmpl gh W hA hExt
    (cliBytesExact_290_cro mmpl gh W hA hExt)
    (cliChunkedCt1SampledMerge_300_cl mmpl gh W hA hExt)
    (cliChunkedCt2SampledMerge_301_cl mmpl gh W hA hExt)
    (cliChunkedHeaderSentMerge_302_cl mmpl gh W hA hExt)
    (cliChunkedCt1ReceivedMerge_303_cl mmpl gh W hA hExt)
    (cliChunkedKeysSampledMerge_304_cl mmpl gh W hA hExt)
    (cliChunkedKeysUnsampledMerge_305_cl mmpl gh W hA hExt)
    (cliChunkedHeaderReceivedMerge_306_cl mmpl gh W hA hExt)
    (cliChunkedCt1AcknowledgedMerge_307_cl mmpl gh W hA hExt)
    (cliChunkedNoHeaderReceivedMerge_308_cl mmpl gh W hA hExt)
    (cliChunkedEkSentCt1ReceivedMerge_309_cl mmpl gh W hA hExt)
    (cliChunkedEkReceivedCt1SampledMerge_310_cl mmpl gh W hA hExt)

/-- Closed `spqrRecvPlacedProg ext` `decodeState_ok` contract under explicit 2-placement `hExt`. -/
theorem cliSpqrDecodeState_recv_closed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget.decodeStatePlacedSpecX
          canonicalV1InnerHeap A lim)) :=
  cliSpqrDecodeState_recv_of_chunked_ok mmpl gh W hA hExt
    (cliBytesExact_290_cro mmpl gh W hA hExt)
    (cliChunkedCt1SampledMerge_300_cl mmpl gh W hA hExt)
    (cliChunkedCt2SampledMerge_301_cl mmpl gh W hA hExt)
    (cliChunkedHeaderSentMerge_302_cl mmpl gh W hA hExt)
    (cliChunkedCt1ReceivedMerge_303_cl mmpl gh W hA hExt)
    (cliChunkedKeysSampledMerge_304_cl mmpl gh W hA hExt)
    (cliChunkedKeysUnsampledMerge_305_cl mmpl gh W hA hExt)
    (cliChunkedHeaderReceivedMerge_306_cl mmpl gh W hA hExt)
    (cliChunkedCt1AcknowledgedMerge_307_cl mmpl gh W hA hExt)
    (cliChunkedNoHeaderReceivedMerge_308_cl mmpl gh W hA hExt)
    (cliChunkedEkSentCt1ReceivedMerge_309_cl mmpl gh W hA hExt)
    (cliChunkedEkReceivedCt1SampledMerge_310_cl mmpl gh W hA hExt)

/-- Closed `spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))`
`decodeState_ok` contract. -/
theorem cliSpqrDecodeState_recv_trTrap_closed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget.decodeStatePlacedSpecX
          canonicalV1InnerHeap A lim)) := by
  have hTrExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym =
        cliGhostExterns gh (cliExternsPlaced mmpl W) sym :=
    fun sym hne => by simp [trTrapExternsPlaced, lsRngFillSym, trapAt, hne]
  exact cliSpqrDecodeState_recv_trTrap_of_chunked_ok mmpl gh W hA
    (cliBytesExact_290_cro mmpl gh W hA hTrExt)
    (cliChunkedCt1SampledMerge_300_cl mmpl gh W hA hTrExt)
    (cliChunkedCt2SampledMerge_301_cl mmpl gh W hA hTrExt)
    (cliChunkedHeaderSentMerge_302_cl mmpl gh W hA hTrExt)
    (cliChunkedCt1ReceivedMerge_303_cl mmpl gh W hA hTrExt)
    (cliChunkedKeysSampledMerge_304_cl mmpl gh W hA hTrExt)
    (cliChunkedKeysUnsampledMerge_305_cl mmpl gh W hA hTrExt)
    (cliChunkedHeaderReceivedMerge_306_cl mmpl gh W hA hTrExt)
    (cliChunkedCt1AcknowledgedMerge_307_cl mmpl gh W hA hTrExt)
    (cliChunkedNoHeaderReceivedMerge_308_cl mmpl gh W hA hTrExt)
    (cliChunkedEkSentCt1ReceivedMerge_309_cl mmpl gh W hA hTrExt)
    (cliChunkedEkReceivedCt1SampledMerge_310_cl mmpl gh W hA hTrExt)

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInstBudget
