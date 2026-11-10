/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInst
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1AcknowledgedClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1SampledClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkSentCt1ReceivedClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceivedClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysUnsampledClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedNoHeaderReceivedClPlaced
import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
import LibsignalBinary.Proofs.SpqrV1.Auth.AuthEncodeMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.BytesMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.SpqrV1.Varint.VarintCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym

/-!
# Placed Chunked Message-Merge Instantiations

Code-and-rodata-loaded (`withLsCodeRoLoaded lsmpl`) own-block contracts for the 11
`V1State::Chunked` protobuf `merge` blocks (Blocks 300..310) under `[CliSpqrExt W ext]`, together
with `blkPC_298`-rebased caller corollaries for `V1State::merge`.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInst

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (LibsignalPlacement LibsignalHooks IsLsBlockProg lsmpl libsignalSessionLib
   libsignalSessionExterns libsignalMutatedBlocks withLsCodeLoaded
   ls_blockPlacement_base ls_externAt?_blockProgram_eq_of_externs_eq
   instIsLsBlockProg_261 instIsLsBlockProg_263 instIsLsBlockProg_290
   instIsLsBlockProg_291 instIsLsBlockProg_295 instIsLsBlockProg_311
   instIsLsBlockProg_312)
open CryptoVerification.RecordCodecs.Placed (instIsLsBlockProg_257)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli (CliSpqrExt)
open CryptoVerification.E2E.HooksE (A0)
open CryptoVerification.LibsignalTripleRatchet
  (withLsCodeRoLoaded extract_withLsCodeRoLoaded
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
   decodeErrorFromSpec decodeErrorPushSpec)
open CryptoVerification.SpqrV1.Varint
  (skipField3Spec decodeVarint2Spec)
open CryptoVerification.SpqrV1.Prost.BytesMerge
  (bytesMerge3RawSpec)
open CryptoVerification.SpqrV1.Auth
  (authMergeSpec)
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
  (unchunkedCt1SentMergeSpec unchunkedEkSentCt1ReceivedMergeSpec)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (polyDecoderMergeSpec polyEncoderMergeSpec
   chunkedCt1SampledMergeSpec chunkedCt2SampledMergeSpec
   chunkedHeaderSentMergeSpec chunkedCt1ReceivedMergeSpec
   chunkedKeysSampledMergeSpec chunkedKeysUnsampledMergeSpec
   chunkedHeaderReceivedMergeSpec chunkedCt1AcknowledgedMergeSpec
   chunkedNoHeaderReceivedMergeSpec chunkedEkSentCt1ReceivedMergeSpec
   chunkedEkReceivedCt1SampledMergeSpec
   chunkedCt1Sampled_merge_cl_placed_ok_of_contracts
   chunked_ct2_sampled_merge_cl_placed_ok_of_contracts
   chunked_header_sent_merge_cl_placed_ok_of_contracts
   chunkedCt1Received_merge_cl_placed_ok_of_contracts
   chunked_keys_sampled_merge_cl_placed_ok_of_contracts
   chunked_keys_unsampled_merge_cl_placed_ok_of_contracts
   chunked_header_received_merge_cl_placed_ok_of_contracts
   chunkedCt1Acknowledged_merge_cl_placed_ok_of_contracts
   chunked_no_header_received_merge_cl_placed_ok_of_contracts
   chunkedEkSentCt1Received_merge_cl_placed_ok_of_contracts
   chunked_ek_received_ct1_sampled_merge_cl_placed_ok_of_contracts
   instIsLsBlockProg_296 instIsLsBlockProg_297
   instIsLsBlockProg_302 instIsLsBlockProg_306 instIsLsBlockProg_308)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2
  (blkPC_298 blkPl_298 instIsLsBlockProg_298
   instIsLsBlockProg_300 instIsLsBlockProg_301 instIsLsBlockProg_303
   instIsLsBlockProg_304 instIsLsBlockProg_305 instIsLsBlockProg_307
   instIsLsBlockProg_309 instIsLsBlockProg_310)

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

private theorem lift_cl_of_own [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [IsLsValidBlock j] {spec : Spec α}
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j)
      (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok callerProg (lsmpl.base j) (withLsCodeRoLoaded lsmpl spec) :=
  lift_cro_of_own (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hcallee)

private theorem own_of_blk_cro [LibsignalPlacement] {α : Type}
    {blkProg : Program} {i : Nat} {H : LibsignalHooks}
    [hprog : IsLsBlockProg blkProg i H] {spec : Spec α}
    (h : subroutine_ok blkProg (libsignalSessionLib.blockPlacement lsmpl i).base
      (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl i H) (lsmpl.base i)
      (withLsCodeRoLoaded lsmpl spec) := by
  rw [← hprog.eq_blockProgram, ← ls_blockPlacement_base lsmpl i]
  exact h

/-! ### 1. Own-Block Code+Rodata-Loaded Theorems (`Blocks 300..310`) -/

theorem cliChunkedCt1SampledMerge_300_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (hUc312 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 312 (Rust.withPanics ext))
      (lsmpl.base 312) (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A0)))
    (hPolyEnc : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A0)))
    (hPolyDec : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A0))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics ext))
      (lsmpl.base 300) (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A0)) :=
  own_of_blk_cro (chunkedCt1Sampled_merge_cl_placed_ok_of_contracts
    (lift_cl_of_own hFrom) (lift_cl_of_own hPush) (lift_cl_of_own hVarint) (lift_cl_of_own hSkip)
    (lift_cro_of_own hUc312) (lift_cro_of_own hPolyEnc) (lift_cro_of_own hPolyDec))

theorem cliChunkedCt2SampledMerge_301_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (hAuth : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A0)))
    (hPolyEnc : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A0))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics ext))
      (lsmpl.base 301) (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A0)) :=
  own_of_blk_cro (chunked_ct2_sampled_merge_cl_placed_ok_of_contracts
    (lift_cl_of_own hFrom) (lift_cl_of_own hPush) (lift_cl_of_own hVarint) (lift_cl_of_own hSkip)
    (lift_cro_of_own hAuth) (lift_cro_of_own hPolyEnc))

theorem cliChunkedHeaderSentMerge_302_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A0)))
    (hAuth : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A0)))
    (hPolyEnc : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A0)))
    (hPolyDec : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A0))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics ext))
      (lsmpl.base 302) (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A0)) :=
  own_of_blk_cro (chunked_header_sent_merge_cl_placed_ok_of_contracts
    (lift_cl_of_own hFrom) (lift_cl_of_own hPush) (lift_cl_of_own hVarint) (lift_cl_of_own hSkip)
    (lift_cro_of_own hBytes) (lift_cro_of_own hAuth)
    (lift_cro_of_own hPolyEnc) (lift_cro_of_own hPolyDec))

theorem cliChunkedCt1ReceivedMerge_303_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (hUc311 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 311 (Rust.withPanics ext))
      (lsmpl.base 311) (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A0)))
    (hPolyEnc : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A0))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics ext))
      (lsmpl.base 303) (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A0)) :=
  own_of_blk_cro (chunkedCt1Received_merge_cl_placed_ok_of_contracts
    (lift_cl_of_own hFrom) (lift_cl_of_own hPush) (lift_cl_of_own hVarint) (lift_cl_of_own hSkip)
    (lift_cro_of_own hUc311) (lift_cro_of_own hPolyEnc))

theorem cliChunkedKeysSampledMerge_304_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A0)))
    (hAuth : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A0)))
    (hPolyEnc : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A0))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A0)) :=
  own_of_blk_cro (chunked_keys_sampled_merge_cl_placed_ok_of_contracts
    (lift_cl_of_own hFrom) (lift_cl_of_own hPush) (lift_cl_of_own hVarint) (lift_cl_of_own hSkip)
    (lift_cro_of_own hBytes) (lift_cro_of_own hAuth) (lift_cro_of_own hPolyEnc))

theorem cliChunkedKeysUnsampledMerge_305_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (hAuth : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A0))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A0)) :=
  own_of_blk_cro (chunked_keys_unsampled_merge_cl_placed_ok_of_contracts
    (lift_cl_of_own hFrom) (lift_cl_of_own hPush) (lift_cl_of_own hVarint) (lift_cl_of_own hSkip)
    (lift_cro_of_own hAuth))

theorem cliChunkedHeaderReceivedMerge_306_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A0)))
    (hAuth : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A0)))
    (hPolyDec : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A0))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext))
      (lsmpl.base 306) (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A0)) :=
  own_of_blk_cro (chunked_header_received_merge_cl_placed_ok_of_contracts
    (lift_cl_of_own hFrom) (lift_cl_of_own hPush) (lift_cl_of_own hVarint) (lift_cl_of_own hSkip)
    (lift_cro_of_own hAuth) (lift_cro_of_own hBytes) (lift_cro_of_own hPolyDec))

theorem cliChunkedCt1AcknowledgedMerge_307_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (hUc312 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 312 (Rust.withPanics ext))
      (lsmpl.base 312) (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A0)))
    (hPolyDec : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A0))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A0)) :=
  own_of_blk_cro (chunkedCt1Acknowledged_merge_cl_placed_ok_of_contracts
    (lift_cl_of_own hFrom) (lift_cl_of_own hPush) (lift_cl_of_own hVarint) (lift_cl_of_own hSkip)
    (lift_cro_of_own hUc312) (lift_cro_of_own hPolyDec))

theorem cliChunkedNoHeaderReceivedMerge_308_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (hAuth : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A0)))
    (hPolyDec : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A0))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics ext))
      (lsmpl.base 308) (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A0)) :=
  own_of_blk_cro (chunked_no_header_received_merge_cl_placed_ok_of_contracts
    (lift_cl_of_own hFrom) (lift_cl_of_own hPush) (lift_cl_of_own hVarint) (lift_cl_of_own hSkip)
    (lift_cro_of_own hAuth) (lift_cro_of_own hPolyDec))

theorem cliChunkedEkSentCt1ReceivedMerge_309_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (hUc311 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 311 (Rust.withPanics ext))
      (lsmpl.base 311) (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A0)))
    (hPolyDec : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A0))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics ext))
      (lsmpl.base 309) (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A0)) :=
  own_of_blk_cro (chunkedEkSentCt1Received_merge_cl_placed_ok_of_contracts
    (lift_cl_of_own hFrom) (lift_cl_of_own hPush) (lift_cl_of_own hVarint) (lift_cl_of_own hSkip)
    (lift_cro_of_own hUc311) (lift_cro_of_own hPolyDec))

theorem cliChunkedEkReceivedCt1SampledMerge_310_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A0)))
    (hAuth : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A0)))
    (hPolyEnc : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A0))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics ext))
      (lsmpl.base 310) (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A0)) :=
  own_of_blk_cro (chunked_ek_received_ct1_sampled_merge_cl_placed_ok_of_contracts
    (lift_cl_of_own hFrom) (lift_cl_of_own hPush) (lift_cl_of_own hVarint) (lift_cl_of_own hSkip)
    (lift_cro_of_own hBytes) (lift_cro_of_own hAuth) (lift_cro_of_own hPolyEnc))

/-! ### 2. `blkPC_298` (`V1State::merge`) Caller Corollaries -/

theorem cliChunkedKeysUnsampledMerge_at_298 [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (hAuth : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A0))) :
    subroutine_ok ((blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (lsmpl.base 305)
      (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A0)) :=
  lift_cro_of_own (cliChunkedKeysUnsampledMerge_305_cl W hFrom hPush hVarint hSkip hAuth)

theorem cliChunkedKeysSampledMerge_at_298 [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A0)))
    (hAuth : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A0)))
    (hPolyEnc : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A0))) :
    subroutine_ok ((blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (lsmpl.base 304)
      (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A0)) :=
  lift_cro_of_own (cliChunkedKeysSampledMerge_304_cl W hFrom hPush hVarint hSkip hBytes hAuth hPolyEnc)

theorem cliChunkedHeaderSentMerge_at_298 [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A0)))
    (hAuth : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A0)))
    (hPolyEnc : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A0)))
    (hPolyDec : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A0))) :
    subroutine_ok ((blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (lsmpl.base 302)
      (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A0)) :=
  lift_cro_of_own (cliChunkedHeaderSentMerge_302_cl W hFrom hPush hVarint hSkip hBytes hAuth hPolyEnc hPolyDec)

theorem cliChunkedCt1ReceivedMerge_at_298 [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (hUc311 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 311 (Rust.withPanics ext))
      (lsmpl.base 311) (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A0)))
    (hPolyEnc : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A0))) :
    subroutine_ok ((blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (lsmpl.base 303)
      (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A0)) :=
  lift_cro_of_own (cliChunkedCt1ReceivedMerge_303_cl W hFrom hPush hVarint hSkip hUc311 hPolyEnc)

theorem cliChunkedEkSentCt1ReceivedMerge_at_298 [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (hUc311 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 311 (Rust.withPanics ext))
      (lsmpl.base 311) (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A0)))
    (hPolyDec : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A0))) :
    subroutine_ok ((blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (lsmpl.base 309)
      (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A0)) :=
  lift_cro_of_own (cliChunkedEkSentCt1ReceivedMerge_309_cl W hFrom hPush hVarint hSkip hUc311 hPolyDec)

theorem cliChunkedNoHeaderReceivedMerge_at_298 [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (hAuth : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A0)))
    (hPolyDec : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A0))) :
    subroutine_ok ((blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (lsmpl.base 308)
      (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A0)) :=
  lift_cro_of_own (cliChunkedNoHeaderReceivedMerge_308_cl W hFrom hPush hVarint hSkip hAuth hPolyDec)

theorem cliChunkedHeaderReceivedMerge_at_298 [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A0)))
    (hAuth : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A0)))
    (hPolyDec : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A0))) :
    subroutine_ok ((blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (lsmpl.base 306)
      (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A0)) :=
  lift_cro_of_own (cliChunkedHeaderReceivedMerge_306_cl W hFrom hPush hVarint hSkip hBytes hAuth hPolyDec)

theorem cliChunkedCt1SampledMerge_at_298 [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (hUc312 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 312 (Rust.withPanics ext))
      (lsmpl.base 312) (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A0)))
    (hPolyEnc : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A0)))
    (hPolyDec : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A0))) :
    subroutine_ok ((blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (lsmpl.base 300)
      (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A0)) :=
  lift_cro_of_own (cliChunkedCt1SampledMerge_300_cl W hFrom hPush hVarint hSkip hUc312 hPolyEnc hPolyDec)

theorem cliChunkedEkReceivedCt1SampledMerge_at_298 [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A0)))
    (hAuth : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A0)))
    (hPolyEnc : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A0))) :
    subroutine_ok ((blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (lsmpl.base 310)
      (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A0)) :=
  lift_cro_of_own (cliChunkedEkReceivedCt1SampledMerge_310_cl W hFrom hPush hVarint hSkip hBytes hAuth hPolyEnc)

theorem cliChunkedCt1AcknowledgedMerge_at_298 [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (hUc312 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 312 (Rust.withPanics ext))
      (lsmpl.base 312) (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A0)))
    (hPolyDec : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A0))) :
    subroutine_ok ((blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (lsmpl.base 307)
      (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A0)) :=
  lift_cro_of_own (cliChunkedCt1AcknowledgedMerge_307_cl W hFrom hPush hVarint hSkip hUc312 hPolyDec)

theorem cliChunkedCt2SampledMerge_at_298 [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (hAuth : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A0)))
    (hPolyEnc : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A0))) :
    subroutine_ok ((blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (lsmpl.base 301)
      (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A0)) :=
  lift_cro_of_own (cliChunkedCt2SampledMerge_301_cl W hFrom hPush hVarint hSkip hAuth hPolyEnc)

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInst
