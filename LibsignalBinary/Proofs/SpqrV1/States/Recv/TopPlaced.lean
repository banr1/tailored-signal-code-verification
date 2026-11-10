/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlaced
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.AddChunkCl1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.LeavesTopPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2ClPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedRecvEkPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart10Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmKeysSampled2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceived2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple3Placed

/-!
# `<States>::recv` (Block `332`): Relocatable Top-Level Assembly

Combines all relocatable arms of `<States>::recv` (Block `332`, `4,884` instructions) to prove
`states_recv_placed_ok_x` and `states_recv_placed_ok_x_closed`, plus `.rodata` placement witnesses.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.Recv.Top

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.DecodedMessage
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.Recv
open LibsignalBinary.Proofs.SpqrV1.States.Recv

/-! ## Per-Variant Relocatable Dispatch (`states_recv_variant_placed_ext` / `states_recv_variant_placed_x`) -/

/-- Unified per-variant relocatable `subroutine_ok` contract for `<States>::recv` (Block `332`)
on `lsProg_332 (Rust.withPanics ext)` with `withLsCodeRoLoaded lsmpl`. -/
theorem states_recv_variant_placed_ext [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : StatesRecvPlacedContracts A F K ext)
    (st : States spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl (statesRecvVariantPlacedSpec A F K st msg)) := by
  cases st with
  | keysUnsampled s =>
      exact Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
        (states_recv_keysUnsampled_placed_ok_ext A F K ext hC s msg)
  | keysSampled s =>
      exact Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
        (states_recv_keysSampled_placed_ok_ext A F K ext hC s msg)
  | headerSent s =>
      exact states_recv_headerSent_placed_ok_ext A F K ext hC s msg
  | ct1Received s =>
      exact Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
        (states_recv_ct1Received_placed_ok_ext A F K ext hC s msg)
  | ekSentCt1Received s =>
      exact states_recv_ekSentCt1Received_placed_ok_ext A F K ext hC s msg
  | noHeaderReceived s =>
      exact states_recv_noHeaderReceived_placed_ok_ext A F K ext hC s msg
  | headerReceived s =>
      exact Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
        (states_recv_headerReceived_placed_ok_ext A F K ext hC s msg)
  | ct1Sampled s =>
      exact states_recv_ct1Sampled_placed_ok_ext A F K ext hC s msg
  | ekReceivedCt1Sampled s =>
      exact Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
        (states_recv_ekReceivedCt1Sampled_placed_ok_ext A F K ext hC s msg)
  | ct1Acknowledged s =>
      exact states_recv_ct1Acknowledged_placed_ok_ext A F K ext hC s msg
  | ct2Sampled s =>
      exact Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
        (states_recv_ct2Sampled_placed_ok_ext A F K ext hC s msg)

/-- Unified per-variant relocatable `subroutine_ok` contract for `<States>::recv` (Block `332`)
on `libsignalSessionLib.blockProgram lsmpl 332 (Rust.withPanics ext)` with `withLsCodeRoLoaded lsmpl`. -/
theorem states_recv_variant_placed_x [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : StatesRecvPlacedContracts A F K ext)
    (st : States spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl (statesRecvVariantPlacedSpec A F K st msg)) :=
  ls_subroutine_ok_to_blockProgram (states_recv_variant_placed_ext A F K ext hC st msg)

/-! ## Top-Level Relocatable `<States>::recv` Contracts (`states_recv_placed_ok_ext` / `states_recv_placed_ok_x`) -/

theorem states_recv_placed_ok_ext_of_variants [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hvar : ∀ (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi),
      subroutine_ok (lsProg_332 (Rust.withPanics ext))
        (lsmpl.base 332)
        (withLsCodeRoLoaded lsmpl (statesRecvVariantPlacedSpec A F K st msg))) :
    StatesRecvPlacedOkExt A F K ext := by
  dsimp only [StatesRecvPlacedOkExt]
  refine subroutine_ok_outcome_intro fun ⟨outA, selfA, msgA, st, msg⟩ R s0 hpc hrun hpre hsp =>
    (hvar st msg).mono_outcome (outA, selfA, msgA) R s0 hpc hrun hpre hsp fun _ hout => hout

/-- Top-level relocatable `subroutine_ok` contract (`StatesRecvPlacedOkExt`) for
`<spqr::v1::chunked::states::States>::recv` (Block `332`, 4,884 instructions)
on `lsProg_332 (Rust.withPanics ext)` with `withLsCodeRoLoaded lsmpl`. -/
theorem states_recv_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : StatesRecvPlacedContracts A F K ext) :
    StatesRecvPlacedOkExt A F K ext :=
  states_recv_placed_ok_ext_of_variants A F K ext
    (states_recv_variant_placed_ext A F K ext hC)

theorem states_recv_placed_ok_x_of_ext [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (h : StatesRecvPlacedOkExt A F K ext) :
    StatesRecvPlacedOkX A F K ext :=
  ls_subroutine_ok_to_blockProgram h

/-- Top-level relocatable `subroutine_ok` contract (`StatesRecvPlacedOkX`) for
`<spqr::v1::chunked::states::States>::recv` (Block `332`, 4,884 instructions)
on `libsignalSessionLib.blockProgram lsmpl 332 (Rust.withPanics ext)` with `withLsCodeRoLoaded lsmpl`. -/
theorem states_recv_placed_ok_x [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : StatesRecvPlacedContracts A F K ext) :
    StatesRecvPlacedOkX A F K ext :=
  states_recv_placed_ok_x_of_ext (states_recv_placed_ok_ext A F K ext hC)

/-! ## Discharging All Leaf Contracts in `StatesRecvPlacedContracts` from `LeavesTopPlaced` -/

private theorem hookSat_sessionMemcpy_of_frameless {H : String → Option (State → State)}
    {sym : String} (hookStack : Nat) (h : HookSat H sym framelessMemcpySpec) :
    HookSat H sym (sessionMemcpySpec hookStack) := by
  refine ProofLib.HookSat.mono h fun ⟨dst, src, bs⟩ R s0 hpre =>
    ⟨(dst, src, bs), stackAt s0.sp hookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [sessionMemcpySpec, libcMemcpySpec, framelessMemcpySpec, memcpyRegionSpec] at hpre ⊢
    ac_nf at hpre ⊢
  · dsimp only [sessionMemcpySpec, framelessMemcpySpec] at hpost ⊢
    ac_nf at hpost ⊢

theorem statesRecvPlacedContracts_of_ro_leaves [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    [HkdfPlacedHooks F (Rust.withPanics ext)]
    (hA : RecvCt2PlacedAlloc A ext)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec growOneStack))
    (hmemset_sat : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionSpec)
    (hval_pk_sat : HookSat (Rust.withPanics ext)
      "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"
      (mlkemValidatePkSpec K))
    (hencaps2_sat : HookSat (Rust.withPanics ext) spqrMlkemEncaps2Sym (mlkemEncaps2Spec K))
    (hdecaps_sat : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (mlkemDecapsSpec K))
    (hhmac_sat : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacSpec F A)) :
    StatesRecvPlacedContracts A F K ext :=
  let hshim_sess : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec :=
    ProofLib.HookSat.mono hA.shim fun x R _ hpre => ⟨x, R, hpre, fun _ hpost => hpost⟩
  let hmemcpy_reg_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionSpec :=
    hA.memcpy
  let hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec :=
    hookSat_sessionMemcpy_of_frameless 4096 hA.memcpy
  StatesRecvPlacedContracts.of_callees
    (ls_subroutine_ok_of_block (i := 332) (j := 370)
      (keys_sampled_recv_ct1_chunk_placed_ok_x hA.handleError hA.shim hA.alloc hA.realloc
        hA.dealloc hmemcpy_reg_sat hmemmove_sat))
    (keys_ls_subroutine_ok_of_block_cro (i := 332) (j := 337)
      (header_sent_recv_ct1_chunk_placed_ok_x hA.handleError hA.shim hA.alloc hA.realloc
        hA.dealloc hmemcpy_reg_sat hmemmove_sat hmemset_sat))
    (ls_subroutine_ok_of_block (i := 332) (j := 346)
      (ct1_received_recv_ct2_chunk_placed_ok_x hA.handleError hA.shim hA.alloc hA.realloc
        hA.dealloc hmemcpy_reg_sat hmemmove_sat))
    (keys_ls_subroutine_ok_of_block_cro (i := 332) (j := 350)
      (ek_sent_ct1_received_recv_ct2_chunk_placed_ok_x hA hmemcpy_reg_sat hmemmove_sat
        hmemset_sat hdecaps_sat hhmac_sat))
    (keys_ls_subroutine_ok_of_block_cro (i := 332) (j := 369)
      (noHeaderReceived_recv_hdr_chunk_placed_closed_okX hA.shim hA.alloc hA.realloc
        hA.dealloc hA.memcpy hmemcpy_reg_sat hA.memcpyRO hmemmove_sat hmemset_sat hhmac_sat
        hA.handleError hA.assertFailedU64 hA.sliceIndexFail hA.panicBoundsCheck))
    (ls_subroutine_ok_of_block (i := 332) (j := 419)
      (add_chunk_cl_placed_ok_x hA.handleError hshim_sess hA.alloc hA.realloc hmemmove_sat))
    (keys_ls_subroutine_ok_of_block_cro (i := 332) (j := 418)
      (polyDecoderDecodedMessage_cro_placed_ok_x hA.handleError hshim_sess
        hA.alloc hA.realloc hA.dealloc hmemcpy_reg_sat hmemset_sat))
    (ls_subroutine_ok_of_block (i := 332) (j := 338)
      (unchunked_ct1_sent_recv_ek_placed_cl_ok_x hA.dealloc hval_pk_sat))
    (ls_subroutine_ok_of_block (i := 332) (j := 347)
      (unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok hA.handleError hA.shim hA.alloc
        hA.realloc hA.dealloc hA.memcpy hA.memcpyRO hencaps2_sat hhmac_sat))
    (ls_subroutine_ok_of_block (i := 332) (j := 382)
      (send_ct2_encoder_placed_ok_x hA.handleError hA.shim hA.alloc hA.realloc
        hA.dealloc hmemcpy_reg_sat))
    (ls_subroutine_ok_of_block (i := 332) (j := 343)
      (ek_received_ct1_sampled_recv_ct1_ack_placed_ok_x hA.handleError hA.shim hA.alloc
        hA.realloc hA.dealloc hA.memcpy hmemcpy_reg_sat hA.memcpyRO
        hencaps2_sat hhmac_sat))
    (keys_ls_subroutine_ok_of_block_cro (i := 332) (j := 349)
      (ct1_acknowledged_recv_ek_chunk_placed_closed_ok_x hA.handleError hA.shim hA.alloc
        hA.realloc hA.dealloc hA.memcpy hmemcpy_reg_sat hA.memcpyRO hmemmove_sat hmemset_sat
        hval_pk_sat hencaps2_sat hhmac_sat))
    (ls_subroutine_ok_of_block (i := 332) (j := 355)
      (ct2_sampled_recv_next_epoch_placed_ok_x hA.dealloc))
    hA.shim hA.alloc hA.dealloc hmemcpy_sat hA.memcpyRO

/-- Closed top-level relocatable `subroutine_ok` contract (`StatesRecvPlacedOkX`) for
`<spqr::v1::chunked::states::States>::recv` (Block `332`, 4,884 instructions),
discharging all 17 cross-block callees from external hook and panic contracts alone. -/
theorem states_recv_placed_ok_x_closed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    [HkdfPlacedHooks F (Rust.withPanics ext)]
    (hA : RecvCt2PlacedAlloc A ext)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec growOneStack))
    (hmemset_sat : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionSpec)
    (hval_pk_sat : HookSat (Rust.withPanics ext)
      "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"
      (mlkemValidatePkSpec K))
    (hencaps2_sat : HookSat (Rust.withPanics ext) spqrMlkemEncaps2Sym (mlkemEncaps2Spec K))
    (hdecaps_sat : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (mlkemDecapsSpec K))
    (hhmac_sat : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacSpec F A)) :
    StatesRecvPlacedOkX A F K ext :=
  states_recv_placed_ok_x A F K ext
    (statesRecvPlacedContracts_of_ro_leaves hA hmemmove_sat hmemset_sat
      hval_pk_sat hencaps2_sat hdecaps_sat hhmac_sat)

/-! ## Relocatable `.rodata` Extraction Lemmas for `statesRecvRoPlacedAt` -/

theorem rodata_ctLabel_statesRecv_placed [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗ P :=
  lsro_intro_chk hro (by decide +kernel) hP

theorem rodata_statesRecvRoPlacedAt [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) {P : SepProp}
    (hP : m ⊨ (lsLogFilterAddr ↦₆₄ 0#64) ∗ tokenInitPlacedAt ∗ P) :
    m ⊨ statesRecvRoPlacedAt ∗ P := by
  have h1 := rodata_statesRecvJumpTablePlacedAt hro hP
  have h2 := rodata_ctLabel_statesRecv_placed hro h1
  have h3 := rodata_reduceTable_placed hro h2
  refine Satisfies.mono (Entails.of_eq ?_) h3
  dsimp only [statesRecvRoPlacedAt, unchunkedSendCt2PlacedRoAt]
  ac_rfl

end CryptoVerification.SpqrV1.States.Recv.Top

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Kdf

abbrev states_recv_variant_placed_ext [LibsignalPlacement] :=
  @Top.states_recv_variant_placed_ext
abbrev states_recv_variant_placed_x [LibsignalPlacement] :=
  @Top.states_recv_variant_placed_x
abbrev states_recv_placed_ok_ext [LibsignalPlacement] :=
  @Top.states_recv_placed_ok_ext
abbrev states_recv_placed_ok_x [LibsignalPlacement] :=
  @Top.states_recv_placed_ok_x
abbrev statesRecvPlacedContracts_of_ro_leaves [LibsignalPlacement] :=
  @Top.statesRecvPlacedContracts_of_ro_leaves
abbrev states_recv_placed_ok_x_closed [LibsignalPlacement] :=
  @Top.states_recv_placed_ok_x_closed
abbrev rodata_ctLabel_statesRecv_placed [LibsignalPlacement] :=
  @Top.rodata_ctLabel_statesRecv_placed
abbrev rodata_statesRecvRoPlacedAt [LibsignalPlacement] :=
  @Top.rodata_statesRecvRoPlacedAt

end CryptoVerification.SpqrV1.States.Recv
