/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeams
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlaced
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.TopPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlaced

/-!
# Relocatable `Subset A4c` Proof Barrel and `StatesPlacedSeams` Bundle

Roots `SpqrV1/States/{Leaves,RecvCt2Chunk,FromPb,Recv}` under `[LibsignalPlacement]` and assembles
the closed `CryptoVerification.SpqrV1.StatesPlacedSeams` bundle from external hook contracts.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Placed.SubsetA4c

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (
  HkdfPlacedHooks
  framelessMemcpySpec
  memsetName
  sessionMemcpySpec
  sessionMemmoveSpec
  sessionMemsetRegionSpec
  sessionShimSpec
)
open CryptoVerification.LibsignalSpqrV1 (
  MlKem
  libcruxHmacSpec
  mlkemDecapsSpec
  mlkemEncaps2Spec
  mlkemValidatePkSpec
)
open CryptoVerification.SpqrV1 (StatesPlacedSeams)
open CryptoVerification.SpqrV1.Alloc (
  growOneStack
  spqrMemcpySym
  spqrMemmoveSym
  spqrRustNoAllocShimSym
)
open CryptoVerification.SpqrV1.Poly.NextChunk (AllocContractsPlaced)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym spqrMlkemEncaps2Sym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced (FromPbAllocHooks)
open CryptoVerification.SpqrV1.States.FromPb (states_from_pb_ok_x_placed)
open CryptoVerification.SpqrV1.States.Leaves (
  ct1_received_send_ek_chunk_placed_ok_x
  ct1_sampled_send_ct1_chunk_placed_ok_x
  ct2_sampled_send_ct2_chunk_placed_ok_x
  ek_received_ct1_sampled_send_ct1_chunk_placed_ok_x
  header_sent_send_ek_chunk_placed_ok_x
)
open CryptoVerification.SpqrV1.States.Recv (states_recv_placed_ok_x_closed)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (RecvCt2PlacedAlloc spqrMlkemDecapsSym)

private theorem hookSat_sessionMemcpy_of_frameless {H : String → Option (State → State)}
    {sym : String} (hookStack : Nat) (h : HookSat H sym framelessMemcpySpec) :
    HookSat H sym (sessionMemcpySpec hookStack) := by
  refine ProofLib.HookSat.mono h fun ⟨dst, src, bs⟩ R s0 hpre =>
    ⟨(dst, src, bs), stackAt s0.sp hookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [sessionMemcpySpec, libcMemcpySpec, framelessMemcpySpec, memcpyRegionSpec] at hpre ⊢
    ac_nf at hpre ⊢
  · dsimp only [sessionMemcpySpec, framelessMemcpySpec] at hpost ⊢
    ac_nf at hpost ⊢

private theorem hookSat_sessionMemmove_of_zero {H : String → Option (State → State)}
    {sym : String} (hookStack : Nat) (h : HookSat H sym (sessionMemmoveSpec 0)) :
    HookSat H sym (sessionMemmoveSpec hookStack) := by
  refine ProofLib.HookSat.mono h fun ⟨base, buf, dst, src, len⟩ R s0 hpre =>
    ⟨(base, buf, dst, src, len), stackAt s0.sp hookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [sessionMemmoveSpec, libcMemmoveSpec, stackAt] at hpre ⊢
    simp only [ProofLib.memRegion_zero, sepConj_emp]
    ac_nf at hpre ⊢
  · dsimp only [sessionMemmoveSpec, stackAt] at hpost ⊢
    simp only [ProofLib.memRegion_zero, sepConj_emp] at hpost
    ac_nf at hpost ⊢

/-- Construct the closed `CryptoVerification.SpqrV1.StatesPlacedSeams` bundle (`Blocks 332, 333,
335, 336, 344, 345, 354`) directly from external allocator, libc, panic, HKDF, HMAC, and ML-KEM
hook contracts. -/
theorem statesPlacedSeams_of_hooks [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    [HkdfPlacedHooks F (Rust.withPanics ext)]
    (hA : RecvCt2PlacedAlloc A ext)
    (hmemmove0 : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec 0))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionSpec)
    (hval_pk : HookSat (Rust.withPanics ext)
      "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"
      (mlkemValidatePkSpec K))
    (hencaps2 : HookSat (Rust.withPanics ext) spqrMlkemEncaps2Sym (mlkemEncaps2Spec K))
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (mlkemDecapsSpec K))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacSpec F A)) :
    StatesPlacedSeams A F K ext :=
  let hshim_sess : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec :=
    ProofLib.HookSat.mono hA.shim fun x R _ hpre => ⟨x, R, hpre, fun _ hpost => hpost⟩
  let hmemcpy_any : ∀ hookStack, HookSat (Rust.withPanics ext) spqrMemcpySym (sessionMemcpySpec hookStack) :=
    fun hookStack => hookSat_sessionMemcpy_of_frameless hookStack hA.memcpy
  let hAllocPlaced : AllocContractsPlaced A ext := {
    handle_error := hA.handleError
    shim := hshim_sess
    alloc := hA.alloc
    dealloc := hA.dealloc
    realloc := hA.realloc
    session_memcpy := hmemcpy_any
    session_memset_region := hmemset
  }
  let hFromPb : FromPbAllocHooks A ext := {
    panic_ok := hA.handleError
    shim := hshim_sess
    alloc := hA.alloc
    dealloc := hA.dealloc
    memcpy := hmemcpy_any 4096
  }
  {
    statesFromPb_ok := states_from_pb_ok_x_placed hFromPb hmemmove0
    statesRecv_ok := states_recv_placed_ok_x_closed hA
      (hookSat_sessionMemmove_of_zero growOneStack hmemmove0)
      hmemset hval_pk hencaps2 hdecaps hhmac
    headerSentSendEkChunk_ok := header_sent_send_ek_chunk_placed_ok_x hAllocPlaced
    ct1ReceivedSendEkChunk_ok := ct1_received_send_ek_chunk_placed_ok_x hAllocPlaced
    ct1SampledSendCt1Chunk_ok := ct1_sampled_send_ct1_chunk_placed_ok_x hAllocPlaced
    ekReceivedCt1SampledSendCt1Chunk_ok := ek_received_ct1_sampled_send_ct1_chunk_placed_ok_x hAllocPlaced
    ct2SampledSendCt2Chunk_ok := ct2_sampled_send_ct2_chunk_placed_ok_x hAllocPlaced
  }

end LibsignalBinary.Proofs.Placed.SubsetA4c
