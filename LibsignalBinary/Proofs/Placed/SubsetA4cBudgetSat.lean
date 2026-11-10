/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.SubsetA4cBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.TopPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.LeavesTopPlacedBudget

/-!
# `HookSat` Sibling of `Placed.SubsetA4cBudget` (`SubsetA4cBudgetSat`)

Replaces `[HkdfPlacedHooks F (Rust.withPanics ext)]` in
`SubsetA4cBudget.statesPlacedSeams_of_hooks` (`:105`) with
`[HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Placed.SubsetA4cBudgetSat

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalSpqrV1 (
  MlKem mlkemDecapsSpec mlkemEncaps2Spec mlkemValidatePkSpec
)
open CryptoVerification.LibsignalTripleRatchet (
  memsetName sessionMemcpyRegionSpec sessionMemcpySpec sessionMemmoveSpec
)
open CryptoVerification.SpqrV1.Alloc (growOneStack spqrMemmoveSym)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (spqrMlkemDecapsSym)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym spqrMlkemEncaps2Sym)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget allocMemcpyVmSpec)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux (framelessMemcpyAcpSpec)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (withAllocVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.TopPlacedBudget (states_from_pb_ok_x_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.LeavesTopPlacedBudget (
  ct1_received_send_ek_chunk_placed_blockProgram_ok_x
  ct1_sampled_send_ct1_chunk_placed_blockProgram_ok_x
  ct2_sampled_send_ct2_chunk_placed_blockProgram_ok_x
  ek_received_ct1_sampled_send_ct1_chunk_placed_blockProgram_ok_x
  header_sent_send_ek_chunk_placed_blockProgram_ok_x
  hookSat_sessionMemcpyRegionBudget_of_framelessAcp
  hookSat_sessionShimBudget_of_rustAllocShimVm
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudget (StatesRecvExactEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudgetSat (states_recv_placed_ok_x_closed_sat)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget (RecvCt2PlacedAlloc)
open LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget (
  Ct1ReceivedSendEkChunkEnv Ct1SampledSendCt1ChunkEnv Ct2SampledSendCt2ChunkEnv
  EkReceivedCt1SampledSendCt1ChunkEnv HeaderSentSendEkChunkEnv StatesPlacedSeamsOfEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec sessionMemsetRegionBudgetSpec
)

private theorem hookSat_allocMemcpyVm_of_framelessAcp {hooks : String → Option (State → State)}
    {name : String}
    (h : HookSat hooks name framelessMemcpyAcpSpec) :
    HookSat hooks name allocMemcpyVmSpec := by
  rcases h with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun ⟨dst, src, bs⟩ R s0 hrun hpre hsp => ?_⟩
  dsimp only [allocMemcpyVmSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2_bv, hlt⟩, hm⟩
  have hx2 : (s0.readReg64 .x2).toNat = bs.length := by
    rw [hx2_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hpre' : s0.mem ⊨ framelessMemcpyAcpSpec.pre (dst, src, bs) s0 ∗ R := by
    dsimp only [framelessMemcpyAcpSpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by simpa only [sepConj_assoc] using hm⟩
  rcases hsat (dst, src, bs) R s0 hrun hpre' hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [allocMemcpyVmSpec, framelessMemcpyAcpSpec] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr hrest

private theorem hookSat_sessionMemcpyBudget_of_region_any {H : String → Option (State → State)}
    {sym : String} (hookStack : Nat)
    (h : HookSat H sym sessionMemcpyRegionBudgetSpec) :
    HookSat H sym (sessionMemcpyBudgetSpec hookStack) := by
  refine ProofLib.HookSat.mono h fun ⟨dst, src, bs⟩ R s0 hpre =>
    ⟨(dst, src, bs), stackAt s0.sp hookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [sessionMemcpyBudgetSpec, sessionMemcpyRegionBudgetSpec,
      sessionMemcpySpec, libcMemcpySpec, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpre ⊢
    ac_nf at hpre ⊢
  · dsimp only [sessionMemcpyBudgetSpec, sessionMemcpyRegionBudgetSpec,
      sessionMemcpySpec, sessionMemcpyRegionSpec] at hpost ⊢
    ac_nf at hpost ⊢

private theorem hookSat_withAllocVmPreserved_memmove_of_zero {H : String → Option (State → State)}
    {sym : String} (hookStack : Nat)
    (h : HookSat H sym (withAllocVmPreserved (sessionMemmoveSpec 0))) :
    HookSat H sym (withAllocVmPreserved (sessionMemmoveSpec hookStack)) := by
  refine ProofLib.HookSat.mono h fun ⟨base, buf, dst, src, len⟩ R s0 hpre =>
    ⟨(base, buf, dst, src, len), stackAt s0.sp hookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [withAllocVmPreserved, sessionMemmoveSpec, libcMemmoveSpec, stackAt] at hpre ⊢
    simp only [ProofLib.memRegion_zero, sepConj_emp]
    ac_nf at hpre ⊢
  · dsimp only [withAllocVmPreserved, sessionMemmoveSpec, stackAt] at hpost ⊢
    simp only [ProofLib.memRegion_zero, sepConj_emp] at hpost
    ac_nf at hpost ⊢

theorem statesPlacedSeams_of_hooks_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hmemmove0 : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec 0)))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hval_pk : HookSat (Rust.withPanics ext)
      "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"
      (withVmPreserved (mlkemValidatePkSpec K)))
    (hencaps2 : HookSat (Rust.withPanics ext) spqrMlkemEncaps2Sym
      (withVmPreserved (mlkemEncaps2Spec K)))
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec F M A lim)) :
    StatesPlacedSeamsOfEnv M A lim F K
      StatesFromPbEnv (StatesRecvExactEnv K)
      HeaderSentSendEkChunkEnv Ct1ReceivedSendEkChunkEnv
      Ct1SampledSendCt1ChunkEnv EkReceivedCt1SampledSendCt1ChunkEnv Ct2SampledSendCt2ChunkEnv
      ext :=
  let hshim_sess :=
    hookSat_sessionShimBudget_of_rustAllocShimVm hA.shim
  let hmemcpy_reg :=
    hookSat_sessionMemcpyRegionBudget_of_framelessAcp hA.memcpy
  let hAllocPlaced : AllocContractsPlaced M A lim ext := {
    handle_error := hA.handleError
    shim := hshim_sess
    alloc := hA.alloc
    dealloc := hA.dealloc
    realloc := hA.realloc
    session_memcpy := fun hookStack => hookSat_sessionMemcpyBudget_of_region_any hookStack hmemcpy_reg
    session_memset_region := hmemset
  }
  let hFromPb : FromPbAllocHooksBudget M A lim ext := {
    panic_ok := hA.handleError
    shim := hA.shim
    alloc := hA.alloc
    dealloc := hA.dealloc
    memcpy := hookSat_allocMemcpyVm_of_framelessAcp hA.memcpy
  }
  {
    statesFromPb_ok :=
      states_from_pb_ok_x_placed hFromPb hmemmove0
    statesRecv_ok :=
      states_recv_placed_ok_x_closed_sat hA
        (hookSat_withAllocVmPreserved_memmove_of_zero growOneStack hmemmove0)
        hmemset hval_pk hencaps2 hdecaps hhmac
    headerSentSendEkChunk_ok :=
      header_sent_send_ek_chunk_placed_blockProgram_ok_x hAllocPlaced
    ct1ReceivedSendEkChunk_ok :=
      ct1_received_send_ek_chunk_placed_blockProgram_ok_x hAllocPlaced
    ct1SampledSendCt1Chunk_ok :=
      ct1_sampled_send_ct1_chunk_placed_blockProgram_ok_x hAllocPlaced
    ekReceivedCt1SampledSendCt1Chunk_ok :=
      ek_received_ct1_sampled_send_ct1_chunk_placed_blockProgram_ok_x
        hAllocPlaced
    ct2SampledSendCt2Chunk_ok :=
      ct2_sampled_send_ct2_chunk_placed_blockProgram_ok_x hAllocPlaced
  }

end LibsignalBinary.Proofs.Placed.SubsetA4cBudgetSat
