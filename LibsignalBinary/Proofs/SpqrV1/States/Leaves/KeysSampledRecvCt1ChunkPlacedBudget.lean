/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkPlaced
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk` (Block `370`, `RustCliAllocBudget` Lifts)

Re-exports the Block `370` `[LibsignalPlacement]` contracts under `RustCliAllocBudget M` from
`KeysSampledRecvCt1ChunkBudgetAux`, and provides envelope-monotonicity lifts,
`sessionShimBudgetSpec` hook variants, and `libsignalSessionLib.blockProgram` / cross-block
`IsLsBlockProg` seam bridges.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement blkPl_370 extract_withLsCodeLoaded
   libsignalSessionLib lsProg_370 ls_subroutine_ok_of_block lsmpl
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (SortedSetPt)
open CryptoVerification.SpqrV1.Alloc
  (spqrRustAllocSym spqrRustNoAllocShimSym spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.States.Leaves
  (KeysSampledRecvCt1ChunkGhost ls_subroutine_ok_to_blockProgram)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget (drop_glue_poly16_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
  (AddChunkPlacedOkExt AddChunkSlotsEnv addChunkSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget (encodeBytesAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.ProofBudget (encode_bytes_placed_ok_ext)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
  (KeysSampledRecvCt1ChunkEnv KeysSampledRecvCt1ChunkPlacedOkX
   KeysSampledRecvCt1ChunkPlacedOkXOfEnv KeysSampledRecvCt1ChunkPlacedOkXOfPrePostEnv
   KeysSampledRecvCt1ChunkPostEnv KeysSampledRecvCt1ChunkPreEnv
   keysSampledRecvCt1ChunkSpec keysSampledRecvCt1ChunkSpecOfEnv
   keysSampledRecvCt1ChunkSpecOfPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkBudgetAux
  (keys_sampled_recv_ct1_chunk_placed_cl_ext_of_callees_ofPrePostEnv
   keysSampledRecvCt1ChunkPostEnv_of_parts keysSampledRecvCt1ChunkPreEnv_of_parts)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux
  (hookSat_sessionMemcpyBudget_of_region)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)

/-! ## 1. Re-Exports from `Batch2DefsPlacedBudget` & `KeysSampledRecvCt1ChunkBudgetAux` -/

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
  (KeysSampledRecvCt1ChunkPreEnv KeysSampledRecvCt1ChunkPostEnv
   KeysSampledRecvCt1ChunkEnv keysSampledRecvCt1ChunkPreEnv_nonempty
   keysSampledRecvCt1ChunkEnv_nonempty)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
  (keysSampledRecvCt1ChunkSpecOfPrePostEnv keysSampledRecvCt1ChunkSpecOfEnv
   keysSampledRecvCt1ChunkSpec)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
  (KeysSampledRecvCt1ChunkPlacedOkXOfPrePostEnv KeysSampledRecvCt1ChunkPlacedOkXOfEnv
   KeysSampledRecvCt1ChunkPlacedOkX)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkBudgetAux
  (emptyPolyDecoder_pts keysSampledRecvCt1ChunkPreEnv_of_parts
   keysSampledRecvCt1ChunkPostEnv_of_parts)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkBudgetAux
  (keys_sampled_recv_ct1_chunk_placed_cl_ext_of_callees_ofPrePostEnv
   keys_sampled_recv_ct1_chunk_placed_cl_ext_of_callees_ofEnv
   keys_sampled_recv_ct1_chunk_placed_cl_ext_of_callees)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkBudgetAux
  (keys_sampled_recv_ct1_chunk_placed_cl_ext_ofPrePostEnv
   keys_sampled_recv_ct1_chunk_placed_cl_ext_ofEnv
   keys_sampled_recv_ct1_chunk_placed_cl_ext)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkBudgetAux
  (keys_sampled_recv_ct1_chunk_placed_ok_x_ofPrePostEnv
   keys_sampled_recv_ct1_chunk_placed_ok_x_ofEnv
   keys_sampled_recv_ct1_chunk_placed_ok_x)

/-! ## 2. Envelope-Monotonicity Lifts for Block `370` -/

/-- Monotonic widening of `(PreEnv, PostEnv)` on plain `keysSampledRecvCt1ChunkSpecOfPrePostEnv`. -/
theorem keysSampledRecvCt1ChunkSpecOfPrePostEnv_mono [LibsignalPlacement]
    {P : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {PreEnv₁ PostEnv₁ PreEnv₂ PostEnv₂ : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop}
    (hPre : ∀ x evs, PreEnv₁ x evs → PreEnv₂ x evs)
    (hPost : ∀ x evs, PostEnv₁ x evs → PostEnv₂ x evs)
    (hok : subroutine_ok P entry
      (keysSampledRecvCt1ChunkSpecOfPrePostEnv M A lim F PreEnv₁ PostEnv₁)) :
    subroutine_ok P entry
      (keysSampledRecvCt1ChunkSpecOfPrePostEnv M A lim F PreEnv₂ PostEnv₂) := by
  refine subroutine_ok_mono hok (fun ⟨x, st⟩ R s0 hp => ?_) (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · dsimp only [keysSampledRecvCt1ChunkSpecOfPrePostEnv] at hp ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    rcases hp with ⟨⟨h0, h1, h2, h3, h4, hfit, hlr⟩, hmem⟩
    exact ⟨⟨h0, h1, h2, h3, h4, FitsEnv.mono (hPre x) hfit, hlr⟩, hmem⟩
  · dsimp only [keysSampledRecvCt1ChunkSpecOfPrePostEnv] at hq ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨⟨htr, hpost⟩, hmem⟩
    exact ⟨⟨htr, hPost x evs hpost⟩, hmem⟩

/-- Monotonic widening of `(PreEnv, PostEnv)` on `[LibsignalPlacement]`
    `KeysSampledRecvCt1ChunkPlacedOkXOfPrePostEnv`. -/
theorem keysSampledRecvCt1ChunkPlacedOkX_mono [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {PreEnv₁ PostEnv₁ PreEnv₂ PostEnv₂ : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop}
    (hPre : ∀ x evs, PreEnv₁ x evs → PreEnv₂ x evs)
    (hPost : ∀ x evs, PostEnv₁ x evs → PostEnv₂ x evs)
    (hok : KeysSampledRecvCt1ChunkPlacedOkXOfPrePostEnv M A lim F PreEnv₁ PostEnv₁ ext) :
    KeysSampledRecvCt1ChunkPlacedOkXOfPrePostEnv M A lim F PreEnv₂ PostEnv₂ ext := by
  refine subroutine_ok_mono hok (fun ⟨x, st⟩ R s0 hp => ?_) (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hp
    dsimp only [keysSampledRecvCt1ChunkSpecOfPrePostEnv] at hpre
    dsimp only [withLsCodeLoaded, keysSampledRecvCt1ChunkSpecOfPrePostEnv]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨h0, h1, h2, h3, h4, hfit, hlr⟩, hmem⟩
    exact ⟨⟨h0, h1, h2, h3, h4, FitsEnv.mono (hPre x) hfit, hlr⟩, hmem⟩
  · dsimp only [withLsCodeLoaded, keysSampledRecvCt1ChunkSpecOfPrePostEnv] at hq ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨⟨htr, hpost⟩, hmem⟩
    exact ⟨⟨htr, hPost x evs hpost⟩, hmem⟩

/-- Lift canonical `KeysSampledRecvCt1ChunkPlacedOkX` into any single-envelope `Env` containing
    `KeysSampledRecvCt1ChunkEnv`. -/
theorem keysSampledRecvCt1ChunkPlacedOkXOfEnv_of_canonical [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop}
    (hEnv : ∀ x evs, KeysSampledRecvCt1ChunkEnv x evs → Env x evs)
    (hok : KeysSampledRecvCt1ChunkPlacedOkX M A lim F ext) :
    KeysSampledRecvCt1ChunkPlacedOkXOfEnv M A lim F Env ext :=
  keysSampledRecvCt1ChunkPlacedOkX_mono
    (fun x evs h => hEnv x evs (Or.inl h)) hEnv hok

/-! ## 3. `sessionShimBudgetSpec` Hook Variants for Block `370` -/

/-- Two-envelope `[LibsignalPlacement]` contract for `<KeysSampled>::recv_ct1_chunk` (Block `370`)
    taking `sessionShimBudgetSpec` directly on `spqrRustNoAllocShimSym`. -/
theorem keys_sampled_recv_ct1_chunk_placed_cl_ext_of_sessionShim_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {PreEnv PostEnv : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop}
    (hPre : ∀ x evs1,
      AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs1 →
      PreEnv x (evs1 ++ encodeBytesAllocEvents x.st.uc.ek.length))
    (hPost : ∀ x evs1 evs_free,
      AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs1 →
      FreeOnlyEvs evs_free →
      PostEnv x ((evs1 ++ encodeBytesAllocEvents x.st.uc.ek.length) ++ evs_free))
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hadd : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec M A lim))) :
    KeysSampledRecvCt1ChunkPlacedOkXOfPrePostEnv M A lim F PreEnv PostEnv ext :=
  keys_sampled_recv_ct1_chunk_placed_cl_ext_of_callees_ofPrePostEnv
    hPre hPost hdealloc hmemcpy hadd
    (ls_subroutine_ok_of_block (i := 370) (j := 417)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (encode_bytes_placed_ok_ext hshim halloc
          (hookSat_sessionMemcpyBudget_of_region hmemcpy))))
    (ls_subroutine_ok_of_block (i := 370) (j := 265)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (drop_glue_poly16_placed_ok (spqr_hook_ok_of_mem hdealloc))))

/-- Canonical `[LibsignalPlacement]` contract for `<KeysSampled>::recv_ct1_chunk` (Block `370`)
    taking `sessionShimBudgetSpec` directly on `spqrRustNoAllocShimSym`. -/
theorem keys_sampled_recv_ct1_chunk_placed_cl_ext_of_sessionShim [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hadd : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec M A lim))) :
    KeysSampledRecvCt1ChunkPlacedOkX M A lim F ext :=
  keys_sampled_recv_ct1_chunk_placed_cl_ext_of_sessionShim_ofPrePostEnv
    keysSampledRecvCt1ChunkPreEnv_of_parts
    keysSampledRecvCt1ChunkPostEnv_of_parts
    hshim halloc hdealloc hmemcpy hadd

/-- Canonical `[LibsignalPlacement]` contract taking `sessionShimBudgetSpec` and
    `AddChunkPlacedOkExt`. -/
theorem keys_sampled_recv_ct1_chunk_placed_ok_x_of_sessionShim [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hadd : AddChunkPlacedOkExt M A lim ext) :
    KeysSampledRecvCt1ChunkPlacedOkX M A lim F ext :=
  keys_sampled_recv_ct1_chunk_placed_cl_ext_of_sessionShim
    hshim halloc hdealloc hmemcpy
    (ls_subroutine_ok_of_block (i := 370) (j := 419)
      (subroutine_ok_withLsCodeLoaded_of_plain hadd))

/-! ## 4. `libsignalSessionLib.blockProgram` & Cross-Block Seam Bridges -/

theorem keys_sampled_recv_ct1_chunk_placed_blockProgram_ok_x_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {PreEnv PostEnv : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop}
    (hok : KeysSampledRecvCt1ChunkPlacedOkXOfPrePostEnv M A lim F PreEnv PostEnv ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 370 (Rust.withPanics ext))
      (blkPl_370).base
      (withLsCodeLoaded lsmpl
        (keysSampledRecvCt1ChunkSpecOfPrePostEnv M A lim F PreEnv PostEnv)) :=
  ls_subroutine_ok_to_blockProgram (calleeProg := lsProg_370 (Rust.withPanics ext)) hok

theorem keys_sampled_recv_ct1_chunk_placed_blockProgram_ok_x_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop}
    (hok : KeysSampledRecvCt1ChunkPlacedOkXOfEnv M A lim F Env ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 370 (Rust.withPanics ext))
      (blkPl_370).base
      (withLsCodeLoaded lsmpl (keysSampledRecvCt1ChunkSpecOfEnv M A lim F Env)) :=
  keys_sampled_recv_ct1_chunk_placed_blockProgram_ok_x_ofPrePostEnv hok

theorem keys_sampled_recv_ct1_chunk_placed_blockProgram_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hok : KeysSampledRecvCt1ChunkPlacedOkX M A lim F ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 370 (Rust.withPanics ext))
      (blkPl_370).base
      (withLsCodeLoaded lsmpl (keysSampledRecvCt1ChunkSpec M A lim F)) :=
  keys_sampled_recv_ct1_chunk_placed_blockProgram_ok_x_ofPrePostEnv hok

/-- Cross-block transfer of `KeysSampledRecvCt1ChunkPlacedOkXOfPrePostEnv` onto any caller
    block `i < 619` (e.g. `i = 332` `States::recv`). -/
theorem keys_sampled_recv_ct1_chunk_placed_in_block_ofPrePostEnv [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {PreEnv PostEnv : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop}
    (hok : KeysSampledRecvCt1ChunkPlacedOkXOfPrePostEnv M A lim F PreEnv PostEnv ext)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_370).base
      (withLsCodeLoaded lsmpl
        (keysSampledRecvCt1ChunkSpecOfPrePostEnv M A lim F PreEnv PostEnv)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg)
    (calleeProg := lsProg_370 (Rust.withPanics ext)) (i := i) (j := 370) hok hi

/-- Cross-block transfer of `KeysSampledRecvCt1ChunkPlacedOkX` onto any caller block `i < 619`. -/
theorem keys_sampled_recv_ct1_chunk_placed_in_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    (hok : KeysSampledRecvCt1ChunkPlacedOkX M A lim F ext)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_370).base
      (withLsCodeLoaded lsmpl (keysSampledRecvCt1ChunkSpec M A lim F)) :=
  keys_sampled_recv_ct1_chunk_placed_in_block_ofPrePostEnv hok hi

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkPlacedBudget
