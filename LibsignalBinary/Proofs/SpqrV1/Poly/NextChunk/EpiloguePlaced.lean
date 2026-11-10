/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Epilogue
public import LibsignalBinary.Proofs.SpqrV1.Drop.Poly
public import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Phase
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Defs
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Defs
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.NextChunkCodeSym
import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Proof
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Placed Prologue and Epilogue

Relocatable `[LibsignalPlacement]` callee bundle (`AllocContractsPlaced`), prologue (`+0..+92`),
OOM panic helpers, and shared epilogue (`+4484`) for Block `416`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.SpqrV1.Poly.LagrangeComplete
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm] bv_add_lit_add_lit
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre
attribute [local arm64_norm, local wp_norm]
  sp_sub_1200_add_1104 sp_sub_968_add_8
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80 sp_sub_96_add_96
  sp_sub_88_add_8 sp_sub_80_add_8 sp_sub_72_add_8 sp_sub_64_add_8 sp_sub_56_add_8
  sp_sub_48_add_8 sp_sub_40_add_8 sp_sub_32_add_8 sp_sub_24_add_8 sp_sub_16_add_8
  sp_sub_96_sub_1104 exists_pow_two_eq_one
  setWidth16_zext64_setWidth32 setWidth32_zext64 setWidth32_zext64_add_one
  extractLsb_0_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_64_64_append
  polyEncoderTagOff polyEncoderVecsOff polyEncoderVecsSize
  polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize
  polyEncoderPointsTag polyEncoderPolysTag
  chunkDataOff chunkIndexOff chunkSize

/-! ## 1. Relocatable Hook & Callee Bundle (`AllocContractsPlaced`) -/

/-- Relocatable `[LibsignalPlacement]` counterpart of `AllocContracts b A ext` for `NextChunk`
    (Block `416`) and its SPQR callees (`compute_at`, `lagrange_interpolate_prepare`,
    `lagrange_interpolate_complete`, `drop_glue::<[Poly; 16]>`). -/
structure AllocContractsPlaced (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  handle_error : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked
  shim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec
  alloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A)
  dealloc : HookSat (Rust.withPanics ext) ComputeAt.spqrRustDeallocSym (rustDeallocSpec A)
  realloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A)
  session_memcpy : ∀ (hookStack : Nat),
    HookSat (Rust.withPanics ext) spqrMemcpySym (sessionMemcpySpec hookStack)
  session_memset_region :
    HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionSpec

namespace AllocContractsPlaced

theorem handle_error_extern [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext) :
    ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)).externAt?
      (lsρ spqrHandleErrorSym) = some Rust.panicked :=
  (spqr_externAt?_of_mem).trans hA.handle_error

theorem shim_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext) :
    subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimSpec :=
  spqr_hook_ok_of_mem hA.shim

theorem alloc_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext) :
    subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustAllocSpec A) :=
  spqr_hook_ok_of_mem hA.alloc

theorem dealloc_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext) :
    subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsρ ComputeAt.spqrRustDeallocSym) (rustDeallocSpec A) :=
  spqr_hook_ok_of_mem hA.dealloc

theorem session_memcpy_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    (hookStack : Nat := 4096) :
    subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) (sessionMemcpySpec hookStack) :=
  spqr_hook_ok_of_mem (hA.session_memcpy hookStack)

theorem computeAt_blk_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    {m : Memory} (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsmpl.base 371) (withMemEq m (computeAtPlacedSpec A)) :=
  lscall_blk_cl
    (computeAt_placed_ok A ext hA.handle_error hA.shim hA.alloc hA.realloc hA.dealloc) hcl

theorem lagrangePrepare_blk_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    {m : Memory} (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsmpl.base 372) (withMemEq m (lagrangePreparePlacedSpec A)) :=
  lscall_blk
    (lagrangePrepare_placed_ok_of_hookSat A ext hA.handle_error hA.shim hA.alloc hA.session_memset_region) hcl

theorem lagrangeComplete_blk_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (_hA : AllocContractsPlaced A ext)
    {m : Memory} (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsmpl.base 373) (withMemEq m lagrangeCompletePlacedSpec) :=
  lscall_blk_cl (lagrangeComplete_placed_ok ext) hcl

theorem dropGluePoly16_blk_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    {m : Memory} (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsmpl.base 265) (withMemEq m (dropGluePoly16Spec A)) :=
  lscall_blk (drop_glue_poly16_placed_ok (spqr_hook_ok_of_mem hA.dealloc)) hcl

end AllocContractsPlaced

/-! ## 2. Shared Epilogue (Block `416`, offset `+4484`, 21 insns) -/

set_option maxHeartbeats 800000 in
theorem epilogue_placed_sepWP [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext)
    (x : PolyNextChunkGhost) (R : SepProp) (s0 sf : State)
    (out_ptr : BitVec 64) (_hout_ne : out_ptr ≠ 0#64)
    (hidx_chunk : x.chunk.index = x.enc.idx.setWidth 16)
    (hidx_enc' : x.enc'.idx = x.enc.idx + 1#32)
    (hpc : sf.pc = (blkPl_416).base + 4484#64)
    (hrun : sf.status = .Running)
    (hsp : sf.sp = s0.sp - 1200#64)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (htr : sf.trace = s0.trace)
    (hx20 : sf.readReg64 .x20 = 32#64)
    (hx24 : sf.readReg64 .x24 = x.encA)
    (hx27 : (sf.readReg64 .x27).setWidth 16 = x.enc.idx.setWidth 16)
    (hvregs : calleeSavedVRegs sf = calleeSavedVRegs s0 := by simp only [arm64_norm, wp_norm, *]) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sf
      ((out_ptr ↦ₛ x.chunk.data.toList) ∗
       A.live out_ptr 32 1 ∗
       memRegion x.outA chunkSize ∗
       encoderStateAt A x.encA x.enc'.s ∗
       ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
       (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
       (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
       (((s0.sp - 1200#64) + 248#64) ↦₆₄ 32#64) ∗
       localFrameRest (s0.sp - 1200#64) ∗
       savedCells s0 ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       A.pool ∗
       stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
      (fun sf1 P_f =>
        ((sf1.mem ⊨ P_f ∗ R) →
          (sf1.mem ⊨
            ⌜sf1.trace = s0.trace⌝ ∗
             chunkAt x.outA x.chunk ∗
             polyEncoderAt A x.encA x.enc' ∗
             tokenInitPlacedAt ∗
             reduceTablePlacedAt ∗
             A.pool ∗
             stackAt s0.sp polyNextChunkStack ∗ R)) ∧
          sf1.sp = s0.sp ∧ CalleeSavedPreserved s0 sf1) := by
  have hdealloc := hA.dealloc_ok
  clear hA
  have hlen32 : x.chunk.data.toList.length = 32 := x.chunk.data.2
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  apply SepWP.fold (memRegion_chunkSize_entails_cells x.outA) (by sep_focus)
  apply sepWP_exists_left_sep; intro w0
  apply sepWP_exists_left_sep; intro w1
  apply sepWP_exists_left_sep; intro w2
  apply sepWP_exists_left_sep; intro w3
  apply sepWP_exists_left_sep; intro idx0
  wp_conv_pre =>
    rw [pointsToBytes32_eq_pointsTo64_four out_ptr hlen32,
        stackAt_nextChunkCallee_split_allocHook (s0.sp - 1200#64),
        ← hsp]
  unfold savedCells
  wp_steps 10
  have hbuf_mem :
      (out_ptr ↦₆₄ pack64 ((x.chunk.data.toList.take 16).take 8)) ∗
        ((out_ptr + 8#64) ↦₆₄ pack64 ((x.chunk.data.toList.take 16).drop 8)) ∗
        ((out_ptr + 16#64) ↦₆₄ pack64 ((x.chunk.data.toList.drop 16).take 8)) ∗
        ((out_ptr + 24#64) ↦₆₄ pack64 ((x.chunk.data.toList.drop 16).drop 8)) ⊢
        memRegion out_ptr 32 := by
    rw [← pointsToBytes32_eq_pointsTo64_four out_ptr hlen32]
    have h := pointsToBytes_entails_memRegion out_ptr x.chunk.data.toList
    rwa [hlen32] at h
  apply SepWP.fold hbuf_mem (by sep_focus)
  wp_call hdealloc
  have hsp_sf1 : sf_1.sp = s0.sp - 1200#64 := by rw [hsp_sf, hsp]
  have hx24_sf1 : sf_1.readReg64 (Reg.gpr 24#5) = x.encA := by rw [h_5, hx24]
  wp_conv_pre => rw [hsp]
  wp_steps 11
  have hchunk_fold :
      (x.outA ↦₆₄ pack64 ((x.chunk.data.toList.take 16).take 8)) ∗
        ((x.outA + 8#64) ↦₆₄ pack64 ((x.chunk.data.toList.take 16).drop 8)) ∗
        ((x.outA + 16#64) ↦₆₄ pack64 ((x.chunk.data.toList.drop 16).take 8)) ∗
        ((x.outA + 24#64) ↦₆₄ pack64 ((x.chunk.data.toList.drop 16).drop 8)) ∗
        ((x.outA + 32#64) ↦₁₆ ((sf.readReg64 (Reg.gpr 27#5)).setWidth 32).setWidth 16) ⊢
        chunkAt x.outA x.chunk := by
    have htr16 : ((sf.readReg64 (Reg.gpr 27#5)).setWidth 32).setWidth 16 = x.chunk.index := by
      rw [BitVec.setWidth_setWidth_of_le (sf.readReg64 (Reg.gpr 27#5)) (by decide : 16 ≤ 32)]
      exact hx27.trans hidx_chunk.symm
    unfold chunkAt
    simp only [chunkIndexOff, htr16, pointsToBytes32_eq_pointsTo64_four x.outA hlen32]
    exact Entails.of_eq (by ac_rfl)
  apply SepWP.fold hchunk_fold (by sep_focus)
  have henc_fold :
      encoderStateAt A x.encA x.enc'.s ∗
        ((x.encA + 392#64) ↦₃₂ (x.enc.idx + 1#32)) ∗
        memRegion (x.encA + 396#64) 4 ⊢
        polyEncoderAt A x.encA x.enc' := by
    unfold polyEncoderAt
    simp only [polyEncoderIdxOff, polyEncoderPadOff, polyEncoderPadSize, ← hidx_enc']
    exact Entails.of_eq (by ac_rfl)
  apply SepWP.fold henc_fold (by sep_focus)
  have hstk_fold :
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        memRegion (s0.sp - 18432#64) 13136 ∗
        stackAt (s0.sp - 1200#64) allocHookStack ∗
        localFrameRest (s0.sp - 1200#64) ∗
        ((s0.sp - 1144#64) ↦₆₄ x.outA) ∗
        ((s0.sp - 968#64) ↦₆₄ 32#64) ∗
        ((s0.sp - 960#64) ↦₆₄ out_ptr) ∗
        ((s0.sp - 952#64) ↦₆₄ 32#64) ∗
        chunkAt x.outA x.chunk ∗
        polyEncoderAt A x.encA x.enc' ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        A.pool ⊢
        (chunkAt x.outA x.chunk ∗ polyEncoderAt A x.encA x.enc' ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool) ∗
          stackAt s0.sp polyNextChunkStack := by
    have h0 := restore_full_stack s0 x.outA 32#64 out_ptr 32#64
      (chunkAt x.outA x.chunk ∗ polyEncoderAt A x.encA x.enc' ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool)
    have hsub18432 : (s0.sp - 1200#64) - 17232#64 = s0.sp - 18432#64 := by bv_omega
    unfold savedCells at h0
    simp only [arm64_norm, hsub18432] at h0
    exact Entails.trans h0 (Entails.of_eq (by ac_rfl))
  apply SepWP.fold hstk_fold (by sep_focus)
  conv => arg 5; ext sf1 P_f; rw [CalleeSavedPreserved, ← hvregs]
  have htr_ret : sf_1.trace = s0.trace := by
    rw [hpost, htr]
  wp_done

/-! ## 3. OOM Panic Helpers (`lsρ spqrHandleErrorSym` and `+4736`) and Prologue (`+0..+92`) -/

/-- Universal `alloc::raw_vec::handle_error` panic at `lsρ spqrHandleErrorSym` for Block `416`. -/
theorem next_chunk_panic_handle_error_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hpc : s.pc = lsρ spqrHandleErrorSym)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hpan_err :
      ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)).externAt?
        (lsρ spqrHandleErrorSym) = some Rust.panicked :=
    (spqr_externAt?_of_mem).trans h_panic
  refine SepWPp.panic hrun (by rw [hpc]; exact hpan_err) fun hm => ?_
  simpa only [nextChunkOnPanic, sepConj_assoc] using
    allowPanic_panicked (by simp [allocFailedIn, Rust.panicked, arm64_norm, htrace]) hm

theorem sepWPp_panic_of_sepWP_handle_error_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hwp : SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsρ spqrHandleErrorSym) s P
      (fun sm Pm => (Pm ⊢ P) ∧ sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm ⟨hPm, htrm⟩ =>
    SepWPp.weaken_pre hPm (next_chunk_panic_handle_error_placed h_panic s0 sm P R hpcm hrunm htrm))

/-- OOM panic block at `+0x1280` (`+4736..+4744`: `mov w0, #1; mov w1, #32; bl handle_error`). -/
theorem next_chunk_panic_4736_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4736#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  refine sepWPp_panic_of_sepWP_handle_error_placed h_panic s0 s P R ?_
  wp_steps 3
  exact SepWP.done (by wp_norm_goal) (by simp only [wp_norm, hrun])
    ⟨Entails.refl _, by simpa [wp_norm] using htrace⟩

theorem sepWPp_panic_of_sepWP_4736_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hwp : SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 4736#64) s P
      (fun sm Pm => (Pm ⊢ P) ∧ sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm ⟨hPm, htrm⟩ =>
    SepWPp.weaken_pre hPm (next_chunk_panic_4736_placed h_panic s0 sm P R hpcm hrunm htrm))

set_option maxHeartbeats 800000 in
theorem prologue_placed_sepWPp [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext)
    (x : PolyNextChunkGhost) (tag : BitVec 64) (restEnc R : SepProp)
    {Q : State → SepProp → Prop}
    (s0 : State)
    (hpc : s0.pc = (blkPl_416).base)
    (hrun : s0.status = .Running)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = x.encA)
    (hx8 : s0.readReg64 .x8 = x.outA)
    (hcont : ∀ s1 (out_ptr : BitVec 64),
      out_ptr ≠ 0#64 →
      s1.pc = (blkPl_416).base + 92#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 1200#64 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      s1.readReg64 .x9 = (tag.setWidth 32).setWidth 64 →
      s1.readReg64 .x19 = x.encA + 8#64 →
      s1.readReg64 .x24 = x.encA →
      s1.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s1
        (memRegion out_ptr 32 ∗
         A.live out_ptr 32 1 ∗
         memRegion x.outA chunkSize ∗
         (x.encA ↦₆₄ tag) ∗
         restEnc ∗
         ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
         memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
         (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
         (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
         (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
         (((s0.sp - 1200#64) + 248#64) ↦₆₄ 0#64) ∗
         localFrameRest (s0.sp - 1200#64) ∗
         savedCells s0 ∗
         tokenInitPlacedAt ∗
         reduceTablePlacedAt ∗
         A.pool ∗
         stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s0
      (memRegion x.outA chunkSize ∗
       (x.encA ↦₆₄ tag) ∗
       restEnc ∗
       ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       A.pool ∗
       stackAt s0.sp polyNextChunkStack)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hlayout : LayoutOk 32 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  have h32_toNat : (32#64 : BitVec 64).toNat = 32 := rfl
  have h1_toNat : (1#64 : BitVec 64).toNat = 1 := rfl
  have hshim := hA.shim_ok
  simp only [sessionShimSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.alloc_ok
  simp only [rustAllocSpec, BitVec.ofNat_eq_ofNat] at halloc
  have hpanic4736 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4736_placed _ ext hA.handle_error Q s0 s P R
  clear hA
  apply SepWPp.of_sepWP (mid := (blkPl_416).base + 64#64)
  apply SepWP.fold (prologue_stack_split s0) (by sep_focus)
  apply sepWP_exists_left_sep; intro v29
  apply sepWP_exists_left_sep; intro v30
  apply sepWP_exists_left_sep; intro v28
  apply sepWP_exists_left_sep; intro v27
  apply sepWP_exists_left_sep; intro v26
  apply sepWP_exists_left_sep; intro v25
  apply sepWP_exists_left_sep; intro v24
  apply sepWP_exists_left_sep; intro v23
  apply sepWP_exists_left_sep; intro v22
  apply sepWP_exists_left_sep; intro v21
  apply sepWP_exists_left_sep; intro v20
  apply sepWP_exists_left_sep; intro v19
  apply sepWP_exists_left_sep; intro u0
  apply sepWP_exists_left_sep; intro u56
  apply sepWP_exists_left_sep; intro u232
  apply sepWP_exists_left_sep; intro u240
  apply sepWP_exists_left_sep; intro u248
  wp_conv_pre =>
    rw [pointsTo32_eq_pointsTo16_pair (x.encA + polyEncoderIdxOff) x.enc.idx,
        pointsTo64_eq_pointsTo32_pair x.encA tag]
    dsimp only [polyEncoderIdxOff]
  wp_steps 12
  wp_call hshim
  wp_steps 3
  wp_call halloc
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr0
    refine hpanic4736 _ _ ?_
    wp_steps 1
    exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
  · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; rintro ⟨_, htr0⟩
    have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    apply SepWPp.of_sepWP (mid := (blkPl_416).base + 92#64)
    wp_steps 7
    have hfold_tag :
        (x.encA ↦₃₂ tag.setWidth 32) ∗ ((x.encA + 4#64) ↦₃₂ (tag >>> 32).setWidth 32) ⊢
          (x.encA ↦₆₄ tag) := by
      rw [← pointsTo64_eq_pointsTo32_pair x.encA tag]
      exact Entails.refl _
    apply SepWP.fold hfold_tag (by sep_focus)
    have hfold_idx :
        ((x.encA + 392#64) ↦₁₆ x.enc.idx.setWidth 16) ∗
          (((x.encA + 392#64) + 2#64) ↦₁₆ (x.enc.idx >>> 16).setWidth 16) ⊢
          ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) := by
      dsimp only [polyEncoderIdxOff]
      rw [← pointsTo32_eq_pointsTo16_pair (x.encA + 392#64) x.enc.idx]
      exact Entails.refl _
    apply SepWP.fold hfold_idx (by sep_focus)
    have hfold_rest :
        ((s0.sp - 1200#64) ↦₆₄ 0#64) ∗
          memRegion ((s0.sp - 1200#64) + 8#64) 48 ∗
          memRegion ((s0.sp - 1200#64) + 64#64) 168 ∗
          memRegion ((s0.sp - 1200#64) + 256#64) 848 ⊢
          localFrameRest (s0.sp - 1200#64) :=
      localFrameRest_fold_prologue (s0.sp - 1200#64) 0#64
    apply SepWP.fold hfold_rest (by sep_focus)
    have hfold_saved :
        ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
          ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
          ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
          savedCells s0 := by
      unfold savedCells
      exact Entails.refl _
    apply SepWP.fold hfold_saved (by sep_focus)
    wp_conv_pre => rw [h_1]
    have hfold_callee :
        memRegion ((s0.sp - 1200#64) - 17232#64) 13136 ∗
          stackAt (s0.sp - 1200#64) allocHookStack ⊢
          stackAt (s0.sp - 1200#64) nextChunkCalleeStack := by
      rw [← stackAt_nextChunkCallee_split_allocHook (s0.sp - 1200#64)]
      exact Entails.refl _
    apply SepWP.fold hfold_callee (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.weaken_pre ?_ (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · simp only [arm64_norm]
      exact Entails.of_eq (by ac_rfl)
    all_goals simp only [arm64_norm, wp_norm, Reg.x0, Reg.x8, Reg.x9, Reg.x19, Reg.x24, Reg.x27, Reg.x29, Reg.lr, *]

end CryptoVerification.SpqrV1.Poly.NextChunk
