/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInit
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInitPlacedA
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Placed Constant Basis Cases (`n = 0, 1, 3`)

Relocatable `[LibsignalPlacement]` OOM panic helpers (`+4700..+4892`) and constant Lagrange basis
construction (`+1136..+2608` / `+4004`) for `n ∈ {0, 1, 3}`.
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
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  exists_pow_two_eq_two exists_pow_two_eq_eight
attribute [local simp, local arm64_norm, local wp_norm] bv_add_lit_add_lit
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre

/-! ## 1. 3-Instruction `handle_error` OOM Panic Helpers (`+4700..+4892`) -/

theorem next_chunk_panic_4700_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4700#64)
    (hrun : s.status = .Running) (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  refine sepWPp_panic_of_sepWP_handle_error_placed h_panic s0 s P R ?_
  wp_steps
  exact SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
    ⟨Entails.refl _, by simpa [wp_norm] using htrace⟩

theorem sepWPp_panic_of_sepWP_4700_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hwp : SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 4700#64) s P
      (fun sm Pm => (Pm ⊢ P) ∧ sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm ⟨hPm, htrm⟩ =>
    SepWPp.weaken_pre hPm (next_chunk_panic_4700_placed h_panic s0 sm P R hpcm hrunm htrm))

theorem next_chunk_panic_4712_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4712#64)
    (hrun : s.status = .Running) (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  refine sepWPp_panic_of_sepWP_handle_error_placed h_panic s0 s P R ?_
  wp_steps
  exact SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
    ⟨Entails.refl _, by simpa [wp_norm] using htrace⟩

theorem sepWPp_panic_of_sepWP_4712_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hwp : SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 4712#64) s P
      (fun sm Pm => (Pm ⊢ P) ∧ sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm ⟨hPm, htrm⟩ =>
    SepWPp.weaken_pre hPm (next_chunk_panic_4712_placed h_panic s0 sm P R hpcm hrunm htrm))

theorem next_chunk_panic_4724_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4724#64)
    (hrun : s.status = .Running) (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  refine sepWPp_panic_of_sepWP_handle_error_placed h_panic s0 s P R ?_
  wp_steps
  exact SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
    ⟨Entails.refl _, by simpa [wp_norm] using htrace⟩

theorem sepWPp_panic_of_sepWP_4724_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hwp : SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 4724#64) s P
      (fun sm Pm => (Pm ⊢ P) ∧ sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm ⟨hPm, htrm⟩ =>
    SepWPp.weaken_pre hPm (next_chunk_panic_4724_placed h_panic s0 sm P R hpcm hrunm htrm))

theorem next_chunk_panic_4784_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4784#64)
    (hrun : s.status = .Running) (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  refine sepWPp_panic_of_sepWP_handle_error_placed h_panic s0 s P R ?_
  wp_steps
  exact SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
    ⟨Entails.refl _, by simpa [wp_norm] using htrace⟩

theorem sepWPp_panic_of_sepWP_4784_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hwp : SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 4784#64) s P
      (fun sm Pm => (Pm ⊢ P) ∧ sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm ⟨hPm, htrm⟩ =>
    SepWPp.weaken_pre hPm (next_chunk_panic_4784_placed h_panic s0 sm P R hpcm hrunm htrm))

theorem next_chunk_panic_4796_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4796#64)
    (hrun : s.status = .Running) (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  refine sepWPp_panic_of_sepWP_handle_error_placed h_panic s0 s P R ?_
  wp_steps
  exact SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
    ⟨Entails.refl _, by simpa [wp_norm] using htrace⟩

theorem sepWPp_panic_of_sepWP_4796_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hwp : SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 4796#64) s P
      (fun sm Pm => (Pm ⊢ P) ∧ sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm ⟨hPm, htrm⟩ =>
    SepWPp.weaken_pre hPm (next_chunk_panic_4796_placed h_panic s0 sm P R hpcm hrunm htrm))

theorem next_chunk_panic_4808_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4808#64)
    (hrun : s.status = .Running) (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  refine sepWPp_panic_of_sepWP_handle_error_placed h_panic s0 s P R ?_
  wp_steps
  exact SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
    ⟨Entails.refl _, by simpa [wp_norm] using htrace⟩

theorem sepWPp_panic_of_sepWP_4808_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hwp : SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 4808#64) s P
      (fun sm Pm => (Pm ⊢ P) ∧ sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm ⟨hPm, htrm⟩ =>
    SepWPp.weaken_pre hPm (next_chunk_panic_4808_placed h_panic s0 sm P R hpcm hrunm htrm))

theorem next_chunk_panic_4832_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4832#64)
    (hrun : s.status = .Running) (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  refine sepWPp_panic_of_sepWP_handle_error_placed h_panic s0 s P R ?_
  wp_steps
  exact SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
    ⟨Entails.refl _, by simpa [wp_norm] using htrace⟩

theorem sepWPp_panic_of_sepWP_4832_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hwp : SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 4832#64) s P
      (fun sm Pm => (Pm ⊢ P) ∧ sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm ⟨hPm, htrm⟩ =>
    SepWPp.weaken_pre hPm (next_chunk_panic_4832_placed h_panic s0 sm P R hpcm hrunm htrm))

theorem next_chunk_panic_4844_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4844#64)
    (hrun : s.status = .Running) (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  refine sepWPp_panic_of_sepWP_handle_error_placed h_panic s0 s P R ?_
  wp_steps
  exact SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
    ⟨Entails.refl _, by simpa [wp_norm] using htrace⟩

theorem sepWPp_panic_of_sepWP_4844_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hwp : SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 4844#64) s P
      (fun sm Pm => (Pm ⊢ P) ∧ sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm ⟨hPm, htrm⟩ =>
    SepWPp.weaken_pre hPm (next_chunk_panic_4844_placed h_panic s0 sm P R hpcm hrunm htrm))

theorem next_chunk_panic_4856_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4856#64)
    (hrun : s.status = .Running) (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  refine sepWPp_panic_of_sepWP_handle_error_placed h_panic s0 s P R ?_
  wp_steps
  exact SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
    ⟨Entails.refl _, by simpa [wp_norm] using htrace⟩

theorem sepWPp_panic_of_sepWP_4856_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hwp : SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 4856#64) s P
      (fun sm Pm => (Pm ⊢ P) ∧ sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm ⟨hPm, htrm⟩ =>
    SepWPp.weaken_pre hPm (next_chunk_panic_4856_placed h_panic s0 sm P R hpcm hrunm htrm))

theorem next_chunk_panic_4868_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4868#64)
    (hrun : s.status = .Running) (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  refine sepWPp_panic_of_sepWP_handle_error_placed h_panic s0 s P R ?_
  wp_steps
  exact SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
    ⟨Entails.refl _, by simpa [wp_norm] using htrace⟩

theorem sepWPp_panic_of_sepWP_4868_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hwp : SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 4868#64) s P
      (fun sm Pm => (Pm ⊢ P) ∧ sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm ⟨hPm, htrm⟩ =>
    SepWPp.weaken_pre hPm (next_chunk_panic_4868_placed h_panic s0 sm P R hpcm hrunm htrm))

theorem next_chunk_panic_4880_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4880#64)
    (hrun : s.status = .Running) (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  refine sepWPp_panic_of_sepWP_handle_error_placed h_panic s0 s P R ?_
  wp_steps
  exact SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
    ⟨Entails.refl _, by simpa [wp_norm] using htrace⟩

theorem sepWPp_panic_of_sepWP_4880_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hwp : SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 4880#64) s P
      (fun sm Pm => (Pm ⊢ P) ∧ sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm ⟨hPm, htrm⟩ =>
    SepWPp.weaken_pre hPm (next_chunk_panic_4880_placed h_panic s0 sm P R hpcm hrunm htrm))

theorem next_chunk_panic_4892_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4892#64)
    (hrun : s.status = .Running) (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  refine sepWPp_panic_of_sepWP_handle_error_placed h_panic s0 s P R ?_
  wp_steps
  exact SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
    ⟨Entails.refl _, by simpa [wp_norm] using htrace⟩

theorem sepWPp_panic_of_sepWP_4892_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hwp : SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 4892#64) s P
      (fun sm Pm => (Pm ⊢ P) ∧ sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm ⟨hPm, htrm⟩ =>
    SepWPp.weaken_pre hPm (next_chunk_panic_4892_placed h_panic s0 sm P R hpcm hrunm htrm))

/-! ## 2. Constant Basis Cases `n = 1`, `n = 3`, and `n = 0` -/

/-- `n = 1` constant basis case (`+1136 -> +2608`). -/
theorem basis_n1_placed_sepWPp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
    (s0 s : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u24 u96 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 1136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = 1#64)
    (hcont : ∀ s1 basisPtr accPtr,
      basisPtr ≠ 0#64 →
      accPtr ≠ 0#64 →
      s1.pc = (blkPl_416).base + 2608#64 →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x0 = accPtr →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x24 = basisPtr →
      s1.readReg64 .x25 = 1#64 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗
         basisVecAt A basisPtr (extractCompletePolys COMPLETE_POINTS_POLYS_1) ∗
         A.live accPtr 2 2 ∗ memRegion accPtr 2 ∗
         ((fsp + 24#64) ↦₆₄ 1#64) ∗
         ((fsp + 96#64) ↦₆₄ 1#64) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 96#64) ↦₆₄ u96) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hshim := hA.shim_ok; simp only [sessionShimSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.alloc_ok; simp only [rustAllocSpec, BitVec.ofNat_eq_ofNat] at halloc
  have hpanic4844 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4844_placed _ ext hA.handle_error Q s0 s P R
  have hpanic4676 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4676_placed _ ext hA.handle_error Q s0 s P R
  have hpanic4796 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4796_placed _ ext hA.handle_error Q s0 s P R
  clear hA
  apply SepWPp.of_sepWP (mid := (blkPl_416).base + 2536#64)
  wp_steps; wp_apply; wp_steps; wp_apply
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr1
    refine hpanic4844 _ _ ?_
    wp_steps
    exact SepWP.done (by simp only [wp_norm, hoom1, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
      ⟨Entails.refl _, by rw [h, htrace] at htr1; exact htr1⟩
  · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro ⟨halign1, htr1⟩
    have hcond1 : ¬(sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
      simpa [beq_iff_eq] using hoom1
    have halign_basis : (sf_1.readReg64 (Reg.gpr 0#5) &&& 7#64 == 0#64) = true :=
      align8_of_mod8_eq_zero halign1
    apply SepWPp.of_sepWP (mid := (blkPl_416).base + 2540#64)
    wp_steps
    refine SepWP.done (by simp only [wp_norm, hcond1, ↓reduceIte]) (by wp_norm_lhs) ?_
    apply SepWPp.of_sepWP (mid := (blkPl_416).base + 2560#64)
    wp_steps; wp_apply; wp_steps; wp_apply
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
    by_cases hoom2 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom2, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr2
      refine hpanic4676 _ _ ?_
      wp_steps
      exact SepWP.done (by simp only [wp_norm, hoom2, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
        ⟨Entails.refl _, by rw [h_22, htr1, h, htrace] at htr2; exact htr2⟩
    · conv => arg 4; simp only [hoom2, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro ⟨_, htr2⟩
      have hcond2 : ¬(sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
        simpa [beq_iff_eq] using hoom2
      have hsp_sf2 : sf_2.sp = fsp := by
        simp only [h_23, ‹sf_1.sp = sf.sp›, h_1, hsp]
      have hsp_sf3 : sf_3.sp = fsp := by
        simp only [‹sf_3.sp = sf_2.sp›, hsp_sf2]
      have hx19_sf3 : sf_3.readReg64 (Reg.gpr 19#5) = 1#64 := by
        simp only [h_34, h_24, wp_norm, h_12, h_2]
      have hx24_sf3 : sf_3.readReg64 (Reg.gpr 24#5) = sf_1.readReg64 (Reg.gpr 0#5) := by
        simp only [h_39, h_29, wp_norm]
      have hx25_sf3 : sf_3.readReg64 (Reg.gpr 25#5) = 1#64 := by
        simp only [h_40, h_30, wp_norm, h_18, h_8, hx25]
      rw [memRegion_split_polyHeader (sf_1.readReg64 (Reg.gpr 0#5)),
          ProofLib.memRegion_two (sf_3.readReg64 (Reg.gpr 0#5))]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWPp.exists_elim; intro u_len
      apply SepWPp.exists_elim; intro u_ptr
      apply SepWPp.exists_elim; intro u_cap
      apply SepWPp.exists_elim; intro u_c0
      apply SepWPp.of_sepWP (mid := (blkPl_416).base + 2564#64)
      wp_steps
      refine SepWP.done (by simp only [wp_norm, hcond2, ↓reduceIte]) (by wp_norm_lhs) ?_
      rw [hsp_sf2]
      apply SepWPp.of_sepWP (mid := (blkPl_416).base + 2604#64)
      wp_steps; wp_apply; wp_steps; wp_apply
      refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
      by_cases hoom3 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64
      · conv => arg 4; simp only [hoom3, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; intro htr3
        refine hpanic4796 _ _ ?_
        wp_steps
        exact SepWP.done (by simp only [wp_norm, hoom3, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
          ⟨Entails.refl _, by rw [h_44, htr2, h_22, htr1, h, htrace] at htr3; exact htr3⟩
      · conv => arg 4; simp only [hoom3, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; intro ⟨_, htr3⟩
        have hcond3 : ¬(sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
          simpa [beq_iff_eq] using hoom3
        apply SepWPp.of_sepWP (mid := (blkPl_416).base + 2608#64)
        wp_steps
        refine SepWP.done (by simp only [wp_norm, hcond3, ↓reduceIte]) (by wp_norm_lhs) ?_
        have hsp_sf4 : sf_4.sp = fsp := by
          simp only [h_45, hsp_sf3]
        rw [hsp_sf4]
        have hpoly0 :
            (((sf_1.readReg64 (Reg.gpr 0#5)) ↦₆₄ 1#64) ∗
             ((sf_1.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ sf_3.readReg64 (Reg.gpr 0#5)) ∗
             ((sf_1.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ 1#64) ∗
             A.live (sf_3.readReg64 (Reg.gpr 0#5)) 2 2 ∗
             ((sf_3.readReg64 (Reg.gpr 0#5)) ↦₁₆ 1#16)) ⊢
            polyOf A (sf_1.readReg64 (Reg.gpr 0#5)) ⟨[GF16.ONE]⟩ := by
          refine Entails.trans (polyAt_const_one_intro A _ _ hoom2) ?_
          unfold polyOf vecOf
          exact Entails.sepExists_right 1#64 (Entails.sepExists_right (sf_3.readReg64 (Reg.gpr 0#5)) (Entails.refl _))
        have hbasis :
            (A.live (sf_1.readReg64 (Reg.gpr 0#5)) 24 8 ∗
             (((sf_1.readReg64 (Reg.gpr 0#5)) ↦₆₄ 1#64) ∗
              ((sf_1.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ sf_3.readReg64 (Reg.gpr 0#5)) ∗
              ((sf_1.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ 1#64) ∗
              A.live (sf_3.readReg64 (Reg.gpr 0#5)) 2 2 ∗
              ((sf_3.readReg64 (Reg.gpr 0#5)) ↦₁₆ 1#16))) ⊢
            basisVecAt A (sf_1.readReg64 (Reg.gpr 0#5)) (extractCompletePolys COMPLETE_POINTS_POLYS_1) := by
          rw [completePointsPolys1_eq]
          unfold extractCompletePolys constPolysToPolys PolyConst.toPoly basisVecAt polyListOf
          simp only [List.map, List.length_singleton, Nat.mul_one, arrayAt, sepConj_emp, GF16.ONE]
          exact Entails.pure_right hoom1 (sepConj_mono_right hpoly0)
        refine SepWPp.weaken_pre ?_
          (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_5.readReg64 (Reg.gpr 0#5))
            hoom1 hoom3
            (by simp only [wp_norm, hcond3, ↓reduceIte])
            (by wp_norm_lhs)
            (by simp only [wp_norm, ‹sf_5.sp = sf_4.sp›, hsp_sf4])
            (by simp only [arm64_norm, wp_norm]; rw [htr3, h_44, htr2, h_22, htr1, h, htrace])
            (by simp only [arm64_norm, wp_norm, *])
            (by wp_norm_lhs)
            (by simp only [wp_norm, h_57, h_47, h_35, h_25, h_13, h_3])
            (by simp only [wp_norm, h_61, h_51, hx24_sf3])
            (by simp only [wp_norm, h_62, h_52, hx25_sf3])
            (by simp only [wp_norm, h_63, h_53, h_41, h_31, h_19, h_9])
            (by simp only [wp_norm, h_64, h_54, h_42, h_32, h_20, h_10])
            (by simp only [wp_norm, h_65, h_55, h_43, h_33, h_21, h_11])
            (by simp only [wp_norm, hcs_sf_2, hpost_sf_2, hcs_sf_1, hpost_sf_1, hcs_sf, hpost_sf]))
        try simp only [hx19_sf3, hx24_sf3]
        refine Entails.trans (Entails.of_eq (show _ =
          (A.live (sf_1.readReg64 (Reg.gpr 0#5)) 24 8 ∗
           (((sf_1.readReg64 (Reg.gpr 0#5)) ↦₆₄ 1#64) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ sf_3.readReg64 (Reg.gpr 0#5)) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ 1#64) ∗
            A.live (sf_3.readReg64 (Reg.gpr 0#5)) 2 2 ∗
            ((sf_3.readReg64 (Reg.gpr 0#5)) ↦₁₆ 1#16))) ∗
          (A.pool ∗
           A.live (sf_5.readReg64 (Reg.gpr 0#5)) 2 2 ∗
           memRegion (sf_5.readReg64 (Reg.gpr 0#5)) 2 ∗
           ((fsp + 24#64) ↦₆₄ 1#64) ∗
           ((fsp + 96#64) ↦₆₄ 1#64) ∗
           stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
        refine Entails.trans (sepConj_mono_left hbasis) ?_
        exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
/-- `n = 3` constant basis case (`+1136 -> +2608`). -/
theorem basis_n3_placed_sepWPp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
    (s0 s : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u24 u96 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 1136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = 3#64)
    (hcont : ∀ s1 basisPtr accPtr,
      basisPtr ≠ 0#64 →
      accPtr ≠ 0#64 →
      s1.pc = (blkPl_416).base + 2608#64 →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x0 = accPtr →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x24 = basisPtr →
      s1.readReg64 .x25 = 3#64 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗
         basisVecAt A basisPtr (extractCompletePolys COMPLETE_POINTS_POLYS_3) ∗
         A.live accPtr 6 2 ∗ memRegion accPtr 6 ∗
         ((fsp + 24#64) ↦₆₄ 3#64) ∗
         ((fsp + 96#64) ↦₆₄ 3#64) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 96#64) ↦₆₄ u96) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hshim := hA.shim_ok; simp only [sessionShimSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.alloc_ok; simp only [rustAllocSpec, BitVec.ofNat_eq_ofNat] at halloc
  have hpanic4832 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4832_placed _ ext hA.handle_error Q s0 s P R
  have hpanic4808 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4808_placed _ ext hA.handle_error Q s0 s P R
  have hpanic4796 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4796_placed _ ext hA.handle_error Q s0 s P R
  clear hA
  apply SepWPp.of_sepWP (mid := (blkPl_416).base + 1404#64)
  wp_steps; wp_apply; wp_steps; wp_apply
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr1
    refine hpanic4832 _ _ ?_
    wp_steps
    exact SepWP.done (by simp only [wp_norm, hoom1, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
      ⟨Entails.refl _, by rw [h, htrace] at htr1; exact htr1⟩
  · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro ⟨halign1, htr1⟩
    have hcond1 : ¬(sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
      simpa [beq_iff_eq] using hoom1
    have halign_basis0 : (sf_1.readReg64 (Reg.gpr 0#5) &&& 7#64 == 0#64) = true :=
      align8_of_mod8_eq_zero halign1
    have halign_basis24 : ((sf_1.readReg64 (Reg.gpr 0#5) + 24#64) &&& 7#64 == 0#64) = true :=
      align8_add_of_mod8_eq_zero halign1 (by decide)
    have halign_basis48 : ((sf_1.readReg64 (Reg.gpr 0#5) + 48#64) &&& 7#64 == 0#64) = true :=
      align8_add_of_mod8_eq_zero halign1 (by decide)
    rw [memRegion_split_basis3 (sf_1.readReg64 (Reg.gpr 0#5))]
    apply SepWPp.of_sepWP (mid := (blkPl_416).base + 1408#64)
    wp_steps
    refine SepWP.done (by simp only [wp_norm, hcond1, ↓reduceIte]) (by wp_norm_lhs) ?_
    apply SepWPp.of_sepWP (mid := (blkPl_416).base + 1432#64)
    wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
    by_cases hoom2 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom2, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr2
      refine hpanic4808 _ _ ?_
      wp_steps
      exact SepWP.done (by simp only [wp_norm, hoom2, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
        ⟨Entails.refl _, by rw [h_22, htr1, h, htrace] at htr2; exact htr2⟩
    · conv => arg 4; simp only [hoom2, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro ⟨_, htr2⟩
      have hcond2 : ¬(sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
        simpa [beq_iff_eq] using hoom2
      have hx24_sf3 : sf_3.readReg64 (Reg.gpr 24#5) = sf_1.readReg64 (Reg.gpr 0#5) := by
        simp only [h_39, h_29, wp_norm]
      rw [memRegion_split_polyHeader (sf_1.readReg64 (Reg.gpr 0#5)),
          memRegion_split_deg2 (sf_3.readReg64 (Reg.gpr 0#5))]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWPp.exists_elim; intro u0_len
      apply SepWPp.exists_elim; intro u0_ptr
      apply SepWPp.exists_elim; intro u0_cap
      apply SepWPp.exists_elim; intro u0_c2
      apply SepWPp.exists_elim; intro u0_w01
      apply SepWPp.of_sepWP (mid := (blkPl_416).base + 1436#64)
      wp_steps
      refine SepWP.done (by simp only [wp_norm, hcond2, ↓reduceIte]) (by wp_norm_lhs) ?_
      apply SepWPp.of_sepWP (mid := (blkPl_416).base + 1480#64)
      wp_steps; wp_apply; wp_steps; wp_apply
      refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
      by_cases hoom3 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64
      · conv => arg 4; simp only [hoom3, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; intro htr3
        refine hpanic4808 _ _ ?_
        wp_steps
        exact SepWP.done (by simp only [wp_norm, hoom3, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
          ⟨Entails.refl _, by rw [h_44, htr2, h_22, htr1, h, htrace] at htr3; exact htr3⟩
      · conv => arg 4; simp only [hoom3, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; intro ⟨_, htr3⟩
        have hcond3 : ¬(sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
          simpa [beq_iff_eq] using hoom3
        have hx24_sf5 : sf_5.readReg64 (Reg.gpr 24#5) = sf_1.readReg64 (Reg.gpr 0#5) := by
          simp only [h_61, h_51, hx24_sf3]
        rw [memRegion_split_polyHeader_off (sf_1.readReg64 (Reg.gpr 0#5)) 24#64 32#64 40#64 (by bv_arith) (by bv_arith),
            memRegion_split_deg2 (sf_5.readReg64 (Reg.gpr 0#5))]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply SepWPp.exists_elim; intro u1_len
        apply SepWPp.exists_elim; intro u1_ptr
        apply SepWPp.exists_elim; intro u1_cap
        apply SepWPp.exists_elim; intro u1_c2
        apply SepWPp.exists_elim; intro u1_w01
        apply SepWPp.of_sepWP (mid := (blkPl_416).base + 1484#64)
        wp_steps
        refine SepWP.done (by simp only [wp_norm, hcond3, ↓reduceIte]) (by wp_norm_lhs) ?_
        apply SepWPp.of_sepWP (mid := (blkPl_416).base + 1524#64)
        wp_steps; wp_apply; wp_steps; wp_apply
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
        by_cases hoom4 : sf_7.readReg64 (Reg.gpr 0#5) = 0#64
        · conv => arg 4; simp only [hoom4, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; intro htr4
          refine hpanic4808 _ _ ?_
          wp_steps
          exact SepWP.done (by simp only [wp_norm, hoom4, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
            ⟨Entails.refl _, by rw [h_66, htr3, h_44, htr2, h_22, htr1, h, htrace] at htr4; exact htr4⟩
        · conv => arg 4; simp only [hoom4, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; intro ⟨_, htr4⟩
          have hcond4 : ¬(sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
            simpa [beq_iff_eq] using hoom4
          have hsp_sf6 : sf_6.sp = fsp := by
            simp only [h_67, ‹sf_5.sp = sf_4.sp›, h_45, ‹sf_3.sp = sf_2.sp›, h_23, ‹sf_1.sp = sf.sp›, h_1, hsp]
          have hsp_sf7 : sf_7.sp = fsp := by
            simp only [‹sf_7.sp = sf_6.sp›, hsp_sf6]
          have hx19_sf7 : sf_7.readReg64 (Reg.gpr 19#5) = 3#64 := by
            simp only [h_78, h_68, h_56, h_46, wp_norm]
          have hx24_sf7 : sf_7.readReg64 (Reg.gpr 24#5) = sf_1.readReg64 (Reg.gpr 0#5) := by
            simp only [h_83, h_73, hx24_sf5]
          have hx25_sf7 : sf_7.readReg64 (Reg.gpr 25#5) = 3#64 := by
            simp only [h_84, h_74, h_62, h_52, h_40, h_30, wp_norm, h_18, h_8, hx25]
          rw [memRegion_split_polyHeader_off (sf_1.readReg64 (Reg.gpr 0#5)) 48#64 56#64 64#64 (by bv_arith) (by bv_arith),
              memRegion_split_deg2 (sf_7.readReg64 (Reg.gpr 0#5))]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right]
          apply SepWPp.exists_elim; intro u2_len
          apply SepWPp.exists_elim; intro u2_ptr
          apply SepWPp.exists_elim; intro u2_cap
          apply SepWPp.exists_elim; intro u2_c2
          apply SepWPp.exists_elim; intro u2_w01
          apply SepWPp.of_sepWP (mid := (blkPl_416).base + 1528#64)
          wp_steps
          refine SepWP.done (by simp only [wp_norm, hcond4, ↓reduceIte]) (by wp_norm_lhs) ?_
          rw [hsp_sf6]
          apply SepWPp.of_sepWP (mid := (blkPl_416).base + 1580#64)
          wp_steps; wp_apply; wp_steps; wp_apply
          refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
          by_cases hoom5 : sf_9.readReg64 (Reg.gpr 0#5) = 0#64
          · conv => arg 4; simp only [hoom5, ↓reduceIte, sepConj_assoc]
            apply sepWPp_pure_mid; intro htr5
            refine hpanic4796 _ _ ?_
            wp_steps
            exact SepWP.done (by simp only [wp_norm, hoom5, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
              ⟨Entails.refl _, by rw [h_88, htr4, h_66, htr3, h_44, htr2, h_22, htr1, h, htrace] at htr5; exact htr5⟩
          · conv => arg 4; simp only [hoom5, ↓reduceIte, sepConj_assoc]
            apply sepWPp_pure_mid; intro ⟨_, htr5⟩
            have hcond5 : ¬(sf_9.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
              simpa [beq_iff_eq] using hoom5
            apply SepWPp.of_sepWP (mid := (blkPl_416).base + 2608#64)
            wp_steps
            refine SepWP.done (by simp only [wp_norm, hcond5, ↓reduceIte]) (by wp_norm_lhs) ?_
            have hsp_sf8 : sf_8.sp = fsp := by
              simp only [h_89, hsp_sf7]
            rw [hsp_sf8]
            have hpoly0 := polyOf_deg2_intro A (sf_1.readReg64 (Reg.gpr 0#5))
              (sf_3.readReg64 (Reg.gpr 0#5)) 0x88040001#32 0x0001#16 0x8804#16 0x8805#16
              hoom2 rfl rfl
            have hpoly1 := polyOf_deg2_intro_off A (sf_1.readReg64 (Reg.gpr 0#5)) 24#64 32#64 40#64
              (sf_5.readReg64 (Reg.gpr 0#5)) 0xf0070000#32 0x0000#16 0xf007#16 0xf006#16
              (by bv_arith) (by bv_arith) hoom3 rfl rfl
            have hpoly2 := polyOf_deg2_intro_off A (sf_1.readReg64 (Reg.gpr 0#5)) 48#64 56#64 64#64
              (sf_7.readReg64 (Reg.gpr 0#5)) 0x78030000#32 0x0000#16 0x7803#16 0x7803#16
              (by bv_arith) (by bv_arith) hoom4 rfl rfl
            have hbasis :
                (A.live (sf_1.readReg64 (Reg.gpr 0#5)) 72 8 ∗
                 (((sf_1.readReg64 (Reg.gpr 0#5)) ↦₆₄ 3#64) ∗
                  ((sf_1.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ sf_3.readReg64 (Reg.gpr 0#5)) ∗
                  ((sf_1.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ 3#64) ∗
                  A.live (sf_3.readReg64 (Reg.gpr 0#5)) 6 2 ∗
                  ((sf_3.readReg64 (Reg.gpr 0#5)) ↦₃₂ 0x88040001#32) ∗
                  ((sf_3.readReg64 (Reg.gpr 0#5) + 4#64) ↦₁₆ 0x8805#16)) ∗
                 (((sf_1.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ 3#64) ∗
                  ((sf_1.readReg64 (Reg.gpr 0#5) + 32#64) ↦₆₄ sf_5.readReg64 (Reg.gpr 0#5)) ∗
                  ((sf_1.readReg64 (Reg.gpr 0#5) + 40#64) ↦₆₄ 3#64) ∗
                  A.live (sf_5.readReg64 (Reg.gpr 0#5)) 6 2 ∗
                  ((sf_5.readReg64 (Reg.gpr 0#5)) ↦₃₂ 0xf0070000#32) ∗
                  ((sf_5.readReg64 (Reg.gpr 0#5) + 4#64) ↦₁₆ 0xf006#16)) ∗
                 (((sf_1.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ 3#64) ∗
                  ((sf_1.readReg64 (Reg.gpr 0#5) + 56#64) ↦₆₄ sf_7.readReg64 (Reg.gpr 0#5)) ∗
                  ((sf_1.readReg64 (Reg.gpr 0#5) + 64#64) ↦₆₄ 3#64) ∗
                  A.live (sf_7.readReg64 (Reg.gpr 0#5)) 6 2 ∗
                  ((sf_7.readReg64 (Reg.gpr 0#5)) ↦₃₂ 0x78030000#32) ∗
                  ((sf_7.readReg64 (Reg.gpr 0#5) + 4#64) ↦₁₆ 0x7803#16))) ⊢
                basisVecAt A (sf_1.readReg64 (Reg.gpr 0#5)) (extractCompletePolys COMPLETE_POINTS_POLYS_3) := by
              rw [completePointsPolys3_eq]
              unfold extractCompletePolys constPolysToPolys PolyConst.toPoly basisVecAt polyListOf
              simp only [List.map, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
                arrayAt, vecHeaderBytes, BitVec.ofNat_eq_ofNat, sepConj_emp,
                BitVec.add_assoc, BitVec.reduceAdd]
              refine Entails.pure_right hoom1 ?_
              exact sepConj_mono_right (sepConj_mono hpoly0 (sepConj_mono hpoly1 hpoly2))
            refine SepWPp.weaken_pre ?_
              (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_9.readReg64 (Reg.gpr 0#5))
                hoom1 hoom5
                (by simp only [wp_norm, hcond5, ↓reduceIte])
                (by wp_norm_lhs)
                (by simp only [wp_norm, ‹sf_9.sp = sf_8.sp›, hsp_sf8])
                (by simp only [arm64_norm, wp_norm]; rw [htr5, h_88, htr4, h_66, htr3, h_44, htr2, h_22, htr1, h, htrace])
                (by simp only [arm64_norm, wp_norm, *])
                (by wp_norm_lhs)
                (by simp only [wp_norm, h_101, h_91, h_79, h_69, h_57, h_47, h_35, h_25, h_13, h_3])
                (by simp only [wp_norm, h_105, h_95, hx24_sf7])
                (by simp only [wp_norm, h_106, h_96, hx25_sf7])
                (by simp only [wp_norm, h_107, h_97, h_85, h_75, h_63, h_53, h_41, h_31, h_19, h_9])
                (by simp only [wp_norm, h_108, h_98, h_86, h_76, h_64, h_54, h_42, h_32, h_20, h_10])
                (by simp only [wp_norm, h_109, h_99, h_87, h_77, h_65, h_55, h_43, h_33, h_21, h_11])
                (by simp only [wp_norm, hcs_sf_4, hpost_sf_4, hcs_sf_3, hpost_sf_3, hcs_sf_2, hpost_sf_2, hcs_sf_1, hpost_sf_1, hcs_sf, hpost_sf]))
            try simp only [hx19_sf7, hx24_sf7, hx24_sf5, hx24_sf3]
            refine Entails.trans (Entails.of_eq (show _ =
              (A.live (sf_1.readReg64 (Reg.gpr 0#5)) 72 8 ∗
               (((sf_1.readReg64 (Reg.gpr 0#5)) ↦₆₄ 3#64) ∗
                ((sf_1.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ sf_3.readReg64 (Reg.gpr 0#5)) ∗
                ((sf_1.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ 3#64) ∗
                A.live (sf_3.readReg64 (Reg.gpr 0#5)) 6 2 ∗
                ((sf_3.readReg64 (Reg.gpr 0#5)) ↦₃₂ 0x88040001#32) ∗
                ((sf_3.readReg64 (Reg.gpr 0#5) + 4#64) ↦₁₆ 0x8805#16)) ∗
               (((sf_1.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ 3#64) ∗
                ((sf_1.readReg64 (Reg.gpr 0#5) + 32#64) ↦₆₄ sf_5.readReg64 (Reg.gpr 0#5)) ∗
                ((sf_1.readReg64 (Reg.gpr 0#5) + 40#64) ↦₆₄ 3#64) ∗
                A.live (sf_5.readReg64 (Reg.gpr 0#5)) 6 2 ∗
                ((sf_5.readReg64 (Reg.gpr 0#5)) ↦₃₂ 0xf0070000#32) ∗
                ((sf_5.readReg64 (Reg.gpr 0#5) + 4#64) ↦₁₆ 0xf006#16)) ∗
               (((sf_1.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ 3#64) ∗
                ((sf_1.readReg64 (Reg.gpr 0#5) + 56#64) ↦₆₄ sf_7.readReg64 (Reg.gpr 0#5)) ∗
                ((sf_1.readReg64 (Reg.gpr 0#5) + 64#64) ↦₆₄ 3#64) ∗
                A.live (sf_7.readReg64 (Reg.gpr 0#5)) 6 2 ∗
                ((sf_7.readReg64 (Reg.gpr 0#5)) ↦₃₂ 0x78030000#32) ∗
                ((sf_7.readReg64 (Reg.gpr 0#5) + 4#64) ↦₁₆ 0x7803#16))) ∗
              (A.pool ∗
               A.live (sf_9.readReg64 (Reg.gpr 0#5)) 6 2 ∗
               memRegion (sf_9.readReg64 (Reg.gpr 0#5)) 6 ∗
               ((fsp + 24#64) ↦₆₄ 3#64) ∗
               ((fsp + 96#64) ↦₆₄ 3#64) ∗
               stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
            refine Entails.trans (sepConj_mono_left hbasis) ?_
            exact Entails.of_eq (by ac_rfl)

/-- `n = 0` empty basis case (`+1136 -> +4004`). -/
theorem basis_n0_placed_sepWPp [LibsignalPlacement] {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (s0 s : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u24 u96 u640 u648 u664 u672 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 1136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = 0#64)
    (hcont : ∀ s1,
      s1.pc = (blkPl_416).base + 4004#64 →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = 0#64 →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x24 = 8#64 →
      s1.readReg64 .x25 = 0#64 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (((fsp + 24#64) ↦₆₄ 0#64) ∗
         ((fsp + 96#64) ↦₆₄ 0#64) ∗
         ((fsp + 640#64) ↦₆₄ 2#64) ∗
         ((fsp + 648#64) ↦₆₄ 0#64) ∗
         ((fsp + 664#64) ↦₆₄ 2#64) ∗
         ((fsp + 672#64) ↦₆₄ 0#64) ∗
         Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 96#64) ↦₆₄ u96) ∗
       ((fsp + 640#64) ↦₆₄ u640) ∗
       ((fsp + 648#64) ↦₆₄ u648) ∗
       ((fsp + 664#64) ↦₆₄ u664) ∗
       ((fsp + 672#64) ↦₆₄ u672) ∗
       Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  apply SepWPp.of_sepWP (mid := (blkPl_416).base + 4004#64)
  wp_steps
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hcont _ (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [wp_norm, hsp])
      (by simp only [arm64_norm, wp_norm, htrace])
      rfl
      (by wp_norm_lhs)
      (by wp_norm_lhs)
      (by wp_norm_lhs)
      (by simp only [wp_norm, hx25])
      (by wp_norm_lhs)
      (by wp_norm_lhs)
      (by wp_norm_lhs)
      (by wp_norm_lhs))

end CryptoVerification.SpqrV1.Poly.NextChunk
