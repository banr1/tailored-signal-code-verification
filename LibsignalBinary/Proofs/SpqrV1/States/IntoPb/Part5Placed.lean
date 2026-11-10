/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.IntoPbCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`): Shared Helpers for Arms 7, 8, and 9

Relocatable `[LibsignalPlacement]` counterparts of the OOM panic helpers at `+1700` and `+884` in
Block `334`, re-exporting pure and separation-logic `vecU8` / `Ct1Sent` helpers from `Part5.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.IntoPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CryptoVerification.SpqrV1.States.IntoPb.Placed

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Relocatable (`[LibsignalPlacement]`) bundle of the four allocation/memory hook
    contracts needed inside Block `334` (`<spqr::v1::chunked::states::States>::into_pb`). -/
structure StatesIntoPbAllocPlaced [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) : Prop where
  shim_ok :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) noAllocShimSpec
  alloc_ok :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustAllocSpec A)
  dealloc_ok :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A)
  memcpy_ok :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpySpec
  panic_ok :
    (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked

/-- OOM panic block at `+1700` (`mov x0, x25; mov x1, x21; bl handle_error`) in Block `334`. -/
theorem states_into_pb_panic_1700_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : StatesIntoPbAllocPlaced A ext)
    (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_334).base + 1700#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesIntoPbOnPanic s0 sf ∗ R)) := by
  have hpanic : ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)).externAt?
      (lsρ spqrHandleErrorSym) = some Rust.panicked := by
    rw [SpqrV1.Alloc.spqr_externAt?_of_mem, hA.panic_ok]
  apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [statesIntoPbOnPanic, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

/-- OOM panic block at `+884` (`mov x0, x25; mov x1, x22; bl handle_error`) in Block `334`. -/
theorem states_into_pb_panic_884_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : StatesIntoPbAllocPlaced A ext)
    (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_334).base + 884#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesIntoPbOnPanic s0 sf ∗ R)) := by
  have hpanic : ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)).externAt?
      (lsρ spqrHandleErrorSym) = some Rust.panicked := by
    rw [SpqrV1.Alloc.spqr_externAt?_of_mem, hA.panic_ok]
  apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [statesIntoPbOnPanic, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

end CryptoVerification.SpqrV1.States.IntoPb
