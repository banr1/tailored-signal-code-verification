/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.TopLeafCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneRustAllocPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WPp

/-!
# Relocatable Intermediate Specification for `spqr::encode_varint` (Block `326`, 164 insns)
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.EncodeVarint

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Top.Placed
open CryptoVerification.SpqrV1.Alloc

/-- Wrap `spec`'s precondition with `⌜StepInvPlaced s0 s⌝` on the left so placed
`SepWPp.call_cs_placed` steps can discharge `LibsignalCodeLoaded` from `hcl0 : LibsignalCodeLoaded lsmpl s0.mem`. -/
def withEncStepInvPlaced {α : Type} (s0 : State) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜StepInvPlaced s0 s⌝ ∗ spec.pre x s }

theorem subroutine_ok_withEncStepInvPlaced_of_lscl [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α} {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok prog entry (withEncStepInvPlaced s0 spec) :=
  subroutine_ok_mono h
    (fun _ s _ hp => by
      dsimp only [withEncStepInvPlaced, withLsCodeLoaded] at hp ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hcl0.of_keepsFrozen hp.1.2, hp.2⟩)
    (fun _ _ _ _ hq => hq)

/-- Relocatable callee-saved registers (`x26..x28`, `calleeSavedVRegs`) + `StepInvPlaced`
across `spqr::encode_varint`. -/
def SpqrEncVarintCalleeSavedPlaced (s0 s : State) : Prop :=
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  StepInvPlaced s0 s

theorem SpqrEncVarintCalleeSavedPlaced.refl (s : State) : SpqrEncVarintCalleeSavedPlaced s s :=
  ⟨rfl, rfl, rfl, rfl, StepInvPlaced.refl s⟩

theorem SpqrEncVarintCalleeSavedPlaced.trans {s0 s1 s2 : State}
    (h1 : SpqrEncVarintCalleeSavedPlaced s0 s1) (h2 : SpqrEncVarintCalleeSavedPlaced s1 s2) :
    SpqrEncVarintCalleeSavedPlaced s0 s2 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
   h2.2.2.2.1.trans h1.2.2.2.1,
   h1.2.2.2.2.trans h2.2.2.2.2⟩

theorem SpqrEncVarintCalleeSavedPlaced.of_calleeSavedPreserved {s1 s2 : State}
    (h : CalleeSavedPreserved s1 s2) (hinv : StepInvPlaced s1 s2) :
    SpqrEncVarintCalleeSavedPlaced s1 s2 :=
  ⟨h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2, hinv⟩

/-- Mangled symbol name for `<alloc::raw_vec::RawVec<u8>>::grow_one` (Block `619`). -/
abbrev spqrGrowOneU8Sym : String :=
  "_RNvMs4_NtCs69KKACWg7bl_5alloc7raw_vecINtB5_6RawVechE8grow_oneB7_"

/-- `<alloc::raw_vec::RawVec<u8>>::grow_one` (Block `619`) meets
`withLsCodeLoaded lsmpl (growOneU8Spec A)` on `(blkPC_326).rebase (blkPl_326).base (Rust.withPanics ext)`. -/
def GrowOneU8PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics ext))
    (lsmpl.base 619)
    (withLsCodeLoaded lsmpl (growOneU8Spec A))

/-- Step-invariant-wrapped `<alloc::raw_vec::RawVec<u8>>::grow_one` (Block `619`) contract anchored at `s0`. -/
def GrowOneU8StepOkExt [LibsignalPlacement] (s0 : State) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics ext))
    (lsmpl.base 619)
    (withEncStepInvPlaced s0 (growOneU8Spec A))

theorem growOneU8StepOkExt_of_lscl [LibsignalPlacement] {s0 : State} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h : GrowOneU8PlacedOkExt A ext) :
    GrowOneU8StepOkExt s0 A ext :=
  subroutine_ok_withEncStepInvPlaced_of_lscl hcl0 h

theorem growOneU8_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A)) :
    GrowOneU8PlacedOkExt A ext :=
  growOneU8_caller_cl_ok h_panic hshim halloc hrealloc

/-- `spqr::encode_varint` (Block `326`) meets `withLsCodeLoaded lsmpl (spqrEncodeVarintSpecX A)` on
`(blkPC_326).rebase (blkPl_326).base (Rust.withPanics ext)`. -/
def SpqrEncodeVarintPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics ext))
    (blkPl_326).base
    (withLsCodeLoaded lsmpl (spqrEncodeVarintSpecX A))

/-- `spqr::encode_varint` (Block `326`) meets `withLsCodeLoaded lsmpl (spqrEncodeVarintSpecX A)` on
`libsignalSessionLib.blockProgram lsmpl 326 (Rust.withPanics ext)`. -/
def SpqrEncodeVarintPlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 326 (Rust.withPanics ext))
    (lsmpl.base 326)
    (withLsCodeLoaded lsmpl (spqrEncodeVarintSpecX A))

abbrev EncodeVarintPlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  SpqrEncodeVarintPlacedOkX A ext

end CryptoVerification.SpqrV1.Top.EncodeVarint
