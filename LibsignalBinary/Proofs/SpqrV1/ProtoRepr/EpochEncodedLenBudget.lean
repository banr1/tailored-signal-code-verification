/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen

/-!
# `VmPreserved` Placed Verification of `Epoch::encoded_len` (Blocks `171`, `399`)

Unpinning bridge and `[LibsignalPlacement]` `subroutine_ok` theorems with `VmPreserved` for
`Epoch::encoded_len [local#1, #2]` (Blocks `171` and `399`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLenBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement blkPC_171 blkPl_171 blkPC_399 blkPl_399)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SpqrV1.ProtoRepr
  (chainEpochPBAt_eq_exists_pinned epochEncodedLen_entry_pinned_ok)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetExterns)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
  (withVmPreserved ls_subroutine_ok_plain_vmPreserved
   epochEncodedLenPinnedSpec epochEncodedLenSpec)

theorem epochEncodedLen_ok_of_pinned {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (epochEncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (epochEncodedLenSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨a, ep⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [epochEncodedLenSpec, withVmPreserved] at hpre
  simp only [CryptoVerification.SpqrV1.ProtoRepr.epochEncodedLenSpec,
    chainEpochPBAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨a, g, ep⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [epochEncodedLenPinnedSpec, epochEncodedLenSpec, withVmPreserved] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, hpost⟩
    refine ⟨hvm, ?_⟩
    simp only [CryptoVerification.SpqrV1.ProtoRepr.epochEncodedLenSpec,
      chainEpochPBAt_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

def EpochEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_171).rebase (blkPl_171).base (Rust.withPanics ext))
    (blkPl_171).base (epochEncodedLenPinnedSpec A)

def EpochEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_171).rebase (blkPl_171).base (Rust.withPanics ext))
    (blkPl_171).base (epochEncodedLenSpec A)

def EpochEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_171).rebase (blkPl_171).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_171).base (epochEncodedLenPinnedSpec A)

def EpochEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_171).rebase (blkPl_171).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_171).base (epochEncodedLenSpec A)

def EpochEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_399).rebase (blkPl_399).base (Rust.withPanics ext))
    (blkPl_399).base (epochEncodedLenPinnedSpec A)

def EpochEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_399).rebase (blkPl_399).base (Rust.withPanics ext))
    (blkPl_399).base (epochEncodedLenSpec A)

def EpochEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_399).rebase (blkPl_399).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_399).base (epochEncodedLenPinnedSpec A)

def EpochEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_399).rebase (blkPl_399).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_399).base (epochEncodedLenSpec A)

theorem epochEncodedLen_local1_pinned_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : EpochEncodedLenLocal1PinnedPlacedOkExt A ext :=
  ls_subroutine_ok_plain_vmPreserved (i := 171) (by decide +kernel)
    (hok := epochEncodedLen_entry_pinned_ok _ A _
      (Or.inr ⟨inst, hooksException (Rust.withPanics ext), Or.inl ⟨rfl, rfl⟩⟩))

theorem epochEncodedLen_local1_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : EpochEncodedLenLocal1PlacedOkExt A ext :=
  epochEncodedLen_ok_of_pinned (epochEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem epochEncodedLen_local1_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    EpochEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  epochEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem epochEncodedLen_local1_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    EpochEncodedLenLocal1PlacedOk C A ctl abs :=
  epochEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem epochEncodedLen_local2_pinned_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : EpochEncodedLenLocal2PinnedPlacedOkExt A ext :=
  ls_subroutine_ok_plain_vmPreserved (i := 399) (by decide +kernel)
    (hok := epochEncodedLen_entry_pinned_ok _ A _
      (Or.inr ⟨inst, hooksException (Rust.withPanics ext), Or.inr ⟨rfl, rfl⟩⟩))

theorem epochEncodedLen_local2_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : EpochEncodedLenLocal2PlacedOkExt A ext :=
  epochEncodedLen_ok_of_pinned (epochEncodedLen_local2_pinned_placed_ok_ext A ext)

theorem epochEncodedLen_local2_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    EpochEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  epochEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem epochEncodedLen_local2_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    EpochEncodedLenLocal2PlacedOk C A ctl abs :=
  epochEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

end LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLenBudget
