/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EpochEncodedLenPlaced
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLenBudget

/-!
# `VmPreserved` Placed Proofs for `Epoch::encoded_len` (Blocks `478` and `399`)

Lifts `[LibsignalPlacement]` `Epoch::encoded_len` contracts to `VmPreserved` on CLI Blocks `478`
(`[local#3]`) and `399` (`[local#2]`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EpochEncodedLenPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (LibsignalPlacement blkPC_399 blkPl_399)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetExterns)
open CryptoVerification.Cli.SpqrV1.ProtoRepr.Placed (lsProg_478 blkPl_478)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
  (ls_subroutine_ok_plain_vmPreserved epochEncodedLenPinnedSpec epochEncodedLenSpec)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLenBudget
  (epochEncodedLen_ok_of_pinned
   EpochEncodedLenLocal2PinnedPlacedOkExt EpochEncodedLenLocal2PlacedOkExt
   EpochEncodedLenLocal2PinnedPlacedOk EpochEncodedLenLocal2PlacedOk)

def EpochEncodedLenLocal1PinnedPlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_478 H) (blkPl_478).base (epochEncodedLenPinnedSpec A)

def EpochEncodedLenLocal1PlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_478 H) (blkPl_478).base (epochEncodedLenSpec A)

def EpochEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_478 (Rust.withPanics ext)) (blkPl_478).base
    (epochEncodedLenPinnedSpec A)

def EpochEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_478 (Rust.withPanics ext)) (blkPl_478).base
    (epochEncodedLenSpec A)

def EpochEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_478 (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_478).base (epochEncodedLenPinnedSpec A)

def EpochEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_478 (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_478).base (epochEncodedLenSpec A)

theorem epochEncodedLen_local1_pinned_placed_ok_x [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : EpochEncodedLenLocal1PinnedPlacedOkX A H :=
  ls_subroutine_ok_plain_vmPreserved (i := 478) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.epochEncodedLen_local1_pinned_placed_ok_x
      A (hooksException H))

theorem epochEncodedLen_local1_placed_ok_x [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : EpochEncodedLenLocal1PlacedOkX A H :=
  epochEncodedLen_ok_of_pinned (epochEncodedLen_local1_pinned_placed_ok_x A H)

theorem epochEncodedLen_local1_pinned_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : EpochEncodedLenLocal1PinnedPlacedOkExt A ext :=
  epochEncodedLen_local1_pinned_placed_ok_x A (Rust.withPanics ext)

theorem epochEncodedLen_local1_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : EpochEncodedLenLocal1PlacedOkExt A ext :=
  epochEncodedLen_local1_placed_ok_x A (Rust.withPanics ext)

theorem epochEncodedLen_local1_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    EpochEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  epochEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem epochEncodedLen_local1_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    EpochEncodedLenLocal1PlacedOk C A ctl abs :=
  epochEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem epochEncodedLen_local2_pinned_placed_ok_x [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_399).rebase (blkPl_399).base H) (blkPl_399).base
      (epochEncodedLenPinnedSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 399) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.epochEncodedLen_local2_pinned_placed_ok_x
      A (hooksException H))

theorem epochEncodedLen_local2_placed_ok_x [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_399).rebase (blkPl_399).base H) (blkPl_399).base
      (epochEncodedLenSpec A) :=
  epochEncodedLen_ok_of_pinned (epochEncodedLen_local2_pinned_placed_ok_x A H)

theorem epochEncodedLen_local2_pinned_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : EpochEncodedLenLocal2PinnedPlacedOkExt A ext :=
  LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLenBudget.epochEncodedLen_local2_pinned_placed_ok_ext
    A ext

theorem epochEncodedLen_local2_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : EpochEncodedLenLocal2PlacedOkExt A ext :=
  LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLenBudget.epochEncodedLen_local2_placed_ok_ext
    A ext

theorem epochEncodedLen_local2_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    EpochEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLenBudget.epochEncodedLen_local2_pinned_placed_ok
    C A ctl abs

theorem epochEncodedLen_local2_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    EpochEncodedLenLocal2PlacedOk C A ctl abs :=
  LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLenBudget.epochEncodedLen_local2_placed_ok
    C A ctl abs

end LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EpochEncodedLenPlacedBudget
