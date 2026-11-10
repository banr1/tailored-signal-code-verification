/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLenBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.ChainEncodedLenBasePlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.ChainEncodedLenPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EpochEncodedLenPlacedBudget

/-!
# `VmPreserved` Placed Proofs for `Chain::encoded_len` (Blocks `485` and `406`)

Lifts `Chain::encoded_len` `[LibsignalPlacement]` contracts to `DefsBudget.chainEncodedLen{Pinned,}Spec`
with `VmPreserved` on CLI Blocks `485` (`[local#3]`) and `406` (`[local#2]`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.ChainEncodedLenPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded blkPC_406 blkPl_406)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetExterns)
open CryptoVerification.SpqrV1.ProtoRepr (withMemPred)
open CryptoVerification.Cli.SpqrV1.ProtoRepr (chainEncodedLen_entry_pinned_placed_ok)
open CryptoVerification.Cli.SpqrV1.ProtoRepr.Placed (lsProg_485 blkPl_485)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
  (LsBlocksCodeLoaded withLsBlocksCodeLoaded
   ls_subroutine_ok_of_block_in ls_subroutine_ok_blocks_vmPreserved
   chainEncodedLenPinnedSpec chainEncodedLenSpec)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLenBaseBudget
  (ChainEncodedLenLocal2PinnedPlacedOkExt ChainEncodedLenLocal2PlacedOkExt
   ChainEncodedLenLocal2PinnedPlacedOk ChainEncodedLenLocal2PlacedOk)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLenBudget
  (chainEncodedLen_lscl_ok_of_pinned
   chainEncodedLen_local2_pinned_placed_ok_hooks chainEncodedLen_local2_placed_ok_hooks)
open LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.ChainEncodedLenBasePlacedBudget
  (ChainEncodedLenLocal1PinnedPlacedOkX ChainEncodedLenLocal1PlacedOkX
   ChainEncodedLenLocal1PinnedPlacedOkExt ChainEncodedLenLocal1PlacedOkExt
   ChainEncodedLenLocal1PinnedPlacedOk ChainEncodedLenLocal1PlacedOk)

private theorem withLsBlocksCodeLoaded_of_withMemPred {α : Type} {prog : Program}
    {entry : BitVec 64} {blks : List Nat} {pl : MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry (withMemPred (LsBlocksCodeLoaded blks pl) spec)) :
    subroutine_ok prog entry (withLsBlocksCodeLoaded blks pl spec) :=
  h

private theorem withMemPred_of_withLsBlocksCodeLoaded {α : Type} {prog : Program}
    {entry : BitVec 64} {blks : List Nat} {pl : MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsBlocksCodeLoaded blks pl spec)) :
    subroutine_ok prog entry (withMemPred (LsBlocksCodeLoaded blks pl) spec) :=
  h

/-! ## Block `485` (`[local#3]`) and Block `406` (`[local#2]`) Placed Corollaries -/

theorem chainEncodedLen_local1_pinned_placed_ok_x [inst : LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) :
    ChainEncodedLenLocal1PinnedPlacedOkX A H :=
  ls_subroutine_ok_blocks_vmPreserved
    (progQ := lsProg_485 (hooksException H))
    (blks := [485, 478]) (i := 485)
    (by decide) (by decide) (by decide +kernel)
    (hok := withLsBlocksCodeLoaded_of_withMemPred
      (chainEncodedLen_entry_pinned_placed_ok _ A _ _
        (fun _ _ h hk => h.of_keepsFrozen hk)
        ⟨inst, hooksException H, rfl, rfl, rfl⟩
        (withMemPred_of_withLsBlocksCodeLoaded
          (ls_subroutine_ok_of_block_in (callerProg := lsProg_485 (hooksException H))
            (blks := [485, 478]) (i := 485) (j := 478) (by decide)
            (CryptoVerification.Cli.SpqrV1.ProtoRepr.epochEncodedLen_local1_placed_ok_x
              A (hooksException H))))))

theorem chainEncodedLen_local1_placed_ok_x [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) :
    ChainEncodedLenLocal1PlacedOkX A H :=
  chainEncodedLen_lscl_ok_of_pinned (chainEncodedLen_local1_pinned_placed_ok_x A H)

theorem chainEncodedLen_local1_pinned_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) :
    ChainEncodedLenLocal1PinnedPlacedOkExt A ext :=
  chainEncodedLen_local1_pinned_placed_ok_x A (Rust.withPanics ext)

theorem chainEncodedLen_local1_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) :
    ChainEncodedLenLocal1PlacedOkExt A ext :=
  chainEncodedLen_local1_placed_ok_x A (Rust.withPanics ext)

theorem chainEncodedLen_local1_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    ChainEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  chainEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem chainEncodedLen_local1_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    ChainEncodedLenLocal1PlacedOk C A ctl abs :=
  chainEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem chainEncodedLen_local2_pinned_placed_ok_x [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_406).rebase (blkPl_406).base H)
      (blkPl_406).base (withLsCodeLoaded lsmpl (chainEncodedLenPinnedSpec A)) :=
  chainEncodedLen_local2_pinned_placed_ok_hooks A H

theorem chainEncodedLen_local2_placed_ok_x [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_406).rebase (blkPl_406).base H)
      (blkPl_406).base (withLsCodeLoaded lsmpl (chainEncodedLenSpec A)) :=
  chainEncodedLen_local2_placed_ok_hooks A H

theorem chainEncodedLen_local2_pinned_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) :
    ChainEncodedLenLocal2PinnedPlacedOkExt A ext :=
  LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLenBudget.chainEncodedLen_local2_pinned_placed_ok_ext A ext

theorem chainEncodedLen_local2_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) :
    ChainEncodedLenLocal2PlacedOkExt A ext :=
  LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLenBudget.chainEncodedLen_local2_placed_ok_ext A ext

theorem chainEncodedLen_local2_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    ChainEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLenBudget.chainEncodedLen_local2_pinned_placed_ok C A ctl abs

theorem chainEncodedLen_local2_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    ChainEncodedLenLocal2PlacedOk C A ctl abs :=
  LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLenBudget.chainEncodedLen_local2_placed_ok C A ctl abs

end LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.ChainEncodedLenPlacedBudget
