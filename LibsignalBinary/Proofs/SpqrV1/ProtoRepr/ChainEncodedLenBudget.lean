/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLenBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLen

/-!
# `VmPreserved` Placed Verification of `Chain::encoded_len` (Blocks `178`, `406`)

Unpinning bridges and `[LibsignalPlacement]` `subroutine_ok` theorems for `Chain::encoded_len`
(Blocks `178 -> 171` and `406 -> 399`) with `VmPreserved`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLenBudget

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification
  (LibsignalPlacement lsmpl withLsCodeLoaded blkPC_178 blkPl_178 blkPC_406 blkPl_406)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetExterns)
open CryptoVerification.SpqrV1.ProtoRepr
  (withMemPred chainPBAt_eq_exists_pinned
   epochEncodedLen_entry_pinned_ok epochEncodedLen_ok_of_pinned
   chainEncodedLen_entry_pinned_ok)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
  (withVmPreserved LsBlocksCodeLoaded withLsBlocksCodeLoaded
   ls_subroutine_ok_of_block_in ls_subroutine_ok_blocks_vmPreserved
   chainEncodedLenPinnedSpec chainEncodedLenSpec)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLenBaseBudget
  (ChainEncodedLenLocal1PinnedPlacedOkExt ChainEncodedLenLocal1PlacedOkExt
   ChainEncodedLenLocal1PinnedPlacedOk ChainEncodedLenLocal1PlacedOk
   ChainEncodedLenLocal2PinnedPlacedOkExt ChainEncodedLenLocal2PlacedOkExt
   ChainEncodedLenLocal2PinnedPlacedOk ChainEncodedLenLocal2PlacedOk)

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

theorem chainEncodedLen_ok_of_pinned {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (chainEncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (chainEncodedLenSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨a, ch⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [chainEncodedLenSpec, withVmPreserved] at hpre
  simp only [CryptoVerification.SpqrV1.ProtoRepr.chainEncodedLenSpec,
    chainPBAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨a, g, ch⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [chainEncodedLenPinnedSpec, chainEncodedLenSpec, withVmPreserved] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, hpost⟩
    refine ⟨hvm, ?_⟩
    simp only [CryptoVerification.SpqrV1.ProtoRepr.chainEncodedLenSpec,
      chainPBAt_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem chainEncodedLen_withMemPred_ok_of_pinned {prog : Program} {entry : BitVec 64}
    {Φ : Memory → Prop} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (withMemPred Φ (chainEncodedLenPinnedSpec A))) :
    subroutine_ok prog entry (withMemPred Φ (chainEncodedLenSpec A)) := by
  refine subroutine_ok_outcome_intro fun ⟨a, ch⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withMemPred, chainEncodedLenSpec, withVmPreserved] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hΦ0, hpre⟩
  simp only [CryptoVerification.SpqrV1.ProtoRepr.chainEncodedLenSpec,
    chainPBAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  have hpre' : s0.mem ⊨ (withMemPred Φ (chainEncodedLenPinnedSpec A)).pre ⟨a, g, ch⟩ s0 ∗ R := by
    dsimp only [withMemPred, chainEncodedLenPinnedSpec, withVmPreserved]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hΦ0, hpre⟩
  refine hpinned.mono_outcome ⟨a, g, ch⟩ R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withMemPred, chainEncodedLenPinnedSpec, chainEncodedLenSpec,
      withVmPreserved] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, hpost⟩
    refine ⟨hvm, ?_⟩
    simp only [CryptoVerification.SpqrV1.ProtoRepr.chainEncodedLenSpec,
      chainPBAt_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem chainEncodedLen_lscl_ok_of_pinned {prog : Program} {entry : BitVec 64}
    {pl : MultiPlacement} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (withLsCodeLoaded pl (chainEncodedLenPinnedSpec A))) :
    subroutine_ok prog entry (withLsCodeLoaded pl (chainEncodedLenSpec A)) := by
  refine subroutine_ok_outcome_intro fun ⟨a, ch⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded, chainEncodedLenSpec, withVmPreserved] at hpre
  simp only [CryptoVerification.SpqrV1.ProtoRepr.chainEncodedLenSpec,
    chainPBAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨a, g, ch⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, chainEncodedLenPinnedSpec, chainEncodedLenSpec,
      withVmPreserved] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, hpost⟩
    refine ⟨hvm, ?_⟩
    simp only [CryptoVerification.SpqrV1.ProtoRepr.chainEncodedLenSpec,
      chainPBAt_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem chainEncodedLen_local1_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_178).rebase (blkPl_178).base H)
      (blkPl_178).base (withLsCodeLoaded lsmpl (chainEncodedLenPinnedSpec A)) :=
  ls_subroutine_ok_blocks_vmPreserved (blks := [178, 171]) (i := 178)
    (by decide) (by decide) (by decide +kernel)
    (hok := withLsBlocksCodeLoaded_of_withMemPred
      (chainEncodedLen_entry_pinned_ok _ A _ _
        (fun _ _ h hk => h.of_keepsFrozen hk)
        (Or.inr ⟨inst, hooksException H, Or.inl ⟨rfl, rfl, rfl⟩⟩)
        (withMemPred_of_withLsBlocksCodeLoaded
          (ls_subroutine_ok_of_block_in (blks := [178, 171]) (i := 178) (j := 171) (by decide)
            (epochEncodedLen_ok_of_pinned
              (epochEncodedLen_entry_pinned_ok _ A _
                (Or.inr ⟨inst, hooksException H, Or.inl ⟨rfl, rfl⟩⟩)))))))

theorem chainEncodedLen_local1_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_178).rebase (blkPl_178).base H)
      (blkPl_178).base (withLsCodeLoaded lsmpl (chainEncodedLenSpec A)) :=
  chainEncodedLen_lscl_ok_of_pinned (chainEncodedLen_local1_pinned_placed_ok_hooks A H)

theorem chainEncodedLen_local1_pinned_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) :
    ChainEncodedLenLocal1PinnedPlacedOkExt A ext :=
  chainEncodedLen_local1_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem chainEncodedLen_local1_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) :
    ChainEncodedLenLocal1PlacedOkExt A ext :=
  chainEncodedLen_lscl_ok_of_pinned (chainEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem chainEncodedLen_local1_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    ChainEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  chainEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem chainEncodedLen_local1_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    ChainEncodedLenLocal1PlacedOk C A ctl abs :=
  chainEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem chainEncodedLen_local2_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_406).rebase (blkPl_406).base H)
      (blkPl_406).base (withLsCodeLoaded lsmpl (chainEncodedLenPinnedSpec A)) :=
  ls_subroutine_ok_blocks_vmPreserved (blks := [406, 399]) (i := 406)
    (by decide) (by decide) (by decide +kernel)
    (hok := withLsBlocksCodeLoaded_of_withMemPred
      (chainEncodedLen_entry_pinned_ok _ A _ _
        (fun _ _ h hk => h.of_keepsFrozen hk)
        (Or.inr ⟨inst, hooksException H, Or.inr ⟨rfl, rfl, rfl⟩⟩)
        (withMemPred_of_withLsBlocksCodeLoaded
          (ls_subroutine_ok_of_block_in (blks := [406, 399]) (i := 406) (j := 399) (by decide)
            (epochEncodedLen_ok_of_pinned
              (epochEncodedLen_entry_pinned_ok _ A _
                (Or.inr ⟨inst, hooksException H, Or.inr ⟨rfl, rfl⟩⟩)))))))

theorem chainEncodedLen_local2_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_406).rebase (blkPl_406).base H)
      (blkPl_406).base (withLsCodeLoaded lsmpl (chainEncodedLenSpec A)) :=
  chainEncodedLen_lscl_ok_of_pinned (chainEncodedLen_local2_pinned_placed_ok_hooks A H)

theorem chainEncodedLen_local2_pinned_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) :
    ChainEncodedLenLocal2PinnedPlacedOkExt A ext :=
  chainEncodedLen_local2_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem chainEncodedLen_local2_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) :
    ChainEncodedLenLocal2PlacedOkExt A ext :=
  chainEncodedLen_lscl_ok_of_pinned (chainEncodedLen_local2_pinned_placed_ok_ext A ext)

theorem chainEncodedLen_local2_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    ChainEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  chainEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem chainEncodedLen_local2_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    ChainEncodedLenLocal2PlacedOk C A ctl abs :=
  chainEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

end LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLenBudget
