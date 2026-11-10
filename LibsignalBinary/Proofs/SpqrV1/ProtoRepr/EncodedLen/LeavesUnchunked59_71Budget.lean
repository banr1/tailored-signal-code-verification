/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71

/-!
# `VmPreserved` Placed Verification of 59- and 71-Instruction Unchunked `encoded_len` Leaves

Unpinning bridges and `[LibsignalPlacement]` `subroutine_ok` theorems with `VmPreserved` for
`KeysUnsampled`, `NoHeaderReceived`, `Ct2Sent`, `EkSent`, and `HeaderReceived` (`[local#1, #2]`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71Budget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalPlacement blkPC_163 blkPl_163 blkPC_172 blkPl_172 blkPC_175 blkPl_175
   blkPC_189 blkPl_189 blkPC_193 blkPl_193 blkPC_389 blkPl_389 blkPC_400 blkPl_400
   blkPC_404 blkPl_404 blkPC_415 blkPl_415 blkPC_424 blkPl_424)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SpqrV1.ProtoRepr
  (unchunked2At_eq_exists_pinned unchunked3At_eq_exists_pinned
   unchunked59_entry_pinned_ok unchunked71_entry_pinned_ok)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetExterns)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
  (withVmPreserved ls_subroutine_ok_plain_vmPreserved)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsBudget
  (unchunked2EncodedLenPinnedSpec unchunked2EncodedLenSpec
   unchunked3EncodedLenPinnedSpec unchunked3EncodedLenSpec
   keysUnsampledEncodedLenPinnedSpec keysUnsampledEncodedLenSpec
   noHeaderReceivedEncodedLenPinnedSpec noHeaderReceivedEncodedLenSpec
   ct2SentEncodedLenPinnedSpec ct2SentEncodedLenSpec
   ekSentEncodedLenPinnedSpec ekSentEncodedLenSpec
   headerReceivedEncodedLenPinnedSpec headerReceivedEncodedLenSpec)

private theorem subroutine_ok_repack {G1 G2 : Type} {prog : Program} {entry : BitVec 64}
    {S1 : Spec G1} {S2 : Spec G2} (f : G2 → G1)
    (hpre : ∀ x s, S2.pre x s = S1.pre (f x) s)
    (hpost : ∀ x s0 sf, S2.post x s0 sf = S1.post (f x) s0 sf)
    (hok : subroutine_ok prog entry S1)
    (honPanic : ∀ x s0 sf, S2.onPanic x s0 sf = S1.onPanic (f x) s0 sf := by intros; rfl)
    (honExit : ∀ x c s0 sf, S2.onExit x c s0 sf = S1.onExit (f x) c s0 sf := by intros; rfl)
    (honOom : ∀ x s0 sf, S2.onOom x s0 sf = S1.onOom (f x) s0 sf := by intros; rfl) :
    subroutine_ok prog entry S2 := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre0 hsp => ?_
  rw [hpre] at hpre0
  refine hok.mono_outcome (f x) R s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost0⟩ | ⟨hpan, hmpan⟩ | ⟨code, hex, hmex⟩ | ⟨hoom, hmoom⟩
  · rw [← hpost] at hpost0; exact Or.inl ⟨hret, hcc, hpost0⟩
  · rw [← honPanic] at hmpan; exact Or.inr (Or.inl ⟨hpan, hmpan⟩)
  · rw [← honExit] at hmex; exact Or.inr (Or.inr (Or.inl ⟨code, hex, hmex⟩))
  · rw [← honOom] at hmoom; exact Or.inr (Or.inr (Or.inr ⟨hoom, hmoom⟩))

/-! ## Part 1: 59-Instruction Group (`KeysUnsampled`, `NoHeaderReceived`, `Ct2Sent`) -/

theorem unchunked2EncodedLen_ok_of_pinned {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (unchunked2EncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (unchunked2EncodedLenSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨a, epoch, auth⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [unchunked2EncodedLenSpec, withVmPreserved] at hpre
  simp only [CryptoVerification.SpqrV1.ProtoRepr.unchunked2EncodedLenSpec,
    unchunked2At_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨a, g, epoch, auth⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [unchunked2EncodedLenPinnedSpec, unchunked2EncodedLenSpec,
      withVmPreserved] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, hpost⟩
    refine ⟨hvm, ?_⟩
    simp only [CryptoVerification.SpqrV1.ProtoRepr.unchunked2EncodedLenSpec,
      unchunked2At_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-! ### `KeysUnsampled` (Blocks `172`, `400`) -/

def KeysUnsampledEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_172).rebase (blkPl_172).base (Rust.withPanics ext))
    (blkPl_172).base (keysUnsampledEncodedLenPinnedSpec A)

def KeysUnsampledEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_172).rebase (blkPl_172).base (Rust.withPanics ext))
    (blkPl_172).base (keysUnsampledEncodedLenSpec A)

def KeysUnsampledEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_172).rebase (blkPl_172).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_172).base (keysUnsampledEncodedLenPinnedSpec A)

def KeysUnsampledEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_172).rebase (blkPl_172).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_172).base (keysUnsampledEncodedLenSpec A)

def KeysUnsampledEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_400).rebase (blkPl_400).base (Rust.withPanics ext))
    (blkPl_400).base (keysUnsampledEncodedLenPinnedSpec A)

def KeysUnsampledEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_400).rebase (blkPl_400).base (Rust.withPanics ext))
    (blkPl_400).base (keysUnsampledEncodedLenSpec A)

def KeysUnsampledEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_400).rebase (blkPl_400).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_400).base (keysUnsampledEncodedLenPinnedSpec A)

def KeysUnsampledEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_400).rebase (blkPl_400).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_400).base (keysUnsampledEncodedLenSpec A)

theorem keysUnsampledEncodedLen_local1_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_172).rebase (blkPl_172).base H)
      (blkPl_172).base (keysUnsampledEncodedLenPinnedSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (ls_subroutine_ok_plain_vmPreserved (i := 172) (by decide +kernel)
      (hok := unchunked59_entry_pinned_ok _ A _
        (Or.inr ⟨inst, hooksException H, Or.inl ⟨rfl, rfl⟩⟩)))

theorem keysUnsampledEncodedLen_local1_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_172).rebase (blkPl_172).base H)
      (blkPl_172).base (keysUnsampledEncodedLenSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked2EncodedLen_ok_of_pinned
      (ls_subroutine_ok_plain_vmPreserved (i := 172) (by decide +kernel)
        (hok := unchunked59_entry_pinned_ok _ A _
          (Or.inr ⟨‹_›, hooksException H, Or.inl ⟨rfl, rfl⟩⟩))))

theorem keysUnsampledEncodedLen_local1_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    KeysUnsampledEncodedLenLocal1PinnedPlacedOkExt A ext :=
  keysUnsampledEncodedLen_local1_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem keysUnsampledEncodedLen_local1_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    KeysUnsampledEncodedLenLocal1PlacedOkExt A ext :=
  keysUnsampledEncodedLen_local1_placed_ok_hooks A (Rust.withPanics ext)

theorem keysUnsampledEncodedLen_local1_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    KeysUnsampledEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  keysUnsampledEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem keysUnsampledEncodedLen_local1_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    KeysUnsampledEncodedLenLocal1PlacedOk C A ctl abs :=
  keysUnsampledEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem keysUnsampledEncodedLen_local2_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_400).rebase (blkPl_400).base H)
      (blkPl_400).base (keysUnsampledEncodedLenPinnedSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (ls_subroutine_ok_plain_vmPreserved (i := 400) (by decide +kernel)
      (hok := unchunked59_entry_pinned_ok _ A _
        (Or.inr ⟨inst, hooksException H, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)))

theorem keysUnsampledEncodedLen_local2_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_400).rebase (blkPl_400).base H)
      (blkPl_400).base (keysUnsampledEncodedLenSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked2EncodedLen_ok_of_pinned
      (ls_subroutine_ok_plain_vmPreserved (i := 400) (by decide +kernel)
        (hok := unchunked59_entry_pinned_ok _ A _
          (Or.inr ⟨‹_›, hooksException H, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩))))

theorem keysUnsampledEncodedLen_local2_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    KeysUnsampledEncodedLenLocal2PinnedPlacedOkExt A ext :=
  keysUnsampledEncodedLen_local2_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem keysUnsampledEncodedLen_local2_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    KeysUnsampledEncodedLenLocal2PlacedOkExt A ext :=
  keysUnsampledEncodedLen_local2_placed_ok_hooks A (Rust.withPanics ext)

theorem keysUnsampledEncodedLen_local2_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    KeysUnsampledEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  keysUnsampledEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem keysUnsampledEncodedLen_local2_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    KeysUnsampledEncodedLenLocal2PlacedOk C A ctl abs :=
  keysUnsampledEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

/-! ### `NoHeaderReceived` (Blocks `193`, `424`) -/

def NoHeaderReceivedEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_193).rebase (blkPl_193).base (Rust.withPanics ext))
    (blkPl_193).base (noHeaderReceivedEncodedLenPinnedSpec A)

def NoHeaderReceivedEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_193).rebase (blkPl_193).base (Rust.withPanics ext))
    (blkPl_193).base (noHeaderReceivedEncodedLenSpec A)

def NoHeaderReceivedEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_193).rebase (blkPl_193).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_193).base (noHeaderReceivedEncodedLenPinnedSpec A)

def NoHeaderReceivedEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_193).rebase (blkPl_193).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_193).base (noHeaderReceivedEncodedLenSpec A)

def NoHeaderReceivedEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_424).rebase (blkPl_424).base (Rust.withPanics ext))
    (blkPl_424).base (noHeaderReceivedEncodedLenPinnedSpec A)

def NoHeaderReceivedEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_424).rebase (blkPl_424).base (Rust.withPanics ext))
    (blkPl_424).base (noHeaderReceivedEncodedLenSpec A)

def NoHeaderReceivedEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_424).rebase (blkPl_424).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_424).base (noHeaderReceivedEncodedLenPinnedSpec A)

def NoHeaderReceivedEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_424).rebase (blkPl_424).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_424).base (noHeaderReceivedEncodedLenSpec A)

theorem noHeaderReceivedEncodedLen_local1_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_193).rebase (blkPl_193).base H)
      (blkPl_193).base (noHeaderReceivedEncodedLenPinnedSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (ls_subroutine_ok_plain_vmPreserved (i := 193) (by decide +kernel)
      (hok := unchunked59_entry_pinned_ok _ A _
        (Or.inr ⟨inst, hooksException H, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)))

theorem noHeaderReceivedEncodedLen_local1_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_193).rebase (blkPl_193).base H)
      (blkPl_193).base (noHeaderReceivedEncodedLenSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked2EncodedLen_ok_of_pinned
      (ls_subroutine_ok_plain_vmPreserved (i := 193) (by decide +kernel)
        (hok := unchunked59_entry_pinned_ok _ A _
          (Or.inr ⟨‹_›, hooksException H, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩))))

theorem noHeaderReceivedEncodedLen_local1_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    NoHeaderReceivedEncodedLenLocal1PinnedPlacedOkExt A ext :=
  noHeaderReceivedEncodedLen_local1_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem noHeaderReceivedEncodedLen_local1_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    NoHeaderReceivedEncodedLenLocal1PlacedOkExt A ext :=
  noHeaderReceivedEncodedLen_local1_placed_ok_hooks A (Rust.withPanics ext)

theorem noHeaderReceivedEncodedLen_local1_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    NoHeaderReceivedEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  noHeaderReceivedEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem noHeaderReceivedEncodedLen_local1_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    NoHeaderReceivedEncodedLenLocal1PlacedOk C A ctl abs :=
  noHeaderReceivedEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem noHeaderReceivedEncodedLen_local2_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_424).rebase (blkPl_424).base H)
      (blkPl_424).base (noHeaderReceivedEncodedLenPinnedSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (ls_subroutine_ok_plain_vmPreserved (i := 424) (by decide +kernel)
      (hok := unchunked59_entry_pinned_ok _ A _
        (Or.inr ⟨inst, hooksException H, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩)))

theorem noHeaderReceivedEncodedLen_local2_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_424).rebase (blkPl_424).base H)
      (blkPl_424).base (noHeaderReceivedEncodedLenSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked2EncodedLen_ok_of_pinned
      (ls_subroutine_ok_plain_vmPreserved (i := 424) (by decide +kernel)
        (hok := unchunked59_entry_pinned_ok _ A _
          (Or.inr ⟨‹_›, hooksException H, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩))))

theorem noHeaderReceivedEncodedLen_local2_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    NoHeaderReceivedEncodedLenLocal2PinnedPlacedOkExt A ext :=
  noHeaderReceivedEncodedLen_local2_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem noHeaderReceivedEncodedLen_local2_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    NoHeaderReceivedEncodedLenLocal2PlacedOkExt A ext :=
  noHeaderReceivedEncodedLen_local2_placed_ok_hooks A (Rust.withPanics ext)

theorem noHeaderReceivedEncodedLen_local2_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    NoHeaderReceivedEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  noHeaderReceivedEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem noHeaderReceivedEncodedLen_local2_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    NoHeaderReceivedEncodedLenLocal2PlacedOk C A ctl abs :=
  noHeaderReceivedEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

/-! ### `Ct2Sent` (Blocks `163`, `389`) -/

def Ct2SentEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_163).rebase (blkPl_163).base (Rust.withPanics ext))
    (blkPl_163).base (ct2SentEncodedLenPinnedSpec A)

def Ct2SentEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_163).rebase (blkPl_163).base (Rust.withPanics ext))
    (blkPl_163).base (ct2SentEncodedLenSpec A)

def Ct2SentEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_163).rebase (blkPl_163).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_163).base (ct2SentEncodedLenPinnedSpec A)

def Ct2SentEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_163).rebase (blkPl_163).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_163).base (ct2SentEncodedLenSpec A)

def Ct2SentEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_389).rebase (blkPl_389).base (Rust.withPanics ext))
    (blkPl_389).base (ct2SentEncodedLenPinnedSpec A)

def Ct2SentEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_389).rebase (blkPl_389).base (Rust.withPanics ext))
    (blkPl_389).base (ct2SentEncodedLenSpec A)

def Ct2SentEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_389).rebase (blkPl_389).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_389).base (ct2SentEncodedLenPinnedSpec A)

def Ct2SentEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_389).rebase (blkPl_389).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_389).base (ct2SentEncodedLenSpec A)

theorem ct2SentEncodedLen_local1_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_163).rebase (blkPl_163).base H)
      (blkPl_163).base (ct2SentEncodedLenPinnedSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (ls_subroutine_ok_plain_vmPreserved (i := 163) (by decide +kernel)
      (hok := unchunked59_entry_pinned_ok _ A _
        (Or.inr ⟨inst, hooksException H, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩)))

theorem ct2SentEncodedLen_local1_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_163).rebase (blkPl_163).base H)
      (blkPl_163).base (ct2SentEncodedLenSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked2EncodedLen_ok_of_pinned
      (ls_subroutine_ok_plain_vmPreserved (i := 163) (by decide +kernel)
        (hok := unchunked59_entry_pinned_ok _ A _
          (Or.inr ⟨‹_›, hooksException H,
            Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩))))

theorem ct2SentEncodedLen_local1_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    Ct2SentEncodedLenLocal1PinnedPlacedOkExt A ext :=
  ct2SentEncodedLen_local1_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem ct2SentEncodedLen_local1_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    Ct2SentEncodedLenLocal1PlacedOkExt A ext :=
  ct2SentEncodedLen_local1_placed_ok_hooks A (Rust.withPanics ext)

theorem ct2SentEncodedLen_local1_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    Ct2SentEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  ct2SentEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem ct2SentEncodedLen_local1_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    Ct2SentEncodedLenLocal1PlacedOk C A ctl abs :=
  ct2SentEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem ct2SentEncodedLen_local2_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_389).rebase (blkPl_389).base H)
      (blkPl_389).base (ct2SentEncodedLenPinnedSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (ls_subroutine_ok_plain_vmPreserved (i := 389) (by decide +kernel)
      (hok := unchunked59_entry_pinned_ok _ A _
        (Or.inr ⟨inst, hooksException H, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))⟩)))

theorem ct2SentEncodedLen_local2_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_389).rebase (blkPl_389).base H)
      (blkPl_389).base (ct2SentEncodedLenSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked2EncodedLen_ok_of_pinned
      (ls_subroutine_ok_plain_vmPreserved (i := 389) (by decide +kernel)
        (hok := unchunked59_entry_pinned_ok _ A _
          (Or.inr ⟨‹_›, hooksException H,
            Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))⟩))))

theorem ct2SentEncodedLen_local2_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    Ct2SentEncodedLenLocal2PinnedPlacedOkExt A ext :=
  ct2SentEncodedLen_local2_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem ct2SentEncodedLen_local2_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    Ct2SentEncodedLenLocal2PlacedOkExt A ext :=
  ct2SentEncodedLen_local2_placed_ok_hooks A (Rust.withPanics ext)

theorem ct2SentEncodedLen_local2_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    Ct2SentEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  ct2SentEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem ct2SentEncodedLen_local2_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    Ct2SentEncodedLenLocal2PlacedOk C A ctl abs :=
  ct2SentEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

/-! ## Part 2: 71-Instruction Group (`EkSent`, `HeaderReceived`) -/

theorem unchunked3EncodedLen_ok_of_pinned {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (unchunked3EncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (unchunked3EncodedLenSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨a, epoch, auth, f3⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [unchunked3EncodedLenSpec, withVmPreserved] at hpre
  simp only [CryptoVerification.SpqrV1.ProtoRepr.unchunked3EncodedLenSpec,
    unchunked3At_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨a, g, epoch, auth, f3⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [unchunked3EncodedLenPinnedSpec, unchunked3EncodedLenSpec,
      withVmPreserved] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, hpost⟩
    refine ⟨hvm, ?_⟩
    simp only [CryptoVerification.SpqrV1.ProtoRepr.unchunked3EncodedLenSpec,
      unchunked3At_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-! ### `EkSent` (Blocks `189`, `415`) -/

def EkSentEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_189).rebase (blkPl_189).base (Rust.withPanics ext))
    (blkPl_189).base (ekSentEncodedLenPinnedSpec A)

def EkSentEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_189).rebase (blkPl_189).base (Rust.withPanics ext))
    (blkPl_189).base (ekSentEncodedLenSpec A)

def EkSentEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_189).rebase (blkPl_189).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_189).base (ekSentEncodedLenPinnedSpec A)

def EkSentEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_189).rebase (blkPl_189).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_189).base (ekSentEncodedLenSpec A)

def EkSentEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_415).rebase (blkPl_415).base (Rust.withPanics ext))
    (blkPl_415).base (ekSentEncodedLenPinnedSpec A)

def EkSentEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_415).rebase (blkPl_415).base (Rust.withPanics ext))
    (blkPl_415).base (ekSentEncodedLenSpec A)

def EkSentEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_415).rebase (blkPl_415).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_415).base (ekSentEncodedLenPinnedSpec A)

def EkSentEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_415).rebase (blkPl_415).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_415).base (ekSentEncodedLenSpec A)

theorem ekSentEncodedLen_local1_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_189).rebase (blkPl_189).base H)
      (blkPl_189).base (ekSentEncodedLenPinnedSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.dk⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (ls_subroutine_ok_plain_vmPreserved (i := 189) (by decide +kernel)
      (hok := unchunked71_entry_pinned_ok _ A _
        (Or.inr ⟨inst, hooksException H, Or.inl ⟨rfl, rfl⟩⟩)))

theorem ekSentEncodedLen_local1_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_189).rebase (blkPl_189).base H)
      (blkPl_189).base (ekSentEncodedLenSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.dk⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked3EncodedLen_ok_of_pinned
      (ls_subroutine_ok_plain_vmPreserved (i := 189) (by decide +kernel)
        (hok := unchunked71_entry_pinned_ok _ A _
          (Or.inr ⟨‹_›, hooksException H, Or.inl ⟨rfl, rfl⟩⟩))))

theorem ekSentEncodedLen_local1_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    EkSentEncodedLenLocal1PinnedPlacedOkExt A ext :=
  ekSentEncodedLen_local1_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem ekSentEncodedLen_local1_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    EkSentEncodedLenLocal1PlacedOkExt A ext :=
  ekSentEncodedLen_local1_placed_ok_hooks A (Rust.withPanics ext)

theorem ekSentEncodedLen_local1_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    EkSentEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  ekSentEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem ekSentEncodedLen_local1_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    EkSentEncodedLenLocal1PlacedOk C A ctl abs :=
  ekSentEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem ekSentEncodedLen_local2_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_415).rebase (blkPl_415).base H)
      (blkPl_415).base (ekSentEncodedLenPinnedSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.dk⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (ls_subroutine_ok_plain_vmPreserved (i := 415) (by decide +kernel)
      (hok := unchunked71_entry_pinned_ok _ A _
        (Or.inr ⟨inst, hooksException H, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)))

theorem ekSentEncodedLen_local2_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_415).rebase (blkPl_415).base H)
      (blkPl_415).base (ekSentEncodedLenSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.dk⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked3EncodedLen_ok_of_pinned
      (ls_subroutine_ok_plain_vmPreserved (i := 415) (by decide +kernel)
        (hok := unchunked71_entry_pinned_ok _ A _
          (Or.inr ⟨‹_›, hooksException H, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩))))

theorem ekSentEncodedLen_local2_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    EkSentEncodedLenLocal2PinnedPlacedOkExt A ext :=
  ekSentEncodedLen_local2_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem ekSentEncodedLen_local2_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    EkSentEncodedLenLocal2PlacedOkExt A ext :=
  ekSentEncodedLen_local2_placed_ok_hooks A (Rust.withPanics ext)

theorem ekSentEncodedLen_local2_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    EkSentEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  ekSentEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem ekSentEncodedLen_local2_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    EkSentEncodedLenLocal2PlacedOk C A ctl abs :=
  ekSentEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

/-! ### `HeaderReceived` (Blocks `175`, `404`) -/

def HeaderReceivedEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_175).rebase (blkPl_175).base (Rust.withPanics ext))
    (blkPl_175).base (headerReceivedEncodedLenPinnedSpec A)

def HeaderReceivedEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_175).rebase (blkPl_175).base (Rust.withPanics ext))
    (blkPl_175).base (headerReceivedEncodedLenSpec A)

def HeaderReceivedEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_175).rebase (blkPl_175).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_175).base (headerReceivedEncodedLenPinnedSpec A)

def HeaderReceivedEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_175).rebase (blkPl_175).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_175).base (headerReceivedEncodedLenSpec A)

def HeaderReceivedEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_404).rebase (blkPl_404).base (Rust.withPanics ext))
    (blkPl_404).base (headerReceivedEncodedLenPinnedSpec A)

def HeaderReceivedEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_404).rebase (blkPl_404).base (Rust.withPanics ext))
    (blkPl_404).base (headerReceivedEncodedLenSpec A)

def HeaderReceivedEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_404).rebase (blkPl_404).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_404).base (headerReceivedEncodedLenPinnedSpec A)

def HeaderReceivedEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_404).rebase (blkPl_404).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_404).base (headerReceivedEncodedLenSpec A)

theorem headerReceivedEncodedLen_local1_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_175).rebase (blkPl_175).base H)
      (blkPl_175).base (headerReceivedEncodedLenPinnedSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.hdr⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (ls_subroutine_ok_plain_vmPreserved (i := 175) (by decide +kernel)
      (hok := unchunked71_entry_pinned_ok _ A _
        (Or.inr ⟨inst, hooksException H, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)))

theorem headerReceivedEncodedLen_local1_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_175).rebase (blkPl_175).base H)
      (blkPl_175).base (headerReceivedEncodedLenSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.hdr⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked3EncodedLen_ok_of_pinned
      (ls_subroutine_ok_plain_vmPreserved (i := 175) (by decide +kernel)
        (hok := unchunked71_entry_pinned_ok _ A _
          (Or.inr ⟨‹_›, hooksException H, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩))))

theorem headerReceivedEncodedLen_local1_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    HeaderReceivedEncodedLenLocal1PinnedPlacedOkExt A ext :=
  headerReceivedEncodedLen_local1_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem headerReceivedEncodedLen_local1_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    HeaderReceivedEncodedLenLocal1PlacedOkExt A ext :=
  headerReceivedEncodedLen_local1_placed_ok_hooks A (Rust.withPanics ext)

theorem headerReceivedEncodedLen_local1_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    HeaderReceivedEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  headerReceivedEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem headerReceivedEncodedLen_local1_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    HeaderReceivedEncodedLenLocal1PlacedOk C A ctl abs :=
  headerReceivedEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem headerReceivedEncodedLen_local2_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_404).rebase (blkPl_404).base H)
      (blkPl_404).base (headerReceivedEncodedLenPinnedSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.hdr⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (ls_subroutine_ok_plain_vmPreserved (i := 404) (by decide +kernel)
      (hok := unchunked71_entry_pinned_ok _ A _
        (Or.inr ⟨inst, hooksException H, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩)))

theorem headerReceivedEncodedLen_local2_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_404).rebase (blkPl_404).base H)
      (blkPl_404).base (headerReceivedEncodedLenSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.hdr⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked3EncodedLen_ok_of_pinned
      (ls_subroutine_ok_plain_vmPreserved (i := 404) (by decide +kernel)
        (hok := unchunked71_entry_pinned_ok _ A _
          (Or.inr ⟨‹_›, hooksException H, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩))))

theorem headerReceivedEncodedLen_local2_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    HeaderReceivedEncodedLenLocal2PinnedPlacedOkExt A ext :=
  headerReceivedEncodedLen_local2_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem headerReceivedEncodedLen_local2_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    HeaderReceivedEncodedLenLocal2PlacedOkExt A ext :=
  headerReceivedEncodedLen_local2_placed_ok_hooks A (Rust.withPanics ext)

theorem headerReceivedEncodedLen_local2_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    HeaderReceivedEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  headerReceivedEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem headerReceivedEncodedLen_local2_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    HeaderReceivedEncodedLenLocal2PlacedOk C A ctl abs :=
  headerReceivedEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

end LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71Budget
