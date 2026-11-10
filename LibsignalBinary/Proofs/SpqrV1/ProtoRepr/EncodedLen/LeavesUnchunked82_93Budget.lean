/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93

/-!
# `VmPreserved` Placed Verification of 82- and 93-Instruction Unchunked `encoded_len` Leaves

Unpinning bridges and `[LibsignalPlacement]` `subroutine_ok` theorems with `VmPreserved` for
`HeaderSent`, `EkSentCt1Received`, `Ct1Sent`, and `Ct1SentEkReceived` (`[local#1, #2]`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93Budget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalPlacement blkPC_162 blkPl_162 blkPC_180 blkPl_180 blkPC_185 blkPl_185
   blkPC_192 blkPl_192 blkPC_387 blkPl_387 blkPC_408 blkPl_408 blkPC_411 blkPl_411
   blkPC_421 blkPl_421)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SpqrV1.ProtoRepr
  (unchunked4At_eq_exists_pinned unchunked5At_eq_exists_pinned
   unchunked82_entry_pinned_ok unchunked93_entry_pinned_ok)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetExterns)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
  (withVmPreserved ls_subroutine_ok_plain_vmPreserved)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsBudget
  (unchunked4EncodedLenPinnedSpec unchunked4EncodedLenSpec
   unchunked5EncodedLenPinnedSpec unchunked5EncodedLenSpec
   headerSentEncodedLenPinnedSpec headerSentEncodedLenSpec
   ekSentCt1ReceivedEncodedLenPinnedSpec ekSentCt1ReceivedEncodedLenSpec
   ct1SentEncodedLenPinnedSpec ct1SentEncodedLenSpec
   ct1SentEkReceivedEncodedLenPinnedSpec ct1SentEkReceivedEncodedLenSpec)

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

/-! ## Part 1: 82-Instruction Group (`HeaderSent`, `EkSentCt1Received`) -/

theorem unchunked4EncodedLen_ok_of_pinned {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (unchunked4EncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (unchunked4EncodedLenSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨a, epoch, auth, f3, f4⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [unchunked4EncodedLenSpec, withVmPreserved] at hpre
  simp only [CryptoVerification.SpqrV1.ProtoRepr.unchunked4EncodedLenSpec,
    unchunked4At_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨a, g, epoch, auth, f3, f4⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [unchunked4EncodedLenPinnedSpec, unchunked4EncodedLenSpec,
      withVmPreserved] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, hpost⟩
    refine ⟨hvm, ?_⟩
    simp only [CryptoVerification.SpqrV1.ProtoRepr.unchunked4EncodedLenSpec,
      unchunked4At_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-! ### `HeaderSent` (Blocks `185`, `411`) -/

def HeaderSentEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_185).rebase (blkPl_185).base (Rust.withPanics ext))
    (blkPl_185).base (headerSentEncodedLenPinnedSpec A)

def HeaderSentEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_185).rebase (blkPl_185).base (Rust.withPanics ext))
    (blkPl_185).base (headerSentEncodedLenSpec A)

def HeaderSentEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_185).rebase (blkPl_185).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_185).base (headerSentEncodedLenPinnedSpec A)

def HeaderSentEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_185).rebase (blkPl_185).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_185).base (headerSentEncodedLenSpec A)

def HeaderSentEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_411).rebase (blkPl_411).base (Rust.withPanics ext))
    (blkPl_411).base (headerSentEncodedLenPinnedSpec A)

def HeaderSentEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_411).rebase (blkPl_411).base (Rust.withPanics ext))
    (blkPl_411).base (headerSentEncodedLenSpec A)

def HeaderSentEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_411).rebase (blkPl_411).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_411).base (headerSentEncodedLenPinnedSpec A)

def HeaderSentEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_411).rebase (blkPl_411).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_411).base (headerSentEncodedLenSpec A)

theorem headerSentEncodedLen_local1_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_185).rebase (blkPl_185).base H)
      (blkPl_185).base (headerSentEncodedLenPinnedSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.ek, x.m.dk⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (ls_subroutine_ok_plain_vmPreserved (i := 185) (by decide +kernel)
      (hok := unchunked82_entry_pinned_ok _ A _
        (Or.inr ⟨inst, hooksException H, Or.inl ⟨rfl, rfl⟩⟩)))

theorem headerSentEncodedLen_local1_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_185).rebase (blkPl_185).base H)
      (blkPl_185).base (headerSentEncodedLenSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.ek, x.m.dk⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked4EncodedLen_ok_of_pinned
      (ls_subroutine_ok_plain_vmPreserved (i := 185) (by decide +kernel)
        (hok := unchunked82_entry_pinned_ok _ A _
          (Or.inr ⟨‹_›, hooksException H, Or.inl ⟨rfl, rfl⟩⟩))))

theorem headerSentEncodedLen_local1_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    HeaderSentEncodedLenLocal1PinnedPlacedOkExt A ext :=
  headerSentEncodedLen_local1_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem headerSentEncodedLen_local1_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    HeaderSentEncodedLenLocal1PlacedOkExt A ext :=
  headerSentEncodedLen_local1_placed_ok_hooks A (Rust.withPanics ext)

theorem headerSentEncodedLen_local1_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    HeaderSentEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  headerSentEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem headerSentEncodedLen_local1_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    HeaderSentEncodedLenLocal1PlacedOk C A ctl abs :=
  headerSentEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem headerSentEncodedLen_local2_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_411).rebase (blkPl_411).base H)
      (blkPl_411).base (headerSentEncodedLenPinnedSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.ek, x.m.dk⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (ls_subroutine_ok_plain_vmPreserved (i := 411) (by decide +kernel)
      (hok := unchunked82_entry_pinned_ok _ A _
        (Or.inr ⟨inst, hooksException H, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)))

theorem headerSentEncodedLen_local2_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_411).rebase (blkPl_411).base H)
      (blkPl_411).base (headerSentEncodedLenSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.ek, x.m.dk⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked4EncodedLen_ok_of_pinned
      (ls_subroutine_ok_plain_vmPreserved (i := 411) (by decide +kernel)
        (hok := unchunked82_entry_pinned_ok _ A _
          (Or.inr ⟨‹_›, hooksException H, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩))))

theorem headerSentEncodedLen_local2_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    HeaderSentEncodedLenLocal2PinnedPlacedOkExt A ext :=
  headerSentEncodedLen_local2_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem headerSentEncodedLen_local2_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    HeaderSentEncodedLenLocal2PlacedOkExt A ext :=
  headerSentEncodedLen_local2_placed_ok_hooks A (Rust.withPanics ext)

theorem headerSentEncodedLen_local2_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    HeaderSentEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  headerSentEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem headerSentEncodedLen_local2_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    HeaderSentEncodedLenLocal2PlacedOk C A ctl abs :=
  headerSentEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

/-! ### `EkSentCt1Received` (Blocks `192`, `421`) -/

def EkSentCt1ReceivedEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_192).rebase (blkPl_192).base (Rust.withPanics ext))
    (blkPl_192).base (ekSentCt1ReceivedEncodedLenPinnedSpec A)

def EkSentCt1ReceivedEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_192).rebase (blkPl_192).base (Rust.withPanics ext))
    (blkPl_192).base (ekSentCt1ReceivedEncodedLenSpec A)

def EkSentCt1ReceivedEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_192).rebase (blkPl_192).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_192).base (ekSentCt1ReceivedEncodedLenPinnedSpec A)

def EkSentCt1ReceivedEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_192).rebase (blkPl_192).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_192).base (ekSentCt1ReceivedEncodedLenSpec A)

def EkSentCt1ReceivedEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_421).rebase (blkPl_421).base (Rust.withPanics ext))
    (blkPl_421).base (ekSentCt1ReceivedEncodedLenPinnedSpec A)

def EkSentCt1ReceivedEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_421).rebase (blkPl_421).base (Rust.withPanics ext))
    (blkPl_421).base (ekSentCt1ReceivedEncodedLenSpec A)

def EkSentCt1ReceivedEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_421).rebase (blkPl_421).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_421).base (ekSentCt1ReceivedEncodedLenPinnedSpec A)

def EkSentCt1ReceivedEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_421).rebase (blkPl_421).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_421).base (ekSentCt1ReceivedEncodedLenSpec A)

theorem ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_192).rebase (blkPl_192).base H)
      (blkPl_192).base (ekSentCt1ReceivedEncodedLenPinnedSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.dk, x.m.ct1⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (ls_subroutine_ok_plain_vmPreserved (i := 192) (by decide +kernel)
      (hok := unchunked82_entry_pinned_ok _ A _
        (Or.inr ⟨inst, hooksException H, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)))

theorem ekSentCt1ReceivedEncodedLen_local1_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_192).rebase (blkPl_192).base H)
      (blkPl_192).base (ekSentCt1ReceivedEncodedLenSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.dk, x.m.ct1⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked4EncodedLen_ok_of_pinned
      (ls_subroutine_ok_plain_vmPreserved (i := 192) (by decide +kernel)
        (hok := unchunked82_entry_pinned_ok _ A _
          (Or.inr ⟨‹_›, hooksException H, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩))))

theorem ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    EkSentCt1ReceivedEncodedLenLocal1PinnedPlacedOkExt A ext :=
  ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem ekSentCt1ReceivedEncodedLen_local1_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    EkSentCt1ReceivedEncodedLenLocal1PlacedOkExt A ext :=
  ekSentCt1ReceivedEncodedLen_local1_placed_ok_hooks A (Rust.withPanics ext)

theorem ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    EkSentCt1ReceivedEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem ekSentCt1ReceivedEncodedLen_local1_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    EkSentCt1ReceivedEncodedLenLocal1PlacedOk C A ctl abs :=
  ekSentCt1ReceivedEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem ekSentCt1ReceivedEncodedLen_local2_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_421).rebase (blkPl_421).base H)
      (blkPl_421).base (ekSentCt1ReceivedEncodedLenPinnedSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.dk, x.m.ct1⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (ls_subroutine_ok_plain_vmPreserved (i := 421) (by decide +kernel)
      (hok := unchunked82_entry_pinned_ok _ A _
        (Or.inr ⟨inst, hooksException H, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩)))

theorem ekSentCt1ReceivedEncodedLen_local2_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_421).rebase (blkPl_421).base H)
      (blkPl_421).base (ekSentCt1ReceivedEncodedLenSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.dk, x.m.ct1⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked4EncodedLen_ok_of_pinned
      (ls_subroutine_ok_plain_vmPreserved (i := 421) (by decide +kernel)
        (hok := unchunked82_entry_pinned_ok _ A _
          (Or.inr ⟨‹_›, hooksException H, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩))))

theorem ekSentCt1ReceivedEncodedLen_local2_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    EkSentCt1ReceivedEncodedLenLocal2PinnedPlacedOkExt A ext :=
  ekSentCt1ReceivedEncodedLen_local2_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem ekSentCt1ReceivedEncodedLen_local2_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    EkSentCt1ReceivedEncodedLenLocal2PlacedOkExt A ext :=
  ekSentCt1ReceivedEncodedLen_local2_placed_ok_hooks A (Rust.withPanics ext)

theorem ekSentCt1ReceivedEncodedLen_local2_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    EkSentCt1ReceivedEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  ekSentCt1ReceivedEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem ekSentCt1ReceivedEncodedLen_local2_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    EkSentCt1ReceivedEncodedLenLocal2PlacedOk C A ctl abs :=
  ekSentCt1ReceivedEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

/-! ## Part 2: 93-Instruction Group (`Ct1Sent`, `Ct1SentEkReceived`) -/

theorem unchunked5EncodedLen_ok_of_pinned {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (unchunked5EncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (unchunked5EncodedLenSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨a, epoch, auth, f3, f4, f5⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [unchunked5EncodedLenSpec, withVmPreserved] at hpre
  simp only [CryptoVerification.SpqrV1.ProtoRepr.unchunked5EncodedLenSpec,
    unchunked5At_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨a, g, epoch, auth, f3, f4, f5⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [unchunked5EncodedLenPinnedSpec, unchunked5EncodedLenSpec,
      withVmPreserved] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, hpost⟩
    refine ⟨hvm, ?_⟩
    simp only [CryptoVerification.SpqrV1.ProtoRepr.unchunked5EncodedLenSpec,
      unchunked5At_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-! ### `Ct1Sent` (Blocks `180`, `408`) -/

def Ct1SentEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_180).rebase (blkPl_180).base (Rust.withPanics ext))
    (blkPl_180).base (ct1SentEncodedLenPinnedSpec A)

def Ct1SentEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_180).rebase (blkPl_180).base (Rust.withPanics ext))
    (blkPl_180).base (ct1SentEncodedLenSpec A)

def Ct1SentEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  Ct1SentEncodedLenLocal1PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)

def Ct1SentEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  Ct1SentEncodedLenLocal1PlacedOkExt A (tripleRatchetExterns C ctl abs)

def Ct1SentEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_408).rebase (blkPl_408).base (Rust.withPanics ext))
    (blkPl_408).base (ct1SentEncodedLenPinnedSpec A)

def Ct1SentEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_408).rebase (blkPl_408).base (Rust.withPanics ext))
    (blkPl_408).base (ct1SentEncodedLenSpec A)

def Ct1SentEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  Ct1SentEncodedLenLocal2PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)

def Ct1SentEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  Ct1SentEncodedLenLocal2PlacedOkExt A (tripleRatchetExterns C ctl abs)

theorem ct1SentEncodedLen_local1_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_180).rebase (blkPl_180).base H)
      (blkPl_180).base (ct1SentEncodedLenPinnedSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.hdr, x.m.es, x.m.ct1⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (ls_subroutine_ok_plain_vmPreserved (i := 180) (by decide +kernel)
      (hok := unchunked93_entry_pinned_ok _ A _
        (Or.inr ⟨inst, hooksException H, Or.inl ⟨rfl, rfl⟩⟩)))

theorem ct1SentEncodedLen_local1_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_180).rebase (blkPl_180).base H)
      (blkPl_180).base (ct1SentEncodedLenSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.hdr, x.m.es, x.m.ct1⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked5EncodedLen_ok_of_pinned
      (ls_subroutine_ok_plain_vmPreserved (i := 180) (by decide +kernel)
        (hok := unchunked93_entry_pinned_ok _ A _
          (Or.inr ⟨‹_›, hooksException H, Or.inl ⟨rfl, rfl⟩⟩))))

theorem ct1SentEncodedLen_local1_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    Ct1SentEncodedLenLocal1PinnedPlacedOkExt A ext :=
  ct1SentEncodedLen_local1_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem ct1SentEncodedLen_local1_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    Ct1SentEncodedLenLocal1PlacedOkExt A ext :=
  ct1SentEncodedLen_local1_placed_ok_hooks A (Rust.withPanics ext)

theorem ct1SentEncodedLen_local1_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    Ct1SentEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  ct1SentEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem ct1SentEncodedLen_local1_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    Ct1SentEncodedLenLocal1PlacedOk C A ctl abs :=
  ct1SentEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem ct1SentEncodedLen_local2_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_408).rebase (blkPl_408).base H)
      (blkPl_408).base (ct1SentEncodedLenPinnedSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.hdr, x.m.es, x.m.ct1⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (ls_subroutine_ok_plain_vmPreserved (i := 408) (by decide +kernel)
      (hok := unchunked93_entry_pinned_ok _ A _
        (Or.inr ⟨inst, hooksException H, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)))

theorem ct1SentEncodedLen_local2_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_408).rebase (blkPl_408).base H)
      (blkPl_408).base (ct1SentEncodedLenSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.hdr, x.m.es, x.m.ct1⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked5EncodedLen_ok_of_pinned
      (ls_subroutine_ok_plain_vmPreserved (i := 408) (by decide +kernel)
        (hok := unchunked93_entry_pinned_ok _ A _
          (Or.inr ⟨‹_›, hooksException H, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩))))

theorem ct1SentEncodedLen_local2_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    Ct1SentEncodedLenLocal2PinnedPlacedOkExt A ext :=
  ct1SentEncodedLen_local2_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem ct1SentEncodedLen_local2_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    Ct1SentEncodedLenLocal2PlacedOkExt A ext :=
  ct1SentEncodedLen_local2_placed_ok_hooks A (Rust.withPanics ext)

theorem ct1SentEncodedLen_local2_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    Ct1SentEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  ct1SentEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem ct1SentEncodedLen_local2_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    Ct1SentEncodedLenLocal2PlacedOk C A ctl abs :=
  ct1SentEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

/-! ### `Ct1SentEkReceived` (Blocks `162`, `387`) -/

def Ct1SentEkReceivedEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_162).rebase (blkPl_162).base (Rust.withPanics ext))
    (blkPl_162).base (ct1SentEkReceivedEncodedLenPinnedSpec A)

def Ct1SentEkReceivedEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_162).rebase (blkPl_162).base (Rust.withPanics ext))
    (blkPl_162).base (ct1SentEkReceivedEncodedLenSpec A)

def Ct1SentEkReceivedEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  Ct1SentEkReceivedEncodedLenLocal1PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)

def Ct1SentEkReceivedEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  Ct1SentEkReceivedEncodedLenLocal1PlacedOkExt A (tripleRatchetExterns C ctl abs)

def Ct1SentEkReceivedEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_387).rebase (blkPl_387).base (Rust.withPanics ext))
    (blkPl_387).base (ct1SentEkReceivedEncodedLenPinnedSpec A)

def Ct1SentEkReceivedEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_387).rebase (blkPl_387).base (Rust.withPanics ext))
    (blkPl_387).base (ct1SentEkReceivedEncodedLenSpec A)

def Ct1SentEkReceivedEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  Ct1SentEkReceivedEncodedLenLocal2PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)

def Ct1SentEkReceivedEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  Ct1SentEkReceivedEncodedLenLocal2PlacedOkExt A (tripleRatchetExterns C ctl abs)

theorem ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_162).rebase (blkPl_162).base H)
      (blkPl_162).base (ct1SentEkReceivedEncodedLenPinnedSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.es, x.m.ek, x.m.ct1⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (ls_subroutine_ok_plain_vmPreserved (i := 162) (by decide +kernel)
      (hok := unchunked93_entry_pinned_ok _ A _
        (Or.inr ⟨inst, hooksException H, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)))

theorem ct1SentEkReceivedEncodedLen_local1_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_162).rebase (blkPl_162).base H)
      (blkPl_162).base (ct1SentEkReceivedEncodedLenSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.es, x.m.ek, x.m.ct1⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked5EncodedLen_ok_of_pinned
      (ls_subroutine_ok_plain_vmPreserved (i := 162) (by decide +kernel)
        (hok := unchunked93_entry_pinned_ok _ A _
          (Or.inr ⟨‹_›, hooksException H, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩))))

theorem ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    Ct1SentEkReceivedEncodedLenLocal1PinnedPlacedOkExt A ext :=
  ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem ct1SentEkReceivedEncodedLen_local1_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    Ct1SentEkReceivedEncodedLenLocal1PlacedOkExt A ext :=
  ct1SentEkReceivedEncodedLen_local1_placed_ok_hooks A (Rust.withPanics ext)

theorem ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    Ct1SentEkReceivedEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem ct1SentEkReceivedEncodedLen_local1_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    Ct1SentEkReceivedEncodedLenLocal1PlacedOk C A ctl abs :=
  ct1SentEkReceivedEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem ct1SentEkReceivedEncodedLen_local2_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_387).rebase (blkPl_387).base H)
      (blkPl_387).base (ct1SentEkReceivedEncodedLenPinnedSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.es, x.m.ek, x.m.ct1⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (ls_subroutine_ok_plain_vmPreserved (i := 387) (by decide +kernel)
      (hok := unchunked93_entry_pinned_ok _ A _
        (Or.inr ⟨inst, hooksException H, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩)))

theorem ct1SentEkReceivedEncodedLen_local2_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_387).rebase (blkPl_387).base H)
      (blkPl_387).base (ct1SentEkReceivedEncodedLenSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.es, x.m.ek, x.m.ct1⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked5EncodedLen_ok_of_pinned
      (ls_subroutine_ok_plain_vmPreserved (i := 387) (by decide +kernel)
        (hok := unchunked93_entry_pinned_ok _ A _
          (Or.inr ⟨‹_›, hooksException H, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩))))

theorem ct1SentEkReceivedEncodedLen_local2_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    Ct1SentEkReceivedEncodedLenLocal2PinnedPlacedOkExt A ext :=
  ct1SentEkReceivedEncodedLen_local2_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem ct1SentEkReceivedEncodedLen_local2_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    Ct1SentEkReceivedEncodedLenLocal2PlacedOkExt A ext :=
  ct1SentEkReceivedEncodedLen_local2_placed_ok_hooks A (Rust.withPanics ext)

theorem ct1SentEkReceivedEncodedLen_local2_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    Ct1SentEkReceivedEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  ct1SentEkReceivedEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem ct1SentEkReceivedEncodedLen_local2_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    Ct1SentEkReceivedEncodedLenLocal2PlacedOk C A ctl abs :=
  ct1SentEkReceivedEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

end LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93Budget
