/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93Placed
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93Budget

/-!
# `VmPreserved` Placed Proofs for 82- and 93-Instruction Unchunked `encoded_len` Leaves

Lifts `[LibsignalPlacement]` `subroutine_ok` contracts to `VmPreserved` for CLI Blocks `492`, `499`
(82-instruction group) and `487`, `469` (93-instruction group).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93PlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetExterns)
open CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.Placed
  (lsProg_492 blkPl_492 lsProg_499 blkPl_499 lsProg_487 blkPl_487 lsProg_469 blkPl_469)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget (ls_subroutine_ok_plain_vmPreserved)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsBudget
  (headerSentEncodedLenPinnedSpec headerSentEncodedLenSpec
   ekSentCt1ReceivedEncodedLenPinnedSpec ekSentCt1ReceivedEncodedLenSpec
   ct1SentEncodedLenPinnedSpec ct1SentEncodedLenSpec
   ct1SentEkReceivedEncodedLenPinnedSpec ct1SentEkReceivedEncodedLenSpec)

/-! ## Part 1: 82-Instruction Group (`492` `HeaderSent`, `499` `EkSentCt1Received`) -/

def HeaderSentEncodedLenLocal1PinnedPlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_492 (Rust.withPanics ext)) (blkPl_492).base
    (headerSentEncodedLenPinnedSpec A)

def HeaderSentEncodedLenLocal1PlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_492 (Rust.withPanics ext)) (blkPl_492).base
    (headerSentEncodedLenSpec A)

def HeaderSentEncodedLenLocal1PinnedPlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_492 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_492).base
    (headerSentEncodedLenPinnedSpec A)

def HeaderSentEncodedLenLocal1PlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_492 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_492).base
    (headerSentEncodedLenSpec A)

theorem headerSentEncodedLen_local1_pinned_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_492 H) (blkPl_492).base (headerSentEncodedLenPinnedSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 492) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.headerSentEncodedLen_local1_pinned_placed_ok_x
      A (hooksException H))

theorem headerSentEncodedLen_local1_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_492 H) (blkPl_492).base (headerSentEncodedLenSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 492) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.headerSentEncodedLen_local1_placed_ok_x
      A (hooksException H))

theorem headerSentEncodedLen_local1_pinned_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    HeaderSentEncodedLenLocal1PinnedPlacedOkExt A ext :=
  headerSentEncodedLen_local1_pinned_placed_ok_x A (Rust.withPanics ext)

theorem headerSentEncodedLen_local1_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    HeaderSentEncodedLenLocal1PlacedOkExt A ext :=
  headerSentEncodedLen_local1_placed_ok_x A (Rust.withPanics ext)

theorem headerSentEncodedLen_local1_pinned_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    HeaderSentEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  headerSentEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem headerSentEncodedLen_local1_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    HeaderSentEncodedLenLocal1PlacedOk C A ctl abs :=
  headerSentEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

def EkSentCt1ReceivedEncodedLenLocal1PinnedPlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_499 (Rust.withPanics ext)) (blkPl_499).base
    (ekSentCt1ReceivedEncodedLenPinnedSpec A)

def EkSentCt1ReceivedEncodedLenLocal1PlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_499 (Rust.withPanics ext)) (blkPl_499).base
    (ekSentCt1ReceivedEncodedLenSpec A)

def EkSentCt1ReceivedEncodedLenLocal1PinnedPlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_499 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_499).base
    (ekSentCt1ReceivedEncodedLenPinnedSpec A)

def EkSentCt1ReceivedEncodedLenLocal1PlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_499 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_499).base
    (ekSentCt1ReceivedEncodedLenSpec A)

theorem ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_499 H) (blkPl_499).base (ekSentCt1ReceivedEncodedLenPinnedSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 499) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_x
      A (hooksException H))

theorem ekSentCt1ReceivedEncodedLen_local1_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_499 H) (blkPl_499).base (ekSentCt1ReceivedEncodedLenSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 499) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLen_local1_placed_ok_x
      A (hooksException H))

theorem ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    EkSentCt1ReceivedEncodedLenLocal1PinnedPlacedOkExt A ext :=
  ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_x A (Rust.withPanics ext)

theorem ekSentCt1ReceivedEncodedLen_local1_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    EkSentCt1ReceivedEncodedLenLocal1PlacedOkExt A ext :=
  ekSentCt1ReceivedEncodedLen_local1_placed_ok_x A (Rust.withPanics ext)

theorem ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    EkSentCt1ReceivedEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem ekSentCt1ReceivedEncodedLen_local1_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    EkSentCt1ReceivedEncodedLenLocal1PlacedOk C A ctl abs :=
  ekSentCt1ReceivedEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

/-! ## Part 2: 93-Instruction Group (`487` `Ct1Sent`, `469` `Ct1SentEkReceived`) -/

def Ct1SentEncodedLenLocal1PinnedPlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_487 (Rust.withPanics ext)) (blkPl_487).base
    (ct1SentEncodedLenPinnedSpec A)

def Ct1SentEncodedLenLocal1PlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_487 (Rust.withPanics ext)) (blkPl_487).base
    (ct1SentEncodedLenSpec A)

def Ct1SentEncodedLenLocal1PinnedPlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_487 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_487).base
    (ct1SentEncodedLenPinnedSpec A)

def Ct1SentEncodedLenLocal1PlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_487 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_487).base
    (ct1SentEncodedLenSpec A)

theorem ct1SentEncodedLen_local1_pinned_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_487 H) (blkPl_487).base (ct1SentEncodedLenPinnedSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 487) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEncodedLen_local1_pinned_placed_ok_x
      A (hooksException H))

theorem ct1SentEncodedLen_local1_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_487 H) (blkPl_487).base (ct1SentEncodedLenSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 487) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEncodedLen_local1_placed_ok_x
      A (hooksException H))

theorem ct1SentEncodedLen_local1_pinned_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    Ct1SentEncodedLenLocal1PinnedPlacedOkExt A ext :=
  ct1SentEncodedLen_local1_pinned_placed_ok_x A (Rust.withPanics ext)

theorem ct1SentEncodedLen_local1_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    Ct1SentEncodedLenLocal1PlacedOkExt A ext :=
  ct1SentEncodedLen_local1_placed_ok_x A (Rust.withPanics ext)

theorem ct1SentEncodedLen_local1_pinned_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    Ct1SentEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  ct1SentEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem ct1SentEncodedLen_local1_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    Ct1SentEncodedLenLocal1PlacedOk C A ctl abs :=
  ct1SentEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

def Ct1SentEkReceivedEncodedLenLocal1PinnedPlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_469 (Rust.withPanics ext)) (blkPl_469).base
    (ct1SentEkReceivedEncodedLenPinnedSpec A)

def Ct1SentEkReceivedEncodedLenLocal1PlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_469 (Rust.withPanics ext)) (blkPl_469).base
    (ct1SentEkReceivedEncodedLenSpec A)

def Ct1SentEkReceivedEncodedLenLocal1PinnedPlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_469 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_469).base
    (ct1SentEkReceivedEncodedLenPinnedSpec A)

def Ct1SentEkReceivedEncodedLenLocal1PlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_469 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_469).base
    (ct1SentEkReceivedEncodedLenSpec A)

theorem ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_469 H) (blkPl_469).base (ct1SentEkReceivedEncodedLenPinnedSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 469) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok_x
      A (hooksException H))

theorem ct1SentEkReceivedEncodedLen_local1_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_469 H) (blkPl_469).base (ct1SentEkReceivedEncodedLenSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 469) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEkReceivedEncodedLen_local1_placed_ok_x
      A (hooksException H))

theorem ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    Ct1SentEkReceivedEncodedLenLocal1PinnedPlacedOkExt A ext :=
  ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok_x A (Rust.withPanics ext)

theorem ct1SentEkReceivedEncodedLen_local1_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    Ct1SentEkReceivedEncodedLenLocal1PlacedOkExt A ext :=
  ct1SentEkReceivedEncodedLen_local1_placed_ok_x A (Rust.withPanics ext)

theorem ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    Ct1SentEkReceivedEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem ct1SentEkReceivedEncodedLen_local1_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    Ct1SentEkReceivedEncodedLenLocal1PlacedOk C A ctl abs :=
  ct1SentEkReceivedEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

end LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93PlacedBudget
