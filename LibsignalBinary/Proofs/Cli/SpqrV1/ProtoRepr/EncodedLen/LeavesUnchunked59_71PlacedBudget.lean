/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71Placed
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71Budget

/-!
# `VmPreserved` Placed Proofs for 59- and 71-Instruction Unchunked `encoded_len` Leaves

Lifts `[LibsignalPlacement]` `subroutine_ok` contracts to `VmPreserved` for CLI Blocks `479`, `500`,
`470` (59-instruction group) and `496`, `482` (71-instruction group).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71PlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetExterns)
open CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.Placed
  (lsProg_479 blkPl_479 lsProg_500 blkPl_500 lsProg_470 blkPl_470
   lsProg_496 blkPl_496 lsProg_482 blkPl_482)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget (ls_subroutine_ok_plain_vmPreserved)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsBudget
  (keysUnsampledEncodedLenPinnedSpec keysUnsampledEncodedLenSpec
   noHeaderReceivedEncodedLenPinnedSpec noHeaderReceivedEncodedLenSpec
   ct2SentEncodedLenPinnedSpec ct2SentEncodedLenSpec
   ekSentEncodedLenPinnedSpec ekSentEncodedLenSpec
   headerReceivedEncodedLenPinnedSpec headerReceivedEncodedLenSpec)

/-! ## Part 1: 59-Instruction Group (`479` `KeysUnsampled`, `500` `NoHeaderReceived`, `470` `Ct2Sent`) -/

def KeysUnsampledEncodedLenLocal1PinnedPlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_479 (Rust.withPanics ext)) (blkPl_479).base
    (keysUnsampledEncodedLenPinnedSpec A)

def KeysUnsampledEncodedLenLocal1PlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_479 (Rust.withPanics ext)) (blkPl_479).base
    (keysUnsampledEncodedLenSpec A)

def KeysUnsampledEncodedLenLocal1PinnedPlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_479 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_479).base
    (keysUnsampledEncodedLenPinnedSpec A)

def KeysUnsampledEncodedLenLocal1PlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_479 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_479).base
    (keysUnsampledEncodedLenSpec A)

theorem keysUnsampledEncodedLen_local1_pinned_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_479 H) (blkPl_479).base (keysUnsampledEncodedLenPinnedSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 479) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.keysUnsampledEncodedLen_local1_pinned_placed_ok_x
      A (hooksException H))

theorem keysUnsampledEncodedLen_local1_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_479 H) (blkPl_479).base (keysUnsampledEncodedLenSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 479) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.keysUnsampledEncodedLen_local1_placed_ok_x
      A (hooksException H))

theorem keysUnsampledEncodedLen_local1_pinned_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    KeysUnsampledEncodedLenLocal1PinnedPlacedOkExt A ext :=
  keysUnsampledEncodedLen_local1_pinned_placed_ok_x A (Rust.withPanics ext)

theorem keysUnsampledEncodedLen_local1_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    KeysUnsampledEncodedLenLocal1PlacedOkExt A ext :=
  keysUnsampledEncodedLen_local1_placed_ok_x A (Rust.withPanics ext)

theorem keysUnsampledEncodedLen_local1_pinned_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    KeysUnsampledEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  keysUnsampledEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem keysUnsampledEncodedLen_local1_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    KeysUnsampledEncodedLenLocal1PlacedOk C A ctl abs :=
  keysUnsampledEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

def NoHeaderReceivedEncodedLenLocal1PinnedPlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_500 (Rust.withPanics ext)) (blkPl_500).base
    (noHeaderReceivedEncodedLenPinnedSpec A)

def NoHeaderReceivedEncodedLenLocal1PlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_500 (Rust.withPanics ext)) (blkPl_500).base
    (noHeaderReceivedEncodedLenSpec A)

def NoHeaderReceivedEncodedLenLocal1PinnedPlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_500 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_500).base
    (noHeaderReceivedEncodedLenPinnedSpec A)

def NoHeaderReceivedEncodedLenLocal1PlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_500 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_500).base
    (noHeaderReceivedEncodedLenSpec A)

theorem noHeaderReceivedEncodedLen_local1_pinned_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_500 H) (blkPl_500).base (noHeaderReceivedEncodedLenPinnedSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 500) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.noHeaderReceivedEncodedLen_local1_pinned_placed_ok_x
      A (hooksException H))

theorem noHeaderReceivedEncodedLen_local1_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_500 H) (blkPl_500).base (noHeaderReceivedEncodedLenSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 500) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.noHeaderReceivedEncodedLen_local1_placed_ok_x
      A (hooksException H))

theorem noHeaderReceivedEncodedLen_local1_pinned_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    NoHeaderReceivedEncodedLenLocal1PinnedPlacedOkExt A ext :=
  noHeaderReceivedEncodedLen_local1_pinned_placed_ok_x A (Rust.withPanics ext)

theorem noHeaderReceivedEncodedLen_local1_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    NoHeaderReceivedEncodedLenLocal1PlacedOkExt A ext :=
  noHeaderReceivedEncodedLen_local1_placed_ok_x A (Rust.withPanics ext)

theorem noHeaderReceivedEncodedLen_local1_pinned_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    NoHeaderReceivedEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  noHeaderReceivedEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem noHeaderReceivedEncodedLen_local1_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    NoHeaderReceivedEncodedLenLocal1PlacedOk C A ctl abs :=
  noHeaderReceivedEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

def Ct2SentEncodedLenLocal1PinnedPlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_470 (Rust.withPanics ext)) (blkPl_470).base
    (ct2SentEncodedLenPinnedSpec A)

def Ct2SentEncodedLenLocal1PlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_470 (Rust.withPanics ext)) (blkPl_470).base
    (ct2SentEncodedLenSpec A)

def Ct2SentEncodedLenLocal1PinnedPlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_470 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_470).base
    (ct2SentEncodedLenPinnedSpec A)

def Ct2SentEncodedLenLocal1PlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_470 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_470).base
    (ct2SentEncodedLenSpec A)

theorem ct2SentEncodedLen_local1_pinned_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_470 H) (blkPl_470).base (ct2SentEncodedLenPinnedSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 470) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.ct2SentEncodedLen_local1_pinned_placed_ok_x
      A (hooksException H))

theorem ct2SentEncodedLen_local1_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_470 H) (blkPl_470).base (ct2SentEncodedLenSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 470) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.ct2SentEncodedLen_local1_placed_ok_x
      A (hooksException H))

theorem ct2SentEncodedLen_local1_pinned_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    Ct2SentEncodedLenLocal1PinnedPlacedOkExt A ext :=
  ct2SentEncodedLen_local1_pinned_placed_ok_x A (Rust.withPanics ext)

theorem ct2SentEncodedLen_local1_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    Ct2SentEncodedLenLocal1PlacedOkExt A ext :=
  ct2SentEncodedLen_local1_placed_ok_x A (Rust.withPanics ext)

theorem ct2SentEncodedLen_local1_pinned_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    Ct2SentEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  ct2SentEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem ct2SentEncodedLen_local1_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    Ct2SentEncodedLenLocal1PlacedOk C A ctl abs :=
  ct2SentEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

/-! ## Part 2: 71-Instruction Group (`496` `EkSent`, `482` `HeaderReceived`) -/

def EkSentEncodedLenLocal1PinnedPlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_496 (Rust.withPanics ext)) (blkPl_496).base
    (ekSentEncodedLenPinnedSpec A)

def EkSentEncodedLenLocal1PlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_496 (Rust.withPanics ext)) (blkPl_496).base
    (ekSentEncodedLenSpec A)

def EkSentEncodedLenLocal1PinnedPlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_496 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_496).base
    (ekSentEncodedLenPinnedSpec A)

def EkSentEncodedLenLocal1PlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_496 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_496).base
    (ekSentEncodedLenSpec A)

theorem ekSentEncodedLen_local1_pinned_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_496 H) (blkPl_496).base (ekSentEncodedLenPinnedSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 496) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentEncodedLen_local1_pinned_placed_ok_x
      A (hooksException H))

theorem ekSentEncodedLen_local1_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_496 H) (blkPl_496).base (ekSentEncodedLenSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 496) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentEncodedLen_local1_placed_ok_x
      A (hooksException H))

theorem ekSentEncodedLen_local1_pinned_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    EkSentEncodedLenLocal1PinnedPlacedOkExt A ext :=
  ekSentEncodedLen_local1_pinned_placed_ok_x A (Rust.withPanics ext)

theorem ekSentEncodedLen_local1_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    EkSentEncodedLenLocal1PlacedOkExt A ext :=
  ekSentEncodedLen_local1_placed_ok_x A (Rust.withPanics ext)

theorem ekSentEncodedLen_local1_pinned_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    EkSentEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  ekSentEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem ekSentEncodedLen_local1_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    EkSentEncodedLenLocal1PlacedOk C A ctl abs :=
  ekSentEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

def HeaderReceivedEncodedLenLocal1PinnedPlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_482 (Rust.withPanics ext)) (blkPl_482).base
    (headerReceivedEncodedLenPinnedSpec A)

def HeaderReceivedEncodedLenLocal1PlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_482 (Rust.withPanics ext)) (blkPl_482).base
    (headerReceivedEncodedLenSpec A)

def HeaderReceivedEncodedLenLocal1PinnedPlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_482 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_482).base
    (headerReceivedEncodedLenPinnedSpec A)

def HeaderReceivedEncodedLenLocal1PlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_482 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_482).base
    (headerReceivedEncodedLenSpec A)

theorem headerReceivedEncodedLen_local1_pinned_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_482 H) (blkPl_482).base (headerReceivedEncodedLenPinnedSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 482) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.headerReceivedEncodedLen_local1_pinned_placed_ok_x
      A (hooksException H))

theorem headerReceivedEncodedLen_local1_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_482 H) (blkPl_482).base (headerReceivedEncodedLenSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 482) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.headerReceivedEncodedLen_local1_placed_ok_x
      A (hooksException H))

theorem headerReceivedEncodedLen_local1_pinned_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    HeaderReceivedEncodedLenLocal1PinnedPlacedOkExt A ext :=
  headerReceivedEncodedLen_local1_pinned_placed_ok_x A (Rust.withPanics ext)

theorem headerReceivedEncodedLen_local1_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    HeaderReceivedEncodedLenLocal1PlacedOkExt A ext :=
  headerReceivedEncodedLen_local1_placed_ok_x A (Rust.withPanics ext)

theorem headerReceivedEncodedLen_local1_pinned_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    HeaderReceivedEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  headerReceivedEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem headerReceivedEncodedLen_local1_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    HeaderReceivedEncodedLenLocal1PlacedOk C A ctl abs :=
  headerReceivedEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

end LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71PlacedBudget
