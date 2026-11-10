/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.TrapRng

/-!
# `Hmac<Sha256>` Memory Layout and `new_from_slice` Specification

Defines the 144-byte `Hmac<Sha256>` separation-logic layout `hmacStateAt` / `hmacCoreAt`
and the contract `newFromSliceSpec` for `<Hmac<Sha256> as KeyInit>::new_from_slice`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr

abbrev newFromSliceName : String :=
  "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]"

/-- `Hmac<Sha256>::new_from_slice` frame (`0x2b3b0`: `sub sp, sp, #0x220` = 544 B; its callees are
hooks that use no stack). -/
abbrev newFromSliceStack : Nat := 544

/-- The 64-byte zero-padded HMAC key block `k₀ = key ‖ 0…0` for `|key| ≤ 64`. -/
def hmacKeyBlock (key : List (BitVec 8)) : List (BitVec 8) :=
  key ++ List.replicate (64 - key.length) 0#8

/-- Inner SHA-256 chaining state after compressing `k₀ ⊕ ipad`. -/
def hmacInnerInit (F : ShaCompress) (key : List (BitVec 8)) : ShaState :=
  F sha256IV ((hmacKeyBlock key).map (· ^^^ 0x36#8))

/-- Outer SHA-256 chaining state after compressing `k₀ ⊕ opad`. -/
def hmacOuterInit (F : ShaCompress) (key : List (BitVec 8)) : ShaState :=
  F sha256IV ((hmacKeyBlock key).map (· ^^^ 0x5c#8))

/-- The 144-byte (`0x90`-byte) `Hmac<Sha256>` (`hmac` 0.13.0 / `sha2` 0.11.0) state at `a` with
buffered bytes `tail` (`|tail| < 64`), inner chaining state `innerSt` after `nBlocks` compressed
64-byte blocks, and outer chaining state `outerSt` after 1 block:
* `+0x00..+0x3f` (63 B): block buffer (`tail` followed by `63 - tail.length` bytes);
* `+0x3f` (1 B): `pos = tail.length` (`u8`);
* `+0x40..+0x60` (32 B): inner `Sha256VarCore` state (`shaStateBytes innerSt`);
* `+0x60` (8 B): inner `block_len = nBlocks` (`u64`);
* `+0x68..+0x88` (32 B): outer `Sha256VarCore` state (`shaStateBytes outerSt`);
* `+0x88` (8 B): outer `block_len = 1` (`u64`). -/
def hmacStateAt (a : BitVec 64) (innerSt : ShaState) (nBlocks : Nat) (outerSt : ShaState)
    (tail : List (BitVec 8)) : SepProp :=
  ⌜tail.length < 64⌝ ∗
    (a ↦ₛ tail) ∗ memRegion (a + BitVec.ofNat 64 tail.length) (63 - tail.length) ∗
    ((a + 0x3f#64) ↦₈ BitVec.ofNat 8 tail.length) ∗
    ((a + 0x40#64) ↦ₛ LibsignalHmac.shaStateBytes innerSt) ∗
    ((a + 0x60#64) ↦₆₄ BitVec.ofNat 64 nBlocks) ∗
    ((a + 0x68#64) ↦ₛ LibsignalHmac.shaStateBytes outerSt) ∗
    ((a + 0x88#64) ↦₆₄ 1#64)

/-- `Hmac<Sha256>` at `a` (`0x90` bytes) right after absorbing `msg` (`|msg| < 64`) on top of the
key block (`nBlocks = 1`, `innerSt = hmacInnerInit F key`, `outerSt = hmacOuterInit F key`). -/
abbrev hmacCoreAt (F : ShaCompress) (a : BitVec 64) (key msg : List (BitVec 8)) : SepProp :=
  hmacStateAt a (hmacInnerInit F key) 1 (hmacOuterInit F key) msg

/-- Ghost arguments of `Hmac<Sha256>::new_from_slice` (`0x2b3b0`). -/
structure NewFromSliceGhost where
  /-- Sret (`x0`, 152 = `0x98` bytes: `Result<Hmac<Sha256>, InvalidLength>`). -/
  ret : BitVec 64
  /-- Key slice pointer (`x1`). -/
  keyA : BitVec 64
  /-- Key bytes (`x2 = key.length ≤ 64`). -/
  key : List (BitVec 8)

/-- Spec of `<Hmac<Sha256> as KeyInit>::new_from_slice` (`0x2b3b0`, 541 instructions):
* `x0 = ret` (152-byte sret), `x1 = keyA`, `x2 = key.length ≤ 64`;
* writes the `Result::Ok` discriminant `0#64` at `ret` and `hmacCoreAt F (ret + 8) key []` at
  `ret + 8 .. ret + 0x98`.
Cannot panic (`onPanic = ⌜False⌝`). -/
def newFromSliceSpec (F : ShaCompress) : Spec NewFromSliceGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.keyA ∧
      (s.readReg64 .x2).toNat = x.key.length ∧ x.key.length ≤ 64⌝ ∗
      memRegion x.ret 0x98 ∗ (x.keyA ↦ₛ x.key) ∗
      stackAt s.sp newFromSliceStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.ret ↦₆₄ 0#64) ∗ hmacCoreAt F (x.ret + 8#64) x.key [] ∗
      (x.keyA ↦ₛ x.key) ∗
      stackAt s0.sp newFromSliceStack

def NewFromSliceOkExt (img : Obj.Image) (C : Crypto)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
    ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr newFromSliceName)
    ((newFromSliceSpec C.F).inImage img)

def NewFromSliceOk_trap (img : Obj.Image) (C : Crypto)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs)
    ((trTrapProgAt img.base C abs).fnAddr newFromSliceName)
    ((newFromSliceSpec C.F).inImage img)

def NewFromSliceOk (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr newFromSliceName)
    ((newFromSliceSpec C.F).inImage img)

theorem NewFromSliceOk.of_trap {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (h : NewFromSliceOk_trap img C abs) :
    NewFromSliceOk img C ctl abs := by
  unfold NewFromSliceOk
  rw [← (trapsOnly_trTrap_kit img.base C ctl abs).fnAddr newFromSliceName]
  exact subroutine_ok_kit_of_trTrap h

end CryptoVerification.LibsignalTripleRatchet
