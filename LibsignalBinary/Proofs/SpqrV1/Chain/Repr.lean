/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.RustHeap.Vec
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain

/-!
# Memory Layouts and Representation Predicates for `spqr::chain`

Separation-logic representation predicates relating `KeyHistory`, `ChainEpochDirection`,
`ChainEpoch`, `VecDeque<ChainEpoch>`, `ChainParamsPB`, `Direction`, and `Chain` to ARM64 memory.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ChainProofs

open Arm64
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1

/-! ## Constants and sizes -/

abbrev chainEpochDirSize : Nat := 56

abbrev chainEpochSize : Nat := 112

abbrev chainEpochAlign : Nat := 8

abbrev chainSize : Nat := 88

/-- Initial capacity of `KeyHistory.data` allocated by `KeyHistory::new()` (`0x48 = 72`). -/
abbrev keyHistoryInitCap : Nat := 72

/-! ## Ghost pins -/

/-- Exact `(cap, ptr)` of a `Vec<u8>`. -/
structure VecPin where
  cap : BitVec 64
  ptr : BitVec 64

/-- Ghost pins for `ChainEpochDirection`: the `next` and `prev.data` `Vec<u8>` buffers. -/
structure ChainEpochDirectionGhost where
  next : VecPin
  prev : VecPin

/-- Ghost pins for `ChainEpoch`: pins for `send` and `recv` directions. -/
structure ChainEpochGhost where
  send : ChainEpochDirectionGhost
  recv : ChainEpochDirectionGhost

/-- Ghost pins for `Chain`: the `links` `VecDeque<ChainEpoch>` buffer and `next_root` `Vec<u8>`. -/
structure ChainGhost where
  linksCap : BitVec 64
  linksPtr : BitVec 64
  linksHead : BitVec 64
  epochs : List ChainEpochGhost
  nextRoot : VecPin

/-! ## `KeyHistory` (24 bytes, align 8) -/

/-- `KeyHistory` at `a` with pinned `(cap, ptr)`: a single `Vec<u8>` header and buffer holding
`kh.data`. -/
def keyHistoryAt (A : RustAlloc) (a : BitVec 64) (pin : VecPin) (kh : KeyHistory) : SepProp :=
  vecU8At A a pin.cap pin.ptr kh.data

/-- `KeyHistory` at `a` (existentially quantified `cap` and `ptr`). -/
def keyHistory (A : RustAlloc) (a : BitVec 64) (kh : KeyHistory) : SepProp :=
  vecU8 A a kh.data

/-! ## `ChainEpochDirection` (56 bytes = `0x38`, align 8) -/

/-- `ChainEpochDirection` at `a` (56 bytes):
- `+0x00..+0x18` (24B): `next: Vec<u8>`
- `+0x18..+0x30` (24B): `prev: KeyHistory` (`Vec<u8>`)
- `+0x30..+0x34` (4B): `ctr: u32`
- `+0x34..+0x38` (4B): 4-byte tail padding (`memRegion`) -/
def chainEpochDirectionAt (A : RustAlloc) (a : BitVec 64)
    (g : ChainEpochDirectionGhost) (ced : ChainEpochDirection) : SepProp :=
  vecU8At A a g.next.cap g.next.ptr ced.next ∗
    keyHistoryAt A (a + 0x18#64) g.prev ced.prev ∗
    ((a + 0x30#64) ↦₃₂ ced.ctr) ∗
    memRegion (a + 0x34#64) 4

/-- `ChainEpochDirection` at `a` with existential `Vec` pins. -/
def chainEpochDirection (A : RustAlloc) (a : BitVec 64) (ced : ChainEpochDirection) : SepProp :=
  vecU8 A a ced.next ∗
    keyHistory A (a + 0x18#64) ced.prev ∗
    ((a + 0x30#64) ↦₃₂ ced.ctr) ∗
    memRegion (a + 0x34#64) 4

/-! ## `ChainEpoch` (112 bytes = `0x70`, align 8) -/

/-- `ChainEpoch` at `a` (112 bytes):
- `+0x00..+0x38` (56B): `send: ChainEpochDirection`
- `+0x38..+0x70` (56B): `recv: ChainEpochDirection` -/
def chainEpochAt (A : RustAlloc) (gce : ChainEpochGhost × ChainEpoch) (a : BitVec 64) : SepProp :=
  chainEpochDirectionAt A a gce.1.send gce.2.send ∗
    chainEpochDirectionAt A (a + 0x38#64) gce.1.recv gce.2.recv

/-- `ChainEpoch` at `a` with existential `Vec` pins. -/
def chainEpoch (A : RustAlloc) (ce : ChainEpoch) (a : BitVec 64) : SepProp :=
  chainEpochDirection A a ce.send ∗
    chainEpochDirection A (a + 0x38#64) ce.recv

/-! ## `VecDeque<ChainEpoch>` (32 bytes = `0x20`, align 8) -/

/-- The 32-byte `VecDeque` header `{cap, ptr, head, len}` at `v`. -/
def vecDequeHeader (v cap ptr head len : BitVec 64) : SepProp :=
  (v ↦₆₄ cap) ∗ ((v + 0x08#64) ↦₆₄ ptr) ∗ ((v + 0x10#64) ↦₆₄ head) ∗ ((v + 0x18#64) ↦₆₄ len)

/-- Physical slot index in a `VecDeque` of capacity `cap` starting at `head` for logical index `i`:
`(head + i) % cap` (computed as `if head + i < cap then head + i else head + i - cap`). -/
def vecDequePhysIdx (head cap i : Nat) : Nat :=
  if head + i < cap then head + i else head + i - cap

/-- Logical index corresponding to physical slot `s` in a `VecDeque` of capacity `cap` with `head`:
`if head ≤ s then s - head else s + cap - head`. -/
def vecDequeLogIdx (head cap s : Nat) : Nat :=
  if head ≤ s then s - head else s + cap - head

/-- Physical slots `[s .. s + n)` of a `VecDeque<T>` buffer at `ptr` (capacity `cap`, head `head`),
where logical index `i < xs.length` holds `elem xs[i]` and unoccupied slots hold `memRegion _ stride`. -/
def vecDequeSlotsAt {α : Type} (elem : α → BitVec 64 → SepProp) (stride cap head : Nat)
    (ptr : BitVec 64) (xs : List α) : Nat → Nat → SepProp
  | _, 0 => emp
  | s, n + 1 =>
    let addr := ptr + BitVec.ofNat 64 (s * stride)
    let i := vecDequeLogIdx head cap s
    (if h : i < xs.length then elem (xs[i]) addr else memRegion addr stride) ∗
      vecDequeSlotsAt elem stride cap head ptr xs (s + 1) n

/-- Ring-buffer heap contents of `VecDeque<T>` at `ptr` with capacity `cap` and `head`. -/
def vecDequeRingBuf {α : Type} (A : RustAlloc) (stride align : Nat) (elem : α → BitVec 64 → SepProp)
    (cap ptr head : BitVec 64) (xs : List α) : SepProp :=
  ⌜xs.length ≤ cap.toNat ∧ cap.toNat * stride < 2 ^ 63 ∧ ptr ≠ 0 ∧
    (if cap = 0 then head = 0 else head.toNat < cap.toNat)⌝ ∗
    (if cap = 0 then emp
     else A.live ptr (cap.toNat * stride) align ∗
       vecDequeSlotsAt elem stride cap.toNat head.toNat ptr xs 0 cap.toNat)

/-- Contiguous (`head = 0`) `VecDeque<T>` at `v` with capacity `cap` and buffer `ptr` holding `xs`:
the 32-byte header `{cap, ptr, 0, xs.length}` and the same `vecBuf` heap layout as `Vec<T>`. -/
def vecDequeContigAt {α : Type} (A : RustAlloc) (stride align : Nat) (elem : α → BitVec 64 → SepProp)
    (v cap ptr : BitVec 64) (xs : List α) : SepProp :=
  vecDequeHeader v cap ptr 0#64 (BitVec.ofNat 64 xs.length) ∗
    vecBuf A stride align elem cap ptr xs

/-- General `VecDeque<T>` at `v` with capacity `cap`, buffer `ptr`, and `head` holding `xs`. -/
def vecDequeAt {α : Type} (A : RustAlloc) (stride align : Nat) (elem : α → BitVec 64 → SepProp)
    (v cap ptr head : BitVec 64) (xs : List α) : SepProp :=
  vecDequeHeader v cap ptr head (BitVec.ofNat 64 xs.length) ∗
    vecDequeRingBuf A stride align elem cap ptr head xs

/-! ## `ChainParamsPB` (8 bytes, align 4) and `Direction` (4 bytes, align 4) -/

/-- `ChainParamsPB` at `a` (8 bytes): `max_jump: u32` at `+0`, `max_ooo_keys: u32` at `+4`. -/
def chainParamsAt (a : BitVec 64) (p : ChainParamsPB) : SepProp :=
  (a ↦₃₂ p.maxJump) ∗ ((a + 0x04#64) ↦₃₂ p.maxOooKeys)

/-- `Direction` at `a` (4 bytes): `0#32` for `.a2b`, `1#32` for `.b2a`. -/
def directionAt (a : BitVec 64) (d : Direction) : SepProp :=
  a ↦₃₂ d.toI32

/-! ## `Chain` (88 bytes = `0x58`, align 8) -/

/-- `Chain` at `a` (88 bytes) with general ring-buffer `links` (`head` arbitrary):
- `+0x00..+0x20` (32B): `links: VecDeque<ChainEpoch>`
- `+0x20..+0x38` (24B): `next_root: Vec<u8>`
- `+0x38..+0x40` (8B): `current_epoch: u64`
- `+0x40..+0x48` (8B): `send_epoch: u64`
- `+0x48..+0x50` (8B): `params: ChainParamsPB`
- `+0x50..+0x54` (4B): `dir: Direction`
- `+0x54..+0x58` (4B): 4-byte tail padding (`memRegion`) -/
def chainAt (A : RustAlloc) (a : BitVec 64) (G : ChainGhost) (c : Chain) : SepProp :=
  ⌜G.epochs.length = c.links.length⌝ ∗
    vecDequeAt A chainEpochSize chainEpochAlign (chainEpochAt A)
      a G.linksCap G.linksPtr G.linksHead (G.epochs.zip c.links) ∗
    vecU8At A (a + 0x20#64) G.nextRoot.cap G.nextRoot.ptr c.nextRoot ∗
    ((a + 0x38#64) ↦₆₄ c.currentEpoch) ∗
    ((a + 0x40#64) ↦₆₄ c.sendEpoch) ∗
    chainParamsAt (a + 0x48#64) c.params ∗
    directionAt (a + 0x50#64) c.dir ∗
    memRegion (a + 0x54#64) 4

/-- `Chain` at `a` (88 bytes) with contiguous `links` (`head = 0`, using `vecBuf`). -/
def chainContigAt (A : RustAlloc) (a : BitVec 64) (G : ChainGhost) (c : Chain) : SepProp :=
  ⌜G.epochs.length = c.links.length ∧ G.linksHead = 0#64⌝ ∗
    vecDequeContigAt A chainEpochSize chainEpochAlign (chainEpochAt A)
      a G.linksCap G.linksPtr (G.epochs.zip c.links) ∗
    vecU8At A (a + 0x20#64) G.nextRoot.cap G.nextRoot.ptr c.nextRoot ∗
    ((a + 0x38#64) ↦₆₄ c.currentEpoch) ∗
    ((a + 0x40#64) ↦₆₄ c.sendEpoch) ∗
    chainParamsAt (a + 0x48#64) c.params ∗
    directionAt (a + 0x50#64) c.dir ∗
    memRegion (a + 0x54#64) 4

/-- `Chain` at `a` (existentially quantified `ChainGhost`). -/
def chainRepr (A : RustAlloc) (a : BitVec 64) (c : Chain) : SepProp :=
  ∃∗ G : ChainGhost, chainAt A a G c

/-- `next_key_internal` 36-byte output tuple `(u32, [u8; 32])` at `out`:
`ctr: u32` at `out + 0`, `key: [u8; 32]` (`key.length = 32`) at `out + 4`. -/
def nextKeyOutAt (out : BitVec 64) (ctr : BitVec 32) (key : List (BitVec 8)) : SepProp :=
  ⌜key.length = 32⌝ ∗ (out ↦₃₂ ctr) ∗ ((out + 0x04#64) ↦ₛ key)

end CryptoVerification.SpqrV1.ChainProofs
