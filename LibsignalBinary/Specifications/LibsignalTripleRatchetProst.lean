/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.RustHeap.Vec
public import ProofLib.Hoare.LibcHooks

/-!
# Reference Semantics and Hoare Contracts for In-Image `prost` Helpers

**Checked by Lean.** Reference semantics (`varintSlow`, `decodeVarintSlowHook`), heap-ownership
representation predicates (`KindNoHeap`, `decodeErrorAtStackLen`, `decodeErrorAt`), and Hoare
contracts (`decodeErrorFromSpec`, `decodeErrorPushSpec`) for three compiled `prost` 0.14.4
functions in the session image:
* `prost::encoding::varint::decode_varint_slow::<&mut &[u8]>` (`x0 = &mut &mut &[u8]`, returning
  `(0, value)` or `(1, box)` in `(x0, x1)`).
* `<prost::error::DecodeError as From<DecodeErrorKind>>::from` (`x0 = &DecodeErrorKind`, returning
  a 72-byte `Box<Inner>` with `stack` at `+0` and `description` at `+24`).
* `<prost::error::DecodeError>::push` (`x0 = &mut DecodeError`, appending an opaque 32-byte
  `(&'static str, &'static str)` location entry).

Only `DecodeErrorKind` variants with niche word `w ∈ [2^63, 2^63 + 11)` (`KindNoHeap`, owning no
heap allocations) are constructed in the session-program call graph (`decodeErrorKindWords`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoVerification.RustHeap

/-! ## `decode_varint_slow` -/

/-- prost's `decode_varint_slow` on the bytes `l` (at most the first 10 are read): the value and
the number of bytes read, or `none` (`InvalidVarint`). `count` is the number of bytes read so far
and `acc` the value so far (`varint.rs:159–171`). -/
def varintSlowAux : Nat → BitVec 64 → List (BitVec 8) → Option (BitVec 64 × Nat)
  | _, _, [] => none
  | count, acc, b :: rest =>
    let acc := acc ||| ((b &&& 0x7f#8).zeroExtend 64 <<< (7 * count))
    if b.toNat ≤ 0x7f then
      if count = 9 ∧ 2 ≤ b.toNat then none else some (acc, count + 1)
    else varintSlowAux (count + 1) acc rest

/-- prost's `decode_varint_slow` on a buffer whose first `min(10, remaining)` bytes are `l`. -/
def varintSlow (l : List (BitVec 8)) : Option (BitVec 64 × Nat) :=
  varintSlowAux 0 0#64 (l.take 10)

/-- The niche word of `DecodeErrorKind::InvalidVarint` (variant 1). -/
def invalidVarintWord : BitVec 64 := 0x8000000000000001#64

/-- `decode_varint_slow::<&mut &[u8]>(x0 = &mut &mut &[u8])`, given the hook `fromHook` of
`<DecodeError as From<DecodeErrorKind>>::from`. With `slot := *x0` and `(ptr, len)` the slice at
`slot`:
* `Ok(v)` after `k` bytes: the slice becomes `(ptr + k, len - k)`, `x0 := 0`, `x1 := v`, return;
* `Err`: the slice becomes `(ptr + k, len - k)` with `k = min(10, len)` (every byte was read),
  then, as `decode_varint_slow::<&[u8]>+0x48..+0x5c` does, `sp := sp - 64`, the word
  `invalidVarintWord` at the new `sp`, `x0 := sp`, and `fromHook` runs. If it returns
  (`Running`), `sp` is restored, `x0 := 1`, `x1 :=` its `x0`, return. Otherwise (a panic) its
  state is the result.

The bytes `[sp - 64, sp)` and `from`'s own stack below them are scratch: a caller must give the
function `64 + decodeErrorHookStack` bytes of stack. -/
def decodeVarintSlowHook (fromHook : State → State) (s : State) : State :=
  let slot := s.mem.read64 (s.readReg64 .x0)
  let ptr := s.mem.read64 slot
  let len := (s.mem.read64 (slot + 8#64)).toNat
  let advance (k : Nat) : Memory :=
    (s.mem.write64 slot (ptr + BitVec.ofNat 64 k)).write64 (slot + 8#64) (BitVec.ofNat 64 (len - k))
  match varintSlow (s.mem.readBytes ptr (min 10 len)) with
  | some (v, k) => retHook (fun s => ((s.setMem (advance k)).writeReg64 .x0 0#64).writeReg64 .x1 v) s
  | none =>
    let kindA := s.sp - 64#64
    let s1 : State := { s with sp := kindA, mem := (advance (min 10 len)).write64 kindA invalidVarintWord }
    let s2 := fromHook (s1.writeReg64 .x0 kindA)
    match s2.status with
    | .Running =>
      (({ s2 with sp := s.sp }.writeReg64 .x1 (s2.readReg64 .x0)).writeReg64 .x0 1#64).setPC
        (s.readReg64 .lr)
    | _ => s2

/-! ### Guards (kernel-checked): the four varint classes -/

/-- A 1-byte varint. -/
theorem varintSlow_oneByte : varintSlow [0x05#8, 0xff#8] = some (5#64, 1) := by decide +kernel

/-- A 10-byte varint: `2^64 - 1` (nine `0xff`, then `0x01`). -/
theorem varintSlow_tenBytes :
    varintSlow (List.replicate 9 0xff#8 ++ [0x01#8, 0x07#8]) =
      some (0xffffffffffffffff#64, 10) := by decide +kernel

/-- Overflow: the 10th byte is `≥ 2`. -/
theorem varintSlow_overflow : varintSlow (List.replicate 9 0xff#8 ++ [0x02#8]) = none := by
  decide +kernel

/-- Too long: ten bytes with the continuation bit (an 11th byte is never read). -/
theorem varintSlow_tooLong : varintSlow (List.replicate 10 0x80#8 ++ [0x00#8]) = none := by
  decide +kernel

/-- Truncated: the buffer ends inside the varint. -/
theorem varintSlow_truncated : varintSlow [0xac#8, 0x82#8] = none := by decide +kernel

/-- A 2-byte varint (`300`). -/
theorem varintSlow_twoBytes : varintSlow [0xac#8, 0x02#8, 0x01#8] = some (300#64, 2) := by
  decide +kernel

/-- A machine state for the hook guards: `x0 = 0x100` holds `slot = 0x200`, which holds the
slice `(0x300, len)` of the bytes `bs`; `sp = 0x1000`, `lr = 0x4444`. -/
def guardState (bs : List (BitVec 8)) : State :=
  let m := ((((Memory.empty.write64 0x100#64 0x200#64).write64 0x200#64 0x300#64).write64 0x208#64
    (BitVec.ofNat 64 bs.length)).writeBytes 0x300#64 bs)
  ({ sp := 0x1000#64, mem := m } : State).writeReg64 .x0 0x100#64 |>.writeReg64 .lr 0x4444#64

/-- The hook on `300 = [0xac, 0x02]` (then one more byte): `x0 = 0`, `x1 = 300`, the slice
advanced by 2, return to `lr`. -/
theorem decodeVarintSlowHook_ok :
    let sf := decodeVarintSlowHook id (guardState [0xac#8, 0x02#8, 0x01#8])
    sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = 300#64 ∧ sf.mem.read64 0x200#64 = 0x302#64 ∧
      sf.mem.read64 0x208#64 = 1#64 ∧ sf.pc = 0x4444#64 ∧ sf.sp = 0x1000#64 := by
  decide +kernel

/-- The hook on a truncated varint, with `fromHook := id` (which "returns" `x0` = its argument):
`x0 = 1`, `x1 = sp - 64` holding `invalidVarintWord`, the slice advanced by `min(10, len) = 2`,
`sp` restored. -/
theorem decodeVarintSlowHook_err :
    let sf := decodeVarintSlowHook id (guardState [0xac#8, 0x82#8])
    sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = 0xfc0#64 ∧
      sf.mem.read64 0xfc0#64 = invalidVarintWord ∧ sf.mem.read64 0x200#64 = 0x302#64 ∧
      sf.mem.read64 0x208#64 = 0#64 ∧ sf.pc = 0x4444#64 ∧ sf.sp = 0x1000#64 := by
  decide +kernel

/-! ## `DecodeError` -/

/-- The first word `w` of a `DecodeErrorKind` encodes one of the 11 variants that own no heap
memory: `2^63 ≤ w < 2^63 + 11`, i.e. index `w ^ 2^63 < 11` (`drop_glue+0x18..+0x2c`). -/
abbrev KindNoHeap (w : BitVec 64) : Prop :=
  0x8000000000000000#64 ≤ w ∧ w < 0x800000000000000b#64

/-- The niche word `2^63 + i` of the variant `i < 11`. -/
def kindWord (i : Nat) : BitVec 64 := 0x8000000000000000#64 + BitVec.ofNat 64 i

/-- The `DecodeErrorKind` first words written before each `from` call of the session-program call
graph (see the module docstring): `InvalidVarint` 1, `RecursionLimitReached` 2, `InvalidWireType` 3,
`InvalidKey` 4, `InvalidTag` 5, `UnexpectedWireType` 6, `BufferUnderflow` 7, `UnexpectedEndGroupTag` 9. -/
def decodeErrorKindWords : List (BitVec 64) :=
  [kindWord 1, kindWord 2, kindWord 3, kindWord 4, kindWord 5, kindWord 6, kindWord 7, kindWord 9]

/-- Guard (kernel-checked): every kind word in `decodeErrorKindWords` owns no heap memory. (Proved per element: a
plain `decide` would pick `BitVec.instDecidableForallBitVec`, which enumerates all `2^64` words.) -/
theorem decodeErrorKindWords_noHeap : ∀ w ∈ decodeErrorKindWords, KindNoHeap w := by
  intro w hw
  simp only [decodeErrorKindWords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- Guard (kernel-checked): `invalidVarintWord` is `kindWord 1`, and the words of
`try_from+0x2ac` / `skip_field+0x27c` / `int32::merge+0x18..+0x24` are `kindWord 3 / 7 / 6`. -/
theorem kindWord_literals :
    invalidVarintWord = kindWord 1 ∧ 0x8000000000000003#64 = kindWord 3 ∧
      0x8000000000000007#64 = kindWord 7 ∧ 0x8000000000000006#64 = kindWord 6 := by
  decide +kernel

/-- One `stack` element, a `(&'static str, &'static str)` location pair: 32 opaque bytes. Nothing
in the session-program call graph reads an element (only `drop_glue` frees the buffer). -/
def stackEntryAt (_ : Unit) (p : BitVec 64) : SepProp :=
  memRegion p 32

/-- **An owned `DecodeError` box at `e` whose `stack` holds `n` locations**: the 72-byte block
(allocator token), the `stack` `Vec` (header at `+0`, `n` opaque 32-byte elements, buffer token
when `cap ≠ 0`), and the 48-byte `description` at `+24` whose first word owns no heap memory
(`KindNoHeap`; the other 40 bytes are not read). This is exactly what `drop_glue` frees. -/
def decodeErrorAtStackLen (A : RustAlloc) (e : BitVec 64) (n : Nat) : SepProp :=
  A.live e 72 8 ∗ vecOf A 32 8 stackEntryAt e (List.replicate n ()) ∗
    (∃∗ w : BitVec 64, ⌜KindNoHeap w⌝ ∗ ((e + 24#64) ↦₆₄ w)) ∗ memRegion (e + 32#64) 40

/-- An owned `DecodeError` box at `e` (any stack length). -/
def decodeErrorAt (A : RustAlloc) (e : BitVec 64) : SepProp :=
  ∃∗ n : Nat, decodeErrorAtStackLen A e n

/-! ## `from` and `push` -/

/-- Stack for the `from` / `push` contracts: the allocator's `allocHookStack` plus their own frames
above it (`Box::new` in `from`, `RawVec::grow_one` / `finish_grow` in `push`, each well under 1 KiB),
rounded up to `2 * allocHookStack`. -/
abbrev decodeErrorHookStack : Nat := 2 * allocHookStack

/-- `<DecodeError as From<DecodeErrorKind>>::from(x0 = &kind)`. Ghost `(k, w)`: the kind's address
and first word. Pre: the 48-byte kind (owned by the callee) with `KindNoHeap w`. Post: `x0` is a
fresh non-null `decodeErrorAtStackLen A x0 0` (empty stack), the kind's bytes are given back
(contents unspecified), trace unchanged. Panic: only if the allocator reported a failure. -/
def decodeErrorFromSpec (A : RustAlloc) : Spec (BitVec 64 × BitVec 64) where
  pre := fun (k, w) s =>
    ⌜s.readReg64 .x0 = k ∧ KindNoHeap w⌝ ∗ (k ↦₆₄ w) ∗ memRegion (k + 8#64) 40 ∗
      A.pool ∗ stackAt s.sp decodeErrorHookStack
  post := fun (k, _) s0 sf =>
    ⌜sf.readReg64 .x0 ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
      memRegion k 48 ∗ A.pool ∗ stackAt s0.sp decodeErrorHookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `<DecodeError>::push(x0 = &mut DecodeError, (x1, x2) = message, (x3, x4) = field)`. Ghost
`(d, e, n)`: the slot `d` holding the box `e`, whose stack has `n < 2^32` locations. Post: the slot
unchanged, the box with `n + 1` locations, trace unchanged. Panic: only if the allocator reported a
failure. -/
def decodeErrorPushSpec (A : RustAlloc) : Spec (BitVec 64 × BitVec 64 × Nat) where
  pre := fun (d, e, n) s =>
    ⌜s.readReg64 .x0 = d ∧ n < 2 ^ 32⌝ ∗ (d ↦₆₄ e) ∗ decodeErrorAtStackLen A e n ∗
      A.pool ∗ stackAt s.sp decodeErrorHookStack
  post := fun (d, e, n) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (d ↦₆₄ e) ∗ decodeErrorAtStackLen A e (n + 1) ∗
      A.pool ∗ stackAt s0.sp decodeErrorHookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

end CryptoVerification.LibsignalTripleRatchet
