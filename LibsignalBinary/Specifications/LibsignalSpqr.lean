/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.HkdfSalt
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# `spqr::recv` on an Empty Post-Quantum State (`spqrRecvEmpty`)

**Checked by Lean.** Models `spqr::recv` on an empty post-quantum ratchet state (`state = []`,
DEV-LS24; see `Computational/docs/TRUSTED_BASE.md`): returns `Ok([], none)` if `msg_preamble(msg)`
succeeds (either `msg = []`, or a version byte followed by a non-zero `u64` epoch varint and a
`< 2^32` index varint under `spqr`'s overflow-dropping 10-byte LEB128 decoder) and
`Err(MsgDecode)` (`.error false`) otherwise.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqr

open CryptoGames.HKDF

/-- `MAX_VARINT_BYTES_LEN` (`src/lib.rs:507`). -/
def maxVarintBytes : Nat := 10

/-- The loop of spqr's `decode_varint` (`src/lib.rs:537–553`) at iteration `i` (`i < 10`), with
`out` the bits decoded so far and `bs` the bytes from `start_at + i` on: the value and the bytes
after the terminating byte, or `none` (`Err(MsgDecode)`). The loop runs while
`i < max_i = min(10, len − start_at)`: running out of bytes (`[]`) or reaching `i = 10` without a
byte `< 0x80` is an error. `out` is a `u64`: the shift drops bits past 63, with no overflow check. -/
def spqrVarintAux : Nat → BitVec 64 → List (BitVec 8) → Option (BitVec 64 × List (BitVec 8))
  | _, _, [] => none
  | i, out, b :: rest =>
    let out := out ||| ((b &&& 0x7F#8).zeroExtend 64 <<< (7 * i))
    if b &&& 0x80#8 = 0#8 then some (out, rest)
    else if i + 1 = maxVarintBytes then none
    else spqrVarintAux (i + 1) out rest

/-- spqr's `decode_varint(from, at)` (`src/lib.rs:523–554`) on `bs` = `from[at..]`: `Err` if
`at ≥ len` (`bs = []`), else the loop `spqrVarintAux` from `i = 0`, `out = 0`. Returns the value
and `from[at'..]` for the advanced `at'`. -/
def spqrDecodeVarint (bs : List (BitVec 8)) : Option (BitVec 64 × List (BitVec 8)) :=
  spqrVarintAux 0 0#64 bs

/-- `MsgPreamble` (`src/lib.rs:556–561`): version byte, epoch, index, remaining bytes. -/
structure MsgPreamble where
  version : BitVec 8
  epoch : BitVec 64
  index : BitVec 32
  remaining : List (BitVec 8)
  deriving DecidableEq

/-- **`msg_preamble(msg)`** (`src/lib.rs:563–590`): `some` = `Ok`, `none` = `Err(MsgDecode)`.
* empty message: `Ok { version: 0, epoch: 0, index: 0, remaining: [] }` (`:564–571`);
* else `version = msg[0]` (`:572`), `epoch = decode_varint(msg, 1)` (`:574`), rejected if `0`
  (`:575–577`); `index = decode_varint(..)` converted with `u32::try_from`, rejected if
  `≥ 2^32` (`:578–580`); the `at > len` test (`:581–583`) cannot fire after a successful
  `decode_varint`; `remaining = msg[at..]` (`:588`). -/
def msgPreamble? : List (BitVec 8) → Option MsgPreamble
  | [] => some ⟨0#8, 0#64, 0#32, []⟩
  | version :: rest =>
    match spqrDecodeVarint rest with
    | none => none
    | some (epoch, rest) =>
      if epoch = 0#64 then none
      else match spqrDecodeVarint rest with
        | none => none
        | some (index, rest) =>
          if index.toNat < 2 ^ 32 then some ⟨version, epoch, index.setWidth 32, rest⟩
          else none

/-- `msg_preamble(msg)` is `Ok`. -/
def msgPreambleOk (msg : List (BitVec 8)) : Bool := (msgPreamble? msg).isSome

/-- **`spqr::recv(state, msg)` on an empty `state`** (module docstring, `src/lib.rs:355–380`): the
new state `[]` and no message key if the preamble parses, else `Err(MsgDecode)` (`false`: not
`StateDecode`). -/
def spqrRecvEmpty (msg : List (BitVec 8)) : Except Bool (List (BitVec 8) × Salt) :=
  if msgPreambleOk msg then .ok ([], none) else .error false

/-! ## Guards (kernel-checked) -/

 def bytes (l : List Nat) : List (BitVec 8) := l.map (BitVec.ofNat 8)

/-- One-byte and two-byte varints (`300 = [0xac, 0x02]`), with the rest returned. -/
theorem spqrDecodeVarint_small :
    spqrDecodeVarint (bytes [0x05, 0xff]) = some (5#64, bytes [0xff]) ∧
      spqrDecodeVarint (bytes [0xac, 0x02, 0x07]) = some (300#64, bytes [0x07]) := by
  decide +kernel

/-- Empty input, a truncated varint, and ten bytes without a terminator are errors (an 11th byte is
never read). -/
theorem spqrDecodeVarint_err :
    spqrDecodeVarint [] = none ∧ spqrDecodeVarint (bytes [0xac, 0x82]) = none ∧
      spqrDecodeVarint (List.replicate 10 0x80#8 ++ [0x00#8]) = none := by
  decide +kernel

/-- Unlike prost, no overflow check: nine `0xff` then `0x02` decodes, the bit of `0x02` past bit 63
dropped (prost's `decodeVarint` returns `none`); `0x01` gives `2^64 - 1`. -/
theorem spqrDecodeVarint_tenBytes :
    spqrDecodeVarint (List.replicate 9 0xff#8 ++ [0x02#8]) = some (0x7fffffffffffffff#64, []) ∧
      spqrDecodeVarint (List.replicate 9 0xff#8 ++ [0x01#8]) = some (0xffffffffffffffff#64, []) := by
  decide +kernel

/-- Accepted preambles: the empty message; version 1, epoch 1, index 0; trailing bytes after the
index are not read; index `2^32 - 1` (`[0xff, 0xff, 0xff, 0xff, 0x0f]`); any version byte. -/
theorem msgPreambleOk_accepts :
    msgPreambleOk [] = true ∧ msgPreambleOk (bytes [0x01, 0x01, 0x00]) = true ∧
      msgPreambleOk (bytes [0x01, 0x01, 0x00, 0xde, 0xad]) = true ∧
      msgPreambleOk (bytes [0x01, 0x01, 0xff, 0xff, 0xff, 0xff, 0x0f]) = true ∧
      msgPreambleOk (bytes [0xff, 0x02, 0x05]) = true := by
  decide +kernel

/-- Rejected preambles: a lone version byte (no epoch); epoch 0; a missing index; index `2^32`
(`[0x80, 0x80, 0x80, 0x80, 0x10]`); a truncated epoch varint; an epoch that wraps to 0 in `u64`
(nine `0x80` then `0x02`: only bit 64 set, dropped). -/
theorem msgPreambleOk_rejects :
    msgPreambleOk (bytes [0x01]) = false ∧ msgPreambleOk (bytes [0x01, 0x00, 0x00]) = false ∧
      msgPreambleOk (bytes [0x01, 0x01]) = false ∧
      msgPreambleOk (bytes [0x01, 0x01, 0x80, 0x80, 0x80, 0x80, 0x10]) = false ∧
      msgPreambleOk (bytes [0x01, 0x81]) = false ∧
      msgPreambleOk (0x01#8 :: (List.replicate 9 0x80#8 ++ [0x02#8, 0x00#8])) = false := by
  decide +kernel

/-- The decoded fields of a preamble. -/
theorem msgPreamble?_fields :
    msgPreamble? (bytes [0x01, 0xac, 0x02, 0x03, 0x09]) = some ⟨1#8, 300#64, 3#32, bytes [0x09]⟩ := by
  decide +kernel

end CryptoVerification.LibsignalSpqr
