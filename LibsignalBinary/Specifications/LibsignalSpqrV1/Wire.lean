/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Core
public import LibsignalBinary.Specifications.LibsignalSpqr

/-!
# SPQR V1: wire format, `Version`, varint, and `msg_preamble` (`src/lib.rs`)

**Trusted in part.** The theorems of `Computational/Theorems/` use only part of this file (see
`Computational/docs/TRUSTED_BASE.md`): the rest (`encodeVarint`, `decodeVarint`, `decodeVarintAt`,
`decode_varint_at`, `MsgPreamble.ofLibsignalSpqr` / `toLibsignalSpqr`, the `Version` constants `V0`,
`V1`, `MAX` and `DISABLED`, `Version.fromI32?` and `Version.tryFromU8`) is checked by Lean.

Defines the shared wire-format aliases (`MessageKey`, `SerializedState`, `SerializedMessage`,
`empty_state` / `emptyState`), `Version` (`toU8`, `toI32`), 10-byte LEB128 varint codecs
(`MAX_VARINT_BYTES_LEN`, `encode_varint`, `decode_varint`), and message header parser
(`MsgPreamble`, `msg_preamble` / `msgPreamble`), together with equivalence theorems against
`LibsignalSpqr.lean` (`decodeVarintLoop_eq_spqrVarintAux`, `decode_varint_eq_spqrDecodeVarint`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

/-! ## Wire type aliases and `Version` (`src/lib.rs:42–48, 177–195, 237–240`) -/

abbrev MessageKey := Option Bytes

abbrev SerializedState := Bytes

abbrev SerializedMessage := Bytes

def empty_state : SerializedState := []

abbrev emptyState : SerializedState := empty_state

/-- SPQR protocol version (`pub enum Version`, `src/proto/pq_ratchet.proto:213–216`). -/
inductive Version where
  | v0
  | v1
  deriving DecidableEq, Repr, Inhabited

namespace Version

abbrev V0 : Version := .v0

abbrev V1 : Version := .v1

abbrev DISABLED : Version := .v0

abbrev MAX : Version := .v1

def toU8 : Version → BitVec 8
  | .v0 => 0#8
  | .v1 => 1#8

def fromU8? (value : BitVec 8) : Option Version :=
  if value == 0#8 then some .v0
  else if value == 1#8 then some .v1
  else none

def tryFromU8 (value : BitVec 8) : Except String Version :=
  match fromU8? value with
  | some v => .ok v
  | none => .error s!"Expected 0 or 1, got {value.toNat}"

def toI32 : Version → BitVec 32
  | .v0 => 0#32
  | .v1 => 1#32

def fromI32? (value : BitVec 32) : Option Version :=
  if value == 0#32 then some .v0
  else if value == 1#32 then some .v1
  else none

end Version

/-! ## Varint encoding/decoding and `msg_preamble` (`src/lib.rs:507–590`) -/

def MAX_VARINT_BYTES_LEN : Nat := 10

def encodeVarintLoop : Nat → BitVec 64 → Bytes
  | 0, _ => []
  | fuel + 1, a =>
    let byte : BitVec 8 := (a &&& 0x7f#64).truncate 8
    if a < 0x80#64 then
      [byte]
    else
      (0x80#8 ||| byte) :: encodeVarintLoop fuel (a >>> 7)

/-- `encode_varint` (`src/lib.rs:509–521`). -/
def encode_varint (a : BitVec 64) (into : SerializedMessage := []) : SerializedMessage :=
  into ++ encodeVarintLoop MAX_VARINT_BYTES_LEN a

abbrev encodeVarint (a : BitVec 64) (into : SerializedMessage := []) : SerializedMessage :=
  encode_varint a into

/-- Inner loop of `decode_varint` (`src/lib.rs:537–553`); at `i = 9`, `<< 63` drops bits `1..6` of
`b & 0x7f`. -/
def decodeVarintLoop : Nat → BitVec 64 → Bytes → Option (BitVec 64 × Bytes)
  | _, _, [] => none
  | i, out, b :: rest =>
    let out := out ||| ((b &&& 0x7f#8).zeroExtend 64 <<< (7 * i))
    if b &&& 0x80#8 = 0#8 then
      some (out, rest)
    else if i + 1 = MAX_VARINT_BYTES_LEN then
      none
    else
      decodeVarintLoop (i + 1) out rest

/-- LEB128 `u64` decoder (`decode_varint`, `src/lib.rs:524–554`); returns `.error .msgDecode` on
truncation or a continuation bit on the 10th byte. -/
def decode_varint (fromSlice : Bytes) : Except Error (BitVec 64 × Bytes) :=
  match decodeVarintLoop 0 0#64 fromSlice with
  | some res => .ok res
  | none => .error .msgDecode

abbrev decodeVarint := decode_varint

/-- Index-based `decode_varint` (`src/lib.rs:524–554`), returning `(value, newAtIdx)`. -/
def decode_varint_at (fromBytes : Bytes) (atIdx : Nat) : Except Error (BitVec 64 × Nat) :=
  if atIdx ≥ fromBytes.length then
    .error .msgDecode
  else
    let rem := fromBytes.drop atIdx
    match decodeVarintLoop 0 0#64 rem with
    | some (val, rest) => .ok (val, fromBytes.length - rest.length)
    | none => .error .msgDecode

abbrev decodeVarintAt := decode_varint_at

/-- Parsed SPQR message header (`struct MsgPreamble<'a>`, `src/lib.rs:556–561`). -/
structure MsgPreamble where
  version : BitVec 8
  epoch : Epoch
  index : BitVec 32
  remaining : Bytes
  deriving DecidableEq, Repr, Inhabited

namespace MsgPreamble

def toLibsignalSpqr (p : MsgPreamble) : CryptoVerification.LibsignalSpqr.MsgPreamble :=
  ⟨p.version, p.epoch, p.index, p.remaining⟩

def ofLibsignalSpqr (p : CryptoVerification.LibsignalSpqr.MsgPreamble) : MsgPreamble :=
  ⟨p.version, p.epoch, p.index, p.remaining⟩

@[simp]
theorem toEmptyOk_ofEmptyOk (p : CryptoVerification.LibsignalSpqr.MsgPreamble) :
    (ofLibsignalSpqr p).toLibsignalSpqr = p := by
  cases p; rfl

@[simp]
theorem ofEmptyOk_toEmptyOk (p : MsgPreamble) :
    ofLibsignalSpqr p.toLibsignalSpqr = p := by
  cases p; rfl

end MsgPreamble

/-- `msg_preamble` (`src/lib.rs:563–590`): returns all-zero preamble on `[]`, otherwise parses the
version byte, nonzero `u64` varint epoch, and `u32` varint index. -/
def msg_preamble (msg : SerializedMessage) : Except Error MsgPreamble :=
  match msg with
  | [] => .ok { version := 0#8, epoch := 0#64, index := 0#32, remaining := [] }
  | version :: rest => do
    let (epoch, rest) ← decode_varint rest
    if epoch = 0#64 then
      .error .msgDecode
    else
      let (index64, rest) ← decode_varint rest
      if index64.toNat < 2 ^ 32 then
        .ok { version := version, epoch := epoch, index := index64.setWidth 32, remaining := rest }
      else
        .error .msgDecode

abbrev msgPreamble := msg_preamble

/-! ## Equivalence with `CryptoVerification.LibsignalSpqr` (`LibsignalSpqr.lean`) -/

theorem decodeVarintLoop_eq_spqrVarintAux (i : Nat) (out : BitVec 64) (bs : Bytes) :
    decodeVarintLoop i out bs = CryptoVerification.LibsignalSpqr.spqrVarintAux i out bs := by
  induction bs generalizing i out with
  | nil => rfl
  | cons b rest ih =>
    simp only [decodeVarintLoop, CryptoVerification.LibsignalSpqr.spqrVarintAux,
      MAX_VARINT_BYTES_LEN, CryptoVerification.LibsignalSpqr.maxVarintBytes]
    split
    · rfl
    · by_cases h10 : i + 1 = 10 <;> simp [h10, ih]

theorem decode_varint_eq_spqrDecodeVarint (bs : Bytes) :
    decode_varint bs =
      match CryptoVerification.LibsignalSpqr.spqrDecodeVarint bs with
      | some res => .ok res
      | none => .error .msgDecode := by
  simp only [decode_varint, CryptoVerification.LibsignalSpqr.spqrDecodeVarint,
    decodeVarintLoop_eq_spqrVarintAux]
  rfl

theorem msg_preamble_eq_msgPreamble? (msg : SerializedMessage) :
    msg_preamble msg =
      match CryptoVerification.LibsignalSpqr.msgPreamble? msg with
      | some p => .ok (MsgPreamble.ofLibsignalSpqr p)
      | none => .error .msgDecode := by
  cases msg with
  | nil => rfl
  | cons version rest =>
    simp only [msg_preamble, CryptoVerification.LibsignalSpqr.msgPreamble?,
      decode_varint_eq_spqrDecodeVarint]
    cases CryptoVerification.LibsignalSpqr.spqrDecodeVarint rest with
    | none => rfl
    | some epRest =>
      rcases epRest with ⟨epoch, rest1⟩
      by_cases hEp : epoch = 0#64
      · simp [hEp, Bind.bind, Except.bind]
      · simp only [hEp, ↓reduceIte, Bind.bind, Except.bind]
        cases CryptoVerification.LibsignalSpqr.spqrDecodeVarint rest1 with
        | none => rfl
        | some idxRest =>
          rcases idxRest with ⟨index64, rest2⟩
          by_cases hIdx : index64.toNat < 4294967296 <;> simp [hIdx, MsgPreamble.ofLibsignalSpqr]

end CryptoVerification.LibsignalSpqrV1
