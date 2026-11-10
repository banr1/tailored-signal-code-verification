/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
public import Mathlib.Tactic.ToAdditive

/-!
# SPQR V1: shared core types (`src/lib.rs`) and constant-time helpers (`src/util.rs`)

**Trusted in part.** The theorems of `Computational/Theorems/` use every definition in this file
except `Direction.A2B` and `Direction.B2A`, which are checked by Lean (see
`Computational/docs/TRUSTED_BASE.md`).

Shared SPQR V1 types (`Epoch`, `Secret`, `EpochSecret`, `Direction` with `switch` and `toI32`,
`Error` with `isStateDecode`, `SpqrPanic`) and constant-time comparison helpers (`inz`,
`isNonZero`, `compare`) from `spqr` (`src/lib.rs`, `src/util.rs`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1
/-! ## Core types from `src/lib.rs` and `src/proto/pq_ratchet.proto` -/

/-- `pub type Epoch = u64` (`src/lib.rs:40`). -/
abbrev Epoch := BitVec 64

/-- `pub type Secret = Vec<u8>` (`src/lib.rs:41`). -/
abbrev Secret := Bytes

/-- `pub struct EpochSecret` (`src/lib.rs:50–53`). -/
structure EpochSecret where
  epoch : Epoch
  secret : Secret
  deriving DecidableEq, Repr, Inhabited

/-- `pub enum Direction` (`src/proto/pq_ratchet.proto:218–221`, `src/lib.rs:28, 63–70`). -/
inductive Direction where
  | a2b
  | b2a
  deriving DecidableEq, Repr, Inhabited

namespace Direction

abbrev A2B : Direction := .a2b

abbrev B2A : Direction := .b2a

def switch : Direction → Direction
  | .a2b => .b2a
  | .b2a => .a2b

/-- Protobuf `i32` encoding (`0` for `a2b`, `1` for `b2a`). -/
def toI32 : Direction → BitVec 32
  | .a2b => 0#32
  | .b2a => 1#32

/-- `Direction::try_from(v: i32)` (`src/proto/pq_ratchet.proto:218–221`). -/
def fromI32? (v : BitVec 32) : Option Direction :=
  if v = 0#32 then some .a2b
  else if v = 1#32 then some .b2a
  else none

end Direction

/-- `pub enum Error` (`src/lib.rs:96–130`). -/
inductive Error where
  | stateDecode
  | notImplemented
  | msgDecode
  | macVerifyFailed
  | epochOutOfRange (epoch : Epoch)
  | encodingDecoding
  | serialization
  | versionMismatch
  | minimumVersion
  | keyJump (ctr atIdx : BitVec 32)
  | keyTrimmed (atIdx : BitVec 32)
  | keyAlreadyRequested (atIdx : BitVec 32)
  | erroneousDataReceived
  | sendKeyEpochDecreased (sendEpoch epoch : Epoch)
  | invalidParams (msg : String)
  | chainNotAvailable
  deriving DecidableEq, Repr, Inhabited

namespace Error

def isStateDecode : Error → Bool
  | .stateDecode => true
  | _ => false

end Error

/-! ## Panics -/

/-- Shared Rust panic sites (`compareBounds` at `src/util.rs:29`, or `site` for cited panics). -/
inductive SpqrPanic where
  /-- `src/util.rs:29`: `rhs[i]` out of bounds in `compare` when `rhs.len() < lhs.len()`. -/
  | compareBounds
  | site (loc : String)
  deriving DecidableEq, Repr, Inhabited

/-! ## `src/util.rs` -/

/-- `spqr::util::inz(value: u8) -> u8` (`src/util.rs:7–13`). -/
def inz (value : BitVec 8) : BitVec 8 :=
  let v16 : BitVec 16 := value.zeroExtend 16
  let result : BitVec 16 := ((v16 ||| ((~~~v16) + 1#16)) >>> 8) &&& 1#16
  result.truncate 8

def isNonZero (value : BitVec 8) : BitVec 8 :=
  inz value

/-- `spqr::util::compare(lhs: &[u8], rhs: &[u8]) -> u8` (`src/util.rs:25–33`): returns `0` iff
`lhs` equals the first `lhs.length` bytes of `rhs`, or panics with `compareBounds` when
`lhs.length > rhs.length`. -/
def compare (lhs rhs : Bytes) : Except SpqrPanic (BitVec 8) :=
  if lhs.length ≤ rhs.length then
    .ok (isNonZero ((lhs.zip rhs).foldl (fun r (a, b) => r ||| (a ^^^ b)) 0#8))
  else .error .compareBounds

example : compare [1#8, 2#8] [1#8, 2#8] = .ok 0#8 := by decide +kernel
example : compare [1#8, 2#8] [1#8, 3#8] = .ok 1#8 := by decide +kernel
example : compare [1#8] [1#8, 3#8] = .ok 0#8 := by decide +kernel
example : compare [1#8, 2#8] [1#8] = .error .compareBounds := by decide +kernel

end CryptoVerification.LibsignalSpqrV1
