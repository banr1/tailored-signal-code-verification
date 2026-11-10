/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.Defs

/-!
# `kem::Key<Public>::deserialize` Specification

Models `kem::PublicKey::deserialize` (`rust/protocol/src/kem.rs:319-332`, `252` bytes, frame
`0x30`). In `Kyber1024`-only builds, `KeyType` is zero-sized and `key_length` returns `1568`.

Arguments: `x0` is the 24-byte result slot `r`, and `(x1, x2)` is the input byte slice `bs`:
- `bs = []`: writes `[r] = speWord 7` (`NoKeyTypeIdentifier`);
- `bs[0] ≠ 0x08`: writes `[r] = speWord 31` (`BadKEMKeyType`) and byte `[r + 8] = bs[0]`;
- `bs.length ≠ 1569`: writes `[r] = speWord 33` (`BadKEMKeyLength`) and `[r + 8] = bs.length`;
- `bs = 0x08 :: key` with `key.length = 1568`: allocates `1568` bytes via `__rust_alloc(1568, 1)`,
  copies `key`, and writes `[r] = -2` (`Ok`), `[r + 8] = buf`, `[r + 16] = 1568`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.Cli

abbrev cliKemDeserializeName : String :=
  "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"

/-- Kyber1024 public key payload length (`1568` bytes). -/
abbrev kemPkLen : Nat := 1568

/-- The outcome of `kem::PublicKey::deserialize` on `Kyber1024`-only builds. -/
inductive KemDeserResult where
  /-- `Ok`: the key bytes after the type byte. -/
  | ok (key : List (BitVec 8))
  /-- `NoKeyTypeIdentifier` (empty input). -/
  | noKeyType
  /-- `BadKEMKeyType t` (first byte `t ≠ 8`). -/
  | badType (t : BitVec 8)
  /-- `BadKEMKeyLength (Kyber1024, n)` (input length `n ≠ 1569`). -/
  | badLength (n : Nat)

/-- Pure specification of `kem::PublicKey::deserialize`. -/
def kemPkDeserialize : List (BitVec 8) → KemDeserResult
  | [] => .noKeyType
  | t :: rest =>
    if t ≠ 0x08#8 then .badType t
    else if rest.length ≠ kemPkLen then .badLength (rest.length + 1)
    else .ok rest

/-- The result slot `r` after the call (only `r .. r+24` is written). `Ok` (word `-2`) holds an
owned `Box<[u8]>` (`ptr`, `len`) at `r + 8`. -/
def kemDeserResAt (A : RustAlloc) (r : BitVec 64) : KemDeserResult → SepProp
  | .ok key =>
    (r ↦₆₄ 0xfffffffffffffffe#64) ∗ (∃∗ buf : BitVec 64, boxU8At A (r + 8#64) buf key)
  | .noKeyType =>
    (r ↦₆₄ speWord 7) ∗ memRegion (r + 8#64) 16
  | .badType t =>
    (r ↦₆₄ speWord 31) ∗ ((r + 8#64) ↦₈ t) ∗ memRegion (r + 9#64) 15
  | .badLength n =>
    (r ↦₆₄ speWord 33) ∗ ((r + 8#64) ↦₆₄ BitVec.ofNat 64 n) ∗ memRegion (r + 16#64) 8

/-- Ghost of a `kem::PublicKey::deserialize` call: the result slot (`x0`) and the input slice
(`x1`, `x2`) with its bytes `bs` (read-only iff `ro`). -/
structure KemDeserializeGhost where
  r : BitVec 64
  ro : Bool
  p : BitVec 64
  bs : List (BitVec 8)

def cliKemDeserializeSpec (A : RustAlloc) (stk : Nat) : Spec KemDeserializeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.r ∧ s.readReg64 .x1 = x.p ∧
      s.readReg64 .x2 = BitVec.ofNat 64 x.bs.length ∧ x.bs.length < 2 ^ 63⌝ ∗
      memRegion x.r 24 ∗ SpqrV1.ChainProofs.bytesAt x.ro x.p x.bs ∗
      A.pool ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      kemDeserResAt A x.r (kemPkDeserialize x.bs) ∗ SpqrV1.ChainProofs.bytesAt x.ro x.p x.bs ∗
      A.pool ∗ stackAt s0.sp stk
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

end CryptoVerification.SignalSession.Cli.RunProofs
