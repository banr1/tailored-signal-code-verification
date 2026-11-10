/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Simulation
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs

/-!
# Little-endian byte encodings and the return helper (`toLEBytes`, `returnToLinkRegister`)

**Trusted: definitions used by the statement.** The theorems of the default library
(`Computational/Theorems/` outside `CliElfLib`) use `toLEBytes`, `blockToBytes`, `bytesToKey` from
this file; the theorems of `Computational/Theorems/Main.lean` (`CliElfLib`) also use
`returnToLinkRegister`. Read them. The theorems here are checked by Lean. See
`Computational/docs/TRUSTED_BASE.md`.

This file defines the little-endian conversions between `BitVec`s (AES blocks and keys from
`LibsignalBinary/Specifications/CryptoGames/AEAD/CBCDefs.lean`) and byte lists, as AArch64 loads
and stores them, together with `returnToLinkRegister`, the return to the caller that the binary
specifications' extern hooks end with. `keyToBytes` and the `memcpy` / `memset` hooks, used only by
proofs, are in `LibsignalBinary/Proofs/AesCbc/LibsignalAesCbcProofDefs.lean`.

Glossary: AAPCS64 = the Arm 64-bit calling convention (arguments in `x0`–`x7`, result in `x0`,
return address in `lr`); LE = little-endian.

`returnToLinkRegister` returns to `lr` and leaves every other register unchanged (the caller keeps
nothing live in caller-saved registers across hook calls).

Despite the file and namespace name, nothing here specifies AES-CBC itself: the cryptographic
primitives' machine code is hooked, not verified (DEV-E8).

## Main definitions

* `toLEBytes`: the low `n` bytes of a `BitVec`, least significant first.
* `blockToBytes`: the 16 LE bytes of an AES `Block`.
* `bytesToKey`: the 256-bit `AesKey` whose LE bytes are the given list.
* `returnToLinkRegister`: return to the caller (`pc := lr`).
-/

@[expose] public section

namespace CryptoVerification
namespace LibsignalAesCbc

open Arm64 ProofLib CryptoGames CryptoGames.CBC

/-! ## Byte encodings (little-endian, as AArch64 loads and stores) -/

/-- The `n` LE bytes of `x`: byte `j` is bits `8j .. 8j+7`. -/
def toLEBytes (n : ℕ) {w : ℕ} (x : BitVec w) : List (BitVec 8) :=
  List.ofFn fun j : Fin n => x.extractLsb' (8 * j.val) 8

/-- The 16 LE bytes of a block (inverse of `bytesToBlock` on 16-byte lists). -/
abbrev blockToBytes (b : Block) : List (BitVec 8) := toLEBytes 16 b

/-- A 256-bit key from its 32 LE bytes. -/
def bytesToKey (bs : List (BitVec 8)) : AesKey :=
  bs.foldr (fun b acc => (acc <<< 8) ||| b.zeroExtend 256) 0

/-! ## Extern hooks -/

/-- Return to the caller: `pc := lr`. -/
def returnToLinkRegister (s : State) : State := s.setPC (s.readReg64 .lr)

end LibsignalAesCbc
end CryptoVerification
