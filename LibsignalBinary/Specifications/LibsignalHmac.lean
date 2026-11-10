/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Simulation
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.LibsignalAesCbc

/-!
# SHA-256 Compression Hook and Chaining-State Layout

**Trusted: definitions used by the statement.** Memory layout of `sha2`'s 8-word little-endian
SHA-256 chaining state (`shaStateBytes`, `readShaState`) and the extern hook `compress256Hook`
modeling `sha2::sha256::compress256(state: &mut [u32; 8], blocks: &[[u8; 64]])` over an abstract
compression function `F : ShaState → List (BitVec 8) → ShaState`. See
`Computational/docs/TRUSTED_BASE.md`.
-/

@[expose] public section

namespace CryptoVerification
namespace LibsignalHmac

open Arm64 ProofLib CryptoGames CryptoGames.HMAC
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister toLEBytes)

/-- The 32 bytes of a chaining state as stored by `sha2` (`[u32; 8]`, native LE words). -/
def shaStateBytes (h : ShaState) : List (BitVec 8) :=
  h.toList.flatMap (toLEBytes 4)

/-- The chaining state stored at `a`: 8 LE 32-bit words. -/
def readShaState (m : Memory) (a : BitVec 64) : ShaState :=
  List.Vector.ofFn fun i : Fin 8 => m.read32 (a + BitVec.ofNat 64 (4 * i.val))

/-- `sha2::sha256::compress256(state = x0, blocks.ptr = x1, blocks.len = x2)`: with `st` the
8 LE words at `x0` and `bs` the `x2 · 64` bytes at `x1`, `mem[x0 .. x0+32] :=
shaStateBytes ((chunks64 bs).foldl F st)` (all inputs read before writing); `pc := lr`. -/
def compress256Hook (F : ShaState → List (BitVec 8) → ShaState) (s : State) : State :=
  let st := readShaState s.mem (s.readReg64 .x0)
  let bs := s.mem.readBytes (s.readReg64 .x1) (64 * (s.readReg64 .x2).toNat)
  returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x0) (shaStateBytes ((chunks64 bs).foldl F st))))

end LibsignalHmac
end CryptoVerification
