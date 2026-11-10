/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalAesCbc
public import Arm64
public import ProofLib.Simulation
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs

/-!
# AES-CBC Proof Helpers and libc Memory Hooks

Key-encoding helper `keyToBytes` and reference `memcpy`/`memset` register-hook transitions for
`LibsignalBinary.Specifications.LibsignalAesCbc`.
-/

@[expose] public section

namespace CryptoVerification
namespace LibsignalAesCbc
open Arm64 ProofLib CryptoGames CryptoGames.CBC

/-- The 32 LE bytes of a 256-bit key. -/
abbrev keyToBytes (k : AesKey) : List (BitVec 8) := toLEBytes 32 k

/-- `memcpy(dst = x0, src = x1, n = x2) -> dst`: `mem[dst .. dst+n] := mem[src .. src+n]`
(source read before writing). -/
def memcpyHook (s : State) : State :=
  returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x0)
    (s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat)))

/-- `memset(dst = x0, c = x1, n = x2) -> dst`: `n` copies of the byte `c mod 256` at `dst`. -/
def memsetHook (s : State) : State :=
  returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x0)
    (List.replicate (s.readReg64 .x2).toNat ((s.readReg64 .x1).truncate 8))))

end LibsignalAesCbc
end CryptoVerification
