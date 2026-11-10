/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import ProofLib.Lemmas

/-!
# `compute_mac` call environment `MacEnv` and pure HMAC-SHA256 intermediates

Bundles the call parameters of `compute_mac` (`MacEnv`) and defines its pure HMAC-SHA256
chaining states, padded messages, and 9-byte output predicate (`resultOk`).
-/

@[expose] public section

namespace CryptoVerification
namespace LibsignalHmac

open Arm64 ProofLib CryptoGames CryptoGames.HMAC

/-! ## Call environment and HMAC-SHA256 intermediates -/

/-- Size of `compute_mac`'s frame `[sp₀ − 0x230, sp₀)` (0x60 saved registers + 0x1d0 locals). -/
abbrev macFrameLen : ℕ := 0x230

/-- The arguments of one `compute_mac` call: image base, the addresses and contents of the
inputs, the 9-byte result buffer, and the entry `sp` / return address. -/
structure MacEnv where
  base : BitVec 64
  sik  : BitVec 64
  rik  : BitVec 64
  key  : BitVec 64
  msg  : BitVec 64
  out  : BitVec 64
  sp0  : BitVec 64
  ret0 : BitVec 64
  vsik : List.Vector (BitVec 8) 33
  vrik : List.Vector (BitVec 8) 33
  vkey : List (BitVec 8)
  vmsg : List (BitVec 8)

namespace MacEnv

variable (e : MacEnv) (F : ShaState → List (BitVec 8) → ShaState)

/-- `compute_mac`'s frame pointer after the prologue (`sp₀ − 0x60`). -/
abbrev cfp : BitVec 64 := e.sp0 - 0x60#64
/-- `compute_mac`'s stack pointer after the prologue (`sp₀ − 0x230`). -/
abbrev csp : BitVec 64 := e.sp0 - 0x230#64
abbrev L : ℕ := e.vmsg.length
/-- `n`: full message blocks compressed in place (long path, `L ≥ 62`). -/
abbrev nFull : ℕ := (e.L - 62) / 64

/-- The key zero-padded to 64 bytes (`get_der_key` for `|key| = 32`). -/
abbrev k0 : List (BitVec 8) := e.vkey ++ List.replicate (64 - e.vkey.length) 0
abbrev ipadKey : List (BitVec 8) := e.k0.map (· ^^^ 0x36)
abbrev opadKey : List (BitVec 8) := e.k0.map (· ^^^ 0x5c)

/-- The inner SHA-256 message `(k⊕ipad) ‖ sik ‖ rik ‖ msg` (`130 + L` bytes). -/
abbrev innerMsg : List (BitVec 8) := e.ipadKey ++ e.vsik.toList ++ e.vrik.toList ++ e.vmsg
/-- `B` at the finalize: whole blocks of `innerMsg` compressed before padding. -/
abbrev innerB : ℕ := e.innerMsg.length / 64
/-- `pos` at the finalize: buffered bytes of `innerMsg`. -/
abbrev innerPos : ℕ := e.innerMsg.length % 64
/-- The buffered tail of `innerMsg` at the finalize. -/
abbrev innerTail : List (BitVec 8) := e.innerMsg.drop (64 * e.innerB)

/-- Inner chaining state after the first `i` 64-byte blocks of `innerMsg`. -/
abbrev hState (i : ℕ) : ShaState := ((chunks64 e.innerMsg).take i).foldl F sha256IV
/-- Outer chaining state after the `k⊕opad` block. -/
abbrev oState1 : ShaState := F sha256IV e.opadKey

/-- `sha256Pad innerMsg` and its length (a multiple of 64). -/
abbrev innerPadded : List (BitVec 8) := sha256Pad e.innerMsg
/-- The inner digest. -/
abbrev innerHash : List (BitVec 8) := sha256With F e.innerMsg
/-- The outer SHA-256 message `(k⊕opad) ‖ innerHash` (96 bytes). -/
abbrev outerMsg : List (BitVec 8) := e.opadKey ++ e.innerHash F

/-- The 9 result bytes of a `compute_mac` call: `1 ‖ hmacSha256Trunc8 …` (`Some`), or just the tag byte `0`
(`None`, the 8 payload bytes unspecified) if the key does not have 32 bytes. -/
def resultOk (m : Memory) : Prop :=
  if e.vkey.length = 32 then
    m.read8 e.out = 1#8 ∧
      m.readBytes (e.out + 1#64) 8 = hmacSha256Trunc8 F e.vkey (e.vsik.toList ++ e.vrik.toList ++ e.vmsg)
  else m.read8 e.out = 0#8

end MacEnv

end LibsignalHmac
end CryptoVerification
