/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.WireAeadDefs
public import Computational.Tests.AEAD.LibsignalAeadTest
public meta import LibsignalBinary.Specifications.CryptoGames.AEAD.WireAeadDefs -- shake: keep
public meta import Computational.Tests.AEAD.LibsignalAeadTest -- shake: keep
public meta import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs -- shake: keep
public meta import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs -- shake: keep
public meta import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead -- shake: keep
public import Computational.Proofs.CryptoGames.AEAD.WireAeadProofDefs
public meta import Computational.Proofs.CryptoGames.AEAD.WireAeadProofDefs

/-!
# Variable-Length Raw-Wire AEAD Tests

Tests `CryptoGames.LibsignalAead.WireAEAD` (`WireAeadDefs.lean`) via `#guard` using length-prefixed
toy wire codecs `v ‖ len(body) (2B LE) ‖ body ‖ h`. Checks honest round-trips, tampering rejection,
raw-wire rejection of non-canonical version bytes, variable-length ciphertext bodies, and agreement
with `etmWire`.
-/

@[expose] public section

namespace CryptoGames.LibsignalAead.WireTests

open CBC HMAC WireAEAD LibsignalAead.Tests

/-- Parse `v ‖ len (2 bytes LE) ‖ body ‖ h` given the version-byte check `ok`. -/
def lenParse (ok : BitVec 8 → Bool) :
    List (BitVec 8) → Option (List (BitVec 8) × List (BitVec 8))
  | v :: l0 :: l1 :: rest =>
    let n := l0.toNat + 256 * l1.toNat
    if ok v ∧ n ≤ rest.length then some (rest.drop n, rest.take n) else none
  | _ => none

/-- Encode `0x44 ‖ len (2 bytes LE) ‖ body ‖ h` (bodies shorter than `2¹⁶` round-trip). -/
def lenEncode (h body : List (BitVec 8)) : List (BitVec 8) :=
  0x44 :: BitVec.ofNat 8 body.length :: BitVec.ofNat 8 (body.length / 256) :: (body ++ h)

def toyCodec : WireCodec (List (BitVec 8)) := ⟨lenEncode, lenParse (· == 0x44)⟩

/-- Non-canonical toy codec accepting any version byte `0x40..0x4f` while encoding `0x44`. -/
def looseCodec : WireCodec (List (BitVec 8)) := ⟨lenEncode, lenParse (fun v => v >>> 4 == 4)⟩

abbrev scheme (codec : WireCodec (List (BitVec 8))) (ℓ : ℕ) :=
  libsignalWireAead E D F ℓ codec toyAddrs (some hdr)

def wireL : List (BitVec 8) × BitVec 64 := (scheme looseCodec 10).enc key ids hdr m

#guard (scheme looseCodec 10).dec key ids wireL == some (hdr, m.toList)
#guard (scheme toyCodec 10).dec key ids ((scheme toyCodec 10).enc key ids hdr m) ==
  some (hdr, m.toList)
#guard wireL == send E D F 10 (looseCodec.toWireEnc (nBlocks 10)) key ids hdr m
#guard recv E D F 10 (looseCodec.toWireEnc (nBlocks 10)) toyAddrs key ids (some hdr) wireL ==
  some (hdr, m)
#guard (scheme looseCodec 10).dec key ids (wireL.1, wireL.2 ^^^ 1) == none
#guard (scheme looseCodec 10).dec key ids (wireL.1.set 5 (wireL.1[5]! ^^^ 1), wireL.2) == none
#guard (scheme looseCodec 10).dec key ids' wireL == none
#guard (libsignalWireAead E D F 10 looseCodec toyAddrs (some (bs [9]))).dec key ids wireL == none

/-- Honest wire with version byte mutated `0x44 → 0x45`: accepted by `looseCodec.parse`, rejected
by raw-wire MAC verification. -/
def wireV : List (BitVec 8) × BitVec 64 := (wireL.1.set 0 0x45, wireL.2)

#guard looseCodec.parse wireV.1 == looseCodec.parse wireL.1
#guard (looseCodec.parse wireV.1).isSome
#guard (scheme looseCodec 10).dec key ids wireV == none

def m20 : Plain 20 := ⟨bs (List.range 20), rfl⟩

/-- Validly MACed 2-block ciphertext (`ℓ = 20`), decrypted by variable-length `libsignalWireAead`
(`ℓ = 10`) and rejected by fixed-block `recv`. -/
def wire20 : List (BitVec 8) × BitVec 64 :=
  let ser := lenEncode hdr (((cbcPkcs7EncryptOnly E 20).enc key.1 m20).toList.flatMap blockToBytesLE)
  (ser, (hmacScheme F).tag key.2 (ids.toList ++ ser))

#guard (looseCodec.parse wire20.1).map (·.2.length) == some 32
#guard (scheme looseCodec 10).dec key ids wire20 == some (hdr, m20.toList)
#guard recv E D F 10 (looseCodec.toWireEnc (nBlocks 10)) toyAddrs key ids (some hdr) wire20 == none

/-- Validly MACed 17-byte body (not a multiple of 16), rejected by `cbcDecRaw`. -/
def wire17 : List (BitVec 8) × BitVec 64 :=
  let ser := lenEncode hdr (bs (List.range 17))
  (ser, (hmacScheme F).tag key.2 (ids.toList ++ ser))

#guard (looseCodec.parse wire17.1).map (·.2.length) == some 17
#guard (scheme looseCodec 10).dec key ids wire17 == none

def wire0 : List (BitVec 8) × BitVec 64 :=
  let ser := lenEncode hdr []
  (ser, (hmacScheme F).tag key.2 (ids.toList ++ ser))

#guard (scheme looseCodec 10).dec key ids wire0 == none

-- Agreement with generic `etmWire` instantiation.
#guard (etmWire (cbcPkcs7EncryptOnly E 10) ((hmacScheme F).precomp wireMacInput) (wireEncode looseCodec)
    (openWire D looseCodec toyAddrs (some hdr))).dec key ids wireL == some (hdr, m.toList)

end CryptoGames.LibsignalAead.WireTests
