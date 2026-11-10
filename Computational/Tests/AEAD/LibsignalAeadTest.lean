/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead
public import Computational.Tests.AEAD.CBCDecTest
public import Computational.Tests.AEAD.HMACTest
public meta import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead -- shake: keep
public meta import Computational.Tests.AEAD.CBCDecTest -- shake: keep
public meta import Computational.Tests.AEAD.HMACTest -- shake: keep
public meta import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs -- shake: keep
public import Computational.Proofs.CryptoGames.AEAD.LibsignalAeadProofDefs
public meta import Computational.Proofs.CryptoGames.AEAD.LibsignalAeadProofDefs

/-!
# Fixed-Block Per-Message AEAD Tests

Tests `CryptoGames.LibsignalAead` (`LibsignalAead.lean`) via `#guard` using `toyE`/`toyD` from
`CBCDecTest`, `sha256Compress` from `HMACTest`, and a toy wire encoding `0x44 ‖ body ‖ h`.
Contrasts raw-wire MAC verification against re-encoded MAC verification under a non-canonical
version-byte parser, and proves `RoundTrip` satisfiability on `byteEnc`.
-/

@[expose] public section

namespace CryptoGames.LibsignalAead.Tests

open CBC HMAC

def bs (l : List ℕ) : List (BitVec 8) := l.map (BitVec.ofNat 8)

/-- Parse `16 n` body bytes followed by the header, given the version-byte check `ok`. -/
def toyParse (ok : BitVec 8 → Bool) (n : ℕ) :
    List (BitVec 8) → Option (List (BitVec 8) × List.Vector Block n)
  | v :: rest =>
    if ok v ∧ 16 * n ≤ rest.length then
      let cs := chunks16 (rest.take (16 * n))
      if hc : cs.length = n then some (rest.drop (16 * n), ⟨cs, hc⟩) else none
    else none
  | [] => none

/-- Toy wire encoding of a byte-string header and an `n`-block body: `0x44 ‖ body ‖ h`. -/
def toyEnc (n : ℕ) : WireEnc (List (BitVec 8)) n where
  encode h c := 0x44 :: (c.toList.flatMap blockToBytesLE ++ h)
  parse := toyParse (· == 0x44) n

/-- Non-canonical variant of `toyEnc`: the parser accepts any version byte `0x40..0x4f` (ignoring
the low nibble, as in `SignalMessage::try_from`), while the encoder writes `0x44`. -/
def looseEnc (n : ℕ) : WireEnc (List (BitVec 8)) n where
  encode := (toyEnc n).encode
  parse := toyParse (fun v => v >>> 4 == 4) n

def toyAddrs (h : List (BitVec 8)) : Option (List (BitVec 8)) := if h = [] then none else some h

abbrev E := CBC.Tests.toyE
abbrev D := CBC.Tests.toyD
abbrev F := HMAC.Tests.sha256Compress

def key : (AesKey × Block) × BitVec 256 := ((CBC.Tests.key, CBC.Tests.iv), 0x1234567890abcdef)
def ids : SerializedIdentityKeys := ⟨bs ([5] ++ List.range' 1 32 ++ [5] ++ List.range' 101 32), rfl⟩
def ids' : SerializedIdentityKeys := ⟨bs ([5] ++ List.range' 2 32 ++ [5] ++ List.range' 101 32), rfl⟩
def hdr : List (BitVec 8) := bs [1, 2, 3]
def m : Plain 10 := CBC.Tests.m10

def wire : List (BitVec 8) × BitVec 64 := send E D F 10 (toyEnc (nBlocks 10)) key ids hdr m

def rcv (ids : SerializedIdentityKeys) (expected : Option (List (BitVec 8))) (w : List (BitVec 8) × BitVec 64) :=
  recv E D F 10 (toyEnc (nBlocks 10)) toyAddrs key ids expected w

#guard (toyEnc (nBlocks 10)).parse wire.1 ==
  some (hdr, ((msgAead E D F 10 (toyEnc (nBlocks 10))).enc key (ids, hdr) m).1)
#guard rcv ids (some hdr) wire == some (hdr, m)
#guard rcv ids (some hdr) (wire.1, wire.2 ^^^ 1) == none
#guard rcv ids (some hdr) (wire.1.set 7 (wire.1[7]! ^^^ 1), wire.2) == none
#guard rcv ids (some hdr) (wire.1.set 17 (wire.1[17]! ^^^ 1), wire.2) == none
#guard rcv ids' (some hdr) wire == none
#guard rcv ids (some (bs [9])) wire == none
#guard rcv ids none wire == none
-- Empty header (`addresses = none`) is accepted regardless of `expected`.
def wire0 : List (BitVec 8) × BitVec 64 := send E D F 10 (toyEnc (nBlocks 10)) key ids [] m
#guard rcv ids none wire0 == some ([], m)
#guard rcv ids (some (bs [9])) wire0 == some ([], m)
#guard rcv ids (some hdr) ([], wire.2) == none
def hdr300 : List (BitVec 8) := bs (List.replicate 300 7)
def wire300 : List (BitVec 8) × BitVec 64 := send E D F 10 (toyEnc (nBlocks 10)) key ids hdr300 m
#guard rcv ids (some hdr300) wire300 == some (hdr300, m)

/-- Honest `looseEnc` wire with version byte mutated `0x44 → 0x45`, which `looseEnc.parse` maps to
the same `(h, c)`. -/
def wireV : List (BitVec 8) × BitVec 64 :=
  let w := send E D F 10 (looseEnc (nBlocks 10)) key ids hdr m
  (w.1.set 0 0x45, w.2)

#guard (looseEnc (nBlocks 10)).parse wireV.1 == (looseEnc (nBlocks 10)).parse wire.1
-- `recv` MACs raw received bytes and rejects `wireV`, whereas `msgAead.dec` re-encodes and accepts.
#guard recv E D F 10 (looseEnc (nBlocks 10)) toyAddrs key ids (some hdr) wireV == none
#guard (match (looseEnc (nBlocks 10)).parse wireV.1 with
    | none => none
    | some (h, c) => (msgAead E D F 10 (looseEnc (nBlocks 10))).dec key (ids, h) (c, wireV.2)) ==
  some m

set_option maxHeartbeats 2000000 in
theorem bytesToBlock_blockToBytesLE' (b : Block) : bytesToBlock (blockToBytesLE b) = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [blockToBytesLE, bytesToBlock, List.ofFn_succ, List.ofFn_zero, List.foldr_cons,
    List.foldr_nil, Fin.val_zero, Fin.val_succ]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

/-- Reads `n` consecutive 16-byte blocks from the front of a byte list. -/
def peel : (n : ℕ) → List (BitVec 8) → List.Vector Block n
  | 0, _ => List.Vector.nil
  | n + 1, l => bytesToBlock (l.take 16) ::ᵥ peel n (l.drop 16)

theorem peel_flatMap (n : ℕ) (c : List.Vector Block n) (rest : List (BitVec 8)) :
    peel n (c.toList.flatMap blockToBytesLE ++ rest) = c := by
  induction n generalizing rest with
  | zero => exact (List.Vector.eq_nil c).symm
  | succ n ih =>
    obtain ⟨b, c', rfl⟩ : ∃ b c', c = b ::ᵥ c' := ⟨c.head, c.tail, (List.Vector.cons_head_tail c).symm⟩
    have h16 : (blockToBytesLE b).length = 16 := by simp [blockToBytesLE]
    simp only [peel, List.Vector.toList_cons, List.flatMap_cons, List.append_assoc]
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
      List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
      List.nil_append, ih, bytesToBlock_blockToBytesLE']

/-- Wire encoding with a 1-byte header prefix followed by `n` 16-byte blocks. -/
def byteEnc (n : ℕ) : WireEnc (BitVec 8) n where
  encode h c := h :: c.toList.flatMap blockToBytesLE
  parse
    | h :: rest => some (h, peel n rest)
    | [] => none

example (n : ℕ) : RoundTrip (byteEnc n) := fun h c => by
  simpa [byteEnc] using peel_flatMap n c []

end CryptoGames.LibsignalAead.Tests
