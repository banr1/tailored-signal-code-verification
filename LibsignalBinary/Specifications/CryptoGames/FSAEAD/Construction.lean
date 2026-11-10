/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Defs
public import VCVio.CryptoFoundations.PRG

/-!
# FS-AEAD from AEAD and PRG: the symmetric ratchet (ACD19 Fig. 6, corrected)

**Trusted in part.** The theorems of `Computational/Theorems/` use only the state types
`RatchetSenderState` and `RatchetReceiverState` from this file: read them. `fromAEADPRG`,
`skipKeys` and the theorems here are checked by Lean. See `Computational/docs/TRUSTED_BASE.md`.

Corrected symmetric ratchet of ACD19 Fig. 6 built from an `AEADScheme`, a position-indexed PRG
family `G p` (DEV-FS10), and skip window `maxSkip` (DEV-FS7, DEV-FS8, DEV-FS9).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.FSAEAD

variable {ChainKey MessageKey AssocData Message Ciphertext : Type}

/-- Sender state of the symmetric ratchet (ACD19 Fig. 6 `v_A = (w, iA)`). -/
structure RatchetSenderState (ChainKey : Type) where
  /-- Current chain key (`w`). -/
  chainKey : ChainKey
  /-- Index of the last message sent (`iA`); `0` before the first message. -/
  lastIndex : ℕ

/-- Receiver state of the symmetric ratchet (ACD19 Fig. 6 `v_B = (w, iB, D)`). -/
structure RatchetReceiverState (ChainKey MessageKey : Type) where
  /-- Current chain key (`w`), deriving the message key for `lastIndex + 1`. -/
  chainKey : ChainKey
  /-- Largest index received so far (`iB`); `0` before the first message. -/
  lastIndex : ℕ
  /-- Stored `(index, key)` pairs for skipped indices below `lastIndex` (`D`). -/
  skippedKeys : List (ℕ × MessageKey)

/-- Advance the chain `n` times from position `p`, storing `(p + 1, K)` pairs along the way.

**DEV-FS7 (paper fix): skipped keys are stored under their own index.** ACD19 Fig. 6's `skip`
writes `D[u] ← K` inside its loop, overwriting under the wrong index; here each skipped key is
stored under its own index. -/
def skipKeys (G : ℕ → PRGScheme ChainKey (ChainKey × MessageKey)) :
    ℕ → ChainKey → ℕ → List (ℕ × MessageKey) → ChainKey × List (ℕ × MessageKey)
  | 0, w, _, acc => (w, acc)
  | n + 1, w, p, acc => skipKeys G n ((G p).gen w).1 (p + 1) ((p + 1, ((G p).gen w).2) :: acc)

/-- Symmetric ratchet FS-AEAD scheme (ACD19 Fig. 6, corrected; DEV-FS5) with indexed ciphertexts
`(i, e)`, AEAD `ae`, PRG family `G`, and skip window `maxSkip`.

**DEV-FS8 (paper fix): old indices are rejected.** ACD19 Fig. 6 accepts `i ≤ iB` with `i ∉ D` by
decrypting under the next chain key and rewinding `iB ← i`, allowing forgeries at old uncompromised
indices after `corr-A`; here such indices are rejected.

**DEV-FS9 (libsignal): bounded skipping.** At most `maxSkip` indices are skipped per step (libsignal:
25,000), bounding chain evaluations per query in Thm 5 (DEV-FS12).

**DEV-FS10 (formalization): a PRG per chain position.** `G p` may depend on chain position `p`;
ACD19 Fig. 6 and libsignal use a constant family `fun _ => G`. -/
def fromAEADPRG (ae : AEADScheme MessageKey (ℕ × AssocData) Message Ciphertext)
    (G : ℕ → PRGScheme ChainKey (ChainKey × MessageKey)) (maxSkip : ℕ) :
    FSAEADScheme ChainKey (RatchetSenderState ChainKey)
      (RatchetReceiverState ChainKey MessageKey) AssocData Message (ℕ × Ciphertext) where
  initSender k := ⟨k, 0⟩
  initReceiver k := ⟨k, 0, []⟩
  send v a m :=
    let (w', key) := (G v.lastIndex).gen v.chainKey
    (⟨w', v.lastIndex + 1⟩, (v.lastIndex + 1, ae.enc key (v.lastIndex + 1, a) m))
  receive v a c :=
    let (i, e) := c
    match v.skippedKeys.lookup i with
    | some key =>
      (ae.dec key (i, a) e).map fun m =>
        ({ v with skippedKeys := v.skippedKeys.filter (·.1 != i) }, i, m)
    | none =>
      if i ≤ v.lastIndex ∨ maxSkip < i - v.lastIndex - 1 then none else
      let (w₁, skipped') :=
        skipKeys G (i - v.lastIndex - 1) v.chainKey v.lastIndex v.skippedKeys
      let (w', key) := (G (i - 1)).gen w₁
      (ae.dec key (i, a) e).map fun m => (⟨w', i, skipped'⟩, i, m)
  maxSkip := maxSkip

end CryptoGames.FSAEAD
