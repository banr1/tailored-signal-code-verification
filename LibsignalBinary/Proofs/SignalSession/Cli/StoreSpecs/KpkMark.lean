/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.PreKey

/-!
# Function-Level Specification for `KyberPreKeyFiles::mark_kyber_pre_key_used` Poll

Separation-logic specification `kpkMarkPollSpec` (`0xf0` frame, 48-byte sret) for
`<KyberPreKeyFiles as KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}` over `KyberGhost`:
- if `one_time` (`self`) holds a nonempty entry for `id`, clears it via `Dir::put`;
- otherwise reads `<id>.base-keys` in `last_resort` (`self + 0x28`), rejecting non-multiples of the
  37-byte record (`malformed`) or duplicate `le32 signedId ‖ baseKey.serialize` entries (`reused`),
  and appends the new entry via `Dir::put` on fresh keys.

Refines `KyberGhost.mark` (`kyberMark_eq`) and leaves both directories unchanged on every error
(`kpkMarkOf_store_of_ne_ok`). Allocation failures trap via `onPanic`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary

/-! ## The answer -/

/-- `mark_kyber_pre_key_used`'s answer, as the binary distinguishes it: `Ok(())`, `Dir::get`'s
error (either directory), the malformed `.base-keys` file, or the reused base key. -/
inductive KpkMarkAns where
  | ok
  | readErr
  | malformed
  | reused

/-- The pure model's view of an answer: every non-`ok` answer is an error. -/
def KpkMarkAns.toExcept : KpkMarkAns → Except Unit Unit
  | .ok => .ok ()
  | _ => .error ()

/-- `mark_kyber_pre_key_used`'s answer and new store, step by step as the binary (and
`KyberGhost.mark`): a read error in `one_time` returns at once; a nonempty one-time key is emptied;
otherwise the last-resort key's `<id>.base-keys` file is read (a read error returns at once), a
length that is not a multiple of the 37-byte entry is `malformed`, an entry equal to
`le32 signedId ‖ baseKey.serialize` is `reused`, and else the entry is appended. -/
def kpkMarkOf (rd : ReadRule) (F0 : FsFiles) (g : KyberGhost) (id signedId : BitVec 32)
    (baseKey : PublicKey) : KpkMarkAns × KyberGhost :=
  match g.oneTime.get rd F0 (keyName id) with
  | .error _ => (.readErr, g)
  | .ok (_ :: _) => (.ok, { g with oneTime := g.oneTime.put (keyName id) [] })
  | .ok [] =>
    match g.lastResort.get rd F0 (baseKeysName id) with
    | .error _ => (.readErr, g)
    | .ok seen =>
      let used := baseKeyEntry signedId baseKey
      if seen.length % used.length ≠ 0 then (.malformed, g)
      else if hasChunk seen used then (.reused, g)
      else (.ok, { g with lastResort := g.lastResort.put (baseKeysName id) (seen ++ used) })

/-- `kpkMarkOf` refines `KyberGhost.mark`: same store, and the answer's `toExcept`. -/
theorem kyberMark_eq (rd : ReadRule) (F0 : FsFiles) (g : KyberGhost) (id signedId : BitVec 32)
    (baseKey : PublicKey) :
    g.mark rd F0 id signedId baseKey =
      ((kpkMarkOf rd F0 g id signedId baseKey).1.toExcept,
        (kpkMarkOf rd F0 g id signedId baseKey).2) := by
  unfold KyberGhost.mark kpkMarkOf
  rcases g.oneTime.get rd F0 (keyName id) with _ | _ | ⟨b, bs⟩
  · rfl
  · rcases g.lastResort.get rd F0 (baseKeysName id) with _ | seen
    · rfl
    · dsimp only
      split
      · rfl
      · split <;> rfl
  · rfl

/-- Every error returns the store unchanged (refusal, malformed file and read errors come
before any `put`). -/
theorem kpkMarkOf_store_of_ne_ok (rd : ReadRule) (F0 : FsFiles) (g : KyberGhost)
    (id signedId : BitVec 32) (baseKey : PublicKey) :
    (kpkMarkOf rd F0 g id signedId baseKey).1 = .ok ∨
      (kpkMarkOf rd F0 g id signedId baseKey).2 = g := by
  unfold kpkMarkOf
  rcases g.oneTime.get rd F0 (keyName id) with _ | _ | ⟨b, bs⟩
  · exact Or.inr rfl
  · rcases g.lastResort.get rd F0 (baseKeysName id) with _ | seen
    · exact Or.inr rfl
    · dsimp only
      split
      · exact Or.inr rfl
      · split
        · exact Or.inr rfl
        · exact Or.inl rfl
  · exact Or.inl rfl

/-! ## The sret -/

/-- A 48-byte `SignalProtocolError` at `a` with tag `i` owning a `String` at `+8`: word 0
`speWord i`, an owned `vecU8` at `+8`, and 16 unspecified bytes at `+0x20`. -/
def strSpeAt (A : RustAlloc) (a : BitVec 64) (i : Nat) : SepProp :=
  (a ↦₆₄ speWord i) ∗ (∃∗ bs : List (BitVec 8), vecU8 A (a + 8#64) bs) ∗
    memRegion (a + 0x20#64) 16

/-- `mark_kyber_pre_key_used`'s sret (48 bytes) for the answer:
* `ok`: word 0 `-2` (`Ok(())`), the rest uninitialized;
* `readErr`: `Dir::get`'s `InvalidState("read", _)` moved in (= `RunDrop.SpeOwned.proto`);
* `malformed`: `InvalidState("base-keys", "malformed file")`, as `strSpeAt A out 1`
  (`RunDrop.SpeOwned.withString 1`);
* `reused`: `InvalidMessage(PreKey, "reused base key")`, as `strSpeAt A out 24`
  (`RunDrop.SpeOwned.withString 24`). -/
def kpkMarkOutAt (A : RustAlloc) (out : BitVec 64) : KpkMarkAns → SepProp
  | .ok => (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (out + 8#64) 40
  | .readErr => speAt A (utf8 "read") out .invalidState
  | .malformed => strSpeAt A out 1
  | .reused => strSpeAt A out 24

/-! ## The poll -/

/-- Ghost of a `mark_kyber_pre_key_used` poll call: the future box, the sret, the store pointer
(`one_time` at `self`, `last_resort` at `self + 0x28`), the borrowed base key's address and value,
the key ids, and the two `Dir`s. -/
structure KpkMarkPollGhost where
  fut : BitVec 64
  out : BitVec 64
  self : BitVec 64
  baseKeyA : BitVec 64
  id : BitVec 32
  signedId : BitVec 32
  baseKey : PublicKey
  kg : KyberGhost

/-- What the second `Dir::get` needs of the `.base-keys` file name: the name
(`decimal(id) ++ ".base-keys"`) and the `Dir` path below `2^32`, and `pathOk` of
`<path>/<id>.base-keys`. It is `PkNameOk` for `baseKeysName`. -/
def KpkBaseKeysOk (pathOk : List (BitVec 8) → Prop) (d : DirGhost) (id : BitVec 32) : Prop :=
  (baseKeysName id).length < 2 ^ 32 ∧ d.path.length < 2 ^ 32 ∧
    pathOk (pathOf d.path (baseKeysName id))

/-- What the append needs of the `.base-keys` file: an answer `Ok bs` that `Dir::get` would
give on the files `F` and that reaches the append (a whole number of entries, without the entry
`le32 signedId ‖ baseKey.serialize`) has fewer than `2^32` bytes, so `seen ++ used` and its
reserve stay far below `2^63`. Files that are malformed or already hold the entry need no bound:
the binary only divides and compares them. The condition survives the append itself (the new file
holds the entry), so a store invariant can carry it. -/
def KpkSeenOk (rd : ReadRule) (F : FsFiles) (d : DirGhost) (id signedId : BitVec 32)
    (baseKey : PublicKey) : Prop :=
  ∀ bs, d.get rd F (baseKeysName id) = .ok bs →
    bs.length % (baseKeyEntry signedId baseKey).length = 0 →
    hasChunk bs (baseKeyEntry signedId baseKey) = false → bs.length < 2 ^ 32

/-- The poll of the `mark_kyber_pre_key_used` future (from state 0).

Pre: the box, both `Dir`s, the borrowed base key (32 bytes at `baseKeyA`, as `kitKpkMarkPollSpec`
and `publicKeySerializeSpec`), the 48-byte sret; `PkNameOk` of `one_time` for `keyName id` (both
`decimal` names), `KpkBaseKeysOk` of `last_resort`, `KpkSeenOk`, and fewer than `2^32` changed
entries in each `Dir` (`Dir::put`).

Post: the answer and the new store are `kpkMarkOf` on the entry files, and the trace is unchanged
(`KyberGhost.mark` by `kyberMark_eq`). The sret holds `kpkMarkOutAt` of the answer, both `Dir`s
are at the new store, the state byte is 1, the base key is given back.

An allocation failure panics (`onPanic`: `decimal`, `do_reserve_and_handle`, `Dir::get`,
`PublicKey::serialize`, `concat`, the error `String`s, the append's reserve, `Dir::put`). `stk`:
the frame (`0xf0`) plus the deepest callee's. -/
def kpkMarkPollSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (img : Obj.Image) (stk : Nat) : Spec KpkMarkPollGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
          PkNameOk pathOk x.kg.oneTime x.id ∧ KpkBaseKeysOk pathOk x.kg.lastResort x.id ∧
          KpkSeenOk rd s.fs.files x.kg.lastResort x.id x.signedId x.baseKey ∧
          x.kg.oneTime.changed.length < 2 ^ 32 ∧ x.kg.lastResort.changed.length < 2 ^ 32⌝ ∗
          kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 0#8 ∗
          dirAt A x.self x.kg.oneTime ∗ dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
          (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗ memRegion x.out 48 ∗
          A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        (∃∗ res : KpkMarkAns × KyberGhost,
          ⌜res = kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey ∧
              sf.trace = s0.trace⌝ ∗
          kpkMarkOutAt A x.out res.1 ∗
          dirAt A x.self res.2.oneTime ∗ dirAt A (x.self + 0x28#64) res.2.lastResort) ∗
          kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
          (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗ A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

end CryptoVerification.SignalSession.Cli
