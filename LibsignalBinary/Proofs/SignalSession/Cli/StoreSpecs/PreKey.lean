/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
public import LibsignalBinary.Specifications.RecordCodecsBinary.SignedPreKey
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# Function-Level Specifications for CLI Pre-Key Store Callbacks

Separation-logic specifications over `DirGhost` (`Cli/Kits.lean`) for `SignedPreKeyFiles`,
`OneTimePreKeyFiles`, and `KyberPreKeyFiles` (`cli/src/stores.rs`):
- `pkShimSpec` (16-byte future box) for `get_signed_pre_key`, `get_pre_key`, `remove_pre_key`, and
  `get_kyber_pre_key`, plus `kpkMarkShimSpec` (32-byte future box) for `mark_kyber_pre_key_used`;
- `spkGetPollSpec`, `pkGetPollSpec`, and `kpkGetPollSpec`: read decimal-ID files via `Dir::get`,
  decode nonempty payloads, and refine `getSignedPreKey`, `getPreKey`, and `KyberGhost.get`;
- `pkRemovePollSpec`: clears nonempty entries via `Dir::put` (`removePreKey_eq_pkRemoveOf`), and
  `dropSpeWordSpec` drops payload-free missing-ID `SignalProtocolError` tags (`13`, `14`).
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary

/-! ## Entry points -/

abbrev spkGetShimName : String :=
  "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key"

abbrev spkGetPollName : String :=
  "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}"

abbrev pkGetShimName : String :=
  "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key"

abbrev pkGetPollName : String :=
  "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"

abbrev pkRemoveShimName : String :=
  "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key"

abbrev pkRemovePollName : String :=
  "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"

abbrev kpkGetShimName : String :=
  "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key"

abbrev kpkGetPollName : String :=
  "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}"

abbrev kpkMarkShimName : String :=
  "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used"

abbrev kpkMarkPollName : String :=
  "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"

theorem spkGetShim_fnOff :
    libsignalSessionCode.fnOff spkGetShimName =
      num% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key")

theorem spkGetPoll_fnOff :
    libsignalSessionCode.fnOff spkGetPollName =
      num% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}")

theorem pkGetShim_fnOff :
    libsignalSessionCode.fnOff pkGetShimName =
      num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key")

theorem pkGetPoll_fnOff :
    libsignalSessionCode.fnOff pkGetPollName =
      num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}")

theorem pkRemoveShim_fnOff :
    libsignalSessionCode.fnOff pkRemoveShimName =
      num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key")

theorem pkRemovePoll_fnOff :
    libsignalSessionCode.fnOff pkRemovePollName =
      num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}")

theorem kpkGetShim_fnOff :
    libsignalSessionCode.fnOff kpkGetShimName =
      num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key")

theorem kpkGetPoll_fnOff :
    libsignalSessionCode.fnOff kpkGetPollName =
      num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}")

theorem kpkMarkShim_fnOff :
    libsignalSessionCode.fnOff kpkMarkShimName =
      num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used")

theorem kpkMarkPoll_fnOff :
    libsignalSessionCode.fnOff kpkMarkPollName =
      num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}")

theorem decodeKyberPreKey_fnOff :
    libsignalSessionCode.fnOff decodeKyberPreKeyName =
      num% (ls_off% "libsignal_cli::stores::decode_kyber_pre_key") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "libsignal_cli::stores::decode_kyber_pre_key")

theorem preKeyDeserialize_fnOff :
    libsignalSessionCode.fnOff preKeyDeserializeName =
      num% (ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize")

/-- Offset of the `get_signed_pre_key` future's vtable: the shim's `adrp`/`add`
(`+0x2c`/`+0x30`). -/
abbrev spkGetFutVtOff : BitVec 64 :=
  bv% (ls_xref% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key" + 0x2c) (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key" + 0x30))

/-- Offset of the `get_pre_key` future's vtable (`+0x2c`/`+0x30`). -/
abbrev pkGetFutVtOff : BitVec 64 :=
  bv% (ls_xref% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key" + 0x2c) (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key" + 0x30))

/-- Offset of the `remove_pre_key` future's vtable (`+0x2c`/`+0x30`). -/
abbrev pkRemoveFutVtOff : BitVec 64 :=
  bv% (ls_xref% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key" + 0x2c) (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key" + 0x30))

/-- Offset of the `get_kyber_pre_key` future's vtable (`+0x2c`/`+0x30`). -/
abbrev kpkGetFutVtOff : BitVec 64 :=
  bv% (ls_xref% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key" + 0x2c) (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key" + 0x30))

/-- Offset of the `mark_kyber_pre_key_used` future's vtable (`+0x38`/`+0x3c`). -/
abbrev kpkMarkFutVtOff : BitVec 64 :=
  bv% (ls_xref% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used" + 0x38) (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used" + 0x3c))

/-! ## The future boxes -/

/-- A pre-key `get` / `remove` future box at `box` (16 bytes): `self` @0, the key id (`u32`) @8,
the state byte @0xc, 3 bytes uninitialized. -/
def pkBoxAt (box self : BitVec 64) (id : BitVec 32) (st : BitVec 8) : SepProp :=
  (box ↦₆₄ self) ∗ ((box + 8#64) ↦₃₂ id) ∗ ((box + 0xc#64) ↦₈ st) ∗ memRegion (box + 0xd#64) 3

/-- The `mark_kyber_pre_key_used` future box at `box` (32 bytes): `self` @0, the base key pointer
@8, the key id @0x10, the signed pre-key id @0x14, the state byte @0x18, 7 bytes
uninitialized. -/
def kpkMarkBoxAt (box self baseKeyA : BitVec 64) (id signedId : BitVec 32) (st : BitVec 8) :
    SepProp :=
  (box ↦₆₄ self) ∗ ((box + 8#64) ↦₆₄ baseKeyA) ∗ ((box + 0x10#64) ↦₃₂ id) ∗
    ((box + 0x14#64) ↦₃₂ signedId) ∗ ((box + 0x18#64) ↦₈ st) ∗ memRegion (box + 0x19#64) 7

/-! ## The shims -/

/-- Arguments of a pre-key `get` / `remove` shim: `self` (`x0`) and the key id (`w1`). -/
structure PkShimCall where
  self : BitVec 64
  id : BitVec 32

/-- A 16-byte pre-key shim (`get_signed_pre_key`, `get_pre_key`, `remove_pre_key`,
`get_kyber_pre_key`), with future vtable offset `vtOff`: a fresh live 16-byte box
`pkBoxAt … 0` (8-aligned, non-null) in `x0`, the vtable `img.base + vtOff` in `x1`; trace
unchanged. Panics only on a failed allocation (`handle_alloc_error`). `stk`: the frame (`0x20`)
plus the hooks'. -/
def pkShimSpec (vtOff : BitVec 64) (A : RustAlloc) (img : Obj.Image) (stk : Nat) :
    Spec PkShimCall :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg32 .x1 = x.id⌝ ∗ A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ⌜sf.readReg64 .x1 = img.base + vtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) 16 8 ∗ pkBoxAt (sf.readReg64 .x0) x.self x.id 0#8 ∗
          A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- Arguments of the `mark_kyber_pre_key_used` shim: `self` (`x0`), the key id (`w1`), the
signed pre-key id (`w2`), the base key pointer (`x3`). -/
structure KpkMarkShimCall where
  self : BitVec 64
  id : BitVec 32
  signedId : BitVec 32
  baseKeyA : BitVec 64

/-- The `mark_kyber_pre_key_used` shim: a fresh live 32-byte box `kpkMarkBoxAt … 0` in `x0`,
the vtable `img.base + kpkMarkFutVtOff` in `x1`; trace unchanged. Panics only on a failed
allocation. `stk`: the frame (`0x30`) plus the hooks'. -/
def kpkMarkShimSpec (A : RustAlloc) (img : Obj.Image) (stk : Nat) : Spec KpkMarkShimCall :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg32 .x1 = x.id ∧ s.readReg32 .x2 = x.signedId ∧
          s.readReg64 .x3 = x.baseKeyA⌝ ∗ A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ⌜sf.readReg64 .x1 = img.base + kpkMarkFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) 32 8 ∗
          kpkMarkBoxAt (sf.readReg64 .x0) x.self x.baseKeyA x.id x.signedId 0#8 ∗
          A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-! ## The `get` answers -/

/-- A `get` poll's answer, as the binary distinguishes it: the record, `Dir::get`'s error,
the decoder's error, or an empty file (the missing-id error). -/
inductive PkAns (α : Type) where
  | found (r : α)
  | readErr
  | decodeErr (e : SignalProtocolError)
  | missing

/-- The answer for `Dir::get`'s answer `gr` and the decoder `dec`: an error stays an error, an
empty file is missing, nonempty bytes are decoded. -/
def pkAnsOf {α : Type} (dec : List (BitVec 8) → Except SignalProtocolError α) :
    Except Unit (List (BitVec 8)) → PkAns α
  | .error _ => .readErr
  | .ok [] => .missing
  | .ok (b :: bs) =>
    match dec (b :: bs) with
    | .ok r => .found r
    | .error e => .decodeErr e

/-- `get_kyber_pre_key`'s answer from its two directories' answers: the second is used only when
the first file is empty. -/
def kpkAnsOf {α : Type} : PkAns α → PkAns α → PkAns α
  | .missing, a2 => a2
  | a1, _ => a1

/-- The pure model's view of an answer: every non-record answer is an error. -/
def PkAns.toExcept {α : Type} : PkAns α → Except Unit α
  | .found r => .ok r
  | _ => .error ()

/-- `record`'s view of an answer (`Kits.lean`): an empty file is no record. -/
def PkAns.toRecord {α : Type} : PkAns α → Except Unit (Option α)
  | .found r => .ok (some r)
  | .missing => .ok none
  | _ => .error ()

/-- `pkAnsOf` refines `get(…).bind (record dec)`. -/
theorem pkAnsOf_toRecord {α : Type} (dec : List (BitVec 8) → Except SignalProtocolError α)
    (gr : Except Unit (List (BitVec 8))) :
    gr.bind (record dec) = (pkAnsOf dec gr).toRecord := by
  rcases gr with _ | _ | ⟨b, bs⟩
  · rfl
  · rfl
  · show record dec (b :: bs) = (pkAnsOf dec (.ok (b :: bs))).toRecord
    rcases h : dec (b :: bs) with e | r <;> simp [record, pkAnsOf, PkAns.toRecord, h]

/-- `get_pre_key`'s pure model is the answer's `toExcept`. -/
theorem getPreKey_eq (rd : ReadRule) (F0 : FsFiles) (d : DirGhost) (id : BitVec 32) :
    getPreKey rd F0 d id = (pkAnsOf PreKeyRecord.deserialize (d.get rd F0 (keyName id))).toExcept := by
  unfold getPreKey
  rw [pkAnsOf_toRecord]
  cases pkAnsOf PreKeyRecord.deserialize (d.get rd F0 (keyName id)) <;> rfl

/-- `get_signed_pre_key`'s pure model is the answer's `toExcept`. -/
theorem getSignedPreKey_eq (rd : ReadRule) (F0 : FsFiles) (d : DirGhost) (id : BitVec 32) :
    getSignedPreKey rd F0 d id =
      (pkAnsOf SignedPreKeyRecord.deserialize (d.get rd F0 (keyName id))).toExcept := by
  unfold getSignedPreKey
  rw [pkAnsOf_toRecord]
  cases pkAnsOf SignedPreKeyRecord.deserialize (d.get rd F0 (keyName id)) <;> rfl

/-- `get_kyber_pre_key`'s pure model is the combined answer's `toExcept`. -/
theorem KyberGhost.get_eq (rd : ReadRule) (F0 : FsFiles) (g : KyberGhost) (id : BitVec 32) :
    g.get rd F0 id =
      (kpkAnsOf (pkAnsOf KyberPreKeyRecord.deserialize (g.oneTime.get rd F0 (keyName id)))
        (pkAnsOf KyberPreKeyRecord.deserialize (g.lastResort.get rd F0 (keyName id)))).toExcept := by
  unfold KyberGhost.get
  generalize g.oneTime.get rd F0 (keyName id) = g1
  generalize g.lastResort.get rd F0 (keyName id) = g2
  show (g1.bind (record KyberPreKeyRecord.deserialize)).bind _ = _
  rw [pkAnsOf_toRecord]
  cases pkAnsOf KyberPreKeyRecord.deserialize g1 with
  | missing =>
    show (g2.bind (record KyberPreKeyRecord.deserialize)).bind _ = _
    rw [pkAnsOf_toRecord]
    cases pkAnsOf KyberPreKeyRecord.deserialize g2 <;> rfl
  | _ => rfl

/-! ## The `get` srets -/

/-- A `get` poll's sret (`size` bytes) for the answer `ans`, with the record layout `resAt`
and the missing-id SPE index `w`:
* `found r`: the decoder's `Ok` result moved in (`resAt out (.ok r)`);
* `decodeErr e`: the decoder's `Err` result moved in (`resAt out (.error e)`);
* `readErr`: `Dir::get`'s `InvalidState("read", _)` behind `errTag` (`errResultAt`);
* `missing`: `errTag`, `speWord w`, the rest uninitialized. -/
def pkAnsAt {α : Type} (A : RustAlloc)
    (resAt : RustAlloc → BitVec 64 → Except SignalProtocolError α → SepProp)
    (size w : Nat) (out : BitVec 64) : PkAns α → SepProp
  | .found r => resAt A out (.ok r)
  | .decodeErr e => resAt A out (.error e)
  | .readErr => errResultAt A (utf8 "read") size out .invalidState
  | .missing =>
    (out ↦₆₄ errTag) ∗ ((out + 8#64) ↦₆₄ speWord w) ∗ memRegion (out + 0x10#64) (size - 16)

/-- `get_signed_pre_key`'s sret (88 bytes; `InvalidSignedPreKeyId` = SPE index 14). -/
abbrev spkAnsAt (A : RustAlloc) (out : BitVec 64) : PkAns SignedPreKeyRecord → SepProp :=
  pkAnsAt A signedPreKeyResultAt 88 14 out

/-- `get_pre_key`'s sret (56 bytes; `InvalidPreKeyId` = SPE index 13). -/
abbrev pkGetAnsAt (A : RustAlloc) (out : BitVec 64) : PkAns PreKeyRecord → SepProp :=
  pkAnsAt A preKeyResultAt 56 13 out

/-- `get_kyber_pre_key`'s sret (88 bytes; `InvalidKyberPreKeyId` = SPE index 15). -/
abbrev kpkAnsAt (A : RustAlloc) (out : BitVec 64) : PkAns KyberPreKeyRecord → SepProp :=
  pkAnsAt A kyberPreKeyResultAt 88 15 out

/-! ## `remove_pre_key`'s answer -/

/-- `remove_pre_key`'s step on `Dir::get`'s answer `gr`: an error is returned before any change,
an empty file is left alone, a nonempty one is emptied. -/
def pkRemoveOf (d : DirGhost) (n : List (BitVec 8)) :
    Except Unit (List (BitVec 8)) → Except Unit Unit × DirGhost
  | .error _ => (.error (), d)
  | .ok [] => (.ok (), d)
  | .ok (_ :: _) => (.ok (), d.put n [])

/-- `remove_pre_key`'s pure model is `pkRemoveOf` on `Dir::get`'s answer. -/
theorem removePreKey_eq_pkRemoveOf (rd : ReadRule) (F0 : FsFiles) (d : DirGhost)
    (id : BitVec 32) :
    removePreKey rd F0 d id = pkRemoveOf d (keyName id) (d.get rd F0 (keyName id)) := by
  unfold removePreKey
  rcases d.get rd F0 (keyName id) with _ | _ | ⟨b, bs⟩ <;> rfl

/-- `remove_pre_key`'s sret (48 bytes): `Ok(())` = word 0 `-2`, the rest uninitialized;
`Err` = `Dir::get`'s `InvalidState("read", _)` moved in. -/
def pkRemoveOutAt (A : RustAlloc) (out : BitVec 64) : Except Unit Unit → SepProp
  | .ok () => (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (out + 8#64) 40
  | .error () => speAt A (utf8 "read") out .invalidState

/-! ## The polls -/

/-- Ghost of a pre-key `get` / `remove` poll call: the future box, the sret, the store pointer
(`self`, its `Dir` at `self`), the key id, and the `Dir`. -/
structure PkPollGhost where
  fut : BitVec 64
  out : BitVec 64
  self : BitVec 64
  id : BitVec 32
  dir : DirGhost

/-- What `Dir::get` needs of the key's file name: the name (`decimal(id)`) and the `Dir`
path below `2^32`, and `pathOk` of `<path>/<id>` (`read_file`'s domain). The name bound holds
(at most 10 digits); it is stated here so that the hops need not prove it. -/
def PkNameOk (pathOk : List (BitVec 8) → Prop) (d : DirGhost) (id : BitVec 32) : Prop :=
  (keyName id).length < 2 ^ 32 ∧ d.path.length < 2 ^ 32 ∧ pathOk (pathOf d.path (keyName id))

/-- What the decoders need of the key's file: every answer `Ok bs` that `Dir::get` would give
on the files `F` has fewer than `2^32` bytes (`preKeyDeserializeSpec` /
`decodeKyberPreKeySpec`). -/
def PkSizeOk (rd : ReadRule) (F : FsFiles) (d : DirGhost) (id : BitVec 32) : Prop :=
  ∀ bs, d.get rd F (keyName id) = .ok bs → bs.length < 2 ^ 32

/-- A pre-key `get` poll (from state 0), generic in the record: decoder `dec`, sret layout
`resAt` of `size` bytes, missing-id SPE index `w`. Pre: the box, the `Dir` at `self`, the sret,
`PkNameOk`, `PkSizeOk`. Post: `ans` is `pkAnsOf dec` of `Dir::get`'s answer (trace unchanged),
the sret holds `pkAnsAt … ans`, the state byte is 1, the `Dir` is unchanged. An allocation failure
panics (`onPanic`: `decimal`, `Dir::get`, the decoder). -/
def pkGetPollSpecOf {α : Type} (dec : List (BitVec 8) → Except SignalProtocolError α)
    (resAt : RustAlloc → BitVec 64 → Except SignalProtocolError α → SepProp) (size w : Nat)
    (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc) (img : Obj.Image)
    (stk : Nat) : Spec PkPollGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧ PkNameOk pathOk x.dir x.id ∧
          PkSizeOk rd s.fs.files x.dir x.id⌝ ∗
          pkBoxAt x.fut x.self x.id 0#8 ∗ dirAt A x.self x.dir ∗ memRegion x.out size ∗
          A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        (∃∗ ans : PkAns α,
          ⌜ans = pkAnsOf dec (x.dir.get rd s0.fs.files (keyName x.id)) ∧ sf.trace = s0.trace⌝ ∗
          pkAnsAt A resAt size w x.out ans) ∗
          pkBoxAt x.fut x.self x.id 1#8 ∗ dirAt A x.self x.dir ∗ A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- The poll of the `get_signed_pre_key` future (`decode_kyber_pre_key`'s code as
`SignedPreKeyRecord::deserialize`, 88-byte sret, `InvalidSignedPreKeyId`). `stk`: the frame
(`0x180`) plus the deepest callee's. -/
abbrev spkGetPollSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (img : Obj.Image) (stk : Nat) : Spec PkPollGhost :=
  pkGetPollSpecOf SignedPreKeyRecord.deserialize signedPreKeyResultAt 88 14 rd pathOk A img stk

/-- The poll of the `get_pre_key` future (`PreKeyRecord::deserialize`, 56-byte sret,
`InvalidPreKeyId`). `stk`: the frame (`0x100`) plus the deepest callee's. -/
abbrev pkGetPollSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (img : Obj.Image) (stk : Nat) : Spec PkPollGhost :=
  pkGetPollSpecOf PreKeyRecord.deserialize preKeyResultAt 56 13 rd pathOk A img stk

/-- The poll of the `remove_pre_key` future (from state 0). Pre: the box, the `Dir`, the
48-byte sret, `PkNameOk`, fewer than `2^32` changed entries (`Dir::put`). Post: the answer and the
`Dir` are `pkRemoveOf dir (keyName id)` of `Dir::get`'s answer (`removePreKey`,
`removePreKey_eq_pkRemoveOf`), trace unchanged; the state byte is 1. An allocation failure panics
(`onPanic`: `decimal`, `Dir::get`, `Dir::put`). `stk`: the frame (`0xc0`) plus the deepest
callee's. -/
def pkRemovePollSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (img : Obj.Image) (stk : Nat) : Spec PkPollGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧ PkNameOk pathOk x.dir x.id ∧
          x.dir.changed.length < 2 ^ 32⌝ ∗
          pkBoxAt x.fut x.self x.id 0#8 ∗ dirAt A x.self x.dir ∗ memRegion x.out 48 ∗
          A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        (∃∗ res : Except Unit Unit × DirGhost,
          ⌜res = pkRemoveOf x.dir (keyName x.id) (x.dir.get rd s0.fs.files (keyName x.id)) ∧
              sf.trace = s0.trace⌝ ∗
          pkRemoveOutAt A x.out res.1 ∗ dirAt A x.self res.2) ∗
          pkBoxAt x.fut x.self x.id 1#8 ∗ A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- Ghost of a `get_kyber_pre_key` poll call: as `PkPollGhost`, with both `Dir`s (`one_time` at
`self`, `last_resort` at `self + 0x28`). -/
structure KpkPollGhost where
  fut : BitVec 64
  out : BitVec 64
  self : BitVec 64
  id : BitVec 32
  kg : KyberGhost

/-- The poll of the `get_kyber_pre_key` future (from state 0). Pre: the box, both `Dir`s, the
88-byte sret, `PkNameOk` and `PkSizeOk` of both. Post: the answer is `kpkAnsOf a1 a2` of the two
directories' `pkAnsOf` answers (`KyberGhost.get_eq`), trace unchanged; the state byte is 1; both
`Dir`s unchanged. An allocation failure panics (`onPanic`: `decimal`, `Dir::get`,
`decode_kyber_pre_key`). `stk`: the frame (`0x1b0`) plus the deepest callee's. -/
def kpkGetPollSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (img : Obj.Image) (stk : Nat) : Spec KpkPollGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
          PkNameOk pathOk x.kg.oneTime x.id ∧ PkNameOk pathOk x.kg.lastResort x.id ∧
          PkSizeOk rd s.fs.files x.kg.oneTime x.id ∧ PkSizeOk rd s.fs.files x.kg.lastResort x.id⌝ ∗
          pkBoxAt x.fut x.self x.id 0#8 ∗ dirAt A x.self x.kg.oneTime ∗
          dirAt A (x.self + 0x28#64) x.kg.lastResort ∗ memRegion x.out 88 ∗
          A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        (∃∗ ans : PkAns KyberPreKeyRecord,
          ⌜ans = kpkAnsOf
                (pkAnsOf KyberPreKeyRecord.deserialize
                  (x.kg.oneTime.get rd s0.fs.files (keyName x.id)))
                (pkAnsOf KyberPreKeyRecord.deserialize
                  (x.kg.lastResort.get rd s0.fs.files (keyName x.id))) ∧
              sf.trace = s0.trace⌝ ∗
          kpkAnsAt A x.out ans) ∗
          pkBoxAt x.fut x.self x.id 1#8 ∗ dirAt A x.self x.kg.oneTime ∗
          dirAt A (x.self + 0x28#64) x.kg.lastResort ∗ A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-! ## Dropping a payload-free missing-id error -/

/-- Ghost of a drop of a payload-free SPE: its address and SPE index. -/
structure DropSpeWordGhost where
  a : BitVec 64
  w : Nat

/-- `drop_glue::<SignalProtocolError> [local#4]` on `InvalidPreKeyId` / `InvalidSignedPreKeyId`
(SPE indices 13 / 14; no payload, no constructor in the trusted SPE model, so `dropSpeSpecX` does
not cover them): word 0 `speWord w`, 40 bytes of anything; afterwards 48 bytes of plain memory,
trace unchanged. The `get` polls drop the eagerly built missing-id error on the `Ok` path. -/
def dropSpeWordSpec (A : RustAlloc) (img : Obj.Image) : Spec DropSpeWordGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.a ∧ (x.w = 13 ∨ x.w = 14)⌝ ∗
          (x.a ↦₆₄ speWord x.w) ∗ memRegion (x.a + 8#64) 40 ∗ A.pool ∗
          stackAt s.sp Getters.dropSpeStackX
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 48 ∗ A.pool ∗ stackAt s0.sp Getters.dropSpeStackX }
    img

end CryptoVerification.SignalSession.Cli
