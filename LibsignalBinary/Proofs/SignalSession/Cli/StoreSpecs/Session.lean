/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKit
public import LibsignalBinary.Proofs.E2E.Record.L1GX.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# Function-Level Specifications for CLI `SessionFiles` Callbacks

Separation-logic specifications over `DirGhost` (`Cli/Kits.lean`) for the `SessionFiles`
(`cli/src/stores.rs`, `Dir` at offset `0`) `dyn SessionStore` callbacks:
- `sessLoadShimSpec` (24-byte box) and `sessStoreShimSpec` (32-byte box): `async_trait` shims;
- `sessDeserializeSpec` and `sessDeserializeExtSpec`: allocator-parametric `SessionRecord::deserialize`
  contracts over a record scope `Scope`;
- `sessLoadPollSpec` (`0x350` frame, 368-byte sret): reads `sessions/<peer>` under `SessFileWf Scope`
  and decodes nonempty records via `SessionRecord::deserialize`;
- `sessStorePollSpec` (`0xd0` frame, 48-byte sret): serializes canonical records via
  `SessionRecord::serialize` and buffers `(addressText, encodeRecord r)` via `Dir::put`.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoGames.LibsignalSessionApi

/-! ## Entry points -/

abbrev sessLoadShimName : String :=
  "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session"

abbrev sessLoadPollName : String :=
  "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"

abbrev sessStoreShimName : String :=
  "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session"

abbrev sessStorePollName : String :=
  "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"

abbrev recordDeserializeName : String :=
  "<libsignal_protocol::state::session::SessionRecord>::deserialize"

abbrev recordSerializeName : String :=
  "<libsignal_protocol::state::session::SessionRecord>::serialize"

theorem sessLoadShim_fnOff :
    libsignalSessionCode.fnOff sessLoadShimName =
      num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session")

theorem sessLoadPoll_fnOff :
    libsignalSessionCode.fnOff sessLoadPollName =
      num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}")

theorem sessStoreShim_fnOff :
    libsignalSessionCode.fnOff sessStoreShimName =
      num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session")

theorem sessStorePoll_fnOff :
    libsignalSessionCode.fnOff sessStorePollName =
      num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}")

theorem recordDeserialize_fnOff :
    libsignalSessionCode.fnOff recordDeserializeName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize")

theorem recordSerialize_fnOff :
    libsignalSessionCode.fnOff recordSerializeName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::serialize")

/-- Offset of the `load_session` future's vtable: the `adrp`/`add` pair of the shim
(`+0x28`/`+0x2c`). -/
abbrev sessLoadFutVtOff : BitVec 64 :=
  bv% (ls_xref% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session" + 0x28) (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session" + 0x2c))

/-- Offset of the `store_session` future's vtable: the shim's `adrp`/`add` (`+0x34`/`+0x38`). -/
abbrev sessStoreFutVtOff : BitVec 64 :=
  bv% (ls_xref% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session" + 0x34) (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session" + 0x38))

/-! ## The future boxes -/

/-- The `load_session` future box at `box` (24 bytes): `self` @0, the address @8, the state
byte @0x10, 7 bytes uninitialized. The shape of `hookSessionStoreSpec`'s `loadBoxAt`. -/
def sessLoadBoxAt (box self addrA : BitVec 64) (st : BitVec 8) : SepProp :=
  (box ↦₆₄ self) ∗ ((box + 8#64) ↦₆₄ addrA) ∗ ((box + 0x10#64) ↦₈ st) ∗
    memRegion (box + 0x11#64) 7

/-- The `store_session` future box at `box` (32 bytes): `self` @0, the address @8, the record
@0x10, the state byte @0x18, 7 bytes uninitialized. The shape of `hookSessionStoreSpec`'s
`storeBoxAt`. -/
def sessStoreBoxAt (box self addrA recA : BitVec 64) (st : BitVec 8) : SepProp :=
  (box ↦₆₄ self) ∗ ((box + 8#64) ↦₆₄ addrA) ∗ ((box + 0x10#64) ↦₆₄ recA) ∗
    ((box + 0x18#64) ↦₈ st) ∗ memRegion (box + 0x19#64) 7

/-- `sessLoadBoxAt` agrees with `(hookSessionStoreSpec A b).loadBoxAt`. -/
theorem sessLoadBoxAt_eq_hook (A : RustAlloc) (b : BitVec 64) :
    sessLoadBoxAt = (hookSessionStoreSpec A b).loadBoxAt := rfl

/-- `sessStoreBoxAt` agrees with `(hookSessionStoreSpec A b).storeBoxAt`. -/
theorem sessStoreBoxAt_eq_hook (A : RustAlloc) (b : BitVec 64) :
    sessStoreBoxAt = (hookSessionStoreSpec A b).storeBoxAt := rfl

/-! ## The shims -/

def sessLoadShimSpec (A : RustAlloc) (img : Obj.Image) (stk : Nat) : Spec LoadShimCall :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA⌝ ∗ A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ⌜sf.readReg64 .x1 = img.base + sessLoadFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) 24 8 ∗ sessLoadBoxAt (sf.readReg64 .x0) x.self x.addrA 0#8 ∗
          A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- The `store_session` shim: a fresh live 32-byte box `sessStoreBoxAt … 0` in `x0`, the
vtable `img.base + sessStoreFutVtOff` in `x1`; trace unchanged. Panics only on a failed
allocation. `stk`: the frame (`0x30`) plus the hooks'. -/
def sessStoreShimSpec (A : RustAlloc) (img : Obj.Image) (stk : Nat) : Spec StoreShimCall :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.recA⌝ ∗
          A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ⌜sf.readReg64 .x1 = img.base + sessStoreFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) 32 8 ∗
          sessStoreBoxAt (sf.readReg64 .x0) x.self x.addrA x.recA 0#8 ∗
          A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-! ## `SessionRecord::deserialize`, generic in the scope and the allocator -/

/-- `SessionRecord::deserialize` on `encodeRecord r` for `r` in `Scope`, parameterized by the
output record allocator `A` (`deserializeGenSpecAt img` at `Scope = DeserializeScope`, `A = A0`). -/
noncomputable def sessDeserializeSpec (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (A : RustAlloc) (img : Obj.Image) :
    Spec E2E.Record.DeserializeGeneral.DeserializeGenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.p ∧
      s.readReg64 .x1 = BitVec.ofNat 64 (E2E.Record.encodeRecord x.r).length ∧
      s.readReg64 .x8 = x.out ∧ Scope x.r ∧ img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      (x.p ↦ₛ E2E.Record.encodeRecord x.r) ∗ memRegion x.out 368 ∗
      stackAt s.sp E2E.Record.recDeserializeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.p ↦ₛ E2E.Record.encodeRecord x.r) ∗
      (∃∗ g : E2E.Record.RecordGhost, ⌜E2E.Record.Serialization.CanonRecord g x.r⌝ ∗
        E2E.Record.sessionRecordAt A x.out g x.r) ∗
      stackAt s0.sp E2E.Record.recDeserializeStack
  onPanic := E2E.Record.Serialization.allocPanic

/-- At `DeserializeScope` and `A0`, `sessDeserializeSpec` equals `deserializeGenSpecAt img`. -/
theorem sessDeserializeSpec_A0 (img : Obj.Image) :
    sessDeserializeSpec E2E.Record.DeserializeGeneral.DeserializeScope E2E.Record.A0 img =
      E2E.Record.DeserializeGeneral.deserializeGenSpecAt img := rfl

/-- At `DeserializeScopeP`, `A0` and `sessionImg0` it is the PQXDH-scope contract. -/
theorem sessDeserializeSpec_X :
    sessDeserializeSpec E2E.RecordX.DeserializeScopeP E2E.Record.A0 E2E.Record.sessionImg0 =
      E2E.Record.L1GX.deserializeXSpec := rfl

/-- `SessionRecord::deserialize` on `encodeRecord r` threading `A.pool` in both `pre` and `post`
for an arbitrary allocator `A : RustAlloc`. -/
noncomputable def sessDeserializeExtSpec (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (A : RustAlloc) (img : Obj.Image) :
    Spec E2E.Record.DeserializeGeneral.DeserializeGenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.p ∧
      s.readReg64 .x1 = BitVec.ofNat 64 (E2E.Record.encodeRecord x.r).length ∧
      s.readReg64 .x8 = x.out ∧ Scope x.r ∧ img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      (x.p ↦ₛ E2E.Record.encodeRecord x.r) ∗ memRegion x.out 368 ∗ A.pool ∗
      stackAt s.sp E2E.Record.recDeserializeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.p ↦ₛ E2E.Record.encodeRecord x.r) ∗
      (∃∗ g : E2E.Record.RecordGhost, ⌜E2E.Record.Serialization.CanonRecord g x.r⌝ ∗
        E2E.Record.sessionRecordAt A x.out g x.r) ∗ A.pool ∗
      stackAt s0.sp E2E.Record.recDeserializeStack
  onPanic := E2E.Record.Serialization.allocPanic

noncomputable abbrev sessDeserializePoolSpec := sessDeserializeExtSpec

/-- Whenever `A.pool = emp` (in particular for `E2E.Record.A0` / `E2E.HooksE.A0`),
`sessDeserializeExtSpec` is equal to `sessDeserializeSpec`. -/
theorem sessDeserializeExtSpec_eq_of_pool_emp {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {A : RustAlloc} (img : Obj.Image) (hpool : A.pool = SepProp.emp) :
    sessDeserializeExtSpec Scope A img = sessDeserializeSpec Scope A img := by
  simp only [sessDeserializeExtSpec, sessDeserializeSpec, hpool, emp_sepConj]

/-- Equivalence at `E2E.Record.A0` (`= E2E.HooksE.A0` definitionally, where `A0.pool = emp`). -/
theorem sessDeserializeExtSpec_A0 (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (img : Obj.Image) :
    sessDeserializeExtSpec Scope E2E.Record.A0 img =
      sessDeserializeSpec Scope E2E.Record.A0 img :=
  sessDeserializeExtSpec_eq_of_pool_emp img rfl

theorem subroutine_ok_sessDeserializeExtSpec_A0_iff {prog : Program} {entry : BitVec 64}
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (img : Obj.Image) :
    subroutine_ok prog entry (sessDeserializeExtSpec Scope E2E.Record.A0 img) ↔
      subroutine_ok prog entry (sessDeserializeSpec Scope E2E.Record.A0 img) := by
  rw [sessDeserializeExtSpec_A0]

/-- Contravariant scope weakening on `sessDeserializeExtSpec`. -/
theorem subroutine_ok_sessDeserializeExtSpec_of_sub {prog : Program} {entry : BitVec 64}
    {Scope Scope' : SessionRecord (List (BitVec 8)) → Prop} {A : RustAlloc} {img : Obj.Image}
    (h : subroutine_ok prog entry (sessDeserializeExtSpec Scope A img))
    (hsub : ∀ r, Scope' r → Scope r) :
    subroutine_ok prog entry (sessDeserializeExtSpec Scope' A img) := by
  refine subroutine_ok_map_panic h fun x R s0 hpre => ?_
  refine ⟨x, R, ?_, fun _ hp => hp, fun _ hp => hp⟩
  dsimp only [sessDeserializeExtSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  obtain ⟨⟨hx0, hx1, hx8, hsc, hF, hsym⟩, hmem⟩ := hpre
  exact ⟨⟨hx0, hx1, hx8, hsub x.r hsc, hF, hsym⟩, hmem⟩

/-! ## The file invariant and the load answer -/

/-- A session file the CLI can load: empty (no session), or the encoding of a record in the
scope `Scope`. -/
def SessFileWf (Scope : SessionRecord (List (BitVec 8)) → Prop) (bs : List (BitVec 8)) : Prop :=
  bs = [] ∨ ∃ r, E2E.Record.encodeRecord r = bs ∧ Scope r

/-- The answer of the load poll for the answer `gr` of `Dir::get`: an error stays an error,
an empty file is no session, and nonempty bytes are the record they encode (in `Scope`). -/
def SessLoadAns (Scope : SessionRecord (List (BitVec 8)) → Prop) :
    Except Unit (List (BitVec 8)) → Except Unit (Option (SessionRecord (List (BitVec 8)))) → Prop
  | .error _, ans => ans = .error ()
  | .ok [], ans => ans = .ok none
  | .ok (b :: bs), ans =>
    ∃ r, ans = .ok (some r) ∧ E2E.Record.encodeRecord r = b :: bs ∧ Scope r

/-- `SessLoadAns` is `Kits.loadSession`'s step `get(…).bind (record dec)` for any decoder `dec`
that inverts `encodeRecord` on `Scope` (the answer relation of the CLI kit). -/
theorem sessLoadAns_bind {ε : Type} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {dec : List (BitVec 8) → Except ε (SessionRecord (List (BitVec 8)))}
    (hdec : ∀ r, Scope r → dec (E2E.Record.encodeRecord r) = .ok r)
    {gr : Except Unit (List (BitVec 8))} {ans : Except Unit (Option (SessionRecord (List (BitVec 8))))}
    (h : SessLoadAns Scope gr ans) : ans = gr.bind (record dec) := by
  match gr, h with
  | .error (), h => exact h
  | .ok [], h => exact h
  | .ok (b :: bs), ⟨r, hans, henc, hsc⟩ =>
    subst hans
    have hd : dec (b :: bs) = .ok r := henc ▸ hdec r hsc
    show Except.ok (some r) = record dec (b :: bs)
    simp only [record, hd]

/-- The load poll's sret (368 bytes) for the answer `ans`:
* `Ok(Some r)`: the record moved in (`sessionRecordAt`; the caller tells it apart by word 0, the
  record's `previous_sessions` capacity, below `2^63`);
* `Ok(None)`: word 0 `-1`, the rest uninitialized;
* `Err`: word 0 `-2`, `Dir::get`'s `InvalidState("read", _)` at `out + 8`, the rest uninitialized. -/
def sessLoadOutAt (A : RustAlloc) (out : BitVec 64) :
    Except Unit (Option (SessionRecord (List (BitVec 8)))) → SepProp
  | .ok (some r) => ∃∗ g : RecordGhost, sessionRecordAt A out g r
  | .ok none => (out ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (out + 8#64) 360
  | .error () =>
    (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ speAt A (utf8 "read") (out + 8#64) .invalidState ∗
      memRegion (out + 0x38#64) 312

/-! ## The polls -/

/-- Ghost of a `load_session` poll call: the kit's call (future box, sret, address), the
`SessionFiles` pointer (`self`, the `Dir` at offset 0) and its `Dir`. -/
structure SessLoadPollGhost where
  call : LoadPollCall
  self : BitVec 64
  dir : DirGhost

def sessLoadPollSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc) (img : Obj.Image)
    (stk : Nat) : Spec SessLoadPollGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.call.fut ∧ s.readReg64 .x8 = x.call.out ∧
          x.call.addr.name.bytes.length < 2 ^ 32 ∧
          (addressText x.call.addr.val).length < 2 ^ 32 ∧ x.dir.path.length < 2 ^ 32 ∧
          pathOk (pathOf x.dir.path (addressText x.call.addr.val)) ∧
          ∀ bs, x.dir.get rd s.fs.files (addressText x.call.addr.val) = .ok bs →
            SessFileWf Scope bs⌝ ∗
          sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗ dirAt A x.self x.dir ∗
          memRegion x.call.out 368 ∗ protocolAddressAt A x.call.addr x.call.addrA ∗
          A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        (∃∗ gr : Except Unit (List (BitVec 8)),
          ∃∗ ans : Except Unit (Option (SessionRecord (List (BitVec 8)))),
          ⌜(gr = x.dir.get rd s0.fs.files (addressText x.call.addr.val) ∧ sf.trace = s0.trace) ∧
            SessLoadAns Scope gr ans⌝ ∗
          sessLoadOutAt A x.call.out ans) ∗
          sessLoadBoxAt x.call.fut x.self x.call.addrA 1#8 ∗ dirAt A x.self x.dir ∗
          protocolAddressAt A x.call.addr x.call.addrA ∗ A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- Ghost of a `store_session` poll call: the kit's call (future box, sret, address, record), the
`SessionFiles` pointer and its `Dir`. -/
structure SessStorePollGhost where
  call : StorePollCall
  self : BitVec 64
  dir : DirGhost

/-- The poll of the `store_session` future (from state 0): `serialize` gives
`encodeRecord record` (`serializeCanonSpec`; the record's `sessionRecordAt` makes its ghost
canonical), then `Dir::put(address_text, bytes)`; the answer is always `Ok(())` (word 0 `-2`),
the next 40 bytes uninitialized; the state byte is 1; the record and the address are unchanged;
trace unchanged. Pre: the encoding below `2^32` bytes (the kit's `RecOk`), fewer than `2^32`
changed entries, the name below `2^32`. Panics only on a failed allocation. `stk`: the frame
(`0xd0`) plus the deepest callee's. -/
def sessStorePollSpec (A : RustAlloc) (img : Obj.Image) (stk : Nat) : Spec SessStorePollGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.call.fut ∧ s.readReg64 .x8 = x.call.out ∧
          x.call.call.addr.name.bytes.length < 2 ^ 32 ∧
          (E2E.Record.encodeRecord x.call.call.record).length < 2 ^ 32 ∧
          x.dir.changed.length < 2 ^ 32⌝ ∗
          sessStoreBoxAt x.call.fut x.self x.call.call.addrA x.call.call.recA 0#8 ∗
          dirAt A x.self x.dir ∗ memRegion x.call.out 48 ∗
          protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
          sessionRecordAt A x.call.call.recA x.call.call.g x.call.call.record ∗
          A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          sessStoreBoxAt x.call.fut x.self x.call.call.addrA x.call.call.recA 1#8 ∗
          dirAt A x.self (x.dir.put (addressText x.call.call.addr.val)
            (E2E.Record.encodeRecord x.call.call.record)) ∗
          (x.call.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (x.call.out + 8#64) 40 ∗
          protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
          sessionRecordAt A x.call.call.recA x.call.call.g x.call.call.record ∗
          A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- `store_session`'s update in the pure model (`Kits.storeSession`) with the encoder
`.ok ∘ encodeRecord`: the answer `Ok`, the `Dir` of `sessStorePollSpec`'s post. -/
theorem storeSession_encodeRecord (d : DirGhost) (a : AddrVal)
    (r : SessionRecord (List (BitVec 8))) :
    storeSession (ε := Unit) (fun r => .ok (E2E.Record.encodeRecord r)) d a r =
      (.ok (), d.put (addressText a) (E2E.Record.encodeRecord r)) := rfl

end CryptoVerification.SignalSession.Cli
