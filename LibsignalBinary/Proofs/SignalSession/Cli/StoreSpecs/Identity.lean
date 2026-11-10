/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKit
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.RecordCodecs.RoundTrip

/-!
# Function-Level Specifications for CLI `IdentityFiles` Callbacks

Separation-logic specifications over `DirGhost` (`Cli/Kits.lean`) for the `IdentityFiles`
(`cli/src/stores.rs`, `peers` at `+0x28`) `dyn IdentityKeyStore` callbacks on the SM path:
- `idSaveShimSpec` and `idTrustShimSpec`: 32-byte `async_trait` future-boxing shims;
- `idTrustPollSpec` (`0xc0` frame, 48-byte sret): reads `identities/<name>` under `IdFileWf`,
  trusting on first use (empty file) or comparing `IdentityKey::decode` against `key`;
- `idSavePollSpec` (`0xd0` frame, 48-byte sret): reads any existing pinned key under `IdFileWf`,
  stores `key.serialize()` via `Dir::put`, and reports whether an existing key was replaced.

Allocation failures trap via `onPanic` (`allocFailedIn s0 sf ∧ s0.trace <+: sf.trace`).
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoGames.LibsignalSessionApi CryptoVerification.RecordCodecs

/-! ## Entry points -/

abbrev idSaveShimName : String :=
  "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity"

abbrev idSavePollName : String :=
  "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"

abbrev idTrustShimName : String :=
  "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity"

abbrev idTrustPollName : String :=
  "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}"

theorem idSaveShim_fnOff :
    libsignalSessionCode.fnOff idSaveShimName =
      num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity")

theorem idSavePoll_fnOff :
    libsignalSessionCode.fnOff idSavePollName =
      num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")

theorem idTrustShim_fnOff :
    libsignalSessionCode.fnOff idTrustShimName =
      num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity")

theorem idTrustPoll_fnOff :
    libsignalSessionCode.fnOff idTrustPollName =
      num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}")

/-- Offset of the `save_identity` future's vtable: the shim's `adrp`/`add` (`+0x34`/`+0x38`). -/
abbrev idSaveFutVtOff : BitVec 64 :=
  bv% (ls_xref% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity" + 0x34) (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity" + 0x38))

/-- Offset of the `is_trusted_identity` future's vtable: the shim's `adrp`/`add`
(`+0x38`/`+0x3c`). -/
abbrev idTrustFutVtOff : BitVec 64 :=
  bv% (ls_xref% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity" + 0x38) (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity" + 0x3c))

/-! ## The future boxes -/

/-- The `save_identity` future box at `box` (32 bytes): `self` @0, the address @8, the key
@0x10, the state byte @0x18, 7 bytes uninitialized. The shape of `hookIdentityStoreSpecAt`'s
`saveBoxAt`. -/
def idSaveBoxAt (box self addrA keyA : BitVec 64) (st : BitVec 8) : SepProp :=
  (box ↦₆₄ self) ∗ ((box + 8#64) ↦₆₄ addrA) ∗ ((box + 0x10#64) ↦₆₄ keyA) ∗
    ((box + 0x18#64) ↦₈ st) ∗ memRegion (box + 0x19#64) 7

/-- The `is_trusted_identity` future box at `box` (32 bytes): as `idSaveBoxAt`, plus the
direction byte @0x19, 6 bytes uninitialized. The shape of `hookIdentityStoreSpecAt`'s
`trustBoxAt`. -/
def idTrustBoxAt (box self addrA keyA : BitVec 64) (st d : BitVec 8) : SepProp :=
  (box ↦₆₄ self) ∗ ((box + 8#64) ↦₆₄ addrA) ∗ ((box + 0x10#64) ↦₆₄ keyA) ∗
    ((box + 0x18#64) ↦₈ st) ∗ ((box + 0x19#64) ↦₈ d) ∗ memRegion (box + 0x1a#64) 6

/-- The CLI's save box is `hookIdentityStoreSpecAt`'s (at any vtable address). -/
theorem idSaveBoxAt_eq_hook (A : RustAlloc) (b id_vt : BitVec 64) :
    idSaveBoxAt = (hookIdentityStoreSpecAt A b id_vt).saveBoxAt := rfl

/-- The CLI's trust box is `hookIdentityStoreSpecAt`'s (at any vtable address). -/
theorem idTrustBoxAt_eq_hook (A : RustAlloc) (b id_vt : BitVec 64) :
    idTrustBoxAt = (hookIdentityStoreSpecAt A b id_vt).trustBoxAt := rfl

/-! ## The shims -/

/-- The `save_identity` shim: a fresh live 32-byte box `idSaveBoxAt … 0` (8-aligned,
non-null) in `x0`, the future's vtable `img.base + idSaveFutVtOff` in `x1`; trace unchanged.
Panics only on a failed allocation (`handle_alloc_error`). `stk`: the frame (`0x30`) plus the
hooks'. -/
def idSaveShimSpec (A : RustAlloc) (img : Obj.Image) (stk : Nat) : Spec IdentityShimCall :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.keyA⌝ ∗
          A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ⌜sf.readReg64 .x1 = img.base + idSaveFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) 32 8 ∗
          idSaveBoxAt (sf.readReg64 .x0) x.self x.addrA x.keyA 0#8 ∗
          A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- The `is_trusted_identity` shim: a fresh live 32-byte box `idTrustBoxAt … 0 d` with the
direction byte `d` (the low byte of `x3`), the vtable `img.base + idTrustFutVtOff` in `x1`; trace
unchanged. Panics only on a failed allocation. `stk`: the frame (`0x30`) plus the hooks'. -/
def idTrustShimSpec (A : RustAlloc) (img : Obj.Image) (stk : Nat) :
    Spec (IdentityShimCall × BitVec 8) :=
  Spec.inImage
    { pre := fun (x, d) s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.keyA ∧
          (s.readReg64 .x3).setWidth 8 = d⌝ ∗ A.pool ∗ stackAt s.sp stk
      post := fun (x, d) s0 sf =>
        ⌜sf.readReg64 .x1 = img.base + idTrustFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) 32 8 ∗
          idTrustBoxAt (sf.readReg64 .x0) x.self x.addrA x.keyA 0#8 d ∗
          A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-! ## The file invariant and the answers -/

/-- An identity file the CLI can read: empty (no pinned key), or `k.serialize` (33 bytes:
type byte `0x05` and the key) for some identity key `k`. -/
def IdFileWf (bs : List (BitVec 8)) : Prop :=
  bs = [] ∨ ∃ k : IdentityKey, k.serialize = bs

/-- The pinned key as the polls see it, for the answer `gr` of `Dir::get`: an error stays an
error, an empty file is no key, and nonempty bytes are the key they serialize. -/
def IdPeerAns : Except Unit (List (BitVec 8)) → Except Unit (Option IdentityKey) → Prop
  | .error _, p => p = .error ()
  | .ok [], p => p = .ok none
  | .ok (b :: bs), p => ∃ k : IdentityKey, p = .ok (some k) ∧ k.serialize = b :: bs

/-- `IdPeerAns` is `IdGhost.peer`'s step `get(…).bind (record decodeIdentityKey)`. -/
theorem idPeerAns_bind {gr : Except Unit (List (BitVec 8))} {p : Except Unit (Option IdentityKey)}
    (h : IdPeerAns gr p) : p = gr.bind (record decodeIdentityKey) := by
  match gr, h with
  | .error (), h => exact h
  | .ok [], h => exact h
  | .ok (b :: bs), ⟨k, hp, hser⟩ =>
    subst hp
    have hd : decodeIdentityKey (b :: bs) = .ok k := hser ▸ decodeIdentityKey_serialize k
    show Except.ok (some k) = record decodeIdentityKey (b :: bs)
    simp only [record, hd]

/-- `is_trusted_identity`'s answer from the pinned key: trusted on first use, then pinned. -/
def idTrustOf : Except Unit (Option IdentityKey) → IdentityKey → Except Unit Bool
  | .error _, _ => .error ()
  | .ok none, _ => .ok true
  | .ok (some known), k => .ok (decide (known = k))

/-- `save_identity`'s answer from the pinned key: `ReplacedExisting` iff a different key was
pinned. -/
def idSaveOf : Except Unit (Option IdentityKey) → IdentityKey → Except Unit IdentityChange
  | .error _, _ => .error ()
  | .ok none, _ => .ok .newOrUnchanged
  | .ok (some known), k => .ok (if known = k then .newOrUnchanged else .replacedExisting)

/-- `save_identity`'s `peers` after the poll: `put(name, key.serialize())` once the pinned key
was read; unchanged on an error (the `?` returns first). -/
def idSavePeers (d : DirGhost) (name : List (BitVec 8)) (k : IdentityKey) :
    Except Unit (Option IdentityKey) → DirGhost
  | .ok _ => d.put name k.serialize
  | .error _ => d

theorem IdGhost.trusted_eq_idTrustOf (rd : ReadRule) (F0 : FsFiles) (g : IdGhost) (a : AddrVal)
    (k : IdentityKey) : g.trusted rd F0 a k = idTrustOf (g.peer rd F0 a) k := by
  unfold IdGhost.trusted
  rcases g.peer rd F0 a with e | (_ | known) <;> rfl

theorem IdGhost.saveAns_eq_idSaveOf (rd : ReadRule) (F0 : FsFiles) (g : IdGhost) (a : AddrVal)
    (k : IdentityKey) : g.saveAns rd F0 a k = idSaveOf (g.peer rd F0 a) k := by
  unfold IdGhost.saveAns
  rcases g.peer rd F0 a with e | (_ | known) <;> rfl

theorem IdGhost.saveUpd_eq_idSavePeers (rd : ReadRule) (F0 : FsFiles) (g : IdGhost) (a : AddrVal)
    (k : IdentityKey) :
    g.saveUpd rd F0 a k = { g with peers := idSavePeers g.peers a.name k (g.peer rd F0 a) } := by
  unfold IdGhost.saveUpd
  rcases g.peer rd F0 a with e | p <;> rfl

/-- The trust poll's answer is the pure model's (`IdGhost.trusted`) on the non-OOM path. -/
theorem IdGhost.trusted_of_peerAns {rd : ReadRule} {F0 : FsFiles} {g : IdGhost} {a : AddrVal}
    {k : IdentityKey} {p : Except Unit (Option IdentityKey)}
    (h : IdPeerAns (g.peers.get rd F0 a.name) p) : g.trusted rd F0 a k = idTrustOf p k := by
  rw [IdGhost.trusted_eq_idTrustOf, idPeerAns_bind h]; rfl

/-- The save poll's answer and update are the pure model's on the non-OOM path. -/
theorem IdGhost.saveAns_of_peerAns {rd : ReadRule} {F0 : FsFiles} {g : IdGhost} {a : AddrVal}
    {k : IdentityKey} {p : Except Unit (Option IdentityKey)}
    (h : IdPeerAns (g.peers.get rd F0 a.name) p) :
    g.saveAns rd F0 a k = idSaveOf p k ∧
      g.saveUpd rd F0 a k = { g with peers := idSavePeers g.peers a.name k p } := by
  rw [IdGhost.saveAns_eq_idSaveOf, IdGhost.saveUpd_eq_idSavePeers, idPeerAns_bind h]
  exact ⟨rfl, rfl⟩

/-- `save_identity`'s `put` keeps the file invariant. -/
theorem idFileWf_put {rd : ReadRule} {F : FsFiles} {d : DirGhost} {n : List (BitVec 8)}
    (k : IdentityKey) (h : ∀ m bs, d.get rd F m = .ok bs → IdFileWf bs) :
    ∀ m bs, (d.put n k.serialize).get rd F m = .ok bs → IdFileWf bs := by
  intro m bs hm
  by_cases hmn : m = n
  · subst hmn
    rw [DirGhost.get_put_self] at hm
    exact .inr ⟨k, Except.ok.inj hm⟩
  · rw [DirGhost.get_put_ne rd F d hmn] at hm
    exact h m bs hm

/-! ## The polls' srets -/

/-- The trust poll's sret (48 bytes) for the answer `ans`: `Ok(t)` = word 0 `-2`, byte 8 `t`,
the rest uninitialized (= `trustPollOutAt`'s `Ok` arm, `idTrustOutAt_ok`); `Err` = `Dir::get`'s
`InvalidState("read", _)` moved in. -/
def idTrustOutAt (A : RustAlloc) (out : BitVec 64) : Except Unit Bool → SepProp
  | .ok t =>
    (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 8#64) ↦₈ (if t then 1#8 else 0#8)) ∗
      memRegion (out + 9#64) 39
  | .error () => speAt A (utf8 "read") out .invalidState

/-- The save poll's sret (48 bytes) for the answer `ans`: `Ok(c)` = word 0 `-2`, `u32` at 8
`replaced`, the rest uninitialized (= `savePollOutAt`'s `Ok` arm, `idSaveOutAt_ok`); `Err` =
`Dir::get`'s `InvalidState("read", _)` moved in. -/
def idSaveOutAt (A : RustAlloc) (out : BitVec 64) : Except Unit IdentityChange → SepProp
  | .ok c =>
    (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
      ((out + 8#64) ↦₃₂ (if c == .replacedExisting then 1#32 else 0#32)) ∗
      memRegion (out + 0xc#64) 36
  | .error () => speAt A (utf8 "read") out .invalidState

theorem idTrustOutAt_ok (A : RustAlloc) (b out : BitVec 64) (t : Bool) :
    idTrustOutAt A out (.ok t) = trustPollOutAt b out (.ok t) := rfl

theorem idSaveOutAt_ok (A : RustAlloc) (b out : BitVec 64) (c : IdentityChange) :
    idSaveOutAt A out (.ok c) = savePollOutAt b out (.ok c) := rfl

/-! ## The polls -/

/-- Ghost of a `save_identity` / `is_trusted_identity` poll call: the kit's call (future box,
sret, address, key), the `IdentityFiles` pointer (`self`; `peers` at `self + 0x28`) and the
`peers` `Dir`. -/
structure IdPollGhost where
  call : IdentityPollCall
  self : BitVec 64
  peers : DirGhost

/-- The poll of the `is_trusted_identity` future (from state 0, any direction byte `d`).
Pre: the box, the `peers` `Dir`, the 48-byte sret, the address, the key (`keyA ↦ₛ` its 32
bytes), `logOff` (`IdentityKey::decode`); the name and the `Dir` path below `2^32`; `pathOk` of
`identities/<name>`; and the file invariant: every answer `Ok bs` that `Dir::get` would give
is `IdFileWf bs`. Post: `gr` is `Dir::get`'s answer (`dirGetSpec`, trace unchanged), `p` the pinned
key (`IdPeerAns`), the sret holds `idTrustOutAt (idTrustOf p key)`, the state byte is 1; everything
else unchanged. An allocation failure panics (`onPanic`, in `Dir::get`). `stk`: the frame (`0xc0`)
plus the deepest callee's. -/
def idTrustPollSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (img : Obj.Image) (stk : Nat) : Spec (IdPollGhost × BitVec 8) :=
  Spec.inImage
    { pre := fun (x, d) s =>
        ⌜s.readReg64 .x0 = x.call.fut ∧ s.readReg64 .x8 = x.call.out ∧
          x.call.call.addr.name.bytes.length < 2 ^ 32 ∧ x.peers.path.length < 2 ^ 32 ∧
          pathOk (pathOf x.peers.path x.call.call.addr.val.name) ∧
          ∀ bs, x.peers.get rd s.fs.files x.call.call.addr.val.name = .ok bs → IdFileWf bs⌝ ∗
          idTrustBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 d ∗
          dirAt A (x.self + 0x28#64) x.peers ∗ memRegion x.call.out 48 ∗
          protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
          (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗ logOff img ∗
          A.pool ∗ stackAt s.sp stk
      post := fun (x, d) s0 sf =>
        (∃∗ gr : Except Unit (List (BitVec 8)),
          ∃∗ p : Except Unit (Option IdentityKey),
          ⌜(gr = x.peers.get rd s0.fs.files x.call.call.addr.val.name ∧ sf.trace = s0.trace) ∧
            IdPeerAns gr p⌝ ∗
          idTrustOutAt A x.call.out (idTrustOf p x.call.call.key)) ∗
          idTrustBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 1#8 d ∗
          dirAt A (x.self + 0x28#64) x.peers ∗
          protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
          (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗ logOff img ∗
          A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- The poll of the `save_identity` future (from state 0). Pre: as `idTrustPollSpec`, plus
fewer than `2^32` changed entries in `peers` (`Dir::put`). Post: `gr`, `p` as there; the sret
holds `idSaveOutAt (idSaveOf p key)`; `peers` becomes `idSavePeers peers name key p` (`put(name,
key.serialize())` unless `p` is an error); the state byte is 1; everything else unchanged. An
allocation failure panics (`onPanic`: `Dir::get`, `PublicKey::serialize`, `Dir::put`). `stk`: the
frame (`0xd0`) plus the deepest callee's. -/
def idSavePollSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (img : Obj.Image) (stk : Nat) : Spec IdPollGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.call.fut ∧ s.readReg64 .x8 = x.call.out ∧
          x.call.call.addr.name.bytes.length < 2 ^ 32 ∧ x.peers.path.length < 2 ^ 32 ∧
          x.peers.changed.length < 2 ^ 32 ∧
          pathOk (pathOf x.peers.path x.call.call.addr.val.name) ∧
          ∀ bs, x.peers.get rd s.fs.files x.call.call.addr.val.name = .ok bs → IdFileWf bs⌝ ∗
          idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 ∗
          dirAt A (x.self + 0x28#64) x.peers ∗ memRegion x.call.out 48 ∗
          protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
          (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗ logOff img ∗
          A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        (∃∗ gr : Except Unit (List (BitVec 8)),
          ∃∗ p : Except Unit (Option IdentityKey),
          ⌜(gr = x.peers.get rd s0.fs.files x.call.call.addr.val.name ∧ sf.trace = s0.trace) ∧
            IdPeerAns gr p⌝ ∗
          idSaveOutAt A x.call.out (idSaveOf p x.call.call.key) ∗
          dirAt A (x.self + 0x28#64)
            (idSavePeers x.peers x.call.call.addr.val.name x.call.call.key p)) ∗
          idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 1#8 ∗
          protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
          (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗ logOff img ∗
          A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

end CryptoVerification.SignalSession.Cli
