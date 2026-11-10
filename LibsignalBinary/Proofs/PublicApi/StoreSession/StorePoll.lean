/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalPublicApi
public import LibsignalBinary.Proofs.CodeLayout
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.PublicApi.StoreSession.Decodes -- shake: keep

/-!
# `HookSessionStore::store_session` Future Poll (`0x42b38`)

Verifies `<HookSessionStore as SessionStore>::store_session::{closure#0}` (31 instructions): reads
the address and record pointers from the future box (`x0`), invokes
`libsignal_session_store_session` (`storeSessionSpec`), writes the 48-byte
`Poll<Result<(), SignalProtocolError>>` to `x8`, and sets the future state byte to `1`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.StoreSession

open Arm64 ProofLib CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- The poll of the `store_session` future (`0x42b38`). -/
abbrev storeSessionPollName : String :=
  "<libsignal_session_stores::HookSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"

/-! ## The poll spec -/

/-- Stack of the poll: its 32-byte frame (`0x42b38: stp x29, x30, [sp, #-0x20]!`) and the hook's. -/
abbrev storeSessionPollStack : Nat := storeHookStack + 32

/-- Ghost of a poll call: the future box (`x0`), the sret (`x8`, 48 bytes) and the hook call. -/
structure StorePollCall where
  fut : BitVec 64
  out : BitVec 64
  call : StoreSessionCall

/-- Word 0 of the `Poll<Result<(), SPE>>` the poll writes: `-2` = `Ready(Ok(()))`, else SPE
variant 26 (`ApplicationCallbackError`, `speWord 26`, the niche-encoded `Ready(Err(_))`). -/
def pollTag : Except Unit Unit → BitVec 64
  | .ok () => 0xFFFFFFFFFFFFFFFE#64
  | .error () => 0x800000000000001A#64

/-- The poll of the `store_session` future (`0x42b38`) on `tripleRatchetProgAt b`. Pre: the future box's
address / record pointers (`+8`, `+0x10`) and state byte 0 (`+0x18`; an odd state byte panics,
`panic_const_async_fn_resumed`), the 48-byte sret, the hook's arguments. Post: for some answer
`ans` of the hook, the trace grew by `storeSessionEvent`, the state byte is 1, and the sret holds
`pollTag ans` and the `ApplicationCallbackError("store hook", Box<HookStoreError>)` payload words
(written on both paths: `&str` at rodata `b + 0x4dab0`, length 10, ZST box data 1, vtable
`b + 0x4da58`), the last word untouched. -/
def storeSessionPollSpec (A : RustAlloc)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (b : BitVec 64) :
    Spec StorePollCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out⌝ ∗
      ((x.fut + 8#64) ↦₆₄ x.call.addrA) ∗ ((x.fut + 0x10#64) ↦₆₄ x.call.recA) ∗
      ((x.fut + 0x18#64) ↦₈ 0#8) ∗ memRegion x.out 48 ∗
      protocolAddressAt A x.call.addr x.call.addrA ∗
      sessionRecordAt A x.call.recA x.call.g x.call.record ∗ A.pool ∗
      stackAt s.sp storeSessionPollStack
  post := fun x s0 sf =>
    ∃∗ ans : Except Unit Unit,
      ⌜sf.trace = s0.trace ++
        [storeSessionEvent encRecord x.call.addr.val x.call.record ans]⌝ ∗
      ((x.fut + 8#64) ↦₆₄ x.call.addrA) ∗ ((x.fut + 0x10#64) ↦₆₄ x.call.recA) ∗
      ((x.fut + 0x18#64) ↦₈ 1#8) ∗
      (x.out ↦₆₄ pollTag ans) ∗ ((x.out + 8#64) ↦₆₄ (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")))) ∗
      ((x.out + 0x10#64) ↦₆₄ 10#64) ∗ ((x.out + 0x18#64) ↦₆₄ 1#64) ∗
      ((x.out + 0x20#64) ↦₆₄ (b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16))) ∗ memRegion (x.out + 0x28#64) 8 ∗
      protocolAddressAt A x.call.addr x.call.addrA ∗
      sessionRecordAt A x.call.recA x.call.g x.call.record ∗ A.pool ∗
      stackAt s0.sp storeSessionPollStack

end CryptoVerification.LibsignalPublicApi.StoreSession
