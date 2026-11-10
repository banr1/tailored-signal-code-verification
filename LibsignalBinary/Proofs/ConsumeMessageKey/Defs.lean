/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSession
public import LibsignalBinary.Proofs.CodeLayout
import GeneratedLean.LibsignalSessionCode -- shake: keep
public import GeneratedLean.LibsignalSession -- shake: keep
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalSessionProofDefs

/-!
# Shared Callee Specifications for `RatchetState::consume_message_key`

Defines the subroutine contracts `findIndexSpec`, `hmacSpec`, and `growOneSpec` (with corresponding
`FindIndexOk`, `HmacOk`, and `GrowOneOk` predicates), image symbol-offset guards, and allocator
hook forwarding across `sessionExterns`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSession

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

/-! ## `RatchetState::find_receiver_chain_index` (`0xea88`) -/

/-- Ghost input `(chainsPtr, chains, theirAddr, theirKey)` for `find_receiver_chain_index`. -/
abbrev FindIndexGhost := BitVec 64 × List (ChainGhost × ReceiverChain) × BitVec 64 × PublicKey

/-- Contract for `find_receiver_chain_index(chains.ptr = x0, chains.len = x1, their = x2) -> Option<usize>`:
returns `(1, i)` for the first chain whose `sender_ratchet_key` deserializes to `their`, or `(0, _)`
if none matches. -/
def findIndexSpec (img : Obj.Image) (A : RustAlloc) : Spec FindIndexGhost where
  pre := fun (p, cs, theirA, their) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = cs.length ∧ s.readReg64 .x2 = theirA ∧
      cs.length * 104 < 2 ^ 63⌝ ∗
    arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
    (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt s.sp 1024
  post := fun (p, cs, theirA, their) s0 sf =>
    ⌜sf.trace = s0.trace ∧
      match (cs.map (·.2)).findIdx? (fun c => c.senderRatchetKey == their) with
      | some i => sf.readReg64 .x0 = 1#64 ∧ (sf.readReg64 .x1).toNat = i
      | none => sf.readReg64 .x0 = 0#64⌝ ∗
    arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
    (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt s0.sp 1024

/-! ## `crypto::hmac_sha256` (`0x20b88`) -/

/-- Ghost input `(out, keyAddr, key, inputAddr, input)` for `hmac_sha256`. -/
abbrev HmacGhost := BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)

/-- Contract for `hmac_sha256(out = x0, key = (x1, x2), input = (x3, x4))` on 32-byte keys and
1-byte inputs: writes `hmacWith F key input` to `out`. -/
def hmacSpec (F : ShaState → List (BitVec 8) → ShaState) : Spec HmacGhost where
  pre := fun (out, ka, key, ia, inp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = ka ∧ (s.readReg64 .x2).toNat = key.length ∧
      s.readReg64 .x3 = ia ∧ (s.readReg64 .x4).toNat = inp.length ∧ key.length = 32 ∧
      inp.length = 1⌝ ∗
    memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt s.sp 2048
  post := fun (out, ka, key, ia, inp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (out ↦ₛ hmacWith F key inp) ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt s0.sp 2048

/-! ## `RawVec<MessageKey>::grow_one` (`0x15cac`) -/

/-- Ghost input `(vecAddr, cap, ptr, bufBytes)` for `grow_one` (`bufBytes.length = cap * 104`). -/
abbrev GrowGhost := BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)

/-- Contract for `RawVec<MessageKey>::grow_one(&mut self = x0)` (`stride = 104`, `align = 8`):
grows capacity to `max(2 * cap, 4)` via `alloc` (`cap = 0`) or `realloc`, preserving the prefix
bytes and panicking via `handle_error` only on allocator failure. -/
def growOneSpec (A : RustAlloc) : Spec GrowGhost where
  pre := fun (v, cap, ptr, bs) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length = cap.toNat * 104 ∧ ptr ≠ 0 ∧
      max (2 * cap.toNat) 4 * 104 + 8 ≤ 2 ^ 63⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
    A.pool ∗ stackAt s.sp 4608
  post := fun (v, cap, _, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0⌝ ∗ (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 4 * 104) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * cap.toNat) 4 - cap.toNat) * 104) ∗
      A.pool ∗ stackAt s0.sp 4608
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## Callee Contract Predicates -/

def FindIndexOk (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State)) (A : RustAlloc) : Prop :=
  subroutine_ok (sessionProg img F alloc) (img.base + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index")) ((findIndexSpec img A).inImage img)

def HmacOk (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State)) : Prop :=
  subroutine_ok (sessionProg img F alloc) (img.base + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256")) ((hmacSpec F).inImage img)

def GrowOneOk (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State)) (A : RustAlloc) : Prop :=
  subroutine_ok (sessionProg img F alloc) (img.base + bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")) ((growOneSpec A).inImage img)

/-! ## Symbol Address Guards

Pins `cmkEntry` and callee symbol lookups in `libsignalSessionImage` to their concrete offsets. -/

section AddrGuards
open ProofLib.ProgramReflection
set_option maxRecDepth 2000000

theorem cmkEntry_eq {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img) :
    cmkEntry img = img.base + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") := by
  rw [cmkEntry, Program.ofImage_eq_rebase libsignalSessionCode_canonical h,
    Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")]

theorem findIndexAddr_eq {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img) :
    (Program.ofImage img).fnAddr
        "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" =
      img.base + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index") := by
  rw [Program.ofImage_eq_rebase libsignalSessionCode_canonical h,
    Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index")]

theorem hmacAddr_eq {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img) :
    (Program.ofImage img).fnAddr "libsignal_protocol::crypto::hmac_sha256" =
      img.base + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256") := by
  rw [Program.ofImage_eq_rebase libsignalSessionCode_canonical h,
    Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::crypto::hmac_sha256")]

/-- `RawVec<MessageKey>::grow_one` resolves to `0x15cac` (shared with `RawVec<Chain>::grow_one`). -/
theorem growOneAddr_eq {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img) :
    (Program.ofImage img).fnAddr
        "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>::grow_one" =
      img.base + bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one") := by
  rw [Program.ofImage_eq_rebase libsignalSessionCode_canonical h,
    Program.fnAddr_rebase, (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>::grow_one")]

end AddrGuards

/-! ## Extern Hook Forwarding -/

/-- `AllocHooks A alloc` lifts across `Rust.withPanics (sessionExterns F alloc)`. -/
theorem allocHooks_sessionExterns (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (hA : AllocHooks A alloc) :
    AllocHooks A (Rust.withPanics (sessionExterns F alloc)) := by
  obtain ⟨ha, hd, hr⟩ := hA
  refine ⟨?_, ?_, ?_⟩ <;>
    simpa [HookSat, Rust.withPanics, Rust.isPanicSymbol, sessionExterns] using ‹_›

end CryptoVerification.LibsignalSession
