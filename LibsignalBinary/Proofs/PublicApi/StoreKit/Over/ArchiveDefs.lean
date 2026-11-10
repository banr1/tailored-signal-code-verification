/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersX
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.HeapDefs

/-!
# Specifications for `promote_state` and `archive_current_state_inner`

Specifications for `<SessionRecord>::archive_current_state_inner` and `<SessionRecord>::promote_state`
when `recPtr` holds a populated current session (with arbitrary `pending_pre_key` and
`pending_kyber_pre_key`) and an empty `previous_sessions` vector (with arbitrary capacity `prevCap`):
`archive_current_state_inner` clears both pending pre-key fields, encodes the cleared session into
`previous_sessions[0]` (growing capacity `0 → 4` via `grow_one` when `prevCap = 0`), and drops the
stack copy; `promote_state` then copies the 344-byte new session into `recPtr + 0x18`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX (serializeSubStackX)
open Proofs.libsignal.Hooks2 (SerContractsX)

abbrev archiveCurrentStateInnerName : String :=
  "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"

abbrev promoteStateName : String :=
  "<libsignal_protocol::state::session::SessionRecord>::promote_state"

/-! ## Pending-Cleared Ghost and Model Helpers -/

/-- Ghost of a `SessionStructure` after `clear_unacknowledged_pre_key_message()`. -/
def clearPendingGhost (G : SessionGhost) : SessionGhost :=
  { G with pending := none, kyber := none }

abbrev clearedGhost : SessionGhost → SessionGhost := clearPendingGhost

/-- Model `Session` after `clear_unacknowledged_pre_key_message()`. -/
def clearPending (s : Session (List (BitVec 8))) : Session (List (BitVec 8)) :=
  { s with
    state := { s.state with pendingPreKey := false }
    pendingPreKey := none
    pendingKyberPreKey := none }

abbrev clearedSession : Session (List (BitVec 8)) → Session (List (BitVec 8)) := clearPending

@[simp]
theorem clearPendingGhost_pending (G : SessionGhost) : (clearPendingGhost G).pending = none := rfl

@[simp]
theorem clearPendingGhost_kyber (G : SessionGhost) : (clearPendingGhost G).kyber = none := rfl

@[simp]
theorem clearPending_pendingPreKey (s : Session (List (BitVec 8))) :
    (clearPending s).pendingPreKey = none := rfl

@[simp]
theorem clearPending_pendingKyberPreKey (s : Session (List (BitVec 8))) :
    (clearPending s).pendingKyberPreKey = none := rfl

@[simp]
theorem clearPending_state_pendingPreKey (s : Session (List (BitVec 8))) :
    (clearPending s).state.pendingPreKey = false := rfl

theorem clearPendingGhost_of_none {G : SessionGhost} (hp : G.pending = none) (hk : G.kyber = none) :
    clearPendingGhost G = G := by
  cases G; simp only [clearPendingGhost] at hp hk ⊢; subst hp hk; rfl

theorem clearPending_of_none {s : Session (List (BitVec 8))}
    (hst : s.state.pendingPreKey = false)
    (hp : s.pendingPreKey = none) (hk : s.pendingKyberPreKey = none) :
    clearPending s = s := by
  rcases s with ⟨st, pp, pk, lr, rr, abk⟩
  rcases st with ⟨sv, li, ri, rk, pc, sc, rcs, ppk, pqr⟩
  simp only [clearPending] at hst hp pk hk ⊢
  subst hst hp hk
  rfl

/-! ## Stack Budgets -/

/-- Stack of `archive_current_state_inner`: its 464-byte frame over the callee budget
`serializeSubStackX` (`encoded_len`, `encode_raw`, `drop_glue` local#1, `__rust_alloc`,
`__rust_dealloc`, the allocator shim, `memcpy`, `grow_one`). -/
abbrev archiveStackX : Nat :=
  464 + serializeSubStackX

/-- Stack of `promote_state`: its 32-byte frame over `archiveStackX`. -/
abbrev promoteStackX : Nat :=
  32 + archiveStackX

/-! ## General Empty-`previous_sessions` Specifications -/

/-- Ghost of the general archive call: the record `recPtr`, the capacity `prevCap` and pointer
`prevPtr` of the empty `previous_sessions`, and the current session (`G`, `sess`) at
`recPtr + 0x18` (with arbitrary `G.pending` and `G.kyber`). -/
structure ArchiveOverGenGhost where
  recPtr : BitVec 64
  prevCap : BitVec 64
  prevPtr : BitVec 64
  G : SessionGhost
  sess : Session (List (BitVec 8))

/-- `archive_current_state_inner(recPtr)` with a populated current session (arbitrary pending
pre-keys) and an empty `previous_sessions` (arbitrary capacity `prevCap`): afterwards
`previous_sessions` holds `[encSessionMem (clearPendingGhost x.G) (clearPending x.sess)]` at some
nonzero capacity `prevCap'`, `recPtr + 0x18` holds `noneCap`, and `recPtr + 0x20 .. +0x170` is a
336-byte `memRegion`. Panics only on allocation failure (`allocPanic`). -/
def archiveOverGenSpec (A : RustAlloc) : Spec ArchiveOverGenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.recPtr ∧
      (encSessionMem (clearPendingGhost x.G) (clearPending x.sess)).length < 2 ^ 32⌝ ∗
      vecAt A 24 8 (fun (_ : Unit) _ => emp) x.recPtr x.prevCap x.prevPtr [] ∗
      sessionStateReprAt A (x.recPtr + 0x18#64) x.G x.sess ∗ A.pool ∗
      stackAt s.sp archiveStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ prevCap' : BitVec 64, ∃∗ prevPtr' : BitVec 64,
        ⌜prevCap' ≠ 0#64⌝ ∗
        prevVecAt A x.recPtr prevCap' prevPtr'
          [encSessionMem (clearPendingGhost x.G) (clearPending x.sess)]) ∗
      ((x.recPtr + 0x18#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.recPtr + 0x20#64) 336 ∗
      A.pool ∗ stackAt s0.sp archiveStackX
  onPanic := allocPanic

/-- The general archive spec holds at `archive_current_state_inner` on
`tripleRatchetProgAtExt img.base ext`. -/
def ArchiveOverGenOk (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) :
    Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr archiveCurrentStateInnerName)
    ((archiveOverGenSpec A).inImage img)

/-- Ghost of the general `promote_state` call: the record `recPtr`, the new session's 344 bytes
`newBs` at `src`, the capacity `prevCap` and pointer `prevPtr` of the empty `previous_sessions`,
and the current session (`G`, `sess`) at `recPtr + 0x18`. -/
structure PromoteOverGenGhost where
  recPtr : BitVec 64
  src : BitVec 64
  prevCap : BitVec 64
  prevPtr : BitVec 64
  G : SessionGhost
  sess : Session (List (BitVec 8))
  newBs : List (BitVec 8)

/-- `promote_state(recPtr, src)` with a populated current session (arbitrary pending pre-keys) and
an empty `previous_sessions` (arbitrary capacity `prevCap`): afterwards `previous_sessions` holds
`[encSessionMem (clearPendingGhost x.G) (clearPending x.sess)]` at some nonzero capacity
`prevCap'`, `recPtr + 0x18` holds a copy of `newBs`, and `src` is unchanged. Panics only on
allocation failure (`allocPanic`). -/
def promoteOverGenSpec (A : RustAlloc) : Spec PromoteOverGenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.recPtr ∧ s.readReg64 .x1 = x.src ∧ x.newBs.length = 344 ∧
      (encSessionMem (clearPendingGhost x.G) (clearPending x.sess)).length < 2 ^ 32⌝ ∗
      vecAt A 24 8 (fun (_ : Unit) _ => emp) x.recPtr x.prevCap x.prevPtr [] ∗
      sessionStateReprAt A (x.recPtr + 0x18#64) x.G x.sess ∗ A.pool ∗
      (x.src ↦ₛ x.newBs) ∗ stackAt s.sp promoteStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ prevCap' : BitVec 64, ∃∗ prevPtr' : BitVec 64,
        ⌜prevCap' ≠ 0#64⌝ ∗
        prevVecAt A x.recPtr prevCap' prevPtr'
          [encSessionMem (clearPendingGhost x.G) (clearPending x.sess)]) ∗
      ((x.recPtr + 0x18#64) ↦ₛ x.newBs) ∗ (x.src ↦ₛ x.newBs) ∗ A.pool ∗
      stackAt s0.sp promoteStackX
  onPanic := allocPanic

/-- The general promote spec holds at `promote_state` on `tripleRatchetProgAtExt img.base ext`. -/
def PromoteStateOverGenOk (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr promoteStateName)
    ((promoteOverGenSpec A).inImage img)

/-- Direct rewrite from `sessionRecordAt` on `some sess` to the two record atoms of
`archiveOverGenSpec` / `promoteOverGenSpec`. -/
theorem sessionRecordAt_some_eq (A : RustAlloc) (recPtr prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) :
    sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some sess⟩ =
      vecAt A 24 8 (fun (_ : Unit) _ => emp) recPtr prevCap prevPtr [] ∗
      sessionStateReprAt A (recPtr + 0x18#64) G sess :=
  rfl

/-! ## Zero-Capacity Specializations (`prevCap = 0#64`) -/

/-- Ghost of the zero-capacity archive call (`prevCap = 0#64`). -/
structure ArchiveOverGhost where
  recPtr : BitVec 64
  prevPtr : BitVec 64
  G : SessionGhost
  sess : Session (List (BitVec 8))

/-- Specialization of `archive_current_state_inner` when `prevCap = 0#64`, producing capacity `4#64`
(`HdrP x.recPtr 4#64 q 1#64 ∗ Prev1 A q ...`). Supports arbitrary `G.pending` and `G.kyber`. -/
def archiveOverSpecX (A : RustAlloc) : Spec ArchiveOverGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.recPtr ∧ x.prevPtr ≠ 0#64 ∧
      (encSessionMem (clearPendingGhost x.G) (clearPending x.sess)).length < 2 ^ 32⌝ ∗
      HdrP x.recPtr 0#64 x.prevPtr 0#64 ∗ sessionStateReprAt A (x.recPtr + 0x18#64) x.G x.sess ∗ A.pool ∗
      stackAt s.sp archiveStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ q : BitVec 64,
        HdrP x.recPtr 4#64 q 1#64 ∗
          Prev1 A q (encSessionMem (clearPendingGhost x.G) (clearPending x.sess))) ∗
      ((x.recPtr + 0x18#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.recPtr + 0x20#64) 336 ∗
      A.pool ∗ stackAt s0.sp archiveStackX
  onPanic := allocPanic

def ArchiveOverOkX (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) :
    Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr archiveCurrentStateInnerName)
    ((archiveOverSpecX A).inImage img)

/-- Ghost of the zero-capacity `promote_state` call (`prevCap = 0#64`). -/
structure PromoteOverGhost where
  recPtr : BitVec 64
  src : BitVec 64
  prevPtr : BitVec 64
  G : SessionGhost
  sess : Session (List (BitVec 8))
  newBs : List (BitVec 8)

/-- Specialization of `promote_state` when `prevCap = 0#64`, producing capacity `4#64`
(`HdrP x.recPtr 4#64 q 1#64 ∗ Prev1 A q ...`). Supports arbitrary `G.pending` and `G.kyber`. -/
def promoteOverSpecX (A : RustAlloc) : Spec PromoteOverGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.recPtr ∧ s.readReg64 .x1 = x.src ∧ x.newBs.length = 344 ∧
      x.prevPtr ≠ 0#64 ∧
      (encSessionMem (clearPendingGhost x.G) (clearPending x.sess)).length < 2 ^ 32⌝ ∗
      HdrP x.recPtr 0#64 x.prevPtr 0#64 ∗ sessionStateReprAt A (x.recPtr + 0x18#64) x.G x.sess ∗ A.pool ∗
      (x.src ↦ₛ x.newBs) ∗ stackAt s.sp promoteStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ q : BitVec 64,
        HdrP x.recPtr 4#64 q 1#64 ∗
          Prev1 A q (encSessionMem (clearPendingGhost x.G) (clearPending x.sess))) ∗
      ((x.recPtr + 0x18#64) ↦ₛ x.newBs) ∗ (x.src ↦ₛ x.newBs) ∗ A.pool ∗
      stackAt s0.sp promoteStackX
  onPanic := allocPanic

def PromoteStateOverOkX (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) :
    Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr promoteStateName)
    ((promoteOverSpecX A).inImage img)

/-! ## Relocatable `[LibsignalPlacement]` Symbol Definitions -/

section Placed

theorem L1_ArchiveDefs_Placed : True := trivial

/-- Mangled extern symbol of `alloc::raw_vec::RawVec::<alloc::vec::Vec<u8>>::grow_one`. -/
abbrev lsGrowOneVecU8Sym : String :=
  "_RNvMs4_NtCs69KKACWg7bl_5alloc7raw_vecINtB5_6RawVecINtNtB7_3vec3VechEE8grow_oneCsfr5T3GFabw_3std"

end Placed

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
