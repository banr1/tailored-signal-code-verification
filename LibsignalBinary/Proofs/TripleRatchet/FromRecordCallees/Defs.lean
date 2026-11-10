/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.Defs

/-!
# Specifications for Small Callees of `try_decrypt_from_record`

Defines symbol names, stack budgets, ghost states, and `Spec` / `subroutine_ok` contracts for five
callees of `try_decrypt_from_record`:
1. `core::ptr::drop_glue::<SessionStructure> [local#2]` (`0x35958`)
2. `core::ptr::drop_glue::<SessionStructure> [local#1]` (`0x25b4`)
3. `<SessionRecord>::set_session_state` (`0x174d4`)
4. `<RawVec<SignalProtocolError>>::grow_one` (`0x15c44`)
5. `try_decrypt_from_record::<HookRng>::{closure#0}` (`0x381ac`, log-off path)
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalSession

/-! ## Symbol names -/

/-- `core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#2]`
(image offset `0x35958`, 69 instructions). -/
abbrev dropSessionStructureLocal2Name : String :=
  "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#2]"

/-- `core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]`
(image offset `0x25b4`, 68 instructions). -/
abbrev dropSessionStructureLocal1Name : String :=
  "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]"

/-- `<libsignal_protocol::state::session::SessionRecord>::set_session_state`
(image offset `0x174d4`, 15 instructions). -/
abbrev setSessionStateName : String :=
  "<libsignal_protocol::state::session::SessionRecord>::set_session_state"

/-- `<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one`
(image offset `0x15c44`, 26 instructions). -/
abbrev growOneSpeName : String :=
  "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one"

/-- `libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_session::HookRng>::{closure#0}`
(image offset `0x381ac`, 109 instructions total, 18 on the log-off path). -/
abbrev logClosureName : String :=
  "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_session::HookRng>::{closure#0}"

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
/-- Guard (kernel-checked): each of the five symbol names appears in the image's symbol table
exactly once (`fnAddr` takes the first match). -/
theorem fromRecordCalleesNames_unique :
    [dropSessionStructureLocal2Name, dropSessionStructureLocal1Name, setSessionStateName, growOneSpeName, logClosureName].all
      (fun n => (libsignalSessionImage.symbols.filter (·.1 == n)).length == 1) = true := by
  rfl_kernel

/-! ## Stack budgets -/

/-- Stack budget of `drop_glue<SessionStructure> [local#2]`: `48 + dropChainStack` (`4192` B). -/
abbrev dropSessionStructureLocal2Stack : Nat := 48 + dropChainStack

/-- Stack budget of `drop_glue<SessionStructure> [local#1]`: `32 + dropVecChainStack` (`4224` B). -/
abbrev dropSessionStructureLocal1Stack : Nat := 32 + dropVecChainStack

/-- Stack budget of `SessionRecord::set_session_state`: `32 + dropSessionStructureLocal1Stack` (`4256` B). -/
abbrev setSessionStateStack : Nat := 32 + dropSessionStructureLocal1Stack

/-- Stack budget of `RawVec<SignalProtocolError>::grow_one`: `64 + finishGrowStack` (`4208` B). -/
abbrev growOneSpeStack : Nat := 4608

/-- Own frame of `try_decrypt_from_record::{closure#0}` (`0x381ac: sub sp, sp, #0x180` = 384 B;
no callees on the log-off path `+0x000..+0x02c -> +0x19c..+0x1b0`). -/
abbrev closureStack : Nat := 0x180

/-! ## 1 & 2. `drop_glue<SessionStructure> [local#2]` (`0x35958`) and `[local#1]` (`0x25b4`) -/

/-- Ghost arguments `(ss, G, st)` for `drop_glue<SessionStructure>` (`[local#1]` or `[local#2]`). -/
structure DropSessionStructureGhost where
  /-- Pointer to `SessionStructure` (`x0`, 344 bytes). -/
  ss : BitVec 64
  /-- Session ghost layout at `ss`. -/
  G : SessionGhost
  /-- `SessionState` model value. -/
  st : SessionState (List (BitVec 8))

/-- Specification of `core::ptr::drop_glue::<SessionStructure> [local#2]` (`0x35958`):
deallocates all owned `Vec<u8>` fields, drops `sender_chain` via `drop_glue<Chain>` and
`receiver_chains` via an inline `drop_glue<Chain>` loop plus buffer deallocation, and leaves
`memRegion x.ss 344`. -/
def dropSessionStructureLocal2Spec (A : RustAlloc) : Spec DropSessionStructureGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss⌝ ∗
      sessionStateAt A x.ss x.G x.st ∗ A.pool ∗ stackAt s.sp dropSessionStructureLocal2Stack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.ss 344 ∗ A.pool ∗ stackAt s0.sp dropSessionStructureLocal2Stack

def DropSessionStructureLocal2OkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal2Name)
    (dropSessionStructureLocal2Spec A)

def DropSessionStructureLocal2Ok_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs)
    ((trTrapProgAt b C abs).fnAddr dropSessionStructureLocal2Name)
    (dropSessionStructureLocal2Spec A)

/-- Target `subroutine_ok` proposition for `drop_glue<SessionStructure> [local#2]` (`0x35958`). -/
def DropSessionStructureLocal2Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr dropSessionStructureLocal2Name)
    (dropSessionStructureLocal2Spec A)

/-- Specification of `core::ptr::drop_glue::<SessionStructure> [local#1]` (`0x25b4`):
deallocates all owned `Vec<u8>` fields, drops `sender_chain` inline via `drop_glue<Vec<MessageKey>>`
and `receiver_chains` via `drop_glue<Vec<Chain>>`, and leaves `memRegion x.ss 344`. -/
def dropSessionStructureLocal1Spec (A : RustAlloc) : Spec DropSessionStructureGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss⌝ ∗
      sessionStateAt A x.ss x.G x.st ∗ A.pool ∗ stackAt s.sp dropSessionStructureLocal1Stack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.ss 344 ∗ A.pool ∗ stackAt s0.sp dropSessionStructureLocal1Stack

def DropSessionStructureLocal1OkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name)
    (dropSessionStructureLocal1Spec A)

def DropSessionStructureLocal1Ok_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs)
    ((trTrapProgAt b C abs).fnAddr dropSessionStructureLocal1Name)
    (dropSessionStructureLocal1Spec A)

/-- Target `subroutine_ok` proposition for `drop_glue<SessionStructure> [local#1]` (`0x25b4`). -/
def DropSessionStructureLocal1Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr dropSessionStructureLocal1Name)
    (dropSessionStructureLocal1Spec A)

/-! ## 3. `SessionRecord::set_session_state` (`0x174d4`, 15 insns) -/

/-- Ghost arguments `(record, src, cur, bs)` for `<SessionRecord>::set_session_state` (`0x174d4`). -/
structure SetSessionStateGhost where
  /-- Pointer to `SessionRecord` (`x0`; `current_session` is at `record + 0x18`). -/
  record : BitVec 64
  /-- Pointer to source 344-byte `SessionStructure` (`x1`). -/
  src : BitVec 64
  /-- Previous `current_session` at `record + 0x18`. -/
  cur : Option (SessionGhost × SessionState (List (BitVec 8)))
  /-- Raw bytes (`bs.length = 344`) of the new `SessionStructure` at `src`. -/
  bs : List (BitVec 8)

/-- Specification of `<SessionRecord>::set_session_state` (`0x174d4`): drops any existing
`current_session` at `record + 0x18` via `drop_glue<SessionStructure> [local#1]` when `cur = some _`,
then copies the 344-byte `SessionStructure` `bs` from `src` to `record + 0x18` via `memcpy`. -/
def setSessionStateSpec (A : RustAlloc) : Spec SetSessionStateGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.record ∧ s.readReg64 .x1 = x.src ∧ x.bs.length = 344⌝ ∗
      (match x.cur with
       | none => ((x.record + 0x18#64) ↦₆₄ noneCap) ∗ memRegion (x.record + 0x20#64) 336
       | some (G, st) => sessionStateAt A (x.record + 0x18#64) G st) ∗
      (x.src ↦ₛ x.bs) ∗ A.pool ∗ stackAt s.sp setSessionStateStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ((x.record + 0x18#64) ↦ₛ x.bs) ∗ (x.src ↦ₛ x.bs) ∗ A.pool ∗
      stackAt s0.sp setSessionStateStack

def SetSessionStateOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr setSessionStateName)
    (setSessionStateSpec A)

def SetSessionStateOk_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs)
    ((trTrapProgAt b C abs).fnAddr setSessionStateName)
    (setSessionStateSpec A)

/-- Target `subroutine_ok` proposition for `SessionRecord::set_session_state` (`0x174d4`). -/
def SetSessionStateOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr setSessionStateName)
    (setSessionStateSpec A)

/-! ## 4. `RawVec<SignalProtocolError>::grow_one` (`0x15c44`, 26 insns) -/

/-- Specification of `<RawVec<SignalProtocolError>>::grow_one` (`0x15c44`, stride `48`,
alignment `8`): grows capacity from `cap` to `max (2 * cap) 4` via `RawVecInner::finish_grow`,
or panics via `alloc::raw_vec::handle_error` on capacity overflow or allocation failure. -/
def growOneSpeSpec (A : RustAlloc) : Spec GrowGhost where
  pre := fun (v, cap, ptr, bs) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length = cap.toNat * 48 ∧ ptr ≠ 0 ∧
      max (2 * cap.toNat) 4 * 48 + 8 ≤ 2 ^ 63⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
    A.pool ∗ stackAt s.sp growOneSpeStack
  post := fun (v, cap, _, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0⌝ ∗ (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 4 * 48) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * cap.toNat) 4 - cap.toNat) * 48) ∗
      A.pool ∗ stackAt s0.sp growOneSpeStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def GrowOneSpeOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr growOneSpeName)
    (growOneSpeSpec A)

def GrowOneSpeOk_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs)
    ((trTrapProgAt b C abs).fnAddr growOneSpeName)
    (growOneSpeSpec A)

/-- Target `subroutine_ok` proposition for `RawVec<SignalProtocolError>::grow_one` (`0x15c44`). -/
def GrowOneSpeOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr growOneSpeName)
    (growOneSpeSpec A)

/-! ## 5. `try_decrypt_from_record::{closure#0}` (`0x381ac`, log-off path) -/

/-- Specification of `try_decrypt_from_record::<HookRng>::{closure#0}` (`0x381ac`) on the
log-off fast path (`logOff img`, `MAX_LOG_LEVEL_FILTER = 0`): returns without dereferencing its
closure arguments or mutating the heap. -/
def logClosureSpec (img : Obj.Image) : Spec Unit where
  pre := fun _ s =>
    logOff img ∗ stackAt s.sp closureStack
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      logOff img ∗ stackAt s0.sp closureStack

def LogClosureOkExt (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr logClosureName)
    ((logClosureSpec img).inImage img)

def LogClosureOk_trap (img : Obj.Image) (C : Crypto)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs)
    ((trTrapProgAt img.base C abs).fnAddr logClosureName)
    ((logClosureSpec img).inImage img)

/-- Target `subroutine_ok` proposition for `try_decrypt_from_record::{closure#0}` (`0x381ac`)
on the log-off path. -/
def LogClosureOk (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr logClosureName)
    ((logClosureSpec img).inImage img)

end CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
