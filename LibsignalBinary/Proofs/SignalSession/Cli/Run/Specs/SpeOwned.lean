/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.Proof

/-!
# Owned `SignalProtocolError` Representation and Drop Specification (`SpeOwned`, `dropSpeOwnedSpec`)

Defines `SpeOwned`, `speOwnedAt`, and `dropSpeOwnedSpec` for the 48-byte `SignalProtocolError`
values dropped by `signal_session::run` (`core::ptr::drop_glue::<SignalProtocolError>`):
- `.proto fnName e`: session-model errors (`speAt`);
- `.sessionNotFound` and `.untrustedIdentity`: wrapper `ApiError` variants (`apiErrAt`) owning a
  cloned `ProtocolAddress`;
- `.badKemKeyType` (`speWord 31`) and `.badKemKeyLength` (`speWord 33`): plain-data KEM key
  deserialization errors;
- `.plain i` (`PlainSpeTag i`): the 25 discriminant tags whose drop frees no heap allocation;
- `.withString i` (`StrSpeTag i`): the 8 discriminant tags whose drop frees a `String` (`Vec<u8>`)
  at `+0x8`.

Tag `26` (`ApplicationCallbackError`, carrying `Box<dyn Error>`) is excluded: CLI stores report
failures as `InvalidState` rather than `ApplicationCallbackError`, and `RunCompose.slotOut`
excludes `.error (.store ())`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunDrop

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApiRepr

/-- Discriminant tags `i` (`speWord i` at `+0`) for which `drop_glue::<SignalProtocolError>` returns
without deallocating (tags `2..11, 13..17, 20, 21, 23, 28..34`). -/
def plainSpeTags : List Nat :=
  [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 20, 21, 23, 28, 29, 30, 31, 32, 33, 34]

/-- Membership in `plainSpeTags`. -/
def PlainSpeTag (i : Nat) : Prop := i ∈ plainSpeTags

instance (i : Nat) : Decidable (PlainSpeTag i) := inferInstanceAs (Decidable (i ∈ plainSpeTags))

/-- Discriminant tags `i` (`speWord i` at `+0`) for which `drop_glue::<SignalProtocolError>` frees
the `Vec<u8>` buffer at `+0x8` (capacity at `+0x8`, pointer at `+0x10`) when capacity is nonzero. -/
def strSpeTags : List Nat := [0, 1, 12, 18, 22, 24, 25, 27]

/-- Membership in `strSpeTags`. -/
def StrSpeTag (i : Nat) : Prop := i ∈ strSpeTags

instance (i : Nat) : Decidable (StrSpeTag i) := inferInstanceAs (Decidable (i ∈ strSpeTags))

/-- Classification of 48-byte `SignalProtocolError` values dropped by `signal_session::run` (excluding tag `26`, `ApplicationCallbackError`). -/
inductive SpeOwned where
  /-- Session-model `SignalProtocolError` (`speAt A fnName a e`). -/
  | proto (fnName : List (BitVec 8)) (e : SignalProtocolError)
  /-- `SessionNotFound { address: Some(addr), op }` (`apiErrAt A a (.sessionNotFound addr op)`). -/
  | sessionNotFound (addr : AddrVal) (op : String)
  /-- `UntrustedIdentity(addr)` (`apiErrAt A a (.untrustedIdentity addr)`). -/
  | untrustedIdentity (addr : AddrVal)
  /-- `SignalProtocolError::BadKEMKeyType(u8)` (`speWord 31`, plain-data payload). -/
  | badKemKeyType
  /-- `SignalProtocolError::BadKEMKeyLength(KeyType, usize)` (`speWord 33`, plain-data payload). -/
  | badKemKeyLength
  /-- `SignalProtocolError` with tag `i` (`PlainSpeTag i`) and 40 plain-data payload bytes. -/
  | plain (i : Nat) (h : PlainSpeTag i)
  /-- `SignalProtocolError` with tag `i` (`StrSpeTag i`), owned `String` at `+0x8`, and 16 trailing bytes at `+0x20`. -/
  | withString (i : Nat) (h : StrSpeTag i)

/-- 48-byte memory layout predicate for `k : SpeOwned` at `a`. -/
def speOwnedAt (A : RustAlloc) (a : BitVec 64) : SpeOwned → SepProp
  | .proto fnName e => speAt A fnName a e
  | .sessionNotFound addr op => apiErrAt A a (.sessionNotFound addr op)
  | .untrustedIdentity addr => apiErrAt A a (.untrustedIdentity addr)
  | .badKemKeyType => (a ↦₆₄ speWord 31) ∗ memRegion (a + 8#64) 40
  | .badKemKeyLength => (a ↦₆₄ speWord 33) ∗ memRegion (a + 8#64) 40
  | .plain i _ => (a ↦₆₄ speWord i) ∗ memRegion (a + 8#64) 40
  | .withString i _ =>
    (a ↦₆₄ speWord i) ∗ (∃∗ bs : List (BitVec 8), vecU8 A (a + 8#64) bs) ∗
      memRegion (a + 0x20#64) 16

/-- Ghost arguments `(a, k)` for `drop_glue::<SignalProtocolError>` on an owned `SpeOwned`. -/
structure DropSpeOwnedGhost where
  /-- Pointer to the 48-byte `SignalProtocolError` (`x0`). -/
  a : BitVec 64
  k : SpeOwned

/-- Specification of `core::ptr::drop_glue::<SignalProtocolError>` on `SpeOwned` at stack budget
`stk`, returning `memRegion x.a 48` with `A.pool` and `stackAt s0.sp stk` preserved. -/
def dropSpeOwnedSpec (A : RustAlloc) (stk : Nat) : Spec DropSpeOwnedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗ speOwnedAt A x.a x.k ∗ A.pool ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 48 ∗ A.pool ∗ stackAt s0.sp stk

/-- `dropSpeOwnedSpec A stk` holds on `tripleRatchetProgAtExt img.base ext` for all `32 + extHookStack ≤ stk ≤ 2^64`. -/
def DropSpeOwnedOk (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) :
    Prop :=
  ∀ stk, 32 + extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      ((dropSpeOwnedSpec A stk).inImage img)

theorem dropSpeOwnedSpec_proto_pre (A : RustAlloc) (stk : Nat) (a : BitVec 64)
    (fnName : List (BitVec 8)) (e : SignalProtocolError) :
    (dropSpeOwnedSpec A stk).pre ⟨a, .proto fnName e⟩ =
      (DropSpeProof.dropSpeSpecStk A stk).pre ⟨a, fnName, e⟩ := rfl

theorem dropSpeOwnedSpec_proto_post (A : RustAlloc) (stk : Nat) (a : BitVec 64)
    (fnName : List (BitVec 8)) (e : SignalProtocolError) :
    (dropSpeOwnedSpec A stk).post ⟨a, .proto fnName e⟩ =
      (DropSpeProof.dropSpeSpecStk A stk).post ⟨a, fnName, e⟩ := rfl

end CryptoVerification.SignalSession.Cli.RunDrop
