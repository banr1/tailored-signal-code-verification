/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import GeneratedLean.LibsignalSessionObj
import ProofLib.VCGen

/-!
# `RandomState::new` and `HashMap::new` TLS lazy-initialization specifications

Specifications and memory-layout predicates for `<InMemSignedPreKeyStore>::new` (`0x127d8`, ICF-shared
with `<InMemSessionStore>::new`) and `<InMemIdentityKeyStore>::new` (`0x0c238`), covering both the
uninitialized (`tag ≠ 1`, calling `hashmap_random_keys`) and initialized (`tag = 1`, incrementing
`word[t + 0]`) paths on the 24-byte thread-local `KEYS` cell at `s.tpidrEl0 + tpoff`.
-/

@[expose] public section

namespace CryptoVerification.E2E.StoreNew

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet

/-! ## Symbol names, image offsets, and stack budgets -/

/-- Symbol name of the `RandomState::new` SipHash key initializer stub (`0x47f80`). -/
abbrev randomKeysName : String := "std::sys::random::linux::hashmap_random_keys"

/-- Symbol name of `<InMemSignedPreKeyStore>::new` (`0x127d8`, 28 instructions, 112 bytes;
`InMemSessionStore::new` is ICF-folded into this symbol). -/
abbrev inMemSignedPreKeyStoreNewName : String :=
  "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore>::new"

/-- Symbol name of `<InMemIdentityKeyStore>::new` (`0x0c238`, 41 instructions, 164 bytes). -/
abbrev inMemIdentityKeyStoreNewName : String :=
  "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore>::new"

abbrev inMemSessionStoreNewOff : BitVec 64 := bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore>::new")

abbrev inMemIdentityStoreNewOff : BitVec 64 := bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore>::new")

/-- Image offset of the GOT slot (`0x51638`, `got[0] = GotEntry.tpoff 16`). -/
abbrev tlsKeysGotOff : BitVec 64 := bv% (ls_field% gotOff)

/-- Thread-pointer offset (`tpoff = 16 = 0x10`) stored in `got[0]` for the `KEYS` TLS variable. -/
abbrev tlsKeysTpoff : BitVec 64 := 0x10#64

/-- Image offset of the 32-byte static empty `RawTableInner` template in `.data.rel.ro` (`0x4a658`). -/
abbrev emptyRawTableOff : BitVec 64 := bv% (ls_reloc% (ls_bytes% "ffffffffffffffff67726f75705f6964"))

/-- Image offset of the 16-byte static empty control group (`0x4a5f0`, target of the relocation at `0x4a658`). -/
abbrev emptyCtrlOff : BitVec 64 := bv% (ls_bytes% "ffffffffffffffff67726f75705f6964")

abbrev inMemSessionStoreNewFrame : Nat := 0x20

abbrev inMemSessionStoreNewStack : Nat := inMemSessionStoreNewFrame + extHookStack

abbrev inMemIdentityStoreNewFrame : Nat := 0x30

abbrev inMemIdentityStoreNewStack : Nat := inMemIdentityStoreNewFrame + extHookStack

/-! ## Symbol and offset guards -/

section AddrGuards
open ProofLib.ProgramReflection
set_option maxRecDepth 2000000

theorem inMemSignedPreKeyStoreNew_fnOff :
    libsignalSessionCode.fnOff inMemSignedPreKeyStoreNewName = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore>::new") := by
  exact libsignalSessionCode_fnOff_0x127d8

theorem inMemIdentityKeyStoreNew_fnOff :
    libsignalSessionCode.fnOff inMemIdentityKeyStoreNewName = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore>::new") := by
  exact libsignalSessionCode_fnOff_0xc238

theorem randomKeys_fnOff :
    libsignalSessionCode.fnOff randomKeysName = num% (ls_off% "std::sys::random::linux::hashmap_random_keys") := by
  exact (ls_stub% "std::sys::random::linux::hashmap_random_keys")

theorem inMemSignedPreKeyStoreNew_addr_eq {img : Obj.Image}
    (h : Obj.Loads libsignalSessionImage img) :
    entryOf img inMemSignedPreKeyStoreNewName = img.base + inMemSessionStoreNewOff := by
  rw [entryOf, Program.ofImage_eq_rebase libsignalSessionCode_canonical h, Program.fnAddr_rebase,
    inMemSignedPreKeyStoreNew_fnOff]

theorem inMemIdentityKeyStoreNew_addr_eq {img : Obj.Image}
    (h : Obj.Loads libsignalSessionImage img) :
    entryOf img inMemIdentityKeyStoreNewName = img.base + inMemIdentityStoreNewOff := by
  rw [entryOf, Program.ofImage_eq_rebase libsignalSessionCode_canonical h, Program.fnAddr_rebase,
    inMemIdentityKeyStoreNew_fnOff]

end AddrGuards

/-! ## TLS `KEYS` cell, `RandomState`, `HashMap`, and `InMem` store layouts -/

/-- The 24-byte `std::sys::thread_local::native::lazy::Storage<Cell<(u64, u64)>, !>` cell at `t`:
`[t + 0 .. t + 8)` holds `k0`, `[t + 8 .. t + 16)` holds `k1`, `[t + 16]` holds `tag`
(`0#8` = `Uninitialized`, `1#8` = `Alive`), and `[t + 17 .. t + 24)` is 7 bytes of padding. -/
def tlsKeysRawAt (t : BitVec 64) (k0 k1 : BitVec 64) (tag : BitVec 8) : SepProp :=
  (t ↦₆₄ k0) ∗ ((t + 8#64) ↦₆₄ k1) ∗ ((t + 16#64) ↦₈ tag) ∗ memRegion (t + 17#64) 7

/-- Initialized 24-byte TLS `KEYS` cell (`tag = 1#8`, `State::Alive`) holding next keys `(k0, k1)`. -/
def tlsKeysInitAt (t : BitVec 64) (k0 k1 : BitVec 64) : SepProp :=
  tlsKeysRawAt t k0 k1 1#8

/-- Uninitialized 24-byte TLS `KEYS` cell (`tag ≠ 1#8`, e.g. `tag = 0#8` for `State::Uninitialized`). -/
def tlsKeysUninitAt (t : BitVec 64) : SepProp :=
  ∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64, ∃∗ tag : BitVec 8,
    ⌜tag ≠ 1#8⌝ ∗ tlsKeysRawAt t k0 k1 tag

/-- Combined 24-byte TLS `KEYS` cell predicate parameterized by `Option (BitVec 64 × BitVec 64)`:
`none` = uninitialized (`tag ≠ 1#8`), `some (k0, k1)` = initialized (`tag = 1#8`) holding `(k0, k1)`. -/
def tlsKeysAt (t : BitVec 64) : Option (BitVec 64 × BitVec 64) → SepProp
  | none => tlsKeysUninitAt t
  | some (k0, k1) => tlsKeysInitAt t k0 k1

/-- `std::hash::random::RandomState { k0, k1 }` (`16` bytes at `p`). -/
def randomStateAt (p : BitVec 64) (k0 k1 : BitVec 64) : SepProp :=
  (p ↦₆₄ k0) ∗ ((p + 8#64) ↦₆₄ k1)

/-- Empty `hashbrown::raw::RawTableInner` (`32` bytes at `out`):
`ctrl = ctrlPtr` at `+0`, `bucket_mask = 0` at `+8`, `growth_left = 0` at `+16`, `items = 0` at `+24`. -/
def emptyRawTableAt (ctrlPtr : BitVec 64) (out : BitVec 64) : SepProp :=
  (out ↦₆₄ ctrlPtr) ∗ ((out + 8#64) ↦₆₄ 0#64) ∗
    ((out + 16#64) ↦₆₄ 0#64) ∗ ((out + 24#64) ↦₆₄ 0#64)

/-- Empty `HashMap<K, V, RandomState>` (`48` bytes at `out`):
`emptyRawTableAt ctrlPtr out` (`32` bytes at `+0..+32`) followed by `randomStateAt (out + 32#64) k0 k1`
(`16` bytes at `+32..+48`). Also the full representation of a newly constructed
`InMemSessionStore` or `InMemSignedPreKeyStore`. -/
def emptyHashMapAt (ctrlPtr : BitVec 64) (out : BitVec 64) (k0 k1 : BitVec 64) : SepProp :=
  emptyRawTableAt ctrlPtr out ∗ randomStateAt (out + 32#64) k0 k1

/-- Newly constructed `InMemIdentityKeyStore` (`120` bytes at `out`):
* `+0x00..+0x30` (`48` B): `emptyHashMapAt ctrlPtr out k0 k1` (`identities` table)
* `+0x30..+0x70` (`64` B): `(out + 48#64) ↦ₛ kpBytes` (`key_pair : IdentityKeyPair`)
* `+0x70..+0x74` (`4` B):  `(out + 112#64) ↦₃₂ regId` (`registration_id : u32`)
* `+0x74..+0x78` (`4` B):  `memRegion (out + 116#64) 4` (struct trailing padding) -/
def emptyIdentityKeyStoreAt (ctrlPtr : BitVec 64) (out : BitVec 64) (k0 k1 : BitVec 64)
    (kpBytes : List (BitVec 8)) (regId : BitVec 32) : SepProp :=
  emptyHashMapAt ctrlPtr out k0 k1 ∗
    ((out + 48#64) ↦ₛ kpBytes) ∗
    ((out + 112#64) ↦₃₂ regId) ∗
    memRegion (out + 116#64) 4

/-- Read-only image constants used by `RandomState::new` and `HashMap::new` at base `b`:
the GOT slot `(b + 0x51638#64) ↦₆₄ᵣ tpoff` and the 32-byte static `RawTableInner` template at
`b + 0x4a658#64` holding `(ctrlPtr, 0, 0, 0)`. -/
def storeNewRoDataAt (b tpoff ctrlPtr : BitVec 64) : SepProp :=
  ((b + tlsKeysGotOff) ↦₆₄ᵣ tpoff) ∗
    ((b + emptyRawTableOff) ↦₆₄ᵣ ctrlPtr) ∗
    ((b + (emptyRawTableOff + 8#64)) ↦₆₄ᵣ 0#64) ∗
    ((b + (emptyRawTableOff + 16#64)) ↦₆₄ᵣ 0#64) ∗
    ((b + (emptyRawTableOff + 24#64)) ↦₆₄ᵣ 0#64)

/-! ## Specifications for `<InMemSignedPreKeyStore>::new` / `<InMemSessionStore>::new` (`0x127d8`) -/

/-- Ghost state for `<InMemSignedPreKeyStore>::new` (`0x127d8`) on the uninitialized TLS path (`tag ≠ 1#8`),
generic over the GOT `tpoff` and static `ctrlPtr`. -/
structure SessionStoreNewUninitGhost where
  out     : BitVec 64
  tpoff   : BitVec 64
  ctrlPtr : BitVec 64
  k0Old   : BitVec 64
  k1Old   : BitVec 64
  tag     : BitVec 8

/-- `RandomState::new` key-generation hook (`x0, x1` returned as two `u64` SipHash keys;
no constraint on `x0`/`x1` in the postcondition so any deterministic hook satisfies `HookOk`).
Definitionally equal to `CryptoVerification.E2E.Bin.randomKeysSpec`. -/
def randomKeysSpec : Spec Unit where
  pre := fun _ s => stackAt s.sp extHookStack
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ stackAt s0.sp extHookStack

/-- `hookNoop` satisfies `HookOk hookNoop randomKeysSpec`. -/
theorem randomKeysSpec_nonvac : HookOk hookNoop randomKeysSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  simp only [randomKeysSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact ⟨rfl, hpre⟩

/-- `randomKeysSpec` strengthened with `sf.tpidrEl0 = s0.tpidrEl0` (satisfied by any `retHook`,
including `hookNoop`). -/
def randomKeysTpidrSpec : Spec Unit where
  pre := fun _ s => stackAt s.sp extHookStack
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0⌝ ∗ stackAt s0.sp extHookStack

/-- `hookNoop` satisfies `HookOk hookNoop randomKeysTpidrSpec`. -/
theorem randomKeysTpidrSpec_nonvac : HookOk hookNoop randomKeysTpidrSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  simp only [randomKeysTpidrSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact ⟨⟨rfl, rfl⟩, hpre⟩

/-- Base-rebased specification of `<InMemSignedPreKeyStore>::new` (`0x127d8`) on the uninitialized
TLS path (`tag ≠ 1#8`), generic over the TLS offset `tpoff` (`t = s.tpidrEl0 + tpoff`) and `ctrlPtr`. -/
def sessionStoreNewUninitBaseSpec (b : BitVec 64) : Spec SessionStoreNewUninitGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x8 = g.out ∧ g.tag ≠ 1#8⌝ ∗
      storeNewRoDataAt b g.tpoff g.ctrlPtr ∗
      memRegion g.out 48 ∗
      tlsKeysRawAt (s.tpidrEl0 + g.tpoff) g.k0Old g.k1Old g.tag ∗
      stackAt s.sp inMemSessionStoreNewStack
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      storeNewRoDataAt b g.tpoff g.ctrlPtr ∗
      (∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64,
        emptyHashMapAt g.ctrlPtr g.out k0 k1 ∗
          tlsKeysInitAt (s0.tpidrEl0 + g.tpoff) (k0 + 1#64) k1) ∗
      stackAt s0.sp inMemSessionStoreNewStack

/-- Ghost state for `<InMemSignedPreKeyStore>::new` (`0x127d8`) on the initialized TLS path (`tag = 1#8`),
generic over the GOT `tpoff` and static `ctrlPtr`. -/
structure SessionStoreNewInitGhost where
  out     : BitVec 64
  tpoff   : BitVec 64
  ctrlPtr : BitVec 64
  k0      : BitVec 64
  k1      : BitVec 64

/-- Base-rebased specification of `<InMemSignedPreKeyStore>::new` (`0x127d8`) on the initialized
TLS path (`tag = 1#8`), generic over the TLS offset `tpoff` (`t = s.tpidrEl0 + tpoff`) and `ctrlPtr`.
Needs only the 32-byte local stack frame (`inMemSessionStoreNewFrame = 0x20`) since no call is made. -/
def sessionStoreNewInitBaseSpec (b : BitVec 64) : Spec SessionStoreNewInitGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x8 = g.out⌝ ∗
      storeNewRoDataAt b g.tpoff g.ctrlPtr ∗
      memRegion g.out 48 ∗
      tlsKeysInitAt (s.tpidrEl0 + g.tpoff) g.k0 g.k1 ∗
      stackAt s.sp inMemSessionStoreNewFrame
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0⌝ ∗
      storeNewRoDataAt b g.tpoff g.ctrlPtr ∗
      emptyHashMapAt g.ctrlPtr g.out g.k0 g.k1 ∗
      tlsKeysInitAt (s0.tpidrEl0 + g.tpoff) (g.k0 + 1#64) g.k1 ∗
      stackAt s0.sp inMemSessionStoreNewFrame

/-- Image-level specification of `<InMemSignedPreKeyStore>::new` (`0x127d8`) on the uninitialized
TLS path (`tag ≠ 1#8`). Ghost: `(out, k0Old, k1Old, tag)`. -/
def sessionStoreNewUninitSpec (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 8) :=
  Spec.inImage
    { pre := fun (out, k0Old, k1Old, tag) s =>
        ⌜s.readReg64 .x8 = out ∧ tag ≠ 1#8⌝ ∗
          memRegion out 48 ∗
          tlsKeysRawAt (s.tpidrEl0 + tlsKeysTpoff) k0Old k1Old tag ∗
          stackAt s.sp inMemSessionStoreNewStack
      post := fun (out, _, _, _) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          (∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64,
            emptyHashMapAt (img.base + emptyCtrlOff) out k0 k1 ∗
              tlsKeysInitAt (s0.tpidrEl0 + tlsKeysTpoff) (k0 + 1#64) k1) ∗
          stackAt s0.sp inMemSessionStoreNewStack }
    img

/-- Image-level specification of `<InMemSignedPreKeyStore>::new` (`0x127d8`) on the initialized
TLS path (`tag = 1#8`). Ghost: `(out, k0, k1)`. -/
def sessionStoreNewInitSpec (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64) :=
  Spec.inImage
    { pre := fun (out, k0, k1) s =>
        ⌜s.readReg64 .x8 = out⌝ ∗
          memRegion out 48 ∗
          tlsKeysInitAt (s.tpidrEl0 + tlsKeysTpoff) k0 k1 ∗
          stackAt s.sp inMemSessionStoreNewFrame
      post := fun (out, k0, k1) s0 sf =>
        ⌜sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0⌝ ∗
          emptyHashMapAt (img.base + emptyCtrlOff) out k0 k1 ∗
          tlsKeysInitAt (s0.tpidrEl0 + tlsKeysTpoff) (k0 + 1#64) k1 ∗
          stackAt s0.sp inMemSessionStoreNewFrame }
    img

/-- Unified image-level specification of `<InMemSignedPreKeyStore>::new` (`0x127d8`) covering both
`st = none` (uninitialized TLS cell) and `st = some (k0, k1)` (initialized TLS cell).
Ghost: `(out, st)`. -/
def sessionStoreNewSpec (img : Obj.Image) :
    Spec (BitVec 64 × Option (BitVec 64 × BitVec 64)) :=
  Spec.inImage
    { pre := fun (out, st) s =>
        ⌜s.readReg64 .x8 = out⌝ ∗
          memRegion out 48 ∗
          tlsKeysAt (s.tpidrEl0 + tlsKeysTpoff) st ∗
          stackAt s.sp inMemSessionStoreNewStack
      post := fun (out, st) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          (match st with
           | none =>
             ∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64,
               emptyHashMapAt (img.base + emptyCtrlOff) out k0 k1 ∗
                 tlsKeysInitAt (s0.tpidrEl0 + tlsKeysTpoff) (k0 + 1#64) k1
           | some (k0, k1) =>
             emptyHashMapAt (img.base + emptyCtrlOff) out k0 k1 ∗
               tlsKeysInitAt (s0.tpidrEl0 + tlsKeysTpoff) (k0 + 1#64) k1) ∗
          stackAt s0.sp inMemSessionStoreNewStack }
    img

/-! ## Specifications for `<InMemIdentityKeyStore>::new` (`0x0c238`) -/

/-- Ghost state for `<InMemIdentityKeyStore>::new` (`0x0c238`) on the uninitialized TLS path (`tag ≠ 1#8`),
generic over the GOT `tpoff` and static `ctrlPtr`. -/
structure IdentityStoreNewUninitGhost where
  out     : BitVec 64
  kpPtr   : BitVec 64
  kpBytes : List (BitVec 8)
  regId   : BitVec 32
  tpoff   : BitVec 64
  ctrlPtr : BitVec 64
  k0Old   : BitVec 64
  k1Old   : BitVec 64
  tag     : BitVec 8

/-- Base-rebased specification of `<InMemIdentityKeyStore>::new` (`0x0c238`) on the uninitialized
TLS path (`tag ≠ 1#8`), generic over the TLS offset `tpoff` (`t = s.tpidrEl0 + tpoff`) and `ctrlPtr`. -/
def identityStoreNewUninitBaseSpec (b : BitVec 64) : Spec IdentityStoreNewUninitGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x8 = g.out ∧ s.readReg64 .x0 = g.kpPtr ∧ s.readReg32 .x1 = g.regId ∧
      g.kpBytes.length = 64 ∧ g.tag ≠ 1#8⌝ ∗
      storeNewRoDataAt b g.tpoff g.ctrlPtr ∗
      memRegion g.out 120 ∗
      (g.kpPtr ↦ₛ g.kpBytes) ∗
      tlsKeysRawAt (s.tpidrEl0 + g.tpoff) g.k0Old g.k1Old g.tag ∗
      stackAt s.sp inMemIdentityStoreNewStack
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      storeNewRoDataAt b g.tpoff g.ctrlPtr ∗
      (∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64,
        emptyIdentityKeyStoreAt g.ctrlPtr g.out k0 k1 g.kpBytes g.regId ∗
          tlsKeysInitAt (s0.tpidrEl0 + g.tpoff) (k0 + 1#64) k1) ∗
      (g.kpPtr ↦ₛ g.kpBytes) ∗
      stackAt s0.sp inMemIdentityStoreNewStack

/-- Ghost state for `<InMemIdentityKeyStore>::new` (`0x0c238`) on the initialized TLS path (`tag = 1#8`),
generic over the GOT `tpoff` and static `ctrlPtr`. -/
structure IdentityStoreNewInitGhost where
  out     : BitVec 64
  kpPtr   : BitVec 64
  kpBytes : List (BitVec 8)
  regId   : BitVec 32
  tpoff   : BitVec 64
  ctrlPtr : BitVec 64
  k0      : BitVec 64
  k1      : BitVec 64

/-- Base-rebased specification of `<InMemIdentityKeyStore>::new` (`0x0c238`) on the initialized
TLS path (`tag = 1#8`), generic over the TLS offset `tpoff` (`t = s.tpidrEl0 + tpoff`) and `ctrlPtr`.
Needs only the 48-byte local stack frame (`inMemIdentityStoreNewFrame = 0x30`) since no call is made. -/
def identityStoreNewInitBaseSpec (b : BitVec 64) : Spec IdentityStoreNewInitGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x8 = g.out ∧ s.readReg64 .x0 = g.kpPtr ∧ s.readReg32 .x1 = g.regId ∧
      g.kpBytes.length = 64⌝ ∗
      storeNewRoDataAt b g.tpoff g.ctrlPtr ∗
      memRegion g.out 120 ∗
      (g.kpPtr ↦ₛ g.kpBytes) ∗
      tlsKeysInitAt (s.tpidrEl0 + g.tpoff) g.k0 g.k1 ∗
      stackAt s.sp inMemIdentityStoreNewFrame
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0⌝ ∗
      storeNewRoDataAt b g.tpoff g.ctrlPtr ∗
      emptyIdentityKeyStoreAt g.ctrlPtr g.out g.k0 g.k1 g.kpBytes g.regId ∗
      tlsKeysInitAt (s0.tpidrEl0 + g.tpoff) (g.k0 + 1#64) g.k1 ∗
      (g.kpPtr ↦ₛ g.kpBytes) ∗
      stackAt s0.sp inMemIdentityStoreNewFrame

/-- Image-level specification of `<InMemIdentityKeyStore>::new` (`0x0c238`) on the uninitialized
TLS path (`tag ≠ 1#8`). Ghost: `(out, kpPtr, kpBytes, regId, k0Old, k1Old, tag)`. -/
def identityStoreNewUninitSpec (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 32 × BitVec 64 × BitVec 64 × BitVec 8) :=
  Spec.inImage
    { pre := fun (out, kpPtr, kpBytes, regId, k0Old, k1Old, tag) s =>
        ⌜s.readReg64 .x8 = out ∧ s.readReg64 .x0 = kpPtr ∧ s.readReg32 .x1 = regId ∧
           kpBytes.length = 64 ∧ tag ≠ 1#8⌝ ∗
          memRegion out 120 ∗
          (kpPtr ↦ₛ kpBytes) ∗
          tlsKeysRawAt (s.tpidrEl0 + tlsKeysTpoff) k0Old k1Old tag ∗
          stackAt s.sp inMemIdentityStoreNewStack
      post := fun (out, kpPtr, kpBytes, regId, _, _, _) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          (∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64,
            emptyIdentityKeyStoreAt (img.base + emptyCtrlOff) out k0 k1 kpBytes regId ∗
              tlsKeysInitAt (s0.tpidrEl0 + tlsKeysTpoff) (k0 + 1#64) k1) ∗
          (kpPtr ↦ₛ kpBytes) ∗
          stackAt s0.sp inMemIdentityStoreNewStack }
    img

/-- Image-level specification of `<InMemIdentityKeyStore>::new` (`0x0c238`) on the initialized
TLS path (`tag = 1#8`). Ghost: `(out, kpPtr, kpBytes, regId, k0, k1)`. -/
def identityStoreNewInitSpec (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 32 × BitVec 64 × BitVec 64) :=
  Spec.inImage
    { pre := fun (out, kpPtr, kpBytes, regId, k0, k1) s =>
        ⌜s.readReg64 .x8 = out ∧ s.readReg64 .x0 = kpPtr ∧ s.readReg32 .x1 = regId ∧
          kpBytes.length = 64⌝ ∗
          memRegion out 120 ∗
          (kpPtr ↦ₛ kpBytes) ∗
          tlsKeysInitAt (s.tpidrEl0 + tlsKeysTpoff) k0 k1 ∗
          stackAt s.sp inMemIdentityStoreNewFrame
      post := fun (out, kpPtr, kpBytes, regId, k0, k1) s0 sf =>
        ⌜sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0⌝ ∗
          emptyIdentityKeyStoreAt (img.base + emptyCtrlOff) out k0 k1 kpBytes regId ∗
          tlsKeysInitAt (s0.tpidrEl0 + tlsKeysTpoff) (k0 + 1#64) k1 ∗
          (kpPtr ↦ₛ kpBytes) ∗
          stackAt s0.sp inMemIdentityStoreNewFrame }
    img

/-- Unified image-level specification of `<InMemIdentityKeyStore>::new` (`0x0c238`) covering both
`st = none` (uninitialized TLS cell) and `st = some (k0, k1)` (initialized TLS cell).
Ghost: `(out, kpPtr, kpBytes, regId, st)`. -/
def identityStoreNewSpec (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 32 × Option (BitVec 64 × BitVec 64)) :=
  Spec.inImage
    { pre := fun (out, kpPtr, kpBytes, regId, st) s =>
        ⌜s.readReg64 .x8 = out ∧ s.readReg64 .x0 = kpPtr ∧ s.readReg32 .x1 = regId ∧
          kpBytes.length = 64⌝ ∗
          memRegion out 120 ∗
          (kpPtr ↦ₛ kpBytes) ∗
          tlsKeysAt (s.tpidrEl0 + tlsKeysTpoff) st ∗
          stackAt s.sp inMemIdentityStoreNewStack
      post := fun (out, kpPtr, kpBytes, regId, st) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          (match st with
           | none =>
             ∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64,
               emptyIdentityKeyStoreAt (img.base + emptyCtrlOff) out k0 k1 kpBytes regId ∗
                 tlsKeysInitAt (s0.tpidrEl0 + tlsKeysTpoff) (k0 + 1#64) k1
           | some (k0, k1) =>
             emptyIdentityKeyStoreAt (img.base + emptyCtrlOff) out k0 k1 kpBytes regId ∗
               tlsKeysInitAt (s0.tpidrEl0 + tlsKeysTpoff) (k0 + 1#64) k1) ∗
          (kpPtr ↦ₛ kpBytes) ∗
          stackAt s0.sp inMemIdentityStoreNewStack }
    img

end CryptoVerification.E2E.StoreNew
