/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Support.SeedModel
public import LibsignalBinary.Proofs.E2E.Record.Support.Hooks
public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
public import LibsignalBinary.Proofs.E2E.Record.Support.Image
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymD
import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSym -- shake: keep

/-!
# Top-Level Specification of `SessionRecord::deserialize` on Seed Bytes

Defines `deserializeSeedSpec` (on `sessionImg0`) and its relocatable `[LibsignalPlacement]`
counterpart `deserializeSeedPlacedSpec` (block `46`, `lsProg_46 H`) for
`<SessionRecord>::deserialize(&rec[..])` (`0x16ed4`, 368-byte `sret` slot in `x8`) when
`bs = seedRecord f` (`SeedOk f`):
* **Precondition**: `FrozenLoaded` (or `LibsignalCodeRoLoaded lsmpl`) providing `.rodata` jump tables
  and `BytesAdapter` vtables, read-only input slice `p ↦ₛ bs`, 368-byte output slot at `out`, and
  64 KiB stack budget `recDeserializeStack`.
* **Postcondition**: `Ok(record)` in niche form (`sessionRecordAt A0 out g r` with `CanonRecord g r`
  and `encodeRecord r = seedRecord f`, word `0` bounded away from the `-1` `Err` niche), input bytes
  and trace unchanged.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Serialization (OkAt CanonRecord allocPanic)

/-- Symbol name of `<SessionRecord>::deserialize` (`0x16ed4`). -/
abbrev recDeserializeName : String :=
  "<libsignal_protocol::state::session::SessionRecord>::deserialize"

/-- 64 KiB stack budget for `SessionRecord::deserialize` (`0x770` local frame plus nested merge and
allocator callees). -/
abbrev recDeserializeStack : Nat := 65536

/-- Ghost state for `SessionRecord::deserialize` on `bs = seedRecord f`. -/
structure DeserializeSeedGhost where
  p : BitVec 64
  out : BitVec 64
  bs : List (BitVec 8)
  f : List (BitVec 8)

/-- Specification of `SessionRecord::deserialize` (`0x16ed4`) on `seedRecord f`: writes canonical
`Ok(record)` (`sessionRecordAt A0 out g r` with `encodeRecord r = seedRecord f`) at `out`. -/
noncomputable def deserializeSeedSpec : Spec DeserializeSeedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.p ∧ s.readReg64 .x1 = BitVec.ofNat 64 x.bs.length ∧
      s.readReg64 .x8 = x.out ∧ SeedOk x.f ∧ x.bs = seedRecord x.f ∧
      sessionImg0.FrozenLoaded s ∧ s.symtab = sessionImg0.symtab⌝ ∗
      (x.p ↦ₛ x.bs) ∗ memRegion x.out 368 ∗ stackAt s.sp recDeserializeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.p ↦ₛ x.bs) ∗
      (∃∗ g : RecordGhost, ∃∗ r : SessionRecord (List (BitVec 8)),
        ⌜CanonRecord g r ∧ encodeRecord r = x.bs⌝ ∗ sessionRecordAt A0 x.out g r) ∗
      stackAt s0.sp recDeserializeStack
  onPanic := allocPanic

/-! ## Relocatable `[LibsignalPlacement]` Specification -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

/-- Image-free base contract of `SessionRecord::deserialize` on seed's bytes `seedRecord f`:
`Ok(record)` at `out` (niche form), canonical and re-encoding to the input. -/
noncomputable def deserializeSeedRawSpec : Spec DeserializeSeedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.p ∧ s.readReg64 .x1 = BitVec.ofNat 64 x.bs.length ∧
      s.readReg64 .x8 = x.out ∧ SeedOk x.f ∧ x.bs = seedRecord x.f⌝ ∗
      (x.p ↦ₛ x.bs) ∗ memRegion x.out 368 ∗ stackAt s.sp recDeserializeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.p ↦ₛ x.bs) ∗
      (∃∗ g : RecordGhost, ∃∗ r : SessionRecord (List (BitVec 8)),
        ⌜CanonRecord g r ∧ encodeRecord r = x.bs⌝ ∗ sessionRecordAt A0 x.out g r) ∗
      stackAt s0.sp recDeserializeStack
  onPanic := allocPanic

noncomputable abbrev deserializeSeedPlacedSpec [LibsignalPlacement] : Spec DeserializeSeedGhost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl deserializeSeedRawSpec

def DeserializeSeedPlacedOk [LibsignalPlacement]
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeSeedPlacedSpec

abbrev lsDeserHandleAllocErrorSym : String :=
  "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error"

/-- External allocator, `memcpy`, and error hook contracts required by relocatable
`SessionRecord::deserialize` and its `prost` / `RawVec` callees on `H`. -/
structure PlacedDeserializeHooks (A : RustAlloc) (H : String → Option (State → State)) : Prop where
  shim : H lsRustNoAllocShimSym = some hookNoop
  alloc : HookSat H lsRustAllocSym (rustAllocSpec A)
  realloc : HookSat H lsRustReallocSym (rustReallocSpec A)
  dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)
  memcpy : HookSat H lsMemcpySym framelessMemcpySpec
  panic_alloc : H lsDeserHandleAllocErrorSym = some Rust.panicked
  panic_raw : H lsHandleErrorSym = some Rust.panicked

end Placed

end CryptoVerification.E2E.Record
