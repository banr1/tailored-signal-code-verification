/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MergeField10_11_13_15WPlaced
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import ProofLib.SepLogic.WPp

/-!
# `SessionStructure::merge_field` on Tags 10, 11, 13, and 15

Verifies `<SessionStructure as prost::Message>::merge_field::<&mut &[u8]>` at `mergeFieldStackX`
with slice length `< 2 ^ 62` on `SP2Ext` and re-exports the relocatable `[LibsignalPlacement]`
leaves for:
- Tag 10 (`remote_registration_id`, `uint32` at `ss + 0x150`),
- Tag 11 (`local_registration_id`, `uint32` at `ss + 0x154`),
- Tag 13 (`alice_base_key`, `Vec<u8>` at `ss + 0x60`),
- Tag 15 (`pq_ratchet_state`, `Vec<u8>` at `ss + 0x78`, replace/last-wins semantics).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.B3DeserQ

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeSeed.IdentityRootKeysStateSimp
open CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenIdentityRootKeys
open CryptoVerification.E2E.Record.L1GX
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem L1_MergeField10_11_13_15W : True := trivial

private theorem int64_raw_toBitVec_dq5 (n : Nat) (h : n < 2 ^ 64) :
    ({ toUInt64 := { toBitVec := { toFin := ⟨n, h⟩ } } } : Int64).toBitVec = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  change n = n % (2 ^ 64)
  exact (Nat.mod_eq_of_lt h).symm

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  setWidth8_setWidth64_setWidth32_identityRootKeys int64_raw_toBitVec_dq5
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre_identityRootKeys
  sp_setMem_setPC_pre_identityRootKeys
  readReg64_setPC_pre_identityRootKeys
  readReg64_setMem_setPC_pre_identityRootKeys
  readReg32_setPC_pre_identityRootKeys
  readReg32_setMem_setPC_pre_identityRootKeys
  readReg_setPC_pre_identityRootKeys
  readReg_setMem_setPC_pre_identityRootKeys

/-! ## `mergeFieldXSpecAtW` specification -/

/-- `L1GX.mergeFieldXSpec` parameterized by `img : Obj.Image`, W-stack `mergeFieldStackX`,
and slice length bound `(x.fld.payload ++ x.tail).length < 2 ^ 62`. -/
def mergeFieldXSpecAtW (img : Obj.Image) (P : GenFieldX → Prop) : Spec MergeFieldXGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧ x.fld.Fresh x.v ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 62 ∧
      img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      prostSSGXAt A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗
      stackAt s.sp mergeFieldStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      prostSSGXAt A0 x.ss (x.v.apply x.fld) ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt s0.sp mergeFieldStackX
  onPanic := Serialization.allocPanic

/-- `subroutine_ok` for `mergeFieldXSpecAtW img P` on `SP2Ext img.base ext`
(defeq `contractProg img.base ext`). -/
def MergeFieldXOkAtW (img : Obj.Image) (ext : String → Option (State → State))
    (P : GenFieldX → Prop) : Prop :=
  OkAtX img.base ext mergeFieldName (mergeFieldXSpecAtW img P)

/-! ## Standalone single-field specifications -/

/-- Ghost state for a standalone `uint32` (`int32::merge`) field of `SessionStructure`
(tag 10 `remote_registration_id` at `ss + 0x150`, tag 11 `local_registration_id` at `ss + 0x154`). -/
structure MergeFieldU32Ghost where
  ss : BitVec 64
  oldVal : BitVec 32
  val : BitVec 32
  payload : List (BitVec 8)
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  tail : List (BitVec 8)

/-- Standalone W-stack spec for `SessionStructure::merge_field` on a `uint32` varint field at
`tag` and struct byte offset `fieldOff` (`0x150#64` for tag 10, `0x154#64` for tag 11).
Only `((x.ss + fieldOff) ↦₃₂ x.oldVal)` is in the footprint; the rest of `SessionStructure`
frames automatically via separation logic. -/
def mergeFieldU32FieldSpecAtW (img : Obj.Image) (tag : Nat) (fieldOff : BitVec 64) :
    Spec MergeFieldU32Ghost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 WireType.varint.toNat ∧
      s.readReg64 .x3 = x.bufRef ∧
      mergeUint32 .varint (x.payload ++ x.tail) = some (x.val, x.tail) ∧
      (x.payload ++ x.tail).length < 2 ^ 62 ∧
      img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      ((x.ss + fieldOff) ↦₃₂ x.oldVal) ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.payload ++ x.tail) ∗
      stackAt s.sp mergeFieldStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      ((x.ss + fieldOff) ↦₃₂ x.val) ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.payload ++ x.tail) x.tail ∗
      stackAt s0.sp mergeFieldStackX
  onPanic := Serialization.allocPanic

/-- Standalone W-stack spec for tag 10 (`remote_registration_id` at `ss + 0x150#64`). -/
abbrev mergeField10FieldSpecAtW (img : Obj.Image) : Spec MergeFieldU32Ghost :=
  mergeFieldU32FieldSpecAtW img 10 0x150#64

/-- Standalone W-stack spec for tag 11 (`local_registration_id` at `ss + 0x154#64`). -/
abbrev mergeField11FieldSpecAtW (img : Obj.Image) : Spec MergeFieldU32Ghost :=
  mergeFieldU32FieldSpecAtW img 11 0x154#64

/-- Ghost state for a standalone `Vec<u8>` (`bytes::merge`) field of `SessionStructure`
(tag 13 `alice_base_key` at `ss + 0x60`, tag 15 `pq_ratchet_state` at `ss + 0x78`). -/
structure MergeFieldBytesGhost where
  ss : BitVec 64
  oldBytes : List (BitVec 8)
  bytes : List (BitVec 8)
  payload : List (BitVec 8)
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  tail : List (BitVec 8)

/-- Standalone W-stack spec for `SessionStructure::merge_field` on a length-delimited `Vec<u8>`
field at `tag` and struct byte offset `fieldOff` (`0x60#64` for tag 13, `0x78#64` for tag 15),
with replace (`last-wins`) semantics `vecU8 A0 (x.ss + fieldOff) x.oldBytes ↦ vecU8 A0 (x.ss + fieldOff) x.bytes`
for `(x.payload ++ x.tail).length < 2 ^ 62`. -/
def mergeFieldBytesFieldSpecAtW (img : Obj.Image) (tag : Nat) (fieldOff : BitVec 64) :
    Spec MergeFieldBytesGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat ∧
      s.readReg64 .x3 = x.bufRef ∧
      mergeBytes .lengthDelimited (x.payload ++ x.tail) = some (x.bytes, x.tail) ∧
      (x.payload ++ x.tail).length < 2 ^ 62 ∧
      img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      vecU8 A0 (x.ss + fieldOff) x.oldBytes ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.payload ++ x.tail) ∗
      stackAt s.sp mergeFieldStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      vecU8 A0 (x.ss + fieldOff) x.bytes ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.payload ++ x.tail) x.tail ∗
      stackAt s0.sp mergeFieldStackX
  onPanic := Serialization.allocPanic

/-- Standalone W-stack spec for tag 13 (`alice_base_key` at `ss + 0x60#64`). -/
abbrev mergeField13FieldSpecAtW (img : Obj.Image) : Spec MergeFieldBytesGhost :=
  mergeFieldBytesFieldSpecAtW img 13 0x60#64

/-- Standalone W-stack spec for tag 15 (`pq_ratchet_state` at `ss + 0x78#64`) with REPLACE
(`last-wins`) semantics `vecU8 A0 (x.ss + 0x78#64) x.oldBytes ↦ vecU8 A0 (x.ss + 0x78#64) x.bytes`
and `< 2 ^ 62` length precondition. -/
abbrev mergeField15FieldSpecAtW (img : Obj.Image) : Spec MergeFieldBytesGhost :=
  mergeFieldBytesFieldSpecAtW img 15 0x78#64

/-- Arbitrary-allocator (`A : RustAlloc`) W-stack spec for `SessionStructure::merge_field` on a
`uint32` varint field at `tag` and struct byte offset `fieldOff`, carrying `A.pool`. -/
def mergeFieldU32FieldSpecAtWA (A : RustAlloc) (img : Obj.Image) (tag : Nat)
    (fieldOff : BitVec 64) : Spec MergeFieldU32Ghost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 WireType.varint.toNat ∧
      s.readReg64 .x3 = x.bufRef ∧
      mergeUint32 .varint (x.payload ++ x.tail) = some (x.val, x.tail) ∧
      (x.payload ++ x.tail).length < 2 ^ 62 ∧
      img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      ((x.ss + fieldOff) ↦₃₂ x.oldVal) ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.payload ++ x.tail) ∗
      A.pool ∗ stackAt s.sp mergeFieldStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      ((x.ss + fieldOff) ↦₃₂ x.val) ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.payload ++ x.tail) x.tail ∗
      A.pool ∗ stackAt s0.sp mergeFieldStackX
  onPanic := Serialization.allocPanic

abbrev mergeField10FieldSpecAtWA (A : RustAlloc) (img : Obj.Image) : Spec MergeFieldU32Ghost :=
  mergeFieldU32FieldSpecAtWA A img 10 0x150#64

abbrev mergeField11FieldSpecAtWA (A : RustAlloc) (img : Obj.Image) : Spec MergeFieldU32Ghost :=
  mergeFieldU32FieldSpecAtWA A img 11 0x154#64

/-- Arbitrary-allocator (`A : RustAlloc`) W-stack spec for `SessionStructure::merge_field` on a
length-delimited `Vec<u8>` field at `tag` and struct byte offset `fieldOff`, carrying `A.pool`. -/
def mergeFieldBytesFieldSpecAtWA (A : RustAlloc) (img : Obj.Image) (tag : Nat)
    (fieldOff : BitVec 64) : Spec MergeFieldBytesGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat ∧
      s.readReg64 .x3 = x.bufRef ∧
      mergeBytes .lengthDelimited (x.payload ++ x.tail) = some (x.bytes, x.tail) ∧
      (x.payload ++ x.tail).length < 2 ^ 62 ∧
      img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      vecU8 A (x.ss + fieldOff) x.oldBytes ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.payload ++ x.tail) ∗
      A.pool ∗ stackAt s.sp mergeFieldStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      vecU8 A (x.ss + fieldOff) x.bytes ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.payload ++ x.tail) x.tail ∗
      A.pool ∗ stackAt s0.sp mergeFieldStackX
  onPanic := Serialization.allocPanic

abbrev mergeField13FieldSpecAtWA (A : RustAlloc) (img : Obj.Image) : Spec MergeFieldBytesGhost :=
  mergeFieldBytesFieldSpecAtWA A img 13 0x60#64

abbrev mergeField15FieldSpecAtWA (A : RustAlloc) (img : Obj.Image) : Spec MergeFieldBytesGhost :=
  mergeFieldBytesFieldSpecAtWA A img 15 0x78#64

private theorem okAtX_of_eq_pre_post_dq5 {α : Type} {b : BitVec 64}
    {ext : String → Option (State → State)} {name : String} {s1 s2 : Spec α}
    (h1 : OkAtX b ext name s1)
    (hpre : ∀ x s, s2.pre x s = s1.pre x s)
    (hpost : ∀ x s0 sf, s1.post x s0 sf = s2.post x s0 sf)
    (hpan : s1.onPanic = s2.onPanic)
    (hex : s1.onExit = s2.onExit)
    (hoom : s1.onOom = s2.onOom) :
    OkAtX b ext name s2 := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hp hal => ?_
  rw [hpre x s0] at hp
  refine h1.mono_outcome x R s0 hpc hrun hp hal fun sf hout => ?_
  rcases hout with ⟨hr, hc, hq⟩ | ⟨hp', hq⟩ | ⟨c, he, hq⟩ | ⟨ho, hq⟩
  · exact Or.inl ⟨hr, hc, hpost x s0 sf ▸ hq⟩
  · exact Or.inr (Or.inl ⟨hp', hpan ▸ hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he, hex ▸ hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom ▸ hq⟩))

/-! ## Decodes, rodata jump table, stack split, and epilogue helpers -/

gen_decodes CryptoVerification.libsignalSessionCode_tree dq5W
  [(ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 108) →
     (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 124),
   (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 208) →
     (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 224),
   (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 876) →
     (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 892),
   (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 920) →
     (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 936)]

private theorem mergeField_fnOff_dq5W :
    CryptoVerification.libsignalSessionCode.fnOff mergeFieldName =
      num% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") :=
  ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>"

abbrev int32MergeRelOff_dq5W : BitVec 64 :=
  bv% ((2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") -
    (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) % 2 ^ 64)

abbrev bytesMergeRelOff_dq5W : BitVec 64 :=
  bv% ((2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
    (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) % 2 ^ 64)

open Lean Elab Tactic in
local elab "dq5W_fetches_range " b:term:max H:term:max kStart:num kEnd:num : tactic => do
  let off ← `(num% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>"))
  let baseOff ← CryptoVerification.CodeLayout.evalNat off "dq5W_fetches_range"
  let mut k := kStart.getNat
  while k <= kEnd.getNat do
    let addrHex := String.ofList (Nat.toDigits 16 (baseOff + k))
    let decId := mkIdent (Name.mkStr4 "Symbolic" "Swarm" "TRREF" "B3DeserQ" |>.str ("dq5W_decode_0x" ++ addrHex))
    let kLit := Syntax.mkNumLit (toString k)
    evalTactic (← `(tactic|
      have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
        (b := $b) (H := $H) (k := $kLit) mergeField_fnOff_dq5W (by decide) $decId))
    k := k + 4

/-- The 4 jump-table bytes for tags 10 (`+9 = 214#8`), 11 (`+10 = 203#8`),
13 (`+12 = 0x0b#8`), and 15 (`+14 = 0x24#8`). -/
def mfRoBytes_dq5_ext (img : Obj.Image) : SepProp :=
  (((mfEntry_identityRootKeys_ext img + 40#64 &&& bv% (2 ^ 64 - 4096)) +
    bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 9 -
      page% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 40))) ↦₈ᵣ 214#8) ∗
  (((mfEntry_identityRootKeys_ext img + 40#64 &&& bv% (2 ^ 64 - 4096)) +
    bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 10 -
      page% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 40))) ↦₈ᵣ 203#8) ∗
  (((mfEntry_identityRootKeys_ext img + 40#64 &&& bv% (2 ^ 64 - 4096)) +
    bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 12 -
      page% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 40))) ↦₈ᵣ 0x0b#8) ∗
  (((mfEntry_identityRootKeys_ext img + 40#64 &&& bv% (2 ^ 64 - 4096)) +
    bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 14 -
      page% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 40))) ↦₈ᵣ 0x24#8)

private theorem mfJumpTable_split_dq5 :
    mfJumpTable_identityRootKeys =
      [0x00#8, 0x82#8, 0x77#8, 0x5f#8, 0x19#8, 0x32#8, 0x8d#8, 0x6d#8, 0xb5#8,
       214#8, 203#8, 0x6d#8, 0x0b#8, 0x4c#8, 0x24#8] := by
  rfl_kernel

theorem rodata_intro_dq5_ext {img : Obj.Image} {m : Memory} {P : SepProp}
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ mfRoBytes_dq5_ext img ∗ P := by
  have hb := base_aligned_of_loads hLoads
  have h := rodata_mfJumpTable_intro_identityRootKeys_ext hLoads hro hP
  rw [mfJumpTable_split_dq5] at h
  simp only [pointsToBytesRO_cons, pointsToBytesRO_nil] at h
  have hadrp := mfEntry_adrp_identityRootKeys_ext img hb
  let jtBase : BitVec 64 := img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d")
  have ha9 : (mfEntry_identityRootKeys_ext img + 40#64 &&& bv% (2 ^ 64 - 4096)) +
      bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 9 -
        page% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 40)) =
      jtBase + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 := by
    dsimp only [jtBase]; rw [hadrp]; bv_omega
  have ha10 : (mfEntry_identityRootKeys_ext img + 40#64 &&& bv% (2 ^ 64 - 4096)) +
      bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 10 -
        page% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 40)) =
      jtBase + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 := by
    dsimp only [jtBase]; rw [hadrp]; bv_omega
  have ha12 : (mfEntry_identityRootKeys_ext img + 40#64 &&& bv% (2 ^ 64 - 4096)) +
      bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 12 -
        page% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 40)) =
      jtBase + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 := by
    dsimp only [jtBase]; rw [hadrp]; bv_omega
  have ha14 : (mfEntry_identityRootKeys_ext img + 40#64 &&& bv% (2 ^ 64 - 4096)) +
      bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 14 -
        page% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 40)) =
      jtBase + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 := by
    dsimp only [jtBase]; rw [hadrp]; bv_omega
  have h' : m ⊨
      (((jtBase) ↦₈ᵣ 0x00#8) ∗
       ((jtBase + 1#64) ↦₈ᵣ 0x82#8) ∗
       ((jtBase + 1#64 + 1#64) ↦₈ᵣ 0x77#8) ∗
       ((jtBase + 1#64 + 1#64 + 1#64) ↦₈ᵣ 0x5f#8) ∗
       ((jtBase + 1#64 + 1#64 + 1#64 + 1#64) ↦₈ᵣ 0x19#8) ∗
       ((jtBase + 1#64 + 1#64 + 1#64 + 1#64 + 1#64) ↦₈ᵣ 0x32#8) ∗
       ((jtBase + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64) ↦₈ᵣ 0x8d#8) ∗
       ((jtBase + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64) ↦₈ᵣ 0x6d#8) ∗
       ((jtBase + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64) ↦₈ᵣ 0xb5#8) ∗
       ((jtBase + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64) ↦₈ᵣ 0x6d#8) ∗
       ((jtBase + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64) ↦₈ᵣ 0x4c#8) ∗
       emp) ∗
      (mfRoBytes_dq5_ext img ∗ P) := by
    dsimp only [mfRoBytes_dq5_ext]
    rw [ha9, ha10, ha12, ha14]
    dsimp only [jtBase]
    convert h using 1; ac_rfl
  exact Satisfies.of_sep_right h'

theorem int32Merge_fnAddr_eq_dq5_ext (img : Obj.Image)
    {ext : String → Option (State → State)} :
    mfEntry_identityRootKeys_ext img + int32MergeRelOff_dq5W =
      (SP2Ext img.base ext).fnAddr Prost.int32MergeName := by
  unfold mfEntry_identityRootKeys_ext int32MergeRelOff_dq5W
  dsimp only [SP2Ext]
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>")]
  bv_omega

theorem bytesMerge_fnAddr_eq_dq5_ext (img : Obj.Image)
    {ext : String → Option (State → State)} :
    mfEntry_identityRootKeys_ext img + bytesMergeRelOff_dq5W =
      (SP2Ext img.base ext).fnAddr Prost.bytesMergeName := by
  unfold mfEntry_identityRootKeys_ext bytesMergeRelOff_dq5W
  dsimp only [SP2Ext]
  rw [Program.fnAddr_rebase,
    (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")]
  bv_omega

theorem stackAt_bytesMergeW_eq_int32MergeW (sp : BitVec 64) :
    stackAt sp Prost.X.bytesMergeStackW =
      memRegion (sp - 24880#64) 144 ∗ stackAt sp Prost.X.int32MergeStackW :=
  ProofLib.stackAt_split_bottom sp Prost.X.int32MergeStackW 144 (by decide)

theorem step_cbz_epilogue_dq5_ext (img : Obj.Image)
    (ext : String → Option (State → State))
    (retOff w56 : BitVec 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hret : retOff = 936#64 ∨ retOff = 892#64 ∨ retOff = 124#64 ∨ retOff = 224#64)
    (hpc : s.pc = mfEntry_identityRootKeys_ext img + retOff)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 240#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = s0.sp →
      sf.trace = s0.trace →
      sf.readReg64 .x0 = 0#64 →
      CalleeSavedPreserved s0 sf →
      Q sf (mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗ F)) :
    SepWPp (SP2Ext img.base ext) (s0.readReg64 .lr) s P Q Qp := by
  let H := Rust.withPanics ext
  dq5W_fetches_range img.base H 936 936
  dq5W_fetches_range img.base H 892 892
  dq5W_fetches_range img.base H 124 124
  dq5W_fetches_range img.base H 224 224
  change SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s P Q Qp
  rw [fnAddr_mergeField_eq_mfEntry_identityRootKeys_ext img H] at *
  examples_hide_fetches
  apply ProofLib.SepWPp.of_sepWP (mid := mfEntry_identityRootKeys_ext img + 1880#64)
  rcases hret with rfl | rfl | rfl | rfl
  · wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    exact step_epilogue_758_identityRootKeys_ext img ext w56
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      halign (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) hP hnext
  · wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    exact step_epilogue_758_identityRootKeys_ext img ext w56
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      halign (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) hP hnext
  · wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    exact step_epilogue_758_identityRootKeys_ext img ext w56
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      halign (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) hP hnext
  · wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    exact step_epilogue_758_identityRootKeys_ext img ext w56
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      halign (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) hP hnext

/-! ## Unified proof for `Vec<u8>` fields (tags 13 and 15) -/

private theorem finish_post_bytes_field_extWA {A : RustAlloc} (img : Obj.Image) (tag : Nat)
    (fieldOff w56 : BitVec 64) (x : MergeFieldBytesGhost)
    {s0 sf : State} {R : SepProp}
    (htrf : sf.trace = s0.trace)
    (hx0f : sf.readReg64 .x0 = 0#64)
    (hmf : sf.mem ⊨
      (mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗
        ((x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
          stackAt (s0.sp - 240#64) Prost.X.bytesMergeStackW ∗
          vecU8 A (x.ss + fieldOff) x.bytes ∗
          Prost.sliceCursorAfter x.slot x.ptr (x.payload ++ x.tail) x.tail ∗
          (mfUnusedStack_identityRootKeys_extW s0.sp ∗ mfRoBytes_dq5_ext img))) ∗ R) :
    sf.mem ⊨ (mergeFieldBytesFieldSpecAtWA A img tag fieldOff).post x s0 sf ∗ R := by
  have h1 : sf.mem ⊨ mfRoBytes_dq5_ext img ∗
      ((mfUnusedStack_identityRootKeys_extW s0.sp ∗ stackAt (s0.sp - 240#64) Prost.X.bytesMergeStackW ∗
          mfSavedRegs_identityRootKeys s0.sp s0 w56) ∗
        (vecU8 A (x.ss + fieldOff) x.bytes ∗
          (x.bufRef ↦₆₄ x.slot) ∗
          Prost.sliceCursorAfter x.slot x.ptr (x.payload ++ x.tail) x.tail ∗
          A.pool ∗ R)) := by
    convert hmf using 1; ac_rfl
  have h2 := Satisfies.of_sep_right h1
  have h3 := Satisfies.mono
    (sepConj_mono_left (stackAt_mergeField_unsplit_identityRootKeys_extW s0.sp s0 w56)) h2
  dsimp only [mergeFieldBytesFieldSpecAtWA]
  rw [pure_true_emp_identityRootKeys ⟨htrf, hx0f⟩, emp_sepConj]
  convert h3 using 1; ac_rfl

private theorem step_bytesMerge_call_field_extWA {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State)) (hbytes : Prost.X.BytesMergeOkW img A ext)
    (tag : Nat) (fieldOff retOff w56 : BitVec 64) (x : MergeFieldBytesGhost)
    {s0 sm : State} {R : SepProp} (hret : retOff = 124#64 ∨ retOff = 224#64)
    (hpcm : sm.pc = mfEntry_identityRootKeys_ext img + bytesMergeRelOff_dq5W)
    (hrunm : sm.status = .Running) (hspm : sm.sp = s0.sp - 240#64)
    (halign : s0.sp &&& 15#64 = 0#64) (hFm : img.FrozenLoaded sm) (hsymm : sm.symtab = img.symtab)
    (htrm : sm.trace = s0.trace) (hlrm : sm.readReg64 .lr = mfEntry_identityRootKeys_ext img + retOff)
    (hx0m : (sm.readReg64 .x0).setWidth 8 = 2#8) (hx1m : sm.readReg64 .x1 = x.ss + fieldOff)
    (hx2m : sm.readReg64 .x2 = x.bufRef) (hx26m : sm.readReg64 .x26 = s0.readReg64 .x26)
    (hx27m : sm.readReg64 .x27 = s0.readReg64 .x27) (hx28m : sm.readReg64 .x28 = s0.readReg64 .x28)
    (hvm : calleeSavedVRegs sm = calleeSavedVRegs s0)
    (hmerge : mergeBytes .lengthDelimited (x.payload ++ x.tail) = some (x.bytes, x.tail))
    (hlen : (x.payload ++ x.tail).length < 2 ^ 62) :
    SepWPp (SP2Ext img.base ext) (s0.readReg64 .lr) sm
      (vecU8 A (x.ss + fieldOff) x.oldBytes ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAt x.slot x.ptr (x.payload ++ x.tail) ∗
        A.pool ∗ stackAt (s0.sp - 240#64) Prost.X.bytesMergeStackW ∗
        mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗
        (mfUnusedStack_identityRootKeys_extW s0.sp ∗ mfRoBytes_dq5_ext img))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (mergeFieldBytesFieldSpecAtWA A img tag fieldOff).post x s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s0 sf ∗ R)) := by
  have hcall : subroutine_ok (SP2Ext img.base ext)
      (mfEntry_identityRootKeys_ext img + bytesMergeRelOff_dq5W) (Prost.X.bytesMergeSpecW A img) := by
    rw [bytesMerge_fnAddr_eq_dq5_ext img (ext := ext)]
    exact hbytes
  have hspm_align : sm.spAligned = true := by
    simp only [State.spAligned, hspm, sp_sub_240_aligned_identityRootKeys halign, beq_self_eq_true]
  unfold vecU8
  simp only [sepExists_sepConj_left]
  refine ProofLib.SepWPp.exists_elim (fun cap0 => ProofLib.SepWPp.exists_elim (fun ptr0 => ?_))
  let g : Prost.BytesMergeGhost :=
    ⟨.lengthDelimited, x.ss + fieldOff, cap0, ptr0, x.oldBytes, x.bufRef, x.slot, x.ptr,
     x.payload ++ x.tail⟩
  refine ProofLib.SepWPp.call (x := g)
    (F := mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗
      (mfUnusedStack_identityRootKeys_extW s0.sp ∗ mfRoBytes_dq5_ext img))
    hcall hpcm hrunm hspm_align hlrm ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [Prost.X.bytesMergeSpecW, Spec.inImage, Prost.X.bytesMergeRawSpecW, g]
    have hp1 : img.FrozenLoaded sm ∧ sm.symtab = img.symtab := ⟨hFm, hsymm⟩
    have hp2 : (sm.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat ∧
        sm.readReg64 .x1 = x.ss + fieldOff ∧ sm.readReg64 .x2 = x.bufRef ∧
        (x.payload ++ x.tail).length < 2 ^ 62 :=
      ⟨hx0m, hx1m, hx2m, hlen⟩
    rw [hspm, pure_true_emp_identityRootKeys hp1, pure_true_emp_identityRootKeys hp2, emp_sepConj, emp_sepConj]
    convert hm using 1; ac_rfl
  · intro sf code R' _ hex
    exact allowPanic_not_exited hex
  · intro sf _ hm
    dsimp only [Prost.X.bytesMergeSpecW, Spec.inImage, Prost.X.bytesMergeRawSpecW,
      Serialization.allocPanic] at hm ⊢
    refine allowPanic_frame (fun ⟨ha, hp⟩ => ?_) hm
    rw [allocFailedIn, htrm] at ha
    rw [htrm] at hp
    exact ⟨ha, hp⟩
  · intro s2 hpc2 hrun2 hsp2 hcs2
    dsimp only [Prost.X.bytesMergeSpecW, Spec.inImage, Prost.X.bytesMergeRawSpecW, g]
    rw [hmerge]
    dsimp only
    rw [sepConj_assoc]
    refine ProofLib.SepWPp.pure_left (fun htr2 => ?_)
    rw [hspm]
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine ProofLib.SepWPp.pure_left (fun hx0_2 => ?_)
    have hvec : (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64, vecU8At A (x.ss + fieldOff) cap' ptr' x.bytes) =
        vecU8 A (x.ss + fieldOff) x.bytes := rfl
    rw [hvec]
    refine step_cbz_epilogue_dq5_ext img ext retOff w56
      (F := (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
        stackAt (s0.sp - 240#64) Prost.X.bytesMergeStackW ∗
        vecU8 A (x.ss + fieldOff) x.bytes ∗
        Prost.sliceCursorAfter x.slot x.ptr (x.payload ++ x.tail) x.tail ∗
        (mfUnusedStack_identityRootKeys_extW s0.sp ∗ mfRoBytes_dq5_ext img))
      (Or.inr (Or.inr hret)) hpc2 hrun2
      (hsp2.trans hspm) halign (htr2.trans htrm) hx0_2
      (hcs2.2.2.2.2.2.2.2.1.trans hx26m)
      (hcs2.2.2.2.2.2.2.2.2.1.trans hx27m)
      (hcs2.2.2.2.2.2.2.2.2.2.1.trans hx28m)
      ((CalleeSavedPreserved.vregs hcs2).trans hvm)
      (by ac_rfl) ?_
    intro sf _ _ hspf htrf hx0f hcsf
    exact ⟨finish_post_bytes_field_extWA img tag fieldOff w56 x htrf hx0f, hspf, hcsf⟩

theorem mergeFieldBytesField_ok_extWA (img : Obj.Image)
    {A : RustAlloc} {ext : String → Option (State → State)}
    {tag : Nat} {fieldOff : BitVec 64}
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hbytes : Prost.X.BytesMergeOkW img A ext)
    (h_case : (tag = 13 ∧ fieldOff = 0x60#64) ∨ (tag = 15 ∧ fieldOff = 0x78#64)) :
    OkAtX img.base ext mergeFieldName (mergeFieldBytesFieldSpecAtWA A img tag fieldOff) := by
  unfold OkAtX
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp_align
  dsimp only [mergeFieldBytesFieldSpecAtWA] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hmerge, hlen, hF, hsym⟩, hmem⟩
  have hmem_ro : s0.mem ⊨
      (mfRoBytes_dq5_ext img ∗ vecU8 A (x.ss + fieldOff) x.oldBytes ∗ (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAt x.slot x.ptr (x.payload ++ x.tail) ∗
        A.pool ∗ stackAt s0.sp mergeFieldStackX) ∗ R := by
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
    exact rodata_intro_dq5_ext hLoads hF.roData (by convert hmem using 1; ac_rfl)
  refine ⟨mfRoBytes_dq5_ext img ∗ vecU8 A (x.ss + fieldOff) x.oldBytes ∗ (x.bufRef ↦₆₄ x.slot) ∗
    Prost.sliceCursorAt x.slot x.ptr (x.payload ++ x.tail) ∗ A.pool ∗ stackAt s0.sp mergeFieldStackX,
    R, hmem_ro, ?_⟩
  rw [stackAt_mergeField_split_identityRootKeys_extW s0.sp]
  unfold mfRoBytes_dq5_ext
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine ProofLib.SepWPp.exists_elim (fun w80 => ProofLib.SepWPp.exists_elim (fun w72 =>
    ProofLib.SepWPp.exists_elim (fun w64 => ProofLib.SepWPp.exists_elim (fun w56 =>
      ProofLib.SepWPp.exists_elim (fun w48 => ProofLib.SepWPp.exists_elim (fun w40 =>
        ProofLib.SepWPp.exists_elim (fun w32 => ProofLib.SepWPp.exists_elim (fun w24 =>
          ProofLib.SepWPp.exists_elim (fun w16 => ProofLib.SepWPp.exists_elim (fun w8 => ?_))))))))))
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned] using hsp_align
  have hsp_align240 := sp_sub_240_aligned_identityRootKeys halign
  let H := Rust.withPanics ext
  mf234_fetches img.base H
  dq5W_fetches_range img.base H 108 120
  dq5W_fetches_range img.base H 208 220
  dsimp only [SP2Ext, contractProg] at hpc
  rw [fnAddr_mergeField_eq_mfEntry_identityRootKeys_ext img H] at *
  examples_hide_fetches
  rcases h_case with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [arm64_norm] at hx0 hx1 hx2 hx3
    change SepWPp (libsignalSessionCode.rebase img.base H) _ _ _ _ _
    refine of_sepWP_inImage_identityRootKeys hF hsym
      (mid := mfEntry_identityRootKeys_ext img + bytesMergeRelOff_dq5W) ?_
    iterate 20 wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    intro hFm hsymm
    refine ProofLib.SepWPp.congr_pre ?_
      (step_bytesMerge_call_field_extWA img ext hbytes 13 0x60#64 124#64 w56 x
        (Or.inl rfl)
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        halign hFm hsymm (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm])
        hmerge hlen)
    unfold mfSavedRegs_identityRootKeys mfRoBytes_dq5_ext
    simp only [Reg.x29, Reg.x30, Reg.x25, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]
    ac_rfl
  · simp only [arm64_norm] at hx0 hx1 hx2 hx3
    change SepWPp (libsignalSessionCode.rebase img.base H) _ _ _ _ _
    refine of_sepWP_inImage_identityRootKeys hF hsym
      (mid := mfEntry_identityRootKeys_ext img + bytesMergeRelOff_dq5W) ?_
    iterate 20 wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    intro hFm hsymm
    refine ProofLib.SepWPp.congr_pre ?_
      (step_bytesMerge_call_field_extWA img ext hbytes 15 0x78#64 224#64 w56 x
        (Or.inr rfl)
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        halign hFm hsymm (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm])
        hmerge hlen)
    unfold mfSavedRegs_identityRootKeys mfRoBytes_dq5_ext
    simp only [Reg.x29, Reg.x30, Reg.x25, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]
    ac_rfl

theorem mergeFieldBytesField_ok_extW (img : Obj.Image)
    {ext : String → Option (State → State)} {tag : Nat} {fieldOff : BitVec 64}
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hbytes : Prost.X.BytesMergeOkW img A0 ext)
    (h_case : (tag = 13 ∧ fieldOff = 0x60#64) ∨ (tag = 15 ∧ fieldOff = 0x78#64)) :
    OkAtX img.base ext mergeFieldName (mergeFieldBytesFieldSpecAtW img tag fieldOff) :=
  okAtX_of_eq_pre_post_dq5 (mergeFieldBytesField_ok_extWA img hLoads hbytes h_case)
    (fun _ _ => by
      dsimp only [mergeFieldBytesFieldSpecAtWA, mergeFieldBytesFieldSpecAtW]
      rw [show A0.pool = emp from rfl]; ac_rfl)
    (fun _ _ _ => by
      dsimp only [mergeFieldBytesFieldSpecAtWA, mergeFieldBytesFieldSpecAtW]
      rw [show A0.pool = emp from rfl]; ac_rfl)
    rfl rfl rfl

/-! ## Unified proof for `uint32` fields (tags 10 and 11) -/

private theorem finish_post_u32_field_extWA {A : RustAlloc} (img : Obj.Image) (tag : Nat)
    (fieldOff w56 : BitVec 64) (x : MergeFieldU32Ghost)
    {s0 sf : State} {R : SepProp}
    (htrf : sf.trace = s0.trace)
    (hx0f : sf.readReg64 .x0 = 0#64)
    (hmf : sf.mem ⊨
      (mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗
        ((x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
          (memRegion (s0.sp - 240#64 - 24880#64) 144 ∗
            stackAt (s0.sp - 240#64) Prost.X.int32MergeStackW) ∗
          ((x.ss + fieldOff) ↦₃₂ x.val) ∗
          Prost.sliceCursorAfter x.slot x.ptr (x.payload ++ x.tail) x.tail ∗
          (mfUnusedStack_identityRootKeys_extW s0.sp ∗ mfRoBytes_dq5_ext img))) ∗ R) :
    sf.mem ⊨ (mergeFieldU32FieldSpecAtWA A img tag fieldOff).post x s0 sf ∗ R := by
  rw [← stackAt_bytesMergeW_eq_int32MergeW (s0.sp - 240#64)] at hmf
  have h1 : sf.mem ⊨ mfRoBytes_dq5_ext img ∗
      ((mfUnusedStack_identityRootKeys_extW s0.sp ∗ stackAt (s0.sp - 240#64) Prost.X.bytesMergeStackW ∗
          mfSavedRegs_identityRootKeys s0.sp s0 w56) ∗
        (((x.ss + fieldOff) ↦₃₂ x.val) ∗
          (x.bufRef ↦₆₄ x.slot) ∗
          Prost.sliceCursorAfter x.slot x.ptr (x.payload ++ x.tail) x.tail ∗
          A.pool ∗ R)) := by
    convert hmf using 1; ac_rfl
  have h2 := Satisfies.of_sep_right h1
  have h3 := Satisfies.mono
    (sepConj_mono_left (stackAt_mergeField_unsplit_identityRootKeys_extW s0.sp s0 w56)) h2
  dsimp only [mergeFieldU32FieldSpecAtWA]
  rw [pure_true_emp_identityRootKeys ⟨htrf, hx0f⟩, emp_sepConj]
  convert h3 using 1; ac_rfl

private theorem step_int32Merge_call_field_extWA {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State)) (hint32 : Prost.X.Int32MergeOkW img A ext)
    (tag : Nat) (fieldOff retOff w56 : BitVec 64) (x : MergeFieldU32Ghost)
    {s0 sm : State} {R : SepProp} (hret : retOff = 936#64 ∨ retOff = 892#64)
    (hpcm : sm.pc = mfEntry_identityRootKeys_ext img + int32MergeRelOff_dq5W)
    (hrunm : sm.status = .Running) (hspm : sm.sp = s0.sp - 240#64)
    (halign : s0.sp &&& 15#64 = 0#64) (hFm : img.FrozenLoaded sm) (hsymm : sm.symtab = img.symtab)
    (htrm : sm.trace = s0.trace) (hlrm : sm.readReg64 .lr = mfEntry_identityRootKeys_ext img + retOff)
    (hx0m : (sm.readReg64 .x0).setWidth 8 = 0#8) (hx1m : sm.readReg64 .x1 = x.ss + fieldOff)
    (hx2m : sm.readReg64 .x2 = x.bufRef) (hx26m : sm.readReg64 .x26 = s0.readReg64 .x26)
    (hx27m : sm.readReg64 .x27 = s0.readReg64 .x27) (hx28m : sm.readReg64 .x28 = s0.readReg64 .x28)
    (hvm : calleeSavedVRegs sm = calleeSavedVRegs s0)
    (hmerge : mergeUint32 .varint (x.payload ++ x.tail) = some (x.val, x.tail))
    (hlen : (x.payload ++ x.tail).length < 2 ^ 62) :
    SepWPp (SP2Ext img.base ext) (s0.readReg64 .lr) sm
      (((x.ss + fieldOff) ↦₃₂ x.oldVal) ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAt x.slot x.ptr (x.payload ++ x.tail) ∗
        A.pool ∗ stackAt (s0.sp - 240#64) Prost.X.bytesMergeStackW ∗
        mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗
        (mfUnusedStack_identityRootKeys_extW s0.sp ∗ mfRoBytes_dq5_ext img))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (mergeFieldU32FieldSpecAtWA A img tag fieldOff).post x s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s0 sf ∗ R)) := by
  have hcall : subroutine_ok (SP2Ext img.base ext)
      (mfEntry_identityRootKeys_ext img + int32MergeRelOff_dq5W)
      ((Prost.X.int32MergeSpecW A).inImage img) := by
    rw [int32Merge_fnAddr_eq_dq5_ext img (ext := ext)]
    exact hint32
  have hspm_align : sm.spAligned = true := by
    simp only [State.spAligned, hspm, sp_sub_240_aligned_identityRootKeys halign, beq_self_eq_true]
  let g : Prost.Int32MergeGhost :=
    ⟨.varint, x.ss + fieldOff, x.bufRef, x.slot, x.ptr, x.payload ++ x.tail⟩
  refine ProofLib.SepWPp.call (x := g)
    (F := memRegion (s0.sp - 240#64 - 24880#64) 144 ∗
      mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗
      (mfUnusedStack_identityRootKeys_extW s0.sp ∗ mfRoBytes_dq5_ext img))
    hcall hpcm hrunm hspm_align hlrm ?_ ?_ ?_ ?_
  · intro R' hm
    rw [stackAt_bytesMergeW_eq_int32MergeW (s0.sp - 240#64)] at hm
    have hcell : ((x.ss + fieldOff) ↦₃₂ x.oldVal) ⊢ memRegion (x.ss + fieldOff) 4 := by
      rw [ProofLib.memRegion_four]
      exact Entails.sepExists_right x.oldVal (Entails.refl _)
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left hcell)) hm
    dsimp only [Spec.inImage, Prost.X.int32MergeSpecW, g]
    have hp1 : img.FrozenLoaded sm ∧ sm.symtab = img.symtab := ⟨hFm, hsymm⟩
    have hlen63 : (x.payload ++ x.tail).length < 2 ^ 63 :=
      Nat.lt_trans hlen (by decide)
    have hp2 : (sm.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 WireType.varint.toNat ∧
        sm.readReg64 .x1 = x.ss + fieldOff ∧ sm.readReg64 .x2 = x.bufRef ∧
        (x.payload ++ x.tail).length < 2 ^ 63 :=
      ⟨hx0m, hx1m, hx2m, hlen63⟩
    rw [hspm, pure_true_emp_identityRootKeys hp1, pure_true_emp_identityRootKeys hp2, emp_sepConj, emp_sepConj]
    convert hm1 using 1; ac_rfl
  · intro sf code R' _ hex
    exact allowPanic_not_exited hex
  · intro sf _ hm
    dsimp only [Spec.inImage, Prost.X.int32MergeSpecW, Serialization.allocPanic] at hm ⊢
    refine allowPanic_frame (fun ⟨ha, hp⟩ => ?_) hm
    rw [allocFailedIn, htrm] at ha
    rw [htrm] at hp
    exact ⟨ha, hp⟩
  · intro s2 hpc2 hrun2 hsp2 hcs2
    dsimp only [Spec.inImage, Prost.X.int32MergeSpecW, g]
    rw [hmerge]
    dsimp only
    rw [sepConj_assoc]
    refine ProofLib.SepWPp.pure_left (fun htr2 => ?_)
    rw [hspm]
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine ProofLib.SepWPp.pure_left (fun hx0_2 => ?_)
    have hret_all : retOff = 936#64 ∨ retOff = 892#64 ∨ retOff = 124#64 ∨ retOff = 224#64 := by
      rcases hret with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    refine step_cbz_epilogue_dq5_ext img ext retOff w56
      (F := (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
        (memRegion (s0.sp - 240#64 - 24880#64) 144 ∗
          stackAt (s0.sp - 240#64) Prost.X.int32MergeStackW) ∗
        ((x.ss + fieldOff) ↦₃₂ x.val) ∗
        Prost.sliceCursorAfter x.slot x.ptr (x.payload ++ x.tail) x.tail ∗
        (mfUnusedStack_identityRootKeys_extW s0.sp ∗ mfRoBytes_dq5_ext img))
      hret_all hpc2 hrun2
      (hsp2.trans hspm) halign (htr2.trans htrm) hx0_2
      (hcs2.2.2.2.2.2.2.2.1.trans hx26m)
      (hcs2.2.2.2.2.2.2.2.2.1.trans hx27m)
      (hcs2.2.2.2.2.2.2.2.2.2.1.trans hx28m)
      ((CalleeSavedPreserved.vregs hcs2).trans hvm)
      (by ac_rfl) ?_
    intro sf _ _ hspf htrf hx0f hcsf
    exact ⟨finish_post_u32_field_extWA img tag fieldOff w56 x htrf hx0f, hspf, hcsf⟩

theorem mergeFieldU32Field_ok_extWA (img : Obj.Image)
    {A : RustAlloc} {ext : String → Option (State → State)}
    {tag : Nat} {fieldOff : BitVec 64}
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hint32 : Prost.X.Int32MergeOkW img A ext)
    (h_case : (tag = 10 ∧ fieldOff = 0x150#64) ∨ (tag = 11 ∧ fieldOff = 0x154#64)) :
    OkAtX img.base ext mergeFieldName (mergeFieldU32FieldSpecAtWA A img tag fieldOff) := by
  unfold OkAtX
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp_align
  dsimp only [mergeFieldU32FieldSpecAtWA] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hmerge, hlen, hF, hsym⟩, hmem⟩
  have hmem_ro : s0.mem ⊨
      (mfRoBytes_dq5_ext img ∗ ((x.ss + fieldOff) ↦₃₂ x.oldVal) ∗ (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAt x.slot x.ptr (x.payload ++ x.tail) ∗
        A.pool ∗ stackAt s0.sp mergeFieldStackX) ∗ R := by
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
    exact rodata_intro_dq5_ext hLoads hF.roData (by convert hmem using 1; ac_rfl)
  refine ⟨mfRoBytes_dq5_ext img ∗ ((x.ss + fieldOff) ↦₃₂ x.oldVal) ∗ (x.bufRef ↦₆₄ x.slot) ∗
    Prost.sliceCursorAt x.slot x.ptr (x.payload ++ x.tail) ∗ A.pool ∗ stackAt s0.sp mergeFieldStackX,
    R, hmem_ro, ?_⟩
  rw [stackAt_mergeField_split_identityRootKeys_extW s0.sp]
  unfold mfRoBytes_dq5_ext
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine ProofLib.SepWPp.exists_elim (fun w80 => ProofLib.SepWPp.exists_elim (fun w72 =>
    ProofLib.SepWPp.exists_elim (fun w64 => ProofLib.SepWPp.exists_elim (fun w56 =>
      ProofLib.SepWPp.exists_elim (fun w48 => ProofLib.SepWPp.exists_elim (fun w40 =>
        ProofLib.SepWPp.exists_elim (fun w32 => ProofLib.SepWPp.exists_elim (fun w24 =>
          ProofLib.SepWPp.exists_elim (fun w16 => ProofLib.SepWPp.exists_elim (fun w8 => ?_))))))))))
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned] using hsp_align
  have hsp_align240 := sp_sub_240_aligned_identityRootKeys halign
  let H := Rust.withPanics ext
  mf234_fetches img.base H
  dq5W_fetches_range img.base H 920 932
  dq5W_fetches_range img.base H 876 888
  dsimp only [SP2Ext, contractProg] at hpc
  rw [fnAddr_mergeField_eq_mfEntry_identityRootKeys_ext img H] at *
  examples_hide_fetches
  rcases h_case with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [arm64_norm] at hx0 hx1 hx2 hx3
    change SepWPp (libsignalSessionCode.rebase img.base H) _ _ _ _ _
    refine of_sepWP_inImage_identityRootKeys hF hsym
      (mid := mfEntry_identityRootKeys_ext img + int32MergeRelOff_dq5W) ?_
    iterate 20 wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    intro hFm hsymm
    refine ProofLib.SepWPp.congr_pre ?_
      (step_int32Merge_call_field_extWA img ext hint32 10 0x150#64 936#64 w56 x
        (Or.inl rfl)
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        halign hFm hsymm (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm])
        hmerge hlen)
    unfold mfSavedRegs_identityRootKeys mfRoBytes_dq5_ext
    simp only [Reg.x29, Reg.x30, Reg.x25, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]
    ac_rfl
  · simp only [arm64_norm] at hx0 hx1 hx2 hx3
    change SepWPp (libsignalSessionCode.rebase img.base H) _ _ _ _ _
    refine of_sepWP_inImage_identityRootKeys hF hsym
      (mid := mfEntry_identityRootKeys_ext img + int32MergeRelOff_dq5W) ?_
    iterate 20 wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    intro hFm hsymm
    refine ProofLib.SepWPp.congr_pre ?_
      (step_int32Merge_call_field_extWA img ext hint32 11 0x154#64 892#64 w56 x
        (Or.inr rfl)
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        halign hFm hsymm (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm])
        hmerge hlen)
    unfold mfSavedRegs_identityRootKeys mfRoBytes_dq5_ext
    simp only [Reg.x29, Reg.x30, Reg.x25, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]
    ac_rfl

theorem mergeFieldU32Field_ok_extW (img : Obj.Image)
    {ext : String → Option (State → State)} {tag : Nat} {fieldOff : BitVec 64}
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hint32 : Prost.X.Int32MergeOkW img A0 ext)
    (h_case : (tag = 10 ∧ fieldOff = 0x150#64) ∨ (tag = 11 ∧ fieldOff = 0x154#64)) :
    OkAtX img.base ext mergeFieldName (mergeFieldU32FieldSpecAtW img tag fieldOff) :=
  okAtX_of_eq_pre_post_dq5 (mergeFieldU32Field_ok_extWA img hLoads hint32 h_case)
    (fun _ _ => by
      dsimp only [mergeFieldU32FieldSpecAtWA, mergeFieldU32FieldSpecAtW]
      rw [show A0.pool = emp from rfl]; ac_rfl)
    (fun _ _ _ => by
      dsimp only [mergeFieldU32FieldSpecAtWA, mergeFieldU32FieldSpecAtW]
      rw [show A0.pool = emp from rfl]; ac_rfl)
    rfl rfl rfl

/-! ## Standalone leaf theorems on `SP2Ext` -/

theorem mergeField10Field_ok_extWA (img : Obj.Image)
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hint32 : Prost.X.Int32MergeOkW img A ext) :
    OkAtX img.base ext mergeFieldName (mergeField10FieldSpecAtWA A img) :=
  mergeFieldU32Field_ok_extWA img hLoads hint32 (Or.inl ⟨rfl, rfl⟩)

theorem mergeField11Field_ok_extWA (img : Obj.Image)
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hint32 : Prost.X.Int32MergeOkW img A ext) :
    OkAtX img.base ext mergeFieldName (mergeField11FieldSpecAtWA A img) :=
  mergeFieldU32Field_ok_extWA img hLoads hint32 (Or.inr ⟨rfl, rfl⟩)

theorem mergeField13Field_ok_extWA (img : Obj.Image)
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hbytes : Prost.X.BytesMergeOkW img A ext) :
    OkAtX img.base ext mergeFieldName (mergeField13FieldSpecAtWA A img) :=
  mergeFieldBytesField_ok_extWA img hLoads hbytes (Or.inl ⟨rfl, rfl⟩)

theorem mergeField15Field_ok_extWA (img : Obj.Image)
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hbytes : Prost.X.BytesMergeOkW img A ext) :
    OkAtX img.base ext mergeFieldName (mergeField15FieldSpecAtWA A img) :=
  mergeFieldBytesField_ok_extWA img hLoads hbytes (Or.inr ⟨rfl, rfl⟩)

/-- Tag 10 (`remote_registration_id`, `ss + 0x150#64`) standalone field leaf on `SP2Ext img.base ext`
(defeq `contractProg img.base ext`). -/
theorem mergeField10Field_ok_extW (img : Obj.Image)
    {ext : String → Option (State → State)}
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hint32 : Prost.X.Int32MergeOkW img A0 ext) :
    OkAtX img.base ext mergeFieldName (mergeField10FieldSpecAtW img) :=
  mergeFieldU32Field_ok_extW img hLoads hint32 (Or.inl ⟨rfl, rfl⟩)

/-- Tag 11 (`local_registration_id`, `ss + 0x154#64`) standalone field leaf on `SP2Ext img.base ext`
(defeq `contractProg img.base ext`). -/
theorem mergeField11Field_ok_extW (img : Obj.Image)
    {ext : String → Option (State → State)}
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hint32 : Prost.X.Int32MergeOkW img A0 ext) :
    OkAtX img.base ext mergeFieldName (mergeField11FieldSpecAtW img) :=
  mergeFieldU32Field_ok_extW img hLoads hint32 (Or.inr ⟨rfl, rfl⟩)

/-- Tag 13 (`alice_base_key`, `ss + 0x60#64`) standalone field leaf on `SP2Ext img.base ext`
(defeq `contractProg img.base ext`). -/
theorem mergeField13Field_ok_extW (img : Obj.Image)
    {ext : String → Option (State → State)}
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hbytes : Prost.X.BytesMergeOkW img A0 ext) :
    OkAtX img.base ext mergeFieldName (mergeField13FieldSpecAtW img) :=
  mergeFieldBytesField_ok_extW img hLoads hbytes (Or.inl ⟨rfl, rfl⟩)

/-- Tag 15 (`pq_ratchet_state`, `ss + 0x78#64`) standalone field leaf on `SP2Ext img.base ext`
(defeq `contractProg img.base ext`), with REPLACE (`last-wins`) semantics and `< 2 ^ 62` length bound. -/
theorem mergeField15Field_ok_extW (img : Obj.Image)
    {ext : String → Option (State → State)}
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hbytes : Prost.X.BytesMergeOkW img A0 ext) :
    OkAtX img.base ext mergeFieldName (mergeField15FieldSpecAtW img) :=
  mergeFieldBytesField_ok_extW img hLoads hbytes (Or.inr ⟨rfl, rfl⟩)

/-! ## Framing combinator and `SSGX` leaf corollaries -/

/-- General framing combinator lifting a standalone single-field `OkAtX` contract to a full-struct
`Spec` with `Serialization.allocPanic` by placing the untouched struct fields in the frame `F`. -/
theorem okAtX_of_imp_frame {α β : Type} {b : BitVec 64} {ext : String → Option (State → State)}
    {name : String} {specField : Spec α} {specFull : Spec β}
    (hField : OkAtX b ext name specField)
    (h_exit : ∀ (g : α) (code : BitVec 64) (s0 sf : State),
      specField.onExit g code s0 sf = ⌜False⌝)
    (h_panic : ∀ (g : α) (x : β) (s0 sf : State) (F R : SepProp),
      (sf.mem ⊨ specField.onPanic g s0 sf ∗ (F ∗ R)) →
      (sf.mem ⊨ specFull.onPanic x s0 sf ∗ R))
    (h_step : ∀ (x : β) (s0 : State) (R : SepProp),
      (s0.mem ⊨ specFull.pre x s0 ∗ R) →
      ∃ (g : α) (F : SepProp),
        (s0.mem ⊨ specField.pre g s0 ∗ (F ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ specField.post g s0 sf ∗ (F ∗ R)) →
          (sf.mem ⊨ specFull.post x s0 sf ∗ R)))
    (h_oom : ∀ (g : α) (s0 sf : State), specField.onOom g s0 sf = ⌜False⌝ := by intros; rfl) :
    OkAtX b ext name specFull := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  obtain ⟨g, F, hpre', hpost_imp⟩ := h_step x s0 R hpre
  refine hField.mono_outcome g (F ∗ R) s0 hpc hrun hpre' hal fun sf h_out => ?_
  rcases h_out with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpanic⟩ | ⟨code, _, hexit⟩ | ⟨_, hoom⟩
  · exact Or.inl ⟨hret, hcc, hpost_imp sf hpost⟩
  · exact Or.inr (Or.inl ⟨hpan, h_panic g x s0 sf F R hpanic⟩)
  · rw [h_exit g code s0 sf, satisfies_pure_sepConj] at hexit
    exact False.elim hexit.1
  · rw [h_oom g s0 sf, satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

private theorem allocPanic_frame_dq5 {α β : Type} (g : α) (x : β) (s0 sf : State) (F R : SepProp)
    (hm : sf.mem ⊨ Serialization.allocPanic g s0 sf ∗ (F ∗ R)) :
    sf.mem ⊨ Serialization.allocPanic x s0 sf ∗ R := by
  dsimp only [Serialization.allocPanic] at hm ⊢
  have hm' : sf.mem ⊨ ((⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact hm
  exact allowPanic_frame id hm'

private theorem mergeUint32_encode_dq5 (u : BitVec 32) (tail : List (BitVec 8)) :
    mergeUint32 .varint (encodeVarint (u.setWidth 64) ++ tail) = some (u, tail) := by
  simp [mergeUint32, decodeVarint_encodeVarint]

private theorem genFieldX_tag10 {fl : GenFieldX} (h : fl.tag = 10) : ∃ v, fl = .remReg v := by
  cases fl with
  | base f => cases f <;> simp [GenFieldX.tag, GenField.tag] at h
  | remReg v => exact ⟨v, rfl⟩
  | _ => simp [GenFieldX.tag] at h

private theorem genFieldX_tag11 {fl : GenFieldX} (h : fl.tag = 11) : ∃ v, fl = .locReg v := by
  cases fl with
  | base f => cases f <;> simp [GenFieldX.tag, GenField.tag] at h
  | locReg v => exact ⟨v, rfl⟩
  | _ => simp [GenFieldX.tag] at h

private theorem genFieldX_tag13 {fl : GenFieldX} (h : fl.tag = 13) : ∃ b, fl = .abk b := by
  cases fl with
  | base f => cases f <;> simp [GenFieldX.tag, GenField.tag] at h
  | abk b => exact ⟨b, rfl⟩
  | _ => simp [GenFieldX.tag] at h

/-- `prostSSGXAt` split at `remote_registration_id` (`+0x150`). -/
def prostSSGXRest_mf10 (A : RustAlloc) (ss : BitVec 64) (v : SSGX) : SepProp :=
  vecU8 A ss v.base.lik ∗ vecU8 A (ss + 0x18#64) v.base.rik ∗ vecU8 A (ss + 0x30#64) v.base.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A (ss + 0x60#64) v.ext.abk ∗ vecU8 A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    kyberAt A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

theorem prostSSGXAt_eq_remReg_sep_rest_mf10 (A : RustAlloc) (ss : BitVec 64) (v : SSGX) :
    prostSSGXAt A ss v = ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ prostSSGXRest_mf10 A ss v := by
  unfold prostSSGXAt prostSSGXRest_mf10
  rcases v.ext.kyber with _ | ⟨i, ct⟩ <;> simp only [kyberAt] <;> ac_rfl

/-- `prostSSGXAt` split at `local_registration_id` (`+0x154`). -/
def prostSSGXRest_dq5_mf11 (A : RustAlloc) (ss : BitVec 64) (v : SSGX) : SepProp :=
  vecU8 A ss v.base.lik ∗ vecU8 A (ss + 0x18#64) v.base.rik ∗ vecU8 A (ss + 0x30#64) v.base.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A (ss + 0x60#64) v.ext.abk ∗ vecU8 A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    kyberAt A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg))

theorem prostSSGXAt_eq_locReg_sep_rest_dq5 (A : RustAlloc) (ss : BitVec 64) (v : SSGX) :
    prostSSGXAt A ss v = ((ss + 0x154#64) ↦₃₂ v.ext.locReg) ∗ prostSSGXRest_dq5_mf11 A ss v := by
  unfold prostSSGXAt prostSSGXRest_dq5_mf11
  rcases v.ext.kyber with _ | ⟨i, ct⟩ <;> simp only [kyberAt] <;> ac_rfl

/-- `prostSSGXAt` without `alice_base_key` (`+0x60`). -/
def prostSSGXRest_mf13 (ss : BitVec 64) (v : SSGX) : SepProp :=
  vecU8 A0 ss v.base.lik ∗ vecU8 A0 (ss + 0x18#64) v.base.rik ∗
      vecU8 A0 (ss + 0x30#64) v.base.root ∗
    vecOf A0 104 8 (fun c a => prostChainGAt A0 a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A0 (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A0 (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A0 (ss + 0xf8#64) k ∗
         pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    kyberAt A0 ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

theorem prostSSGXAt_eq_split_mf13 (ss : BitVec 64) (v : SSGX) :
    prostSSGXAt A0 ss v = vecU8 A0 (ss + 0x60#64) v.ext.abk ∗ prostSSGXRest_mf13 ss v := by
  unfold prostSSGXAt prostSSGXRest_mf13
  rw [sepConj_left_comm (vecOf A0 104 8 _ _ _) (vecU8 A0 (ss + 0x60#64) _),
    sepConj_left_comm (vecU8 A0 (ss + 0x30#64) _) (vecU8 A0 (ss + 0x60#64) _),
    sepConj_left_comm (vecU8 A0 (ss + 0x18#64) _) (vecU8 A0 (ss + 0x60#64) _),
    sepConj_left_comm (vecU8 A0 ss _) (vecU8 A0 (ss + 0x60#64) _)]
  rfl

/-- Tag 10 (`remote_registration_id`) `SSGX` leaf on `SP2Ext img.base ext` (`mergeFieldXSpecAtW`). -/
theorem mergeFieldX10_ok_extW (img : Obj.Image)
    {ext : String → Option (State → State)}
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hint32 : Prost.X.Int32MergeOkW img A0 ext) :
    MergeFieldXOkAtW img ext (fun fl => fl.tag = 10) := by
  refine okAtX_of_imp_frame (mergeField10Field_ok_extW img hLoads hint32)
    (fun _ _ _ _ => rfl) allocPanic_frame_dq5 ?_
  intro x s0 R hpre
  dsimp only [mergeFieldXSpecAtW] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, _, htag, _, _, hlen, hF, hsym⟩, hmem⟩
  obtain ⟨u, hfl⟩ := genFieldX_tag10 htag
  rw [hfl] at hx1 hx2 hlen hmem
  refine ⟨⟨x.ss, x.v.ext.remReg, u, (GenFieldX.remReg u).payload, x.bufRef, x.slot, x.ptr, x.tail⟩,
    prostSSGXRest_mf10 A0 x.ss x.v, ?_, ?_⟩
  · dsimp only [mergeField10FieldSpecAtW, mergeFieldU32FieldSpecAtW]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, mergeUint32_encode_dq5 u x.tail, hlen, hF, hsym⟩, ?_⟩
    rw [prostSSGXAt_eq_remReg_sep_rest_mf10 A0 x.ss x.v] at hmem
    convert hmem using 1; ac_rfl
  · intro sf hpost
    dsimp only [mergeField10FieldSpecAtW, mergeFieldU32FieldSpecAtW] at hpost
    dsimp only [mergeFieldXSpecAtW]
    rw [hfl]
    have hss : prostSSGXAt A0 x.ss (x.v.apply (.remReg u)) =
        ((x.ss + 0x150#64) ↦₃₂ u) ∗ prostSSGXRest_mf10 A0 x.ss x.v :=
      prostSSGXAt_eq_remReg_sep_rest_mf10 A0 x.ss (x.v.apply (.remReg u))
    rw [hss]
    convert hpost using 1; ac_rfl

/-- Tag 11 (`local_registration_id`) `SSGX` leaf on `SP2Ext img.base ext` (`mergeFieldXSpecAtW`). -/
theorem mergeFieldX11_ok_extW (img : Obj.Image)
    {ext : String → Option (State → State)}
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hint32 : Prost.X.Int32MergeOkW img A0 ext) :
    MergeFieldXOkAtW img ext (fun fl => fl.tag = 11) := by
  refine okAtX_of_imp_frame (mergeField11Field_ok_extW img hLoads hint32)
    (fun _ _ _ _ => rfl) allocPanic_frame_dq5 ?_
  intro x s0 R hpre
  dsimp only [mergeFieldXSpecAtW] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, _, htag, _, _, hlen, hF, hsym⟩, hmem⟩
  obtain ⟨u, hfl⟩ := genFieldX_tag11 htag
  rw [hfl] at hx1 hx2 hlen hmem
  refine ⟨⟨x.ss, x.v.ext.locReg, u, (GenFieldX.locReg u).payload, x.bufRef, x.slot, x.ptr, x.tail⟩,
    prostSSGXRest_dq5_mf11 A0 x.ss x.v, ?_, ?_⟩
  · dsimp only [mergeField11FieldSpecAtW, mergeFieldU32FieldSpecAtW]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, mergeUint32_encode_dq5 u x.tail, hlen, hF, hsym⟩, ?_⟩
    rw [prostSSGXAt_eq_locReg_sep_rest_dq5 A0 x.ss x.v] at hmem
    convert hmem using 1; ac_rfl
  · intro sf hpost
    dsimp only [mergeField11FieldSpecAtW, mergeFieldU32FieldSpecAtW] at hpost
    dsimp only [mergeFieldXSpecAtW]
    rw [hfl]
    have hss : prostSSGXAt A0 x.ss (x.v.apply (.locReg u)) =
        ((x.ss + 0x154#64) ↦₃₂ u) ∗ prostSSGXRest_dq5_mf11 A0 x.ss x.v :=
      prostSSGXAt_eq_locReg_sep_rest_dq5 A0 x.ss (x.v.apply (.locReg u))
    rw [hss]
    convert hpost using 1; ac_rfl

/-- Tag 13 (`alice_base_key`) `SSGX` leaf on `SP2Ext img.base ext` (`mergeFieldXSpecAtW`). -/
theorem mergeFieldX13_ok_extW (img : Obj.Image)
    {ext : String → Option (State → State)}
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hbytes : Prost.X.BytesMergeOkW img A0 ext) :
    MergeFieldXOkAtW img ext (fun fl => fl.tag = 13) := by
  refine okAtX_of_imp_frame (mergeField13Field_ok_extW img hLoads hbytes)
    (fun _ _ _ _ => rfl) allocPanic_frame_dq5 ?_
  intro x s0 R hpre
  dsimp only [mergeFieldXSpecAtW] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, _, htag, hok, _, hlen, hF, hsym⟩, hmem⟩
  obtain ⟨b, hfl⟩ := genFieldX_tag13 htag
  rw [hfl] at hx1 hx2 hok hlen hmem
  have hb : b.length = 33 := hok
  have hb_lt : b.length < 128 := by omega
  have hpay : (GenFieldX.abk b).payload = [BitVec.ofNat 8 b.length] ++ b := by
    dsimp only [GenFieldX.payload]; rw [hb]; rfl
  refine ⟨⟨x.ss, x.v.ext.abk, b, (GenFieldX.abk b).payload, x.bufRef, x.slot, x.ptr, x.tail⟩,
    prostSSGXRest_mf13 x.ss x.v, ?_, ?_⟩
  · dsimp only [mergeField13FieldSpecAtW, mergeFieldBytesFieldSpecAtW]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    have hmerge : mergeBytes .lengthDelimited ((GenFieldX.abk b).payload ++ x.tail) = some (b, x.tail) := by
      rw [hpay]
      exact mergeBytes_lengthDelimited_of_lt_128_identityRootKeys hb_lt
    refine ⟨⟨hx0, hx1, hx2, hx3, hmerge, hlen, hF, hsym⟩, ?_⟩
    rw [prostSSGXAt_eq_split_mf13 x.ss x.v] at hmem
    convert hmem using 1; ac_rfl
  · intro sf hpost
    dsimp only [mergeField13FieldSpecAtW, mergeFieldBytesFieldSpecAtW] at hpost
    dsimp only [mergeFieldXSpecAtW]
    rw [hfl]
    have hss : prostSSGXAt A0 x.ss (x.v.apply (.abk b)) =
        vecU8 A0 (x.ss + 0x60#64) b ∗ prostSSGXRest_mf13 x.ss x.v :=
      prostSSGXAt_eq_split_mf13 x.ss (x.v.apply (.abk b))
    rw [hss]
    convert hpost using 1; ac_rfl

/-! ## Relocatable `[LibsignalPlacement]` leaves (Block `15`) -/

section Placed

open Arm64.Obj CryptoVerification.E2E.Record.Placed

theorem L1_MergeField10_11_13_15W_Placed : True := trivial

def mergeFieldU32FieldRawSpecW (tag : Nat) (fieldOff : BitVec 64) : Spec MergeFieldU32Ghost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 WireType.varint.toNat ∧
      s.readReg64 .x3 = x.bufRef ∧
      mergeUint32 .varint (x.payload ++ x.tail) = some (x.val, x.tail) ∧
      (x.payload ++ x.tail).length < 2 ^ 62⌝ ∗
      ((x.ss + fieldOff) ↦₃₂ x.oldVal) ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.payload ++ x.tail) ∗ stackAt s.sp mergeFieldStackX
  post := fun x s0 sf => DQ5Placed.u32Post x.ss fieldOff x.bufRef x.slot x.ptr x.val x.payload x.tail s0 sf
  onPanic := Serialization.allocPanic

abbrev mergeFieldU32FieldPlacedSpecW [LibsignalPlacement] (tag : Nat) (fieldOff : BitVec 64) :
    Spec MergeFieldU32Ghost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (mergeFieldU32FieldRawSpecW tag fieldOff)
abbrev mergeField10FieldPlacedSpecW [LibsignalPlacement] := mergeFieldU32FieldPlacedSpecW 10 0x150#64
abbrev mergeField11FieldPlacedSpecW [LibsignalPlacement] := mergeFieldU32FieldPlacedSpecW 11 0x154#64

def mergeFieldBytesFieldRawSpecW (tag : Nat) (fieldOff : BitVec 64) : Spec MergeFieldBytesGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat ∧
      s.readReg64 .x3 = x.bufRef ∧
      mergeBytes .lengthDelimited (x.payload ++ x.tail) = some (x.bytes, x.tail) ∧
      (x.payload ++ x.tail).length < 2 ^ 62⌝ ∗
      vecU8 A0 (x.ss + fieldOff) x.oldBytes ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.payload ++ x.tail) ∗ stackAt s.sp mergeFieldStackX
  post := fun x s0 sf => DQ5Placed.bytesPost x.ss fieldOff x.bufRef x.slot x.ptr x.bytes x.payload x.tail s0 sf
  onPanic := Serialization.allocPanic

abbrev mergeFieldBytesFieldPlacedSpecW [LibsignalPlacement] (tag : Nat) (fieldOff : BitVec 64) :
    Spec MergeFieldBytesGhost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (mergeFieldBytesFieldRawSpecW tag fieldOff)
abbrev mergeField13FieldPlacedSpecW [LibsignalPlacement] := mergeFieldBytesFieldPlacedSpecW 13 0x60#64
abbrev mergeField15FieldPlacedSpecW [LibsignalPlacement] := mergeFieldBytesFieldPlacedSpecW 15 0x78#64

theorem mergeFieldU32Field_placed_ok_extW [LibsignalPlacement] {H : LibsignalHooks}
    {tag : Nat} {fieldOff : BitVec 64} (hint32 : Prost.X.Int32MergePlacedOkW A0 H)
    (h_case : (tag = 10 ∧ fieldOff = 0x150#64) ∨ (tag = 11 ∧ fieldOff = 0x154#64)) :
    subroutine_ok (lsProg_15 H) (blkPl_15).base (mergeFieldU32FieldPlacedSpecW tag fieldOff) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hal
  obtain ⟨hcrl0, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  dsimp only [mergeFieldU32FieldRawSpecW] at hpre_raw
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_raw
  rcases hpre_raw with ⟨⟨hx0, hx1, hx2, hx3, hmerge, hlen⟩, hmem⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc] at hmem
  exact DQ5Placed.mergeFieldU32_placed_sepWPp hint32 h_case x.ss x.bufRef x.slot x.ptr
    x.oldVal x.val x.payload x.tail hpc hrun hal hcrl0 hx0 hx1 hx2 hx3 hmerge hlen hmem

theorem mergeFieldBytesField_placed_ok_extW [LibsignalPlacement] {H : LibsignalHooks}
    {tag : Nat} {fieldOff : BitVec 64} (hbytes : Prost.X.BytesMergePlacedOkW A0 H)
    (h_case : (tag = 13 ∧ fieldOff = 0x60#64) ∨ (tag = 15 ∧ fieldOff = 0x78#64)) :
    subroutine_ok (lsProg_15 H) (blkPl_15).base (mergeFieldBytesFieldPlacedSpecW tag fieldOff) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hal
  obtain ⟨hcrl0, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  dsimp only [mergeFieldBytesFieldRawSpecW] at hpre_raw
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_raw
  rcases hpre_raw with ⟨⟨hx0, hx1, hx2, hx3, hmerge, hlen⟩, hmem⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc] at hmem
  exact DQ5Placed.mergeFieldBytes_placed_sepWPp hbytes h_case x.ss x.bufRef x.slot x.ptr
    x.oldBytes x.bytes x.payload x.tail hpc hrun hal hcrl0 hx0 hx1 hx2 hx3 hmerge hlen hmem

theorem mergeField10Field_placed_ok_extW [LibsignalPlacement] {H : LibsignalHooks}
    (hint32 : Prost.X.Int32MergePlacedOkW A0 H) :
    subroutine_ok (lsProg_15 H) (blkPl_15).base mergeField10FieldPlacedSpecW :=
  mergeFieldU32Field_placed_ok_extW hint32 (Or.inl ⟨rfl, rfl⟩)
theorem mergeField11Field_placed_ok_extW [LibsignalPlacement] {H : LibsignalHooks}
    (hint32 : Prost.X.Int32MergePlacedOkW A0 H) :
    subroutine_ok (lsProg_15 H) (blkPl_15).base mergeField11FieldPlacedSpecW :=
  mergeFieldU32Field_placed_ok_extW hint32 (Or.inr ⟨rfl, rfl⟩)
theorem mergeField13Field_placed_ok_extW [LibsignalPlacement] {H : LibsignalHooks}
    (hbytes : Prost.X.BytesMergePlacedOkW A0 H) :
    subroutine_ok (lsProg_15 H) (blkPl_15).base mergeField13FieldPlacedSpecW :=
  mergeFieldBytesField_placed_ok_extW hbytes (Or.inl ⟨rfl, rfl⟩)
theorem mergeField15Field_placed_ok_extW [LibsignalPlacement] {H : LibsignalHooks}
    (hbytes : Prost.X.BytesMergePlacedOkW A0 H) :
    subroutine_ok (lsProg_15 H) (blkPl_15).base mergeField15FieldPlacedSpecW :=
  mergeFieldBytesField_placed_ok_extW hbytes (Or.inr ⟨rfl, rfl⟩)
end Placed
end Symbolic.Swarm.TRREF.B3DeserQ
