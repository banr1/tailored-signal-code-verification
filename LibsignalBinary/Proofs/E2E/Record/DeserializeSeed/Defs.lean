/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefs
public import LibsignalBinary.Proofs.E2E.Record.Support.Hooks
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymA
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymC
public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
public import LibsignalBinary.Proofs.E2E.Record.Support.Image
public import LibsignalBinary.Proofs.E2E.Record.Support.SeedModel
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym
import ProofLib.SepLogic.WPFrozen

/-!
# Definitions and Callee Contracts for Seed `SessionRecord::deserialize`

Defines the field decomposition (`SeedField`, `seedFields`), decoded prost value prefix (`ChainV`,
`SSV`, `SSV.apply`, `ssvAfter`), memory layouts (`prostChainAt`, `prostSSAt`), and subroutine
contracts (`mergeFieldSeedSpec`, `chainMergeSeedSpec`, `DeserializeCallees`, and their
`[LibsignalPlacement]` counterparts) for `SessionRecord::deserialize` (`0x16ed4`) on `seedRecord f`:
* `prostSSAt` (344 bytes): six `Vec` headers (`{0, 1, 0}` for `Vec<u8>`, `{0, 8, 0}` for
  `receiver_chains` at `+0x48`), `Option` `-1` niches (`sender_chain` at `+0x90`,
  `pending_pre_key` at `+0xf8`, `pending_kyber_pre_key` at `+0x128`), and scalar fields at
  `+0x148..+0x158`.
* `prostChainAt` (104 bytes): `sender_ratchet_key` at `+0x00`, `sender_ratchet_key_private` at
  `+0x18`, empty `message_keys` at `+0x30`, and `Option<ChainKey>` at `+0x48`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeSeed

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record

/-! ## Decoded Values and Seed Field Encoding -/

/-- Decoded prost `session_structure::Chain` written by seed: serialized `sender_ratchet_key`,
optional `sender_ratchet_key_private` (`[]` when absent), empty `message_keys`, and `chain_key`. -/
structure ChainV where
  srk : List (BitVec 8)
  priv : List (BitVec 8)
  ck : Option (BitVec 32 × List (BitVec 8))

/-- Decoded prefix of prost `SessionStructure` modified by seed fields (remaining fields stay at
`SessionStructure::default()`). -/
structure SSV where
  version : BitVec 32
  lik : List (BitVec 8)
  rik : List (BitVec 8)
  root : List (BitVec 8)
  recv : List ChainV
  sender : Option ChainV
  pending : Option (List (BitVec 8))

def SSV.empty : SSV := ⟨0, [], [], [], [], none, none⟩

/-- One field of `seedSession f`, with its decoded payload. -/
inductive SeedField where
  /-- Tag `1` (`session_version`, varint). -/
  | version (v : BitVec 32)
  /-- Tag `2` (`local_identity_public`). -/
  | lik (b : List (BitVec 8))
  /-- Tag `3` (`remote_identity_public`). -/
  | rik (b : List (BitVec 8))
  /-- Tag `4` (`root_key`). -/
  | root (b : List (BitVec 8))
  /-- Tag `6` (`sender_chain` `Chain` message). -/
  | sender (c : ChainV)
  /-- Tag `7` (`receiver_chains` `Chain` message). -/
  | recv (c : ChainV)
  /-- Tag `9` (`pending_pre_key` `PendingPreKey` message with `base_key` at tag `2`). -/
  | pending (baseKey : List (BitVec 8))

def SeedField.tag : SeedField → Nat
  | .version _ => 1 | .lik _ => 2 | .rik _ => 3 | .root _ => 4
  | .sender _ => 6 | .recv _ => 7 | .pending _ => 9

def SeedField.wt : SeedField → WireType
  | .version _ => .varint
  | _ => .lengthDelimited

/-- Protobuf encoding of `c` matching `pbChain`: `srk` (tag `1`), optional private key (tag `2`),
and `chain_key` (tag `3`). -/
def ChainV.enc (c : ChainV) : List (BitVec 8) :=
  pbBytes 1 c.srk ++ (if c.priv = [] then [] else pbBytes 2 c.priv) ++
    (match c.ck with
     | some (i, k) => pbBytes 3 (pbVarint 1 i.toNat ++ pbBytes 2 k)
     | none => [])

def SeedField.payload : SeedField → List (BitVec 8)
  | .version v => pbVarintBody 5 v.toNat
  | .lik b => [BitVec.ofNat 8 b.length] ++ b
  | .rik b => [BitVec.ofNat 8 b.length] ++ b
  | .root b => [BitVec.ofNat 8 b.length] ++ b
  | .sender c => [BitVec.ofNat 8 c.enc.length] ++ c.enc
  | .recv c => [BitVec.ofNat 8 c.enc.length] ++ c.enc
  | .pending k => [BitVec.ofNat 8 (pbBytes 2 k).length] ++ pbBytes 2 k

def SeedField.enc (fl : SeedField) : List (BitVec 8) :=
  pbKey fl.tag (if fl.wt = .varint then 0 else 2) ++ fl.payload

def seedChain (pub : List (BitVec 8)) (priv : Option (List (BitVec 8))) (key : List (BitVec 8))
    (index : Nat) : ChainV :=
  ⟨pbPubkey pub, priv.getD [], some (BitVec.ofNat 32 index, key)⟩

/-- Ordered list of protobuf fields emitted by `seedSession f`. -/
def seedFields (f : List (BitVec 8)) : List SeedField :=
  [.version 4, .lik (pbPubkey (seedSlice f 0 32)), .rik (pbPubkey (seedSlice f 32 32)),
    .root (seedSlice f 64 32)] ++
  (if f.getD 96 0 = 1 then
    [.sender (seedChain (seedSlice f 97 32) (some (seedSlice f 129 32)) (seedSlice f 161 32)
      (seedU32 f 193))] else []) ++
  (if f.getD 197 0 = 1 then
    [.recv (seedChain (seedSlice f 198 32) none (seedSlice f 230 32) (seedU32 f 262))] else []) ++
  (if f.getD 266 0 = 1 then [.pending (pbPubkey (List.replicate 32 0#8))] else [])

/-- Effect of `SessionStructure::merge_field` on `SSV` for one seed field. -/
def SSV.apply (v : SSV) : SeedField → SSV
  | .version x => { v with version := x }
  | .lik b => { v with lik := b }
  | .rik b => { v with rik := b }
  | .root b => { v with root := b }
  | .sender c => { v with sender := some c }
  | .recv c => { v with recv := v.recv ++ [c] }
  | .pending k => { v with pending := some k }

def ssvAfter (f : List (BitVec 8)) (k : Nat) : SSV :=
  ((seedFields f).take k).foldl SSV.apply SSV.empty

/-! ## Memory Layouts -/

/-- 104-byte prost `session_structure::Chain` layout at `a`: `sender_ratchet_key` at `+0x00`,
`sender_ratchet_key_private` at `+0x18`, empty `message_keys` at `+0x30`, and `optChainKeyAt` at `+0x48`. -/
def prostChainAt (A : RustAlloc) (a : BitVec 64) (c : ChainV) : SepProp :=
  vecU8 A a c.srk ∗ vecU8 A (a + 0x18#64) c.priv ∗
    vecOf A 104 8 (fun (_ : Unit) _ => emp) (a + 0x30#64) [] ∗
    match c.ck with
    | none => ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24
    | some (i, k) => vecU8 A (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗
        memRegion (a + 0x64#64) 4

/-- 344-byte prost `SessionStructure` layout at `ss` holding `v`, with fields unwritten by seed fixed
at `SessionStructure::default()`: `local_identity_public` at `+0x00`, `remote_identity_public` at
`+0x18`, `root_key` at `+0x30`, `receiver_chains` at `+0x48`, `alice_base_key` at `+0x60`,
`pq_ratchet_state` at `+0x78`, `sender_chain` at `+0x90`, `pending_pre_key` at `+0xf8`,
`pending_kyber_pre_key` at `+0x128`, and scalar fields at `+0x148..+0x158`. -/
def prostSSAt (A : RustAlloc) (ss : BitVec 64) (v : SSV) : SepProp :=
  vecU8 A ss v.lik ∗ vecU8 A (ss + 0x18#64) v.rik ∗ vecU8 A (ss + 0x30#64) v.root ∗
    vecOf A 104 8 (fun c a => prostChainAt A a c) (ss + 0x48#64) v.recv ∗
    vecU8 A (ss + 0x60#64) [] ∗ vecU8 A (ss + 0x78#64) [] ∗
    (match v.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainAt A (ss + 0x90#64) c) ∗
    (match v.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗ ((ss + 0x110#64) ↦₃₂ 0#32) ∗
         memRegion (ss + 0x114#64) 4 ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗
         ((ss + 0x120#64) ↦₃₂ 0#32) ∗ memRegion (ss + 0x124#64) 4) ∗
    ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24 ∗
    ((ss + 0x148#64) ↦₃₂ v.version) ∗ ((ss + 0x14c#64) ↦₃₂ 0#32) ∗ ((ss + 0x150#64) ↦₆₄ 0#64)

/-! ## Seed-Restricted Callee Contracts -/

/-- `SessionStructure::merge_field` (image offset `0x581c`, 700 instructions). -/
abbrev mergeFieldName : String :=
  "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>"

/-- `prost::encoding::message::merge::<Chain, &mut &[u8]> [local#1]` (image offset `0x3974`, 634
instructions). -/
abbrev chainMergeName : String :=
  "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"

/-- Stack budget for `SessionStructure::merge_field` (`0xf0` local frame plus `message::merge<Chain>`
and allocator hooks). -/
abbrev mergeFieldStack : Nat := 0x4000

/-- Stack budget for `prost::encoding::message::merge::<Chain>` on seed chains. -/
abbrev chainMergeStack : Nat := 0x3000

/-- Ghost state for a seed `SessionStructure::merge_field` call. -/
structure MergeFieldGhost where
  ss : BitVec 64
  v : SSV
  fld : SeedField
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  tail : List (BitVec 8)
  f : List (BitVec 8)

/-- Contract of `SessionStructure::merge_field` (`0x581c`) on one seed field satisfying `P`:
advances the slice cursor past `fld.payload`, updates `prostSSAt` from `v` to `v.apply fld`, and
returns `x0 = 0`. -/
def mergeFieldSeedSpec (P : SeedField → Prop) : Spec MergeFieldGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ SeedOk x.f ∧ x.fld ∈ seedFields x.f ∧
      (x.fld matches .sender _ → x.v.sender = none) ∧
      (x.fld matches .pending _ → x.v.pending = none) ∧
      (x.fld matches .recv _ → x.v.recv = []) ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 32 ∧
      sessionImg0.FrozenLoaded s ∧ s.symtab = sessionImg0.symtab⌝ ∗
      prostSSAt A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗ stackAt s.sp mergeFieldStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ prostSSAt A0 x.ss (x.v.apply x.fld) ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt s0.sp mergeFieldStack
  onPanic := Serialization.allocPanic

/-- Ghost state for a seed `prost::encoding::message::merge::<Chain>` call. -/
structure ChainMergeGhost where
  a : BitVec 64
  c : ChainV
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  tail : List (BitVec 8)
  f : List (BitVec 8)

/-- Contract of `prost::encoding::message::merge::<Chain>` (`0x3974`) on a seed chain `c`: decodes
`[len] ++ c.enc` into a default-initialized `prostChainAt` slot at `a` and returns `x0 = 0`. -/
def chainMergeSeedSpec : Spec ChainMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = 2#8 ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = 99#32 ∧ SeedOk x.f ∧
      (SeedField.sender x.c ∈ seedFields x.f ∨ SeedField.recv x.c ∈ seedFields x.f) ∧
      ([BitVec.ofNat 8 x.c.enc.length] ++ x.c.enc ++ x.tail).length < 2 ^ 32 ∧
      sessionImg0.FrozenLoaded s ∧ s.symtab = sessionImg0.symtab⌝ ∗
      prostChainAt A0 x.a ⟨[], [], none⟩ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr ([BitVec.ofNat 8 x.c.enc.length] ++ x.c.enc ++ x.tail) ∗
      stackAt s.sp chainMergeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ prostChainAt A0 x.a x.c ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr ([BitVec.ofNat 8 x.c.enc.length] ++ x.c.enc ++ x.tail)
        x.tail ∗
      stackAt s0.sp chainMergeStack
  onPanic := Serialization.allocPanic

/-! ## Callee Bundles -/

/-- Callee contracts required by seed `SessionRecord::deserialize` on `tripleRatchetProgAt`:
`decode_varint_slice`, `int32::merge`, `bytes::merge`, and `RawVec<Chain>::grow_one`. -/
def DeserializeCallees (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  Prost.DecodeVarintSliceOk sessionImg0.base C A0 ctl abs ∧
    Prost.Int32MergeOk sessionImg0.base C A0 ctl abs ∧
    Prost.BytesMergeOk sessionImg0 C A0 ctl abs ∧
    subroutine_ok (tripleRatchetProgAt sessionImg0.base C ctl abs)
      ((tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr
        "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")
      ((CryptoVerification.LibsignalSession.growOneSpec A0).inImage sessionImg0)

def MergeFieldSeedOk (C : Crypto) (ctl : BitVec 64)
    (P : SeedField → Prop) (abs : String → Option (State → State)) : Prop :=
  Serialization.OkAt sessionImg0.base C ctl abs mergeFieldName (mergeFieldSeedSpec P)

def ChainMergeSeedOk (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  Serialization.OkAt sessionImg0.base C ctl abs chainMergeName chainMergeSeedSpec

/-! ## Relocatable `[LibsignalPlacement]` Contracts and Callee Bundles -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

/-- `.rodata` jump-table symbol of `SessionStructure::merge_field` (block `15`, 15 bytes, tags `1..15`). -/
abbrev mergeFieldRodataSym : String :=
  "libsignal_protocol:.rodata.<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>"

/-- Image-free base contract of `SessionStructure::merge_field` (block `15`) on one seed field
restricted by `P`. -/
def mergeFieldSeedRawSpec (P : SeedField → Prop) : Spec MergeFieldGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ SeedOk x.f ∧ x.fld ∈ seedFields x.f ∧
      (x.fld matches .sender _ → x.v.sender = none) ∧
      (x.fld matches .pending _ → x.v.pending = none) ∧
      (x.fld matches .recv _ → x.v.recv = []) ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 32⌝ ∗
      prostSSAt A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗ stackAt s.sp mergeFieldStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ prostSSAt A0 x.ss (x.v.apply x.fld) ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt s0.sp mergeFieldStack
  onPanic := Serialization.allocPanic

abbrev mergeFieldSeedPlacedSpec [LibsignalPlacement] (P : SeedField → Prop) : Spec MergeFieldGhost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (mergeFieldSeedRawSpec P)

/-- Image-free base contract of `message::merge<Chain>` (block `11`) on one of seed's chains. -/
def chainMergeSeedRawSpec : Spec ChainMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = 2#8 ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = 99#32 ∧ SeedOk x.f ∧
      (SeedField.sender x.c ∈ seedFields x.f ∨ SeedField.recv x.c ∈ seedFields x.f) ∧
      ([BitVec.ofNat 8 x.c.enc.length] ++ x.c.enc ++ x.tail).length < 2 ^ 32⌝ ∗
      prostChainAt A0 x.a ⟨[], [], none⟩ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr ([BitVec.ofNat 8 x.c.enc.length] ++ x.c.enc ++ x.tail) ∗
      stackAt s.sp chainMergeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ prostChainAt A0 x.a x.c ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr ([BitVec.ofNat 8 x.c.enc.length] ++ x.c.enc ++ x.tail)
        x.tail ∗
      stackAt s0.sp chainMergeStack
  onPanic := Serialization.allocPanic

abbrev chainMergeSeedPlacedSpec [LibsignalPlacement] : Spec ChainMergeGhost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl chainMergeSeedRawSpec

/-- Relocatable `[LibsignalPlacement]` callee bundle for `SessionRecord::deserialize` at `A0`:
* `decode_varint_slice` (block `76`),
* `int32::merge` (block `8`),
* `bytes::merge` (block `7`, carrying `LibsignalCodeRoLoaded lsmpl`),
* `RawVec<Chain>::grow_one` (block `43`). -/
def DeserializeCalleesPlaced [LibsignalPlacement]
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_76).rebase (blkPl_76).base H) (blkPl_76).base
      (withLsCodeLoaded lsmpl (Prost.decodeVarintSliceSpec A0)) ∧
    subroutine_ok ((blkPC_8).rebase (blkPl_8).base H) (blkPl_8).base
      (withLsCodeLoaded lsmpl (Prost.int32MergeSpec A0)) ∧
    subroutine_ok ((blkPC_7).rebase (blkPl_7).base H) (blkPl_7).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (Prost.bytesMergeRawSpec A0)) ∧
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (CryptoVerification.LibsignalSession.growOneSpec A0))

def MergeFieldSeedPlacedOk [LibsignalPlacement]
    (P : SeedField → Prop) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_15 H) (blkPl_15).base (mergeFieldSeedPlacedSpec P)

def ChainMergeSeedPlacedOk [LibsignalPlacement]
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_11 H) (blkPl_11).base chainMergeSeedPlacedSpec

/-- Cross-block call transfer from `calleeProg` (block `j`) to `callerProg` (block `i`) for a
callee specification wrapped with `LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl`. -/
theorem ls_call_ro_of_block [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl spec))
    (_hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcrl0, _⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  have hQL : calleeProg.CodeLoaded s0.mem :=
    hcallee_prog.eq_blockProgram ▸ hcrl0.1 j (Nat.lt_of_lt_of_le hj (by decide)) hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact Arm64.reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ)
    (reaches_outcome.of_outcome hout)

/-- Cross-block call transfer from `withLsCodeLoaded lsmpl spec` on `calleeProg` (block `j`) to
`LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl spec` on `callerProg` (block `i`). -/
theorem ls_call_ro_of_cl [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl spec) :=
  ls_call_ro_of_block (callerProg := callerProg)
    (LibsignalTripleRatchet.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hcallee)
    hi hj hj_unmut

/-- Step a `subroutine_ok prog entry (withLsCodeRoLoaded pl spec)` call inside `SepWPp`,
threading `LibsignalCodeRoLoaded pl ·.mem` across `Steps.keepsFrozen`. -/
theorem SepWPp.call_lscro {α : Type} {prog : Program} {pl : MultiPlacement}
    {ret entry ret_pc : BitVec 64} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (LibsignalTripleRatchet.withLsCodeRoLoaded pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded pl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → LibsignalCodeRoLoaded pl sf.mem →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hpre' : s.mem ⊨ (LibsignalTripleRatchet.withLsCodeRoLoaded pl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcrl, hpre R hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hpre' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm (hcrl.of_keepsFrozen hsteps.keepsFrozen)
        hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, hpanic sm hpan⟩)⟩
  · exact (hexit sm code _ hex hpost).elim
  · dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded] at hpost
    rw [hoom sm] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

end Placed

end CryptoVerification.E2E.Record.DeserializeSeed
