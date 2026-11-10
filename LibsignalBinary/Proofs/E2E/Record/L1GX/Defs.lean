/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.RecordX.ScopeP

/-!
# Definitions and Specifications for PQXDH-Scope `SessionRecord::deserialize`

Extends `DeserializeGeneral` (`Record/DeserializeGeneral/Defs.lean`) to cover every record in the
PQXDH decoder scope `DeserializeScopeP` (`RecordX/ScopeP.lean`), adding `ExtraG`, `SSGX`,
`prostSSGXAt`, and `GenFieldX` for tags `9` (full `PendingPreKey` with `pre_key_id` and
`signed_pre_key_id`), `10` (`remote_registration_id`), `11` (`local_registration_id`), `13`
(`alice_base_key`), `14` (`pending_kyber_pre_key`), and `15` (`pq_ratchet_state`).
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.L1GX

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (OkAt CanonRecord allocPanic)
open CryptoVerification.E2E.RecordX (DeserializeScopeP SessionScopeP)

/-! ## Decoded Value -/

/-- Decoded values of the PQXDH-scope `SessionStructure` fields beyond `DeserializeGeneral.SSG`:
`PendingPreKey` IDs (`pid`, `spk`), registration IDs (`remReg`, `locReg`), `alice_base_key`,
`pending_kyber_pre_key`, and `pq_ratchet_state`. -/
structure ExtraG where
  pid : Option (BitVec 32)
  spkId : BitVec 32
  remReg : BitVec 32
  locReg : BitVec 32
  abk : List (BitVec 8)
  kyber : Option (BitVec 32 × List (BitVec 8))
  pq : List (BitVec 8)

def ExtraG.empty : ExtraG := ⟨none, 0#32, 0#32, 0#32, [], none, []⟩

/-- Full decoded `SessionStructure` value for a PQXDH-scope session (`SSG` plus `ExtraG`). -/
structure SSGX where
  base : SSG
  ext : ExtraG

def SSGX.empty : SSGX := ⟨SSG.empty, ExtraG.empty⟩

/-! ## `SessionStructure` Memory Layout -/

/-- `pre_key_id : Option<u32>` at `ss + 0x110` inside a present `PendingPreKey`, separated from `R`. -/
def pidAt (ss : BitVec 64) (pid : Option (BitVec 32)) (R : SepProp) : SepProp :=
  match pid with
  | none => ((ss + 0x110#64) ↦₃₂ 0#32) ∗ memRegion (ss + 0x114#64) 4 ∗ R
  | some i => ((ss + 0x110#64) ↦₃₂ 1#32) ∗ ((ss + 0x114#64) ↦₃₂ i) ∗ R

/-- 32-byte `pending_kyber_pre_key : Option<PendingKyberPreKey>` at `ss + 0x128`, separated from `R`. -/
def kyberAt (A : RustAlloc) (ss : BitVec 64) (kyber : Option (BitVec 32 × List (BitVec 8)))
    (R : SepProp) : SepProp :=
  match kyber with
  | none => ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24 ∗ R
  | some (i, ct) => vecU8 A (ss + 0x128#64) ct ∗ ((ss + 0x140#64) ↦₃₂ i) ∗
      memRegion (ss + 0x144#64) 4 ∗ R

/-- 344-byte prost `SessionStructure` layout at `ss` holding `v : SSGX`: extends `prostSSGAt` on
`v.base` with `alice_base_key` at `+0x60`, `pq_ratchet_state` at `+0x78`, `PendingPreKey` IDs at
`+0x110` and `+0x120`, `pending_kyber_pre_key` at `+0x128`, and registration IDs at `+0x150`/`+0x154`. -/
def prostSSGXAt (A : RustAlloc) (ss : BitVec 64) (v : SSGX) : SepProp :=
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
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

private theorem pointsTo64_zero_eq_two32 (ss : BitVec 64) :
    ((ss + 0x150#64) ↦₃₂ 0#32) ∗ ((ss + 0x154#64) ↦₃₂ 0#32) = ((ss + 0x150#64) ↦₆₄ 0#64) := by
  have h := pointsTo64_split32 (ss + 0x150#64) 0#64
  have ha : ss + 0x150#64 + 4#64 = ss + 0x154#64 := by rw [BitVec.add_assoc]; rfl
  have h0 : BitVec.extractLsb' 0 32 0#64 = 0#32 := rfl
  have h1 : BitVec.extractLsb' 32 32 0#64 = 0#32 := rfl
  rw [ha, h0, h1] at h
  exact h.symm

/-- With `ExtraG.empty`, `prostSSGXAt` reduces to `DeserializeGeneral.prostSSGAt`. -/
theorem prostSSGXAt_empty (A : RustAlloc) (ss : BitVec 64) (v : SSG) :
    prostSSGXAt A ss ⟨v, ExtraG.empty⟩ = prostSSGAt A ss v := by
  unfold prostSSGXAt prostSSGAt ExtraG.empty
  dsimp only [kyberAt, pidAt]
  rw [pointsTo64_zero_eq_two32 ss]
  rcases v with ⟨_, _, _, _, _, _, _, _ | _⟩ <;> rfl

/-! ## Protobuf Field Decomposition -/

/-- Encoded body of `PendingPreKey` with `pre_key_id = some i`, `base_key = k`, and zero
`signed_pre_key_id` / `timestamp`. -/
def pendingIdBody (i : BitVec 32) (k : List (BitVec 8)) : List (BitVec 8) :=
  encodeKey 1 .varint ++ encodeVarint (i.setWidth 64) ++ lenField 2 k

/-- Encoded body of `PendingPreKey` with `pre_key_id = pid`, `base_key = k`, `signed_pre_key_id = spk`,
and zero `timestamp`. -/
def pendingSpkBody (pid : Option (BitVec 32)) (k : List (BitVec 8)) (spk : BitVec 32) :
    List (BitVec 8) :=
  optUint32Field 1 pid ++ lenField 2 k ++ int32Field 3 spk

/-- Encoded body of `PendingKyberPreKey` (`pre_key_id` tag `1`, `ciphertext` tag `2`). -/
def kyberBody (i : BitVec 32) (ct : List (BitVec 8)) : List (BitVec 8) :=
  uint32Field 1 i ++ lenField 2 ct

/-- One protobuf field of a PQXDH-scope `encSession s`. -/
inductive GenFieldX where
  /-- Field inherited from `DeserializeGeneral.GenField` (tags `1..7`, or tag `9` with only `base_key`). -/
  | base (f : GenField)
  /-- Tag `9` (`pending_pre_key`) with `pre_key_id = some i`, `base_key = k`, and `signed_pre_key_id = 0`. -/
  | pendingId (i : BitVec 32) (k : List (BitVec 8))
  /-- Tag `9` (`pending_pre_key`) with `pre_key_id = pid`, `base_key = k`, and `signed_pre_key_id = spk ≠ 0`. -/
  | pendingSpk (pid : Option (BitVec 32)) (k : List (BitVec 8)) (spk : BitVec 32)
  /-- Tag `10` (`remote_registration_id`). -/
  | remReg (v : BitVec 32)
  /-- Tag `11` (`local_registration_id`). -/
  | locReg (v : BitVec 32)
  /-- Tag `13` (`alice_base_key`). -/
  | abk (b : List (BitVec 8))
  /-- Tag `14` (`pending_kyber_pre_key`). -/
  | kyber (i : BitVec 32) (ct : List (BitVec 8))
  /-- Tag `15` (`pq_ratchet_state`). -/
  | pq (b : List (BitVec 8))

def GenFieldX.tag : GenFieldX → Nat
  | .base f => f.tag
  | .pendingId _ _ => 9
  | .pendingSpk _ _ _ => 9
  | .remReg _ => 10
  | .locReg _ => 11
  | .abk _ => 13
  | .kyber _ _ => 14
  | .pq _ => 15

def GenFieldX.wt : GenFieldX → WireType
  | .base f => f.wt
  | .remReg _ | .locReg _ => .varint
  | _ => .lengthDelimited

def GenFieldX.payload : GenFieldX → List (BitVec 8)
  | .base f => f.payload
  | .pendingId i k =>
      encodeVarint (BitVec.ofNat 64 (pendingIdBody i k).length) ++ pendingIdBody i k
  | .pendingSpk pid k spk =>
      encodeVarint (BitVec.ofNat 64 (pendingSpkBody pid k spk).length) ++
        pendingSpkBody pid k spk
  | .remReg v | .locReg v => encodeVarint (v.setWidth 64)
  | .abk b => encodeVarint (BitVec.ofNat 64 b.length) ++ b
  | .kyber i ct => encodeVarint (BitVec.ofNat 64 (kyberBody i ct).length) ++ kyberBody i ct
  | .pq b => encodeVarint (BitVec.ofNat 64 b.length) ++ b

def GenFieldX.enc (fl : GenFieldX) : List (BitVec 8) := encodeKey fl.tag fl.wt ++ fl.payload

/-- Effect of `SessionStructure::merge_field` on `SSGX` for one `GenFieldX`. -/
def SSGX.apply (v : SSGX) : GenFieldX → SSGX
  | .base f => ⟨v.base.apply f, v.ext⟩
  | .pendingId i k => ⟨{ v.base with pending := some k }, { v.ext with pid := some i }⟩
  | .pendingSpk pid k spk =>
      ⟨{ v.base with pending := some k }, { v.ext with pid := pid, spkId := spk }⟩
  | .remReg r => ⟨v.base, { v.ext with remReg := r }⟩
  | .locReg l => ⟨v.base, { v.ext with locReg := l }⟩
  | .abk b => ⟨v.base, { v.ext with abk := b }⟩
  | .kyber i ct => ⟨v.base, { v.ext with kyber := some (i, ct) }⟩
  | .pq b => ⟨v.base, { v.ext with pq := b }⟩

def GenFieldX.Ok : GenFieldX → Prop
  | .base f => f.Ok
  | .pendingId _ k => k.length = 33
  | .pendingSpk _ k spk => k.length = 33 ∧ spk ≠ 0#32
  | .remReg _ | .locReg _ | .pq _ => True
  | .abk b => b.length = 33
  | .kyber _ ct => ct.length = 1569

def GenFieldX.Fresh (v : SSGX) : GenFieldX → Prop
  | .base f => v.ext = ExtraG.empty ∧ f.Fresh v.base
  | .pendingId _ _ => v.base.pending = none ∧ v.ext = ExtraG.empty
  | .pendingSpk _ _ _ => v.base.pending = none ∧ v.ext = ExtraG.empty
  | .remReg _ => v.ext.remReg = 0
  | .locReg _ => v.ext.locReg = 0
  | .abk _ => v.ext.abk = []
  | .kyber _ _ => v.ext.kyber = none
  | .pq _ => v.ext.pq = []

/-! ## Session and Record Field Lists -/

def pendingFieldX : Option PendingPreKey → List GenFieldX
  | none => []
  | some p =>
    if p.signedPreKeyId = 0 then
      match p.preKeyId with
      | none => [GenFieldX.base (GenField.pending p.baseKey.serialize)]
      | some i => [GenFieldX.pendingId i p.baseKey.serialize]
    else
      [GenFieldX.pendingSpk p.preKeyId p.baseKey.serialize p.signedPreKeyId]

/-- Ordered list of protobuf fields emitted by `encSession s` for `s` in `SessionScopeP`. -/
def genFieldsX (s : Session (List (BitVec 8))) : List GenFieldX :=
  (genFields { s with pendingPreKey := none }).map GenFieldX.base ++
    pendingFieldX s.pendingPreKey ++
    (if s.remoteRegistrationId = 0 then [] else [GenFieldX.remReg s.remoteRegistrationId]) ++
    (if s.localRegistrationId = 0 then [] else [GenFieldX.locReg s.localRegistrationId]) ++
    (if s.aliceBaseKey = [] then [] else [GenFieldX.abk s.aliceBaseKey]) ++
    (match s.pendingKyberPreKey with
     | some k => [GenFieldX.kyber k.preKeyId k.ciphertext]
     | none => []) ++
    (if s.state.pqRatchetState = [] then [] else [GenFieldX.pq s.state.pqRatchetState])

def recFieldsX (r : SessionRecord (List (BitVec 8))) : List GenFieldX :=
  match r.currentSession with
  | some s => genFieldsX s
  | none => []

def ssgxAfter (r : SessionRecord (List (BitVec 8))) (k : Nat) : SSGX :=
  ((recFieldsX r).take k).foldl SSGX.apply SSGX.empty

def ssgxOf (s : Session (List (BitVec 8))) : SSGX :=
  ⟨ssgOf s,
    ⟨s.pendingPreKey.bind (·.preKeyId),
     (s.pendingPreKey.map (·.signedPreKeyId)).getD 0,
     s.remoteRegistrationId,
     s.localRegistrationId,
     s.aliceBaseKey,
     s.pendingKyberPreKey.map (fun k => (k.preKeyId, k.ciphertext)),
     s.state.pqRatchetState⟩⟩

/-! ## Callee Contracts -/

structure MergeFieldXGhost where
  ss : BitVec 64
  v : SSGX
  fld : GenFieldX
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  tail : List (BitVec 8)

/-- Contract of `SessionStructure::merge_field` (`0x581c`) on one PQXDH-scope field satisfying `P`. -/
def mergeFieldXSpec (P : GenFieldX → Prop) : Spec MergeFieldXGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧ x.fld.Fresh x.v ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 32 ∧
      sessionImg0.FrozenLoaded s ∧ s.symtab = sessionImg0.symtab⌝ ∗
      prostSSGXAt A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗ stackAt s.sp mergeFieldStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ prostSSGXAt A0 x.ss (x.v.apply x.fld) ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt s0.sp mergeFieldStack
  onPanic := allocPanic

def MergeFieldXOk (C : Crypto) (ctl : BitVec 64)
    (P : GenFieldX → Prop) (abs : String → Option (State → State)) : Prop :=
  OkAt sessionImg0.base C ctl abs mergeFieldName (mergeFieldXSpec P)

/-! ## PQXDH-Scope `SessionRecord::deserialize` Contract -/

/-- Contract of `SessionRecord::deserialize` (`0x16ed4`) on `encodeRecord r` for `r` in
`DeserializeScopeP`, yielding canonical `sessionRecordAt` at `out`. -/
noncomputable def deserializeXSpec : Spec DeserializeGenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.p ∧ s.readReg64 .x1 = BitVec.ofNat 64 (encodeRecord x.r).length ∧
      s.readReg64 .x8 = x.out ∧ DeserializeScopeP x.r ∧
      sessionImg0.FrozenLoaded s ∧ s.symtab = sessionImg0.symtab⌝ ∗
      (x.p ↦ₛ encodeRecord x.r) ∗ memRegion x.out 368 ∗ stackAt s.sp recDeserializeStack
  post := deserializeGenSpec.post
  onPanic := allocPanic

end CryptoVerification.E2E.Record.L1GX
