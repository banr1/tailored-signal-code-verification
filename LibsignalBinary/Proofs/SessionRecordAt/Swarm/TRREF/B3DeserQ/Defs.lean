/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.L1GX.BodyDefs
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3Defs
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsX

/-!
# `Q`-Generalized W-Stack `SessionRecord::deserialize` Definitions

Extends the `L1GX` `SessionStructure` decoded representation, spatial layout (`prostSSGQAt`),
field decomposition (`GenFieldQ`, adding protobuf tag 15 `pq_ratchet_state`), and `merge_field` /
`SessionRecord::deserialize` contracts to `DeserializeScopeP_Q NonEmptyV1Q` (`b.length < 2 ^ 32`)
at `mergeFieldStackX = 32768` and slice length `< 2 ^ 62`, on `SP2Ext` and under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.B3DeserQ

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (OkAt CanonRecord allocPanic)
open CryptoVerification.E2E.RecordX (DeserializeScopeP SessionScopeP)
open CryptoVerification.E2E.Record.L1GX
open Symbolic.Swarm.TRREF.B3Defs
open Proofs.libsignal.Hooks2

theorem L1_B3DeserQ_Defs : True := trivial

/-! ## Decoded value (`ExtraGQ`, `SSGQ`) -/

/-- Decoded values of the `SessionStructure` fields beyond `DeserializeGeneral.SSG`, including
`pq : List (BitVec 8)` (`pq_ratchet_state`, protobuf tag 15, struct offset `+0x78`). -/
structure ExtraGQ where
  pid : Option (BitVec 32)
  spkId : BitVec 32
  remReg : BitVec 32
  locReg : BitVec 32
  abk : List (BitVec 8)
  pq : List (BitVec 8)
  kyber : Option (BitVec 32 × List (BitVec 8))

/-- Default `ExtraGQ` (`SessionStructure::default()`). -/
def ExtraGQ.empty : ExtraGQ := ⟨none, 0#32, 0#32, 0#32, [], [], none⟩

/-- Project `ExtraGQ` to `L1GX.ExtraG` (dropping `pq`). -/
def ExtraGQ.toExtraG (e : ExtraGQ) : ExtraG :=
  ⟨e.pid, e.spkId, e.remReg, e.locReg, e.abk, e.kyber, []⟩

/-- Lift `L1GX.ExtraG` to `ExtraGQ` with a given `pq` (default `[]`). -/
def ExtraG.toExtraGQ (e : ExtraG) (pq : List (BitVec 8) := []) : ExtraGQ :=
  ⟨e.pid, e.spkId, e.remReg, e.locReg, e.abk, pq, e.kyber⟩

/-- Decoded value of all `SessionStructure` fields in `DeserializeScopeP_Q NonEmptyV1Q`. -/
structure SSGQ where
  base : SSG
  ext : ExtraGQ

/-- `SessionStructure::default()` in `SSGQ`. -/
def SSGQ.empty : SSGQ := ⟨SSG.empty, ExtraGQ.empty⟩

/-- Project `SSGQ` to `L1GX.SSGX` (dropping `ext.pq`). -/
def SSGQ.toSSGX (v : SSGQ) : SSGX := ⟨v.base, v.ext.toExtraG⟩

/-- Lift `L1GX.SSGX` to `SSGQ` with a given `pq` (default `[]`). -/
def SSGX.toSSGQ (v : SSGX) (pq : List (BitVec 8) := []) : SSGQ :=
  ⟨v.base, ExtraG.toExtraGQ v.ext pq⟩

@[simp] theorem toExtraGQ_empty : ExtraG.toExtraGQ ExtraG.empty [] = ExtraGQ.empty := rfl
@[simp] theorem toExtraG_empty : ExtraGQ.empty.toExtraG = ExtraG.empty := rfl
@[simp] theorem toSSGQ_empty : SSGX.toSSGQ SSGX.empty [] = SSGQ.empty := rfl
@[simp] theorem toSSGX_empty : SSGQ.empty.toSSGX = SSGX.empty := rfl

theorem ext_eq_empty_iff_toExtraG_and_pq (e : ExtraGQ) :
    e = ExtraGQ.empty ↔ e.toExtraG = ExtraG.empty ∧ e.pq = [] := by
  cases e
  simp [ExtraGQ.empty, ExtraGQ.toExtraG, ExtraG.empty]
  tauto

/-! ## `SessionStructure` spatial layout (`prostSSGQAt`) -/

/-- The prost `SessionStructure` at `ss` (344 bytes) holding `v : SSGQ`:
`L1GX.prostSSGXAt` with `pq_ratchet_state` at `ss + 0x78` holding `v.ext.pq` instead of `[]`. -/
def prostSSGQAt (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
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

/-- When `v.ext.pq = []`, `prostSSGQAt` is identical to `L1GX.prostSSGXAt` on `v.toSSGX`. -/
theorem prostSSGQAt_empty_pq (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) (hpq : v.ext.pq = []) :
    prostSSGQAt A ss v = prostSSGXAt A ss v.toSSGX := by
  unfold prostSSGQAt prostSSGXAt SSGQ.toSSGX ExtraGQ.toExtraG
  rw [hpq]
  rfl

/-- Lifting `v : SSGX` with `v.ext.pq` gives `prostSSGXAt A ss v`. -/
theorem prostSSGQAt_of_ssgx (A : RustAlloc) (ss : BitVec 64) (v : SSGX) :
    prostSSGQAt A ss (SSGX.toSSGQ v v.ext.pq) = prostSSGXAt A ss v := rfl

/-- With `ExtraGQ.empty`, `prostSSGQAt` is `DeserializeGeneral.prostSSGAt`. -/
theorem prostSSGQAt_empty (A : RustAlloc) (ss : BitVec 64) (v : SSG) :
    prostSSGQAt A ss ⟨v, ExtraGQ.empty⟩ = prostSSGAt A ss v := by
  rw [prostSSGQAt_empty_pq A ss ⟨v, ExtraGQ.empty⟩ rfl]
  exact prostSSGXAt_empty A ss v

/-! ## Field syntax and semantics (`GenFieldQ`) -/

/-- One field of an `encSession s` in `DeserializeScopeP_Q NonEmptyV1Q`, adding tag 15 (`pq`). -/
inductive GenFieldQ where
  | base (f : GenField)
  | pendingId (i : BitVec 32) (k : List (BitVec 8))
  | pendingSpk (pid : Option (BitVec 32)) (k : List (BitVec 8)) (spk : BitVec 32)
  | remReg (v : BitVec 32)
  | locReg (v : BitVec 32)
  | abk (b : List (BitVec 8))
  | kyber (i : BitVec 32) (ct : List (BitVec 8))
  | pq (b : List (BitVec 8))

/-- Embed a `L1GX.GenFieldX` into `GenFieldQ`. -/
def GenFieldX.toGenFieldQ : GenFieldX → GenFieldQ
  | .base f => .base f
  | .pendingId i k => .pendingId i k
  | .pendingSpk pid k spk => .pendingSpk pid k spk
  | .remReg v => .remReg v
  | .locReg v => .locReg v
  | .abk b => .abk b
  | .kyber i ct => .kyber i ct
  | .pq b => .pq b

/-- Whether a `L1GX.GenFieldX` is a non-`pq` field (tags 1–14). -/
def GenFieldX.NoPq : GenFieldX → Prop
  | .pq _ => False
  | _ => True

/-- The protobuf field number of a `GenFieldQ`. -/
def GenFieldQ.tag : GenFieldQ → Nat
  | .base f => f.tag
  | .pendingId _ _ => 9
  | .pendingSpk _ _ _ => 9
  | .remReg _ => 10
  | .locReg _ => 11
  | .abk _ => 13
  | .kyber _ _ => 14
  | .pq _ => 15

/-- The wire type of a `GenFieldQ`. -/
def GenFieldQ.wt : GenFieldQ → WireType
  | .base f => f.wt
  | .remReg _ | .locReg _ => .varint
  | _ => .lengthDelimited

/-- The payload bytes of a `GenFieldQ` after its key byte. -/
def GenFieldQ.payload : GenFieldQ → List (BitVec 8)
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

/-- Encoded bytes of a `GenFieldQ`: key followed by payload. -/
def GenFieldQ.enc (fl : GenFieldQ) : List (BitVec 8) :=
  encodeKey fl.tag fl.wt ++ fl.payload

/-- `prost`'s `SessionStructure::merge_field` action on `SSGQ`. -/
def SSGQ.apply (v : SSGQ) : GenFieldQ → SSGQ
  | .base f => ⟨v.base.apply f, v.ext⟩
  | .pendingId i k => ⟨{ v.base with pending := some k }, { v.ext with pid := some i }⟩
  | .pendingSpk pid k spk =>
      ⟨{ v.base with pending := some k }, { v.ext with pid := pid, spkId := spk }⟩
  | .remReg r => ⟨v.base, { v.ext with remReg := r }⟩
  | .locReg l => ⟨v.base, { v.ext with locReg := l }⟩
  | .abk b => ⟨v.base, { v.ext with abk := b }⟩
  | .kyber i ct => ⟨v.base, { v.ext with kyber := some (i, ct) }⟩
  | .pq b => ⟨v.base, { v.ext with pq := b }⟩

/-- Payload well-formedness of a `GenFieldQ` (`pq` requires `b.length < 2 ^ 32`, i.e. `NonEmptyV1Q b`). -/
def GenFieldQ.Ok : GenFieldQ → Prop
  | .base f => f.Ok
  | .pendingId _ k => k.length = 33
  | .pendingSpk _ k spk => k.length = 33 ∧ spk ≠ 0#32
  | .remReg _ | .locReg _ => True
  | .abk b => b.length = 33
  | .kyber _ ct => ct.length = 1569
  | .pq b => b.length < 2 ^ 32

/-- Freshness side condition of a `GenFieldQ` against the decoded value `v` before it. -/
def GenFieldQ.Fresh (v : SSGQ) : GenFieldQ → Prop
  | .base f => v.ext = ExtraGQ.empty ∧ f.Fresh v.base
  | .pendingId _ _ => v.base.pending = none ∧ v.ext = ExtraGQ.empty
  | .pendingSpk _ _ _ => v.base.pending = none ∧ v.ext = ExtraGQ.empty
  | .remReg _ => v.ext.remReg = 0 ∧ v.ext.pq = []
  | .locReg _ => v.ext.locReg = 0 ∧ v.ext.pq = []
  | .abk _ => v.ext.abk = [] ∧ v.ext.pq = []
  | .kyber _ _ => v.ext.kyber = none ∧ v.ext.pq = []
  | .pq _ => v.ext.pq = []

@[simp] theorem toGenFieldQ_tag (fx : GenFieldX) :
    (GenFieldX.toGenFieldQ fx).tag = fx.tag := by
  cases fx <;> rfl

@[simp] theorem toGenFieldQ_wt (fx : GenFieldX) :
    (GenFieldX.toGenFieldQ fx).wt = fx.wt := by
  cases fx <;> rfl

@[simp] theorem toGenFieldQ_payload (fx : GenFieldX) :
    (GenFieldX.toGenFieldQ fx).payload = fx.payload := by
  cases fx <;> rfl

@[simp] theorem toGenFieldQ_enc (fx : GenFieldX) :
    (GenFieldX.toGenFieldQ fx).enc = fx.enc := by
  cases fx <;> rfl

theorem toGenFieldQ_ok (fx : GenFieldX) (hnpq : GenFieldX.NoPq fx := by trivial) :
    (GenFieldX.toGenFieldQ fx).Ok ↔ fx.Ok := by
  cases fx with
  | pq _ => cases hnpq
  | _ => rfl

theorem toGenFieldQ_fresh_iff (v : SSGQ) (fx : GenFieldX) :
    (GenFieldX.toGenFieldQ fx).Fresh v ↔ fx.Fresh v.toSSGX ∧ v.ext.pq = [] := by
  cases fx <;>
    simp only [GenFieldX.toGenFieldQ, GenFieldQ.Fresh, GenFieldX.Fresh,
      SSGQ.toSSGX, ExtraGQ.toExtraG, ext_eq_empty_iff_toExtraG_and_pq] <;>
    tauto

theorem apply_toGenFieldQ (v : SSGQ) (fx : GenFieldX) (hnpq : GenFieldX.NoPq fx := by trivial) :
    v.apply (GenFieldX.toGenFieldQ fx) = SSGX.toSSGQ (v.toSSGX.apply fx) v.ext.pq := by
  rcases v with ⟨b, ⟨pid, spkId, remReg, locReg, abk, pq, kyber⟩⟩
  cases fx with
  | pq _ => cases hnpq
  | _ => rfl

theorem apply_toGenFieldQ_toSSGX (v : SSGQ) (fx : GenFieldX)
    (hnpq : GenFieldX.NoPq fx := by trivial) :
    (v.apply (GenFieldX.toGenFieldQ fx)).toSSGX = v.toSSGX.apply fx := by
  rcases v with ⟨b, ⟨pid, spkId, remReg, locReg, abk, pq, kyber⟩⟩
  cases fx with
  | pq _ => cases hnpq
  | _ => rfl

theorem apply_toGenFieldQ_pq (v : SSGQ) (fx : GenFieldX)
    (hnpq : GenFieldX.NoPq fx := by trivial) :
    (v.apply (GenFieldX.toGenFieldQ fx)).ext.pq = v.ext.pq := by
  rcases v with ⟨b, ⟨pid, spkId, remReg, locReg, abk, pq, kyber⟩⟩
  cases fx with
  | pq _ => cases hnpq
  | _ => rfl

/-! ## Record field lists (`genFieldsQ`, `recFieldsQ`, `ssgqAfter`, `ssgqOf`) -/

def pendingFieldQ (o : Option PendingPreKey) : List GenFieldQ :=
  (pendingFieldX o).map GenFieldX.toGenFieldQ

def genFieldsQ (s : Session (List (BitVec 8))) : List GenFieldQ :=
  (genFieldsX { s with state := { s.state with pqRatchetState := [] } }).map GenFieldX.toGenFieldQ ++
    (if s.state.pqRatchetState = [] then [] else [GenFieldQ.pq s.state.pqRatchetState])

theorem noPq_of_mem_genFieldsX {s : Session (List (BitVec 8))}
    (hpq : s.state.pqRatchetState = []) {fx : GenFieldX} (hfx : fx ∈ genFieldsX s) :
    GenFieldX.NoPq fx := by
  unfold genFieldsX at hfx
  simp only [hpq, ↓reduceIte, List.append_nil, List.mem_append, List.mem_map] at hfx
  rcases hfx with (((((⟨f, _, rfl⟩ | h9) | h10) | h11) | h13) | h14)
  · trivial
  · rcases hp : s.pendingPreKey with _ | p <;> rw [hp] at h9
    · cases h9
    · dsimp only [pendingFieldX] at h9
      split_ifs at h9
      · rcases hid : p.preKeyId with _ | i <;> rw [hid] at h9 <;>
          simp only [List.mem_singleton] at h9 <;> subst h9 <;> trivial
      · simp only [List.mem_singleton] at h9; subst h9; trivial
  · split_ifs at h10
    · cases h10
    · simp only [List.mem_singleton] at h10; subst h10; trivial
  · split_ifs at h11
    · cases h11
    · simp only [List.mem_singleton] at h11; subst h11; trivial
  · split_ifs at h13
    · cases h13
    · simp only [List.mem_singleton] at h13; subst h13; trivial
  · rcases hk : s.pendingKyberPreKey with _ | k <;> rw [hk] at h14
    · cases h14
    · simp only [List.mem_singleton] at h14; subst h14; trivial

def recFieldsQ (r : SessionRecord (List (BitVec 8))) : List GenFieldQ :=
  match r.currentSession with
  | some s => genFieldsQ s
  | none => []

def ssgqAfter (r : SessionRecord (List (BitVec 8))) (k : Nat) : SSGQ :=
  ((recFieldsQ r).take k).foldl SSGQ.apply SSGQ.empty

def ssgqOf (s : Session (List (BitVec 8))) : SSGQ :=
  ⟨ssgOf s,
    ⟨s.pendingPreKey.bind (·.preKeyId),
     (s.pendingPreKey.map (·.signedPreKeyId)).getD 0,
     s.remoteRegistrationId,
     s.localRegistrationId,
     s.aliceBaseKey,
     s.state.pqRatchetState,
     s.pendingKyberPreKey.map (fun k => (k.preKeyId, k.ciphertext))⟩⟩

theorem ssgqOf_eq_toSSGQ (s : Session (List (BitVec 8))) :
    ssgqOf s = SSGX.toSSGQ (ssgxOf s) s.state.pqRatchetState := rfl

/-! ## W-stack `merge_field` contract (`mergeFieldQSpecAtW`, `MergeFieldQOkAtW`) -/

structure MergeFieldQGhost where
  ss : BitVec 64
  v : SSGQ
  fld : GenFieldQ
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  tail : List (BitVec 8)

def mergeFieldQSpecAtW (img : Obj.Image) (P : GenFieldQ → Prop) : Spec MergeFieldQGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧ x.fld.Fresh x.v ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 62 ∧
      img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      prostSSGQAt A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗
      stackAt s.sp mergeFieldStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      prostSSGQAt A0 x.ss (x.v.apply x.fld) ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt s0.sp mergeFieldStackX
  onPanic := allocPanic

def MergeFieldQOkAtW (img : Obj.Image) (ext : String → Option (State → State))
    (P : GenFieldQ → Prop) : Prop :=
  OkAtX img.base ext mergeFieldName (mergeFieldQSpecAtW img P)

theorem mergeFieldQSpecAtW_pre_iff (img : Obj.Image) {P : GenFieldQ → Prop}
    {x : MergeFieldQGhost} {s0 : State} {R : SepProp} :
    (s0.mem ⊨ (mergeFieldQSpecAtW img P).pre x s0 ∗ R) ↔
      P x.fld ∧ (s0.mem ⊨ (mergeFieldQSpecAtW img (fun _ => True)).pre x s0 ∗ R) := by
  simp only [mergeFieldQSpecAtW, sepConj_assoc, satisfies_pure_sepConj]
  tauto

theorem mergeFieldQOkAtW_of_imp (img : Obj.Image) (ext : String → Option (State → State))
    {P Q : GenFieldQ → Prop} (h : ∀ fl, P fl → Q fl)
    (hQ : MergeFieldQOkAtW img ext Q) :
    MergeFieldQOkAtW img ext P := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  rw [mergeFieldQSpecAtW_pre_iff] at hpre
  exact hQ.mono_outcome x R s0 hpc hrun
    (mergeFieldQSpecAtW_pre_iff img |>.mpr ⟨h x.fld hpre.1, hpre.2⟩) hal fun _ hout => hout

theorem mergeFieldQOkAtW_or (img : Obj.Image) (ext : String → Option (State → State))
    {P Q : GenFieldQ → Prop}
    (hP : MergeFieldQOkAtW img ext P) (hQ : MergeFieldQOkAtW img ext Q) :
    MergeFieldQOkAtW img ext (fun fl => P fl ∨ Q fl) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  rw [mergeFieldQSpecAtW_pre_iff] at hpre
  rcases hpre.1 with hp | hq
  · exact hP.mono_outcome x R s0 hpc hrun
      (mergeFieldQSpecAtW_pre_iff img |>.mpr ⟨hp, hpre.2⟩) hal fun _ hout => hout
  · exact hQ.mono_outcome x R s0 hpc hrun
      (mergeFieldQSpecAtW_pre_iff img |>.mpr ⟨hq, hpre.2⟩) hal fun _ hout => hout

/-! ## `SessionRecord::deserialize` loop and contract definitions -/

def deserLocalsQ (L p : BitVec 64) (bs rest : List (BitVec 8)) (v : SSGQ) : SepProp :=
  memRegion L 0x3f8 ∗ Prost.sliceCursorAfter (L + 0x3f8#64) p bs rest ∗
    ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
    prostSSGQAt A0 (L + 0x420#64) v ∗ memRegion (L + 0x578#64) 0x170 ∗
    ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ memRegion (L + 0x6f0#64) 0x20

theorem deserLocalsQ_empty_pq (L p : BitVec 64) (bs rest : List (BitVec 8)) (v : SSGQ)
    (hpq : v.ext.pq = []) :
    deserLocalsQ L p bs rest v = deserLocalsX L p bs rest v.toSSGX := by
  unfold deserLocalsQ deserLocalsX
  rw [prostSSGQAt_empty_pq A0 (L + 0x420#64) v hpq]

theorem deserLocalsQ_base (L p : BitVec 64) (bs rest : List (BitVec 8)) (v : SSG) :
    deserLocalsQ L p bs rest ⟨v, ExtraGQ.empty⟩ = deserLocalsG L p bs rest v := by
  unfold deserLocalsQ deserLocalsG
  rw [prostSSGQAt_empty]

def deserOutRecordQ (out : BitVec 64) (r : SessionRecord (List (BitVec 8))) : SepProp :=
  (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64) ∗
    prostSSGQAt A0 (out + 0x18#64) (ssgqAfter r (recFieldsQ r).length)

def deserOutRawQ (x : DeserializeGenGhost) (s0 sf : State) : SepProp :=
  ⌜sf.trace = s0.trace⌝ ∗ (x.p ↦ₛ encodeRecord x.r) ∗ deserOutRecordQ x.out x.r ∗
    stackAt s0.sp recDeserializeStack

noncomputable def deserializeQSpecAtW (img : Obj.Image) : Spec DeserializeGenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.p ∧ s.readReg64 .x1 = BitVec.ofNat 64 (encodeRecord x.r).length ∧
      s.readReg64 .x8 = x.out ∧ DeserializeScopeP_Q NonEmptyV1Q x.r ∧
      img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      (x.p ↦ₛ encodeRecord x.r) ∗ memRegion x.out 368 ∗ stackAt s.sp recDeserializeStack
  post := (deserializeGenSpecAt img).post
  onPanic := allocPanic

noncomputable def deserializeQExactSpecAtW (img : Obj.Image) : Spec DeserializeGenGhost where
  pre := (deserializeQSpecAtW img).pre
  post := fun x s0 sf => deserOutRawQ x s0 sf
  onPanic := allocPanic

abbrev DeserStepQAtW (img : Obj.Image) (ext : String → Option (State → State))
    (x : DeserializeGenGhost) (R : SepProp) (s0 s : State) (Q : State → Prop) : Prop :=
  SegStepG (SP2Ext img.base ext) (deserializeQSpecAtW img) x R s0 s Q

def DeserLoopQAtW (img : Obj.Image) (ext : String → Option (State → State))
    (x : DeserializeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State) : Prop :=
  s.pc = deserPCAtX img ext 0x254#64 ∧ s.status = .Running ∧
    (s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) ∧
    s.symtab = img.symtab ∧ img.FrozenLoaded s ∧
    s.sp = deserSpL s0.sp ∧ s.spAligned = true ∧ s.readReg64 .x29 = deserSpL s0.sp + 0x710#64 ∧
    s.readReg64 .x19 = x.out ∧ s.readReg64 .x20 = 0#64 ∧
    s.readReg64 .x23 = deserSpL s0.sp + 0x408#64 ∧
    (s.mem ⊨ deserLocalsQ (deserSpL s0.sp) x.p (encodeRecord x.r)
        (((recFieldsQ x.r).drop k).flatMap GenFieldQ.enc) (ssgqAfter x.r k) ∗
      memRegion x.out 368 ∗ stackAt (deserSpL s0.sp) deserCalleeStack ∗ deserSaved s0 ∗ R)

def DeserRetQAtW (x : DeserializeGenGhost) (R : SepProp) (s0 sf : State) : Prop :=
  Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧ (sf.mem ⊨ deserOutRawQ x s0 sf ∗ R)

/-! ## `prostSSGXNoPqAt`, `pendingAt9P`, and `rfl` bridges -/

/-- The 48-byte `pending_pre_key: Option<PendingPreKey>` field slice at `ss + 0xf8 .. ss + 0x128`. -/
def pendingAt9P (A : RustAlloc) (ss : BitVec 64) (v : SSGX) : SepProp :=
  match v.base.pending with
  | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
  | some k => vecU8 A (ss + 0xf8#64) k ∗
      pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
        ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)

/-- `prostSSGXAt` without the `vecU8 A (ss + 0x78#64) []` pin (`MF14AuxW` form). -/
def prostSSGXNoPqAt_x14 (A : RustAlloc) (ss : BitVec 64) (v : SSGX) : SepProp :=
  vecU8 A ss v.base.lik ∗ vecU8 A (ss + 0x18#64) v.base.rik ∗ vecU8 A (ss + 0x30#64) v.base.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A (ss + 0x60#64) v.ext.abk ∗
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

/-- `prostSSGXAt` without the `vecU8 A (ss + 0x78#64) []` pin (`MF9PAuxW` form). -/
def prostSSGXNoPqAt_x9pW (A : RustAlloc) (ss : BitVec 64) (v : SSGX) : SepProp :=
  vecU8 A ss v.base.lik ∗ vecU8 A (ss + 0x18#64) v.base.rik ∗ vecU8 A (ss + 0x30#64) v.base.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A (ss + 0x60#64) v.ext.abk ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    pendingAt9P A ss v ∗
    kyberAt A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

/-- Canonical `prostSSGXAt` without the `pq_ratchet_state` (`+0x78`) slot. -/
abbrev prostSSGXNoPqAt (A : RustAlloc) (ss : BitVec 64) (v : SSGX) : SepProp :=
  prostSSGXNoPqAt_x14 A ss v

@[simp] theorem prostSSGXNoPqAt_eq_x9pW (A : RustAlloc) (ss : BitVec 64) (v : SSGX) :
    prostSSGXNoPqAt A ss v = prostSSGXNoPqAt_x9pW A ss v := rfl

@[simp] theorem prostSSGXNoPqAt_eq_x14 (A : RustAlloc) (ss : BitVec 64) (v : SSGX) :
    prostSSGXNoPqAt A ss v = prostSSGXNoPqAt_x14 A ss v := rfl

theorem prostSSGXNoPqAt_x9pW_eq_x14 (A : RustAlloc) (ss : BitVec 64) (v : SSGX) :
    prostSSGXNoPqAt_x9pW A ss v = prostSSGXNoPqAt_x14 A ss v := rfl

theorem prostSSGQAt_eq_noPq_sep_pq (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) :
    prostSSGQAt A ss v = prostSSGXNoPqAt A ss v.toSSGX ∗ vecU8 A (ss + 0x78#64) v.ext.pq := by
  unfold prostSSGQAt prostSSGXNoPqAt prostSSGXNoPqAt_x14 SSGQ.toSSGX ExtraGQ.toExtraG
  ac_rfl

theorem prostSSGQAt_eq_x9pW_sep_pq (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) :
    prostSSGQAt A ss v = prostSSGXNoPqAt_x9pW A ss v.toSSGX ∗ vecU8 A (ss + 0x78#64) v.ext.pq :=
  prostSSGQAt_eq_noPq_sep_pq A ss v

theorem prostSSGQAt_eq_x14_sep_pq (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) :
    prostSSGQAt A ss v = prostSSGXNoPqAt_x14 A ss v.toSSGX ∗ vecU8 A (ss + 0x78#64) v.ext.pq :=
  prostSSGQAt_eq_noPq_sep_pq A ss v

/-! ## Arbitrary-allocator (`A : RustAlloc`) `*WA` contracts -/

def mergeFieldQSpecAtWA (A : RustAlloc) (img : Obj.Image) (P : GenFieldQ → Prop) : Spec MergeFieldQGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧ x.fld.Fresh x.v ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 62 ∧
      img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      prostSSGQAt A x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗
      A.pool ∗ stackAt s.sp mergeFieldStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      prostSSGQAt A x.ss (x.v.apply x.fld) ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      A.pool ∗ stackAt s0.sp mergeFieldStackX
  onPanic := allocPanic

def MergeFieldQOkAtWA (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (P : GenFieldQ → Prop) : Prop :=
  OkAtX img.base ext mergeFieldName (mergeFieldQSpecAtWA A img P)

theorem mergeFieldQSpecAtWA_pre_iff (A : RustAlloc) (img : Obj.Image) {P : GenFieldQ → Prop}
    {x : MergeFieldQGhost} {s0 : State} {R : SepProp} :
    (s0.mem ⊨ (mergeFieldQSpecAtWA A img P).pre x s0 ∗ R) ↔
      P x.fld ∧ (s0.mem ⊨ (mergeFieldQSpecAtWA A img (fun _ => True)).pre x s0 ∗ R) := by
  simp only [mergeFieldQSpecAtWA, sepConj_assoc, satisfies_pure_sepConj]
  tauto

theorem mergeFieldQOkAtWA_of_imp (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    {P Q : GenFieldQ → Prop} (h : ∀ fl, P fl → Q fl)
    (hQ : MergeFieldQOkAtWA img A ext Q) :
    MergeFieldQOkAtWA img A ext P := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  rw [mergeFieldQSpecAtWA_pre_iff] at hpre
  exact hQ.mono_outcome x R s0 hpc hrun
    (mergeFieldQSpecAtWA_pre_iff A img |>.mpr ⟨h x.fld hpre.1, hpre.2⟩) hal fun _ hout => hout

theorem mergeFieldQOkAtWA_or (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    {P Q : GenFieldQ → Prop}
    (hP : MergeFieldQOkAtWA img A ext P) (hQ : MergeFieldQOkAtWA img A ext Q) :
    MergeFieldQOkAtWA img A ext (fun fl => P fl ∨ Q fl) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  rw [mergeFieldQSpecAtWA_pre_iff] at hpre
  rcases hpre.1 with hp | hq
  · exact hP.mono_outcome x R s0 hpc hrun
      (mergeFieldQSpecAtWA_pre_iff A img |>.mpr ⟨hp, hpre.2⟩) hal fun _ hout => hout
  · exact hQ.mono_outcome x R s0 hpc hrun
      (mergeFieldQSpecAtWA_pre_iff A img |>.mpr ⟨hq, hpre.2⟩) hal fun _ hout => hout

def deserLocalsQA (A : RustAlloc) (L p : BitVec 64) (bs rest : List (BitVec 8)) (v : SSGQ) : SepProp :=
  memRegion L 0x3f8 ∗ Prost.sliceCursorAfter (L + 0x3f8#64) p bs rest ∗
    ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
    prostSSGQAt A (L + 0x420#64) v ∗ memRegion (L + 0x578#64) 0x170 ∗
    ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ memRegion (L + 0x6f0#64) 0x20

@[simp] theorem deserLocalsQA_A0 : deserLocalsQA A0 = deserLocalsQ := rfl

theorem deserLocalsQA_base (A : RustAlloc) (L p : BitVec 64) (bs rest : List (BitVec 8)) (v : SSG) :
    deserLocalsQA A L p bs rest ⟨v, ExtraGQ.empty⟩ = deserLocalsGA A L p bs rest v := by
  unfold deserLocalsQA deserLocalsGA
  rw [prostSSGQAt_empty]

def deserOutRecordQA (A : RustAlloc) (out : BitVec 64) (r : SessionRecord (List (BitVec 8))) : SepProp :=
  (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64) ∗
    prostSSGQAt A (out + 0x18#64) (ssgqAfter r (recFieldsQ r).length)

@[simp] theorem deserOutRecordQA_A0 : deserOutRecordQA A0 = deserOutRecordQ := rfl

def deserOutRawQA (A : RustAlloc) (x : DeserializeGenGhost) (s0 sf : State) : SepProp :=
  ⌜sf.trace = s0.trace⌝ ∗ (x.p ↦ₛ encodeRecord x.r) ∗ deserOutRecordQA A x.out x.r ∗
    A.pool ∗ stackAt s0.sp recDeserializeStack

/-- General `Q`-scope `SessionRecord::deserialize` contract carrying `A.pool` and `sessionRecordAt A`
(`= sessDeserializeExtSpec scopeKit A img` definitionally by `rfl`). -/
noncomputable def deserializeQSpecAtWA (A : RustAlloc) (img : Obj.Image) : Spec DeserializeGenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.p ∧ s.readReg64 .x1 = BitVec.ofNat 64 (encodeRecord x.r).length ∧
      s.readReg64 .x8 = x.out ∧ DeserializeScopeP_Q NonEmptyV1Q x.r ∧
      img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      (x.p ↦ₛ encodeRecord x.r) ∗ memRegion x.out 368 ∗ A.pool ∗ stackAt s.sp recDeserializeStack
  post := (deserializeGenSpecAtA A img).post
  onPanic := allocPanic

noncomputable def deserializeQExactSpecAtWA (A : RustAlloc) (img : Obj.Image) : Spec DeserializeGenGhost where
  pre := (deserializeQSpecAtWA A img).pre
  post := fun x s0 sf => deserOutRawQA A x s0 sf
  onPanic := allocPanic

abbrev DeserStepQAtWA (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (x : DeserializeGenGhost) (R : SepProp) (s0 s : State) (Q : State → Prop) : Prop :=
  SegStepG (SP2Ext img.base ext) (deserializeQSpecAtWA A img) x R s0 s Q

def DeserLoopQAtWA (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (x : DeserializeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State) : Prop :=
  s.pc = deserPCAtX img ext 0x254#64 ∧ s.status = .Running ∧
    (s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) ∧
    s.symtab = img.symtab ∧ img.FrozenLoaded s ∧
    s.sp = deserSpL s0.sp ∧ s.spAligned = true ∧ s.readReg64 .x29 = deserSpL s0.sp + 0x710#64 ∧
    s.readReg64 .x19 = x.out ∧ s.readReg64 .x20 = 0#64 ∧
    s.readReg64 .x23 = deserSpL s0.sp + 0x408#64 ∧
    (s.mem ⊨ deserLocalsQA A (deserSpL s0.sp) x.p (encodeRecord x.r)
        (((recFieldsQ x.r).drop k).flatMap GenFieldQ.enc) (ssgqAfter x.r k) ∗
      memRegion x.out 368 ∗ A.pool ∗ stackAt (deserSpL s0.sp) deserCalleeStack ∗ deserSaved s0 ∗ R)

def DeserRetQAtWA (A : RustAlloc) (x : DeserializeGenGhost) (R : SepProp) (s0 sf : State) : Prop :=
  Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧ (sf.mem ⊨ deserOutRawQA A x s0 sf ∗ R)

/-! ## Relocatable `[LibsignalPlacement]` definitions (Blocks `15` and `46`) -/

section Placed

open Arm64.Obj CryptoVerification.E2E.Record.Placed

theorem L1_B3DeserQ_Defs_Placed : True := trivial

/-- Image-free base contract of `SessionStructure::merge_field` (block `15`) on one `GenFieldQ`
restricted by `P`, at `mergeFieldStackX`. -/
def mergeFieldQRawSpecW (P : GenFieldQ → Prop) : Spec MergeFieldQGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧ x.fld.Fresh x.v ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 62⌝ ∗
      prostSSGQAt A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗
      stackAt s.sp mergeFieldStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      prostSSGQAt A0 x.ss (x.v.apply x.fld) ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt s0.sp mergeFieldStackX
  onPanic := allocPanic

/-- Relocatable `[LibsignalPlacement]` contract of `SessionStructure::merge_field` (block `15`) on
`GenFieldQ` restricted by `P`, carrying `LibsignalCodeRoLoaded lsmpl`. -/
abbrev mergeFieldQPlacedSpecW [LibsignalPlacement] (P : GenFieldQ → Prop) : Spec MergeFieldQGhost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (mergeFieldQRawSpecW P)

/-- Relocatable `SessionStructure::merge_field` (block `15`) contract on `lsProg_15 H`. -/
def MergeFieldQPlacedOkW [LibsignalPlacement] (H : LibsignalHooks)
    (P : GenFieldQ → Prop) : Prop :=
  subroutine_ok (lsProg_15 H) (blkPl_15).base (mergeFieldQPlacedSpecW P)

theorem mergeFieldQPlacedSpecW_pre_iff [LibsignalPlacement] {P : GenFieldQ → Prop}
    {x : MergeFieldQGhost} {s0 : State} {R : SepProp} :
    (s0.mem ⊨ (mergeFieldQPlacedSpecW P).pre x s0 ∗ R) ↔
      P x.fld ∧ (s0.mem ⊨ (mergeFieldQPlacedSpecW (fun _ => True)).pre x s0 ∗ R) := by
  simp only [mergeFieldQRawSpecW, sepConj_assoc, satisfies_pure_sepConj]
  tauto

theorem mergeFieldQPlacedOkW_of_imp [LibsignalPlacement] (H : LibsignalHooks)
    {P Q : GenFieldQ → Prop} (h : ∀ fl, P fl → Q fl)
    (hQ : MergeFieldQPlacedOkW H Q) :
    MergeFieldQPlacedOkW H P := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  rw [mergeFieldQPlacedSpecW_pre_iff] at hpre
  exact hQ.mono_outcome x R s0 hpc hrun
    (mergeFieldQPlacedSpecW_pre_iff.mpr ⟨h x.fld hpre.1, hpre.2⟩) hal fun _ hout => hout

theorem mergeFieldQPlacedOkW_or [LibsignalPlacement] (H : LibsignalHooks)
    {P Q : GenFieldQ → Prop}
    (hP : MergeFieldQPlacedOkW H P) (hQ : MergeFieldQPlacedOkW H Q) :
    MergeFieldQPlacedOkW H (fun fl => P fl ∨ Q fl) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  rw [mergeFieldQPlacedSpecW_pre_iff] at hpre
  rcases hpre.1 with hp | hq
  · exact hP.mono_outcome x R s0 hpc hrun
      (mergeFieldQPlacedSpecW_pre_iff.mpr ⟨hp, hpre.2⟩) hal fun _ hout => hout
  · exact hQ.mono_outcome x R s0 hpc hrun
      (mergeFieldQPlacedSpecW_pre_iff.mpr ⟨hq, hpre.2⟩) hal fun _ hout => hout

/-- Image-free base contract of `SessionRecord::deserialize` (block `46`) on `DeserializeScopeP_Q NonEmptyV1Q`. -/
noncomputable def deserializeQRawSpecW : Spec DeserializeGenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.p ∧ s.readReg64 .x1 = BitVec.ofNat 64 (encodeRecord x.r).length ∧
      s.readReg64 .x8 = x.out ∧ DeserializeScopeP_Q NonEmptyV1Q x.r⌝ ∗
      (x.p ↦ₛ encodeRecord x.r) ∗ memRegion x.out 368 ∗ stackAt s.sp recDeserializeStack
  post := deserializeGenPost
  onPanic := allocPanic

/-- Relocatable `[LibsignalPlacement]` contract of `SessionRecord::deserialize` (block `46`) on
`DeserializeScopeP_Q NonEmptyV1Q`, carrying `LibsignalCodeRoLoaded lsmpl`. -/
noncomputable abbrev deserializeQPlacedSpecW [LibsignalPlacement] : Spec DeserializeGenGhost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl deserializeQRawSpecW

/-- Image-free exact contract of `SessionRecord::deserialize` (block `46`) on `DeserializeScopeP_Q NonEmptyV1Q`. -/
noncomputable def deserializeQExactRawSpecW : Spec DeserializeGenGhost where
  pre := deserializeQRawSpecW.pre
  post := fun x s0 sf => deserOutRawQ x s0 sf
  onPanic := allocPanic

/-- Relocatable `[LibsignalPlacement]` exact contract of `SessionRecord::deserialize` (block `46`)
on `DeserializeScopeP_Q NonEmptyV1Q`, carrying `LibsignalCodeRoLoaded lsmpl`. -/
noncomputable abbrev deserializeQExactPlacedSpecW [LibsignalPlacement] : Spec DeserializeGenGhost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl deserializeQExactRawSpecW

/-- One segment step of relocatable `Q`-scope deserialize on `lsProg_46 H`. -/
abbrev DeserStepQPlacedW [LibsignalPlacement] (H : LibsignalHooks)
    (x : DeserializeGenGhost) (R : SepProp) (s0 s : State) (Q : State → Prop) : Prop :=
  SegStepG (lsProg_46 H) deserializeQPlacedSpecW x R s0 s Q

/-- Loop invariant at `(blkPl_46).base + 0x254` after `k` fields of `recFieldsQ x.r` under
`[LibsignalPlacement]`, carrying `LibsignalCodeRoLoaded lsmpl s.mem`. -/
def DeserLoopQPlacedW [LibsignalPlacement]
    (x : DeserializeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State) : Prop :=
  s.pc = deserPlacedPC 0x254#64 ∧ s.status = .Running ∧
    (s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) ∧
    LibsignalCodeRoLoaded lsmpl s.mem ∧
    s.sp = deserSpL s0.sp ∧ s.spAligned = true ∧ s.readReg64 .x29 = deserSpL s0.sp + 0x710#64 ∧
    s.readReg64 .x19 = x.out ∧ s.readReg64 .x20 = 0#64 ∧
    s.readReg64 .x23 = deserSpL s0.sp + 0x408#64 ∧
    (s.mem ⊨ deserLocalsQ (deserSpL s0.sp) x.p (encodeRecord x.r)
        (((recFieldsQ x.r).drop k).flatMap GenFieldQ.enc) (ssgqAfter x.r k) ∗
      memRegion x.out 368 ∗ stackAt (deserSpL s0.sp) deserCalleeStack ∗ deserSaved s0 ∗ R)

end Placed

end Symbolic.Swarm.TRREF.B3DeserQ
