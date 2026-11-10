/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop

/-!
# `PreKeySignalMessage::try_from`: Stack `ProtoPreKeySignalMessage` and Decode-Loop Interface

Defines the X25519 key-parsing helpers (`ecKeyParses`, `pkOf`), the 128-byte stack
`proto::wire::PreKeySignalMessage` predicates (`WirePreKeyGhost`, `wirePreKeyAt`,
`wirePreKeyOf`), and the decode-loop cut/postcondition predicates (`PreKeyLoopRegs`,
`PreKeyLoopExitState`, `PreKeyDecodeLoopOk`, `PreKeyDecodeLoopF4Ok`) at `+0x0e4..+0x460`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAt optVecU8At)
open CryptoVerification.LibsignalTripleRatchet.Wire (tryFromQp)
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## 1. Symbol name & stack budget -/

export CryptoVerification.E2E.Pqxdh.ResponderWire
  (preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack)

/-! ## 2. EC key predicate and `pkOf` lemmas -/

/-- Whether `b` begins with `0x05` (`djbType`) and has at least 33 bytes
(`PublicKey::deserialize` succeeds). -/
def ecKeyParses (b : List (BitVec 8)) : Bool :=
  b.head? == some 0x05#8 && 33 ≤ b.length

/-- the key `PublicKey::deserialize bk` returns; an all-zero dummy on `Err` (never reached
on paths guarded by `ecKeyParses bk = true`). -/
def pkOf (bk : List (BitVec 8)) : PublicKey :=
  match PublicKey.deserialize bk with
  | .ok k => k
  | .error _ => ⟨List.Vector.replicate 32 0#8⟩

/-- `ecKeyParses` is equivalent to `PublicKey::deserialize` succeeding. -/
theorem ecKeyParses_iff_deserialize_ok (bk : List (BitVec 8)) :
    ecKeyParses bk = true ↔ ∃ k, PublicKey.deserialize bk = .ok k := by
  cases bk with
  | nil => simp [ecKeyParses, PublicKey.deserialize]
  | cons t rest =>
    by_cases ht : t = djbType
    · subst ht
      by_cases hl : 32 ≤ rest.length
      · simp [ecKeyParses, PublicKey.deserialize, hl, djbType]
      · simp [ecKeyParses, PublicKey.deserialize, hl, djbType]
    · have ht' : t ≠ 0x05#8 := by simpa [djbType] using ht
      simp [ecKeyParses, PublicKey.deserialize, ht, ht']

/-- `PublicKey::deserialize bk = .ok k` implies `ecKeyParses bk = true`. -/
theorem ecKeyParses_of_deserialize_ok {bk : List (BitVec 8)} {k : PublicKey}
    (h : PublicKey.deserialize bk = .ok k) : ecKeyParses bk = true :=
  (ecKeyParses_iff_deserialize_ok bk).2 ⟨k, h⟩

/-- `pkOf` returns the deserialized key when `PublicKey.deserialize bk = .ok k`. -/
theorem pkOf_of_deserialize_ok {bk : List (BitVec 8)} {k : PublicKey}
    (h : PublicKey.deserialize bk = .ok k) : pkOf bk = k := by
  simp [pkOf, h]

/-- when `ecKeyParses bk = true`, the 32 stored key bytes are
`(bk.take 33).drop 1`. -/
theorem pkOf_bytes_of_ecKeyParses {bk : List (BitVec 8)} (h : ecKeyParses bk = true) :
    (pkOf bk).bytes.toList = (bk.take 33).drop 1 := by
  cases bk with
  | nil => simp [ecKeyParses] at h
  | cons t rest =>
    have h' : t = djbType ∧ 32 ≤ rest.length := by
      simp [ecKeyParses] at h
      exact ⟨h.1, by omega⟩
    obtain ⟨rfl, hl⟩ := h'
    simp [pkOf, PublicKey.deserialize, hl]

/-! ## 3. Stack `proto::wire::PreKeySignalMessage` representation -/

/-- Pins of the four `Option<Vec<u8>>` fields of the stack `proto::wire::PreKeySignalMessage`. -/
structure WirePreKeyGhost where
  kyberCt : VecPin
  baseKey : VecPin
  identityKey : VecPin
  message : VecPin

/-- The stack `proto::wire::PreKeySignalMessage` (128 bytes at `a = sp' + 312`) holding `m`. -/
def wirePreKeyAt (A : RustAlloc) (g : WirePreKeyGhost) (a : BitVec 64)
    (m : ProtoPreKeySignalMessage) : SepProp :=
  optVecU8At A g.kyberCt a m.kyberCiphertext ∗
    optVecU8At A g.baseKey (a + 0x18#64) m.baseKey ∗
    optVecU8At A g.identityKey (a + 0x30#64) m.identityKey ∗
    optVecU8At A g.message (a + 0x48#64) m.message ∗
    CryptoVerification.LibsignalTripleRatchet.Prost.optU32At (a + 0x60#64) m.registrationId ∗
    CryptoVerification.LibsignalTripleRatchet.Prost.optU32At (a + 0x68#64) m.preKeyId ∗
    CryptoVerification.LibsignalTripleRatchet.Prost.optU32At (a + 0x70#64) m.signedPreKeyId ∗
    CryptoVerification.LibsignalTripleRatchet.Prost.optU32At (a + 0x78#64) m.kyberPreKeyId

/-- Unpinned form (decode-loop invariant; analog of `wireSignalMessageOf`). -/
def wirePreKeyOf (A : RustAlloc) (a : BitVec 64) (m : ProtoPreKeySignalMessage) : SepProp :=
  ∃∗ g : WirePreKeyGhost, wirePreKeyAt A g a m

/-- The cells written by the init block (`+0x098..+0x0b4`: 4 flags `:= 0`, 4 caps `:= -1`) entail
`wirePreKeyOf A a Pksm.emptyProto`. -/
theorem emptyPreKey_cells_entails_wirePreKeyOf (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 16 ∗
    ((a + 0x18#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x18#64 + 8#64) 16 ∗
    ((a + 0x30#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x30#64 + 8#64) 16 ∗
    ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x48#64 + 8#64) 16 ∗
    ((a + 0x60#64) ↦₃₂ 0#32) ∗ memRegion (a + 0x60#64 + 4#64) 4 ∗
    ((a + 0x68#64) ↦₃₂ 0#32) ∗ memRegion (a + 0x68#64 + 4#64) 4 ∗
    ((a + 0x70#64) ↦₃₂ 0#32) ∗ memRegion (a + 0x70#64 + 4#64) 4 ∗
    ((a + 0x78#64) ↦₃₂ 0#32) ∗ memRegion (a + 0x78#64 + 4#64) 4 ⊢
      wirePreKeyOf A a Pksm.emptyProto := by
  refine Entails.trans ?_ (Entails.sepExists_intro
    (⟨⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩⟩ : WirePreKeyGhost))
  unfold wirePreKeyAt Pksm.emptyProto optVecU8At
    CryptoVerification.LibsignalTripleRatchet.Prost.optU32At
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.refl _

/-! ## 4. Decode-loop interface -/

/-- Registers invariant across the decode loop (`+0x0e4 .. +0x460`):
`x19 = sret`, `x20 = len`, `x21 = ptr`, `x22 = version byte` (read again at the Kyber check),
`x23 = sp' + 312`, `x25 = 1`, `x27 = 0x8000000000000002`. -/
structure PreKeyLoopRegs (sp' sret len ptr : BitVec 64) (vb : BitVec 8) (s : State) : Prop where
  sp : s.sp = sp'
  x29 : s.readReg64 .x29 = sp' + 512#64
  x27 : s.readReg64 .x27 = 0x8000000000000002#64
  x25 : s.readReg64 .x25 = 1#64
  x23 : s.readReg64 .x23 = sp' + 312#64
  x22 : s.readReg64 .x22 = vb.zeroExtend 64
  x21 : s.readReg64 .x21 = ptr
  x20 : s.readReg64 .x20 = len
  x19 : s.readReg64 .x19 = sret

/-- Memory at the loop exit `+0x460` for `res = Pksm.decodeProtoLoop fuel m bs`:
Ok ⇒ `x24 = 0` and the decoded struct; Err ⇒ `x24 ≠ 0`, a live `DecodeError`, and some struct. -/
def preKeyLoopExitMem (A : RustAlloc) (sp' ptr : BitVec 64) (bs : List (BitVec 8))
    (x24 : BitVec 64) (res : Option ProtoPreKeySignalMessage) : SepProp :=
  memRegion (sp' + 296#64) 16 ∗ (ptr ↦ₛ bs) ∗
    ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ memRegion (sp' + 448#64) 64 ∗
    A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
    match res with
    | some m' => ⌜x24 = 0#64⌝ ∗ wirePreKeyOf A (sp' + 312#64) m'
    | none =>
      ⌜x24 ≠ 0#64⌝ ∗ decodeErrorAt A x24 ∗ (∃∗ mErr, wirePreKeyOf A (sp' + 312#64) mErr)

/-- State at the loop exit `+0x460` (analog of `Wire.LoopExitState`). -/
def PreKeyLoopExitState (img : Obj.Image) (s0 : State) (sp' sret len ptr : BitVec 64) (vb : BitVec 8)
    (sf : State) : Prop :=
  PreKeyLoopRegs sp' sret len ptr vb sf ∧ sf.spAligned = true ∧ img.FrozenLoaded sf ∧
    sf.symtab = img.symtab ∧ sf.trace = s0.trace

/-- Full loop-exit postcondition (analog of `loopExitPostX`). -/
def preKeyLoopExitPost (img : Obj.Image) (A : RustAlloc) (s0 : State) (sp' sret len ptr0 : BitVec 64)
    (vb : BitVec 8) (ptr : BitVec 64) (bs : List (BitVec 8)) (res : Option ProtoPreKeySignalMessage)
    (sf : State) (P : SepProp) : Prop :=
  PreKeyLoopExitState img s0 sp' sret len ptr0 vb sf ∧
    (P ⊢ preKeyLoopExitMem A sp' ptr bs (sf.readReg64 .x24) res)

/-- Decode-loop invariant (`fuel` induction): from the loop head `+0x0e4` to `+0x460`.-/
def PreKeyDecodeLoopOk (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) :
    Prop :=
  ∀ (s0 : State) (sp' sret len ptr0 : BitVec 64) (vb : BitVec 8) (fuel : Nat) (s : State)
    (ptr : BitVec 64) (bs : List (BitVec 8)) (m : ProtoPreKeySignalMessage),
    s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0e4#64 →
    s.status = .Running →
    PreKeyLoopRegs sp' sret len ptr0 vb s →
    s.spAligned = true → img.FrozenLoaded s → s.symtab = img.symtab → s.trace = s0.trace →
    bs.length ≤ fuel → bs.length < 2 ^ 32 →
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs
        (Pksm.decodeProtoLoop fuel m bs))
      (tryFromQp s0)

/-- First-iteration decode-loop entry `+0x0f4` (jumped to from `+0x0d0` on a non-empty body,
with `x28 = sp' + 296`, `x26 = sp' + 304`, `x2 = len`).-/
def PreKeyDecodeLoopF4Ok (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) :
    Prop :=
  ∀ (s0 : State) (sp' sret len ptr0 : BitVec 64) (vb : BitVec 8) (fuel : Nat) (s : State)
    (ptr : BitVec 64) (b0 : BitVec 8) (bs1 : List (BitVec 8)) (m : ProtoPreKeySignalMessage),
    s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0f4#64 →
    s.status = .Running →
    PreKeyLoopRegs sp' sret len ptr0 vb s →
    s.readReg64 .x28 = sp' + 296#64 → s.readReg64 .x26 = sp' + 304#64 →
    s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length →
    s.spAligned = true → img.FrozenLoaded s → s.symtab = img.symtab → s.trace = s0.trace →
    (b0 :: bs1).length ≤ fuel + 1 → (b0 :: bs1).length < 2 ^ 32 →
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr (b0 :: bs1) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr (b0 :: bs1)
        (Pksm.decodeProtoLoop (fuel + 1) m (b0 :: bs1)))
      (tryFromQp s0)

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
