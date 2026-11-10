/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aBaseKey
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDeser
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ParseLemmas
import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32Merge

/-!
# Pure and Separation-Logic `Ok`-Path Bridge for `PreKeySignalMessage::try_from`

Connects the machine-level post-loop checks (version window `0x30 ≤ vb ≤ 0x4f`, 3-way Kyber
field check `kyberStageOut`, X25519 key deserializations, and inner `SignalMessage.tryFrom`)
to `Pksm.pksmParse (vb :: body) = some (pksmModelOf ...)` and `RunCompose.pksmResAt`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

theorem L1_PksmWire_OkBridge : True := trivial

/-! ## 0. Kyber Stage Output (`kyberStageOut`) and Frozen Ok State (`KyberOkState`) -/

/-- Separation-logic postcondition of the Kyber 3-way dispatch (`+0x684 → +0x86c`). -/
def kyberStageOut (A : RustAlloc) (kpkVal : BitVec 32) (vb : BitVec 8)
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8)))
    (kyberBoxPtr kyberBoxLen : BitVec 64) : SepProp :=
  match kpkOpt, kyberOpt with
  | some kpkId, some kyberCt =>
    ⌜kyberBoxPtr ≠ 0#64 ∧ kyberBoxLen = BitVec.ofNat 64 kyberCt.length ∧ kpkVal = kpkId⌝ ∗
      boxU8Buf A kyberBoxPtr kyberCt
  | none, none =>
    ⌜kyberBoxPtr = 0#64 ∧ vb.toNat < 0x40⌝
  | _, _ => ⌜False⌝

/-- Frozen Ok exit state at `+0x86c` (`2156`). -/
def KyberOkState (img : Obj.Image) (s0 : State)
    (sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap : BitVec 64) (vb : BitVec 8)
    (bk : List (BitVec 8)) (pk : PublicKey) (sf : State) : Prop :=
  PostEpilogueState img s0 sp' sf ∧
  ecKeyParses bk = true ∧ pkOf bk = pk ∧ (pkOf bk).bytes.toList = (bk.take 33).drop 1 ∧
  sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x28 = kyberBoxPtr ∧
  sf.readReg64 .x27 = 0x8000000000000002#64 ∧ sf.readReg64 .x26 = msgCap ∧
  sf.readReg64 .x25 = kyberBoxLen ∧ sf.readReg64 .x24 = sp' + 312#64 ∧
  sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = vb.zeroExtend 64 ∧
  sf.readReg64 .x21 = ptr0 ∧ sf.readReg64 .x20 = len ∧ sf.readReg64 .x19 = sret

/-! ## 1. Version-Window Lemmas (`0x30 ≤ vb.toNat ≤ 0x4f` ⇒ `3 ≤ (vb >>> 4).toNat ≤ 4`) -/

theorem vb_lsr4_toNat (vb : BitVec 8) : (vb >>> 4).toNat = vb.toNat / 16 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- Version-window bound: `0x30 ≤ vb.toNat` and `vb.toNat ≤ 0x4f` imply
`3 ≤ (vb >>> 4).toNat ∧ (vb >>> 4).toNat ≤ 4`. -/
theorem ver_bounds_of_vb_window {vb : BitVec 8}
    (hlo : 0x30 ≤ vb.toNat) (hhi : vb.toNat ≤ 0x4f) :
    3 ≤ (vb >>> 4).toNat ∧ (vb >>> 4).toNat ≤ 4 := by
  rw [vb_lsr4_toNat]
  omega

/-- Version-window bound in negated branch form:
`0x30 ≤ vb.toNat` and `vb.toNat ≤ 0x4f` imply `¬ ((vb >>> 4).toNat < 3 ∨ 4 < (vb >>> 4).toNat)`. -/
theorem not_ver_out_of_range_of_vb_window {vb : BitVec 8}
    (hlo : 0x30 ≤ vb.toNat) (hhi : vb.toNat ≤ 0x4f) :
    ¬ ((vb >>> 4).toNat < 3 ∨ 4 < (vb >>> 4).toNat) := by
  have ⟨h1, h2⟩ := ver_bounds_of_vb_window hlo hhi
  omega

/-- Converts `Nat` version-window bounds into `BitVec.ule` bounds `0x30#8 ≤ vb ∧ vb ≤ 0x4f#8`
for `ParseLemmas.pksmParse_eq_some`. -/
theorem vb_ule_window_of_toNat {vb : BitVec 8}
    (hlo : 0x30 ≤ vb.toNat) (hhi : vb.toNat ≤ 0x4f) :
    0x30#8 ≤ vb ∧ vb ≤ 0x4f#8 := by
  rw [BitVec.le_def, BitVec.le_def]
  exact ⟨hlo, hhi⟩

/-- Version-window bound from `BitVec.ule` (`0x30#8 ≤ vb` and `vb ≤ 0x4f#8`). -/
theorem ver_bounds_of_vb_ule {vb : BitVec 8}
    (hlo : 0x30#8 ≤ vb) (hhi : vb ≤ 0x4f#8) :
    3 ≤ (vb >>> 4).toNat ∧ (vb >>> 4).toNat ≤ 4 := by
  rw [BitVec.le_def] at hlo hhi
  exact ver_bounds_of_vb_window hlo hhi

/-- Version-window bound from the prologue's unsigned range check `(vb - 0x30#8).toNat ≤ 0x1f`. -/
theorem vb_window_of_sub_0x30_le {vb : BitVec 8}
    (h : (vb - 0x30#8).toNat ≤ 0x1f) :
    0x30 ≤ vb.toNat ∧ vb.toNat ≤ 0x4f := by
  have hlt : vb.toNat < 256 := vb.isLt
  rw [BitVec.toNat_sub] at h
  change (256 - 48 + vb.toNat) % 256 ≤ 31 at h
  omega

/-- In the `(none, none)` Kyber arm, `vb.toNat < 0x40` implies `(vb >>> 4).toNat ≤ 3`. -/
theorem ver_le_three_of_vb_lt_0x40 {vb : BitVec 8} (hlt : vb.toNat < 0x40) :
    (vb >>> 4).toNat ≤ 3 := by
  rw [vb_lsr4_toNat]
  omega

/-- In the `(none, none)` Kyber arm, `vb.toNat < 0x40` implies `(vb >>> 4) ≤ preKyberVersion`. -/
theorem ver_le_preKyberVersion_of_vb_lt_0x40 {vb : BitVec 8} (hlt : vb.toNat < 0x40) :
    (vb >>> 4) ≤ preKyberVersion := by
  rw [BitVec.le_def]
  exact ver_le_three_of_vb_lt_0x40 hlt

theorem decide_ver_le_three_of_vb_lt_0x40 {vb : BitVec 8} (hlt : vb.toNat < 0x40) :
    decide ((vb >>> 4).toNat ≤ 3) = true :=
  decide_eq_true (ver_le_three_of_vb_lt_0x40 hlt)

theorem ofNat8_ver_eq_lsr4 (vb : BitVec 8) :
    BitVec.ofNat 8 (vb >>> 4).toNat = vb >>> 4 := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem truncate8_lsr4_zeroExtend64 (vb : BitVec 8) :
    BitVec.truncate 8 ((vb.zeroExtend 64) >>> 4) = vb >>> 4 := by
  apply BitVec.eq_of_toNat_eq
  have := vb.isLt
  simp only [BitVec.truncate_eq_setWidth,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

/-! ## 2. Kyber 3-Way Check Bridge (`Pksm.kyberOk`, `kyberOkBool`, `kyberStageOut`, `optKyberAt`) -/

/-- Two-field boolean form of `Pksm.kyberOk`. -/
def kyberOkBool (ver : Nat) (kpkOpt : Option (BitVec 32))
    (kyberOpt : Option (List (BitVec 8))) : Bool :=
  (kpkOpt.isSome && kyberOpt.isSome) ||
    (kpkOpt.isNone && kyberOpt.isNone && decide (ver ≤ 3))

/-- Exact equivalence between `kyberOkBool (vb >>> 4).toNat m.kyberPreKeyId m.kyberCiphertext`
and `Pksm.kyberOk (vb >>> 4) m`. -/
theorem kyberOkBool_eq_kyberOk (vb : BitVec 8) (m : ProtoPreKeySignalMessage) :
    kyberOkBool (vb >>> 4).toNat m.kyberPreKeyId m.kyberCiphertext =
      Pksm.kyberOk (vb >>> 4) m := by
  have hdec : decide ((vb >>> 4).toNat ≤ 3) = decide ((vb >>> 4) ≤ preKyberVersion) := by
    apply Bool.decide_congr
    rw [BitVec.le_def]
    rfl
  simp only [kyberOkBool, Pksm.kyberOk, hdec]

theorem kyberOkBool_of_some {ver : Nat} {kpkOpt : Option (BitVec 32)}
    {kyberOpt : Option (List (BitVec 8))} {kpkId : BitVec 32} {kyberCt : List (BitVec 8)}
    (hkpk : kpkOpt = some kpkId) (hct : kyberOpt = some kyberCt) :
    kyberOkBool ver kpkOpt kyberOpt = true := by
  subst hkpk; subst hct; rfl

theorem kyberOkBool_of_none {ver : Nat} {kpkOpt : Option (BitVec 32)}
    {kyberOpt : Option (List (BitVec 8))}
    (hkpk : kpkOpt = none) (hct : kyberOpt = none) (hver : ver ≤ 3) :
    kyberOkBool ver kpkOpt kyberOpt = true := by
  subst hkpk; subst hct
  simp [kyberOkBool, hver]

theorem kyberOkBool_of_none_lt_0x40 {vb : BitVec 8} {kpkOpt : Option (BitVec 32)}
    {kyberOpt : Option (List (BitVec 8))}
    (hkpk : kpkOpt = none) (hct : kyberOpt = none) (hlt : vb.toNat < 0x40) :
    kyberOkBool (vb >>> 4).toNat kpkOpt kyberOpt = true :=
  kyberOkBool_of_none hkpk hct (ver_le_three_of_vb_lt_0x40 hlt)

theorem kyberOkBool_of_disj {vb : BitVec 8} {kpkOpt : Option (BitVec 32)}
    {kyberOpt : Option (List (BitVec 8))}
    (h : (∃ kpkId kyberCt, kpkOpt = some kpkId ∧ kyberOpt = some kyberCt) ∨
         (kpkOpt = none ∧ kyberOpt = none ∧ vb.toNat < 0x40)) :
    kyberOkBool (vb >>> 4).toNat kpkOpt kyberOpt = true := by
  rcases h with ⟨kpkId, kyberCt, hkpk, hct⟩ | ⟨hkpk, hct, hlt⟩
  · exact kyberOkBool_of_some hkpk hct
  · exact kyberOkBool_of_none_lt_0x40 hkpk hct hlt

/-- `Pksm.kyberOk` holds when both `kyberPreKeyId` and `kyberCiphertext` are `some`. -/
theorem kyberOk_of_some {ver : BitVec 8} {m : ProtoPreKeySignalMessage}
    {kpkId : BitVec 32} {kyberCt : List (BitVec 8)}
    (hkpk : m.kyberPreKeyId = some kpkId) (hct : m.kyberCiphertext = some kyberCt) :
    Pksm.kyberOk ver m = true := by
  simp [Pksm.kyberOk, hkpk, hct]

/-- `Pksm.kyberOk (vb >>> 4) m = true` when both Kyber fields are `none` and `vb.toNat < 0x40`. -/
theorem kyberOk_of_none_lt_0x40 {vb : BitVec 8} {m : ProtoPreKeySignalMessage}
    (hkpk : m.kyberPreKeyId = none) (hct : m.kyberCiphertext = none) (hlt : vb.toNat < 0x40) :
    Pksm.kyberOk (vb >>> 4) m = true := by
  rw [← kyberOkBool_eq_kyberOk]
  exact kyberOkBool_of_none_lt_0x40 hkpk hct hlt

/-- Either valid arm of the Kyber 3-way check implies `Pksm.kyberOk (vb >>> 4) m = true`. -/
theorem kyberOk_of_disj {vb : BitVec 8} {m : ProtoPreKeySignalMessage}
    (h : (∃ kpkId kyberCt, m.kyberPreKeyId = some kpkId ∧ m.kyberCiphertext = some kyberCt) ∨
         (m.kyberPreKeyId = none ∧ m.kyberCiphertext = none ∧ vb.toNat < 0x40)) :
    Pksm.kyberOk (vb >>> 4) m = true := by
  rw [← kyberOkBool_eq_kyberOk]
  exact kyberOkBool_of_disj h

/-- `kyberStageOut` entails `kyberOkBool (vb >>> 4).toNat kpkOpt kyberOpt = true` while preserving
`kyberStageOut`. -/
theorem kyberStageOut_entails_kyberOkBool (A : RustAlloc) (kpkVal : BitVec 32) (vb : BitVec 8)
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8)))
    (kyberBoxPtr kyberBoxLen : BitVec 64) :
    kyberStageOut A kpkVal vb kpkOpt kyberOpt kyberBoxPtr kyberBoxLen ⊢
      ⌜kyberOkBool (vb >>> 4).toNat kpkOpt kyberOpt = true⌝ ∗
        kyberStageOut A kpkVal vb kpkOpt kyberOpt kyberBoxPtr kyberBoxLen := by
  cases kpkOpt with
  | some kpkId =>
    cases kyberOpt with
    | some kyberCt =>
      have hok : kyberOkBool (vb >>> 4).toNat (some kpkId) (some kyberCt) = true := rfl
      rw [pure_true_emp hok, emp_sepConj]
      exact Entails.refl _
    | none =>
      dsimp only [kyberStageOut]
      exact Entails.pure_left_only fun h => False.elim h
  | none =>
    cases kyberOpt with
    | some kyberCt =>
      dsimp only [kyberStageOut]
      exact Entails.pure_left_only fun h => False.elim h
    | none =>
      dsimp only [kyberStageOut]
      refine Entails.pure_left_only fun ⟨hptr, hlt⟩ => ?_
      have hok := kyberOkBool_of_none_lt_0x40 (vb := vb) rfl rfl hlt
      rw [pure_true_emp hok, emp_sepConj, pure_true_emp ⟨hptr, hlt⟩]
      exact Entails.refl _

/-- `kyberStageOut` for `m.kyberPreKeyId` / `m.kyberCiphertext` entails
`Pksm.kyberOk (vb >>> 4) m = true` while preserving `kyberStageOut`. -/
theorem kyberStageOut_entails_kyberOk (A : RustAlloc) (kpkVal : BitVec 32) (vb : BitVec 8)
    (m : ProtoPreKeySignalMessage) (kyberBoxPtr kyberBoxLen : BitVec 64) :
    kyberStageOut A kpkVal vb m.kyberPreKeyId m.kyberCiphertext kyberBoxPtr kyberBoxLen ⊢
      ⌜Pksm.kyberOk (vb >>> 4) m = true⌝ ∗
        kyberStageOut A kpkVal vb m.kyberPreKeyId m.kyberCiphertext kyberBoxPtr kyberBoxLen := by
  rw [← kyberOkBool_eq_kyberOk]
  exact kyberStageOut_entails_kyberOkBool A kpkVal vb
    m.kyberPreKeyId m.kyberCiphertext kyberBoxPtr kyberBoxLen

/-- Uniform packing of the 24-byte `Option<KyberPayload>` field at `a = sret + 0x90`:
when `a ↦₆₄ kyberBoxPtr`, `(a + 8) ↦₆₄ kyberBoxLen`, and `(a + 16) ↦₃₂ kpkVal` are written,
combining with `kyberStageOut` yields `optKyberAt A a kyberBoxPtr (Pksm.kyberPayloadOf kpkOpt kyberOpt)`
in both the `(some, some)` and `(none, none)` cases. -/
theorem kyberCells_entails_optKyberAt (A : RustAlloc) (a : BitVec 64)
    (kpkVal : BitVec 32) (vb : BitVec 8)
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8)))
    (kyberBoxPtr kyberBoxLen : BitVec 64) :
    ((a ↦₆₄ kyberBoxPtr) ∗ ((a + 8#64) ↦₆₄ kyberBoxLen) ∗
      ((a + 0x10#64) ↦₃₂ kpkVal) ∗ memRegion (a + 0x14#64) 4) ∗
      kyberStageOut A kpkVal vb kpkOpt kyberOpt kyberBoxPtr kyberBoxLen ⊢
      optKyberAt A a kyberBoxPtr (Pksm.kyberPayloadOf kpkOpt kyberOpt) := by
  cases kpkOpt with
  | some kpkId =>
    cases kyberOpt with
    | some kyberCt =>
      dsimp only [kyberStageOut, Pksm.kyberPayloadOf, optKyberAt]
      simp only [sepConj_pure_left_comm, sepConj_assoc]
      refine Entails.pure_left fun ⟨_, hlen, hkpk⟩ => ?_
      subst hlen; subst hkpk
      rw [boxU8At_eq_boxU8Buf A a kyberBoxPtr kyberCt]
      simp only [sepConj_assoc]
      apply entails_of_eq; ac_rfl
    | none =>
      dsimp only [kyberStageOut]
      rw [sepConj_comm]
      exact Entails.pure_left fun h => False.elim h
  | none =>
    cases kyberOpt with
    | some kyberCt =>
      dsimp only [kyberStageOut]
      rw [sepConj_comm]
      exact Entails.pure_left fun h => False.elim h
    | none =>
      dsimp only [kyberStageOut, Pksm.kyberPayloadOf, optKyberAt]
      rw [sepConj_comm]
      refine Entails.pure_left fun ⟨hptr, _⟩ => ?_
      subst hptr
      have hm16 :
          ((a + 8#64) ↦₆₄ kyberBoxLen) ∗ ((a + 0x10#64) ↦₃₂ kpkVal) ∗
            memRegion (a + 0x14#64) 4 ⊢ memRegion (a + 8#64) 16 := by
        rw [show (16 : Nat) = 8 + (4 + 4) by decide,
            Prost.memRegion_split (a + 8#64) 8 8 (by decide),
            Prost.memRegion_split (a + 8#64 + 8#64) 4 4 (by decide)]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        exact sepConj_mono (pointsTo64_entails_memRegion8 (a + 8#64) kyberBoxLen)
          (sepConj_mono_left (pointsTo32_entails_memRegion4 (a + 16#64) kpkVal))
      exact sepConj_mono_right hm16

/-- Packing `optKyberAt` in the `(none, none)` case when `a ↦₆₄ 0#64` and `memRegion (a + 8#64) 16`
are present directly (when `cbz x28` skips storing `kyberBoxLen` and `kpkVal`). -/
theorem kyberNoneCells_entails_optKyberAt (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ memRegion (a + 8#64) 16 ⊢
      optKyberAt A a 0#64 (Pksm.kyberPayloadOf none none) :=
  Entails.refl _

/-! ## 3. Key Deserialization & State Projections (`BaseKeyOkState`, `KyberOkState`) -/

/-- Projection bundle from `PublicKey.deserialize bs = .ok pk`:
`ecKeyParses bs = true`, `pkOf bs = pk`, and `(pkOf bs).bytes.toList = (bs.take 33).drop 1`. -/
theorem ecKeyParses_and_pkOf_of_deserialize_ok {bs : List (BitVec 8)} {pk : PublicKey}
    (h : PublicKey.deserialize bs = .ok pk) :
    ecKeyParses bs = true ∧ pkOf bs = pk ∧ (pkOf bs).bytes.toList = (bs.take 33).drop 1 ∧
      pk.bytes.toList = (bs.take 33).drop 1 := by
  have hec := ecKeyParses_of_deserialize_ok h
  have hpk := pkOf_of_deserialize_ok h
  have hbytes := pkOf_bytes_of_ecKeyParses hec
  exact ⟨hec, hpk, hbytes, hpk ▸ hbytes⟩

/-- `ecKeyParses bs = true` implies `PublicKey.deserialize bs = .ok (pkOf bs)`. -/
theorem deserialize_ok_pkOf_of_ecKeyParses {bs : List (BitVec 8)}
    (h : ecKeyParses bs = true) :
    PublicKey.deserialize bs = .ok (pkOf bs) := by
  rcases (ecKeyParses_iff_deserialize_ok bs).mp h with ⟨k, hk⟩
  rwa [pkOf_of_deserialize_ok hk]

theorem BaseKeyOkState.ecKeyParses {img : Obj.Image} {s0 : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {pk : PublicKey} {sf : State}
    (h : BaseKeyOkState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb bk pk sf) :
    ecKeyParses bk = true :=
  h.2.1

theorem BaseKeyOkState.pkOf_eq {img : Obj.Image} {s0 : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {pk : PublicKey} {sf : State}
    (h : BaseKeyOkState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb bk pk sf) :
    pkOf bk = pk :=
  h.2.2.1

theorem BaseKeyOkState.pkOf_bytes {img : Obj.Image} {s0 : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {pk : PublicKey} {sf : State}
    (h : BaseKeyOkState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb bk pk sf) :
    (pkOf bk).bytes.toList = (bk.take 33).drop 1 :=
  h.2.2.2.1

theorem KyberOkState.ecKeyParses {img : Obj.Image} {s0 : State}
    {sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {pk : PublicKey} {sf : State}
    (h : KyberOkState img s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb bk pk sf) :
    ecKeyParses bk = true :=
  h.2.1

theorem KyberOkState.pkOf_eq {img : Obj.Image} {s0 : State}
    {sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {pk : PublicKey} {sf : State}
    (h : KyberOkState img s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb bk pk sf) :
    pkOf bk = pk :=
  h.2.2.1

theorem KyberOkState.pkOf_bytes {img : Obj.Image} {s0 : State}
    {sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {pk : PublicKey} {sf : State}
    (h : KyberOkState img s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb bk pk sf) :
    (pkOf bk).bytes.toList = (bk.take 33).drop 1 :=
  h.2.2.2.1

/-! ## 4. Main `Pksm.pksmParse` and `pksmModelOf` Ok-Path Bridge Theorems -/

/-- Concrete `PreKeySignalMessage` model constructed on the Ok path of
`PreKeySignalMessage::try_from` from decoded protobuf `m`, raw key byte slices `bk` / `ik`,
`signedPreKeyId = sid`, and inner `SignalMessage` `inner`. -/
def pksmModelOf (b : List (BitVec 8)) (vb : BitVec 8) (m : ProtoPreKeySignalMessage)
    (bk ik : List (BitVec 8)) (sid : BitVec 32) (inner : SignalMessage) :
    PreKeySignalMessage :=
  { messageVersion := vb >>> 4
    registrationId := m.registrationId.getD 0#32
    preKeyId := m.preKeyId
    signedPreKeyId := sid
    kyberPayload := Pksm.kyberPayloadOf m.kyberPreKeyId m.kyberCiphertext
    baseKey := pkOf bk
    identityKey := ⟨pkOf ik⟩
    message := inner
    serialized := b }

/-- Pure `Pksm.pksmParse` `Ok`-path characterization:
when the binary's version-window check (`0x30 ≤ vb.toNat ≤ 0x4f`), protobuf decode
(`Pksm.decodeProto body = some m`), required-field presence (`baseKey`, `identityKey`, `message`,
`signedPreKeyId`), Kyber check (`Pksm.kyberOk (vb >>> 4) m = true`), key deserializations
(`ecKeyParses bk`, `ecKeyParses ik`), and inner `SignalMessage.tryFrom` check all succeed,
`Pksm.pksmParse (vb :: body) = some (pksmModelOf (vb :: body) vb m bk ik sid inner)`. -/
theorem pksmParse_eq_some_of_ok {vb : BitVec 8} {body : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage}
    {bk ik msg : List (BitVec 8)} {sid : BitVec 32} {inner : SignalMessage}
    (hlo : 0x30 ≤ vb.toNat) (hhi : vb.toNat ≤ 0x4f)
    (hdec : Pksm.decodeProto body = some m)
    (hbk : m.baseKey = some bk)
    (hik : m.identityKey = some ik)
    (hmsg : m.message = some msg)
    (hsid : m.signedPreKeyId = some sid)
    (hkyber : Pksm.kyberOk (vb >>> 4) m = true)
    (hbk_ok : ecKeyParses bk = true)
    (hik_ok : ecKeyParses ik = true)
    (hinner : SignalMessage.tryFrom protoSignalCodec msg = .ok inner) :
    Pksm.pksmParse (vb :: body) = some (pksmModelOf (vb :: body) vb m bk ik sid inner) :=
  pksmParse_eq_some (vb_ule_window_of_toNat hlo hhi) hdec hbk hik hmsg hsid hkyber
    (deserialize_ok_pkOf_of_ecKeyParses hbk_ok)
    (deserialize_ok_pkOf_of_ecKeyParses hik_ok)
    hinner

/-- Variant of `pksmParse_eq_some_of_ok` taking `PublicKey.deserialize` for both keys and the
2-way Kyber disjunction directly. -/
theorem pksmParse_eq_some_of_deser_and_kyber {vb : BitVec 8} {body : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {bk ik msg : List (BitVec 8)} {sid : BitVec 32}
    {bkPk ikPk : PublicKey} {inner : SignalMessage}
    (hlo : 0x30 ≤ vb.toNat) (hhi : vb.toNat ≤ 0x4f)
    (hdec : Pksm.decodeProto body = some m)
    (hbk : m.baseKey = some bk)
    (hik : m.identityKey = some ik)
    (hmsg : m.message = some msg)
    (hsid : m.signedPreKeyId = some sid)
    (hkyber : (∃ kpkId kyberCt, m.kyberPreKeyId = some kpkId ∧ m.kyberCiphertext = some kyberCt) ∨
              (m.kyberPreKeyId = none ∧ m.kyberCiphertext = none ∧ vb.toNat < 0x40))
    (hbk_deser : PublicKey.deserialize bk = .ok bkPk)
    (hik_deser : PublicKey.deserialize ik = .ok ikPk)
    (hinner : SignalMessage.tryFrom protoSignalCodec msg = .ok inner) :
    Pksm.pksmParse (vb :: body) = some
      { messageVersion := vb >>> 4
        registrationId := m.registrationId.getD 0#32
        preKeyId := m.preKeyId
        signedPreKeyId := sid
        kyberPayload := Pksm.kyberPayloadOf m.kyberPreKeyId m.kyberCiphertext
        baseKey := bkPk
        identityKey := ⟨ikPk⟩
        message := inner
        serialized := vb :: body } :=
  pksmParse_eq_some (vb_ule_window_of_toNat hlo hhi) hdec hbk hik hmsg hsid
    (kyberOk_of_disj hkyber) hbk_deser hik_deser hinner

/-! ## 5. `RunCompose.pksmResAt` Separation-Logic Bridge Lemmas -/

/-- Introduces `RunCompose.pksmResAt A sret (some msg)` from `preKeyMsgAt A g sret msg ∗ R`. -/
theorem pksmResAt_some_intro (A : RustAlloc) (sret : BitVec 64) (g : PreKeyMsgGhost)
    (msg : PreKeySignalMessage) (R : SepProp) :
    preKeyMsgAt A g sret msg ∗ R ⊢ RunCompose.pksmResAt A sret (some msg) := by
  unfold RunCompose.pksmResAt
  exact sepConj_mono (Entails.sepExists_right g (Entails.refl _)) (entails_anyHeap R)

/-- Introduces `RunCompose.pksmResAt A sret (Pksm.pksmParse b)` on the Ok path (`Pksm.pksmParse b = some msg`). -/
theorem pksmResAt_ok_of_parse (A : RustAlloc) (sret : BitVec 64) (b : List (BitVec 8))
    (g : PreKeyMsgGhost) (msg : PreKeySignalMessage) (R : SepProp)
    (hparse : Pksm.pksmParse b = some msg) :
    preKeyMsgAt A g sret msg ∗ R ⊢ RunCompose.pksmResAt A sret (Pksm.pksmParse b) := by
  rw [hparse]
  exact pksmResAt_some_intro A sret g msg R

/-- Introduces `RunCompose.pksmResAt A sret (Pksm.pksmParse b)` on the Err path (`Pksm.pksmParse b = none` and exact `pksmErrE A fn sret e ∗ R`). -/
theorem pksmResAt_err_of_parse (A : RustAlloc) (fn : List (BitVec 8)) (sret : BitVec 64)
    (b : List (BitVec 8)) (e : SignalProtocolError) (R : SepProp)
    (hparse : Pksm.pksmParse b = none) :
    pksmErrE A fn sret e ∗ R ⊢ RunCompose.pksmResAt A sret (Pksm.pksmParse b) := by
  rw [hparse]
  exact pksm0c_pksmErrE_frame_entails_resAt_none A fn sret e R

/-- Absorbs trailing heap/rodata residue `R` into `RunCompose.pksmResAt A sret res`. -/
theorem pksmResAt_absorb_right (A : RustAlloc) (sret : BitVec 64)
    (res : Option PreKeySignalMessage) (R : SepProp) :
    RunCompose.pksmResAt A sret res ∗ R ⊢ RunCompose.pksmResAt A sret res := by
  cases res with
  | none =>
    unfold RunCompose.pksmResAt
    simp only [sepConj_assoc]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (entails_anyHeap _)))
  | some msg =>
    unfold RunCompose.pksmResAt
    rw [sepConj_assoc]
    exact sepConj_mono_right (entails_anyHeap _)

/-- `Prost.optU32At` unpacked into `(opkTag, opkVal)` packs into
`LibsignalPublicApiRepr.optU32At a opt`. -/
theorem pointsTo32_pair_entails_publicOptU32At (a : BitVec 64) (opt : Option (BitVec 32))
    (opkTag opkVal : BitVec 32)
    (htag : opkTag = if opt.isSome then 1#32 else 0#32)
    (hval : ∀ v, opt = some v → opkVal = v) :
    (a ↦₃₂ opkTag) ∗ ((a + 4#64) ↦₃₂ opkVal) ⊢
      LibsignalPublicApiRepr.optU32At a opt := by
  subst htag
  cases opt with
  | none =>
    dsimp only [Option.isSome, Bool.false_eq_true, ↓reduceIte, LibsignalPublicApiRepr.optU32At]
    exact sepConj_mono_right (pointsTo32_entails_memRegion4 (a + 4#64) opkVal)
  | some v =>
    have hv := hval v rfl
    subst hv
    exact Entails.refl _

/-- Unpacks `Prost.optU32At a opt` into `∃ opkTag opkVal` with
`opkTag = if opt.isSome then 1#32 else 0#32` and `∀ v, opt = some v → opkVal = v`. -/
theorem prostOptU32At_entails_pair (a : BitVec 64) (opt : Option (BitVec 32)) :
    Prost.optU32At a opt ⊢
      ∃∗ opkTag : BitVec 32, ∃∗ opkVal : BitVec 32,
        ⌜opkTag = (if opt.isSome then 1#32 else 0#32) ∧ (∀ v, opt = some v → opkVal = v)⌝ ∗
        (a ↦₃₂ opkTag) ∗ ((a + 4#64) ↦₃₂ opkVal) := by
  cases opt with
  | none =>
    unfold Prost.optU32At
    rw [ProofLib.memRegion_four (a + 4#64), sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro 0#32)
    refine Entails.trans ?_ (Entails.sepExists_intro w)
    have hp : (0#32 = (if (none : Option (BitVec 32)).isSome then 1#32 else 0#32) ∧
        ∀ v, (none : Option (BitVec 32)) = some v → w = v) :=
      ⟨rfl, by intro _ h; cases h⟩
    rw [pure_true_emp hp, emp_sepConj]
    exact Entails.refl _
  | some v =>
    unfold Prost.optU32At
    refine Entails.trans ?_ (Entails.sepExists_intro 1#32)
    refine Entails.trans ?_ (Entails.sepExists_intro v)
    have hp : (1#32 = (if (some v).isSome then 1#32 else 0#32) ∧
        ∀ v', some v = some v' → v = v') :=
      ⟨rfl, fun _ h => Option.some.inj h⟩
    rw [pure_true_emp hp, emp_sepConj]
    exact Entails.refl _

/-- Packs the 248 bytes of `sret` + `msgHeapAt` + `boxU8Buf A serBoxPtr b` + `kyberStageOut` into
`preKeyMsgAt A ⟨msgG, serBoxPtr, kyberBoxPtr⟩ sret (pksmModelOf b vb m bk ik sid innerMsg)`. -/
theorem sret_cells_entails_preKeyMsgAt_model (A : RustAlloc) (sret : BitVec 64)
    (b : List (BitVec 8)) (vb : BitVec 8) (m : ProtoPreKeySignalMessage)
    (bk ik : List (BitVec 8)) (sid : BitVec 32) (innerMsg : SignalMessage)
    (msgG : SignalMessageGhost) (serBoxPtr kyberBoxPtr kyberBoxLen : BitVec 64)
    (rk0 rk1 rk2 rk3 addrW0 addrW1 : BitVec 64) (verHi56 : BitVec 56)
    (ik0 ik1 ik2 ik3 : BitVec 64)
    (opkTag opkVal kpkVal : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8)
    (w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64)
    (hopkTag : opkTag = if m.preKeyId.isSome then 1#32 else 0#32)
    (hopkVal : ∀ v, m.preKeyId = some v → opkVal = v)
    (hpk : (pkOf bk).bytes.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hrk : ∀ a : BitVec 64, (a ↦ₛ innerMsg.senderRatchetKey.bytes.toList) =
      (a ↦₆₄ rk0) ∗ ((a + 8#64) ↦₆₄ rk1) ∗ ((a + 16#64) ↦₆₄ rk2) ∗ ((a + 24#64) ↦₆₄ rk3))
    (hik : ∀ a : BitVec 64, (a ↦ₛ (pkOf ik).bytes.toList) =
      (a ↦₆₄ ik0) ∗ ((a + 8#64) ↦₆₄ ik1) ∗ ((a + 16#64) ↦₆₄ ik2) ∗ ((a + 24#64) ↦₆₄ ik3)) :
    (msgWords15At sret
      msgG.pqCap msgG.pqPtr (BitVec.ofNat 64 innerMsg.pqRatchet.length)
      msgG.ctPtr (BitVec.ofNat 64 innerMsg.ciphertext.length)
      msgG.serPtr (BitVec.ofNat 64 innerMsg.serialized.length)
      rk0 rk1 rk2 rk3 addrW0 addrW1
      (innerMsg.previousCounter ++ innerMsg.counter) (verHi56 ++ innerMsg.messageVersion) ∗
      msgHeapAt A msgG innerMsg addrW0 addrW1) ∗
    (((sret + 120#64) ↦₃₂ opkTag) ∗ ((sret + 124#64) ↦₃₂ opkVal)) ∗
    (((sret + 128#64) ↦₆₄ serBoxPtr) ∗
      ((sret + 136#64) ↦₆₄ BitVec.ofNat 64 b.length) ∗
      boxU8Buf A serBoxPtr b) ∗
    ((((sret + 144#64) ↦₆₄ kyberBoxPtr) ∗
        ((sret + 152#64) ↦₆₄ kyberBoxLen) ∗
        ((sret + 160#64) ↦₃₂ kpkVal) ∗
        memRegion (sret + 164#64) 4) ∗
      kyberStageOut A kpkVal vb m.kyberPreKeyId m.kyberCiphertext kyberBoxPtr kyberBoxLen) ∗
    pkLayoutAt (sret + 168#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 ∗
    (((sret + 200#64) ↦₆₄ ik0) ∗ ((sret + 208#64) ↦₆₄ ik1) ∗
      ((sret + 216#64) ↦₆₄ ik2) ∗ ((sret + 224#64) ↦₆₄ ik3)) ∗
    ((sret + 232#64) ↦₃₂ m.registrationId.getD 0#32) ∗
    ((sret + 236#64) ↦₃₂ sid) ∗
    ((sret + 240#64) ↦₈ (vb >>> 4)) ∗
    memRegion (sret + 241#64) 7 ⊢
      preKeyMsgAt A ⟨msgG, serBoxPtr, kyberBoxPtr⟩ sret
        (pksmModelOf b vb m bk ik sid innerMsg) := by
  unfold preKeyMsgAt pksmModelOf
  dsimp only
  have hmsg := signalMessageAt_pack A msgG sret innerMsg rk0 rk1 rk2 rk3 addrW0 addrW1 verHi56 hrk
  have hopk := pointsTo32_pair_entails_publicOptU32At (sret + 120#64) m.preKeyId opkTag opkVal
    hopkTag hopkVal
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hopk
  have hkyb := kyberCells_entails_optKyberAt A (sret + 0x90#64) kpkVal vb
    m.kyberPreKeyId m.kyberCiphertext kyberBoxPtr kyberBoxLen
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hkyb
  refine Entails.trans
    (sepConj_mono hmsg
      (sepConj_mono hopk
        (sepConj_mono_right (sepConj_mono_left hkyb)))) ?_
  rw [boxU8At_eq_boxU8Buf A (sret + 0x80#64) serBoxPtr b,
      hpk, ← pkLayoutAt_eq_pointsToBytes (sret + 0xa8#64),
      hik (sret + 0xc8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply entails_of_eq; ac_rfl

/-- One-shot bridge from the packed 248-byte `sret` layout + `kyberStageOut` + trailing heap `R`
directly to `RunCompose.pksmResAt A sret (Pksm.pksmParse (vb :: body))`:
extracts `Pksm.kyberOk (vb >>> 4) m = true` from `kyberStageOut`, proves
`Pksm.pksmParse (vb :: body) = some (pksmModelOf (vb :: body) vb m bk ik sid innerMsg)`,
packs `preKeyMsgAt`, and absorbs `R` into `anyHeap`. -/
theorem sret_cells_entails_pksmResAt (A : RustAlloc) (sret : BitVec 64)
    (vb : BitVec 8) (body : List (BitVec 8)) (m : ProtoPreKeySignalMessage)
    (bk ik msg : List (BitVec 8)) (sid : BitVec 32) (innerMsg : SignalMessage)
    (msgG : SignalMessageGhost) (serBoxPtr kyberBoxPtr kyberBoxLen : BitVec 64)
    (rk0 rk1 rk2 rk3 addrW0 addrW1 : BitVec 64) (verHi56 : BitVec 56)
    (ik0 ik1 ik2 ik3 : BitVec 64)
    (opkTag opkVal kpkVal : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8)
    (w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64)
    (R : SepProp)
    (hlo : 0x30 ≤ vb.toNat) (hhi : vb.toNat ≤ 0x4f)
    (hdec : Pksm.decodeProto body = some m)
    (hbk : m.baseKey = some bk)
    (hik_some : m.identityKey = some ik)
    (hmsg : m.message = some msg)
    (hsid : m.signedPreKeyId = some sid)
    (hbk_ok : ecKeyParses bk = true)
    (hik_ok : ecKeyParses ik = true)
    (hinner : SignalMessage.tryFrom protoSignalCodec msg = .ok innerMsg)
    (hopkTag : opkTag = if m.preKeyId.isSome then 1#32 else 0#32)
    (hopkVal : ∀ v, m.preKeyId = some v → opkVal = v)
    (hpk : (pkOf bk).bytes.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hrk : ∀ a : BitVec 64, (a ↦ₛ innerMsg.senderRatchetKey.bytes.toList) =
      (a ↦₆₄ rk0) ∗ ((a + 8#64) ↦₆₄ rk1) ∗ ((a + 16#64) ↦₆₄ rk2) ∗ ((a + 24#64) ↦₆₄ rk3))
    (hik : ∀ a : BitVec 64, (a ↦ₛ (pkOf ik).bytes.toList) =
      (a ↦₆₄ ik0) ∗ ((a + 8#64) ↦₆₄ ik1) ∗ ((a + 16#64) ↦₆₄ ik2) ∗ ((a + 24#64) ↦₆₄ ik3)) :
    ((msgWords15At sret
        msgG.pqCap msgG.pqPtr (BitVec.ofNat 64 innerMsg.pqRatchet.length)
        msgG.ctPtr (BitVec.ofNat 64 innerMsg.ciphertext.length)
        msgG.serPtr (BitVec.ofNat 64 innerMsg.serialized.length)
        rk0 rk1 rk2 rk3 addrW0 addrW1
        (innerMsg.previousCounter ++ innerMsg.counter) (verHi56 ++ innerMsg.messageVersion) ∗
        msgHeapAt A msgG innerMsg addrW0 addrW1) ∗
      (((sret + 120#64) ↦₃₂ opkTag) ∗ ((sret + 124#64) ↦₃₂ opkVal)) ∗
      (((sret + 128#64) ↦₆₄ serBoxPtr) ∗
        ((sret + 136#64) ↦₆₄ BitVec.ofNat 64 (vb :: body).length) ∗
        boxU8Buf A serBoxPtr (vb :: body)) ∗
      ((((sret + 144#64) ↦₆₄ kyberBoxPtr) ∗
          ((sret + 152#64) ↦₆₄ kyberBoxLen) ∗
          ((sret + 160#64) ↦₃₂ kpkVal) ∗
          memRegion (sret + 164#64) 4) ∗
        kyberStageOut A kpkVal vb m.kyberPreKeyId m.kyberCiphertext kyberBoxPtr kyberBoxLen) ∗
      pkLayoutAt (sret + 168#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 ∗
      (((sret + 200#64) ↦₆₄ ik0) ∗ ((sret + 208#64) ↦₆₄ ik1) ∗
        ((sret + 216#64) ↦₆₄ ik2) ∗ ((sret + 224#64) ↦₆₄ ik3)) ∗
      ((sret + 232#64) ↦₃₂ m.registrationId.getD 0#32) ∗
      ((sret + 236#64) ↦₃₂ sid) ∗
      ((sret + 240#64) ↦₈ (vb >>> 4)) ∗
      memRegion (sret + 241#64) 7) ∗ R ⊢
      RunCompose.pksmResAt A sret (Pksm.pksmParse (vb :: body)) := by
  have hkybOk := kyberStageOut_entails_kyberOk A kpkVal vb m kyberBoxPtr kyberBoxLen
  refine Entails.trans
    (sepConj_mono_left
      (sepConj_mono_right
        (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono_left
              (sepConj_mono_right hkybOk)))))) ?_
  simp only [sepConj_pure_left_comm, sepConj_assoc]
  refine Entails.pure_left fun hkyber => ?_
  have hparse := pksmParse_eq_some_of_ok hlo hhi hdec hbk hik_some hmsg hsid
    hkyber hbk_ok hik_ok hinner
  have hpack := sret_cells_entails_preKeyMsgAt_model A sret (vb :: body) vb m bk ik sid innerMsg
    msgG serBoxPtr kyberBoxPtr kyberBoxLen rk0 rk1 rk2 rk3 addrW0 addrW1 verHi56
    ik0 ik1 ik2 ik3 opkTag opkVal kpkVal b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 w9 w13 w15 w23
    hopkTag hopkVal hpk hrk hik
  simp only [sepConj_assoc] at hpack
  refine Entails.trans ?_
    (pksmResAt_ok_of_parse A sret (vb :: body) ⟨msgG, serBoxPtr, kyberBoxPtr⟩
      (pksmModelOf (vb :: body) vb m bk ik sid innerMsg) R hparse)
  refine Entails.trans ?_ (sepConj_mono_left hpack)
  apply entails_of_eq; ac_rfl

/-- Direct `some (pksmModelOf ...)` corollary of `sret_cells_entails_preKeyMsgAt_model` + `R`
into `RunCompose.pksmResAt A sret (some ...)`. -/
theorem sret_cells_entails_pksmResAt_some (A : RustAlloc) (sret : BitVec 64)
    (b : List (BitVec 8)) (vb : BitVec 8) (m : ProtoPreKeySignalMessage)
    (bk ik : List (BitVec 8)) (sid : BitVec 32) (innerMsg : SignalMessage)
    (msgG : SignalMessageGhost) (serBoxPtr kyberBoxPtr kyberBoxLen : BitVec 64)
    (rk0 rk1 rk2 rk3 addrW0 addrW1 : BitVec 64) (verHi56 : BitVec 56)
    (ik0 ik1 ik2 ik3 : BitVec 64)
    (opkTag opkVal kpkVal : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8)
    (w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64)
    (R : SepProp)
    (hopkTag : opkTag = if m.preKeyId.isSome then 1#32 else 0#32)
    (hopkVal : ∀ v, m.preKeyId = some v → opkVal = v)
    (hpk : (pkOf bk).bytes.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hrk : ∀ a : BitVec 64, (a ↦ₛ innerMsg.senderRatchetKey.bytes.toList) =
      (a ↦₆₄ rk0) ∗ ((a + 8#64) ↦₆₄ rk1) ∗ ((a + 16#64) ↦₆₄ rk2) ∗ ((a + 24#64) ↦₆₄ rk3))
    (hik : ∀ a : BitVec 64, (a ↦ₛ (pkOf ik).bytes.toList) =
      (a ↦₆₄ ik0) ∗ ((a + 8#64) ↦₆₄ ik1) ∗ ((a + 16#64) ↦₆₄ ik2) ∗ ((a + 24#64) ↦₆₄ ik3)) :
    ((msgWords15At sret
        msgG.pqCap msgG.pqPtr (BitVec.ofNat 64 innerMsg.pqRatchet.length)
        msgG.ctPtr (BitVec.ofNat 64 innerMsg.ciphertext.length)
        msgG.serPtr (BitVec.ofNat 64 innerMsg.serialized.length)
        rk0 rk1 rk2 rk3 addrW0 addrW1
        (innerMsg.previousCounter ++ innerMsg.counter) (verHi56 ++ innerMsg.messageVersion) ∗
        msgHeapAt A msgG innerMsg addrW0 addrW1) ∗
      (((sret + 120#64) ↦₃₂ opkTag) ∗ ((sret + 124#64) ↦₃₂ opkVal)) ∗
      (((sret + 128#64) ↦₆₄ serBoxPtr) ∗
        ((sret + 136#64) ↦₆₄ BitVec.ofNat 64 b.length) ∗
        boxU8Buf A serBoxPtr b) ∗
      ((((sret + 144#64) ↦₆₄ kyberBoxPtr) ∗
          ((sret + 152#64) ↦₆₄ kyberBoxLen) ∗
          ((sret + 160#64) ↦₃₂ kpkVal) ∗
          memRegion (sret + 164#64) 4) ∗
        kyberStageOut A kpkVal vb m.kyberPreKeyId m.kyberCiphertext kyberBoxPtr kyberBoxLen) ∗
      pkLayoutAt (sret + 168#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 ∗
      (((sret + 200#64) ↦₆₄ ik0) ∗ ((sret + 208#64) ↦₆₄ ik1) ∗
        ((sret + 216#64) ↦₆₄ ik2) ∗ ((sret + 224#64) ↦₆₄ ik3)) ∗
      ((sret + 232#64) ↦₃₂ m.registrationId.getD 0#32) ∗
      ((sret + 236#64) ↦₃₂ sid) ∗
      ((sret + 240#64) ↦₈ (vb >>> 4)) ∗
      memRegion (sret + 241#64) 7) ∗ R ⊢
      RunCompose.pksmResAt A sret (some (pksmModelOf b vb m bk ik sid innerMsg)) :=
  Entails.trans
    (sepConj_mono_left
      (sret_cells_entails_preKeyMsgAt_model A sret b vb m bk ik sid innerMsg
        msgG serBoxPtr kyberBoxPtr kyberBoxLen rk0 rk1 rk2 rk3 addrW0 addrW1 verHi56
        ik0 ik1 ik2 ik3 opkTag opkVal kpkVal b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 w9 w13 w15 w23
        hopkTag hopkVal hpk hrk hik))
    (pksmResAt_some_intro A sret ⟨msgG, serBoxPtr, kyberBoxPtr⟩
      (pksmModelOf b vb m bk ik sid innerMsg) R)

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
