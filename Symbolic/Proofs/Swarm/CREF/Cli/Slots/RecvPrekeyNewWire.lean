/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatementDefs
public import Symbolic.Proofs.Swarm.CREF.Cli.DirInvBridge
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewCodec
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewInv
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Pre-Key Wire Projections and Store Inversions

Relates `PreKeyMessageFields` and `PqParty` store lookups (`pqRecvPrekeyModel`, `trusts`,
`preKeysNamedBy`, `markKyberUsed`) under Bob's `PqPartyInv` to `PreKeyFields`, `parsePreKeyWire`,
`HonestIdentity`, and `.base-keys` replay freshness.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli.Slots

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SignalSession
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup ProtocolSetupWF PreKeyFields HonestIdentity parsePreKeyWire setupPublic pubBytes secretBytes
   ecKey PqFromHonest)
open DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Swarm.CREF
open Symbolic.Swarm.CREF.Cli
open Symbolic.Swarm.TRREF.SpqrSemOf (bytesToVec)
open Symbolic.Swarm.CREF.TR (ekBytes)

/-! ## Key Projections -/

@[simp] theorem djbKey_head? (v : List.Vector (BitVec 8) 32) :
    (djbKey v).head? = some 0x05#8 :=
  rfl

@[simp] theorem djbKey_drop_one (v : List.Vector (BitVec 8) 32) :
    (djbKey v).drop 1 = v.toList :=
  rfl

@[simp] private theorem djbKey_take_33_rpnwa64 (v : List.Vector (BitVec 8) 32) :
    (djbKey v).take 33 = djbKey v :=
  List.take_of_length_le (by simp [djbKey])

theorem djbKey_eq_ecKey (v : List.Vector (BitVec 8) 32) :
    djbKey v = ecKey v.toList :=
  rfl

private theorem djbKey_inj_rpnwa64 {v₁ v₂ : List.Vector (BitVec 8) 32} (h : djbKey v₁ = djbKey v₂) :
    v₁ = v₂ :=
  List.Vector.eq v₁ v₂ (List.cons.inj h).2

/-- Canonical `PreKeyFields` extracted from a typed `PreKeyMessageFields` whose inner `SignalMessage`
decodes to `inner`. -/
def rpkNew_preKeyFieldsOf (m : PreKeyMessageFields) (inner : SignalMessage) : PreKeyFields where
  version := 4
  preKeyId := m.opkId
  signedPreKeyId := m.spkId
  kyberPreKeyId := some m.kpkId
  kyberCiphertext := some (CryptoVerification.E2E.kyberKey m.kyberCt)
  baseKey := djbKey m.baseKey
  identityKey := djbKey m.idPub
  message := m.inner
  inner := inner

theorem parsePreKeyWire_preKeyMsgE_ok (m : PreKeyMessageFields) (inner : SignalMessage)
    (hlen : m.inner.length < 2 ^ 64)
    (htry : SignalMessage.tryFrom protoSignalCodec m.inner = .ok inner) :
    parsePreKeyWire (wirePrekey :: m.bytes) = some (rpkNew_preKeyFieldsOf m inner) := by
  rw [parsePreKeyWire_preKeyMsgE m hlen, htry]
  rfl

@[simp] theorem preKeyFieldsOf_baseKey_take_33 (m : PreKeyMessageFields) (inner : SignalMessage) :
    (rpkNew_preKeyFieldsOf m inner).baseKey.take 33 = djbKey m.baseKey :=
  djbKey_take_33_rpnwa64 m.baseKey

@[simp] theorem ekBytes_preKeyFieldsOf (m : PreKeyMessageFields) (inner : SignalMessage) :
    ekBytes (rpkNew_preKeyFieldsOf m inner) = m.baseKey.toList := by
  simp [ekBytes, rpkNew_preKeyFieldsOf, djbKey]

/-! ## Model and Store Inversions under `PqPartyInv` -/

/-- Inversion of `pqRecvPrekeyModel X P st m rc = some (some (st', pt))` when `st.session = none`. -/
theorem pqRecvPrekeyModel_none_ok_inv {X : UnreachedPqxdhPrimitives} {P : PEParams}
    {st st' : PqParty} {m : PreKeyMessageFields} {rc : BitVec 256} {pt : HwBytes}
    (hsess : st.session = none)
    (h : pqRecvPrekeyModel X P st m rc = some (some (st', pt))) :
    ∃ (inner : SignalMessage) (k : ResponderPreKeySecrets) (x : RecordExtras) (g : GhostState HwBytes) (st1 : PqParty),
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok inner ∧
      st.trusts ⟨⟨m.idPub⟩⟩ = true ∧
      preKeysNamedBy st m = some k ∧
      recvPrekeyState X P st.party st.me k m rc = some (some (x, g, pt)) ∧
      markKyberUsed st m = some st1 ∧
      st' = { removeOpk st1 m with peerId := some ⟨⟨m.idPub⟩⟩, session := some (x, g) } := by
  unfold pqRecvPrekeyModel at h
  cases htry : SignalMessage.tryFrom protoSignalCodec m.inner with
  | error _ => rw [htry] at h; cases h
  | ok inner =>
    rw [htry] at h; dsimp only at h
    cases htr : st.trusts ⟨⟨m.idPub⟩⟩ with
    | false => simp [htr] at h
    | true =>
      simp only [htr, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hsess] at h
      cases hk : preKeysNamedBy st m with
      | none => rw [hk] at h; cases h
      | some k =>
        rw [hk] at h; dsimp only at h
        cases hdec : recvPrekeyState X P st.party st.me k m rc with
        | none => rw [hdec] at h; cases h
        | some opt =>
          rw [hdec] at h
          cases opt with
          | none => cases h
          | some xgpt =>
            rcases xgpt with ⟨x, g, pt'⟩
            cases hmk : markKyberUsed st m with
            | none => rw [hmk] at h; cases h
            | some st1 =>
              rw [hmk] at h; dsimp only at h
              injection h with hsome
              injection hsome with hpair
              injection hpair with hst' hpt
              subst hpt
              exact ⟨inner, k, x, g, st1, rfl, rfl, rfl, hdec, rfl, hst'.symm⟩

/-- Peer identity trust check on Bob's `PqPartyInv` yields `m.idPub` and `HonestIdentity`. -/
theorem pqPartyInv_bob_honestIdentity {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} (hr : ProtocolSetupWF r) (hagree : ModelAgree interp P)
    {accepted : List HwBytes} {stB : PqParty} {d : DirectorySnapshot}
    (hB : PqPartyInv interp P r accepted r.bob stB d)
    {m : PreKeyMessageFields} (hlen : m.inner.length < 2 ^ 64)
    (htrust : stB.trusts ⟨⟨m.idPub⟩⟩ = true) :
    m.idPub = bytesToVec 32 (pubBytes interp (secretBytes r 0)) ∧
    m.idPub.toList = pubBytes interp (secretBytes r 0) ∧
    HonestIdentity interp r (wirePrekey :: m.bytes) := by
  have hpeer_sec : peerIdSecret r r.bob = secretBytes r 0 := by
    unfold peerIdSecret ProtocolSetup.ikASecBytes; simp [hr.1.symm]
  unfold PqParty.trusts at htrust
  rw [hB.peerId_eq, hpeer_sec, decide_eq_true_eq] at htrust
  have hid : bytesToVec 32 (pubBytes interp (secretBytes r 0)) = m.idPub :=
    congrArg (fun x => x.publicKey.bytes) htrust
  have hid_len : (pubBytes interp (secretBytes r 0)).length = 32 :=
    pubBytes_length_of_modelAgree hagree (rpkNew_secretBytes_0_length hr)
  have hid_list : m.idPub.toList = pubBytes interp (secretBytes r 0) := by
    rw [← hid, bytesToVec_toList_of_len hid_len]
  refine ⟨hid.symm, hid_list, fun pf hparse => ?_⟩
  rw [parsePreKeyWire_preKeyMsgE m hlen] at hparse
  cases htry : SignalMessage.tryFrom protoSignalCodec m.inner with
  | error _ => rw [htry] at hparse; cases hparse
  | ok inner =>
    rw [htry, Option.some.injEq] at hparse
    subst hparse
    change (djbKey m.idPub).take 33 = ecKey (pubBytes interp (secretBytes r 0))
    rw [djbKey_take_33_rpnwa64, djbKey_eq_ecKey, hid_list]

/-- Consequences of `preKeysNamedBy stB m = some k` under Bob's `PqPartyInv`. -/
structure BobKeysForPost (r : ProtocolSetup) (used : Bool) (m : PreKeyMessageFields) (k : ResponderPreKeySecrets) : Prop where
  spkId_eq : m.spkId = r.spkId
  k_spkId_eq : k.spkId = r.spkId
  k_spkPriv_eq : k.spkPriv = bytesToVec 32 (secretBytes r 2)
  kpkId_eq : m.kpkId = r.kpkId
  k_kpkId_eq : k.kpkId = r.kpkId
  k_kpkPub_eq : k.kpkPub = bytesToVec 1568 (r.opaqueBytes (setupPublic r 6))
  k_kpkSec_eq : k.kpkSec = bytesToVec 3168 (r.kyberSecB.drop 1)
  opk_cases :
    (m.opkId = none ∧ k.opk = none) ∨
      (r.withOpk = true ∧ used = false ∧ m.opkId = some r.opkId ∧
        k.opk = some (r.opkId, bytesToVec 32 (secretBytes r 6)))

theorem pqPartyInv_bob_keysFor_inv {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} (hne : r.alice ≠ r.bob) {accepted : List HwBytes} {t : CliTurn} {stB : PqParty}
    (hB : PqPartyInv interp P r accepted r.bob stB (t.dirs r.bob))
    {m : PreKeyMessageFields} {k : ResponderPreKeySecrets} (hk : preKeysNamedBy stB m = some k) :
    BobKeysForPost r (t.opkUsed r) m k := by
  obtain ⟨hsigned, hkot, honeTime, ⟨seen, hklr, _, _⟩⟩ := hB.bob_stores hne.symm
  have hopk_char := rpkNew_opkUsed_of_pqPartyInv hne hB
  unfold preKeysNamedBy at hk
  rw [hsigned, hkot, hklr] at hk
  simp only [List.lookup] at hk
  cases hspk_beq : (m.spkId == r.spkId)
  · simp [hspk_beq] at hk
  · have hspk_id : m.spkId = r.spkId := beq_iff_eq.mp hspk_beq
    simp only [hspk_beq] at hk
    cases hkpk_beq : (m.kpkId == r.kpkId)
    · simp [hkpk_beq] at hk
    · have hkpk_id : m.kpkId = r.kpkId := beq_iff_eq.mp hkpk_beq
      simp only [hkpk_beq, Option.map_some] at hk
      cases hopk : m.opkId with
      | none =>
        simp only [hopk, Option.map_some, Option.some.injEq] at hk
        subst hk
        exact ⟨hspk_id, hspk_id, rfl, hkpk_id, hkpk_id, rfl, rfl, Or.inl ⟨hopk, rfl⟩⟩
      | some j =>
        rw [hopk] at hk
        rcases honeTime with ⟨hno, hot_nil⟩ | ⟨hyes, hot_some | hot_none⟩
        · simp [hot_nil] at hk
        · rw [hot_some] at hk
          simp only [List.lookup] at hk
          cases hj_beq : (j == r.opkId)
          · simp [hj_beq] at hk
          · have hj : j = r.opkId := beq_iff_eq.mp hj_beq
            simp only [hj_beq, Option.map_some, Option.some.injEq] at hk
            subst hk
            have hu : t.opkUsed r = false := (hopk_char.2 hyes).1.mpr hot_some
            exact ⟨hspk_id, hspk_id, rfl, hkpk_id, hkpk_id, rfl, rfl,
              Or.inr ⟨hyes, hu, hopk.trans (congrArg some hj), congrArg some (Prod.ext hj rfl)⟩⟩
        · rw [hot_none] at hk
          simp only [List.lookup] at hk
          by_cases hj_beq : (j == r.opkId) = true <;> simp [hj_beq] at hk

theorem opk_ok_of_bobKeysForPost {r : ProtocolSetup} {used : Bool} {m : PreKeyMessageFields} {k : ResponderPreKeySecrets}
    (inner : SignalMessage) (hp : BobKeysForPost r used m k) :
    (rpkNew_preKeyFieldsOf m inner).preKeyId = none ∨
      (r.withOpk = true ∧ used = false ∧ (rpkNew_preKeyFieldsOf m inner).preKeyId = some r.opkId) := by
  rcases hp.opk_cases with ⟨hnone, _⟩ | ⟨hw, hu, hsome, _⟩
  · exact Or.inl hnone
  · exact Or.inr ⟨hw, hu, hsome⟩

/-- Inversion of `markKyberUsed stB m = some st1` under Bob's `PqPartyInv`: proves
`djbKey m.baseKey ∉ accepted` (`pf.baseKey.take 33 ∉ accepted`) and characterizes `st1`. -/
theorem pqPartyInv_bob_markKyberUsed_inv {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} (hne : r.alice ≠ r.bob) {accepted : List HwBytes} {stB st1 : PqParty} {d : DirectorySnapshot}
    (hB : PqPartyInv interp P r accepted r.bob stB d)
    {m : PreKeyMessageFields} (hspk : m.spkId = r.spkId) (hkpk : m.kpkId = r.kpkId)
    (hmk : markKyberUsed stB m = some st1) :
    djbKey m.baseKey ∉ accepted ∧
    st1.party = stB.party ∧
    st1.me = stB.me ∧
    st1.signed = stB.signed ∧
    st1.oneTime = stB.oneTime ∧
    st1.kyberOneTime = [] ∧
    ∃ seen,
      st1.kyberLastResort = [(r.kpkId,
        ⟨bytesToVec 1568 (r.opaqueBytes (setupPublic r 6)),
         bytesToVec 3168 (r.kyberSecB.drop 1),
         bytesToVec 64 (r.opaqueBytes (setupPublic r 7)), 0⟩, seen)] ∧
      (∀ q ∈ seen, q.1 = r.spkId) ∧
      (∀ bk : HwBytes, bk ∈ accepted ++ [djbKey m.baseKey] ↔
        ∃ v : List.Vector (BitVec 8) 32, bk = djbKey v ∧ (r.spkId, v) ∈ seen) := by
  obtain ⟨_, hkot, _, ⟨seen₀, hklr, hseen_spk, hseen_acc⟩⟩ := hB.bob_stores hne.symm
  unfold markKyberUsed at hmk
  rw [hkot, hklr, hkpk, hspk] at hmk
  simp only [List.lookup, beq_self_eq_true] at hmk
  by_cases hover : 37 * seen₀.length > fileCapBytes ∨ (r.spkId, m.baseKey) ∈ seen₀
  · simp [hover] at hmk
  · have hmem : (r.spkId, m.baseKey) ∉ seen₀ := fun hm => hover (Or.inr hm)
    simp only [hover, ↓reduceIte, List.map_cons, List.map_nil, Option.some.injEq] at hmk
    subst hmk
    have hfresh : djbKey m.baseKey ∉ accepted := by
      intro hin_acc
      obtain ⟨v, hv, hv_seen⟩ := (hseen_acc (djbKey m.baseKey)).mp hin_acc
      cases djbKey_inj_rpnwa64 hv
      exact hmem hv_seen
    refine ⟨hfresh, rfl, rfl, rfl, rfl, rfl, seen₀ ++ [(r.spkId, m.baseKey)], rfl, ?_, ?_⟩
    · intro q hq
      rcases List.mem_append.mp hq with hq₀ | hq₁
      · exact hseen_spk q hq₀
      · rw [List.mem_singleton] at hq₁; rw [hq₁]
    · intro bk
      rw [List.mem_append, List.mem_singleton, hseen_acc bk]
      constructor
      · rintro (⟨v, rfl, hv⟩ | rfl)
        · exact ⟨v, rfl, List.mem_append_left _ hv⟩
        · exact ⟨m.baseKey, rfl, List.mem_append_right _ (List.mem_singleton_self _)⟩
      · rintro ⟨v, rfl, hv⟩
        rcases List.mem_append.mp hv with hv₀ | hv₁
        · exact Or.inl ⟨v, rfl, hv₀⟩
        · rw [List.mem_singleton] at hv₁
          exact Or.inr (congrArg djbKey (Prod.mk.inj hv₁).2)

theorem fresh_of_parse_preKeyMsgE {m : PreKeyMessageFields} {accepted : List HwBytes}
    (hlen : m.inner.length < 2 ^ 64) (hfresh : djbKey m.baseKey ∉ accepted) :
    ∀ q, parsePreKeyWire (wirePrekey :: m.bytes) = some q → q.baseKey.take 33 ∉ accepted := by
  intro q hparse
  rw [parsePreKeyWire_preKeyMsgE m hlen] at hparse
  cases htry : SignalMessage.tryFrom protoSignalCodec m.inner with
  | error _ => rw [htry] at hparse; cases hparse
  | ok inner =>
    rw [htry, Option.some.injEq] at hparse
    subst hparse
    simpa [rpkNew_preKeyFieldsOf] using hfresh

end Symbolic.Swarm.CREF.Cli.Slots
