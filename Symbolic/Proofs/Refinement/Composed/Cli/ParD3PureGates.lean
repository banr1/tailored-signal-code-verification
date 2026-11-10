/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.World.HeldRecPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewWire
public import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyPromModel
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptBinPure
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptHypsPure
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTieNormPure
public import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.BranchesBPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.OooRpkPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPureA
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyPromAccept
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.TRREF.EncodeRecordPqInj

/-!
# Pre-Key Parser, Matching, and Session-Record Lemmas

Proves parser inversions, `PreKeyFieldsEquiv` contract transfer lemmas, session-matching
equivalences (`PqFieldsMatch`, `EligibleForSessionPromotion`, `PqSessionMatches`), model evaluation
for matching pre-key decryption (`pqRecvMatchingFieldsModel_accept_eval`), and previous-session
stripping lemmas for `noMatchRecordBytes`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace DY.Libsignal.Composed.Refinement.Cli.ParD3

open DY (Participant)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent StateAndMessage)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup ProtocolSetupWF OpaqueSymbolSemantics PreKeyFields ecKeyParses parsePreKey parsePreKeyWire decodePreKey
   EligibleForSessionPromotion SingleSession HonestIdentity PqFromHonest LeakableSecret recordBytes msgField
   ecKey kyberKey secretBytes opkRemovedIdx preKeySpqrIndex)
open DY.Libsignal.Composed.Refinement.Cli
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
  (PreKeyMessageFields UnreachedPqxdhPrimitives PEParams RecordExtras ReachablePqxdhSession wireWhisper wirePrekey encodeRecordUnderExtras
   encStateUnderExtras lenField pqxdhSpqrSession pqxdhSessionParams djbKey)
open CryptoVerification.E2E.RecordX
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.SignalSession
  (PqParty PqSessionMatches PqxdhPartyInSpecDomain)
open Symbolic.Swarm.CREF.CliPure
  (RecvAcceptContractPure RpkAcceptBin pureStripBytes pureStripPrev promAccBlk)
open Symbolic.Swarm.CREF.Cli
  (pqSession sessionToRecordRecPending BobPromDirInv PromPureAcceptOut ModelHookBridge rpkPromMid)

/-! ## Wire-tag and parser inversions -/

theorem wirePrekey_eq_wirePrekeyTag : wirePrekey = wirePrekeyTag := by decide

theorem wireWhisper_eq_wireWhisperTag : wireWhisper = wireWhisperTag := by decide

@[simp]
theorem parsePreKeyWire_wirePrekey_cons (body : HwBytes) :
    parsePreKeyWire (wirePrekey :: body) = parsePreKey body := by
  unfold parsePreKeyWire
  rw [wirePrekey_eq_wirePrekeyTag]
  simp

theorem ecKeyParses_take33 {b : HwBytes} (h : ecKeyParses b = true) :
    b.take 33 = 5#8 :: (vec32 (b.drop 1)).toList ∧
      (b.drop 1).take 32 = (vec32 (b.drop 1)).toList := by
  unfold ecKeyParses at h
  cases b with
  | nil => simp at h
  | cons hd tl =>
    simp only [List.head?_cons, Bool.and_eq_true, beq_iff_eq, Option.some.injEq,
      decide_eq_true_eq, List.length_cons] at h
    rcases h with ⟨rfl, hlen⟩
    have htl32 : 32 ≤ tl.length := by omega
    have hvec : (vec32 tl).toList = tl.take 32 := by
      change (tl ++ List.replicate 32 0#8).take 32 = tl.take 32
      exact List.take_append_of_le_length htl32
    dsimp only [List.drop_succ_cons, List.drop_zero, List.take_succ_cons]
    exact ⟨congrArg (5#8 :: ·) hvec.symm, hvec.symm⟩

theorem drop1_take32_eq_take33_drop1 (b : HwBytes) :
    (b.drop 1).take 32 = (b.take 33).drop 1 := by
  cases b <;> rfl

theorem parsePreKey_some_inv {body : HwBytes} {q : PreKeyFields}
    (hq : parsePreKey body = some q) :
    ecKeyParses q.baseKey = true ∧
      ecKeyParses q.identityKey = true ∧
      SignalMessage.tryFrom protoSignalCodec q.message = .ok q.inner ∧
      (q.version = 3 ∨ q.version = 4) := by
  cases body with
  | nil => simp [parsePreKey] at hq
  | cons vb rest =>
    unfold parsePreKey at hq
    dsimp only at hq
    split_ifs at hq with hver
    cases hdec : decodePreKey rest with
    | none => rw [hdec] at hq; cases hq
    | some raw =>
      rw [hdec] at hq
      rcases hbk : raw.baseKey with _ | bk
      · simp [hbk] at hq
      rcases hik : raw.identityKey with _ | ik
      · simp [hbk, hik] at hq
      rcases hmsg : raw.message with _ | msg
      · simp [hbk, hik, hmsg] at hq
      rcases hsid : raw.signedPreKeyId with _ | sid
      · simp [hbk, hik, hmsg, hsid] at hq
      simp only [hbk, hik, hmsg, hsid] at hq
      split_ifs at hq with hok
      cases htry : SignalMessage.tryFrom protoSignalCodec msg with
      | error _ => rw [htry] at hq; cases hq
      | ok inner =>
        rw [htry] at hq
        injection hq with hq_eq
        subst hq_eq
        simp only [Bool.and_eq_true] at hok
        exact ⟨hok.1.2, hok.2, htry, by dsimp; omega⟩

/-! ## `preKeyOfBody?` inversion and `PreKeyFieldsEquiv` transfer -/

/-- Fieldwise equivalence of two `PreKeyFields` records up to trailing EC key bytes past 33. -/
structure PreKeyFieldsEquiv (p q : PreKeyFields) : Prop where
  version_eq : p.version = q.version
  preKeyId_eq : p.preKeyId = q.preKeyId
  signedPreKeyId_eq : p.signedPreKeyId = q.signedPreKeyId
  kyberPreKeyId_eq : p.kyberPreKeyId = q.kyberPreKeyId
  kyberCiphertext_eq : p.kyberCiphertext = q.kyberCiphertext
  baseKey_take33_eq : p.baseKey.take 33 = q.baseKey.take 33
  identityKey_take33_eq : p.identityKey.take 33 = q.identityKey.take 33
  message_eq : p.message = q.message
  inner_eq : p.inner = q.inner

theorem PreKeyFieldsEquiv.ekBytes_eq {p q : PreKeyFields} (h : PreKeyFieldsEquiv p q) :
    Symbolic.Swarm.CREF.TR.ekBytes p = Symbolic.Swarm.CREF.TR.ekBytes q := by
  unfold Symbolic.Swarm.CREF.TR.ekBytes
  rw [drop1_take32_eq_take33_drop1, drop1_take32_eq_take33_drop1, h.baseKey_take33_eq]

theorem PreKeyFieldsEquiv.spqrIdx_eq {p q : PreKeyFields} (h : PreKeyFieldsEquiv p q) :
    preKeySpqrIndex p = preKeySpqrIndex q := by
  unfold preKeySpqrIndex
  rw [h.inner_eq]

theorem preKeyOfBody?_some_inv {body : HwBytes} {m : PreKeyMessageFields}
    (hm : preKeyOfBody? body = some m) :
    ∃ q : PreKeyFields,
      parsePreKey body = some q ∧
      q.version = 4 ∧
      m.inner = q.message ∧
      q.preKeyId = m.opkId ∧
      q.signedPreKeyId = m.spkId ∧
      q.kyberPreKeyId = some m.kpkId ∧
      q.kyberCiphertext = some (kyberKey m.kyberCt.toList) ∧
      q.baseKey.take 33 = djbKey m.baseKey ∧
      q.identityKey.take 33 = djbKey m.idPub ∧
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok q.inner := by
  unfold preKeyOfBody? at hm
  cases hq : parsePreKey body with
  | none => rw [hq] at hm; cases hm
  | some q =>
    rw [hq] at hm
    cases hraw : decodePreKey (body.drop 1) with
    | none => rw [hraw] at hm; cases hm
    | some raw =>
      rw [hraw] at hm
      dsimp only at hm
      split_ifs at hm with hv4
      cases hkid : q.kyberPreKeyId with
      | none => rw [hkid] at hm; cases hm
      | some kid =>
        cases hct : q.kyberCiphertext with
        | none => rw [hkid, hct] at hm; cases hm
        | some ctBytes =>
          cases ctBytes with
          | nil => rw [hkid, hct] at hm; cases hm
          | cons t ct =>
            rw [hkid, hct] at hm
            dsimp only at hm
            split at hm
            · next htag =>
              injection hm with hm_eq
              obtain ⟨hbk_ok, hik_ok, htry, _⟩ := parsePreKey_some_inv hq
              have hbk33 := (ecKeyParses_take33 hbk_ok).1
              have hik33 := (ecKeyParses_take33 hik_ok).1
              have hct_m : m.kyberCt.toList = ct :=
                congrArg (fun z => z.kyberCt.toList) hm_eq.symm
              have hkct : q.kyberCiphertext = some (kyberKey m.kyberCt.toList) := by
                rw [hct, hct_m, htag.1]; rfl
              refine ⟨q, rfl, hv4, ?_, ?_, ?_, ?_, hkct, ?_, ?_, ?_⟩
              · rw [← hm_eq]
              · rw [← hm_eq]
              · rw [← hm_eq]
              · rw [← hm_eq, hkid]
              · rw [← hm_eq]; exact hbk33
              · rw [← hm_eq]; exact hik33
              · rw [← hm_eq]; exact htry
            · cases hm

theorem preKeyFieldsEquiv_rpkNew_of_preKeyOfBody? {body : HwBytes} {m : PreKeyMessageFields}
    {q : PreKeyFields} {inner : SignalMessage}
    (hm : preKeyOfBody? body = some m)
    (hq : parsePreKey body = some q)
    (htry : SignalMessage.tryFrom protoSignalCodec m.inner = .ok inner) :
    PreKeyFieldsEquiv (Symbolic.Swarm.CREF.Cli.Slots.rpkNew_preKeyFieldsOf m inner) q := by
  obtain ⟨q', hq', hv4, hminner, hopk, hspk, hkpk, hkct, hbk, hik, htry_q⟩ :=
    preKeyOfBody?_some_inv hm
  cases Option.some.inj (hq.symm.trans hq')
  have hinner : inner = q.inner := Except.ok.inj (htry.symm.trans htry_q)
  subst hinner
  refine
    { version_eq := hv4.symm
      preKeyId_eq := hopk.symm
      signedPreKeyId_eq := hspk.symm
      kyberPreKeyId_eq := hkpk.symm
      kyberCiphertext_eq := hkct.symm
      baseKey_take33_eq := (Symbolic.Swarm.CREF.Cli.Slots.preKeyFieldsOf_baseKey_take_33 m q.inner).trans hbk.symm
      identityKey_take33_eq := by
        have hid_take :
            (Symbolic.Swarm.CREF.Cli.Slots.rpkNew_preKeyFieldsOf m q.inner).identityKey.take 33 =
              djbKey m.idPub := by
          change (ecKey m.idPub.toList).take 33 = 5#8 :: m.idPub.toList
          exact List.take_of_length_le (by simp [ecKey])
        exact hid_take.trans hik.symm
      message_eq := hminner
      inner_eq := rfl }

theorem PreKeyFieldsEquiv.bobSaltSeedBytes_eq {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {p q : PreKeyFields} (h : PreKeyFieldsEquiv p q) (ct_wire : HwBytes) :
    Symbolic.Swarm.CREF.TR.bobSaltSeedBytes interp r S p ct_wire =
      Symbolic.Swarm.CREF.TR.bobSaltSeedBytes interp r S q ct_wire := by
  unfold Symbolic.Swarm.CREF.TR.bobSaltSeedBytes
  rw [h.ekBytes_eq, h.preKeyId_eq, h.inner_eq, h.spqrIdx_eq]

theorem PreKeyFieldsEquiv.bobExpectedMacBytes_eq {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {p q : PreKeyFields} (h : PreKeyFieldsEquiv p q) (ct_wire : HwBytes) :
    Symbolic.Swarm.CREF.TR.bobExpectedMacBytes interp r S p ct_wire =
      Symbolic.Swarm.CREF.TR.bobExpectedMacBytes interp r S q ct_wire := by
  unfold Symbolic.Swarm.CREF.TR.bobExpectedMacBytes
  rw [h.ekBytes_eq, h.preKeyId_eq, h.inner_eq, h.spqrIdx_eq, h.message_eq]

theorem PreKeyFieldsEquiv.recvAcceptContractPure {interp : ExternInterpretation} {r : ProtocolSetup}
    {used : Bool} {b b' : HwBytes} {sm : StateAndMessage} {p q : PreKeyFields}
    {d ct_wire pt : HwBytes}
    (heq : PreKeyFieldsEquiv p q)
    (hp' : parsePreKeyWire b' = some q)
    (hc : RecvAcceptContractPure interp r used b sm p d ct_wire pt) :
    RecvAcceptContractPure interp r used b' sm q d ct_wire pt where
  parse := hp'
  outer_ver := heq.version_eq ▸ hc.outer_ver
  spkId_eq := heq.signedPreKeyId_eq ▸ hc.spkId_eq
  kpkId_eq := heq.kyberPreKeyId_eq ▸ hc.kpkId_eq
  kyber_ct := heq.kyberCiphertext_eq ▸ hc.kyber_ct
  ct_len := hc.ct_len
  d_len := hc.d_len
  opk_ok := heq.preKeyId_eq ▸ hc.opk_ok
  opk_removed := heq.preKeyId_eq ▸ hc.opk_removed
  counter_le := heq.inner_eq ▸ hc.counter_le
  pqRatchet_ne_nil := heq.inner_eq ▸ hc.pqRatchet_ne_nil
  version := heq.inner_eq ▸ hc.version
  baseKey_ok := heq.baseKey_take33_eq ▸ hc.baseKey_ok
  ratchetKey_ok := heq.inner_eq ▸ hc.ratchetKey_ok
  mac_eq := fun S hS => by
    rw [← heq.bobExpectedMacBytes_eq, ← heq.message_eq]
    exact hc.mac_eq S hS
  dec_eq := fun S hS => by
    rw [← heq.inner_eq, ← heq.bobSaltSeedBytes_eq]
    exact hc.dec_eq S hS

theorem PreKeyFieldsEquiv.rpkAcceptBin {p q : PreKeyFields} {sm : StateAndMessage}
    (heq : PreKeyFieldsEquiv p q) (hb : RpkAcceptBin p sm) :
    RpkAcceptBin q sm := by
  rcases hb with ⟨hrec, hkyb, hbk⟩
  exact ⟨heq.baseKey_take33_eq ▸ hrec, hkyb, hbk.trans heq.baseKey_take33_eq⟩

theorem PreKeyFieldsEquiv.acceptRecTie {r : ProtocolSetup} {p q : PreKeyFields}
    {st' : SessionState HwBytes} {sm : StateAndMessage}
    (heq : PreKeyFieldsEquiv p q)
    (ht : Symbolic.Swarm.CREF.CliPure.AcceptRecTie r p (p.baseKey.take 33) st' sm) :
    Symbolic.Swarm.CREF.CliPure.AcceptRecTie r q (q.baseKey.take 33) st' sm := by
  unfold Symbolic.Swarm.CREF.CliPure.AcceptRecTie at ht ⊢
  rwa [← heq.baseKey_take33_eq]

theorem PreKeyFieldsEquiv.acceptSt0ModelInvs {interp : ExternInterpretation} {r : ProtocolSetup}
    {p q : PreKeyFields} {st0 : SessionState HwBytes}
    (heq : PreKeyFieldsEquiv p q)
    (hi : Symbolic.Swarm.CREF.CliPure.AcceptSt0ModelInvs interp r p st0) :
    Symbolic.Swarm.CREF.CliPure.AcceptSt0ModelInvs interp r q st0 := by
  unfold Symbolic.Swarm.CREF.CliPure.AcceptSt0ModelInvs at hi ⊢
  rw [← heq.ekBytes_eq, ← heq.preKeyId_eq, ← heq.kyberCiphertext_eq,
      ← heq.baseKey_take33_eq, ← heq.inner_eq, ← heq.message_eq]
  exact hi

theorem PreKeyFieldsEquiv.acceptTieD {interp : ExternInterpretation} {r : ProtocolSetup}
    {p q : PreKeyFields} {d pt : HwBytes} {sm : StateAndMessage}
    (heq : PreKeyFieldsEquiv p q)
    (ht : Symbolic.Swarm.CREF.CliPure.AcceptD.AcceptTieD interp r p d pt sm) :
    Symbolic.Swarm.CREF.CliPure.AcceptD.AcceptTieD interp r q d pt sm := by
  obtain ⟨st0, st', expected, hrt, hinv, hsk, hdec⟩ := ht
  refine ⟨st0, st', expected, heq.acceptRecTie hrt, heq.acceptSt0ModelInvs hinv, hsk, ?_⟩
  rwa [← heq.inner_eq]

theorem PreKeyFieldsEquiv.honestIdentity {interp : ExternInterpretation} {r : ProtocolSetup}
    {b b' : HwBytes} {p q : PreKeyFields}
    (heq : PreKeyFieldsEquiv p q)
    (hp : parsePreKeyWire b = some p)
    (hp' : parsePreKeyWire b' = some q)
    (hhon : HonestIdentity interp r b) :
    HonestIdentity interp r b' := by
  intro q₀ hq₀
  cases Option.some.inj (hq₀.symm.trans hp')
  rw [← heq.identityKey_take33_eq]
  exact hhon p hp

theorem PreKeyFieldsEquiv.fresh {accepted : List HwBytes} {b b' : HwBytes}
    {p q : PreKeyFields}
    (heq : PreKeyFieldsEquiv p q)
    (hp : parsePreKeyWire b = some p)
    (hp' : parsePreKeyWire b' = some q)
    (hfr : ∀ q₀, parsePreKeyWire b = some q₀ → q₀.baseKey.take 33 ∉ accepted) :
    ∀ q₀, parsePreKeyWire b' = some q₀ → q₀.baseKey.take 33 ∉ accepted := by
  intro q₀ hq₀
  cases Option.some.inj (hq₀.symm.trans hp')
  rw [← heq.baseKey_take33_eq]
  exact hfr p hp

/-! ## Session-matching equivalences -/

private theorem bv32_toNat_eq_four_iff (v : BitVec 32) :
    v.toNat = 4 ↔ v = 4#32 := by
  constructor
  · intro h
    exact BitVec.eq_of_toNat_eq (by simpa using h)
  · rintro rfl; rfl

theorem encodeRecordX_eq_recordBytes_of_wfPq {P : PEParams} {st : PqParty}
    {x : RecordExtras} {g : GhostState HwBytes}
    (hwf : PqxdhPartyInSpecDomain P st) (hsess : st.session = some (x, g)) :
    encodeRecordUnderExtras (fun _ => x) g =
      recordBytes (sessionToRecordRecPending (pqSession x g)) := by
  have hlen31 : (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31 :=
    (Symbolic.Swarm.CREF.Cli.reachPqInvPure_of_wfPq hwf hsess).2.2
  have henc := Symbolic.Swarm.CREF.Cli.encodeRecordX_eq_encodeRecord_pqSession x g
  have hlt63 : (CryptoVerification.E2E.Record.encodeRecord ⟨some (pqSession x g)⟩).length < 2 ^ 63 := by
    rw [← henc]; omega
  exact henc.trans (Symbolic.Swarm.CREF.Cli.recordBytes_sessionToRecordRecPending_of_encodeRecord_lt
    (pqSession x g) hlt63).symm

theorem promoteMatch_of_pqFieldsMatch {P : PEParams} {st : PqParty}
    {x : RecordExtras} {g : GhostState HwBytes} {body : HwBytes} {q : PreKeyFields}
    (hwf : PqxdhPartyInSpecDomain P st) (hsess : st.session = some (x, g))
    (hq : parsePreKey body = some q)
    (hfm : PqFieldsMatch x g q) :
    EligibleForSessionPromotion (encodeRecordUnderExtras (fun _ => x) g) (wirePrekey :: body) := by
  refine ⟨sessionToRecordRecPending (pqSession x g), q,
    encodeRecordX_eq_recordBytes_of_wfPq hwf hsess, rfl, ?_, hfm.1⟩
  simpa using hq

theorem pqFieldsMatch_of_promoteMatch_v4 {P : PEParams} {st : PqParty}
    {x : RecordExtras} {g : GhostState HwBytes} {body : HwBytes} {q : PreKeyFields}
    (hwf : PqxdhPartyInSpecDomain P st) (hsess : st.session = some (x, g))
    (hq : parsePreKey body = some q) (hv4 : q.version = 4)
    (hprom : EligibleForSessionPromotion (encodeRecordUnderExtras (fun _ => x) g) (wirePrekey :: body)) :
    PqFieldsMatch x g q := by
  obtain ⟨rr, p, hrb, _, hp, habk⟩ := hprom
  rw [parsePreKeyWire_wirePrekey_cons] at hp
  cases Option.some.inj (hp.symm.trans hq)
  have hrb_sx := encodeRecordX_eq_recordBytes_of_wfPq hwf hsess
  have hnorm := Symbolic.Swarm.CREF.TR.recordBytes_injective (hrb.symm.trans hrb_sx)
  have habk_sx : rr.current.aliceBaseKey = x.aliceBaseKey := by
    simpa [Symbolic.Swarm.CREF.TR.normPending, Symbolic.Swarm.CREF.TR.normPendingS,
      sessionToRecordRecPending, pqSession,
      Swarm.Phase0WholeFunctionBridge.sessionToSessionRec] using
      congrArg (fun r => r.current.aliceBaseKey) hnorm
  have hsver : g.session.sessionVersion = 4#32 :=
    Symbolic.Swarm.CREF.Cli.pqSession_sessionVersion_of_wfPq hwf hsess
  exact ⟨habk_sx.symm.trans habk, by rw [hsver, hv4]; rfl⟩

theorem pqFieldsMatch_iff_pqSessionMatches (x : RecordExtras) (g : GhostState HwBytes)
    {body : HwBytes} {q : PreKeyFields} {m : PreKeyMessageFields}
    (hq : parsePreKey body = some q) (hm : preKeyOfBody? body = some m) :
    PqFieldsMatch x g q ↔ PqSessionMatches x g m := by
  obtain ⟨q', hq', hv4, _, _, _, _, _, hbk, _, _⟩ := preKeyOfBody?_some_inv hm
  cases Option.some.inj (hq.symm.trans hq')
  unfold PqFieldsMatch PqSessionMatches
  rw [hbk, hv4]
  exact and_congr_right' (bv32_toNat_eq_four_iff g.session.sessionVersion)

/-! ## Matching pre-key decryption evaluation -/

theorem pqRecvMatchingFieldsModel_ok_inv {P : PEParams} {st st' : PqParty}
    {x : RecordExtras} {g : GhostState HwBytes} {q : PreKeyFields}
    {rc : BitVec 256} {pt : HwBytes}
    (hok : pqRecvMatchingFieldsModel P st x g q rc = some (some (st', pt))) :
    let idA : IdentityKey := ⟨⟨vec32 (q.identityKey.drop 1)⟩⟩
    ∃ s : SessionState HwBytes,
      st.trusts idA = true ∧
      g.session.remoteIdentity = some idA ∧
      SessionState.tryDecryptFromRecord P.C (pqxdhSpqrSession P)
        ((pqxdhSessionParams P).expectedAddrs g.party) q.inner .preKey rc g.session = (.ok pt, s) ∧
      st' = { st with peerId := some idA, session := some (x, { g with session := s }) } := by
  intro idA
  unfold pqRecvMatchingFieldsModel at hok
  have hlet : (⟨⟨vec32 (q.identityKey.drop 1)⟩⟩ : IdentityKey) = idA := rfl
  rw [hlet] at hok
  cases htr : st.trusts idA
  · simp [htr] at hok
  simp only [htr, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
  split_ifs at hok with hrem
  · cases hok
  · have hrem_eq : g.session.remoteIdentity = some idA := Decidable.of_not_not hrem
    rcases hdec : SessionState.tryDecryptFromRecord P.C (pqxdhSpqrSession P)
        ((pqxdhSessionParams P).expectedAddrs g.party) q.inner .preKey rc g.session with ⟨err | pt0, s⟩
    · rw [hdec] at hok
      cases err <;> cases hok
    · rw [hdec] at hok
      simp only [Option.some.injEq, Prod.mk.injEq] at hok
      rcases hok with ⟨hst', hpt⟩
      subst hpt
      exact ⟨s, rfl, hrem_eq, rfl, hst'.symm⟩

theorem honestIdentity_of_matching_trusts {interp : ExternInterpretation} {W : PEParams}
    {r : ProtocolSetup} {st : PqParty} {rec_ body : HwBytes} {q : PreKeyFields}
    (hinv : BobPromDirInv interp W r st rec_)
    (hq : parsePreKey body = some q)
    (htrusts : st.trusts ⟨⟨vec32 (q.identityKey.drop 1)⟩⟩ = true) :
    HonestIdentity interp r (wirePrekey :: body) ∧
      st.peerId = some ⟨⟨vec32 (q.identityKey.drop 1)⟩⟩ := by
  obtain ⟨kA, hkA, hkA_ser⟩ := hinv.peerId
  have hkA_eq : kA = ⟨⟨vec32 (q.identityKey.drop 1)⟩⟩ := by
    unfold PqParty.trusts at htrusts
    rw [hkA] at htrusts
    exact of_decide_eq_true htrusts
  subst hkA_eq
  obtain ⟨_, hik_ok, _, _⟩ := parsePreKey_some_inv hq
  have hik33 := (ecKeyParses_take33 hik_ok).1
  refine ⟨fun p hp => ?_, hkA⟩
  rw [parsePreKeyWire_wirePrekey_cons] at hp
  cases Option.some.inj (hp.symm.trans hq)
  exact hik33.trans hkA_ser

theorem pqRecvMatchingFieldsModel_accept_eval
    {interp : ExternInterpretation} {W : PEParams}
    {r : ProtocolSetup} {records : Participant → Option HwBytes}
    {st st' : PqParty} {x : RecordExtras} {g : GhostState HwBytes}
    {rec_ body c_coins pt : HwBytes} {q : PreKeyFields}
    (hb : ModelHookBridge interp W)
    (hinv : BobPromDirInv interp W r st rec_)
    (hsess : st.session = some (x, g))
    (hrec_eq : rec_ = encodeRecordUnderExtras (fun _ => x) g)
    (hrec_bob : records r.bob = some rec_)
    (hooo_all : Symbolic.Swarm.CREF.COooAll records)
    (hbkn : Symbolic.Swarm.CREF.PureBobKyberNone r records)
    (hc_coins : c_coins.length = 32)
    (hq : parsePreKey body = some q)
    (hok : pqRecvMatchingFieldsModel W st x g q (HKDF.bytesToKey32 c_coins) =
      some (some (st', pt))) :
    ∃ (s : SessionState HwBytes) (g₁ : GhostState HwBytes)
      (coins : BitVec 256) (sess sess' : Session HwBytes),
      let rec' := encodeRecordUnderExtras (fun _ => x) { g with session := s }
      let mid := rpkPromMid interp x g q.inner c_coins
      st' = { st with session := some (x, { g with session := s }) } ∧
      ReachablePqxdhSession W st.me x g₁ ∧ g₁.party = g.party ∧ g₁.session = s ∧
      HonestIdentity interp r (wirePrekey :: body) ∧
      PromPureAcceptOut interp r rec_ (wirePrekey :: body) rec' mid pt
        q sess sess' coins ((pqxdhSessionParams W).expectedAddrs .B) := by
  obtain ⟨s, htrusts, hrem_idA, hdec, hst'⟩ := pqRecvMatchingFieldsModel_ok_inv hok
  obtain ⟨hhon_wire, hpeer_eq⟩ := honestIdentity_of_matching_trusts hinv hq htrusts
  have hst'_eq : st' = { st with session := some (x, { g with session := s }) } := by
    rw [hst', ← hpeer_eq]
  obtain ⟨_, _, htry, _⟩ := parsePreKey_some_inv hq
  have hg_party : g.party = .B := (hinv.wfSt.1 x g hsess).2.1.trans hinv.party
  obtain ⟨g₁, hrpq₁, hp₁, hs₁⟩ :=
    Symbolic.Swarm.CREF.Cli.rpkProm_reachPq_promote hinv.wfSt hsess htry hdec
  let sess := pqSession x g
  let sess' : Session HwBytes :=
    { sess with state := s, pendingPreKey := none, pendingKyberPreKey := none }
  let expected := (pqxdhSessionParams W).expectedAddrs .B
  have hcan_in := hrec_eq ▸ Symbolic.Swarm.CREF.Cli.recordCanonical_Q_of_wfPq hinv.wfSt hsess
  have hrem_some : sess.state.remoteIdentity.isSome = true := by
    change g.session.remoteIdentity.isSome = true; rw [hrem_idA]; rfl
  have hdecW_rc : Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW
      (Proofs.libsignal.Hooks2.cryptoOf' interp)
      (Proofs.libsignal.SR.interpW interp) (Symbolic.Swarm.CREF.CliPure.pureSpqrOf interp)
      expected q.inner .preKey (HKDF.bytesToKey32 c_coins) sess.state = (.ok pt, s) := by
    rw [← Symbolic.Swarm.CREF.Cli.rpkProm_cliPureSpqrOf_eq interp,
        ← Symbolic.Swarm.CREF.Cli.tryDecryptFromRecord_eq_tryDecryptFromRecordW_of_bridge hb]
    dsimp [expected, sess, pqSession]
    rwa [← hg_party]
  have hparse_c : parsePreKeyWire (wirePrekey :: body) = some q := by simpa using hq
  have hkyb_none : sess.pendingKyberPreKey = none :=
    Symbolic.Swarm.CREF.Cli.rpkProm_sess_pendingKyberPreKey_none hinv.wfSt hsess hrec_eq hrec_bob hbkn
  have hooo_in : Symbolic.Swarm.CREF.SpqrOooBounded sess.state.pqRatchetState := by
    have hooo_rec := hooo_all r.bob rec_ hrec_bob
    rwa [Symbolic.Swarm.CREF.CliPure.RpkCli.pqStateOf_of_canonical_Q hcan_in] at hooo_rec
  have hpq_in_lt : sess.state.pqRatchetState.length < 2 ^ 32 :=
    Symbolic.Swarm.CREF.Cli.recordScopeP_of_wfPq hinv.wfSt hsess sess rfl
  have hlen31_in : (CryptoVerification.E2E.Record.encodeRecord ⟨some sess⟩).length < 2 ^ 31 := by
    rw [← Symbolic.Swarm.CREF.Cli.encodeRecordX_eq_encodeRecord_pqSession]
    exact (hinv.wfSt.1 x g hsess).2.2
  have hpost_of_coins : ∀ (mid : List MachineEvent) (coins : BitVec 256),
      ((coins = 0#256 ∧ mid = []) ∨
        (∃ rb : HwBytes, mid = [.rng rb] ∧ rb.length = 32 ∧
          coins = Symbolic.Swarm.CREF.CliPure.RpkCli.pinCoins (some rb) ∧
          Symbolic.Swarm.CREF.CliPure.pureDrawsCoins (Proofs.libsignal.Hooks2.cryptoOf' interp)
            sess.state q.inner.senderRatchetKey = true)) →
      (mid = [] → Symbolic.Swarm.CREF.CliPure.pureDrawsCoins (Proofs.libsignal.Hooks2.cryptoOf' interp)
        sess.state q.inner.senderRatchetKey = false) →
      Symbolic.Swarm.CREF.CliPure.PureDecryptCoinsOk (Proofs.libsignal.Hooks2.cryptoOf' interp)
        sess.state q.inner.senderRatchetKey coins →
      Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW
        (Proofs.libsignal.Hooks2.cryptoOf' interp)
        (Proofs.libsignal.SR.interpW interp) (Symbolic.Swarm.CREF.CliPure.pureSpqrOf interp)
        expected q.inner .preKey coins sess.state = (.ok pt, s) →
      PromPureAcceptOut interp r rec_ (wirePrekey :: body)
        (encodeRecordUnderExtras (fun _ => x) { g with session := s }) mid pt
        q sess sess' coins expected := by
    intro mid coins hcoins hnodraw hdecOk hdecW
    obtain ⟨hv_eq, hexec, hppk_s⟩ :=
      Symbolic.Swarm.CREF.Cli.rpkProm_tryDecryptFromRecordW_ok_inv hdecW
    have hsver : sess.state.sessionVersion = 4#32 :=
      Symbolic.Swarm.CREF.Cli.pqSession_sessionVersion_of_wfPq hinv.wfSt hsess
    have hsver_nat : sess.state.version.toNat = 4 := by
      unfold SessionState.version; rw [hsver]; decide
    have hver : q.inner.messageVersion = 4#8 :=
      BitVec.eq_of_toNat_eq (by rw [← hv_eq, hsver_nat]; rfl)
    obtain ⟨hooo_s, hpq_growth⟩ :=
      Symbolic.Swarm.CREF.CliPure.RpkCli.spqrOooBounded_recvPrekey_promote
        (Proofs.libsignal.Hooks2.cryptoOf' interp) (Proofs.libsignal.SR.interpW interp) interp
        expected q.inner .preKey coins sess s pt hexec hooo_in hpq_in_lt
    have hsess'_g1 : sess' = pqSession x g₁ := by
      simp [sess', sess, pqSession, hs₁, hppk_s]
    have hstate : encodeRecordUnderExtras (fun _ => x) { g with session := s } =
        CryptoVerification.E2E.Record.encodeRecord ⟨some sess'⟩ :=
      Symbolic.Swarm.CREF.Cli.encodeRecordX_clearPending_eq_storedSession x g s hppk_s
    have hrec'_g1 : encodeRecordUnderExtras (fun _ => x) { g with session := s } =
        encodeRecordUnderExtras (fun _ => x) g₁ :=
      Symbolic.Swarm.CREF.Cli.rpkProm_encodeRecordX_session_congr x { g with session := s } g₁ hs₁.symm
    have hinv₁ := Symbolic.Swarm.CREF.Cli.reachPq_inv hrpq₁
    have hcaps' : Symbolic.Swarm.TRREF.GrowthRecord.DRCaps sess' := by
      rw [hsess'_g1]; exact Symbolic.Swarm.CREF.Cli.rpkProm_drCaps_of_reachPqInv hinv₁
    have hext_le : Symbolic.Swarm.TRREF.GrowthRecord.extLen sess' ≤
        Symbolic.Swarm.TRREF.GrowthRecord.extLen sess :=
      Symbolic.Swarm.TRREF.GrowthRecord.extLen_decrypt_le sess s
    have hlen_enc_out : (CryptoVerification.E2E.Record.encodeRecord ⟨some sess'⟩).length < 2 ^ 32 :=
      Symbolic.Swarm.TRREF.GrowthRecord.encodeRecord_lt_of_growth
        sess sess' hcaps' hext_le hpq_growth (by omega)
    have hlen_out : (encodeRecordUnderExtras (fun _ => x) { g with session := s }).length < 2 ^ 32 := by
      rwa [hstate]
    have hwrc : Symbolic.Swarm.CREF.TR.Pure.WireRecCanon
        (encodeRecordUnderExtras (fun _ => x) { g with session := s }) := by
      rw [hrec'_g1]
      exact Symbolic.Swarm.CREF.Cli.rpkProm_wireRecCanon_of_reachPqInv hinv₁ (hs₁ ▸ hppk_s)
        (by rwa [← hrec'_g1])
    have hooo_out : Symbolic.Swarm.CREF.SpqrOooBounded
        (Symbolic.Swarm.CREF.pqStateOf (encodeRecordUnderExtras (fun _ => x) { g with session := s })) := by
      obtain ⟨sess₁, hrc₁, _, _, _, h62, _⟩ := hwrc
      rw [Symbolic.Swarm.CREF.CliPure.RpkCli.pqStateOf_of_canonical_Q hrc₁,
          Symbolic.Swarm.TRREF.EncodeRecordPqInj.encodeRecord_pq_inj_of_eq hrc₁.1 hstate h62]
      exact hooo_s
    have hcanon_out : (encodeRecordUnderExtras (fun _ => x) { g with session := s }).length < 2 ^ 32 - 2 ^ 20 →
        Symbolic.Swarm.CREF.TR.PureTRRecordCanon r r.bob
          (encodeRecordUnderExtras (fun _ => x) { g with session := s }) :=
      Symbolic.Swarm.CREF.CliPure.RpkCli.cref_trRecordCanon_of_wireRecCanon_pqInj r r.bob hwrc hstate hooo_s
    exact ⟨hparse_c, hcan_in, hcoins, hdecOk, hexec, rfl, rfl, hkyb_none.symm,
      hstate, hlen_out, hwrc, hooo_out, hcanon_out, hver, hnodraw⟩
  by_cases hdraws :
      Symbolic.Swarm.CREF.CliPure.pureDrawsCoins (Proofs.libsignal.Hooks2.cryptoOf' interp)
        sess.state q.inner.senderRatchetKey = true
  · have hmid_eq : rpkPromMid interp x g q.inner c_coins = [.rng c_coins] := by
      unfold rpkPromMid; split_ifs with hd <;> [rfl; exact absurd hdraws hd]
    have hcoins_eq := Symbolic.Swarm.CREF.Cli.rpkProm_pureCoinsOf_eq_bytesToKey32 hc_coins
    have hdecOk : Symbolic.Swarm.CREF.CliPure.PureDecryptCoinsOk
        (Proofs.libsignal.Hooks2.cryptoOf' interp) sess.state q.inner.senderRatchetKey
        (HKDF.bytesToKey32 c_coins) := by
      rw [← hcoins_eq]
      exact Symbolic.Swarm.CREF.CliPure.pureDecryptCoinsOk_of_draws_true
        (Proofs.libsignal.Hooks2.cryptoOf' interp) sess.state q.inner.senderRatchetKey
        c_coins hdraws (by omega)
    have hout := hpost_of_coins [.rng c_coins] (HKDF.bytesToKey32 c_coins)
      (Or.inr ⟨c_coins, rfl, hc_coins, hcoins_eq.symm, hdraws⟩) (fun h => nomatch h) hdecOk hdecW_rc
    exact ⟨s, g₁, HKDF.bytesToKey32 c_coins, sess, sess', hst'_eq, hrpq₁, hp₁, hs₁,
      hhon_wire, hmid_eq ▸ hout⟩
  · have hdraws_f :
        Symbolic.Swarm.CREF.CliPure.pureDrawsCoins (Proofs.libsignal.Hooks2.cryptoOf' interp)
          sess.state q.inner.senderRatchetKey = false :=
      Bool.eq_false_iff.mpr hdraws
    have hmid_eq : rpkPromMid interp x g q.inner c_coins = [] := by
      unfold rpkPromMid; split_ifs with hd <;> [exact absurd hd hdraws; rfl]
    have hdecW_zero : Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW
        (Proofs.libsignal.Hooks2.cryptoOf' interp)
        (Proofs.libsignal.SR.interpW interp) (Symbolic.Swarm.CREF.CliPure.pureSpqrOf interp)
        expected q.inner .preKey 0#256 sess.state = (.ok pt, s) := by
      rwa [← Symbolic.Swarm.CREF.Cli.tryDecryptFromRecordW_coins_irrel_of_drawsCoins_false
        (Proofs.libsignal.Hooks2.cryptoOf' interp) (Proofs.libsignal.SR.interpW interp)
        (Symbolic.Swarm.CREF.CliPure.pureSpqrOf interp) expected q.inner .preKey
        (HKDF.bytesToKey32 c_coins) 0#256 sess.state hrem_some
        ((Symbolic.Swarm.CREF.Cli.rpkProm_cliDrawsCoins_eq _ _ _).trans hdraws_f)]
    have hdecOk := Symbolic.Swarm.CREF.CliPure.pureDecryptCoinsOk_of_draws_false
      (Proofs.libsignal.Hooks2.cryptoOf' interp) sess.state q.inner.senderRatchetKey hdraws_f
    have hout := hpost_of_coins [] 0#256 (Or.inl ⟨rfl, rfl⟩) (fun _ => hdraws_f) hdecOk hdecW_zero
    exact ⟨s, g₁, 0#256, sess, sess', hst'_eq, hrpq₁, hp₁, hs₁, hhon_wire, hmid_eq ▸ hout⟩

/-! ## Previous-session record stripping -/

theorem encStateX_clearPending_length_lt {x : RecordExtras} {g : GhostState HwBytes}
    (hlen : (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31) :
    (encStateUnderExtras x { g.session with pendingPreKey := false }).length < 2 ^ 64 := by
  simp only [encodeRecordUnderExtras, CryptoVerification.E2E.msgField, lenField, encStateUnderExtras] at hlen ⊢
  cases g.session.pendingPreKey
  · simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_nil] at hlen ⊢
    omega
  · simp only [↓reduceIte, Bool.false_eq_true, List.length_append, List.length_nil] at hlen ⊢
    omega

theorem noMatchRecordBytes_ne_nil (x : RecordExtras) (g : GhostState HwBytes)
    (x' : RecordExtras) (g' : GhostState HwBytes) :
    noMatchRecordBytes x g x' g' ≠ [] := by
  unfold noMatchRecordBytes
  rw [Symbolic.Swarm.CREF.Cli.encodeRecordX_eq_encodeRecord_pqSession x' g']
  intro h
  exact Symbolic.Swarm.CREF.Cli.rpkProm_encodeRecord_some_ne_nil (pqSession x' g')
    (List.append_eq_nil_iff.mp h).1

theorem noMatchRecordBytes_eq_recordBytes {x : RecordExtras} {g : GhostState HwBytes}
    {x' : RecordExtras} {g' : GhostState HwBytes}
    (hlen : (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31)
    (hlen' : (encodeRecordUnderExtras (fun _ => x') g').length < 2 ^ 63) :
    noMatchRecordBytes x g x' g' =
      recordBytes
        { sessionToRecordRecPending (pqSession x' g') with
          previous := [encStateUnderExtras x { g.session with pendingPreKey := false }] } := by
  have henc' := Symbolic.Swarm.CREF.Cli.encodeRecordX_eq_encodeRecord_pqSession x' g'
  have hlt63' :
      (CryptoVerification.E2E.Record.encodeRecord ⟨some (pqSession x' g')⟩).length < 2 ^ 63 := by
    rwa [← henc']
  have hrb' :=
    (Symbolic.Swarm.CREF.Cli.recordBytes_sessionToRecordRecPending_of_encodeRecord_lt
      (pqSession x' g') hlt63').symm
  have hprev64 := encStateX_clearPending_length_lt hlen
  have hlen_msg :
      lenField 2 (encStateUnderExtras x { g.session with pendingPreKey := false }) =
        msgField 2 (encStateUnderExtras x { g.session with pendingPreKey := false }) :=
    (Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 2 _ hprev64).symm
  unfold noMatchRecordBytes
  rw [henc', hrb', hlen_msg]
  unfold recordBytes
  simp [sessionToRecordRecPending]

theorem pureStripBytes_noMatchRecordBytes {x : RecordExtras} {g : GhostState HwBytes}
    {x' : RecordExtras} {g' : GhostState HwBytes}
    (hlen : (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31)
    (hlen' : (encodeRecordUnderExtras (fun _ => x') g').length < 2 ^ 63) :
    pureStripBytes (noMatchRecordBytes x g x' g') = encodeRecordUnderExtras (fun _ => x') g' := by
  have henc' := Symbolic.Swarm.CREF.Cli.encodeRecordX_eq_encodeRecord_pqSession x' g'
  have hlt63' :
      (CryptoVerification.E2E.Record.encodeRecord ⟨some (pqSession x' g')⟩).length < 2 ^ 63 := by
    rwa [← henc']
  have hrb' :=
    Symbolic.Swarm.CREF.Cli.recordBytes_sessionToRecordRecPending_of_encodeRecord_lt
      (pqSession x' g') hlt63'
  rw [noMatchRecordBytes_eq_recordBytes hlen hlen',
      Symbolic.Swarm.CREF.CliPure.pureStripBytes_recordBytes]
  have hrr :
      ({ { sessionToRecordRecPending (pqSession x' g') with
           previous := [encStateUnderExtras x { g.session with pendingPreKey := false }] } with
         previous := [] } : DY.Libsignal.Rust.RecordRec) =
        sessionToRecordRecPending (pqSession x' g') := rfl
  rw [hrr, hrb', henc']

theorem pureStripBytes_encodeRecordX {x : RecordExtras} {g : GhostState HwBytes}
    (hlen : (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 63) :
    pureStripBytes (encodeRecordUnderExtras (fun _ => x) g) = encodeRecordUnderExtras (fun _ => x) g := by
  have henc := Symbolic.Swarm.CREF.Cli.encodeRecordX_eq_encodeRecord_pqSession x g
  have hlt63 :
      (CryptoVerification.E2E.Record.encodeRecord ⟨some (pqSession x g)⟩).length < 2 ^ 63 := by
    rwa [← henc]
  have hrb :=
    Symbolic.Swarm.CREF.Cli.recordBytes_sessionToRecordRecPending_of_encodeRecord_lt
      (pqSession x g) hlt63
  have hsing : SingleSession (encodeRecordUnderExtras (fun _ => x) g) :=
    ⟨sessionToRecordRecPending (pqSession x g), henc.trans hrb.symm, rfl⟩
  exact Symbolic.Swarm.CREF.CliPure.pureStripBytes_of_singleSession hsing

end DY.Libsignal.Composed.Refinement.Cli.ParD3
