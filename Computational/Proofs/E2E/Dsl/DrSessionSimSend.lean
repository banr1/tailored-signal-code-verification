/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.DrSessionSimHooks
import Computational.Proofs.E2E.ComposedBinaryLinkV1

/-!
# Double Ratchet + SPQR V1 Send Simulator

Constructs the `ReductionDsl` send subprogram `drSendC` over `e2eOps` (parameterized by
`SpqrDslHooks`), bounds its query count and static cost, and proves `Comp.eval` agreement with
`Params.send` and `sessionSchemeFixedSpk.send` under `PartyReachInv`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.DrSessionSimSend

open OracleSpec OracleComp
open ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp bits)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.Ratchet (keyToBytesVec32)
open CryptoGames.SM (sendsInE)
open CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey ChainKey SenderChain
  OutgoingTripleRatchet SessionState GhostState SignalMessage aesCbcEncrypt Mut)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.E2E (Bytes serializedPartyAddresses paramsIdsWithSpqr
  sessionSchemeFixedSpk keyToBytes32_bytesToKey32)
open CryptoVerification.E2E.Costed (e2eSig B U8 U32 BV128 BV256 BV512 IdKey PK PlainT GhostStT
  drSenderChainT drRecvChainT ghostPartsT E2EPureOp E2ECryptoOp e2ePureOps e2eCryptoOps e2eOps
  ghostSplitEval ghostJoinEval partyToBool boolToParty)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp e2eCryptoOp eval_e2ePureOp
  cost_e2ePureOp eval_e2eCryptoOp cost_e2eCryptoOp)
open Computational.Proofs.E2E.Dsl.ClampsLossless (aesCbcEncrypt_length_eq
  e2eCryptoOps_eval_aes256CbcEnc_lossless signalMsgNew_serialized_length_le
  e2eCryptoOps_eval_signalMsgEncode_lossless)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (PartyReachInv
  serializedPartyAddresses_length_le_128 spqrV1Send_pqMsg_length_le_96)
open Computational.Proofs.E2E.Dsl.DrSessionSimHooks (SpqrDslHooks decodeSenderChain
  decodeSenderChain_encodeSenderChain decodeRecvChains_encodeRecvChains salt_roundtrip
  boolToParty_partyToBool_eq chainKey_messageKeys_seed_len ghostSplitEval_eq_of_le
  ghostJoinEval_eq_of_le gpIsB gpVer gpLocId gpRemId gpRk gpPrevCtr gpPend gpEp gpCEps gpSc gpRcs
  gpPqSt gpMk sendAddrsE eval_sendAddrsE cost_sendAddrsE_le sessionVersionEffE
  eval_sessionVersionEffE cost_sessionVersionEffE)

section SendProgram

variable {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "S" => e2eSig ℓ
local notation "OO" => e2eOps ℓ P C K decT encT

@[reducible] def drSendPreT (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .opt (.prod ghostPartsT (.prod drSenderChainT IdKey))

def drSendPreE {Γ : List (Ty S)} (gE : Expr OO Γ GhostStT) : Expr OO Γ (drSendPreT ℓ) :=
  .letE (e2ePureOp .ghostStateSplit gE)
    (.caseOpt (gpSc .v0)
      .none
      (.ite (.lt (e2ePureOp .u32ToNat (sessionVersionEffE (gpVer .v1))) (.nat 256))
        (.caseOpt (gpRemId .v1)
          .none
          (.some (.pair .v2 (.pair .v1 .v0))))
        .none))

theorem cost_drSendPreE_le {Γ : List (Ty S)} (gE : Expr OO Γ GhostStT) :
    (drSendPreE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) gE).cost ≤
      gE.cost + 760 := by
  simp only [drSendPreE, gpSc, gpVer, gpRemId, cost_sessionVersionEffE, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, cost_e2ePureOp, E2EPureOp.cost]
  have hb : bits 256 = 9 := by decide
  rw [hb]
  omega

def drSendPostE {Γ : List (Ty S)}
    (gE : Expr OO Γ GhostStT)
    (mE : Expr OO Γ PlainT)
    (partsE : Expr OO Γ ghostPartsT)
    (scE : Expr OO Γ drSenderChainT)
    (remIdE : Expr OO Γ IdKey)
    (pqOutE : Expr OO Γ (.prod (B 32) (.prod (.opt BV256) (B 32)))) :
    Expr OO Γ (.prod GhostStT (B 32)) :=
  .letE (.pair (.pair gE mE) (.pair partsE (.pair scE (.pair remIdE pqOutE))))
    (let top := .v0
     let g0 : Expr OO _ GhostStT := .fst (.fst top)
     let sc0 : Expr OO _ drSenderChainT := .fst (.snd (.snd top))
     .caseOpt (e2eCryptoOp .chainStep (.snd sc0))
       (.pair g0 (e2ePureOp (.bytesLit 32 []) .unit))
       (let step0 : Expr OO _ (.prod (.prod BV256 U32) BV256) := .v0
        let outer := .v1
        let sc1 : Expr OO _ drSenderChainT := .fst (.snd (.snd outer))
        let pq1 : Expr OO _ (.prod (B 32) (.prod (.opt BV256) (B 32))) :=
          .snd (.snd (.snd (.snd outer)))
        let ckIdx : Expr OO _ U32 := .snd (.snd sc1)
        let salt? : Expr OO _ (.opt BV256) := .fst (.snd pq1)
        .letE (e2eCryptoOp .deriveMsgKeys (.pair (.snd step0) (.pair ckIdx salt?)))
          (let mks : Expr OO _ (.prod BV256 (.prod BV256 (.prod BV128 U32))) := .v0
           let step2 : Expr OO _ (.prod (.prod BV256 U32) BV256) := .v1
           let outer2 := .v2
           let m2 : Expr OO _ PlainT := .snd (.fst outer2)
           let parts2 : Expr OO _ ghostPartsT := .fst (.snd outer2)
           let sc2 : Expr OO _ drSenderChainT := .fst (.snd (.snd outer2))
           let rem2 : Expr OO _ IdKey := .fst (.snd (.snd (.snd outer2)))
           let pq2 : Expr OO _ (.prod (B 32) (.prod (.opt BV256) (B 32))) :=
             .snd (.snd (.snd (.snd outer2)))
           let cipherKey : Expr OO _ BV256 := .fst mks
           let macKey : Expr OO _ BV256 := .fst (.snd mks)
           let iv : Expr OO _ BV128 := .fst (.snd (.snd mks))
           let ct : Expr OO _ (B 32) := e2eCryptoOp .aes256CbcEnc (.pair cipherKey (.pair iv m2))
           let addr? : Expr OO _ (.opt (B 32)) :=
             .ite (gpPend parts2) (sendAddrsE (gpIsB parts2)) .none
           let verU8 : Expr OO _ U8 :=
             e2ePureOp .u8OfNat (e2ePureOp .u32ToNat (sessionVersionEffE (gpVer parts2)))
           let wire : Expr OO _ (B 32) :=
             e2eCryptoOp .signalMsgEncode
               (.pair (.pair verU8 (.pair (.fst (.fst sc2)) (.pair (.snd (.snd sc2)) (gpPrevCtr parts2))))
                 (.pair ct (.pair (.snd (.snd pq2)) (.pair addr?
                   (.pair (gpLocId parts2) (.pair rem2 macKey))))))
           let ep' : Expr OO _ .nat :=
             .ite (sendsInE (gpIsB parts2) (gpEp parts2))
               (gpEp parts2)
               (.add (gpEp parts2) (.nat 1))
           let sc?' : Expr OO _ (.opt drSenderChainT) :=
             .some (.pair (.fst sc2) (.fst step2))
           let g' : Expr OO _ GhostStT :=
             e2ePureOp .ghostStateJoin
               (gpMk (gpIsB parts2) (gpVer parts2) (gpLocId parts2) (gpRemId parts2)
                 (gpRk parts2) (gpPrevCtr parts2) (gpPend parts2) ep' (gpCEps parts2)
                 sc?' (gpRcs parts2) (.fst pq2))
           .pair g' wire)))

theorem cost_drSendPostE_le {Γ : List (Ty S)}
    (gE : Expr OO Γ GhostStT)
    (mE : Expr OO Γ PlainT)
    (partsE : Expr OO Γ ghostPartsT)
    (scE : Expr OO Γ drSenderChainT)
    (remIdE : Expr OO Γ IdKey)
    (pqOutE : Expr OO Γ (.prod (B 32) (.prod (.opt BV256) (B 32)))) :
    (drSendPostE gE mE partsE scE remIdE pqOutE).cost ≤
      gE.cost + mE.cost + partsE.cost + scE.cost + remIdE.cost + pqOutE.cost +
        1400 + 10 * (ℓ / 32 + 1) := by
  have haddr := cost_sendAddrsE_le (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    (gpIsB (.fst (.snd .v2)) :
      Expr OO (.prod BV256 (.prod BV256 (.prod BV128 U32)) ::
        .prod (.prod BV256 U32) BV256 ::
        .prod (.prod GhostStT PlainT)
          (.prod ghostPartsT
            (.prod drSenderChainT
              (.prod IdKey (.prod (B 32) (.prod (.opt BV256) (B 32)))))) :: Γ) .bool)
  have h32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb2 : bits 2 = 2 := by decide
  simp only [drSendPostE, sendsInE, gpIsB, gpVer, gpLocId, gpRemId, gpRk, gpPrevCtr, gpPend,
    gpEp, gpCEps, gpRcs, gpMk, cost_sessionVersionEffE, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, cost_e2ePureOp, cost_e2eCryptoOp,
    E2EPureOp.cost, E2ECryptoOp.cost, h32, hb0, hb1, hb2, List.length_nil] at haddr ⊢
  omega

/-- `ReductionDsl` simulator for `Params.send` and `sessionSchemeFixedSpk.send`. -/
def drSendC (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I : Iface S T) {Γ : List (Ty S)}
    (e : Expr OO Γ (.prod GhostStT (.prod PlainT BV512))) :
    Comp OO I Γ (.prod GhostStT (B 32)) :=
  .bind (.ret e)
    (.caseOpt (drSendPreE (.fst .v0))
      (.ret (.pair (.fst .v0) (e2ePureOp (.bytesLit 32 []) .unit)))
      (.bind (hooks.sendC I (.pair (gpPqSt (.fst .v0)) (.snd (.snd .v1))))
        (.caseOpt .v0
          (.ret (.pair (.fst .v2) (e2ePureOp (.bytesLit 32 []) .unit)))
          (.ret (drSendPostE
            (.fst .v3)
            (.fst (.snd .v3))
            (.fst .v2)
            (.fst (.snd .v2))
            (.snd (.snd .v2))
            .v0)))))

theorem drSendC_queries (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I : Iface S T) {Γ : List (Ty S)}
    (e : Expr OO Γ (.prod GhostStT (.prod PlainT BV512)))
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (drSendC hooks I e).queries w ws = 0 := by
  simp [drSendC, Comp.queries, hooks.sendC_queries]

theorem drSendC_cost (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I : Iface S T) {Γ : List (Ty S)}
    (e : Expr OO Γ (.prod GhostStT (.prod PlainT BV512))) :
    (drSendC hooks I e).cost ≤ e.cost + 67800 + 10 * (ℓ / 32 + 1) := by
  have hpre := cost_drSendPreE_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (.fst .v0 : Expr OO (.prod GhostStT (.prod PlainT BV512) :: Γ) GhostStT)
  have hspqr := hooks.sendC_cost I
    (.pair (gpPqSt (.fst .v0)) (.snd (.snd .v1)) :
      Expr OO (.prod ghostPartsT (.prod drSenderChainT IdKey) ::
        .prod GhostStT (.prod PlainT BV512) :: Γ) (.prod (B 32) BV512))
  have hpost := cost_drSendPostE_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (.fst .v3 : Expr OO (.prod (B 32) (.prod (.opt BV256) (B 32)) ::
      .opt (.prod (B 32) (.prod (.opt BV256) (B 32))) ::
      .prod ghostPartsT (.prod drSenderChainT IdKey) ::
      .prod GhostStT (.prod PlainT BV512) :: Γ) GhostStT)
    (.fst (.snd .v3)) (.fst .v2) (.fst (.snd .v2)) (.snd (.snd .v2)) .v0
  have h32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  simp only [drSendC, gpPqSt, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    cost_e2ePureOp, E2EPureOp.cost, h32, List.length_nil] at hpre hspqr hpost ⊢
  omega

private theorem sendsIn_partyToBool (p : Party) (ep : ℕ) :
    (if partyToBool p then decide (ep % 2 = 0) else decide (ep % 2 = 1)) = p.sendsIn ep := by
  cases p <;> {
    simp only [partyToBool, Party.sendsIn, Bool.false_eq_true, ↓reduceIte]
    apply Bool.eq_iff_iff.mpr
    simp
  }

private theorem mut_exec_bind_s {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    (m >>= f).exec s =
      match m.exec s with
      | (.error e, s') => (.error e, s')
      | (.ok a, s') => (f a).exec s' := by
  unfold Mut.exec
  rw [ExceptT.run_bind, StateT.run_bind]
  rcases StateT.run (ExceptT.run m) s with ⟨err | val, s'⟩ <;> rfl

private theorem outgoingFromSessionState_exec {PQ : Type} [Inhabited PQ] (s : SessionState PQ) :
    OutgoingTripleRatchet.fromSessionState.exec s =
      match s.senderChain with
      | none => (.error (.invalidSessionStructure .missingSenderChain), s)
      | some sc =>
        if 256 ≤ s.version.toNat then
          (.error (.invalidSessionStructure .versionTooLarge), { s with pqRatchetState := default })
        else
          match s.remoteIdentity with
          | none =>
            (.error (.invalidSessionStructure .missingRemoteIdentity),
             { s with pqRatchetState := default })
          | some rem =>
            (.ok ⟨sc.ratchetKey, sc.chainKey, s.previousCounter, s.pqRatchetState,
                  BitVec.ofNat 8 s.version.toNat, s.localIdentity, rem⟩,
             { s with pqRatchetState := default }) := by
  rcases s with ⟨sv, lid, rid, rk, pc, _ | sc, rcs, ppk, pqs⟩
  · rfl
  · unfold OutgoingTripleRatchet.fromSessionState
    rw [mut_exec_bind_s]
    have hg0 : (get : Mut (SessionState PQ) (SessionState PQ)).exec
        ⟨sv, lid, rid, rk, pc, some sc, rcs, ppk, pqs⟩ =
        (.ok ⟨sv, lid, rid, rk, pc, some sc, rcs, ppk, pqs⟩,
         ⟨sv, lid, rid, rk, pc, some sc, rcs, ppk, pqs⟩) := rfl
    rw [hg0]
    dsimp only
    rw [mut_exec_bind_s]
    have htpq : SessionState.takePqRatchetState.exec
        ⟨sv, lid, rid, rk, pc, some sc, rcs, ppk, pqs⟩ =
        (.ok pqs, ⟨sv, lid, rid, rk, pc, some sc, rcs, ppk, default⟩) := rfl
    rw [htpq]
    dsimp only
    rw [mut_exec_bind_s]
    have hg1 : (get : Mut (SessionState PQ) (SessionState PQ)).exec
        ⟨sv, lid, rid, rk, pc, some sc, rcs, ppk, default⟩ =
        (.ok ⟨sv, lid, rid, rk, pc, some sc, rcs, ppk, default⟩,
         ⟨sv, lid, rid, rk, pc, some sc, rcs, ppk, default⟩) := rfl
    rw [hg1]
    dsimp only
    have hver : (⟨sv, lid, rid, rk, pc, some sc, rcs, ppk, (default : PQ)⟩ : SessionState PQ).version =
        (⟨sv, lid, rid, rk, pc, some sc, rcs, ppk, pqs⟩ : SessionState PQ).version := rfl
    rw [hver]
    by_cases hv : 256 ≤ (⟨sv, lid, rid, rk, pc, some sc, rcs, ppk, pqs⟩ : SessionState PQ).version.toNat
    · simp only [hv, ↓reduceIte]
      rfl
    · simp only [hv, ↓reduceIte]
      rcases rid with _ | rem <;> rfl

private theorem outgoingEncrypt_exec {PQ PQC : Type} (C' : Crypto)
    (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec)
    (spqr : CryptoGames.LibsignalSession.Spqr PQ PQC)
    (ptext : List (BitVec 8)) (addresses : Option (List (BitVec 8))) (coins : PQC)
    (o : OutgoingTripleRatchet PQ) :
    (OutgoingTripleRatchet.encrypt C' codec spqr ptext addresses coins).exec o =
      if spqr.sendPanics o.pqrState coins then
        (.error .panic, o)
      else
        match spqr.send o.pqrState coins with
        | none => (.error .invalidState, o)
        | some (newPqrState, pqrKey, pqrMsg) =>
          let mks := (o.senderChainKey.messageKeys C'.F).generateKeys C'.F pqrKey
          let ctext := aesCbcEncrypt C'.E mks.cipherKey mks.iv ptext
          let message := SignalMessage.new C'.F codec o.sessionVersion mks.macKey addresses
            o.senderRatchetKey.publicKey o.senderChainKey.index o.previousCounter ctext
            o.localIdentityKey o.remoteIdentityKey pqrMsg
          match o.senderChainKey.nextChainKey C'.F with
          | .error e => (.error e, o)
          | .ok next =>
            (.ok message, { o with senderChainKey := next, pqrState := newPqrState }) := by
  unfold OutgoingTripleRatchet.encrypt
  rw [mut_exec_bind_s]
  have hg0 : (get : Mut (OutgoingTripleRatchet PQ) (OutgoingTripleRatchet PQ)).exec o =
      (.ok o, o) := rfl
  rw [hg0]
  dsimp only
  cases hpan : spqr.sendPanics o.pqrState coins with
  | true =>
    simp only [↓reduceIte]
    rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rcases hsend : spqr.send o.pqrState coins with _ | ⟨newPqrState, pqrKey, pqrMsg⟩
    · rfl
    · dsimp only
      rw [mut_exec_bind_s]
      rcases hnext : o.senderChainKey.nextChainKey C'.F with err | next <;> rfl

theorem params_send_wire_length_le (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (g : GhostState Bytes) (m : Plain ℓ) (r : BitVec 512) :
    ((paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB).send g m.toList r).2.length ≤
      32 * (ℓ / 32) + 450 := by
  let prm := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  dsimp only [CryptoGames.LibsignalSession.Params.send, SessionState.messageEncrypt]
  rw [outgoingFromSessionState_exec]
  rcases hsc : g.session.senderChain with _ | sc
  · simp
  · dsimp only
    by_cases hver : 256 ≤ g.session.version.toNat
    · simp [hver]
    · simp only [hver, ↓reduceIte]
      rcases hrem : g.session.remoteIdentity with _ | remId
      · simp
      · dsimp only
        have hprmC :
            (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB).C = C := rfl
        have hprmCodec :
            (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB).codec =
              protoSignalCodec := rfl
        have hprmSpqr :
            (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB).spqr =
              spqrV1SessionUniformCoins C.F K := rfl
        rw [hprmC, hprmCodec, hprmSpqr, outgoingEncrypt_exec]
        dsimp only
        by_cases hpan : (spqrV1SessionUniformCoins C.F K).sendPanics g.session.pqRatchetState r
        · simp [hpan]
        · have hpan_f :
              (spqrV1SessionUniformCoins C.F K).sendPanics g.session.pqRatchetState r = false :=
            Bool.eq_false_iff.mpr hpan
          simp only [hpan_f, Bool.false_eq_true, ↓reduceIte]
          rcases hsend : (spqrV1SessionUniformCoins C.F K).send g.session.pqRatchetState r with
            _ | ⟨pq', pqrKey, pqMsg⟩
          · simp
          · dsimp only
            rcases hnext : sc.chainKey.nextChainKey C.F with _ | nextCk
            · simp
            · dsimp only
              have hct_len :
                  (aesCbcEncrypt C.E
                    ((sc.chainKey.messageKeys C.F).generateKeys C.F pqrKey).cipherKey
                    ((sc.chainKey.messageKeys C.F).generateKeys C.F pqrKey).iv
                    m.toList).length ≤ 32 * (ℓ / 32 + 2) := by
                rw [aesCbcEncrypt_length_eq C.E _ _ m]
                omega
              have hpq_len : pqMsg.length ≤ 96 :=
                spqrV1Send_pqMsg_length_le_96 C.F K g.session.pqRatchetState r hsend
              have haddr_len :
                  ∀ a ∈ g.session.encryptAddresses (prm.sendAddrs g.party), a.length ≤ 128 := by
                intro a ha
                dsimp only [SessionState.encryptAddresses] at ha
                cases hpend : g.session.pendingPreKey
                · simp [hpend] at ha
                · simp only [hpend, ↓reduceIte, prm, paramsIdsWithSpqr,
                    CryptoGames.LibsignalSession.Params.sendAddrs] at ha
                  cases hp : g.party <;> simp only [hp] at ha <;>
                    exact serializedPartyAddresses_length_le_128 uuidTryParse _ _ a ha
              exact signalMsgNew_serialized_length_le C.F _ _ _ _ _ _ _ _ _ _
                hct_len hpq_len haddr_len

theorem drSendC_eval_params (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I : Iface S T) {Γ : List (Ty S)}
    (e : Expr OO Γ (.prod GhostStT (.prod PlainT BV512))) (ρ : Env Γ)
    (idA idB : IdentityKey)
    (hg : PartyReachInv C K (e.eval ρ).1) :
    (drSendC hooks I e).eval ρ =
      pure ((paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB).send
        (e.eval ρ).1 (e.eval ρ).2.1.toList (e.eval ρ).2.2) := by
  rcases he : e.eval ρ with ⟨g, ⟨m, r⟩⟩
  rw [he] at hg
  let spqr := spqrV1SessionUniformCoins C.F K
  let prm := paramsIdsWithSpqr C spqr idA idB
  have hrc5 : g.session.receiverChains.length ≤ 5 := hg.receiverChains_le_five
  have hsplit := ghostSplitEval_eq_of_le (ℓ := ℓ) hrc5
  simp only [drSendC, drSendPreE, Comp.eval, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    Env.get, pure_bind, he, eval_e2ePureOp, E2EPureOp.eval, hsplit,
    gpSc, gpVer, gpRemId, gpPqSt, eval_sessionVersionEffE]
  dsimp only [CryptoGames.LibsignalSession.Params.send, SessionState.messageEncrypt]
  rw [outgoingFromSessionState_exec]
  dsimp only [SessionState.version]
  rcases hsc : g.session.senderChain with _ | sc
  · simp
  · dsimp only [Option.map]
    by_cases hver_lt :
        (if g.session.sessionVersion = 0 then (2 : BitVec 32) else g.session.sessionVersion).toNat <
          256
    · have hver_nle :
          ¬ (256 ≤ (if g.session.sessionVersion = 0 then (2 : BitVec 32)
            else g.session.sessionVersion).toNat) := by omega
      simp only [decide_eq_true_eq, hver_lt, hver_nle, ↓reduceIte]
      rcases hrem : g.session.remoteIdentity with _ | remId
      · simp
      · dsimp only
        have hprmC :
            (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB).C = C := rfl
        have hprmCodec :
            (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB).codec =
              protoSignalCodec := rfl
        have hprmSpqr :
            (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB).spqr =
              spqrV1SessionUniformCoins C.F K := rfl
        rw [hprmC, hprmCodec, hprmSpqr]
        rw [hooks.sendC_eval I _ _ (by simp only [Expr.eval, Env.get]; exact hg.topTight)]
        simp only [Expr.eval, Env.get, pure_bind]
        rw [outgoingEncrypt_exec]
        dsimp only
        by_cases hpan : (spqrV1SessionUniformCoins C.F K).sendPanics g.session.pqRatchetState r
        · simp [hpan]
        · have hpan_f :
              (spqrV1SessionUniformCoins C.F K).sendPanics g.session.pqRatchetState r = false :=
            Bool.eq_false_iff.mpr hpan
          simp only [hpan_f, Bool.false_eq_true, ↓reduceIte]
          rcases hsend : (spqrV1SessionUniformCoins C.F K).send g.session.pqRatchetState r with
            _ | ⟨pq', pqrKey, pqMsg⟩
          · simp
          · simp only [Option.map_some, drSendPostE, sendsInE, gpIsB, gpVer, gpLocId, gpRemId,
              gpRk, gpPrevCtr, gpPend, gpEp, gpCEps, gpRcs, gpMk, Expr.eval, Expr.v0, Expr.v1,
              Expr.v2, Env.get, eval_e2ePureOp, eval_e2eCryptoOp, eval_sendAddrsE,
              eval_sessionVersionEffE, E2EPureOp.eval, E2ECryptoOp.eval]
            have hck_eq :
                ({ key := (DrSessionSimHooks.encodeSenderChain (ℓ := ℓ) sc).2.1
                   index := (DrSessionSimHooks.encodeSenderChain (ℓ := ℓ) sc).2.2 } : ChainKey) =
                sc.chainKey := by
              rcases sc with ⟨_, ⟨_, _⟩⟩; rfl
            rw [hck_eq]
            rcases hnext : sc.chainKey.nextChainKey C.F with _ | nextCk
            · simp
            · dsimp only
              congr 1
              have hseed :
                  keyToBytes32 (bytesToKey32 (sc.chainKey.messageKeys C.F).seed) =
                    (sc.chainKey.messageKeys C.F).seed :=
                keyToBytes32_bytesToKey32 _ (chainKey_messageKeys_seed_len C.F sc.chainKey)
              have hidx_eq :
                  (DrSessionSimHooks.encodeSenderChain (ℓ := ℓ) sc).2.2 = sc.chainKey.index := rfl
              have hpub_eq :
                  (DrSessionSimHooks.encodeSenderChain (ℓ := ℓ) sc).1.1 =
                    sc.ratchetKey.publicKey := rfl
              have hgen_eq :
                  ({ seed := keyToBytes32 (bytesToKey32 (sc.chainKey.messageKeys C.F).seed)
                     counter := (DrSessionSimHooks.encodeSenderChain (ℓ := ℓ) sc).2.2 } :
                      CryptoGames.LibsignalSession.MessageKeyGenerator) =
                    sc.chainKey.messageKeys C.F := by
                rw [hseed, hidx_eq]
                rfl
              rw [salt_roundtrip pqrKey, hgen_eq]
              let mks := (sc.chainKey.messageKeys C.F).generateKeys C.F pqrKey
              have henc_lossless :
                  (aesCbcEncrypt C.E mks.cipherKey mks.iv m.toList).take (32 * (ℓ / 32 + 2)) =
                    aesCbcEncrypt C.E mks.cipherKey mks.iv m.toList := by
                have hlen := aesCbcEncrypt_length_eq C.E mks.cipherKey mks.iv m
                exact List.take_of_length_le (by omega)
              rw [henc_lossless, boolToParty_partyToBool_eq, hpub_eq, hidx_eq]
              have hct_len :
                  (aesCbcEncrypt C.E mks.cipherKey mks.iv m.toList).length ≤ 32 * (ℓ / 32 + 2) := by
                rw [aesCbcEncrypt_length_eq C.E _ _ m]
                omega
              have hpq_len : pqMsg.length ≤ 96 :=
                spqrV1Send_pqMsg_length_le_96 C.F K g.session.pqRatchetState r hsend
              have haddr_len :
                  ∀ a ∈ g.session.encryptAddresses (prm.sendAddrs g.party), a.length ≤ 128 := by
                intro a ha
                dsimp only [SessionState.encryptAddresses] at ha
                cases hpend : g.session.pendingPreKey
                · simp [hpend] at ha
                · simp only [hpend, ↓reduceIte, prm, paramsIdsWithSpqr,
                    CryptoGames.LibsignalSession.Params.sendAddrs] at ha
                  cases hp : g.party <;> simp only [hp] at ha <;>
                    exact serializedPartyAddresses_length_le_128 uuidTryParse _ _ a ha
              have hsig_lossless :
                  (SignalMessage.new C.F protoSignalCodec
                    (BitVec.ofNat 8
                      (if g.session.sessionVersion = 0 then (2 : BitVec 32)
                       else g.session.sessionVersion).toNat)
                    mks.macKey (g.session.encryptAddresses (prm.sendAddrs g.party))
                    sc.ratchetKey.publicKey sc.chainKey.index g.session.previousCounter
                    (aesCbcEncrypt C.E mks.cipherKey mks.iv m.toList)
                    g.session.localIdentity remId pqMsg).serialized.take
                      (32 * (2 * (ℓ / 32) + 24)) =
                  (SignalMessage.new C.F protoSignalCodec
                    (BitVec.ofNat 8
                      (if g.session.sessionVersion = 0 then (2 : BitVec 32)
                       else g.session.sessionVersion).toNat)
                    mks.macKey (g.session.encryptAddresses (prm.sendAddrs g.party))
                    sc.ratchetKey.publicKey sc.chainKey.index g.session.previousCounter
                    (aesCbcEncrypt C.E mks.cipherKey mks.iv m.toList)
                    g.session.localIdentity remId pqMsg).serialized := by
                have hlen := signalMsgNew_serialized_length_le C.F
                  (BitVec.ofNat 8
                    (if g.session.sessionVersion = 0 then (2 : BitVec 32)
                     else g.session.sessionVersion).toNat)
                  mks.macKey (g.session.encryptAddresses (prm.sendAddrs g.party))
                  sc.ratchetKey.publicKey sc.chainKey.index g.session.previousCounter
                  (aesCbcEncrypt C.E mks.cipherKey mks.iv m.toList)
                  g.session.localIdentity remId pqMsg
                  hct_len hpq_len haddr_len
                exact List.take_of_length_le (by omega)
              refine Prod.ext ?_ ?_
              · have hrcs_len :
                    (g.session.receiverChains.map
                      (DrSessionSimHooks.encodeRecvChain (ℓ := ℓ))).length ≤ 5 := by
                  simpa using hrc5
                rw [ghostJoinEval_eq_of_le _ _ _ _ _ _ _ _ _ _ _ _ hrcs_len,
                  boolToParty_partyToBool_eq,
                  decodeRecvChains_encodeRecvChains g.session.receiverChains hg.messageKeySeed_eq,
                  sendsIn_partyToBool]
                have hsc_upd :
                    decodeSenderChain (ℓ := ℓ)
                      ((DrSessionSimHooks.encodeSenderChain (ℓ := ℓ) sc).1,
                       (nextCk.key, nextCk.index)) =
                    { sc with chainKey := nextCk } := by
                  rcases sc with ⟨⟨pub, priv⟩, ⟨_, _⟩⟩
                  rcases nextCk with ⟨_, _⟩
                  simp [DrSessionSimHooks.encodeSenderChain, decodeSenderChain]
                dsimp only [OutgoingTripleRatchet.applyToSessionState, Option.map]
                rw [hsc_upd]
              · dsimp only
                refine (?_ : _ =
                  (SignalMessage.new C.F protoSignalCodec
                    (BitVec.ofNat 8
                      (if g.session.sessionVersion = 0 then (2 : BitVec 32)
                       else g.session.sessionVersion).toNat)
                    mks.macKey (g.session.encryptAddresses (prm.sendAddrs g.party))
                    sc.ratchetKey.publicKey sc.chainKey.index g.session.previousCounter
                    (aesCbcEncrypt C.E mks.cipherKey mks.iv m.toList)
                    g.session.localIdentity remId pqMsg).serialized.take
                      (32 * (2 * (ℓ / 32) + 24))).trans hsig_lossless
                congr 2
    · have hver_le :
          256 ≤ (if g.session.sessionVersion = 0 then (2 : BitVec 32)
            else g.session.sessionVersion).toNat := by omega
      simp only [decide_eq_true_eq, hver_lt, hver_le, ↓reduceIte]

/-- `Comp.eval` agreement of `drSendC` with `sessionSchemeFixedSpk.send` under `PartyReachInv`. -/
theorem drSendC_eval (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I : Iface S T) {Γ : List (Ty S)}
    (e : Expr OO Γ (.prod GhostStT (.prod PlainT BV512))) (ρ : Env Γ)
    (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (hg : PartyReachInv C K (e.eval ρ).1) :
    (drSendC hooks I e).eval ρ =
      pure ((sessionSchemeFixedSpk
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins).send
        (e.eval ρ).1 (e.eval ρ).2.1 (e.eval ρ).2.2) :=
  drSendC_eval_params hooks I e ρ idA idB hg

end SendProgram

end Computational.Proofs.E2E.Dsl.DrSessionSimSend
