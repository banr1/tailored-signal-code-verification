/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux
import LibsignalBinary.Proofs.E2E.V1.ReachSteps
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Oblig.EncSessionInj
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbState

@[expose] public section

set_option autoImplicit false

/-!
# SPQR V1 Point-Slice (`K ≤ 640`) and `ChainParamsPB` Preservation Across Sessions

Proves preservation of the tight SPQR V1 `PolyEncoder` point-slice cap (`ValidStatePtsAt K` for
`576 ≤ K`, specialized at `K = 640`) and `ChainParamsPB` domain bounds (`ValidStateChainParams`)
across `spqrV1Init`, `spqrV1.send`, `spqrV1.recv`, and `ReachablePqxdhSession`, and lifts them to
CLI session records (`RecordSpqrTightValid`, `PeerSpqrTightValidAt`) for `.send` and `.recv`.
-/

namespace LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps

open Arm64.Process (bytesOfString)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.HKDF (Salt)
open CryptoGames.LibsignalSession
  (GhostState KeyPair SessionState ShaCompress SignalMessage SpqrDirection
   initializeInitiatorSession initializeRecipientSession maxReceiverChains rootCreateChain)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.E2E
  (LocalIdentity PEParams PreKeyMessageFields ReachablePqxdhSession RecordExtras
   acceptInput initiateInput keyPairOf modelPrims ofU8 pqxdhSessionParams responderRecordExtras
   wirePrekey wireWhisper)
open CryptoVerification.E2E.Record (receive_eq_afterRecv send_eq_afterSend toRecord)
open CryptoVerification.E2E.RecordX (extrasOf sessionOfX toRecord_extrasOf_eq)
open CryptoVerification.E2E.V1 (messageEncrypt_ok_props_gen tryDecryptFromRecord_ok_props_gen)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chain ChainPB Direction EpochSecret HkdfFn MessageKey MlKem PqRatchetState
   PqRatchetStatePB Recv Send SpqrApiError SpqrApiPanic SpqrApiResult States V1State Version
   VersionNegotiationPB chainFrom chainFromVersionNegotiation initInner initialState
   libsignalChainParams libsignalSpqrParams liftStatesResult messageKeyToSalt? pbToPqRatchetState
   pqRatchetStateToPb recv recvKeyToSalt? send sendAfterStates spqrAuthApi spqrDeps spqrHkdfWith
   spqrPolyApi spqrV1 spqrV1Init spqrV1InitialStateFor spqrV1SessionUniformCoins spqrV1_eq
   toSpqrModel)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeState spqrDecodeState)
open CryptoVerification.LibsignalTripleRatchet (SeedsLen32)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession
  (CliPqxdhInputs Cmd Inputs PqParty PqxdhPartyInSpecDomain bundleDir partyAddress pqInitInputs
   pqRecvInputs pqSendInputs)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.KitInst (cliSessionStoreSpec)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV cliIo encodeInjOn_scopeIn parseArgs ratchetScopeCoversPq_scopeIn)
open CryptoVerification.SignalSession.Cli.RunCompose (addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (loadRec_scopeKit_eq w1SessKit)
open CryptoVerification.SignalSession.Cli.RunRefine (parseArgs_init parseArgs_recv parseArgs_send)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots
  (callPeer_of_cmd encodeInjOn_deserializeScopeP_Q filesOkPeer_pqRecv filesOkPeer_pqSend loadRec
   loadRec_pqRecv loadRec_pqSend loadRec_unique partyAddr pqSessBytes_le_fileCapBytes scopeIn
   scopeKit)
open CryptoVerification.SignalSession.Cli.Slots.PqValid
  (initiateStateV1 paramsPV1 pqRatchetState_length_le_encodeRecordX reachPq_inv recvPrekeyStateV1)
open CryptoVerification.SpqrV1.Top.StateSize
  (encodeState_len_lt_recv encodeState_len_lt_send encodeState_length_le_rawPqState
   except_bind_eq_ok initInner_spqrDeps_raw_le optRaw_none optRaw_some rawPqState rawVN
   sendAfterStates_raw_le)
open CryptoVerification.SpqrV1Sync.Codec (decodeState_spqrDeps_encodeState_pb spqrDecodeState_encodeState)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (PeerSpqrValid)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux
  (EncPtsBoundedAt StatesPtsBoundedAt ValidChainPBParams ValidChainParams ValidChainParamsPB
   ValidEncPbPtsAt ValidEncoderPts640 ValidEncoderPtsAt ValidOptEncPbPtsAt ValidPqChainParams
   ValidPqPtsAt ValidV1PtsAt ValidVNParams chainAddEpoch_params_eq chainNew_params_eq
   chainRecvKey_params_eq chainSendKey_params_eq encPtsBoundedAt_of_encoderFromPb
   encPtsBoundedAt_of_expectEncodeBytes_le encPtsBoundedAt_of_nextChunk spqrEncTightPtsCap
   statesPtsBoundedAt_of_from_pb statesPtsBoundedAt_of_recv statesPtsBoundedAt_of_send
   validChainPBParams_intoPb validChainParamsPB_default
   validChainParamsPB_of_chainFrom validChainParamsPB_of_chainFromPb
   validChainParamsPB_of_chainFromVN validChainParamsPB_of_chainFrom_pq
   validChainParamsPB_trimSize_le validEncPbPtsAt_mono validEncPbPtsAt_of_encPtsBoundedAt
   validEncoderPtsAt_mono validEncoderPts_of_validEncoderPts640
   validEncoderPts_of_validEncoderPtsAt validOptEncPbPtsAt_mono validPqPtsAt_mono
   validV1PtsAt_mono validV1PtsAt_states_into_pb)
export LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux
  (ValidChainParams ValidChainParamsPB ValidEncoderPts640 ValidEncoderPtsAt spqrEncTightPtsCap)

/-! ## `ValidStatePtsAt K` and `ReachablePqxdhSession` Point-Slice Preservation -/

/-- Serialized SPQR state that is either empty (`V0`) or the canonical encoding of a `ValidPqPtsAt K` state.
-/
def ValidStatePtsAt (K : Nat) (s : Bytes) : Prop :=
  s = [] ∨ ∃ st : PqRatchetState, s = encodeState st ∧ ValidPqPtsAt K st

private theorem validStatePtsAt_exists_encodeState {K : Nat} {s : Bytes} (h : ValidStatePtsAt K s) :
    ∃ st : PqRatchetState, s = encodeState st ∧ ValidPqPtsAt K st := by
  rcases h with rfl | h
  · exact ⟨default, rfl, trivial⟩
  · exact h

theorem validEncoderPtsAt_of_validStatePtsAt {K : Nat} {s : Bytes} (hlen : s.length < 2 ^ 64)
    (h : ValidStatePtsAt K s) : ValidEncoderPtsAt K s := by
  obtain ⟨st, rfl, hpq⟩ := validStatePtsAt_exists_encodeState h
  unfold ValidEncoderPtsAt
  rw [spqrDecodeState_encodeState st hlen]
  exact hpq

private theorem validV1PtsAt_initInner {F : ShaCompress} {mlk : MlKem} {K : Nat}
    {v : Version} {dir : Direction} {authKey : Bytes} {inner? : Option V1State}
    (h : initInner (spqrDeps F mlk) v dir authKey = .ok inner?) :
    ∀ v1, inner? = some v1 → ValidV1PtsAt K v1 := by
  unfold initInner at h
  cases v with
  | v0 =>
    dsimp only at h
    have hinj := Except.ok.inj h; subst hinj
    intro _ h0; nomatch h0
  | v1 =>
    dsimp only [Functor.map, Except.map] at h
    split at h <;> try contradiction
    rename_i v1pb hv1
    have hinj := Except.ok.inj h; subst hinj
    intro v1 hv1_eq; cases hv1_eq
    unfold spqrDeps at hv1; dsimp only at hv1
    cases dir with
    | a2b =>
      cases ha : States.init_a spqrPolyApi (spqrAuthApi F) authKey <;> rw [ha] at hv1
      · contradiction
      · have hinj2 := Except.ok.inj hv1; subst hinj2
        unfold States.init_a CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysUnsampled.new
          CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.KeysUnsampled.new spqrAuthApi at ha
        dsimp only [Bind.bind, Except.bind] at ha
        have hst := Except.ok.inj ha; subst hst; trivial
    | b2a =>
      cases hb : States.init_b spqrPolyApi (spqrAuthApi F) authKey <;> rw [hb] at hv1
      · contradiction
      · have hinj2 := Except.ok.inj hv1; subst hinj2
        unfold States.init_b at hb
        rcases except_bind_eq_ok hb with ⟨_, _, hst⟩
        have hst_eq := Except.ok.inj hst; subst hst_eq; trivial

theorem validStatePtsAt_spqrV1Init (K : Nat) (F : ShaCompress) (mlk : MlKem)
    (dir : SpqrDirection) (k : BitVec 256) :
    ValidStatePtsAt K (spqrV1Init F mlk dir k) ∧ (spqrV1Init F mlk dir k).length < 2 ^ 32 := by
  unfold spqrV1Init spqrV1InitialStateFor
  split
  · rename_i st hst
    simp only [initialState, libsignalSpqrParams] at hst
    rcases hi : initInner (spqrDeps F mlk) Version.v1
        (Direction.ofSpqrDirection dir) (keyToBytes32 k) with _ | inner
    · rw [hi] at hst; cases hst
    · rw [hi] at hst
      have hst' := Except.ok.inj hst; subst hst'
      have hin := initInner_spqrDeps_raw_le hi
      have hv_in := validV1PtsAt_initInner (K := K) hi
      have hk : (keyToBytes32 k).length = 32 := by simp [keyToBytes32]
      have hpq : ValidPqPtsAt K (pbToPqRatchetState {
          inner := inner,
          versionNegotiation := some {
            direction := (Direction.ofSpqrDirection dir).toI32,
            minVersion := Version.v1.toI32,
            authKey := keyToBytes32 k,
            chainParams := some (libsignalChainParams false).intoPb },
          chain := none }) := by
        unfold ValidPqPtsAt pbToPqRatchetState
        cases inner with
        | none => trivial
        | some v1 => exact hv_in v1 rfl
      refine ⟨Or.inr ⟨_, rfl, hpq⟩, ?_⟩
      have hle := encodeState_length_le_rawPqState (pbToPqRatchetState {
          inner := inner,
          versionNegotiation := some {
            direction := (Direction.ofSpqrDirection dir).toI32,
            minVersion := Version.v1.toI32,
            authKey := keyToBytes32 k,
            chainParams := some (libsignalChainParams false).intoPb },
          chain := none })
      have hraw : rawPqState (pbToPqRatchetState {
          inner := inner,
          versionNegotiation := some {
            direction := (Direction.ofSpqrDirection dir).toI32,
            minVersion := Version.v1.toI32,
            authKey := keyToBytes32 k,
            chainParams := some (libsignalChainParams false).intoPb },
          chain := none }) ≤ 456 := by
        simp only [rawPqState, pbToPqRatchetState, optRaw_some, optRaw_none, rawVN, hk]
        omega
      dsimp only [spqrDeps]
      omega
  · exact ⟨Or.inl rfl, by decide⟩

theorem validEncoderPtsAt_spqrV1Init (K : Nat) (F : ShaCompress) (mlk : MlKem)
    (dir : SpqrDirection) (k : BitVec 256) :
    ValidEncoderPtsAt K (spqrV1Init F mlk dir k) := by
  obtain ⟨hv, h32⟩ := validStatePtsAt_spqrV1Init K F mlk dir k
  exact validEncoderPtsAt_of_validStatePtsAt (Nat.lt_trans h32 (by decide)) hv

private theorem if_error_eq_ok_l {ε α : Type} {c : Prop} [Decidable c] {e : ε}
    {rest : Except ε α} {v : α}
    (h : (if c then Except.error e else rest) = .ok v) : rest = .ok v := by
  by_cases hc : c <;> simp [hc] at h; exact h

private theorem if_eq_ok_cases_l {ε α : Type} {c : Prop} [Decidable c]
    {t f : Except ε α} {v : α}
    (h : (if c then t else f) = .ok v) : t = .ok v ∨ f = .ok v := by
  by_cases hc : c <;> simp [hc] at h <;> [exact Or.inl h; exact Or.inr h]

private theorem pure_bind_except_l {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Pure.pure x >>= f) = f x := rfl

private theorem if_pure_bind_eq_ok_l {ε α β : Type} {c : Prop} [Decidable c]
    {a : α} {Kfn : α → Except ε β} {f : Except ε β} {v : β}
    (h : (if c then (Pure.pure a >>= Kfn) else f) = .ok v) (P : α → Prop) (ha : P a)
    (hf : f = .ok v → ∃ a', P a' ∧ Kfn a' = .ok v) : ∃ a', P a' ∧ Kfn a' = .ok v := by
  rcases if_eq_ok_cases_l h with h1 | h1
  · rw [pure_bind_except_l] at h1; exact ⟨a, ha, h1⟩
  · exact hf h1

theorem validStatePtsAt_spqrV1_send {K : Nat} (hK : 576 ≤ K) (F : ShaCompress) (mlk : MlKem)
    (s tape s' : Bytes) (salt : Salt) (msg : Bytes)
    (hval : ValidStatePtsAt K s) (hlen : s.length < 2 ^ 64)
    (h : (spqrV1 F mlk).send s tape = some (s', salt, msg)) :
    ValidStatePtsAt K s' := by
  obtain ⟨st, rfl, hst_pts⟩ := validStatePtsAt_exists_encodeState hval
  rw [spqrV1_eq] at h; unfold toSpqrModel at h; dsimp only at h
  cases hsend : (send (spqrDeps F mlk) (spqrHkdfWith F) (encodeState st) tape).1 with
  | error _ => rw [hsend] at h; contradiction
  | ok out =>
    rw [hsend] at h; dsimp only at h
    cases hsalt : messageKeyToSalt? out.key with
    | none => rw [hsalt] at h; contradiction
    | some _ =>
      rw [hsalt] at h; dsimp only at h
      have hs'_eq := (Prod.mk.inj (Option.some.inj h)).1; subst hs'_eq
      have hdec := decodeState_spqrDeps_encodeState_pb F mlk st hlen
      unfold send at hsend; rw [hdec] at hsend; dsimp only at hsend
      cases hinner : (pqRatchetStateToPb st).inner with
      | none =>
        rw [hinner] at hsend; have hinj := Except.ok.inj hsend; subst hinj
        exact Or.inl rfl
      | some pb =>
        have hpb_pts : ValidV1PtsAt K pb := by
          unfold ValidPqPtsAt at hst_pts
          cases hin : st.inner with
          | none => simp [pqRatchetStateToPb, hin] at hinner
          | some i =>
            cases i with
            | v1 v =>
              simp only [pqRatchetStateToPb, hin, Option.map, Option.some.injEq] at hinner
              subst hinner; rw [hin] at hst_pts; exact hst_pts
        rw [hinner] at hsend; dsimp only at hsend
        cases hfrom : (spqrDeps F mlk).statesFromPb pb with
        | error _ => rw [hfrom] at hsend; contradiction
        | ok st0' =>
          rw [hfrom] at hsend; dsimp only at hsend
          unfold spqrDeps liftStatesResult at hfrom; dsimp only at hfrom
          cases hs0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb with
          | error e => rw [hs0] at hfrom; cases e <;> contradiction
          | ok st0 =>
            rw [hs0] at hfrom; have hst0 := Except.ok.inj hfrom; subst hst0
            have hst0_pts := statesPtsBoundedAt_of_from_pb hpb_pts hs0
            cases hsend_st : ((spqrDeps F mlk).statesSend st0 tape).1 with
            | error _ => rw [hsend_st] at hsend; contradiction
            | ok val =>
              rcases val with ⟨mOut, kOut, st1⟩
              rw [hsend_st] at hsend; dsimp only at hsend
              unfold spqrDeps at hsend_st; dsimp only at hsend_st
              cases hsend0 : st0.send mlk tape with
              | error se => rw [hsend0] at hsend_st; cases se <;> contradiction
              | ok p =>
                rcases p with ⟨sOut, _⟩
                rw [hsend0] at hsend_st
                have hst1 := (Prod.mk.inj (Prod.mk.inj (Except.ok.inj hsend_st)).2).2
                subst hst1
                have hsOut_pts := validV1PtsAt_states_into_pb
                  (statesPtsBoundedAt_of_send hK hst0_pts hsend0)
                rcases sendAfterStates_raw_le hsend with ⟨chainPb, _, hout_eq⟩
                exact Or.inr ⟨_, hout_eq, hsOut_pts⟩

theorem validStatePtsAt_spqrV1_recv {K : Nat} (hK : 576 ≤ K) (F : ShaCompress) (mlk : MlKem)
    (s msg s' : Bytes) (salt : Salt)
    (hval : ValidStatePtsAt K s) (hlen : s.length < 2 ^ 64)
    (h : (spqrV1 F mlk).recv s msg = .ok (s', salt)) :
    ValidStatePtsAt K s' := by
  obtain ⟨st, rfl, hst_pts⟩ := validStatePtsAt_exists_encodeState hval
  rw [spqrV1_eq] at h; unfold toSpqrModel at h; dsimp only at h
  cases hrecv : recv (spqrDeps F mlk) (spqrHkdfWith F) (encodeState st) msg with
  | error e => rw [hrecv] at h; cases e <;> contradiction
  | ok out =>
    rw [hrecv] at h; dsimp only at h
    cases hsalt : recvKeyToSalt? out.key with
    | none => rw [hsalt] at h; contradiction
    | some _ =>
      rw [hsalt] at h; dsimp only at h
      have hs'_eq := (Prod.mk.inj (Except.ok.inj h)).1; subst hs'_eq
      have hdec_eq := decodeState_spqrDeps_encodeState_pb F mlk st hlen
      unfold recv at hrecv; dsimp only at hrecv
      rcases except_bind_eq_ok hrecv with ⟨pmsg, _, h1⟩
      rcases except_bind_eq_ok h1 with ⟨prePb, hdec, h2⟩
      rw [SpqrApiResult.ofError_eq_ok, hdec_eq] at hdec
      have hpre := Except.ok.inj hdec; subst hpre
      replace h2 := if_error_eq_ok_l (if_error_eq_ok_l h2)
      rcases if_eq_ok_cases_l h2 with h2 | h2
      · have hinj := Except.ok.inj h2; subst hinj; exact Or.inl rfl
      · rcases if_eq_ok_cases_l h2 with h2 | h2
        · rcases except_bind_eq_ok h2 with ⟨chain0, _, h3⟩
          rcases except_bind_eq_ok h3 with ⟨⟨chain1, _⟩, _, h4⟩
          dsimp only at h4; have hinj := Except.ok.inj h4; subst hinj
          refine Or.inr ⟨_, rfl, ?_⟩
          unfold ValidPqPtsAt pbToPqRatchetState pqRatchetStateToPb
          unfold ValidPqPtsAt at hst_pts
          cases hin : st.inner with
          | none => trivial
          | some i => cases i; rw [hin] at hst_pts; exact hst_pts
        · have hpre_pts : ∀ pb, (pqRatchetStateToPb st).inner = some pb → ValidV1PtsAt K pb := by
            intro pb hpb
            unfold ValidPqPtsAt at hst_pts
            cases hin : st.inner with
            | none => simp [pqRatchetStateToPb, hin] at hpb
            | some i =>
              cases i with
              | v1 v =>
                simp only [pqRatchetStateToPb, hin, Option.map, Option.some.injEq] at hpb
                subst hpb; rw [hin] at hst_pts; exact hst_pts
          rcases if_pure_bind_eq_ok_l h2
            (fun statePb => ∀ pb, statePb.inner = some pb → ValidV1PtsAt K pb)
            hpre_pts
            (by
              intro h2
              rcases if_eq_ok_cases_l h2 with h2 | h2
              · dsimp only [Bind.bind, Except.bind] at h2; contradiction
              · cases hvn : (pqRatchetStateToPb st).versionNegotiation with
                | none => rw [hvn] at h2; dsimp only [Bind.bind, Except.bind] at h2; contradiction
                | some vn =>
                  rw [hvn] at h2; dsimp only at h2; rw [pure_bind_except_l] at h2
                  cases hv : Version.fromU8? pmsg.version with
                  | none => rw [hv] at h2; dsimp only [Bind.bind, Except.bind] at h2; contradiction
                  | some v =>
                    rw [hv] at h2; dsimp only at h2; rw [pure_bind_except_l] at h2
                    cases hd : Direction.fromI32? vn.direction with
                    | none => rw [hd] at h2; dsimp only [Bind.bind, Except.bind] at h2; contradiction
                    | some dir =>
                      rw [hd] at h2; dsimp only at h2; rw [pure_bind_except_l] at h2
                      rcases except_bind_eq_ok h2 with ⟨inner', hinit, hlt4⟩
                      rcases except_bind_eq_ok hlt4 with ⟨chain', _, hlt5⟩
                      rw [SpqrApiResult.ofPanic_eq_ok] at hinit
                      rw [pure_bind_except_l] at hlt5
                      exact ⟨{ inner := inner', versionNegotiation := none, chain := some chain'.intoPb },
                        validV1PtsAt_initInner (K := K) hinit, hlt5⟩)
            with ⟨statePb, hstPb_pts, h3⟩
          cases hinner : statePb.inner with
          | none =>
            rw [hinner] at h3; have hinj := Except.ok.inj h3; subst hinj; exact Or.inl rfl
          | some pb =>
            rw [hinner] at h3; dsimp only at h3
            rcases except_bind_eq_ok h3 with ⟨sckaMsg, _, h4⟩
            rcases except_bind_eq_ok h4 with ⟨st0', hfrom, h5⟩
            rcases except_bind_eq_ok h5 with ⟨⟨key, st1⟩, hrecv_st, h6⟩
            unfold spqrDeps liftStatesResult at hfrom; dsimp only at hfrom
            cases hs0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb with
            | error se => rw [hs0] at hfrom; cases se <;> contradiction
            | ok st0 =>
              rw [hs0] at hfrom; have hst0 := Except.ok.inj hfrom; subst hst0
              have hst0_pts := statesPtsBoundedAt_of_from_pb (hstPb_pts pb hinner) hs0
              unfold spqrDeps at hrecv_st; dsimp only at hrecv_st
              cases hr0 : st0.recv mlk sckaMsg with
              | error se => rw [hr0] at hrecv_st; cases se <;> contradiction
              | ok rOut =>
                rw [hr0] at hrecv_st
                have hst1 := (Prod.mk.inj (Except.ok.inj hrecv_st)).2; subst hst1
                have hrOut_pts := validV1PtsAt_states_into_pb
                  (statesPtsBoundedAt_of_recv hK hst0_pts hr0)
                dsimp only at h6; split at h6 <;> [contradiction; skip]
                rcases except_bind_eq_ok h6 with ⟨chain0, _, h7⟩
                have htail : ∀ (chain1 : Chain),
                    (do
                      let (chain2, msgKey) ← SpqrApiResult.ofChainResult
                        (chain1.recvKey (spqrHkdfWith F) (pmsg.epoch - 1#64) pmsg.index)
                      Except.ok ({
                        state := (spqrDeps F mlk).encodeState {
                          inner := some ((spqrDeps F mlk).statesIntoPb rOut.state),
                          versionNegotiation := none, chain := some chain2.intoPb },
                        key := if msgKey.isEmpty then none else some msgKey } : Recv)) = .ok out →
                    ValidStatePtsAt K out.state := by
                  intro chain1 h8
                  rcases except_bind_eq_ok h8 with ⟨⟨chain2, msgKey⟩, _, h9⟩
                  have hinj := Except.ok.inj h9; subst hinj
                  exact Or.inr ⟨_, rfl, hrOut_pts⟩
                cases key with
                | none =>
                  dsimp only at h7; rw [pure_bind_except_l] at h7
                  exact htail chain0 h7
                | some es =>
                  dsimp only at h7
                  rcases except_bind_eq_ok h7 with ⟨chain1, _, h8⟩
                  exact htail chain1 h8

theorem validStatePtsAt_of_reachPq {K : Nat} (hK : 576 ≤ K)
    {W : PEParams} {me : LocalIdentity} {x : RecordExtras}
    {g : GhostState Bytes} (h : ReachablePqxdhSession W me x g) :
    ValidStatePtsAt K g.session.pqRatchetState ∧ g.session.pqRatchetState.length < 2 ^ 64 := by
  induction h with
  | initiate X P me b t x g hi =>
    change initiateStateV1 X W W.Q.K P me b t = some (x, g) at hi
    unfold initiateStateV1 at hi
    rcases hinit : SignalPqxdh.Model.initiateKeys (modelPrims X W) (initiateInput W me b t) with
      _ | ⟨dk, hdr⟩
    · simp [hinit] at hi
    · rw [hinit] at hi; dsimp only at hi
      unfold initializeInitiatorSession at hi
      dsimp only [bind, Except.bind, pure, Except.pure] at hi
      rcases hrc : rootCreateChain W.C (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.rootKey)) ⟨b.spkPub⟩
          (KeyPair.generate W.C
            (CryptoGames.HKDF.bytesToKey32 ((t.toList.drop 160).take 32))).privateKey with
        _ | ⟨_, _⟩
      · simp [hrc] at hi
      · rw [hrc] at hi
        simp only [Option.some.injEq, Prod.mk.injEq] at hi
        rcases hi with ⟨rfl, rfl⟩
        obtain ⟨hv, h32⟩ := validStatePtsAt_spqrV1Init K W.C.F W.Q.K .a2b _
        exact ⟨hv, Nat.lt_trans h32 (by decide)⟩
  | recvPrekey X P me k m rc x g pt hr =>
    change recvPrekeyStateV1 X W W.Q.K P me k m rc = some (some (x, g, pt)) at hr
    unfold recvPrekeyStateV1 at hr
    rcases htf : SignalMessage.tryFrom protoSignalCodec m.inner with _ | inner
    · simp [htf] at hr
    · rw [htf] at hr; dsimp only at hr
      split_ifs at hr with hids
      · simp at hr
      · rcases hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W me k m) with
          _ | dk
        · simp [hacc] at hr
        · rw [hacc] at hr; dsimp only at hr
          let st0 : SessionState Bytes :=
            initializeRecipientSession (spqrV1SessionUniformCoins W.C.F W.Q.K)
              ⟨(keyPairOf W.C me.idPriv).publicKey⟩ ⟨⟨m.idPub⟩⟩ (keyPairOf W.C k.spkPriv)
              (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.rootKey))
              (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.chainKey))
              (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.pqrKey))
          have hseeds0 : SeedsLen32 st0 := by
            simp [st0, initializeRecipientSession, SessionState.new, SessionState.setSenderChain,
              SeedsLen32]
          have hlen0 : st0.receiverChains.length ≤ maxReceiverChains := by
            simp [st0, initializeRecipientSession, SessionState.new, SessionState.setSenderChain]
          obtain ⟨hval0, h32_0⟩ := validStatePtsAt_spqrV1Init K W.C.F W.Q.K .b2a
            (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.pqrKey))
          change (match SessionState.tryDecryptFromRecord W.C (spqrV1SessionUniformCoins W.C.F W.Q.K)
              ((paramsPV1 W.C W.Q.K).expectedAddrs P) inner .preKey rc st0 with
            | (.ok pt, st) => some (some (responderRecordExtras me m, ⟨P, st, 1, [1]⟩, pt))
            | (.error .panic, _) => none
            | (.error _, _) => some none) = some (some (x, g, pt)) at hr
          rcases hdec : SessionState.tryDecryptFromRecord W.C (spqrV1SessionUniformCoins W.C.F W.Q.K)
              ((paramsPV1 W.C W.Q.K).expectedAddrs P) inner .preKey rc st0 with ⟨e | pt', st⟩
          · rw [hdec] at hr; cases e <;> simp at hr
          · rw [hdec] at hr
            simp only [Option.some.injEq, Prod.mk.injEq] at hr
            rcases hr with ⟨rfl, rfl, rfl⟩
            obtain ⟨-, -, -, -, key, hrecv⟩ :=
              tryDecryptFromRecord_ok_props_gen W.C (spqrV1SessionUniformCoins W.C.F W.Q.K)
                ((paramsPV1 W.C W.Q.K).expectedAddrs P) inner .preKey rc st0 st pt'
                hseeds0 hlen0 hdec
            exact ⟨validStatePtsAt_spqrV1_recv hK W.C.F W.Q.K _ _ _ key hval0
                (Nat.lt_trans h32_0 (by decide)) hrecv,
              (encodeState_len_lt_recv W.C.F W.Q.K _ _ _ key h32_0 hrecv).2.2.2⟩
  | @send _ x_s g_s m r hr hlen ih =>
    have h32 : g_s.session.pqRatchetState.length < 2 ^ 32 := by
      have hle := pqRatchetState_length_le_encodeRecordX (fun _ => x_s) g_s
      omega
    rw [send_eq_afterSend]
    rcases hm : SessionState.messageEncrypt (pqxdhSessionParams W).C (pqxdhSessionParams W).codec
        (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session with
      ⟨_ | msg, s⟩
    · exact ih
    · obtain ⟨hseeds, hlen', -⟩ := reachPq_inv hr
      obtain ⟨-, -, -, -, key, pm, hsend, -⟩ :=
        messageEncrypt_ok_props_gen (pqxdhSessionParams W).C (pqxdhSessionParams W).codec
          (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session s msg
          hseeds hlen' hm
      exact ⟨validStatePtsAt_spqrV1_send hK W.C.F W.Q.K _ _ _ key pm ih.1 ih.2 hsend,
        (encodeState_len_lt_send W.C.F W.Q.K _ _ _ key pm h32 hsend).2.2.2⟩
  | @recv _ x_r g_r g'_r c rc res hr hlen hrec ih =>
    have h32 : g_r.session.pqRatchetState.length < 2 ^ 32 := by
      have hle := pqRatchetState_length_le_encodeRecordX (fun _ => x_r) g_r
      omega
    rcases res with ⟨_, _, pt⟩
    rw [receive_eq_afterRecv] at hrec
    rcases htf : SignalMessage.tryFrom (pqxdhSessionParams W).codec c with _ | msg
    · simp [htf] at hrec
    · rw [htf] at hrec; dsimp only at hrec
      rcases hd : SessionState.tryDecryptFromRecord (pqxdhSessionParams W).C
          (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).expectedAddrs g_r.party)
          msg .whisper rc g_r.session with ⟨_ | pt', s⟩
      · simp [hd] at hrec
      · rw [hd] at hrec
        simp only [Option.some.injEq] at hrec
        rcases hrec with ⟨rfl, rfl, rfl, rfl⟩
        obtain ⟨hseeds, hlen', -⟩ := reachPq_inv hr
        obtain ⟨-, -, -, -, key, hrecv⟩ :=
          tryDecryptFromRecord_ok_props_gen (pqxdhSessionParams W).C
            (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).expectedAddrs g_r.party)
            msg .whisper rc g_r.session s pt hseeds hlen' hd
        exact ⟨validStatePtsAt_spqrV1_recv hK W.C.F W.Q.K _ _ _ key ih.1 ih.2 hrecv,
          (encodeState_len_lt_recv W.C.F W.Q.K _ _ _ key h32 hrecv).2.2.2⟩

theorem validEncoderPtsAt_of_reachPq {K : Nat} (hK : 576 ≤ K)
    {W : PEParams} {me : LocalIdentity} {x : RecordExtras}
    {g : GhostState Bytes} (h : ReachablePqxdhSession W me x g) :
    ValidEncoderPtsAt K g.session.pqRatchetState := by
  obtain ⟨hv, hlen⟩ := validStatePtsAt_of_reachPq hK h
  exact validEncoderPtsAt_of_validStatePtsAt hlen hv

theorem validEncoderPts640_of_reachPq {W : PEParams} {me : LocalIdentity} {x : RecordExtras}
    {g : GhostState Bytes} (h : ReachablePqxdhSession W me x g) :
    ValidEncoderPts640 g.session.pqRatchetState :=
  validEncoderPtsAt_of_reachPq (by decide) h

/-! ## `ValidStateChainParams` and `ReachablePqxdhSession` `ChainParamsPB` Preservation -/

theorem validChainParamsPB_libsignal_false :
    ValidChainParamsPB (libsignalChainParams false).intoPb := by
  unfold ValidChainParamsPB
  decide

/-- Serialized SPQR state that is either empty (`V0`) or the canonical encoding of a `ValidPqChainParams` state.
-/
def ValidStateChainParams (s : Bytes) : Prop :=
  s = [] ∨ ∃ st : PqRatchetState, s = encodeState st ∧ ValidPqChainParams st

private theorem validStateChainParams_exists_encodeState {s : Bytes} (h : ValidStateChainParams s) :
    ∃ st : PqRatchetState, s = encodeState st ∧ ValidPqChainParams st := by
  rcases h with rfl | h
  · refine ⟨default, rfl, ?_, ?_⟩
    · intro _ hc; dsimp [default] at hc; nomatch hc
    · intro _ hvn; dsimp [default] at hvn; nomatch hvn
  · exact h

theorem validChainParams_of_validStateChainParams {s : Bytes} (hlen : s.length < 2 ^ 64)
    (h : ValidStateChainParams s) : ValidChainParams s := by
  obtain ⟨st, rfl, hpq⟩ := validStateChainParams_exists_encodeState h
  unfold ValidChainParams
  rw [spqrDecodeState_encodeState st hlen]
  exact hpq

theorem validStateChainParams_spqrV1Init (F : ShaCompress) (mlk : MlKem)
    (dir : SpqrDirection) (k : BitVec 256) :
    ValidStateChainParams (spqrV1Init F mlk dir k) := by
  unfold spqrV1Init spqrV1InitialStateFor
  split
  · rename_i st hst
    simp only [initialState, libsignalSpqrParams] at hst
    rcases hi : initInner (spqrDeps F mlk) Version.v1
        (Direction.ofSpqrDirection dir) (keyToBytes32 k) with _ | inner
    · rw [hi] at hst; cases hst
    · rw [hi] at hst
      have hst' := Except.ok.inj hst; subst hst'
      refine Or.inr ⟨_, rfl, ⟨?_, ?_⟩⟩
      · intro _ hc; dsimp [pbToPqRatchetState] at hc; nomatch hc
      · intro vn hvn
        dsimp [pbToPqRatchetState] at hvn
        cases hvn
        intro p hp
        cases hp
        exact validChainParamsPB_libsignal_false
  · exact Or.inl rfl

theorem validChainParams_spqrV1Init (F : ShaCompress) (mlk : MlKem)
    (dir : SpqrDirection) (k : BitVec 256) :
    ValidChainParams (spqrV1Init F mlk dir k) := by
  obtain ⟨_, h32⟩ := validStatePtsAt_spqrV1Init 640 F mlk dir k
  exact validChainParams_of_validStateChainParams (Nat.lt_trans h32 (by decide))
    (validStateChainParams_spqrV1Init F mlk dir k)

private theorem validChainParams_of_sendAfterStates {F : ShaCompress} {mlk : MlKem}
    {statePb : PqRatchetStatePB V1State}
    {msg : (spqrDeps F mlk).MessageV1} {key : Option EpochSecret}
    {state : (spqrDeps F mlk).States} {out : Send}
    (hchain : ∀ c, statePb.chain = some c → ValidChainPBParams c)
    (hvn : ∀ vn, statePb.versionNegotiation = some vn → ValidVNParams vn)
    (h : sendAfterStates (spqrDeps F mlk) (spqrHkdfWith F) statePb msg key state = .ok out) :
    ValidStateChainParams out.state := by
  unfold sendAfterStates at h
  simp only [pure_bind_except_l] at h
  have hchain? : ∃ chain? : Option Chain,
      (∀ c0, chain? = some c0 → ValidChainParamsPB c0.params) ∧
      ((do
        let (index, msgKey, chainPb) ← match chain? with
          | none =>
            if key.isNone then pure (0#32, ([] : Bytes), (none : Option ChainPB))
            else Except.error (SpqrApiError.panic SpqrApiPanic.sendKeySomeWithoutChain)
          | some chain0 => do
            let chain1 ← match key with
              | some epochSecret => SpqrApiResult.ofChainPanic (chain0.addEpoch (spqrHkdfWith F) epochSecret)
              | none => pure chain0
            let epoch := (spqrDeps F mlk).msgEpoch msg
            if epoch == 0#64 then Except.error (SpqrApiError.panic SpqrApiPanic.sendEpochUnderflow)
            else do
              let (chain2, (idx, mk)) ←
                SpqrApiResult.ofChainResult (chain1.sendKey (spqrHkdfWith F) (epoch - 1#64))
              pure (idx, mk, some chain2.intoPb)
        let msgBytes := (spqrDeps F mlk).msgSerialize msg index
        match msgBytes with
        | [] => Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgEmpty)
        | b0 :: _ =>
          if b0 != Version.v1.toU8 then Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgBadVersion)
          else
            let newStateBytes := (spqrDeps F mlk).encodeState {
              inner := some ((spqrDeps F mlk).statesIntoPb state),
              versionNegotiation := statePb.versionNegotiation, chain := chainPb }
            let outKey : MessageKey := if msgKey.isEmpty then none else some msgKey
            Except.ok ({ state := newStateBytes, msg := msgBytes, key := outKey } : Send)) :
        SpqrApiResult Send) = .ok out := by
    cases hch_opt : statePb.chain with
    | none =>
      rw [hch_opt] at h; dsimp only [] at h
      cases hsvn : statePb.versionNegotiation with
      | none => rw [hsvn] at h; contradiction
      | some vn =>
        rw [hsvn] at h; dsimp only [] at h; split at h
        · rcases except_bind_eq_ok h with ⟨c, hc, h1⟩
          rw [SpqrApiResult.ofError_eq_ok] at hc
          refine ⟨some c, ?_, h1⟩
          intro c0 hc0; cases hc0
          exact validChainParamsPB_of_chainFromVN (hvn vn hsvn) hc
        · refine ⟨none, ?_, h⟩; intro _ hc; nomatch hc
    | some pb =>
      rw [hch_opt] at h; dsimp only [] at h
      rcases except_bind_eq_ok h with ⟨c, hc, h1⟩
      rw [SpqrApiResult.ofError_eq_ok] at hc
      refine ⟨some c, ?_, h1⟩
      intro c0 hc0; cases hc0
      exact validChainParamsPB_of_chainFromPb (hchain pb hch_opt) hc
  rcases hchain? with ⟨chain?, hch_p, h1⟩
  simp only [pure_bind_except_l] at h1
  cases chain? with
  | none =>
    dsimp only [] at h1; split at h1
    · split at h1 <;> [contradiction; skip]; split at h1 <;> [contradiction; skip]
      have hinj := Except.ok.inj h1; subst hinj
      exact Or.inr ⟨_, rfl, ⟨fun _ hc => (by dsimp [pbToPqRatchetState] at hc; nomatch hc), hvn⟩⟩
    · dsimp only [Bind.bind, Except.bind] at h1; contradiction
  | some chain0 =>
    have hc0_p : ValidChainParamsPB chain0.params := hch_p chain0 rfl
    have htail : ∀ (chain1 : Chain),
        ValidChainParamsPB chain1.params →
        (if ((spqrDeps F mlk).msgEpoch msg == 0#64) = true then do
          let __x : BitVec 32 × Bytes × Option ChainPB ←
            Except.error (SpqrApiError.panic SpqrApiPanic.sendEpochUnderflow)
          match (spqrDeps F mlk).msgSerialize msg __x.1 with
          | [] => Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgEmpty)
          | b0 :: _ =>
            if (b0 != Version.v1.toU8) = true then
              Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgBadVersion)
            else Except.ok ({
              state := (spqrDeps F mlk).encodeState {
                inner := some ((spqrDeps F mlk).statesIntoPb state),
                versionNegotiation := statePb.versionNegotiation, chain := __x.2.2 },
              msg := (spqrDeps F mlk).msgSerialize msg __x.1,
              key := if __x.2.1.isEmpty = true then none else some __x.2.1 } : Send)
        else do
          let __x ← SpqrApiResult.ofChainResult
            (chain1.sendKey (spqrHkdfWith F) ((spqrDeps F mlk).msgEpoch msg - 1#64))
          match (spqrDeps F mlk).msgSerialize msg __x.2.1 with
          | [] => Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgEmpty)
          | b0 :: _ =>
            if (b0 != Version.v1.toU8) = true then
              Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgBadVersion)
            else Except.ok ({
              state := (spqrDeps F mlk).encodeState {
                inner := some ((spqrDeps F mlk).statesIntoPb state),
                versionNegotiation := statePb.versionNegotiation, chain := some __x.1.intoPb },
              msg := (spqrDeps F mlk).msgSerialize msg __x.2.1,
              key := if List.isEmpty __x.2.2 = true then none else some __x.2.2 } : Send)) = .ok out →
        ValidStateChainParams out.state := by
      intro chain1 hc1_p hstep2; split at hstep2
      · dsimp only [Bind.bind, Except.bind] at hstep2; contradiction
      · rcases except_bind_eq_ok hstep2 with ⟨⟨chain2, idx, mk⟩, hc2, h2⟩
        rw [SpqrApiResult.ofChainResult_eq_ok] at hc2
        have hc2_p : ValidChainParamsPB chain2.params := chainSendKey_params_eq hc2 ▸ hc1_p
        dsimp only [] at h2; split at h2 <;> [contradiction; skip]; split at h2 <;> [contradiction; skip]
        have hinj2 := Except.ok.inj h2; subst hinj2
        exact Or.inr ⟨_, rfl,
          ⟨fun c hc => by
            dsimp [pbToPqRatchetState] at hc
            cases hc
            exact validChainPBParams_intoPb hc2_p,
           hvn⟩⟩
    cases key with
    | none => exact htail chain0 hc0_p h1
    | some es =>
      dsimp only [] at h1; rcases except_bind_eq_ok h1 with ⟨chain1, hc1, hstep2⟩
      rw [SpqrApiResult.ofChainPanic_eq_ok] at hc1
      exact htail chain1 (chainAddEpoch_params_eq hc1 ▸ hc0_p) hstep2

theorem validStateChainParams_spqrV1_send (F : ShaCompress) (mlk : MlKem)
    (s tape s' : Bytes) (salt : Salt) (msg : Bytes)
    (hval : ValidStateChainParams s) (hlen : s.length < 2 ^ 64)
    (h : (spqrV1 F mlk).send s tape = some (s', salt, msg)) :
    ValidStateChainParams s' := by
  obtain ⟨st, rfl, hst_cp⟩ := validStateChainParams_exists_encodeState hval
  rw [spqrV1_eq] at h; unfold toSpqrModel at h; dsimp only at h
  cases hsend : (send (spqrDeps F mlk) (spqrHkdfWith F) (encodeState st) tape).1 with
  | error _ => rw [hsend] at h; contradiction
  | ok out =>
    rw [hsend] at h; dsimp only at h
    cases hsalt : messageKeyToSalt? out.key with
    | none => rw [hsalt] at h; contradiction
    | some _ =>
      rw [hsalt] at h; dsimp only at h
      have hs'_eq := (Prod.mk.inj (Option.some.inj h)).1; subst hs'_eq
      have hdec := decodeState_spqrDeps_encodeState_pb F mlk st hlen
      unfold send at hsend; rw [hdec] at hsend; dsimp only at hsend
      cases hinner : (pqRatchetStateToPb st).inner with
      | none =>
        rw [hinner] at hsend; have hinj := Except.ok.inj hsend; subst hinj
        exact Or.inl rfl
      | some pb =>
        rw [hinner] at hsend; dsimp only at hsend
        cases hfrom : (spqrDeps F mlk).statesFromPb pb with
        | error _ => rw [hfrom] at hsend; contradiction
        | ok st0 =>
          rw [hfrom] at hsend; dsimp only at hsend
          cases hsend_st : ((spqrDeps F mlk).statesSend st0 tape).1 with
          | error _ => rw [hsend_st] at hsend; contradiction
          | ok val =>
            rcases val with ⟨mOut, kOut, st1⟩
            rw [hsend_st] at hsend; dsimp only at hsend
            exact validChainParams_of_sendAfterStates hst_cp.1 hst_cp.2 hsend

theorem validStateChainParams_spqrV1_recv (F : ShaCompress) (mlk : MlKem)
    (s msg s' : Bytes) (salt : Salt)
    (hval : ValidStateChainParams s) (hlen : s.length < 2 ^ 64)
    (h : (spqrV1 F mlk).recv s msg = .ok (s', salt)) :
    ValidStateChainParams s' := by
  obtain ⟨st, rfl, hst_cp⟩ := validStateChainParams_exists_encodeState hval
  rw [spqrV1_eq] at h; unfold toSpqrModel at h; dsimp only at h
  cases hrecv : recv (spqrDeps F mlk) (spqrHkdfWith F) (encodeState st) msg with
  | error e => rw [hrecv] at h; cases e <;> contradiction
  | ok out =>
    rw [hrecv] at h; dsimp only at h
    cases hsalt : recvKeyToSalt? out.key with
    | none => rw [hsalt] at h; contradiction
    | some _ =>
      rw [hsalt] at h; dsimp only at h
      have hs'_eq := (Prod.mk.inj (Except.ok.inj h)).1; subst hs'_eq
      have hdec_eq := decodeState_spqrDeps_encodeState_pb F mlk st hlen
      unfold recv at hrecv; dsimp only at hrecv
      rcases except_bind_eq_ok hrecv with ⟨pmsg, _, h1⟩
      rcases except_bind_eq_ok h1 with ⟨prePb, hdec, h2⟩
      rw [SpqrApiResult.ofError_eq_ok, hdec_eq] at hdec
      have hpre := Except.ok.inj hdec; subst hpre
      replace h2 := if_error_eq_ok_l (if_error_eq_ok_l h2)
      rcases if_eq_ok_cases_l h2 with h2 | h2
      · have hinj := Except.ok.inj h2; subst hinj; exact Or.inl rfl
      · rcases if_eq_ok_cases_l h2 with h2 | h2
        · rcases except_bind_eq_ok h2 with ⟨chain0, hc0, h3⟩
          rcases except_bind_eq_ok h3 with ⟨⟨chain1, _⟩, hrk, h4⟩
          rw [SpqrApiResult.ofError_eq_ok] at hc0
          rw [SpqrApiResult.ofChainResult_eq_ok] at hrk
          dsimp only at h4; have hinj := Except.ok.inj h4; subst hinj
          have hc0_p := validChainParamsPB_of_chainFrom hst_cp.1 hst_cp.2 hc0
          have hc1_p := chainRecvKey_params_eq hrk ▸ hc0_p
          refine Or.inr ⟨_, rfl, ⟨?_, hst_cp.2⟩⟩
          intro c hc
          dsimp [pbToPqRatchetState] at hc
          cases hc
          exact validChainPBParams_intoPb hc1_p
        · have hpre_cp : (∀ c, (pqRatchetStateToPb st).chain = some c → ValidChainPBParams c) ∧
              (∀ vn, (pqRatchetStateToPb st).versionNegotiation = some vn → ValidVNParams vn) :=
            hst_cp
          rcases if_pure_bind_eq_ok_l h2
            (fun statePb => (∀ c, statePb.chain = some c → ValidChainPBParams c) ∧
              (∀ vn, statePb.versionNegotiation = some vn → ValidVNParams vn))
            hpre_cp
            (by
              intro h2
              rcases if_eq_ok_cases_l h2 with h2 | h2
              · dsimp only [Bind.bind, Except.bind] at h2; contradiction
              · cases hvn : (pqRatchetStateToPb st).versionNegotiation with
                | none => rw [hvn] at h2; dsimp only [Bind.bind, Except.bind] at h2; contradiction
                | some vn =>
                  rw [hvn] at h2; dsimp only at h2; rw [pure_bind_except_l] at h2
                  cases hv : Version.fromU8? pmsg.version with
                  | none => rw [hv] at h2; dsimp only [Bind.bind, Except.bind] at h2; contradiction
                  | some v =>
                    rw [hv] at h2; dsimp only at h2; rw [pure_bind_except_l] at h2
                    cases hd : Direction.fromI32? vn.direction with
                    | none => rw [hd] at h2; dsimp only [Bind.bind, Except.bind] at h2; contradiction
                    | some dir =>
                      rw [hd] at h2; dsimp only at h2; rw [pure_bind_except_l] at h2
                      rcases except_bind_eq_ok h2 with ⟨inner', _, hlt4⟩
                      rcases except_bind_eq_ok hlt4 with ⟨chain', hcvn, hlt5⟩
                      rw [SpqrApiResult.ofError_eq_ok] at hcvn
                      rw [pure_bind_except_l] at hlt5
                      have hcp' := validChainParamsPB_of_chainFrom hst_cp.1
                        (fun vn' hvn' => by cases hvn'; exact hst_cp.2 vn hvn) hcvn
                      exact ⟨{ inner := inner', versionNegotiation := none,
                               chain := some chain'.intoPb },
                        ⟨fun c hc => by cases hc; exact validChainPBParams_intoPb hcp',
                         fun _ hnone => nomatch hnone⟩, hlt5⟩)
            with ⟨statePb, hstPb_cp, h3⟩
          cases hinner : statePb.inner with
          | none =>
            rw [hinner] at h3; have hinj := Except.ok.inj h3; subst hinj; exact Or.inl rfl
          | some pb =>
            rw [hinner] at h3; dsimp only at h3
            rcases except_bind_eq_ok h3 with ⟨sckaMsg, _, h4⟩
            rcases except_bind_eq_ok h4 with ⟨st0', _, h5⟩
            rcases except_bind_eq_ok h5 with ⟨⟨key, st1⟩, _, h6⟩
            dsimp only at h6; split at h6 <;> [contradiction; skip]
            rcases except_bind_eq_ok h6 with ⟨chain0, hc0, h7⟩
            rw [SpqrApiResult.ofError_eq_ok] at hc0
            have hc0_p := validChainParamsPB_of_chainFrom hstPb_cp.1 hstPb_cp.2 hc0
            have htail : ∀ (chain1 : Chain), ValidChainParamsPB chain1.params →
                (do
                  let (chain2, msgKey) ← SpqrApiResult.ofChainResult
                    (chain1.recvKey (spqrHkdfWith F) (pmsg.epoch - 1#64) pmsg.index)
                  Except.ok ({
                    state := (spqrDeps F mlk).encodeState {
                      inner := some ((spqrDeps F mlk).statesIntoPb st1),
                      versionNegotiation := none, chain := some chain2.intoPb },
                    key := if msgKey.isEmpty then none else some msgKey } : Recv)) = .ok out →
                ValidStateChainParams out.state := by
              intro chain1 hc1_p h8
              rcases except_bind_eq_ok h8 with ⟨⟨chain2, msgKey⟩, hrk, h9⟩
              rw [SpqrApiResult.ofChainResult_eq_ok] at hrk
              have hinj := Except.ok.inj h9; subst hinj
              have hc2_p := chainRecvKey_params_eq hrk ▸ hc1_p
              exact Or.inr ⟨_, rfl,
                ⟨fun c hc => by
                  dsimp [pbToPqRatchetState] at hc
                  cases hc
                  exact validChainPBParams_intoPb hc2_p,
                 fun _ hnone => by
                  dsimp [pbToPqRatchetState] at hnone
                  nomatch hnone⟩⟩
            cases key with
            | none =>
              dsimp only at h7; rw [pure_bind_except_l] at h7
              exact htail chain0 hc0_p h7
            | some es =>
              dsimp only at h7
              rcases except_bind_eq_ok h7 with ⟨chain1, hadd, h8⟩
              rw [SpqrApiResult.ofChainPanic_eq_ok] at hadd
              exact htail chain1 (chainAddEpoch_params_eq hadd ▸ hc0_p) h8

theorem validStateChainParams_of_reachPq {W : PEParams} {me : LocalIdentity} {x : RecordExtras}
    {g : GhostState Bytes} (h : ReachablePqxdhSession W me x g) :
    ValidStateChainParams g.session.pqRatchetState ∧ g.session.pqRatchetState.length < 2 ^ 64 := by
  induction h with
  | initiate X P me b t x g hi =>
    change initiateStateV1 X W W.Q.K P me b t = some (x, g) at hi
    unfold initiateStateV1 at hi
    rcases hinit : SignalPqxdh.Model.initiateKeys (modelPrims X W) (initiateInput W me b t) with
      _ | ⟨dk, hdr⟩
    · simp [hinit] at hi
    · rw [hinit] at hi; dsimp only at hi
      unfold initializeInitiatorSession at hi
      dsimp only [bind, Except.bind, pure, Except.pure] at hi
      rcases hrc : rootCreateChain W.C (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.rootKey)) ⟨b.spkPub⟩
          (KeyPair.generate W.C
            (CryptoGames.HKDF.bytesToKey32 ((t.toList.drop 160).take 32))).privateKey with
        _ | ⟨_, _⟩
      · simp [hrc] at hi
      · rw [hrc] at hi
        simp only [Option.some.injEq, Prod.mk.injEq] at hi
        rcases hi with ⟨rfl, rfl⟩
        obtain ⟨_, h32⟩ := validStatePtsAt_spqrV1Init 640 W.C.F W.Q.K .a2b _
        exact ⟨validStateChainParams_spqrV1Init W.C.F W.Q.K .a2b _, Nat.lt_trans h32 (by decide)⟩
  | recvPrekey X P me k m rc x g pt hr =>
    change recvPrekeyStateV1 X W W.Q.K P me k m rc = some (some (x, g, pt)) at hr
    unfold recvPrekeyStateV1 at hr
    rcases htf : SignalMessage.tryFrom protoSignalCodec m.inner with _ | inner
    · simp [htf] at hr
    · rw [htf] at hr; dsimp only at hr
      split_ifs at hr with hids
      · simp at hr
      · rcases hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W me k m) with
          _ | dk
        · simp [hacc] at hr
        · rw [hacc] at hr; dsimp only at hr
          let st0 : SessionState Bytes :=
            initializeRecipientSession (spqrV1SessionUniformCoins W.C.F W.Q.K)
              ⟨(keyPairOf W.C me.idPriv).publicKey⟩ ⟨⟨m.idPub⟩⟩ (keyPairOf W.C k.spkPriv)
              (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.rootKey))
              (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.chainKey))
              (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.pqrKey))
          have hseeds0 : SeedsLen32 st0 := by
            simp [st0, initializeRecipientSession, SessionState.new, SessionState.setSenderChain,
              SeedsLen32]
          have hlen0 : st0.receiverChains.length ≤ maxReceiverChains := by
            simp [st0, initializeRecipientSession, SessionState.new, SessionState.setSenderChain]
          have hval0 := validStateChainParams_spqrV1Init W.C.F W.Q.K .b2a
            (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.pqrKey))
          obtain ⟨_, h32_0⟩ := validStatePtsAt_spqrV1Init 640 W.C.F W.Q.K .b2a
            (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.pqrKey))
          change (match SessionState.tryDecryptFromRecord W.C (spqrV1SessionUniformCoins W.C.F W.Q.K)
              ((paramsPV1 W.C W.Q.K).expectedAddrs P) inner .preKey rc st0 with
            | (.ok pt, st) => some (some (responderRecordExtras me m, ⟨P, st, 1, [1]⟩, pt))
            | (.error .panic, _) => none
            | (.error _, _) => some none) = some (some (x, g, pt)) at hr
          rcases hdec : SessionState.tryDecryptFromRecord W.C (spqrV1SessionUniformCoins W.C.F W.Q.K)
              ((paramsPV1 W.C W.Q.K).expectedAddrs P) inner .preKey rc st0 with ⟨e | pt', st⟩
          · rw [hdec] at hr; cases e <;> simp at hr
          · rw [hdec] at hr
            simp only [Option.some.injEq, Prod.mk.injEq] at hr
            rcases hr with ⟨rfl, rfl, rfl⟩
            obtain ⟨-, -, -, -, key, hrecv⟩ :=
              tryDecryptFromRecord_ok_props_gen W.C (spqrV1SessionUniformCoins W.C.F W.Q.K)
                ((paramsPV1 W.C W.Q.K).expectedAddrs P) inner .preKey rc st0 st pt'
                hseeds0 hlen0 hdec
            exact ⟨validStateChainParams_spqrV1_recv W.C.F W.Q.K _ _ _ key hval0
                (Nat.lt_trans h32_0 (by decide)) hrecv,
              (encodeState_len_lt_recv W.C.F W.Q.K _ _ _ key h32_0 hrecv).2.2.2⟩
  | @send _ x_s g_s m r hr hlen ih =>
    have h32 : g_s.session.pqRatchetState.length < 2 ^ 32 := by
      have hle := pqRatchetState_length_le_encodeRecordX (fun _ => x_s) g_s
      omega
    rw [send_eq_afterSend]
    rcases hm : SessionState.messageEncrypt (pqxdhSessionParams W).C (pqxdhSessionParams W).codec
        (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session with
      ⟨_ | msg, s⟩
    · exact ih
    · obtain ⟨hseeds, hlen', -⟩ := reachPq_inv hr
      obtain ⟨-, -, -, -, key, pm, hsend, -⟩ :=
        messageEncrypt_ok_props_gen (pqxdhSessionParams W).C (pqxdhSessionParams W).codec
          (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session s msg
          hseeds hlen' hm
      exact ⟨validStateChainParams_spqrV1_send W.C.F W.Q.K _ _ _ key pm ih.1 ih.2 hsend,
        (encodeState_len_lt_send W.C.F W.Q.K _ _ _ key pm h32 hsend).2.2.2⟩
  | @recv _ x_r g_r g'_r c rc res hr hlen hrec ih =>
    have h32 : g_r.session.pqRatchetState.length < 2 ^ 32 := by
      have hle := pqRatchetState_length_le_encodeRecordX (fun _ => x_r) g_r
      omega
    rcases res with ⟨_, _, pt⟩
    rw [receive_eq_afterRecv] at hrec
    rcases htf : SignalMessage.tryFrom (pqxdhSessionParams W).codec c with _ | msg
    · simp [htf] at hrec
    · rw [htf] at hrec; dsimp only at hrec
      rcases hd : SessionState.tryDecryptFromRecord (pqxdhSessionParams W).C
          (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).expectedAddrs g_r.party)
          msg .whisper rc g_r.session with ⟨_ | pt', s⟩
      · simp [hd] at hrec
      · rw [hd] at hrec
        simp only [Option.some.injEq] at hrec
        rcases hrec with ⟨rfl, rfl, rfl, rfl⟩
        obtain ⟨hseeds, hlen', -⟩ := reachPq_inv hr
        obtain ⟨-, -, -, -, key, hrecv⟩ :=
          tryDecryptFromRecord_ok_props_gen (pqxdhSessionParams W).C
            (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).expectedAddrs g_r.party)
            msg .whisper rc g_r.session s pt hseeds hlen' hd
        exact ⟨validStateChainParams_spqrV1_recv W.C.F W.Q.K _ _ _ key ih.1 ih.2 hrecv,
          (encodeState_len_lt_recv W.C.F W.Q.K _ _ _ key h32 hrecv).2.2.2⟩

theorem validChainParams_of_reachPq {W : PEParams} {me : LocalIdentity} {x : RecordExtras}
    {g : GhostState Bytes} (h : ReachablePqxdhSession W me x g) :
    ValidChainParams g.session.pqRatchetState := by
  obtain ⟨hv, hlen⟩ := validStateChainParams_of_reachPq h
  exact validChainParams_of_validStateChainParams hlen hv

/-! ## CLI Record and Peer Store Validity Bridges (`K = 640`) -/

/-- SPQR validity on a `SessionRecord` (`ValidEncoderPtsAt K`, `ValidChainParams`, and `< 2 ^ 31` byte length on every active session's `pqRatchetState`).
-/
def RecordSpqrTightValid (K : Nat) (r : SessionRecord (List (BitVec 8))) : Prop :=
  ∀ sess, r.currentSession = some sess →
    ValidEncoderPtsAt K sess.state.pqRatchetState ∧
    ValidChainParams sess.state.pqRatchetState ∧
    sess.state.pqRatchetState.length < 2 ^ 31

/-- SPQR validity on the session record stored for `rem` in `F` under `scopeKit`. -/
def PeerSpqrTightValidAt (K : Nat) (F : FsFiles) (rem : AddrVal) : Prop :=
  match loadRec scopeKit F rem with
  | .ok (some r) => RecordSpqrTightValid K r
  | _ => True

/-- `K = 640` specialization of `PeerSpqrTightValidAt`. -/
abbrev PeerSpqrTightValid640 (F : FsFiles) (rem : AddrVal) : Prop :=
  PeerSpqrTightValidAt 640 F rem

theorem peerSpqrTightValidAt_mono {K₁ K₂ : Nat} (hK : K₁ ≤ K₂) {F : FsFiles} {rem : AddrVal}
    (h : PeerSpqrTightValidAt K₁ F rem) : PeerSpqrTightValidAt K₂ F rem := by
  revert h
  unfold PeerSpqrTightValidAt RecordSpqrTightValid
  cases loadRec scopeKit F rem with
  | error _ => intro _; trivial
  | ok opt =>
    cases opt with
    | none => intro _; trivial
    | some r =>
      intro h sess hsess
      obtain ⟨h1, h2, h3⟩ := h sess hsess
      exact ⟨validEncoderPtsAt_mono hK h1, h2, h3⟩

theorem peerSpqrValid_of_peerSpqrTightValidAt {K : Nat} (hK : K ≤ 524288)
    {F : FsFiles} {rem : AddrVal} (h : PeerSpqrTightValidAt K F rem) :
    PeerSpqrValid F rem := by
  revert h
  unfold PeerSpqrTightValidAt RecordSpqrTightValid PeerSpqrValid
  cases loadRec scopeKit F rem with
  | error _ => intro _; trivial
  | ok opt =>
    cases opt with
    | none => intro _; trivial
    | some r =>
      intro h
      dsimp only
      cases hcur : r.currentSession with
      | none => trivial
      | some sess =>
        obtain ⟨h1, _, h3⟩ := h sess hcur
        exact ⟨validEncoderPts_of_validEncoderPtsAt hK h1, h3⟩

/-- Extracts `RecordSpqrTightValid K r` from `cliSessionStoreSpec.ScopeAt` and `PeerSpqrTightValidAt K F rem`.
-/
theorem recordSpqrTightValid_of_cliSessionStoreSpec {A : RustAlloc} {b : BitVec 64}
    {F : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {rem : AddrVal} {r : SessionRecord (List (BitVec 8))} {K : Nat}
    (hScAt : (cliSessionStoreSpec A b cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4).ScopeAt
      scopeKit StoresGhost.opened.sessions rem r)
    (hValid : PeerSpqrTightValidAt K F rem) :
    RecordSpqrTightValid K r := by
  obtain ⟨bs, hbs, hla⟩ := hScAt.2
  have hlr : loadRec scopeKit F rem = .ok (some r) := by
    symm
    exact loadRec_unique encodeInjOn_deserializeScopeP_Q (hbs ▸ hla)
  unfold PeerSpqrTightValidAt at hValid
  rw [hlr] at hValid
  exact hValid

theorem peerSpqrTightValidAt_of_cliSessionStoreSpec {A : RustAlloc} {b : BitVec 64}
    {F : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {rem : AddrVal} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otrPqr : List (BitVec 8)} {K : Nat}
    (hScAt : (cliSessionStoreSpec A b cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4).ScopeAt
      scopeKit StoresGhost.opened.sessions rem r)
    (hcur : r.currentSession = some sess)
    (hpqr : otrPqr = sess.state.pqRatchetState)
    (hValid : PeerSpqrTightValidAt K F rem) :
    ValidEncoderPtsAt K otrPqr ∧ ValidChainParams otrPqr ∧ otrPqr.length < 2 ^ 31 := by
  have hrec := recordSpqrTightValid_of_cliSessionStoreSpec hScAt hValid sess hcur
  simpa [hpqr] using hrec

theorem peerSpqrTightValidAt_of_w1ScopeAt {B : RunBudgets} {img : Arm64.Obj.Image}
    {F : FsFiles} {peer : AddrGhost} {rem : AddrVal}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otrPqr : List (BitVec 8)} {K : Nat}
    (hScAt : (w1SessKit B img F peer).ScopeAt scopeKit StoresGhost.opened.sessions rem r)
    (hcur : r.currentSession = some sess)
    (hpqr : otrPqr = sess.state.pqRatchetState)
    (hValid : PeerSpqrTightValidAt K F rem) :
    ValidEncoderPtsAt K otrPqr ∧ ValidChainParams otrPqr ∧ otrPqr.length < 2 ^ 31 :=
  peerSpqrTightValidAt_of_cliSessionStoreSpec hScAt hcur hpqr hValid

private theorem recordSpqrTightValid_of_wfSession {K : Nat} (hK : 576 ≤ K)
    {W : PEParams} {st : PqParty} (hwf : PqxdhPartyInSpecDomain W st)
    {x : RecordExtras} {g : GhostState Bytes} (hs : st.session = some (x, g)) :
    RecordSpqrTightValid K (toRecord (extrasOf fun _ => x) g) := by
  intro sess hsess
  simp only [toRecord_extrasOf_eq, Option.some.injEq] at hsess
  subst hsess
  dsimp only [sessionOfX]
  have hwf_sess := hwf.1 x g hs
  rcases hwf_sess.1 with ⟨g₀, hr, _, hsess₀⟩
  have hpq31 : g.session.pqRatchetState.length < 2 ^ 31 :=
    Nat.lt_of_le_of_lt (pqRatchetState_length_le_encodeRecordX (fun _ => x) g) hwf_sess.2.2
  have hve := validEncoderPtsAt_of_reachPq hK hr
  have hcp := validChainParams_of_reachPq hr
  rw [hsess₀] at hve hcp
  exact ⟨hve, hcp, hpq31⟩

/-- Every `CliPqxdhInputs W i` invocation parsing as `.send peer` satisfies `PeerSpqrTightValidAt K` for `576 ≤ K`.
-/
theorem peerSpqrTightValidAt_of_cliPqInputs_send {K : Nat} (hK : 576 ≤ K)
    {W : PEParams} {i : Inputs} {peer : AddrV}
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.send peer)) :
    PeerSpqrTightValidAt K (runFiles i) (addrValOf peer) := by
  obtain ⟨st, hwf, hcases⟩ := hi
  rcases hcases with ⟨_, b, t, rfl⟩ | ⟨m, r, _, rfl⟩ | ⟨c, rc, _, rfl⟩ | ⟨m, rc, _, rfl⟩ |
    ⟨c, rc, _, _, _, rfl⟩
  · have ha : (pqInitInputs W st b t).argv = (Cmd.init (partyAddress st.party.other) bundleDir).argv := rfl
    rw [ha, parseArgs_init] at hparse
    cases hparse
  · have ha : (pqSendInputs W st m r).argv = (Cmd.send (partyAddress st.party.other)).argv := rfl
    have hpeer : addrValOf peer = partyAddr st.party.other :=
      callPeer_of_cmd (.send (partyAddress st.party.other)) rfl (ha ▸ hparse) rfl
    have hcov := fun x g hs => ratchetScopeCoversPq_scopeIn W st x g hwf hs
    have hok := filesOkPeer_pqSend W st m r hcov (pqSessBytes_le_fileCapBytes hwf)
    have hlrK := loadRec_scopeKit_eq encodeInjOn_deserializeScopeP_Q (fun _ h => h) hok
    have hlrIn := loadRec_pqSend encodeInjOn_scopeIn W st m r hcov (pqSessBytes_le_fileCapBytes hwf)
    rw [hpeer]
    unfold PeerSpqrTightValidAt
    rw [hlrK, hlrIn]
    rcases hs : st.session with _ | ⟨x, g⟩
    · trivial
    · exact recordSpqrTightValid_of_wfSession hK hwf hs
  · have ha : (pqRecvInputs W st (wireWhisper :: c) rc).argv =
        (Cmd.recv (partyAddress st.party.other)).argv := rfl
    rw [ha, parseArgs_recv] at hparse
    cases hparse
  · have ha : (pqRecvInputs W st (wirePrekey :: m.bytes) rc).argv =
        (Cmd.recv (partyAddress st.party.other)).argv := rfl
    rw [ha, parseArgs_recv] at hparse
    cases hparse
  · have ha : (pqRecvInputs W st c rc).argv = (Cmd.recv (partyAddress st.party.other)).argv := rfl
    rw [ha, parseArgs_recv] at hparse
    cases hparse

/-- Every `CliPqxdhInputs W i` invocation parsing as `.recv peer` satisfies `PeerSpqrTightValidAt K` for `576 ≤ K`.
-/
theorem peerSpqrTightValidAt_of_cliPqInputs_recv {K : Nat} (hK : 576 ≤ K)
    {W : PEParams} {i : Inputs} {peer : AddrV}
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer)) :
    PeerSpqrTightValidAt K (runFiles i) (addrValOf peer) := by
  obtain ⟨st, hwf, hcases⟩ := hi
  have hrecvCase : ∀ (ct : List (BitVec 8)) (rc : BitVec 256),
      parseArgs uuidTryParse ((pqRecvInputs W st ct rc).argv.map bytesOfString) =
        some (.recv peer) →
      PeerSpqrTightValidAt K (runFiles (pqRecvInputs W st ct rc)) (addrValOf peer) := by
    intro ct rc hp
    have ha : (pqRecvInputs W st ct rc).argv = (Cmd.recv (partyAddress st.party.other)).argv := rfl
    have hpeer : addrValOf peer = partyAddr st.party.other :=
      callPeer_of_cmd (.recv (partyAddress st.party.other)) rfl (ha ▸ hp) rfl
    have hcov := fun x g hs => ratchetScopeCoversPq_scopeIn W st x g hwf hs
    have hok := filesOkPeer_pqRecv W st ct rc hcov (pqSessBytes_le_fileCapBytes hwf)
    have hlrK := loadRec_scopeKit_eq encodeInjOn_deserializeScopeP_Q (fun _ h => h) hok
    have hlrIn := loadRec_pqRecv encodeInjOn_scopeIn W st ct rc hcov (pqSessBytes_le_fileCapBytes hwf)
    rw [hpeer]
    unfold PeerSpqrTightValidAt
    rw [hlrK, hlrIn]
    rcases hs : st.session with _ | ⟨x, g⟩
    · trivial
    · exact recordSpqrTightValid_of_wfSession hK hwf hs
  rcases hcases with ⟨_, b, t, rfl⟩ | ⟨m, r, _, rfl⟩ | ⟨c, rc, _, rfl⟩ | ⟨m, rc, _, rfl⟩ |
    ⟨c, rc, _, _, _, rfl⟩
  · have ha : (pqInitInputs W st b t).argv = (Cmd.init (partyAddress st.party.other) bundleDir).argv := rfl
    rw [ha, parseArgs_init] at hparse
    cases hparse
  · have ha : (pqSendInputs W st m r).argv = (Cmd.send (partyAddress st.party.other)).argv := rfl
    rw [ha, parseArgs_send] at hparse
    cases hparse
  · exact hrecvCase (wireWhisper :: c) rc hparse
  · exact hrecvCase (wirePrekey :: m.bytes) rc hparse
  · exact hrecvCase c rc hparse

theorem peerSpqrTightValid640_of_cliPqInputs_send {W : PEParams} {i : Inputs} {peer : AddrV}
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.send peer)) :
    PeerSpqrTightValid640 (runFiles i) (addrValOf peer) :=
  peerSpqrTightValidAt_of_cliPqInputs_send (by decide) hi hparse

theorem peerSpqrTightValid640_of_cliPqInputs_recv {W : PEParams} {i : Inputs} {peer : AddrV}
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer)) :
    PeerSpqrTightValid640 (runFiles i) (addrValOf peer) :=
  peerSpqrTightValidAt_of_cliPqInputs_recv (by decide) hi hparse

end LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
