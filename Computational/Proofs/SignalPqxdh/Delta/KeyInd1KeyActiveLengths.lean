/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Bound
public import Computational.Proofs.GameHop.StateSim -- proof-setup: allow-public-import
public import Computational.Proofs.GameHop.Fel -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.Collisions -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.SigHop1Key -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.RoKemHop1Key -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.FgGapDh1Key -- proof-setup: allow-public-import

/-!
# Creation-Order Active-Count Length Invariants

Proves online-query (`b.q_on`) creation-order list-length and counter invariants across the
one-key and two-key `KeyInd` games (`G0`–`G3`).
-/

set_option autoImplicit false

open BigOperators OracleSpec OracleComp
open SignalPqxdh (Setup Primitives Bytes QueryBudget BoundedAdv KeyIndAdversary KeyIndQuery
  KeyIndResponse KeyIndState PrincipalEntry SpkBundleEntry OpkEntry KeyIndInitiatorEntry
  HandshakeHdr SessionId PreKeyBundleInput keyIndSpec pqxdhKeyIndImpl pqxdhKeyIndImpl1KeyRo
  pqxdhKeyIndImpl1KeyReal runKeyIndInitiate recordKeyIndResp isKeyIndOnlineQuery isKeyIndSendQuery
  sampleScalar32 sampleCoins32 sampleRandom64 sampleKemKeyGen koskBundleOk resolveSigPk encodeEC
  encodeKEM isHonestUncorruptedPeer checkBundleProvenance CryptoWellFormedPrimitivesδ activeIdCount
  activeSpkCount activeOpkCount activeSendCount activeSendOpkCount activeDhCount)
open SignalPqxdh.Security (HasKeyIndState ShCrState KeyIndShCrState isNoneKeyIndResp
  allHonestEcPksKeyInd runKeyIndSim runKeyInd1KeySim PreservesAt
  spkSlotFlatIdx spkSlotFlatIdx_lt opkSlotFlatIdx opkSlotFlatIdx_lt IsSendSessionId
  sessSlotFlatIdx sessSlotFlatIdx_lt ValidPrincipals ValidSpkBundles ValidOpkEntries
  ValidSessionIds ValidEcLists validEcLists_nil validPrincipals_cons validSpkBundles_cons
  validOpkEntries_cons validSessionIds_cons validPrincipals_map_corrupted
  validSpkBundles_map_revealed ValidKeyIndEc sessPksKeyInd ecSpkSlotIdx ecOpkSlotIdx ecSessSlotIdx)
open Proofs.SignalPqxdh.Security (InitKemRecord RecvKemRecord pqxdhKeyIndShCrImpl
  pqxdhKeyInd1KeyShCrImpl runKeyInd1KeyShCrSim runKeyIndShCrSim1Key
  pqxdhKeyIndImpl1KeyRo_initPrin_preserves_spkBundles map_base_fullKeyInd1KeyShCrImpl_false
  map_proj_simulateQ liftShCrBase liftKeyIndShCrBase recordAcceptKemGeneric
  mem_support_recordAcceptKemGeneric runShCrAcceptGeneric runShCrGenSPKGeneric_false_run
  genSpkBaseGeneric mem_support_genSpkBaseGeneric runShCrInitiate2 mem_support_runShCrInitiate2
  applyShCrFinish_send preCheckKeyInd finishKeyIndBase finishKeyIndBase_spkBundles keyInd1KeyAdvG2_5
  KeyIndAdvCutoffState runKeyIndAdvG3Sim1Key runKeyIndAdvG3Sim1Key_shCr runKeyIndAdvG3Sim1Key_toFg)
open Proofs.SignalPqxdh.Security.FgGapDh1Key (runKeyIndFgSim1Key)

namespace Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveLengths

public section
/-! ## Static-capacity invariant -/

theorem length_le_of_nodup_lt {L : List Nat} {N : Nat}
    (hnd : L.Nodup) (hlt : ∀ x ∈ L, x < N) : L.length ≤ N := by
  have hcard := Finset.card_le_card (s := L.toFinset) (t := Finset.range N)
    (fun x hx => Finset.mem_range.mpr (hlt x (List.mem_toFinset.mp hx)))
  rwa [List.toFinset_card_of_nodup hnd, Finset.card_range] at hcard

private theorem nodup_of_add_map {L : List Nat} (c : Nat)
    (h : (L.map (fun k => c + k)).Nodup) : L.Nodup :=
  (List.nodup_map_iff (fun _ _ (hab : c + _ = c + _) => by omega)).mp h

@[expose] def isSendOpkSession {S : Setup} (e : KeyIndInitiatorEntry S) : Bool :=
  match e.sid with | .sendOPK _ _ => true | _ => false

@[expose] def ValidOpkSessions (S : Setup) (sessions : List (KeyIndInitiatorEntry S)) : Prop :=
  ∀ e ∈ sessions,
    e.hdr.opkId?.isSome = isSendOpkSession e ∧ e.peerOpkPk?.isSome = isSendOpkSession e

@[expose] def KeyIndSlotValid (S : Setup) (st : KeyIndState S) : Prop :=
  ValidKeyIndEc S st ∧ ValidOpkSessions S st.sessions

theorem keyIndSlotValid_empty (S : Setup) (secb : Bool) :
    KeyIndSlotValid S (KeyIndState.empty S secb) :=
  ⟨validEcLists_nil S, fun _ h => False.elim (List.not_mem_nil h)⟩

theorem principals_length_le_of_valid {S : Setup} {principals : List (Nat × PrincipalEntry)}
    (hV : ValidPrincipals S principals) : principals.length ≤ S.N_id := by
  simpa using length_le_of_nodup_lt hV.2
    (fun _ hx => by rcases List.mem_map.mp hx with ⟨e, he, rfl⟩; exact hV.1 e he)

theorem spkBundles_length_le_of_valid {S : Setup}
    {spkBundles : List ((Nat × Nat) × SpkBundleEntry)}
    (hV : ValidSpkBundles S spkBundles) : spkBundles.length ≤ S.N_spk_tot := by
  have hnd : (spkBundles.map (fun e => spkSlotFlatIdx S e.1)).Nodup :=
    nodup_of_add_map S.N_id (by simpa [ecSpkSlotIdx, List.map_map, Function.comp_def] using hV.2)
  simpa using length_le_of_nodup_lt hnd (fun _ hx => by
    rcases List.mem_map.mp hx with ⟨⟨⟨_, _⟩, _⟩, he, rfl⟩
    exact spkSlotFlatIdx_lt S (hV.1 _ he).1 (hV.1 _ he).2)

theorem opkEntries_length_le_of_valid {S : Setup}
    {opkEntries : List ((Nat × Nat × Nat) × OpkEntry)}
    (hV : ValidOpkEntries S opkEntries) : opkEntries.length ≤ S.N_opk_tot := by
  have hnd : (opkEntries.map (fun e => opkSlotFlatIdx S e.1)).Nodup :=
    nodup_of_add_map (S.N_id + S.N_spk_tot)
      (by simpa [ecOpkSlotIdx, List.map_map, Function.comp_def] using hV.2)
  simpa using length_le_of_nodup_lt hnd (fun _ hx => by
    rcases List.mem_map.mp hx with ⟨⟨⟨_, _, _⟩, _⟩, he, rfl⟩
    exact opkSlotFlatIdx_lt S (hV.1 _ he).1 (hV.1 _ he).2.1 (hV.1 _ he).2.2)

private theorem nodup_sessions_flatIdx {S : Setup} {st : KeyIndState S}
    (hV : ValidSessionIds S ((sessPksKeyInd S st).map Prod.fst)) :
    (st.sessions.map (fun e => sessSlotFlatIdx S e.sid)).Nodup :=
  nodup_of_add_map (S.N_id + S.N_spk_tot + S.N_opk_tot)
    (by simpa [sessPksKeyInd, ecSessSlotIdx, List.map_map, Function.comp_def] using hV.2)

theorem sessions_length_le_of_valid {S : Setup} {st : KeyIndState S}
    (hV : ValidSessionIds S ((sessPksKeyInd S st).map Prod.fst)) :
    st.sessions.length ≤ S.N_send_tot := by
  simpa using length_le_of_nodup_lt (nodup_sessions_flatIdx hV) (fun _ hx => by
    rcases List.mem_map.mp hx with ⟨e, he, rfl⟩
    exact sessSlotFlatIdx_lt S e.sid (hV.1 e.sid (by
      simpa [sessPksKeyInd, List.map_map, Function.comp_def] using
        List.mem_map_of_mem (f := KeyIndInitiatorEntry.sid) he)))

theorem sessions_filter_opk_le_of_valid {S : Setup} {st : KeyIndState S}
    (hV : KeyIndSlotValid S st) :
    (st.sessions.filter isSendOpkSession).length ≤ S.N_send_opk_tot := by
  let opkSess := st.sessions.filter isSendOpkSession
  have hnd : (opkSess.map (fun e => sessSlotFlatIdx S e.sid)).Nodup :=
    (nodup_sessions_flatIdx hV.1.2.2.2).sublist (List.filter_sublist.map _)
  simpa [opkSess] using length_le_of_nodup_lt hnd (fun _ hx => by
    rcases List.mem_map.mp hx with ⟨e, he, rfl⟩
    have he_opk : isSendOpkSession e = true := (List.mem_filter.mp he).2
    cases hsid : e.sid with
    | sendOPK u i =>
      dsimp only [sessSlotFlatIdx, Setup.N_send_opk_tot]
      have hmul := Nat.mul_le_mul_right S.N_send_opk (Nat.succ_le_of_lt u.isLt)
      have := i.isLt
      calc u.val * S.N_send_opk + i.val < (u.val + 1) * S.N_send_opk := by ring_nf; omega
        _ ≤ S.N_id * S.N_send_opk := hmul
    | _ => simp [isSendOpkSession, hsid] at he_opk)

theorem sessions_countP_opk_eq_filter {S : Setup} {st : KeyIndState S}
    (hV : KeyIndSlotValid S st) :
    st.sessions.countP (fun e => e.hdr.opkId?.isSome) =
      (st.sessions.filter isSendOpkSession).length := by
  rw [List.countP_eq_length_filter]
  exact congrArg List.length (List.filter_congr fun e he => by rw [(hV.2 e he).1])

theorem sessions_countP_opk_le_of_valid {S : Setup} {st : KeyIndState S}
    (hV : KeyIndSlotValid S st) :
    st.sessions.countP (fun e => e.hdr.opkId?.isSome) ≤ S.N_send_opk_tot :=
  sessions_countP_opk_eq_filter hV ▸ sessions_filter_opk_le_of_valid hV

@[expose] def ecTotalCount {S : Setup} (st : KeyIndState S) : Nat :=
  st.principals.length + st.spkBundles.length + st.opkEntries.length + st.sessions.length

@[simp] theorem ecTotalCount_empty (S : Setup) (secb : Bool) :
    ecTotalCount (KeyIndState.empty S secb) = 0 := rfl

theorem length_allHonestEcPksKeyInd (S : Setup) (P : Primitives) (st : KeyIndState S) :
    (allHonestEcPksKeyInd P st).length = ecTotalCount st := by
  unfold allHonestEcPksKeyInd ecTotalCount; simp [HasKeyIndState.toKeyIndState]; omega

theorem ecTotalCount_le_of_valid {S : Setup} {st : KeyIndState S} (hV : KeyIndSlotValid S st) :
    ecTotalCount st ≤ S.N_dh := by
  have hp := principals_length_le_of_valid hV.1.1
  have hs := spkBundles_length_le_of_valid hV.1.2.1
  have ho := opkEntries_length_le_of_valid hV.1.2.2.1
  have hsess := sessions_length_le_of_valid hV.1.2.2.2
  unfold ecTotalCount Setup.N_dh; omega

/-! ## Online-query length invariants -/

structure KeyIndActiveLengths (S : Setup) (q_on : Nat) (st : KeyIndState S) : Prop where
  principals_le : st.principals.length ≤ activeIdCount S q_on
  spkBundles_le : st.spkBundles.length ≤ activeSpkCount S q_on
  opkEntries_le : st.opkEntries.length ≤ activeOpkCount S q_on
  sessions_le : st.sessions.length ≤ activeSendCount S q_on
  sessionsOpk_le : (st.sessions.filter isSendOpkSession).length ≤ activeSendOpkCount S q_on
  sendOpk_le : st.sessions.countP (fun e => e.hdr.opkId?.isSome) ≤ activeSendOpkCount S q_on
  honestEc_sum_le : ecTotalCount st ≤ activeDhCount S q_on

/-- Active creation-order list-length invariant on `KeyIndState S`. -/
structure KeyIndActiveBounded {S : Setup} (P : Primitives) (st : KeyIndState S)
    (q_on : Nat) : Prop where
  principals_le  : st.principals.length ≤ activeIdCount S q_on
  spkBundles_le  : st.spkBundles.length ≤ activeSpkCount S q_on
  opkEntries_le  : st.opkEntries.length ≤ activeOpkCount S q_on
  sessions_le    : st.sessions.length ≤ activeSendCount S q_on
  sessionsOpk_le : (st.sessions.filter (fun s => match s.sid with
                      | .sendOPK _ _ => true | _ => false)).length ≤ activeSendOpkCount S q_on
  ecPks_le       : (allHonestEcPksKeyInd P st).length ≤ activeDhCount S q_on

theorem KeyIndActiveLengths.allHonestEcPks_le {S : Setup} {q_on : Nat} {st : KeyIndState S}
    (h : KeyIndActiveLengths S q_on st) (P : Primitives) :
    (allHonestEcPksKeyInd P st).length ≤ activeDhCount S q_on :=
  length_allHonestEcPksKeyInd S P st ▸ h.honestEc_sum_le

theorem KeyIndActiveLengths.toBounded {S : Setup} {q_on : Nat} {st : KeyIndState S}
    (h : KeyIndActiveLengths S q_on st) (P : Primitives) : KeyIndActiveBounded P st q_on :=
  ⟨h.principals_le, h.spkBundles_le, h.opkEntries_le, h.sessions_le,
   h.sessionsOpk_le, h.allHonestEcPks_le P⟩

theorem KeyIndActiveLengths.sendOpk_bne_none_le {S : Setup} {q_on : Nat} {st : KeyIndState S}
    (h : KeyIndActiveLengths S q_on st) :
    st.sessions.countP (fun e => e.hdr.opkId? != none) ≤ activeSendOpkCount S q_on := by
  have heq : (fun e : KeyIndInitiatorEntry S => e.hdr.opkId? != none) =
      (fun e => e.hdr.opkId?.isSome) := by funext e; cases e.hdr.opkId? <;> rfl
  rw [heq]; exact h.sendOpk_le

theorem keyIndActiveLengths_of_valid_and_total {S : Setup} {q_on : Nat} {st : KeyIndState S}
    (hV : KeyIndSlotValid S st) (hOn : ecTotalCount st ≤ q_on) :
    KeyIndActiveLengths S q_on st := by
  have hp_s := principals_length_le_of_valid hV.1.1
  have hs_s := spkBundles_length_le_of_valid hV.1.2.1
  have ho_s := opkEntries_length_le_of_valid hV.1.2.2.1
  have hsess_s := sessions_length_le_of_valid hV.1.2.2.2
  have hfilt_s := sessions_filter_opk_le_of_valid hV
  have hopk_s := sessions_countP_opk_le_of_valid hV
  have hdh_act : ecTotalCount st ≤ activeDhCount S q_on :=
    Nat.le_min.mpr ⟨hOn, ecTotalCount_le_of_valid hV⟩
  have hfilt_le : (st.sessions.filter isSendOpkSession).length ≤ st.sessions.length :=
    List.length_filter_le _ _
  have hcnt_le : st.sessions.countP (fun e => e.hdr.opkId?.isSome) ≤ st.sessions.length :=
    List.countP_le_length
  unfold ecTotalCount at hOn
  refine ⟨by unfold activeIdCount; omega, by unfold activeSpkCount; omega,
    by unfold activeOpkCount; omega, by unfold activeSendCount; omega,
    by unfold activeSendOpkCount; omega, by unfold activeSendOpkCount; omega, hdh_act⟩

theorem mem_support_runKeyIndInitiate (useRo : Bool) (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (st : KeyIndState S)
    (x : KeyIndResponse × KeyIndState S)
    (hx : x ∈ support ((runKeyIndInitiate useRo S P sid u bundle).run st)) :
    x.2 = st ∨
    (st.sessions.any (fun e => e.sid == sid) = false ∧
     ∃ eNew roCache',
       eNew.sid = sid ∧
       eNew.hdr.opkId? = bundle.opkB?.map Prod.fst ∧
       eNew.peerOpkPk? = bundle.opkB?.map Prod.snd ∧
       x.2 = { st with sessions := eNew :: st.sessions, roCache := roCache' }) := by
  unfold runKeyIndInitiate at hx; dsimp only at hx
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
  cases hFresh : st.sessions.any (fun e => e.sid == sid) with
  | true =>
    rw [hFresh] at hx; simp only [↓reduceIte, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hx; subst hx; exact Or.inl rfl
  | false =>
    rw [hFresh] at hx; simp only [Bool.false_eq_true, ↓reduceIte] at hx
    cases hFind : st.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      rw [hFind] at hx; simp only [StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hx; subst hx; exact Or.inl rfl
    | some uPair =>
      rw [hFind] at hx; rcases uPair with ⟨_, _⟩; dsimp only at hx
      cases hKosk : !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle with
      | true =>
        rw [hKosk] at hx; simp only [↓reduceIte, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hx; subst hx; exact Or.inl rfl
      | false =>
        rw [hKosk] at hx
        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hx
        rcases hx with ⟨ekASk, _, kemCoins, _, hx⟩
        cases hSig : !(P.sigVerify (resolveSigPk P st.principals bundle.ikB)
            (encodeEC bundle.spkB) bundle.spkSig &&
            P.sigVerify (resolveSigPk P st.principals bundle.ikB)
            (encodeKEM bundle.pqspkB) bundle.pqspkSig) with
        | true =>
          rw [hSig] at hx; simp only [↓reduceIte, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at hx; subst hx; exact Or.inl rfl
        | false =>
          rw [hSig] at hx; simp only [Bool.false_eq_true, ↓reduceIte] at hx
          cases hKem : P.kemEncaps bundle.pqspkB kemCoins with
          | none =>
            rw [hKem] at hx; simp only [StateT.run_pure, support_pure,
              Set.mem_singleton_iff] at hx; subst hx; exact Or.inl rfl
          | some kemOut =>
            rw [hKem] at hx; rcases kemOut with ⟨_, _⟩; dsimp only at hx
            simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
              bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hx
            rcases hx with ⟨⟨_, roCache'⟩, _, hx⟩
            split at hx <;>
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hx
            swap; rcases hx with ⟨_, _, hx⟩; all_goals
            cases hHon : SignalPqxdh.findHonestPrincipal P st.principals bundle.ikB <;> (
              rw [hHon] at hx; simp only [StateT.run_pure, support_pure,
                Set.mem_singleton_iff] at hx
              subst hx; exact Or.inr ⟨rfl, _, roCache', rfl, rfl, rfl, rfl⟩)

theorem runKeyIndInitiate_slotValid_and_step (useRo : Bool) (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (hOpkSid : bundle.opkB?.isSome = match sid with | .sendOPK _ _ => true | _ => false)
    (hSend : IsSendSessionId S sid)
    (st : KeyIndState S) (hV : KeyIndSlotValid S st) :
    ∀ x ∈ support ((runKeyIndInitiate useRo S P sid u bundle).run st),
      KeyIndSlotValid S x.2 ∧ ecTotalCount x.2 ≤ ecTotalCount st + 1 := by
  intro x hx
  rcases mem_support_runKeyIndInitiate useRo S P sid u bundle st x hx with
    hEq | ⟨hFresh, eNew, roCache', hsid, hopk, hpeer, hEq⟩
  · rw [hEq]; exact ⟨hV, Nat.le_succ _⟩
  · rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hVOpk⟩
    have hFresh' : ((sessPksKeyInd S st).map Prod.fst).any (fun s => s == sid) = false := by
      simpa [sessPksKeyInd, List.any_map, Function.comp_def] using hFresh
    have hVSess' := (validSessionIds_cons S sid ((sessPksKeyInd S st).map Prod.fst)
      hSend hVSess hFresh').1
    rw [hEq]
    refine ⟨⟨⟨hVP, hVS, hVO, by simpa [sessPksKeyInd, hsid] using hVSess'⟩, fun e he => ?_⟩,
      by simp [ecTotalCount]; omega⟩
    rcases List.mem_cons.mp he with rfl | hmem
    · have hm1 : (bundle.opkB?.map Prod.fst).isSome = bundle.opkB?.isSome := by
        cases bundle.opkB? <;> rfl
      have hm2 : (bundle.opkB?.map Prod.snd).isSome = bundle.opkB?.isSome := by
        cases bundle.opkB? <;> rfl
      simpa [isSendOpkSession, hsid, hopk, hpeer] using
        And.intro (hm1.trans hOpkSid) (hm2.trans hOpkSid)
    · exact hVOpk e hmem

@[expose] def PqxdhStepShape {S : Setup} (useRo : Bool) (P : Primitives)
    (q : KeyIndQuery S) (st : KeyIndState S) (x : (keyIndSpec S).Range q × KeyIndState S) : Prop :=
  match q with
  | .initPrin u => x.2 = st ∨
      (st.principals.any (fun (idx, _) => idx == u.val) = false ∧
       ∃ sk1 sk2, x.2 = { st with principals := (u.val,
         { secIKA0 := sk1, ikAPk := P.x25519Base sk1, secIKAsign := sk2,
           ikSignPk := P.sigPkGen sk2, corrupted := false }) :: st.principals })
  | .corruptIK u => x.2 = st ∨
      x.2 = { st with principals := st.principals.map (fun (idx, e) =>
        if idx == u.val then (idx, { e with corrupted := true }) else (idx, e)) }
  | .genSPK u j => x.2 = st ∨
      (st.spkBundles.any (fun (k, _) => k == (u.val, j.val)) = false ∧
       ∃ spkSk pqspkPk pqspkSk spkSig pqspkSig,
         x.2 = { st with spkBundles := ((u.val, j.val),
           { spkSk := spkSk, spkPk := P.x25519Base spkSk, pqspkSk := pqspkSk,
             pqspkPk := pqspkPk, spkSig := spkSig, pqspkSig := pqspkSig,
             revealed := false }) :: st.spkBundles })
  | .genOPK u j o => x.2 = st ∨
      (st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) = false ∧
       ∃ opkSk, x.2 = { st with opkEntries := ((u.val, j.val, o.val),
         { opkSk := opkSk, opkPk := P.x25519Base opkSk, consumed := false }) :: st.opkEntries })
  | .initiateOPK u i bundle => x.2 = st ∨
      (bundle.opkB?.isSome = true ∧
       x ∈ support ((runKeyIndInitiate useRo S P (.sendOPK u i) u bundle).run st))
  | .initiateNoOPK u i bundle => x.2 = st ∨
      (bundle.opkB?.isSome = false ∧
       x ∈ support ((runKeyIndInitiate useRo S P (.sendNoOPK u i) u bundle).run st))
  | .acceptOPK _ _ _ _ =>
      x.2.principals = st.principals ∧ x.2.spkBundles = st.spkBundles ∧
      x.2.sessions = st.sessions ∧
      x.2.opkEntries.map (fun (idx, e) => (idx, e.opkPk)) =
        st.opkEntries.map (fun (idx, e) => (idx, e.opkPk))
  | .revealSpkSk u j => x.2 = st ∨
      x.2 = { st with spkBundles := st.spkBundles.map (fun (idx, b) =>
        if idx == (u.val, j.val) then (idx, { b with revealed := true }) else (idx, b)) }
  | .testSession _ | .revealSessionKey _ =>
      x.2.principals = st.principals ∧ x.2.spkBundles = st.spkBundles ∧
      x.2.opkEntries = st.opkEntries ∧
      x.2.sessions.map (fun e => (e.sid, e.ekASk, e.peerIkPk, e.peerOpkPk?, e.hdr)) =
        st.sessions.map (fun e => (e.sid, e.ekASk, e.peerIkPk, e.peerOpkPk?, e.hdr))
  | .acceptNoOPK _ _ _ _ | .roQuery _ | .registerKey _ | .revealDhSecrets =>
      x.2.principals = st.principals ∧ x.2.spkBundles = st.spkBundles ∧
      x.2.opkEntries = st.opkEntries ∧ x.2.sessions = st.sessions

theorem mem_support_pqxdhKeyIndImpl (useRo : Bool) (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (st : KeyIndState S)
    (x : (keyIndSpec S).Range q × KeyIndState S)
    (hx : x ∈ support ((pqxdhKeyIndImpl useRo S P q).run st)) :
    PqxdhStepShape useRo P q st x := by
  cases q with
  | initPrin u =>
    unfold pqxdhKeyIndImpl at hx; dsimp only [PqxdhStepShape] at hx ⊢
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
    cases hF : st.principals.any (fun (idx, _) => idx == u.val) with
    | true =>
      rw [hF] at hx; simp only [↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hx; subst hx; exact Or.inl rfl
    | false =>
      rw [hF] at hx; simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc,
        pure_bind, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨sk1, _, sk2, _, rfl⟩; exact Or.inr ⟨rfl, sk1, sk2, rfl⟩
  | corruptIK u =>
    unfold pqxdhKeyIndImpl at hx; dsimp only [PqxdhStepShape] at hx ⊢
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
    cases hF : st.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      rw [hF] at hx; simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact Or.inl rfl
    | some p =>
      rw [hF] at hx; rcases p with ⟨_, _⟩; dsimp only at hx
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hx; subst hx; exact Or.inr rfl
  | genSPK u j =>
    unfold pqxdhKeyIndImpl at hx; dsimp only [PqxdhStepShape] at hx ⊢
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
    cases hF : st.spkBundles.any (fun (k, _) => k == (u.val, j.val)) with
    | true =>
      rw [hF] at hx; simp only [↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hx; subst hx; exact Or.inl rfl
    | false =>
      rw [hF] at hx; simp only [Bool.false_eq_true, ↓reduceIte] at hx
      cases hU : st.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        rw [hU] at hx; simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
        subst hx; exact Or.inl rfl
      | some p =>
        rw [hU] at hx; rcases p with ⟨_, _⟩; dsimp only at hx
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind,
          support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨spkSk, _, _, _, ⟨pqspkPk, pqspkSk⟩, _, _, _, rfl⟩
        exact Or.inr ⟨rfl, spkSk, pqspkPk, pqspkSk, _, _, rfl⟩
  | genOPK u j o =>
    unfold pqxdhKeyIndImpl at hx; dsimp only [PqxdhStepShape] at hx ⊢
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
    cases hF : st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) with
    | true =>
      rw [hF] at hx; simp only [↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hx; subst hx; exact Or.inl rfl
    | false =>
      rw [hF] at hx; simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc,
        pure_bind, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨opkSk, _, rfl⟩; exact Or.inr ⟨rfl, opkSk, rfl⟩
  | initiateOPK u i bundle =>
    unfold pqxdhKeyIndImpl at hx; dsimp only [PqxdhStepShape] at hx ⊢
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
    cases hOpt : bundle.opkB? with
    | none =>
      rw [hOpt] at hx; simp only [Option.isNone_none, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hx; subst hx; exact Or.inl rfl
    | some _ =>
      rw [hOpt] at hx; simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at hx
      exact Or.inr ⟨rfl, hx⟩
  | initiateNoOPK u i bundle =>
    unfold pqxdhKeyIndImpl at hx; dsimp only [PqxdhStepShape] at hx ⊢
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
    cases hOpt : bundle.opkB? with
    | some _ =>
      rw [hOpt] at hx; simp only [Option.isSome_some, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hx; subst hx; exact Or.inl rfl
    | none =>
      rw [hOpt] at hx; simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hx
      exact Or.inr ⟨rfl, hx⟩
  | acceptOPK k j o hdr =>
    let projOpk := fun s : KeyIndState S =>
      (s.principals, s.spkBundles, s.sessions, s.opkEntries.map (fun (idx, e) => (idx, e.opkPk)))
    have hp : PreservesAt projOpk st (pqxdhKeyIndImpl useRo S P (.acceptOPK k j o hdr)) := by
      have h_step : ∀ (s : KeyIndState S) u t rc,
          projOpk { s with
            opkEntries := s.opkEntries.map (fun (idx, e) =>
              if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
            usedRecvOPK := u, seenKyberBaseKeys := t, roCache := rc } = projOpk s := by
        intro s u t rc; refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
        dsimp only [projOpk]; rw [List.map_map]
        exact List.map_congr_left fun ⟨_, _⟩ _ => by simp only [Function.comp_def]; split_ifs <;> rfl
      unfold pqxdhKeyIndImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | ((with_reducible apply PreservesAt.recordKeyIndResp_pure); intro _; rfl)
        | ((with_reducible apply PreservesAt.set_bind); exact h_step _ _ _ _)
        | split)
    have h := hp x hx
    exact ⟨congrArg Prod.fst h, congrArg (Prod.fst ∘ Prod.snd) h,
      congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) h, congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) h⟩
  | revealSpkSk u j =>
    unfold pqxdhKeyIndImpl at hx; dsimp only [PqxdhStepShape] at hx ⊢
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
    cases hF : st.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with
    | none =>
      rw [hF] at hx; simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact Or.inl rfl
    | some bp =>
      rw [hF] at hx; rcases bp with ⟨_, _⟩; dsimp only at hx
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hx; subst hx; exact Or.inr rfl
  | testSession sid | revealSessionKey sid =>
    let projSess := fun s : KeyIndState S =>
      (s.principals, s.spkBundles, s.opkEntries,
       s.sessions.map (fun e => (e.sid, e.ekASk, e.peerIkPk, e.peerOpkPk?, e.hdr)))
    suffices h : projSess x.2 = projSess st from
      ⟨congrArg Prod.fst h, congrArg (Prod.fst ∘ Prod.snd) h,
       congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) h, congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) h⟩
    revert x hx
    change PreservesAt projSess st _
    unfold pqxdhKeyIndImpl; dsimp only
    repeat (first
      | with_reducible apply PreservesAt.pure
      | with_reducible apply PreservesAt.get_bind
      | ((with_reducible apply PreservesAt.set_bind); rfl)
      | ((with_reducible apply PreservesAt.set_bind);
          refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_));
          dsimp only [projSess]; rw [List.map_map];
          exact List.map_congr_left fun _ _ => by simp only [Function.comp_def]; split_ifs <;> rfl)
      | (split; try dsimp only))
  | _ =>
    let proj := fun s : KeyIndState S => (s.principals, s.spkBundles, s.opkEntries, s.sessions)
    suffices h : proj x.2 = proj st from
      ⟨congrArg Prod.fst h, congrArg (Prod.fst ∘ Prod.snd) h,
       congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) h, congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) h⟩
    revert x hx
    change PreservesAt proj st _
    unfold pqxdhKeyIndImpl; dsimp only
    repeat (first
      | with_reducible apply PreservesAt.pure
      | with_reducible apply PreservesAt.get_bind
      | (with_reducible apply PreservesAt.liftM_bind; intro _)
      | ((with_reducible apply PreservesAt.recordKeyIndResp_pure); intro _; rfl)
      | ((with_reducible apply PreservesAt.set_bind); rfl)
      | (split; try dsimp only))

theorem pqxdhKeyIndImpl_slotValid_and_step (useRo : Bool) (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (st : KeyIndState S) (hV : KeyIndSlotValid S st) :
    ∀ x ∈ support ((pqxdhKeyIndImpl useRo S P q).run st),
      KeyIndSlotValid S x.2 ∧
      (if isKeyIndOnlineQuery (.inr q) then ecTotalCount x.2 ≤ ecTotalCount st + 1
       else ecTotalCount x.2 = ecTotalCount st) := by
  intro x hx
  have hsh := mem_support_pqxdhKeyIndImpl useRo S P q st x hx
  rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hVOpk⟩
  cases q with
  | initPrin u =>
    rcases hsh with hEq | ⟨hF, _, _, hEq⟩
    · rw [hEq]; exact ⟨⟨⟨hVP, hVS, hVO, hVSess⟩, hVOpk⟩, by simp [isKeyIndOnlineQuery]⟩
    · rw [hEq]; exact ⟨⟨⟨(validPrincipals_cons S u _ st.principals hVP hF).1, hVS, hVO, hVSess⟩,
        hVOpk⟩, by simp [isKeyIndOnlineQuery, ecTotalCount]; omega⟩
  | corruptIK u =>
    rcases hsh with hEq | hEq
    · rw [hEq]; exact ⟨⟨⟨hVP, hVS, hVO, hVSess⟩, hVOpk⟩, by simp [isKeyIndOnlineQuery]⟩
    · rw [hEq]; exact ⟨⟨⟨(validPrincipals_map_corrupted S P u.val st.principals hVP).1, hVS, hVO,
        hVSess⟩, hVOpk⟩, by simp [isKeyIndOnlineQuery, ecTotalCount]⟩
  | genSPK u j =>
    rcases hsh with hEq | ⟨hF, _, _, _, _, _, hEq⟩
    · rw [hEq]; exact ⟨⟨⟨hVP, hVS, hVO, hVSess⟩, hVOpk⟩, by simp [isKeyIndOnlineQuery]⟩
    · rw [hEq]; exact ⟨⟨⟨hVP, (validSpkBundles_cons S u j _ st.spkBundles hVS hF).1, hVO, hVSess⟩,
        hVOpk⟩, by simp [isKeyIndOnlineQuery, ecTotalCount]; omega⟩
  | genOPK u j o =>
    rcases hsh with hEq | ⟨hF, _, hEq⟩
    · rw [hEq]; exact ⟨⟨⟨hVP, hVS, hVO, hVSess⟩, hVOpk⟩, by simp [isKeyIndOnlineQuery]⟩
    · rw [hEq]; exact ⟨⟨⟨hVP, hVS, (validOpkEntries_cons S u j o _ st.opkEntries hVO hF).1, hVSess⟩,
        hVOpk⟩, by simp [isKeyIndOnlineQuery, ecTotalCount]; omega⟩
  | initiateOPK u i bundle =>
    rcases hsh with hEq | ⟨hSome, hx'⟩
    · rw [hEq]; exact ⟨⟨⟨hVP, hVS, hVO, hVSess⟩, hVOpk⟩, by simp [isKeyIndOnlineQuery]⟩
    · simpa [isKeyIndOnlineQuery] using runKeyIndInitiate_slotValid_and_step useRo S P
        (.sendOPK u i) u bundle hSome trivial st ⟨⟨hVP, hVS, hVO, hVSess⟩, hVOpk⟩ x hx'
  | initiateNoOPK u i bundle =>
    rcases hsh with hEq | ⟨hNone, hx'⟩
    · rw [hEq]; exact ⟨⟨⟨hVP, hVS, hVO, hVSess⟩, hVOpk⟩, by simp [isKeyIndOnlineQuery]⟩
    · simpa [isKeyIndOnlineQuery] using runKeyIndInitiate_slotValid_and_step useRo S P
        (.sendNoOPK u i) u bundle hNone trivial st ⟨⟨hVP, hVS, hVO, hVSess⟩, hVOpk⟩ x hx'
  | acceptOPK k j o hdr =>
    rcases hsh with ⟨hp1, hp2, hp4, hp3_pair⟩
    have hp3 : x.2.opkEntries.map Prod.fst = st.opkEntries.map Prod.fst := by
      simpa [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) hp3_pair
    have hp_len : x.2.opkEntries.length = st.opkEntries.length := by
      simpa using congrArg List.length hp3
    have hVO' : ValidOpkEntries S x.2.opkEntries := ⟨fun e he => by
        rcases List.mem_map.mp (hp3 ▸ List.mem_map_of_mem he) with ⟨e', he', heq⟩
        exact heq ▸ hVO.1 e' he',
      by
        have hs : x.2.opkEntries.map (fun e => ecOpkSlotIdx S e.1) =
            st.opkEntries.map (fun e => ecOpkSlotIdx S e.1) := by
          simpa [List.map_map, Function.comp_def] using congrArg (List.map (ecOpkSlotIdx S)) hp3
        rw [hs]; exact hVO.2⟩
    exact ⟨⟨⟨hp1 ▸ hVP, hp2 ▸ hVS, hVO', by simpa [sessPksKeyInd, hp4] using hVSess⟩,
      hp4 ▸ hVOpk⟩, by simp [isKeyIndOnlineQuery, ecTotalCount, hp1, hp2, hp4, hp_len]⟩
  | revealSpkSk u j =>
    rcases hsh with hEq | hEq
    · rw [hEq]; exact ⟨⟨⟨hVP, hVS, hVO, hVSess⟩, hVOpk⟩, by simp [isKeyIndOnlineQuery]⟩
    · rw [hEq]; exact ⟨⟨⟨hVP, (validSpkBundles_map_revealed S P (u.val, j.val) st.spkBundles hVS).1,
        hVO, hVSess⟩, hVOpk⟩, by simp [isKeyIndOnlineQuery, ecTotalCount]⟩
  | testSession _ | revealSessionKey _ =>
    rcases hsh with ⟨hp1, hp2, hp3, hp4⟩
    have hlen : x.2.sessions.length = st.sessions.length := by
      simpa using congrArg List.length hp4
    have hsid : (sessPksKeyInd S x.2).map Prod.fst = (sessPksKeyInd S st).map Prod.fst := by
      simpa [sessPksKeyInd, List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) hp4
    have hopk : ValidOpkSessions S x.2.sessions := fun e he => by
      rcases List.mem_map.mp (hp4 ▸ List.mem_map_of_mem he) with ⟨e', he', heq⟩
      rcases Prod.mk.inj heq with ⟨hs1, heq2⟩
      rcases Prod.mk.inj heq2 with ⟨_, heq3⟩
      rcases Prod.mk.inj heq3 with ⟨_, heq4⟩
      rcases Prod.mk.inj heq4 with ⟨hpeer, hhdr⟩
      simpa [isSendOpkSession, ← hs1, ← hpeer, ← hhdr] using hVOpk e' he'
    exact ⟨⟨⟨hp1 ▸ hVP, hp2 ▸ hVS, hp3 ▸ hVO, hsid ▸ hVSess⟩, hopk⟩,
      by simp [isKeyIndOnlineQuery, ecTotalCount, hp1, hp2, hp3, hlen]⟩
  | acceptNoOPK _ _ _ _ | roQuery _ | registerKey _ | revealDhSecrets =>
    rcases hsh with ⟨hp1, hp2, hp3, hp4⟩
    exact ⟨⟨⟨hp1 ▸ hVP, hp2 ▸ hVS, hp3 ▸ hVO, by simpa [sessPksKeyInd, hp4] using hVSess⟩,
      hp4 ▸ hVOpk⟩, by split_ifs <;> simp [ecTotalCount, hp1, hp2, hp3, hp4]⟩

theorem pqxdhKeyIndImpl1KeyRo_slotValid_and_step (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (st : KeyIndState S) (hV : KeyIndSlotValid S st) :
    ∀ x ∈ support ((pqxdhKeyIndImpl1KeyRo S P q).run st),
      KeyIndSlotValid S x.2 ∧
      (if isKeyIndOnlineQuery (.inr q) then ecTotalCount x.2 ≤ ecTotalCount st + 1
       else ecTotalCount x.2 = ecTotalCount st) := by
  cases q with
  | initPrin u =>
    rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hVOpk⟩
    intro x hx
    unfold pqxdhKeyIndImpl1KeyRo pqxdhKeyIndImpl1KeyReal at hx; dsimp only at hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
    cases hFresh : st.principals.any (fun (idx, _) => idx == u.val) with
    | true =>
      rw [hFresh] at hx
      simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨⟨⟨hVP, hVS, hVO, hVSess⟩, hVOpk⟩, by simp [isKeyIndOnlineQuery]⟩
    | false =>
      rw [hFresh] at hx
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨_, _, rfl⟩
      refine ⟨⟨⟨(validPrincipals_cons S u _ st.principals hVP hFresh).1, hVS, hVO, hVSess⟩, hVOpk⟩,
        ?_⟩
      simp [isKeyIndOnlineQuery, ecTotalCount]; omega
  | _ =>
    exact pqxdhKeyIndImpl_slotValid_and_step true S P _ st hV

/-- Generic support invariant for a counter that grows by at most `1` on `charged` queries and is
    unchanged on uncharged queries. -/
theorem simulateQ_count_le_of_queryBound {ι σ α : Type} {spec : OracleSpec.{0, 0} ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (charged : ι → Prop) [DecidablePred charged]
    (inv : σ → Prop) (cnt : σ → Nat)
    (hstep : ∀ t s, inv s → ∀ z ∈ support ((impl t).run s),
      inv z.2 ∧ (if charged t then cnt z.2 ≤ cnt s + 1 else cnt z.2 = cnt s))
    (oa : OracleComp spec α) (rem cap : Nat)
    (hqb : oa.IsQueryBoundP charged rem)
    (s : σ) (hinv : inv s) (hbud : cnt s + rem ≤ cap) :
    ∀ z ∈ support ((simulateQ impl oa).run s), inv z.2 ∧ cnt z.2 ≤ cap := by
  induction oa using OracleComp.inductionOn generalizing rem s with
  | pure a =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    dsimp only
    exact ⟨hinv, by omega⟩
  | query_bind t cont ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hqb
    intro z hz
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
      simulateQ_query_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨y, hy, hz⟩
    have hy_step := hstep t s hinv y hy
    by_cases ht : charged t
    · rcases rem with _ | m
      · exact absurd (hqb.1.resolve_left (not_not.mpr ht)) (Nat.not_lt_zero 0)
      · have hqb' : (cont y.1).IsQueryBoundP charged m := by simpa [ht] using hqb.2 y.1
        have hcnt : cnt y.2 ≤ cnt s + 1 := by simpa [ht] using hy_step.2
        exact ih y.1 m hqb' y.2 hy_step.1 (by omega) z hz
    · have hqb' : (cont y.1).IsQueryBoundP charged rem := by simpa [ht] using hqb.2 y.1
      have hcnt : cnt y.2 = cnt s := by simpa [ht] using hy_step.2
      exact ih y.1 rem hqb' y.2 hy_step.1 (by omega) z hz

private theorem keyIndActiveLengths_of_simulateQ_impl {α : Type} (S : Setup)
    (impl : QueryImpl (keyIndSpec S) (StateT (KeyIndState S) ProbComp))
    (hstep : ∀ gq s, KeyIndSlotValid S s → ∀ z ∈ support ((impl gq).run s),
      KeyIndSlotValid S z.2 ∧
      (if isKeyIndOnlineQuery (.inr gq) then ecTotalCount z.2 ≤ ecTotalCount s + 1
       else ecTotalCount z.2 = ecTotalCount s))
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (rem q_on : Nat)
    (hqb : oa.IsQueryBoundP isKeyIndOnlineQuery rem)
    (st : KeyIndState S) (hV : KeyIndSlotValid S st) (hbud : ecTotalCount st + rem ≤ q_on) :
    ∀ z ∈ support ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndState S) ProbComp) + impl) oa).run st),
      KeyIndSlotValid S z.2 ∧ KeyIndActiveLengths S q_on z.2 := by
  let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (KeyIndState S) ProbComp) + impl
  have hsim := simulateQ_count_le_of_queryBound fullImpl isKeyIndOnlineQuery
    (KeyIndSlotValid S) ecTotalCount
    (fun t s hs z hz => by
      cases t with
      | inl _ =>
        simp only [fullImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
          QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
        rcases hz with ⟨_, _, rfl⟩; exact ⟨hs, by simp [isKeyIndOnlineQuery]⟩
      | inr gq => exact hstep gq s hs z hz)
    oa rem q_on hqb st hV hbud
  exact fun z hz => ⟨(hsim z hz).1, keyIndActiveLengths_of_valid_and_total (hsim z hz).1 (hsim z hz).2⟩

theorem keyIndActiveLengths_of_simulateQ_1Key {α : Type} (S : Setup) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (rem q_on : Nat)
    (hqb : oa.IsQueryBoundP isKeyIndOnlineQuery rem)
    (st : KeyIndState S) (hV : KeyIndSlotValid S st) (hbud : ecTotalCount st + rem ≤ q_on) :
    ∀ z ∈ support ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndState S) ProbComp) + pqxdhKeyIndImpl1KeyRo S P) oa).run st),
      KeyIndSlotValid S z.2 ∧ KeyIndActiveLengths S q_on z.2 :=
  keyIndActiveLengths_of_simulateQ_impl S (pqxdhKeyIndImpl1KeyRo S P)
    (pqxdhKeyIndImpl1KeyRo_slotValid_and_step S P) oa rem q_on hqb st hV hbud

theorem keyIndActiveLengths_of_simulateQ {α : Type} (useRo : Bool) (S : Setup) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (rem q_on : Nat)
    (hqb : oa.IsQueryBoundP isKeyIndOnlineQuery rem)
    (st : KeyIndState S) (hV : KeyIndSlotValid S st) (hbud : ecTotalCount st + rem ≤ q_on) :
    ∀ z ∈ support ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndState S) ProbComp) + pqxdhKeyIndImpl useRo S P) oa).run st),
      KeyIndSlotValid S z.2 ∧ KeyIndActiveLengths S q_on z.2 :=
  keyIndActiveLengths_of_simulateQ_impl S (pqxdhKeyIndImpl useRo S P)
    (pqxdhKeyIndImpl_slotValid_and_step useRo S P) oa rem q_on hqb st hV hbud

theorem keyIndActiveLengths_of_runKeyInd1KeySim (S : Setup) (P : Primitives) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    ∀ x ∈ support (runKeyInd1KeySim S P A.1), KeyIndActiveLengths S b.q_on x.2.2 := by
  intro x hx
  simp only [runKeyInd1KeySim, MonadAttach.mem_support_bind, support_pure,
    Set.mem_singleton_iff] at hx
  rcases hx with ⟨secb, _, ⟨b', finalSt⟩, hmem, rfl⟩
  exact (keyIndActiveLengths_of_simulateQ_1Key S P A.1.run b.q_on b.q_on A.2.2.2.2.2
    (KeyIndState.empty S secb) (keyIndSlotValid_empty S secb) (by simp) (b', finalSt) hmem).2

theorem keyIndActiveLengths_of_runKeyIndSim (useRo : Bool) (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    ∀ x ∈ support (runKeyIndSim useRo S P A.1), KeyIndActiveLengths S b.q_on x.2.2 := by
  intro x hx
  simp only [runKeyIndSim, MonadAttach.mem_support_bind, support_pure,
    Set.mem_singleton_iff] at hx
  rcases hx with ⟨secb, _, ⟨b', finalSt⟩, hmem, rfl⟩
  exact (keyIndActiveLengths_of_simulateQ useRo S P A.1.run b.q_on b.q_on A.2.2.2.2.2
    (KeyIndState.empty S secb) (keyIndSlotValid_empty S secb) (by simp) (b', finalSt) hmem).2

theorem keyIndActiveLengths_of_runKeyInd1KeyShCrSim (S : Setup) (P : Primitives) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    ∀ x ∈ support (runKeyInd1KeyShCrSim S P A.1), KeyIndActiveLengths S b.q_on x.2.2.base := by
  intro x hx
  simp only [runKeyInd1KeyShCrSim, MonadAttach.mem_support_bind, support_pure,
    Set.mem_singleton_iff] at hx
  rcases hx with ⟨secb, _, ⟨b', finalHst⟩, hmem, rfl⟩
  have hproj := map_proj_simulateQ ShCrState.base
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyInd1KeyShCrImpl false S P)
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndState S) ProbComp) + pqxdhKeyIndImpl1KeyRo S P)
    (map_base_fullKeyInd1KeyShCrImpl_false S P)
    A.1.run { base := KeyIndState.empty S secb }
  have hmem_base : (b', finalHst.base) ∈ support
      ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndState S) ProbComp) + pqxdhKeyIndImpl1KeyRo S P) A.1.run).run
        (KeyIndState.empty S secb)) := by
    rw [← hproj, support_map]
    exact ⟨(b', finalHst), hmem, rfl⟩
  exact (keyIndActiveLengths_of_simulateQ_1Key S P A.1.run b.q_on b.q_on A.2.2.2.2.2
    (KeyIndState.empty S secb) (keyIndSlotValid_empty S secb) (by simp)
    (b', finalHst.base) hmem_base).2

theorem keyIndActiveLengths_of_runKeyIndShCrSim1Key (S : Setup) (P : Primitives) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    ∀ x ∈ support (runKeyIndShCrSim1Key S P A.1), KeyIndActiveLengths S b.q_on x.2.2.base :=
  keyIndActiveLengths_of_runKeyInd1KeyShCrSim S P b A

theorem keyIndActiveLengths_of_runKeyIndAdvG3Sim1Key (S : Setup) (P : Primitives) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    ∀ x ∈ support (runKeyIndAdvG3Sim1Key S P A.1),
      KeyIndActiveLengths S b.q_on x.2.2.shCr.base := by
  intro x hx
  have hmem_shcr : (x.1, x.2.1, x.2.2.shCr) ∈ support (runKeyIndShCrSim1Key S P A.1) := by
    rw [← runKeyIndAdvG3Sim1Key_shCr, support_map]
    exact ⟨x, hx, by rcases x with ⟨_, _, _⟩; rfl⟩
  exact keyIndActiveLengths_of_runKeyIndShCrSim1Key S P b A _ hmem_shcr

theorem keyIndActiveLengths_of_runKeyIndFgSim1Key (S : Setup) (P : Primitives) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    ∀ x ∈ support (runKeyIndFgSim1Key S P A.1), KeyIndActiveLengths S b.q_on x.2.2.base := by
  intro x hx
  have hx_fg : x ∈ support (Prod.map id (Prod.map id KeyIndAdvCutoffState.toFg) <$>
      runKeyIndAdvG3Sim1Key S P A.1) := by
    rwa [runKeyIndAdvG3Sim1Key_toFg]
  rw [support_map] at hx_fg
  rcases hx_fg with ⟨y, hy, rfl⟩
  exact keyIndActiveLengths_of_runKeyIndAdvG3Sim1Key S P b A y hy

/-- Every reachable final state of `runKeyInd1KeySim` for a `b`-bounded adversary satisfies
    `KeyIndActiveBounded`. -/
theorem runKeyInd1KeySim_mem_support_activeBounded
    (S : Setup) (P : Primitives) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b)
    (secb out : Bool) (finalSt : KeyIndState S)
    (hsupp : (secb, out, finalSt) ∈ support (runKeyInd1KeySim S P A.1)) :
    KeyIndActiveBounded P finalSt b.q_on :=
  (keyIndActiveLengths_of_runKeyInd1KeySim S P b A (secb, out, finalSt) hsupp).toBounded P

/-- Invariant relating `initKemRecs` and `recvKemRecs` in `KeyIndShCrState S` to `sendCount` and
    `base.spkBundles`. -/
@[expose] def ShCrKemRecsValid {S : Setup} (hst : KeyIndShCrState S) : Prop :=
  (∀ i ∈ hst.initKemRecs, i.sendIdx < hst.sendCount) ∧
  (∀ r ∈ hst.recvKemRecs, r.k < S.N_id ∧ r.j < S.N_recv ∧
    r.bIdx = spkSlotFlatIdx S (r.k, r.j) ∧
    ((r.k, r.j), r.pqspkPk, r.pqspkSk) ∈
      hst.base.spkBundles.map (fun (idx, b) => (idx, b.pqspkPk, b.pqspkSk)))

private theorem liftShCrBase_kemRecs_step {S : Setup} {Resp : Type}
    (m : StateT (KeyIndState S) ProbComp Resp) (hst : KeyIndShCrState S)
    (hV : ShCrKemRecsValid hst)
    (hSub : ∀ y ∈ support (m.run hst.base),
      ∀ p ∈ hst.base.spkBundles.map (fun (idx, b) => (idx, b.pqspkPk, b.pqspkSk)),
        p ∈ y.2.spkBundles.map (fun (idx, b) => (idx, b.pqspkPk, b.pqspkSk))) :
    ∀ x ∈ support ((liftKeyIndShCrBase m).run hst),
      ShCrKemRecsValid x.2 ∧ x.2.sendCount = hst.sendCount := by
  intro x hx
  simp only [liftKeyIndShCrBase, liftShCrBase, StateT.run, MonadAttach.mem_support_bind,
    support_pure, Set.mem_singleton_iff] at hx
  rcases hx with ⟨y, hy, rfl⟩
  refine ⟨⟨hV.1, fun r hr => ?_⟩, rfl⟩
  rcases hV.2 r hr with ⟨hk, hj, hb, hmem⟩
  exact ⟨hk, hj, hb, hSub y hy _ hmem⟩

theorem pqxdhKeyIndImpl_preserves_spkBundles_nonGen {S : Setup} (useRo : Bool)
    (P : Primitives) (q : KeyIndQuery S) (st : KeyIndState S)
    (hNotGen : ∀ u j, q ≠ .genSPK u j) (hNotRev : ∀ u j, q ≠ .revealSpkSk u j) :
    ∀ y ∈ support ((pqxdhKeyIndImpl useRo S P q).run st), y.2.spkBundles = st.spkBundles := by
  intro y hy; have h := mem_support_pqxdhKeyIndImpl useRo S P q st y hy
  cases q with
  | genSPK u j => exact absurd rfl (hNotGen u j)
  | revealSpkSk u j => exact absurd rfl (hNotRev u j)
  | initPrin _ => rcases h with hEq | ⟨_, _, _, hEq⟩ <;> simp [hEq]
  | genOPK _ _ _ => rcases h with hEq | ⟨_, _, hEq⟩ <;> simp [hEq]
  | corruptIK _ => rcases h with hEq | hEq <;> simp [hEq]
  | initiateOPK u i b | initiateNoOPK u i b =>
    rcases h with hEq | ⟨_, hy'⟩
    · rw [hEq]
    · rcases mem_support_runKeyIndInitiate useRo S P _ u b st y hy' with hEq | ⟨_, _, _, _, _, _, hEq⟩
      <;> simp [hEq]
  | acceptOPK _ _ _ _ | testSession _ | revealSessionKey _
  | acceptNoOPK _ _ _ _ | roQuery _ | registerKey _ | revealDhSecrets => exact h.2.1

theorem pqxdhKeyInd1KeyShCrImpl_activeStep (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndShCrState S) (hV : ShCrKemRecsValid hst) :
    ∀ x ∈ support ((pqxdhKeyInd1KeyShCrImpl false S P q).run hst),
      ShCrKemRecsValid x.2 ∧
      (if isKeyIndSendQuery (.inr q) then x.2.sendCount ≤ hst.sendCount + 1
       else x.2.sendCount = hst.sendCount) := by
  have hInitStep : ∀ (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
      (x : KeyIndResponse × KeyIndShCrState S),
      x ∈ support ((runShCrInitiate2 P KeyIndState.principals KeyIndResponse.noneResp
        (preCheckKeyInd S P sid u bundle) sid bundle
        (finishKeyIndBase S P sid bundle)).run hst) →
      ShCrKemRecsValid x.2 ∧ x.2.sendCount ≤ hst.sendCount + 1 := by
    intro sid u bundle x hx
    rcases mem_support_runShCrInitiate2 P KeyIndState.principals KeyIndResponse.noneResp
        (preCheckKeyInd S P sid u bundle) sid bundle
        (finishKeyIndBase S P sid bundle) hst x hx with
      ⟨rfl, _⟩ | ⟨uInfo, _, _, rfl | ⟨ekASk, ss, kemCt, out, hout, rfl⟩⟩
    · exact ⟨hV, Nat.le_succ _⟩
    · exact ⟨⟨fun i hi => Nat.lt_succ_of_lt (hV.1 i hi), hV.2⟩, le_rfl⟩
    · have hsend := applyShCrFinish_send sid bundle.pqspkB ss kemCt hst out
      refine ⟨⟨fun i hi => ?_, fun r hr => ?_⟩, by omega⟩
      · rcases hsend.2 i hi with hi_old | ⟨_, _, _, _⟩
        · have := hV.1 i hi_old; omega
        · have := hsend.1; omega
      · have hbase_spk : (SignalPqxdh.Security.RoKem.applyShCrFinish sid bundle.pqspkB ss kemCt
            hst out).2.base.spkBundles = hst.base.spkBundles := by
          rcases out with ⟨resp, none | base'⟩
          · rfl
          · exact finishKeyIndBase_spkBundles S P sid bundle uInfo ekASk ss kemCt hst.base
              (resp, some base') hout base' rfl
        have hr' : r ∈ hst.recvKemRecs := by rcases out with ⟨_, none | _⟩ <;> exact hr
        rcases hV.2 r hr' with ⟨hk, hj, hb, hmem⟩
        exact ⟨hk, hj, hb, hbase_spk.symm ▸ hmem⟩
  have hAccStep : ∀ (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
      (m : StateT (KeyIndState S) ProbComp KeyIndResponse)
      (hm : ∀ y ∈ support (m.run hst.base), y.2.spkBundles = hst.base.spkBundles)
      (x : KeyIndResponse × KeyIndShCrState S),
      x ∈ support ((runShCrAcceptGeneric P KeyIndState.spkBundles isNoneKeyIndResp m k j hdr).run
        hst) →
      ShCrKemRecsValid x.2 ∧ x.2.sendCount = hst.sendCount := by
    intro k j hdr m hm x hx; unfold runShCrAcceptGeneric at hx
    simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hx
    rcases hx with ⟨y, hy, hx⟩
    have hy_step := liftShCrBase_kemRecs_step m hst hV (fun z hz p hp => hm z hz ▸ hp) y hy
    rcases mem_support_recordAcceptKemGeneric P KeyIndState.spkBundles isNoneKeyIndResp
        k j hdr y.1 y.2 x hx with rfl | ⟨idxPair, bEntry, _, hfind, _, rfl⟩
    · exact hy_step
    · refine ⟨⟨hy_step.1.1, fun r hr => ?_⟩, hy_step.2⟩
      rcases List.mem_cons.mp hr with rfl | hr_old
      · have hmem_b := List.mem_of_find?_eq_some hfind
        rw [beq_iff_eq.mp (List.find?_eq_some_iff_append.mp hfind).1] at hmem_b
        exact ⟨k.isLt, j.isLt, rfl, List.mem_map_of_mem hmem_b⟩
      · exact hy_step.1.2 r hr_old
  intro x hx
  cases q with
  | initPrin u =>
    simpa [isKeyIndSendQuery] using liftShCrBase_kemRecs_step
      (pqxdhKeyIndImpl1KeyRo S P (.initPrin u)) hst hV
      (fun y hy p hp => pqxdhKeyIndImpl1KeyRo_initPrin_preserves_spkBundles S P u hst.base y hy ▸ hp)
      x hx
  | genSPK u j =>
    dsimp only [pqxdhKeyInd1KeyShCrImpl, pqxdhKeyIndShCrImpl] at hx
    rw [runShCrGenSPKGeneric_false_run] at hx
    simpa [isKeyIndSendQuery] using liftShCrBase_kemRecs_step _ hst hV (fun y hy p hp => by
      rcases mem_support_genSpkBaseGeneric P KeyIndState.principals KeyIndState.spkBundles
          (fun st bs => { st with spkBundles := bs })
          KeyIndResponse.noneResp KeyIndResponse.bundleResp u j hst.base y hy with
        rfl | ⟨_, _, _, _, _, _, _, rfl⟩
      · exact hp
      · exact List.mem_cons_of_mem _ hp) x hx
  | initiateOPK u i bundle =>
    dsimp only [pqxdhKeyInd1KeyShCrImpl, pqxdhKeyIndShCrImpl] at hx
    cases hNone : bundle.opkB?.isNone <;> rw [hNone] at hx
    · simp only [Bool.false_eq_true, ↓reduceIte] at hx
      simpa [isKeyIndSendQuery] using hInitStep (.sendOPK u i) u bundle x hx
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact ⟨hV, by simp [isKeyIndSendQuery]⟩
  | initiateNoOPK u i bundle =>
    dsimp only [pqxdhKeyInd1KeyShCrImpl, pqxdhKeyIndShCrImpl] at hx
    cases hSome : bundle.opkB?.isSome <;> rw [hSome] at hx
    · simp only [Bool.false_eq_true, ↓reduceIte] at hx
      simpa [isKeyIndSendQuery] using hInitStep (.sendNoOPK u i) u bundle x hx
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact ⟨hV, by simp [isKeyIndSendQuery]⟩
  | acceptOPK k j o hdr =>
    simpa [isKeyIndSendQuery] using hAccStep k j hdr _
      (pqxdhKeyIndImpl_preserves_spkBundles_nonGen true P _ hst.base
        (fun _ _ h => by cases h) (fun _ _ h => by cases h)) x hx
  | acceptNoOPK k j l hdr =>
    simpa [isKeyIndSendQuery] using hAccStep k j hdr _
      (pqxdhKeyIndImpl_preserves_spkBundles_nonGen true P _ hst.base
        (fun _ _ h => by cases h) (fun _ _ h => by cases h)) x hx
  | revealSpkSk u j =>
    simpa [isKeyIndSendQuery] using liftShCrBase_kemRecs_step
      (pqxdhKeyIndImpl true S P (.revealSpkSk u j)) hst hV (fun y hy p hp => by
        rcases mem_support_pqxdhKeyIndImpl true S P (.revealSpkSk u j) hst.base y hy with hEq | hEq
        · rwa [hEq]
        · rw [hEq]; dsimp only
          have hm : (hst.base.spkBundles.map (fun (idx, b) =>
              if idx == (u.val, j.val) then (idx, { b with revealed := true }) else (idx, b))).map
              (fun (idx, b) => (idx, b.pqspkPk, b.pqspkSk)) =
              hst.base.spkBundles.map (fun (idx, b) => (idx, b.pqspkPk, b.pqspkSk)) := by
            rw [List.map_map]
            exact List.map_congr_left fun ⟨_, _⟩ _ => by simp only [Function.comp_def]; split_ifs <;> rfl
          rwa [hm]) x hx
  | corruptIK _ | genOPK _ _ _ | testSession _ | revealSessionKey _
  | registerKey _ | roQuery _ | revealDhSecrets =>
    simpa [isKeyIndSendQuery] using liftShCrBase_kemRecs_step _ hst hV
      (fun y hy p hp => pqxdhKeyIndImpl_preserves_spkBundles_nonGen true P _ hst.base
        (fun _ _ h => by cases h) (fun _ _ h => by cases h) y hy ▸ hp) x hx

private theorem runKeyInd1KeyShCrSim_kemRecs_and_send
    (S : Setup) (P : Primitives) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b)
    (secb out : Bool) (finalHst : KeyIndShCrState S)
    (hsupp : (secb, out, finalHst) ∈ support (runKeyInd1KeyShCrSim S P A.1)) :
    ShCrKemRecsValid finalHst ∧ finalHst.sendCount ≤ activeSendCount S b.q_on := by
  simp only [runKeyInd1KeyShCrSim, MonadAttach.mem_support_bind, support_pure,
    Set.mem_singleton_iff] at hsupp
  rcases hsupp with ⟨_, _, ⟨_, _⟩, hmem, heq⟩
  rcases Prod.mk.inj heq with ⟨rfl, heq2⟩
  rcases Prod.mk.inj heq2 with ⟨rfl, rfl⟩
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyInd1KeyShCrImpl false S P
  have hInitV : ShCrKemRecsValid ({ base := KeyIndState.empty S secb } : KeyIndShCrState S) :=
    ⟨fun _ h => False.elim (List.not_mem_nil h), fun _ h => False.elim (List.not_mem_nil h)⟩
  have hSend := simulateQ_count_le_of_queryBound impl isKeyIndSendQuery ShCrKemRecsValid
    (fun s => s.sendCount)
    (fun t s hs z hz => by
      cases t with
      | inl _ =>
        simp only [impl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
          QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
        rcases hz with ⟨_, _, rfl⟩; exact ⟨hs, by simp [isKeyIndSendQuery]⟩
      | inr gq => exact pqxdhKeyInd1KeyShCrImpl_activeStep S P gq s hs z hz)
    A.1.run S.N_send_tot S.N_send_tot A.2.2.1
    { base := KeyIndState.empty S secb } hInitV (by simp) (out, finalHst) hmem
  have hOn := (simulateQ_count_le_of_queryBound impl isKeyIndOnlineQuery ShCrKemRecsValid
    (fun s => s.sendCount)
    (fun t s hs z hz => by
      cases t with
      | inl _ =>
        simp only [impl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
          QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
        rcases hz with ⟨_, _, rfl⟩; exact ⟨hs, by simp [isKeyIndOnlineQuery]⟩
      | inr gq =>
        have hst_step := pqxdhKeyInd1KeyShCrImpl_activeStep S P gq s hs z hz
        refine ⟨hst_step.1, ?_⟩
        by_cases hsend : isKeyIndSendQuery (.inr gq)
        · have hon : isKeyIndOnlineQuery (.inr gq) := by
            cases gq <;> simp [isKeyIndSendQuery, isKeyIndOnlineQuery] at hsend ⊢
          simpa [hsend, hon] using hst_step.2
        · have hcnt : z.2.sendCount = s.sendCount := by simpa [hsend] using hst_step.2
          split_ifs <;> omega)
    A.1.run b.q_on b.q_on A.2.2.2.2.2
    { base := KeyIndState.empty S secb } hInitV (by simp) (out, finalHst) hmem).2
  exact ⟨hSend.1, Nat.le_min.mpr ⟨hOn, hSend.2⟩⟩

/-- Every reachable final state of `runKeyInd1KeyShCrSim` satisfies `KeyIndActiveBounded` and
    `sendCount ≤ activeSendCount S b.q_on`. -/
theorem runKeyInd1KeyShCrSim_mem_support_activeBounded
    (S : Setup) (P : Primitives) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b)
    (secb out : Bool) (finalHst : KeyIndShCrState S)
    (hsupp : (secb, out, finalHst) ∈ support (runKeyInd1KeyShCrSim S P A.1)) :
    KeyIndActiveBounded P finalHst.base b.q_on ∧
      finalHst.sendCount ≤ activeSendCount S b.q_on :=
  ⟨(keyIndActiveLengths_of_runKeyInd1KeyShCrSim S P b A (secb, out, finalHst) hsupp).toBounded P,
   (runKeyInd1KeyShCrSim_kemRecs_and_send S P b A secb out finalHst hsupp).2⟩

/-- Creation-order active-count bounds on `initKemRecs` and `recvKemRecs` in
    `runKeyInd1KeyShCrSim`. -/
theorem runKeyInd1KeyShCrSim_mem_support_kemRecs_active
    (S : Setup) (P : Primitives) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b)
    (secb out : Bool) (finalHst : KeyIndShCrState S)
    (hsupp : (secb, out, finalHst) ∈ support (runKeyInd1KeyShCrSim S P A.1)) :
    (∀ i ∈ finalHst.initKemRecs, i.sendIdx < activeSendCount S b.q_on) ∧
    (∀ r ∈ finalHst.recvKemRecs,
      r.k < S.N_id ∧ r.j < S.N_recv ∧ r.bIdx = spkSlotFlatIdx S (r.k, r.j) ∧
      ∃ spkOrd < activeSpkCount S b.q_on, ∃ bEntry,
        finalHst.base.spkBundles.reverse[spkOrd]? = some ((r.k, r.j), bEntry) ∧
        bEntry.pqspkPk = r.pqspkPk ∧ bEntry.pqspkSk = r.pqspkSk) := by
  have hBase := (keyIndActiveLengths_of_runKeyInd1KeyShCrSim S P b A
    (secb, out, finalHst) hsupp).toBounded P
  rcases runKeyInd1KeyShCrSim_kemRecs_and_send S P b A secb out finalHst hsupp with ⟨hV, hSend⟩
  refine ⟨fun i hi => Nat.lt_of_lt_of_le (hV.1 i hi) hSend, fun r hr => ?_⟩
  rcases hV.2 r hr with ⟨hk, hj, hb, hmem_map⟩
  rcases List.mem_map.mp hmem_map with ⟨⟨idx, bEntry⟩, hmem_b, heq_b⟩
  rcases Prod.mk.inj heq_b with ⟨hidx, heq_pk⟩
  rcases Prod.mk.inj heq_pk with ⟨hpk, hsk⟩
  subst hidx
  have hmem_rev : ((r.k, r.j), bEntry) ∈ finalHst.base.spkBundles.reverse :=
    List.mem_reverse.mpr hmem_b
  rcases List.mem_iff_getElem.mp hmem_rev with ⟨spkOrd, hlt_rev, hget⟩
  have hlt_act : spkOrd < activeSpkCount S b.q_on := by
    rw [List.length_reverse] at hlt_rev
    exact Nat.lt_of_lt_of_le hlt_rev hBase.spkBundles_le
  exact ⟨hk, hj, hb, spkOrd, hlt_act, bEntry,
    by rw [List.getElem?_eq_getElem hlt_rev, hget], hpk, hsk⟩

end

end Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveLengths
