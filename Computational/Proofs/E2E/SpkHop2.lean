/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SpkHop2A
public import Computational.Proofs.E2E.SpkHop2Red
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins

@[expose] public section

/-!
# Hops 1 and 3 of the Leaked-SPK Session Chain and Hop 2 Combiner

Identifies the `sessionSchemeFixedSpk` and `sessionSchemeU` games with the real `extractPRF`
branches of `spkLeakRed` and `spkLeakRedU`, and combines Hops 1–3 with the 9-hybrid Hop 2 chain.
-/

open OracleComp OracleSpec ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.SM CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
  CryptoGames.LibsignalSession CryptoGames.CKA CryptoGames.MACScheme CryptoGames.HKDF
  CryptoGames.HMAC CBC CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E.Relabel CryptoVerification.E2E.Relabel.GameEq

namespace SpkHop2

open CryptoGames.LibsignalSM.Proofs
open CryptoVerification.E2E.Relabel

set_option linter.unusedSectionVars false

variable {Pt : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt]
variable {PQC : Type} [SampleableType PQC] {ℓ : ℕ}

theorem mapSt_accept_of_patch_eq
    (rk0 : BitVec 256) (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (Q : Party) (st' : GhostState Bytes) (hpatch : patchPartySpk rk0 st' = st') (pos : SM.Pos) :
    (GameEq.mapSt (patchPartySpk rk0) st).accept Q st' pos =
      GameEq.mapSt (patchPartySpk rk0) (st.accept Q st' pos) := by
  conv_lhs => rw [← hpatch]
  exact GameEq.mapSt_accept (patchPartySpk rk0) st Q st' pos

theorem deliverSpk_pure_eq
    (P : Params Bytes PQC) (hcodec : P.codec = protoSignalCodec)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hz : ∀ x, Dh.dh x 0 = 0)
    (rk0 ck0 s alice pqr : BitVec 256)
    (x : Party × Bytes)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (hs : SpkStateInv P decT encT ck0 s alice pqr st) :
    (SM.deliverR (sessionSchemeU P ℓ) (configRefuseEarlyBobCorr decT encT) x).run
        (GameEq.mapSt (patchPartySpk rk0) st) =
      Prod.map id (GameEq.mapSt (patchPartySpk rk0)) <$>
        simulateQ (purePrfImpl P.C.F encPt rk0)
          ((deliverSpk P ℓ Dh encT decT s x).run st) := by
  rcases x with ⟨Q, c⟩
  unfold deliverSpk SM.deliverR configRefuseEarlyBobCorr configR1OnCurve configR1 SM.Config.h1
  simp only [StateT.run_bind, StateT.run_get, pure_bind, GameEq.mapSt_win, GameEq.mapSt_inTransit]
  cases hwin : st.win
  · cases htr : st.inTransit Q.other c with
    | none => simp
    | some r =>
      obtain ⟨hpos, horc⟩ := inTransit_spkStateInv hs htr
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and, StateT.run_bind,
        stateT_lift_run, StateT.run_monadLift, bind_assoc, pure_bind, map_eq_bind_pure_comp,
        simulateQ_bind, simulateQ_purePrfImpl_liftM]
      congr 1
      funext rc
      rw [simulateQ_purePrfImpl_receiveSpk P hcodec Dh encPt encT decT hX hz rk0 ck0 s alice pqr
        st hs Q c horc rc]
      simp only [pure_bind, GameEq.mapSt_st, GameEq.mapSt_chall]
      cases hrec : (sessionSchemeU P ℓ).receive (patchPartySpk rk0 (st.st Q)) c rc with
      | none => simp
      | some v =>
        rcases v with ⟨st', t', i', m'⟩
        obtain ⟨hpatch, _, _⟩ := spkStateInv_accept_receive P rk0 hs Q c rc st' t' i' m' hrec
          r.pos (fun _ _ _ => hpos)
        simp [mapSt_accept_of_patch_eq rk0 st Q st' hpatch r.pos]
  · simp

theorem deliverSpk_pure_preserve
    (P : Params Bytes PQC) (hcodec : P.codec = protoSignalCodec)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hz0 : ∀ x, Dh.dh x 0 = 0)
    (rk0 ck0 s alice pqr : BitVec 256)
    (x : Party × Bytes)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (hs : SpkStateInv P decT encT ck0 s alice pqr st) :
    ∀ z ∈ support (simulateQ (purePrfImpl P.C.F encPt rk0)
        ((deliverSpk P ℓ Dh encT decT s x).run st)),
      SpkStateInv P decT encT ck0 s alice pqr z.2 := by
  rcases x with ⟨Q, c⟩
  intro z hz
  unfold deliverSpk at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  cases hwin : st.win
  · simp only [hwin, Bool.false_eq_true, ↓reduceIte] at hz
    cases htr : st.inTransit Q.other c with
    | none =>
      simp only [htr, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hs
    | some r =>
      obtain ⟨hpos, horc⟩ := inTransit_spkStateInv hs htr
      simp only [htr, StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind,
        simulateQ_bind, simulateQ_purePrfImpl_liftM] at hz
      rw [MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨rc, _, hz⟩
      rw [simulateQ_purePrfImpl_receiveSpk P hcodec Dh encPt encT decT hX hz0 rk0 ck0 s alice pqr
        st hs Q c horc rc] at hz
      simp only [pure_bind] at hz
      cases hrec : (sessionSchemeU P ℓ).receive (patchPartySpk rk0 (st.st Q)) c rc with
      | none =>
        simp only [hrec, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hs
      | some v =>
        rcases v with ⟨st', t', i', m'⟩
        simp only [hrec, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact (spkStateInv_accept_receive P rk0 hs Q c rc st' t' i' m' hrec
          r.pos (fun _ _ _ => hpos)).2.2
  · simp only [hwin, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz; exact hs

theorem injectSpk_pure_eq
    (P : Params Bytes PQC) (hcodec : P.codec = protoSignalCodec)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hz : ∀ x, Dh.dh x 0 = 0)
    (qep : ℕ) (rk0 ck0 s alice pqr : BitVec 256)
    (x : Party × Bytes)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (hs : SpkStateInv P decT encT ck0 s alice pqr st) :
    (SM.injectR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x).run
        (GameEq.mapSt (patchPartySpk rk0) st) =
      Prod.map id (GameEq.mapSt (patchPartySpk rk0)) <$>
        simulateQ (purePrfImpl P.C.F encPt rk0)
          ((injectSpk P ℓ Dh encT decT qep s x).run st) := by
  rcases x with ⟨Q, c⟩
  unfold injectSpk SM.injectR configRefuseEarlyBobCorr configR1OnCurve configR1 SM.Config.h1
  simp only [StateT.run_bind, StateT.run_get, pure_bind, GameEq.mapSt_win,
    GameEq.mapSt_inTransit, GameEq.mapSt_safeInj]
  by_cases hcond : (st.win || (st.inTransit Q.other c).isSome || !st.safeInj 3 ||
      !ratchetKeyAdmissible protoSignalCodec decT encT c) = true
  · simp [hcond]
  · have horc : ratchetKeyAdmissible protoSignalCodec decT encT c = true := by
      revert hcond
      cases ratchetKeyAdmissible protoSignalCodec decT encT c <;> simp
    simp only [hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run,
      StateT.run_monadLift, bind_assoc, pure_bind, map_eq_bind_pure_comp,
      simulateQ_bind, simulateQ_purePrfImpl_liftM]
    congr 1
    funext rc
    rw [simulateQ_purePrfImpl_receiveSpk P hcodec Dh encPt encT decT hX hz rk0 ck0 s alice pqr
      st hs Q c horc rc]
    simp only [pure_bind, GameEq.mapSt_st]
    cases hrec : (sessionSchemeU P ℓ).receive (patchPartySpk rk0 (st.st Q)) c rc with
    | none => simp
    | some v =>
      rcases v with ⟨st', t', i', m'⟩
      obtain ⟨hpatch, _, _⟩ := spkStateInv_accept_receive P rk0 hs Q c rc st' t' i' m' hrec
        ⟨Q.other, t', i'⟩ (fun _ _ ht1 => by dsimp; omega)
      dsimp only
      by_cases hqep : qep + 1 < t'
      · simp [hqep]
      · simp only [hqep, ↓reduceIte, GameEq.mapSt_trivial]
        by_cases htriv : st.trivial 3 ⟨Q.other, t', i'⟩ = true
        · simp [htriv, mapSt_accept_of_patch_eq rk0 st Q st' hpatch ⟨Q.other, t', i'⟩]
        · simp [htriv, GameEq.mapSt]

theorem injectSpk_pure_preserve
    (P : Params Bytes PQC) (hcodec : P.codec = protoSignalCodec)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hz0 : ∀ x, Dh.dh x 0 = 0)
    (qep : ℕ) (rk0 ck0 s alice pqr : BitVec 256)
    (x : Party × Bytes)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (hs : SpkStateInv P decT encT ck0 s alice pqr st) :
    ∀ z ∈ support (simulateQ (purePrfImpl P.C.F encPt rk0)
        ((injectSpk P ℓ Dh encT decT qep s x).run st)),
      SpkStateInv P decT encT ck0 s alice pqr z.2 := by
  rcases x with ⟨Q, c⟩
  intro z hz
  unfold injectSpk at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hcond : (st.win || (st.inTransit Q.other c).isSome || !st.safeInj 3 ||
      !ratchetKeyAdmissible protoSignalCodec decT encT c) = true
  · simp only [hcond, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz; exact hs
  · have horc : ratchetKeyAdmissible protoSignalCodec decT encT c = true := by
      revert hcond
      cases ratchetKeyAdmissible protoSignalCodec decT encT c <;> simp
    simp only [hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run,
      bind_assoc, pure_bind, simulateQ_bind, simulateQ_purePrfImpl_liftM] at hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨rc, _, hz⟩
    rw [simulateQ_purePrfImpl_receiveSpk P hcodec Dh encPt encT decT hX hz0 rk0 ck0 s alice pqr
      st hs Q c horc rc] at hz
    simp only [pure_bind] at hz
    cases hrec : (sessionSchemeU P ℓ).receive (patchPartySpk rk0 (st.st Q)) c rc with
    | none =>
      simp only [hrec, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hs
    | some v =>
      rcases v with ⟨st', t', i', m'⟩
      simp only [hrec] at hz
      split at hz
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hs
      · split at hz
        · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact (spkStateInv_accept_receive P rk0 hs Q c rc st' t' i' m' hrec
            ⟨Q.other, t', i'⟩ (fun _ _ ht1 => by dsimp; omega)).2.2
        · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact spkStateInv_with_win hs true

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem corrR_spk_eq
    (P : Params Bytes PQC)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (rk0 ck0 s alice pqr : BitVec 256)
    (Q : Party)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (hs : SpkStateInv P decT encT ck0 s alice pqr st) :
    (SM.corrR (configRefuseEarlyBobCorr decT encT) Q).run (GameEq.mapSt (patchPartySpk rk0) st) =
      Prod.map id (GameEq.mapSt (patchPartySpk rk0)) <$>
        (SM.corrR (configRefuseEarlyBobCorr decT encT) Q).run st := by
  unfold SM.corrR configRefuseEarlyBobCorr configR1OnCurve configR1
  simp only [StateT.run_bind, StateT.run_get, pure_bind, GameEq.mapSt_win, GameEq.mapSt_corrAllowed,
    GameEq.mapSt_inWindow, GameEq.mapSt_noSpkCorr, mapSt_noCorrB0, mapSt_noCorrBWin, Bool.true_and]
  by_cases hcond : (st.win || !st.corrAllowed Q || inWindow st Q ||
      !(noAliceCorrWhileAliceBelowEpoch10 st Q && noBobCorrInEpoch0 st Q && noBobCorrWhileAliceBelowEpoch10 st Q)) = true
  · simp only [hcond, ↓reduceIte]
    simp
  · have hok : noBobSendInEpoch0 st Q = true := by
      change noBobCorrInEpoch0 st Q = true
      revert hcond
      cases noBobCorrInEpoch0 st Q <;> simp
    have hpatch := (patchPartySpk_st_of_noBobEpoch0 hs rk0 Q hok).1
    simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    simp [GameEq.mapSt_afterCorr, hpatch]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem corrR_spk_preserve
    (P : Params Bytes PQC)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ck0 s alice pqr : BitVec 256)
    (Q : Party)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (hs : SpkStateInv P decT encT ck0 s alice pqr st) :
    ∀ z ∈ support ((SM.corrR (configRefuseEarlyBobCorr decT encT) Q).run st),
      SpkStateInv P decT encT ck0 s alice pqr z.2 := by
  intro z hz
  unfold SM.corrR at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  split at hz
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hs
  · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact spkStateInv_afterCorr hs Q

def spkPureStep
    (P : Params Bytes PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (rk0 s : BitVec 256) :
    QueryImpl (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes)
      (StateT (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) ProbComp) :=
  fun q st => simulateQ (purePrfImpl P.C.F encPt rk0)
    ((spkOracleImpl P ℓ Dh encT decT qep s q).run st)

omit [SampleableType Pt] in
@[simp] theorem spkPureStep_run
    (P : Params Bytes PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (rk0 s : BitVec 256)
    (q : (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes).Domain)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) :
    (spkPureStep P ℓ Dh encPt encT decT qep rk0 s q).run st =
      simulateQ (purePrfImpl P.C.F encPt rk0)
        ((spkOracleImpl P ℓ Dh encT decT qep s q).run st) := rfl

theorem spkPureStep_eq
    (P : Params Bytes PQC) (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hz : ∀ x, Dh.dh x 0 = 0)
    (qep : ℕ) (rk0 ck0 s alice pqr : BitVec 256)
    (q : (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes).Domain)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (hs : SpkStateInv P decT encT ck0 s alice pqr st) :
    (GameEq.fullImpl (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) q).run
        (GameEq.mapSt (patchPartySpk rk0) st) =
      Prod.map id (GameEq.mapSt (patchPartySpk rk0)) <$>
        (spkPureStep P ℓ Dh encPt encT decT qep rk0 s q).run st := by
  rcases q with u | ((((x | x) | x) | x) | Q)
  · simp only [spkPureStep_run, spkOracleImpl, stateT_lift_run, simulateQ_bind,
      simulateQ_oracleSpec_query, purePrfImpl, simulateQ_pure, GameEq.fullImpl, QueryImpl.add_apply]
    change ((liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>=
        fun x => pure (x, GameEq.mapSt (patchPartySpk rk0) st)) =
      Prod.map id (GameEq.mapSt (patchPartySpk rk0)) <$>
        ((liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun x => pure (x, st))
    simp [map_eq_bind_pure_comp, bind_assoc]
  · simp only [spkPureStep_run, spkOracleImpl, simulateQ_purePrfImpl_liftSpkGameM,
      GameEq.fullImpl, QueryImpl.add_apply, SM.oracleImplR]
    exact transmitR_spk_eq P hcodec hL Dh encPt encT decT hX hdec qep rk0 ck0 s alice pqr x st hs
  · simp only [spkPureStep_run, spkOracleImpl, simulateQ_purePrfImpl_liftSpkGameM,
      GameEq.fullImpl, QueryImpl.add_apply, SM.oracleImplR]
    exact challR_spk_eq P hcodec hL Dh encPt encT decT hX hdec qep rk0 ck0 s alice pqr x st hs
  · simp only [spkPureStep_run, spkOracleImpl, GameEq.fullImpl, QueryImpl.add_apply, SM.oracleImplR]
    exact deliverSpk_pure_eq P hcodec Dh encPt encT decT hX hz rk0 ck0 s alice pqr x st hs
  · simp only [spkPureStep_run, spkOracleImpl, GameEq.fullImpl, QueryImpl.add_apply, SM.oracleImplR]
    exact injectSpk_pure_eq P hcodec Dh encPt encT decT hX hz qep rk0 ck0 s alice pqr x st hs
  · simp only [spkPureStep_run, spkOracleImpl, simulateQ_purePrfImpl_liftSpkGameM,
      GameEq.fullImpl, QueryImpl.add_apply, SM.oracleImplR]
    exact corrR_spk_eq P decT encT rk0 ck0 s alice pqr Q st hs

theorem spkPureStep_preserve
    (P : Params Bytes PQC) (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hz : ∀ x, Dh.dh x 0 = 0)
    (qep : ℕ) (rk0 ck0 s alice pqr : BitVec 256)
    (q : (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes).Domain)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (hs : SpkStateInv P decT encT ck0 s alice pqr st) :
    ∀ z ∈ support ((spkPureStep P ℓ Dh encPt encT decT qep rk0 s q).run st),
      SpkStateInv P decT encT ck0 s alice pqr z.2 := by
  rcases q with u | ((((x | x) | x) | x) | Q)
  · intro z hz
    simp only [spkPureStep_run, spkOracleImpl, stateT_lift_run, simulateQ_bind,
      simulateQ_oracleSpec_query, purePrfImpl, simulateQ_pure] at hz
    change z ∈ support ((liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>=
      fun x => pure (x, st)) at hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨x, _, hzx⟩
    simp only [support_pure, Set.mem_singleton_iff] at hzx
    rw [hzx]
    exact hs
  · simp only [spkPureStep_run, spkOracleImpl, simulateQ_purePrfImpl_liftSpkGameM]
    exact transmitR_spk_preserve P hcodec hL Dh encPt encT decT hX hdec qep rk0 ck0 s alice pqr
      x st hs
  · simp only [spkPureStep_run, spkOracleImpl, simulateQ_purePrfImpl_liftSpkGameM]
    exact challR_spk_preserve P hcodec hL Dh encPt encT decT hX hdec qep rk0 ck0 s alice pqr x st hs
  · simp only [spkPureStep_run, spkOracleImpl]
    exact deliverSpk_pure_preserve P hcodec Dh encPt encT decT hX hz rk0 ck0 s alice pqr x st hs
  · simp only [spkPureStep_run, spkOracleImpl]
    exact injectSpk_pure_preserve P hcodec Dh encPt encT decT hX hz qep rk0 ck0 s alice pqr x st hs
  · simp only [spkPureStep_run, spkOracleImpl, simulateQ_purePrfImpl_liftSpkGameM]
    exact corrR_spk_preserve P decT encT ck0 s alice pqr Q st hs

theorem simulateQ_mapSt_run_eq {ι : Type}
    {ospec : OracleSpec.{0, 0} ι} {S₁ S₂ α : Type}
    (impl₁ : QueryImpl ospec (StateT S₁ ProbComp))
    (impl₂ : QueryImpl ospec (StateT S₂ ProbComp))
    (f : S₁ → S₂) (inv : S₁ → Prop)
    (heq : ∀ t s, inv s → (impl₂ t).run (f s) = Prod.map id f <$> (impl₁ t).run s)
    (hstep : ∀ t s, inv s → ∀ z ∈ support ((impl₁ t).run s), inv z.2)
    (oa : OracleComp ospec α) (s : S₁) (hs : inv s) :
    (simulateQ impl₂ oa).run (f s) =
      Prod.map id f <$> (simulateQ impl₁ oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rw [heq t s hs, bind_map_left, map_eq_bind_pure_comp, bind_assoc]
    apply GameEq.bind_congr_of_support
    intro z hz
    dsimp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
    rw [ih z.1 z.2 (hstep t s hs z hz), map_eq_bind_pure_comp]

/-! ## Hops 1 and 3 -/

theorem sample_prod_bind {α β γ : Type} [SampleableType α] [SampleableType β]
    (f : α × β → ProbComp γ) :
    (($ᵗ (α × β) : ProbComp (α × β)) >>= f) =
      (($ᵗ α : ProbComp α) >>= fun a => ($ᵗ β : ProbComp β) >>= fun b => f (a, b)) := by
  have hsel : ($ᵗ (α × β) : ProbComp (α × β)) =
      (Prod.mk <$> ($ᵗ α : ProbComp α) <*> ($ᵗ β : ProbComp β)) := rfl
  rw [hsel]
  simp only [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]

theorem evalDist_sample_keyU_swap (G : Bool → KeyU → ProbComp Bool) :
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b => ($ᵗ KeyU : ProbComp KeyU) >>= fun k => G b k] =
      𝒟[($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun rk0 =>
        ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun s =>
        ($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun ck0 =>
        ($ᵗ (BitVec 256 × BitVec 256) : ProbComp (BitVec 256 × BitVec 256)) >>= fun rest =>
          G b ((rk0, ck0), s, rest)] := by
  have hkeyU : ∀ b, (($ᵗ KeyU : ProbComp KeyU) >>= fun k => G b k) =
      (($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun rk0 =>
        ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun ck0 =>
        ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun s =>
        ($ᵗ (BitVec 256 × BitVec 256) : ProbComp (BitVec 256 × BitVec 256)) >>= fun rest =>
          G b ((rk0, ck0), s, rest)) := by
    intro b
    unfold KeyU
    rw [sample_prod_bind]
    simp only [sample_prod_bind]
  simp only [hkeyU]
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Bool) ($ᵗ (BitVec 256))]
  refine evalDist_bind_congr ($ᵗ (BitVec 256)) _ _ fun rk0 => ?_
  rw [← OracleComp.evalDist_bind_bind_swap ($ᵗ Bool) ($ᵗ (BitVec 256))]
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  exact OracleComp.evalDist_bind_bind_swap ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) _

theorem simulateQ_purePrfImpl_spkLeakRed
    (P : Params Bytes PQC) (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hz : ∀ x, Dh.dh x 0 = 0)
    (qep : ℕ) (rk0 s : BitVec 256)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) :
    simulateQ (purePrfImpl P.C.F encPt rk0) (spkLeakRed P Dh encPt encT decT qep s A) =
      (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let ck0 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        let rest ← ($ᵗ (BitVec 256 × BitVec 256) : ProbComp (BitVec 256 × BitVec 256))
        let (b', finalSt) ←
          (simulateQ (GameEq.fullImpl (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT)) A).run
            (SM.initState (sessionSchemeFixedSpk P ℓ s).sendPart ((rk0, ck0), rest) b)
        return (b == b' || finalSt.win)) := by
  unfold spkLeakRed
  simp only [simulateQ_bind, simulateQ_purePrfImpl_liftM]
  congr 1; funext b
  congr 1; funext ck0
  congr 1; funext rest
  rw [simulateQ_purePrfImpl_initAOracle P Dh hDh encPt encT hX rk0 ck0 s rest.1 rest.2,
    pure_bind, simulateQ_run_stateT]
  set initSt0 : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes :=
    { st := fun Q => match Q with
        | .A => P.initA ⟨rk0, ck0, s, rest.1, rest.2⟩
        | .B => P.initB ⟨0, ck0, s, rest.1, rest.2⟩,
      b := b }
  have hinit : SM.initState (sessionSchemeFixedSpk P ℓ s).sendPart ((rk0, ck0), rest) b =
      GameEq.mapSt (patchPartySpk rk0) initSt0 := by
    simp only [initSt0, SM.initState, SMSchemeR.sendPart, sessionSchemeFixedSpk, initKeysOfSampled, GameEq.mapSt,
      SM.GameState.mk.injEq, and_true]
    funext Q
    cases Q
    · exact (patchPartySpk_initA P rk0 ck0 s rest.1 rest.2).symm
    · exact (patchPartySpk_initB P rk0 ck0 s rest.1 rest.2).symm
  rw [hinit,
    simulateQ_mapSt_run_eq
      (spkPureStep P ℓ Dh encPt encT decT qep rk0 s)
      (GameEq.fullImpl (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT))
      (GameEq.mapSt (patchPartySpk rk0))
      (SpkStateInv P decT encT ck0 s rest.1 rest.2)
      (fun t st hs => spkPureStep_eq P hcodec hL Dh encPt encT decT hX hdec hz qep rk0 ck0 s
        rest.1 rest.2 t st hs)
      (fun t st hs => spkPureStep_preserve P hcodec hL Dh encPt encT decT hX hdec hz qep rk0 ck0 s
        rest.1 rest.2 t st hs)
      A initSt0 (spkStateInv_init P decT encT rk0 ck0 s rest.1 rest.2 b)]
  simp only [simulateQ_pure, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply,
    pure_bind, Prod.map_fst, Prod.map_snd, id_eq, GameEq.mapSt_win]
  rfl

/-- `SM.gameR` for `sessionSchemeFixedSpk` has the same distribution as the real `extractPRF` branch on `spkLeakRed`. -/
theorem evalDist_gameR_sessionSchemeSpk_eq_branch_false
    (P : Params Bytes PQC) (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hz : ∀ x, Dh.dh x 0 = 0)
    (qep : ℕ) (s : BitVec 256)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) :
    𝒟[SM.gameR (sessionSchemeFixedSpk P ℓ s) 3 qep (configRefuseEarlyBobCorr decT encT) A] =
      𝒟[MACScheme.branch (extractPRF P.C.F encPt) false
        (spkLeakRed P Dh encPt encT decT qep s A)] := by
  have horacle :
      SM.oracleImplR (sessionSchemeFixedSpk P ℓ s) 3 qep (configRefuseEarlyBobCorr decT encT) =
        SM.oracleImplR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) := rfl
  unfold MACScheme.branch SM.gameR SM.runR
  simp only [horacle,
    simulateQ_prf_false_run' P.C.F encPt _ (spkLeakRed P Dh encPt encT decT qep s A),
    simulateQ_purePrfImpl_spkLeakRed P hcodec hL Dh hDh encPt encT decT hX hdec hz qep _ s A,
    bind_assoc]
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ (BitVec 256)) ($ᵗ Bool)]
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  change 𝒟[($ᵗ ((BitVec 256 × BitVec 256) × (BitVec 256 × BitVec 256)) : ProbComp _) >>= _] = _
  rw [sample_prod_bind]
  simp only [sample_prod_bind]

/-- `SM.gameR` for `sessionSchemeU` has the same distribution as the real `extractPRF` branch on `spkLeakRedU spkLeakRed`. -/
theorem evalDist_gameR_sessionSchemeU_eq_branch_false_spkLeakRedU
    (P : Params Bytes PQC) (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hz : ∀ x, Dh.dh x 0 = 0)
    (qep : ℕ)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) :
    𝒟[SM.gameR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) A] =
      𝒟[MACScheme.branch (extractPRF P.C.F encPt) false
        (spkLeakRedU spkLeakRed P Dh encPt encT decT qep A)] := by
  have hinit : ∀ (rk0 ck0 s : BitVec 256) (rest : BitVec 256 × BitVec 256) (b : Bool),
      SM.initState (sessionSchemeFixedSpk P ℓ s).sendPart ((rk0, ck0), rest) b =
        SM.initState (sessionSchemeU P ℓ).sendPart ((rk0, ck0), s, rest) b :=
    fun _ _ _ _ _ => rfl
  unfold MACScheme.branch
  simp only [simulateQ_prf_false_run' P.C.F encPt]
  unfold spkLeakRedU SM.gameR SM.runR
  simp only [simulateQ_bind, simulateQ_purePrfImpl_liftM,
    simulateQ_purePrfImpl_spkLeakRed P hcodec hL Dh hDh encPt encT decT hX hdec hz qep,
    hinit, bind_assoc]
  exact evalDist_sample_keyU_swap _

/-! ## Hop 2 hybrid reductions -/

section Hop2RedK

omit [SampleableType Pt]

/-- Per-step collision supremum in `hop2CreateCollTerm`. -/
noncomputable def hop2CreateCollUnit (Dh : DHFun (BitVec 256) Pt) : ℝ≥0∞ :=
  ⨆ (T : Pt) (Q : Pt),
    if Q = 0 then 0 else 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {r | Dh.dh r T = Q}

theorem hop2CreateCollTerm_eq (Dh : DHFun (BitVec 256) Pt) (q : ℕ) :
    hop2CreateCollTerm Dh q =
      ((spkSwapHybridCount - 1 : ℕ) : ℝ≥0∞) * ((6 * q : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh := rfl

theorem hop2CreateCollTerm_eq_mul (Dh : DHFun (BitVec 256) Pt) (q : ℕ) :
    hop2CreateCollTerm Dh q =
      ((spkSwapHybridCount - 1 : ℕ) : ℝ≥0∞) * (((6 * q : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) := by
  rw [hop2CreateCollTerm_eq, mul_assoc]

theorem hop2RecvHalf_chall_fst_irrel
    (P : Params Bytes PQC) (k : ℕ) (r₁ r₂ : Ratchet.RootKey) (c : BitVec 256)
    (step : Pt → Hop2Comp Pt (BitVec 256)) :
    hop2RecvHalf (ℓ := ℓ) P ⟨k, (r₁, c), step⟩ = hop2RecvHalf (ℓ := ℓ) P ⟨k, (r₂, c), step⟩ := rfl

theorem hop2SendHalf_chall_fst_irrel
    (P : Params Bytes PQC) (k : ℕ) (r₁ r₂ : Ratchet.RootKey) (c : BitVec 256)
    (step : Pt → Hop2Comp Pt (BitVec 256)) :
    hop2SendHalf P ⟨k, (r₁, c), step⟩ = hop2SendHalf P ⟨k, (r₂, c), step⟩ := rfl

theorem hop2DH_chall_fst_irrel
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (k : ℕ) (r₁ r₂ : Ratchet.RootKey) (c : BitVec 256)
    (step : Pt → Hop2Comp Pt (BitVec 256)) :
    hop2DH (ℓ := ℓ) P Dh encT decT ⟨k, (r₁, c), step⟩ =
      hop2DH (ℓ := ℓ) P Dh encT decT ⟨k, (r₂, c), step⟩ := by
  funext idx coins g msg rc
  unfold hop2DH
  rw [hop2RecvHalf_chall_fst_irrel P k r₁ r₂ c step,
    hop2SendHalf_chall_fst_irrel P k r₁ r₂ c step]

theorem hop2Recv_chall_fst_irrel
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (k : ℕ) (r₁ r₂ : Ratchet.RootKey) (c : BitVec 256)
    (step : Pt → Hop2Comp Pt (BitVec 256)) :
    hop2Recv (ℓ := ℓ) P Dh encT decT ⟨k, (r₁, c), step⟩ =
      hop2Recv (ℓ := ℓ) P Dh encT decT ⟨k, (r₂, c), step⟩ := by
  funext g ct rc
  unfold hop2Recv
  rw [hop2DH_chall_fst_irrel P Dh encT decT k r₁ r₂ c step]

theorem hop2Deliver_chall_fst_irrel
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (s : BitVec 256) (k : ℕ) (r₁ r₂ : Ratchet.RootKey)
    (c : BitVec 256)
    (step : Pt → Hop2Comp Pt (BitVec 256)) :
    hop2Deliver (ℓ := ℓ) P Dh encT decT s ⟨k, (r₁, c), step⟩ =
      hop2Deliver (ℓ := ℓ) P Dh encT decT s ⟨k, (r₂, c), step⟩ := by
  funext y
  unfold hop2Deliver
  rw [hop2Recv_chall_fst_irrel P Dh encT decT k r₁ r₂ c step]

theorem hop2Inject_chall_fst_irrel
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) (k : ℕ) (r₁ r₂ : Ratchet.RootKey)
    (c : BitVec 256) (step : Pt → Hop2Comp Pt (BitVec 256)) :
    hop2Inject (ℓ := ℓ) P Dh encT decT qep s ⟨k, (r₁, c), step⟩ =
      hop2Inject (ℓ := ℓ) P Dh encT decT qep s ⟨k, (r₂, c), step⟩ := by
  funext y
  unfold hop2Inject
  rw [hop2Recv_chall_fst_irrel P Dh encT decT k r₁ r₂ c step]

theorem hop2Impl_chall_fst_irrel
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) (k : ℕ) (r₁ r₂ : Ratchet.RootKey)
    (c : BitVec 256) (step : Pt → Hop2Comp Pt (BitVec 256)) :
    hop2Impl (ℓ := ℓ) P Dh encT decT qep s ⟨k, (r₁, c), step⟩ =
      hop2Impl (ℓ := ℓ) P Dh encT decT qep s ⟨k, (r₂, c), step⟩ := by
  funext q
  rcases q with u | ((((y | y) | y) | y) | y)
  · rfl
  · rfl
  · rfl
  · exact congrFun (hop2Deliver_chall_fst_irrel P Dh encT decT s k r₁ r₂ c step) y
  · exact congrFun (hop2Inject_chall_fst_irrel P Dh encT decT qep s k r₁ r₂ c step) y
  · rfl

theorem hop2Game_chall_fst_irrel
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) (k : ℕ) (r₁ r₂ : Ratchet.RootKey)
    (c : BitVec 256) (step : Pt → Hop2Comp Pt (BitVec 256))
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) :
    hop2Game P ℓ Dh encT decT qep s ⟨k, (r₁, c), step⟩ A =
      hop2Game P ℓ Dh encT decT qep s ⟨k, (r₂, c), step⟩ A := by
  unfold hop2Game
  dsimp only
  rw [hop2Impl_chall_fst_irrel P Dh encT decT qep s k r₁ r₂ c step]

omit [Zero Pt] [DecidableEq Pt] in
theorem simulateQ_stateT_lift_run {σ α : Type}
    (impl : QueryImpl (unifSpec + prfSpec Pt (BitVec 256)) ProbComp)
    (m : Hop2Comp Pt α) (st : σ) :
    simulateQ impl ((StateT.lift m : StateT σ (Hop2Comp Pt) α).run st) =
      (simulateQ impl m >>= fun a => pure (a, st)) := by
  simp [StateT.lift, StateT.run]

theorem simulateQ_hop2RecvHalf_step_congr
    (impl : QueryImpl (unifSpec + prfSpec Pt (BitVec 256)) ProbComp)
    (P : Params Bytes PQC) (k : ℕ) (rc : Ratchet.RootKey × BitVec 256)
    (step₁ step₂ : Pt → Hop2Comp Pt (BitVec 256))
    (hstep : ∀ I, simulateQ impl (step₁ I) = simulateQ impl (step₂ I))
    (idx : Option ℕ) (rk : Ratchet.RootKey) (their : PublicKey) (our : PrivateKey) (Q : Pt)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt) :
    simulateQ impl ((hop2RecvHalf (ℓ := ℓ) P ⟨k, rc, step₁⟩ idx rk their our Q).run st) =
      simulateQ impl ((hop2RecvHalf (ℓ := ℓ) P ⟨k, rc, step₂⟩ idx rk their our Q).run st) := by
  unfold hop2RecvHalf
  cases idx with
  | none => rfl
  | some t =>
    dsimp only
    by_cases hQ : Q = 0
    · simp [hQ]
    · simp only [hQ, ↓reduceIte]
      by_cases ht : t ≤ k
      · simp [ht]
      · simp only [ht, ↓reduceIte, StateT.run_bind, simulateQ_bind,
          simulateQ_stateT_lift_run, hstep]

theorem simulateQ_hop2SendHalf_step_congr
    (impl : QueryImpl (unifSpec + prfSpec Pt (BitVec 256)) ProbComp)
    (P : Params Bytes PQC) (k : ℕ) (rc : Ratchet.RootKey × BitVec 256)
    (step₁ step₂ : Pt → Hop2Comp Pt (BitVec 256))
    (hstep : ∀ I, simulateQ impl (step₁ I) = simulateQ impl (step₂ I))
    (idx : Option ℕ) (rk : Ratchet.RootKey) (their : PublicKey) (our' : PrivateKey) (Q' : Pt) :
    simulateQ impl (hop2SendHalf P ⟨k, rc, step₁⟩ idx rk their our' Q') =
      simulateQ impl (hop2SendHalf P ⟨k, rc, step₂⟩ idx rk their our' Q') := by
  unfold hop2SendHalf
  cases idx with
  | none => rfl
  | some j =>
    dsimp only
    by_cases hQ : Q' = 0
    · simp [hQ]
    · simp only [hQ, ↓reduceIte]
      by_cases hjlt : j < k
      · simp [hjlt]
      · simp only [hjlt, ↓reduceIte]
        by_cases hjeq : j = k
        · simp [hjeq]
        · simp only [hjeq, ↓reduceIte, simulateQ_bind, hstep]

theorem simulateQ_hop2DH_step_congr
    (impl : QueryImpl (unifSpec + prfSpec Pt (BitVec 256)) ProbComp)
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (k : ℕ) (chall : Ratchet.RootKey × BitVec 256)
    (step₁ step₂ : Pt → Hop2Comp Pt (BitVec 256))
    (hstep : ∀ I, simulateQ impl (step₁ I) = simulateQ impl (step₂ I))
    (idx : Option ℕ) (coins : BitVec 256) (g : GhostState Bytes) (msg : SignalMessage)
    (rc : BitVec 256)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt) :
    simulateQ impl ((hop2DH (ℓ := ℓ) P Dh encT decT ⟨k, chall, step₁⟩ idx coins g msg rc).run st) =
      simulateQ impl
        ((hop2DH (ℓ := ℓ) P Dh encT decT ⟨k, chall, step₂⟩ idx coins g msg rc).run st) := by
  unfold hop2DH
  cases decT msg.senderRatchetKey with
  | none => rfl
  | some T =>
    dsimp only
    split
    · rfl
    · cases g.session.senderChain with
      | none => rfl
      | some sc =>
        dsimp only
        simp only [StateT.run_bind, simulateQ_bind]
        rw [simulateQ_hop2RecvHalf_step_congr impl P k chall step₁ step₂ hstep
          idx g.session.rootKey msg.senderRatchetKey sc.ratchetKey.privateKey (Dh.dh coins T) st]
        refine bind_congr fun r1 => ?_
        rcases r1 with ⟨o1, st1⟩
        cases o1 with
        | none => rfl
        | some v1 =>
          rcases v1 with ⟨idx1, rkM, ckR⟩
          dsimp only
          simp only [StateT.run_bind, simulateQ_bind, simulateQ_stateT_lift_run]
          rw [simulateQ_hop2SendHalf_step_congr impl P k chall step₁ step₂ hstep
            idx1 rkM msg.senderRatchetKey (KeyPair.generate P.C rc).privateKey (Dh.dh rc T)]

theorem simulateQ_hop2Recv_step_congr
    (impl : QueryImpl (unifSpec + prfSpec Pt (BitVec 256)) ProbComp)
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (k : ℕ) (chall : Ratchet.RootKey × BitVec 256)
    (step₁ step₂ : Pt → Hop2Comp Pt (BitVec 256))
    (hstep : ∀ I, simulateQ impl (step₁ I) = simulateQ impl (step₂ I))
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt) :
    simulateQ impl ((hop2Recv (ℓ := ℓ) P Dh encT decT ⟨k, chall, step₁⟩ g c rc).run st) =
      simulateQ impl ((hop2Recv (ℓ := ℓ) P Dh encT decT ⟨k, chall, step₂⟩ g c rc).run st) := by
  unfold hop2Recv
  cases SignalMessage.tryFrom P.codec c with
  | error _ => rfl
  | ok msg =>
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.2.idx g.party with
    | none => rfl
    | some t =>
      dsimp only
      split
      · exact simulateQ_hop2DH_step_congr impl P Dh encT decT k chall step₁ step₂ hstep
          (some t) (st.2.coins g.party) g msg rc st
      · rfl

theorem simulateQ_hop2Deliver_step_congr
    (impl : QueryImpl (unifSpec + prfSpec Pt (BitVec 256)) ProbComp)
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (s : BitVec 256) (k : ℕ) (chall : Ratchet.RootKey × BitVec 256)
    (step₁ step₂ : Pt → Hop2Comp Pt (BitVec 256))
    (hstep : ∀ I, simulateQ impl (step₁ I) = simulateQ impl (step₂ I))
    (y : Party × Bytes)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt) :
    simulateQ impl ((hop2Deliver (ℓ := ℓ) P Dh encT decT s ⟨k, chall, step₁⟩ y).run st) =
      simulateQ impl ((hop2Deliver (ℓ := ℓ) P Dh encT decT s ⟨k, chall, step₂⟩ y).run st) := by
  rcases y with ⟨Q, c⟩
  unfold hop2Deliver
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · rfl
  · cases st.1.inTransit Q.other c with
    | none => rfl
    | some r =>
      simp only [StateT.run_bind, simulateQ_bind, simulateQ_stateT_lift_run, bind_assoc, pure_bind]
      refine bind_congr fun rc => ?_
      rw [simulateQ_hop2Recv_step_congr impl P Dh encT decT k chall step₁ step₂ hstep (st.1.st Q)
        c rc st]

theorem simulateQ_hop2Inject_step_congr
    (impl : QueryImpl (unifSpec + prfSpec Pt (BitVec 256)) ProbComp)
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) (k : ℕ)
    (chall : Ratchet.RootKey × BitVec 256)
    (step₁ step₂ : Pt → Hop2Comp Pt (BitVec 256))
    (hstep : ∀ I, simulateQ impl (step₁ I) = simulateQ impl (step₂ I))
    (y : Party × Bytes)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt) :
    simulateQ impl ((hop2Inject (ℓ := ℓ) P Dh encT decT qep s ⟨k, chall, step₁⟩ y).run st) =
      simulateQ impl ((hop2Inject (ℓ := ℓ) P Dh encT decT qep s ⟨k, chall, step₂⟩ y).run st) := by
  rcases y with ⟨Q, c⟩
  unfold hop2Inject
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · rfl
  · simp only [StateT.run_bind, simulateQ_bind, simulateQ_stateT_lift_run, bind_assoc, pure_bind]
    refine bind_congr fun rc => ?_
    rw [simulateQ_hop2Recv_step_congr impl P Dh encT decT k chall step₁ step₂ hstep (st.1.st Q)
      c rc st]

theorem simulateQ_hop2Impl_step_congr
    (impl : QueryImpl (unifSpec + prfSpec Pt (BitVec 256)) ProbComp)
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) (k : ℕ)
    (chall : Ratchet.RootKey × BitVec 256)
    (step₁ step₂ : Pt → Hop2Comp Pt (BitVec 256))
    (hstep : ∀ I, simulateQ impl (step₁ I) = simulateQ impl (step₂ I))
    (q : (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes).Domain)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt) :
    simulateQ impl ((hop2Impl (ℓ := ℓ) P Dh encT decT qep s ⟨k, chall, step₁⟩ q).run st) =
      simulateQ impl ((hop2Impl (ℓ := ℓ) P Dh encT decT qep s ⟨k, chall, step₂⟩ q).run st) := by
  rcases q with u | ((((y | y) | y) | y) | y)
  · rfl
  · rfl
  · rfl
  · exact simulateQ_hop2Deliver_step_congr impl P Dh encT decT s k chall step₁ step₂ hstep y st
  · exact simulateQ_hop2Inject_step_congr impl P Dh encT decT qep s k chall step₁ step₂ hstep y st
  · rfl

theorem simulateQ_hop2Comp_step_congr {α : Type}
    (impl : QueryImpl (unifSpec + prfSpec Pt (BitVec 256)) ProbComp)
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) (k : ℕ)
    (chall : Ratchet.RootKey × BitVec 256)
    (step₁ step₂ : Pt → Hop2Comp Pt (BitVec 256))
    (hstep : ∀ I, simulateQ impl (step₁ I) = simulateQ impl (step₂ I))
    (comp : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) α)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt) :
    simulateQ impl
        ((simulateQ (hop2Impl (ℓ := ℓ) P Dh encT decT qep s ⟨k, chall, step₁⟩) comp).run st) =
      simulateQ impl
        ((simulateQ (hop2Impl (ℓ := ℓ) P Dh encT decT qep s ⟨k, chall, step₂⟩) comp).run st) := by
  induction comp using OracleComp.inductionOn generalizing st with
  | pure a => rfl
  | query_bind q m ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rw [simulateQ_hop2Impl_step_congr impl P Dh encT decT qep s k chall step₁ step₂ hstep q st]
    refine bind_congr fun x => ih x.1 x.2

theorem simulateQ_hop2Game_step_congr
    (impl : QueryImpl (unifSpec + prfSpec Pt (BitVec 256)) ProbComp)
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) (k : ℕ)
    (chall : Ratchet.RootKey × BitVec 256)
    (step₁ step₂ : Pt → Hop2Comp Pt (BitVec 256))
    (hstep : ∀ I, simulateQ impl (step₁ I) = simulateQ impl (step₂ I))
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) :
    simulateQ impl (hop2Game P ℓ Dh encT decT qep s ⟨k, chall, step₁⟩ A) =
      simulateQ impl (hop2Game P ℓ Dh encT decT qep s ⟨k, chall, step₂⟩ A) := by
  unfold hop2Game
  simp only [simulateQ_bind]
  refine bind_congr fun b => bind_congr fun ck0 => bind_congr fun x => bind_congr fun alice =>
    bind_congr fun pqr => bind_congr fun u1 => ?_
  rw [simulateQ_hop2Comp_step_congr impl P Dh encT decT qep s k chall step₁ step₂ hstep A]

omit [Zero Pt] [DecidableEq Pt] in
theorem purePrfImpl_eq_add (F : ShaCompress) (encPt : Pt → Bytes) (rk0 : BitVec 256) :
    purePrfImpl F encPt rk0 =
      QueryImpl.ofLift unifSpec ProbComp +
        (fun I => pure ((extractPRF F encPt).tag rk0 I) :
          QueryImpl (prfSpec Pt (BitVec 256)) ProbComp) := by
  funext t
  cases t <;> rfl

theorem uniform_prod (α β : Type) [SampleableType α] [SampleableType β] :
    ($ᵗ (α × β) : ProbComp (α × β)) =
      (do let a ← $ᵗ α; let b ← $ᵗ β; pure (a, b)) := by
  simp only [uniformSample, SampleableType.selectElem, seq_eq_bind_map, map_eq_bind_pure_comp,
    bind_assoc, pure_bind, Function.comp_apply]
  rfl

/-- Under `purePrfImpl`, `hop2PrfRedK` simulates `hop2PrgRedK` on an ideal challenge. -/
theorem hop2PrfRedK_purePrfImpl_eq
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) (k : ℕ)
    (rk : Ratchet.RootKey)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) :
    simulateQ (purePrfImpl P.C.F encPt rk) (hop2PrfRedK P ℓ Dh encT decT qep s k A) =
      (do
        let _r ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let ck ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        hop2PrgRedK P ℓ Dh encPt encT decT qep s k A (rk, ck)) := by
  unfold hop2PrfRedK hop2Unif
  rw [simulateQ_bind, simulateQ_purePrfImpl_liftM]
  congr 1
  funext r
  rw [simulateQ_bind, simulateQ_purePrfImpl_liftM]
  congr 1
  funext ck
  unfold hop2PrgRedK
  dsimp only
  rw [hop2Game_chall_fst_irrel P ℓ Dh encT decT qep s k r rk ck,
    ← purePrfImpl_eq_add P.C.F encPt rk]
  exact simulateQ_hop2Game_step_congr
    (purePrfImpl P.C.F encPt rk) P ℓ Dh encT decT qep s k (rk, ck)
    (fun I => evalQuery (Input := Pt) (Tag := BitVec 256) I)
    (fun I => pure ((extractPRF P.C.F encPt).tag rk I))
    (fun I => simulateQ_purePrfImpl_evalQuery P.C.F encPt rk I) A

theorem evalDist_hop2PrgRedK_ideal_eq_hop2PrfRedK_false
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) (k : ℕ)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) :
    𝒟[PRGScheme.prgIdealExperiment (hop2PrgRedK P ℓ Dh encPt encT decT qep s k A)] =
      𝒟[(extractPRF P.C.F encPt).branch false (hop2PrfRedK P ℓ Dh encT decT qep s k A)] := by
  unfold PRGScheme.prgIdealExperiment MACScheme.branch
  rw [uniform_prod Ratchet.RootKey (BitVec 256), bind_assoc]
  refine evalDist_bind_congr ($ᵗ Ratchet.RootKey) _ _ fun rk => ?_
  simp only [bind_assoc, pure_bind]
  rw [simulateQ_prf_false_run' P.C.F encPt rk (hop2PrfRedK P ℓ Dh encT decT qep s k A),
    hop2PrfRedK_purePrfImpl_eq, OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]

theorem prgReal_true_le {Seed Out : Type} [SampleableType Seed] [SampleableType Out]
    (G : PRGScheme Seed Out) (B : PRGScheme.PRGAdversary Out) :
    𝒟[G.prgRealExperiment B] {true} ≤
      G.prgAdvantage B + 𝒟[PRGScheme.prgIdealExperiment B] {true} := by
  unfold PRGScheme.prgAdvantage MeasureTheory.Measure.boolDist ENNReal.absDiff
  calc 𝒟[G.prgRealExperiment B] {true}
      ≤ (𝒟[G.prgRealExperiment B] {true} - 𝒟[PRGScheme.prgIdealExperiment B] {true}) +
          𝒟[PRGScheme.prgIdealExperiment B] {true} := le_tsub_add
    _ ≤ ((𝒟[G.prgRealExperiment B] {true} - 𝒟[PRGScheme.prgIdealExperiment B] {true}) +
          (𝒟[PRGScheme.prgIdealExperiment B] {true} - 𝒟[G.prgRealExperiment B] {true})) +
          𝒟[PRGScheme.prgIdealExperiment B] {true} := by
        gcongr
        exact le_self_add

theorem prfBranch_false_true_le {Key Input Tag : Type} [SampleableType Key]
    [DecidableEq Input] [SampleableType Tag]
    (mac : MACScheme Key Input Tag) (A : MACScheme.PRFAdversary Input Tag) :
    𝒟[mac.branch false A] {true} ≤
      mac.prfAdvantage A + 𝒟[mac.branch true A] {true} := by
  rw [MACScheme.prfAdvantage_eq_boolDist]
  unfold MeasureTheory.Measure.boolDist ENNReal.absDiff
  calc 𝒟[mac.branch false A] {true}
      ≤ (𝒟[mac.branch false A] {true} - 𝒟[mac.branch true A] {true}) +
          𝒟[mac.branch true A] {true} := le_tsub_add
    _ ≤ ((𝒟[mac.branch true A] {true} - 𝒟[mac.branch false A] {true}) +
          (𝒟[mac.branch false A] {true} - 𝒟[mac.branch true A] {true})) +
          𝒟[mac.branch true A] {true} := by
        gcongr
        exact le_add_self

end Hop2RedK

end SpkHop2

end CryptoVerification.E2E
