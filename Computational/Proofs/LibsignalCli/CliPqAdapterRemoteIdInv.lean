/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.CliPqAdapterDefs
import Computational.Proofs.E2E.BhAdapterIjHelpersV1Core
import Computational.Proofs.SignalPqxdh.Security.CollisionsB
import LibsignalBinary.Proofs.SignalSession.Closure.Version
import ProofLib.BV.WidthNorm
import VCVio.EvalDist.Monad.Basic

/-!
# E2E remote-identity invariant and `DEq` support transport

**Checked by Lean.** Proves preservation of `CliE2ERemoteIdInv` across `cliE2EDrvImplWith` and
`cliComposedAdapterImplWith`, together with `DEq` right-marginal support transport.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.constructorNameAsVariable false

open scoped ENNReal BigOperators
open ReductionDsl OracleComp OracleSpec MeasureTheory

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SignalSession

/-- Every promoted model instance in `σ_e2e` keeps Alice's `remoteIdentity = some d.idB` and
Bob's `remoteIdentity = some d.idA`. -/
def CliE2ERemoteIdInv {S : SignalPqxdh.Setup} {ℓ : ℕ} (σ_e2e : BHE2EDrvState S ℓ) : Prop :=
  ∀ d ∈ σ_e2e.insts, ∀ gs_m, d.gs = some gs_m →
    (gs_m.st .A).session.remoteIdentity = some d.idB ∧
    (gs_m.st .B).session.remoteIdentity = some d.idA

theorem cliE2ERemoteIdInv_init (S : SignalPqxdh.Setup) (ℓ : ℕ) (b : Bool) (secb : Bool) :
    CliE2ERemoteIdInv ({ b := b, st := SignalPqxdh.KeyIndState.empty S secb } : BHE2EDrvState S ℓ) :=
  fun _ h => False.elim (List.not_mem_nil h)

@[local simp] private theorem exec_pure_loc {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a) s = (.ok a, s) := rfl

@[local simp] private theorem exec_throw_loc {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl

@[local simp] private theorem exec_get_loc {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

@[local simp] private theorem exec_modifyGet_loc {σ α : Type} (f : σ → α × σ) (s : σ) :
    Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl

@[local simp] private theorem exec_bind_loc {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  unfold Mut.exec
  change (ExceptT.run (m >>= f)).run s = _
  rw [ExceptT.run_bind]
  simp only [StateT.run_bind]
  rcases (m.run).run s with ⟨r, s'⟩
  cases r <;> rfl

private theorem fromSessionState_remoteIdentity {PQ : Type} [Inhabited PQ]
    (st : SessionState PQ) :
    ((OutgoingTripleRatchet.fromSessionState (PQ := PQ)).exec st).2.remoteIdentity =
      st.remoteIdentity := by
  unfold OutgoingTripleRatchet.fromSessionState SessionState.takePqRatchetState
  simp only [exec_bind_loc, exec_get_loc]
  rcases st.senderChain with _ | sc
  · rfl
  · simp only [exec_bind_loc, exec_modifyGet_loc, exec_get_loc]
    split_ifs
    · simp only [exec_bind_loc, exec_throw_loc]
    · rcases st.remoteIdentity with _ | remote <;> rfl

private theorem messageEncrypt_remoteIdentity {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (codec : SignalMessageProtoCodec) (spqr : Spqr PQ PQC) (addrs : Option Bytes)
    (m : Bytes) (r : PQC) (st : SessionState PQ) :
    (SessionState.messageEncrypt C codec spqr addrs m r st).2.remoteIdentity =
      st.remoteIdentity := by
  unfold SessionState.messageEncrypt
  have h1 := fromSessionState_remoteIdentity st
  rcases hf : OutgoingTripleRatchet.fromSessionState.exec st with ⟨_ | session, taken⟩
  · rfl
  · rw [hf] at h1
    dsimp only
    rcases (OutgoingTripleRatchet.encrypt C codec spqr m (st.encryptAddresses addrs) r).exec session
      with ⟨_ | msg, session'⟩
    · rfl
    · exact h1

private theorem params_send_remoteIdentity {PQ PQC : Type} [Inhabited PQ]
    (P : Params PQ PQC) (g : GhostState PQ) (m : Bytes) (r : PQC) :
    (P.send g m r).1.session.remoteIdentity = g.session.remoteIdentity := by
  unfold Params.send
  have h := messageEncrypt_remoteIdentity P.C P.codec P.spqr (P.sendAddrs g.party) m r g.session
  rcases he : SessionState.messageEncrypt P.C P.codec P.spqr (P.sendAddrs g.party) m r g.session
    with ⟨_ | _, s'⟩
  · rfl
  · rw [he] at h; exact h

private theorem params_receive_remoteIdentity {PQ PQC : Type} [Inhabited PQ]
    (P : Params PQ PQC) (g g' : GhostState PQ) (c : Bytes) (rc : BitVec 256)
    {t i : ℕ} {pt : Bytes}
    (h : P.receive g c rc = some (g', t, i, pt)) :
    g'.session.remoteIdentity = g.session.remoteIdentity := by
  unfold Params.receive at h
  rcases htf : SignalMessage.tryFrom P.codec c with _ | msg
  · simp [htf] at h
  · rw [htf] at h; dsimp only at h
    rcases hd : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
        msg .whisper rc g.session with ⟨_ | pt', s'⟩
    · simp [hd] at h
    · rw [hd] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      have hrem := (Closure.Version.tryDecryptFromRecord_sessionVersion_remoteIdentity
        P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc g.session).2
      rw [hd] at hrem
      have hg' : g'.session = s' := by rw [← h.1]
      exact (congrArg SessionState.remoteIdentity hg').trans hrem

private theorem sessionSchemeSpk_send_remoteIdentity {PQ PQC : Type} [Inhabited PQ]
    (P : Params PQ PQC) (ℓ : ℕ) (spkCoins : BitVec 256)
    (g : GhostState PQ) (m : Plain ℓ) (r : PQC) :
    ((sessionSchemeFixedSpk P ℓ spkCoins).send g m r).1.session.remoteIdentity =
      g.session.remoteIdentity :=
  params_send_remoteIdentity P g m.toList r

private theorem sessionSchemeSpk_receive_remoteIdentity {PQ PQC : Type} [Inhabited PQ]
    (P : Params PQ PQC) (ℓ : ℕ) (spkCoins : BitVec 256)
    (g g' : GhostState PQ) (c : Bytes) (rc : BitVec 256)
    {t i : ℕ} {m' : Plain ℓ}
    (h : (sessionSchemeFixedSpk P ℓ spkCoins).receive g c rc = some (g', t, i, m')) :
    g'.session.remoteIdentity = g.session.remoteIdentity := by
  unfold sessionSchemeFixedSpk at h
  dsimp only at h
  rcases hr : P.receive g c rc with _ | ⟨g₁, t₁, i₁, pt⟩
  · simp [hr] at h
  · rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _, _, _⟩
    exact params_receive_remoteIdentity P g g₁ c rc hr

private theorem epMgmt_st {St Msg C : Type}
    (s s₁ : SM.GameState St Msg C) (Δ qep : ℕ) (P : Party) (bad : Bool)
    (h : s.epMgmt Δ qep P bad = some s₁) :
    s₁.st = s.st := by
  unfold SM.GameState.epMgmt at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;> rfl

private theorem oracleImplR_sessionSchemeSpk_preserves_remoteIdentity
    {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (gs : SM.GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hA : (gs.st .A).session.remoteIdentity = some idB)
    (hB : (gs.st .B).session.remoteIdentity = some idA) :
    ∀ p ∈ support ((SM.oracleImplR
        (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
        (2 + 1) qep (configRefuseEarlyBobCorr decT encT) q).run gs),
      (p.2.st .A).session.remoteIdentity = some idB ∧
      (p.2.st .B).session.remoteIdentity = some idA := by
  set P_v1 := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  set sch := sessionSchemeFixedSpk P_v1 ℓ spkCoins
  set cfg := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT
  intro p hp
  rcases q with (((⟨P, m, r?⟩ | ⟨P, m0, m1, r?⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  ·
    change p ∈ support ((SM.transmitR sch (2 + 1) qep cfg ⟨P, m, r?⟩).run gs) at hp
    unfold SM.transmitR SM.transmitImpl at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    split_ifs at hp
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact ⟨hA, hB⟩
    · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
      by_cases hw : gs.win = true
      · simp only [hw, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
        subst hp; exact ⟨hA, hB⟩
      · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hp
        rcases hp with ⟨⟨r, bad⟩, _, hp⟩
        dsimp only at hp
        rcases hep : gs.epMgmt (2 + 1) qep P bad with _ | s₁
        · rw [hep] at hp
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
          subst hp; exact ⟨hA, hB⟩
        · rw [hep] at hp; dsimp only at hp
          have hst := epMgmt_st gs s₁ (2 + 1) qep P bad hep
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hp
          subst hp
          cases P <;> simp [SM.GameState.record, SMSchemeR.sendPart, sch, hst,
            sessionSchemeSpk_send_remoteIdentity, hA, hB]
  ·
    change p ∈ support ((SM.challR sch (2 + 1) qep cfg ⟨P, m0, m1, r?⟩).run gs) at hp
    unfold SM.challR SM.challImpl at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    split_ifs at hp
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact ⟨hA, hB⟩
    · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
      by_cases hw : gs.win = true
      · simp only [hw, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
        subst hp; exact ⟨hA, hB⟩
      · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hp
        rcases hp with ⟨⟨r, bad⟩, _, hp⟩
        dsimp only at hp
        rcases hep : gs.epMgmt (2 + 1) qep P bad with _ | s₁
        · rw [hep] at hp
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
          subst hp; exact ⟨hA, hB⟩
        · rw [hep] at hp; dsimp only at hp
          have hst := epMgmt_st gs s₁ (2 + 1) qep P bad hep
          by_cases hch : (!s₁.safeCh (2 + 1) P || !cfg.base.challAllowedIn (s₁.epoch P)) = true
          · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
            subst hp; exact ⟨hA, hB⟩
          · simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
              StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hp
            subst hp
            cases P <;> simp [SM.GameState.record, SMSchemeR.sendPart, sch, hst,
              sessionSchemeSpk_send_remoteIdentity, hA, hB]
  ·
    change p ∈ support ((SM.deliverR sch cfg ⟨P, c⟩).run gs) at hp
    unfold SM.deliverR at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    split_ifs at hp
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact ⟨hA, hB⟩
    · rcases htr : gs.inTransit P.other c with _ | r_tr
      · rw [htr] at hp
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
        subst hp; exact ⟨hA, hB⟩
      · rw [htr] at hp
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc,
          pure_bind, MonadAttach.mem_support_bind] at hp
        rcases hp with ⟨rc, _, hp⟩
        rcases hrcv : sch.receive (gs.st P) c rc with _ | ⟨st', t', i', m'⟩
        · rw [hrcv] at hp; dsimp only at hp
          split_ifs at hp <;>
            simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hp <;>
            subst hp <;> exact ⟨hA, hB⟩
        · rw [hrcv] at hp; dsimp only at hp
          have hrem := sessionSchemeSpk_receive_remoteIdentity P_v1 ℓ spkCoins _ _ c rc hrcv
          split_ifs at hp <;>
            simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hp <;>
            subst hp <;>
            cases P <;> simp [SM.GameState.accept, SM.GameState.delete, hrem, hA, hB]
  ·
    change p ∈ support ((SM.injectR sch (2 + 1) qep cfg ⟨P, c⟩).run gs) at hp
    rw [BhAdapterIjHelpersV1.injectR_run] at hp
    split_ifs at hp
    · simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact ⟨hA, hB⟩
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hp
      rcases hp with ⟨rc, _, rfl⟩
      unfold BhAdapterIjHelpersV1.injectPost
      rcases hrcv : sch.receive (gs.st P) c rc with _ | ⟨st', t', i', m'⟩
      · exact ⟨hA, hB⟩
      · have hrem := sessionSchemeSpk_receive_remoteIdentity P_v1 ℓ spkCoins _ _ c rc hrcv
        dsimp only
        split_ifs <;> cases P <;> simp [SM.GameState.accept, SM.GameState.delete, hrem, hA, hB]
  ·
    change p ∈ support ((SM.corrR cfg P).run gs) at hp
    unfold SM.corrR at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    split_ifs at hp
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact ⟨hA, hB⟩
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨hA, hB⟩

theorem bhE2EFinishStartSpk_preserves_remoteIdInv {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (bMode? : Option Bool)
    (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (kr1 kr2 : SignalPqxdh.KeyIndResponse) (ac : BitVec 256)
    (hInv : CliE2ERemoteIdInv σ) :
    CliE2ERemoteIdInv (bhE2EFinishStartSpk C K bMode? σ sid kr1 kr2 ac).2 := by
  unfold bhE2EFinishStartSpk
  rcases bhE2EGuard σ sid with _ | ⟨hdr, bnd, ⟨u, j⟩⟩
  · exact hInv
  · cases kr1 <;> try exact hInv
    cases kr2 <;> try exact hInv
    dsimp only
    split_ifs
    · intro d hd gs_m hgs
      rw [List.mem_append] at hd
      rcases hd with hd | hd
      · exact hInv d hd gs_m hgs
      · rw [List.mem_singleton] at hd; subst hd
        dsimp only at hgs
        cases bMode? with
        | none => simp at hgs
        | some b =>
          simp only [Option.map_some, Option.some.injEq] at hgs
          subst hgs
          dsimp only [SM.initState, SMSchemeR.sendPart, sessionSchemeFixedSpk, paramsIdsWithSpqr,
            Params.initA, Params.initB, initializeInitiatorSession, initializeRecipientSession]
          refine ⟨?_, rfl⟩
          rcases rootCreateChain C _ _ _ with _ | ⟨_, _⟩ <;> rfl
    · exact hInv

theorem bhE2EStepLocalSm_preserves_remoteIdInv {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (q : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hInv : CliE2ERemoteIdInv σ) :
    ∀ p ∈ support (bhE2EStepLocalSm C K qep decT encT σ i q),
      CliE2ERemoteIdInv p.2 := by
  intro p hp
  unfold bhE2EStepLocalSm at hp
  by_cases hclean : (!bhE2EDrvInstClean σ i) = true
  · simp only [hclean, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hp
    subst hp; exact hInv
  · simp only [hclean, Bool.false_eq_true, ↓reduceIte] at hp
    rcases hi : σ.insts[i]? with _ | d
    · rw [hi] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hInv
    · rcases hm : σ.instMeta[i]? with _ | im
      · rw [hi, hm] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hInv
      · rw [hi, hm] at hp; dsimp only at hp
        by_cases hcorr : (!im.bobAccepted && bhIsBobRecvSMQuery q && bhE2EInstIkACorr σ d) = true
        · simp only [hcorr, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hp
          subst hp; exact hInv
        · simp only [hcorr, Bool.false_eq_true, ↓reduceIte] at hp
          rcases hgs : d.gs with _ | gs
          · rw [hgs] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hInv
          · rw [hgs] at hp; dsimp only at hp
            have hd_mem : d ∈ σ.insts := List.mem_of_getElem? hi
            obtain ⟨hA0, hB0⟩ := hInv d hd_mem gs hgs
            have hSet : ∀ (gs' : SM.GameState (GhostState Bytes) (Plain ℓ) Bytes) (im' : ModelDriverInstanceMeta S),
                (gs'.st .A).session.remoteIdentity = some d.idB →
                (gs'.st .B).session.remoteIdentity = some d.idA →
                CliE2ERemoteIdInv { σ with insts := σ.insts.set i { d with gs := some gs' },
                                           instMeta := σ.instMeta.set i im' } := by
              intro gs' im' hA' hB' d' hd' gs_m hgs_m
              rcases List.mem_or_eq_of_mem_set hd' with hd_old | rfl
              · exact hInv d' hd_old gs_m hgs_m
              · simp only [Option.some.injEq] at hgs_m; subst hgs_m
                exact ⟨hA', hB'⟩
            rcases q with (((sq1 | sq2) | ⟨P, c⟩) | ⟨P, c⟩) | sq5
            · dsimp only at hp
              simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hp
              rcases hp with ⟨⟨r, gs'⟩, hsm, rfl⟩
              have h12 := oracleImplR_sessionSchemeSpk_preserves_remoteIdentity
                C K d.idA d.idB d.spkCoins qep decT encT _ gs hA0 hB0 _ hsm
              exact hSet gs' _ h12.1 h12.2
            · dsimp only at hp
              simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hp
              rcases hp with ⟨⟨r, gs'⟩, hsm, rfl⟩
              have h12 := oracleImplR_sessionSchemeSpk_preserves_remoteIdentity
                C K d.idA d.idB d.spkCoins qep decT encT _ gs hA0 hB0 _ hsm
              exact hSet gs' _ h12.1 h12.2
            · cases P <;> dsimp only at hp
              · by_cases hd : (bhDecodePreKeyMsgE c).isSome = true
                · simp only [hd, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hp
                  subst hp; exact hInv
                · simp only [hd, Bool.false_eq_true, ↓reduceIte, MonadAttach.mem_support_bind,
                    support_pure, Set.mem_singleton_iff] at hp
                  rcases hp with ⟨⟨r, gs'⟩, hsm, rfl⟩
                  have h12 := oracleImplR_sessionSchemeSpk_preserves_remoteIdentity
                    C K d.idA d.idB d.spkCoins qep decT encT _ gs hA0 hB0 _ hsm
                  exact hSet gs' _ h12.1 h12.2
              · by_cases hba : (!im.bobAccepted) = true
                · simp only [hba, ↓reduceIte] at hp
                  rcases hd_opt : bhDecodePreKeyMsgE c with _ | m <;> rw [hd_opt] at hp <;> dsimp only at hp
                  · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hInv
                  · by_cases heq : (c == wirePrekey ::
                        (bhExpectedPreKeyMsg (bhInitRegId d.sid) d.hdr m.inner).bytes) = true
                    · simp only [heq, ↓reduceIte, MonadAttach.mem_support_bind,
                        support_pure, Set.mem_singleton_iff] at hp
                      rcases hp with ⟨⟨r, gs'⟩, hsm, rfl⟩
                      have h12 := oracleImplR_sessionSchemeSpk_preserves_remoteIdentity
                        C K d.idA d.idB d.spkCoins qep decT encT _ gs hA0 hB0 _ hsm
                      exact hSet gs' _ h12.1 h12.2
                    · simp only [heq, Bool.false_eq_true, ↓reduceIte, support_pure,
                        Set.mem_singleton_iff] at hp
                      subst hp; exact hInv
                · simp only [hba, Bool.false_eq_true, ↓reduceIte] at hp
                  rcases hd_opt : bhDecodePreKeyMsgE c with _ | m <;> rw [hd_opt] at hp <;> dsimp only at hp
                  · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hp
                    rcases hp with ⟨⟨r, gs'⟩, hsm, rfl⟩
                    have h12 := oracleImplR_sessionSchemeSpk_preserves_remoteIdentity
                      C K d.idA d.idB d.spkCoins qep decT encT _ gs hA0 hB0 _ hsm
                    exact hSet gs' _ h12.1 h12.2
                  · by_cases hh : (bhHdrOfPreKeyMsg m == d.hdr) = true
                    · simp only [hh, ↓reduceIte, MonadAttach.mem_support_bind,
                        support_pure, Set.mem_singleton_iff] at hp
                      rcases hp with ⟨⟨r, gs'⟩, hsm, rfl⟩
                      have h12 := oracleImplR_sessionSchemeSpk_preserves_remoteIdentity
                        C K d.idA d.idB d.spkCoins qep decT encT _ gs hA0 hB0 _ hsm
                      exact hSet gs' _ h12.1 h12.2
                    · simp only [hh, Bool.false_eq_true, ↓reduceIte, support_pure,
                        Set.mem_singleton_iff] at hp
                      subst hp; exact hInv
            · cases P <;> dsimp only at hp
              · by_cases hd : (bhDecodePreKeyMsgE c).isSome = true
                · simp only [hd, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hp
                  subst hp; exact hInv
                · simp only [hd, Bool.false_eq_true, ↓reduceIte, MonadAttach.mem_support_bind,
                    support_pure, Set.mem_singleton_iff] at hp
                  rcases hp with ⟨⟨r, gs'⟩, hsm, rfl⟩
                  have h12 := oracleImplR_sessionSchemeSpk_preserves_remoteIdentity
                    C K d.idA d.idB d.spkCoins qep decT encT _ gs hA0 hB0 _ hsm
                  exact hSet gs' _ h12.1 h12.2
              · by_cases hba : (!im.bobAccepted) = true
                · simp only [hba, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hp
                  subst hp; exact hInv
                · simp only [hba, Bool.false_eq_true, ↓reduceIte] at hp
                  rcases hd_opt : bhDecodePreKeyMsgE c with _ | m <;> rw [hd_opt] at hp <;> dsimp only at hp
                  · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hp
                    rcases hp with ⟨⟨r, gs'⟩, hsm, rfl⟩
                    have h12 := oracleImplR_sessionSchemeSpk_preserves_remoteIdentity
                      C K d.idA d.idB d.spkCoins qep decT encT _ gs hA0 hB0 _ hsm
                    exact hSet gs' _ h12.1 h12.2
                  · by_cases hh : (bhHdrOfPreKeyMsg m == d.hdr && shortCiphertext c &&
                        decide (m.inner.length + 2048 < 2 ^ 32)) = true
                    · simp only [hh, ↓reduceIte, MonadAttach.mem_support_bind,
                        support_pure, Set.mem_singleton_iff] at hp
                      rcases hp with ⟨⟨r, gs'⟩, hsm, rfl⟩
                      have h12 := oracleImplR_sessionSchemeSpk_preserves_remoteIdentity
                        C K d.idA d.idB d.spkCoins qep decT encT _ gs hA0 hB0 _ hsm
                      exact hSet gs' _ h12.1 h12.2
                    · simp only [hh, Bool.false_eq_true, ↓reduceIte, support_pure,
                        Set.mem_singleton_iff] at hp
                      subst hp; exact hInv
            · dsimp only at hp
              simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hp
              rcases hp with ⟨⟨r, gs'⟩, hsm, rfl⟩
              have h12 := oracleImplR_sessionSchemeSpk_preserves_remoteIdentity
                C K d.idA d.idB d.spkCoins qep decT encT _ gs hA0 hB0 _ hsm
              exact hSet gs' _ h12.1 h12.2

theorem cliE2EDrvImplWith_preserves_remoteIdInv {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (σ : BHE2EDrvState S ℓ) (hInv : CliE2ERemoteIdInv σ) :
    ∀ p ∈ support ((cliE2EDrvImplWith P ki C K qep decT encT q).run σ),
      CliE2ERemoteIdInv p.2 := by
  intro p hp
  rcases q with n | ((kq | cq) | ⟨i, sq⟩)
  · simp only [cliE2EDrvImplWith, StateT.run_monadLift, monadLift_self, support_bind,
      Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hp
    rcases hp with ⟨_, _, rfl⟩; exact hInv
  · simp only [cliE2EDrvImplWith, StateT.run_bind, StateT.run_get, pure_bind] at hp
    split_ifs at hp
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hInv
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hInv
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
        StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind,
        support_pure, Set.mem_singleton_iff] at hp
      rcases hp with ⟨⟨kr, st'⟩, _, rfl⟩
      exact hInv
  · cases cq with | startDR sid =>
    simp only [cliE2EDrvImplWith, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hp
    rcases hp with ⟨⟨idx?, σ'⟩, hstart, rfl⟩
    unfold compositionLocalStart at hstart
    rcases hguard : bhE2EGuard σ sid with _ | ⟨_, _, ⟨u, j⟩⟩
    · rw [hguard] at hstart
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hstart
      rcases hstart with ⟨_, rfl⟩; exact hInv
    · rw [hguard] at hstart
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hstart
      rcases hstart with ⟨⟨kr1, st1⟩, _, ⟨kr2, st2⟩, _, ac, _, hfin⟩
      have hσ' : σ' = (bhE2EFinishStartSpk C K (some σ.b) { σ with st := (kr2, st2).2 }
          sid (kr1, st1).1 (kr2, st2).1 ac).2 := congrArg Prod.snd hfin
      dsimp only
      rw [hσ']
      exact bhE2EFinishStartSpk_preserves_remoteIdInv C K (some σ.b)
        { σ with st := (kr2, st2).2 } sid (kr1, st1).1 (kr2, st2).1 ac hInv
  · simp only [cliE2EDrvImplWith, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hp
    rcases hp with ⟨⟨sr, σ'⟩, hsm, rfl⟩
    exact bhE2EStepLocalSm_preserves_remoteIdInv C K qep decT encT σ i sq hInv (sr, σ') hsm

theorem simulateQ_cliE2EDrvImplWith_preserves_remoteIdInv
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt α : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σ : BHE2EDrvState S ℓ) (hInv : CliE2ERemoteIdInv σ) :
    ∀ p ∈ support ((simulateQ (cliE2EDrvImplWith P ki C K qep decT encT) oa).run σ),
      CliE2ERemoteIdInv p.2 := by
  induction oa using OracleComp.inductionOn generalizing σ with
  | pure a =>
    intro p hp
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp; exact hInv
  | query_bind q oa ih =>
    intro p hp
    rw [run_simulateQ_query_bind, MonadAttach.mem_support_bind] at hp
    rcases hp with ⟨⟨r, σ'⟩, h1, h2⟩
    exact ih r σ' (cliE2EDrvImplWith_preserves_remoteIdInv P ki C K qep decT encT q σ hInv _ h1) p h2

theorem cliComposedAdapterImplWith_preserves_remoteIdInv
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q : (cliGameSpec S ℓ (BitVec 512)).Domain)
    (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ)
    (hInv : CliE2ERemoteIdInv σ_e2e) :
    ∀ p ∈ support (((cliComposedAdapterImplWith P ki C K qep decT encT q).run σ_ad).run σ_e2e),
      CliE2ERemoteIdInv p.2 := by
  rcases q with ((n | kq) | cq) | dq <;>
    exact simulateQ_cliE2EDrvImplWith_preserves_remoteIdInv P ki C K qep decT encT _ σ_e2e hInv

private theorem evalDist_pos_of_mem_support_probComp {α : Type}
    [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : ProbComp α) {a : α} (ha : a ∈ support mx) :
    𝒟[mx] {a} ≠ 0 := by
  induction mx using OracleComp.inductionOn with
  | pure x =>
    simp only [support_pure, Set.mem_singleton_iff] at ha
    subst ha
    simp
  | query_bind n oa ih =>
    simp only [MonadAttach.mem_support_bind] at ha
    rcases ha with ⟨i, _, ha⟩
    rw [evalDist_bind_of_discrete,
        Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
    intro hzero
    have hsum : ∀ j, 𝒟[(liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1)))] {j} *
        𝒟[oa j] {a} = 0 := by
      rw [MeasureTheory.lintegral_fintype] at hzero
      intro j
      simpa [mul_comm] using (Finset.sum_eq_zero_iff.mp hzero j (Finset.mem_univ j))
    have hpos_i :
        𝒟[(liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1)))] {i} ≠ 0 := by
      have hunif := SampleableType.evalDist_selectElem_eq_uniform (β := Fin (n + 1))
      change 𝒟[(liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1)))] = _ at hunif
      rw [hunif]
      simp
    have hmul := hsum i
    rcases mul_eq_zero.mp hmul with h1 | h2
    · exact hpos_i h1
    · exact ih i ha h2

/-- Any property `P` that holds across `support c_ad` automatically holds on the right marginal of
any coupling `μ` with `DEq (Prod.snd <$> μ) c_ad`. -/
theorem deq_support_snd_imp {α β : Type}
    {μ : ProbComp (α × β)} {c_ad : ProbComp β} {P : β → Prop}
    (hDeq : CryptoGames.Lazy.DEq (Prod.snd <$> μ) c_ad)
    (hP : ∀ y ∈ support c_ad, P y) :
    ∀ x y, (x, y) ∈ support μ → P y := by
  classical
  let _ : MeasurableSpace β := ⊤
  have _ : DiscreteMeasurableSpace β := ⟨fun _ => trivial⟩
  intro x y hxy
  by_contra hnot
  have h1 : 𝒟[(Prod.snd <$> μ) >>= fun z => pure (decide (¬ P z))] {true} =
      𝒟[c_ad >>= fun z => pure (decide (¬ P z))] {true} := by
    have := congrArg (fun ν => ν {true}) (hDeq (fun z => pure (decide (¬ P z))))
    simpa [map_eq_bind_pure_comp, bind_assoc, pure_bind] using this
  have hrhs : 𝒟[c_ad >>= fun z => pure (decide (¬ P z))] {true} = 0 := by
    rw [SignalPqxdh.Security.evalDist_bind_true_eq_probExpect, ← le_zero_iff]
    calc SignalPqxdh.Security.probExpect c_ad (fun z => 𝒟[(pure (decide (¬ P z)) : ProbComp Bool)] {true})
        ≤ SignalPqxdh.Security.probExpect c_ad (fun _ => 0) :=
          SignalPqxdh.Security.probExpect_mono_of_support _ _ _ (fun z hz => by simp [hP z hz])
      _ = 0 := SignalPqxdh.Security.probExpect_const _ 0
  have hlhs_pos : 𝒟[(Prod.snd <$> μ) >>= fun z => pure (decide (¬ P z))] {true} ≠ 0 := by
    apply evalDist_pos_of_mem_support_probComp
    rw [MonadAttach.mem_support_bind]
    refine ⟨y, ?_, by simp [hnot]⟩
    rw [support_map, Set.mem_image]
    exact ⟨(x, y), hxy, rfl⟩
  exact hlhs_pos (h1.trans hrhs)

end CryptoVerification.E2E
