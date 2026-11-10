/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3H1
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3D
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3E
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3H2
import Computational.Proofs.SignalPqxdh.Security.RoKemHopA
import Computational.Proofs.SignalPqxdh.Security.RoKemHop
import VCVio.EvalDist.Monad.Basic

@[expose] public section
set_option autoImplicit false
open OracleSpec OracleComp MeasureTheory ENNReal BigOperators
namespace SignalPqxdh.Security
open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security
open RoKem
namespace AuthSubHops1to3
def finishAuthSendMkSlotsH3 {S : Setup} (P : Primitives) (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes) (drKey : DRKey) (rk1 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (deriveMessageKeys : MessageKeys) :
    AuthResponse × AuthHybridStateFixed S :=
  let (resp, hst0) := finishAuthSendMk P sid uEntry peerPrincipal? bundle m0 m1
    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
    spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys
  (resp, { hst0 with slots := hst.slots })
def prepareAuthSendMkSlotsH3 (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) : ProbComp (PreparedAuthSend S) :=
  PreparedAuthSend.mapState (fun s => { s with slots := hst.slots }) <$>
    prepareAuthSendMk S P sid u bundle m0 m1 hst
def finishAuthRecvMkSlotsH3 {S : Setup} (P : Primitives) (msg : PreKeyMsg) (prep : PreparedAuthRecv S)
    (drKey : DRKey) (rk1 ck1_1 : Bytes) (recvCount' : Nat)
    (mkSaltCache' : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (slots' : AuthSlotState) (deriveMessageKeys : MessageKeys) :
    AuthResponse × AuthHybridStateFixed S :=
  let (resp, hst0) := finishAuthRecvMk P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache'
    deriveMessageKeys
  (resp, { hst0 with slots := slots' })
private theorem simulateQ_finishAuthSendMkSlotsH3Prim (S : Setup) (P : Primitives)
    (sid : SessionId S) (uEntry : PrincipalEntry) (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (deriveMessageKeys : MessageKeys)
    (hPrin : hst.toAuthHybridState.base.principals.length ≤ S.N_dh)
    (hSpk : hst.toAuthHybridState.base.spkBundles.length ≤ S.N_dh)
    (hOpk : hst.toAuthHybridState.base.opkEntries.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P)
      (finishAuthSendMkPrim S sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys) =
      pure (finishAuthSendMkSlotsH3 P sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys) := by
  unfold finishAuthSendMkPrim finishAuthSendMkSlotsH3 finishAuthSendMk
  dsimp only
  rw [simulateQ_bind, simulateQ_primQ_aeadEnc, pure_bind, simulateQ_bind,
      simulateQ_finishAuthHybridSendPrim S P sid uEntry peerPrincipal? _ bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] mkSeed ck1_1
        spqrSalt? pqRatchetMsg deriveMessageKeys _ _ msgPlain _ _ hst.toAuthHybridState hPrin hSpk hOpk,
      pure_bind]
  rfl
private theorem simulateQ_prepareAuthSendMkSlotsH3Prim (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (hPrin : hst.toAuthHybridState.base.principals.length ≤ S.N_dh)
    (hSpk : hst.toAuthHybridState.base.spkBundles.length ≤ S.N_dh)
    (hOpk : hst.toAuthHybridState.base.opkEntries.length ≤ S.N_dh)
    (hAdv : ValidAdvKeysPow8 P hst.toAuthHybridState.base.advKeys) :
    simulateQ (primBaseImpl P) (prepareAuthSendMkPrim S sid u bundle m0 m1 hst) =
      prepareAuthSendMkSlotsH3 S P sid u bundle m0 m1 hst := by
  unfold prepareAuthSendMkPrim prepareAuthSendMkSlotsH3 prepareAuthSendMk
  dsimp only
  cases hst.toAuthHybridState.base.hasWonAuth <;> simp only [Bool.false_eq_true, ↓reduceIte]
  swap; · simp [PreparedAuthSend.mapState]
  by_cases hLen : (m0.length != m1.length) = true
  · simp [hLen, PreparedAuthSend.mapState]
  · simp only [hLen, Bool.false_eq_true, ↓reduceIte]
    by_cases hUsed : (hst.toAuthHybridState.base.usedSendSessions.contains sid) = true
    · simp only [hUsed, ↓reduceIte]; rfl
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte]
      cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp [PreparedAuthSend.mapState]
      | some uPair =>
        rcases uPair with ⟨_, uEntry⟩
        dsimp only
        rw [simulateQ_bind,
            simulateQ_findHonestPrincipalPrim S P hst.toAuthHybridState.base.principals bundle.ikB
              hPrin,
            pure_bind]
        have hProv2 := (checkBundleProvenanceExact_spk_pqspk P hst.toAuthHybridState.base.principals
          hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries bundle).2
        cases hpeer : findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB with
        | none =>
          dsimp only
          by_cases hCh : (m0 != m1) = true
          · simp only [Bool.not_false, Bool.true_and, hCh, ↓reduceIte]; rfl
          · simp only [Bool.not_false, Bool.true_and, hCh, Bool.false_eq_true, ↓reduceIte]
            rw [simulateQ_bind, simulateQ_koskBundleOkPrim S P _ _ _ _ bundle hPrin hSpk hOpk hAdv,
              pure_bind]
            by_cases hKosk : (!koskBundleOk P hst.toAuthHybridState.base.principals
                hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries
                hst.toAuthHybridState.base.advKeys bundle) = true
            · simp [hKosk, PreparedAuthSend.mapState]
            · simp only [hKosk, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, simulateQ_embedUnif,
                map_bind]
              congr 1; funext ekASk; congr 1; funext kemCoins; congr 1; funext ephASk; congr 1;
                funext spqrCoins
              rw [simulateQ_resolveSigPkPrim S P _ bundle.ikB hPrin, pure_bind,
                  simulateQ_primQ_sigVerify, pure_bind, simulateQ_primQ_sigVerify, pure_bind]
              by_cases hSig : (!(P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals
                bundle.ikB)
                    (encodeEC bundle.spkB) bundle.spkSig &&
                  P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
                    (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
              · simp [hSig, PreparedAuthSend.mapState]
              · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
                rw [simulateQ_bind, simulateQ_primQ_kemEncaps, pure_bind]
                cases P.kemEncaps bundle.pqspkB kemCoins with
                | none => simp [PreparedAuthSend.mapState]
                | some pair =>
                  rcases pair with ⟨ss, kemCt⟩; dsimp only
                  rw [simulateQ_bind, simulateQ_primQ_x25519Base, pure_bind,
                      simulateQ_bind, simulateQ_primQ_x25519Base, pure_bind,
                      simulateQ_bind,
                      simulateQ_checkBundleSpkHonIdealPrim S P hst.toAuthHybridState.base.principals
                        hst.toAuthHybridState.base.spkBundles bundle hPrin hSpk,
                      pure_bind]
                  simp only [Option.isSome, Bool.false_and, Bool.or_false, Bool.false_eq_true,
                    ↓reduceIte, map_bind]
                  rw [simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                      simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                      simulateQ_bind, simulateQ_primQ_x25519, pure_bind]
                  have hDh4 : simulateQ (primBaseImpl P)
                      (Option.casesOn bundle.opkB? (pure none) (fun (_, opkPk) => do
                        let d4 ← primQ (.x25519 ekASk opkPk); pure (some d4))) =
                      pure (bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)) := by
                    cases bundle.opkB? with
                    | none => rfl
                    | some opkPair => rcases opkPair with ⟨_, opkPk⟩; simp only [simulateQ_bind,
                      simulateQ_pure]; rfl
                  rw [simulateQ_bind, hDh4, pure_bind]
                  simp only [simulateQ_bind, simulateQ_embedUnif, evalHkdfOrRo_true_eq_pure]
                  congr 1; funext ⟨drKey, roCache'⟩
                  rw [simulateQ_primQ_x25519, pure_bind]
                  simp only [evalRootKdfOrRo_true_eq_pure]
                  congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
                  rw [simulateQ_primQ_chainKdfSeed, pure_bind,
                      simulateQ_primQ_chainKdfNext, pure_bind, simulateQ_primQ_spqrInitSend,
                        pure_bind]
                  cases P.spqrInitSend drKey.pqrKey spqrCoins with
                  | none => simp [PreparedAuthSend.mapState]
                  | some spqrVal =>
                    rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩; dsimp only
                    rw [simulateQ_bind, simulateQ_primQ_deriveMsgKeys, pure_bind,
                        simulateQ_bind, simulateQ_primQ_aeadEnc, pure_bind, simulateQ_bind,
                        simulateQ_finishAuthHybridSendPrim S P sid _ _ _ bundle m0 m1 ekASk _ ss
                          kemCt
                          ephASk _ drKey rk1 ck1_0 _ _ spqrSalt? pqRatchetMsg _ _ _ _ roCache'
                            rootRoCache'
                          hst.toAuthHybridState hPrin hSpk hOpk, pure_bind]
                    simp [PreparedAuthSend.mapState]
        | some pPair =>
          rcases pPair with ⟨pIdx, pEntry⟩; dsimp only
          rw [hpeer] at hProv2
          by_cases hCh : (!!pEntry.corrupted && (m0 != m1)) = true
          · simp only [hCh, ↓reduceIte]; rfl
          · simp only [hCh, Bool.false_eq_true, ↓reduceIte]
            rw [simulateQ_bind, simulateQ_koskBundleOkPrim S P _ _ _ _ bundle hPrin hSpk hOpk hAdv,
              pure_bind]
            by_cases hKosk : (!koskBundleOk P hst.toAuthHybridState.base.principals
                hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries
                hst.toAuthHybridState.base.advKeys bundle) = true
            · simp [hKosk, PreparedAuthSend.mapState]
            · simp only [hKosk, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, simulateQ_embedUnif,
                map_bind]
              congr 1; funext ekASk; congr 1; funext kemCoins; congr 1; funext ephASk; congr 1;
                funext spqrCoins
              rw [simulateQ_resolveSigPkPrim S P _ bundle.ikB hPrin, pure_bind,
                  simulateQ_primQ_sigVerify, pure_bind, simulateQ_primQ_sigVerify, pure_bind]
              by_cases hSig : (!(P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals
                bundle.ikB)
                    (encodeEC bundle.spkB) bundle.spkSig &&
                  P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
                    (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
              · simp [hSig, PreparedAuthSend.mapState]
              · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
                rw [simulateQ_bind, simulateQ_primQ_kemEncaps, pure_bind]
                cases P.kemEncaps bundle.pqspkB kemCoins with
                | none => simp [PreparedAuthSend.mapState]
                | some pair =>
                  rcases pair with ⟨ss, kemCt⟩; dsimp only
                  rw [simulateQ_bind, simulateQ_primQ_x25519Base, pure_bind,
                      simulateQ_bind, simulateQ_primQ_x25519Base, pure_bind,
                      simulateQ_bind,
                      simulateQ_checkBundleSpkHonIdealPrim S P hst.toAuthHybridState.base.principals
                        hst.toAuthHybridState.base.spkBundles bundle hPrin hSpk,
                      pure_bind, ← hProv2]
                  by_cases hIdeal : (!pEntry.corrupted ||
                      ((some (pIdx, pEntry)).isSome &&
                       checkBundleSpkHonIdeal P hst.toAuthHybridState.base.principals
                         hst.toAuthHybridState.base.spkBundles bundle &&
                       (checkBundleProvenanceExact P hst.toAuthHybridState.base.principals
                         hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries
                           bundle).2.2)) = true
                  · simp only [hIdeal, ↓reduceIte, simulateQ_bind, simulateQ_embedUnif, map_bind]
                    congr 1; funext drKey; congr 1; funext rk1
                    rw [simulateQ_primQ_spqrInitSend, pure_bind]
                    cases P.spqrInitSend drKey.pqrKey spqrCoins with
                    | none => simp [PreparedAuthSend.mapState]
                    | some spqrVal => rcases spqrVal with ⟨_, _, _⟩; simp [PreparedAuthSend.mapState]
                  · simp only [hIdeal, Bool.false_eq_true, ↓reduceIte, map_bind]
                    rw [simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                        simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                        simulateQ_bind, simulateQ_primQ_x25519, pure_bind]
                    have hDh4 : simulateQ (primBaseImpl P)
                        (Option.casesOn bundle.opkB? (pure none) (fun (_, opkPk) => do
                          let d4 ← primQ (.x25519 ekASk opkPk); pure (some d4))) =
                        pure (bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)) := by
                      cases bundle.opkB? with
                      | none => rfl
                      | some opkPair => rcases opkPair with ⟨_, opkPk⟩; simp only [simulateQ_bind,
                        simulateQ_pure]; rfl
                    rw [simulateQ_bind, hDh4, pure_bind]
                    simp only [simulateQ_bind, simulateQ_embedUnif, evalHkdfOrRo_true_eq_pure]
                    congr 1; funext ⟨drKey, roCache'⟩
                    rw [simulateQ_primQ_x25519, pure_bind]
                    simp only [evalRootKdfOrRo_true_eq_pure]
                    congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
                    rw [simulateQ_primQ_chainKdfSeed, pure_bind,
                        simulateQ_primQ_chainKdfNext, pure_bind, simulateQ_primQ_spqrInitSend,
                          pure_bind]
                    cases P.spqrInitSend drKey.pqrKey spqrCoins with
                    | none => simp [PreparedAuthSend.mapState]
                    | some spqrVal =>
                      rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩; dsimp only
                      rw [simulateQ_bind, simulateQ_primQ_deriveMsgKeys, pure_bind,
                          simulateQ_bind, simulateQ_primQ_aeadEnc, pure_bind, simulateQ_bind,
                          simulateQ_finishAuthHybridSendPrim S P sid _ _ _ bundle m0 m1 ekASk _ ss
                            kemCt
                            ephASk _ drKey rk1 ck1_0 _ _ spqrSalt? pqRatchetMsg _ _ _ _ roCache'
                              rootRoCache'
                            hst.toAuthHybridState hPrin hSpk hOpk, pure_bind]
                      simp [PreparedAuthSend.mapState]
private theorem prepareAuthSendMkSlotsH3_cacheAuthAdvKeysFixed (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    prepareAuthSendMkSlotsH3 S P sid u bundle m0 m1 (cacheAuthAdvKeysFixed P hst) =
      PreparedAuthSend.mapState (cacheAuthAdvKeysFixed P) <$>
        prepareAuthSendMkSlotsH3 S P sid u bundle m0 m1 hst := by
  unfold prepareAuthSendMkSlotsH3
  have hSlots : (cacheAuthAdvKeysFixed P hst).slots = hst.slots := rfl
  rw [hSlots, prepareAuthSendMk_cacheAuthAdvKeysFixed, Functor.map_map, Functor.map_map]
  congr 1; funext p; cases p <;> rfl
private theorem simulateQ_finishAuthRecvMkSlotsH3Prim (S : Setup) (P : Primitives)
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S) (drKey : DRKey) (rk1 ck1_1 : Bytes)
    (recvCount' : Nat) (mkSaltCache' : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (slots' : AuthSlotState) (deriveMessageKeys : MessageKeys)
    (hPrin : prep.finishTag.hstDec.base.principals.length ≤ S.N_dh)
    (hSentOPK : prep.finishTag.hstDec.base.sentOPKEvents.length ≤ S.N_dh)
    (hSentNoOPK : prep.finishTag.hstDec.base.sentNoOPKEvents.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P)
      (finishAuthRecvMkSlotsPrim S msg prep drKey rk1 ck1_1 recvCount' mkSaltCache' slots'
        deriveMessageKeys) =
      pure (finishAuthRecvMkSlotsH3 P msg (prep.toPure true P) drKey rk1 ck1_1 recvCount'
        mkSaltCache' slots' deriveMessageKeys) := by
  unfold finishAuthRecvMkSlotsPrim finishAuthRecvMkSlotsH3 finishAuthRecvMk PreparedAuthRecvPrim.toPure
  dsimp only
  rw [simulateQ_bind, simulateQ_primQ_aeadDec, pure_bind, simulateQ_bind,
      simulateQ_recvFinishTag_runPrim S true P prep.finishTag _ hPrin hSentOPK hSentNoOPK,
      pure_bind]
  rfl
private theorem finishAuthRecvMkSlotsH3_mapState_cacheAuthAdvKeys {S : Setup} (P : Primitives)
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S) (drKey : DRKey) (rk1 ck1_1 : Bytes)
    (recvCount' : Nat) (mkSaltCache' : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (slots' : AuthSlotState) (deriveMessageKeys : MessageKeys) :
    finishAuthRecvMkSlotsH3 P msg ((prep.mapState (cacheAuthAdvKeys P)).toPure true P)
      drKey rk1 ck1_1 recvCount' mkSaltCache' slots' deriveMessageKeys =
    let (resp, hst') := finishAuthRecvMkSlotsH3 P msg (prep.toPure true P) drKey rk1 ck1_1 recvCount'
      mkSaltCache' slots' deriveMessageKeys
    (resp, cacheAuthAdvKeysFixed P hst') := by
  unfold finishAuthRecvMkSlotsH3 finishAuthRecvMk PreparedAuthRecvPrim.mapState
    PreparedAuthRecvPrim.toPure cacheAuthAdvKeysFixed
  simp only [cacheAuthAdvKeys_roCache, cacheAuthAdvKeys_rootRoCache,
    recvFinishTag_mapState_toPure_fst, recvFinishTag_mapState_toPure_snd]
theorem simulateQ_prfMkFullImpl_embedPrimMk {Cache α : Type} (P : Primitives)
    (impl : QueryImpl prfMsgKeysSpec (StateT Cache ProbComp))
    (mx : OracleComp PrimBaseSpec α) (cache : Cache) :
    let fullImpl := (primBaseImpl P).liftTarget (StateT Cache ProbComp) + impl
    (simulateQ fullImpl (embedPrimMk mx)).run cache =
      (simulateQ (primBaseImpl P) mx >>= fun a => pure (a, cache)) := by
  intro fullImpl
  unfold embedPrimMk
  rw [simulateQ_embedPrim_run, map_eq_bind_pure_comp]
  rfl
theorem simulateQ_prfMkFullImpl_embedUnifMk {Cache α : Type} (P : Primitives)
    (impl : QueryImpl prfMsgKeysSpec (StateT Cache ProbComp)) (mx : ProbComp α) (cache : Cache) :
    let fullImpl := (primBaseImpl P).liftTarget (StateT Cache ProbComp) + impl
    (simulateQ fullImpl (embedUnifMk mx)).run cache =
      (mx >>= fun a => pure (a, cache)) := by
  intro fullImpl
  unfold embedUnifMk
  rw [simulateQ_prfMkFullImpl_embedPrimMk, simulateQ_embedUnif]
theorem simulateQ_prfMkFullImpl_deriveMkQ {Cache : Type} (P : Primitives)
    (impl : QueryImpl prfMsgKeysSpec (StateT Cache ProbComp))
    (spqrSalt? : Option Bytes) (cache : Cache) :
    let fullImpl := (primBaseImpl P).liftTarget (StateT Cache ProbComp) + impl
    (simulateQ fullImpl (deriveMkQ spqrSalt?)).run cache =
      (impl (.derive (effectiveHkdfSaltBytes spqrSalt?))).run cache := by
  intro fullImpl
  simp [deriveMkQ, fullImpl]
theorem simulateQ_prfMkFullImpl_embedPrimMk_bind {Cache α β : Type} (P : Primitives)
    (impl : QueryImpl prfMsgKeysSpec (StateT Cache ProbComp)) (mx : OracleComp PrimBaseSpec α)
    (k : α → OracleComp PrfMkSimSpec β) (cache : Cache) :
    let fullImpl := (primBaseImpl P).liftTarget (StateT Cache ProbComp) + impl
    (simulateQ fullImpl (embedPrimMk mx >>= k)).run cache =
      (simulateQ (primBaseImpl P) mx >>= fun a => (simulateQ fullImpl (k a)).run cache) := by
  intro fullImpl
  rw [simulateQ_bind, StateT.run_bind, simulateQ_prfMkFullImpl_embedPrimMk, bind_assoc]
  simp only [pure_bind]
theorem simulateQ_prfMkFullImpl_embedUnifMk_bind {Cache α β : Type} (P : Primitives)
    (impl : QueryImpl prfMsgKeysSpec (StateT Cache ProbComp)) (mx : ProbComp α)
    (k : α → OracleComp PrfMkSimSpec β) (cache : Cache) :
    let fullImpl := (primBaseImpl P).liftTarget (StateT Cache ProbComp) + impl
    (simulateQ fullImpl (embedUnifMk mx >>= k)).run cache =
      (mx >>= fun a => (simulateQ fullImpl (k a)).run cache) := by
  intro fullImpl
  rw [simulateQ_bind, StateT.run_bind, simulateQ_prfMkFullImpl_embedUnifMk, bind_assoc]
  simp only [pure_bind]
theorem simulateQ_prfMkFullImpl_deriveMkQ_bind {Cache β : Type} (P : Primitives)
    (impl : QueryImpl prfMsgKeysSpec (StateT Cache ProbComp)) (spqrSalt? : Option Bytes)
    (k : MessageKeys → OracleComp PrfMkSimSpec β) (cache : Cache) :
    let fullImpl := (primBaseImpl P).liftTarget (StateT Cache ProbComp) + impl
    (simulateQ fullImpl (deriveMkQ spqrSalt? >>= k)).run cache =
      ((impl (.derive (effectiveHkdfSaltBytes spqrSalt?))).run cache >>= fun (mk, cache') =>
        (simulateQ fullImpl (k mk)).run cache') := by
  intro fullImpl
  rw [simulateQ_bind, StateT.run_bind, simulateQ_prfMkFullImpl_deriveMkQ]
def authMkSendRedProb (S : Setup) (P : Primitives) (idx : Nat) {Cache : Type}
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache) :
    ProbComp (AuthResponse × ((AuthHybridStateFixed S × Bool) × Cache)) := do
  match ← prepareAuthSendMk S P sid u bundle m0 m1 hst with
  | .done resp hst' => pure (resp, ((hst', sentChal), cache))
  | .idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk
      drKey rk1 spqrSalt? pqRatchetMsg msgPlain =>
    let sIdx := sessionSlotIndex sid
    if !sentChal && (sIdx == idx) then
      let ck1_1 ← sampleBytes32
      let (deriveMessageKeys, cache') ← evalPrf spqrSalt? cache
      let (resp, hst') := finishAuthSendMk P sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys
      pure (resp, ((hst', true), cache'))
    else if decide (sIdx < idx) then
      let ck1_1 ← sampleBytes32
      let deriveMessageKeys ← sampleMessageKeys80
      let (resp, hst') := finishAuthSendMk P sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys
      pure (resp, ((hst', sentChal), cache))
    else
      let mkSeed ← sampleBytes32
      let ck1_1 ← sampleBytes32
      let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
      let (resp, hst') := finishAuthSendMk P sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys
      pure (resp, ((hst', sentChal), cache))
def finishAuthRecvUnmatchedRedProb (S : Setup) (P : Primitives) (idx : Nat) {Cache : Type}
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (msg : PreKeyMsg) (prep : PreparedAuthRecv S) (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (rSlot recvCount' : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (sentChal : Bool) (cache : Cache) :
    ProbComp ((AuthResponse × AuthHybridStateFixed S) × Cache) := do
  if rSlot == idx then
    let ck1_1 ← sampleBytes32
    let (deriveMessageKeys, cache') ←
      if !sentChal then evalPrf spqrSalt? cache
      else do
        let mk ← sampleMessageKeys80
        pure (mk, cache)
    pure (finishAuthRecvMk P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache deriveMessageKeys, cache')
  else if decide (rSlot < idx) then
    let ck1_1 ← sampleBytes32
    let deriveMessageKeys ← sampleMessageKeys80
    pure (finishAuthRecvMk P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache deriveMessageKeys, cache)
  else
    let mkSeed ← sampleBytes32
    let ck1_1 ← sampleBytes32
    let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
    pure (finishAuthRecvMk P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache deriveMessageKeys, cache)
def matchedSameEphMkRedProb (S : Setup) (P : Primitives) (idx : Nat) {Cache : Type}
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (s : IdealAuthSession S) (spqrSalt? : Option Bytes) (recvCount : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys))) (cache : Cache) :
    ProbComp ((MessageKeys × List ((SessionId S × Option Bytes) × (Nat × MessageKeys))) × Cache) :=
  let sIdx := sessionSlotIndex s.sid
  if sIdx == idx then
    if sameSaltKey spqrSalt? s.spqrSalt? then
      pure ((s.deriveMessageKeys, mkSaltCache), cache)
    else
      match mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
      | some (_, (_, mk)) => pure ((mk, mkSaltCache), cache)
      | none => do
        let (mk, cache') ← evalPrf spqrSalt? cache
        pure ((mk, ((s.sid, spqrSalt?), (recvCount, mk)) :: mkSaltCache), cache')
  else if decide (sIdx < idx) then
    if sameSaltKey spqrSalt? s.spqrSalt? then
      pure ((s.deriveMessageKeys, mkSaltCache), cache)
    else
      match mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
      | some (_, (_, mk)) => pure ((mk, mkSaltCache), cache)
      | none => do
        let mk ← sampleMessageKeys80
        pure ((mk, ((s.sid, spqrSalt?), (recvCount, mk)) :: mkSaltCache), cache)
  else
    pure ((P.deriveMsgKeys s.mkSeed spqrSalt?, mkSaltCache), cache)
def authMkRecvRedProb (S : Setup) (P : Primitives) (idx : Nat) {Cache : Type}
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache) :
    ProbComp ((AuthResponse × AuthHybridStateFixed S) × Cache) := do
  let recvCount' := hst.recvCount + 1
  let rSlot := S.N_send_tot + hst.recvCount
  match prep? with
  | none => pure ((.noneResp, { hst with recvCount := recvCount' }), cache)
  | some prep =>
    let st := prep.hstDec.base
    let useIdealBranch : Bool := prep.matchedSess?.isSome || prep.isUncorruptedHonestSender
    if useIdealBranch then
      match prep.matchedSess? with
      | some s =>
        if prep.sameEph then
          match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            let (resp, hst') := prep.finish none
            pure ((resp, { toAuthHybridState := hst', recvCount := recvCount', mkSaltCache :=
                           hst.mkSaltCache }), cache)
          | some (_pqrStB, spqrSalt?) =>
            let ((mk, mkSaltCache'), cache') ←
              matchedSameEphMkRedProb S P idx evalPrf s spqrSalt? hst.recvCount hst.mkSaltCache
                cache
            pure (finishAuthRecvMk P msg prep s.drKey s.rk1 s.ck1_1 recvCount' mkSaltCache' mk,
                   cache')
        else
          let rk1 ← sampleBytes32
          match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            let (resp, hst') := prep.finish none
            pure ((resp, { toAuthHybridState := hst', recvCount := recvCount', mkSaltCache :=
                           hst.mkSaltCache }), cache)
          | some (_pqrStB, spqrSalt?) =>
            finishAuthRecvUnmatchedRedProb S P idx evalPrf msg prep s.drKey rk1
              spqrSalt? rSlot recvCount' hst.mkSaltCache sentChal cache
      | none =>
        let drKey ← sampleDRKey96
        let rk1 ← sampleBytes32
        match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          let (resp, hst') := prep.finish none
          pure ((resp, { toAuthHybridState := hst', recvCount := recvCount', mkSaltCache :=
                         hst.mkSaltCache }), cache)
        | some (_pqrStB, spqrSalt?) =>
          finishAuthRecvUnmatchedRedProb S P idx evalPrf msg prep drKey rk1
            spqrSalt? rSlot recvCount' hst.mkSaltCache sentChal cache
    else
      let (drKey, roCache') ← evalHkdfOrRo true P st.roCache prep.secrets
      let ((rk1, ck1_0), rootRoCache') ← evalRootKdfOrRo true P st.rootRoCache drKey.rootKey
        prep.dhRatchet
      let mkSeed := P.chainKdfSeed ck1_0
      let ck1_1 := P.chainKdfNext ck1_0
      match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none =>
        let (resp, hst') := prep.finish none
        pure ((resp, { toAuthHybridState := hst', recvCount := recvCount', mkSaltCache :=
                       hst.mkSaltCache }), cache)
      | some (_pqrStB, spqrSalt?) =>
        let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
        let ad := firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
        let res? := (P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
          (drKey, rk1, ck1_1, pt, roCache', rootRoCache'))
        let (resp, hst') := prep.finish res?
        pure ((resp, { toAuthHybridState := hst', recvCount := recvCount', mkSaltCache :=
                       hst.mkSaltCache }), cache)
def authMkStepRedProb (S : Setup) (P : Primitives) (idx : Nat) {Cache : Type}
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache) :
    ProbComp ((authSpec S).Range q × ((AuthHybridStateFixed S × Bool) × Cache)) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.noneResp, ((hst, sentChal), cache))
    else authMkSendRedProb S P idx evalPrf (.sendOPK u i) u bundle m0 m1 hst sentChal cache
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.noneResp, ((hst, sentChal), cache))
    else authMkSendRedProb S P idx evalPrf (.sendNoOPK u i) u bundle m0 m1 hst sentChal cache
  | .recvOPK k j o msg => do
    let prep? := prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState
    let ((resp, hst'), cache') ← authMkRecvRedProb S P idx evalPrf msg prep? hst sentChal cache
    pure (resp, ((hst', sentChal), cache'))
  | .recvNoOPK k j l msg => do
    let prep? := prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState
    let ((resp, hst'), cache') ← authMkRecvRedProb S P idx evalPrf msg prep? hst sentChal cache
    pure (resp, ((hst', sentChal), cache'))
  | qOther => do
    let (resp, hst') ← authCkOtherStep S P qOther hst
    pure (resp, ((hst', sentChal), cache))
def authMkRedProbImpl (S : Setup) (P : Primitives) (idx : Nat) {Cache : Type}
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache)) :
    QueryImpl (authSpec S) (StateT ((AuthHybridStateFixed S × Bool) × Cache) ProbComp) :=
  fun q => StateT.mk (fun ((hst, sentChal), cache) =>
    authMkStepRedProb S P idx evalPrf q hst sentChal cache)
def authMkSlotsSendRedProb (S : Setup) (P : Primitives) (idx : Nat) {Cache : Type}
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache) :
    ProbComp (AuthResponse × ((AuthHybridStateFixed S × Bool) × Cache)) := do
  match ← prepareAuthSendMkSlotsH3 S P sid u bundle m0 m1 hst with
  | .done resp hst' => pure (resp, ((hst', sentChal), cache))
  | .idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk
      drKey rk1 spqrSalt? pqRatchetMsg msgPlain =>
    let (sIdx, slots') := hst.slots.allocSend sid
    let hst1 := { hst with slots := slots' }
    if !sentChal && (sIdx == idx) then
      let ck1_1 ← sampleBytes32
      let (deriveMessageKeys, cache') ← evalPrf spqrSalt? cache
      let (resp, hst') := finishAuthSendMkSlotsH3 P sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst1 deriveMessageKeys
      pure (resp, ((hst', true), cache'))
    else if decide (sIdx < idx) then
      let ck1_1 ← sampleBytes32
      let deriveMessageKeys ← sampleMessageKeys80
      let (resp, hst') := finishAuthSendMkSlotsH3 P sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst1 deriveMessageKeys
      pure (resp, ((hst', sentChal), cache))
    else
      let mkSeed ← sampleBytes32
      let ck1_1 ← sampleBytes32
      let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
      let (resp, hst') := finishAuthSendMkSlotsH3 P sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst1 deriveMessageKeys
      pure (resp, ((hst', sentChal), cache))
def finishAuthRecvUnmatchedSlotsRedProb (S : Setup) (P : Primitives) (idx : Nat) {Cache : Type}
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (msg : PreKeyMsg) (prep : PreparedAuthRecv S) (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (rSlot recvCount' : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (slots' : AuthSlotState) (sentChal : Bool) (cache : Cache) :
    ProbComp ((AuthResponse × AuthHybridStateFixed S) × Cache) := do
  if rSlot == idx then
    let ck1_1 ← sampleBytes32
    let (deriveMessageKeys, cache') ←
      if !sentChal then evalPrf spqrSalt? cache
      else do
        let mk ← sampleMessageKeys80
        pure (mk, cache)
    pure (finishAuthRecvMkSlotsH3 P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache slots'
      deriveMessageKeys, cache')
  else if decide (rSlot < idx) then
    let ck1_1 ← sampleBytes32
    let deriveMessageKeys ← sampleMessageKeys80
    pure (finishAuthRecvMkSlotsH3 P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache slots'
      deriveMessageKeys, cache)
  else
    let mkSeed ← sampleBytes32
    let ck1_1 ← sampleBytes32
    let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
    pure (finishAuthRecvMkSlotsH3 P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache slots'
      deriveMessageKeys, cache)
def matchedSameEphMkSlotsRedProb (S : Setup) (P : Primitives) (idx : Nat) {Cache : Type}
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (s : IdealAuthSession S) (sIdx : Nat) (spqrSalt? : Option Bytes) (recvCount : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys))) (cache : Cache) :
    ProbComp ((MessageKeys × List ((SessionId S × Option Bytes) × (Nat × MessageKeys))) × Cache) :=
  if sIdx == idx then
    if sameSaltKey spqrSalt? s.spqrSalt? then
      pure ((s.deriveMessageKeys, mkSaltCache), cache)
    else
      match mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
      | some (_, (_, mk)) => pure ((mk, mkSaltCache), cache)
      | none => do
        let (mk, cache') ← evalPrf spqrSalt? cache
        pure ((mk, ((s.sid, spqrSalt?), (recvCount, mk)) :: mkSaltCache), cache')
  else if decide (sIdx < idx) then
    if sameSaltKey spqrSalt? s.spqrSalt? then
      pure ((s.deriveMessageKeys, mkSaltCache), cache)
    else
      match mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
      | some (_, (_, mk)) => pure ((mk, mkSaltCache), cache)
      | none => do
        let mk ← sampleMessageKeys80
        pure ((mk, ((s.sid, spqrSalt?), (recvCount, mk)) :: mkSaltCache), cache)
  else
    pure ((P.deriveMsgKeys s.mkSeed spqrSalt?, mkSaltCache), cache)
def authMkSlotsRecvRedProb (S : Setup) (P : Primitives) (idx : Nat) {Cache : Type}
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache) :
    ProbComp ((AuthResponse × AuthHybridStateFixed S) × Cache) := do
  let recvCount' := hst.recvCount + 1
  match prep? with
  | none => pure ((.noneResp, { hst with recvCount := recvCount' }), cache)
  | some prep =>
    let st := prep.hstDec.base
    let useIdealBranch : Bool := prep.matchedSess?.isSome || prep.isUncorruptedHonestSender
    if useIdealBranch then
      match prep.matchedSess? with
      | some s =>
        if prep.sameEph then
          match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            let (resp, hst') := prep.finish none
            pure ((resp, { toAuthHybridState := hst', recvCount := recvCount',
                           mkSaltCache := hst.mkSaltCache, slots := hst.slots }), cache)
          | some (_pqrStB, spqrSalt?) =>
            let sIdx := hst.slots.lookupSendOrZero s.sid
            let ((mk, mkSaltCache'), cache') ←
              matchedSameEphMkSlotsRedProb S P idx evalPrf s sIdx spqrSalt? hst.recvCount
                hst.mkSaltCache cache
            pure (finishAuthRecvMkSlotsH3 P msg prep s.drKey s.rk1 s.ck1_1 recvCount'
              mkSaltCache' hst.slots mk, cache')
        else
          let rk1 ← sampleBytes32
          match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            let (resp, hst') := prep.finish none
            pure ((resp, { toAuthHybridState := hst', recvCount := recvCount',
                           mkSaltCache := hst.mkSaltCache, slots := hst.slots }), cache)
          | some (_pqrStB, spqrSalt?) =>
            let (rSlot, slots') := hst.slots.allocRecv hst.recvCount
            finishAuthRecvUnmatchedSlotsRedProb S P idx evalPrf msg prep s.drKey rk1
              spqrSalt? rSlot recvCount' hst.mkSaltCache slots' sentChal cache
      | none =>
        let drKey ← sampleDRKey96
        let rk1 ← sampleBytes32
        match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          let (resp, hst') := prep.finish none
          pure ((resp, { toAuthHybridState := hst', recvCount := recvCount',
                         mkSaltCache := hst.mkSaltCache, slots := hst.slots }), cache)
        | some (_pqrStB, spqrSalt?) =>
          let (rSlot, slots') := hst.slots.allocRecv hst.recvCount
          finishAuthRecvUnmatchedSlotsRedProb S P idx evalPrf msg prep drKey rk1
            spqrSalt? rSlot recvCount' hst.mkSaltCache slots' sentChal cache
    else
      let (drKey, roCache') ← evalHkdfOrRo true P st.roCache prep.secrets
      let ((rk1, ck1_0), rootRoCache') ← evalRootKdfOrRo true P st.rootRoCache drKey.rootKey
        prep.dhRatchet
      let mkSeed := P.chainKdfSeed ck1_0
      let ck1_1 := P.chainKdfNext ck1_0
      match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none =>
        let (resp, hst') := prep.finish none
        pure ((resp, { toAuthHybridState := hst', recvCount := recvCount',
                       mkSaltCache := hst.mkSaltCache, slots := hst.slots }), cache)
      | some (_pqrStB, spqrSalt?) =>
        let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
        let ad := firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
        let res? := (P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
          (drKey, rk1, ck1_1, pt, roCache', rootRoCache'))
        let (resp, hst') := prep.finish res?
        pure ((resp, { toAuthHybridState := hst', recvCount := recvCount',
                       mkSaltCache := hst.mkSaltCache, slots := hst.slots }), cache)
def authMkSlotsStepRedProb (S : Setup) (P : Primitives) (idx : Nat) {Cache : Type}
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache) :
    ProbComp ((authSpec S).Range q × ((AuthHybridStateFixed S × Bool) × Cache)) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.noneResp, ((hst, sentChal), cache))
    else authMkSlotsSendRedProb S P idx evalPrf (.sendOPK u i) u bundle m0 m1 hst sentChal cache
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.noneResp, ((hst, sentChal), cache))
    else authMkSlotsSendRedProb S P idx evalPrf (.sendNoOPK u i) u bundle m0 m1 hst sentChal cache
  | .recvOPK k j o msg => do
    let prep? := prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState
    let ((resp, hst'), cache') ← authMkSlotsRecvRedProb S P idx evalPrf msg prep? hst sentChal cache
    pure (resp, ((hst', sentChal), cache'))
  | .recvNoOPK k j l msg => do
    let prep? := prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState
    let ((resp, hst'), cache') ← authMkSlotsRecvRedProb S P idx evalPrf msg prep? hst sentChal cache
    pure (resp, ((hst', sentChal), cache'))
  | qOther => do
    let (resp, hst') ← authCkOtherStep S P qOther hst
    pure (resp, ((hst', sentChal), cache))
def authMkSlotsRedProbImpl (S : Setup) (P : Primitives) (idx : Nat) {Cache : Type}
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache)) :
    QueryImpl (authSpec S) (StateT ((AuthHybridStateFixed S × Bool) × Cache) ProbComp) :=
  fun q => StateT.mk (fun ((hst, sentChal), cache) =>
    authMkSlotsStepRedProb S P idx evalPrf q hst sentChal cache)
theorem simulateQ_authMkSendReduction {Cache : Type} (S : Setup) (P : Primitives) (idx : Nat)
    (impl : QueryImpl prfMsgKeysSpec (StateT Cache ProbComp))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache)
    (hPrin : hst.toAuthHybridState.base.principals.length ≤ S.N_dh)
    (hSpk : hst.toAuthHybridState.base.spkBundles.length ≤ S.N_dh)
    (hOpk : hst.toAuthHybridState.base.opkEntries.length ≤ S.N_dh)
    (hAdv : ValidAdvKeysPow8 P hst.toAuthHybridState.base.advKeys) :
    let fullImpl := (primBaseImpl P).liftTarget (StateT Cache ProbComp) + impl
    let evalPrf := fun s c => (impl (.derive (effectiveHkdfSaltBytes s))).run c
    (simulateQ fullImpl (authMkSendReduction S idx sid u bundle m0 m1 hst sentChal)).run cache =
      (fun (resp, ((hst', sentChal'), cache')) => (((resp, hst'), sentChal'), cache')) <$>
        authMkSlotsSendRedProb S P idx evalPrf sid u bundle m0 m1 hst sentChal cache := by
  intro fullImpl evalPrf
  unfold authMkSendReduction authMkSlotsSendRedProb
  dsimp only
  rw [simulateQ_prfMkFullImpl_embedPrimMk_bind,
      simulateQ_prepareAuthSendMkSlotsH3Prim S P sid u bundle m0 m1 hst hPrin hSpk hOpk hAdv,
      map_bind]
  congr 1; funext prep
  cases prep with
  | done resp hst' =>
    simp [StateT.run_pure]
  | idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk
      drKey rk1 spqrSalt? pqRatchetMsg msgPlain =>
    dsimp only
    split
    · rw [simulateQ_prfMkFullImpl_embedUnifMk_bind]
      simp only [map_bind]
      congr 1; funext ck1_1
      rw [simulateQ_prfMkFullImpl_deriveMkQ_bind]
      congr 1; funext ⟨deriveMessageKeys, cache'⟩
      dsimp only
      rw [simulateQ_prfMkFullImpl_embedPrimMk_bind,
          simulateQ_finishAuthSendMkSlotsH3Prim S P sid uEntry peerPrincipal? bundle m0 m1
            ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1
            spqrSalt? pqRatchetMsg msgPlain { hst with slots := (hst.slots.allocSend sid).2 }
            deriveMessageKeys hPrin hSpk hOpk,
          pure_bind]
      simp [StateT.run_pure]
    · split
      · rw [simulateQ_prfMkFullImpl_embedUnifMk_bind]
        simp only [map_bind]
        congr 1; funext ck1_1
        rw [simulateQ_prfMkFullImpl_embedUnifMk_bind]
        congr 1; funext deriveMessageKeys
        rw [simulateQ_prfMkFullImpl_embedPrimMk_bind,
            simulateQ_finishAuthSendMkSlotsH3Prim S P sid uEntry peerPrincipal? bundle m0 m1
              ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1
              spqrSalt? pqRatchetMsg msgPlain { hst with slots := (hst.slots.allocSend sid).2 }
              deriveMessageKeys hPrin hSpk hOpk,
            pure_bind]
        simp [StateT.run_pure]
      · rw [simulateQ_prfMkFullImpl_embedUnifMk_bind]
        simp only [map_bind]
        congr 1; funext mkSeed
        rw [simulateQ_prfMkFullImpl_embedUnifMk_bind]
        congr 1; funext ck1_1
        rw [simulateQ_prfMkFullImpl_embedPrimMk_bind, simulateQ_primQ_deriveMsgKeys, pure_bind,
            simulateQ_prfMkFullImpl_embedPrimMk_bind,
            simulateQ_finishAuthSendMkSlotsH3Prim S P sid uEntry peerPrincipal? bundle m0 m1
              ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
              spqrSalt? pqRatchetMsg msgPlain { hst with slots := (hst.slots.allocSend sid).2 }
              _ hPrin hSpk hOpk,
            pure_bind]
        simp [StateT.run_pure]
theorem authMkSlotsSendRedProb_cacheAuthAdvKeysFixed {Cache : Type} (S : Setup) (P : Primitives)
    (idx : Nat)
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache) :
    authMkSlotsSendRedProb S P idx evalPrf sid u bundle m0 m1 (cacheAuthAdvKeysFixed P hst) sentChal
      cache =
      (fun (resp, ((hst', sentChal'), cache')) =>
        (resp, ((cacheAuthAdvKeysFixed P hst', sentChal'), cache'))) <$>
      authMkSlotsSendRedProb S P idx evalPrf sid u bundle m0 m1 hst sentChal cache := by
  unfold authMkSlotsSendRedProb
  rw [prepareAuthSendMkSlotsH3_cacheAuthAdvKeysFixed, bind_map_left, map_bind]
  congr 1; funext prep
  cases prep with
  | done resp hst' =>
    simp [PreparedAuthSend.mapState]
  | idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk
      drKey rk1 spqrSalt? pqRatchetMsg msgPlain =>
    dsimp only [PreparedAuthSend.mapState]
    have hSlots : (cacheAuthAdvKeysFixed P hst).slots = hst.slots := rfl
    rw [hSlots]
    split
    · simp only [map_bind]; rfl
    · split
      · simp only [map_bind]; rfl
      · simp only [map_bind]; rfl
theorem authMkSendRedProb_cacheAuthAdvKeysFixed {Cache : Type} (S : Setup) (P : Primitives)
  (idx : Nat)
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache) :
    authMkSendRedProb S P idx evalPrf sid u bundle m0 m1 (cacheAuthAdvKeysFixed P hst) sentChal
      cache =
      (fun (resp, ((hst', sentChal'), cache')) =>
        (resp, ((cacheAuthAdvKeysFixed P hst', sentChal'), cache'))) <$>
      authMkSendRedProb S P idx evalPrf sid u bundle m0 m1 hst sentChal cache := by
  unfold authMkSendRedProb
  rw [prepareAuthSendMk_cacheAuthAdvKeysFixed, bind_map_left, map_bind]
  congr 1; funext prep
  cases prep with
  | done resp hst' =>
    simp [PreparedAuthSend.mapState]
  | idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk
      drKey rk1 spqrSalt? pqRatchetMsg msgPlain =>
    dsimp only [PreparedAuthSend.mapState]
    split
    · simp only [map_bind]; rfl
    · split
      · simp only [map_bind]; rfl
      · simp only [map_bind]; rfl
theorem simulateQ_finishAuthRecvUnmatchedReduction {Cache : Type} (S : Setup) (P : Primitives)
  (idx : Nat)
    (impl : QueryImpl prfMsgKeysSpec (StateT Cache ProbComp))
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S) (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (rSlot recvCount' : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (sentChal : Bool) (cache : Cache)
    (hPrin : prep.finishTag.hstDec.base.principals.length ≤ S.N_dh)
    (hSentOPK : prep.finishTag.hstDec.base.sentOPKEvents.length ≤ S.N_dh)
    (hSentNoOPK : prep.finishTag.hstDec.base.sentNoOPKEvents.length ≤ S.N_dh) :
    let fullImpl := (primBaseImpl P).liftTarget (StateT Cache ProbComp) + impl
    let evalPrf := fun s c => (impl (.derive (effectiveHkdfSaltBytes s))).run c
    (simulateQ fullImpl
      (finishAuthRecvUnmatchedReduction S idx msg prep drKey rk1 spqrSalt? rSlot recvCount'
        mkSaltCache sentChal)).run cache =
      finishAuthRecvUnmatchedRedProb S P idx evalPrf msg (prep.toPure true P) drKey rk1
        spqrSalt? rSlot recvCount' mkSaltCache sentChal cache := by
  intro fullImpl evalPrf
  unfold finishAuthRecvUnmatchedReduction finishAuthRecvUnmatchedSlotsReduction
    finishAuthRecvUnmatchedRedProb
  dsimp only
  split
  · rw [simulateQ_prfMkFullImpl_embedUnifMk_bind]
    congr 1; funext ck1_1
    cases sentChal
    · simp only [Bool.not_false, ↓reduceIte, simulateQ_prfMkFullImpl_deriveMkQ_bind]
      congr 1; funext ⟨deriveMessageKeys, cache'⟩
      rw [simulateQ_prfMkFullImpl_embedPrimMk,
          ← finishAuthRecvMkPrim,
          simulateQ_finishAuthRecvMkPrim S P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache deriveMessageKeys
            hPrin hSentOPK hSentNoOPK,
          pure_bind]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        simulateQ_prfMkFullImpl_embedUnifMk_bind]
      congr 1; funext deriveMessageKeys
      rw [pure_bind, simulateQ_prfMkFullImpl_embedPrimMk,
          ← finishAuthRecvMkPrim,
          simulateQ_finishAuthRecvMkPrim S P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache deriveMessageKeys
            hPrin hSentOPK hSentNoOPK,
          pure_bind]
  · split
    · rw [simulateQ_prfMkFullImpl_embedUnifMk_bind]
      congr 1; funext ck1_1
      rw [simulateQ_prfMkFullImpl_embedUnifMk_bind]
      congr 1; funext deriveMessageKeys
      rw [simulateQ_prfMkFullImpl_embedPrimMk,
          ← finishAuthRecvMkPrim,
          simulateQ_finishAuthRecvMkPrim S P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache deriveMessageKeys
            hPrin hSentOPK hSentNoOPK,
          pure_bind]
    · rw [simulateQ_prfMkFullImpl_embedUnifMk_bind]
      congr 1; funext mkSeed
      rw [simulateQ_prfMkFullImpl_embedUnifMk_bind]
      congr 1; funext ck1_1
      rw [simulateQ_prfMkFullImpl_embedPrimMk_bind, simulateQ_primQ_deriveMsgKeys, pure_bind,
          simulateQ_prfMkFullImpl_embedPrimMk,
          ← finishAuthRecvMkPrim,
          simulateQ_finishAuthRecvMkPrim S P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache _
            hPrin hSentOPK hSentNoOPK,
          pure_bind]
theorem simulateQ_matchedSameEphMkReduction {Cache : Type} (S : Setup) (P : Primitives) (idx : Nat)
    (impl : QueryImpl prfMsgKeysSpec (StateT Cache ProbComp))
    (s : IdealAuthSession S) (spqrSalt? : Option Bytes) (recvCount : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys))) (cache : Cache) :
    let fullImpl := (primBaseImpl P).liftTarget (StateT Cache ProbComp) + impl
    let evalPrf := fun s c => (impl (.derive (effectiveHkdfSaltBytes s))).run c
    (simulateQ fullImpl (matchedSameEphMkReduction S idx s spqrSalt? recvCount mkSaltCache)).run
      cache =
      matchedSameEphMkRedProb S P idx evalPrf s spqrSalt? recvCount mkSaltCache cache := by
  intro fullImpl evalPrf
  unfold matchedSameEphMkReduction matchedSameEphMkSlotsReduction matchedSameEphMkRedProb
  dsimp only
  split
  · split
    · rfl
    · cases mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
      | some entry => rcases entry with ⟨_, ⟨_, mk⟩⟩; rfl
      | none =>
        rw [simulateQ_prfMkFullImpl_deriveMkQ_bind]
        rfl
  · split
    · split
      · rfl
      · cases mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
        | some entry => rcases entry with ⟨_, ⟨_, mk⟩⟩; rfl
        | none =>
          rw [simulateQ_prfMkFullImpl_embedUnifMk_bind]
          rfl
    · rw [simulateQ_prfMkFullImpl_embedPrimMk_bind, simulateQ_primQ_deriveMsgKeys, pure_bind]
      rfl
theorem simulateQ_finishAuthRecvUnmatchedSlotsReduction {Cache : Type} (S : Setup) (P : Primitives)
    (idx : Nat)
    (impl : QueryImpl prfMsgKeysSpec (StateT Cache ProbComp))
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S) (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (rSlot recvCount' : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (slots' : AuthSlotState) (sentChal : Bool) (cache : Cache)
    (hPrin : prep.finishTag.hstDec.base.principals.length ≤ S.N_dh)
    (hSentOPK : prep.finishTag.hstDec.base.sentOPKEvents.length ≤ S.N_dh)
    (hSentNoOPK : prep.finishTag.hstDec.base.sentNoOPKEvents.length ≤ S.N_dh) :
    let fullImpl := (primBaseImpl P).liftTarget (StateT Cache ProbComp) + impl
    let evalPrf := fun s c => (impl (.derive (effectiveHkdfSaltBytes s))).run c
    (simulateQ fullImpl
      (finishAuthRecvUnmatchedSlotsReduction S idx msg prep drKey rk1 spqrSalt? rSlot recvCount'
        mkSaltCache slots' sentChal)).run cache =
      finishAuthRecvUnmatchedSlotsRedProb S P idx evalPrf msg (prep.toPure true P) drKey rk1
        spqrSalt? rSlot recvCount' mkSaltCache slots' sentChal cache := by
  intro fullImpl evalPrf
  unfold finishAuthRecvUnmatchedSlotsReduction finishAuthRecvUnmatchedSlotsRedProb
  dsimp only
  split
  · rw [simulateQ_prfMkFullImpl_embedUnifMk_bind]
    congr 1; funext ck1_1
    cases sentChal
    · simp only [Bool.not_false, ↓reduceIte, simulateQ_prfMkFullImpl_deriveMkQ_bind]
      congr 1; funext ⟨deriveMessageKeys, cache'⟩
      rw [simulateQ_prfMkFullImpl_embedPrimMk,
          simulateQ_finishAuthRecvMkSlotsH3Prim S P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache
            slots' deriveMessageKeys hPrin hSentOPK hSentNoOPK,
          pure_bind]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        simulateQ_prfMkFullImpl_embedUnifMk_bind]
      congr 1; funext deriveMessageKeys
      rw [pure_bind, simulateQ_prfMkFullImpl_embedPrimMk,
          simulateQ_finishAuthRecvMkSlotsH3Prim S P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache
            slots' deriveMessageKeys hPrin hSentOPK hSentNoOPK,
          pure_bind]
  · split
    · rw [simulateQ_prfMkFullImpl_embedUnifMk_bind]
      congr 1; funext ck1_1
      rw [simulateQ_prfMkFullImpl_embedUnifMk_bind]
      congr 1; funext deriveMessageKeys
      rw [simulateQ_prfMkFullImpl_embedPrimMk,
          simulateQ_finishAuthRecvMkSlotsH3Prim S P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache
            slots' deriveMessageKeys hPrin hSentOPK hSentNoOPK,
          pure_bind]
    · rw [simulateQ_prfMkFullImpl_embedUnifMk_bind]
      congr 1; funext mkSeed
      rw [simulateQ_prfMkFullImpl_embedUnifMk_bind]
      congr 1; funext ck1_1
      rw [simulateQ_prfMkFullImpl_embedPrimMk_bind, simulateQ_primQ_deriveMsgKeys, pure_bind,
          simulateQ_prfMkFullImpl_embedPrimMk,
          simulateQ_finishAuthRecvMkSlotsH3Prim S P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache
            slots' _ hPrin hSentOPK hSentNoOPK,
          pure_bind]
theorem simulateQ_matchedSameEphMkSlotsReduction {Cache : Type} (S : Setup) (P : Primitives)
    (idx : Nat)
    (impl : QueryImpl prfMsgKeysSpec (StateT Cache ProbComp))
    (s : IdealAuthSession S) (sIdx : Nat) (spqrSalt? : Option Bytes) (recvCount : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys))) (cache : Cache) :
    let fullImpl := (primBaseImpl P).liftTarget (StateT Cache ProbComp) + impl
    let evalPrf := fun s c => (impl (.derive (effectiveHkdfSaltBytes s))).run c
    (simulateQ fullImpl
      (matchedSameEphMkSlotsReduction S idx s sIdx spqrSalt? recvCount mkSaltCache)).run cache =
      matchedSameEphMkSlotsRedProb S P idx evalPrf s sIdx spqrSalt? recvCount mkSaltCache cache := by
  intro fullImpl evalPrf
  unfold matchedSameEphMkSlotsReduction matchedSameEphMkSlotsRedProb
  dsimp only
  split
  · split
    · rfl
    · cases mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
      | some entry => rcases entry with ⟨_, ⟨_, mk⟩⟩; rfl
      | none =>
        rw [simulateQ_prfMkFullImpl_deriveMkQ_bind]
        rfl
  · split
    · split
      · rfl
      · cases mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
        | some entry => rcases entry with ⟨_, ⟨_, mk⟩⟩; rfl
        | none =>
          rw [simulateQ_prfMkFullImpl_embedUnifMk_bind]
          rfl
    · rw [simulateQ_prfMkFullImpl_embedPrimMk_bind, simulateQ_primQ_deriveMsgKeys, pure_bind]
      rfl
theorem simulateQ_authMkRecvReduction {Cache : Type} (S : Setup) (P : Primitives) (idx : Nat)
    (impl : QueryImpl prfMsgKeysSpec (StateT Cache ProbComp))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecvPrim S))
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache)
    (hPrep : ∀ prep, prep? = some prep →
      prep.finishTag.hstDec.base.sentOPKEvents.length ≤ S.N_dh ∧
      prep.finishTag.hstDec.base.sentNoOPKEvents.length ≤ S.N_dh ∧
      prep.finishTag.hstDec.base.principals.length ≤ S.N_dh) :
    let fullImpl := (primBaseImpl P).liftTarget (StateT Cache ProbComp) + impl
    let evalPrf := fun s c => (impl (.derive (effectiveHkdfSaltBytes s))).run c
    (simulateQ fullImpl (authMkRecvReduction S idx msg prep? hst sentChal)).run cache =
      authMkSlotsRecvRedProb S P idx evalPrf msg (prep?.map (PreparedAuthRecvPrim.toPure true P))
        hst sentChal cache := by
  intro fullImpl evalPrf
  unfold authMkRecvReduction authMkSlotsRecvRedProb
  cases prep? with
  | none => rfl
  | some prep =>
    obtain ⟨hSentOPK, hSentNoOPK, hPrin⟩ := hPrep prep rfl
    dsimp only [Option.map, PreparedAuthRecvPrim.toPure]
    split
    · cases prep.matchedSess? with
      | some s =>
        dsimp only
        split
        · rw [simulateQ_prfMkFullImpl_embedPrimMk_bind, simulateQ_primQ_spqrInitRecv, pure_bind]
          cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            dsimp only
            rw [simulateQ_prfMkFullImpl_embedPrimMk_bind,
                simulateQ_recvFinishTag_runPrim S true P prep.finishTag none hPrin hSentOPK
                  hSentNoOPK,
                pure_bind]
            rfl
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            dsimp only
            rw [simulateQ_bind, StateT.run_bind,
                simulateQ_matchedSameEphMkSlotsReduction S P idx impl s
                  (hst.slots.lookupSendOrZero s.sid) spqrSalt? hst.recvCount hst.mkSaltCache cache]
            congr 1; funext ⟨⟨mk, mkSaltCache'⟩, cache'⟩
            rw [simulateQ_prfMkFullImpl_embedPrimMk,
                simulateQ_finishAuthRecvMkSlotsH3Prim S P msg prep s.drKey s.rk1 s.ck1_1 _
                  mkSaltCache' hst.slots mk hPrin hSentOPK hSentNoOPK,
                pure_bind]
            rfl
        · rw [simulateQ_prfMkFullImpl_embedUnifMk_bind]
          congr 1; funext rk1
          rw [simulateQ_prfMkFullImpl_embedPrimMk_bind, simulateQ_primQ_spqrInitRecv, pure_bind]
          cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            dsimp only
            rw [simulateQ_prfMkFullImpl_embedPrimMk_bind,
                simulateQ_recvFinishTag_runPrim S true P prep.finishTag none hPrin hSentOPK
                  hSentNoOPK,
                pure_bind]
            rfl
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            exact simulateQ_finishAuthRecvUnmatchedSlotsReduction S P idx impl msg prep s.drKey rk1
              spqrSalt? _ _ hst.mkSaltCache _ sentChal cache hPrin hSentOPK hSentNoOPK
      | none =>
        dsimp only
        rw [simulateQ_prfMkFullImpl_embedUnifMk_bind]
        congr 1; funext drKey
        rw [simulateQ_prfMkFullImpl_embedUnifMk_bind]
        congr 1; funext rk1
        rw [simulateQ_prfMkFullImpl_embedPrimMk_bind, simulateQ_primQ_spqrInitRecv, pure_bind]
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          dsimp only
          rw [simulateQ_prfMkFullImpl_embedPrimMk_bind,
              simulateQ_recvFinishTag_runPrim S true P prep.finishTag none hPrin hSentOPK
                hSentNoOPK,
              pure_bind]
          rfl
        | some pqr =>
          rcases pqr with ⟨_, spqrSalt?⟩
          exact simulateQ_finishAuthRecvUnmatchedSlotsReduction S P idx impl msg prep drKey rk1
            spqrSalt? _ _ hst.mkSaltCache _ sentChal cache hPrin hSentOPK hSentNoOPK
    · rw [simulateQ_prfMkFullImpl_embedUnifMk_bind]
      simp only [evalHkdfOrRo_true_eq_pure, evalRootKdfOrRo_true_eq_pure]
      congr 1; funext ⟨drKey, roCache'⟩
      rw [simulateQ_prfMkFullImpl_embedUnifMk_bind]
      congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      rw [simulateQ_prfMkFullImpl_embedPrimMk_bind, simulateQ_primQ_chainKdfSeed, pure_bind,
          simulateQ_prfMkFullImpl_embedPrimMk_bind, simulateQ_primQ_chainKdfNext, pure_bind,
          simulateQ_prfMkFullImpl_embedPrimMk_bind, simulateQ_primQ_spqrInitRecv, pure_bind]
      cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none =>
        dsimp only
        rw [simulateQ_prfMkFullImpl_embedPrimMk_bind,
            simulateQ_recvFinishTag_runPrim S true P prep.finishTag none hPrin hSentOPK hSentNoOPK,
            pure_bind]
        rfl
      | some pqr =>
        rcases pqr with ⟨_, spqrSalt?⟩
        dsimp only
        rw [simulateQ_prfMkFullImpl_embedPrimMk_bind, simulateQ_primQ_deriveMsgKeys, pure_bind,
            simulateQ_prfMkFullImpl_embedPrimMk_bind, simulateQ_primQ_aeadDec, pure_bind,
            simulateQ_prfMkFullImpl_embedPrimMk_bind,
            simulateQ_recvFinishTag_runPrim S true P prep.finishTag _ hPrin hSentOPK hSentNoOPK,
            pure_bind]
        rfl
theorem finishAuthRecvUnmatchedRedProb_cacheAuthAdvKeysFixed {Cache : Type} (S : Setup)
  (P : Primitives) (idx : Nat)
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S) (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (rSlot recvCount' : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (sentChal : Bool) (cache : Cache) :
    finishAuthRecvUnmatchedRedProb S P idx evalPrf msg
      ((prep.mapState (cacheAuthAdvKeys P)).toPure true P)
      drKey rk1 spqrSalt? rSlot recvCount' mkSaltCache sentChal cache =
    (fun ((resp, hst'), cache') => ((resp, cacheAuthAdvKeysFixed P hst'), cache')) <$>
      finishAuthRecvUnmatchedRedProb S P idx evalPrf msg (prep.toPure true P)
        drKey rk1 spqrSalt? rSlot recvCount' mkSaltCache sentChal cache := by
  unfold finishAuthRecvUnmatchedRedProb
  dsimp only
  split
  · simp only [map_bind]
    congr 1; funext ck1_1
    cases sentChal
    · simp only [Bool.not_false, ↓reduceIte, map_bind]
      congr 1; funext ⟨deriveMessageKeys, cache'⟩
      simp [finishAuthRecvMk_mapState_cacheAuthAdvKeys]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, map_bind]
      congr 1; funext deriveMessageKeys
      simp [finishAuthRecvMk_mapState_cacheAuthAdvKeys]
  · split
    · simp only [map_bind]
      congr 1; funext ck1_1
      congr 1; funext deriveMessageKeys
      simp [finishAuthRecvMk_mapState_cacheAuthAdvKeys]
    · simp only [map_bind]
      congr 1; funext mkSeed
      congr 1; funext ck1_1
      simp [finishAuthRecvMk_mapState_cacheAuthAdvKeys]
theorem authMkRecvRedProb_cacheAuthAdvKeysFixed {Cache : Type} (S : Setup) (P : Primitives)
  (idx : Nat)
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecvPrim S))
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache) :
    authMkRecvRedProb S P idx evalPrf msg
      ((prep?.map (PreparedAuthRecvPrim.mapState (cacheAuthAdvKeys P))).map
        (PreparedAuthRecvPrim.toPure true P))
      (cacheAuthAdvKeysFixed P hst) sentChal cache =
    (fun ((resp, hst'), cache') => ((resp, cacheAuthAdvKeysFixed P hst'), cache')) <$>
      authMkRecvRedProb S P idx evalPrf msg (prep?.map (PreparedAuthRecvPrim.toPure true P))
        hst sentChal cache := by
  unfold authMkRecvRedProb
  cases prep? with
  | none =>
    simp [cacheAuthAdvKeysFixed]
  | some prep =>
    dsimp only [Option.map]
    have hMatch : ((prep.mapState (cacheAuthAdvKeys P)).toPure true P).matchedSess? =
        (prep.toPure true P).matchedSess? := rfl
    have hHon : ((prep.mapState (cacheAuthAdvKeys P)).toPure true P).isUncorruptedHonestSender =
        (prep.toPure true P).isUncorruptedHonestSender := rfl
    have hEph : ((prep.mapState (cacheAuthAdvKeys P)).toPure true P).sameEph =
        (prep.toPure true P).sameEph := rfl
    have hSec : ((prep.mapState (cacheAuthAdvKeys P)).toPure true P).secrets =
        (prep.toPure true P).secrets := rfl
    have hDh : ((prep.mapState (cacheAuthAdvKeys P)).toPure true P).dhRatchet =
        (prep.toPure true P).dhRatchet := rfl
    have hKE : ((prep.mapState (cacheAuthAdvKeys P)).toPure true P).kEntry =
        (prep.toPure true P).kEntry := rfl
    have hRo : ((prep.mapState (cacheAuthAdvKeys P)).toPure true P).hstDec.base.roCache =
        (prep.toPure true P).hstDec.base.roCache := by
      simp [PreparedAuthRecvPrim.mapState, PreparedAuthRecvPrim.toPure]
    have hRootRo : ((prep.mapState (cacheAuthAdvKeys P)).toPure true P).hstDec.base.rootRoCache =
        (prep.toPure true P).hstDec.base.rootRoCache := by
      simp [PreparedAuthRecvPrim.mapState, PreparedAuthRecvPrim.toPure]
    have hRecvCnt : (cacheAuthAdvKeysFixed P hst).recvCount = hst.recvCount := rfl
    have hMkCache : (cacheAuthAdvKeysFixed P hst).mkSaltCache = hst.mkSaltCache := rfl
    rw [hMatch, hHon, hEph, hSec, hDh, hKE, hRo, hRootRo, hRecvCnt, hMkCache]
    split
    · cases (prep.toPure true P).matchedSess? with
      | some s =>
        dsimp only
        split
        · cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            unfold PreparedAuthRecvPrim.mapState PreparedAuthRecvPrim.toPure
            simp [cacheAuthAdvKeysFixed, recvFinishTag_mapState_toPure_fst,
                   recvFinishTag_mapState_toPure_snd]
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            dsimp only
            simp only [map_bind]
            congr 1; funext ⟨⟨mk, mkSaltCache'⟩, cache'⟩
            simp [finishAuthRecvMk_mapState_cacheAuthAdvKeys]
        · simp only [map_bind]
          congr 1; funext rk1
          cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            unfold PreparedAuthRecvPrim.mapState PreparedAuthRecvPrim.toPure
            simp [cacheAuthAdvKeysFixed, recvFinishTag_mapState_toPure_fst,
                   recvFinishTag_mapState_toPure_snd]
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            exact finishAuthRecvUnmatchedRedProb_cacheAuthAdvKeysFixed S P idx evalPrf msg prep
              s.drKey rk1 spqrSalt? _ _ hst.mkSaltCache sentChal cache
      | none =>
        dsimp only
        simp only [map_bind]
        congr 1; funext drKey
        congr 1; funext rk1
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          unfold PreparedAuthRecvPrim.mapState PreparedAuthRecvPrim.toPure
          simp [cacheAuthAdvKeysFixed, recvFinishTag_mapState_toPure_fst,
                 recvFinishTag_mapState_toPure_snd]
        | some pqr =>
          rcases pqr with ⟨_, spqrSalt?⟩
          exact finishAuthRecvUnmatchedRedProb_cacheAuthAdvKeysFixed S P idx evalPrf msg prep
            drKey rk1 spqrSalt? _ _ hst.mkSaltCache sentChal cache
    · simp only [map_bind]
      congr 1; funext ⟨drKey, roCache'⟩
      congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none =>
        unfold PreparedAuthRecvPrim.mapState PreparedAuthRecvPrim.toPure
        simp [cacheAuthAdvKeysFixed, recvFinishTag_mapState_toPure_fst,
               recvFinishTag_mapState_toPure_snd]
      | some pqr =>
        rcases pqr with ⟨_, spqrSalt?⟩
        unfold PreparedAuthRecvPrim.mapState PreparedAuthRecvPrim.toPure
        simp [cacheAuthAdvKeysFixed, recvFinishTag_mapState_toPure_fst,
               recvFinishTag_mapState_toPure_snd]
theorem finishAuthRecvUnmatchedSlotsRedProb_cacheAuthAdvKeysFixed {Cache : Type} (S : Setup)
    (P : Primitives) (idx : Nat)
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S) (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (rSlot recvCount' : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (slots' : AuthSlotState) (sentChal : Bool) (cache : Cache) :
    finishAuthRecvUnmatchedSlotsRedProb S P idx evalPrf msg
      ((prep.mapState (cacheAuthAdvKeys P)).toPure true P)
      drKey rk1 spqrSalt? rSlot recvCount' mkSaltCache slots' sentChal cache =
    (fun ((resp, hst'), cache') => ((resp, cacheAuthAdvKeysFixed P hst'), cache')) <$>
      finishAuthRecvUnmatchedSlotsRedProb S P idx evalPrf msg (prep.toPure true P)
        drKey rk1 spqrSalt? rSlot recvCount' mkSaltCache slots' sentChal cache := by
  unfold finishAuthRecvUnmatchedSlotsRedProb
  dsimp only
  split
  · simp only [map_bind]
    congr 1; funext ck1_1
    cases sentChal
    · simp only [Bool.not_false, ↓reduceIte, map_bind]
      congr 1; funext ⟨deriveMessageKeys, cache'⟩
      simp [finishAuthRecvMkSlotsH3_mapState_cacheAuthAdvKeys]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, map_bind]
      congr 1; funext deriveMessageKeys
      simp [finishAuthRecvMkSlotsH3_mapState_cacheAuthAdvKeys]
  · split
    · simp only [map_bind]
      congr 1; funext ck1_1
      congr 1; funext deriveMessageKeys
      simp [finishAuthRecvMkSlotsH3_mapState_cacheAuthAdvKeys]
    · simp only [map_bind]
      congr 1; funext mkSeed
      congr 1; funext ck1_1
      simp [finishAuthRecvMkSlotsH3_mapState_cacheAuthAdvKeys]
theorem authMkSlotsRecvRedProb_cacheAuthAdvKeysFixed {Cache : Type} (S : Setup) (P : Primitives)
    (idx : Nat)
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecvPrim S))
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache) :
    authMkSlotsRecvRedProb S P idx evalPrf msg
      ((prep?.map (PreparedAuthRecvPrim.mapState (cacheAuthAdvKeys P))).map
        (PreparedAuthRecvPrim.toPure true P))
      (cacheAuthAdvKeysFixed P hst) sentChal cache =
    (fun ((resp, hst'), cache') => ((resp, cacheAuthAdvKeysFixed P hst'), cache')) <$>
      authMkSlotsRecvRedProb S P idx evalPrf msg (prep?.map (PreparedAuthRecvPrim.toPure true P))
        hst sentChal cache := by
  unfold authMkSlotsRecvRedProb
  cases prep? with
  | none =>
    simp [cacheAuthAdvKeysFixed]
  | some prep =>
    dsimp only [Option.map]
    have hMatch : ((prep.mapState (cacheAuthAdvKeys P)).toPure true P).matchedSess? =
        (prep.toPure true P).matchedSess? := rfl
    have hHon : ((prep.mapState (cacheAuthAdvKeys P)).toPure true P).isUncorruptedHonestSender =
        (prep.toPure true P).isUncorruptedHonestSender := rfl
    have hEph : ((prep.mapState (cacheAuthAdvKeys P)).toPure true P).sameEph =
        (prep.toPure true P).sameEph := rfl
    have hSec : ((prep.mapState (cacheAuthAdvKeys P)).toPure true P).secrets =
        (prep.toPure true P).secrets := rfl
    have hDh : ((prep.mapState (cacheAuthAdvKeys P)).toPure true P).dhRatchet =
        (prep.toPure true P).dhRatchet := rfl
    have hKE : ((prep.mapState (cacheAuthAdvKeys P)).toPure true P).kEntry =
        (prep.toPure true P).kEntry := rfl
    have hRo : ((prep.mapState (cacheAuthAdvKeys P)).toPure true P).hstDec.base.roCache =
        (prep.toPure true P).hstDec.base.roCache := by
      simp [PreparedAuthRecvPrim.mapState, PreparedAuthRecvPrim.toPure]
    have hRootRo : ((prep.mapState (cacheAuthAdvKeys P)).toPure true P).hstDec.base.rootRoCache =
        (prep.toPure true P).hstDec.base.rootRoCache := by
      simp [PreparedAuthRecvPrim.mapState, PreparedAuthRecvPrim.toPure]
    have hRecvCnt : (cacheAuthAdvKeysFixed P hst).recvCount = hst.recvCount := rfl
    have hMkCache : (cacheAuthAdvKeysFixed P hst).mkSaltCache = hst.mkSaltCache := rfl
    have hSlots : (cacheAuthAdvKeysFixed P hst).slots = hst.slots := rfl
    rw [hMatch, hHon, hEph, hSec, hDh, hKE, hRo, hRootRo, hRecvCnt, hMkCache, hSlots]
    split
    · cases (prep.toPure true P).matchedSess? with
      | some s =>
        dsimp only
        split
        · cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            unfold PreparedAuthRecvPrim.mapState PreparedAuthRecvPrim.toPure
            simp [cacheAuthAdvKeysFixed, recvFinishTag_mapState_toPure_fst,
                   recvFinishTag_mapState_toPure_snd]
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            dsimp only
            simp only [map_bind]
            congr 1; funext ⟨⟨mk, mkSaltCache'⟩, cache'⟩
            simp [finishAuthRecvMkSlotsH3_mapState_cacheAuthAdvKeys]
        · simp only [map_bind]
          congr 1; funext rk1
          cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            unfold PreparedAuthRecvPrim.mapState PreparedAuthRecvPrim.toPure
            simp [cacheAuthAdvKeysFixed, recvFinishTag_mapState_toPure_fst,
                   recvFinishTag_mapState_toPure_snd]
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            exact finishAuthRecvUnmatchedSlotsRedProb_cacheAuthAdvKeysFixed S P idx evalPrf msg prep
              s.drKey rk1 spqrSalt? _ _ hst.mkSaltCache _ sentChal cache
      | none =>
        dsimp only
        simp only [map_bind]
        congr 1; funext drKey
        congr 1; funext rk1
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          unfold PreparedAuthRecvPrim.mapState PreparedAuthRecvPrim.toPure
          simp [cacheAuthAdvKeysFixed, recvFinishTag_mapState_toPure_fst,
                 recvFinishTag_mapState_toPure_snd]
        | some pqr =>
          rcases pqr with ⟨_, spqrSalt?⟩
          exact finishAuthRecvUnmatchedSlotsRedProb_cacheAuthAdvKeysFixed S P idx evalPrf msg prep
            drKey rk1 spqrSalt? _ _ hst.mkSaltCache _ sentChal cache
    · simp only [map_bind]
      congr 1; funext ⟨drKey, roCache'⟩
      congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none =>
        unfold PreparedAuthRecvPrim.mapState PreparedAuthRecvPrim.toPure
        simp [cacheAuthAdvKeysFixed, recvFinishTag_mapState_toPure_fst,
               recvFinishTag_mapState_toPure_snd]
      | some pqr =>
        rcases pqr with ⟨_, spqrSalt?⟩
        unfold PreparedAuthRecvPrim.mapState PreparedAuthRecvPrim.toPure
        simp [cacheAuthAdvKeysFixed, recvFinishTag_mapState_toPure_fst,
               recvFinishTag_mapState_toPure_snd]
theorem simulateQ_authMkStepReduction {Cache : Type} (S : Setup) (P : Primitives) (idx : Nat)
    (impl : QueryImpl prfMsgKeysSpec (StateT Cache ProbComp))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache)
    (hV : ValidAuthHybrid S P hst) :
    let fullImpl := (primBaseImpl P).liftTarget (StateT Cache ProbComp) + impl
    let evalPrf := fun s c => (impl (.derive (effectiveHkdfSaltBytes s))).run c
    (simulateQ fullImpl (authMkStepReduction S idx q (cacheAuthAdvKeysFixed P hst) sentChal)).run
      cache =
      (fun (resp, ((hst', sentChal'), cache')) =>
        (((resp, cacheAuthAdvKeysFixed P hst'), sentChal'), cache')) <$>
      authMkSlotsStepRedProb S P idx evalPrf q hst sentChal cache := by
  intro fullImpl evalPrf
  have hVC : ValidAuthHybrid S P (cacheAuthAdvKeysFixed P hst) :=
    (validAuthHybrid_cacheAuthAdvKeysFixed P hst).mpr hV
  have hAdv : ValidAdvKeysPow8 P (cacheAuthAdvKeysFixed P hst).toAuthHybridState.base.advKeys :=
    validAdvKeysPow8_cacheAuthAdvKeys P hst.toAuthHybridState
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authMkStepReduction authMkSlotsStepRedProb
    dsimp only
    split
    · simp [StateT.run_pure]
    · rw [simulateQ_authMkSendReduction S P idx impl (.sendOPK u i) u bundle m0 m1
            (cacheAuthAdvKeysFixed P hst) sentChal cache
            hVC.principals_le hVC.spkBundles_le hVC.opkEntries_le hAdv,
          authMkSlotsSendRedProb_cacheAuthAdvKeysFixed]
      simp [Functor.map_map]; rfl
  | sendNoOPK u i bundle m0 m1 =>
    unfold authMkStepReduction authMkSlotsStepRedProb
    dsimp only
    split
    · simp [StateT.run_pure]
    · rw [simulateQ_authMkSendReduction S P idx impl (.sendNoOPK u i) u bundle m0 m1
            (cacheAuthAdvKeysFixed P hst) sentChal cache
            hVC.principals_le hVC.spkBundles_le hVC.opkEntries_le hAdv,
          authMkSlotsSendRedProb_cacheAuthAdvKeysFixed]
      simp [Functor.map_map]; rfl
  | recvOPK k j o msg =>
    unfold authMkStepReduction authMkSlotsStepRedProb
    dsimp only
    rw [simulateQ_prfMkFullImpl_embedPrimMk_bind,
        simulateQ_prepareAuthHybridRecvOPKPrim S P k j o msg
          (cacheAuthAdvKeysFixed P hst).toAuthHybridState
          hVC.principals_le hVC.idealSessions_le hAdv,
        pure_bind]
    have hPrep : ∀ prep,
        prepareAuthHybridRecvOPKPure P k j o msg (cacheAuthAdvKeysFixed P hst).toAuthHybridState =
          some prep →
        prep.finishTag.hstDec.base.sentOPKEvents.length ≤ S.N_dh ∧
        prep.finishTag.hstDec.base.sentNoOPKEvents.length ≤ S.N_dh ∧
        prep.finishTag.hstDec.base.principals.length ≤ S.N_dh := by
      intro prep hp
      obtain ⟨hTag, hBase⟩ := prepareAuthHybridRecvOPKPure_finishTag_base P k j o msg _ prep hp
      rw [hTag, hBase]
      exact ⟨hVC.sentOPKEvents_le, hVC.sentNoOPKEvents_le, hVC.principals_le⟩
    rw [simulateQ_bind, StateT.run_bind,
        simulateQ_authMkRecvReduction S P idx impl msg _ (cacheAuthAdvKeysFixed P hst) sentChal
          cache hPrep]
    change (authMkSlotsRecvRedProb S P idx evalPrf msg
        ((prepareAuthHybridRecvOPKPure P k j o msg (cacheAuthAdvKeys P hst.toAuthHybridState)).map
          (PreparedAuthRecvPrim.toPure true P))
        (cacheAuthAdvKeysFixed P hst) sentChal cache >>= _) = _
    rw [prepareAuthHybridRecvOPKPure_cacheAuthAdvKeys,
        authMkSlotsRecvRedProb_cacheAuthAdvKeysFixed,
        prepareAuthHybridRecvOPKPure_map_toPure,
        bind_map_left, map_bind]
    congr 1
  | recvNoOPK k j l msg =>
    unfold authMkStepReduction authMkSlotsStepRedProb
    dsimp only
    rw [simulateQ_prfMkFullImpl_embedPrimMk_bind,
        simulateQ_prepareAuthHybridRecvNoOPKPrim S P k j l msg
          (cacheAuthAdvKeysFixed P hst).toAuthHybridState
          hVC.principals_le hVC.idealSessions_le hAdv,
        pure_bind]
    have hPrep : ∀ prep,
        prepareAuthHybridRecvNoOPKPure P k j l msg (cacheAuthAdvKeysFixed P hst).toAuthHybridState =
          some prep →
        prep.finishTag.hstDec.base.sentOPKEvents.length ≤ S.N_dh ∧
        prep.finishTag.hstDec.base.sentNoOPKEvents.length ≤ S.N_dh ∧
        prep.finishTag.hstDec.base.principals.length ≤ S.N_dh := by
      intro prep hp
      obtain ⟨hTag, hBase⟩ := prepareAuthHybridRecvNoOPKPure_finishTag_base P k j l msg _ prep hp
      rw [hTag, hBase]
      exact ⟨hVC.sentOPKEvents_le, hVC.sentNoOPKEvents_le, hVC.principals_le⟩
    rw [simulateQ_bind, StateT.run_bind,
        simulateQ_authMkRecvReduction S P idx impl msg _ (cacheAuthAdvKeysFixed P hst) sentChal
          cache hPrep]
    change (authMkSlotsRecvRedProb S P idx evalPrf msg
        ((prepareAuthHybridRecvNoOPKPure P k j l msg (cacheAuthAdvKeys P hst.toAuthHybridState)).map
          (PreparedAuthRecvPrim.toPure true P))
        (cacheAuthAdvKeysFixed P hst) sentChal cache >>= _) = _
    rw [prepareAuthHybridRecvNoOPKPure_cacheAuthAdvKeys,
        authMkSlotsRecvRedProb_cacheAuthAdvKeysFixed,
        prepareAuthHybridRecvNoOPKPure_map_toPure,
        bind_map_left, map_bind]
    congr 1
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _
  | roRootQuery _ _ | revealDhSecrets =>
    unfold authMkStepReduction authMkSlotsStepRedProb
    dsimp only
    rw [simulateQ_prfMkFullImpl_embedPrimMk_bind,
        simulateQ_stepAuthOtherPrim S P _ hst (by intro h; cases h) (by intro h; cases h),
        bind_map_left, map_bind]
    rfl
theorem validAuthHybrid_of_toAuthHybridState_eq {S : Setup} {P : Primitives}
    {hst1 hst2 : AuthHybridStateFixed S}
    (hV : ValidAuthHybrid S P hst1) (hEq : hst1.toAuthHybridState = hst2.toAuthHybridState) :
    ValidAuthHybrid S P hst2 := by
  rcases hV with ⟨h1, h2, h3, h4, h5, h6⟩
  rw [hEq] at h1 h2 h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, h6⟩
private theorem forall_mem_support_ite_mk {α : Type} (c : Bool) (t e : ProbComp α) (Q : α → Prop)
    (ht : ∀ x ∈ support t, Q x) (he : ∀ x ∈ support e, Q x) :
    ∀ x ∈ support (if c then t else e), Q x := by
  cases c <;> [exact he; exact ht]
theorem prepareAuthSendMk_validAuthHybrid {S : Setup} (P : Primitives)
    (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (hV : ValidAuthHybrid S P hst) :
    ∀ p ∈ support (prepareAuthSendMk S P sid u bundle m0 m1 hst),
      match p with
      | .done _ hst' => ValidAuthHybrid S P hst'
      | .idealMk _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        hst.toAuthHybridState.base.usedSendSessions.contains sid = false := by
  unfold prepareAuthSendMk
  dsimp only
  refine forall_mem_support_ite_mk _ _ _ _ (fun x hx => by simp at hx; subst hx; exact hV) ?_
  refine forall_mem_support_ite_mk _ _ _ _ (fun x hx => by simp at hx; subst hx; exact hV) ?_
  cases hFresh : hst.toAuthHybridState.base.usedSendSessions.contains sid
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · intro x hx; simp at hx; subst hx; exact hV
    · refine forall_mem_support_ite_mk _ _ _ _ (fun x hx => by simp at hx; subst hx; exact hV) ?_
      refine forall_mem_support_ite_mk _ _ _ _ (fun x hx => by simp at hx; subst hx; exact hV) ?_
      intro x hx
      simp only [MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨ekASk, _, kemCoins, _, ephASk, _, spqrCoins, _, hx⟩
      revert x hx
      refine forall_mem_support_ite_mk _ _ _ _ (fun x hx => by simp at hx; subst hx; exact hV) ?_
      cases P.kemEncaps bundle.pqspkB kemCoins with
      | none => intro x hx; simp at hx; subst hx; exact hV
      | some pair =>
        rcases pair with ⟨ss, kemCt⟩
        dsimp only
        refine forall_mem_support_ite_mk _ _ _ _ ?_ ?_
        · intro x hx
          simp only [MonadAttach.mem_support_bind] at hx
          rcases hx with ⟨drKey, _, rk1, _, hx⟩
          revert x hx
          cases P.spqrInitSend drKey.pqrKey spqrCoins with
          | none => intro x hx; simp at hx; subst hx; exact hV
          | some spqrVal =>
            rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
            intro x hx
            simp only [support_pure, Set.mem_singleton_iff] at hx
            subst hx; trivial
        · intro x hx
          simp only [MonadAttach.mem_support_bind] at hx
          rcases hx with ⟨⟨drKey, roCache'⟩, _, ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩, _, hx⟩
          revert x hx
          cases P.spqrInitSend drKey.pqrKey spqrCoins with
          | none => intro x hx; simp at hx; subst hx; exact hV
          | some spqrVal =>
            rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
            intro x hx
            simp only [support_pure, Set.mem_singleton_iff] at hx
            subst hx
            exact validAuthHybrid_of_toAuthHybridState_eq
              (validAuthHybrid_finishAuthHybridSend P sid hSend _ _ _ bundle m0 m1
                ekASk _ _ _ ephASk _ drKey rk1 ck1_0 _ _ _ _ _ _ _ _ roCache' rootRoCache' hst hV
                  hFresh) rfl
  · simp only [↓reduceIte]
    intro x hx; simp at hx; subst hx; exact hV
theorem authMkSendRedProb_validAuthHybrid {Cache : Type} (S : Setup) (P : Primitives) (idx : Nat)
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache)
    (hV : ValidAuthHybrid S P hst) :
    ∀ x ∈ support (authMkSendRedProb S P idx evalPrf sid u bundle m0 m1 hst sentChal cache),
      ValidAuthHybrid S P x.2.1.1 := by
  unfold authMkSendRedProb
  intro x hx
  simp only [MonadAttach.mem_support_bind] at hx
  rcases hx with ⟨prep, hprep, hx⟩
  have hVP := prepareAuthSendMk_validAuthHybrid P sid hSend u bundle m0 m1 hst hV prep hprep
  cases prep with
  | done resp hst' =>
    simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx; exact hVP
  | idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk
      drKey rk1 spqrSalt? pqRatchetMsg msgPlain =>
    have hFinish : ∀ mkSeed ck1_1 deriveMessageKeys,
        ValidAuthHybrid S P (finishAuthSendMk P sid uEntry peerPrincipal? bundle m0 m1
          ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
          spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys).2 :=
      fun mkSeed ck1_1 deriveMessageKeys =>
        validAuthHybrid_of_toAuthHybridState_eq
          (validAuthHybrid_finishAuthHybridSend P sid hSend uEntry peerPrincipal? _ bundle m0 m1
            ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] mkSeed ck1_1
            spqrSalt? pqRatchetMsg deriveMessageKeys _ _ msgPlain _ _ hst hV hVP) rfl
    dsimp only at hx
    split at hx
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨ck1_1, _, ⟨deriveMessageKeys, cache'⟩, _, rfl⟩
      exact hFinish [] ck1_1 deriveMessageKeys
    · split at hx
      · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨ck1_1, _, deriveMessageKeys, _, rfl⟩
        exact hFinish [] ck1_1 deriveMessageKeys
      · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨mkSeed, _, ck1_1, _, rfl⟩
        exact hFinish mkSeed ck1_1 _
theorem finishAuthRecvUnmatchedRedProb_validAuthHybrid {Cache : Type} (S : Setup) (P : Primitives)
  (idx : Nat)
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (msg : PreKeyMsg) (prep : PreparedAuthRecv S) (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (rSlot recvCount' : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (sentChal : Bool) (cache : Cache)
    (hFinish : ∀ res?, ValidAuthHybrid S P { toAuthHybridState := (prep.finish res?).2, recvCount :=
                                             recvCount' }) :
    ∀ x ∈ support (finishAuthRecvUnmatchedRedProb S P idx evalPrf msg prep drKey rk1
      spqrSalt? rSlot recvCount' mkSaltCache sentChal cache),
      ValidAuthHybrid S P x.1.2 := by
  unfold finishAuthRecvUnmatchedRedProb
  intro x hx
  dsimp only at hx
  split at hx
  · simp only [MonadAttach.mem_support_bind] at hx
    rcases hx with ⟨ck1_1, _, hx⟩
    cases sentChal
    · simp only [Bool.not_false, ↓reduceIte, MonadAttach.mem_support_bind, support_pure,
                  Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨deriveMessageKeys, cache'⟩, _, rfl⟩
      exact validAuthHybrid_of_toAuthHybridState_eq (hFinish _) rfl
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind,
                  MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨deriveMessageKeys, _, rfl⟩
      exact validAuthHybrid_of_toAuthHybridState_eq (hFinish _) rfl
  · split at hx
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨ck1_1, _, deriveMessageKeys, _, rfl⟩
      exact validAuthHybrid_of_toAuthHybridState_eq (hFinish _) rfl
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨mkSeed, _, ck1_1, _, rfl⟩
      exact validAuthHybrid_of_toAuthHybridState_eq (hFinish _) rfl
theorem authMkRecvRedProb_validAuthHybrid {Cache : Type} (S : Setup) (P : Primitives) (idx : Nat)
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache) (hV : ValidAuthHybrid S P hst)
    (hFinish : ∀ prep, prep? = some prep → ∀ res? recvCount',
      ValidAuthHybrid S P { toAuthHybridState := (prep.finish res?).2, recvCount := recvCount' }) :
    ∀ x ∈ support (authMkRecvRedProb S P idx evalPrf msg prep? hst sentChal cache),
      ValidAuthHybrid S P x.1.2 := by
  unfold authMkRecvRedProb
  cases prep? with
  | none =>
    intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
    exact validAuthHybrid_of_toAuthHybridState_eq hV rfl
  | some prep =>
    have hF := hFinish prep rfl
    dsimp only
    split
    · cases prep.matchedSess? with
      | some s =>
        dsimp only
        split
        · cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
            exact validAuthHybrid_of_toAuthHybridState_eq (hF none (hst.recvCount + 1)) rfl
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            intro x hx
            simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
            rcases hx with ⟨⟨⟨mk, mkSaltCache'⟩, cache'⟩, _, rfl⟩
            exact validAuthHybrid_of_toAuthHybridState_eq (hF _ (hst.recvCount + 1)) rfl
        · intro x hx
          simp only [MonadAttach.mem_support_bind] at hx
          rcases hx with ⟨rk1, _, hx⟩
          revert x hx
          cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
            exact validAuthHybrid_of_toAuthHybridState_eq (hF none (hst.recvCount + 1)) rfl
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            exact finishAuthRecvUnmatchedRedProb_validAuthHybrid S P idx evalPrf msg prep s.drKey
              rk1
              spqrSalt? _ _ hst.mkSaltCache sentChal cache (fun res? => hF res? (hst.recvCount + 1))
      | none =>
        dsimp only
        intro x hx
        simp only [MonadAttach.mem_support_bind] at hx
        rcases hx with ⟨drKey, _, rk1, _, hx⟩
        revert x hx
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
          exact validAuthHybrid_of_toAuthHybridState_eq (hF none (hst.recvCount + 1)) rfl
        | some pqr =>
          rcases pqr with ⟨_, spqrSalt?⟩
          exact finishAuthRecvUnmatchedRedProb_validAuthHybrid S P idx evalPrf msg prep drKey rk1
            spqrSalt? _ _ hst.mkSaltCache sentChal cache (fun res? => hF res? (hst.recvCount + 1))
    · intro x hx
      simp only [MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨⟨drKey, roCache'⟩, _, ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩, _, hx⟩
      revert x hx
      cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none =>
        intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
        exact validAuthHybrid_of_toAuthHybridState_eq (hF none (hst.recvCount + 1)) rfl
      | some pqr =>
        rcases pqr with ⟨_, spqrSalt?⟩
        intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
        exact validAuthHybrid_of_toAuthHybridState_eq (hF _ (hst.recvCount + 1)) rfl
theorem authMkStepRedProb_validAuthHybrid {Cache : Type} (S : Setup) (P : Primitives) (idx : Nat)
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache)
    (hV : ValidAuthHybrid S P hst) :
    ∀ x ∈ support (authMkStepRedProb S P idx evalPrf q hst sentChal cache),
      ValidAuthHybrid S P x.2.1.1 := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authMkStepRedProb; dsimp only
    split
    · intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx; exact hV
    · exact authMkSendRedProb_validAuthHybrid S P idx evalPrf (.sendOPK u i) trivial
        u bundle m0 m1 hst sentChal cache hV
  | sendNoOPK u i bundle m0 m1 =>
    unfold authMkStepRedProb; dsimp only
    split
    · intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx; exact hV
    · exact authMkSendRedProb_validAuthHybrid S P idx evalPrf (.sendNoOPK u i) trivial
        u bundle m0 m1 hst sentChal cache hV
  | recvOPK k j o msg =>
    unfold authMkStepRedProb; dsimp only
    intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨⟨resp, hst'⟩, cache'⟩, hmem, rfl⟩
    exact authMkRecvRedProb_validAuthHybrid S P idx evalPrf msg _ hst sentChal cache hV
      (fun prep hPrep res? recvCount' =>
        prepareAuthHybridRecvOPK_validAuthHybrid P k j o msg hst hV prep hPrep res? recvCount')
      ((resp, hst'), cache') hmem
  | recvNoOPK k j l msg =>
    unfold authMkStepRedProb; dsimp only
    intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨⟨resp, hst'⟩, cache'⟩, hmem, rfl⟩
    exact authMkRecvRedProb_validAuthHybrid S P idx evalPrf msg _ hst sentChal cache hV
      (fun prep hPrep res? recvCount' =>
        prepareAuthHybridRecvNoOPK_validAuthHybrid P k j l msg hst hV prep hPrep res? recvCount')
      ((resp, hst'), cache') hmem
  | initPrin u =>
    unfold authMkStepRedProb; dsimp only; intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
    exact authCkStepWith_validAuthHybrid S P (fun _ => do let a ← sampleBytes32; pure (a, a))
      (.initPrin u) hst hV (resp, hst') hmem
  | corruptIK u =>
    unfold authMkStepRedProb; dsimp only; intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
    exact authCkStepWith_validAuthHybrid S P (fun _ => do let a ← sampleBytes32; pure (a, a))
      (.corruptIK u) hst hV (resp, hst') hmem
  | genSPK u j =>
    unfold authMkStepRedProb; dsimp only; intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
    exact authCkStepWith_validAuthHybrid S P (fun _ => do let a ← sampleBytes32; pure (a, a))
      (.genSPK u j) hst hV (resp, hst') hmem
  | genOPK u j o =>
    unfold authMkStepRedProb; dsimp only; intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
    exact authCkStepWith_validAuthHybrid S P (fun _ => do let a ← sampleBytes32; pure (a, a))
      (.genOPK u j o) hst hV (resp, hst') hmem
  | registerKey sk =>
    unfold authMkStepRedProb; dsimp only; intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
    exact authCkStepWith_validAuthHybrid S P (fun _ => do let a ← sampleBytes32; pure (a, a))
      (.registerKey sk) hst hV (resp, hst') hmem
  | roQuery secrets =>
    unfold authMkStepRedProb; dsimp only; intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
    exact authCkStepWith_validAuthHybrid S P (fun _ => do let a ← sampleBytes32; pure (a, a))
      (.roQuery secrets) hst hV (resp, hst') hmem
  | roRootQuery rk dh =>
    unfold authMkStepRedProb; dsimp only; intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
    exact authCkStepWith_validAuthHybrid S P (fun _ => do let a ← sampleBytes32; pure (a, a))
      (.roRootQuery rk dh) hst hV (resp, hst') hmem
  | revealDhSecrets =>
    unfold authMkStepRedProb; dsimp only; intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
    exact authCkStepWith_validAuthHybrid S P (fun _ => do let a ← sampleBytes32; pure (a, a))
      .revealDhSecrets hst hV (resp, hst') hmem
theorem prepareAuthSendMkSlotsH3_validAuthHybrid {S : Setup} (P : Primitives)
    (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (hV : ValidAuthHybrid S P hst) :
    ∀ p ∈ support (prepareAuthSendMkSlotsH3 S P sid u bundle m0 m1 hst),
      match p with
      | .done _ hst' => ValidAuthHybrid S P hst'
      | .idealMk _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        hst.toAuthHybridState.base.usedSendSessions.contains sid = false := by
  unfold prepareAuthSendMkSlotsH3
  intro p hp
  rw [support_map, Set.mem_image] at hp
  rcases hp with ⟨p0, hp0, rfl⟩
  have hVP := prepareAuthSendMk_validAuthHybrid P sid hSend u bundle m0 m1 hst hV p0 hp0
  cases p0 with
  | done _ _ => exact validAuthHybrid_of_toAuthHybridState_eq hVP rfl
  | idealMk _ _ _ _ _ _ _ _ _ _ _ _ _ => exact hVP
theorem authMkSlotsSendRedProb_validAuthHybrid {Cache : Type} (S : Setup) (P : Primitives)
    (idx : Nat)
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache)
    (hV : ValidAuthHybrid S P hst) :
    ∀ x ∈ support (authMkSlotsSendRedProb S P idx evalPrf sid u bundle m0 m1 hst sentChal cache),
      ValidAuthHybrid S P x.2.1.1 := by
  unfold authMkSlotsSendRedProb
  intro x hx
  simp only [MonadAttach.mem_support_bind] at hx
  rcases hx with ⟨prep, hprep, hx⟩
  have hVP := prepareAuthSendMkSlotsH3_validAuthHybrid P sid hSend u bundle m0 m1 hst hV prep hprep
  cases prep with
  | done resp hst' =>
    simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx; exact hVP
  | idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk
      drKey rk1 spqrSalt? pqRatchetMsg msgPlain =>
    have hFinish : ∀ mkSeed ck1_1 deriveMessageKeys (hst1 : AuthHybridStateFixed S),
        hst1.toAuthHybridState = hst.toAuthHybridState →
        ValidAuthHybrid S P (finishAuthSendMkSlotsH3 P sid uEntry peerPrincipal? bundle m0 m1
          ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
          spqrSalt? pqRatchetMsg msgPlain hst1 deriveMessageKeys).2 :=
      fun mkSeed ck1_1 deriveMessageKeys hst1 hEq =>
        validAuthHybrid_of_toAuthHybridState_eq
          (validAuthHybrid_finishAuthHybridSend P sid hSend uEntry peerPrincipal? _ bundle m0 m1
            ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] mkSeed ck1_1
            spqrSalt? pqRatchetMsg deriveMessageKeys _ _ msgPlain _ _ hst hV hVP)
          (by unfold finishAuthSendMkSlotsH3 finishAuthSendMk; dsimp only; rw [hEq])
    dsimp only at hx
    split at hx
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨ck1_1, _, ⟨deriveMessageKeys, cache'⟩, _, rfl⟩
      exact hFinish [] ck1_1 deriveMessageKeys _ rfl
    · split at hx
      · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨ck1_1, _, deriveMessageKeys, _, rfl⟩
        exact hFinish [] ck1_1 deriveMessageKeys _ rfl
      · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨mkSeed, _, ck1_1, _, rfl⟩
        exact hFinish mkSeed ck1_1 _ _ rfl
theorem finishAuthRecvUnmatchedSlotsRedProb_validAuthHybrid {Cache : Type} (S : Setup)
    (P : Primitives) (idx : Nat)
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (msg : PreKeyMsg) (prep : PreparedAuthRecv S) (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (rSlot recvCount' : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (slots' : AuthSlotState) (sentChal : Bool) (cache : Cache)
    (hFinish : ∀ res?, ValidAuthHybrid S P { toAuthHybridState := (prep.finish res?).2, recvCount :=
                                             recvCount' }) :
    ∀ x ∈ support (finishAuthRecvUnmatchedSlotsRedProb S P idx evalPrf msg prep drKey rk1
      spqrSalt? rSlot recvCount' mkSaltCache slots' sentChal cache),
      ValidAuthHybrid S P x.1.2 := by
  unfold finishAuthRecvUnmatchedSlotsRedProb
  intro x hx
  dsimp only at hx
  split at hx
  · simp only [MonadAttach.mem_support_bind] at hx
    rcases hx with ⟨ck1_1, _, hx⟩
    cases sentChal
    · simp only [Bool.not_false, ↓reduceIte, MonadAttach.mem_support_bind, support_pure,
                  Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨deriveMessageKeys, cache'⟩, _, rfl⟩
      exact validAuthHybrid_of_toAuthHybridState_eq (hFinish _) rfl
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind,
                  MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨deriveMessageKeys, _, rfl⟩
      exact validAuthHybrid_of_toAuthHybridState_eq (hFinish _) rfl
  · split at hx
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨ck1_1, _, deriveMessageKeys, _, rfl⟩
      exact validAuthHybrid_of_toAuthHybridState_eq (hFinish _) rfl
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨mkSeed, _, ck1_1, _, rfl⟩
      exact validAuthHybrid_of_toAuthHybridState_eq (hFinish _) rfl
theorem authMkSlotsRecvRedProb_validAuthHybrid {Cache : Type} (S : Setup) (P : Primitives)
    (idx : Nat)
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache) (hV : ValidAuthHybrid S P hst)
    (hFinish : ∀ prep, prep? = some prep → ∀ res? recvCount',
      ValidAuthHybrid S P { toAuthHybridState := (prep.finish res?).2, recvCount := recvCount' }) :
    ∀ x ∈ support (authMkSlotsRecvRedProb S P idx evalPrf msg prep? hst sentChal cache),
      ValidAuthHybrid S P x.1.2 := by
  unfold authMkSlotsRecvRedProb
  cases prep? with
  | none =>
    intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
    exact validAuthHybrid_of_toAuthHybridState_eq hV rfl
  | some prep =>
    have hF := hFinish prep rfl
    dsimp only
    split
    · cases prep.matchedSess? with
      | some s =>
        dsimp only
        split
        · cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
            exact validAuthHybrid_of_toAuthHybridState_eq (hF none (hst.recvCount + 1)) rfl
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            intro x hx
            simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
            rcases hx with ⟨⟨⟨mk, mkSaltCache'⟩, cache'⟩, _, rfl⟩
            exact validAuthHybrid_of_toAuthHybridState_eq (hF _ (hst.recvCount + 1)) rfl
        · intro x hx
          simp only [MonadAttach.mem_support_bind] at hx
          rcases hx with ⟨rk1, _, hx⟩
          revert x hx
          cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
            exact validAuthHybrid_of_toAuthHybridState_eq (hF none (hst.recvCount + 1)) rfl
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            exact finishAuthRecvUnmatchedSlotsRedProb_validAuthHybrid S P idx evalPrf msg prep
              s.drKey rk1 spqrSalt? _ _ hst.mkSaltCache _ sentChal cache
              (fun res? => hF res? (hst.recvCount + 1))
      | none =>
        dsimp only
        intro x hx
        simp only [MonadAttach.mem_support_bind] at hx
        rcases hx with ⟨drKey, _, rk1, _, hx⟩
        revert x hx
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
          exact validAuthHybrid_of_toAuthHybridState_eq (hF none (hst.recvCount + 1)) rfl
        | some pqr =>
          rcases pqr with ⟨_, spqrSalt?⟩
          exact finishAuthRecvUnmatchedSlotsRedProb_validAuthHybrid S P idx evalPrf msg prep drKey
            rk1 spqrSalt? _ _ hst.mkSaltCache _ sentChal cache
            (fun res? => hF res? (hst.recvCount + 1))
    · intro x hx
      simp only [MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨⟨drKey, roCache'⟩, _, ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩, _, hx⟩
      revert x hx
      cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none =>
        intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
        exact validAuthHybrid_of_toAuthHybridState_eq (hF none (hst.recvCount + 1)) rfl
      | some pqr =>
        rcases pqr with ⟨_, spqrSalt?⟩
        intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
        exact validAuthHybrid_of_toAuthHybridState_eq (hF _ (hst.recvCount + 1)) rfl
theorem authMkSlotsStepRedProb_validAuthHybrid {Cache : Type} (S : Setup) (P : Primitives)
    (idx : Nat)
    (evalPrf : Option Bytes → Cache → ProbComp (MessageKeys × Cache))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache)
    (hV : ValidAuthHybrid S P hst) :
    ∀ x ∈ support (authMkSlotsStepRedProb S P idx evalPrf q hst sentChal cache),
      ValidAuthHybrid S P x.2.1.1 := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authMkSlotsStepRedProb; dsimp only
    split
    · intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx; exact hV
    · exact authMkSlotsSendRedProb_validAuthHybrid S P idx evalPrf (.sendOPK u i) trivial
        u bundle m0 m1 hst sentChal cache hV
  | sendNoOPK u i bundle m0 m1 =>
    unfold authMkSlotsStepRedProb; dsimp only
    split
    · intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx; exact hV
    · exact authMkSlotsSendRedProb_validAuthHybrid S P idx evalPrf (.sendNoOPK u i) trivial
        u bundle m0 m1 hst sentChal cache hV
  | recvOPK k j o msg =>
    unfold authMkSlotsStepRedProb; dsimp only
    intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨⟨resp, hst'⟩, cache'⟩, hmem, rfl⟩
    exact authMkSlotsRecvRedProb_validAuthHybrid S P idx evalPrf msg _ hst sentChal cache hV
      (fun prep hPrep res? recvCount' =>
        prepareAuthHybridRecvOPK_validAuthHybrid P k j o msg hst hV prep hPrep res? recvCount')
      ((resp, hst'), cache') hmem
  | recvNoOPK k j l msg =>
    unfold authMkSlotsStepRedProb; dsimp only
    intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨⟨resp, hst'⟩, cache'⟩, hmem, rfl⟩
    exact authMkSlotsRecvRedProb_validAuthHybrid S P idx evalPrf msg _ hst sentChal cache hV
      (fun prep hPrep res? recvCount' =>
        prepareAuthHybridRecvNoOPK_validAuthHybrid P k j l msg hst hV prep hPrep res? recvCount')
      ((resp, hst'), cache') hmem
  | initPrin u =>
    exact authMkStepRedProb_validAuthHybrid S P idx evalPrf (.initPrin u) hst sentChal cache hV
  | corruptIK u =>
    exact authMkStepRedProb_validAuthHybrid S P idx evalPrf (.corruptIK u) hst sentChal cache hV
  | genSPK u j =>
    exact authMkStepRedProb_validAuthHybrid S P idx evalPrf (.genSPK u j) hst sentChal cache hV
  | genOPK u k o =>
    exact authMkStepRedProb_validAuthHybrid S P idx evalPrf (.genOPK u k o) hst sentChal cache hV
  | registerKey sk =>
    exact authMkStepRedProb_validAuthHybrid S P idx evalPrf (.registerKey sk) hst sentChal cache hV
  | roQuery secrets =>
    exact authMkStepRedProb_validAuthHybrid S P idx evalPrf (.roQuery secrets) hst sentChal cache hV
  | roRootQuery rk dh =>
    exact authMkStepRedProb_validAuthHybrid S P idx evalPrf (.roRootQuery rk dh) hst sentChal cache
      hV
  | revealDhSecrets =>
    exact authMkStepRedProb_validAuthHybrid S P idx evalPrf .revealDhSecrets hst sentChal cache hV
theorem simulateQ_runWithPrfMkStep_eq_redProb {Cache α : Type} (S : Setup) (P : Primitives)
  (idx : Nat)
    (impl : QueryImpl prfMsgKeysSpec (StateT Cache ProbComp))
    (oa : OracleComp (unifSpec + authSpec S) α)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : Cache) (hV : ValidAuthHybrid S P hst)
    (obs1 : ((α × AuthHybridStateFixed S) × Bool) × Cache → ProbComp Bool)
    (obs2 : α × ((AuthHybridStateFixed S × Bool) × Cache) → ProbComp Bool)
    (hObs : ∀ a hst' sentChal' cache', ValidAuthHybrid S P hst' →
      obs1 (((a, cacheAuthAdvKeysFixed P hst'), sentChal'), cache') =
      obs2 (a, ((hst', sentChal'), cache'))) :
    let fullImpl := (primBaseImpl P).liftTarget (StateT Cache ProbComp) + impl
    let evalPrf := fun s c => (impl (.derive (effectiveHkdfSaltBytes s))).run c
    let fullRed := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT ((AuthHybridStateFixed S × Bool) × Cache) ProbComp) +
      authMkSlotsRedProbImpl S P idx evalPrf
    ((simulateQ fullImpl (runWithPrfMkStep (authMkStepReduction S idx) oa
        (cacheAuthAdvKeysFixed P hst) sentChal)).run cache >>= obs1) =
      ((simulateQ fullRed oa).run ((hst, sentChal), cache) >>= obs2) := by
  intro fullImpl evalPrf fullRed
  induction oa using OracleComp.inductionOn generalizing hst sentChal cache with
  | pure a =>
    rw [runWithPrfMkStep_pure]
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hObs a hst sentChal cache hV
  | query_bind q k ih =>
    rcases q with uq | gq
    · rw [runWithPrfMkStep_query_bind_inl, simulateQ_prfMkFullImpl_embedUnifMk_bind,
          simulateQ_run_query_inl_local, bind_assoc, bind_assoc]
      congr 1; funext u
      exact ih u hst sentChal cache hV
    · rw [runWithPrfMkStep_query_bind_inr, simulateQ_bind, StateT.run_bind,
          simulateQ_authMkStepReduction S P idx impl gq hst sentChal cache hV,
          bind_map_left, bind_assoc,
          simulateQ_run_query_inr_local, bind_assoc]
      refine bind_congr_of_support
        (authMkSlotsStepRedProb S P idx evalPrf gq hst sentChal cache) _ _ (fun x hx => ?_)
      rcases x with ⟨resp, ⟨⟨hst', sentChal'⟩, cache'⟩⟩
      exact ih resp hst' sentChal' cache'
        (authMkSlotsStepRedProb_validAuthHybrid S P idx evalPrf gq hst sentChal cache hV _ hx)
theorem simulateQ_authMkReductionRun_eq_redProb {Cache : Type} (S : Setup) (P : Primitives)
  (idx : Nat)
    (impl : QueryImpl prfMsgKeysSpec (StateT Cache ProbComp))
    (initCache : Cache) (A : AuthAdversary S) :
    let fullImpl := (primBaseImpl P).liftTarget (StateT Cache ProbComp) + impl
    let evalPrf := fun s c => (impl (.derive (effectiveHkdfSaltBytes s))).run c
    let fullRed := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT ((AuthHybridStateFixed S × Bool) × Cache) ProbComp) +
      authMkSlotsRedProbImpl S P idx evalPrf
    ((simulateQ fullImpl (authMkReductionRun S idx A)).run initCache >>= fun (b', _) => pure b') =
      (do
        let secb ← $ᵗ Bool
        let initSt := AuthHybridStateFixed.empty S secb
        let (b', ((finalSt, _), _)) ← (simulateQ fullRed A.run).run ((initSt, false), initCache)
        finalizeAuthFixed P secb b' finalSt.toAuthHybridState) := by
  intro fullImpl evalPrf fullRed
  unfold authMkReductionRun
  rw [simulateQ_prfMkFullImpl_embedUnifMk_bind, bind_assoc]
  congr 1; funext secb
  rw [simulateQ_bind, StateT.run_bind, bind_assoc]
  have hInit : AuthHybridStateFixed.empty S secb =
      cacheAuthAdvKeysFixed P (AuthHybridStateFixed.empty S secb) := rfl
  rw [hInit]
  exact simulateQ_runWithPrfMkStep_eq_redProb S P idx impl A.run
    (AuthHybridStateFixed.empty S secb) false initCache (validAuthHybrid_empty S P secb)
    (fun (((b', finalSt), _), cache') =>
      (simulateQ fullImpl (embedPrimMk (finalizeAuthFixedPrim S secb b'
                                         finalSt.toAuthHybridState))).run cache' >>=
        fun (z, _) => pure z)
    (fun (b', ((finalSt, _), _)) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState)
    (fun b' hst' _ cache' hV' => by
      dsimp only [fullImpl]
      have hVC : ValidAuthHybrid S P (cacheAuthAdvKeysFixed P hst') :=
        (validAuthHybrid_cacheAuthAdvKeysFixed P hst').mpr hV'
      rw [simulateQ_prfMkFullImpl_embedPrimMk,
          simulateQ_finalizeAuthFixedPrim S P secb b' (cacheAuthAdvKeysFixed P
                                                        hst').toAuthHybridState
            hVC.principals_le hVC.spkBundles_le hVC.opkEntries_le hVC.sessions_le hVC.validKem]
      simp [cacheAuthAdvKeysFixed, finalizeAuthFixed_cacheAuthAdvKeys])
def restoreIdealMkAtIdx {S : Setup} (idx : Nat) (mkSeedStar : Bytes)
    (s : IdealAuthSession S) : IdealAuthSession S :=
  if sessionSlotIndex s.sid == idx then { s with mkSeed := mkSeedStar } else s
def restoreAuthMkAtIdx {S : Setup} (idx : Nat) (mkSeedStar : Bytes)
    (hst : AuthHybridState S) : AuthHybridState S :=
  { hst with idealSessions := hst.idealSessions.map (restoreIdealMkAtIdx idx mkSeedStar) }
def filterOutMkSaltCacheAtIdx {S : Setup} (idx : Nat)
    (c : List ((SessionId S × Option Bytes) × (Nat × MessageKeys))) :
    List ((SessionId S × Option Bytes) × (Nat × MessageKeys)) :=
  c.filter (fun (k, _) => !(sessionSlotIndex k.1 == idx))
def restoreAuthFixedMkAtIdx {S : Setup} (idx : Nat) (mkSeedStar : Bytes)
    (hst : AuthHybridStateFixed S) : AuthHybridStateFixed S :=
  { toAuthHybridState := restoreAuthMkAtIdx idx mkSeedStar hst.toAuthHybridState
    recvCount := hst.recvCount
    mkSaltCache := filterOutMkSaltCacheAtIdx idx hst.mkSaltCache }
@[simp] theorem restoreAuthMkAtIdx_base {S : Setup} (idx : Nat) (mkSeedStar : Bytes)
    (hst : AuthHybridState S) : (restoreAuthMkAtIdx idx mkSeedStar hst).base = hst.base := rfl
@[simp] theorem restoreAuthMkAtIdx_initKemRecs {S : Setup} (idx : Nat) (mkSeedStar : Bytes)
    (hst : AuthHybridState S) :
    (restoreAuthMkAtIdx idx mkSeedStar hst).initKemRecs = hst.initKemRecs := rfl
@[simp] theorem restoreAuthMkAtIdx_recvKemRecs {S : Setup} (idx : Nat) (mkSeedStar : Bytes)
    (hst : AuthHybridState S) :
    (restoreAuthMkAtIdx idx mkSeedStar hst).recvKemRecs = hst.recvKemRecs := rfl
@[simp] theorem restoreAuthMkAtIdx_idealSessions {S : Setup} (idx : Nat) (mkSeedStar : Bytes)
    (hst : AuthHybridState S) : (restoreAuthMkAtIdx idx mkSeedStar hst).idealSessions =
      hst.idealSessions.map (restoreIdealMkAtIdx idx mkSeedStar) := rfl
@[simp] theorem finalizeAuthFixed_restoreAuthMkAtIdx {S : Setup} (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes) (secb b' : Bool) (hst : AuthHybridState S) :
    finalizeAuthFixed P secb b' (restoreAuthMkAtIdx idx mkSeedStar hst) =
      finalizeAuthFixed P secb b' hst := rfl
@[simp] theorem authSlotFired_restoreAuthFixedMkAtIdx {S : Setup}
    (idx' idx : Nat) (mkSeedStar : Bytes) (hst : AuthHybridStateFixed S) :
    authSlotFired S idx' (restoreAuthFixedMkAtIdx idx mkSeedStar hst) =
      authSlotFired S idx' hst := rfl
@[simp] theorem matchIdealAuthHandshake_restoreIdealMkAtIdx {S : Setup} (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes)
    (ikBPk spkBPk : Bytes) (opkPk? : Option Bytes) (pqspkBPk : Bytes)
    (hdr : HandshakeHdr) (s : IdealAuthSession S) :
    matchIdealAuthHandshake P ikBPk spkBPk opkPk? pqspkBPk hdr
      (restoreIdealMkAtIdx idx mkSeedStar s) =
      matchIdealAuthHandshake P ikBPk spkBPk opkPk? pqspkBPk hdr s := by
  unfold restoreIdealMkAtIdx
  split <;> rfl
@[simp] theorem find?_matchIdealAuthHandshake_restoreIdealMkAtIdx {S : Setup} (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes)
    (ikBPk spkBPk : Bytes) (opkPk? : Option Bytes) (pqspkBPk : Bytes)
    (hdr : HandshakeHdr) (l : List (IdealAuthSession S)) :
    (l.map (restoreIdealMkAtIdx idx mkSeedStar)).find?
        (matchIdealAuthHandshake P ikBPk spkBPk opkPk? pqspkBPk hdr) =
      (l.find? (matchIdealAuthHandshake P ikBPk spkBPk opkPk? pqspkBPk hdr)).map
        (restoreIdealMkAtIdx idx mkSeedStar) := by
  induction l with
  | nil => rfl
  | cons s tl ih =>
    simp only [List.map_cons, List.find?_cons, matchIdealAuthHandshake_restoreIdealMkAtIdx]
    cases matchIdealAuthHandshake P ikBPk spkBPk opkPk? pqspkBPk hdr s
    · exact ih
    · rfl
@[simp] theorem match_sameEph_map_restoreIdealMkAtIdx {S : Setup} (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes) (ms? : Option (IdealAuthSession S)) (ephAPk : Bytes) :
    (match ms?.map (restoreIdealMkAtIdx idx mkSeedStar) with
     | some s => P.pow8 ephAPk == P.pow8 s.ephAPk
     | none => false) =
    (match ms? with
     | some s => P.pow8 ephAPk == P.pow8 s.ephAPk
     | none => false) := by
  cases ms? with
  | none => rfl
  | some s =>
    dsimp only [Option.map, restoreIdealMkAtIdx]
    split <;> rfl
def restorePreparedAuthRecvMk {S : Setup} (idx : Nat) (mkSeedStar : Bytes)
    (prep : PreparedAuthRecv S) : PreparedAuthRecv S :=
  { prep with
    hstDec := restoreAuthMkAtIdx idx mkSeedStar prep.hstDec
    matchedSess? := prep.matchedSess?.map (restoreIdealMkAtIdx idx mkSeedStar)
    finish := fun res? =>
      let (resp, hst') := prep.finish res?
      (resp, restoreAuthMkAtIdx idx mkSeedStar hst') }
theorem finishAuthHybridRecvOPK_restoreAuthMkAtIdx {S : Setup} (checkAuth : Bool) (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (oEntry : OpkEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (hstDec : AuthHybridState S) (res?) :
    let x := finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry usedTriples' msg hstDec
      res?
    (x.1, restoreAuthMkAtIdx idx mkSeedStar x.2) =
      finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry usedTriples' msg
        (restoreAuthMkAtIdx idx mkSeedStar hstDec) res? := by
  dsimp only [restoreAuthMkAtIdx]
  unfold finishAuthHybridRecvOPK
  cases res? with
  | none => rfl
  | some r =>
    rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    dsimp only
    cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none => rfl
    | some p =>
      rcases p with ⟨_, senderEntry⟩
      dsimp only
      cases senderEntry.corrupted <;> rfl
theorem finishAuthHybridRecvNoOPK_restoreAuthMkAtIdx {S : Setup} (checkAuth : Bool) (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes) (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (hstDec : AuthHybridState S) (res?) :
    let x := finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry usedTriples' msg hstDec res?
    (x.1, restoreAuthMkAtIdx idx mkSeedStar x.2) =
      finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry usedTriples' msg
        (restoreAuthMkAtIdx idx mkSeedStar hstDec) res? := by
  dsimp only [restoreAuthMkAtIdx]
  unfold finishAuthHybridRecvNoOPK
  cases res? with
  | none => rfl
  | some r =>
    rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    dsimp only
    cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none => rfl
    | some p =>
      rcases p with ⟨_, senderEntry⟩
      dsimp only
      cases senderEntry.corrupted <;> rfl
theorem prepareAuthHybridRecvOPK_restoreAuthMkAtIdx {S : Setup} (checkAuth : Bool) (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    prepareAuthHybridRecvOPK checkAuth P k j o msg (restoreAuthMkAtIdx idx mkSeedStar hst) =
      (prepareAuthHybridRecvOPK checkAuth P k j o msg hst).map
        (restorePreparedAuthRecvMk idx mkSeedStar) := by
  unfold prepareAuthHybridRecvOPK restorePreparedAuthRecvMk
  dsimp only [restoreAuthMkAtIdx_base]
  split; · rfl
  split; · rfl
  split; · rfl
  split; · rfl
  split
  · split; · rfl
    split; · rfl
    split
    · rfl
    · simp only [Option.map_some, restoreAuthMkAtIdx_initKemRecs, restoreAuthMkAtIdx_recvKemRecs,
        restoreAuthMkAtIdx_idealSessions, find?_matchIdealAuthHandshake_restoreIdealMkAtIdx]
      congr 2
      · exact match_sameEph_map_restoreIdealMkAtIdx P idx mkSeedStar _ _
      · funext res?
        apply Eq.symm
        exact finishAuthHybridRecvOPK_restoreAuthMkAtIdx checkAuth P idx mkSeedStar k j o _ _ _ _
          msg _ res?
  · rfl
theorem prepareAuthHybridRecvNoOPK_restoreAuthMkAtIdx {S : Setup} (checkAuth : Bool)
  (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes) (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    prepareAuthHybridRecvNoOPK checkAuth P k j l msg (restoreAuthMkAtIdx idx mkSeedStar hst) =
      (prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst).map
        (restorePreparedAuthRecvMk idx mkSeedStar) := by
  unfold prepareAuthHybridRecvNoOPK restorePreparedAuthRecvMk
  dsimp only [restoreAuthMkAtIdx_base]
  split; · rfl
  split; · rfl
  split; · rfl
  split; · rfl
  split
  · split; · rfl
    split
    · rfl
    · simp only [Option.map_some, restoreAuthMkAtIdx_initKemRecs, restoreAuthMkAtIdx_recvKemRecs,
        restoreAuthMkAtIdx_idealSessions, find?_matchIdealAuthHandshake_restoreIdealMkAtIdx]
      congr 2
      · exact match_sameEph_map_restoreIdealMkAtIdx P idx mkSeedStar _ _
      · funext res?
        apply Eq.symm
        exact finishAuthHybridRecvNoOPK_restoreAuthMkAtIdx checkAuth P idx mkSeedStar k j l _ _ _
          msg _ res?
  · rfl
private theorem ite_elim_false_first₂ {α β : Sort*} (R : α → β → Prop) {c : Prop} [Decidable c]
    {t₁ e₁ : α} {t₂ e₂ : β} (he : ¬ c → R e₁ e₂) (ht : c → R t₁ t₂) :
    R (if c then t₁ else e₁) (if c then t₂ else e₂) := by
  by_cases h : c
  · simpa [h] using ht h
  · simpa [h] using he h
theorem prepareAuthSendMk_restoreAuthFixedMkAtIdx (S : Setup) (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    prepareAuthSendMk S P sid u bundle m0 m1 (restoreAuthFixedMkAtIdx idx mkSeedStar hst) =
      PreparedAuthSend.mapState (restoreAuthFixedMkAtIdx idx mkSeedStar) <$>
        prepareAuthSendMk S P sid u bundle m0 m1 hst := by
  unfold prepareAuthSendMk finishAuthHybridSend restoreAuthFixedMkAtIdx restoreAuthMkAtIdx
  dsimp only
  cases hst.toAuthHybridState.base.hasWonAuth <;> simp only [Bool.false_eq_true, ↓reduceIte]
  swap; · simp [PreparedAuthSend.mapState]
  cases (m0.length != m1.length) <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · cases hst.toAuthHybridState.base.usedSendSessions.contains sid <;> simp only
      [Bool.false_eq_true, ↓reduceIte]
    · cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp [PreparedAuthSend.mapState]
      | some uPair =>
        rcases uPair with ⟨_, uEntry⟩
        dsimp only
        refine ite_elim_false_first₂
          (fun m₁ m₂ => m₁ = PreparedAuthSend.mapState (restoreAuthFixedMkAtIdx idx mkSeedStar) <$> m₂)
          (fun _ => ?_) (fun _ => ?_) <;>
          (unfold restoreAuthFixedMkAtIdx restoreAuthMkAtIdx; dsimp only)
        · cases (!koskBundleOk P hst.toAuthHybridState.base.principals
            hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries
            hst.toAuthHybridState.base.advKeys bundle) <;>
            simp only [Bool.false_eq_true, ↓reduceIte]
          · simp only [map_bind]
            congr 1; funext ekASk; congr 1; funext kemCoins; congr 1; funext ephASk; congr 1; funext
              spqrCoins
            cases (!(P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
                (encodeEC bundle.spkB) bundle.spkSig &&
              P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
                (encodeKEM bundle.pqspkB) bundle.pqspkSig)) <;>
              simp only [Bool.false_eq_true, ↓reduceIte]
            · cases P.kemEncaps bundle.pqspkB kemCoins with
              | none => simp [PreparedAuthSend.mapState]
              | some pair =>
                rcases pair with ⟨ss, kemCt⟩
                dsimp only
                refine ite_elim_false_first₂
                  (fun m₁ m₂ => m₁ = PreparedAuthSend.mapState (restoreAuthFixedMkAtIdx idx mkSeedStar) <$> m₂)
                  (fun h_ideal => ?_) (fun _ => ?_) <;>
                  (unfold restoreAuthFixedMkAtIdx restoreAuthMkAtIdx; dsimp only)
                · simp only [map_bind]
                  congr 1; funext ⟨drKey, roCache'⟩
                  congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
                  cases P.spqrInitSend drKey.pqrKey spqrCoins with
                  | none => simp [PreparedAuthSend.mapState]
                  | some spqrVal =>
                    rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
                    dsimp only
                    simp [PreparedAuthSend.mapState, h_ideal]
                · simp only [map_bind]
                  congr 1; funext drKey
                  congr 1; funext rk1
                  cases P.spqrInitSend drKey.pqrKey spqrCoins with
                  | none => simp [PreparedAuthSend.mapState]
                  | some spqrVal =>
                    rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
                    simp [PreparedAuthSend.mapState]
            · simp [PreparedAuthSend.mapState]
          · simp [PreparedAuthSend.mapState]
        · simp [PreparedAuthSend.mapState]
    · simp [PreparedAuthSend.mapState]
  · simp [PreparedAuthSend.mapState]
theorem finishAuthSendMk_restoreAuthFixedMkAtIdx_eq {S : Setup} (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes)
    (sid : SessionId S) (hIdx : (sessionSlotIndex sid == idx) = true)
    (uEntry : PrincipalEntry) (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 ck1_1 : Bytes) (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (deriveMessageKeys : MessageKeys) :
    finishAuthSendMk P sid uEntry peerPrincipal? bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeedStar ck1_1
      spqrSalt? pqRatchetMsg msgPlain (restoreAuthFixedMkAtIdx idx mkSeedStar hst) deriveMessageKeys =
    let (resp, hst') := finishAuthSendMk P sid uEntry peerPrincipal? bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1
      spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys
    (resp, restoreAuthFixedMkAtIdx idx mkSeedStar hst') := by
  unfold finishAuthSendMk finishAuthHybridSend restoreAuthFixedMkAtIdx restoreAuthMkAtIdx
  dsimp only
  simp only [Prod.mk.injEq, AuthHybridStateFixed.mk.injEq, AuthHybridState.mk.injEq, true_and,
    and_true]
  refine ite_elim_false_first₂ (fun s₁ s₂ => s₁ = List.map (restoreIdealMkAtIdx idx mkSeedStar) s₂)
    (fun _ => rfl) (fun _ => ?_)
  simp [restoreIdealMkAtIdx, hIdx]
theorem finishAuthSendMk_restoreAuthFixedMkAtIdx_ne {S : Setup} (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes)
    (sid : SessionId S) (hNe : (sessionSlotIndex sid == idx) = false)
    (uEntry : PrincipalEntry) (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (deriveMessageKeys : MessageKeys) :
    finishAuthSendMk P sid uEntry peerPrincipal? bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
      spqrSalt? pqRatchetMsg msgPlain (restoreAuthFixedMkAtIdx idx mkSeedStar hst) deriveMessageKeys =
    let (resp, hst') := finishAuthSendMk P sid uEntry peerPrincipal? bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
      spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys
    (resp, restoreAuthFixedMkAtIdx idx mkSeedStar hst') := by
  unfold finishAuthSendMk finishAuthHybridSend restoreAuthFixedMkAtIdx restoreAuthMkAtIdx
  dsimp only
  simp only [Prod.mk.injEq, AuthHybridStateFixed.mk.injEq, AuthHybridState.mk.injEq, true_and,
    and_true]
  refine ite_elim_false_first₂ (fun s₁ s₂ => s₁ = List.map (restoreIdealMkAtIdx idx mkSeedStar) s₂)
    (fun _ => rfl) (fun _ => ?_)
  simp [restoreIdealMkAtIdx, hNe]
theorem finishAuthRecvMk_restorePreparedAuthRecvMk {S : Setup} (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes) (msg : PreKeyMsg) (prep : PreparedAuthRecv S)
    (drKey : DRKey) (rk1 ck1_1 : Bytes) (recvCount' : Nat)
    (mkSaltCache' : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (deriveMessageKeys : MessageKeys) :
    finishAuthRecvMk P msg (restorePreparedAuthRecvMk idx mkSeedStar prep)
      drKey rk1 ck1_1 recvCount' (filterOutMkSaltCacheAtIdx idx mkSaltCache') deriveMessageKeys =
    let (resp, hst') := finishAuthRecvMk P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache' deriveMessageKeys
    (resp, restoreAuthFixedMkAtIdx idx mkSeedStar hst') := rfl
theorem find?_filterOutMkSaltCacheAtIdx_of_ne {S : Setup} (idx : Nat)
    (sid : SessionId S) (salt? : Option Bytes) (hNe : (sessionSlotIndex sid == idx) = false) :
    ∀ (c : List ((SessionId S × Option Bytes) × (Nat × MessageKeys))),
      (filterOutMkSaltCacheAtIdx idx c).find? (fun (k, _) => mkSaltKeyMatch k sid salt?) =
        c.find? (fun (k, _) => mkSaltKeyMatch k sid salt?)
  | [] => rfl
  | ((sid', salt'), v) :: rest => by
    unfold filterOutMkSaltCacheAtIdx
    rw [List.filter_cons]
    by_cases hEq : (!(sessionSlotIndex sid' == idx)) = true
    · simp only [hEq, ↓reduceIte, List.find?]
      rw [← filterOutMkSaltCacheAtIdx, find?_filterOutMkSaltCacheAtIdx_of_ne idx sid salt? hNe rest]
    · simp only [hEq, Bool.false_eq_true, ↓reduceIte]
      have hIdx' : (sessionSlotIndex sid' == idx) = true := by revert hEq; simp
      have hne_pair : mkSaltKeyMatch (sid', salt') sid salt? = false := by
        have hSidNe : sid' ≠ sid := by
          rintro rfl
          rw [hNe] at hIdx'; cases hIdx'
        simp [mkSaltKeyMatch, hSidNe]
      rw [List.find?, hne_pair, ← filterOutMkSaltCacheAtIdx]
      exact find?_filterOutMkSaltCacheAtIdx_of_ne idx sid salt? hNe rest
theorem filterOutMkSaltCacheAtIdx_cons_of_ne {S : Setup} (idx : Nat)
    (sid : SessionId S) (salt? : Option Bytes) (v : Nat × MessageKeys)
    (c : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (hNe : (sessionSlotIndex sid == idx) = false) :
    filterOutMkSaltCacheAtIdx idx (((sid, salt?), v) :: c) =
      ((sid, salt?), v) :: filterOutMkSaltCacheAtIdx idx c := by
  unfold filterOutMkSaltCacheAtIdx
  simp [hNe]
theorem filterOutMkSaltCacheAtIdx_cons_of_eq {S : Setup} (idx : Nat)
    (sid : SessionId S) (salt? : Option Bytes) (v : Nat × MessageKeys)
    (c : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (hEq : (sessionSlotIndex sid == idx) = true) :
    filterOutMkSaltCacheAtIdx idx (((sid, salt?), v) :: c) =
      filterOutMkSaltCacheAtIdx idx c := by
  unfold filterOutMkSaltCacheAtIdx
  simp [hEq]
theorem authCkOtherStep_restoreAuthFixedMkAtIdx {S : Setup} (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes) (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    authCkOtherStep S P q (restoreAuthFixedMkAtIdx idx mkSeedStar hst) =
      Prod.map id (restoreAuthFixedMkAtIdx idx mkSeedStar) <$> authCkOtherStep S P q hst := by
  unfold authCkOtherStep restoreAuthFixedMkAtIdx restoreAuthMkAtIdx
  dsimp only
  cases hst.toAuthHybridState.base.hasWonAuth <;> simp [map_eq_bind_pure_comp, Prod.map]
theorem finishAuthSendMk_idealSessions_props {S : Setup} (P : Primitives)
    (sid : SessionId S) (uEntry : PrincipalEntry) (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (deriveMessageKeys : MessageKeys) :
    let hst' := (finishAuthSendMk P sid uEntry peerPrincipal? bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
      spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys).2
    hst'.mkSaltCache = hst.mkSaltCache ∧
    hst'.recvCount = hst.recvCount ∧
    (hst'.toAuthHybridState.idealSessions = hst.toAuthHybridState.idealSessions ∨
     ∃ s0 : IdealAuthSession S,
       s0.sid = sid ∧ s0.mkSeed = mkSeed ∧ s0.spqrSalt? = spqrSalt? ∧ s0.deriveMessageKeys = deriveMessageKeys ∧
       hst'.toAuthHybridState.idealSessions = s0 :: hst.toAuthHybridState.idealSessions) := by
  dsimp only
  unfold finishAuthSendMk finishAuthHybridSend
  dsimp only
  refine ⟨rfl, rfl, ?_⟩
  split_ifs
  · exact Or.inr ⟨_, rfl, rfl, rfl, rfl, rfl⟩
  · exact Or.inl rfl
theorem sendSlotIndex?_of_isSendSessionId {S : Setup} {sid : SessionId S}
    (hSend : IsSendSessionId S sid) :
    sendSlotIndex? sid = some (sessionSlotIndex sid) := by
  cases sid with
  | sendOPK _ _ => rfl
  | sendNoOPK _ _ => rfl
  | recvOPK _ _ _ => cases hSend
  | recvNoOPK _ _ _ => cases hSend
theorem sentChal_false_of_send_idealMk {S : Setup} {idx : Nat} {sid : SessionId S}
    {hst : AuthHybridStateFixed S} {sentChal : Bool}
    (hSent : sentChal = true → idx < S.N_send_tot ∧ authSlotFired S idx hst = true)
    (hSend : IsSendSessionId S sid)
    (hCont : hst.toAuthHybridState.base.usedSendSessions.contains sid = false)
    (hIdx : (sessionSlotIndex sid == idx) = true) :
    authSlotFired S idx hst = false ∧ sentChal = false := by
  have hSlot : sendSlotIndex? sid = some idx := by
    rw [sendSlotIndex?_of_isSendSessionId hSend, beq_iff_eq.mp hIdx]
  have hNF : authSlotFired S idx hst = false := by
    cases hF : authSlotFired S idx hst
    · rfl
    · have := contains_sid_of_authSlotFired hF hSlot
      rw [hCont] at this; cases this
  have hSC : sentChal = false := by
    cases hS : sentChal
    · rfl
    · have := (hSent hS).2
      rw [hNF] at this; cases this
  exact ⟨hNF, hSC⟩
theorem sentChal_false_of_recv_slot {S : Setup} {idx : Nat}
    {hst : AuthHybridStateFixed S} {sentChal : Bool}
    (hSent : sentChal = true → idx < S.N_send_tot ∧ authSlotFired S idx hst = true)
    (hIdx : (S.N_send_tot + hst.recvCount == idx) = true) :
    authSlotFired S idx hst = false ∧ sentChal = false := by
  have hEq : S.N_send_tot + hst.recvCount = idx := beq_iff_eq.mp hIdx
  have hNlt : ¬ (idx < S.N_send_tot) := by omega
  have hNF : authSlotFired S idx hst = false := by
    unfold authSlotFired
    simp [← hEq]
  have hSC : sentChal = false := by
    cases hS : sentChal
    · rfl
    · exact False.elim (hNlt (hSent hS).1)
  exact ⟨hNF, hSC⟩
end AuthSubHops1to3
end SignalPqxdh.Security
