/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.PqxdhSimTypes

/-!
# Per-Branch `ReductionDsl` Simulators for One-Key Real PQXDH

Defines the 14 per-constructor `ReductionDsl` handler arms over `E2EPqxdhHooks` for
`SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P`, and proves `Comp.eval` equivalence and
zero-target-query bounds for each arm.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.PqxdhSimBranches

open Classical
open OracleSpec OracleComp

open ReductionDsl (Ty Ops Samplers Var Expr Comp Iface Env bits findML anyML mapML)
open CryptoVerification.E2E.Costed (E2ESort E2EUnifBase E2EPureOp E2ECryptoOp e2eSig e2eSamplers
  e2ePureOps e2eCryptoOps e2eOps PB PU32 FinT drKeyT drKeyV drKeyOfV bundleT bundleV bundleOfV
  hdrT hdrV hdrOfV sidT sidV sidOfV keyIndRT keyIndRenc)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp e2eCryptoOp eval_e2ePureOp eval_e2eCryptoOp
  drKeyOfV_drKeyV bundleOfV_bundleV bundleV_bundleOfV hdrOfV_hdrV hdrV_hdrOfV
  sidOfV_sidV sidV_sidOfV)
open Computational.Proofs.E2E.Dsl.ClampsLossless (e2eCryptoOps_eval_x25519_lossless
  e2eCryptoOps_eval_x25519Base_lossless e2eCryptoOps_eval_pow8_lossless
  e2eCryptoOps_eval_sigSign_lossless e2eCryptoOps_eval_kemEncaps_lossless
  e2eCryptoOps_eval_hkdfDerive96_lossless)
open Computational.Proofs.GameHop.ReductionDsl.CostUB (exprCostUB compCostUB compQueriesUB)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (Ext v v_def ext_refl_wk ext_step_wk
  eval_v_refl eval_v_cons env_get_zero env_get_succ
  eLet eCaseOpt eFind eAny eMap bindV letV caseOptV
  compQueriesUB_bindV compQueriesUB_letV compQueriesUB_caseOptV
  liftP_pure liftP_bind liftP_map
  E2EPqxdhHooks HooksNoTargetQueries stepAIface mkStepAPqxdhHooks
  e2ePrincipalEntryTy e2ePrincipalEntryToVal e2eSpkBundleEntryTy e2eSpkBundleEntryToVal
  e2eOpkEntryTy e2eOpkEntryToVal e2eInitiatorEntryTy e2eInitiatorEntryToVal
  e2eRespEntryTy e2eRespEntryToVal e2eKeyIndStateTy e2eKeyIndStateToVal
  KeyIndSetupBounded stListBounded isSomeE eval_isSomeE isNoneE eval_isNoneE optMapE eval_optMapE
  nat2EqE eval_nat2EqE nat3EqE eval_nat3EqE
  finValE sidEqE eval_sidEqE optPu32EqE eval_optPu32EqE
  peSec0 peIkPk peSecSign peSignPk peSetCorrE
  beSpkSk beSpkPk beSpkSig bePqSk bePqPk bePqSig beSetRevE
  oeSk oePk oeCons oeSetConsE
  bndIkB bndSpkId bndSpkB bndSpkSig bndOpkB bndPqId bndPqB bndPqSig
  hdrIkA hdrEkA hdrSpkId hdrOpkId hdrPqId hdrKemCt
  ieSid ieHonPeer iePeerIk iePeerSpk iePeerOpk iePeerPq ieSpkHon ieOpkHon iePqHon
  ieEkSk ieFresh ieReal ieRand ieHdr ieTested ieRev ieSetTestedE ieSetRevE ieSetRandE
  reSid reIk reSpk reOpk rePq reHdr reSendHon reReal reRand reTested reRev
  reSetTestedE reSetRevE
  stSecb stPrin stSpk stOpk stSess stResp stUsedOpk stUsedNoOpk stSeen stRo stAdv
  setPrinE setSpkE setOpkE setSessE setRespE setAdvE setAcceptOpkE setAcceptNoOpkE
  rNoneE rInitPrinE rPkE rCorrE rBundleE rHdrE rInitUnfreshE rAcceptFreshE rDrKeyE rSpkSkE rsE
  encECWideE eval_encECWideE encKEME eval_encKEME buildSecretsE eval_buildSecretsE
  checkSeenE eval_checkSeenE checkSeenEFuel eval_checkSeenEFuel
  isTestableE eval_isTestableE isTestableEFuel eval_isTestableEFuel
  sBytes32C eval_sBytes32C queriesUB_sBytes32C
  sRandom64C eval_sRandom64C queriesUB_sRandom64C
  sDrKey96C eval_sDrKey96C queriesUB_sDrKey96C
  sKemKeyGenC eval_sKemKeyGenC queriesUB_sKemKeyGenC
  findHonestC eval_findHonestC queriesUB_findHonestC
  findHonestCFuel eval_findHonestCFuel queriesUB_findHonestCFuel
  koskBundleOkC eval_koskBundleOkC queriesUB_koskBundleOkC
  koskBundleOkCFuel eval_koskBundleOkCFuel queriesUB_koskBundleOkCFuel
  koskSenderOkC eval_koskSenderOkC queriesUB_koskSenderOkC
  koskSenderOkCFuel eval_koskSenderOkCFuel queriesUB_koskSenderOkCFuel
  resolveSigPkC eval_resolveSigPkC queriesUB_resolveSigPkC
  resolveSigPkCFuel eval_resolveSigPkCFuel queriesUB_resolveSigPkCFuel
  honestPeerC eval_honestPeerC queriesUB_honestPeerC
  honestPeerCFuel eval_honestPeerCFuel queriesUB_honestPeerCFuel
  checkProvC eval_checkProvC queriesUB_checkProvC
  checkProvCFuel eval_checkProvCFuel queriesUB_checkProvCFuel
  partnerRandKeyC eval_partnerRandKeyC queriesUB_partnerRandKeyC
  partnerRandKeyCFuel eval_partnerRandKeyCFuel queriesUB_partnerRandKeyCFuel
  recordRespC eval_recordRespC queriesUB_recordRespC
  recordRespCFuel eval_recordRespCFuel queriesUB_recordRespCFuel
  acceptKeysC eval_acceptKeysC queriesUB_acceptKeysC acceptKeys_some_matched)
open CryptoGames.LibsignalSession (Crypto PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open SignalPqxdh (Setup Primitives WellFormedPrimitivesδ PreKeyBundleInput HandshakeHdr SessionId
  PrincipalEntry SpkBundleEntry OpkEntry KeyIndInitiatorEntry KeyIndRespEntry KeyIndQuery
  KeyIndResponse KeyIndState AcceptKeysInput encodeEC encodeKEM buildSecrets sampleBytes32
  sampleScalar32 sampleCoins32 sampleRandom64 sampleDRKey96 sampleKemKeyGen findHonestPrincipal
  resolveSigPk isHonestUncorruptedPeer checkBundleProvenance koskBundleOk koskSenderOk
  registerAdvKey evalHkdfOrRo checkAndMarkKyberBaseKeySeen isKeyIndSessionTestable recordKeyIndResp
  keyIndPartnerRandKey? runKeyIndInitiate pqxdhKeyIndImpl pqxdhKeyIndImpl1KeyReal)
open SignalPqxdh.Model (acceptKeys)

/-! ## Branch programs -/

section BranchDefs

variable {ℓ : ℕ} {S : Setup} {O : Ops (e2eSig ℓ)} {ι : Type} {T : OracleSpec ι}
  {I : Iface (e2eSig ℓ) T}

/-- Non-reducible wrapper around `Expr.eqN` preventing `simp` from unfolding `@decide`. -/
def natEqE {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (a b : Expr O Γ .nat) : Expr O Γ .bool :=
  .eqN a b

def initPrin1KeyBFuel (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (u : Expr O Γ (FinT S.N_id)) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  letV (finValE H u) fun uNat =>
    .ite (eAny (min nFuel S.N_id) (stPrin (v st)) fun p => natEqE (.fst (v p)) (v uNat))
      (.ret (rsE rNoneE (v st)))
      (bindV (sBytes32C H) fun sec =>
        bindV (H.callPrim .x25519Base (v sec)) fun pk =>
          let entry := .pair (v sec) (.pair (v pk) (.pair (v sec) (.pair (v pk) (.bool false))))
          .ret (rsE (rInitPrinE (v pk) (v pk))
            (setPrinE (v st) (.cons (.pair (v uNat) entry) (stPrin (v st))))))

def initPrin1KeyB (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (u : Expr O Γ (FinT S.N_id)) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  letV (finValE H u) fun uNat =>
    .ite (eAny S.N_id (stPrin (v st)) fun p => natEqE (.fst (v p)) (v uNat))
      (.ret (rsE rNoneE (v st)))
      (bindV (sBytes32C H) fun sec =>
        bindV (H.callPrim .x25519Base (v sec)) fun pk =>
          let entry := .pair (v sec) (.pair (v pk) (.pair (v sec) (.pair (v pk) (.bool false))))
          .ret (rsE (rInitPrinE (v pk) (v pk))
            (setPrinE (v st) (.cons (.pair (v uNat) entry) (stPrin (v st))))))

def corruptBFuel (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (u : Expr O Γ (FinT S.N_id)) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  letV (finValE H u) fun uNat =>
    caseOptV (eFind (min nFuel S.N_id) (stPrin (v st)) fun p => natEqE (.fst (v p)) (v uNat))
      (.ret (rsE rNoneE (v st)))
      (fun found =>
        let ps' := eMap (min nFuel S.N_id) (stPrin (v st)) fun p =>
          .ite (natEqE (.fst (v p)) (v uNat))
            (.pair (.fst (v p)) (peSetCorrE (.snd (v p))))
            (v p)
        .ret (rsE (rCorrE (peSec0 (.snd (v found))) (peSecSign (.snd (v found))))
          (setPrinE (v st) ps')))

def corruptB (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (u : Expr O Γ (FinT S.N_id)) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  letV (finValE H u) fun uNat =>
    caseOptV (eFind S.N_id (stPrin (v st)) fun p => natEqE (.fst (v p)) (v uNat))
      (.ret (rsE rNoneE (v st)))
      (fun found =>
        let ps' := eMap S.N_id (stPrin (v st)) fun p =>
          .ite (natEqE (.fst (v p)) (v uNat))
            (.pair (.fst (v p)) (peSetCorrE (.snd (v p))))
            (v p)
        .ret (rsE (rCorrE (peSec0 (.snd (v found))) (peSecSign (.snd (v found))))
          (setPrinE (v st) ps')))

def genSpkBFuel (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr O Γ (FinT S.N_id)) (j : Expr O Γ (FinT S.N_recv)) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  letV (.pair (finValE H u) (finValE H j)) fun uj =>
    .ite (eAny (min nFuel S.N_spk_tot) (stSpk (v st)) fun b => nat2EqE (.fst (v b)) (v uj))
      (.ret (rsE rNoneE (v st)))
      (caseOptV (eFind (min nFuel S.N_id) (stPrin (v st)) fun p => natEqE (.fst (v p)) (.fst (v uj)))
        (.ret (rsE rNoneE (v st)))
        (fun uFound =>
          bindV (sBytes32C H) fun spkSk =>
          bindV (H.callPrim .x25519Base (v spkSk)) fun spkPk =>
          bindV (sRandom64C H) fun rSpk =>
          bindV (H.callPrim .sigSign
            (.pair (peSecSign (.snd (v uFound)))
                   (.pair (encECWideE H (v spkPk)) (v rSpk)))) fun spkSig =>
          bindV (sKemKeyGenC H) fun pqKp =>
          bindV (sRandom64C H) fun rPq =>
          bindV (H.callPrim .sigSign
            (.pair (peSecSign (.snd (v uFound)))
                   (.pair (encKEME H (.fst (v pqKp))) (v rPq)))) fun pqSig =>
            let bEntry := .pair (v spkSk) (.pair (v spkPk) (.pair (v spkSig)
              (.pair (.snd (v pqKp)) (.pair (.fst (v pqKp)) (.pair (v pqSig) (.bool false))))))
            let jId := H.pureOp .pu32OfNat (.snd (v uj))
            let bOut := .pair (peIkPk (.snd (v uFound))) (.pair jId (.pair (v spkPk)
              (.pair (v spkSig) (.pair .none (.pair jId (.pair (.fst (v pqKp)) (v pqSig)))))))
            .ret (rsE (rBundleE bOut)
              (setSpkE (v st) (.cons (.pair (v uj) bEntry) (stSpk (v st)))))))

def genSpkB (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr O Γ (FinT S.N_id)) (j : Expr O Γ (FinT S.N_recv)) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  letV (.pair (finValE H u) (finValE H j)) fun uj =>
    .ite (eAny S.N_spk_tot (stSpk (v st)) fun b => nat2EqE (.fst (v b)) (v uj))
      (.ret (rsE rNoneE (v st)))
      (caseOptV (eFind S.N_id (stPrin (v st)) fun p => natEqE (.fst (v p)) (.fst (v uj)))
        (.ret (rsE rNoneE (v st)))
        (fun uFound =>
          bindV (sBytes32C H) fun spkSk =>
          bindV (H.callPrim .x25519Base (v spkSk)) fun spkPk =>
          bindV (sRandom64C H) fun rSpk =>
          bindV (H.callPrim .sigSign
            (.pair (peSecSign (.snd (v uFound)))
                   (.pair (encECWideE H (v spkPk)) (v rSpk)))) fun spkSig =>
          bindV (sKemKeyGenC H) fun pqKp =>
          bindV (sRandom64C H) fun rPq =>
          bindV (H.callPrim .sigSign
            (.pair (peSecSign (.snd (v uFound)))
                   (.pair (encKEME H (.fst (v pqKp))) (v rPq)))) fun pqSig =>
            let bEntry := .pair (v spkSk) (.pair (v spkPk) (.pair (v spkSig)
              (.pair (.snd (v pqKp)) (.pair (.fst (v pqKp)) (.pair (v pqSig) (.bool false))))))
            let jId := H.pureOp .pu32OfNat (.snd (v uj))
            let bOut := .pair (peIkPk (.snd (v uFound))) (.pair jId (.pair (v spkPk)
              (.pair (v spkSig) (.pair .none (.pair jId (.pair (.fst (v pqKp)) (v pqSig)))))))
            .ret (rsE (rBundleE bOut)
              (setSpkE (v st) (.cons (.pair (v uj) bEntry) (stSpk (v st)))))))

def genOpkBFuel (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr O Γ (FinT S.N_id)) (j : Expr O Γ (FinT S.N_recv)) (o : Expr O Γ (FinT S.N_opk)) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  letV (.pair (finValE H u) (.pair (finValE H j) (finValE H o))) fun ujo =>
    .ite (eAny (min nFuel S.N_opk_tot) (stOpk (v st)) fun x => nat3EqE (.fst (v x)) (v ujo))
      (.ret (rsE rNoneE (v st)))
      (bindV (sBytes32C H) fun opkSk =>
        bindV (H.callPrim .x25519Base (v opkSk)) fun opkPk =>
          let oEntry := .pair (v opkSk) (.pair (v opkPk) (.bool false))
          .ret (rsE (rPkE (v opkPk))
            (setOpkE (v st) (.cons (.pair (v ujo) oEntry) (stOpk (v st))))))

def genOpkB (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr O Γ (FinT S.N_id)) (j : Expr O Γ (FinT S.N_recv)) (o : Expr O Γ (FinT S.N_opk)) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  letV (.pair (finValE H u) (.pair (finValE H j) (finValE H o))) fun ujo =>
    .ite (eAny S.N_opk_tot (stOpk (v st)) fun x => nat3EqE (.fst (v x)) (v ujo))
      (.ret (rsE rNoneE (v st)))
      (bindV (sBytes32C H) fun opkSk =>
        bindV (H.callPrim .x25519Base (v opkSk)) fun opkPk =>
          let oEntry := .pair (v opkSk) (.pair (v opkPk) (.bool false))
          .ret (rsE (rPkE (v opkPk))
            (setOpkE (v st) (.cons (.pair (v ujo) oEntry) (stOpk (v st))))))

def initiateCFuel (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (sid : Expr O Γ (sidT S)) (u : Expr O Γ (FinT S.N_id)) (bundle : Expr O Γ bundleT) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  letV (.pair sid (.pair (finValE H u) bundle)) fun sub =>
    .ite (eAny (min nFuel S.N_send_tot) (stSess (v st)) fun e =>
          sidEqE H (ieSid (v e)) (.fst (v sub)))
      (.ret (rsE rNoneE (v st)))
      (caseOptV (eFind (min nFuel S.N_id) (stPrin (v st)) fun p =>
            natEqE (.fst (v p)) (.fst (.snd (v sub))))
        (.ret (rsE rNoneE (v st)))
        (fun uFound =>
          bindV (koskBundleOkCFuel H nFuel (v st) (.snd (.snd (v sub)))) fun koskOk =>
            .ite (.not (v koskOk))
              (.ret (rsE rNoneE (v st)))
              (bindV (sBytes32C H) fun ekASk =>
              bindV (sBytes32C H) fun kemCoins =>
              bindV (resolveSigPkCFuel (S := S) H nFuel (stPrin (v st))
                (bndIkB (.snd (.snd (v sub))))) fun sigPkB =>
              bindV (H.callPrim .sigVerify
                (.pair (v sigPkB)
                  (.pair (encECWideE H (bndSpkB (.snd (.snd (v sub)))))
                         (bndSpkSig (.snd (.snd (v sub))))))) fun ok1 =>
              bindV (H.callPrim .sigVerify
                (.pair (v sigPkB)
                  (.pair (encKEME H (bndPqB (.snd (.snd (v sub)))))
                         (bndPqSig (.snd (.snd (v sub))))))) fun ok2 =>
                .ite (.not (.and (v ok1) (v ok2)))
                  (.ret (rsE rNoneE (v st)))
                  (bindV (H.callPrim .kemEncaps
                    (.pair (bndPqB (.snd (.snd (v sub)))) (v kemCoins))) fun enc? =>
                    caseOptV (v enc?)
                      (.ret (rsE rNoneE (v st)))
                      (fun sc =>
                        bindV (H.callPrim .x25519Base (v ekASk)) fun ekAPk =>
                        bindV (H.callPrim .x25519
                          (.pair (peSec0 (.snd (v uFound)))
                                 (bndSpkB (.snd (.snd (v sub)))))) fun dh1 =>
                        bindV (H.callPrim .x25519
                          (.pair (v ekASk) (bndIkB (.snd (.snd (v sub)))))) fun dh2 =>
                        bindV (H.callPrim .x25519
                          (.pair (v ekASk) (bndSpkB (.snd (.snd (v sub)))))) fun dh3 =>
                        bindV
                          (caseOptV (bndOpkB (.snd (.snd (v sub))))
                            (.ret .none)
                            (fun opk =>
                              bindV (H.callPrim .x25519 (.pair (v ekASk) (.snd (v opk)))) fun d =>
                                .ret (.some (v d))))
                          fun dh4? =>
                        bindV (H.callPrim .hkdfDerive96
                          (buildSecretsE H (v dh1) (v dh2) (v dh3) (v dh4?) (.fst (v sc))))
                          fun drKeyReal =>
                        bindV (honestPeerCFuel (S := S) H nFuel (stPrin (v st))
                          (bndIkB (.snd (.snd (v sub))))) fun honPeer =>
                        bindV (checkProvCFuel H nFuel (v st) (.snd (.snd (v sub)))) fun prov =>
                        letV (τ := hdrT)
                          (.pair (peIkPk (.snd (v uFound)))
                            (.pair (v ekAPk) (.pair (bndSpkId (.snd (.snd (v sub))))
                              (.pair (optMapE (bndOpkB (.snd (.snd (v sub))))
                                fun opk => .fst (v opk))
                                (.pair (bndPqId (.snd (.snd (v sub)))) (.snd (v sc)))))))
                          fun hdrOut =>
                        letV (τ := e2eInitiatorEntryTy ℓ S)
                          (.pair (.fst (v sub)) (.pair (v honPeer)
                            (.pair (bndIkB (.snd (.snd (v sub))))
                              (.pair (bndSpkB (.snd (.snd (v sub))))
                                (.pair (optMapE (bndOpkB (.snd (.snd (v sub))))
                                  fun opk => .snd (v opk))
                                  (.pair (bndPqB (.snd (.snd (v sub))))
                                    (.pair (.fst (v prov))
                                      (.pair (.fst (.snd (v prov)))
                                        (.pair (.snd (.snd (v prov)))
                                          (.pair (v ekASk)
                                            (.pair (isSomeE (v honPeer))
                                              (.pair (v drKeyReal)
                                                (.pair (v drKeyReal)
                                                  (.pair (v hdrOut)
                                                    (.pair (.bool false)
                                                      (.bool false))))))))))))))))
                          fun sessV =>
                          bindV (partnerRandKeyCFuel H nFuel (stResp (v st)) (v sessV)) fun prk? =>
                          bindV (caseOptV (v prk?) (sDrKey96C H) fun rk => .ret (v rk))
                            fun drKeyRand =>
                          bindV (findHonestCFuel (S := S) H nFuel (stPrin (v st))
                            (bndIkB (.snd (.snd (v sub))))) fun fh =>
                            .ret (rsE
                              (eCaseOpt (v fh)
                                (rInitUnfreshE (v drKeyReal) (v hdrOut))
                                (fun _ => rHdrE (v hdrOut)))
                              (setSessE (v st)
                                (.cons (ieSetRandE (v sessV) (v drKeyRand)) (stSess (v st))))))))))

/-- Shared one-key real initiator handshake body for `.initiateOPK` and `.initiateNoOPK`. -/
def initiateC (H : E2EPqxdhHooks ℓ O I) (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (sid : Expr O Γ (sidT S)) (u : Expr O Γ (FinT S.N_id)) (bundle : Expr O Γ bundleT) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  letV (.pair sid (.pair (finValE H u) bundle)) fun sub =>
    .ite (eAny S.N_send_tot (stSess (v st)) fun e =>
          sidEqE H (ieSid (v e)) (.fst (v sub)))
      (.ret (rsE rNoneE (v st)))
      (caseOptV (eFind S.N_id (stPrin (v st)) fun p =>
            natEqE (.fst (v p)) (.fst (.snd (v sub))))
        (.ret (rsE rNoneE (v st)))
        (fun uFound =>
          bindV (koskBundleOkC H nAdv (v st) (.snd (.snd (v sub)))) fun koskOk =>
            .ite (.not (v koskOk))
              (.ret (rsE rNoneE (v st)))
              (bindV (sBytes32C H) fun ekASk =>
              bindV (sBytes32C H) fun kemCoins =>
              bindV (resolveSigPkC (S := S) H (stPrin (v st))
                (bndIkB (.snd (.snd (v sub))))) fun sigPkB =>
              bindV (H.callPrim .sigVerify
                (.pair (v sigPkB)
                  (.pair (encECWideE H (bndSpkB (.snd (.snd (v sub)))))
                         (bndSpkSig (.snd (.snd (v sub))))))) fun ok1 =>
              bindV (H.callPrim .sigVerify
                (.pair (v sigPkB)
                  (.pair (encKEME H (bndPqB (.snd (.snd (v sub)))))
                         (bndPqSig (.snd (.snd (v sub))))))) fun ok2 =>
                .ite (.not (.and (v ok1) (v ok2)))
                  (.ret (rsE rNoneE (v st)))
                  (bindV (H.callPrim .kemEncaps
                    (.pair (bndPqB (.snd (.snd (v sub)))) (v kemCoins))) fun enc? =>
                    caseOptV (v enc?)
                      (.ret (rsE rNoneE (v st)))
                      (fun sc =>
                        bindV (H.callPrim .x25519Base (v ekASk)) fun ekAPk =>
                        bindV (H.callPrim .x25519
                          (.pair (peSec0 (.snd (v uFound)))
                                 (bndSpkB (.snd (.snd (v sub)))))) fun dh1 =>
                        bindV (H.callPrim .x25519
                          (.pair (v ekASk) (bndIkB (.snd (.snd (v sub)))))) fun dh2 =>
                        bindV (H.callPrim .x25519
                          (.pair (v ekASk) (bndSpkB (.snd (.snd (v sub)))))) fun dh3 =>
                        bindV
                          (caseOptV (bndOpkB (.snd (.snd (v sub))))
                            (.ret .none)
                            (fun opk =>
                              bindV (H.callPrim .x25519 (.pair (v ekASk) (.snd (v opk)))) fun d =>
                                .ret (.some (v d))))
                          fun dh4? =>
                        bindV (H.callPrim .hkdfDerive96
                          (buildSecretsE H (v dh1) (v dh2) (v dh3) (v dh4?) (.fst (v sc))))
                          fun drKeyReal =>
                        bindV (honestPeerC (S := S) H (stPrin (v st))
                          (bndIkB (.snd (.snd (v sub))))) fun honPeer =>
                        bindV (checkProvC H (v st) (.snd (.snd (v sub)))) fun prov =>
                        letV (τ := hdrT)
                          (.pair (peIkPk (.snd (v uFound)))
                            (.pair (v ekAPk) (.pair (bndSpkId (.snd (.snd (v sub))))
                              (.pair (optMapE (bndOpkB (.snd (.snd (v sub))))
                                fun opk => .fst (v opk))
                                (.pair (bndPqId (.snd (.snd (v sub)))) (.snd (v sc)))))))
                          fun hdrOut =>
                        letV (τ := e2eInitiatorEntryTy ℓ S)
                          (.pair (.fst (v sub)) (.pair (v honPeer)
                            (.pair (bndIkB (.snd (.snd (v sub))))
                              (.pair (bndSpkB (.snd (.snd (v sub))))
                                (.pair (optMapE (bndOpkB (.snd (.snd (v sub))))
                                  fun opk => .snd (v opk))
                                  (.pair (bndPqB (.snd (.snd (v sub))))
                                    (.pair (.fst (v prov))
                                      (.pair (.fst (.snd (v prov)))
                                        (.pair (.snd (.snd (v prov)))
                                          (.pair (v ekASk)
                                            (.pair (isSomeE (v honPeer))
                                              (.pair (v drKeyReal)
                                                (.pair (v drKeyReal)
                                                  (.pair (v hdrOut)
                                                    (.pair (.bool false)
                                                      (.bool false))))))))))))))))
                          fun sessV =>
                          bindV (partnerRandKeyC H (stResp (v st)) (v sessV)) fun prk? =>
                          bindV (caseOptV (v prk?) (sDrKey96C H) fun rk => .ret (v rk))
                            fun drKeyRand =>
                          bindV (findHonestC (S := S) H (stPrin (v st))
                            (bndIkB (.snd (.snd (v sub))))) fun fh =>
                            .ret (rsE
                              (eCaseOpt (v fh)
                                (rInitUnfreshE (v drKeyReal) (v hdrOut))
                                (fun _ => rHdrE (v hdrOut)))
                              (setSessE (v st)
                                (.cons (ieSetRandE (v sessV) (v drKeyRand)) (stSess (v st))))))))))

def initiateOpkBFuel (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr O Γ (FinT S.N_id)) (i : Expr O Γ (FinT S.N_send_opk))
    (bundle : Expr O Γ bundleT) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  .ite (isNoneE (bndOpkB bundle))
    (.ret (rsE rNoneE (v st)))
    (initiateCFuel H nFuel st (.inl (.pair u i)) u bundle)

def initiateOpkB (H : E2EPqxdhHooks ℓ O I) (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr O Γ (FinT S.N_id)) (i : Expr O Γ (FinT S.N_send_opk))
    (bundle : Expr O Γ bundleT) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  .ite (isNoneE (bndOpkB bundle))
    (.ret (rsE rNoneE (v st)))
    (initiateC H nAdv st (.inl (.pair u i)) u bundle)

def initiateNoOpkBFuel (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr O Γ (FinT S.N_id)) (i : Expr O Γ (FinT S.N_send_no_opk))
    (bundle : Expr O Γ bundleT) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  .ite (isSomeE (bndOpkB bundle))
    (.ret (rsE rNoneE (v st)))
    (initiateCFuel H nFuel st (.inr (.inl (.pair u i))) u bundle)

def initiateNoOpkB (H : E2EPqxdhHooks ℓ O I) (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr O Γ (FinT S.N_id)) (i : Expr O Γ (FinT S.N_send_no_opk))
    (bundle : Expr O Γ bundleT) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  .ite (isSomeE (bndOpkB bundle))
    (.ret (rsE rNoneE (v st)))
    (initiateC H nAdv st (.inr (.inl (.pair u i))) u bundle)

def acceptOpkBFuel (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (k : Expr O Γ (FinT S.N_id)) (j : Expr O Γ (FinT S.N_recv)) (o : Expr O Γ (FinT S.N_opk))
    (hdr : Expr O Γ hdrT) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  letV (.pair (.pair k (.pair j o)) hdr) fun args =>
    .ite (.not
      (.and (H.pureOp .pu32Eq (.pair (hdrSpkId (.snd (v args)))
              (H.pureOp .pu32OfNat (finValE H (.fst (.snd (.fst (v args))))))))
        (.and (H.pureOp .pu32Eq (.pair (hdrPqId (.snd (v args)))
                (H.pureOp .pu32OfNat (finValE H (.fst (.snd (.fst (v args))))))))
          (.and (optPu32EqE H (hdrOpkId (.snd (v args)))
                  (.some (H.pureOp .pu32OfNat (finValE H (.snd (.snd (.fst (v args))))))))
            (.and (natEqE (H.pureOp (.pbytesLen 32) (hdrIkA (.snd (v args)))) (.nat 32))
                  (natEqE (H.pureOp (.pbytesLen 32) (hdrEkA (.snd (v args)))) (.nat 32)))))))
      (.ret (rsE rNoneE (v st)))
      (.ite (eAny (min nFuel S.N_opk_tot) (stUsedOpk (v st)) fun x =>
            nat3EqE (v x) (.pair (finValE H (.fst (.fst (v args))))
              (.pair (finValE H (.fst (.snd (.fst (v args)))))
                     (finValE H (.snd (.snd (.fst (v args))))))))
        (.ret (rsE rNoneE (v st)))
        (bindV (koskSenderOkCFuel H nFuel (v st) (hdrIkA (.snd (v args)))) fun ksOk =>
          .ite (.not (v ksOk))
            (.ret (rsE rNoneE (v st)))
            (caseOptV (eFind (min nFuel S.N_id) (stPrin (v st)) fun p =>
                  natEqE (.fst (v p)) (finValE H (.fst (.fst (v args)))))
              (.ret (rsE rNoneE (v st)))
              (fun kFound =>
                caseOptV (eFind (min nFuel S.N_spk_tot) (stSpk (v st)) fun b =>
                      nat2EqE (.fst (v b))
                        (.pair (finValE H (.fst (.fst (v args))))
                               (finValE H (.fst (.snd (.fst (v args)))))))
                  (.ret (rsE rNoneE (v st)))
                  (fun bFound =>
                    caseOptV (eFind (min nFuel S.N_opk_tot) (stOpk (v st)) fun x =>
                          nat3EqE (.fst (v x))
                            (.pair (finValE H (.fst (.fst (v args))))
                              (.pair (finValE H (.fst (.snd (.fst (v args)))))
                                     (finValE H (.snd (.snd (.fst (v args))))))))
                      (.ret (rsE rNoneE (v st)))
                      (fun oFound =>
                        .ite (oeCons (.snd (v oFound)))
                          (.ret (rsE rNoneE (v st)))
                          (letV (checkSeenEFuel (S := S) H nFuel (stSeen (v st))
                              (finValE H (.fst (.fst (v args))))
                              (hdrPqId (.snd (v args)))
                              (hdrSpkId (.snd (v args)))
                              (hdrEkA (.snd (v args)))) fun seenRes =>
                            bindV (acceptKeysC H
                              (peSec0 (.snd (v kFound)))
                              (beSpkSk (.snd (v bFound)))
                              (.some (oeSk (.snd (v oFound))))
                              (bePqSk (.snd (v bFound)))
                              (.bool true)
                              (.fst (v seenRes))
                              (.snd (v args))) fun acc? =>
                              caseOptV (v acc?)
                                (.ret (rsE rNoneE (v st)))
                                (fun drKey =>
                                  bindV (findHonestCFuel (S := S) H nFuel (stPrin (v st))
                                    (hdrIkA (.snd (v args)))) fun fh =>
                                  bindV (recordRespCFuel H nFuel
                                    (setAcceptOpkE (v st)
                                      (eMap (min nFuel S.N_opk_tot) (stOpk (v st)) fun x =>
                                        .ite (nat3EqE (.fst (v x))
                                              (.pair (finValE H (.fst (.fst (v args))))
                                                (.pair (finValE H (.fst (.snd (.fst (v args)))))
                                                       (finValE H (.snd (.snd (.fst (v args))))))))
                                          (.pair (.fst (v x)) (oeSetConsE (.snd (v x))))
                                          (v x))
                                      (.cons
                                        (.pair (finValE H (.fst (.fst (v args))))
                                          (.pair (finValE H (.fst (.snd (.fst (v args)))))
                                                 (finValE H (.snd (.snd (.fst (v args)))))))
                                        (stUsedOpk (v st)))
                                      (.snd (v seenRes)))
                                    (.pair (.inr (.inr (.inl (.fst (v args)))))
                                      (.pair (peIkPk (.snd (v kFound)))
                                        (.pair (beSpkPk (.snd (v bFound)))
                                          (.pair (.some (oePk (.snd (v oFound))))
                                            (.pair (bePqPk (.snd (v bFound)))
                                              (.pair (.snd (v args))
                                                (.pair (isSomeE (v fh))
                                                  (.pair (v drKey)
                                                    (.pair (v drKey)
                                                      (.pair (.bool false)
                                                        (.bool false)))))))))))) fun st2 =>
                                    .ret (rsE
                                      (eCaseOpt (v fh) (rDrKeyE (v drKey))
                                        (fun _ => rAcceptFreshE))
                                      (v st2))))))))))

def acceptOpkB (H : E2EPqxdhHooks ℓ O I) (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (k : Expr O Γ (FinT S.N_id)) (j : Expr O Γ (FinT S.N_recv)) (o : Expr O Γ (FinT S.N_opk))
    (hdr : Expr O Γ hdrT) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  letV (.pair (.pair k (.pair j o)) hdr) fun args =>
    .ite (.not
      (.and (H.pureOp .pu32Eq (.pair (hdrSpkId (.snd (v args)))
              (H.pureOp .pu32OfNat (finValE H (.fst (.snd (.fst (v args))))))))
        (.and (H.pureOp .pu32Eq (.pair (hdrPqId (.snd (v args)))
                (H.pureOp .pu32OfNat (finValE H (.fst (.snd (.fst (v args))))))))
          (.and (optPu32EqE H (hdrOpkId (.snd (v args)))
                  (.some (H.pureOp .pu32OfNat (finValE H (.snd (.snd (.fst (v args))))))))
            (.and (natEqE (H.pureOp (.pbytesLen 32) (hdrIkA (.snd (v args)))) (.nat 32))
                  (natEqE (H.pureOp (.pbytesLen 32) (hdrEkA (.snd (v args)))) (.nat 32)))))))
      (.ret (rsE rNoneE (v st)))
      (.ite (eAny S.N_opk_tot (stUsedOpk (v st)) fun x =>
            nat3EqE (v x) (.pair (finValE H (.fst (.fst (v args))))
              (.pair (finValE H (.fst (.snd (.fst (v args)))))
                     (finValE H (.snd (.snd (.fst (v args))))))))
        (.ret (rsE rNoneE (v st)))
        (bindV (koskSenderOkC H nAdv (v st) (hdrIkA (.snd (v args)))) fun ksOk =>
          .ite (.not (v ksOk))
            (.ret (rsE rNoneE (v st)))
            (caseOptV (eFind S.N_id (stPrin (v st)) fun p =>
                  natEqE (.fst (v p)) (finValE H (.fst (.fst (v args)))))
              (.ret (rsE rNoneE (v st)))
              (fun kFound =>
                caseOptV (eFind S.N_spk_tot (stSpk (v st)) fun b =>
                      nat2EqE (.fst (v b))
                        (.pair (finValE H (.fst (.fst (v args))))
                               (finValE H (.fst (.snd (.fst (v args)))))))
                  (.ret (rsE rNoneE (v st)))
                  (fun bFound =>
                    caseOptV (eFind S.N_opk_tot (stOpk (v st)) fun x =>
                          nat3EqE (.fst (v x))
                            (.pair (finValE H (.fst (.fst (v args))))
                              (.pair (finValE H (.fst (.snd (.fst (v args)))))
                                     (finValE H (.snd (.snd (.fst (v args))))))))
                      (.ret (rsE rNoneE (v st)))
                      (fun oFound =>
                        .ite (oeCons (.snd (v oFound)))
                          (.ret (rsE rNoneE (v st)))
                          (letV (checkSeenE (S := S) H (stSeen (v st))
                              (finValE H (.fst (.fst (v args))))
                              (hdrPqId (.snd (v args)))
                              (hdrSpkId (.snd (v args)))
                              (hdrEkA (.snd (v args)))) fun seenRes =>
                            bindV (acceptKeysC H
                              (peSec0 (.snd (v kFound)))
                              (beSpkSk (.snd (v bFound)))
                              (.some (oeSk (.snd (v oFound))))
                              (bePqSk (.snd (v bFound)))
                              (.bool true)
                              (.fst (v seenRes))
                              (.snd (v args))) fun acc? =>
                              caseOptV (v acc?)
                                (.ret (rsE rNoneE (v st)))
                                (fun drKey =>
                                  bindV (findHonestC (S := S) H (stPrin (v st))
                                    (hdrIkA (.snd (v args)))) fun fh =>
                                  bindV (recordRespC H
                                    (setAcceptOpkE (v st)
                                      (eMap S.N_opk_tot (stOpk (v st)) fun x =>
                                        .ite (nat3EqE (.fst (v x))
                                              (.pair (finValE H (.fst (.fst (v args))))
                                                (.pair (finValE H (.fst (.snd (.fst (v args)))))
                                                       (finValE H (.snd (.snd (.fst (v args))))))))
                                          (.pair (.fst (v x)) (oeSetConsE (.snd (v x))))
                                          (v x))
                                      (.cons
                                        (.pair (finValE H (.fst (.fst (v args))))
                                          (.pair (finValE H (.fst (.snd (.fst (v args)))))
                                                 (finValE H (.snd (.snd (.fst (v args)))))))
                                        (stUsedOpk (v st)))
                                      (.snd (v seenRes)))
                                    (.pair (.inr (.inr (.inl (.fst (v args)))))
                                      (.pair (peIkPk (.snd (v kFound)))
                                        (.pair (beSpkPk (.snd (v bFound)))
                                          (.pair (.some (oePk (.snd (v oFound))))
                                            (.pair (bePqPk (.snd (v bFound)))
                                              (.pair (.snd (v args))
                                                (.pair (isSomeE (v fh))
                                                  (.pair (v drKey)
                                                    (.pair (v drKey)
                                                      (.pair (.bool false)
                                                        (.bool false)))))))))))) fun st2 =>
                                    .ret (rsE
                                      (eCaseOpt (v fh) (rDrKeyE (v drKey))
                                        (fun _ => rAcceptFreshE))
                                      (v st2))))))))))

def acceptNoOpkBFuel (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (k : Expr O Γ (FinT S.N_id)) (j : Expr O Γ (FinT S.N_recv)) (l : Expr O Γ (FinT S.N_no_opk))
    (hdr : Expr O Γ hdrT) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  letV (.pair (.pair k (.pair j l)) hdr) fun args =>
    .ite (.not
      (.and (H.pureOp .pu32Eq (.pair (hdrSpkId (.snd (v args)))
              (H.pureOp .pu32OfNat (finValE H (.fst (.snd (.fst (v args))))))))
        (.and (H.pureOp .pu32Eq (.pair (hdrPqId (.snd (v args)))
                (H.pureOp .pu32OfNat (finValE H (.fst (.snd (.fst (v args))))))))
          (.and (isNoneE (hdrOpkId (.snd (v args))))
            (.and (natEqE (H.pureOp (.pbytesLen 32) (hdrIkA (.snd (v args)))) (.nat 32))
                  (natEqE (H.pureOp (.pbytesLen 32) (hdrEkA (.snd (v args)))) (.nat 32)))))))
      (.ret (rsE rNoneE (v st)))
      (.ite (eAny (min nFuel S.N_no_opk_tot) (stUsedNoOpk (v st)) fun x =>
            nat3EqE (v x) (.pair (finValE H (.fst (.fst (v args))))
              (.pair (finValE H (.fst (.snd (.fst (v args)))))
                     (finValE H (.snd (.snd (.fst (v args))))))))
        (.ret (rsE rNoneE (v st)))
        (bindV (koskSenderOkCFuel H nFuel (v st) (hdrIkA (.snd (v args)))) fun ksOk =>
          .ite (.not (v ksOk))
            (.ret (rsE rNoneE (v st)))
            (caseOptV (eFind (min nFuel S.N_id) (stPrin (v st)) fun p =>
                  natEqE (.fst (v p)) (finValE H (.fst (.fst (v args)))))
              (.ret (rsE rNoneE (v st)))
              (fun kFound =>
                caseOptV (eFind (min nFuel S.N_spk_tot) (stSpk (v st)) fun b =>
                      nat2EqE (.fst (v b))
                        (.pair (finValE H (.fst (.fst (v args))))
                               (finValE H (.fst (.snd (.fst (v args)))))))
                  (.ret (rsE rNoneE (v st)))
                  (fun bFound =>
                    letV (checkSeenEFuel (S := S) H nFuel (stSeen (v st))
                        (finValE H (.fst (.fst (v args))))
                        (hdrPqId (.snd (v args)))
                        (hdrSpkId (.snd (v args)))
                        (hdrEkA (.snd (v args)))) fun seenRes =>
                      bindV (acceptKeysC H
                        (peSec0 (.snd (v kFound)))
                        (beSpkSk (.snd (v bFound)))
                        .none
                        (bePqSk (.snd (v bFound)))
                        (.bool true)
                        (.fst (v seenRes))
                        (.snd (v args))) fun acc? =>
                        caseOptV (v acc?)
                          (.ret (rsE rNoneE (v st)))
                          (fun drKey =>
                            bindV (findHonestCFuel (S := S) H nFuel (stPrin (v st))
                              (hdrIkA (.snd (v args)))) fun fh =>
                            bindV (recordRespCFuel H nFuel
                              (setAcceptNoOpkE (v st)
                                (.cons
                                  (.pair (finValE H (.fst (.fst (v args))))
                                    (.pair (finValE H (.fst (.snd (.fst (v args)))))
                                           (finValE H (.snd (.snd (.fst (v args)))))))
                                  (stUsedNoOpk (v st)))
                                (.snd (v seenRes)))
                              (.pair (.inr (.inr (.inr (.fst (v args)))))
                                (.pair (peIkPk (.snd (v kFound)))
                                  (.pair (beSpkPk (.snd (v bFound)))
                                    (.pair .none
                                      (.pair (bePqPk (.snd (v bFound)))
                                        (.pair (.snd (v args))
                                          (.pair (isSomeE (v fh))
                                            (.pair (v drKey)
                                              (.pair (v drKey)
                                                (.pair (.bool false)
                                                  (.bool false)))))))))))) fun st2 =>
                              .ret (rsE
                                (eCaseOpt (v fh) (rDrKeyE (v drKey))
                                  (fun _ => rAcceptFreshE))
                                (v st2))))))))

def acceptNoOpkB (H : E2EPqxdhHooks ℓ O I) (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (k : Expr O Γ (FinT S.N_id)) (j : Expr O Γ (FinT S.N_recv)) (l : Expr O Γ (FinT S.N_no_opk))
    (hdr : Expr O Γ hdrT) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  letV (.pair (.pair k (.pair j l)) hdr) fun args =>
    .ite (.not
      (.and (H.pureOp .pu32Eq (.pair (hdrSpkId (.snd (v args)))
              (H.pureOp .pu32OfNat (finValE H (.fst (.snd (.fst (v args))))))))
        (.and (H.pureOp .pu32Eq (.pair (hdrPqId (.snd (v args)))
                (H.pureOp .pu32OfNat (finValE H (.fst (.snd (.fst (v args))))))))
          (.and (isNoneE (hdrOpkId (.snd (v args))))
            (.and (natEqE (H.pureOp (.pbytesLen 32) (hdrIkA (.snd (v args)))) (.nat 32))
                  (natEqE (H.pureOp (.pbytesLen 32) (hdrEkA (.snd (v args)))) (.nat 32)))))))
      (.ret (rsE rNoneE (v st)))
      (.ite (eAny S.N_no_opk_tot (stUsedNoOpk (v st)) fun x =>
            nat3EqE (v x) (.pair (finValE H (.fst (.fst (v args))))
              (.pair (finValE H (.fst (.snd (.fst (v args)))))
                     (finValE H (.snd (.snd (.fst (v args))))))))
        (.ret (rsE rNoneE (v st)))
        (bindV (koskSenderOkC H nAdv (v st) (hdrIkA (.snd (v args)))) fun ksOk =>
          .ite (.not (v ksOk))
            (.ret (rsE rNoneE (v st)))
            (caseOptV (eFind S.N_id (stPrin (v st)) fun p =>
                  natEqE (.fst (v p)) (finValE H (.fst (.fst (v args)))))
              (.ret (rsE rNoneE (v st)))
              (fun kFound =>
                caseOptV (eFind S.N_spk_tot (stSpk (v st)) fun b =>
                      nat2EqE (.fst (v b))
                        (.pair (finValE H (.fst (.fst (v args))))
                               (finValE H (.fst (.snd (.fst (v args)))))))
                  (.ret (rsE rNoneE (v st)))
                  (fun bFound =>
                    letV (checkSeenE (S := S) H (stSeen (v st))
                        (finValE H (.fst (.fst (v args))))
                        (hdrPqId (.snd (v args)))
                        (hdrSpkId (.snd (v args)))
                        (hdrEkA (.snd (v args)))) fun seenRes =>
                      bindV (acceptKeysC H
                        (peSec0 (.snd (v kFound)))
                        (beSpkSk (.snd (v bFound)))
                        .none
                        (bePqSk (.snd (v bFound)))
                        (.bool true)
                        (.fst (v seenRes))
                        (.snd (v args))) fun acc? =>
                        caseOptV (v acc?)
                          (.ret (rsE rNoneE (v st)))
                          (fun drKey =>
                            bindV (findHonestC (S := S) H (stPrin (v st))
                              (hdrIkA (.snd (v args)))) fun fh =>
                            bindV (recordRespC H
                              (setAcceptNoOpkE (v st)
                                (.cons
                                  (.pair (finValE H (.fst (.fst (v args))))
                                    (.pair (finValE H (.fst (.snd (.fst (v args)))))
                                           (finValE H (.snd (.snd (.fst (v args)))))))
                                  (stUsedNoOpk (v st)))
                                (.snd (v seenRes)))
                              (.pair (.inr (.inr (.inr (.fst (v args)))))
                                (.pair (peIkPk (.snd (v kFound)))
                                  (.pair (beSpkPk (.snd (v bFound)))
                                    (.pair .none
                                      (.pair (bePqPk (.snd (v bFound)))
                                        (.pair (.snd (v args))
                                          (.pair (isSomeE (v fh))
                                            (.pair (v drKey)
                                              (.pair (v drKey)
                                                (.pair (.bool false)
                                                  (.bool false)))))))))))) fun st2 =>
                              .ret (rsE
                                (eCaseOpt (v fh) (rDrKeyE (v drKey))
                                  (fun _ => rAcceptFreshE))
                                (v st2))))))))

def testBFuel (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (sid : Expr O Γ (sidT S)) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  letV sid fun sidV =>
    .ite (.not (isTestableEFuel H nFuel (v st) (v sidV)))
      (.ret (rsE rNoneE (v st)))
      (caseOptV (eFind (min nFuel S.N_send_tot) (stSess (v st)) fun e => sidEqE H (ieSid (v e)) (v sidV))
        (caseOptV (eFind (min nFuel S.N_recv_tot) (stResp (v st)) fun r => sidEqE H (reSid (v r)) (v sidV))
          (.ret (rsE rNoneE (v st)))
          (fun r =>
            let rs' := eMap (min nFuel S.N_recv_tot) (stResp (v st)) fun x =>
              .ite (sidEqE H (reSid (v x)) (v sidV)) (reSetTestedE (v x)) (v x)
            .ret (rsE (rDrKeyE (.ite (stSecb (v st)) (reReal (v r)) (reRand (v r))))
              (setRespE (v st) rs'))))
        (fun e =>
          let ss' := eMap (min nFuel S.N_send_tot) (stSess (v st)) fun x =>
            .ite (sidEqE H (ieSid (v x)) (v sidV)) (ieSetTestedE (v x)) (v x)
          .ret (rsE (rDrKeyE (.ite (stSecb (v st)) (ieReal (v e)) (ieRand (v e))))
            (setSessE (v st) ss'))))

def testB (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (sid : Expr O Γ (sidT S)) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  letV sid fun sidV =>
    .ite (.not (isTestableE H (v st) (v sidV)))
      (.ret (rsE rNoneE (v st)))
      (caseOptV (eFind S.N_send_tot (stSess (v st)) fun e => sidEqE H (ieSid (v e)) (v sidV))
        (caseOptV (eFind S.N_recv_tot (stResp (v st)) fun r => sidEqE H (reSid (v r)) (v sidV))
          (.ret (rsE rNoneE (v st)))
          (fun r =>
            let rs' := eMap S.N_recv_tot (stResp (v st)) fun x =>
              .ite (sidEqE H (reSid (v x)) (v sidV)) (reSetTestedE (v x)) (v x)
            .ret (rsE (rDrKeyE (.ite (stSecb (v st)) (reReal (v r)) (reRand (v r))))
              (setRespE (v st) rs'))))
        (fun e =>
          let ss' := eMap S.N_send_tot (stSess (v st)) fun x =>
            .ite (sidEqE H (ieSid (v x)) (v sidV)) (ieSetTestedE (v x)) (v x)
          .ret (rsE (rDrKeyE (.ite (stSecb (v st)) (ieReal (v e)) (ieRand (v e))))
            (setSessE (v st) ss'))))

def ro1KeyRealB (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (secrets : Expr O Γ (PB 192)) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  bindV (H.callPrim .hkdfDerive96 secrets) fun dk =>
    .ret (rsE (rDrKeyE (v dk)) (v st))

def revealDh1KeyRealB {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  .ret (rsE rNoneE (v st))

def revealBFuel (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (sid : Expr O Γ (sidT S)) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  letV sid fun sidV =>
    caseOptV (eFind (min nFuel S.N_send_tot) (stSess (v st)) fun e => sidEqE H (ieSid (v e)) (v sidV))
      (caseOptV (eFind (min nFuel S.N_recv_tot) (stResp (v st)) fun r => sidEqE H (reSid (v r)) (v sidV))
        (.ret (rsE rNoneE (v st)))
        (fun r =>
          .ite (reTested (v r))
            (.ret (rsE rNoneE (v st)))
            (let rs' := eMap (min nFuel S.N_recv_tot) (stResp (v st)) fun x =>
               .ite (sidEqE H (reSid (v x)) (v sidV)) (reSetRevE (v x)) (v x)
             .ret (rsE (rDrKeyE (reReal (v r))) (setRespE (v st) rs')))))
      (fun e =>
        .ite (ieTested (v e))
          (.ret (rsE rNoneE (v st)))
          (let ss' := eMap (min nFuel S.N_send_tot) (stSess (v st)) fun x =>
             .ite (sidEqE H (ieSid (v x)) (v sidV)) (ieSetRevE (v x)) (v x)
           .ret (rsE (rDrKeyE (ieReal (v e))) (setSessE (v st) ss'))))

def revealB (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (sid : Expr O Γ (sidT S)) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  letV sid fun sidV =>
    caseOptV (eFind S.N_send_tot (stSess (v st)) fun e => sidEqE H (ieSid (v e)) (v sidV))
      (caseOptV (eFind S.N_recv_tot (stResp (v st)) fun r => sidEqE H (reSid (v r)) (v sidV))
        (.ret (rsE rNoneE (v st)))
        (fun r =>
          .ite (reTested (v r))
            (.ret (rsE rNoneE (v st)))
            (let rs' := eMap S.N_recv_tot (stResp (v st)) fun x =>
               .ite (sidEqE H (reSid (v x)) (v sidV)) (reSetRevE (v x)) (v x)
             .ret (rsE (rDrKeyE (reReal (v r))) (setRespE (v st) rs')))))
      (fun e =>
        .ite (ieTested (v e))
          (.ret (rsE rNoneE (v st)))
          (let ss' := eMap S.N_send_tot (stSess (v st)) fun x =>
             .ite (sidEqE H (ieSid (v x)) (v sidV)) (ieSetRevE (v x)) (v x)
           .ret (rsE (rDrKeyE (ieReal (v e))) (setSessE (v st) ss'))))

def registerB (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (sk : Expr O Γ (PB 32)) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  letV sk fun skV =>
    .ite (.not (natEqE (H.pureOp (.pbytesLen 32) (v skV)) (.nat 32)))
      (.ret (rsE rNoneE (v st)))
      (bindV (H.callPrim .x25519Base (v skV)) fun pk =>
        .ret (rsE (rPkE (v pk))
          (setAdvE (v st) (.cons (.pair (v skV) (v pk)) (stAdv (v st))))))

def revealSpkBFuel (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr O Γ (FinT S.N_id)) (j : Expr O Γ (FinT S.N_recv)) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  letV (.pair (finValE H u) (finValE H j)) fun uj =>
    caseOptV (eFind (min nFuel S.N_spk_tot) (stSpk (v st)) fun b => nat2EqE (.fst (v b)) (v uj))
      (.ret (rsE rNoneE (v st)))
      (fun bFound =>
        let bs' := eMap (min nFuel S.N_spk_tot) (stSpk (v st)) fun b =>
          .ite (nat2EqE (.fst (v b)) (v uj))
            (.pair (.fst (v b)) (beSetRevE (.snd (v b))))
            (v b)
        .ret (rsE (rSpkSkE (beSpkSk (.snd (v bFound)))) (setSpkE (v st) bs')))

def revealSpkB (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr O Γ (FinT S.N_id)) (j : Expr O Γ (FinT S.N_recv)) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  letV (.pair (finValE H u) (finValE H j)) fun uj =>
    caseOptV (eFind S.N_spk_tot (stSpk (v st)) fun b => nat2EqE (.fst (v b)) (v uj))
      (.ret (rsE rNoneE (v st)))
      (fun bFound =>
        let bs' := eMap S.N_spk_tot (stSpk (v st)) fun b =>
          .ite (nat2EqE (.fst (v b)) (v uj))
            (.pair (.fst (v b)) (beSetRevE (.snd (v b))))
            (v b)
        .ret (rsE (rSpkSkE (beSpkSk (.snd (v bFound)))) (setSpkE (v st) bs')))

end BranchDefs

/-! ## Evaluation equivalence -/

section BranchProofs

variable {ℓ : ℕ} {S : Setup} {Pt : Type} {P : Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
  {ι : Type} {T : OracleSpec ι} {I₀ : Iface (e2eSig ℓ) T}

@[reducible] def encKiStepOut (out : KeyIndResponse × KeyIndState S) :
    (Ty.prod (keyIndRT (ℓ := ℓ)) (e2eKeyIndStateTy ℓ S)).denote :=
  (keyIndRenc out.1, e2eKeyIndStateToVal out.2)

@[simp] theorem eval_natEqE {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (a b : Expr O Γ .nat) (ρ : Env Γ) :
    (natEqE a b).eval ρ = (a.eval ρ == b.eval ρ) := by
  unfold natEqE
  change decide (a.eval ρ = b.eval ρ) = (a.eval ρ == b.eval ρ)
  by_cases h : a.eval ρ = b.eval ρ <;> simp [h]

@[simp] theorem mkStepAPqxdhHooks_pureOp (o : E2EPureOp)
    {Γ : List (Ty (e2eSig ℓ))} (e : Expr (e2eOps ℓ P C K decT encT) Γ ((e2ePureOps ℓ).dom o)) :
    (mkStepAPqxdhHooks ℓ P C K decT encT I₀).pureOp o e = e2ePureOp o e := rfl

@[simp] theorem mkStepAPqxdhHooks_callPrim (o : E2ECryptoOp)
    {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ ((e2eCryptoOps ℓ P C K).dom o)) :
    (mkStepAPqxdhHooks ℓ P C K decT encT I₀).callPrim o e = .ret (e2eCryptoOp o e) := rfl

theorem eval_iteC {O : Ops (e2eSig ℓ)} {I : Iface (e2eSig ℓ) T}
    {Γ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)}
    (c : Expr O Γ .bool) (t e : Comp O I Γ τ) (ρ : Env Γ) :
    (Comp.ite c t e).eval ρ = if c.eval ρ then t.eval ρ else e.eval ρ := rfl

theorem eval_iteC_eq {O : Ops (e2eSig ℓ)} {I : Iface (e2eSig ℓ) T}
    {Γ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)}
    {c : Expr O Γ .bool} {t e : Comp O I Γ τ} {ρ : Env Γ} {b : Bool}
    (hc : c.eval ρ = b) :
    (Comp.ite c t e).eval ρ = if b then t.eval ρ else e.eval ρ := by
  rw [eval_iteC, hc]

theorem eval_retC {O : Ops (e2eSig ℓ)} {I : Iface (e2eSig ℓ) T}
    {Γ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)}
    (e : Expr O Γ τ) (ρ : Env Γ) :
    (Comp.ret (I := I) e).eval ρ = pure (e.eval ρ) := rfl

theorem eval_letV {O : Ops (e2eSig ℓ)} {I : Iface (e2eSig ℓ) T}
    {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ τ) (k : Var (τ :: Γ) τ → Comp O I (τ :: Γ) υ) (ρ : Env Γ) :
    (letV e k).eval ρ = (k .zero).eval (.cons (e.eval ρ) ρ) := by
  simp only [letV, Comp.eval, pure_bind]

theorem eval_letV_eq {O : Ops (e2eSig ℓ)} {I : Iface (e2eSig ℓ) T}
    {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    {e : Expr O Γ τ} {k : Var (τ :: Γ) τ → Comp O I (τ :: Γ) υ} {ρ : Env Γ}
    {val : τ.denote} (he : e.eval ρ = val) :
    (letV e k).eval ρ = (k .zero).eval (.cons val ρ) := by
  rw [eval_letV, he]

theorem eval_bindV {O : Ops (e2eSig ℓ)} {I : Iface (e2eSig ℓ) T}
    {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    (c : Comp O I Γ τ) (k : Var (τ :: Γ) τ → Comp O I (τ :: Γ) υ) (ρ : Env Γ) :
    (bindV c k).eval ρ = c.eval ρ >>= fun x => (k .zero).eval (.cons x ρ) := rfl

theorem eval_bindV_eq {O : Ops (e2eSig ℓ)} {I : Iface (e2eSig ℓ) T}
    {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    {c : Comp O I Γ τ} {k : Var (τ :: Γ) τ → Comp O I (τ :: Γ) υ} {ρ : Env Γ}
    {m : OracleComp T τ.denote} (hc : c.eval ρ = m) :
    (bindV c k).eval ρ = m >>= fun x => (k .zero).eval (.cons x ρ) := by
  rw [eval_bindV, hc]

theorem eval_caseOptV {O : Ops (e2eSig ℓ)} {I : Iface (e2eSig ℓ) T}
    {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt τ)) (n : Comp O I Γ υ)
    (s : Var (τ :: Γ) τ → Comp O I (τ :: Γ) υ) (ρ : Env Γ) :
    (caseOptV e n s).eval ρ =
      match e.eval ρ with
      | none => n.eval ρ
      | some x => (s .zero).eval (.cons x ρ) := by
  simp only [caseOptV, Comp.eval]
  cases e.eval ρ <;> rfl

theorem eval_caseOptV_eq {O : Ops (e2eSig ℓ)} {I : Iface (e2eSig ℓ) T}
    {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    {e : Expr O Γ (.opt τ)} {n : Comp O I Γ υ}
    {s : Var (τ :: Γ) τ → Comp O I (τ :: Γ) υ} {ρ : Env Γ}
    {v? : Option τ.denote} (he : e.eval ρ = v?) :
    (caseOptV e n s).eval ρ =
      Option.casesOn v? (n.eval ρ) (fun x => (s .zero).eval (.cons x ρ)) := by
  rw [eval_caseOptV, he]
  cases v? <;> rfl

private theorem st_run_pure {σ : Type} {m : Type → Type} [Monad m] {α : Type}
    (a : α) (s : σ) : (pure a : StateT σ m α).run s = pure (a, s) := rfl

private theorem st_run_get_bind {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (k : σ → StateT σ m α) (s : σ) :
    (get >>= k : StateT σ m α).run s = (k s).run s := by
  change (StateT.get >>= k).run s = (k s).run s
  simp only [StateT.run, Bind.bind, StateT.bind, StateT.get, pure_bind]

private theorem st_run_set_bind {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (s' : σ) (k : PUnit → StateT σ m α) (s : σ) :
    (set s' >>= k : StateT σ m α).run s = (k ⟨⟩).run s' := by
  change (StateT.set s' >>= k).run s = (k ⟨⟩).run s'
  simp only [StateT.run, Bind.bind, StateT.bind, StateT.set, pure_bind]

private theorem st_run_map_set {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α : Type} (f : PUnit → α) (s' s : σ) :
    (f <$> set s' : StateT σ m α).run s = pure (f ⟨⟩, s') := by
  simp [StateT.run, set, StateT.set, Functor.map, StateT.map]

private theorem st_run_lift_bind {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (c : m α) (k : α → StateT σ m β) (s : σ) :
    ((liftM c : StateT σ m α) >>= k).run s = c >>= fun a => (k a).run s := by
  change (StateT.lift c >>= k).run s = c >>= fun a => (k a).run s
  simp only [StateT.run, Bind.bind, StateT.bind, StateT.lift,
    LawfulMonad.bind_assoc, pure_bind]

private theorem st_run_bind {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (x : StateT σ m α) (k : α → StateT σ m β) (s : σ) :
    (x >>= k).run s = x.run s >>= fun p => (k p.1).run p.2 := rfl

private theorem st_run_ite {σ : Type} {m : Type → Type} {α : Type}
    (c : Prop) [Decidable c] (t e : StateT σ m α) (s : σ) :
    (if c then t else e).run s = if c then t.run s else e.run s := by
  split_ifs <;> rfl

private theorem fmap_bind {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β γ : Type} (f : α → β) (x : m α) (g : β → m γ) :
    (f <$> x) >>= g = x >>= fun a => g (f a) := by
  rw [map_eq_bind_pure_comp, LawfulMonad.bind_assoc]
  simp only [Function.comp_def, pure_bind]

private theorem eval_ret_rNoneE {Γ Δ : List (Ty (e2eSig ℓ))} [Ext Γ Δ]
    (stV : Var Γ (e2eKeyIndStateTy ℓ S)) (ρ : Env Δ)
    (st : KeyIndState S)
    (hst_eq : (v (O := e2eOps ℓ P C K decT encT) stV).eval ρ = e2eKeyIndStateToVal st) :
    (Comp.ret (I := stepAIface ℓ I₀)
      (rsE (O := e2eOps ℓ P C K decT encT) rNoneE (v stV))).eval ρ =
      (stepAIface ℓ I₀).liftP
        (encKiStepOut <$> (pure .noneResp : StateT (KeyIndState S) ProbComp KeyIndResponse).run st) := by
  simp only [eval_retC, rsE, rNoneE, Expr.eval, hst_eq, st_run_pure, map_pure, liftP_pure,
    encKiStepOut, keyIndRenc]

private theorem principals_any_eq (ps : List (ℕ × PrincipalEntry)) (n : ℕ) :
    (ps.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ)))).any (fun p => p.1 == n) =
      ps.any (fun (idx, _) => idx == n) := by
  rw [List.any_map]
  apply List.any_congr rfl
  rintro ⟨idx, _⟩
  rfl

private theorem principals_find_eq (ps : List (ℕ × PrincipalEntry)) (n : ℕ) :
    (ps.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ)))).find? (fun p => p.1 == n) =
      (ps.find? (fun (idx, _) => idx == n)).map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ))) := by
  rw [List.find?_map]
  congr 1

private theorem spkBundles_any_eq (bs : List ((ℕ × ℕ) × SpkBundleEntry)) (k : ℕ × ℕ) :
    (bs.map (Prod.map id (e2eSpkBundleEntryToVal (ℓ := ℓ)))).any (fun b => b.1 == k) =
      bs.any (fun (idx, _) => idx == k) := by
  rw [List.any_map]
  apply List.any_congr rfl
  rintro ⟨idx, _⟩
  rfl

private theorem spkBundles_find_eq (bs : List ((ℕ × ℕ) × SpkBundleEntry)) (k : ℕ × ℕ) :
    (bs.map (Prod.map id (e2eSpkBundleEntryToVal (ℓ := ℓ)))).find? (fun b => b.1 == k) =
      (bs.find? (fun (idx, _) => idx == k)).map (Prod.map id (e2eSpkBundleEntryToVal (ℓ := ℓ))) := by
  rw [List.find?_map]
  congr 1

private theorem opkEntries_any_eq (os : List ((ℕ × ℕ × ℕ) × OpkEntry)) (k : ℕ × ℕ × ℕ) :
    (os.map (Prod.map id (e2eOpkEntryToVal (ℓ := ℓ)))).any (fun x => x.1 == k) =
      os.any (fun (idx, _) => idx == k) := by
  rw [List.any_map]
  apply List.any_congr rfl
  rintro ⟨idx, _⟩
  rfl

private theorem opkEntries_find_eq (os : List ((ℕ × ℕ × ℕ) × OpkEntry)) (k : ℕ × ℕ × ℕ) :
    (os.map (Prod.map id (e2eOpkEntryToVal (ℓ := ℓ)))).find? (fun x => x.1 == k) =
      (os.find? (fun (idx, _) => idx == k)).map (Prod.map id (e2eOpkEntryToVal (ℓ := ℓ))) := by
  rw [List.find?_map]
  congr 1

set_option linter.unusedSimpArgs false in
theorem eval_initPrin1KeyB (hP : WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (uE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id)) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st)
    (hst : KeyIndSetupBounded S st) :
    (initPrin1KeyB (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) stV uE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P (.initPrin (uE.eval ρ))).run st)) := by
  have hp_len :
      (st.principals.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ)))).length ≤ S.N_id := by
    simpa using hst.principals_le
  simp only [initPrin1KeyB, letV, bindV, eAny, finValE, mkStepAPqxdhHooks, Comp.eval, v,
    ext_refl_wk, ext_step_wk, Expr.eval, eval_natEqE, eval_e2ePureOp, E2EPureOp.eval, env_get_zero,
    env_get_succ, pure_bind, hst_eq, stPrin, e2eKeyIndStateToVal, List.take_of_length_le hp_len]
  set u := uE.eval ρ
  rw [principals_any_eq]
  unfold pqxdhKeyIndImpl1KeyReal sampleScalar32
  simp only [LawfulMonad.bind_assoc, st_run_get_bind, st_run_ite]
  split_ifs with hdup
  · simp only [Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ,
      rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure, encKiStepOut, keyIndRenc]
  · simp only [Comp.eval, eval_sBytes32C, v, ext_refl_wk, ext_step_wk, Expr.eval,
      eval_e2eCryptoOp, env_get_zero, env_get_succ,
      LawfulMonad.bind_assoc, st_run_lift_bind, st_run_set_bind, st_run_map_set, st_run_pure,
      map_bind, map_pure, pure_bind, liftP_bind, liftP_pure]
    congr 1
    funext sec
    have hxb := e2eCryptoOps_eval_x25519Base_lossless ℓ hP C K sec
    dsimp only [e2eCryptoOps] at hxb
    rw [hxb]
    cases st
    simp only [v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ, rsE, rInitPrinE,
      setPrinE, eLet, hst_eq, encKiStepOut, keyIndRenc, e2eKeyIndStateToVal,
      e2ePrincipalEntryToVal, stSecb, stPrin, List.map_cons, Prod.map, id]

set_option linter.unusedSimpArgs false in
theorem eval_corruptB {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (uE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id)) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st)
    (hst : KeyIndSetupBounded S st) :
    (corruptB (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) stV uE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P (.corruptIK (uE.eval ρ))).run st)) := by
  have hp_len :
      (st.principals.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ)))).length ≤ S.N_id := by
    simpa using hst.principals_le
  simp only [corruptB, letV, caseOptV, eFind, eMap, finValE, mkStepAPqxdhHooks, Comp.eval,
    v, ext_refl_wk, ext_step_wk, Expr.eval, eval_natEqE, eval_e2ePureOp, E2EPureOp.eval,
    env_get_zero, env_get_succ, pure_bind, hst_eq, stPrin, e2eKeyIndStateToVal,
    List.take_of_length_le hp_len]
  set u := uE.eval ρ
  rw [principals_find_eq]
  unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl
  simp only [LawfulMonad.bind_assoc, st_run_get_bind]
  rcases hfind : st.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨_, entry⟩
  · simp only [hfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero,
      env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure, encKiStepOut,
      keyIndRenc]
  · simp only [hfind, Option.map, Prod.map, id, Comp.eval, v, ext_refl_wk, ext_step_wk,
      Expr.eval, env_get_zero, env_get_succ, hst_eq, List.take_of_length_le hp_len,
      LawfulMonad.bind_assoc, st_run_set_bind, st_run_map_set, st_run_pure, map_pure,
      liftP_pure, encKiStepOut, keyIndRenc, rsE, rCorrE, setPrinE, eLet, stSecb, stPrin, stSpk,
      stOpk, stSess, stResp, stUsedOpk, stUsedNoOpk, stSeen, stRo, stAdv, peSec0, peSecSign,
      e2eKeyIndStateToVal, e2ePrincipalEntryToVal]
    rw [show (st.principals.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ)))).map _ =
          (st.principals.map (fun (idx, e) =>
            if idx == u.val then (idx, { e with corrupted := true }) else (idx, e))).map
            (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ))) by
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro ⟨idx, e⟩ _
        by_cases h : idx = u.val <;>
          simp [h, beq_iff_eq, eval_natEqE, Prod.map, peSetCorrE, eLet, v, ext_refl_wk,
            ext_step_wk, Expr.eval, env_get_zero, env_get_succ, peSec0, peIkPk, peSecSign,
            peSignPk, e2ePrincipalEntryToVal]]

set_option linter.unusedSimpArgs false in
theorem eval_genSpkB (hP : WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (uE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (jE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv)) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st)
    (hst : KeyIndSetupBounded S st) :
    (genSpkB (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) stV uE jE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P (.genSPK (uE.eval ρ) (jE.eval ρ))).run st)) := by
  have hp_len :
      (st.principals.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ)))).length ≤ S.N_id := by
    simpa using hst.principals_le
  have hs_len :
      (st.spkBundles.map (Prod.map id (e2eSpkBundleEntryToVal (ℓ := ℓ)))).length ≤ S.N_spk_tot := by
    simpa using hst.spkBundles_le
  simp only [genSpkB, letV, caseOptV, bindV, eAny, eFind, finValE, mkStepAPqxdhHooks, Comp.eval,
    v, ext_refl_wk, ext_step_wk, Expr.eval, eval_natEqE, eval_e2ePureOp, E2EPureOp.eval,
    eval_nat2EqE, env_get_zero, env_get_succ, pure_bind, hst_eq, stSpk, stPrin,
    e2eKeyIndStateToVal, List.take_of_length_le hs_len, List.take_of_length_le hp_len]
  set u := uE.eval ρ
  set j := jE.eval ρ
  rw [spkBundles_any_eq, principals_find_eq]
  unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl sampleScalar32
  simp only [LawfulMonad.bind_assoc, st_run_get_bind, st_run_ite]
  split_ifs with hdup
  · simp only [Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ,
      rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure, encKiStepOut, keyIndRenc]
  · rcases hfind : st.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨_, uEntry⟩
    · simp only [hfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
        env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure,
        encKiStepOut, keyIndRenc]
    · simp only [hfind, Option.map, Prod.map, id, Comp.eval, eval_sBytes32C, eval_sRandom64C,
        eval_sKemKeyGenC hP, v, ext_refl_wk, ext_step_wk, Expr.eval, eval_e2eCryptoOp,
        eval_encECWideE, eval_encKEME, env_get_zero, env_get_succ, peSecSign,
        e2ePrincipalEntryToVal,
        LawfulMonad.bind_assoc, st_run_lift_bind, st_run_set_bind, st_run_map_set, st_run_pure,
        map_bind, map_pure, pure_bind, liftP_bind, liftP_pure]
      congr 1; funext spkSk
      have hxb := e2eCryptoOps_eval_x25519Base_lossless ℓ hP C K spkSk
      dsimp only [e2eCryptoOps] at hxb
      rw [hxb]
      congr 1; funext rSpk
      have hsig1 := e2eCryptoOps_eval_sigSign_lossless ℓ hP C K uEntry.secIKAsign
        (encodeEC (P.x25519Base spkSk)) rSpk
      dsimp only [e2eCryptoOps] at hsig1
      rw [hsig1]
      congr 1; funext ⟨pqPk, pqSk⟩
      congr 1; funext rPq
      have hsig2 := e2eCryptoOps_eval_sigSign_lossless ℓ hP C K uEntry.secIKAsign
        (encodeKEM pqPk) rPq
      dsimp only [e2eCryptoOps] at hsig2
      rw [hsig2]
      cases st
      simp only [v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ,
        eval_e2ePureOp, E2EPureOp.eval, rsE, rBundleE, setSpkE, eLet, hst_eq, encKiStepOut,
        keyIndRenc, bundleV, peIkPk, e2eKeyIndStateToVal, e2ePrincipalEntryToVal,
        e2eSpkBundleEntryToVal, stSecb, stPrin, stSpk, List.map_cons, Prod.map, id]

set_option linter.unusedSimpArgs false in
theorem eval_genOpkB (hP : WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (uE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (jE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (oE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_opk)) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st)
    (hst : KeyIndSetupBounded S st) :
    (genOpkB (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) stV uE jE oE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P (.genOPK (uE.eval ρ) (jE.eval ρ) (oE.eval ρ))).run st)) := by
  have ho_len :
      (st.opkEntries.map (Prod.map id (e2eOpkEntryToVal (ℓ := ℓ)))).length ≤ S.N_opk_tot := by
    simpa using hst.opkEntries_le
  simp only [genOpkB, letV, bindV, eAny, finValE, mkStepAPqxdhHooks, Comp.eval, v,
    ext_refl_wk, ext_step_wk, Expr.eval, eval_e2ePureOp, E2EPureOp.eval, eval_nat3EqE,
    env_get_zero, env_get_succ, pure_bind, hst_eq, stOpk, e2eKeyIndStateToVal,
    List.take_of_length_le ho_len]
  set u := uE.eval ρ
  set j := jE.eval ρ
  set o := oE.eval ρ
  rw [opkEntries_any_eq]
  unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl sampleScalar32
  simp only [LawfulMonad.bind_assoc, st_run_get_bind, st_run_ite]
  split_ifs with hdup
  · simp only [Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ,
      rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure, encKiStepOut, keyIndRenc]
  · simp only [Comp.eval, eval_sBytes32C, v, ext_refl_wk, ext_step_wk, Expr.eval,
      eval_e2eCryptoOp, env_get_zero, env_get_succ,
      LawfulMonad.bind_assoc, st_run_lift_bind, st_run_set_bind, st_run_map_set, st_run_pure,
      map_bind, map_pure, pure_bind, liftP_bind, liftP_pure]
    congr 1; funext opkSk
    have hxb := e2eCryptoOps_eval_x25519Base_lossless ℓ hP C K opkSk
    dsimp only [e2eCryptoOps] at hxb
    rw [hxb]
    cases st
    simp only [v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ, rsE, rPkE,
      setOpkE, eLet, hst_eq, encKiStepOut, keyIndRenc, e2eKeyIndStateToVal, e2eOpkEntryToVal,
      stSecb, stPrin, stSpk, stOpk, List.map_cons, Prod.map, id]

private theorem eval_ieSetRandE {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (sE : Expr O Γ (e2eInitiatorEntryTy ℓ S)) (rE : Expr O Γ drKeyT) (ρ : Env Γ)
    (s : KeyIndInitiatorEntry S) (hs : sE.eval ρ = e2eInitiatorEntryToVal s)
    (r : SignalPqxdh.DRKey) (hr : rE.eval ρ = drKeyV r) :
    (ieSetRandE sE rE).eval ρ = e2eInitiatorEntryToVal { s with drKeyRand := r } := by
  simp [ieSetRandE, eLet, hs, hr, v, ext_refl_wk, Expr.eval, env_get_zero,
    e2eInitiatorEntryToVal, ieSid, ieHonPeer, iePeerIk, iePeerSpk, iePeerOpk, iePeerPq,
    ieSpkHon, ieOpkHon, iePqHon, ieEkSk, ieFresh, ieReal, ieHdr, ieTested, ieRev]

set_option linter.unusedSimpArgs false in
theorem eval_initiateC (hP : WellFormedPrimitivesδ P) (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (uE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (bndE : Expr (e2eOps ℓ P C K decT encT) Γ bundleT) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st)
    (hst : KeyIndSetupBounded S st) (hadv : st.advKeys.length ≤ nAdv) :
    (initiateC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv stV sidE uE bndE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((runKeyIndInitiate false S P (sidOfV (sidE.eval ρ)) (uE.eval ρ)
          (bundleOfV (bndE.eval ρ))).run st)) := by
  set sid := sidOfV (sidE.eval ρ)
  have hsidE : sidE.eval ρ = sidV sid := (sidV_sidOfV (sidE.eval ρ)).symm
  set bnd := bundleOfV (bndE.eval ρ)
  have hbndE : bndE.eval ρ = bundleV bnd := (bundleV_bundleOfV (bndE.eval ρ)).symm
  set u := uE.eval ρ
  have hs_len :
      (st.sessions.map (e2eInitiatorEntryToVal (ℓ := ℓ))).length ≤ S.N_send_tot := by
    simpa using hst.sessions_le
  have hp_len :
      (st.principals.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ)))).length ≤ S.N_id := by
    simpa using hst.principals_le
  unfold initiateC
  rw [eval_letV_eq (val := (sidV sid, (u.val, bundleV bnd))) (by
        simp [finValE, Expr.eval, eval_e2ePureOp, E2EPureOp.eval, hsidE, hbndE, u]),
    eval_iteC_eq (b := st.sessions.any (fun e => e.sid == sid)) (by
      simp only [eAny, Expr.eval, eval_v_cons, eval_v_refl, env_get_zero, hst_eq, stSess,
        e2eKeyIndStateToVal, List.take_of_length_le hs_len, List.any_map]
      apply List.any_congr rfl; intro e; dsimp only [Function.comp_def]
      rw [eval_sidEqE]
      simp [ieSid, e2eInitiatorEntryToVal, sidOfV_sidV, Expr.eval, eval_v_cons, eval_v_refl,
        env_get_zero])]
  unfold runKeyIndInitiate sampleScalar32 sampleCoins32
  simp only [LawfulMonad.bind_assoc, st_run_get_bind, st_run_ite]
  by_cases hdup : st.sessions.any (fun e => e.sid == sid) = true
  · simp only [hdup, ↓reduceIte, ite_true]
    exact eval_ret_rNoneE stV _ st (by simp [hst_eq])
  · simp only [hdup, Bool.false_eq_true, ↓reduceIte, ite_false]
    rw [eval_caseOptV_eq
      (v? := (st.principals.find? (fun (idx, _) => idx == u.val)).map
        (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ)))) (by
      simp only [eFind, Expr.eval, eval_natEqE, eval_v_cons, eval_v_refl, env_get_zero, hst_eq,
        stPrin, e2eKeyIndStateToVal, List.take_of_length_le hp_len]
      exact principals_find_eq st.principals u.val)]
    rcases hfind : st.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨uIdx, uEntry⟩
    · simp only [hfind, Option.map]
      exact eval_ret_rNoneE stV _ st (by simp [hst_eq])
    · simp only [hfind, Option.map, Prod.map, id]
      rw [eval_bindV_eq (m := pure (koskBundleOk P st.principals st.spkBundles st.opkEntries
            st.advKeys bnd)) (by
            rw [eval_koskBundleOkC hP nAdv _ _ _ (by simp [hst_eq]) hst hadv]
            simp [Expr.eval, bundleOfV_bundleV]),
        pure_bind,
        eval_iteC_eq (b := !koskBundleOk P st.principals st.spkBundles st.opkEntries
            st.advKeys bnd) (by simp [Expr.eval]),
        st_run_ite]
      by_cases hkosk : koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bnd = true
      · simp only [hkosk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ite_false]
        rw [eval_bindV_eq (τ := PB 32)
              (m := (stepAIface ℓ I₀).liftP sampleBytes32) (eval_sBytes32C _)]
        simp only [LawfulMonad.bind_assoc, st_run_lift_bind, map_bind, liftP_bind]
        congr 1; funext ekASk
        rw [eval_bindV_eq (τ := PB 32)
              (m := (stepAIface ℓ I₀).liftP sampleBytes32) (eval_sBytes32C _)]
        congr 1; funext kemCoins
        rw [eval_bindV_eq (m := pure (resolveSigPk P st.principals bnd.ikB)) (by
              rw [eval_resolveSigPkC hP _ _ _
                (by simp [stPrin, Expr.eval, e2eKeyIndStateToVal, hst_eq]) hst.principals_le]
              simp [Expr.eval, bndIkB, bundleV]),
          pure_bind,
          eval_bindV_eq (m := pure (P.sigVerify (resolveSigPk P st.principals bnd.ikB)
              (encodeEC bnd.spkB) bnd.spkSig)) (by
            simp [mkStepAPqxdhHooks_callPrim, eval_retC, Expr.eval, eval_e2eCryptoOp,
              eval_encECWideE, bndSpkB, bndSpkSig, bundleV]
            rfl),
          pure_bind,
          eval_bindV_eq (m := pure (P.sigVerify (resolveSigPk P st.principals bnd.ikB)
              (encodeKEM bnd.pqspkB) bnd.pqspkSig)) (by
            simp [mkStepAPqxdhHooks_callPrim, eval_retC, Expr.eval, eval_e2eCryptoOp,
              eval_encKEME, bndPqB, bndPqSig, bundleV]
            rfl),
          pure_bind,
          eval_iteC_eq (b := !(P.sigVerify (resolveSigPk P st.principals bnd.ikB)
              (encodeEC bnd.spkB) bnd.spkSig &&
            P.sigVerify (resolveSigPk P st.principals bnd.ikB)
              (encodeKEM bnd.pqspkB) bnd.pqspkSig)) (by simp [Expr.eval]),
          st_run_ite]
        by_cases hsig :
            (P.sigVerify (resolveSigPk P st.principals bnd.ikB) (encodeEC bnd.spkB) bnd.spkSig &&
             P.sigVerify (resolveSigPk P st.principals bnd.ikB) (encodeKEM bnd.pqspkB) bnd.pqspkSig) = true
        · simp only [hsig, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ite_false]
          have henc := e2eCryptoOps_eval_kemEncaps_lossless ℓ hP C K bnd.pqspkB kemCoins
          dsimp only [e2eCryptoOps] at henc
          rw [eval_bindV_eq (m := pure (P.kemEncaps bnd.pqspkB kemCoins)) (by
                simp [mkStepAPqxdhHooks_callPrim, eval_retC, Expr.eval, eval_e2eCryptoOp,
                  bndPqB, bundleV, henc]),
            pure_bind,
            eval_caseOptV_eq (v? := P.kemEncaps bnd.pqspkB kemCoins) (by simp)]
          rcases hkem : P.kemEncaps bnd.pqspkB kemCoins with _ | ⟨ss, kemCt⟩
          · simp only [hkem]
            exact eval_ret_rNoneE stV _ st (by simp [hst_eq])
          · simp only [hkem]
            have hxb := e2eCryptoOps_eval_x25519Base_lossless ℓ hP C K ekASk
            have hdh1 := e2eCryptoOps_eval_x25519_lossless ℓ hP C K uEntry.secIKA0 bnd.spkB
            have hdh2 := e2eCryptoOps_eval_x25519_lossless ℓ hP C K ekASk bnd.ikB
            have hdh3 := e2eCryptoOps_eval_x25519_lossless ℓ hP C K ekASk bnd.spkB
            dsimp only [e2eCryptoOps] at hxb hdh1 hdh2 hdh3
            rw [eval_bindV_eq (m := pure (P.x25519Base ekASk)) (by
                  simp [mkStepAPqxdhHooks_callPrim, eval_retC, Expr.eval, eval_e2eCryptoOp, hxb]),
              pure_bind,
              eval_bindV_eq (m := pure (P.x25519 uEntry.secIKA0 bnd.spkB)) (by
                simp [mkStepAPqxdhHooks_callPrim, eval_retC, Expr.eval, eval_e2eCryptoOp,
                  peSec0, e2ePrincipalEntryToVal, bndSpkB, bundleV, hdh1]),
              pure_bind,
              eval_bindV_eq (m := pure (P.x25519 ekASk bnd.ikB)) (by
                simp [mkStepAPqxdhHooks_callPrim, eval_retC, Expr.eval, eval_e2eCryptoOp,
                  bndIkB, bundleV, hdh2]),
              pure_bind,
              eval_bindV_eq (m := pure (P.x25519 ekASk bnd.spkB)) (by
                simp [mkStepAPqxdhHooks_callPrim, eval_retC, Expr.eval, eval_e2eCryptoOp,
                  bndSpkB, bundleV, hdh3]),
              pure_bind,
              eval_bindV_eq (m := pure (bnd.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk))) (by
                rw [eval_caseOptV_eq (v? := bnd.opkB?)
                  (by simp [Expr.eval, bndOpkB, bundleV])]
                rcases bnd.opkB? with _ | ⟨oid, opkPk⟩
                · simp [eval_retC, Expr.eval]
                · have hdh4 := e2eCryptoOps_eval_x25519_lossless ℓ hP C K ekASk opkPk
                  dsimp only [e2eCryptoOps] at hdh4
                  simp [eval_bindV, mkStepAPqxdhHooks_callPrim, eval_retC, Expr.eval,
                    eval_e2eCryptoOp, hdh4, pure_bind]),
              pure_bind]
            set secrets := buildSecrets (P.x25519 uEntry.secIKA0 bnd.spkB)
              (P.x25519 ekASk bnd.ikB) (P.x25519 ekASk bnd.spkB)
              (bnd.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)) ss
            have hhk := e2eCryptoOps_eval_hkdfDerive96_lossless ℓ hP C K secrets
            dsimp only [e2eCryptoOps] at hhk
            set drKeyReal := P.hkdfDerive96 secrets
            set hdr : HandshakeHdr :=
              { ikAPk := uEntry.ikAPk, ekAPk := P.x25519Base ekASk, spkId := bnd.spkId,
                opkId? := bnd.opkB?.map Prod.fst, pqspkId := bnd.pqspkId, kemCt := kemCt }
            set honestPeer := isHonestUncorruptedPeer P st.principals bnd.ikB
            set prov := checkBundleProvenance P st.principals st.spkBundles st.opkEntries bnd
            set sessEntry : KeyIndInitiatorEntry S :=
              { sid := sid, honestPeer := honestPeer, peerIkPk := bnd.ikB,
                peerSpkPk := bnd.spkB, peerOpkPk? := bnd.opkB?.map Prod.snd,
                peerPqspkPk := bnd.pqspkB, spkHonest := prov.1, opkHonest := prov.2.1,
                pqspkHonest := prov.2.2, ekASk := ekASk, fresh := honestPeer.isSome,
                drKeyReal := drKeyReal, drKeyRand := drKeyReal, hdr := hdr, tested := false }
            rw [eval_bindV_eq (m := pure (drKeyV drKeyReal)) (by
                  simp [mkStepAPqxdhHooks_callPrim, eval_retC, Expr.eval, eval_e2eCryptoOp,
                    eval_buildSecretsE, hhk, secrets, drKeyReal, drKeyV]),
              pure_bind,
              eval_bindV_eq (m := pure honestPeer) (by
                rw [eval_honestPeerC hP _ _ _
                  (by simp [stPrin, Expr.eval, e2eKeyIndStateToVal, hst_eq]) hst.principals_le]
                simp [Expr.eval, bndIkB, bundleV, honestPeer]),
              pure_bind,
              eval_bindV_eq (m := pure prov) (by
                rw [eval_checkProvC hP _ _ _ (by simp [hst_eq]) hst]
                simp [Expr.eval, bundleOfV_bundleV, prov]),
              pure_bind,
              eval_letV_eq (val := hdrV hdr) (by
                simp [Expr.eval, peIkPk, e2ePrincipalEntryToVal, bndSpkId, bndOpkB, bndPqId,
                  bundleV, eval_optMapE, hdr, hdrV]),
              eval_letV_eq (val := e2eInitiatorEntryToVal sessEntry) (by
                simp [Expr.eval, bndIkB, bndSpkB, bndOpkB, bndPqB, bundleV, eval_optMapE,
                  eval_isSomeE, sessEntry, e2eInitiatorEntryToVal]),
              eval_bindV_eq
                (m := pure ((keyIndPartnerRandKey? P st.respSessions sessEntry).map drKeyV)) (by
                  exact eval_partnerRandKeyC hP _ _ _
                    (by simp [stResp, Expr.eval, e2eKeyIndStateToVal, hst_eq])
                    (by simp) hst.respSessions_le),
              pure_bind,
              eval_bindV_eq
                (m := (stepAIface ℓ I₀).liftP (drKeyV <$>
                  match keyIndPartnerRandKey? P st.respSessions sessEntry with
                  | some k => pure k
                  | none => sampleDRKey96)) (by
                  rw [eval_caseOptV_eq
                    (v? := (keyIndPartnerRandKey? P st.respSessions sessEntry).map drKeyV)
                    (by simp)]
                  rcases keyIndPartnerRandKey? P st.respSessions sessEntry with _ | k
                  · exact eval_sDrKey96C _
                  · simp [eval_retC, map_pure, liftP_pure])]
            unfold evalHkdfOrRo
            simp only [Bool.not_false, ↓reduceIte, ite_true, LawfulMonad.bind_assoc,
              st_run_lift_bind, pure_bind]
            have hpartner_bind :
                ((match keyIndPartnerRandKey? P st.respSessions sessEntry with
                  | some drKeyRand => do
                    set { st with sessions := { sessEntry with drKeyRand := drKeyRand } :: st.sessions }
                    match findHonestPrincipal P st.principals bnd.ikB with
                    | some _ => pure (KeyIndResponse.hdrResp hdr)
                    | none => pure (KeyIndResponse.initUnfreshResp drKeyReal hdr)
                  | none => do
                    let drKeyRand ← liftM sampleDRKey96
                    set { st with sessions := { sessEntry with drKeyRand := drKeyRand } :: st.sessions }
                    match findHonestPrincipal P st.principals bnd.ikB with
                    | some _ => pure (KeyIndResponse.hdrResp hdr)
                    | none => pure (KeyIndResponse.initUnfreshResp drKeyReal hdr)) :
                  StateT (KeyIndState S) ProbComp KeyIndResponse).run st =
                (match keyIndPartnerRandKey? P st.respSessions sessEntry with
                 | some k => pure k
                 | none => sampleDRKey96) >>= fun drKeyRand =>
                  ((do
                    set { st with sessions := { sessEntry with drKeyRand := drKeyRand } :: st.sessions }
                    match findHonestPrincipal P st.principals bnd.ikB with
                    | some _ => pure (KeyIndResponse.hdrResp hdr)
                    | none => pure (KeyIndResponse.initUnfreshResp drKeyReal hdr)) :
                    StateT (KeyIndState S) ProbComp KeyIndResponse).run st := by
              cases keyIndPartnerRandKey? P st.respSessions sessEntry
              · exact st_run_lift_bind sampleDRKey96 _ st
              · simp only [pure_bind]
            refine Eq.trans ?_
              (congrArg (fun m => (stepAIface ℓ I₀).liftP (encKiStepOut <$> m)) hpartner_bind.symm)
            simp only [liftP_bind, liftP_map, fmap_bind, map_bind, map_pure, pure_bind,
              LawfulMonad.bind_assoc, st_run_set_bind]
            congr 1; funext drKeyRand
            rw [eval_bindV_eq
                  (m := pure ((findHonestPrincipal P st.principals bnd.ikB).map
                    (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ))))) (by
                    rw [eval_findHonestC hP _ _ _
                      (by simp [stPrin, Expr.eval, e2eKeyIndStateToVal, hst_eq]) hst.principals_le]
                    simp [Expr.eval, bndIkB, bundleV]),
              pure_bind, eval_retC]
            have hie_rand :
                ∀ {Δ} (eS : Expr (e2eOps ℓ P C K decT encT) Δ (e2eInitiatorEntryTy ℓ S))
                  (eR : Expr (e2eOps ℓ P C K decT encT) Δ drKeyT) (ρ' : Env Δ),
                  eS.eval ρ' = e2eInitiatorEntryToVal sessEntry →
                  eR.eval ρ' = drKeyV drKeyRand →
                  (ieSetRandE eS eR).eval ρ' =
                    e2eInitiatorEntryToVal { sessEntry with drKeyRand := drKeyRand } :=
              fun eS eR ρ' hs hr => eval_ieSetRandE eS eR ρ' sessEntry hs drKeyRand hr
            simp only [rsE, setSessE, eLet, Expr.eval]
            rw [hie_rand _ _ _ (by simp) (by simp)]
            rcases hfh : findHonestPrincipal P st.principals bnd.ikB with _ | ⟨_, _⟩ <;>
              cases st <;>
              simp only [hfh, Option.map, eCaseOpt, Expr.eval, eval_v_cons, eval_v_refl,
                env_get_zero, env_get_succ, rHdrE, rInitUnfreshE, setSessE, eLet, hst_eq,
                st_run_pure, map_pure, liftP_pure, encKiStepOut, keyIndRenc, e2eKeyIndStateToVal,
                stSecb, stPrin, stSpk, stOpk, stSess, List.map_cons]
        · simp only [hsig, Bool.false_eq_true, Bool.not_false, ↓reduceIte, ite_true, ite_false]
          exact eval_ret_rNoneE stV _ st (by simp [hst_eq])
      · simp only [hkosk, Bool.false_eq_true, Bool.not_false, ↓reduceIte, ite_true, ite_false]
        exact eval_ret_rNoneE stV _ st (by simp [hst_eq])

set_option linter.unusedSimpArgs false in
theorem eval_initiateOpkB (hP : WellFormedPrimitivesδ P) (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (uE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (iE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_send_opk))
    (bndE : Expr (e2eOps ℓ P C K decT encT) Γ bundleT) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st)
    (hst : KeyIndSetupBounded S st) (hadv : st.advKeys.length ≤ nAdv) :
    (initiateOpkB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv stV uE iE bndE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P
          (.initiateOPK (uE.eval ρ) (iE.eval ρ) (bundleOfV (bndE.eval ρ)))).run st)) := by
  set bnd := bundleOfV (bndE.eval ρ)
  have hbndE : bndE.eval ρ = bundleV bnd := (bundleV_bundleOfV (bndE.eval ρ)).symm
  simp only [initiateOpkB, Comp.eval, Expr.eval, eval_isNoneE, bndOpkB, hbndE, bundleV]
  unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl
  simp only [LawfulMonad.bind_assoc, st_run_get_bind, st_run_ite]
  cases bnd.opkB?
  · simp only [Option.isNone, ↓reduceIte, ite_true, Comp.eval, v, ext_refl_wk, ext_step_wk,
      Expr.eval, env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure,
      liftP_pure, encKiStepOut, keyIndRenc]
  · simp only [Option.isNone, Bool.false_eq_true, ↓reduceIte, ite_false]
    have h := eval_initiateC (I₀ := I₀) hP nAdv stV (.inl (.pair uE iE)) uE bndE ρ hst_eq hst hadv
    simpa only [Expr.eval, sidOfV, hbndE, bundleOfV_bundleV] using h

set_option linter.unusedSimpArgs false in
theorem eval_initiateNoOpkB (hP : WellFormedPrimitivesδ P) (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (uE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (iE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_send_no_opk))
    (bndE : Expr (e2eOps ℓ P C K decT encT) Γ bundleT) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st)
    (hst : KeyIndSetupBounded S st) (hadv : st.advKeys.length ≤ nAdv) :
    (initiateNoOpkB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv stV uE iE bndE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P
          (.initiateNoOPK (uE.eval ρ) (iE.eval ρ) (bundleOfV (bndE.eval ρ)))).run st)) := by
  set bnd := bundleOfV (bndE.eval ρ)
  have hbndE : bndE.eval ρ = bundleV bnd := (bundleV_bundleOfV (bndE.eval ρ)).symm
  simp only [initiateNoOpkB, Comp.eval, Expr.eval, eval_isSomeE, bndOpkB, hbndE, bundleV]
  unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl
  simp only [LawfulMonad.bind_assoc, st_run_get_bind, st_run_ite]
  cases bnd.opkB?
  · simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte, ite_false]
    have h := eval_initiateC (I₀ := I₀) hP nAdv stV (.inr (.inl (.pair uE iE))) uE bndE ρ
      hst_eq hst hadv
    simpa only [Expr.eval, sidOfV, hbndE, bundleOfV_bundleV] using h
  · simp only [Option.isSome, ↓reduceIte, ite_true, Comp.eval, v, ext_refl_wk, ext_step_wk,
      Expr.eval, env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure,
      liftP_pure, encKiStepOut, keyIndRenc]

set_option linter.unusedSimpArgs false in
theorem eval_acceptOpkB (hP : WellFormedPrimitivesδ P) (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (kE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (jE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (oE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_opk))
    (hdrE : Expr (e2eOps ℓ P C K decT encT) Γ hdrT) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st)
    (hst : KeyIndSetupBounded S st) (hadv : st.advKeys.length ≤ nAdv) :
    (acceptOpkB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv stV kE jE oE hdrE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P
          (.acceptOPK (kE.eval ρ) (jE.eval ρ) (oE.eval ρ) (hdrOfV (hdrE.eval ρ)))).run st)) := by
  set hdr := hdrOfV (hdrE.eval ρ)
  have hhdrE : hdrE.eval ρ = hdrV hdr := (hdrV_hdrOfV (hdrE.eval ρ)).symm
  have hu_len : st.usedRecvOPK.length ≤ S.N_opk_tot := hst.usedRecvOPK_le
  have hp_len :
      (st.principals.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ)))).length ≤ S.N_id := by
    simpa using hst.principals_le
  have hb_len :
      (st.spkBundles.map (Prod.map id (e2eSpkBundleEntryToVal (ℓ := ℓ)))).length ≤ S.N_spk_tot := by
    simpa using hst.spkBundles_le
  have ho_len :
      (st.opkEntries.map (Prod.map id (e2eOpkEntryToVal (ℓ := ℓ)))).length ≤ S.N_opk_tot := by
    simpa using hst.opkEntries_le
  simp only [acceptOpkB, letV, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, eval_natEqE,
    eval_optPu32EqE, finValE, mkStepAPqxdhHooks_pureOp, eval_e2ePureOp, E2EPureOp.eval,
    env_get_zero, env_get_succ, pure_bind, hst_eq, hhdrE,
    hdrSpkId, hdrPqId, hdrOpkId, hdrIkA, hdrEkA, hdrV]
  set k := kE.eval ρ
  set j := jE.eval ρ
  set o := oE.eval ρ
  unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl
  simp only [LawfulMonad.bind_assoc, st_run_get_bind]
  have hhdr_guard :
      ((hdr.spkId == UInt32.ofNat j.val) &&
       ((hdr.pqspkId == UInt32.ofNat j.val) &&
        ((hdr.opkId? == some (UInt32.ofNat o.val)) &&
         ((hdr.ikAPk.length == 32) && (hdr.ekAPk.length == 32))))) =
      ((hdr.spkId == UInt32.ofNat j.val) &&
       (hdr.pqspkId == UInt32.ofNat j.val) &&
       (hdr.opkId? == some (UInt32.ofNat o.val)) &&
       (hdr.ikAPk.length == 32) &&
       (hdr.ekAPk.length == 32)) := by
    simp only [Bool.and_assoc]
  rw [hhdr_guard]
  by_cases hok :
      ((hdr.spkId == UInt32.ofNat j.val) &&
       (hdr.pqspkId == UInt32.ofNat j.val) &&
       (hdr.opkId? == some (UInt32.ofNat o.val)) &&
       (hdr.ikAPk.length == 32) &&
       (hdr.ekAPk.length == 32)) = true
  · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ite_false, eAny, Comp.eval, v,
      ext_refl_wk, ext_step_wk, Expr.eval, eval_natEqE, eval_nat3EqE, eval_e2ePureOp, E2EPureOp.eval,
      env_get_zero, env_get_succ, hst_eq, stUsedOpk, e2eKeyIndStateToVal,
      List.take_of_length_le hu_len]
    have hused_eq :
        st.usedRecvOPK.any (fun x => x == (k.val, j.val, o.val)) =
        st.usedRecvOPK.contains (k.val, j.val, o.val) := by
      rw [List.contains_eq_any_beq]
      apply List.any_congr rfl
      rintro ⟨a, b, c⟩
      rw [Bool.eq_iff_iff]
      simp only [beq_iff_eq]
      exact eq_comm
    rw [hused_eq]
    by_cases hused : st.usedRecvOPK.contains (k.val, j.val, o.val) = true
    · simp only [hused, ↓reduceIte, ite_true, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
        env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_ite, st_run_pure, map_pure,
        liftP_pure, encKiStepOut, keyIndRenc]
    · simp only [hused, Bool.false_eq_true, ↓reduceIte, ite_false, bindV, Comp.eval]
      rw [eval_koskSenderOkC hP nAdv _ _ _
            (by simp [v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ, hst_eq])
            hst hadv, pure_bind]
      simp only [v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ, hdrIkA, hdrV]
      by_cases hks : koskSenderOk P st.principals st.advKeys hdr.ikAPk = true
      · simp only [hks, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ite_false, caseOptV, eFind,
          mkStepAPqxdhHooks_pureOp, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
          eval_natEqE, eval_e2ePureOp, E2EPureOp.eval, eval_nat2EqE, eval_nat3EqE, env_get_zero,
          env_get_succ, hst_eq, stPrin, stSpk, stOpk, e2eKeyIndStateToVal,
          List.take_of_length_le hp_len, List.take_of_length_le hb_len,
          List.take_of_length_le ho_len]
        rw [principals_find_eq]
        rcases hkfind : st.principals.find? (fun (idx, _) => idx == k.val) with _ | ⟨_, kEntry⟩
        · simp only [hkfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
            env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure,
            encKiStepOut, keyIndRenc]
        · simp only [hkfind, Option.map, Prod.map, id, Comp.eval, v, ext_refl_wk, ext_step_wk,
            Expr.eval, eval_e2ePureOp, E2EPureOp.eval, eval_nat2EqE, env_get_zero, env_get_succ,
            hst_eq, stSpk, e2eKeyIndStateToVal, List.take_of_length_le hb_len]
          rw [spkBundles_find_eq]
          rcases hbfind : st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
              _ | ⟨_, bEntry⟩
          · simp only [hbfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
              env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure,
              encKiStepOut, keyIndRenc]
          · simp only [hbfind, Option.map, Prod.map, id, Comp.eval, v, ext_refl_wk, ext_step_wk,
              Expr.eval, eval_e2ePureOp, E2EPureOp.eval, eval_nat3EqE, env_get_zero, env_get_succ,
              hst_eq, stOpk, e2eKeyIndStateToVal, List.take_of_length_le ho_len]
            rw [opkEntries_find_eq]
            rcases hofind : st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
                _ | ⟨_, oEntry⟩
            · simp only [hofind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
                env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure,
                encKiStepOut, keyIndRenc]
            · simp only [hofind, Option.map, Prod.map, id, Comp.eval, v, ext_refl_wk, ext_step_wk,
                Expr.eval, env_get_zero, env_get_succ, oeCons, e2eOpkEntryToVal]
              by_cases hcons : oEntry.consumed = true
              · simp only [hcons, ↓reduceIte, ite_true, Comp.eval, v, ext_refl_wk, ext_step_wk,
                  Expr.eval, env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_ite,
                  st_run_pure, map_pure, liftP_pure, encKiStepOut, keyIndRenc]
              · simp only [hcons, Bool.false_eq_true, ↓reduceIte, ite_false, letV, Comp.eval,
                  pure_bind]
                rw [eval_checkSeenE _ _ _ _ _ _
                      (by simpa [stSeen, e2eKeyIndStateToVal, v, ext_refl_wk, ext_step_wk,
                        Expr.eval, env_get_zero, env_get_succ, hst_eq] using
                        hst.seenKyberBaseKeys_le),
                  eval_acceptKeysC hP, pure_bind]
                simp only [v, ext_refl_wk, ext_step_wk, Expr.eval, eval_e2ePureOp, E2EPureOp.eval,
                  env_get_zero, env_get_succ, peSec0, e2ePrincipalEntryToVal, beSpkSk, bePqSk,
                  e2eSpkBundleEntryToVal, oeSk, e2eOpkEntryToVal, stSeen, e2eKeyIndStateToVal,
                  hdrPqId, hdrSpkId, hdrEkA, hdrV, hdrOfV_hdrV, hst_eq]
                rw [show hdrOfV (ℓ := ℓ)
                      (hdr.ikAPk, (hdr.ekAPk, (hdr.spkId, (hdr.opkId?, (hdr.pqspkId, hdr.kemCt))))) = hdr
                    by cases hdr; rfl]
                set seenPair := checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys
                  k.val hdr.pqspkId hdr.spkId hdr.ekAPk
                have hacc_eq :
                    acceptKeys P
                      { ikBSk := kEntry.secIKA0, ikBPk := [], spkBSk := bEntry.spkSk, spkBPk := [],
                        opkBSk? := some oEntry.opkSk, pqspkBSk := bEntry.pqspkSk, pqspkBPk := [],
                        trustedPeer := true, replayOk := seenPair.1, hdr := hdr } =
                    acceptKeys P
                      { ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk, spkBSk := bEntry.spkSk,
                        spkBPk := bEntry.spkPk, opkBSk? := some oEntry.opkSk,
                        pqspkBSk := bEntry.pqspkSk, pqspkBPk := bEntry.pqspkPk,
                        trustedPeer := true, replayOk := seenPair.1, hdr := hdr } := rfl
                rw [hacc_eq]
                rcases hacc : acceptKeys P
                    { ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk, spkBSk := bEntry.spkSk,
                      spkBPk := bEntry.spkPk, opkBSk? := some oEntry.opkSk,
                      pqspkBSk := bEntry.pqspkSk, pqspkBPk := bEntry.pqspkPk,
                      trustedPeer := true, replayOk := seenPair.1, hdr := hdr } with _ | dk
                · simp only [hacc, Option.map, caseOptV, Comp.eval, v, ext_refl_wk, ext_step_wk,
                    Expr.eval, env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure,
                    map_pure, liftP_pure, encKiStepOut, keyIndRenc]
                · have hopk_id : hdr.opkId? = some (UInt32.ofNat o.val) := by
                    simp only [Bool.and_eq_true, beq_iff_eq] at hok
                    exact hok.1.1.2
                  obtain ⟨ss, hdec, hdk_eq⟩ := acceptKeys_some_matched hacc
                    (Or.inr ⟨UInt32.ofNat o.val, oEntry.opkSk, hopk_id, rfl⟩)
                  dsimp only [Option.map] at hdec hdk_eq
                  rw [hdec]
                  dsimp only [Option.map]
                  rw [eval_findHonestC hP _ _ _
                        (by simp [stPrin, e2eKeyIndStateToVal, v, ext_refl_wk, ext_step_wk,
                          Expr.eval, env_get_zero, env_get_succ, hst_eq]) hst.principals_le,
                    pure_bind]
                  unfold evalHkdfOrRo
                  simp only [Bool.not_false, ↓reduceIte, ite_true, LawfulMonad.bind_assoc,
                    st_run_lift_bind, st_run_set_bind, pure_bind, ← hdk_eq]
                  rw [st_run_bind]
                  set stUpdated : KeyIndState S :=
                    { st with
                      opkEntries := st.opkEntries.map (fun (idx, e) =>
                        if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true })
                        else (idx, e))
                      usedRecvOPK := (k.val, j.val, o.val) :: st.usedRecvOPK
                      seenKyberBaseKeys := seenPair.2
                      roCache := st.roCache }
                  set rEnt : KeyIndRespEntry S :=
                    { sid := .recvOPK k j o, respIkPk := kEntry.ikAPk, spkPk := bEntry.spkPk,
                      opkPk? := some oEntry.opkPk, pqspkPk := bEntry.pqspkPk, hdr := hdr,
                      senderHonest := (findHonestPrincipal P st.principals hdr.ikAPk).isSome,
                      drKeyReal := dk, drKeyRand := dk }
                  rw [eval_recordRespC hP _ _ _
                    (st := stUpdated)
                    (by
                      simp only [setAcceptOpkE, eLet, eMap, finValE, mkStepAPqxdhHooks_pureOp, v,
                        ext_refl_wk, ext_step_wk, Expr.eval, eval_e2ePureOp, E2EPureOp.eval,
                        eval_nat3EqE, env_get_zero, env_get_succ, hst_eq, stSecb, stPrin, stSpk,
                        stSess, stResp, stUsedOpk, stUsedNoOpk, stRo, stAdv, stOpk,
                        e2eKeyIndStateToVal, List.take_of_length_le ho_len, stUpdated]
                      rw [show (st.opkEntries.map (Prod.map id (e2eOpkEntryToVal (ℓ := ℓ)))).map _ =
                            (st.opkEntries.map (fun (idx, e) =>
                              if idx == (k.val, j.val, o.val) then
                                (idx, { e with consumed := true })
                              else (idx, e))).map (Prod.map id (e2eOpkEntryToVal (ℓ := ℓ))) by
                          rw [List.map_map, List.map_map]
                          apply List.map_congr_left
                          intro ⟨idx, e⟩ _
                          by_cases h : idx = (k.val, j.val, o.val) <;>
                            simp [h, beq_iff_eq, eval_nat3EqE, Prod.map, oeSetConsE, eLet, v,
                              ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ,
                              oeSk, oePk, e2eOpkEntryToVal]])
                    (r := rEnt)
                    (by
                      simp [rEnt, e2eRespEntryToVal, sidV, peIkPk, e2ePrincipalEntryToVal,
                        beSpkPk, bePqPk, e2eSpkBundleEntryToVal, oePk, e2eOpkEntryToVal,
                        hdrIkA, hdrV, eval_isSomeE, v, ext_refl_wk, ext_step_wk, Expr.eval,
                        env_get_zero, env_get_succ])
                    hst.sessions_le]
                  simp only [liftP_bind, liftP_map, fmap_bind, map_bind, map_pure, pure_bind,
                    LawfulMonad.bind_assoc]
                  congr 1; funext ⟨_, stFinal⟩
                  rcases hfh : findHonestPrincipal P st.principals hdr.ikAPk with _ | ⟨_, _⟩ <;>
                    simp only [hdrIkA, hdrV, hfh, Option.map, eCaseOpt, Comp.eval, v, ext_refl_wk,
                      ext_step_wk, Expr.eval, env_get_zero, env_get_succ, rsE, rDrKeyE,
                      rAcceptFreshE, st_run_pure, map_pure, liftP_pure, encKiStepOut, keyIndRenc]
      · simp only [hks, Bool.false_eq_true, Bool.not_false, ↓reduceIte, ite_true, ite_false,
          Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ,
          rsE, rNoneE, hst_eq, st_run_ite, st_run_pure, map_pure, liftP_pure, encKiStepOut,
          keyIndRenc]
  · simp only [hok, Bool.false_eq_true, Bool.not_false, ↓reduceIte, ite_true, ite_false,
      Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ,
      rsE, rNoneE, hst_eq, st_run_ite, st_run_pure, map_pure, liftP_pure, encKiStepOut, keyIndRenc]

set_option linter.unusedSimpArgs false in
theorem eval_acceptNoOpkB (hP : WellFormedPrimitivesδ P) (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (kE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (jE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (lE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_no_opk))
    (hdrE : Expr (e2eOps ℓ P C K decT encT) Γ hdrT) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st)
    (hst : KeyIndSetupBounded S st) (hadv : st.advKeys.length ≤ nAdv) :
    (acceptNoOpkB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv stV kE jE lE hdrE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P
          (.acceptNoOPK (kE.eval ρ) (jE.eval ρ) (lE.eval ρ) (hdrOfV (hdrE.eval ρ)))).run st)) := by
  set hdr := hdrOfV (hdrE.eval ρ)
  have hhdrE : hdrE.eval ρ = hdrV hdr := (hdrV_hdrOfV (hdrE.eval ρ)).symm
  have hu_len : st.usedRecvNoOPK.length ≤ S.N_no_opk_tot := hst.usedRecvNoOPK_le
  have hp_len :
      (st.principals.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ)))).length ≤ S.N_id := by
    simpa using hst.principals_le
  have hb_len :
      (st.spkBundles.map (Prod.map id (e2eSpkBundleEntryToVal (ℓ := ℓ)))).length ≤ S.N_spk_tot := by
    simpa using hst.spkBundles_le
  simp only [acceptNoOpkB, letV, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, eval_natEqE,
    eval_isNoneE, finValE, mkStepAPqxdhHooks_pureOp, eval_e2ePureOp, E2EPureOp.eval,
    env_get_zero, env_get_succ, pure_bind, hst_eq, hhdrE,
    hdrSpkId, hdrPqId, hdrOpkId, hdrIkA, hdrEkA, hdrV]
  set k := kE.eval ρ
  set j := jE.eval ρ
  set l := lE.eval ρ
  unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl
  simp only [LawfulMonad.bind_assoc, st_run_get_bind]
  have hhdr_guard :
      ((hdr.spkId == UInt32.ofNat j.val) &&
       ((hdr.pqspkId == UInt32.ofNat j.val) &&
        (hdr.opkId?.isNone &&
         ((hdr.ikAPk.length == 32) && (hdr.ekAPk.length == 32))))) =
      ((hdr.spkId == UInt32.ofNat j.val) &&
       (hdr.pqspkId == UInt32.ofNat j.val) &&
       (hdr.opkId? == none) &&
       (hdr.ikAPk.length == 32) &&
       (hdr.ekAPk.length == 32)) := by
    cases hdr.opkId? <;> simp [Bool.and_assoc]
  rw [hhdr_guard]
  by_cases hok :
      ((hdr.spkId == UInt32.ofNat j.val) &&
       (hdr.pqspkId == UInt32.ofNat j.val) &&
       (hdr.opkId? == none) &&
       (hdr.ikAPk.length == 32) &&
       (hdr.ekAPk.length == 32)) = true
  · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ite_false, eAny, Comp.eval, v,
      ext_refl_wk, ext_step_wk, Expr.eval, eval_natEqE, eval_nat3EqE, eval_e2ePureOp, E2EPureOp.eval,
      env_get_zero, env_get_succ, hst_eq, stUsedNoOpk, e2eKeyIndStateToVal,
      List.take_of_length_le hu_len]
    have hused_eq :
        st.usedRecvNoOPK.any (fun x => x == (k.val, j.val, l.val)) =
        st.usedRecvNoOPK.contains (k.val, j.val, l.val) := by
      rw [List.contains_eq_any_beq]
      apply List.any_congr rfl
      rintro ⟨a, b, c⟩
      rw [Bool.eq_iff_iff]
      simp only [beq_iff_eq]
      exact eq_comm
    rw [hused_eq]
    by_cases hused : st.usedRecvNoOPK.contains (k.val, j.val, l.val) = true
    · simp only [hused, ↓reduceIte, ite_true, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
        env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_ite, st_run_pure, map_pure,
        liftP_pure, encKiStepOut, keyIndRenc]
    · simp only [hused, Bool.false_eq_true, ↓reduceIte, ite_false, bindV, Comp.eval]
      rw [eval_koskSenderOkC hP nAdv _ _ _
            (by simp [v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ, hst_eq])
            hst hadv, pure_bind]
      simp only [v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ, hdrIkA, hdrV]
      by_cases hks : koskSenderOk P st.principals st.advKeys hdr.ikAPk = true
      · simp only [hks, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ite_false, caseOptV, eFind,
          mkStepAPqxdhHooks_pureOp, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
          eval_natEqE, eval_e2ePureOp, E2EPureOp.eval, eval_nat2EqE, env_get_zero, env_get_succ,
          hst_eq, stPrin, stSpk, e2eKeyIndStateToVal,
          List.take_of_length_le hp_len, List.take_of_length_le hb_len]
        rw [principals_find_eq]
        rcases hkfind : st.principals.find? (fun (idx, _) => idx == k.val) with _ | ⟨_, kEntry⟩
        · simp only [hkfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
            env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure,
            encKiStepOut, keyIndRenc]
        · simp only [hkfind, Option.map, Prod.map, id, Comp.eval, v, ext_refl_wk, ext_step_wk,
            Expr.eval, eval_e2ePureOp, E2EPureOp.eval, eval_nat2EqE, env_get_zero, env_get_succ,
            hst_eq, stSpk, e2eKeyIndStateToVal, List.take_of_length_le hb_len]
          rw [spkBundles_find_eq]
          rcases hbfind : st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
              _ | ⟨_, bEntry⟩
          · simp only [hbfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
              env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure,
              encKiStepOut, keyIndRenc]
          · simp only [hbfind, Option.map, Prod.map, id, letV, Comp.eval, pure_bind]
            rw [eval_checkSeenE _ _ _ _ _ _
                  (by simpa [stSeen, e2eKeyIndStateToVal, v, ext_refl_wk, ext_step_wk,
                    Expr.eval, env_get_zero, env_get_succ, hst_eq] using
                    hst.seenKyberBaseKeys_le),
              eval_acceptKeysC hP, pure_bind]
            simp only [v, ext_refl_wk, ext_step_wk, Expr.eval, eval_e2ePureOp, E2EPureOp.eval,
              env_get_zero, env_get_succ, peSec0, e2ePrincipalEntryToVal, beSpkSk, bePqSk,
              e2eSpkBundleEntryToVal, stSeen, e2eKeyIndStateToVal, hdrPqId, hdrSpkId, hdrEkA,
              hdrV, hdrOfV_hdrV, hst_eq]
            rw [show hdrOfV (ℓ := ℓ)
                  (hdr.ikAPk, (hdr.ekAPk, (hdr.spkId, (hdr.opkId?, (hdr.pqspkId, hdr.kemCt))))) = hdr
                by cases hdr; rfl]
            set seenPair := checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys
              k.val hdr.pqspkId hdr.spkId hdr.ekAPk
            have hacc_eq :
                acceptKeys P
                  { ikBSk := kEntry.secIKA0, ikBPk := [], spkBSk := bEntry.spkSk, spkBPk := [],
                    opkBSk? := none, pqspkBSk := bEntry.pqspkSk, pqspkBPk := [],
                    trustedPeer := true, replayOk := seenPair.1, hdr := hdr } =
                acceptKeys P
                  { ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk, spkBSk := bEntry.spkSk,
                    spkBPk := bEntry.spkPk, opkBSk? := none,
                    pqspkBSk := bEntry.pqspkSk, pqspkBPk := bEntry.pqspkPk,
                    trustedPeer := true, replayOk := seenPair.1, hdr := hdr } := rfl
            rw [hacc_eq]
            rcases hacc : acceptKeys P
                { ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk, spkBSk := bEntry.spkSk,
                  spkBPk := bEntry.spkPk, opkBSk? := none,
                  pqspkBSk := bEntry.pqspkSk, pqspkBPk := bEntry.pqspkPk,
                  trustedPeer := true, replayOk := seenPair.1, hdr := hdr } with _ | dk
            · simp only [hacc, Option.map, caseOptV, Comp.eval, v, ext_refl_wk, ext_step_wk,
                Expr.eval, env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure,
                liftP_pure, encKiStepOut, keyIndRenc]
            · have hopk_id : hdr.opkId? = none := by
                simp only [Bool.and_eq_true, beq_iff_eq] at hok
                exact hok.1.1.2
              obtain ⟨ss, hdec, hdk_eq⟩ := acceptKeys_some_matched hacc (Or.inl ⟨hopk_id, rfl⟩)
              dsimp only [Option.map] at hdec hdk_eq
              rw [hdec]
              dsimp only [Option.map]
              rw [eval_findHonestC hP _ _ _
                    (by simp [stPrin, e2eKeyIndStateToVal, v, ext_refl_wk, ext_step_wk,
                      Expr.eval, env_get_zero, env_get_succ, hst_eq]) hst.principals_le,
                pure_bind]
              unfold evalHkdfOrRo
              simp only [Bool.not_false, ↓reduceIte, ite_true, LawfulMonad.bind_assoc,
                st_run_lift_bind, st_run_set_bind, pure_bind, ← hdk_eq]
              rw [st_run_bind]
              set stUpdated : KeyIndState S :=
                { st with
                  usedRecvNoOPK := (k.val, j.val, l.val) :: st.usedRecvNoOPK
                  seenKyberBaseKeys := seenPair.2
                  roCache := st.roCache }
              set rEnt : KeyIndRespEntry S :=
                { sid := .recvNoOPK k j l, respIkPk := kEntry.ikAPk, spkPk := bEntry.spkPk,
                  opkPk? := none, pqspkPk := bEntry.pqspkPk, hdr := hdr,
                  senderHonest := (findHonestPrincipal P st.principals hdr.ikAPk).isSome,
                  drKeyReal := dk, drKeyRand := dk }
              rw [eval_recordRespC hP _ _ _
                (st := stUpdated)
                (by
                  cases st
                  simp only [setAcceptNoOpkE, eLet, finValE, mkStepAPqxdhHooks_pureOp, v,
                    ext_refl_wk, ext_step_wk, Expr.eval, eval_e2ePureOp, E2EPureOp.eval,
                    env_get_zero, env_get_succ, hst_eq, stSecb, stPrin, stSpk, stOpk, stSess,
                    stResp, stUsedOpk, stUsedNoOpk, stRo, stAdv, e2eKeyIndStateToVal, stUpdated])
                (r := rEnt)
                (by
                  simp [rEnt, e2eRespEntryToVal, sidV, peIkPk, e2ePrincipalEntryToVal,
                    beSpkPk, bePqPk, e2eSpkBundleEntryToVal, hdrIkA, hdrV, eval_isSomeE, v,
                    ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ])
                hst.sessions_le]
              simp only [liftP_bind, liftP_map, fmap_bind, map_bind, map_pure, pure_bind,
                LawfulMonad.bind_assoc]
              congr 1; funext ⟨_, stFinal⟩
              rcases hfh : findHonestPrincipal P st.principals hdr.ikAPk with _ | ⟨_, _⟩ <;>
                simp only [hdrIkA, hdrV, hfh, Option.map, eCaseOpt, Comp.eval, v, ext_refl_wk,
                  ext_step_wk, Expr.eval, env_get_zero, env_get_succ, rsE, rDrKeyE, rAcceptFreshE,
                  st_run_pure, map_pure, liftP_pure, encKiStepOut, keyIndRenc]
      · simp only [hks, Bool.false_eq_true, Bool.not_false, ↓reduceIte, ite_true, ite_false,
          Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ,
          rsE, rNoneE, hst_eq, st_run_ite, st_run_pure, map_pure, liftP_pure, encKiStepOut,
          keyIndRenc]
  · simp only [hok, Bool.false_eq_true, Bool.not_false, ↓reduceIte, ite_true, ite_false,
      Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ,
      rsE, rNoneE, hst_eq, st_run_ite, st_run_pure, map_pure, liftP_pure, encKiStepOut, keyIndRenc]

set_option linter.unusedSimpArgs false in
theorem eval_testB {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st)
    (hst : KeyIndSetupBounded S st) :
    (testB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) stV sidE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P (.testSession (sidOfV (sidE.eval ρ)))).run st)) := by
  set sid := sidOfV (sidE.eval ρ)
  have hsidE : sidE.eval ρ = sidV sid := (sidV_sidOfV (sidE.eval ρ)).symm
  have hs_len :
      (st.sessions.map (e2eInitiatorEntryToVal (ℓ := ℓ))).length ≤ S.N_send_tot := by
    simpa using hst.sessions_le
  have hr_len :
      (st.respSessions.map (e2eRespEntryToVal (ℓ := ℓ))).length ≤ S.N_recv_tot := by
    simpa using hst.respSessions_le
  simp only [testB, letV, Comp.eval, pure_bind, hsidE]
  have htest := eval_isTestableE (S := S) (I₀ := I₀) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (v (Γ := Γ) stV) (v (Γ := sidT S :: Γ) Var.zero)
    (.cons (sidV sid) ρ) (by simp [eval_v_cons, eval_v_refl, hst_eq]) hst
  simp only [Expr.eval, htest, eval_v_refl, env_get_zero, sidOfV_sidV]
  unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl
  simp only [LawfulMonad.bind_assoc, st_run_get_bind]
  by_cases htestable : isKeyIndSessionTestable st sid = true
  · simp only [htestable, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ite_false, caseOptV, eFind,
      eMap, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ, hst_eq,
      stSess, stResp, e2eKeyIndStateToVal,
      List.take_of_length_le hs_len, List.take_of_length_le hr_len]
    have hs_find_eq :
        (st.sessions.map (e2eInitiatorEntryToVal (ℓ := ℓ))).find?
          (fun e => (sidEqE (mkStepAPqxdhHooks ℓ P C K decT encT I₀)
            (ieSid (Expr.var Var.zero))
            (Expr.var Var.zero.succ)).eval (.cons e (.cons (sidV sid) ρ))) =
        (st.sessions.find? (fun e => e.sid == sid)).map (e2eInitiatorEntryToVal (ℓ := ℓ)) := by
      rw [List.find?_map]
      apply congrArg (Option.map _)
      apply List.find?_congr
      intro e _
      dsimp only [Function.comp_def]
      rw [eval_sidEqE]
      simp [ieSid, e2eInitiatorEntryToVal, Expr.eval, env_get_zero, env_get_succ, sidOfV_sidV]
    rw [hs_find_eq]
    rcases hsfind : st.sessions.find? (fun e => e.sid == sid) with _ | e
    · simp only [hsfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
        env_get_zero, env_get_succ, hst_eq, stResp, e2eKeyIndStateToVal,
        List.take_of_length_le hr_len]
      have hr_find_eq :
          (st.respSessions.map (e2eRespEntryToVal (ℓ := ℓ))).find?
            (fun r => (sidEqE (mkStepAPqxdhHooks ℓ P C K decT encT I₀)
              (reSid (Expr.var Var.zero))
              (Expr.var Var.zero.succ)).eval (.cons r (.cons (sidV sid) ρ))) =
          (st.respSessions.find? (fun r => r.sid == sid)).map (e2eRespEntryToVal (ℓ := ℓ)) := by
        rw [List.find?_map]
        apply congrArg (Option.map _)
        apply List.find?_congr
        intro r _
        dsimp only [Function.comp_def]
        rw [eval_sidEqE]
        simp [reSid, e2eRespEntryToVal, Expr.eval, env_get_zero, env_get_succ, sidOfV_sidV]
      rw [hr_find_eq]
      rcases hrfind : st.respSessions.find? (fun r => r.sid == sid) with _ | r
      · simp only [hrfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
          env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure,
          encKiStepOut, keyIndRenc]
      · simp only [hrfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
          env_get_zero, env_get_succ, hst_eq, List.take_of_length_le hr_len,
          LawfulMonad.bind_assoc, st_run_set_bind, st_run_map_set, st_run_pure, map_pure,
          liftP_pure, encKiStepOut, keyIndRenc, rsE, rDrKeyE, setRespE, eLet, stSecb, stPrin,
          stSpk, stOpk, stSess, stResp, stUsedOpk, stUsedNoOpk, stSeen, stRo, stAdv, reReal,
          reRand, e2eKeyIndStateToVal, e2eRespEntryToVal]
        rw [show (st.respSessions.map (e2eRespEntryToVal (ℓ := ℓ))).map _ =
              (st.respSessions.map (fun x =>
                if x.sid == sid then { x with tested := true } else x)).map
                (e2eRespEntryToVal (ℓ := ℓ)) by
            rw [List.map_map, List.map_map]
            apply List.map_congr_left
            intro x _
            dsimp only [Function.comp_def]
            rw [eval_sidEqE]
            simp only [reSid, e2eRespEntryToVal, sidOfV_sidV, v, ext_refl_wk, ext_step_wk,
              Expr.eval, env_get_zero, env_get_succ]
            split_ifs <;> simp [reSetTestedE, eLet, v, ext_refl_wk, ext_step_wk, Expr.eval,
              env_get_zero, env_get_succ, e2eRespEntryToVal, reSid, reReal, reRand, reTested,
              reIk, reSpk, reOpk, rePq, reHdr, reSendHon, reRev]]
        rcases st with ⟨secb, _⟩
        cases secb <;> simp [encKiStepOut, keyIndRenc, e2eKeyIndStateToVal]
    · simp only [hsfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
        env_get_zero, env_get_succ, hst_eq, List.take_of_length_le hs_len,
        LawfulMonad.bind_assoc, st_run_set_bind, st_run_map_set, st_run_pure, map_pure,
        liftP_pure, encKiStepOut, keyIndRenc, rsE, rDrKeyE, setSessE, eLet, stSecb, stPrin,
        stSpk, stOpk, stSess, stResp, stUsedOpk, stUsedNoOpk, stSeen, stRo, stAdv, ieReal,
        ieRand, e2eKeyIndStateToVal, e2eInitiatorEntryToVal]
      rw [show (st.sessions.map (e2eInitiatorEntryToVal (ℓ := ℓ))).map _ =
            (st.sessions.map (fun x =>
              if x.sid == sid then { x with tested := true } else x)).map
              (e2eInitiatorEntryToVal (ℓ := ℓ)) by
          rw [List.map_map, List.map_map]
          apply List.map_congr_left
          intro x _
          dsimp only [Function.comp_def]
          rw [eval_sidEqE]
          simp only [ieSid, e2eInitiatorEntryToVal, sidOfV_sidV, v, ext_refl_wk, ext_step_wk,
            Expr.eval, env_get_zero, env_get_succ]
          split_ifs <;> simp [ieSetTestedE, eLet, v, ext_refl_wk, ext_step_wk, Expr.eval,
            env_get_zero, env_get_succ, e2eInitiatorEntryToVal, ieSid, ieReal, ieRand, ieTested,
            ieHonPeer, iePeerIk, iePeerSpk, iePeerOpk, iePeerPq, ieSpkHon, ieOpkHon, iePqHon,
            ieEkSk, ieFresh, ieHdr, ieRev]]
      rcases st with ⟨secb, _⟩
      cases secb <;> simp [encKiStepOut, keyIndRenc, e2eKeyIndStateToVal]
  · simp only [htestable, Bool.false_eq_true, Bool.not_false, ↓reduceIte, ite_true, ite_false,
      Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ,
      rsE, rNoneE, hst_eq, st_run_ite, st_run_pure, map_pure, liftP_pure, encKiStepOut, keyIndRenc]

set_option linter.unusedSimpArgs false in
theorem eval_ro1KeyRealB (hP : WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (secE : Expr (e2eOps ℓ P C K decT encT) Γ (PB 192)) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st) :
    (ro1KeyRealB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) stV secE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P (.roQuery (secE.eval ρ))).run st)) := by
  have hhk := e2eCryptoOps_eval_hkdfDerive96_lossless ℓ hP C K (secE.eval ρ)
  dsimp only [e2eCryptoOps] at hhk
  unfold pqxdhKeyIndImpl1KeyReal evalHkdfOrRo
  cases st
  simp only [ro1KeyRealB, bindV, mkStepAPqxdhHooks, Comp.eval, v, ext_refl_wk, ext_step_wk,
    Expr.eval, env_get_zero, env_get_succ, eval_e2eCryptoOp, hhk, hst_eq, rsE, rDrKeyE,
    Bool.not_false, ↓reduceIte, ite_true, LawfulMonad.bind_assoc, st_run_get_bind,
    st_run_lift_bind, st_run_set_bind, st_run_map_set, st_run_pure, pure_bind, map_pure,
    liftP_pure, encKiStepOut, keyIndRenc, drKeyV, e2eKeyIndStateToVal]

set_option linter.unusedSimpArgs false in
theorem eval_revealDh1KeyRealB {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S)) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st) :
    (revealDh1KeyRealB (S := S) (O := e2eOps ℓ P C K decT encT)
      (I := stepAIface ℓ I₀) stV).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P .revealDhSecrets).run st)) := by
  unfold pqxdhKeyIndImpl1KeyReal
  simp only [revealDh1KeyRealB, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero,
    env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure, encKiStepOut,
    keyIndRenc]

set_option linter.unusedSimpArgs false in
theorem eval_revealB {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st)
    (hst : KeyIndSetupBounded S st) :
    (revealB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) stV sidE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P (.revealSessionKey (sidOfV (sidE.eval ρ)))).run st)) := by
  set sid := sidOfV (sidE.eval ρ)
  have hsidE : sidE.eval ρ = sidV sid := (sidV_sidOfV (sidE.eval ρ)).symm
  have hs_len :
      (st.sessions.map (e2eInitiatorEntryToVal (ℓ := ℓ))).length ≤ S.N_send_tot := by
    simpa using hst.sessions_le
  have hr_len :
      (st.respSessions.map (e2eRespEntryToVal (ℓ := ℓ))).length ≤ S.N_recv_tot := by
    simpa using hst.respSessions_le
  simp only [revealB, letV, caseOptV, eFind, eMap, Comp.eval, v, ext_refl_wk, ext_step_wk,
    Expr.eval, env_get_zero, env_get_succ, pure_bind, hst_eq, hsidE, stSess, stResp,
    e2eKeyIndStateToVal, List.take_of_length_le hs_len, List.take_of_length_le hr_len]
  have hs_find_eq :
      (st.sessions.map (e2eInitiatorEntryToVal (ℓ := ℓ))).find?
        (fun e => (sidEqE (mkStepAPqxdhHooks ℓ P C K decT encT I₀)
          (ieSid (Expr.var Var.zero))
          (Expr.var Var.zero.succ)).eval (.cons e (.cons (sidV sid) ρ))) =
      (st.sessions.find? (fun e => e.sid == sid)).map (e2eInitiatorEntryToVal (ℓ := ℓ)) := by
    rw [List.find?_map]
    apply congrArg (Option.map _)
    apply List.find?_congr
    intro e _
    dsimp only [Function.comp_def]
    rw [eval_sidEqE]
    simp [ieSid, e2eInitiatorEntryToVal, Expr.eval, env_get_zero, env_get_succ, sidOfV_sidV]
  rw [hs_find_eq]
  unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl
  simp only [LawfulMonad.bind_assoc, st_run_get_bind]
  rcases hsfind : st.sessions.find? (fun e => e.sid == sid) with _ | e
  · simp only [hsfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
      env_get_zero, env_get_succ, hst_eq, stResp, e2eKeyIndStateToVal,
      List.take_of_length_le hr_len]
    have hr_find_eq :
        (st.respSessions.map (e2eRespEntryToVal (ℓ := ℓ))).find?
          (fun r => (sidEqE (mkStepAPqxdhHooks ℓ P C K decT encT I₀)
            (reSid (Expr.var Var.zero))
            (Expr.var Var.zero.succ)).eval (.cons r (.cons (sidV sid) ρ))) =
        (st.respSessions.find? (fun r => r.sid == sid)).map (e2eRespEntryToVal (ℓ := ℓ)) := by
      rw [List.find?_map]
      apply congrArg (Option.map _)
      apply List.find?_congr
      intro r _
      dsimp only [Function.comp_def]
      rw [eval_sidEqE]
      simp [reSid, e2eRespEntryToVal, Expr.eval, env_get_zero, env_get_succ, sidOfV_sidV]
    rw [hr_find_eq]
    rcases hrfind : st.respSessions.find? (fun r => r.sid == sid) with _ | r
    · simp only [hrfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
        env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure,
        encKiStepOut, keyIndRenc]
    · simp only [hrfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
        env_get_zero, env_get_succ, reTested, e2eRespEntryToVal]
      by_cases hrtest : r.tested = true
      · simp only [hrtest, ↓reduceIte, ite_true, Comp.eval, v, ext_refl_wk, ext_step_wk,
          Expr.eval, env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_ite, st_run_pure,
          map_pure, liftP_pure, encKiStepOut, keyIndRenc]
      · simp only [hrtest, Bool.false_eq_true, ↓reduceIte, ite_false, Comp.eval, v, ext_refl_wk,
          ext_step_wk, Expr.eval, env_get_zero, env_get_succ, hst_eq,
          List.take_of_length_le hr_len, st_run_ite, LawfulMonad.bind_assoc,
          st_run_set_bind, st_run_map_set, st_run_pure, map_pure, liftP_pure, encKiStepOut,
          keyIndRenc, rsE, rDrKeyE, setRespE, eLet, stSecb, stPrin, stSpk, stOpk, stSess, stResp,
          stUsedOpk, stUsedNoOpk, stSeen, stRo, stAdv, reReal, e2eKeyIndStateToVal,
          e2eRespEntryToVal]
        rw [show (st.respSessions.map (e2eRespEntryToVal (ℓ := ℓ))).map _ =
              (st.respSessions.map (fun x =>
                if x.sid == sid then { x with revealed := true } else x)).map
                (e2eRespEntryToVal (ℓ := ℓ)) by
            rw [List.map_map, List.map_map]
            apply List.map_congr_left
            intro x _
            dsimp only [Function.comp_def]
            rw [eval_sidEqE]
            simp only [reSid, e2eRespEntryToVal, sidOfV_sidV, v, ext_refl_wk, ext_step_wk,
              Expr.eval, env_get_zero, env_get_succ]
            split_ifs <;> simp [reSetRevE, eLet, v, ext_refl_wk, ext_step_wk, Expr.eval,
              env_get_zero, env_get_succ, e2eRespEntryToVal, reSid, reReal, reRand, reTested,
              reIk, reSpk, reOpk, rePq, reHdr, reSendHon, reRev]]
  · simp only [hsfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
      env_get_zero, env_get_succ, ieTested, e2eInitiatorEntryToVal]
    by_cases hstest : e.tested = true
    · simp only [hstest, ↓reduceIte, ite_true, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
        env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_ite, st_run_pure, map_pure,
        liftP_pure, encKiStepOut, keyIndRenc]
    · simp only [hstest, Bool.false_eq_true, ↓reduceIte, ite_false, Comp.eval, v, ext_refl_wk,
        ext_step_wk, Expr.eval, env_get_zero, env_get_succ, hst_eq,
        List.take_of_length_le hs_len, st_run_ite, LawfulMonad.bind_assoc,
        st_run_set_bind, st_run_map_set, st_run_pure, map_pure, liftP_pure, encKiStepOut,
        keyIndRenc, rsE, rDrKeyE, setSessE, eLet, stSecb, stPrin, stSpk, stOpk, stSess, stResp,
        stUsedOpk, stUsedNoOpk, stSeen, stRo, stAdv, ieReal, e2eKeyIndStateToVal,
        e2eInitiatorEntryToVal]
      rw [show (st.sessions.map (e2eInitiatorEntryToVal (ℓ := ℓ))).map _ =
            (st.sessions.map (fun x =>
              if x.sid == sid then { x with revealed := true } else x)).map
              (e2eInitiatorEntryToVal (ℓ := ℓ)) by
          rw [List.map_map, List.map_map]
          apply List.map_congr_left
          intro x _
          dsimp only [Function.comp_def]
          rw [eval_sidEqE]
          simp only [ieSid, e2eInitiatorEntryToVal, sidOfV_sidV, v, ext_refl_wk, ext_step_wk,
            Expr.eval, env_get_zero, env_get_succ]
          split_ifs <;> simp [ieSetRevE, eLet, v, ext_refl_wk, ext_step_wk, Expr.eval,
            env_get_zero, env_get_succ, e2eInitiatorEntryToVal, ieSid, ieReal, ieRand, ieTested,
            ieHonPeer, iePeerIk, iePeerSpk, iePeerOpk, iePeerPq, ieSpkHon, ieOpkHon, iePqHon,
            ieEkSk, ieFresh, ieHdr, ieRev]]

set_option linter.unusedSimpArgs false in
theorem eval_registerB (hP : WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (skE : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st) :
    (registerB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) stV skE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P (.registerKey (skE.eval ρ))).run st)) := by
  simp only [registerB, letV, bindV, mkStepAPqxdhHooks, Comp.eval, v, ext_refl_wk, ext_step_wk,
    Expr.eval, eval_natEqE, env_get_zero, env_get_succ, eval_e2ePureOp, E2EPureOp.eval, pure_bind]
  set sk := skE.eval ρ
  unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl registerAdvKey
  simp only [LawfulMonad.bind_assoc, st_run_get_bind]
  by_cases hlen : sk.length = 32
  · have hxb := e2eCryptoOps_eval_x25519Base_lossless ℓ hP C K sk
    dsimp only [e2eCryptoOps] at hxb
    cases st
    simp only [hlen, beq_self_eq_true, bne_self_eq_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, ite_false, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero,
      env_get_succ, eval_e2eCryptoOp, hxb, hst_eq, rsE, rPkE, setAdvE, eLet, st_run_ite,
      LawfulMonad.bind_assoc, st_run_set_bind, st_run_map_set, st_run_pure, pure_bind, map_pure,
      liftP_pure, encKiStepOut, keyIndRenc, e2eKeyIndStateToVal, stSecb, stPrin, stSpk, stOpk,
      stSess, stResp, stUsedOpk, stUsedNoOpk, stSeen, stRo, stAdv]
  · have hbeq : (sk.length == 32) = false := beq_eq_false_iff_ne.mpr hlen
    have hbne : (sk.length != 32) = true := bne_iff_ne.mpr hlen
    simp only [hbeq, hbne, Bool.not_false, ↓reduceIte, ite_true, Comp.eval, v, ext_refl_wk,
      ext_step_wk, Expr.eval, env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_ite,
      st_run_pure, map_pure, liftP_pure, encKiStepOut, keyIndRenc]

set_option linter.unusedSimpArgs false in
theorem eval_revealSpkB {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (uE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (jE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv)) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st)
    (hst : KeyIndSetupBounded S st) :
    (revealSpkB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) stV uE jE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P (.revealSpkSk (uE.eval ρ) (jE.eval ρ))).run st)) := by
  have hb_len :
      (st.spkBundles.map (Prod.map id (e2eSpkBundleEntryToVal (ℓ := ℓ)))).length ≤ S.N_spk_tot := by
    simpa using hst.spkBundles_le
  simp only [revealSpkB, letV, caseOptV, eFind, eMap, finValE, mkStepAPqxdhHooks, Comp.eval,
    v, ext_refl_wk, ext_step_wk, Expr.eval, eval_e2ePureOp, E2EPureOp.eval, eval_nat2EqE,
    env_get_zero, env_get_succ, pure_bind, hst_eq, stSpk, e2eKeyIndStateToVal,
    List.take_of_length_le hb_len]
  set u := uE.eval ρ
  set j := jE.eval ρ
  rw [spkBundles_find_eq]
  unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl
  simp only [LawfulMonad.bind_assoc, st_run_get_bind]
  rcases hbfind : st.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with _ | ⟨_, bEntry⟩
  · simp only [hbfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
      env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure,
      encKiStepOut, keyIndRenc]
  · simp only [hbfind, Option.map, Prod.map, id, Comp.eval, v, ext_refl_wk, ext_step_wk,
      Expr.eval, env_get_zero, env_get_succ, hst_eq, List.take_of_length_le hb_len,
      LawfulMonad.bind_assoc, st_run_set_bind, st_run_map_set, st_run_pure, map_pure, liftP_pure,
      encKiStepOut, keyIndRenc, rsE, rSpkSkE, setSpkE, eLet, stSecb, stPrin, stSpk, stOpk,
      stSess, stResp, stUsedOpk, stUsedNoOpk, stSeen, stRo, stAdv, beSpkSk,
      e2eKeyIndStateToVal, e2eSpkBundleEntryToVal]
    rw [show (st.spkBundles.map (Prod.map id (e2eSpkBundleEntryToVal (ℓ := ℓ)))).map _ =
          (st.spkBundles.map (fun (idx, b) =>
            if idx == (u.val, j.val) then (idx, { b with revealed := true }) else (idx, b))).map
            (Prod.map id (e2eSpkBundleEntryToVal (ℓ := ℓ))) by
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro ⟨idx, b⟩ _
        by_cases h : idx = (u.val, j.val) <;>
          simp [h, beq_iff_eq, Prod.map, beSetRevE, eLet, v, ext_refl_wk, ext_step_wk, Expr.eval,
            env_get_zero, env_get_succ, beSpkSk, beSpkPk, bePqSk, bePqPk, beSpkSig, bePqSig,
            e2eSpkBundleEntryToVal]]

set_option linter.unusedSimpArgs false in
theorem eval_initPrin1KeyBFuel (hP : WellFormedPrimitivesδ P) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (uE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id)) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st)
    (hst : stListBounded S nFuel st) :
    (initPrin1KeyBFuel (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel stV uE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P (.initPrin (uE.eval ρ))).run st)) := by
  have hp_len :
      (st.principals.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ)))).length ≤
        min nFuel S.N_id := by
    simpa using hst.principals_le
  simp only [initPrin1KeyBFuel, letV, bindV, eAny, finValE, mkStepAPqxdhHooks, Comp.eval, v,
    ext_refl_wk, ext_step_wk, Expr.eval, eval_natEqE, eval_e2ePureOp, E2EPureOp.eval, env_get_zero,
    env_get_succ, pure_bind, hst_eq, stPrin, e2eKeyIndStateToVal, List.take_of_length_le hp_len]
  set u := uE.eval ρ
  rw [principals_any_eq]
  unfold pqxdhKeyIndImpl1KeyReal sampleScalar32
  simp only [LawfulMonad.bind_assoc, st_run_get_bind, st_run_ite]
  split_ifs with hdup
  · simp only [Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ,
      rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure, encKiStepOut, keyIndRenc]
  · simp only [Comp.eval, eval_sBytes32C, v, ext_refl_wk, ext_step_wk, Expr.eval,
      eval_e2eCryptoOp, env_get_zero, env_get_succ,
      LawfulMonad.bind_assoc, st_run_lift_bind, st_run_set_bind, st_run_map_set, st_run_pure,
      map_bind, map_pure, pure_bind, liftP_bind, liftP_pure]
    congr 1
    funext sec
    have hxb := e2eCryptoOps_eval_x25519Base_lossless ℓ hP C K sec
    dsimp only [e2eCryptoOps] at hxb
    rw [hxb]
    cases st
    simp only [v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ, rsE, rInitPrinE,
      setPrinE, eLet, hst_eq, encKiStepOut, keyIndRenc, e2eKeyIndStateToVal,
      e2ePrincipalEntryToVal, stSecb, stPrin, List.map_cons, Prod.map, id]

set_option linter.unusedSimpArgs false in
theorem eval_corruptBFuel (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (uE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id)) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st)
    (hst : stListBounded S nFuel st) :
    (corruptBFuel (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel stV uE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P (.corruptIK (uE.eval ρ))).run st)) := by
  have hp_len :
      (st.principals.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ)))).length ≤
        min nFuel S.N_id := by
    simpa using hst.principals_le
  simp only [corruptBFuel, letV, caseOptV, eFind, eMap, finValE, mkStepAPqxdhHooks, Comp.eval,
    v, ext_refl_wk, ext_step_wk, Expr.eval, eval_natEqE, eval_e2ePureOp, E2EPureOp.eval,
    env_get_zero, env_get_succ, pure_bind, hst_eq, stPrin, e2eKeyIndStateToVal,
    List.take_of_length_le hp_len]
  set u := uE.eval ρ
  rw [principals_find_eq]
  unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl
  simp only [LawfulMonad.bind_assoc, st_run_get_bind]
  rcases hfind : st.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨_, entry⟩
  · simp only [hfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero,
      env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure, encKiStepOut,
      keyIndRenc]
  · simp only [hfind, Option.map, Prod.map, id, Comp.eval, v, ext_refl_wk, ext_step_wk,
      Expr.eval, env_get_zero, env_get_succ, hst_eq, List.take_of_length_le hp_len,
      LawfulMonad.bind_assoc, st_run_set_bind, st_run_map_set, st_run_pure, map_pure,
      liftP_pure, encKiStepOut, keyIndRenc, rsE, rCorrE, setPrinE, eLet, stSecb, stPrin, stSpk,
      stOpk, stSess, stResp, stUsedOpk, stUsedNoOpk, stSeen, stRo, stAdv, peSec0, peSecSign,
      e2eKeyIndStateToVal, e2ePrincipalEntryToVal]
    rw [show (st.principals.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ)))).map _ =
          (st.principals.map (fun (idx, e) =>
            if idx == u.val then (idx, { e with corrupted := true }) else (idx, e))).map
            (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ))) by
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro ⟨idx, e⟩ _
        by_cases h : idx = u.val <;>
          simp [h, beq_iff_eq, eval_natEqE, Prod.map, peSetCorrE, eLet, v, ext_refl_wk,
            ext_step_wk, Expr.eval, env_get_zero, env_get_succ, peSec0, peIkPk, peSecSign,
            peSignPk, e2ePrincipalEntryToVal]]

set_option linter.unusedSimpArgs false in
theorem eval_genSpkBFuel (hP : WellFormedPrimitivesδ P) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (uE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (jE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv)) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st)
    (hst : stListBounded S nFuel st) :
    (genSpkBFuel (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel stV uE jE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P (.genSPK (uE.eval ρ) (jE.eval ρ))).run st)) := by
  have hp_len :
      (st.principals.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ)))).length ≤
        min nFuel S.N_id := by
    simpa using hst.principals_le
  have hs_len :
      (st.spkBundles.map (Prod.map id (e2eSpkBundleEntryToVal (ℓ := ℓ)))).length ≤
        min nFuel S.N_spk_tot := by
    simpa using hst.spkBundles_le
  simp only [genSpkBFuel, letV, caseOptV, bindV, eAny, eFind, finValE, mkStepAPqxdhHooks, Comp.eval,
    v, ext_refl_wk, ext_step_wk, Expr.eval, eval_natEqE, eval_e2ePureOp, E2EPureOp.eval,
    eval_nat2EqE, env_get_zero, env_get_succ, pure_bind, hst_eq, stSpk, stPrin,
    e2eKeyIndStateToVal, List.take_of_length_le hs_len, List.take_of_length_le hp_len]
  set u := uE.eval ρ
  set j := jE.eval ρ
  rw [spkBundles_any_eq, principals_find_eq]
  unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl sampleScalar32
  simp only [LawfulMonad.bind_assoc, st_run_get_bind, st_run_ite]
  split_ifs with hdup
  · simp only [Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ,
      rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure, encKiStepOut, keyIndRenc]
  · rcases hfind : st.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨_, uEntry⟩
    · simp only [hfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
        env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure,
        encKiStepOut, keyIndRenc]
    · simp only [hfind, Option.map, Prod.map, id, Comp.eval, eval_sBytes32C, eval_sRandom64C,
        eval_sKemKeyGenC hP, v, ext_refl_wk, ext_step_wk, Expr.eval, eval_e2eCryptoOp,
        eval_encECWideE, eval_encKEME, env_get_zero, env_get_succ, peSecSign,
        e2ePrincipalEntryToVal,
        LawfulMonad.bind_assoc, st_run_lift_bind, st_run_set_bind, st_run_map_set, st_run_pure,
        map_bind, map_pure, pure_bind, liftP_bind, liftP_pure]
      congr 1; funext spkSk
      have hxb := e2eCryptoOps_eval_x25519Base_lossless ℓ hP C K spkSk
      dsimp only [e2eCryptoOps] at hxb
      rw [hxb]
      congr 1; funext rSpk
      have hsig1 := e2eCryptoOps_eval_sigSign_lossless ℓ hP C K uEntry.secIKAsign
        (encodeEC (P.x25519Base spkSk)) rSpk
      dsimp only [e2eCryptoOps] at hsig1
      rw [hsig1]
      congr 1; funext ⟨pqPk, pqSk⟩
      congr 1; funext rPq
      have hsig2 := e2eCryptoOps_eval_sigSign_lossless ℓ hP C K uEntry.secIKAsign
        (encodeKEM pqPk) rPq
      dsimp only [e2eCryptoOps] at hsig2
      rw [hsig2]
      cases st
      simp only [v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ,
        eval_e2ePureOp, E2EPureOp.eval, rsE, rBundleE, setSpkE, eLet, hst_eq, encKiStepOut,
        keyIndRenc, bundleV, peIkPk, e2eKeyIndStateToVal, e2ePrincipalEntryToVal,
        e2eSpkBundleEntryToVal, stSecb, stPrin, stSpk, List.map_cons, Prod.map, id]

set_option linter.unusedSimpArgs false in
theorem eval_genOpkBFuel (hP : WellFormedPrimitivesδ P) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (uE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (jE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (oE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_opk)) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st)
    (hst : stListBounded S nFuel st) :
    (genOpkBFuel (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel stV uE jE oE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P (.genOPK (uE.eval ρ) (jE.eval ρ) (oE.eval ρ))).run st)) := by
  have ho_len :
      (st.opkEntries.map (Prod.map id (e2eOpkEntryToVal (ℓ := ℓ)))).length ≤
        min nFuel S.N_opk_tot := by
    simpa using hst.opkEntries_le
  simp only [genOpkBFuel, letV, bindV, eAny, finValE, mkStepAPqxdhHooks, Comp.eval, v,
    ext_refl_wk, ext_step_wk, Expr.eval, eval_e2ePureOp, E2EPureOp.eval, eval_nat3EqE,
    env_get_zero, env_get_succ, pure_bind, hst_eq, stOpk, e2eKeyIndStateToVal,
    List.take_of_length_le ho_len]
  set u := uE.eval ρ
  set j := jE.eval ρ
  set o := oE.eval ρ
  rw [opkEntries_any_eq]
  unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl sampleScalar32
  simp only [LawfulMonad.bind_assoc, st_run_get_bind, st_run_ite]
  split_ifs with hdup
  · simp only [Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ,
      rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure, encKiStepOut, keyIndRenc]
  · simp only [Comp.eval, eval_sBytes32C, v, ext_refl_wk, ext_step_wk, Expr.eval,
      eval_e2eCryptoOp, env_get_zero, env_get_succ,
      LawfulMonad.bind_assoc, st_run_lift_bind, st_run_set_bind, st_run_map_set, st_run_pure,
      map_bind, map_pure, pure_bind, liftP_bind, liftP_pure]
    congr 1; funext opkSk
    have hxb := e2eCryptoOps_eval_x25519Base_lossless ℓ hP C K opkSk
    dsimp only [e2eCryptoOps] at hxb
    rw [hxb]
    cases st
    simp only [v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ, rsE, rPkE,
      setOpkE, eLet, hst_eq, encKiStepOut, keyIndRenc, e2eKeyIndStateToVal, e2eOpkEntryToVal,
      stSecb, stPrin, stSpk, stOpk, List.map_cons, Prod.map, id]

set_option linter.unusedSimpArgs false in
theorem eval_initiateCFuel (hP : WellFormedPrimitivesδ P) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (uE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (bndE : Expr (e2eOps ℓ P C K decT encT) Γ bundleT) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st)
    (hst : stListBounded S nFuel st) :
    (initiateCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel stV sidE uE bndE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((runKeyIndInitiate false S P (sidOfV (sidE.eval ρ)) (uE.eval ρ)
          (bundleOfV (bndE.eval ρ))).run st)) := by
  set sid := sidOfV (sidE.eval ρ)
  have hsidE : sidE.eval ρ = sidV sid := (sidV_sidOfV (sidE.eval ρ)).symm
  set bnd := bundleOfV (bndE.eval ρ)
  have hbndE : bndE.eval ρ = bundleV bnd := (bundleV_bundleOfV (bndE.eval ρ)).symm
  set u := uE.eval ρ
  have hs_len :
      (st.sessions.map (e2eInitiatorEntryToVal (ℓ := ℓ))).length ≤ min nFuel S.N_send_tot := by
    simpa using hst.sessions_le
  have hp_len :
      (st.principals.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ)))).length ≤
        min nFuel S.N_id := by
    simpa using hst.principals_le
  unfold initiateCFuel
  rw [eval_letV_eq (val := (sidV sid, (u.val, bundleV bnd))) (by
        simp [finValE, Expr.eval, eval_e2ePureOp, E2EPureOp.eval, hsidE, hbndE, u]),
    eval_iteC_eq (b := st.sessions.any (fun e => e.sid == sid)) (by
      simp only [eAny, Expr.eval, eval_v_cons, eval_v_refl, env_get_zero, hst_eq, stSess,
        e2eKeyIndStateToVal, List.take_of_length_le hs_len, List.any_map]
      apply List.any_congr rfl; intro e; dsimp only [Function.comp_def]
      rw [eval_sidEqE]
      simp [ieSid, e2eInitiatorEntryToVal, sidOfV_sidV, Expr.eval, eval_v_cons, eval_v_refl,
        env_get_zero])]
  unfold runKeyIndInitiate sampleScalar32 sampleCoins32
  simp only [LawfulMonad.bind_assoc, st_run_get_bind, st_run_ite]
  by_cases hdup : st.sessions.any (fun e => e.sid == sid) = true
  · simp only [hdup, ↓reduceIte, ite_true]
    exact eval_ret_rNoneE stV _ st (by simp [hst_eq])
  · simp only [hdup, Bool.false_eq_true, ↓reduceIte, ite_false]
    rw [eval_caseOptV_eq
      (v? := (st.principals.find? (fun (idx, _) => idx == u.val)).map
        (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ)))) (by
      simp only [eFind, Expr.eval, eval_natEqE, eval_v_cons, eval_v_refl, env_get_zero, hst_eq,
        stPrin, e2eKeyIndStateToVal, List.take_of_length_le hp_len]
      exact principals_find_eq st.principals u.val)]
    rcases hfind : st.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨uIdx, uEntry⟩
    · simp only [hfind, Option.map]
      exact eval_ret_rNoneE stV _ st (by simp [hst_eq])
    · simp only [hfind, Option.map, Prod.map, id]
      rw [eval_bindV_eq (m := pure (koskBundleOk P st.principals st.spkBundles st.opkEntries
            st.advKeys bnd)) (by
            rw [eval_koskBundleOkCFuel hP nFuel _ _ _ (by simp [hst_eq]) hst]
            simp [Expr.eval, bundleOfV_bundleV]),
        pure_bind,
        eval_iteC_eq (b := !koskBundleOk P st.principals st.spkBundles st.opkEntries
            st.advKeys bnd) (by simp [Expr.eval]),
        st_run_ite]
      by_cases hkosk : koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bnd = true
      · simp only [hkosk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ite_false]
        rw [eval_bindV_eq (τ := PB 32)
              (m := (stepAIface ℓ I₀).liftP sampleBytes32) (eval_sBytes32C _)]
        simp only [LawfulMonad.bind_assoc, st_run_lift_bind, map_bind, liftP_bind]
        congr 1; funext ekASk
        rw [eval_bindV_eq (τ := PB 32)
              (m := (stepAIface ℓ I₀).liftP sampleBytes32) (eval_sBytes32C _)]
        congr 1; funext kemCoins
        rw [eval_bindV_eq (m := pure (resolveSigPk P st.principals bnd.ikB)) (by
              rw [eval_resolveSigPkCFuel hP nFuel _ _ _
                (by simp [stPrin, Expr.eval, e2eKeyIndStateToVal, hst_eq]) hst.principals_le]
              simp [Expr.eval, bndIkB, bundleV]),
          pure_bind,
          eval_bindV_eq (m := pure (P.sigVerify (resolveSigPk P st.principals bnd.ikB)
              (encodeEC bnd.spkB) bnd.spkSig)) (by
            simp [mkStepAPqxdhHooks_callPrim, eval_retC, Expr.eval, eval_e2eCryptoOp,
              eval_encECWideE, bndSpkB, bndSpkSig, bundleV]
            rfl),
          pure_bind,
          eval_bindV_eq (m := pure (P.sigVerify (resolveSigPk P st.principals bnd.ikB)
              (encodeKEM bnd.pqspkB) bnd.pqspkSig)) (by
            simp [mkStepAPqxdhHooks_callPrim, eval_retC, Expr.eval, eval_e2eCryptoOp,
              eval_encKEME, bndPqB, bndPqSig, bundleV]
            rfl),
          pure_bind,
          eval_iteC_eq (b := !(P.sigVerify (resolveSigPk P st.principals bnd.ikB)
              (encodeEC bnd.spkB) bnd.spkSig &&
            P.sigVerify (resolveSigPk P st.principals bnd.ikB)
              (encodeKEM bnd.pqspkB) bnd.pqspkSig)) (by simp [Expr.eval]),
          st_run_ite]
        by_cases hsig :
            (P.sigVerify (resolveSigPk P st.principals bnd.ikB) (encodeEC bnd.spkB) bnd.spkSig &&
             P.sigVerify (resolveSigPk P st.principals bnd.ikB) (encodeKEM bnd.pqspkB) bnd.pqspkSig) = true
        · simp only [hsig, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ite_false]
          have henc := e2eCryptoOps_eval_kemEncaps_lossless ℓ hP C K bnd.pqspkB kemCoins
          dsimp only [e2eCryptoOps] at henc
          rw [eval_bindV_eq (m := pure (P.kemEncaps bnd.pqspkB kemCoins)) (by
                simp [mkStepAPqxdhHooks_callPrim, eval_retC, Expr.eval, eval_e2eCryptoOp,
                  bndPqB, bundleV, henc]),
            pure_bind,
            eval_caseOptV_eq (v? := P.kemEncaps bnd.pqspkB kemCoins) (by simp)]
          rcases hkem : P.kemEncaps bnd.pqspkB kemCoins with _ | ⟨ss, kemCt⟩
          · simp only [hkem]
            exact eval_ret_rNoneE stV _ st (by simp [hst_eq])
          · simp only [hkem]
            have hxb := e2eCryptoOps_eval_x25519Base_lossless ℓ hP C K ekASk
            have hdh1 := e2eCryptoOps_eval_x25519_lossless ℓ hP C K uEntry.secIKA0 bnd.spkB
            have hdh2 := e2eCryptoOps_eval_x25519_lossless ℓ hP C K ekASk bnd.ikB
            have hdh3 := e2eCryptoOps_eval_x25519_lossless ℓ hP C K ekASk bnd.spkB
            dsimp only [e2eCryptoOps] at hxb hdh1 hdh2 hdh3
            rw [eval_bindV_eq (m := pure (P.x25519Base ekASk)) (by
                  simp [mkStepAPqxdhHooks_callPrim, eval_retC, Expr.eval, eval_e2eCryptoOp, hxb]),
              pure_bind,
              eval_bindV_eq (m := pure (P.x25519 uEntry.secIKA0 bnd.spkB)) (by
                simp [mkStepAPqxdhHooks_callPrim, eval_retC, Expr.eval, eval_e2eCryptoOp,
                  peSec0, e2ePrincipalEntryToVal, bndSpkB, bundleV, hdh1]),
              pure_bind,
              eval_bindV_eq (m := pure (P.x25519 ekASk bnd.ikB)) (by
                simp [mkStepAPqxdhHooks_callPrim, eval_retC, Expr.eval, eval_e2eCryptoOp,
                  bndIkB, bundleV, hdh2]),
              pure_bind,
              eval_bindV_eq (m := pure (P.x25519 ekASk bnd.spkB)) (by
                simp [mkStepAPqxdhHooks_callPrim, eval_retC, Expr.eval, eval_e2eCryptoOp,
                  bndSpkB, bundleV, hdh3]),
              pure_bind,
              eval_bindV_eq (m := pure (bnd.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk))) (by
                rw [eval_caseOptV_eq (v? := bnd.opkB?)
                  (by simp [Expr.eval, bndOpkB, bundleV])]
                rcases bnd.opkB? with _ | ⟨oid, opkPk⟩
                · simp [eval_retC, Expr.eval]
                · have hdh4 := e2eCryptoOps_eval_x25519_lossless ℓ hP C K ekASk opkPk
                  dsimp only [e2eCryptoOps] at hdh4
                  simp [eval_bindV, mkStepAPqxdhHooks_callPrim, eval_retC, Expr.eval,
                    eval_e2eCryptoOp, hdh4, pure_bind]),
              pure_bind]
            set secrets := buildSecrets (P.x25519 uEntry.secIKA0 bnd.spkB)
              (P.x25519 ekASk bnd.ikB) (P.x25519 ekASk bnd.spkB)
              (bnd.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)) ss
            have hhk := e2eCryptoOps_eval_hkdfDerive96_lossless ℓ hP C K secrets
            dsimp only [e2eCryptoOps] at hhk
            set drKeyReal := P.hkdfDerive96 secrets
            set hdr : HandshakeHdr :=
              { ikAPk := uEntry.ikAPk, ekAPk := P.x25519Base ekASk, spkId := bnd.spkId,
                opkId? := bnd.opkB?.map Prod.fst, pqspkId := bnd.pqspkId, kemCt := kemCt }
            set honestPeer := isHonestUncorruptedPeer P st.principals bnd.ikB
            set prov := checkBundleProvenance P st.principals st.spkBundles st.opkEntries bnd
            set sessEntry : KeyIndInitiatorEntry S :=
              { sid := sid, honestPeer := honestPeer, peerIkPk := bnd.ikB,
                peerSpkPk := bnd.spkB, peerOpkPk? := bnd.opkB?.map Prod.snd,
                peerPqspkPk := bnd.pqspkB, spkHonest := prov.1, opkHonest := prov.2.1,
                pqspkHonest := prov.2.2, ekASk := ekASk, fresh := honestPeer.isSome,
                drKeyReal := drKeyReal, drKeyRand := drKeyReal, hdr := hdr, tested := false }
            rw [eval_bindV_eq (m := pure (drKeyV drKeyReal)) (by
                  simp [mkStepAPqxdhHooks_callPrim, eval_retC, Expr.eval, eval_e2eCryptoOp,
                    eval_buildSecretsE, hhk, secrets, drKeyReal, drKeyV]),
              pure_bind,
              eval_bindV_eq (m := pure honestPeer) (by
                rw [eval_honestPeerCFuel hP nFuel _ _ _
                  (by simp [stPrin, Expr.eval, e2eKeyIndStateToVal, hst_eq]) hst.principals_le]
                simp [Expr.eval, bndIkB, bundleV, honestPeer]),
              pure_bind,
              eval_bindV_eq (m := pure prov) (by
                rw [eval_checkProvCFuel hP nFuel _ _ _ (by simp [hst_eq]) hst]
                simp [Expr.eval, bundleOfV_bundleV, prov]),
              pure_bind,
              eval_letV_eq (val := hdrV hdr) (by
                simp [Expr.eval, peIkPk, e2ePrincipalEntryToVal, bndSpkId, bndOpkB, bndPqId,
                  bundleV, eval_optMapE, hdr, hdrV]),
              eval_letV_eq (val := e2eInitiatorEntryToVal sessEntry) (by
                simp [Expr.eval, bndIkB, bndSpkB, bndOpkB, bndPqB, bundleV, eval_optMapE,
                  eval_isSomeE, sessEntry, e2eInitiatorEntryToVal]),
              eval_bindV_eq
                (m := pure ((keyIndPartnerRandKey? P st.respSessions sessEntry).map drKeyV)) (by
                  exact eval_partnerRandKeyCFuel hP nFuel _ _ _
                    (by simp [stResp, Expr.eval, e2eKeyIndStateToVal, hst_eq])
                    (by simp) hst.respSessions_le),
              pure_bind,
              eval_bindV_eq
                (m := (stepAIface ℓ I₀).liftP (drKeyV <$>
                  match keyIndPartnerRandKey? P st.respSessions sessEntry with
                  | some k => pure k
                  | none => sampleDRKey96)) (by
                  rw [eval_caseOptV_eq
                    (v? := (keyIndPartnerRandKey? P st.respSessions sessEntry).map drKeyV)
                    (by simp)]
                  rcases keyIndPartnerRandKey? P st.respSessions sessEntry with _ | k
                  · exact eval_sDrKey96C _
                  · simp [eval_retC, map_pure, liftP_pure])]
            unfold evalHkdfOrRo
            simp only [Bool.not_false, ↓reduceIte, ite_true, LawfulMonad.bind_assoc,
              st_run_lift_bind, pure_bind]
            have hpartner_bind :
                ((match keyIndPartnerRandKey? P st.respSessions sessEntry with
                  | some drKeyRand => do
                    set { st with sessions := { sessEntry with drKeyRand := drKeyRand } :: st.sessions }
                    match findHonestPrincipal P st.principals bnd.ikB with
                    | some _ => pure (KeyIndResponse.hdrResp hdr)
                    | none => pure (KeyIndResponse.initUnfreshResp drKeyReal hdr)
                  | none => do
                    let drKeyRand ← liftM sampleDRKey96
                    set { st with sessions := { sessEntry with drKeyRand := drKeyRand } :: st.sessions }
                    match findHonestPrincipal P st.principals bnd.ikB with
                    | some _ => pure (KeyIndResponse.hdrResp hdr)
                    | none => pure (KeyIndResponse.initUnfreshResp drKeyReal hdr)) :
                  StateT (KeyIndState S) ProbComp KeyIndResponse).run st =
                (match keyIndPartnerRandKey? P st.respSessions sessEntry with
                 | some k => pure k
                 | none => sampleDRKey96) >>= fun drKeyRand =>
                  ((do
                    set { st with sessions := { sessEntry with drKeyRand := drKeyRand } :: st.sessions }
                    match findHonestPrincipal P st.principals bnd.ikB with
                    | some _ => pure (KeyIndResponse.hdrResp hdr)
                    | none => pure (KeyIndResponse.initUnfreshResp drKeyReal hdr)) :
                    StateT (KeyIndState S) ProbComp KeyIndResponse).run st := by
              cases keyIndPartnerRandKey? P st.respSessions sessEntry
              · exact st_run_lift_bind sampleDRKey96 _ st
              · simp only [pure_bind]
            refine Eq.trans ?_
              (congrArg (fun m => (stepAIface ℓ I₀).liftP (encKiStepOut <$> m)) hpartner_bind.symm)
            simp only [liftP_bind, liftP_map, fmap_bind, map_bind, map_pure, pure_bind,
              LawfulMonad.bind_assoc, st_run_set_bind]
            congr 1; funext drKeyRand
            rw [eval_bindV_eq
                  (m := pure ((findHonestPrincipal P st.principals bnd.ikB).map
                    (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ))))) (by
                    rw [eval_findHonestCFuel hP nFuel _ _ _
                      (by simp [stPrin, Expr.eval, e2eKeyIndStateToVal, hst_eq]) hst.principals_le]
                    simp [Expr.eval, bndIkB, bundleV]),
              pure_bind, eval_retC]
            have hie_rand :
                ∀ {Δ} (eS : Expr (e2eOps ℓ P C K decT encT) Δ (e2eInitiatorEntryTy ℓ S))
                  (eR : Expr (e2eOps ℓ P C K decT encT) Δ drKeyT) (ρ' : Env Δ),
                  eS.eval ρ' = e2eInitiatorEntryToVal sessEntry →
                  eR.eval ρ' = drKeyV drKeyRand →
                  (ieSetRandE eS eR).eval ρ' =
                    e2eInitiatorEntryToVal { sessEntry with drKeyRand := drKeyRand } :=
              fun eS eR ρ' hs hr => eval_ieSetRandE eS eR ρ' sessEntry hs drKeyRand hr
            simp only [rsE, setSessE, eLet, Expr.eval]
            rw [hie_rand _ _ _ (by simp) (by simp)]
            rcases hfh : findHonestPrincipal P st.principals bnd.ikB with _ | ⟨_, _⟩ <;>
              cases st <;>
              simp only [hfh, Option.map, eCaseOpt, Expr.eval, eval_v_cons, eval_v_refl,
                env_get_zero, env_get_succ, rHdrE, rInitUnfreshE, setSessE, eLet, hst_eq,
                st_run_pure, map_pure, liftP_pure, encKiStepOut, keyIndRenc, e2eKeyIndStateToVal,
                stSecb, stPrin, stSpk, stOpk, stSess, List.map_cons]
        · simp only [hsig, Bool.false_eq_true, Bool.not_false, ↓reduceIte, ite_true, ite_false]
          exact eval_ret_rNoneE stV _ st (by simp [hst_eq])
      · simp only [hkosk, Bool.false_eq_true, Bool.not_false, ↓reduceIte, ite_true, ite_false]
        exact eval_ret_rNoneE stV _ st (by simp [hst_eq])

set_option linter.unusedSimpArgs false in
theorem eval_initiateOpkBFuel (hP : WellFormedPrimitivesδ P) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (uE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (iE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_send_opk))
    (bndE : Expr (e2eOps ℓ P C K decT encT) Γ bundleT) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st)
    (hst : stListBounded S nFuel st) :
    (initiateOpkBFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel stV uE iE bndE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P
          (.initiateOPK (uE.eval ρ) (iE.eval ρ) (bundleOfV (bndE.eval ρ)))).run st)) := by
  set bnd := bundleOfV (bndE.eval ρ)
  have hbndE : bndE.eval ρ = bundleV bnd := (bundleV_bundleOfV (bndE.eval ρ)).symm
  simp only [initiateOpkBFuel, Comp.eval, Expr.eval, eval_isNoneE, bndOpkB, hbndE, bundleV]
  unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl
  simp only [LawfulMonad.bind_assoc, st_run_get_bind, st_run_ite]
  cases bnd.opkB?
  · simp only [Option.isNone, ↓reduceIte, ite_true, Comp.eval, v, ext_refl_wk, ext_step_wk,
      Expr.eval, env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure,
      liftP_pure, encKiStepOut, keyIndRenc]
  · simp only [Option.isNone, Bool.false_eq_true, ↓reduceIte, ite_false]
    have h := eval_initiateCFuel (I₀ := I₀) hP nFuel stV (.inl (.pair uE iE)) uE bndE ρ hst_eq hst
    simpa only [Expr.eval, sidOfV, hbndE, bundleOfV_bundleV] using h

set_option linter.unusedSimpArgs false in
theorem eval_initiateNoOpkBFuel (hP : WellFormedPrimitivesδ P) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (uE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (iE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_send_no_opk))
    (bndE : Expr (e2eOps ℓ P C K decT encT) Γ bundleT) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st)
    (hst : stListBounded S nFuel st) :
    (initiateNoOpkBFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel stV uE iE bndE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P
          (.initiateNoOPK (uE.eval ρ) (iE.eval ρ) (bundleOfV (bndE.eval ρ)))).run st)) := by
  set bnd := bundleOfV (bndE.eval ρ)
  have hbndE : bndE.eval ρ = bundleV bnd := (bundleV_bundleOfV (bndE.eval ρ)).symm
  simp only [initiateNoOpkBFuel, Comp.eval, Expr.eval, eval_isSomeE, bndOpkB, hbndE, bundleV]
  unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl
  simp only [LawfulMonad.bind_assoc, st_run_get_bind, st_run_ite]
  cases bnd.opkB?
  · simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte, ite_false]
    have h := eval_initiateCFuel (I₀ := I₀) hP nFuel stV (.inr (.inl (.pair uE iE))) uE bndE ρ
      hst_eq hst
    simpa only [Expr.eval, sidOfV, hbndE, bundleOfV_bundleV] using h
  · simp only [Option.isSome, ↓reduceIte, ite_true, Comp.eval, v, ext_refl_wk, ext_step_wk,
      Expr.eval, env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure,
      liftP_pure, encKiStepOut, keyIndRenc]

set_option linter.unusedSimpArgs false in
theorem eval_acceptOpkBFuel (hP : WellFormedPrimitivesδ P) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (kE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (jE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (oE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_opk))
    (hdrE : Expr (e2eOps ℓ P C K decT encT) Γ hdrT) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st)
    (hst : stListBounded S nFuel st) :
    (acceptOpkBFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel stV kE jE oE hdrE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P
          (.acceptOPK (kE.eval ρ) (jE.eval ρ) (oE.eval ρ) (hdrOfV (hdrE.eval ρ)))).run st)) := by
  set hdr := hdrOfV (hdrE.eval ρ)
  have hhdrE : hdrE.eval ρ = hdrV hdr := (hdrV_hdrOfV (hdrE.eval ρ)).symm
  have hu_len : st.usedRecvOPK.length ≤ min nFuel S.N_opk_tot := hst.usedRecvOPK_le
  have hp_len :
      (st.principals.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ)))).length ≤
        min nFuel S.N_id := by
    simpa using hst.principals_le
  have hb_len :
      (st.spkBundles.map (Prod.map id (e2eSpkBundleEntryToVal (ℓ := ℓ)))).length ≤
        min nFuel S.N_spk_tot := by
    simpa using hst.spkBundles_le
  have ho_len :
      (st.opkEntries.map (Prod.map id (e2eOpkEntryToVal (ℓ := ℓ)))).length ≤
        min nFuel S.N_opk_tot := by
    simpa using hst.opkEntries_le
  simp only [acceptOpkBFuel, letV, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, eval_natEqE,
    eval_optPu32EqE, finValE, mkStepAPqxdhHooks_pureOp, eval_e2ePureOp, E2EPureOp.eval,
    env_get_zero, env_get_succ, pure_bind, hst_eq, hhdrE,
    hdrSpkId, hdrPqId, hdrOpkId, hdrIkA, hdrEkA, hdrV]
  set k := kE.eval ρ
  set j := jE.eval ρ
  set o := oE.eval ρ
  unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl
  simp only [LawfulMonad.bind_assoc, st_run_get_bind]
  have hhdr_guard :
      ((hdr.spkId == UInt32.ofNat j.val) &&
       ((hdr.pqspkId == UInt32.ofNat j.val) &&
        ((hdr.opkId? == some (UInt32.ofNat o.val)) &&
         ((hdr.ikAPk.length == 32) && (hdr.ekAPk.length == 32))))) =
      ((hdr.spkId == UInt32.ofNat j.val) &&
       (hdr.pqspkId == UInt32.ofNat j.val) &&
       (hdr.opkId? == some (UInt32.ofNat o.val)) &&
       (hdr.ikAPk.length == 32) &&
       (hdr.ekAPk.length == 32)) := by
    simp only [Bool.and_assoc]
  rw [hhdr_guard]
  by_cases hok :
      ((hdr.spkId == UInt32.ofNat j.val) &&
       (hdr.pqspkId == UInt32.ofNat j.val) &&
       (hdr.opkId? == some (UInt32.ofNat o.val)) &&
       (hdr.ikAPk.length == 32) &&
       (hdr.ekAPk.length == 32)) = true
  · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ite_false, eAny, Comp.eval, v,
      ext_refl_wk, ext_step_wk, Expr.eval, eval_natEqE, eval_nat3EqE, eval_e2ePureOp, E2EPureOp.eval,
      env_get_zero, env_get_succ, hst_eq, stUsedOpk, e2eKeyIndStateToVal,
      List.take_of_length_le hu_len]
    have hused_eq :
        st.usedRecvOPK.any (fun x => x == (k.val, j.val, o.val)) =
        st.usedRecvOPK.contains (k.val, j.val, o.val) := by
      rw [List.contains_eq_any_beq]
      apply List.any_congr rfl
      rintro ⟨a, b, c⟩
      rw [Bool.eq_iff_iff]
      simp only [beq_iff_eq]
      exact eq_comm
    rw [hused_eq]
    by_cases hused : st.usedRecvOPK.contains (k.val, j.val, o.val) = true
    · simp only [hused, ↓reduceIte, ite_true, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
        env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_ite, st_run_pure, map_pure,
        liftP_pure, encKiStepOut, keyIndRenc]
    · simp only [hused, Bool.false_eq_true, ↓reduceIte, ite_false, bindV, Comp.eval]
      rw [eval_koskSenderOkCFuel hP nFuel _ _ _
            (by simp [v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ, hst_eq])
            hst, pure_bind]
      simp only [v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ, hdrIkA, hdrV]
      by_cases hks : koskSenderOk P st.principals st.advKeys hdr.ikAPk = true
      · simp only [hks, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ite_false, caseOptV, eFind,
          mkStepAPqxdhHooks_pureOp, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
          eval_natEqE, eval_e2ePureOp, E2EPureOp.eval, eval_nat2EqE, eval_nat3EqE, env_get_zero,
          env_get_succ, hst_eq, stPrin, stSpk, stOpk, e2eKeyIndStateToVal,
          List.take_of_length_le hp_len, List.take_of_length_le hb_len,
          List.take_of_length_le ho_len]
        rw [principals_find_eq]
        rcases hkfind : st.principals.find? (fun (idx, _) => idx == k.val) with _ | ⟨_, kEntry⟩
        · simp only [hkfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
            env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure,
            encKiStepOut, keyIndRenc]
        · simp only [hkfind, Option.map, Prod.map, id, Comp.eval, v, ext_refl_wk, ext_step_wk,
            Expr.eval, eval_e2ePureOp, E2EPureOp.eval, eval_nat2EqE, env_get_zero, env_get_succ,
            hst_eq, stSpk, e2eKeyIndStateToVal, List.take_of_length_le hb_len]
          rw [spkBundles_find_eq]
          rcases hbfind : st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
              _ | ⟨_, bEntry⟩
          · simp only [hbfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
              env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure,
              encKiStepOut, keyIndRenc]
          · simp only [hbfind, Option.map, Prod.map, id, Comp.eval, v, ext_refl_wk, ext_step_wk,
              Expr.eval, eval_e2ePureOp, E2EPureOp.eval, eval_nat3EqE, env_get_zero, env_get_succ,
              hst_eq, stOpk, e2eKeyIndStateToVal, List.take_of_length_le ho_len]
            rw [opkEntries_find_eq]
            rcases hofind : st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
                _ | ⟨_, oEntry⟩
            · simp only [hofind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
                env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure,
                encKiStepOut, keyIndRenc]
            · simp only [hofind, Option.map, Prod.map, id, Comp.eval, v, ext_refl_wk, ext_step_wk,
                Expr.eval, env_get_zero, env_get_succ, oeCons, e2eOpkEntryToVal]
              by_cases hcons : oEntry.consumed = true
              · simp only [hcons, ↓reduceIte, ite_true, Comp.eval, v, ext_refl_wk, ext_step_wk,
                  Expr.eval, env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_ite,
                  st_run_pure, map_pure, liftP_pure, encKiStepOut, keyIndRenc]
              · simp only [hcons, Bool.false_eq_true, ↓reduceIte, ite_false, letV, Comp.eval,
                  pure_bind]
                rw [eval_checkSeenEFuel nFuel _ _ _ _ _ _
                      (by simpa [stSeen, e2eKeyIndStateToVal, v, ext_refl_wk, ext_step_wk,
                        Expr.eval, env_get_zero, env_get_succ, hst_eq] using
                        hst.seenKyberBaseKeys_le),
                  eval_acceptKeysC hP, pure_bind]
                simp only [v, ext_refl_wk, ext_step_wk, Expr.eval, eval_e2ePureOp, E2EPureOp.eval,
                  env_get_zero, env_get_succ, peSec0, e2ePrincipalEntryToVal, beSpkSk, bePqSk,
                  e2eSpkBundleEntryToVal, oeSk, e2eOpkEntryToVal, stSeen, e2eKeyIndStateToVal,
                  hdrPqId, hdrSpkId, hdrEkA, hdrV, hdrOfV_hdrV, hst_eq]
                rw [show hdrOfV (ℓ := ℓ)
                      (hdr.ikAPk, (hdr.ekAPk, (hdr.spkId, (hdr.opkId?, (hdr.pqspkId, hdr.kemCt))))) = hdr
                    by cases hdr; rfl]
                set seenPair := checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys
                  k.val hdr.pqspkId hdr.spkId hdr.ekAPk
                have hacc_eq :
                    acceptKeys P
                      { ikBSk := kEntry.secIKA0, ikBPk := [], spkBSk := bEntry.spkSk, spkBPk := [],
                        opkBSk? := some oEntry.opkSk, pqspkBSk := bEntry.pqspkSk, pqspkBPk := [],
                        trustedPeer := true, replayOk := seenPair.1, hdr := hdr } =
                    acceptKeys P
                      { ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk, spkBSk := bEntry.spkSk,
                        spkBPk := bEntry.spkPk, opkBSk? := some oEntry.opkSk,
                        pqspkBSk := bEntry.pqspkSk, pqspkBPk := bEntry.pqspkPk,
                        trustedPeer := true, replayOk := seenPair.1, hdr := hdr } := rfl
                rw [hacc_eq]
                rcases hacc : acceptKeys P
                    { ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk, spkBSk := bEntry.spkSk,
                      spkBPk := bEntry.spkPk, opkBSk? := some oEntry.opkSk,
                      pqspkBSk := bEntry.pqspkSk, pqspkBPk := bEntry.pqspkPk,
                      trustedPeer := true, replayOk := seenPair.1, hdr := hdr } with _ | dk
                · simp only [hacc, Option.map, caseOptV, Comp.eval, v, ext_refl_wk, ext_step_wk,
                    Expr.eval, env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure,
                    map_pure, liftP_pure, encKiStepOut, keyIndRenc]
                · have hopk_id : hdr.opkId? = some (UInt32.ofNat o.val) := by
                    simp only [Bool.and_eq_true, beq_iff_eq] at hok
                    exact hok.1.1.2
                  obtain ⟨ss, hdec, hdk_eq⟩ := acceptKeys_some_matched hacc
                    (Or.inr ⟨UInt32.ofNat o.val, oEntry.opkSk, hopk_id, rfl⟩)
                  dsimp only [Option.map] at hdec hdk_eq
                  rw [hdec]
                  dsimp only [Option.map]
                  rw [eval_findHonestCFuel hP nFuel _ _ _
                        (by simp [stPrin, e2eKeyIndStateToVal, v, ext_refl_wk, ext_step_wk,
                          Expr.eval, env_get_zero, env_get_succ, hst_eq]) hst.principals_le,
                    pure_bind]
                  unfold evalHkdfOrRo
                  simp only [Bool.not_false, ↓reduceIte, ite_true, LawfulMonad.bind_assoc,
                    st_run_lift_bind, st_run_set_bind, pure_bind, ← hdk_eq]
                  rw [st_run_bind]
                  set stUpdated : KeyIndState S :=
                    { st with
                      opkEntries := st.opkEntries.map (fun (idx, e) =>
                        if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true })
                        else (idx, e))
                      usedRecvOPK := (k.val, j.val, o.val) :: st.usedRecvOPK
                      seenKyberBaseKeys := seenPair.2
                      roCache := st.roCache }
                  set rEnt : KeyIndRespEntry S :=
                    { sid := .recvOPK k j o, respIkPk := kEntry.ikAPk, spkPk := bEntry.spkPk,
                      opkPk? := some oEntry.opkPk, pqspkPk := bEntry.pqspkPk, hdr := hdr,
                      senderHonest := (findHonestPrincipal P st.principals hdr.ikAPk).isSome,
                      drKeyReal := dk, drKeyRand := dk }
                  rw [eval_recordRespCFuel hP nFuel _ _ _
                    (st := stUpdated)
                    (by
                      simp only [setAcceptOpkE, eLet, eMap, finValE, mkStepAPqxdhHooks_pureOp, v,
                        ext_refl_wk, ext_step_wk, Expr.eval, eval_e2ePureOp, E2EPureOp.eval,
                        eval_nat3EqE, env_get_zero, env_get_succ, hst_eq, stSecb, stPrin, stSpk,
                        stSess, stResp, stUsedOpk, stUsedNoOpk, stRo, stAdv, stOpk,
                        e2eKeyIndStateToVal, List.take_of_length_le ho_len, stUpdated]
                      rw [show (st.opkEntries.map (Prod.map id (e2eOpkEntryToVal (ℓ := ℓ)))).map _ =
                            (st.opkEntries.map (fun (idx, e) =>
                              if idx == (k.val, j.val, o.val) then
                                (idx, { e with consumed := true })
                              else (idx, e))).map (Prod.map id (e2eOpkEntryToVal (ℓ := ℓ))) by
                          rw [List.map_map, List.map_map]
                          apply List.map_congr_left
                          intro ⟨idx, e⟩ _
                          by_cases h : idx = (k.val, j.val, o.val) <;>
                            simp [h, beq_iff_eq, eval_nat3EqE, Prod.map, oeSetConsE, eLet, v,
                              ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ,
                              oeSk, oePk, e2eOpkEntryToVal]])
                    (r := rEnt)
                    (by
                      simp [rEnt, e2eRespEntryToVal, sidV, peIkPk, e2ePrincipalEntryToVal,
                        beSpkPk, bePqPk, e2eSpkBundleEntryToVal, oePk, e2eOpkEntryToVal,
                        hdrIkA, hdrV, eval_isSomeE, v, ext_refl_wk, ext_step_wk, Expr.eval,
                        env_get_zero, env_get_succ])
                    hst.sessions_le]
                  simp only [liftP_bind, liftP_map, fmap_bind, map_bind, map_pure, pure_bind,
                    LawfulMonad.bind_assoc]
                  congr 1; funext ⟨_, stFinal⟩
                  rcases hfh : findHonestPrincipal P st.principals hdr.ikAPk with _ | ⟨_, _⟩ <;>
                    simp only [hdrIkA, hdrV, hfh, Option.map, eCaseOpt, Comp.eval, v, ext_refl_wk,
                      ext_step_wk, Expr.eval, env_get_zero, env_get_succ, rsE, rDrKeyE,
                      rAcceptFreshE, st_run_pure, map_pure, liftP_pure, encKiStepOut, keyIndRenc]
      · simp only [hks, Bool.false_eq_true, Bool.not_false, ↓reduceIte, ite_true, ite_false,
          Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ,
          rsE, rNoneE, hst_eq, st_run_ite, st_run_pure, map_pure, liftP_pure, encKiStepOut,
          keyIndRenc]
  · simp only [hok, Bool.false_eq_true, Bool.not_false, ↓reduceIte, ite_true, ite_false,
      Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ,
      rsE, rNoneE, hst_eq, st_run_ite, st_run_pure, map_pure, liftP_pure, encKiStepOut, keyIndRenc]

set_option linter.unusedSimpArgs false in
theorem eval_acceptNoOpkBFuel (hP : WellFormedPrimitivesδ P) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (kE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (jE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (lE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_no_opk))
    (hdrE : Expr (e2eOps ℓ P C K decT encT) Γ hdrT) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st)
    (hst : stListBounded S nFuel st) :
    (acceptNoOpkBFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel stV kE jE lE hdrE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P
          (.acceptNoOPK (kE.eval ρ) (jE.eval ρ) (lE.eval ρ) (hdrOfV (hdrE.eval ρ)))).run st)) := by
  set hdr := hdrOfV (hdrE.eval ρ)
  have hhdrE : hdrE.eval ρ = hdrV hdr := (hdrV_hdrOfV (hdrE.eval ρ)).symm
  have hu_len : st.usedRecvNoOPK.length ≤ min nFuel S.N_no_opk_tot := hst.usedRecvNoOPK_le
  have hp_len :
      (st.principals.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ)))).length ≤
        min nFuel S.N_id := by
    simpa using hst.principals_le
  have hb_len :
      (st.spkBundles.map (Prod.map id (e2eSpkBundleEntryToVal (ℓ := ℓ)))).length ≤
        min nFuel S.N_spk_tot := by
    simpa using hst.spkBundles_le
  simp only [acceptNoOpkBFuel, letV, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, eval_natEqE,
    eval_isNoneE, finValE, mkStepAPqxdhHooks_pureOp, eval_e2ePureOp, E2EPureOp.eval,
    env_get_zero, env_get_succ, pure_bind, hst_eq, hhdrE,
    hdrSpkId, hdrPqId, hdrOpkId, hdrIkA, hdrEkA, hdrV]
  set k := kE.eval ρ
  set j := jE.eval ρ
  set l := lE.eval ρ
  unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl
  simp only [LawfulMonad.bind_assoc, st_run_get_bind]
  have hhdr_guard :
      ((hdr.spkId == UInt32.ofNat j.val) &&
       ((hdr.pqspkId == UInt32.ofNat j.val) &&
        (hdr.opkId?.isNone &&
         ((hdr.ikAPk.length == 32) && (hdr.ekAPk.length == 32))))) =
      ((hdr.spkId == UInt32.ofNat j.val) &&
       (hdr.pqspkId == UInt32.ofNat j.val) &&
       (hdr.opkId? == none) &&
       (hdr.ikAPk.length == 32) &&
       (hdr.ekAPk.length == 32)) := by
    cases hdr.opkId? <;> simp [Bool.and_assoc]
  rw [hhdr_guard]
  by_cases hok :
      ((hdr.spkId == UInt32.ofNat j.val) &&
       (hdr.pqspkId == UInt32.ofNat j.val) &&
       (hdr.opkId? == none) &&
       (hdr.ikAPk.length == 32) &&
       (hdr.ekAPk.length == 32)) = true
  · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ite_false, eAny, Comp.eval, v,
      ext_refl_wk, ext_step_wk, Expr.eval, eval_natEqE, eval_nat3EqE, eval_e2ePureOp, E2EPureOp.eval,
      env_get_zero, env_get_succ, hst_eq, stUsedNoOpk, e2eKeyIndStateToVal,
      List.take_of_length_le hu_len]
    have hused_eq :
        st.usedRecvNoOPK.any (fun x => x == (k.val, j.val, l.val)) =
        st.usedRecvNoOPK.contains (k.val, j.val, l.val) := by
      rw [List.contains_eq_any_beq]
      apply List.any_congr rfl
      rintro ⟨a, b, c⟩
      rw [Bool.eq_iff_iff]
      simp only [beq_iff_eq]
      exact eq_comm
    rw [hused_eq]
    by_cases hused : st.usedRecvNoOPK.contains (k.val, j.val, l.val) = true
    · simp only [hused, ↓reduceIte, ite_true, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
        env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_ite, st_run_pure, map_pure,
        liftP_pure, encKiStepOut, keyIndRenc]
    · simp only [hused, Bool.false_eq_true, ↓reduceIte, ite_false, bindV, Comp.eval]
      rw [eval_koskSenderOkCFuel hP nFuel _ _ _
            (by simp [v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ, hst_eq])
            hst, pure_bind]
      simp only [v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ, hdrIkA, hdrV]
      by_cases hks : koskSenderOk P st.principals st.advKeys hdr.ikAPk = true
      · simp only [hks, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ite_false, caseOptV, eFind,
          mkStepAPqxdhHooks_pureOp, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
          eval_natEqE, eval_e2ePureOp, E2EPureOp.eval, eval_nat2EqE, env_get_zero, env_get_succ,
          hst_eq, stPrin, stSpk, e2eKeyIndStateToVal,
          List.take_of_length_le hp_len, List.take_of_length_le hb_len]
        rw [principals_find_eq]
        rcases hkfind : st.principals.find? (fun (idx, _) => idx == k.val) with _ | ⟨_, kEntry⟩
        · simp only [hkfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
            env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure,
            encKiStepOut, keyIndRenc]
        · simp only [hkfind, Option.map, Prod.map, id, Comp.eval, v, ext_refl_wk, ext_step_wk,
            Expr.eval, eval_e2ePureOp, E2EPureOp.eval, eval_nat2EqE, env_get_zero, env_get_succ,
            hst_eq, stSpk, e2eKeyIndStateToVal, List.take_of_length_le hb_len]
          rw [spkBundles_find_eq]
          rcases hbfind : st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
              _ | ⟨_, bEntry⟩
          · simp only [hbfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
              env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure,
              encKiStepOut, keyIndRenc]
          · simp only [hbfind, Option.map, Prod.map, id, letV, Comp.eval, pure_bind]
            rw [eval_checkSeenEFuel nFuel _ _ _ _ _ _
                  (by simpa [stSeen, e2eKeyIndStateToVal, v, ext_refl_wk, ext_step_wk,
                    Expr.eval, env_get_zero, env_get_succ, hst_eq] using
                    hst.seenKyberBaseKeys_le),
              eval_acceptKeysC hP, pure_bind]
            simp only [v, ext_refl_wk, ext_step_wk, Expr.eval, eval_e2ePureOp, E2EPureOp.eval,
              env_get_zero, env_get_succ, peSec0, e2ePrincipalEntryToVal, beSpkSk, bePqSk,
              e2eSpkBundleEntryToVal, stSeen, e2eKeyIndStateToVal, hdrPqId, hdrSpkId, hdrEkA,
              hdrV, hdrOfV_hdrV, hst_eq]
            rw [show hdrOfV (ℓ := ℓ)
                  (hdr.ikAPk, (hdr.ekAPk, (hdr.spkId, (hdr.opkId?, (hdr.pqspkId, hdr.kemCt))))) = hdr
                by cases hdr; rfl]
            set seenPair := checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys
              k.val hdr.pqspkId hdr.spkId hdr.ekAPk
            have hacc_eq :
                acceptKeys P
                  { ikBSk := kEntry.secIKA0, ikBPk := [], spkBSk := bEntry.spkSk, spkBPk := [],
                    opkBSk? := none, pqspkBSk := bEntry.pqspkSk, pqspkBPk := [],
                    trustedPeer := true, replayOk := seenPair.1, hdr := hdr } =
                acceptKeys P
                  { ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk, spkBSk := bEntry.spkSk,
                    spkBPk := bEntry.spkPk, opkBSk? := none,
                    pqspkBSk := bEntry.pqspkSk, pqspkBPk := bEntry.pqspkPk,
                    trustedPeer := true, replayOk := seenPair.1, hdr := hdr } := rfl
            rw [hacc_eq]
            rcases hacc : acceptKeys P
                { ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk, spkBSk := bEntry.spkSk,
                  spkBPk := bEntry.spkPk, opkBSk? := none,
                  pqspkBSk := bEntry.pqspkSk, pqspkBPk := bEntry.pqspkPk,
                  trustedPeer := true, replayOk := seenPair.1, hdr := hdr } with _ | dk
            · simp only [hacc, Option.map, caseOptV, Comp.eval, v, ext_refl_wk, ext_step_wk,
                Expr.eval, env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure,
                liftP_pure, encKiStepOut, keyIndRenc]
            · have hopk_id : hdr.opkId? = none := by
                simp only [Bool.and_eq_true, beq_iff_eq] at hok
                exact hok.1.1.2
              obtain ⟨ss, hdec, hdk_eq⟩ := acceptKeys_some_matched hacc (Or.inl ⟨hopk_id, rfl⟩)
              dsimp only [Option.map] at hdec hdk_eq
              rw [hdec]
              dsimp only [Option.map]
              rw [eval_findHonestCFuel hP nFuel _ _ _
                    (by simp [stPrin, e2eKeyIndStateToVal, v, ext_refl_wk, ext_step_wk,
                      Expr.eval, env_get_zero, env_get_succ, hst_eq]) hst.principals_le,
                pure_bind]
              unfold evalHkdfOrRo
              simp only [Bool.not_false, ↓reduceIte, ite_true, LawfulMonad.bind_assoc,
                st_run_lift_bind, st_run_set_bind, pure_bind, ← hdk_eq]
              rw [st_run_bind]
              set stUpdated : KeyIndState S :=
                { st with
                  usedRecvNoOPK := (k.val, j.val, l.val) :: st.usedRecvNoOPK
                  seenKyberBaseKeys := seenPair.2
                  roCache := st.roCache }
              set rEnt : KeyIndRespEntry S :=
                { sid := .recvNoOPK k j l, respIkPk := kEntry.ikAPk, spkPk := bEntry.spkPk,
                  opkPk? := none, pqspkPk := bEntry.pqspkPk, hdr := hdr,
                  senderHonest := (findHonestPrincipal P st.principals hdr.ikAPk).isSome,
                  drKeyReal := dk, drKeyRand := dk }
              rw [eval_recordRespCFuel hP nFuel _ _ _
                (st := stUpdated)
                (by
                  cases st
                  simp only [setAcceptNoOpkE, eLet, finValE, mkStepAPqxdhHooks_pureOp, v,
                    ext_refl_wk, ext_step_wk, Expr.eval, eval_e2ePureOp, E2EPureOp.eval,
                    env_get_zero, env_get_succ, hst_eq, stSecb, stPrin, stSpk, stOpk, stSess,
                    stResp, stUsedOpk, stUsedNoOpk, stRo, stAdv, e2eKeyIndStateToVal, stUpdated])
                (r := rEnt)
                (by
                  simp [rEnt, e2eRespEntryToVal, sidV, peIkPk, e2ePrincipalEntryToVal,
                    beSpkPk, bePqPk, e2eSpkBundleEntryToVal, hdrIkA, hdrV, eval_isSomeE, v,
                    ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ])
                hst.sessions_le]
              simp only [liftP_bind, liftP_map, fmap_bind, map_bind, map_pure, pure_bind,
                LawfulMonad.bind_assoc]
              congr 1; funext ⟨_, stFinal⟩
              rcases hfh : findHonestPrincipal P st.principals hdr.ikAPk with _ | ⟨_, _⟩ <;>
                simp only [hdrIkA, hdrV, hfh, Option.map, eCaseOpt, Comp.eval, v, ext_refl_wk,
                  ext_step_wk, Expr.eval, env_get_zero, env_get_succ, rsE, rDrKeyE, rAcceptFreshE,
                  st_run_pure, map_pure, liftP_pure, encKiStepOut, keyIndRenc]
      · simp only [hks, Bool.false_eq_true, Bool.not_false, ↓reduceIte, ite_true, ite_false,
          Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ,
          rsE, rNoneE, hst_eq, st_run_ite, st_run_pure, map_pure, liftP_pure, encKiStepOut,
          keyIndRenc]
  · simp only [hok, Bool.false_eq_true, Bool.not_false, ↓reduceIte, ite_true, ite_false,
      Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ,
      rsE, rNoneE, hst_eq, st_run_ite, st_run_pure, map_pure, liftP_pure, encKiStepOut, keyIndRenc]

set_option linter.unusedSimpArgs false in
theorem eval_testBFuel (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st)
    (hst : stListBounded S nFuel st) :
    (testBFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel stV sidE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P (.testSession (sidOfV (sidE.eval ρ)))).run st)) := by
  set sid := sidOfV (sidE.eval ρ)
  have hsidE : sidE.eval ρ = sidV sid := (sidV_sidOfV (sidE.eval ρ)).symm
  have hs_len :
      (st.sessions.map (e2eInitiatorEntryToVal (ℓ := ℓ))).length ≤ min nFuel S.N_send_tot := by
    simpa using hst.sessions_le
  have hr_len :
      (st.respSessions.map (e2eRespEntryToVal (ℓ := ℓ))).length ≤ min nFuel S.N_recv_tot := by
    simpa using hst.respSessions_le
  simp only [testBFuel, letV, Comp.eval, pure_bind, hsidE]
  have htest := eval_isTestableEFuel (S := S) (I₀ := I₀) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nFuel
    (v (Γ := Γ) stV) (v (Γ := sidT S :: Γ) Var.zero)
    (.cons (sidV sid) ρ) (by simp [eval_v_cons, eval_v_refl, hst_eq]) hst
  simp only [Expr.eval, htest, eval_v_refl, env_get_zero, sidOfV_sidV]
  unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl
  simp only [LawfulMonad.bind_assoc, st_run_get_bind]
  by_cases htestable : isKeyIndSessionTestable st sid = true
  · simp only [htestable, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ite_false, caseOptV, eFind,
      eMap, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ, hst_eq,
      stSess, stResp, e2eKeyIndStateToVal,
      List.take_of_length_le hs_len, List.take_of_length_le hr_len]
    have hs_find_eq :
        (st.sessions.map (e2eInitiatorEntryToVal (ℓ := ℓ))).find?
          (fun e => (sidEqE (mkStepAPqxdhHooks ℓ P C K decT encT I₀)
            (ieSid (Expr.var Var.zero))
            (Expr.var Var.zero.succ)).eval (.cons e (.cons (sidV sid) ρ))) =
        (st.sessions.find? (fun e => e.sid == sid)).map (e2eInitiatorEntryToVal (ℓ := ℓ)) := by
      rw [List.find?_map]
      apply congrArg (Option.map _)
      apply List.find?_congr
      intro e _
      dsimp only [Function.comp_def]
      rw [eval_sidEqE]
      simp [ieSid, e2eInitiatorEntryToVal, Expr.eval, env_get_zero, env_get_succ, sidOfV_sidV]
    rw [hs_find_eq]
    rcases hsfind : st.sessions.find? (fun e => e.sid == sid) with _ | e
    · simp only [hsfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
        env_get_zero, env_get_succ, hst_eq, stResp, e2eKeyIndStateToVal,
        List.take_of_length_le hr_len]
      have hr_find_eq :
          (st.respSessions.map (e2eRespEntryToVal (ℓ := ℓ))).find?
            (fun r => (sidEqE (mkStepAPqxdhHooks ℓ P C K decT encT I₀)
              (reSid (Expr.var Var.zero))
              (Expr.var Var.zero.succ)).eval (.cons r (.cons (sidV sid) ρ))) =
          (st.respSessions.find? (fun r => r.sid == sid)).map (e2eRespEntryToVal (ℓ := ℓ)) := by
        rw [List.find?_map]
        apply congrArg (Option.map _)
        apply List.find?_congr
        intro r _
        dsimp only [Function.comp_def]
        rw [eval_sidEqE]
        simp [reSid, e2eRespEntryToVal, Expr.eval, env_get_zero, env_get_succ, sidOfV_sidV]
      rw [hr_find_eq]
      rcases hrfind : st.respSessions.find? (fun r => r.sid == sid) with _ | r
      · simp only [hrfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
          env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure,
          encKiStepOut, keyIndRenc]
      · simp only [hrfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
          env_get_zero, env_get_succ, hst_eq, List.take_of_length_le hr_len,
          LawfulMonad.bind_assoc, st_run_set_bind, st_run_map_set, st_run_pure, map_pure,
          liftP_pure, encKiStepOut, keyIndRenc, rsE, rDrKeyE, setRespE, eLet, stSecb, stPrin,
          stSpk, stOpk, stSess, stResp, stUsedOpk, stUsedNoOpk, stSeen, stRo, stAdv, reReal,
          reRand, e2eKeyIndStateToVal, e2eRespEntryToVal]
        rw [show (st.respSessions.map (e2eRespEntryToVal (ℓ := ℓ))).map _ =
              (st.respSessions.map (fun x =>
                if x.sid == sid then { x with tested := true } else x)).map
                (e2eRespEntryToVal (ℓ := ℓ)) by
            rw [List.map_map, List.map_map]
            apply List.map_congr_left
            intro x _
            dsimp only [Function.comp_def]
            rw [eval_sidEqE]
            simp only [reSid, e2eRespEntryToVal, sidOfV_sidV, v, ext_refl_wk, ext_step_wk,
              Expr.eval, env_get_zero, env_get_succ]
            split_ifs <;> simp [reSetTestedE, eLet, v, ext_refl_wk, ext_step_wk, Expr.eval,
              env_get_zero, env_get_succ, e2eRespEntryToVal, reSid, reReal, reRand, reTested,
              reIk, reSpk, reOpk, rePq, reHdr, reSendHon, reRev]]
        rcases st with ⟨secb, _⟩
        cases secb <;> simp [encKiStepOut, keyIndRenc, e2eKeyIndStateToVal]
    · simp only [hsfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
        env_get_zero, env_get_succ, hst_eq, List.take_of_length_le hs_len,
        LawfulMonad.bind_assoc, st_run_set_bind, st_run_map_set, st_run_pure, map_pure,
        liftP_pure, encKiStepOut, keyIndRenc, rsE, rDrKeyE, setSessE, eLet, stSecb, stPrin,
        stSpk, stOpk, stSess, stResp, stUsedOpk, stUsedNoOpk, stSeen, stRo, stAdv, ieReal,
        ieRand, e2eKeyIndStateToVal, e2eInitiatorEntryToVal]
      rw [show (st.sessions.map (e2eInitiatorEntryToVal (ℓ := ℓ))).map _ =
            (st.sessions.map (fun x =>
              if x.sid == sid then { x with tested := true } else x)).map
              (e2eInitiatorEntryToVal (ℓ := ℓ)) by
          rw [List.map_map, List.map_map]
          apply List.map_congr_left
          intro x _
          dsimp only [Function.comp_def]
          rw [eval_sidEqE]
          simp only [ieSid, e2eInitiatorEntryToVal, sidOfV_sidV, v, ext_refl_wk, ext_step_wk,
            Expr.eval, env_get_zero, env_get_succ]
          split_ifs <;> simp [ieSetTestedE, eLet, v, ext_refl_wk, ext_step_wk, Expr.eval,
            env_get_zero, env_get_succ, e2eInitiatorEntryToVal, ieSid, ieReal, ieRand, ieTested,
            ieHonPeer, iePeerIk, iePeerSpk, iePeerOpk, iePeerPq, ieSpkHon, ieOpkHon, iePqHon,
            ieEkSk, ieFresh, ieHdr, ieRev]]
      rcases st with ⟨secb, _⟩
      cases secb <;> simp [encKiStepOut, keyIndRenc, e2eKeyIndStateToVal]
  · simp only [htestable, Bool.false_eq_true, Bool.not_false, ↓reduceIte, ite_true, ite_false,
      Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ,
      rsE, rNoneE, hst_eq, st_run_ite, st_run_pure, map_pure, liftP_pure, encKiStepOut, keyIndRenc]

set_option linter.unusedSimpArgs false in
theorem eval_revealBFuel (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st)
    (hst : stListBounded S nFuel st) :
    (revealBFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel stV sidE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P (.revealSessionKey (sidOfV (sidE.eval ρ)))).run st)) := by
  set sid := sidOfV (sidE.eval ρ)
  have hsidE : sidE.eval ρ = sidV sid := (sidV_sidOfV (sidE.eval ρ)).symm
  have hs_len :
      (st.sessions.map (e2eInitiatorEntryToVal (ℓ := ℓ))).length ≤ min nFuel S.N_send_tot := by
    simpa using hst.sessions_le
  have hr_len :
      (st.respSessions.map (e2eRespEntryToVal (ℓ := ℓ))).length ≤ min nFuel S.N_recv_tot := by
    simpa using hst.respSessions_le
  simp only [revealBFuel, letV, caseOptV, eFind, eMap, Comp.eval, v, ext_refl_wk, ext_step_wk,
    Expr.eval, env_get_zero, env_get_succ, pure_bind, hst_eq, hsidE, stSess, stResp,
    e2eKeyIndStateToVal, List.take_of_length_le hs_len, List.take_of_length_le hr_len]
  have hs_find_eq :
      (st.sessions.map (e2eInitiatorEntryToVal (ℓ := ℓ))).find?
        (fun e => (sidEqE (mkStepAPqxdhHooks ℓ P C K decT encT I₀)
          (ieSid (Expr.var Var.zero))
          (Expr.var Var.zero.succ)).eval (.cons e (.cons (sidV sid) ρ))) =
      (st.sessions.find? (fun e => e.sid == sid)).map (e2eInitiatorEntryToVal (ℓ := ℓ)) := by
    rw [List.find?_map]
    apply congrArg (Option.map _)
    apply List.find?_congr
    intro e _
    dsimp only [Function.comp_def]
    rw [eval_sidEqE]
    simp [ieSid, e2eInitiatorEntryToVal, Expr.eval, env_get_zero, env_get_succ, sidOfV_sidV]
  rw [hs_find_eq]
  unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl
  simp only [LawfulMonad.bind_assoc, st_run_get_bind]
  rcases hsfind : st.sessions.find? (fun e => e.sid == sid) with _ | e
  · simp only [hsfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
      env_get_zero, env_get_succ, hst_eq, stResp, e2eKeyIndStateToVal,
      List.take_of_length_le hr_len]
    have hr_find_eq :
        (st.respSessions.map (e2eRespEntryToVal (ℓ := ℓ))).find?
          (fun r => (sidEqE (mkStepAPqxdhHooks ℓ P C K decT encT I₀)
            (reSid (Expr.var Var.zero))
            (Expr.var Var.zero.succ)).eval (.cons r (.cons (sidV sid) ρ))) =
        (st.respSessions.find? (fun r => r.sid == sid)).map (e2eRespEntryToVal (ℓ := ℓ)) := by
      rw [List.find?_map]
      apply congrArg (Option.map _)
      apply List.find?_congr
      intro r _
      dsimp only [Function.comp_def]
      rw [eval_sidEqE]
      simp [reSid, e2eRespEntryToVal, Expr.eval, env_get_zero, env_get_succ, sidOfV_sidV]
    rw [hr_find_eq]
    rcases hrfind : st.respSessions.find? (fun r => r.sid == sid) with _ | r
    · simp only [hrfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
        env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure,
        encKiStepOut, keyIndRenc]
    · simp only [hrfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
        env_get_zero, env_get_succ, reTested, e2eRespEntryToVal]
      by_cases hrtest : r.tested = true
      · simp only [hrtest, ↓reduceIte, ite_true, Comp.eval, v, ext_refl_wk, ext_step_wk,
          Expr.eval, env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_ite, st_run_pure,
          map_pure, liftP_pure, encKiStepOut, keyIndRenc]
      · simp only [hrtest, Bool.false_eq_true, ↓reduceIte, ite_false, Comp.eval, v, ext_refl_wk,
          ext_step_wk, Expr.eval, env_get_zero, env_get_succ, hst_eq,
          List.take_of_length_le hr_len, st_run_ite, LawfulMonad.bind_assoc,
          st_run_set_bind, st_run_map_set, st_run_pure, map_pure, liftP_pure, encKiStepOut,
          keyIndRenc, rsE, rDrKeyE, setRespE, eLet, stSecb, stPrin, stSpk, stOpk, stSess, stResp,
          stUsedOpk, stUsedNoOpk, stSeen, stRo, stAdv, reReal, e2eKeyIndStateToVal,
          e2eRespEntryToVal]
        rw [show (st.respSessions.map (e2eRespEntryToVal (ℓ := ℓ))).map _ =
              (st.respSessions.map (fun x =>
                if x.sid == sid then { x with revealed := true } else x)).map
                (e2eRespEntryToVal (ℓ := ℓ)) by
            rw [List.map_map, List.map_map]
            apply List.map_congr_left
            intro x _
            dsimp only [Function.comp_def]
            rw [eval_sidEqE]
            simp only [reSid, e2eRespEntryToVal, sidOfV_sidV, v, ext_refl_wk, ext_step_wk,
              Expr.eval, env_get_zero, env_get_succ]
            split_ifs <;> simp [reSetRevE, eLet, v, ext_refl_wk, ext_step_wk, Expr.eval,
              env_get_zero, env_get_succ, e2eRespEntryToVal, reSid, reReal, reRand, reTested,
              reIk, reSpk, reOpk, rePq, reHdr, reSendHon, reRev]]
  · simp only [hsfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
      env_get_zero, env_get_succ, ieTested, e2eInitiatorEntryToVal]
    by_cases hstest : e.tested = true
    · simp only [hstest, ↓reduceIte, ite_true, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
        env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_ite, st_run_pure, map_pure,
        liftP_pure, encKiStepOut, keyIndRenc]
    · simp only [hstest, Bool.false_eq_true, ↓reduceIte, ite_false, Comp.eval, v, ext_refl_wk,
        ext_step_wk, Expr.eval, env_get_zero, env_get_succ, hst_eq,
        List.take_of_length_le hs_len, st_run_ite, LawfulMonad.bind_assoc,
        st_run_set_bind, st_run_map_set, st_run_pure, map_pure, liftP_pure, encKiStepOut,
        keyIndRenc, rsE, rDrKeyE, setSessE, eLet, stSecb, stPrin, stSpk, stOpk, stSess, stResp,
        stUsedOpk, stUsedNoOpk, stSeen, stRo, stAdv, ieReal, e2eKeyIndStateToVal,
        e2eInitiatorEntryToVal]
      rw [show (st.sessions.map (e2eInitiatorEntryToVal (ℓ := ℓ))).map _ =
            (st.sessions.map (fun x =>
              if x.sid == sid then { x with revealed := true } else x)).map
              (e2eInitiatorEntryToVal (ℓ := ℓ)) by
          rw [List.map_map, List.map_map]
          apply List.map_congr_left
          intro x _
          dsimp only [Function.comp_def]
          rw [eval_sidEqE]
          simp only [ieSid, e2eInitiatorEntryToVal, sidOfV_sidV, v, ext_refl_wk, ext_step_wk,
            Expr.eval, env_get_zero, env_get_succ]
          split_ifs <;> simp [ieSetRevE, eLet, v, ext_refl_wk, ext_step_wk, Expr.eval,
            env_get_zero, env_get_succ, e2eInitiatorEntryToVal, ieSid, ieReal, ieRand, ieTested,
            ieHonPeer, iePeerIk, iePeerSpk, iePeerOpk, iePeerPq, ieSpkHon, ieOpkHon, iePqHon,
            ieEkSk, ieFresh, ieHdr, ieRev]]

set_option linter.unusedSimpArgs false in
theorem eval_revealSpkBFuel (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stV : Var Γ (e2eKeyIndStateTy ℓ S))
    (uE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (jE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv)) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : ρ.get stV = e2eKeyIndStateToVal st)
    (hst : stListBounded S nFuel st) :
    (revealSpkBFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel stV uE jE).eval ρ =
      (stepAIface ℓ I₀).liftP (encKiStepOut <$>
        ((pqxdhKeyIndImpl1KeyReal S P (.revealSpkSk (uE.eval ρ) (jE.eval ρ))).run st)) := by
  have hb_len :
      (st.spkBundles.map (Prod.map id (e2eSpkBundleEntryToVal (ℓ := ℓ)))).length ≤
        min nFuel S.N_spk_tot := by
    simpa using hst.spkBundles_le
  simp only [revealSpkBFuel, letV, caseOptV, eFind, eMap, finValE, mkStepAPqxdhHooks, Comp.eval,
    v, ext_refl_wk, ext_step_wk, Expr.eval, eval_e2ePureOp, E2EPureOp.eval, eval_nat2EqE,
    env_get_zero, env_get_succ, pure_bind, hst_eq, stSpk, e2eKeyIndStateToVal,
    List.take_of_length_le hb_len]
  set u := uE.eval ρ
  set j := jE.eval ρ
  rw [spkBundles_find_eq]
  unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl
  simp only [LawfulMonad.bind_assoc, st_run_get_bind]
  rcases hbfind : st.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with _ | ⟨_, bEntry⟩
  · simp only [hbfind, Option.map, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
      env_get_zero, env_get_succ, rsE, rNoneE, hst_eq, st_run_pure, map_pure, liftP_pure,
      encKiStepOut, keyIndRenc]
  · simp only [hbfind, Option.map, Prod.map, id, Comp.eval, v, ext_refl_wk, ext_step_wk,
      Expr.eval, env_get_zero, env_get_succ, hst_eq, List.take_of_length_le hb_len,
      LawfulMonad.bind_assoc, st_run_set_bind, st_run_map_set, st_run_pure, map_pure, liftP_pure,
      encKiStepOut, keyIndRenc, rsE, rSpkSkE, setSpkE, eLet, stSecb, stPrin, stSpk, stOpk,
      stSess, stResp, stUsedOpk, stUsedNoOpk, stSeen, stRo, stAdv, beSpkSk,
      e2eKeyIndStateToVal, e2eSpkBundleEntryToVal]
    rw [show (st.spkBundles.map (Prod.map id (e2eSpkBundleEntryToVal (ℓ := ℓ)))).map _ =
          (st.spkBundles.map (fun (idx, b) =>
            if idx == (u.val, j.val) then (idx, { b with revealed := true }) else (idx, b))).map
            (Prod.map id (e2eSpkBundleEntryToVal (ℓ := ℓ))) by
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro ⟨idx, b⟩ _
        by_cases h : idx = (u.val, j.val) <;>
          simp [h, beq_iff_eq, Prod.map, beSetRevE, eLet, v, ext_refl_wk, ext_step_wk, Expr.eval,
            env_get_zero, env_get_succ, beSpkSk, beSpkPk, bePqSk, bePqPk, beSpkSig, bePqSig,
            e2eSpkBundleEntryToVal]]

end BranchProofs

/-! ## Zero-target-query bounds -/

section BranchZeroQueries

variable {ℓ : ℕ} {S : Setup} {O : Ops (e2eSig ℓ)} {ι : Type} {T : OracleSpec ι}
  {I : Iface (e2eSig ℓ) T}

@[simp] theorem queriesUB_initPrin1KeyB {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hQ : HooksNoTargetQueries H w) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (u : Expr O Γ (FinT S.N_id)) :
    compQueriesUB w (fun _ => 0) (initPrin1KeyB H st u) = 0 := by
  simp [initPrin1KeyB, queriesUB_sBytes32C hQ, hQ.callPrim_q]

@[simp] theorem queriesUB_initPrin1KeyBFuel {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hQ : HooksNoTargetQueries H w) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (u : Expr O Γ (FinT S.N_id)) :
    compQueriesUB w (fun _ => 0) (initPrin1KeyBFuel H nFuel st u) = 0 := by
  simp [initPrin1KeyBFuel, queriesUB_sBytes32C hQ, hQ.callPrim_q]

@[simp] theorem queriesUB_corruptB {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (_hQ : HooksNoTargetQueries H w) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (u : Expr O Γ (FinT S.N_id)) :
    compQueriesUB w (fun _ => 0) (corruptB H st u) = 0 := by
  simp [corruptB]

@[simp] theorem queriesUB_corruptBFuel {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (_hQ : HooksNoTargetQueries H w) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (u : Expr O Γ (FinT S.N_id)) :
    compQueriesUB w (fun _ => 0) (corruptBFuel H nFuel st u) = 0 := by
  simp [corruptBFuel]

@[simp] theorem queriesUB_genSpkB {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hQ : HooksNoTargetQueries H w) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (u : Expr O Γ (FinT S.N_id))
    (j : Expr O Γ (FinT S.N_recv)) :
    compQueriesUB w (fun _ => 0) (genSpkB H st u j) = 0 := by
  simp [genSpkB, queriesUB_sBytes32C hQ, queriesUB_sRandom64C hQ,
    queriesUB_sKemKeyGenC hQ, hQ.callPrim_q]

@[simp] theorem queriesUB_genSpkBFuel {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hQ : HooksNoTargetQueries H w) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (u : Expr O Γ (FinT S.N_id))
    (j : Expr O Γ (FinT S.N_recv)) :
    compQueriesUB w (fun _ => 0) (genSpkBFuel H nFuel st u j) = 0 := by
  simp [genSpkBFuel, queriesUB_sBytes32C hQ, queriesUB_sRandom64C hQ,
    queriesUB_sKemKeyGenC hQ, hQ.callPrim_q]

@[simp] theorem queriesUB_genOpkB {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hQ : HooksNoTargetQueries H w) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (u : Expr O Γ (FinT S.N_id))
    (j : Expr O Γ (FinT S.N_recv)) (o : Expr O Γ (FinT S.N_opk)) :
    compQueriesUB w (fun _ => 0) (genOpkB H st u j o) = 0 := by
  simp [genOpkB, queriesUB_sBytes32C hQ, hQ.callPrim_q]

@[simp] theorem queriesUB_genOpkBFuel {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hQ : HooksNoTargetQueries H w) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (u : Expr O Γ (FinT S.N_id))
    (j : Expr O Γ (FinT S.N_recv)) (o : Expr O Γ (FinT S.N_opk)) :
    compQueriesUB w (fun _ => 0) (genOpkBFuel H nFuel st u j o) = 0 := by
  simp [genOpkBFuel, queriesUB_sBytes32C hQ, hQ.callPrim_q]

@[simp] theorem queriesUB_initiateC {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hQ : HooksNoTargetQueries H w) (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (sid : Expr O Γ (sidT S))
    (u : Expr O Γ (FinT S.N_id)) (bnd : Expr O Γ bundleT) :
    compQueriesUB w (fun _ => 0) (initiateC H nAdv st sid u bnd) = 0 := by
  simp [initiateC, queriesUB_koskBundleOkC hQ, queriesUB_sBytes32C hQ, queriesUB_sDrKey96C hQ,
    queriesUB_resolveSigPkC hQ, queriesUB_honestPeerC hQ, queriesUB_checkProvC hQ,
    queriesUB_partnerRandKeyC hQ, queriesUB_findHonestC hQ, hQ.callPrim_q]

@[simp] theorem queriesUB_initiateCFuel {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hQ : HooksNoTargetQueries H w) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (sid : Expr O Γ (sidT S))
    (u : Expr O Γ (FinT S.N_id)) (bnd : Expr O Γ bundleT) :
    compQueriesUB w (fun _ => 0) (initiateCFuel H nFuel st sid u bnd) = 0 := by
  simp [initiateCFuel, queriesUB_koskBundleOkCFuel hQ, queriesUB_sBytes32C hQ, queriesUB_sDrKey96C hQ,
    queriesUB_resolveSigPkCFuel hQ, queriesUB_honestPeerCFuel hQ, queriesUB_checkProvCFuel hQ,
    queriesUB_partnerRandKeyCFuel hQ, queriesUB_findHonestCFuel hQ, hQ.callPrim_q]

@[simp] theorem queriesUB_initiateOpkB {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hQ : HooksNoTargetQueries H w) (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (u : Expr O Γ (FinT S.N_id))
    (i : Expr O Γ (FinT S.N_send_opk)) (bnd : Expr O Γ bundleT) :
    compQueriesUB w (fun _ => 0) (initiateOpkB H nAdv st u i bnd) = 0 := by
  simp [initiateOpkB, queriesUB_initiateC hQ]

@[simp] theorem queriesUB_initiateOpkBFuel {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hQ : HooksNoTargetQueries H w) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (u : Expr O Γ (FinT S.N_id))
    (i : Expr O Γ (FinT S.N_send_opk)) (bnd : Expr O Γ bundleT) :
    compQueriesUB w (fun _ => 0) (initiateOpkBFuel H nFuel st u i bnd) = 0 := by
  simp [initiateOpkBFuel, queriesUB_initiateCFuel hQ]

@[simp] theorem queriesUB_initiateNoOpkB {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hQ : HooksNoTargetQueries H w) (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (u : Expr O Γ (FinT S.N_id))
    (i : Expr O Γ (FinT S.N_send_no_opk)) (bnd : Expr O Γ bundleT) :
    compQueriesUB w (fun _ => 0) (initiateNoOpkB H nAdv st u i bnd) = 0 := by
  simp [initiateNoOpkB, queriesUB_initiateC hQ]

@[simp] theorem queriesUB_initiateNoOpkBFuel {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hQ : HooksNoTargetQueries H w) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (u : Expr O Γ (FinT S.N_id))
    (i : Expr O Γ (FinT S.N_send_no_opk)) (bnd : Expr O Γ bundleT) :
    compQueriesUB w (fun _ => 0) (initiateNoOpkBFuel H nFuel st u i bnd) = 0 := by
  simp [initiateNoOpkBFuel, queriesUB_initiateCFuel hQ]

@[simp] theorem queriesUB_acceptOpkB {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hQ : HooksNoTargetQueries H w) (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (k : Expr O Γ (FinT S.N_id))
    (j : Expr O Γ (FinT S.N_recv)) (o : Expr O Γ (FinT S.N_opk))
    (hdr : Expr O Γ hdrT) :
    compQueriesUB w (fun _ => 0) (acceptOpkB H nAdv st k j o hdr) = 0 := by
  simp [acceptOpkB, queriesUB_koskSenderOkC hQ, queriesUB_acceptKeysC hQ,
    queriesUB_findHonestC hQ, queriesUB_recordRespC hQ]

@[simp] theorem queriesUB_acceptOpkBFuel {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hQ : HooksNoTargetQueries H w) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (k : Expr O Γ (FinT S.N_id))
    (j : Expr O Γ (FinT S.N_recv)) (o : Expr O Γ (FinT S.N_opk))
    (hdr : Expr O Γ hdrT) :
    compQueriesUB w (fun _ => 0) (acceptOpkBFuel H nFuel st k j o hdr) = 0 := by
  simp [acceptOpkBFuel, queriesUB_koskSenderOkCFuel hQ, queriesUB_acceptKeysC hQ,
    queriesUB_findHonestCFuel hQ, queriesUB_recordRespCFuel hQ]

@[simp] theorem queriesUB_acceptNoOpkB {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hQ : HooksNoTargetQueries H w) (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (k : Expr O Γ (FinT S.N_id))
    (j : Expr O Γ (FinT S.N_recv)) (l : Expr O Γ (FinT S.N_no_opk))
    (hdr : Expr O Γ hdrT) :
    compQueriesUB w (fun _ => 0) (acceptNoOpkB H nAdv st k j l hdr) = 0 := by
  simp [acceptNoOpkB, queriesUB_koskSenderOkC hQ, queriesUB_acceptKeysC hQ,
    queriesUB_findHonestC hQ, queriesUB_recordRespC hQ]

@[simp] theorem queriesUB_acceptNoOpkBFuel {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hQ : HooksNoTargetQueries H w) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (k : Expr O Γ (FinT S.N_id))
    (j : Expr O Γ (FinT S.N_recv)) (l : Expr O Γ (FinT S.N_no_opk))
    (hdr : Expr O Γ hdrT) :
    compQueriesUB w (fun _ => 0) (acceptNoOpkBFuel H nFuel st k j l hdr) = 0 := by
  simp [acceptNoOpkBFuel, queriesUB_koskSenderOkCFuel hQ, queriesUB_acceptKeysC hQ,
    queriesUB_findHonestCFuel hQ, queriesUB_recordRespCFuel hQ]

@[simp] theorem queriesUB_testB {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (_hQ : HooksNoTargetQueries H w) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (sid : Expr O Γ (sidT S)) :
    compQueriesUB w (fun _ => 0) (testB H st sid) = 0 := by
  simp [testB]

@[simp] theorem queriesUB_testBFuel {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (_hQ : HooksNoTargetQueries H w) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (sid : Expr O Γ (sidT S)) :
    compQueriesUB w (fun _ => 0) (testBFuel H nFuel st sid) = 0 := by
  simp [testBFuel]

@[simp] theorem queriesUB_ro1KeyRealB {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hQ : HooksNoTargetQueries H w) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (sec : Expr O Γ (PB 192)) :
    compQueriesUB w (fun _ => 0) (ro1KeyRealB H st sec) = 0 := by
  simp [ro1KeyRealB, hQ.callPrim_q]

@[simp] theorem queriesUB_revealDh1KeyRealB (w : I.Tag → ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) :
    compQueriesUB w (fun _ => 0) (revealDh1KeyRealB (O := O) (I := I) st) = 0 := by
  simp [revealDh1KeyRealB]

@[simp] theorem queriesUB_revealB {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (_hQ : HooksNoTargetQueries H w) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (sid : Expr O Γ (sidT S)) :
    compQueriesUB w (fun _ => 0) (revealB H st sid) = 0 := by
  simp [revealB]

@[simp] theorem queriesUB_revealBFuel {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (_hQ : HooksNoTargetQueries H w) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (sid : Expr O Γ (sidT S)) :
    compQueriesUB w (fun _ => 0) (revealBFuel H nFuel st sid) = 0 := by
  simp [revealBFuel]

@[simp] theorem queriesUB_registerB {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hQ : HooksNoTargetQueries H w) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (sk : Expr O Γ (PB 32)) :
    compQueriesUB w (fun _ => 0) (registerB H st sk) = 0 := by
  simp [registerB, hQ.callPrim_q]

@[simp] theorem queriesUB_revealSpkB {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (_hQ : HooksNoTargetQueries H w) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (u : Expr O Γ (FinT S.N_id))
    (j : Expr O Γ (FinT S.N_recv)) :
    compQueriesUB w (fun _ => 0) (revealSpkB H st u j) = 0 := by
  simp [revealSpkB]

@[simp] theorem queriesUB_revealSpkBFuel {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (_hQ : HooksNoTargetQueries H w) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) (u : Expr O Γ (FinT S.N_id))
    (j : Expr O Γ (FinT S.N_recv)) :
    compQueriesUB w (fun _ => 0) (revealSpkBFuel H nFuel st u j) = 0 := by
  simp [revealSpkBFuel]

end BranchZeroQueries

end Computational.Proofs.E2E.Dsl.PqxdhSimBranches
