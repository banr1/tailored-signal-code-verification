/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.PqxdhSimBranches
public import Computational.Proofs.E2E.Dsl.M2Interfaces

/-!
# 14-Branch ReductionDsl Simulator for One-Key Real PQXDH

Assembles the 14 per-branch `ReductionDsl` handlers from `PqxdhSimBranches.lean` into a unified
query dispatcher (`pqxdh1KeyRealStepC`) with its fuel-clamped and standalone sub-step variants.
Proves zero target queries, linear step-cost bounds, and `Comp.eval` equivalence with
`SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P` to instantiate `PqxdhSimIface`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.PqxdhSim

open Classical
open OracleSpec OracleComp

open ReductionDsl (Ty Ops Samplers Var Expr Comp Iface Env UniformSamplerTag bits)
open CryptoVerification.E2E.Costed (E2EUnifBase E2EPureOp E2ECryptoOp e2eSig e2eSamplers
  e2ePureOps e2eCryptoOps e2eOps PB PU32 FinT drKeyT bundleT bundleOfV hdrT hdrOfV
  sidT sidOfV keyIndQT keyIndQenc keyIndRT keyIndRenc)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp e2eCryptoOp
  bundleOfV_bundleV hdrOfV_hdrV sidOfV_sidV)
open Computational.Proofs.GameHop.ReductionDsl.CostUB (exprCostUB compCostUB compQueriesUB
  exprCost_le_costUB compCost_le_costUB compQueries_le_queriesUB)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (Ext v env_get_zero env_get_succ
  eLet eCaseOpt eCaseSum eFind eAny eMap bindV letV caseOptV findMV anyMV
  e2eProbIface e2eProbIface_liftP stepAIface E2EPqxdhHooks HooksNoTargetQueries
  mkStepAPqxdhHooks mkStepAPqxdhHooks_noQueries
  e2ePrincipalEntryTy e2eSpkBundleEntryTy e2eOpkEntryTy e2eInitiatorEntryTy e2eRespEntryTy
  e2eKeyIndStateTy e2eKeyIndStateToVal KeyIndSetupBounded stListBounded
  pqxdhKeyIndImpl1KeyReal_testSession_preserves_stListBounded
  pqxdhKeyIndImpl1KeyReal_revealSpkSk_preserves_stListBounded
  orE isSomeE isNoneE optMapE nat2EqE nat3EqE nat4EqE
  finValE sidKeyE sidEqE optEqByE optPu32EqE optPb32EqE
  peSec0 peIkPk peSecSign peSignPk peCorr peSetCorrE
  beSpkSk beSpkPk beSpkSig bePqSk bePqPk bePqSig beRev beSetRevE
  oeSk oePk oeCons oeSetConsE
  bndIkB bndSpkId bndSpkB bndSpkSig bndOpkB bndPqId bndPqB bndPqSig
  hdrIkA hdrEkA hdrSpkId hdrOpkId hdrPqId hdrKemCt
  ieSid ieHonPeer iePeerIk iePeerSpk iePeerOpk iePeerPq ieSpkHon ieOpkHon iePqHon
  ieEkSk ieFresh ieReal ieRand ieHdr ieTested ieRev ieSetTestedE ieSetRevE ieSetRandE
  reSid reIk reSpk reOpk rePq reHdr reSendHon reReal reRand reTested reRev
  reSetTestedE reSetRevE reSetRandE
  stSecb stPrin stSpk stOpk stSess stResp stUsedOpk stUsedNoOpk stSeen stRo stAdv
  setPrinE setSpkE setOpkE setSessE setRespE setAdvE setAcceptOpkE setAcceptNoOpkE
  rNoneE rInitPrinE rPkE rCorrE rBundleE rHdrE rInitUnfreshE rAcceptFreshE rDrKeyE rSpkSkE rsE
  encECWideE encKEME zero32E dhNonZeroE dhOptNonZeroE buildSecretsE
  checkSeenE checkSeenEFuel isTestableE isTestableEFuel
  sBytes32C sRandom64C sDrKey96C sKemKeyGenC
  findHonestC findHonestCFuel isAdvRegC isGameSpkC isGameSpkCFuel isGameOpkC isGameOpkCFuel
  koskBundleOkC koskBundleOkCFuel koskSenderOkC koskSenderOkCFuel
  resolveSigPkC resolveSigPkCFuel honestPeerC honestPeerCFuel checkProvC checkProvCFuel optPow8C
  partnerC partnerRandKeyC partnerRandKeyCFuel recordRespC recordRespCFuel
  accIkSk accSpkSk accOpkSk accPqSk accTp accRp accHdr
  acceptKeysC)
open Computational.Proofs.E2E.Dsl.PqxdhSimBranches (natEqE
  initPrin1KeyB initPrin1KeyBFuel corruptB corruptBFuel
  genSpkB genSpkBFuel genOpkB genOpkBFuel
  initiateC initiateCFuel initiateOpkB initiateOpkBFuel initiateNoOpkB initiateNoOpkBFuel
  acceptOpkB acceptOpkBFuel acceptNoOpkB acceptNoOpkBFuel
  testB testBFuel ro1KeyRealB revealDh1KeyRealB revealB revealBFuel registerB
  revealSpkB revealSpkBFuel
  eval_initPrin1KeyB eval_initPrin1KeyBFuel eval_corruptB eval_corruptBFuel
  eval_genSpkB eval_genSpkBFuel eval_genOpkB eval_genOpkBFuel
  eval_initiateOpkB eval_initiateOpkBFuel eval_initiateNoOpkB eval_initiateNoOpkBFuel
  eval_acceptOpkB eval_acceptOpkBFuel eval_acceptNoOpkB eval_acceptNoOpkBFuel
  eval_testB eval_testBFuel eval_ro1KeyRealB eval_revealDh1KeyRealB
  eval_revealB eval_revealBFuel eval_registerB eval_revealSpkB eval_revealSpkBFuel
  queriesUB_initPrin1KeyB queriesUB_initPrin1KeyBFuel
  queriesUB_corruptB queriesUB_corruptBFuel
  queriesUB_genSpkB queriesUB_genSpkBFuel
  queriesUB_genOpkB queriesUB_genOpkBFuel
  queriesUB_initiateOpkB queriesUB_initiateOpkBFuel
  queriesUB_initiateNoOpkB queriesUB_initiateNoOpkBFuel
  queriesUB_acceptOpkB queriesUB_acceptOpkBFuel
  queriesUB_acceptNoOpkB queriesUB_acceptNoOpkBFuel
  queriesUB_testB queriesUB_testBFuel
  queriesUB_ro1KeyRealB queriesUB_revealDh1KeyRealB
  queriesUB_revealB queriesUB_revealBFuel
  queriesUB_registerB queriesUB_revealSpkB queriesUB_revealSpkBFuel)
open Computational.Proofs.E2E.Dsl.M2Interfaces (PqxdhSimIface)
open CryptoGames.LibsignalSession (Crypto PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open SignalPqxdh (Bytes Setup SessionId Primitives WellFormedPrimitivesδ
  KeyIndQuery KeyIndResponse KeyIndState F_X25519 pqxdhKeyIndImpl1KeyReal)

/-! ## 14-Way Dispatcher and Step Program -/

section Dispatcher

variable {ℓ : ℕ} {S : Setup} {O : Ops (e2eSig ℓ)} {ι : Type} {T : OracleSpec ι}
  {I : Iface (e2eSig ℓ) T}

def pqxdh1KeyRealBodyG (H : E2EPqxdhHooks ℓ O I) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (st0 : Var Γ (e2eKeyIndStateTy ℓ S))
    (qE : Expr O Γ (keyIndQT S)) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  .caseSum qE
    (initPrin1KeyB H st0.succ (.var .zero))
    (let st1 := st0.succ
     .caseSum (.var .zero)
       (corruptB H st1.succ (.var .zero))
       (let st2 := st1.succ
        .caseSum (.var .zero)
          (genSpkB H st2.succ (.fst (.var .zero)) (.snd (.var .zero)))
          (let st3 := st2.succ
           .caseSum (.var .zero)
             (genOpkB H st3.succ (.fst (.var .zero)) (.fst (.snd (.var .zero)))
               (.snd (.snd (.var .zero))))
             (let st4 := st3.succ
              .caseSum (.var .zero)
                (initiateOpkB H nAdv st4.succ (.fst (.var .zero))
                  (.fst (.snd (.var .zero))) (.snd (.snd (.var .zero))))
                (let st5 := st4.succ
                 .caseSum (.var .zero)
                   (initiateNoOpkB H nAdv st5.succ (.fst (.var .zero))
                     (.fst (.snd (.var .zero))) (.snd (.snd (.var .zero))))
                   (let st6 := st5.succ
                    .caseSum (.var .zero)
                      (acceptOpkB H nAdv st6.succ (.fst (.var .zero))
                        (.fst (.snd (.var .zero)))
                        (.fst (.snd (.snd (.var .zero))))
                        (.snd (.snd (.snd (.var .zero)))))
                      (let st7 := st6.succ
                       .caseSum (.var .zero)
                         (acceptNoOpkB H nAdv st7.succ (.fst (.var .zero))
                           (.fst (.snd (.var .zero)))
                           (.fst (.snd (.snd (.var .zero))))
                           (.snd (.snd (.snd (.var .zero)))))
                         (let st8 := st7.succ
                          .caseSum (.var .zero)
                            (testB H st8.succ (.var .zero))
                            (let st9 := st8.succ
                             .caseSum (.var .zero)
                               (ro1KeyRealB H st9.succ (.var .zero))
                               (let st10 := st9.succ
                                .caseSum (.var .zero)
                                  (revealDh1KeyRealB st10.succ)
                                  (let st11 := st10.succ
                                   .caseSum (.var .zero)
                                     (revealB H st11.succ (.var .zero))
                                     (let st12 := st11.succ
                                      .caseSum (.var .zero)
                                        (registerB H st12.succ (.var .zero))
                                        (revealSpkB H st12.succ (.fst (.var .zero))
                                          (.snd (.var .zero)))))))))))))))

def pqxdh1KeyRealStepG (H : E2EPqxdhHooks ℓ O I) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (qE : Expr O Γ (keyIndQT S)) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  .bind (.ret (.pair stE qE))
    (.bind (.ret (.fst (.var .zero)))
      (pqxdh1KeyRealBodyG H nAdv .zero (.snd (.var (.succ .zero)))))

end Dispatcher

/-- Concrete `ReductionDsl` handler simulating one `pqxdhKeyIndImpl1KeyReal S P` query over
`e2eOps` and `stepAIface`. -/
@[local irreducible] def pqxdh1KeyRealStepC (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S)) :
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) Γ
      (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  pqxdh1KeyRealStepG (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv stE qE

/-- Closed-form linear `Comp.cost` budget for one `pqxdh1KeyRealStepC` query. -/
def pqxdh1KeyRealStepCost (S : Setup) (nAdv : ℕ) : ℕ :=
  600 * S.N_id + 3500 * S.N_spk_tot + 300 * S.N_opk_tot +
    7100 * S.N_send_tot + 7200 * S.N_recv_tot + 300 * nAdv + 12200

/-! ## Zero-Target-Query Proofs -/

private theorem queriesUB_caseSum_zero {Sig : ReductionDsl.Sig} {O : Ops Sig}
    {ι : Type} {T : OracleSpec ι} {I : Iface Sig T}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    {Γ : List (Ty Sig)} {α β υ : Ty Sig}
    (e : Expr O Γ (.sum α β)) (l : Comp O I (α :: Γ) υ) (r : Comp O I (β :: Γ) υ)
    (hl : compQueriesUB w ws l = 0) (hr : compQueriesUB w ws r = 0) :
    compQueriesUB w ws (.caseSum e l r) = 0 := by
  simp only [compQueriesUB, hl, hr]

theorem queriesUB_pqxdh1KeyRealBodyG {ℓ : ℕ} {S : Setup} {O : Ops (e2eSig ℓ)}
    {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hQ : HooksNoTargetQueries H w) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (st0 : Var Γ (e2eKeyIndStateTy ℓ S)) (qE : Expr O Γ (keyIndQT S)) :
    compQueriesUB w (fun _ => 0) (pqxdh1KeyRealBodyG H nAdv st0 qE) = 0 := by
  unfold pqxdh1KeyRealBodyG
  exact
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_initPrin1KeyB hQ _ _) <|
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_corruptB hQ _ _) <|
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_genSpkB hQ _ _ _) <|
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_genOpkB hQ _ _ _ _) <|
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_initiateOpkB hQ nAdv _ _ _ _) <|
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_initiateNoOpkB hQ nAdv _ _ _ _) <|
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_acceptOpkB hQ nAdv _ _ _ _ _) <|
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_acceptNoOpkB hQ nAdv _ _ _ _ _) <|
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_testB hQ _ _) <|
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_ro1KeyRealB hQ _ _) <|
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_revealDh1KeyRealB w _) <|
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_revealB hQ _ _) <|
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_registerB hQ _ _)
      (queriesUB_revealSpkB hQ _ _ _)

theorem queriesUB_pqxdh1KeyRealStepG {ℓ : ℕ} {S : Setup} {O : Ops (e2eSig ℓ)}
    {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hQ : HooksNoTargetQueries H w) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr O Γ (e2eKeyIndStateTy ℓ S)) (qE : Expr O Γ (keyIndQT S)) :
    compQueriesUB w (fun _ => 0) (pqxdh1KeyRealStepG H nAdv stE qE) = 0 := by
  simp only [pqxdh1KeyRealStepG, compQueriesUB, queriesUB_pqxdh1KeyRealBodyG hQ]

@[simp] theorem pqxdh1KeyRealStepC_queries (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S))
    (w : (stepAIface ℓ I₀).Tag → ℕ) :
    (pqxdh1KeyRealStepC ℓ S P C K decT encT I₀ nAdv stE qE).queries w (fun _ => 0) = 0 := by
  unfold pqxdh1KeyRealStepC
  exact Nat.eq_zero_of_le_zero
    ((compQueries_le_queriesUB w (fun _ => 0) _).trans_eq
      (queriesUB_pqxdh1KeyRealStepG (mkStepAPqxdhHooks_noQueries ℓ P C K decT encT I₀ w)
        nAdv stE qE))

/-! ## Modular Static Cost Upper Bounds -/

section CostBounds

variable {ℓ : ℕ} {S : Setup} {Pt : Type} {P : Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
  {ι : Type} {T : OracleSpec ι} {I₀ : Iface (e2eSig ℓ) T} {nAdv : ℕ}

/-! ### Op, Sampler, Projection, and Response Cost Identities -/

@[local dsl_cost] private theorem bits_1568 : bits 1568 = 11 := by
  have h : Nat.log 2 1568 = 10 := (Nat.log_eq_iff (by omega)).mpr ⟨by omega, by omega⟩
  simp [bits, h]

@[local dsl_cost] private theorem length_F_X25519 : F_X25519.length = 32 := by
  simp [F_X25519]

attribute [local dsl_cost] PNat.val_ofNat List.length_replicate

@[local dsl_cost] private theorem pnat_val_one : (1 : PNat).val = 1 := rfl

@[local dsl_cost] private theorem pnat_add_val (a b : PNat) : (a + b).val = a.val + b.val := rfl

@[local dsl_cost] private theorem cost_sampBv256 :
    (e2eSamplers ℓ).sCost (UniformSamplerTag.base E2EUnifBase.bv256) = 1 := rfl

@[local dsl_cost] private theorem cost_x25519 : E2ECryptoOp.cost ℓ .x25519 = 8 := rfl
@[local dsl_cost] private theorem cost_x25519Base : E2ECryptoOp.cost ℓ .x25519Base = 8 := rfl
@[local dsl_cost] private theorem cost_pow8 : E2ECryptoOp.cost ℓ .pow8 = 8 := rfl
@[local dsl_cost] private theorem cost_isCanonical : E2ECryptoOp.cost ℓ .isCanonical = 2 := rfl
@[local dsl_cost] private theorem cost_sigSign : E2ECryptoOp.cost ℓ .sigSign = 60 := rfl
@[local dsl_cost] private theorem cost_sigVerify : E2ECryptoOp.cost ℓ .sigVerify = 60 := rfl
@[local dsl_cost] private theorem cost_kemKeyGen : E2ECryptoOp.cost ℓ .kemKeyGen = 160 := rfl
@[local dsl_cost] private theorem cost_kemEncaps : E2ECryptoOp.cost ℓ .kemEncaps = 160 := rfl
@[local dsl_cost] private theorem cost_kemDecaps : E2ECryptoOp.cost ℓ .kemDecaps = 160 := rfl
@[local dsl_cost] private theorem cost_hkdfDerive96 : E2ECryptoOp.cost ℓ .hkdfDerive96 = 16 := rfl

@[local dsl_cost] private theorem cost_pu32OfNat : E2EPureOp.cost ℓ .pu32OfNat = 1 := rfl
@[local dsl_cost] private theorem cost_pu32Eq : E2EPureOp.cost ℓ .pu32Eq = 1 := rfl
@[local dsl_cost] private theorem cost_finVal (n : ℕ) : E2EPureOp.cost ℓ (.finVal n) = 1 := rfl
@[local dsl_cost] private theorem cost_bv256ToPbytes32 :
    E2EPureOp.cost ℓ .bv256ToPbytes32 = 32 := rfl
@[local dsl_cost] private theorem cost_pbytesCat (m n : PNat) :
    E2EPureOp.cost ℓ (.pbytesCat m n) = m.val + n.val := rfl
@[local dsl_cost] private theorem cost_pbytesEq (m n : PNat) :
    E2EPureOp.cost ℓ (.pbytesEq m n) = m.val + n.val := rfl
@[local dsl_cost] private theorem cost_pbytesWiden (w d : PNat) :
    E2EPureOp.cost ℓ (.pbytesWiden w d) = w.val + d.val := rfl
@[local dsl_cost] private theorem cost_pbytesCons (b : UInt8) (w : PNat) :
    E2EPureOp.cost ℓ (.pbytesCons b w) = w.val + 1 := rfl
@[local dsl_cost] private theorem cost_pbytesLit (w : PNat) (bs : Bytes) :
    E2EPureOp.cost ℓ (.pbytesLit w bs) = w.val + bs.length := rfl
@[local dsl_cost] private theorem cost_pbytesLen (w : PNat) :
    E2EPureOp.cost ℓ (.pbytesLen w) = bits w.val + 1 := rfl

variable {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}

@[local dsl_cost] private theorem ub_peSec0 (e : Expr O Γ e2ePrincipalEntryTy) :
    exprCostUB (peSec0 e) = exprCostUB e + 1 := rfl
@[local dsl_cost] private theorem ub_peIkPk (e : Expr O Γ e2ePrincipalEntryTy) :
    exprCostUB (peIkPk e) = exprCostUB e + 2 := rfl
@[local dsl_cost] private theorem ub_peSecSign (e : Expr O Γ e2ePrincipalEntryTy) :
    exprCostUB (peSecSign e) = exprCostUB e + 3 := rfl
@[local dsl_cost] private theorem ub_peSignPk (e : Expr O Γ e2ePrincipalEntryTy) :
    exprCostUB (peSignPk e) = exprCostUB e + 4 := rfl
@[local dsl_cost] private theorem ub_peCorr (e : Expr O Γ e2ePrincipalEntryTy) :
    exprCostUB (peCorr e) = exprCostUB e + 4 := rfl

@[local dsl_cost] private theorem ub_beSpkSk (e : Expr O Γ e2eSpkBundleEntryTy) :
    exprCostUB (beSpkSk e) = exprCostUB e + 1 := rfl
@[local dsl_cost] private theorem ub_beSpkPk (e : Expr O Γ e2eSpkBundleEntryTy) :
    exprCostUB (beSpkPk e) = exprCostUB e + 2 := rfl
@[local dsl_cost] private theorem ub_beSpkSig (e : Expr O Γ e2eSpkBundleEntryTy) :
    exprCostUB (beSpkSig e) = exprCostUB e + 3 := rfl
@[local dsl_cost] private theorem ub_bePqSk (e : Expr O Γ e2eSpkBundleEntryTy) :
    exprCostUB (bePqSk e) = exprCostUB e + 4 := rfl
@[local dsl_cost] private theorem ub_bePqPk (e : Expr O Γ e2eSpkBundleEntryTy) :
    exprCostUB (bePqPk e) = exprCostUB e + 5 := rfl
@[local dsl_cost] private theorem ub_bePqSig (e : Expr O Γ e2eSpkBundleEntryTy) :
    exprCostUB (bePqSig e) = exprCostUB e + 6 := rfl
@[local dsl_cost] private theorem ub_beRev (e : Expr O Γ e2eSpkBundleEntryTy) :
    exprCostUB (beRev e) = exprCostUB e + 6 := rfl

@[local dsl_cost] private theorem ub_oeSk (e : Expr O Γ e2eOpkEntryTy) :
    exprCostUB (oeSk e) = exprCostUB e + 1 := rfl
@[local dsl_cost] private theorem ub_oePk (e : Expr O Γ e2eOpkEntryTy) :
    exprCostUB (oePk e) = exprCostUB e + 2 := rfl
@[local dsl_cost] private theorem ub_oeCons (e : Expr O Γ e2eOpkEntryTy) :
    exprCostUB (oeCons e) = exprCostUB e + 2 := rfl

@[local dsl_cost] private theorem ub_bndIkB (b : Expr O Γ bundleT) :
    exprCostUB (bndIkB b) = exprCostUB b + 1 := rfl
@[local dsl_cost] private theorem ub_bndSpkId (b : Expr O Γ bundleT) :
    exprCostUB (bndSpkId b) = exprCostUB b + 2 := rfl
@[local dsl_cost] private theorem ub_bndSpkB (b : Expr O Γ bundleT) :
    exprCostUB (bndSpkB b) = exprCostUB b + 3 := rfl
@[local dsl_cost] private theorem ub_bndSpkSig (b : Expr O Γ bundleT) :
    exprCostUB (bndSpkSig b) = exprCostUB b + 4 := rfl
@[local dsl_cost] private theorem ub_bndOpkB (b : Expr O Γ bundleT) :
    exprCostUB (bndOpkB b) = exprCostUB b + 5 := rfl
@[local dsl_cost] private theorem ub_bndPqId (b : Expr O Γ bundleT) :
    exprCostUB (bndPqId b) = exprCostUB b + 6 := rfl
@[local dsl_cost] private theorem ub_bndPqB (b : Expr O Γ bundleT) :
    exprCostUB (bndPqB b) = exprCostUB b + 7 := rfl
@[local dsl_cost] private theorem ub_bndPqSig (b : Expr O Γ bundleT) :
    exprCostUB (bndPqSig b) = exprCostUB b + 7 := rfl

@[local dsl_cost] private theorem ub_hdrIkA (h : Expr O Γ hdrT) :
    exprCostUB (hdrIkA h) = exprCostUB h + 1 := rfl
@[local dsl_cost] private theorem ub_hdrEkA (h : Expr O Γ hdrT) :
    exprCostUB (hdrEkA h) = exprCostUB h + 2 := rfl
@[local dsl_cost] private theorem ub_hdrSpkId (h : Expr O Γ hdrT) :
    exprCostUB (hdrSpkId h) = exprCostUB h + 3 := rfl
@[local dsl_cost] private theorem ub_hdrOpkId (h : Expr O Γ hdrT) :
    exprCostUB (hdrOpkId h) = exprCostUB h + 4 := rfl
@[local dsl_cost] private theorem ub_hdrPqId (h : Expr O Γ hdrT) :
    exprCostUB (hdrPqId h) = exprCostUB h + 5 := rfl
@[local dsl_cost] private theorem ub_hdrKemCt (h : Expr O Γ hdrT) :
    exprCostUB (hdrKemCt h) = exprCostUB h + 5 := rfl

@[local dsl_cost] private theorem ub_ieSid (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    exprCostUB (ieSid e) = exprCostUB e + 1 := rfl
@[local dsl_cost] private theorem ub_ieHonPeer (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    exprCostUB (ieHonPeer e) = exprCostUB e + 2 := rfl
@[local dsl_cost] private theorem ub_iePeerIk (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    exprCostUB (iePeerIk e) = exprCostUB e + 3 := rfl
@[local dsl_cost] private theorem ub_iePeerSpk (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    exprCostUB (iePeerSpk e) = exprCostUB e + 4 := rfl
@[local dsl_cost] private theorem ub_iePeerOpk (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    exprCostUB (iePeerOpk e) = exprCostUB e + 5 := rfl
@[local dsl_cost] private theorem ub_iePeerPq (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    exprCostUB (iePeerPq e) = exprCostUB e + 6 := rfl
@[local dsl_cost] private theorem ub_ieSpkHon (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    exprCostUB (ieSpkHon e) = exprCostUB e + 7 := rfl
@[local dsl_cost] private theorem ub_ieOpkHon (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    exprCostUB (ieOpkHon e) = exprCostUB e + 8 := rfl
@[local dsl_cost] private theorem ub_iePqHon (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    exprCostUB (iePqHon e) = exprCostUB e + 9 := rfl
@[local dsl_cost] private theorem ub_ieEkSk (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    exprCostUB (ieEkSk e) = exprCostUB e + 10 := rfl
@[local dsl_cost] private theorem ub_ieFresh (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    exprCostUB (ieFresh e) = exprCostUB e + 11 := rfl
@[local dsl_cost] private theorem ub_ieReal (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    exprCostUB (ieReal e) = exprCostUB e + 12 := rfl
@[local dsl_cost] private theorem ub_ieRand (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    exprCostUB (ieRand e) = exprCostUB e + 13 := rfl
@[local dsl_cost] private theorem ub_ieHdr (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    exprCostUB (ieHdr e) = exprCostUB e + 14 := rfl
@[local dsl_cost] private theorem ub_ieTested (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    exprCostUB (ieTested e) = exprCostUB e + 15 := rfl
@[local dsl_cost] private theorem ub_ieRev (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    exprCostUB (ieRev e) = exprCostUB e + 15 := rfl

@[local dsl_cost] private theorem ub_reSid (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    exprCostUB (reSid e) = exprCostUB e + 1 := rfl
@[local dsl_cost] private theorem ub_reIk (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    exprCostUB (reIk e) = exprCostUB e + 2 := rfl
@[local dsl_cost] private theorem ub_reSpk (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    exprCostUB (reSpk e) = exprCostUB e + 3 := rfl
@[local dsl_cost] private theorem ub_reOpk (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    exprCostUB (reOpk e) = exprCostUB e + 4 := rfl
@[local dsl_cost] private theorem ub_rePq (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    exprCostUB (rePq e) = exprCostUB e + 5 := rfl
@[local dsl_cost] private theorem ub_reHdr (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    exprCostUB (reHdr e) = exprCostUB e + 6 := rfl
@[local dsl_cost] private theorem ub_reSendHon (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    exprCostUB (reSendHon e) = exprCostUB e + 7 := rfl
@[local dsl_cost] private theorem ub_reReal (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    exprCostUB (reReal e) = exprCostUB e + 8 := rfl
@[local dsl_cost] private theorem ub_reRand (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    exprCostUB (reRand e) = exprCostUB e + 9 := rfl
@[local dsl_cost] private theorem ub_reTested (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    exprCostUB (reTested e) = exprCostUB e + 10 := rfl
@[local dsl_cost] private theorem ub_reRev (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    exprCostUB (reRev e) = exprCostUB e + 10 := rfl

@[local dsl_cost] private theorem ub_stSecb (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    exprCostUB (stSecb st) = exprCostUB st + 1 := rfl
@[local dsl_cost] private theorem ub_stPrin (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    exprCostUB (stPrin st) = exprCostUB st + 2 := rfl
@[local dsl_cost] private theorem ub_stSpk (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    exprCostUB (stSpk st) = exprCostUB st + 3 := rfl
@[local dsl_cost] private theorem ub_stOpk (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    exprCostUB (stOpk st) = exprCostUB st + 4 := rfl
@[local dsl_cost] private theorem ub_stSess (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    exprCostUB (stSess st) = exprCostUB st + 5 := rfl
@[local dsl_cost] private theorem ub_stResp (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    exprCostUB (stResp st) = exprCostUB st + 6 := rfl
@[local dsl_cost] private theorem ub_stUsedOpk (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    exprCostUB (stUsedOpk st) = exprCostUB st + 7 := rfl
@[local dsl_cost] private theorem ub_stUsedNoOpk (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    exprCostUB (stUsedNoOpk st) = exprCostUB st + 8 := rfl
@[local dsl_cost] private theorem ub_stSeen (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    exprCostUB (stSeen st) = exprCostUB st + 9 := rfl
@[local dsl_cost] private theorem ub_stRo (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    exprCostUB (stRo st) = exprCostUB st + 10 := rfl
@[local dsl_cost] private theorem ub_stAdv (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    exprCostUB (stAdv st) = exprCostUB st + 10 := rfl

@[local dsl_cost] private theorem ub_accIkSk (e : Expr O Γ (PqxdhSimTypes.accInpTy ℓ)) :
    exprCostUB (accIkSk e) = exprCostUB e + 1 := rfl
@[local dsl_cost] private theorem ub_accSpkSk (e : Expr O Γ (PqxdhSimTypes.accInpTy ℓ)) :
    exprCostUB (accSpkSk e) = exprCostUB e + 2 := rfl
@[local dsl_cost] private theorem ub_accOpkSk (e : Expr O Γ (PqxdhSimTypes.accInpTy ℓ)) :
    exprCostUB (accOpkSk e) = exprCostUB e + 3 := rfl
@[local dsl_cost] private theorem ub_accPqSk (e : Expr O Γ (PqxdhSimTypes.accInpTy ℓ)) :
    exprCostUB (accPqSk e) = exprCostUB e + 4 := rfl
@[local dsl_cost] private theorem ub_accTp (e : Expr O Γ (PqxdhSimTypes.accInpTy ℓ)) :
    exprCostUB (accTp e) = exprCostUB e + 5 := rfl
@[local dsl_cost] private theorem ub_accRp (e : Expr O Γ (PqxdhSimTypes.accInpTy ℓ)) :
    exprCostUB (accRp e) = exprCostUB e + 6 := rfl
@[local dsl_cost] private theorem ub_accHdr (e : Expr O Γ (PqxdhSimTypes.accInpTy ℓ)) :
    exprCostUB (accHdr e) = exprCostUB e + 6 := rfl

@[local dsl_cost] private theorem ub_rNoneE :
    exprCostUB (rNoneE (O := O) (Γ := Γ)) = 2 := rfl
@[local dsl_cost] private theorem ub_rInitPrinE (ik s : Expr O Γ (PB 32)) :
    exprCostUB (rInitPrinE ik s) = exprCostUB ik + exprCostUB s + 3 := rfl
@[local dsl_cost] private theorem ub_rPkE (pk : Expr O Γ (PB 32)) :
    exprCostUB (rPkE pk) = exprCostUB pk + 3 := rfl
@[local dsl_cost] private theorem ub_rCorrE (ik s : Expr O Γ (PB 32)) :
    exprCostUB (rCorrE ik s) = exprCostUB ik + exprCostUB s + 5 := rfl
@[local dsl_cost] private theorem ub_rBundleE (b : Expr O Γ bundleT) :
    exprCostUB (rBundleE b) = exprCostUB b + 5 := rfl
@[local dsl_cost] private theorem ub_rHdrE (h : Expr O Γ hdrT) :
    exprCostUB (rHdrE h) = exprCostUB h + 6 := rfl
@[local dsl_cost] private theorem ub_rInitUnfreshE (dk : Expr O Γ drKeyT) (h : Expr O Γ hdrT) :
    exprCostUB (rInitUnfreshE dk h) = exprCostUB dk + exprCostUB h + 8 := rfl
@[local dsl_cost] private theorem ub_rAcceptFreshE :
    exprCostUB (rAcceptFreshE (O := O) (Γ := Γ)) = 9 := rfl
@[local dsl_cost] private theorem ub_rDrKeyE (dk : Expr O Γ drKeyT) :
    exprCostUB (rDrKeyE dk) = exprCostUB dk + 9 := rfl
@[local dsl_cost] private theorem ub_rSpkSkE (sk : Expr O Γ (PB 32)) :
    exprCostUB (rSpkSkE sk) = exprCostUB sk + 10 := rfl
@[local dsl_cost] private theorem ub_rsE (r : Expr O Γ keyIndRT)
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    exprCostUB (rsE r st) = exprCostUB r + exprCostUB st + 1 := rfl

@[local dsl_cost] private theorem exprCostUB_orE (a b : Expr O Γ .bool) :
    exprCostUB (orE a b) = exprCostUB a + exprCostUB b + 4 := by
  simp only [orE, dsl_cost]; omega

@[local dsl_cost] private theorem exprCostUB_isSomeE {τ : Ty (e2eSig ℓ)} (e : Expr O Γ (.opt τ)) :
    exprCostUB (isSomeE e) = exprCostUB e + 3 := rfl

@[local dsl_cost] private theorem exprCostUB_isNoneE {τ : Ty (e2eSig ℓ)} (e : Expr O Γ (.opt τ)) :
    exprCostUB (isNoneE e) = exprCostUB e + 3 := rfl

@[local dsl_cost] private theorem exprCostUB_optMapE {τ υ : Ty (e2eSig ℓ)} (e : Expr O Γ (.opt τ))
    (f : Var (τ :: Γ) τ → Expr O (τ :: Γ) υ) :
    exprCostUB (optMapE e f) = exprCostUB e + exprCostUB (f .zero) + 3 := by
  simp only [optMapE, dsl_cost]; omega

@[local dsl_cost] private theorem exprCostUB_natEqE (a b : Expr O Γ .nat) :
    exprCostUB (natEqE a b) = exprCostUB a + exprCostUB b + 1 := rfl

@[local dsl_cost] private theorem exprCostUB_nat2EqE (a b : Expr O Γ (.prod .nat .nat)) :
    exprCostUB (nat2EqE a b) = 2 * exprCostUB a + 2 * exprCostUB b + 7 := by
  simp only [nat2EqE, dsl_cost]; omega

@[local dsl_cost] private theorem exprCostUB_nat3EqE
    (a b : Expr O Γ (.prod .nat (.prod .nat .nat))) :
    exprCostUB (nat3EqE a b) = 3 * exprCostUB a + 3 * exprCostUB b + 15 := by
  simp only [nat3EqE, dsl_cost]; omega

@[local dsl_cost] private theorem exprCostUB_nat4EqE
    (a b : Expr O Γ (.prod .nat (.prod .nat (.prod .nat .nat)))) :
    exprCostUB (nat4EqE a b) = 4 * exprCostUB a + 4 * exprCostUB b + 25 := by
  simp only [nat4EqE, dsl_cost]; omega

@[local dsl_cost] private theorem exprCostUB_peSetCorrE (e : Expr O Γ e2ePrincipalEntryTy) :
    exprCostUB (peSetCorrE e) = exprCostUB e + 20 := by
  simp only [peSetCorrE, dsl_cost]

@[local dsl_cost] private theorem exprCostUB_beSetRevE (e : Expr O Γ e2eSpkBundleEntryTy) :
    exprCostUB (beSetRevE e) = exprCostUB e + 35 := by
  simp only [beSetRevE, dsl_cost]

@[local dsl_cost] private theorem exprCostUB_oeSetConsE (e : Expr O Γ e2eOpkEntryTy) :
    exprCostUB (oeSetConsE e) = exprCostUB e + 9 := by
  simp only [oeSetConsE, dsl_cost]

@[local dsl_cost] private theorem exprCostUB_ieSetTestedE
    (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    exprCostUB (ieSetTestedE e) = exprCostUB e + 152 := by
  simp only [ieSetTestedE, dsl_cost]

@[local dsl_cost] private theorem exprCostUB_ieSetRevE
    (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    exprCostUB (ieSetRevE e) = exprCostUB e + 152 := by
  simp only [ieSetRevE, dsl_cost]

@[local dsl_cost] private theorem exprCostUB_ieSetRandE
    (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) (rk : Expr O Γ drKeyT) :
    exprCostUB (ieSetRandE e rk) = exprCostUB e + exprCostUB rk + 171 := by
  simp only [ieSetRandE, dsl_cost]

@[local dsl_cost] private theorem exprCostUB_reSetTestedE
    (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    exprCostUB (reSetTestedE e) = exprCostUB e + 77 := by
  simp only [reSetTestedE, dsl_cost]

@[local dsl_cost] private theorem exprCostUB_reSetRevE
    (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    exprCostUB (reSetRevE e) = exprCostUB e + 77 := by
  simp only [reSetRevE, dsl_cost]

@[local dsl_cost] private theorem exprCostUB_reSetRandE
    (e : Expr O Γ (e2eRespEntryTy ℓ S)) (rk : Expr O Γ drKeyT) :
    exprCostUB (reSetRandE e rk) = exprCostUB e + exprCostUB rk + 90 := by
  simp only [reSetRandE, dsl_cost]

@[local dsl_cost] private theorem exprCostUB_setPrinE
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (ps : Expr O Γ (.list (.prod .nat e2ePrincipalEntryTy))) :
    exprCostUB (setPrinE st ps) = exprCostUB st + exprCostUB ps + 13 := by
  simp only [setPrinE, dsl_cost]

@[local dsl_cost] private theorem exprCostUB_setSpkE
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (bs : Expr O Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy))) :
    exprCostUB (setSpkE st bs) = exprCostUB st + exprCostUB bs + 19 := by
  simp only [setSpkE, dsl_cost]

@[local dsl_cost] private theorem exprCostUB_setOpkE
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (os : Expr O Γ (.list (.prod (.prod .nat (.prod .nat .nat)) e2eOpkEntryTy))) :
    exprCostUB (setOpkE st os) = exprCostUB st + exprCostUB os + 26 := by
  simp only [setOpkE, dsl_cost]

@[local dsl_cost] private theorem exprCostUB_setSessE
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (ss : Expr O Γ (.list (e2eInitiatorEntryTy ℓ S))) :
    exprCostUB (setSessE st ss) = exprCostUB st + exprCostUB ss + 34 := by
  simp only [setSessE, dsl_cost]

@[local dsl_cost] private theorem exprCostUB_setRespE
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (rs : Expr O Γ (.list (e2eRespEntryTy ℓ S))) :
    exprCostUB (setRespE st rs) = exprCostUB st + exprCostUB rs + 43 := by
  simp only [setRespE, dsl_cost]

@[local dsl_cost] private theorem exprCostUB_setAdvE
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (ak : Expr O Γ (.list (.prod (PB 32) (PB 32)))) :
    exprCostUB (setAdvE st ak) = exprCostUB st + exprCostUB ak + 89 := by
  simp only [setAdvE, dsl_cost]

@[local dsl_cost] private theorem exprCostUB_setAcceptOpkE
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (os : Expr O Γ (.list (.prod (.prod .nat (.prod .nat .nat)) e2eOpkEntryTy)))
    (used : Expr O Γ (.list (.prod .nat (.prod .nat .nat))))
    (seen : Expr O Γ (.list (.prod .nat (.prod PU32 (.prod PU32 (PB 32)))))) :
    exprCostUB (setAcceptOpkE st os used seen) =
      exprCostUB st + exprCostUB os + exprCostUB used + exprCostUB seen + 86 := by
  simp only [setAcceptOpkE, dsl_cost]; omega

@[local dsl_cost] private theorem exprCostUB_setAcceptNoOpkE
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (used : Expr O Γ (.list (.prod .nat (.prod .nat .nat))))
    (seen : Expr O Γ (.list (.prod .nat (.prod PU32 (.prod PU32 (PB 32)))))) :
    exprCostUB (setAcceptNoOpkE st used seen) =
      exprCostUB st + exprCostUB used + exprCostUB seen + 85 := by
  simp only [setAcceptNoOpkE, dsl_cost]; omega

/-! ### Hook-Parameterized Expression and Monadic Helper Cost Identities -/

@[local dsl_cost] private theorem exprCostUB_finValE {Γ : List (Ty (e2eSig ℓ))} {n : ℕ}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (FinT n)) :
    exprCostUB (finValE (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) e) = exprCostUB e + 1 := rfl

@[local dsl_cost] private theorem exprCostUB_sidKeyE {Γ : List (Ty (e2eSig ℓ))}
    (s : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) :
    exprCostUB (sidKeyE (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) s) = exprCostUB s + 59 := by
  simp only [sidKeyE, dsl_cost]

@[local dsl_cost] private theorem exprCostUB_sidEqE {Γ : List (Ty (e2eSig ℓ))}
    (a b : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) :
    exprCostUB (sidEqE (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) a b) =
      4 * exprCostUB a + 4 * exprCostUB b + 497 := by
  simp only [sidEqE, dsl_cost]; omega

@[local dsl_cost] private theorem exprCostUB_optPu32EqE {Γ : List (Ty (e2eSig ℓ))}
    (a b : Expr (e2eOps ℓ P C K decT encT) Γ (.opt PU32)) :
    exprCostUB (optPu32EqE (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) a b) =
      exprCostUB a + exprCostUB b + 18 := by
  simp only [optPu32EqE, optEqByE, dsl_cost]

@[local dsl_cost] private theorem exprCostUB_optPb32EqE {Γ : List (Ty (e2eSig ℓ))}
    (a b : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (PB 32))) :
    exprCostUB (optPb32EqE (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) a b) =
      exprCostUB a + exprCostUB b + 81 := by
  simp only [optPb32EqE, optEqByE, dsl_cost]

@[local dsl_cost] private theorem exprCostUB_encECWideE {Γ : List (Ty (e2eSig ℓ))}
    (pk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    exprCostUB (encECWideE (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) pk) = exprCostUB pk + 1602 := by
  unfold encECWideE mkStepAPqxdhHooks e2ePureOp
  dsimp only [exprCostUB, e2eOps, e2ePureOps, Ops.sum, E2EPureOp.cost]
  change exprCostUB pk + 33 + 1569 = exprCostUB pk + 1602
  omega

@[local dsl_cost] private theorem exprCostUB_encKEME {Γ : List (Ty (e2eSig ℓ))}
    (pk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 1568)) :
    exprCostUB (encKEME (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) pk) = exprCostUB pk + 1569 := by
  unfold encKEME mkStepAPqxdhHooks e2ePureOp
  dsimp only [exprCostUB, e2eOps, e2ePureOps, Ops.sum, E2EPureOp.cost]
  rfl

@[local dsl_cost] private theorem exprCostUB_dhNonZeroE {Γ : List (Ty (e2eSig ℓ))}
    (dh : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    exprCostUB (dhNonZeroE (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) dh) = exprCostUB dh + 131 := by
  unfold dhNonZeroE zero32E
  simp only [dsl_cost]

@[local dsl_cost] private theorem exprCostUB_dhOptNonZeroE {Γ : List (Ty (e2eSig ℓ))}
    (dh4? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (PB 32))) :
    exprCostUB (dhOptNonZeroE (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) dh4?) = exprCostUB dh4? + 134 := by
  unfold dhOptNonZeroE
  simp only [dsl_cost]

@[local dsl_cost] private theorem exprCostUB_buildSecretsE {Γ : List (Ty (e2eSig ℓ))}
    (dh1 dh2 dh3 : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32))
    (dh4? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (PB 32)))
    (ss : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    exprCostUB (buildSecretsE (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) dh1 dh2 dh3 dh4? ss) =
      exprCostUB dh1 + exprCostUB dh2 + exprCostUB dh3 +
        exprCostUB dh4? + exprCostUB ss + 1081 := by
  unfold buildSecretsE eLet eCaseOpt
  dsimp only [exprCostUB, mkStepAPqxdhHooks, e2ePureOp, e2eOps, e2ePureOps, Ops.sum,
    Sum.elim_inl, E2EPureOp.cost, PNat.val_ofNat, pnat_add_val, v]
  simp only [length_F_X25519]
  omega

@[local dsl_cost] private theorem exprCostUB_checkSeenE {Γ : List (Ty (e2eSig ℓ))}
    (used : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod .nat (.prod PU32 (.prod PU32 (PB 32))))))
    (k : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (pqspkId spkId : Expr (e2eOps ℓ P C K decT encT) Γ PU32)
    (ekAPk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    exprCostUB (checkSeenE (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) used k pqspkId spkId ekAPk) =
      exprCostUB used + exprCostUB k + exprCostUB pqspkId +
        exprCostUB spkId + exprCostUB ekAPk + 104 * S.N_recv_tot + 20 := by
  simp only [checkSeenE, dsl_cost]; omega

@[local dsl_cost] private theorem exprCostUB_isTestableE {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (sid : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) :
    exprCostUB (isTestableE (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st sid) =
      exprCostUB st + exprCostUB sid + 514 * S.N_send_tot + 514 * S.N_recv_tot + 104 := by
  simp only [isTestableE, dsl_cost]; omega

@[local dsl_cost] private theorem compCostUB_sBytes32C {Γ : List (Ty (e2eSig ℓ))} :
    compCostUB (sBytes32C (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) (Γ := Γ)) = 37 := rfl

@[local dsl_cost] private theorem compCostUB_sRandom64C {Γ : List (Ty (e2eSig ℓ))} :
    compCostUB (sRandom64C (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) (Γ := Γ)) = 144 := by
  unfold sRandom64C
  simp only [dsl_cost]
  change 37 + (37 + (exprCostUB (t := (E2EPureOp.pbytesCat 32 32).cod ℓ)
    (e2ePureOp (.pbytesCat 32 32) ((v .zero).pair (v .zero))) + 1) + 1) + 1 = 144
  simp only [dsl_cost]

@[local dsl_cost] private theorem compCostUB_sDrKey96C {Γ : List (Ty (e2eSig ℓ))} :
    compCostUB (sDrKey96C (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) (Γ := Γ)) = 120 := by
  unfold sDrKey96C
  simp only [dsl_cost]

@[local dsl_cost] private theorem compCostUB_sKemKeyGenC {Γ : List (Ty (e2eSig ℓ))} :
    compCostUB (sKemKeyGenC (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) (Γ := Γ)) = 307 := by
  unfold sKemKeyGenC
  simp only [dsl_cost]

@[local dsl_cost] private theorem compCostUB_findHonestC {Γ : List (Ty (e2eSig ℓ))}
    (ps : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (ik : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    compCostUB (findHonestC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) ps ik) =
      exprCostUB ps + exprCostUB ik + 83 * S.N_id + 18 := by
  unfold findHonestC
  simp only [dsl_cost]; omega

@[local dsl_cost] private theorem compCostUB_isAdvRegC (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (ak : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod (PB 32) (PB 32))))
    (pk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    compCostUB (isAdvRegC (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv ak pk) =
      exprCostUB ak + exprCostUB pk + 81 * nAdv + 18 := by
  unfold isAdvRegC
  simp only [dsl_cost]; omega

@[local dsl_cost] private theorem compCostUB_isGameSpkC {Γ : List (Ty (e2eSig ℓ))}
    (bs : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)))
    (pk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    compCostUB (isGameSpkC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) bs pk) =
      exprCostUB bs + exprCostUB pk + 83 * S.N_spk_tot + 18 := by
  unfold isGameSpkC
  simp only [dsl_cost]; omega

@[local dsl_cost] private theorem compCostUB_isGameOpkC {Γ : List (Ty (e2eSig ℓ))}
    (os : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod (.prod .nat (.prod .nat .nat)) e2eOpkEntryTy)))
    (pk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    compCostUB (isGameOpkC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) os pk) =
      exprCostUB os + exprCostUB pk + 83 * S.N_opk_tot + 18 := by
  unfold isGameOpkC
  simp only [dsl_cost]; omega

@[local dsl_cost] private theorem compCostUB_koskBundleOkC (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (bundle : Expr (e2eOps ℓ P C K decT encT) Γ bundleT) :
    compCostUB (koskBundleOkC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st bundle) =
      exprCostUB st + exprCostUB bundle +
        83 * S.N_id + 83 * S.N_spk_tot + 83 * S.N_opk_tot + 243 * nAdv + 225 := by
  unfold koskBundleOkC
  simp only [dsl_cost]; omega

@[local dsl_cost] private theorem compCostUB_koskSenderOkC (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (ik : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    compCostUB (koskSenderOkC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st ik) =
      exprCostUB st + exprCostUB ik + 83 * S.N_id + 81 * nAdv + 71 := by
  unfold koskSenderOkC
  simp only [dsl_cost]; omega

@[local dsl_cost] private theorem compCostUB_resolveSigPkC {Γ : List (Ty (e2eSig ℓ))}
    (ps : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (ik : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    compCostUB (resolveSigPkC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) ps ik) =
      exprCostUB ps + exprCostUB ik + 83 * S.N_id + 37 := by
  unfold resolveSigPkC
  simp only [dsl_cost]; omega

@[local dsl_cost] private theorem compCostUB_honestPeerC {Γ : List (Ty (e2eSig ℓ))}
    (ps : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (ik : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    compCostUB (honestPeerC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) ps ik) =
      exprCostUB ps + exprCostUB ik + 83 * S.N_id + 35 := by
  unfold honestPeerC
  simp only [dsl_cost]

@[local dsl_cost] private theorem compCostUB_checkProvC {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (bundle : Expr (e2eOps ℓ P C K decT encT) Γ bundleT) :
    compCostUB (checkProvC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st bundle) =
      exprCostUB st + exprCostUB bundle +
        83 * S.N_id + 3251 * S.N_spk_tot + 90 * S.N_opk_tot + 103 := by
  unfold checkProvC
  simp only [dsl_cost]; omega

@[local dsl_cost] private theorem compCostUB_optPow8C {Γ : List (Ty (e2eSig ℓ))}
    (pk? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (PB 32))) :
    compCostUB (optPow8C (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) pk?) = exprCostUB pk? + 17 := rfl

@[local dsl_cost] private theorem compCostUB_partnerC {Γ : List (Ty (e2eSig ℓ))}
    (s : Expr (e2eOps ℓ P C K decT encT) Γ (e2eInitiatorEntryTy ℓ S))
    (r : Expr (e2eOps ℓ P C K decT encT) Γ (e2eRespEntryTy ℓ S)) :
    compCostUB (partnerC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) s r) =
      exprCostUB s + exprCostUB r + 6865 := by
  unfold partnerC
  simp only [dsl_cost]

@[local dsl_cost] private theorem compCostUB_partnerRandKeyC {Γ : List (Ty (e2eSig ℓ))}
    (rs : Expr (e2eOps ℓ P C K decT encT) Γ (.list (e2eRespEntryTy ℓ S)))
    (s : Expr (e2eOps ℓ P C K decT encT) Γ (e2eInitiatorEntryTy ℓ S)) :
    compCostUB (partnerRandKeyC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) rs s) =
      exprCostUB rs + exprCostUB s + 6869 * S.N_recv_tot + 22 := by
  unfold partnerRandKeyC
  simp only [dsl_cost]; omega

@[local dsl_cost] private theorem compCostUB_recordRespC {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (r : Expr (e2eOps ℓ P C K decT encT) Γ (e2eRespEntryTy ℓ S)) :
    compCostUB (recordRespC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st r) =
      exprCostUB st + exprCostUB r + 6869 * S.N_send_tot + 298 := by
  unfold recordRespC
  simp only [dsl_cost]; omega

@[local dsl_cost] private theorem compCostUB_acceptKeysC {Γ : List (Ty (e2eSig ℓ))}
    (ikBSk spkBSk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32))
    (opkBSk? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (PB 32)))
    (pqspkBSk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 3168))
    (tp rp : Expr (e2eOps ℓ P C K decT encT) Γ .bool)
    (hdr : Expr (e2eOps ℓ P C K decT encT) Γ hdrT) :
    compCostUB (acceptKeysC (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) ikBSk spkBSk opkBSk? pqspkBSk tp rp hdr) =
      exprCostUB ikBSk + exprCostUB spkBSk + exprCostUB opkBSk? +
        exprCostUB pqspkBSk + exprCostUB tp + exprCostUB rp + exprCostUB hdr + 2095 := by
  unfold acceptKeysC
  simp only [dsl_cost]; omega

/-! ### Per-Branch `Comp.cost` Upper Bounds -/

private abbrev armBudget (S : Setup) (nAdv : ℕ) : ℕ :=
  600 * S.N_id + 3500 * S.N_spk_tot + 300 * S.N_opk_tot +
    7100 * S.N_send_tot + 7200 * S.N_recv_tot + 300 * nAdv + 12000

private theorem cost_initPrin1KeyB {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id)) (hu : exprCostUB u ≤ 4) :
    (initPrin1KeyB (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st u).cost ≤ armBudget S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  unfold initPrin1KeyB
  simp only [armBudget, dsl_cost]; omega

private theorem cost_corruptB {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id)) (hu : exprCostUB u ≤ 4) :
    (corruptB (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st u).cost ≤ armBudget S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  unfold corruptB
  simp only [armBudget, dsl_cost]; omega

private theorem cost_genSpkB {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (j : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (hu : exprCostUB u ≤ 4) (hj : exprCostUB j ≤ 4) :
    (genSpkB (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st u j).cost ≤ armBudget S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  unfold genSpkB
  simp only [armBudget, dsl_cost]; omega

private theorem cost_genOpkB {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (j : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (o : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_opk))
    (hu : exprCostUB u ≤ 4) (hj : exprCostUB j ≤ 4) (ho : exprCostUB o ≤ 4) :
    (genOpkB (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st u j o).cost ≤ armBudget S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  unfold genOpkB
  simp only [armBudget, dsl_cost]; omega

private theorem compCostUB_initiateC {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (sid : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (bundle : Expr (e2eOps ℓ P C K decT encT) Γ bundleT)
    (hsid : exprCostUB sid ≤ 12) (hu : exprCostUB u ≤ 4) (hbnd : exprCostUB bundle ≤ 4) :
    compCostUB (initiateC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st sid u bundle) ≤
      600 * S.N_id + 3500 * S.N_spk_tot + 300 * S.N_opk_tot +
        600 * S.N_send_tot + 7000 * S.N_recv_tot + 300 * nAdv + 11500 := by
  unfold initiateC
  simp only [dsl_cost]; omega

private theorem cost_initiateOpkB {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (i : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_send_opk))
    (bundle : Expr (e2eOps ℓ P C K decT encT) Γ bundleT)
    (hu : exprCostUB u ≤ 4) (hi : exprCostUB i ≤ 4) (hbnd : exprCostUB bundle ≤ 4) :
    (initiateOpkB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st u i bundle).cost ≤ armBudget S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  unfold initiateOpkB
  have hinit := compCostUB_initiateC (S := S) (I₀ := I₀) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (nAdv := nAdv)
    st (.inl (.pair u i)) u bundle (by simp only [dsl_cost]; omega) hu hbnd
  simp only [armBudget, dsl_cost]
  omega

private theorem cost_initiateNoOpkB {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (i : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_send_no_opk))
    (bundle : Expr (e2eOps ℓ P C K decT encT) Γ bundleT)
    (hu : exprCostUB u ≤ 4) (hi : exprCostUB i ≤ 4) (hbnd : exprCostUB bundle ≤ 4) :
    (initiateNoOpkB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st u i bundle).cost ≤ armBudget S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  unfold initiateNoOpkB
  have hinit := compCostUB_initiateC (S := S) (I₀ := I₀) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (nAdv := nAdv)
    st (.inr (.inl (.pair u i))) u bundle (by simp only [dsl_cost]; omega) hu hbnd
  simp only [armBudget, dsl_cost]
  omega

private theorem cost_acceptOpkB {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (k : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (j : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (o : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_opk))
    (hdr : Expr (e2eOps ℓ P C K decT encT) Γ hdrT)
    (hk : exprCostUB k ≤ 4) (hj : exprCostUB j ≤ 4) (ho : exprCostUB o ≤ 4)
    (hhdr : exprCostUB hdr ≤ 5) :
    (acceptOpkB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st k j o hdr).cost ≤ armBudget S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  unfold acceptOpkB
  simp only [armBudget, dsl_cost]; omega

private theorem cost_acceptNoOpkB {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (k : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (j : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (l : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_no_opk))
    (hdr : Expr (e2eOps ℓ P C K decT encT) Γ hdrT)
    (hk : exprCostUB k ≤ 4) (hj : exprCostUB j ≤ 4) (hl : exprCostUB l ≤ 4)
    (hhdr : exprCostUB hdr ≤ 5) :
    (acceptNoOpkB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st k j l hdr).cost ≤ armBudget S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  have hno : S.N_no_opk_tot ≤ S.N_recv_tot := by
    unfold Setup.N_recv_tot; omega
  unfold acceptNoOpkB
  simp only [armBudget, dsl_cost]; omega

private theorem cost_testB {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (sid : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) (hsid : exprCostUB sid ≤ 4) :
    (testB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st sid).cost ≤ armBudget S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  unfold testB
  simp only [armBudget, dsl_cost]; omega

private theorem cost_ro1KeyRealB {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (sec : Expr (e2eOps ℓ P C K decT encT) Γ (PB 192)) (hsec : exprCostUB sec ≤ 4) :
    (ro1KeyRealB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st sec).cost ≤ armBudget S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  unfold ro1KeyRealB
  simp only [armBudget, dsl_cost]; omega

private theorem cost_revealDh1KeyRealB {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) :
    (revealDh1KeyRealB (S := S) (O := e2eOps ℓ P C K decT encT)
      (I := stepAIface ℓ I₀) st).cost ≤ armBudget S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  unfold revealDh1KeyRealB
  simp only [armBudget, dsl_cost]; omega

private theorem cost_revealB {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (sid : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) (hsid : exprCostUB sid ≤ 4) :
    (revealB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st sid).cost ≤ armBudget S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  unfold revealB
  simp only [armBudget, dsl_cost]; omega

private theorem cost_registerB {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (sk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) (hsk : exprCostUB sk ≤ 4) :
    (registerB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st sk).cost ≤ armBudget S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  unfold registerB
  simp only [armBudget, dsl_cost]; omega

private theorem cost_revealSpkB {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (j : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (hu : exprCostUB u ≤ 4) (hj : exprCostUB j ≤ 4) :
    (revealSpkB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st u j).cost ≤ armBudget S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  unfold revealSpkB
  simp only [armBudget, dsl_cost]; omega

@[local dsl_cost] private theorem exprCostUB_checkSeenEFuel (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (used : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod .nat (.prod PU32 (.prod PU32 (PB 32))))))
    (k : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (pqspkId spkId : Expr (e2eOps ℓ P C K decT encT) Γ PU32)
    (ekAPk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    exprCostUB (checkSeenEFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel used k pqspkId spkId ekAPk) =
      exprCostUB used + exprCostUB k + exprCostUB pqspkId +
        exprCostUB spkId + exprCostUB ekAPk + 104 * min nFuel S.N_recv_tot + 20 := by
  simp only [checkSeenEFuel, dsl_cost]; omega

@[local dsl_cost] private theorem exprCostUB_isTestableEFuel (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (sid : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) :
    exprCostUB (isTestableEFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel st sid) =
      exprCostUB st + exprCostUB sid +
        514 * min nFuel S.N_send_tot + 514 * min nFuel S.N_recv_tot + 104 := by
  simp only [isTestableEFuel, dsl_cost]; omega

@[local dsl_cost] private theorem compCostUB_findHonestCFuel (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (ps : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (ik : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    compCostUB (findHonestCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel ps ik) =
      exprCostUB ps + exprCostUB ik + 83 * min nFuel S.N_id + 18 := by
  unfold findHonestCFuel
  simp only [dsl_cost]; omega

@[local dsl_cost] private theorem compCostUB_isGameSpkCFuel (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (bs : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)))
    (pk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    compCostUB (isGameSpkCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel bs pk) =
      exprCostUB bs + exprCostUB pk + 83 * min nFuel S.N_spk_tot + 18 := by
  unfold isGameSpkCFuel
  simp only [dsl_cost]; omega

@[local dsl_cost] private theorem compCostUB_isGameOpkCFuel (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (os : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod (.prod .nat (.prod .nat .nat)) e2eOpkEntryTy)))
    (pk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    compCostUB (isGameOpkCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel os pk) =
      exprCostUB os + exprCostUB pk + 83 * min nFuel S.N_opk_tot + 18 := by
  unfold isGameOpkCFuel
  simp only [dsl_cost]; omega

@[local dsl_cost] private theorem compCostUB_koskBundleOkCFuel (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (bundle : Expr (e2eOps ℓ P C K decT encT) Γ bundleT) :
    compCostUB (koskBundleOkCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel st bundle) =
      exprCostUB st + exprCostUB bundle +
        83 * min nFuel S.N_id + 83 * min nFuel S.N_spk_tot + 83 * min nFuel S.N_opk_tot +
        243 * nFuel + 225 := by
  unfold koskBundleOkCFuel
  simp only [dsl_cost]; omega

@[local dsl_cost] private theorem compCostUB_koskSenderOkCFuel (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (ik : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    compCostUB (koskSenderOkCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel st ik) =
      exprCostUB st + exprCostUB ik + 83 * min nFuel S.N_id + 81 * nFuel + 71 := by
  unfold koskSenderOkCFuel
  simp only [dsl_cost]; omega

@[local dsl_cost] private theorem compCostUB_resolveSigPkCFuel (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (ps : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (ik : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    compCostUB (resolveSigPkCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel ps ik) =
      exprCostUB ps + exprCostUB ik + 83 * min nFuel S.N_id + 37 := by
  unfold resolveSigPkCFuel
  simp only [dsl_cost]; omega

@[local dsl_cost] private theorem compCostUB_honestPeerCFuel (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (ps : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (ik : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    compCostUB (honestPeerCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel ps ik) =
      exprCostUB ps + exprCostUB ik + 83 * min nFuel S.N_id + 35 := by
  unfold honestPeerCFuel
  simp only [dsl_cost]

@[local dsl_cost] private theorem compCostUB_checkProvCFuel (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (bundle : Expr (e2eOps ℓ P C K decT encT) Γ bundleT) :
    compCostUB (checkProvCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel st bundle) =
      exprCostUB st + exprCostUB bundle +
        83 * min nFuel S.N_id + 3251 * min nFuel S.N_spk_tot +
        90 * min nFuel S.N_opk_tot + 103 := by
  unfold checkProvCFuel
  simp only [dsl_cost]; omega

@[local dsl_cost] private theorem compCostUB_partnerRandKeyCFuel (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (rs : Expr (e2eOps ℓ P C K decT encT) Γ (.list (e2eRespEntryTy ℓ S)))
    (s : Expr (e2eOps ℓ P C K decT encT) Γ (e2eInitiatorEntryTy ℓ S)) :
    compCostUB (partnerRandKeyCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel rs s) =
      exprCostUB rs + exprCostUB s + 6869 * min nFuel S.N_recv_tot + 22 := by
  unfold partnerRandKeyCFuel
  simp only [dsl_cost]; omega

@[local dsl_cost] private theorem compCostUB_recordRespCFuel (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (r : Expr (e2eOps ℓ P C K decT encT) Γ (e2eRespEntryTy ℓ S)) :
    compCostUB (recordRespCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel st r) =
      exprCostUB st + exprCostUB r + 6869 * min nFuel S.N_send_tot + 298 := by
  unfold recordRespCFuel
  simp only [dsl_cost]; omega

private abbrev armBudgetClamped (S : Setup) (nAdv : ℕ) : ℕ :=
  600 * min nAdv S.N_id + 3500 * min nAdv S.N_spk_tot + 300 * min nAdv S.N_opk_tot +
    7100 * min nAdv S.N_send_tot + 7200 * min nAdv S.N_recv_tot + 300 * nAdv + 12000

private theorem cost_initPrin1KeyBFuel {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id)) (hu : exprCostUB u ≤ 4) :
    (initPrin1KeyBFuel (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st u).cost ≤ armBudgetClamped S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  unfold initPrin1KeyBFuel
  simp only [armBudgetClamped, dsl_cost]; omega

private theorem cost_corruptBFuel {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id)) (hu : exprCostUB u ≤ 4) :
    (corruptBFuel (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st u).cost ≤ armBudgetClamped S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  unfold corruptBFuel
  simp only [armBudgetClamped, dsl_cost]; omega

private theorem cost_genSpkBFuel {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (j : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (hu : exprCostUB u ≤ 4) (hj : exprCostUB j ≤ 4) :
    (genSpkBFuel (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st u j).cost ≤ armBudgetClamped S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  unfold genSpkBFuel
  simp only [armBudgetClamped, dsl_cost]; omega

private theorem cost_genOpkBFuel {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (j : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (o : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_opk))
    (hu : exprCostUB u ≤ 4) (hj : exprCostUB j ≤ 4) (ho : exprCostUB o ≤ 4) :
    (genOpkBFuel (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st u j o).cost ≤ armBudgetClamped S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  unfold genOpkBFuel
  simp only [armBudgetClamped, dsl_cost]; omega

private theorem compCostUB_initiateCFuel {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (sid : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (bundle : Expr (e2eOps ℓ P C K decT encT) Γ bundleT)
    (hsid : exprCostUB sid ≤ 12) (hu : exprCostUB u ≤ 4) (hbnd : exprCostUB bundle ≤ 4) :
    compCostUB (initiateCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st sid u bundle) ≤
      600 * min nAdv S.N_id + 3500 * min nAdv S.N_spk_tot + 300 * min nAdv S.N_opk_tot +
        600 * min nAdv S.N_send_tot + 7000 * min nAdv S.N_recv_tot + 300 * nAdv + 11500 := by
  unfold initiateCFuel
  simp only [dsl_cost]; omega

private theorem cost_initiateOpkBFuel {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (i : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_send_opk))
    (bundle : Expr (e2eOps ℓ P C K decT encT) Γ bundleT)
    (hu : exprCostUB u ≤ 4) (hi : exprCostUB i ≤ 4) (hbnd : exprCostUB bundle ≤ 4) :
    (initiateOpkBFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st u i bundle).cost ≤ armBudgetClamped S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  unfold initiateOpkBFuel
  have hinit := compCostUB_initiateCFuel (S := S) (I₀ := I₀) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (nAdv := nAdv)
    st (.inl (.pair u i)) u bundle (by simp only [dsl_cost]; omega) hu hbnd
  simp only [armBudgetClamped, dsl_cost]
  omega

private theorem cost_initiateNoOpkBFuel {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (i : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_send_no_opk))
    (bundle : Expr (e2eOps ℓ P C K decT encT) Γ bundleT)
    (hu : exprCostUB u ≤ 4) (hi : exprCostUB i ≤ 4) (hbnd : exprCostUB bundle ≤ 4) :
    (initiateNoOpkBFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st u i bundle).cost ≤ armBudgetClamped S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  unfold initiateNoOpkBFuel
  have hinit := compCostUB_initiateCFuel (S := S) (I₀ := I₀) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (nAdv := nAdv)
    st (.inr (.inl (.pair u i))) u bundle (by simp only [dsl_cost]; omega) hu hbnd
  simp only [armBudgetClamped, dsl_cost]
  omega

private theorem cost_acceptOpkBFuel {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (k : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (j : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (o : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_opk))
    (hdr : Expr (e2eOps ℓ P C K decT encT) Γ hdrT)
    (hk : exprCostUB k ≤ 4) (hj : exprCostUB j ≤ 4) (ho : exprCostUB o ≤ 4)
    (hhdr : exprCostUB hdr ≤ 5) :
    (acceptOpkBFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st k j o hdr).cost ≤ armBudgetClamped S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  unfold acceptOpkBFuel
  simp only [armBudgetClamped, dsl_cost]; omega

private theorem cost_acceptNoOpkBFuel {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (k : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (j : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (l : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_no_opk))
    (hdr : Expr (e2eOps ℓ P C K decT encT) Γ hdrT)
    (hk : exprCostUB k ≤ 4) (hj : exprCostUB j ≤ 4) (hl : exprCostUB l ≤ 4)
    (hhdr : exprCostUB hdr ≤ 5) :
    (acceptNoOpkBFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st k j l hdr).cost ≤ armBudgetClamped S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  have hno : min nAdv S.N_no_opk_tot ≤ min nAdv S.N_recv_tot := by
    unfold Setup.N_recv_tot; omega
  unfold acceptNoOpkBFuel
  simp only [armBudgetClamped, dsl_cost]; omega

private theorem cost_testBFuel_tight (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (sid : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) (hsid : exprCostUB sid ≤ 4) :
    (testBFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel st sid).cost ≤
      1750 * min nFuel S.N_send_tot + 1750 * min nFuel S.N_recv_tot + 580 := by
  refine (compCost_le_costUB _).trans ?_
  unfold testBFuel
  simp only [dsl_cost]; omega

private theorem cost_testBFuel {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (sid : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) (hsid : exprCostUB sid ≤ 4) :
    (testBFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st sid).cost ≤ armBudgetClamped S nAdv := by
  have h := cost_testBFuel_tight (S := S) (I₀ := I₀) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nAdv st sid hsid
  simp only [armBudgetClamped]; omega

private theorem cost_ro1KeyRealB_clamped {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (sec : Expr (e2eOps ℓ P C K decT encT) Γ (PB 192)) (hsec : exprCostUB sec ≤ 4) :
    (ro1KeyRealB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st sec).cost ≤ armBudgetClamped S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  unfold ro1KeyRealB
  simp only [armBudgetClamped, dsl_cost]; omega

private theorem cost_revealDh1KeyRealB_clamped {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) :
    (revealDh1KeyRealB (S := S) (O := e2eOps ℓ P C K decT encT)
      (I := stepAIface ℓ I₀) st).cost ≤ armBudgetClamped S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  unfold revealDh1KeyRealB
  simp only [armBudgetClamped, dsl_cost]; omega

private theorem cost_revealBFuel {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (sid : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) (hsid : exprCostUB sid ≤ 4) :
    (revealBFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st sid).cost ≤ armBudgetClamped S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  unfold revealBFuel
  simp only [armBudgetClamped, dsl_cost]; omega

private theorem cost_registerB_clamped {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (sk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) (hsk : exprCostUB sk ≤ 4) :
    (registerB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st sk).cost ≤ armBudgetClamped S nAdv := by
  refine (compCost_le_costUB _).trans ?_
  unfold registerB
  simp only [armBudgetClamped, dsl_cost]; omega

private theorem cost_revealSpkBFuel_tight (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (j : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (hu : exprCostUB u ≤ 4) (hj : exprCostUB j ≤ 4) :
    (revealSpkBFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel st u j).cost ≤
      200 * min nFuel S.N_spk_tot + 280 := by
  refine (compCost_le_costUB _).trans ?_
  unfold revealSpkBFuel
  simp only [dsl_cost]; omega

private theorem cost_revealSpkBFuel {Γ : List (Ty (e2eSig ℓ))}
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (j : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (hu : exprCostUB u ≤ 4) (hj : exprCostUB j ≤ 4) :
    (revealSpkBFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st u j).cost ≤ armBudgetClamped S nAdv := by
  have h := cost_revealSpkBFuel_tight (S := S) (I₀ := I₀) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nAdv st u j hu hj
  simp only [armBudgetClamped]; omega

end CostBounds

private theorem cost_caseSum_le {Sig : ReductionDsl.Sig} {O : Ops Sig}
    {ι : Type} {T : OracleSpec ι} {I : Iface Sig T}
    {Γ : List (Ty Sig)} {α β υ : Ty Sig}
    (e : Expr O Γ (.sum α β)) (l : Comp O I (α :: Γ) υ) (r : Comp O I (β :: Γ) υ)
    {B k : ℕ} (hl : l.cost ≤ B) (hr : r.cost ≤ B + k) :
    (Comp.caseSum e l r).cost ≤ e.cost + B + (k + 1) := by
  simp only [Comp.cost]; omega

private theorem cost_caseSum_var_le {Sig : ReductionDsl.Sig} {O : Ops Sig}
    {ι : Type} {T : OracleSpec ι} {I : Iface Sig T}
    {Γ : List (Ty Sig)} {α β υ : Ty Sig}
    (v0 : Var Γ (.sum α β)) (l : Comp O I (α :: Γ) υ) (r : Comp O I (β :: Γ) υ)
    {B k : ℕ} (hl : l.cost ≤ B) (hr : r.cost ≤ B + k) :
    (Comp.caseSum (.var v0) l r).cost ≤ B + (k + 2) := by
  simp only [Comp.cost, Expr.cost]; omega

theorem pqxdh1KeyRealStepC_cost (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S)) :
    (pqxdh1KeyRealStepC ℓ S P C K decT encT I₀ nAdv stE qE).cost ≤
      stE.cost + qE.cost + pqxdh1KeyRealStepCost S nAdv := by
  unfold pqxdh1KeyRealStepC pqxdh1KeyRealStepG
  have hbody :
      (pqxdh1KeyRealBodyG (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv
        (Γ := e2eKeyIndStateTy ℓ S :: .prod (e2eKeyIndStateTy ℓ S) (keyIndQT S) :: Γ)
        .zero (.snd (.var (.succ .zero)))).cost ≤
        (Expr.snd (O := e2eOps ℓ P C K decT encT)
          (Γ := e2eKeyIndStateTy ℓ S :: .prod (e2eKeyIndStateTy ℓ S) (keyIndQT S) :: Γ)
          (.var (.succ .zero))).cost + armBudget S nAdv + 25 := by
    unfold pqxdh1KeyRealBodyG
    refine cost_caseSum_le _ _ _
      (cost_initPrin1KeyB _ _ (by simp only [dsl_cost]; omega)) ?_
    refine cost_caseSum_var_le _ _ _
      (cost_corruptB _ _ (by simp only [dsl_cost]; omega)) ?_
    refine cost_caseSum_var_le _ _ _
      (cost_genSpkB _ _ _ (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)) ?_
    refine cost_caseSum_var_le _ _ _
      (cost_genOpkB _ _ _ _
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)) ?_
    refine cost_caseSum_var_le _ _ _
      (cost_initiateOpkB _ _ _ _
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)) ?_
    refine cost_caseSum_var_le _ _ _
      (cost_initiateNoOpkB _ _ _ _
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)) ?_
    refine cost_caseSum_var_le _ _ _
      (cost_acceptOpkB _ _ _ _ _
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)) ?_
    refine cost_caseSum_var_le _ _ _
      (cost_acceptNoOpkB _ _ _ _ _
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)) ?_
    refine cost_caseSum_var_le _ _ _
      (cost_testB _ _ (by simp only [dsl_cost]; omega)) ?_
    refine cost_caseSum_var_le _ _ _
      (cost_ro1KeyRealB _ _ (by simp only [dsl_cost]; omega)) ?_
    refine cost_caseSum_var_le _ _ _
      (cost_revealDh1KeyRealB _) ?_
    refine cost_caseSum_var_le _ _ _
      (cost_revealB _ _ (by simp only [dsl_cost]; omega)) ?_
    exact cost_caseSum_var_le _ _ _ (k := 0)
      (cost_registerB _ _ (by simp only [dsl_cost]; omega))
      (cost_revealSpkB _ _ _
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega))
  simp only [Comp.cost, Expr.cost, pqxdh1KeyRealStepCost, armBudget] at hbody ⊢
  omega

/-! ## Exact `Comp.eval` Equivalence and `PqxdhSimIface` Instance -/

theorem pqxdh1KeyRealStepC_eval (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S))
    (ρ : Env Γ) (st : KeyIndState S) (kq : KeyIndQuery S)
    (hP : WellFormedPrimitivesδ P)
    (hstE : stE.eval ρ = e2eKeyIndStateToVal st)
    (hqE : qE.eval ρ = keyIndQenc kq)
    (hBnd : KeyIndSetupBounded S st)
    (hAdv : st.advKeys.length ≤ nAdv) :
    (pqxdh1KeyRealStepC ℓ S P C K decT encT I₀ nAdv stE qE).eval ρ =
      (stepAIface ℓ I₀).liftP
        ((fun out => (keyIndRenc out.1, e2eKeyIndStateToVal out.2)) <$>
          ((pqxdhKeyIndImpl1KeyReal S P kq).run st)) := by
  unfold pqxdh1KeyRealStepC pqxdh1KeyRealStepG
  simp only [Comp.eval, Expr.eval, env_get_zero, pure_bind, hstE, hqE]
  cases kq with
  | initPrin u =>
    dsimp only [pqxdh1KeyRealBodyG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    exact eval_initPrin1KeyB hP _ _ _ rfl hBnd
  | corruptIK u =>
    dsimp only [pqxdh1KeyRealBodyG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    exact eval_corruptB _ _ _ rfl hBnd
  | genSPK u j =>
    dsimp only [pqxdh1KeyRealBodyG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    exact eval_genSpkB hP _ _ _ _ rfl hBnd
  | genOPK u j o =>
    dsimp only [pqxdh1KeyRealBodyG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    exact eval_genOpkB hP _ _ _ _ _ rfl hBnd
  | initiateOPK u i bundle =>
    dsimp only [pqxdh1KeyRealBodyG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    conv_rhs => rw [← bundleOfV_bundleV (ℓ := ℓ) bundle]
    exact eval_initiateOpkB hP nAdv _ _ _ _ _ rfl hBnd hAdv
  | initiateNoOPK u i bundle =>
    dsimp only [pqxdh1KeyRealBodyG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    conv_rhs => rw [← bundleOfV_bundleV (ℓ := ℓ) bundle]
    exact eval_initiateNoOpkB hP nAdv _ _ _ _ _ rfl hBnd hAdv
  | acceptOPK k j o hdr =>
    dsimp only [pqxdh1KeyRealBodyG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    conv_rhs => rw [← hdrOfV_hdrV (ℓ := ℓ) hdr]
    exact eval_acceptOpkB hP nAdv _ _ _ _ _ _ rfl hBnd hAdv
  | acceptNoOPK k j l hdr =>
    dsimp only [pqxdh1KeyRealBodyG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    conv_rhs => rw [← hdrOfV_hdrV (ℓ := ℓ) hdr]
    exact eval_acceptNoOpkB hP nAdv _ _ _ _ _ _ rfl hBnd hAdv
  | testSession sid =>
    dsimp only [pqxdh1KeyRealBodyG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    conv_rhs => rw [← sidOfV_sidV (ℓ := ℓ) sid]
    exact eval_testB _ _ _ rfl hBnd
  | roQuery secrets =>
    dsimp only [pqxdh1KeyRealBodyG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    exact eval_ro1KeyRealB hP _ _ _ rfl
  | revealDhSecrets =>
    dsimp only [pqxdh1KeyRealBodyG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    exact eval_revealDh1KeyRealB _ _ rfl
  | revealSessionKey sid =>
    dsimp only [pqxdh1KeyRealBodyG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    conv_rhs => rw [← sidOfV_sidV (ℓ := ℓ) sid]
    exact eval_revealB _ _ _ rfl hBnd
  | registerKey sk =>
    dsimp only [pqxdh1KeyRealBodyG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    exact eval_registerB hP _ _ _ rfl
  | revealSpkSk u j =>
    dsimp only [pqxdh1KeyRealBodyG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    exact eval_revealSpkB _ _ _ _ rfl hBnd

theorem pqxdh1KeyRealStepC_eval_prob (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S))
    (ρ : Env Γ) (st : KeyIndState S) (kq : KeyIndQuery S)
    (hP : WellFormedPrimitivesδ P)
    (hstE : stE.eval ρ = e2eKeyIndStateToVal st)
    (hqE : qE.eval ρ = keyIndQenc kq)
    (hBnd : KeyIndSetupBounded S st)
    (hAdv : st.advKeys.length ≤ nAdv) :
    (pqxdh1KeyRealStepC ℓ S P C K decT encT (e2eProbIface ℓ) nAdv stE qE).eval ρ =
      ((fun out => (keyIndRenc out.1, e2eKeyIndStateToVal out.2)) <$>
        ((pqxdhKeyIndImpl1KeyReal S P kq).run st)) := by
  rw [pqxdh1KeyRealStepC_eval ℓ S P C K decT encT (e2eProbIface ℓ) nAdv stE qE
    ρ st kq hP hstE hqE hBnd hAdv]
  exact e2eProbIface_liftP _

/-- Canonical `PqxdhSimIface` instance packaging `pqxdh1KeyRealStepC` and its cost, query, and
evaluation theorems. -/
def pqxdhSimIface (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    PqxdhSimIface ℓ S P C K decT encT where
  stepC := pqxdh1KeyRealStepC ℓ S P C K decT encT
  stepCost := pqxdh1KeyRealStepCost S
  stepC_cost := pqxdh1KeyRealStepC_cost ℓ S P C K decT encT
  stepC_queries := pqxdh1KeyRealStepC_queries ℓ S P C K decT encT
  stepC_eval := pqxdh1KeyRealStepC_eval ℓ S P C K decT encT

/-! ## `nAdv`-Clamped Step Program and Standalone Sub-Steps -/

section ClampedDispatcher

variable {ℓ : ℕ} {S : Setup} {O : Ops (e2eSig ℓ)} {ι : Type} {T : OracleSpec ι}
  {I : Iface (e2eSig ℓ) T}

def pqxdh1KeyRealBodyClampedG (H : E2EPqxdhHooks ℓ O I) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (st0 : Var Γ (e2eKeyIndStateTy ℓ S))
    (qE : Expr O Γ (keyIndQT S)) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  .caseSum qE
    (initPrin1KeyBFuel H nAdv st0.succ (.var .zero))
    (let st1 := st0.succ
     .caseSum (.var .zero)
       (corruptBFuel H nAdv st1.succ (.var .zero))
       (let st2 := st1.succ
        .caseSum (.var .zero)
          (genSpkBFuel H nAdv st2.succ (.fst (.var .zero)) (.snd (.var .zero)))
          (let st3 := st2.succ
           .caseSum (.var .zero)
             (genOpkBFuel H nAdv st3.succ (.fst (.var .zero)) (.fst (.snd (.var .zero)))
               (.snd (.snd (.var .zero))))
             (let st4 := st3.succ
              .caseSum (.var .zero)
                (initiateOpkBFuel H nAdv st4.succ (.fst (.var .zero))
                  (.fst (.snd (.var .zero))) (.snd (.snd (.var .zero))))
                (let st5 := st4.succ
                 .caseSum (.var .zero)
                   (initiateNoOpkBFuel H nAdv st5.succ (.fst (.var .zero))
                     (.fst (.snd (.var .zero))) (.snd (.snd (.var .zero))))
                   (let st6 := st5.succ
                    .caseSum (.var .zero)
                      (acceptOpkBFuel H nAdv st6.succ (.fst (.var .zero))
                        (.fst (.snd (.var .zero)))
                        (.fst (.snd (.snd (.var .zero))))
                        (.snd (.snd (.snd (.var .zero)))))
                      (let st7 := st6.succ
                       .caseSum (.var .zero)
                         (acceptNoOpkBFuel H nAdv st7.succ (.fst (.var .zero))
                           (.fst (.snd (.var .zero)))
                           (.fst (.snd (.snd (.var .zero))))
                           (.snd (.snd (.snd (.var .zero)))))
                         (let st8 := st7.succ
                          .caseSum (.var .zero)
                            (testBFuel H nAdv st8.succ (.var .zero))
                            (let st9 := st8.succ
                             .caseSum (.var .zero)
                               (ro1KeyRealB H st9.succ (.var .zero))
                               (let st10 := st9.succ
                                .caseSum (.var .zero)
                                  (revealDh1KeyRealB st10.succ)
                                  (let st11 := st10.succ
                                   .caseSum (.var .zero)
                                     (revealBFuel H nAdv st11.succ (.var .zero))
                                     (let st12 := st11.succ
                                      .caseSum (.var .zero)
                                        (registerB H st12.succ (.var .zero))
                                        (revealSpkBFuel H nAdv st12.succ (.fst (.var .zero))
                                          (.snd (.var .zero)))))))))))))))

def pqxdh1KeyRealStepClampedG (H : E2EPqxdhHooks ℓ O I) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (qE : Expr O Γ (keyIndQT S)) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  .bind (.ret (.pair stE qE))
    (.bind (.ret (.fst (.var .zero)))
      (pqxdh1KeyRealBodyClampedG H nAdv .zero (.snd (.var (.succ .zero)))))

def pqxdhTestStepG (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (sidE : Expr O Γ (sidT S)) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  .bind (.ret (.pair stE sidE))
    (.bind (.ret (.fst (.var .zero)))
      (testBFuel H nFuel .zero (.snd (.var (.succ .zero)))))

def pqxdhRevealSpkStepG (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (uE : Expr O Γ (FinT S.N_id))
    (jE : Expr O Γ (FinT S.N_recv)) :
    Comp O I Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  .bind (.ret (.pair stE (.pair uE jE)))
    (.bind (.ret (.fst (.var .zero)))
      (revealSpkBFuel H nFuel .zero
        (.fst (.snd (.var (.succ .zero))))
        (.snd (.snd (.var (.succ .zero))))))

end ClampedDispatcher

/-- Concrete fuel-clamped (`min nAdv S.N_*`) `ReductionDsl` handler simulating one
`pqxdhKeyIndImpl1KeyReal S P` query. -/
@[local irreducible] def pqxdh1KeyRealStepClampedC (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S)) :
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) Γ
      (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  pqxdh1KeyRealStepClampedG (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv stE qE

/-- Closed-form linear `Comp.cost` budget for one `pqxdh1KeyRealStepClampedC` query. -/
def pqxdh1KeyRealStepClampedCost (S : Setup) (nAdv : ℕ) : ℕ :=
  600 * min nAdv S.N_id + 3500 * min nAdv S.N_spk_tot + 300 * min nAdv S.N_opk_tot +
    7100 * min nAdv S.N_send_tot + 7200 * min nAdv S.N_recv_tot + 300 * nAdv + 12200

/-- Standalone fuel-clamped `testSession` step program for `HaltedPrefixSubprogs`. -/
@[local irreducible] def pqxdhTestStepC (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nFuel : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) :
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) Γ
      (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  pqxdhTestStepG (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel stE sidE

def pqxdhTestStepCost (S : Setup) (nFuel : ℕ) : ℕ :=
  1750 * min nFuel S.N_send_tot + 1750 * min nFuel S.N_recv_tot + 600

/-- Standalone fuel-clamped `revealSpkSk` step program for `HaltedPrefixSubprogs`. -/
@[local irreducible] def pqxdhRevealSpkStepC (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nFuel : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (uE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (jE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv)) :
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) Γ
      (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  pqxdhRevealSpkStepG (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel stE uE jE

def pqxdhRevealSpkStepCost (S : Setup) (nFuel : ℕ) : ℕ :=
  200 * min nFuel S.N_spk_tot + 300

theorem queriesUB_pqxdh1KeyRealBodyClampedG {ℓ : ℕ} {S : Setup} {O : Ops (e2eSig ℓ)}
    {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hQ : HooksNoTargetQueries H w) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (st0 : Var Γ (e2eKeyIndStateTy ℓ S)) (qE : Expr O Γ (keyIndQT S)) :
    compQueriesUB w (fun _ => 0) (pqxdh1KeyRealBodyClampedG H nAdv st0 qE) = 0 := by
  unfold pqxdh1KeyRealBodyClampedG
  exact
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_initPrin1KeyBFuel hQ nAdv _ _) <|
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_corruptBFuel hQ nAdv _ _) <|
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_genSpkBFuel hQ nAdv _ _ _) <|
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_genOpkBFuel hQ nAdv _ _ _ _) <|
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_initiateOpkBFuel hQ nAdv _ _ _ _) <|
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_initiateNoOpkBFuel hQ nAdv _ _ _ _) <|
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_acceptOpkBFuel hQ nAdv _ _ _ _ _) <|
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_acceptNoOpkBFuel hQ nAdv _ _ _ _ _) <|
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_testBFuel hQ nAdv _ _) <|
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_ro1KeyRealB hQ _ _) <|
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_revealDh1KeyRealB w _) <|
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_revealBFuel hQ nAdv _ _) <|
    queriesUB_caseSum_zero w _ _ _ _ (queriesUB_registerB hQ _ _)
      (queriesUB_revealSpkBFuel hQ nAdv _ _ _)

theorem queriesUB_pqxdh1KeyRealStepClampedG {ℓ : ℕ} {S : Setup} {O : Ops (e2eSig ℓ)}
    {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hQ : HooksNoTargetQueries H w) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr O Γ (e2eKeyIndStateTy ℓ S)) (qE : Expr O Γ (keyIndQT S)) :
    compQueriesUB w (fun _ => 0) (pqxdh1KeyRealStepClampedG H nAdv stE qE) = 0 := by
  simp only [pqxdh1KeyRealStepClampedG, compQueriesUB, queriesUB_pqxdh1KeyRealBodyClampedG hQ]

@[simp] theorem pqxdh1KeyRealStepClampedC_queries (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S))
    (w : (stepAIface ℓ I₀).Tag → ℕ) :
    (pqxdh1KeyRealStepClampedC ℓ S P C K decT encT I₀ nAdv stE qE).queries w (fun _ => 0) = 0 := by
  unfold pqxdh1KeyRealStepClampedC
  exact Nat.eq_zero_of_le_zero
    ((compQueries_le_queriesUB w (fun _ => 0) _).trans_eq
      (queriesUB_pqxdh1KeyRealStepClampedG (mkStepAPqxdhHooks_noQueries ℓ P C K decT encT I₀ w)
        nAdv stE qE))

theorem queriesUB_pqxdhTestStepG {ℓ : ℕ} {S : Setup} {O : Ops (e2eSig ℓ)}
    {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hQ : HooksNoTargetQueries H w) (nFuel : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr O Γ (e2eKeyIndStateTy ℓ S)) (sidE : Expr O Γ (sidT S)) :
    compQueriesUB w (fun _ => 0) (pqxdhTestStepG H nFuel stE sidE) = 0 := by
  simp only [pqxdhTestStepG, compQueriesUB, queriesUB_testBFuel hQ]

@[simp] theorem pqxdhTestStepC_queries (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nFuel : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (w : (stepAIface ℓ I₀).Tag → ℕ) :
    (pqxdhTestStepC ℓ S P C K decT encT I₀ nFuel stE sidE).queries w (fun _ => 0) = 0 := by
  unfold pqxdhTestStepC
  exact Nat.eq_zero_of_le_zero
    ((compQueries_le_queriesUB w (fun _ => 0) _).trans_eq
      (queriesUB_pqxdhTestStepG (mkStepAPqxdhHooks_noQueries ℓ P C K decT encT I₀ w)
        nFuel stE sidE))

theorem queriesUB_pqxdhRevealSpkStepG {ℓ : ℕ} {S : Setup} {O : Ops (e2eSig ℓ)}
    {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hQ : HooksNoTargetQueries H w) (nFuel : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (uE : Expr O Γ (FinT S.N_id))
    (jE : Expr O Γ (FinT S.N_recv)) :
    compQueriesUB w (fun _ => 0) (pqxdhRevealSpkStepG H nFuel stE uE jE) = 0 := by
  simp only [pqxdhRevealSpkStepG, compQueriesUB, queriesUB_revealSpkBFuel hQ]

@[simp] theorem pqxdhRevealSpkStepC_queries (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nFuel : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (uE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (jE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (w : (stepAIface ℓ I₀).Tag → ℕ) :
    (pqxdhRevealSpkStepC ℓ S P C K decT encT I₀ nFuel stE uE jE).queries w (fun _ => 0) = 0 := by
  unfold pqxdhRevealSpkStepC
  exact Nat.eq_zero_of_le_zero
    ((compQueries_le_queriesUB w (fun _ => 0) _).trans_eq
      (queriesUB_pqxdhRevealSpkStepG (mkStepAPqxdhHooks_noQueries ℓ P C K decT encT I₀ w)
        nFuel stE uE jE))

theorem pqxdh1KeyRealStepClampedC_cost (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S)) :
    (pqxdh1KeyRealStepClampedC ℓ S P C K decT encT I₀ nAdv stE qE).cost ≤
      stE.cost + qE.cost + pqxdh1KeyRealStepClampedCost S nAdv := by
  unfold pqxdh1KeyRealStepClampedC pqxdh1KeyRealStepClampedG
  have hbody :
      (pqxdh1KeyRealBodyClampedG (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv
        (Γ := e2eKeyIndStateTy ℓ S :: .prod (e2eKeyIndStateTy ℓ S) (keyIndQT S) :: Γ)
        .zero (.snd (.var (.succ .zero)))).cost ≤
        (Expr.snd (O := e2eOps ℓ P C K decT encT)
          (Γ := e2eKeyIndStateTy ℓ S :: .prod (e2eKeyIndStateTy ℓ S) (keyIndQT S) :: Γ)
          (.var (.succ .zero))).cost + armBudgetClamped S nAdv + 25 := by
    unfold pqxdh1KeyRealBodyClampedG
    refine cost_caseSum_le _ _ _
      (cost_initPrin1KeyBFuel _ _ (by simp only [dsl_cost]; omega)) ?_
    refine cost_caseSum_var_le _ _ _
      (cost_corruptBFuel _ _ (by simp only [dsl_cost]; omega)) ?_
    refine cost_caseSum_var_le _ _ _
      (cost_genSpkBFuel _ _ _ (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)) ?_
    refine cost_caseSum_var_le _ _ _
      (cost_genOpkBFuel _ _ _ _
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)) ?_
    refine cost_caseSum_var_le _ _ _
      (cost_initiateOpkBFuel _ _ _ _
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)) ?_
    refine cost_caseSum_var_le _ _ _
      (cost_initiateNoOpkBFuel _ _ _ _
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)) ?_
    refine cost_caseSum_var_le _ _ _
      (cost_acceptOpkBFuel _ _ _ _ _
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)) ?_
    refine cost_caseSum_var_le _ _ _
      (cost_acceptNoOpkBFuel _ _ _ _ _
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega)) ?_
    refine cost_caseSum_var_le _ _ _
      (cost_testBFuel _ _ (by simp only [dsl_cost]; omega)) ?_
    refine cost_caseSum_var_le _ _ _
      (cost_ro1KeyRealB_clamped _ _ (by simp only [dsl_cost]; omega)) ?_
    refine cost_caseSum_var_le _ _ _
      (cost_revealDh1KeyRealB_clamped _) ?_
    refine cost_caseSum_var_le _ _ _
      (cost_revealBFuel _ _ (by simp only [dsl_cost]; omega)) ?_
    exact cost_caseSum_var_le _ _ _ (k := 0)
      (cost_registerB_clamped _ _ (by simp only [dsl_cost]; omega))
      (cost_revealSpkBFuel _ _ _
        (by simp only [dsl_cost]; omega)
        (by simp only [dsl_cost]; omega))
  simp only [Comp.cost, Expr.cost, pqxdh1KeyRealStepClampedCost, armBudgetClamped] at hbody ⊢
  omega

theorem pqxdhTestStepC_cost (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nFuel : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) :
    (pqxdhTestStepC ℓ S P C K decT encT I₀ nFuel stE sidE).cost ≤
      stE.cost + sidE.cost + pqxdhTestStepCost S nFuel := by
  unfold pqxdhTestStepC pqxdhTestStepG
  have hbody := cost_testBFuel_tight (S := S) (I₀ := I₀) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nFuel
    (Γ := e2eKeyIndStateTy ℓ S :: .prod (e2eKeyIndStateTy ℓ S) (sidT S) :: Γ)
    .zero (.snd (.var (.succ .zero))) (by simp only [dsl_cost]; omega)
  simp only [Comp.cost, Expr.cost, pqxdhTestStepCost] at hbody ⊢
  omega

theorem pqxdhRevealSpkStepC_cost (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nFuel : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (uE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (jE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv)) :
    (pqxdhRevealSpkStepC ℓ S P C K decT encT I₀ nFuel stE uE jE).cost ≤
      stE.cost + uE.cost + jE.cost + pqxdhRevealSpkStepCost S nFuel := by
  unfold pqxdhRevealSpkStepC pqxdhRevealSpkStepG
  have hbody := cost_revealSpkBFuel_tight (S := S) (I₀ := I₀) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nFuel
    (Γ := e2eKeyIndStateTy ℓ S ::
      .prod (e2eKeyIndStateTy ℓ S) (.prod (FinT S.N_id) (FinT S.N_recv)) :: Γ)
    .zero (.fst (.snd (.var (.succ .zero)))) (.snd (.snd (.var (.succ .zero))))
    (by simp only [dsl_cost]; omega) (by simp only [dsl_cost]; omega)
  simp only [Comp.cost, Expr.cost, pqxdhRevealSpkStepCost] at hbody ⊢
  omega

theorem pqxdh1KeyRealStepClampedC_eval (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S))
    (ρ : Env Γ) (st : KeyIndState S) (kq : KeyIndQuery S)
    (hP : WellFormedPrimitivesδ P)
    (hstE : stE.eval ρ = e2eKeyIndStateToVal st)
    (hqE : qE.eval ρ = keyIndQenc kq)
    (hst : stListBounded S nAdv st) :
    (pqxdh1KeyRealStepClampedC ℓ S P C K decT encT I₀ nAdv stE qE).eval ρ =
      (stepAIface ℓ I₀).liftP
        ((fun out => (keyIndRenc out.1, e2eKeyIndStateToVal out.2)) <$>
          ((pqxdhKeyIndImpl1KeyReal S P kq).run st)) := by
  unfold pqxdh1KeyRealStepClampedC pqxdh1KeyRealStepClampedG
  simp only [Comp.eval, Expr.eval, env_get_zero, pure_bind, hstE, hqE]
  cases kq with
  | initPrin u =>
    dsimp only [pqxdh1KeyRealBodyClampedG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    exact eval_initPrin1KeyBFuel hP nAdv _ _ _ rfl hst
  | corruptIK u =>
    dsimp only [pqxdh1KeyRealBodyClampedG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    exact eval_corruptBFuel nAdv _ _ _ rfl hst
  | genSPK u j =>
    dsimp only [pqxdh1KeyRealBodyClampedG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    exact eval_genSpkBFuel hP nAdv _ _ _ _ rfl hst
  | genOPK u j o =>
    dsimp only [pqxdh1KeyRealBodyClampedG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    exact eval_genOpkBFuel hP nAdv _ _ _ _ _ rfl hst
  | initiateOPK u i bundle =>
    dsimp only [pqxdh1KeyRealBodyClampedG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    conv_rhs => rw [← bundleOfV_bundleV (ℓ := ℓ) bundle]
    exact eval_initiateOpkBFuel hP nAdv _ _ _ _ _ rfl hst
  | initiateNoOPK u i bundle =>
    dsimp only [pqxdh1KeyRealBodyClampedG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    conv_rhs => rw [← bundleOfV_bundleV (ℓ := ℓ) bundle]
    exact eval_initiateNoOpkBFuel hP nAdv _ _ _ _ _ rfl hst
  | acceptOPK k j o hdr =>
    dsimp only [pqxdh1KeyRealBodyClampedG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    conv_rhs => rw [← hdrOfV_hdrV (ℓ := ℓ) hdr]
    exact eval_acceptOpkBFuel hP nAdv _ _ _ _ _ _ rfl hst
  | acceptNoOPK k j l hdr =>
    dsimp only [pqxdh1KeyRealBodyClampedG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    conv_rhs => rw [← hdrOfV_hdrV (ℓ := ℓ) hdr]
    exact eval_acceptNoOpkBFuel hP nAdv _ _ _ _ _ _ rfl hst
  | testSession sid =>
    dsimp only [pqxdh1KeyRealBodyClampedG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    conv_rhs => rw [← sidOfV_sidV (ℓ := ℓ) sid]
    exact eval_testBFuel nAdv _ _ _ rfl hst
  | roQuery secrets =>
    dsimp only [pqxdh1KeyRealBodyClampedG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    exact eval_ro1KeyRealB hP _ _ _ rfl
  | revealDhSecrets =>
    dsimp only [pqxdh1KeyRealBodyClampedG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    exact eval_revealDh1KeyRealB _ _ rfl
  | revealSessionKey sid =>
    dsimp only [pqxdh1KeyRealBodyClampedG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    conv_rhs => rw [← sidOfV_sidV (ℓ := ℓ) sid]
    exact eval_revealBFuel nAdv _ _ _ rfl hst
  | registerKey sk =>
    dsimp only [pqxdh1KeyRealBodyClampedG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    exact eval_registerB hP _ _ _ rfl
  | revealSpkSk u j =>
    dsimp only [pqxdh1KeyRealBodyClampedG, Comp.eval, Expr.eval, env_get_zero, env_get_succ, keyIndQenc]
    exact eval_revealSpkBFuel nAdv _ _ _ _ rfl hst

theorem pqxdh1KeyRealStepClampedC_eval_prob (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S))
    (ρ : Env Γ) (st : KeyIndState S) (kq : KeyIndQuery S)
    (hP : WellFormedPrimitivesδ P)
    (hstE : stE.eval ρ = e2eKeyIndStateToVal st)
    (hqE : qE.eval ρ = keyIndQenc kq)
    (hst : stListBounded S nAdv st) :
    (pqxdh1KeyRealStepClampedC ℓ S P C K decT encT (e2eProbIface ℓ) nAdv stE qE).eval ρ =
      ((fun out => (keyIndRenc out.1, e2eKeyIndStateToVal out.2)) <$>
        ((pqxdhKeyIndImpl1KeyReal S P kq).run st)) := by
  rw [pqxdh1KeyRealStepClampedC_eval ℓ S P C K decT encT (e2eProbIface ℓ) nAdv stE qE
    ρ st kq hP hstE hqE hst]
  exact e2eProbIface_liftP _

theorem pqxdhTestStepC_eval (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nFuel : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (ρ : Env Γ) (st : KeyIndState S)
    (hstE : stE.eval ρ = e2eKeyIndStateToVal st)
    (hst : stListBounded S nFuel st) :
    (pqxdhTestStepC ℓ S P C K decT encT I₀ nFuel stE sidE).eval ρ =
      (stepAIface ℓ I₀).liftP
        ((fun out => (keyIndRenc out.1, e2eKeyIndStateToVal out.2)) <$>
          ((pqxdhKeyIndImpl1KeyReal S P (.testSession (sidOfV (sidE.eval ρ)))).run st)) := by
  unfold pqxdhTestStepC pqxdhTestStepG
  simp only [Comp.eval, Expr.eval, env_get_zero, pure_bind, hstE]
  exact eval_testBFuel nFuel _ _ _ rfl hst

theorem pqxdhTestStepC_eval_prob (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (nFuel : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (ρ : Env Γ) (st : KeyIndState S)
    (hstE : stE.eval ρ = e2eKeyIndStateToVal st)
    (hst : stListBounded S nFuel st) :
    (pqxdhTestStepC ℓ S P C K decT encT (e2eProbIface ℓ) nFuel stE sidE).eval ρ =
      ((fun out => (keyIndRenc out.1, e2eKeyIndStateToVal out.2)) <$>
        ((pqxdhKeyIndImpl1KeyReal S P (.testSession (sidOfV (sidE.eval ρ)))).run st)) := by
  rw [pqxdhTestStepC_eval ℓ S P C K decT encT (e2eProbIface ℓ) nFuel stE sidE ρ st hstE hst]
  exact e2eProbIface_liftP _

theorem pqxdhRevealSpkStepC_eval (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nFuel : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (uE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (jE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (ρ : Env Γ) (st : KeyIndState S)
    (hstE : stE.eval ρ = e2eKeyIndStateToVal st)
    (hst : stListBounded S nFuel st) :
    (pqxdhRevealSpkStepC ℓ S P C K decT encT I₀ nFuel stE uE jE).eval ρ =
      (stepAIface ℓ I₀).liftP
        ((fun out => (keyIndRenc out.1, e2eKeyIndStateToVal out.2)) <$>
          ((pqxdhKeyIndImpl1KeyReal S P (.revealSpkSk (uE.eval ρ) (jE.eval ρ))).run st)) := by
  unfold pqxdhRevealSpkStepC pqxdhRevealSpkStepG
  simp only [Comp.eval, Expr.eval, env_get_zero, pure_bind, hstE]
  exact eval_revealSpkBFuel nFuel _ _ _ _ rfl hst

theorem pqxdhRevealSpkStepC_eval_prob (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (nFuel : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (uE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (jE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (ρ : Env Γ) (st : KeyIndState S)
    (hstE : stE.eval ρ = e2eKeyIndStateToVal st)
    (hst : stListBounded S nFuel st) :
    (pqxdhRevealSpkStepC ℓ S P C K decT encT (e2eProbIface ℓ) nFuel stE uE jE).eval ρ =
      ((fun out => (keyIndRenc out.1, e2eKeyIndStateToVal out.2)) <$>
        ((pqxdhKeyIndImpl1KeyReal S P (.revealSpkSk (uE.eval ρ) (jE.eval ρ))).run st)) := by
  rw [pqxdhRevealSpkStepC_eval ℓ S P C K decT encT (e2eProbIface ℓ) nFuel stE uE jE ρ st hstE hst]
  exact e2eProbIface_liftP _

theorem stListBounded_of_testSession {S : Setup} {P : Primitives} {nFuel : ℕ}
    (sid : SessionId S) {st : KeyIndState S} (hst : stListBounded S nFuel st)
    {out : KeyIndResponse × KeyIndState S}
    (hmem : out ∈ support ((pqxdhKeyIndImpl1KeyReal S P (.testSession sid)).run st)) :
    stListBounded S nFuel out.2 :=
  pqxdhKeyIndImpl1KeyReal_testSession_preserves_stListBounded sid hst hmem

theorem stListBounded_of_revealSpkSk {S : Setup} {P : Primitives} {nFuel : ℕ}
    (u : Fin S.N_id) (j : Fin S.N_recv) {st : KeyIndState S} (hst : stListBounded S nFuel st)
    {out : KeyIndResponse × KeyIndState S}
    (hmem : out ∈ support ((pqxdhKeyIndImpl1KeyReal S P (.revealSpkSk u j)).run st)) :
    stListBounded S nFuel out.2 :=
  pqxdhKeyIndImpl1KeyReal_revealSpkSk_preserves_stListBounded u j hst hmem

end Computational.Proofs.E2E.Dsl.PqxdhSim
