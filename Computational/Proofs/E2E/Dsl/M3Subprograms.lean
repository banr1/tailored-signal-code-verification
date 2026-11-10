/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.M3Interfaces
public import Computational.Proofs.E2E.Dsl.PqxdhSim
public import Computational.Proofs.E2E.Dsl.SpqrSim
public import Computational.Proofs.E2E.Dsl.DrSessionSim
public import Computational.Proofs.E2E.Dsl.E2EStateRepr
public import Computational.Proofs.E2E.Dsl.FreshnessSim
public import Computational.Proofs.E2E.Dsl.LocalSessionStep
public import Computational.Proofs.E2E.Dsl.StartAndExtSm
import Computational.Proofs.ReductionDsl.SizeBudgetBridge

/-!
# Concrete M3 Sub-Program Bundle

Instantiates `DrvStateGuardFreshIface` and the combined `M3SubprogramsIface` bundle over `e2eSig ℓ`
and `e2eOps`, wiring together the PQXDH simulator, SPQR-backed Double Ratchet session simulator,
driver guard and freshness handlers, local multi-session `SM` handler, and session promotion.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.M3Subprograms

open _root_.ReductionDsl (Ty Expr Comp Iface bits)
open CryptoGames.LibsignalSession (Crypto PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E.Costed (E2EPureOp e2eSig e2eOps keyIndQT keyIndRT sidT smQT BV256)
open Computational.Proofs.E2E.Dsl.TablesHonest (size_e2ePureOp size_e2eCurveOp size_e2eCryptoOp)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (Ext v eLet eLet2 eCaseOpt eCaseSum eFind eAny eMap
  bindV letV bindV2 caseOptV caseSumV findMV anyMV mapMV orE isSomeE isNoneE optMapE e2eKeyIndStateTy)
open Computational.Proofs.E2E.Dsl.M2Interfaces (PqxdhSimIface DrSessionSimIface)
open Computational.Proofs.E2E.Dsl.M3Interfaces (e2eDrvStateTy DrvStateGuardFreshIface
  LocalSessionStepIface StartAndExtSmIface M3SubprogramsIface)
open Computational.Proofs.E2E.Dsl.PqxdhSim (pqxdhSimIface pqxdh1KeyRealStepCost)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks)
open Computational.Proofs.E2E.Dsl.DrSessionSim (drSessionSimIface drOracleStepCost)
open Computational.Proofs.E2E.Dsl.LocalSessionStep (localSessionStepIface stepLocalSmCost)
open Computational.Proofs.E2E.Dsl.StartAndExtSm (startAndExtSmIface
  finishStartSpkCost promoteSlotKCost extSmStepCost)

def concreteDrSessionSim (ℓ : ℕ) {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    DrSessionSimIface ℓ P C K decT encT :=
  drSessionSimIface (spqrDslHooks ℓ P C K decT encT)

theorem add_le_group3 (x c d e : ℕ) : x + c + d + e ≤ x + (c + d + e) := by omega

theorem add_le_group6 (x a b c d e f : ℕ) :
    x + a + b + c + d + e + f ≤ x + (a + b + c + d + e + f) := by omega

/-! ## Compositional `.size` Bounds for `M3SubprogramsSizeIface` -/

section SizeBounds

@[simp] private theorem size_v {ℓ : ℕ} {O : ReductionDsl.Ops (e2eSig ℓ)}
    {Γ Δ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)} [Ext Γ Δ] (x : ReductionDsl.Var Γ τ) :
    (v (O := O) (Δ := Δ) x).size = 1 := rfl

private theorem size_drvWonE (ℓ : ℕ) (S : SignalPqxdh.Setup) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (bE : Expr (e2eOps ℓ P C K decT encT) Γ .bool) :
    (FreshnessSim.drvWonE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) qStart σE bE).size ≤
      σE.size + bE.size + bits qStart + 40 := by
  simp only [FreshnessSim.drvWonE, E2EStateRepr.drvInsts, E2EStateRepr.miGs,
    FreshnessSim.gsB, FreshnessSim.gsWin, FreshnessSim.boolEqE,
    eLet, eAny, eCaseOpt, size_v, Expr.size]
  omega

theorem size_finishKindE (ℓ : ℕ) (S : SignalPqxdh.Setup) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (b'E : Expr (e2eOps ℓ P C K decT encT) Γ .bool) :
    (FreshnessSim.finishKindE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) qStart σE b'E).size ≤
      σE.size + b'E.size + bits qStart + 80 := by
  let Δ := (e2eDrvStateTy S ℓ).prod .bool :: Γ
  have hw := size_drvWonE ℓ S P C K decT encT qStart (Γ := Δ)
    (.fst (.var .zero)) (E2EStateRepr.drvB (.fst (.var .zero)))
  simp only [E2EStateRepr.drvB, Expr.size, Nat.reduceAdd] at hw
  unfold FreshnessSim.finishKindE
  dsimp only [v, Ext.wk]
  simp only [orE, FreshnessSim.boolEqE, E2EStateRepr.drvB,
    eLet, Expr.size, Nat.reduceAdd]
  omega

private theorem size_isHonestUncorruptedPeerSomeE (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (nId : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (principalsE : Expr (e2eOps ℓ P C K decT encT) Γ
      (.list (.prod .nat PqxdhSimTypes.e2ePrincipalEntryTy)))
    (pkE : Expr (e2eOps ℓ P C K decT encT) Γ (CryptoVerification.E2E.Costed.PB 32)) :
    (FreshnessSim.isHonestUncorruptedPeerSomeE (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) nId principalsE pkE).size ≤
      principalsE.size + pkE.size + bits nId + 50 := by
  simp only [FreshnessSim.isHonestUncorruptedPeerSomeE,
    PqxdhSimTypes.peIkPk, PqxdhSimTypes.peCorr,
    size_e2ePureOp, E2EPureOp.opSize, size_e2eCryptoOp,
    eLet, eCaseOpt, eFind, size_v, Expr.size]
  omega

private theorem size_isSpkRevealedE (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (nSpk : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (spkBundlesE : Expr (e2eOps ℓ P C K decT encT) Γ
      (.list (.prod (.prod .nat .nat) PqxdhSimTypes.e2eSpkBundleEntryTy)))
    (pkE : Expr (e2eOps ℓ P C K decT encT) Γ (CryptoVerification.E2E.Costed.PB 32)) :
    (FreshnessSim.isSpkRevealedE (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) nSpk spkBundlesE pkE).size ≤
      spkBundlesE.size + pkE.size + bits nSpk + 50 := by
  simp only [FreshnessSim.isSpkRevealedE,
    PqxdhSimTypes.beRev, PqxdhSimTypes.beSpkPk,
    size_e2ePureOp, E2EPureOp.opSize, size_e2eCryptoOp,
    eLet, eAny, size_v, Expr.size]
  omega

private theorem size_keyIndInitCorrClauseE (ℓ : ℕ) (S : SignalPqxdh.Setup) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (nId nSpk : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (principalsE : Expr (e2eOps ℓ P C K decT encT) Γ
      (.list (.prod .nat PqxdhSimTypes.e2ePrincipalEntryTy)))
    (spkBundlesE : Expr (e2eOps ℓ P C K decT encT) Γ
      (.list (.prod (.prod .nat .nat) PqxdhSimTypes.e2eSpkBundleEntryTy)))
    (sE : Expr (e2eOps ℓ P C K decT encT) Γ (PqxdhSimTypes.e2eInitiatorEntryTy ℓ S)) :
    (FreshnessSim.keyIndInitCorrClauseE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) nId nSpk principalsE spkBundlesE sE).size ≤
      principalsE.size + spkBundlesE.size + sE.size + bits nId + bits nSpk + 180 := by
  let Δ := (Ty.list (.prod .nat PqxdhSimTypes.e2ePrincipalEntryTy)).prod
    ((Ty.list (.prod (.prod .nat .nat) PqxdhSimTypes.e2eSpkBundleEntryTy)).prod
      (PqxdhSimTypes.e2eInitiatorEntryTy ℓ S)) :: Γ
  have h1 := size_isHonestUncorruptedPeerSomeE ℓ P C K decT encT nId (Γ := Δ)
    (.fst (.var .zero)) (PqxdhSimTypes.iePeerIk (.snd (.snd (.var .zero))))
  have h2 := size_isSpkRevealedE ℓ P C K decT encT nSpk (Γ := Δ)
    (.fst (.snd (.var .zero))) (PqxdhSimTypes.iePeerSpk (.snd (.snd (.var .zero))))
  simp only [PqxdhSimTypes.iePeerIk, PqxdhSimTypes.iePeerSpk, Expr.size, Nat.reduceAdd] at h1 h2
  unfold FreshnessSim.keyIndInitCorrClauseE
  dsimp only [v, Ext.wk]
  simp only [PqxdhSimTypes.ieFresh, PqxdhSimTypes.ieSpkHon, PqxdhSimTypes.ieOpkHon,
    PqxdhSimTypes.iePeerIk, PqxdhSimTypes.iePeerSpk, orE,
    eLet, Expr.size, Nat.reduceAdd]
  omega

private theorem size_optPow8EqE (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {Γ : List (Ty (e2eSig ℓ))}
    (aE bE : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (CryptoVerification.E2E.Costed.PB 32))) :
    (FreshnessSim.optPow8EqE (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) aE bE).size ≤ aE.size + bE.size + 40 := by
  simp only [FreshnessSim.optPow8EqE, isNoneE, size_e2ePureOp, E2EPureOp.opSize, size_e2eCryptoOp,
    eLet, eCaseOpt, size_v, Expr.size]
  omega

private theorem size_keyIndPartnerE (ℓ : ℕ) (S : SignalPqxdh.Setup) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {Γ : List (Ty (e2eSig ℓ))}
    (sE : Expr (e2eOps ℓ P C K decT encT) Γ (PqxdhSimTypes.e2eInitiatorEntryTy ℓ S))
    (rE : Expr (e2eOps ℓ P C K decT encT) Γ (PqxdhSimTypes.e2eRespEntryTy ℓ S)) :
    (FreshnessSim.keyIndPartnerE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) sE rE).size ≤ sE.size + rE.size + 220 := by
  let Δ := (PqxdhSimTypes.e2eInitiatorEntryTy ℓ S).prod (PqxdhSimTypes.e2eRespEntryTy ℓ S) :: Γ
  have hopk := size_optPow8EqE ℓ P C K decT encT (Γ := Δ)
    (PqxdhSimTypes.iePeerOpk (.fst (.var .zero))) (PqxdhSimTypes.reOpk (.snd (.var .zero)))
  simp only [PqxdhSimTypes.iePeerOpk, PqxdhSimTypes.reOpk, Expr.size, Nat.reduceAdd] at hopk
  unfold FreshnessSim.keyIndPartnerE
  dsimp only [v, Ext.wk]
  simp only [PqxdhSimTypes.ieHdr, PqxdhSimTypes.iePeerIk, PqxdhSimTypes.iePeerSpk,
    PqxdhSimTypes.iePeerOpk, PqxdhSimTypes.iePeerPq,
    PqxdhSimTypes.reHdr, PqxdhSimTypes.reIk, PqxdhSimTypes.reSpk,
    PqxdhSimTypes.reOpk, PqxdhSimTypes.rePq,
    PqxdhSimTypes.hdrIkA, PqxdhSimTypes.hdrEkA, PqxdhSimTypes.hdrKemCt,
    size_e2ePureOp, E2EPureOp.opSize, size_e2eCryptoOp,
    eLet, Expr.size, Nat.reduceAdd]
  omega

private theorem size_isKeyIndInitStillFreshE (ℓ : ℕ) (S : SignalPqxdh.Setup) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (nId nSpk nResp : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (principalsE : Expr (e2eOps ℓ P C K decT encT) Γ
      (.list (.prod .nat PqxdhSimTypes.e2ePrincipalEntryTy)))
    (spkBundlesE : Expr (e2eOps ℓ P C K decT encT) Γ
      (.list (.prod (.prod .nat .nat) PqxdhSimTypes.e2eSpkBundleEntryTy)))
    (respE : Expr (e2eOps ℓ P C K decT encT) Γ (.list (PqxdhSimTypes.e2eRespEntryTy ℓ S)))
    (sE : Expr (e2eOps ℓ P C K decT encT) Γ (PqxdhSimTypes.e2eInitiatorEntryTy ℓ S)) :
    (FreshnessSim.isKeyIndInitStillFreshE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) nId nSpk nResp principalsE spkBundlesE respE sE).size ≤
      principalsE.size + spkBundlesE.size + respE.size + sE.size +
        bits nId + bits nSpk + bits nResp + 500 := by
  let Δ := (Ty.list (.prod .nat PqxdhSimTypes.e2ePrincipalEntryTy)).prod
    ((Ty.list (.prod (.prod .nat .nat) PqxdhSimTypes.e2eSpkBundleEntryTy)).prod
      ((Ty.list (PqxdhSimTypes.e2eRespEntryTy ℓ S)).prod
        (PqxdhSimTypes.e2eInitiatorEntryTy ℓ S))) :: Γ
  have hc := size_keyIndInitCorrClauseE ℓ S P C K decT encT nId nSpk (Γ := Δ)
    (.fst (.var .zero)) (.fst (.snd (.var .zero))) (.snd (.snd (.snd (.var .zero))))
  have hp := size_keyIndPartnerE ℓ S P C K decT encT (Γ := PqxdhSimTypes.e2eRespEntryTy ℓ S :: Δ)
    (.snd (.snd (.snd (.var (.succ .zero))))) (.var .zero)
  simp only [Expr.size, Nat.reduceAdd] at hc hp
  unfold FreshnessSim.isKeyIndInitStillFreshE
  dsimp only [v, Ext.wk]
  simp only [PqxdhSimTypes.ieRev, PqxdhSimTypes.reSendHon, PqxdhSimTypes.reRev, orE,
    eLet, eAny, Expr.size, Nat.reduceAdd]
  omega

private theorem size_respPartnerFoldE (ℓ : ℕ) (S : SignalPqxdh.Setup) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (nInit : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (initE : Expr (e2eOps ℓ P C K decT encT) Γ (.list (PqxdhSimTypes.e2eInitiatorEntryTy ℓ S)))
    (rE : Expr (e2eOps ℓ P C K decT encT) Γ (PqxdhSimTypes.e2eRespEntryTy ℓ S))
    (aE bE : Expr (e2eOps ℓ P C K decT encT) Γ .bool) :
    (FreshnessSim.respPartnerFoldE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) nInit initE rE aE bE).size ≤
      initE.size + rE.size + aE.size + bE.size + bits nInit + 350 := by
  have hp := size_keyIndPartnerE ℓ S P C K decT encT
    (Γ := PqxdhSimTypes.e2eInitiatorEntryTy ℓ S :: .prod .bool .bool ::
      .prod (.list (PqxdhSimTypes.e2eInitiatorEntryTy ℓ S))
        (.prod (PqxdhSimTypes.e2eRespEntryTy ℓ S) (.prod .bool .bool)) :: Γ)
    (.var .zero) (.fst (.snd (.var (.succ (.succ .zero)))))
  simp only [Expr.size, Nat.reduceAdd] at hp
  unfold FreshnessSim.respPartnerFoldE FreshnessSim.respPartnerStepE
  simp only [PqxdhSimTypes.ieRev, PqxdhSimTypes.ieFresh, PqxdhSimTypes.ieSpkHon,
    PqxdhSimTypes.ieOpkHon, orE, Expr.size, Nat.reduceAdd]
  omega

private theorem size_isKeyIndRespStillFreshE (ℓ : ℕ) (S : SignalPqxdh.Setup) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (nId nSpk nInit : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (principalsE : Expr (e2eOps ℓ P C K decT encT) Γ
      (.list (.prod .nat PqxdhSimTypes.e2ePrincipalEntryTy)))
    (spkBundlesE : Expr (e2eOps ℓ P C K decT encT) Γ
      (.list (.prod (.prod .nat .nat) PqxdhSimTypes.e2eSpkBundleEntryTy)))
    (initE : Expr (e2eOps ℓ P C K decT encT) Γ (.list (PqxdhSimTypes.e2eInitiatorEntryTy ℓ S)))
    (rE : Expr (e2eOps ℓ P C K decT encT) Γ (PqxdhSimTypes.e2eRespEntryTy ℓ S)) :
    (FreshnessSim.isKeyIndRespStillFreshE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) nId nSpk nInit principalsE spkBundlesE initE rE).size ≤
      principalsE.size + spkBundlesE.size + initE.size + rE.size +
        2 * bits nId + bits nSpk + bits nInit + 700 := by
  let Δ := (Ty.list (.prod .nat PqxdhSimTypes.e2ePrincipalEntryTy)).prod
    ((Ty.list (.prod (.prod .nat .nat) PqxdhSimTypes.e2eSpkBundleEntryTy)).prod
      ((Ty.list (PqxdhSimTypes.e2eInitiatorEntryTy ℓ S)).prod
        (PqxdhSimTypes.e2eRespEntryTy ℓ S))) :: Γ
  have h1 := size_isHonestUncorruptedPeerSomeE ℓ P C K decT encT nId (Γ := Δ)
    (.fst (.var .zero)) (PqxdhSimTypes.reIk (.snd (.snd (.snd (.var .zero)))))
  have h2 := size_isSpkRevealedE ℓ P C K decT encT nSpk (Γ := Δ)
    (.fst (.snd (.var .zero))) (PqxdhSimTypes.reSpk (.snd (.snd (.snd (.var .zero)))))
  have h3 := size_isHonestUncorruptedPeerSomeE ℓ P C K decT encT nId (Γ := Δ)
    (.fst (.var .zero))
    (PqxdhSimTypes.hdrIkA (PqxdhSimTypes.reHdr (.snd (.snd (.snd (.var .zero))))))
  have hf := size_respPartnerFoldE ℓ S P C K decT encT nInit
    (Γ := Ty.prod .bool (.prod .bool .bool) :: Δ)
    (.fst (.snd (.snd (.var (.succ .zero)))))
    (.snd (.snd (.snd (.var (.succ .zero)))))
    (.fst (.var .zero)) (.fst (.snd (.var .zero)))
  simp only [PqxdhSimTypes.reIk, PqxdhSimTypes.reSpk, PqxdhSimTypes.reHdr,
    PqxdhSimTypes.hdrIkA, Expr.size, Nat.reduceAdd] at h1 h2 h3 hf
  unfold FreshnessSim.isKeyIndRespStillFreshE
  dsimp only [v, Ext.wk]
  simp only [PqxdhSimTypes.reRev, PqxdhSimTypes.reSendHon,
    PqxdhSimTypes.reIk, PqxdhSimTypes.reSpk, PqxdhSimTypes.reHdr, PqxdhSimTypes.hdrIkA,
    eLet, Expr.size, Nat.reduceAdd]
  omega

private theorem size_allTestedSessionsFreshBoundedE (ℓ : ℕ) (S : SignalPqxdh.Setup) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (nInit nResp nId nSpk : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S)) :
    (FreshnessSim.allTestedSessionsFreshBoundedE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) nInit nResp nId nSpk stE).size ≤
      stE.size + 2 * bits nInit + 2 * bits nResp + 3 * bits nId + 2 * bits nSpk + 1500 := by
  let Δ := e2eKeyIndStateTy ℓ S :: Γ
  have hi := size_isKeyIndInitStillFreshE ℓ S P C K decT encT nId nSpk nResp
    (Γ := PqxdhSimTypes.e2eInitiatorEntryTy ℓ S :: Δ)
    (PqxdhSimTypes.stPrin (.var (.succ .zero)))
    (PqxdhSimTypes.stSpk (.var (.succ .zero)))
    (PqxdhSimTypes.stResp (.var (.succ .zero)))
    (.var .zero)
  have hr := size_isKeyIndRespStillFreshE ℓ S P C K decT encT nId nSpk nInit
    (Γ := PqxdhSimTypes.e2eRespEntryTy ℓ S :: Δ)
    (PqxdhSimTypes.stPrin (.var (.succ .zero)))
    (PqxdhSimTypes.stSpk (.var (.succ .zero)))
    (PqxdhSimTypes.stSess (.var (.succ .zero)))
    (.var .zero)
  simp only [PqxdhSimTypes.stPrin, PqxdhSimTypes.stSpk, PqxdhSimTypes.stResp,
    PqxdhSimTypes.stSess, Expr.size, Nat.reduceAdd] at hi hr
  unfold FreshnessSim.allTestedSessionsFreshBoundedE
  dsimp only [v, Ext.wk]
  simp only [PqxdhSimTypes.stPrin, PqxdhSimTypes.stSpk, PqxdhSimTypes.stResp,
    PqxdhSimTypes.stSess, PqxdhSimTypes.ieTested, PqxdhSimTypes.reTested, orE,
    eLet, eAny, Expr.size, Nat.reduceAdd]
  omega

theorem size_finishPrefixC (ℓ : ℕ) (S : SignalPqxdh.Setup) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (b'E flipE : Expr (e2eOps ℓ P C K decT encT) Γ .bool) :
    (FreshnessSim.finishPrefixC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) I₀ qStart nAdv σE b'E flipE).size ≤
      σE.size + b'E.size + flipE.size +
        2 * bits qStart + 2 * bits S.N_send_tot + 2 * bits S.N_recv_tot +
        3 * bits S.N_id + 2 * bits S.N_spk_tot + 1800 := by
  let Δ := (e2eDrvStateTy S ℓ).prod (.prod .bool .bool) :: Γ
  have hf := size_allTestedSessionsFreshBoundedE ℓ S P C K decT encT
    S.N_send_tot S.N_recv_tot S.N_id S.N_spk_tot (Γ := Δ)
    (E2EStateRepr.drvSt (.fst .v0))
  have hwT := size_drvWonE ℓ S P C K decT encT qStart (Γ := Δ) (.fst .v0) (.bool true)
  have hwF := size_drvWonE ℓ S P C K decT encT qStart (Γ := Δ) (.fst .v0) (.bool false)
  simp only [E2EStateRepr.drvSt, Expr.v0, Expr.size, Nat.reduceAdd] at hf hwT hwF
  unfold FreshnessSim.finishPrefixC FreshnessSim.finishPrefixBoundedC
  simp only [E2EStateRepr.drvPaused, E2EStateRepr.drvSt, FreshnessSim.boolXorE,
    Expr.v0, Expr.v1, Comp.size, Expr.size, Nat.reduceAdd]
  omega

section StartAndExtSize

variable {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
  {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "E2EExpr" => Expr (e2eOps ℓ P C K decT encT)

private theorem size_listSnocE (n : ℕ) {O : ReductionDsl.Ops (e2eSig ℓ)} {Γ} {τ : Ty (e2eSig ℓ)}
    (xs : Expr O Γ (.list τ)) (x : Expr O Γ τ) :
    (StartAndExtSmAux.listSnocE n xs x).size ≤ xs.size + x.size + bits n + 6 := by
  have hk := _root_.Computational.Proofs.ReductionDsl.SizeBudgetBridge.bits_succ_le n
  unfold StartAndExtSmAux.listSnocE
  simp only [Expr.size]
  omega

private theorem size_listGetOptE (n : ℕ) {O : ReductionDsl.Ops (e2eSig ℓ)} {Γ} {τ : Ty (e2eSig ℓ)}
    (l : Expr O Γ (.list τ)) (idx : Expr O Γ .nat) :
    (StartAndExtSmAux.listGetOptE n l idx).size ≤ 2 * l.size + idx.size + bits n + 60 := by
  unfold StartAndExtSmAux.listGetOptE
  dsimp only [v, Ext.wk]
  simp only [eLet, Expr.v0, Expr.v1, Expr.v2, Expr.size,
    show bits 0 = 1 from rfl, show bits 1 = 1 from rfl]
  omega

private theorem size_listSetE (n : ℕ) {O : ReductionDsl.Ops (e2eSig ℓ)} {Γ} {τ : Ty (e2eSig ℓ)}
    (l : Expr O Γ (.list τ)) (idx : Expr O Γ .nat) (val : Expr O Γ τ) :
    (StartAndExtSmAux.listSetE n l idx val).size ≤
      2 * l.size + idx.size + val.size + bits n + 70 := by
  unfold StartAndExtSmAux.listSetE
  dsimp only [v, Ext.wk]
  simp only [eLet, Expr.v0, Expr.v1, Expr.v2, Expr.size,
    show bits 0 = 1 from rfl, show bits 1 = 1 from rfl]
  omega

theorem size_promoteSlotKC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (nInsts : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : E2EExpr Γ .nat) (idxOptE : E2EExpr Γ (.opt .nat))
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) :
    (StartAndExtSm.promoteSlotKC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) I₀ nInsts kE idxOptE σE).size ≤
      kE.size + idxOptE.size + σE.size + 2 * bits nInsts + 420 := by
  let τp : Ty (e2eSig ℓ) := .prod .nat (.prod (.opt .nat) (e2eDrvStateTy S ℓ))
  have hg := size_listGetOptE (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) nInsts (Γ := τp :: Γ)
    (StartAndExtSmAux.drvInsts (.snd (.snd (.var .zero)))) (.fst (.var .zero))
  have hs := size_listSetE (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) nInsts
    (Γ := M3Interfaces.e2eModelInstTy S ℓ :: τp :: Γ)
    (StartAndExtSmAux.drvInsts (.snd (.snd (.var (.succ .zero)))))
    (.fst (.var (.succ .zero)))
    (StartAndExtSmAux.miSetGsE (.var .zero) .none)
  dsimp only [τp] at hg hs
  unfold StartAndExtSm.promoteSlotKC StartAndExtSm.promoteSlotKE
  dsimp only [v, Ext.wk]
  simp only [M3Interfaces.defaultPrefixCtxE, StartAndExtSmAux.drvInsts,
    StartAndExtSmAux.drvSetInstsAndPausedE, StartAndExtSmAux.drvBase,
    StartAndExtSmAux.drvCorrPrins, StartAndExtSmAux.drvRevSpks, StartAndExtSmAux.drvInstMeta,
    StartAndExtSmAux.drvSt, StartAndExtSmAux.drvB, StartAndExtSmAux.miIdA, StartAndExtSmAux.miIdB,
    StartAndExtSmAux.miSpkCoins, StartAndExtSmAux.miSetGsE, StartAndExtSmAux.miSid,
    StartAndExtSmAux.miHdr, eLet, eCaseOpt, size_v, size_e2ePureOp, E2EPureOp.opSize,
    List.length_nil, Comp.size, Expr.size]
    at hg hs ⊢
  omega

private theorem size_startAux_e2eSidEqE {Γ} (a b : E2EExpr Γ (sidT S)) :
    (StartAndExtSmAux.e2eSidEqE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      a b).size ≤ a.size + b.size + 140 := by
  unfold StartAndExtSmAux.e2eSidEqE
  dsimp only [v, Ext.wk]
  simp only [eLet, eCaseSum, size_e2ePureOp, E2EPureOp.opSize, Expr.size]
  omega

private theorem size_startAux_hdrEqE {Γ}
    (a b : E2EExpr Γ CryptoVerification.E2E.Costed.hdrT) :
    (StartAndExtSmAux.hdrEqE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      a b).size ≤ a.size + b.size + 160 := by
  unfold StartAndExtSmAux.hdrEqE StartAndExtSmAux.optPu32EqE
  dsimp only [v, Ext.wk]
  simp only [PqxdhSimTypes.hdrIkA, PqxdhSimTypes.hdrEkA, PqxdhSimTypes.hdrSpkId,
    PqxdhSimTypes.hdrOpkId, PqxdhSimTypes.hdrPqId, PqxdhSimTypes.hdrKemCt,
    eLet, eCaseOpt, size_e2ePureOp, E2EPureOp.opSize, Expr.size]
  omega

private theorem size_startAux_bhBaseOpkOkE (nOpks : ℕ) {Γ}
    (dsE : E2EExpr Γ (M3Interfaces.e2eMirrorBaseTy S ℓ))
    (uE : E2EExpr Γ (CryptoVerification.E2E.Costed.FinT S.N_id))
    (jE : E2EExpr Γ (CryptoVerification.E2E.Costed.FinT S.N_recv))
    (bndE : E2EExpr Γ CryptoVerification.E2E.Costed.bundleT) :
    (StartAndExtSmAux.bhBaseOpkOkE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      nOpks dsE uE jE bndE).size ≤
      dsE.size + uE.size + jE.size + bndE.size + bits nOpks + 70 := by
  unfold StartAndExtSmAux.bhBaseOpkOkE
  dsimp only [v, Ext.wk]
  simp only [PqxdhSimTypes.bndOpkB, StartAndExtSmAux.mbOpks, eLet, eCaseOpt, eAny,
    size_e2ePureOp, E2EPureOp.opSize, Expr.size]
  omega

private theorem size_startAux_guardFindBundleE (nBundles : ℕ) {Γ}
    (bundlesE : E2EExpr Γ (.list (M3Interfaces.e2eMirrorBundleEntryTy S)))
    (bndE : E2EExpr Γ CryptoVerification.E2E.Costed.bundleT)
    (hdrE : E2EExpr Γ CryptoVerification.E2E.Costed.hdrT) :
    (StartAndExtSmAux.guardFindBundleE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      nBundles bundlesE bndE hdrE).size ≤
      bundlesE.size + bndE.size + hdrE.size + bits nBundles + 70 := by
  unfold StartAndExtSmAux.guardFindBundleE
  dsimp only [v, Ext.wk]
  simp only [PqxdhSimTypes.bndSpkB, PqxdhSimTypes.bndPqB, PqxdhSimTypes.hdrSpkId,
    PqxdhSimTypes.hdrPqId, optMapE, eLet, eCaseOpt, eFind, size_e2ePureOp, E2EPureOp.opSize,
    Expr.size]
  omega

private theorem size_startAux_guardCheckPrinOpkE (nPrins nOpks : ℕ) {Γ}
    (baseE : E2EExpr Γ (M3Interfaces.e2eMirrorBaseTy S ℓ))
    (ujE : E2EExpr Γ (.prod (CryptoVerification.E2E.Costed.FinT S.N_id)
      (CryptoVerification.E2E.Costed.FinT S.N_recv)))
    (bndE : E2EExpr Γ CryptoVerification.E2E.Costed.bundleT) :
    (StartAndExtSmAux.guardCheckPrinOpkE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      nPrins nOpks baseE ujE bndE).size ≤
      baseE.size + ujE.size + bndE.size + bits nPrins + bits nOpks + 120 := by
  let τp : Ty (e2eSig ℓ) :=
    .prod (M3Interfaces.e2eMirrorBaseTy S ℓ)
      (.prod (.prod (CryptoVerification.E2E.Costed.FinT S.N_id)
        (CryptoVerification.E2E.Costed.FinT S.N_recv)) CryptoVerification.E2E.Costed.bundleT)
  have hopk := size_startAux_bhBaseOpkOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nOpks (Γ := τp :: Γ)
    (.fst (.var .zero)) (.fst (.fst (.snd (.var .zero))))
    (.snd (.fst (.snd (.var .zero)))) (.snd (.snd (.var .zero)))
  dsimp only [τp] at hopk
  unfold StartAndExtSmAux.guardCheckPrinOpkE
  dsimp only [v, Ext.wk]
  simp only [StartAndExtSmAux.mbPrins, PqxdhSimTypes.bndIkB, eLet, eAny,
    size_e2ePureOp, E2EPureOp.opSize, Expr.size] at hopk ⊢
  omega

private theorem size_startAux_guardCorrOkE (nCorr : ℕ) {Γ}
    (corrE : E2EExpr Γ (.list (CryptoVerification.E2E.Costed.FinT S.N_id)))
    (uE : E2EExpr Γ (CryptoVerification.E2E.Costed.FinT S.N_id))
    (bndE : E2EExpr Γ CryptoVerification.E2E.Costed.bundleT) :
    (StartAndExtSmAux.guardCorrOkE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      nCorr corrE uE bndE).size ≤
      corrE.size + uE.size + bndE.size + bits nCorr + 30 := by
  unfold StartAndExtSmAux.guardCorrOkE
  dsimp only [v, Ext.wk]
  simp only [PqxdhSimTypes.bndOpkB, eLet, eCaseOpt, eAny, size_e2ePureOp, E2EPureOp.opSize,
    Expr.size]
  omega

private theorem size_startAux_bhE2EGuardE (qStart nPrins nBundles nOpks nSends : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (sidE : E2EExpr Γ (sidT S)) :
    (StartAndExtSmAux.bhE2EGuardE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      qStart nPrins nBundles nOpks nSends σE sidE).size ≤
      σE.size + sidE.size + 2 * bits qStart + 2 * bits nPrins + bits nBundles +
        bits nOpks + bits nSends + 650 := by
  let τps : Ty (e2eSig ℓ) := .prod (e2eDrvStateTy S ℓ) (sidT S)
  let τsbh : Ty (e2eSig ℓ) := M3Interfaces.e2eMirrorSendEntryTy S ℓ
  let τuj : Ty (e2eSig ℓ) :=
    .prod (CryptoVerification.E2E.Costed.FinT S.N_id)
      (CryptoVerification.E2E.Costed.FinT S.N_recv)
  have hs0 := size_startAux_e2eSidEqE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := M3Interfaces.e2eModelInstTy S ℓ :: τps :: Γ)
    (StartAndExtSmAux.miSid (.var .zero)) (.snd (.var (.succ .zero)))
  have hs1 := size_startAux_e2eSidEqE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := τsbh :: τps :: Γ)
    (.fst (.var .zero)) (.snd (.var (.succ .zero)))
  have hfb := size_startAux_guardFindBundleE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nBundles (Γ := τsbh :: τps :: Γ)
    (StartAndExtSmAux.mbBundles (StartAndExtSmAux.drvBase (.fst (.var (.succ .zero)))))
    (.fst (.snd (.var .zero))) (.snd (.snd (.var .zero)))
  have hcp := size_startAux_guardCheckPrinOpkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nPrins nOpks (Γ := τuj :: τsbh :: τps :: Γ)
    (StartAndExtSmAux.drvBase (.fst (.var (.succ (.succ .zero)))))
    (.var .zero) (.fst (.snd (.var (.succ .zero))))
  have hcc := size_startAux_guardCorrOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nPrins (Γ := τuj :: τsbh :: τps :: Γ)
    (StartAndExtSmAux.drvCorrPrins (.fst (.var (.succ (.succ .zero))))) (.fst (.var .zero))
    (.fst (.snd (.var (.succ .zero))))
  unfold StartAndExtSmAux.bhE2EGuardE
  dsimp only [v, Ext.wk, τps, τsbh, τuj, M3Interfaces.e2eMirrorSendEntryTy,
    M3Interfaces.e2eModelInstTy, M3Interfaces.e2eMirrorBaseTy, e2eDrvStateTy]
    at hs0 hs1 hfb hcp hcc ⊢
  simp only [StartAndExtSmAux.drvInsts, StartAndExtSmAux.drvBase, StartAndExtSmAux.drvCorrPrins,
    StartAndExtSmAux.mbSends, StartAndExtSmAux.mbBundles, StartAndExtSmAux.miSid,
    StartAndExtSmAux.miHdr, PqxdhSimTypes.hdrEkA, eLet, eCaseOpt, eAny, eFind,
    size_e2ePureOp, E2EPureOp.opSize, Expr.size] at hs0 hs1 hfb hcp hcc ⊢
  omega

private theorem size_initFixedSpkBobE {Γ}
    (idsE : E2EExpr Γ (.prod CryptoVerification.E2E.Costed.IdKey
      CryptoVerification.E2E.Costed.IdKey))
    (keysE : E2EExpr Γ (.prod BV256 (.prod (.prod BV256 BV256) BV256))) :
    (StartAndExtSmAux.initFixedSpkBobE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      idsE keysE).size ≤ idsE.size + keysE.size + 105 := by
  unfold StartAndExtSmAux.initFixedSpkBobE
  dsimp only [v, Ext.wk]
  simp only [eLet, size_e2eCryptoOp, size_e2ePureOp, E2EPureOp.opSize, Expr.size,
    show bits 0 = 1 from rfl]
  omega

private theorem size_initFixedSpkAliceE {Γ}
    (idsE : E2EExpr Γ (.prod CryptoVerification.E2E.Costed.IdKey
      CryptoVerification.E2E.Costed.IdKey))
    (keysE : E2EExpr Γ (.prod BV256 (.prod (.prod BV256 BV256) (.prod BV256 BV256)))) :
    (StartAndExtSmAux.initFixedSpkAliceE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      idsE keysE).size ≤ idsE.size + keysE.size + 245 := by
  unfold StartAndExtSmAux.initFixedSpkAliceE
  dsimp only [v, Ext.wk]
  simp only [eLet, eCaseOpt, size_e2eCryptoOp, size_e2ePureOp, E2EPureOp.opSize, Expr.size,
    show bits 0 = 1 from rfl]
  omega

private theorem size_initFixedSpkGsE {Γ}
    (idsE : E2EExpr Γ (.prod CryptoVerification.E2E.Costed.IdKey
      CryptoVerification.E2E.Costed.IdKey))
    (argE : E2EExpr Γ (.prod BV256
      (.prod (.prod (.prod BV256 BV256) (.prod BV256 BV256)) .bool))) :
    (StartAndExtSmAux.initFixedSpkGsE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      idsE argE).size ≤ idsE.size + argE.size + 470 := by
  let τ0 : Ty (e2eSig ℓ) :=
    .prod (.prod CryptoVerification.E2E.Costed.IdKey CryptoVerification.E2E.Costed.IdKey)
      (.prod BV256 (.prod (.prod (.prod BV256 BV256) (.prod BV256 BV256)) .bool))
  have ha := size_initFixedSpkAliceE (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := τ0 :: Γ)
    (.fst (.var .zero)) (.pair (.fst (.snd (.var .zero))) (.fst (.snd (.snd (.var .zero)))))
  have hb := size_initFixedSpkBobE (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := τ0 :: Γ)
    (.fst (.var .zero))
    (.pair (.fst (.snd (.var .zero)))
      (.pair (.fst (.fst (.snd (.snd (.var .zero)))))
        (.snd (.snd (.fst (.snd (.snd (.var .zero))))))))
  unfold StartAndExtSmAux.initFixedSpkGsE
  dsimp only [v, Ext.wk]
  simp only [eLet, Expr.size, show bits 0 = 1 from rfl] at ha hb ⊢
  omega

private theorem size_extractDrKey32E {Γ} (krE : E2EExpr Γ keyIndRT) :
    (StartAndExtSmAux.extractDrKey32E (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      krE).size ≤ krE.size + 90 := by
  unfold StartAndExtSmAux.extractDrKey32E
  dsimp only [v, Ext.wk]
  simp only [eCaseSum, size_e2ePureOp, E2EPureOp.opSize, Expr.size, show bits 32 = 6 from rfl]
  omega

private theorem size_extractSpkSk32E {Γ} (krE : E2EExpr Γ keyIndRT) :
    (StartAndExtSmAux.extractSpkSk32E (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      krE).size ≤ krE.size + 70 := by
  unfold StartAndExtSmAux.extractSpkSk32E
  dsimp only [v, Ext.wk]
  simp only [eCaseSum, size_e2ePureOp, E2EPureOp.opSize, Expr.size, show bits 32 = 6 from rfl]
  omega

private theorem size_finishStartSlotE {Γ}
    (guardHitE : E2EExpr Γ (.prod (sidT S)
      (.prod CryptoVerification.E2E.Costed.hdrT
        (.prod CryptoVerification.E2E.Costed.bundleT
          (.prod (CryptoVerification.E2E.Costed.FinT S.N_id)
            (CryptoVerification.E2E.Costed.FinT S.N_recv))))))
    (argsE : E2EExpr Γ (.prod keyIndRT (.prod keyIndRT (.prod BV256 (.opt .bool))))) :
    (StartAndExtSmAux.finishStartSlotE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      guardHitE argsE).size ≤ guardHitE.size + argsE.size + 750 := by
  let τp : Ty (e2eSig ℓ) :=
    .prod (.prod (sidT S) (.prod CryptoVerification.E2E.Costed.hdrT
      (.prod CryptoVerification.E2E.Costed.bundleT
        (.prod (CryptoVerification.E2E.Costed.FinT S.N_id)
          (CryptoVerification.E2E.Costed.FinT S.N_recv)))))
      (.prod keyIndRT (.prod keyIndRT (.prod BV256 (.opt .bool))))
  let τdk : Ty (e2eSig ℓ) := .prod (.prod BV256 BV256) BV256
  let τin : Ty (e2eSig ℓ) :=
    .prod (.prod CryptoVerification.E2E.Costed.IdKey CryptoVerification.E2E.Costed.IdKey)
      (.prod BV256 (.prod (.prod BV256 BV256) (.prod BV256 BV256)))
  have hdr := size_extractDrKey32E (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := τp :: Γ) (.fst (.snd (.var .zero)))
  have hsk := size_extractSpkSk32E (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := τdk :: τp :: Γ)
    (.fst (.snd (.snd (.var (.succ .zero)))))
  have hgs := size_initFixedSpkGsE (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := .bool :: τin :: BV256 :: τdk :: τp :: Γ)
    (.fst (.var (.succ .zero)))
    (.pair (.fst (.snd (.var (.succ .zero))))
      (.pair (.snd (.snd (.var (.succ .zero)))) (.var .zero)))
  unfold StartAndExtSmAux.finishStartSlotE
  dsimp only [v, Ext.wk]
  simp only [PqxdhSimTypes.hdrIkA, PqxdhSimTypes.bndIkB, PqxdhSimTypes.hdrOpkId,
    eLet, eCaseOpt, size_e2ePureOp, E2EPureOp.opSize, Expr.size] at hdr hsk hgs ⊢
  omega

private theorem size_finishStartSpkGenE (qStart nPrins nBundles nOpks nSends : ℕ) {Γ}
    (bModeE : E2EExpr Γ (.opt .bool))
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (argsE : E2EExpr Γ (.prod (sidT S) (.prod keyIndRT (.prod keyIndRT BV256)))) :
    (StartAndExtSmAux.finishStartSpkGenE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      qStart nPrins nBundles nOpks nSends bModeE σE argsE).size ≤
      bModeE.size + σE.size + argsE.size +
        4 * bits qStart + 2 * bits nPrins + bits nBundles + bits nOpks + bits nSends + 1550 := by
  let τp : Ty (e2eSig ℓ) :=
    .prod (.prod (.opt .bool) (e2eDrvStateTy S ℓ))
          (.prod (sidT S) (.prod keyIndRT (.prod keyIndRT BV256)))
  let τg : Ty (e2eSig ℓ) :=
    .prod CryptoVerification.E2E.Costed.hdrT
      (.prod CryptoVerification.E2E.Costed.bundleT
        (.prod (CryptoVerification.E2E.Costed.FinT S.N_id)
          (CryptoVerification.E2E.Costed.FinT S.N_recv)))
  let τsl : Ty (e2eSig ℓ) :=
    .prod (M3Interfaces.e2eModelInstTy S ℓ) (M3Interfaces.e2eInstMetaTy S ℓ)
  have hg := size_startAux_bhE2EGuardE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) qStart nPrins nBundles nOpks nSends (Γ := τp :: Γ)
    (.snd (.fst (.var .zero))) (.fst (.snd (.var .zero)))
  have hsl := size_finishStartSlotE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := τg :: τp :: Γ)
    (.pair (.fst (.snd (.var (.succ .zero)))) (.var .zero))
    (.pair (.fst (.snd (.snd (.var (.succ .zero)))))
      (.pair (.fst (.snd (.snd (.snd (.var (.succ .zero))))))
        (.pair (.snd (.snd (.snd (.snd (.var (.succ .zero))))))
          (.fst (.fst (.var (.succ .zero)))))))
  have hsn1 := size_listSnocE (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) qStart
    (Γ := τsl :: τg :: τp :: Γ)
    (StartAndExtSmAux.drvInsts (.snd (.fst (.var (.succ (.succ .zero)))))) (.fst (.var .zero))
  have hsn2 := size_listSnocE (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) qStart
    (Γ := τsl :: τg :: τp :: Γ)
    (StartAndExtSmAux.drvInstMeta (.snd (.fst (.var (.succ (.succ .zero)))))) (.snd (.var .zero))
  dsimp only [τp, τg, τsl] at hg hsl hsn1 hsn2
  unfold StartAndExtSmAux.finishStartSpkGenE
  dsimp only [v, Ext.wk]
  simp only [StartAndExtSmAux.drvSetInstsAndMetaE, StartAndExtSmAux.drvBase,
    StartAndExtSmAux.drvCorrPrins, StartAndExtSmAux.drvRevSpks,
    StartAndExtSmAux.drvInsts, StartAndExtSmAux.drvInstMeta,
    eLet, eCaseOpt, size_v, Expr.size] at hg hsl hsn1 hsn2 ⊢
  omega

theorem size_finishStartSpkC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nPrins nBundles nOpks nSends : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (bModeE : E2EExpr Γ (.opt .bool))
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sidE : E2EExpr Γ (sidT S))
    (kr1E kr2E : E2EExpr Γ keyIndRT)
    (acE : E2EExpr Γ BV256) :
    (StartAndExtSm.finishStartSpkC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) I₀ qStart nPrins nBundles nOpks nSends
      bModeE σE sidE kr1E kr2E acE).size ≤
      bModeE.size + σE.size + sidE.size + kr1E.size + kr2E.size + acE.size +
        4 * bits qStart + 2 * bits nPrins + bits nBundles + bits nOpks + bits nSends + 1560 := by
  have hg := size_finishStartSpkGenE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) qStart nPrins nBundles nOpks nSends
    bModeE σE (.pair sidE (.pair kr1E (.pair kr2E acE)))
  unfold StartAndExtSm.finishStartSpkC
  simp only [Comp.size, Expr.size] at hg ⊢
  omega

private theorem size_respNotRevealedE_aux (nCorr : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (imE : E2EExpr Γ (M3Interfaces.e2eInstMetaTy S ℓ))
    (revE : E2EExpr Γ (.list (.prod (CryptoVerification.E2E.Costed.FinT S.N_id)
      (CryptoVerification.E2E.Costed.FinT S.N_recv)))) :
    (M3Interfaces.respNotRevealedE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      nCorr imE revE).size ≤ imE.size + revE.size + bits nCorr + 50 := by
  unfold M3Interfaces.respNotRevealedE
  dsimp only [v, Ext.wk]
  simp only [eLet, eCaseOpt, eAny, size_e2ePureOp, E2EPureOp.opSize, Expr.size]
  omega

private theorem size_bhE2EDrvInstCleanE (qStart nCorr : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (kE : E2EExpr Γ .nat) :
    (StartAndExtSm.bhE2EDrvInstCleanE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      qStart nCorr σE kE).size ≤ σE.size + kE.size + 2 * bits qStart + bits nCorr + 250 := by
  let τp : Ty (e2eSig ℓ) := .prod (e2eDrvStateTy S ℓ) .nat
  have hg1 := size_listGetOptE (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) qStart (Γ := τp :: Γ)
    (StartAndExtSmAux.drvInsts (.fst (.var .zero))) (.snd (.var .zero))
  have hg2 := size_listGetOptE (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) qStart
    (Γ := M3Interfaces.e2eModelInstTy S ℓ :: τp :: Γ)
    (StartAndExtSmAux.drvInstMeta (.fst (.var (.succ .zero)))) (.snd (.var (.succ .zero)))
  have hrn := size_respNotRevealedE_aux (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nCorr
    (Γ := M3Interfaces.e2eInstMetaTy S ℓ :: M3Interfaces.e2eModelInstTy S ℓ :: τp :: Γ)
    (.var .zero) (StartAndExtSmAux.drvRevSpks (.fst (.var (.succ (.succ .zero)))))
  dsimp only [τp] at hg1 hg2 hrn
  unfold StartAndExtSm.bhE2EDrvInstCleanE
  dsimp only [v, Ext.wk]
  simp only [StartAndExtSmAux.drvInsts, StartAndExtSmAux.drvInstMeta,
    StartAndExtSmAux.drvRevSpks, StartAndExtSmAux.miSid, StartAndExtSmAux.imIkACorr,
    isSomeE, StartAndExtSmAux.bhDrvSessionInitPrinE,
    eLet, eCaseOpt, eCaseSum, size_v, Expr.size] at hg1 hg2 hrn ⊢
  omega

private theorem size_corrTblE (nCorr : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (corrPrinsE : E2EExpr Γ (.list (CryptoVerification.E2E.Costed.FinT S.N_id))) :
    (StartAndExtSm.corrTblE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      nCorr corrPrinsE).size ≤ corrPrinsE.size + bits nCorr + 20 := by
  unfold StartAndExtSm.corrTblE
  simp only [Expr.v0, Expr.v1, size_e2ePureOp, E2EPureOp.opSize, Expr.size]
  omega

private theorem size_bhE2EInstIkACorrE (nCorr nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (dE : E2EExpr Γ (M3Interfaces.e2eModelInstTy S ℓ)) :
    (StartAndExtSm.bhE2EInstIkACorrE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      nCorr nPrins σE dE).size ≤ σE.size + dE.size + bits nCorr + bits nPrins + 120 := by
  let τp : Ty (e2eSig ℓ) := .prod (e2eDrvStateTy S ℓ) (M3Interfaces.e2eModelInstTy S ℓ)
  have htbl := size_corrTblE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nCorr (Γ := τp :: Γ)
    (StartAndExtSmAux.drvCorrPrins (.fst (.var .zero)))
  dsimp only [τp] at htbl
  unfold StartAndExtSm.bhE2EInstIkACorrE
  dsimp only [v, Ext.wk]
  simp only [StartAndExtSmAux.drvCorrPrins, StartAndExtSmAux.drvBase, StartAndExtSmAux.mbPrins,
    StartAndExtSmAux.miSid, StartAndExtSmAux.miHdr, PqxdhSimTypes.hdrIkA,
    StartAndExtSmAux.bhDrvSessionInitPrinE, orE, eLet, eCaseOpt, eCaseSum, eAny,
    size_v, size_e2ePureOp, E2EPureOp.opSize, Expr.size] at htbl ⊢
  omega

private theorem size_filterSmQueryE {Γ : List (Ty (e2eSig ℓ))}
    (dE : E2EExpr Γ (M3Interfaces.e2eModelInstTy S ℓ))
    (imE : E2EExpr Γ (M3Interfaces.e2eInstMetaTy S ℓ))
    (sqE : E2EExpr Γ smQT) :
    (StartAndExtSm.filterSmQueryE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      dE imE sqE).size ≤ dE.size + imE.size + sqE.size + 600 := by
  let τp : Ty (e2eSig ℓ) :=
    .prod (M3Interfaces.e2eModelInstTy S ℓ) (.prod (M3Interfaces.e2eInstMetaTy S ℓ) smQT)
  let τpc : Ty (e2eSig ℓ) := .prod .bool (CryptoVerification.E2E.Costed.B 32)
  let τSub : Ty (e2eSig ℓ) :=
    .prod (M3Interfaces.e2eModelInstTy S ℓ) (.prod (M3Interfaces.e2eInstMetaTy S ℓ) τpc)
  let τParsed : Ty (e2eSig ℓ) :=
    .prod CryptoVerification.E2E.Costed.U32
      (.prod CryptoVerification.E2E.Costed.hdrT (CryptoVerification.E2E.Costed.B 32))
  have hhd1 := size_startAux_hdrEqE (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (Γ := τParsed :: τSub :: τpc :: (.sum τpc (.sum τpc .bool)) ::
          (.sum (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
            (.prod CryptoVerification.E2E.Costed.PlainT (.opt CryptoVerification.E2E.Costed.BV512))))
            (.sum τpc (.sum τpc .bool))) :: τp :: Γ)
    (.fst (.snd (.var .zero))) (StartAndExtSmAux.miHdr (.fst (.var (.succ .zero))))
  have hhd2 := size_startAux_hdrEqE (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (Γ := τParsed :: τSub :: τpc :: (.sum τpc .bool) ::
          (.sum τpc (.sum τpc .bool)) ::
          (.sum (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
            (.prod CryptoVerification.E2E.Costed.PlainT (.opt CryptoVerification.E2E.Costed.BV512))))
            (.sum τpc (.sum τpc .bool))) :: τp :: Γ)
    (.fst (.snd (.var .zero))) (StartAndExtSmAux.miHdr (.fst (.var (.succ .zero))))
  dsimp only [τp, τpc, τSub, τParsed] at hhd1 hhd2
  unfold StartAndExtSm.filterSmQueryE StartAndExtSm.filterDeliverE StartAndExtSm.filterInjectE
  dsimp only [v, Ext.wk]
  simp only [StartAndExtSm.mkDeliverSmQE, StartAndExtSm.mkInjectSmQE,
    StartAndExtSmAux.imBobAccepted, StartAndExtSmAux.miSid, StartAndExtSmAux.miHdr,
    StartAndExtSmAux.bhInitRegIdE, StartAndExtSmAux.bhDrvSessionInitPrinE,
    optMapE, isSomeE, eLet, eCaseSum, eCaseOpt, size_v, size_e2ePureOp, E2EPureOp.opSize,
    Expr.size] at hhd1 hhd2 ⊢
  omega

private theorem size_forwardExtSmC {Γ : List (Ty (e2eSig ℓ))}
    (sqE : E2EExpr Γ smQT) :
    (StartAndExtSm.forwardExtSmC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      sqE).size ≤ sqE.size + 80 := by
  unfold StartAndExtSm.forwardExtSmC
  dsimp only [caseSumV, bindV, v, Ext.wk]
  simp only [Comp.size, Expr.size]
  omega

theorem size_extSmStepC (qStart nCorr nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : E2EExpr Γ .nat)
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (sqE : E2EExpr Γ smQT) :
    (StartAndExtSm.extSmStepC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      qStart nCorr nPrins kE σE sqE).size ≤
      kE.size + σE.size + sqE.size +
        6 * bits qStart + 3 * bits nCorr + 2 * bits nPrins + 1800 := by
  let τp : Ty (e2eSig ℓ) := .prod .nat (.prod (e2eDrvStateTy S ℓ) smQT)
  have hcl := size_bhE2EDrvInstCleanE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) qStart nCorr (Γ := τp :: Γ) (.fst (.snd (.var .zero)))
    (.fst (.var .zero))
  have hg1 := size_listGetOptE (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) qStart (Γ := τp :: Γ)
    (StartAndExtSmAux.drvInsts (.fst (.snd (.var .zero)))) (.fst (.var .zero))
  have hg2 := size_listGetOptE (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) qStart
    (Γ := M3Interfaces.e2eModelInstTy S ℓ :: τp :: Γ)
    (StartAndExtSmAux.drvInstMeta (.fst (.snd (.var (.succ .zero))))) (.fst (.var (.succ .zero)))
  have hcr1 := size_bhE2EInstIkACorrE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nCorr nPrins
    (Γ := M3Interfaces.e2eInstMetaTy S ℓ :: M3Interfaces.e2eModelInstTy S ℓ :: τp :: Γ)
    (.fst (.snd (.var (.succ (.succ .zero))))) (.var (.succ .zero))
  have hs1 := size_listSetE (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) qStart
    (Γ := M3Interfaces.e2eInstMetaTy S ℓ :: M3Interfaces.e2eModelInstTy S ℓ :: τp :: Γ)
    (StartAndExtSmAux.drvInstMeta (.fst (.snd (.var (.succ (.succ .zero))))))
    (.fst (.var (.succ (.succ .zero))))
    (.pair (.bool true) (.pair (.bool true) (.snd (.snd (.var .zero)))))
  have hfl := size_filterSmQueryE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (Γ := M3Interfaces.e2eInstMetaTy S ℓ :: M3Interfaces.e2eModelInstTy S ℓ :: τp :: Γ)
    (.var (.succ .zero)) (.var .zero) (.snd (.snd (.var (.succ (.succ .zero)))))
  have hfw := size_forwardExtSmC (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (Γ := smQT :: M3Interfaces.e2eInstMetaTy S ℓ :: M3Interfaces.e2eModelInstTy S ℓ :: τp :: Γ)
    (.var .zero)
  have hcr2 := size_bhE2EInstIkACorrE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nCorr nPrins
    (Γ := CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT ::
          smQT :: M3Interfaces.e2eInstMetaTy S ℓ :: M3Interfaces.e2eModelInstTy S ℓ :: τp :: Γ)
    (.fst (.snd (.var (.succ (.succ (.succ (.succ .zero)))))))
    (.var (.succ (.succ (.succ .zero))))
  have hs2 := size_listSetE (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) qStart
    (Γ := CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT ::
          smQT :: M3Interfaces.e2eInstMetaTy S ℓ :: M3Interfaces.e2eModelInstTy S ℓ :: τp :: Γ)
    (StartAndExtSmAux.drvInstMeta (.fst (.snd (.var (.succ (.succ (.succ (.succ .zero))))))))
    (.fst (.var (.succ (.succ (.succ (.succ .zero))))))
    (.ite
      (.and (.not (StartAndExtSmAux.imBobAccepted (.var (.succ (.succ .zero)))))
        (StartAndExtSm.isBobAcceptSmRE (.var (.succ .zero)) (.var .zero)))
      (.pair (.bool true)
        (.pair
          (StartAndExtSm.bhE2EInstIkACorrE nCorr nPrins
            (.fst (.snd (.var (.succ (.succ (.succ (.succ .zero)))))))
            (.var (.succ (.succ (.succ .zero)))))
          (.snd (.snd (.var (.succ (.succ .zero)))))))
      (.var (.succ (.succ .zero))))
  dsimp only [τp] at hcl hg1 hg2 hcr1 hs1 hfl hfw hcr2 hs2
  unfold StartAndExtSm.extSmStepC
  dsimp only [letV, caseOptV, bindV, v, Ext.wk]
  simp only [StartAndExtSmAux.drvInsts, StartAndExtSmAux.drvInstMeta,
    StartAndExtSmAux.drvSetInstMetaE, StartAndExtSmAux.drvBase, StartAndExtSmAux.drvCorrPrins,
    StartAndExtSmAux.drvRevSpks, StartAndExtSmAux.imBobAccepted, StartAndExtSm.isBobRecvSmQE,
    StartAndExtSm.isBobAcceptSmRE,
    eLet, eCaseOpt, eCaseSum, size_v, Comp.size, Expr.size]
    at hcl hg1 hg2 hcr1 hs1 hfl hfw hcr2 hs2 ⊢
  omega

end StartAndExtSize

end SizeBounds

/-- Concrete `DrvStateGuardFreshIface` wired from `E2EStateRepr` and `FreshnessSim`. -/
def drvStateGuardFreshIface (ℓ : ℕ) (S : SignalPqxdh.Setup) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    DrvStateGuardFreshIface ℓ S P C K decT encT where
  emptyDrvStateE := fun {_} bE =>
    E2EStateRepr.emptyDrvStateE (ℓ := ℓ) (S := S) bE
  emptyDrvStateCost := 40
  emptyDrvStateE_cost := fun {_} bE =>
    Nat.le_of_eq (E2EStateRepr.cost_emptyDrvStateE (ℓ := ℓ) (S := S) bE)
  emptyDrvStateE_eval := fun {_} bE ρ =>
    E2EStateRepr.eval_emptyDrvStateE (ℓ := ℓ) (S := S) bE ρ
  initKindC := fun {_} {_} I₀ {_} =>
    E2EStateRepr.initKindC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) I₀
  initKindCost := 48
  initKindC_cost := fun {_} {_} I₀ {_} =>
    E2EStateRepr.cost_initKindC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) I₀
  initKindC_queries := fun {_} {_} I₀ {_} w =>
    E2EStateRepr.queries_initKindC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) I₀ w
  initKindC_eval := fun {_} {_} I₀ {_} ρ =>
    E2EStateRepr.eval_initKindC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) I₀ ρ
  kiQueryOkE := fun nPrins qStart {_} σE kqE =>
    E2EStateRepr.kiQueryOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) nPrins qStart σE kqE
  kiQueryOkCost := fun nPrins qStart => 168 * nPrins + 24 * qStart + 560
  kiQueryOkE_cost := fun nPrins qStart {_} σE kqE =>
    le_trans
      (E2EStateRepr.cost_kiQueryOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
        (decT := decT) (encT := encT) nPrins qStart σE kqE)
      (add_le_group3 _ _ _ _)
  kiQueryOkE_eval := fun nPrins qStart {_} σE kqE ρ _ kq hP hσ hkq hlen hMeta => by
    have h := E2EStateRepr.eval_kiQueryOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) nPrins qStart hP σE kqE ρ hσ hkq hlen hMeta
    cases kq <;> exact h
  mirrorE := fun {_} σE kqE krE =>
    E2EStateRepr.bhE2EMirrorE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) σE kqE krE
  mirrorCost := 800
  mirrorE_cost := fun {_} σE kqE krE =>
    E2EStateRepr.cost_bhE2EMirrorE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) σE kqE krE
  mirrorE_eval := fun {_} σE kqE krE ρ σ kq kr hσ hkq hkr =>
    E2EStateRepr.eval_bhE2EMirrorE_enc (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) σE kqE krE ρ σ kq kr hσ hkq hkr
  prepStartSpkE := fun qStart nPrins nBundles nOpks nSends {_} σE sidE =>
    E2EStateRepr.prepStartSpkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) qStart nPrins nBundles nOpks nSends σE sidE
  prepStartSpkCost := fun qStart nPrins nBundles nOpks nSends =>
    361 * qStart + 300 * nSends + 3300 * nBundles + 112 * nPrins + 160 * nOpks + 228
  prepStartSpkE_cost := fun qStart nPrins nBundles nOpks nSends {_} σE sidE =>
    le_trans
      (E2EStateRepr.cost_prepStartSpkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
        (decT := decT) (encT := encT) qStart nPrins nBundles nOpks nSends σE sidE)
      (add_le_group6 _ _ _ _ _ _ _)
  prepStartSpkE_eval := fun qStart nPrins nBundles nOpks nSends nCorr {_} σE sidE ρ σ sid hσ hsid hBnd
      hCorrN =>
    E2EStateRepr.eval_prepStartSpkE_mirrorBounded (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) qStart nPrins nBundles nOpks nSends nCorr σE sidE ρ σ sid
      hσ hsid
      ⟨hBnd.prins_le, hBnd.bundles_le, hBnd.opks_le, hBnd.sends_le,
       hBnd.corrPrins_le, hBnd.insts_le, hBnd.instMeta_le⟩ hCorrN
  drvWonE := fun qStart {_} σE bE =>
    FreshnessSim.drvWonE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) qStart σE bE
  drvWonCost := FreshnessSim.drvWonCost
  drvWonE_cost := fun qStart {_} σE bE =>
    FreshnessSim.cost_drvWonE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) qStart σE bE
  drvWonE_eval := fun qStart {_} σE bE ρ _ hσ hInsts =>
    FreshnessSim.eval_drvWonE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) qStart σE bE ρ hσ hInsts
  finishKindE := fun qStart {_} σE b'E =>
    FreshnessSim.finishKindE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) qStart σE b'E
  finishKindCost := FreshnessSim.finishKindCost
  finishKindE_cost := fun qStart {_} σE b'E =>
    FreshnessSim.cost_finishKindE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) qStart σE b'E
  finishKindE_eval := fun qStart {_} σE b'E ρ _ hσ hInsts =>
    FreshnessSim.eval_finishKindE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) qStart σE b'E ρ hσ hInsts
  finishPrefixC := fun {_} {_} I₀ qStart nAdv {_} σE b'E flipE =>
    FreshnessSim.finishPrefixC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) I₀ qStart nAdv σE b'E flipE
  finishPrefixCost := FreshnessSim.finishPrefixCost S
  finishPrefixC_cost := fun {_} {_} I₀ qStart nAdv {_} σE b'E flipE =>
    FreshnessSim.cost_finishPrefixC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) I₀ qStart nAdv σE b'E flipE
  finishPrefixC_queries := fun {_} {_} I₀ qStart nAdv {_} σE b'E flipE w =>
    FreshnessSim.queries_finishPrefixC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) I₀ qStart nAdv σE b'E flipE w
  finishPrefixC_eval := fun {_} {_} I₀ qStart nAdv {_} σE b'E flipE ρ σ ki qep hP hσ hInsts hReach =>
    FreshnessSim.eval_finishPrefixC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) I₀ qStart nAdv σE b'E flipE ρ σ ki qep hP hσ hInsts hReach.setup

/-- Complete concrete `M3SubprogramsIface` bundle over `e2eSig ℓ` and `e2eOps ℓ P C K decT encT`. -/
def m3Subprograms (ℓ : ℕ) (S : SignalPqxdh.Setup) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    M3SubprogramsIface ℓ S P C K decT encT where
  pqxdh := pqxdhSimIface ℓ S P C K decT encT
  dr := concreteDrSessionSim ℓ P C K decT encT
  drv := drvStateGuardFreshIface ℓ S P C K decT encT
  localSm := localSessionStepIface (S := S) (concreteDrSessionSim ℓ P C K decT encT)
  startExt := startAndExtSmIface ℓ S P C K decT encT

@[simp] theorem m3Subprograms_pqxdh_stepCost (ℓ : ℕ) (S : SignalPqxdh.Setup) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (nAdv : ℕ) :
    (m3Subprograms ℓ S P C K decT encT).pqxdh.stepCost nAdv = pqxdh1KeyRealStepCost S nAdv := rfl

@[simp] theorem m3Subprograms_dr_oracleStepCost (ℓ : ℕ) (S : SignalPqxdh.Setup) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (qBound qep : ℕ) :
    (m3Subprograms ℓ S P C K decT encT).dr.oracleStepCost qBound qep =
      drOracleStepCost ℓ qBound qep := rfl

@[simp] theorem m3Subprograms_localSm_stepLocalSmCost (ℓ : ℕ) (S : SignalPqxdh.Setup) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qStart nCorr nPrins qBound qep : ℕ) :
    (m3Subprograms ℓ S P C K decT encT).localSm.stepLocalSmCost qStart nCorr nPrins qBound qep =
      drOracleStepCost ℓ qBound qep + 190 * qStart + 160 * nCorr + 160 * nPrins + 9500 := rfl

@[simp] theorem m3Subprograms_startExt_finishStartSpkCost (ℓ : ℕ) (S : SignalPqxdh.Setup)
    {Pt : Type} (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qStart nPrins nBundles nOpks nSends : ℕ) :
    (m3Subprograms ℓ S P C K decT encT).startExt.finishStartSpkCost
      qStart nPrins nBundles nOpks nSends =
      finishStartSpkCost qStart nPrins nBundles nOpks nSends := rfl

@[simp] theorem m3Subprograms_startExt_promoteSlotKCost (ℓ : ℕ) (S : SignalPqxdh.Setup)
    {Pt : Type} (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (nInsts : ℕ) :
    (m3Subprograms ℓ S P C K decT encT).startExt.promoteSlotKCost nInsts =
      promoteSlotKCost nInsts := rfl

@[simp] theorem m3Subprograms_startExt_extSmStepCost (ℓ : ℕ) (S : SignalPqxdh.Setup)
    {Pt : Type} (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (qStart nCorr nPrins : ℕ) :
    (m3Subprograms ℓ S P C K decT encT).startExt.extSmStepCost qStart nCorr nPrins =
      extSmStepCost ℓ qStart nCorr nPrins := rfl

end Computational.Proofs.E2E.Dsl.M3Subprograms
