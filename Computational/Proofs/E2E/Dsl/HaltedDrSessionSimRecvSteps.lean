/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.DrSessionSim -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.HaltedDrSessionLifter -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.HaltedDrTrackerDsl -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.LocalSessionStep -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.SpqrSim -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
import Computational.Proofs.E2E.Dsl.M3SessionSize

/-!
# Online-Halted Double Ratchet Receive, Inject, and Corrupt Step Arms

Lifts the single-session `deliver`, `inject`, and `corr` arms of `drOracleStepC` into
`atomicE2EOps`, updating `KemFailSessionTrack` on `deliver` and proving static cost/size bounds
together with `SmReachBounded` and `KemBridgeTrackInv` preservation.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.HaltedDrSessionSimRecvSteps

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp
  atomicSig atomicE2EOps atomicBaseSamplers B GhostStT
  recvResultEnc smQT smRT partyToBool bits)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (RecvResult GameState deliverR injectR corrR partyEnc)
open CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey GhostState)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes BHE2ESmResp bhPackSmResp liftStateT
  paramsIdsWithSpqr sessionSchemeFixedSpk configRefuseEarlyBobCorr)
open CryptoVerification.E2E.Costed (e2eSig e2eOps)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (stepAIface)
open Computational.Proofs.E2E.Dsl.SmReachInv (SmReachBounded)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (e2eGsTy e2eGsEnc partyToBool_eq_partyEnc)
open Computational.Proofs.E2E.Dsl.DrSessionSim (e2eStepACoinSamplers
  drDlArmC drIjArmC drCrArmC drOracleStepC drSessionSimIface
  drDlArmC_cost drIjArmC_cost drCrArmC_cost
  drDlArmC_eval drIjArmC_eval drCrArmC_eval)
open Computational.Proofs.E2E.Dsl.HaltedDrSessionLifter
  (emptyTargetE2EIface liftE2ECoinComp liftE2ECoinComp_queries_zero
   liftE2ECoinComp_cost liftE2ECoinComp_size liftE2ECoinComp_eval_prob)
open Computational.Proofs.E2E.Dsl.HaltedDrTrackerDsl
  (sessHTy sessHEnc KemBridgeTrackInv kemBridgeTrackInv_mono
   findRevHonestWireIdxAtomicE kemOnDeliverPostAtomicE
   findRevHonestWireIdxAtomicE_eval kemOnDeliverPostAtomicE_eval_and_inv)
open Computational.Proofs.E2E.Dsl.LocalSessionStep (smReachBounded_step_oracleImplR)
open Computational.Proofs.E2E.Dsl.M3SessionSize (size_drOracleStepC_concrete)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
  (liftTy liftVal liftEnv renExpr renComp renComp_queries renComp_cost renComp_eval pullEnv)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge
  (KemFailSessionTrack deliverRTrackHalted oracleImplRTrackHalted)
open Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (e2eEmbed findRevHonestWireIdxE_cost_le findRevHonestWireIdxE_size_le
   kemOnDeliverPostE_cost_le kemOnDeliverPostE_size_le)

/-! ## Atomic encodings and renaming helpers -/

@[expose, reducible] def gsAtomicTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  liftTy (Pt := Pt) (e2eGsTy ℓ)

@[expose, reducible] def gsAtomicEnc {ℓ : ℕ} {Pt : Type}
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) : (gsAtomicTy ℓ Pt).denote :=
  liftVal (Pt := Pt) (e2eGsEnc gs)

@[expose, reducible] def smRecvTailTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .sum (.prod .bool (B (ℓ := ℓ) (Pt := Pt) 32))
    (.sum (.prod .bool (B (ℓ := ℓ) (Pt := Pt) 32)) .bool)

@[expose, reducible] def smRecvTailEnc {ℓ : ℕ} {Pt : Type} :
    (Party × Bytes) ⊕ ((Party × Bytes) ⊕ Party) → (smRecvTailTy ℓ Pt).denote
  | .inl (Q, w) => .inl (partyToBool Q, w)
  | .inr (.inl (Q, w)) => .inr (.inl (partyToBool Q, w))
  | .inr (.inr Q) => .inr (.inr (partyToBool Q))

@[expose, reducible] def smRecvTailToSpec {ℓ : ℕ} {PQC : Type} :
    (Party × Bytes) ⊕ ((Party × Bytes) ⊕ Party) →
    (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) PQC Bytes).Domain
  | .inl dl => .inl (.inl (.inr dl))
  | .inr (.inl ij) => .inl (.inr ij)
  | .inr (.inr cr) => .inr cr

@[expose, reducible] def packAtomicSmRespEnc {ℓ : ℕ} {Pt : Type}
    (br : BHE2ESmResp ℓ) : (smRT (ℓ := ℓ) (Pt := Pt) GhostStT).denote :=
  (br.1, (br.2.1.map recvResultEnc, br.2.2))

private theorem renExpr_size {S₀ : Sig} {O : Ops S₀} {Γ₁ Γ₂ : List (Ty S₀)} {t : Ty S₀}
    (f : ∀ {u}, Var Γ₁ u → Var Γ₂ u) (e : Expr O Γ₁ t) :
    (renExpr f e).size = e.size := by
  induction e generalizing Γ₂ <;> simp [renExpr, Expr.size, *]

private theorem renComp_size {S₀ : Sig} {O : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {Γ₁ Γ₂ : List (Ty S₀)} {t : Ty S₀}
    (f : ∀ {u}, Var Γ₁ u → Var Γ₂ u) (c : Comp O I₀ Γ₁ t) :
    (renComp f c).size = c.size := by
  induction c generalizing Γ₂ <;> simp [renComp, Comp.size, renExpr_size, *]

@[expose] def wk5Ren {S₀ : Sig} {a b c d e : Ty S₀} {Γ : List (Ty S₀)} :
    ∀ {u}, Var [a, b, c, d, e] u → Var (a :: b :: c :: d :: e :: Γ) u
  | _, .zero => .zero
  | _, .succ .zero => .succ .zero
  | _, .succ (.succ .zero) => .succ (.succ .zero)
  | _, .succ (.succ (.succ .zero)) => .succ (.succ (.succ .zero))
  | _, .succ (.succ (.succ (.succ .zero))) => .succ (.succ (.succ (.succ .zero)))

@[expose] def wk6Ren {S₀ : Sig} {a b c d e f : Ty S₀} {Γ : List (Ty S₀)} :
    ∀ {u}, Var [a, b, c, d, e, f] u → Var (a :: b :: c :: d :: e :: f :: Γ) u
  | _, .zero => .zero
  | _, .succ .zero => .succ .zero
  | _, .succ (.succ .zero) => .succ (.succ .zero)
  | _, .succ (.succ (.succ .zero)) => .succ (.succ (.succ .zero))
  | _, .succ (.succ (.succ (.succ .zero))) => .succ (.succ (.succ (.succ .zero)))
  | _, .succ (.succ (.succ (.succ (.succ .zero)))) => .succ (.succ (.succ (.succ (.succ .zero))))

private theorem pullEnv_wk5Ren {S₀ : Sig} {a b c d e : Ty S₀} {Γ : List (Ty S₀)}
    (va : a.denote) (vb : b.denote) (vc : c.denote) (vd : d.denote) (ve : e.denote) (ρ : Env Γ) :
    pullEnv (wk5Ren (Γ := Γ)) (.cons va (.cons vb (.cons vc (.cons vd (.cons ve ρ))))) =
      .cons va (.cons vb (.cons vc (.cons vd (.cons ve .nil)))) := rfl

private theorem pullEnv_wk6Ren {S₀ : Sig} {a b c d e f : Ty S₀} {Γ : List (Ty S₀)}
    (va : a.denote) (vb : b.denote) (vc : c.denote) (vd : d.denote) (ve : e.denote)
    (vf : f.denote) (ρ : Env Γ) :
    pullEnv (wk6Ren (Γ := Γ)) (.cons va (.cons vb (.cons vc (.cons vd (.cons ve (.cons vf ρ)))))) =
      .cons va (.cons vb (.cons vc (.cons vd (.cons ve (.cons vf .nil))))) := rfl

private theorem liftVal_smRRecv {ℓ : ℕ} {Pt : Type} (rr : Option (RecvResult (Plain ℓ))) :
    liftVal (ℓ := ℓ) (Pt := Pt)
      (t := CryptoVerification.E2E.Costed.smRT (ℓ := ℓ) CryptoVerification.E2E.Costed.GhostStT)
      (none, (rr.map CryptoVerification.E2E.Costed.recvResultEnc, none)) =
      ((none, (rr.map (recvResultEnc (ℓ := ℓ) (Pt := Pt)), none)) :
        (smRT (ℓ := ℓ) (Pt := Pt) GhostStT).denote) := by
  cases rr with
  | none => rfl
  | some r =>
    cases r with
    | rejected => rfl
    | accepted t i m => cases m <;> rfl

private theorem liftVal_smRCorr (ℓ : ℕ) {Pt : Type} (st? : Option (GhostState Bytes)) :
    liftVal (ℓ := ℓ) (Pt := Pt)
      (t := CryptoVerification.E2E.Costed.smRT (ℓ := ℓ) CryptoVerification.E2E.Costed.GhostStT)
      ((none, (none, st?)) :
        (CryptoVerification.E2E.Costed.smRT (ℓ := ℓ) CryptoVerification.E2E.Costed.GhostStT).denote) =
      ((none, (none, st?)) : (smRT (ℓ := ℓ) (Pt := Pt) GhostStT).denote) := by
  cases st? <;> rfl

private theorem map_liftP_eq {S₀ : Sig} {ι : Type} {T : OracleSpec ι}
    (I₀ : Iface S₀ T) {α β : Type} (f : α → β) (m : ProbComp α) :
    f <$> I₀.liftP m = I₀.liftP (f <$> m) := by
  simp [Iface.liftP, map_eq_bind_pure_comp, simulateQ_bind, simulateQ_pure]

private theorem findIdx_deliver_eq (hw : List (Bytes × Party)) (w : Bytes) (Q : Party) :
    @List.findIdx? (Bytes × Party)
      (fun wp => @BEq.beq Bytes (@instBEqOfDecidableEq Bytes inferInstance) wp.1 w && wp.2 == Q.other)
      hw.reverse =
    hw.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) := by
  congr 1; ext ⟨x, P⟩
  have hx : @BEq.beq Bytes (@instBEqOfDecidableEq Bytes inferInstance) x w = (x == w) := by
    rw [Bool.eq_iff_iff]
    change (decide (x = w) = true) ↔ ((x == w) = true)
    simp
  rw [hx]

private theorem liftStateT_run_state {σ τ α : Type}
    (x : StateT σ ProbComp α) (s : σ) (t : τ) :
    ((liftStateT (n := StateT τ ProbComp) x).run s).run t = (x.run s >>= fun a => pure (a, t)) :=
  rfl

/-! ## Un-halted subterm wrappers -/

abbrev e2eTTop (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (e2eGsTy ℓ) CryptoVerification.E2E.Costed.smQT

abbrev e2eR1T (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .sum (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.prod CryptoVerification.E2E.Costed.PlainT (.opt CryptoVerification.E2E.Costed.BV512))))
    (.sum (.prod .bool (CryptoVerification.E2E.Costed.B 32))
      (.sum (.prod .bool (CryptoVerification.E2E.Costed.B 32)) .bool))

abbrev e2eR2T (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .sum (.prod .bool (CryptoVerification.E2E.Costed.B 32))
    (.sum (.prod .bool (CryptoVerification.E2E.Costed.B 32)) .bool)

abbrev e2eR3T (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .sum (.prod .bool (CryptoVerification.E2E.Costed.B 32)) .bool

abbrev e2eDlArgT (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod .bool (CryptoVerification.E2E.Costed.B 32)

private def dummySmQVal {ℓ : ℕ} : (CryptoVerification.E2E.Costed.smQT (ℓ := ℓ)).denote :=
  .inr (.inr (.inr (.inr false)))

private def dummyR1Val {ℓ : ℕ} : (e2eR1T ℓ).denote := .inr (.inr (.inr false))
private def dummyR2Val {ℓ : ℕ} : (e2eR2T ℓ).denote := .inr (.inr false)
private def dummyR3Val {ℓ : ℕ} : (e2eR3T ℓ).denote := .inr false

@[expose] def dummySmQE {ℓ : ℕ} {Pt : Type} {O : Ops (atomicSig ℓ Pt)} {Γ : List (Ty (atomicSig ℓ Pt))} :
    Expr O Γ (smQT (ℓ := ℓ) (Pt := Pt)) :=
  .inr (.inr (.inr (.inr (.bool false))))

@[expose] def dummyR1E {ℓ : ℕ} {Pt : Type} {O : Ops (atomicSig ℓ Pt)} {Γ : List (Ty (atomicSig ℓ Pt))} :
    Expr O Γ (liftTy (Pt := Pt) (e2eR1T ℓ)) :=
  .inr (.inr (.inr (.bool false)))

@[expose] def dummyR2E {ℓ : ℕ} {Pt : Type} {O : Ops (atomicSig ℓ Pt)} {Γ : List (Ty (atomicSig ℓ Pt))} :
    Expr O Γ (liftTy (Pt := Pt) (e2eR2T ℓ)) :=
  .inr (.inr (.bool false))

@[expose] def dummyR3E {ℓ : ℕ} {Pt : Type} {O : Ops (atomicSig ℓ Pt)} {Γ : List (Ty (atomicSig ℓ Pt))} :
    Expr O Γ (liftTy (Pt := Pt) (e2eR3T ℓ)) :=
  .inr (.bool false)

@[expose] def dlCoreUnlifted (ℓ : ℕ) {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (q : ℕ) :
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ (emptyTargetE2EIface ℓ))
      [e2eDlArgT ℓ, e2eR2T ℓ, e2eR1T ℓ, e2eTTop ℓ, e2eTTop ℓ]
      (.prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT) (e2eGsTy ℓ)) :=
  drDlArmC (spqrDslHooks ℓ P C K decT encT)
    (e2eStepACoinSamplers ℓ P C K decT encT (emptyTargetE2EIface ℓ))
    q (.fst .v3) .v0

@[expose] def ijCoreUnlifted (ℓ : ℕ) {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (q qep : ℕ) :
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ (emptyTargetE2EIface ℓ))
      [e2eDlArgT ℓ, e2eR3T ℓ, e2eR2T ℓ, e2eR1T ℓ, e2eTTop ℓ, e2eTTop ℓ]
      (.prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT) (e2eGsTy ℓ)) :=
  drIjArmC (spqrDslHooks ℓ P C K decT encT)
    (e2eStepACoinSamplers ℓ P C K decT encT (emptyTargetE2EIface ℓ))
    q (2 + 1) qep (.fst .v4) .v0

@[expose] def crCoreUnlifted (ℓ : ℕ) {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (q : ℕ) :
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ (emptyTargetE2EIface ℓ))
      [.bool, e2eR3T ℓ, e2eR2T ℓ, e2eR1T ℓ, e2eTTop ℓ, e2eTTop ℓ]
      (.prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT) (e2eGsTy ℓ)) :=
  drCrArmC (I := stepAIface ℓ (emptyTargetE2EIface ℓ)) q (.fst .v4) .v0

private theorem size_dl_ij_cr_core (ℓ : ℕ) {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (q qep : ℕ) :
    (dlCoreUnlifted ℓ P C K decT encT q).size +
      (ijCoreUnlifted ℓ P C K decT encT q qep).size +
      (crCoreUnlifted ℓ P C K decT encT q).size ≤
        17 * bits q + 5 * bits qep + 32000 ∧
    (dlCoreUnlifted ℓ P C K decT encT q).size ≤ 17 * bits q + 32000 ∧
    (ijCoreUnlifted ℓ P C K decT encT q qep).size ≤ 17 * bits q + 5 * bits qep + 32000 ∧
    (crCoreUnlifted ℓ P C K decT encT q).size ≤ 17 * bits q + 32000 := by
  have h0 := size_drOracleStepC_concrete (I₀ := emptyTargetE2EIface ℓ) q 0
    (.fst .v0 : Expr (e2eOps ℓ P C K decT encT) [e2eTTop ℓ] (e2eGsTy ℓ)) (.snd .v0)
  have hqep := size_drOracleStepC_concrete (I₀ := emptyTargetE2EIface ℓ) q qep
    (.fst .v0 : Expr (e2eOps ℓ P C K decT encT) [e2eTTop ℓ] (e2eGsTy ℓ)) (.snd .v0)
  have hb0 : bits 0 = 1 := rfl
  dsimp only [drSessionSimIface, drOracleStepC, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at h0 hqep
  rw [hb0] at h0
  dsimp only [dlCoreUnlifted, ijCoreUnlifted, crCoreUnlifted, Expr.v0, Expr.v3, Expr.v4]
  omega

@[expose] def runLiftedDlCore {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (dlArgE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod .bool (B 32))) :
    Comp (atomicE2EOps ℓ P C K decT encT) I Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (gsAtomicTy ℓ Pt)) :=
  .bind (.ret (.pair gsE dlArgE))
    (.bind (.ret (.pair (.fst .v0) dummySmQE))
      (.bind (.ret .v0)
        (.bind (.ret dummyR1E)
          (.bind (.ret dummyR2E)
            (.bind (.ret (.snd .v4))
              (renComp wk5Ren
                (liftE2ECoinComp (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
                  (decT := decT) (encT := encT) I hsmp
                  (dlCoreUnlifted ℓ P C K decT encT q))))))))

@[expose] def runLiftedIjCore {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (ijArgE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod .bool (B 32))) :
    Comp (atomicE2EOps ℓ P C K decT encT) I Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (gsAtomicTy ℓ Pt)) :=
  .bind (.ret (.pair gsE ijArgE))
    (.bind (.ret (.pair (.fst .v0) dummySmQE))
      (.bind (.ret .v0)
        (.bind (.ret dummyR1E)
          (.bind (.ret dummyR2E)
            (.bind (.ret dummyR3E)
              (.bind (.ret (.snd .v5))
                (renComp wk6Ren
                  (liftE2ECoinComp (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
                    (decT := decT) (encT := encT) I hsmp
                    (ijCoreUnlifted ℓ P C K decT encT q qep)))))))))

@[expose] def runLiftedCrCore {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (crArgE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool) :
    Comp (atomicE2EOps ℓ P C K decT encT) I Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (gsAtomicTy ℓ Pt)) :=
  .bind (.ret (.pair gsE crArgE))
    (.bind (.ret (.pair (.fst .v0) dummySmQE))
      (.bind (.ret .v0)
        (.bind (.ret dummyR1E)
          (.bind (.ret dummyR2E)
            (.bind (.ret dummyR3E)
              (.bind (.ret (.snd .v5))
                (renComp wk6Ren
                  (liftE2ECoinComp (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
                    (decT := decT) (encT := encT) I hsmp
                    (crCoreUnlifted ℓ P C K decT encT q)))))))))

/-! ## Halted `deliver`, `inject`, `corr`, and combined tail arms -/

@[expose] def haltedDrDlArmC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (dlArgE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod .bool (B 32))) :
    Comp (atomicE2EOps ℓ P C K decT encT) I Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (.prod (gsAtomicTy ℓ Pt) (sessHTy ℓ Pt))) :=
  .bind (.ret (.pair gsE (.pair shE dlArgE)))
    (.bind (.ret (findRevHonestWireIdxAtomicE q
        (.snd (.fst (.snd .v0))) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))))
      (.bind (runLiftedDlCore I hsmp q (.fst .v1) (.snd (.snd .v1)))
        (.ret (.pair (.fst .v0)
          (.pair (.snd .v0)
            (.pair (kemOnDeliverPostAtomicE q
                (.fst (.snd (.snd .v2))) .v1 (.fst (.snd (.fst .v0))) (.fst (.fst (.snd .v2))))
              (.snd (.fst (.snd .v2)))))))))

@[expose] def haltedDrIjArmC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (ijArgE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod .bool (B 32))) :
    Comp (atomicE2EOps ℓ P C K decT encT) I Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (.prod (gsAtomicTy ℓ Pt) (sessHTy ℓ Pt))) :=
  .bind (.ret (.pair gsE (.pair shE ijArgE)))
    (.bind (runLiftedIjCore I hsmp q qep (.fst .v0) (.snd (.snd .v0)))
      (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.fst (.snd .v1))))))

@[expose] def haltedDrCrArmC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (crArgE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool) :
    Comp (atomicE2EOps ℓ P C K decT encT) I Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (.prod (gsAtomicTy ℓ Pt) (sessHTy ℓ Pt))) :=
  .bind (.ret (.pair gsE (.pair shE crArgE)))
    (.bind (runLiftedCrCore I hsmp q (.fst .v0) (.snd (.snd .v0)))
      (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.fst (.snd .v1))))))

/-- Combined dispatcher for the non-send `deliver ⊕ (inject ⊕ corr)` tail of `smQT`. -/
@[expose] def haltedDrRecvTailC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (tailE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smRecvTailTy ℓ Pt)) :
    Comp (atomicE2EOps ℓ P C K decT encT) I Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (.prod (gsAtomicTy ℓ Pt) (sessHTy ℓ Pt))) :=
  .bind (.ret (.pair (.pair gsE shE) tailE))
    (.caseSum (.snd .v0)
      (haltedDrDlArmC I hsmp q (.fst (.fst .v1)) (.snd (.fst .v1)) .v0)
      (.caseSum .v0
        (haltedDrIjArmC I hsmp q qep (.fst (.fst .v2)) (.snd (.fst .v2)) .v0)
        (haltedDrCrArmC I hsmp q (.fst (.fst .v2)) (.snd (.fst .v2)) .v0)))

/-! ## Static query, cost, and size bounds -/

@[simp] theorem haltedDrDlArmC_queries_zero {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (dlArgE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod .bool (B 32)))
    (w : I.Tag → ℕ) :
    (haltedDrDlArmC I hsmp q gsE shE dlArgE).queries w (fun _ => 0) = 0 := by
  simp [haltedDrDlArmC, runLiftedDlCore, Comp.queries, renComp_queries,
    liftE2ECoinComp_queries_zero]

@[simp] theorem haltedDrIjArmC_queries_zero {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (ijArgE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod .bool (B 32)))
    (w : I.Tag → ℕ) :
    (haltedDrIjArmC I hsmp q qep gsE shE ijArgE).queries w (fun _ => 0) = 0 := by
  simp [haltedDrIjArmC, runLiftedIjCore, Comp.queries, renComp_queries,
    liftE2ECoinComp_queries_zero]

@[simp] theorem haltedDrCrArmC_queries_zero {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (crArgE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool)
    (w : I.Tag → ℕ) :
    (haltedDrCrArmC I hsmp q gsE shE crArgE).queries w (fun _ => 0) = 0 := by
  simp [haltedDrCrArmC, runLiftedCrCore, Comp.queries, renComp_queries,
    liftE2ECoinComp_queries_zero]

@[simp] theorem haltedDrRecvTailC_queries_zero {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (tailE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smRecvTailTy ℓ Pt))
    (w : I.Tag → ℕ) :
    (haltedDrRecvTailC I hsmp q qep gsE shE tailE).queries w (fun _ => 0) = 0 := by
  simp [haltedDrRecvTailC, Comp.queries, haltedDrDlArmC_queries_zero,
    haltedDrIjArmC_queries_zero, haltedDrCrArmC_queries_zero]

theorem haltedDrDlArmC_cost_le {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (dlArgE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod .bool (B 32))) :
    (haltedDrDlArmC I hsmp q gsE shE dlArgE).cost ≤
      gsE.cost + shE.cost + dlArgE.cost + 525 * q + 8 * (ℓ / 32 + 1) + 5113150 := by
  have hdl := drDlArmC_cost (spqrDslHooks ℓ P C K decT encT)
    (e2eStepACoinSamplers ℓ P C K decT encT (emptyTargetE2EIface ℓ)) q
    (.fst .v3 : Expr (e2eOps ℓ P C K decT encT)
      [e2eDlArgT ℓ, e2eR2T ℓ, e2eR1T ℓ, e2eTTop ℓ, e2eTTop ℓ] (e2eGsTy ℓ)) .v0
  have hfind := findRevHonestWireIdxE_cost_le (e2eEmbed ℓ P C K decT encT) q
    (.snd (.fst (.snd .v0)) : Expr (atomicE2EOps ℓ P C K decT encT)
      (.prod (gsAtomicTy ℓ Pt) (.prod (sessHTy ℓ Pt) (.prod .bool (B 32))) :: Γ) _)
    (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
  have hpost := kemOnDeliverPostE_cost_le (e2eEmbed ℓ P C K decT encT) q
    (.fst (.snd (.snd .v2)) : Expr (atomicE2EOps ℓ P C K decT encT)
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (gsAtomicTy ℓ Pt) :: .opt .nat ::
        .prod (gsAtomicTy ℓ Pt) (.prod (sessHTy ℓ Pt) (.prod .bool (B 32))) :: Γ) .bool)
    .v1 (.fst (.snd (.fst .v0))) (.fst (.fst (.snd .v2)))
  dsimp only [haltedDrDlArmC, runLiftedDlCore, findRevHonestWireIdxAtomicE,
    kemOnDeliverPostAtomicE, dlCoreUnlifted, dummySmQE, dummyR1E, dummyR2E,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hdl ⊢
  dsimp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2] at hfind hpost
  rw [renComp_cost, liftE2ECoinComp_cost]
  omega

theorem haltedDrIjArmC_cost_le {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (ijArgE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod .bool (B 32))) :
    (haltedDrIjArmC I hsmp q qep gsE shE ijArgE).cost ≤
      gsE.cost + shE.cost + ijArgE.cost + 420 * q + 10 * (ℓ / 32 + 1) +
        bits (qep + 1) + 5105300 := by
  have hij := drIjArmC_cost (spqrDslHooks ℓ P C K decT encT)
    (e2eStepACoinSamplers ℓ P C K decT encT (emptyTargetE2EIface ℓ)) q (2 + 1) qep
    (.fst .v4 : Expr (e2eOps ℓ P C K decT encT)
      [e2eDlArgT ℓ, e2eR3T ℓ, e2eR2T ℓ, e2eR1T ℓ, e2eTTop ℓ, e2eTTop ℓ] (e2eGsTy ℓ)) .v0
  have hb3 : bits (2 + 1) = 2 := rfl
  dsimp only [haltedDrIjArmC, runLiftedIjCore, ijCoreUnlifted, dummySmQE, dummyR1E,
    dummyR2E, dummyR3E, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v4, Expr.v5] at hij ⊢
  rw [hb3] at hij
  rw [renComp_cost, liftE2ECoinComp_cost]
  omega

theorem haltedDrCrArmC_cost_le {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (crArgE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool) :
    (haltedDrCrArmC I hsmp q gsE shE crArgE).cost ≤
      gsE.cost + shE.cost + crArgE.cost + 75 * q + 610 := by
  have hcr := drCrArmC_cost (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    (I := stepAIface ℓ (emptyTargetE2EIface ℓ)) q
    (.fst .v4 : Expr (e2eOps ℓ P C K decT encT)
      [.bool, e2eR3T ℓ, e2eR2T ℓ, e2eR1T ℓ, e2eTTop ℓ, e2eTTop ℓ] (e2eGsTy ℓ)) .v0
  dsimp only [haltedDrCrArmC, runLiftedCrCore, crCoreUnlifted, dummySmQE, dummyR1E,
    dummyR2E, dummyR3E, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v4, Expr.v5] at hcr ⊢
  rw [renComp_cost, liftE2ECoinComp_cost]
  omega

theorem haltedDrRecvTailC_cost_le {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (tailE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smRecvTailTy ℓ Pt)) :
    (haltedDrRecvTailC I hsmp q qep gsE shE tailE).cost ≤
      gsE.cost + shE.cost + tailE.cost + 525 * q + 10 * (ℓ / 32 + 1) +
        bits (qep + 1) + 5113200 := by
  let tTopA := Ty.prod (.prod (gsAtomicTy ℓ Pt) (sessHTy ℓ Pt)) (smRecvTailTy ℓ Pt)
  let r3A := Ty.sum (.prod .bool (B (ℓ := ℓ) (Pt := Pt) 32)) .bool
  have hdl := haltedDrDlArmC_cost_le (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    I hsmp q (.fst (.fst .v1) : Expr _ (.prod .bool (B 32) :: tTopA :: Γ) _) (.snd (.fst .v1)) .v0
  have hij := haltedDrIjArmC_cost_le (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    I hsmp q qep
    (.fst (.fst .v2) : Expr _ (.prod .bool (B 32) :: r3A :: tTopA :: Γ) _) (.snd (.fst .v2)) .v0
  have hcr := haltedDrCrArmC_cost_le (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    I hsmp q (.fst (.fst .v2) : Expr _ (.bool :: r3A :: tTopA :: Γ) _) (.snd (.fst .v2)) .v0
  dsimp only [haltedDrRecvTailC, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2] at hdl hij hcr ⊢
  omega

private theorem haltedDrDlArmC_size_rel {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (dlArgE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod .bool (B 32))) :
    (haltedDrDlArmC I hsmp q gsE shE dlArgE).size ≤
      gsE.size + shE.size + dlArgE.size +
        (dlCoreUnlifted ℓ P C K decT encT q).size + 3 * bits q + 490 := by
  have hfind := findRevHonestWireIdxE_size_le (e2eEmbed ℓ P C K decT encT) q
    (.snd (.fst (.snd .v0)) : Expr (atomicE2EOps ℓ P C K decT encT)
      (.prod (gsAtomicTy ℓ Pt) (.prod (sessHTy ℓ Pt) (.prod .bool (B 32))) :: Γ) _)
    (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
  have hpost := kemOnDeliverPostE_size_le (e2eEmbed ℓ P C K decT encT) q
    (.fst (.snd (.snd .v2)) : Expr (atomicE2EOps ℓ P C K decT encT)
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (gsAtomicTy ℓ Pt) :: .opt .nat ::
        .prod (gsAtomicTy ℓ Pt) (.prod (sessHTy ℓ Pt) (.prod .bool (B 32))) :: Γ) .bool)
    .v1 (.fst (.snd (.fst .v0))) (.fst (.fst (.snd .v2)))
  dsimp only [haltedDrDlArmC, runLiftedDlCore, findRevHonestWireIdxAtomicE,
    kemOnDeliverPostAtomicE, dummySmQE, dummyR1E, dummyR2E,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v4]
  dsimp only [Expr.size, Expr.v0, Expr.v1, Expr.v2] at hfind hpost
  rw [renComp_size, liftE2ECoinComp_size]
  omega

private theorem haltedDrIjArmC_size_rel {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (ijArgE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod .bool (B 32))) :
    (haltedDrIjArmC I hsmp q qep gsE shE ijArgE).size ≤
      gsE.size + shE.size + ijArgE.size +
        (ijCoreUnlifted ℓ P C K decT encT q qep).size + 60 := by
  dsimp only [haltedDrIjArmC, runLiftedIjCore, dummySmQE, dummyR1E, dummyR2E, dummyR3E,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v5]
  rw [renComp_size, liftE2ECoinComp_size]
  omega

private theorem haltedDrCrArmC_size_rel {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (crArgE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool) :
    (haltedDrCrArmC I hsmp q gsE shE crArgE).size ≤
      gsE.size + shE.size + crArgE.size +
        (crCoreUnlifted ℓ P C K decT encT q).size + 65 := by
  dsimp only [haltedDrCrArmC, runLiftedCrCore, dummySmQE, dummyR1E, dummyR2E, dummyR3E,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v5]
  rw [renComp_size, liftE2ECoinComp_size]
  omega

theorem haltedDrDlArmC_size_le {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (dlArgE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod .bool (B 32))) :
    (haltedDrDlArmC I hsmp q gsE shE dlArgE).size ≤
      gsE.size + shE.size + dlArgE.size + 20 * bits q + 32500 := by
  have hrel := haltedDrDlArmC_size_rel I hsmp q gsE shE dlArgE
  have hdl := (size_dl_ij_cr_core ℓ (Pt := Pt) P C K decT encT q 0).2.1
  omega

theorem haltedDrIjArmC_size_le {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (ijArgE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod .bool (B 32))) :
    (haltedDrIjArmC I hsmp q qep gsE shE ijArgE).size ≤
      gsE.size + shE.size + ijArgE.size + 17 * bits q + 5 * bits qep + 32070 := by
  have hrel := haltedDrIjArmC_size_rel I hsmp q qep gsE shE ijArgE
  have hij := (size_dl_ij_cr_core ℓ (Pt := Pt) P C K decT encT q qep).2.2.1
  omega

theorem haltedDrCrArmC_size_le {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (crArgE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool) :
    (haltedDrCrArmC I hsmp q gsE shE crArgE).size ≤
      gsE.size + shE.size + crArgE.size + 17 * bits q + 32070 := by
  have hrel := haltedDrCrArmC_size_rel I hsmp q gsE shE crArgE
  have hcr := (size_dl_ij_cr_core ℓ (Pt := Pt) P C K decT encT q 0).2.2.2
  omega

theorem haltedDrRecvTailC_size_le {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (tailE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smRecvTailTy ℓ Pt)) :
    (haltedDrRecvTailC I hsmp q qep gsE shE tailE).size ≤
      gsE.size + shE.size + tailE.size + 54 * bits q + 5 * bits qep + 80720 := by
  let tTopA := Ty.prod (.prod (gsAtomicTy ℓ Pt) (sessHTy ℓ Pt)) (smRecvTailTy ℓ Pt)
  let r3A := Ty.sum (.prod .bool (B (ℓ := ℓ) (Pt := Pt) 32)) .bool
  have hsum := (size_dl_ij_cr_core ℓ (Pt := Pt) P C K decT encT q qep).1
  have hdl := haltedDrDlArmC_size_rel (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    I hsmp q (.fst (.fst .v1) : Expr _ (.prod .bool (B 32) :: tTopA :: Γ) _) (.snd (.fst .v1)) .v0
  have hij := haltedDrIjArmC_size_rel (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    I hsmp q qep
    (.fst (.fst .v2) : Expr _ (.prod .bool (B 32) :: r3A :: tTopA :: Γ) _) (.snd (.fst .v2)) .v0
  have hcr := haltedDrCrArmC_size_rel (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    I hsmp q (.fst (.fst .v2) : Expr _ (.bool :: r3A :: tTopA :: Γ) _) (.snd (.fst .v2)) .v0
  dsimp only [haltedDrRecvTailC, Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2] at hdl hij hcr ⊢
  omega

/-! ## Evaluation agreement and invariant preservation -/

theorem haltedDrDlArmC_eval_and_inv {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (dlArgE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod .bool (B 32)))
    (ρ : Env Γ) (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (sh : KemFailSessionTrack C.F Bytes) (Q : Party) (w : Bytes)
    (hReach : SmReachBounded C K q gs)
    (hInv : KemBridgeTrackInv C.F K q sh)
    (hgs : gsE.eval ρ = gsAtomicEnc gs)
    (hsh : shE.eval ρ = sessHEnc sh)
    (harg : dlArgE.eval ρ = (partyToBool Q, w)) :
    let sm := sessionSchemeFixedSpk
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
    let cfg := configRefuseEarlyBobCorr decT encT
    let m := ((deliverRTrackHalted C.F K sm cfg (Q, w)).run gs).run sh
    (haltedDrDlArmC I hsmp q gsE shE dlArgE).eval ρ =
      (fun out => ((none, (out.1.1.map recvResultEnc, none)),
        (gsAtomicEnc out.1.2, sessHEnc out.2))) <$> I.liftP m ∧
    (∀ out ∈ support m,
      SmReachBounded C K (q + 1) out.1.2 ∧ KemBridgeTrackInv C.F K (q + 1) out.2) := by
  set sm := sessionSchemeFixedSpk
    (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
  set cfg := configRefuseEarlyBobCorr decT encT
  set ρ₀ := Env.cons
    (t := .prod (gsAtomicTy ℓ Pt) (.prod (sessHTy ℓ Pt) (.prod .bool (B 32))))
    (gsAtomicEnc gs, (sessHEnc sh, (partyToBool Q, w))) ρ
  have hj := findRevHonestWireIdxAtomicE_eval (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) q
    (.snd (.fst (.snd .v0))) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
    ρ₀ sh.2 Q w hInv.wires_len rfl rfl rfl
  let jVal := sh.2.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other)
  set ρ₁ := Env.cons (t := .opt .nat) jVal ρ₀
  let ρCore : Env [e2eDlArgT ℓ, e2eR2T ℓ, e2eR1T ℓ, e2eTTop ℓ, e2eTTop ℓ] :=
    .cons (partyEnc Q, w) (.cons dummyR2Val (.cons dummyR1Val
      (.cons (e2eGsEnc gs, dummySmQVal) (.cons (e2eGsEnc gs, dummySmQVal) .nil))))
  have hDlUn := drDlArmC_eval (spqrDslHooks ℓ P C K decT encT)
    (e2eStepACoinSamplers ℓ P C K decT encT (emptyTargetE2EIface ℓ))
    q (.fst .v3) .v0 ρCore idA idB spkCoins gs Q w hReach rfl rfl
  have hDlLift := liftE2ECoinComp_eval_prob I hsmp (dlCoreUnlifted ℓ P C K decT encT q) ρCore
    (Prod.map (fun rr => (none, (rr.map CryptoVerification.E2E.Costed.recvResultEnc, none)))
      e2eGsEnc <$> (deliverR sm cfg (Q, w)).run gs)
    (hDlUn.trans (map_liftP_eq _ _ _))
  have hParty : partyToBool Q = partyEnc Q := partyToBool_eq_partyEnc Q
  constructor
  · dsimp only [haltedDrDlArmC, runLiftedDlCore, Comp.eval]
    rw [show (Expr.pair gsE (.pair shE dlArgE)).eval ρ =
        (gsAtomicEnc gs, (sessHEnc sh, (partyToBool Q, w))) by
      simp [Expr.eval, hgs, hsh, harg], pure_bind]
    rw [hj, pure_bind]
    simp only [Expr.eval, Env.get, Expr.v0, Expr.v1, Expr.v4,
      dummySmQE, dummyR1E, dummyR2E, pure_bind, renComp_eval, pullEnv_wk5Ren]
    conv_lhs => arg 1; rw [hParty]
    change ((liftE2ECoinComp I hsmp (dlCoreUnlifted ℓ P C K decT encT q)).eval
      (liftEnv (Pt := Pt) ρCore) >>= _) = _
    rw [hDlLift]
    unfold deliverRTrackHalted Iface.liftP
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, liftStateT_run_state,
      map_eq_bind_pure_comp, Function.comp_def,
      simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
    refine bind_congr fun ⟨rr, gs'⟩ => ?_
    have hSmR := liftVal_smRRecv (Pt := Pt) rr
    set smRVal : (smRT (ℓ := ℓ) (Pt := Pt) GhostStT).denote :=
      (none, (rr.map recvResultEnc, none))
    set ρ₂ := Env.cons (t := .prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (gsAtomicTy ℓ Pt))
      (smRVal, gsAtomicEnc gs') ρ₁
    have hPost := (kemOnDeliverPostAtomicE_eval_and_inv (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) q
      (.fst (.snd (.snd .v2))) .v1 (.fst (.snd (.fst .v0))) (.fst (.fst (.snd .v2)))
      ρ₂ sh Q w rr hInv rfl rfl rfl rfl).1
    dsimp only [Prod.map]
    have hPair :
        liftVal (ℓ := ℓ) (Pt := Pt)
          (t := .prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
            (e2eGsTy ℓ))
          ((none, (rr.map CryptoVerification.E2E.Costed.recvResultEnc, none)), e2eGsEnc gs') =
        (smRVal, gsAtomicEnc gs') :=
      Prod.ext hSmR rfl
    rw [hPair]
    dsimp only [Expr.v0, Expr.v1] at hPost
    rw [hPost]
    dsimp only [Expr.eval, Env.get, Expr.v2]
    rcases sh with ⟨tr, hw⟩
    dsimp only
    rw [findIdx_deliver_eq]
    rcases rr with _ | r
    · dsimp only [StateT.run_pure, smRVal]
      simp only [simulateQ_pure, pure_bind]; rfl
    · cases r with
      | rejected =>
        dsimp only [StateT.run_pure, smRVal]
        simp only [simulateQ_pure, pure_bind]; rfl
      | accepted t i m =>
        cases hFind : hw.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) with
        | none =>
          dsimp only [StateT.run_pure, smRVal]
          simp only [simulateQ_pure, pure_bind]; rfl
        | some j =>
          dsimp only [StateT.run_bind, StateT.run_lift, StateT.run_modify, StateT.run_pure,
            monadLift_self, pure_bind, bind_assoc, smRVal]
          simp only [simulateQ_pure, pure_bind]; rfl
  · intro out hout
    rcases sh with ⟨tr, hw⟩
    unfold deliverRTrackHalted at hout
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, liftStateT_run_state,
      pure_bind, bind_assoc, support_bind,
      Set.mem_iUnion, exists_prop] at hout
    rcases hout with ⟨⟨rr, gs'⟩, hDel, hRest⟩
    dsimp only at hRest
    rw [findIdx_deliver_eq] at hRest
    have hReach' : SmReachBounded C K (q + 1) gs' :=
      smReachBounded_step_oracleImplR C K idA idB qep q spkCoins decT encT
        (.inl (.inl (.inr (Q, w)))) hReach hDel
    set ρ₂ := Env.cons (t := .prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (gsAtomicTy ℓ Pt))
      ((none, (rr.map recvResultEnc, none)), gsAtomicEnc gs') ρ₁
    have hInvStep := (kemOnDeliverPostAtomicE_eval_and_inv (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) q
      (.fst (.snd (.snd .v2))) .v1 (.fst (.snd (.fst .v0))) (.fst (.fst (.snd .v2)))
      ρ₂ (tr, hw) Q w rr hInv rfl rfl rfl rfl).2
    have hInv' := kemBridgeTrackInv_mono (Nat.le_succ q) hInvStep
    rcases rr with _ | r
    · simp [StateT.run_pure] at hRest
      subst hRest; exact ⟨hReach', kemBridgeTrackInv_mono (Nat.le_succ q) hInv⟩
    · cases r with
      | rejected =>
        simp [StateT.run_pure] at hRest
        subst hRest; exact ⟨hReach', kemBridgeTrackInv_mono (Nat.le_succ q) hInv⟩
      | accepted t i m =>
        cases hFind : hw.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) with
        | none =>
          rw [hFind] at hRest
          dsimp only [StateT.run_pure] at hRest
          simp at hRest
          subst hRest; exact ⟨hReach', kemBridgeTrackInv_mono (Nat.le_succ q) hInv⟩
        | some j =>
          rw [hFind] at hRest hInv'
          dsimp only [StateT.run_lift, StateT.run_modify, StateT.run_map, StateT.run_pure,
            map_eq_bind_pure_comp, Function.comp_def, monadLift_self, pure_bind, bind_assoc] at hRest hInv'
          simp at hRest
          subst hRest; exact ⟨hReach', hInv'⟩

theorem haltedDrIjArmC_eval_and_inv {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (ijArgE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod .bool (B 32)))
    (ρ : Env Γ) (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (sh : KemFailSessionTrack C.F Bytes) (Q : Party) (w : Bytes)
    (hReach : SmReachBounded C K q gs)
    (hInv : KemBridgeTrackInv C.F K q sh)
    (hgs : gsE.eval ρ = gsAtomicEnc gs)
    (hsh : shE.eval ρ = sessHEnc sh)
    (harg : ijArgE.eval ρ = (partyToBool Q, w)) :
    let sm := sessionSchemeFixedSpk
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
    let cfg := configRefuseEarlyBobCorr decT encT
    let m := (((liftStateT (injectR sm 3 qep cfg (Q, w)) :
      StateT _ (StateT (KemFailSessionTrack C.F Bytes) ProbComp) _).run gs).run sh)
    (haltedDrIjArmC I hsmp q qep gsE shE ijArgE).eval ρ =
      (fun out => ((none, (out.1.1.map recvResultEnc, none)),
        (gsAtomicEnc out.1.2, sessHEnc out.2))) <$> I.liftP m ∧
    (∀ out ∈ support m,
      SmReachBounded C K (q + 1) out.1.2 ∧ KemBridgeTrackInv C.F K (q + 1) out.2) := by
  set sm := sessionSchemeFixedSpk
    (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
  set cfg := configRefuseEarlyBobCorr decT encT
  let ρCore : Env [e2eDlArgT ℓ, e2eR3T ℓ, e2eR2T ℓ, e2eR1T ℓ, e2eTTop ℓ, e2eTTop ℓ] :=
    .cons (partyEnc Q, w) (.cons dummyR3Val (.cons dummyR2Val (.cons dummyR1Val
      (.cons (e2eGsEnc gs, dummySmQVal) (.cons (e2eGsEnc gs, dummySmQVal) .nil)))))
  have hIjUn := drIjArmC_eval (spqrDslHooks ℓ P C K decT encT)
    (e2eStepACoinSamplers ℓ P C K decT encT (emptyTargetE2EIface ℓ))
    q (2 + 1) qep (.fst .v4) .v0 ρCore idA idB spkCoins gs Q w hReach rfl rfl
  have hIjLift := liftE2ECoinComp_eval_prob I hsmp (ijCoreUnlifted ℓ P C K decT encT q qep) ρCore
    (Prod.map (fun rr => (none, (rr.map CryptoVerification.E2E.Costed.recvResultEnc, none)))
      e2eGsEnc <$> (injectR sm (2 + 1) qep cfg (Q, w)).run gs)
    (hIjUn.trans (map_liftP_eq _ _ _))
  have hParty : partyToBool Q = partyEnc Q := partyToBool_eq_partyEnc Q
  constructor
  · dsimp only [haltedDrIjArmC, runLiftedIjCore, Comp.eval]
    rw [show (Expr.pair gsE (.pair shE ijArgE)).eval ρ =
        (gsAtomicEnc gs, (sessHEnc sh, (partyToBool Q, w))) by
      simp [Expr.eval, hgs, hsh, harg], pure_bind]
    simp only [Expr.eval, Env.get, Expr.v0, Expr.v5,
      dummySmQE, dummyR1E, dummyR2E, dummyR3E, pure_bind, renComp_eval, pullEnv_wk6Ren]
    conv_lhs => arg 1; rw [hParty]
    change ((liftE2ECoinComp I hsmp (ijCoreUnlifted ℓ P C K decT encT q qep)).eval
      (liftEnv (Pt := Pt) ρCore) >>= _) = _
    rw [hIjLift]
    change _ = _ <$> I.liftP (((liftStateT (n := StateT (KemFailSessionTrack C.F Bytes) ProbComp)
      (injectR sm (2 + 1) qep cfg (Q, w))).run gs).run sh)
    rw [liftStateT_run_state]
    unfold Iface.liftP
    simp only [map_eq_bind_pure_comp, Function.comp_def,
      simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
    refine bind_congr fun ⟨rr, gs'⟩ => ?_
    dsimp only [Prod.map, Expr.eval, Env.get, Expr.v0, Expr.v1, gsAtomicEnc]
    exact congrArg pure (Prod.ext (liftVal_smRRecv (Pt := Pt) rr) rfl)
  · intro out hout
    change out ∈ support (((liftStateT (n := StateT (KemFailSessionTrack C.F Bytes) ProbComp)
      (injectR sm 3 qep cfg (Q, w))).run gs).run sh) at hout
    rw [liftStateT_run_state] at hout
    simp only [support_bind, support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff, exists_prop] at hout
    rcases hout with ⟨⟨rr, gs'⟩, hInj, rfl⟩
    exact ⟨smReachBounded_step_oracleImplR C K idA idB qep q spkCoins decT encT
        (.inl (.inr (Q, w))) hReach hInj,
      kemBridgeTrackInv_mono (Nat.le_succ q) hInv⟩

theorem haltedDrCrArmC_eval_and_inv {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (crArgE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool)
    (ρ : Env Γ) (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (sh : KemFailSessionTrack C.F Bytes) (Q : Party)
    (hReach : SmReachBounded C K q gs)
    (hInv : KemBridgeTrackInv C.F K q sh)
    (hgs : gsE.eval ρ = gsAtomicEnc gs)
    (hsh : shE.eval ρ = sessHEnc sh)
    (harg : crArgE.eval ρ = partyToBool Q) :
    let cfg := configRefuseEarlyBobCorr decT encT
    let m := (((liftStateT (corrR cfg Q) :
      StateT _ (StateT (KemFailSessionTrack C.F Bytes) ProbComp) _).run gs).run sh)
    (haltedDrCrArmC I hsmp q gsE shE crArgE).eval ρ =
      (fun out => ((none, (none, out.1.1)),
        (gsAtomicEnc out.1.2, sessHEnc out.2))) <$> I.liftP m ∧
    (∀ out ∈ support m,
      SmReachBounded C K (q + 1) out.1.2 ∧ KemBridgeTrackInv C.F K (q + 1) out.2) := by
  set cfg := configRefuseEarlyBobCorr decT encT
  let ρCore : Env [.bool, e2eR3T ℓ, e2eR2T ℓ, e2eR1T ℓ, e2eTTop ℓ, e2eTTop ℓ] :=
    .cons (partyEnc Q) (.cons dummyR3Val (.cons dummyR2Val (.cons dummyR1Val
      (.cons (e2eGsEnc gs, dummySmQVal) (.cons (e2eGsEnc gs, dummySmQVal) .nil)))))
  have hCrUn := drCrArmC_eval (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    (I := stepAIface ℓ (emptyTargetE2EIface ℓ))
    q (.fst .v4) .v0 ρCore gs Q hReach.lists rfl rfl
  have hCrLift := liftE2ECoinComp_eval_prob I hsmp (crCoreUnlifted ℓ P C K decT encT q) ρCore
    (Prod.map (fun st? => (none, (none, st?))) e2eGsEnc <$> (corrR cfg Q).run gs)
    (hCrUn.trans (map_liftP_eq _ _ _))
  have hParty : partyToBool Q = partyEnc Q := partyToBool_eq_partyEnc Q
  constructor
  · dsimp only [haltedDrCrArmC, runLiftedCrCore, Comp.eval]
    rw [show (Expr.pair gsE (.pair shE crArgE)).eval ρ =
        (gsAtomicEnc gs, (sessHEnc sh, partyToBool Q)) by
      simp [Expr.eval, hgs, hsh, harg], pure_bind]
    simp only [Expr.eval, Env.get, Expr.v0, Expr.v5,
      dummySmQE, dummyR1E, dummyR2E, dummyR3E, pure_bind, renComp_eval, pullEnv_wk6Ren]
    conv_lhs => arg 1; rw [hParty]
    change ((liftE2ECoinComp I hsmp (crCoreUnlifted ℓ P C K decT encT q)).eval
      (liftEnv (Pt := Pt) ρCore) >>= _) = _
    rw [hCrLift]
    change _ = _ <$> I.liftP (((liftStateT (n := StateT (KemFailSessionTrack C.F Bytes) ProbComp)
      (corrR cfg Q)).run gs).run sh)
    rw [liftStateT_run_state]
    unfold Iface.liftP
    simp only [map_eq_bind_pure_comp, Function.comp_def,
      simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
    refine bind_congr fun ⟨st?, gs'⟩ => ?_
    dsimp only [Prod.map, Expr.eval, Env.get, Expr.v0, Expr.v1, gsAtomicEnc]
    exact congrArg pure (Prod.ext (liftVal_smRCorr ℓ (Pt := Pt) st?) rfl)
  · intro out hout
    change out ∈ support (((liftStateT (n := StateT (KemFailSessionTrack C.F Bytes) ProbComp)
      (corrR cfg Q)).run gs).run sh) at hout
    rw [liftStateT_run_state] at hout
    simp only [support_bind, support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff, exists_prop] at hout
    rcases hout with ⟨⟨st?, gs'⟩, hCr, rfl⟩
    exact ⟨smReachBounded_step_oracleImplR C K idA idB qep q spkCoins decT encT
        (.inr Q) hReach hCr,
      kemBridgeTrackInv_mono (Nat.le_succ q) hInv⟩

theorem haltedDrRecvTailC_eval_and_inv {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (tailE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smRecvTailTy ℓ Pt))
    (ρ : Env Γ) (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (sh : KemFailSessionTrack C.F Bytes)
    (tail : (Party × Bytes) ⊕ ((Party × Bytes) ⊕ Party))
    (hReach : SmReachBounded C K q gs)
    (hInv : KemBridgeTrackInv C.F K q sh)
    (hgs : gsE.eval ρ = gsAtomicEnc gs)
    (hsh : shE.eval ρ = sessHEnc sh)
    (htail : tailE.eval ρ = smRecvTailEnc tail) :
    let sm := sessionSchemeFixedSpk
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
    let cfg := configRefuseEarlyBobCorr decT encT
    let sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
      smRecvTailToSpec tail
    let m := ((oracleImplRTrackHalted C.F K sm 3 qep cfg sq).run gs).run sh
    (haltedDrRecvTailC I hsmp q qep gsE shE tailE).eval ρ =
      (fun out => (packAtomicSmRespEnc (Pt := Pt) (bhPackSmResp sq out.1.1),
        (gsAtomicEnc out.1.2, sessHEnc out.2))) <$> I.liftP m ∧
    (∀ out ∈ support m,
      SmReachBounded C K (q + 1) out.1.2 ∧ KemBridgeTrackInv C.F K (q + 1) out.2) := by
  let tTopA := Ty.prod (.prod (gsAtomicTy ℓ Pt) (sessHTy ℓ Pt)) (smRecvTailTy ℓ Pt)
  let r3A := Ty.sum (.prod .bool (B (ℓ := ℓ) (Pt := Pt) 32)) .bool
  dsimp only [haltedDrRecvTailC, Comp.eval]
  rw [show (Expr.pair (.pair gsE shE) tailE).eval ρ =
      ((gsAtomicEnc gs, sessHEnc sh), smRecvTailEnc tail) by
    simp [Expr.eval, hgs, hsh, htail], pure_bind]
  rcases tail with ⟨Q, w⟩ | (⟨Q, w⟩ | Q)
  · exact haltedDrDlArmC_eval_and_inv I hsmp q qep (.fst (.fst .v1)) (.snd (.fst .v1)) .v0
      (Env.cons (t := .prod .bool (B 32)) (partyToBool Q, w)
        (Env.cons (t := tTopA) ((gsAtomicEnc gs, sessHEnc sh), .inl (partyToBool Q, w)) ρ))
      idA idB spkCoins gs sh Q w hReach hInv rfl rfl rfl
  · exact haltedDrIjArmC_eval_and_inv I hsmp q qep (.fst (.fst .v2)) (.snd (.fst .v2)) .v0
      (Env.cons (t := .prod .bool (B 32)) (partyToBool Q, w)
        (Env.cons (t := r3A) (.inl (partyToBool Q, w))
          (Env.cons (t := tTopA)
            ((gsAtomicEnc gs, sessHEnc sh), .inr (.inl (partyToBool Q, w))) ρ)))
      idA idB spkCoins gs sh Q w hReach hInv rfl rfl rfl
  · exact haltedDrCrArmC_eval_and_inv I hsmp q qep (.fst (.fst .v2)) (.snd (.fst .v2)) .v0
      (Env.cons (t := .bool) (partyToBool Q)
        (Env.cons (t := r3A) (.inr (partyToBool Q))
          (Env.cons (t := tTopA)
            ((gsAtomicEnc gs, sessHEnc sh), .inr (.inr (partyToBool Q))) ρ)))
      idA idB spkCoins gs sh Q hReach hInv rfl rfl rfl

end Computational.Proofs.E2E.Dsl.HaltedDrSessionSimRecvSteps
