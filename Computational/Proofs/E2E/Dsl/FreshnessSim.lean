/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.E2EStateRepr
public import Computational.Specifications.Reductions.Pqxdh.StatementPqReds
public import Computational.Proofs.SpecLemmas.Game.BhShallowHelpers
import Computational.Proofs.E2E.Dsl.ClampsLossless

/-!
# Session Freshness and End-of-Game Win Decisions in `ReductionDsl`

Defines bounded `ReductionDsl` expressions and computations for `bhE2EDrvWon`,
`allTestedSessionsFresh`, `finishKind`, and `bhShallowFinishPrefix`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Computational.Proofs.E2E.Dsl.FreshnessSim

open OracleSpec OracleComp
open ReductionDsl (Ty Var Env Ops Iface Expr Comp UniformSamplerTag)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (GameState)
open CryptoGames.LibsignalSession (Crypto PublicKey GhostState)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes BHModelInst BHE2EDrvState bhE2EDrvWon allTestedSessionsFresh
  bhShallowFinishPrefix)
open CryptoVerification.E2E.Costed (e2eSig PB E2EPureOp E2ECryptoOp e2eCryptoOps e2eOps hdrV)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp eval_e2ePureOp cost_e2ePureOp
  size_e2ePureOp e2eCryptoOp eval_e2eCryptoOp cost_e2eCryptoOp size_e2eCryptoOp)
open Computational.Proofs.E2E.Dsl.ClampsLossless (e2eCryptoOps_eval_pow8_lossless)
open Computational.Proofs.E2E.Dsl.M2Interfaces (e2eGsTy e2eGsEnc)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (Ext v eLet eCaseOpt eFind eAny
  orE eval_orE isNoneE eval_isNoneE stepAIface liftP_bind liftP_pure
  e2ePrincipalEntryTy e2ePrincipalEntryToVal e2eSpkBundleEntryTy e2eSpkBundleEntryToVal
  e2eInitiatorEntryTy e2eInitiatorEntryToVal e2eRespEntryTy e2eRespEntryToVal
  e2eKeyIndStateTy e2eKeyIndStateToVal KeyIndSetupBounded
  peIkPk peCorr beSpkPk beRev hdrIkA hdrEkA hdrKemCt
  iePeerIk iePeerSpk iePeerOpk iePeerPq ieSpkHon ieOpkHon ieFresh ieHdr ieTested ieRev
  reIk reSpk reOpk rePq reHdr reSendHon reTested reRev
  stPrin stSpk stSess stResp)
open Computational.Proofs.E2E.Dsl.E2EStateRepr (e2eModelInstTy e2eModelInstEnc
  e2eDrvStateTy e2eDrvStateEnc drvInsts drvSt drvB drvPaused miGs)

section GenericHelpers

variable {ℓ : ℕ} {O : Ops (e2eSig ℓ)}

def boolEqE {Γ : List (Ty (e2eSig ℓ))} (a b : Expr O Γ .bool) : Expr O Γ .bool :=
  .ite a b (.not b)

@[simp] theorem eval_boolEqE {Γ : List (Ty (e2eSig ℓ))} (a b : Expr O Γ .bool) (ρ : Env Γ) :
    (boolEqE a b).eval ρ = (a.eval ρ == b.eval ρ) := by
  simp only [boolEqE, Expr.eval]
  cases a.eval ρ <;> cases b.eval ρ <;> rfl

@[simp] theorem cost_boolEqE {Γ : List (Ty (e2eSig ℓ))} (a b : Expr O Γ .bool) :
    (boolEqE a b).cost = a.cost + b.cost + 2 := by
  simp only [boolEqE, Expr.cost]; omega

def boolXorE {Γ : List (Ty (e2eSig ℓ))} (a b : Expr O Γ .bool) : Expr O Γ .bool :=
  .ite a (.not b) b

@[simp] theorem eval_boolXorE {Γ : List (Ty (e2eSig ℓ))} (a b : Expr O Γ .bool) (ρ : Env Γ) :
    (boolXorE a b).eval ρ = (a.eval ρ ^^ b.eval ρ) := by
  simp only [boolXorE, Expr.eval]
  cases a.eval ρ <;> cases b.eval ρ <;> rfl

@[simp] theorem cost_boolXorE {Γ : List (Ty (e2eSig ℓ))} (a b : Expr O Γ .bool) :
    (boolXorE a b).cost = a.cost + b.cost + 2 := by
  simp only [boolXorE, Expr.cost]; omega

@[simp] theorem cost_orE {Γ : List (Ty (e2eSig ℓ))} (a b : Expr O Γ .bool) :
    (orE a b).cost = a.cost + b.cost + 4 := by
  simp only [orE, Expr.cost]; omega

@[simp] theorem cost_isNoneE {Γ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt τ)) : (isNoneE e).cost = e.cost + 2 := by
  simp only [isNoneE, Expr.cost]; omega

def gsB {Γ : List (Ty (e2eSig ℓ))} (gs : Expr O Γ (e2eGsTy ℓ)) : Expr O Γ .bool :=
  .fst (.snd gs)

def gsWin {Γ : List (Ty (e2eSig ℓ))} (gs : Expr O Γ (e2eGsTy ℓ)) : Expr O Γ .bool :=
  .fst (.snd (.snd gs))

@[simp] theorem eval_gsB {Γ : List (Ty (e2eSig ℓ))} (gsE : Expr O Γ (e2eGsTy ℓ)) (ρ : Env Γ)
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hgs : gsE.eval ρ = e2eGsEnc gs) :
    (gsB gsE).eval ρ = gs.b := by
  simp [gsB, e2eGsEnc, Expr.eval, hgs]

@[simp] theorem eval_gsWin {Γ : List (Ty (e2eSig ℓ))} (gsE : Expr O Γ (e2eGsTy ℓ)) (ρ : Env Γ)
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hgs : gsE.eval ρ = e2eGsEnc gs) :
    (gsWin gsE).eval ρ = gs.win := by
  simp [gsWin, e2eGsEnc, Expr.eval, hgs]

private theorem list_all_eq_not_any_not {α : Type} (l : List α) (p : α → Bool) :
    l.all p = !(l.any (fun x => !(p x))) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.all_cons, List.any_cons, ih]

end GenericHelpers

section FreshnessAndWin

variable {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
  {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "E2EExpr" => Expr (e2eOps ℓ P C K decT encT)
local notation "ePure" => e2ePureOp (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
local notation "eCrypt" =>
  e2eCryptoOp (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)

@[simp] private theorem pnat32_val : (32 : ℕ+).val = 32 := rfl
@[simp] private theorem pnat1568_val : (1568 : ℕ+).val = 1568 := rfl

def drvWonCost (qStart : ℕ) : ℕ := 24 * qStart + 12

/-- Bounded local-instance win predicate `bhE2EDrvWon σ b`. -/
def drvWonE (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (bE : E2EExpr Γ .bool) : E2EExpr Γ .bool :=
  eLet (.pair σE bE) fun sb =>
    eAny qStart (drvInsts (.fst (v sb))) fun d =>
      eCaseOpt (miGs (v d)) (.bool false) fun gs =>
        .and (boolEqE (gsB (v gs)) (.snd (v sb))) (gsWin (v gs))

theorem eval_drvWonE (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (bE : E2EExpr Γ .bool) (ρ : Env Γ)
    {σ : BHE2EDrvState S ℓ} (hσ : σE.eval ρ = e2eDrvStateEnc σ)
    (hInsts : σ.insts.length ≤ qStart) :
    (drvWonE qStart σE bE).eval ρ = bhE2EDrvWon σ (bE.eval ρ) := by
  have hInsts' : (σ.insts.map (e2eModelInstEnc (ℓ := ℓ))).length ≤ qStart := by simp [hInsts]
  set ρ0 : Env ((e2eDrvStateTy S ℓ).prod .bool :: Γ) :=
    .cons (e2eDrvStateEnc σ, bE.eval ρ) ρ with hρ0
  have hb0 : (ρ0.get .zero).2 = bE.eval ρ := rfl
  have hInsts0 :
      (drvInsts (O := e2eOps ℓ P C K decT encT) (.fst (.var .zero))).eval ρ0 =
        σ.insts.map e2eModelInstEnc := rfl
  simp only [drvWonE, bhE2EDrvWon, eLet, v, Ext.wk, Ext.refl, Ext.step, Expr.eval, hσ, ← hρ0]
  dsimp only [eAny, Expr.eval]
  simp only [hInsts0, List.take_of_length_le hInsts', List.any_map]
  apply List.any_congr rfl
  intro d
  rcases hgs : d.gs with _ | gs <;>
    simp only [Function.comp_apply, eCaseOpt, miGs, gsB, gsWin, e2eModelInstEnc, e2eGsEnc,
      eval_boolEqE, Expr.eval, Env.get, hb0, hgs, Option.map]

theorem cost_drvWonE (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (bE : E2EExpr Γ .bool) :
    (drvWonE qStart σE bE).cost ≤ σE.cost + bE.cost + drvWonCost qStart := by
  simp only [drvWonE, drvWonCost, drvInsts, miGs, gsB, gsWin, cost_boolEqE,
    eLet, eAny, eCaseOpt, v, Ext.wk, Ext.refl, Ext.step, Expr.cost,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

def drvWonC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (bE : E2EExpr Γ .bool) :
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) Γ .bool :=
  .ret (drvWonE qStart σE bE)

theorem eval_drvWonC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (bE : E2EExpr Γ .bool) (ρ : Env Γ)
    {σ : BHE2EDrvState S ℓ} (hσ : σE.eval ρ = e2eDrvStateEnc σ)
    (hInsts : σ.insts.length ≤ qStart) :
    (drvWonC I₀ qStart σE bE).eval ρ = pure (bhE2EDrvWon σ (bE.eval ρ)) := by
  simp only [drvWonC, Comp.eval, eval_drvWonE qStart σE bE ρ hσ hInsts]

theorem cost_drvWonC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (bE : E2EExpr Γ .bool) :
    (drvWonC I₀ qStart σE bE).cost ≤ σE.cost + bE.cost + drvWonCost qStart + 1 := by
  have h := cost_drvWonE qStart σE bE
  simp only [drvWonC, Comp.cost]; omega

@[simp] theorem queries_drvWonC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (bE : E2EExpr Γ .bool)
    (w : (stepAIface ℓ I₀).Tag → ℕ) :
    (drvWonC I₀ qStart σE bE).queries w (fun _ => 0) = 0 := rfl

attribute [local irreducible] drvWonE drvWonC

def finishKindCost (qStart : ℕ) : ℕ := drvWonCost qStart + 32

/-- End-of-game bit decision `b' == σ.b || bhE2EDrvWon σ σ.b` for `kindRed`. -/
def finishKindE (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (b'E : E2EExpr Γ .bool) : E2EExpr Γ .bool :=
  eLet (.pair σE b'E) fun sb =>
    orE (boolEqE (.snd (v sb)) (drvB (.fst (v sb))))
        (drvWonE qStart (.fst (v sb)) (drvB (.fst (v sb))))

theorem eval_finishKindE (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (b'E : E2EExpr Γ .bool) (ρ : Env Γ)
    {σ : BHE2EDrvState S ℓ} (hσ : σE.eval ρ = e2eDrvStateEnc σ)
    (hInsts : σ.insts.length ≤ qStart) :
    (finishKindE qStart σE b'E).eval ρ = (b'E.eval ρ == σ.b || bhE2EDrvWon σ σ.b) := by
  set ρ0 : Env ((e2eDrvStateTy S ℓ).prod .bool :: Γ) :=
    .cons (e2eDrvStateEnc σ, b'E.eval ρ) ρ with hρ0
  have hσ0 : (Expr.fst (O := e2eOps ℓ P C K decT encT) (.var .zero)).eval ρ0 =
      e2eDrvStateEnc σ := rfl
  have hb'0 : (ρ0.get .zero).2 = b'E.eval ρ := rfl
  have hdrvB : (drvB (O := e2eOps ℓ P C K decT encT) (.fst (.var .zero))).eval ρ0 = σ.b := rfl
  simp only [finishKindE, eLet, v, Ext.wk, Ext.refl, Expr.eval, eval_orE, eval_boolEqE,
    hσ, ← hρ0, hb'0, hdrvB, eval_drvWonE qStart _ _ ρ0 hσ0 hInsts]

theorem cost_finishKindE (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (b'E : E2EExpr Γ .bool) :
    (finishKindE qStart σE b'E).cost ≤ σE.cost + b'E.cost + finishKindCost qStart := by
  let Δ0 := (e2eDrvStateTy S ℓ).prod .bool :: Γ
  have hw := cost_drvWonE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ0) qStart (.fst (.var .zero)) (drvB (.fst (.var .zero)))
  simp only [finishKindE, finishKindCost, drvB, cost_orE, cost_boolEqE,
    eLet, v, Ext.wk, Ext.refl, Expr.cost, Nat.reduceAdd] at hw ⊢
  omega

def finishKindC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (b'E : E2EExpr Γ .bool) :
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) Γ .bool :=
  .ret (finishKindE qStart σE b'E)

theorem eval_finishKindC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (b'E : E2EExpr Γ .bool) (ρ : Env Γ)
    {σ : BHE2EDrvState S ℓ} (hσ : σE.eval ρ = e2eDrvStateEnc σ)
    (hInsts : σ.insts.length ≤ qStart) :
    (finishKindC I₀ qStart σE b'E).eval ρ =
      pure (b'E.eval ρ == σ.b || bhE2EDrvWon σ σ.b) := by
  simp only [finishKindC, Comp.eval, eval_finishKindE qStart σE b'E ρ hσ hInsts]

theorem cost_finishKindC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (b'E : E2EExpr Γ .bool) :
    (finishKindC I₀ qStart σE b'E).cost ≤ σE.cost + b'E.cost + finishKindCost qStart + 1 := by
  have h := cost_finishKindE qStart σE b'E
  simp only [finishKindC, Comp.cost]; omega

@[simp] theorem queries_finishKindC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (b'E : E2EExpr Γ .bool)
    (w : (stepAIface ℓ I₀).Tag → ℕ) :
    (finishKindC I₀ qStart σE b'E).queries w (fun _ => 0) = 0 := rfl

attribute [local irreducible] finishKindE finishKindC

def isHonestUncorruptedPeerSomeE (nId : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (principalsE : E2EExpr Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (pkE : E2EExpr Γ (PB 32)) : E2EExpr Γ .bool :=
  eLet (.pair principalsE (eCrypt .pow8 pkE)) fun pp =>
    eCaseOpt
      (eFind nId (.fst (v pp)) fun pe =>
        ePure (.pbytesEq 32 32)
          (.pair (.snd (v pp)) (eCrypt .pow8 (peIkPk (.snd (v pe))))))
      (.bool false)
      (fun pe => .not (peCorr (.snd (v pe))))

theorem eval_isHonestUncorruptedPeerSomeE (nId : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (principalsE : E2EExpr Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (pkE : E2EExpr Γ (PB 32)) (ρ : Env Γ)
    {principals : List (ℕ × SignalPqxdh.PrincipalEntry)} {pk : SignalPqxdh.Bytes}
    (hp : principalsE.eval ρ = principals.map (Prod.map id e2ePrincipalEntryToVal))
    (hpk : pkE.eval ρ = pk) (hlen : principals.length ≤ nId) :
    (isHonestUncorruptedPeerSomeE nId principalsE pkE).eval ρ =
      (SignalPqxdh.isHonestUncorruptedPeer P principals pk).isSome := by
  have hpowPk := e2eCryptoOps_eval_pow8_lossless ℓ hP C K pk
  dsimp only [e2eCryptoOps] at hpowPk
  have hlen' : (principals.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ)))).length ≤ nId := by
    simp [hlen]
  simp only [isHonestUncorruptedPeerSomeE, SignalPqxdh.isHonestUncorruptedPeer,
    SignalPqxdh.findHonestPrincipal, eLet, eCaseOpt, eFind, peIkPk, peCorr,
    v, Ext.wk, Ext.refl, Ext.step, Expr.eval, eval_e2ePureOp, E2EPureOp.eval,
    eval_e2eCryptoOp, Env.get, hp, hpk, hpowPk, List.take_of_length_le hlen', List.find?_map]
  have hfind :
      principals.find? ((fun x =>
        P.pow8 pk ==
          (e2eCryptoOps ℓ P C K).eval .pow8 x.2.2.1) ∘
          Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ))) =
      principals.find? (fun x => P.pow8 pk == P.pow8 x.2.ikAPk) := by
    congr 1; funext ⟨k, entry⟩
    have hpowE := e2eCryptoOps_eval_pow8_lossless ℓ hP C K entry.ikAPk
    dsimp only [e2eCryptoOps] at hpowE
    simp only [Function.comp_apply, Prod.map_apply, id_eq, e2ePrincipalEntryToVal, hpowE]
  rw [hfind]
  rcases hf : principals.find? (fun x => P.pow8 pk == P.pow8 x.2.ikAPk) with
    _ | ⟨k, entry⟩
  · rw [hf]; rfl
  · rw [hf]; simp only [Option.map, Prod.map_apply, id_eq, e2ePrincipalEntryToVal]
    cases entry.corrupted <;> rfl

theorem cost_isHonestUncorruptedPeerSomeE (nId : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (principalsE : E2EExpr Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (pkE : E2EExpr Γ (PB 32)) :
    (isHonestUncorruptedPeerSomeE nId principalsE pkE).cost ≤
      principalsE.cost + pkE.cost + 96 * nId + 32 := by
  simp only [isHonestUncorruptedPeerSomeE, peIkPk, peCorr, eLet, eCaseOpt, eFind,
    v, Ext.wk, Ext.refl, Ext.step, Expr.cost,
    cost_e2ePureOp, E2EPureOp.cost, cost_e2eCryptoOp, E2ECryptoOp.cost,
    pnat32_val, Nat.reduceAdd]
  omega

attribute [local irreducible] isHonestUncorruptedPeerSomeE

def isSpkRevealedE (nSpk : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (spkBundlesE : E2EExpr Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)))
    (pkE : E2EExpr Γ (PB 32)) : E2EExpr Γ .bool :=
  eLet (.pair spkBundlesE (eCrypt .pow8 pkE)) fun bp =>
    eAny nSpk (.fst (v bp)) fun be =>
      .and (beRev (.snd (v be)))
        (ePure (.pbytesEq 32 32)
          (.pair (eCrypt .pow8 (beSpkPk (.snd (v be)))) (.snd (v bp))))

theorem eval_isSpkRevealedE (nSpk : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (spkBundlesE : E2EExpr Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)))
    (pkE : E2EExpr Γ (PB 32)) (ρ : Env Γ)
    {spkBundles : List ((ℕ × ℕ) × SignalPqxdh.SpkBundleEntry)} {pk : SignalPqxdh.Bytes}
    (hb : spkBundlesE.eval ρ = spkBundles.map (Prod.map id e2eSpkBundleEntryToVal))
    (hpk : pkE.eval ρ = pk) (hlen : spkBundles.length ≤ nSpk) :
    (isSpkRevealedE nSpk spkBundlesE pkE).eval ρ =
      SignalPqxdh.isSpkRevealed P spkBundles pk := by
  have hpowPk := e2eCryptoOps_eval_pow8_lossless ℓ hP C K pk
  dsimp only [e2eCryptoOps] at hpowPk
  have hlen' :
      (spkBundles.map (Prod.map id (e2eSpkBundleEntryToVal (ℓ := ℓ)))).length ≤ nSpk := by
    simp [hlen]
  simp only [isSpkRevealedE, SignalPqxdh.isSpkRevealed, eLet, eAny, beRev, beSpkPk,
    v, Ext.wk, Ext.refl, Ext.step, Expr.eval, eval_e2ePureOp, E2EPureOp.eval,
    eval_e2eCryptoOp, Env.get, hb, hpk, hpowPk, List.take_of_length_le hlen', List.any_map]
  apply List.any_congr rfl
  rintro ⟨_, b⟩
  have hpowB := e2eCryptoOps_eval_pow8_lossless ℓ hP C K b.spkPk
  dsimp only [e2eCryptoOps] at hpowB
  simp only [Function.comp_apply, Prod.map_apply, id_eq, e2eSpkBundleEntryToVal, hpowB]

theorem cost_isSpkRevealedE (nSpk : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (spkBundlesE : E2EExpr Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)))
    (pkE : E2EExpr Γ (PB 32)) :
    (isSpkRevealedE nSpk spkBundlesE pkE).cost ≤
      spkBundlesE.cost + pkE.cost + 104 * nSpk + 24 := by
  simp only [isSpkRevealedE, beRev, beSpkPk, eLet, eAny,
    v, Ext.wk, Ext.refl, Ext.step, Expr.cost,
    cost_e2ePureOp, E2EPureOp.cost, cost_e2eCryptoOp, E2ECryptoOp.cost,
    pnat32_val, Nat.reduceAdd]
  omega

attribute [local irreducible] isSpkRevealedE

def keyIndInitCorrClauseE (nId nSpk : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (principalsE : E2EExpr Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (spkBundlesE : E2EExpr Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)))
    (sE : E2EExpr Γ (e2eInitiatorEntryTy ℓ S)) : E2EExpr Γ .bool :=
  eLet (.pair principalsE (.pair spkBundlesE sE)) fun p =>
    .and (ieFresh (.snd (.snd (v p))))
      (orE
        (orE
          (isHonestUncorruptedPeerSomeE nId (.fst (v p)) (iePeerIk (.snd (.snd (v p)))))
          (.and (ieSpkHon (.snd (.snd (v p))))
            (.not (isSpkRevealedE nSpk (.fst (.snd (v p))) (iePeerSpk (.snd (.snd (v p))))))))
        (ieOpkHon (.snd (.snd (v p)))))

theorem eval_keyIndInitCorrClauseE (nId nSpk : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (principalsE : E2EExpr Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (spkBundlesE : E2EExpr Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)))
    (sE : E2EExpr Γ (e2eInitiatorEntryTy ℓ S)) (ρ : Env Γ)
    {principals : List (ℕ × SignalPqxdh.PrincipalEntry)}
    {spkBundles : List ((ℕ × ℕ) × SignalPqxdh.SpkBundleEntry)}
    {s : SignalPqxdh.KeyIndInitiatorEntry S}
    (hp : principalsE.eval ρ = principals.map (Prod.map id e2ePrincipalEntryToVal))
    (hb : spkBundlesE.eval ρ = spkBundles.map (Prod.map id e2eSpkBundleEntryToVal))
    (hs : sE.eval ρ = e2eInitiatorEntryToVal s)
    (hId : principals.length ≤ nId) (hSpk : spkBundles.length ≤ nSpk) :
    (keyIndInitCorrClauseE nId nSpk principalsE spkBundlesE sE).eval ρ =
      SignalPqxdh.keyIndInitCorruptionClause P true principals spkBundles s := by
  set ρ0 : Env
      ((Ty.list (.prod .nat e2ePrincipalEntryTy)).prod
        ((Ty.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)).prod
          (e2eInitiatorEntryTy ℓ S)) :: Γ) :=
    .cons (principals.map (Prod.map id e2ePrincipalEntryToVal),
      (spkBundles.map (Prod.map id e2eSpkBundleEntryToVal),
       e2eInitiatorEntryToVal s)) ρ with hρ0
  have hp0 : (Expr.fst (O := e2eOps ℓ P C K decT encT) (.var .zero)).eval ρ0 =
      principals.map (Prod.map id e2ePrincipalEntryToVal) := rfl
  have hb0 : (Expr.fst (O := e2eOps ℓ P C K decT encT) (.snd (.var .zero))).eval ρ0 =
      spkBundles.map (Prod.map id e2eSpkBundleEntryToVal) := rfl
  have hFresh0 : (ieFresh (O := e2eOps ℓ P C K decT encT)
      (.snd (.snd (.var .zero)))).eval ρ0 = s.fresh := rfl
  have hPeerIk0 : (iePeerIk (O := e2eOps ℓ P C K decT encT)
      (.snd (.snd (.var .zero)))).eval ρ0 = s.peerIkPk := rfl
  have hPeerSpk0 : (iePeerSpk (O := e2eOps ℓ P C K decT encT)
      (.snd (.snd (.var .zero)))).eval ρ0 = s.peerSpkPk := rfl
  have hSpkHon0 : (ieSpkHon (O := e2eOps ℓ P C K decT encT)
      (.snd (.snd (.var .zero)))).eval ρ0 = s.spkHonest := rfl
  have hOpkHon0 : (ieOpkHon (O := e2eOps ℓ P C K decT encT)
      (.snd (.snd (.var .zero)))).eval ρ0 = s.opkHonest := rfl
  simp only [keyIndInitCorrClauseE, SignalPqxdh.keyIndInitCorruptionClause, ↓reduceIte,
    eLet, v, Ext.wk, Ext.refl, Expr.eval, eval_orE, hp, hb, hs, ← hρ0,
    hFresh0, hSpkHon0, hOpkHon0,
    eval_isHonestUncorruptedPeerSomeE nId hP _ _ ρ0 hp0 hPeerIk0 hId,
    eval_isSpkRevealedE nSpk hP _ _ ρ0 hb0 hPeerSpk0 hSpk]

theorem cost_keyIndInitCorrClauseE (nId nSpk : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (principalsE : E2EExpr Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (spkBundlesE : E2EExpr Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)))
    (sE : E2EExpr Γ (e2eInitiatorEntryTy ℓ S)) :
    (keyIndInitCorrClauseE nId nSpk principalsE spkBundlesE sE).cost ≤
      principalsE.cost + spkBundlesE.cost + sE.cost + 96 * nId + 104 * nSpk + 160 := by
  let Δ0 :=
    (Ty.list (.prod .nat e2ePrincipalEntryTy)).prod
      ((Ty.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)).prod
        (e2eInitiatorEntryTy ℓ S)) :: Γ
  have h1 := cost_isHonestUncorruptedPeerSomeE (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ0) nId
    (.fst (.var .zero)) (iePeerIk (.snd (.snd (.var .zero))))
  have h2 := cost_isSpkRevealedE (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ0) nSpk
    (.fst (.snd (.var .zero))) (iePeerSpk (.snd (.snd (.var .zero))))
  simp only [keyIndInitCorrClauseE, ieFresh, iePeerIk, iePeerSpk, ieSpkHon, ieOpkHon,
    cost_orE, eLet, v, Ext.wk, Ext.refl, Expr.cost, Nat.reduceAdd] at h1 h2 ⊢
  omega

attribute [local irreducible] keyIndInitCorrClauseE

def optPow8EqE {Γ : List (Ty (e2eSig ℓ))}
    (aE bE : E2EExpr Γ (.opt (PB 32))) : E2EExpr Γ .bool :=
  eLet (.pair aE bE) fun ab =>
    eCaseOpt (.fst (v ab))
      (isNoneE (.snd (v ab)))
      (fun a => eCaseOpt (.snd (v ab))
        (.bool false)
        (fun b => ePure (.pbytesEq 32 32) (.pair (eCrypt .pow8 (v a)) (eCrypt .pow8 (v b)))))

theorem eval_optPow8EqE (hP : SignalPqxdh.WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (aE bE : E2EExpr Γ (.opt (PB 32))) (ρ : Env Γ) :
    (optPow8EqE aE bE).eval ρ =
      ((aE.eval ρ).map P.pow8 == (bE.eval ρ).map P.pow8) := by
  simp only [optPow8EqE, eLet, eCaseOpt, v, Ext.wk, Ext.refl, Ext.step,
    Expr.eval, eval_isNoneE, eval_e2ePureOp, E2EPureOp.eval, eval_e2eCryptoOp, Env.get]
  rcases aE.eval ρ with _ | a <;> rcases bE.eval ρ with _ | b
  · rfl
  · rfl
  · rfl
  · have ha := e2eCryptoOps_eval_pow8_lossless ℓ hP C K a
    have hb := e2eCryptoOps_eval_pow8_lossless ℓ hP C K b
    dsimp only [e2eCryptoOps] at ha hb
    dsimp only [Option.map]
    rw [ha, hb]; rfl

theorem cost_optPow8EqE {Γ : List (Ty (e2eSig ℓ))}
    (aE bE : E2EExpr Γ (.opt (PB 32))) :
    (optPow8EqE aE bE).cost ≤ aE.cost + bE.cost + 96 := by
  simp only [optPow8EqE, cost_isNoneE, eLet, eCaseOpt, v, Ext.wk, Ext.refl, Ext.step,
    Expr.cost, cost_e2ePureOp, E2EPureOp.cost, cost_e2eCryptoOp, E2ECryptoOp.cost,
    pnat32_val, Nat.reduceAdd]
  omega

attribute [local irreducible] optPow8EqE

def keyIndPartnerE {Γ : List (Ty (e2eSig ℓ))}
    (sE : E2EExpr Γ (e2eInitiatorEntryTy ℓ S))
    (rE : E2EExpr Γ (e2eRespEntryTy ℓ S)) : E2EExpr Γ .bool :=
  eLet (.pair sE rE) fun sr =>
    .and
      (.and
        (.and
          (.and
            (.and
              (.and
                (ePure (.pbytesEq 32 32)
                  (.pair (eCrypt .pow8 (hdrIkA (ieHdr (.fst (v sr)))))
                         (eCrypt .pow8 (hdrIkA (reHdr (.snd (v sr)))))))
                (ePure (.pbytesEq 32 32)
                  (.pair (eCrypt .pow8 (iePeerIk (.fst (v sr))))
                         (eCrypt .pow8 (reIk (.snd (v sr)))))))
              (ePure (.pbytesEq 32 32)
                (.pair (eCrypt .pow8 (iePeerSpk (.fst (v sr))))
                       (eCrypt .pow8 (reSpk (.snd (v sr)))))))
            (optPow8EqE (iePeerOpk (.fst (v sr))) (reOpk (.snd (v sr)))))
          (ePure (.pbytesEq 32 32)
            (.pair (hdrEkA (ieHdr (.fst (v sr)))) (hdrEkA (reHdr (.snd (v sr)))))))
        (ePure (.pbytesEq 1568 1568)
          (.pair (iePeerPq (.fst (v sr))) (rePq (.snd (v sr))))))
      (ePure (.pbytesEq 1568 1568)
        (.pair (hdrKemCt (ieHdr (.fst (v sr)))) (hdrKemCt (reHdr (.snd (v sr))))))

theorem eval_keyIndPartnerE (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {Γ : List (Ty (e2eSig ℓ))}
    (sE : E2EExpr Γ (e2eInitiatorEntryTy ℓ S))
    (rE : E2EExpr Γ (e2eRespEntryTy ℓ S)) (ρ : Env Γ)
    {s : SignalPqxdh.KeyIndInitiatorEntry S} {r : SignalPqxdh.KeyIndRespEntry S}
    (hs : sE.eval ρ = e2eInitiatorEntryToVal s)
    (hr : rE.eval ρ = e2eRespEntryToVal r) :
    (keyIndPartnerE sE rE).eval ρ = SignalPqxdh.keyIndPartner P s r := by
  have hp1 := e2eCryptoOps_eval_pow8_lossless ℓ hP C K s.hdr.ikAPk
  have hp2 := e2eCryptoOps_eval_pow8_lossless ℓ hP C K r.hdr.ikAPk
  have hp3 := e2eCryptoOps_eval_pow8_lossless ℓ hP C K s.peerIkPk
  have hp4 := e2eCryptoOps_eval_pow8_lossless ℓ hP C K r.respIkPk
  have hp5 := e2eCryptoOps_eval_pow8_lossless ℓ hP C K s.peerSpkPk
  have hp6 := e2eCryptoOps_eval_pow8_lossless ℓ hP C K r.spkPk
  dsimp only [e2eCryptoOps] at hp1 hp2 hp3 hp4 hp5 hp6
  simp only [keyIndPartnerE, SignalPqxdh.keyIndPartner, eLet,
    ieHdr, iePeerIk, iePeerSpk, iePeerOpk, iePeerPq,
    reHdr, reIk, reSpk, reOpk, rePq, hdrIkA, hdrEkA, hdrKemCt, hdrV,
    e2eInitiatorEntryToVal, e2eRespEntryToVal,
    v, Ext.wk, Ext.refl, Expr.eval, eval_optPow8EqE hP,
    eval_e2ePureOp, E2EPureOp.eval, eval_e2eCryptoOp, Env.get,
    hs, hr, hp1, hp2, hp3, hp4, hp5, hp6]

theorem cost_keyIndPartnerE {Γ : List (Ty (e2eSig ℓ))}
    (sE : E2EExpr Γ (e2eInitiatorEntryTy ℓ S))
    (rE : E2EExpr Γ (e2eRespEntryTy ℓ S)) :
    (keyIndPartnerE sE rE).cost ≤ sE.cost + rE.cost + 6900 := by
  let Δ0 := (e2eInitiatorEntryTy ℓ S).prod (e2eRespEntryTy ℓ S) :: Γ
  have hopk := cost_optPow8EqE (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ0)
    (iePeerOpk (.fst (.var .zero))) (reOpk (.snd (.var .zero)))
  simp only [keyIndPartnerE, ieHdr, iePeerIk, iePeerSpk, iePeerOpk, iePeerPq,
    reHdr, reIk, reSpk, reOpk, rePq, hdrIkA, hdrEkA, hdrKemCt,
    eLet, v, Ext.wk, Ext.refl, Expr.cost,
    cost_e2ePureOp, E2EPureOp.cost, cost_e2eCryptoOp, E2ECryptoOp.cost,
    pnat32_val, pnat1568_val, Nat.reduceAdd] at hopk ⊢
  omega

attribute [local irreducible] keyIndPartnerE

def isKeyIndInitStillFreshE (nId nSpk nResp : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (principalsE : E2EExpr Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (spkBundlesE : E2EExpr Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)))
    (respE : E2EExpr Γ (.list (e2eRespEntryTy ℓ S)))
    (sE : E2EExpr Γ (e2eInitiatorEntryTy ℓ S)) : E2EExpr Γ .bool :=
  eLet (.pair principalsE (.pair spkBundlesE (.pair respE sE))) fun p =>
    .and
      (.and
        (keyIndInitCorrClauseE nId nSpk
          (.fst (v p)) (.fst (.snd (v p))) (.snd (.snd (.snd (v p)))))
        (.not (ieRev (.snd (.snd (.snd (v p)))))))
      (.not (eAny nResp (.fst (.snd (.snd (v p)))) fun r =>
        .not (orE
          (.not (keyIndPartnerE (.snd (.snd (.snd (v p)))) (v r)))
          (.and (reSendHon (v r)) (.not (reRev (v r)))))))

theorem eval_isKeyIndInitStillFreshE (nId nSpk nResp : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (principalsE : E2EExpr Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (spkBundlesE : E2EExpr Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)))
    (respE : E2EExpr Γ (.list (e2eRespEntryTy ℓ S)))
    (sE : E2EExpr Γ (e2eInitiatorEntryTy ℓ S)) (ρ : Env Γ)
    {principals : List (ℕ × SignalPqxdh.PrincipalEntry)}
    {spkBundles : List ((ℕ × ℕ) × SignalPqxdh.SpkBundleEntry)}
    {respSessions : List (SignalPqxdh.KeyIndRespEntry S)}
    {s : SignalPqxdh.KeyIndInitiatorEntry S}
    (hp : principalsE.eval ρ = principals.map (Prod.map id e2ePrincipalEntryToVal))
    (hb : spkBundlesE.eval ρ = spkBundles.map (Prod.map id e2eSpkBundleEntryToVal))
    (hr : respE.eval ρ = respSessions.map e2eRespEntryToVal)
    (hs : sE.eval ρ = e2eInitiatorEntryToVal s)
    (hId : principals.length ≤ nId) (hSpk : spkBundles.length ≤ nSpk)
    (hResp : respSessions.length ≤ nResp) :
    (isKeyIndInitStillFreshE nId nSpk nResp principalsE spkBundlesE respE sE).eval ρ =
      SignalPqxdh.isKeyIndInitStillFresh P true principals spkBundles respSessions s := by
  have hResp' : (respSessions.map (e2eRespEntryToVal (ℓ := ℓ))).length ≤ nResp := by simp [hResp]
  set ρ0 : Env
      ((Ty.list (.prod .nat e2ePrincipalEntryTy)).prod
        ((Ty.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)).prod
          ((Ty.list (e2eRespEntryTy ℓ S)).prod (e2eInitiatorEntryTy ℓ S))) :: Γ) :=
    .cons (principals.map (Prod.map id e2ePrincipalEntryToVal),
      (spkBundles.map (Prod.map id e2eSpkBundleEntryToVal),
       (respSessions.map e2eRespEntryToVal, e2eInitiatorEntryToVal s))) ρ with hρ0
  have hp0 : (Expr.fst (O := e2eOps ℓ P C K decT encT) (.var .zero)).eval ρ0 =
      principals.map (Prod.map id e2ePrincipalEntryToVal) := rfl
  have hb0 : (Expr.fst (O := e2eOps ℓ P C K decT encT) (.snd (.var .zero))).eval ρ0 =
      spkBundles.map (Prod.map id e2eSpkBundleEntryToVal) := rfl
  have hr0 : (ρ0.get .zero).2.2.1 = respSessions.map e2eRespEntryToVal := rfl
  have hs0 : (Expr.snd (O := e2eOps ℓ P C K decT encT) (.snd (.snd (.var .zero)))).eval ρ0 =
      e2eInitiatorEntryToVal s := rfl
  have hRev0 : (ieRev (O := e2eOps ℓ P C K decT encT)
      (.snd (.snd (.snd (.var .zero))))).eval ρ0 = s.revealed := rfl
  simp only [isKeyIndInitStillFreshE, SignalPqxdh.isKeyIndInitStillFresh, list_all_eq_not_any_not,
    eLet, v, Ext.wk, Ext.refl, Ext.step, Expr.eval, hp, hb, hr, hs, ← hρ0, hRev0,
    eval_keyIndInitCorrClauseE nId nSpk hP _ _ _ ρ0 hp0 hb0 hs0 hId hSpk]
  dsimp only [eAny, Expr.eval]
  simp only [hr0, List.take_of_length_le hResp', List.any_map]
  congr 2
  apply List.any_congr rfl
  intro r
  have hs1 : (Expr.snd (O := e2eOps ℓ P C K decT encT)
      (.snd (.snd (.var (.succ .zero))))).eval (.cons (e2eRespEntryToVal r) ρ0) =
      e2eInitiatorEntryToVal s := rfl
  have hr1 : (Expr.var (O := e2eOps ℓ P C K decT encT) .zero).eval
      (.cons (e2eRespEntryToVal r) ρ0) = e2eRespEntryToVal r := rfl
  have hSendHon1 : (reSendHon (O := e2eOps ℓ P C K decT encT) (.var .zero)).eval
      (.cons (e2eRespEntryToVal r) ρ0) = r.senderHonest := rfl
  have hReRev1 : (reRev (O := e2eOps ℓ P C K decT encT) (.var .zero)).eval
      (.cons (e2eRespEntryToVal r) ρ0) = r.revealed := rfl
  simp only [Function.comp_apply, Expr.eval, eval_orE,
    eval_keyIndPartnerE hP _ _ _ hs1 hr1, hSendHon1, hReRev1]

theorem cost_isKeyIndInitStillFreshE (nId nSpk nResp : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (principalsE : E2EExpr Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (spkBundlesE : E2EExpr Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)))
    (respE : E2EExpr Γ (.list (e2eRespEntryTy ℓ S)))
    (sE : E2EExpr Γ (e2eInitiatorEntryTy ℓ S)) :
    (isKeyIndInitStillFreshE nId nSpk nResp principalsE spkBundlesE respE sE).cost ≤
      principalsE.cost + spkBundlesE.cost + respE.cost + sE.cost +
        96 * nId + 104 * nSpk + 7000 * nResp + 240 := by
  let Δ0 :=
    (Ty.list (.prod .nat e2ePrincipalEntryTy)).prod
      ((Ty.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)).prod
        ((Ty.list (e2eRespEntryTy ℓ S)).prod (e2eInitiatorEntryTy ℓ S))) :: Γ
  let Δ1 := e2eRespEntryTy ℓ S :: Δ0
  have hc := cost_keyIndInitCorrClauseE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ0) nId nSpk
    (.fst (.var .zero)) (.fst (.snd (.var .zero))) (.snd (.snd (.snd (.var .zero))))
  have hp := cost_keyIndPartnerE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ1)
    (.snd (.snd (.snd (.var (.succ .zero))))) (.var .zero)
  simp only [Expr.cost, Nat.reduceAdd] at hc hp
  unfold isKeyIndInitStillFreshE
  simp only [ieRev, reSendHon, reRev, cost_orE, eLet, eAny,
    v, Ext.wk, Ext.refl, Ext.step, Expr.cost, Nat.reduceAdd]
  have hpB :
      (keyIndPartnerE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
        (decT := decT) (encT := encT) (Γ := Δ1)
        (.snd (.snd (.snd (.var (.succ .zero))))) (.var .zero)).cost + 1 +
      21 + 4 + 1 + 1 ≤ 7000 := by omega
  have hpM :
      nResp * ((keyIndPartnerE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
        (decT := decT) (encT := encT) (Γ := Δ1)
        (.snd (.snd (.snd (.var (.succ .zero))))) (.var .zero)).cost + 1 +
      21 + 4 + 1 + 1) ≤ 7000 * nResp := by
    rw [Nat.mul_comm 7000 nResp]; exact Nat.mul_le_mul_left nResp hpB
  omega

attribute [local irreducible] isKeyIndInitStillFreshE

def respPartnerStepE {Γ : List (Ty (e2eSig ℓ))} :
    E2EExpr (e2eInitiatorEntryTy ℓ S :: .prod .bool .bool ::
      .prod (.list (e2eInitiatorEntryTy ℓ S)) (.prod (e2eRespEntryTy ℓ S) (.prod .bool .bool)) :: Γ)
      (.prod .bool .bool) :=
  .letE (keyIndPartnerE (.var .zero) (.fst (.snd (.var (.succ (.succ .zero))))))
    (.pair
      (orE (.var .zero) (.fst (.var (.succ (.succ .zero)))))
      (.and
        (orE (.not (.var .zero))
          (.and (.not (ieRev (.var (.succ .zero))))
            (.and (ieFresh (.var (.succ .zero)))
              (orE
                (orE (.fst (.snd (.snd (.var (.succ (.succ (.succ .zero)))))))
                  (.and (ieSpkHon (.var (.succ .zero)))
                    (.snd (.snd (.snd (.var (.succ (.succ (.succ .zero)))))))))
                (ieOpkHon (.var (.succ .zero)))))))
        (.snd (.var (.succ (.succ .zero))))))

private theorem eval_respPartnerStepE (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {Γ : List (Ty (e2eSig ℓ))}
    (ρ' : Env (.prod (.list (e2eInitiatorEntryTy ℓ S))
      (.prod (e2eRespEntryTy ℓ S) (.prod .bool .bool)) :: Γ))
    {r : SignalPqxdh.KeyIndRespEntry S} {a b : Bool}
    (hr : (ρ'.get .zero).2.1 = e2eRespEntryToVal r) (ha : (ρ'.get .zero).2.2.1 = a)
    (hb : (ρ'.get .zero).2.2.2 = b)
    (s : SignalPqxdh.KeyIndInitiatorEntry S) (acc : Bool × Bool) :
    (respPartnerStepE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)).eval
        (.cons (e2eInitiatorEntryToVal s) (.cons (t := .prod .bool .bool) acc ρ')) =
      (SignalPqxdh.keyIndPartner P s r || acc.1,
       (!SignalPqxdh.keyIndPartner P s r ||
          (!s.revealed && (s.fresh && ((a || (s.spkHonest && b)) || s.opkHonest)))) && acc.2) := by
  have hs1 : (Expr.var (O := e2eOps ℓ P C K decT encT) .zero).eval
      (Env.cons (e2eInitiatorEntryToVal s) (Env.cons (t := .prod .bool .bool) acc ρ')) =
      e2eInitiatorEntryToVal s := rfl
  have hr1 : (Expr.fst (O := e2eOps ℓ P C K decT encT) (.snd (.var (.succ (.succ .zero))))).eval
      (Env.cons (e2eInitiatorEntryToVal s) (Env.cons (t := .prod .bool .bool) acc ρ')) =
      e2eRespEntryToVal r := hr
  simp only [respPartnerStepE, Expr.eval, eval_orE, eval_keyIndPartnerE hP _ _ _ hs1 hr1]
  simp only [ieRev, ieFresh, ieSpkHon, ieOpkHon, Expr.eval, Env.get, e2eInitiatorEntryToVal,
    ha, hb]

private theorem foldr_respPartnerStepE (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {Γ : List (Ty (e2eSig ℓ))}
    (ρ' : Env (.prod (.list (e2eInitiatorEntryTy ℓ S))
      (.prod (e2eRespEntryTy ℓ S) (.prod .bool .bool)) :: Γ))
    {r : SignalPqxdh.KeyIndRespEntry S} {a b : Bool}
    (hr : (ρ'.get .zero).2.1 = e2eRespEntryToVal r) (ha : (ρ'.get .zero).2.2.1 = a)
    (hb : (ρ'.get .zero).2.2.2 = b) :
    ∀ ss : List (SignalPqxdh.KeyIndInitiatorEntry S),
      (ss.map e2eInitiatorEntryToVal).foldr
        (fun x acc => (respPartnerStepE (P := P) (C := C) (K := K) (decT := decT)
          (encT := encT)).eval (.cons x (.cons (t := .prod .bool .bool) acc ρ'))) (false, true) =
      (ss.any (fun s => SignalPqxdh.keyIndPartner P s r),
       ss.all (fun s => !SignalPqxdh.keyIndPartner P s r ||
         (!s.revealed && (s.fresh && ((a || (s.spkHonest && b)) || s.opkHonest)))))
  | [] => rfl
  | s :: ss => by
    rw [List.map_cons, List.foldr_cons, foldr_respPartnerStepE hP ρ' hr ha hb ss,
      eval_respPartnerStepE hP ρ' hr ha hb]
    rfl

theorem cost_respPartnerStepE {Γ : List (Ty (e2eSig ℓ))} :
    (respPartnerStepE (S := S) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      (Γ := Γ)).cost ≤ 7090 := by
  have hp := cost_keyIndPartnerE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (Γ := e2eInitiatorEntryTy ℓ S :: .prod .bool .bool ::
      .prod (.list (e2eInitiatorEntryTy ℓ S)) (.prod (e2eRespEntryTy ℓ S) (.prod .bool .bool)) :: Γ)
    (.var .zero) (.fst (.snd (.var (.succ (.succ .zero)))))
  simp only [Expr.cost, Nat.reduceAdd] at hp
  simp only [respPartnerStepE, ieRev, ieFresh, ieSpkHon, ieOpkHon, cost_orE, Expr.cost,
    Nat.reduceAdd]
  omega

def respPartnerFoldE (nInit : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (initE : E2EExpr Γ (.list (e2eInitiatorEntryTy ℓ S)))
    (rE : E2EExpr Γ (e2eRespEntryTy ℓ S)) (aE bE : E2EExpr Γ .bool) :
    E2EExpr Γ (.prod .bool .bool) :=
  .letE (.pair initE (.pair rE (.pair aE bE)))
    (.foldrB nInit (.fst (.var .zero)) (.pair (.bool false) (.bool true)) respPartnerStepE)

theorem eval_respPartnerFoldE (nInit : ℕ) (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {Γ : List (Ty (e2eSig ℓ))}
    (initE : E2EExpr Γ (.list (e2eInitiatorEntryTy ℓ S)))
    (rE : E2EExpr Γ (e2eRespEntryTy ℓ S)) (aE bE : E2EExpr Γ .bool) (ρ : Env Γ)
    {sessions : List (SignalPqxdh.KeyIndInitiatorEntry S)} {r : SignalPqxdh.KeyIndRespEntry S}
    {a b : Bool}
    (hi : initE.eval ρ = sessions.map e2eInitiatorEntryToVal)
    (hr : rE.eval ρ = e2eRespEntryToVal r) (ha : aE.eval ρ = a) (hb : bE.eval ρ = b)
    (hInit : sessions.length ≤ nInit) :
    (respPartnerFoldE nInit initE rE aE bE).eval ρ =
      (sessions.any (fun s => SignalPqxdh.keyIndPartner P s r),
       sessions.all (fun s => !SignalPqxdh.keyIndPartner P s r ||
         (!s.revealed && (s.fresh && ((a || (s.spkHonest && b)) || s.opkHonest))))) := by
  have hInit' : (sessions.map (e2eInitiatorEntryToVal (ℓ := ℓ))).length ≤ nInit := by
    simp [hInit]
  simp only [respPartnerFoldE, Expr.eval, Env.get, hi, List.take_of_length_le hInit']
  exact foldr_respPartnerStepE hP _ (by simp only [Env.get, hr]) (by simp only [Env.get, ha])
    (by simp only [Env.get, hb]) sessions

theorem cost_respPartnerFoldE (nInit : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (initE : E2EExpr Γ (.list (e2eInitiatorEntryTy ℓ S)))
    (rE : E2EExpr Γ (e2eRespEntryTy ℓ S)) (aE bE : E2EExpr Γ .bool) :
    (respPartnerFoldE nInit initE rE aE bE).cost ≤
      initE.cost + rE.cost + aE.cost + bE.cost + 7100 * nInit + 20 := by
  have hs := cost_respPartnerStepE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ)
  have hM := Nat.mul_le_mul_left nInit (Nat.add_le_add_right hs 1)
  simp only [respPartnerFoldE, Expr.cost, Nat.reduceAdd] at hM ⊢
  omega

attribute [local irreducible] respPartnerFoldE

/-- Checks `isKeyIndRespStillFresh`, evaluating peer-key corruption lookups once against `r` up to `pow8`. -/
def isKeyIndRespStillFreshE (nId nSpk nInit : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (principalsE : E2EExpr Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (spkBundlesE : E2EExpr Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)))
    (initE : E2EExpr Γ (.list (e2eInitiatorEntryTy ℓ S)))
    (rE : E2EExpr Γ (e2eRespEntryTy ℓ S)) : E2EExpr Γ .bool :=
  eLet (.pair principalsE (.pair spkBundlesE (.pair initE rE))) fun p =>
    .and
      (.and (.not (reRev (.snd (.snd (.snd (v p)))))) (reSendHon (.snd (.snd (.snd (v p))))))
      (.letE
        (.pair
          (isHonestUncorruptedPeerSomeE nId (.fst (v p)) (reIk (.snd (.snd (.snd (v p))))))
          (.pair
            (.not (isSpkRevealedE nSpk (.fst (.snd (v p))) (reSpk (.snd (.snd (.snd (v p)))))))
            (isHonestUncorruptedPeerSomeE nId (.fst (v p))
              (hdrIkA (reHdr (.snd (.snd (.snd (v p)))))))))
        (.letE
          (respPartnerFoldE nInit (.fst (.snd (.snd (.var (.succ .zero)))))
            (.snd (.snd (.snd (.var (.succ .zero))))) (.fst (.var .zero))
            (.fst (.snd (.var .zero))))
          (.ite (.fst (.var .zero)) (.snd (.var .zero))
            (.and (.snd (.snd (.var (.succ .zero)))) (.fst (.snd (.var (.succ .zero))))))))

theorem eval_isKeyIndRespStillFreshE (nId nSpk nInit : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (principalsE : E2EExpr Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (spkBundlesE : E2EExpr Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)))
    (initE : E2EExpr Γ (.list (e2eInitiatorEntryTy ℓ S)))
    (rE : E2EExpr Γ (e2eRespEntryTy ℓ S)) (ρ : Env Γ)
    {principals : List (ℕ × SignalPqxdh.PrincipalEntry)}
    {spkBundles : List ((ℕ × ℕ) × SignalPqxdh.SpkBundleEntry)}
    {sessions : List (SignalPqxdh.KeyIndInitiatorEntry S)}
    {r : SignalPqxdh.KeyIndRespEntry S}
    (hp : principalsE.eval ρ = principals.map (Prod.map id e2ePrincipalEntryToVal))
    (hb : spkBundlesE.eval ρ = spkBundles.map (Prod.map id e2eSpkBundleEntryToVal))
    (hi : initE.eval ρ = sessions.map e2eInitiatorEntryToVal)
    (hr : rE.eval ρ = e2eRespEntryToVal r)
    (hId : principals.length ≤ nId) (hSpk : spkBundles.length ≤ nSpk)
    (hInit : sessions.length ≤ nInit) :
    (isKeyIndRespStillFreshE nId nSpk nInit principalsE spkBundlesE initE rE).eval ρ =
      SignalPqxdh.isKeyIndRespStillFresh P true principals spkBundles sessions r := by
  have hInit' : (sessions.map (e2eInitiatorEntryToVal (ℓ := ℓ))).length ≤ nInit := by simp [hInit]
  set ρ0 : Env
      ((Ty.list (.prod .nat e2ePrincipalEntryTy)).prod
        ((Ty.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)).prod
          ((Ty.list (e2eInitiatorEntryTy ℓ S)).prod (e2eRespEntryTy ℓ S))) :: Γ) :=
    .cons (principals.map (Prod.map id e2ePrincipalEntryToVal),
      (spkBundles.map (Prod.map id e2eSpkBundleEntryToVal),
       (sessions.map e2eInitiatorEntryToVal, e2eRespEntryToVal r))) ρ with hρ0
  have hp0 : (Expr.fst (O := e2eOps ℓ P C K decT encT) (.var .zero)).eval ρ0 =
      principals.map (Prod.map id e2ePrincipalEntryToVal) := rfl
  have hb0 : (Expr.fst (O := e2eOps ℓ P C K decT encT) (.snd (.var .zero))).eval ρ0 =
      spkBundles.map (Prod.map id e2eSpkBundleEntryToVal) := rfl
  have hi0 : (ρ0.get .zero).2.2.1 = sessions.map e2eInitiatorEntryToVal := rfl
  have hReRev0 : (reRev (O := e2eOps ℓ P C K decT encT)
      (.snd (.snd (.snd (.var .zero))))).eval ρ0 = r.revealed := rfl
  have hSendHon0 : (reSendHon (O := e2eOps ℓ P C K decT encT)
      (.snd (.snd (.snd (.var .zero))))).eval ρ0 = r.senderHonest := rfl
  have hHdrIk0 : (hdrIkA (O := e2eOps ℓ P C K decT encT)
      (reHdr (.snd (.snd (.snd (.var .zero)))))).eval ρ0 = r.hdr.ikAPk := rfl
  have hReSpk0 : (reSpk (O := e2eOps ℓ P C K decT encT)
      (.snd (.snd (.snd (.var .zero))))).eval ρ0 = r.spkPk := rfl
  have hReIk0 : (reIk (O := e2eOps ℓ P C K decT encT)
      (.snd (.snd (.snd (.var .zero))))).eval ρ0 = r.respIkPk := rfl
  simp only [isKeyIndRespStillFreshE, SignalPqxdh.isKeyIndRespStillFresh, Bool.true_and,
    eLet, v, Ext.wk, Ext.refl, Ext.step, Expr.eval, hp, hb, hi, hr, ← hρ0, hReRev0, hSendHon0,
    eval_isHonestUncorruptedPeerSomeE nId hP _ _ ρ0 hp0 hReIk0 hId,
    eval_isHonestUncorruptedPeerSomeE nId hP _ _ ρ0 hp0 hHdrIk0 hId,
    eval_isSpkRevealedE nSpk hP _ _ ρ0 hb0 hReSpk0 hSpk]
  rw [eval_respPartnerFoldE nInit hP _ _ _ _ _ (sessions := sessions) (r := r)
    (a := (SignalPqxdh.isHonestUncorruptedPeer P principals r.respIkPk).isSome)
    (b := !SignalPqxdh.isSpkRevealed P spkBundles r.spkPk) ?hi1 ?hr1 ?ha1 ?hb1 hInit]
  case hi1 => rfl
  case hr1 => rfl
  case ha1 => rfl
  case hb1 => rfl
  have hall :
      sessions.all (fun s => !SignalPqxdh.keyIndPartner P s r ||
        (!s.revealed && (s.fresh &&
          (((SignalPqxdh.isHonestUncorruptedPeer P principals r.respIkPk).isSome ||
            (s.spkHonest && !SignalPqxdh.isSpkRevealed P spkBundles r.spkPk)) ||
            s.opkHonest)))) =
      sessions.all (fun s => !SignalPqxdh.keyIndPartner P s r ||
        (!s.revealed && SignalPqxdh.keyIndInitCorruptionClause P true principals spkBundles s)) := by
    apply List.all_congr rfl
    intro s
    cases hps : SignalPqxdh.keyIndPartner P s r
    · rfl
    · simp only [SignalPqxdh.keyIndPartner, Bool.and_eq_true, beq_iff_eq] at hps
      have hIk : P.pow8 s.peerIkPk = P.pow8 r.respIkPk := hps.1.1.1.1.1.2
      have hSpkEq : P.pow8 s.peerSpkPk = P.pow8 r.spkPk := hps.1.1.1.1.2
      have h1 : SignalPqxdh.isHonestUncorruptedPeer P principals s.peerIkPk =
          SignalPqxdh.isHonestUncorruptedPeer P principals r.respIkPk := by
        simp only [SignalPqxdh.isHonestUncorruptedPeer, SignalPqxdh.findHonestPrincipal, hIk]
      have h2 : SignalPqxdh.isSpkRevealed P spkBundles s.peerSpkPk =
          SignalPqxdh.isSpkRevealed P spkBundles r.spkPk := by
        simp only [SignalPqxdh.isSpkRevealed, hSpkEq]
      simp only [SignalPqxdh.keyIndInitCorruptionClause, ↓reduceIte, h1, h2]
  rw [hall]
  simp only [Env.get]

theorem cost_isKeyIndRespStillFreshE (nId nSpk nInit : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (principalsE : E2EExpr Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (spkBundlesE : E2EExpr Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)))
    (initE : E2EExpr Γ (.list (e2eInitiatorEntryTy ℓ S)))
    (rE : E2EExpr Γ (e2eRespEntryTy ℓ S)) :
    (isKeyIndRespStillFreshE nId nSpk nInit principalsE spkBundlesE initE rE).cost ≤
      principalsE.cost + spkBundlesE.cost + initE.cost + rE.cost +
        7100 * nInit + 192 * nId + 104 * nSpk + 400 := by
  let Δ0 :=
    (Ty.list (.prod .nat e2ePrincipalEntryTy)).prod
      ((Ty.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)).prod
        ((Ty.list (e2eInitiatorEntryTy ℓ S)).prod (e2eRespEntryTy ℓ S))) :: Γ
  let Δ1 := ((Ty.bool : Ty (e2eSig ℓ)).prod (Ty.prod .bool .bool)) :: Δ0
  have hh1 := cost_isHonestUncorruptedPeerSomeE (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ0) nId
    (.fst (.var .zero)) (reIk (.snd (.snd (.snd (.var .zero)))))
  have hh2 := cost_isHonestUncorruptedPeerSomeE (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ0) nId
    (.fst (.var .zero)) (hdrIkA (reHdr (.snd (.snd (.snd (.var .zero))))))
  have hspk := cost_isSpkRevealedE (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ0) nSpk
    (.fst (.snd (.var .zero))) (reSpk (.snd (.snd (.snd (.var .zero)))))
  have hf := cost_respPartnerFoldE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ1) nInit
    (.fst (.snd (.snd (.var (.succ .zero))))) (.snd (.snd (.snd (.var (.succ .zero)))))
    (.fst (.var .zero)) (.fst (.snd (.var .zero)))
  simp only [reHdr, hdrIkA, reSpk, reIk, Expr.cost, Nat.reduceAdd] at hh1 hh2 hspk hf
  unfold isKeyIndRespStillFreshE
  simp only [reRev, reSendHon, reHdr, hdrIkA, reSpk, reIk,
    eLet, v, Ext.wk, Ext.refl, Ext.step, Expr.cost, Nat.reduceAdd]
  omega

attribute [local irreducible] isKeyIndRespStillFreshE

def initStillFreshStepCost (nId nSpk nResp : ℕ) : ℕ :=
  96 * nId + 104 * nSpk + 7000 * nResp + 300

def respStillFreshStepCost (nId nSpk nInit : ℕ) : ℕ :=
  7100 * nInit + 192 * nId + 104 * nSpk + 460

def allTestedSessionsFreshBoundedCost (nInit nResp nId nSpk : ℕ) : ℕ :=
  nInit * initStillFreshStepCost nId nSpk nResp +
    nResp * respStillFreshStepCost nId nSpk nInit + 32

/-- Bounded scan for `allTestedSessionsFresh P st`. -/
def allTestedSessionsFreshBoundedE (nInit nResp nId nSpk : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stE : E2EExpr Γ (e2eKeyIndStateTy ℓ S)) : E2EExpr Γ .bool :=
  eLet stE fun st =>
    .and
      (.not (eAny nInit (stSess (v st)) fun s =>
        .not (orE
          (.not (ieTested (v s)))
          (isKeyIndInitStillFreshE nId nSpk nResp
            (stPrin (v st)) (stSpk (v st)) (stResp (v st)) (v s)))))
      (.not (eAny nResp (stResp (v st)) fun r =>
        .not (orE
          (.not (reTested (v r)))
          (isKeyIndRespStillFreshE nId nSpk nInit
            (stPrin (v st)) (stSpk (v st)) (stSess (v st)) (v r)))))

theorem eval_allTestedSessionsFreshBoundedE (nInit nResp nId nSpk : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (stE : E2EExpr Γ (e2eKeyIndStateTy ℓ S)) (ρ : Env Γ)
    {st : SignalPqxdh.KeyIndState S}
    (hst : stE.eval ρ = e2eKeyIndStateToVal st)
    (hInit : st.sessions.length ≤ nInit) (hResp : st.respSessions.length ≤ nResp)
    (hId : st.principals.length ≤ nId) (hSpk : st.spkBundles.length ≤ nSpk) :
    (allTestedSessionsFreshBoundedE nInit nResp nId nSpk stE).eval ρ =
      allTestedSessionsFresh P st := by
  have hInit' : (st.sessions.map (e2eInitiatorEntryToVal (ℓ := ℓ))).length ≤ nInit := by
    simp [hInit]
  have hResp' : (st.respSessions.map (e2eRespEntryToVal (ℓ := ℓ))).length ≤ nResp := by
    simp [hResp]
  set ρ0 : Env (e2eKeyIndStateTy ℓ S :: Γ) := .cons (e2eKeyIndStateToVal st) ρ with hρ0
  have hSess0 : (stSess (O := e2eOps ℓ P C K decT encT) (.var .zero)).eval ρ0 =
      st.sessions.map e2eInitiatorEntryToVal := rfl
  have hResp0 : (stResp (O := e2eOps ℓ P C K decT encT) (.var .zero)).eval ρ0 =
      st.respSessions.map e2eRespEntryToVal := rfl
  simp only [allTestedSessionsFreshBoundedE, allTestedSessionsFresh, list_all_eq_not_any_not,
    eLet, v, Ext.wk, Ext.refl, Ext.step, Expr.eval, hst, ← hρ0]
  dsimp only [eAny, Expr.eval]
  simp only [hSess0, hResp0, List.take_of_length_le hInit', List.take_of_length_le hResp',
    List.any_map]
  have hanyInit :
      st.sessions.any ((fun x =>
        !((!(ieTested (O := e2eOps ℓ P C K decT encT) (.var .zero)).eval (.cons x ρ0)) ||
          (isKeyIndInitStillFreshE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
            nId nSpk nResp
            (stPrin (.var (.succ .zero))) (stSpk (.var (.succ .zero)))
            (stResp (.var (.succ .zero))) (.var .zero)).eval (.cons x ρ0))) ∘
        e2eInitiatorEntryToVal) =
      st.sessions.any (fun s =>
        !(!s.tested ||
          SignalPqxdh.isKeyIndInitStillFresh P true st.principals st.spkBundles
            st.respSessions s)) := by
    apply List.any_congr rfl
    intro s
    dsimp only [Function.comp_apply]
    set ρs : Env (e2eInitiatorEntryTy ℓ S :: e2eKeyIndStateTy ℓ S :: Γ) :=
      .cons (e2eInitiatorEntryToVal s) ρ0
    have hp1 : (stPrin (O := e2eOps ℓ P C K decT encT) (.var (.succ .zero))).eval ρs =
        st.principals.map (Prod.map id e2ePrincipalEntryToVal) := rfl
    have hb1 : (stSpk (O := e2eOps ℓ P C K decT encT) (.var (.succ .zero))).eval ρs =
        st.spkBundles.map (Prod.map id e2eSpkBundleEntryToVal) := rfl
    have hr1 : (stResp (O := e2eOps ℓ P C K decT encT) (.var (.succ .zero))).eval ρs =
        st.respSessions.map e2eRespEntryToVal := rfl
    have hs1 : (Expr.var (O := e2eOps ℓ P C K decT encT) .zero).eval ρs =
        e2eInitiatorEntryToVal s := rfl
    have ht1 : (ieTested (O := e2eOps ℓ P C K decT encT) (.var .zero)).eval ρs = s.tested := rfl
    simp only [ht1,
      eval_isKeyIndInitStillFreshE nId nSpk nResp hP _ _ _ _ ρs hp1 hb1 hr1 hs1 hId hSpk hResp]
  have hanyResp :
      st.respSessions.any ((fun x =>
        !((!(reTested (O := e2eOps ℓ P C K decT encT) (.var .zero)).eval (.cons x ρ0)) ||
          (isKeyIndRespStillFreshE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
            nId nSpk nInit
            (stPrin (.var (.succ .zero))) (stSpk (.var (.succ .zero)))
            (stSess (.var (.succ .zero))) (.var .zero)).eval (.cons x ρ0))) ∘
        e2eRespEntryToVal) =
      st.respSessions.any (fun r =>
        !(!r.tested ||
          SignalPqxdh.isKeyIndRespStillFresh P true st.principals st.spkBundles
            st.sessions r)) := by
    apply List.any_congr rfl
    intro r
    dsimp only [Function.comp_apply]
    set ρr : Env (e2eRespEntryTy ℓ S :: e2eKeyIndStateTy ℓ S :: Γ) :=
      .cons (e2eRespEntryToVal r) ρ0
    have hp1 : (stPrin (O := e2eOps ℓ P C K decT encT) (.var (.succ .zero))).eval ρr =
        st.principals.map (Prod.map id e2ePrincipalEntryToVal) := rfl
    have hb1 : (stSpk (O := e2eOps ℓ P C K decT encT) (.var (.succ .zero))).eval ρr =
        st.spkBundles.map (Prod.map id e2eSpkBundleEntryToVal) := rfl
    have hi1 : (stSess (O := e2eOps ℓ P C K decT encT) (.var (.succ .zero))).eval ρr =
        st.sessions.map e2eInitiatorEntryToVal := rfl
    have hr1 : (Expr.var (O := e2eOps ℓ P C K decT encT) .zero).eval ρr =
        e2eRespEntryToVal r := rfl
    have ht1 : (reTested (O := e2eOps ℓ P C K decT encT) (.var .zero)).eval ρr = r.tested := rfl
    simp only [ht1,
      eval_isKeyIndRespStillFreshE nId nSpk nInit hP _ _ _ _ ρr hp1 hb1 hi1 hr1 hId hSpk hInit]
  simp only [eval_orE, Expr.eval]
  rw [hanyInit, hanyResp]

theorem cost_allTestedSessionsFreshBoundedE (nInit nResp nId nSpk : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : E2EExpr Γ (e2eKeyIndStateTy ℓ S)) :
    (allTestedSessionsFreshBoundedE nInit nResp nId nSpk stE).cost ≤
      stE.cost + allTestedSessionsFreshBoundedCost nInit nResp nId nSpk := by
  let Δ0 := e2eKeyIndStateTy ℓ S :: Γ
  let Δs := e2eInitiatorEntryTy ℓ S :: Δ0
  let Δr := e2eRespEntryTy ℓ S :: Δ0
  have hs := cost_isKeyIndInitStillFreshE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δs) nId nSpk nResp
    (stPrin (.var (.succ .zero))) (stSpk (.var (.succ .zero)))
    (stResp (.var (.succ .zero))) (.var .zero)
  have hr := cost_isKeyIndRespStillFreshE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δr) nId nSpk nInit
    (stPrin (.var (.succ .zero))) (stSpk (.var (.succ .zero)))
    (stSess (.var (.succ .zero))) (.var .zero)
  simp only [stPrin, stSpk, stSess, stResp, Expr.cost, Nat.reduceAdd] at hs hr
  unfold allTestedSessionsFreshBoundedE allTestedSessionsFreshBoundedCost
  simp only [stSess, stResp, stPrin, stSpk, ieTested, reTested, cost_orE,
    eLet, eAny, v, Ext.wk, Ext.refl, Ext.step, Expr.cost, Nat.reduceAdd]
  have hsB :
      17 +
      (isKeyIndInitStillFreshE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
        (decT := decT) (encT := encT) (Γ := Δs) nId nSpk nResp
        (.fst (.snd (.var (.succ .zero)))) (.fst (.snd (.snd (.var (.succ .zero)))))
        (.fst (.snd (.snd (.snd (.snd (.snd (.var (.succ .zero)))))))) (.var .zero)).cost +
      4 + 1 + 1 ≤ initStillFreshStepCost nId nSpk nResp := by
    simp only [initStillFreshStepCost]; omega
  have hsM :
      nInit * (17 +
      (isKeyIndInitStillFreshE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
        (decT := decT) (encT := encT) (Γ := Δs) nId nSpk nResp
        (.fst (.snd (.var (.succ .zero)))) (.fst (.snd (.snd (.var (.succ .zero)))))
        (.fst (.snd (.snd (.snd (.snd (.snd (.var (.succ .zero)))))))) (.var .zero)).cost +
      4 + 1 + 1) ≤ nInit * initStillFreshStepCost nId nSpk nResp :=
    Nat.mul_le_mul_left nInit hsB
  have hrB :
      12 +
      (isKeyIndRespStillFreshE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
        (decT := decT) (encT := encT) (Γ := Δr) nId nSpk nInit
        (.fst (.snd (.var (.succ .zero)))) (.fst (.snd (.snd (.var (.succ .zero)))))
        (.fst (.snd (.snd (.snd (.snd (.var (.succ .zero))))))) (.var .zero)).cost +
      4 + 1 + 1 ≤ respStillFreshStepCost nId nSpk nInit := by
    simp only [respStillFreshStepCost]; omega
  have hrM :
      nResp * (12 +
      (isKeyIndRespStillFreshE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
        (decT := decT) (encT := encT) (Γ := Δr) nId nSpk nInit
        (.fst (.snd (.var (.succ .zero)))) (.fst (.snd (.snd (.var (.succ .zero)))))
        (.fst (.snd (.snd (.snd (.snd (.var (.succ .zero))))))) (.var .zero)).cost +
      4 + 1 + 1) ≤ nResp * respStillFreshStepCost nId nSpk nInit :=
    Nat.mul_le_mul_left nResp hrB
  omega

attribute [local irreducible] allTestedSessionsFreshBoundedE

def allTestedSessionsFreshCost (S : SignalPqxdh.Setup) : ℕ :=
  allTestedSessionsFreshBoundedCost S.N_send_tot S.N_recv_tot S.N_id S.N_spk_tot

def allTestedSessionsFreshE {Γ : List (Ty (e2eSig ℓ))}
    (stE : E2EExpr Γ (e2eKeyIndStateTy ℓ S)) : E2EExpr Γ .bool :=
  allTestedSessionsFreshBoundedE S.N_send_tot S.N_recv_tot S.N_id S.N_spk_tot stE

theorem eval_allTestedSessionsFreshE (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : E2EExpr Γ (e2eKeyIndStateTy ℓ S)) (ρ : Env Γ)
    {st : SignalPqxdh.KeyIndState S}
    (hst : stE.eval ρ = e2eKeyIndStateToVal st) (hSetup : KeyIndSetupBounded S st) :
    (allTestedSessionsFreshE stE).eval ρ = allTestedSessionsFresh P st :=
  eval_allTestedSessionsFreshBoundedE S.N_send_tot S.N_recv_tot S.N_id S.N_spk_tot hP stE ρ hst
    hSetup.sessions_le hSetup.respSessions_le hSetup.principals_le hSetup.spkBundles_le

theorem cost_allTestedSessionsFreshE {Γ : List (Ty (e2eSig ℓ))}
    (stE : E2EExpr Γ (e2eKeyIndStateTy ℓ S)) :
    (allTestedSessionsFreshE stE).cost ≤ stE.cost + allTestedSessionsFreshCost S :=
  cost_allTestedSessionsFreshBoundedE S.N_send_tot S.N_recv_tot S.N_id S.N_spk_tot stE

def allTestedSessionsFreshC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : E2EExpr Γ (e2eKeyIndStateTy ℓ S)) :
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) Γ .bool :=
  .ret (allTestedSessionsFreshE stE)

theorem eval_allTestedSessionsFreshC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (stE : E2EExpr Γ (e2eKeyIndStateTy ℓ S)) (ρ : Env Γ)
    {st : SignalPqxdh.KeyIndState S}
    (hst : stE.eval ρ = e2eKeyIndStateToVal st) (hSetup : KeyIndSetupBounded S st) :
    (allTestedSessionsFreshC I₀ stE).eval ρ = pure (allTestedSessionsFresh P st) := by
  simp only [allTestedSessionsFreshC, Comp.eval, eval_allTestedSessionsFreshE hP stE ρ hst hSetup]

theorem cost_allTestedSessionsFreshC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : E2EExpr Γ (e2eKeyIndStateTy ℓ S)) :
    (allTestedSessionsFreshC I₀ stE).cost ≤ stE.cost + allTestedSessionsFreshCost S + 1 := by
  have h := cost_allTestedSessionsFreshE stE
  simp only [allTestedSessionsFreshC, Comp.cost]; omega

@[simp] theorem queries_allTestedSessionsFreshC {ι : Type} {T : OracleSpec ι}
    (I₀ : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (stE : E2EExpr Γ (e2eKeyIndStateTy ℓ S))
    (w : (stepAIface ℓ I₀).Tag → ℕ) :
    (allTestedSessionsFreshC I₀ stE).queries w (fun _ => 0) = 0 := rfl

attribute [local irreducible] allTestedSessionsFreshE allTestedSessionsFreshC

def finishPrefixBoundedCost (qStart nInit nResp nId nSpk : ℕ) : ℕ :=
  allTestedSessionsFreshBoundedCost nInit nResp nId nSpk + 2 * drvWonCost qStart + 64

def finishPrefixBoundedC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nInit nResp nId nSpk : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (b'E flipE : E2EExpr Γ .bool) :
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) Γ .bool :=
  .bind (.ret (.pair σE (.pair b'E flipE)))
    (.ite (.not (drvPaused (.fst .v0)))
      (.ret (.bool false))
      (.ite (.not (allTestedSessionsFreshBoundedE nInit nResp nId nSpk (drvSt (.fst .v0))))
        (.bind (.sample (I := stepAIface ℓ I₀) UniformSamplerTag.bool .unit)
          (.ret (boolXorE .v0 (.snd (.snd .v1)))))
        (.ret (boolXorE
          (.ite (drvWonE qStart (.fst .v0) (.bool true))
            (.bool true)
            (.ite (drvWonE qStart (.fst .v0) (.bool false))
              (.bool false)
              (.fst (.snd .v0))))
          (.snd (.snd .v0))))))

private theorem expr_eval_ite_cond {Γ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)}
    (c : E2EExpr Γ .bool) (a b : E2EExpr Γ τ) (ρ : Env Γ) :
    (Expr.ite c a b).eval ρ = cond (c.eval ρ) (a.eval ρ) (b.eval ρ) := by
  simp only [Expr.eval]; cases c.eval ρ <;> rfl

private theorem comp_eval_ite_cond {ι : Type} {T : OracleSpec ι}
    {I : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)}
    (c : E2EExpr Γ .bool)
    (a b : Comp (e2eOps ℓ P C K decT encT) I Γ τ) (ρ : Env Γ) :
    (Comp.ite c a b).eval ρ = cond (c.eval ρ) (a.eval ρ) (b.eval ρ) := by
  simp only [Comp.eval]; cases c.eval ρ <;> rfl

private theorem comp_eval_bind_ret {ι : Type} {T : OracleSpec ι}
    {I : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))} {α β : Ty (e2eSig ℓ)}
    (x : E2EExpr Γ α)
    (k : Comp (e2eOps ℓ P C K decT encT) I (α :: Γ) β) (ρ : Env Γ) :
    (Comp.bind (.ret x) k).eval ρ = k.eval (.cons (x.eval ρ) ρ) := by
  simp only [Comp.eval, pure_bind]

theorem eval_finishPrefixBoundedC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nInit nResp nId nSpk : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (b'E flipE : E2EExpr Γ .bool) (ρ : Env Γ)
    (σ : BHE2EDrvState S ℓ)
    (_ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (_qep : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (hσ : σE.eval ρ = e2eDrvStateEnc σ)
    (hInsts : σ.insts.length ≤ qStart)
    (hInit : σ.st.sessions.length ≤ nInit)
    (hResp : σ.st.respSessions.length ≤ nResp)
    (hId : σ.st.principals.length ≤ nId)
    (hSpk : σ.st.spkBundles.length ≤ nSpk) :
    (finishPrefixBoundedC I₀ qStart nInit nResp nId nSpk σE b'E flipE).eval ρ =
      (stepAIface ℓ I₀).liftP
        (bhShallowFinishPrefix P σ (b'E.eval ρ) (flipE.eval ρ)) := by
  set ρ0 : Env ((e2eDrvStateTy S ℓ).prod (.prod .bool .bool) :: Γ) :=
    .cons (e2eDrvStateEnc σ, (b'E.eval ρ, flipE.eval ρ)) ρ with hρ0
  have hpair0 :
      (Expr.pair σE (.pair b'E flipE)).eval ρ =
        (e2eDrvStateEnc σ, (b'E.eval ρ, flipE.eval ρ)) := by
    simp only [Expr.eval, hσ]
  have hσ0 : (Expr.fst (O := e2eOps ℓ P C K decT encT) Expr.v0).eval ρ0 =
      e2eDrvStateEnc σ := rfl
  have hPaused0 :
      (Expr.not (O := e2eOps ℓ P C K decT encT) (drvPaused (.fst Expr.v0))).eval ρ0 =
        !σ.paused := rfl
  have hSt0 : (drvSt (O := e2eOps ℓ P C K decT encT) (.fst Expr.v0)).eval ρ0 =
      e2eKeyIndStateToVal σ.st := rfl
  have hb'0 : (Expr.fst (O := e2eOps ℓ P C K decT encT) (.snd Expr.v0)).eval ρ0 =
      b'E.eval ρ := rfl
  have hflip0 : (Expr.snd (O := e2eOps ℓ P C K decT encT) (.snd Expr.v0)).eval ρ0 =
      flipE.eval ρ := rfl
  have hsamp : (stepAIface ℓ I₀).smp.samp UniformSamplerTag.bool () = ($ᵗ Bool) := rfl
  unfold finishPrefixBoundedC
  rw [comp_eval_bind_ret, hpair0, ← hρ0, comp_eval_ite_cond, hPaused0]
  cases hp : σ.paused
  · simp only [bhShallowFinishPrefix, hp, Bool.not_false, cond, ↓reduceIte, Comp.eval, Expr.eval,
      liftP_pure]
  · simp only [Bool.not_true, cond]
    rw [comp_eval_ite_cond]
    have hnotFresh :
        (Expr.not (O := e2eOps ℓ P C K decT encT)
          (allTestedSessionsFreshBoundedE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
            nInit nResp nId nSpk (drvSt (.fst .v0)))).eval
          ρ0 = !(allTestedSessionsFresh P σ.st) := by
      simp only [Expr.eval,
        eval_allTestedSessionsFreshBoundedE nInit nResp nId nSpk hP _ ρ0 hSt0 hInit hResp hId hSpk]
    rw [hnotFresh]
    cases hf : allTestedSessionsFresh P σ.st
    · simp only [bhShallowFinishPrefix, hp, hf, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        cond, ↓reduceIte, Comp.eval, Expr.eval, hsamp, liftP_bind, liftP_pure, eval_boolXorE]
      congr 1
    · simp only [bhShallowFinishPrefix, hp, hf, Bool.not_true, Bool.false_eq_true, cond, ↓reduceIte,
        Comp.eval, liftP_pure, eval_boolXorE, hflip0]
      rw [expr_eval_ite_cond, expr_eval_ite_cond,
          eval_drvWonE qStart _ _ ρ0 hσ0 hInsts,
          eval_drvWonE qStart _ _ ρ0 hσ0 hInsts, hb'0]
      have hbt : (Expr.bool (O := e2eOps ℓ P C K decT encT) true).eval ρ0 = true := rfl
      have hbf : (Expr.bool (O := e2eOps ℓ P C K decT encT) false).eval ρ0 = false := rfl
      rw [hbt, hbf]
      cases bhE2EDrvWon σ true <;> cases bhE2EDrvWon σ false <;> rfl

theorem cost_finishPrefixBoundedC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nInit nResp nId nSpk : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (b'E flipE : E2EExpr Γ .bool) :
    (finishPrefixBoundedC I₀ qStart nInit nResp nId nSpk σE b'E flipE).cost ≤
      σE.cost + b'E.cost + flipE.cost + finishPrefixBoundedCost qStart nInit nResp nId nSpk := by
  let Δ0 := (e2eDrvStateTy S ℓ).prod (.prod .bool .bool) :: Γ
  have hf := cost_allTestedSessionsFreshBoundedE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ0) nInit nResp nId nSpk (drvSt (.fst .v0))
  have hwT := cost_drvWonE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ0) qStart (.fst .v0) (.bool true)
  have hwF := cost_drvWonE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ0) qStart (.fst .v0) (.bool false)
  have hsCost : (stepAIface ℓ I₀).smp.sCost UniformSamplerTag.bool = 1 := rfl
  simp only [drvSt, Expr.v0, Expr.cost, Nat.reduceAdd] at hf hwT hwF
  unfold finishPrefixBoundedC finishPrefixBoundedCost
  simp only [drvPaused, drvSt, cost_boolXorE, Expr.v0, Expr.v1, Comp.cost, Expr.cost,
    hsCost, Nat.reduceAdd]
  omega

@[simp] theorem queries_finishPrefixBoundedC {ι : Type} {T : OracleSpec ι}
    (I₀ : Iface (e2eSig ℓ) T) (qStart nInit nResp nId nSpk : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (b'E flipE : E2EExpr Γ .bool)
    (w : (stepAIface ℓ I₀).Tag → ℕ) :
    (finishPrefixBoundedC I₀ qStart nInit nResp nId nSpk σE b'E flipE).queries w (fun _ => 0) =
      0 := by
  simp [finishPrefixBoundedC, Comp.queries]

attribute [local irreducible] finishPrefixBoundedC

def finishPrefixCost (S : SignalPqxdh.Setup) (qStart _nAdv : ℕ) : ℕ :=
  finishPrefixBoundedCost qStart S.N_send_tot S.N_recv_tot S.N_id S.N_spk_tot

/-- End-of-game freshness check and bit decision `bhShallowFinishPrefix`. -/
def finishPrefixC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart _nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (b'E flipE : E2EExpr Γ .bool) :
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) Γ .bool :=
  finishPrefixBoundedC I₀ qStart S.N_send_tot S.N_recv_tot S.N_id S.N_spk_tot σE b'E flipE

theorem eval_finishPrefixC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (b'E flipE : E2EExpr Γ .bool) (ρ : Env Γ)
    (σ : BHE2EDrvState S ℓ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (qep : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (hσ : σE.eval ρ = e2eDrvStateEnc σ)
    (hInsts : σ.insts.length ≤ qStart)
    (hSetup : KeyIndSetupBounded S σ.st) :
    (finishPrefixC I₀ qStart nAdv σE b'E flipE).eval ρ =
      (stepAIface ℓ I₀).liftP
        (bhShallowFinishPrefix P σ (b'E.eval ρ) (flipE.eval ρ)) :=
  eval_finishPrefixBoundedC I₀ qStart S.N_send_tot S.N_recv_tot S.N_id S.N_spk_tot
    σE b'E flipE ρ σ ki qep hP hσ hInsts
    hSetup.sessions_le hSetup.respSessions_le hSetup.principals_le hSetup.spkBundles_le

theorem cost_finishPrefixC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (b'E flipE : E2EExpr Γ .bool) :
    (finishPrefixC I₀ qStart nAdv σE b'E flipE).cost ≤
      σE.cost + b'E.cost + flipE.cost + finishPrefixCost S qStart nAdv :=
  cost_finishPrefixBoundedC I₀ qStart S.N_send_tot S.N_recv_tot S.N_id S.N_spk_tot σE b'E flipE

@[simp] theorem queries_finishPrefixC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (b'E flipE : E2EExpr Γ .bool)
    (w : (stepAIface ℓ I₀).Tag → ℕ) :
    (finishPrefixC I₀ qStart nAdv σE b'E flipE).queries w (fun _ => 0) = 0 :=
  queries_finishPrefixBoundedC I₀ qStart S.N_send_tot S.N_recv_tot S.N_id S.N_spk_tot
    σE b'E flipE w

attribute [local irreducible] finishPrefixC

def testedInitSessionsFreshE (nInst nSend nId nSpk nRecv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stE : E2EExpr Γ (e2eKeyIndStateTy ℓ S)) : E2EExpr Γ .bool :=
  eLet stE fun st =>
    let testedListE : E2EExpr (e2eKeyIndStateTy ℓ S :: Γ) (.list (e2eInitiatorEntryTy ℓ S)) :=
      .foldrB nSend (stSess (v st)) .nil (.ite (ieTested .v0) (.cons .v0 .v1) .v1)
    .not (eAny nInst testedListE fun s =>
      .not (isKeyIndInitStillFreshE nId nSpk nRecv
        (stPrin (v st)) (stSpk (v st)) (stResp (v st)) (v s)))

def finishPrefixClampedCost (S : SignalPqxdh.Setup) (qStart nAdv : ℕ) : ℕ :=
  let nId := min nAdv S.N_id
  let nSpk := min nAdv S.N_spk_tot
  let nSend := min nAdv S.N_send_tot
  let nRecv := min nAdv S.N_recv_tot
  let nInst := min qStart nSend
  24 * nSend + nInst * initStillFreshStepCost nId nSpk nRecv + 2 * drvWonCost nInst + 160

def finishPrefixClampedSize (S : SignalPqxdh.Setup) (qStart nAdv : ℕ) : ℕ :=
  let nId := min nAdv S.N_id
  let nSpk := min nAdv S.N_spk_tot
  let nSend := min nAdv S.N_send_tot
  let nRecv := min nAdv S.N_recv_tot
  let nInst := min qStart nSend
  4 * ReductionDsl.bits nInst + 2 * ReductionDsl.bits nSend + 2 * ReductionDsl.bits nRecv +
    3 * ReductionDsl.bits nId + 2 * ReductionDsl.bits nSpk + 1900

/-- Clamped end-of-game freshness check and bit decision `bhShallowFinishPrefix`. -/
def finishPrefixClampedC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (b'E flipE : E2EExpr Γ .bool) :
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) Γ .bool :=
  let nId := min nAdv S.N_id
  let nSpk := min nAdv S.N_spk_tot
  let nSend := min nAdv S.N_send_tot
  let nRecv := min nAdv S.N_recv_tot
  let nInst := min qStart nSend
  .bind (.ret (.pair σE (.pair b'E flipE)))
    (.ite (.not (drvPaused (.fst .v0)))
      (.ret (.bool false))
      (.ite (.not (testedInitSessionsFreshE nInst nSend nId nSpk nRecv (drvSt (.fst .v0))))
        (.bind (.sample (I := stepAIface ℓ I₀) UniformSamplerTag.bool .unit)
          (.ret (boolXorE .v0 (.snd (.snd .v1)))))
        (.ret (boolXorE
          (.ite (drvWonE nInst (.fst .v0) (.bool true))
            (.bool true)
            (.ite (drvWonE nInst (.fst .v0) (.bool false))
              (.bool false)
              (.fst (.snd .v0))))
          (.snd (.snd .v0))))))

@[simp] theorem queries_finishPrefixClampedC {ι : Type} {T : OracleSpec ι}
    (I₀ : Iface (e2eSig ℓ) T) (qStart nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (b'E flipE : E2EExpr Γ .bool)
    (w : (stepAIface ℓ I₀).Tag → ℕ) :
    (finishPrefixClampedC I₀ qStart nAdv σE b'E flipE).queries w (fun _ => 0) = 0 := by
  simp [finishPrefixClampedC, Comp.queries]

private theorem foldr_ieTested_filter {Γ : List (Ty (e2eSig ℓ))}
    (ρ0 : Env (e2eKeyIndStateTy ℓ S :: Γ))
    (xs : List (SignalPqxdh.KeyIndInitiatorEntry S)) :
    (xs.map (e2eInitiatorEntryToVal (ℓ := ℓ))).foldr
      (fun x (acc : (Ty.list (e2eInitiatorEntryTy ℓ S)).denote) =>
        if (ieTested (O := e2eOps ℓ P C K decT encT) Expr.v0).eval
            (Env.cons (t := e2eInitiatorEntryTy ℓ S) x
              (Env.cons (t := .list (e2eInitiatorEntryTy ℓ S)) acc ρ0)) = true then
          (Expr.v0 (O := e2eOps ℓ P C K decT encT)).eval
              (Env.cons (t := e2eInitiatorEntryTy ℓ S) x
                (Env.cons (t := .list (e2eInitiatorEntryTy ℓ S)) acc ρ0)) ::
            (Expr.v1 (O := e2eOps ℓ P C K decT encT)).eval
              (Env.cons (t := e2eInitiatorEntryTy ℓ S) x
                (Env.cons (t := .list (e2eInitiatorEntryTy ℓ S)) acc ρ0))
        else (Expr.v1 (O := e2eOps ℓ P C K decT encT)).eval
            (Env.cons (t := e2eInitiatorEntryTy ℓ S) x
              (Env.cons (t := .list (e2eInitiatorEntryTy ℓ S)) acc ρ0)))
      ([] : (Ty.list (e2eInitiatorEntryTy ℓ S)).denote) =
    (xs.filter (·.tested)).map (e2eInitiatorEntryToVal (ℓ := ℓ)) := by
  induction xs with
  | nil => rfl
  | cons s rest ih =>
    let acc0 : (Ty.list (e2eInitiatorEntryTy ℓ S)).denote :=
      (rest.filter (·.tested)).map (e2eInitiatorEntryToVal (ℓ := ℓ))
    have ht : (ieTested (O := e2eOps ℓ P C K decT encT) Expr.v0).eval
        (Env.cons (t := e2eInitiatorEntryTy ℓ S) (e2eInitiatorEntryToVal (ℓ := ℓ) s)
          (Env.cons (t := .list (e2eInitiatorEntryTy ℓ S)) acc0 ρ0)) = s.tested := rfl
    have hv0 : (Expr.v0 (O := e2eOps ℓ P C K decT encT)).eval
        (Env.cons (t := e2eInitiatorEntryTy ℓ S) (e2eInitiatorEntryToVal (ℓ := ℓ) s)
          (Env.cons (t := .list (e2eInitiatorEntryTy ℓ S)) acc0 ρ0)) =
        e2eInitiatorEntryToVal (ℓ := ℓ) s := rfl
    have hv1 : (Expr.v1 (O := e2eOps ℓ P C K decT encT)).eval
        (Env.cons (t := e2eInitiatorEntryTy ℓ S) (e2eInitiatorEntryToVal (ℓ := ℓ) s)
          (Env.cons (t := .list (e2eInitiatorEntryTy ℓ S)) acc0 ρ0)) = acc0 := rfl
    simp only [List.map_cons, List.foldr_cons]
    change (if (ieTested (O := e2eOps ℓ P C K decT encT) Expr.v0).eval _ = true then _ else _) = _
    rw [ih]
    change (if (ieTested (O := e2eOps ℓ P C K decT encT) Expr.v0).eval
        (Env.cons (t := e2eInitiatorEntryTy ℓ S) (e2eInitiatorEntryToVal (ℓ := ℓ) s)
          (Env.cons (t := .list (e2eInitiatorEntryTy ℓ S)) acc0 ρ0)) = true then _ else _) = _
    rw [ht, hv0, hv1]
    simp only [acc0, List.filter_cons]
    cases s.tested <;> rfl

private theorem filter_tested_any_not_eq {α : Type} (t : α → Bool) (Q : α → Bool) :
    ∀ xs : List α,
      (xs.filter t).any (fun s => !(Q s)) = xs.any (fun s => !(!(t s) || Q s))
  | [] => rfl
  | s :: rest => by
    simp only [List.filter_cons, List.any_cons]
    cases t s <;> simp [filter_tested_any_not_eq t Q rest]

theorem eval_testedInitSessionsFreshE (nInst nSend nId nSpk nRecv : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (stE : E2EExpr Γ (e2eKeyIndStateTy ℓ S)) (ρ : Env Γ)
    {st : SignalPqxdh.KeyIndState S}
    (hst : stE.eval ρ = e2eKeyIndStateToVal st)
    (hTested : (st.sessions.filter (·.tested)).length ≤ nInst)
    (hInit : st.sessions.length ≤ nSend) (hResp : st.respSessions.length ≤ nRecv)
    (hId : st.principals.length ≤ nId) (hSpk : st.spkBundles.length ≤ nSpk)
    (hRespUntested : ∀ r ∈ st.respSessions, r.tested = false) :
    (testedInitSessionsFreshE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      nInst nSend nId nSpk nRecv stE).eval ρ =
      allTestedSessionsFresh P st := by
  have hInit' : (st.sessions.map (e2eInitiatorEntryToVal (ℓ := ℓ))).length ≤ nSend := by
    simp [hInit]
  have hTested' : ((st.sessions.filter (·.tested)).map (e2eInitiatorEntryToVal (ℓ := ℓ))).length ≤
      nInst := by
    simp [hTested]
  set ρ0 : Env (e2eKeyIndStateTy ℓ S :: Γ) := .cons (e2eKeyIndStateToVal st) ρ with hρ0
  have hSess0 : (stSess (O := e2eOps ℓ P C K decT encT) (.var .zero)).eval ρ0 =
      st.sessions.map e2eInitiatorEntryToVal := rfl
  simp only [testedInitSessionsFreshE, allTestedSessionsFresh, list_all_eq_not_any_not,
    eLet, v, Ext.wk, Ext.refl, Ext.step, Expr.eval, hst, ← hρ0]
  dsimp only [eAny, Expr.eval]
  rw [hSess0, List.take_of_length_le hInit', foldr_ieTested_filter,
    List.take_of_length_le hTested', List.any_map]
  have hanyInit :
      (st.sessions.filter (·.tested)).any ((fun x =>
        !((isKeyIndInitStillFreshE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
            nId nSpk nRecv
            (stPrin (.var (.succ .zero))) (stSpk (.var (.succ .zero)))
            (stResp (.var (.succ .zero))) (.var .zero)).eval (.cons x ρ0))) ∘
        e2eInitiatorEntryToVal) =
      (st.sessions.filter (·.tested)).any (fun s =>
        !(SignalPqxdh.isKeyIndInitStillFresh P true st.principals st.spkBundles
            st.respSessions s)) := by
    apply List.any_congr rfl
    intro s
    dsimp only [Function.comp_apply]
    set ρs : Env (e2eInitiatorEntryTy ℓ S :: e2eKeyIndStateTy ℓ S :: Γ) :=
      .cons (e2eInitiatorEntryToVal s) ρ0
    have hp1 : (stPrin (O := e2eOps ℓ P C K decT encT) (.var (.succ .zero))).eval ρs =
        st.principals.map (Prod.map id e2ePrincipalEntryToVal) := rfl
    have hb1 : (stSpk (O := e2eOps ℓ P C K decT encT) (.var (.succ .zero))).eval ρs =
        st.spkBundles.map (Prod.map id e2eSpkBundleEntryToVal) := rfl
    have hr1 : (stResp (O := e2eOps ℓ P C K decT encT) (.var (.succ .zero))).eval ρs =
        st.respSessions.map e2eRespEntryToVal := rfl
    have hs1 : (Expr.var (O := e2eOps ℓ P C K decT encT) .zero).eval ρs =
        e2eInitiatorEntryToVal s := rfl
    simp only [eval_isKeyIndInitStillFreshE nId nSpk nRecv hP _ _ _ _ ρs hp1 hb1 hr1 hs1 hId hSpk hResp]
  have hanyResp :
      st.respSessions.any (fun r =>
        !(!r.tested ||
          SignalPqxdh.isKeyIndRespStillFresh P true st.principals st.spkBundles
            st.sessions r)) = false := by
    rw [List.any_eq_false]
    intro r hr
    simp [hRespUntested r hr]
  rw [hanyInit,
    filter_tested_any_not_eq (fun x : SignalPqxdh.KeyIndInitiatorEntry S => x.tested),
    hanyResp]
  simp

theorem cost_testedInitSessionsFreshE (nInst nSend nId nSpk nRecv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : E2EExpr Γ (e2eKeyIndStateTy ℓ S)) :
    (testedInitSessionsFreshE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      nInst nSend nId nSpk nRecv stE).cost ≤
      stE.cost + 24 * nSend + nInst * initStillFreshStepCost nId nSpk nRecv + 32 := by
  let Δ0 := e2eKeyIndStateTy ℓ S :: Γ
  let Δs := e2eInitiatorEntryTy ℓ S :: Δ0
  have hs := cost_isKeyIndInitStillFreshE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δs) nId nSpk nRecv
    (stPrin (.var (.succ .zero))) (stSpk (.var (.succ .zero)))
    (stResp (.var (.succ .zero))) (.var .zero)
  simp only [stPrin, stSpk, stResp, Expr.cost, Nat.reduceAdd] at hs
  unfold testedInitSessionsFreshE
  simp only [stSess, stPrin, stSpk, stResp, ieTested,
    eLet, eAny, v, Ext.wk, Ext.refl, Ext.step, Expr.v0, Expr.v1, Expr.cost, Nat.reduceAdd]
  have hm : max 3 1 = 3 := rfl
  rw [hm]
  have hsB :
      (isKeyIndInitStillFreshE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
        (decT := decT) (encT := encT) (Γ := Δs) nId nSpk nRecv
        (.fst (.snd (.var (.succ .zero)))) (.fst (.snd (.snd (.var (.succ .zero)))))
        (.fst (.snd (.snd (.snd (.snd (.snd (.var (.succ .zero)))))))) (.var .zero)).cost +
      1 + 1 ≤ initStillFreshStepCost nId nSpk nRecv := by
    simp only [initStillFreshStepCost]; omega
  have hsM := Nat.mul_le_mul_left nInst hsB
  omega

@[simp] private theorem size_v_aux {Γ Δ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)} [Ext Γ Δ]
    (x : Var Γ τ) :
    (v (O := e2eOps ℓ P C K decT encT) (Δ := Δ) x).size = 1 := rfl

private theorem size_drvWonE_aux (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (bE : E2EExpr Γ .bool) :
    (drvWonE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) qStart σE bE).size ≤
      σE.size + bE.size + ReductionDsl.bits qStart + 40 := by
  unfold drvWonE
  simp only [drvInsts, miGs, gsB, gsWin, boolEqE, eLet, eAny, eCaseOpt, size_v_aux, Expr.size]
  omega

private theorem size_isHonestUncorruptedPeerSomeE_aux (nId : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (principalsE : E2EExpr Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (pkE : E2EExpr Γ (PB 32)) :
    (isHonestUncorruptedPeerSomeE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      nId principalsE pkE).size ≤
      principalsE.size + pkE.size + ReductionDsl.bits nId + 50 := by
  unfold isHonestUncorruptedPeerSomeE
  simp only [peIkPk, peCorr, size_e2ePureOp, E2EPureOp.opSize, size_e2eCryptoOp,
    eLet, eCaseOpt, eFind, size_v_aux, Expr.size]
  omega

private theorem size_isSpkRevealedE_aux (nSpk : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (spkBundlesE : E2EExpr Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)))
    (pkE : E2EExpr Γ (PB 32)) :
    (isSpkRevealedE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      nSpk spkBundlesE pkE).size ≤
      spkBundlesE.size + pkE.size + ReductionDsl.bits nSpk + 50 := by
  unfold isSpkRevealedE
  simp only [beRev, beSpkPk, size_e2ePureOp, E2EPureOp.opSize, size_e2eCryptoOp,
    eLet, eAny, size_v_aux, Expr.size]
  omega

private theorem size_keyIndInitCorrClauseE_aux (nId nSpk : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (principalsE : E2EExpr Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (spkBundlesE : E2EExpr Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)))
    (sE : E2EExpr Γ (e2eInitiatorEntryTy ℓ S)) :
    (keyIndInitCorrClauseE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      nId nSpk principalsE spkBundlesE sE).size ≤
      principalsE.size + spkBundlesE.size + sE.size +
        ReductionDsl.bits nId + ReductionDsl.bits nSpk + 180 := by
  let Δ := (Ty.list (.prod .nat e2ePrincipalEntryTy)).prod
    ((Ty.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)).prod
      (e2eInitiatorEntryTy ℓ S)) :: Γ
  have h1 := size_isHonestUncorruptedPeerSomeE_aux (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nId (Γ := Δ)
    (.fst (.var .zero)) (iePeerIk (.snd (.snd (.var .zero))))
  have h2 := size_isSpkRevealedE_aux (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nSpk (Γ := Δ)
    (.fst (.snd (.var .zero))) (iePeerSpk (.snd (.snd (.var .zero))))
  simp only [iePeerIk, iePeerSpk, Expr.size, Nat.reduceAdd] at h1 h2
  unfold keyIndInitCorrClauseE
  dsimp only [v, Ext.wk]
  simp only [ieFresh, ieSpkHon, ieOpkHon, iePeerIk, iePeerSpk, orE,
    eLet, Expr.size, Nat.reduceAdd]
  omega

private theorem size_optPow8EqE_aux {Γ : List (Ty (e2eSig ℓ))}
    (aE bE : E2EExpr Γ (.opt (PB 32))) :
    (optPow8EqE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) aE bE).size ≤
      aE.size + bE.size + 40 := by
  unfold optPow8EqE
  simp only [isNoneE, size_e2ePureOp, E2EPureOp.opSize, size_e2eCryptoOp,
    eLet, eCaseOpt, size_v_aux, Expr.size]
  omega

private theorem size_keyIndPartnerE_aux {Γ : List (Ty (e2eSig ℓ))}
    (sE : E2EExpr Γ (e2eInitiatorEntryTy ℓ S))
    (rE : E2EExpr Γ (e2eRespEntryTy ℓ S)) :
    (keyIndPartnerE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) sE rE).size ≤
      sE.size + rE.size + 220 := by
  let Δ := (e2eInitiatorEntryTy ℓ S).prod (e2eRespEntryTy ℓ S) :: Γ
  have hopk := size_optPow8EqE_aux (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ)
    (iePeerOpk (.fst (.var .zero))) (reOpk (.snd (.var .zero)))
  simp only [iePeerOpk, reOpk, Expr.size, Nat.reduceAdd] at hopk
  unfold keyIndPartnerE
  dsimp only [v, Ext.wk]
  simp only [ieHdr, iePeerIk, iePeerSpk, iePeerOpk, iePeerPq,
    reHdr, reIk, reSpk, reOpk, rePq, hdrIkA, hdrEkA, hdrKemCt,
    size_e2ePureOp, E2EPureOp.opSize, size_e2eCryptoOp,
    eLet, Expr.size, Nat.reduceAdd]
  omega

private theorem size_isKeyIndInitStillFreshE_aux (nId nSpk nResp : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (principalsE : E2EExpr Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (spkBundlesE : E2EExpr Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)))
    (respE : E2EExpr Γ (.list (e2eRespEntryTy ℓ S)))
    (sE : E2EExpr Γ (e2eInitiatorEntryTy ℓ S)) :
    (isKeyIndInitStillFreshE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      nId nSpk nResp principalsE spkBundlesE respE sE).size ≤
      principalsE.size + spkBundlesE.size + respE.size + sE.size +
        ReductionDsl.bits nId + ReductionDsl.bits nSpk + ReductionDsl.bits nResp + 500 := by
  let Δ := (Ty.list (.prod .nat e2ePrincipalEntryTy)).prod
    ((Ty.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)).prod
      ((Ty.list (e2eRespEntryTy ℓ S)).prod
        (e2eInitiatorEntryTy ℓ S))) :: Γ
  have hc := size_keyIndInitCorrClauseE_aux (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nId nSpk (Γ := Δ)
    (.fst (.var .zero)) (.fst (.snd (.var .zero))) (.snd (.snd (.snd (.var .zero))))
  have hp := size_keyIndPartnerE_aux (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := e2eRespEntryTy ℓ S :: Δ)
    (.snd (.snd (.snd (.var (.succ .zero))))) (.var .zero)
  simp only [Expr.size, Nat.reduceAdd] at hc hp
  unfold isKeyIndInitStillFreshE
  dsimp only [v, Ext.wk]
  simp only [ieRev, reSendHon, reRev, orE, eLet, eAny, Expr.size, Nat.reduceAdd]
  omega

theorem size_testedInitSessionsFreshE (nInst nSend nId nSpk nRecv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : E2EExpr Γ (e2eKeyIndStateTy ℓ S)) :
    (testedInitSessionsFreshE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      nInst nSend nId nSpk nRecv stE).size ≤
      stE.size + ReductionDsl.bits nInst + ReductionDsl.bits nSend +
        ReductionDsl.bits nId + ReductionDsl.bits nSpk + ReductionDsl.bits nRecv + 600 := by
  let Δ0 := e2eKeyIndStateTy ℓ S :: Γ
  let Δs := e2eInitiatorEntryTy ℓ S :: Δ0
  have hs := size_isKeyIndInitStillFreshE_aux (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nId nSpk nRecv (Γ := Δs)
    (stPrin (.var (.succ .zero))) (stSpk (.var (.succ .zero)))
    (stResp (.var (.succ .zero))) (.var .zero)
  simp only [stPrin, stSpk, stResp, Expr.size, Nat.reduceAdd] at hs
  unfold testedInitSessionsFreshE
  dsimp only [v, Ext.wk]
  simp only [stSess, stPrin, stSpk, stResp, ieTested,
    eLet, eAny, Expr.v0, Expr.v1, Expr.size, Nat.reduceAdd]
  omega

theorem size_finishPrefixClampedC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (b'E flipE : E2EExpr Γ .bool) :
    (finishPrefixClampedC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I₀ qStart nAdv σE b'E flipE).size ≤
      σE.size + b'E.size + flipE.size + finishPrefixClampedSize S qStart nAdv := by
  let Δ0 := (e2eDrvStateTy S ℓ).prod (.prod .bool .bool) :: Γ
  let nId := min nAdv S.N_id
  let nSpk := min nAdv S.N_spk_tot
  let nSend := min nAdv S.N_send_tot
  let nRecv := min nAdv S.N_recv_tot
  let nInst := min qStart nSend
  have hf := size_testedInitSessionsFreshE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ0) nInst nSend nId nSpk nRecv (drvSt (.fst .v0))
  have hwT := size_drvWonE_aux (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ0) nInst (.fst .v0) (.bool true)
  have hwF := size_drvWonE_aux (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ0) nInst (.fst .v0) (.bool false)
  simp only [drvSt, Expr.v0, Expr.size, Nat.reduceAdd] at hf hwT hwF
  dsimp only [nId, nSpk, nSend, nRecv, nInst] at hf hwT hwF
  unfold finishPrefixClampedC finishPrefixClampedSize
  dsimp only
  simp only [drvPaused, drvSt, boolXorE, Expr.v0, Expr.v1, Comp.size, Expr.size, Nat.reduceAdd]
  omega

theorem cost_finishPrefixClampedC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (b'E flipE : E2EExpr Γ .bool) :
    (finishPrefixClampedC I₀ qStart nAdv σE b'E flipE).cost ≤
      σE.cost + b'E.cost + flipE.cost + finishPrefixClampedCost S qStart nAdv := by
  let Δ0 := (e2eDrvStateTy S ℓ).prod (.prod .bool .bool) :: Γ
  let nId := min nAdv S.N_id
  let nSpk := min nAdv S.N_spk_tot
  let nSend := min nAdv S.N_send_tot
  let nRecv := min nAdv S.N_recv_tot
  let nInst := min qStart nSend
  have hf := cost_testedInitSessionsFreshE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ0) nInst nSend nId nSpk nRecv (drvSt (.fst .v0))
  have hwT := cost_drvWonE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ0) nInst (.fst .v0) (.bool true)
  have hwF := cost_drvWonE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ0) nInst (.fst .v0) (.bool false)
  have hsCost : (stepAIface ℓ I₀).smp.sCost UniformSamplerTag.bool = 1 := rfl
  simp only [drvSt, Expr.v0, Expr.cost, Nat.reduceAdd] at hf hwT hwF
  dsimp only [nId, nSpk, nSend, nRecv, nInst] at hf hwT hwF
  unfold finishPrefixClampedC finishPrefixClampedCost
  dsimp only
  simp only [drvPaused, drvSt, cost_boolXorE, Expr.v0, Expr.v1, Comp.cost, Expr.cost,
    hsCost, Nat.reduceAdd]
  omega

theorem eval_finishPrefixClampedC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (b'E flipE : E2EExpr Γ .bool) (ρ : Env Γ)
    (σ : BHE2EDrvState S ℓ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (hσ : σE.eval ρ = e2eDrvStateEnc σ)
    (hInsts : σ.insts.length ≤ min qStart (min nAdv S.N_send_tot))
    (hTested : (σ.st.sessions.filter (·.tested)).length ≤ min qStart (min nAdv S.N_send_tot))
    (hInit : σ.st.sessions.length ≤ min nAdv S.N_send_tot)
    (hResp : σ.st.respSessions.length ≤ min nAdv S.N_recv_tot)
    (hId : σ.st.principals.length ≤ min nAdv S.N_id)
    (hSpk : σ.st.spkBundles.length ≤ min nAdv S.N_spk_tot)
    (hRespUntested : ∀ r ∈ σ.st.respSessions, r.tested = false) :
    (finishPrefixClampedC I₀ qStart nAdv σE b'E flipE).eval ρ =
      (stepAIface ℓ I₀).liftP
        (bhShallowFinishPrefix P σ (b'E.eval ρ) (flipE.eval ρ)) := by
  let nId := min nAdv S.N_id
  let nSpk := min nAdv S.N_spk_tot
  let nSend := min nAdv S.N_send_tot
  let nRecv := min nAdv S.N_recv_tot
  let nInst := min qStart nSend
  set ρ0 : Env ((e2eDrvStateTy S ℓ).prod (.prod .bool .bool) :: Γ) :=
    .cons (e2eDrvStateEnc σ, (b'E.eval ρ, flipE.eval ρ)) ρ with hρ0
  have hpair0 :
      (Expr.pair σE (.pair b'E flipE)).eval ρ =
        (e2eDrvStateEnc σ, (b'E.eval ρ, flipE.eval ρ)) := by
    simp only [Expr.eval, hσ]
  have hσ0 : (Expr.fst (O := e2eOps ℓ P C K decT encT) Expr.v0).eval ρ0 =
      e2eDrvStateEnc σ := rfl
  have hPaused0 :
      (Expr.not (O := e2eOps ℓ P C K decT encT) (drvPaused (.fst Expr.v0))).eval ρ0 =
        !σ.paused := rfl
  have hSt0 : (drvSt (O := e2eOps ℓ P C K decT encT) (.fst Expr.v0)).eval ρ0 =
      e2eKeyIndStateToVal σ.st := rfl
  have hb'0 : (Expr.fst (O := e2eOps ℓ P C K decT encT) (.snd Expr.v0)).eval ρ0 =
      b'E.eval ρ := rfl
  have hflip0 : (Expr.snd (O := e2eOps ℓ P C K decT encT) (.snd Expr.v0)).eval ρ0 =
      flipE.eval ρ := rfl
  have hsamp : (stepAIface ℓ I₀).smp.samp UniformSamplerTag.bool () = ($ᵗ Bool) := rfl
  unfold finishPrefixClampedC
  dsimp only
  rw [comp_eval_bind_ret, hpair0, ← hρ0, comp_eval_ite_cond, hPaused0]
  cases hp : σ.paused
  · simp only [bhShallowFinishPrefix, hp, Bool.not_false, cond, ↓reduceIte, Comp.eval, Expr.eval,
      liftP_pure]
  · simp only [Bool.not_true, cond]
    rw [comp_eval_ite_cond]
    have hnotFresh :
        (Expr.not (O := e2eOps ℓ P C K decT encT)
          (testedInitSessionsFreshE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
            nInst nSend nId nSpk nRecv (drvSt (.fst .v0)))).eval
          ρ0 = !(allTestedSessionsFresh P σ.st) := by
      simp only [Expr.eval,
        eval_testedInitSessionsFreshE nInst nSend nId nSpk nRecv hP _ ρ0 hSt0 hTested hInit hResp hId hSpk hRespUntested]
    rw [hnotFresh]
    cases hf : allTestedSessionsFresh P σ.st
    · simp only [bhShallowFinishPrefix, hp, hf, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        cond, ↓reduceIte, Comp.eval, Expr.eval, hsamp, liftP_bind, liftP_pure, eval_boolXorE]
      congr 1
    · simp only [bhShallowFinishPrefix, hp, hf, Bool.not_true, Bool.false_eq_true, cond, ↓reduceIte,
        Comp.eval, liftP_pure, eval_boolXorE, hflip0]
      rw [expr_eval_ite_cond, expr_eval_ite_cond,
          eval_drvWonE nInst _ _ ρ0 hσ0 hInsts,
          eval_drvWonE nInst _ _ ρ0 hσ0 hInsts, hb'0]
      have hbt : (Expr.bool (O := e2eOps ℓ P C K decT encT) true).eval ρ0 = true := rfl
      have hbf : (Expr.bool (O := e2eOps ℓ P C K decT encT) false).eval ρ0 = false := rfl
      rw [hbt, hbf]
      cases bhE2EDrvWon σ true <;> cases bhE2EDrvWon σ false <;> rfl

end FreshnessAndWin

end Computational.Proofs.E2E.Dsl.FreshnessSim
