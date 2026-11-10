/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Specifications.Game.ModelIface
public import Computational.Proofs.SpecLemmas.Game.BhShallowHelpers -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.BinaryHarnessCostedRedsV1 -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.SizeBudgetBridge

/-!
# Halted Multi-Session Handshake Reduction

Constructs the halted one-stage `CostedReduction` `kindRedHalted` over `atomicE2EOps` and
`e2eKeyIndTargetIface`, proving `GRedBounded` and per-instance `SignalPqxdh.QueryBounded`
alongside the shallow halted reference reduction `bhKindRedWithHalted`.
-/

public section

set_option autoImplicit false

open scoped ENNReal BigOperators

namespace Computational.Proofs.E2E.Dsl.KindRedHalted

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Ops Iface GameCodec Env Expr Comp CostedReduction bits
  reductionSizeBudget OpsSizeHonest SampSizeHonest atomicSig atomicE2EOps atomicE2EOps_sizeHonest
  atomicBaseSamplers_sizeHonest e2eKeyIndTargetIface E2EKeyIndTag FinT BV256 UniformSamplerTag
  AtomicBaseUnif keyIndQT keyIndQenc keyIndQdec keyIndRT keyIndRenc keyIndRdec sidT sidV sidOfV
  smQT smQenc smRT smRdec recvResultEnc recvResultDec GhostStT
  liftP_queryBound simulateQ_run_StateT_of_step_le)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (GameState)
open CryptoGames.LibsignalSession (Crypto PublicKey GhostState)
open CryptoVerification.LibsignalSession (GRedBounded)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes BHE2EDrvState BHE2ESmResp BHTargetQuery BHTargetResp
  BhShallowRed bhShallowImplOfHandle bhTargetGameSpec e2eTargetGameCodec bhTargetQenc bhTargetRdec
  bhUnpackSmResp bhLiftP bhDrvKiQueryOk bhNoOpkRespPromoted bhE2EMirror bhE2EGuard
  bhE2EFinishStartSpk bhE2EDrvWon bhKeySOf SampledSessionKey keyIndReductionBudget
  pqxdhKeyIndExpForHandshake bhClassifyTarget bhClassifyTargetOnly)
open CryptoVerification.E2E.Costed (gRedBounded_of_bounds)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (size_le_budget_of_log_cost)

/-! ## Shallow halted reference reduction -/

section ShallowHalted

variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {SessH : Type}

@[expose] def bhE2EFinishStartSpkTracked
    (initTrack : SampledSessionKey → SessH)
    (C : Crypto) (K : MlKem) (bMode? : Option Bool)
    (σH : BHE2EDrvState S ℓ × List SessH) (sid : SignalPqxdh.SessionId S)
    (kr1 kr2 : SignalPqxdh.KeyIndResponse) (ac : BitVec 256) :
    Option ℕ × (BHE2EDrvState S ℓ × List SessH) :=
  let (idx?, σ') := bhE2EFinishStartSpk C K bMode? σH.1 sid kr1 kr2 ac
  let tracks' := match idx?, kr1 with
    | some _, .drKeyResp dk => σH.2 ++ [initTrack (bhKeySOf dk ac)]
    | _, _ => σH.2
  (idx?, (σ', tracks'))

@[expose] def bhKindHandleWithHalted
    (initTrack : SampledSessionKey → SessH)
    (stepLocalSmH : BHE2EDrvState S ℓ × List SessH → ℕ →
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain →
      ProbComp (BHE2ESmResp ℓ × (BHE2EDrvState S ℓ × List SessH)))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (σH : BHE2EDrvState S ℓ × List SessH) (q : BHTargetQuery S ℓ (BitVec 512)) :
    OracleComp (unifSpec + SignalPqxdh.keyIndSpec S)
      (BHTargetResp ℓ × (BHE2EDrvState S ℓ × List SessH)) :=
  match q with
  | .inl (.inl kq) =>
    if bhDrvKiQueryOk P σH.1.toModelDriverBase kq &&
        !(match kq with | .corruptIK u => bhNoOpkRespPromoted σH.1.instMeta u | _ => false) then do
      let kr ← (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
        OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _)
      return (.inl (.inl kr), (bhE2EMirror σH.1 kq kr, σH.2))
    else
      pure (.inl (.inl .noneResp), σH)
  | .inl (.inr sid) =>
    match (bhE2EGuard σH.1 sid).map (fun (_, _, uj) => uj) with
    | none => pure (.inl (.inr none), σH)
    | some (u, j) => do
      let ts ← (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr (.testSession sid))) :
        OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _)
      let sk ← (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr (.revealSpkSk u j))) :
        OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _)
      let bv ← bhLiftP (G := SignalPqxdh.keyIndSpec S) ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let fin := bhE2EFinishStartSpkTracked initTrack C K (some σH.1.b) σH sid ts sk bv
      return (.inl (.inr fin.1), fin.2)
  | .inr (i, sq) => do
    let res ← bhLiftP (G := SignalPqxdh.keyIndSpec S) (stepLocalSmH σH i sq)
    return (.inr res.1, res.2)

/-- Shallow one-stage halted `KeyInd` reference reduction. -/
@[expose] def bhKindRedWithHalted
    (initTrack : SampledSessionKey → SessH)
    (stepLocalSmH : BHE2EDrvState S ℓ × List SessH → ℕ →
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain →
      ProbComp (BHE2ESmResp ℓ × (BHE2EDrvState S ℓ × List SessH)))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) :
    BhShallowRed (bhTargetGameSpec S ℓ (BitVec 512))
      (unifSpec + SignalPqxdh.keyIndSpec S)
      Unit Bool Unit Bool (BHE2EDrvState S ℓ × List SessH) where
  init _ := do
    let drvH ← bhLiftP (G := SignalPqxdh.keyIndSpec S)
      (do let b ← ($ᵗ Bool : ProbComp Bool)
          return (({ b := b } : BHE2EDrvState S ℓ), ([] : List SessH)))
    return ((), drvH)
  impl := bhShallowImplOfHandle bhTargetQenc bhTargetRdec
    (bhKindHandleWithHalted initTrack stepLocalSmH P C K)
  finish drvH aOut := pure (aOut == drvH.1.b || bhE2EDrvWon drvH.1 drvH.1.b)

end ShallowHalted

/-! ## Atomic `ReductionDsl` construction of `kindRedHalted` -/

section AtomicProgram

@[expose] def mkAtomicTestSessionE {ℓ : ℕ} {Pt : Type} {S : SignalPqxdh.Setup}
    {O : Ops (atomicSig ℓ Pt)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (sidE : Expr O Γ (sidT (ℓ := ℓ) (Pt := Pt) S)) :
    Expr O Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S) :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl sidE))))))))

@[expose] def mkAtomicRevealSpkSkE {ℓ : ℕ} {Pt : Type} {S : SignalPqxdh.Setup}
    {O : Ops (atomicSig ℓ Pt)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (ujE : Expr O Γ (.prod (FinT (ℓ := ℓ) (Pt := Pt) S.N_id) (FinT (ℓ := ℓ) (Pt := Pt) S.N_recv))) :
    Expr O Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S) :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ujE))))))))))))

@[simp] theorem eval_mkAtomicTestSessionE {ℓ : ℕ} {Pt : Type} {S : SignalPqxdh.Setup}
    {O : Ops (atomicSig ℓ Pt)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (sidE : Expr O Γ (sidT (ℓ := ℓ) (Pt := Pt) S)) (ρ : Env Γ) :
    (mkAtomicTestSessionE sidE).eval ρ =
      keyIndQenc (.testSession (sidOfV (sidE.eval ρ))) := by
  cases h : sidE.eval ρ with
  | inl ui => rcases ui with ⟨u, i⟩; simp [mkAtomicTestSessionE, Expr.eval, h, sidOfV, keyIndQenc, sidV]
  | inr r1 => cases r1 with
    | inl ui => rcases ui with ⟨u, i⟩; simp [mkAtomicTestSessionE, Expr.eval, h, sidOfV, keyIndQenc, sidV]
    | inr r2 => cases r2 with
      | inl kjo => rcases kjo with ⟨k, j, o⟩; simp [mkAtomicTestSessionE, Expr.eval, h, sidOfV, keyIndQenc, sidV]
      | inr kjl => rcases kjl with ⟨k, j, l⟩; simp [mkAtomicTestSessionE, Expr.eval, h, sidOfV, keyIndQenc, sidV]

@[simp] theorem eval_mkAtomicRevealSpkSkE {ℓ : ℕ} {Pt : Type} {S : SignalPqxdh.Setup}
    {O : Ops (atomicSig ℓ Pt)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (ujE : Expr O Γ (.prod (FinT (ℓ := ℓ) (Pt := Pt) S.N_id) (FinT (ℓ := ℓ) (Pt := Pt) S.N_recv)))
    (ρ : Env Γ) :
    (mkAtomicRevealSpkSkE ujE).eval ρ =
      keyIndQenc (.revealSpkSk (ujE.eval ρ).1 (ujE.eval ρ).2) := by
  rcases h : ujE.eval ρ with ⟨u, j⟩
  simp [mkAtomicRevealSpkSkE, Expr.eval, h, keyIndQenc]

/-- Interface of atomic `ReductionDsl` subprograms over `atomicE2EOps` and `e2eKeyIndTargetIface` for `kindRedHalted`. -/
structure HaltedKindSubprograms (S : SignalPqxdh.Setup) {Pt : Type} (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (SessH : Type) where
  drvTy : Ty (atomicSig ℓ Pt)
  sessHTy : Ty (atomicSig ℓ Pt)
  drvEnc : BHE2EDrvState S ℓ → drvTy.denote
  sessHEnc : SessH → sessHTy.denote

  initKindC : ∀ {Γ},
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt) Γ drvTy
  initKindCost : ℕ
  initKindSize : ℕ
  initKindC_cost : ∀ {Γ}, (initKindC (Γ := Γ)).cost ≤ initKindCost
  initKindC_size : ∀ {Γ}, (initKindC (Γ := Γ)).size ≤ initKindSize
  initKindC_queries : ∀ {Γ} (w : (e2eKeyIndTargetIface S ℓ Pt).Tag → ℕ),
    (initKindC (Γ := Γ)).queries w (fun _ => 0) = 0

  drvBitE : ∀ {Γ}, Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool
  drvBitCost : ℕ
  drvBitSize : ℕ
  drvBitE_cost : ∀ {Γ} (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy),
    (drvBitE σE).cost ≤ σE.cost + drvBitCost
  drvBitE_size : ∀ {Γ} (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy),
    (drvBitE σE).size ≤ σE.size + drvBitSize
  drvBitE_eval : ∀ {Γ} (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy)
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ),
    σE.eval ρ = drvEnc σ → (drvBitE σE).eval ρ = σ.b

  kiQueryOkE : SignalPqxdh.QueryBudget → ℕ → ∀ {Γ},
    Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S) →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool
  kiQueryOkCost : SignalPqxdh.QueryBudget → ℕ → ℕ
  kiQueryOkSize : SignalPqxdh.QueryBudget → ℕ → ℕ
  kiQueryOkE_cost : ∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy)
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S)),
    (kiQueryOkE b qStart σE kqE).cost ≤ σE.cost + kqE.cost + kiQueryOkCost b qStart
  kiQueryOkE_size : ∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy)
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S)),
    (kiQueryOkE b qStart σE kqE).size ≤ σE.size + kqE.size + kiQueryOkSize b qStart

  mirrorE : ∀ {Γ},
    Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S) →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndRT (ℓ := ℓ) (Pt := Pt)) →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy
  mirrorCost : ℕ
  mirrorSize : ℕ
  mirrorE_cost : ∀ {Γ}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy)
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (krE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndRT (ℓ := ℓ) (Pt := Pt))),
    (mirrorE σE kqE krE).cost ≤ σE.cost + kqE.cost + krE.cost + mirrorCost
  mirrorE_size : ∀ {Γ}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy)
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (krE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndRT (ℓ := ℓ) (Pt := Pt))),
    (mirrorE σE kqE krE).size ≤ σE.size + kqE.size + krE.size + mirrorSize

  prepStartSpkE : SignalPqxdh.QueryBudget → ℕ → ∀ {Γ},
    Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S) →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.opt (.prod (FinT (ℓ := ℓ) (Pt := Pt) S.N_id) (FinT (ℓ := ℓ) (Pt := Pt) S.N_recv)))
  prepStartSpkCost : SignalPqxdh.QueryBudget → ℕ → ℕ
  prepStartSpkSize : SignalPqxdh.QueryBudget → ℕ → ℕ
  prepStartSpkE_cost : ∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy)
    (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S)),
    (prepStartSpkE b qStart σE sidE).cost ≤ σE.cost + sidE.cost + prepStartSpkCost b qStart
  prepStartSpkE_size : ∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy)
    (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S)),
    (prepStartSpkE b qStart σE sidE).size ≤ σE.size + sidE.size + prepStartSpkSize b qStart

  finishStartSpkHaltedC : SignalPqxdh.QueryBudget → ℕ → ∀ {Γ},
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt .bool) →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod drvTy (.list sessHTy)) →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S) →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndRT (ℓ := ℓ) (Pt := Pt)) →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndRT (ℓ := ℓ) (Pt := Pt)) →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (BV256 (ℓ := ℓ) (Pt := Pt)) →
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt) Γ
      (.prod (.opt .nat) (.prod drvTy (.list sessHTy)))
  finishStartSpkHaltedCost : SignalPqxdh.QueryBudget → ℕ → ℕ
  finishStartSpkHaltedSize : SignalPqxdh.QueryBudget → ℕ → ℕ
  finishStartSpkHaltedC_cost : ∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ}
    (bmE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt .bool))
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod drvTy (.list sessHTy)))
    (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
    (kr1E kr2E : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndRT (ℓ := ℓ) (Pt := Pt)))
    (acE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (BV256 (ℓ := ℓ) (Pt := Pt))),
    (finishStartSpkHaltedC b qStart bmE σHE sidE kr1E kr2E acE).cost ≤
      bmE.cost + σHE.cost + sidE.cost + kr1E.cost + kr2E.cost + acE.cost +
        finishStartSpkHaltedCost b qStart
  finishStartSpkHaltedC_size : ∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ}
    (bmE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt .bool))
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod drvTy (.list sessHTy)))
    (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
    (kr1E kr2E : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndRT (ℓ := ℓ) (Pt := Pt)))
    (acE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (BV256 (ℓ := ℓ) (Pt := Pt))),
    (finishStartSpkHaltedC b qStart bmE σHE sidE kr1E kr2E acE).size ≤
      bmE.size + σHE.size + sidE.size + kr1E.size + kr2E.size + acE.size +
        finishStartSpkHaltedSize b qStart
  finishStartSpkHaltedC_queries : ∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ}
    (bmE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt .bool))
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod drvTy (.list sessHTy)))
    (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
    (kr1E kr2E : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndRT (ℓ := ℓ) (Pt := Pt)))
    (acE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (BV256 (ℓ := ℓ) (Pt := Pt)))
    (w : (e2eKeyIndTargetIface S ℓ Pt).Tag → ℕ),
    (finishStartSpkHaltedC b qStart bmE σHE sidE kr1E kr2E acE).queries w (fun _ => 0) = 0

  haltedStepLocalSmC : SignalPqxdh.QueryBudget → ℕ → ℕ → ℕ → ∀ {Γ},
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod drvTy (.list sessHTy)) →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt)) →
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt) Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (.prod drvTy (.list sessHTy)))
  haltedStepLocalSmCost : SignalPqxdh.QueryBudget → ℕ → ℕ → ℕ → ℕ
  haltedStepLocalSmSize : SignalPqxdh.QueryBudget → ℕ → ℕ → ℕ → ℕ
  haltedStepLocalSmC_cost : ∀ (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) {Γ}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod drvTy (.list sessHTy)))
    (idxE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt))),
    (haltedStepLocalSmC b qStart qDR qep σHE idxE sqE).cost ≤
      σHE.cost + idxE.cost + sqE.cost + haltedStepLocalSmCost b qStart qDR qep
  haltedStepLocalSmC_size : ∀ (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) {Γ}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod drvTy (.list sessHTy)))
    (idxE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt))),
    (haltedStepLocalSmC b qStart qDR qep σHE idxE sqE).size ≤
      σHE.size + idxE.size + sqE.size + haltedStepLocalSmSize b qStart qDR qep
  haltedStepLocalSmC_queries : ∀ (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) {Γ}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod drvTy (.list sessHTy)))
    (idxE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt)))
    (w : (e2eKeyIndTargetIface S ℓ Pt).Tag → ℕ),
    (haltedStepLocalSmC b qStart qDR qep σHE idxE sqE).queries w (fun _ => 0) = 0

  finishKindE : ℕ → ∀ {Γ},
    Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool
  finishKindCost : ℕ → ℕ
  finishKindSize : ℕ → ℕ
  finishKindE_cost : ∀ (qStart : ℕ) {Γ}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy)
    (bOutE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool),
    (finishKindE qStart σE bOutE).cost ≤ σE.cost + bOutE.cost + finishKindCost qStart
  finishKindE_size : ∀ (qStart : ℕ) {Γ}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy)
    (bOutE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool),
    (finishKindE qStart σE bOutE).size ≤ σE.size + bOutE.size + finishKindSize qStart

variable {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
  {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}

abbrev drvKindHaltedTy (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH) :
    Ty (atomicSig ℓ Pt) :=
  .prod subs.drvTy (.list subs.sessHTy)

@[expose] def drvKindHaltedEnc (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (σH : BHE2EDrvState S ℓ × List SessH) : (drvKindHaltedTy subs).denote :=
  (subs.drvEnc σH.1, σH.2.map subs.sessHEnc)

@[expose] def kindStartStepHaltedC
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvKindHaltedTy subs))
    (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S)) :
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt) Γ
      (.prod (.opt .nat) (drvKindHaltedTy subs)) :=
  .bind (.ret (.pair σHE sidE))
    (.caseOpt
      (subs.prepStartSpkE b qStart (.fst (.fst .v0)) (.snd .v0))
      (.ret (.pair .none (.fst .v0)))
      (.bind
        (.query E2EKeyIndTag.keyInd (mkAtomicTestSessionE (.snd .v1)))
        (.bind
          (.query E2EKeyIndTag.keyInd (mkAtomicRevealSpkSkE .v1))
          (.bind
            (.sample (UniformSamplerTag.base AtomicBaseUnif.bv256) .unit)
            (subs.finishStartSpkHaltedC b qStart
              (.some (subs.drvBitE (.fst (.fst .v4))))
              (.fst .v4)
              (.snd .v4)
              .v2
              .v1
              .v0)))))

@[expose] def kindHandleHalted
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) :
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt)
      [drvKindHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]
      (.prod (e2eTargetGameCodec S ℓ Pt).R (drvKindHaltedTy subs)) :=
  .caseSum .v1
    (.caseSum .v0
      (.ite (subs.kiQueryOkE b qStart (.fst .v2) .v0)
        (.bind (.query E2EKeyIndTag.keyInd .v0)
          (.ret (.pair (.inl (.inl .v0))
            (.pair (subs.mirrorE (.fst .v3) .v1 .v0) (.snd .v3)))))
        (.ret (.pair (.inl (.inl (.inl .unit))) .v2)))
      (.bind (kindStartStepHaltedC subs b qStart .v2 .v0)
        (.ret (.pair (.inl (.inr (.fst .v0))) (.snd .v0)))))
    (.bind
      (subs.haltedStepLocalSmC b qStart qDR qep .v1 (.fst .v0) (.snd .v0))
      (.ret (.pair (.inr (.fst .v0)) (.snd .v0))))

/-- Halted one-stage handshake reduction over `atomicE2EOps` and `e2eKeyIndTargetIface`. -/
@[expose, reducible] def kindRedHalted
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) :
    CostedReduction (atomicE2EOps ℓ P C K decT encT)
      (e2eKeyIndTargetIface S ℓ Pt)
      (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ Pt)
      .unit .unit .bool .bool where
  σ := drvKindHaltedTy subs
  init := .bind subs.initKindC (.ret (.pair .unit (.pair .v0 .nil)))
  handle := kindHandleHalted subs b qStart qDR qep
  finish := .ret (subs.finishKindE qStart (.fst .v0) .v1)

/-! ### Static query bounds -/

theorem kindStartStepHaltedC_queries
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvKindHaltedTy subs))
    (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S)) :
    (kindStartStepHaltedC subs b qStart σHE sidE).queries (fun _ => 1) (fun _ => 0) = 2 := by
  have hfin := subs.finishStartSpkHaltedC_queries b qStart
    (Γ := (e2eKeyIndTargetIface S ℓ Pt).smp.sTy (UniformSamplerTag.base AtomicBaseUnif.bv256) ::
      keyIndRT (ℓ := ℓ) (Pt := Pt) :: keyIndRT (ℓ := ℓ) (Pt := Pt) ::
      Ty.prod (FinT (ℓ := ℓ) (Pt := Pt) S.N_id) (FinT (ℓ := ℓ) (Pt := Pt) S.N_recv) ::
      Ty.prod (drvKindHaltedTy subs) (sidT (ℓ := ℓ) (Pt := Pt) S) :: Γ)
    (.some (subs.drvBitE (.fst (.fst .v4)))) (.fst .v4) (.snd .v4) .v2 .v1 .v0 (fun _ => 1)
  simp only [kindStartStepHaltedC, Comp.queries, Nat.zero_add]
  exact congrArg (fun x => max 0 (1 + (1 + x))) hfin

theorem kindHandleHalted_queries_le
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) :
    (kindHandleHalted subs b qStart qDR qep).queries (fun _ => 1) (fun _ => 0) ≤ 2 := by
  have hst := kindStartStepHaltedC_queries subs b qStart
    (Γ := [sidT (ℓ := ℓ) (Pt := Pt) S,
      Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
      drvKindHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]) .v2 .v0
  have hsm := subs.haltedStepLocalSmC_queries b qStart qDR qep
    (Γ := [Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)),
      drvKindHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]) .v1 (.fst .v0) (.snd .v0) (fun _ => 1)
  simp only [kindHandleHalted, Comp.queries]
  rw [hst, hsm]
  omega

theorem kindRedHalted_totalQueries_le
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep qTot : ℕ) :
    (kindRedHalted subs b qStart qDR qep).totalQueries (fun _ => 1) (fun _ => 0) qTot ≤
      2 * qTot := by
  have hinit := subs.initKindC_queries (Γ := [.unit]) (fun _ => 1)
  have hhand := kindHandleHalted_queries_le subs b qStart qDR qep
  dsimp only [CostedReduction.totalQueries, kindRedHalted, Comp.queries]
  rw [hinit]
  simp only [Nat.zero_add, Nat.add_zero]
  exact (Nat.mul_le_mul_left qTot hhand).trans (by omega)

/-! ### Cost, size, and `GRedBounded` -/

@[expose] def haltedKindEndpointCost
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH) (qStart : ℕ) : ℕ :=
  subs.initKindCost + subs.finishKindCost qStart + 24

@[expose] def haltedKindStepCost
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) : ℕ :=
  max (subs.kiQueryOkCost b qStart + subs.mirrorCost)
      (subs.prepStartSpkCost b qStart + subs.drvBitCost + subs.finishStartSpkHaltedCost b qStart) +
    subs.haltedStepLocalSmCost b qStart qDR qep + 480

theorem kindStartStepHaltedC_cost
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvKindHaltedTy subs))
    (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S)) :
    (kindStartStepHaltedC subs b qStart σHE sidE).cost ≤
      σHE.cost + sidE.cost +
        subs.prepStartSpkCost b qStart + subs.drvBitCost +
        subs.finishStartSpkHaltedCost b qStart + 380 := by
  let Γ1 := Ty.prod (drvKindHaltedTy subs) (sidT (ℓ := ℓ) (Pt := Pt) S) :: Γ
  let Γ2 := Ty.prod (FinT (ℓ := ℓ) (Pt := Pt) S.N_id) (FinT (ℓ := ℓ) (Pt := Pt) S.N_recv) :: Γ1
  let Γ3 := keyIndRT (ℓ := ℓ) (Pt := Pt) :: Γ2
  let Γ4 := keyIndRT (ℓ := ℓ) (Pt := Pt) :: Γ3
  let Γ5 := (e2eKeyIndTargetIface S ℓ Pt).smp.sTy
    (UniformSamplerTag.base AtomicBaseUnif.bv256) :: Γ4
  have hprep := subs.prepStartSpkE_cost b qStart (Γ := Γ1) (.fst (.fst .v0)) (.snd .v0)
  have hts : (mkAtomicTestSessionE (O := atomicE2EOps ℓ P C K decT encT) (Γ := Γ2) (.snd .v1)).cost =
      11 := by
    simp [mkAtomicTestSessionE, Expr.cost, Expr.v1]
  have hrv : (mkAtomicRevealSpkSkE (O := atomicE2EOps ℓ P C K decT encT) (Γ := Γ3) .v1).cost =
      14 := by
    simp [mkAtomicRevealSpkSkE, Expr.cost, Expr.v1]
  have hbit := subs.drvBitE_cost (Γ := Γ5) (.fst (.fst .v4))
  have hfin := subs.finishStartSpkHaltedC_cost b qStart (Γ := Γ5)
    (.some (subs.drvBitE (.fst (.fst .v4)))) (.fst .v4) (.snd .v4) .v2 .v1 .v0
  dsimp only [kindStartStepHaltedC, Comp.cost, AtomicBaseUnif.cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v4] at hprep hts hrv hbit hfin ⊢
  omega

theorem kindHandleHalted_cost_le
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) :
    (kindHandleHalted subs b qStart qDR qep).cost + 64 ≤
      haltedKindStepCost subs b qStart qDR qep := by
  let Γ_ki : List (Ty (atomicSig ℓ Pt)) :=
    [keyIndQT (ℓ := ℓ) (Pt := Pt) S,
      Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
      drvKindHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]
  let Γ_kr : List (Ty (atomicSig ℓ Pt)) := keyIndRT (ℓ := ℓ) (Pt := Pt) :: Γ_ki
  let Γ_ctl : List (Ty (atomicSig ℓ Pt)) :=
    [sidT (ℓ := ℓ) (Pt := Pt) S,
      Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
      drvKindHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]
  let Γ_sm : List (Ty (atomicSig ℓ Pt)) :=
    [Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)), drvKindHaltedTy subs,
      (e2eTargetGameCodec S ℓ Pt).Q]
  have hok := subs.kiQueryOkE_cost b qStart (Γ := Γ_ki) (.fst .v2) .v0
  have hmir := subs.mirrorE_cost (Γ := Γ_kr) (.fst .v3) .v1 .v0
  have hst := kindStartStepHaltedC_cost subs b qStart (Γ := Γ_ctl) .v2 .v0
  have hsm := subs.haltedStepLocalSmC_cost b qStart qDR qep (Γ := Γ_sm) .v1 (.fst .v0) (.snd .v0)
  dsimp only [kindHandleHalted, haltedKindStepCost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hok hmir hst hsm ⊢
  omega

theorem kindRedHalted_totalCost_le_leaf
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep qTot : ℕ) :
    (kindRedHalted subs b qStart qDR qep).totalCost qTot ≤
      haltedKindEndpointCost subs qStart + qTot * haltedKindStepCost subs b qStart qDR qep := by
  have hinit := subs.initKindC_cost (Γ := [.unit])
  have hfin := subs.finishKindE_cost qStart (Γ := [drvKindHaltedTy subs, .bool]) (.fst .v0) .v1
  have hhand := kindHandleHalted_cost_le subs b qStart qDR qep
  have hcc : (e2eTargetGameCodec S ℓ Pt).codecCost ≤ 64 := by
    dsimp [e2eTargetGameCodec, _root_.ReductionDsl.e2eGameCodec]; omega
  have hstep : max 1 ((kindHandleHalted subs b qStart qDR qep).cost +
      (e2eTargetGameCodec S ℓ Pt).codecCost) ≤
      haltedKindStepCost subs b qStart qDR qep := by
    have hpos : 1 ≤ haltedKindStepCost subs b qStart qDR qep := by
      unfold haltedKindStepCost; omega
    omega
  have hmul : qTot * max 1 ((kindHandleHalted subs b qStart qDR qep).cost +
      (e2eTargetGameCodec S ℓ Pt).codecCost) ≤
      qTot * haltedKindStepCost subs b qStart qDR qep :=
    Nat.mul_le_mul_left qTot hstep
  dsimp only [CostedReduction.totalCost, kindRedHalted, haltedKindEndpointCost,
    e2eKeyIndTargetIface, e2eTargetGameCodec, _root_.ReductionDsl.e2eGameCodec,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1] at hinit hfin hmul ⊢
  omega

@[expose] def haltedKindSizeBound
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) : ℕ :=
  subs.initKindSize +
    subs.finishKindSize qStart +
    subs.kiQueryOkSize b qStart +
    subs.mirrorSize +
    subs.prepStartSpkSize b qStart +
    subs.drvBitSize +
    subs.finishStartSpkHaltedSize b qStart +
    subs.haltedStepLocalSmSize b qStart qDR qep +
    160

theorem kindStartStepHaltedC_size
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvKindHaltedTy subs))
    (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S)) :
    (kindStartStepHaltedC subs b qStart σHE sidE).size ≤
      σHE.size + sidE.size +
        subs.prepStartSpkSize b qStart + subs.drvBitSize +
        subs.finishStartSpkHaltedSize b qStart + 80 := by
  let Γ1 := Ty.prod (drvKindHaltedTy subs) (sidT (ℓ := ℓ) (Pt := Pt) S) :: Γ
  let Γ2 := Ty.prod (FinT (ℓ := ℓ) (Pt := Pt) S.N_id) (FinT (ℓ := ℓ) (Pt := Pt) S.N_recv) :: Γ1
  let Γ3 := keyIndRT (ℓ := ℓ) (Pt := Pt) :: Γ2
  let Γ4 := keyIndRT (ℓ := ℓ) (Pt := Pt) :: Γ3
  let Γ5 := (e2eKeyIndTargetIface S ℓ Pt).smp.sTy
    (UniformSamplerTag.base AtomicBaseUnif.bv256) :: Γ4
  have hprep := subs.prepStartSpkE_size b qStart (Γ := Γ1) (.fst (.fst .v0)) (.snd .v0)
  have hts : (mkAtomicTestSessionE (O := atomicE2EOps ℓ P C K decT encT) (Γ := Γ2) (.snd .v1)).size ≤
      12 := by
    simp [mkAtomicTestSessionE, Expr.size, Expr.v1]
  have hrv : (mkAtomicRevealSpkSkE (O := atomicE2EOps ℓ P C K decT encT) (Γ := Γ3) .v1).size ≤
      15 := by
    simp [mkAtomicRevealSpkSkE, Expr.size, Expr.v1]
  have hbit := subs.drvBitE_size (Γ := Γ5) (.fst (.fst .v4))
  have hfin := subs.finishStartSpkHaltedC_size b qStart (Γ := Γ5)
    (.some (subs.drvBitE (.fst (.fst .v4)))) (.fst .v4) (.snd .v4) .v2 .v1 .v0
  dsimp only [kindStartStepHaltedC, Comp.size,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v4] at hprep hts hrv hbit hfin ⊢
  omega

theorem kindRedHalted_size_le_leaf
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) :
    (kindRedHalted subs b qStart qDR qep).size ≤
      haltedKindSizeBound subs b qStart qDR qep := by
  let Γ_ki : List (Ty (atomicSig ℓ Pt)) :=
    [keyIndQT (ℓ := ℓ) (Pt := Pt) S,
      Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
      drvKindHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]
  let Γ_kr : List (Ty (atomicSig ℓ Pt)) := keyIndRT (ℓ := ℓ) (Pt := Pt) :: Γ_ki
  let Γ_ctl : List (Ty (atomicSig ℓ Pt)) :=
    [sidT (ℓ := ℓ) (Pt := Pt) S,
      Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
      drvKindHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]
  let Γ_sm : List (Ty (atomicSig ℓ Pt)) :=
    [Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)), drvKindHaltedTy subs,
      (e2eTargetGameCodec S ℓ Pt).Q]
  have hinit := subs.initKindC_size (Γ := [.unit])
  have hfin := subs.finishKindE_size qStart (Γ := [drvKindHaltedTy subs, .bool]) (.fst .v0) .v1
  have hok := subs.kiQueryOkE_size b qStart (Γ := Γ_ki) (.fst .v2) .v0
  have hmir := subs.mirrorE_size (Γ := Γ_kr) (.fst .v3) .v1 .v0
  have hst := kindStartStepHaltedC_size subs b qStart (Γ := Γ_ctl) .v2 .v0
  have hsm := subs.haltedStepLocalSmC_size b qStart qDR qep (Γ := Γ_sm) .v1 (.fst .v0) (.snd .v0)
  dsimp only [CostedReduction.size, kindRedHalted, kindHandleHalted, haltedKindSizeBound,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at *
  omega

theorem kindRedHalted_size_le_budget
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep costBudget C₀ C₁ : ℕ)
    (h₀ : C₀ ≤ 2 ^ 22) (h₁ : C₁ ≤ 2 ^ 11)
    (hLeaf : haltedKindSizeBound subs b qStart qDR qep ≤ C₀ + C₁ * bits costBudget) :
    (kindRedHalted subs b qStart qDR qep).size ≤
      reductionSizeBudget + 2 ^ 12 * bits costBudget :=
  size_le_budget_of_log_cost h₀ h₁
    (le_trans (kindRedHalted_size_le_leaf subs b qStart qDR qep) hLeaf)

/-- `GRedBounded` certificate for `kindRedHalted` under `costBudget`. -/
theorem kindRedHalted_gRedBounded
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep qTot costBudget : ℕ)
    (hCost :
      haltedKindEndpointCost subs qStart +
        qTot * haltedKindStepCost subs b qStart qDR qep ≤ costBudget)
    (hSize :
      (kindRedHalted subs b qStart qDR qep).size ≤
        reductionSizeBudget + 2 ^ 12 * bits costBudget) :
    GRedBounded (kindRedHalted subs b qStart qDR qep)
      (fun _ => 1) (fun _ => 0) qTot (2 * qTot) costBudget :=
  gRedBounded_of_bounds (kindRedHalted subs b qStart qDR qep)
    (fun _ => 1) (fun _ => 0) qTot (2 * qTot) costBudget
    (le_trans (kindRedHalted_totalCost_le_leaf subs b qStart qDR qep qTot) hCost)
    hSize
    (kindRedHalted_totalQueries_le subs b qStart qDR qep qTot)
    (atomicE2EOps_sizeHonest ℓ P C K decT encT)
    (atomicBaseSamplers_sizeHonest ℓ Pt)

end AtomicProgram

/-! ## Codec round-trips and `SignalPqxdh.QueryBounded` transfer -/

section QueryBounds

variable {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
  {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}

@[simp] theorem sidOfV_sidV (sid : SignalPqxdh.SessionId S) :
    sidOfV (ℓ := ℓ) (Pt := Pt) (sidV sid) = sid := by
  cases sid <;> rfl

@[simp] theorem keyIndQdec_keyIndQenc (kq : SignalPqxdh.KeyIndQuery S) :
    keyIndQdec (ℓ := ℓ) (Pt := Pt) (keyIndQenc kq) = kq := by
  cases kq with
  | testSession sid => cases sid <;> rfl
  | revealSessionKey sid => cases sid <;> rfl
  | _ => rfl

@[simp] theorem keyIndRdec_keyIndRenc (kr : SignalPqxdh.KeyIndResponse) :
    keyIndRdec (ℓ := ℓ) (Pt := Pt) (keyIndRenc kr) = kr := by
  cases kr <;> rfl

@[simp] private theorem recvResultDec_recvResultEnc (rr : CryptoGames.SM.RecvResult (Plain ℓ)) :
    recvResultDec (ℓ := ℓ) (Pt := Pt) (recvResultEnc rr) = rr := by
  cases rr <;> rfl

@[expose] def packAtomicSmRespEnc (br : BHE2ESmResp ℓ) : (smRT (ℓ := ℓ) (Pt := Pt) GhostStT).denote :=
  (br.1, (br.2.1.map recvResultEnc, br.2.2))

@[simp] theorem smRdec_id_packAtomicSmRespEnc
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (br : BHE2ESmResp ℓ) :
    smRdec (ℓ := ℓ) (Pt := Pt) (stT := GhostStT) id sq (packAtomicSmRespEnc br) =
      bhUnpackSmResp sq br := by
  rcases br with ⟨w, rr?, st?⟩
  rcases sq with (((_ | _) | _) | _) | _
  · rfl
  · rfl
  · cases rr? <;> simp [packAtomicSmRespEnc, smRdec, bhUnpackSmResp]
  · cases rr? <;> simp [packAtomicSmRespEnc, smRdec, bhUnpackSmResp]
  · cases st? <;> rfl

@[expose] def atomicKindRespEnc : BHTargetResp ℓ → (e2eTargetGameCodec S ℓ Pt).R.denote
  | .inl (.inl kr) => .inl (.inl (keyIndRenc kr))
  | .inl (.inr idx?) => .inl (.inr idx?)
  | .inr sr => .inr (packAtomicSmRespEnc sr)

@[simp] theorem e2eTargetGameCodec_rdec_atomicKindRespEnc
    (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) (r : BHTargetResp ℓ) :
    (e2eTargetGameCodec S ℓ Pt).rdec t (atomicKindRespEnc (S := S) (Pt := Pt) r) =
      bhTargetRdec t r := by
  rcases t with (kq | cq) | ⟨i, sq⟩
  · rcases r with (kr | idx?) | sr
    · exact keyIndRdec_keyIndRenc kr
    · rfl
    · rfl
  · rcases cq with ⟨sid⟩
    rcases r with (kr | idx?) | sr <;> rfl
  · rcases r with (kr | idx?) | sr
    · rcases sq with (((_ | _) | _) | _) | _ <;> rfl
    · rcases sq with (((_ | _) | _) | _) | _ <;> rfl
    · exact smRdec_id_packAtomicSmRespEnc sq sr

/-- Target-game query-budget hypotheses on `B_A` over `unifSpec + bhTargetGameSpec`. -/
structure KindTargetAdvBounded (S : SignalPqxdh.Setup) {ℓ : ℕ}
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) : Prop where
  ro : B_A.IsQueryBoundP
    (fun q => bhClassifyTarget (fun kq => kq matches .roQuery _) (fun _ => false) (fun _ => false) q = true)
    b.q_ro
  send : B_A.IsQueryBoundP
    (fun q => bhClassifyTarget
      (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
      (fun _ => false) (fun _ => false) q = true)
    S.N_send_tot
  recv : B_A.IsQueryBoundP
    (fun q => bhClassifyTarget
      (fun kq => kq matches .acceptOPK .. || kq matches .acceptNoOPK ..)
      (fun _ => false) (fun _ => false) q = true)
    S.N_recv_tot
  tot : B_A.IsQueryBoundP
    (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
    b.q_total
  on : B_A.IsQueryBoundP
    (fun q => bhClassifyTarget (fun kq => !(kq matches .roQuery _)) (fun _ => false) (fun _ => false) q = true)
    b.q_on
  ctl : B_A.IsQueryBoundP
    (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
    S.N_send_tot
  start : B_A.IsQueryBoundP
    (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
    qStart
  dr : B_A.IsQueryBoundP
    (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun _ => true) q = true)
    qDR

private theorem isQueryBoundP_keyIndTargetIface_fwdU
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n, ¬ P_ki (.inl n)) (n : ℕ) :
    ((e2eKeyIndTargetIface S ℓ Pt).fwdU n).IsQueryBoundP P_ki 0 :=
  (isQueryBoundP_query_iff (spec := unifSpec + SignalPqxdh.keyIndSpec S)
    P_ki (Sum.inl n) 0).2 (fun h => False.elim (hInl n h))

private theorem hw_keyIndTargetIface
    (P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop) :
    ∀ (g : (e2eKeyIndTargetIface S ℓ Pt).Tag) (x : ((e2eKeyIndTargetIface S ℓ Pt).dom g).denote),
      P_ki ((e2eKeyIndTargetIface S ℓ Pt).enc g x) → 1 ≤ (fun _ => 1) g :=
  fun _ _ _ => le_rfl

private theorem isQueryBoundP_kindRedHalted_init
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n, ¬ P_ki (.inl n)) :
    ((kindRedHalted subs b qStart qDR qep).init.eval
      (Env.cons (t := .unit) () Env.nil)).IsQueryBoundP P_ki 0 := by
  dsimp only [kindRedHalted, Comp.eval]
  have hq := subs.initKindC_queries (Γ := [.unit]) (fun _ => 1)
  have hc := (Comp.queryBound_eval P_ki (fun _ => 1) (fun _ => 0)
    (hw_keyIndTargetIface P_ki) (isQueryBoundP_keyIndTargetIface_fwdU hInl)
    (subs.initKindC (Γ := [.unit]))
    (Env.cons (t := .unit) () Env.nil)).mono (by rw [hq])
  exact (isQueryBoundP_bind hc (fun v _ => isQueryBoundP_pure P_ki _ 0)).mono (by omega)

theorem kindHandleHalted_eval_ki
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    (s : (drvKindHaltedTy subs).denote) (kq : SignalPqxdh.KeyIndQuery S) :
    let Γ_ki : List (Ty (atomicSig ℓ Pt)) :=
      [keyIndQT (ℓ := ℓ) (Pt := Pt) S,
        Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
        drvKindHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]
    let ρ_ki : Env Γ_ki :=
      .cons (keyIndQenc kq) (.cons (Sum.inl (keyIndQenc kq))
        (.cons s (.cons (Sum.inl (Sum.inl (keyIndQenc kq))) .nil)))
    (kindHandleHalted subs b qStart qDR qep).eval
        (.cons s (.cons ((e2eTargetGameCodec S ℓ Pt).qenc (.inl (.inl kq))) .nil)) =
      if (subs.kiQueryOkE b qStart (.fst .v2) .v0).eval ρ_ki = true then
        (Comp.query (O := atomicE2EOps ℓ P C K decT encT)
            (I := e2eKeyIndTargetIface S ℓ Pt) E2EKeyIndTag.keyInd .v0).eval ρ_ki >>=
          fun krV =>
          pure ((.inl (.inl krV) : (e2eTargetGameCodec S ℓ Pt).R.denote),
            ((subs.mirrorE (.fst .v3) .v1 .v0).eval (.cons krV ρ_ki), s.2))
      else
        pure ((.inl (.inl (.inl ())) : (e2eTargetGameCodec S ℓ Pt).R.denote), s) := rfl

theorem kindHandleHalted_eval_ctl
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    (s : (drvKindHaltedTy subs).denote) (sid : SignalPqxdh.SessionId S) :
    let Γ_ctl : List (Ty (atomicSig ℓ Pt)) :=
      [sidT (ℓ := ℓ) (Pt := Pt) S,
        Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
        drvKindHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]
    let ρ_ctl : Env Γ_ctl :=
      .cons (sidV sid) (.cons (Sum.inr (sidV sid))
        (.cons s (.cons (Sum.inl (Sum.inr (sidV sid))) .nil)))
    (kindHandleHalted subs b qStart qDR qep).eval
        (.cons s (.cons ((e2eTargetGameCodec S ℓ Pt).qenc (.inl (.inr (.startDR sid)))) .nil)) =
      ((kindStartStepHaltedC subs b qStart .v2 .v0).eval ρ_ctl >>=
        fun v => pure ((.inl (.inr v.1) : (e2eTargetGameCodec S ℓ Pt).R.denote), v.2)) := rfl

theorem kindHandleHalted_eval_sm
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    (s : (drvKindHaltedTy subs).denote) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    let Γ_sm : List (Ty (atomicSig ℓ Pt)) :=
      [Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)), drvKindHaltedTy subs,
        (e2eTargetGameCodec S ℓ Pt).Q]
    let ρ_sm : Env Γ_sm :=
      .cons (i, smQenc sq) (.cons s (.cons (Sum.inr (i, smQenc sq)) .nil))
    (kindHandleHalted subs b qStart qDR qep).eval
        (.cons s (.cons ((e2eTargetGameCodec S ℓ Pt).qenc (.inr (i, sq))) .nil)) =
      ((subs.haltedStepLocalSmC b qStart qDR qep .v1 (.fst .v0) (.snd .v0)).eval ρ_sm >>=
        fun v => pure ((.inr v.1 : (e2eTargetGameCodec S ℓ Pt).R.denote), v.2)) := rfl

private theorem isQueryBoundP_kindHandleHalted_ki_subpred
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (pKi : SignalPqxdh.KeyIndQuery S → Bool) (hSub : ∀ kq, P_ki (.inr kq) → pKi kq = true)
    (s : (drvKindHaltedTy subs).denote) (kq : SignalPqxdh.KeyIndQuery S) :
    ((kindHandleHalted subs b qStart qDR qep).eval
      (.cons s (.cons ((e2eTargetGameCodec S ℓ Pt).qenc (.inl (.inl kq))) .nil))).IsQueryBoundP
      P_ki (if pKi kq = true then 1 else 0) := by
  rw [kindHandleHalted_eval_ki]
  let Γ_ki : List (Ty (atomicSig ℓ Pt)) :=
    [keyIndQT (ℓ := ℓ) (Pt := Pt) S,
      Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
      drvKindHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]
  let ρ_ki : Env Γ_ki :=
    .cons (keyIndQenc kq) (.cons (Sum.inl (keyIndQenc kq))
      (.cons s (.cons (Sum.inl (Sum.inl (keyIndQenc kq))) .nil)))
  by_cases hp : pKi kq = true
  · simp only [hp, ↓reduceIte]
    split
    · have hq1 : ((Comp.query (O := atomicE2EOps ℓ P C K decT encT)
          (I := e2eKeyIndTargetIface S ℓ Pt) E2EKeyIndTag.keyInd .v0).eval ρ_ki).IsQueryBoundP
          P_ki 1 := by
        simp only [Comp.eval, isQueryBoundP_map_iff, isQueryBoundP_query_iff]; intro _; omega
      exact (isQueryBoundP_bind hq1 (fun _ _ => isQueryBoundP_pure P_ki _ 0)).mono (by omega)
    · exact isQueryBoundP_pure P_ki _ 1
  · have hpF : pKi kq = false := Bool.eq_false_iff.mpr hp
    simp only [hpF, Bool.false_eq_true, ↓reduceIte]
    have hnot : ¬ P_ki (.inr kq) := fun h => hp (hSub kq h)
    split
    · have hq0 : ((Comp.query (O := atomicE2EOps ℓ P C K decT encT)
          (I := e2eKeyIndTargetIface S ℓ Pt) E2EKeyIndTag.keyInd .v0).eval ρ_ki).IsQueryBoundP
          P_ki 0 := by
        simp only [Comp.eval, isQueryBoundP_map_iff, isQueryBoundP_query_iff, e2eKeyIndTargetIface]
        change P_ki (.inr (keyIndQdec (keyIndQenc kq))) → 1 ≤ 0
        rw [keyIndQdec_keyIndQenc]; exact fun h => False.elim (hnot h)
      exact (isQueryBoundP_bind hq0 (fun _ _ => isQueryBoundP_pure P_ki _ 0)).mono (by omega)
    · exact isQueryBoundP_pure P_ki _ 0

private theorem isQueryBoundP_kindHandleHalted_ctl_two
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n, ¬ P_ki (.inl n))
    (s : (drvKindHaltedTy subs).denote) (sid : SignalPqxdh.SessionId S) :
    ((kindHandleHalted subs b qStart qDR qep).eval
      (.cons s (.cons ((e2eTargetGameCodec S ℓ Pt).qenc (.inl (.inr (.startDR sid)))) .nil))).IsQueryBoundP
      P_ki 2 :=
  (Comp.queryBound_eval P_ki (fun _ => 1) (fun _ => 0)
    (hw_keyIndTargetIface P_ki) (isQueryBoundP_keyIndTargetIface_fwdU hInl)
    (kindHandleHalted subs b qStart qDR qep) _).mono
    (kindHandleHalted_queries_le subs b qStart qDR qep)

private theorem isQueryBoundP_kindHandleHalted_sm_zero
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n, ¬ P_ki (.inl n)) (s : (drvKindHaltedTy subs).denote) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    ((kindHandleHalted subs b qStart qDR qep).eval
      (.cons s (.cons ((e2eTargetGameCodec S ℓ Pt).qenc (.inr ⟨i, sq⟩)) .nil))).IsQueryBoundP
      P_ki 0 := by
  rw [kindHandleHalted_eval_sm]
  let Γ_sm : List (Ty (atomicSig ℓ Pt)) :=
    [Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)), drvKindHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]
  let ρ_sm : Env Γ_sm := .cons (i, smQenc sq) (.cons s (.cons (Sum.inr (i, smQenc sq)) .nil))
  have hq := subs.haltedStepLocalSmC_queries b qStart qDR qep (Γ := Γ_sm)
    .v1 (.fst .v0) (.snd .v0) (fun _ => 1)
  have hc := (Comp.queryBound_eval P_ki (fun _ => 1) (fun _ => 0)
    (hw_keyIndTargetIface P_ki) (isQueryBoundP_keyIndTargetIface_fwdU hInl)
    (subs.haltedStepLocalSmC b qStart qDR qep (Γ := Γ_sm) .v1 (.fst .v0) (.snd .v0)) ρ_sm).mono
    (by rw [hq])
  exact (isQueryBoundP_bind hc (fun _ _ => isQueryBoundP_pure P_ki _ 0)).mono (by omega)

private theorem isQueryBoundP_kindHandleHalted_subpred
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n, ¬ P_ki (.inl n)) (hTest : ∀ sid, ¬ P_ki (.inr (.testSession sid)))
    (hRev : ∀ u j, ¬ P_ki (.inr (.revealSpkSk u j))) (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (hSub : ∀ kq, P_ki (.inr kq) → pKi kq = true) (s : (drvKindHaltedTy subs).denote)
    (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) :
    ((kindHandleHalted subs b qStart qDR qep).eval
      (.cons s (.cons ((e2eTargetGameCodec S ℓ Pt).qenc t) .nil))).IsQueryBoundP
      P_ki (if bhClassifyTargetOnly pKi (fun _ => false) (fun _ => false) t then 1 else 0) := by
  have hU := isQueryBoundP_keyIndTargetIface_fwdU (S := S) (ℓ := ℓ) (Pt := Pt) hInl
  have hw := hw_keyIndTargetIface (S := S) (ℓ := ℓ) (Pt := Pt) P_ki
  rcases t with (kq | cq) | ⟨i, sq⟩
  · simp only [bhClassifyTargetOnly]
    exact isQueryBoundP_kindHandleHalted_ki_subpred subs b qStart qDR qep pKi hSub s kq
  · rcases cq with ⟨sid⟩
    simp only [bhClassifyTargetOnly, Bool.false_eq_true, ↓reduceIte]
    rw [kindHandleHalted_eval_ctl]
    let Γ_ctl : List (Ty (atomicSig ℓ Pt)) :=
      [sidT (ℓ := ℓ) (Pt := Pt) S,
        Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
        drvKindHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]
    let ρ_ctl : Env Γ_ctl :=
      .cons (sidV sid) (.cons (Sum.inr (sidV sid))
        (.cons s (.cons (Sum.inl (Sum.inr (sidV sid))) .nil)))
    have hctl0 : ((kindStartStepHaltedC subs b qStart .v2 .v0).eval ρ_ctl).IsQueryBoundP P_ki 0 := by
      dsimp only [kindStartStepHaltedC, Comp.eval]; rw [pure_bind]
      let Γ1 := Ty.prod (drvKindHaltedTy subs) (sidT (ℓ := ℓ) (Pt := Pt) S) :: Γ_ctl
      let ρ1 : Env Γ1 :=
        .cons ((Expr.pair (O := atomicE2EOps ℓ P C K decT encT) .v2 .v0).eval ρ_ctl) ρ_ctl
      cases (subs.prepStartSpkE b qStart (.fst (.fst .v0)) (.snd .v0)).eval ρ1 with
      | none => exact isQueryBoundP_pure P_ki _ 0
      | some uj =>
        let Γ2 := Ty.prod (FinT (ℓ := ℓ) (Pt := Pt) S.N_id) (FinT (ℓ := ℓ) (Pt := Pt) S.N_recv) :: Γ1
        let ρ2 : Env Γ2 := .cons uj ρ1
        have hts0 : ((Comp.query (O := atomicE2EOps ℓ P C K decT encT)
              (I := e2eKeyIndTargetIface S ℓ Pt) E2EKeyIndTag.keyInd
              (mkAtomicTestSessionE (.snd .v1))).eval ρ2).IsQueryBoundP P_ki 0 := by
          simp only [Comp.eval, isQueryBoundP_map_iff, isQueryBoundP_query_iff, e2eKeyIndTargetIface,
            eval_mkAtomicTestSessionE]
          change P_ki (.inr (keyIndQdec (keyIndQenc (.testSession (sidOfV (sidV sid)))))) → 1 ≤ 0
          rw [sidOfV_sidV, keyIndQdec_keyIndQenc]; exact fun h => False.elim (hTest sid h)
        refine (isQueryBoundP_bind (n := 0) (m := 0) hts0 (fun kr1V _ => ?_)).mono (by omega)
        let Γ3 := keyIndRT (ℓ := ℓ) (Pt := Pt) :: Γ2
        let ρ3 : Env Γ3 := .cons kr1V ρ2
        have hrv0 : ((Comp.query (O := atomicE2EOps ℓ P C K decT encT)
              (I := e2eKeyIndTargetIface S ℓ Pt) E2EKeyIndTag.keyInd
              (mkAtomicRevealSpkSkE .v1)).eval ρ3).IsQueryBoundP P_ki 0 := by
          simp only [Comp.eval, isQueryBoundP_map_iff, isQueryBoundP_query_iff, e2eKeyIndTargetIface,
            eval_mkAtomicRevealSpkSkE]
          change P_ki (.inr (keyIndQdec (keyIndQenc (.revealSpkSk uj.1 uj.2)))) → 1 ≤ 0
          rw [keyIndQdec_keyIndQenc]; exact fun h => False.elim (hRev uj.1 uj.2 h)
        refine (isQueryBoundP_bind (n := 0) (m := 0) hrv0 (fun kr2V _ => ?_)).mono (by omega)
        let Γ4 := keyIndRT (ℓ := ℓ) (Pt := Pt) :: Γ3
        let ρ4 : Env Γ4 := .cons kr2V ρ3
        have hsmp0 : ((Comp.sample (O := atomicE2EOps ℓ P C K decT encT)
              (I := e2eKeyIndTargetIface S ℓ Pt)
              (UniformSamplerTag.base AtomicBaseUnif.bv256) .unit).eval ρ4).IsQueryBoundP P_ki 0 :=
          liftP_queryBound P_ki hU _
        refine (isQueryBoundP_bind (n := 0) (m := 0) hsmp0 (fun ac _ => ?_)).mono (by omega)
        let Γ5 := (e2eKeyIndTargetIface S ℓ Pt).smp.sTy
          (UniformSamplerTag.base AtomicBaseUnif.bv256) :: Γ4
        let ρ5 : Env Γ5 := .cons ac ρ4
        have hfin := subs.finishStartSpkHaltedC_queries b qStart (Γ := Γ5)
          (.some (subs.drvBitE (.fst (.fst .v4)))) (.fst .v4) (.snd .v4) .v2 .v1 .v0 (fun _ => 1)
        exact (Comp.queryBound_eval P_ki (fun _ => 1) (fun _ => 0) hw hU
          (subs.finishStartSpkHaltedC b qStart (Γ := Γ5)
            (.some (subs.drvBitE (.fst (.fst .v4)))) (.fst .v4) (.snd .v4) .v2 .v1 .v0) ρ5).mono
          (by rw [hfin])
    exact (isQueryBoundP_bind hctl0 (fun _ _ => isQueryBoundP_pure P_ki _ 0)).mono (by omega)
  · simp only [bhClassifyTargetOnly, Bool.false_eq_true, ↓reduceIte]
    exact isQueryBoundP_kindHandleHalted_sm_zero subs b qStart qDR qep hInl s i sq

private theorem isQueryBoundP_kindRedHalted_eval_subpred
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n, ¬ P_ki (.inl n)) (hTest : ∀ sid, ¬ P_ki (.inr (.testSession sid)))
    (hRev : ∀ u j, ¬ P_ki (.inr (.revealSpkSk u j))) (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (hSub : ∀ kq, P_ki (.inr kq) → pKi kq = true)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) (n : ℕ)
    (hB : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget pKi (fun _ => false) (fun _ => false) q = true) n) :
    ((kindRedHalted subs b qStart qDR qep).eval (fun _ => B_A) ()).IsQueryBoundP P_ki n := by
  have hstep : ∀ (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
      (s : (kindRedHalted subs b qStart qDR qep).σ.denote),
      (((kindRedHalted subs b qStart qDR qep).impl q).run s).IsQueryBoundP
        P_ki (if bhClassifyTarget pKi (fun _ => false) (fun _ => false) q = true then 1 else 0) := by
    intro q s; cases q with
    | inl m =>
      show ((e2eKeyIndTargetIface S ℓ Pt).fwdU m >>= fun a => pure (a, s)).IsQueryBoundP P_ki 0
      exact (isQueryBoundP_bind (isQueryBoundP_keyIndTargetIface_fwdU hInl m)
        (fun a _ => isQueryBoundP_pure P_ki (a, s) 0)).mono (by omega)
    | inr t =>
      show ((kindHandleHalted subs b qStart qDR qep).eval
          (.cons s (.cons ((e2eTargetGameCodec S ℓ Pt).qenc t) .nil)) >>=
          fun p => pure ((e2eTargetGameCodec S ℓ Pt).rdec t p.1, p.2)).IsQueryBoundP
        P_ki (if bhClassifyTargetOnly pKi (fun _ => false) (fun _ => false) t = true then 1 else 0)
      simpa only [Nat.add_zero] using isQueryBoundP_bind
        (isQueryBoundP_kindHandleHalted_subpred subs b qStart qDR qep hInl hTest hRev pKi hSub s t)
        (fun p _ => isQueryBoundP_pure P_ki ((e2eTargetGameCodec S ℓ Pt).rdec t p.1, p.2) 0)
  have hsim : ∀ s, ((simulateQ (kindRedHalted subs b qStart qDR qep).impl B_A).run s).IsQueryBoundP
      P_ki n := fun s => (simulateQ_run_StateT_of_step_le (k := 1) hstep hB s).mono (by omega)
  have hinit := isQueryBoundP_kindRedHalted_init subs b qStart qDR qep hInl
  have hfin : ∀ s' b_out,
      ((kindRedHalted subs b qStart qDR qep).finish.eval
        (Env.cons s' (Env.cons b_out Env.nil))).IsQueryBoundP P_ki 0 :=
    fun _ _ => isQueryBoundP_pure P_ki _ 0
  unfold CostedReduction.eval
  exact (isQueryBoundP_bind (n := 0) (m := n) hinit (fun ⟨_, s⟩ _ =>
    (isQueryBoundP_bind (n := n) (m := 0) (hsim s)
      (fun ⟨b_out, s'⟩ _ => hfin s' b_out)).mono (by omega))).mono (by omega)

private theorem isQueryBoundP_simulateQ_kindRedHalted_subpred_ctl
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n, ¬ P_ki (.inl n))
    (pKi : SignalPqxdh.KeyIndQuery S → Bool) (hSub : ∀ kq, P_ki (.inr kq) → pKi kq = true)
    {α : Type} (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (s : (kindRedHalted subs b qStart qDR qep).σ.denote) (n₁ n₂ : ℕ)
    (h₁ : oa.IsQueryBoundP
      (fun q => bhClassifyTarget pKi (fun _ => false) (fun _ => false) q = true) n₁)
    (h₂ : oa.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true) n₂) :
    ((simulateQ (kindRedHalted subs b qStart qDR qep).impl oa).run s).IsQueryBoundP
      P_ki (n₁ + 2 * n₂) := by
  induction oa using OracleComp.inductionOn generalizing s n₁ n₂ with
  | pure _ => simp [simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h₁ h₂
    rw [simulateQ_query_bind, StateT.run_bind]
    rcases q with m | ((kq | cq) | ⟨i, sq⟩)
    · have hstep : (((kindRedHalted subs b qStart qDR qep).impl (.inl m)).run s).IsQueryBoundP
          P_ki 0 :=
        (isQueryBoundP_bind (isQueryBoundP_keyIndTargetIface_fwdU hInl m)
          (fun a _ => isQueryBoundP_pure P_ki (a, s) 0)).mono (by omega)
      exact (isQueryBoundP_bind hstep fun y _ => ih y.1 y.2 n₁ n₂
        ((h₁.2 y.1).mono (by simp [bhClassifyTarget]))
        ((h₂.2 y.1).mono (by simp [bhClassifyTarget]))).mono (by omega)
    · by_cases hp : pKi kq = true
      · have hn₁ : 0 < n₁ :=
          h₁.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly, hp])
        have hki := isQueryBoundP_kindHandleHalted_ki_subpred subs b qStart qDR qep pKi hSub s kq
        simp only [hp, ↓reduceIte] at hki
        have hstep : (((kindRedHalted subs b qStart qDR qep).impl
            (.inr (.inl (.inl kq)))).run s).IsQueryBoundP P_ki 1 :=
          (isQueryBoundP_bind hki
            (fun p _ => isQueryBoundP_pure P_ki
              ((e2eTargetGameCodec S ℓ Pt).rdec (.inl (.inl kq)) p.1, p.2) 0)).mono (by omega)
        exact (isQueryBoundP_bind hstep fun y _ => ih y.1 y.2 (n₁ - 1) n₂
          ((h₁.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly, hp]))
          ((h₂.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))).mono (by omega)
      · have hpF : pKi kq = false := Bool.eq_false_iff.mpr hp
        have hki := isQueryBoundP_kindHandleHalted_ki_subpred subs b qStart qDR qep pKi hSub s kq
        simp only [hpF, Bool.false_eq_true, ↓reduceIte] at hki
        have hstep : (((kindRedHalted subs b qStart qDR qep).impl
            (.inr (.inl (.inl kq)))).run s).IsQueryBoundP P_ki 0 :=
          (isQueryBoundP_bind hki
            (fun p _ => isQueryBoundP_pure P_ki
              ((e2eTargetGameCodec S ℓ Pt).rdec (.inl (.inl kq)) p.1, p.2) 0)).mono (by omega)
        exact (isQueryBoundP_bind hstep fun y _ => ih y.1 y.2 n₁ n₂
          ((h₁.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly, hpF]))
          ((h₂.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))).mono (by omega)
    · rcases cq with ⟨sid⟩
      have hn₂ : 0 < n₂ := h₂.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
      have hstep : (((kindRedHalted subs b qStart qDR qep).impl
          (.inr (.inl (.inr (.startDR sid))))).run s).IsQueryBoundP P_ki 2 :=
        (isQueryBoundP_bind (isQueryBoundP_kindHandleHalted_ctl_two subs b qStart qDR qep hInl s sid)
          (fun p _ => isQueryBoundP_pure P_ki
            ((e2eTargetGameCodec S ℓ Pt).rdec (.inl (.inr (.startDR sid))) p.1, p.2) 0)).mono
          (by omega)
      exact (isQueryBoundP_bind hstep fun y _ => ih y.1 y.2 n₁ (n₂ - 1)
        ((h₁.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
        ((h₂.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))).mono (by omega)
    · have hstep : (((kindRedHalted subs b qStart qDR qep).impl
          (.inr (.inr ⟨i, sq⟩))).run s).IsQueryBoundP P_ki 0 :=
        (isQueryBoundP_bind (isQueryBoundP_kindHandleHalted_sm_zero subs b qStart qDR qep hInl s i sq)
          (fun p _ => isQueryBoundP_pure P_ki
            ((e2eTargetGameCodec S ℓ Pt).rdec (.inr ⟨i, sq⟩) p.1, p.2) 0)).mono (by omega)
      exact (isQueryBoundP_bind hstep fun y _ => ih y.1 y.2 n₁ n₂
        ((h₁.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
        ((h₂.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))).mono (by omega)

private theorem isQueryBoundP_kindRedHalted_eval_subpred_ctl
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n, ¬ P_ki (.inl n))
    (pKi : SignalPqxdh.KeyIndQuery S → Bool) (hSub : ∀ kq, P_ki (.inr kq) → pKi kq = true)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) (n₁ n₂ : ℕ)
    (h₁ : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget pKi (fun _ => false) (fun _ => false) q = true) n₁)
    (h₂ : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true) n₂) :
    ((kindRedHalted subs b qStart qDR qep).eval (fun _ => B_A) ()).IsQueryBoundP
      P_ki (n₁ + 2 * n₂) := by
  have hinit := isQueryBoundP_kindRedHalted_init subs b qStart qDR qep hInl
  have hfin : ∀ s' b_out,
      ((kindRedHalted subs b qStart qDR qep).finish.eval
        (Env.cons s' (Env.cons b_out Env.nil))).IsQueryBoundP P_ki 0 :=
    fun _ _ => isQueryBoundP_pure P_ki _ 0
  unfold CostedReduction.eval
  exact (isQueryBoundP_bind hinit (fun ⟨_, s⟩ _ =>
    isQueryBoundP_bind
      (isQueryBoundP_simulateQ_kindRedHalted_subpred_ctl subs b qStart qDR qep hInl pKi hSub
        B_A s n₁ n₂ h₁ h₂)
      (fun ⟨b_out, s'⟩ _ => hfin s' b_out))).mono (by omega)

theorem kindRedHalted_queryBounded_inst
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qInst qep : ℕ)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : KindTargetAdvBounded S B_A b qStart qDR) :
    SignalPqxdh.QueryBounded
      (⟨(kindRedHalted subs b qStart qInst qep).eval (fun _ => B_A) ()⟩ :
        SignalPqxdh.KeyIndAdversary S)
      (keyIndReductionBudget S qStart b) := by
  have hCtlMin : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      (min qStart S.N_send_tot) := by
    by_cases hle : qStart ≤ S.N_send_tot
    · rw [Nat.min_eq_left hle]; exact hB.start
    · rw [Nat.min_eq_right (by omega)]; exact hB.ctl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact isQueryBoundP_kindRedHalted_eval_subpred subs b qStart qInst qep
      (by intro n; simp [SignalPqxdh.isKeyIndRoQuery])
      (by intro sid; simp [SignalPqxdh.isKeyIndRoQuery])
      (by intro u j; simp [SignalPqxdh.isKeyIndRoQuery])
      (fun kq => kq matches .roQuery _)
      (by intro kq h; cases kq <;> first | rfl | exact False.elim h)
      B_A b.q_ro hB.ro
  · exact isQueryBoundP_kindRedHalted_eval_subpred subs b qStart qInst qep
      (by intro n; simp [SignalPqxdh.isKeyIndSendQuery])
      (by intro sid; simp [SignalPqxdh.isKeyIndSendQuery])
      (by intro u j; simp [SignalPqxdh.isKeyIndSendQuery])
      (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
      (by intro kq h; cases kq <;> first | rfl | exact False.elim h)
      B_A S.N_send_tot hB.send
  · exact isQueryBoundP_kindRedHalted_eval_subpred subs b qStart qInst qep
      (by intro n; simp [SignalPqxdh.isKeyIndRecvQuery])
      (by intro sid; simp [SignalPqxdh.isKeyIndRecvQuery])
      (by intro u j; simp [SignalPqxdh.isKeyIndRecvQuery])
      (fun kq => kq matches .acceptOPK .. || kq matches .acceptNoOPK ..)
      (by intro kq h; cases kq <;> first | rfl | exact False.elim h)
      B_A S.N_recv_tot hB.recv
  · exact isQueryBoundP_kindRedHalted_eval_subpred_ctl subs b qStart qInst qep
      (P_ki := fun q => SignalPqxdh.isGameQuery q = true)
      (by intro n; simp [SignalPqxdh.isGameQuery])
      (fun _ => true) (fun _ _ => rfl)
      B_A b.q_total (min qStart S.N_send_tot) hB.tot hCtlMin
  · exact isQueryBoundP_kindRedHalted_eval_subpred_ctl subs b qStart qInst qep
      (P_ki := SignalPqxdh.isKeyIndOnlineQuery)
      (by intro n; simp [SignalPqxdh.isKeyIndOnlineQuery])
      (fun kq => !(kq matches .roQuery _))
      (by intro kq h; cases kq <;> first | rfl | exact False.elim h)
      B_A b.q_on (min qStart S.N_send_tot) hB.on hCtlMin

/-- Per-instance `SignalPqxdh.QueryBounded` transfer for `kindRedHalted`. -/
theorem kindRedHalted_queryBounded
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : KindTargetAdvBounded S B_A b qStart qDR) :
    SignalPqxdh.QueryBounded
      (⟨(kindRedHalted subs b qStart qDR qep).eval (fun _ => B_A) ()⟩ :
        SignalPqxdh.KeyIndAdversary S)
      (keyIndReductionBudget S qStart b) :=
  kindRedHalted_queryBounded_inst subs b qStart qDR qDR qep B_A hB

end QueryBounds

end Computational.Proofs.E2E.Dsl.KindRedHalted
