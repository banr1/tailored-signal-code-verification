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
public import Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge -- proof-setup: allow-public-import
public import Computational.Proofs.LibsignalCli.MainHaltedPrefixCore -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge -- proof-setup: allow-public-import
public import Computational.Specifications.Reductions.ReductionDsl.AtomicOps
public import Computational.Specifications.Reductions.ReductionDsl.TargetCodecs

/-!
# Single-Argument `e2eOps` to `atomicE2EOps` Lifters

Provides single-argument expression and coin-only computation lifters (`appLiftE`, `appLiftC`)
from `e2eOps` into `atomicE2EOps`, together with atomic game-state and SM-response codecs for
`HaltedDrSessionSim`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.HaltedDrSessionSimAux

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp UniformSamplerTag
  atomicSig atomicE2EOps atomicBaseSamplers AtomicBaseUnif
  AtomicPureOp AtomicCurveCheckOp AtomicSymOp AtomicSpqrKemOp AtomicPqxdhOp
  B U8 U32 U64 BV256 BV512 GhostStT PlainT recvResultT recvResultEnc smQT smRT
  partyToBool boolToParty bytesToWordLE spqrMsgPayloadSuffix bits iterM)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (RecvResult GameState)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.Ratchet (keyToBytesVec32)
open CryptoGames.LibsignalSession (Crypto PublicKey GhostState ShaCompress)
open CryptoVerification.LibsignalSpqrV1 (MlKem V1State coinBytes coinBytes_length)
open CryptoVerification.E2E (Bytes BHE2EDrvState SampledSessionKey)
open CryptoVerification.E2E.Costed (E2EPureOp E2ECurveCheckOp E2ECryptoOp E2EUnifBase
  e2eSig e2eOps e2eSamplers)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
  (liftSort liftTy liftCtx liftVal liftVal_heq liftVar liftEnv liftEnv_get wk1Expr wk1Comp)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge
  (KemFailTrackState KemFailSessionTrack initKemFailTrack initKemFailSessionTrack
   stepKemFailSend stepKemFailDeliver)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (stepAIface)
open Computational.Proofs.E2E.Dsl.HaltedDrSessionLifter
  (liftE2EExpr liftE2EExpr_cost liftE2EExpr_size liftE2EExpr_eval
   emptyTargetE2EIface liftE2ECoinComp liftE2ECoinComp_queries_zero
   liftE2ECoinComp_cost liftE2ECoinComp_size liftE2ECoinComp_eval_prob)
open Computational.Proofs.E2E.Dsl.HaltedDrTrackerDsl
  (kemTrackT honestWireEntryT sessHTy prependHonestWireAtomicE)



section SingleArgLifting

open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore (SessionHaltTracker)
open CryptoVerification.E2E (SampledSessionKey BHE2ESmResp bhUnpackSmResp)
open _root_.ReductionDsl (smRT smRdec recvResultDec)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
  (renExpr renComp wk1Ren wk1Expr wk1Comp wk1Expr_cost wk1Expr_eval
   wk1Comp_queries wk1Comp_cost wk1Comp_eval)

/-- `SessionHaltTracker` instantiating `MainHaltedPrefixCore` with `KemFailSessionTrack C.F Bytes`. -/
@[expose] def kemFailSessionTracker {ℓ : ℕ} (C : Crypto) (K : MlKem) :
    SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes
      SampledSessionKey (KemFailSessionTrack C.F Bytes) where
  init k := initKemFailSessionTrack C.F Bytes k.2.2
  onSend _ P coins st :=
    let tr' := stepKemFailSend C.F K st.1 P coins
    (tr'.cand.isSome,
     ({ st.1 with cand := tr'.cand }, st.2),
     fun ct => (tr', (ct, P) :: st.2))
  onDeliver _ Q w res st :=
    let j? := st.2.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other)
    match res, j? with
    | some (.accepted _ _ _), some j => (stepKemFailDeliver C.F K st.1 Q j, st.2)
    | _, _ => st

@[simp] theorem kemFailSessionTracker_init {ℓ : ℕ} (C : Crypto) (K : MlKem)
    (k : SampledSessionKey) :
    (kemFailSessionTracker (ℓ := ℓ) C K).init k =
      initKemFailSessionTrack C.F Bytes k.2.2 :=
  rfl

@[expose, reducible] def gsAtomicTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  liftTy (Computational.Proofs.E2E.Dsl.M2Interfaces.e2eGsTy ℓ)

@[expose, reducible] def gsAtomicEnc {ℓ : ℕ} {Pt : Type}
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) : (gsAtomicTy ℓ Pt).denote :=
  liftVal (Pt := Pt) (Computational.Proofs.E2E.Dsl.M2Interfaces.e2eGsEnc gs)

@[expose] def smRWireAtomicE {ℓ : ℕ} {Pt : Type} {O : Ops (atomicSig ℓ Pt)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (wE : Expr O Γ (.opt (B 32))) : Expr O Γ (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) :=
  .pair wE (.pair .none .none)

@[expose] def emptyAtomicSmRespE {ℓ : ℕ} {Pt : Type} {O : Ops (atomicSig ℓ Pt)}
    {Γ : List (Ty (atomicSig ℓ Pt))} : Expr O Γ (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) :=
  .pair .none (.pair .none .none)

theorem prependHonestWireAtomicE_eval {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (trOutE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (kemTrackT ℓ Pt))
    (hwE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.list (honestWireEntryT ℓ Pt)))
    (wE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (B 32))
    (pBE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool) (ρ : Env Γ) :
    (prependHonestWireAtomicE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      trOutE hwE wE pBE).eval ρ =
      (trOutE.eval ρ, (wE.eval ρ, pBE.eval ρ) :: hwE.eval ρ) :=
  rfl

@[expose, reducible] def packAtomicSmRespEnc {ℓ : ℕ} {Pt : Type} (br : BHE2ESmResp ℓ) :
    (smRT (ℓ := ℓ) (Pt := Pt) (_root_.ReductionDsl.GhostStT (ℓ := ℓ) (Pt := Pt))).denote :=
  (br.1, (br.2.1.map recvResultEnc, br.2.2))

theorem liftVal_packSmRespEnc_eq {ℓ : ℕ} {Pt : Type} (br : BHE2ESmResp ℓ) :
    liftVal (Pt := Pt) (Computational.Proofs.E2E.Dsl.M3Interfaces.packSmRespEnc br) =
      packAtomicSmRespEnc (Pt := Pt) br := by
  rcases br with ⟨w, rr?, st?⟩
  rcases rr? with _ | rr
  · cases w <;> cases st? <;> rfl
  · rcases rr with _ | ⟨t, i, m?⟩
    · cases w <;> cases st? <;> rfl
    · cases m? <;> cases w <;> cases st? <;> rfl

theorem liftVal_smQenc_eq {ℓ : ℕ} {Pt : Type}
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    liftVal (Pt := Pt) (CryptoVerification.E2E.Costed.smQenc (ℓ := ℓ) sq) =
      _root_.ReductionDsl.smQenc (ℓ := ℓ) (Pt := Pt) sq := by
  rcases sq with (((⟨_, _, r⟩ | ⟨_, _, _, r⟩) | _) | _) | _
  · cases r <;> rfl
  · cases r <;> rfl
  · rfl
  · rfl
  · rfl

theorem liftVal_smRenc_eq {ℓ : ℕ} {Pt : Type}
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (r : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq) :
    liftVal (Pt := Pt)
        (Computational.Proofs.E2E.Dsl.M2Interfaces.smRenc
          (stT := CryptoVerification.E2E.Costed.GhostStT (ℓ := ℓ)) id sq r) =
      packAtomicSmRespEnc (Pt := Pt) (CryptoVerification.E2E.bhPackSmResp sq r) := by
  rcases sq with (((_ | _) | _) | _) | _
  · cases r <;> rfl
  · cases r <;> rfl
  · rcases r with _ | rr
    · rfl
    · rcases rr with _ | ⟨t, i, m?⟩
      · rfl
      · cases m? <;> rfl
  · rcases r with _ | rr
    · rfl
    · rcases rr with _ | ⟨t, i, m?⟩
      · rfl
      · cases m? <;> rfl
  · cases r <;> rfl

@[simp] theorem renExpr_size {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)} {t : Ty S₀}
    (e : Expr O Γ t) :
    ∀ {Δ : List (Ty S₀)} (f : ∀ {τ}, Var Γ τ → Var Δ τ),
      (renExpr f e).size = e.size := by
  induction e <;> intro Δ f <;> simp only [renExpr, Expr.size, *]

@[simp] theorem wk1Expr_size {S₀ : Sig} {O : Ops S₀} {a b : Ty S₀} {Γ : List (Ty S₀)}
    (e : Expr O [a] b) :
    (wk1Expr (Γ := Γ) e).size = e.size :=
  renExpr_size e wk1Ren

@[simp] theorem renComp_size {S₀ : Sig} {O : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {Γ : List (Ty S₀)} {t : Ty S₀} (c : Comp O I₀ Γ t) :
    ∀ {Δ : List (Ty S₀)} (f : ∀ {τ}, Var Γ τ → Var Δ τ),
      (renComp f c).size = c.size := by
  induction c <;> intro Δ f <;> simp only [renComp, Comp.size, renExpr_size, *]

@[simp] theorem wk1Comp_size {S₀ : Sig} {O : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {a b : Ty S₀} {Γ : List (Ty S₀)} (c : Comp O I₀ [a] b) :
    (wk1Comp (Γ := Γ) c).size = c.size :=
  renComp_size c wk1Ren

/-- Applies a single-argument `e2eOps` expression to an `atomicE2EOps` argument in context `Γ`. -/
@[expose] def appLiftE {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {a b : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (f : Expr (e2eOps ℓ P C K decT encT) [a] b)
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) a)) :
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) b) :=
  .letE argE (wk1Expr (liftE2EExpr (Pt := Pt) f))

theorem appLiftE_cost {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {a b : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (f : Expr (e2eOps ℓ P C K decT encT) [a] b)
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) a)) :
    (appLiftE f argE).cost = argE.cost + f.cost + 1 := by
  simp [appLiftE, Expr.cost, wk1Expr_cost, liftE2EExpr_cost]

theorem appLiftE_size {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {a b : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (f : Expr (e2eOps ℓ P C K decT encT) [a] b)
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) a)) :
    (appLiftE f argE).size = argE.size + f.size + 1 := by
  simp [appLiftE, Expr.size, wk1Expr_size, liftE2EExpr_size]

theorem appLiftE_eval {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {a b : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (f : Expr (e2eOps ℓ P C K decT encT) [a] b)
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) a))
    (ρ : Env Γ) (x : a.denote) (harg : argE.eval ρ = liftVal (Pt := Pt) x) :
    (appLiftE f argE).eval ρ = liftVal (Pt := Pt) (f.eval (.cons x .nil)) := by
  simp only [appLiftE, Expr.eval, harg, wk1Expr_eval]
  exact liftE2EExpr_eval f (.cons x .nil)

/-- Applies a single-argument coin-only `e2eOps` computation to an `atomicE2EOps` argument in context `Γ`. -/
@[expose] def appLiftC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt)
    {a b : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (c : Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ (emptyTargetE2EIface ℓ)) [a] b)
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) a)) :
    Comp (atomicE2EOps ℓ P C K decT encT) I Γ (liftTy (Pt := Pt) b) :=
  .bind (.ret argE) (wk1Comp (liftE2ECoinComp (Pt := Pt) I hsmp c))

@[simp] theorem appLiftC_queries_zero {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt)
    {a b : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (c : Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ (emptyTargetE2EIface ℓ)) [a] b)
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) a))
    (w : I.Tag → ℕ) :
    (appLiftC I hsmp c argE).queries w (fun _ => 0) = 0 := by
  simp [appLiftC, Comp.queries, wk1Comp_queries, liftE2ECoinComp_queries_zero]

theorem appLiftC_cost {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt)
    {a b : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (c : Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ (emptyTargetE2EIface ℓ)) [a] b)
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) a)) :
    (appLiftC I hsmp c argE).cost ≤ argE.cost + c.cost + 4 := by
  simp only [appLiftC, Comp.cost, wk1Comp_cost, liftE2ECoinComp_cost]
  omega

theorem appLiftC_size {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt)
    {a b : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (c : Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ (emptyTargetE2EIface ℓ)) [a] b)
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) a)) :
    (appLiftC I hsmp c argE).size ≤ argE.size + c.size + 4 := by
  simp only [appLiftC, Comp.size, wk1Comp_size, liftE2ECoinComp_size]
  omega

theorem appLiftC_eval_prob {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt)
    {a b : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (c : Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ (emptyTargetE2EIface ℓ)) [a] b)
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) a))
    (ρ : Env Γ) (x : a.denote) (m : ProbComp b.denote)
    (harg : argE.eval ρ = liftVal (Pt := Pt) x)
    (hc : c.eval (.cons x .nil) = (stepAIface ℓ (emptyTargetE2EIface ℓ)).liftP m) :
    (appLiftC I hsmp c argE).eval ρ = I.liftP (liftVal (Pt := Pt) <$> m) := by
  simp only [appLiftC, Comp.eval, pure_bind, harg, wk1Comp_eval]
  exact liftE2ECoinComp_eval_prob I hsmp c (.cons x .nil) m hc

end SingleArgLifting

end Computational.Proofs.E2E.Dsl.HaltedDrSessionSimAux
