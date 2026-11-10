/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost

/-!
# Sanitized `simFig8` Oracle and Game-Loop `.eval` Theorem

Defines the read-time-sanitized query implementation `simFig8OracleSan` and adversary wrapper
`simFig8ClampSan`, and proves that `simFig8ProgOfStep` evaluates to `simFig8ClampSan` under any
preserved simulator invariant.
-/

@[expose] public section

set_option autoImplicit false

open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore (semHandleHookDedupS semHandleHookDedupS_preserves_sC_inv)

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle

open OracleSpec OracleComp
open ReductionDsl (Ty Comp CostedReduction handlerImpl atomicSessionOps e2eSessionCodec GhostStT
  fig8SmIface smQT smRT)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C Fig8Comp SimCStateBounded SimCStateInv
  makesAtMostQueriesDF_iff_isGameQuery)
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState initSimC)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState Params)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes paramsV1)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (simFullT simFullDec simFullDec_simFullEnc simFig8ProgOfStep simFig8InitC simFig8FinishC
   simFig8InitC_eval simFig8InitImpl simCStateInv_initSimC fig8IdSemHook)

/-- Sanitized semantic query implementation for `simFig8`. -/
def simFig8OracleSan {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ) :
    QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes)
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ))
  | .inl n => StateT.lift
    (query (spec := unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl n))
  | .inr t => StateT.mk fun sC =>
    Prod.map id Prod.fst <$>
      semHandleHookDedupS P Dh encPt encT decT lam T Kc Bsk (fig8IdSemHook (PQC := PQC) none)
        qep B t sC ()

/-- Sanitized counterpart of `simFig8ClampTG`. -/
def simFig8ClampSan {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes) :
    CryptoGames.SM.Adversary (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt) :=
  show Fig8Comp Pt ℓ Bool from do
    let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
    let sC₀ := initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
    (simulateQ (simFig8OracleSan P Dh encPt encT decT lam qep B T Kc Bsk) A).run' sC₀

/-- Sim-only invariant used by atomic `simFig8` steps: tight SPQR states. -/
def SanExtra {ℓ : ℕ} {Pt : Type} (C : Crypto) (K : MlKem)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) : Prop :=
  ∀ Q, CryptoVerification.SpqrV1Sync.SendTotal.TopStateTight C.F K (sC.base.pq Q)

/-- Game-loop `.eval` theorem for `simFig8ProgOfStep` against `simFig8ClampSan`. -/
theorem simFig8ProgOfStep_eval_san {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt]
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (L qep B T Kc Bsk : ℕ) (hℓ : ℓ < 10 ^ 6)
    (Extra : LibsignalToModularSchemeSimState Bytes Pt ℓ → Prop)
    (hExtra_init : ∀ pqrKey : BitVec 256,
      Extra (initSimC ((paramsV1 C K idA idB).spqr.init .a2b pqrKey)
        ((paramsV1 C K idA idB).spqr.init .b2a pqrKey)))
    (hExtra_step : ∀ t (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ), Extra sC →
      ∀ x ∈ support ((simFig8OracleSan (paramsV1 C K idA idB) Dh encPt encT decT lam
          qep B T Kc Bsk (.inr t)).run sC), Extra x.2)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep : ∀ t (s_raw : (simFullT ℓ Pt).denote),
      SimCStateBounded L (simFullDec s_raw) →
      Extra (simFullDec s_raw) →
      (Prod.map id (simFullDec) <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) step (.inr t)).run s_raw)) =
      ((simFig8OracleSan (paramsV1 C K idA idB) Dh encPt encT decT lam qep B T Kc Bsk
        (.inr t)).run (simFullDec s_raw)))
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (q : ℕ) (hq : CryptoGames.SM.MakesAtMostQueries A q) (hqL : q ≤ L) :
    (simFig8ProgOfStep C K Dh encPt encT decT lam step).eval (fun _ => A) () =
      simFig8ClampSan (paramsV1 C K idA idB) ℓ Dh encPt encT decT lam qep B T Kc Bsk A := by
  have hq' := (CryptoGames.Ratchet.LibsignalSim.makesAtMostQueries_iff_isGameQuery A q).mp hq
  let P := paramsV1 C K idA idB
  unfold simFig8ProgOfStep
  simp only [hℓ, ↓reduceDIte]
  set prog : CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (fig8SmIface ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) .unit .unit .bool .bool :=
    { σ := simFullT ℓ Pt
      init := simFig8InitC C K Dh encPt encT decT lam
      handle := step
      finish := simFig8FinishC C K Dh encPt encT decT lam }
  have hinit_eval :
      (Prod.map id (simFullDec (ℓ := ℓ) (Pt := Pt)) <$>
        prog.init.eval (.cons () .nil)) =
      (do
        let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
        return ((), initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) := by
    dsimp only [prog]
    rw [simFig8InitC_eval, Functor.map_map]
    unfold simFig8InitImpl
    rw [map_bind]
    refine bind_congr fun pqrKey => ?_
    rw [map_pure]
    simp only [Prod.map, id_eq, simFullDec_simFullEnc]
    rfl
  have hinit_inv :
      ∀ r ∈ support (prog.init.eval (.cons () .nil)),
        SimCStateInv L q (simFullDec (ℓ := ℓ) (Pt := Pt) r.2) ∧
          Extra (simFullDec (ℓ := ℓ) (Pt := Pt) r.2) := by
    rintro ⟨u₀, s_raw⟩ hr
    dsimp only [prog] at hr
    rw [simFig8InitC_eval, support_map, Set.mem_image] at hr
    obtain ⟨⟨_, sC₀⟩, hs, hEq₀⟩ := hr
    dsimp only [Prod.map, id_eq] at hEq₀
    injection hEq₀ with _ hs_raw
    rw [← hs_raw, simFullDec_simFullEnc]
    unfold simFig8InitImpl at hs
    rw [mem_support_bind_iff] at hs
    obtain ⟨pqrKey, -, hs⟩ := hs
    rw [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hs
    rcases hs with ⟨_, rfl⟩
    exact ⟨simCStateInv_initSimC hqL _ _, hExtra_init pqrKey⟩
  have habs := prog.eval_eq_simulateQ_of_abs
    (simFullDec (ℓ := ℓ) (Pt := Pt))
    (fun m s_raw => SimCStateInv L m (simFullDec (ℓ := ℓ) (Pt := Pt) s_raw) ∧
      Extra (simFullDec (ℓ := ℓ) (Pt := Pt) s_raw))
    (fun _ => do
      let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
      return ((), initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)))
    (simFig8OracleSan P Dh encPt encT decT lam qep B T Kc Bsk)
    (fun _ b => pure b)
    q ()
    hinit_eval
    hinit_inv
    (fun _ _ => rfl)
    (fun m t s_raw hInv => by
      have heq := hstep t s_raw hInv.1.toBounded hInv.2
      refine ⟨heq, ?_⟩
      rintro ⟨rr, s_raw'⟩ hmem
      have hmem' : (rr, simFullDec s_raw') ∈
          support ((simFig8OracleSan P Dh encPt encT decT lam qep B T Kc Bsk (.inr t)).run
            (simFullDec s_raw)) := by
        rw [← heq, support_map, Set.mem_image]
        exact ⟨(rr, s_raw'), hmem, rfl⟩
      refine ⟨?_, hExtra_step t _ hInv.2 (rr, simFullDec s_raw') hmem'⟩
      dsimp only [simFig8OracleSan, StateT.run, StateT.mk] at hmem'
      rw [support_map, Set.mem_image] at hmem'
      obtain ⟨⟨rr₀, sC', u'⟩, hsem, hEq⟩ := hmem'
      dsimp only [Prod.map, id_eq] at hEq
      injection hEq with _ hsC'
      change SimCStateInv L m (simFullDec s_raw')
      rw [← hsC']
      exact semHandleHookDedupS_preserves_sC_inv P Dh encPt encT decT lam T Kc Bsk
          (fig8IdSemHook (PQC := BitVec 512) none) L m qep B t
          (simFullDec s_raw) () hInv.1 (rr₀, sC', u') hsem)
    (fun _ _ _ => rfl)
    (fun _ hle hInv => ⟨hInv.1.mono hle, hInv.2⟩)
    (fun _ => A)
    (fun _ => hq')
  rw [habs]
  dsimp only [simFig8ClampSan, P]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun pqrKey => ?_
  rw [StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def]

end Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle
