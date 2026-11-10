/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.DrSessionSimHooks
public import Computational.Proofs.E2E.Dsl.DrSessionSimSend
public import Computational.Proofs.E2E.Dsl.DrSessionSimRecv
public import Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping
public import Computational.Proofs.E2E.Dsl.SmReachInv
public import Computational.Proofs.E2E.Dsl.M2Interfaces

/-!
# `ReductionDsl` Step Simulator for `SM.oracleImplR`

Combines the send simulator, receive simulator, `O(q)` `SM.GameState` bookkeeping, and
reachability invariant into a single `ReductionDsl.Comp` handler `drOracleStepC` simulating all
five arms of `SM.oracleImplR` on `sessionSchemeFixedSpk`. Establishes exact evaluation agreement,
zero non-coin target queries, concrete step-cost bounds, and the `DrSessionSimIface` instance.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.DrSessionSim

open OracleSpec OracleComp
open ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp UniformSamplerTag bits)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (Pos Record RecvResult GameState inWindow samIfNec transmitImpl
  challImpl transmitR challR deliverR injectR corrR oracleImplR partyEnc posTy posEnc orE isSomeE
  otherE pGet letE_eval ite_eval pair_eval some_eval orE_eval isSomeE_eval otherE_eval pGet_eval)
open CryptoGames.Ratchet.LibsignalInst (ratchetKeyAdmissible configR1OnCurve)
open CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey GhostState)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes paramsIdsWithSpqr sessionSchemeFixedSpk configRefuseEarlyBobCorr)
open CryptoVerification.E2E.Costed (e2eSig B BV256 BV512 PlainT GhostStT recvResultT recvResultEnc
  partyToBool smQT smQenc smRT smRdec E2EUnifBase e2eSamplers e2eOps
  e2eKeyIndTargetIface e2eSessionTargetIface e2eAdapterIface)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (stepAIface)
open Computational.Proofs.E2E.Dsl.M2Interfaces (DrSessionSimIface)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (PartyReachInv)
open Computational.Proofs.E2E.Dsl.SmReachInv (dedupComp GameReachInv SmListBounded SmReachBounded)
open Computational.Proofs.E2E.Dsl.DrSessionSimHooks (SpqrDslHooks)
open Computational.Proofs.E2E.Dsl.DrSessionSimSend (drSendC drSendC_queries drSendC_cost
  drSendC_eval_params drSendC_eval params_send_wire_length_le)
open Computational.Proofs.E2E.Dsl.DrSessionSimRecv (drRecvOutT drReceiveC drReceiveC_queries
  drReceiveC_cost drReceiveC_eval_core drReceiveC_eval_params drReceiveC_eval)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (bytesEqE wrapWhisperWireE wrapPreKeyWireE
  parsePreKeyWireE partneredInnerBytesE wireInnerBytesE decEncCheckE ratchetKeyAdmissibleE
  eval_ratchetKeyAdmissibleE cost_ratchetKeyAdmissibleE partyToBool_eq_partyEnc smRenc smRdec_smRenc
  smRdec_smRenc_id smRenc_id_eq_bhPackSmResp recvResultRejE recvResultAccE smRWireE smRRecvE
  smRCorrE eval_recvResultRejE cost_recvResultRejE eval_recvResultAccE cost_recvResultAccE
  eval_smRWireE cost_smRWireE eval_smRRecvE cost_smRRecvE eval_smRCorrE cost_smRCorrE
  e2eRecTy e2eRecEncWith e2eRecPos e2eGsTy e2eGsEnc e2eGsDec e2eGsSt e2eGsB e2eGsWin e2eGsEpoch
  e2eGsIdx e2eInitGsE eval_e2eInitGsE cost_e2eInitGsE_le e2eGsSetWin eval_e2eGsSetWin
  cost_e2eGsSetWin_le e2eSafeChE eval_e2eSafeChE cost_e2eSafeChE_le e2eSafeInjE eval_e2eSafeInjE
  cost_e2eSafeInjE_le e2eEpMgmtE eval_e2eEpMgmtE cost_e2eEpMgmtE_le e2eChallContainsE
  eval_e2eChallContainsE cost_e2eChallContainsE_le e2eRecordE eval_e2eRecordE cost_e2eRecordE_le
  e2eAcceptE eval_e2eAcceptE cost_e2eAcceptE_le e2eTrivialE eval_e2eTrivialE cost_e2eTrivialE_le
  e2eCorrAllowedE eval_e2eCorrAllowedE cost_e2eCorrAllowedE_le e2eAfterCorrAllowedE
  eval_e2eAfterCorrAllowedE cost_e2eAfterCorrAllowedE_le e2eInWindowE eval_e2eInWindowE
  cost_e2eInWindowE_le e2eSendOKE eval_e2eSendOKE cost_e2eSendOKE_le e2eCorrOKE eval_e2eCorrOKE
  cost_e2eCorrOKE_le e2eInTransitE eval_e2eInTransitE cost_e2eInTransitE_le)

export Computational.Proofs.E2E.Dsl.DrSessionSimHooks (SpqrDslHooks)
export Computational.Proofs.E2E.Dsl.DrSessionSimSend
  (drSendC drSendC_queries drSendC_cost drSendC_eval_params drSendC_eval)
export Computational.Proofs.E2E.Dsl.DrSessionSimSend (params_send_wire_length_le)
export Computational.Proofs.E2E.Dsl.DrSessionSimRecv
  (drRecvOutT drReceiveC drReceiveC_queries drReceiveC_cost drReceiveC_eval_core)
export Computational.Proofs.E2E.Dsl.DrSessionSimRecv (drReceiveC_eval_params drReceiveC_eval)
export Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping
  (bytesEqE wrapWhisperWireE wrapPreKeyWireE parsePreKeyWireE partneredInnerBytesE)
export Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping
  (wireInnerBytesE decEncCheckE ratchetKeyAdmissibleE smRenc smRdec_smRenc)
export Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping
  (smRdec_smRenc_id smRenc_id_eq_bhPackSmResp e2eGsTy e2eGsEnc e2eGsDec)
export Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping
  (e2eInitGsE eval_e2eInitGsE cost_e2eInitGsE_le)

/-! ## Coin-sampler hooks -/

/-- Coin-drawing hooks over `I : Iface (e2eSig ℓ) T` providing uniform 256-bit and 512-bit
randomness draws with zero non-coin query count and bounded static cost. -/
structure E2ECoinSamplers (ℓ : ℕ) {Pt : Type} (P : SignalPqxdh.Primitives) (C : Crypto)
    (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) where
  draw256 : ∀ {Γ : List (Ty (e2eSig ℓ))},
    Comp (e2eOps ℓ P C K decT encT) I Γ BV256
  draw512 : ∀ {Γ : List (Ty (e2eSig ℓ))},
    Comp (e2eOps ℓ P C K decT encT) I Γ BV512
  draw256_cost : ∀ {Γ : List (Ty (e2eSig ℓ))},
    (draw256 (Γ := Γ)).cost ≤ 4
  draw512_cost : ∀ {Γ : List (Ty (e2eSig ℓ))},
    (draw512 (Γ := Γ)).cost ≤ 4
  draw256_queries_zero : ∀ {Γ : List (Ty (e2eSig ℓ))} (w : I.Tag → ℕ),
    (draw256 (Γ := Γ)).queries w (fun _ => 0) = 0
  draw512_queries_zero : ∀ {Γ : List (Ty (e2eSig ℓ))} (w : I.Tag → ℕ),
    (draw512 (Γ := Γ)).queries w (fun _ => 0) = 0
  draw256_queries_le : ∀ {Γ : List (Ty (e2eSig ℓ))} (w : I.Tag → ℕ)
    (ws : I.smp.Samp → ℕ) (m : ℕ),
    (∀ s, ws s ≤ m) → (draw256 (Γ := Γ)).queries w ws ≤ m
  draw512_queries_le : ∀ {Γ : List (Ty (e2eSig ℓ))} (w : I.Tag → ℕ)
    (ws : I.smp.Samp → ℕ) (m : ℕ),
    (∀ s, ws s ≤ m) → (draw512 (Γ := Γ)).queries w ws ≤ m
  draw256_eval : ∀ {Γ : List (Ty (e2eSig ℓ))} (ρ : Env Γ),
    (draw256 (Γ := Γ)).eval ρ = I.liftP ($ᵗ (BitVec 256))
  draw512_eval : ∀ {Γ : List (Ty (e2eSig ℓ))} (ρ : Env Γ),
    (draw512 (Γ := Γ)).eval ρ = I.liftP ($ᵗ (BitVec 512))

def mkE2ECoinSamplers {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1))) (uCost : ℕ)
    (Tag : Type) (dom cod : Tag → Ty (e2eSig ℓ))
    (enc : (g : Tag) → (dom g).denote → ι)
    (dec : (g : Tag) → (x : (dom g).denote) → T (enc g x) → (cod g).denote)
    (qCost : Tag → ℕ) :
    E2ECoinSamplers ℓ P C K decT encT
      ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, e2eSamplers ℓ⟩ :=
  let I₀ : Iface (e2eSig ℓ) T := ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, e2eSamplers ℓ⟩
  { draw256 := fun {_} =>
      Comp.sample (I := I₀) (UniformSamplerTag.base E2EUnifBase.bv256) .unit
    draw512 := fun {_} =>
      Comp.sample (I := I₀) (UniformSamplerTag.base E2EUnifBase.bv512) .unit
    draw256_cost := fun {_} => by simp [Comp.cost, Expr.cost, E2EUnifBase.cost]
    draw512_cost := fun {_} => by simp [Comp.cost, Expr.cost, E2EUnifBase.cost]
    draw256_queries_zero := fun {_} _ => rfl
    draw512_queries_zero := fun {_} _ => rfl
    draw256_queries_le := fun {_} _ _ _ hm => hm (UniformSamplerTag.base E2EUnifBase.bv256)
    draw512_queries_le := fun {_} _ _ _ hm => hm (UniformSamplerTag.base E2EUnifBase.bv512)
    draw256_eval := fun {_} _ => by dsimp only [Comp.eval]; congr 1
    draw512_eval := fun {_} _ => by dsimp only [Comp.eval]; congr 1 }

def E2ECoinSamplers.ofSmpEq {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    (hsmp : I.smp = e2eSamplers ℓ) : E2ECoinSamplers ℓ P C K decT encT I := by
  rcases I with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at hsmp
  subst hsmp
  exact mkE2ECoinSamplers fwdU uCost Tag dom cod enc dec qCost

def e2eKeyIndCoinSamplers (SetupS : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    E2ECoinSamplers ℓ P C K decT encT (e2eKeyIndTargetIface SetupS ℓ) :=
  E2ECoinSamplers.ofSmpEq rfl

def e2eSessionCoinSamplers (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    E2ECoinSamplers ℓ P C K decT encT (e2eSessionTargetIface ℓ) :=
  E2ECoinSamplers.ofSmpEq rfl

def e2eAdapterCoinSamplers (SetupS : SignalPqxdh.Setup) (ℓ : ℕ) {Ctl : Type}
    (mkStart : SignalPqxdh.SessionId SetupS → Ctl) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    E2ECoinSamplers ℓ P C K decT encT (e2eAdapterIface SetupS ℓ mkStart) :=
  E2ECoinSamplers.ofSmpEq rfl

def e2eStepACoinSamplers (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) :
    E2ECoinSamplers ℓ P C K decT encT (stepAIface ℓ I₀) :=
  E2ECoinSamplers.ofSmpEq rfl

/-! ## Arm handlers and `drOracleStepC` -/

section StepSimulator

variable {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "S" => e2eSig ℓ
local notation "OO" => e2eOps ℓ P C K decT encT

private theorem liftP_pure {ι : Type} {T : OracleSpec ι} (I : Iface S T)
    {α : Type} (a : α) : I.liftP (pure a) = pure a := by
  simp [Iface.liftP]

private theorem liftP_bind {ι : Type} {T : OracleSpec ι} (I : Iface S T)
    {α β : Type} (p : ProbComp α) (k : α → ProbComp β) :
    I.liftP (p >>= k) = (I.liftP p >>= fun a => I.liftP (k a)) := by
  simp [Iface.liftP]

private theorem liftP_map {ι : Type} {T : OracleSpec ι} (I : Iface S T)
    {α β : Type} (f : α → β) (p : ProbComp α) :
    I.liftP (f <$> p) = f <$> I.liftP p := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp, liftP_bind]
  refine bind_congr fun a => ?_
  exact liftP_pure I (f a)

private theorem not_partyEnc (p : Party) : (!partyEnc p) = partyEnc p.other := by
  cases p <;> rfl

private theorem epMgmt_preserve_fields {Δ qep : ℕ}
    {st s1 : GameState (GhostState Bytes) (Plain ℓ) Bytes} {party : Party} {bad : Bool}
    (hep : st.epMgmt Δ qep party bad = some s1) :
    s1.st = st.st ∧ s1.trans = st.trans ∧ s1.comp = st.comp := by
  unfold GameState.epMgmt at hep
  by_cases hs : party.sendsIn (st.epoch party + 1) = true
  · simp only [hs, ↓reduceIte] at hep
    by_cases hq : qep < st.epoch party + 1
    · simp [hq] at hep
    · simp only [hq, ↓reduceIte] at hep
      by_cases hb : (bad && !st.safeCh Δ party) = true
      · simp only [hb, ↓reduceIte, Option.some.injEq] at hep
        subst hep
        exact ⟨rfl, rfl, rfl⟩
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hep
        subst hep
        exact ⟨rfl, rfl, rfl⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep
    by_cases hq : qep < st.epoch party
    · simp [hq] at hep
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      exact ⟨rfl, rfl, rfl⟩

/-- `SM.samIfNec` on `Option (BitVec 512)`: draws fresh 512-bit coins with `bad = false` on `none`
and returns `(r, true)` on `some r`. -/
def e2eSamIfNec512C {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I) {Γ : List (Ty S)}
    (optR : Expr OO Γ (.opt BV512)) : Comp OO I Γ (.prod BV512 .bool) :=
  .caseOpt optR
    (.bind coins.draw512 (.ret (.pair .v0 (.bool false))))
    (.ret (.pair .v0 (.bool true)))

theorem e2eSamIfNec512C_queries_zero {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I) {Γ : List (Ty S)}
    (optR : Expr OO Γ (.opt BV512)) (w : I.Tag → ℕ) :
    (e2eSamIfNec512C coins optR).queries w (fun _ => 0) = 0 := by
  simp [e2eSamIfNec512C, Comp.queries, coins.draw512_queries_zero]

theorem e2eSamIfNec512C_queries_le {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I) {Γ : List (Ty S)}
    (optR : Expr OO Γ (.opt BV512)) (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (m : ℕ)
    (hm : ∀ s, ws s ≤ m) :
    (e2eSamIfNec512C coins optR).queries w ws ≤ m := by
  have hd := coins.draw512_queries_le (Γ := Γ) w ws m hm
  simp only [e2eSamIfNec512C, Comp.queries]
  omega

theorem e2eSamIfNec512C_cost {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I) {Γ : List (Ty S)}
    (optR : Expr OO Γ (.opt BV512)) :
    (e2eSamIfNec512C coins optR).cost ≤ optR.cost + 12 := by
  have hd := coins.draw512_cost (Γ := Γ)
  simp only [e2eSamIfNec512C, Comp.cost, Expr.cost, Expr.v0] at hd ⊢
  omega

theorem e2eSamIfNec512C_eval {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I) {Γ : List (Ty S)}
    (optR : Expr OO Γ (.opt BV512)) (ρ : Env Γ) :
    (e2eSamIfNec512C coins optR).eval ρ = I.liftP (samIfNec (optR.eval ρ)) := by
  simp only [e2eSamIfNec512C, Comp.eval]
  rcases optR.eval ρ with _ | r
  · simp [samIfNec, coins.draw512_eval, Iface.liftP, Expr.eval, Expr.v0]
  · simp [samIfNec, Iface.liftP, Expr.eval, Expr.v0]

def drTrArmC (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (q Δ qep : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (trArg : Expr OO Γ (.prod .bool (.prod PlainT (.opt BV512)))) :
    Comp OO I Γ (.prod (smRT GhostStT) (e2eGsTy ℓ)) :=
  .bind (.ret (.pair gsE trArg))
    (.ite (orE (.not (e2eSendOKE (.fst .v0) (.fst (.snd .v0)))) (e2eGsWin (.fst .v0)))
      (.ret (.pair (smRWireE .none) (.fst .v0)))
      (.bind (e2eSamIfNec512C coins (.snd (.snd (.snd .v0))))
        (.caseOpt (e2eEpMgmtE Δ qep (.fst .v1) (.fst (.snd .v1)) (.snd .v0))
          (.ret (.pair (smRWireE .none) (.fst .v1)))
          (.bind (drSendC hooks I
              (.pair (pGet (e2eGsSt .v0) (.fst (.snd .v2)))
                (.pair (.fst (.snd (.snd .v2))) (.fst .v1))))
            (let st' : Expr OO _ GhostStT := .fst .v0
             let ct' : Expr OO _ (B 32) := .snd .v0
             let s1 : Expr OO _ (e2eGsTy ℓ) := .v1
             let p3 : Expr OO _ .bool := .fst (.snd .v3)
             let m3 : Expr OO _ PlainT := .fst (.snd (.snd .v3))
             let posE : Expr OO _ posTy :=
               .pair p3 (.pair (pGet (e2eGsEpoch s1) p3) (.add (pGet (e2eGsIdx s1) p3) (.nat 1)))
             .ret (.pair (smRWireE (.some ct'))
               (e2eRecordE q Δ s1 p3 st' posE m3 ct' (.bool false))))))))

def drChArmC (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (q Δ qep : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (chArg : Expr OO Γ (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))) :
    Comp OO I Γ (.prod (smRT GhostStT) (e2eGsTy ℓ)) :=
  .bind (.ret (.pair gsE chArg))
    (.ite (orE (.not (e2eSendOKE (.fst .v0) (.fst (.snd .v0)))) (e2eGsWin (.fst .v0)))
      (.ret (.pair (smRWireE .none) (.fst .v0)))
      (.bind (e2eSamIfNec512C coins (.snd (.snd (.snd (.snd .v0)))))
        (.caseOpt (e2eEpMgmtE Δ qep (.fst .v1) (.fst (.snd .v1)) (.snd .v0))
          (.ret (.pair (smRWireE .none) (.fst .v1)))
          (.ite (.not (e2eSafeChE Δ .v0 (.fst (.snd .v2))))
            (.ret (.pair (smRWireE .none) (.fst .v2)))
            (let mCh2 : Expr OO _ PlainT :=
               .ite (e2eGsB (.fst .v2))
                 (.fst (.snd (.snd (.snd .v2))))
                 (.fst (.snd (.snd .v2)))
             .bind (drSendC hooks I
                 (.pair (pGet (e2eGsSt .v0) (.fst (.snd .v2)))
                   (.pair mCh2 (.fst .v1))))
               (let st' : Expr OO _ GhostStT := .fst .v0
                let ct' : Expr OO _ (B 32) := .snd .v0
                let s1 : Expr OO _ (e2eGsTy ℓ) := .v1
                let gs3 : Expr OO _ (e2eGsTy ℓ) := .fst .v3
                let p3 : Expr OO _ .bool := .fst (.snd .v3)
                let mCh3 : Expr OO _ PlainT :=
                  .ite (e2eGsB gs3)
                    (.fst (.snd (.snd (.snd .v3))))
                    (.fst (.snd (.snd .v3)))
                let posE : Expr OO _ posTy :=
                  .pair p3 (.pair (pGet (e2eGsEpoch s1) p3) (.add (pGet (e2eGsIdx s1) p3) (.nat 1)))
                .ret (.pair (smRWireE (.some ct'))
                  (e2eRecordE q Δ s1 p3 st' posE mCh3 ct' (.bool true)))))))))

def drDlArmC (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (q : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (dlArg : Expr OO Γ (.prod .bool (B 32))) :
    Comp OO I Γ (.prod (smRT GhostStT) (e2eGsTy ℓ)) :=
  .bind (.ret (.pair gsE dlArg))
    (.ite (e2eGsWin (.fst .v0))
      (.ret (.pair (smRRecvE .none) (.fst .v0)))
      (.caseOpt (e2eInTransitE q (.fst .v0) (otherE (.fst (.snd .v0))) (.snd (.snd .v0)))
        (.ret (.pair (smRRecvE .none) (.fst .v0)))
        (.bind coins.draw256
          (.bind (drReceiveC hooks I
              (.pair (pGet (e2eGsSt (.fst .v2)) (.fst (.snd .v2)))
                (.pair (.snd (.snd .v2)) .v0)))
            (.caseOpt .v0
              (.ret (.pair (smRRecvE (.some recvResultRejE)) (.fst .v3)))
              (let st' : Expr OO _ GhostStT := .fst .v0
               let t' : Expr OO _ .nat := .fst (.snd .v0)
               let i' : Expr OO _ .nat := .fst (.snd (.snd .v0))
               let m' : Expr OO _ PlainT := .snd (.snd (.snd .v0))
               let rPos : Expr OO _ posTy := e2eRecPos .v3
               let gs4 : Expr OO _ (e2eGsTy ℓ) := .fst .v4
               let p4 : Expr OO _ .bool := .fst (.snd .v4)
               let mOut : Expr OO _ (.opt PlainT) :=
                 .ite (e2eChallContainsE q gs4 rPos) .none (.some m')
               .ret (.pair (smRRecvE (.some (recvResultAccE t' i' mOut)))
                 (e2eAcceptE q gs4 p4 st' rPos))))))))

def drIjArmC (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (q Δ qep : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (ijArg : Expr OO Γ (.prod .bool (B 32))) :
    Comp OO I Γ (.prod (smRT GhostStT) (e2eGsTy ℓ)) :=
  .bind (.ret (.pair gsE ijArg))
    (let gs0 : Expr OO _ (e2eGsTy ℓ) := .fst .v0
     let p0 : Expr OO _ .bool := .fst (.snd .v0)
     let c0 : Expr OO _ (B 32) := .snd (.snd .v0)
     let refuseCond : Expr OO _ .bool :=
       orE (e2eGsWin gs0)
         (orE (isSomeE (e2eInTransitE q gs0 (otherE p0) c0))
           (orE (.not (e2eSafeInjE Δ gs0)) (.not (ratchetKeyAdmissibleE c0))))
     .ite refuseCond
       (.ret (.pair (smRRecvE .none) gs0))
       (.bind coins.draw256
         (.bind (drReceiveC hooks I
             (.pair (pGet (e2eGsSt (.fst .v1)) (.fst (.snd .v1)))
               (.pair (.snd (.snd .v1)) .v0)))
           (.caseOpt .v0
             (.ret (.pair (smRRecvE (.some recvResultRejE)) (.fst .v2)))
             (let st' : Expr OO _ GhostStT := .fst .v0
              let t' : Expr OO _ .nat := .fst (.snd .v0)
              let i' : Expr OO _ .nat := .fst (.snd (.snd .v0))
              let m' : Expr OO _ PlainT := .snd (.snd (.snd .v0))
              let gs3 : Expr OO _ (e2eGsTy ℓ) := .fst .v3
              let p3 : Expr OO _ .bool := .fst (.snd .v3)
              .ite (.lt (.nat (qep + 1)) t')
                (.ret (.pair (smRRecvE (.some recvResultRejE)) gs3))
                (let posE : Expr OO _ posTy := .pair (otherE p3) (.pair t' i')
                 .ite (e2eTrivialE q Δ gs3 posE)
                   (.ret (.pair (smRRecvE (.some (recvResultAccE t' i' (.some m'))))
                     (e2eAcceptE q gs3 p3 st' posE)))
                   (.ret (.pair (smRRecvE (.some recvResultRejE))
                     (e2eGsSetWin gs3 (.bool true))))))))))

def drCrArmC {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (q : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (crArg : Expr OO Γ .bool) :
    Comp OO I Γ (.prod (smRT GhostStT) (e2eGsTy ℓ)) :=
  .bind (.ret (.pair gsE crArg))
    (let gs0 : Expr OO _ (e2eGsTy ℓ) := .fst .v0
     let p0 : Expr OO _ .bool := .snd .v0
     let refuseCond : Expr OO _ .bool :=
       orE (e2eGsWin gs0)
         (orE (.not (e2eCorrAllowedE q gs0 p0))
           (orE (e2eInWindowE gs0 p0) (.not (e2eCorrOKE gs0 p0))))
     .ite refuseCond
       (.ret (.pair (smRCorrE .none) gs0))
       (.ret (.pair (smRCorrE (.some (pGet (e2eGsSt gs0) p0)))
         (e2eAfterCorrAllowedE gs0 p0))))

/-- Combined `ReductionDsl` step simulator for `SM.oracleImplR` over `smQT` and `e2eGsTy ℓ`. -/
def drOracleStepC (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (q Δ qep : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (qryE : Expr OO Γ smQT) :
    Comp OO I Γ (.prod (smRT GhostStT) (e2eGsTy ℓ)) :=
  .bind (.ret (.pair gsE qryE))
    (.caseSum (.snd .v0)
      (drTrArmC hooks coins q Δ qep (.fst .v1) .v0)
      (.caseSum .v0
        (drChArmC hooks coins q Δ qep (.fst .v2) .v0)
        (.caseSum .v0
          (drDlArmC hooks coins q (.fst .v3) .v0)
          (.caseSum .v0
            (drIjArmC hooks coins q Δ qep (.fst .v4) .v0)
            (drCrArmC q (.fst .v4) .v0)))))

/-! ## Static query-count bounds -/

theorem drTrArmC_queries_zero (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (q Δ qep : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (trArg : Expr OO Γ (.prod .bool (.prod PlainT (.opt BV512))))
    (w : I.Tag → ℕ) :
    (drTrArmC hooks coins q Δ qep gsE trArg).queries w (fun _ => 0) = 0 := by
  simp [drTrArmC, Comp.queries, e2eSamIfNec512C_queries_zero, drSendC_queries]

theorem drChArmC_queries_zero (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (q Δ qep : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (chArg : Expr OO Γ (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512)))))
    (w : I.Tag → ℕ) :
    (drChArmC hooks coins q Δ qep gsE chArg).queries w (fun _ => 0) = 0 := by
  simp [drChArmC, Comp.queries, e2eSamIfNec512C_queries_zero, drSendC_queries]

theorem drDlArmC_queries_zero (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (q : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (dlArg : Expr OO Γ (.prod .bool (B 32)))
    (w : I.Tag → ℕ) :
    (drDlArmC hooks coins q gsE dlArg).queries w (fun _ => 0) = 0 := by
  simp [drDlArmC, Comp.queries, coins.draw256_queries_zero, drReceiveC_queries]

theorem drIjArmC_queries_zero (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (q Δ qep : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (ijArg : Expr OO Γ (.prod .bool (B 32)))
    (w : I.Tag → ℕ) :
    (drIjArmC hooks coins q Δ qep gsE ijArg).queries w (fun _ => 0) = 0 := by
  simp [drIjArmC, Comp.queries, coins.draw256_queries_zero, drReceiveC_queries]

theorem drCrArmC_queries {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (q : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (crArg : Expr OO Γ .bool)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (drCrArmC (I := I) q gsE crArg).queries w ws = 0 := by
  simp [drCrArmC, Comp.queries]

theorem drOracleStepC_queries_zero (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (q Δ qep : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (qryE : Expr OO Γ smQT)
    (w : I.Tag → ℕ) :
    (drOracleStepC hooks coins q Δ qep gsE qryE).queries w (fun _ => 0) = 0 := by
  simp [drOracleStepC, Comp.queries, drTrArmC_queries_zero, drChArmC_queries_zero,
    drDlArmC_queries_zero, drIjArmC_queries_zero, drCrArmC_queries]

theorem drOracleStepC_queries_le (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (q Δ qep : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (qryE : Expr OO Γ smQT)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (m : ℕ)
    (hm : ∀ s, ws s ≤ m) :
    (drOracleStepC hooks coins q Δ qep gsE qryE).queries w ws ≤ m := by
  let tTop : Ty S := .prod (e2eGsTy ℓ) smQT
  let r1T : Ty S :=
    .sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
      (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool))
  let r2T : Ty S := .sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool)
  let r3T : Ty S := .sum (.prod .bool (B 32)) .bool
  have hsTr := e2eSamIfNec512C_queries_le coins
    (.snd (.snd (.snd .v0)) :
      Expr OO (.prod (e2eGsTy ℓ) (.prod .bool (.prod PlainT (.opt BV512))) ::
        .prod .bool (.prod PlainT (.opt BV512)) :: tTop :: Γ) (.opt BV512))
    w ws m hm
  have hsCh := e2eSamIfNec512C_queries_le coins
    (.snd (.snd (.snd (.snd .v0))) :
      Expr OO (.prod (e2eGsTy ℓ) (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512)))) ::
        .prod .bool (.prod PlainT (.prod PlainT (.opt BV512))) :: r1T :: tTop :: Γ) (.opt BV512))
    w ws m hm
  have hdDl := coins.draw256_queries_le
    (Γ := e2eRecTy ℓ :: .prod (e2eGsTy ℓ) (.prod .bool (B 32)) ::
      .prod .bool (B 32) :: r2T :: r1T :: tTop :: Γ) w ws m hm
  have hdIj := coins.draw256_queries_le
    (Γ := .prod (e2eGsTy ℓ) (.prod .bool (B 32)) ::
      .prod .bool (B 32) :: r3T :: r2T :: r1T :: tTop :: Γ) w ws m hm
  simp only [drOracleStepC, drTrArmC, drChArmC, drDlArmC, drIjArmC, drCrArmC_queries,
    Comp.queries, drSendC_queries, drReceiveC_queries] at hsTr hsCh hdDl hdIj ⊢
  omega

/-! ## Static cost bounds -/

theorem drTrArmC_cost (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (q Δ qep : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (trArg : Expr OO Γ (.prod .bool (.prod PlainT (.opt BV512)))) :
    (drTrArmC hooks coins q Δ qep gsE trArg).cost ≤
      gsE.cost + trArg.cost + 69000 + 10 * (ℓ / 32 + 1) + 135 * q + 2 * bits Δ + bits qep := by
  let t0 : Ty S := .prod (e2eGsTy ℓ) (.prod .bool (.prod PlainT (.opt BV512)))
  let t1 : Ty S := .prod BV512 .bool
  let tOut : Ty S := .prod GhostStT (B 32)
  have hsendOK := cost_e2eSendOKE_le (ℓ := ℓ) (O' := OO)
    (.fst .v0 : Expr OO (t0 :: Γ) (e2eGsTy ℓ)) (.fst (.snd .v0))
  have hsam := e2eSamIfNec512C_cost coins
    (.snd (.snd (.snd .v0)) : Expr OO (t0 :: Γ) (.opt BV512))
  have hep := cost_e2eEpMgmtE_le (ℓ := ℓ) (O' := OO) Δ qep
    (.fst .v1 : Expr OO (t1 :: t0 :: Γ) (e2eGsTy ℓ)) (.fst (.snd .v1)) (.snd .v0)
  have hsend := drSendC_cost hooks I
    (.pair (pGet (e2eGsSt .v0) (.fst (.snd .v2)))
      (.pair (.fst (.snd (.snd .v2))) (.fst .v1)) :
      Expr OO (e2eGsTy ℓ :: t1 :: t0 :: Γ) (.prod GhostStT (.prod PlainT BV512)))
  have hrec := cost_e2eRecordE_le (ℓ := ℓ) (O' := OO) q Δ
    (.v1 : Expr OO (tOut :: e2eGsTy ℓ :: t1 :: t0 :: Γ) (e2eGsTy ℓ))
    (.fst (.snd .v3)) (.fst .v0)
    (.pair (.fst (.snd .v3))
      (.pair (pGet (e2eGsEpoch .v1) (.fst (.snd .v3)))
        (.add (pGet (e2eGsIdx .v1) (.fst (.snd .v3))) (.nat 1))))
    (.fst (.snd (.snd .v3))) (.snd .v0) (.bool false)
  have hb1 : bits 1 = 1 := by decide
  simp only [drTrArmC, orE, pGet, e2eGsSt, e2eGsWin, e2eGsEpoch, e2eGsIdx, cost_smRWireE,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, hb1] at hsendOK hsam hep hsend hrec ⊢
  omega

theorem drChArmC_cost (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (q Δ qep : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (chArg : Expr OO Γ (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))) :
    (drChArmC hooks coins q Δ qep gsE chArg).cost ≤
      gsE.cost + chArg.cost + 69200 + 10 * (ℓ / 32 + 1) + 135 * q + 3 * bits Δ + bits qep := by
  let t0 : Ty S := .prod (e2eGsTy ℓ) (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
  let t1 : Ty S := .prod BV512 .bool
  let tOut : Ty S := .prod GhostStT (B 32)
  have hsendOK := cost_e2eSendOKE_le (ℓ := ℓ) (O' := OO)
    (.fst .v0 : Expr OO (t0 :: Γ) (e2eGsTy ℓ)) (.fst (.snd .v0))
  have hsam := e2eSamIfNec512C_cost coins
    (.snd (.snd (.snd (.snd .v0))) : Expr OO (t0 :: Γ) (.opt BV512))
  have hep := cost_e2eEpMgmtE_le (ℓ := ℓ) (O' := OO) Δ qep
    (.fst .v1 : Expr OO (t1 :: t0 :: Γ) (e2eGsTy ℓ)) (.fst (.snd .v1)) (.snd .v0)
  have hsafe := cost_e2eSafeChE_le (ℓ := ℓ) (O' := OO) Δ
    (.v0 : Expr OO (e2eGsTy ℓ :: t1 :: t0 :: Γ) (e2eGsTy ℓ)) (.fst (.snd .v2))
  have hsend := drSendC_cost hooks I
    (.pair (pGet (e2eGsSt .v0) (.fst (.snd .v2)))
      (.pair (.ite (e2eGsB (.fst .v2))
        (.fst (.snd (.snd (.snd .v2)))) (.fst (.snd (.snd .v2)))) (.fst .v1)) :
      Expr OO (e2eGsTy ℓ :: t1 :: t0 :: Γ) (.prod GhostStT (.prod PlainT BV512)))
  have hrec := cost_e2eRecordE_le (ℓ := ℓ) (O' := OO) q Δ
    (.v1 : Expr OO (tOut :: e2eGsTy ℓ :: t1 :: t0 :: Γ) (e2eGsTy ℓ))
    (.fst (.snd .v3)) (.fst .v0)
    (.pair (.fst (.snd .v3))
      (.pair (pGet (e2eGsEpoch .v1) (.fst (.snd .v3)))
        (.add (pGet (e2eGsIdx .v1) (.fst (.snd .v3))) (.nat 1))))
    (.ite (e2eGsB (.fst .v3))
      (.fst (.snd (.snd (.snd .v3)))) (.fst (.snd (.snd .v3))))
    (.snd .v0) (.bool true)
  have hb1 : bits 1 = 1 := by decide
  simp only [drChArmC, orE, pGet, e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx, cost_smRWireE,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, hb1]
    at hsendOK hsam hep hsafe hsend hrec ⊢
  omega

theorem drDlArmC_cost (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (q : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (dlArg : Expr OO Γ (.prod .bool (B 32))) :
    (drDlArmC hooks coins q gsE dlArg).cost ≤
      gsE.cost + dlArg.cost + 5104900 + 8 * (ℓ / 32 + 1) + 365 * q := by
  let t0 : Ty S := .prod (e2eGsTy ℓ) (.prod .bool (B 32))
  let tQuad : Ty S := .prod GhostStT (.prod .nat (.prod .nat PlainT))
  have htr := cost_e2eInTransitE_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) q
    (.fst .v0 : Expr OO (t0 :: Γ) (e2eGsTy ℓ)) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hc256 := coins.draw256_cost (Γ := e2eRecTy ℓ :: t0 :: Γ)
  have hrecv := drReceiveC_cost hooks I
    (.pair (pGet (e2eGsSt (.fst .v2)) (.fst (.snd .v2)))
      (.pair (.snd (.snd .v2)) .v0) :
      Expr OO (BV256 :: e2eRecTy ℓ :: t0 :: Γ) (.prod GhostStT (.prod (B 32) BV256)))
  have hch := cost_e2eChallContainsE_le (ℓ := ℓ) (O' := OO) q
    (.fst .v4 : Expr OO (tQuad :: drRecvOutT ℓ :: BV256 :: e2eRecTy ℓ :: t0 :: Γ) (e2eGsTy ℓ))
    (e2eRecPos .v3)
  have hacc := cost_e2eAcceptE_le (ℓ := ℓ) (O' := OO) q
    (.fst .v4 : Expr OO (tQuad :: drRecvOutT ℓ :: BV256 :: e2eRecTy ℓ :: t0 :: Γ) (e2eGsTy ℓ))
    (.fst (.snd .v4)) (.fst .v0) (e2eRecPos .v3)
  simp only [drDlArmC, otherE, pGet, e2eGsSt, e2eGsWin, e2eRecPos, cost_smRRecvE,
    cost_recvResultRejE, cost_recvResultAccE, Comp.cost, Expr.cost, Expr.v0, Expr.v2,
    Expr.v3, Expr.v4] at htr hc256 hrecv hch hacc ⊢
  omega

theorem drIjArmC_cost (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (q Δ qep : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (ijArg : Expr OO Γ (.prod .bool (B 32))) :
    (drIjArmC hooks coins q Δ qep gsE ijArg).cost ≤
      gsE.cost + ijArg.cost + 5105200 + 10 * (ℓ / 32 + 1) + 420 * q + 2 * bits Δ +
        bits (qep + 1) := by
  let t0 : Ty S := .prod (e2eGsTy ℓ) (.prod .bool (B 32))
  let tQuad : Ty S := .prod GhostStT (.prod .nat (.prod .nat PlainT))
  have htr := cost_e2eInTransitE_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) q
    (.fst .v0 : Expr OO (t0 :: Γ) (e2eGsTy ℓ)) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hsinj := cost_e2eSafeInjE_le (ℓ := ℓ) (O' := OO) Δ
    (.fst .v0 : Expr OO (t0 :: Γ) (e2eGsTy ℓ))
  have hc256 := coins.draw256_cost (Γ := t0 :: Γ)
  have hrecv := drReceiveC_cost hooks I
    (.pair (pGet (e2eGsSt (.fst .v1)) (.fst (.snd .v1)))
      (.pair (.snd (.snd .v1)) .v0) :
      Expr OO (BV256 :: t0 :: Γ) (.prod GhostStT (.prod (B 32) BV256)))
  have htriv := cost_e2eTrivialE_le (ℓ := ℓ) (O' := OO) q Δ
    (.fst .v3 : Expr OO (tQuad :: drRecvOutT ℓ :: BV256 :: t0 :: Γ) (e2eGsTy ℓ))
    (.pair (otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hacc := cost_e2eAcceptE_le (ℓ := ℓ) (O' := OO) q
    (.fst .v3 : Expr OO (tQuad :: drRecvOutT ℓ :: BV256 :: t0 :: Γ) (e2eGsTy ℓ))
    (.fst (.snd .v3)) (.fst .v0)
    (.pair (otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hwin := cost_e2eGsSetWin_le (ℓ := ℓ) (O' := OO)
    (.fst .v3 : Expr OO (tQuad :: drRecvOutT ℓ :: BV256 :: t0 :: Γ) (e2eGsTy ℓ)) (.bool true)
  simp only [drIjArmC, orE, isSomeE, otherE, pGet, e2eGsSt, e2eGsWin, cost_ratchetKeyAdmissibleE,
    cost_smRRecvE, cost_recvResultRejE, cost_recvResultAccE, Comp.cost, Expr.cost, Expr.v0,
    Expr.v1, Expr.v2, Expr.v3] at htr hsinj hc256 hrecv htriv hacc hwin ⊢
  omega

theorem drCrArmC_cost {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (q : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (crArg : Expr OO Γ .bool) :
    (drCrArmC (I := I) q gsE crArg).cost ≤
      gsE.cost + crArg.cost + 75 * q + 550 := by
  let t0 : Ty S := .prod (e2eGsTy ℓ) .bool
  have hallow := cost_e2eCorrAllowedE_le (ℓ := ℓ) (O' := OO) q
    (.fst .v0 : Expr OO (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hwin := cost_e2eInWindowE_le (ℓ := ℓ) (O' := OO)
    (.fst .v0 : Expr OO (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hcorrOK := cost_e2eCorrOKE_le (ℓ := ℓ) (O' := OO)
    (.fst .v0 : Expr OO (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hafter := cost_e2eAfterCorrAllowedE_le (ℓ := ℓ) (O' := OO)
    (.fst .v0 : Expr OO (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  simp only [drCrArmC, orE, pGet, e2eGsSt, e2eGsWin, cost_smRCorrE, Comp.cost, Expr.cost,
    Expr.v0] at hallow hwin hcorrOK hafter ⊢
  omega

theorem drOracleStepC_cost (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (q Δ qep : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (qryE : Expr OO Γ smQT) :
    (drOracleStepC hooks coins q Δ qep gsE qryE).cost ≤
      gsE.cost + qryE.cost + 5105300 + 10 * (ℓ / 32 + 1) + 420 * q +
        3 * bits Δ + bits qep + bits (qep + 1) := by
  let tTop : Ty S := .prod (e2eGsTy ℓ) smQT
  let r1T : Ty S :=
    .sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
      (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool))
  let r2T : Ty S := .sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool)
  let r3T : Ty S := .sum (.prod .bool (B 32)) .bool
  have htr := drTrArmC_cost hooks coins q Δ qep
    (.fst .v1 : Expr OO (.prod .bool (.prod PlainT (.opt BV512)) :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  have hch := drChArmC_cost hooks coins q Δ qep
    (.fst .v2 : Expr OO (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))) :: r1T :: tTop :: Γ)
      (e2eGsTy ℓ)) .v0
  have hdl := drDlArmC_cost hooks coins q
    (.fst .v3 : Expr OO (.prod .bool (B 32) :: r2T :: r1T :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  have hij := drIjArmC_cost hooks coins q Δ qep
    (.fst .v4 : Expr OO (.prod .bool (B 32) :: r3T :: r2T :: r1T :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  have hcr := drCrArmC_cost (I := I) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) q
    (.fst .v4 : Expr OO (.bool :: r3T :: r2T :: r1T :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  simp only [drOracleStepC, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    Expr.v4] at htr hch hdl hij hcr ⊢
  omega

theorem drOracleStepC_cost_lt (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (q qep : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (qryE : Expr OO Γ smQT)
    (hq : q ≤ 1350)
    (hargs : gsE.cost + qryE.cost ≤ 2000)
    (hqep : bits qep + bits (qep + 1) ≤ 2000) :
    (drOracleStepC hooks coins q (2 + 1) qep gsE qryE).cost <
      5700000 + 32 * (ℓ / 32 + 1) := by
  have hmain := drOracleStepC_cost hooks coins q (2 + 1) qep gsE qryE
  have hb3 : bits (2 + 1) = 2 := by decide
  rw [hb3] at hmain
  omega

/-! ## Evaluation agreement with `SM.oracleImplR` -/

theorem drTrArmC_eval (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (q Δ qep : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (trArg : Expr OO Γ (.prod .bool (.prod PlainT (.opt BV512))))
    (ρ : Env Γ)
    (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (party : Party) (m : Plain ℓ) (optR : Option (BitVec 512))
    (h : SmReachBounded C K q st)
    (hgs : gsE.eval ρ = e2eGsEnc st)
    (harg : trArg.eval ρ = (partyEnc party, (m, optR))) :
    (drTrArmC hooks coins q Δ qep gsE trArg).eval ρ =
      Prod.map (fun w => (w, (none, none))) e2eGsEnc <$>
        I.liftP ((transmitR
          (sessionSchemeFixedSpk
            (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
          Δ qep (configRefuseEarlyBobCorr decT encT) (party, m, optR)).run st) := by
  set sm := sessionSchemeFixedSpk
    (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
  set cfg : CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes :=
    configRefuseEarlyBobCorr decT encT
  unfold drTrArmC transmitR transmitImpl
  simp only [Comp.eval, Expr.eval, hgs, harg, pure_bind]
  let t0 : Ty S := .prod (e2eGsTy ℓ) (.prod .bool (.prod PlainT (.opt BV512)))
  set ρ₁ := Env.cons (t := t0) (e2eGsEnc st, (partyEnc party, (m, optR))) ρ
  have hSendOK : (e2eSendOKE (.fst (Expr.v0 (O := OO))) (.fst (.snd .v0))).eval ρ₁ =
      cfg.sendOK st party :=
    eval_e2eSendOKE decT encT (.fst .v0) (.fst (.snd .v0)) ρ₁ st party rfl rfl
  have hWin : (e2eGsWin (.fst (Expr.v0 (O := OO)))).eval ρ₁ = st.win := rfl
  simp only [orE_eval, Expr.eval, hSendOK, hWin]
  by_cases hok : cfg.sendOK st party
  · by_cases hwin : st.win
    · simp [ρ₁, hok, hwin, StateT.run_bind, StateT.run_get, StateT.run_pure,
        Expr.eval, Expr.v0, Prod.map]
    · have hOptR : (Expr.snd (.snd (.snd (Expr.v0 (O := OO))))).eval ρ₁ = optR := rfl
      simp only [hok, hwin, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
        e2eSamIfNec512C_eval coins, hOptR, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
        monadLift_self, pure_bind, bind_assoc, liftP_bind, map_bind]
      refine bind_congr fun ⟨rCoins, bad⟩ => ?_
      let t1 : Ty S := .prod BV512 .bool
      set ρ₂ := Env.cons (t := t1) (rCoins, bad) ρ₁
      have hep : (e2eEpMgmtE Δ qep (.fst (Expr.v1 (O := OO))) (.fst (.snd .v1)) (.snd .v0)).eval ρ₂ =
          (st.epMgmt Δ qep party bad).map e2eGsEnc :=
        eval_e2eEpMgmtE Δ qep (.fst .v1) (.fst (.snd .v1)) (.snd .v0) ρ₂ st party rfl rfl
      rw [hep]
      cases hepEq : st.epMgmt Δ qep party bad with
      | none =>
        simp [ρ₂, ρ₁, StateT.run_pure, Expr.eval, Expr.v1, Prod.map]
      | some s1 =>
        simp only [Option.map_some]
        obtain ⟨hst1, htr1, hcp1⟩ := epMgmt_preserve_fields hepEq
        set ρ₃ := Env.cons (t := e2eGsTy ℓ) (e2eGsEnc s1) ρ₂
        have hSendIn :
            (Expr.pair (pGet (e2eGsSt (Expr.v0 (O := OO))) (.fst (.snd .v2)))
              (.pair (.fst (.snd (.snd .v2))) (.fst .v1))).eval ρ₃ =
            (s1.st party, (m, rCoins)) := by
          rw [pair_eval, pGet_eval _ _ ρ₃ s1.st party rfl rfl]
          rfl
        have hgParty : PartyReachInv C K
            ((Expr.pair (pGet (e2eGsSt (Expr.v0 (O := OO))) (.fst (.snd .v2)))
              (.pair (.fst (.snd (.snd .v2))) (.fst .v1))).eval ρ₃).1 := by
          rw [hSendIn, hst1]
          exact h.reach.party party
        rw [drSendC_eval hooks I _ ρ₃ idA idB spkCoins hgParty, hSendIn]
        simp only [pure_bind, StateT.run_bind, StateT.run_set, StateT.run_pure, liftP_pure,
          map_pure, Prod.map]
        let tOut : Ty S := .prod GhostStT (B 32)
        set out := sm.send (s1.st party) m rCoins
        set ρ₄ := Env.cons (t := tOut) out ρ₃
        have hpos4 :
            (Expr.pair (.fst (.snd (Expr.v3 (O := OO))))
              (.pair (pGet (e2eGsEpoch .v1) (.fst (.snd .v3)))
                (.add (pGet (e2eGsIdx .v1) (.fst (.snd .v3))) (.nat 1)))).eval ρ₄ =
            posEnc ⟨party, s1.epoch party, s1.idx party + 1⟩ := by
          have hep4 : (pGet (e2eGsEpoch (Expr.v1 (O := OO))) (.fst (.snd .v3))).eval ρ₄ =
              s1.epoch party := pGet_eval (t := .nat) _ _ ρ₄ s1.epoch party rfl rfl
          have hidx4 : (pGet (e2eGsIdx (Expr.v1 (O := OO))) (.fst (.snd .v3))).eval ρ₄ =
              s1.idx party := pGet_eval (t := .nat) _ _ ρ₄ s1.idx party rfl rfl
          simp only [Expr.eval, hep4, hidx4]
          rfl
        have htr1_le : s1.trans.length ≤ q := htr1 ▸ h.lists.trans_le
        have hcp1_le : (dedupComp s1.comp).length ≤ q := hcp1 ▸ h.lists.dedupComp_le
        have hrec4 := eval_e2eRecordE q Δ (.v1 : Expr OO _ (e2eGsTy ℓ)) (.fst (.snd .v3))
          (.fst .v0)
          (.pair (.fst (.snd .v3))
            (.pair (pGet (e2eGsEpoch .v1) (.fst (.snd .v3)))
              (.add (pGet (e2eGsIdx .v1) (.fst (.snd .v3))) (.nat 1))))
          (.fst (.snd (.snd .v3))) (.snd .v0) (.bool false)
          ρ₄ s1 party ⟨party, s1.epoch party, s1.idx party + 1⟩
          htr1_le hcp1_le rfl rfl hpos4
        simp only [eval_smRWireE, hrec4]
        rfl
  · simp [ρ₁, hok, StateT.run_bind, StateT.run_get, StateT.run_pure,
      Expr.eval, Expr.v0, Prod.map]

theorem drChArmC_eval (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (q Δ qep : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (chArg : Expr OO Γ (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512)))))
    (ρ : Env Γ)
    (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (party : Party) (m0 m1 : Plain ℓ) (optR : Option (BitVec 512))
    (h : SmReachBounded C K q st)
    (hgs : gsE.eval ρ = e2eGsEnc st)
    (harg : chArg.eval ρ = (partyEnc party, (m0, (m1, optR)))) :
    (drChArmC hooks coins q Δ qep gsE chArg).eval ρ =
      Prod.map (fun w => (w, (none, none))) e2eGsEnc <$>
        I.liftP ((challR
          (sessionSchemeFixedSpk
            (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
          Δ qep (configRefuseEarlyBobCorr decT encT) (party, m0, m1, optR)).run st) := by
  set sm := sessionSchemeFixedSpk
    (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
  set cfg : CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes :=
    configRefuseEarlyBobCorr decT encT
  have hchallAllowed : ∀ t, cfg.base.challAllowedIn t = true := fun _ => rfl
  have hchallMsg : ∀ t, cfg.base.challMsg t = none := fun _ => rfl
  unfold drChArmC challR challImpl
  simp only [Comp.eval, Expr.eval, hgs, harg, pure_bind]
  let t0 : Ty S := .prod (e2eGsTy ℓ) (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
  set ρ₁ := Env.cons (t := t0) (e2eGsEnc st, (partyEnc party, (m0, (m1, optR)))) ρ
  have hSendOK : (e2eSendOKE (.fst (Expr.v0 (O := OO))) (.fst (.snd .v0))).eval ρ₁ =
      cfg.sendOK st party :=
    eval_e2eSendOKE decT encT (.fst .v0) (.fst (.snd .v0)) ρ₁ st party rfl rfl
  have hWin : (e2eGsWin (.fst (Expr.v0 (O := OO)))).eval ρ₁ = st.win := rfl
  simp only [orE_eval, Expr.eval, hSendOK, hWin]
  by_cases hok : cfg.sendOK st party
  · by_cases hwin : st.win
    · simp [ρ₁, hok, hwin, StateT.run_bind, StateT.run_get, StateT.run_pure,
        Expr.eval, Expr.v0, Prod.map]
    · have hOptR : (Expr.snd (.snd (.snd (.snd (Expr.v0 (O := OO)))))).eval ρ₁ = optR := rfl
      simp only [hok, hwin, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
        e2eSamIfNec512C_eval coins, hOptR, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
        monadLift_self, pure_bind, bind_assoc, liftP_bind, map_bind]
      refine bind_congr fun ⟨rCoins, bad⟩ => ?_
      let t1 : Ty S := .prod BV512 .bool
      set ρ₂ := Env.cons (t := t1) (rCoins, bad) ρ₁
      have hep : (e2eEpMgmtE Δ qep (.fst (Expr.v1 (O := OO))) (.fst (.snd .v1)) (.snd .v0)).eval ρ₂ =
          (st.epMgmt Δ qep party bad).map e2eGsEnc :=
        eval_e2eEpMgmtE Δ qep (.fst .v1) (.fst (.snd .v1)) (.snd .v0) ρ₂ st party rfl rfl
      rw [hep]
      cases hepEq : st.epMgmt Δ qep party bad with
      | none =>
        simp [ρ₂, ρ₁, StateT.run_pure, Expr.eval, Expr.v1, Prod.map]
      | some s1 =>
        simp only [Option.map_some, hchallAllowed, Bool.not_true, Bool.or_false]
        obtain ⟨hst1, htr1, hcp1⟩ := epMgmt_preserve_fields hepEq
        set ρ₃ := Env.cons (t := e2eGsTy ℓ) (e2eGsEnc s1) ρ₂
        have hSafe : (e2eSafeChE Δ (Expr.v0 (O := OO)) (.fst (.snd .v2))).eval ρ₃ =
            s1.safeCh Δ party :=
          eval_e2eSafeChE Δ .v0 (.fst (.snd .v2)) ρ₃ s1 party rfl rfl
        simp only [hSafe]
        by_cases hsafe : s1.safeCh Δ party
        · simp only [hsafe, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hchallMsg,
            Option.getD_none]
          set mCh := if st.b then m1 else m0
          have hmCh3 :
              (Expr.ite (e2eGsB (.fst (Expr.v2 (O := OO))))
                (.fst (.snd (.snd (.snd .v2))))
                (.fst (.snd (.snd .v2)))).eval ρ₃ = mCh := by
            simp [ρ₃, ρ₂, ρ₁, mCh, e2eGsB, e2eGsEnc, Expr.eval, Expr.v2]
          have hSendIn :
              (Expr.pair (pGet (e2eGsSt (Expr.v0 (O := OO))) (.fst (.snd .v2)))
                (.pair (.ite (e2eGsB (.fst .v2))
                  (.fst (.snd (.snd (.snd .v2))))
                  (.fst (.snd (.snd .v2)))) (.fst .v1))).eval ρ₃ =
              (s1.st party, (mCh, rCoins)) := by
            rw [pair_eval, pGet_eval _ _ ρ₃ s1.st party rfl rfl, pair_eval, hmCh3]
            rfl
          have hgParty : PartyReachInv C K
              ((Expr.pair (pGet (e2eGsSt (Expr.v0 (O := OO))) (.fst (.snd .v2)))
                (.pair (.ite (e2eGsB (.fst .v2))
                  (.fst (.snd (.snd (.snd .v2))))
                  (.fst (.snd (.snd .v2)))) (.fst .v1))).eval ρ₃).1 := by
            rw [hSendIn, hst1]
            exact h.reach.party party
          rw [drSendC_eval hooks I _ ρ₃ idA idB spkCoins hgParty, hSendIn]
          simp only [pure_bind, StateT.run_bind, StateT.run_set, StateT.run_pure, liftP_pure,
            map_pure, Prod.map]
          let tOut : Ty S := .prod GhostStT (B 32)
          set out := sm.send (s1.st party) mCh rCoins
          set ρ₄ := Env.cons (t := tOut) out ρ₃
          have hmCh4 :
              (Expr.ite (e2eGsB (.fst (Expr.v3 (O := OO))))
                (.fst (.snd (.snd (.snd .v3))))
                (.fst (.snd (.snd .v3)))).eval ρ₄ = mCh := by
            simp [ρ₄, ρ₃, ρ₂, ρ₁, mCh, e2eGsB, e2eGsEnc, Expr.eval, Expr.v3]
          have hpos4 :
              (Expr.pair (.fst (.snd (Expr.v3 (O := OO))))
                (.pair (pGet (e2eGsEpoch .v1) (.fst (.snd .v3)))
                  (.add (pGet (e2eGsIdx .v1) (.fst (.snd .v3))) (.nat 1)))).eval ρ₄ =
              posEnc ⟨party, s1.epoch party, s1.idx party + 1⟩ := by
            have hep4 : (pGet (e2eGsEpoch (Expr.v1 (O := OO))) (.fst (.snd .v3))).eval ρ₄ =
                s1.epoch party := pGet_eval (t := .nat) _ _ ρ₄ s1.epoch party rfl rfl
            have hidx4 : (pGet (e2eGsIdx (Expr.v1 (O := OO))) (.fst (.snd .v3))).eval ρ₄ =
                s1.idx party := pGet_eval (t := .nat) _ _ ρ₄ s1.idx party rfl rfl
            simp only [Expr.eval, hep4, hidx4]
            rfl
          have htr1_le : s1.trans.length ≤ q := htr1 ▸ h.lists.trans_le
          have hcp1_le : (dedupComp s1.comp).length ≤ q := hcp1 ▸ h.lists.dedupComp_le
          have hrec4 := eval_e2eRecordE q Δ (.v1 : Expr OO _ (e2eGsTy ℓ)) (.fst (.snd .v3))
            (.fst .v0)
            (.pair (.fst (.snd .v3))
              (.pair (pGet (e2eGsEpoch .v1) (.fst (.snd .v3)))
                (.add (pGet (e2eGsIdx .v1) (.fst (.snd .v3))) (.nat 1))))
            (.ite (e2eGsB (.fst .v3))
              (.fst (.snd (.snd (.snd .v3))))
              (.fst (.snd (.snd .v3))))
            (.snd .v0) (.bool true)
            ρ₄ s1 party ⟨party, s1.epoch party, s1.idx party + 1⟩
            htr1_le hcp1_le rfl rfl hpos4
          simp only [eval_smRWireE, hrec4, hmCh4]
          rfl
        · simp [ρ₃, ρ₂, ρ₁, hsafe, StateT.run_pure, Expr.eval, Expr.v2, Prod.map]
  · simp [ρ₁, hok, StateT.run_bind, StateT.run_get, StateT.run_pure,
      Expr.eval, Expr.v0, Prod.map]

theorem drDlArmC_eval (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (q : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (dlArg : Expr OO Γ (.prod .bool (B 32)))
    (ρ : Env Γ)
    (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (party : Party) (c : Bytes)
    (h : SmReachBounded C K q st)
    (hgs : gsE.eval ρ = e2eGsEnc st)
    (harg : dlArg.eval ρ = (partyEnc party, c)) :
    (drDlArmC hooks coins q gsE dlArg).eval ρ =
      Prod.map (fun rr => (none, (rr.map recvResultEnc, none))) e2eGsEnc <$>
        I.liftP ((deliverR
          (sessionSchemeFixedSpk
            (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
          (configRefuseEarlyBobCorr decT encT) (party, c)).run st) := by
  set sm := sessionSchemeFixedSpk
    (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
  set cfg : CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes :=
    configRefuseEarlyBobCorr decT encT
  have hdelWin : cfg.base.deliverWin = false := rfl
  unfold drDlArmC deliverR
  dsimp only [Comp.eval]
  rw [pair_eval, hgs, harg, pure_bind]
  let t0 : Ty S := .prod (e2eGsTy ℓ) (.prod .bool (B 32))
  set ρ₁ := Env.cons (t := t0) (e2eGsEnc st, (partyEnc party, c)) ρ
  have hWin : (e2eGsWin (.fst (Expr.v0 (O := OO)))).eval ρ₁ = st.win := rfl
  rw [hWin]
  by_cases hwin : st.win
  · simp only [hwin, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure,
      pure_bind, liftP_pure, map_pure, Prod.map]
    rfl
  · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
    have hOther : (otherE (.fst (.snd (Expr.v0 (O := OO))))).eval ρ₁ = partyEnc party.other := by
      rw [otherE_eval]
      exact not_partyEnc party
    have hInTr := eval_e2eInTransitE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) q
      (.fst .v0) (otherE (.fst (.snd .v0))) (.snd (.snd .v0)) ρ₁ st party.other
      h.lists.trans_le rfl hOther
    have hc1 : (Expr.snd (.snd (Expr.v0 (O := OO)))).eval ρ₁ = c := rfl
    rw [hc1] at hInTr
    rw [hInTr]
    cases htrEq : st.inTransit party.other c with
    | none =>
      simp only [Option.map_none, StateT.run_pure, liftP_pure, map_pure, Prod.map]
      rfl
    | some rec_ =>
      simp only [Option.map_some, coins.draw256_eval, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, pure_bind, bind_assoc, liftP_bind, map_bind, hdelWin,
        Bool.false_and]
      refine bind_congr fun rc => ?_
      set ρ₂ := Env.cons (t := BV256) rc
        (Env.cons (t := e2eRecTy ℓ) (e2eRecEncWith st.comp rec_) ρ₁)
      have hRecvIn :
          (Expr.pair (pGet (e2eGsSt (.fst (Expr.v2 (O := OO)))) (.fst (.snd .v2)))
            (.pair (.snd (.snd .v2)) .v0)).eval ρ₂ =
          (st.st party, (c, rc)) := by
        rw [pair_eval, pGet_eval _ _ ρ₂ st.st party rfl rfl]
        rfl
      have hgParty : PartyReachInv C K
          ((Expr.pair (pGet (e2eGsSt (.fst (Expr.v2 (O := OO)))) (.fst (.snd .v2)))
            (.pair (.snd (.snd .v2)) .v0)).eval ρ₂).1 := by
        rw [hRecvIn]
        exact h.reach.party party
      rw [drReceiveC_eval hooks I _ ρ₂ idA idB spkCoins hgParty, hRecvIn]
      simp only [pure_bind]
      cases hrecv : sm.receive (st.st party) c rc with
      | none =>
        have hv0 : (Expr.v0 (O := OO)).eval (Env.cons (t := drRecvOutT ℓ) none ρ₂) = none := rfl
        rw [hv0]
        rfl
      | some quad =>
        rcases quad with ⟨st', t', i', m'⟩
        have hv0 : (Expr.v0 (O := OO)).eval
            (Env.cons (t := drRecvOutT ℓ) (some (st', (t', (i', m')))) ρ₂) =
            some (st', (t', (i', m'))) := rfl
        rw [hv0]
        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
          pure_bind, liftP_pure, map_pure, Prod.map]
        let tQuad : Ty S := .prod GhostStT (.prod .nat (.prod .nat PlainT))
        set ρ₃ := Env.cons (t := tQuad) (st', (t', (i', m')))
          (Env.cons (t := drRecvOutT ℓ) (some (st', (t', (i', m')))) ρ₂)
        have hrPos : (e2eRecPos (Expr.v3 (O := OO))).eval ρ₃ = posEnc rec_.pos := rfl
        have hChall := eval_e2eChallContainsE q (.fst (Expr.v4 (O := OO))) (e2eRecPos .v3)
          ρ₃ st rec_.pos h.lists.chall_le rfl hrPos
        have hAcc := eval_e2eAcceptE q (.fst (Expr.v4 (O := OO))) (.fst (.snd .v4)) (.fst .v0)
          (e2eRecPos .v3) ρ₃ st party rec_.pos h.lists rfl rfl hrPos
        simp only [pair_eval, eval_smRRecvE, some_eval, eval_recvResultAccE, ite_eval,
          hChall, hAcc]
        cases st.chall.contains rec_.pos <;> rfl

theorem drIjArmC_eval (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (q Δ qep : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (ijArg : Expr OO Γ (.prod .bool (B 32)))
    (ρ : Env Γ)
    (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (party : Party) (c : Bytes)
    (h : SmReachBounded C K q st)
    (hgs : gsE.eval ρ = e2eGsEnc st)
    (harg : ijArg.eval ρ = (partyEnc party, c)) :
    (drIjArmC hooks coins q Δ qep gsE ijArg).eval ρ =
      Prod.map (fun rr => (none, (rr.map recvResultEnc, none))) e2eGsEnc <$>
        I.liftP ((injectR
          (sessionSchemeFixedSpk
            (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
          Δ qep (configRefuseEarlyBobCorr decT encT) (party, c)).run st) := by
  set sm := sessionSchemeFixedSpk
    (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
  set cfg : CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes :=
    configRefuseEarlyBobCorr decT encT
  have hinjFull : ∀ t, cfg.base.injectFull t = true := fun _ => rfl
  have hinjOK : cfg.injOK = ratchetKeyAdmissible protoSignalCodec decT encT := rfl
  unfold drIjArmC injectR
  dsimp only [Comp.eval]
  rw [pair_eval, hgs, harg, pure_bind]
  let t0 : Ty S := .prod (e2eGsTy ℓ) (.prod .bool (B 32))
  set ρ₁ := Env.cons (t := t0) (e2eGsEnc st, (partyEnc party, c)) ρ
  have hOther : (otherE (.fst (.snd (Expr.v0 (O := OO))))).eval ρ₁ = partyEnc party.other := by
    rw [otherE_eval]
    exact not_partyEnc party
  have hInTr := eval_e2eInTransitE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) q
    (.fst .v0) (otherE (.fst (.snd .v0))) (.snd (.snd .v0)) ρ₁ st party.other
    h.lists.trans_le rfl hOther
  have hc1 : (Expr.snd (.snd (Expr.v0 (O := OO)))).eval ρ₁ = c := rfl
  rw [hc1] at hInTr
  have hSafeInj : (e2eSafeInjE Δ (.fst (Expr.v0 (O := OO)))).eval ρ₁ = st.safeInj Δ :=
    eval_e2eSafeInjE Δ (.fst .v0) ρ₁ st rfl
  have hAdm : (ratchetKeyAdmissibleE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      (.snd (.snd .v0))).eval ρ₁ = cfg.injOK c := by
    rw [eval_ratchetKeyAdmissibleE, hc1, hinjOK]
  have hRefuse :
      (orE (e2eGsWin (.fst (Expr.v0 (O := OO))))
        (orE (isSomeE (e2eInTransitE q (.fst .v0) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))))
          (orE (.not (e2eSafeInjE Δ (.fst .v0)))
            (.not (ratchetKeyAdmissibleE (.snd (.snd .v0))))))).eval ρ₁ =
      (st.win || (st.inTransit party.other c).isSome || !st.safeInj Δ || !cfg.injOK c) := by
    simp only [orE_eval, isSomeE_eval, Expr.eval, hInTr, hSafeInj, hAdm, Option.isSome_map]
    simp [ρ₁, e2eGsWin, e2eGsEnc, Expr.eval, Expr.v0, Bool.or_assoc]
  rw [hRefuse]
  by_cases href : st.win || (st.inTransit party.other c).isSome || !st.safeInj Δ || !cfg.injOK c
  · simp only [href, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure,
      pure_bind, liftP_pure, map_pure, Prod.map]
    rfl
  · simp only [href, Bool.false_eq_true, ↓reduceIte, coins.draw256_eval,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      pure_bind, bind_assoc, liftP_bind, map_bind]
    refine bind_congr fun rc => ?_
    set ρ₂ := Env.cons (t := BV256) rc ρ₁
    have hRecvIn :
        (Expr.pair (pGet (e2eGsSt (.fst (Expr.v1 (O := OO)))) (.fst (.snd .v1)))
          (.pair (.snd (.snd .v1)) .v0)).eval ρ₂ =
        (st.st party, (c, rc)) := by
      rw [pair_eval, pGet_eval _ _ ρ₂ st.st party rfl rfl]
      rfl
    have hgParty : PartyReachInv C K
        ((Expr.pair (pGet (e2eGsSt (.fst (Expr.v1 (O := OO)))) (.fst (.snd .v1)))
          (.pair (.snd (.snd .v1)) .v0)).eval ρ₂).1 := by
      rw [hRecvIn]
      exact h.reach.party party
    rw [drReceiveC_eval hooks I _ ρ₂ idA idB spkCoins hgParty, hRecvIn]
    simp only [pure_bind]
    cases hrecv : sm.receive (st.st party) c rc with
    | none =>
      have hv0 : (Expr.v0 (O := OO)).eval (Env.cons (t := drRecvOutT ℓ) none ρ₂) = none := rfl
      rw [hv0]
      simp only [StateT.run_pure, liftP_pure, map_pure, Prod.map]
      rfl
    | some quad =>
      rcases quad with ⟨st', t', i', m'⟩
      have hv0 : (Expr.v0 (O := OO)).eval
          (Env.cons (t := drRecvOutT ℓ) (some (st', (t', (i', m')))) ρ₂) =
          some (st', (t', (i', m'))) := rfl
      rw [hv0]
      dsimp only
      let tQuad : Ty S := .prod GhostStT (.prod .nat (.prod .nat PlainT))
      set ρ₃ := Env.cons (t := tQuad) (st', (t', (i', m')))
        (Env.cons (t := drRecvOutT ℓ) (some (st', (t', (i', m')))) ρ₂)
      have hlt : (Expr.lt (.nat (qep + 1)) (.fst (.snd (Expr.v0 (O := OO))))).eval ρ₃ =
          decide (qep + 1 < t') := rfl
      rw [hlt]
      by_cases hqep : qep + 1 < t'
      · simp only [hqep, decide_true, ↓reduceIte, StateT.run_pure, liftP_pure, map_pure, Prod.map]
        rfl
      · simp only [hqep, decide_false, Bool.false_eq_true, ↓reduceIte]
        have hpos3 :
            (Expr.pair (otherE (.fst (.snd (Expr.v3 (O := OO)))))
              (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0))))).eval ρ₃ =
            posEnc ⟨party.other, t', i'⟩ := by
          have ho3 : (otherE (.fst (.snd (Expr.v3 (O := OO))))).eval ρ₃ =
              partyEnc party.other := by
            rw [otherE_eval]
            exact not_partyEnc party
          simp only [Expr.eval, ho3]
          rfl
        have hTriv := eval_e2eTrivialE q Δ (.fst (Expr.v3 (O := OO)))
          (.pair (otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
          ρ₃ st ⟨party.other, t', i'⟩ h.lists rfl hpos3
        rw [hTriv]
        by_cases htriv : st.trivial Δ ⟨party.other, t', i'⟩
        · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, liftP_pure, map_pure, Prod.map]
          have hAcc := eval_e2eAcceptE q (.fst (Expr.v3 (O := OO))) (.fst (.snd .v3)) (.fst .v0)
            (.pair (otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
            ρ₃ st party ⟨party.other, t', i'⟩ h.lists rfl rfl hpos3
          simp only [pair_eval, eval_smRRecvE, some_eval, eval_recvResultAccE, hAcc]
          rfl
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte, hinjFull, StateT.run_bind,
            StateT.run_set, StateT.run_pure, pure_bind, liftP_pure, map_pure, Prod.map]
          have hSetWin := eval_e2eGsSetWin (.fst (Expr.v3 (O := OO))) (.bool true) ρ₃ st rfl
          simp only [pair_eval, eval_smRRecvE, some_eval, eval_recvResultRejE, hSetWin]
          rfl

theorem drCrArmC_eval {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (q : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (crArg : Expr OO Γ .bool)
    (ρ : Env Γ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (party : Party)
    (h : SmListBounded q st)
    (hgs : gsE.eval ρ = e2eGsEnc st)
    (harg : crArg.eval ρ = partyEnc party) :
    (drCrArmC (I := I) q gsE crArg).eval ρ =
      Prod.map (fun st? => (none, (none, st?))) e2eGsEnc <$>
        I.liftP ((corrR (configRefuseEarlyBobCorr decT encT) party).run st) := by
  set cfg : CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes :=
    configRefuseEarlyBobCorr decT encT
  have hr1 : cfg.r1 = true := rfl
  unfold drCrArmC corrR
  simp only [Comp.eval, Expr.eval, hgs, harg, pure_bind]
  let t0 : Ty S := .prod (e2eGsTy ℓ) .bool
  set ρ₁ := Env.cons (t := t0) (e2eGsEnc st, partyEnc party) ρ
  have hAllow := eval_e2eCorrAllowedE q (.fst (Expr.v0 (O := OO))) (.snd .v0)
    ρ₁ st party h rfl rfl
  have hInWin := eval_e2eInWindowE (.fst (Expr.v0 (O := OO))) (.snd .v0)
    ρ₁ st party rfl rfl
  have hCorrOK :
      (e2eCorrOKE (.fst (Expr.v0 (O := OO))) (.snd .v0)).eval ρ₁ = cfg.corrOK st party :=
    eval_e2eCorrOKE decT encT (.fst (Expr.v0 (O := OO))) (.snd .v0) ρ₁ st party rfl rfl
  have hRefuse :
      (orE (e2eGsWin (.fst (Expr.v0 (O := OO))))
        (orE (.not (e2eCorrAllowedE q (.fst .v0) (.snd .v0)))
          (orE (e2eInWindowE (.fst .v0) (.snd .v0))
            (.not (e2eCorrOKE (.fst .v0) (.snd .v0)))))).eval ρ₁ =
      (st.win || !st.corrAllowed party || (cfg.r1 && inWindow st party) ||
        !cfg.corrOK st party) := by
    simp only [orE_eval, Expr.eval, hAllow, hInWin, hCorrOK, hr1, Bool.true_and]
    simp [ρ₁, e2eGsWin, e2eGsEnc, Expr.eval, Expr.v0, Bool.or_assoc]
  rw [hRefuse]
  by_cases href :
      st.win || !st.corrAllowed party || (cfg.r1 && inWindow st party) || !cfg.corrOK st party
  · simp only [href, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure,
      pure_bind, liftP_pure, map_pure, Prod.map]
    rfl
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      StateT.run_set, StateT.run_pure, pure_bind, liftP_pure, map_pure, Prod.map]
    have hallowTrue : st.corrAllowed party = true := by
      cases hc : st.corrAllowed party
      · simp [hc] at href
      · rfl
    have hAfter := eval_e2eAfterCorrAllowedE (.fst (Expr.v0 (O := OO))) (.snd .v0)
      ρ₁ st party hallowTrue rfl rfl
    have hpGet := pGet_eval (e2eGsSt (.fst (Expr.v0 (O := OO)))) (.snd .v0) ρ₁ st.st party rfl rfl
    simp only [eval_smRCorrE, some_eval, hpGet, hAfter]

/-- Exact `Comp.eval` agreement of `drOracleStepC` with `SM.oracleImplR` under `SmReachBounded`. -/
theorem drOracleStepC_eval (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (q Δ qep : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (qryE : Expr OO Γ smQT)
    (ρ : Env Γ)
    (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (h : SmReachBounded C K q st)
    (hgs : gsE.eval ρ = e2eGsEnc st)
    (hqry : qryE.eval ρ = smQenc sq) :
    (drOracleStepC hooks coins q Δ qep gsE qryE).eval ρ =
      Prod.map (smRenc (stT := GhostStT) id sq) e2eGsEnc <$>
        I.liftP ((oracleImplR
          (sessionSchemeFixedSpk
            (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
          Δ qep (configRefuseEarlyBobCorr decT encT) sq).run st) := by
  unfold drOracleStepC
  simp only [Comp.eval, Expr.eval, hgs, hqry, pure_bind]
  rcases sq with (((⟨party, m, optR⟩ | ⟨party, m0, m1, optR⟩) | ⟨party, c⟩) | ⟨party, c⟩) | party
  · dsimp only [smQenc, partyToBool_eq_partyEnc]
    exact drTrArmC_eval hooks coins q Δ qep _ _ _ idA idB spkCoins st party m optR h rfl rfl
  · dsimp only [smQenc, partyToBool_eq_partyEnc]
    exact drChArmC_eval hooks coins q Δ qep _ _ _ idA idB spkCoins st party m0 m1 optR h rfl rfl
  · dsimp only [smQenc, partyToBool_eq_partyEnc]
    exact drDlArmC_eval hooks coins q _ _ _ idA idB spkCoins st party c h rfl rfl
  · dsimp only [smQenc, partyToBool_eq_partyEnc]
    exact drIjArmC_eval hooks coins q Δ qep _ _ _ idA idB spkCoins st party c h rfl rfl
  · dsimp only [smQenc, partyToBool_eq_partyEnc, Expr.v0, Expr.eval, Env.get]
    refine Eq.trans (drCrArmC_eval (I := I) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      q _ _ _ st party h.lists ?_ ?_) ?_
    · rfl
    · rfl
    · dsimp only [oracleImplR]
      congr 1
      funext ⟨st?, s'⟩
      cases st? <;> rfl

theorem drOracleStepC_eval_rdec (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (q Δ qep : ℕ) {Γ : List (Ty S)}
    (gsE : Expr OO Γ (e2eGsTy ℓ))
    (qryE : Expr OO Γ smQT)
    (ρ : Env Γ)
    (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (h : SmReachBounded C K q st)
    (hgs : gsE.eval ρ = e2eGsEnc st)
    (hqry : qryE.eval ρ = smQenc sq) :
    (Prod.map (smRdec (stT := GhostStT) id sq) id <$>
        (drOracleStepC hooks coins q Δ qep gsE qryE).eval ρ) =
      Prod.map id e2eGsEnc <$>
        I.liftP ((oracleImplR
          (sessionSchemeFixedSpk
            (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
          Δ qep (configRefuseEarlyBobCorr decT encT) sq).run st) := by
  rw [drOracleStepC_eval hooks coins q Δ qep gsE qryE ρ idA idB spkCoins st sq h hgs hqry,
    Functor.map_map]
  congr 1
  funext ⟨r, s'⟩
  dsimp only [Prod.map, id]
  exact Prod.ext (smRdec_smRenc_id sq r) rfl

/-! ## `DrSessionSimIface` instance -/

def drOracleStepCost (ℓ qBound qep : ℕ) : ℕ :=
  5105306 + 10 * (ℓ / 32 + 1) + 420 * qBound + bits qep + bits (qep + 1)

/-- `DrSessionSimIface` instance wired from `drOracleStepC` over `SpqrDslHooks`. -/
def drSessionSimIface (hooks : SpqrDslHooks ℓ P C K decT encT) :
    DrSessionSimIface ℓ P C K decT encT where
  oracleStepC := fun {_} {_} I₀ qBound qep {_} gsE qE =>
    drOracleStepC hooks (e2eStepACoinSamplers ℓ P C K decT encT I₀)
      qBound (2 + 1) qep gsE qE
  oracleStepCost := drOracleStepCost ℓ
  oracleStepC_cost := fun {_} {_} I₀ qBound qep {_} gsE qE => by
    have hmain := drOracleStepC_cost hooks
      (e2eStepACoinSamplers ℓ P C K decT encT I₀) qBound (2 + 1) qep gsE qE
    have hb3 : bits (2 + 1) = 2 := by decide
    rw [hb3] at hmain
    dsimp only [drOracleStepCost]
    omega
  oracleStepC_queries := fun {_} {_} I₀ qBound qep {_} gsE qE w =>
    drOracleStepC_queries_zero hooks
      (e2eStepACoinSamplers ℓ P C K decT encT I₀) qBound (2 + 1) qep gsE qE w
  oracleStepC_eval := fun {_} {_} I₀ qBound qep {_} gsE qE ρ idA idB spkCoins gs sq
      hReach hgsE hqE => by
    have hgsE' : gsE.eval ρ = e2eGsEnc gs := hgsE
    have hev := drOracleStepC_eval hooks
      (e2eStepACoinSamplers ℓ P C K decT encT I₀)
      qBound (2 + 1) qep gsE qE ρ idA idB spkCoins gs sq hReach hgsE' hqE
    have hfg :
        Prod.map (smRenc (stT := GhostStT) id sq) e2eGsEnc =
          (fun out : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq ×
              GameState (GhostState Bytes) (Plain ℓ) Bytes =>
            (Computational.Proofs.E2E.Dsl.M2Interfaces.smRenc (stT := GhostStT) id sq out.1,
             Computational.Proofs.E2E.Dsl.M2Interfaces.e2eGsEnc out.2)) := by
      funext ⟨r, s'⟩
      refine Prod.ext ?_ rfl
      rcases sq with (((_ | _) | _) | _) | _ <;> rfl
    rw [hev, hfg, liftP_map]

end StepSimulator

end Computational.Proofs.E2E.Dsl.DrSessionSim
