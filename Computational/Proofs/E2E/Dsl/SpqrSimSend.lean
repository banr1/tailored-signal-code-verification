/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.SpqrSimChain
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopSend
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidCodec
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidPhi
import LibsignalBinary.Proofs.SpqrV1Sync.ChainSync

/-!
# SPQR V1 `ReductionDsl` Send Simulation

Implements `spqrSendComp` over `e2eOps` and proves its static cost bound, zero oracle query
count, and functional equivalence with `spqrV1SessionUniformCoins` on `TopStateTight` states.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.SpqrSimSend

open List Option Prod BitVec OracleSpec OracleComp
open ReductionDsl (Ty Ops Var Expr Comp Iface Env bits)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (Crypto ShaCompress PublicKey)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.E2E (Bytes)
open CryptoVerification.E2E.Costed (B U8 U32 U64 BV256 BV512 E2EPureOp
  e2eSig e2ePureOps e2eOps spqrVnT spqrChainT spqrVnToV spqrChainToV
  spqrSplitEval spqrJoinEval spqrMsgPayloadSuffix spqrBraidSendEval)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp eval_e2ePureOp cost_e2ePureOp)
open Computational.Proofs.E2E.Dsl.ClampsLossless (spqrAssembleMsg_spqrMsgPayloadSuffix)
open Computational.Proofs.E2E.Dsl.SpqrSimChain (spqrBraidSendC cost_spqrBraidSendC
  queries_spqrBraidSendC eval_spqrBraidSendC spqrSplitEval_topStateTightW
  spqrJoinEval_topStateTightW chainOk_send_next_le_64 topStateTightW_links_le_three
  states_send_secret_len spqrBraidSendEval_of_bOkTight
  spqrResolveChainComp queries_spqrResolveChainComp cost_spqrResolveChainComp
  eval_spqrResolveChainComp_topStateTightW
  spqrAddEpochOptComp queries_spqrAddEpochOptComp cost_spqrAddEpochOptComp
  eval_spqrAddEpochOptComp
  spqrChainSendKeyComp queries_spqrChainSendKeyComp cost_spqrChainSendKeyComp
  eval_spqrChainSendKeyComp)
open CryptoVerification.LibsignalSpqrV1 (MlKem ChainPB V1State Chain EpochSecret States Message
  spqrPolyApi spqrAuthApi spqrDeps spqrHkdfWith spqrV1 spqrV1_eq spqrV1Assembled toSpqrModel
  sendPanicsPureB messageKeyToSalt? sendAfterStates liftStatesResult spqrV1SessionUniformCoins
  coinBytes)
open CryptoVerification.SpqrV1Sync.InSync (St)
open CryptoVerification.SpqrV1Sync.ChainSync (ChainOk chainOk_congr seedAt keyAt sendKey_ok)
open LibsignalBinary.Proofs.SpqrV1Sync.ChainSyncBase (length_keyAt)
open CryptoVerification.SpqrV1Sync.TopSync (topPb topBytes decodeState_topBytes send_topBytes
  sendKey_sendPrevNil chainCur epoch_sub_one_le_chainCur send_facts chainCur_send_key)
open CryptoVerification.SpqrV1Sync.SendTotal (TopWitness TopStateTight TopStateTightW
  RecvSmallTight phiB topStateW_length_lt st_bCodec st_bSendClosed_tight
  tsnd_send_addEpoch tsnd_addEpoch_opt tsnd_sendAfterStates_ok tsnd_messageKeyToSalt_keyAt
  sendKey_err_of_ge sendAfterStates_err_of_sendKey_err st_recvSmallAdd_tight
  st_recvSmallSend_tight)

def spqrRunSendChainComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (vn? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt spqrVnT))
    (ch? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt spqrChainT))
    (epSec? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (.prod U64 BV256)))
    (msgEpoch : Expr (e2eOps ℓ P C K decT encT) Γ U64) :
    Comp (e2eOps ℓ P C K decT encT) I Γ
      (.opt (.prod spqrChainT (.prod U32 BV256))) :=
  .bind (.ret (.pair (.pair vn? ch?) (.pair epSec? msgEpoch)))
    (.bind (spqrResolveChainComp I (.fst (.fst .v0)) (.snd (.fst .v0)))
      (.caseOpt .v0
        (.ret .none)
        (.bind (spqrAddEpochOptComp I .v0 (.fst (.snd .v2)))
          (.caseOpt .v0
            (.ret .none)
            (.ite (e2ePureOp .u64Eq
                (.pair (.snd (.snd .v4)) (e2ePureOp (.u64Lit 0#64) .unit)))
              (.ret .none)
              (spqrChainSendKeyComp I .v0
                (e2ePureOp .u64Sub
                  (.pair (.snd (.snd .v4)) (e2ePureOp (.u64Lit 1#64) .unit)))))))))

theorem queries_spqrRunSendChainComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (vn? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt spqrVnT))
    (ch? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt spqrChainT))
    (epSec? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (.prod U64 BV256)))
    (msgEpoch : Expr (e2eOps ℓ P C K decT encT) Γ U64) :
    (spqrRunSendChainComp I vn? ch? epSec? msgEpoch).queries w ws = 0 := by
  simp [spqrRunSendChainComp, Comp.queries, queries_spqrResolveChainComp,
    queries_spqrAddEpochOptComp, queries_spqrChainSendKeyComp]

theorem cost_spqrRunSendChainComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (vn? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt spqrVnT))
    (ch? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt spqrChainT))
    (epSec? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (.prod U64 BV256)))
    (msgEpoch : Expr (e2eOps ℓ P C K decT encT) Γ U64) :
    (spqrRunSendChainComp I vn? ch? epSec? msgEpoch).cost ≤
      vn?.cost + ch?.cost + epSec?.cost + msgEpoch.cost + 1400 := by
  let Γ1 := .prod (.prod (.opt spqrVnT) (.opt spqrChainT))
    (.prod (.opt (.prod U64 BV256)) U64) :: Γ
  let Γ3 := spqrChainT :: .opt spqrChainT :: Γ1
  let Γ5 := spqrChainT :: .opt spqrChainT :: Γ3
  have hc1 := cost_spqrResolveChainComp (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ1) I (.fst (.fst .v0)) (.snd (.fst .v0))
  have hc2 := cost_spqrAddEpochOptComp (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ3) I .v0 (.fst (.snd .v2))
  have hc3 := cost_spqrChainSendKeyComp (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ5) I .v0
    (e2ePureOp .u64Sub (.pair (.snd (.snd .v4)) (e2ePureOp (.u64Lit 1#64) .unit)))
  dsimp only [Γ1, Γ3, Γ5] at hc1 hc2 hc3
  simp only [Expr.cost, cost_e2ePureOp, E2EPureOp.cost, Expr.v0, Expr.v2, Expr.v4] at hc1 hc2 hc3
  simp only [spqrRunSendChainComp, Comp.cost, Expr.cost, cost_e2ePureOp, E2EPureOp.cost,
    Expr.v0, Expr.v2, Expr.v4]
  omega

private theorem addEpoch_links_le_four (F : ShaCompress) (chE chain1 : Chain)
    (key : Option EpochSecret) (hlen3 : chE.links.length ≤ 3)
    (hadd : (match key with
      | some es => chE.addEpoch (spqrHkdfWith F) es
      | none => .ok chE) = .ok chain1) :
    chain1.links.length ≤ 4 := by
  cases key with
  | none =>
    cases hadd
    omega
  | some es =>
    dsimp only at hadd
    unfold Chain.addEpoch at hadd
    split_ifs at hadd
    injection hadd with hadd'
    subst hadd'
    simp only [List.length_append, List.length_singleton]
    omega

/-- Simulates `(spqrV1SessionUniformCoins C.F K).send` in `ReductionDsl`. -/
def spqrSendComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) BV512)) :
    Comp (e2eOps ℓ P C K decT encT) I Γ
      (.opt (.prod (B 32) (.prod (.opt BV256) (B 32)))) :=
  .bind (.ret e)
    (.caseOpt (e2ePureOp .spqrStateSplit (.fst .v0))
      (.ret .none)
      (.caseOpt (.fst .v0)
        (.ret (.some (.pair
          (e2ePureOp (.bytesLit 32 []) .unit)
          (.pair .none (e2ePureOp (.bytesLit 32 []) .unit)))))
        (.bind (spqrBraidSendC I (.pair .v0 (.snd .v2)))
          (.caseOpt (.snd .v0)
            (.ret .none)
            (.bind
              (spqrRunSendChainComp I
                (.fst (.snd .v3))
                (.snd (.snd .v3))
                (.fst (.snd (.snd .v0)))
                (.fst (.snd .v0)))
              (.caseOpt .v0
                (.ret .none)
                (.ret (.some (.pair
                  (e2ePureOp .spqrStateJoin
                    (.pair (.some (.fst .v2))
                      (.pair (.fst (.snd .v5)) (.some (.fst .v0)))))
                  (.pair
                    (.some (.snd (.snd .v0)))
                    (e2ePureOp .spqrAssembleMsg
                      (.pair (.fst (.snd .v2))
                        (.pair (.fst (.snd .v0)) (.snd (.snd (.snd .v2))))))))))))))))

theorem spqrSendComp_cost {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) BV512)) :
    (spqrSendComp I e).cost ≤ e.cost + 65536 := by
  let braidOutT : Ty (e2eSig ℓ) :=
    .prod (B 32) (.prod U64 (.prod (.opt (.prod U64 BV256)) (B 64)))
  let partsT : Ty (e2eSig ℓ) := .prod (.opt (B 32)) (.prod (.opt spqrVnT) (.opt spqrChainT))
  let Γrun : List (Ty (e2eSig ℓ)) :=
    braidOutT :: .prod .bool (.opt braidOutT) :: B 32 :: partsT :: .prod (B 32) BV512 :: Γ
  have hcRun := cost_spqrRunSendChainComp (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γrun) I
    (.fst (.snd .v3)) (.snd (.snd .v3)) (.fst (.snd (.snd .v0))) (.fst (.snd .v0))
  have hp32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  dsimp only [Γrun, braidOutT, partsT] at hcRun
  simp only [Expr.cost, Expr.v0, Expr.v3] at hcRun
  simp only [spqrSendComp, Comp.cost, cost_spqrBraidSendC, Expr.cost, cost_e2ePureOp,
    E2EPureOp.cost, hp32, List.length_nil, Expr.v0, Expr.v2, Expr.v3, Expr.v5]
  omega

theorem spqrSendComp_queries {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) BV512))
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (spqrSendComp I e).queries w ws = 0 := by
  simp [spqrSendComp, Comp.queries, queries_spqrRunSendChainComp]

private theorem spqrUniform_send_rhs (F : ShaCompress) (K : MlKem) (pq : Bytes) (r : BitVec 512) :
    (let spqr := spqrV1SessionUniformCoins F K
     if spqr.sendPanics pq r then none
     else (spqr.send pq r).map fun (pq', saltVec?, pqMsg) =>
       (pq', (saltVec?.map (fun v => bytesToKey32 v.toList), pqMsg))) =
    match (CryptoVerification.LibsignalSpqrV1.send (spqrDeps F K) (spqrHkdfWith F) pq
        (coinBytes r)).1 with
    | .ok s =>
      match messageKeyToSalt? s.key with
      | some saltVec? =>
        some (s.state, (saltVec?.map (fun v => bytesToKey32 v.toList), s.msg))
      | none => none
    | .error _ => none := by
  dsimp only [spqrV1SessionUniformCoins, SpqrModel.spqrWith]
  rw [spqrV1_eq]
  dsimp only [toSpqrModel, spqrV1Assembled, sendPanicsPureB]
  suffices ∀ res : CryptoVerification.LibsignalSpqrV1.SpqrApiResult
      CryptoVerification.LibsignalSpqrV1.Send,
      (if (match res with
          | .ok _ => false
          | .error (.err _) => false
          | .error (.panic _) => true) = true then none
       else Option.map (fun (pq', saltVec?, pqMsg) =>
            (pq', (Option.map (fun v => bytesToKey32 v.toList) saltVec?, pqMsg)))
          (match res with
          | .ok s =>
            match messageKeyToSalt? s.key with
            | some salt => some (s.state, salt, s.msg)
            | none => none
          | .error _ => none)) =
      match res with
      | .ok s =>
        match messageKeyToSalt? s.key with
        | some saltVec? =>
          some (s.state, (saltVec?.map (fun v => bytesToKey32 v.toList), s.msg))
        | none => none
      | .error _ => none from this _
  intro res
  cases res with
  | error err => cases err <;> rfl
  | ok s =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases messageKeyToSalt? s.key <;> rfl

private theorem eval_spqrRunSendChainComp_of_chain1 {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (vnExpr : Expr (e2eOps ℓ P C K decT encT) Γ (.opt spqrVnT))
    (chExpr : Expr (e2eOps ℓ P C K decT encT) Γ (.opt spqrChainT))
    (epSecExpr : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (.prod U64 BV256)))
    (epExpr : Expr (e2eOps ℓ P C K decT encT) Γ U64)
    (ρ : Env Γ) {pq : Bytes} {w : TopWitness C.F}
    (hw : TopStateTightW C.F K pq w)
    (secret' : ℕ → Bytes) (m : Message spqrPolyApi) (key : Option EpochSecret) (chain1 : Chain)
    (hok' : ChainOk C.F w.authKey w.dir secret' w.sendCtr w.recvSet w.chE)
    (hok1 : ChainOk C.F w.authKey w.dir secret' w.sendCtr w.recvSet chain1)
    (hadd : (match key with
      | some es => w.chE.addEpoch (spqrHkdfWith C.F) es
      | none => .ok w.chE) = .ok chain1)
    (hsec_len : ∀ es, key = some es → es.secret.length = 32)
    (he_ne0 : (m.epoch == 0#64) = false)
    (hvn : vnExpr.eval ρ = w.vn?.map (spqrVnToV (ℓ := ℓ)))
    (hch : chExpr.eval ρ = (w.ch?.map Chain.intoPb).map (spqrChainToV (ℓ := ℓ)))
    (hkey : epSecExpr.eval ρ = key.map (fun es => (es.epoch, bytesToKey32 es.secret)))
    (hep : epExpr.eval ρ = m.epoch) :
    (spqrRunSendChainComp I vnExpr chExpr epSecExpr epExpr).eval ρ =
      pure (match chain1.sendKey (spqrHkdfWith C.F) (m.epoch - 1#64) with
        | .ok (ch2, (idx, mkBytes)) =>
          some (spqrChainToV (ℓ := ℓ) ch2.intoPb, (idx, bytesToKey32 mkBytes))
        | .error _ => none) := by
  have hlen3 := topStateTightW_links_le_three C.F K hw
  have hlen4 := addEpoch_links_le_four C.F w.chE chain1 key hlen3 hadd
  have hnext1 := chainOk_send_next_le_64 C.F w.authKey w.dir secret' w.sendCtr w.recvSet
    chain1 hok1
  simp only [spqrRunSendChainComp, Comp.eval, Expr.eval, pure_bind,
    hvn, hch, hkey, hep]
  let argsT : Ty (e2eSig ℓ) := .prod (.prod (.opt spqrVnT) (.opt spqrChainT))
    (.prod (.opt (.prod U64 BV256)) U64)
  let argsV : argsT.denote :=
    ((w.vn?.map (spqrVnToV (ℓ := ℓ)),
      (w.ch?.map Chain.intoPb).map (spqrChainToV (ℓ := ℓ))),
     (key.map (fun es => (es.epoch, bytesToKey32 es.secret)), m.epoch))
  let ρ1 : Env (argsT :: Γ) := Env.cons (t := argsT) argsV ρ
  have hres :
      (spqrResolveChainComp (P := P) (decT := decT) (encT := encT) I
        (.fst (.fst .v0)) (.snd (.fst .v0))).eval ρ1 =
        pure (some (spqrChainToV (ℓ := ℓ) w.chE.intoPb)) :=
    eval_spqrResolveChainComp_topStateTightW (ℓ := ℓ) (P := P) (decT := decT) (encT := encT)
      I _ _ ρ1 hw
      (by dsimp only [ρ1, argsV, argsT]; simp only [Expr.eval, Expr.v0, Env.get])
      (by dsimp only [ρ1, argsV, argsT]; simp only [Expr.eval, Expr.v0, Env.get])
  have hv0_1 : (Expr.v0 : Expr (e2eOps ℓ P C K decT encT) _ (.opt spqrChainT)).eval
      (Env.cons (t := .opt spqrChainT) (some (spqrChainToV (ℓ := ℓ) w.chE.intoPb)) ρ1) =
      some (spqrChainToV (ℓ := ℓ) w.chE.intoPb) := by
    simp only [Expr.eval, Expr.v0, Env.get]
  dsimp only [ρ1, argsV, argsT] at hres hv0_1
  rw [hres]
  simp only [pure_bind, hv0_1]
  let ρ3 := Env.cons (t := spqrChainT) (spqrChainToV (ℓ := ℓ) w.chE.intoPb)
    (Env.cons (t := .opt spqrChainT) (some (spqrChainToV (ℓ := ℓ) w.chE.intoPb)) ρ1)
  have hadd_eval :
      (spqrAddEpochOptComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I
        .v0 (.fst (.snd .v2))).eval ρ3 =
        pure (some (spqrChainToV (ℓ := ℓ) chain1.intoPb)) := by
    rw [eval_spqrAddEpochOptComp (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I _ _ ρ3 w.authKey w.dir secret' w.sendCtr w.recvSet
      w.chE key hok' hw.htop.hsendPrev hw.hsmall hlen3
      (by dsimp only [ρ3, ρ1, argsV, argsT]; simp only [Expr.eval, Expr.v0, Env.get])
      (by dsimp only [ρ3, ρ1, argsV, argsT]; simp only [Expr.eval, Expr.v2, Env.get]) hsec_len]
    cases key with
    | none =>
      cases hadd
      rfl
    | some es =>
      dsimp only at hadd ⊢
      rw [hadd]
  have hv0_3 : (Expr.v0 : Expr (e2eOps ℓ P C K decT encT) _ (.opt spqrChainT)).eval
      (Env.cons (t := .opt spqrChainT) (some (spqrChainToV (ℓ := ℓ) chain1.intoPb)) ρ3) =
      some (spqrChainToV (ℓ := ℓ) chain1.intoPb) := by
    simp only [Expr.eval, Expr.v0, Env.get]
  dsimp only [ρ3, ρ1, argsV, argsT] at hadd_eval hv0_3
  rw [hadd_eval]
  simp only [pure_bind, hv0_3, Expr.eval, eval_e2ePureOp, E2EPureOp.eval,
    Expr.v4, Env.get, he_ne0, Bool.false_eq_true, ↓reduceIte]
  let ρ5 := Env.cons (t := spqrChainT) (spqrChainToV (ℓ := ℓ) chain1.intoPb)
    (Env.cons (t := .opt spqrChainT) (some (spqrChainToV (ℓ := ℓ) chain1.intoPb)) ρ3)
  have hsk_eval := eval_spqrChainSendKeyComp (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) I .v0
    (e2ePureOp .u64Sub (.pair (.snd (.snd .v4)) (e2ePureOp (.u64Lit 1#64) .unit)))
    ρ5 chain1 hlen4 hnext1 (by dsimp only [ρ5]; simp only [Expr.eval, Expr.v0, Env.get])
  dsimp only [ρ5, ρ3, ρ1, argsV, argsT, Expr.v4] at hsk_eval
  exact hsk_eval

/-- Functional equivalence between `spqrSendComp` and `(spqrV1SessionUniformCoins C.F K).send`
on `TopStateTight` states. -/
theorem spqrSendComp_eval {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) BV512)) (ρ : Env Γ) :
    TopStateTight C.F K (e.eval ρ).1 →
    (spqrSendComp I e).eval ρ = pure (
      let (pq, r) := e.eval ρ
      let spqr := spqrV1SessionUniformCoins C.F K
      if spqr.sendPanics pq r then none
      else (spqr.send pq r).map fun (pq', saltVec?, pqMsg) =>
        (pq', (saltVec?.map (fun v => bytesToKey32 v.toList), pqMsg))) := by
  intro htight
  rcases he : e.eval ρ with ⟨pq, r⟩
  rw [he] at htight
  dsimp only at htight ⊢
  obtain ⟨w, hw⟩ := htight
  refine Eq.trans ?_ (congrArg pure (spqrUniform_send_rhs C.F K pq r)).symm
  have hsize : pq.length < 2 ^ 64 := topStateW_length_lt C.F K hw.toTopStateW
  have hsize' : (topBytes C.F K w.st w.vn? w.ch?).length < 2 ^ 64 := hw.htop.hbytes ▸ hsize
  have hcodec : States.from_pb spqrPolyApi (spqrAuthApi C.F) w.st.into_pb = .ok w.st :=
    st_bCodec C.F w.st hw.hbok.1
  have hsplit := spqrSplitEval_topStateTightW (ℓ := ℓ) C.F K hw
  simp only [spqrSendComp, Comp.eval, Expr.eval, eval_e2ePureOp, E2EPureOp.eval,
    he, pure_bind, Expr.v0, Expr.v2, Env.get, hsplit,
    eval_spqrBraidSendC, spqrBraidSendEval_of_bOkTight C.F K w.st hw.hbok r]
  cases hsendB : w.st.send K (coinBytes r) with
  | error err =>
    rw [hw.htop.hbytes]
    unfold CryptoVerification.LibsignalSpqrV1.send
    rw [decodeState_topBytes C.F K w.st w.vn? w.ch? hsize']
    cases err <;> simp [topPb, spqrDeps, hcodec, liftStatesResult, hsendB]
  | ok p =>
    rcases p with ⟨⟨m, key, st'⟩, tape'⟩
    dsimp only
    have hep_pos : 1 ≤ w.st.epoch.toNat := by have := hw.htop.hsendLe; omega
    obtain ⟨hm_ep, hst'_ep, -, -⟩ := send_facts C.F K w.st st' (coinBytes r) tape' m key hsendB
    have htop := send_topBytes C.F K w.st st' w.vn? w.ch? (coinBytes r) tape' m key
      hsize' hcodec hsendB
    let secret' : ℕ → Bytes :=
      match key with
      | none => w.secret
      | some es => Function.update w.secret (chainCur w.st + 1) es.secret
    have hsec_eq : ∀ ep, 1 ≤ ep → ep ≤ w.chE.currentEpoch.toNat → secret' ep = w.secret ep := by
      intro ep _ hep_le
      have hcur := hw.htop.hcur
      cases key with
      | none => rfl
      | some es => exact Function.update_of_ne (by omega) _ _
    have hok' : ChainOk C.F w.authKey w.dir secret' w.sendCtr w.recvSet w.chE :=
      chainOk_congr C.F w.authKey w.dir w.secret secret' w.sendCtr w.recvSet w.chE
        hw.htop.hok hsec_eq
    have hsec : ∀ es, key = some es → es.secret = secret' es.epoch.toNat := by
      intro es hk
      subst hk
      obtain ⟨hes_ep, -⟩ :=
        chainCur_send_key C.F K w.st st' (coinBytes r) tape' m es hep_pos hsendB
      change es.secret = Function.update w.secret (chainCur w.st + 1) es.secret es.epoch.toNat
      rw [hes_ep, Function.update_self]
    have hsec_len : ∀ es, key = some es → es.secret.length = 32 := by
      intro es hk
      subst hk
      exact states_send_secret_len C.F K hsendB
    obtain ⟨chain1, hadd, hok1, hcur1, hsend1, hle1⟩ :=
      tsnd_send_addEpoch C.F K w.authKey w.dir secret' w.st st' w.sendCtr w.recvSet w.chE hok'
        hw.htop.hcur hep_pos (coinBytes r) tape' m key hsendB hsec
    have he_ne0 : (m.epoch == 0#64) = false := by
      rw [beq_eq_false_iff_ne]
      intro h0
      have : m.epoch.toNat = 0 := congrArg BitVec.toNat h0
      rw [hm_ep] at this
      omega
    have hebv_nat : (m.epoch - 1#64).toNat = w.st.epoch.toNat - 1 := by
      rw [hm_ep, BitVec.toNat_sub_of_le]
      · rfl
      · show 1 ≤ w.st.epoch.toNat
        exact hep_pos
    have hlo : chain1.sendEpoch.toNat ≤ (m.epoch - 1#64).toNat := by
      rw [hsend1, hw.htop.hsendEp, hebv_nat]
      have := hw.htop.hsendLe
      omega
    have hhi : (m.epoch - 1#64).toNat ≤ chain1.currentEpoch.toNat := by
      rw [hebv_nat]
      exact (epoch_sub_one_le_chainCur w.st).trans hle1
    let braidOutT : Ty (e2eSig ℓ) :=
      .prod (B 32) (.prod U64 (.prod (.opt (.prod U64 BV256)) (B 64)))
    let partsT : Ty (e2eSig ℓ) := .prod (.opt (B 32)) (.prod (.opt spqrVnT) (.opt spqrChainT))
    let braidOutV : braidOutT.denote :=
      (V1State.encodeRaw st'.into_pb,
       (m.epoch,
        (key.map (fun es => (es.epoch, bytesToKey32 es.secret)),
         spqrMsgPayloadSuffix m)))
    let partsV : partsT.denote :=
      (some (V1State.encodeRaw w.st.into_pb),
       (w.vn?.map (spqrVnToV (ℓ := ℓ)),
        (w.ch?.map Chain.intoPb).map (spqrChainToV (ℓ := ℓ))))
    let ρRun : Env (braidOutT :: .prod .bool (.opt braidOutT) :: B 32 ::
        partsT :: .prod (B 32) BV512 :: Γ) :=
      Env.cons braidOutV
        (Env.cons (t := .prod .bool (.opt braidOutT)) (false, some braidOutV)
          (Env.cons (t := B 32) (V1State.encodeRaw w.st.into_pb)
            (Env.cons partsV (Env.cons (t := .prod (B 32) BV512) (pq, r) ρ))))
    have hrun := eval_spqrRunSendChainComp_of_chain1 (ℓ := ℓ) (P := P) (decT := decT) (encT := encT) I
      (.fst (.snd .v3)) (.snd (.snd .v3)) (.fst (.snd (.snd .v0))) (.fst (.snd .v0))
      ρRun hw secret' m key chain1 hok' hok1 hadd hsec_len he_ne0
      (by dsimp only [ρRun, braidOutV, partsV]; simp only [Expr.eval, Expr.v3, Env.get])
      (by dsimp only [ρRun, braidOutV, partsV]; simp only [Expr.eval, Expr.v3, Env.get])
      (by dsimp only [ρRun, braidOutV, partsV]; simp only [Expr.eval, Expr.v0, Env.get])
      (by dsimp only [ρRun, braidOutV, partsV]; simp only [Expr.eval, Expr.v0, Env.get])
    dsimp only [ρRun, braidOutV, partsV, Expr.v0] at hrun
    rw [hrun, hw.htop.hbytes, htop]
    dsimp only
    by_cases hctr_lt : w.sendCtr (m.epoch - 1#64).toNat + 1 < 2 ^ 32
    · obtain ⟨chain2, hsk, hcur2, hsend2, hok2⟩ :=
        sendKey_ok C.F w.authKey w.dir secret' w.sendCtr w.recvSet chain1 hok1
          (m.epoch - 1#64) hlo hhi hctr_lt
      rw [hsk]
      rw [hebv_nat] at hsk hok2
      have hafter := tsnd_sendAfterStates_ok C.F K w.authKey w.dir secret' w.st st'
        w.sendCtr w.recvSet w.vn? w.ch? w.chE chain1 chain2 hw.htop.hch hok' m key hadd he_ne0
        (BitVec.ofNat 32 (w.sendCtr (w.st.epoch.toNat - 1) + 1))
        (w.sendCtr (w.st.epoch.toNat - 1))
        (seedAt C.F w.authKey secret' w.dir (w.st.epoch.toNat - 1)) hsk
      rw [hafter]
      dsimp only
      rw [tsnd_messageKeyToSalt_keyAt]
      simp only [pure_bind, Expr.eval, Expr.v5, Env.get]
      have hsp1 := tsnd_addEpoch_opt (spqrHkdfWith C.F) w.chE chain1 key hw.htop.hsendPrev hadd
      have hsmall1 : RecvSmallTight chain1 := by
        cases key with
        | none => cases hadd; exact hw.hsmall
        | some _ => exact st_recvSmallAdd_tight hw.hsmall hadd
      let w' : TopWitness C.F :=
        ⟨w.authKey, w.dir, secret', st', w.st.epoch.toNat - 1,
          Function.update w.sendCtr (w.st.epoch.toNat - 1)
            (w.sendCtr (w.st.epoch.toNat - 1) + 1),
          w.recvSet, w.vn?, some chain2, chain2⟩
      have hw' : TopStateTightW C.F K (topBytes C.F K st' w.vn? (some chain2)) w' :=
        { htop :=
            { hbytes := rfl
              hvn := hw.htop.hvn
              hch := .inl rfl
              hok := hok2
              hcur := by rw [hcur2, hcur1]
              hsendEp := by rw [hsend2, hebv_nat]
              hsendLe := by dsimp only [w']; rw [hst'_ep]; omega
              hsendPrev := sendKey_sendPrevNil (spqrHkdfWith C.F) chain1 chain2 _ _ hsp1 hsk }
          hauth := hw.hauth
          hbok := st_bSendClosed_tight C.F K hw.hbok hsendB
          hphi := by
            dsimp only [w', phiB]
            rw [hst'_ep]
            split <;> omega
          hsmall := st_recvSmallSend_tight hsmall1 hsk }
      have hjoin := spqrJoinEval_topStateTightW (ℓ := ℓ) C.F K hw'
      dsimp only [w'] at hjoin
      have hasm : (e2ePureOps ℓ).eval .spqrAssembleMsg
          (m.epoch, (BitVec.ofNat 32 (w.sendCtr (w.st.epoch.toNat - 1) + 1),
            spqrMsgPayloadSuffix m)) =
          m.serialize (BitVec.ofNat 32 (w.sendCtr (w.st.epoch.toNat - 1) + 1)) :=
        spqrAssembleMsg_spqrMsgPayloadSuffix (ℓ := ℓ) m _
      apply congrArg pure
      apply congrArg some
      refine Prod.ext hjoin (Prod.ext ?_ ?_)
      · rw [hebv_nat]
        rfl
      · rw [hebv_nat]
        exact hasm
    · have herr := sendKey_err_of_ge C.F w.authKey w.dir secret' w.sendCtr w.recvSet chain1 hok1
        (m.epoch - 1#64) hlo hhi hctr_lt
      have hafter := sendAfterStates_err_of_sendKey_err C.F K w.authKey w.dir secret' w.st st'
        w.sendCtr w.recvSet w.vn? w.ch? w.chE chain1 hw.htop.hch hok' m key hadd he_ne0 herr
      rw [herr, hafter]
      simp only [pure_bind]

end Computational.Proofs.E2E.Dsl.SpqrSimSend
