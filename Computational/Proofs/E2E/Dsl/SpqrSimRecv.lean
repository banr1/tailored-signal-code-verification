/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.SpqrSimHist
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopRecv
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopRecvEqual
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidCodec
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidPhi
import LibsignalBinary.Proofs.SpqrV1Sync.ChainSync

/-!
# SPQR V1 `ReductionDsl` Receive Simulation

Implements `spqrRecvComp` over `e2eOps` and proves its static cost bound, zero oracle query
count, and functional equivalence with `spqrV1SessionUniformCoins` on `TopStateTight` states.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.SpqrSimRecv

open List Option Prod BitVec OracleSpec OracleComp
open ReductionDsl (Ty Ops Var Expr Comp Iface Env)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (Crypto ShaCompress PublicKey)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.E2E (Bytes)
open CryptoVerification.E2E.Costed (B U8 U32 U64 BV256 E2EPureOp
  e2eSig e2ePureOps e2eOps spqrVnT spqrChainT spqrStatePartsT
  spqrVnToV spqrChainToV spqrSplitEval spqrJoinEval spqrBraidRecvEval)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp eval_e2ePureOp cost_e2ePureOp)
open Computational.Proofs.E2E.Dsl.ClampsLossless (e2ePureOps_eval_spqrParsePreamble_lossless)
open Computational.Proofs.E2E.Dsl.SpqrSimChain (spqrNegotiateInitC cost_spqrNegotiateInitC
  queries_spqrNegotiateInitC
  spqrBraidRecvC cost_spqrBraidRecvC queries_spqrBraidRecvC eval_spqrBraidRecvC
  spqrSplitEval_topStateTightW spqrJoinEval_topStateTightW
  topStateTightW_links_le_three states_recv_secret_len spqrBraidRecvEval_of_bOkTight
  spqrResolveChainComp queries_spqrResolveChainComp cost_spqrResolveChainComp
  eval_spqrResolveChainComp_topStateTightW
  spqrAddEpochOptComp queries_spqrAddEpochOptComp cost_spqrAddEpochOptComp
  eval_spqrAddEpochOptComp)
open Computational.Proofs.E2E.Dsl.SpqrSimHist (comp_eval_ret comp_eval_bind_ret
  comp_eval_bind_pure comp_eval_ite_true comp_eval_ite_false
  comp_eval_caseOpt_none comp_eval_caseOpt_some
  spqrChainRecvKeyComp queries_spqrChainRecvKeyComp cost_spqrChainRecvKeyComp
  eval_spqrChainRecvKeyComp recvKey_out_empty_or_32)
open CryptoVerification.LibsignalSpqrV1 (MlKem Direction Version V1State Chain EpochSecret States
  Message msgPreamble MsgPreamble stateVersion spqrPolyApi spqrAuthApi spqrDeps spqrHkdfWith
  spqrV1 spqrV1_eq spqrV1Assembled toSpqrModel recvPanicsB messageKeyToSalt? recvKeyToSalt?
  recvKeyToSalt?_of_ne SpqrApiResult SpqrApiError spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.InSync (St)
open CryptoVerification.SpqrV1Sync.ChainSync (ChainOk chainOk_congr addEpoch_ok)
open CryptoVerification.SpqrV1Sync.TopSync (topPb topBytes vnOf SendPrevNil decodeState_topBytes
  recv_topBytes recvEqual chainCur chainCur_recv_none chainCur_recv_key
  addEpoch_sendPrevNil recvKey_sendPrevNil partyTop_epoch_pos)
open CryptoVerification.SpqrV1Sync.SendTotal (TopWitness TopStateTight TopStateTightW
  RecvSmallTight BPhiStmt isEkSide topStateW_length_lt st_bCodec st_bPhi
  st_bRecvCt_tight st_bRecvEk_tight st_chainFrom_ok st_chainRecv_tight st_recvSmallAdd_tight
  treq_recv_epoch_le treq_spqrDeps_statesFromPb treq_statesRecv_ok)

/-! ## Receive sub-computations -/

@[reducible] def spqrPreambleT {ℓ : ℕ} : Ty (e2eSig ℓ) :=
  .prod U8 (.prod U64 (.prod U32 (B 32)))

def spqrRecvGreaterComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (parts : Expr (e2eOps ℓ P C K decT encT) Γ spqrStatePartsT)
    (msgIdx : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    Comp (e2eOps ℓ P C K decT encT) I Γ (.opt (.prod (B 32) (.opt BV256))) :=
  .bind (.ret (.pair parts msgIdx))
    (.bind (spqrResolveChainComp I (.fst (.snd (.fst .v0))) (.snd (.snd (.fst .v0))))
      (.caseOpt .v0
        (.ret .none)
        (.bind (spqrChainRecvKeyComp I .v0 (e2ePureOp (.u64Lit 0#64) .unit) (.snd .v2))
          (.caseOpt .v0
            (.ret .none)
            (.ret (.some (.pair
              (e2ePureOp .spqrStateJoin
                (.pair (.fst (.fst .v4))
                  (.pair (.fst (.snd (.fst .v4))) (.some (.fst .v0)))))
              (.snd .v0))))))))

theorem queries_spqrRecvGreaterComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (parts : Expr (e2eOps ℓ P C K decT encT) Γ spqrStatePartsT)
    (msgIdx : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    (spqrRecvGreaterComp I parts msgIdx).queries w ws = 0 := by
  simp [spqrRecvGreaterComp, Comp.queries, queries_spqrResolveChainComp,
    queries_spqrChainRecvKeyComp]

theorem cost_spqrRecvGreaterComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (parts : Expr (e2eOps ℓ P C K decT encT) Γ spqrStatePartsT)
    (msgIdx : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    (spqrRecvGreaterComp I parts msgIdx).cost ≤ parts.cost + msgIdx.cost + 3992000 := by
  let Γ1 : List (Ty (e2eSig ℓ)) := .prod spqrStatePartsT U32 :: Γ
  let Γ3 : List (Ty (e2eSig ℓ)) := spqrChainT :: .opt spqrChainT :: Γ1
  have hc1 := cost_spqrResolveChainComp (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ1) I (.fst (.snd (.fst .v0))) (.snd (.snd (.fst .v0)))
  have hc2 := cost_spqrChainRecvKeyComp (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ3) I .v0 (e2ePureOp (.u64Lit 0#64) .unit) (.snd .v2)
  dsimp only [Γ1, Γ3] at hc1 hc2
  simp only [Expr.cost, cost_e2ePureOp, E2EPureOp.cost, Expr.v0, Expr.v2] at hc1 hc2
  simp only [spqrRecvGreaterComp, Comp.cost, Expr.cost, cost_e2ePureOp, E2EPureOp.cost,
    Expr.v0, Expr.v2, Expr.v4]
  omega

def spqrRecvPrepStateComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (parts : Expr (e2eOps ℓ P C K decT encT) Γ spqrStatePartsT)
    (msgVer curVer : Expr (e2eOps ℓ P C K decT encT) Γ U8)
    (stillNeg : Expr (e2eOps ℓ P C K decT encT) Γ .bool) :
    Comp (e2eOps ℓ P C K decT encT) I Γ (.opt spqrStatePartsT) :=
  .bind (.ret (.pair parts (.pair msgVer (.pair curVer stillNeg))))
    (.ite (e2ePureOp .u8Eq (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
      (.ret (.some (.fst .v0)))
      (.ite (.not (.and
          (e2ePureOp .u8Lt (.pair (e2ePureOp (.u8Lit 0#8) .unit) (.fst (.snd (.snd .v0)))))
          (.snd (.snd (.snd .v0)))))
        (.ret .none)
        (.caseOpt (.fst (.snd (.fst .v0)))
          (.ret .none)
          (.bind (spqrNegotiateInitC I
              (.pair (.fst (.snd .v1)) (.pair (.fst (.snd .v0)) (.fst .v0))))
            (.caseOpt (.snd .v0)
              (.ret .none)
              (.bind (spqrResolveChainComp I (.some .v2) (.snd (.snd (.fst .v3))))
                (.caseOpt .v0
                  (.ret .none)
                  (.ret (.some (.pair .v2 (.pair .none (.some .v0))))))))))))

theorem queries_spqrRecvPrepStateComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (parts : Expr (e2eOps ℓ P C K decT encT) Γ spqrStatePartsT)
    (msgVer curVer : Expr (e2eOps ℓ P C K decT encT) Γ U8)
    (stillNeg : Expr (e2eOps ℓ P C K decT encT) Γ .bool) :
    (spqrRecvPrepStateComp I parts msgVer curVer stillNeg).queries w ws = 0 := by
  simp [spqrRecvPrepStateComp, Comp.queries, queries_spqrResolveChainComp]

theorem cost_spqrRecvPrepStateComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (parts : Expr (e2eOps ℓ P C K decT encT) Γ spqrStatePartsT)
    (msgVer curVer : Expr (e2eOps ℓ P C K decT encT) Γ U8)
    (stillNeg : Expr (e2eOps ℓ P C K decT encT) Γ .bool) :
    (spqrRecvPrepStateComp I parts msgVer curVer stillNeg).cost ≤
      parts.cost + msgVer.cost + curVer.cost + stillNeg.cost + 1700 := by
  let argsT : Ty (e2eSig ℓ) := .prod spqrStatePartsT (.prod U8 (.prod U8 .bool))
  let negT : Ty (e2eSig ℓ) := .prod .bool (.opt (.opt (B 32)))
  let Γ4 : List (Ty (e2eSig ℓ)) := .opt (B 32) :: negT :: spqrVnT :: argsT :: Γ
  have hcRes := cost_spqrResolveChainComp (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ4) I (.some .v2) (.snd (.snd (.fst .v3)))
  dsimp only [Γ4, negT, argsT] at hcRes
  simp only [Expr.cost, Expr.v2, Expr.v3] at hcRes
  simp only [spqrRecvPrepStateComp, Comp.cost, cost_spqrNegotiateInitC, Expr.cost,
    cost_e2ePureOp, E2EPureOp.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3]
  omega

def spqrRunRecvChainComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (vn? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt spqrVnT))
    (ch? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt spqrChainT))
    (epSec? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (.prod U64 BV256)))
    (msgEpoch : Expr (e2eOps ℓ P C K decT encT) Γ U64)
    (msgIdx : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    Comp (e2eOps ℓ P C K decT encT) I Γ (.opt (.prod spqrChainT (.opt BV256))) :=
  .bind (.ret (.pair (.pair vn? ch?) (.pair epSec? (.pair msgEpoch msgIdx))))
    (.ite (e2ePureOp .u64Eq
        (.pair (.fst (.snd (.snd .v0))) (e2ePureOp (.u64Lit 0#64) .unit)))
      (.ret .none)
      (.bind (spqrResolveChainComp I (.fst (.fst .v0)) (.snd (.fst .v0)))
        (.caseOpt .v0
          (.ret .none)
          (.bind (spqrAddEpochOptComp I .v0 (.fst (.snd .v2)))
            (.caseOpt .v0
              (.ret .none)
              (spqrChainRecvKeyComp I .v0
                (e2ePureOp .u64Sub
                  (.pair (.fst (.snd (.snd .v4))) (e2ePureOp (.u64Lit 1#64) .unit)))
                (.snd (.snd (.snd .v4)))))))))

theorem queries_spqrRunRecvChainComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (vn? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt spqrVnT))
    (ch? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt spqrChainT))
    (epSec? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (.prod U64 BV256)))
    (msgEpoch : Expr (e2eOps ℓ P C K decT encT) Γ U64)
    (msgIdx : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    (spqrRunRecvChainComp I vn? ch? epSec? msgEpoch msgIdx).queries w ws = 0 := by
  simp [spqrRunRecvChainComp, Comp.queries, queries_spqrResolveChainComp,
    queries_spqrAddEpochOptComp, queries_spqrChainRecvKeyComp]

theorem cost_spqrRunRecvChainComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (vn? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt spqrVnT))
    (ch? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt spqrChainT))
    (epSec? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (.prod U64 BV256)))
    (msgEpoch : Expr (e2eOps ℓ P C K decT encT) Γ U64)
    (msgIdx : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    (spqrRunRecvChainComp I vn? ch? epSec? msgEpoch msgIdx).cost ≤
      vn?.cost + ch?.cost + epSec?.cost + msgEpoch.cost + msgIdx.cost + 3981000 := by
  let argsT : Ty (e2eSig ℓ) :=
    .prod (.prod (.opt spqrVnT) (.opt spqrChainT))
      (.prod (.opt (.prod U64 BV256)) (.prod U64 U32))
  let Γ1 : List (Ty (e2eSig ℓ)) := argsT :: Γ
  let Γ3 : List (Ty (e2eSig ℓ)) := spqrChainT :: .opt spqrChainT :: Γ1
  let Γ5 : List (Ty (e2eSig ℓ)) := spqrChainT :: .opt spqrChainT :: Γ3
  have hc1 := cost_spqrResolveChainComp (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ1) I (.fst (.fst .v0)) (.snd (.fst .v0))
  have hc2 := cost_spqrAddEpochOptComp (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ3) I .v0 (.fst (.snd .v2))
  have hc3 := cost_spqrChainRecvKeyComp (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ5) I .v0
    (e2ePureOp .u64Sub (.pair (.fst (.snd (.snd .v4))) (e2ePureOp (.u64Lit 1#64) .unit)))
    (.snd (.snd (.snd .v4)))
  dsimp only [Γ1, Γ3, Γ5, argsT] at hc1 hc2 hc3
  simp only [Expr.cost, cost_e2ePureOp, E2EPureOp.cost, Expr.v0, Expr.v2, Expr.v4] at hc1 hc2 hc3
  simp only [spqrRunRecvChainComp, Comp.cost, Expr.cost, cost_e2ePureOp, E2EPureOp.cost,
    Expr.v0, Expr.v2, Expr.v4]
  omega

def spqrRecvV1BodyComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (stateParts : Expr (e2eOps ℓ P C K decT encT) Γ spqrStatePartsT)
    (msgEp : Expr (e2eOps ℓ P C K decT encT) Γ U64)
    (msgIdx : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (msgRem : Expr (e2eOps ℓ P C K decT encT) Γ (B 32)) :
    Comp (e2eOps ℓ P C K decT encT) I Γ (.opt (.prod (B 32) (.opt BV256))) :=
  .bind (.ret (.pair stateParts (.pair msgEp (.pair msgIdx msgRem))))
    (.caseOpt (.fst (.fst .v0))
      (.ret (.some (.pair (e2ePureOp (.bytesLit 32 []) .unit) .none)))
      (.bind
        (spqrBraidRecvC I
          (.pair .v0 (.pair (.fst (.snd .v1)) (.snd (.snd (.snd .v1))))))
        (.caseOpt (.snd (.snd .v0))
          (.ret .none)
          (.bind
            (spqrRunRecvChainComp I
              (.fst (.snd (.fst .v3)))
              (.snd (.snd (.fst .v3)))
              (.fst .v0)
              (.fst (.snd .v3))
              (.fst (.snd (.snd .v3))))
            (.caseOpt .v0
              (.ret .none)
              (.ret (.some (.pair
                (e2ePureOp .spqrStateJoin
                  (.pair (.some (.snd .v2))
                    (.pair .none (.some (.fst .v0)))))
                (.snd .v0)))))))))

theorem queries_spqrRecvV1BodyComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (stateParts : Expr (e2eOps ℓ P C K decT encT) Γ spqrStatePartsT)
    (msgEp : Expr (e2eOps ℓ P C K decT encT) Γ U64)
    (msgIdx : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (msgRem : Expr (e2eOps ℓ P C K decT encT) Γ (B 32)) :
    (spqrRecvV1BodyComp I stateParts msgEp msgIdx msgRem).queries w ws = 0 := by
  simp [spqrRecvV1BodyComp, Comp.queries, queries_spqrRunRecvChainComp]

theorem cost_spqrRecvV1BodyComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (stateParts : Expr (e2eOps ℓ P C K decT encT) Γ spqrStatePartsT)
    (msgEp : Expr (e2eOps ℓ P C K decT encT) Γ U64)
    (msgIdx : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (msgRem : Expr (e2eOps ℓ P C K decT encT) Γ (B 32)) :
    (spqrRecvV1BodyComp I stateParts msgEp msgIdx msgRem).cost ≤
      stateParts.cost + msgEp.cost + msgIdx.cost + msgRem.cost + 3996000 := by
  let argsT : Ty (e2eSig ℓ) := .prod spqrStatePartsT (.prod U64 (.prod U32 (B 32)))
  let braidOutT : Ty (e2eSig ℓ) := .prod (.opt (.prod U64 BV256)) (B 32)
  let braidResT : Ty (e2eSig ℓ) := .prod .bool (.prod .bool (.opt braidOutT))
  let Γ4 : List (Ty (e2eSig ℓ)) := braidOutT :: braidResT :: B 32 :: argsT :: Γ
  have hcRun := cost_spqrRunRecvChainComp (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ4) I
    (.fst (.snd (.fst .v3)))
    (.snd (.snd (.fst .v3)))
    (.fst .v0)
    (.fst (.snd .v3))
    (.fst (.snd (.snd .v3)))
  have hp32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  dsimp only [Γ4, braidOutT, braidResT, argsT] at hcRun
  simp only [Expr.cost, Expr.v0, Expr.v3] at hcRun
  simp only [spqrRecvV1BodyComp, Comp.cost, cost_spqrBraidRecvC, Expr.cost, cost_e2ePureOp,
    E2EPureOp.cost, hp32, List.length_nil, Expr.v0, Expr.v1, Expr.v2, Expr.v3]
  omega

/-! ## Full `recv` simulation -/

/-- Simulates `(spqrV1SessionUniformCoins C.F K).recv` in `ReductionDsl`. -/
def spqrRecvComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) (B 32))) :
    Comp (e2eOps ℓ P C K decT encT) I Γ (.opt (.prod (B 32) (.opt BV256))) :=
  .bind (.ret e)
    (.caseOpt (e2ePureOp .spqrParsePreamble (.snd .v0))
      (.ret .none)
      (.caseOpt (e2ePureOp .spqrStateSplit (.fst .v1))
        (.ret .none)
        (.bind
          (.ret
            (.letE
              (.caseOpt (.fst .v0)
                (e2ePureOp (.u8Lit 0#8) .unit)
                (e2ePureOp (.u8Lit 1#8) .unit))
              (.pair .v0
                (.caseOpt (.fst (.snd .v1))
                  (.pair .v0
                    (e2ePureOp .u8Eq (.pair .v0 (e2ePureOp (.u8Lit 0#8) .unit))))
                  (.pair
                    (e2ePureOp .u8OfNat (e2ePureOp .u32ToNat (.fst (.snd (.snd .v0)))))
                    (.bool true))))))
          (.ite (e2ePureOp .u8Lt (.pair (.fst .v2) (.fst (.snd .v0))))
            (.ret .none)
            (.ite (.and
                (.not (e2ePureOp .u8Eq (.pair (.fst .v2) (.fst .v0))))
                (.not (.snd (.snd .v0))))
              (.ret .none)
              (.ite (e2ePureOp .u8Eq (.pair (.fst .v0) (e2ePureOp (.u8Lit 0#8) .unit)))
                (.ret (.some (.pair (e2ePureOp (.bytesLit 32 []) .unit) .none)))
                (.ite (e2ePureOp .u8Lt (.pair (.fst .v0) (.fst .v2)))
                  (spqrRecvGreaterComp I .v1 (.fst (.snd (.snd .v2))))
                  (.bind
                    (spqrRecvPrepStateComp I .v1 (.fst .v2) (.fst .v0) (.snd (.snd .v0)))
                    (.caseOpt .v0
                      (.ret .none)
                      (spqrRecvV1BodyComp I .v0
                        (.fst (.snd .v4))
                        (.fst (.snd (.snd .v4)))
                        (.snd (.snd (.snd .v4)))))))))))))

theorem spqrRecvComp_cost {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) (B 32))) :
    (spqrRecvComp I e).cost ≤ e.cost + 4100000 := by
  let hdrT : Ty (e2eSig ℓ) := .prod U8 (.prod U8 .bool)
  let Γhdr : List (Ty (e2eSig ℓ)) :=
    hdrT :: spqrStatePartsT :: spqrPreambleT :: .prod (B 32) (B 32) :: Γ
  let Γbody : List (Ty (e2eSig ℓ)) := spqrStatePartsT :: .opt spqrStatePartsT :: Γhdr
  have hcG := cost_spqrRecvGreaterComp (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γhdr) I .v1 (.fst (.snd (.snd .v2)))
  have hcP := cost_spqrRecvPrepStateComp (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γhdr) I .v1 (.fst .v2) (.fst .v0) (.snd (.snd .v0))
  have hcB := cost_spqrRecvV1BodyComp (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γbody) I .v0
    (.fst (.snd .v4)) (.fst (.snd (.snd .v4))) (.snd (.snd (.snd .v4)))
  have hp32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  dsimp only [Γbody, Γhdr, hdrT] at hcG hcP hcB
  simp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v4] at hcG hcP hcB
  simp only [spqrRecvComp, Comp.cost, Expr.cost, cost_e2ePureOp, E2EPureOp.cost, hp32,
    List.length_nil, Expr.v0, Expr.v1, Expr.v2, Expr.v4]
  omega

theorem spqrRecvComp_queries {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) (B 32)))
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (spqrRecvComp I e).queries w ws = 0 := by
  simp [spqrRecvComp, Comp.queries, queries_spqrRecvGreaterComp,
    queries_spqrRecvPrepStateComp, queries_spqrRecvV1BodyComp]

/-! ## Evaluation equivalence -/

private theorem spqrUniform_recv_rhs (F : ShaCompress) (K : MlKem) (pq pqMsg : Bytes) :
    (let spqr := spqrV1SessionUniformCoins F K
     if spqr.recvPanics pq pqMsg then none
     else match spqr.recv pq pqMsg with
       | .ok (pq', saltVec?) =>
         some (pq', saltVec?.map (fun v => bytesToKey32 v.toList))
       | .error _ => none) =
    match CryptoVerification.LibsignalSpqrV1.recv (spqrDeps F K) (spqrHkdfWith F) pq pqMsg with
    | .ok r =>
      match recvKeyToSalt? r.key with
      | some saltVec? =>
        some (r.state, saltVec?.map (fun v => bytesToKey32 v.toList))
      | none => none
    | .error _ => none := by
  dsimp only [spqrV1SessionUniformCoins, SpqrModel.spqrWith]
  rw [spqrV1_eq]
  dsimp only [toSpqrModel, spqrV1Assembled, recvPanicsB]
  suffices ∀ res : SpqrApiResult CryptoVerification.LibsignalSpqrV1.Recv,
      (if (match res with
          | .ok _ => false
          | .error (.err _) => false
          | .error (.panic _) => true) = true then none
       else
         match (match res with
           | .ok r =>
             match recvKeyToSalt? r.key with
             | some salt => Except.ok (r.state, salt)
             | none => Except.error false
           | .error (.err e) => Except.error e.isStateDecode
           | .error (.panic _) => Except.error false) with
         | Except.ok (pq', saltVec?) =>
           some (pq', saltVec?.map (fun v => bytesToKey32 v.toList))
         | Except.error _ => none) =
      match res with
      | .ok r =>
        match recvKeyToSalt? r.key with
        | some saltVec? =>
          some (r.state, saltVec?.map (fun v => bytesToKey32 v.toList))
        | none => none
      | .error _ => none from this _
  intro res
  cases res with
  | error err => cases err <;> rfl
  | ok r =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases recvKeyToSalt? r.key <;> rfl

private theorem recvKeyToSalt_some_eq (stBytes : Bytes) {rawKey : Bytes}
    (h : rawKey = [] ∨ rawKey.length = 32) :
    (match recvKeyToSalt? (some rawKey) with
     | some saltVec? =>
       some (stBytes, saltVec?.map (fun v => bytesToKey32 v.toList))
     | none => none) =
    some (stBytes, if rawKey.isEmpty then none else some (bytesToKey32 rawKey)) := by
  rcases h with rfl | h32
  · rfl
  · have hemp : rawKey.isEmpty = false := by
      cases rawKey with
      | nil => cases h32
      | cons _ _ => rfl
    have hms : messageKeyToSalt? (some rawKey) =
        some (some (⟨rawKey, h32⟩ : List.Vector (BitVec 8) 32)) := by
      simp only [messageKeyToSalt?, h32, ↓reduceDIte]
      rfl
    have hrk : recvKeyToSalt? (some rawKey) =
        some (some (⟨rawKey, h32⟩ : List.Vector (BitVec 8) 32)) := by
      rw [recvKeyToSalt?_of_ne]
      · exact hms
      · rintro h
        injection h with hk
        rw [hk] at h32
        cases h32
    rw [hrk, hemp]
    rfl

private theorem recvKeyToSalt_ite_eq (stBytes : Bytes) {msgKey : Bytes}
    (h : msgKey = [] ∨ msgKey.length = 32) :
    (match recvKeyToSalt? (if msgKey.isEmpty then none else some msgKey) with
     | some saltVec? =>
       some (stBytes, saltVec?.map (fun v => bytesToKey32 v.toList))
     | none => none) =
    some (stBytes, if msgKey.isEmpty then none else some (bytesToKey32 msgKey)) := by
  rcases h with rfl | h32
  · rfl
  · have hemp : msgKey.isEmpty = false := by
      cases msgKey with
      | nil => cases h32
      | cons _ _ => rfl
    simpa [hemp] using recvKeyToSalt_some_eq stBytes (Or.inr h32)

private def addEpochSecretRecv (secret : ℕ → Bytes) (cur : ℕ) :
    Option EpochSecret → ℕ → Bytes
  | none => secret
  | some es => Function.update secret (cur + 1) es.secret

private theorem recv_addEpoch_tight_facts (F : ShaCompress) (K : MlKem) (authKey : Bytes)
    (dir : Direction) (secret : ℕ → Bytes) (st st' : St F) (sendCtr : ℕ → ℕ)
    (recvSet : ℕ → Finset ℕ) (chE : Chain)
    (hok : ChainOk F authKey dir secret sendCtr recvSet chE)
    (hcur : chE.currentEpoch.toNat = chainCur st) (hep_pos : 1 ≤ st.epoch.toNat)
    (hsmall : RecvSmallTight chE) (hsp : SendPrevNil chE)
    (hlen3 : chE.links.length ≤ 3)
    (m : Message spqrPolyApi) (key : Option EpochSecret)
    (hrecvB : st.recv K m = .ok { key := key, state := st' }) :
    let secret1 := addEpochSecretRecv secret chE.currentEpoch.toNat key
    ∃ chain1 : Chain,
      ChainOk F authKey dir secret1 sendCtr recvSet chE ∧
      (match key with
       | some es => chE.addEpoch (spqrHkdfWith F) es
       | none => .ok chE) = .ok chain1 ∧
      (match key with
       | some es => SpqrApiResult.ofChainPanic (chE.addEpoch (spqrHkdfWith F) es)
       | none => pure chE) = .ok chain1 ∧
      ChainOk F authKey dir secret1 sendCtr recvSet chain1 ∧
      chain1.currentEpoch.toNat = chainCur st' ∧
      chain1.sendEpoch = chE.sendEpoch ∧
      RecvSmallTight chain1 ∧
      SendPrevNil chain1 ∧
      chain1.links.length ≤ 4 := by
  intro secret1
  cases key with
  | none =>
    have hc := chainCur_recv_none F K st st' m hep_pos hrecvB
    exact ⟨chE, hok, rfl, rfl, hok, by rw [hcur, hc], rfl, hsmall, hsp, by omega⟩
  | some es =>
    obtain ⟨hes_ep, hc'⟩ := chainCur_recv_key F K st st' m es hep_pos hrecvB
    have hep : es.epoch.toNat = chE.currentEpoch.toNat + 1 := by omega
    have hok0 : ChainOk F authKey dir secret1 sendCtr recvSet chE :=
      chainOk_congr F authKey dir secret secret1 sendCtr recvSet chE hok
        (fun _ _ _ => Function.update_of_ne (by omega) _ _)
    have hsec1 : es.secret = secret1 (chE.currentEpoch.toNat + 1) :=
      (Function.update_self (chE.currentEpoch.toNat + 1) es.secret secret).symm
    obtain ⟨ch1, hadd, hcur1, hsend1, hok1⟩ :=
      addEpoch_ok F authKey dir secret1 sendCtr recvSet chE hok0 es hep hsec1
    have hlen4 : ch1.links.length ≤ 4 := by
      have hadd' := hadd
      unfold Chain.addEpoch at hadd'
      split_ifs at hadd'
      injection hadd' with hc_eq
      subst hc_eq
      simp only [List.length_append, List.length_singleton]
      omega
    refine ⟨ch1, hok0, hadd, ?_, hok1, ?_, hsend1, st_recvSmallAdd_tight hsmall hadd,
      addEpoch_sendPrevNil (spqrHkdfWith F) chE ch1 es hsp hadd, hlen4⟩
    · simp [hadd, SpqrApiResult.ofChainPanic]
    · rw [hcur1, hes_ep, hc']

private theorem eval_spqrRecvPrepStateComp_eq {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (parts : Expr (e2eOps ℓ P C K decT encT) Γ spqrStatePartsT)
    (msgVer curVer : Expr (e2eOps ℓ P C K decT encT) Γ U8)
    (stillNeg : Expr (e2eOps ℓ P C K decT encT) Γ .bool)
    (ρ : Env Γ) (heq : msgVer.eval ρ = curVer.eval ρ) :
    (spqrRecvPrepStateComp I parts msgVer curVer stillNeg).eval ρ =
      pure (some (parts.eval ρ)) := by
  unfold spqrRecvPrepStateComp
  rw [comp_eval_bind_ret]
  have hc :
      (e2ePureOp (P := P) (C := C) (K := K) (decT := decT) (encT := encT) .u8Eq
        (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0))))).eval
        (Env.cons
          ((Expr.pair parts (.pair msgVer (.pair curVer stillNeg))).eval ρ) ρ) = true := by
    simp only [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Env.get, heq, beq_self_eq_true]
  rw [comp_eval_ite_true _ _ _ _ hc, comp_eval_ret]
  simp only [Expr.eval, Expr.v0, Env.get]

private theorem eval_spqrRecvGreaterComp_topStateTightW {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (partsExpr : Expr (e2eOps ℓ P C K decT encT) Γ spqrStatePartsT)
    (idxExpr : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (ρ : Env Γ) {pq : Bytes} {w : TopWitness C.F} (hw : TopStateTightW C.F K pq w)
    (hvn_some : w.vn? = some (vnOf w.dir w.authKey))
    (hparts : partsExpr.eval ρ =
      (some (V1State.encodeRaw w.st.into_pb),
       (w.vn?.map (spqrVnToV (ℓ := ℓ)),
        (w.ch?.map Chain.intoPb).map (spqrChainToV (ℓ := ℓ))))) :
    (spqrRecvGreaterComp I partsExpr idxExpr).eval ρ =
      pure (match w.chE.recvKey (spqrHkdfWith C.F) 0#64 (idxExpr.eval ρ) with
        | .ok (chain1, rawKey) =>
          some (topBytes C.F K w.st (some (vnOf w.dir w.authKey)) (some chain1),
            if rawKey.isEmpty then none else some (bytesToKey32 rawKey))
        | .error _ => none) := by
  have hlen3 := topStateTightW_links_le_three C.F K hw
  unfold spqrRecvGreaterComp
  rw [comp_eval_bind_ret]
  let partsV : (spqrStatePartsT (ℓ := ℓ)).denote :=
    (some (V1State.encodeRaw w.st.into_pb),
     (w.vn?.map (spqrVnToV (ℓ := ℓ)),
      (w.ch?.map Chain.intoPb).map (spqrChainToV (ℓ := ℓ))))
  let idxV := idxExpr.eval ρ
  let ρ1 : Env (.prod spqrStatePartsT U32 :: Γ) :=
    Env.cons (t := .prod spqrStatePartsT U32) (partsV, idxV) ρ
  have hp_eq : (Expr.pair partsExpr idxExpr).eval ρ = (partsV, idxV) := by
    simp only [Expr.eval, hparts, partsV, idxV]
  rw [hp_eq]
  have hres :
      (spqrResolveChainComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I
        (.fst (.snd (.fst .v0))) (.snd (.snd (.fst .v0)))).eval ρ1 =
        pure (some (spqrChainToV (ℓ := ℓ) w.chE.intoPb)) :=
    eval_spqrResolveChainComp_topStateTightW (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) I _ _ ρ1 hw
      (by dsimp only [ρ1, partsV]; simp only [Expr.eval, Expr.v0, Env.get])
      (by dsimp only [ρ1, partsV]; simp only [Expr.eval, Expr.v0, Env.get])
  rw [comp_eval_bind_pure _ _ _ _ hres, comp_eval_caseOpt_some _ _ _ _ rfl]
  let ρ3 : Env (spqrChainT :: .opt spqrChainT :: .prod spqrStatePartsT U32 :: Γ) :=
    Env.cons (t := spqrChainT) (spqrChainToV (ℓ := ℓ) w.chE.intoPb)
      (Env.cons (t := .opt spqrChainT) (some (spqrChainToV (ℓ := ℓ) w.chE.intoPb)) ρ1)
  have hrk := eval_spqrChainRecvKeyComp (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) I .v0 (e2ePureOp (.u64Lit 0#64) .unit) (.snd .v2)
    ρ3 w.authKey w.dir w.secret w.sendCtr w.recvSet w.chE hw.htop.hok hw.hsmall (by omega)
    (by dsimp only [ρ3]; simp only [Expr.eval, Expr.v0, Env.get])
  have he0 :
      (e2ePureOp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        (.u64Lit 0#64) .unit).eval ρ3 = 0#64 := rfl
  have hi0 :
      (Expr.snd (O := e2eOps ℓ P C K decT encT) .v2).eval ρ3 = idxV := rfl
  rw [he0, hi0] at hrk
  cases hck : w.chE.recvKey (spqrHkdfWith C.F) 0#64 idxV with
  | error _ =>
    rw [hck] at hrk
    rw [comp_eval_bind_pure _ _ _ _ hrk, comp_eval_caseOpt_none _ _ _ _ rfl, comp_eval_ret]
    rfl
  | ok cm =>
    rcases cm with ⟨chain1, rawKey⟩
    rw [hck] at hrk
    rw [comp_eval_bind_pure _ _ _ _ hrk, comp_eval_caseOpt_some _ _ _ _ rfl, comp_eval_ret]
    obtain ⟨recvSet', hok', hsmall', hcur', hsendEp'⟩ :=
      st_chainRecv_tight C.F hw.htop.hok hw.hsmall hck
    let w' : TopWitness C.F :=
      ⟨w.authKey, w.dir, w.secret, w.st, w.sendEp, w.sendCtr, recvSet',
        some (vnOf w.dir w.authKey), some chain1, chain1⟩
    have hw' :
        TopStateTightW C.F K (topBytes C.F K w.st (some (vnOf w.dir w.authKey)) (some chain1)) w' :=
      { htop :=
          { hbytes := rfl
            hvn := Or.inr rfl
            hch := Or.inl rfl
            hok := hok'
            hcur := by rw [hcur', hw.htop.hcur]
            hsendEp := by rw [hsendEp', hw.htop.hsendEp]
            hsendLe := hw.htop.hsendLe
            hsendPrev := recvKey_sendPrevNil (spqrHkdfWith C.F) w.chE chain1 0#64 idxV rawKey
              hw.htop.hsendPrev hck }
        hauth := hw.hauth
        hbok := hw.hbok
        hphi := hw.hphi
        hsmall := hsmall' }
    have hjoin := spqrJoinEval_topStateTightW (ℓ := ℓ) C.F K hw'
    dsimp only [w', Option.map] at hjoin
    dsimp only [ρ3, ρ1, partsV]
    simp only [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Expr.v4, Env.get, hvn_some,
      Option.map, hjoin]

private theorem eval_spqrRunRecvChainComp_of_chain1 {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (vnExpr : Expr (e2eOps ℓ P C K decT encT) Γ (.opt spqrVnT))
    (chExpr : Expr (e2eOps ℓ P C K decT encT) Γ (.opt spqrChainT))
    (epSecExpr : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (.prod U64 BV256)))
    (epExpr : Expr (e2eOps ℓ P C K decT encT) Γ U64)
    (idxExpr : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (ρ : Env Γ) {pq : Bytes} {w : TopWitness C.F}
    (hw : TopStateTightW C.F K pq w)
    (secret1 : ℕ → Bytes) (key : Option EpochSecret) (chain1 : Chain)
    (hok0 : ChainOk C.F w.authKey w.dir secret1 w.sendCtr w.recvSet w.chE)
    (hok1 : ChainOk C.F w.authKey w.dir secret1 w.sendCtr w.recvSet chain1)
    (hsmall1 : RecvSmallTight chain1)
    (hlen4 : chain1.links.length ≤ 4)
    (hadd : (match key with
      | some es => w.chE.addEpoch (spqrHkdfWith C.F) es
      | none => .ok w.chE) = .ok chain1)
    (hsec_len : ∀ es, key = some es → es.secret.length = 32)
    (he_ne0 : (epExpr.eval ρ == 0#64) = false)
    (hvn : vnExpr.eval ρ = w.vn?.map (spqrVnToV (ℓ := ℓ)))
    (hch : chExpr.eval ρ = (w.ch?.map Chain.intoPb).map (spqrChainToV (ℓ := ℓ)))
    (hkey : epSecExpr.eval ρ = key.map (fun es => (es.epoch, bytesToKey32 es.secret))) :
    (spqrRunRecvChainComp I vnExpr chExpr epSecExpr epExpr idxExpr).eval ρ =
      pure (match chain1.recvKey (spqrHkdfWith C.F) (epExpr.eval ρ - 1#64) (idxExpr.eval ρ) with
        | .ok (ch2, msgKey) =>
          some (spqrChainToV (ℓ := ℓ) ch2.intoPb,
            if msgKey.isEmpty then none else some (bytesToKey32 msgKey))
        | .error _ => none) := by
  have hlen3 := topStateTightW_links_le_three C.F K hw
  let argsT : Ty (e2eSig ℓ) :=
    .prod (.prod (.opt spqrVnT) (.opt spqrChainT))
      (.prod (.opt (.prod U64 BV256)) (.prod U64 U32))
  let epV := epExpr.eval ρ
  let idxV := idxExpr.eval ρ
  let argsV : argsT.denote :=
    ((w.vn?.map (spqrVnToV (ℓ := ℓ)),
      (w.ch?.map Chain.intoPb).map (spqrChainToV (ℓ := ℓ))),
     (key.map (fun es => (es.epoch, bytesToKey32 es.secret)), (epV, idxV)))
  let ρ1 : Env (argsT :: Γ) := Env.cons (t := argsT) argsV ρ
  have hargs :
      (Expr.pair (.pair vnExpr chExpr) (.pair epSecExpr (.pair epExpr idxExpr))).eval ρ = argsV := by
    simp only [Expr.eval, hvn, hch, hkey, argsV, epV, idxV]
  unfold spqrRunRecvChainComp
  rw [comp_eval_bind_ret, hargs]
  have hcond :
      (e2ePureOp (P := P) (C := C) (K := K) (decT := decT) (encT := encT) .u64Eq
        (.pair (.fst (.snd (.snd .v0))) (e2ePureOp (.u64Lit 0#64) .unit))).eval ρ1 = false := by
    dsimp only [ρ1, argsV]
    simpa [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Env.get, epV] using he_ne0
  rw [comp_eval_ite_false _ _ _ _ hcond]
  have hres :
      (spqrResolveChainComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I
        (.fst (.fst .v0)) (.snd (.fst .v0))).eval ρ1 =
        pure (some (spqrChainToV (ℓ := ℓ) w.chE.intoPb)) :=
    eval_spqrResolveChainComp_topStateTightW (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) I _ _ ρ1 hw
      (by dsimp only [ρ1, argsV]; simp only [Expr.eval, Expr.v0, Env.get])
      (by dsimp only [ρ1, argsV]; simp only [Expr.eval, Expr.v0, Env.get])
  rw [comp_eval_bind_pure _ _ _ _ hres, comp_eval_caseOpt_some _ _ _ _ rfl]
  let ρ3 : Env (spqrChainT :: .opt spqrChainT :: argsT :: Γ) :=
    Env.cons (t := spqrChainT) (spqrChainToV (ℓ := ℓ) w.chE.intoPb)
      (Env.cons (t := .opt spqrChainT) (some (spqrChainToV (ℓ := ℓ) w.chE.intoPb)) ρ1)
  have hadd_eval :
      (spqrAddEpochOptComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I
        .v0 (.fst (.snd .v2))).eval ρ3 =
        pure (some (spqrChainToV (ℓ := ℓ) chain1.intoPb)) := by
    rw [eval_spqrAddEpochOptComp (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I _ _ ρ3 w.authKey w.dir secret1 w.sendCtr w.recvSet
      w.chE key hok0 hw.htop.hsendPrev hw.hsmall hlen3
      (by dsimp only [ρ3]; simp only [Expr.eval, Expr.v0, Env.get])
      (by dsimp only [ρ3, ρ1, argsV]; simp only [Expr.eval, Expr.v2, Env.get]) hsec_len]
    cases key with
    | none =>
      cases hadd
      rfl
    | some es =>
      dsimp only at hadd ⊢
      rw [hadd]
  rw [comp_eval_bind_pure _ _ _ _ hadd_eval, comp_eval_caseOpt_some _ _ _ _ rfl]
  let ρ5 : Env (spqrChainT :: .opt spqrChainT :: spqrChainT :: .opt spqrChainT :: argsT :: Γ) :=
    Env.cons (t := spqrChainT) (spqrChainToV (ℓ := ℓ) chain1.intoPb)
      (Env.cons (t := .opt spqrChainT) (some (spqrChainToV (ℓ := ℓ) chain1.intoPb)) ρ3)
  have hrk := eval_spqrChainRecvKeyComp (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) I .v0
    (e2ePureOp .u64Sub (.pair (.fst (.snd (.snd .v4))) (e2ePureOp (.u64Lit 1#64) .unit)))
    (.snd (.snd (.snd .v4)))
    ρ5 w.authKey w.dir secret1 w.sendCtr w.recvSet chain1 hok1 hsmall1 hlen4
    (by dsimp only [ρ5]; simp only [Expr.eval, Expr.v0, Env.get])
  have hep5 :
      (e2ePureOp (P := P) (C := C) (K := K) (decT := decT) (encT := encT) .u64Sub
        (.pair (.fst (.snd (.snd .v4))) (e2ePureOp (.u64Lit 1#64) .unit))).eval ρ5 =
      epV - 1#64 := rfl
  have hidx5 :
      (Expr.snd (O := e2eOps ℓ P C K decT encT) (.snd (.snd .v4))).eval ρ5 = idxV := rfl
  rw [hep5, hidx5] at hrk
  exact hrk

private theorem eval_spqrRecvV1BodyComp_topStateTightW {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (partsExpr : Expr (e2eOps ℓ P C K decT encT) Γ spqrStatePartsT)
    (epExpr : Expr (e2eOps ℓ P C K decT encT) Γ U64)
    (idxExpr : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (remExpr : Expr (e2eOps ℓ P C K decT encT) Γ (B 32))
    (ρ : Env Γ) {pq : Bytes} {w : TopWitness C.F} (hw : TopStateTightW C.F K pq w)
    (pre : MsgPreamble)
    (hparts : partsExpr.eval ρ =
      (some (V1State.encodeRaw w.st.into_pb),
       (w.vn?.map (spqrVnToV (ℓ := ℓ)),
        (w.ch?.map Chain.intoPb).map (spqrChainToV (ℓ := ℓ)))))
    (hep : epExpr.eval ρ = pre.epoch)
    (hidx : idxExpr.eval ρ = pre.index)
    (hrem : remExpr.eval ρ = pre.remaining) :
    (spqrRecvV1BodyComp I partsExpr epExpr idxExpr remExpr).eval ρ =
      pure (match recvEqual C.F K w.st w.vn? w.ch? pre with
        | .ok r =>
          match recvKeyToSalt? r.key with
          | some saltVec? =>
            some (r.state, saltVec?.map (fun v => bytesToKey32 v.toList))
          | none => none
        | .error _ => none) := by
  have hPhi : BPhiStmt C.F K := st_bPhi C.F K
  have hcodec := treq_spqrDeps_statesFromPb C.F K w.st (st_bCodec C.F w.st hw.hbok.1)
  have hcf := st_chainFrom_ok C.F w.authKey w.dir w.secret w.sendCtr w.recvSet
    w.vn? w.ch? w.chE hw.htop.hch hw.htop.hok
  have hep_pos : 1 ≤ w.st.epoch.toNat := partyTop_epoch_pos ⟨w.vn?, w.ch?, w.chE, hw.htop⟩
  have hlen3 := topStateTightW_links_le_three C.F K hw
  let partsV : (spqrStatePartsT (ℓ := ℓ)).denote :=
    (some (V1State.encodeRaw w.st.into_pb),
     (w.vn?.map (spqrVnToV (ℓ := ℓ)),
      (w.ch?.map Chain.intoPb).map (spqrChainToV (ℓ := ℓ))))
  let argsT : Ty (e2eSig ℓ) := .prod spqrStatePartsT (.prod U64 (.prod U32 (B 32)))
  let argsV : argsT.denote := (partsV, (pre.epoch, (pre.index, pre.remaining)))
  have hargs :
      (Expr.pair partsExpr (.pair epExpr (.pair idxExpr remExpr))).eval ρ = argsV := by
    simp only [Expr.eval, hparts, hep, hidx, hrem, argsV, partsV]
  unfold spqrRecvV1BodyComp
  rw [comp_eval_bind_ret, hargs, comp_eval_caseOpt_some _ _ _ _ rfl]
  let ρ2 : Env (B 32 :: argsT :: Γ) :=
    Env.cons (t := B 32) (V1State.encodeRaw w.st.into_pb) (Env.cons (t := argsT) argsV ρ)
  have hbr := eval_spqrBraidRecvC (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) I
    (.pair .v0 (.pair (.fst (.snd .v1)) (.snd (.snd (.snd .v1))))) ρ2
  have hbr_arg :
      (Expr.pair (O := e2eOps ℓ P C K decT encT) .v0
        (.pair (.fst (.snd .v1)) (.snd (.snd (.snd .v1))))).eval ρ2 =
      (V1State.encodeRaw w.st.into_pb, (pre.epoch, pre.remaining)) := rfl
  rw [hbr_arg, spqrBraidRecvEval_of_bOkTight C.F K w.st hw.hbok pre.epoch pre.remaining] at hbr
  unfold recvEqual
  cases hdes : Message.deserialize spqrPolyApi pre.epoch pre.remaining with
  | error e =>
    rw [hdes] at hbr
    rw [comp_eval_bind_pure _ _ _ _ hbr, comp_eval_caseOpt_none _ _ _ _ rfl, comp_eval_ret]
    simp [spqrDeps, hdes, Bind.bind, Except.bind, Expr.eval]
  | ok sckaMsg =>
    rw [hdes] at hbr
    dsimp only at hbr
    have hdes_deps : (spqrDeps C.F K).msgDeserialize pre.epoch pre.remaining = .ok sckaMsg := by
      simp [spqrDeps, hdes]
    rw [hdes_deps]
    dsimp only [Bind.bind, Except.bind]
    rw [hcodec]
    dsimp only
    cases hrecvB : w.st.recv K sckaMsg with
    | error err =>
      rw [hrecvB] at hbr
      cases err with
      | panic _ =>
        rw [comp_eval_bind_pure _ _ _ _ hbr, comp_eval_caseOpt_none _ _ _ _ rfl, comp_eval_ret]
        simp [spqrDeps, hrecvB, Expr.eval]
      | err _ =>
        rw [comp_eval_bind_pure _ _ _ _ hbr, comp_eval_caseOpt_none _ _ _ _ rfl, comp_eval_ret]
        simp [spqrDeps, hrecvB, Expr.eval]
    | ok rOut =>
      rcases rOut with ⟨key, st'⟩
      rw [hrecvB] at hbr
      dsimp only at hbr
      have hsr_deps : (spqrDeps C.F K).statesRecv w.st sckaMsg = .ok (key, st') := by
        simp [spqrDeps, hrecvB]
      rw [hsr_deps]
      dsimp only
      rw [comp_eval_bind_pure _ _ _ _ hbr, comp_eval_caseOpt_some _ _ _ _ rfl]
      let braidOutT : Ty (e2eSig ℓ) := .prod (.opt (.prod U64 BV256)) (B 32)
      let braidResT : Ty (e2eSig ℓ) := .prod .bool (.prod .bool (.opt braidOutT))
      let braidOutV : braidOutT.denote :=
        (key.map (fun es => (es.epoch, bytesToKey32 es.secret)),
         V1State.encodeRaw st'.into_pb)
      let ρ4 : Env (braidOutT :: braidResT :: B 32 :: argsT :: Γ) :=
        Env.cons (t := braidOutT) braidOutV
          (Env.cons (t := braidResT) (false, (false, some braidOutV)) ρ2)
      by_cases he0 : (pre.epoch == 0#64) = true
      · simp only [he0, ↓reduceIte]
        have hrun0 :
            (spqrRunRecvChainComp (Pt := Pt) (P := P) (C := C) (K := K)
              (decT := decT) (encT := encT) I
              (.fst (.snd (.fst .v3)))
              (.snd (.snd (.fst .v3)))
              (.fst .v0)
              (.fst (.snd .v3))
              (.fst (.snd (.snd .v3)))).eval ρ4 = pure none := by
          unfold spqrRunRecvChainComp
          rw [comp_eval_bind_ret]
          refine (comp_eval_ite_true _ _ _ _ ?_).trans (comp_eval_ret _ _)
          dsimp only [ρ4, ρ2, argsV]
          simpa [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Expr.v3, Env.get] using he0
        rw [comp_eval_bind_pure _ _ _ _ hrun0, comp_eval_caseOpt_none _ _ _ _ rfl, comp_eval_ret]
        rfl
      · have he0_f : (pre.epoch == 0#64) = false := Bool.eq_false_iff.mpr he0
        simp only [he0_f, Bool.false_eq_true, ↓reduceIte]
        rw [hcf]
        dsimp only [SpqrApiResult.ofError]
        let secret1 := addEpochSecretRecv w.secret w.chE.currentEpoch.toNat key
        obtain ⟨chain1, hok0, hadd, hadd_api, hok1, hcur1, hsend1, hsmall1, hsp1, hlen4⟩ :=
          recv_addEpoch_tight_facts C.F K w.authKey w.dir w.secret w.st st'
            w.sendCtr w.recvSet w.chE hw.htop.hok hw.htop.hcur hep_pos hw.hsmall
            hw.htop.hsendPrev hlen3 sckaMsg key hrecvB
        have hsec_len : ∀ es, key = some es → es.secret.length = 32 := by
          intro es hk
          subst hk
          exact states_recv_secret_len C.F K hrecvB
        have hrun := eval_spqrRunRecvChainComp_of_chain1 (ℓ := ℓ) (Pt := Pt) (P := P) (C := C)
          (K := K) (decT := decT) (encT := encT) I
          (.fst (.snd (.fst .v3)))
          (.snd (.snd (.fst .v3)))
          (.fst .v0)
          (.fst (.snd .v3))
          (.fst (.snd (.snd .v3)))
          ρ4 hw secret1 key chain1 hok0 hok1 hsmall1 hlen4 hadd hsec_len
          (by dsimp only [ρ4, ρ2, argsV]; exact he0_f)
          (by dsimp only [ρ4, ρ2, argsV, partsV]; rfl)
          (by dsimp only [ρ4, ρ2, argsV, partsV]; rfl)
          (by dsimp only [ρ4, braidOutV]; rfl)
        have hep4 :
            (Expr.fst (O := e2eOps ℓ P C K decT encT) (.snd .v3)).eval ρ4 = pre.epoch := rfl
        have hidx4 :
            (Expr.fst (O := e2eOps ℓ P C K decT encT) (.snd (.snd .v3))).eval ρ4 = pre.index := rfl
        rw [hep4, hidx4] at hrun
        cases hrk : chain1.recvKey (spqrHkdfWith C.F) (pre.epoch - 1#64) pre.index with
        | error ce =>
          rw [hrk] at hrun
          rw [comp_eval_bind_pure _ _ _ _ hrun, comp_eval_caseOpt_none _ _ _ _ rfl, comp_eval_ret]
          cases hk : key with
          | none =>
            rw [hk] at hadd
            injection hadd with hc_eq
            rw [hc_eq]
            dsimp only [Pure.pure, Except.pure]
            rw [hrk]
            cases ce <;> rfl
          | some epochSecret =>
            rw [hk] at hadd_api
            dsimp only at hadd_api ⊢
            rw [hadd_api]
            dsimp only
            rw [hrk]
            cases ce <;> rfl
        | ok cm =>
          rcases cm with ⟨chain2, msgKey⟩
          rw [hrk] at hrun
          rw [comp_eval_bind_pure _ _ _ _ hrun, comp_eval_caseOpt_some _ _ _ _ rfl, comp_eval_ret]
          have hout_len := recvKey_out_empty_or_32 C.F chain1 chain2
            (pre.epoch - 1#64) pre.index msgKey hrk
          obtain ⟨recvSet', hok2, hsmall2, hcur2, hsend2⟩ :=
            st_chainRecv_tight C.F hok1 hsmall1 hrk
          let w' : TopWitness C.F :=
            ⟨w.authKey, w.dir, secret1, st', w.sendEp, w.sendCtr, recvSet',
              none, some chain2, chain2⟩
          have hw' : TopStateTightW C.F K (topBytes C.F K st' none (some chain2)) w' :=
            { htop :=
                { hbytes := rfl
                  hvn := .inl rfl
                  hch := .inl rfl
                  hok := hok2
                  hcur := by rw [hcur2, hcur1]
                  hsendEp := by rw [hsend2, hsend1, hw.htop.hsendEp]
                  hsendLe := hw.htop.hsendLe.trans
                    (treq_recv_epoch_le C.F K w.st st' sckaMsg key hrecvB)
                  hsendPrev :=
                    recvKey_sendPrevNil (spqrHkdfWith C.F) chain1 chain2 _ _ _ hsp1 hrk }
              hauth := hw.hauth
              hbok := by
                cases hek : isEkSide w.st
                · exact st_bRecvCt_tight C.F K hek hw.hbok hrecvB
                · exact st_bRecvEk_tight C.F K hek hw.hbok hrecvB
              hphi := (hPhi.2 w.st st' sckaMsg key hrecvB).trans hw.hphi
              hsmall := hsmall2 }
          have hjoin := spqrJoinEval_topStateTightW (ℓ := ℓ) C.F K hw'
          dsimp only [w', Option.map] at hjoin
          dsimp only [ρ4, braidOutV]
          simp only [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Expr.v2, Env.get, hjoin]
          cases hk : key with
          | none =>
            rw [hk] at hadd
            injection hadd with hc_eq
            rw [hc_eq]
            dsimp only [Pure.pure, Except.pure]
            rw [hrk]
            dsimp only [SpqrApiResult.ofChainResult]
            apply congrArg
            exact (recvKeyToSalt_ite_eq (topBytes C.F K st' none (some chain2)) hout_len).symm
          | some epochSecret =>
            rw [hk] at hadd_api
            dsimp only at hadd_api ⊢
            rw [hadd_api]
            dsimp only
            rw [hrk]
            dsimp only [SpqrApiResult.ofChainResult]
            apply congrArg
            exact (recvKeyToSalt_ite_eq (topBytes C.F K st' none (some chain2)) hout_len).symm

/-- Functional equivalence between `spqrRecvComp` and `(spqrV1SessionUniformCoins C.F K).recv`
on `TopStateTight` states. -/
theorem spqrRecvComp_eval {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) (B 32))) (ρ : Env Γ) :
    TopStateTight C.F K (e.eval ρ).1 →
    (spqrRecvComp I e).eval ρ = pure (
      let (pq, pqMsg) := e.eval ρ
      let spqr := spqrV1SessionUniformCoins C.F K
      if spqr.recvPanics pq pqMsg then none
      else match spqr.recv pq pqMsg with
        | .ok (pq', saltVec?) =>
          some (pq', saltVec?.map (fun v => bytesToKey32 v.toList))
        | .error _ => none) := by
  intro htight
  rcases he : e.eval ρ with ⟨pq, pqMsg⟩
  rw [he] at htight
  dsimp only at htight ⊢
  obtain ⟨w, hw⟩ := htight
  refine Eq.trans ?_ (congrArg pure (spqrUniform_recv_rhs C.F K pq pqMsg)).symm
  have hsize : pq.length < 2 ^ 64 := topStateW_length_lt C.F K hw.toTopStateW
  have hsize' : (topBytes C.F K w.st w.vn? w.ch?).length < 2 ^ 64 := hw.htop.hbytes ▸ hsize
  have hsplit := spqrSplitEval_topStateTightW (ℓ := ℓ) C.F K hw
  unfold spqrRecvComp
  rw [comp_eval_bind_ret, he]
  let ρ0 : Env (.prod (B 32) (B 32) :: Γ) := Env.cons (t := .prod (B 32) (B 32)) (pq, pqMsg) ρ
  have hpre_op :
      (e2ePureOp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        .spqrParsePreamble (.snd .v0)).eval ρ0 =
      match msgPreamble pqMsg with
      | .ok p => some (p.version, (p.epoch, (p.index, p.remaining)))
      | .error _ => none := by
    dsimp only [ρ0, Expr.eval, Expr.v0, Env.get]
    rw [eval_e2ePureOp]
    exact e2ePureOps_eval_spqrParsePreamble_lossless ℓ pqMsg
  cases hpre : msgPreamble pqMsg with
  | error _ =>
    rw [hpre] at hpre_op
    rw [comp_eval_caseOpt_none _ _ _ _ hpre_op, comp_eval_ret]
    unfold CryptoVerification.LibsignalSpqrV1.recv
    simp [hpre, SpqrApiResult.ofError, Bind.bind, Except.bind, Expr.eval]
  | ok pre =>
    rw [hpre] at hpre_op
    rw [comp_eval_caseOpt_some _ _ _ _ hpre_op]
    let preV : (spqrPreambleT (ℓ := ℓ)).denote :=
      (pre.version, (pre.epoch, (pre.index, pre.remaining)))
    let ρ1 : Env (spqrPreambleT :: .prod (B 32) (B 32) :: Γ) :=
      Env.cons (t := spqrPreambleT) preV ρ0
    have hsplit_op :
        (e2ePureOp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
          .spqrStateSplit (.fst .v1)).eval ρ1 =
        some (some (V1State.encodeRaw w.st.into_pb),
          (w.vn?.map (spqrVnToV (ℓ := ℓ)),
           (w.ch?.map Chain.intoPb).map (spqrChainToV (ℓ := ℓ)))) := by
      dsimp only [ρ1, ρ0]
      simpa [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v1, Env.get] using hsplit
    rw [comp_eval_caseOpt_some _ _ _ _ hsplit_op, comp_eval_bind_ret]
    let partsV : (spqrStatePartsT (ℓ := ℓ)).denote :=
      (some (V1State.encodeRaw w.st.into_pb),
       (w.vn?.map (spqrVnToV (ℓ := ℓ)),
        (w.ch?.map Chain.intoPb).map (spqrChainToV (ℓ := ℓ))))
    let ρ2 : Env (spqrStatePartsT :: spqrPreambleT :: .prod (B 32) (B 32) :: Γ) :=
      Env.cons (t := spqrStatePartsT) partsV ρ1
    let stillNeg : Bool := w.vn?.isSome
    have hhdr_eval :
        (Expr.letE (O := e2eOps ℓ P C K decT encT)
          (.caseOpt (.fst .v0)
            (e2ePureOp (.u8Lit 0#8) .unit)
            (e2ePureOp (.u8Lit 1#8) .unit))
          (.pair .v0
            (.caseOpt (.fst (.snd .v1))
              (.pair .v0
                (e2ePureOp .u8Eq (.pair .v0 (e2ePureOp (.u8Lit 0#8) .unit))))
              (.pair
                (e2ePureOp .u8OfNat (e2ePureOp .u32ToNat (.fst (.snd (.snd .v0)))))
                (.bool true))))).eval ρ2 =
        (1#8, (1#8, stillNeg)) := by
      rcases hw.htop.hvn with hvn | hvn
      · dsimp only [ρ2, partsV, stillNeg]
        simp [hvn, Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Expr.v1, Env.get,
          show (1#8 == 0#8) = false by decide]
      · dsimp only [ρ2, partsV, stillNeg]
        have hm : BitVec.ofNat 8 (vnOf w.dir w.authKey).minVersion.toNat = 1#8 := by
          change BitVec.ofNat 8 Version.v1.toI32.toNat = 1#8
          decide
        simp [hvn, spqrVnToV, hm, Expr.eval, eval_e2ePureOp, E2EPureOp.eval,
          Expr.v0, Expr.v1, Env.get]
    rw [hhdr_eval]
    let hdrT : Ty (e2eSig ℓ) := .prod U8 (.prod U8 .bool)
    let ρ3 : Env (hdrT :: spqrStatePartsT :: spqrPreambleT :: .prod (B 32) (B 32) :: Γ) :=
      Env.cons (t := hdrT) (1#8, (1#8, stillNeg)) ρ2
    have hg1 :
        (e2ePureOp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
          .u8Lt (.pair (.fst .v2) (.fst (.snd .v0)))).eval ρ3 =
        decide (pre.version < 1#8) := rfl
    by_cases hlt1 : pre.version < 1#8
    · rw [comp_eval_ite_true _ _ _ _ (hg1.trans (decide_eq_true hlt1)), comp_eval_ret]
      rw [hw.htop.hbytes]
      unfold CryptoVerification.LibsignalSpqrV1.recv
      rw [hpre, decodeState_topBytes C.F K w.st w.vn? w.ch? hsize']
      have hv1 : Version.v1.toU8 = 1#8 := by decide
      have hm1 : ∀ dir ak, (vnOf dir ak).minVersion.truncate 8 = 1#8 := fun _ _ => by
        change Version.v1.toI32.truncate 8 = 1#8
        decide
      rcases hw.htop.hvn with hvn | hvn <;>
        simp [hvn, topPb, stateVersion, hv1, hm1, hlt1, SpqrApiResult.ofError,
          Bind.bind, Except.bind, Expr.eval]
    · rw [comp_eval_ite_false _ _ _ _ (hg1.trans (decide_eq_false hlt1))]
      by_cases hver : pre.version = 1#8
      · have hg2 :
            (Expr.and (O := e2eOps ℓ P C K decT encT)
              (.not (e2ePureOp .u8Eq (.pair (.fst .v2) (.fst .v0))))
              (.not (.snd (.snd .v0)))).eval ρ3 = false := by
          dsimp only [ρ3, ρ2, ρ1, preV]
          simp [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Expr.v2, Env.get, hver]
        have hg3 :
            (e2ePureOp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
              .u8Eq (.pair (.fst .v0) (e2ePureOp (.u8Lit 0#8) .unit))).eval ρ3 = false := by
          dsimp only [ρ3]
          simp only [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Env.get]
          rfl
        have hg4 :
            (e2ePureOp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
              .u8Lt (.pair (.fst .v0) (.fst .v2))).eval ρ3 = false := by
          dsimp only [ρ3, ρ2, ρ1, preV]
          simp only [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Expr.v2, Env.get, hver]
          rfl
        rw [comp_eval_ite_false _ _ _ _ hg2,
          comp_eval_ite_false _ _ _ _ hg3,
          comp_eval_ite_false _ _ _ _ hg4]
        have hprep := eval_spqrRecvPrepStateComp_eq (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
          (decT := decT) (encT := encT) I .v1 (.fst .v2) (.fst .v0) (.snd (.snd .v0)) ρ3 hver
        have hp_ρ3 :
            (Expr.v1 : Expr (e2eOps ℓ P C K decT encT) _ spqrStatePartsT).eval ρ3 = partsV := rfl
        rw [hp_ρ3] at hprep
        rw [comp_eval_bind_pure _ _ _ _ hprep, comp_eval_caseOpt_some _ _ _ _ rfl]
        rw [hw.htop.hbytes, recv_topBytes C.F K w.authKey w.dir w.st w.vn? w.ch? pqMsg pre
          hsize' hw.htop.hvn hpre hver]
        exact eval_spqrRecvV1BodyComp_topStateTightW (ℓ := ℓ) (Pt := Pt) (P := P) (C := C)
          (K := K) (decT := decT) (encT := encT) I .v0
          (.fst (.snd .v4)) (.fst (.snd (.snd .v4))) (.snd (.snd (.snd .v4)))
          (Env.cons (t := spqrStatePartsT) partsV
            (Env.cons (t := .opt spqrStatePartsT) (some partsV) ρ3)) hw pre
          rfl rfl rfl rfl
      · rcases hw.htop.hvn with hvn | hvn
        · have hsn : stillNeg = false := by simp [stillNeg, hvn]
          have hg2 :
              (Expr.and (O := e2eOps ℓ P C K decT encT)
                (.not (e2ePureOp .u8Eq (.pair (.fst .v2) (.fst .v0))))
                (.not (.snd (.snd .v0)))).eval ρ3 = true := by
            dsimp only [ρ3, ρ2, ρ1, preV]
            simp [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Expr.v2, Env.get, hsn, hver]
          rw [comp_eval_ite_true _ _ _ _ hg2, comp_eval_ret]
          rw [hw.htop.hbytes, hvn]
          unfold CryptoVerification.LibsignalSpqrV1.recv
          rw [hpre, decodeState_topBytes C.F K w.st none w.ch? (hvn ▸ hsize')]
          have hv1 : Version.v1.toU8 = 1#8 := by decide
          have hbne : (pre.version != 1#8) = true := bne_iff_ne.mpr hver
          simp [topPb, stateVersion, hv1, hlt1, hbne, SpqrApiResult.ofError,
            Bind.bind, Except.bind, Expr.eval]
        · have hsn : stillNeg = true := by simp [stillNeg, hvn]
          have hgt1 : 1#8 < pre.version := by
            have hne : pre.version.toNat ≠ 1 := fun h => hver (BitVec.eq_of_toNat_eq h)
            simp only [BitVec.lt_def, BitVec.toNat_ofNat] at hlt1 ⊢
            omega
          have hg2 :
              (Expr.and (O := e2eOps ℓ P C K decT encT)
                (.not (e2ePureOp .u8Eq (.pair (.fst .v2) (.fst .v0))))
                (.not (.snd (.snd .v0)))).eval ρ3 = false := by
            dsimp only [ρ3, ρ2, ρ1, preV]
            simp [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Expr.v2, Env.get, hsn]
          have hg3 :
              (e2ePureOp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
                .u8Eq (.pair (.fst .v0) (e2ePureOp (.u8Lit 0#8) .unit))).eval ρ3 = false := by
            dsimp only [ρ3]
            simp only [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Env.get]
            rfl
          have hg4 :
              (e2ePureOp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
                .u8Lt (.pair (.fst .v0) (.fst .v2))).eval ρ3 = true := by
            dsimp only [ρ3, ρ2, ρ1, preV]
            simpa [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Expr.v2, Env.get] using hgt1
          rw [comp_eval_ite_false _ _ _ _ hg2,
            comp_eval_ite_false _ _ _ _ hg3,
            comp_eval_ite_true _ _ _ _ hg4]
          have hgr := eval_spqrRecvGreaterComp_topStateTightW (ℓ := ℓ) (Pt := Pt) (P := P)
            (C := C) (K := K) (decT := decT) (encT := encT) I .v1 (.fst (.snd (.snd .v2)))
            ρ3 hw hvn rfl
          have hidx3 :
              (Expr.fst (O := e2eOps ℓ P C K decT encT) (.snd (.snd .v2))).eval ρ3 =
              pre.index := rfl
          rw [hidx3] at hgr
          rw [hgr]
          have hcf := st_chainFrom_ok C.F w.authKey w.dir w.secret w.sendCtr w.recvSet
            w.vn? w.ch? w.chE hw.htop.hch hw.htop.hok
          rw [hvn] at hcf
          rw [hw.htop.hbytes, hvn]
          unfold CryptoVerification.LibsignalSpqrV1.recv
          rw [hpre, decodeState_topBytes C.F K w.st (some (vnOf w.dir w.authKey)) w.ch?
            (hvn ▸ hsize')]
          have hv1 : Version.v1.toU8 = 1#8 := by decide
          have hm1 : (vnOf w.dir w.authKey).minVersion.truncate 8 = 1#8 := by
            change Version.v1.toI32.truncate 8 = 1#8
            decide
          have hgt1' : pre.version > 1#8 := hgt1
          simp only [SpqrApiResult.ofError, Bind.bind, Except.bind, topPb, stateVersion,
            hv1, hm1, hlt1, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
            show (1#8 == 0#8) = false by decide, hgt1', hcf]
          cases hck : w.chE.recvKey (spqrHkdfWith C.F) 0#64 pre.index with
          | error ce =>
            cases ce <;> rfl
          | ok cm =>
            rcases cm with ⟨chain1, rawKey⟩
            dsimp only [SpqrApiResult.ofChainResult]
            have hout_len := recvKey_out_empty_or_32 C.F w.chE chain1 0#64 pre.index rawKey hck
            exact congrArg pure
              (recvKeyToSalt_some_eq
                (topBytes C.F K w.st (some (vnOf w.dir w.authKey)) (some chain1))
                hout_len).symm

end Computational.Proofs.E2E.Dsl.SpqrSimRecv
