/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeySigProg

/-!
# Shadow-Indexed `KeyInd` Gap-DH Simulation Core

Defines the shadow-indexed `KeyInd` Gap-DH simulation programs in `pqAtomicOps`, augmenting the
legacy `simTy` state with a session-entry list `(fgSess, ctr)` and length-aware `B 192` AVL caches
`(fgRoAvl, rawAvl)`. Online arms clamp scans via `KeyIndKFuels`, the random-oracle arm combines
pre-AVL secret-position checks with `fgRoAvl` lookup and restricted `fgSess` scanning, and
`gdhFinishK` / `gdhFinish2K` clamp final CDH extraction.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK

open OracleSpec
open _root_.SignalPqxdh (Setup Bytes F_X25519 QueryBudget)
open _root_.ReductionDsl (
  Sig Ty Var Expr Comp Env Ops Iface
  pqAtomicSig pqAtomicOps pqAtomicSamplers pqKeyIndCodec
  AtomicPureOp PB drKeyT bundleT hdrT sidT bits
)
open _root_.SignalPqxdh.LegacyCosted (
  B pqSig pqxdhOps pqPrimIface pqGapDhIface pqSigAndDdhIface
)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  PT Ext v letV bindV caseOptV caseSumV findMV foldMV eFind eAny eMap eCaseOpt
  sBytes32 sRandom64 sDrKey96 u32OfNat
  fgPosTy fgPatchEntryTy drKeyTy simTy paramsTy params2Ty gdhStateTy gdhState2Ty
  keyIndStateTy keyIndQueryTy keyIndRespTy sessionIdTy initQTy accQTy
  wrapBase wrapSim wrapBase2 wrapSim2
  feDk feMk gPrim eqB eqU32 optU32Eq optFst optSnd natEq nat2Eq nat3Eq nonZero32
  litB takeKB lenB slice32 isSomeE encEC encKEM
  entryMatchesC mkSecretPosC computePosC computeOptPosInitC
  smBase smFgL smRaw smLog smPows smUpd emptySimE
  stPrin stSpks stOpks stSess stResps stUsedO stUsedN stKyb stUpd
  peIkAPk peSecIKA0 peSecIKAsign sbMk sbSpkSk sbSpkPk sbPqspkSk
  oeOpkSk oeOpkPk oeConsumed oeUpd
  buMk buIkB buSpkId buSpkB buSpkSig buOpkB buPqspkId buPqspkB buPqspkSig
  hdMk hdIkAPk hdEkAPk hdSpkId hdOpkId hdPqspkId hdKemCt
  seMk seSid seUpd qK qJ qO qKJO qHdr initSidE sidEq
  rNone rBundle rHdr rInitUnfresh rDrKey
  paMode paU paV paSpkIdx paDhFlag paEphIdx paOpkMode
  pa2Mode pa2U pa2V pa2DhFlag pa2EphTarget pa2OpkMode ephSidMatchesE initSlotIdxE
  qX25519 qX25519Base qIsCanonical qSigSign qSigVerify qKemKeyGen qKemEncaps qKemDecaps ddhQ
  koskBundleOkPowsC koskSenderOkPowsC lookupSpkSkC resolveSigPkC honestPeerC checkProvC
  chooseInitRandC findHonestC kyberCheckE finishAcceptGdhC
  corruptB testB revealB revealSpkB registerGdhB
  initPrinGdhB initPrinGdh2B genSpkGdhB genSpkGdh2B genOpkGdhB genOpkGdh2B
  logFindC logFind2C spkPowsC initDh1CandC respDh1CandC findMapStepC findMapStep2C
)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (liftGdhComp)
open Computational.Proofs.SignalPqxdh.AtomicLift (
  TagLift AtomicIface aiGapDh aiSigDdh aiOfIface embedTy embedCtx mapExpr mapComp
  exprRename compRename finSidToNatExpr
  keyIndUnsupportedPrimW mapKeyIndPrimTag mapExpr_eval
  tlPrimKeyInd tlGapDhKeyInd tlSigDdhKeyInd
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (
  aop avlTy avlPathItemTy avlSearchResTy avlEmptyE dfltB192E dfltDrKeyE
  avlSearchB192C avlInsertAtPathC
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK (
  keyIndCoreFuels emptyVarRen atomicRNoneE finPairToNatE finTripleToNatE initPayToNatE accPayToNatE
  dispatchKeyIndQ ren2 ren3 ren4 runAt2 runAt3 runAt4
)

/-- Clamped loop-fuel and AVL-capacity parameters for kind-split `KeyInd` Gap-DH handlers. -/
structure KeyIndKFuels where
  /-- Total query budget `b.q_total`. -/
  kTotal : ℕ
  /-- Clamped online query bound `min b.q_on b.q_total`. -/
  kOn : ℕ
  /-- Clamped random-oracle query bound `min b.q_ro b.q_total`. -/
  kOff : ℕ
  /-- Combined `fgL` scan bound `min kTotal (kOn + kOff)`. -/
  kFg : ℕ
  /-- Persistent AVL table capacity `kOff + 2 * kOn + 1`. -/
  kAvl : ℕ
  deriving DecidableEq, Repr

@[reducible, expose] def KeyIndKFuels.kTbl (f : KeyIndKFuels) : ℕ := f.kAvl

/-- Canonical `KeyIndKFuels` derived from a `QueryBudget`. -/
@[expose] def keyIndKFuelsOfBudget (_S : Setup) (b : QueryBudget) : KeyIndKFuels :=
  let K := b.q_total
  let mOn := min b.q_on K
  let mOff := min b.q_ro K
  { kTotal := K
    kOn := mOn
    kOff := mOff
    kFg := min K (mOn + mOff)
    kAvl := mOff + 2 * mOn + 1 }

theorem keyIndKFuelsOfBudget_bridge (S : Setup) (b : QueryBudget) :
    (keyIndKFuelsOfBudget S b).kOn = (keyIndCoreFuels S b).M_on ∧
    (keyIndKFuelsOfBudget S b).kOff = (keyIndCoreFuels S b).M_off ∧
    (keyIndKFuelsOfBudget S b).kAvl = (keyIndCoreFuels S b).roCap :=
  ⟨rfl, rfl, rfl⟩

@[reducible, expose] def seqFgEntryTy : PT := .prod .nat fgPatchEntryTy

@[reducible, expose] def fgSessCtrTy : PT := .prod (.list seqFgEntryTy) .nat

@[reducible, expose] def fgListAndShadowTy : PT :=
  .prod (.list fgPatchEntryTy) fgSessCtrTy

/-- Scans `fgL` with fuel `kFg` and, on a miss, samples a fresh key and appends the new entry to
    both `fgL` and `(fgSess, ctr)`. -/
@[expose] def fgPatchShadowC (kFg : ℕ) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32))
    (fgL : Expr pqxdhOps Δ (.list fgPatchEntryTy))
    (fgSess : Expr pqxdhOps Δ (.list seqFgEntryTy))
    (ctr : Expr pqxdhOps Δ .nat) :
    Comp pqxdhOps pqGapDhIface Δ (.prod drKeyTy fgListAndShadowTy) :=
  letV (.pair fgL (.pair fgSess ctr)) fun packV =>
  bindV (findMV kFg (.fst (v packV)) fun e => entryMatchesC pos1 pos2 pos3 pos4? ss e) fun hit =>
  caseOptV (v hit)
    (bindV (gPrim sDrKey96) fun dk =>
      let newE := feMk (v pos1) (v pos2) (v pos3) (v pos4?) (v ss) (v dk)
      let fgL0 := .fst (v packV)
      let fgSess0 := .fst (.snd (v packV))
      let ctr0 := .snd (.snd (v packV))
      .ret (.pair (v dk)
        (.pair (.cons newE fgL0)
          (.pair (.cons (.pair ctr0 newE) fgSess0) (.add ctr0 (.nat 1))))))
    fun e => .ret (.pair (feDk (v e)) (v packV))

/-- Entry predicate for restricted `fgSess` scanning that skips entries below `minIdx` and
    otherwise runs `entryMatchesC`. -/
@[expose] def sessScanMinPredC {Γ₀ Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₀ Δ] [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (minIdx : Var Γ₀ .nat)
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32))
    (se : Var Δ seqFgEntryTy) : Comp pqxdhOps pqGapDhIface Δ .bool :=
  .ite (.lt (.fst (v se)) (v minIdx))
    (.ret (.bool false))
    (letV (.snd (v se)) fun e => entryMatchesC pos1 pos2 pos3 pos4? ss e)

@[expose] def fgSessScanC (kOn : ℕ) {Γ₀ Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₀ Δ] [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (minIdx : Var Γ₀ .nat)
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32))
    (fgSess : Expr pqxdhOps Δ (.list seqFgEntryTy)) :
    Comp pqxdhOps pqGapDhIface Δ (.opt seqFgEntryTy) :=
  findMV kOn fgSess fun se => sessScanMinPredC minIdx pos1 pos2 pos3 pos4? ss se

@[reducible, expose] def roPosPackTy : PT :=
  .prod fgPosTy (.prod fgPosTy (.prod fgPosTy (.prod (.opt fgPosTy) (B 32))))

@[expose] def fgSessScanPackC (kOn : ℕ) :
    Comp pqxdhOps pqGapDhIface [.nat, roPosPackTy, .list seqFgEntryTy] (.opt seqFgEntryTy) :=
  let minIdx : Var [.nat, roPosPackTy, .list seqFgEntryTy] .nat := .zero
  let pack : Var [.nat, roPosPackTy, .list seqFgEntryTy] roPosPackTy := .succ .zero
  let fgSess : Var [.nat, roPosPackTy, .list seqFgEntryTy] (.list seqFgEntryTy) :=
    .succ (.succ .zero)
  letV (.fst (v pack)) fun p1 =>
  letV (.fst (.snd (v pack))) fun p2 =>
  letV (.fst (.snd (.snd (v pack)))) fun p3 =>
  letV (.fst (.snd (.snd (.snd (v pack))))) fun p4 =>
  letV (.snd (.snd (.snd (.snd (v pack))))) fun ss =>
  fgSessScanC kOn minIdx p1 p2 p3 p4 ss (v fgSess)

@[expose] def roParsedPrePos160C {Γ Δ : List PT} [Ext Γ Δ] (sec : Var Γ (B 192)) :
    Comp pqxdhOps pqGapDhIface Δ roPosPackTy :=
  bindV (mkSecretPosC (slice32 32 (v sec))) fun pos1 =>
  bindV (mkSecretPosC (slice32 64 (v sec))) fun pos2 =>
  bindV (mkSecretPosC (slice32 96 (v sec))) fun pos3 =>
  letV (slice32 128 (v sec)) fun ss =>
  .ret (.pair (v pos1) (.pair (v pos2) (.pair (v pos3) (.pair .none (v ss)))))

@[expose] def roParsedPrePos192C {Γ Δ : List PT} [Ext Γ Δ] (sec : Var Γ (B 192)) :
    Comp pqxdhOps pqGapDhIface Δ roPosPackTy :=
  bindV (mkSecretPosC (slice32 32 (v sec))) fun pos1 =>
  bindV (mkSecretPosC (slice32 64 (v sec))) fun pos2 =>
  bindV (mkSecretPosC (slice32 96 (v sec))) fun pos3 =>
  bindV (mkSecretPosC (slice32 128 (v sec))) fun pos4 =>
  letV (.some (v pos4)) fun pos4? =>
  letV (slice32 160 (v sec)) fun ss =>
  .ret (.pair (v pos1) (.pair (v pos2) (.pair (v pos3) (.pair (v pos4?) (v ss)))))

@[expose] def extractMode0KC (S : Setup) (f : KeyIndKFuels) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) : Comp pqxdhOps pqGapDhIface Δ (B 32) :=
  let cands := eMap f.kOff (smLog (v sm)) fun sec => slice32 32 (v sec)
  bindV (findMV f.kOff cands fun z => ddhQ (paU (v pa)) (paV (v pa)) (v z)) fun f1 =>
  caseOptV (v f1)
    (bindV (spkPowsC S f.kOn (stSpks (smBase (v sm)))) fun spkPows =>
     letV (smPows (v sm)) fun advPows =>
     bindV (foldMV (min f.kOn S.N_dh) (stSess (smBase (v sm))) .none fun s acc =>
       findMapStepC pa acc (initDh1CandC S f.kOn spkPows advPows s)) fun f2 =>
     caseOptV (v f2)
       (letV (stSpks (smBase (v sm))) fun spks =>
        bindV (foldMV (min f.kOn S.N_sess_tot) (stResps (smBase (v sm))) .none fun r acc =>
          findMapStepC pa acc (respDh1CandC S f.kOn spks r)) fun f3 =>
        .ret (eCaseOpt (v f3) (litB 32 (List.replicate 32 0)) fun z => v z))
       fun z => .ret (v z))
    fun z => .ret (v z)

/-- Clamped stage-1 Gap-DH CDH extractor using `f.kOff` and `f.kOn` scan fuels. -/
@[expose] def gdhFinishK (S : Setup) (f : KeyIndKFuels) :
    Comp pqxdhOps pqGapDhIface [gdhStateTy, .bool] (B 32) :=
  let st : Var [gdhStateTy, .bool] gdhStateTy := .zero
  letV (.fst (v st)) fun pa =>
  letV (.snd (v st)) fun sm =>
  .ite (natEq (paMode (v pa)) (.nat 0)) (extractMode0KC S f pa sm)
    (.ite (natEq (paMode (v pa)) (.nat 1))
      (logFindC f.kOff 96 pa sm)
      (.ite (natEq (paMode (v pa)) (.nat 2))
        (logFindC f.kOff 64 pa sm)
        (logFindC f.kOff 128 pa sm)))

@[expose] def extractMode0_2KC (S : Setup) (f : KeyIndKFuels) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) : Comp pqxdhOps pqGapDhIface Δ (B 32) :=
  let cands := eMap f.kOff (smLog (v sm)) fun sec => slice32 32 (v sec)
  bindV (findMV f.kOff cands fun z => ddhQ (pa2U (v pa)) (pa2V (v pa)) (v z)) fun f1 =>
  caseOptV (v f1)
    (bindV (spkPowsC S f.kOn (stSpks (smBase (v sm)))) fun spkPows =>
     letV (smPows (v sm)) fun advPows =>
     bindV (foldMV (min f.kOn S.N_dh) (stSess (smBase (v sm))) .none fun s acc =>
       findMapStep2C pa acc (initDh1CandC S f.kOn spkPows advPows s)) fun f2 =>
     caseOptV (v f2)
       (letV (stSpks (smBase (v sm))) fun spks =>
        bindV (foldMV (min f.kOn S.N_sess_tot) (stResps (smBase (v sm))) .none fun r acc =>
          findMapStep2C pa acc (respDh1CandC S f.kOn spks r)) fun f3 =>
        .ret (eCaseOpt (v f3) (litB 32 (List.replicate 32 0)) fun z => v z))
       fun z => .ret (v z))
    fun z => .ret (v z)

/-- Clamped tuple-keyed Gap-DH CDH extractor using `f.kOff` and `f.kOn` scan fuels. -/
@[expose] def gdhFinish2K (S : Setup) (f : KeyIndKFuels) :
    Comp pqxdhOps pqGapDhIface [gdhState2Ty, .bool] (B 32) :=
  let st : Var [gdhState2Ty, .bool] gdhState2Ty := .zero
  letV (.fst (v st)) fun pa =>
  letV (.snd (v st)) fun sm =>
  .ite (natEq (pa2Mode (v pa)) (.nat 0)) (extractMode0_2KC S f pa sm)
    (.ite (natEq (pa2Mode (v pa)) (.nat 1))
      (logFind2C f.kOff 96 pa sm)
      (.ite (natEq (pa2Mode (v pa)) (.nat 2))
        (logFind2C f.kOff 64 pa sm)
        (logFind2C f.kOff 128 pa sm)))

@[reducible, expose] def fgRoValAtomicTy : Ty pqAtomicSig :=
  .prod (drKeyT (ℓ := 0) (Pt := Empty)) .nat

@[reducible, expose] def rawRoValAtomicTy : Ty pqAtomicSig :=
  drKeyT (ℓ := 0) (Pt := Empty)

/-- Derived shadow state `(fgSess, (ctr, (fgRoAvl, rawAvl)))` in `pqAtomicSig`. -/
@[reducible, expose] def fgShadowAtomicTy : Ty pqAtomicSig :=
  .prod (embedTy (.list seqFgEntryTy))
    (.prod .nat
      (.prod (avlTy (_root_.ReductionDsl.B 192) fgRoValAtomicTy)
             (avlTy (_root_.ReductionDsl.B 192) rawRoValAtomicTy)))

@[expose] def dfltFgRoValE {Γ : List (Ty pqAtomicSig)} : Expr pqAtomicOps Γ fgRoValAtomicTy :=
  .pair dfltDrKeyE (.nat 0)

@[expose] def emptyFgShadowE {Γ : List (Ty pqAtomicSig)} : Expr pqAtomicOps Γ fgShadowAtomicTy :=
  .pair .nil
    (.pair (.nat 0)
      (.pair (avlEmptyE dfltB192E dfltFgRoValE)
             (avlEmptyE dfltB192E dfltDrKeyE)))

@[reducible, expose] def simShadowAtomicTy : Ty pqAtomicSig :=
  .prod (embedTy simTy) fgShadowAtomicTy

/-- Projects `simShadowAtomicTy` to the underlying `simTy` state by dropping the shadow components. -/
@[expose] def forgetSimShadow (s : simShadowAtomicTy.denote) : (embedTy simTy).denote :=
  s.1

@[reducible, expose] def gdhShadowStateAtomicTy : Ty pqAtomicSig :=
  .prod (embedTy gdhStateTy) fgShadowAtomicTy

@[expose] def forgetGdhShadow (s : gdhShadowStateAtomicTy.denote) : (embedTy gdhStateTy).denote :=
  s.1

@[reducible, expose] def gdhShadowState2AtomicTy : Ty pqAtomicSig :=
  .prod (embedTy gdhState2Ty) fgShadowAtomicTy

@[expose] def forgetGdhShadow2 (s : gdhShadowState2AtomicTy.denote) : (embedTy gdhState2Ty).denote :=
  s.1

@[expose] def genSpkGdhActiveKB (kOn : ℕ) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ (.prod .nat .nat)) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy) :=
  .ite (eAny kOn (stSpks (v bSt)) fun p => nat2Eq (.fst (v p)) (v x))
    (.ret (.pair rNone (v sm)))
    (caseOptV (eFind kOn (stPrin (v bSt)) fun p => natEq (.fst (v p)) (.fst (v x)))
      (.ret (.pair rNone (v sm)))
      fun ue =>
        letV (natEq (.len (stSpks (v bSt))) (paSpkIdx (v pa))) fun isT =>
        bindV (gPrim sBytes32) fun spkSkRaw =>
        bindV (gPrim (qX25519Base (v spkSkRaw))) fun spkPkRaw =>
        letV (.ite (v isT) (litB 32 []) (v spkSkRaw)) fun spkSk =>
        letV (.ite (v isT) (paV (v pa)) (v spkPkRaw)) fun spkPk =>
        bindV (gPrim sRandom64) fun rSpk =>
        bindV (gPrim (qSigSign 33 (.pair (peSecIKAsign (.snd (v ue)))
          (.pair (encEC (v spkPk)) (v rSpk))))) fun spkSig =>
        bindV (gPrim sRandom64) fun seed =>
        bindV (gPrim (qKemKeyGen (v seed))) fun kp =>
        bindV (gPrim sRandom64) fun rPq =>
        bindV (qSigSign 1569 (.pair (peSecIKAsign (.snd (v ue)))
          (.pair (encKEM (.fst (v kp))) (v rPq))) |> gPrim) fun pqSig =>
        let jId := u32OfNat (.snd (v x))
        let bE := sbMk (v spkSk) (v spkPk) (v spkSig)
          (.snd (v kp)) (.fst (v kp)) (v pqSig) (.bool false)
        let buOut := buMk (peIkAPk (.snd (v ue))) jId (v spkPk) (v spkSig)
          .none jId (.fst (v kp)) (v pqSig)
        let bSt' := stUpd (v bSt) (spks := .cons (.pair (v x) bE) (stSpks (v bSt)))
        .ret (.pair (rBundle buOut) (smUpd (v sm) (base := bSt'))))

@[expose] def initiateGdhShadowB (S : Setup) (f : KeyIndKFuels)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (fgSh : Var Γ₅ fgSessCtrTy) (hasOpk : Bool) (x : Var Γ₄ initQTy) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy (.prod simTy fgSessCtrTy)) :=
  let K := f.kOn
  letV (.snd (.snd (v x))) fun bu =>
  let guardOk := if hasOpk then isSomeE (buOpkB (v bu)) else .not (isSomeE (buOpkB (v bu)))
  .ite (.not guardOk) (.ret (.pair rNone (.pair (v sm) (v fgSh))))
    (letV (initSidE hasOpk (v x)) fun sid =>
     .ite (eAny K (stSess (v bSt)) fun s => sidEq (seSid (v s)) (v sid))
       (.ret (.pair rNone (.pair (v sm) (v fgSh))))
       (caseOptV (eFind K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (.fst (v x)))
         (.ret (.pair rNone (.pair (v sm) (v fgSh))))
         fun ue =>
           bindV (gPrim (koskBundleOkPowsC S K bSt (smPows (v sm)) bu)) fun ok =>
           .ite (.not (v ok)) (.ret (.pair rNone (.pair (v sm) (v fgSh))))
             (letV (.and (.not (paDhFlag (v pa)))
               (natEq (initSlotIdxE S (v sid)) (paEphIdx (v pa)))) fun isTE =>
              bindV (gPrim sBytes32) fun ekSkRaw =>
              bindV (gPrim sBytes32) fun coins =>
              bindV (gPrim (resolveSigPkC S K bSt (buIkB (v bu)))) fun sigPk =>
              bindV (gPrim (qSigVerify 33 (.pair (v sigPk)
                (.pair (encEC (buSpkB (v bu))) (buSpkSig (v bu)))))) fun v1 =>
              bindV (gPrim (qSigVerify 1569 (.pair (v sigPk)
                (.pair (encKEM (buPqspkB (v bu))) (buPqspkSig (v bu)))))) fun v2 =>
              .ite (.not (.and (v v1) (v v2))) (.ret (.pair rNone (.pair (v sm) (v fgSh))))
                (bindV (gPrim (qKemEncaps (.pair (buPqspkB (v bu)) (v coins)))) fun krOpt =>
                 caseOptV (v krOpt) (.ret (.pair rNone (.pair (v sm) (v fgSh)))) fun kr =>
                   bindV (gPrim (qX25519Base (v ekSkRaw))) fun ekPkRaw =>
                   letV (.ite (v isTE) (litB 32 []) (v ekSkRaw)) fun ekSk =>
                   letV (.ite (v isTE) (paU (v pa)) (v ekPkRaw)) fun ekPk =>
                   bindV (gPrim (lookupSpkSkC S K bSt (smPows (v sm)) (buSpkB (v bu))))
                     fun spkSk =>
                   bindV (computePosC (peSecIKA0 (.snd (v ue))) (v spkSk)
                     (peIkAPk (.snd (v ue))) (buSpkB (v bu))) fun p1 =>
                   bindV (computePosC (v ekSk) (litB 32 []) (v ekPk) (buIkB (v bu))) fun p2 =>
                   bindV (computePosC (v ekSk) (litB 32 []) (v ekPk) (buSpkB (v bu))) fun p3 =>
                   bindV (computeOptPosInitC (v ekSk) (v ekPk) (buOpkB (v bu))) fun p4 =>
                   letV (.fst (v kr)) fun ss =>
                   bindV (fgPatchShadowC f.kFg p1 p2 p3 p4 ss
                     (smFgL (v sm)) (.fst (v fgSh)) (.snd (v fgSh))) fun patchR =>
                   letV (.fst (v patchR)) fun dkReal =>
                   letV (.fst (.snd (v patchR))) fun fgL' =>
                   letV (.snd (.snd (v patchR))) fun fgSh' =>
                   letV (hdMk (peIkAPk (.snd (v ue))) (v ekPk) (buSpkId (v bu))
                     (optFst (buOpkB (v bu))) (buPqspkId (v bu)) (.snd (v kr))) fun hdr =>
                   bindV (gPrim (honestPeerC S K bSt (buIkB (v bu)))) fun hp =>
                   bindV (gPrim (checkProvC S K bSt bu)) fun prov =>
                   letV (seMk (v sid) (v hp) (buIkB (v bu)) (buSpkB (v bu))
                     (optSnd (buOpkB (v bu))) (buPqspkB (v bu)) (.fst (v prov))
                     (.fst (.snd (v prov))) (.snd (.snd (v prov))) (v ekSk)
                     (isSomeE (v hp)) (v dkReal) (v dkReal) (v hdr)
                     (.bool false) (.bool false)) fun sInit =>
                   bindV (chooseInitRandC S K bSt sInit) fun dkRand =>
                   let sFinal := seUpd (v sInit) (drRand := v dkRand)
                   let bSt' := stUpd (v bSt) (sess := .cons sFinal (stSess (v bSt)))
                   letV (smUpd (v sm) (base := bSt') (fgL := v fgL')) fun smV =>
                   bindV (gPrim (findHonestC S K bSt (buIkB (v bu)))) fun fh =>
                   .ret (eCaseOpt (v fh)
                     (.pair (rInitUnfresh (v dkReal) (v hdr)) (.pair (v smV) (v fgSh')))
                     fun _ => .pair (rHdr (v hdr)) (.pair (v smV) (v fgSh')))))))

@[expose] def initiateGdh2ShadowB (S : Setup) (f : KeyIndKFuels)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (fgSh : Var Γ₅ fgSessCtrTy) (hasOpk : Bool) (x : Var Γ₄ initQTy) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy (.prod simTy fgSessCtrTy)) :=
  let K := f.kOn
  letV (.snd (.snd (v x))) fun bu =>
  let guardOk := if hasOpk then isSomeE (buOpkB (v bu)) else .not (isSomeE (buOpkB (v bu)))
  .ite (.not guardOk) (.ret (.pair rNone (.pair (v sm) (v fgSh))))
    (letV (initSidE hasOpk (v x)) fun sid =>
     .ite (eAny K (stSess (v bSt)) fun s => sidEq (seSid (v s)) (v sid))
       (.ret (.pair rNone (.pair (v sm) (v fgSh))))
       (caseOptV (eFind K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (.fst (v x)))
         (.ret (.pair rNone (.pair (v sm) (v fgSh))))
         fun ue =>
           bindV (gPrim (koskBundleOkPowsC S K bSt (smPows (v sm)) bu)) fun ok =>
           .ite (.not (v ok)) (.ret (.pair rNone (.pair (v sm) (v fgSh))))
             (letV (.and (.not (pa2DhFlag (v pa)))
               (ephSidMatchesE sid (pa2EphTarget (v pa)))) fun isTE =>
              bindV (gPrim sBytes32) fun ekSkRaw =>
              bindV (gPrim sBytes32) fun coins =>
              bindV (gPrim (resolveSigPkC S K bSt (buIkB (v bu)))) fun sigPk =>
              bindV (gPrim (qSigVerify 33 (.pair (v sigPk)
                (.pair (encEC (buSpkB (v bu))) (buSpkSig (v bu)))))) fun v1 =>
              bindV (gPrim (qSigVerify 1569 (.pair (v sigPk)
                (.pair (encKEM (buPqspkB (v bu))) (buPqspkSig (v bu)))))) fun v2 =>
              .ite (.not (.and (v v1) (v v2))) (.ret (.pair rNone (.pair (v sm) (v fgSh))))
                (bindV (gPrim (qKemEncaps (.pair (buPqspkB (v bu)) (v coins)))) fun krOpt =>
                 caseOptV (v krOpt) (.ret (.pair rNone (.pair (v sm) (v fgSh)))) fun kr =>
                   bindV (gPrim (qX25519Base (v ekSkRaw))) fun ekPkRaw =>
                   letV (.ite (v isTE) (litB 32 []) (v ekSkRaw)) fun ekSk =>
                   letV (.ite (v isTE) (pa2U (v pa)) (v ekPkRaw)) fun ekPk =>
                   bindV (gPrim (lookupSpkSkC S K bSt (smPows (v sm)) (buSpkB (v bu))))
                     fun spkSk =>
                   bindV (computePosC (peSecIKA0 (.snd (v ue))) (v spkSk)
                     (peIkAPk (.snd (v ue))) (buSpkB (v bu))) fun p1 =>
                   bindV (computePosC (v ekSk) (litB 32 []) (v ekPk) (buIkB (v bu))) fun p2 =>
                   bindV (computePosC (v ekSk) (litB 32 []) (v ekPk) (buSpkB (v bu))) fun p3 =>
                   bindV (computeOptPosInitC (v ekSk) (v ekPk) (buOpkB (v bu))) fun p4 =>
                   letV (.fst (v kr)) fun ss =>
                   bindV (fgPatchShadowC f.kFg p1 p2 p3 p4 ss
                     (smFgL (v sm)) (.fst (v fgSh)) (.snd (v fgSh))) fun patchR =>
                   letV (.fst (v patchR)) fun dkReal =>
                   letV (.fst (.snd (v patchR))) fun fgL' =>
                   letV (.snd (.snd (v patchR))) fun fgSh' =>
                   letV (hdMk (peIkAPk (.snd (v ue))) (v ekPk) (buSpkId (v bu))
                     (optFst (buOpkB (v bu))) (buPqspkId (v bu)) (.snd (v kr))) fun hdr =>
                   bindV (gPrim (honestPeerC S K bSt (buIkB (v bu)))) fun hp =>
                   bindV (gPrim (checkProvC S K bSt bu)) fun prov =>
                   letV (seMk (v sid) (v hp) (buIkB (v bu)) (buSpkB (v bu))
                     (optSnd (buOpkB (v bu))) (buPqspkB (v bu)) (.fst (v prov))
                     (.fst (.snd (v prov))) (.snd (.snd (v prov))) (v ekSk)
                     (isSomeE (v hp)) (v dkReal) (v dkReal) (v hdr)
                     (.bool false) (.bool false)) fun sInit =>
                   bindV (chooseInitRandC S K bSt sInit) fun dkRand =>
                   let sFinal := seUpd (v sInit) (drRand := v dkRand)
                   let bSt' := stUpd (v bSt) (sess := .cons sFinal (stSess (v bSt)))
                   letV (smUpd (v sm) (base := bSt') (fgL := v fgL')) fun smV =>
                   bindV (gPrim (findHonestC S K bSt (buIkB (v bu)))) fun fh =>
                   .ret (eCaseOpt (v fh)
                     (.pair (rInitUnfresh (v dkReal) (v hdr)) (.pair (v smV) (v fgSh')))
                     fun _ => .pair (rHdr (v hdr)) (.pair (v smV) (v fgSh')))))))

@[expose] def initiateGdhActiveShadowInnerB (S : Setup) (f : KeyIndKFuels)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (fgSh : Var Γ₆ fgSessCtrTy) (sendOpkCnt : Var Γ₅ .nat)
    (hasOpk : Bool) (x : Var Γ₄ initQTy) :
    Comp pqxdhOps pqGapDhIface Δ
      (.prod keyIndRespTy (.prod (.prod simTy fgSessCtrTy) .nat)) :=
  let K := f.kOn
  letV (.snd (.snd (v x))) fun bu =>
  let guardOk := if hasOpk then isSomeE (buOpkB (v bu)) else .not (isSomeE (buOpkB (v bu)))
  .ite (.not guardOk) (.ret (.pair rNone (.pair (.pair (v sm) (v fgSh)) (v sendOpkCnt))))
    (letV (initSidE hasOpk (v x)) fun sid =>
     .ite (eAny K (stSess (v bSt)) fun s => sidEq (seSid (v s)) (v sid))
       (.ret (.pair rNone (.pair (.pair (v sm) (v fgSh)) (v sendOpkCnt))))
       (caseOptV (eFind K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (.fst (v x)))
         (.ret (.pair rNone (.pair (.pair (v sm) (v fgSh)) (v sendOpkCnt))))
         fun ue =>
           bindV (gPrim (koskBundleOkPowsC S K bSt (smPows (v sm)) bu)) fun ok =>
           .ite (.not (v ok)) (.ret (.pair rNone (.pair (.pair (v sm) (v fgSh)) (v sendOpkCnt))))
             (let ephMatchE : Expr pqxdhOps _ .bool :=
                if hasOpk then
                  .and (.not (paDhFlag (v pa)))
                    (natEq (.ite (paOpkMode (v pa)) (v sendOpkCnt) (.len (stSess (v bSt))))
                      (paEphIdx (v pa)))
                else
                  .and (.not (paDhFlag (v pa)))
                    (.and (.not (paOpkMode (v pa)))
                      (natEq (.len (stSess (v bSt))) (paEphIdx (v pa))))
              letV ephMatchE fun isTE =>
              bindV (gPrim sBytes32) fun ekSkRaw =>
              bindV (gPrim sBytes32) fun coins =>
              bindV (gPrim (resolveSigPkC S K bSt (buIkB (v bu)))) fun sigPk =>
              bindV (gPrim (qSigVerify 33 (.pair (v sigPk)
                (.pair (encEC (buSpkB (v bu))) (buSpkSig (v bu)))))) fun v1 =>
              bindV (gPrim (qSigVerify 1569 (.pair (v sigPk)
                (.pair (encKEM (buPqspkB (v bu))) (buPqspkSig (v bu)))))) fun v2 =>
              .ite (.not (.and (v v1) (v v2)))
                (.ret (.pair rNone (.pair (.pair (v sm) (v fgSh)) (v sendOpkCnt))))
                (bindV (gPrim (qKemEncaps (.pair (buPqspkB (v bu)) (v coins)))) fun krOpt =>
                 caseOptV (v krOpt)
                   (.ret (.pair rNone (.pair (.pair (v sm) (v fgSh)) (v sendOpkCnt)))) fun kr =>
                   bindV (gPrim (qX25519Base (v ekSkRaw))) fun ekPkRaw =>
                   letV (.ite (v isTE) (litB 32 []) (v ekSkRaw)) fun ekSk =>
                   letV (.ite (v isTE) (paU (v pa)) (v ekPkRaw)) fun ekPk =>
                   bindV (gPrim (lookupSpkSkC S K bSt (smPows (v sm)) (buSpkB (v bu))))
                     fun spkSk =>
                   bindV (computePosC (peSecIKA0 (.snd (v ue))) (v spkSk)
                     (peIkAPk (.snd (v ue))) (buSpkB (v bu))) fun p1 =>
                   bindV (computePosC (v ekSk) (litB 32 []) (v ekPk) (buIkB (v bu))) fun p2 =>
                   bindV (computePosC (v ekSk) (litB 32 []) (v ekPk) (buSpkB (v bu))) fun p3 =>
                   bindV (computeOptPosInitC (v ekSk) (v ekPk) (buOpkB (v bu))) fun p4 =>
                   letV (.fst (v kr)) fun ss =>
                   bindV (fgPatchShadowC f.kFg p1 p2 p3 p4 ss
                     (smFgL (v sm)) (.fst (v fgSh)) (.snd (v fgSh))) fun patchR =>
                   letV (.fst (v patchR)) fun dkReal =>
                   letV (.fst (.snd (v patchR))) fun fgL' =>
                   letV (.snd (.snd (v patchR))) fun fgSh' =>
                   letV (hdMk (peIkAPk (.snd (v ue))) (v ekPk) (buSpkId (v bu))
                     (optFst (buOpkB (v bu))) (buPqspkId (v bu)) (.snd (v kr))) fun hdr =>
                   bindV (gPrim (honestPeerC S K bSt (buIkB (v bu)))) fun hp =>
                   bindV (gPrim (checkProvC S K bSt bu)) fun prov =>
                   letV (seMk (v sid) (v hp) (buIkB (v bu)) (buSpkB (v bu))
                     (optSnd (buOpkB (v bu))) (buPqspkB (v bu)) (.fst (v prov))
                     (.fst (.snd (v prov))) (.snd (.snd (v prov))) (v ekSk)
                     (isSomeE (v hp)) (v dkReal) (v dkReal) (v hdr)
                     (.bool false) (.bool false)) fun sInit =>
                   bindV (chooseInitRandC S K bSt sInit) fun dkRand =>
                   let sFinal := seUpd (v sInit) (drRand := v dkRand)
                   let bSt' := stUpd (v bSt) (sess := .cons sFinal (stSess (v bSt)))
                   letV (smUpd (v sm) (base := bSt') (fgL := v fgL')) fun smV =>
                   letV (if hasOpk then .add (v sendOpkCnt) (.nat 1) else v sendOpkCnt) fun cntV =>
                   bindV (gPrim (findHonestC S K bSt (buIkB (v bu)))) fun fh =>
                   .ret (eCaseOpt (v fh)
                     (.pair (rInitUnfresh (v dkReal) (v hdr))
                       (.pair (.pair (v smV) (v fgSh')) (v cntV)))
                     fun _ => .pair (rHdr (v hdr))
                       (.pair (.pair (v smV) (v fgSh')) (v cntV)))))))

@[expose] def acceptOpkGdhCoreShadowB (S : Setup) (f : KeyIndKFuels)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (opkModeB : Var Γ₁ .bool) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (fgSh : Var Γ₅ fgSessCtrTy) (x : Var Γ₄ accQTy) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy (.prod simTy fgSessCtrTy)) :=
  let K := f.kOn
  let hdr := qHdr (v x)
  let guardOk := Expr.and
    (.and (.and (.and (eqU32 (hdSpkId hdr) (u32OfNat (qJ (v x))))
                      (eqU32 (hdPqspkId hdr) (u32OfNat (qJ (v x)))))
                (optU32Eq (hdOpkId hdr) (.some (u32OfNat (qO (v x))))))
          (natEq (lenB (hdIkAPk hdr)) (.nat 32)))
    (natEq (lenB (hdEkAPk hdr)) (.nat 32))
  .ite (.not guardOk) (.ret (.pair rNone (.pair (v sm) (v fgSh))))
    (.ite (eAny K (stUsedO (v bSt)) fun u => nat3Eq (v u) (qKJO (v x)))
      (.ret (.pair rNone (.pair (v sm) (v fgSh))))
      (bindV (gPrim (koskSenderOkPowsC S K bSt (smPows (v sm)) (hdIkAPk (qHdr (v x))))) fun sOk =>
       .ite (.not (v sOk)) (.ret (.pair rNone (.pair (v sm) (v fgSh))))
         (caseOptV (eFind K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (qK (v x)))
           (.ret (.pair rNone (.pair (v sm) (v fgSh))))
           fun ke =>
             caseOptV (eFind K (stSpks (v bSt)) fun p =>
               nat2Eq (.fst (v p)) (.pair (qK (v x)) (qJ (v x))))
               (.ret (.pair rNone (.pair (v sm) (v fgSh))))
               fun be =>
                 caseOptV (eFind K (stOpks (v bSt)) fun p => nat3Eq (.fst (v p)) (qKJO (v x)))
                   (.ret (.pair rNone (.pair (v sm) (v fgSh))))
                   fun oe =>
                     .ite (oeConsumed (.snd (v oe))) (.ret (.pair rNone (.pair (v sm) (v fgSh))))
                       (letV (kyberCheckE K (stKyb (v bSt)) (.pair (qK (v x))
                         (.pair (hdPqspkId (qHdr (v x)))
                           (.pair (hdSpkId (qHdr (v x))) (hdEkAPk (qHdr (v x))))))) fun kybR =>
                        bindV (gPrim (qIsCanonical (hdEkAPk (qHdr (v x))))) fun canon =>
                        bindV (gPrim (qX25519 (.pair (litB 32 (List.replicate 32 0))
                          (hdIkAPk (qHdr (v x)))))) fun dh1Z =>
                        bindV (gPrim (qX25519 (.pair (litB 32 (List.replicate 32 0))
                          (hdEkAPk (qHdr (v x)))))) fun dh2Z =>
                        .ite (v opkModeB)
                          (bindV (gPrim (qKemDecaps (.pair (sbPqspkSk (.snd (v be)))
                            (hdKemCt (qHdr (v x)))))) fun ssOpt =>
                           .ite (.not (.and (.and (.and (.fst (v kybR)) (v canon))
                             (nonZero32 (v dh1Z))) (nonZero32 (v dh2Z))))
                             (.ret (.pair rNone (.pair (v sm) (v fgSh))))
                             (caseOptV (v ssOpt) (.ret (.pair rNone (.pair (v sm) (v fgSh)))) fun ss =>
                               bindV (computePosC (litB 32 []) (sbSpkSk (.snd (v be)))
                                 (hdIkAPk (qHdr (v x))) (sbSpkPk (.snd (v be)))) fun p1 =>
                               bindV (computePosC (litB 32 []) (peSecIKA0 (.snd (v ke)))
                                 (hdEkAPk (qHdr (v x))) (peIkAPk (.snd (v ke)))) fun p2 =>
                               bindV (computePosC (litB 32 []) (sbSpkSk (.snd (v be)))
                                 (hdEkAPk (qHdr (v x))) (sbSpkPk (.snd (v be)))) fun p3 =>
                               bindV (computePosC (litB 32 []) (oeOpkSk (.snd (v oe)))
                                 (hdEkAPk (qHdr (v x))) (oeOpkPk (.snd (v oe)))) fun p4Raw =>
                               letV (.some (v p4Raw)) fun p4 =>
                               bindV (fgPatchShadowC f.kFg p1 p2 p3 p4 ss
                                 (smFgL (v sm)) (.fst (v fgSh)) (.snd (v fgSh))) fun patchFull =>
                               letV (.pair (.fst (v patchFull)) (.fst (.snd (v patchFull))))
                                 fun patchR =>
                               let opks' := eMap K (stOpks (v bSt)) fun p =>
                                 .ite (nat3Eq (.fst (v p)) (qKJO (v x)))
                                   (.pair (.fst (v p))
                                     (oeUpd (.snd (v p)) (consumed := .bool true)))
                                   (v p)
                               bindV (finishAcceptGdhC S K sm bSt true x ke be
                                 (.some (oeOpkPk (.snd (v oe)))) opks'
                                 (.cons (qKJO (v x)) (stUsedO (v bSt)))
                                 (stUsedN (v bSt)) (.snd (v kybR)) patchR) fun accRes =>
                               .ret (.pair (.fst (v accRes))
                                 (.pair (.snd (v accRes)) (.snd (.snd (v patchFull)))))))
                          (bindV (gPrim (qX25519 (.pair (oeOpkSk (.snd (v oe)))
                            (hdEkAPk (qHdr (v x)))))) fun dh4 =>
                           bindV (gPrim (qKemDecaps (.pair (sbPqspkSk (.snd (v be)))
                             (hdKemCt (qHdr (v x)))))) fun ssOpt =>
                           .ite (.not (.and (.and (.and (.and (.fst (v kybR)) (v canon))
                             (nonZero32 (v dh1Z))) (nonZero32 (v dh2Z))) (nonZero32 (v dh4))))
                             (.ret (.pair rNone (.pair (v sm) (v fgSh))))
                             (caseOptV (v ssOpt) (.ret (.pair rNone (.pair (v sm) (v fgSh)))) fun ss =>
                               bindV (computePosC (litB 32 []) (sbSpkSk (.snd (v be)))
                                 (hdIkAPk (qHdr (v x))) (sbSpkPk (.snd (v be)))) fun p1 =>
                               bindV (computePosC (litB 32 []) (peSecIKA0 (.snd (v ke)))
                                 (hdEkAPk (qHdr (v x))) (peIkAPk (.snd (v ke)))) fun p2 =>
                               bindV (computePosC (litB 32 []) (sbSpkSk (.snd (v be)))
                                 (hdEkAPk (qHdr (v x))) (sbSpkPk (.snd (v be)))) fun p3 =>
                               bindV (mkSecretPosC (v dh4)) fun p4Raw =>
                               letV (.some (v p4Raw)) fun p4 =>
                               bindV (fgPatchShadowC f.kFg p1 p2 p3 p4 ss
                                 (smFgL (v sm)) (.fst (v fgSh)) (.snd (v fgSh))) fun patchFull =>
                               letV (.pair (.fst (v patchFull)) (.fst (.snd (v patchFull))))
                                 fun patchR =>
                               let opks' := eMap K (stOpks (v bSt)) fun p =>
                                 .ite (nat3Eq (.fst (v p)) (qKJO (v x)))
                                   (.pair (.fst (v p))
                                     (oeUpd (.snd (v p)) (consumed := .bool true)))
                                   (v p)
                               bindV (finishAcceptGdhC S K sm bSt true x ke be
                                 (.some (oeOpkPk (.snd (v oe)))) opks'
                                 (.cons (qKJO (v x)) (stUsedO (v bSt)))
                                 (stUsedN (v bSt)) (.snd (v kybR)) patchR) fun accRes =>
                               .ret (.pair (.fst (v accRes))
                                 (.pair (.snd (v accRes)) (.snd (.snd (v patchFull)))))))))))

@[expose] def acceptOpkGdhShadowB (S : Setup) (f : KeyIndKFuels)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (fgSh : Var Γ₅ fgSessCtrTy) (x : Var Γ₄ accQTy) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy (.prod simTy fgSessCtrTy)) :=
  letV (paOpkMode (v pa)) fun opkM =>
  acceptOpkGdhCoreShadowB S f opkM sm bSt fgSh x

@[expose] def acceptOpkGdh2ShadowB (S : Setup) (f : KeyIndKFuels)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (fgSh : Var Γ₅ fgSessCtrTy) (x : Var Γ₄ accQTy) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy (.prod simTy fgSessCtrTy)) :=
  letV (pa2OpkMode (v pa)) fun opkM =>
  acceptOpkGdhCoreShadowB S f opkM sm bSt fgSh x

@[expose] def acceptNoOpkGdhShadowB (S : Setup) (f : KeyIndKFuels)
    {Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (fgSh : Var Γ₅ fgSessCtrTy) (x : Var Γ₄ accQTy) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy (.prod simTy fgSessCtrTy)) :=
  let K := f.kOn
  let hdr := qHdr (v x)
  let guardOk := Expr.and
    (.and (.and (.and (eqU32 (hdSpkId hdr) (u32OfNat (qJ (v x))))
                      (eqU32 (hdPqspkId hdr) (u32OfNat (qJ (v x)))))
                (optU32Eq (hdOpkId hdr) .none))
          (natEq (lenB (hdIkAPk hdr)) (.nat 32)))
    (natEq (lenB (hdEkAPk hdr)) (.nat 32))
  .ite (.not guardOk) (.ret (.pair rNone (.pair (v sm) (v fgSh))))
    (.ite (eAny K (stUsedN (v bSt)) fun u => nat3Eq (v u) (qKJO (v x)))
      (.ret (.pair rNone (.pair (v sm) (v fgSh))))
      (bindV (gPrim (koskSenderOkPowsC S K bSt (smPows (v sm)) (hdIkAPk (qHdr (v x))))) fun sOk =>
       .ite (.not (v sOk)) (.ret (.pair rNone (.pair (v sm) (v fgSh))))
         (caseOptV (eFind K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (qK (v x)))
           (.ret (.pair rNone (.pair (v sm) (v fgSh))))
           fun ke =>
             caseOptV (eFind K (stSpks (v bSt)) fun p =>
               nat2Eq (.fst (v p)) (.pair (qK (v x)) (qJ (v x))))
               (.ret (.pair rNone (.pair (v sm) (v fgSh))))
               fun be =>
                 letV (kyberCheckE K (stKyb (v bSt)) (.pair (qK (v x))
                   (.pair (hdPqspkId (qHdr (v x)))
                     (.pair (hdSpkId (qHdr (v x))) (hdEkAPk (qHdr (v x))))))) fun kybR =>
                 bindV (gPrim (qIsCanonical (hdEkAPk (qHdr (v x))))) fun canon =>
                 bindV (gPrim (qX25519 (.pair (litB 32 (List.replicate 32 0))
                   (hdIkAPk (qHdr (v x)))))) fun dh1Z =>
                 bindV (gPrim (qX25519 (.pair (litB 32 (List.replicate 32 0))
                   (hdEkAPk (qHdr (v x)))))) fun dh2Z =>
                 bindV (gPrim (qKemDecaps (.pair (sbPqspkSk (.snd (v be)))
                   (hdKemCt (qHdr (v x)))))) fun ssOpt =>
                 .ite (.not (.and (.and (.and (.fst (v kybR)) (v canon))
                   (nonZero32 (v dh1Z))) (nonZero32 (v dh2Z))))
                   (.ret (.pair rNone (.pair (v sm) (v fgSh))))
                   (caseOptV (v ssOpt) (.ret (.pair rNone (.pair (v sm) (v fgSh)))) fun ss =>
                     bindV (computePosC (litB 32 []) (sbSpkSk (.snd (v be)))
                       (hdIkAPk (qHdr (v x))) (sbSpkPk (.snd (v be)))) fun p1 =>
                     bindV (computePosC (litB 32 []) (peSecIKA0 (.snd (v ke)))
                       (hdEkAPk (qHdr (v x))) (peIkAPk (.snd (v ke)))) fun p2 =>
                     bindV (computePosC (litB 32 []) (sbSpkSk (.snd (v be)))
                       (hdEkAPk (qHdr (v x))) (sbSpkPk (.snd (v be)))) fun p3 =>
                     letV (.none (t := fgPosTy)) fun p4 =>
                     bindV (fgPatchShadowC f.kFg p1 p2 p3 p4 ss
                       (smFgL (v sm)) (.fst (v fgSh)) (.snd (v fgSh))) fun patchFull =>
                     letV (.pair (.fst (v patchFull)) (.fst (.snd (v patchFull)))) fun patchR =>
                     bindV (finishAcceptGdhC S K sm bSt false x ke be
                       .none (stOpks (v bSt)) (stUsedO (v bSt))
                       (.cons (qKJO (v x)) (stUsedN (v bSt))) (.snd (v kybR)) patchR) fun accRes =>
                     .ret (.pair (.fst (v accRes))
                       (.pair (.snd (v accRes)) (.snd (.snd (v patchFull)))))))))

/-- Bundles a target `pqSig` interface, syntax lifter from `pqGapDhIface`, and atomic `TagLift`
    for uniform 1-key and 2-key instantiation. -/
structure GdhAtomicLift {ι : Type} {T : OracleSpec ι} (A : AtomicIface T) : Type 1 where
  I₁ : Iface pqSig T
  liftI : ∀ {Γ : List PT} {τ : PT}, Comp pqxdhOps pqGapDhIface Γ τ → Comp pqxdhOps I₁ Γ τ
  tl : TagLift I₁ A

@[expose] def gdhLift2Key : GdhAtomicLift aiGapDh where
  I₁ := pqGapDhIface
  liftI := fun c => c
  tl := tlGapDhKeyInd

@[expose] def gdhLift1Key : GdhAtomicLift aiSigDdh where
  I₁ := pqSigAndDdhIface
  liftI := liftGdhComp
  tl := tlSigDdhKeyInd

@[expose] def liftGdhAtomic {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) {Γ : List PT} {τ : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ τ) :
    Comp pqAtomicOps A.toIface (embedCtx Γ) (embedTy τ) :=
  mapComp gl.tl (gl.liftI c)

@[expose] def ren1 {Γ : List (Ty pqAtomicSig)} {A a : Ty pqAtomicSig} :
    Var [A] a → Var (A :: Γ) a
  | .zero => .zero

@[expose] def wkSndVar {A B a : Ty pqAtomicSig} :
    Var [B] a → Var [A, B] a
  | .zero => .succ .zero

@[expose] def runAt1 {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (c : Comp pqAtomicOps I [A] R) : Comp pqAtomicOps I Γ R :=
  .bind (.ret aE) (compRename ren1 c)

@[expose] def sampleDrKey96LiftC {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) {Γ : List (Ty pqAtomicSig)} :
    Comp pqAtomicOps A.toIface Γ (drKeyT (ℓ := 0) (Pt := Empty)) :=
  compRename emptyVarRen (liftGdhAtomic gl (gPrim (sDrKey96 (Γ := []))))

@[expose] def roNotPrefixE : Expr pqxdhOps [B 192] .bool :=
  let sec : Var [B 192] (B 192) := .zero
  .not (eqB (takeKB 192 32 (v sec)) (litB 32 F_X25519))

@[expose] def roLenEqE (n : ℕ) : Expr pqxdhOps [B 192] .bool :=
  let sec : Var [B 192] (B 192) := .zero
  natEq (lenB (v sec)) (.nat n)

@[expose] def seqFgEntryDkE : Expr pqxdhOps [seqFgEntryTy] drKeyTy :=
  let se : Var [seqFgEntryTy] seqFgEntryTy := .zero
  feDk (.snd (v se))

@[expose] def roHitRespSimE : Expr pqxdhOps [drKeyTy, simTy, B 192] (.prod keyIndRespTy simTy) :=
  let dk : Var [drKeyTy, simTy, B 192] drKeyTy := .zero
  let sm : Var [drKeyTy, simTy, B 192] simTy := .succ .zero
  let sec : Var [drKeyTy, simTy, B 192] (B 192) := .succ (.succ .zero)
  .pair (rDrKey (v dk)) (smUpd (v sm) (log := .cons (v sec) (smLog (v sm))))

@[expose] def rawMissRespSimE : Expr pqxdhOps [drKeyTy, simTy, B 192] (.prod keyIndRespTy simTy) :=
  let dk : Var [drKeyTy, simTy, B 192] drKeyTy := .zero
  let sm : Var [drKeyTy, simTy, B 192] simTy := .succ .zero
  let sec : Var [drKeyTy, simTy, B 192] (B 192) := .succ (.succ .zero)
  .pair (rDrKey (v dk))
    (smUpd (v sm) (raw := .cons (.pair (v sec) (v dk)) (smRaw (v sm)))
      (log := .cons (v sec) (smLog (v sm))))

@[expose] def parsedMissRespSimE :
    Expr pqxdhOps [drKeyTy, roPosPackTy, simTy, B 192] (.prod keyIndRespTy simTy) :=
  let dk : Var [drKeyTy, roPosPackTy, simTy, B 192] drKeyTy := .zero
  let ppVar : Var [drKeyTy, roPosPackTy, simTy, B 192] roPosPackTy := .succ .zero
  let pp : Expr pqxdhOps [drKeyTy, roPosPackTy, simTy, B 192] roPosPackTy := v ppVar
  let sm : Var [drKeyTy, roPosPackTy, simTy, B 192] simTy := .succ (.succ .zero)
  let sec : Var [drKeyTy, roPosPackTy, simTy, B 192] (B 192) := .succ (.succ (.succ .zero))
  let newE := feMk (.fst pp) (.fst (.snd pp)) (.fst (.snd (.snd pp)))
    (.fst (.snd (.snd (.snd pp)))) (.snd (.snd (.snd (.snd pp)))) (v dk)
  .pair (rDrKey (v dk))
    (smUpd (v sm) (fgL := .cons newE (smFgL (v sm))) (log := .cons (v sec) (smLog (v sm))))

@[expose] def roRawFallbackShadowAtomicC {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) (f : KeyIndKFuels) :
    Comp pqAtomicOps A.toIface [simShadowAtomicTy, PB 192]
      (.prod (embedTy keyIndRespTy) simShadowAtomicTy) :=
  .bind (avlSearchB192C f.kAvl (.snd (.snd (.snd (.snd .v0)))) (aop (.pbytesToBytes 192) .v1))
    (.caseOpt (.fst .v0)
      (.bind (sampleDrKey96LiftC gl)
        (.bind (avlInsertAtPathC f.kAvl
            (.snd (.snd (.snd (.snd .v2)))) (.snd .v1) (aop (.pbytesToBytes 192) .v3) .v0)
          (let sec3 : Expr pqAtomicOps _ (PB 192) := .var (.succ (.succ (.succ (.succ .zero))))
           .bind (runAt3 .v1 (.fst .v3) sec3 (.ret (mapExpr rawMissRespSimE)))
             (let st4 : Expr pqAtomicOps _ simShadowAtomicTy :=
                .var (.succ (.succ (.succ (.succ .zero))))
              .ret (.pair (.fst .v0)
                (.pair (.snd .v0)
                  (.pair (.fst (.snd st4))
                    (.pair (.fst (.snd (.snd st4)))
                      (.pair (.fst (.snd (.snd (.snd st4)))) .v1)))))))))
      (.bind (runAt3 .v0 (.fst .v2) .v3 (.ret (mapExpr roHitRespSimE)))
        (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd .v3))))))

@[expose] def roParsedPostPosShadowAtomicC {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) (f : KeyIndKFuels) :
    Comp pqAtomicOps A.toIface [embedTy roPosPackTy, simShadowAtomicTy, PB 192]
      (.prod (embedTy keyIndRespTy) simShadowAtomicTy) :=
  .bind (avlSearchB192C f.kAvl (.fst (.snd (.snd (.snd .v1)))) (aop (.pbytesToBytes 192) .v2))
    (let minIdxE : Expr pqAtomicOps _ .nat :=
       .caseOpt (.fst .v0) (.nat 0) (.add (.snd .v0) (.nat 1))
     .bind (runAt3 minIdxE .v1 (.fst (.snd .v2)) (liftGdhAtomic gl (fgSessScanPackC f.kOn)))
       (.caseOpt .v0
         (.caseOpt (.fst .v1)
           (.bind (sampleDrKey96LiftC gl)
             (let stM : Expr pqAtomicOps _ simShadowAtomicTy :=
                .var (.succ (.succ (.succ (.succ .zero))))
              let secM : Expr pqAtomicOps _ (PB 192) :=
                .var (.succ (.succ (.succ (.succ (.succ .zero)))))
              .bind (avlInsertAtPathC f.kAvl
                  (.fst (.snd (.snd (.snd stM)))) (.snd .v2) (aop (.pbytesToBytes 192) secM)
                  (.pair .v0 (.fst (.snd (.snd stM)))))
                (let packM : Expr pqAtomicOps _ (embedTy roPosPackTy) :=
                   .var (.succ (.succ (.succ (.succ .zero))))
                 let stM' : Expr pqAtomicOps _ simShadowAtomicTy :=
                   .var (.succ (.succ (.succ (.succ (.succ .zero)))))
                 let secM' : Expr pqAtomicOps _ (PB 192) :=
                   .var (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))
                 .bind (runAt4 .v1 packM (.fst stM') secM' (.ret (mapExpr parsedMissRespSimE)))
                   (let stM'' : Expr pqAtomicOps _ simShadowAtomicTy :=
                      .var (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))
                    .ret (.pair (.fst .v0)
                      (.pair (.snd .v0)
                        (.pair (.fst (.snd stM''))
                          (.pair (.add (.fst (.snd (.snd stM''))) (.nat 1))
                            (.pair .v1 (.snd (.snd (.snd (.snd stM'')))))))))))))
           (let stA : Expr pqAtomicOps _ simShadowAtomicTy :=
              .var (.succ (.succ (.succ (.succ .zero))))
            let secA : Expr pqAtomicOps _ (PB 192) :=
              .var (.succ (.succ (.succ (.succ (.succ .zero)))))
            .bind (runAt3 (.fst .v0) (.fst stA) secA (.ret (mapExpr roHitRespSimE)))
              (let stA' : Expr pqAtomicOps _ simShadowAtomicTy :=
                 .var (.succ (.succ (.succ (.succ (.succ .zero)))))
               .ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd stA'))))))
         (let stS : Expr pqAtomicOps _ simShadowAtomicTy :=
            .var (.succ (.succ (.succ (.succ .zero))))
          let secS : Expr pqAtomicOps _ (PB 192) :=
            .var (.succ (.succ (.succ (.succ (.succ .zero)))))
          let dkS : Expr pqAtomicOps _ (embedTy drKeyTy) := exprRename ren1 (mapExpr seqFgEntryDkE)
          .bind (runAt3 dkS (.fst stS) secS (.ret (mapExpr roHitRespSimE)))
            (let stS' : Expr pqAtomicOps _ simShadowAtomicTy :=
               .var (.succ (.succ (.succ (.succ (.succ .zero)))))
             .ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd stS')))))))

/-- Shadow-indexed `.roQuery` handler in `pqAtomicOps`, running pre-AVL secret-position checks
    before `fgRoAvl` lookup and restricted `fgSess` scanning. -/
@[expose] def roParsedShadowAtomicC {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) (f : KeyIndKFuels) :
    Comp pqAtomicOps A.toIface [simShadowAtomicTy, PB 192]
      (.prod (embedTy keyIndRespTy) simShadowAtomicTy) :=
  let notPreE : Expr pqAtomicOps [simShadowAtomicTy, PB 192] .bool :=
    exprRename wkSndVar (mapExpr roNotPrefixE)
  let len160E : Expr pqAtomicOps [simShadowAtomicTy, PB 192] .bool :=
    exprRename wkSndVar (mapExpr (roLenEqE 160))
  let len192E : Expr pqAtomicOps [simShadowAtomicTy, PB 192] .bool :=
    exprRename wkSndVar (mapExpr (roLenEqE 192))
  .ite notPreE
    (roRawFallbackShadowAtomicC gl f)
    (.ite len160E
      (.bind (runAt1 .v1 (liftGdhAtomic gl (roParsedPrePos160C (Γ := [B 192]) (Δ := [B 192]) .zero)))
        (runAt3 .v0 .v1 .v2 (roParsedPostPosShadowAtomicC gl f)))
      (.ite len192E
        (.bind (runAt1 .v1 (liftGdhAtomic gl (roParsedPrePos192C (Γ := [B 192]) (Δ := [B 192]) .zero)))
          (runAt3 .v0 .v1 .v2 (roParsedPostPosShadowAtomicC gl f)))
        (roRawFallbackShadowAtomicC gl f)))

@[expose] def liftKind0NoFgArm {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) (S : Setup)
    {stTy qPayTy : PT} {PayAtomic : Ty pqAtomicSig}
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy stTy) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (embedTy qPayTy))
    (arm : Comp pqxdhOps pqGapDhIface [stTy, qPayTy] (.prod keyIndRespTy stTy)) :
    Comp pqAtomicOps A.toIface
      (PayAtomic :: [.prod (embedTy stTy) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (.prod (pqKeyIndCodec S).R (.prod (embedTy stTy) fgShadowAtomicTy)) :=
  .bind (runAt2 (.fst .v1) payE (liftGdhAtomic gl arm))
    (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd .v2))))

@[expose] def liftKind0SessArm {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) (S : Setup)
    {stTy qPayTy : PT} {PayAtomic : Ty pqAtomicSig}
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy stTy) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (embedTy qPayTy))
    (arm : Comp pqxdhOps pqGapDhIface [.prod stTy fgSessCtrTy, qPayTy]
      (.prod keyIndRespTy (.prod stTy fgSessCtrTy))) :
    Comp pqAtomicOps A.toIface
      (PayAtomic :: [.prod (embedTy stTy) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (.prod (pqKeyIndCodec S).R (.prod (embedTy stTy) fgShadowAtomicTy)) :=
  let fgScE : Expr pqAtomicOps _ (embedTy fgSessCtrTy) :=
    .pair (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))
  .bind (runAt2 (.pair (.fst .v1) fgScE) payE (liftGdhAtomic gl arm))
    (.ret (.pair (.fst .v0)
      (.pair (.fst (.snd .v0))
        (.pair (.fst (.snd (.snd .v0)))
          (.pair (.snd (.snd (.snd .v0))) (.snd (.snd (.snd .v2))))))))

@[expose] def liftKind1RoArm {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) (S : Setup) (f : KeyIndKFuels) {paTy : PT} :
    Comp pqAtomicOps A.toIface
      (PB 192 :: [.prod (embedTy (.prod paTy simTy)) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (.prod (pqKeyIndCodec S).R (.prod (embedTy (.prod paTy simTy)) fgShadowAtomicTy)) :=
  let simShE : Expr pqAtomicOps _ simShadowAtomicTy := .pair (.snd (.fst .v1)) (.snd .v1)
  .bind (runAt2 simShE .v0 (roParsedShadowAtomicC gl f))
    (.ret (.pair (.fst .v0)
      (.pair (.pair (.fst (.fst .v2)) (.fst (.snd .v0))) (.snd (.snd .v0)))))

@[expose] def wrapSimSessArm {paTy qPayTy : PT}
    (body : Var [paTy, .prod paTy simTy, .prod (.prod paTy simTy) fgSessCtrTy, qPayTy] paTy →
      Var [simTy, paTy, .prod paTy simTy, .prod (.prod paTy simTy) fgSessCtrTy, qPayTy] simTy →
      Var [keyIndStateTy, simTy, paTy, .prod paTy simTy,
        .prod (.prod paTy simTy) fgSessCtrTy, qPayTy] keyIndStateTy →
      Var [fgSessCtrTy, keyIndStateTy, simTy, paTy, .prod paTy simTy,
        .prod (.prod paTy simTy) fgSessCtrTy, qPayTy] fgSessCtrTy →
      Var [.prod (.prod paTy simTy) fgSessCtrTy, qPayTy] qPayTy →
      Comp pqxdhOps pqGapDhIface
        [fgSessCtrTy, keyIndStateTy, simTy, paTy, .prod paTy simTy,
          .prod (.prod paTy simTy) fgSessCtrTy, qPayTy]
        (.prod keyIndRespTy (.prod simTy fgSessCtrTy))) :
    Comp pqxdhOps pqGapDhIface [.prod (.prod paTy simTy) fgSessCtrTy, qPayTy]
      (.prod keyIndRespTy (.prod (.prod paTy simTy) fgSessCtrTy)) :=
  let stSc : Var [.prod (.prod paTy simTy) fgSessCtrTy, qPayTy]
      (.prod (.prod paTy simTy) fgSessCtrTy) := .zero
  let x : Var [.prod (.prod paTy simTy) fgSessCtrTy, qPayTy] qPayTy := .succ .zero
  letV (.fst (v stSc)) fun st =>
  letV (.fst (v st)) fun pa =>
  letV (.snd (v st)) fun sm =>
  letV (smBase (v sm)) fun bSt =>
  letV (.snd (v stSc)) fun fgSh =>
  bindV (body pa sm bSt fgSh x) fun r =>
  .ret (.pair (.fst (v r)) (.pair (.pair (v pa) (.fst (.snd (v r)))) (.snd (.snd (v r)))))

@[expose] def wrapNoFgArm {paTy qPayTy : PT}
    (body : Var [paTy, .prod paTy simTy, qPayTy] paTy →
      Var [simTy, paTy, .prod paTy simTy, qPayTy] simTy →
      Var [keyIndStateTy, simTy, paTy, .prod paTy simTy, qPayTy] keyIndStateTy →
      Var [.prod paTy simTy, qPayTy] qPayTy →
      Comp pqxdhOps pqGapDhIface
        [keyIndStateTy, simTy, paTy, .prod paTy simTy, qPayTy]
        (.prod keyIndRespTy (.prod paTy simTy))) :
    Comp pqxdhOps pqGapDhIface [.prod paTy simTy, qPayTy]
      (.prod keyIndRespTy (.prod paTy simTy)) :=
  let st : Var [.prod paTy simTy, qPayTy] (.prod paTy simTy) := .zero
  let x : Var [.prod paTy simTy, qPayTy] qPayTy := .succ .zero
  letV (.fst (v st)) fun pa =>
  letV (.snd (v st)) fun sm =>
  letV (smBase (v sm)) fun bSt =>
  body pa sm bSt x

/-- Tuple-keyed 14-way shadow-indexed `KeyInd` Gap-DH query handler in `pqAtomicOps`. -/
@[expose] def gdhShadowHandle2Atomic {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) (S : Setup) (f : KeyIndKFuels) :
    Comp pqAtomicOps A.toIface [gdhShadowState2AtomicTy, (pqKeyIndCodec S).Q]
      (.prod (pqKeyIndCodec S).R gdhShadowState2AtomicTy) :=
  dispatchKeyIndQ S .v1
    (liftKind0NoFgArm gl S (aop (.finVal S.N_id) .v0)
      (wrapNoFgArm fun pa sm bSt u => wrapSim2 pa (initPrinGdh2B f.kOn pa sm bSt u)))
    (liftKind0NoFgArm gl S (aop (.finVal S.N_id) .v0)
      (wrapNoFgArm fun pa sm bSt u => wrapBase2 pa sm (corruptB f.kOn bSt u)))
    (liftKind0NoFgArm gl S (finPairToNatE S.N_id S.N_recv .v0)
      (wrapNoFgArm fun pa sm bSt x => wrapSim2 pa (genSpkGdh2B f.kOn pa sm bSt x)))
    (liftKind0NoFgArm gl S (finTripleToNatE S.N_id S.N_recv S.N_opk .v0)
      (wrapNoFgArm fun pa sm bSt x => wrapSim2 pa (genOpkGdh2B f.kOn pa sm bSt x)))
    (liftKind0SessArm gl S (initPayToNatE S.N_send_opk S .v0)
      (wrapSimSessArm fun pa sm bSt fgSh x => initiateGdh2ShadowB S f pa sm bSt fgSh true x))
    (liftKind0SessArm gl S (initPayToNatE S.N_send_no_opk S .v0)
      (wrapSimSessArm fun pa sm bSt fgSh x => initiateGdh2ShadowB S f pa sm bSt fgSh false x))
    (liftKind0SessArm gl S (accPayToNatE S.N_opk S .v0)
      (wrapSimSessArm fun pa sm bSt fgSh x => acceptOpkGdh2ShadowB S f pa sm bSt fgSh x))
    (liftKind0SessArm gl S (accPayToNatE S.N_no_opk S .v0)
      (wrapSimSessArm fun _ sm bSt fgSh x => acceptNoOpkGdhShadowB S f sm bSt fgSh x))
    (liftKind0NoFgArm gl S (finSidToNatExpr S .v0)
      (wrapNoFgArm fun pa sm bSt sid => wrapBase2 pa sm (testB f.kOn bSt sid)))
    (liftKind1RoArm gl S f)
    (.ret (.pair atomicRNoneE .v1))
    (liftKind0NoFgArm gl S (finSidToNatExpr S .v0)
      (wrapNoFgArm fun pa sm bSt sid => wrapBase2 pa sm (revealB f.kOn bSt sid)))
    (liftKind0NoFgArm gl S .v0
      (wrapNoFgArm fun pa sm bSt sk => wrapSim2 pa (registerGdhB sm bSt sk)))
    (liftKind0NoFgArm gl S (finPairToNatE S.N_id S.N_recv .v0)
      (wrapNoFgArm fun pa sm bSt x => wrapBase2 pa sm (revealSpkB f.kOn bSt x)))

/-- Stage-1 14-way shadow-indexed `KeyInd` Gap-DH query handler in `pqAtomicOps`. -/
@[expose] def gdhShadowHandleAtomic {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) (S : Setup) (f : KeyIndKFuels) :
    Comp pqAtomicOps A.toIface [gdhShadowStateAtomicTy, (pqKeyIndCodec S).Q]
      (.prod (pqKeyIndCodec S).R gdhShadowStateAtomicTy) :=
  dispatchKeyIndQ S .v1
    (liftKind0NoFgArm gl S (aop (.finVal S.N_id) .v0)
      (wrapNoFgArm fun pa sm bSt u => wrapSim pa (initPrinGdhB f.kOn pa sm bSt u)))
    (liftKind0NoFgArm gl S (aop (.finVal S.N_id) .v0)
      (wrapNoFgArm fun pa sm bSt u => wrapBase pa sm (corruptB f.kOn bSt u)))
    (liftKind0NoFgArm gl S (finPairToNatE S.N_id S.N_recv .v0)
      (wrapNoFgArm fun pa sm bSt x => wrapSim pa (genSpkGdhB S f.kOn pa sm bSt x)))
    (liftKind0NoFgArm gl S (finTripleToNatE S.N_id S.N_recv S.N_opk .v0)
      (wrapNoFgArm fun pa sm bSt x => wrapSim pa (genOpkGdhB S f.kOn pa sm bSt x)))
    (liftKind0SessArm gl S (initPayToNatE S.N_send_opk S .v0)
      (wrapSimSessArm fun pa sm bSt fgSh x => initiateGdhShadowB S f pa sm bSt fgSh true x))
    (liftKind0SessArm gl S (initPayToNatE S.N_send_no_opk S .v0)
      (wrapSimSessArm fun pa sm bSt fgSh x => initiateGdhShadowB S f pa sm bSt fgSh false x))
    (liftKind0SessArm gl S (accPayToNatE S.N_opk S .v0)
      (wrapSimSessArm fun pa sm bSt fgSh x => acceptOpkGdhShadowB S f pa sm bSt fgSh x))
    (liftKind0SessArm gl S (accPayToNatE S.N_no_opk S .v0)
      (wrapSimSessArm fun _ sm bSt fgSh x => acceptNoOpkGdhShadowB S f sm bSt fgSh x))
    (liftKind0NoFgArm gl S (finSidToNatExpr S .v0)
      (wrapNoFgArm fun pa sm bSt sid => wrapBase pa sm (testB f.kOn bSt sid)))
    (liftKind1RoArm gl S f)
    (.ret (.pair atomicRNoneE .v1))
    (liftKind0NoFgArm gl S (finSidToNatExpr S .v0)
      (wrapNoFgArm fun pa sm bSt sid => wrapBase pa sm (revealB f.kOn bSt sid)))
    (liftKind0NoFgArm gl S .v0
      (wrapNoFgArm fun pa sm bSt sk => wrapSim pa (registerGdhB sm bSt sk)))
    (liftKind0NoFgArm gl S (finPairToNatE S.N_id S.N_recv .v0)
      (wrapNoFgArm fun pa sm bSt x => wrapBase pa sm (revealSpkB f.kOn bSt x)))

@[expose] def gdhShadowFinish2Atomic {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) (S : Setup) (f : KeyIndKFuels) :
    Comp pqAtomicOps A.toIface [gdhShadowState2AtomicTy, .bool] (PB 32) :=
  runAt2 (.fst .v0) .v1 (liftGdhAtomic gl (gdhFinish2K S f))

@[expose] def gdhShadowFinishAtomic {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    (gl : GdhAtomicLift A) (S : Setup) (f : KeyIndKFuels) :
    Comp pqAtomicOps A.toIface [gdhShadowStateAtomicTy, .bool] (PB 32) :=
  runAt2 (.fst .v0) .v1 (liftGdhAtomic gl (gdhFinishK S f))

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK
