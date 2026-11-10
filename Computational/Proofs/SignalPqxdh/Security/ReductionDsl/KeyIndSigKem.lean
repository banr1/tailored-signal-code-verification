/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndCore

/-!
# Costed DSL Programs for the `KeyInd` `SigEufCma` and `KemShCr` Reductions

Defines the first-order `ReductionDsl` programs `sigKeyIndProg` (`CostedReduction`) and
`shcrKeyIndProg` (`TwoStageCostedReduction`) for the `KeyInd` signature and KEM collision-resistance
reductions.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyInd

def widenEC {Γ : List PT} (e : Expr pqxdhOps Γ (B 33)) : Expr pqxdhOps Γ (B 1569) :=
  widenB 33 1536 e

def qChalSign (m : ℕ+) {Γ : List PT} (msg : Expr pqxdhOps Γ (B m)) :
    Comp pqxdhOps pqxdhEufCmaIface Γ (B 64) :=
  Comp.query (I := pqxdhEufCmaIface) (Sum.inr m) msg

/-! ## `SigEufCma` reduction -/

/-- State type `(game, targetParty, targetPk, forgery, signBudget)` of `sigKeyIndProg`. -/
abbrev sigStTy : PT :=
  .prod keyIndStateTy (.prod .nat (.prod (B 32) (.prod (.opt (.prod (B 1569) (B 64))) .nat)))

@[reducible] def sgGame {Γ : List PT} (e : Expr pqxdhOps Γ sigStTy) : Expr pqxdhOps Γ keyIndStateTy :=
  .fst e
@[reducible] def sgTarget {Γ : List PT} (e : Expr pqxdhOps Γ sigStTy) : Expr pqxdhOps Γ .nat :=
  .fst (.snd e)
@[reducible] def sgPk {Γ : List PT} (e : Expr pqxdhOps Γ sigStTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd e))
@[reducible] def sgForgery {Γ : List PT} (e : Expr pqxdhOps Γ sigStTy) :
    Expr pqxdhOps Γ (.opt (.prod (B 1569) (B 64))) :=
  .fst (.snd (.snd (.snd e)))
@[reducible] def sgBudget {Γ : List PT} (e : Expr pqxdhOps Γ sigStTy) : Expr pqxdhOps Γ .nat :=
  .snd (.snd (.snd (.snd e)))

@[reducible] def sgUpd {Γ : List PT} (e : Expr pqxdhOps Γ sigStTy)
    (game : Expr pqxdhOps Γ keyIndStateTy := sgGame e)
    (forgery : Expr pqxdhOps Γ (.opt (.prod (B 1569) (B 64))) := sgForgery e)
    (budget : Expr pqxdhOps Γ .nat := sgBudget e) : Expr pqxdhOps Γ sigStTy :=
  .pair game (.pair (sgTarget e) (.pair (sgPk e) (.pair forgery budget)))

abbrev SRS : PT := .prod keyIndRespTy sigStTy

section SigBranches

variable (useRo : Bool) (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}

def onGame (s : Var Γ₁ sigStTy) [Ext Γ₁ Δ]
    (br : (g : Var (keyIndStateTy :: Δ) keyIndStateTy) →
      Comp pqxdhOps pqPrimIface (keyIndStateTy :: Δ) RS) :
    Comp pqxdhOps pqxdhEufCmaIface Δ SRS :=
  bindV (liftBase (letV (sgGame (v s)) fun g => br g)) fun r =>
  .ret (.pair (.fst (v r)) (sgUpd (v s) (game := .snd (v r))))

def extractC (s : Var Γ₁ sigStTy) (bu : Var Γ₂ preKeyBundleTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqxdhEufCmaIface Δ (.opt (.prod (B 1569) (B 64))) :=
  bindV (liftBase (letV (sgGame (v s)) fun g => honestPeerC S K g (buIkB (v bu)))) fun peer =>
  bindV (liftBase (qSigVerify 33
      (.pair (sgPk (v s)) (.pair (encEC (buSpkB (v bu))) (buSpkSig (v bu)))))) fun v1 =>
  bindV (liftBase (qSigVerify 1569
      (.pair (sgPk (v s)) (.pair (encKEM (buPqspkB (v bu))) (buPqspkSig (v bu)))))) fun v2 =>
  .ret (eCaseOpt (sgForgery (v s))
    (eCaseOpt (v peer) .none fun k =>
      .ite (natEq (v k) (sgTarget (v s)))
        (.ite (.and (v v1) (.not (eAny K (stSpks (sgGame (v s))) fun e =>
            .and (natEq (.fst (.fst (v e))) (v k)) (eqB (sbSpkPk (.snd (v e))) (buSpkB (v bu))))))
          (.some (.pair (widenEC (encEC (buSpkB (v bu)))) (buSpkSig (v bu))))
          (.ite (.and (v v2) (.not (eAny K (stSpks (sgGame (v s))) fun e =>
              .and (natEq (.fst (.fst (v e))) (v k))
                (eqB (sbPqspkPk (.snd (v e))) (buPqspkB (v bu))))))
            (.some (.pair (encKEM (buPqspkB (v bu))) (buPqspkSig (v bu))))
            .none))
        .none)
    fun fg => .some (v fg))

def sigInitPrinB (s : Var Γ₁ sigStTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqxdhEufCmaIface Δ SRS :=
  .ite (eAny K (stPrin (sgGame (v s))) fun e => natEq (.fst (v e)) (v u))
    (.ret (.pair rNone (v s))) <|
  .ite (natEq (v u) (sgTarget (v s)))
    (bindV (liftBase sBytes32) fun s0 =>
      bindV (liftBase (qX25519Base (v s0))) fun ik =>
      .ret (.pair (rInitPrin (v ik) (sgPk (v s))) (sgUpd (v s) (game := stUpd (sgGame (v s))
        (prin := .cons (.pair (v u) (peMk (v s0) (v ik) (litB 32 []) (sgPk (v s))
          (.bool false))) (stPrin (sgGame (v s))))))))
    (onGame s fun g => initPrinB K g u)

def sigCorruptB (s : Var Γ₁ sigStTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqxdhEufCmaIface Δ SRS :=
  .ite (natEq (v u) (sgTarget (v s)))
    (caseOptV (eFind K (stPrin (sgGame (v s))) fun e => natEq (.fst (v e)) (v u))
      (.ret (.pair rNone (v s))) fun _ =>
      .ret (.pair rNone (sgUpd (v s) (game := stUpd (sgGame (v s))
        (prin := eMap K (stPrin (sgGame (v s))) fun x =>
          .ite (natEq (.fst (v x)) (v u))
            (.pair (.fst (v x)) (peUpd (.snd (v x)) (corrupted := .bool true))) (v x))))))
    (onGame s fun g => corruptB K g u)

def sigGenSpkB (s : Var Γ₁ sigStTy) (x : Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqxdhEufCmaIface Δ SRS :=
  .ite (natEq (.fst (v x)) (sgTarget (v s)))
    (.ite (eAny K (stSpks (sgGame (v s))) fun e => nat2Eq (.fst (v e)) (v x))
      (.ret (.pair rNone (v s))) <|
    caseOptV (eFind K (stPrin (sgGame (v s))) fun e => natEq (.fst (v e)) (.fst (v x)))
      (.ret (.pair rNone (v s))) fun uE =>
    bindV (liftBase sBytes32) fun spkSk =>
    bindV (liftBase (qX25519Base (v spkSk))) fun spkPk =>
    .ite (natEq (sgBudget (v s)) (.nat 0)) (.ret (.pair rNone (v s))) <|
    bindV (qChalSign 33 (encEC (v spkPk))) fun sig1 =>
    bindV (liftBase sRandom64) fun seed =>
    bindV (liftBase (qKemKeyGen (v seed))) fun kp =>
    bindV (qChalSign 1569 (encKEM (.fst (v kp)))) fun sig2 =>
    .ret (.pair (rBundle (buMk (peIkAPk (.snd (v uE))) (u32OfNat (.snd (v x))) (v spkPk) (v sig1)
        .none (u32OfNat (.snd (v x))) (.fst (v kp)) (v sig2)))
      (sgUpd (v s)
        (game := stUpd (sgGame (v s)) (spks := .cons (.pair (v x) (sbMk (v spkSk) (v spkPk)
          (v sig1) (.snd (v kp)) (.fst (v kp)) (v sig2) (.bool false))) (stSpks (sgGame (v s)))))
        (budget := .sub (sgBudget (v s)) (.nat 1)))))
    (onGame s fun g => genSpkB K g x)

def sigInitiateB (opk : Bool) (s : Var Γ₁ sigStTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqxdhEufCmaIface Δ SRS :=
  letV (.snd (.snd (v x))) fun bu =>
  bindV (extractC S K s bu) fun fg =>
  bindV (liftBase (letV (sgGame (v s)) fun g =>
      if opk then initiateOpkB useRo S K g x else initiateNoOpkB useRo S K g x)) fun r =>
  .ret (.pair (.fst (v r)) (sgUpd (v s) (game := .snd (v r)) (forgery := v fg)))

def sigHandleC (s : Var Γ₁ sigStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqxdhEufCmaIface Δ SRS :=
  .ite (isSomeE (sgForgery (v s))) (.ret (.pair rNone (v s))) <|
  caseSumV (v q) (fun u => sigInitPrinB K s u) fun q =>
  caseSumV (v q) (fun u => sigCorruptB K s u) fun q =>
  caseSumV (v q) (fun x => sigGenSpkB K s x) fun q =>
  caseSumV (v q) (fun x => onGame s fun g => genOpkB K g x) fun q =>
  caseSumV (v q) (fun x => sigInitiateB useRo S K true s x) fun q =>
  caseSumV (v q) (fun x => sigInitiateB useRo S K false s x) fun q =>
  caseSumV (v q) (fun x => onGame s fun g => acceptOpkB useRo S K g x) fun q =>
  caseSumV (v q) (fun x => onGame s fun g => acceptNoOpkB useRo S K g x) fun q =>
  caseSumV (v q) (fun sid => onGame s fun g => testB K g sid) fun q =>
  caseSumV (v q) (fun sec => onGame s fun g => roB useRo K g sec) fun q =>
  caseSumV (v q) (fun _ => onGame s fun g => revealDhB useRo K g) fun q =>
  caseSumV (v q) (fun sid => onGame s fun g => revealB K g sid) fun q =>
  caseSumV (v q) (fun sk => onGame s fun g => registerB g sk) fun x =>
  onGame s fun g => revealSpkB K g x

end SigBranches

/-- Costed-DSL program for the `KeyInd` `SigEufCma` reduction (`sigReductionKeyIndCore`). -/
def sigKeyIndProg (useRo : Bool) (S : Setup) (K : Nat) :
    CostedReduction pqxdhOps pqxdhEufCmaIface (keyIndSpec S) (keyIndCodec S) (B 32) .unit .bool (.prod (B 1569) (B 64))
    where
  σ := sigStTy
  init :=
    bindV (liftBase (sIndex S.N_id)) fun k =>
    bindV (liftBase sBool) fun secb =>
    .ret (.pair .unit (.pair (emptyStE (v secb)) (.pair (v k)
      (.pair (.var (.succ (.succ .zero))) (.pair .none (.nat (min K S.N_spk_tot)))))))
  handle := sigHandleC useRo S K (Γ₁ := [sigStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
    (Δ := [sigStTy, keyIndQueryTy]) .zero .zero
  finish := .ret (if S.N_id = 0 then
    .pair (litB 1569 []) (litB 64 [])
  else
    eCaseOpt (sgForgery (.var .zero)) (.pair (litB 1569 []) (litB 64 [])) fun fg => v fg)

/-! ## `KemShCr` reduction -/

abbrev initRecTy : PT := .prod .nat (.prod sessionIdTy (.prod (B 1568) (.prod (B 1568) (B 32))))
abbrev recvRecTy : PT :=
  .prod .nat (.prod .nat (.prod .nat (.prod (B 1568) (.prod (B 3168) (.prod (B 1568) (B 32))))))

/-- State type `(base, targetSpk?, targetPk, targetSk, sendCount, initKemRecs, recvKemRecs, sIdx, chosenPk)`
    of `shcrKeyIndProg`. -/
abbrev shcrStTy : PT :=
  .prod keyIndStateTy (.prod (.opt (.prod .nat .nat)) (.prod (B 1568) (.prod (B 3168) (.prod .nat
    (.prod (.list initRecTy) (.prod (.list recvRecTy) (.prod .nat (B 1568))))))))

@[reducible] def scBase {Γ : List PT} (e : Expr pqxdhOps Γ shcrStTy) : Expr pqxdhOps Γ keyIndStateTy :=
  .fst e
@[reducible] def scTB {Γ : List PT} (e : Expr pqxdhOps Γ shcrStTy) :
    Expr pqxdhOps Γ (.opt (.prod .nat .nat)) :=
  .fst (.snd e)
@[reducible] def scTPk {Γ : List PT} (e : Expr pqxdhOps Γ shcrStTy) : Expr pqxdhOps Γ (B 1568) :=
  .fst (.snd (.snd e))
@[reducible] def scTSk {Γ : List PT} (e : Expr pqxdhOps Γ shcrStTy) : Expr pqxdhOps Γ (B 3168) :=
  .fst (.snd (.snd (.snd e)))
@[reducible] def scCnt {Γ : List PT} (e : Expr pqxdhOps Γ shcrStTy) : Expr pqxdhOps Γ .nat :=
  .fst (.snd (.snd (.snd (.snd e))))
@[reducible] def scIR {Γ : List PT} (e : Expr pqxdhOps Γ shcrStTy) : Expr pqxdhOps Γ (.list initRecTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd e)))))
@[reducible] def scRR {Γ : List PT} (e : Expr pqxdhOps Γ shcrStTy) : Expr pqxdhOps Γ (.list recvRecTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd e))))))
@[reducible] def scSIdx {Γ : List PT} (e : Expr pqxdhOps Γ shcrStTy) : Expr pqxdhOps Γ .nat :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))
@[reducible] def scChosen {Γ : List PT} (e : Expr pqxdhOps Γ shcrStTy) : Expr pqxdhOps Γ (B 1568) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))

@[reducible] def scMk {Γ : List PT} (base : Expr pqxdhOps Γ keyIndStateTy)
    (tB : Expr pqxdhOps Γ (.opt (.prod .nat .nat)))
    (tPk : Expr pqxdhOps Γ (B 1568)) (tSk : Expr pqxdhOps Γ (B 3168))
    (cnt : Expr pqxdhOps Γ .nat) (iR : Expr pqxdhOps Γ (.list initRecTy))
    (rR : Expr pqxdhOps Γ (.list recvRecTy)) (sIdx : Expr pqxdhOps Γ .nat) (chosen : Expr pqxdhOps Γ (B 1568)) :
    Expr pqxdhOps Γ shcrStTy :=
  .pair base (.pair tB (.pair tPk (.pair tSk (.pair cnt
    (.pair iR (.pair rR (.pair sIdx chosen)))))))

@[reducible] def scUpd {Γ : List PT} (e : Expr pqxdhOps Γ shcrStTy)
    (base : Expr pqxdhOps Γ keyIndStateTy := scBase e) (cnt : Expr pqxdhOps Γ .nat := scCnt e)
    (iR : Expr pqxdhOps Γ (.list initRecTy) := scIR e) (rR : Expr pqxdhOps Γ (.list recvRecTy) := scRR e)
    (chosen : Expr pqxdhOps Γ (B 1568) := scChosen e) : Expr pqxdhOps Γ shcrStTy :=
  scMk base (scTB e) (scTPk e) (scTSk e) cnt iR rR (scSIdx e) chosen

@[reducible] def rrCt {Γ : List PT} (e : Expr pqxdhOps Γ recvRecTy) : Expr pqxdhOps Γ (B 1568) :=
  .fst (.snd (.snd (.snd (.snd (.snd e)))))

abbrev pauseTy : PT := .prod sessionIdTy (.prod preKeyBundleTy (.prod .nat principalEntryTy))

abbrev SCS : PT := .prod keyIndRespTy shcrStTy

def isNoneRespE {Γ : List PT} (r : Expr pqxdhOps Γ keyIndRespTy) : Expr pqxdhOps Γ .bool :=
  eCaseSum r (fun _ => .bool true) fun _ => .bool false

section ShCrBranches

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}

def onBase (s : Var Γ₁ shcrStTy) [Ext Γ₁ Δ]
    (br : (g : Var (keyIndStateTy :: Δ) keyIndStateTy) →
      Comp pqxdhOps pqPrimIface (keyIndStateTy :: Δ) RS) :
    Comp pqxdhOps pqPrimIface Δ SCS :=
  bindV (letV (scBase (v s)) fun g => br g) fun r =>
  .ret (.pair (.fst (v r)) (scUpd (v s) (base := .snd (v r))))

def shcrFinE {Γ : List PT} (s : Expr pqxdhOps Γ shcrStTy) (sid : Expr pqxdhOps Γ sessionIdTy)
    (bu : Expr pqxdhOps Γ preKeyBundleTy) (sc : Expr pqxdhOps Γ (.prod (B 32) (B 1568)))
    (r : Expr pqxdhOps Γ RS) : Expr pqxdhOps Γ SCS :=
  .pair (.fst r) (scUpd s (base := .snd r) (cnt := .add (scCnt s) (.nat 1))
    (iR := .cons (.pair (scCnt s) (.pair sid (.pair (buPqspkB bu) (.pair (.snd sc) (.fst sc)))))
      (scIR s)))

def nRecv (S : Setup) : Nat := if S.N_id = 0 then 0 else S.N_recv

def shcrGenSpkB (s : Var Γ₁ shcrStTy) (x : Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ SCS :=
  let _ := S
  caseOptV (scTB (v s)) (onBase s fun g => genSpkB K g x) fun bIdx =>
  .ite (.not (nat2Eq (v x) (v bIdx)))
    (onBase s fun g => genSpkB K g x) <|
  .ite (eAny K (stSpks (scBase (v s))) fun e => nat2Eq (.fst (v e)) (v x))
    (.ret (.pair rNone (v s))) <|
  caseOptV (eFind K (stPrin (scBase (v s))) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (.pair rNone (v s))) fun uE =>
  bindV sBytes32 fun spkSk =>
  bindV (qX25519Base (v spkSk)) fun spkPk =>
  bindV sRandom64 fun r1 =>
  bindV (qSigSign 33 (.pair (peSecIKAsign (.snd (v uE))) (.pair (encEC (v spkPk)) (v r1))))
    fun sig1 =>
  bindV sRandom64 fun r2 =>
  bindV (qSigSign 1569 (.pair (peSecIKAsign (.snd (v uE))) (.pair (encKEM (scTPk (v s))) (v r2))))
    fun sig2 =>
  .ret (.pair (rBundle (buMk (peIkAPk (.snd (v uE))) (u32OfNat (.snd (v x))) (v spkPk) (v sig1)
      .none (u32OfNat (.snd (v x))) (scTPk (v s)) (v sig2)))
    (scUpd (v s) (base := stUpd (scBase (v s)) (spks := .cons (.pair (v x) (sbMk (v spkSk)
      (v spkPk) (v sig1) (scTSk (v s)) (scTPk (v s)) (v sig2) (.bool false)))
      (stSpks (scBase (v s)))))))

def initGuardE {Γ : List PT} (opk : Bool) (x : Expr pqxdhOps Γ initQTy) : Expr pqxdhOps Γ .bool :=
  if opk then .not (isSomeE (buOpkB (.snd (.snd x)))) else isSomeE (buOpkB (.snd (.snd x)))

def shcrInitiateC (opk : Bool) (s : Var Γ₁ shcrStTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ SCS :=
  .ite (initGuardE opk (v x)) (.ret (.pair rNone (v s))) <|
  letV (.snd (.snd (v x))) fun bu => letV (initSidE opk (v x)) fun sid =>
  letV (scBase (v s)) fun st => letV (.fst (v x)) fun u =>
  bindV (preCheckC S K st sid u bu) fun pc =>
  caseOptV (v pc) (.ret (.pair rNone (v s))) fun uE =>
  bindV sBytes32 fun ekSk =>
  bindV sBytes32 fun coins =>
  bindV (checkSigsC S K st bu) fun ok =>
  .ite (.not (v ok)) (.ret (.pair rNone (v s))) <|
  bindV (qKemEncaps (.pair (buPqspkB (v bu)) (v coins))) fun enc =>
  caseOptV (v enc)
    (.ret (.pair rNone (scUpd (v s) (cnt := .add (scCnt (v s)) (.nat 1))))) fun sc =>
  bindV (initFinishC true S K st sid bu uE ekSk sc) fun r =>
  .ret (shcrFinE (v s) (v sid) (v bu) (v sc) (v r))

def shcrAcceptB (opk : Bool) (s : Var Γ₁ shcrStTy) (x : Var Γ₂ accQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ SCS :=
  bindV (onBase s fun g => if opk then acceptOpkB true S K g x else acceptNoOpkB true S K g x)
    fun r =>
  .ite (isNoneRespE (.fst (v r))) (.ret (v r)) <|
  caseOptV (eFind K (stSpks (scBase (.snd (v r)))) fun e =>
      nat2Eq (.fst (v e)) (.pair (qK (v x)) (qJ (v x))))
    (.ret (v r)) fun bE =>
  bindV (qKemDecaps (.pair (sbPqspkSk (.snd (v bE))) (hdKemCt (qHdr (v x))))) fun ss? =>
  caseOptV (v ss?) (.ret (v r)) fun ss =>
  .ret (.pair (.fst (v r)) (scUpd (.snd (v r)) (rR := .cons
    (.pair (.nat 0)
      (.pair (qK (v x)) (.pair (qJ (v x)) (.pair (sbPqspkPk (.snd (v bE)))
        (.pair (sbPqspkSk (.snd (v bE))) (.pair (hdKemCt (qHdr (v x))) (v ss)))))))
    (scRR (.snd (v r))))))

def shcrPostC (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ SCS :=
  caseSumV (v q) (fun u => onBase s fun g => initPrinB K g u) fun q =>
  caseSumV (v q) (fun u => onBase s fun g => corruptB K g u) fun q =>
  caseSumV (v q) (fun x => shcrGenSpkB S K s x) fun q =>
  caseSumV (v q) (fun x => onBase s fun g => genOpkB K g x) fun q =>
  caseSumV (v q) (fun x => shcrInitiateC S K true s x) fun q =>
  caseSumV (v q) (fun x => shcrInitiateC S K false s x) fun q =>
  caseSumV (v q) (fun x => shcrAcceptB S K true s x) fun q =>
  caseSumV (v q) (fun x => shcrAcceptB S K false s x) fun q =>
  caseSumV (v q) (fun sid => onBase s fun g => testB K g sid) fun q =>
  caseSumV (v q) (fun sec => onBase s fun g => roB true K g sec) fun q =>
  caseSumV (v q) (fun _ => onBase s fun g => revealDhB true K g) fun q =>
  caseSumV (v q) (fun sid => onBase s fun g => revealB K g sid) fun q =>
  caseSumV (v q) (fun sk => onBase s fun g => registerB g sk) fun x =>
  onBase s fun g => revealSpkB K g x

def tryPauseC (opk : Bool) (s : Var Γ₁ shcrStTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ (.opt pauseTy) :=
  .ite (initGuardE opk (v x)) (.ret .none) <|
  letV (.snd (.snd (v x))) fun bu => letV (initSidE opk (v x)) fun sid =>
  letV (scBase (v s)) fun st => letV (.fst (v x)) fun u =>
  bindV (preCheckC S K st sid u bu) fun pc =>
  caseOptV (v pc) (.ret .none) fun uE =>
  bindV (checkSigsC S K st bu) fun ok =>
  .ret (.ite (.not (v ok)) .none
    (.ite (natEq (scCnt (v s)) (scSIdx (v s))) (.some (.pair (v sid) (.pair (v bu) (v uE)))) .none))

def pauseCheckC (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ (.opt pauseTy) :=
  caseSumV (v q) (fun _ => .ret .none) fun q =>
  caseSumV (v q) (fun _ => .ret .none) fun q =>
  caseSumV (v q) (fun _ => .ret .none) fun q =>
  caseSumV (v q) (fun _ => .ret .none) fun q =>
  caseSumV (v q) (fun x => tryPauseC S K true s x) fun q =>
  caseSumV (v q) (fun x => tryPauseC S K false s x) fun _ =>
  .ret .none

def shcrPreC (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ (.sum SCS (.prod (B 1568) (.prod pauseTy shcrStTy))) :=
  bindV (pauseCheckC S K s q) fun p =>
  caseOptV (v p) (bindV (shcrPostC S K s q) fun r => .ret (.inl (v r))) fun d =>
  .ret (.inr (.pair (buPqspkB (.fst (.snd (v d)))) (.pair (v d) (v s))))

def shcrResumeC (sc : Var Γ₁ (.prod (B 32) (B 1568))) (d : Var Γ₂ pauseTy)
    (s : Var Γ₃ shcrStTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : Comp pqxdhOps pqPrimIface Δ SCS :=
  letV (scBase (v s)) fun st => letV (.fst (v d)) fun sid =>
  letV (.fst (.snd (v d))) fun bu => letV (.snd (.snd (v d))) fun uE =>
  bindV sBytes32 fun ekSk =>
  bindV (initFinishC true S K st sid bu uE ekSk sc) fun r =>
  letV (shcrFinE (v s) (v sid) (v bu) (v sc) (v r)) fun out =>
  .ret (.pair (.fst (v out)) (scUpd (.snd (v out)) (chosen := buPqspkB (v bu))))

def shcrExtractC (Q : Nat) (sc : Var Γ₁ (.prod (B 32) (B 1568))) (s : Var Γ₃ shcrStTy)
    [Ext Γ₁ Δ] [Ext Γ₃ Δ] : Comp pqxdhOps pqPrimIface Δ (B 1568) :=
  bindV (findMV Q (scRR (v s)) fun r =>
    bindV (qKemDecaps (.pair (scTSk (v s)) (rrCt (v r)))) fun dec =>
    .ret (.and (optBytesEq (v dec) (.some (.fst (v sc))))
      (orE (.not (eqB (rrCt (v r)) (.snd (v sc))))
        (.not (eqB (scChosen (v s)) (scTPk (v s))))))) fun f =>
  .ret (eCaseOpt (v f) (.snd (v sc)) fun r => rrCt (v r))

end ShCrBranches

/-- Two-stage costed-DSL program for the `KeyInd` `KemShCr` reduction (`shcrReductionKeyIndCore`). -/
def shcrKeyIndProg (S : Setup) (Q K : Nat) :
    TwoStageCostedReduction pqxdhOps pqPrimIface (keyIndSpec S) (keyIndCodec S)
      (.prod (B 1568) (B 3168)) .unit .bool (B 1568) (.prod (B 32) (B 1568)) (B 1568) where
  σ := shcrStTy
  π := pauseTy
  init :=
    if S.N_spk_tot * S.N_send_tot = 0 then
      bindV sBool fun secb =>
      .ret (.pair .unit (scMk (emptyStE (v secb)) (.some (.pair (.nat 0) (.nat 0)))
        (.fst (.var (.succ .zero))) (.snd (.var (.succ .zero))) (.nat 0) .nil .nil
        (.nat 0) (.fst (.var (.succ .zero)))))
    else
      bindV (sIndex S.N_id) fun u =>
      bindV (sIndex S.N_recv) fun j =>
      bindV (sIndex S.N_send_tot) fun sIdx =>
      bindV sBool fun secb =>
      .ret (.pair .unit (scMk (emptyStE (v secb)) (.some (.pair (v u) (v j)))
        (.fst (.var (.succ (.succ (.succ (.succ .zero))))))
        (.snd (.var (.succ (.succ (.succ (.succ .zero))))))
        (.nat 0) .nil .nil (v sIdx)
        (.fst (.var (.succ (.succ (.succ (.succ .zero))))))))
  handlePre := shcrPreC S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
    (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  chDone := .ret (scTPk (.var .zero))
  resume := shcrResumeC S K (Γ₁ := [.prod (B 32) (B 1568)])
    (Γ₂ := [pauseTy, .prod (B 32) (B 1568)])
    (Γ₃ := [shcrStTy, pauseTy, .prod (B 32) (B 1568)])
    (Δ := [shcrStTy, pauseTy, .prod (B 32) (B 1568)]) .zero .zero .zero
  handlePost := shcrPostC S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
    (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  finish := shcrExtractC (Γ₁ := [.prod (B 32) (B 1568)])
    (Γ₃ := [shcrStTy, .bool, .prod (B 32) (B 1568)])
    (Δ := [shcrStTy, .bool, .prod (B 32) (B 1568)]) Q .zero .zero

end SignalPqxdh.Security.ReductionDsl.KeyInd
