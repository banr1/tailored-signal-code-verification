/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs
public import Computational.Specifications.Pqxdh.Bound
public import Computational.Specifications.Pqxdh.Security.Headline

/-!
# Per-Query-Kind Active Reductions for One-Key PQXDH `KeyInd`

Defines the native `pqAtomicOps` creation-order reductions `sigKeyInd1KeyKindAtomicProg`,
`shcrKeyInd1KeyKindAtomicProg`, and `fgKeyInd1KeyGapDhKindAtomicProg` over shadow-indexed
states with outer 14-way query-constructor dispatch, packaged as `pqxdhKeyInd1KeyKindCostedSims`.
Each `init` clamps unreachable ordinal sentinels to `keyIndSentinel S b`, and the file also proves
`unsupportedW = 0` on the lifted legacy `pqxdhOps` sub-blocks.
-/

namespace Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs

public section

set_option autoImplicit false

section LegacySubBlocks

open _root_.ReductionDsl (Expr Comp Var)
open _root_.SignalPqxdh (Setup QueryBudget activeIdCount activeSpkCount activeOpkCount
  activeSendCount activeSendOpkCount)
open _root_.SignalPqxdh.LegacyCosted (sigAndDdhOracle pqxdhOps B pqSigAndDdhIface pqPrimIface
  pqGapDhIface)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (Ext PT v letV bindV isSomeE rNone
  keyIndRespTy initQTy accQTy s1Prim s1Forgery s1Fg s1Pk s1Upd s1Mk emptySimE emptyStE shcrStTy
  scMk sig1KeyStTy sig1KeyTargetGenSpkB liftGdhToSigDdh keyIndStateTy simTy params2Ty gdhState2Ty
  smBase pa2Mk paU paV paUp paOpkMode wrapBase2 wrapSim2 genSpkGdh2B
  sBool sIndex litB eCaseOpt paramsTy paMk gPrim chooseArm2C)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (gdh1KeyStateTy liftGdhComp)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (activeSigBudget optNatMatchesE
  fgActiveTotalIndexCount sig1KeyActiveStTy S1ARS saTP saInner extract1KeyActiveC
  sig1KeyActiveInitPrinB gdh1KeyActiveStateTy initPrin1KeyActiveGdhB genSpk1KeyActiveGdhB
  genOpkActiveGdhB)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK (keyIndSentinel)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK (KeyIndKFuels
  fgSessCtrTy initiateGdh2ShadowB initiateGdhActiveShadowInnerB acceptOpkGdh2ShadowB
  acceptNoOpkGdhShadowB)

section
set_option allowUnsafeReducibility true
attribute [implicit_reducible] sigAndDdhOracle
end

/-- Base `pqxdhOps` `init` for `sigKeyInd1KeyKindAtomicProg`, clamping the unreachable target
    ordinal to `keyIndSentinel S b` when `n_id = 0`. -/
@[expose] def sig1KeyKindBaseInit (S : Setup) (b : QueryBudget) :
    Comp pqxdhOps pqSigAndDdhIface [B 32] (.prod .unit sig1KeyActiveStTy) :=
  let n_id := activeIdCount S b.q_on
  bindV (s1Prim (sIndex n_id)) fun k =>
  bindV (s1Prim sBool) fun secb =>
  let ordE : Expr pqxdhOps _ .nat := if n_id = 0 then .nat (keyIndSentinel S b) else v k
  .ret (.pair .unit (.pair .none
    (s1Mk (emptySimE (v secb)) ordE (.var (.succ (.succ .zero)))
      (.nat (activeSigBudget S b)) .none)))

@[expose] def sig1KeyKindBaseFinish :
    Comp pqxdhOps pqSigAndDdhIface [sig1KeyActiveStTy, .bool] (.prod (B 1569) (B 64)) :=
  .ret (eCaseOpt (s1Forgery (saInner (.var .zero)))
    (.pair (litB 1569 []) (litB 64 [])) fun fg => v fg)

/-- Base `pqxdhOps` `init` for `shcrKeyInd1KeyKindAtomicProg`, clamping `scSIdx` to
    `keyIndSentinel S b` when `n_prod = 0`. -/
@[expose] def shcr1KeyKindBaseInit (S : Setup) (b : QueryBudget) :
    Comp pqxdhOps pqPrimIface [.prod (B 1568) (B 3168)] (.prod .unit shcrStTy) :=
  let n_spk := activeSpkCount S b.q_on
  let n_send := activeSendCount S b.q_on
  let n_prod := n_spk * n_send
  if n_prod = 0 then
    bindV sBool fun secb =>
    .ret (.pair .unit (scMk (emptyStE (v secb)) .none
      (.fst (.var (.succ .zero))) (.snd (.var (.succ .zero))) (.nat 0) .nil .nil
      (.nat (keyIndSentinel S b)) (.fst (.var (.succ .zero)))))
  else
    bindV (sIndex n_spk) fun spkOrd =>
    bindV (sIndex n_send) fun sIdx =>
    bindV sBool fun secb =>
    .ret (.pair .unit (scMk (emptyStE (v secb)) (.some (.pair (v spkOrd) (.nat 0)))
      (.fst (.var (.succ (.succ (.succ .zero))))) (.snd (.var (.succ (.succ (.succ .zero)))))
      (.nat 0) .nil .nil (v sIdx) (.fst (.var (.succ (.succ (.succ .zero)))))))

/-- Flat active parameter decoder matching `initParams1KeyKindC`, clamping the four unreachable
    ordinal slots to `keyIndSentinel S b`. -/
@[expose] def initParams1KeyKindFlat (S : Setup) (b : QueryBudget) {Γ : List PT}
    (U V : Expr pqxdhOps Γ (B 32)) (idx : Expr pqxdhOps Γ .nat) : Expr pqxdhOps Γ paramsTy :=
  let n_id := activeIdCount S b.q_on
  let n_spk := activeSpkCount S b.q_on
  let n_opk := activeOpkCount S b.q_on
  let n_send := activeSendCount S b.q_on
  let nA := n_id * n_spk
  let nC := n_send * n_spk
  let nB := n_send * n_id
  let tot := fgActiveTotalIndexCount S b.q_on
  let unreach := keyIndSentinel S b
  if tot = 0 then
    paMk U V U (.bool false) (.nat unreach) (.bool true) (.nat unreach) (.nat unreach)
      (.bool false) (.nat unreach) (.nat 0)
  else
    .ite (.lt idx (.nat nA))
      (paMk U V U (.bool true) (.divK n_spk idx) (.bool true) (.nat unreach) (.modK n_spk idx)
        (.bool false) (.nat unreach) (.nat 0))
      (.ite (.lt idx (.nat (nA + nC)))
        (let r := Expr.sub idx (.nat nA)
         paMk U V U (.bool false) (.nat unreach) (.bool false) (.divK n_spk r) (.modK n_spk r)
           (.bool false) (.nat unreach) (.nat 1))
        (.ite (.lt idx (.nat (nA + nC + nB)))
          (let r := Expr.sub idx (.nat (nA + nC))
           paMk V U U (.bool true) (.modK n_id r) (.bool false) (.divK n_id r) (.nat unreach)
             (.bool false) (.nat unreach) (.nat 2))
          (let r := Expr.sub idx (.nat (nA + nC + nB))
           paMk U V U (.bool false) (.nat unreach) (.bool false) (.divK n_opk r) (.nat unreach)
             (.bool true) (.modK n_opk r) (.nat 3))))

/-- Four-leg active parameter sampler matching `initParams1KeyKindFlat`, clamping the four
    unreachable ordinal slots to `keyIndSentinel S b`. -/
@[expose] def initParams1KeyKindC (S : Setup) (b : QueryBudget) {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (uv : Var Γ₁ (.prod (B 32) (B 32))) : Comp pqxdhOps pqGapDhIface Δ paramsTy :=
  let n_id := activeIdCount S b.q_on
  let n_spk := activeSpkCount S b.q_on
  let n_opk := activeOpkCount S b.q_on
  let n_send := activeSendCount S b.q_on
  let n_send_opk := activeSendOpkCount S b.q_on
  let nA := n_id * n_spk
  let nC := n_send * n_spk
  let nB := n_send * n_id
  let nD := n_send_opk * n_opk
  let unreach := keyIndSentinel S b
  if fgActiveTotalIndexCount S b.q_on = 0 then
    let U := .fst (v uv)
    let V := .snd (v uv)
    .ret (paMk U V U (.bool false) (.nat unreach) (.bool true) (.nat unreach) (.nat unreach)
      (.bool false) (.nat unreach) (.nat 0))
  else
    chooseArm2C (Γ₁ := Γ₁) (nA + nC) (nB + nD)
      (fun {_} [_] =>
        chooseArm2C (Γ₁ := Γ₁) nA nC
          (fun {_} [_] =>
            if nA = 0 then
              let U := .fst (v uv)
              let V := .snd (v uv)
              .ret (paMk U V U (.bool true) (.nat 0) (.bool true) (.nat unreach) (.nat 0)
                (.bool false) (.nat unreach) (.nat 0))
            else
              bindV (gPrim (sIndex n_id)) fun pOrd =>
              bindV (gPrim (sIndex n_spk)) fun spkOrd =>
              let U := .fst (v uv)
              let V := .snd (v uv)
              .ret (paMk U V U (.bool true) (v pOrd) (.bool true) (.nat unreach) (v spkOrd)
                (.bool false) (.nat unreach) (.nat 0)))
          (fun {_} [_] =>
            if nC = 0 then
              let U := .fst (v uv)
              let V := .snd (v uv)
              .ret (paMk U V U (.bool false) (.nat unreach) (.bool false) (.nat 0) (.nat 0)
                (.bool false) (.nat unreach) (.nat 1))
            else
              bindV (gPrim (sIndex n_send)) fun ephOrd =>
              bindV (gPrim (sIndex n_spk)) fun spkOrd =>
              let U := .fst (v uv)
              let V := .snd (v uv)
              .ret (paMk U V U (.bool false) (.nat unreach) (.bool false) (v ephOrd) (v spkOrd)
                (.bool false) (.nat unreach) (.nat 1))))
      (fun {_} [_] =>
        chooseArm2C (Γ₁ := Γ₁) nB nD
          (fun {_} [_] =>
            if nB = 0 then
              let U := .fst (v uv)
              let V := .snd (v uv)
              .ret (paMk V U U (.bool true) (.nat 0) (.bool false) (.nat 0) (.nat unreach)
                (.bool false) (.nat unreach) (.nat 2))
            else
              bindV (gPrim (sIndex n_send)) fun ephOrd =>
              bindV (gPrim (sIndex n_id)) fun pOrd =>
              let U := .fst (v uv)
              let V := .snd (v uv)
              .ret (paMk V U U (.bool true) (v pOrd) (.bool false) (v ephOrd) (.nat unreach)
                (.bool false) (.nat unreach) (.nat 2)))
          (fun {_} [_] =>
            if nD = 0 then
              let U := .fst (v uv)
              let V := .snd (v uv)
              .ret (paMk U V U (.bool false) (.nat unreach) (.bool false) (.nat 0) (.nat unreach)
                (.bool true) (.nat 0) (.nat 3))
            else
              bindV (gPrim (sIndex n_send_opk)) fun ephOrd =>
              bindV (gPrim (sIndex n_opk)) fun opkOrd =>
              let U := .fst (v uv)
              let V := .snd (v uv)
              .ret (paMk U V U (.bool false) (.nat unreach) (.bool false) (v ephOrd) (.nat unreach)
                (.bool true) (v opkOrd) (.nat 3))))

@[expose] def gdh1KeyKindBaseInit (S : Setup) (b : QueryBudget) :
    Comp pqxdhOps pqSigAndDdhIface [.prod (B 32) (B 32)] (.prod .unit gdh1KeyActiveStateTy) :=
  letV (.pair (.fst (.var .zero)) (.snd (.var .zero))) fun uv =>
  bindV (liftGdhComp (initParams1KeyKindC S b uv)) fun pa =>
  bindV (liftGdhComp (gPrim sBool)) fun secb =>
  let gSt := Expr.pair (v pa) (emptySimE (v secb))
  .ret (.pair .unit (.pair (.pair gSt (.nat (activeSigBudget S b)))
    (.pair .none (.nat 0))))

@[expose] def sigKindInitPrinLeg (K_on : Nat) :
    Comp pqxdhOps pqSigAndDdhIface [sig1KeyActiveStTy, .nat] S1ARS :=
  let st : Var [sig1KeyActiveStTy, .nat] sig1KeyActiveStTy := .zero
  let u : Var [sig1KeyActiveStTy, .nat] .nat := .succ .zero
  .ite (isSomeE (s1Forgery (saInner (v st)))) (.ret (.pair rNone (v st)))
    (sig1KeyActiveInitPrinB K_on st u)

@[expose] def sigKindGenSpkLeg (K_on : Nat) :
    Comp pqxdhOps pqSigAndDdhIface [sig1KeyActiveStTy, .prod .nat .nat] S1ARS :=
  let st : Var [sig1KeyActiveStTy, .prod .nat .nat] sig1KeyActiveStTy := .zero
  let x : Var [sig1KeyActiveStTy, .prod .nat .nat] (.prod .nat .nat) := .succ .zero
  .ite (isSomeE (s1Forgery (saInner (v st)))) (.ret (.pair rNone (v st)))
    (.ite (optNatMatchesE (saTP (v st)) (.fst (v x)))
      (letV (saInner (v st)) fun s =>
       bindV (sig1KeyTargetGenSpkB K_on s x) fun r =>
       .ret (.pair (.fst (v r)) (.pair (saTP (v st)) (.snd (v r)))))
      (letV (saInner (v st)) fun s =>
       letV (pa2Mk (litB 32 []) (s1Pk (v s)) (litB 32 []) .none (.bool false) .none .none
         (.bool false) .none (.nat 1)) fun pa =>
       letV (s1Fg (v s)) fun sm =>
       letV (smBase (v sm)) fun bSt =>
       bindV (liftGdhToSigDdh (wrapSim2 pa (genSpkGdh2B K_on pa sm bSt x))) fun r =>
       .ret (.pair (.fst (v r)) (.pair (saTP (v st)) (s1Upd (v s) (fg := .snd (.snd (v r))))))))

/-- Wraps a non-session `gdhHandle2` online arm with a forgery short-circuit guard for
    `sigKeyInd1KeyKindAtomicProg`. -/
@[expose] def sigWrapGdh2NoFgLeg {qPayTy : PT}
    (gdhBody : Var [params2Ty, sig1KeyStTy, sig1KeyActiveStTy, qPayTy] params2Ty →
      Var [simTy, params2Ty, sig1KeyStTy, sig1KeyActiveStTy, qPayTy] simTy →
      Var [keyIndStateTy, simTy, params2Ty, sig1KeyStTy, sig1KeyActiveStTy, qPayTy] keyIndStateTy →
      Var [sig1KeyActiveStTy, qPayTy] qPayTy →
      Comp pqxdhOps pqGapDhIface
        [keyIndStateTy, simTy, params2Ty, sig1KeyStTy, sig1KeyActiveStTy, qPayTy]
        (.prod keyIndRespTy gdhState2Ty)) :
    Comp pqxdhOps pqSigAndDdhIface [sig1KeyActiveStTy, qPayTy] S1ARS :=
  let st : Var [sig1KeyActiveStTy, qPayTy] sig1KeyActiveStTy := .zero
  let x : Var [sig1KeyActiveStTy, qPayTy] qPayTy := .succ .zero
  .ite (isSomeE (s1Forgery (saInner (v st)))) (.ret (.pair rNone (v st)))
    (letV (saInner (v st)) fun s =>
     letV (pa2Mk (litB 32 []) (s1Pk (v s)) (litB 32 []) .none (.bool false) .none .none
       (.bool false) .none (.nat 1)) fun pa =>
     letV (s1Fg (v s)) fun sm =>
     letV (smBase (v sm)) fun bSt =>
     bindV (liftGdhToSigDdh (gdhBody pa sm bSt x)) fun r =>
     .ret (.pair (.fst (v r)) (.pair (saTP (v st)) (s1Upd (v s) (fg := .snd (.snd (v r)))))))

@[expose] def gdhKindInitPrinLeg (K_on : Nat) :
    Comp pqxdhOps pqSigAndDdhIface [gdh1KeyActiveStateTy, .nat]
      (.prod keyIndRespTy gdh1KeyActiveStateTy) :=
  initPrin1KeyActiveGdhB K_on
    (Γ₁ := [gdh1KeyActiveStateTy, .nat]) (Γ₂ := [gdh1KeyActiveStateTy, .nat])
    .zero (.succ .zero)

@[expose] def gdhKindGenSpkLeg (K_on : Nat) :
    Comp pqxdhOps pqSigAndDdhIface [gdh1KeyActiveStateTy, .prod .nat .nat]
      (.prod keyIndRespTy gdh1KeyActiveStateTy) :=
  genSpk1KeyActiveGdhB K_on
    (Γ₁ := [gdh1KeyActiveStateTy, .prod .nat .nat])
    (Γ₂ := [gdh1KeyActiveStateTy, .prod .nat .nat])
    .zero (.succ .zero)

@[expose] def gdhKindGenOpkLeg (K_on : Nat) :
    Comp pqxdhOps pqSigAndDdhIface [gdh1KeyActiveStateTy, .prod .nat (.prod .nat .nat)]
      (.prod keyIndRespTy gdh1KeyActiveStateTy) :=
  genOpkActiveGdhB K_on
    (Γ₁ := [gdh1KeyActiveStateTy, .prod .nat (.prod .nat .nat)])
    (Γ₂ := [gdh1KeyActiveStateTy, .prod .nat (.prod .nat .nat)])
    .zero (.succ .zero)

/-- Wraps a non-session `gdhHandle2` online arm over `gdh1KeyActiveStateTy` for
    `fgKeyInd1KeyGapDhKindAtomicProg`. -/
@[expose] def gdhWrapDelegNoFgLeg {qPayTy : PT}
    (gdhBody : Var [params2Ty, paramsTy, gdh1KeyStateTy, gdh1KeyActiveStateTy, qPayTy] params2Ty →
      Var [simTy, params2Ty, paramsTy, gdh1KeyStateTy, gdh1KeyActiveStateTy, qPayTy] simTy →
      Var [keyIndStateTy, simTy, params2Ty, paramsTy, gdh1KeyStateTy,
        gdh1KeyActiveStateTy, qPayTy] keyIndStateTy →
      Var [gdh1KeyActiveStateTy, qPayTy] qPayTy →
      Comp pqxdhOps pqGapDhIface
        [keyIndStateTy, simTy, params2Ty, paramsTy, gdh1KeyStateTy, gdh1KeyActiveStateTy, qPayTy]
        (.prod keyIndRespTy gdhState2Ty)) :
    Comp pqxdhOps pqSigAndDdhIface [gdh1KeyActiveStateTy, qPayTy]
      (.prod keyIndRespTy gdh1KeyActiveStateTy) :=
  let stA : Var [gdh1KeyActiveStateTy, qPayTy] gdh1KeyActiveStateTy := .zero
  let x : Var [gdh1KeyActiveStateTy, qPayTy] qPayTy := .succ .zero
  letV (.fst (v stA)) fun st1 =>
  letV (.fst (.fst (v st1))) fun pa =>
  letV (pa2Mk (paU (v pa)) (paV (v pa)) (paUp (v pa)) .none (.bool false) .none .none
    (paOpkMode (v pa)) .none (.nat 1)) fun pa2 =>
  letV (.snd (.fst (v st1))) fun sm =>
  letV (smBase (v sm)) fun bSt =>
  bindV (liftGdhComp (gdhBody pa2 sm bSt x)) fun res =>
  .ret (.pair (.fst (v res))
    (.pair (.pair (.pair (v pa) (.snd (.snd (v res)))) (.snd (v st1))) (.snd (v stA))))

@[expose] def sigKindInitiateSessLeg (S : Setup) (f : KeyIndKFuels) (hasOpk : Bool) :
    Comp pqxdhOps pqSigAndDdhIface [.prod sig1KeyActiveStTy fgSessCtrTy, initQTy]
      (.prod keyIndRespTy (.prod sig1KeyActiveStTy fgSessCtrTy)) :=
  let stSc : Var [.prod sig1KeyActiveStTy fgSessCtrTy, initQTy]
      (.prod sig1KeyActiveStTy fgSessCtrTy) := .zero
  let x : Var [.prod sig1KeyActiveStTy fgSessCtrTy, initQTy] initQTy := .succ .zero
  letV (.fst (v stSc)) fun st =>
  letV (.snd (v stSc)) fun fgSc =>
  .ite (isSomeE (s1Forgery (saInner (v st)))) (.ret (.pair rNone (v stSc)))
    (letV (.snd (.snd (v x))) fun bu =>
     bindV (extract1KeyActiveC S f.kOn st bu) fun fg =>
     .ite (isSomeE (v fg))
       (.ret (.pair rNone
         (.pair (.pair (saTP (v st)) (s1Upd (saInner (v st)) (forgery := v fg))) (v fgSc))))
       (letV (saInner (v st)) fun s =>
        letV (pa2Mk (litB 32 []) (s1Pk (v s)) (litB 32 []) .none (.bool false) .none .none
          (.bool false) .none (.nat 1)) fun pa =>
        letV (s1Fg (v s)) fun sm =>
        letV (smBase (v sm)) fun bSt =>
        bindV (liftGdhToSigDdh (initiateGdh2ShadowB S f pa sm bSt fgSc hasOpk x)) fun r =>
        .ret (.pair (.fst (v r))
          (.pair (.pair (saTP (v st)) (s1Upd (v s) (fg := .fst (.snd (v r)))))
            (.snd (.snd (v r)))))))

@[expose] def sigKindAcceptOpkSessLeg (S : Setup) (f : KeyIndKFuels) :
    Comp pqxdhOps pqSigAndDdhIface [.prod sig1KeyActiveStTy fgSessCtrTy, accQTy]
      (.prod keyIndRespTy (.prod sig1KeyActiveStTy fgSessCtrTy)) :=
  let stSc : Var [.prod sig1KeyActiveStTy fgSessCtrTy, accQTy]
      (.prod sig1KeyActiveStTy fgSessCtrTy) := .zero
  let x : Var [.prod sig1KeyActiveStTy fgSessCtrTy, accQTy] accQTy := .succ .zero
  letV (.fst (v stSc)) fun st =>
  letV (.snd (v stSc)) fun fgSc =>
  .ite (isSomeE (s1Forgery (saInner (v st)))) (.ret (.pair rNone (v stSc)))
    (letV (saInner (v st)) fun s =>
     letV (pa2Mk (litB 32 []) (s1Pk (v s)) (litB 32 []) .none (.bool false) .none .none
       (.bool false) .none (.nat 1)) fun pa =>
     letV (s1Fg (v s)) fun sm =>
     letV (smBase (v sm)) fun bSt =>
     bindV (liftGdhToSigDdh (acceptOpkGdh2ShadowB S f pa sm bSt fgSc x)) fun r =>
     .ret (.pair (.fst (v r))
       (.pair (.pair (saTP (v st)) (s1Upd (v s) (fg := .fst (.snd (v r)))))
         (.snd (.snd (v r))))))

@[expose] def sigKindAcceptNoOpkSessLeg (S : Setup) (f : KeyIndKFuels) :
    Comp pqxdhOps pqSigAndDdhIface [.prod sig1KeyActiveStTy fgSessCtrTy, accQTy]
      (.prod keyIndRespTy (.prod sig1KeyActiveStTy fgSessCtrTy)) :=
  let stSc : Var [.prod sig1KeyActiveStTy fgSessCtrTy, accQTy]
      (.prod sig1KeyActiveStTy fgSessCtrTy) := .zero
  let x : Var [.prod sig1KeyActiveStTy fgSessCtrTy, accQTy] accQTy := .succ .zero
  letV (.fst (v stSc)) fun st =>
  letV (.snd (v stSc)) fun fgSc =>
  .ite (isSomeE (s1Forgery (saInner (v st)))) (.ret (.pair rNone (v stSc)))
    (letV (saInner (v st)) fun s =>
     letV (s1Fg (v s)) fun sm =>
     letV (smBase (v sm)) fun bSt =>
     bindV (liftGdhToSigDdh (acceptNoOpkGdhShadowB S f sm bSt fgSc x)) fun r =>
     .ret (.pair (.fst (v r))
       (.pair (.pair (saTP (v st)) (s1Upd (v s) (fg := .fst (.snd (v r)))))
         (.snd (.snd (v r))))))

@[expose] def gdhKindInitiateSessLeg (S : Setup) (f : KeyIndKFuels) (hasOpk : Bool) :
    Comp pqxdhOps pqSigAndDdhIface [.prod gdh1KeyActiveStateTy fgSessCtrTy, initQTy]
      (.prod keyIndRespTy (.prod gdh1KeyActiveStateTy fgSessCtrTy)) :=
  let stSc : Var [.prod gdh1KeyActiveStateTy fgSessCtrTy, initQTy]
      (.prod gdh1KeyActiveStateTy fgSessCtrTy) := .zero
  let x : Var [.prod gdh1KeyActiveStateTy fgSessCtrTy, initQTy] initQTy := .succ .zero
  letV (.fst (v stSc)) fun stA =>
  letV (.snd (v stSc)) fun fgSc =>
  letV (.fst (v stA)) fun st1 =>
  letV (.fst (.fst (v st1))) fun pa =>
  letV (.snd (.fst (v st1))) fun sm =>
  letV (smBase (v sm)) fun bSt =>
  letV (.snd (.snd (v stA))) fun sendOpkCnt =>
  bindV (liftGdhComp (initiateGdhActiveShadowInnerB S f pa sm bSt fgSc sendOpkCnt hasOpk x))
    fun res =>
  .ret (.pair (.fst (v res))
    (.pair
      (.pair (.pair (.pair (v pa) (.fst (.fst (.snd (v res))))) (.snd (v st1)))
        (.pair (.fst (.snd (v stA))) (.snd (.snd (v res)))))
      (.snd (.fst (.snd (v res))))))

@[expose] def gdhKindAcceptOpkSessLeg (S : Setup) (f : KeyIndKFuels) :
    Comp pqxdhOps pqSigAndDdhIface [.prod gdh1KeyActiveStateTy fgSessCtrTy, accQTy]
      (.prod keyIndRespTy (.prod gdh1KeyActiveStateTy fgSessCtrTy)) :=
  let stSc : Var [.prod gdh1KeyActiveStateTy fgSessCtrTy, accQTy]
      (.prod gdh1KeyActiveStateTy fgSessCtrTy) := .zero
  let x : Var [.prod gdh1KeyActiveStateTy fgSessCtrTy, accQTy] accQTy := .succ .zero
  letV (.fst (v stSc)) fun stA =>
  letV (.snd (v stSc)) fun fgSc =>
  letV (.fst (v stA)) fun st1 =>
  letV (.fst (.fst (v st1))) fun pa =>
  letV (pa2Mk (paU (v pa)) (paV (v pa)) (paUp (v pa)) .none (.bool false) .none .none
    (paOpkMode (v pa)) .none (.nat 1)) fun pa2 =>
  letV (.snd (.fst (v st1))) fun sm =>
  letV (smBase (v sm)) fun bSt =>
  bindV (liftGdhComp (acceptOpkGdh2ShadowB S f pa2 sm bSt fgSc x)) fun res =>
  .ret (.pair (.fst (v res))
    (.pair
      (.pair (.pair (.pair (v pa) (.fst (.snd (v res)))) (.snd (v st1))) (.snd (v stA)))
      (.snd (.snd (v res)))))

@[expose] def gdhKindAcceptNoOpkSessLeg (S : Setup) (f : KeyIndKFuels) :
    Comp pqxdhOps pqSigAndDdhIface [.prod gdh1KeyActiveStateTy fgSessCtrTy, accQTy]
      (.prod keyIndRespTy (.prod gdh1KeyActiveStateTy fgSessCtrTy)) :=
  let stSc : Var [.prod gdh1KeyActiveStateTy fgSessCtrTy, accQTy]
      (.prod gdh1KeyActiveStateTy fgSessCtrTy) := .zero
  let x : Var [.prod gdh1KeyActiveStateTy fgSessCtrTy, accQTy] accQTy := .succ .zero
  letV (.fst (v stSc)) fun stA =>
  letV (.snd (v stSc)) fun fgSc =>
  letV (.fst (v stA)) fun st1 =>
  letV (.fst (.fst (v st1))) fun pa =>
  letV (.snd (.fst (v st1))) fun sm =>
  letV (smBase (v sm)) fun bSt =>
  bindV (liftGdhComp (acceptNoOpkGdhShadowB S f sm bSt fgSc x)) fun res =>
  .ret (.pair (.fst (v res))
    (.pair
      (.pair (.pair (.pair (v pa) (.fst (.snd (v res)))) (.snd (v st1))) (.snd (v stA)))
      (.snd (.snd (v res)))))

end LegacySubBlocks

section AtomicProgs

open _root_.ReductionDsl (Ty Expr Comp CostedReduction TwoStageCostedReduction pqAtomicSig)
open _root_.SignalPqxdh (Setup QueryBudget keyIndSpec)
open _root_.SignalPqxdh.LegacyCosted (pqxdhOps)
open _root_.SignalPqxdh.Costed (pqAtomicOps pqKeyIndCodec pqSigAndDdhIface pqPrimIface PB)
open _root_.SignalPqxdh.Security (KeyIndCostedReductionFamily)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (PT keyIndRespTy pauseTy simTy isSomeE
  s1Forgery s1Fg s1Upd wrapBase2 wrapSim2 genOpkGdh2B corruptB testB revealB registerGdhB
  revealSpkB)
open Computational.Proofs.SignalPqxdh.AtomicLift (embedTy mapComp mapExpr exprRename
  finSidToNatExpr tlSigDdhKeyInd tlPrimKeyInd)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (sig1KeyActiveStTy saTP saInner
  gdh1KeyActiveStateTy)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK (keyIndCoreFuels
  emptyRoAvlE shcrKindStTy atomicRNoneE finPairToNatE finTripleToNatE initPayToNatE accPayToNatE
  dispatchKeyIndQ ren1 runAt2 shcrKindHandlePreC shcrKindChDoneC shcrKindResumeC
  shcrKindHandlePostC shcrKindFinishC)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK (KeyIndKFuels
  keyIndKFuelsOfBudget seqFgEntryTy fgSessCtrTy fgShadowAtomicTy emptyFgShadowE simShadowAtomicTy
  gdhFinishK gdhLift1Key liftGdhAtomic roParsedShadowAtomicC)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (aop)

@[reducible, expose] def sig1KeyActiveKindStTy : Ty pqAtomicSig :=
  .prod (embedTy sig1KeyActiveStTy) fgShadowAtomicTy

@[reducible, expose] def gdh1KeyActiveKindStateTy : Ty pqAtomicSig :=
  .prod (embedTy gdh1KeyActiveStateTy) fgShadowAtomicTy

@[expose] def sigHasForgeryAtomicE {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ (embedTy sig1KeyActiveStTy)) : Expr pqAtomicOps Γ .bool :=
  .letE stE (exprRename ren1
    (mapExpr (isSomeE (s1Forgery (saInner (Γ := [sig1KeyActiveStTy]) (.var .zero))))))

@[expose] def sigGetFgAtomicE {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ (embedTy sig1KeyActiveStTy)) : Expr pqAtomicOps Γ (embedTy simTy) :=
  .letE stE (exprRename ren1
    (mapExpr (s1Fg (saInner (Γ := [sig1KeyActiveStTy]) (.var .zero)))))

@[expose] def sigSetFgAtomicE {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ (embedTy sig1KeyActiveStTy))
    (smE : Expr pqAtomicOps Γ (embedTy simTy)) :
    Expr pqAtomicOps Γ (embedTy sig1KeyActiveStTy) :=
  .letE (.pair stE smE) (exprRename ren1
    (mapExpr (Γ := [.prod sig1KeyActiveStTy simTy])
      (.pair (saTP (.fst (.var .zero)))
        (s1Upd (saInner (.fst (.var .zero))) (fg := .snd (.var .zero))))))

/-- Lifts a `pqSigAndDdhIface` online arm to `pqAtomicOps` while leaving `fgShadowAtomicTy`
    unchanged. -/
@[expose] def liftSigDdhNoFgArm (S : Setup) {stTy qPayTy : PT} {PayAtomic : Ty pqAtomicSig}
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy stTy) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (embedTy qPayTy))
    (arm : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface
      [stTy, qPayTy] (.prod keyIndRespTy stTy)) :
    Comp pqAtomicOps pqSigAndDdhIface
      (PayAtomic :: [.prod (embedTy stTy) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (.prod ((pqKeyIndCodec S).R) (.prod (embedTy stTy) fgShadowAtomicTy)) :=
  .bind (runAt2 (.fst .v1) payE (mapComp tlSigDdhKeyInd arm))
    (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd .v2))))

/-- Lifts a `pqSigAndDdhIface` session arm updating `fgSessCtrTy` to `pqAtomicOps` while leaving
    `(fgRoAvl, rawAvl)` unchanged. -/
@[expose] def liftSigDdhSessArm (S : Setup) {stTy qPayTy : PT} {PayAtomic : Ty pqAtomicSig}
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy stTy) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (embedTy qPayTy))
    (arm : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface
      [.prod stTy fgSessCtrTy, qPayTy]
      (.prod keyIndRespTy (.prod stTy fgSessCtrTy))) :
    Comp pqAtomicOps pqSigAndDdhIface
      (PayAtomic :: [.prod (embedTy stTy) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (.prod ((pqKeyIndCodec S).R) (.prod (embedTy stTy) fgShadowAtomicTy)) :=
  let fgScE : Expr pqAtomicOps _ (embedTy fgSessCtrTy) :=
    .pair (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))
  .bind (runAt2 (.pair (.fst .v1) fgScE) payE (mapComp tlSigDdhKeyInd arm))
    (.ret (.pair (.fst .v0)
      (.pair (.fst (.snd .v0))
        (.pair (.fst (.snd (.snd .v0)))
          (.pair (.snd (.snd (.snd .v0))) (.snd (.snd (.snd .v2))))))))

@[expose] def sig1KeyKindInitC (S : Setup) (b : QueryBudget) :
    Comp pqAtomicOps pqSigAndDdhIface [PB 32] (.prod .unit sig1KeyActiveKindStTy) :=
  .bind (mapComp tlSigDdhKeyInd (sig1KeyKindBaseInit S b))
    (.ret (.pair (.fst (.var .zero)) (.pair (.snd (.var .zero)) emptyFgShadowE)))

@[expose] def sig1KeyKindFinishC :
    Comp pqAtomicOps pqSigAndDdhIface [sig1KeyActiveKindStTy, .bool] (.prod (PB 1569) (PB 64)) :=
  runAt2 (.fst (.var .zero)) (.var (.succ .zero)) (mapComp tlSigDdhKeyInd sig1KeyKindBaseFinish)

@[expose] def shcr1KeyKindInitC (S : Setup) (b : QueryBudget) :
    Comp pqAtomicOps pqPrimIface [.prod (PB 1568) (PB 3168)] (.prod .unit shcrKindStTy) :=
  .bind (mapComp tlPrimKeyInd (shcr1KeyKindBaseInit S b))
    (.ret (.pair (.fst (.var .zero)) (.pair (.snd (.var .zero)) emptyRoAvlE)))

@[expose] def gdh1KeyKindInitC (S : Setup) (b : QueryBudget) :
    Comp pqAtomicOps pqSigAndDdhIface [.prod (PB 32) (PB 32)]
      (.prod .unit gdh1KeyActiveKindStateTy) :=
  .bind (mapComp tlSigDdhKeyInd (gdh1KeyKindBaseInit S b))
    (.ret (.pair (.fst (.var .zero)) (.pair (.snd (.var .zero)) emptyFgShadowE)))

/-- Shadow-indexed `.roQuery` arm for `sigKeyInd1KeyKindAtomicProg` with atomic forgery
    short-circuiting. -/
@[expose] def sigKindRoArm (S : Setup) (f : KeyIndKFuels) :
    Comp pqAtomicOps pqSigAndDdhIface
      (PB 192 :: [sig1KeyActiveKindStTy, (pqKeyIndCodec S).Q])
      (.prod ((pqKeyIndCodec S).R) sig1KeyActiveKindStTy) :=
  .ite (sigHasForgeryAtomicE (.fst .v1))
    (.ret (.pair atomicRNoneE .v1))
    (.bind (runAt2 (.pair (sigGetFgAtomicE (.fst .v1)) (.snd .v1)) .v0
        (roParsedShadowAtomicC gdhLift1Key f))
      (.ret (.pair (.fst .v0)
        (.pair (sigSetFgAtomicE (.fst .v2) (.fst (.snd .v0))) (.snd (.snd .v0))))))

/-- Shadow-indexed `.roQuery` arm for `fgKeyInd1KeyGapDhKindAtomicProg` delegating `(sm, fgShadow)`
    to `roParsedShadowAtomicC`. -/
@[expose] def gdhKindRoArm (S : Setup) (f : KeyIndKFuels) :
    Comp pqAtomicOps pqSigAndDdhIface
      (PB 192 :: [gdh1KeyActiveKindStateTy, (pqKeyIndCodec S).Q])
      (.prod ((pqKeyIndCodec S).R) gdh1KeyActiveKindStateTy) :=
  let simShE : Expr pqAtomicOps _ simShadowAtomicTy :=
    .pair (.snd (.fst (.fst (.fst .v1)))) (.snd .v1)
  .bind (runAt2 simShE .v0 (roParsedShadowAtomicC gdhLift1Key f))
    (.ret (.pair (.fst .v0)
      (.pair
        (.pair
          (.pair (.pair (.fst (.fst (.fst (.fst .v2)))) (.fst (.snd .v0)))
                 (.snd (.fst (.fst .v2))))
          (.snd (.fst .v2)))
        (.snd (.snd .v0)))))

@[expose] def sig1KeyKindHandleC (S : Setup) (b : QueryBudget) :
    Comp pqAtomicOps pqSigAndDdhIface [sig1KeyActiveKindStTy, (pqKeyIndCodec S).Q]
      (.prod ((pqKeyIndCodec S).R) sig1KeyActiveKindStTy) :=
  let f := keyIndKFuelsOfBudget S b
  dispatchKeyIndQ S .v1
    (liftSigDdhNoFgArm S (aop (.finVal S.N_id) .v0) (sigKindInitPrinLeg f.kOn))
    (liftSigDdhNoFgArm S (aop (.finVal S.N_id) .v0)
      (sigWrapGdh2NoFgLeg fun pa sm bSt u => wrapBase2 pa sm (corruptB f.kOn bSt u)))
    (liftSigDdhNoFgArm S (finPairToNatE S.N_id S.N_recv .v0) (sigKindGenSpkLeg f.kOn))
    (liftSigDdhNoFgArm S (finTripleToNatE S.N_id S.N_recv S.N_opk .v0)
      (sigWrapGdh2NoFgLeg fun pa sm bSt x => wrapSim2 pa (genOpkGdh2B f.kOn pa sm bSt x)))
    (liftSigDdhSessArm S (initPayToNatE S.N_send_opk S .v0)
      (sigKindInitiateSessLeg S f true))
    (liftSigDdhSessArm S (initPayToNatE S.N_send_no_opk S .v0)
      (sigKindInitiateSessLeg S f false))
    (liftSigDdhSessArm S (accPayToNatE S.N_opk S .v0)
      (sigKindAcceptOpkSessLeg S f))
    (liftSigDdhSessArm S (accPayToNatE S.N_no_opk S .v0)
      (sigKindAcceptNoOpkSessLeg S f))
    (liftSigDdhNoFgArm S (finSidToNatExpr S .v0)
      (sigWrapGdh2NoFgLeg fun pa sm bSt sid => wrapBase2 pa sm (testB f.kOn bSt sid)))
    (sigKindRoArm S f)
    (.ret (.pair atomicRNoneE .v1))
    (liftSigDdhNoFgArm S (finSidToNatExpr S .v0)
      (sigWrapGdh2NoFgLeg fun pa sm bSt sid => wrapBase2 pa sm (revealB f.kOn bSt sid)))
    (liftSigDdhNoFgArm S .v0
      (sigWrapGdh2NoFgLeg fun pa sm bSt sk => wrapSim2 pa (registerGdhB sm bSt sk)))
    (liftSigDdhNoFgArm S (finPairToNatE S.N_id S.N_recv .v0)
      (sigWrapGdh2NoFgLeg fun pa sm bSt x => wrapBase2 pa sm (revealSpkB f.kOn bSt x)))

@[expose] def shcr1KeyKindHandlePreC (S : Setup) (b : QueryBudget) :
    Comp pqAtomicOps pqPrimIface [shcrKindStTy, (pqKeyIndCodec S).Q]
      (.sum (.prod ((pqKeyIndCodec S).R) shcrKindStTy)
            (.prod (PB 1568) (.prod (embedTy pauseTy) shcrKindStTy))) :=
  let f := keyIndCoreFuels S b
  shcrKindHandlePreC true S f.M_on f.roCap

@[expose] def shcr1KeyKindResumeC (S : Setup) (b : QueryBudget) :
    Comp pqAtomicOps pqPrimIface [shcrKindStTy, embedTy pauseTy, .prod (PB 32) (PB 1568)]
      (.prod ((pqKeyIndCodec S).R) shcrKindStTy) :=
  let f := keyIndCoreFuels S b
  shcrKindResumeC S f.M_on f.roCap

@[expose] def shcr1KeyKindHandlePostC (S : Setup) (b : QueryBudget) :
    Comp pqAtomicOps pqPrimIface [shcrKindStTy, (pqKeyIndCodec S).Q]
      (.prod ((pqKeyIndCodec S).R) shcrKindStTy) :=
  let f := keyIndCoreFuels S b
  shcrKindHandlePostC true S f.M_on f.roCap

@[expose] def gdh1KeyKindHandleC (S : Setup) (b : QueryBudget) :
    Comp pqAtomicOps pqSigAndDdhIface [gdh1KeyActiveKindStateTy, (pqKeyIndCodec S).Q]
      (.prod ((pqKeyIndCodec S).R) gdh1KeyActiveKindStateTy) :=
  let f := keyIndKFuelsOfBudget S b
  dispatchKeyIndQ S .v1
    (liftSigDdhNoFgArm S (aop (.finVal S.N_id) .v0) (gdhKindInitPrinLeg f.kOn))
    (liftSigDdhNoFgArm S (aop (.finVal S.N_id) .v0)
      (gdhWrapDelegNoFgLeg fun pa2 sm bSt u => wrapBase2 pa2 sm (corruptB f.kOn bSt u)))
    (liftSigDdhNoFgArm S (finPairToNatE S.N_id S.N_recv .v0) (gdhKindGenSpkLeg f.kOn))
    (liftSigDdhNoFgArm S (finTripleToNatE S.N_id S.N_recv S.N_opk .v0) (gdhKindGenOpkLeg f.kOn))
    (liftSigDdhSessArm S (initPayToNatE S.N_send_opk S .v0)
      (gdhKindInitiateSessLeg S f true))
    (liftSigDdhSessArm S (initPayToNatE S.N_send_no_opk S .v0)
      (gdhKindInitiateSessLeg S f false))
    (liftSigDdhSessArm S (accPayToNatE S.N_opk S .v0)
      (gdhKindAcceptOpkSessLeg S f))
    (liftSigDdhSessArm S (accPayToNatE S.N_no_opk S .v0)
      (gdhKindAcceptNoOpkSessLeg S f))
    (liftSigDdhNoFgArm S (finSidToNatExpr S .v0)
      (gdhWrapDelegNoFgLeg fun pa2 sm bSt sid => wrapBase2 pa2 sm (testB f.kOn bSt sid)))
    (gdhKindRoArm S f)
    (.ret (.pair atomicRNoneE .v1))
    (liftSigDdhNoFgArm S (finSidToNatExpr S .v0)
      (gdhWrapDelegNoFgLeg fun pa2 sm bSt sid => wrapBase2 pa2 sm (revealB f.kOn bSt sid)))
    (liftSigDdhNoFgArm S .v0
      (gdhWrapDelegNoFgLeg fun pa2 sm bSt sk => wrapSim2 pa2 (registerGdhB sm bSt sk)))
    (liftSigDdhNoFgArm S (finPairToNatE S.N_id S.N_recv .v0)
      (gdhWrapDelegNoFgLeg fun pa2 sm bSt x => wrapBase2 pa2 sm (revealSpkB f.kOn bSt x)))

@[expose] def gdh1KeyKindFinishC (S : Setup) (b : QueryBudget) :
    Comp pqAtomicOps pqSigAndDdhIface [gdh1KeyActiveKindStateTy, .bool] (PB 32) :=
  let f := keyIndKFuelsOfBudget S b
  runAt2 (.fst (.fst (.fst .v0))) .v1 (liftGdhAtomic gdhLift1Key (gdhFinishK S f))

/-- Per-query-kind one-key `GapSigEufCma` reduction over `pqAtomicOps`. -/
@[expose] def sigKeyInd1KeyKindAtomicProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqSigAndDdhIface (keyIndSpec S) (pqKeyIndCodec S)
      (PB 32) .unit .bool (.prod (PB 1569) (PB 64)) where
  σ := sig1KeyActiveKindStTy
  init := sig1KeyKindInitC S b
  handle := sig1KeyKindHandleC S b
  finish := sig1KeyKindFinishC

/-- Per-query-kind one-key two-stage `KemShCr` reduction over `pqAtomicOps`. -/
@[expose] def shcrKeyInd1KeyKindAtomicProg (S : Setup) (b : QueryBudget) :
    TwoStageCostedReduction pqAtomicOps pqPrimIface (keyIndSpec S) (pqKeyIndCodec S)
      (.prod (PB 1568) (PB 3168)) .unit .bool (PB 1568)
      (.prod (PB 32) (PB 1568)) (PB 1568) :=
  let f := keyIndCoreFuels S b
  { σ := shcrKindStTy
    π := embedTy pauseTy
    init := shcr1KeyKindInitC S b
    handlePre := shcr1KeyKindHandlePreC S b
    chDone := shcrKindChDoneC
    resume := shcr1KeyKindResumeC S b
    handlePost := shcr1KeyKindHandlePostC S b
    finish := shcrKindFinishC f.M_on }

/-- Per-query-kind one-key `GapDhWithSign` reduction over `pqAtomicOps`. -/
@[expose] def fgKeyInd1KeyGapDhKindAtomicProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqSigAndDdhIface (keyIndSpec S) (pqKeyIndCodec S)
      (.prod (PB 32) (PB 32)) .unit .bool (PB 32) where
  σ := gdh1KeyActiveKindStateTy
  init := gdh1KeyKindInitC S b
  handle := gdh1KeyKindHandleC S b
  finish := gdh1KeyKindFinishC S b

/-- Per-query-kind creation-order `KeyIndCostedReductionFamily` over `pqAtomicOps`. -/
@[expose] def pqxdhKeyInd1KeyKindCostedSims (S : Setup) : KeyIndCostedReductionFamily S where
  sig  := sigKeyInd1KeyKindAtomicProg S
  shcr := shcrKeyInd1KeyKindAtomicProg S
  gdh  := fgKeyInd1KeyGapDhKindAtomicProg S

end AtomicProgs

section UnsupportedLemmas

open _root_.ReductionDsl (Expr Comp Var Iface)
open _root_.SignalPqxdh (Setup QueryBudget)
open _root_.SignalPqxdh.LegacyCosted (pqSig sigAndDdhOracle pqxdhOps B pqPrimIface pqGapDhIface
  pqSigAndDdhIface)
open Computational.Proofs.SignalPqxdh.AtomicLift (tlSigDdhKeyInd tlPrimKeyInd tlGapDhKeyInd
  keyIndUnsupportedPrimW)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (fgActiveTotalIndexCount
  sig1KeyActiveStTy extract1KeyActiveC sig1KeyActiveInitPrinB gdh1KeyActiveStateTy
  initPrin1KeyActiveGdhB genSpkGdhActiveB genSpk1KeyActiveGdhB genOpkActiveGdhB)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK (shcrChDoneLeg
  shcrExtractLeg)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (liftGdhComp sigChalQ_dsl)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (PT Ext preKeyBundleTy sig1KeyStTy
  sig1KeyTargetGenSpkB bindV letV caseOptV s1Prim gPrim liftBase sIndex sBool sBytes32 sRandom64
  findMV shcrExtractC qKemDecaps qKemKeyGen qSigSign qSigVerify qSigDdhSign qX25519Base qPow8
  honestPeerC findHonestC chooseArm2C bernoulliRatioGdhC)

section
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] sigAndDdhOracle
end

private def zPrimW : pqPrimIface.Tag → ℕ := keyIndUnsupportedPrimW
private def zPrimWS : pqPrimIface.smp.Samp → ℕ := fun _ => 0
private def zGapDhW : pqGapDhIface.Tag → ℕ := tlGapDhKeyInd.unsupportedW
private def zGapDhWS : pqGapDhIface.smp.Samp → ℕ := fun _ => 0
private def zSigDdhW : pqSigAndDdhIface.Tag → ℕ := tlSigDdhKeyInd.unsupportedW
private def zSigDdhWS : pqSigAndDdhIface.smp.Samp → ℕ := fun _ => 0

@[local simp] private theorem letV_queries' {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {a b : PT} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (e : Expr pqxdhOps Γ a) (k : Var (a :: Γ) a → Comp pqxdhOps I (a :: Γ) b) :
    (letV e k).queries w ws = (k .zero).queries w ws := by
  simp [letV, Comp.queries]

@[local simp] private theorem bindV_queries' {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {a b : PT} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (c : Comp pqxdhOps I Γ a) (k : Var (a :: Γ) a → Comp pqxdhOps I (a :: Γ) b) :
    (bindV c k).queries w ws = c.queries w ws + (k .zero).queries w ws :=
  rfl

@[local simp] private theorem caseOptV_queries' {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {a b : PT} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (e : Expr pqxdhOps Γ (.opt a)) (cNone : Comp pqxdhOps I Γ b)
    (cSome : Var (a :: Γ) a → Comp pqxdhOps I (a :: Γ) b) :
    (caseOptV e cNone cSome).queries w ws =
      max (cNone.queries w ws) ((cSome .zero).queries w ws) :=
  rfl

@[local simp] private theorem findMV_queries' {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {a : PT} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (fuel : ℕ)
    (xs : Expr pqxdhOps Γ (.list a))
    (p : Var (a :: Γ) a → Comp pqxdhOps I (a :: Γ) .bool) :
    (findMV fuel xs p).queries w ws = fuel * (p .zero).queries w ws := by
  simp [findMV, Comp.queries]

@[local simp] private theorem sBool_unsup {Γ : List PT} :
    (sBool (Γ := Γ)).queries zPrimW zPrimWS = 0 := rfl
@[local simp] private theorem sBytes32_unsup {Γ : List PT} :
    (sBytes32 (Γ := Γ)).queries zPrimW zPrimWS = 0 := rfl
@[local simp] private theorem sRandom64_unsup {Γ : List PT} :
    (sRandom64 (Γ := Γ)).queries zPrimW zPrimWS = 0 := rfl
@[local simp] private theorem sIndex_unsup (N : ℕ) {Γ : List PT} :
    (sIndex N (Γ := Γ)).queries zPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qX25519Base_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) :
    (qX25519Base e).queries zPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qPow8_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) :
    (qPow8 e).queries zPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qSigSign_unsup (m : ℕ+) {Γ : List PT}
    (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) :
    (qSigSign m e).queries zPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qSigVerify_unsup (m : ℕ+) {Γ : List PT}
    (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) :
    (qSigVerify m e).queries zPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qKemKeyGen_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (B 64)) :
    (qKemKeyGen e).queries zPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qKemDecaps_unsup {Γ : List PT}
    (e : Expr pqxdhOps Γ (.prod (B 3168) (B 1568))) :
    (qKemDecaps e).queries zPrimW zPrimWS = 0 := rfl

@[local simp] private theorem gPrim_unsup {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (gPrim c).queries zGapDhW zGapDhWS = c.queries zPrimW zPrimWS := by
  unfold gPrim
  induction c with
  | query _ _ => rfl
  | sample _ _ => rfl
  | _ => simp_all [liftBase, Comp.queries]

@[local simp] private theorem s1Prim_unsup {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (s1Prim c).queries zSigDdhW zSigDdhWS = c.queries zPrimW zPrimWS := by
  unfold s1Prim
  induction c with
  | query _ _ => rfl
  | sample _ _ => rfl
  | _ => simp_all [liftBase, Comp.queries]

@[local simp] private theorem liftGdhComp_unsup {Γ : List PT} {τ : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ τ) :
    (liftGdhComp c).queries zSigDdhW zSigDdhWS = c.queries zGapDhW zGapDhWS := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhComp, Comp.queries]

@[local simp] private theorem qSigDdhSign_unsup (m : ℕ+) {Γ : List PT}
    (msg : Expr pqxdhOps Γ (B m)) :
    (qSigDdhSign m msg).queries zSigDdhW zSigDdhWS = 0 := rfl

@[local simp] private theorem sigChalQ_dsl_unsup (m : ℕ+) {Γ : List PT}
    (msg : Expr pqxdhOps Γ (B m)) :
    (sigChalQ_dsl m msg).queries zSigDdhW zSigDdhWS = 0 := rfl

@[local simp] private theorem bernoulliRatioGdhC_unsup {Δ : List PT} (A B_w : Nat) :
    (bernoulliRatioGdhC (Δ := Δ) A B_w).queries zGapDhW zGapDhWS = 0 := by
  unfold bernoulliRatioGdhC
  split_ifs <;> simp [Comp.queries]

private theorem chooseArm2C_unsup {Γ₁ Δ : List PT} {α : PT} [Ext Γ₁ Δ] (w1 w2 : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' α)
    (h1 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c1 (Δ' := Δ')).queries zGapDhW zGapDhWS = 0)
    (h2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c2 (Δ' := Δ')).queries zGapDhW zGapDhWS = 0) :
    (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) w1 w2 c1 c2).queries zGapDhW zGapDhWS = 0 := by
  unfold chooseArm2C
  split_ifs <;> simp [Comp.queries, h1, h2]

theorem sig1KeyKindBaseInit_unsupported (S : Setup) (b : QueryBudget) :
    (sig1KeyKindBaseInit S b).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (sig1KeyKindBaseInit S b).queries zSigDdhW zSigDdhWS = 0
  simp [sig1KeyKindBaseInit, Comp.queries]

theorem sig1KeyKindBaseFinish_unsupported :
    sig1KeyKindBaseFinish.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 :=
  rfl

theorem shcr1KeyKindBaseInit_unsupported (S : Setup) (b : QueryBudget) :
    (shcr1KeyKindBaseInit S b).queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcr1KeyKindBaseInit S b).queries zPrimW zPrimWS = 0
  unfold shcr1KeyKindBaseInit; dsimp only; split_ifs <;> simp [Comp.queries]

theorem shcrChDoneLeg_unsupported :
    shcrChDoneLeg.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 :=
  rfl

theorem shcrExtractLeg_unsupported (K_on : Nat) :
    (shcrExtractLeg K_on).queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrExtractLeg K_on).queries zPrimW zPrimWS = 0
  simp [shcrExtractLeg, shcrExtractC, Comp.queries]

theorem initParams1KeyKindC_unsupported (S : Setup) (b : QueryBudget)
    {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))) :
    (initParams1KeyKindC S b (Δ := Δ) uv).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (initParams1KeyKindC S b (Δ := Δ) uv).queries zGapDhW zGapDhWS = 0
  unfold initParams1KeyKindC
  dsimp only
  by_cases htot : fgActiveTotalIndexCount S b.q_on = 0
  · simp [htot, Comp.queries]
  · simp only [htot, ↓reduceIte]
    exact chooseArm2C_unsup _ _ _ _
      (fun {_} [_] => chooseArm2C_unsup _ _ _ _
        (fun {_} [_] => by split_ifs <;> simp [Comp.queries])
        (fun {_} [_] => by split_ifs <;> simp [Comp.queries]))
      (fun {_} [_] => chooseArm2C_unsup _ _ _ _
        (fun {_} [_] => by split_ifs <;> simp [Comp.queries])
        (fun {_} [_] => by split_ifs <;> simp [Comp.queries]))

theorem gdh1KeyKindBaseInit_unsupported (S : Setup) (b : QueryBudget) :
    (gdh1KeyKindBaseInit S b).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (gdh1KeyKindBaseInit S b).queries zSigDdhW zSigDdhWS = 0
  simp only [gdh1KeyKindBaseInit, letV_queries', bindV_queries', liftGdhComp_unsup, gPrim_unsup,
    sBool_unsup, Comp.queries, Nat.add_zero]
  exact initParams1KeyKindC_unsupported S b .zero

theorem extract1KeyActiveC_unsupported (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st : Var Γ₁ sig1KeyActiveStTy) (bu : Var Γ₂ preKeyBundleTy) :
    (extract1KeyActiveC (Δ := Δ) S K st bu).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (extract1KeyActiveC (Δ := Δ) S K st bu).queries zSigDdhW zSigDdhWS = 0
  simp [extract1KeyActiveC, honestPeerC, findHonestC, Comp.queries]

theorem sig1KeyActiveInitPrinB_unsupported (K : Nat)
    {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st : Var Γ₁ sig1KeyActiveStTy) (u : Var Γ₂ .nat) :
    (sig1KeyActiveInitPrinB (Δ := Δ) K st u).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (sig1KeyActiveInitPrinB (Δ := Δ) K st u).queries zSigDdhW zSigDdhWS = 0
  simp [sig1KeyActiveInitPrinB, Comp.queries]

theorem sig1KeyTargetGenSpkB_unsupported (K : Nat)
    {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ sig1KeyStTy) (x : Var Γ₂ (.prod .nat .nat)) :
    (sig1KeyTargetGenSpkB (Δ := Δ) K s x).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (sig1KeyTargetGenSpkB (Δ := Δ) K s x).queries zSigDdhW zSigDdhWS = 0
  simp [sig1KeyTargetGenSpkB, Comp.queries]

theorem initPrin1KeyActiveGdhB_unsupported (K : Nat)
    {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (stA : Var Γ₁ gdh1KeyActiveStateTy) (u : Var Γ₂ .nat) :
    (initPrin1KeyActiveGdhB (Δ := Δ) K stA u).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (initPrin1KeyActiveGdhB (Δ := Δ) K stA u).queries zSigDdhW zSigDdhWS = 0
  simp [initPrin1KeyActiveGdhB, Comp.queries]

theorem genSpk1KeyActiveGdhB_unsupported (K : Nat)
    {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (stA : Var Γ₁ gdh1KeyActiveStateTy) (x : Var Γ₂ (.prod .nat .nat)) :
    (genSpk1KeyActiveGdhB (Δ := Δ) K stA x).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (genSpk1KeyActiveGdhB (Δ := Δ) K stA x).queries zSigDdhW zSigDdhWS = 0
  simp [genSpk1KeyActiveGdhB, genSpkGdhActiveB, Comp.queries]

theorem genOpkActiveGdhB_unsupported (K : Nat)
    {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (stA : Var Γ₁ gdh1KeyActiveStateTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat))) :
    (genOpkActiveGdhB (Δ := Δ) K stA x).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (genOpkActiveGdhB (Δ := Δ) K stA x).queries zSigDdhW zSigDdhWS = 0
  simp [genOpkActiveGdhB, Comp.queries]

end UnsupportedLemmas

end

end Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs
