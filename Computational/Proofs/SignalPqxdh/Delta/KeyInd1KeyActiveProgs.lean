/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKemBounds -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeySigProg -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyShcr -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndShcrLoop -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh -- proof-setup: allow-public-import
public import Computational.Specifications.Pqxdh.Bound

/-!
# Creation-Order Active `ReductionDsl` Programs for One-Key PQXDH `KeyInd`

**Checked by Lean.** Defines the creation-order `ReductionDsl` syntax trees over `pqxdhOps` for
one-key `GapSigEufCma`, `KemShCr`, and `GapDhWithSign`, together with their `AtomicLift`
counterparts over `pqAtomicOps` packaged into `pqxdhKeyInd1KeyActiveCostedSims`.
-/

namespace Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs

public section

set_option autoImplicit false

section ActiveDsl

open _root_.ReductionDsl (Expr Comp Var CostedReduction TwoStageCostedReduction)
open _root_.SignalPqxdh (Setup QueryBudget activeIdCount activeSpkCount activeOpkCount
  activeSendCount activeSendOpkCount keyIndSpec)
open _root_.SignalPqxdh.LegacyCosted (sigAndDdhOracle pqxdhOps B pqSigAndDdhIface pqPrimIface
  pqGapDhIface keyIndCodec bundleT hdrT sidT)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (Ext PT eLet2 eCaseOpt v natEq
  sig1KeyStTy keyIndRespTy keyIndQueryTy keyIndQueryRestTy preKeyBundleTy initQTy initPrin1KeyB
  keyIndLoopBound
  letV bindV caseSumV caseOptV s1Prim s1Fg eqB s1Base s1Pk s1Forgery s1Target s1Mk s1Upd
  honestPeerC buIkB buSpkB buSpkSig buPqspkB buPqspkSig buOpkB buSpkId buPqspkId buMk
  qSigVerify encEC encKEM widenEC eAny eFind stSpks stPrin stOpks stSess stUpd
  sbSpkPk sbPqspkPk sbMk rNone rInitPrin rBundle rPk rInitUnfresh rHdr
  sBytes32 sRandom64 sBool sIndex qX25519Base qSigSign qKemKeyGen qKemEncaps
  litB peMk peSecIKAsign peSecIKA0 peIkAPk isSomeE sig1KeyTargetGenSpkB
  liftGdhToSigDdh renamePair pa2Mk gdhHandle2
  emptySimE emptyStE shcrStTy pauseTy SCS scTB scBase scTPk scTSk scMk scUpd
  onBase genSpkB genOpkB corruptB testB roB revealDhB revealB registerB revealSpkB
  nat2Eq nat3Eq u32OfNat shcrInitiateC shcrAcceptB pauseCheckC shcrResumeC shcrExtractC
  oeMk initSidE sidEq seSid seMk seUpd hdMk optFst optSnd
  paramsTy simTy keyIndStateTy smBase smUpd smPows smFgL gPrim paPrinFlag paPrinIdx paUp
  paSpkIdx paV paU paOpkMode paOpkIdx paDhFlag paEphIdx paMk koskBundleOkPowsC resolveSigPkC
  lookupSpkSkC computePosC computeOptPosInitC fgPatchC checkProvC chooseInitRandC findHonestC
  gdhFinish chooseArm2C)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (gdh1KeyStateTy callGdhHandle
  liftGdhComp sigChalQ_dsl renameComp twoVarRen)

section
set_option allowUnsafeReducibility true
attribute [implicit_reducible] sigAndDdhOracle
end

/-- Clamped signing-oracle budget `min b.q_total (min S.N_spk_tot S.N_recv)` so `.nat` literals stay
    bounded by `b.q_total` while remaining `≤ min S.N_spk_tot S.N_recv`. -/
@[expose] def activeSigBudget (S : Setup) (b : QueryBudget) : Nat :=
  min b.q_total (min S.N_spk_tot S.N_recv)

@[expose] def optNatMatchesE {Γ : List PT} (tpOpt : Expr pqxdhOps Γ (.opt .nat))
    (u : Expr pqxdhOps Γ .nat) : Expr pqxdhOps Γ .bool :=
  eLet2 tpOpt u fun tp uV =>
    eCaseOpt (v tp) (.bool false) fun t => natEq (v uV) (v t)

/-! ## Creation-order `GapSigEufCma` program -/

/-- State `(targetParty?, sig1KeySt)` where `s1Target (.snd st)` holds the creation-order index
    `targetOrd` and `.fst st` holds the resolved principal ID `Option Nat`. -/
abbrev sig1KeyActiveStTy : PT := .prod (.opt .nat) sig1KeyStTy

abbrev S1ARS : PT := .prod keyIndRespTy sig1KeyActiveStTy

@[expose, reducible] def saTP {Γ : List PT} (e : Expr pqxdhOps Γ sig1KeyActiveStTy) :
    Expr pqxdhOps Γ (.opt .nat) := .fst e

@[expose, reducible] def saInner {Γ : List PT} (e : Expr pqxdhOps Γ sig1KeyActiveStTy) :
    Expr pqxdhOps Γ sig1KeyStTy := .snd e

@[expose] def extract1KeyActiveC (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st : Var Γ₁ sig1KeyActiveStTy) (bu : Var Γ₂ preKeyBundleTy) :
    Comp pqxdhOps pqSigAndDdhIface Δ (.opt (.prod (B 1569) (B 64))) :=
  letV (saInner (v st)) fun s =>
  bindV (s1Prim (letV (s1Base (v s)) fun g => honestPeerC S K g (buIkB (v bu)))) fun peer =>
  bindV (s1Prim (qSigVerify 33
      (.pair (s1Pk (v s)) (.pair (encEC (buSpkB (v bu))) (buSpkSig (v bu)))))) fun v1 =>
  bindV (s1Prim (qSigVerify 1569
      (.pair (s1Pk (v s)) (.pair (encKEM (buPqspkB (v bu))) (buPqspkSig (v bu)))))) fun v2 =>
  .ret (eCaseOpt (s1Forgery (v s))
    (eCaseOpt (v peer) .none fun k =>
      .ite (optNatMatchesE (saTP (v st)) (v k))
        (.ite (.and (v v1) (.not (eAny K (stSpks (s1Base (v s))) fun e =>
            .and (natEq (.fst (.fst (v e))) (v k)) (eqB (sbSpkPk (.snd (v e))) (buSpkB (v bu))))))
          (.some (.pair (widenEC (encEC (buSpkB (v bu)))) (buSpkSig (v bu))))
          (.ite (.and (v v2) (.not (eAny K (stSpks (s1Base (v s))) fun e =>
              .and (natEq (.fst (.fst (v e))) (v k))
                (eqB (sbPqspkPk (.snd (v e))) (buPqspkB (v bu))))))
            (.some (.pair (encKEM (buPqspkB (v bu))) (buPqspkSig (v bu))))
            .none))
        .none)
    fun fg => .some (v fg))

@[expose] def sig1KeyActiveInitPrinB (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st : Var Γ₁ sig1KeyActiveStTy) (u : Var Γ₂ .nat) :
    Comp pqxdhOps pqSigAndDdhIface Δ S1ARS :=
  letV (saInner (v st)) fun s =>
  .ite (eAny K (stPrin (s1Base (v s))) fun e => natEq (.fst (v e)) (v u))
    (.ret (.pair rNone (v st))) <|
  bindV (s1Prim sBytes32) fun s0 =>
  bindV (s1Prim (qX25519Base (v s0))) fun ik =>
  let isTgt := natEq (.len (stPrin (s1Base (v s)))) (s1Target (v s))
  let sec := Expr.ite isTgt (litB 32 []) (v s0)
  let pk := Expr.ite isTgt (s1Pk (v s)) (v ik)
  let tp' := Expr.ite isTgt (.some (v u)) (saTP (v st))
  .ret (.pair (rInitPrin pk pk)
    (.pair tp' (s1Upd (v s) (fg := smUpd (s1Fg (v s))
      (base := stUpd (s1Base (v s))
        (prin := .cons (.pair (v u) (peMk sec pk sec pk (.bool false)))
          (stPrin (s1Base (v s)))))))))

@[expose] def sig1KeyActiveInitiateCheckC (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st : Var Γ₁ sig1KeyActiveStTy) (x : Var Γ₂ initQTy) :
    Comp pqxdhOps pqSigAndDdhIface Δ (.sum S1ARS .unit) :=
  letV (.snd (.snd (v x))) fun bu =>
  bindV (extract1KeyActiveC S K st bu) fun fg =>
  .ite (isSomeE (v fg))
    (.ret (.inl (.pair rNone (.pair (saTP (v st)) (s1Upd (saInner (v st)) (forgery := v fg))))))
    (.ret (.inr .unit))

@[expose] def sig1KeyActivePreDispatchC (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st : Var Γ₁ sig1KeyActiveStTy) (q : Var Γ₂ keyIndQueryTy) :
    Comp pqxdhOps pqSigAndDdhIface Δ (.sum S1ARS .unit) :=
  .ite (isSomeE (s1Forgery (saInner (v st)))) (.ret (.inl (.pair rNone (v st)))) <|
  caseSumV (v q) (fun u => bindV (sig1KeyActiveInitPrinB K st u) fun r => .ret (.inl (v r))) fun q =>
  caseSumV (v q) (fun _ => .ret (.inr .unit)) fun q =>
  caseSumV (v q)
    (fun x => .ite (optNatMatchesE (saTP (v st)) (.fst (v x)))
      (letV (saInner (v st)) fun s =>
       bindV (sig1KeyTargetGenSpkB K s x) fun r =>
       .ret (.inl (.pair (.fst (v r)) (.pair (saTP (v st)) (.snd (v r))))))
      (.ret (.inr .unit))) fun q =>
  caseSumV (v q) (fun _ => .ret (.inr .unit)) fun q =>
  caseSumV (v q) (fun x => sig1KeyActiveInitiateCheckC S K st x) fun q =>
  caseSumV (v q) (fun x => sig1KeyActiveInitiateCheckC S K st x) fun _ =>
  .ret (.inr .unit)

@[expose] def sig1KeyActiveHandleC (S : Setup) (K : Nat) :
    Comp pqxdhOps pqSigAndDdhIface [sig1KeyActiveStTy, keyIndQueryTy] S1ARS :=
  let st : Var [sig1KeyActiveStTy, keyIndQueryTy] sig1KeyActiveStTy := .zero
  let q : Var [sig1KeyActiveStTy, keyIndQueryTy] keyIndQueryTy := .succ .zero
  bindV (sig1KeyActivePreDispatchC S K st q) fun pre =>
  caseSumV (v pre) (fun res => .ret (v res)) fun _ =>
  letV (saInner (v st)) fun s =>
  letV (.pair (pa2Mk (litB 32 []) (s1Pk (v s)) (litB 32 []) .none (.bool false) .none .none
      (.bool false) .none (.nat 1)) (s1Fg (v s))) fun gdhSt2 =>
  bindV (liftGdhToSigDdh ((gdhHandle2 S K).rename (renamePair gdhSt2 (Ext.wk q)))) fun r =>
  .ret (.pair (.fst (v r)) (.pair (saTP (v st)) (s1Upd (v s) (fg := .snd (.snd (v r))))))

/-- Creation-order `CostedReduction` program for one-key `GapSigEufCma` over
    `activeIdCount S b.q_on`. -/
@[expose] def sigKeyInd1KeyActiveDslProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqxdhOps pqSigAndDdhIface (keyIndSpec S) (keyIndCodec S)
      (B 32) .unit .bool (.prod (B 1569) (B 64)) :=
  let n_id := activeIdCount S b.q_on
  let K := b.q_total
  { σ := sig1KeyActiveStTy
    init :=
      bindV (s1Prim (sIndex n_id)) fun k =>
      bindV (s1Prim sBool) fun secb =>
      let ordE : Expr pqxdhOps _ .nat := if n_id = 0 then .nat (K + 1) else v k
      .ret (.pair .unit (.pair .none
        (s1Mk (emptySimE (v secb)) ordE (.var (.succ (.succ .zero)))
          (.nat (activeSigBudget S b)) .none)))
    handle := sig1KeyActiveHandleC S K
    finish :=
      .ret (eCaseOpt (s1Forgery (saInner (.var .zero)))
        (.pair (litB 1569 []) (litB 64 [])) fun fg => v fg) }

/-! ## Creation-order `KemShCr` program -/

@[expose] def shcrActiveGenSpkB (_S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ (.prod .nat .nat)) :
    Comp pqxdhOps pqPrimIface Δ SCS :=
  caseOptV (scTB (v s)) (onBase s fun g => genSpkB K g x) fun spkOrd =>
  .ite (eAny K (stSpks (scBase (v s))) fun e => nat2Eq (.fst (v e)) (v x))
    (.ret (.pair rNone (v s))) <|
  caseOptV (eFind K (stPrin (scBase (v s))) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (.pair rNone (v s))) fun uE =>
  .ite (.not (natEq (.len (stSpks (scBase (v s)))) (.fst (v spkOrd))))
    (onBase s fun g => genSpkB K g x) <|
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

@[expose] def shcrActivePostTailC (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (s : Var Γ₁ shcrStTy) [Ext Γ₁ Δ]
    (q : Var (keyIndQueryRestTy :: Δ) keyIndQueryRestTy) :
    Comp pqxdhOps pqPrimIface (keyIndQueryRestTy :: Δ) SCS :=
  caseSumV (v q) (fun u => onBase s fun g => corruptB K g u) fun q =>
  caseSumV (v q) (fun x => shcrActiveGenSpkB S K s x) fun q =>
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

@[expose] def shcr1KeyActivePostC (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ SCS :=
  caseSumV (v q) (fun u => onBase s fun g => initPrin1KeyB K g u)
    (shcrActivePostTailC S K s)

@[expose] def shcr1KeyActivePreC (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ (.sum SCS (.prod (B 1568) (.prod pauseTy shcrStTy))) :=
  bindV (pauseCheckC S K s q) fun p =>
  caseOptV (v p) (bindV (shcr1KeyActivePostC S K s q) fun r => .ret (.inl (v r))) fun d =>
  .ret (.inr (.pair (buPqspkB (.fst (.snd (v d)))) (.pair (v d) (v s))))

/-- Creation-order two-stage `ReductionDsl` program for one-key `KemShCr` over
    `activeSpkCount S b.q_on * activeSendCount S b.q_on`. -/
@[expose] def shcrKeyInd1KeyActiveDslProg (S : Setup) (b : QueryBudget) :
    TwoStageCostedReduction pqxdhOps pqPrimIface (keyIndSpec S) (keyIndCodec S)
      (.prod (B 1568) (B 3168)) .unit .bool (B 1568) (.prod (B 32) (B 1568)) (B 1568) :=
  let n_spk := activeSpkCount S b.q_on
  let n_send := activeSendCount S b.q_on
  let n_prod := n_spk * n_send
  let Q := b.q_total
  let K := keyIndLoopBound b
  { σ := shcrStTy
    π := pauseTy
    init :=
      if n_prod = 0 then
        bindV sBool fun secb =>
        .ret (.pair .unit (scMk (emptyStE (v secb)) .none
          (.fst (.var (.succ .zero))) (.snd (.var (.succ .zero))) (.nat 0) .nil .nil
          (.nat (Q + 1)) (.fst (.var (.succ .zero)))))
      else
        bindV (sIndex n_spk) fun spkOrd =>
        bindV (sIndex n_send) fun sIdx =>
        bindV sBool fun secb =>
        .ret (.pair .unit (scMk (emptyStE (v secb)) (.some (.pair (v spkOrd) (.nat 0)))
          (.fst (.var (.succ (.succ (.succ .zero))))) (.snd (.var (.succ (.succ (.succ .zero)))))
          (.nat 0) .nil .nil (v sIdx) (.fst (.var (.succ (.succ (.succ .zero)))))))
    handlePre := shcr1KeyActivePreC S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
      (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
    chDone := .ret (scTPk (.var .zero))
    resume := shcrResumeC S K (Γ₁ := [.prod (B 32) (B 1568)])
      (Γ₂ := [pauseTy, .prod (B 32) (B 1568)])
      (Γ₃ := [shcrStTy, pauseTy, .prod (B 32) (B 1568)])
      (Δ := [shcrStTy, pauseTy, .prod (B 32) (B 1568)]) .zero .zero .zero
    handlePost := shcr1KeyActivePostC S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
      (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
    finish := shcrExtractC (Γ₁ := [.prod (B 32) (B 1568)])
      (Γ₃ := [shcrStTy, .bool, .prod (B 32) (B 1568)])
      (Δ := [shcrStTy, .bool, .prod (B 32) (B 1568)]) Q .zero .zero }

/-! ## Creation-order `GapDhWithSign` program -/

/-- Total active DH pair count across the four PQXDH DH legs:
    `n_id * n_spk + n_send * n_spk + n_send * n_id + n_send_opk * n_opk`. -/
@[expose] def fgActiveTotalIndexCount (S : Setup) (q_on : Nat) : Nat :=
  let n_id := activeIdCount S q_on
  let n_spk := activeSpkCount S q_on
  let n_opk := activeOpkCount S q_on
  let n_send := activeSendCount S q_on
  let n_send_opk := activeSendOpkCount S q_on
  n_id * n_spk + n_send * n_spk + n_send * n_id + n_send_opk * n_opk

/-- Full DSL state type `(((params, simState), sigBudget), (resolvedPrin?, sendOpkCnt))` for
    `fgKeyInd1KeyGapDhActiveDslProg`. -/
abbrev gdh1KeyActiveStateTy : PT := .prod gdh1KeyStateTy (.prod (.opt .nat) .nat)

@[expose] def callGdhActiveHandle (S : Setup) (K : Nat) {Δ : List PT}
    (stA : Var Δ gdh1KeyActiveStateTy) (q : Var Δ keyIndQueryTy) :
    Comp pqxdhOps pqSigAndDdhIface Δ (.prod keyIndRespTy gdh1KeyActiveStateTy) :=
  letV (.fst (v stA)) fun st1 =>
  letV (.fst (.fst (v st1))) fun pa =>
  letV (.pair (pa2Mk (paU (v pa)) (paV (v pa)) (paUp (v pa)) .none (.bool false) .none .none
      (paOpkMode (v pa)) .none (.nat 1)) (.snd (.fst (v st1)))) fun gst2 =>
  bindV (renameComp (twoVarRen gst2 (.succ (.succ (.succ q)))) (liftGdhComp (gdhHandle2 S K))) fun res =>
  .ret (.pair (.fst (v res))
    (.pair (.pair (.pair (v pa) (.snd (.snd (v res)))) (.snd (v st1))) (.snd (v stA))))

@[expose] def initPrin1KeyActiveGdhB (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (stA : Var Γ₁ gdh1KeyActiveStateTy) (u : Var Γ₂ .nat) :
    Comp pqxdhOps pqSigAndDdhIface Δ (.prod keyIndRespTy gdh1KeyActiveStateTy) :=
  letV (.fst (v stA)) fun st1 =>
  letV (.fst (.fst (v st1))) fun pa =>
  letV (.snd (.fst (v st1))) fun sm =>
  letV (smBase (v sm)) fun bSt =>
  .ite (eAny K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (v u))
    (.ret (.pair rNone (v stA)))
    (letV (.and (paPrinFlag (v pa)) (natEq (.len (stPrin (v bSt))) (paPrinIdx (v pa)))) fun isT =>
     bindV (liftGdhComp (gPrim sBytes32)) fun sk0 =>
     bindV (liftGdhComp (gPrim (qX25519Base (v sk0)))) fun pk0 =>
     letV (.ite (v isT) (litB 32 []) (v sk0)) fun sec0 =>
     letV (.ite (v isT) (paUp (v pa)) (v pk0)) fun ikPk =>
     let e := peMk (v sec0) (v ikPk) (v sec0) (v ikPk) (.bool false)
     let bSt' := stUpd (v bSt) (prin := .cons (.pair (v u) e) (stPrin (v bSt)))
     let sm' := smUpd (v sm) (base := bSt')
     let tp' := Expr.ite (v isT) (.some (v u)) (.fst (.snd (v stA)))
     .ret (.pair (rInitPrin (v ikPk) (v ikPk))
       (.pair (.pair (.pair (v pa) sm') (.snd (v st1)))
         (.pair tp' (.snd (.snd (v stA)))))))

@[expose] def genSpkGdhActiveB (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ (.prod .nat .nat)) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy) :=
  .ite (eAny K (stSpks (v bSt)) fun p => nat2Eq (.fst (v p)) (v x))
    (.ret (.pair rNone (v sm)))
    (caseOptV (eFind K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (.fst (v x)))
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

@[expose] def genSpk1KeyActiveGdhB (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (stA : Var Γ₁ gdh1KeyActiveStateTy) (x : Var Γ₂ (.prod .nat .nat)) :
    Comp pqxdhOps pqSigAndDdhIface Δ (.prod keyIndRespTy gdh1KeyActiveStateTy) :=
  letV (.fst (v stA)) fun st1 =>
  letV (.fst (.fst (v st1))) fun pa =>
  letV (.snd (.fst (v st1))) fun sm =>
  letV (smBase (v sm)) fun bSt =>
  letV (.snd (v st1)) fun sigB =>
  .ite (optNatMatchesE (.fst (.snd (v stA))) (.fst (v x)))
    (.ite (eAny K (stSpks (v bSt)) fun p => nat2Eq (.fst (v p)) (v x))
      (.ret (.pair rNone (v stA)))
      (caseOptV (eFind K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (.fst (v x)))
        (.ret (.pair rNone (v stA)))
        fun ue =>
          .ite (natEq (v sigB) (.nat 0))
            (.ret (.pair rNone (v stA)))
            (letV (natEq (.len (stSpks (v bSt))) (paSpkIdx (v pa))) fun isT =>
             bindV (liftGdhComp (gPrim sBytes32)) fun spkSkRaw =>
             bindV (liftGdhComp (gPrim (qX25519Base (v spkSkRaw)))) fun spkPkRaw =>
             letV (.ite (v isT) (litB 32 []) (v spkSkRaw)) fun spkSk =>
             letV (.ite (v isT) (paV (v pa)) (v spkPkRaw)) fun spkPk =>
             bindV (sigChalQ_dsl 33 (encEC (v spkPk))) fun spkSig =>
             bindV (liftGdhComp (gPrim sRandom64)) fun seed =>
             bindV (liftGdhComp (gPrim (qKemKeyGen (v seed)))) fun kp =>
             bindV (sigChalQ_dsl 1569 (encKEM (.fst (v kp)))) fun pqSig =>
             let jId := u32OfNat (.snd (v x))
             let bE := sbMk (v spkSk) (v spkPk) (v spkSig)
               (.snd (v kp)) (.fst (v kp)) (v pqSig) (.bool false)
             let buOut := buMk (peIkAPk (.snd (v ue))) jId (v spkPk) (v spkSig)
               .none jId (.fst (v kp)) (v pqSig)
             let bSt' := stUpd (v bSt) (spks := .cons (.pair (v x) bE) (stSpks (v bSt)))
             let sm' := smUpd (v sm) (base := bSt')
             .ret (.pair (rBundle buOut)
               (.pair (.pair (.pair (v pa) sm') (.sub (v sigB) (.nat 1)))
                 (.snd (v stA)))))))
    (bindV (liftGdhComp (genSpkGdhActiveB K pa sm bSt x)) fun res =>
     .ret (.pair (.fst (v res))
       (.pair (.pair (.pair (v pa) (.snd (v res))) (v sigB)) (.snd (v stA)))))

@[expose] def genOpkActiveGdhB (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (stA : Var Γ₁ gdh1KeyActiveStateTy)
    (x : Var Γ₂ (.prod .nat (.prod .nat .nat))) :
    Comp pqxdhOps pqSigAndDdhIface Δ (.prod keyIndRespTy gdh1KeyActiveStateTy) :=
  letV (.fst (v stA)) fun st1 =>
  letV (.fst (.fst (v st1))) fun pa =>
  letV (.snd (.fst (v st1))) fun sm =>
  letV (smBase (v sm)) fun bSt =>
  .ite (eAny K (stOpks (v bSt)) fun p => nat3Eq (.fst (v p)) (v x))
    (.ret (.pair rNone (v stA)))
    (letV (.and (paOpkMode (v pa))
      (natEq (.len (stOpks (v bSt))) (paOpkIdx (v pa)))) fun isT =>
     bindV (liftGdhComp (gPrim sBytes32)) fun opkSkRaw =>
     bindV (liftGdhComp (gPrim (qX25519Base (v opkSkRaw)))) fun opkPkRaw =>
     letV (.ite (v isT) (litB 32 []) (v opkSkRaw)) fun opkSk =>
     letV (.ite (v isT) (paV (v pa)) (v opkPkRaw)) fun opkPk =>
     let oE := oeMk (v opkSk) (v opkPk) (.bool false)
     let bSt' := stUpd (v bSt) (opks := .cons (.pair (v x) oE) (stOpks (v bSt)))
     let sm' := smUpd (v sm) (base := bSt')
     .ret (.pair (rPk (v opkPk))
       (.pair (.pair (.pair (v pa) sm') (.snd (v st1))) (.snd (v stA)))))

@[expose] def initiateGdhActiveInnerB (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (sendOpkCnt : Var Γ₅ .nat) (hasOpk : Bool) (x : Var Γ₄ initQTy) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy (.prod simTy .nat)) :=
  letV (.snd (.snd (v x))) fun bu =>
  let guardOk := if hasOpk then isSomeE (buOpkB (v bu)) else .not (isSomeE (buOpkB (v bu)))
  .ite (.not guardOk) (.ret (.pair rNone (.pair (v sm) (v sendOpkCnt))))
    (letV (initSidE hasOpk (v x)) fun sid =>
     .ite (eAny K (stSess (v bSt)) fun s => sidEq (seSid (v s)) (v sid))
       (.ret (.pair rNone (.pair (v sm) (v sendOpkCnt))))
       (caseOptV (eFind K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (.fst (v x)))
         (.ret (.pair rNone (.pair (v sm) (v sendOpkCnt))))
         fun ue =>
           bindV (gPrim (koskBundleOkPowsC S K bSt (smPows (v sm)) bu)) fun ok =>
           .ite (.not (v ok)) (.ret (.pair rNone (.pair (v sm) (v sendOpkCnt))))
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
              .ite (.not (.and (v v1) (v v2))) (.ret (.pair rNone (.pair (v sm) (v sendOpkCnt))))
                (bindV (gPrim (qKemEncaps (.pair (buPqspkB (v bu)) (v coins)))) fun krOpt =>
                 caseOptV (v krOpt) (.ret (.pair rNone (.pair (v sm) (v sendOpkCnt)))) fun kr =>
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
                   bindV (fgPatchC K p1 p2 p3 p4 ss (smFgL (v sm))) fun patchR =>
                   letV (.fst (v patchR)) fun dkReal =>
                   letV (.snd (v patchR)) fun fgL' =>
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
                     (.pair (rInitUnfresh (v dkReal) (v hdr)) (.pair (v smV) (v cntV)))
                     fun _ => .pair (rHdr (v hdr)) (.pair (v smV) (v cntV)))))))

@[expose] def initiateActiveGdhB (S : Setup) (K : Nat) (hasOpk : Bool)
    {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (stA : Var Γ₁ gdh1KeyActiveStateTy) (x : Var Γ₂ initQTy) :
    Comp pqxdhOps pqSigAndDdhIface Δ (.prod keyIndRespTy gdh1KeyActiveStateTy) :=
  letV (.fst (v stA)) fun st1 =>
  letV (.fst (.fst (v st1))) fun pa =>
  letV (.snd (.fst (v st1))) fun sm =>
  letV (smBase (v sm)) fun bSt =>
  letV (.snd (.snd (v stA))) fun sendOpkCnt =>
  bindV (liftGdhComp (initiateGdhActiveInnerB S K pa sm bSt sendOpkCnt hasOpk x)) fun res =>
  .ret (.pair (.fst (v res))
    (.pair (.pair (.pair (v pa) (.fst (.snd (v res)))) (.snd (v st1)))
      (.pair (.fst (.snd (v stA))) (.snd (.snd (v res))))))

@[expose] def gdh1KeyActiveHandle (S : Setup) (K : Nat) :
    Comp pqxdhOps pqSigAndDdhIface [gdh1KeyActiveStateTy, keyIndQueryTy]
      (.prod keyIndRespTy gdh1KeyActiveStateTy) :=
  let stA : Var [gdh1KeyActiveStateTy, keyIndQueryTy] gdh1KeyActiveStateTy := .zero
  let q : Var [gdh1KeyActiveStateTy, keyIndQueryTy] keyIndQueryTy := .succ .zero
  caseSumV (v q) (fun u => initPrin1KeyActiveGdhB K stA u) fun r1 =>
  caseSumV (v r1) (fun _ => callGdhActiveHandle S K (.succ (.succ stA)) (.succ (.succ q))) fun r2 =>
  caseSumV (v r2) (fun x => genSpk1KeyActiveGdhB K stA x) fun r3 =>
  caseSumV (v r3) (fun x => genOpkActiveGdhB K stA x) fun r4 =>
  caseSumV (v r4) (fun x => initiateActiveGdhB S K true stA x) fun r5 =>
  caseSumV (v r5) (fun x => initiateActiveGdhB S K false stA x) fun _ =>
  callGdhActiveHandle S K
    (.succ (.succ (.succ (.succ (.succ (.succ stA))))))
    (.succ (.succ (.succ (.succ (.succ (.succ q))))))

@[expose] def gdh1KeyActiveFinish (S : Setup) (K : Nat) :
    Comp pqxdhOps pqSigAndDdhIface [gdh1KeyActiveStateTy, .bool] (B 32) :=
  let stA : Var [gdh1KeyActiveStateTy, .bool] gdh1KeyActiveStateTy := .zero
  letV (.fst (.fst (v stA))) fun gst =>
  renameComp (twoVarRen gst (.succ (.succ .zero))) (liftGdhComp (gdhFinish S K))

/-- Active parameter tuple decoded from flat index `idx ∈ [0, fgActiveTotalIndexCount S b.q_on)`. -/
@[expose] def initParams1KeyActiveFlat (S : Setup) (b : QueryBudget) {Γ : List PT}
    (U V : Expr pqxdhOps Γ (B 32)) (idx : Expr pqxdhOps Γ .nat) : Expr pqxdhOps Γ paramsTy :=
  let n_id := activeIdCount S b.q_on
  let n_spk := activeSpkCount S b.q_on
  let n_opk := activeOpkCount S b.q_on
  let n_send := activeSendCount S b.q_on
  let nA := n_id * n_spk
  let nC := n_send * n_spk
  let nB := n_send * n_id
  let tot := fgActiveTotalIndexCount S b.q_on
  let unreach := b.q_total + 1
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

/-- Four-leg creation-order parameter sampler for `fgKeyInd1KeyGapDhActiveDslProg` matching
    `initParams1KeyActiveFlat` over `sampleIndexRange (fgActiveTotalIndexCount S b.q_on)`. -/
@[expose] def initParams1KeyActiveC (S : Setup) (b : QueryBudget) {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
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
  let unreach := b.q_total + 1
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

/-- Creation-order `CostedReduction` program for one-key `GapDhWithSign`. -/
@[expose] def fgKeyInd1KeyGapDhActiveDslProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqxdhOps pqSigAndDdhIface (keyIndSpec S) (keyIndCodec S)
      (.prod (B 32) (B 32)) .unit .bool (B 32) where
  σ := gdh1KeyActiveStateTy
  init :=
    letV (.pair (.fst (.var .zero)) (.snd (.var .zero))) fun uv =>
    bindV (liftGdhComp (initParams1KeyActiveC S b uv)) fun pa =>
    bindV (liftGdhComp (gPrim sBool)) fun secb =>
    let gSt := Expr.pair (v pa) (emptySimE (v secb))
    .ret (.pair .unit (.pair (.pair gSt (.nat (activeSigBudget S b)))
      (.pair .none (.nat 0))))
  handle := gdh1KeyActiveHandle S b.q_total
  finish := gdh1KeyActiveFinish S b.q_total

end ActiveDsl

/-! ## Atomic-signature lifts and costed family -/

open _root_.ReductionDsl (CostedReduction TwoStageCostedReduction)
open _root_.SignalPqxdh (Setup QueryBudget keyIndSpec)
open _root_.SignalPqxdh.Costed (pqAtomicOps pqKeyIndCodec pqSigAndDdhIface pqPrimIface PB)
open _root_.SignalPqxdh.Security (KeyIndCostedReductionFamily)
open Computational.Proofs.SignalPqxdh.AtomicLift (tlSigDdhKeyInd tlPrimKeyInd liftKeyInd1Stage liftKeyInd2Stage)

@[expose] def sigKeyInd1KeyActiveAtomicProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqSigAndDdhIface (keyIndSpec S) (pqKeyIndCodec S)
      (PB 32) .unit .bool (.prod (PB 1569) (PB 64)) :=
  liftKeyInd1Stage tlSigDdhKeyInd S (sigKeyInd1KeyActiveDslProg S b)

@[expose] def shcrKeyInd1KeyActiveAtomicProg (S : Setup) (b : QueryBudget) :
    TwoStageCostedReduction pqAtomicOps pqPrimIface (keyIndSpec S) (pqKeyIndCodec S)
      (.prod (PB 1568) (PB 3168)) .unit .bool (PB 1568)
      (.prod (PB 32) (PB 1568)) (PB 1568) :=
  liftKeyInd2Stage tlPrimKeyInd S (shcrKeyInd1KeyActiveDslProg S b)

@[expose] def fgKeyInd1KeyGapDhActiveAtomicProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqSigAndDdhIface (keyIndSpec S) (pqKeyIndCodec S)
      (.prod (PB 32) (PB 32)) .unit .bool (PB 32) :=
  liftKeyInd1Stage tlSigDdhKeyInd S (fgKeyInd1KeyGapDhActiveDslProg S b)

/-- Creation-order `KeyIndCostedReductionFamily S` packaging the three active one-key reductions. -/
@[expose] def pqxdhKeyInd1KeyActiveCostedSims (S : Setup) : KeyIndCostedReductionFamily S where
  sig  := sigKeyInd1KeyActiveAtomicProg S
  shcr := shcrKeyInd1KeyActiveAtomicProg S
  gdh  := fgKeyInd1KeyGapDhActiveAtomicProg S

end

end Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs
