/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShallow -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeySigEval -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Pqxdh.Security.BoundProofDefs -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKemBounds
import VCVio.EvalDist.Monad.Basic

/-!
# Evaluation Equivalence for `sigKeyInd1KeyActiveAtomicProg`

Proves `.eval` equivalence and `GapSigEufCma` / `GapSigEufCmaReal` advantage equality between
`(pqxdhKeyInd1KeyActiveCostedSims S).eval.sig b A` and the shallow creation-order signature
reduction `sigReductionKeyInd1KeyActive S b A`.
-/


set_option autoImplicit false

open OracleSpec OracleComp
open ReductionDsl (Ty Var Env Expr Comp CostedReduction handlerImpl)
open SignalPqxdh (Bytes Setup PreKeyBundleInput KeyIndQuery KeyIndResponse PrincipalEntry
  SpkBundleEntry KeyIndAdversary QueryBudget BoundedAdv Primitives activeIdCount keyIndSpec
  encodeEC encodeKEM GapSigEufCmaAdv GapSigEufCma GapSigEufCmaReal sigAndDdhSpec
  sampleScalar32 sampleRandom64 gdhQueryBudget primQueryBudget gdhPrimQueryBudget)
open SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface pqGapDhIface pqSigAndDdhIface
  sigAndDdhOracle keyIndCodec keyIndQenc keyIndRenc keyIndRdec_keyIndRenc bundleV)
open SignalPqxdh.Security (embedPrim KeyIndCostedReductionFamily)
open SignalPqxdh.Security.RoKem (sampleIndexRange)
open SignalPqxdh.Security.Sig1Key (SigDdhSimSpec unifSigDdh primSigDdhQ sigChalQ embedGdhSigDdh
  Sig1KeySimState runWithSigDdhStep)
open SignalPqxdh.Security.FgGapDh (FgKeyIndSimState fgKeyIndStep)
open SignalPqxdh.Security.ReductionDsl (embedPrim_bind embedPrim_pure)
open SignalPqxdh.Security.ReductionDsl.KeyInd (PT Ext v letV letV_eval bindV bind_congr2 caseOptV
  caseSumV isSomeE eCaseOpt eLet eLet2 eAny natEq natEq_eval nat2Eq nat2_beq litB litB_eval
  widenEC_eval sBool sBool_eval sIndex qSigDdhSign_eval liftBase liftGdhToSigDdh
  rNone keyIndQueryTy keyIndRespTy preKeyBundleTy initQTy keyIndQueryToVal keyIndRespToVal
  keyIndStateToVal principalEntryToVal preKeyBundleToVal decPrin_enc honestPeerC_eval
  KeyIndListsBounded sig1KeyStTy s1Base s1Fg s1Target s1Pk s1Budget s1Forgery s1Mk s1Upd s1Prim
  s1Prim_eval qSigDdhSign sig1KeyStToVal encSig1KeyRS sig1KeyTargetGenSpkB delegateFgC
  AllOut_embedGdhSigDdh grow_refl renamePair pa2Mk gdhHandle2
  simulateQ_handlerImpl_bind_eq_runWithSigDdhStep_bind sIndex_eval smBase smFgL smRaw smLog smPows
  smMk smUpd emptySimE simStateToVal gdhHandle stPrin stSpks)
open SignalPqxdh.Security.ReductionDsl.KeyIndGapDh (FgSimListsBounded AllOut Grow Inv emptySimE_eval
  fgKeyIndStep_grow)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (activeSigBudget optNatMatchesE
  sig1KeyActiveStTy S1ARS saTP saInner extract1KeyActiveC sig1KeyActiveInitPrinB
  sig1KeyActiveInitiateCheckC sig1KeyActivePreDispatchC sig1KeyActiveHandleC
  sigKeyInd1KeyActiveDslProg sigKeyInd1KeyActiveAtomicProg pqxdhKeyInd1KeyActiveCostedSims)
open Computational.Proofs.SignalPqxdh.AtomicLift (tlSigDdhKeyInd tlGapDhKeyInd
  keyIndUnsupportedPrimW liftKeyInd1Stage_eval embedVal)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShallow (optNatMatches
  Sig1KeyActiveSimState extractBundleForgeryActivePrim sig1KeyTargetGenSpk sig1KeyActiveStep
  sigReductionKeyInd1KeyActiveRunAt sigReductionKeyInd1KeyActive)

namespace Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveSigEval

public section
/-! ## Unsupported-query vanishing and `AtomicLift` `.eval` bridge -/

private def zPrimWS : pqPrimIface.smp.Samp → ℕ := fun _ => 0

private def zGapDhW : pqGapDhIface.Tag → ℕ := tlGapDhKeyInd.unsupportedW

private def zGapDhWS : pqGapDhIface.smp.Samp → ℕ := fun _ => 0

private def zSigDdhW : pqSigAndDdhIface.Tag → ℕ :=
  tlSigDdhKeyInd.unsupportedW

private def zSigDdhWS : pqSigAndDdhIface.smp.Samp → ℕ :=
  fun _ => 0

section UnsupportedHelpers

open SignalPqxdh.Security.ReductionDsl.KeyInd (keyIndStateTy sBytes32 sRandom64 sDrKey96 qX25519 qX25519Base
  qPow8 qIsCanonical qSigPkGen qSigSign qSigVerify qKemKeyGen qKemEncaps qKemDecaps qHkdfDerive96
  gPrim ddhQ findMV anyMV findHonestC isAdvRegC isGameSpkC isGameOpkC resolveSigPkC honestPeerC
  checkProvC keyIndSessionEntryTy keyIndRespEntryTy partnerC koskSenderOkPowsC koskBundleOkPowsC
  lookupSpkSkC chooseRespRandC chooseInitRandC mkSecretPosC mkPairPosC computePosC
  computeOptPosInitC fgPosTy ddhEqC ddhEqOptC fgPatchEntryTy entryMatchesC fgPatchC accQTy
  principalEntryTy spkBundleEntryTy opkEntryTy drKeyTy finishAcceptGdhC simTy roParsedC
  roRawFallbackC wrapSim2 wrapBase2 initPrinGdh2B corruptB genSpkGdh2B genOpkGdh2B initiateGdh2B
  acceptOpkGdh2B acceptNoOpkGdhB testB revealB registerGdhB revealSpkB)

@[local simp] private theorem sBool_unsup {Γ : List PT} :
    (sBool (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem sBytes32_unsup {Γ : List PT} :
    (sBytes32 (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem sRandom64_unsup {Γ : List PT} :
    (sRandom64 (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem sDrKey96_unsup {Γ : List PT} :
    (sDrKey96 (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem sIndex_unsup (N : ℕ) {Γ : List PT} :
    (sIndex N (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qX25519_unsup {Γ : List PT}
    (e : Expr pqxdhOps Γ (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32))) :
    (qX25519 e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qX25519Base_unsup {Γ : List PT}
    (e : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32)) :
    (qX25519Base e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qPow8_unsup {Γ : List PT}
    (e : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32)) :
    (qPow8 e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qIsCanonical_unsup {Γ : List PT}
    (e : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32)) :
    (qIsCanonical e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qSigPkGen_unsup {Γ : List PT}
    (e : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32)) :
    (qSigPkGen e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qSigSign_unsup (m : ℕ+) {Γ : List PT}
    (e : Expr pqxdhOps Γ (.prod (SignalPqxdh.LegacyCosted.B 32)
      (.prod (SignalPqxdh.LegacyCosted.B m) (SignalPqxdh.LegacyCosted.B 64)))) :
    (qSigSign m e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qSigVerify_unsup (m : ℕ+) {Γ : List PT}
    (e : Expr pqxdhOps Γ (.prod (SignalPqxdh.LegacyCosted.B 32)
      (.prod (SignalPqxdh.LegacyCosted.B m) (SignalPqxdh.LegacyCosted.B 64)))) :
    (qSigVerify m e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qKemKeyGen_unsup {Γ : List PT}
    (e : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 64)) :
    (qKemKeyGen e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qKemEncaps_unsup {Γ : List PT}
    (e : Expr pqxdhOps Γ (.prod (SignalPqxdh.LegacyCosted.B 1568) (SignalPqxdh.LegacyCosted.B 32))) :
    (qKemEncaps e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qKemDecaps_unsup {Γ : List PT}
    (e : Expr pqxdhOps Γ (.prod (SignalPqxdh.LegacyCosted.B 3168) (SignalPqxdh.LegacyCosted.B 1568))) :
    (qKemDecaps e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qHkdfDerive96_unsup (w : ℕ+) {Γ : List PT}
    (e : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B w)) :
    (qHkdfDerive96 w e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl

@[local simp] private theorem s1Prim_unsupported {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (s1Prim c).queries zSigDdhW zSigDdhWS = c.queries keyIndUnsupportedPrimW zPrimWS := by
  unfold s1Prim
  induction c with
  | query _ _ => rfl
  | sample _ _ => rfl
  | _ => simp_all [liftBase, Comp.queries]

@[local simp] private theorem gPrim_unsup {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (gPrim c).queries zGapDhW zGapDhWS = c.queries keyIndUnsupportedPrimW zPrimWS := by
  unfold gPrim
  induction c with
  | query _ _ => rfl
  | sample _ _ => rfl
  | _ => simp_all [liftBase, Comp.queries]

@[local simp] private theorem ddhQ_unsup {Γ : List PT}
    (x y z : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32)) :
    (ddhQ x y z).queries zGapDhW zGapDhWS = 0 := rfl

@[local simp] private theorem qSigDdhSign_unsupported (m : ℕ+) {Γ : List PT}
    (msg : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B m)) :
    (qSigDdhSign m msg).queries zSigDdhW zSigDdhWS = 0 := rfl

@[local simp] private theorem liftGdhToSigDdh_unsupported {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (liftGdhToSigDdh c).queries zSigDdhW zSigDdhWS = c.queries zGapDhW zGapDhWS := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhToSigDdh, Comp.queries]

@[local simp] private theorem findHonestC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (findHonestC S K st ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [findHonestC, letV, findMV, bindV, Comp.queries]

@[local simp] private theorem isAdvRegC_unsup (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (isAdvRegC K st pk).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [isAdvRegC, bindV, Comp.queries]

@[local simp] private theorem isGameSpkC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (isGameSpkC S K st pk).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [isGameSpkC, letV, anyMV, bindV, Comp.queries]

@[local simp] private theorem isGameOpkC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (isGameOpkC S K st pk).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [isGameOpkC, letV, anyMV, bindV, Comp.queries]

@[local simp] private theorem resolveSigPkC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (resolveSigPkC S K st ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [resolveSigPkC, letV, bindV, Comp.queries]

@[local simp] private theorem honestPeerC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (honestPeerC S K st ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [honestPeerC, bindV, Comp.queries]

@[local simp] private theorem checkProvC_unsup (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ preKeyBundleTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (checkProvC (Δ := Δ) S K st bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [checkProvC, bindV, letV, caseOptV, anyMV, Comp.queries]

@[local simp] private theorem partnerC_unsup {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ keyIndSessionEntryTy) (r : Var Γ₂ keyIndRespEntryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (partnerC (Δ := Δ) s r).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl

@[local simp] private theorem koskSenderOkPowsC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT}
    [Ext Γ Δ] (st : Var Γ keyIndStateTy)
    (pows : Expr pqxdhOps Δ (.list (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32))))
    (ik : Expr pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (koskSenderOkPowsC S K st pows ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [koskSenderOkPowsC, letV, bindV, Comp.queries]

@[local simp] private theorem koskBundleOkPowsC_unsup (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ keyIndStateTy)
    (pows : Expr pqxdhOps Δ (.list (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32))))
    (bu : Var Γ₂ preKeyBundleTy) :
    (koskBundleOkPowsC S K st pows bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [koskBundleOkPowsC, letV, bindV, caseOptV, Comp.queries]

@[local simp] private theorem lookupSpkSkC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT}
    [Ext Γ Δ] (st : Var Γ keyIndStateTy)
    (pows : Expr pqxdhOps Δ (.list (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32))))
    (spkPk : Expr pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (lookupSpkSkC S K st pows spkPk).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [lookupSpkSkC, letV, bindV, findMV, Comp.queries]

@[local simp] private theorem chooseRespRandC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (r : Var Δ keyIndRespEntryTy) :
    (chooseRespRandC S K st r).queries zGapDhW zGapDhWS = 0 := by
  simp [chooseRespRandC, bindV, findMV, caseOptV, Comp.queries]

@[local simp] private theorem chooseInitRandC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (s : Var Δ keyIndSessionEntryTy) :
    (chooseInitRandC S K st s).queries zGapDhW zGapDhWS = 0 := by
  simp [chooseInitRandC, bindV, findMV, caseOptV, Comp.queries]

@[local simp] private theorem mkSecretPosC_unsup {Γ : List PT}
    (z : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32)) :
    (mkSecretPosC z).queries zGapDhW zGapDhWS = 0 := by
  simp [mkSecretPosC, letV, bindV, Comp.queries]

@[local simp] private theorem mkPairPosC_unsup {Γ : List PT}
    (pk1 pk2 : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32)) :
    (mkPairPosC pk1 pk2).queries zGapDhW zGapDhWS = 0 := by
  simp [mkPairPosC, letV, bindV, Comp.queries]

@[local simp] private theorem computePosC_unsup {Γ : List PT}
    (sk1 sk2 pk1 pk2 : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32)) :
    (computePosC sk1 sk2 pk1 pk2).queries zGapDhW zGapDhWS = 0 := by
  simp [computePosC, bindV, Comp.queries]

@[local simp] private theorem computeOptPosInitC_unsup {Γ : List PT}
    (sk1 pk1 : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32))
    (opkB? : Expr pqxdhOps Γ (.opt (.prod SignalPqxdh.LegacyCosted.U32 (SignalPqxdh.LegacyCosted.B 32)))) :
    (computeOptPosInitC sk1 pk1 opkB?).queries zGapDhW zGapDhWS = 0 := by
  simp [computeOptPosInitC, letV, caseOptV, bindV, Comp.queries]

@[local simp] private theorem ddhEqC_unsup {Γ : List PT} (p1 p2 : Expr pqxdhOps Γ fgPosTy) :
    (ddhEqC p1 p2).queries zGapDhW zGapDhWS = 0 := by
  simp [ddhEqC, letV, caseSumV, Comp.queries]

@[local simp] private theorem ddhEqOptC_unsup {Γ : List PT}
    (p1? p2? : Expr pqxdhOps Γ (.opt fgPosTy)) :
    (ddhEqOptC p1? p2?).queries zGapDhW zGapDhWS = 0 := by
  simp [ddhEqOptC, letV, caseOptV, Comp.queries]

@[local simp] private theorem entryMatchesC_unsup {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₃ Δ] [Ext Γ₂ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (SignalPqxdh.LegacyCosted.B 32))
    (e : Var Δ fgPatchEntryTy) :
    (entryMatchesC pos1 pos2 pos3 pos4? ss e).queries zGapDhW zGapDhWS = 0 := by
  simp [entryMatchesC, bindV, Comp.queries]

@[local simp] private theorem fgPatchC_unsup (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (SignalPqxdh.LegacyCosted.B 32))
    (fgL : Expr pqxdhOps Δ (.list fgPatchEntryTy)) :
    (fgPatchC K pos1 pos2 pos3 pos4? ss fgL).queries zGapDhW zGapDhWS = 0 := by
  simp [fgPatchC, letV, findMV, caseOptV, bindV, Comp.queries]

@[local simp] private theorem finishAcceptGdhC_unsup (S : Setup) (K : Nat)
    {Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Δ : List PT}
    [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ] [Ext Γ₇ Δ]
    (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (hasOpk : Bool) (x : Var Γ₄ accQTy)
    (ke : Var Γ₅ (.prod .nat principalEntryTy))
    (be : Var Γ₆ (.prod (.prod .nat .nat) spkBundleEntryTy))
    (opkPkOpt : Expr pqxdhOps Δ (.opt (SignalPqxdh.LegacyCosted.B 32)))
    (opks' : Expr pqxdhOps Δ (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)))
    (usedO' : Expr pqxdhOps Δ (.list (.prod .nat (.prod .nat .nat))))
    (usedN' : Expr pqxdhOps Δ (.list (.prod .nat (.prod .nat .nat))))
    (kyb' : Expr pqxdhOps Δ (.list (.prod .nat (.prod SignalPqxdh.LegacyCosted.U32
      (.prod SignalPqxdh.LegacyCosted.U32 (SignalPqxdh.LegacyCosted.B 32))))))
    (patchR : Var Γ₇ (.prod drKeyTy (.list fgPatchEntryTy))) :
    (finishAcceptGdhC S K sm bSt hasOpk x ke be opkPkOpt opks' usedO' usedN' kyb' patchR).queries
      zGapDhW zGapDhWS = 0 := by
  simp [finishAcceptGdhC, letV, bindV, Comp.queries]

@[local simp] private theorem roParsedC_unsup (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (sm : Var Γ₁ simTy) (sec : Var Γ₂ (SignalPqxdh.LegacyCosted.B 192)) :
    (roParsedC (Δ := Δ) K sm sec).queries zGapDhW zGapDhWS = 0 := by
  simp [roParsedC, roRawFallbackC, letV, bindV, caseOptV, Comp.queries]

@[local simp] private theorem rename_queries_eq {Γ Δ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) (ρ : ∀ {τ}, Var Γ τ → Var Δ τ) :
    (c.rename ρ).queries zGapDhW zGapDhWS = c.queries zGapDhW zGapDhWS := by
  induction c generalizing Δ with
  | _ => simp_all [ReductionDsl.Comp.rename, Comp.queries]

private theorem gdhHandle2_unsupported (S : Setup) (K : Nat) :
    (gdhHandle2 S K).queries zGapDhW zGapDhWS = 0 := by
  simp [gdhHandle2, wrapSim2, wrapBase2, initPrinGdh2B, corruptB, genSpkGdh2B, genOpkGdh2B,
    initiateGdh2B, acceptOpkGdh2B, acceptNoOpkGdhB, testB, revealB, registerGdhB, revealSpkB,
    letV, bindV, caseOptV, caseSumV, Comp.queries]

private theorem sigActive_init_unsupported (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyActiveDslProg S b).init.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (sigKeyInd1KeyActiveDslProg S b).init.queries zSigDdhW zSigDdhWS = 0
  simp [sigKeyInd1KeyActiveDslProg, bindV, Comp.queries]

private theorem sigActive_finish_unsupported (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyActiveDslProg S b).finish.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 :=
  rfl

private theorem sigActive_handle_unsupported (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyActiveDslProg S b).handle.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (sig1KeyActiveHandleC S b.q_total).queries zSigDdhW zSigDdhWS = 0
  simp [sig1KeyActiveHandleC, sig1KeyActivePreDispatchC, sig1KeyActiveInitPrinB,
    sig1KeyTargetGenSpkB, sig1KeyActiveInitiateCheckC, extract1KeyActiveC,
    gdhHandle2_unsupported S b.q_total,
    letV, bindV, caseOptV, caseSumV, Comp.queries]

end UnsupportedHelpers

theorem sigKeyInd1KeyActiveAtomicProg_eval_eq (S : Setup) (b : QueryBudget)
    (adv : Unit → OracleComp (unifSpec + keyIndSpec S) Bool) (pk : Bytes) :
    (sigKeyInd1KeyActiveAtomicProg S b).eval adv pk =
      (sigKeyInd1KeyActiveDslProg S b).eval adv pk := by
  have h := liftKeyInd1Stage_eval tlSigDdhKeyInd S (sigKeyInd1KeyActiveDslProg S b)
    (sigActive_init_unsupported S b)
    (sigActive_handle_unsupported S b)
    (sigActive_finish_unsupported S b) adv pk
  have hId : embedVal (.prod (SignalPqxdh.LegacyCosted.B 1569) (SignalPqxdh.LegacyCosted.B 64)) =
      id := by
    funext ⟨x, y⟩; rfl
  rw [hId, id_map] at h
  exact h

/-! ## State encoding and per-branch evaluation agreement -/

@[expose] def sig1KeyActiveStToVal {S : Setup} (st : Sig1KeyActiveSimState S) : sig1KeyActiveStTy.denote :=
  (st.resolvedPrin?, sig1KeyStToVal st.inner)

@[expose] def encSig1KeyActiveRS {S : Setup} (p : KeyIndResponse × Sig1KeyActiveSimState S) : S1ARS.denote :=
  (keyIndRespToVal p.1, sig1KeyActiveStToVal p.2)

section
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] Env.get Ext.wk sigAndDdhOracle

@[simp] theorem optNatMatchesE_eval {Γ : List PT}
    (tpOpt : Expr pqxdhOps Γ (.opt .nat)) (u : Expr pqxdhOps Γ .nat) (env : Env Γ) :
    (optNatMatchesE tpOpt u).eval env = optNatMatches (tpOpt.eval env) (u.eval env) := by
  simp only [optNatMatchesE, eLet2, eLet, eCaseOpt, v, natEq_eval, Expr.eval,
    SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
    SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
    SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
    SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk']
  cases tpOpt.eval env <;> rfl

theorem extract1KeyActiveC_eval (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (stV : Var Γ₁ sig1KeyActiveStTy) (buV : Var Γ₂ preKeyBundleTy) (env : Env Δ)
    (st : Sig1KeyActiveSimState S) (bu : PreKeyBundleInput)
    (hst : env.get (Ext.wk stV) = sig1KeyActiveStToVal st)
    (hbu : env.get (Ext.wk buV) = preKeyBundleToVal bu)
    (hB : KeyIndListsBounded st.inner.fg.base K) :
    (extract1KeyActiveC S K stV buV).eval env =
      embedPrim (spec := sigAndDdhSpec)
        (extractBundleForgeryActivePrim S st.resolvedPrin? st.inner.targetPk
          st.inner.fg.base.principals st.inner.fg.base.spkBundles bu st.inner.forgery) := by
  rcases st with ⟨tp?, ⟨fgSt, tp, tpk, bud, fg⟩⟩
  unfold extract1KeyActiveC extractBundleForgeryActivePrim
  simp only [bindV, letV_eval, Comp.eval, s1Prim_eval]
  rw [honestPeerC_eval]
  core_simp [hst, hbu, saTP, saInner, optNatMatchesE_eval, s1Base, s1Fg, s1Forgery, s1Target,
    s1Pk, smBase, sig1KeyActiveStToVal, sig1KeyStToVal, simStateToVal, decPrin_enc,
    preKeyBundleToVal, List.take_of_length_le, hB.spkBundles_le, widenEC_eval]
  simp only [embedPrim_bind, embedPrim_pure, Prod.map, id]
  rw [decPrin_enc, List.take_of_length_le hB.principals_le]
  refine bind_congr2 rfl fun peer => bind_congr2 ?_ fun v1 => bind_congr2 ?_ fun v2 => ?_
  · rw [hbu]; rfl
  · rw [hbu]; rfl
  · congr 1
    rcases fg with _ | fg
    · rcases peer with _ | k
      · rfl
      · simp only [encodeEC, encodeKEM]
        cases optNatMatches tp? k <;> rfl
    · rfl

theorem sig1KeyActiveInitPrinB_eval (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (stV : Var Γ₁ sig1KeyActiveStTy) (uV : Var Γ₂ .nat) (env : Env Δ)
    (st : Sig1KeyActiveSimState S) (u : Fin S.N_id)
    (hst : env.get (Ext.wk stV) = sig1KeyActiveStToVal st)
    (hu : env.get (Ext.wk uV) = u.val)
    (hfg : st.inner.forgery = none)
    (hB : KeyIndListsBounded st.inner.fg.base K) :
    (sig1KeyActiveInitPrinB K stV uV).eval env =
      encSig1KeyActiveRS <$> sig1KeyActiveStep S K (.initPrin u) st := by
  rcases st with ⟨tp?, ⟨fgSt, tp, tpk, bud, fg⟩⟩
  subst hfg
  have hsa : (saInner (v stV)).eval env = sig1KeyStToVal ⟨fgSt, tp, tpk, bud, none⟩ := by
    simp [v, Expr.eval, hst, sig1KeyActiveStToVal]
  unfold sig1KeyActiveInitPrinB
  rw [letV_eval, hsa]
  have c1 : (eAny K (stPrin (s1Base (v (Var.zero : Var (sig1KeyStTy :: Δ) sig1KeyStTy)))) fun e =>
        natEq (.fst (v e)) (v uV)).eval (.cons (sig1KeyStToVal ⟨fgSt, tp, tpk, bud, none⟩) env) =
      fgSt.base.principals.any (fun x => x.1 == u.val) := by
    simp only [Expr.eval, v, eAny, hu, stPrin, s1Base, s1Fg, smBase, natEq_eval,
      SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
      SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
      SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
      SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
      keyIndStateToVal, simStateToVal, sig1KeyStToVal, List.any_map,
      Function.comp_def, List.take_of_length_le, List.length_map, hB.principals_le, Prod.map, id]
  simp only [Comp.eval, c1]
  by_cases h1 : (fgSt.base.principals.any fun x => x.1 == u.val) = true
  · simp only [h1, ↓reduceIte, sig1KeyActiveStep, Option.isSome_none, Bool.false_eq_true,
      map_pure, Expr.eval, v, hst, rNone, encSig1KeyActiveRS, sig1KeyActiveStToVal,
      keyIndRespToVal, keyIndRenc,
      SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
      SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk']
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, sig1KeyActiveStep, Option.isSome_none]
    core_simp [hst, hu, saTP, s1Pk, s1Upd, s1Mk, s1Fg, s1Base, s1Target, s1Budget, s1Forgery,
      smUpd, smMk, smBase, smFgL, smRaw, smLog, smPows,
      sig1KeyActiveStToVal, sig1KeyStToVal, simStateToVal, s1Prim_eval, List.length_map]
    simp only [unifSigDdh, primSigDdhQ, SignalPqxdh.Security.primQ, sampleScalar32,
      bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def,
      encSig1KeyActiveRS, sig1KeyActiveStToVal, sig1KeyStToVal, simStateToVal,
      keyIndStateToVal, keyIndRespToVal, keyIndRenc, List.map_cons]
    refine congrArg (fun h => _ >>= h) (funext fun s0 => ?_)
    refine congrArg (fun h => _ >>= h) (funext fun ik => ?_)
    cases (fgSt.base.principals.length == tp) <;> rfl

theorem sig1KeyTargetGenSpkB_active_eval (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (sV : Var Γ₁ sig1KeyStTy) (xV : Var Γ₂ (.prod .nat .nat)) (env : Env Δ)
    (st : Sig1KeySimState S) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hs : env.get (Ext.wk sV) = sig1KeyStToVal st)
    (hx : env.get (Ext.wk xV) = (u.val, j.val))
    (hB : KeyIndListsBounded st.fg.base K) :
    (sig1KeyTargetGenSpkB K sV xV).eval env =
      encSig1KeyRS <$> sig1KeyTargetGenSpk S u j st := by
  rcases st with ⟨fgSt, tp, tpk, bud, fg⟩
  unfold sig1KeyTargetGenSpkB sig1KeyTargetGenSpk
  have c3 : (eAny K (stSpks (s1Base (v sV))) fun e => nat2Eq (.fst (v e)) (v xV)).eval env =
      fgSt.base.spkBundles.any (fun x => x.1.1 == u.val && x.1.2 == j.val) := by
    core_simp [hs, hx, s1Base, s1Fg, smBase, sig1KeyStToVal, simStateToVal,
      List.take_of_length_le, hB.spkBundles_le, Prod.map, id]
  simp only [Comp.eval, c3, nat2_beq]
  by_cases h3 : (fgSt.base.spkBundles.any fun x => x.1.1 == u.val && x.1.2 == j.val) = true
  · simp only [h3, ↓reduceIte, map_pure, Expr.eval, v, hs, rNone,
      encSig1KeyRS, keyIndRespToVal, keyIndRenc]
  · simp only [h3, Bool.false_eq_true, ↓reduceIte]
    core_simp [hs, hx, s1Base, s1Fg, s1Upd, s1Mk, s1Pk, s1Target, s1Budget, s1Forgery,
      smUpd, smMk, smBase, smFgL, smRaw, smLog, smPows,
      sig1KeyStToVal, simStateToVal, List.take_of_length_le, hB.principals_le,
      s1Prim_eval, qSigDdhSign_eval]
    rcases hfd : fgSt.base.principals.find? (fun x => x.1 == u.val) with _ | ⟨i, e⟩
    · simp [hfd, encSig1KeyRS, sig1KeyStToVal, simStateToVal, keyIndStateToVal,
        keyIndRespToVal, keyIndRenc]
    · have hfd' : List.find? (fun x : Nat × PrincipalEntry =>
          (Prod.map id principalEntryToVal x).1 == u.val) fgSt.base.principals = some (i, e) := hfd
      rw [hfd', hfd]
      cases bud with
      | zero =>
        simp [encSig1KeyRS, sig1KeyStToVal, simStateToVal, keyIndStateToVal,
          keyIndRespToVal, keyIndRenc]
      | succ bud' =>
        simp only [Option.map, beq_iff_eq, Nat.add_one_ne_zero,
          ↓reduceIte, Nat.add_sub_cancel, unifSigDdh, sampleScalar32,
          bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def,
          encSig1KeyRS, sig1KeyStToVal, simStateToVal, keyIndStateToVal,
          bundleV, keyIndRespToVal, keyIndRenc, List.map_cons, encodeEC, encodeKEM]
        rfl

theorem sig1KeyActiveInitiateCheckC_eval (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (stV : Var Γ₁ sig1KeyActiveStTy) (xV : Var Γ₂ initQTy) (env : Env Δ)
    (st : Sig1KeyActiveSimState S) (uVal iVal : Nat) (bu : PreKeyBundleInput)
    (hst : env.get (Ext.wk stV) = sig1KeyActiveStToVal st)
    (hx : env.get (Ext.wk xV) = (uVal, (iVal, preKeyBundleToVal bu)))
    (hB : KeyIndListsBounded st.inner.fg.base K) :
    (sig1KeyActiveInitiateCheckC S K stV xV).eval env =
      (do
        let fg' ← embedPrim (spec := sigAndDdhSpec)
          (extractBundleForgeryActivePrim S st.resolvedPrin? st.inner.targetPk
            st.inner.fg.base.principals st.inner.fg.base.spkBundles bu st.inner.forgery)
        if fg'.isSome then
          pure (.inl (encSig1KeyActiveRS (.noneResp, { st with inner := { st.inner with forgery := fg' } })))
        else
          pure (.inr ())) := by
  have hE := extract1KeyActiveC_eval S K stV
    (Γ₂ := preKeyBundleTy :: Δ) .zero (.cons (preKeyBundleToVal bu) env) st bu
    (by simp [hst]) rfl hB
  unfold sig1KeyActiveInitiateCheckC
  simp only [letV_eval, bindV, Comp.eval, Expr.eval, v, hx]
  rw [hE]
  refine congrArg (fun h => _ >>= h) (funext fun fg' => ?_)
  cases fg' <;>
    simp [isSomeE, Expr.eval, hst,
      encSig1KeyActiveRS, sig1KeyActiveStToVal, sig1KeyStToVal, rNone, keyIndRespToVal, keyIndRenc]

section DelegateHelpers
open SignalPqxdh.Security.ReductionDsl.KeyInd (pa2ZeroVal params2ToFlat gdhStateTy gdhState2Ty
  liftGdhToSigDdh_eval embedGdhSigDdh_bind embedGdhSigDdh_pure)
open SignalPqxdh.Security.ReductionDsl.KeyIndGapDh (InBoundsParams2 gdhHandle2_eval_map_eq
  paramsDhVal gdhHandle_eval_dh encGdhRS)

private theorem delegateFgActiveC_eval (S : Setup) (K : Nat)
    (st : Sig1KeyActiveSimState S) (q : KeyIndQuery S)
    (hB : FgSimListsBounded st.inner.fg K) :
    (let stV : Var [sig1KeyActiveStTy, keyIndQueryTy] sig1KeyActiveStTy := .zero
     let qV : Var [sig1KeyActiveStTy, keyIndQueryTy] keyIndQueryTy := .succ .zero
     let Δ : List PT := [.unit, .sum S1ARS .unit, sig1KeyActiveStTy, keyIndQueryTy]
     (letV (saInner (v (Δ := Δ) stV)) fun s =>
      letV (.pair (pa2Mk (litB 32 []) (s1Pk (v s)) (litB 32 []) .none (.bool false) .none .none
        (.bool false) .none (.nat 1)) (s1Fg (v s))) fun gdhSt2 =>
      bindV (liftGdhToSigDdh ((gdhHandle2 S K).rename (renamePair gdhSt2 (Ext.wk qV)))) fun r =>
      .ret (.pair (.fst (v r)) (.pair (saTP (v stV)) (s1Upd (v s) (fg := .snd (.snd (v r))))))).eval
       (.cons () (.cons (.inr ()) (.cons (sig1KeyActiveStToVal st) (.cons (keyIndQueryToVal q) .nil))))) =
    (fun p => encSig1KeyActiveRS (p.1, { st with inner := { st.inner with fg := p.2 } })) <$>
      embedGdhSigDdh
        (fgKeyIndStep false S.N_send_tot S.N_spk_tot S K [] st.inner.targetPk q st.inner.fg) := by
  simp only [letV_eval, bindV, Comp.eval, liftGdhToSigDdh_eval, ReductionDsl.Comp.rename_eval,
    pa2Mk, litB_eval, v, Expr.eval, sig1KeyActiveStToVal, saTP, saInner, sig1KeyStToVal,
    s1Pk, s1Fg, s1Upd, s1Mk, s1Target, s1Budget, s1Forgery,
    ReductionDsl.Env.ofRename, renamePair,
    SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
    SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
    SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
    SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk']
  have hB2 : InBoundsParams2 S (pa2ZeroVal st.inner.targetPk) := by
    unfold InBoundsParams2 pa2ZeroVal
    refine _root_.Or.inr ⟨?_, ?_, ?_, ?_⟩
    · intro _ h; cases h
    · intro _ _ _ h; cases h
    · intro _ _ h; cases h
    · intro _ _ _ h; cases h
  have hGdh2 := congrArg (Functor.map (fun r : keyIndRespTy.denote × gdhStateTy.denote => (r.1, r.2.2)))
    (gdhHandle2_eval_map_eq S K (pa2ZeroVal st.inner.targetPk) hB2
      (simStateToVal st.inner.fg) q).1
  have hFlat : params2ToFlat S (pa2ZeroVal st.inner.targetPk) =
      paramsDhVal S false S.N_send_tot S.N_spk_tot [] st.inner.targetPk := rfl
  dsimp only [keyIndCodec] at hGdh2
  rw [hFlat, gdhHandle_eval_dh S K false S.N_send_tot S.N_spk_tot [] st.inner.targetPk q st.inner.fg hB]
    at hGdh2
  have hMap := congrArg embedGdhSigDdh hGdh2
  unfold pa2ZeroVal at hMap
  simp only [encGdhRS, keyIndQueryToVal, map_eq_bind_pure_comp, embedGdhSigDdh_bind, embedGdhSigDdh_pure,
    bind_assoc, Function.comp_def, pure_bind] at hMap ⊢
  calc
    _ = ((embedGdhSigDdh ((gdhHandle2 S K).eval
          (.cons (([], (st.inner.targetPk, ([], (none, (false, (none, (none, (false, (none, 1))))))))),
                  simStateToVal st.inner.fg)
            (.cons (keyIndQenc q) .nil))) >>=
          fun x : keyIndRespTy.denote × gdhState2Ty.denote => pure (x.1, x.2.2)) >>=
        fun y => pure (y.1, (st.resolvedPrin?,
          (y.2, (st.inner.targetParty, (st.inner.targetPk,
            (st.inner.signBudget, st.inner.forgery))))))) := by
        simp only [bind_assoc, pure_bind]
    _ = _ := by
        rw [hMap]
        simp only [bind_assoc, pure_bind, encSig1KeyActiveRS, sig1KeyActiveStToVal, sig1KeyStToVal]

end DelegateHelpers

theorem sig1KeyActiveHandleC_eval (S : Setup) (K : Nat)
    (q : KeyIndQuery S) (st : Sig1KeyActiveSimState S) (hB : FgSimListsBounded st.inner.fg K) :
    (sig1KeyActiveHandleC S K).eval (.cons (sig1KeyActiveStToVal st) (.cons (keyIndQueryToVal q) .nil)) =
      encSig1KeyActiveRS <$> sig1KeyActiveStep S K q st := by
  let env0 : Env [sig1KeyActiveStTy, keyIndQueryTy] :=
    .cons (sig1KeyActiveStToVal st) (.cons (keyIndQueryToVal q) .nil)
  change (sig1KeyActiveHandleC S K).eval env0 = encSig1KeyActiveRS <$> sig1KeyActiveStep S K q st
  rcases hfg : st.inner.forgery with _ | fgVal
  ·
    have hIsSome : ∀ (qVal : keyIndQueryTy.denote),
        (isSomeE (s1Forgery (saInner (Expr.var Var.zero)))).eval
          (.cons (sig1KeyActiveStToVal st) (.cons qVal .nil)) = false := by
      intro qVal
      simp [isSomeE, s1Forgery, saInner, sig1KeyActiveStToVal, sig1KeyStToVal, hfg, Expr.eval]
    simp only [sig1KeyActiveHandleC, sig1KeyActivePreDispatchC, bindV, Comp.eval, env0, v,
      hIsSome, Bool.false_eq_true, ↓reduceIte,
      SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk']
    cases q with
    | initPrin u =>
      simp only [caseSumV, Comp.eval, keyIndQueryToVal, keyIndQenc,
        Expr.eval, SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk']
      rw [sig1KeyActiveInitPrinB_eval S K .zero .zero _ st u rfl rfl hfg hB.1]
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    | genSPK u j =>
      simp only [caseSumV, Comp.eval, keyIndQueryToVal, keyIndQenc,
        optNatMatchesE_eval, saTP, saInner, sig1KeyActiveStToVal,
        Expr.eval, SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk']
      by_cases htgt : optNatMatches st.resolvedPrin? u.val = true
      · simp only [htgt, ↓reduceIte, letV_eval, Comp.eval, Expr.eval,
          SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
          SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', bind_assoc]
        rw [sig1KeyTargetGenSpkB_active_eval S K .zero .zero _ st.inner u j rfl rfl hB.1]
        simp only [sig1KeyActiveStep, hfg, Option.isSome_none, htgt, Bool.false_eq_true, ↓reduceIte,
          encSig1KeyRS, encSig1KeyActiveRS, sig1KeyActiveStToVal,
          map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
      · simp only [htgt, Bool.false_eq_true, ↓reduceIte, pure_bind]
        exact (delegateFgActiveC_eval S K st (.genSPK u j) hB).trans (by
          simp only [sig1KeyActiveStep, hfg, Option.isSome_none, htgt, Bool.false_eq_true, ↓reduceIte,
            map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind])
    | initiateOPK u i bu =>
      simp only [caseSumV, Comp.eval, keyIndQueryToVal, keyIndQenc,
        saTP, saInner, sig1KeyActiveStToVal,
        Expr.eval, SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk']
      rw [sig1KeyActiveInitiateCheckC_eval S K .zero .zero _ st u.val i.val bu rfl rfl hB.1]
      simp only [sig1KeyActiveStep, hfg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        bind_assoc, map_eq_bind_pure_comp, Function.comp_def]
      refine congrArg (fun h => _ >>= h) (funext fun fg' => ?_)
      by_cases hfg' : fg'.isSome = true
      · simp only [hfg', ↓reduceIte, pure_bind]
      · simp only [hfg', Bool.false_eq_true, ↓reduceIte, pure_bind]
        exact (delegateFgActiveC_eval S K st (.initiateOPK u i bu) hB).trans (by
          simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind, hfg])
    | initiateNoOPK u i bu =>
      simp only [caseSumV, Comp.eval, keyIndQueryToVal, keyIndQenc,
        saTP, saInner, sig1KeyActiveStToVal,
        Expr.eval, SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk']
      rw [sig1KeyActiveInitiateCheckC_eval S K .zero .zero _ st u.val i.val bu rfl rfl hB.1]
      simp only [sig1KeyActiveStep, hfg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        bind_assoc, map_eq_bind_pure_comp, Function.comp_def]
      refine congrArg (fun h => _ >>= h) (funext fun fg' => ?_)
      by_cases hfg' : fg'.isSome = true
      · simp only [hfg', ↓reduceIte, pure_bind]
      · simp only [hfg', Bool.false_eq_true, ↓reduceIte, pure_bind]
        exact (delegateFgActiveC_eval S K st (.initiateNoOPK u i bu) hB).trans (by
          simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind, hfg])
    | corruptIK u =>
      simp only [caseSumV, Comp.eval, keyIndQueryToVal, keyIndQenc,
        Expr.eval, SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', pure_bind]
      exact (delegateFgActiveC_eval S K st (.corruptIK u) hB).trans (by
        simp only [sig1KeyActiveStep, hfg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind])
    | genOPK u j o =>
      simp only [caseSumV, Comp.eval, keyIndQueryToVal, keyIndQenc,
        Expr.eval, SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', pure_bind]
      exact (delegateFgActiveC_eval S K st (.genOPK u j o) hB).trans (by
        simp only [sig1KeyActiveStep, hfg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind])
    | acceptOPK k j o hdr =>
      simp only [caseSumV, Comp.eval, keyIndQueryToVal, keyIndQenc,
        Expr.eval, SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', pure_bind]
      exact (delegateFgActiveC_eval S K st (.acceptOPK k j o hdr) hB).trans (by
        simp only [sig1KeyActiveStep, hfg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind])
    | acceptNoOPK k j l hdr =>
      simp only [caseSumV, Comp.eval, keyIndQueryToVal, keyIndQenc,
        Expr.eval, SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', pure_bind]
      exact (delegateFgActiveC_eval S K st (.acceptNoOPK k j l hdr) hB).trans (by
        simp only [sig1KeyActiveStep, hfg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind])
    | testSession sid =>
      simp only [caseSumV, Comp.eval, keyIndQueryToVal, keyIndQenc,
        Expr.eval, SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', pure_bind]
      exact (delegateFgActiveC_eval S K st (.testSession sid) hB).trans (by
        simp only [sig1KeyActiveStep, hfg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind])
    | roQuery sec =>
      simp only [caseSumV, Comp.eval, keyIndQueryToVal, keyIndQenc,
        Expr.eval, SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', pure_bind]
      exact (delegateFgActiveC_eval S K st (.roQuery sec) hB).trans (by
        simp only [sig1KeyActiveStep, hfg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind])
    | revealDhSecrets =>
      simp only [caseSumV, Comp.eval, keyIndQueryToVal, keyIndQenc,
        Expr.eval, SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', pure_bind]
      exact (delegateFgActiveC_eval S K st .revealDhSecrets hB).trans (by
        simp only [sig1KeyActiveStep, hfg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind])
    | revealSessionKey sid =>
      simp only [caseSumV, Comp.eval, keyIndQueryToVal, keyIndQenc,
        Expr.eval, SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', pure_bind]
      exact (delegateFgActiveC_eval S K st (.revealSessionKey sid) hB).trans (by
        simp only [sig1KeyActiveStep, hfg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind])
    | registerKey sk =>
      simp only [caseSumV, Comp.eval, keyIndQueryToVal, keyIndQenc,
        Expr.eval, SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', pure_bind]
      exact (delegateFgActiveC_eval S K st (.registerKey sk) hB).trans (by
        simp only [sig1KeyActiveStep, hfg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind])
    | revealSpkSk u j =>
      simp only [caseSumV, Comp.eval, keyIndQueryToVal, keyIndQenc,
        Expr.eval, SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk', pure_bind]
      exact (delegateFgActiveC_eval S K st (.revealSpkSk u j) hB).trans (by
        simp only [sig1KeyActiveStep, hfg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind])
  ·
    have hIsSome : ∀ (qVal : keyIndQueryTy.denote),
        (isSomeE (s1Forgery (saInner (Expr.var Var.zero)))).eval
          (.cons (sig1KeyActiveStToVal st) (.cons qVal .nil)) = true := by
      intro qVal
      simp [isSomeE, s1Forgery, saInner, sig1KeyActiveStToVal, sig1KeyStToVal, hfg, Expr.eval]
    simp only [sig1KeyActiveHandleC, sig1KeyActivePreDispatchC, bindV, Comp.eval, env0, v,
      hIsSome, ↓reduceIte, pure_bind,
      SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk']
    simp only [caseSumV, Comp.eval, sig1KeyActiveStep, hfg, Option.isSome_some, ↓reduceIte,
      map_pure, Expr.eval, SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero', rNone,
      encSig1KeyActiveRS, sig1KeyActiveStToVal, keyIndRespToVal, keyIndRenc]

end

/-! ## Runner bridge and advantage equalities -/

theorem sig1KeyTargetGenSpk_grow {S : Setup} (u : Fin S.N_id) (j : Fin S.N_recv)
    (st : Sig1KeySimState S) :
    AllOut (sig1KeyTargetGenSpk S u j st) (fun x => Grow st.fg x.2.fg) := by
  unfold sig1KeyTargetGenSpk
  split
  · exact AllOut.pure_of (grow_refl st.fg)
  · split
    · split
      · exact AllOut.pure_of (grow_refl st.fg)
      · refine AllOut.bind_of (fun _ => AllOut.bind_of (fun _ =>
          AllOut.bind_of (fun _ => AllOut.bind_of (fun _ =>
          AllOut.bind_of (fun _ => AllOut.bind_of (fun _ => ?_))))))
        refine AllOut.pure_of ?_
        simp only [Grow, List.length_cons]; omega
    · exact AllOut.pure_of (grow_refl st.fg)

theorem sig1KeyActiveStep_grow {S : Setup} (K : Nat) (q : KeyIndQuery S)
    (st : Sig1KeyActiveSimState S) :
    AllOut (sig1KeyActiveStep S K q st) (fun x => Grow st.inner.fg x.2.inner.fg) := by
  unfold sig1KeyActiveStep
  split
  · exact AllOut.pure_of (grow_refl st.inner.fg)
  · have hDel : ∀ q', AllOut
        (do
          let (out, fg') ← embedGdhSigDdh
            (fgKeyIndStep false S.N_send_tot S.N_spk_tot S K [] st.inner.targetPk q' st.inner.fg)
          return (out, { st with inner := { st.inner with fg := fg' } }))
        (fun x => Grow st.inner.fg x.2.inner.fg) := by
      intro q' x hx
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨out, fg'⟩, hmem, rfl⟩
      exact AllOut_embedGdhSigDdh
        (fgKeyIndStep_grow false S.N_send_tot S.N_spk_tot K [] st.inner.targetPk q' st.inner.fg)
        (out, fg') hmem
    cases q with
    | initPrin u =>
      dsimp only
      split
      · exact AllOut.pure_of (grow_refl st.inner.fg)
      · refine AllOut.bind_of (fun _ => AllOut.bind_of (fun _ => ?_))
        refine AllOut.pure_of ?_
        simp only [Grow, List.length_cons]; omega
    | genSPK u j =>
      dsimp only
      split
      · intro x hx
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
        rcases hx with ⟨⟨out, inner'⟩, hmem, rfl⟩
        exact sig1KeyTargetGenSpk_grow u j st.inner (out, inner') hmem
      · exact hDel (.genSPK u j)
    | initiateOPK u i bundle =>
      dsimp only
      refine AllOut.bind_of (fun fg' => ?_)
      split
      · exact AllOut.pure_of (grow_refl st.inner.fg)
      · exact hDel (.initiateOPK u i bundle)
    | initiateNoOPK u i bundle =>
      dsimp only
      refine AllOut.bind_of (fun fg' => ?_)
      split
      · exact AllOut.pure_of (grow_refl st.inner.fg)
      · exact hDel (.initiateNoOPK u i bundle)
    | corruptIK u => exact hDel (.corruptIK u)
    | genOPK u j o => exact hDel (.genOPK u j o)
    | acceptOPK k j o hdr => exact hDel (.acceptOPK k j o hdr)
    | acceptNoOPK k j l hdr => exact hDel (.acceptNoOPK k j l hdr)
    | testSession sid => exact hDel (.testSession sid)
    | roQuery sec => exact hDel (.roQuery sec)
    | revealDhSecrets => exact hDel .revealDhSecrets
    | revealSessionKey sid => exact hDel (.revealSessionKey sid)
    | registerKey sk => exact hDel (.registerKey sk)
    | revealSpkSk u j => exact hDel (.revealSpkSk u j)

/-- Pointwise evaluation equivalence between `(sigKeyInd1KeyActiveDslProg S b).eval` and
    `(sigReductionKeyInd1KeyActive S b A).run`. -/
theorem sigKeyInd1KeyActiveDslProg_eval_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) (pk : Bytes) :
    (sigKeyInd1KeyActiveDslProg S b).eval (fun _ => A.1.run) pk =
      (sigReductionKeyInd1KeyActive S b A).run pk := by
  have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total := by
    obtain ⟨_, _, _, h, _⟩ := A.2
    convert h using 1
    funext q; cases q <;> rfl
  simp only [CostedReduction.eval, CostedReduction.impl, sigKeyInd1KeyActiveDslProg,
    sigReductionKeyInd1KeyActive, sigReductionKeyInd1KeyActiveRunAt, bindV, Comp.eval,
    s1Prim_eval, sIndex_eval, sBool_eval, emptySimE_eval (S := S),
    s1Mk, v, Expr.eval,
    SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
    SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
    SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
    SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
    bind_assoc, pure_bind]
  refine bind_congr fun k => bind_congr fun secb => ?_
  let n_id := activeIdCount S b.q_on
  let targetOrd := if n_id = 0 then b.q_total + 1 else k
  let initSt := Sig1KeyActiveSimState.empty S b secb targetOrd pk
  have hOrd : (if n_id = 0 then Expr.nat (O := pqxdhOps) (b.q_total + 1)
      else Expr.var Var.zero.succ).eval
      (.cons (t := .bool) secb (.cons (t := .nat) k
        (.cons (t := SignalPqxdh.LegacyCosted.B 32) pk .nil))) = targetOrd := by
    by_cases hn : n_id = 0 <;>
      simp [hn, targetOrd, Expr.eval]
  rw [hOrd]
  have hInitEnc :
      ((none : Option Nat),
        (simStateToVal (FgKeyIndSimState.empty S secb),
          (targetOrd, (pk, (activeSigBudget S b, (none : Option (Bytes × Bytes))))))) =
        sig1KeyActiveStToVal initSt := rfl
  rw [hInitEnc]
  refine simulateQ_handlerImpl_bind_eq_runWithSigDdhStep_bind
    (C := keyIndCodec S) (σ := sig1KeyActiveStTy) (α := Bool)
    (sig1KeyActiveHandleC S b.q_total) (sig1KeyActiveStep S b.q_total)
    sig1KeyActiveStToVal (fun n st => Inv b.q_total n st.inner.fg)
    (fun n st h => Inv.mono b.q_total n st.inner.fg h)
    (fun n q st h => ?_)
    (fun n q st h x hx =>
      Inv.of_grow b.q_total n st.inner.fg x.2.inner.fg h
        (sig1KeyActiveStep_grow b.q_total q st x hx))
    (fun p => pure ((eCaseOpt (s1Forgery (saInner (.var .zero)))
        (.pair (litB 1569 []) (litB 64 [])) fun fg => v fg).eval
      (.cons p.2 (.cons (t := .bool) p.1 .nil))))
    (fun p => pure (p.2.inner.forgery.getD ([], [])))
    (fun _ st _ => ?_)
    A.1.run b.q_total hA initSt (Inv.empty S b.q_total secb)
  · dsimp only [keyIndCodec, keyIndQueryToVal]
    rw [sig1KeyActiveHandleC_eval S b.q_total q st (Inv.bnd b.q_total (n + 1) st.inner.fg h)]
    simp only [encSig1KeyActiveRS, keyIndRespToVal, keyIndRdec_keyIndRenc,
      map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
  · rcases hfg : st.inner.forgery with _ | fgVal <;>
      simp [eCaseOpt, s1Forgery, saInner, sig1KeyActiveStToVal, sig1KeyStToVal, hfg,
        litB_eval, Expr.eval, v]

theorem pqxdhKeyInd1KeyActiveCostedSims_eval_sig_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (pqxdhKeyInd1KeyActiveCostedSims S).eval.sig b A = sigReductionKeyInd1KeyActive S b A := by
  dsimp only [KeyIndCostedReductionFamily.eval, pqxdhKeyInd1KeyActiveCostedSims]
  cases h : sigReductionKeyInd1KeyActive S b A with
  | mk run q_sig q_ddh q_prim =>
    have hq : q_sig = 2 * min S.N_spk_tot S.N_recv ∧ q_ddh = gdhQueryBudget S b ∧
        q_prim = gdhPrimQueryBudget S b := by
      injection h with _ h1 h2 h3
      exact ⟨h1.symm, h2.symm, h3.symm⟩
    have hrun :
        (fun pk => (sigKeyInd1KeyActiveAtomicProg S b).eval (fun _ => A.1.run) pk) = run := by
      funext pk
      rw [sigKeyInd1KeyActiveAtomicProg_eval_eq S b (fun _ => A.1.run) pk,
        sigKeyInd1KeyActiveDslProg_eval_eq S b A pk, h]
    rw [hq.1, hq.2.1, hq.2.2, hrun]

theorem gapSigEufCma_sigKeyInd1KeyActiveAtomicProg_eq (S : Setup) (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    GapSigEufCma P isValidDhTriple ((pqxdhKeyInd1KeyActiveCostedSims S).eval.sig b A) =
      GapSigEufCma P isValidDhTriple (sigReductionKeyInd1KeyActive S b A) := by
  rw [pqxdhKeyInd1KeyActiveCostedSims_eval_sig_eq]

/-- `GapSigEufCmaReal` advantage equality between `(pqxdhKeyInd1KeyActiveCostedSims S).eval.sig b A`
    and `sigReductionKeyInd1KeyActive S b A`. -/
theorem gapSigEufCmaReal_sigKeyInd1KeyActiveAtomicProg_eq (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    GapSigEufCmaReal P P.isValidDhTriple
      ((pqxdhKeyInd1KeyActiveCostedSims S).eval.sig b A) =
    GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1KeyActive S b A) :=
  congrArg ENNReal.toReal (gapSigEufCma_sigKeyInd1KeyActiveAtomicProg_eq S P P.isValidDhTriple b A)

end

end Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveSigEval
