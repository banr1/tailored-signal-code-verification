/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Auth.Headline
public import Computational.Specifications.Pqxdh.Security.CostedBudgets
public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyGapDh -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeySig -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK -- proof-setup: allow-public-import

/-!
# Shadow-Index One-Key `Auth` `GapDhWithSign` and `GapSigEufCma` Programs

Defines the kind-split shadow-indexed `CostedReduction` programs `a1g2KindProg` and
`a1s2KindProg` over `pqAtomicOps` and `pqAuthSigAndDdhIface` for the one-key `Auth`
`GapDhWithSign` and `GapSigEufCma` reductions. Pairs the atomic-lifted simulator state
with AVL random-oracle tables and sequence-indexed session shadow lists, clamping online
scans to `F.K_on` and random-oracle lookups to `O(log F.K_cap) + O(F.K_on)`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhK

open _root_.SignalPqxdh (Setup QueryBudget F_X25519 authSpec)
open _root_.SignalPqxdh.LegacyCosted (
  pqSig pqxdhOps pqPrimIface pqGapDhIface pqSigAndDdhIface gapDhDdhOracle sigAndDdhOracle
)
open _root_.SignalPqxdh.Costed (pqAuthSigAndDdhIface authCodec)
open _root_.SignalPqxdh.Security.ReductionDsl (
  authStateTy authRespTy drKeyTy fgPosTy fgPatchEntryTy authSessionEntryTy
)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (liftBase)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (liftGdhComp)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs (
  Ext v letV bindV caseOptV caseSumV findMV mapMV eAny eFind eMap eCaseOpt eCaseSum
  natEq nat2Eq nat3Eq sidEq optU32Eq isSomeE sendGuardE kyberCheckE firstMsgADE
  encEC encKEM slice32 bytesEmpty zero32 optFst optSnd
  stPrin stSpks stOpks stSess stUsedS stUsedO stUsedN stKyb stAdv stSecb stUpd
  peMk peSecIKA0 peIkAPk peSecIKAsign peCorrupted
  sbMk sbSpkSk sbSpkPk sbPqspkSk sbPqspkPk
  oeOpkSk oeOpkPk oeConsumed oeUpd
  buMk buIkB buSpkId buSpkB buSpkSig buOpkB buPqspkId buPqspkB buPqspkSig
  hdMk hdIkAPk hdEkAPk hdSpkId hdOpkId hdPqspkId hdKemCt
  pmHdr pmEphAPk pmPqMsg pmAeadCt seMk seEkASk sePeerSpk
  aNone aInitPrin aBundle aPk aSendFresh aSendUnfresh aRecvHonest aRecvUnfresh
  findHonestC resolveSigPkC corruptB genOpkB
  rootEntryTy fgSimTy patchKeyTy sendQTy recvQTy
  a1gParams2Ty gs2Ty a1g2StTy a1sStTy a1sRS
  fsBase fsL fsRootL fsRaw fsLog fsResp fsPows fsUpd
  pa2U pa2Role pa2Dh1
  pkP1 pkP2 pkP3 pkP4 pkSs feDk reRk rePos reRk1 reCk q4
  mkSecretPosC twoSideC twoSideOptC ddhEqC entryMatchesC
  koskBundleOkPowsC koskSenderOkPowsC lookupSpkSkC onBaseF fgRegisterC
  fgGenSpk2C a1gInitPrin2C a1gGenSpk2C
  logScan2C findMap2C initDh1Cand2C respCand2C
  a1g2InitDsl a1sCaseAPa2 a1sG a1sTp a1sTpk a1sFg a1sMk a1sBase
  a1sInit2Dsl
)
open _root_.ReductionDsl (Ty Var Expr Comp CostedReduction pqAtomicSig pqAtomicOps PB drKeyT bits)
open _root_.ReductionDsl.Expr (litBytes)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift (
  embedTy mapExpr exprRename mapComp compRename tlAuthSigDdh
  exprRename_cost exprRename_size mapExpr_size
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (
  aop avlTy avlEmptyE dfltB192E dfltPair32E dfltDrKeyE dfltPbytesPair32E
  avlSearchB192C avlSearchPair32C avlInsertAtPathC
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK (
  AuthKindFuels roAvlTy emptyRoAvlE wk1 liftExpr1 liftExpr2
  dispatchAuthQ authQueryAtomicTy authSendQAtomicTy authRecvQAtomicTy authRespAtomicTy
  aNoneAtomicE aDrKeyAtomicE aRootKdfAtomicE extractKC
)

@[reducible, expose] def seqFgEntryTy : Ty pqSig := .prod .nat fgPatchEntryTy
@[reducible, expose] def seqRootEntryTy : Ty pqSig := .prod .nat rootEntryTy
@[reducible, expose] def sessAuxLegTy : Ty pqSig :=
  .prod (.list seqFgEntryTy) (.prod .nat (.prod (.list seqRootEntryTy) .nat))

@[reducible, expose] def fgRoAvlTy : Ty pqAtomicSig :=
  avlTy (_root_.ReductionDsl.B 192) (.prod (drKeyT (ℓ := 0) (Pt := Empty)) .nat)

@[reducible, expose] def fgRootRoAvlTy : Ty pqAtomicSig :=
  avlTy (.prod (_root_.ReductionDsl.B 32) (_root_.ReductionDsl.B 32))
    (.prod (.prod (PB 32) (PB 32)) .nat)

@[reducible, expose] def rawAvlTy : Ty pqAtomicSig := roAvlTy

/-- Combined shadow auxiliary state
    `(fgSess, (fgCtr, (fgRoAvl, (fgRootSess, (fgRootCtr, (fgRootRoAvl, rawAvl))))))`. -/
@[reducible, expose] def fgAuthShadowAuxTy : Ty pqAtomicSig :=
  .prod (embedTy (.list seqFgEntryTy))
    (.prod .nat
      (.prod fgRoAvlTy
        (.prod (embedTy (.list seqRootEntryTy))
          (.prod .nat (.prod fgRootRoAvlTy rawAvlTy)))))

@[reducible, expose] def a1g2ShadowStTy : Ty pqAtomicSig :=
  .prod (embedTy a1g2StTy) fgAuthShadowAuxTy

@[reducible, expose] def a1s2ShadowStTy : Ty pqAtomicSig :=
  .prod (embedTy a1sStTy) fgAuthShadowAuxTy

@[reducible, expose] def fgCoreOutTy : Ty pqAtomicSig :=
  .prod authRespAtomicTy (.prod (.prod (embedTy fgSimTy) .nat) fgAuthShadowAuxTy)

@[reducible, expose] def auxFgSess (aux : fgAuthShadowAuxTy.denote) :
    (embedTy (.list seqFgEntryTy)).denote := aux.1
@[reducible, expose] def auxFgCtr (aux : fgAuthShadowAuxTy.denote) : ℕ := aux.2.1
@[reducible, expose] def auxFgRoAvl (aux : fgAuthShadowAuxTy.denote) :
    fgRoAvlTy.denote := aux.2.2.1
@[reducible, expose] def auxFgRootSess (aux : fgAuthShadowAuxTy.denote) :
    (embedTy (.list seqRootEntryTy)).denote := aux.2.2.2.1
@[reducible, expose] def auxFgRootCtr (aux : fgAuthShadowAuxTy.denote) : ℕ := aux.2.2.2.2.1
@[reducible, expose] def auxFgRootRoAvl (aux : fgAuthShadowAuxTy.denote) :
    fgRootRoAvlTy.denote := aux.2.2.2.2.2.1
@[reducible, expose] def auxRawAvl (aux : fgAuthShadowAuxTy.denote) :
    rawAvlTy.denote := aux.2.2.2.2.2.2

@[expose] def auxFgSessE {Γ : List (Ty pqAtomicSig)}
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy) :
    Expr pqAtomicOps Γ (embedTy (.list seqFgEntryTy)) := .fst auxE
@[expose] def auxFgCtrE {Γ : List (Ty pqAtomicSig)}
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy) :
    Expr pqAtomicOps Γ .nat := .fst (.snd auxE)
@[expose] def auxFgRoAvlE {Γ : List (Ty pqAtomicSig)}
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy) :
    Expr pqAtomicOps Γ fgRoAvlTy := .fst (.snd (.snd auxE))
@[expose] def auxFgRootSessE {Γ : List (Ty pqAtomicSig)}
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy) :
    Expr pqAtomicOps Γ (embedTy (.list seqRootEntryTy)) := .fst (.snd (.snd (.snd auxE)))
@[expose] def auxFgRootCtrE {Γ : List (Ty pqAtomicSig)}
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy) :
    Expr pqAtomicOps Γ .nat := .fst (.snd (.snd (.snd (.snd auxE))))
@[expose] def auxFgRootRoAvlE {Γ : List (Ty pqAtomicSig)}
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy) :
    Expr pqAtomicOps Γ fgRootRoAvlTy := .fst (.snd (.snd (.snd (.snd (.snd auxE)))))
@[expose] def auxRawAvlE {Γ : List (Ty pqAtomicSig)}
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy) :
    Expr pqAtomicOps Γ rawAvlTy := .snd (.snd (.snd (.snd (.snd (.snd auxE)))))

@[expose] def fgAuxMkE {Γ : List (Ty pqAtomicSig)}
    (fgSess : Expr pqAtomicOps Γ (embedTy (.list seqFgEntryTy)))
    (fgCtr : Expr pqAtomicOps Γ .nat)
    (fgRoAvl : Expr pqAtomicOps Γ fgRoAvlTy)
    (fgRootSess : Expr pqAtomicOps Γ (embedTy (.list seqRootEntryTy)))
    (fgRootCtr : Expr pqAtomicOps Γ .nat)
    (fgRootRoAvl : Expr pqAtomicOps Γ fgRootRoAvlTy)
    (rawAvl : Expr pqAtomicOps Γ rawAvlTy) :
    Expr pqAtomicOps Γ fgAuthShadowAuxTy :=
  .pair fgSess (.pair fgCtr (.pair fgRoAvl
    (.pair fgRootSess (.pair fgRootCtr (.pair fgRootRoAvl rawAvl)))))

@[expose] def auxSessSliceE {Γ : List (Ty pqAtomicSig)}
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy) :
    Expr pqAtomicOps Γ (embedTy sessAuxLegTy) :=
  .letE auxE (.pair (auxFgSessE .v0)
    (.pair (auxFgCtrE .v0) (.pair (auxFgRootSessE .v0) (auxFgRootCtrE .v0))))

@[expose] def auxPutSessSliceE {Γ : List (Ty pqAtomicSig)}
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy)
    (sauxE : Expr pqAtomicOps Γ (embedTy sessAuxLegTy)) :
    Expr pqAtomicOps Γ fgAuthShadowAuxTy :=
  .letE (.pair auxE sauxE)
    (fgAuxMkE (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (auxFgRoAvlE (.fst .v0))
      (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd .v0))))
      (auxFgRootRoAvlE (.fst .v0)) (auxRawAvlE (.fst .v0)))

@[expose] def emptyFgRoAvlE {Γ : List (Ty pqAtomicSig)} : Expr pqAtomicOps Γ fgRoAvlTy :=
  avlEmptyE dfltB192E (.pair dfltDrKeyE (.nat 0))

@[expose] def emptyFgRootRoAvlE {Γ : List (Ty pqAtomicSig)} : Expr pqAtomicOps Γ fgRootRoAvlTy :=
  avlEmptyE dfltPair32E (.pair dfltPbytesPair32E (.nat 0))

@[expose] def emptyFgAuthShadowAuxE {Γ : List (Ty pqAtomicSig)} :
    Expr pqAtomicOps Γ fgAuthShadowAuxTy :=
  fgAuxMkE .nil (.nat 0) emptyFgRoAvlE .nil (.nat 0) emptyFgRootRoAvlE emptyRoAvlE

@[expose] def wk0 {y : Ty pqAtomicSig} {Γ : List (Ty pqAtomicSig)} : Var [] y → Var Γ y :=
  fun v => nomatch v

@[expose] def liftCs0 {out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqSigAndDdhIface [] out) :
    Comp pqAtomicOps pqAuthSigAndDdhIface Γ (embedTy out) :=
  compRename wk0 (mapComp tlAuthSigDdh c)

@[expose] def liftCs1 {a out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqSigAndDdhIface [a] out)
    (argE : Expr pqAtomicOps Γ (embedTy a)) :
    Comp pqAtomicOps pqAuthSigAndDdhIface Γ (embedTy out) :=
  .bind (.ret argE) (compRename wk1 (mapComp tlAuthSigDdh c))

@[expose] def liftGdh0 {out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqGapDhIface [] out) :
    Comp pqAtomicOps pqAuthSigAndDdhIface Γ (embedTy out) :=
  liftCs0 (liftGdhComp c)

@[expose] def liftGdh1 {a out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqGapDhIface [a] out)
    (argE : Expr pqAtomicOps Γ (embedTy a)) :
    Comp pqAtomicOps pqAuthSigAndDdhIface Γ (embedTy out) :=
  liftCs1 (liftGdhComp c) argE

section LegacySubroutines

open _root_.SignalPqxdh.LegacyCosted (B)

@[reducible, expose] def saFgSess {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ sessAuxLegTy) :
    Expr pqxdhOps Γ (.list seqFgEntryTy) := .fst e
@[reducible, expose] def saFgCtr {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ sessAuxLegTy) :
    Expr pqxdhOps Γ .nat := .fst (.snd e)
@[reducible, expose] def saRootSess {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ sessAuxLegTy) :
    Expr pqxdhOps Γ (.list seqRootEntryTy) := .fst (.snd (.snd e))
@[reducible, expose] def saRootCtr {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ sessAuxLegTy) :
    Expr pqxdhOps Γ .nat := .snd (.snd (.snd e))

@[expose] def sampleRootPair64LegC :
    Comp pqxdhOps pqGapDhIface [] (.prod (B 32) (B 32)) :=
  bindV .sampleBytes32C fun rk1 =>
  bindV .sampleBytes32C fun ck1 =>
  .ret (.pair (v rk1) (v ck1))

/-- Shadow-maintaining `fgPatch` lookup and insertion bounded by `K_ro`. -/
@[expose] def patchWithShadowC (K_ro : ℕ) {Γ₁ Δ : List (Ty pqSig)}
    (k : Var Γ₁ patchKeyTy) [Ext Γ₁ Δ]
    (fgL : Expr pqxdhOps Δ (.list fgPatchEntryTy))
    (fgSess : Expr pqxdhOps Δ (.list seqFgEntryTy))
    (fgCtr : Expr pqxdhOps Δ .nat) :
    Comp pqxdhOps pqGapDhIface Δ
      (.prod drKeyTy (.prod (.list fgPatchEntryTy) (.prod (.list seqFgEntryTy) .nat))) :=
  letV (.pair fgL (.pair fgSess fgCtr)) fun st0 =>
  bindV (findMV K_ro (.fst (v st0)) fun e => entryMatchesC k e) fun f =>
  caseOptV (v f)
    (bindV .sampleDrKey96C fun dk =>
      letV (.pair (pkP1 (v k)) (.pair (pkP2 (v k)) (.pair (pkP3 (v k))
        (.pair (pkP4 (v k)) (.pair (pkSs (v k)) (v dk)))))) fun newE =>
      .ret (.pair (v dk)
        (.pair (.listCons (v newE) (.fst (v st0)))
          (.pair (.listCons (.pair (.snd (.snd (v st0))) (v newE)) (.fst (.snd (v st0))))
            (.add (.snd (.snd (v st0))) (.litNat 1))))))
    fun e =>
      .ret (.pair (feDk (v e)) (v st0))

/-- Shadow-maintaining `fgRootPatch` lookup and insertion bounded by `K_ro`. -/
@[expose] def rootPatchWithShadowC (K_ro : ℕ) {Δ : List (Ty pqSig)}
    (rk : Expr pqxdhOps Δ (B 32))
    (pos : Expr pqxdhOps Δ fgPosTy)
    (rootL : Expr pqxdhOps Δ (.list rootEntryTy))
    (rootSess : Expr pqxdhOps Δ (.list seqRootEntryTy))
    (rootCtr : Expr pqxdhOps Δ .nat) :
    Comp pqxdhOps pqGapDhIface Δ
      (.prod (.prod (B 32) (B 32))
        (.prod (.list rootEntryTy) (.prod (.list seqRootEntryTy) .nat))) :=
  letV (.pair rk (.pair pos (.pair rootL (.pair rootSess rootCtr)))) fun a =>
  bindV (findMV K_ro (.fst (.snd (.snd (v a)))) fun e =>
      .iteC (.boolNot (.bytesBeq (.fst (v a)) (reRk (v e)))) (.ret (.litBool false))
        (ddhEqC (.fst (.snd (v a))) (rePos (v e)))) fun f =>
  caseOptV (v f)
    (bindV .sampleBytes32C fun rk1 =>
     bindV .sampleBytes32C fun ck1 =>
     letV (.pair (.fst (v a)) (.pair (.fst (.snd (v a))) (.pair (v rk1) (v ck1)))) fun newRE =>
     .ret (.pair (.pair (v rk1) (v ck1))
       (.pair (.listCons (v newRE) (.fst (.snd (.snd (v a)))))
         (.pair (.listCons (.pair (.snd (.snd (.snd (.snd (v a))))) (v newRE))
             (.fst (.snd (.snd (.snd (v a))))))
           (.add (.snd (.snd (.snd (.snd (v a))))) (.litNat 1))))))
    fun e =>
      .ret (.pair (.pair (reRk1 (v e)) (reCk (v e))) (.snd (.snd (v a))))

/-- Parses an `.roQuery` input and canonicalizes its group elements via `mkSecretPosC`. -/
@[expose] def roParsedPrePosC :
    Comp pqxdhOps pqGapDhIface [B 192] (.opt patchKeyTy) :=
  let sec : Var [B 192] (B 192) := .vz
  .iteC (.boolAnd (.bytesBeq (.bytesTakeK 32 (v sec)) (litBytes 32 F_X25519))
      (.boolOr (natEq (.bytesLen (v sec)) (.litNat 160))
        (natEq (.bytesLen (v sec)) (.litNat 192))))
    (bindV (mkSecretPosC (slice32 32 (v sec))) fun p1 =>
     bindV (mkSecretPosC (slice32 64 (v sec))) fun p2 =>
     bindV (mkSecretPosC (slice32 96 (v sec))) fun p3 =>
     bindV (.iteC (natEq (.bytesLen (v sec)) (.litNat 192))
         (bindV (mkSecretPosC (slice32 128 (v sec))) fun p => .ret (.someE (v p)))
         (.ret .noneE))
       fun p4 =>
     letV (.pair (v p1) (.pair (v p2) (.pair (v p3) (.pair (v p4)
         (.ite (natEq (.bytesLen (v sec)) (.litNat 192)) (slice32 160 (v sec))
           (slice32 128 (v sec))))))) fun pk =>
     .ret (.someE (v pk)))
    (.ret .noneE)

/-- Bounded `K_on` scan of `fgSess` for entries with index at least `minIdx` matching `pk`. -/
@[expose] def fgSessScanC (K_on : ℕ) :
    Comp pqxdhOps pqGapDhIface [.prod patchKeyTy (.prod .nat (.list seqFgEntryTy))]
      (.opt seqFgEntryTy) :=
  let arg : Var [.prod patchKeyTy (.prod .nat (.list seqFgEntryTy))]
      (.prod patchKeyTy (.prod .nat (.list seqFgEntryTy))) := .vz
  letV (.fst (v arg)) fun pk =>
  letV (.fst (.snd (v arg))) fun minIdx =>
  findMV K_on (.snd (.snd (v arg))) fun se =>
    .ite (.lt (.fst (v se)) (v minIdx))
      (.ret (.litBool false))
      (letV (.snd (v se)) fun e => entryMatchesC pk e)

/-- Bounded `K_on` scan of `fgRootSess` for entries with index at least `minIdx` matching `(rk, pos)`. -/
@[expose] def rootSessScanC (K_on : ℕ) :
    Comp pqxdhOps pqGapDhIface
      [.prod (.prod (B 32) fgPosTy) (.prod .nat (.list seqRootEntryTy))]
      (.opt seqRootEntryTy) :=
  let arg : Var [.prod (.prod (B 32) fgPosTy) (.prod .nat (.list seqRootEntryTy))]
      (.prod (.prod (B 32) fgPosTy) (.prod .nat (.list seqRootEntryTy))) := .vz
  letV (.fst (.fst (v arg))) fun rk =>
  letV (.snd (.fst (v arg))) fun pos =>
  letV (.fst (.snd (v arg))) fun minIdx =>
  findMV K_on (.snd (.snd (v arg))) fun se =>
    .ite (.lt (.fst (v se)) (v minIdx))
      (.ret (.litBool false))
      (letV (.snd (v se)) fun e =>
        .iteC (.boolNot (.bytesBeq (v rk) (reRk (v e)))) (.ret (.litBool false))
          (ddhEqC (v pos) (rePos (v e))))

/-- Shadow-maintaining `fgSend2C` with clamped fuels and shadow rollback on abort. -/
@[expose] def fgSend2ShadowC (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    Comp pqxdhOps pqGapDhIface
      [.prod a1gParams2Ty (.prod fgSimTy (.prod sessAuxLegTy sendQTy))]
      (.prod authRespTy (.prod fgSimTy sessAuxLegTy)) :=
  let inp : Var [.prod a1gParams2Ty (.prod fgSimTy (.prod sessAuxLegTy sendQTy))]
      (.prod a1gParams2Ty (.prod fgSimTy (.prod sessAuxLegTy sendQTy))) := .vz
  letV (.fst (v inp)) fun pa =>
  letV (.fst (.snd (v inp))) fun sim =>
  letV (.fst (.snd (.snd (v inp)))) fun saux =>
  letV (.snd (.snd (.snd (v inp)))) fun x =>
  .iteC (sendGuardE opk (v x)) (.ret (.pair aNone (.pair (v sim) (v saux)))) <|
  letV (fsBase (v sim)) fun st => letV (fsPows (v sim)) fun pows =>
  letV (.fst (.snd (.snd (v x)))) fun bu =>
  letV (.fst (.snd (.snd (.snd (v x))))) fun m0 =>
  letV (.snd (.snd (.snd (.snd (v x))))) fun m1 =>
  letV (if opk then .inl (.pair (.fst (v x)) (.fst (.snd (v x))))
    else .inr (.inl (.pair (.fst (v x)) (.fst (.snd (v x)))))) fun sid =>
  .iteC (.boolNot (natEq (.bytesLen (v m0)) (.bytesLen (v m1))))
    (.ret (.pair aNone (.pair (v sim) (v saux)))) <|
  .iteC (eAny F.K_on (stUsedS (v st)) fun e => sidEq (v e) (v sid))
    (.ret (.pair aNone (.pair (v sim) (v saux)))) <|
  caseOptV (eFind F.K_on (stPrin (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (.pair aNone (.pair (v sim) (v saux)))) fun uE =>
  bindV (Comp.liftChal (C := gapDhDdhOracle) (findHonestC S F.K_on st (buIkB (v bu)))) fun pp =>
  letV (eCaseOpt (v pp) (.litBool false) fun p => .boolNot (peCorrupted (.snd (v p))))
    fun fresh =>
  .iteC (.boolAnd (.boolNot (v fresh)) (.boolNot (.bytesBeq (v m0) (v m1))))
    (.ret (.pair aNone (.pair (v sim) (v saux)))) <|
  bindV (Comp.liftChal (C := gapDhDdhOracle) (koskBundleOkPowsC S F.K_on st pows bu)) fun ok =>
  .iteC (.boolNot (v ok)) (.ret (.pair aNone (.pair (v sim) (v saux)))) <|
  letV (eCaseSum (pa2Role (v pa)) (fun _ => .litBool false) fun s =>
      eCaseSum (v s)
        (fun p => if opk then nat2Eq (.pair (.fst (v x)) (.fst (.snd (v x)))) (v p) else .litBool false)
        (fun p => if opk then .litBool false else nat2Eq (.pair (.fst (v x)) (.fst (.snd (v x)))) (v p)))
    fun isT =>
  bindV .sampleBytes32C fun ekRaw =>
  bindV .sampleBytes32C fun coins =>
  bindV .sampleBytes32C fun ephSk =>
  bindV .sampleBytes32C fun spqrCoins =>
  bindV (Comp.liftChal (C := gapDhDdhOracle) (resolveSigPkC S F.K_on st (buIkB (v bu)))) fun spk =>
  bindV (.queryPrimC (.sigVerify 33)
      (.pair (v spk) (.pair (encEC (buSpkB (v bu))) (buSpkSig (v bu)))))
    fun v1 =>
  bindV (.queryPrimC (.sigVerify 1569)
      (.pair (v spk) (.pair (encKEM (buPqspkB (v bu))) (buPqspkSig (v bu)))))
    fun v2 =>
  .iteC (.boolNot (.boolAnd (v v1) (v v2))) (.ret (.pair aNone (.pair (v sim) (v saux)))) <|
  bindV (.queryPrimC .kemEncaps (.pair (buPqspkB (v bu)) (v coins))) fun enc =>
  caseOptV (v enc) (.ret (.pair aNone (.pair (v sim) (v saux)))) fun sc =>
  bindV (.queryPrimC .x25519Base (v ekRaw)) fun ekPkRaw =>
  letV (.ite (v isT) (litBytes 32 []) (v ekRaw)) fun ekSk =>
  letV (.ite (v isT) (pa2U (v pa)) (v ekPkRaw)) fun ekPk =>
  bindV (Comp.liftChal (C := gapDhDdhOracle) (lookupSpkSkC S F.K_on st pows (buSpkB (v bu))))
    fun spkSk =>
  bindV (twoSideC (q4 (peSecIKA0 (.snd (v uE))) (v spkSk)
      (peIkAPk (.snd (v uE))) (buSpkB (v bu))))
    fun p1 =>
  bindV (twoSideC (q4 (v ekSk) (litBytes 32 []) (v ekPk) (buIkB (v bu)))) fun p2 =>
  bindV (twoSideC (q4 (v ekSk) (litBytes 32 []) (v ekPk) (buSpkB (v bu)))) fun p3 =>
  bindV (twoSideOptC (eCaseOpt (buOpkB (v bu)) .noneE fun o =>
      .someE (q4 (v ekSk) (litBytes 32 []) (v ekPk) (.snd (v o))))) fun p4 =>
  letV (.pair (v p1) (.pair (v p2) (.pair (v p3) (.pair (v p4) (.fst (v sc)))))) fun pk =>
  bindV (patchWithShadowC F.K_ro pk (fsL (v sim)) (saFgSess (v saux)) (saFgCtr (v saux))) fun dr =>
  bindV (.queryPrimC .x25519Base (v ephSk)) fun ephPk =>
  bindV (.queryPrimC .x25519 (.pair (v ephSk) (buSpkB (v bu)))) fun dhR =>
  bindV (mkSecretPosC (v dhR)) fun posR =>
  bindV (rootPatchWithShadowC F.K_ro (.fst (.fst (v dr))) (v posR)
      (fsRootL (v sim)) (saRootSess (v saux)) (saRootCtr (v saux))) fun rkOut =>
  bindV (.queryPrimC .chainKdfSeed (.snd (.fst (v rkOut)))) fun mkSeed =>
  bindV (.queryPrimC .chainKdfNext (.snd (.fst (v rkOut)))) fun ck11 =>
  bindV (.queryPrimC (.spqrInitSend 32 32)
      (.pair (.snd (.snd (.fst (v dr)))) (v spqrCoins))) fun sp? =>
  caseOptV (v sp?) (.ret (.pair aNone (.pair (v sim) (v saux)))) fun sp =>
  bindV (.queryPrimC (.deriveMsgKeys 32) (.pair (v mkSeed) (.fst (.snd (v sp))))) fun mk =>
  letV (firstMsgADE (peIkAPk (.snd (v uE))) (buIkB (v bu)) (v ephPk) (.snd (.snd (v sp))))
    fun ad =>
  bindV (.queryPrimC (.aeadEnc 158 32 32) (.pair (v mk) (.pair (v ad)
      (.ite (v fresh) (.ite (stSecb (v st)) (v m1) (v m0)) (v m0))))) fun ct =>
  letV (.pair (hdMk (peIkAPk (.snd (v uE))) (v ekPk) (buSpkId (v bu)) (optFst (buOpkB (v bu)))
      (buPqspkId (v bu)) (.snd (v sc))) (.pair (v ephPk) (.pair (.snd (.snd (v sp))) (v ct))))
    fun wm =>
  letV (eCaseOpt (v pp) (.pair (.litBool false) (.litBool false)) fun p =>
      .pair (eAny F.K_on (stSpks (v st)) fun b => .boolAnd (natEq (.fst (.fst (v b))) (.fst (v p)))
          (.bytesBeq (sbSpkPk (.snd (v b))) (buSpkB (v bu))))
        (eAny F.K_on (stSpks (v st)) fun b => .boolAnd (natEq (.fst (.fst (v b))) (.fst (v p)))
          (.bytesBeq (sbPqspkPk (.snd (v b))) (buPqspkB (v bu))))) fun hon =>
  letV (seMk (v sid) (buIkB (v bu)) (buSpkB (v bu)) (optSnd (buOpkB (v bu))) (buPqspkB (v bu))
      (.fst (v hon)) (.litBool false) (.snd (v hon)) (v ekSk) (v ephSk) (v fresh)
      (.boolAnd (v fresh) (.boolNot (.bytesBeq (v m0) (v m1))))) fun se =>
  .ret (.pair (eCaseOpt (v pp)
      (aSendUnfresh (.fst (v dr)) (.fst (.fst (v rkOut))) (v ck11) (v wm))
      fun _ => aSendFresh (v wm))
    (.pair
      (fsUpd (v sim) (base := stUpd (v st) (sess := .listCons (v se) (stSess (v st)))
          (usedS := .listCons (v sid) (stUsedS (v st))))
        (fgL := .fst (.snd (v dr))) (rootL := .fst (.snd (v rkOut))))
      (.pair (.fst (.snd (.snd (v dr))))
        (.pair (.snd (.snd (.snd (v dr)))) (.snd (.snd (v rkOut)))))))

/-- Shadow-maintaining `fgRecvC` with clamped fuels and shadow rollback on abort. -/
@[expose] def fgRecvShadowC (S : Setup) (F : AuthKindFuels) (opk : Bool) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (sim : Var Γ₁ fgSimTy) (saux : Var Γ₂ sessAuxLegTy) (x : Var Γ₃ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    Comp pqxdhOps pqGapDhIface Δ (.prod authRespTy (.prod fgSimTy sessAuxLegTy)) :=
  letV (fsBase (v sim)) fun st => letV (fsPows (v sim)) fun pows =>
  letV (.snd (.snd (.snd (v x)))) fun msg =>
  letV (pmHdr (v msg)) fun hdr =>
  letV (.pair (.fst (v x)) (.pair (.fst (.snd (v x))) (.fst (.snd (.snd (v x)))))) fun kjo =>
  .iteC (.boolNot (.boolAnd (.boolAnd (.boolAnd (.boolAnd (.boolAnd
      (.u32Beq (hdSpkId (v hdr)) (.u32OfNat (.fst (.snd (v x)))))
      (.u32Beq (hdPqspkId (v hdr)) (.u32OfNat (.fst (.snd (v x))))))
      (optU32Eq (hdOpkId (v hdr))
        (if opk then .someE (.u32OfNat (.fst (.snd (.snd (v x))))) else .noneE)))
      (natEq (.bytesLen (hdIkAPk (v hdr))) (.litNat 32)))
      (natEq (.bytesLen (hdEkAPk (v hdr))) (.litNat 32)))
      (natEq (.bytesLen (pmEphAPk (v msg))) (.litNat 32))))
    (.ret (.pair aNone (.pair (v sim) (v saux)))) <|
  .iteC (eAny F.K_on (if opk then stUsedO (v st) else stUsedN (v st)) fun e => nat3Eq (v e) (v kjo))
    (.ret (.pair aNone (.pair (v sim) (v saux)))) <|
  bindV (Comp.liftChal (C := gapDhDdhOracle)
      (koskSenderOkPowsC S F.K_on st pows (hdIkAPk (v hdr))))
    fun ok =>
  .iteC (.boolNot (v ok)) (.ret (.pair aNone (.pair (v sim) (v saux)))) <|
  caseOptV (eFind F.K_on (stPrin (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (.pair aNone (.pair (v sim) (v saux)))) fun kE =>
  caseOptV (eFind F.K_on (stSpks (v st)) fun e =>
      nat2Eq (.fst (v e)) (.pair (.fst (v x)) (.fst (.snd (v x)))))
    (.ret (.pair aNone (.pair (v sim) (v saux)))) fun bE =>
  bindV (if opk then
      caseOptV (eFind F.K_on (stOpks (v st)) fun e => nat3Eq (.fst (v e)) (v kjo))
          (.ret .noneE) fun oE =>
        .ret (.ite (oeConsumed (.snd (v oE))) .noneE
          (.someE (.someE (.pair (oeOpkSk (.snd (v oE))) (oeOpkPk (.snd (v oE)))))))
    else .ret (.someE .noneE)) fun oChk =>
  caseOptV (v oChk) (.ret (.pair aNone (.pair (v sim) (v saux)))) fun oKey =>
  letV (kyberCheckE F.K_on (stKyb (v st)) (.pair (.fst (v x)) (.pair (hdPqspkId (v hdr))
      (.pair (hdSpkId (v hdr)) (hdEkAPk (v hdr)))))) fun kc =>
  bindV (.queryPrimC .isCanonical (hdEkAPk (v hdr))) fun can =>
  bindV (.queryPrimC .isCanonical (pmEphAPk (v msg))) fun canE =>
  .iteC (.boolOr (.boolOr (.boolNot (.fst (v kc))) (.boolNot (v can))) (.boolNot (v canE)))
    (.ret (.pair aNone (.pair (v sim) (v saux)))) <|
  bindV (.queryPrimC .kemDecaps (.pair (sbPqspkSk (.snd (v bE))) (hdKemCt (v hdr)))) fun ss? =>
  caseOptV (v ss?) (.ret (.pair aNone (.pair (v sim) (v saux)))) fun ss =>
  bindV (twoSideOptC (eCaseOpt (v oKey) .noneE fun o =>
      .someE (q4 (litBytes 32 []) (.fst (v o)) (hdEkAPk (v hdr)) (.snd (v o))))) fun p4 =>
  letV (.snd (v kE)) fun kE' => letV (.snd (v bE)) fun bE' =>
  bindV (twoSideC (q4 (litBytes 32 []) (sbSpkSk (v bE'))
      (hdIkAPk (v hdr)) (sbSpkPk (v bE')))) fun p1 =>
  bindV (twoSideC (q4 (litBytes 32 []) (peSecIKA0 (v kE'))
      (hdEkAPk (v hdr)) (peIkAPk (v kE')))) fun p2 =>
  bindV (twoSideC (q4 (litBytes 32 []) (sbSpkSk (v bE'))
      (hdEkAPk (v hdr)) (sbSpkPk (v bE')))) fun p3 =>
  letV (.pair (v p1) (.pair (v p2) (.pair (v p3) (.pair (v p4) (v ss))))) fun pk =>
  bindV (patchWithShadowC F.K_ro pk (fsL (v sim)) (saFgSess (v saux)) (saFgCtr (v saux))) fun dkL =>
  bindV (twoSideC (q4 (litBytes 32 []) (sbSpkSk (v bE')) (pmEphAPk (v msg)) (sbSpkPk (v bE'))))
    fun posR =>
  bindV (rootPatchWithShadowC F.K_ro (.fst (.fst (v dkL))) (v posR)
      (fsRootL (v sim)) (saRootSess (v saux)) (saRootCtr (v saux))) fun rkOut =>
  bindV (.queryPrimC .chainKdfSeed (.snd (.fst (v rkOut)))) fun mkSeed =>
  bindV (.queryPrimC .chainKdfNext (.snd (.fst (v rkOut)))) fun ck11 =>
  bindV (.queryPrimC (.spqrInitRecv 32 32) (.pair (.snd (.snd (.fst (v dkL)))) (pmPqMsg (v msg))))
    fun sp? =>
  caseOptV (v sp?) (.ret (.pair aNone (.pair (v sim) (v saux)))) fun sp =>
  bindV (.queryPrimC (.deriveMsgKeys 32) (.pair (v mkSeed) (.snd (v sp)))) fun mk =>
  bindV (.queryPrimC (.aeadDec 158 32 32) (.pair (v mk)
      (.pair (firstMsgADE (hdIkAPk (v hdr)) (peIkAPk (v kE'))
      (pmEphAPk (v msg)) (pmPqMsg (v msg))) (pmAeadCt (v msg))))) fun pt? =>
  caseOptV (v pt?) (.ret (.pair aNone (.pair (v sim) (v saux)))) fun pt =>
  bindV (Comp.liftChal (C := gapDhDdhOracle) (findHonestC S F.K_on st (hdIkAPk (v hdr)))) fun snd? =>
  letV (if opk then
      stUpd (v st)
        (opks := eMap F.K_on (stOpks (v st)) fun e =>
          .ite (nat3Eq (.fst (v e)) (v kjo))
            (.pair (.fst (v e)) (oeUpd (.snd (v e)) (consumed := .litBool true))) (v e))
        (usedO := .listCons (v kjo) (stUsedO (v st))) (kyb := .snd (v kc))
    else
      stUpd (v st) (usedN := .listCons (v kjo) (stUsedN (v st))) (kyb := .snd (v kc))) fun st' =>
  .ret (.pair (eCaseOpt (v snd?)
      (aRecvUnfresh (.fst (v dkL)) (.fst (.fst (v rkOut))) (v ck11) (v pt))
      fun _ => aRecvHonest)
    (.pair
      (fsUpd (v sim) (base := v st')
        (fgL := .fst (.snd (v dkL))) (rootL := .fst (.snd (v rkOut))))
      (.pair (.fst (.snd (.snd (v dkL))))
        (.pair (.snd (.snd (.snd (v dkL)))) (.snd (.snd (v rkOut)))))))

@[expose] def fgRecvShadowB (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    Comp pqxdhOps pqGapDhIface
      [.prod fgSimTy (.prod sessAuxLegTy recvQTy)]
      (.prod authRespTy (.prod fgSimTy sessAuxLegTy)) :=
  let inp : Var [.prod fgSimTy (.prod sessAuxLegTy recvQTy)]
      (.prod fgSimTy (.prod sessAuxLegTy recvQTy)) := .vz
  letV (.fst (v inp)) fun sim =>
  letV (.fst (.snd (v inp))) fun saux =>
  letV (.snd (.snd (v inp))) fun x =>
  letV (fsUpd (v sim) (resp := .listCons (.pair (.pair (.fst (v x)) (.fst (.snd (v x))))
      (.pair (hdIkAPk (pmHdr (.snd (.snd (.snd (v x))))))
        (hdEkAPk (pmHdr (.snd (.snd (.snd (v x))))))))
      (fsResp (v sim)))) fun sim' =>
  fgRecvShadowC S F opk sim' saux x

@[expose] def a1gInitPrin2LegC (F : AuthKindFuels) :
    Comp pqxdhOps pqGapDhIface [.prod a1gParams2Ty (.prod fgSimTy .nat)]
      (.prod authRespTy fgSimTy) :=
  let inp : Var [.prod a1gParams2Ty (.prod fgSimTy .nat)]
      (.prod a1gParams2Ty (.prod fgSimTy .nat)) := .vz
  letV (.fst (v inp)) fun pa =>
  letV (.fst (.snd (v inp))) fun sim =>
  letV (.snd (.snd (v inp))) fun u =>
  a1gInitPrin2C F.K_on pa sim u

@[expose] def fgCorruptLegC (F : AuthKindFuels) :
    Comp pqxdhOps pqGapDhIface [.prod fgSimTy .nat] (.prod authRespTy fgSimTy) :=
  let inp : Var [.prod fgSimTy .nat] (.prod fgSimTy .nat) := .vz
  letV (.fst (v inp)) fun sim =>
  letV (.snd (v inp)) fun u =>
  onBaseF sim fun g => corruptB F.K_on g u

@[expose] def a1gGenSpk2LegC (F : AuthKindFuels) :
    Comp pqxdhOps pqSigAndDdhIface
      [.prod a1gParams2Ty (.prod fgSimTy (.prod .nat (.prod .nat .nat)))]
      (.prod authRespTy (.prod fgSimTy .nat)) :=
  let inp : Var [.prod a1gParams2Ty (.prod fgSimTy (.prod .nat (.prod .nat .nat)))]
      (.prod a1gParams2Ty (.prod fgSimTy (.prod .nat (.prod .nat .nat)))) := .vz
  letV (.fst (v inp)) fun pa =>
  letV (.fst (.snd (v inp))) fun sim =>
  letV (.fst (.snd (.snd (v inp)))) fun sigB =>
  letV (.snd (.snd (.snd (v inp)))) fun x =>
  .iteC (eCaseSum (pa2Role (v pa)) (fun uT => natEq (.fst (v x)) (v uT)) (fun _ => .litBool false))
    (a1gGenSpk2C F.K_on pa sim sigB x)
    (bindV (liftGdhComp (fgGenSpk2C F.K_on pa sim x)) fun r =>
      .ret (.pair (.fst (v r)) (.pair (.snd (v r)) (v sigB))))

@[expose] def fgGenOpkLegC (F : AuthKindFuels) :
    Comp pqxdhOps pqGapDhIface
      [.prod fgSimTy (.prod .nat (.prod .nat .nat))]
      (.prod authRespTy fgSimTy) :=
  let inp : Var [.prod fgSimTy (.prod .nat (.prod .nat .nat))]
      (.prod fgSimTy (.prod .nat (.prod .nat .nat))) := .vz
  letV (.fst (v inp)) fun sim =>
  letV (.snd (v inp)) fun x =>
  onBaseF sim fun g => genOpkB F.K_on g x

@[expose] def fgRegisterLegC :
    Comp pqxdhOps pqGapDhIface [.prod fgSimTy (B 32)] (.prod authRespTy fgSimTy) :=
  let inp : Var [.prod fgSimTy (B 32)] (.prod fgSimTy (B 32)) := .vz
  letV (.fst (v inp)) fun sim =>
  letV (.snd (v inp)) fun sk =>
  fgRegisterC sim sk

@[expose] def a1sSendCheckLegC (S : Setup) (F : AuthKindFuels) :
    Comp pqxdhOps pqSigAndDdhIface [.prod a1sStTy sendQTy] (.sum a1sRS .unit) :=
  let inp : Var [.prod a1sStTy sendQTy] (.prod a1sStTy sendQTy) := .vz
  letV (.fst (v inp)) fun s =>
  letV (.snd (v inp)) fun x =>
  letV (a1sTp (v s)) fun tp =>
  letV (a1sTpk (v s)) fun tpk =>
  letV (a1sBase (v s)) fun st =>
  letV (.fst (.snd (.snd (v x)))) fun bu =>
  bindV (liftBase (C := sigAndDdhOracle) (extractKC S F tp tpk st bu)) fun fg =>
  .iteC (isSomeE (v fg))
    (.ret (.inl (.pair aNone (a1sMk (a1sG (v s)) (a1sTp (v s)) (a1sTpk (v s)) (v fg)))))
    (.ret (.inr .litUnit))

/-- Clamped end-of-game CDH candidate extraction under `F`. -/
@[expose] def fgExtract2K (S : Setup) (F : AuthKindFuels) :
    Comp pqxdhOps pqGapDhIface [gs2Ty] (B 32) :=
  let gst : Var [gs2Ty] gs2Ty := .vz
  letV (.fst (v gst)) fun pa =>
  letV (.snd (v gst)) fun sim =>
  .iteC (pa2Dh1 (v pa))
    (bindV (logScan2C F.M_off pa sim 32) fun f =>
     caseOptV (v f)
       (bindV (mapMV F.M_dh (stSpks (fsBase (v sim))) fun e =>
           bindV (.queryPrimC .pow8 (sbSpkPk (.snd (v e)))) fun w =>
           .ret (.pair (sbSpkSk (.snd (v e))) (v w))) fun spkPows =>
        bindV (findMap2C pa F.M_dh (stSess (fsBase (v sim)))
            fun s => initDh1Cand2C S F.K_on sim spkPows s)
          fun f2 =>
        caseOptV (v f2)
          (bindV (findMap2C pa F.M_sess (fsResp (v sim)) fun r =>
              respCand2C S F.K_on sim r (.fst (.snd (v r)))) fun f3 =>
           .ret (eCaseOpt (v f3) zero32 fun z => v z))
          fun z => .ret (v z))
       fun z => .ret (v z))
    (bindV (logScan2C F.M_off pa sim 96) fun f =>
     caseOptV (v f)
       (bindV (findMap2C pa F.M_dh (stSess (fsBase (v sim))) fun s =>
           .iteC (bytesEmpty (seEkASk (v s))) (.ret zero32)
             (.queryPrimC .x25519 (.pair (seEkASk (v s)) (sePeerSpk (v s))))) fun f2 =>
        caseOptV (v f2)
          (bindV (findMap2C pa F.M_sess (fsResp (v sim)) fun r =>
              respCand2C S F.K_on sim r (.snd (.snd (v r)))) fun f3 =>
           .ret (eCaseOpt (v f3) zero32 fun z => v z))
          fun z => .ret (v z))
       fun z => .ret (v z))

end LegacySubroutines

section AtomicArms

/-- Target-principal corruption halt guard bounded by `K_on`. -/
@[expose] def a1gHaltGuard2E (K_on : ℕ) {Γ : List (Ty pqAtomicSig)}
    (paE : Expr pqAtomicOps Γ (embedTy a1gParams2Ty))
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy)) :
    Expr pqAtomicOps Γ .bool :=
  let pa  : Var [a1gParams2Ty, fgSimTy] a1gParams2Ty := .vz
  let sim : Var [a1gParams2Ty, fgSimTy] fgSimTy := .vs .vz
  liftExpr2
    (eCaseSum (pa2Role (v pa))
      (fun uT =>
        eCaseOpt (eFind K_on (stPrin (fsBase (v sim))) fun e => natEq (.fst (v e)) (v uT))
          (.litBool false) fun e => peCorrupted (.snd (v e)))
      (fun _ => .litBool false))
    paE simE

@[expose] def simPrependLogE {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (secE : Expr pqAtomicOps Γ (PB 192)) :
    Expr pqAtomicOps Γ (embedTy fgSimTy) :=
  liftExpr2
    (fsUpd (.var .vz) (log := .listCons (.var (.vs .vz)) (fsLog (.var .vz))))
    simE secE

@[expose] def simPrependRawAndLogE {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (secDkE : Expr pqAtomicOps Γ (.prod (PB 192) (drKeyT (ℓ := 0) (Pt := Empty)))) :
    Expr pqAtomicOps Γ (embedTy fgSimTy) :=
  liftExpr2
    (fsUpd (.var .vz)
      (raw := .listCons (.var (.vs .vz)) (fsRaw (.var .vz)))
      (log := .listCons (.fst (.var (.vs .vz))) (fsLog (.var .vz))))
    simE secDkE

@[expose] def simPrependFgAndLogE {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (pkSecDkE : Expr pqAtomicOps Γ
      (.prod (embedTy patchKeyTy) (.prod (PB 192) (drKeyT (ℓ := 0) (Pt := Empty))))) :
    Expr pqAtomicOps Γ (embedTy fgSimTy) :=
  liftExpr2
    (let pk := Expr.fst (.var (.vs .vz))
     let sec := Expr.fst (.snd (.var (.vs .vz)))
     let dk := Expr.snd (.snd (.var (.vs .vz)))
     let newE := Expr.pair (pkP1 pk) (.pair (pkP2 pk) (.pair (pkP3 pk)
       (.pair (pkP4 pk) (.pair (pkSs pk) dk))))
     fsUpd (.var .vz)
       (fgL := .listCons newE (fsL (.var .vz)))
       (log := .listCons sec (fsLog (.var .vz))))
    simE pkSecDkE

@[expose] def simPrependRootE {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (newReE : Expr pqAtomicOps Γ (embedTy rootEntryTy)) :
    Expr pqAtomicOps Γ (embedTy fgSimTy) :=
  liftExpr2
    (fsUpd (.var .vz) (rootL := .listCons (.var (.vs .vz)) (fsRootL (.var .vz))))
    simE newReE

@[expose] def fgCoreArm_roQuery (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy)
    (secE : Expr pqAtomicOps Γ (PB 192)) :
    Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy :=
  .bind (.ret (.pair simE (.pair sigBE (.pair auxE (.pair secE (aop (.pbytesToBytes 192) secE))))))
    (.bind (liftGdh1 roParsedPrePosC (.fst (.snd (.snd (.snd .v0)))))
      (.caseOpt .v0
        (.bind (avlSearchB192C F.K_cap
            (auxRawAvlE (.fst (.snd (.snd .v1))))
            (.snd (.snd (.snd (.snd .v1)))))
          (.caseOpt (.fst .v0)
            (.bind (liftGdh0 .sampleDrKey96C)
              (.bind (avlInsertAtPathC F.K_cap
                  (auxRawAvlE (.fst (.snd (.snd .v3))))
                  (.snd .v1)
                  (.snd (.snd (.snd (.snd .v3))))
                  .v0)
                (.ret (.pair (aDrKeyAtomicE .v1)
                  (.pair
                    (.pair
                      (simPrependRawAndLogE (.fst .v4)
                        (.pair (.fst (.snd (.snd (.snd .v4)))) .v1))
                      (.fst (.snd .v4)))
                    (let aux4 := Expr.fst (.snd (.snd .v4))
                     fgAuxMkE (auxFgSessE aux4) (auxFgCtrE aux4) (auxFgRoAvlE aux4)
                       (auxFgRootSessE aux4) (auxFgRootCtrE aux4) (auxFgRootRoAvlE aux4) .v0))))))
            (.ret (.pair (aDrKeyAtomicE .v0)
              (.pair
                (.pair (simPrependLogE (.fst .v3) (.fst (.snd (.snd (.snd .v3)))))
                  (.fst (.snd .v3)))
                (.fst (.snd (.snd .v3))))))))
        (.bind (avlSearchB192C F.K_cap
            (auxFgRoAvlE (.fst (.snd (.snd .v2))))
            (.snd (.snd (.snd (.snd .v2)))))
          (.bind
            (let minIdxE := Expr.caseOpt (.fst .v0) (.nat 0) (.add (.snd .v0) (.nat 1))
             liftGdh1 (fgSessScanC F.K_on)
               (.pair .v1 (.pair minIdxE (auxFgSessE (.fst (.snd (.snd .v3)))))))
            (.caseOpt .v0
              (.caseOpt (.fst .v1)
                (.bind (liftGdh0 .sampleDrKey96C)
                  (.bind (avlInsertAtPathC F.K_cap
                      (auxFgRoAvlE (.fst (.snd (.snd .v5))))
                      (.snd .v2)
                      (.snd (.snd (.snd (.snd .v5))))
                      (.pair .v0 (auxFgCtrE (.fst (.snd (.snd .v5))))))
                    (let tup6 := Expr.var (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))
                     .ret (.pair (aDrKeyAtomicE .v1)
                       (.pair
                         (.pair
                           (simPrependFgAndLogE (.fst tup6)
                             (.pair .v4 (.pair (.fst (.snd (.snd (.snd tup6)))) .v1)))
                           (.fst (.snd tup6)))
                         (let aux6 := Expr.fst (.snd (.snd tup6))
                          fgAuxMkE (auxFgSessE aux6) (.add (auxFgCtrE aux6) (.nat 1)) .v0
                            (auxFgRootSessE aux6) (auxFgRootCtrE aux6)
                            (auxFgRootRoAvlE aux6) (auxRawAvlE aux6)))))))
                (.ret (.pair (aDrKeyAtomicE (.fst .v0))
                  (.pair
                    (.pair (simPrependLogE (.fst .v5) (.fst (.snd (.snd (.snd .v5)))))
                      (.fst (.snd .v5)))
                    (.fst (.snd (.snd .v5)))))))
              (.ret (.pair (aDrKeyAtomicE (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))
                (.pair
                  (.pair (simPrependLogE (.fst .v5) (.fst (.snd (.snd (.snd .v5)))))
                    (.fst (.snd .v5)))
                  (.fst (.snd (.snd .v5)))))))))))

@[expose] def fgCoreArm_roRootQuery (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy :=
  let keyPairE : Expr pqAtomicOps Γ (.prod (_root_.ReductionDsl.B 32) (_root_.ReductionDsl.B 32)) :=
    .letE inpE (.pair (aop (.pbytesToBytes 32) (.fst .v0)) (aop (.pbytesToBytes 32) (.snd .v0)))
  .bind (.ret (.pair simE (.pair sigBE (.pair auxE (.pair inpE keyPairE)))))
    (.bind (liftGdh1 (mkSecretPosC (.var .vz)) (.snd (.fst (.snd (.snd (.snd .v0))))))
      (.bind (avlSearchPair32C F.K_cap
          (auxFgRootRoAvlE (.fst (.snd (.snd .v1))))
          (.snd (.snd (.snd (.snd .v1)))))
        (.bind
          (let minIdxE := Expr.caseOpt (.fst .v0) (.nat 0) (.add (.snd .v0) (.nat 1))
           let rkE := Expr.fst (.fst (.snd (.snd (.snd .v2))))
           liftGdh1 (rootSessScanC F.K_on)
             (.pair (.pair rkE .v1) (.pair minIdxE (auxFgRootSessE (.fst (.snd (.snd .v2)))))))
          (.caseOpt .v0
            (.caseOpt (.fst .v1)
              (.bind (liftGdh0 sampleRootPair64LegC)
                (.bind (avlInsertAtPathC F.K_cap
                    (auxFgRootRoAvlE (.fst (.snd (.snd .v4))))
                    (.snd .v2)
                    (.snd (.snd (.snd (.snd .v4))))
                    (.pair .v0 (auxFgRootCtrE (.fst (.snd (.snd .v4))))))
                  (.ret (.pair (aRootKdfAtomicE .v1)
                    (.pair
                      (.pair
                        (simPrependRootE (.fst .v5)
                          (.pair (.fst (.fst (.snd (.snd (.snd .v5))))) (.pair .v4 .v1)))
                        (.fst (.snd .v5)))
                      (let aux5 := Expr.fst (.snd (.snd .v5))
                       fgAuxMkE (auxFgSessE aux5) (auxFgCtrE aux5) (auxFgRoAvlE aux5)
                         (auxFgRootSessE aux5) (.add (auxFgRootCtrE aux5) (.nat 1))
                         .v0 (auxRawAvlE aux5)))))))
              (.ret (.pair (aRootKdfAtomicE (.fst .v0))
                (.pair (.pair (.fst .v4) (.fst (.snd .v4))) (.fst (.snd (.snd .v4)))))))
            (.ret (.pair (aRootKdfAtomicE (.snd (.snd (.snd .v0))))
              (.pair (.pair (.fst .v4) (.fst (.snd .v4))) (.fst (.snd (.snd .v4))))))))))

@[expose] def fgCoreArm_initPrin (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (paE : Expr pqAtomicOps Γ (embedTy a1gParams2Ty))
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy)
    (uE : Expr pqAtomicOps Γ .nat) :
    Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy :=
  .bind (.ret (.pair sigBE auxE))
    (.bind (liftGdh1 (a1gInitPrin2LegC F)
        (.pair (exprRename Var.succ paE)
          (.pair (exprRename Var.succ simE) (exprRename Var.succ uE))))
      (.ret (.pair (.fst .v0) (.pair (.pair (.snd .v0) (.fst .v1)) (.snd .v1)))))

@[expose] def fgCoreArm_corrupt (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy)
    (uE : Expr pqAtomicOps Γ .nat) :
    Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy :=
  .bind (.ret (.pair sigBE auxE))
    (.bind (liftGdh1 (fgCorruptLegC F)
        (.pair (exprRename Var.succ simE) (exprRename Var.succ uE)))
      (.ret (.pair (.fst .v0) (.pair (.pair (.snd .v0) (.fst .v1)) (.snd .v1)))))

@[expose] def fgCoreArm_genSPK (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (paE : Expr pqAtomicOps Γ (embedTy a1gParams2Ty))
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy)
    (xE : Expr pqAtomicOps Γ (.prod .nat .nat)) :
    Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy :=
  .bind (.ret auxE)
    (.bind (liftCs1 (a1gGenSpk2LegC F)
        (.pair (exprRename Var.succ paE)
          (.pair (exprRename Var.succ simE)
            (.pair (exprRename Var.succ sigBE) (exprRename Var.succ xE)))))
      (.ret (.pair (.fst .v0) (.pair (.snd .v0) .v1))))

@[expose] def fgCoreArm_genOPK (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy)
    (xE : Expr pqAtomicOps Γ (.prod .nat (.prod .nat .nat))) :
    Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy :=
  .bind (.ret (.pair sigBE auxE))
    (.bind (liftGdh1 (fgGenOpkLegC F)
        (.pair (exprRename Var.succ simE) (exprRename Var.succ xE)))
      (.ret (.pair (.fst .v0) (.pair (.pair (.snd .v0) (.fst .v1)) (.snd .v1)))))

@[expose] def fgCoreArm_send (S : Setup) (F : AuthKindFuels) (opk : Bool) {Γ : List (Ty pqAtomicSig)}
    (paE : Expr pqAtomicOps Γ (embedTy a1gParams2Ty))
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy)
    (xE : Expr pqAtomicOps Γ authSendQAtomicTy) :
    Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy :=
  .bind (.ret (.pair sigBE auxE))
    (.bind (liftGdh1 (fgSend2ShadowC S F opk)
        (.pair (exprRename Var.succ paE)
          (.pair (exprRename Var.succ simE)
            (.pair (auxSessSliceE (.snd .v0)) (exprRename Var.succ xE)))))
      (.ret (.pair (.fst .v0)
        (.pair (.pair (.fst (.snd .v0)) (.fst .v1))
          (auxPutSessSliceE (.snd .v1) (.snd (.snd .v0)))))))

@[expose] def fgCoreArm_recv (S : Setup) (F : AuthKindFuels) (opk : Bool) {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy)
    (xE : Expr pqAtomicOps Γ authRecvQAtomicTy) :
    Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy :=
  .bind (.ret (.pair sigBE auxE))
    (.bind (liftGdh1 (fgRecvShadowB S F opk)
        (.pair (exprRename Var.succ simE)
          (.pair (auxSessSliceE (.snd .v0)) (exprRename Var.succ xE))))
      (.ret (.pair (.fst .v0)
        (.pair (.pair (.fst (.snd .v0)) (.fst .v1))
          (auxPutSessSliceE (.snd .v1) (.snd (.snd .v0)))))))

@[expose] def fgCoreArm_revealDh {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy) :
    Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy :=
  .ret (.pair aNoneAtomicE (.pair (.pair simE sigBE) auxE))

@[expose] def fgCoreArm_registerKey {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy)
    (skE : Expr pqAtomicOps Γ (PB 32)) :
    Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy :=
  .bind (.ret (.pair sigBE auxE))
    (.bind (liftGdh1 fgRegisterLegC
        (.pair (exprRename Var.succ simE) (exprRename Var.succ skE)))
      (.ret (.pair (.fst .v0) (.pair (.pair (.snd .v0) (.fst .v1)) (.snd .v1)))))

@[expose] def a1gWrapCoreArm (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ a1g2ShadowStTy)
    (core : Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy) :
    Comp pqAtomicOps pqAuthSigAndDdhIface Γ (.prod authRespAtomicTy a1g2ShadowStTy) :=
  let paE  := Expr.fst (.fst (.fst stE))
  let simE := Expr.snd (.fst (.fst stE))
  .ite (a1gHaltGuard2E F.K_on paE simE)
    (.ret (.pair aNoneAtomicE stE))
    (.bind (.ret (.pair stE .unit))
      (.bind (compRename Var.succ core)
        (.ret (.pair (.fst .v0)
          (.pair
            (.pair (.pair (.fst (.fst (.fst (.fst .v1)))) (.fst (.fst (.snd .v0))))
              (.snd (.fst (.snd .v0))))
            (.snd (.snd .v0)))))))

@[expose] def a1gArm_initPrin (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthSigAndDdhIface [.nat, a1g2ShadowStTy, authQueryAtomicTy]
      (.prod authRespAtomicTy a1g2ShadowStTy) :=
  a1gWrapCoreArm F .v1
    (fgCoreArm_initPrin F (.fst (.fst (.fst .v1))) (.snd (.fst (.fst .v1)))
      (.snd (.fst .v1)) (.snd .v1) .v0)

@[expose] def a1gArm_corrupt (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthSigAndDdhIface [.nat, a1g2ShadowStTy, authQueryAtomicTy]
      (.prod authRespAtomicTy a1g2ShadowStTy) :=
  a1gWrapCoreArm F .v1
    (fgCoreArm_corrupt F (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0)

@[expose] def a1gArm_genSPK (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthSigAndDdhIface [.prod .nat .nat, a1g2ShadowStTy, authQueryAtomicTy]
      (.prod authRespAtomicTy a1g2ShadowStTy) :=
  a1gWrapCoreArm F .v1
    (fgCoreArm_genSPK F (.fst (.fst (.fst .v1))) (.snd (.fst (.fst .v1)))
      (.snd (.fst .v1)) (.snd .v1) .v0)

@[expose] def a1gArm_genOPK (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthSigAndDdhIface
      [.prod .nat (.prod .nat .nat), a1g2ShadowStTy, authQueryAtomicTy]
      (.prod authRespAtomicTy a1g2ShadowStTy) :=
  a1gWrapCoreArm F .v1
    (fgCoreArm_genOPK F (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0)

@[expose] def a1gArm_send (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    Comp pqAtomicOps pqAuthSigAndDdhIface
      [authSendQAtomicTy, a1g2ShadowStTy, authQueryAtomicTy]
      (.prod authRespAtomicTy a1g2ShadowStTy) :=
  a1gWrapCoreArm F .v1
    (fgCoreArm_send S F opk (.fst (.fst (.fst .v1))) (.snd (.fst (.fst .v1)))
      (.snd (.fst .v1)) (.snd .v1) .v0)

@[expose] def a1gArm_recv (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    Comp pqAtomicOps pqAuthSigAndDdhIface
      [authRecvQAtomicTy, a1g2ShadowStTy, authQueryAtomicTy]
      (.prod authRespAtomicTy a1g2ShadowStTy) :=
  a1gWrapCoreArm F .v1
    (fgCoreArm_recv S F opk (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0)

@[expose] def a1gArm_roQuery (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthSigAndDdhIface [PB 192, a1g2ShadowStTy, authQueryAtomicTy]
      (.prod authRespAtomicTy a1g2ShadowStTy) :=
  a1gWrapCoreArm F .v1
    (fgCoreArm_roQuery F (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0)

@[expose] def a1gArm_roRootQuery (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthSigAndDdhIface
      [.prod (PB 32) (PB 32), a1g2ShadowStTy, authQueryAtomicTy]
      (.prod authRespAtomicTy a1g2ShadowStTy) :=
  a1gWrapCoreArm F .v1
    (fgCoreArm_roRootQuery F (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0)

@[expose] def a1gArm_revealDh (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthSigAndDdhIface [.unit, a1g2ShadowStTy, authQueryAtomicTy]
      (.prod authRespAtomicTy a1g2ShadowStTy) :=
  a1gWrapCoreArm F .v1
    (fgCoreArm_revealDh (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1))

@[expose] def a1gArm_registerKey (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthSigAndDdhIface [PB 32, a1g2ShadowStTy, authQueryAtomicTy]
      (.prod authRespAtomicTy a1g2ShadowStTy) :=
  a1gWrapCoreArm F .v1
    (fgCoreArm_registerKey (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0)

@[expose] def a1sIsFrozenE {Γ : List (Ty pqAtomicSig)}
    (sLegE : Expr pqAtomicOps Γ (embedTy a1sStTy)) : Expr pqAtomicOps Γ .bool :=
  liftExpr1 (isSomeE (a1sFg (.var .vz))) sLegE

@[expose] def a1sCaseAPa2AtomicE {Γ : List (Ty pqAtomicSig)}
    (sLegE : Expr pqAtomicOps Γ (embedTy a1sStTy)) :
    Expr pqAtomicOps Γ (embedTy a1gParams2Ty) :=
  liftExpr1 (a1sCaseAPa2 (a1sTpk (.var .vz)) (a1sTp (.var .vz))) sLegE

@[expose] def a1sSimAtomicE {Γ : List (Ty pqAtomicSig)}
    (sLegE : Expr pqAtomicOps Γ (embedTy a1sStTy)) :
    Expr pqAtomicOps Γ (embedTy fgSimTy) := .snd (.fst (.fst sLegE))

@[expose] def a1sSigBAtomicE {Γ : List (Ty pqAtomicSig)}
    (sLegE : Expr pqAtomicOps Γ (embedTy a1sStTy)) :
    Expr pqAtomicOps Γ .nat := .snd (.fst sLegE)

@[expose] def a1sPutSimSigBE {Γ : List (Ty pqAtomicSig)}
    (sLegE : Expr pqAtomicOps Γ (embedTy a1sStTy))
    (simSigBE : Expr pqAtomicOps Γ (.prod (embedTy fgSimTy) .nat)) :
    Expr pqAtomicOps Γ (embedTy a1sStTy) :=
  liftExpr2
    (a1sMk
      (.pair (.pair (.fst (.fst (a1sG (.var .vz)))) (.fst (.var (.vs .vz))))
        (.snd (.var (.vs .vz))))
      (a1sTp (.var .vz)) (a1sTpk (.var .vz)) (a1sFg (.var .vz)))
    sLegE simSigBE

@[expose] def a1sDelegateCoreArm (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ a1s2ShadowStTy)
    (core : Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy) :
    Comp pqAtomicOps pqAuthSigAndDdhIface Γ (.prod authRespAtomicTy a1s2ShadowStTy) :=
  let paE  := a1sCaseAPa2AtomicE (.fst stE)
  let simE := a1sSimAtomicE (.fst stE)
  .ite (a1gHaltGuard2E F.K_on paE simE)
    (.ret (.pair aNoneAtomicE stE))
    (.bind (.ret (.pair stE .unit))
      (.bind (compRename Var.succ core)
        (.ret (.pair (.fst .v0)
          (.pair (a1sPutSimSigBE (.fst (.fst .v1)) (.fst (.snd .v0))) (.snd (.snd .v0)))))))

@[expose] def a1sWrapNonSendArm (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ a1s2ShadowStTy)
    (core : Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy) :
    Comp pqAtomicOps pqAuthSigAndDdhIface Γ (.prod authRespAtomicTy a1s2ShadowStTy) :=
  .ite (a1sIsFrozenE (.fst stE))
    (.ret (.pair aNoneAtomicE stE))
    (a1sDelegateCoreArm F stE core)

@[expose] def a1sArm_initPrin (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthSigAndDdhIface [.nat, a1s2ShadowStTy, authQueryAtomicTy]
      (.prod authRespAtomicTy a1s2ShadowStTy) :=
  a1sWrapNonSendArm F .v1
    (fgCoreArm_initPrin F (a1sCaseAPa2AtomicE (.fst .v1)) (a1sSimAtomicE (.fst .v1))
      (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0)

@[expose] def a1sArm_corrupt (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthSigAndDdhIface [.nat, a1s2ShadowStTy, authQueryAtomicTy]
      (.prod authRespAtomicTy a1s2ShadowStTy) :=
  a1sWrapNonSendArm F .v1
    (fgCoreArm_corrupt F (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0)

@[expose] def a1sArm_genSPK (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthSigAndDdhIface [.prod .nat .nat, a1s2ShadowStTy, authQueryAtomicTy]
      (.prod authRespAtomicTy a1s2ShadowStTy) :=
  a1sWrapNonSendArm F .v1
    (fgCoreArm_genSPK F (a1sCaseAPa2AtomicE (.fst .v1)) (a1sSimAtomicE (.fst .v1))
      (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0)

@[expose] def a1sArm_genOPK (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthSigAndDdhIface
      [.prod .nat (.prod .nat .nat), a1s2ShadowStTy, authQueryAtomicTy]
      (.prod authRespAtomicTy a1s2ShadowStTy) :=
  a1sWrapNonSendArm F .v1
    (fgCoreArm_genOPK F (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0)

@[expose] def a1sArm_send (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    Comp pqAtomicOps pqAuthSigAndDdhIface
      [authSendQAtomicTy, a1s2ShadowStTy, authQueryAtomicTy]
      (.prod authRespAtomicTy a1s2ShadowStTy) :=
  .ite (a1sIsFrozenE (.fst .v1))
    (.ret (.pair aNoneAtomicE .v1))
    (.bind (liftCs1 (a1sSendCheckLegC S F) (.pair (.fst .v1) .v0))
      (.caseSum .v0
        (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd .v3))))
        (a1sDelegateCoreArm F .v3
          (fgCoreArm_send S F opk (a1sCaseAPa2AtomicE (.fst .v3)) (a1sSimAtomicE (.fst .v3))
            (a1sSigBAtomicE (.fst .v3)) (.snd .v3) .v2))))

@[expose] def a1sArm_recv (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    Comp pqAtomicOps pqAuthSigAndDdhIface
      [authRecvQAtomicTy, a1s2ShadowStTy, authQueryAtomicTy]
      (.prod authRespAtomicTy a1s2ShadowStTy) :=
  a1sWrapNonSendArm F .v1
    (fgCoreArm_recv S F opk (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0)

@[expose] def a1sArm_roQuery (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthSigAndDdhIface [PB 192, a1s2ShadowStTy, authQueryAtomicTy]
      (.prod authRespAtomicTy a1s2ShadowStTy) :=
  a1sWrapNonSendArm F .v1
    (fgCoreArm_roQuery F (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0)

@[expose] def a1sArm_roRootQuery (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthSigAndDdhIface
      [.prod (PB 32) (PB 32), a1s2ShadowStTy, authQueryAtomicTy]
      (.prod authRespAtomicTy a1s2ShadowStTy) :=
  a1sWrapNonSendArm F .v1
    (fgCoreArm_roRootQuery F (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0)

@[expose] def a1sArm_revealDh (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthSigAndDdhIface [.unit, a1s2ShadowStTy, authQueryAtomicTy]
      (.prod authRespAtomicTy a1s2ShadowStTy) :=
  a1sWrapNonSendArm F .v1
    (fgCoreArm_revealDh (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1))

@[expose] def a1sArm_registerKey (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthSigAndDdhIface [PB 32, a1s2ShadowStTy, authQueryAtomicTy]
      (.prod authRespAtomicTy a1s2ShadowStTy) :=
  a1sWrapNonSendArm F .v1
    (fgCoreArm_registerKey (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0)

end AtomicArms

@[expose] def a1g2KindInit (S : Setup) (b : QueryBudget) :
    Comp pqAtomicOps pqAuthSigAndDdhIface [.prod (PB 32) (PB 32)]
      (.prod .unit a1g2ShadowStTy) :=
  .bind (mapComp tlAuthSigDdh (a1g2InitDsl S b.q_total))
    (.ret (.pair (.fst .v0) (.pair (.snd .v0) emptyFgAuthShadowAuxE)))

@[expose] def a1g2KindHandle (S : Setup) (b : QueryBudget) :
    Comp pqAtomicOps pqAuthSigAndDdhIface [a1g2ShadowStTy, authQueryAtomicTy]
      (.prod authRespAtomicTy a1g2ShadowStTy) :=
  let F := AuthKindFuels.ofBudget S b
  dispatchAuthQ .v1
    (a1gArm_initPrin F)
    (a1gArm_corrupt F)
    (a1gArm_genSPK F)
    (a1gArm_genOPK F)
    (a1gArm_send S F true)
    (a1gArm_send S F false)
    (a1gArm_recv S F true)
    (a1gArm_recv S F false)
    (a1gArm_roQuery F)
    (a1gArm_roRootQuery F)
    (a1gArm_revealDh F)
    (a1gArm_registerKey F)

@[expose] def a1g2KindFinish (S : Setup) (b : QueryBudget) :
    Comp pqAtomicOps pqAuthSigAndDdhIface [a1g2ShadowStTy, .bool] (PB 32) :=
  let F := AuthKindFuels.ofBudget S b
  liftGdh1 (fgExtract2K S F) (.fst (.fst .v0))

/-- Kind-split shadow-indexed `CostedReduction` for one-key `Auth` `GapDhWithSign`. -/
@[expose] def a1g2KindProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqAuthSigAndDdhIface (authSpec S) (authCodec S)
      (.prod (PB 32) (PB 32)) .unit .bool (PB 32) where
  σ      := a1g2ShadowStTy
  init   := a1g2KindInit S b
  handle := a1g2KindHandle S b
  finish := a1g2KindFinish S b

@[expose] def a1s2KindInit (S : Setup) (b : QueryBudget) :
    Comp pqAtomicOps pqAuthSigAndDdhIface [PB 32]
      (.prod .unit a1s2ShadowStTy) :=
  .bind (mapComp tlAuthSigDdh (a1sInit2Dsl S b.q_total))
    (.ret (.pair (.fst .v0) (.pair (.snd .v0) emptyFgAuthShadowAuxE)))

@[expose] def a1s2KindHandle (S : Setup) (b : QueryBudget) :
    Comp pqAtomicOps pqAuthSigAndDdhIface [a1s2ShadowStTy, authQueryAtomicTy]
      (.prod authRespAtomicTy a1s2ShadowStTy) :=
  let F := AuthKindFuels.ofBudget S b
  dispatchAuthQ .v1
    (a1sArm_initPrin F)
    (a1sArm_corrupt F)
    (a1sArm_genSPK F)
    (a1sArm_genOPK F)
    (a1sArm_send S F true)
    (a1sArm_send S F false)
    (a1sArm_recv S F true)
    (a1sArm_recv S F false)
    (a1sArm_roQuery F)
    (a1sArm_roRootQuery F)
    (a1sArm_revealDh F)
    (a1sArm_registerKey F)

@[expose] def a1s2KindFinish :
    Comp pqAtomicOps pqAuthSigAndDdhIface [a1s2ShadowStTy, .bool]
      (.prod (PB 1569) (PB 64)) :=
  .ret
    (liftExpr1
      (eCaseOpt (a1sFg (.var .vz))
        (.pair (litBytes 1569 []) (litBytes 64 []))
        fun f => v f)
      (.fst .v0))

/-- Kind-split shadow-indexed `CostedReduction` for one-key `Auth` `GapSigEufCma`. -/
@[expose] def a1s2KindProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqAuthSigAndDdhIface (authSpec S) (authCodec S)
      (PB 32) .unit .bool (.prod (PB 1569) (PB 64)) where
  σ      := a1s2ShadowStTy
  init   := a1s2KindInit S b
  handle := a1s2KindHandle S b
  finish := a1s2KindFinish

theorem a1gHaltGuard2E_cost_le (K_on : ℕ) {Γ : List (Ty pqAtomicSig)}
    (paE : Expr pqAtomicOps Γ (embedTy a1gParams2Ty))
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy)) :
    (a1gHaltGuard2E K_on paE simE).cost ≤ paE.cost + simE.cost + 5 * K_on + 20 := by
  simp only [a1gHaltGuard2E, liftExpr2, eCaseSum, pa2Role, eCaseOpt, eFind, stPrin, fsBase,
    natEq, peCorrupted, v, Var.vz, Var.vs, Expr.litBool, mapExpr,
    exprRename_cost, Expr.cost]
  omega

theorem a1gHaltGuard2E_size_le (K_on : ℕ) {Γ : List (Ty pqAtomicSig)}
    (paE : Expr pqAtomicOps Γ (embedTy a1gParams2Ty))
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy)) :
    (a1gHaltGuard2E K_on paE simE).size ≤ paE.size + simE.size + bits K_on + 30 := by
  simp only [a1gHaltGuard2E, liftExpr2, eCaseSum, pa2Role, eCaseOpt, eFind, stPrin, fsBase,
    natEq, peCorrupted, v, Var.vz, Var.vs, Expr.litBool,
    exprRename_size, mapExpr_size, _root_.Computational.Proofs.SignalPqxdh.AtomicLift.exprLitSize,
    Expr.size]
  omega

theorem a1sIsFrozenE_cost_le {Γ : List (Ty pqAtomicSig)}
    (sLegE : Expr pqAtomicOps Γ (embedTy a1sStTy)) :
    (a1sIsFrozenE sLegE).cost ≤ sLegE.cost + 10 := by
  simp only [a1sIsFrozenE, liftExpr1, isSomeE, a1sFg, Expr.litBool, mapExpr,
    exprRename_cost, Expr.cost]
  omega

theorem a1sIsFrozenE_size_le {Γ : List (Ty pqAtomicSig)}
    (sLegE : Expr pqAtomicOps Γ (embedTy a1sStTy)) :
    (a1sIsFrozenE sLegE).size ≤ sLegE.size + 12 := by
  simp only [a1sIsFrozenE, liftExpr1, isSomeE, a1sFg, Expr.litBool,
    exprRename_size, mapExpr_size, _root_.Computational.Proofs.SignalPqxdh.AtomicLift.exprLitSize,
    Expr.size]
  omega

theorem a1sCaseAPa2AtomicE_cost_le {Γ : List (Ty pqAtomicSig)}
    (sLegE : Expr pqAtomicOps Γ (embedTy a1sStTy)) :
    (a1sCaseAPa2AtomicE sLegE).cost ≤ sLegE.cost + 20 := by
  simp only [a1sCaseAPa2AtomicE, liftExpr1, mapExpr, exprRename_cost, Expr.cost]
  omega

theorem a1sCaseAPa2AtomicE_size_le {Γ : List (Ty pqAtomicSig)}
    (sLegE : Expr pqAtomicOps Γ (embedTy a1sStTy)) :
    (a1sCaseAPa2AtomicE sLegE).size ≤ sLegE.size + 20 := by
  simp only [a1sCaseAPa2AtomicE, liftExpr1, exprRename_size, mapExpr_size,
    _root_.Computational.Proofs.SignalPqxdh.AtomicLift.exprLitSize, Expr.size]
  omega

theorem a1sPutSimSigBE_cost_le {Γ : List (Ty pqAtomicSig)}
    (sLegE : Expr pqAtomicOps Γ (embedTy a1sStTy))
    (simSigBE : Expr pqAtomicOps Γ (.prod (embedTy fgSimTy) .nat)) :
    (a1sPutSimSigBE sLegE simSigBE).cost ≤ sLegE.cost + simSigBE.cost + 30 := by
  simp only [a1sPutSimSigBE, liftExpr2, mapExpr, exprRename_cost, Expr.cost]
  omega

theorem a1sPutSimSigBE_size_le {Γ : List (Ty pqAtomicSig)}
    (sLegE : Expr pqAtomicOps Γ (embedTy a1sStTy))
    (simSigBE : Expr pqAtomicOps Γ (.prod (embedTy fgSimTy) .nat)) :
    (a1sPutSimSigBE sLegE simSigBE).size ≤ sLegE.size + simSigBE.size + 40 := by
  simp only [a1sPutSimSigBE, liftExpr2, exprRename_size, mapExpr_size,
    _root_.Computational.Proofs.SignalPqxdh.AtomicLift.exprLitSize, Expr.size]
  omega

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhK
