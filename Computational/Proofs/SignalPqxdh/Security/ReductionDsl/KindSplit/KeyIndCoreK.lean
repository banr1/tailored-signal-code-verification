/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Headline
public import Computational.Specifications.Pqxdh.Security.CostedBudgets
public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndCore -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKem -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableSpec -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyShcr -- proof-setup: allow-public-import

/-!
# Shadow-Indexed `KeyIndCore` and `KemShCr` Query-Kind Handlers

Defines the shadow-indexed `KeyInd` and `KemShCr` DSL handlers over `pqAtomicSig` for the
online/offline query-kind split. Random-oracle accesses probe an AVL shadow table (`roAvl`) in
logarithmic time while updating the legacy `stRo` association list in lockstep so forgetful
projections (`forgetCore`, `forgetShcrKind`) match the unsplit handlers verbatim.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK

open OracleSpec OracleComp
open _root_.SignalPqxdh (Setup QueryBudget keyIndSpec)
open _root_.ReductionDsl (
  Ty Var Expr Comp Env Iface
  pqAtomicSig pqAtomicOps pqPrimIface pqKeyIndCodec
  AtomicPureOp B PB drKeyT bundleT hdrT sidT bits
)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift (
  TagLift embedTy embedVal mapExpr mapComp exprRename compRename
  finSidToNatExpr tlPrimKeyInd
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (
  aop avlTy avlEmptyE dfltB192E dfltDrKeyE
  avlSearchB192C avlInsertAtPathC
)

/-- Clamped online, offline, DH, session, and random-oracle table bounds for `KeyInd` reductions. -/
structure KeyIndCoreFuels where
  M_on   : ℕ
  M_off  : ℕ
  M_dh   : ℕ
  M_sess : ℕ
  roCap  : ℕ
  deriving DecidableEq, Repr

@[expose] def keyIndCoreFuels (S : Setup) (b : QueryBudget) : KeyIndCoreFuels :=
  let mOn  := min b.q_on b.q_total
  let mOff := min b.q_ro b.q_total
  { M_on   := mOn
    M_off  := mOff
    M_dh   := min mOn S.N_dh
    M_sess := min mOn S.N_sess_tot
    roCap  := mOff + 2 * mOn + 1 }

/-- Non-matching creation-ordinal sentinel strictly exceeding all online and `gdh` ordinals while
    bounded by `b.q_total + 1`. -/
@[expose] def keyIndSentinel (S : Setup) (b : QueryBudget) : ℕ :=
  min (b.q_total + 1) (S.N_dh + min b.q_on b.q_total + 1)

theorem keyIndSentinel_le (S : Setup) (b : QueryBudget) :
    keyIndSentinel S b ≤ b.q_total + 1 :=
  Nat.min_le_left _ _

theorem lt_keyIndSentinel (S : Setup) (b : QueryBudget) :
    min b.q_on b.q_total < keyIndSentinel S b := by
  simp only [keyIndSentinel]
  omega

abbrev roAvlTy : Ty pqAtomicSig :=
  avlTy (B 192) (drKeyT (ℓ := 0) (Pt := Empty))

abbrev roListAtomicTy : Ty pqAtomicSig :=
  .list (.prod (PB 192) (drKeyT (ℓ := 0) (Pt := Empty)))

abbrev keyIndBaseAtomicTy : Ty pqAtomicSig :=
  embedTy _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndStateTy

/-- Shadow-indexed `KeyIndCore` state pairing the base state with its `roAvl` table. -/
abbrev keyIndStateKTy : Ty pqAtomicSig :=
  .prod keyIndBaseAtomicTy roAvlTy

/-- Forgetful projection dropping the `roAvl` shadow from `keyIndStateKTy`. -/
@[expose] def forgetCore (s : keyIndStateKTy.denote) : keyIndBaseAtomicTy.denote :=
  s.1

/-- Shadow-indexed `KemShCr` state pairing `shcrStTy` with its `roAvl` table. -/
abbrev shcrKindStTy : Ty pqAtomicSig :=
  .prod (embedTy _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.shcrStTy) roAvlTy

/-- Forgetful projection dropping the `roAvl` shadow from `shcrKindStTy`. -/
@[expose] def forgetShcrKind (s : shcrKindStTy.denote) :
    (embedTy _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.shcrStTy).denote :=
  s.1

@[expose] def emptyRoAvlE {Γ : List (Ty pqAtomicSig)} : Expr pqAtomicOps Γ roAvlTy :=
  avlEmptyE dfltB192E dfltDrKeyE

@[expose] def emptyVarRen {Δ : List (Ty pqAtomicSig)} {a : Ty pqAtomicSig} :
    Var [] a → Var Δ a :=
  fun v => nomatch v

/-- AVL-backed random-oracle lookup-or-sample maintaining `stRo` and its `roAvl` shadow in lockstep. -/
@[expose] def roShadowQueryC {ι : Type} {T : OracleSpec ι}
    {I₁ : _root_.ReductionDsl.Iface _root_.SignalPqxdh.LegacyCosted.pqSig T}
    {A : _root_.Computational.Proofs.SignalPqxdh.AtomicLift.AtomicIface T}
    (_tl : TagLift I₁ A) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy)
    (tblE : Expr pqAtomicOps Γ roAvlTy)
    (secE : Expr pqAtomicOps Γ (PB 192)) :
    Comp pqAtomicOps A.toIface Γ
      (.prod (drKeyT (ℓ := 0) (Pt := Empty)) (.prod roListAtomicTy roAvlTy)) :=
  .bind (.ret (.pair roListE (.pair tblE (.pair secE (aop (.pbytesToBytes 192) secE)))))
    (.bind (avlSearchB192C cap (.fst (.snd .v0)) (.snd (.snd (.snd .v0))))
      (.caseOpt (.fst .v0)
        (.bind (_root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs.sampleDrKey96AtomicC
            (I := A.toIface) rfl)
          (.bind (avlInsertAtPathC cap
              (.fst (.snd .v2))
              (.snd .v1)
              (.snd (.snd (.snd .v2)))
              .v0)
            (.ret (.pair .v1
              (.pair (.cons (.pair (.fst (.snd (.snd .v3))) .v1) (.fst .v3)) .v0)))))
        (.ret (.pair .v0 (.pair (.fst .v2) (.fst (.snd .v2)))))))

/-- Byte-slice equality `.eq 192 192` in `pqxdhOps` agrees with `ofU8` equality on arbitrary-length byte lists. -/
theorem pbytesEq192_iff_ofU8_eq (a b : List UInt8) :
    (_root_.SignalPqxdh.LegacyCosted.pqxdhOps.eval (.inl (.eq 192 192)) (a, b) = true) ↔
      CryptoVerification.E2E.ofU8 a = CryptoVerification.E2E.ofU8 b := by
  change (a == b) = true ↔ CryptoVerification.E2E.ofU8 a = CryptoVerification.E2E.ofU8 b
  rw [← _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableSpec.ofU8_beq_eq,
    beq_iff_eq]

section LegacySplits

open _root_.SignalPqxdh.LegacyCosted (
  pqSig pqxdhOps
)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  Ext PT RS SCS accInpTy accQTy acceptKeysC bindV buIkB buMk buOpkB buPqspkB buPqspkId buPqspkSig
  buSpkB buSpkId buSpkSig buildSecretsE caseOptV checkProvC checkSigsC corruptB eAny eCaseOpt
  eFind eMap encEC encKEM eqB eqU32 findHonestC findMV genOpkB genSpkB getDBytes hdEkAPk hdIkAPk
  hdKemCt hdMk hdOpkId hdPqspkId hdSpkId honestPeerC initGuardE initPrin1KeyB initPrinB initQTy
  initSidE isNoneRespE isSomeE keyIndRespTy keyIndStateTy koskBundleOkC koskSenderOkC kyberCheckE
  lenB letV nat2Eq nat3Eq natEq nonZero32 oeConsumed oeOpkPk oeOpkSk oeUpd onBase optFst optSnd
  optU32Eq partnerC pauseTy peIkAPk peSecIKA0 peSecIKAsign preCheckC principalEntryTy qHdr qJ qK
  qKJO qKemDecaps qKemEncaps qO qSigSign qSigVerify qX25519 qX25519Base rAccFresh rBundle rDrKey
  rHdr rInitUnfresh rNone reDrRand reMk recordRespC registerB resolveSigPkC revealB revealDhB
  revealSpkB rs sBytes32 sDrKey96 sRandom64 sbMk sbPqspkPk sbPqspkSk sbSpkPk sbSpkSk scBase scCnt
  scIR scRR scTB scTPk scTSk scUpd seMk seSid seUpd shcrExtractC shcrFinE shcrGenSpkB shcrStTy
  sidEq spkBundleEntryTy stKyb stOpks stPrin stResps stRo stSess stSpks stUpd stUsedN stUsedO
  testB tryPauseC u32OfNat v
)

abbrev roListLegacyTy : PT :=
  .list (.prod (_root_.SignalPqxdh.LegacyCosted.B 192) _root_.SignalPqxdh.LegacyCosted.drKeyT)

@[expose] def coreGetRoE {Γ : List PT} (st : Expr pqxdhOps Γ keyIndStateTy) :
    Expr pqxdhOps Γ roListLegacyTy :=
  stRo st

@[expose] def coreSetRoRespC :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface
      [_root_.SignalPqxdh.LegacyCosted.drKeyT, roListLegacyTy, keyIndStateTy] RS :=
  let Δ  : List PT := [_root_.SignalPqxdh.LegacyCosted.drKeyT, roListLegacyTy, keyIndStateTy]
  let dk : Var Δ _root_.SignalPqxdh.LegacyCosted.drKeyT := .zero
  let ro : Var Δ roListLegacyTy := .succ .zero
  let st : Var Δ keyIndStateTy := .succ (.succ .zero)
  .ret (rs (rDrKey (v dk)) (stUpd (v st) (ro := v ro)))

@[expose] def shcrGetRoE {Γ : List PT} (s : Expr pqxdhOps Γ shcrStTy) :
    Expr pqxdhOps Γ roListLegacyTy :=
  stRo (scBase s)

@[expose] def shcrSetRoRespC :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface
      [_root_.SignalPqxdh.LegacyCosted.drKeyT, roListLegacyTy, shcrStTy] SCS :=
  let Δ  : List PT := [_root_.SignalPqxdh.LegacyCosted.drKeyT, roListLegacyTy, shcrStTy]
  let dk : Var Δ _root_.SignalPqxdh.LegacyCosted.drKeyT := .zero
  let ro : Var Δ roListLegacyTy := .succ .zero
  let s  : Var Δ shcrStTy := .succ (.succ .zero)
  .ret (.pair (rDrKey (v dk)) (scUpd (v s) (base := stUpd (scBase (v s)) (ro := v ro))))

@[expose] def initFinishPreRoC {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (bu : Var Γ₁ _root_.SignalPqxdh.LegacyCosted.bundleT)
    (uE : Var Γ₂ (.prod .nat principalEntryTy))
    (ekSk : Var Γ₃ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (sc : Var Γ₄ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
                        (_root_.SignalPqxdh.LegacyCosted.B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface Δ
      (.prod (_root_.SignalPqxdh.LegacyCosted.B 192)
             (_root_.SignalPqxdh.LegacyCosted.B 32)) :=
  bindV (qX25519Base (v ekSk)) fun ekPk =>
  bindV (qX25519 (.pair (peSecIKA0 (.snd (v uE))) (buSpkB (v bu)))) fun dh1 =>
  bindV (qX25519 (.pair (v ekSk) (buIkB (v bu)))) fun dh2 =>
  bindV (qX25519 (.pair (v ekSk) (buSpkB (v bu)))) fun dh3 =>
  bindV (qX25519 (.pair (v ekSk) (getDBytes (optSnd (buOpkB (v bu)))))) fun dh4r =>
  .ret (.pair
    (buildSecretsE (v dh1) (v dh2) (v dh3)
      (eCaseOpt (buOpkB (v bu)) .none fun _ => .some (v dh4r)) (.fst (v sc)))
    (v ekPk))

@[expose] def initFinishPostRoC (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Γ₈ Γ₉ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy)
    (sid : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.sidT)
    (bu : Var Γ₃ _root_.SignalPqxdh.LegacyCosted.bundleT)
    (uE : Var Γ₄ (.prod .nat principalEntryTy))
    (ekSk : Var Γ₅ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (sc : Var Γ₆ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
                        (_root_.SignalPqxdh.LegacyCosted.B 1568)))
    (ekPk : Var Γ₇ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (dk : Var Γ₈ _root_.SignalPqxdh.LegacyCosted.drKeyT)
    (roNew : Var Γ₉ roListLegacyTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    [Ext Γ₆ Δ] [Ext Γ₇ Δ] [Ext Γ₈ Δ] [Ext Γ₉ Δ] :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface Δ RS :=
  letV (hdMk (peIkAPk (.snd (v uE))) (v ekPk) (buSpkId (v bu)) (optFst (buOpkB (v bu)))
      (buPqspkId (v bu)) (.snd (v sc))) fun hdr =>
  bindV (honestPeerC S K st (buIkB (v bu))) fun hp =>
  bindV (checkProvC S K st bu) fun prov =>
  letV (seMk (v sid) (v hp) (buIkB (v bu)) (buSpkB (v bu)) (optSnd (buOpkB (v bu)))
      (buPqspkB (v bu)) (.fst (v prov)) (.fst (.snd (v prov))) (.snd (.snd (v prov))) (v ekSk)
      (isSomeE (v hp)) (v dk) (v dk) (v hdr) (.bool false) (.bool false)) fun se =>
  bindV (findMV (min K S.N_sess_tot) (stResps (v st)) fun r => partnerC se r) fun found =>
  bindV (caseOptV (v found) sDrKey96 fun r => .ret (reDrRand (v r))) fun drr =>
  bindV (findHonestC S K st (buIkB (v bu))) fun fh =>
  .ret (rs (eCaseOpt (v fh) (rInitUnfresh (v dk) (v hdr)) fun _ => rHdr (v hdr))
    (stUpd (v st) (sess := .cons (seUpd (v se) (drRand := v drr)) (stSess (v st)))
      (ro := v roNew)))

abbrev shcrInitMidTy : PT :=
  .prod (_root_.SignalPqxdh.LegacyCosted.B 192)
    (.prod _root_.SignalPqxdh.LegacyCosted.sidT
      (.prod _root_.SignalPqxdh.LegacyCosted.bundleT
        (.prod (.prod .nat principalEntryTy)
          (.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
            (.prod (.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
                          (_root_.SignalPqxdh.LegacyCosted.B 1568))
                   (_root_.SignalPqxdh.LegacyCosted.B 32))))))

@[expose] def shcrInitiatePreRoC (S : Setup) (K : Nat) (opk : Bool) :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface
      [shcrStTy, initQTy] (.sum SCS shcrInitMidTy) :=
  let s : Var [shcrStTy, initQTy] shcrStTy := .zero
  let x : Var [shcrStTy, initQTy] initQTy := .succ .zero
  .ite (initGuardE opk (v x)) (.ret (.inl (.pair rNone (v s)))) <|
  letV (.snd (.snd (v x))) fun bu => letV (initSidE opk (v x)) fun sid =>
  letV (scBase (v s)) fun st => letV (.fst (v x)) fun u =>
  bindV (preCheckC S K st sid u bu) fun pc =>
  caseOptV (v pc) (.ret (.inl (.pair rNone (v s)))) fun uE =>
  bindV sBytes32 fun ekSk =>
  bindV sBytes32 fun coins =>
  bindV (checkSigsC S K st bu) fun ok =>
  .ite (.not (v ok)) (.ret (.inl (.pair rNone (v s)))) <|
  bindV (qKemEncaps (.pair (buPqspkB (v bu)) (v coins))) fun enc =>
  caseOptV (v enc)
    (.ret (.inl (.pair rNone (scUpd (v s) (cnt := .add (scCnt (v s)) (.nat 1)))))) fun sc =>
  bindV (initFinishPreRoC bu uE ekSk sc) fun sp =>
  .ret (.inr (.pair (.fst (v sp)) (.pair (v sid) (.pair (v bu)
    (.pair (v uE) (.pair (v ekSk) (.pair (v sc) (.snd (v sp)))))))))

@[expose] def shcrInitiatePostRoC (S : Setup) (K : Nat) :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface
      [_root_.SignalPqxdh.LegacyCosted.drKeyT, roListLegacyTy, shcrInitMidTy, shcrStTy] SCS :=
  let Δ     : List PT :=
    [_root_.SignalPqxdh.LegacyCosted.drKeyT, roListLegacyTy, shcrInitMidTy, shcrStTy]
  let dk    : Var Δ _root_.SignalPqxdh.LegacyCosted.drKeyT := .zero
  let roNew : Var Δ roListLegacyTy := .succ .zero
  let mid   : Var Δ shcrInitMidTy := .succ (.succ .zero)
  let s     : Var Δ shcrStTy := .succ (.succ (.succ .zero))
  letV (scBase (v s)) fun st =>
  letV (.fst (.snd (v mid))) fun sid =>
  letV (.fst (.snd (.snd (v mid)))) fun bu =>
  letV (.fst (.snd (.snd (.snd (v mid))))) fun uE =>
  letV (.fst (.snd (.snd (.snd (.snd (v mid)))))) fun ekSk =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (v mid))))))) fun sc =>
  letV (.snd (.snd (.snd (.snd (.snd (.snd (v mid))))))) fun ekPk =>
  bindV (initFinishPostRoC S K st sid bu uE ekSk sc ekPk dk roNew) fun r =>
  .ret (shcrFinE (v s) (v sid) (v bu) (v sc) (v r))

@[expose] def shcrResumePreRoC :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface
      [shcrStTy, pauseTy,
       .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)]
      (.prod (_root_.SignalPqxdh.LegacyCosted.B 192)
        (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32))) :=
  let Δ  : List PT :=
    [shcrStTy, pauseTy,
     .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)]
  let d  : Var Δ pauseTy := .succ .zero
  let sc : Var Δ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
                        (_root_.SignalPqxdh.LegacyCosted.B 1568)) := .succ (.succ .zero)
  letV (.fst (.snd (v d))) fun bu =>
  letV (.snd (.snd (v d))) fun uE =>
  bindV sBytes32 fun ekSk =>
  bindV (initFinishPreRoC bu uE ekSk sc) fun sp =>
  .ret (.pair (.fst (v sp)) (.pair (v ekSk) (.snd (v sp))))

@[expose] def shcrResumePostRoC (S : Setup) (K : Nat) :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface
      [_root_.SignalPqxdh.LegacyCosted.drKeyT, roListLegacyTy,
       .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32),
       shcrStTy, pauseTy,
       .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)]
      SCS :=
  let Δ     : List PT :=
    [_root_.SignalPqxdh.LegacyCosted.drKeyT, roListLegacyTy,
     .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32),
     shcrStTy, pauseTy,
     .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)]
  let dk    : Var Δ _root_.SignalPqxdh.LegacyCosted.drKeyT := .zero
  let roNew : Var Δ roListLegacyTy := .succ .zero
  let ep    : Var Δ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
                           (_root_.SignalPqxdh.LegacyCosted.B 32)) := .succ (.succ .zero)
  let s     : Var Δ shcrStTy := .succ (.succ (.succ .zero))
  let d     : Var Δ pauseTy := .succ (.succ (.succ (.succ .zero)))
  let sc    : Var Δ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
                           (_root_.SignalPqxdh.LegacyCosted.B 1568)) :=
    .succ (.succ (.succ (.succ (.succ .zero))))
  letV (scBase (v s)) fun st =>
  letV (.fst (v d)) fun sid =>
  letV (.fst (.snd (v d))) fun bu =>
  letV (.snd (.snd (v d))) fun uE =>
  letV (.fst (v ep)) fun ekSk =>
  letV (.snd (v ep)) fun ekPk =>
  bindV (initFinishPostRoC S K st sid bu uE ekSk sc ekPk dk roNew) fun r =>
  letV (shcrFinE (v s) (v sid) (v bu) (v sc) (v r)) fun out =>
  .ret (.pair (.fst (v out)) (scUpd (.snd (v out)) (chosen := buPqspkB (v bu))))

abbrev shcrAccMidTy : PT :=
  .prod (_root_.SignalPqxdh.LegacyCosted.B 192)
    (.prod keyIndStateTy
      (.prod (.prod .nat principalEntryTy)
        (.prod (.prod (.prod .nat .nat) spkBundleEntryTy)
               (.opt (_root_.SignalPqxdh.LegacyCosted.B 32)))))

@[expose] def coreAcceptPreRoC (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ accQTy) :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface Δ (.opt shcrAccMidTy) :=
  if opk then
    .ite (.not (.and (.and (.and (.and
        (eqU32 (hdSpkId (qHdr (v x))) (u32OfNat (qJ (v x))))
        (eqU32 (hdPqspkId (qHdr (v x))) (u32OfNat (qJ (v x)))))
        (optU32Eq (hdOpkId (qHdr (v x))) (.some (u32OfNat (qO (v x))))))
        (natEq (lenB (hdIkAPk (qHdr (v x)))) (.nat 32)))
        (natEq (lenB (hdEkAPk (qHdr (v x)))) (.nat 32))))
      (.ret .none) <|
    .ite (eAny K (stUsedO (v st)) fun e => nat3Eq (qKJO (v x)) (v e)) (.ret .none) <|
    bindV (koskSenderOkC S K st (hdIkAPk (qHdr (v x)))) fun ok =>
    .ite (.not (v ok)) (.ret .none) <|
    caseOptV (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (qK (v x)))
      (.ret .none) fun kE =>
    caseOptV (eFind K (stSpks (v st)) fun e => nat2Eq (.fst (v e)) (.pair (qK (v x)) (qJ (v x))))
      (.ret .none) fun bE =>
    caseOptV (eFind K (stOpks (v st)) fun e => nat3Eq (.fst (v e)) (qKJO (v x)))
      (.ret .none) fun oE =>
    .ite (oeConsumed (.snd (v oE))) (.ret .none) <|
    letV (kyberCheckE K (stKyb (v st)) (.pair (qK (v x)) (.pair (hdPqspkId (qHdr (v x)))
        (.pair (hdSpkId (qHdr (v x))) (hdEkAPk (qHdr (v x))))))) fun rk =>
    bindV (acceptKeysC (.pair (peSecIKA0 (.snd (v kE))) (.pair (sbSpkSk (.snd (v bE)))
        (.pair (.some (oeOpkSk (.snd (v oE)))) (.pair (sbPqspkSk (.snd (v bE)))
          (.pair (.fst (v rk)) (qHdr (v x)))))))) fun acc =>
    caseOptV (v acc) (.ret .none) fun _ =>
    bindV (qKemDecaps (.pair (sbPqspkSk (.snd (v bE))) (hdKemCt (qHdr (v x))))) fun ss? =>
    caseOptV (v ss?) (.ret .none) fun ss =>
    bindV (qX25519 (.pair (sbSpkSk (.snd (v bE))) (hdIkAPk (qHdr (v x))))) fun dh1 =>
    bindV (qX25519 (.pair (peSecIKA0 (.snd (v kE))) (hdEkAPk (qHdr (v x))))) fun dh2 =>
    bindV (qX25519 (.pair (sbSpkSk (.snd (v bE))) (hdEkAPk (qHdr (v x))))) fun dh3 =>
    bindV (qX25519 (.pair (oeOpkSk (.snd (v oE))) (hdEkAPk (qHdr (v x))))) fun dh4 =>
    let stMid := stUpd (v st)
      (opks := eMap K (stOpks (v st)) fun e =>
        .ite (nat3Eq (.fst (v e)) (qKJO (v x)))
          (.pair (.fst (v e)) (oeUpd (.snd (v e)) (consumed := .bool true))) (v e))
      (usedO := .cons (qKJO (v x)) (stUsedO (v st)))
      (kyb := .snd (v rk))
    .ret (.some (.pair (buildSecretsE (v dh1) (v dh2) (v dh3) (.some (v dh4)) (v ss))
      (.pair stMid (.pair (v kE) (.pair (v bE) (.some (oeOpkPk (.snd (v oE)))))))))
  else
    .ite (.not (.and (.and (.and (.and
        (eqU32 (hdSpkId (qHdr (v x))) (u32OfNat (qJ (v x))))
        (eqU32 (hdPqspkId (qHdr (v x))) (u32OfNat (qJ (v x)))))
        (optU32Eq (hdOpkId (qHdr (v x))) .none))
        (natEq (lenB (hdIkAPk (qHdr (v x)))) (.nat 32)))
        (natEq (lenB (hdEkAPk (qHdr (v x)))) (.nat 32))))
      (.ret .none) <|
    .ite (eAny K (stUsedN (v st)) fun e => nat3Eq (qKJO (v x)) (v e)) (.ret .none) <|
    bindV (koskSenderOkC S K st (hdIkAPk (qHdr (v x)))) fun ok =>
    .ite (.not (v ok)) (.ret .none) <|
    caseOptV (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (qK (v x)))
      (.ret .none) fun kE =>
    caseOptV (eFind K (stSpks (v st)) fun e => nat2Eq (.fst (v e)) (.pair (qK (v x)) (qJ (v x))))
      (.ret .none) fun bE =>
    letV (kyberCheckE K (stKyb (v st)) (.pair (qK (v x)) (.pair (hdPqspkId (qHdr (v x)))
        (.pair (hdSpkId (qHdr (v x))) (hdEkAPk (qHdr (v x))))))) fun rk =>
    bindV (acceptKeysC (.pair (peSecIKA0 (.snd (v kE))) (.pair (sbSpkSk (.snd (v bE)))
        (.pair .none (.pair (sbPqspkSk (.snd (v bE)))
          (.pair (.fst (v rk)) (qHdr (v x)))))))) fun acc =>
    caseOptV (v acc) (.ret .none) fun _ =>
    bindV (qKemDecaps (.pair (sbPqspkSk (.snd (v bE))) (hdKemCt (qHdr (v x))))) fun ss? =>
    caseOptV (v ss?) (.ret .none) fun ss =>
    bindV (qX25519 (.pair (sbSpkSk (.snd (v bE))) (hdIkAPk (qHdr (v x))))) fun dh1 =>
    bindV (qX25519 (.pair (peSecIKA0 (.snd (v kE))) (hdEkAPk (qHdr (v x))))) fun dh2 =>
    bindV (qX25519 (.pair (sbSpkSk (.snd (v bE))) (hdEkAPk (qHdr (v x))))) fun dh3 =>
    let stMid := stUpd (v st)
      (usedN := .cons (qKJO (v x)) (stUsedN (v st)))
      (kyb := .snd (v rk))
    .ret (.some (.pair (buildSecretsE (v dh1) (v dh2) (v dh3) .none (v ss))
      (.pair stMid (.pair (v kE) (.pair (v bE) .none)))))

@[expose] def shcrAcceptPreRoC (S : Setup) (K : Nat) (opk : Bool) :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface
      [shcrStTy, accQTy] (.opt shcrAccMidTy) :=
  let s : Var [shcrStTy, accQTy] shcrStTy := .zero
  let x : Var [shcrStTy, accQTy] accQTy := .succ .zero
  letV (scBase (v s)) fun st =>
  coreAcceptPreRoC S K opk st x

@[expose] def shcrAcceptPostRoC (S : Setup) (K : Nat) (opk : Bool) :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface
      [_root_.SignalPqxdh.LegacyCosted.drKeyT, roListLegacyTy, shcrAccMidTy, shcrStTy, accQTy]
      SCS :=
  let Δ     : List PT :=
    [_root_.SignalPqxdh.LegacyCosted.drKeyT, roListLegacyTy, shcrAccMidTy, shcrStTy, accQTy]
  let dk    : Var Δ _root_.SignalPqxdh.LegacyCosted.drKeyT := .zero
  let roNew : Var Δ roListLegacyTy := .succ .zero
  let mid   : Var Δ shcrAccMidTy := .succ (.succ .zero)
  let s     : Var Δ shcrStTy := .succ (.succ (.succ .zero))
  let x     : Var Δ accQTy := .succ (.succ (.succ (.succ .zero)))
  letV (scBase (v s)) fun stOrig =>
  letV (stUpd (.fst (.snd (v mid))) (ro := v roNew)) fun st1 =>
  letV (.fst (.snd (.snd (v mid)))) fun kE =>
  letV (.fst (.snd (.snd (.snd (v mid))))) fun bE =>
  letV (.snd (.snd (.snd (.snd (v mid))))) fun opkPk? =>
  let sidE : Expr pqxdhOps _ _root_.SignalPqxdh.LegacyCosted.sidT :=
    if opk then .inr (.inr (.inl (qKJO (v x)))) else .inr (.inr (.inr (qKJO (v x))))
  bindV (findHonestC S K stOrig (hdIkAPk (qHdr (v x)))) fun sh =>
  bindV (recordRespC S K (.pair (reMk sidE (peIkAPk (.snd (v kE)))
      (sbSpkPk (.snd (v bE))) (v opkPk?) (sbPqspkPk (.snd (v bE))) (qHdr (v x))
      (isSomeE (v sh)) (v dk) (v dk) (.bool false) (.bool false)) (v st1))) fun st2 =>
  bindV (findHonestC S K stOrig (hdIkAPk (qHdr (v x)))) fun sh2 =>
  let respE := eCaseOpt (v sh2) (rDrKey (v dk)) fun _ => rAccFresh
  letV (.pair respE (scUpd (v s) (base := v st2))) fun r =>
  .ite (isNoneRespE (.fst (v r))) (.ret (v r)) <|
  caseOptV (eFind K (stSpks (scBase (.snd (v r)))) fun e =>
      nat2Eq (.fst (v e)) (.pair (qK (v x)) (qJ (v x))))
    (.ret (v r)) fun bE2 =>
  bindV (qKemDecaps (.pair (sbPqspkSk (.snd (v bE2))) (hdKemCt (qHdr (v x))))) fun ss? =>
  caseOptV (v ss?) (.ret (v r)) fun ss =>
  .ret (.pair (.fst (v r)) (scUpd (.snd (v r)) (rR := .cons
    (.pair (.nat 0)
      (.pair (qK (v x)) (.pair (qJ (v x)) (.pair (sbPqspkPk (.snd (v bE2)))
        (.pair (sbPqspkSk (.snd (v bE2))) (.pair (hdKemCt (qHdr (v x))) (v ss)))))))
    (scRR (.snd (v r))))))

@[expose] def shcrInitPrin1KeyLeg (K : Nat) :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface [shcrStTy, .nat] SCS :=
  onBase (Γ₁ := [shcrStTy, .nat]) .zero fun g =>
    initPrin1KeyB K g (.succ (.succ .zero) : Var [keyIndStateTy, shcrStTy, .nat] .nat)

@[expose] def shcrInitPrin2KeyLeg (K : Nat) :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface [shcrStTy, .nat] SCS :=
  onBase (Γ₁ := [shcrStTy, .nat]) .zero fun g =>
    initPrinB K g (.succ (.succ .zero) : Var [keyIndStateTy, shcrStTy, .nat] .nat)

@[expose] def shcrCorruptLeg (K : Nat) :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface [shcrStTy, .nat] SCS :=
  onBase (Γ₁ := [shcrStTy, .nat]) .zero fun g =>
    corruptB K g (.succ (.succ .zero) : Var [keyIndStateTy, shcrStTy, .nat] .nat)

@[expose] def shcrGenSpkLeg (S : Setup) (K : Nat) :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface
      [shcrStTy, .prod .nat .nat] SCS :=
  shcrGenSpkB S K (Γ₁ := [shcrStTy, .prod .nat .nat]) (Γ₂ := [shcrStTy, .prod .nat .nat])
    .zero (.succ .zero)

@[expose] def shcrActiveGenSpkLeg (_S : Setup) (K : Nat) :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface
      [shcrStTy, .prod .nat .nat] SCS :=
  let s : Var [shcrStTy, .prod .nat .nat] shcrStTy := .zero
  let x : Var [shcrStTy, .prod .nat .nat] (.prod .nat .nat) := .succ .zero
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

@[expose] def shcrGenOpkLeg (K : Nat) :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface
      [shcrStTy, .prod .nat (.prod .nat .nat)] SCS :=
  onBase (Γ₁ := [shcrStTy, .prod .nat (.prod .nat .nat)]) .zero
    fun g => genOpkB K g
      (.succ (.succ .zero) :
        Var [keyIndStateTy, shcrStTy, .prod .nat (.prod .nat .nat)]
          (.prod .nat (.prod .nat .nat)))

@[expose] def shcrTestLeg (K : Nat) :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface
      [shcrStTy, _root_.SignalPqxdh.LegacyCosted.sidT] SCS :=
  onBase (Γ₁ := [shcrStTy, _root_.SignalPqxdh.LegacyCosted.sidT]) .zero
    fun g => testB K g
      (.succ (.succ .zero) :
        Var [keyIndStateTy, shcrStTy, _root_.SignalPqxdh.LegacyCosted.sidT]
          _root_.SignalPqxdh.LegacyCosted.sidT)

@[expose] def shcrRevDhLeg (K : Nat) :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface [shcrStTy, .unit] SCS :=
  onBase (Γ₁ := [shcrStTy, .unit]) .zero fun g => revealDhB true K g

@[expose] def shcrRevSessLeg (K : Nat) :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface
      [shcrStTy, _root_.SignalPqxdh.LegacyCosted.sidT] SCS :=
  onBase (Γ₁ := [shcrStTy, _root_.SignalPqxdh.LegacyCosted.sidT]) .zero
    fun g => revealB K g
      (.succ (.succ .zero) :
        Var [keyIndStateTy, shcrStTy, _root_.SignalPqxdh.LegacyCosted.sidT]
          _root_.SignalPqxdh.LegacyCosted.sidT)

@[expose] def shcrRegKeyLeg :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface
      [shcrStTy, _root_.SignalPqxdh.LegacyCosted.B 32] SCS :=
  onBase (Γ₁ := [shcrStTy, _root_.SignalPqxdh.LegacyCosted.B 32]) .zero
    fun g => registerB g
      (.succ (.succ .zero) :
        Var [keyIndStateTy, shcrStTy, _root_.SignalPqxdh.LegacyCosted.B 32]
          (_root_.SignalPqxdh.LegacyCosted.B 32))

@[expose] def shcrRevSpkLeg (K : Nat) :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface
      [shcrStTy, .prod .nat .nat] SCS :=
  onBase (Γ₁ := [shcrStTy, .prod .nat .nat]) .zero
    fun g => revealSpkB K g
      (.succ (.succ .zero) :
        Var [keyIndStateTy, shcrStTy, .prod .nat .nat] (.prod .nat .nat))

@[expose] def shcrChDoneLeg :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface
      [shcrStTy, .bool] (_root_.SignalPqxdh.LegacyCosted.B 1568) :=
  .ret (scTPk (.var .zero))

@[expose] def shcrExtractLeg (K : Nat) :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface
      [shcrStTy, .bool,
       .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)]
      (_root_.SignalPqxdh.LegacyCosted.B 1568) :=
  shcrExtractC
    (Γ₁ := [.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)])
    (Γ₃ := [shcrStTy, .bool,
            .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)])
    (Δ := [shcrStTy, .bool,
           .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)])
    K .zero .zero

end LegacySplits

@[expose] def atomicRNoneE {S : Setup} {Γ : List (Ty pqAtomicSig)} :
    Expr pqAtomicOps Γ ((pqKeyIndCodec S).R) :=
  .inl .unit

@[expose] def finPairToNatE (n1 n2 : ℕ) {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ (.prod (.base (.fin n1)) (.base (.fin n2)))) :
    Expr pqAtomicOps Γ (.prod .nat .nat) :=
  .pair (aop (.finVal n1) (.fst e)) (aop (.finVal n2) (.snd e))

@[expose] def finTripleToNatE (n1 n2 n3 : ℕ) {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ
      (.prod (.base (.fin n1)) (.prod (.base (.fin n2)) (.base (.fin n3))))) :
    Expr pqAtomicOps Γ (.prod .nat (.prod .nat .nat)) :=
  .pair (aop (.finVal n1) (.fst e))
    (.pair (aop (.finVal n2) (.fst (.snd e))) (aop (.finVal n3) (.snd (.snd e))))

@[expose] def initPayToNatE (N_s : ℕ) (S : Setup) {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ
      (.prod (.base (.fin S.N_id)) (.prod (.base (.fin N_s)) (bundleT (ℓ := 0) (Pt := Empty))))) :
    Expr pqAtomicOps Γ (embedTy _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initQTy) :=
  .pair (aop (.finVal S.N_id) (.fst e))
    (.pair (aop (.finVal N_s) (.fst (.snd e))) (.snd (.snd e)))

@[expose] def accPayToNatE (N_o : ℕ) (S : Setup) {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_recv))
          (.prod (.base (.fin N_o)) (hdrT (ℓ := 0) (Pt := Empty)))))) :
    Expr pqAtomicOps Γ (embedTy _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.accQTy) :=
  .pair (aop (.finVal S.N_id) (.fst e))
    (.pair (aop (.finVal S.N_recv) (.fst (.snd e)))
      (.pair (aop (.finVal N_o) (.fst (.snd (.snd e)))) (.snd (.snd (.snd e)))))

@[expose] def wkRen1 {Γ' : List (Ty pqAtomicSig)} {A B a : Ty pqAtomicSig} :
    Var (A :: Γ') a → Var (A :: B :: Γ') a
  | .zero => .zero
  | .succ v => .succ (.succ v)

/-- Outermost 14-way `.caseSum` query dispatcher for `(pqKeyIndCodec S).Q`. -/
@[expose] def dispatchKeyIndQ {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (S : Setup) {Γ : List (Ty pqAtomicSig)} {R : Ty pqAtomicSig}
    (qE : Expr pqAtomicOps Γ ((pqKeyIndCodec S).Q))
    (onInitPrin  : Comp pqAtomicOps I (.base (.fin S.N_id) :: Γ) R)
    (onCorrupt   : Comp pqAtomicOps I (.base (.fin S.N_id) :: Γ) R)
    (onGenSpk    : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)) :: Γ) R)
    (onGenOpk    : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_recv)) (.base (.fin S.N_opk))) :: Γ) R)
    (onInitOpk   : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_send_opk)) (bundleT (ℓ := 0) (Pt := Empty))) :: Γ) R)
    (onInitNoOpk : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_send_no_opk)) (bundleT (ℓ := 0) (Pt := Empty))) :: Γ) R)
    (onAccOpk    : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_recv))
          (.prod (.base (.fin S.N_opk)) (hdrT (ℓ := 0) (Pt := Empty)))) :: Γ) R)
    (onAccNoOpk  : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_recv))
          (.prod (.base (.fin S.N_no_opk)) (hdrT (ℓ := 0) (Pt := Empty)))) :: Γ) R)
    (onTest      : Comp pqAtomicOps I (sidT (ℓ := 0) (Pt := Empty) S :: Γ) R)
    (onRo        : Comp pqAtomicOps I (PB 192 :: Γ) R)
    (onRevDh     : Comp pqAtomicOps I (.unit :: Γ) R)
    (onRevSess   : Comp pqAtomicOps I (sidT (ℓ := 0) (Pt := Empty) S :: Γ) R)
    (onRegKey    : Comp pqAtomicOps I (PB 32 :: Γ) R)
    (onRevSpk    : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)) :: Γ) R) :
    Comp pqAtomicOps I Γ R :=
  let wk1 {Γ' : List (Ty pqAtomicSig)} {A B : Ty pqAtomicSig}
      (c : Comp pqAtomicOps I (A :: Γ') R) : Comp pqAtomicOps I (A :: B :: Γ') R :=
    compRename wkRen1 c
  .caseSum qE onInitPrin <|
  .caseSum .v0 (wk1 onCorrupt) <|
  .caseSum .v0 (wk1 (wk1 onGenSpk)) <|
  .caseSum .v0 (wk1 (wk1 (wk1 onGenOpk))) <|
  .caseSum .v0 (wk1 (wk1 (wk1 (wk1 onInitOpk)))) <|
  .caseSum .v0 (wk1 (wk1 (wk1 (wk1 (wk1 onInitNoOpk))))) <|
  .caseSum .v0 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 onAccOpk)))))) <|
  .caseSum .v0 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 onAccNoOpk))))))) <|
  .caseSum .v0 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 onTest)))))))) <|
  .caseSum .v0 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 onRo))))))))) <|
  .caseSum .v0 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 onRevDh)))))))))) <|
  .caseSum .v0 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 onRevSess))))))))))) <|
  .caseSum .v0
    (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 onRegKey))))))))))))
    (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 (wk1 onRevSpk))))))))))))

@[expose] def ren2 {Γ : List (Ty pqAtomicSig)} {A B a : Ty pqAtomicSig} :
    Var [A, B] a → Var (A :: B :: Γ) a
  | .zero => .zero
  | .succ .zero => .succ .zero

@[expose] def ren3 {Γ : List (Ty pqAtomicSig)} {A B C a : Ty pqAtomicSig} :
    Var [A, B, C] a → Var (A :: B :: C :: Γ) a
  | .zero => .zero
  | .succ .zero => .succ .zero
  | .succ (.succ .zero) => .succ (.succ .zero)

@[expose] def ren4 {Γ : List (Ty pqAtomicSig)} {A B C D a : Ty pqAtomicSig} :
    Var [A, B, C, D] a → Var (A :: B :: C :: D :: Γ) a
  | .zero => .zero
  | .succ .zero => .succ .zero
  | .succ (.succ .zero) => .succ (.succ .zero)
  | .succ (.succ (.succ .zero)) => .succ (.succ (.succ .zero))

@[expose] def ren5 {Γ : List (Ty pqAtomicSig)} {A B C D E a : Ty pqAtomicSig} :
    Var [A, B, C, D, E] a → Var (A :: B :: C :: D :: E :: Γ) a
  | .zero => .zero
  | .succ .zero => .succ .zero
  | .succ (.succ .zero) => .succ (.succ .zero)
  | .succ (.succ (.succ .zero)) => .succ (.succ (.succ .zero))
  | .succ (.succ (.succ (.succ .zero))) => .succ (.succ (.succ (.succ .zero)) )

@[expose] def ren6 {Γ : List (Ty pqAtomicSig)} {A B C D E F a : Ty pqAtomicSig} :
    Var [A, B, C, D, E, F] a → Var (A :: B :: C :: D :: E :: F :: Γ) a
  | .zero => .zero
  | .succ .zero => .succ .zero
  | .succ (.succ .zero) => .succ (.succ .zero)
  | .succ (.succ (.succ .zero)) => .succ (.succ (.succ .zero))
  | .succ (.succ (.succ (.succ .zero))) => .succ (.succ (.succ (.succ .zero)))
  | .succ (.succ (.succ (.succ (.succ .zero)))) => .succ (.succ (.succ (.succ (.succ .zero))))

@[expose] def wkTop3 {A B C X a : Ty pqAtomicSig} :
    Var [A, B, C] a → Var [X, A, B, C] a
  | .zero => .succ .zero
  | .succ .zero => .succ (.succ .zero)
  | .succ (.succ .zero) => .succ (.succ (.succ .zero))

@[expose] def runAt2 {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B)
    (c : Comp pqAtomicOps I [A, B] R) : Comp pqAtomicOps I Γ R :=
  .bind (.ret bE)
    (.bind (.ret (exprRename .succ aE))
      (compRename ren2 c))

@[expose] def runAt3 {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B C R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B) (cE : Expr pqAtomicOps Γ C)
    (m : Comp pqAtomicOps I [A, B, C] R) : Comp pqAtomicOps I Γ R :=
  .bind (.ret cE)
    (.bind (.ret (exprRename .succ bE))
      (.bind (.ret (exprRename (fun v => .succ (.succ v)) aE))
        (compRename ren3 m)))

@[expose] def runAt4 {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B C D R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B)
    (cE : Expr pqAtomicOps Γ C) (dE : Expr pqAtomicOps Γ D)
    (m : Comp pqAtomicOps I [A, B, C, D] R) : Comp pqAtomicOps I Γ R :=
  .bind (.ret dE)
    (.bind (.ret (exprRename .succ cE))
      (.bind (.ret (exprRename (fun v => .succ (.succ v)) bE))
        (.bind (.ret (exprRename (fun v => .succ (.succ (.succ v))) aE))
          (compRename ren4 m))))

@[expose] def runAt5 {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B C D E R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B)
    (cE : Expr pqAtomicOps Γ C) (dE : Expr pqAtomicOps Γ D) (eE : Expr pqAtomicOps Γ E)
    (m : Comp pqAtomicOps I [A, B, C, D, E] R) : Comp pqAtomicOps I Γ R :=
  .bind (.ret eE)
    (.bind (.ret (exprRename .succ dE))
      (.bind (.ret (exprRename (fun v => .succ (.succ v)) cE))
        (.bind (.ret (exprRename (fun v => .succ (.succ (.succ v))) bE))
          (.bind (.ret (exprRename (fun v => .succ (.succ (.succ (.succ v)))) aE))
            (compRename ren5 m)))))

@[expose] def runAt6 {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B C D E F R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B) (cE : Expr pqAtomicOps Γ C)
    (dE : Expr pqAtomicOps Γ D) (eE : Expr pqAtomicOps Γ E) (fE : Expr pqAtomicOps Γ F)
    (m : Comp pqAtomicOps I [A, B, C, D, E, F] R) : Comp pqAtomicOps I Γ R :=
  .bind (.ret fE)
    (.bind (.ret (exprRename .succ eE))
      (.bind (.ret (exprRename (fun v => .succ (.succ v)) dE))
        (.bind (.ret (exprRename (fun v => .succ (.succ (.succ v))) cE))
          (.bind (.ret (exprRename (fun v => .succ (.succ (.succ (.succ v)))) bE))
            (.bind (.ret (exprRename (fun v => .succ (.succ (.succ (.succ (.succ v))))) aE))
              (compRename ren6 m))))))

@[expose] def ren1 {Γ : List (Ty pqAtomicSig)} {A a : Ty pqAtomicSig} :
    Var [A] a → Var (A :: Γ) a
  | .zero => .zero

@[expose] def shcrRoListAtomicE {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ (embedTy _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.shcrStTy)) :
    Expr pqAtomicOps Γ roListAtomicTy :=
  .letE sE (exprRename ren1
    (mapExpr (shcrGetRoE (Γ := [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.shcrStTy])
      (.var .zero))))

@[expose] def shcrLiftLegArmK (S : Setup) {A : Ty pqAtomicSig}
    {P : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    (payE : Expr pqAtomicOps [A, shcrKindStTy, (pqKeyIndCodec S).Q] (embedTy P))
    (leg : Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps
      _root_.SignalPqxdh.LegacyCosted.pqPrimIface
      [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.shcrStTy, P]
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.SCS) :
    Comp pqAtomicOps pqPrimIface [A, shcrKindStTy, (pqKeyIndCodec S).Q]
      (.prod ((pqKeyIndCodec S).R) shcrKindStTy) :=
  .bind (runAt2 (.fst .v1) payE (mapComp tlPrimKeyInd leg))
    (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd .v2))))

@[expose] def shcrRoArmK (S : Setup) (capRo : ℕ) :
    Comp pqAtomicOps pqPrimIface [PB 192, shcrKindStTy, (pqKeyIndCodec S).Q]
      (.prod ((pqKeyIndCodec S).R) shcrKindStTy) :=
  .bind (roShadowQueryC tlPrimKeyInd capRo (shcrRoListAtomicE (.fst .v1)) (.snd .v1) .v0)
    (.bind (runAt3 (.fst .v0) (.fst (.snd .v0)) (.fst .v2) (mapComp tlPrimKeyInd shcrSetRoRespC))
      (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd (.snd .v1))))))

@[expose] def shcrInitArmPostK (S : Setup) (K_on capRo N_s : ℕ) (opk : Bool) :
    Comp pqAtomicOps pqPrimIface
      [.prod (.base (.fin S.N_id)) (.prod (.base (.fin N_s)) (bundleT (ℓ := 0) (Pt := Empty))),
       shcrKindStTy, (pqKeyIndCodec S).Q]
      (.prod ((pqKeyIndCodec S).R) shcrKindStTy) :=
  .bind (runAt2 (.fst .v1) (initPayToNatE N_s S .v0)
    (mapComp tlPrimKeyInd (shcrInitiatePreRoC S K_on opk)))
    (.caseSum .v0
      (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd .v3))))
      (.bind (roShadowQueryC tlPrimKeyInd capRo
          (shcrRoListAtomicE (.fst .v3)) (.snd .v3) (.fst .v0))
        (.bind (runAt4 (.fst .v0) (.fst (.snd .v0)) .v1 (.fst .v4)
          (mapComp tlPrimKeyInd (shcrInitiatePostRoC S K_on)))
          (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd (.snd .v1))))))))

@[expose] def shcrInitArmPreK (S : Setup) (K_on capRo N_s : ℕ) (opk : Bool) :
    Comp pqAtomicOps pqPrimIface
      [.prod (.base (.fin S.N_id)) (.prod (.base (.fin N_s)) (bundleT (ℓ := 0) (Pt := Empty))),
       shcrKindStTy, (pqKeyIndCodec S).Q]
      (.sum (.prod ((pqKeyIndCodec S).R) shcrKindStTy)
            (.prod (PB 1568)
              (.prod (embedTy _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.pauseTy)
                     shcrKindStTy))) :=
  .bind (runAt2 (.fst .v1) (initPayToNatE N_s S .v0)
    (mapComp tlPrimKeyInd (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.tryPauseC S K_on opk
      (Γ₁ := [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.shcrStTy,
              _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initQTy])
      (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initQTy])
      (Δ := [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.shcrStTy,
             _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initQTy]) .zero .zero)))
    (.caseOpt .v0
      (.bind (compRename wkTop3 (shcrInitArmPostK S K_on capRo N_s opk))
        (.ret (.inl .v0)))
      (.ret (.inr (.pair (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.fst (.snd .v0)))))))))
        (.pair .v0 .v3)))))

@[expose] def shcrAccArmPostK (S : Setup) (K_on capRo N_o : ℕ) (opk : Bool) :
    Comp pqAtomicOps pqPrimIface
      [.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_recv))
          (.prod (.base (.fin N_o)) (hdrT (ℓ := 0) (Pt := Empty)))),
       shcrKindStTy, (pqKeyIndCodec S).Q]
      (.prod ((pqKeyIndCodec S).R) shcrKindStTy) :=
  .bind (runAt2 (.fst .v1) (accPayToNatE N_o S .v0)
    (mapComp tlPrimKeyInd (shcrAcceptPreRoC S K_on opk)))
    (.caseOpt .v0
      (.ret (.pair atomicRNoneE .v2))
      (.bind (roShadowQueryC tlPrimKeyInd capRo
          (shcrRoListAtomicE (.fst .v3)) (.snd .v3) (.fst .v0))
        (.bind (runAt5 (.fst .v0) (.fst (.snd .v0)) .v1 (.fst .v4) (accPayToNatE N_o S .v3)
          (mapComp tlPrimKeyInd (shcrAcceptPostRoC S K_on opk)))
          (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd (.snd .v1))))))))

/-- Shadow-indexed post-pause `KemShCr` query handler (`oneKey = true` selects 1-key active arms). -/
@[expose] def shcrKindHandlePostC (oneKey : Bool) (S : Setup) (K_on capRo : ℕ) :
    Comp pqAtomicOps pqPrimIface [shcrKindStTy, (pqKeyIndCodec S).Q]
      (.prod ((pqKeyIndCodec S).R) shcrKindStTy) :=
  let initLeg   := if oneKey then shcrInitPrin1KeyLeg K_on else shcrInitPrin2KeyLeg K_on
  let genSpkLeg := if oneKey then shcrActiveGenSpkLeg S K_on else shcrGenSpkLeg S K_on
  dispatchKeyIndQ S .v1
    (shcrLiftLegArmK S (P := .nat) (aop (.finVal S.N_id) .v0) initLeg)
    (shcrLiftLegArmK S (P := .nat) (aop (.finVal S.N_id) .v0) (shcrCorruptLeg K_on))
    (shcrLiftLegArmK S (P := .prod .nat .nat) (finPairToNatE S.N_id S.N_recv .v0) genSpkLeg)
    (shcrLiftLegArmK S (P := .prod .nat (.prod .nat .nat))
      (finTripleToNatE S.N_id S.N_recv S.N_opk .v0) (shcrGenOpkLeg K_on))
    (shcrInitArmPostK S K_on capRo S.N_send_opk true)
    (shcrInitArmPostK S K_on capRo S.N_send_no_opk false)
    (shcrAccArmPostK S K_on capRo S.N_opk true)
    (shcrAccArmPostK S K_on capRo S.N_no_opk false)
    (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.sidT)
      (finSidToNatExpr S .v0) (shcrTestLeg K_on))
    (shcrRoArmK S capRo)
    (shcrLiftLegArmK S (P := .unit) .unit (shcrRevDhLeg K_on))
    (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.sidT)
      (finSidToNatExpr S .v0) (shcrRevSessLeg K_on))
    (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.B 32) .v0 shcrRegKeyLeg)
    (shcrLiftLegArmK S (P := .prod .nat .nat)
      (finPairToNatE S.N_id S.N_recv .v0) (shcrRevSpkLeg K_on))

/-- Shadow-indexed pre-pause `KemShCr` query handler (`oneKey = true` selects 1-key active arms). -/
@[expose] def shcrKindHandlePreC (oneKey : Bool) (S : Setup) (K_on capRo : ℕ) :
    Comp pqAtomicOps pqPrimIface [shcrKindStTy, (pqKeyIndCodec S).Q]
      (.sum (.prod ((pqKeyIndCodec S).R) shcrKindStTy)
            (.prod (PB 1568)
              (.prod (embedTy _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.pauseTy)
                     shcrKindStTy))) :=
  let initLeg   := if oneKey then shcrInitPrin1KeyLeg K_on else shcrInitPrin2KeyLeg K_on
  let genSpkLeg := if oneKey then shcrActiveGenSpkLeg S K_on else shcrGenSpkLeg S K_on
  let wrapInl {A} (c : Comp pqAtomicOps pqPrimIface [A, shcrKindStTy, (pqKeyIndCodec S).Q]
      (.prod ((pqKeyIndCodec S).R) shcrKindStTy)) :
      Comp pqAtomicOps pqPrimIface [A, shcrKindStTy, (pqKeyIndCodec S).Q] _ :=
    .bind c (.ret (.inl .v0))
  dispatchKeyIndQ S .v1
    (wrapInl (shcrLiftLegArmK S (P := .nat) (aop (.finVal S.N_id) .v0) initLeg))
    (wrapInl (shcrLiftLegArmK S (P := .nat) (aop (.finVal S.N_id) .v0) (shcrCorruptLeg K_on)))
    (wrapInl (shcrLiftLegArmK S (P := .prod .nat .nat)
      (finPairToNatE S.N_id S.N_recv .v0) genSpkLeg))
    (wrapInl (shcrLiftLegArmK S (P := .prod .nat (.prod .nat .nat))
      (finTripleToNatE S.N_id S.N_recv S.N_opk .v0) (shcrGenOpkLeg K_on)))
    (shcrInitArmPreK S K_on capRo S.N_send_opk true)
    (shcrInitArmPreK S K_on capRo S.N_send_no_opk false)
    (wrapInl (shcrAccArmPostK S K_on capRo S.N_opk true))
    (wrapInl (shcrAccArmPostK S K_on capRo S.N_no_opk false))
    (wrapInl (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.sidT)
      (finSidToNatExpr S .v0) (shcrTestLeg K_on)))
    (wrapInl (shcrRoArmK S capRo))
    (wrapInl (shcrLiftLegArmK S (P := .unit) .unit (shcrRevDhLeg K_on)))
    (wrapInl (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.sidT)
      (finSidToNatExpr S .v0) (shcrRevSessLeg K_on)))
    (wrapInl (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.B 32) .v0 shcrRegKeyLeg))
    (wrapInl (shcrLiftLegArmK S (P := .prod .nat .nat)
      (finPairToNatE S.N_id S.N_recv .v0) (shcrRevSpkLeg K_on)))

@[expose] def shcrKindChDoneC :
    Comp pqAtomicOps pqPrimIface [shcrKindStTy, .bool] (PB 1568) :=
  runAt2 (.fst .v0) .v1 (mapComp tlPrimKeyInd shcrChDoneLeg)

/-- Shadow-indexed `KemShCr` resume stage updating both `stRo` and `roAvl`. -/
@[expose] def shcrKindResumeC (S : Setup) (K_on capRo : ℕ) :
    Comp pqAtomicOps pqPrimIface
      [shcrKindStTy,
       embedTy _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.pauseTy,
       .prod (PB 32) (PB 1568)]
      (.prod ((pqKeyIndCodec S).R) shcrKindStTy) :=
  .bind (runAt3 (.fst .v0) .v1 .v2 (mapComp tlPrimKeyInd shcrResumePreRoC))
    (.bind (roShadowQueryC tlPrimKeyInd capRo
        (shcrRoListAtomicE (.fst .v1)) (.snd .v1) (.fst .v0))
      (.bind (runAt6 (.fst .v0) (.fst (.snd .v0)) (.snd .v1) (.fst .v2) .v3 .v4
        (mapComp tlPrimKeyInd (shcrResumePostRoC S K_on)))
        (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd (.snd .v1)))))))

@[expose] def shcrKindFinishC (K_on : ℕ) :
    Comp pqAtomicOps pqPrimIface
      [shcrKindStTy, .bool, .prod (PB 32) (PB 1568)]
      (PB 1568) :=
  runAt3 (.fst .v0) .v1 .v2 (mapComp tlPrimKeyInd (shcrExtractLeg K_on))

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK
