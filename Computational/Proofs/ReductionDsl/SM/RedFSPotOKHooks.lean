/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.RedFS -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Potential -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.Notation

/-!
# Hook-level potential bounds for FS-AEAD reductions

Defines the invariant-carrying potential predicate `PotOKInvFS`, the one-credit hook potential
`fsHPot`, and the virtual-party invariant `fsVpInv`, and proves potential preservation for
`hooksFSC`, `vSendC`, and `vRecvC`.
-/

namespace Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks

public section

set_option autoImplicit false

open OracleSpec OracleComp
open _root_.ReductionDsl
  (Sig Ty Ops Iface Env Expr Comp GameCodec CostedReduction handlerImpl isGameQuery)
open _root_.CryptoGames (Party)
open _root_.CryptoGames.CKA (CKASamp CKAOp ckaSMQ ckaSMR ckaHdrTy ckaHdrCtTy ckaPsTy)
open _root_.CryptoGames.PRFPRNG (prngSig prngOps fsaeadHeaderAdIface prngSMCodec FSHdrTag)
open _root_.CryptoGames.SM
  (Adversary MakesAtMostQueries posTy partyEnc partyDec partyDec_partyEnc sendsInE otherE pGet pSet
   orE isSomeE letE_eval pair_eval ite_eval some_eval orE_eval sendsInE_eval)
open _root_.CryptoGames.SM.Engine
  (HooksC ConfigEC Policy modeCfgEC cRecTy cGsTy esTy
   esG esH esAbort esMk esSetG esSetH esSetAbort
   cGsSt cGsEpoch cGsWin cGsB cGsMk cGsSetStP cGsSetWin cRecPos cRecMsg
   cSafeChE cCorrAllowedE corrDoomE
   cLeakE cEpMgmtE cDeleteE cAcceptE cRecordE cAfterCorrE
   mkPartiesE realPartyE cGsInitE
   vpMk vpId vpTcur vpTcurNat vpΓ vpRoot vpVS vpVR vpSetVS vpSetVR
   vSendStep1C vSendC vRecvStep1C vRecvC commitEC
   transmitEC challEC deliverEC injectEC corrEC implEC
   eval_bind eval_bind_ret eval_ret)
open _root_.CryptoGames.SM.Construction
  (Header PartyState Mode
   fsHsTy fsVpTy fsEsTy
   fsHsCache fsHsTable fsHsSessions fsHsTrans fsHsCount fsHsSCorr fsHsExt fsHsMk
   fsHsSetCache fsHsSetTable fsHsSetSessions fsHsSetTrans fsHsSetCountTrans fsHsSetSCorr fsHsSetExt
   fsHsEmptyE tableLookupE lookupFC lookupFC_queries
   isExtE extOfE
   rootFSC rootFSC_queries fsStartSendC fsStartSendC_queries fsStartRecvC fsStartRecvC_queries
   fsFsSendC fsFsSendC_queries fsFsSendC_decQueries
   fsTransFindE fsTransFilterE fsFsRecvC fsFsRecvC_queries fsFsRecvC_decQueries
   fsCommitC fsCommitC_queries rangeListC rangeListC_queries unliftEntryE unliftVRE
   fsRevealC fsRevealC_queries fsRevealC_decQueries
   hooksFSC)

section FsPotOK

variable
  {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E}
  {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I} {sampK : ProbComp K}

local notation "S" => prngSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hsTy" => fsHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "vpTyFS" => fsVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "esTyFS" => fsEsTy KC Γ CCoins T I KR RSt K SS RS M E

local notation "OO" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

local notation "II" =>
  fsaeadHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

local notation "P_fs" => isGameQuery (G := CryptoGames.FSAEAD.spec SS RS (Header T) M E)

/-- Per-party invariant ensuring externalized sender and receiver states at `tStar` have disjoint
party polarities. -/
@[expose] def fsVpInv (tStar : ℕ) (vp : (vpTyFS).denote) : Prop :=
  (vp.2.2.1 = some none → (partyDec vp.1).sendsIn tStar = true) ∧
  (vp.2.2.2.1 tStar = some none → (partyDec vp.1).sendsIn tStar = false)

@[expose] def fsEsInv (tStar : ℕ) (es : (esTyFS).denote) : Prop :=
  fsVpInv (KC := KC) (CCoins := CCoins) (I := I) (KR := KR) (K := K) (M := M) (E := E)
    tStar es.1.1.1 ∧
  fsVpInv (KC := KC) (CCoins := CCoins) (I := I) (KR := KR) (K := K) (M := M) (E := E)
    tStar es.1.1.2

/-- One-credit hook potential: `1` while neither `.cs` nor `.cr` has run, and `0` thereafter. -/
@[expose] def fsHPot (h : (hsTy).denote) : ℕ :=
  if !h.2.2.2.2.2.1 && h.2.2.2.2.2.2.isNone then 1 else 0

@[expose] def fsPot (es : (esTyFS).denote) : ℕ :=
  fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) es.2.1

theorem fsHPot_le_one (h : (hsTy).denote) :
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) h ≤ 1 := by
  unfold fsHPot; split <;> omega

theorem fsPot_le_one (es : (esTyFS).denote) :
    fsPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) es ≤ 1 :=
  fsHPot_le_one es.2.1

theorem pGet_eval_st_fs {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (st : Expr O' Γ' (.prod vpT vpT)) (p : Expr O' Γ' .bool) (ρ : Env Γ') :
    (pGet st p).eval ρ = if p.eval ρ then (st.eval ρ).2 else (st.eval ρ).1 := by
  cases hp : (p.eval ρ : Bool) <;> simp [pGet, Expr.eval, Expr.v0, hp]

theorem pSet_eval_st_fs {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (st : Expr O' Γ' (.prod vpT vpT)) (p : Expr O' Γ' .bool) (v : Expr O' Γ' vpT) (ρ : Env Γ') :
    (pSet st p v).eval ρ =
      if p.eval ρ then ((st.eval ρ).1, v.eval ρ) else (v.eval ρ, (st.eval ρ).2) := by
  cases hp : (p.eval ρ : Bool) <;> simp [pSet, Expr.eval, Expr.v0, hp]

theorem fsVpInv_pGet (tStar : ℕ) (stAB : (vpTyFS).denote × (vpTyFS).denote) (p : Bool)
    (hAB : fsVpInv tStar stAB.1 ∧ fsVpInv tStar stAB.2) :
    fsVpInv tStar (if p then stAB.2 else stAB.1) := by
  cases p <;> simp [hAB.1, hAB.2]

theorem fsVpInv_pSet (tStar : ℕ) (stAB : (vpTyFS).denote × (vpTyFS).denote) (p : Bool)
    (vp' : (vpTyFS).denote) (hAB : fsVpInv tStar stAB.1 ∧ fsVpInv tStar stAB.2)
    (hvp' : fsVpInv tStar vp') :
    let st' := if p then (stAB.1, vp') else (vp', stAB.2)
    fsVpInv tStar st'.1 ∧ fsVpInv tStar st'.2 := by
  cases p <;> simp [hAB.1, hAB.2, hvp']

theorem fsVpInv_mk_tset (tStar : ℕ)
    (id0 : Bool) (σ' : RSt) (vS0 : Option (Option SS))
    (vR0 : ℕ → Option (Option RS)) (γ' : Γ) (curT0 : Option T) (tcur' t0 : ℕ)
    (rsv : Option RS)
    (h1 : vS0 = some none → (partyDec id0).sendsIn tStar = true)
    (h2 : vR0 tStar = some none → (partyDec id0).sendsIn tStar = false)
    (hNotSends : (partyDec id0).sendsIn t0 = false) :
    fsVpInv (KC := KC) (CCoins := CCoins) (I := I) (KR := KR) (K := K) (M := M) (E := E)
      tStar (id0, σ', vS0, (fun j => if j = t0 then some rsv else vR0 j), γ', curT0, tcur') := by
  refine ⟨h1, fun hvr => ?_⟩
  by_cases hjt : tStar = t0
  · subst hjt; exact hNotSends
  · simp only [hjt, ↓reduceIte] at hvr; exact h2 hvr

theorem cLeakE_st_fs {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (s : Expr O' Γ' (cGsTy vpT)) (l : Expr O' Γ' .nat) (ρ : Env Γ') :
    ((cLeakE s l).eval ρ).1 = (s.eval ρ).1 := by
  simp [cLeakE, cGsMk, cGsSt, Expr.eval, Expr.v0]

theorem cEpMgmtE_some_st_fs {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (Δ qep : ℕ) (s : Expr O' Γ' (cGsTy vpT)) (p bad : Expr O' Γ' .bool) (ρ : Env Γ')
    {s₁ : (cGsTy vpT).denote} (h : (cEpMgmtE Δ qep s p bad).eval ρ = some s₁) :
    s₁.1 = (s.eval ρ).1 := by
  simp only [cEpMgmtE, letE_eval, pair_eval, ite_eval] at h
  set v0 : (Ty.prod (cGsTy vpT) (.prod .bool .bool)).denote := (s.eval ρ, p.eval ρ, bad.eval ρ)
  change (if (sendsInE _ _).eval (Env.cons (t := .prod (cGsTy vpT) (.prod .bool .bool)) v0 ρ)
    then _ else _) = some s₁ at h
  split_ifs at h
  · cases h
  · simp only [some_eval, Option.some.injEq] at h
    subst h
    simp only [cGsMk, cGsSt, Expr.eval, Expr.v0, Env.get_cons_zero]
    exact cLeakE_st_fs _ _ _
  · simp only [some_eval, Option.some.injEq] at h; subst h; rfl
  · cases h
  · simp only [some_eval, Option.some.injEq] at h; subst h; rfl

theorem cDeleteE_st_fs {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (L : ℕ) (s : Expr O' Γ' (cGsTy vpT)) (pos : Expr O' Γ' posTy) (ρ : Env Γ') :
    ((cDeleteE L s pos).eval ρ).1 = (s.eval ρ).1 := by
  simp [cDeleteE, cGsMk, cGsSt, Expr.eval, Expr.v0]

theorem cAcceptE_st_fs {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (L : ℕ) (s : Expr O' Γ' (cGsTy vpT)) (p : Expr O' Γ' .bool)
    (st' : Expr O' Γ' vpT) (pos : Expr O' Γ' posTy) (ρ : Env Γ') :
    ((cAcceptE L s p st' pos).eval ρ).1 =
      if p.eval ρ then ((s.eval ρ).1.1, st'.eval ρ) else (st'.eval ρ, (s.eval ρ).1.2) := by
  cases hp : (p.eval ρ : Bool) <;>
    simp [cAcceptE, cGsMk, cGsSt, pSet_eval_st_fs, cDeleteE_st_fs, Expr.eval, Expr.v0, hp]

theorem cGsSetStP_st_fs {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (s : Expr O' Γ' (cGsTy vpT)) (p : Expr O' Γ' .bool) (st' : Expr O' Γ' vpT) (ρ : Env Γ') :
    ((cGsSetStP s p st').eval ρ).1 =
      if p.eval ρ then ((s.eval ρ).1.1, st'.eval ρ) else (st'.eval ρ, (s.eval ρ).1.2) := by
  cases hp : (p.eval ρ : Bool) <;>
    simp [cGsSetStP, cGsMk, cGsSt, pSet_eval_st_fs, Expr.eval, Expr.v0, hp]

theorem cGsSetWin_st_fs {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (s : Expr O' Γ' (cGsTy vpT)) (w : Expr O' Γ' .bool) (ρ : Env Γ') :
    ((cGsSetWin s w).eval ρ).1 = (s.eval ρ).1 := by
  simp [cGsSetWin, cGsMk, cGsSt, Expr.eval, Expr.v0]

theorem cRecordE_st_fs {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (L Δ : ℕ) (s : Expr O' Γ' (cGsTy vpT)) (p : Expr O' Γ' .bool)
    (st' : Expr O' Γ' vpT) (r : Expr O' Γ' cRecTy) (isChall : Expr O' Γ' .bool) (ρ : Env Γ') :
    ((cRecordE L Δ s p st' r isChall).eval ρ).1 =
      if p.eval ρ then ((s.eval ρ).1.1, st'.eval ρ) else (st'.eval ρ, (s.eval ρ).1.2) := by
  cases hp : (p.eval ρ : Bool) <;>
    simp [cRecordE, cGsMk, cGsSt, pSet_eval_st_fs, Expr.eval, Expr.v0, hp]

theorem cAfterCorrE_st_fs {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (L : ℕ) (s : Expr O' Γ' (cGsTy vpT)) (p : Expr O' Γ' .bool) (ρ : Env Γ') :
    ((cAfterCorrE L s p).eval ρ).1 = (s.eval ρ).1 := by
  simp [cAfterCorrE, cGsMk, cGsSt, cLeakE_st_fs, Expr.eval, Expr.v0]

theorem ite_fst_eq_fs {α β : Type} {P_cond : Prop} [Decidable P_cond]
    {g1 g2 : α × β} {x : α} (h1 : g1.1 = x) (h2 : g2.1 = x) :
    (if P_cond then g1 else g2).1 = x := by
  by_cases hc : P_cond <;> simp [hc, h1, h2]

@[simp] theorem fsHPot_setCache {O' : Ops S} {Γ' : List (Ty S)}
    (hE : Expr O' Γ' hsTy) (cE : Expr O' Γ' _) (ρ : Env Γ') :
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
      ((fsHsSetCache hE cE).eval ρ) =
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ) := rfl

@[simp] theorem fsHPot_setTable {O' : Ops S} {Γ' : List (Ty S)}
    (hE : Expr O' Γ' hsTy) (tblE : Expr O' Γ' _) (ρ : Env Γ') :
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
      ((fsHsSetTable hE tblE).eval ρ) =
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ) := rfl

@[simp] theorem fsHPot_setSessions {O' : Ops S} {Γ' : List (Ty S)}
    (hE : Expr O' Γ' hsTy) (sesE : Expr O' Γ' _) (ρ : Env Γ') :
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
      ((fsHsSetSessions hE sesE).eval ρ) =
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ) := rfl

@[simp] theorem fsHPot_setTrans {O' : Ops S} {Γ' : List (Ty S)}
    (hE : Expr O' Γ' hsTy) (trE : Expr O' Γ' _) (ρ : Env Γ') :
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
      ((fsHsSetTrans hE trE).eval ρ) =
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ) := rfl

@[simp] theorem fsHPot_setCountTrans {O' : Ops S} {Γ' : List (Ty S)}
    (hE : Expr O' Γ' hsTy) (cntE : Expr O' Γ' .nat) (trE : Expr O' Γ' _) (ρ : Env Γ') :
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
      ((fsHsSetCountTrans hE cntE trE).eval ρ) =
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ) := rfl

@[simp] theorem fsHPot_setSCorr_true {O' : Ops S} {Γ' : List (Ty S)}
    (hE : Expr O' Γ' hsTy) (ρ : Env Γ') :
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
      ((fsHsSetSCorr hE (.bool true)).eval ρ) = 0 := by
  simp [fsHPot, fsHsSetSCorr, fsHsMk, Expr.eval]

@[simp] theorem fsHPot_setExt_some {O' : Ops S} {Γ' : List (Ty S)}
    (hE : Expr O' Γ' hsTy) (exE : Expr O' Γ' (.prod (.base .ss) (.base .rs))) (ρ : Env Γ') :
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
      ((fsHsSetExt hE (.some exE)).eval ρ) = 0 := by
  simp [fsHPot, fsHsSetExt, fsHsMk, Expr.eval]

@[simp] theorem fsHPot_isExtE (L j : ℕ) {Γ' : List (Ty S)}
    (hE : Expr OO Γ' hsTy) (ikE : Expr OO Γ' (.base .i)) (ρ : Env Γ') :
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
      (((isExtE L j hE ikE).eval ρ).2) =
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ) := by
  unfold isExtE
  simp only [letE_eval, pair_eval, ite_eval]
  split_ifs <;> rfl

@[simp] theorem fsHPot_extOfE (L j : ℕ) {Γ' : List (Ty S)}
    (hE : Expr OO Γ' hsTy) (sidE : Expr OO Γ' (.opt (.base .i))) (ρ : Env Γ') :
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
      (((extOfE L j hE sidE).eval ρ).2) =
    fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ) := by
  unfold extOfE
  simp only [letE_eval, pair_eval]
  cases (sidE.eval ρ) <;> simp [Expr.eval, Expr.v0, Expr.v1, fsHPot_isExtE]

theorem extOfE_none_fst (L j : ℕ) {Γ' : List (Ty S)}
    (hE : Expr OO Γ' hsTy) (sidE : Expr OO Γ' (.opt (.base .i))) (ρ : Env Γ')
    (hsid : sidE.eval ρ = none) :
    ((extOfE L j hE sidE).eval ρ).1 = false := by
  unfold extOfE
  simp [Expr.eval, Expr.v0, hsid]

theorem isQueryBoundP_min_fs {ι' : Type} {spec' : OracleSpec.{0, 0} ι'} {α : Type}
    {P : ι' → Prop} [DecidablePred P] {oa : OracleComp spec' α} {a b : ℕ}
    (ha : oa.IsQueryBoundP P a) (hb : oa.IsQueryBoundP P b) :
    oa.IsQueryBoundP P (min a b) := by
  rcases Nat.le_total a b with h | h
  · rwa [Nat.min_eq_left h]
  · rwa [Nat.min_eq_right h]

theorem fsIface_fwdU_zero (n : ℕ) :
    ((II).fwdU n).IsQueryBoundP P_fs 0 := by
  change OracleComp.IsQueryBoundP
    (liftM (OracleSpec.query (spec := unifSpec + CryptoGames.FSAEAD.spec SS RS (Header T) M E) (.inl n)))
    P_fs 0
  rw [← bind_pure (liftM _), isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (by simp [isGameQuery]), fun _ => by simp⟩

/-- Invariant-carrying potential predicate for `OracleComp`. -/
structure PotOKInvFS {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {α : Type}
    (P : ι' → Prop) [DecidablePred P] (Inv : α → Prop) (B : α → ℕ)
    (oa : OracleComp T' α) (n : ℕ) : Prop where
  run : ∀ {β : Type} (k : α → OracleComp T' β),
    (∀ a, Inv a → (k a).IsQueryBoundP P (B a)) → (oa >>= k).IsQueryBoundP P n

theorem PotOKInvFS.mono {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {α : Type}
    {P : ι' → Prop} [DecidablePred P] {Inv : α → Prop} {B : α → ℕ}
    {oa : OracleComp T' α} {n₁ n₂ : ℕ}
    (h : PotOKInvFS P Inv B oa n₁) (hn : n₁ ≤ n₂) :
    PotOKInvFS P Inv B oa n₂ :=
  ⟨fun k hk => (h.run k hk).mono hn⟩

theorem PotOKInvFS.bindPot {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {α γ : Type}
    {P : ι' → Prop} [DecidablePred P] {Inv₁ : α → Prop} {Inv₂ : γ → Prop}
    {B₁ : α → ℕ} {B₂ : γ → ℕ}
    {oa : OracleComp T' α} {f : α → OracleComp T' γ} {n : ℕ}
    (h1 : PotOKInvFS P Inv₁ B₁ oa n)
    (h2 : ∀ a, Inv₁ a → PotOKInvFS P Inv₂ B₂ (f a) (B₁ a)) :
    PotOKInvFS P Inv₂ B₂ (oa >>= f) n :=
  ⟨fun k hk => by
    rw [bind_assoc]
    exact h1.run (fun a => f a >>= k) (fun a ha => (h2 a ha).run k hk)⟩

theorem PotOKInvFS.bind' {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {α γ : Type}
    {P : ι' → Prop} [DecidablePred P] {Inv : γ → Prop} {B : γ → ℕ}
    {oa : OracleComp T' α} {f : α → OracleComp T' γ} {m n r : ℕ}
    (hoa : oa.IsQueryBoundP P m) (hf : ∀ a, PotOKInvFS P Inv B (f a) r) (hmn : m + r ≤ n) :
    PotOKInvFS P Inv B (oa >>= f) n :=
  ⟨fun k hk => by
    rw [bind_assoc]
    exact (isQueryBoundP_bind hoa (fun a _ => (hf a).run k hk)).mono hmn⟩

theorem potInvFS_ret {S' : Sig} {ι' : Type} {T' : OracleSpec.{0, 0} ι'}
    {O' : Ops S'} {I' : Iface S' T'} {P : ι' → Prop} [DecidablePred P]
    {Γ' : List (Ty S')} {τ : Ty S'} {Inv : τ.denote → Prop} {B : τ.denote → ℕ}
    {e : Expr O' Γ' τ} {ρ : Env Γ'} {n : ℕ}
    (hInv : Inv (e.eval ρ)) (hB : B (e.eval ρ) ≤ n) :
    PotOKInvFS P Inv B ((Comp.ret (I := I') e).eval ρ) n :=
  ⟨fun k hk => by simpa [Comp.eval] using (hk (e.eval ρ) hInv).mono hB⟩

theorem potInvFS_ite {S' : Sig} {ι' : Type} {T' : OracleSpec.{0, 0} ι'}
    {O' : Ops S'} {I' : Iface S' T'} {P : ι' → Prop} [DecidablePred P]
    {Γ' : List (Ty S')} {τ : Ty S'} {Inv : τ.denote → Prop} {B : τ.denote → ℕ}
    {cond : Expr O' Γ' .bool} {t f : Comp O' I' Γ' τ} {ρ : Env Γ'} {n : ℕ}
    (ht : cond.eval ρ = true → PotOKInvFS P Inv B (t.eval ρ) n)
    (hf : cond.eval ρ = false → PotOKInvFS P Inv B (f.eval ρ) n) :
    PotOKInvFS P Inv B ((Comp.ite cond t f).eval ρ) n :=
  ⟨fun k hk => by
    simp only [Comp.eval]
    cases hc : cond.eval ρ
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact (hf hc).run k hk
    · simp only [↓reduceIte]; exact (ht hc).run k hk⟩

theorem potInvFS_caseOpt {S' : Sig} {ι' : Type} {T' : OracleSpec.{0, 0} ι'}
    {O' : Ops S'} {I' : Iface S' T'} {P : ι' → Prop} [DecidablePred P]
    {Γ' : List (Ty S')} {α τ : Ty S'} {Inv : τ.denote → Prop} {B : τ.denote → ℕ}
    {scrut : Expr O' Γ' (.opt α)} {onNone : Comp O' I' Γ' τ}
    {onSome : Comp O' I' (α :: Γ') τ} {ρ : Env Γ'} {n : ℕ}
    (hNone : scrut.eval ρ = none → PotOKInvFS P Inv B (onNone.eval ρ) n)
    (hSome : ∀ v, scrut.eval ρ = some v → PotOKInvFS P Inv B (onSome.eval (.cons v ρ)) n) :
    PotOKInvFS P Inv B ((Comp.caseOpt scrut onNone onSome).eval ρ) n :=
  ⟨fun k hk => by
    simp only [Comp.eval]
    split
    · next h => exact (hNone h).run k hk
    · next v h => exact (hSome v h).run k hk⟩

theorem potInvFS_caseSum {S' : Sig} {ι' : Type} {T' : OracleSpec.{0, 0} ι'}
    {O' : Ops S'} {I' : Iface S' T'} {P : ι' → Prop} [DecidablePred P]
    {Γ' : List (Ty S')} {α β τ : Ty S'} {Inv : τ.denote → Prop} {B : τ.denote → ℕ}
    {scrut : Expr O' Γ' (.sum α β)} {onInl : Comp O' I' (α :: Γ') τ}
    {onInr : Comp O' I' (β :: Γ') τ} {ρ : Env Γ'} {n : ℕ}
    (hInl : ∀ v, scrut.eval ρ = .inl v → PotOKInvFS P Inv B (onInl.eval (.cons v ρ)) n)
    (hInr : ∀ v, scrut.eval ρ = .inr v → PotOKInvFS P Inv B (onInr.eval (.cons v ρ)) n) :
    PotOKInvFS P Inv B ((Comp.caseSum scrut onInl onInr).eval ρ) n :=
  ⟨fun k hk => by
    simp only [Comp.eval]
    split
    · next v h => exact (hInl v h).run k hk
    · next v h => exact (hInr v h).run k hk⟩

theorem potInvFS_comp_const {Γ' : List (Ty S)} {τ : Ty S}
    (c : Comp OO II Γ' τ) (ρ : Env Γ') {B : τ.denote → ℕ} (r n : ℕ)
    (hB : ∀ a, B a ≤ r) (hq : c.queries (fun _ => 1) (fun _ => 0) + r ≤ n) :
    PotOKInvFS P_fs (fun _ => True) B (c.eval ρ) n :=
  ⟨fun _k hk =>
    (isQueryBoundP_bind
      (Comp.queryBound_eval P_fs (fun _ => 1) (fun _ => 0)
        (fun _ _ _ => Nat.le_refl 1) fsIface_fwdU_zero c ρ)
      (fun a _ => (hk a trivial).mono (hB a))).mono hq⟩

theorem potOKInvFS_simulateQ_handlerImpl_step1
    {S' : Sig} {O' : Ops S'} {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {I' : Iface S' T'}
    {κ : Type} {G : OracleSpec.{0, 0} κ} {C : GameCodec S' G} {σ : Ty S'} {α : Type}
    {P : ι' → Prop} [DecidablePred P] (Inv : σ.denote → Prop) (B : σ.denote → ℕ)
    (hU : ∀ n, (I'.fwdU n).IsQueryBoundP P 0) (h : Comp O' I' [σ, C.Q] (.prod C.R σ))
    (hStep : ∀ (m : ℕ) q s, Inv s →
      PotOKInvFS P (fun x : C.R.denote × σ.denote => Inv x.2)
        (fun x : C.R.denote × σ.denote => m + B x.2)
        (h.eval (.cons s (.cons q .nil))) (1 + m + B s))
    {mx : OracleComp (unifSpec + G) α} {qAdv : ℕ}
    (hq : mx.IsQueryBoundP (isGameQuery (G := G)) qAdv)
    (st : σ.denote) (hInv : Inv st) :
    PotOKInvFS P (fun x : α × σ.denote => Inv x.2) (fun _ : α × σ.denote => 0)
      ((simulateQ (handlerImpl (C := C) h) mx).run st) (qAdv + B st) := by
  induction mx using OracleComp.inductionOn generalizing qAdv st with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact ⟨fun k hk => by simpa using (hk (a, st) hInv).mono (Nat.zero_le (qAdv + B st))⟩
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [simulateQ_query_bind, StateT.run_bind]
    rcases q with uq | gq
    · change PotOKInvFS P _ _
        ((do let u ← I'.fwdU uq; return (u, st)) >>=
          fun x => (simulateQ (handlerImpl (C := C) h) (k x.1)).run x.2) (qAdv + B st)
      rw [bind_assoc]
      refine PotOKInvFS.bind' (m := 0) (r := qAdv + B st) (hU uq) (fun u => ?_) (by omega)
      rw [pure_bind]; exact ih u (by simpa [isGameQuery] using hq.2 u) st hInv
    · have hpos : 0 < qAdv := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      change PotOKInvFS P _ _
        ((do let p ← h.eval (.cons st (.cons (C.qenc gq) .nil)); return (C.rdec gq p.1, p.2)) >>=
          fun x => (simulateQ (handlerImpl (C := C) h) (k x.1)).run x.2) ((m + 1) + B st)
      rw [show (m + 1) + B st = 1 + m + B st by omega, bind_assoc]
      refine PotOKInvFS.bindPot (hStep m (C.qenc gq) st hInv) (fun p hpInv => ?_)
      rw [pure_bind]
      exact ih (C.rdec gq p.1) (by simpa [isGameQuery] using hq.2 (C.rdec gq p.1)) p.2 hpInv

theorem lookupFC_potOKInv (L : ℕ) {Γ' : List (Ty S)}
    (hE : Expr OO Γ' hsTy) (ikE : Expr OO Γ' (.base .i)) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS P_fs (fun _ => True)
      (fun x => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) x.2)
      ((lookupFC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L hE ikE).eval ρ)
      (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ)) := by
  unfold lookupFC; rw [eval_bind_ret]
  refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v1]))
  rw [eval_bind]
  refine PotOKInvFS.bindPot
    (potInvFS_comp_const _ _ (m + fsHPot (hE.eval ρ)) (m + fsHPot (hE.eval ρ))
      (fun _ => Nat.le_refl _) (by simp [Comp.queries]))
    (fun _ _ => potInvFS_ret trivial (by simp [fsHPot_setTable, Expr.eval, Expr.v0, Expr.v1]))

theorem rootFSC_potOKInv (L : ℕ) (mo : Mode) {Γ' : List (Ty S)}
    (hE : Expr OO Γ' hsTy) (tE : Expr OO Γ' .nat)
    (ikE : Expr OO Γ' (.base .i)) (σE : Expr OO Γ' (.base .sig)) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS P_fs (fun x => x.1.2.2 ≠ none → tE.eval ρ = mo.tStar)
      (fun x => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) x.2)
      ((rootFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo hE tE ikE σE).eval ρ)
      (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ)) := by
  unfold rootFSC; rw [eval_bind_ret]
  refine potInvFS_ite
    (fun _ => potInvFS_ret (fun h => absurd rfl h) (by simp [Expr.eval, Expr.v0])) (fun _ => ?_)
  refine potInvFS_ite (fun htEq => ?_) (fun _ => ?_)
  · have htStar : tE.eval ρ = mo.tStar := by
      simp only [Expr.eval, Expr.v0, Env.get_cons_zero, decide_eq_true_eq] at htEq
      exact htEq
    refine potInvFS_ite (fun _ => ?_) (fun _ => ?_)
    · rw [eval_bind]
      refine PotOKInvFS.bindPot
        (potInvFS_comp_const _ _ (m + fsHPot (hE.eval ρ)) (m + fsHPot (hE.eval ρ))
          (fun _ => Nat.le_refl _) (by simp [Comp.queries]))
        (fun _ _ => ?_)
      rw [eval_bind]
      refine PotOKInvFS.bindPot
        (potInvFS_comp_const _ _ (m + fsHPot (hE.eval ρ)) (m + fsHPot (hE.eval ρ))
          (fun _ => Nat.le_refl _) (by simp [Comp.queries]))
        (fun _ _ => potInvFS_ret (fun _ => htStar) (by simp [Expr.eval, Expr.v2]))
    · rw [eval_bind]
      have hLk := lookupFC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
        L (.fst (Expr.v0 (O := OO))) (.fst (.snd (.snd .v0)))
        (.cons (hE.eval ρ, tE.eval ρ, ikE.eval ρ, σE.eval ρ) ρ) m
      simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hLk
      exact PotOKInvFS.bindPot hLk
        (fun _ _ => potInvFS_ret (fun _ => htStar) (by simp [Expr.eval, Expr.v0]))
  · refine potInvFS_ite (fun _ => ?_)
      (fun _ => potInvFS_ret (fun h => absurd rfl h) (by simp [Expr.eval, Expr.v0]))
    rw [eval_bind]
    exact PotOKInvFS.bindPot
      (potInvFS_comp_const _ _ (m + fsHPot (hE.eval ρ)) (m + fsHPot (hE.eval ρ))
        (fun _ => Nat.le_refl _) (by simp [Comp.queries]))
      (fun _ _ => potInvFS_ret (fun h => absurd rfl h) (by simp [Expr.eval, Expr.v1]))

theorem fsStartSendC_potOKInv (L : ℕ) (mo : Mode) (j : ℕ) {Γ' : List (Ty S)}
    (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σE : Expr OO Γ' (.base .sig))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS P_fs
      (fun res => ∀ tup, res.1 = some tup → tup.2.2.2 = none → tE.eval ρ = mo.tStar)
      (fun res => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) res.2)
      ((fsStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo j hE ctxE pE tE γE σE rE).eval ρ)
      (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ)) := by
  unfold fsStartSendC; rw [eval_bind_ret, eval_bind]
  refine PotOKInvFS.bindPot
    (potInvFS_comp_const _ _ (m + fsHPot (hE.eval ρ)) (m + fsHPot (hE.eval ρ))
      (fun _ => Nat.le_refl _) (by simp [Comp.queries]))
    (fun coins _ => ?_)
  rw [eval_bind]
  have hRoot := rootFSC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    L mo (.fst (Expr.v1 (O := OO))) (.fst (.snd .v1))
    (.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair (.fst (.snd (.snd .v1))) .v0))))
    (.fst (.snd (.snd (.snd .v1))))
    (.cons coins (.cons (hE.eval ρ, tE.eval ρ, γE.eval ρ, σE.eval ρ, rE.eval ρ) ρ)) m
  simp only [Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ] at hRoot
  refine PotOKInvFS.bindPot hRoot (fun rootOut hRootInv => ?_)
  refine potInvFS_ret ?_ (by simp [fsHPot_setCache, fsHPot_extOfE, Expr.eval, Expr.v0])
  intro tup htup hssv
  simp only [some_eval, Option.some.injEq, pair_eval, ite_eval] at htup
  subst htup
  dsimp only at hssv
  apply hRootInv
  intro hsidNone
  have hextFalse := extOfE_none_fst L j (.snd (Expr.v0 (O := OO))) (.snd (.snd (.fst .v0)))
    (.cons rootOut (.cons coins (.cons ((hE.pair (tE.pair (γE.pair (σE.pair rE)))).eval ρ) ρ)))
    (by simpa [Expr.eval, Expr.v0, Env.get_cons_zero] using hsidNone)
  simp [Expr.eval, Expr.v0, Env.get_cons_zero] at hssv
  exact Bool.noConfusion (hextFalse.symm.trans hssv)

theorem fsStartRecvC_potOKInv (L : ℕ) (mo : Mode) (j : ℕ) {Γ' : List (Ty S)}
    (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS P_fs (fun _ => True)
      (fun res => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) res.2)
      ((fsStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo j hE ctxE pE tE γE σE tnE).eval ρ)
      (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ)) := by
  unfold fsStartRecvC; rw [eval_bind_ret]
  refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v0, Expr.v1]))
  refine potInvFS_ite (fun _ => ?_) (fun _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v0]))
  refine potInvFS_ite (fun _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v0])) (fun _ => ?_)
  rw [eval_bind]
  have hLk := lookupFC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    L (.fst (Expr.v0 (O := OO)))
    (.snd (Expr.op (O := OO) CKAOp.ckaReceive (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd (.snd .v0)))))))
    (.cons (hE.eval ρ, tE.eval ρ, γE.eval ρ, σE.eval ρ, tnE.eval ρ) ρ) m
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hLk
  exact PotOKInvFS.bindPot hLk
    (fun _ _ => potInvFS_ret trivial (by simp [fsHPot_isExtE, Expr.eval, Expr.v0]))

theorem fsFsSendC_potOKInv (Δcka : ℕ) {Γ' : List (Ty S)}
    (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (ssvE : Expr OO Γ' (.opt (.base .ss))) (hdrE : Expr OO Γ' hdrTy)
    (mE : Expr OO Γ' (.base .msg)) (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg))))
    (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS P_fs
      (fun res => ∀ vc, res.1 = some vc → vc.1 = none → ssvE.eval ρ = none)
      (fun res => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) res.2)
      ((fsFsSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) Δcka hE ctxE pE tE ssvE hdrE mE pairE).eval ρ)
      (1 + m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ)) := by
  unfold fsFsSendC; rw [eval_bind_ret]
  refine potInvFS_caseOpt (fun hSsvNone => ?_) (fun ss hSsvSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSsvNone
    refine potInvFS_caseOpt (fun hExtNone => ?_) (fun _ _ => ?_)
    · simp only [fsHsExt, Expr.eval, Expr.v0, Env.get_cons_zero] at hExtNone
      rw [eval_bind]
      refine PotOKInvFS.bindPot
        (Inv₁ := fun _ => True)
        (B₁ := fun okH =>
          (if okH.1 then 1 else 0) + m +
            fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) okH.2)
        ?_ (fun okH _ => ?_)
      · refine potInvFS_ite (fun hCond => ?_)
          (fun _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v0]))
        have hNotSC : (hE.eval ρ).2.2.2.2.2.1 = false := by
          simp only [fsHsSCorr, Expr.eval, Expr.v0, Env.get_cons_zero,
            Bool.and_eq_true, Bool.not_eq_true'] at hCond
          exact hCond.2
        have hHPot1 : fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
            (hE.eval ρ) = 1 := by
          simp [fsHPot, hNotSC, hExtNone]
        rw [eval_bind]
        refine PotOKInvFS.bindPot
          (potInvFS_comp_const _ _ (m + 1) (1 + m + fsHPot (hE.eval ρ))
            (fun _ => Nat.le_refl _) (by simp [Comp.queries, hHPot1]; omega))
          (fun _ _ => ?_)
        refine potInvFS_caseOpt
          (fun _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v1, hHPot1]))
          (fun _ _ => potInvFS_ret trivial (by simp [fsHPot_setSCorr_true, Expr.eval, Expr.v2]; omega))
      · refine potInvFS_ite
          (fun hNotOk => potInvFS_ret (fun _ h => by simp [Expr.eval] at h) (by
            simp only [Expr.eval, Expr.v0, Env.get_cons_zero, Bool.not_eq_true'] at hNotOk
            simp [Expr.eval, Expr.v0, hNotOk]))
          (fun hNotNotOk => ?_)
        have hOkTrue : okH.1 = true := by
          cases hok : okH.1 <;> [simp [Expr.eval, Expr.v0, hok] at hNotNotOk; rfl]
        rw [eval_bind]
        refine PotOKInvFS.bindPot
          (potInvFS_comp_const _ _ (m + fsHPot okH.2)
            ((if okH.1 then 1 else 0) + m + fsHPot okH.2)
            (fun _ => Nat.le_refl _) (by simp [Comp.queries, hOkTrue]; omega))
          (fun _ _ => ?_)
        refine potInvFS_caseOpt
          (fun _ => potInvFS_ret (fun _ h => by simp [Expr.eval] at h) (by simp [Expr.eval, Expr.v1]))
          (fun _ _ => potInvFS_ret (fun _ _ _ => hSsvNone)
            (by simp [fsHPot_setCountTrans, Expr.eval, Expr.v0, Expr.v2]))
    · refine potInvFS_ret (fun _ _ _ => hSsvNone) ?_
      simp only [fsHPot_setExt_some, Expr.eval, Expr.v1, Nat.add_zero]
      omega
  · refine potInvFS_ret ?_
      (by simp only [Expr.eval, Expr.v1, Env.get_cons_succ, Env.get_cons_zero]; omega)
    intro vc hvc hvc1
    simp only [some_eval, Option.some.injEq, pair_eval] at hvc
    subst hvc
    simp [Expr.eval] at hvc1

theorem fsFsRecvC_potOKInv (L B : ℕ) {Γ' : List (Ty S)}
    (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (rsvE : Expr OO Γ' (.opt (.base .rs))) (hdrE : Expr OO Γ' hdrTy)
    (eE : Expr OO Γ' (.base .ct)) (recE : Expr OO Γ' (.opt cRecTy))
    (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS P_fs (fun _ => True)
      (fun res => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) res.2)
      ((fsFsRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B hE ctxE pE tE rsvE hdrE eE recE).eval ρ)
      (1 + m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ)) := by
  unfold fsFsRecvC; rw [eval_bind_ret]
  refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
  · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
    · rw [eval_bind]
      refine PotOKInvFS.bindPot
        (potInvFS_comp_const _ _ (m + fsHPot (hE.eval ρ)) (1 + m + fsHPot (hE.eval ρ))
          (fun _ => Nat.le_refl _) (by simp [Comp.queries]; omega))
        (fun _ _ => ?_)
      refine potInvFS_caseOpt
        (fun _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v1]))
        (fun _ _ => potInvFS_caseSum
          (fun _ _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v3]))
          (fun _ _ => potInvFS_ret trivial (by simp [fsHPot_setTrans, Expr.eval, Expr.v3])))
    · exact potInvFS_caseOpt
        (fun _ => potInvFS_ret trivial
          (by simp only [Expr.eval, Expr.v1, Env.get_cons_succ, Env.get_cons_zero]; omega))
        (fun _ _ => potInvFS_ret trivial (by simp [fsHPot_setExt_some, Expr.eval]; omega))
  · exact potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial
        (by simp only [Expr.eval, Expr.v1, Env.get_cons_succ, Env.get_cons_zero]; omega))
      (fun _ _ => potInvFS_ret trivial
        (by simp only [Expr.eval, Expr.v2, Env.get_cons_succ, Env.get_cons_zero]; omega))

theorem fsCommitC_potOKInv {Γ' : List (Ty S)}
    (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (pE : Expr OO Γ' .bool) (oldE newE : Expr OO Γ' vpTyFS) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS P_fs (fun res => res.1 = some (newE.eval ρ))
      (fun res => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) res.2)
      ((fsCommitC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) hE ctxE pE oldE newE).eval ρ)
      (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ)) := by
  unfold fsCommitC
  exact potInvFS_ret (by simp [Expr.eval]) (by simp [Expr.eval])

theorem fsRevealC_potOKInv (L : ℕ) (mo : Mode) {Γ' : List (Ty S)}
    (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' vpTyFS) (ρ : Env Γ') (m : ℕ)
    (hVp : fsVpInv mo.tStar (vpE.eval ρ)) :
    PotOKInvFS P_fs (fun _ => True)
      (fun res => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) res.2)
      ((fsRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo hE ctxE pE vpE).eval ρ)
      (1 + m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ)) := by
  unfold fsRevealC; rw [eval_bind_ret, eval_bind]
  by_cases hVS : (vpE.eval ρ).2.2.1 = some none
  · have hVRNotNone : (vpE.eval ρ).2.2.2.1 mo.tStar ≠ some none := by
      intro hVR
      have hsT := hVp.1 hVS
      have hsF := hVp.2 hVR
      rw [hsT] at hsF; cases hsF
    refine PotOKInvFS.bindPot
      (Inv₁ := fun _ => True)
      (B₁ := fun ssH => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) ssH.2)
      ?_ (fun ssH _ => ?_)
    · refine potInvFS_caseOpt
        (fun _ => potInvFS_ret trivial
          (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
        (fun _ _ => potInvFS_caseOpt (fun _ => ?_)
          (fun _ _ => potInvFS_ret trivial
            (by simp only [Expr.eval, Expr.v2, Env.get_cons_succ, Env.get_cons_zero]; omega)))
      refine potInvFS_caseOpt (fun _ => ?_)
        (fun _ _ => potInvFS_ret trivial
          (by simp only [Expr.eval, Expr.v2, Env.get_cons_succ, Env.get_cons_zero]; omega))
      rw [eval_bind]
      exact PotOKInvFS.bindPot
        (potInvFS_comp_const _ _ (m + fsHPot (hE.eval ρ)) (1 + m + fsHPot (hE.eval ρ))
          (fun _ => Nat.le_refl _) (by simp [Comp.queries]; omega))
        (fun _ _ => potInvFS_caseOpt
          (fun _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v2]))
          (fun _ _ => potInvFS_ret trivial (by simp [fsHPot_setSCorr_true, Expr.eval])))
    · refine potInvFS_caseOpt
        (fun _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v0]))
        (fun _ _ => ?_)
      rw [eval_bind]
      refine PotOKInvFS.bindPot
        (Inv₁ := fun _ => True)
        (B₁ := fun rsH => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) rsH.2)
        ?_ (fun rsH _ => ?_)
      · refine potInvFS_caseOpt
          (fun _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v1]))
          (fun rsv hrsv => ?_)
        refine potInvFS_caseOpt (fun hrsvNone => ?_)
          (fun _ _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v3]))
        exfalso
        simp only [vpVR, Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ] at hrsv hrsvNone
        subst hrsvNone
        exact hVRNotNone hrsv
      · refine potInvFS_caseOpt
          (fun _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v0]))
          (fun _ _ => ?_)
        rw [eval_bind]
        exact PotOKInvFS.bindPot
          (potInvFS_comp_const _ _ (m + fsHPot rsH.2) (m + fsHPot rsH.2)
            (fun _ => Nat.le_refl _) (by simp [rangeListC_queries]))
          (fun _ _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v2]))
  · refine PotOKInvFS.bindPot
      (Inv₁ := fun _ => True)
      (B₁ := fun ssH => 1 + m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) ssH.2)
      ?_ (fun ssH _ => ?_)
    · refine potInvFS_caseOpt
        (fun _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v0]))
        (fun ssv hssv => ?_)
      refine potInvFS_caseOpt (fun hssvNone => ?_)
        (fun _ _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v2]))
      exfalso
      simp only [vpVS, Expr.eval, Expr.v0, Env.get_cons_zero] at hssv hssvNone
      subst hssvNone
      exact hVS hssv
    · refine potInvFS_caseOpt
        (fun _ => potInvFS_ret trivial
          (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
        (fun _ _ => ?_)
      rw [eval_bind]
      refine PotOKInvFS.bindPot
        (Inv₁ := fun _ => True)
        (B₁ := fun rsH => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) rsH.2)
        ?_ (fun rsH _ => ?_)
      · refine potInvFS_caseOpt
          (fun _ => potInvFS_ret trivial
            (by simp only [Expr.eval, Expr.v1, Env.get_cons_succ, Env.get_cons_zero]; omega))
          (fun _ _ => potInvFS_caseOpt (fun _ => ?_)
            (fun _ _ => potInvFS_ret trivial
              (by simp only [Expr.eval, Expr.v3, Env.get_cons_succ, Env.get_cons_zero]; omega)))
        refine potInvFS_caseOpt (fun _ => ?_)
          (fun _ _ => potInvFS_ret trivial
            (by simp only [Expr.eval, Expr.v3, Env.get_cons_succ, Env.get_cons_zero]; omega))
        refine potInvFS_ite
          (fun _ => potInvFS_ret trivial
            (by simp only [Expr.eval, Expr.v2, Env.get_cons_succ, Env.get_cons_zero]; omega))
          (fun _ => ?_)
        rw [eval_bind]
        exact PotOKInvFS.bindPot
          (potInvFS_comp_const _ _ (m + fsHPot ssH.2) (1 + m + fsHPot ssH.2)
            (fun _ => Nat.le_refl _) (by simp [Comp.queries]; omega))
          (fun _ _ => potInvFS_caseOpt
            (fun _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v3]))
            (fun _ _ => potInvFS_ret trivial (by simp [fsHPot_setExt_some, Expr.eval])))
      · refine potInvFS_caseOpt
          (fun _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v0]))
          (fun _ _ => ?_)
        rw [eval_bind]
        exact PotOKInvFS.bindPot
          (potInvFS_comp_const _ _ (m + fsHPot rsH.2) (m + fsHPot rsH.2)
            (fun _ => Nat.le_refl _) (by simp [rangeListC_queries]))
          (fun _ _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v2]))

theorem vSendStep1C_hooksFSC_potOKInv (L B Δcka : ℕ) (mo : Mode) (j : ℕ)
    {Γ' : List (Ty S)} (hE : Expr OO Γ' hsTy)
    (ctxE : Expr OO Γ' (cGsTy vpTyFS)) (pE : Expr OO Γ' .bool)
    (sE : Expr OO Γ' vpTyFS) (rE : Expr OO Γ' (.opt (.base .ccoins)))
    (ρ : Env Γ') (m : ℕ) (hs0 : fsVpInv mo.tStar (sE.eval ρ)) :
    PotOKInvFS P_fs (fun res => ∀ s1, res.1 = some s1 → fsVpInv mo.tStar s1)
      (fun res => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) res.2)
      ((vSendStep1C (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo j) hE ctxE pE sE rE).eval ρ)
      (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ)) := by
  unfold vSendStep1C; rw [eval_bind_ret]
  refine potInvFS_ite (fun hs => ?_)
    (fun _ => potInvFS_ret
      (fun s1 hs1 => by simp only [Option.some.injEq, Expr.eval, Expr.v0, Env.get_cons_zero] at hs1; subst hs1; exact hs0)
      (by simp [Expr.eval, Expr.v0]))
  rw [sendsInE_eval _ _ _ (partyDec (sE.eval ρ).1) (by simp [vpId, Expr.eval, Expr.v0])] at hs
  simp only [vpTcurNat, Expr.eval, Expr.v0, Env.get_cons_zero] at hs
  dsimp only [hooksFSC]; rw [eval_bind]
  have hSS := fsStartSendC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    L mo j (.fst (Expr.v0 (O := OO))) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.add (vpTcurNat (.fst (.snd (.snd (.snd .v0))))) (.nat 1))
    (vpΓ (.fst (.snd (.snd (.snd .v0))))) (vpRoot (.fst (.snd (.snd (.snd .v0)))))
    (.snd (.snd (.snd (.snd .v0))))
    (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, rE.eval ρ) ρ) m
  simp only [vpTcurNat, Expr.eval, Expr.v0, Env.get_cons_zero] at hSS
  refine PotOKInvFS.bindPot hSS (fun ssOut hSSInv => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret (fun _ h => by simp [Expr.eval] at h) (by simp [Expr.eval, Expr.v0]))
    (fun tup htup => ?_)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at htup
  refine potInvFS_ret ?_ (by simp [Expr.eval, Expr.v1])
  intro s1 hs1
  simp only [Option.some.injEq, vpMk, vpId, vpVR, vpTcurNat,
    Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ] at hs1
  subst hs1
  refine ⟨fun hvS => ?_, hs0.2⟩
  simp only [Option.some.injEq] at hvS
  have htStar := hSSInv tup htup hvS
  rwa [← htStar]

theorem vSendC_hooksFSC_potOKInv (L B Δcka : ℕ) (mo : Mode) (j : ℕ)
    {Γ' : List (Ty S)} (hE : Expr OO Γ' hsTy)
    (ctxE : Expr OO Γ' (cGsTy vpTyFS)) (pE : Expr OO Γ' .bool)
    (sE : Expr OO Γ' vpTyFS) (mE : Expr OO Γ' (.base .msg))
    (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg))))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ') (m : ℕ)
    (hs0 : fsVpInv mo.tStar (sE.eval ρ)) :
    PotOKInvFS P_fs (fun res => ∀ stCt, res.1 = some stCt → fsVpInv mo.tStar stCt.1)
      (fun res => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) res.2)
      ((vSendC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo j) hE ctxE pE sE mE pairE rE).eval ρ)
      (1 + m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ)) := by
  unfold vSendC; rw [eval_bind_ret, eval_bind]
  have h1 := vSendStep1C_hooksFSC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    L B Δcka mo j (.fst (Expr.v0 (O := OO)))
    (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
    (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
    (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, mE.eval ρ, pairE.eval ρ, rE.eval ρ) ρ)
    (1 + m) (by simpa [Expr.eval, Expr.v0, Env.get_cons_zero] using hs0)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at h1
  refine PotOKInvFS.bindPot h1 (fun step1Out hStep1Inv => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret (fun _ h => by simp [Expr.eval] at h)
      (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
    (fun s1 hs1 => ?_)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hs1
  have hs1Inv := hStep1Inv s1 hs1
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret
      (fun stCt hstCt => by
        simp only [Option.some.injEq, Expr.eval, Expr.v0, Env.get_cons_zero] at hstCt
        subst hstCt; exact hs1Inv)
      (by simp only [Expr.eval, Expr.v1, Env.get_cons_succ, Env.get_cons_zero]; omega))
    (fun v hv => ?_)
  simp only [vpVS, Expr.eval, Expr.v0, Env.get_cons_zero] at hv
  dsimp only [hooksFSC]; rw [eval_bind]
  have hFS := fsFsSendC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    Δcka (.snd (Expr.v2 (O := OO))) (.fst (.snd .v3)) (.fst (.snd (.snd .v3)))
    (vpTcurNat .v1) .v0 (.pair (vpTcurNat .v1) (vpTcur .v1))
    (.fst (.snd (.snd (.snd (.snd .v3))))) (.fst (.snd (.snd (.snd (.snd (.snd .v3))))))
    (.cons v (.cons s1 (.cons step1Out
      (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, mE.eval ρ, pairE.eval ρ, rE.eval ρ) ρ)))) m
  simp only [Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ] at hFS
  refine PotOKInvFS.bindPot hFS (fun fsOut hFSInv => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret (fun _ h => by simp [Expr.eval] at h) (by simp [Expr.eval, Expr.v0]))
    (fun vc hvc => ?_)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hvc
  refine potInvFS_ret ?_ (by simp [Expr.eval, Expr.v1])
  intro stCt hstCt
  simp only [Option.some.injEq, vpSetVS, letE_eval, vpMk,
    vpId, vpRoot, vpVR, vpΓ, vpTcur, vpTcurNat,
    Expr.eval, Expr.v0, Expr.v3, Env.get_cons_zero, Env.get_cons_succ] at hstCt
  subst hstCt
  refine ⟨fun hv' => ?_, hs1Inv.2⟩
  simp only [Option.some.injEq] at hv'
  have hvNone := hFSInv vc hvc hv'
  exact hs1Inv.1 (by rw [hv, hvNone])

theorem vRecvStep1C_hooksFSC_potOKInv (L B Δcka : ℕ) (mo : Mode) (j : ℕ)
    {Γ' : List (Ty S)} (hE : Expr OO Γ' hsTy)
    (ctxE : Expr OO Γ' (cGsTy vpTyFS)) (pE : Expr OO Γ' .bool)
    (sE : Expr OO Γ' vpTyFS) (cE : Expr OO Γ' hdrCtTy) (ρ : Env Γ') (m : ℕ)
    (hs0 : fsVpInv mo.tStar (sE.eval ρ))
    (hNotSends : (partyDec (sE.eval ρ).1).sendsIn (cE.eval ρ).1.1 = false) :
    PotOKInvFS P_fs
      (fun res => ∀ s1, res.1 = some (some s1) → s1.1 = (sE.eval ρ).1 ∧ fsVpInv mo.tStar s1)
      (fun res => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) res.2)
      ((vRecvStep1C (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo j) hE ctxE pE sE cE).eval ρ)
      (m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ)) := by
  unfold vRecvStep1C; rw [eval_bind_ret]
  refine potInvFS_ite (fun _ => ?_)
    (fun _ => potInvFS_ret
      (fun s1 hs1 => by
        simp only [Option.some.injEq, Expr.eval, Expr.v0, Env.get_cons_zero] at hs1
        subst hs1; exact ⟨rfl, hs0⟩)
      (by simp [Expr.eval, Expr.v0]))
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret (fun _ h => by simp [Expr.eval] at h) (by simp [Expr.eval, Expr.v0]))
    (fun Tn _ => ?_)
  dsimp only [hooksFSC]; rw [eval_bind]
  have hSR := fsStartRecvC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    L mo j (.fst (Expr.v1 (O := OO))) (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))
    (.fst (.fst (.snd (.snd (.snd (.snd .v1))))))
    (vpΓ (.fst (.snd (.snd (.snd .v1))))) (vpRoot (.fst (.snd (.snd (.snd .v1))))) .v0
    (.cons Tn (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, cE.eval ρ) ρ)) m
  simp only [Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ] at hSR
  refine PotOKInvFS.bindPot hSR (fun _ _ => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret (fun _ h => by simp [Expr.eval] at h) (by simp [Expr.eval, Expr.v0]))
    (fun _ _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret (fun _ h => by simp [Expr.eval] at h) (by simp [Expr.eval, Expr.v1]))
      (fun _ _ => potInvFS_ret ?_ (by simp [Expr.eval, Expr.v2])))
  intro s1 hs1
  simp only [Option.some.injEq, vpMk, vpId, vpVS, vpVR, vpTcur,
    Expr.eval, Expr.v0, Expr.v4, Env.get_cons_zero, Env.get_cons_succ] at hs1
  subst hs1
  exact ⟨rfl, fsVpInv_mk_tset mo.tStar _ _ _ _ _ _ _ _ _ hs0.1 hs0.2 hNotSends⟩

theorem vRecvC_hooksFSC_potOKInv (L B Δcka : ℕ) (mo : Mode) (j : ℕ)
    {Γ' : List (Ty S)} (hE : Expr OO Γ' hsTy)
    (ctxE : Expr OO Γ' (cGsTy vpTyFS)) (pE : Expr OO Γ' .bool)
    (sE : Expr OO Γ' vpTyFS) (cE : Expr OO Γ' hdrCtTy)
    (recE : Expr OO Γ' (.opt cRecTy)) (ρ : Env Γ') (m : ℕ)
    (hs0 : fsVpInv mo.tStar (sE.eval ρ)) :
    PotOKInvFS P_fs
      (fun res => ∀ tup, res.1 = some (some tup) → fsVpInv mo.tStar tup.1)
      (fun res => m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) res.2)
      ((vRecvC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo j) hE ctxE pE sE cE recE).eval ρ)
      (1 + m + fsHPot (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (hE.eval ρ)) := by
  unfold vRecvC; rw [eval_bind_ret]
  refine potInvFS_ite
    (fun _ => potInvFS_ret (fun _ h => by simp [Expr.eval] at h)
      (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
    (fun hGuard => ?_)
  have hNotSends : (partyDec (sE.eval ρ).1).sendsIn (cE.eval ρ).1.1 = false := by
    simp only [orE_eval, Bool.or_eq_false_iff] at hGuard
    have h1 := hGuard.1
    rw [sendsInE_eval _ _ _ (partyDec (sE.eval ρ).1) (by simp [vpId, Expr.eval, Expr.v0])] at h1
    simpa [Expr.eval, Expr.v0] using h1
  rw [eval_bind]
  have hStep1 := vRecvStep1C_hooksFSC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    L B Δcka mo j (.fst (Expr.v0 (O := OO)))
    (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
    (.fst (.snd (.snd (.snd (.snd .v0)))))
    (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, cE.eval ρ, recE.eval ρ) ρ) (1 + m)
    (by simpa [Expr.eval, Expr.v0, Env.get_cons_zero] using hs0)
    (by simpa [Expr.eval, Expr.v0, Env.get_cons_zero] using hNotSends)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hStep1
  refine PotOKInvFS.bindPot hStep1 (fun step1Out hStep1Inv => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret (fun _ h => by simp [Expr.eval] at h)
      (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
    (fun step1In hS1 => ?_)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hS1
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret (fun _ h => by simp [Expr.eval] at h)
      (by simp only [Expr.eval, Expr.v1, Env.get_cons_succ, Env.get_cons_zero]; omega))
    (fun s1 hs1 => ?_)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hs1
  obtain ⟨hs1Id, hs1Inv⟩ := hStep1Inv s1 (by rw [hS1, hs1])
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret (fun _ h => by simp [Expr.eval] at h)
      (by simp only [Expr.eval, Expr.v2, Env.get_cons_succ, Env.get_cons_zero]; omega))
    (fun v _ => ?_)
  dsimp only [hooksFSC]; rw [eval_bind]
  have hFR := fsFsRecvC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    L B (.snd (Expr.v3 (O := OO))) (.fst (.snd .v4)) (.fst (.snd (.snd .v4)))
    (.fst (.fst (.fst (.snd (.snd (.snd (.snd .v4))))))) .v0
    (.fst (.fst (.snd (.snd (.snd (.snd .v4)))))) (.snd (.fst (.snd (.snd (.snd (.snd .v4))))))
    (.snd (.snd (.snd (.snd (.snd .v4)))))
    (.cons v (.cons s1 (.cons step1In (.cons step1Out
      (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, cE.eval ρ, recE.eval ρ) ρ))))) m
  simp only [Expr.eval, Expr.v3, Env.get_cons_zero, Env.get_cons_succ] at hFR
  refine PotOKInvFS.bindPot hFR (fun _ _ => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret (fun _ h => by simp [Expr.eval] at h) (by simp [Expr.eval, Expr.v0]))
    (fun _ _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret (fun _ h => by simp [Expr.eval] at h) (by simp [Expr.eval, Expr.v1]))
      (fun _ _ => potInvFS_ret ?_ (by simp [Expr.eval, Expr.v2])))
  intro tup htup
  simp only [Option.some.injEq, vpSetVR, letE_eval, vpMk,
    vpId, vpRoot, vpVS, vpVR, vpΓ, vpTcur, vpTcurNat,
    Expr.eval, Expr.v0, Expr.v4, Expr.v7, Env.get_cons_zero, Env.get_cons_succ] at htup
  subst htup
  exact fsVpInv_mk_tset mo.tStar _ _ _ _ _ _ _ _ _ hs1Inv.1 hs1Inv.2 (by rwa [hs1Id])


end FsPotOK

end

end Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks
