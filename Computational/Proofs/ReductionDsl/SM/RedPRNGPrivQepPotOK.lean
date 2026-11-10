/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.RedPRNG -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK
import Computational.Proofs.GameHop.ReductionDsl.SupportWP

/-!
# Epoch-Cap Potential Query Bound for `redPRNGPrivProg`

Proves the unconditional `2 * qep + 2` PRF-PRNG query bound `redPRNGPrivProg_queries_qep` and
combines it with `redPRNGPrivProg_makesAtMostQueries_q3` to obtain
`min (2 + 2 * q) (min (q + 3) (2 * qep + 2))`.
-/

namespace Computational.Proofs.ReductionDsl.SM.RedPRNGPrivQepPotOK

public section

set_option autoImplicit false

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Ops Iface Env Expr Comp GameCodec CostedReduction handlerImpl
  isGameQuery)
open _root_.CryptoGames (Party)
open _root_.CryptoGames.CKA (CKASamp CKAOp ckaSMQ ckaHdrCtTy)
open _root_.CryptoGames.PRFPRNG (prngSig prngOps prngIface)
open _root_.CryptoGames.SM (Adversary MakesAtMostQueries posTy posEpoch partyEnc partyDec
  partyDec_partyEnc sendsInE otherE pGet pSet maxN_eval orE isSomeE letE_eval ite_eval some_eval
  sendsInE_eval)
open _root_.CryptoGames.SM.Engine (ConfigEC Policy modeCfgEC cRecTy cGsTy esG esH esAbort esMk
  esSetG esSetH esSetAbort cGsSt cGsEpoch cGsTrans cGsWin cGsB cGsMk cGsSetStP cGsSetWin cRecPos
  cRecCt hdrCtEqE cLeakE cEpMgmtE cDeleteE cAcceptE cRecordE cAfterCorrE cInTransitE privOutC
  mkPartiesE cGsInitE vpMk vpId vpTcurNat vpΓ vpRoot vpSetVS vpSetVR vSendStep1C vSendC vRecvStep1C
  vRecvC commitEC transmitEC challEC deliverEC injectEC corrEC implEC eval_bind eval_bind_ret
  eval_ret)
open _root_.CryptoGames.SM.Construction (Header PartyState Mode prngHsTy prngVpTy prngEsTy rootPRNGC
  rootPRNGC_queries prngStartSendC_queries prngStartRecvC prngFsSendC prngFsRecvC prngCommitC
  prngRevealC_queries hooksPRNGC initPRNGEStateC redPRNGPrivProg)
open Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK (pGet_eval_st_prng pSet_eval_st_prng
  cLeakE_st_prng cAcceptE_st_prng cGsSetStP_st_prng cGsSetWin_st_prng cRecordE_st_prng
  cAfterCorrE_st_prng isQueryBoundP_min_prng prngIface_fwdU_zero ite_fst_eq_prng
  prngStartRecvC_potOKS redPRNGPrivProg_makesAtMostQueries_q3)

section PrngPrivQepPotOK

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
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "II" =>
  prngIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK
local notation "P_prng" => isGameQuery (G := _root_.CryptoGames.PRFPRNG.spec RSt I K)
private structure PotOKInv {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {α : Type}
    (P : ι' → Prop) [DecidablePred P] (Inv : α → Prop) (B : α → ℕ)
    (oa : OracleComp T' α) (n : ℕ) : Prop where
  run : ∀ {β : Type} (k : α → OracleComp T' β),
    (∀ a, Inv a → (k a).IsQueryBoundP P (B a)) → (oa >>= k).IsQueryBoundP P n
private theorem PotOKInv.mono {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {α : Type}
    {P : ι' → Prop} [DecidablePred P] {Inv : α → Prop} {B : α → ℕ}
    {oa : OracleComp T' α} {n₁ n₂ : ℕ} (h : PotOKInv P Inv B oa n₁) (hle : n₁ ≤ n₂) :
    PotOKInv P Inv B oa n₂ := ⟨fun k hk => (h.run k hk).mono hle⟩
private theorem PotOKInv.bindPot {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {α γ : Type} {P : ι' →
    Prop} [DecidablePred P] {Inv₁ : α → Prop} {Inv₂ : γ → Prop} {B₁ : α → ℕ} {B₂ : γ → ℕ} {oa :
    OracleComp T' α} {f : α → OracleComp T' γ} {n : ℕ} (h1 : PotOKInv P Inv₁ B₁ oa n) (h2 : ∀ a,
    Inv₁ a → PotOKInv P Inv₂ B₂ (f a) (B₁ a)) : PotOKInv P Inv₂ B₂ (oa >>= f) n :=
  ⟨fun k hk => by rw [bind_assoc]; exact h1.run _ (fun a ha => (h2 a ha).run k hk)⟩
private theorem PotOKInv.bindSupp {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {α γ : Type} {P : ι' →
    Prop} [DecidablePred P] {Inv : γ → Prop} {B : γ → ℕ} {oa : OracleComp T' α} {f : α → OracleComp
    T' γ} {m r n : ℕ} (hoa : oa.IsQueryBoundP P m) (hf : ∀ a ∈ support oa, PotOKInv P Inv B (f a) r)
    (hmn : m + r ≤ n) : PotOKInv P Inv B (oa >>= f) n :=
  ⟨fun k hk => by
    rw [bind_assoc]; exact (isQueryBoundP_bind hoa (fun a ha => (hf a ha).run k hk)).mono hmn⟩
private theorem potInv_ret {S' : Sig} {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {O' : Ops S'} {I' :
    Iface S' T'} {P : ι' → Prop} [DecidablePred P] {Γ' : List (Ty S')} {τ : Ty S'} {Inv : τ.denote →
    Prop} {B : τ.denote → ℕ} {e : Expr O' Γ' τ} {ρ : Env Γ'} {n : ℕ} (hInv : Inv (e.eval ρ)) (hB : B
    (e.eval ρ) ≤ n) : PotOKInv P Inv B ((Comp.ret (I := I') e).eval ρ) n :=
  ⟨fun _ hk => by rw [eval_ret, pure_bind]; exact (hk (e.eval ρ) hInv).mono hB⟩
private theorem potInv_ite {S' : Sig} {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {O' : Ops S'} {I' :
    Iface S' T'} {P : ι' → Prop} [DecidablePred P] {Γ' : List (Ty S')} {τ : Ty S'} {Inv : τ.denote →
    Prop} {B : τ.denote → ℕ} {cond : Expr O' Γ' .bool} {t f : Comp O' I' Γ' τ} {ρ : Env Γ'} {n : ℕ}
    (ht : cond.eval ρ = true → PotOKInv P Inv B (t.eval ρ) n) (hf : cond.eval ρ = false → PotOKInv P
    Inv B (f.eval ρ) n) : PotOKInv P Inv B ((Comp.ite cond t f).eval ρ) n :=
  ⟨fun k hk => by
    simp only [Comp.eval]
    cases hc : cond.eval ρ
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact (hf hc).run k hk
    · simp only [↓reduceIte]; exact (ht hc).run k hk⟩
private theorem potInv_caseOpt {S' : Sig} {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {O' : Ops S'} {I'
    : Iface S' T'} {P : ι' → Prop} [DecidablePred P] {Γ' : List (Ty S')} {α τ : Ty S'} {Inv :
    τ.denote → Prop} {B : τ.denote → ℕ} {scrut : Expr O' Γ' (.opt α)} {onNone : Comp O' I' Γ' τ}
    {onSome : Comp O' I' (α :: Γ') τ} {ρ : Env Γ'} {n : ℕ} (hNone : scrut.eval ρ = none → PotOKInv P
    Inv B (onNone.eval ρ) n) (hSome : ∀ v, scrut.eval ρ = some v → PotOKInv P Inv B (onSome.eval
    (.cons v ρ)) n) : PotOKInv P Inv B ((Comp.caseOpt scrut onNone onSome).eval ρ) n :=
  ⟨fun k hk => by
    simp only [Comp.eval]
    cases h : scrut.eval ρ with
    | none => exact (hNone h).run k hk
    | some v => exact (hSome v h).run k hk⟩
private theorem potInv_caseSum {S' : Sig} {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {O' : Ops S'} {I'
    : Iface S' T'} {P : ι' → Prop} [DecidablePred P] {Γ' : List (Ty S')} {α β τ : Ty S'} {Inv :
    τ.denote → Prop} {B : τ.denote → ℕ} {scrut : Expr O' Γ' (.sum α β)} {onInl : Comp O' I' (α ::
    Γ') τ} {onInr : Comp O' I' (β :: Γ') τ} {ρ : Env Γ'} {n : ℕ} (hInl : ∀ v, scrut.eval ρ = .inl v
    → PotOKInv P Inv B (onInl.eval (.cons v ρ)) n) (hInr : ∀ v, scrut.eval ρ = .inr v → PotOKInv P
    Inv B (onInr.eval (.cons v ρ)) n) : PotOKInv P Inv B ((Comp.caseSum scrut onInl onInr).eval ρ) n
    :=
  ⟨fun k hk => by
    simp only [Comp.eval]
    cases h : scrut.eval ρ with
    | inl v => exact (hInl v h).run k hk
    | inr v => exact (hInr v h).run k hk⟩
private theorem potOKInv_simulateQ_handlerImpl_c0 {S' : Sig} {O' : Ops S'} {ι' : Type} {T' :
    OracleSpec.{0, 0} ι'} {I' : Iface S' T'} {κ : Type} {G : OracleSpec.{0, 0} κ} {C : GameCodec S'
    G} {σ : Ty S'} {α : Type} {P : ι' → Prop} [DecidablePred P] (Inv : σ.denote → Prop) (B :
    σ.denote → ℕ) (hU : ∀ n, (I'.fwdU n).IsQueryBoundP P 0) (h : Comp O' I' [σ, C.Q] (.prod C.R σ))
    (hStep : ∀ q s, Inv s → PotOKInv P (fun x : C.R.denote × σ.denote => Inv x.2) (fun x => B x.2)
    (h.eval (.cons s (.cons q .nil))) (B s)) (mx : OracleComp (unifSpec + G) α) {st : σ.denote} (hst
    : Inv st) : PotOKInv P (fun x : α × σ.denote => Inv x.2) (fun _ => 0) ((simulateQ (handlerImpl
    (C := C) h) mx).run st) (B st) := by
  induction mx using OracleComp.inductionOn generalizing st with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact ⟨fun k hk => by simpa using (hk (a, st) hst).mono (Nat.zero_le (B st))⟩
  | query_bind q k ih =>
    rw [simulateQ_query_bind, StateT.run_bind]; rcases q with uq | gq
    · change PotOKInv P _ _
        ((do let u ← I'.fwdU uq; return (u, st)) >>=
          fun x => (simulateQ (handlerImpl (C := C) h) (k x.1)).run x.2) (B st)
      rw [bind_assoc]
      refine PotOKInv.bindSupp (hU uq) (fun u _ => ?_) (Nat.zero_add (B st)).le
      rw [pure_bind]; exact ih u hst
    · change PotOKInv P _ _
        ((do let p ← h.eval (.cons st (.cons (C.qenc gq) .nil)); return (C.rdec gq p.1, p.2)) >>=
          fun x => (simulateQ (handlerImpl (C := C) h) (k x.1)).run x.2) (B st)
      rw [bind_assoc]
      refine PotOKInv.bindPot (hStep (C.qenc gq) st hst) (fun p hp => ?_)
      rw [pure_bind]; exact ih (C.rdec gq p.1) hp
private def prngPrivPartyCount (P : Party) (e : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => prngPrivPartyCount P e k + (if P.sendsIn (k + 1) && decide (e < k + 1) then 1 else 0)
private theorem party_sendsIn_succ_partition (k : ℕ) : (if Party.A.sendsIn (k + 1) then 1 else 0) +
    (if Party.B.sendsIn (k + 1) then 1 else 0) = 1 := by
  cases hA : Party.A.sendsIn (k + 1) <;> cases hB : Party.B.sendsIn (k + 1)
  · exfalso; simp [Party.sendsIn] at hA hB; omega
  · rfl
  · rfl
  · exfalso; simp [Party.sendsIn] at hA hB; omega
private theorem prngPrivPartyCount_zero_sum (qep : ℕ) : prngPrivPartyCount .A 0 qep +
    prngPrivPartyCount .B 0 qep = qep := by
  induction qep with
  | zero => rfl
  | succ k ih =>
    have hp := party_sendsIn_succ_partition k
    simp only [prngPrivPartyCount, Nat.zero_lt_succ, decide_true, Bool.and_true]; omega
private theorem prngPrivPartyCount_anti (P : Party) {e₁ e₂ : ℕ} (hle : e₁ ≤ e₂) (qep : ℕ) :
    prngPrivPartyCount P e₂ qep ≤ prngPrivPartyCount P e₁ qep := by
  induction qep with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    simp only [prngPrivPartyCount]; refine Nat.add_le_add ih ?_
    by_cases hk2 : e₂ < k + 1
    · have hk1 : e₁ < k + 1 := Nat.lt_of_le_of_lt hle hk2; simp [hk1, hk2]
    · simp [hk2]
private theorem prngPrivPartyCount_step (P : Party) (e qep : ℕ) (hs : P.sendsIn (e + 1) = true) (hle
    : e + 1 ≤ qep) : prngPrivPartyCount P (e + 1) qep + 1 ≤ prngPrivPartyCount P e qep := by
  induction qep with
  | zero => omega
  | succ k ih =>
    by_cases heq : e = k
    · subst heq
      have hanti := prngPrivPartyCount_anti P (show e ≤ e + 1 by omega) e
      simp only [prngPrivPartyCount, hs, Nat.lt_succ_self, Nat.lt_irrefl, decide_true, decide_false,
        Bool.and_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      omega
    · have ih' := ih (by omega)
      have hk1 : e < k + 1 := by omega
      have hk2 : e + 1 < k + 1 := by omega
      simp only [prngPrivPartyCount, hk1, hk2, decide_true, Bool.and_true]; omega
private def prngPrivVpPot (qep : ℕ) (vp : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote) : ℕ
    :=
  2 * prngPrivPartyCount (partyDec vp.1) vp.2.2.2.2.2.2 qep
private def prngPrivPot (qep : ℕ) (es : (@prngEsTy KC Γ CCoins T I KR RSt K SS RS M E).denote) : ℕ
    :=
  if es.2.2 then 0 else prngPrivVpPot qep es.1.1.1 + prngPrivVpPot qep es.1.1.2
private def prngPrivOtherPot (qep : ℕ) (stAB : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote
    × (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote) (p : Bool) : ℕ :=
  if p then prngPrivVpPot qep stAB.1 else prngPrivVpPot qep stAB.2
private theorem prngPrivOtherPot_add_pGet (qep : ℕ) (stAB : (@prngVpTy KC Γ CCoins T I KR RSt K SS
    RS M E).denote × (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote) (p : Bool) :
    prngPrivOtherPot qep stAB p + prngPrivVpPot qep (if p then stAB.2 else stAB.1) = prngPrivVpPot
    qep stAB.1 + prngPrivVpPot qep stAB.2 := by
  cases p <;> simp [prngPrivOtherPot, Nat.add_comm]
private theorem prngPrivPot_pSet_eq (qep : ℕ) (stAB : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M
    E).denote × (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote) (p : Bool) (vp' : (@prngVpTy
    KC Γ CCoins T I KR RSt K SS RS M E).denote) : (let st' := if p then (stAB.1, vp') else (vp',
    stAB.2); prngPrivVpPot qep st'.1 + prngPrivVpPot qep st'.2) = prngPrivOtherPot qep stAB p +
    prngPrivVpPot qep vp' := by
  cases p <;> simp [prngPrivOtherPot, Nat.add_comm]
private theorem prngPrivPot_mk_eq (qep : ℕ) {g1 g2 : (@cGsTy KC Γ CCoins T I KR RSt K SS RS M E
    prngVpTy).denote} {h1 h2 : (@prngHsTy KC Γ CCoins T I KR RSt K SS RS M E).denote} {ab : Bool}
    (hst : g1.1 = g2.1) : prngPrivPot qep (g1, h1, ab) = prngPrivPot qep (g2, h2, ab) := by
  simp only [prngPrivPot, hst]
private def prngGsInv (g : (@cGsTy KC Γ CCoins T I KR RSt K SS RS M E prngVpTy).denote) : Prop :=
  g.1.1.1 = false ∧ g.1.2.1 = true ∧
  g.1.1.2.2.2.2.2.2 ≤ g.2.2.2.1.1 ∧ g.1.2.2.2.2.2.2.2 ≤ g.2.2.2.1.2 ∧
  ∀ r ∈ g.2.2.2.2.2.2.1, r.2.2.1.1 ≤ r.1.2.1
private def prngPrivInv (es : (@prngEsTy KC Γ CCoins T I KR RSt K SS RS M E).denote) : Prop :=
  es.2.2 = false → prngGsInv es.1
private theorem prngPrivInv_abort {g : (@cGsTy KC Γ CCoins T I KR RSt K SS RS M E prngVpTy).denote}
    {h : (@prngHsTy KC Γ CCoins T I KR RSt K SS RS M E).denote} :
    prngPrivInv (g, h, true) := fun hab => by cases hab
private theorem prngGsInv_of_fields_eq {g₁ g₂ : (@cGsTy KC Γ CCoins T I KR RSt K SS RS M E
    prngVpTy).denote} (hSt : g₁.1 = g₂.1) (hEp : g₁.2.2.2.1 = g₂.2.2.2.1) (hTr : ∀ r ∈
    g₁.2.2.2.2.2.2.1, r ∈ g₂.2.2.2.2.2.2.1) (hg : prngGsInv g₂) : prngGsInv g₁ :=
  ⟨by rw [hSt]; exact hg.1, by rw [hSt]; exact hg.2.1,
   by rw [hSt, hEp]; exact hg.2.2.1, by rw [hSt, hEp]; exact hg.2.2.2.1,
   fun r hr => hg.2.2.2.2 r (hTr r hr)⟩
private theorem prngGsInv_ite {P_cond : Prop} [Decidable P_cond] {g₁ g₂ : (@cGsTy KC Γ CCoins T I KR
    RSt K SS RS M E prngVpTy).denote} (h₁ : prngGsInv g₁) (h₂ : prngGsInv g₂) : prngGsInv (if P_cond
    then g₁ else g₂) := by
  by_cases hc : P_cond <;> simp [hc, h₁, h₂]
private theorem cGsSetWin_gsInv {O' : Ops S} {Γ' : List (Ty S)} (s : Expr O' Γ' (cGsTy prngVpTy)) (w
    : Expr O' Γ' .bool) (ρ : Env Γ') (hg : prngGsInv (s.eval ρ)) : prngGsInv ((cGsSetWin s w).eval
    ρ) :=
  prngGsInv_of_fields_eq
    (by simp [cGsSetWin, letE_eval, cGsMk, cGsSt, Expr.eval, Expr.v0])
    (by simp [cGsSetWin, letE_eval, cGsMk, cGsEpoch, Expr.eval, Expr.v0])
    (fun _ hr => by simpa [cGsSetWin, letE_eval, cGsMk, cGsTrans, Expr.eval, Expr.v0] using hr) hg
private theorem cLeakE_priv_fields {O' : Ops S} {Γ' : List (Ty S)} (s : Expr O' Γ' (cGsTy prngVpTy))
    (l : Expr O' Γ' .nat) (ρ : Env Γ') : ((cLeakE s l).eval ρ).1 = (s.eval ρ).1 ∧ ((cLeakE s l).eval
    ρ).2.2.2.1 = (s.eval ρ).2.2.2.1 ∧ ((cLeakE s l).eval ρ).2.2.2.2.2.2.1 = (s.eval ρ).2.2.2.2.2.2.1
    := by
  simp [cLeakE, letE_eval, cGsMk, cGsSt, cGsEpoch, cGsTrans, Expr.eval, Expr.v0]
private theorem cAfterCorrE_gsInv {O' : Ops S} {Γ' : List (Ty S)} (L : ℕ) (s : Expr O' Γ' (cGsTy
    prngVpTy)) (p : Expr O' Γ' .bool) (ρ : Env Γ') (hg : prngGsInv (s.eval ρ)) : prngGsInv
    ((cAfterCorrE L s p).eval ρ) := by
  refine prngGsInv_of_fields_eq ?_ ?_ (fun _ hr => ?_) hg
  · simp [cAfterCorrE, letE_eval, cGsMk, cGsSt, cLeakE_st_prng, Expr.eval, Expr.v0]
  · simp [cAfterCorrE, letE_eval, cGsMk, cGsEpoch, cLeakE, Expr.eval, Expr.v0]
  · simpa [cAfterCorrE, letE_eval, cGsMk, cGsTrans, cLeakE, Expr.eval, Expr.v0] using hr
private theorem cEpMgmtE_some_priv {O' : Ops S} {Γ' : List (Ty S)} (Δ qep : ℕ) (s : Expr O' Γ'
    (cGsTy prngVpTy)) (p bad : Expr O' Γ' .bool) (ρ : Env Γ') {s₁ : (cGsTy prngVpTy).denote} (hg :
    prngGsInv (s.eval ρ)) (h : (cEpMgmtE Δ qep s p bad).eval ρ = some s₁) : s₁.1 = (s.eval ρ).1 ∧
    prngGsInv s₁ ∧ (if (p.eval ρ : Bool) then (s.eval ρ).1.2 else (s.eval ρ).1.1).1 = p.eval ρ ∧ (if
    (p.eval ρ : Bool) then (s.eval ρ).1.2 else (s.eval ρ).1.1).2.2.2.2.2.2 ≤ (if (p.eval ρ : Bool)
    then s₁.2.2.2.1.2 else s₁.2.2.2.1.1) ∧ ((partyDec (if (p.eval ρ : Bool) then (s.eval ρ).1.2 else
    (s.eval ρ).1.1).1).sendsIn ((if (p.eval ρ : Bool) then (s.eval ρ).1.2 else (s.eval
    ρ).1.1).2.2.2.2.2.2 + 1) = true → (if (p.eval ρ : Bool) then (s.eval ρ).1.2 else (s.eval
    ρ).1.1).2.2.2.2.2.2 + 1 ≤ qep ∧ (if (p.eval ρ : Bool) then (s.eval ρ).1.2 else (s.eval
    ρ).1.1).2.2.2.2.2.2 + 1 ≤ (if (p.eval ρ : Bool) then s₁.2.2.2.1.2 else s₁.2.2.2.1.1)) := by
  set g := s.eval ρ; set p0 : Bool := p.eval ρ; set b0 : Bool := bad.eval ρ
  have hvpId : (if p0 then g.1.2 else g.1.1).1 = p0 := by cases p0 <;> simp [hg.1, hg.2.1]
  have hvpEp : (if p0 then g.1.2 else g.1.1).2.2.2.2.2.2 ≤
      (if p0 then g.2.2.2.1.2 else g.2.2.2.1.1) := by cases p0 <;> simp [hg.2.2.1, hg.2.2.2.1]
  unfold cEpMgmtE at h; rw [letE_eval] at h
  have hp0 : (Expr.pair s (.pair p bad)).eval ρ = (g, p0, b0) := rfl
  rw [hp0] at h; set ρ₁ := Env.cons (t := .prod (cGsTy prngVpTy) (.prod .bool .bool)) (g, p0, b0) ρ
  rw [ite_eval] at h
  have hSends : (sendsInE (.fst (.snd (Expr.v0 (O := O')))) (.add (pGet (cGsEpoch (.fst (Expr.v0 (O
    := O')))) (.fst (.snd (Expr.v0 (O := O'))))) (.nat 1))).eval ρ₁ =
      (partyDec p0).sendsIn ((if p0 then g.2.2.2.1.2 else g.2.2.2.1.1) + 1) := by
    rw [sendsInE_eval _ _ ρ₁ (partyDec p0) (by simp [ρ₁, Expr.eval, Expr.v0])]
    simp [ρ₁, pGet_eval_st_prng, cGsEpoch, Expr.eval, Expr.v0]; rfl
  rw [hSends] at h
  by_cases h1 : (partyDec p0).sendsIn ((if p0 then g.2.2.2.1.2 else g.2.2.2.1.1) + 1) = true
  · simp only [h1, ↓reduceIte, ite_eval] at h
    have hlt1 : (Expr.lt (.nat qep) (.add (pGet (cGsEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd
        (Expr.v0 (O := O'))))) (.nat 1))).eval ρ₁ = decide (qep < (if p0 then g.2.2.2.1.2 else
        g.2.2.2.1.1) + 1) := by
      simp [ρ₁, pGet_eval_st_prng, cGsEpoch, Expr.eval, Expr.v0]; exact Iff.rfl
    rw [hlt1] at h
    by_cases h2 : qep < (if p0 then g.2.2.2.1.2 else g.2.2.2.1.1) + 1
    · simp [h2, Expr.eval] at h
    · simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte, letE_eval, some_eval,
      Option.some.injEq] at h
      set s_mid := (Expr.ite _ (cLeakE _ _) (.fst .v0)).eval ρ₁
      have hmid : s_mid.1 = g.1 ∧ s_mid.2.2.2.1 = g.2.2.2.1 ∧ s_mid.2.2.2.2.2.2.1 = g.2.2.2.2.2.2.1
          := by
        dsimp only [s_mid]; rw [ite_eval]; split_ifs
        · exact cLeakE_priv_fields _ _ ρ₁
        · exact ⟨rfl, rfl, rfl⟩
      have hSt : s₁.1 = g.1 := by rw [← h]; simp [cGsMk, cGsSt, Expr.eval, Expr.v0, hmid.1]
      have hEpA : s₁.2.2.2.1 = if p0 then (g.2.2.2.1.1, g.2.2.2.1.2 + 1) else (g.2.2.2.1.1 + 1,
          g.2.2.2.1.2) := by
        rw [← h]; cases hp0_val : p0 <;>
          simp [ρ₁, hp0_val, cGsMk, cGsEpoch, pSet_eval_st_prng, pGet_eval_st_prng,
            Expr.eval, Expr.v0, Expr.v1, hmid.2.1]
      have hTr : s₁.2.2.2.2.2.2.1 = g.2.2.2.2.2.2.1 := by
        rw [← h]; simp [cGsMk, cGsTrans, Expr.eval, Expr.v0, hmid.2.2]
      refine ⟨hSt, ?_, hvpId, ?_, fun _ => ?_⟩
      · refine ⟨by rw [hSt]; exact hg.1, by rw [hSt]; exact hg.2.1, ?_, ?_,
          fun r hr => hg.2.2.2.2 r (by rwa [hTr] at hr)⟩
        · rw [hSt, hEpA]; cases p0
          · exact Nat.le_trans hg.2.2.1 (Nat.le_succ _)
          · exact hg.2.2.1
        · rw [hSt, hEpA]; cases p0
          · exact hg.2.2.2.1
          · exact Nat.le_trans hg.2.2.2.1 (Nat.le_succ _)
      · rw [hEpA]; cases hp0_val : p0 <;>
          (rw [hp0_val] at hvpEp; exact Nat.le_trans hvpEp (Nat.le_succ _))
      · rw [hEpA]
        have h2' : (if p0 then g.2.2.2.1.2 else g.2.2.2.1.1) + 1 ≤ qep := Nat.le_of_not_lt h2
        cases hp0_val : p0
        · rw [hp0_val] at hvpEp h2'
          exact ⟨Nat.le_trans (Nat.add_le_add_right hvpEp 1) h2', Nat.add_le_add_right hvpEp 1⟩
        · rw [hp0_val] at hvpEp h2'
          exact ⟨Nat.le_trans (Nat.add_le_add_right hvpEp 1) h2', Nat.add_le_add_right hvpEp 1⟩
  · have h1f : (partyDec p0).sendsIn ((if p0 then g.2.2.2.1.2 else g.2.2.2.1.1) + 1) = false :=
      Bool.eq_false_iff.mpr h1
    simp only [h1f, Bool.false_eq_true, ↓reduceIte, ite_eval] at h
    have hlt2 : (Expr.lt (.nat qep) (pGet (cGsEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd (Expr.v0
        (O := O')))))).eval ρ₁ = decide (qep < (if p0 then g.2.2.2.1.2 else g.2.2.2.1.1)) := by
      simp [ρ₁, pGet_eval_st_prng, cGsEpoch, Expr.eval, Expr.v0]; exact Iff.rfl
    rw [hlt2] at h
    by_cases h2 : qep < (if p0 then g.2.2.2.1.2 else g.2.2.2.1.1)
    · simp [h2, Expr.eval] at h
    · simp only [ρ₁, h2, decide_false, Bool.false_eq_true, ↓reduceIte, Expr.eval, Expr.v0,
      Env.get_cons_zero, Option.some.injEq] at h
      subst h; refine ⟨rfl, hg, hvpId, hvpEp, fun hsVp => ?_⟩; rw [hvpId] at hsVp
      have hne : (if p0 then g.1.2 else g.1.1).2.2.2.2.2.2 ≠
          (if p0 then g.2.2.2.1.2 else g.2.2.2.1.1) := fun heq => h1 (heq ▸ hsVp)
      have hlt_ep := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hvpEp hne)
      exact ⟨Nat.le_trans hlt_ep (Nat.le_of_not_lt h2), hlt_ep⟩
private theorem cRecordE_gsInv {O' : Ops S} {Γ' : List (Ty S)} (L Δ : ℕ) (s : Expr O' Γ' (cGsTy
    prngVpTy)) (p : Expr O' Γ' .bool) (st' : Expr O' Γ' prngVpTy) (r : Expr O' Γ' cRecTy) (isChall :
    Expr O' Γ' .bool) (ρ : Env Γ') (hs : prngGsInv (s.eval ρ)) (hp : (st'.eval ρ).1 = p.eval ρ)
    (hstEp : (st'.eval ρ).2.2.2.2.2.2 ≤ (if (p.eval ρ : Bool) then (s.eval ρ).2.2.2.1.2 else (s.eval
    ρ).2.2.2.1.1)) (hr : (r.eval ρ).2.2.1.1 ≤ (r.eval ρ).1.2.1) : prngGsInv ((cRecordE L Δ s p st' r
    isChall).eval ρ) := by
  have hSt := cRecordE_st_prng L Δ s p st' r isChall ρ
  have hEp : ((cRecordE L Δ s p st' r isChall).eval ρ).2.2.2.1 = (s.eval ρ).2.2.2.1 := by
    simp [cRecordE, letE_eval, cGsMk, cGsEpoch, Expr.eval, Expr.v0]
  have hTr : ((cRecordE L Δ s p st' r isChall).eval ρ).2.2.2.2.2.2.1 = (r.eval ρ) :: (s.eval
      ρ).2.2.2.2.2.2.1 := by
    simp [cRecordE, letE_eval, cGsMk, cGsTrans, Expr.eval, Expr.v0]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hSt]; cases hp0 : (p.eval ρ : Bool) <;> simp [hp0, hp, hs.1]
  · rw [hSt]; cases hp0 : (p.eval ρ : Bool) <;> simp [hp0, hp, hs.2.1]
  · rw [hSt, hEp]; cases hp0 : (p.eval ρ : Bool) <;> simp [hp0] at hstEp ⊢
    · exact hstEp
    · exact hs.2.2.1
  · rw [hSt, hEp]; cases hp0 : (p.eval ρ : Bool) <;> simp [hp0] at hstEp ⊢
    · exact hs.2.2.2.1
    · exact hstEp
  · rw [hTr]; rintro x hx; rcases List.mem_cons.mp hx with rfl | hmem
    · exact hr
    · exact hs.2.2.2.2 x hmem
private theorem find?_eq_some_mem_and {α : Type} {ls : List α} {p : α → Bool} {x : α} (h : ls.find?
    p = some x) : x ∈ ls ∧ p x = true := by
  induction ls with
  | nil => cases h
  | cons hd tl ih =>
    simp only [List.find?] at h
    cases hp : p hd
    · simp only [hp] at h; obtain ⟨hm, hpx⟩ := ih h; exact ⟨List.mem_cons_of_mem hd hm, hpx⟩
    · simp only [hp, Option.some.injEq] at h; subst h; exact ⟨List.mem_cons_self, hp⟩
private theorem foldr_filter_acc_mem {α : Type} (ls : List α) (f : α → List α → Bool) {x : α} (hx :
    x ∈ ls.foldr (fun r acc => if f r acc then r :: acc else acc) []) : x ∈ ls := by
  induction ls with
  | nil => simp at hx
  | cons hd tl ih =>
    simp only [List.foldr_cons] at hx; split_ifs at hx
    · rcases List.mem_cons.mp hx with rfl | hmem
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem hd (ih hmem)
    · exact List.mem_cons_of_mem hd (ih hx)
private theorem cInTransitE_some_priv {Γ' : List (Ty S)} (L : ℕ) (s : Expr OO Γ' (cGsTy prngVpTy))
    (qParty : Expr OO Γ' .bool) (c : Expr OO Γ' hdrCtTy) (ρ : Env Γ') {r1 : cRecTy.denote} (hg :
    prngGsInv (s.eval ρ)) (h : (cInTransitE L s qParty c).eval ρ = some r1) : (c.eval ρ).1.1 ≤
    r1.1.2.1 := by
  simp only [cInTransitE, letE_eval, cGsTrans, Expr.eval, Expr.v0, Env.get_cons_zero] at h
  obtain ⟨hmemTake, hpred⟩ := find?_eq_some_mem_and h
  have hrLe : r1.2.2.1.1 ≤ r1.1.2.1 := hg.2.2.2.2 r1 (List.mem_of_mem_take hmemTake)
  simp only [Bool.and_eq_true] at hpred
  have hct := hpred.2
  simp only [hdrCtEqE, letE_eval, cRecCt, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero,
    Env.get_cons_succ, Bool.and_eq_true] at hct
  have heq : r1.2.2.1.1 = (c.eval ρ).1.1 := of_decide_eq_true hct.1.1
  exact heq ▸ hrLe
private theorem cDeleteE_trans_mem {O' : Ops S} {Γ' : List (Ty S)} (L : ℕ) (s : Expr O' Γ' (cGsTy
    prngVpTy)) (pos : Expr O' Γ' posTy) (ρ : Env Γ') {r : cRecTy.denote} (hr : r ∈ ((cDeleteE L s
    pos).eval ρ).2.2.2.2.2.2.1) : r ∈ (s.eval ρ).2.2.2.2.2.2.1 := by
  simp only [cDeleteE, letE_eval, cGsMk, cGsTrans, Expr.eval, Expr.v0, Env.get_cons_zero] at hr
  exact List.mem_of_mem_take (foldr_filter_acc_mem _ _ hr)
private def prngVSendStep1PrivInv (s0 : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote) (ep1
    : ℕ) (res : (Ty.prod (.opt prngVpTy) prngHsTy : Ty S).denote) : Prop :=
  ∀ s1, res.1 = some s1 → s1.1 = s0.1 ∧ s1.2.2.2.2.2.2 ≤ ep1
private def prngVpOptPrivPost (qep m_other : ℕ) (res : (Ty.prod (.opt prngVpTy) prngHsTy : Ty
    S).denote) : ℕ :=
  match res.1 with
  | none => 0
  | some vp' => m_other + prngPrivVpPot qep vp'
private theorem vSendStep1C_priv_potOKInv (B qep : ℕ) (tL : Option ℕ) (t : ℕ) {Γ' : List (Ty S)} (hE
    : Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy)) (pE : Expr OO Γ' .bool) (sE : Expr
    OO Γ' prngVpTy) (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ') (m_other ep1 : ℕ) (hEp0 :
    (sE.eval ρ).2.2.2.2.2.2 ≤ ep1) (hSendQep : (partyDec (sE.eval ρ).1).sendsIn ((sE.eval
    ρ).2.2.2.2.2.2 + 1) = true → (sE.eval ρ).2.2.2.2.2.2 + 1 ≤ qep ∧ (sE.eval ρ).2.2.2.2.2.2 + 1 ≤
    ep1) : PotOKInv P_prng (prngVSendStep1PrivInv (sE.eval ρ) ep1) (prngVpOptPrivPost qep m_other)
    ((vSendStep1C (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B ⟨false, tL, t⟩) hE ctxE pE sE rE).eval ρ) (m_other +
    prngPrivVpPot qep (sE.eval ρ)) := by
  unfold vSendStep1C; rw [eval_bind_ret]
  refine potInv_ite (fun hs => ?_) (fun _ => ?_)
  · rw [sendsInE_eval _ _ _ (partyDec (sE.eval ρ).1) (by simp [vpId, Expr.eval, Expr.v0])] at hs
    simp only [vpTcurNat, Expr.eval, Expr.v0, Env.get_cons_zero] at hs
    obtain ⟨hqep, hep1⟩ := hSendQep hs
    have hStep := prngPrivPartyCount_step (partyDec (sE.eval ρ).1) (sE.eval ρ).2.2.2.2.2.2 qep hs hqep
    rw [eval_bind]
    refine PotOKInv.bindSupp
      (r := m_other + 2 * prngPrivPartyCount (partyDec (sE.eval ρ).1)
        ((sE.eval ρ).2.2.2.2.2.2 + 1) qep)
      (Comp.queryBound_eval P_prng (fun _ => 1) (fun _ => 0)
        (fun _ _ _ => Nat.le_refl 1) prngIface_fwdU_zero _ _) (fun _ _ => ?_)
      (by simp only [hooksPRNGC, prngStartSendC_queries, prngPrivVpPot]; omega)
    refine potInv_caseOpt
      (fun _ => potInv_ret (fun _ h => by simp [Expr.eval] at h)
        (by simp [prngVpOptPrivPost, Expr.eval]))
      (fun _ _ => potInv_ret ?_ ?_)
    · intro s1 hs1; simp only [Expr.eval, Option.some.injEq] at hs1; subst hs1
      exact ⟨by simp [vpMk, vpId, Expr.eval, Expr.v0, Expr.v2],
        by simpa [vpMk, vpTcurNat, Expr.eval, Expr.v0, Expr.v2] using hep1⟩
    · simp [prngVpOptPrivPost, prngPrivVpPot, vpMk, vpId, vpTcurNat, Expr.eval, Expr.v0, Expr.v2]
  · exact potInv_ret
      (fun s1 hs1 => by
        simp only [Expr.eval, Expr.v0, Env.get_cons_zero, Option.some.injEq] at hs1
        subst hs1; exact ⟨rfl, hEp0⟩)
      (by simp [prngVpOptPrivPost, Expr.eval, Expr.v0])
private def prngVSendPrivInv (s0 : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote) (ep1 : ℕ)
    (res : (Ty.prod (.opt (.prod prngVpTy hdrCtTy)) prngHsTy : Ty S).denote) : Prop :=
  ∀ vp' ct, res.1 = some (vp', ct) → vp'.1 = s0.1 ∧ vp'.2.2.2.2.2.2 ≤ ep1 ∧ ct.1.1 ≤ ep1
private def prngVSendPrivPost (qep m_other : ℕ) (res : (Ty.prod (.opt (.prod prngVpTy hdrCtTy))
    prngHsTy : Ty S).denote) : ℕ :=
  match res.1 with
  | none => 0
  | some (vp', _) => m_other + prngPrivVpPot qep vp'
private theorem vSendC_priv_potOKInv (B qep : ℕ) (tL : Option ℕ) (t : ℕ) {Γ' : List (Ty S)} (hE :
    Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy)) (pE : Expr OO Γ' .bool) (sE : Expr OO
    Γ' prngVpTy) (mE : Expr OO Γ' (.base .msg)) (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base
    .msg)))) (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ') (m_other ep1 : ℕ) (hEp0 :
    (sE.eval ρ).2.2.2.2.2.2 ≤ ep1) (hSendQep : (partyDec (sE.eval ρ).1).sendsIn ((sE.eval
    ρ).2.2.2.2.2.2 + 1) = true → (sE.eval ρ).2.2.2.2.2.2 + 1 ≤ qep ∧ (sE.eval ρ).2.2.2.2.2.2 + 1 ≤
    ep1) : PotOKInv P_prng (prngVSendPrivInv (sE.eval ρ) ep1) (prngVSendPrivPost qep m_other)
    ((vSendC (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI :=
    sampI) (sampK := sampK) B ⟨false, tL, t⟩) hE ctxE pE sE mE pairE rE).eval ρ) (m_other +
    prngPrivVpPot qep (sE.eval ρ)) := by
  unfold vSendC; rw [eval_bind_ret, eval_bind]
  have h1 := vSendStep1C_priv_potOKInv (sampKR := sampKR) (sampKC := sampKC) (sampCCoins :=
    sampCCoins) (sampI := sampI) (sampK := sampK) B qep tL t (.fst (Expr.v0 (O := OO))) (.fst (.snd
    .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd (.snd
    (.snd .v0)))))) (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, mE.eval ρ, pairE.eval ρ,
    rE.eval ρ) ρ)
    m_other ep1 (by simpa [Expr.eval, Expr.v0, Env.get_cons_zero] using hEp0)
    (by simpa [Expr.eval, Expr.v0, Env.get_cons_zero] using hSendQep)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at h1
  refine PotOKInv.bindPot h1 (fun step1Out hInv1 => ?_)
  refine potInv_caseOpt (fun hNone => ?_) (fun s1 hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potInv_ret (fun _ _ h => by simp [Expr.eval] at h)
      (by simp [prngVSendPrivPost, prngVpOptPrivPost, hNone, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    obtain ⟨hs1Id, hs1Ep⟩ := hInv1 s1 hSome
    refine potInv_caseOpt (fun _ => ?_) (fun _ _ => ?_)
    · refine potInv_ret ?_ (by simp [prngVSendPrivPost, prngVpOptPrivPost, hSome, Expr.eval, Expr.v0])
      intro vp' ct hEq
      simp only [vpTcurNat, Expr.eval, Expr.v0, Env.get_cons_zero, Option.some.injEq, Prod.mk.injEq]
        at hEq
      rcases hEq with ⟨rfl, hct⟩; rw [← hct]; exact ⟨hs1Id, hs1Ep, hs1Ep⟩
    · rw [eval_bind]; dsimp only [hooksPRNGC, prngFsSendC]; rw [eval_ret, pure_bind]
      refine potInv_caseOpt (fun hFNone => by simp [Expr.eval, Expr.v0] at hFNone) (fun _ _ => ?_)
      refine potInv_ret ?_
        (by simp [prngVSendPrivPost, prngVpOptPrivPost, hSome, prngPrivVpPot,
          vpSetVS, letE_eval, vpMk, vpId, vpTcurNat, Expr.eval, Expr.v0, Expr.v3])
      intro vp' ct hEq
      simp only [vpSetVS, letE_eval, vpMk, vpId, vpTcurNat, Expr.eval, Expr.v0, Expr.v3,
        Env.get_cons_zero, Env.get_cons_succ, Option.some.injEq, Prod.mk.injEq] at hEq
      rcases hEq with ⟨rfl, hct⟩; rw [← hct]; exact ⟨hs1Id, hs1Ep, hs1Ep⟩
private theorem prngStartRecvC_priv_queries_zero (tL : Option ℕ) (t : ℕ) {Γ' : List (Ty S)} (hE :
    Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy)) (pE : Expr OO Γ' .bool) (tE : Expr OO
    Γ' .nat) (γE : Expr OO Γ' (.base .γ)) (σvE : Expr OO Γ' (.opt (.base .sig))) (tnE : Expr OO Γ'
    (.base .t)) (ρ : Env Γ') : ((prngStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins :=
    sampCCoins) (sampI := sampI) (sampK := sampK) ⟨false, tL, t⟩ hE ctxE pE tE γE σvE tnE).eval
    ρ).IsQueryBoundP P_prng 0 := by
  have h := (prngStartRecvC_potOKS (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
    ⟨false, tL, t⟩ hE ctxE pE tE γE σvE tnE ρ 0).run pure (fun _ => by simp)
  simpa using h
private def prngVRecvStep1PrivInv (s0 : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote) (t0 :
    ℕ) (res : (Ty.prod (.opt (.opt prngVpTy)) prngHsTy : Ty S).denote) : Prop :=
  ∀ s1, res.1 = some (some s1) →
    s1.1 = s0.1 ∧ s0.2.2.2.2.2.2 ≤ s1.2.2.2.2.2.2 ∧
    (s1.2.2.2.2.2.2 = s0.2.2.2.2.2.2 ∨ s1.2.2.2.2.2.2 = t0)
private def prngVRecvStep1PrivPost (qep m_other : ℕ) (s0 : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS
    M E).denote) (res : (Ty.prod (.opt (.opt prngVpTy)) prngHsTy : Ty S).denote) : ℕ :=
  match res.1 with
  | none => 0
  | some none => m_other + prngPrivVpPot qep s0
  | some (some s1) => m_other + max (prngPrivVpPot qep s0) (prngPrivVpPot qep s1)
private theorem vRecvStep1C_priv_potOKInv (B qep : ℕ) (tL : Option ℕ) (t : ℕ) {Γ' : List (Ty S)} (hE
    : Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy)) (pE : Expr OO Γ' .bool) (sE : Expr
    OO Γ' prngVpTy) (cE : Expr OO Γ' hdrCtTy) (ρ : Env Γ') (m_other : ℕ) : PotOKInv P_prng
    (prngVRecvStep1PrivInv (sE.eval ρ) (cE.eval ρ).1.1) (prngVRecvStep1PrivPost qep m_other (sE.eval
    ρ)) ((vRecvStep1C (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B ⟨false, tL, t⟩) hE ctxE pE sE cE).eval ρ) (m_other +
    prngPrivVpPot qep (sE.eval ρ)) := by
  unfold vRecvStep1C; rw [eval_bind_ret]
  refine potInv_ite (fun ht => ?_) (fun _ => ?_)
  · have ht' : ((cE.eval ρ).1.1 : ℕ) = ((sE.eval ρ).2.2.2.2.2.2 : ℕ) + 1 := of_decide_eq_true ht
    have hle_c : ((sE.eval ρ).2.2.2.2.2.2 : ℕ) ≤ ((cE.eval ρ).1.1 : ℕ) := ht' ▸ Nat.le_succ _
    refine potInv_caseOpt
      (fun _ => potInv_ret (fun _ h => by simp [Expr.eval] at h)
        (by simp [prngVRecvStep1PrivPost, Expr.eval]))
      (fun Tn _ => ?_)
    rw [eval_bind]
    refine PotOKInv.bindSupp
      (prngStartRecvC_priv_queries_zero (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) tL t
        (.fst (Expr.v1 (O := OO))) (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))
        (.fst (.fst (.snd (.snd (.snd (.snd .v1))))))
        (vpΓ (.fst (.snd (.snd (.snd .v1))))) (vpRoot (.fst (.snd (.snd (.snd .v1)))))
        .v0 (.cons Tn (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, cE.eval ρ) ρ)))
      (fun _ _ => ?_) (Nat.zero_add _).le
    refine potInv_caseOpt
      (fun _ => potInv_ret (fun _ h => by simp [Expr.eval] at h)
        (by simp [prngVRecvStep1PrivPost, Expr.eval]))
      (fun _ _ => potInv_caseOpt
        (fun _ => potInv_ret (fun _ h => by simp [Expr.eval] at h)
          (by simp [prngVRecvStep1PrivPost, Expr.eval]))
        (fun _ _ => potInv_ret ?_ ?_))
    · intro s1 hs1; simp only [Expr.eval, Option.some.injEq] at hs1; subst hs1
      exact ⟨by simp [vpMk, vpId, Expr.eval, Expr.v0, Expr.v4],
        by simpa [vpMk, Expr.eval, Expr.v0, Expr.v4] using hle_c,
        Or.inr (by simp [vpMk, Expr.eval, Expr.v0, Expr.v4])⟩
    · have hAnti := prngPrivPartyCount_anti (partyDec (sE.eval ρ).1) hle_c qep
      simp only [prngVRecvStep1PrivPost, prngPrivVpPot, vpMk, vpId, Expr.eval, Expr.v0, Expr.v4,
        Env.get_cons_zero, Env.get_cons_succ]; omega
  · exact potInv_ret
      (fun s1 hs1 => by
        simp only [Expr.eval, Expr.v0, Env.get_cons_zero, Option.some.injEq] at hs1
        subst hs1; exact ⟨rfl, Nat.le_refl _, Or.inl rfl⟩)
      (by simp [prngVRecvStep1PrivPost, Expr.eval, Expr.v0])
private def prngVRecvPrivInv (s0 : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote) (t0 : ℕ)
    (res : (Ty.prod (.opt (.opt (.prod prngVpTy (.prod .nat (.prod .nat (.base .msg)))))) prngHsTy :
    Ty S).denote) : Prop :=
  ∀ st' t' i' m', res.1 = some (some (st', t', i', m')) →
    st'.1 = s0.1 ∧ t' = t0 ∧ s0.2.2.2.2.2.2 ≤ st'.2.2.2.2.2.2 ∧
    (st'.2.2.2.2.2.2 = s0.2.2.2.2.2.2 ∨ st'.2.2.2.2.2.2 = t0)
private def prngVRecvPrivPost (qep m_other : ℕ) (s0 : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M
    E).denote) (res : (Ty.prod (.opt (.opt (.prod prngVpTy (.prod .nat (.prod .nat (.base .msg))))))
    prngHsTy : Ty S).denote) : ℕ :=
  match res.1 with
  | none => 0
  | some none => m_other + prngPrivVpPot qep s0
  | some (some (st', _, _, _)) => m_other + max (prngPrivVpPot qep s0) (prngPrivVpPot qep st')
private theorem vRecvC_priv_potOKInv (B qep : ℕ) (tL : Option ℕ) (t : ℕ) {Γ' : List (Ty S)} (hE :
    Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy)) (pE : Expr OO Γ' .bool) (sE : Expr OO
    Γ' prngVpTy) (cE : Expr OO Γ' hdrCtTy) (recE : Expr OO Γ' (.opt cRecTy)) (ρ : Env Γ') (m_other :
    ℕ) : PotOKInv P_prng (prngVRecvPrivInv (sE.eval ρ) (cE.eval ρ).1.1) (prngVRecvPrivPost qep
    m_other (sE.eval ρ)) ((vRecvC (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins :=
    sampCCoins) (sampI := sampI) (sampK := sampK) B ⟨false, tL, t⟩) hE ctxE pE sE cE recE).eval ρ)
    (m_other + prngPrivVpPot qep (sE.eval ρ)) := by
  unfold vRecvC; rw [eval_bind_ret]
  refine potInv_ite
    (fun _ => potInv_ret (fun _ _ _ _ h => by simp [Expr.eval] at h)
      (by simp [prngVRecvPrivPost, Expr.eval]))
    (fun _ => ?_)
  rw [eval_bind]
  have hStep1 := vRecvStep1C_priv_potOKInv (sampKR := sampKR) (sampKC := sampKC) (sampCCoins :=
    sampCCoins) (sampI := sampI) (sampK := sampK) B qep tL t (.fst (Expr.v0 (O := OO))) (.fst (.snd
    .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0)))) (.fst (.snd (.snd (.snd (.snd
    .v0))))) (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, cE.eval ρ, recE.eval ρ) ρ)
    m_other
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hStep1
  refine PotOKInv.bindPot hStep1 (fun step1Out hInv1 => ?_)
  refine potInv_caseOpt (fun hNone => ?_) (fun inner hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potInv_ret (fun _ _ _ _ h => by simp [Expr.eval] at h)
      (by simp [prngVRecvPrivPost, prngVRecvStep1PrivPost, hNone, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potInv_caseOpt (fun hInNone => ?_) (fun s1 hInSome => ?_)
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInNone
      exact potInv_ret (fun _ _ _ _ h => by simp [Expr.eval] at h)
        (by simp [prngVRecvPrivPost, prngVRecvStep1PrivPost, hSome, hInNone, Expr.eval])
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInSome
      obtain ⟨hs1Id, hs1Le, hs1Cases⟩ := hInv1 s1 (by rw [hSome, hInSome])
      refine potInv_caseOpt
        (fun _ => potInv_ret (fun _ _ _ _ h => by simp [Expr.eval] at h)
          (by simp [prngVRecvPrivPost, prngVRecvStep1PrivPost, hSome, hInSome, Expr.eval]))
        (fun _ _ => ?_)
      rw [eval_bind]; dsimp only [hooksPRNGC, prngFsRecvC]; rw [eval_ret, pure_bind]
      refine potInv_caseOpt (fun hFNone => by simp [Expr.eval, Expr.v0] at hFNone)
        (fun _ _ => potInv_caseOpt
          (fun _ => potInv_ret (fun _ _ _ _ h => by simp [Expr.eval] at h)
            (by simp [prngVRecvPrivPost, prngVRecvStep1PrivPost, hSome, hInSome, Expr.eval]))
          (fun _ _ => potInv_ret ?_ ?_))
      · intro st' t' i' m' hEq
        simp only [vpSetVR, letE_eval, vpMk, vpId, vpTcurNat, Expr.eval, Expr.v0, Expr.v4,
          Env.get_cons_zero, Env.get_cons_succ, Option.some.injEq, Prod.mk.injEq] at hEq
        rcases hEq with ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨hs1Id, rfl, hs1Le, hs1Cases⟩
      · simp [prngVRecvPrivPost, prngVRecvStep1PrivPost, hSome, hInSome, prngPrivVpPot,
          vpSetVR, letE_eval, vpMk, vpId, vpTcurNat, Expr.eval, Expr.v0, Expr.v4]
private def prngCommitPrivInv (res : (Ty.prod (.opt (cGsTy prngVpTy)) prngEsTy : Ty S).denote) :
    Prop :=
  match res.1 with
  | none => prngPrivInv res.2
  | some s_acc => res.2.2.2 = false ∧ prngGsInv s_acc
private def prngCommitPrivPost (qep : ℕ) (res : (Ty.prod (.opt (cGsTy prngVpTy)) prngEsTy : Ty
    S).denote) : ℕ :=
  match res.1 with
  | none => prngPrivPot qep res.2
  | some s_acc => prngPrivPot qep (s_acc, res.2.2.1, res.2.2.2)
private theorem commitEC_priv_potOKInv (L B qep : ℕ) (tL : Option ℕ) (t : ℕ) {Γ' : List (Ty S)} (esE
    : Expr OO Γ' prngEsTy) (sE : Expr OO Γ' (cGsTy prngVpTy)) (pE : Expr OO Γ' .bool) (oldE newE :
    Expr OO Γ' prngVpTy) (posE : Expr OO Γ' posTy) (ρ : Env Γ') (hNoAbort : (esE.eval ρ).2.2 =
    false) (hg : prngGsInv (sE.eval ρ)) (hNewId : (newE.eval ρ).1 = pE.eval ρ) (hNewEp : (newE.eval
    ρ).2.2.2.2.2.2 ≤ max (if (pE.eval ρ : Bool) then (sE.eval ρ).2.2.2.1.2 else (sE.eval
    ρ).2.2.2.1.1) (posE.eval ρ).2.1) : PotOKInv P_prng prngCommitPrivInv (prngCommitPrivPost qep)
    ((commitEC (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI
    := sampI) (sampK := sampK) B ⟨false, tL, t⟩) L esE sE pE oldE newE posE).eval ρ)
    (prngPrivOtherPot qep (sE.eval ρ).1 (pE.eval ρ) + prngPrivVpPot qep (newE.eval ρ)) := by
  unfold commitEC; rw [eval_bind_ret, eval_bind]
  dsimp only [hooksPRNGC, prngCommitC]; rw [eval_ret, pure_bind]
  refine potInv_caseOpt (fun hCNone => by simp [Expr.eval, Expr.v0] at hCNone) (fun _ hCSome => ?_)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero, Option.some.injEq] at hCSome; subst hCSome
  refine potInv_ret ?_ ?_
  · simp only [prngCommitPrivInv, esMk, esAbort, Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero,
    Env.get_cons_succ, hNoAbort, true_and]
    set s_acc := (cGsSetStP _ _ _).eval _
    have hAccSt : s_acc.1 = if (pE.eval ρ : Bool) then ((sE.eval ρ).1.1, newE.eval ρ) else
        (newE.eval ρ, (sE.eval ρ).1.2) := by
      cases hp : pE.eval ρ <;> simp [s_acc, hp, cGsSetStP_st_prng, cAcceptE_st_prng, Expr.eval]
    have hAccEp : s_acc.2.2.2.1 = if (pE.eval ρ : Bool) then ((sE.eval ρ).2.2.2.1.1, max (sE.eval
        ρ).2.2.2.1.2 (posE.eval ρ).2.1) else (max (sE.eval ρ).2.2.2.1.1 (posE.eval ρ).2.1, (sE.eval
        ρ).2.2.2.1.2) := by
      cases hp : pE.eval ρ <;>
        simp [s_acc, hp, cGsSetStP, cAcceptE, cDeleteE, letE_eval, cGsMk, cGsEpoch,
          pSet_eval_st_prng, pGet_eval_st_prng, posEpoch, maxN_eval, Expr.eval, Expr.v0]
    have hAccTr : ∀ r ∈ s_acc.2.2.2.2.2.2.1, r ∈ (sE.eval ρ).2.2.2.2.2.2.1 := fun r hr =>
      cDeleteE_trans_mem L sE posE ρ
        (by simpa [s_acc, cGsSetStP, cAcceptE, letE_eval, cGsMk, cGsTrans, Expr.eval, Expr.v0] using hr)
    refine ⟨?_, ?_, ?_, ?_, fun r hr => hg.2.2.2.2 r (hAccTr r hr)⟩
    · rw [hAccSt]; cases hp : pE.eval ρ <;> simp [hp, hNewId, hg.1]
    · rw [hAccSt]; cases hp : pE.eval ρ <;> simp [hp, hNewId, hg.2.1]
    · rw [hAccSt, hAccEp]; cases hp : pE.eval ρ <;> simp [hp] at hNewEp ⊢
      · exact hNewEp
      · exact hg.2.2.1
    · rw [hAccSt, hAccEp]; cases hp : pE.eval ρ <;> simp [hp] at hNewEp ⊢
      · exact hg.2.2.2.1
      · exact hNewEp
  · simp only [prngCommitPrivPost, prngPrivPot, esMk, esAbort, cGsSetStP_st_prng, cAcceptE_st_prng,
    Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ, hNoAbort, Bool.false_eq_true,
    ↓reduceIte]
    cases (pE.eval ρ : Bool)
    · simp only [prngPrivOtherPot, Bool.false_eq_true, ↓reduceIte]; omega
    · simp only [prngPrivOtherPot, ↓reduceIte]; omega
private theorem transmitEC_priv_potOKInv (L B Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (π : Policy) {Γ'
    : List (Ty S)} (esE : Expr OO Γ' prngEsTy) (argE : Expr OO Γ' (.prod .bool (.prod (.base .msg)
    (.opt (.base .ccoins))))) (ρ : Env Γ') (hInv : prngPrivInv (esE.eval ρ)) : PotOKInv P_prng (fun
    x => prngPrivInv x.2) (fun x => prngPrivPot qep x.2) ((transmitEC (hooksPRNGC (sampKR := sampKR)
    (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B ⟨false, tL,
    t⟩) L (2 + Δcka) qep π esE argE).eval ρ) (prngPrivPot qep (esE.eval ρ)) := by
  unfold transmitEC; rw [eval_bind_ret]
  refine potInv_ite (fun _ => potInv_ret (by simpa [Expr.eval, Expr.v0] using hInv)
    (by simp [Expr.eval, Expr.v0])) (fun hNotAbWin => ?_)
  have hab : (esE.eval ρ).2.2 = false := by
    simp only [orE, esAbort, cGsWin, esG, Expr.eval, Expr.v0, Env.get_cons_zero] at hNotAbWin
    cases h : (esE.eval ρ).2.2 <;> [rfl; simp [h] at hNotAbWin]
  have hg0 : prngGsInv (esE.eval ρ).1 := hInv hab
  refine potInv_caseOpt (fun _ => potInv_ret (by simpa [Expr.eval, Expr.v0] using hInv)
    (by simp [Expr.eval, Expr.v0])) (fun s1 hs1 => ?_)
  refine potInv_ite (fun _ => potInv_ret
    (by simp [esSetAbort, letE_eval, esMk, Expr.eval, Expr.v0, Expr.v1]; exact prngPrivInv_abort)
    (by simp [prngPrivPot, esSetAbort, letE_eval, esMk, Expr.eval, Expr.v0, Expr.v1])) (fun _ => ?_)
  rw [eval_bind]
  have hs1Props := cEpMgmtE_some_priv (2 + Δcka) qep (esG (.fst .v0)) (.fst (.snd .v0)) (isSomeE
    (.snd (.snd (.snd .v0)))) (.cons (esE.eval ρ, argE.eval ρ) ρ)
    (by simpa [esG, Expr.eval, Expr.v0, Env.get_cons_zero] using hg0) hs1
  simp only [esG, Expr.eval, Expr.v0, Env.get_cons_zero] at hs1Props
  obtain ⟨hs1_st, hs1Inv, hvpId, hvpEp, hSendQep⟩ := hs1Props; set p0 : Bool := (argE.eval ρ).1
  set ep1 : ℕ := if p0 then s1.2.2.2.1.2 else s1.2.2.2.1.1
  set m_other := prngPrivOtherPot qep s1.1 p0
  have hSend := vSendC_priv_potOKInv (sampKR := sampKR) (sampKC := sampKC) (sampCCoins :=
    sampCCoins) (sampI := sampI) (sampK := sampK) B qep tL t (esH (.fst (Expr.v1 (O := OO)))) .v0
    (.fst (.snd .v1)) (pGet (cGsSt .v0) (.fst (.snd .v1))) (.fst (.snd (.snd .v1))) .none (.snd
    (.snd (.snd .v1))) (.cons s1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m_other ep1
    (by simpa [pGet_eval_st_prng, cGsSt, Expr.eval, Expr.v0, Expr.v1, hs1_st] using hvpEp)
    (by simpa [pGet_eval_st_prng, cGsSt, Expr.eval, Expr.v0, Expr.v1, hs1_st] using hSendQep)
  simp only [pGet_eval_st_prng, cGsSt, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero,
    Env.get_cons_succ] at hSend
  change PotOKInv P_prng (prngVSendPrivInv (if p0 then s1.1.2 else s1.1.1) ep1) (prngVSendPrivPost
    qep m_other) _ (m_other + prngPrivVpPot qep (if p0 then s1.1.2 else s1.1.1)) at hSend
  have hSum : m_other + prngPrivVpPot qep (if p0 then s1.1.2 else s1.1.1) = prngPrivPot qep
      (esE.eval ρ) := by rw [prngPrivOtherPot_add_pGet, hs1_st]; simp [prngPrivPot, hab]
  rw [← hSum]
  refine PotOKInv.bindPot hSend (fun sendOut hSendInv => ?_)
  refine potInv_caseOpt (fun hNone => ?_) (fun stCt hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potInv_ret (by simp [esMk, Expr.eval]; exact prngPrivInv_abort)
      (by simp [prngVSendPrivPost, hNone, prngPrivPot, esMk, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    obtain ⟨hVp'Id, hVp'Ep, hCtEp⟩ := hSendInv stCt.1 stCt.2 hSome
    refine potInv_ret ?_ ?_
    · simp only [esMk, esAbort, Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero,
      Env.get_cons_succ, hab]
      exact fun _ => cRecordE_gsInv L (2 + Δcka) .v2 (.fst (.snd .v3)) (.fst .v0) _ (.bool false) _
        hs1Inv (by simpa [Expr.eval, Expr.v0, Expr.v3, hs1_st, hvpId] using hVp'Id)
        (by simpa [Expr.eval, Expr.v0, Expr.v2, Expr.v3] using hVp'Ep)
        (by simp only [pGet_eval_st_prng, cGsEpoch, Expr.eval, Env.get_cons_zero,
          Env.get_cons_succ]; exact hCtEp)
    · simp only [prngVSendPrivPost, hSome, prngPrivPot, esMk, esAbort, cRecordE_st_prng, Expr.eval,
      Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab, Bool.false_eq_true,
      ↓reduceIte]
      have hEq := prngPrivPot_pSet_eq qep s1.1 p0 stCt.1; dsimp only at hEq
      change (let st' := if p0 then (s1.1.1, stCt.1) else (stCt.1, s1.1.2);
        prngPrivVpPot qep st'.1 + prngPrivVpPot qep st'.2) ≤ m_other + prngPrivVpPot qep stCt.1
      rw [hEq]
private theorem challEC_priv_potOKInv (L B Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (cfg : ConfigEC OO)
    (π : Policy) {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy) (argE : Expr OO Γ' (.prod .bool
    (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins)))))) (ρ : Env Γ') (hInv :
    prngPrivInv (esE.eval ρ)) : PotOKInv P_prng (fun x => prngPrivInv x.2) (fun x => prngPrivPot qep
    x.2) ((challEC (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B ⟨false, tL, t⟩) L (2 + Δcka) qep cfg π esE argE).eval ρ)
    (prngPrivPot qep (esE.eval ρ)) := by
  unfold challEC; rw [eval_bind_ret]
  refine potInv_ite (fun _ => potInv_ret (by simpa [Expr.eval, Expr.v0] using hInv)
    (by simp [Expr.eval, Expr.v0])) (fun hNotAbWin => ?_)
  have hab : (esE.eval ρ).2.2 = false := by
    simp only [orE, esAbort, cGsWin, esG, Expr.eval, Expr.v0, Env.get_cons_zero] at hNotAbWin
    cases h : (esE.eval ρ).2.2 <;> [rfl; simp [h] at hNotAbWin]
  have hg0 : prngGsInv (esE.eval ρ).1 := hInv hab
  refine potInv_caseOpt (fun _ => potInv_ret (by simpa [Expr.eval, Expr.v0] using hInv)
    (by simp [Expr.eval, Expr.v0])) (fun s1 hs1 => potInv_ite
      (fun _ => potInv_ret (by simpa [Expr.eval, Expr.v1] using hInv) (by simp [Expr.eval, Expr.v1]))
      (fun _ => potInv_ite (fun _ => potInv_ret
        (by simp [esSetAbort, letE_eval, esMk, Expr.eval, Expr.v0, Expr.v1]; exact prngPrivInv_abort)
        (by simp [prngPrivPot, esSetAbort, letE_eval, esMk, Expr.eval, Expr.v0, Expr.v1])) (fun _ => ?_)))
  rw [eval_bind]
  have hs1Props := cEpMgmtE_some_priv (2 + Δcka) qep (esG (.fst .v0)) (.fst (.snd .v0)) (isSomeE
    (.snd (.snd (.snd (.snd .v0))))) (.cons (esE.eval ρ, argE.eval ρ) ρ)
    (by simpa [esG, Expr.eval, Expr.v0, Env.get_cons_zero] using hg0) hs1
  simp only [esG, Expr.eval, Expr.v0, Env.get_cons_zero] at hs1Props
  obtain ⟨hs1_st, hs1Inv, hvpId, hvpEp, hSendQep⟩ := hs1Props; set p0 : Bool := (argE.eval ρ).1
  set ep1 : ℕ := if p0 then s1.2.2.2.1.2 else s1.2.2.2.1.1
  set m_other := prngPrivOtherPot qep s1.1 p0
  have hSend := vSendC_priv_potOKInv (sampKR := sampKR) (sampKC := sampKC) (sampCCoins :=
    sampCCoins) (sampI := sampI) (sampK := sampK) B qep tL t (esH (.fst (Expr.v1 (O := OO)))) .v0
    (.fst (.snd .v1)) (pGet (cGsSt .v0) (.fst (.snd .v1))) (cfg.challMsgE (pGet (cGsEpoch .v0) (.fst
    (.snd .v1))) (cGsB (esG (.fst .v1))) (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1)))))
    (.some (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1)))))) (.snd (.snd (.snd (.snd
    .v1)))) (.cons s1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m_other ep1
    (by simpa [pGet_eval_st_prng, cGsSt, Expr.eval, Expr.v0, Expr.v1, hs1_st] using hvpEp)
    (by simpa [pGet_eval_st_prng, cGsSt, Expr.eval, Expr.v0, Expr.v1, hs1_st] using hSendQep)
  simp only [pGet_eval_st_prng, cGsSt, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero,
    Env.get_cons_succ] at hSend
  change PotOKInv P_prng (prngVSendPrivInv (if p0 then s1.1.2 else s1.1.1) ep1) (prngVSendPrivPost
    qep m_other) _ (m_other + prngPrivVpPot qep (if p0 then s1.1.2 else s1.1.1)) at hSend
  have hSum : m_other + prngPrivVpPot qep (if p0 then s1.1.2 else s1.1.1) = prngPrivPot qep
      (esE.eval ρ) := by rw [prngPrivOtherPot_add_pGet, hs1_st]; simp [prngPrivPot, hab]
  rw [← hSum]
  refine PotOKInv.bindPot hSend (fun sendOut hSendInv => ?_)
  refine potInv_caseOpt (fun hNone => ?_) (fun stCt hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potInv_ret (by simp [esMk, Expr.eval]; exact prngPrivInv_abort)
      (by simp [prngVSendPrivPost, hNone, prngPrivPot, esMk, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    obtain ⟨hVp'Id, hVp'Ep, hCtEp⟩ := hSendInv stCt.1 stCt.2 hSome
    refine potInv_ret ?_ ?_
    · simp only [esMk, esAbort, Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero,
      Env.get_cons_succ, hab]
      exact fun _ => cRecordE_gsInv L (2 + Δcka) .v2 (.fst (.snd .v3)) (.fst .v0) _ (.bool true) _
        hs1Inv (by simpa [Expr.eval, Expr.v0, Expr.v3, hs1_st, hvpId] using hVp'Id)
        (by simpa [Expr.eval, Expr.v0, Expr.v2, Expr.v3] using hVp'Ep)
        (by simp only [pGet_eval_st_prng, cGsEpoch, Expr.eval, Env.get_cons_zero,
          Env.get_cons_succ]; exact hCtEp)
    · simp only [prngVSendPrivPost, hSome, prngPrivPot, esMk, esAbort, cRecordE_st_prng, Expr.eval,
      Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab, Bool.false_eq_true,
      ↓reduceIte]
      have hEq := prngPrivPot_pSet_eq qep s1.1 p0 stCt.1; dsimp only at hEq
      change (let st' := if p0 then (s1.1.1, stCt.1) else (stCt.1, s1.1.2);
        prngPrivVpPot qep st'.1 + prngPrivVpPot qep st'.2) ≤ m_other + prngPrivVpPot qep stCt.1
      rw [hEq]
private theorem deliverEC_priv_potOKInv (L B maxSkip qep : ℕ) (tL : Option ℕ) (t : ℕ) (cfg :
    ConfigEC OO) {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy) (argE : Expr OO Γ' (.prod .bool
    hdrCtTy)) (ρ : Env Γ') (hInv : prngPrivInv (esE.eval ρ)) : PotOKInv P_prng (fun x => prngPrivInv
    x.2) (fun x => prngPrivPot qep x.2) ((deliverEC (hooksPRNGC (sampKR := sampKR) (sampKC :=
    sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B ⟨false, tL, t⟩) L maxSkip
    cfg esE argE).eval ρ) (prngPrivPot qep (esE.eval ρ)) := by
  unfold deliverEC; rw [eval_bind_ret]
  refine potInv_ite (fun _ => potInv_ret (by simpa [Expr.eval, Expr.v0] using hInv)
    (by simp [Expr.eval, Expr.v0])) (fun hNotAbWin => ?_)
  have hab : (esE.eval ρ).2.2 = false := by
    simp only [orE, esAbort, cGsWin, esG, Expr.eval, Expr.v0, Env.get_cons_zero] at hNotAbWin
    cases h : (esE.eval ρ).2.2 <;> [rfl; simp [h] at hNotAbWin]
  have hg0 : prngGsInv (esE.eval ρ).1 := hInv hab
  refine potInv_caseOpt (fun _ => potInv_ret (by simpa [Expr.eval, Expr.v0] using hInv)
    (by simp [Expr.eval, Expr.v0])) (fun r1 hr1 => ?_)
  have hcLe : (argE.eval ρ).2.1.1 ≤ r1.1.2.1 := by
    simpa [Expr.eval, Expr.v0, Env.get_cons_zero] using cInTransitE_some_priv L (esG (.fst .v0))
      (otherE (.fst (.snd .v0))) (.snd (.snd .v0)) (.cons (esE.eval ρ, argE.eval ρ) ρ)
      (by simpa [esG, Expr.eval, Expr.v0, Env.get_cons_zero] using hg0) hr1
  rw [eval_bind]; set m_other := prngPrivOtherPot qep (esE.eval ρ).1.1 (argE.eval ρ).1
  have hRecv := vRecvC_priv_potOKInv (sampKR := sampKR) (sampKC := sampKC) (sampCCoins :=
    sampCCoins) (sampI := sampI) (sampK := sampK) B qep tL t (esH (.fst (Expr.v1 (O := OO)))) (esG
    (.fst .v1)) (.fst (.snd .v1)) (pGet (cGsSt (esG (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd
    .v1)) (.some .v0) (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m_other
  simp only [pGet_eval_st_prng, cGsSt, esG, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero,
    Env.get_cons_succ] at hRecv
  change PotOKInv P_prng (prngVRecvPrivInv (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else
    (esE.eval ρ).1.1.1) (argE.eval ρ).2.1.1) (prngVRecvPrivPost qep m_other (if ((argE.eval ρ).1 :
    Bool) then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1)) _ (m_other + prngPrivVpPot qep (if
    ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1)) at hRecv
  have hSum : m_other + prngPrivVpPot qep (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else
      (esE.eval ρ).1.1.1) = prngPrivPot qep (esE.eval ρ) := by
    rw [prngPrivOtherPot_add_pGet]; simp [prngPrivPot, hab]
  rw [← hSum]
  refine PotOKInv.bindPot hRecv (fun recvOut hRecvInv => ?_)
  refine potInv_caseOpt (fun hNone => ?_) (fun resInner hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potInv_ret (by simp [esMk, Expr.eval]; exact prngPrivInv_abort)
      (by simp [prngVRecvPrivPost, hNone, prngPrivPot, esMk, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potInv_caseOpt (fun hInNone => ?_) (fun tup hInSome => ?_)
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInNone
      refine potInv_ret ?_ ?_
      · simp only [esMk, esAbort, esG, Expr.eval, Expr.v1, Expr.v2, Expr.v3, Env.get_cons_zero,
        Env.get_cons_succ, hab]
        exact fun _ => prngGsInv_ite
          (cGsSetWin_gsInv _ _ _ (by simpa [esG, Expr.eval, Expr.v3] using hg0)) hg0
      · simp only [prngVRecvPrivPost, hSome, hInNone, esMk, esAbort, esG, Expr.eval, Expr.v1,
        Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab]
        refine Nat.le_trans
          (Nat.le_of_eq (prngPrivPot_mk_eq qep (g2 := (esE.eval ρ).1) (h2 := (esE.eval ρ).2.1)
            (ite_fst_eq_prng (by rw [cGsSetWin_st_prng]; rfl) rfl))) ?_
        simpa [prngPrivPot, hab] using hSum.symm.le
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInSome
      obtain ⟨hstId, _, _, hstCases⟩ :=
        hRecvInv tup.1 tup.2.1 tup.2.2.1 tup.2.2.2 (by rw [hSome, hInSome])
      have hvpId : (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1).1 =
          (argE.eval ρ).1 := by cases ((argE.eval ρ).1 : Bool) <;> simp [hg0.1, hg0.2.1]
      have hvpEp : (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else (esE.eval
          ρ).1.1.1).2.2.2.2.2.2 ≤ (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.2.2.2.1.2 else
          (esE.eval ρ).1.2.2.2.1.1) := by
        cases ((argE.eval ρ).1 : Bool) <;> simp [hg0.2.2.1, hg0.2.2.2.1]
      rw [eval_bind]
      have hCom := commitEC_priv_potOKInv (sampKR := sampKR) (sampKC := sampKC) (sampCCoins :=
        sampCCoins) (sampI := sampI) (sampK := sampK) L B qep tL t (esSetH (.fst (Expr.v4 (O :=
        OO))) (.snd .v2)) (esG (.fst .v4)) (.fst (.snd .v4)) (pGet (cGsSt (esG (.fst .v4))) (.fst
        (.snd .v4))) (.fst .v0) (cRecPos .v3) (.cons tup (.cons resInner (.cons recvOut (.cons r1
        (.cons (esE.eval ρ, argE.eval ρ) ρ)))))
        (by simp [esSetH, letE_eval, esMk, esAbort, Expr.eval, Expr.v0, Expr.v4, hab])
        (by simpa [esG, Expr.eval, Expr.v4] using hg0)
        (by simpa [Expr.eval, Expr.v0, Expr.v4, hvpId] using hstId)
        (by simp only [esG, cRecPos, Expr.eval, Expr.v0, Expr.v3, Expr.v4, Env.get_cons_zero,
          Env.get_cons_succ]
            rcases hstCases with hEq0 | hEqC
            · rw [hEq0]; exact Nat.le_trans hvpEp (Nat.le_max_left _ _)
            · rw [hEqC]; exact Nat.le_trans hcLe (Nat.le_max_right _ _))
      simp only [esG, Expr.eval, Expr.v0, Expr.v4, Env.get_cons_zero, Env.get_cons_succ] at hCom
      have hPre : prngPrivOtherPot qep (esE.eval ρ).1.1 (argE.eval ρ).1 + prngPrivVpPot qep tup.1 ≤
          prngVRecvPrivPost qep m_other (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else
          (esE.eval ρ).1.1.1) recvOut := by simp [prngVRecvPrivPost, hSome, hInSome, m_other]
      refine (PotOKInv.bindPot hCom (fun comOut hComInv => ?_)).mono hPre
      refine potInv_caseOpt (fun hCNone => ?_) (fun s_acc hCSome => ?_)
      · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCNone
        exact potInv_ret (by simpa [prngCommitPrivInv, hCNone, Expr.eval, Expr.v0] using hComInv)
          (by simp [prngCommitPrivPost, hCNone, Expr.eval, Expr.v0])
      · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCSome
        simp only [prngCommitPrivInv, hCSome] at hComInv; obtain ⟨hComAb, hsAccInv⟩ := hComInv
        refine potInv_ret ?_ ?_
        · simp only [esSetG, letE_eval, esMk, esAbort, esH, Expr.eval, Expr.v0, Expr.v1,
          Env.get_cons_zero, Env.get_cons_succ, hComAb]
          exact fun _ => prngGsInv_ite (cGsSetWin_gsInv _ _ _ hsAccInv) hsAccInv
        · simp only [prngCommitPrivPost, hCSome, esSetG, letE_eval, esMk, esAbort, esH, Expr.eval,
          Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
          exact Nat.le_of_eq
            (prngPrivPot_mk_eq qep (g2 := s_acc) (h2 := comOut.2.2.1)
              (ite_fst_eq_prng (by rw [cGsSetWin_st_prng]; rfl) rfl))
private theorem injectEC_priv_potOKInv (L B Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (cfg : ConfigEC
    OO) {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy) (argE : Expr OO Γ' (.prod .bool hdrCtTy)) (ρ
    : Env Γ') (hInv : prngPrivInv (esE.eval ρ)) : PotOKInv P_prng (fun x => prngPrivInv x.2) (fun x
    => prngPrivPot qep x.2) ((injectEC (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins
    := sampCCoins) (sampI := sampI) (sampK := sampK) B ⟨false, tL, t⟩) L (2 + Δcka) qep cfg esE
    argE).eval ρ) (prngPrivPot qep (esE.eval ρ)) := by
  unfold injectEC; rw [eval_bind_ret]
  refine potInv_ite (fun _ => potInv_ret (by simpa [Expr.eval, Expr.v0] using hInv)
    (by simp [Expr.eval, Expr.v0])) (fun hNotRef => ?_)
  have hab : (esE.eval ρ).2.2 = false := by
    simp only [orE, esAbort, Expr.eval, Expr.v0, Env.get_cons_zero] at hNotRef
    cases h : (esE.eval ρ).2.2 <;> [rfl; simp [h] at hNotRef]
  have hg0 : prngGsInv (esE.eval ρ).1 := hInv hab
  rw [eval_bind]; set m_other := prngPrivOtherPot qep (esE.eval ρ).1.1 (argE.eval ρ).1
  have hRecv := vRecvC_priv_potOKInv (sampKR := sampKR) (sampKC := sampKC) (sampCCoins :=
    sampCCoins) (sampI := sampI) (sampK := sampK) B qep tL t (esH (.fst (Expr.v0 (O := OO)))) (esG
    (.fst .v0)) (.fst (.snd .v0)) (pGet (cGsSt (esG (.fst .v0))) (.fst (.snd .v0))) (.snd (.snd
    .v0)) .none (.cons (esE.eval ρ, argE.eval ρ) ρ) m_other
  simp only [pGet_eval_st_prng, cGsSt, esG, Expr.eval, Expr.v0, Env.get_cons_zero] at hRecv
  change PotOKInv P_prng (prngVRecvPrivInv (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else
    (esE.eval ρ).1.1.1) (argE.eval ρ).2.1.1) (prngVRecvPrivPost qep m_other (if ((argE.eval ρ).1 :
    Bool) then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1)) _ (m_other + prngPrivVpPot qep (if
    ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1)) at hRecv
  have hSum : m_other + prngPrivVpPot qep (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else
      (esE.eval ρ).1.1.1) = prngPrivPot qep (esE.eval ρ) := by
    rw [prngPrivOtherPot_add_pGet]; simp [prngPrivPot, hab]
  rw [← hSum]
  refine PotOKInv.bindPot hRecv (fun recvOut hRecvInv => ?_)
  refine potInv_caseOpt (fun hNone => ?_) (fun resInner hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potInv_ret (by simp [esMk, Expr.eval]; exact prngPrivInv_abort)
      (by simp [prngVRecvPrivPost, hNone, prngPrivPot, esMk, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potInv_caseOpt (fun hInNone => ?_) (fun tup hInSome => ?_)
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInNone
      exact potInv_ret
        (by simp only [esSetH, letE_eval, esMk, esAbort, esG, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
          Env.get_cons_zero, Env.get_cons_succ, hab]; exact fun _ => hg0)
        (by simp only [prngVRecvPrivPost, hSome, hInNone, prngPrivPot, esSetH, letE_eval, esMk,
          esAbort, esG, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get_cons_zero, Env.get_cons_succ,
          hab, Bool.false_eq_true, ↓reduceIte]
            simpa [prngPrivPot, hab] using hSum.symm.le)
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInSome
      obtain ⟨hstId, ht'Eq, _, hstCases⟩ :=
        hRecvInv tup.1 tup.2.1 tup.2.2.1 tup.2.2.2 (by rw [hSome, hInSome])
      refine potInv_ite
        (fun _ => potInv_ret
          (by simp only [esSetH, letE_eval, esMk, esAbort, esG, Expr.eval, Expr.v0, Expr.v2,
            Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab]; exact fun _ => hg0)
          (by simp only [prngVRecvPrivPost, hSome, hInSome, prngPrivPot, esSetH, letE_eval, esMk,
            esAbort, esG, Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero,
            Env.get_cons_succ, hab, Bool.false_eq_true, ↓reduceIte]
              have hEqSum : prngPrivVpPot qep (esE.eval ρ).1.1.1 + prngPrivVpPot qep (esE.eval
                  ρ).1.1.2 = m_other + prngPrivVpPot qep (if ((argE.eval ρ).1 : Bool) then (esE.eval
                  ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
                simpa [prngPrivPot, hab] using hSum.symm
              omega))
        (fun _ => potInv_ite (fun _ => ?_) (fun _ => ?_))
      · have hvpId : (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else
            (esE.eval ρ).1.1.1).1 = (argE.eval ρ).1 := by
          cases ((argE.eval ρ).1 : Bool) <;> simp [hg0.1, hg0.2.1]
        have hvpEp : (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else
            (esE.eval ρ).1.1.1).2.2.2.2.2.2 ≤ (if ((argE.eval ρ).1 : Bool) then
            (esE.eval ρ).1.2.2.2.1.2 else (esE.eval ρ).1.2.2.2.1.1) := by
          cases ((argE.eval ρ).1 : Bool) <;> simp [hg0.2.2.1, hg0.2.2.2.1]
        rw [eval_bind]
        have hCom := commitEC_priv_potOKInv (sampKR := sampKR) (sampKC := sampKC) (sampCCoins :=
          sampCCoins) (sampI := sampI) (sampK := sampK) L B qep tL t (esSetH (.fst (Expr.v3 (O :=
          OO))) (.snd .v2)) (esG (.fst .v3)) (.fst (.snd .v3)) (pGet (cGsSt (esG (.fst .v3))) (.fst
          (.snd .v3))) (.fst .v0) (.pair (otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst
          (.snd (.snd .v0))))) (.cons tup (.cons resInner (.cons recvOut (.cons (esE.eval ρ,
          argE.eval ρ) ρ))))
          (by simp [esSetH, letE_eval, esMk, esAbort, Expr.eval, Expr.v0, Expr.v3, hab])
          (by simpa [esG, Expr.eval, Expr.v3] using hg0)
          (by simpa [Expr.eval, Expr.v0, Expr.v3, hvpId] using hstId)
          (by simp only [esG, Expr.eval, Expr.v0, Expr.v3, Env.get_cons_zero, Env.get_cons_succ]
              rcases hstCases with hEq0 | hEqC
              · rw [hEq0]; exact Nat.le_trans hvpEp (Nat.le_max_left _ _)
              · rw [hEqC, ← ht'Eq]; exact Nat.le_max_right _ _)
        simp only [esG, Expr.eval, Expr.v0, Expr.v3, Env.get_cons_zero, Env.get_cons_succ] at hCom
        have hPre : prngPrivOtherPot qep (esE.eval ρ).1.1 (argE.eval ρ).1 + prngPrivVpPot qep tup.1
            ≤ prngVRecvPrivPost qep m_other (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2
            else (esE.eval ρ).1.1.1) recvOut := by simp [prngVRecvPrivPost, hSome, hInSome, m_other]
        refine (PotOKInv.bindPot hCom (fun comOut hComInv => ?_)).mono hPre
        refine potInv_caseOpt (fun hCNone => ?_) (fun s_acc hCSome => ?_)
        · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCNone
          exact potInv_ret (by simpa [prngCommitPrivInv, hCNone, Expr.eval, Expr.v0] using hComInv)
            (by simp [prngCommitPrivPost, hCNone, Expr.eval, Expr.v0])
        · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCSome
          simp only [prngCommitPrivInv, hCSome] at hComInv; obtain ⟨_, hsAccInv⟩ := hComInv
          exact potInv_ret
            (by simp only [esSetG, letE_eval, esMk, esAbort, esH, Expr.eval, Expr.v0, Expr.v1]
                exact fun _ => hsAccInv)
            (by simp [prngCommitPrivPost, hCSome, prngPrivPot, esSetG, letE_eval, esMk, esAbort,
                  esH, Expr.eval, Expr.v0, Expr.v1])
      · refine potInv_ret ?_ ?_
        · simp only [esSetG, esSetH, letE_eval, esMk, esAbort, esG, esH, Expr.eval, Expr.v0,
          Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab]
          exact fun _ => prngGsInv_ite
            (cGsSetWin_gsInv _ _ _ (by simpa [esG, Expr.eval, Expr.v3] using hg0)) hg0
        · simp only [prngVRecvPrivPost, hSome, hInSome, esSetG, esSetH, letE_eval, esMk, esAbort,
          esG, esH, Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab]
          refine Nat.le_trans
            (Nat.le_of_eq (prngPrivPot_mk_eq qep (g2 := (esE.eval ρ).1) (h2 := (esE.eval ρ).2.1)
              (ite_fst_eq_prng (by rw [cGsSetWin_st_prng]; rfl) rfl))) ?_
          simp only [prngPrivPot, Bool.false_eq_true, ↓reduceIte]
          have hEqSum : prngPrivVpPot qep (esE.eval ρ).1.1.1 + prngPrivVpPot qep (esE.eval ρ).1.1.2
              = m_other + prngPrivVpPot qep (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2
              else (esE.eval ρ).1.1.1) := by simpa [prngPrivPot, hab] using hSum.symm
          omega
private theorem corrEC_priv_potOKInv (L B qep : ℕ) (tL : Option ℕ) (t : ℕ) (π : Policy) {Γ' : List
    (Ty S)} (esE : Expr OO Γ' prngEsTy) (pE : Expr OO Γ' .bool) (ρ : Env Γ') (hInv : prngPrivInv
    (esE.eval ρ)) : PotOKInv P_prng (fun x => prngPrivInv x.2) (fun x => prngPrivPot qep x.2)
    ((corrEC (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI :=
    sampI) (sampK := sampK) B ⟨false, tL, t⟩) L π esE pE).eval ρ) (prngPrivPot qep (esE.eval ρ)) :=
    by
  unfold corrEC; rw [eval_bind_ret]
  refine potInv_ite (fun _ => potInv_ret (by simpa [Expr.eval, Expr.v0] using hInv)
    (by simp [Expr.eval, Expr.v0])) (fun hNotRef => ?_)
  have hab : (esE.eval ρ).2.2 = false := by
    simp only [orE, esAbort, Expr.eval, Expr.v0, Env.get_cons_zero] at hNotRef
    cases h : (esE.eval ρ).2.2 <;> [rfl; simp [h] at hNotRef]
  have hg0 : prngGsInv (esE.eval ρ).1 := hInv hab
  refine potInv_ite (fun _ => potInv_ret
    (by simp [esSetAbort, letE_eval, esMk, Expr.eval, Expr.v0]; exact prngPrivInv_abort)
    (by simp [prngPrivPot, esSetAbort, letE_eval, esMk, Expr.eval, Expr.v0])) (fun _ => ?_)
  rw [eval_bind]
  refine PotOKInv.bindSupp (r := prngPrivPot qep (esE.eval ρ)) (Comp.queryBound_eval P_prng
    (fun _ => 1) (fun _ => 0) (fun _ _ _ => Nat.le_refl 1) prngIface_fwdU_zero _ _) (fun _ _ => ?_)
    (by simp [hooksPRNGC, prngRevealC_queries])
  refine potInv_caseOpt
    (fun _ => potInv_ret (by simp [esMk, Expr.eval]; exact prngPrivInv_abort)
      (by simp [prngPrivPot, esMk, Expr.eval]))
    (fun _ _ => potInv_ret
      (by simp only [esMk, esAbort, Expr.eval, Expr.v2, Env.get_cons_succ, Env.get_cons_zero, hab]
          exact fun _ => cAfterCorrE_gsInv L (esG (.fst .v2)) (.snd .v2) _
            (by simpa [esG, Expr.eval, Expr.v2] using hg0))
      (by simp [prngPrivPot, esMk, esAbort, esG, cAfterCorrE_st_prng, Expr.eval, Expr.v2]))
private theorem implEC_priv_potOKInv (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) (cfg :
    ConfigEC OO) (π : Policy) {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy) (qE : Expr OO Γ'
    (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) (ρ : Env Γ') (hInv : prngPrivInv (esE.eval ρ)) :
    PotOKInv P_prng (fun x => prngPrivInv x.2) (fun x => prngPrivPot qep x.2) ((implEC (hooksPRNGC
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK :=
    sampK) B ⟨false, tL, t⟩) L (2 + Δcka) qep maxSkip cfg π esE qE).eval ρ) (prngPrivPot qep
    (esE.eval ρ)) := by
  unfold implEC; rw [eval_bind_ret]
  refine potInv_caseSum (fun _ _ => potInv_caseSum (fun _ _ => potInv_caseSum
    (fun _ _ => potInv_caseSum (fun _ _ => ?_) (fun _ _ => ?_)) (fun _ _ => ?_)) (fun _ _ => ?_))
    (fun _ _ => ?_)
  · rw [eval_bind]; exact PotOKInv.bindPot (transmitEC_priv_potOKInv L B Δcka qep tL t π (.fst
      (Expr.v4 (O := OO))) .v0 _ (by simpa [Expr.eval, Expr.v4] using hInv)) (fun _ hOut =>
      potInv_ret (by simpa [Expr.eval, Expr.v0] using hOut) (by simp [Expr.eval, Expr.v0]))
  · rw [eval_bind]; exact PotOKInv.bindPot (challEC_priv_potOKInv L B Δcka qep tL t cfg π (.fst
      (Expr.v4 (O := OO))) .v0 _ (by simpa [Expr.eval, Expr.v4] using hInv)) (fun _ hOut =>
      potInv_ret (by simpa [Expr.eval, Expr.v0] using hOut) (by simp [Expr.eval, Expr.v0]))
  · rw [eval_bind]; exact PotOKInv.bindPot (deliverEC_priv_potOKInv L B maxSkip qep tL t cfg (.fst
      (Expr.v3 (O := OO))) .v0 _ (by simpa [Expr.eval, Expr.v3] using hInv)) (fun _ hOut =>
      potInv_ret (by simpa [Expr.eval, Expr.v0] using hOut) (by simp [Expr.eval, Expr.v0]))
  · rw [eval_bind]; exact PotOKInv.bindPot (injectEC_priv_potOKInv L B Δcka qep tL t cfg (.fst
      (Expr.v2 (O := OO))) .v0 _ (by simpa [Expr.eval, Expr.v2] using hInv)) (fun _ hOut =>
      potInv_ret (by simpa [Expr.eval, Expr.v0] using hOut) (by simp [Expr.eval, Expr.v0]))
  · rw [eval_bind]; exact PotOKInv.bindPot (corrEC_priv_potOKInv L B qep tL t π (.fst
      (Expr.v1 (O := OO))) .v0 _ (by simpa [Expr.eval, Expr.v1] using hInv)) (fun _ hOut =>
      potInv_ret (by simpa [Expr.eval, Expr.v0] using hOut) (by simp [Expr.eval, Expr.v0]))
private theorem initPRNGEStateC_priv_potOKInv (qep : ℕ) (tL : Option ℕ) (t : ℕ) {Γ' : List (Ty S)}
    (bE : Expr OO Γ' .bool) (ρ : Env Γ') : PotOKInv P_prng prngPrivInv (prngPrivPot qep)
    ((initPRNGEStateC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI :=
    sampI) (sampK := sampK) ⟨false, tL, t⟩ bE).eval ρ) (2 * qep + 2) := by
  unfold initPRNGEStateC; rw [eval_bind_ret, eval_bind]
  refine PotOKInv.bindSupp (m := 0) (r := 2 * qep + 2) ((Comp.queryBound_eval P_prng (fun _ => 1)
    (fun _ => 0) (fun _ _ _ => Nat.le_refl 1) prngIface_fwdU_zero
    (Comp.sample (O := OO) (I := II) CKASamp.kc (.unit)) (.cons (bE.eval ρ) ρ)).mono
    (by simp [Comp.queries])) (fun kc _ => ?_) (Nat.zero_add _).le
  rw [eval_bind]
  refine PotOKInv.bindSupp (m := 2) (r := 2 * qep) ((Comp.queryBound_eval P_prng (fun _ => 1)
    (fun _ => 0) (fun _ _ _ => Nat.le_refl 1) prngIface_fwdU_zero
    (rootPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI)
      (sampK := sampK) ⟨false, tL, t⟩ (.nat 0) (Expr.op (O := OO) CKAOp.lamI .unit) .none)
    (.cons kc (.cons (bE.eval ρ) ρ))).mono (by simp [rootPRNGC_queries])) (fun _ _ => ?_) (by omega)
  refine potInv_caseOpt (fun _ => potInv_ret (by simp [esMk, Expr.eval]; exact prngPrivInv_abort)
    (by simp [prngPrivPot, esMk, Expr.eval])) (fun _ _ => potInv_ret ?_ ?_)
  · intro _
    simp only [esMk, cGsInitE, cGsMk, mkPartiesE, vpMk, partyEnc, Expr.eval, Expr.v0,
      Env.get_cons_zero]
    exact ⟨rfl, rfl, Nat.le_refl 0, Nat.le_refl 0, fun _ hr => by simp at hr⟩
  · have hSum := prngPrivPartyCount_zero_sum qep
    simp only [prngPrivPot, prngPrivVpPot, esMk, cGsInitE, cGsMk, mkPartiesE, vpMk,
      partyDec_partyEnc, Expr.eval, Bool.false_eq_true, ↓reduceIte]
    omega
/-- Unconditional `2 * qep + 2` PRF-PRNG query bound for `redPRNGPrivProg`. -/
theorem redPRNGPrivProg_queries_qep (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) (A :
    Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) : (((redPRNGPrivProg (ckaInitA :=
    ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit :=
    prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins :=
    sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip tL t).eval (fun _ => A)
    ())).IsQueryBoundP (· matches .inr _) (2 * qep + 2) := by
  suffices hGame : (((redPRNGPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend :=
      ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender :=
      fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK :=
      sampK) L B Δcka qep maxSkip tL t).eval (fun _ => A) ())).IsQueryBoundP P_prng (2 * qep + 2) by
    exact hGame.of_imp (fun x hx => by cases x <;> [cases hx; trivial])
  set R := redPRNGPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender :=
    fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR
    := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B
    Δcka qep maxSkip tL t
  have hInit : PotOKInv P_prng (fun as : (Ty.prod .unit prngEsTy : Ty S).denote => prngPrivInv as.2)
      (fun as => prngPrivPot qep as.2) (R.init.eval (Env.cons (t := .unit) () .nil)) (2 * qep + 2)
      := by
    dsimp only [R, redPRNGPrivProg]; rw [eval_bind]
    refine PotOKInv.bindSupp (r := 2 * qep + 2)
      (Comp.queryBound_eval P_prng (fun _ => 1) (fun _ => 0)
        (fun _ _ _ => Nat.le_refl 1) prngIface_fwdU_zero _ _)
      (fun b0 _ => ?_) (by simp [Comp.queries])
    rw [eval_bind]
    exact PotOKInv.bindPot
      (initPRNGEStateC_priv_potOKInv (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
        qep tL t .v0 (Env.cons (t := .bool) b0 (Env.cons (t := .unit) () .nil)))
      (fun _ hEs => potInv_ret (by simpa [Expr.eval, Expr.v0] using hEs)
        (by simp [Expr.eval, Expr.v0]))
  unfold CostedReduction.eval CostedReduction.impl
  refine hInit.run _ ?_; rintro ⟨_, s0⟩ hs0
  have hSim := potOKInv_simulateQ_handlerImpl_c0 prngPrivInv (prngPrivPot qep) (prngIface_fwdU_zero
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK :=
    sampK)) R.handle (fun qv sv hsv => implEC_priv_potOKInv L B Δcka qep maxSkip tL t (modeCfgEC OO
    ⟨false, tL, t⟩) (⟨false, tL, t⟩ : Mode).policy .v0 .v1 (.cons sv (.cons qv .nil)) hsv) A hs0
  refine hSim.run _ ?_; rintro ⟨bOut, sOut⟩ _
  exact (Comp.queryBound_eval P_prng (fun _ => 1) (fun _ => 0)
    (fun _ _ _ => Nat.le_refl 1) prngIface_fwdU_zero R.finish
    (.cons sOut (.cons bOut .nil))).mono (by simp [R, redPRNGPrivProg, privOutC, Comp.queries])
/-- Combined `min (2 + 2 * q) (min (q + 3) (2 * qep + 2))` PRF-PRNG query bound for
`redPRNGPrivProg`. -/
theorem redPRNGPrivProg_makesAtMostQueries (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t q : ℕ) (A :
    Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) (hA : MakesAtMostQueries A q) :
    (((redPRNGPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender :=
    fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR
    := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B
    Δcka qep maxSkip tL t).eval (fun _ => A) ())).IsQueryBoundP (· matches .inr _) (min (2 + 2 * q)
    (min (q + 3) (2 * qep + 2))) := by
  have h12 := redPRNGPrivProg_makesAtMostQueries_q3 (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive
    := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE :=
    defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI)
    (sampK := sampK) L B Δcka qep maxSkip tL t q A hA
  have h3 := redPRNGPrivProg_queries_qep (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend :=
    ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender :=
    fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR
    := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B
    Δcka qep maxSkip tL t A
  have hMin := isQueryBoundP_min_prng h12 h3
  rwa [Nat.min_assoc] at hMin

end PrngPrivQepPotOK

end

end Computational.Proofs.ReductionDsl.SM.RedPRNGPrivQepPotOK
