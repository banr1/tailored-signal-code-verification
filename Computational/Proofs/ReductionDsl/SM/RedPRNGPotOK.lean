/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.RedPRNG -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Potential -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.Notation

/-!
# Potential-Based PRF-PRNG Query Bounds

Proves `min (2 + 2 * q) (q + 3)` PRF-PRNG query bounds (`PotOKSPrng`) for `redPRNGAuthProg`,
`redPRNGAuthStage2Prog`, and `redPRNGPrivProg`.
-/

namespace Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK

public section

set_option autoImplicit false

open OracleSpec OracleComp
open _root_.ReductionDsl
  (Sig Ty Ops Iface Env Expr Comp GameCodec CostedReduction handlerImpl isGameQuery)
open _root_.Computational.Proofs.GameHop.ReductionDsl.SupportWP
  (PotOK potC_ret potC_ite potC_caseOpt potC_caseSum)
open _root_.CryptoGames (Party)
open _root_.CryptoGames.CKA (CKASamp CKAOp ckaSMQ ckaHdrTy ckaHdrCtTy)
open _root_.CryptoGames.PRFPRNG (prngSig prngOps prngIface prngSMCodec)
open _root_.CryptoGames.SM
  (Adversary MakesAtMostQueries posTy partyDec partyDec_partyEnc sendsInE otherE pGet pSet
   orE isSomeE letE_eval pair_eval ite_eval some_eval orE_eval sendsInE_eval)
open _root_.CryptoGames.SM.Engine
  (HooksC ConfigEC Policy modeCfgEC cRecTy cGsTy esTy
   esG esH esAbort esMk esSetG esSetH esSetAbort
   cGsSt cGsEpoch cGsWin cGsB cGsMk cGsSetStP cGsSetWin cRecPos
   cLeakE cEpMgmtE cDeleteE cAcceptE cRecordE cAfterCorrE authOutE privOutC
   mkPartiesE cGsInitE
   vpMk vpId vpTcur vpTcurNat vpΓ vpRoot vpSetVS vpSetVR
   vSendStep1C vSendC vRecvStep1C vRecvC commitEC
   transmitEC challEC deliverEC injectEC corrEC implEC
   eval_bind eval_bind_ret eval_ret)
open _root_.CryptoGames.SM.Construction
  (Header PartyState Mode
   prngHsTy prngVpTy prngEsTy prngStage2EsTy
   prngProcessCorrC rootPRNGC rootPRNGC_queries
   prngStartSendC prngStartRecvC prngStartRecvMainC
   prngFsSendC prngFsRecvC prngCommitC prngRevealC prngRevealC_queries
   hooksPRNGC hooksPRNGMainC initPRNGEStateC
   redPRNGAuthProg redPRNGAuthProg_totalQueries
   redPRNGAuthStage2Prog
   redPRNGPrivProg redPRNGPrivProg_totalQueries)

section PrngPotOK

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

local notation "OO" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

local notation "II" =>
  prngIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

local notation "P_prng" => isGameQuery (G := CryptoGames.PRFPRNG.spec RSt I K)

@[expose] def prngReady (mo : Mode) (P : Party) (e : ℕ) : ℕ :=
  if P.sendsIn (e + 1) && decide (e + 1 ≤ mo.tStar) then 1 else 0

@[expose] def prngVpReady (mo : Mode)
    (vp : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote) : ℕ :=
  prngReady mo (partyDec vp.1) vp.2.2.2.2.2.2

@[expose] def prngPot (mo : Mode)
    (es : (@prngEsTy KC Γ CCoins T I KR RSt K SS RS M E).denote) : ℕ :=
  if es.2.2 then 0 else prngVpReady mo es.1.1.1 + prngVpReady mo es.1.1.2

theorem prngReady_le_one (mo : Mode) (P : Party) (e : ℕ) :
    prngReady mo P e ≤ 1 := by
  unfold prngReady; split <;> omega

theorem party_sendsIn_succ_false (P : Party) (n : ℕ) (h : P.sendsIn n = true) :
    P.sendsIn (n + 1) = false := by
  cases P <;> simp [Party.sendsIn] at h ⊢ <;> omega

@[expose] def prngOtherPot (mo : Mode)
    (stAB : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote ×
      (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote)
    (p : Bool) : ℕ :=
  if p then prngVpReady mo stAB.1 else prngVpReady mo stAB.2

theorem pGet_eval_st_prng {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (st : Expr O' Γ' (.prod vpT vpT)) (p : Expr O' Γ' .bool) (ρ : Env Γ') :
    (pGet st p).eval ρ = if p.eval ρ then (st.eval ρ).2 else (st.eval ρ).1 := by
  cases hp : (p.eval ρ : Bool) <;> simp [pGet, Expr.eval, Expr.v0, hp]

theorem pSet_eval_st_prng {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (st : Expr O' Γ' (.prod vpT vpT)) (p : Expr O' Γ' .bool) (v : Expr O' Γ' vpT) (ρ : Env Γ') :
    (pSet st p v).eval ρ =
      if p.eval ρ then ((st.eval ρ).1, v.eval ρ) else (v.eval ρ, (st.eval ρ).2) := by
  cases hp : (p.eval ρ : Bool) <;> simp [pSet, Expr.eval, Expr.v0, hp]

theorem prngOtherPot_add_pGet (mo : Mode)
    (stAB : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote ×
      (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote) (p : Bool) :
    prngOtherPot mo stAB p + prngVpReady mo (if p then stAB.2 else stAB.1) =
      prngVpReady mo stAB.1 + prngVpReady mo stAB.2 := by
  cases p <;> simp [prngOtherPot, Nat.add_comm]

theorem prngPot_pSet_eq (mo : Mode)
    (stAB : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote ×
      (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote)
    (p : Bool) (vp' : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote) :
    (let st' := if p then (stAB.1, vp') else (vp', stAB.2);
     prngVpReady mo st'.1 + prngVpReady mo st'.2) =
      prngOtherPot mo stAB p + prngVpReady mo vp' := by
  cases p <;> simp [prngOtherPot, Nat.add_comm]

theorem cLeakE_st_prng {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (s : Expr O' Γ' (cGsTy vpT)) (l : Expr O' Γ' .nat) (ρ : Env Γ') :
    ((cLeakE s l).eval ρ).1 = (s.eval ρ).1 := by
  simp [cLeakE, cGsMk, cGsSt, Expr.eval, Expr.v0]

theorem cEpMgmtE_some_st_prng {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
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
    exact cLeakE_st_prng _ _ _
  · simp only [some_eval, Option.some.injEq] at h; subst h; rfl
  · cases h
  · simp only [some_eval, Option.some.injEq] at h; subst h; rfl

theorem cDeleteE_st_prng {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (L : ℕ) (s : Expr O' Γ' (cGsTy vpT)) (pos : Expr O' Γ' posTy) (ρ : Env Γ') :
    ((cDeleteE L s pos).eval ρ).1 = (s.eval ρ).1 := by
  simp [cDeleteE, cGsMk, cGsSt, Expr.eval, Expr.v0]

theorem cAcceptE_st_prng {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (L : ℕ) (s : Expr O' Γ' (cGsTy vpT)) (p : Expr O' Γ' .bool)
    (st' : Expr O' Γ' vpT) (pos : Expr O' Γ' posTy) (ρ : Env Γ') :
    ((cAcceptE L s p st' pos).eval ρ).1 =
      if p.eval ρ then ((s.eval ρ).1.1, st'.eval ρ) else (st'.eval ρ, (s.eval ρ).1.2) := by
  cases hp : (p.eval ρ : Bool) <;>
    simp [cAcceptE, cGsMk, cGsSt, pSet_eval_st_prng, cDeleteE_st_prng, Expr.eval, Expr.v0, hp]

theorem cGsSetStP_st_prng {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (s : Expr O' Γ' (cGsTy vpT)) (p : Expr O' Γ' .bool) (st' : Expr O' Γ' vpT) (ρ : Env Γ') :
    ((cGsSetStP s p st').eval ρ).1 =
      if p.eval ρ then ((s.eval ρ).1.1, st'.eval ρ) else (st'.eval ρ, (s.eval ρ).1.2) := by
  cases hp : (p.eval ρ : Bool) <;>
    simp [cGsSetStP, cGsMk, cGsSt, pSet_eval_st_prng, Expr.eval, Expr.v0, hp]

theorem cGsSetWin_st_prng {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (s : Expr O' Γ' (cGsTy vpT)) (w : Expr O' Γ' .bool) (ρ : Env Γ') :
    ((cGsSetWin s w).eval ρ).1 = (s.eval ρ).1 := by
  simp [cGsSetWin, cGsMk, cGsSt, Expr.eval, Expr.v0]

theorem cRecordE_st_prng {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (L Δ : ℕ) (s : Expr O' Γ' (cGsTy vpT)) (p : Expr O' Γ' .bool)
    (st' : Expr O' Γ' vpT) (r : Expr O' Γ' cRecTy) (isChall : Expr O' Γ' .bool) (ρ : Env Γ') :
    ((cRecordE L Δ s p st' r isChall).eval ρ).1 =
      if p.eval ρ then ((s.eval ρ).1.1, st'.eval ρ) else (st'.eval ρ, (s.eval ρ).1.2) := by
  cases hp : (p.eval ρ : Bool) <;>
    simp [cRecordE, cGsMk, cGsSt, pSet_eval_st_prng, Expr.eval, Expr.v0, hp]

theorem cAfterCorrE_st_prng {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (L : ℕ) (s : Expr O' Γ' (cGsTy vpT)) (p : Expr O' Γ' .bool) (ρ : Env Γ') :
    ((cAfterCorrE L s p).eval ρ).1 = (s.eval ρ).1 := by
  simp [cAfterCorrE, cGsMk, cGsSt, cLeakE_st_prng, Expr.eval, Expr.v0]

theorem isQueryBoundP_min_prng {ι' : Type} {spec' : OracleSpec.{0, 0} ι'} {α : Type}
    {P : ι' → Prop} [DecidablePred P] {oa : OracleComp spec' α} {a b : ℕ}
    (ha : oa.IsQueryBoundP P a) (hb : oa.IsQueryBoundP P b) :
    oa.IsQueryBoundP P (min a b) := by
  rcases Nat.le_total a b with h | h
  · rwa [Nat.min_eq_left h]
  · rwa [Nat.min_eq_right h]

theorem prngIface_fwdU_zero (n : ℕ) :
    ((II).fwdU n).IsQueryBoundP P_prng 0 := by
  change OracleComp.IsQueryBoundP
    (liftM (OracleSpec.query (spec := unifSpec + CryptoGames.PRFPRNG.spec RSt I K) (.inl n)))
    P_prng 0
  rw [← bind_pure (liftM _), isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (by simp [isGameQuery]), fun _ => by simp⟩

structure PotOKSPrng {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {α : Type}
    (P : ι' → Prop) [DecidablePred P] (B : α → ℕ) (oa : OracleComp T' α) (n : ℕ) : Prop where
  run : PotOK P B oa n

theorem PotOKSPrng.bindPot {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {α γ : Type}
    {P : ι' → Prop} [DecidablePred P] {B₁ : α → ℕ} {B₂ : γ → ℕ}
    {oa : OracleComp T' α} {f : α → OracleComp T' γ} {n : ℕ}
    (h1 : PotOKSPrng P B₁ oa n) (h2 : ∀ a, PotOKSPrng P B₂ (f a) (B₁ a)) :
    PotOKSPrng P B₂ (oa >>= f) n :=
  ⟨PotOK.bindPot h1.run (fun a => (h2 a).run)⟩

theorem PotOKSPrng.bind' {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {α γ : Type}
    {P : ι' → Prop} [DecidablePred P] {B : γ → ℕ}
    {oa : OracleComp T' α} {f : α → OracleComp T' γ} {m n r : ℕ}
    (hoa : oa.IsQueryBoundP P m) (hf : ∀ a, PotOKSPrng P B (f a) r) (hmn : m + r ≤ n) :
    PotOKSPrng P B (oa >>= f) n :=
  ⟨PotOK.bind' hoa (fun a => (hf a).run) hmn⟩

theorem potSPrng_ret {S' : Sig} {ι' : Type} {T' : OracleSpec.{0, 0} ι'}
    {O' : Ops S'} {I' : Iface S' T'} {P : ι' → Prop} [DecidablePred P]
    {Γ' : List (Ty S')} {τ : Ty S'} {B : τ.denote → ℕ}
    {e : Expr O' Γ' τ} {ρ : Env Γ'} {n : ℕ} (h : B (e.eval ρ) ≤ n) :
    PotOKSPrng P B ((Comp.ret (I := I') e).eval ρ) n := ⟨potC_ret e ρ h⟩

theorem potSPrng_ite {S' : Sig} {ι' : Type} {T' : OracleSpec.{0, 0} ι'}
    {O' : Ops S'} {I' : Iface S' T'} {P : ι' → Prop} [DecidablePred P]
    {Γ' : List (Ty S')} {τ : Ty S'} {B : τ.denote → ℕ}
    {cond : Expr O' Γ' .bool} {t f : Comp O' I' Γ' τ} {ρ : Env Γ'} {n : ℕ}
    (ht : cond.eval ρ = true → PotOKSPrng P B (t.eval ρ) n)
    (hf : cond.eval ρ = false → PotOKSPrng P B (f.eval ρ) n) :
    PotOKSPrng P B ((Comp.ite cond t f).eval ρ) n :=
  ⟨potC_ite cond t f ρ (fun h => (ht h).run) (fun h => (hf h).run)⟩

theorem potSPrng_caseOpt {S' : Sig} {ι' : Type} {T' : OracleSpec.{0, 0} ι'}
    {O' : Ops S'} {I' : Iface S' T'} {P : ι' → Prop} [DecidablePred P]
    {Γ' : List (Ty S')} {α τ : Ty S'} {B : τ.denote → ℕ}
    {scrut : Expr O' Γ' (.opt α)} {onNone : Comp O' I' Γ' τ}
    {onSome : Comp O' I' (α :: Γ') τ} {ρ : Env Γ'} {n : ℕ}
    (hNone : scrut.eval ρ = none → PotOKSPrng P B (onNone.eval ρ) n)
    (hSome : ∀ v, scrut.eval ρ = some v → PotOKSPrng P B (onSome.eval (.cons v ρ)) n) :
    PotOKSPrng P B ((Comp.caseOpt scrut onNone onSome).eval ρ) n :=
  ⟨potC_caseOpt scrut onNone onSome ρ (fun h => (hNone h).run) (fun v h => (hSome v h).run)⟩

theorem potSPrng_caseSum {S' : Sig} {ι' : Type} {T' : OracleSpec.{0, 0} ι'}
    {O' : Ops S'} {I' : Iface S' T'} {P : ι' → Prop} [DecidablePred P]
    {Γ' : List (Ty S')} {α β τ : Ty S'} {B : τ.denote → ℕ}
    {scrut : Expr O' Γ' (.sum α β)} {onInl : Comp O' I' (α :: Γ') τ}
    {onInr : Comp O' I' (β :: Γ') τ} {ρ : Env Γ'} {n : ℕ}
    (hInl : ∀ v, scrut.eval ρ = .inl v → PotOKSPrng P B (onInl.eval (.cons v ρ)) n)
    (hInr : ∀ v, scrut.eval ρ = .inr v → PotOKSPrng P B (onInr.eval (.cons v ρ)) n) :
    PotOKSPrng P B ((Comp.caseSum scrut onInl onInr).eval ρ) n :=
  ⟨potC_caseSum scrut onInl onInr ρ (fun v h => (hInl v h).run) (fun v h => (hInr v h).run)⟩

theorem ite_fst_eq_prng {α β : Type} {P_cond : Prop} [Decidable P_cond]
    {g1 g2 : α × β} {x : α} (h1 : g1.1 = x) (h2 : g2.1 = x) :
    (if P_cond then g1 else g2).1 = x := by
  by_cases hc : P_cond <;> simp [hc, h1, h2]

theorem prngPot_mk_eq (mo : Mode)
    {g1 g2 : (@cGsTy KC Γ CCoins T I KR RSt K SS RS M E prngVpTy).denote}
    {h1 h2 : (@prngHsTy KC Γ CCoins T I KR RSt K SS RS M E).denote} {ab : Bool}
    (hst : g1.1 = g2.1) :
    prngPot mo (g1, h1, ab) = prngPot mo (g2, h2, ab) := by
  simp only [prngPot, hst]

theorem potSPrng_comp_const {Γ' : List (Ty S)} {τ : Ty S}
    (c : Comp OO II Γ' τ) (ρ : Env Γ') {B : τ.denote → ℕ} (r n : ℕ)
    (hB : ∀ a, B a ≤ r) (hq : c.queries (fun _ => 1) (fun _ => 0) + r ≤ n) :
    PotOKSPrng P_prng B (c.eval ρ) n :=
  ⟨fun {_} _ hk =>
    (isQueryBoundP_bind
      (Comp.queryBound_eval P_prng (fun _ => 1) (fun _ => 0)
        (fun _ _ _ => Nat.le_refl 1) prngIface_fwdU_zero c ρ)
      (fun a _ => (hk a).mono (hB a))).mono hq⟩

theorem potOKS_simulateQ_handlerImpl_step1_prng
    {S' : Sig} {O' : Ops S'} {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {I' : Iface S' T'}
    {κ : Type} {G : OracleSpec.{0, 0} κ} {C : GameCodec S' G} {σ : Ty S'} {α : Type}
    {P : ι' → Prop} [DecidablePred P] (B : σ.denote → ℕ)
    (hU : ∀ n, (I'.fwdU n).IsQueryBoundP P 0) (h : Comp O' I' [σ, C.Q] (.prod C.R σ))
    (hStep : ∀ (m : ℕ) q s, PotOKSPrng P (fun x : C.R.denote × σ.denote => m + B x.2)
      (h.eval (.cons s (.cons q .nil))) (1 + m + B s))
    {mx : OracleComp (unifSpec + G) α} {qAdv : ℕ}
    (hq : mx.IsQueryBoundP (isGameQuery (G := G)) qAdv) (st : σ.denote) :
    PotOKSPrng P (fun _ : α × σ.denote => 0)
      ((simulateQ (handlerImpl (C := C) h) mx).run st) (qAdv + B st) := by
  induction mx using OracleComp.inductionOn generalizing qAdv st with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact ⟨fun {β} k hk => by simpa using (hk (a, st)).mono (Nat.zero_le (qAdv + B st))⟩
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [simulateQ_query_bind, StateT.run_bind]
    rcases q with uq | gq
    · change PotOKSPrng P _
        ((do let u ← I'.fwdU uq; return (u, st)) >>=
          fun x => (simulateQ (handlerImpl (C := C) h) (k x.1)).run x.2) (qAdv + B st)
      rw [bind_assoc]
      refine PotOKSPrng.bind' (m := 0) (r := qAdv + B st) (hU uq) (fun u => ?_) (by omega)
      rw [pure_bind]; exact ih u (by simpa [isGameQuery] using hq.2 u) st
    · have hpos : 0 < qAdv := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      change PotOKSPrng P _
        ((do let p ← h.eval (.cons st (.cons (C.qenc gq) .nil)); return (C.rdec gq p.1, p.2)) >>=
          fun x => (simulateQ (handlerImpl (C := C) h) (k x.1)).run x.2) ((m + 1) + B st)
      rw [show (m + 1) + B st = 1 + m + B st by omega, bind_assoc]
      refine PotOKSPrng.bindPot (hStep m (C.qenc gq) st) (fun p => ?_)
      rw [pure_bind]; exact ih (C.rdec gq p.1) (by simpa [isGameQuery] using hq.2 (C.rdec gq p.1)) p.2

theorem rootPRNGC_potOKS (mo : Mode) {Γ' : List (Ty S)}
    (tE : Expr OO Γ' .nat) (ikE : Expr OO Γ' (.base .i)) (σvE : Expr OO Γ' (.opt (.base .sig)))
    (ρ : Env Γ') (r : ℕ) :
    PotOKSPrng P_prng (fun _ => r)
      ((rootPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) mo tE ikE σvE).eval ρ)
      ((if decide (tE.eval ρ ≤ mo.tStar) then 2 else 0) + r) := by
  unfold rootPRNGC; rw [eval_bind_ret]
  refine potSPrng_ite (fun hlt => ?_) (fun hle => ?_)
  · have hleFalse : decide (tE.eval ρ ≤ mo.tStar) = false :=
      decide_eq_false (Nat.not_le_of_gt (of_decide_eq_true hlt))
    exact potSPrng_comp_const _ _ r _ (fun _ => Nat.le_refl r) (by simp [Comp.queries, hleFalse])
  · have hleTrue : decide (tE.eval ρ ≤ mo.tStar) = true :=
      decide_eq_true (Nat.le_of_not_lt (of_decide_eq_false hle))
    exact potSPrng_comp_const _ _ r _ (fun _ => Nat.le_refl r)
      (by simp [prngProcessCorrC, Comp.queries, hleTrue])

theorem prngStartSendC_potOKS (mo : Mode) {Γ' : List (Ty S)}
    (hE : Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat) (γE : Expr OO Γ' (.base .γ))
    (σvE : Expr OO Γ' (.opt (.base .sig))) (rE : Expr OO Γ' (.opt (.base .ccoins)))
    (ρ : Env Γ') (r : ℕ) :
    PotOKSPrng P_prng (fun _ => r)
      ((prngStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) mo hE ctxE pE tE γE σvE rE).eval ρ)
      ((if decide (tE.eval ρ ≤ mo.tStar) then 2 else 0) + r) := by
  unfold prngStartSendC; rw [eval_bind_ret, eval_bind]
  refine PotOKSPrng.bindPot
    (potSPrng_comp_const _ _ ((if decide (tE.eval ρ ≤ mo.tStar) then 2 else 0) + r)
      ((if decide (tE.eval ρ ≤ mo.tStar) then 2 else 0) + r)
      (fun _ => Nat.le_refl _) (by simp [Comp.queries])) (fun coins => ?_)
  rw [eval_bind]
  have hRoot := rootPRNGC_potOKS (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    mo (.fst (.snd (Expr.v1 (O := OO))))
    (.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair (.fst (.snd (.snd .v1))) .v0))))
    (.fst (.snd (.snd (.snd .v1))))
    (.cons coins (.cons (hE.eval ρ, tE.eval ρ, γE.eval ρ, σvE.eval ρ, rE.eval ρ) ρ)) r
  simp only [Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ] at hRoot
  exact PotOKSPrng.bindPot hRoot (fun _ =>
    potSPrng_caseOpt (fun _ => potSPrng_ret (Nat.le_refl r))
      (fun _ _ => potSPrng_ret (Nat.le_refl r)))

theorem prngStartRecvC_potOKS (mo : Mode) {Γ' : List (Ty S)}
    (hE : Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat) (γE : Expr OO Γ' (.base .γ))
    (σvE : Expr OO Γ' (.opt (.base .sig))) (tnE : Expr OO Γ' (.base .t))
    (ρ : Env Γ') (r : ℕ) :
    PotOKSPrng P_prng (fun _ => r)
      ((prngStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) mo hE ctxE pE tE γE σvE tnE).eval ρ)
      ((if mo.auth && decide (tE.eval ρ = mo.tStar) then 1 else 0) + r) := by
  unfold prngStartRecvC; rw [eval_bind_ret]
  refine potSPrng_caseOpt (fun _ => ?_) (fun _ _ => potSPrng_ret (by omega))
  refine potSPrng_ite (fun hc => ?_) (fun _ => potSPrng_ret (by omega))
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hc
  exact potSPrng_comp_const _ _ r _ (fun _ => Nat.le_refl r) (by simp [Comp.queries, hc])

@[local simp] private theorem prngStartRecvMainC_queries {Γ' : List (Ty S)}
    (hE : Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat) (γE : Expr OO Γ' (.base .γ))
    (σvE : Expr OO Γ' (.opt (.base .sig))) (tnE : Expr OO Γ' (.base .t)) :
    (prngStartRecvMainC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) hE ctxE pE tE γE σvE tnE).queries
      (fun _ => 1) (fun _ => 0) = 0 := by
  simp [prngStartRecvMainC, Comp.queries]

theorem prngStartRecvMainC_potOKS (mo : Mode) {Γ' : List (Ty S)}
    (hE : Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat) (γE : Expr OO Γ' (.base .γ))
    (σvE : Expr OO Γ' (.opt (.base .sig))) (tnE : Expr OO Γ' (.base .t))
    (ρ : Env Γ') (r : ℕ) :
    PotOKSPrng P_prng (fun _ => r)
      ((prngStartRecvMainC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) hE ctxE pE tE γE σvE tnE).eval ρ)
      ((if mo.auth && decide (tE.eval ρ = mo.tStar) then 1 else 0) + r) :=
  potSPrng_comp_const _ ρ r _ (fun _ => Nat.le_refl r) (by simp)

structure PrngHooksSpec (B : ℕ) (mo : Mode)
    (hk : HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) prngHsTy) :
    Prop where
  hStartSend : ∀ {Γ' : List (Ty S)} (hE : Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat) (γE : Expr OO Γ' (.base .γ))
    (σvE : Expr OO Γ' (.opt (.base .sig))) (rE : Expr OO Γ' (.opt (.base .ccoins))),
    hk.startSend hE ctxE pE tE γE σvE rE =
      prngStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) mo hE ctxE pE tE γE σvE rE
  hStartRecv : ∀ {Γ' : List (Ty S)} (hE : Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat) (γE : Expr OO Γ' (.base .γ))
    (σvE : Expr OO Γ' (.opt (.base .sig))) (tnE : Expr OO Γ' (.base .t)) (ρ : Env Γ') (r : ℕ),
    PotOKSPrng P_prng (fun _ => r) ((hk.startRecv hE ctxE pE tE γE σvE tnE).eval ρ)
      ((if mo.auth && decide (tE.eval ρ = mo.tStar) then 1 else 0) + r)
  hFsSend : ∀ {Γ' : List (Ty S)} (hE : Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat) (ssE : Expr OO Γ' (.base .ss))
    (hdrE : Expr OO Γ' hdrTy) (mE : Expr OO Γ' (.base .msg))
    (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))),
    hk.fsSend hE ctxE pE tE ssE hdrE mE pairE =
      prngFsSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) hE ctxE pE tE ssE hdrE mE pairE
  hFsRecv : ∀ {Γ' : List (Ty S)} (hE : Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat) (rsE : Expr OO Γ' (.base .rs))
    (hdrE : Expr OO Γ' hdrTy) (eE : Expr OO Γ' (.base .ct)) (recE : Expr OO Γ' (.opt cRecTy)),
    hk.fsRecv hE ctxE pE tE rsE hdrE eE recE =
      prngFsRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B hE ctxE pE tE rsE hdrE eE recE
  hCommit : ∀ {Γ' : List (Ty S)} (hE : Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (pE : Expr OO Γ' .bool) (oldE newE : Expr OO Γ' prngVpTy),
    hk.commit hE ctxE pE oldE newE =
      prngCommitC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) hE ctxE pE oldE newE
  hReveal : ∀ {Γ' : List (Ty S)} (hE : Expr OO Γ' prngHsTy) (ctxE : Expr OO Γ' (cGsTy prngVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' prngVpTy),
    hk.reveal hE ctxE pE vpE =
      prngRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) hE ctxE pE vpE

theorem hooksPRNGC_spec (B : ℕ) (mo : Mode) :
    PrngHooksSpec (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B mo (hooksPRNGC B mo) :=
  ⟨fun _ _ _ _ _ _ _ => rfl, prngStartRecvC_potOKS mo,
   fun _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl,
   fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem hooksPRNGMainC_spec (B : ℕ) (mo : Mode) :
    PrngHooksSpec (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B mo (hooksPRNGMainC B mo) :=
  ⟨fun _ _ _ _ _ _ _ => rfl, prngStartRecvMainC_potOKS mo,
   fun _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl,
   fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

@[expose] def prngVpOptPost (mo : Mode) (m m_other : ℕ)
    (res : (Ty.prod (.opt prngVpTy) prngHsTy : Ty S).denote) : ℕ :=
  match res.1 with
  | none => m
  | some vp' => m + m_other + prngVpReady mo vp'

theorem vSendStep1C_potOKS {B : ℕ} {mo : Mode}
    {hk : HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) prngHsTy}
    (hhk : PrngHooksSpec B mo hk) {Γ' : List (Ty S)} (hE : Expr OO Γ' prngHsTy)
    (ctxE : Expr OO Γ' (cGsTy prngVpTy)) (pE : Expr OO Γ' .bool)
    (sE : Expr OO Γ' prngVpTy) (rE : Expr OO Γ' (.opt (.base .ccoins)))
    (ρ : Env Γ') (m m_other : ℕ) :
    PotOKSPrng P_prng (prngVpOptPost mo m m_other)
      ((vSendStep1C hk hE ctxE pE sE rE).eval ρ)
      (1 + m + m_other + prngVpReady mo (sE.eval ρ)) := by
  unfold vSendStep1C; rw [eval_bind_ret]
  refine potSPrng_ite (fun hs => ?_) (fun _ => potSPrng_ret (by simp [prngVpOptPost, Expr.eval, Expr.v0]))
  rw [sendsInE_eval _ _ _ (partyDec (sE.eval ρ).1) (by simp [vpId, Expr.eval, Expr.v0])] at hs
  simp only [vpTcurNat, Expr.eval, Expr.v0, Env.get_cons_zero] at hs
  rw [hhk.hStartSend, eval_bind]
  have hSS := prngStartSendC_potOKS (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    mo (.fst (Expr.v0 (O := OO))) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.add (vpTcurNat (.fst (.snd (.snd (.snd .v0))))) (.nat 1))
    (vpΓ (.fst (.snd (.snd (.snd .v0))))) (vpRoot (.fst (.snd (.snd (.snd .v0)))))
    (.snd (.snd (.snd (.snd .v0))))
    (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, rE.eval ρ) ρ) (m + m_other)
  simp only [vpTcurNat, Expr.eval, Expr.v0, Env.get_cons_zero] at hSS
  have hBud :
      (if decide ((sE.eval ρ).2.2.2.2.2.2 + 1 ≤ mo.tStar) then 2 else 0) + (m + m_other) ≤
        1 + m + m_other + prngVpReady mo (sE.eval ρ) := by
    simp only [prngVpReady, prngReady, hs, Bool.true_and]; split <;> omega
  refine ⟨fun {_} k hk' => (PotOKSPrng.bindPot hSS (fun _ => ?_)).run k hk' |>.mono hBud⟩
  refine potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [prngVpOptPost, Expr.eval])) (fun _ _ => ?_)
  have hNextFalse := party_sendsIn_succ_false _ _ hs
  exact potSPrng_ret (by
    simp [prngVpOptPost, prngVpReady, prngReady, vpMk, vpId, vpTcurNat,
      Expr.eval, Expr.v0, Expr.v2, hNextFalse])

@[expose] def prngVSendPost (mo : Mode) (m m_other : ℕ)
    (res : (Ty.prod (.opt (.prod prngVpTy hdrCtTy)) prngHsTy : Ty S).denote) : ℕ :=
  match res.1 with
  | none => m
  | some (vp', _) => m + m_other + prngVpReady mo vp'

theorem vSendC_potOKS {B : ℕ} {mo : Mode}
    {hk : HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) prngHsTy}
    (hhk : PrngHooksSpec B mo hk) {Γ' : List (Ty S)} (hE : Expr OO Γ' prngHsTy)
    (ctxE : Expr OO Γ' (cGsTy prngVpTy)) (pE : Expr OO Γ' .bool)
    (sE : Expr OO Γ' prngVpTy) (mE : Expr OO Γ' (.base .msg))
    (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg))))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ') (m m_other : ℕ) :
    PotOKSPrng P_prng (prngVSendPost mo m m_other)
      ((vSendC hk hE ctxE pE sE mE pairE rE).eval ρ)
      (1 + m + m_other + prngVpReady mo (sE.eval ρ)) := by
  unfold vSendC; rw [eval_bind_ret, eval_bind]
  have h1 := vSendStep1C_potOKS hhk (.fst (Expr.v0 (O := OO)))
    (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
    (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
    (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, mE.eval ρ, pairE.eval ρ, rE.eval ρ) ρ)
    m m_other
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at h1
  refine PotOKSPrng.bindPot h1 (fun _ => ?_)
  refine potSPrng_caseOpt (fun hNone => ?_) (fun _ hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potSPrng_ret (by simp [prngVSendPost, prngVpOptPost, hNone, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potSPrng_caseOpt
      (fun _ => potSPrng_ret (by simp [prngVSendPost, prngVpOptPost, hSome, Expr.eval, Expr.v0]))
      (fun _ _ => ?_)
    rw [hhk.hFsSend, eval_bind]; dsimp only [prngFsSendC]; rw [eval_ret, pure_bind]
    exact potSPrng_caseOpt (fun hFNone => by simp [Expr.eval, Expr.v0] at hFNone)
      (fun _ _ => potSPrng_ret (by
        simp [prngVSendPost, prngVpOptPost, hSome, prngVpReady, vpSetVS, vpMk, vpId, vpTcurNat,
          letE_eval, Expr.eval, Expr.v0, Expr.v3]))

@[expose] def prngVRecvStep1Post (mo : Mode) (m m_other : ℕ)
    (s0 : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote)
    (res : (Ty.prod (.opt (.opt prngVpTy)) prngHsTy : Ty S).denote) : ℕ :=
  match res.1 with
  | none => m
  | some none => m + m_other + prngVpReady mo s0
  | some (some s1) => m + m_other + max (prngVpReady mo s0) (prngVpReady mo s1)

theorem vRecvStep1C_potOKS {B : ℕ} {mo : Mode}
    {hk : HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) prngHsTy}
    (hhk : PrngHooksSpec B mo hk) {Γ' : List (Ty S)} (hE : Expr OO Γ' prngHsTy)
    (ctxE : Expr OO Γ' (cGsTy prngVpTy)) (pE : Expr OO Γ' .bool)
    (sE : Expr OO Γ' prngVpTy) (cE : Expr OO Γ' hdrCtTy) (ρ : Env Γ') (m m_other : ℕ)
    (hNotSends : (partyDec (sE.eval ρ).1).sendsIn (cE.eval ρ).1.1 = false) :
    PotOKSPrng P_prng (prngVRecvStep1Post mo m m_other (sE.eval ρ))
      ((vRecvStep1C hk hE ctxE pE sE cE).eval ρ)
      (1 + m + m_other + prngVpReady mo (sE.eval ρ)) := by
  unfold vRecvStep1C; rw [eval_bind_ret]
  refine potSPrng_ite (fun ht => ?_)
    (fun _ => potSPrng_ret (by simp [prngVRecvStep1Post, Expr.eval, Expr.v0]))
  have ht' : (cE.eval ρ).1.1 = (sE.eval ρ).2.2.2.2.2.2 + 1 := of_decide_eq_true ht
  have hReady0 : prngVpReady mo (sE.eval ρ) = 0 := by
    rw [ht'] at hNotSends; simp [prngVpReady, prngReady, hNotSends]
  refine potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [prngVRecvStep1Post, Expr.eval]))
    (fun Tn _ => ?_)
  rw [eval_bind]
  have hSR := hhk.hStartRecv (.fst (Expr.v1 (O := OO)))
    (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))
    (.fst (.fst (.snd (.snd (.snd (.snd .v1))))))
    (vpΓ (.fst (.snd (.snd (.snd .v1))))) (vpRoot (.fst (.snd (.snd (.snd .v1))))) .v0
    (.cons Tn (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, cE.eval ρ) ρ))
    (m + m_other + prngReady mo (partyDec (sE.eval ρ).1) ((sE.eval ρ).2.2.2.2.2.2 + 1))
  simp only [Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ, ht'] at hSR
  have hBud :
      (if mo.auth && decide ((sE.eval ρ).2.2.2.2.2.2 + 1 = mo.tStar) then 1 else 0) +
        (m + m_other + prngReady mo (partyDec (sE.eval ρ).1) ((sE.eval ρ).2.2.2.2.2.2 + 1)) ≤
        1 + m + m_other + prngVpReady mo (sE.eval ρ) := by
    by_cases hEq : ((sE.eval ρ).2.2.2.2.2.2 : ℕ) + 1 = mo.tStar
    · rw [hReady0, hEq]; cases mo.auth <;> simp [prngReady, Nat.add_assoc]
    · rw [hReady0]
      simp only [hEq, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      have hLe1 := prngReady_le_one mo (partyDec (sE.eval ρ).1) ((sE.eval ρ).2.2.2.2.2.2 + 1)
      omega
  refine ⟨fun {_} k hk' => (PotOKSPrng.bindPot hSR (fun _ => ?_)).run k hk' |>.mono hBud⟩
  refine potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [prngVRecvStep1Post, Expr.eval]; omega))
    (fun _ _ => potSPrng_caseOpt
      (fun _ => potSPrng_ret (by simp [prngVRecvStep1Post, hReady0, Expr.eval]))
      (fun _ _ => potSPrng_ret (by
        rw [prngVRecvStep1Post, hReady0]
        simp [prngVpReady, vpMk, vpId, ht', Expr.eval, Expr.v0, Expr.v4])))

@[expose] def prngVRecvPost (mo : Mode) (m m_other : ℕ)
    (s0 : (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote)
    (res : (Ty.prod (.opt (.opt (.prod prngVpTy (.prod .nat (.prod .nat (.base .msg))))))
      prngHsTy : Ty S).denote) : ℕ :=
  match res.1 with
  | none => m
  | some none => m + m_other + prngVpReady mo s0
  | some (some (st', _, _, _)) => m + m_other + max (prngVpReady mo s0) (prngVpReady mo st')

theorem vRecvC_potOKS {B : ℕ} {mo : Mode}
    {hk : HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) prngHsTy}
    (hhk : PrngHooksSpec B mo hk) {Γ' : List (Ty S)} (hE : Expr OO Γ' prngHsTy)
    (ctxE : Expr OO Γ' (cGsTy prngVpTy)) (pE : Expr OO Γ' .bool)
    (sE : Expr OO Γ' prngVpTy) (cE : Expr OO Γ' hdrCtTy)
    (recE : Expr OO Γ' (.opt cRecTy)) (ρ : Env Γ') (m m_other : ℕ) :
    PotOKSPrng P_prng (prngVRecvPost mo m m_other (sE.eval ρ))
      ((vRecvC hk hE ctxE pE sE cE recE).eval ρ)
      (1 + m + m_other + prngVpReady mo (sE.eval ρ)) := by
  unfold vRecvC; rw [eval_bind_ret]
  refine potSPrng_ite (fun _ => potSPrng_ret (by simp [prngVRecvPost, Expr.eval])) (fun hGuard => ?_)
  have hNotSends : (partyDec (sE.eval ρ).1).sendsIn (cE.eval ρ).1.1 = false := by
    simp only [orE_eval, Bool.or_eq_false_iff] at hGuard
    have h1 := hGuard.1
    rw [sendsInE_eval _ _ _ (partyDec (sE.eval ρ).1) (by simp [vpId, Expr.eval, Expr.v0])] at h1
    simpa [Expr.eval, Expr.v0] using h1
  rw [eval_bind]
  have hStep1 := vRecvStep1C_potOKS hhk (.fst (Expr.v0 (O := OO)))
    (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
    (.fst (.snd (.snd (.snd (.snd .v0)))))
    (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, cE.eval ρ, recE.eval ρ) ρ)
    m m_other (by simpa [Expr.eval, Expr.v0, Env.get_cons_zero] using hNotSends)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hStep1
  refine PotOKSPrng.bindPot hStep1 (fun _ => ?_)
  refine potSPrng_caseOpt (fun hNone => ?_) (fun _ hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potSPrng_ret (by simp [prngVRecvPost, prngVRecvStep1Post, hNone, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potSPrng_caseOpt (fun hInNone => ?_) (fun _ hInSome => ?_)
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInNone
      exact potSPrng_ret (by simp [prngVRecvPost, prngVRecvStep1Post, hSome, hInNone, Expr.eval])
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInSome
      refine potSPrng_caseOpt
        (fun _ => potSPrng_ret (by simp [prngVRecvPost, prngVRecvStep1Post, hSome, hInSome, Expr.eval]))
        (fun _ _ => ?_)
      rw [hhk.hFsRecv, eval_bind]; dsimp only [prngFsRecvC]; rw [eval_ret, pure_bind]
      exact potSPrng_caseOpt (fun hFNone => by simp [Expr.eval, Expr.v0] at hFNone)
        (fun _ _ => potSPrng_caseOpt
          (fun _ => potSPrng_ret (by
            simp [prngVRecvPost, prngVRecvStep1Post, hSome, hInSome, Expr.eval]))
          (fun _ _ => potSPrng_ret (by
            simp [prngVRecvPost, prngVRecvStep1Post, hSome, hInSome, prngVpReady,
              vpSetVR, vpMk, vpId, vpTcurNat, letE_eval, Expr.eval, Expr.v0, Expr.v4])))

@[expose] def prngCommitECPost (mo : Mode) (m : ℕ)
    (res : (Ty.prod (.opt (cGsTy prngVpTy)) prngEsTy : Ty S).denote) : ℕ :=
  match res.1 with
  | none => m + prngPot mo res.2
  | some s_acc => m + prngPot mo (s_acc, res.2.2.1, res.2.2.2)

theorem commitEC_potOKS {B : ℕ} {mo : Mode}
    {hk : HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) prngHsTy}
    (hhk : PrngHooksSpec B mo hk) (L : ℕ) {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy)
    (sE : Expr OO Γ' (cGsTy prngVpTy)) (pE : Expr OO Γ' .bool)
    (oldE newE : Expr OO Γ' prngVpTy) (posE : Expr OO Γ' posTy)
    (ρ : Env Γ') (m : ℕ) (hNoAbort : (esE.eval ρ).2.2 = false) :
    PotOKSPrng P_prng (prngCommitECPost mo m)
      ((commitEC hk L esE sE pE oldE newE posE).eval ρ)
      (m + prngOtherPot mo (sE.eval ρ).1 (pE.eval ρ) + prngVpReady mo (newE.eval ρ)) := by
  unfold commitEC; rw [eval_bind_ret, hhk.hCommit, eval_bind]; dsimp only [prngCommitC]
  rw [eval_ret, pure_bind]
  refine potSPrng_caseOpt (fun hCNone => by simp [Expr.eval, Expr.v0] at hCNone) (fun _ hCSome => ?_)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero, Option.some.injEq] at hCSome
  subst hCSome; refine potSPrng_ret ?_
  simp only [prngCommitECPost, prngPot, esMk, esAbort, cGsSetStP_st_prng, cAcceptE_st_prng,
    Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ, hNoAbort,
    Bool.false_eq_true, ↓reduceIte]
  cases (pE.eval ρ : Bool) <;> (simp only [prngOtherPot, ↓reduceIte, Bool.false_eq_true]; omega)

theorem transmitEC_potOKS {B : ℕ} {mo : Mode}
    {hk : HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) prngHsTy}
    (hhk : PrngHooksSpec B mo hk) (L Δcka qep : ℕ) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy)
    (argE : Expr OO Γ' (.prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))))
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng (fun x => m + prngPot mo x.2)
      ((transmitEC hk L (2 + Δcka) qep π esE argE).eval ρ)
      (1 + m + prngPot mo (esE.eval ρ)) := by
  unfold transmitEC; rw [eval_bind_ret]
  refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun hNotAbWin => ?_)
  have hab : (esE.eval ρ).2.2 = false := by
    simp [orE_eval, esAbort, Expr.eval, Expr.v0] at hNotAbWin; exact hNotAbWin.1
  refine potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun s1 hs1 => ?_)
  refine potSPrng_ite
    (fun _ => potSPrng_ret (by simp [prngPot, esSetAbort, letE_eval, esMk, Expr.eval, Expr.v0, Expr.v1]; omega))
    (fun _ => ?_)
  rw [eval_bind]
  have hs1_st : s1.1 = (esE.eval ρ).1.1 := by
    have hs1' := cEpMgmtE_some_st_prng (2 + Δcka) qep (esG (.fst .v0))
      (.fst (.snd .v0)) (isSomeE (.snd (.snd (.snd .v0)))) (.cons (esE.eval ρ, argE.eval ρ) ρ) hs1
    simpa [esG, Expr.eval, Expr.v0, Env.get_cons_zero] using hs1'
  set p0 := (argE.eval ρ).1
  set m_other := prngOtherPot mo s1.1 p0
  have hSend := vSendC_potOKS hhk (esH (.fst (Expr.v1 (O := OO)))) .v0 (.fst (.snd .v1))
    (pGet (cGsSt .v0) (.fst (.snd .v1))) (.fst (.snd (.snd .v1))) .none (.snd (.snd (.snd .v1)))
    (.cons s1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m m_other
  simp only [pGet_eval_st_prng, cGsSt, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ] at hSend
  have hSum : m_other + prngVpReady mo (if p0 then s1.1.2 else s1.1.1) = prngPot mo (esE.eval ρ) := by
    rw [prngOtherPot_add_pGet, hs1_st]; simp [prngPot, hab]
  rw [show 1 + m + prngPot mo (esE.eval ρ) =
      1 + m + m_other + prngVpReady mo (if p0 then s1.1.2 else s1.1.1) by omega]
  refine PotOKSPrng.bindPot hSend (fun _ => ?_)
  refine potSPrng_caseOpt (fun hNone => ?_) (fun stCt hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potSPrng_ret (by simp [prngVSendPost, hNone, prngPot, esMk, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potSPrng_ret ?_
    simp only [prngVSendPost, hSome, prngPot, esMk, esAbort, cRecordE_st_prng,
      Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab,
      Bool.false_eq_true, ↓reduceIte]
    have hEq := prngPot_pSet_eq mo s1.1 p0 stCt.1; dsimp only at hEq
    change m + (let st' := if p0 then (s1.1.1, stCt.1) else (stCt.1, s1.1.2);
                prngVpReady mo st'.1 + prngVpReady mo st'.2) ≤
      m + m_other + prngVpReady mo stCt.1
    rw [hEq]; omega

theorem challEC_potOKS {B : ℕ} {mo : Mode}
    {hk : HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) prngHsTy}
    (hhk : PrngHooksSpec B mo hk) (L Δcka qep : ℕ) (cfg : ConfigEC OO) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy)
    (argE : Expr OO Γ'
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))))
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng (fun x => m + prngPot mo x.2)
      ((challEC hk L (2 + Δcka) qep cfg π esE argE).eval ρ)
      (1 + m + prngPot mo (esE.eval ρ)) := by
  unfold challEC; rw [eval_bind_ret]
  refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun hNotAbWin => ?_)
  have hab : (esE.eval ρ).2.2 = false := by
    simp [orE_eval, esAbort, Expr.eval, Expr.v0] at hNotAbWin; exact hNotAbWin.1
  refine potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun s1 hs1 => ?_)
  refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v1])) (fun _ => ?_)
  refine potSPrng_ite
    (fun _ => potSPrng_ret (by simp [prngPot, esSetAbort, letE_eval, esMk, Expr.eval, Expr.v0, Expr.v1]; omega))
    (fun _ => ?_)
  rw [eval_bind]
  have hs1_st : s1.1 = (esE.eval ρ).1.1 := by
    have hs1' := cEpMgmtE_some_st_prng (2 + Δcka) qep (esG (.fst .v0))
      (.fst (.snd .v0)) (isSomeE (.snd (.snd (.snd (.snd .v0))))) (.cons (esE.eval ρ, argE.eval ρ) ρ) hs1
    simpa [esG, Expr.eval, Expr.v0, Env.get_cons_zero] using hs1'
  set p0 := (argE.eval ρ).1
  set m_other := prngOtherPot mo s1.1 p0
  have hSend := vSendC_potOKS hhk (esH (.fst (Expr.v1 (O := OO)))) .v0 (.fst (.snd .v1))
    (pGet (cGsSt .v0) (.fst (.snd .v1)))
    (cfg.challMsgE (pGet (cGsEpoch .v0) (.fst (.snd .v1))) (cGsB (esG (.fst .v1)))
      (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1)))))
    (.some (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))))
    (.snd (.snd (.snd (.snd .v1)))) (.cons s1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m m_other
  simp only [pGet_eval_st_prng, cGsSt, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ] at hSend
  have hSum : m_other + prngVpReady mo (if p0 then s1.1.2 else s1.1.1) = prngPot mo (esE.eval ρ) := by
    rw [prngOtherPot_add_pGet, hs1_st]; simp [prngPot, hab]
  rw [show 1 + m + prngPot mo (esE.eval ρ) =
      1 + m + m_other + prngVpReady mo (if p0 then s1.1.2 else s1.1.1) by omega]
  refine PotOKSPrng.bindPot hSend (fun _ => ?_)
  refine potSPrng_caseOpt (fun hNone => ?_) (fun stCt hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potSPrng_ret (by simp [prngVSendPost, hNone, prngPot, esMk, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potSPrng_ret ?_
    simp only [prngVSendPost, hSome, prngPot, esMk, esAbort, cRecordE_st_prng,
      Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab,
      Bool.false_eq_true, ↓reduceIte]
    have hEq := prngPot_pSet_eq mo s1.1 p0 stCt.1; dsimp only at hEq
    change m + (let st' := if p0 then (s1.1.1, stCt.1) else (stCt.1, s1.1.2);
                prngVpReady mo st'.1 + prngVpReady mo st'.2) ≤
      m + m_other + prngVpReady mo stCt.1
    rw [hEq]; omega

theorem deliverEC_potOKS {B : ℕ} {mo : Mode}
    {hk : HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) prngHsTy}
    (hhk : PrngHooksSpec B mo hk) (L maxSkip : ℕ) (cfg : ConfigEC OO)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy) (argE : Expr OO Γ' (.prod .bool hdrCtTy))
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng (fun x => m + prngPot mo x.2)
      ((deliverEC hk L maxSkip cfg esE argE).eval ρ)
      (1 + m + prngPot mo (esE.eval ρ)) := by
  unfold deliverEC; rw [eval_bind_ret]
  refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun hNotAbWin => ?_)
  have hab : (esE.eval ρ).2.2 = false := by
    simp [orE_eval, esAbort, Expr.eval, Expr.v0] at hNotAbWin; exact hNotAbWin.1
  refine potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun r1 _ => ?_)
  rw [eval_bind]
  set m_other := prngOtherPot mo (esE.eval ρ).1.1 (argE.eval ρ).1
  have hRecv := vRecvC_potOKS hhk (esH (.fst (Expr.v1 (O := OO)))) (esG (.fst .v1))
    (.fst (.snd .v1)) (pGet (cGsSt (esG (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd .v1)) (.some .v0)
    (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m m_other
  simp only [pGet_eval_st_prng, cGsSt, esG, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ] at hRecv
  change PotOKSPrng P_prng
    (prngVRecvPost mo m m_other
      (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1)) _ _ at hRecv
  have hSum : m_other +
      prngVpReady mo (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) =
      prngPot mo (esE.eval ρ) := by
    rw [prngOtherPot_add_pGet]; simp [prngPot, hab]
  rw [show 1 + m + prngPot mo (esE.eval ρ) =
      1 + m + m_other +
        prngVpReady mo (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) by omega]
  refine PotOKSPrng.bindPot hRecv (fun recvOut => ?_)
  refine potSPrng_caseOpt (fun hNone => ?_) (fun resInner hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potSPrng_ret (by simp [prngVRecvPost, hNone, prngPot, esMk, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potSPrng_caseOpt (fun hInNone => ?_) (fun tup hInSome => ?_)
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInNone
      refine potSPrng_ret ?_
      simp only [prngVRecvPost, hSome, hInNone, esMk, esAbort, esG,
        Expr.eval, Expr.v1, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab]
      refine Nat.le_trans
        (Nat.add_le_add_left (Nat.le_of_eq
          (prngPot_mk_eq mo (g2 := (esE.eval ρ).1) (h2 := (esE.eval ρ).2.1)
            (ite_fst_eq_prng (by rw [cGsSetWin_st_prng]; rfl) rfl))) m) ?_
      simp only [prngPot, Bool.false_eq_true, ↓reduceIte]
      have hEqSum : prngVpReady mo (esE.eval ρ).1.1.1 + prngVpReady mo (esE.eval ρ).1.1.2 =
          m_other + prngVpReady mo
            (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
        simpa [prngPot, hab] using hSum.symm
      omega
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInSome
      rw [eval_bind]
      have hCom := commitEC_potOKS hhk L (esSetH (.fst (Expr.v4 (O := OO))) (.snd .v2))
        (esG (.fst .v4)) (.fst (.snd .v4)) (pGet (cGsSt (esG (.fst .v4))) (.fst (.snd .v4)))
        (.fst .v0) (cRecPos .v3)
        (.cons tup (.cons resInner (.cons recvOut (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ))))) m
        (by simp [esSetH, letE_eval, esMk, esAbort, Expr.eval, Expr.v0, Expr.v4, hab])
      simp only [esG, Expr.eval, Expr.v0, Expr.v4, Env.get_cons_zero, Env.get_cons_succ] at hCom
      have hPre :
          m + prngOtherPot mo (esE.eval ρ).1.1 (argE.eval ρ).1 + prngVpReady mo tup.1 ≤
            prngVRecvPost mo m m_other
              (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) recvOut := by
        simp [prngVRecvPost, hSome, hInSome, m_other]
      refine ⟨fun {_} k hk' => (PotOKSPrng.bindPot hCom (fun comOut => ?_)).run k hk' |>.mono hPre⟩
      refine potSPrng_caseOpt (fun hCNone => ?_) (fun s_acc hCSome => ?_)
      · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCNone
        exact potSPrng_ret (by simp [prngCommitECPost, hCNone, Expr.eval, Expr.v0])
      · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCSome
        refine potSPrng_ret ?_
        simp only [prngCommitECPost, hCSome, esSetG, letE_eval, esMk, esAbort,
          Expr.eval, Expr.v0, Expr.v1, Expr.v5, Expr.v6, Env.get_cons_zero, Env.get_cons_succ]
        exact Nat.add_le_add_left (Nat.le_of_eq
          (prngPot_mk_eq mo (g2 := s_acc) (h2 := comOut.2.2.1)
            (ite_fst_eq_prng (by rw [cGsSetWin_st_prng]; rfl) rfl))) m

theorem injectEC_potOKS {B : ℕ} {mo : Mode}
    {hk : HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) prngHsTy}
    (hhk : PrngHooksSpec B mo hk) (L Δcka qep : ℕ) (cfg : ConfigEC OO)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy) (argE : Expr OO Γ' (.prod .bool hdrCtTy))
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng (fun x => m + prngPot mo x.2)
      ((injectEC hk L (2 + Δcka) qep cfg esE argE).eval ρ)
      (1 + m + prngPot mo (esE.eval ρ)) := by
  unfold injectEC; rw [eval_bind_ret]
  refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun hNotRef => ?_)
  have hab : (esE.eval ρ).2.2 = false := by
    simp [orE_eval, esAbort, Expr.eval, Expr.v0] at hNotRef; exact hNotRef.1
  rw [eval_bind]
  set m_other := prngOtherPot mo (esE.eval ρ).1.1 (argE.eval ρ).1
  have hRecv := vRecvC_potOKS hhk (esH (.fst (Expr.v0 (O := OO)))) (esG (.fst .v0))
    (.fst (.snd .v0)) (pGet (cGsSt (esG (.fst .v0))) (.fst (.snd .v0))) (.snd (.snd .v0)) .none
    (.cons (esE.eval ρ, argE.eval ρ) ρ) m m_other
  simp only [pGet_eval_st_prng, cGsSt, esG, Expr.eval, Expr.v0, Env.get_cons_zero] at hRecv
  change PotOKSPrng P_prng
    (prngVRecvPost mo m m_other
      (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1)) _ _ at hRecv
  have hSum : m_other +
      prngVpReady mo (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) =
      prngPot mo (esE.eval ρ) := by
    rw [prngOtherPot_add_pGet]; simp [prngPot, hab]
  rw [show 1 + m + prngPot mo (esE.eval ρ) =
      1 + m + m_other +
        prngVpReady mo (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) by omega]
  refine PotOKSPrng.bindPot hRecv (fun recvOut => ?_)
  refine potSPrng_caseOpt (fun hNone => ?_) (fun resInner hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potSPrng_ret (by simp [prngVRecvPost, hNone, prngPot, esMk, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potSPrng_caseOpt (fun hInNone => ?_) (fun tup hInSome => ?_)
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInNone
      refine potSPrng_ret ?_
      simp only [prngVRecvPost, hSome, hInNone, prngPot, esSetH, letE_eval, esMk, esAbort, esG,
        Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get_cons_zero, Env.get_cons_succ, hab,
        Bool.false_eq_true, ↓reduceIte]
      have hEqSum : prngVpReady mo (esE.eval ρ).1.1.1 + prngVpReady mo (esE.eval ρ).1.1.2 =
          m_other + prngVpReady mo
            (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
        simpa [prngPot, hab] using hSum.symm
      omega
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInSome
      refine potSPrng_ite (fun _ => ?_) (fun _ => ?_)
      · refine potSPrng_ret ?_
        simp only [prngVRecvPost, hSome, hInSome, prngPot, esSetH, letE_eval, esMk, esAbort, esG,
          Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab,
          Bool.false_eq_true, ↓reduceIte]
        have hEqSum : prngVpReady mo (esE.eval ρ).1.1.1 + prngVpReady mo (esE.eval ρ).1.1.2 =
            m_other + prngVpReady mo
              (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
          simpa [prngPot, hab] using hSum.symm
        omega
      · refine potSPrng_ite (fun _ => ?_) (fun _ => ?_)
        · rw [eval_bind]
          have hCom := commitEC_potOKS hhk L (esSetH (.fst (Expr.v3 (O := OO))) (.snd .v2))
            (esG (.fst .v3)) (.fst (.snd .v3)) (pGet (cGsSt (esG (.fst .v3))) (.fst (.snd .v3)))
            (.fst .v0) (.pair (otherE (.fst (.snd .v3)))
              (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
            (.cons tup (.cons resInner (.cons recvOut (.cons (esE.eval ρ, argE.eval ρ) ρ)))) m
            (by simp [esSetH, letE_eval, esMk, esAbort, Expr.eval, Expr.v0, Expr.v3, hab])
          simp only [esG, Expr.eval, Expr.v0, Expr.v3, Env.get_cons_zero, Env.get_cons_succ] at hCom
          have hPre :
              m + prngOtherPot mo (esE.eval ρ).1.1 (argE.eval ρ).1 + prngVpReady mo tup.1 ≤
                prngVRecvPost mo m m_other
                  (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) recvOut := by
            simp [prngVRecvPost, hSome, hInSome, m_other]
          refine ⟨fun {_} k hk' => (PotOKSPrng.bindPot hCom (fun comOut => ?_)).run k hk' |>.mono hPre⟩
          refine potSPrng_caseOpt (fun hCNone => ?_) (fun _ hCSome => ?_)
          · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCNone
            exact potSPrng_ret (by simp [prngCommitECPost, hCNone, Expr.eval, Expr.v0])
          · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCSome
            exact potSPrng_ret (by
              simp [prngCommitECPost, hCSome, prngPot, esSetG, letE_eval, esMk, esH, esAbort,
                Expr.eval, Expr.v0, Expr.v1])
        · refine potSPrng_ret ?_
          simp only [prngVRecvPost, hSome, hInSome, esSetG, esSetH, letE_eval, esMk, esAbort, esG,
            Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab]
          refine Nat.le_trans
            (Nat.add_le_add_left (Nat.le_of_eq
              (prngPot_mk_eq mo (g2 := (esE.eval ρ).1) (h2 := (esE.eval ρ).2.1)
                (ite_fst_eq_prng (by rw [cGsSetWin_st_prng]; rfl) rfl))) m) ?_
          simp only [prngPot, Bool.false_eq_true, ↓reduceIte]
          have hEqSum : prngVpReady mo (esE.eval ρ).1.1.1 + prngVpReady mo (esE.eval ρ).1.1.2 =
              m_other + prngVpReady mo
                (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
            simpa [prngPot, hab] using hSum.symm
          omega

theorem corrEC_potOKS {B : ℕ} {mo : Mode}
    {hk : HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) prngHsTy}
    (hhk : PrngHooksSpec B mo hk) (L : ℕ) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy) (pE : Expr OO Γ' .bool)
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng (fun x => m + prngPot mo x.2)
      ((corrEC hk L π esE pE).eval ρ)
      (1 + m + prngPot mo (esE.eval ρ)) := by
  unfold corrEC; rw [eval_bind_ret]
  refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun _ => ?_)
  refine potSPrng_ite
    (fun _ => potSPrng_ret (by simp [prngPot, esSetAbort, letE_eval, esMk, Expr.eval, Expr.v0]; omega))
    (fun _ => ?_)
  rw [hhk.hReveal, eval_bind]
  refine PotOKSPrng.bindPot
    (potSPrng_comp_const _ _ (m + prngPot mo (esE.eval ρ)) (1 + m + prngPot mo (esE.eval ρ))
      (fun _ => Nat.le_refl _) (by simp [prngRevealC_queries])) (fun _ => ?_)
  exact potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [prngPot, esMk, Expr.eval]))
    (fun _ _ => potSPrng_ret (by
      simp [prngPot, esMk, esAbort, esG, cAfterCorrE_st_prng, Expr.eval, Expr.v2]))

theorem implEC_potOKS {B : ℕ} {mo : Mode}
    {hk : HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) prngHsTy}
    (hhk : PrngHooksSpec B mo hk) (L Δcka qep maxSkip : ℕ) (cfg : ConfigEC OO) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' prngEsTy)
    (qE : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng (fun x => m + prngPot mo x.2)
      ((implEC hk L (2 + Δcka) qep maxSkip cfg π esE qE).eval ρ)
      (1 + m + prngPot mo (esE.eval ρ)) := by
  unfold implEC; rw [eval_bind_ret]
  refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
  · refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
    · refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
      · refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
        · rw [eval_bind]; exact PotOKSPrng.bindPot
            (transmitEC_potOKS hhk L Δcka qep π (.fst (Expr.v4 (O := OO))) .v0 _ m)
            (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
        · rw [eval_bind]; exact PotOKSPrng.bindPot
            (challEC_potOKS hhk L Δcka qep cfg π (.fst (Expr.v4 (O := OO))) .v0 _ m)
            (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
      · rw [eval_bind]; exact PotOKSPrng.bindPot
          (deliverEC_potOKS hhk L maxSkip cfg (.fst (Expr.v3 (O := OO))) .v0 _ m)
          (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
    · rw [eval_bind]; exact PotOKSPrng.bindPot
        (injectEC_potOKS hhk L Δcka qep cfg (.fst (Expr.v2 (O := OO))) .v0 _ m)
        (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
  · rw [eval_bind]; exact PotOKSPrng.bindPot
      (corrEC_potOKS hhk L π (.fst (Expr.v1 (O := OO))) .v0 _ m)
      (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))

theorem initPRNGEStateC_potOKS (mo : Mode) {Γ' : List (Ty S)} (bE : Expr OO Γ' .bool)
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng (fun es => m + prngPot mo es)
      ((initPRNGEStateC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) mo bE).eval ρ) (m + 3) := by
  unfold initPRNGEStateC; rw [eval_bind_ret, eval_bind]
  refine PotOKSPrng.bindPot
    (potSPrng_comp_const _ _ (m + 3) (m + 3) (fun _ => Nat.le_refl _) (by simp [Comp.queries]))
    (fun _ => ?_)
  rw [eval_bind]
  refine PotOKSPrng.bindPot
    (potSPrng_comp_const _ _ (m + 1) (m + 3) (fun _ => Nat.le_refl _)
      (by simp [rootPRNGC_queries]; omega)) (fun _ => ?_)
  refine potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [prngPot, esMk, Expr.eval])) (fun _ _ => ?_)
  refine potSPrng_ret ?_
  simp only [prngPot, esMk, cGsInitE, cGsMk, mkPartiesE, vpMk, Expr.eval,
    Bool.false_eq_true, ↓reduceIte]
  have hB : prngReady mo Party.B 0 = 0 := by simp [prngReady, Party.sendsIn]
  simp only [prngVpReady, partyDec_partyEnc, hB, Nat.add_zero]
  exact Nat.add_le_add_left (prngReady_le_one mo _ _) m

/-- Generic `min (2 + 2 * q) (q + 3)` PRF-PRNG query bound combinator for `CostedReduction`
programs over `prngOps` and `prngIface`. -/
theorem costedReduction_makesAtMostQueries_prng
    {κ : Type} {G : OracleSpec.{0, 0} κ} {C : GameCodec S G}
    (R : CostedReduction OO II G C .unit .unit .bool .bool)
    (pot : R.σ.denote → ℕ) (q : ℕ)
    (A : OracleComp (unifSpec + G) Bool)
    (hA' : A.IsQueryBoundP (isGameQuery (G := G)) q)
    (hTot : R.totalQueries (fun _ => 1) (fun _ => 0) q = 2 + q * 2)
    (hInit : PotOKSPrng P_prng (fun as : (Ty.prod .unit R.σ : Ty S).denote => q + pot as.2)
      (R.init.eval (Env.cons (t := .unit) () .nil)) (q + 3))
    (hStep : ∀ (m : ℕ) qv sv, PotOKSPrng P_prng (fun x => m + pot x.2)
      (R.handle.eval (.cons sv (.cons qv .nil))) (1 + m + pot sv))
    (hFin : R.finish.queries (fun _ => 1) (fun _ => 0) = 0) :
    (R.eval (fun _ => A) ()).IsQueryBoundP (· matches .inr _) (min (2 + 2 * q) (q + 3)) := by
  refine isQueryBoundP_min_prng ?_ ?_
  · have hSyn := CostedReduction.queryBound_eval R P_prng (fun _ => 1) (fun _ => 0)
      (fun _ _ _ => Nat.le_refl 1) prngIface_fwdU_zero (fun _ => A) q (fun _ => hA') ()
    rw [hTot, Nat.mul_comm] at hSyn
    exact hSyn.of_imp (fun x hx => by cases x <;> [cases hx; trivial])
  · suffices hGame : (R.eval (fun _ => A) ()).IsQueryBoundP P_prng (q + 3) by
      exact hGame.of_imp (fun x hx => by cases x <;> [cases hx; trivial])
    unfold CostedReduction.eval CostedReduction.impl
    refine hInit.run _ ?_
    rintro ⟨_, s0⟩
    have hSim := potOKS_simulateQ_handlerImpl_step1_prng pot prngIface_fwdU_zero R.handle hStep hA' s0
    refine hSim.run _ ?_
    rintro ⟨bOut, sOut⟩
    have hF := Comp.queryBound_eval P_prng (fun _ => 1) (fun _ => 0)
      (fun _ _ _ => Nat.le_refl 1) prngIface_fwdU_zero R.finish (.cons sOut (.cons bOut .nil))
    exact hF.mono (by simp [hFin])

@[local simp] private theorem implEC_hooksPRNGMainC_queries (L B Δcka qep maxSkip : ℕ)
    (mo : Mode) {Γ' : List (Ty S)} (es : Expr OO Γ' prngEsTy)
    (q : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implEC (hooksPRNGMainC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B mo)
      L (2 + Δcka) qep maxSkip (modeCfgEC OO mo) mo.policy es q).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  simp [implEC, transmitEC, challEC, deliverEC, injectEC, corrEC,
    vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC, hooksPRNGMainC, Comp.queries]

/-- PRF-PRNG query bound `min (2 + 2 * q) (q + 3)` for `redPRNGAuthProg`. -/
theorem redPRNGAuthProg_makesAtMostQueries (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (t q : ℕ)
    (A : _root_.CryptoGames.SM.Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
    (hA : MakesAtMostQueries A q) :
    (((redPRNGAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep maxSkip tL t).eval (fun _ => A) ())).IsQueryBoundP
      (· matches .inr _) (min (2 + 2 * q) (q + 3)) := by
  refine costedReduction_makesAtMostQueries_prng _ (prngPot ⟨true, tL, t⟩) q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (redPRNGAuthProg_totalQueries L B Δcka qep maxSkip tL t q) ?_ ?_
    (by simp [redPRNGAuthProg, Comp.queries])
  · dsimp only [redPRNGAuthProg]; rw [eval_bind]
    exact PotOKSPrng.bindPot (initPRNGEStateC_potOKS ⟨true, tL, t⟩ (.bool false) _ q)
      (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
  · intro m qv sv
    exact implEC_potOKS (hooksPRNGC_spec B ⟨true, tL, t⟩) L Δcka qep maxSkip
      (modeCfgEC OO ⟨true, tL, t⟩) (⟨true, tL, t⟩ : Mode).policy .v0 .v1 (.cons sv (.cons qv .nil)) m

/-- PRF-PRNG query bound `min (2 + 2 * q) (q + 3)` for `redPRNGAuthStage2Prog`. -/
theorem redPRNGAuthStage2Prog_makesAtMostQueries (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (t q : ℕ)
    (A : _root_.CryptoGames.SM.Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
    (hA : MakesAtMostQueries A q) :
    (((redPRNGAuthStage2Prog (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep maxSkip tL t).eval (fun _ => A) ())).IsQueryBoundP
      (· matches .inr _) (min (2 + 2 * q) (q + 3)) := by
  refine costedReduction_makesAtMostQueries_prng _
    (fun (st : (@prngStage2EsTy KC Γ CCoins T I KR RSt K SS RS M E).denote) =>
      prngPot ⟨true, tL, t⟩ st.1) q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (by simp [CostedReduction.totalQueries, redPRNGAuthStage2Prog, Comp.queries]) ?_ ?_
    (by simp [redPRNGAuthStage2Prog, Comp.queries])
  · dsimp only [redPRNGAuthStage2Prog]; rw [eval_bind]
    refine PotOKSPrng.bindPot
      (potSPrng_comp_const _ _ (q + 3) (q + 3) (fun _ => Nat.le_refl _) (by simp [Comp.queries]))
      (fun forgedMode => ?_)
    rw [eval_bind]
    exact PotOKSPrng.bindPot
      (initPRNGEStateC_potOKS ⟨true, tL, t⟩ (.bool false)
        (Env.cons (t := .bool) forgedMode (Env.cons (t := .unit) () .nil)) q)
      (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0, Expr.v1]))
  · intro m qv sv
    dsimp only [redPRNGAuthStage2Prog]; rw [eval_bind_ret]
    refine potSPrng_ite (fun _ => ?_) (fun _ => ?_)
    · rw [eval_bind]
      have hImpl := implEC_potOKS
        (hooksPRNGC_spec (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) B ⟨true, tL, t⟩) L Δcka qep maxSkip
        (modeCfgEC OO ⟨true, tL, t⟩) (⟨true, tL, t⟩ : Mode).policy
        (.fst (Expr.v0 (O := OO))) (.snd (.snd .v0))
        (.cons (sv.1, sv.2, qv) (.cons sv (.cons qv .nil))) m
      simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hImpl
      refine PotOKSPrng.bindPot hImpl (fun outEs => potSPrng_ret ?_)
      simp only [esSetG, letE_eval, esMk, esAbort, esG,
        Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
      split_ifs
      · exact Nat.add_le_add_left (Nat.le_of_eq
          (prngPot_mk_eq ⟨true, tL, t⟩ (g2 := outEs.2.1) (h2 := outEs.2.2.1)
            (by rw [cGsSetWin_st_prng]; rfl))) m
      · exact Nat.le_refl _
    · rw [eval_bind]
      have hImpl := implEC_potOKS
        (hooksPRNGMainC_spec (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) B ⟨true, tL, t⟩) L Δcka qep maxSkip
        (modeCfgEC OO ⟨true, tL, t⟩) (⟨true, tL, t⟩ : Mode).policy
        (.fst (Expr.v0 (O := OO))) (.snd (.snd .v0))
        (.cons (sv.1, sv.2, qv) (.cons sv (.cons qv .nil))) m
      simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hImpl
      exact PotOKSPrng.bindPot hImpl (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))

theorem redPRNGPrivProg_makesAtMostQueries_q3 (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (t q : ℕ)
    (A : _root_.CryptoGames.SM.Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
    (hA : MakesAtMostQueries A q) :
    (((redPRNGPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep maxSkip tL t).eval (fun _ => A) ())).IsQueryBoundP
      (· matches .inr _) (min (2 + 2 * q) (q + 3)) := by
  refine costedReduction_makesAtMostQueries_prng _ (prngPot ⟨false, tL, t⟩) q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (redPRNGPrivProg_totalQueries L B Δcka qep maxSkip tL t q) ?_ ?_
    (by simp [redPRNGPrivProg, privOutC, Comp.queries])
  · dsimp only [redPRNGPrivProg]; rw [eval_bind]
    refine PotOKSPrng.bindPot
      (potSPrng_comp_const _ _ (q + 3) (q + 3) (fun _ => Nat.le_refl _) (by simp [Comp.queries]))
      (fun b0 => ?_)
    rw [eval_bind]
    exact PotOKSPrng.bindPot
      (initPRNGEStateC_potOKS ⟨false, tL, t⟩ .v0
        (Env.cons (t := .bool) b0 (Env.cons (t := .unit) () .nil)) q)
      (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
  · intro m qv sv
    exact implEC_potOKS (hooksPRNGC_spec B ⟨false, tL, t⟩) L Δcka qep maxSkip
      (modeCfgEC OO ⟨false, tL, t⟩) (⟨false, tL, t⟩ : Mode).policy .v0 .v1 (.cons sv (.cons qv .nil)) m

end PrngPotOK

end

end Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK
