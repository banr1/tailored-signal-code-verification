/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.RedCKA -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Potential
import Computational.Proofs.ReductionDsl.Notation

/-!
# Potential-based CKA query bounds

Proves `min (2 * q) (q + 2)` CKA query bounds for the four CKA reductions in `RedCKA` using a
two-credit party-externalization potential on encoded engine states.
-/

namespace Computational.Proofs.ReductionDsl.SM.RedCKAPotOK

public section

set_option autoImplicit false

open OracleSpec OracleComp
open _root_.ReductionDsl
  (Sig Ty Ops Iface Env Expr Comp GameCodec CostedReduction handlerImpl isGameQuery)
open _root_.Computational.Proofs.GameHop.ReductionDsl.SupportWP
  (PotOK potC_ret potC_ite potC_caseOpt potC_caseSum potC_bind)
open _root_.CryptoGames.CKA
  (CKASamp CKATag CKAOp ckaSig ckaOps ckaIface ckaSMCodec ckaSMQ ckaHdrTy ckaHdrCtTy)
open _root_.CryptoGames.SM
  (MakesAtMostQueries posTy sendsInE otherE validGuessE pGet pSet orE isSomeE
   letE_eval pair_eval ite_eval some_eval orE_eval)
open _root_.CryptoGames.SM.Engine
  (HooksC ConfigEC Policy modeCfgEC cRecTy cGsTy esTy
   esG esH esAbort esMk esSetG esSetH esSetAbort
   cGsSt cGsEpoch cGsIdx cGsWin cGsB cGsMk cGsSetStP cGsSetWin cRecPos
   cLeakE cEpMgmtE cDeleteE cAcceptE cRecordE cCorrAllowedE cAfterCorrE cAuthOKE
   vpMk vpId vpTcur vpTcurNat vpΓ vpRoot vpVS vpVR vpSetΓ vpSetVS
   vSendStep1C vSendC vRecvStep1C vRecvC commitEC
   transmitEC challEC deliverEC injectEC corrEC implEC privOutC
   eval_bind eval_bind_ret)
open _root_.CryptoGames.SM.Construction
  (Header PartyState Mode
   ckaVpTy ckaHsTy ckaEsTy
   ckaStartSendC ckaStartRecvC ckaFsSendC ckaFsRecvC ckaCommitC ckaRevealC
   hooksCKAC initCKAEStateC initCKAEStateC_queries
   redCKAAuthProg redCKAAuthProg_totalQueries
   hooksCKABucketC bucketAuthCfgEC ckaBucketEsTy redCKAAuthBucketProg
   redCKAPrivProg redCKAPrivProg_totalQueries
   ckaUHsTy ckaUEsTy ckaStartSendUC hooksCKAUC redCKAPrivUProg)

section CkaPotOK

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

local notation "S" => ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E

local notation "OO" =>
  ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

local notation "II" =>
  ckaIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

local notation "P_cka" => isGameQuery (G := CryptoGames.CKA.spec Γ CCoins T I)

private def ckaVpPot (vp : (@ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote) : ℕ :=
  if vp.2.2.2.2.1.isNone then 1 else 0

private def ckaPotGen {hsTy : Ty S}
    (es : (esTy (@ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E) hsTy).denote) : ℕ :=
  if es.2.2 then 0 else ckaVpPot es.1.1.1 + ckaVpPot es.1.1.2

private theorem ckaVpPot_le_one (vp : (@ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote) :
    ckaVpPot vp ≤ 1 := by
  unfold ckaVpPot; split <;> omega

private theorem ckaPotGen_le_two {hsTy : Ty S}
    (es : (esTy (@ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E) hsTy).denote) :
    ckaPotGen es ≤ 2 := by
  unfold ckaPotGen
  have hA := ckaVpPot_le_one es.1.1.1
  have hB := ckaVpPot_le_one es.1.1.2
  split <;> omega

private def ckaOtherPot
    (stAB : (@ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote ×
      (@ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote)
    (p : Bool) : ℕ :=
  if p then ckaVpPot stAB.1 else ckaVpPot stAB.2

private theorem pGet_eval_st {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (st : Expr O' Γ' (.prod vpT vpT)) (p : Expr O' Γ' .bool) (ρ : Env Γ') :
    (pGet st p).eval ρ = if p.eval ρ then (st.eval ρ).2 else (st.eval ρ).1 := by
  cases hp : (p.eval ρ : Bool) <;> simp [pGet, Expr.eval, Expr.v0, hp]

private theorem pSet_eval_st {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (st : Expr O' Γ' (.prod vpT vpT)) (p : Expr O' Γ' .bool) (v : Expr O' Γ' vpT) (ρ : Env Γ') :
    (pSet st p v).eval ρ =
      if p.eval ρ then ((st.eval ρ).1, v.eval ρ) else (v.eval ρ, (st.eval ρ).2) := by
  cases hp : (p.eval ρ : Bool) <;> simp [pSet, Expr.eval, Expr.v0, hp]

private theorem ckaOtherPot_add_pGet
    (stAB : (@ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote ×
      (@ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote)
    (p : Bool) :
    ckaOtherPot stAB p + ckaVpPot (if p then stAB.2 else stAB.1) =
      ckaVpPot stAB.1 + ckaVpPot stAB.2 := by
  cases p <;> simp [ckaOtherPot, Nat.add_comm]

private theorem cLeakE_st {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (s : Expr O' Γ' (cGsTy vpT)) (l : Expr O' Γ' .nat) (ρ : Env Γ') :
    ((cLeakE s l).eval ρ).1 = (s.eval ρ).1 := by
  simp [cLeakE, cGsMk, cGsSt, Expr.eval, Expr.v0]

private theorem cEpMgmtE_some_st {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
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
    exact cLeakE_st _ _ _
  · simp only [some_eval, Option.some.injEq] at h
    subst h; rfl
  · cases h
  · simp only [some_eval, Option.some.injEq] at h
    subst h; rfl

private theorem cDeleteE_st {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (L : ℕ) (s : Expr O' Γ' (cGsTy vpT)) (pos : Expr O' Γ' posTy) (ρ : Env Γ') :
    ((cDeleteE L s pos).eval ρ).1 = (s.eval ρ).1 := by
  simp [cDeleteE, cGsMk, cGsSt, Expr.eval, Expr.v0]

private theorem cAcceptE_st {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (L : ℕ) (s : Expr O' Γ' (cGsTy vpT)) (p : Expr O' Γ' .bool)
    (st' : Expr O' Γ' vpT) (pos : Expr O' Γ' posTy) (ρ : Env Γ') :
    ((cAcceptE L s p st' pos).eval ρ).1 =
      if p.eval ρ then ((s.eval ρ).1.1, st'.eval ρ) else (st'.eval ρ, (s.eval ρ).1.2) := by
  cases hp : (p.eval ρ : Bool) <;>
    simp [cAcceptE, cGsMk, cGsSt, pSet_eval_st, cDeleteE_st, Expr.eval, Expr.v0, hp]

private theorem cGsSetStP_st {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (s : Expr O' Γ' (cGsTy vpT)) (p : Expr O' Γ' .bool) (st' : Expr O' Γ' vpT) (ρ : Env Γ') :
    ((cGsSetStP s p st').eval ρ).1 =
      if p.eval ρ then ((s.eval ρ).1.1, st'.eval ρ) else (st'.eval ρ, (s.eval ρ).1.2) := by
  cases hp : (p.eval ρ : Bool) <;> simp [cGsSetStP, cGsMk, cGsSt, pSet_eval_st, Expr.eval, Expr.v0, hp]

private theorem cGsSetWin_st {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (s : Expr O' Γ' (cGsTy vpT)) (w : Expr O' Γ' .bool) (ρ : Env Γ') :
    ((cGsSetWin s w).eval ρ).1 = (s.eval ρ).1 := by
  simp [cGsSetWin, cGsMk, cGsSt, Expr.eval, Expr.v0]

private theorem cRecordE_st {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (L Δ : ℕ) (s : Expr O' Γ' (cGsTy vpT)) (p : Expr O' Γ' .bool)
    (st' : Expr O' Γ' vpT) (r : Expr O' Γ' cRecTy) (ch : Expr O' Γ' .bool) (ρ : Env Γ') :
    ((cRecordE L Δ s p st' r ch).eval ρ).1 =
      if p.eval ρ then ((s.eval ρ).1.1, st'.eval ρ) else (st'.eval ρ, (s.eval ρ).1.2) := by
  cases hp : (p.eval ρ : Bool) <;> simp [cRecordE, cGsMk, cGsSt, pSet_eval_st, Expr.eval, Expr.v0, hp]

private theorem cAfterCorrE_st {O' : Ops S} {vpT : Ty S} {Γ' : List (Ty S)}
    (L : ℕ) (s : Expr O' Γ' (cGsTy vpT)) (p : Expr O' Γ' .bool) (ρ : Env Γ') :
    ((cAfterCorrE L s p).eval ρ).1 = (s.eval ρ).1 := by
  simp [cAfterCorrE, cLeakE_st, cGsMk, cGsSt, Expr.eval, Expr.v0]

private theorem isQueryBoundP_min_cka {ι' : Type} {spec : OracleSpec.{0, 0} ι'} {α : Type}
    {P : ι' → Prop} [DecidablePred P] {oa : OracleComp spec α} {m n : ℕ}
    (hm : oa.IsQueryBoundP P m) (hn : oa.IsQueryBoundP P n) :
    oa.IsQueryBoundP P (min m n) := by
  rcases Nat.le_total m n with h | h
  · rw [Nat.min_eq_left h]; exact hm
  · rw [Nat.min_eq_right h]; exact hn

private theorem ckaIface_fwdU_zero (n : ℕ) :
    ((II).fwdU n).IsQueryBoundP P_cka 0 := by
  change OracleComp.IsQueryBoundP
    (liftM (OracleSpec.query (spec := unifSpec + CryptoGames.CKA.spec Γ CCoins T I) (.inl n))) P_cka 0
  rw [← bind_pure (liftM _), isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (by simp [isGameQuery]), fun _ => by simp⟩

private structure PotOKS {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {α : Type}
    (P : ι' → Prop) [DecidablePred P] (B : α → ℕ) (oa : OracleComp T' α) (n : ℕ) : Prop where
  run : PotOK P B oa n

private theorem PotOKS.bindPot {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {α γ : Type}
    {P : ι' → Prop} [DecidablePred P] {B₁ : α → ℕ} {B₂ : γ → ℕ}
    {oa : OracleComp T' α} {f : α → OracleComp T' γ} {n : ℕ}
    (hoa : PotOKS P B₁ oa n) (hf : ∀ a, PotOKS P B₂ (f a) (B₁ a)) :
    PotOKS P B₂ (oa >>= f) n :=
  ⟨PotOK.bindPot hoa.run (fun a => (hf a).run)⟩

private theorem PotOKS.bind' {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {α γ : Type}
    {P : ι' → Prop} [DecidablePred P] {B : γ → ℕ}
    {oa : OracleComp T' α} {f : α → OracleComp T' γ} {m n r : ℕ}
    (hoa : oa.IsQueryBoundP P m) (hf : ∀ a, PotOKS P B (f a) r) (hmn : m + r ≤ n) :
    PotOKS P B (oa >>= f) n :=
  ⟨PotOK.bind' hoa (fun a => (hf a).run) hmn⟩

private theorem potS_ret {S' : Sig} {ι' : Type} {T' : OracleSpec.{0, 0} ι'}
    {O' : Ops S'} {I' : Iface S' T'} {P : ι' → Prop} [DecidablePred P]
    {Γ' : List (Ty S')} {τ : Ty S'} {B : τ.denote → ℕ}
    {e : Expr O' Γ' τ} {env : Env Γ'} {n : ℕ} (h : B (e.eval env) ≤ n) :
    PotOKS P B ((Comp.ret (I := I') e).eval env) n :=
  ⟨potC_ret e env h⟩

private theorem potS_ite {S' : Sig} {ι' : Type} {T' : OracleSpec.{0, 0} ι'}
    {O' : Ops S'} {I' : Iface S' T'} {P : ι' → Prop} [DecidablePred P]
    {Γ' : List (Ty S')} {τ : Ty S'} {B : τ.denote → ℕ}
    {c : Expr O' Γ' .bool} {t e : Comp O' I' Γ' τ} {env : Env Γ'} {n : ℕ}
    (ht : c.eval env = true → PotOKS P B (t.eval env) n)
    (he : c.eval env = false → PotOKS P B (e.eval env) n) :
    PotOKS P B ((Comp.ite c t e).eval env) n :=
  ⟨potC_ite c t e env (fun h => (ht h).run) (fun h => (he h).run)⟩

private theorem potS_caseOpt {S' : Sig} {ι' : Type} {T' : OracleSpec.{0, 0} ι'}
    {O' : Ops S'} {I' : Iface S' T'} {P : ι' → Prop} [DecidablePred P]
    {Γ' : List (Ty S')} {τ₁ τ : Ty S'} {B : τ.denote → ℕ}
    {o : Expr O' Γ' (.opt τ₁)} {kn : Comp O' I' Γ' τ} {ks : Comp O' I' (τ₁ :: Γ') τ}
    {env : Env Γ'} {n : ℕ}
    (hn : o.eval env = none → PotOKS P B (kn.eval env) n)
    (hs : ∀ x, o.eval env = some x → PotOKS P B (ks.eval (.cons x env)) n) :
    PotOKS P B ((Comp.caseOpt o kn ks).eval env) n :=
  ⟨potC_caseOpt o kn ks env (fun h => (hn h).run) (fun a h => (hs a h).run)⟩

private theorem potS_caseSum {S' : Sig} {ι' : Type} {T' : OracleSpec.{0, 0} ι'}
    {O' : Ops S'} {I' : Iface S' T'} {P : ι' → Prop} [DecidablePred P]
    {Γ' : List (Ty S')} {τ₁ τ₂ τ : Ty S'} {B : τ.denote → ℕ}
    {s : Expr O' Γ' (.sum τ₁ τ₂)} {kl : Comp O' I' (τ₁ :: Γ') τ} {kr : Comp O' I' (τ₂ :: Γ') τ}
    {env : Env Γ'} {n : ℕ}
    (hl : ∀ a, s.eval env = .inl a → PotOKS P B (kl.eval (.cons a env)) n)
    (hr : ∀ b, s.eval env = .inr b → PotOKS P B (kr.eval (.cons b env)) n) :
    PotOKS P B ((Comp.caseSum s kl kr).eval env) n :=
  ⟨potC_caseSum s kl kr env (fun a h => (hl a h).run) (fun b h => (hr b h).run)⟩

private theorem potS_bind {Γ' : List (Ty S)} {τ₁ τ₂ : Ty S} {B : τ₂.denote → ℕ}
    {m : Comp OO II Γ' τ₁} {k : Comp OO II (τ₁ :: Γ') τ₂} {env : Env Γ'} (r : ℕ) {n : ℕ}
    (hmn : m.queries (fun _ => 1) (fun _ => 0) + r ≤ n)
    (hk : ∀ x, PotOKS P_cka B (k.eval (.cons x env)) r) :
    PotOKS P_cka B ((Comp.bind m k).eval env) n :=
  ⟨potC_bind (fun _ => 1) (fun _ => 0)
    (fun _ _ _ => Nat.le_refl 1) ckaIface_fwdU_zero m k env (fun x => (hk x).run) hmn⟩

private theorem ite_fst_eq {α β : Type} {P_cond : Prop} [Decidable P_cond]
    {g1 g2 : α × β} {x : α} (h1 : g1.1 = x) (h2 : g2.1 = x) :
    (if P_cond then g1 else g2).1 = x := by
  by_cases hc : P_cond <;> simp [hc, h1, h2]

private theorem ckaPotGen_mk_eq {hsTy : Ty S}
    {g1 g2 : (cGsTy (@ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E)).denote}
    {h1 h2 : hsTy.denote} {ab : Bool}
    (hst : g1.1 = g2.1) :
    ckaPotGen (hsTy := hsTy) (g1, h1, ab) = ckaPotGen (hsTy := hsTy) (g2, h2, ab) := by
  simp [ckaPotGen, hst]

private theorem potS_comp_const {Γ' : List (Ty S)} {a : Ty S}
    (c : Comp OO II Γ' a) (ρ : Env Γ') {B : a.denote → ℕ} (r n : ℕ)
    (hB : ∀ x, B x ≤ r)
    (hle : c.queries (fun _ => 1) (fun _ => 0) + r ≤ n) :
    PotOKS P_cka B (c.eval ρ) n :=
  ⟨fun {_} _ hk => (isQueryBoundP_bind
    (Comp.queryBound_eval P_cka (fun _ => 1) (fun _ => 0)
      (fun _ _ _ => Nat.le_refl 1) ckaIface_fwdU_zero c ρ)
    (fun x _ => (hk x).mono (hB x))).mono hle⟩

private theorem potOKS_simulateQ_handlerImpl_step1_cka
    {S' : Sig} {O' : Ops S'} {ι' : Type} {T' : OracleSpec.{0, 0} ι'} {I' : Iface S' T'}
    {κ : Type} {G : OracleSpec.{0, 0} κ}
    {C : GameCodec S' G} {σ : Ty S'} {α : Type}
    {P : ι' → Prop} [DecidablePred P]
    (B : σ.denote → ℕ)
    (hU : ∀ n, (I'.fwdU n).IsQueryBoundP P 0)
    (h : Comp O' I' [σ, C.Q] (.prod C.R σ))
    (hStep : ∀ (m : ℕ) q s, PotOKS P (fun x : C.R.denote × σ.denote => m + B x.2)
      (h.eval (.cons s (.cons q .nil))) (1 + m + B s))
    {mx : OracleComp (unifSpec + G) α} {qAdv : ℕ}
    (hq : mx.IsQueryBoundP (isGameQuery (G := G)) qAdv) (st : σ.denote) :
    PotOKS P (fun _ : α × σ.denote => 0)
      ((simulateQ (handlerImpl (C := C) h) mx).run st) (qAdv + B st) := by
  induction mx using OracleComp.inductionOn generalizing qAdv st with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact ⟨fun {β} k hk => by simpa using (hk (a, st)).mono (Nat.zero_le (qAdv + B st))⟩
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [simulateQ_query_bind, StateT.run_bind]
    rcases q with uq | gq
    · change PotOKS P _
        ((do let u ← I'.fwdU uq; return (u, st)) >>=
          fun x => (simulateQ (handlerImpl (C := C) h) (k x.1)).run x.2)
        (qAdv + B st)
      rw [bind_assoc]
      refine PotOKS.bind' (m := 0) (r := qAdv + B st) (hU uq) (fun u => ?_) (by omega)
      rw [pure_bind]
      exact ih u (by simpa [isGameQuery] using hq.2 u) st
    · have hpos : 0 < qAdv := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      change PotOKS P _
        ((do
            let p ← h.eval (.cons st (.cons (C.qenc gq) .nil))
            return (C.rdec gq p.1, p.2)) >>=
          fun x => (simulateQ (handlerImpl (C := C) h) (k x.1)).run x.2)
        ((m + 1) + B st)
      rw [show (m + 1) + B st = 1 + m + B st by omega, bind_assoc]
      refine PotOKS.bindPot (hStep m (C.qenc gq) st) (fun p => ?_)
      rw [pure_bind]
      exact ih (C.rdec gq p.1) (by simpa [isGameQuery] using hq.2 (C.rdec gq p.1)) p.2

private def ckaStartSendPostGen {hsTy : Ty S} (m m_other : ℕ)
    (res : (Ty.prod (.opt (.prod (.opt (.base .γ)) (.prod (.base .t) (.prod (.base .sig) (.base .ss)))))
      hsTy : Ty S).denote) : ℕ :=
  match res.1 with | none => m | some (γ', _, _, _) => m + m_other + (if γ'.isNone then 1 else 0)

private def ckaVpOptPostGen {hsTy : Ty S} (m m_other : ℕ)
    (res : (Ty.prod (.opt ckaVpTy) hsTy : Ty S).denote) : ℕ :=
  match res.1 with | none => m | some vp' => m + m_other + ckaVpPot vp'

private def ckaVSendPostGen {hsTy : Ty S} (m m_other : ℕ)
    (res : (Ty.prod (.opt (.prod ckaVpTy hdrCtTy)) hsTy : Ty S).denote) : ℕ :=
  match res.1 with | none => m | some (vp', _) => m + m_other + ckaVpPot vp'

private def ckaCommitECPostGen {hsTy : Ty S} (m : ℕ)
    (res : (Ty.prod (.opt (cGsTy ckaVpTy)) (esTy ckaVpTy hsTy) : Ty S).denote) : ℕ :=
  match res.1 with
  | none => m + ckaPotGen res.2
  | some s_acc => m + (if res.2.2.2 then 0 else ckaVpPot s_acc.1.1 + ckaVpPot s_acc.1.2)

private structure CkaHooksPotOK {hsTy : Ty S}
    (hk : HooksC OO II (.opt (.base .γ)) (.base .sig) (.base .ss) (.base .rs) hsTy) : Prop where
  startSend_pot : ∀ {Γ' : List (Ty S)} (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat) (γvE : Expr OO Γ' (.opt (.base .γ)))
    (σE : Expr OO Γ' (.base .sig)) (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ') (m m_other : ℕ),
    PotOKS P_cka (ckaStartSendPostGen m m_other) ((hk.startSend hE ctxE pE tE γvE σE rE).eval ρ)
      (1 + m + m_other + (if (γvE.eval ρ).isNone then 1 else 0))
  startRecv_queries : ∀ {Γ' : List (Ty S)} (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat) (γvE : Expr OO Γ' (.opt (.base .γ)))
    (σE : Expr OO Γ' (.base .sig)) (tnE : Expr OO Γ' (.base .t)),
    (hk.startRecv hE ctxE pE tE γvE σE tnE).queries (fun _ => 1) (fun _ => 0) = 0
  fsSend_pot : ∀ {Γ' : List (Ty S)} (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat) (ssE : Expr OO Γ' (.base .ss))
    (hdrE : Expr OO Γ' hdrTy) (mE : Expr OO Γ' (.base .msg))
    (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))) (ρ : Env Γ') (m : ℕ)
    (B_post : (Ty.prod (.opt (.prod (.base .ss) (.base .ct))) hsTy : Ty S).denote → ℕ),
    (∀ v' ct h', B_post (some (v', ct), h') ≤ m) →
    PotOKS P_cka B_post ((hk.fsSend hE ctxE pE tE ssE hdrE mE pairE).eval ρ) m
  fsRecv_queries : ∀ {Γ' : List (Ty S)} (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat) (rsE : Expr OO Γ' (.base .rs))
    (hdrE : Expr OO Γ' hdrTy) (eE : Expr OO Γ' (.base .ct)) (recE : Expr OO Γ' (.opt cRecTy)),
    (hk.fsRecv hE ctxE pE tE rsE hdrE eE recE).queries (fun _ => 1) (fun _ => 0) = 0
  commit_pot : ∀ {Γ' : List (Ty S)} (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (oldE newE : Expr OO Γ' ckaVpTy) (ρ : Env Γ') (m m_other : ℕ),
    PotOKS P_cka (ckaVpOptPostGen m m_other) ((hk.commit hE ctxE pE oldE newE).eval ρ)
      (1 + m + m_other + ckaVpPot (oldE.eval ρ))
  reveal_queries : ∀ {Γ' : List (Ty S)} (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' ckaVpTy),
    (hk.reveal hE ctxE pE vpE).queries (fun _ => 1) (fun _ => 0) ≤ 1

private theorem vRecvC_queries_zero {hsTy : Ty S}
    {hk : HooksC OO II (.opt (.base .γ)) (.base .sig) (.base .ss) (.base .rs) hsTy}
    (hhk : CkaHooksPotOK hk) {Γ' : List (Ty S)} (hE : Expr OO Γ' hsTy)
    (ctxE : Expr OO Γ' (cGsTy ckaVpTy)) (pE : Expr OO Γ' .bool) (sE : Expr OO Γ' ckaVpTy)
    (cE : Expr OO Γ' hdrCtTy) (recE : Expr OO Γ' (.opt cRecTy)) :
    (vRecvC hk hE ctxE pE sE cE recE).queries (fun _ => 1) (fun _ => 0) = 0 := by
  simp [vRecvC, vRecvStep1C, hhk.startRecv_queries, hhk.fsRecv_queries, Comp.queries]

private theorem vSendStep1C_potOKS_gen {hsTy : Ty S}
    {hk : HooksC OO II (.opt (.base .γ)) (.base .sig) (.base .ss) (.base .rs) hsTy}
    (hhk : CkaHooksPotOK hk) {Γ' : List (Ty S)} (hE : Expr OO Γ' hsTy)
    (ctxE : Expr OO Γ' (cGsTy ckaVpTy)) (pE : Expr OO Γ' .bool) (sE : Expr OO Γ' ckaVpTy)
    (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ') (m m_other : ℕ) :
    PotOKS P_cka (ckaVpOptPostGen m m_other) ((vSendStep1C hk hE ctxE pE sE rE).eval ρ)
      (1 + m + m_other + ckaVpPot (sE.eval ρ)) := by
  unfold vSendStep1C; rw [eval_bind_ret]
  refine potS_ite (fun _ => ?_) (fun _ => ?_)
  · rw [eval_bind]
    set ρ₁ := Env.cons ((hE.pair (ctxE.pair (pE.pair (sE.pair rE)))).eval ρ) ρ
    have hStart := hhk.startSend_pot (.fst (Expr.v0 (O := OO))) (.fst (.snd .v0))
      (.fst (.snd (.snd .v0))) (.add (vpTcurNat (.fst (.snd (.snd (.snd .v0))))) (.nat 1))
      (vpΓ (.fst (.snd (.snd (.snd .v0))))) (vpRoot (.fst (.snd (.snd (.snd .v0)))))
      (.snd (.snd (.snd (.snd .v0)))) ρ₁ m m_other
    have hPre : (if ((vpΓ (.fst (.snd (.snd (.snd (Expr.v0 (O := OO))))))).eval ρ₁).isNone
        then 1 else 0) = ckaVpPot (sE.eval ρ) := rfl
    rw [hPre] at hStart
    refine PotOKS.bindPot hStart (fun stepOut => ?_)
    refine potS_caseOpt (fun hNone => ?_) (fun ⟨γ', T', σ', ss⟩ hSome => ?_)
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
      exact potS_ret (by simp [ckaStartSendPostGen, ckaVpOptPostGen, hNone, Expr.eval])
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
      exact potS_ret (by
        simp [ckaStartSendPostGen, ckaVpOptPostGen, ckaVpPot, vpMk, hSome, Expr.eval, Expr.v0, Expr.v1])
  · exact potS_ret (by simp only [ckaVpOptPostGen, Expr.eval, Expr.v0, Env.get_cons_zero]; omega)

private theorem vSendC_potOKS_gen {hsTy : Ty S}
    {hk : HooksC OO II (.opt (.base .γ)) (.base .sig) (.base .ss) (.base .rs) hsTy}
    (hhk : CkaHooksPotOK hk) {Γ' : List (Ty S)} (hE : Expr OO Γ' hsTy)
    (ctxE : Expr OO Γ' (cGsTy ckaVpTy)) (pE : Expr OO Γ' .bool) (sE : Expr OO Γ' ckaVpTy)
    (mE : Expr OO Γ' (.base .msg)) (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg))))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ') (m m_other : ℕ) :
    PotOKS P_cka (ckaVSendPostGen m m_other) ((vSendC hk hE ctxE pE sE mE pairE rE).eval ρ)
      (1 + m + m_other + ckaVpPot (sE.eval ρ)) := by
  unfold vSendC; rw [eval_bind_ret, eval_bind]
  set ρ₁ := Env.cons ((hE.pair (ctxE.pair (pE.pair (sE.pair (mE.pair (pairE.pair rE)))))).eval ρ) ρ
  have hStep1 := vSendStep1C_potOKS_gen hhk (.fst (Expr.v0 (O := OO))) (.fst (.snd .v0))
    (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
    (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))) ρ₁ m m_other
  refine PotOKS.bindPot hStep1 (fun stepOut => ?_)
  refine potS_caseOpt (fun hNone => ?_) (fun s1 hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potS_ret (by simp [ckaVpOptPostGen, ckaVSendPostGen, hNone, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potS_caseOpt (fun _ => ?_) (fun v _ => ?_)
    · exact potS_ret (by simp [ckaVpOptPostGen, ckaVSendPostGen, hSome, Expr.eval, Expr.v0, Expr.v1])
    · rw [eval_bind]
      set ρ₂ := Env.cons v (Env.cons s1 (Env.cons stepOut ρ₁))
      have hFs := hhk.fsSend_pot (.snd (Expr.v2 (O := OO))) (.fst (.snd .v3))
        (.fst (.snd (.snd .v3))) (vpTcurNat .v1) .v0 (.pair (vpTcurNat .v1) (vpTcur .v1))
        (.fst (.snd (.snd (.snd (.snd .v3))))) (.fst (.snd (.snd (.snd (.snd (.snd .v3))))))
        ρ₂ (m + m_other + ckaVpPot s1) (fun _ => m + m_other + ckaVpPot s1) (fun _ _ _ => Nat.le_refl _)
      have hStepEq : ckaVpOptPostGen m m_other stepOut = m + m_other + ckaVpPot s1 := by
        simp [ckaVpOptPostGen, hSome]
      rw [← hStepEq] at hFs
      refine PotOKS.bindPot hFs (fun fsOut => ?_)
      rw [hStepEq]
      refine potS_caseOpt (fun _ => ?_) (fun ⟨v', ct⟩ _ => ?_)
      · exact potS_ret (by simp only [ckaVSendPostGen, Expr.eval]; omega)
      · exact potS_ret (by
          simp [ckaVSendPostGen, ckaVpPot, vpSetVS, vpMk, vpΓ, letE_eval,
            Expr.eval, Expr.v0, Expr.v3, ρ₂])

private theorem commitEC_potOKS_gen {hsTy : Ty S}
    {hk : HooksC OO II (.opt (.base .γ)) (.base .sig) (.base .ss) (.base .rs) hsTy}
    (hhk : CkaHooksPotOK hk) (L : ℕ) {Γ' : List (Ty S)}
    (esE : Expr OO Γ' (esTy ckaVpTy hsTy)) (sE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (oldE newE : Expr OO Γ' ckaVpTy)
    (posE : Expr OO Γ' posTy) (ρ : Env Γ') (m : ℕ)
    (hab : (esE.eval ρ).2.2 = false)
    (hold : oldE.eval ρ = (pGet (cGsSt sE) pE).eval ρ) :
    PotOKS P_cka (ckaCommitECPostGen m)
      ((commitEC hk L esE sE pE oldE newE posE).eval ρ)
      (1 + m + (ckaVpPot (sE.eval ρ).1.1 + ckaVpPot (sE.eval ρ).1.2)) := by
  unfold commitEC
  rw [eval_bind_ret, eval_bind]
  set s0 := sE.eval ρ
  set p0 := pE.eval ρ
  set m_other := ckaOtherPot s0.1 p0
  have hSum : 1 + m + (ckaVpPot s0.1.1 + ckaVpPot s0.1.2) =
      1 + m + m_other + ckaVpPot (oldE.eval ρ) := by
    have hp := ckaOtherPot_add_pGet s0.1 p0
    rw [hold, pGet_eval_st]
    dsimp only [cGsSt, Expr.eval, m_other, s0, p0] at hp ⊢
    omega
  rw [hSum]
  set ρ₁ := Env.cons ((esE.pair ((cAcceptE L sE pE newE posE).pair (pE.pair (oldE.pair newE)))).eval ρ) ρ
  have hCom := hhk.commit_pot
    (esH (.fst (Expr.v0 (O := OO)))) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd .v0))))
    ρ₁ m m_other
  refine PotOKS.bindPot hCom (fun comOut => ?_)
  refine potS_caseOpt (fun hNone => ?_) (fun new' hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potS_ret (by simp [ckaVpOptPostGen, ckaCommitECPostGen, ckaPotGen, esMk, hNone, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potS_ret ?_
    simp only [ckaVpOptPostGen, ckaCommitECPostGen, hSome, pair_eval, esMk, esAbort,
      Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get_cons_zero, Env.get_cons_succ,
      ρ₁, hab, Bool.false_eq_true, ↓reduceIte]
    have hSt := cGsSetStP_st (O' := OO)
      (.fst (.snd .v2)) (.fst (.snd (.snd .v2))) .v0
      (Env.cons new' (Env.cons comOut ρ₁))
    have hAcc := cAcceptE_st L sE pE newE posE ρ
    simp only [Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ, ρ₁] at hSt
    rw [hSt, hAcc]
    change m + (ckaVpPot (if p0 = true then
        ((if p0 = true then (s0.1.1, newE.eval ρ) else (newE.eval ρ, s0.1.2)).1, new')
      else
        (new', (if p0 = true then (s0.1.1, newE.eval ρ) else (newE.eval ρ, s0.1.2)).2)).1 +
      ckaVpPot (if p0 = true then
        ((if p0 = true then (s0.1.1, newE.eval ρ) else (newE.eval ρ, s0.1.2)).1, new')
      else
        (new', (if p0 = true then (s0.1.1, newE.eval ρ) else (newE.eval ρ, s0.1.2)).2)).2) ≤
      m + m_other + ckaVpPot new'
    have hm : m_other = ckaOtherPot s0.1 p0 := rfl
    rw [hm]
    cases p0 <;> (simp [ckaOtherPot]; omega)

private theorem transmitEC_potOKS_gen {hsTy : Ty S}
    {hk : HooksC OO II (.opt (.base .γ)) (.base .sig) (.base .ss) (.base .rs) hsTy}
    (hhk : CkaHooksPotOK hk) (L Δ qep : ℕ) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' (esTy ckaVpTy hsTy))
    (argE : Expr OO Γ' (.prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))))
    (ρ : Env Γ') (m : ℕ) :
    PotOKS P_cka (fun x => m + ckaPotGen x.2)
      ((transmitEC hk L Δ qep π esE argE).eval ρ)
      (1 + m + ckaPotGen (esE.eval ρ)) := by
  unfold transmitEC
  rw [eval_bind_ret]
  refine potS_ite (fun _ => ?_) (fun hNotOr => ?_)
  · exact potS_ret (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega)
  · have hab : (esE.eval ρ).2.2 = false := by
      simp [orE_eval, esAbort, Expr.eval, Expr.v0] at hNotOr; exact hNotOr.1
    refine potS_caseOpt (fun _ => ?_) (fun s1 hs1 => ?_)
    · exact potS_ret (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega)
    · have hs1St : s1.1 = (esE.eval ρ).1.1 :=
        cEpMgmtE_some_st Δ qep _ _ _ _ hs1
      refine potS_ite (fun _ => ?_) (fun _ => ?_)
      · exact potS_ret (by simp [ckaPotGen, esSetAbort, esMk, Expr.eval, Expr.v0, Expr.v1]; omega)
      · rw [eval_bind]
        set p0 := (argE.eval ρ).1
        set m_other := ckaOtherPot s1.1 p0
        have hPreEq : 1 + m + ckaPotGen (esE.eval ρ) =
            1 + m + m_other + ckaVpPot (if p0 then s1.1.2 else s1.1.1) := by
          have hp := ckaOtherPot_add_pGet s1.1 p0
          simp only [ckaPotGen, hab, Bool.false_eq_true, ↓reduceIte, ← hs1St]
          omega
        rw [hPreEq]
        set ρ₁ := Env.cons s1 (Env.cons ((esE.pair argE).eval ρ) ρ)
        have hSend := vSendC_potOKS_gen hhk
          (esH (.fst (Expr.v1 (O := OO)))) .v0 (.fst (.snd .v1)) (pGet (cGsSt .v0) (.fst (.snd .v1)))
          (.fst (.snd (.snd .v1))) .none (.snd (.snd (.snd .v1)))
          ρ₁ m m_other
        have hGetEq : (pGet (cGsSt (Expr.v0 (O := OO))) (.fst (.snd .v1))).eval ρ₁ =
            (if p0 then s1.1.2 else s1.1.1) := by
          rw [pGet_eval_st]; rfl
        rw [hGetEq] at hSend
        refine PotOKS.bindPot hSend (fun sendOut => ?_)
        refine potS_caseOpt (fun hNone => ?_) (fun stCt hSome => ?_)
        · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
          exact potS_ret (by simp [ckaVSendPostGen, ckaPotGen, esMk, hNone, Expr.eval])
        · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
          refine potS_ret ?_
          have hRec := cRecordE_st (O' := OO) L Δ .v2 (.fst (.snd .v3)) (.fst .v0)
            (.pair (.pair (.fst (.snd .v3))
              (.pair (pGet (cGsEpoch .v2) (.fst (.snd .v3)))
                (.add (pGet (cGsIdx .v2) (.fst (.snd .v3))) (.nat 1))))
              (.pair (.fst (.snd (.snd .v3))) (.snd .v0))) (.bool false)
            (Env.cons stCt (Env.cons sendOut ρ₁))
          simp only [ckaVSendPostGen, hSome, ckaPotGen, esMk, esAbort, pair_eval,
            Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ,
            ρ₁, hab, Bool.false_eq_true, ↓reduceIte] at hRec ⊢
          rw [hRec]
          change m + (ckaVpPot (if p0 = true then (s1.1.1, stCt.1) else (stCt.1, s1.1.2)).1 +
            ckaVpPot (if p0 = true then (s1.1.1, stCt.1) else (stCt.1, s1.1.2)).2) ≤
            m + m_other + ckaVpPot stCt.1
          have hm : m_other = ckaOtherPot s1.1 p0 := rfl
          rw [hm]
          cases p0 <;> (simp [ckaOtherPot]; omega)

private theorem challEC_potOKS_gen {hsTy : Ty S}
    {hk : HooksC OO II (.opt (.base .γ)) (.base .sig) (.base .ss) (.base .rs) hsTy}
    (hhk : CkaHooksPotOK hk) (L Δ qep : ℕ) (cfg : ConfigEC OO) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' (esTy ckaVpTy hsTy))
    (argE : Expr OO Γ'
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))))
    (ρ : Env Γ') (m : ℕ) :
    PotOKS P_cka (fun x => m + ckaPotGen x.2)
      ((challEC hk L Δ qep cfg π esE argE).eval ρ)
      (1 + m + ckaPotGen (esE.eval ρ)) := by
  unfold challEC
  rw [eval_bind_ret]
  refine potS_ite (fun _ => ?_) (fun hNotOr => ?_)
  · exact potS_ret (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega)
  · have hab : (esE.eval ρ).2.2 = false := by
      simp [orE_eval, esAbort, Expr.eval, Expr.v0] at hNotOr; exact hNotOr.1
    refine potS_caseOpt (fun _ => ?_) (fun s1 hs1 => ?_)
    · exact potS_ret (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega)
    · have hs1St : s1.1 = (esE.eval ρ).1.1 :=
        cEpMgmtE_some_st Δ qep _ _ _ _ hs1
      refine potS_ite (fun _ => ?_) (fun _ => ?_)
      · exact potS_ret (by
          simp only [Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]; omega)
      · refine potS_ite (fun _ => ?_) (fun _ => ?_)
        · exact potS_ret (by simp [ckaPotGen, esSetAbort, esMk, Expr.eval, Expr.v0, Expr.v1]; omega)
        · rw [eval_bind]
          set p0 := (argE.eval ρ).1
          set m_other := ckaOtherPot s1.1 p0
          have hPreEq : 1 + m + ckaPotGen (esE.eval ρ) =
              1 + m + m_other + ckaVpPot (if p0 then s1.1.2 else s1.1.1) := by
            have hp := ckaOtherPot_add_pGet s1.1 p0
            simp only [ckaPotGen, hab, Bool.false_eq_true, ↓reduceIte, ← hs1St]
            omega
          rw [hPreEq]
          set ρ₁ := Env.cons s1 (Env.cons ((esE.pair argE).eval ρ) ρ)
          have hSend := vSendC_potOKS_gen hhk
            (esH (.fst (Expr.v1 (O := OO)))) .v0 (.fst (.snd .v1)) (pGet (cGsSt .v0) (.fst (.snd .v1)))
            (cfg.challMsgE (pGet (cGsEpoch .v0) (.fst (.snd .v1))) (cGsB (esG (.fst .v1)))
              (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1)))))
            (.some (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))))
            (.snd (.snd (.snd (.snd .v1))))
            ρ₁ m m_other
          have hGetEq : (pGet (cGsSt (Expr.v0 (O := OO))) (.fst (.snd .v1))).eval ρ₁ =
              (if p0 then s1.1.2 else s1.1.1) := by
            rw [pGet_eval_st]; rfl
          rw [hGetEq] at hSend
          refine PotOKS.bindPot hSend (fun sendOut => ?_)
          refine potS_caseOpt (fun hNone => ?_) (fun stCt hSome => ?_)
          · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
            exact potS_ret (by simp [ckaVSendPostGen, ckaPotGen, esMk, hNone, Expr.eval])
          · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
            refine potS_ret ?_
            have hRec := cRecordE_st (O' := OO) L Δ .v2 (.fst (.snd .v3)) (.fst .v0)
              (.pair (.pair (.fst (.snd .v3))
                (.pair (pGet (cGsEpoch .v2) (.fst (.snd .v3)))
                  (.add (pGet (cGsIdx .v2) (.fst (.snd .v3))) (.nat 1))))
                (.pair (cfg.challMsgE (pGet (cGsEpoch .v2) (.fst (.snd .v3)))
                  (cGsB (esG (.fst .v3))) (.fst (.snd (.snd .v3)))
                  (.fst (.snd (.snd (.snd .v3))))) (.snd .v0))) (.bool true)
              (Env.cons stCt (Env.cons sendOut ρ₁))
            simp only [ckaVSendPostGen, hSome, ckaPotGen, esMk, esAbort, pair_eval,
              Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ,
              ρ₁, hab, Bool.false_eq_true, ↓reduceIte] at hRec ⊢
            rw [hRec]
            change m + (ckaVpPot (if p0 = true then (s1.1.1, stCt.1) else (stCt.1, s1.1.2)).1 +
              ckaVpPot (if p0 = true then (s1.1.1, stCt.1) else (stCt.1, s1.1.2)).2) ≤
              m + m_other + ckaVpPot stCt.1
            have hm : m_other = ckaOtherPot s1.1 p0 := rfl
            rw [hm]
            cases p0 <;> (simp [ckaOtherPot]; omega)

private theorem deliverEC_potOKS_gen {hsTy : Ty S}
    {hk : HooksC OO II (.opt (.base .γ)) (.base .sig) (.base .ss) (.base .rs) hsTy}
    (hhk : CkaHooksPotOK hk) (L maxSkip : ℕ) (cfg : ConfigEC OO)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' (esTy ckaVpTy hsTy))
    (argE : Expr OO Γ' (.prod .bool hdrCtTy)) (ρ : Env Γ') (m : ℕ) :
    PotOKS P_cka (fun x => m + ckaPotGen x.2)
      ((deliverEC hk L maxSkip cfg esE argE).eval ρ)
      (1 + m + ckaPotGen (esE.eval ρ)) := by
  unfold deliverEC
  rw [eval_bind_ret]
  refine potS_ite (fun _ => ?_) (fun hNotOr => ?_)
  · exact potS_ret (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega)
  · have hab : (esE.eval ρ).2.2 = false := by
      simp [orE_eval, esAbort, Expr.eval, Expr.v0] at hNotOr; exact hNotOr.1
    refine potS_caseOpt (fun _ => ?_) (fun r1 _ => ?_)
    · exact potS_ret (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega)
    · refine potS_bind (1 + m + ckaPotGen (esE.eval ρ))
        (by rw [vRecvC_queries_zero hhk]; omega) (fun recvOut => ?_)
      refine potS_caseOpt (fun _ => ?_) (fun resInner _ => ?_)
      · exact potS_ret (by simp [ckaPotGen, esMk, Expr.eval]; omega)
      · refine potS_caseOpt (fun _ => ?_) (fun stTim _ => ?_)
        · refine potS_ret ?_
          simp only [esMk, esAbort, esG, pair_eval,
            Expr.eval, Expr.v1, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab]
          refine Nat.le_trans
            (Nat.add_le_add_left (Nat.le_of_eq
              (ckaPotGen_mk_eq (g2 := (esE.eval ρ).1) (h2 := (esE.eval ρ).2.1)
                (ite_fst_eq (by rw [cGsSetWin_st]; rfl) rfl))) m) ?_
          simp only [ckaPotGen, hab, Bool.false_eq_true, ↓reduceIte]
          omega
        · rw [eval_bind]
          set ρ₂ := Env.cons stTim (Env.cons resInner (Env.cons recvOut
            (Env.cons r1 (Env.cons ((esE.pair argE).eval ρ) ρ))))
          have hCom := commitEC_potOKS_gen hhk L
            (esSetH (.fst (Expr.v4 (O := OO))) (.snd .v2)) (esG (.fst .v4)) (.fst (.snd .v4))
            (pGet (cGsSt (esG (.fst .v4))) (.fst (.snd .v4))) (.fst .v0) (cRecPos .v3) ρ₂ m
            (by simp [ρ₂, esSetH, letE_eval, esMk, esAbort, esG, hab, Expr.eval, Expr.v0, Expr.v2, Expr.v4])
            rfl
          have hPreEq : 1 + m + ckaPotGen (esE.eval ρ) =
              1 + m + (ckaVpPot (esE.eval ρ).1.1.1 + ckaVpPot (esE.eval ρ).1.1.2) := by
            simp [ckaPotGen, hab]
          rw [hPreEq]
          refine PotOKS.bindPot hCom (fun comOut => ?_)
          refine potS_caseOpt (fun hNone => ?_) (fun s_acc hSome => ?_)
          · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
            exact potS_ret (by simp [ckaCommitECPostGen, hNone, Expr.eval, Expr.v0])
          · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
            refine potS_ret ?_
            simp only [ckaCommitECPostGen, hSome, esSetG, esMk, esAbort,
              Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
            refine Nat.le_trans
              (Nat.add_le_add_left (Nat.le_of_eq
                (ckaPotGen_mk_eq (g2 := s_acc) (h2 := comOut.2.2.1)
                  (ite_fst_eq (by rw [cGsSetWin_st]; rfl) rfl))) m) ?_
            simp only [ckaPotGen]
            omega

private theorem injectEC_potOKS_gen {hsTy : Ty S}
    {hk : HooksC OO II (.opt (.base .γ)) (.base .sig) (.base .ss) (.base .rs) hsTy}
    (hhk : CkaHooksPotOK hk) (L Δ qep : ℕ) (cfg : ConfigEC OO)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' (esTy ckaVpTy hsTy))
    (argE : Expr OO Γ' (.prod .bool hdrCtTy)) (ρ : Env Γ') (m : ℕ) :
    PotOKS P_cka (fun x => m + ckaPotGen x.2)
      ((injectEC hk L Δ qep cfg esE argE).eval ρ)
      (1 + m + ckaPotGen (esE.eval ρ)) := by
  unfold injectEC
  rw [eval_bind_ret]
  refine potS_ite (fun _ => ?_) (fun hNotRef => ?_)
  · exact potS_ret (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega)
  · have hab : (esE.eval ρ).2.2 = false := by
      simp [orE_eval, esAbort, Expr.eval, Expr.v0] at hNotRef; exact hNotRef.1
    refine potS_bind (1 + m + ckaPotGen (esE.eval ρ))
      (by rw [vRecvC_queries_zero hhk]; omega) (fun recvOut => ?_)
    refine potS_caseOpt (fun _ => ?_) (fun resInner _ => ?_)
    · exact potS_ret (by simp [ckaPotGen, esMk, Expr.eval]; omega)
    · refine potS_caseOpt (fun _ => ?_) (fun stTim _ => ?_)
      · exact potS_ret (by
          simp only [ckaPotGen, esSetH, esMk, esG, esAbort, hab, Bool.false_eq_true, ↓reduceIte,
            Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get_cons_zero, Env.get_cons_succ]
          omega)
      · refine potS_ite (fun _ => ?_) (fun _ => ?_)
        · exact potS_ret (by
            simp only [ckaPotGen, esSetH, esMk, esG, esAbort, hab, Bool.false_eq_true, ↓reduceIte,
              Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ]
            omega)
        · refine potS_ite (fun _ => ?_) (fun _ => ?_)
          · rw [eval_bind]
            set ρ₂ := Env.cons stTim (Env.cons resInner (Env.cons recvOut
              (Env.cons ((esE.pair argE).eval ρ) ρ)))
            have hCom := commitEC_potOKS_gen hhk L
              (esSetH (.fst (Expr.v3 (O := OO))) (.snd .v2)) (esG (.fst .v3)) (.fst (.snd .v3))
              (pGet (cGsSt (esG (.fst .v3))) (.fst (.snd .v3))) (.fst .v0)
              (.pair (otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
              ρ₂ m
              (by simp [ρ₂, esSetH, letE_eval, esMk, esAbort, esG, hab, Expr.eval, Expr.v0, Expr.v2, Expr.v3])
              rfl
            have hPreEq : 1 + m + ckaPotGen (esE.eval ρ) =
                1 + m + (ckaVpPot (esE.eval ρ).1.1.1 + ckaVpPot (esE.eval ρ).1.1.2) := by
              simp [ckaPotGen, hab]
            rw [hPreEq]
            refine PotOKS.bindPot hCom (fun comOut => ?_)
            refine potS_caseOpt (fun hNone => ?_) (fun s_acc hSome => ?_)
            · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
              exact potS_ret (by simp [ckaCommitECPostGen, hNone, Expr.eval, Expr.v0])
            · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
              exact potS_ret (by
                simp [ckaCommitECPostGen, hSome, ckaPotGen, esSetG, esMk, esAbort,
                  Expr.eval, Expr.v0, Expr.v1])
          · refine potS_ret ?_
            simp only [esSetG, esSetH, esMk, esAbort, esG,
              Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab]
            refine Nat.le_trans
              (Nat.add_le_add_left (Nat.le_of_eq
                (ckaPotGen_mk_eq (g2 := (esE.eval ρ).1) (h2 := (esE.eval ρ).2.1)
                  (ite_fst_eq (by rw [cGsSetWin_st]; rfl) rfl))) m) ?_
            simp only [ckaPotGen, hab, Bool.false_eq_true, ↓reduceIte]
            omega

private theorem corrEC_potOKS_gen {hsTy : Ty S}
    {hk : HooksC OO II (.opt (.base .γ)) (.base .sig) (.base .ss) (.base .rs) hsTy}
    (hhk : CkaHooksPotOK hk) (L : ℕ) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' (esTy ckaVpTy hsTy)) (pE : Expr OO Γ' .bool)
    (ρ : Env Γ') (m : ℕ) :
    PotOKS P_cka (fun x => m + ckaPotGen x.2)
      ((corrEC hk L π esE pE).eval ρ)
      (1 + m + ckaPotGen (esE.eval ρ)) := by
  unfold corrEC
  rw [eval_bind_ret]
  refine potS_ite (fun _ => ?_) (fun hNotRef => ?_)
  · exact potS_ret (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega)
  · have hab : (esE.eval ρ).2.2 = false := by
      simp [orE_eval, esAbort, Expr.eval, Expr.v0] at hNotRef; exact hNotRef.1
    refine potS_ite (fun _ => ?_) (fun _ => ?_)
    · exact potS_ret (by simp [ckaPotGen, esSetAbort, letE_eval, esMk, esG, Expr.eval, Expr.v0]; omega)
    · refine potS_bind (m + ckaPotGen (esE.eval ρ))
        (Nat.le_trans (Nat.add_le_add_right (hhk.reveal_queries _ _ _ _) _) (by omega))
        (fun corrOut => ?_)
      refine potS_caseOpt (fun _ => ?_) (fun ps _ => ?_)
      · exact potS_ret (by simp [ckaPotGen, esMk, Expr.eval])
      · refine potS_ret ?_
        have hAfter := cAfterCorrE_st (O' := OO) L (esG (.fst .v2)) (.snd .v2)
          (Env.cons ps (Env.cons corrOut (Env.cons ((esE.pair pE).eval ρ) ρ)))
        simp only [ckaPotGen, esMk, esAbort, esG, pair_eval,
          Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ,
          hab, Bool.false_eq_true, ↓reduceIte] at hAfter ⊢
        rw [hAfter]

private theorem implEC_potOKS_gen {hsTy : Ty S}
    {hk : HooksC OO II (.opt (.base .γ)) (.base .sig) (.base .ss) (.base .rs) hsTy}
    (hhk : CkaHooksPotOK hk) (L Δ qep maxSkip : ℕ)
    (cfg : ConfigEC OO) (π : Policy)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' (esTy ckaVpTy hsTy))
    (qE : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ') (m : ℕ) :
    PotOKS P_cka (fun x => m + ckaPotGen x.2)
      ((implEC hk L Δ qep maxSkip cfg π esE qE).eval ρ)
      (1 + m + ckaPotGen (esE.eval ρ)) := by
  unfold implEC
  rw [eval_bind_ret]
  refine potS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
  · refine potS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
    · refine potS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
      · refine potS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
        · rw [eval_bind]
          exact PotOKS.bindPot
            (transmitEC_potOKS_gen hhk L Δ qep π (.fst (Expr.v4 (O := OO))) .v0 _ m)
            (fun _ => potS_ret (by simp [Expr.eval, Expr.v0]))
        · rw [eval_bind]
          exact PotOKS.bindPot
            (challEC_potOKS_gen hhk L Δ qep cfg π (.fst (Expr.v4 (O := OO))) .v0 _ m)
            (fun _ => potS_ret (by simp [Expr.eval, Expr.v0]))
      · rw [eval_bind]
        exact PotOKS.bindPot
          (deliverEC_potOKS_gen hhk L maxSkip cfg (.fst (Expr.v3 (O := OO))) .v0 _ m)
          (fun _ => potS_ret (by simp [Expr.eval, Expr.v0]))
    · rw [eval_bind]
      exact PotOKS.bindPot
        (injectEC_potOKS_gen hhk L Δ qep cfg (.fst (Expr.v2 (O := OO))) .v0 _ m)
        (fun _ => potS_ret (by simp [Expr.eval, Expr.v0]))
  · rw [eval_bind]
    exact PotOKS.bindPot
      (corrEC_potOKS_gen hhk L π (.fst (Expr.v1 (O := OO))) .v0 _ m)
      (fun _ => potS_ret (by simp [Expr.eval, Expr.v0]))

/-! ## Hook instances -/

private theorem ckaStartSendC_potOKS (Δcka : ℕ) (mo : Mode) {Γ' : List (Ty S)}
    (hE : Expr OO Γ' ckaHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γvE : Expr OO Γ' (.opt (.base .γ))) (σE : Expr OO Γ' (.base .sig))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ') (m m_other : ℕ) :
    PotOKS P_cka (ckaStartSendPostGen m m_other)
      ((ckaStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) Δcka mo hE ctxE pE tE γvE σE rE).eval ρ)
      (1 + m + m_other + (if (γvE.eval ρ).isNone then 1 else 0)) := by
  unfold ckaStartSendC
  rw [eval_bind_ret]
  refine potS_caseOpt (fun hNone => ?_) (fun γ _ => ?_)
  · have hγ : (γvE.eval ρ).isNone = true := by
      simp [Expr.eval, Expr.v0] at hNone; simp [hNone]
    refine potS_bind (1 + m + m_other) (by simp [hγ, Comp.queries]; omega) (fun tiOpt => ?_)
    refine potS_caseOpt (fun _ => ?_) (fun ⟨tMsg, ik⟩ _ => ?_)
    · exact potS_ret (by simp [ckaStartSendPostGen, Expr.eval]; omega)
    · refine potS_ite (fun _ => ?_) (fun _ => ?_)
      · refine potS_bind (m + m_other) (by simp [Comp.queries]; omega) (fun γOpt => ?_)
        refine potS_caseOpt (fun _ => ?_) (fun γ' _ => ?_)
        · exact potS_ret (by simp [ckaStartSendPostGen, Expr.eval])
        · exact potS_ret (by simp [ckaStartSendPostGen, Expr.eval])
      · exact potS_ret (by simp [ckaStartSendPostGen, Expr.eval])
  · refine potS_bind (m + m_other) (by simp [Comp.queries]; omega) (fun _ => ?_)
    exact potS_ret (by simp [ckaStartSendPostGen, Expr.eval])

private theorem ckaCommitC_potOKS (Δcka : ℕ) (mo : Mode) {Γ' : List (Ty S)}
    (hE : Expr OO Γ' ckaHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (oldE newE : Expr OO Γ' ckaVpTy)
    (ρ : Env Γ') (m m_other : ℕ) :
    PotOKS P_cka (ckaVpOptPostGen m m_other)
      ((ckaCommitC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) Δcka mo hE ctxE pE oldE newE).eval ρ)
      (1 + m + m_other + ckaVpPot (oldE.eval ρ)) := by
  unfold ckaCommitC
  rw [eval_bind_ret]
  refine potS_ite (fun hc => ?_) (fun _ => ?_)
  · have hOldPot : ckaVpPot (oldE.eval ρ) = 1 := by
      simp only [Expr.eval, Expr.v0, Env.get_cons_zero, isSomeE, vpΓ] at hc
      rcases hγ : (oldE.eval ρ).2.2.2.2.1 with _ | γ
      · simp [ckaVpPot, hγ]
      · simp [hγ] at hc
    refine potS_bind (1 + m + m_other) (by simp [hOldPot, Comp.queries]; omega) (fun rOpt => ?_)
    refine potS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
    · exact potS_ret (by simp [ckaVpOptPostGen, Expr.eval]; omega)
    · refine potS_ite (fun _ => ?_) (fun _ => ?_)
      · refine potS_bind (m + m_other) (by simp [Comp.queries]; omega) (fun γOpt => ?_)
        refine potS_caseOpt (fun _ => ?_) (fun γ' _ => ?_)
        · exact potS_ret (by simp [ckaVpOptPostGen, Expr.eval])
        · exact potS_ret (by
            simp [ckaVpOptPostGen, ckaVpPot, vpSetΓ, vpMk, vpId, vpRoot, vpVS, vpVR, vpTcur, vpTcurNat,
              Expr.eval, Expr.v0, Expr.v4])
      · refine potS_ret ?_
        simp only [ckaVpOptPostGen, Expr.eval, Expr.v2, Env.get_cons_succ, Env.get_cons_zero]
        have := ckaVpPot_le_one (newE.eval ρ)
        omega
  · refine potS_ret ?_
    simp only [ckaVpOptPostGen, Expr.eval, Expr.v0, Env.get_cons_zero]
    have := ckaVpPot_le_one (newE.eval ρ)
    omega

private theorem hooksCKAC_potOK (B Δcka : ℕ) (mo : Mode) :
    CkaHooksPotOK (hooksCKAC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B Δcka mo) where
  startSend_pot := ckaStartSendC_potOKS Δcka mo
  startRecv_queries _ _ _ _ _ _ _ := by simp [hooksCKAC, ckaStartRecvC, Comp.queries]
  fsSend_pot _ _ _ _ _ _ _ _ _ _ _ hB := by
    dsimp only [hooksCKAC, ckaFsSendC]; exact potS_ret (by simp only [Expr.eval]; exact hB _ _ _)
  fsRecv_queries _ _ _ _ _ _ _ _ := by simp [hooksCKAC, ckaFsRecvC, Comp.queries]
  commit_pot := ckaCommitC_potOKS Δcka mo
  reveal_queries _ _ _ _ := by simp [hooksCKAC, ckaRevealC, Comp.queries]

private theorem hooksCKABucketC_potOK (B Δcka : ℕ) (tL : Option ℕ) :
    CkaHooksPotOK (hooksCKABucketC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B Δcka tL) where
  startSend_pot := ckaStartSendC_potOKS Δcka ⟨true, tL, 0⟩
  startRecv_queries _ _ _ _ _ _ _ := by simp [hooksCKABucketC, Comp.queries]
  fsSend_pot _ _ _ _ _ _ _ _ _ _ _ hB := by
    dsimp only [hooksCKABucketC, ckaFsSendC]; exact potS_ret (by simp only [Expr.eval]; exact hB _ _ _)
  fsRecv_queries _ _ _ _ _ _ _ _ := by simp [hooksCKABucketC, ckaFsRecvC, Comp.queries]
  commit_pot := ckaCommitC_potOKS Δcka ⟨true, tL, 0⟩
  reveal_queries _ _ _ _ := by simp [hooksCKABucketC, ckaRevealC, Comp.queries]

private theorem ckaStartSendUC_potOKS (Δcka : ℕ) (mo : Mode) {Γ' : List (Ty S)}
    (hE : Expr OO Γ' ckaUHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy)) (pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat) (γvE : Expr OO Γ' (.opt (.base .γ))) (σE : Expr OO Γ' (.base .sig))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ') (m m_other : ℕ) :
    PotOKS P_cka (ckaStartSendPostGen m m_other)
      ((ckaStartSendUC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) Δcka mo hE ctxE pE tE γvE σE rE).eval ρ)
      (1 + m + m_other + (if (γvE.eval ρ).isNone then 1 else 0)) := by
  unfold ckaStartSendUC; rw [eval_bind_ret]
  refine potS_caseOpt (fun hNone => ?_) (fun γ _ => ?_)
  · have hγ : (γvE.eval ρ).isNone = true := by simp [Expr.eval, Expr.v0] at hNone; simp [hNone]
    refine potS_bind (1 + m + m_other) (by simp [hγ, Comp.queries]; omega) (fun tiOpt => ?_)
    refine potS_caseOpt (fun _ => ?_) (fun ⟨tMsg, ik⟩ _ => ?_)
    · exact potS_ret (by simp [ckaStartSendPostGen, Expr.eval]; omega)
    · refine potS_bind (1 + m + m_other) (by simp [Comp.queries]) (fun _ => ?_)
      refine potS_ite (fun _ => ?_) (fun _ => ?_)
      · refine potS_bind (m + m_other) (by simp [Comp.queries]; omega) (fun γOpt => ?_)
        refine potS_caseOpt (fun _ => ?_) (fun γ' _ => ?_) <;>
          exact potS_ret (by simp [ckaStartSendPostGen, Expr.eval])
      · exact potS_ret (by simp [ckaStartSendPostGen, Expr.eval])
  · refine potS_bind (m + m_other) (by simp [Comp.queries]; omega) (fun _ => ?_)
    refine potS_bind (m + m_other) (by simp [Comp.queries]) (fun _ => ?_)
    exact potS_ret (by simp [ckaStartSendPostGen, Expr.eval])

private theorem hooksCKAUC_potOK (B Δcka : ℕ) (mo : Mode) :
    CkaHooksPotOK (hooksCKAUC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B Δcka mo) where
  startSend_pot := ckaStartSendUC_potOKS Δcka mo
  startRecv_queries _ _ _ _ _ _ _ := by simp [hooksCKAUC, Comp.queries]
  fsSend_pot _ _ _ _ _ _ _ _ _ _ _ hB := by
    dsimp only [hooksCKAUC]; exact potS_ret (by simp only [Expr.eval]; exact hB _ _ _)
  fsRecv_queries _ _ _ _ _ _ _ _ := by simp [hooksCKAUC, Comp.queries]
  commit_pot hE ctxE pE oldE newE ρ m m_other := by
    dsimp only [hooksCKAUC]; rw [eval_bind_ret]
    refine potS_ite (fun hc => ?_) (fun _ => ?_)
    · have hOldPot : ckaVpPot (oldE.eval ρ) = 1 := by
        simp only [Expr.eval, Expr.v0, Env.get_cons_zero, isSomeE, vpΓ] at hc
        rcases hγ : (oldE.eval ρ).2.2.2.2.1 with _ | γ <;> [simp [ckaVpPot, hγ]; simp [hγ] at hc]
      refine potS_bind (1 + m + m_other) (by simp [hOldPot, Comp.queries]; omega) (fun rOpt => ?_)
      refine potS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
      · exact potS_ret (by simp [ckaVpOptPostGen, Expr.eval]; omega)
      · refine potS_ite (fun _ => ?_) (fun _ => ?_)
        · refine potS_bind (m + m_other) (by simp [Comp.queries]; omega) (fun γOpt => ?_)
          refine potS_caseOpt (fun _ => ?_) (fun γ' _ => ?_)
          · exact potS_ret (by simp [ckaVpOptPostGen, Expr.eval])
          · exact potS_ret (by
              simp [ckaVpOptPostGen, ckaVpPot, vpSetΓ, vpMk, vpId, vpRoot, vpVS, vpVR, vpTcur, vpTcurNat,
                Expr.eval, Expr.v0, Expr.v4])
        · refine potS_ret ?_
          simp only [ckaVpOptPostGen, Expr.eval, Expr.v2, Env.get_cons_succ, Env.get_cons_zero]
          have := ckaVpPot_le_one (newE.eval ρ); omega
    · refine potS_ret ?_
      simp only [ckaVpOptPostGen, Expr.eval, Expr.v0, Env.get_cons_zero]
      have := ckaVpPot_le_one (newE.eval ρ); omega
  reveal_queries _ _ _ _ := by simp [hooksCKAUC, Comp.queries]

private def ckaBucketPot
    (st : (@ckaBucketEsTy KC Γ CCoins T I KR RSt K SS RS M E).denote) : ℕ :=
  ckaPotGen st.1

private theorem redCKAAuthBucketProg_handle_potOKS (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ)
    (m : ℕ) (qv : (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E).denote)
    (sv : (@ckaBucketEsTy KC Γ CCoins T I KR RSt K SS RS M E).denote) :
    PotOKS P_cka (fun x => m + ckaBucketPot x.2)
      (((redCKAAuthBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
          (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
          (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip tL).handle).eval
        (.cons sv (.cons qv .nil)))
      (1 + m + ckaBucketPot sv) := by
  have hhk := hooksCKABucketC_potOK (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B Δcka tL
  dsimp only [redCKAAuthBucketProg]; rw [eval_bind_ret]
  refine potS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
  · refine potS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
    · refine potS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
      · refine potS_caseSum (fun x _ => ?_) (fun _ _ => ?_)
        · rw [eval_bind_ret]
          refine potS_ite (fun _ => ?_) (fun hNotOr => ?_)
          · exact potS_ret (by
              simp only [ckaBucketPot, Expr.eval, Expr.v0, Expr.v5, Env.get_cons_zero, Env.get_cons_succ]
              omega)
          · have hab : sv.1.2.2 = false := by
              simp [orE_eval, esAbort, Expr.eval, Expr.v0, Expr.v5] at hNotOr; exact hNotOr.1
            refine potS_caseOpt (fun _ => ?_) (fun s1 hs1 => ?_)
            · exact potS_ret (by
                simp only [ckaBucketPot, Expr.eval, Expr.v0, Expr.v5, Env.get_cons_zero, Env.get_cons_succ]
                omega)
            · have hs1St : s1.1 = sv.1.1.1 := cEpMgmtE_some_st (2 + Δcka) qep _ _ _ _ hs1
              rw [eval_bind]
              set p0 := x.1
              set m_other := ckaOtherPot s1.1 p0
              have hPreEq : 1 + m + ckaBucketPot sv =
                  1 + m + m_other + ckaVpPot (if p0 then s1.1.2 else s1.1.1) := by
                have hp := ckaOtherPot_add_pGet s1.1 p0
                simp only [ckaBucketPot, ckaPotGen, hab, Bool.false_eq_true, ↓reduceIte, ← hs1St]
                omega
              rw [hPreEq]
              refine PotOKS.bindPot (B₁ := ckaVSendPostGen m m_other) ?_ (fun sendOut => ?_)
              · convert vSendC_potOKS_gen hhk _ _ _ _ _ _ _ _ m m_other using 2
                rw [pGet_eval_st]; rfl
              · refine potS_caseOpt (fun hNone => ?_) (fun stCt hSome => ?_)
                · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
                  exact potS_ret (by simp [ckaVSendPostGen, ckaBucketPot, ckaPotGen, esMk, hNone, Expr.eval])
                · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
                  refine potS_ret ?_
                  simp only [ckaVSendPostGen, hSome, ckaBucketPot, ckaPotGen, esMk, esAbort, pair_eval,
                    Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
                    Env.get_cons_zero, Env.get_cons_succ, hab, Bool.false_eq_true, ↓reduceIte]
                  rw [cRecordE_st]
                  change m + (ckaVpPot (if p0 = true then (s1.1.1, stCt.1) else (stCt.1, s1.1.2)).1 +
                    ckaVpPot (if p0 = true then (s1.1.1, stCt.1) else (stCt.1, s1.1.2)).2) ≤
                    m + m_other + ckaVpPot stCt.1
                  have hm : m_other = ckaOtherPot s1.1 p0 := rfl
                  rw [hm]; cases p0 <;> (simp [ckaOtherPot]; omega)
        · exact potS_ret (by
            simp only [ckaBucketPot, Expr.eval, Expr.v0, Expr.v4, Env.get_cons_zero, Env.get_cons_succ]
            omega)
      · rw [eval_bind]
        exact PotOKS.bindPot
          (deliverEC_potOKS_gen hhk L maxSkip (bucketAuthCfgEC Δcka tL) (.fst (Expr.v3 (O := OO))) .v0 _ m)
          (fun _ => potS_ret (by simp [ckaBucketPot, Expr.eval, Expr.v0, Expr.v4]))
    · rw [eval_bind]
      exact PotOKS.bindPot
        (injectEC_potOKS_gen hhk L (2 + Δcka) qep (bucketAuthCfgEC Δcka tL) (.fst (Expr.v2 (O := OO))) .v0 _ m)
        (fun _ => potS_ret (by simp [ckaBucketPot, Expr.eval, Expr.v0, Expr.v3]))
  · refine potS_ite (fun _ => ?_) (fun hNotRef => ?_)
    · exact potS_ret (by
        simp only [ckaBucketPot, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
        omega)
    · have hab : sv.1.2.2 = false := by
        simp [orE_eval, esAbort, Expr.eval, Expr.v0, Expr.v1] at hNotRef; exact hNotRef.1
      refine potS_bind (m + ckaBucketPot sv) (by simp [ckaRevealC, Comp.queries]; omega) (fun corrOut => ?_)
      refine potS_caseOpt (fun _ => ?_) (fun ps _ => ?_)
      · exact potS_ret (by simp [ckaBucketPot, ckaPotGen, esMk, Expr.eval])
      · refine potS_ret ?_
        simp only [ckaBucketPot, ckaPotGen, esMk, esAbort, pair_eval,
          Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ,
          hab, Bool.false_eq_true, ↓reduceIte]
        rw [cAfterCorrE_st]
        simp [esG, Expr.eval]

/-! ## Top-level query bounds -/

private theorem ckaRed_makesAtMostQueries
    (R : CostedReduction OO II
      (CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool)
    (pot : R.σ.denote → ℕ) (hPot : ∀ s, pot s ≤ 2) (q : ℕ)
    (A : CryptoGames.SM.Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
    (hA : MakesAtMostQueries A q)
    (hTot : R.totalQueries (fun _ => 1) (fun _ => 0) q = 2 * q)
    (hInitQ : R.init.queries (fun _ => 1) (fun _ => 0) = 0)
    (hStep : ∀ (m : ℕ) qv sv, PotOKS P_cka (fun x => m + pot x.2)
      (R.handle.eval (.cons sv (.cons qv .nil))) (1 + m + pot sv))
    (hFinQ : R.finish.queries (fun _ => 1) (fun _ => 0) = 0) :
    (R.eval (fun _ => A) ()).IsQueryBoundP (· matches .inr _) (min (2 * q) (q + 2)) := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) q :=
    hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl])
  refine isQueryBoundP_min_cka ?_ ?_
  · have hSyntactic := CostedReduction.queryBound_eval R
      P_cka (fun _ => 1) (fun _ => 0) (fun _ _ _ => Nat.le_refl 1) ckaIface_fwdU_zero
      (fun _ => A) q (fun _ => hA') ()
    rw [hTot] at hSyntactic
    exact hSyntactic.of_imp (fun x hx => by cases x <;> [cases hx; trivial])
  · suffices hGame : (R.eval (fun _ => A) ()).IsQueryBoundP P_cka (q + 2) from
      hGame.of_imp (fun x hx => by cases x <;> [cases hx; trivial])
    have hInit := potS_comp_const R.init (.cons () .nil)
      (B := fun as : Unit × R.σ.denote => q + pot as.2) (q + 2) (q + 2)
      (fun as => by have := hPot as.2; omega) (by omega)
    unfold CostedReduction.eval CostedReduction.impl
    refine hInit.run _ fun ⟨_, s0⟩ => ?_
    refine (potOKS_simulateQ_handlerImpl_step1_cka pot ckaIface_fwdU_zero R.handle hStep hA' s0).run
      _ fun ⟨bOut, sOut⟩ => ?_
    exact (Comp.queryBound_eval P_cka (fun _ => 1) (fun _ => 0)
      (fun _ _ _ => Nat.le_refl 1) ckaIface_fwdU_zero R.finish
      (.cons sOut (.cons bOut .nil))).mono (by omega)

theorem redCKAAuthProg_makesAtMostQueries (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t q : ℕ)
    (A : CryptoGames.SM.Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
    (hA : MakesAtMostQueries A q) :
    (((redCKAAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip tL t).eval (fun _ => A) ())).IsQueryBoundP
      (· matches .inr _) (min (2 * q) (q + 2)) :=
  ckaRed_makesAtMostQueries _ ckaPotGen ckaPotGen_le_two q A hA
    (by rw [redCKAAuthProg_totalQueries, Nat.mul_comm]) (by simp [redCKAAuthProg, Comp.queries])
    (fun m qv sv => implEC_potOKS_gen (hooksCKAC_potOK B Δcka ⟨true, tL, t⟩)
      L (2 + Δcka) qep maxSkip (modeCfgEC OO ⟨true, tL, t⟩) (⟨true, tL, t⟩ : Mode).policy
      .v0 .v1 (.cons sv (.cons qv .nil)) m)
    (by simp [redCKAAuthProg, Comp.queries])

theorem redCKAAuthBucketProg_makesAtMostQueries (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (q : ℕ)
    (A : CryptoGames.SM.Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
    (hA : MakesAtMostQueries A q) :
    (((redCKAAuthBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip tL).eval (fun _ => A) ())).IsQueryBoundP
      (· matches .inr _) (min (2 * q) (q + 2)) :=
  ckaRed_makesAtMostQueries _ ckaBucketPot (fun (s : ckaBucketEsTy.denote) => ckaPotGen_le_two s.1) q A hA
    (by simp [CostedReduction.totalQueries, redCKAAuthBucketProg, deliverEC, injectEC,
          vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC, hooksCKABucketC, Comp.queries, Nat.mul_comm])
    (by simp [redCKAAuthBucketProg, Comp.queries])
    (redCKAAuthBucketProg_handle_potOKS L B Δcka qep maxSkip tL)
    (by simp [redCKAAuthBucketProg, Comp.queries])

theorem redCKAPrivProg_makesAtMostQueries (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t q : ℕ)
    (A : CryptoGames.SM.Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
    (hA : MakesAtMostQueries A q) :
    (((redCKAPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip tL t).eval (fun _ => A) ())).IsQueryBoundP
      (· matches .inr _) (min (2 * q) (q + 2)) :=
  ckaRed_makesAtMostQueries _ ckaPotGen ckaPotGen_le_two q A hA
    (by rw [redCKAPrivProg_totalQueries, Nat.mul_comm]) (by simp [redCKAPrivProg, Comp.queries])
    (fun m qv sv => implEC_potOKS_gen (hooksCKAC_potOK B Δcka ⟨false, tL, t⟩)
      L (2 + Δcka) qep maxSkip (modeCfgEC OO ⟨false, tL, t⟩) (⟨false, tL, t⟩ : Mode).policy
      .v0 .v1 (.cons sv (.cons qv .nil)) m)
    (by simp [redCKAPrivProg, privOutC, Comp.queries])

theorem redCKAPrivUProg_makesAtMostQueries (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (i q : ℕ)
    (A : CryptoGames.SM.Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
    (hA : MakesAtMostQueries A q) :
    (((redCKAPrivUProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
        (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip tL i).eval (fun _ => A) ())).IsQueryBoundP
      (· matches .inr _) (min (2 * q) (q + 2)) :=
  ckaRed_makesAtMostQueries _ ckaPotGen ckaPotGen_le_two q A hA
    (by simp [CostedReduction.totalQueries, redCKAPrivUProg, privOutC, implEC, transmitEC, challEC,
          deliverEC, injectEC, corrEC, vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC,
          hooksCKAUC, ckaStartSendUC, Comp.queries, Nat.mul_comm])
    (by simp [redCKAPrivUProg, initCKAEStateC_queries, Comp.queries])
    (fun m qv sv => implEC_potOKS_gen (hooksCKAUC_potOK B Δcka ⟨false, tL, i⟩)
      L (2 + Δcka) qep maxSkip (modeCfgEC OO ⟨false, tL, i⟩) (⟨false, tL, i⟩ : Mode).policy
      .v0 .v1 (.cons sv (.cons qv .nil)) m)
    (by simp [redCKAPrivUProg, privOutC, Comp.queries])

end CkaPotOK

end

end Computational.Proofs.ReductionDsl.SM.RedCKAPotOK
