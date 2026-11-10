/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperCKA
import Computational.Proofs.ReductionDsl.Notation

/-!
# Costed `redPRNGAuthDFPaperProg` Reduction

Deep-embedded `CostedReduction` formulation of `DeliverForge.redPRNGAuthDFPaper` with evaluation,
advantage, query, cost, and size-honesty theorems.
-/

@[expose] public section

open ReductionDsl OracleSpec OracleComp

namespace CryptoGames.SM.Construction

open Engine Engine.RedPRNG CKA PRFPRNG
open scoped Computational.Proofs.ReductionDsl.Notation

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "S" => ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "rrTy" => ckaRrTy KC Γ CCoins T I KR RSt K SS RS M E

section HooksPRNGCDFPaper

variable
  {ckaInitA : KC → Γ}
  {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt}
  {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS}
  {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool}
  {eqI : I → I → Bool}
  {eqM : M → M → Bool}
  {eqE : E → E → Bool}
  {lam : I}
  {defaultE : E}
  {sampKR : ProbComp KR}
  {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I}
  {sampK : ProbComp K}

local notation "OO" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

local notation "II" =>
  prngIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

/-- Costed `DeliverForge.redPRNGAuthDFPaper` reduction over `SM.specDF`. -/
def redPRNGAuthDFPaperProg (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction OO II
      (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := prngEsTy
  init := rdsl [_] do
    es ← initPRNGEStateC (raw ⟨true, tL, t⟩) false
    return ((), es)
  handle := rdsl [st, q] do
    implECDFPaper (raw (hooksPRNGC B ⟨true, tL, t⟩)) L (raw (2 + Δcka)) qep maxSkip
      (raw (modeCfgEC OO ⟨true, tL, t⟩)) (raw (⟨true, tL, t⟩ : Mode).policy) st q
  finish := rdsl [st, _] do
    return authOutE L (raw (2 + Δcka)) (raw (⟨true, tL, t⟩ : Mode).policy) st

private theorem simulateQ_liftM_unif {ι : Type} {tspec : OracleSpec.{0, 0} ι} {St α : Type}
    (impl : QueryImpl tspec (StateT St ProbComp)) (mx : ProbComp α) :
    simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
      (liftM mx : TComp tspec α) =
    StateT.lift mx := by
  ext st
  change (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
    (liftM mx : TComp tspec α)).run st = (mx >>= fun a => pure (a, st))
  rw [← liftComp_eq_liftM]
  induction mx using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t r ih =>
    rw [liftComp_bind, liftComp_liftM_query]
    have hq : (liftM (OracleSpec.query t) : TComp tspec _) =
        (liftM (OracleSpec.query (spec := unifSpec + tspec) (.inl t)) : TComp tspec _) := rfl
    have hrun :
        ((liftM ((QueryImpl.liftTarget (StateT St ProbComp)
          (QueryImpl.ofLift unifSpec ProbComp) + impl)
          (.inl t)) : StateT St ProbComp (unifSpec.Range t))).run st =
        ((liftM (OracleSpec.query t) : ProbComp _) >>= fun u => pure (u, st)) := rfl
    rw [hq, simulateQ_query_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind]
    rw [hrun]
    simp only [bind_assoc, pure_bind, ih]

private theorem simulateQ_sampleT_run {ι : Type} {tspec : OracleSpec.{0, 0} ι} {St α : Type}
    [SampleableType α] (impl : QueryImpl tspec (StateT St ProbComp)) (st : St) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
      (sampleT α)).run st =
    (($ᵗ α : ProbComp α) >>= fun a => pure (a, st)) := by
  unfold sampleT
  rw [simulateQ_liftM_unif]
  rfl

theorem redPRNGAuthDFPaperProg_eval_eq_bind_initPRNGRaw_vr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KC] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    {VROkStep : ℕ → RS → Prop}
    (hInitA : ckaInitA = cka.initA)
    (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hVRHk : HooksVRInv VROkStep (hooksPRNG cka prng fs ⟨true, tL, t⟩))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    (redPRNGAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep fs.maxSkip tL t).eval (fun _ => A) () =
      (do
        let es₀ ← initPRNGRaw cka prng fs lam ⟨true, tL, t⟩ false
        let (_, es') ←
          (simulateQ
            (DeliverForge.implEDFPaper (hooksPRNG cka prng fs ⟨true, tL, t⟩)
              (2 + Δcka) qep fs.maxSkip (⟨true, tL, t⟩ : Mode).cfg (⟨true, tL, t⟩ : Mode).policy)
            A).run es₀
        return authOut (2 + Δcka) (⟨true, tL, t⟩ : Mode).policy es') := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  have hHk := hooksPRNGC_agrees_vr
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (prngInit := prngInit)
    (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    cka prng fs B ⟨true, tL, t⟩ hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT hSampCCoins (fun k => hVRHk.mono (Nat.zero_le B_q) (hInitR k)) hFsB
  have hInit := initPRNGEStateC_eval (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    cka prng fs hInitA hInitB hPrngUp hFsInitS hFsInitR hSampKC
    ⟨true, tL, t⟩ (.bool false) (Env.cons (t := (.unit : Ty S)) () .nil)
  unfold CostedReduction.eval redPRNGAuthDFPaperProg CostedReduction.impl
  dsimp only
  rw [eval_bind, hInit]
  let vpE := vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    (γvT := .base .γ) (svT := .opt (.base .sig)) (ssvT := .base .ss) (rsvT := .base .rs)
  let esT := @prngEsTy KC Γ CCoins T I KR RSt K SS RS M E
  have hVp : prngVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K) =
      vpE := rfl
  rw [hVp]
  simp only [bind_map_left, eval_ret, Expr.eval, Expr.v0, Env.get_cons_zero,
    bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initPRNGRaw cka prng fs lam ⟨true, tL, t⟩ false)
    fun es₀ hes₀ => ?_
  have ⟨hInv₀, _⟩ := initPRNGRaw_inv cka prng fs lam ⟨true, tL, t⟩ false hqB hB1 hBB es₀ hes₀
  have hVR₀ := initPRNGRaw_vrInv (B := B_q) (qAdv := qAdv) cka prng fs lam ⟨true, tL, t⟩ false
    (fun k => hVRHk.mono (Nat.zero_le _) (hInitR k)) es₀ hes₀
  have ⟨hSim, hSimInv⟩ := Engine.simulateQ_implECDFPaper_vr_eq hDefaultE (fun _ => rfl) prngHsEnc
    (fun _ => True)
    (hooksPRNGC B ⟨true, tL, t⟩) (hooksPRNG cka prng fs ⟨true, tL, t⟩)
    L B_q (2 + Δcka) qep fs.maxSkip hHk hVRHk
    (modeCfgEC OO ⟨true, tL, t⟩) (⟨true, tL, t⟩ : Mode).cfg
    (modeCfgEC_agrees ⟨true, tL, t⟩)
    heqT heqM heqE (⟨true, tL, t⟩ : Mode).policy (fun _ _ _ _ _ _ => trivial) hA' es₀ trivial hInv₀
    hVR₀
  dsimp only [Expr.v0] at hSim
  rw [hSim, bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨b', es'⟩ hes' => ?_
  obtain ⟨_, hInv', _⟩ := hSimInv (b', es') hes'
  have hBnd' := hInv'.toBoundedEngine
  have hOut := authOutE_eval vpE prngHsEnc (O' := OO) L (2 + Δcka)
    (⟨true, tL, t⟩ : Mode).policy .v0
    (Env.cons (t := esT) (esEnc vpE prngHsEnc es')
      (Env.cons (t := (.bool : Ty S)) b' .nil))
    es' hBnd'.leaks_le hBnd'.corrs_le rfl
  dsimp only [Prod.map, id, Expr.v0, vpE, Mode.policy] at hOut ⊢
  rw [hOut]

theorem redPRNGAuthDFPaperProg_branch_eval_vr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    {VROkStep : ℕ → RS → Prop}
    (hInitA : ckaInitA = cka.initA)
    (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hVRHk : HooksVRInv VROkStep (hooksPRNG cka prng fs ⟨true, tL, t⟩))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q)
    (b_prng : Bool) :
    PRFPRNG.branch prng b_prng
      ((redPRNGAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep fs.maxSkip tL t).eval (fun _ => A) ()) =
      PRFPRNG.branch prng b_prng
        (DeliverForge.redPRNGAuthDFPaper cka prng fs lam Δcka qep tL t A) := by
  rw [redPRNGAuthDFPaperProg_eval_eq_bind_initPRNGRaw_vr cka prng fs L B B_q Δcka qep tL t
    hInitA hInitB hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT heqM heqE hDefaultE hSampKC hSampCCoins hVRHk hInitR hFsB hB1 hBB A qAdv hA hqB]
  unfold PRFPRNG.branch DeliverForge.redPRNGAuthDFPaper DeliverForge.authSimDFPaper
    DeliverForge.engRunDFPaper initPRNG initPRNGRaw
  refine bind_congr fun kr => ?_
  rw [StateT.run'_eq, StateT.run'_eq]
  refine congrArg (Prod.fst <$> ·) ?_
  simp only [StateT.run_bind, StateT.run_lift, simulateQ_bind, simulateQ_sampleT_run,
    bind_assoc, pure_bind]
  refine bind_congr fun kc => ?_
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨step, h₀⟩, sp⟩ hmem => ?_
  obtain ⟨σv, k, rfl, rfl⟩ := rootPRNG_zero_support_some (T := T) prng ⟨true, tL, t⟩ lam kr b_prng
    step h₀ sp hmem
  simp [StateT.run_pure, simulateQ_pure, Mode.policy]
  rfl

theorem redPRNGAuthDFPaperProg_eval_vr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    {VROkStep : ℕ → RS → Prop}
    (hInitA : ckaInitA = cka.initA)
    (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hVRHk : HooksVRInv VROkStep (hooksPRNG cka prng fs ⟨true, tL, t⟩))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    PRFPRNG.game prng
      ((redPRNGAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep fs.maxSkip tL t).eval (fun _ => A) ()) =
      PRFPRNG.game prng (DeliverForge.redPRNGAuthDFPaper cka prng fs lam Δcka qep tL t A) := by
  unfold PRFPRNG.game
  refine bind_congr fun b_prng => ?_
  have hBr := redPRNGAuthDFPaperProg_branch_eval_vr (prngInit := prngInit) (eqI := eqI) (lam := lam)
    (sampKR := sampKR) (sampI := sampI) (sampK := sampK)
    cka prng fs L B B_q Δcka qep tL t hInitA hInitB hSend hRecv hPrngUp
    hFsInitS hFsInitR hFsSend hFsRecv heqT heqM heqE hDefaultE hSampKC hSampCCoins
    hVRHk hInitR hFsB hB1 hBB A qAdv hA hqB b_prng
  unfold PRFPRNG.branch at hBr
  simp only [← bind_assoc]
  exact congrArg (· >>= fun b' => pure (b_prng == b')) hBr

theorem redPRNGAuthDFPaperProg_advantage_vr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    {VROkStep : ℕ → RS → Prop}
    (hInitA : ckaInitA = cka.initA)
    (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hVRHk : HooksVRInv VROkStep (hooksPRNG cka prng fs ⟨true, tL, t⟩))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    PRFPRNG.advantage prng
      ((redPRNGAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep fs.maxSkip tL t).eval (fun _ => A) ()) =
      PRFPRNG.advantage prng (DeliverForge.redPRNGAuthDFPaper cka prng fs lam Δcka qep tL t A) := by
  unfold PRFPRNG.advantage
  rw [redPRNGAuthDFPaperProg_eval_vr cka prng fs L B B_q Δcka qep tL t
    hInitA hInitB hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT heqM heqE hDefaultE hSampKC hSampCCoins hVRHk hInitR hFsB hB1 hBB A qAdv hA hqB]

@[simp] theorem redPRNGAuthDFPaperProg_totalQueries (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (t q : ℕ) :
    (redPRNGAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip tL t).totalQueries (fun _ => 1) (fun _ => 0) q = 2 + q * 2 := by
  simp [CostedReduction.totalQueries, redPRNGAuthDFPaperProg, Comp.queries]

end HooksPRNGCDFPaper

end CryptoGames.SM.Construction
