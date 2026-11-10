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
# Costed `redFSAuthDFPaperProg` Reduction

Deep-embedded `CostedReduction` formulation of `DeliverForge.redFSAuthDFPaper` with evaluation,
advantage, query, cost, size-honesty, and `fromAEADPRG` clamp theorems.
-/

@[expose] public section

open ReductionDsl OracleSpec OracleComp
open scoped Computational.Proofs.ReductionDsl.Notation

namespace CryptoGames.SM.Construction

open Engine Engine.RedPRNG CKA PRFPRNG

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "S" => ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "rrTy" => ckaRrTy KC Γ CCoins T I KR RSt K SS RS M E

section HooksFSCDFPaper

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
  fsaeadHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

local notation "hsTy" => fsHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hsEnc" => fsHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
local notation "hsDec" => fsHsDec (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
local notation "vpTyFS" => fsVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "vpEnc" =>
  fsVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K) (M := M) (E := E)
local notation "esTyFS" => fsEsTy KC Γ CCoins T I KR RSt K SS RS M E

theorem corrEPaper_hooksFSL_eq [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L : ℕ) (π : Policy) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (P : Party)
    (hvR : ∀ t, L ≤ t → (es.g.st P).vR t = none) :
    (DeliverForge.corrEPaper (hooksFSL cka prng fs L Δcka mo j) π P).run es =
      (DeliverForge.corrEPaper (hooksFS cka prng fs Δcka mo j) π P).run es := by
  unfold DeliverForge.corrEPaper
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases href : (es.abort || es.g.win || !es.g.corrAllowedPaper P)
  · simp [href]
  · simp only [href, Bool.false_eq_true, ↓reduceIte]
    by_cases hdoom : (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P)
    · simp [hdoom]
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
        hooksFSL_reveal_eq cka prng fs L Δcka mo j es.g P (es.g.st P) hvR]

theorem implEDFPaper_hooksFSL_eq [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (q : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hVR : ∀ P t, L ≤ t → (es.g.st P).vR t = none) :
    (DeliverForge.implEDFPaper (hooksFSL cka prng fs L Δcka mo j)
      Δ qep maxSkip cfg π (.inr q)).run es =
      (DeliverForge.implEDFPaper (hooksFS cka prng fs Δcka mo j)
        Δ qep maxSkip cfg π (.inr q)).run es := by
  rcases q with (t4 | P) | arg
  · exact implE_hooksFSL_eq cka prng fs L Δ qep maxSkip cfg π Δcka mo j es (.inl t4) hVR
  · exact corrEPaper_hooksFSL_eq cka prng fs L π Δcka mo j es P (hVR P)
  · change (DeliverForge.deliverForgeE (hooksFSL cka prng fs L Δcka mo j) Δ qep cfg arg).run es =
      (DeliverForge.deliverForgeE (hooksFS cka prng fs Δcka mo j) Δ qep cfg arg).run es
    rw [deliverForgeE_hooksFSL_eq]

theorem corrEPaper_fs_inv [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q : ℕ} (π : Policy) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (P : Party)
    (hInv : FSEngineInv L B (q + 1) es) :
    ∀ res ∈ support
      ((DeliverForge.corrEPaper (hooksFS cka prng fs Δcka mo j) π P).run es),
      FSEngineInv L B q res.2 := by
  intro ⟨out, es'⟩ hmem
  have hInvQ : FSEngineInv L B q es := hInv.mono (Nat.le_succ q)
  have hSm := corrEPaper_inv (hooksFS cka prng fs Δcka mo j) π es P hInv.sm (out, es') hmem
  unfold DeliverForge.corrEPaper abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases hdoom : (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P)
    · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩
      exact ⟨hSm, hInvQ.table_le, hInvQ.sessions_le, hInvQ.fsTrans_le,
        hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte] at hmem
      rw [run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, h'⟩, hrev, hmem⟩ := hmem
      have hPres := fsReveal_preserve cka prng fs Δcka mo j es.h es.g P (es.g.st P)
        (revRes, h') hrev
      rcases revRes with _ | st
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        exact ⟨hSm,
          by dsimp only; rw [hPres.1]; exact hInvQ.table_le,
          by dsimp only; rw [hPres.2.1]; exact hInvQ.sessions_le,
          by dsimp only; rw [hPres.2.2]; exact hInvQ.fsTrans_le,
          hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        exact ⟨hSm,
          by dsimp only; rw [hPres.1]; exact hInvQ.table_le,
          by dsimp only; rw [hPres.2.1]; exact hInvQ.sessions_le,
          by dsimp only; rw [hPres.2.2]; exact hInvQ.fsTrans_le,
          hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩

theorem implEDFPaper_fs_inv [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q Δ qep maxSkip : ℕ} (cfg : Config M) (π : Policy)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (q_df : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : FSEngineInv L B (q + 1) es) :
    ∀ res ∈ support
      ((DeliverForge.implEDFPaper (hooksFS cka prng fs Δcka mo j)
        Δ qep maxSkip cfg π (.inr q_df)).run es),
      FSEngineInv L B q res.2 := by
  rcases q_df with (t4 | P) | arg
  · exact implE_fs_inv cka prng fs cfg π Δcka mo j es (.inl t4) hInv
  · exact corrEPaper_fs_inv cka prng fs π Δcka mo j es P hInv
  · exact deliverForgeE_fs_inv cka prng fs cfg Δcka mo j es arg hInv

theorem simulateQ_implECDFPaper_fs_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (heqT : eqT = (· == ·))
    (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hFsRecvB : ∀ rs hdr e,
      (fsReceive rs hdr e).map (fun (rs', i, m) => (rs', min i B, m)) =
        fs.receive rs hdr e) :
    ∀ {α : Type}
      {oa : OracleComp (unifSpec + SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) α}
      {qAdv : ℕ},
      oa.IsQueryBoundP
        (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv →
      ∀ (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
          (FSState T RSt K I SS RS E)),
        FSEngineInv L B_q qAdv es →
        (simulateQ
          (handlerImpl (C := prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
            (implECDFPaper
              (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
                (sampI := sampI) (sampK := sampK) L B Δcka mo j)
              L (2 + Δcka) qep fs.maxSkip (modeCfgEC OO mo) mo.policy .v0 .v1)) oa).run
          (esEnc vpEnc hsEnc es) =
          (Prod.map id (esEnc vpEnc hsEnc) <$>
            (simulateQ (DeliverForge.implEDFPaper (hooksFS cka prng fs Δcka mo j)
              (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run es) ∧
        ∀ res ∈ support ((simulateQ (DeliverForge.implEDFPaper (hooksFS cka prng fs Δcka mo j)
            (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run es),
          FSEngineInv L B_q 0 res.2 ∧ res.2.g.b = es.g.b := by
  have hHk := hooksFSC_agrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (prngInit := prngInit) (eqM := eqM) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC)
    cka prng fs L B Δcka mo j hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend
    heqT heqI heqE hSampCCoins hSampI hSampK hFsRecvB
  let vpE := vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    (γvT := .base .γ) (svT := .base .sig)
    (ssvT := .opt (.base .ss)) (rsvT := .opt (.base .rs))
  have hVp : vpEnc = vpE := rfl
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qAdv _ es hInv
    refine ⟨by simp [simulateQ_pure, Prod.map], ?_⟩
    intro res hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨hInv.mono (Nat.zero_le qAdv), rfl⟩
  | query_bind q mx ih =>
    intro qAdv hq es hInv
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind]
    cases q with
    | inl n =>
      have hCoinL :
          ((handlerImpl (C := prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
            (implECDFPaper (hooksFSC (sampKR := sampKR) (sampKC := sampKC)
                (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka mo j)
              L (2 + Δcka) qep fs.maxSkip (modeCfgEC OO mo) mo.policy .v0 .v1)) (.inl n)).run
            (esEnc vpEnc hsEnc es) =
          (fun u => (u, esEnc vpEnc hsEnc es)) <$>
            query (spec := unifSpec + FSAEAD.spec SS RS (Header T) M E) (.inl n) := by
        simp [handlerImpl, StateT.run_lift, map_eq_bind_pure_comp]
      have hCoinR :
          (DeliverForge.implEDFPaper (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip
            mo.cfg mo.policy (.inl n)).run es =
          (fun u => (u, es)) <$>
            query (spec := unifSpec + FSAEAD.spec SS RS (Header T) M E) (.inl n) := by
        simp [DeliverForge.implEDFPaper, coinsE, StateT.run_lift, map_eq_bind_pure_comp]
      rw [hCoinL, hCoinR, bind_map_left, bind_map_left, map_bind]
      refine ⟨bind_congr fun u => (ih u (hq.2 u) es hInv).1, ?_⟩
      intro res hmem
      rw [mem_support_bind_iff] at hmem
      obtain ⟨u, _, hmem⟩ := hmem
      exact (ih u (hq.2 u) es hInv).2 res hmem
    | inr t =>
      have hpos : 0 < qAdv := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP
          (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) m := by
        intro u; simpa [isGameQuery] using hq.2 u
      have hHB : FSHBounded L es.h := hInv.toFSHBounded
      have hStepL := rdecDF_implECDFPaper_eval hDefaultE hsEnc (FSHBounded L)
        (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo j)
        (hooksFSL cka prng fs L Δcka mo j) hHk
        L (2 + Δcka) qep fs.maxSkip (modeCfgEC OO mo) mo.cfg (modeCfgEC_agrees mo)
        heqT heqM heqE mo.policy .v0 .v1
        (.cons (esEnc vpE hsEnc es)
          (.cons ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc t) .nil))
        es t hHB hInv.sm.toBoundedEngine (fun _ _ _ _ => trivial) rfl rfl
      rw [implEDFPaper_hooksFSL_eq cka prng fs L (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy
        Δcka mo j es t hInv.vR_none_of_le_L] at hStepL
      have hStep :
          ((handlerImpl (C := prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
            (implECDFPaper (hooksFSC (sampKR := sampKR) (sampKC := sampKC)
                (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka mo j)
              L (2 + Δcka) qep fs.maxSkip (modeCfgEC OO mo) mo.policy .v0 .v1)) (.inr t)).run
            (esEnc vpEnc hsEnc es) =
          Prod.map id (esEnc vpEnc hsEnc) <$>
            (DeliverForge.implEDFPaper (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip
              mo.cfg mo.policy (.inr t)).run es := by
        rw [hVp]
        dsimp only [vpE] at hStepL ⊢
        simp only [handlerImpl, StateT.run_mk, prngSMCodecDF, ← hStepL,
          map_eq_bind_pure_comp, Function.comp_def]
      rw [hStep, bind_map_left, map_bind]
      refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es₁⟩ hmem => ?_, ?_⟩
      · have hInv₁ := implEDFPaper_fs_inv cka prng fs mo.cfg mo.policy Δcka mo j es t
          hInv (u, es₁) hmem
        exact (ih u (hqm u) es₁ hInv₁).1
      · intro res hmem
        rw [mem_support_bind_iff] at hmem
        obtain ⟨⟨u, es₁⟩, hmem₁, hmem₂⟩ := hmem
        have hInv₁ := implEDFPaper_fs_inv cka prng fs mo.cfg mo.policy Δcka mo j es t
          hInv (u, es₁) hmem₁
        have hb₁ := implEDFPaper_b_eq (hooksFS cka prng fs Δcka mo j) mo.cfg mo.policy es t
          (u, es₁) hmem₁
        obtain ⟨hInv₂, hb₂⟩ := (ih u (hqm u) es₁ hInv₁).2 res hmem₂
        exact ⟨hInv₂, hb₂.trans hb₁⟩

def runFSDFPaper [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (Δcka qep : ℕ) (mo : Mode) (j : ℕ) (b : Bool)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) :
    FSAEAD.AdversaryComp SS RS (Header T) M E
      (Option (Bool × EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
        (FSState T RSt K I SS RS E))) :=
  DeliverForge.engRunDFPaper (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip
    mo.cfg mo.policy (initFS cka prng fs lam mo j) {} b A

theorem runFSDFPaper_eq_bind_initFSRaw
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (Δcka qep : ℕ) (mo : Mode) (j : ℕ) (b : Bool)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) :
    runFSDFPaper cka prng fs lam Δcka qep mo j b A =
      (do
        let es₀ ← initFSRaw cka prng fs lam mo j b
        let res ←
          (simulateQ (DeliverForge.implEDFPaper (hooksFS cka prng fs Δcka mo j)
            (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) A).run es₀
        pure (some res)) := by
  unfold runFSDFPaper DeliverForge.engRunDFPaper initFS initFSRaw
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
  refine bind_congr fun _ => bind_congr fun _ =>
    bind_congr fun ⟨⟨_, _, _⟩, _⟩ => bind_congr fun ⟨_, _⟩ => rfl

/-- Costed `DeliverForge.redFSAuthDFPaper` reduction over `SM.specDF`. -/
def redFSAuthDFPaperProg (L B Δcka qep maxSkip : ℕ) (j : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction OO II
      (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := esTyFS
  init := rdsl [_] do
    es ← initFSEStateC L (raw ⟨true, tL, t⟩) j false
    return ((), es)
  handle := rdsl [st, q] do
    implECDFPaper (raw (hooksFSC L B Δcka ⟨true, tL, t⟩ j)) L (raw (2 + Δcka)) qep maxSkip
      (raw (modeCfgEC OO ⟨true, tL, t⟩)) (raw (⟨true, tL, t⟩ : Mode).policy) st q
  finish := rdsl [_, _] do
    sample (O := OO) (I := II) CKASamp.bit ()

/-- Evaluation agreement for `redFSAuthDFPaperProg` against `fsClamp B fs`. -/
theorem redFSAuthDFPaperProg_eval_clamp
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (j : ℕ) (tL : Option ℕ) (t : ℕ)
    (hInitA : ckaInitA = cka.initA)
    (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngInit : prngInit = prng.init)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR))
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    (redFSAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep fs.maxSkip j tL t).eval (fun _ => A) () =
      DeliverForge.redFSAuthDFPaper cka prng (fsClamp B fs) lam Δcka qep j tL t A := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  have hBit : ∀ {Γ'} (ρ' : Env Γ'),
      (@Comp.sample _ _ _ OO II _ CKASamp.bit .unit).eval ρ' =
        (sampleT Bool : TComp (FSAEAD.spec SS RS (Header T) M E) Bool) := by
    intro Γ' ρ'
    simp only [Comp.eval, fsaeadHeaderAdIface, prngSamplers, ckaSamplers, sampleT]
    exact Engine.liftP_eq_liftM II (fun _ => rfl) ($ᵗ Bool)
  have hInit := initFSEStateC_eval (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampCCoins := sampCCoins)
    cka prng (fsClamp B fs) hInitA hInitB hPrngInit hPrngUp hFsInitS hFsInitR heqI
    hSampKR hSampKC hSampI hSampK L ⟨true, tL, t⟩ j (.bool false)
    (Env.cons (t := (.unit : Ty S)) () .nil)
  unfold CostedReduction.eval redFSAuthDFPaperProg CostedReduction.impl
    DeliverForge.redFSAuthDFPaper
  dsimp only
  change _ =
    (runFSDFPaper cka prng (fsClamp B fs) lam Δcka qep ⟨true, tL, t⟩ j false A >>=
      fun _ => sampleT Bool)
  rw [runFSDFPaper_eq_bind_initFSRaw, eval_bind, hInit]
  simp only [bind_map_left, eval_ret, Expr.eval, Expr.v0, Env.get_cons_zero,
    bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initFSRaw cka prng (fsClamp B fs) lam ⟨true, tL, t⟩ j false) fun es₀ hes₀ => ?_
  have ⟨hInv₀, _⟩ := initFSRaw_inv cka prng (fsClamp B fs) lam ⟨true, tL, t⟩ j false
    hqB hB1 hBB es₀ hes₀
  have ⟨hSim, _⟩ := simulateQ_implECDFPaper_fs_eq (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (prngInit := prngInit) (fsReceive := fsReceive) (lam := lam)
    (sampKR := sampKR) (sampKC := sampKC)
    cka prng (fsClamp B fs) L B B_q Δcka qep ⟨true, tL, t⟩ j
    hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend
    heqT heqI heqM heqE hDefaultE hSampCCoins hSampI hSampK
    (fun rs hdr e => by simp [fsClamp, hFsRecv]) hA' es₀ hInv₀
  have hms : (fsClamp B fs).maxSkip = fs.maxSkip := rfl
  dsimp only [Expr.v0] at hSim
  rw [hms] at hSim
  rw [hSim, bind_map_left]
  refine bind_congr fun ⟨b', es'⟩ => ?_
  exact hBit _

@[simp] theorem redFSAuthDFPaperProg_totalQueries (L B Δcka qep maxSkip : ℕ) (j : ℕ)
    (tL : Option ℕ) (t q : ℕ) :
    (redFSAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip j tL t).totalQueries (fun _ => 1) (fun _ => 0) q = q * 2 := by
  simp [CostedReduction.totalQueries, redFSAuthDFPaperProg, Comp.queries]

@[simp] theorem redFSAuthDFPaperProg_totalDecQueries (L B Δcka qep maxSkip : ℕ) (j : ℕ)
    (tL : Option ℕ) (t q : ℕ) :
    (redFSAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip j tL t).totalQueries fsHdrDecWt (fun _ => 0) q = q := by
  simp [CostedReduction.totalQueries, redFSAuthDFPaperProg, Comp.queries]

theorem redFSAuthDFPaperProg_queries (L B Δcka qep maxSkip : ℕ) (j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (q : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A q) :
    FSAEAD.MakesAtMostQueries
      ((redFSAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep maxSkip j tL t).eval (fun _ => A) ()) (2 * q) := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) q := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  have h := CostedReduction.queryBound_eval
    (redFSAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip j tL t)
    (isGameQuery (G := FSAEAD.spec SS RS (Header T) M E))
    (fun _ => 1) (fun _ => 0)
    (fun _ _ _ => le_rfl)
    (fun n => by simp [isGameQuery, isQueryBoundP_query_iff])
    (fun _ => A) q (fun _ => hA') ()
  rw [redFSAuthDFPaperProg_totalQueries, Nat.mul_comm] at h
  refine h.of_imp (fun x hx => ?_)
  rcases x with _ | _ <;> simp_all [isGameQuery]

theorem redFSAuthDFPaperProg_decQueries (L B Δcka qep maxSkip : ℕ) (j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (q : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A q) :
    FSAEAD.MakesAtMostDecQueries
      ((redFSAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep maxSkip j tL t).eval (fun _ => A) ()) q := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) q := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  have h := CostedReduction.queryBound_eval
    (redFSAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip j tL t)
    (fun t => FSAEAD.isDecQuery (SS := SS) (RS := RS) (AD := Header T) (Msg := M) (C := E) t = true)
    fsHdrDecWt (fun _ => 0)
    (fun g x hg => by cases g <;> simp_all [FSAEAD.isDecQuery, fsHdrDecWt])
    (fun n => (isQueryBoundP_query_iff
      (spec := unifSpec + FSAEAD.spec SS RS (Header T) M E) _ (.inl n) 0).2 (fun h => by cases h))
    (fun _ => A) q (fun _ => hA') ()
  rwa [redFSAuthDFPaperProg_totalDecQueries] at h

end HooksFSCDFPaper

section FromAEADPRGDFPaper

variable {MK C : Type}

theorem corrEPaper_fsClamp_eq [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (B Δcka : ℕ) (mo : Mode) (j : ℕ) :
    DeliverForge.corrEPaper (hooksFS cka prng (fsClamp B fs) Δcka mo j) =
      DeliverForge.corrEPaper (hooksFS cka prng fs Δcka mo j) := by
  unfold DeliverForge.corrEPaper hooksFS fsClamp
  rfl

theorem implEDFPaper_fsClamp_eq [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C]
    [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip B B_q q Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (hB : (B_q + 1) * (maxSkip + 1) ≤ B)
    (es : EState (VP Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK))) M (Header T × (ℕ × C))
      (FSState T RSt K I (FSAEAD.RatchetSenderState K)
        (FSAEAD.RatchetReceiverState K MK) (ℕ × C)))
    (t : (SM.specDF (PartyState Γ T RSt (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK)) M CCoins (Header T × (ℕ × C))).Domain)
    (hVR : SMVRInv (FSVROkStep maxSkip) B_q (q + 1) es.g)
    (hExt : FSVROkStep maxSkip (B_q - (q + 1)) (es.h.ext.map Prod.snd)) :
    (DeliverForge.implEDFPaper
        (hooksFS cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo j)
        (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr t)).run es =
      (DeliverForge.implEDFPaper
        (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
        (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr t)).run es := by
  rcases t with (t4 | P) | arg
  · exact implE_fsClamp_eq cka prng ae G maxSkip B B_q q Δcka qep mo j hB es (.inl t4) hVR hExt
  · change (DeliverForge.corrEPaper _ mo.policy P).run es =
      (DeliverForge.corrEPaper _ mo.policy P).run es
    rw [corrEPaper_fsClamp_eq]
  · exact deliverForgeE_fsClamp_eq cka prng ae G maxSkip B B_q q Δcka qep mo j hB es arg hVR hExt

theorem corrEPaper_ext_snd_fromAEADPRG [DecidableEq T] [DecidableEq I] [DecidableEq M]
    [DecidableEq C] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip k Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK))) M (Header T × (ℕ × C))
      (FSState T RSt K I (FSAEAD.RatchetSenderState K)
        (FSAEAD.RatchetReceiverState K MK) (ℕ × C)))
    (P : Party)
    (st : FSAEAD.State (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C))
    (hExt : FSVROkStep maxSkip k (es.h.ext.map Prod.snd))
    (hSt : RSReach maxSkip k st.receiverState) :
    ∀ z ∈ support
      ((simulateQ (fsFullImpl (FSAEAD.fromAEADPRG ae G maxSkip))
        ((DeliverForge.corrEPaper
          (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
          mo.policy P).run es)).run st),
      FSVROkStep maxSkip k (z.1.2.h.ext.map Prod.snd) := by
  intro z hz
  unfold DeliverForge.corrEPaper abortE at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
  · simp only [href, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz; exact hExt
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hz
    by_cases hdoom : (mo.policy.leakDoom es.g (es.g.afterCorr P) || mo.policy.corrDoom es.g P)
    · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hExt
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind] at hz
      simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨⟨⟨revRes, h'⟩, st'⟩, hrev, hz⟩ := hz
      have hExt' := fsReveal_ext_snd_fromAEADPRG cka prng ae G maxSkip k Δcka mo j
        es.g P (es.g.st P) es.h st hExt hSt ((revRes, h'), st') hrev
      rcases revRes with _ | stP <;>
        (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
           simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz;
         subst hz; exact hExt')

theorem implEDFPaper_ext_snd_fromAEADPRG [DecidableEq T] [DecidableEq I] [DecidableEq M]
    [DecidableEq C] [Inhabited C] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip k Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK))) M (Header T × (ℕ × C))
      (FSState T RSt K I (FSAEAD.RatchetSenderState K)
        (FSAEAD.RatchetReceiverState K MK) (ℕ × C)))
    (q : (SM.specDF (PartyState Γ T RSt (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK)) M CCoins (Header T × (ℕ × C))).Domain)
    (st : FSAEAD.State (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C))
    (hVR : ∀ P t₀ v, (es.g.st P).vR t₀ = some v → FSVROkStep maxSkip k v)
    (hExt : FSVROkStep maxSkip k (es.h.ext.map Prod.snd))
    (hSt : RSReach maxSkip k st.receiverState) :
    ∀ z ∈ support
      ((simulateQ (fsFullImpl (FSAEAD.fromAEADPRG ae G maxSkip))
        ((DeliverForge.implEDFPaper
          (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
          (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr q)).run es)).run st),
      FSVROkStep maxSkip (k + 1) (z.1.2.h.ext.map Prod.snd) := by
  intro z hz
  rcases q with (t4 | P) | arg
  · exact implE_ext_snd_fromAEADPRG cka prng ae G maxSkip k Δcka qep mo j es (.inl t4) st
      hVR hExt hSt z hz
  · exact (corrEPaper_ext_snd_fromAEADPRG cka prng ae G maxSkip k Δcka mo j es P st hExt hSt z
      hz).mono (Nat.le_succ k)
  · exact deliverForgeE_ext_snd cka prng ae G maxSkip k Δcka qep mo j es arg hVR hExt z.1
      (fst_mem_support_of_mem_support_simulateQ_run _ _ st hz)

theorem qb_corrEPaper_zero
    {Q : (ReductionsQueries.RSpec SS RS T M E).Domain → Prop} [DecidablePred Q]
    (hQcs : ¬ Q (.inr (.inl (.inl (.inl (.inr ()))))))
    (hQcr : ¬ Q (.inr (.inl (.inl (.inr ())))))
    [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (P : Party) :
    ReductionsQueries.QB Q (DeliverForge.corrEPaper (hooksFS cka prng fs Δcka mo j) mo.policy P)
      0 := by
  unfold DeliverForge.corrEPaper
  refine ReductionsQueries.qb_bind0 ReductionsQueries.qb_get fun es => ?_
  dsimp only
  split_ifs
  · exact ReductionsQueries.qb_pure none 0
  · exact ReductionsQueries.qb_bind0 ReductionsQueries.qb_abortE fun _ =>
      ReductionsQueries.qb_pure none 0
  · refine ReductionsQueries.qb_bind0
      (ReductionsQueries.qb_liftH
        (ReductionsQueries.qb_reveal_zero hQcs hQcr cka prng fs Δcka mo j es.g P (es.g.st P)))
      fun res => ?_
    cases res with
    | none => exact ReductionsQueries.qb_bind0 ReductionsQueries.qb_abortE fun _ =>
        ReductionsQueries.qb_pure none 0
    | some st => exact ReductionsQueries.qb_bind0 (ReductionsQueries.qb_modify _) fun _ =>
        ReductionsQueries.qb_pure (some st) 0

theorem qb_implEDFPaper_inr_one
    {Q : (ReductionsQueries.RSpec SS RS T M E).Domain → Prop} [DecidablePred Q]
    (hQu : ∀ u, ¬ Q (.inl u))
    (hQt : ∀ a m, ¬ Q (.inr (.inl (.inl (.inl (.inl (.inl (a, m))))))))
    (hQch : ∀ a m₀ m₁, ¬ Q (.inr (.inl (.inl (.inl (.inl (.inr (a, m₀, m₁))))))))
    (hQcs : ¬ Q (.inr (.inl (.inl (.inl (.inr ()))))))
    (hQcr : ¬ Q (.inr (.inl (.inl (.inr ())))))
    [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (t : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain) :
    ReductionsQueries.QB Q
      (DeliverForge.implEDFPaper (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip
        mo.cfg mo.policy (.inr t)) 1 := by
  rcases t with (t4 | P) | arg
  · exact ReductionsQueries.qb_implE_inr_one hQu hQt hQch hQcs hQcr
      cka prng fs Δcka qep mo j (.inl t4)
  · exact ReductionsQueries.qb_mono (qb_corrEPaper_zero hQcs hQcr cka prng fs Δcka mo j P)
      (by omega)
  · exact qb_deliverForgeE_one hQu cka prng fs Δcka qep mo j arg

theorem simulateQ_implEDFPaper_fsClamp_fromAEADPRG_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK))
    (fs₀ : FSAEADScheme K (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C))
    (L B B_q Δcka qep maxSkip : ℕ)
    (mo : Mode) (j : ℕ)
    (hfs₀ : fs₀ = FSAEAD.fromAEADPRG ae G maxSkip)
    (hB : (B_q + 1) * (maxSkip + 1) ≤ B)
    {α : Type} {oa : OracleComp (unifSpec + SM.specDF
      (PartyState Γ T RSt (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK))
      M CCoins (Header T × (ℕ × C))) α}
    {q : ℕ}
    (hoa : oa.IsQueryBoundP
      (isGameQuery (G := SM.specDF
        (PartyState Γ T RSt (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK))
        M CCoins (Header T × (ℕ × C)))) q)
    (es : EState (VP Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK))) M (Header T × (ℕ × C))
      (FSState T RSt K I (FSAEAD.RatchetSenderState K)
        (FSAEAD.RatchetReceiverState K MK) (ℕ × C)))
    (st : FSAEAD.State (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C))
    (hInv : SMEngineInv L B_q q es.g)
    (hVR : SMVRInv (FSVROkStep maxSkip) B_q q es.g)
    (hExt : FSVROkStep maxSkip (B_q - q) (es.h.ext.map Prod.snd))
    (hSt : RSReach maxSkip (B_q - q) st.receiverState) :
    (simulateQ (fsFullImpl fs₀)
      ((simulateQ (DeliverForge.implEDFPaper (hooksFS cka prng (fsClamp B fs₀) Δcka mo j)
        (2 + Δcka) qep maxSkip mo.cfg mo.policy) oa).run es)).run st =
    (simulateQ (fsFullImpl fs₀)
      ((simulateQ (DeliverForge.implEDFPaper (hooksFS cka prng fs₀ Δcka mo j)
        (2 + Δcka) qep maxSkip mo.cfg mo.policy) oa).run es)).run st := by
  subst hfs₀
  induction oa using OracleComp.inductionOn generalizing q es st with
  | pure x => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    rcases hoa with ⟨hq0, hmx⟩
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind,
      simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
    have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
        (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
    rw [hLift, hLift]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rcases qy with n | t_sm
    · simp only [isGameQuery, ↓reduceIte] at hmx
      have hInl1 :
          (DeliverForge.implEDFPaper
              (hooksFS cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo j)
              (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inl n)).run es =
            (coinsE n).run es := rfl
      have hInl2 :
          (DeliverForge.implEDFPaper
              (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
              (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inl n)).run es =
            (coinsE n).run es := rfl
      rw [hInl1, hInl2]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, st'⟩ hmem => ?_
      have hmem1 : (u, es') ∈ support ((coinsE n).run es) :=
        fst_mem_support_of_mem_support_simulateQ_run _ _ st hmem
      simp only [coinsE, StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
      obtain ⟨_, _, _, rfl⟩ := hmem1
      have hQbCoins : ((coinsE n).run es').IsQueryBoundP
          (ReductionsQueries.QFSDec (FSAEAD.RatchetSenderState K)
            (FSAEAD.RatchetReceiverState K MK) T M (ℕ × C)) 0 :=
        ReductionsQueries.qb_coinsE (ReductionsQueries.hQu_QFSDec _ _ T M (ℕ × C)) n es'
      have hSt' : RSReach maxSkip (B_q - q) st'.receiverState := by
        simpa using receiverState_reach_of_isDecQuery_bound ae G maxSkip hQbCoins st hSt
          ((u, es'), st') hmem
      exact ih u (hmx u) es' st' hInv hVR hExt hSt'
    · simp only [isGameQuery, ↓reduceIte] at hq0 hmx
      have hqp : 0 < q := hq0.resolve_left (by decide)
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have hStep :
          (DeliverForge.implEDFPaper
              (hooksFS cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo j)
              (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr t_sm)).run es =
            (DeliverForge.implEDFPaper
              (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
              (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr t_sm)).run es :=
        implEDFPaper_fsClamp_eq cka prng ae G maxSkip B B_q q' Δcka qep mo j hB es t_sm hVR hExt
      rw [hStep]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, st'⟩ hmem => ?_
      have hmem1 := fst_mem_support_of_mem_support_simulateQ_run _ _ st hmem
      have hInv' := implEDFPaper_inv
        (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
        mo.cfg mo.policy es t_sm hInv (u, es') hmem1
      have hVR' : SMVRInv (FSVROkStep maxSkip) B_q q' es'.g :=
        implEDFPaper_vrInv
          (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
          (hooksFS_vrInv_fromAEADPRG cka prng ae G maxSkip Δcka mo j)
          mo.cfg mo.policy es t_sm hInv hVR (u, es') hmem1
      have hBq : B_q - (q' + 1) + 1 ≤ B_q - q' := by have := hInv.1; omega
      have hExt' : FSVROkStep maxSkip (B_q - q') (es'.h.ext.map Prod.snd) :=
        (implEDFPaper_ext_snd_fromAEADPRG cka prng ae G maxSkip (B_q - (q' + 1)) Δcka qep mo j
          es t_sm st (fun P _ _ hv => hVR P _ _ hv) hExt hSt ((u, es'), st') hmem).mono hBq
      have hSt' : RSReach maxSkip (B_q - q') st'.receiverState := by
        have hQbStep :
            ((DeliverForge.implEDFPaper
              (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
              (2 + Δcka) qep (FSAEAD.fromAEADPRG ae G maxSkip).maxSkip
              mo.cfg mo.policy (.inr t_sm)).run es).IsQueryBoundP
              (ReductionsQueries.QFSDec (FSAEAD.RatchetSenderState K)
                (FSAEAD.RatchetReceiverState K MK) T M (ℕ × C)) 1 :=
          qb_implEDFPaper_inr_one
            (ReductionsQueries.hQu_QFSDec _ _ T M (ℕ × C))
            (ReductionsQueries.hQt_QFSDec _ _ T M (ℕ × C))
            (ReductionsQueries.hQch_QFSDec _ _ T M (ℕ × C))
            (ReductionsQueries.hQcs_QFSDec _ _ T M (ℕ × C))
            (ReductionsQueries.hQcr_QFSDec _ _ T M (ℕ × C))
            cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka qep mo j t_sm es
        exact (receiverState_reach_of_isDecQuery_bound ae G maxSkip hQbStep st hSt
          ((u, es'), st') hmem).mono hBq
      exact ih u (by simpa using hmx u) es' st' hInv' hVR' hExt' hSt'

theorem simulateQ_runFSDFPaper_fsClamp_fromAEADPRG
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip L B B_q Δcka qep : ℕ)
    (lam : I) (mo : Mode) (j : ℕ) (b : Bool)
    (hFsB : (B_q + 1) * (maxSkip + 1) ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK) M CCoins (ℕ × C)) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q)
    (st₀ : FSAEAD.State (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C))
    (hSt₀ : RSReach maxSkip 0 st₀.receiverState) :
    (simulateQ (fsFullImpl (FSAEAD.fromAEADPRG ae G maxSkip))
      (runFSDFPaper cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
        lam Δcka qep mo j b A)).run st₀ =
    (simulateQ (fsFullImpl (FSAEAD.fromAEADPRG ae G maxSkip))
      (runFSDFPaper cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
        lam Δcka qep mo j b A)).run st₀ := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.specDF
        (PartyState Γ T RSt (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK))
        M CCoins (Header T × (ℕ × C)))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  rw [runFSDFPaper_eq_bind_initFSRaw, runFSDFPaper_eq_bind_initFSRaw]
  have hInitEq :
      initFSRaw cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) lam mo j b =
        initFSRaw cka prng (FSAEAD.fromAEADPRG ae G maxSkip) lam mo j b := rfl
  rw [hInitEq, simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨es₀, st₁⟩ hmem₀ => ?_
  have hes₀ : es₀ ∈ support (initFSRaw cka prng (FSAEAD.fromAEADPRG ae G maxSkip) lam mo j b) :=
    fst_mem_support_of_mem_support_simulateQ_run _ _ st₀ hmem₀
  have ⟨hInv₀, _⟩ := initFSRaw_inv cka prng (FSAEAD.fromAEADPRG ae G maxSkip) lam mo j b
    hqB hB1 hBB es₀ hes₀
  have ⟨hVR₀, hext₀⟩ := initFSRaw_vrInv_fromAEADPRG cka prng ae G maxSkip lam mo j b
    B_q qAdv es₀ hes₀
  have hExt₀ : FSVROkStep maxSkip (B_q - qAdv) (es₀.h.ext.map Prod.snd) := by
    simp [hext₀, FSVROkStep]
  have hSt₁ : RSReach maxSkip (B_q - qAdv) st₁.receiverState :=
    (receiverState_reach_of_isDecQuery_bound ae G maxSkip
      (isQueryBoundP_initFSRaw_dec cka prng (FSAEAD.fromAEADPRG ae G maxSkip) lam mo j b)
      st₀ hSt₀ (es₀, st₁) hmem₀).mono (Nat.zero_le _)
  rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
  have hSim := simulateQ_implEDFPaper_fsClamp_fromAEADPRG_eq cka prng ae G
    (FSAEAD.fromAEADPRG ae G maxSkip) L B B_q Δcka qep maxSkip
    mo j rfl hFsB hA' es₀ st₁ hInv₀.sm hVR₀ hExt₀ hSt₁
  have hms1 : (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)).maxSkip = maxSkip := rfl
  have hms2 : (FSAEAD.fromAEADPRG ae G maxSkip).maxSkip = maxSkip := rfl
  rw [hms1, hms2, hSim]

end FromAEADPRGDFPaper

end CryptoGames.SM.Construction
