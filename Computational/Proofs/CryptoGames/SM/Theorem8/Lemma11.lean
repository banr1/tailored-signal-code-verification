/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux
import VCVio.OracleComp.EvalDist.Measure

/-!
# Proof of Lemma 11 (Theorem 8, hop H2 → FS-AEAD)

**Checked by Lean.**

Proves ACD19 §5.3.2 Lemma 11 (`lemma11` in `SM/Theorem8.lean`), reducing `localAuthAt j` in `H2`
to `redFSAuth j` in the FS-AEAD game by hoisting session `j`'s uniform key sample and coupling with
the FS-AEAD oracle simulation.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Construction.AuthL11

open CryptoGames.SM.Construction

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section HalfA

open Engine

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ) (mo : Mode)

local notation "LHM" => HM nilSpec (LState T Sig K I)

def lookupFLFixed (j : ℕ) (k_fs : K) (Ik : I) : LHM K := do
  let s ← get
  match s.table.lookup Ik with
  | some k => return k
  | none =>
    let k ← StateT.lift (sampleT K)
    let k_use := if s.sessions.length == j then k_fs else k
    modify fun s => { s with table := (Ik, k_use) :: s.table }
    return k_use

def rootLFixed (j : ℕ) (k_fs : K) (t : ℕ) (Ik : I) (σ : Sig) : LHM (Sig × K × Option I) := do
  if mo.tStar < t then
    let p := prng.up σ Ik
    return (p.1, p.2, none)
  else if t = mo.tStar then
    if mo.tL.isSome && t = mo.tH then
      let Ir ← StateT.lift (sampleT I)
      let k ← StateT.lift (sampleT K)
      let s ← get
      let k_use := if decide (Ir ∉ s.sessions) && (s.sessions.length == j) then k_fs else k
      return ((prng.up σ Ir).1, k_use, some Ir)
    else
      let k ← lookupFLFixed j k_fs Ik
      return ((prng.up σ Ik).1, k, some Ik)
  else if mo.tL.isSome && t = mo.tH then
    let Ir ← StateT.lift (sampleT I)
    let p := prng.up σ Ir
    return (p.1, p.2, none)
  else
    let p := prng.up σ Ik
    return (p.1, p.2, none)

def hooksLocalFixed (j : ℕ) (k_fs : K) :
    Hooks nilSpec (LState T Sig K I) Γ T Sig SS RS M E CCoins Γ Sig
      (SS × Option ℕ) (RS × Option ℕ) where
  startSend _ _ t γ σ r := do
    let coins ← match r with
      | some c => pure c
      | none => StateT.lift (sampleT CCoins)
    let c := cka.send γ coins
    let (σ', k, sid) ← rootLFixed prng mo j k_fs t c.2.2 σ
    let idx? ← regSessOf sid
    modify fun s => { s with cache := Function.update s.cache t (some (c.2.1, σ', k, idx?)) }
    return some (c.1, c.2.1, σ', (fs.initSender k, idx?))
  startRecv _ _ t γ σ Tn := do
    let honest := match (← get).cache t with
      | some (Tc, σc, k, idx?) => if Tc = Tn then some (σc, k, idx?) else none
      | none => none
    match honest with
    | some (σc, k, idx?) =>
      return some (some ((cka.receive γ Tn).1, σc, (fs.initReceiver k, idx?)))
    | none =>
      if mo.auth && t = mo.tStar then
        if mo.tL.isSome && mo.tStar = mo.tH then return none
        let kk := cka.receive γ Tn
        let k' ← lookupFLFixed j k_fs kk.2
        let idx ← regSess kk.2
        return some (some (kk.1, (prng.up σ kk.2).1, (fs.initReceiver k', some idx)))
      else return some none
  fsSend _ _ _ ssv h m _ := do
    let o := fs.send ssv.1 h m
    return some ((o.1, ssv.2), o.2)
  fsRecv _ _ _ rsv h e _ := do
    match fs.receive rsv.1 h e with
    | none => return some none
    | some (rs', i, m) =>
      modify fun s => { s with lastIdx := rsv.2 }
      return some (some ((rs', rsv.2), i, m))
  commit _ _ _ new := pure (some new)
  reveal _ _ vp := do
    return some (realParty vp vp.γ vp.root (vp.vS.map Prod.fst) (fun t => (vp.vR t).map Prod.fst))

def initLocalFixed (j : ℕ) (k_fs : K) :
    LHM (Option (PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ) ×
      PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ))) := do
  let kr ← StateT.lift (sampleT KR)
  let kc ← StateT.lift (sampleT KC)
  let (σ, k, sid) ← rootLFixed prng mo j k_fs 0 lam (prng.init kr)
  let idx? ← regSessOf sid
  return some (mkParties (cka.initA kc) (cka.initB kc) σ
    (fs.initSender k, idx?) (fs.initReceiver k, idx?))

def stepLFixed (j : ℕ) (k_fs : K) (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    ProbComp ((SMSpec Γ T Sig SS RS M CCoins E).Range q × EStateL Γ T Sig SS RS M E K I) :=
  simulateQ lImpl
    ((implE (hooksLocalFixed cka prng fs mo j k_fs) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy q).run
      esL)

def runLocAtFixed (j : ℕ) (k_fs : K) (oa : SMComp Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) : ProbComp Bool := do
  let r ← simulateQ lImpl
    ((simulateQ (implE (hooksLocalFixed cka prng fs mo j k_fs)
      (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run esL)
  pure (authOut (2 + Δcka) mo.policy r.2 && (r.2.h.lastIdx == some j))

/-- Local `H2` authenticity game restricted to session `j` with key fixed to `k_fs`. -/
def localAuthAtFixed (j : ℕ) (k_fs : K) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) : ProbComp Bool := do
  let mo : Mode := ⟨true, tL, t⟩
  let (vs, h) ← simulateQ lImpl ((initLocalFixed cka prng fs lam mo j k_fs).run {})
  match vs with
  | none => return false
  | some (vA, vB) =>
    let g : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := false }
    runLocAtFixed cka prng fs Δcka qep mo j k_fs A { g, h }

theorem runLocAtFixed_pure (j : ℕ) (k_fs : K) (b' : Bool) (esL : EStateL Γ T Sig SS RS M E K I) :
    runLocAtFixed cka prng fs Δcka qep mo j k_fs (pure b') esL =
      pure (authOut (2 + Δcka) mo.policy esL && (esL.h.lastIdx == some j)) := by
  simp [runLocAtFixed, map_eq_bind_pure_comp]

theorem runLocAtFixed_query_bind (j : ℕ) (k_fs : K)
    (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpec Γ T Sig SS RS M CCoins E).Range q → SMComp Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    runLocAtFixed cka prng fs Δcka qep mo j k_fs (liftM (OracleSpec.query q) >>= k) esL =
      stepLFixed cka prng fs Δcka qep mo j k_fs q esL >>= fun r =>
        runLocAtFixed cka prng fs Δcka qep mo j k_fs (k r.1) r.2 := by
  simp [runLocAtFixed, stepLFixed, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp,
    bind_assoc]

theorem stepLFixed_coinsE (j : ℕ) (k_fs : K) (n : unifSpec.Domain)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    stepLFixed cka prng fs Δcka qep mo j k_fs (.inl n) esL =
      (fun u => (u, esL)) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1))) := by
  simp [stepLFixed, implE, coinsE, lImpl, map_eq_bind_pure_comp, simulateQ_bind,
    simulateQ_query]

/-! ### Agreement after session `j` is created -/

theorem lookupFLFixed_eq_of_lt {j : ℕ} (k_fs : K) (Ik : I) {s : LState T Sig K I}
    (hlt : j < s.sessions.length) :
    (lookupFLFixed j k_fs Ik).run s = (lookupFL Ik).run s := by
  have hne : (s.sessions.length == j) = false := beq_eq_false_iff_ne.mpr (ne_of_gt hlt)
  unfold lookupFLFixed lookupFL
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases s.table.lookup Ik with
  | some k => rfl
  | none => simp only [hne, Bool.false_eq_true, ↓reduceIte]

theorem rootLFixed_eq_of_lt {j : ℕ} (k_fs : K) (t : ℕ) (Ik : I) (σ : Sig)
    {s : LState T Sig K I} (hlt : j < s.sessions.length) :
    (rootLFixed prng mo j k_fs t Ik σ).run s = (rootL prng mo t Ik σ).run s := by
  have hne : s.sessions.length ≠ j := ne_of_gt hlt
  unfold rootLFixed rootL
  split
  · rfl
  · split
    · split
      · simp [StateT.run_bind, StateT.run_get, hne]
      · simp [StateT.run_bind, lookupFLFixed_eq_of_lt k_fs Ik hlt]
    · rfl

theorem startSend_fixed_eq_of_lt {j : ℕ} (k_fs : K)
    (ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E)
    (P : Party) (t : ℕ) (γ : Γ) (σ : Sig) (r : Option CCoins)
    {s : LState T Sig K I} (hlt : j < s.sessions.length) :
    ((hooksLocalFixed cka prng fs mo j k_fs).startSend ctx P t γ σ r).run s =
      ((hooksLocal cka prng fs mo).startSend ctx P t γ σ r).run s := by
  cases r with
  | some c =>
    simp [hooksLocalFixed, hooksLocal, StateT.run_bind,
      rootLFixed_eq_of_lt prng mo k_fs t (cka.send γ c).2.2 σ hlt]
  | none =>
    simp [hooksLocalFixed, hooksLocal, StateT.run_bind,
      rootLFixed_eq_of_lt prng mo k_fs t _ σ hlt]

theorem vSend_fixed_eq_of_lt {j : ℕ} (k_fs : K)
    (ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E)
    (P : Party) (vp : VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ))
    (m : M) (pair : Option (M × M)) (r : Option CCoins)
    {s : LState T Sig K I} (hlt : j < s.sessions.length) :
    (vSend (hooksLocalFixed cka prng fs mo j k_fs) ctx P vp m pair r).run s =
      (vSend (hooksLocal cka prng fs mo) ctx P vp m pair r).run s := by
  unfold vSend
  split
  · rw [StateT.run_bind, StateT.run_bind,
      startSend_fixed_eq_of_lt cka prng fs mo k_fs ctx P (vp.tcur + 1) vp.γ vp.root r hlt]
    rfl
  · rfl

theorem startRecv_fixed_eq_of_lt {j : ℕ} (k_fs : K)
    (ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E)
    (P : Party) (t : ℕ) (γ : Γ) (σ : Sig) (Tn : T)
    {s : LState T Sig K I} (hlt : j < s.sessions.length) :
    ((hooksLocalFixed cka prng fs mo j k_fs).startRecv ctx P t γ σ Tn).run s =
      ((hooksLocal cka prng fs mo).startRecv ctx P t γ σ Tn).run s := by
  have hbranch :
      (if mo.auth && decide (t = mo.tStar) then
        if mo.tL.isSome && decide (mo.tStar = mo.tH) then pure none
        else do
          let kk := cka.receive γ Tn
          let k' ← lookupFLFixed j k_fs kk.2
          let idx ← regSess kk.2
          return some (some (kk.1, (prng.up σ kk.2).1, (fs.initReceiver k', some idx)))
      else pure (some none) :
        LHM (Option (Option (Γ × Sig × (RS × Option ℕ))))).run s =
      (if mo.auth && decide (t = mo.tStar) then
        if mo.tL.isSome && decide (mo.tStar = mo.tH) then pure none
        else do
          let kk := cka.receive γ Tn
          let k' ← lookupFL kk.2
          let idx ← regSess kk.2
          return some (some (kk.1, (prng.up σ kk.2).1, (fs.initReceiver k', some idx)))
      else pure (some none) :
        LHM (Option (Option (Γ × Sig × (RS × Option ℕ))))).run s := by
    split
    · split
      · rfl
      · simp [StateT.run_bind, lookupFLFixed_eq_of_lt k_fs (cka.receive γ Tn).2 hlt]
    · rfl
  simp only [hooksLocalFixed, hooksLocal, StateT.run_bind, StateT.run_get, pure_bind]
  cases s.cache t with
  | none => exact hbranch
  | some val =>
    rcases val with ⟨Tc, σc, k, idx?⟩
    by_cases hTc : Tc = Tn
    · simp [hTc]
    · simp only [hTc, ↓reduceIte]
      exact hbranch

theorem vRecv_fixed_eq_of_lt {j : ℕ} (k_fs : K)
    (ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E)
    (P : Party) (vp : VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ))
    (c : Header T × E) (rec : Option (SM.Record M (Header T × E)))
    {s : LState T Sig K I} (hlt : j < s.sessions.length) :
    (vRecv (hooksLocalFixed cka prng fs mo j k_fs) ctx P vp c rec).run s =
      (vRecv (hooksLocal cka prng fs mo) ctx P vp c rec).run s := by
  unfold vRecv
  dsimp only
  split
  · rfl
  · split
    · cases c.1.2 with
      | none => rfl
      | some Tn =>
        rw [StateT.run_bind, StateT.run_bind,
          startRecv_fixed_eq_of_lt cka prng fs mo k_fs ctx P c.1.1 vp.γ vp.root Tn hlt]
        rfl
    · rfl

theorem stepLFixed_eq_of_lt {j : ℕ} (k_fs : K)
    (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    {esL : EStateL Γ T Sig SS RS M E K I} (hlt : j < esL.h.sessions.length) :
    stepLFixed cka prng fs Δcka qep mo j k_fs q esL =
      stepL cka prng fs Δcka qep mo q esL := by
  rcases q with n | ((((q1 | q2) | q3) | q4) | P)
  · rw [stepLFixed_coinsE, stepL_coinsE]
  · rcases q1 with ⟨P, m, r_coins⟩
    simp only [stepLFixed, stepL, implE, QueryImpl.add_apply, transmitE, StateT.run_bind,
      StateT.run_get, pure_bind]
    split
    · rfl
    · cases esL.g.epMgmt (2 + Δcka) qep P r_coins.isSome with
      | none => rfl
      | some s₁ =>
        dsimp only
        split
        · rfl
        · simp [StateT.run_bind, run_liftH,
            vSend_fixed_eq_of_lt cka prng fs mo k_fs s₁ P (s₁.st P) m none r_coins hlt]
  · rcases q2 with ⟨P, m₀, m₁, r_coins⟩
    simp only [stepLFixed, stepL, implE, QueryImpl.add_apply, challE, StateT.run_bind,
      StateT.run_get, pure_bind]
    split
    · rfl
    · cases esL.g.epMgmt (2 + Δcka) qep P r_coins.isSome with
      | none => rfl
      | some s₁ =>
        dsimp only
        split
        · rfl
        · split
          · rfl
          · simp [StateT.run_bind, run_liftH,
              vSend_fixed_eq_of_lt cka prng fs mo k_fs s₁ P (s₁.st P) _ (some (m₀, m₁)) r_coins hlt]
  · rcases q3 with ⟨P, c⟩
    simp only [stepLFixed, stepL, implE, QueryImpl.add_apply, deliverE, StateT.run_bind,
      StateT.run_get, pure_bind]
    split
    · rfl
    · split
      · rfl
      · simp only [StateT.run_bind, run_liftH,
          vRecv_fixed_eq_of_lt cka prng fs mo k_fs esL.g P (esL.g.st P) c _ hlt]
        rfl
  · rcases q4 with ⟨P, c⟩
    simp only [stepLFixed, stepL, implE, QueryImpl.add_apply, injectE, StateT.run_bind,
      StateT.run_get, pure_bind]
    split
    · rfl
    · simp only [StateT.run_bind, run_liftH,
        vRecv_fixed_eq_of_lt cka prng fs mo k_fs esL.g P (esL.g.st P) c none hlt]
      rfl
  · simp [stepLFixed, stepL, implE, QueryImpl.add_apply, corrE, hooksLocalFixed, hooksLocal,
      StateT.run_bind, StateT.run_get, pure_bind, run_liftH]

theorem mem_support_startSend_sessions_le {ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E}
    {P : Party} {t : ℕ} {γ : Γ} {σ : Sig} {r : Option CCoins} {s : LState T Sig K I}
    {res : Option (Γ × T × Sig × (SS × Option ℕ))} {s' : LState T Sig K I}
    (h : (res, s') ∈ support (simulateQ lImpl
      (((hooksLocal cka prng fs mo).startSend ctx P t γ σ r).run s))) :
    s.sessions.length ≤ s'.sessions.length := by
  have hcoins : ∃ coins, (res, s') ∈ support (simulateQ lImpl
      (((hooksLocal cka prng fs mo).startSend ctx P t γ σ (some coins)).run s)) := by
    cases r with
    | some c => exact ⟨c, h⟩
    | none =>
      have hbind : ((hooksLocal cka prng fs mo).startSend ctx P t γ σ none).run s =
          ((StateT.lift (sampleT CCoins) : LHM CCoins).run s >>= fun p =>
            ((hooksLocal cka prng fs mo).startSend ctx P t γ σ (some p.1)).run p.2) := rfl
      rw [hbind, simulateQ_bind, simulateQ_lImpl_run_lift_sampleT] at h
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at h
      rcases h with ⟨_, ⟨c, _, rfl⟩, hc⟩
      exact ⟨c, hc⟩
  rcases hcoins with ⟨coins, h⟩
  simp only [hooksLocal, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
    simulateQ_bind, simulateQ_pure, MonadAttach.mem_support_bind, support_pure,
    Set.mem_singleton_iff] at h
  rcases h with ⟨⟨⟨σ', k, sid⟩, s₁⟩, hroot, ⟨idx?, s₂⟩, hreg, hpair⟩
  injection hpair with _ hs'; subst hs'
  obtain ⟨h1_sess, _⟩ := mem_support_rootL prng mo hroot
  obtain ⟨h2_none, h2_some⟩ := mem_support_regSessOf hreg
  cases sid with
  | none =>
    obtain ⟨_, hs₂⟩ := h2_none rfl
    subst hs₂; dsimp only; rw [h1_sess]
  | some Ik =>
    obtain ⟨_, hle, _⟩ := h2_some Ik rfl
    dsimp only at hle ⊢; rw [h1_sess] at hle; exact hle

theorem mem_support_vSend_sessions_le {ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E}
    {P : Party} {vp : VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ)} {m : M}
    {pair : Option (M × M)} {r : Option CCoins} {s : LState T Sig K I}
    {res : Option (VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ) × (Header T × E))}
    {s' : LState T Sig K I}
    (h : (res, s') ∈ support (simulateQ lImpl
      ((vSend (hooksLocal cka prng fs mo) ctx P vp m pair r).run s))) :
    s.sessions.length ≤ s'.sessions.length := by
  unfold vSend at h
  split at h
  · simp only [StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at h
    rcases h with ⟨⟨res_ss, s_ss⟩, hss, h2⟩
    have hl1 := mem_support_startSend_sessions_le cka prng fs mo hss
    cases res_ss with
    | none =>
      simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at h2
      injection h2 with _ hs'; subst hs'; exact hl1
    | some val =>
      rcases val with ⟨γ', T', σ', ss⟩
      simp only [hooksLocal, pure_bind, StateT.run_bind, StateT.run_pure, simulateQ_pure,
        support_pure, Set.mem_singleton_iff] at h2
      injection h2 with _ hs'; subst hs'; exact hl1
  · simp only [pure_bind] at h
    cases hvS : vp.vS with
    | none =>
      simp only [hvS, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at h
      injection h with _ hs'; subst hs'; exact le_rfl
    | some v =>
      simp only [hvS, hooksLocal, StateT.run_bind, StateT.run_pure, pure_bind, simulateQ_pure,
        support_pure, Set.mem_singleton_iff] at h
      injection h with _ hs'; subst hs'; exact le_rfl

theorem mem_support_startRecv_sessions_le {ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E}
    {P : Party} {t : ℕ} {γ : Γ} {σ : Sig} {Tn : T} {s : LState T Sig K I}
    {res : Option (Option (Γ × Sig × (RS × Option ℕ)))} {s' : LState T Sig K I}
    (h : (res, s') ∈ support (simulateQ lImpl
      (((hooksLocal cka prng fs mo).startRecv ctx P t γ σ Tn).run s))) :
    s.sessions.length ≤ s'.sessions.length := by
  simp only [hooksLocal, StateT.run_bind, StateT.run_get, pure_bind] at h
  cases hcache : s.cache t with
  | none =>
    simp only [hcache] at h
    split at h
    · split at h
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at h
        injection h with _ hs'; subst hs'; exact le_rfl
      · simp only [StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at h
        rcases h with ⟨⟨k', s₁⟩, hlk, ⟨idx, s₂⟩, hreg, hpair⟩
        injection hpair with _ hs'; subst hs'
        obtain ⟨h1_sess, _⟩ := mem_support_lookupFL hlk
        obtain ⟨_, h2_le, _⟩ := mem_support_regSess hreg
        dsimp only at h2_le ⊢; rw [h1_sess] at h2_le; exact h2_le
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at h
      injection h with _ hs'; subst hs'; exact le_rfl
  | some val =>
    rcases val with ⟨Tc, σc, k, idx?⟩
    simp only [hcache] at h
    split at h
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at h
      injection h with _ hs'; subst hs'; exact le_rfl
    · split at h
      · split at h
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at h
          injection h with _ hs'; subst hs'; exact le_rfl
        · simp only [StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
            MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at h
          rcases h with ⟨⟨k', s₁⟩, hlk, ⟨idx, s₂⟩, hreg, hpair⟩
          injection hpair with _ hs'; subst hs'
          obtain ⟨h1_sess, _⟩ := mem_support_lookupFL hlk
          obtain ⟨_, h2_le, _⟩ := mem_support_regSess hreg
          dsimp only at h2_le ⊢; rw [h1_sess] at h2_le; exact h2_le
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at h
        injection h with _ hs'; subst hs'; exact le_rfl

theorem mem_support_vRecv_sessions_le {ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E}
    {P : Party} {vp : VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ)} {c : Header T × E}
    {rec : Option (SM.Record M (Header T × E))} {s : LState T Sig K I}
    {res : Option (Option (VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ) × ℕ × ℕ × M))}
    {s' : LState T Sig K I}
    (h : (res, s') ∈ support (simulateQ lImpl
      ((vRecv (hooksLocal cka prng fs mo) ctx P vp c rec).run s))) :
    s.sessions.length ≤ s'.sessions.length := by
  unfold vRecv at h
  dsimp only at h
  split at h
  · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at h
    injection h with _ hs'; subst hs'; exact le_rfl
  · split at h
    · cases hc2 : c.1.2 with
      | none =>
        simp only [hc2, pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at h
        injection h with _ hs'; subst hs'; exact le_rfl
      | some Tn =>
        simp only [hc2, StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at h
        rcases h with ⟨⟨res_sr, s_sr⟩, hsr, h2⟩
        have hl1 := mem_support_startRecv_sessions_le cka prng fs mo hsr
        cases res_sr with
        | none =>
          simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at h2
          injection h2 with _ hs'; subst hs'; exact hl1
        | some res_sr' =>
          cases res_sr' with
          | none =>
            simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at h2
            injection h2 with _ hs'; subst hs'; exact hl1
          | some val =>
            rcases val with ⟨γ', σ', rs⟩
            simp only [pure_bind, Function.update_self, hooksLocal] at h2
            cases hfs : fs.receive rs.1 c.1 c.2 with
            | none =>
              simp only [hfs, pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at h2
              injection h2 with _ hs'; subst hs'; exact hl1
            | some out =>
              rcases out with ⟨rs', i, m⟩
              simp only [hfs, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at h2
              injection h2 with _ hs'; subst hs'; exact hl1
    · simp only [pure_bind] at h
      cases hvR : vp.vR c.1.1 with
      | none =>
        simp only [hvR, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at h
        injection h with _ hs'; subst hs'; exact le_rfl
      | some v =>
        simp only [hvR, hooksLocal] at h
        cases hfs : fs.receive v.1 c.1 c.2 with
        | none =>
          simp only [hfs, pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at h
          injection h with _ hs'; subst hs'; exact le_rfl
        | some out =>
          rcases out with ⟨rs', i, m⟩
          simp only [hfs, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at h
          injection h with _ hs'; subst hs'; exact le_rfl

theorem mem_support_stepL_sessions_le
    (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I)
    {r : (SMSpec Γ T Sig SS RS M CCoins E).Range q × EStateL Γ T Sig SS RS M E K I}
    (hr : r ∈ support (stepL cka prng fs Δcka qep mo q esL)) :
    esL.h.sessions.length ≤ r.2.h.sessions.length := by
  rcases q with n | ((((q1 | q2) | q3) | q4) | P)
  · rw [stepL_coinsE, support_map] at hr
    rcases hr with ⟨_, _, rfl⟩; exact le_rfl
  · rcases q1 with ⟨P, m, r_coins⟩
    simp only [stepL, implE, QueryImpl.add_apply, transmitE, StateT.run_bind, StateT.run_get,
      pure_bind] at hr
    split at hr
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact le_rfl
    · cases hep : esL.g.epMgmt (2 + Δcka) qep P r_coins.isSome with
      | none =>
        simp only [hep, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact le_rfl
      | some s₁ =>
        simp only [hep] at hr
        split at hr
        · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact le_rfl
        · simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind,
            MonadAttach.mem_support_bind] at hr
          rcases hr with ⟨⟨res_vs, h'⟩, hvs, hr2⟩
          have hl := mem_support_vSend_sessions_le cka prng fs mo hvs
          cases res_vs with
          | none =>
            simp only [abortE, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
            subst hr2; exact hl
          | some val =>
            rcases val with ⟨st', c⟩
            simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
            subst hr2; exact hl
  · rcases q2 with ⟨P, m₀, m₁, r_coins⟩
    simp only [stepL, implE, QueryImpl.add_apply, challE, StateT.run_bind, StateT.run_get,
      pure_bind] at hr
    split at hr
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact le_rfl
    · cases hep : esL.g.epMgmt (2 + Δcka) qep P r_coins.isSome with
      | none =>
        simp only [hep, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact le_rfl
      | some s₁ =>
        simp only [hep] at hr
        split at hr
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact le_rfl
        · split at hr
          · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact le_rfl
          · simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind,
              MonadAttach.mem_support_bind] at hr
            rcases hr with ⟨⟨res_vs, h'⟩, hvs, hr2⟩
            have hl := mem_support_vSend_sessions_le cka prng fs mo hvs
            cases res_vs with
            | none =>
              simp only [abortE, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
              subst hr2; exact hl
            | some val =>
              rcases val with ⟨st', c⟩
              simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
              subst hr2; exact hl
  · rcases q3 with ⟨P, c⟩
    simp only [stepL, implE, QueryImpl.add_apply, deliverE, StateT.run_bind, StateT.run_get,
      pure_bind] at hr
    split at hr
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact le_rfl
    · split at hr
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact le_rfl
      · simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind,
          MonadAttach.mem_support_bind] at hr
        rcases hr with ⟨⟨res_vr, h'⟩, hvr, hr2⟩
        have hl := mem_support_vRecv_sessions_le cka prng fs mo hvr
        cases res_vr with
        | none =>
          simp only [abortE, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
          subst hr2; exact hl
        | some res_vr' =>
          cases res_vr' with
          | none =>
            simp only [pure_bind] at hr2
            split at hr2
            · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
              subst hr2; exact hl
            · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hr2
              subst hr2; exact hl
          | some val =>
            rcases val with ⟨st', t', i', m'⟩
            simp only [commitE, hooksLocal, run_liftH, pure_bind, StateT.run_bind,
              StateT.run_pure, StateT.run_modify, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hr2
            subst hr2; exact hl
  · rcases q4 with ⟨P, c⟩
    simp only [stepL, implE, QueryImpl.add_apply, injectE, StateT.run_bind, StateT.run_get,
      pure_bind] at hr
    split at hr
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact le_rfl
    · simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind,
        MonadAttach.mem_support_bind] at hr
      rcases hr with ⟨⟨res_vr, h'⟩, hvr, hr2⟩
      have hl := mem_support_vRecv_sessions_le cka prng fs mo hvr
      cases res_vr with
      | none =>
        simp only [abortE, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
        subst hr2; exact hl
      | some res_vr' =>
        cases res_vr' with
        | none =>
          simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hr2
          subst hr2; exact hl
        | some val =>
          rcases val with ⟨st', t', i', m'⟩
          simp only [pure_bind] at hr2
          split at hr2
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
            subst hr2; exact hl
          · split at hr2
            · simp only [commitE, hooksLocal, run_liftH, pure_bind, StateT.run_bind,
                StateT.run_pure, StateT.run_modify, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hr2
              subst hr2; exact hl
            · split at hr2
              · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                  simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
                subst hr2; exact hl
              · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hr2
                subst hr2; exact hl
  · simp only [stepL, implE, QueryImpl.add_apply, corrE, StateT.run_bind, StateT.run_get,
      pure_bind] at hr
    split at hr
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact le_rfl
    · split at hr
      · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact le_rfl
      · simp only [hooksLocal, run_liftH, pure_bind, StateT.run_bind, StateT.run_pure,
          StateT.run_modify, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact le_rfl

theorem evalDist_runLocAt_eq_fixed_of_lt {j : ℕ} (k_fs : K)
    (oa : SMComp Γ T Sig SS RS M CCoins E Bool)
    {esL : EStateL Γ T Sig SS RS M E K I} (hlt : j < esL.h.sessions.length) :
    𝒟[runLocAt cka prng fs Δcka qep mo j oa esL] {true} =
      𝒟[runLocAtFixed cka prng fs Δcka qep mo j k_fs oa esL] {true} := by
  induction oa using OracleComp.inductionOn generalizing esL with
  | pure b' =>
    rw [runLocAt_pure, runLocAtFixed_pure]
  | query_bind q k ih =>
    rw [runLocAt_query_bind, runLocAtFixed_query_bind,
      stepLFixed_eq_of_lt cka prng fs Δcka qep mo k_fs q hlt]
    refine evalDist_bind_congr_true _ _ _ fun r hr => ?_
    exact ih r.1 (lt_of_lt_of_le hlt (mem_support_stepL_sessions_le cka prng fs Δcka qep mo q esL hr))

/-! ### `ShiftLe` key-hoisting coupling -/

def TabSessInv (s : LState T Sig K I) : Prop :=
  ¬ (mo.tL.isSome = true ∧ mo.tStar = mo.tH) →
    ∀ Ik, (s.table.lookup Ik).isSome = decide (Ik ∈ s.sessions)

/-- Relational coupling for shifting `k_fs ← $ᵗ K` from session `j`'s creation to the top level. -/
def ShiftLe {α : Type} (j : ℕ) (getH : α → LState T Sig K I)
    (mL : ProbComp α) (mF : K → ProbComp α) : Prop :=
  ∀ (contL : α → ProbComp Bool) (contF : K → α → ProbComp Bool),
    (∀ a, j < (getH a).sessions.length → ∀ k_fs, 𝒟[contL a] {true} ≤ 𝒟[contF k_fs a] {true}) →
    (∀ a, (getH a).sessions.length ≤ j → TabSessInv mo (getH a) →
      𝒟[contL a] {true} ≤ 𝒟[($ᵗ K : ProbComp K) >>= fun k_fs => contF k_fs a] {true}) →
    𝒟[mL >>= contL] {true} ≤
      𝒟[($ᵗ K : ProbComp K) >>= fun k_fs => mF k_fs >>= contF k_fs] {true}

theorem evalDist_bind_comm {α β : Type} (x : ProbComp α) (y : ProbComp β)
    (f : α → β → ProbComp Bool) :
    𝒟[x >>= fun a => y >>= fun b => f a b] {true} =
      𝒟[y >>= fun b => x >>= fun a => f a b] {true} := by
  rw [OracleComp.evalDist_bind_bind_swap x y f]

theorem ShiftLe.of_eq {α : Type} {j : ℕ} {getH : α → LState T Sig K I}
    {mL : ProbComp α} {mF : K → ProbComp α}
    (heq : ∀ k_fs, mF k_fs = mL)
    (hsupp : ∀ a ∈ support mL, (getH a).sessions.length ≤ j ∧ TabSessInv mo (getH a)) :
    ShiftLe (K := K) mo j getH mL mF := by
  intro contL contF _ h1
  simp only [heq]
  rw [evalDist_bind_comm ($ᵗ K) mL]
  exact evalDist_bind_mono mL _ _ fun a ha => h1 a (hsupp a ha).1 (hsupp a ha).2

theorem ShiftLe.pure {α : Type} {j : ℕ} {getH : α → LState T Sig K I}
    (a : α) {s : LState T Sig K I} (hle : s.sessions.length ≤ j) (hinv : TabSessInv mo s)
    (hs : (getH a).sessions = s.sessions ∧ (getH a).table = s.table := by exact ⟨rfl, rfl⟩) :
    ShiftLe (K := K) mo j getH (Pure.pure a) (fun _ => Pure.pure a) := by
  refine ShiftLe.of_eq mo (fun _ => rfl) ?_
  intro a' ha'
  simp only [support_pure, Set.mem_singleton_iff] at ha'
  subst ha'
  refine ⟨by rw [hs.1]; exact hle, fun hnot Ik => ?_⟩
  rw [hs.1, hs.2]
  exact hinv hnot Ik

theorem ShiftLe.sample_bind {α δ : Type} {j : ℕ} {getH : α → LState T Sig K I}
    (p : ProbComp δ) {fL : δ → ProbComp α} {fF : K → δ → ProbComp α}
    (hf : ∀ d ∈ support p, ShiftLe mo j getH (fL d) (fun k_fs => fF k_fs d)) :
    ShiftLe mo j getH (p >>= fL) (fun k_fs => p >>= fF k_fs) := by
  intro contL contF h2 h1
  simp only [bind_assoc]
  rw [evalDist_bind_comm ($ᵗ K) p]
  exact evalDist_bind_mono p _ _ fun d hd => hf d hd contL contF h2 h1

theorem ShiftLe.transition {α : Type} {j : ℕ} {getH : α → LState T Sig K I}
    (f : K → α) (hlt : ∀ k, j < (getH (f k)).sessions.length) :
    ShiftLe mo j getH (($ᵗ K : ProbComp K) >>= fun k => Pure.pure (f k))
      (fun k_fs => ($ᵗ K : ProbComp K) >>= fun _ => Pure.pure (f k_fs)) := by
  intro contL contF h2 _
  simp only [bind_assoc, pure_bind]
  have hrhs : 𝒟[($ᵗ K : ProbComp K) >>= fun k_fs => ($ᵗ K : ProbComp K) >>= fun _ => contF k_fs (f k_fs)] {true} =
      𝒟[($ᵗ K : ProbComp K) >>= fun k_fs => contF k_fs (f k_fs)] {true} := by
    refine evalDist_bind_congr_true ($ᵗ K) _ _ fun k_fs _ => ?_
    rw [OracleComp.evalDist_bind_const]
  rw [hrhs]
  exact evalDist_bind_mono ($ᵗ K) _ _ fun k _ => h2 (f k) (hlt k) k

theorem ShiftLe.post {α β : Type} {j : ℕ}
    {getH₁ : α → LState T Sig K I} {getH₂ : β → LState T Sig K I}
    {mL : ProbComp α} {mF : K → ProbComp α}
    (hm : ShiftLe mo j getH₁ mL mF)
    (f : α → ProbComp β)
    (hpres : ∀ a, ∀ b ∈ support (f a),
      (getH₂ b).sessions = (getH₁ a).sessions ∧ (getH₂ b).table = (getH₁ a).table) :
    ShiftLe mo j getH₂ (mL >>= f) (fun k_fs => mF k_fs >>= f) := by
  intro contL contF h2 h1
  simp only [bind_assoc]
  refine hm (fun a => f a >>= contL) (fun k_fs a => f a >>= contF k_fs) ?_ ?_
  · intro a hlt k_fs
    refine evalDist_bind_mono (f a) _ _ fun b hb => ?_
    have hlt_b : j < (getH₂ b).sessions.length := by
      rw [(hpres a b hb).1]; exact hlt
    exact h2 b hlt_b k_fs
  · intro a hle hinv
    rw [evalDist_bind_comm ($ᵗ K) (f a)]
    refine evalDist_bind_mono (f a) _ _ fun b hb => ?_
    obtain ⟨hsess, htab⟩ := hpres a b hb
    have hle_b : (getH₂ b).sessions.length ≤ j := by rw [hsess]; exact hle
    have hinv_b : TabSessInv mo (getH₂ b) := by
      intro hnot Ik
      rw [htab, hsess]
      exact hinv hnot Ik
    exact h1 b hle_b hinv_b

theorem tabSessInv_insert {s : LState T Sig K I} (hinv : TabSessInv mo s)
    (Ik : I) (k : K) :
    TabSessInv mo { s with table := (Ik, k) :: s.table, sessions := s.sessions ++ [Ik] } := by
  intro hnot Ik'
  dsimp only [List.lookup]
  by_cases heq : (Ik' == Ik) = true
  · have heq' : Ik' = Ik := beq_iff_eq.mp heq
    subst heq'
    simp [heq]
  · simp only [heq, List.mem_append, List.mem_singleton, hinv hnot Ik']
    have hne : Ik' ≠ Ik := fun h => by subst h; simp at heq
    simp [hne]

theorem shiftLe_lookupFL_regSess {j : ℕ} (Ik : I) {s : LState T Sig K I}
    (hle : s.sessions.length ≤ j) (hinv : TabSessInv mo s)
    (hnot_th : ¬ (mo.tL.isSome = true ∧ mo.tStar = mo.tH)) :
    ShiftLe mo j Prod.snd
      (simulateQ lImpl (((lookupFL Ik >>= fun k => regSess Ik >>= fun idx => pure (k, idx)) :
        LHM (K × ℕ)).run s))
      (fun k_fs => simulateQ lImpl
        (((lookupFLFixed j k_fs Ik >>= fun k => regSess Ik >>= fun idx => pure (k, idx)) :
          LHM (K × ℕ)).run s)) := by
  have htab_iff := hinv hnot_th Ik
  simp only [lookupFL, lookupFLFixed, regSess, StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hmem : Ik ∈ s.sessions
  · have hsome : (s.table.lookup Ik).isSome = true := by simpa [hmem] using htab_iff
    obtain ⟨k₀, hlk⟩ := Option.isSome_iff_exists.mp hsome
    simp only [hlk, pure_bind, StateT.run_get, hmem, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact ShiftLe.pure mo ((k₀, s.sessions.idxOf Ik), s) hle hinv
  · have hnone : s.table.lookup Ik = none := by
      cases h : s.table.lookup Ik with
      | none => rfl
      | some v => simp [h, hmem] at htab_iff
    simp only [hnone, StateT.run_bind, StateT.run_modify, StateT.run_get, pure_bind, hmem,
      ↓reduceIte, StateT.run_set, StateT.run_pure, simulateQ_bind,
      simulateQ_lImpl_run_lift_sampleT, simulateQ_pure, bind_assoc]
    by_cases hlen_eq : s.sessions.length = j
    · subst hlen_eq
      simp only [beq_self_eq_true, ↓reduceIte]
      refine ShiftLe.transition (getH := Prod.snd) mo
        (fun (k : K) => ((k, s.sessions.length),
          { s with table := (Ik, k) :: s.table, sessions := s.sessions ++ [Ik] })) ?_
      intro k
      dsimp only
      rw [List.length_append, List.length_singleton]
      exact Nat.lt_succ_self _
    · have hlt : s.sessions.length < j := Nat.lt_of_le_of_ne hle hlen_eq
      have hbeq : (s.sessions.length == j) = false := beq_eq_false_iff_ne.mpr hlen_eq
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      refine ShiftLe.sample_bind mo ($ᵗ K) fun k _ => ?_
      refine ShiftLe.pure (getH := Prod.snd) mo ((k, s.sessions.length),
        { s with table := (Ik, k) :: s.table, sessions := s.sessions ++ [Ik] }) ?_
        (tabSessInv_insert mo hinv Ik k)
      dsimp only
      rw [List.length_append, List.length_singleton]
      omega

theorem shiftLe_rootL_regSessOf {j : ℕ} (t : ℕ) (Ik : I) (σ : Sig) {s : LState T Sig K I}
    (hle : s.sessions.length ≤ j) (hinv : TabSessInv mo s) :
    ShiftLe mo j Prod.snd
      (simulateQ lImpl (((rootL prng mo t Ik σ >>= fun (σ', k, sid) =>
        regSessOf sid >>= fun idx? => pure (σ', k, idx?)) :
          LHM (Sig × K × Option ℕ)).run s))
      (fun k_fs => simulateQ lImpl (((rootLFixed prng mo j k_fs t Ik σ >>= fun (σ', k, sid) =>
        regSessOf sid >>= fun idx? => pure (σ', k, idx?)) :
          LHM (Sig × K × Option ℕ)).run s)) := by
  unfold rootL rootLFixed
  by_cases hgt : mo.tStar < t
  · simp only [hgt, ↓reduceIte, regSessOf, StateT.run_bind, StateT.run_pure, pure_bind,
      simulateQ_pure]
    exact ShiftLe.pure (getH := Prod.snd) mo (((prng.up σ Ik).1, (prng.up σ Ik).2, none), s) hle hinv
  · simp only [hgt, ↓reduceIte]
    by_cases heq : t = mo.tStar
    · subst heq
      simp only [↓reduceIte]
      by_cases hth : (mo.tL.isSome && decide (mo.tStar = mo.tH)) = true
      · simp only [hth, ↓reduceIte, regSessOf, regSess, StateT.run_bind, StateT.run_get,
          StateT.run_map, StateT.run_pure, pure_bind, simulateQ_bind,
          simulateQ_lImpl_run_lift_sampleT, simulateQ_pure, bind_assoc]
        have hinv_any : ∀ s' : LState T Sig K I, TabSessInv mo s' := by
          intro s' hnot
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hth
          exact False.elim (hnot hth)
        refine ShiftLe.sample_bind mo ($ᵗ I) fun Ir _ => ?_
        by_cases hmem : Ir ∈ s.sessions
        · simp only [hmem, not_true_eq_false, decide_false, Bool.false_and, Bool.false_eq_true,
            ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
          refine ShiftLe.sample_bind mo ($ᵗ K) fun k _ => ?_
          exact ShiftLe.pure (getH := Prod.snd) mo
            (((prng.up σ Ir).1, k, some (s.sessions.idxOf Ir)), s) hle (hinv_any s)
        · simp only [hmem, not_false_eq_true, decide_true, Bool.true_and, ↓reduceIte,
            StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind]
          by_cases hlen_eq : s.sessions.length = j
          · subst hlen_eq
            simp only [beq_self_eq_true, ↓reduceIte]
            refine ShiftLe.transition (getH := Prod.snd) mo
              (fun (k : K) => (((prng.up σ Ir).1, k, some s.sessions.length),
                { s with sessions := s.sessions ++ [Ir] })) ?_
            intro k
            dsimp only
            rw [List.length_append, List.length_singleton]
            exact Nat.lt_succ_self _
          · have hlt : s.sessions.length < j := Nat.lt_of_le_of_ne hle hlen_eq
            have hbeq : (s.sessions.length == j) = false := beq_eq_false_iff_ne.mpr hlen_eq
            simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
            refine ShiftLe.sample_bind mo ($ᵗ K) fun k _ => ?_
            refine ShiftLe.pure (getH := Prod.snd) mo
              (((prng.up σ Ir).1, k, some s.sessions.length),
                { s with sessions := s.sessions ++ [Ir] }) ?_ (hinv_any _)
            dsimp only
            rw [List.length_append, List.length_singleton]
            omega
      · simp only [hth, Bool.false_eq_true, ↓reduceIte]
        have hnot_th : ¬ (mo.tL.isSome = true ∧ mo.tStar = mo.tH) := by
          intro ⟨h1, h2⟩; simp [h1, h2] at hth
        have hbindL : StateT.run (((lookupFL Ik >>= fun k => pure ((prng.up σ Ik).1, k, some Ik)) >>=
            fun x => regSessOf x.2.2 >>= fun idx? => pure (x.1, x.2.1, idx?)) :
              LHM (Sig × K × Option ℕ)) s =
          (((lookupFL Ik >>= fun k => regSess Ik >>= fun idx => pure (k, idx)) :
            LHM (K × ℕ)).run s >>= fun r =>
              pure (((prng.up σ Ik).1, r.1.1, some r.1.2), r.2)) := by
          simp only [regSessOf, StateT.run_bind, StateT.run_map, StateT.run_pure, pure_bind,
            map_eq_bind_pure_comp, bind_assoc, Function.comp_apply]
        have hbindF : ∀ k_fs, StateT.run (((lookupFLFixed j k_fs Ik >>= fun k => pure ((prng.up σ Ik).1, k, some Ik)) >>=
            fun x => regSessOf x.2.2 >>= fun idx? => pure (x.1, x.2.1, idx?)) :
              LHM (Sig × K × Option ℕ)) s =
          (((lookupFLFixed j k_fs Ik >>= fun k => regSess Ik >>= fun idx => pure (k, idx)) :
            LHM (K × ℕ)).run s >>= fun r =>
              pure (((prng.up σ Ik).1, r.1.1, some r.1.2), r.2)) := by
          intro k_fs
          simp only [regSessOf, StateT.run_bind, StateT.run_map, StateT.run_pure, pure_bind,
            map_eq_bind_pure_comp, bind_assoc, Function.comp_apply]
        simp only [hbindL, hbindF, simulateQ_bind, simulateQ_pure]
        refine (shiftLe_lookupFL_regSess mo Ik hle hinv hnot_th).post mo _ ?_
        intro a b hb
        simp only [support_pure, Set.mem_singleton_iff] at hb
        subst hb; exact ⟨rfl, rfl⟩
    · simp only [heq, ↓reduceIte]
      split
      · simp only [regSessOf, StateT.run_bind, StateT.run_pure, pure_bind, simulateQ_bind,
          simulateQ_lImpl_run_lift_sampleT, simulateQ_pure, bind_assoc]
        refine ShiftLe.sample_bind mo ($ᵗ I) fun Ir _ => ?_
        exact ShiftLe.pure mo (((prng.up σ Ir).1, (prng.up σ Ir).2, none), s) hle hinv
      · simp only [regSessOf, StateT.run_bind, StateT.run_pure, pure_bind, simulateQ_pure]
        exact ShiftLe.pure mo (((prng.up σ Ik).1, (prng.up σ Ik).2, none), s) hle hinv

theorem shiftLe_initLocal {j : ℕ} {s : LState T Sig K I}
    (hle : s.sessions.length ≤ j) (hinv : TabSessInv mo s) :
    ShiftLe mo j Prod.snd
      (simulateQ lImpl ((initLocal cka prng fs lam mo).run s))
      (fun k_fs => simulateQ lImpl ((initLocalFixed cka prng fs lam mo j k_fs).run s)) := by
  have hbindL : (initLocal cka prng fs lam mo).run s =
      ((StateT.lift (sampleT KR) : LHM KR).run s >>= fun p1 =>
        (StateT.lift (sampleT KC) : LHM KC).run p1.2 >>= fun p2 =>
          ((rootL prng mo 0 lam (prng.init p1.1) >>= fun (σ, k, sid) =>
            regSessOf sid >>= fun idx? => pure (σ, k, idx?)) :
              LHM (Sig × K × Option ℕ)).run p2.2 >>= fun r =>
            pure (some (mkParties (cka.initA p2.1) (cka.initB p2.1) r.1.1
              (fs.initSender r.1.2.1, r.1.2.2) (fs.initReceiver r.1.2.1, r.1.2.2)), r.2)) := by
    simp [initLocal, StateT.run_bind, bind_assoc]
  have hbindF : ∀ k_fs, (initLocalFixed cka prng fs lam mo j k_fs).run s =
      ((StateT.lift (sampleT KR) : LHM KR).run s >>= fun p1 =>
        (StateT.lift (sampleT KC) : LHM KC).run p1.2 >>= fun p2 =>
          ((rootLFixed prng mo j k_fs 0 lam (prng.init p1.1) >>= fun (σ, k, sid) =>
            regSessOf sid >>= fun idx? => pure (σ, k, idx?)) :
              LHM (Sig × K × Option ℕ)).run p2.2 >>= fun r =>
            pure (some (mkParties (cka.initA p2.1) (cka.initB p2.1) r.1.1
              (fs.initSender r.1.2.1, r.1.2.2) (fs.initReceiver r.1.2.1, r.1.2.2)), r.2)) := by
    intro k_fs
    simp [initLocalFixed, StateT.run_bind, bind_assoc]
  simp only [hbindL, hbindF, simulateQ_bind, simulateQ_lImpl_run_lift_sampleT, simulateQ_pure,
    bind_assoc, pure_bind]
  refine ShiftLe.sample_bind mo ($ᵗ KR) fun kr _ => ?_
  refine ShiftLe.sample_bind mo ($ᵗ KC) fun kc _ => ?_
  refine (shiftLe_rootL_regSessOf prng mo 0 lam (prng.init kr) hle hinv).post mo _ ?_
  intro a b hb
  simp only [support_pure, Set.mem_singleton_iff] at hb
  subst hb; exact ⟨rfl, rfl⟩

theorem shiftLe_startSend {j : ℕ}
    (ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E)
    (P : Party) (t : ℕ) (γ : Γ) (σ : Sig) (r : Option CCoins)
    {s : LState T Sig K I} (hle : s.sessions.length ≤ j) (hinv : TabSessInv mo s) :
    ShiftLe mo j Prod.snd
      (simulateQ lImpl (((hooksLocal cka prng fs mo).startSend ctx P t γ σ r).run s))
      (fun k_fs => simulateQ lImpl
        (((hooksLocalFixed cka prng fs mo j k_fs).startSend ctx P t γ σ r).run s)) := by
  have hsome : ∀ coins : CCoins,
      ShiftLe mo j Prod.snd
        (simulateQ lImpl (((hooksLocal cka prng fs mo).startSend ctx P t γ σ (some coins)).run s))
        (fun k_fs => simulateQ lImpl
          (((hooksLocalFixed cka prng fs mo j k_fs).startSend ctx P t γ σ (some coins)).run s)) := by
    intro coins
    let c := cka.send γ coins
    have hbindL : ((hooksLocal cka prng fs mo).startSend ctx P t γ σ (some coins)).run s =
        (((rootL prng mo t c.2.2 σ >>= fun (σ', k, sid) =>
          regSessOf sid >>= fun idx? => pure (σ', k, idx?)) :
            LHM (Sig × K × Option ℕ)).run s >>= fun r =>
          pure (some (c.1, c.2.1, r.1.1, (fs.initSender r.1.2.1, r.1.2.2)),
            { r.2 with cache := Function.update r.2.cache t (some (c.2.1, r.1.1, r.1.2.1, r.1.2.2)) })) := by
      simp [c, hooksLocal, StateT.run_bind, StateT.run_modify, bind_assoc]
    have hbindF : ∀ k_fs,
        ((hooksLocalFixed cka prng fs mo j k_fs).startSend ctx P t γ σ (some coins)).run s =
        (((rootLFixed prng mo j k_fs t c.2.2 σ >>= fun (σ', k, sid) =>
          regSessOf sid >>= fun idx? => pure (σ', k, idx?)) :
            LHM (Sig × K × Option ℕ)).run s >>= fun r =>
          pure (some (c.1, c.2.1, r.1.1, (fs.initSender r.1.2.1, r.1.2.2)),
            { r.2 with cache := Function.update r.2.cache t (some (c.2.1, r.1.1, r.1.2.1, r.1.2.2)) })) := by
      intro k_fs
      simp [c, hooksLocalFixed, StateT.run_bind, StateT.run_modify, bind_assoc]
    simp only [hbindL, hbindF, simulateQ_bind, simulateQ_pure]
    refine (shiftLe_rootL_regSessOf prng mo t c.2.2 σ hle hinv).post mo _ ?_
    intro a b hb
    simp only [support_pure, Set.mem_singleton_iff] at hb
    subst hb; exact ⟨rfl, rfl⟩
  cases r with
  | some c => exact hsome c
  | none =>
    have hbindL : ((hooksLocal cka prng fs mo).startSend ctx P t γ σ none).run s =
        ((StateT.lift (sampleT CCoins) : LHM CCoins).run s >>= fun p =>
          ((hooksLocal cka prng fs mo).startSend ctx P t γ σ (some p.1)).run p.2) := rfl
    have hbindF : ∀ k_fs,
        ((hooksLocalFixed cka prng fs mo j k_fs).startSend ctx P t γ σ none).run s =
        ((StateT.lift (sampleT CCoins) : LHM CCoins).run s >>= fun p =>
          ((hooksLocalFixed cka prng fs mo j k_fs).startSend ctx P t γ σ (some p.1)).run p.2) :=
      fun _ => rfl
    rw [hbindL, simulateQ_bind, simulateQ_lImpl_run_lift_sampleT]
    simp only [hbindF, simulateQ_bind, simulateQ_lImpl_run_lift_sampleT, bind_assoc, pure_bind]
    exact ShiftLe.sample_bind mo ($ᵗ CCoins) fun c _ => hsome c

theorem shiftLe_vSend {j : ℕ}
    (ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E)
    (P : Party) (vp : VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ))
    (m : M) (pair : Option (M × M)) (r : Option CCoins)
    {s : LState T Sig K I} (hle : s.sessions.length ≤ j) (hinv : TabSessInv mo s) :
    ShiftLe mo j Prod.snd
      (simulateQ lImpl ((vSend (hooksLocal cka prng fs mo) ctx P vp m pair r).run s))
      (fun k_fs => simulateQ lImpl
        ((vSend (hooksLocalFixed cka prng fs mo j k_fs) ctx P vp m pair r).run s)) := by
  unfold vSend
  split
  · simp only [StateT.run_bind, simulateQ_bind]
    have hss := shiftLe_startSend cka prng fs mo ctx P (vp.tcur + 1) vp.γ vp.root r hle hinv
    change ShiftLe mo j Prod.snd
      (simulateQ lImpl (((hooksLocal cka prng fs mo).startSend ctx P (vp.tcur + 1) vp.γ vp.root r).run s) >>= _)
      (fun k_fs => simulateQ lImpl (((hooksLocalFixed cka prng fs mo j k_fs).startSend ctx P (vp.tcur + 1) vp.γ vp.root r).run s) >>= _)
    refine hss.post mo _ ?_
    intro a b hb
    rcases a with ⟨res_ss, s_ss⟩
    cases res_ss with
    | none =>
      simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hb
      subst hb; exact ⟨rfl, rfl⟩
    | some val =>
      rcases val with ⟨γ', T', σ', ss⟩
      simp only [hooksLocal, pure_bind, StateT.run_bind, StateT.run_pure, simulateQ_pure,
        support_pure, Set.mem_singleton_iff] at hb
      subst hb; exact ⟨rfl, rfl⟩
  · simp only [pure_bind, hooksLocal, hooksLocalFixed]
    cases vp.vS with
    | none =>
      simp only [StateT.run_pure, simulateQ_pure]
      exact ShiftLe.pure mo _ hle hinv
    | some v =>
      simp only [StateT.run_bind, StateT.run_pure, pure_bind, simulateQ_pure]
      exact ShiftLe.pure mo _ hle hinv

theorem shiftLe_startRecv {j : ℕ}
    (ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E)
    (P : Party) (t : ℕ) (γ : Γ) (σ : Sig) (Tn : T)
    {s : LState T Sig K I} (hle : s.sessions.length ≤ j) (hinv : TabSessInv mo s) :
    ShiftLe mo j Prod.snd
      (simulateQ lImpl (((hooksLocal cka prng fs mo).startRecv ctx P t γ σ Tn).run s))
      (fun k_fs => simulateQ lImpl
        (((hooksLocalFixed cka prng fs mo j k_fs).startRecv ctx P t γ σ Tn).run s)) := by
  have hbranch :
      ShiftLe mo j Prod.snd
        (simulateQ lImpl ((if mo.auth && decide (t = mo.tStar) then
          if mo.tL.isSome && decide (mo.tStar = mo.tH) then pure none
          else do
            let kk := cka.receive γ Tn
            let k' ← lookupFL kk.2
            let idx ← regSess kk.2
            return some (some (kk.1, (prng.up σ kk.2).1, (fs.initReceiver k', some idx)))
        else pure (some none) :
          LHM (Option (Option (Γ × Sig × (RS × Option ℕ))))).run s))
        (fun k_fs => simulateQ lImpl ((if mo.auth && decide (t = mo.tStar) then
          if mo.tL.isSome && decide (mo.tStar = mo.tH) then pure none
          else do
            let kk := cka.receive γ Tn
            let k' ← lookupFLFixed j k_fs kk.2
            let idx ← regSess kk.2
            return some (some (kk.1, (prng.up σ kk.2).1, (fs.initReceiver k', some idx)))
        else pure (some none) :
          LHM (Option (Option (Γ × Sig × (RS × Option ℕ))))).run s)) := by
    split
    · split
      · rename_i _ hth
        simp only [StateT.run_pure, simulateQ_pure]
        exact ShiftLe.pure mo _ hle hinv
      · rename_i _ hth
        have hnot_th : ¬ (mo.tL.isSome = true ∧ mo.tStar = mo.tH) := by
          intro ⟨h1, h2⟩; simp [h1, h2] at hth
        let kk := cka.receive γ Tn
        have hbindL : ((do
            let k' ← lookupFL kk.2
            let idx ← regSess kk.2
            return some (some (kk.1, (prng.up σ kk.2).1, (fs.initReceiver k', some idx))) :
              LHM (Option (Option (Γ × Sig × (RS × Option ℕ))))).run s) =
          (((lookupFL kk.2 >>= fun k' => regSess kk.2 >>= fun idx => pure (k', idx)) :
            LHM (K × ℕ)).run s >>= fun r =>
              pure (some (some (kk.1, (prng.up σ kk.2).1, (fs.initReceiver r.1.1, some r.1.2))),
                r.2)) := by
          simp [StateT.run_bind, bind_assoc]
        have hbindF : ∀ k_fs, ((do
            let k' ← lookupFLFixed j k_fs kk.2
            let idx ← regSess kk.2
            return some (some (kk.1, (prng.up σ kk.2).1, (fs.initReceiver k', some idx))) :
              LHM (Option (Option (Γ × Sig × (RS × Option ℕ))))).run s) =
          (((lookupFLFixed j k_fs kk.2 >>= fun k' => regSess kk.2 >>= fun idx => pure (k', idx)) :
            LHM (K × ℕ)).run s >>= fun r =>
              pure (some (some (kk.1, (prng.up σ kk.2).1, (fs.initReceiver r.1.1, some r.1.2))),
                r.2)) := by
          intro k_fs
          simp [StateT.run_bind, bind_assoc]
        change ShiftLe mo j Prod.snd
          (simulateQ lImpl ((do
            let k' ← lookupFL kk.2
            let idx ← regSess kk.2
            return some (some (kk.1, (prng.up σ kk.2).1, (fs.initReceiver k', some idx))) :
              LHM (Option (Option (Γ × Sig × (RS × Option ℕ))))).run s))
          (fun k_fs => simulateQ lImpl ((do
            let k' ← lookupFLFixed j k_fs kk.2
            let idx ← regSess kk.2
            return some (some (kk.1, (prng.up σ kk.2).1, (fs.initReceiver k', some idx))) :
              LHM (Option (Option (Γ × Sig × (RS × Option ℕ))))).run s))
        simp only [hbindL, hbindF, simulateQ_bind, simulateQ_pure]
        refine (shiftLe_lookupFL_regSess mo kk.2 hle hinv hnot_th).post mo _ ?_
        intro a b hb
        simp only [support_pure, Set.mem_singleton_iff] at hb
        subst hb; exact ⟨rfl, rfl⟩
    · simp only [StateT.run_pure, simulateQ_pure]
      exact ShiftLe.pure mo _ hle hinv
  simp only [hooksLocal, hooksLocalFixed, StateT.run_bind, StateT.run_get, pure_bind]
  cases s.cache t with
  | none => exact hbranch
  | some val =>
    rcases val with ⟨Tc, σc, k, idx?⟩
    by_cases hTc : Tc = Tn
    · simp only [hTc, ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact ShiftLe.pure mo _ hle hinv
    · simp only [hTc, ↓reduceIte]
      exact hbranch

theorem shiftLe_vRecv {j : ℕ}
    (ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E)
    (P : Party) (vp : VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ))
    (c : Header T × E) (rec : Option (SM.Record M (Header T × E)))
    {s : LState T Sig K I} (hle : s.sessions.length ≤ j) (hinv : TabSessInv mo s) :
    ShiftLe mo j Prod.snd
      (simulateQ lImpl ((vRecv (hooksLocal cka prng fs mo) ctx P vp c rec).run s))
      (fun k_fs => simulateQ lImpl
        ((vRecv (hooksLocalFixed cka prng fs mo j k_fs) ctx P vp c rec).run s)) := by
  unfold vRecv
  dsimp only
  split
  · simp only [StateT.run_pure, simulateQ_pure]
    exact ShiftLe.pure mo _ hle hinv
  · split
    · cases c.1.2 with
      | none =>
        simp only [pure_bind, StateT.run_pure, simulateQ_pure]
        exact ShiftLe.pure mo _ hle hinv
      | some Tn =>
        simp only [StateT.run_bind, simulateQ_bind]
        have hsr := shiftLe_startRecv cka prng fs mo ctx P c.1.1 vp.γ vp.root Tn hle hinv
        change ShiftLe mo j Prod.snd
          (simulateQ lImpl (((hooksLocal cka prng fs mo).startRecv ctx P c.1.1 vp.γ vp.root Tn).run s) >>= _)
          (fun k_fs => simulateQ lImpl (((hooksLocalFixed cka prng fs mo j k_fs).startRecv ctx P c.1.1 vp.γ vp.root Tn).run s) >>= _)
        refine hsr.post mo _ ?_
        intro a b hb
        rcases a with ⟨res_sr, s_sr⟩
        cases res_sr with
        | none =>
          simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hb
          subst hb; exact ⟨rfl, rfl⟩
        | some res_sr' =>
          cases res_sr' with
          | none =>
            simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hb
            subst hb; exact ⟨rfl, rfl⟩
          | some val =>
            rcases val with ⟨γ', σ', rs⟩
            simp only [hooksLocal, pure_bind, Function.update_self] at hb
            cases hfs : fs.receive rs.1 c.1 c.2 with
            | none =>
              simp only [hfs, pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hb
              subst hb; exact ⟨rfl, rfl⟩
            | some out =>
              rcases out with ⟨rs', i, m⟩
              simp only [hfs, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
              subst hb; exact ⟨rfl, rfl⟩
    · simp only [pure_bind, hooksLocal, hooksLocalFixed]
      cases vp.vR c.1.1 with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure]
        exact ShiftLe.pure mo _ hle hinv
      | some v =>
        dsimp only
        cases hfs : fs.receive v.1 c.1 c.2 with
        | none =>
          simp only [hfs, pure_bind, StateT.run_pure, simulateQ_pure]
          exact ShiftLe.pure mo _ hle hinv
        | some out =>
          rcases out with ⟨rs', i, m⟩
          simp only [hfs, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
            simulateQ_pure]
          exact ShiftLe.pure mo _ hle hinv

theorem shiftLe_stepL {j : ℕ}
    (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    {esL : EStateL Γ T Sig SS RS M E K I}
    (hle : esL.h.sessions.length ≤ j) (hinv : TabSessInv mo esL.h) :
    ShiftLe mo j (fun r => r.2.h)
      (stepL cka prng fs Δcka qep mo q esL)
      (fun k_fs => stepLFixed cka prng fs Δcka qep mo j k_fs q esL) := by
  rcases q with n | ((((q1 | q2) | q3) | q4) | P)
  · rw [stepL_coinsE]
    refine ShiftLe.of_eq mo
      (fun k_fs => stepLFixed_coinsE cka prng fs Δcka qep mo j k_fs n esL) ?_
    intro r hr
    rw [support_map] at hr
    rcases hr with ⟨_, _, rfl⟩
    exact ⟨hle, hinv⟩
  · rcases q1 with ⟨P, m, r_coins⟩
    simp only [stepL, stepLFixed, implE, QueryImpl.add_apply, transmitE, StateT.run_bind,
      StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure, simulateQ_pure]
      exact ShiftLe.pure mo _ hle hinv
    · cases esL.g.epMgmt (2 + Δcka) qep P r_coins.isSome with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure]
        exact ShiftLe.pure mo _ hle hinv
      | some s₁ =>
        dsimp only
        split
        · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
            simulateQ_pure]
          exact ShiftLe.pure mo _ hle hinv
        · simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind]
          refine (shiftLe_vSend cka prng fs mo s₁ P (s₁.st P) m none r_coins hle hinv).post
            mo _ ?_
          intro a b hb
          rcases a with ⟨res_vs, h'⟩
          cases res_vs with
          | none =>
            simp only [abortE, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
            subst hb; exact ⟨rfl, rfl⟩
          | some val =>
            rcases val with ⟨st', c⟩
            simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
            subst hb; exact ⟨rfl, rfl⟩
  · rcases q2 with ⟨P, m₀, m₁, r_coins⟩
    simp only [stepL, stepLFixed, implE, QueryImpl.add_apply, challE, StateT.run_bind,
      StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure, simulateQ_pure]
      exact ShiftLe.pure mo _ hle hinv
    · cases esL.g.epMgmt (2 + Δcka) qep P r_coins.isSome with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure]
        exact ShiftLe.pure mo _ hle hinv
      | some s₁ =>
        dsimp only
        split
        · simp only [StateT.run_pure, simulateQ_pure]
          exact ShiftLe.pure mo _ hle hinv
        · split
          · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
              simulateQ_pure]
            exact ShiftLe.pure mo _ hle hinv
          · simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind]
            refine (shiftLe_vSend cka prng fs mo s₁ P (s₁.st P) _ (some (m₀, m₁)) r_coins hle hinv).post
              mo _ ?_
            intro a b hb
            rcases a with ⟨res_vs, h'⟩
            cases res_vs with
            | none =>
              simp only [abortE, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
              subst hb; exact ⟨rfl, rfl⟩
            | some val =>
              rcases val with ⟨st', c⟩
              simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
              subst hb; exact ⟨rfl, rfl⟩
  · rcases q3 with ⟨P, c⟩
    simp only [stepL, stepLFixed, implE, QueryImpl.add_apply, deliverE, StateT.run_bind,
      StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure, simulateQ_pure]
      exact ShiftLe.pure mo _ hle hinv
    · split
      · simp only [StateT.run_pure, simulateQ_pure]
        exact ShiftLe.pure mo _ hle hinv
      · simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind,
          commitE, hooksLocal, hooksLocalFixed]
        refine (shiftLe_vRecv cka prng fs mo esL.g P (esL.g.st P) c _ hle hinv).post
          mo _ ?_
        intro a b hb
        rcases a with ⟨res_vr, h'⟩
        cases res_vr with
        | none =>
          simp only [abortE, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
          subst hb; exact ⟨rfl, rfl⟩
        | some res_vr' =>
          cases res_vr' with
          | none =>
            simp only [pure_bind] at hb
            split at hb
            · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
              subst hb; exact ⟨rfl, rfl⟩
            · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hb
              subst hb; exact ⟨rfl, rfl⟩
          | some val =>
            rcases val with ⟨st', t', i', m'⟩
            simp only [pure_bind, StateT.run_bind, StateT.run_pure, StateT.run_modify,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
            subst hb; exact ⟨rfl, rfl⟩
  · rcases q4 with ⟨P, c⟩
    simp only [stepL, stepLFixed, implE, QueryImpl.add_apply, injectE, StateT.run_bind,
      StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure, simulateQ_pure]
      exact ShiftLe.pure mo _ hle hinv
    · simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind,
        commitE, hooksLocal, hooksLocalFixed]
      refine (shiftLe_vRecv cka prng fs mo esL.g P (esL.g.st P) c none hle hinv).post
        mo _ ?_
      intro a b hb
      rcases a with ⟨res_vr, h'⟩
      cases res_vr with
      | none =>
        simp only [abortE, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
        subst hb; exact ⟨rfl, rfl⟩
      | some res_vr' =>
        cases res_vr' with
        | none =>
          simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hb
          subst hb; exact ⟨rfl, rfl⟩
        | some val =>
          rcases val with ⟨st', t', i', m'⟩
          simp only [pure_bind] at hb
          split at hb
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
            subst hb; exact ⟨rfl, rfl⟩
          · split at hb
            · simp only [StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_pure,
                support_pure, Set.mem_singleton_iff] at hb
              subst hb; exact ⟨rfl, rfl⟩
            · split at hb
              · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                  simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
                subst hb; exact ⟨rfl, rfl⟩
              · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hb
                subst hb; exact ⟨rfl, rfl⟩
  · simp only [stepL, stepLFixed, implE, QueryImpl.add_apply, corrE, StateT.run_bind,
      StateT.run_get, pure_bind, hooksLocal, hooksLocalFixed, run_liftH]
    split
    · simp only [StateT.run_pure, simulateQ_pure]
      exact ShiftLe.pure mo _ hle hinv
    · split
      · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
          simulateQ_pure]
        exact ShiftLe.pure mo _ hle hinv
      · simp only [pure_bind, StateT.run_bind, StateT.run_pure, StateT.run_modify,
          simulateQ_pure]
        exact ShiftLe.pure mo _ hle hinv

theorem evalDist_runLocAt_le_fixed {j : ℕ}
    (oa : SMComp Γ T Sig SS RS M CCoins E Bool)
    {esL : EStateL Γ T Sig SS RS M E K I}
    (hle : esL.h.sessions.length ≤ j) (hinv : TabSessInv mo esL.h) :
    𝒟[runLocAt cka prng fs Δcka qep mo j oa esL] {true} ≤
      𝒟[($ᵗ K : ProbComp K) >>= fun k_fs =>
        runLocAtFixed cka prng fs Δcka qep mo j k_fs oa esL] {true} := by
  induction oa using OracleComp.inductionOn generalizing esL with
  | pure b' =>
    simp only [runLocAt_pure, runLocAtFixed_pure, OracleComp.evalDist_bind_const, le_rfl]
  | query_bind q k ih =>
    simp only [runLocAt_query_bind, runLocAtFixed_query_bind]
    refine shiftLe_stepL cka prng fs Δcka qep mo q hle hinv
      (fun r => runLocAt cka prng fs Δcka qep mo j (k r.1) r.2)
      (fun k_fs r => runLocAtFixed cka prng fs Δcka qep mo j k_fs (k r.1) r.2) ?_ ?_
    · intro r hlt k_fs
      exact (evalDist_runLocAt_eq_fixed_of_lt cka prng fs Δcka qep mo k_fs (k r.1) hlt).le
    · intro r hle' hinv'
      exact ih r.1 hle' hinv'

theorem localAuthAt_le_localAuthAtFixed (j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[localAuthAt cka prng fs lam Δcka qep j tL t A] {true} ≤
      𝒟[($ᵗ K : ProbComp K) >>= fun k_fs =>
        localAuthAtFixed cka prng fs lam Δcka qep j k_fs tL t A] {true} := by
  let mo : Mode := ⟨true, tL, t⟩
  dsimp only [localAuthAt, localAuthAtFixed]
  have hle0 : ({} : LState T Sig K I).sessions.length ≤ j := Nat.zero_le j
  have hinv0 : TabSessInv mo ({} : LState T Sig K I) := fun _ _ => rfl
  refine shiftLe_initLocal cka prng fs lam mo hle0 hinv0
    (fun r => match r.1 with
      | none => pure false
      | some (vA, vB) =>
        runLocAt cka prng fs Δcka qep mo j A
          { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := r.2 })
    (fun k_fs r => match r.1 with
      | none => pure false
      | some (vA, vB) =>
        runLocAtFixed cka prng fs Δcka qep mo j k_fs A
          { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := r.2 })
    ?_ ?_
  · intro r hlt k_fs
    rcases r with ⟨vs, h⟩
    cases vs with
    | none => exact le_rfl
    | some vAB =>
      rcases vAB with ⟨vA, vB⟩
      exact (evalDist_runLocAt_eq_fixed_of_lt cka prng fs Δcka qep mo k_fs A hlt).le
  · intro r hle hinv
    rcases r with ⟨vs, h⟩
    cases vs with
    | none =>
      simp [OracleComp.evalDist_bind_const]
    | some vAB =>
      rcases vAB with ⟨vA, vB⟩
      exact evalDist_runLocAt_le_fixed cka prng fs Δcka qep mo A hle hinv

end HalfA

/-! ## Coupling `localAuthAtFixed` with `fsWin` -/

section HalfB

open Engine

variable {ι : Type} {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ) (mo : Mode)

abbrev EStateF (Γ T Sig SS RS M E K I : Type) :=
  EState (PartyState Γ T Sig (Option SS) (Option RS)) M (Header T × E)
    (FSState T Sig K I SS RS E)

abbrev FSGameState (SS RS T M E : Type) :=
  FSAEAD.State SS RS (Header T) M E

def stepF (j : ℕ) (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    (esF : EStateF Γ T Sig SS RS M E K I) (st : FSGameState SS RS T M E) :
    ProbComp (((SMSpec Γ T Sig SS RS M CCoins E).Range q ×
      EStateF Γ T Sig SS RS M E K I) × FSGameState SS RS T M E) :=
  (simulateQ (implFS fs)
    ((implE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy q).run
      esF)).run st

def runF (j : ℕ) (oa : SMComp Γ T Sig SS RS M CCoins E Bool)
    (esF : EStateF Γ T Sig SS RS M E K I) (st : FSGameState SS RS T M E) : ProbComp Bool := do
  let r ← (simulateQ (implFS fs)
    ((simulateQ (implE (hooksFS cka prng fs Δcka mo j)
      (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run esF)).run st
  pure r.2.win

theorem runF_query_bind (j : ℕ)
    (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpec Γ T Sig SS RS M CCoins E).Range q → SMComp Γ T Sig SS RS M CCoins E Bool)
    (esF : EStateF Γ T Sig SS RS M E K I) (st : FSGameState SS RS T M E) :
    runF cka prng fs Δcka qep mo j
      (liftM (OracleSpec.query q) >>= k) esF st =
      stepF cka prng fs Δcka qep mo j q esF st >>= fun r =>
        runF cka prng fs Δcka qep mo j (k r.1.1) r.1.2 r.2 := by
  simp [runF, stepF, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc]

theorem stepF_coinsE (j : ℕ) (n : unifSpec.Domain)
    (esF : EStateF Γ T Sig SS RS M E K I) (st : FSGameState SS RS T M E) :
    stepF cka prng fs Δcka qep mo j (.inl n) esF st =
      (fun u => ((u, esF), st)) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1))) := by
  simp [stepF, implE, coinsE, implFS, map_eq_bind_pure_comp, simulateQ_bind, simulateQ_query,
    StateT.run_bind]

/-! ### Absorbing `st.win` state -/

theorem fsOracleImpl_preserves_win
    (q : (FSAEAD.spec SS RS (Header T) M E).Domain)
    (st : FSGameState SS RS T M E) (hwin : st.win = true) :
    ∀ r ∈ support ((FSAEAD.oracleImpl fs q).run st), r.2.win = true := by
  intro r hr
  rcases q with (((((⟨a, m⟩ | ⟨a, m₀, m₁⟩) | ⟨⟩) | ⟨⟩) | ⟨a, e⟩) | ⟨a, e⟩)
  · simp only [FSAEAD.oracleImpl, QueryImpl.add_apply, FSAEAD.transmitImpl, StateT.run_modifyGet,
      FSAEAD.transmit, support_pure, Set.mem_singleton_iff] at hr
    subst hr; split <;> simp [hwin]
  · simp only [FSAEAD.oracleImpl, QueryImpl.add_apply, FSAEAD.challengeImpl, StateT.run_modifyGet,
      FSAEAD.challenge, support_pure, Set.mem_singleton_iff] at hr
    subst hr; split <;> simp [hwin]
  · simp only [FSAEAD.oracleImpl, QueryImpl.add_apply, FSAEAD.corruptSenderImpl,
      StateT.run_modifyGet, FSAEAD.corruptSender, support_pure, Set.mem_singleton_iff] at hr
    subst hr; split <;> simp [hwin]
  · simp only [FSAEAD.oracleImpl, QueryImpl.add_apply, FSAEAD.corruptReceiverImpl,
      StateT.run_modifyGet, FSAEAD.corruptReceiver, support_pure, Set.mem_singleton_iff] at hr
    subst hr; split <;> simp [hwin]
  · simp only [FSAEAD.oracleImpl, QueryImpl.add_apply, FSAEAD.deliverImpl, StateT.run_modifyGet,
      FSAEAD.deliver, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    split
    · exact hwin
    · split
      · exact hwin
      · split
        · simp [hwin]
        · simp [FSAEAD.State.removeFromTransit, hwin]
  · simp only [FSAEAD.oracleImpl, QueryImpl.add_apply, FSAEAD.injectImpl, StateT.run_modifyGet,
      FSAEAD.inject, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    split
    · exact hwin
    · split
      · exact hwin
      · simp [FSAEAD.State.removeFromTransit, hwin]

theorem simulateQ_implFS_preserves_win {α : Type}
    (oa : FSAEAD.AdversaryComp SS RS (Header T) M E α)
    (st : FSGameState SS RS T M E) (hwin : st.win = true) :
    ∀ r ∈ support ((simulateQ (implFS fs) oa).run st), r.2.win = true := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a =>
    intro r hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hwin
  | query_bind q k ih =>
    intro r hr
    simp only [simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query, id_eq,
      StateT.run_bind, MonadAttach.mem_support_bind] at hr
    obtain ⟨u, hu, hr⟩ := hr
    cases q with
    | inl n =>
      change u ∈ support
        ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp _) >>= fun x => pure (x, st)) at hu
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hu
      obtain ⟨_, _, rfl⟩ := hu
      exact ih _ st hwin r hr
    | inr oq =>
      change u ∈ support ((FSAEAD.oracleImpl fs oq).run st) at hu
      exact ih u.1 u.2 (fsOracleImpl_preserves_win fs oq st hwin u hu) r hr

theorem evalDist_runF_eq_one_of_win (j : ℕ)
    (oa : SMComp Γ T Sig SS RS M CCoins E Bool)
    (esF : EStateF Γ T Sig SS RS M E K I) (st : FSGameState SS RS T M E)
    (hwin : st.win = true) :
    𝒟[runF cka prng fs Δcka qep mo j oa esF st] {true} = 1 := by
  unfold runF
  refine evalDist_bind_eq_one _ _ fun r hr => ?_
  rw [simulateQ_implFS_preserves_win fs _ st hwin r hr]
  simp

/-! ### Absorbing `LHSDead` state -/

def RWrongSession (j : ℕ) (esL : EStateL Γ T Sig SS RS M E K I) : Prop :=
  let vpR := esL.g.st (Party.receiverOf mo.tStar)
  mo.tStar ≤ vpR.tcur ∧
  ∀ rs, vpR.vR mo.tStar ≠ some (rs, some j)

/-- Terminal / doomed LHS states from which `runLocAtFixed` outputs `true` with probability `0`. -/
def LHSDead (j : ℕ) (esL : EStateL Γ T Sig SS RS M E K I) : Prop :=
  ((esL.abort || esL.g.win) = true ∧
    (authOut (2 + Δcka) mo.policy esL && (esL.h.lastIdx == some j)) = false) ∨
  (esL.abort = false ∧ esL.g.win = false ∧ (∀ P, (esL.g.st P).id = P) ∧ RWrongSession mo j esL)

theorem LHSDead.of_abort (j : ℕ) {esL : EStateL Γ T Sig SS RS M E K I}
    (hab : esL.abort = true) : LHSDead Δcka mo j esL := by
  left
  simp [authOut, hab]

theorem LHSDead.of_win_ne (j : ℕ) {esL : EStateL Γ T Sig SS RS M E K I}
    (hwin : esL.g.win = true) (hne : esL.h.lastIdx ≠ some j) : LHSDead Δcka mo j esL := by
  left
  have hbeq : (esL.h.lastIdx == some j) = false := beq_eq_false_iff_ne.mpr hne
  simp [hwin, hbeq]

theorem stepLFixed_eq_of_abort_or_win (j : ℕ) (k_fs : K)
    (oq : (spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I) (h : (esL.abort || esL.g.win) = true) :
    ∀ r ∈ support (stepLFixed cka prng fs Δcka qep mo j k_fs (.inr oq) esL), r.2 = esL := by
  intro r hr
  rcases oq with ((((⟨P, m, rc⟩ | ⟨P, m₀, m₁, rc⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · simp only [stepLFixed, implE, QueryImpl.add_apply, transmitE, StateT.run_bind,
      StateT.run_get, pure_bind, h, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hr
    exact congrArg Prod.snd hr
  · simp only [stepLFixed, implE, QueryImpl.add_apply, challE, StateT.run_bind,
      StateT.run_get, pure_bind, h, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hr
    exact congrArg Prod.snd hr
  · simp only [stepLFixed, implE, QueryImpl.add_apply, deliverE, StateT.run_bind,
      StateT.run_get, pure_bind, h, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hr
    exact congrArg Prod.snd hr
  · simp only [stepLFixed, implE, QueryImpl.add_apply, injectE, StateT.run_bind,
      StateT.run_get, pure_bind, h, Bool.true_or, ↓reduceIte, StateT.run_pure,
      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
    exact congrArg Prod.snd hr
  · simp only [stepLFixed, implE, QueryImpl.add_apply, corrE, StateT.run_bind,
      StateT.run_get, pure_bind, h, Bool.true_or, ↓reduceIte, StateT.run_pure,
      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
    exact congrArg Prod.snd hr

theorem vSend_LFixed_preserves_id_vR (j : ℕ) (k_fs : K)
    (ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E)
    (P : Party) (vp : PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ))
    (m : M) (pair : Option (M × M)) (r : Option CCoins) (s : LState T Sig K I) :
    ∀ out ∈ support (simulateQ lImpl
      ((vSend (hooksLocalFixed cka prng fs mo j k_fs) ctx P vp m pair r).run s)),
      ∀ vp' c, out.1 = some (vp', c) →
        vp'.id = vp.id ∧ vp.tcur ≤ vp'.tcur ∧ vp'.vR = vp.vR := by
  intro out hout vp' c hsome
  unfold vSend at hout
  by_cases hsends : vp.id.sendsIn (vp.tcur + 1) = true
  · simp only [hsends, ↓reduceIte, StateT.run_bind, simulateQ_bind,
      MonadAttach.mem_support_bind] at hout
    obtain ⟨r1, hr1, hout⟩ := hout
    cases h1 : r1.1 with
    | none =>
      rw [h1] at hout
      simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hout
      rw [hout] at hsome; cases hsome
    | some val =>
      rcases val with ⟨γ', T', σ', ss⟩
      rw [h1] at hout
      simp only [pure_bind, StateT.run_bind, simulateQ_bind, StateT.run_pure, simulateQ_pure,
        MonadAttach.mem_support_bind] at hout
      obtain ⟨r2, hr2, hout⟩ := hout
      cases h2 : r2.1 with
      | none =>
        rw [h2] at hout
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hout
        rw [hout] at hsome; cases hsome
      | some vc =>
        rw [h2] at hout
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hout
        rw [hout] at hsome
        cases hsome
        exact ⟨rfl, Nat.le_succ _, rfl⟩
  · simp only [hsends, Bool.false_eq_true, ↓reduceIte, pure_bind, StateT.run_bind,
      simulateQ_bind] at hout
    cases hvs : vp.vS with
    | none =>
      simp only [hvs, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hout
      rw [hout] at hsome
      cases hsome
      exact ⟨rfl, le_rfl, rfl⟩
    | some v =>
      simp only [hvs, StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at hout
      obtain ⟨r2, hr2, hout⟩ := hout
      cases h2 : r2.1 with
      | none =>
        rw [h2] at hout
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hout
        rw [hout] at hsome; cases hsome
      | some vc =>
        rw [h2] at hout
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hout
        rw [hout] at hsome
        cases hsome
        exact ⟨rfl, le_rfl, rfl⟩

theorem party_eq_receiverOf_of_sendsIn_false (P : Party) (t : ℕ)
    (h : P.sendsIn t = false) : P = Party.receiverOf t := by
  unfold Party.sendsIn at h
  unfold Party.receiverOf Party.senderOf
  cases P <;> split <;> simp_all

theorem vRecv_LFixed_preserves_RWrongSession (j : ℕ) (k_fs : K)
    (ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E)
    (P : Party) (vp : PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ))
    (c : Header T × E) (rec : Option (Record M (Header T × E))) (s : LState T Sig K I)
    (hid : vp.id = P)
    (hR : P = Party.receiverOf mo.tStar →
      mo.tStar ≤ vp.tcur ∧ ∀ rs, vp.vR mo.tStar ≠ some (rs, some j)) :
    ∀ out ∈ support (simulateQ lImpl
      ((vRecv (hooksLocalFixed cka prng fs mo j k_fs) ctx P vp c rec).run s)),
      ∀ vp' t' i' m', out.1 = some (some (vp', t', i', m')) →
        vp'.id = P ∧
        (P = Party.receiverOf mo.tStar →
          mo.tStar ≤ vp'.tcur ∧ ∀ rs, vp'.vR mo.tStar ≠ some (rs, some j)) ∧
        (t' = mo.tStar → out.2.lastIdx ≠ some j) := by
  intro out hout vp' t' i' m' hsome
  unfold vRecv at hout
  by_cases hcond : (vp.id.sendsIn c.1.1 || decide (vp.tcur + 1 < c.1.1)) = true
  · simp only [hcond, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hout
    rw [hout] at hsome; cases hsome
  · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hout
    have hnsends : vp.id.sendsIn c.1.1 = false := by
      cases h : vp.id.sendsIn c.1.1
      · rfl
      · simp [h] at hcond
    have hP_recv : P = Party.receiverOf c.1.1 :=
      party_eq_receiverOf_of_sendsIn_false P c.1.1 (hid ▸ hnsends)
    by_cases hstep : c.1.1 = vp.tcur + 1
    · simp only [hstep, ↓reduceIte] at hout
      cases hhdr : c.1.2 with
      | none =>
        simp only [hhdr, pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hout
        rw [hout] at hsome; cases hsome
      | some Tn =>
        simp only [hhdr, StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at hout
        obtain ⟨r1, hr1, hout⟩ := hout
        cases h1 : r1.1 with
        | none =>
          rw [h1] at hout
          simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hout
          rw [hout] at hsome; cases hsome
        | some o1 =>
          cases o1 with
          | none =>
            rw [h1] at hout
            simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hout
            rw [hout] at hsome; cases hsome
          | some val =>
            rcases val with ⟨γ', σ', rs⟩
            rw [h1] at hout
            simp only [pure_bind, Function.update_self] at hout
            unfold hooksLocalFixed at hout
            dsimp only at hout
            cases hrcv : fs.receive rs.1 c.1 c.2 with
            | none =>
              simp only [hrcv, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hout
              rw [hout] at hsome; cases hsome
            | some r_fs =>
              rcases r_fs with ⟨rs', i0, m0⟩
              simp only [hrcv, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hout
              rw [hout] at hsome
              cases hsome
              have ht_ne : c.1.1 ≠ mo.tStar := by
                intro heq
                have hPR : P = Party.receiverOf mo.tStar := heq ▸ hP_recv
                have hle := (hR hPR).1
                omega
              refine ⟨hid, fun hPR => ⟨by dsimp only; have := (hR hPR).1; omega, fun rs0 => ?_⟩,
                fun heq => False.elim (ht_ne (hstep.trans heq))⟩
              dsimp only
              have hne_step : mo.tStar ≠ vp.tcur + 1 := fun h => ht_ne (hstep.trans h.symm)
              rw [Function.update_of_ne hne_step, Function.update_of_ne hne_step]
              exact (hR hPR).2 rs0
    · simp only [hstep, ↓reduceIte, pure_bind] at hout
      cases hvr : vp.vR c.1.1 with
      | none =>
        simp only [hvr, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hout
        rw [hout] at hsome; cases hsome
      | some v =>
        simp only [hvr] at hout
        unfold hooksLocalFixed at hout
        dsimp only at hout
        cases hrcv : fs.receive v.1 c.1 c.2 with
        | none =>
          simp only [hrcv, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hout
          rw [hout] at hsome; cases hsome
        | some r_fs =>
          rcases r_fs with ⟨rs', i0, m0⟩
          simp only [hrcv, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hout
          rw [hout] at hsome
          cases hsome
          refine ⟨hid, fun hPR => ⟨(hR hPR).1, fun rs0 => ?_⟩, fun heq => ?_⟩
          · dsimp only
            by_cases heq : c.1.1 = mo.tStar
            · rw [heq, Function.update_self]
              simp only [ne_eq, Option.some.injEq, Prod.mk.injEq, not_and]
              intro h_eq
              subst h_eq
              intro hv2
              exact (hR hPR).2 v.1 (by rw [← heq, hvr, ← Prod.eta v, hv2])
            · simp only [Function.update_of_ne (Ne.symm heq)]
              exact (hR hPR).2 rs0
          · rw [hout]
            dsimp only
            intro hv2
            have hPR : P = Party.receiverOf mo.tStar := heq ▸ hP_recv
            exact (hR hPR).2 v.1 (by rw [← heq, hvr, ← Prod.eta v, hv2])

theorem stepLFixed_preserves_LHSDead (hmo : mo.auth = true) (j : ℕ) (k_fs : K)
    (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I) (hdead : LHSDead Δcka mo j esL) :
    ∀ r ∈ support (stepLFixed cka prng fs Δcka qep mo j k_fs q esL),
      LHSDead Δcka mo j r.2 := by
  intro r hr
  cases q with
  | inl n =>
    rw [stepLFixed_coinsE] at hr
    simp only [support_map, Set.mem_image] at hr
    obtain ⟨u, _, rfl⟩ := hr
    exact hdead
  | inr oq =>
    rcases hdead with ⟨habw, hout⟩ | ⟨hab, hwin, hid, hR⟩
    · rw [stepLFixed_eq_of_abort_or_win cka prng fs Δcka qep mo j k_fs oq esL habw r hr]
      exact Or.inl ⟨habw, hout⟩
    · have habw : (esL.abort || esL.g.win) = false := by simp [hab, hwin]
      rcases oq with ((((⟨P, m, rc⟩ | ⟨P, m₀, m₁, rc⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
      ·
        simp only [stepLFixed, implE, QueryImpl.add_apply, transmitE, StateT.run_bind,
          StateT.run_get, pure_bind, habw, Bool.false_eq_true, ↓reduceIte] at hr
        cases hep : esL.g.epMgmt (2 + Δcka) qep P rc.isSome with
        | none =>
          simp only [hep, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hr
          subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
        | some s₁ =>
          have hs1_st : s₁.st = esL.g.st := by
            unfold GameState.epMgmt at hep
            split at hep
            · split at hep
              · cases hep
              · cases hep; split <;> rfl
            · split at hep
              · cases hep
              · cases hep; rfl
          have hs1_win : s₁.win = false := by
            unfold GameState.epMgmt at hep
            split at hep
            · split at hep
              · cases hep
              · cases hep; split <;> exact hwin
            · split at hep
              · cases hep
              · cases hep; exact hwin
          simp only [hep] at hr
          split at hr
          · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact LHSDead.of_abort Δcka mo j rfl
          · simp only [run_liftH, StateT.run_bind, simulateQ_bind, simulateQ_pure, pure_bind,
              bind_assoc, MonadAttach.mem_support_bind] at hr
            obtain ⟨out, hout, hr⟩ := hr
            cases hout1 : out.1 with
            | none =>
              rw [hout1] at hr
              simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
              subst hr; exact LHSDead.of_abort Δcka mo j rfl
            | some vc =>
              rcases vc with ⟨vp', ct⟩
              rw [hout1] at hr
              simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
              subst hr
              obtain ⟨hid', htcur', hvR'⟩ :=
                vSend_LFixed_preserves_id_vR cka prng fs mo j k_fs s₁ P (s₁.st P) m none rc
                  esL.h out hout vp' ct hout1
              refine Or.inr ⟨hab, hs1_win, fun Q => ?_, ?_⟩
              · by_cases hQP : Q = P
                · subst hQP
                  simp only [GameState.record, Function.update_self, hid', hs1_st, hid]
                · simp only [GameState.record, Function.update_of_ne hQP, hs1_st, hid]
              · unfold RWrongSession at hR ⊢
                by_cases hRP : Party.receiverOf mo.tStar = P
                · rw [hRP] at hR ⊢
                  simp only [GameState.record, Function.update_self]
                  rw [hs1_st] at htcur' hvR'
                  exact ⟨le_trans hR.1 htcur', fun rs => by rw [hvR']; exact hR.2 rs⟩
                · simp only [GameState.record, Function.update_of_ne hRP, hs1_st]
                  exact hR
      ·
        have hcfg : (mo.cfg : Config M).challAllowedIn = fun _ => false := by
          simp [Mode.cfg, hmo, Config.auth]
        simp only [stepLFixed, implE, QueryImpl.add_apply, challE, StateT.run_bind,
          StateT.run_get, pure_bind, habw, Bool.false_eq_true, ↓reduceIte] at hr
        cases hep : esL.g.epMgmt (2 + Δcka) qep P rc.isSome with
        | none =>
          simp only [hep, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hr
          subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
        | some s₁ =>
          simp only [hep, hcfg, Bool.not_false, Bool.or_true, ↓reduceIte, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
      ·
        have hdelWin : (mo.cfg : Config M).deliverWin = false := by
          simp [Mode.cfg, hmo, Config.auth]
        simp only [stepLFixed, implE, QueryImpl.add_apply, deliverE, StateT.run_bind,
          StateT.run_get, pure_bind, habw, Bool.false_eq_true, ↓reduceIte, hdelWin,
          Bool.false_and] at hr
        cases hint : esL.g.inTransit P.other c with
        | none =>
          simp only [hint, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hr
          subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
        | some rec =>
          simp only [hint, run_liftH, StateT.run_bind, simulateQ_bind, simulateQ_pure, pure_bind,
            bind_assoc, MonadAttach.mem_support_bind] at hr
          obtain ⟨out, hout, hr⟩ := hr
          cases hout1 : out.1 with
          | none =>
            rw [hout1] at hr
            simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact LHSDead.of_abort Δcka mo j rfl
          | some o1 =>
            cases o1 with
            | none =>
              rw [hout1] at hr
              simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
              subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
            | some val =>
              rcases val with ⟨vp', t', i', m'⟩
              rw [hout1] at hr
              simp only [commitE, hooksLocalFixed, run_liftH, StateT.run_bind,
                StateT.run_pure, pure_bind, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
                StateT.run_modify, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
              subst hr
              obtain ⟨hid', hR', _⟩ :=
                vRecv_LFixed_preserves_RWrongSession cka prng fs mo j k_fs esL.g P (esL.g.st P)
                  c (some rec) esL.h (hid P) (fun hPR => hPR ▸ hR) out hout vp' t' i' m' hout1
              refine Or.inr ⟨hab, hwin, fun Q => ?_, ?_⟩
              · by_cases hQP : Q = P
                · subst hQP; simp [Function.update_self, hid']
                · simp [GameState.accept, GameState.delete, Function.update_of_ne hQP, hid]
              · unfold RWrongSession at hR ⊢
                by_cases hRP : Party.receiverOf mo.tStar = P
                · simp only [hRP, Function.update_self]
                  exact hR' hRP.symm
                · simp only [GameState.accept, GameState.delete, Function.update_of_ne hRP]
                  exact hR
      ·
        have hinjFull : (mo.cfg : Config M).injectFull = fun t => t == mo.tStar := by
          simp [Mode.cfg, hmo, Config.auth]
        simp only [stepLFixed, implE, QueryImpl.add_apply, injectE, StateT.run_bind,
          StateT.run_get, pure_bind, hab, hwin, Bool.false_or] at hr
        split at hr
        · simp only [StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hr
          subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
        · simp only [run_liftH, StateT.run_bind, simulateQ_bind, simulateQ_pure, pure_bind,
            bind_assoc, MonadAttach.mem_support_bind] at hr
          obtain ⟨out, hout, hr⟩ := hr
          cases hout1 : out.1 with
          | none =>
            rw [hout1] at hr
            simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact LHSDead.of_abort Δcka mo j rfl
          | some o1 =>
            cases o1 with
            | none =>
              rw [hout1] at hr
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hr
              subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
            | some val =>
              rcases val with ⟨vp', t', i', m'⟩
              rw [hout1] at hr
              simp only [pure_bind] at hr
              obtain ⟨hid', hR', hlast⟩ :=
                vRecv_LFixed_preserves_RWrongSession cka prng fs mo j k_fs esL.g P (esL.g.st P)
                  c none esL.h (hid P) (fun hPR => hPR ▸ hR) out hout vp' t' i' m' hout1
              split at hr
              · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hr
                subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
              · split at hr
                · simp only [commitE, hooksLocalFixed, run_liftH, StateT.run_bind, StateT.run_pure,
                    pure_bind, StateT.run_modify, simulateQ_pure, support_pure,
                    Set.mem_singleton_iff] at hr
                  subst hr
                  refine Or.inr ⟨hab, hwin, fun Q => ?_, ?_⟩
                  · by_cases hQP : Q = P
                    · subst hQP; simp [Function.update_self, hid']
                    · simp [GameState.accept, GameState.delete, Function.update_of_ne hQP, hid]
                  · unfold RWrongSession at hR ⊢
                    by_cases hRP : Party.receiverOf mo.tStar = P
                    · simp only [hRP, Function.update_self]
                      exact hR' hRP.symm
                    · simp only [GameState.accept, GameState.delete, Function.update_of_ne hRP]
                      exact hR
                · simp only [hinjFull] at hr
                  by_cases ht_eq : (t' == mo.tStar) = true
                  · simp only [ht_eq, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
                      StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
                    subst hr
                    exact LHSDead.of_win_ne Δcka mo j rfl (hlast (beq_iff_eq.mp ht_eq))
                  · simp only [ht_eq, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
                    subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
      ·
        simp only [stepLFixed, implE, QueryImpl.add_apply, corrE, StateT.run_bind,
          StateT.run_get, pure_bind, hab, hwin, Bool.false_or] at hr
        split at hr
        · simp only [StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hr
          subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
        · split at hr
          · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact LHSDead.of_abort Δcka mo j rfl
          · simp only [run_liftH, hooksLocalFixed, StateT.run_bind, StateT.run_pure, pure_bind,
              StateT.run_modify, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr
            refine Or.inr ⟨hab, hwin, hid, hR⟩

theorem evalDist_runLocAtFixed_eq_zero_of_dead (hmo : mo.auth = true) (j : ℕ) (k_fs : K)
    (oa : SMComp Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) (hdead : LHSDead Δcka mo j esL) :
    𝒟[runLocAtFixed cka prng fs Δcka qep mo j k_fs oa esL] {true} = 0 := by
  induction oa using OracleComp.inductionOn generalizing esL with
  | pure b' =>
    rw [runLocAtFixed_pure]
    rcases hdead with ⟨_, hout⟩ | ⟨_, hwin, _, _⟩
    · simp [hout]
    · simp [authOut, hwin]
  | query_bind q k ih =>
    rw [runLocAtFixed_query_bind]
    exact evalDist_bind_eq_zero _ _ fun r hr =>
      ih r.1 r.2 (stepLFixed_preserves_LHSDead cka prng fs Δcka qep mo hmo j k_fs q esL hdead r hr)

theorem evalDist_runLocAtFixed_eq_zero_of_not_validGuess (j : ℕ) (k_fs : K)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = false)
    (oa : SMComp Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    𝒟[runLocAtFixed cka prng fs Δcka qep mo j k_fs oa esL] {true} = 0 := by
  unfold runLocAtFixed
  refine evalDist_bind_eq_zero _ _ fun r _ => ?_
  have h : authOut (2 + Δcka) mo.policy r.2 = false := by
    simp [authOut, Mode.policy, authLosingConditionsAvoided, hvg]
  simp [h]

/-! ### Bookkeeping coupling `BookSync` -/

/-- Synchronization between `sL : LState` and `sF : FSState` on `sessions`, `table`, and `cache`. -/
def BookSync (j : ℕ) (k_fs : K) (sL : LState T Sig K I)
    (sF : FSState T Sig K I SS RS E) : Prop :=
  sL.sessions = sF.sessions ∧
  sL.sessions.Nodup ∧
  (¬(mo.tL.isSome = true ∧ mo.tStar = mo.tH) →
    ∀ Ik : I,
      (sL.table.lookup Ik).isSome = decide (Ik ∈ sL.sessions) ∧
      (sF.table.lookup Ik).isSome = decide (Ik ∈ sL.sessions) ∧
      (Ik ∈ sL.sessions →
        (sL.sessions.idxOf Ik = j → sL.table.lookup Ik = some k_fs) ∧
        (sL.sessions.idxOf Ik ≠ j → sL.table.lookup Ik = sF.table.lookup Ik))) ∧
  (∀ t : ℕ, t ≠ mo.tStar →
    (sL.cache t = none ∧ sF.cache t = none) ∨
    ∃ Tc σc k, sL.cache t = some (Tc, σc, k, none) ∧ sF.cache t = some (Tc, σc, k, false)) ∧
  ((sL.cache mo.tStar = none ∧ sF.cache mo.tStar = none) ∨
    ∃ Tc σc kL kF idx,
      sL.cache mo.tStar = some (Tc, σc, kL, some idx) ∧
      sF.cache mo.tStar = some (Tc, σc, kF, idx == j) ∧
      (idx = j → kL = k_fs) ∧
      (idx ≠ j → kL = kF))

theorem bookSync_init (j : ℕ) (k_fs : K) :
    BookSync mo j k_fs ({} : LState T Sig K I) ({} : FSState T Sig K I SS RS E) := by
  refine ⟨rfl, List.nodup_nil, fun _ Ik => ⟨rfl, rfl, fun h => by cases h⟩,
    fun _ _ => Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩

theorem idxOf_append_singleton_of_mem {α : Type} [DecidableEq α] {l : List α} {a x : α}
    (hx : x ∈ l) : (l ++ [a]).idxOf x = l.idxOf x := by
  induction l with
  | nil => cases hx
  | cons y l ih =>
    simp only [List.cons_append, List.idxOf_cons]
    by_cases hxy : y == x
    · simp [hxy]
    · simp only [hxy, Bool.false_eq_true, ↓reduceIte]
      rcases List.mem_cons.mp hx with rfl | hx'
      · simp at hxy
      · rw [ih hx']

theorem idxOf_append_singleton_self {α : Type} [DecidableEq α] {l : List α} {a : α}
    (ha : a ∉ l) : (l ++ [a]).idxOf a = l.length := by
  induction l with
  | nil => simp
  | cons y l ih =>
    have hy : (y == a) = false := beq_eq_false_iff_ne.mpr ( fun h => ha (by simp [h]))
    have ha' : a ∉ l := fun h => ha (List.mem_cons_of_mem y h)
    simp [List.cons_append, List.idxOf_cons, hy, ih ha']

theorem bookSync_insert (j : ℕ) (k_fs : K) {sL : LState T Sig K I}
    {sF : FSState T Sig K I SS RS E} (hbs : BookSync mo j k_fs sL sF)
    (Ik : I) (hmem : Ik ∉ sL.sessions) (kL kF : K)
    (hk_eq : (sL.sessions.length = j → kL = k_fs) ∧ (sL.sessions.length ≠ j → kL = kF)) :
    BookSync mo j k_fs
      { sL with table := (Ik, kL) :: sL.table, sessions := sL.sessions ++ [Ik] }
      { sF with table := (Ik, kF) :: sF.table, sessions := sF.sessions ++ [Ik] } := by
  rcases hbs with ⟨hsess, hnodup, htab, hcache_ne, hcache_eq⟩
  refine ⟨by dsimp only; rw [hsess], ?_, ?_, hcache_ne, hcache_eq⟩
  · exact hnodup.append (List.nodup_singleton Ik) (fun x hx1 hx2 => by
      simp only [List.mem_singleton] at hx2; subst hx2; exact hmem hx1)
  · intro hnot_th Ik'
    obtain ⟨htL, htF, hidx⟩ := htab hnot_th Ik'
    dsimp only [List.lookup]
    by_cases heq : (Ik' == Ik) = true
    · have heq' : Ik' = Ik := beq_iff_eq.mp heq
      subst heq'
      simp only [heq, Option.isSome_some, List.mem_append, List.mem_singleton, or_true,
        decide_true, idxOf_append_singleton_self hmem, Option.some.injEq, true_and]
      intro _
      exact hk_eq
    · have hne : Ik' ≠ Ik := fun h => by subst h; simp at heq
      simp only [heq, List.mem_append, List.mem_singleton, hne, or_false]
      refine ⟨htL, htF, fun hmem' => ?_⟩
      rw [idxOf_append_singleton_of_mem hmem']
      exact hidx hmem'

theorem bookSync_update_cache (j : ℕ) (k_fs : K) {sL : LState T Sig K I}
    {sF : FSState T Sig K I SS RS E} (hbs : BookSync mo j k_fs sL sF)
    (t : ℕ) (Tc : T) (σ' : Sig) (kL kF : K) (idx? : Option ℕ) (ext : Bool)
    (h_tstar : t = mo.tStar →
      ∃ idx, idx? = some idx ∧ ext = (idx == j) ∧ (idx = j → kL = k_fs) ∧ (idx ≠ j → kL = kF))
    (h_ne : t ≠ mo.tStar → idx? = none ∧ ext = false ∧ kL = kF) :
    BookSync mo j k_fs
      { sL with cache := Function.update sL.cache t (some (Tc, σ', kL, idx?)) }
      { sF with cache := Function.update sF.cache t (some (Tc, σ', kF, ext)) } := by
  obtain ⟨hsess, hnodup, htab, hcache_ne, hcache_eq⟩ := hbs
  refine ⟨hsess, hnodup, htab, ?_, ?_⟩
  · intro t' ht'
    dsimp only
    by_cases heq : t' = t
    · subst heq
      obtain ⟨rfl, rfl, rfl⟩ := h_ne ht'
      simp only [Function.update_self]
      exact Or.inr ⟨Tc, σ', kL, rfl, rfl⟩
    · simp only [Function.update_of_ne heq]
      exact hcache_ne t' ht'
  · dsimp only
    by_cases heq : mo.tStar = t
    · subst heq
      obtain ⟨idx, rfl, rfl, h1, h2⟩ := h_tstar rfl
      simp only [Function.update_self]
      exact Or.inr ⟨Tc, σ', kL, kF, idx, rfl, rfl, h1, h2⟩
    · simp only [Function.update_of_ne heq]
      exact hcache_eq

theorem simulateQ_implFS_run_lift_sampleT {α : Type} [SampleableType α]
    (sF : FSState T Sig K I SS RS E) (st : FSGameState SS RS T M E) :
    (simulateQ (implFS fs)
      ((StateT.lift (sampleT α) :
        HM (FSAEAD.spec SS RS (Header T) M E) (FSState T Sig K I SS RS E) α).run sF)).run st =
      (($ᵗ α : ProbComp α) >>= fun a => pure ((a, sF), st)) := by
  have h1 : ((StateT.lift (sampleT α) :
      HM (FSAEAD.spec SS RS (Header T) M E) (FSState T Sig K I SS RS E) α).run sF) =
      (sampleT α >>= fun a => pure (a, sF)) := by
    simp [StateT.run_lift, map_eq_bind_pure_comp]
  rw [h1]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    simulateQ_sampleT_run, bind_assoc, pure_bind]

theorem leComp_lookup_regSess (j : ℕ) (k_fs : K) (Ik : I)
    {sL : LState T Sig K I} {sF : FSState T Sig K I SS RS E}
    (hbs : BookSync mo j k_fs sL sF)
    (hnot_th : ¬(mo.tL.isSome = true ∧ mo.tStar = mo.tH))
    (st : FSGameState SS RS T M E) :
    LeComp
      (fun (rL : (K × ℕ) × LState T Sig K I)
           (rF : ((K × Bool) × FSState T Sig K I SS RS E) × FSGameState SS RS T M E) =>
        rF.2 = st ∧
        rF.1.1.2 = (rL.1.2 == j) ∧
        (rL.1.2 = j → rL.1.1 = k_fs) ∧
        (rL.1.2 ≠ j → rL.1.1 = rF.1.1.1) ∧
        (sL.sessions = [] → rL.1.2 = 0) ∧
        rL.2.cache = sL.cache ∧
        rF.1.2.cache = sF.cache ∧
        rF.1.2.fsTrans = sF.fsTrans ∧
        rF.1.2.fsCount = sF.fsCount ∧
        rF.1.2.fsSCorr = sF.fsSCorr ∧
        rF.1.2.ext = sF.ext ∧
        BookSync mo j k_fs rL.2 rF.1.2)
      (simulateQ lImpl
        (((lookupFLFixed j k_fs Ik >>= fun k => regSess Ik >>= fun idx => pure (k, idx)) :
          HM nilSpec (LState T Sig K I) (K × ℕ)).run sL))
      ((simulateQ (implFS fs)
        (((lookupF Ik >>= fun k => isExt j Ik >>= fun ext => pure (k, ext)) :
          HM (FSAEAD.spec SS RS (Header T) M E) (FSState T Sig K I SS RS E) (K × Bool)).run sF)).run st) := by
  obtain ⟨hsess, hnodup, htab, hcache_ne, hcache_eq⟩ := hbs
  obtain ⟨htL, htF, hidx⟩ := htab hnot_th Ik
  unfold lookupFLFixed lookupF regSess isExt
  by_cases hmem : Ik ∈ sL.sessions
  · have hmemF : Ik ∈ sF.sessions := hsess ▸ hmem
    have hsomeL : ∃ kL, sL.table.lookup Ik = some kL := Option.isSome_iff_exists.mp (by simp [htL, hmem])
    have hsomeF : ∃ kF, sF.table.lookup Ik = some kF := Option.isSome_iff_exists.mp (by simp [htF, hmem])
    obtain ⟨kL, hkL⟩ := hsomeL
    obtain ⟨kF, hkF⟩ := hsomeF
    obtain ⟨h_eq_j, h_ne_j⟩ := hidx hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hkL, hkF, hmem, hmemF, ↓reduceIte,
      StateT.run_pure, simulateQ_pure]
    refine LeComp.pure ⟨rfl, ?_, ?_, ?_, fun hemp => by simp [hemp] at hmem,
      rfl, rfl, rfl, rfl, rfl, rfl, ⟨hsess, hnodup, htab, hcache_ne, hcache_eq⟩⟩
    · rw [hsess]
    · intro hj
      have := h_eq_j hj
      rw [hkL] at this
      exact Option.some.inj this
    · intro hne
      have := h_ne_j hne
      rw [hkL, hkF] at this
      exact Option.some.inj this
  · have hmemF : Ik ∉ sF.sessions := hsess ▸ hmem
    have hnoneL : sL.table.lookup Ik = none := by
      cases h : sL.table.lookup Ik with
      | none => rfl
      | some v => simp [h, hmem] at htL
    have hnoneF : sF.table.lookup Ik = none := by
      cases h : sF.table.lookup Ik with
      | none => rfl
      | some v => simp [h, hmem] at htF
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hnoneL, hnoneF,
      StateT.run_modify, hmem, hmemF, ↓reduceIte, StateT.run_set, StateT.run_pure,
      simulateQ_bind, simulateQ_pure, simulateQ_implFS_run_lift_sampleT,
      simulateQ_lImpl_run_lift_sampleT, bind_assoc]
    refine LeComp.sample_bind ($ᵗ K) fun k _ => ?_
    by_cases hlen_eq : sL.sessions.length = j
    · have hbeqL : (sL.sessions.length == j) = true := beq_iff_eq.mpr hlen_eq
      have hbeqF : (sF.sessions.length == j) = true := by rw [← hsess, hbeqL]
      simp only [hbeqL, hbeqF, ↓reduceIte]
      exact LeComp.pure ⟨rfl, hbeqL.symm, fun _ => rfl, fun hne => False.elim (hne hlen_eq),
        fun hemp => by simp [hemp], rfl, rfl, rfl, rfl, rfl, rfl,
        bookSync_insert mo j k_fs ⟨hsess, hnodup, htab, hcache_ne, hcache_eq⟩ Ik hmem k_fs k
          ⟨fun _ => rfl, fun hne => False.elim (hne hlen_eq)⟩⟩
    · have hbeqL : (sL.sessions.length == j) = false := beq_eq_false_iff_ne.mpr hlen_eq
      have hbeqF : (sF.sessions.length == j) = false := by rw [← hsess, hbeqL]
      simp only [hbeqL, hbeqF, Bool.false_eq_true, ↓reduceIte]
      exact LeComp.pure ⟨rfl, hbeqL.symm, fun hj => False.elim (hlen_eq hj), fun _ => rfl,
        fun hemp => by simp [hemp], rfl, rfl, rfl, rfl, rfl, rfl,
        bookSync_insert mo j k_fs ⟨hsess, hnodup, htab, hcache_ne, hcache_eq⟩ Ik hmem k k
          ⟨fun hj => False.elim (hlen_eq hj), fun _ => rfl⟩⟩

theorem leComp_root_regSessOf (j : ℕ) (k_fs : K) (t : ℕ) (Ik : I) (σ : Sig)
    {sL : LState T Sig K I} {sF : FSState T Sig K I SS RS E}
    (hbs : BookSync mo j k_fs sL sF)
    (hsess_empty : t = mo.tStar → mo.tL.isSome = true → t = mo.tH → sL.sessions = [])
    (st : FSGameState SS RS T M E) :
    LeComp
      (fun (rL : (Sig × K × Option ℕ) × LState T Sig K I)
           (rF : ((Sig × K × Bool) × FSState T Sig K I SS RS E) × FSGameState SS RS T M E) =>
        rF.2 = st ∧
        rL.1.1 = rF.1.1.1 ∧
        (t = mo.tStar →
          ∃ idx,
            rL.1.2.2 = some idx ∧
            rF.1.1.2.2 = (idx == j) ∧
            (idx = j → rL.1.2.1 = k_fs) ∧
            (idx ≠ j → rL.1.2.1 = rF.1.1.2.1) ∧
            (sL.sessions = [] → idx = 0)) ∧
        (t ≠ mo.tStar →
          rL.1.2.2 = none ∧
          rF.1.1.2.2 = false ∧
          rL.1.2.1 = rF.1.1.2.1 ∧
          rL.2.sessions = sL.sessions) ∧
        rL.2.cache = sL.cache ∧
        rF.1.2.cache = sF.cache ∧
        rF.1.2.fsTrans = sF.fsTrans ∧
        rF.1.2.fsCount = sF.fsCount ∧
        rF.1.2.fsSCorr = sF.fsSCorr ∧
        rF.1.2.ext = sF.ext ∧
        BookSync mo j k_fs rL.2 rF.1.2)
      (simulateQ lImpl
        (((rootLFixed prng mo j k_fs t Ik σ >>= fun (σ', k, sid) =>
            regSessOf sid >>= fun idx? => pure (σ', k, idx?)) :
          HM nilSpec (LState T Sig K I) (Sig × K × Option ℕ)).run sL))
      ((simulateQ (implFS fs)
        (((rootFS prng mo t Ik σ >>= fun (σ', k, sid) =>
            extOf j sid >>= fun ext => pure (σ', k, ext)) :
          HM (FSAEAD.spec SS RS (Header T) M E) (FSState T Sig K I SS RS E) (Sig × K × Bool)).run sF)).run st) := by
  unfold rootLFixed rootFS
  by_cases hgt : mo.tStar < t
  · have hne : t ≠ mo.tStar := by omega
    simp only [hgt, ↓reduceIte, regSessOf, extOf, StateT.run_bind, StateT.run_pure,
      pure_bind, simulateQ_pure]
    exact LeComp.pure ⟨rfl, rfl, fun h => False.elim (hne h),
      fun _ => ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, hbs⟩
  · simp only [hgt, ↓reduceIte]
    by_cases heq : t = mo.tStar
    · subst heq
      simp only [↓reduceIte]
      by_cases hth : (mo.tL.isSome && decide (mo.tStar = mo.tH)) = true
      · have hth' : mo.tL.isSome = true ∧ mo.tStar = mo.tH := by
          simpa [Bool.and_eq_true] using hth
        have hempL : sL.sessions = [] := hsess_empty rfl hth'.1 hth'.2
        have hempF : sF.sessions = [] := hbs.1 ▸ hempL
        simp only [hth'.1, hth'.2, decide_true, Bool.and_self, ↓reduceIte,
          regSessOf, regSess, extOf, isExt,
          StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_map, StateT.run_pure,
          simulateQ_bind, simulateQ_pure, simulateQ_lImpl_run_lift_sampleT,
          simulateQ_implFS_run_lift_sampleT, bind_assoc, pure_bind]
        refine LeComp.sample_bind ($ᵗ I) fun Ir _ => ?_
        refine LeComp.sample_bind ($ᵗ K) fun k _ => ?_
        simp only [hempL, hempF, List.not_mem_nil, not_false_eq_true, decide_true,
          Bool.true_and, List.length_nil, ↓reduceIte, List.nil_append,
          StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind]
        refine LeComp.pure ⟨rfl, rfl, ?_, fun hne => False.elim (hne rfl),
          rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
        · intro _
          refine ⟨0, rfl, rfl, ?_, ?_, fun _ => rfl⟩
          · intro h0j
            simp [h0j]
          · intro h0ne
            have hbeq : (0 == j) = false := beq_eq_false_iff_ne.mpr h0ne
            simp [hbeq]
        · refine ⟨rfl, List.nodup_singleton Ir, fun hnot => False.elim (hnot hth'),
            hbs.2.2.2.1, hbs.2.2.2.2⟩
      · have hnot_th : ¬(mo.tL.isSome = true ∧ mo.tStar = mo.tH) := by
          intro ⟨h1, h2⟩
          apply hth
          simp [h1, h2]
        have hth_false : (mo.tL.isSome && decide (mo.tStar = mo.tH)) = false :=
           Bool.eq_false_iff.mpr hth
        have h_eqL :
            simulateQ lImpl
              ((((lookupFLFixed j k_fs Ik >>= fun k => pure ((prng.up σ Ik).1, k, some Ik)) >>=
                fun (σ', k, sid) => regSessOf sid >>= fun idx? => pure (σ', k, idx?)) :
                HM nilSpec (LState T Sig K I) (Sig × K × Option ℕ)).run sL) =
            (simulateQ lImpl
              (((lookupFLFixed j k_fs Ik >>= fun k => regSess Ik >>= fun idx => pure (k, idx)) :
                HM nilSpec (LState T Sig K I) (K × ℕ)).run sL) >>= fun r =>
              pure (((prng.up σ Ik).1, r.1.1, some r.1.2), r.2)) := by
          simp [regSessOf, StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, bind_assoc]
        have h_eqF :
            (simulateQ (implFS fs)
              ((((lookupF Ik >>= fun k => pure ((prng.up σ Ik).1, k, some Ik)) >>=
                fun (σ', k, sid) => extOf j sid >>= fun ext => pure (σ', k, ext)) :
                HM (FSAEAD.spec SS RS (Header T) M E) (FSState T Sig K I SS RS E) (Sig × K × Bool)).run sF)).run st =
            ((simulateQ (implFS fs)
              (((lookupF Ik >>= fun k => isExt j Ik >>= fun ext => pure (k, ext)) :
                HM (FSAEAD.spec SS RS (Header T) M E) (FSState T Sig K I SS RS E) (K × Bool)).run sF)).run st >>= fun r =>
              pure ((((prng.up σ Ik).1, r.1.1.1, r.1.1.2), r.1.2), r.2)) := by
          simp [extOf, StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, bind_assoc]
        simp only [hth_false, Bool.false_eq_true, ↓reduceIte]
        rw [h_eqL, h_eqF]
        refine LeComp.bind (leComp_lookup_regSess fs mo j k_fs Ik hbs hnot_th st) ?_
        intro rL rF ⟨hr_st, hr_ext, hr_eq_j, hr_ne_j, hr_emp, hr_cL, hr_cF, hr_tr, hr_cnt, hr_sc, hr_ex, hr_bs⟩
        refine LeComp.pure ⟨hr_st, rfl, ?_, fun hne => False.elim (hne rfl),
          hr_cL, hr_cF, hr_tr, hr_cnt, hr_sc, hr_ex, hr_bs⟩
        intro _
        exact ⟨rL.1.2, rfl, hr_ext, hr_eq_j, hr_ne_j, hr_emp⟩
    · rw [ite_eq_right_iff.mpr (fun h => False.elim (heq h)),
          ite_eq_right_iff.mpr (fun h => False.elim (heq h))]
      by_cases hth : (mo.tL.isSome && decide (t = mo.tH)) = true
      · simp only [hth, ↓reduceIte, regSessOf, extOf,
          StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
          simulateQ_lImpl_run_lift_sampleT, simulateQ_implFS_run_lift_sampleT,
          bind_assoc, pure_bind]
        refine LeComp.sample_bind ($ᵗ I) fun Ir _ => ?_
        exact LeComp.pure ⟨rfl, rfl, fun h => False.elim (heq h),
          fun _ => ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, hbs⟩
      · simp only [hth, Bool.false_eq_true, ↓reduceIte, regSessOf, extOf,
          StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, pure_bind]
        exact LeComp.pure ⟨rfl, rfl, fun h => False.elim (heq h),
          fun _ => ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, hbs⟩

theorem leComp_lookup_regSess_bind {α β : Type} {R : α → β → Prop}
    (j : ℕ) (k_fs : K) (Ik : I)
    {sL : LState T Sig K I} {sF : FSState T Sig K I SS RS E}
    (hbs : BookSync mo j k_fs sL sF)
    (hnot_th : ¬(mo.tL.isSome = true ∧ mo.tStar = mo.tH))
    (st : FSGameState SS RS T M E)
    (fL : (K × ℕ) × LState T Sig K I → ProbComp α)
    (fF : ((K × Bool) × FSState T Sig K I SS RS E) × FSGameState SS RS T M E → ProbComp β)
    (hf : ∀ rL rF,
      (rF.2 = st ∧
       rF.1.1.2 = (rL.1.2 == j) ∧
       (rL.1.2 = j → rL.1.1 = k_fs) ∧
       (rL.1.2 ≠ j → rL.1.1 = rF.1.1.1) ∧
       (sL.sessions = [] → rL.1.2 = 0) ∧
       rL.2.cache = sL.cache ∧
       rF.1.2.cache = sF.cache ∧
       rF.1.2.fsTrans = sF.fsTrans ∧
       rF.1.2.fsCount = sF.fsCount ∧
       rF.1.2.fsSCorr = sF.fsSCorr ∧
       rF.1.2.ext = sF.ext ∧
       BookSync mo j k_fs rL.2 rF.1.2) →
      LeComp R (fL rL) (fF rF)) :
    LeComp R
      (simulateQ lImpl ((lookupFLFixed j k_fs Ik).run sL) >>= fun x =>
        simulateQ lImpl ((regSess Ik).run x.2) >>= fun x_1 =>
        fL ((x.1, x_1.1), x_1.2))
      ((simulateQ (implFS fs) ((lookupF Ik).run sF)).run st >>= fun p =>
        (simulateQ (implFS fs) ((isExt j Ik).run p.1.2)).run p.2 >>= fun p_1 =>
        fF (((p.1.1, p_1.1.1), p_1.1.2), p_1.2)) := by
  have h := LeComp.bind (leComp_lookup_regSess fs mo j k_fs Ik hbs hnot_th st) hf
  simpa only [StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
    bind_assoc, pure_bind] using h

theorem leComp_root_regSessOf_bind {α β : Type} {R : α → β → Prop}
    (j : ℕ) (k_fs : K) (t : ℕ) (Ik : I) (σ : Sig)
    {sL : LState T Sig K I} {sF : FSState T Sig K I SS RS E}
    (hbs : BookSync mo j k_fs sL sF)
    (hsess_empty : t = mo.tStar → mo.tL.isSome = true → t = mo.tH → sL.sessions = [])
    (st : FSGameState SS RS T M E)
    (fL : (Sig × K × Option ℕ) × LState T Sig K I → ProbComp α)
    (fF : ((Sig × K × Bool) × FSState T Sig K I SS RS E) × FSGameState SS RS T M E → ProbComp β)
    (hf : ∀ rL rF,
      (rF.2 = st ∧
       rL.1.1 = rF.1.1.1 ∧
       (t = mo.tStar →
         ∃ idx,
           rL.1.2.2 = some idx ∧
           rF.1.1.2.2 = (idx == j) ∧
           (idx = j → rL.1.2.1 = k_fs) ∧
           (idx ≠ j → rL.1.2.1 = rF.1.1.2.1) ∧
           (sL.sessions = [] → idx = 0)) ∧
       (t ≠ mo.tStar →
         rL.1.2.2 = none ∧
         rF.1.1.2.2 = false ∧
         rL.1.2.1 = rF.1.1.2.1 ∧
         rL.2.sessions = sL.sessions) ∧
       rL.2.cache = sL.cache ∧
       rF.1.2.cache = sF.cache ∧
       rF.1.2.fsTrans = sF.fsTrans ∧
       rF.1.2.fsCount = sF.fsCount ∧
       rF.1.2.fsSCorr = sF.fsSCorr ∧
       rF.1.2.ext = sF.ext ∧
       BookSync mo j k_fs rL.2 rF.1.2) →
      LeComp R (fL rL) (fF rF)) :
    LeComp R
      (simulateQ lImpl ((rootLFixed prng mo j k_fs t Ik σ).run sL) >>= fun x =>
        simulateQ lImpl ((regSessOf x.1.2.2).run x.2) >>= fun x_1 =>
        fL ((x.1.1, x.1.2.1, x_1.1), x_1.2))
      ((simulateQ (implFS fs) ((rootFS prng mo t Ik σ).run sF)).run st >>= fun p =>
        (simulateQ (implFS fs) ((extOf j p.1.1.2.2).run p.1.2)).run p.2 >>= fun p_1 =>
        fF (((p.1.1.1, p.1.1.2.1, p_1.1.1), p_1.1.2), p_1.2)) := by
  have h := LeComp.bind (leComp_root_regSessOf prng fs mo j k_fs t Ik σ hbs hsess_empty st) hf
  simpa only [StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
    bind_assoc, pure_bind] using h

/-! ### State invariant `SyncLFS` and oracle steps -/

theorem simulateQ_implFS_transmitQuery (h : Header T) (m : M)
    (sF : FSState T Sig K I SS RS E) (st : FSGameState SS RS T M E) :
    (simulateQ (implFS fs)
      ((liftF (FSAEAD.transmitQuery (SenderState := SS) (ReceiverState := RS) h m)).run sF)).run st =
      pure (((FSAEAD.transmit fs st h m).1, sF), (FSAEAD.transmit fs st h m).2) := by
  simp [liftF, StateT.run_lift, map_eq_bind_pure_comp, FSAEAD.transmitQuery,
    implFS, FSAEAD.oracleImpl, FSAEAD.transmitImpl, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet]
  rfl

theorem simulateQ_implFS_corruptSenderQuery
    (sF : FSState T Sig K I SS RS E) (st : FSGameState SS RS T M E) :
    (simulateQ (implFS fs)
      ((liftF (FSAEAD.corruptSenderQuery (ReceiverState := RS) (AssocData := Header T)
        (Message := M) (Ciphertext := E))).run sF)).run st =
      pure (((FSAEAD.corruptSender st).1, sF), (FSAEAD.corruptSender st).2) := by
  simp [liftF, StateT.run_lift, map_eq_bind_pure_comp, FSAEAD.corruptSenderQuery,
    implFS, FSAEAD.oracleImpl, FSAEAD.corruptSenderImpl, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet]
  rfl

theorem simulateQ_implFS_deliverQuery (h : Header T) (e : E)
    (sF : FSState T Sig K I SS RS E) (st : FSGameState SS RS T M E) :
    (simulateQ (implFS fs)
      ((liftF (FSAEAD.deliverQuery (SenderState := SS) (ReceiverState := RS) h e)).run sF)).run st =
      pure (((FSAEAD.deliver fs st h e).1, sF), (FSAEAD.deliver fs st h e).2) := by
  simp [liftF, StateT.run_lift, map_eq_bind_pure_comp, FSAEAD.deliverQuery,
    implFS, FSAEAD.oracleImpl, FSAEAD.deliverImpl, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet]
  rfl

theorem simulateQ_implFS_injectQuery (h : Header T) (e : E)
    (sF : FSState T Sig K I SS RS E) (st : FSGameState SS RS T M E) :
    (simulateQ (implFS fs)
      ((liftF (FSAEAD.injectQuery (SenderState := SS) (ReceiverState := RS) h e)).run sF)).run st =
      pure (((FSAEAD.inject fs st h e).1, sF), (FSAEAD.inject fs st h e).2) := by
  simp [liftF, StateT.run_lift, map_eq_bind_pure_comp, FSAEAD.injectQuery,
    implFS, FSAEAD.oracleImpl, FSAEAD.injectImpl, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet]
  rfl

def SenderIsJ (j : ℕ) (esL : EStateL Γ T Sig SS RS M E K I) : Prop :=
  (mo.tStar = 0 ∧ j = 0) ∨
  ∃ Tc σc k, esL.h.cache mo.tStar = some (Tc, σc, k, some j)

/-- Full synchronization invariant between `esL : EStateL`, `esF : EStateF`, and
`st : FSGameState`. -/
structure SyncLFS (j : ℕ) (k_fs : K)
    (esL : EStateL Γ T Sig SS RS M E K I)
    (esF : EStateF Γ T Sig SS RS M E K I)
    (st : FSGameState SS RS T M E) : Prop where
  habortL : esL.abort = false
  habortF : esF.abort = false
  hwinL : esL.g.win = false
  hwinF : esF.g.win = false
  hwinFS : st.win = false
  hendedFS : st.ended = false
  hchallFS : st.challengesInTransit = []
  hextF : esF.h.ext = none
  hepoch : esL.g.epoch = esF.g.epoch
  hidx : esL.g.idx = esF.g.idx
  htL : esL.g.tL = esF.g.tL
  htrans : esL.g.trans = esF.g.trans
  hchall : esL.g.chall = []
  hchallF : esF.g.chall = []
  hcomp : esL.g.comp = esF.g.comp
  hcomp_inv : ∀ pos ∈ esL.g.comp, healedBy esL.g.tL (2 + Δcka) pos.epoch = false
  hmaxAcc : esL.g.maxAcc = esF.g.maxAcc
  hb : esL.g.b = esF.g.b
  hleaks : esL.g.leaks = esF.g.leaks
  hcorrs : esL.g.corrs = esF.g.corrs
  hbs : BookSync mo j k_fs esL.h esF.h
  hcache_zero : esL.h.cache 0 = none
  hcache_gt : ∀ t, (esL.g.st (Party.senderOf t)).tcur < t → esL.h.cache t = none
  hsess_before :
    (esL.g.st (Party.senderOf mo.tStar)).tcur < mo.tStar →
    mo.tL.isSome = true → mo.tStar = mo.tH → esL.h.sessions = []
  hidL : ∀ P, (esL.g.st P).id = P
  hidF : ∀ P, (esF.g.st P).id = P
  hroot : ∀ P, (esL.g.st P).root = (esF.g.st P).root
  hγ : ∀ P, (esL.g.st P).γ = (esF.g.st P).γ
  hTcur : ∀ P, (esL.g.st P).curCkaMsg = (esF.g.st P).curCkaMsg
  htcur : ∀ P, (esL.g.st P).tcur = (esF.g.st P).tcur
  htcur_epoch : ∀ P, (esL.g.st P).tcur = esL.g.epoch P
  htcur_le_qep : ∀ P, P.sendsIn (esL.g.st P).tcur = true → (esL.g.st P).tcur ≤ qep
  hTcur_sender : ∀ P, P.sendsIn (esL.g.st P).tcur = true → 0 < (esL.g.st P).tcur →
    ∃ Tc σc k idx?, esL.h.cache (esL.g.st P).tcur = some (Tc, σc, k, idx?) ∧
      (esL.g.st P).curCkaMsg = some Tc
  hvS_some : ∀ P, P.sendsIn (esL.g.st P).tcur = true → (esL.g.st P).vS ≠ none
  hvS : ∀ P,
    ((esL.g.st P).vS = none ∧ (esF.g.st P).vS = none) ∨
    (∃ ss idx?, (esL.g.st P).vS = some (ss, idx?) ∧ (esF.g.st P).vS = some (some ss) ∧
      idx? ≠ some j ∧
      (P = Party.senderOf mo.tStar → (esL.g.st P).tcur = mo.tStar → ¬ SenderIsJ mo j esL)) ∨
    (P = Party.senderOf mo.tStar ∧
      mo.tStar ≤ (esL.g.st P).tcur ∧
      mo.tStar ≤ qep ∧
      (P.sendsIn (esL.g.st P).tcur = true →
        (esL.g.st P).tcur = mo.tStar ∧ st.lastSentIdx = esL.g.idx P) ∧
      SenderIsJ mo j esL ∧
      (esL.g.st P).vS = some (st.senderState, some j) ∧
      (esF.g.st P).vS = some none)
  hvR_other : ∀ P t, (P, t) ≠ (Party.receiverOf mo.tStar, mo.tStar) →
    ((esL.g.st P).vR t = none ∧ (esF.g.st P).vR t = none) ∨
    ∃ rs idx?, (esL.g.st P).vR t = some (rs, idx?) ∧ (esF.g.st P).vR t = some (some rs) ∧
      idx? ≠ some j
  hvR_target_lt :
    (esL.g.st (Party.receiverOf mo.tStar)).tcur < mo.tStar →
    (esL.g.st (Party.receiverOf mo.tStar)).vR mo.tStar = none ∧
    (esF.g.st (Party.receiverOf mo.tStar)).vR mo.tStar = none ∧
    st.receiverState = fs.initReceiver k_fs
  hvR_target_ge :
    mo.tStar ≤ (esL.g.st (Party.receiverOf mo.tStar)).tcur →
    SenderIsJ mo j esL ∧
    (esL.g.st (Party.receiverOf mo.tStar)).vR mo.tStar = some (st.receiverState, some j) ∧
    (esF.g.st (Party.receiverOf mo.tStar)).vR mo.tStar = some none
  hfsCount : esF.h.fsCount = st.lastSentIdx
  hfsTrans : esF.h.fsTrans = st.inTransit.map (fun r => (r.idx, r.ad, r.ct))
  hfsSCorr : esF.h.fsSCorr = st.senderCorruptedAt.isSome
  htrans_wf : ∀ r ∈ esL.g.trans,
    r.pos.epoch = r.ct.1.1 ∧
    r.pos.sender = Party.senderOf r.pos.epoch ∧
    r.pos.epoch ≤ (esL.g.st r.pos.sender).tcur ∧
    (0 < r.pos.epoch → ∃ Tc σc k idx?, esL.h.cache r.pos.epoch = some (Tc, σc, k, idx?) ∧
      r.ct.1 = (r.pos.epoch, some Tc)) ∧
    (r.pos.epoch = mo.tStar → SenderIsJ mo j esL → r.pos.idx ≤ st.lastSentIdx)
  hnot_senderJ : ¬ SenderIsJ mo j esL →
    st.senderState = fs.initSender k_fs ∧
    st.lastSentIdx = 0 ∧
    st.senderCorruptedAt = none ∧
    st.inTransit = []
  hsenderJ_trans : SenderIsJ mo j esL →
    st.inTransit = (esL.g.trans.filter (fun r => r.pos.epoch == mo.tStar)).map
      (fun r => ⟨r.pos.idx, r.ct.1, r.msg, r.ct.2⟩)
  hcorr_sync : ∀ corrAt, st.senderCorruptedAt = some corrAt →
    SenderIsJ mo j esL ∧
    mo.tStar ≤ qep ∧
    healedBy esL.g.tL (2 + Δcka) mo.tStar = false ∧
    (∀ r ∈ esL.g.trans, r.pos.epoch = mo.tStar → corrAt < r.pos.idx → r.pos ∈ esL.g.comp)

def StepRelFS {α : Type} (j : ℕ) (k_fs : K)
    (rL : α × EStateL Γ T Sig SS RS M E K I)
    (rF : (α × EStateF Γ T Sig SS RS M E K I) × FSGameState SS RS T M E) : Prop :=
  LHSDead Δcka mo j rL.2 ∨
  rF.2.win = true ∨
  (rL.1 = rF.1.1 ∧ SyncLFS fs Δcka qep mo j k_fs rL.2 rF.1.2 rF.2)

theorem lhsDead_of_abort (j : ℕ) (esL : EStateL Γ T Sig SS RS M E K I) :
    LHSDead Δcka mo j { esL with abort := true } := by
  exact Or.inl ⟨by simp, by simp [authOut]⟩

theorem leComp_challE (j : ℕ) (k_fs : K) (hauth : mo.auth = true)
    (q : Party × M × M × Option CCoins)
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st) :
    LeComp (StepRelFS fs Δcka qep mo j k_fs)
      (simulateQ lImpl
        ((challE (hooksLocalFixed cka prng fs mo j k_fs) (2 + Δcka) qep mo.cfg mo.policy q).run esL))
      ((simulateQ (implFS fs)
        ((challE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.cfg mo.policy q).run esF)).run st) := by
  rcases q with ⟨P, m₀, m₁, r⟩
  have hcfg : ∀ t, (mo.cfg (M := M)).challAllowedIn t = false := by
    intro t
    simp [Mode.cfg, hauth, Config.auth]
  unfold challE
  simp only [StateT.run_bind, StateT.run_get, pure_bind,
    hs.habortL, hs.habortF, hs.hwinL, hs.hwinF, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  cases esL.g.epMgmt (2 + Δcka) qep P r.isSome <;>
    cases esF.g.epMgmt (2 + Δcka) qep P r.isSome <;>
    simp only [hcfg, Bool.not_false, Bool.or_true, ↓reduceIte,
      StateT.run_pure, simulateQ_pure] <;>
    exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))

theorem corrDoom_true_of_ge (hauth : mo.auth = true)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    {St Msg C : Type} (g : GameState St Msg C)
    (hge : mo.tStar ≤ g.epoch (Party.receiverOf mo.tStar)) :
    mo.policy.corrDoom g (Party.receiverOf mo.tStar) = true := by
  simp only [Policy.corrDoom, Mode.policy, beq_self_eq_true, hauth, ↓reduceIte, Bool.true_and]
  simp only [lastLeakGuessAdmissible, healedBy] at hvg
  cases h : mo.tL with
  | none => rfl
  | some l =>
    rw [h] at hvg
    simp only [decide_eq_true_eq] at hvg
    simp only [ltOpt, decide_eq_true_eq]
    omega

theorem healedBy_leak_false_of_false {tL : Option ℕ} {Δ t l : ℕ}
    (h : healedBy tL Δ t = false) :
    healedBy (some (maxOpt tL l)) Δ t = false := by
  cases tL with
  | none => simp [healedBy] at h
  | some l₀ =>
    simp only [healedBy, decide_eq_false_iff_not] at h ⊢
    simp only [maxOpt, Nat.max_def]
    split <;> omega

theorem healedBy_leak_false_of_le {tL : Option ℕ} {Δ t l : ℕ}
    (hΔ : 0 < Δ) (hle : t ≤ l) :
    healedBy (some (maxOpt tL l)) Δ t = false := by
  simp only [healedBy, decide_eq_false_iff_not]
  cases tL with
  | none =>
    simp only [maxOpt]
    omega
  | some l₀ =>
    simp only [maxOpt, Nat.max_def]
    split <;> omega

theorem leComp_corrE (j : ℕ) (k_fs : K)
    (hauth : mo.auth = true)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    (P : Party)
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st) :
    LeComp (StepRelFS fs Δcka qep mo j k_fs)
      (simulateQ lImpl
        ((corrE (hooksLocalFixed cka prng fs mo j k_fs) mo.policy P).run esL))
      ((simulateQ (implFS fs)
        ((corrE (hooksFS cka prng fs Δcka mo j) mo.policy P).run esF)).run st) := by
  have hcorrAll : esF.g.corrAllowed P = esL.g.corrAllowed P := by
    simp only [GameState.corrAllowed, ← hs.hchallF, hs.hchall, ← hs.htrans, ← hs.hcomp]
  unfold corrE
  simp only [StateT.run_bind, StateT.run_get, pure_bind,
    hs.habortL, hs.habortF, hs.hwinL, hs.hwinF, Bool.false_or, hcorrAll]
  by_cases hallow : esL.g.corrAllowed P = true
  · simp only [hallow, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hdoom_eq :
        (mo.policy.leakDoom esF.g (esF.g.afterCorr P) || mo.policy.corrDoom esF.g P) =
        (mo.policy.leakDoom esL.g (esL.g.afterCorr P) || mo.policy.corrDoom esL.g P) := by
      simp only [Policy.leakDoom, Policy.corrDoom, GameState.afterCorr, GameState.leak,
        ← hs.hepoch, ← hs.htL, ← hs.hleaks]
    rw [hdoom_eq]
    by_cases hdoom :
        (mo.policy.leakDoom esL.g (esL.g.afterCorr P) || mo.policy.corrDoom esL.g P) = true
    · simp only [hdoom, ↓reduceIte, abortE, StateT.run_modify, pure_bind,
        StateT.run_pure, simulateQ_pure]
      exact LeComp.pure (Or.inl (lhsDead_of_abort Δcka mo j esL))
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte]
      have hnot_cdoom : mo.policy.corrDoom esL.g P = false := by
        cases h : mo.policy.corrDoom esL.g P
        · rfl
        · simp [h] at hdoom
      have hvR_tStar : (esF.g.st P).vR mo.tStar ≠ some none := by
        by_cases hP : P = Party.receiverOf mo.tStar
        · subst hP
          have hlt : (esL.g.st (Party.receiverOf mo.tStar)).tcur < mo.tStar := by
            rw [hs.htcur_epoch]
            by_contra hge
            have := corrDoom_true_of_ge Δcka mo hauth hvg esL.g (Nat.le_of_not_lt hge)
            rw [this] at hnot_cdoom
            cases hnot_cdoom
          rw [(hs.hvR_target_lt hlt).2.1]
          intro h; cases h
        · have hne : (P, mo.tStar) ≠ (Party.receiverOf mo.tStar, mo.tStar) :=
            fun h => hP (Prod.ext_iff.mp h).1
          rcases hs.hvR_other P mo.tStar hne with ⟨_, hF⟩ | ⟨rs, idx?, _, hF, _⟩ <;>
            · rw [hF]; intro h; cases h
      have hvR_eq : ∀ t,
          (match (esF.g.st P).vR t with
            | some (some rs) => some rs
            | some none => none
            | none => none) = ((esL.g.st P).vR t).map Prod.fst := by
        intro t
        by_cases hPt : (P, t) = (Party.receiverOf mo.tStar, mo.tStar)
        · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hPt
          have hlt : (esL.g.st (Party.receiverOf mo.tStar)).tcur < mo.tStar := by
            rw [hs.htcur_epoch]
            by_contra hge
            have := corrDoom_true_of_ge Δcka mo hauth hvg esL.g (Nat.le_of_not_lt hge)
            rw [this] at hnot_cdoom
            cases hnot_cdoom
          obtain ⟨hL, hF, _⟩ := hs.hvR_target_lt hlt
          rw [hL, hF]
          rfl
        · rcases hs.hvR_other P t hPt with ⟨hL, hF⟩ | ⟨rs, idx?, hL, hF, _⟩ <;>
            · rw [hL, hF]; rfl
      have hmatch_tStar :
          (match (esF.g.st P).vR mo.tStar with
            | some none =>
              do
                match (← get).ext with
                | some (_, rs) => pure (some (some rs))
                | none =>
                  if mo.auth then pure none
                  else do
                    match ← liftF (FSAEAD.corruptReceiverQuery (SenderState := SS)
                        (ReceiverState := RS) (AssocData := Header T) (Message := M)
                        (Ciphertext := E)) with
                    | none => pure none
                    | some (ss, rs) =>
                      modify fun (s : FSState T Sig K I SS RS E) => { s with ext := some (ss, rs) }
                      pure (some (some rs))
            | _ => pure (some none) :
                HM (FSAEAD.spec SS RS (Header T) M E) (FSState T Sig K I SS RS E)
                  (Option (Option RS))) = pure (some none) := by
        cases h : (esF.g.st P).vR mo.tStar with
        | none => rfl
        | some v =>
          cases v with
          | none => exact False.elim (hvR_tStar h)
          | some rs => rfl
      have hcorr_pres :
          ∀ corrAt, st.senderCorruptedAt = some corrAt →
            SenderIsJ mo j esL ∧
            mo.tStar ≤ qep ∧
            healedBy (esL.g.afterCorr P).tL (2 + Δcka) mo.tStar = false ∧
            (∀ r ∈ (esL.g.afterCorr P).trans,
              r.pos.epoch = mo.tStar → corrAt < r.pos.idx → r.pos ∈ (esL.g.afterCorr P).comp) := by
        intro corrAt hcorr
        obtain ⟨hsJ, hqep, hheal, hcomp_mem⟩ := hs.hcorr_sync corrAt hcorr
        refine ⟨hsJ, hqep, ?_, ?_⟩
        · dsimp only [GameState.afterCorr, GameState.leak]
          exact healedBy_leak_false_of_false hheal
        · intro r hr hepoch_r hlt_r
          dsimp only [GameState.afterCorr, GameState.leak] at hr ⊢
          exact List.mem_append_right _ (hcomp_mem r hr hepoch_r hlt_r)
      rcases hs.hvS P with ⟨hvSL, hvSF⟩ | ⟨ss, idx?, hvSL, hvSF, _, _⟩ |
          ⟨hP_s, hle_tcur, hqep_s, hsend_s, hsJ, hvSL, hvSF⟩
      · simp only [run_liftH, hooksLocalFixed, hooksFS, hvSL, hvSF, hmatch_tStar,
          StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind,
          simulateQ_pure]
        refine LeComp.pure (Or.inr (Or.inr ⟨?_, ?_⟩))
        · dsimp only [realParty, Option.map]
          congr 2 <;> first | exact (hs.hidL P).trans (hs.hidF P).symm |
            exact hs.hroot P | exact hs.hγ P |
            exact hs.hTcur P | exact hs.htcur P | (funext t; exact (hvR_eq t).symm)
        · exact { hs with
            htL := by simp [GameState.afterCorr, GameState.leak, hs.htL, hs.hepoch]
            hcomp := by simp [GameState.afterCorr, GameState.leak, hs.htrans, hs.hcomp]
            hcomp_inv := comp_inv_afterCorr esL.g (2 + Δcka) (by omega) P
              (fun r hr => by rw [← hs.htcur_epoch r.pos.sender]; exact (hs.htrans_wf r hr).2.2.1)
              hs.hcomp_inv
            hleaks := by simp [GameState.afterCorr, GameState.leak, hs.htL, hs.hepoch, hs.hleaks]
            hcorrs := by simp [GameState.afterCorr, GameState.leak, hs.hepoch, hs.hcorrs]
            hcorr_sync := hcorr_pres }
      · simp only [run_liftH, hooksLocalFixed, hooksFS, hvSL, hvSF, hmatch_tStar,
          StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind,
          simulateQ_pure]
        refine LeComp.pure (Or.inr (Or.inr ⟨?_, ?_⟩))
        · dsimp only [realParty, Option.map]
          congr 2 <;> first | exact (hs.hidL P).trans (hs.hidF P).symm |
            exact hs.hroot P | exact hs.hγ P |
            exact hs.hTcur P | exact hs.htcur P | (funext t; exact (hvR_eq t).symm)
        · exact { hs with
            htL := by simp [GameState.afterCorr, GameState.leak, hs.htL, hs.hepoch]
            hcomp := by simp [GameState.afterCorr, GameState.leak, hs.htrans, hs.hcomp]
            hcomp_inv := comp_inv_afterCorr esL.g (2 + Δcka) (by omega) P
              (fun r hr => by rw [← hs.htcur_epoch r.pos.sender]; exact (hs.htrans_wf r hr).2.2.1)
              hs.hcomp_inv
            hleaks := by simp [GameState.afterCorr, GameState.leak, hs.htL, hs.hepoch, hs.hleaks]
            hcorrs := by simp [GameState.afterCorr, GameState.leak, hs.hepoch, hs.hcorrs]
            hcorr_sync := hcorr_pres }
      · simp only [run_liftH, hooksLocalFixed, hooksFS, hvSL, hvSF, hmatch_tStar,
          StateT.run_bind, StateT.run_get, hs.hextF, pure_bind,
          simulateQ_bind, simulateQ_implFS_corruptSenderQuery, bind_assoc,
          FSAEAD.corruptSender, hs.hendedFS, Bool.false_eq_true, ↓reduceIte,
          StateT.run_modify, StateT.run_pure, simulateQ_pure]
        refine LeComp.pure (Or.inr (Or.inr ⟨?_, ?_⟩))
        · dsimp only [realParty, Option.map]
          congr 2 <;> first | exact (hs.hidL P).trans (hs.hidF P).symm |
            exact hs.hroot P | exact hs.hγ P |
            exact hs.hTcur P | exact hs.htcur P | (funext t; exact (hvR_eq t).symm)
        · refine { hs with
            hendedFS := rfl
            hextF := rfl
            htL := by simp [GameState.afterCorr, GameState.leak, hs.htL, hs.hepoch]
            hcomp := by simp [GameState.afterCorr, GameState.leak, hs.htrans, hs.hcomp]
            hcomp_inv := comp_inv_afterCorr esL.g (2 + Δcka) (by omega) P
              (fun r hr => by rw [← hs.htcur_epoch r.pos.sender]; exact (hs.htrans_wf r hr).2.2.1)
              hs.hcomp_inv
            hleaks := by simp [GameState.afterCorr, GameState.leak, hs.htL, hs.hepoch, hs.hleaks]
            hcorrs := by simp [GameState.afterCorr, GameState.leak, hs.hepoch, hs.hcorrs]
            hfsSCorr := rfl
            hnot_senderJ := fun hnot => False.elim (hnot hsJ)
            hcorr_sync := ?_ }
          intro corrAt hcorr
          dsimp only at hcorr
          injection hcorr with hcorr_eq
          subst hcorr_eq
          have hheal : healedBy (esL.g.afterCorr P).tL (2 + Δcka) mo.tStar = false := by
            dsimp only [GameState.afterCorr, GameState.leak]
            have hle_max : mo.tStar ≤ max (esL.g.epoch .A) (esL.g.epoch .B) := by
              have hep : mo.tStar ≤ esL.g.epoch P := by rwa [← hs.htcur_epoch P]
              cases P <;> omega
            exact healedBy_leak_false_of_le (by omega) hle_max
          refine ⟨hsJ, hqep_s, hheal, ?_⟩
          intro r hr hepoch_r hlt_r
          cases hsc : st.senderCorruptedAt with
          | none =>
            rw [hsc, Option.getD_none] at hlt_r
            have hle_idx := (hs.htrans_wf r hr).2.2.2.2 hepoch_r hsJ
            omega
          | some c₀ =>
            rw [hsc, Option.getD_some] at hlt_r
            exact (hcorr_pres c₀ hsc).2.2.2 r hr hepoch_r hlt_r
  · simp only [hallow, Bool.not_false, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))

theorem leComp_init (j : ℕ) (k_fs : K) (b_fs : Bool) :
    LeComp
      (fun (rL : Option (VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ) ×
                  VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ)) × LState T Sig K I)
           (rF : (Option (VP Γ T Sig (Option SS) (Option RS) ×
                  VP Γ T Sig (Option SS) (Option RS)) × FSState T Sig K I SS RS E) ×
                  FSGameState SS RS T M E) =>
        ∃ vAL vBL vAF vBF,
          rL.1 = some (vAL, vBL) ∧
          rF.1.1 = some (vAF, vBF) ∧
          let esL : EStateL Γ T Sig SS RS M E K I :=
            { g := { st := (fun P => match P with | .A => vAL | .B => vBL), b := false }, h := rL.2 }
          let esF : EStateF Γ T Sig SS RS M E K I :=
            { g := { st := (fun P => match P with | .A => vAF | .B => vBF), b := false }, h := rF.1.2 }
          LHSDead Δcka mo j esL ∨ SyncLFS fs Δcka qep mo j k_fs esL esF rF.2)
      (simulateQ lImpl ((initLocalFixed cka prng fs lam mo j k_fs).run {}))
      ((simulateQ (implFS fs) ((initFS cka prng fs lam mo j).run {})).run (FSAEAD.initState fs k_fs b_fs)) := by
  unfold initLocalFixed initFS
  simp only [StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
    simulateQ_lImpl_run_lift_sampleT, simulateQ_implFS_run_lift_sampleT, bind_assoc, pure_bind]
  refine LeComp.sample_bind ($ᵗ KR) fun kr _ => ?_
  refine LeComp.sample_bind ($ᵗ KC) fun kc _ => ?_
  refine leComp_root_regSessOf_bind prng fs mo j k_fs 0 lam (prng.init kr)
    (bookSync_init mo j k_fs) (fun _ _ _ => rfl) (FSAEAD.initState fs k_fs b_fs)
    (fun rL => pure (some (mkParties (cka.initA kc) (cka.initB kc) rL.1.1
      (fs.initSender rL.1.2.1, rL.1.2.2) (fs.initReceiver rL.1.2.1, rL.1.2.2)), rL.2))
    (fun rF => pure ((some (mkParties (cka.initA kc) (cka.initB kc) rF.1.1.1
      (if rF.1.1.2.2 = true then none else some (fs.initSender rF.1.1.2.1))
      (if rF.1.1.2.2 = true then none else some (fs.initReceiver rF.1.1.2.1))),
      rF.1.2), rF.2)) ?_
  intro rL rF ⟨hr_st, hr_σ, hr_tstar, hr_ne, hr_cL, hr_cF, hr_tr, hr_cnt, hr_sc, hr_ex, hr_bs⟩
  refine LeComp.pure ⟨_, _, _, _, rfl, rfl, ?_⟩
  let pL := mkParties (T := T) (cka.initA kc) (cka.initB kc) rL.1.1
    (fs.initSender rL.1.2.1, rL.1.2.2) (fs.initReceiver rL.1.2.1, rL.1.2.2)
  let esL₀ : EStateL Γ T Sig SS RS M E K I :=
    { g := { st := (fun P => match P with | .A => pL.1 | .B => pL.2), b := false }, h := rL.2 }
  have hrec0 : Party.receiverOf 0 = .A := rfl
  have hsend0 : Party.senderOf 0 = .B := rfl
  by_cases h0 : 0 = mo.tStar
  · obtain ⟨idx, hidx?, hext, h_eq_j, h_ne_j, hidx0⟩ := hr_tstar h0
    have hidx_zero : idx = 0 := hidx0 rfl
    subst hidx_zero
    by_cases hj0 : 0 = j
    · subst hj0
      have hkL : rL.1.2.1 = k_fs := h_eq_j rfl
      refine Or.inr ?_
      have hsJ : SenderIsJ mo 0 esL₀ := Or.inl ⟨h0.symm, rfl⟩
      exact {
        habortL := rfl
        habortF := rfl
        hwinL := rfl
        hwinF := rfl
        hwinFS := by rw [hr_st]; rfl
        hendedFS := by rw [hr_st]; rfl
        hchallFS := by rw [hr_st]; rfl
        hextF := hr_ex
        hepoch := rfl
        hidx := rfl
        htL := rfl
        htrans := rfl
        hchall := rfl
        hchallF := rfl
        hcomp := rfl
        hcomp_inv := fun _ h => by cases h
        hmaxAcc := rfl
        hb := rfl
        hleaks := rfl
        hcorrs := rfl
        hbs := hr_bs
        hcache_zero := by rw [hr_cL]
        hcache_gt := fun t _ => by rw [hr_cL]
        hsess_before := fun hlt => by simp [← h0, esL₀, pL, mkParties] at hlt
        hidL := fun P => by cases P <;> rfl
        hidF := fun P => by cases P <;> rfl
        hroot := fun P => by cases P <;> exact hr_σ
        hγ := fun P => by cases P <;> rfl
        hTcur := fun P => by cases P <;> rfl
        htcur := fun P => by cases P <;> rfl
        htcur_epoch := fun P => by cases P <;> rfl
        htcur_le_qep := fun P _ => by cases P <;> simp [esL₀, pL, mkParties]
        hTcur_sender := fun P _ hpos => by cases P <;> simp [esL₀, pL, mkParties] at hpos
        hvS_some := fun P hsends => by cases P <;> simp [Party.sendsIn, esL₀, pL, mkParties] at hsends ⊢
        hvS := fun P => by
          cases P
          · exact Or.inl ⟨rfl, rfl⟩
          · refine Or.inr (Or.inr ⟨by rw [← h0, hsend0], by simp [← h0, esL₀, pL, mkParties],
              by omega, fun _ => ⟨by simp [← h0, esL₀, pL, mkParties], by rw [hr_st]; rfl⟩,
              hsJ, ?_, ?_⟩)
            · simp [esL₀, pL, mkParties, hidx?, hkL, hr_st, FSAEAD.initState]
            · simp [mkParties, hext]
        hvR_other := fun P t hne => by
          cases P
          · have ht0 : t ≠ 0 := fun ht => hne (by subst ht; rw [← h0, hrec0])
            exact Or.inl ⟨by simp [esL₀, pL, mkParties, ht0], by simp [mkParties, ht0]⟩
          · exact Or.inl ⟨rfl, rfl⟩
        hvR_target_lt := fun hlt => by simp [← h0, esL₀, pL, mkParties] at hlt
        hvR_target_ge := fun _ => ⟨hsJ,
          by rw [← h0, hrec0]; simp [esL₀, pL, mkParties, hidx?, hkL, hr_st, FSAEAD.initState],
          by rw [← h0, hrec0]; simp [mkParties, hext]⟩
        hfsCount := by rw [hr_cnt, hr_st]; rfl
        hfsTrans := by rw [hr_tr, hr_st]; rfl
        hfsSCorr := by rw [hr_sc, hr_st]; rfl
        htrans_wf := fun r hr => by cases hr
        hnot_senderJ := fun hnot => False.elim (hnot hsJ)
        hsenderJ_trans := fun _ => by rw [hr_st]; rfl
        hcorr_sync := fun corrAt hcorr => by rw [hr_st] at hcorr; cases hcorr }
    · refine Or.inl (Or.inr ⟨rfl, rfl, fun P => by cases P <;> rfl, ?_, ?_⟩)
      · simp [← h0, esL₀, pL, mkParties]
      · intro rs hrs
        rw [← h0, hrec0] at hrs
        simp only [esL₀, pL, mkParties, ↓reduceIte, hidx?,
          Option.some.injEq, Prod.mk.injEq] at hrs
        exact hj0 hrs.2
  · obtain ⟨hidx?, hext, hk_eq, _⟩ := hr_ne h0
    have hgt0 : 0 < mo.tStar := Nat.pos_of_ne_zero (Ne.symm h0)
    have hnot_sJ : ¬ SenderIsJ mo j esL₀ := by
      rintro (⟨h1, _⟩ | ⟨Tc, σc, k, h2⟩)
      · exact h0 h1.symm
      · change rL.2.cache mo.tStar = _ at h2
        rw [hr_cL] at h2
        cases h2
    exact Or.inr {
      habortL := rfl
      habortF := rfl
      hwinL := rfl
      hwinF := rfl
      hwinFS := by rw [hr_st]; rfl
      hendedFS := by rw [hr_st]; rfl
      hchallFS := by rw [hr_st]; rfl
      hextF := hr_ex
      hepoch := rfl
      hidx := rfl
      htL := rfl
      htrans := rfl
      hchall := rfl
      hchallF := rfl
      hcomp := rfl
      hcomp_inv := fun _ h => by cases h
      hmaxAcc := rfl
      hb := rfl
      hleaks := rfl
      hcorrs := rfl
      hbs := hr_bs
      hcache_zero := by rw [hr_cL]
      hcache_gt := fun t _ => by rw [hr_cL]
      hsess_before := fun _ _ _ => (hr_ne h0).2.2.2
      hidL := fun P => by cases P <;> rfl
      hidF := fun P => by cases P <;> rfl
      hroot := fun P => by cases P <;> exact hr_σ
      hγ := fun P => by cases P <;> rfl
      hTcur := fun P => by cases P <;> rfl
      htcur := fun P => by cases P <;> rfl
      htcur_epoch := fun P => by cases P <;> rfl
      htcur_le_qep := fun P _ => by cases P <;> simp [mkParties]
      hTcur_sender := fun P _ hpos => by cases P <;> simp [mkParties] at hpos
      hvS_some := fun P hsends => by cases P <;> simp [Party.sendsIn, mkParties] at hsends ⊢
      hvS := fun P => by
        cases P
        · exact Or.inl ⟨rfl, rfl⟩
        · refine Or.inr (Or.inl ⟨fs.initSender rL.1.2.1, none,
            by simp [mkParties, hidx?], by simp [mkParties, hext, hk_eq],
            (by intro h; cases h), fun _ htcur => False.elim (h0 htcur)⟩)
      hvR_other := fun P t _ => by
        cases P
        · by_cases ht0 : t = 0
          · subst ht0
            exact Or.inr ⟨fs.initReceiver rL.1.2.1, none,
              by simp [mkParties, hidx?], by simp [mkParties, hext, hk_eq],
              (by intro h; cases h)⟩
          · exact Or.inl ⟨by simp [mkParties, ht0], by simp [mkParties, ht0]⟩
        · exact Or.inl ⟨rfl, rfl⟩
      hvR_target_lt := fun _ => by
        have hne0 : mo.tStar ≠ 0 := Ne.symm h0
        cases hR : Party.receiverOf mo.tStar <;>
          simp [mkParties, hne0, hr_st, FSAEAD.initState]
      hvR_target_ge := fun hge => by
        cases hR : Party.receiverOf mo.tStar <;>
          simp [hR, mkParties] at hge <;> omega
      hfsCount := by rw [hr_cnt, hr_st]; rfl
      hfsTrans := by rw [hr_tr, hr_st]; rfl
      hfsSCorr := by rw [hr_sc, hr_st]; rfl
      htrans_wf := fun r hr => by cases hr
      hnot_senderJ := fun _ => by rw [hr_st]; exact ⟨rfl, rfl, rfl, rfl⟩
      hsenderJ_trans := fun hsJ => False.elim (hnot_sJ hsJ)
      hcorr_sync := fun corrAt hcorr => by rw [hr_st] at hcorr; cases hcorr }

theorem bookSync_cache {j : ℕ} {k_fs : K} {sL : LState T Sig K I}
    {sF : FSState T Sig K I SS RS E} (hbs : BookSync mo j k_fs sL sF) (t : ℕ) :
    (sL.cache t = none ∧ sF.cache t = none) ∨
    ∃ Tc σc kL kF idx? ext,
      sL.cache t = some (Tc, σc, kL, idx?) ∧
      sF.cache t = some (Tc, σc, kF, ext) ∧
      ext = (idx? == some j) ∧
      (idx? = some j → kL = k_fs ∧ t = mo.tStar) ∧
      (idx? ≠ some j → kL = kF) ∧
      (t ≠ mo.tStar → idx? = none) := by
  rcases hbs with ⟨_, _, _, hcache_ne, hcache_eq⟩
  by_cases ht : t = mo.tStar
  · subst ht
    rcases hcache_eq with ⟨h1, h2⟩ | ⟨Tc, σc, kL, kF, idx, h1, h2, h3, h4⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨Tc, σc, kL, kF, some idx, idx == j, h1, h2, rfl,
        fun h => ⟨h3 (Option.some.inj h), rfl⟩,
        fun h => h4 (fun heq => h (congrArg some heq)),
        fun hne => False.elim (hne rfl)⟩
  · rcases hcache_ne t ht with ⟨h1, h2⟩ | ⟨Tc, σc, k, h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨Tc, σc, k, k, none, false, h1, h2, rfl,
        (fun h => by cases h), fun _ => rfl, fun _ => rfl⟩

theorem leComp_startSend_core (j : ℕ) (k_fs : K) (t : ℕ) (γ : Γ) (σ : Sig) (coins : CCoins)
    {sL : LState T Sig K I} {sF : FSState T Sig K I SS RS E}
    (hbs : BookSync mo j k_fs sL sF)
    (hsess_empty : t = mo.tStar → mo.tL.isSome = true → t = mo.tH → sL.sessions = [])
    (st : FSGameState SS RS T M E) :
    let c := cka.send γ coins
    LeComp
      (fun (rL : Option (Γ × T × Sig × (SS × Option ℕ)) × LState T Sig K I)
           (rF : (Option (Γ × T × Sig × Option SS) × FSState T Sig K I SS RS E) ×
                  FSGameState SS RS T M E) =>
        ∃ σ' kL kF idx? ext,
          rL.1 = some (c.1, c.2.1, σ', (fs.initSender kL, idx?)) ∧
          rF.1.1 = some (c.1, c.2.1, σ', if ext then none else some (fs.initSender kF)) ∧
          rF.2 = st ∧
          (t = mo.tStar →
            ∃ idx,
              idx? = some idx ∧
              ext = (idx == j) ∧
              (idx = j → kL = k_fs) ∧
              (idx ≠ j → kL = kF) ∧
              (sL.sessions = [] → idx = 0)) ∧
          (t ≠ mo.tStar →
            idx? = none ∧
            ext = false ∧
            kL = kF ∧
            rL.2.sessions = sL.sessions) ∧
          rL.2.cache = Function.update sL.cache t (some (c.2.1, σ', kL, idx?)) ∧
          rF.1.2.cache = Function.update sF.cache t (some (c.2.1, σ', kF, ext)) ∧
          rF.1.2.fsTrans = sF.fsTrans ∧
          rF.1.2.fsCount = sF.fsCount ∧
          rF.1.2.fsSCorr = sF.fsSCorr ∧
          rF.1.2.ext = sF.ext ∧
          BookSync mo j k_fs rL.2 rF.1.2)
      (do
        let x ← simulateQ lImpl ((rootLFixed prng mo j k_fs t (cka.send γ coins).2.2 σ).run sL)
        let x_1 ← simulateQ lImpl ((regSessOf x.1.2.2).run x.2)
        pure (some ((cka.send γ coins).1, (cka.send γ coins).2.1, x.1.1,
            (fs.initSender x.1.2.1, x_1.1)),
          { x_1.2 with cache :=
              Function.update x_1.2.cache t (some ((cka.send γ coins).2.1, x.1.1, x.1.2.1, x_1.1)) }))
      (do
        let p ← (simulateQ (implFS fs)
          ((rootFS prng mo t (cka.send γ coins).2.2 σ).run sF)).run st
        let p_1 ← (simulateQ (implFS fs) ((extOf j p.1.1.2.2).run p.1.2)).run p.2
        pure ((some ((cka.send γ coins).1, (cka.send γ coins).2.1, p.1.1.1,
            if p_1.1.1 = true then none else some (fs.initSender p.1.1.2.1)),
          { p_1.1.2 with cache :=
              Function.update p_1.1.2.cache t (some ((cka.send γ coins).2.1, p.1.1.1, p.1.1.2.1, p_1.1.1)) }),
          p_1.2)) := by
  intro c
  refine leComp_root_regSessOf_bind prng fs mo j k_fs t c.2.2 σ hbs hsess_empty st
    (fun rL => pure (some (c.1, c.2.1, rL.1.1, (fs.initSender rL.1.2.1, rL.1.2.2)),
      { rL.2 with cache := Function.update rL.2.cache t (some (c.2.1, rL.1.1, rL.1.2.1, rL.1.2.2)) }))
    (fun rF => pure ((some (c.1, c.2.1, rF.1.1.1,
        if rF.1.1.2.2 = true then none else some (fs.initSender rF.1.1.2.1)),
      { rF.1.2 with cache := Function.update rF.1.2.cache t (some (c.2.1, rF.1.1.1, rF.1.1.2.1, rF.1.1.2.2)) }),
      rF.2)) ?_
  intro rL rF ⟨hr_st, hr_σ, hr_tstar, hr_ne, hr_cL, hr_cF, hr_tr, hr_cnt, hr_sc, hr_ex, hr_bs⟩
  refine LeComp.pure ⟨rL.1.1, rL.1.2.1, rF.1.1.2.1, rL.1.2.2, rF.1.1.2.2,
    rfl, by rw [hr_σ], hr_st, hr_tstar, hr_ne, ?_, ?_, hr_tr, hr_cnt, hr_sc, hr_ex, ?_⟩
  · dsimp only; rw [hr_cL]
  · dsimp only; rw [hr_cF, hr_σ]
  · dsimp only
    rw [← hr_σ]
    refine bookSync_update_cache mo j k_fs hr_bs t c.2.1 rL.1.1 rL.1.2.1 rF.1.1.2.1 rL.1.2.2 rF.1.1.2.2
      ?_ ?_
    · intro ht
      obtain ⟨idx, h1, h2, h3, h4, _⟩ := hr_tstar ht
      exact ⟨idx, h1, h2, h3, h4⟩
    · intro ht
      obtain ⟨h1, h2, h3, _⟩ := hr_ne ht
      exact ⟨h1, h2, h3⟩

theorem leComp_startSend (j : ℕ) (k_fs : K)
    (ctxL : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E)
    (ctxF : Ctx Γ T Sig (Option SS) (Option RS) M E)
    (P : Party) (t : ℕ) (γ : Γ) (σ : Sig) (r : Option CCoins)
    {sL : LState T Sig K I} {sF : FSState T Sig K I SS RS E}
    (hbs : BookSync mo j k_fs sL sF)
    (hsess_empty : t = mo.tStar → mo.tL.isSome = true → t = mo.tH → sL.sessions = [])
    (st : FSGameState SS RS T M E) :
    LeComp
      (fun (rL : Option (Γ × T × Sig × (SS × Option ℕ)) × LState T Sig K I)
           (rF : (Option (Γ × T × Sig × Option SS) × FSState T Sig K I SS RS E) ×
                  FSGameState SS RS T M E) =>
        ∃ coins σ' kL kF idx? ext,
          let c := cka.send γ coins
          rL.1 = some (c.1, c.2.1, σ', (fs.initSender kL, idx?)) ∧
          rF.1.1 = some (c.1, c.2.1, σ', if ext then none else some (fs.initSender kF)) ∧
          rF.2 = st ∧
          (t = mo.tStar →
            ∃ idx,
              idx? = some idx ∧
              ext = (idx == j) ∧
              (idx = j → kL = k_fs) ∧
              (idx ≠ j → kL = kF) ∧
              (sL.sessions = [] → idx = 0)) ∧
          (t ≠ mo.tStar →
            idx? = none ∧
            ext = false ∧
            kL = kF ∧
            rL.2.sessions = sL.sessions) ∧
          rL.2.cache = Function.update sL.cache t (some (c.2.1, σ', kL, idx?)) ∧
          rF.1.2.cache = Function.update sF.cache t (some (c.2.1, σ', kF, ext)) ∧
          rF.1.2.fsTrans = sF.fsTrans ∧
          rF.1.2.fsCount = sF.fsCount ∧
          rF.1.2.fsSCorr = sF.fsSCorr ∧
          rF.1.2.ext = sF.ext ∧
          BookSync mo j k_fs rL.2 rF.1.2)
      (simulateQ lImpl (((hooksLocalFixed cka prng fs mo j k_fs).startSend ctxL P t γ σ r).run sL))
      ((simulateQ (implFS fs) (((hooksFS cka prng fs Δcka mo j).startSend ctxF P t γ σ r).run sF)).run st) := by
  cases r with
  | some coins =>
    simp only [hooksLocalFixed, hooksFS, StateT.run_bind, StateT.run_pure, StateT.run_modify,
      simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
    exact fun f g hfg =>
      leComp_startSend_core cka prng fs mo j k_fs t γ σ coins hbs hsess_empty st f g
        (fun a b ⟨σ', kL, kF, idx?, ext, h⟩ => hfg a b ⟨coins, σ', kL, kF, idx?, ext, h⟩)
  | none =>
    simp only [hooksLocalFixed, hooksFS, StateT.run_bind, StateT.run_pure, StateT.run_modify,
      simulateQ_bind, simulateQ_pure, simulateQ_lImpl_run_lift_sampleT,
      simulateQ_implFS_run_lift_sampleT, bind_assoc, pure_bind]
    refine LeComp.sample_bind ($ᵗ CCoins) fun coins _ => ?_
    exact fun f g hfg =>
      leComp_startSend_core cka prng fs mo j k_fs t γ σ coins hbs hsess_empty st f g
        (fun a b ⟨σ', kL, kF, idx?, ext, h⟩ => hfg a b ⟨coins, σ', kL, kF, idx?, ext, h⟩)

theorem leComp_startRecv (j : ℕ) (k_fs : K)
    (ctxL : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E)
    (ctxF : Ctx Γ T Sig (Option SS) (Option RS) M E)
    (P : Party) (t : ℕ) (γ : Γ) (σ : Sig) (Tn : T)
    {sL : LState T Sig K I} {sF : FSState T Sig K I SS RS E}
    (hbs : BookSync mo j k_fs sL sF)
    (st : FSGameState SS RS T M E) :
    LeComp
      (fun (rL : Option (Option (Γ × Sig × (RS × Option ℕ))) × LState T Sig K I)
           (rF : (Option (Option (Γ × Sig × Option RS)) × FSState T Sig K I SS RS E) ×
                  FSGameState SS RS T M E) =>
        rF.2 = st ∧
        rL.2.cache = sL.cache ∧
        rF.1.2.cache = sF.cache ∧
        rF.1.2.fsTrans = sF.fsTrans ∧
        rF.1.2.fsCount = sF.fsCount ∧
        rF.1.2.fsSCorr = sF.fsSCorr ∧
        rF.1.2.ext = sF.ext ∧
        BookSync mo j k_fs rL.2 rF.1.2 ∧
        ((rL.1 = none ∧ rF.1.1 = none) ∨
         (rL.1 = some none ∧ rF.1.1 = some none ∧ rL.2.sessions = sL.sessions) ∨
         (∃ σ' kL kF idx? ext,
           rL.1 = some (some ((cka.receive γ Tn).1, σ', (fs.initReceiver kL, idx?))) ∧
           rF.1.1 = some (some ((cka.receive γ Tn).1, σ',
             if ext then none else some (fs.initReceiver kF))) ∧
           ext = (idx? == some j) ∧
           (idx? = some j → kL = k_fs ∧ t = mo.tStar) ∧
           (idx? ≠ some j → kL = kF) ∧
           (t ≠ mo.tStar → idx? = none ∧ rL.2.sessions = sL.sessions) ∧
           ((∃ σc, sL.cache t = some (Tn, σc, kL, idx?) ∧ σ' = σc ∧ rL.2.sessions = sL.sessions) ∨
            (t = mo.tStar ∧ ¬ (mo.tL.isSome = true ∧ mo.tStar = mo.tH) ∧
             (∀ Tc σc k idx?, sL.cache t = some (Tc, σc, k, idx?) → Tc ≠ Tn) ∧
             ∃ idx, idx? = some idx ∧ (sL.sessions = [] → idx = 0))))))
      (simulateQ lImpl (((hooksLocalFixed cka prng fs mo j k_fs).startRecv ctxL P t γ σ Tn).run sL))
      ((simulateQ (implFS fs) (((hooksFS cka prng fs Δcka mo j).startRecv ctxF P t γ σ Tn).run sF)).run st) := by
  have hnone_case :
      ∀ (hno_cache : ∀ Tc σc k idx?, sL.cache t = some (Tc, σc, k, idx?) → Tc ≠ Tn),
      LeComp
        (fun (rL : Option (Option (Γ × Sig × (RS × Option ℕ))) × LState T Sig K I)
             (rF : (Option (Option (Γ × Sig × Option RS)) × FSState T Sig K I SS RS E) ×
                    FSGameState SS RS T M E) =>
          rF.2 = st ∧
          rL.2.cache = sL.cache ∧
          rF.1.2.cache = sF.cache ∧
          rF.1.2.fsTrans = sF.fsTrans ∧
          rF.1.2.fsCount = sF.fsCount ∧
          rF.1.2.fsSCorr = sF.fsSCorr ∧
          rF.1.2.ext = sF.ext ∧
          BookSync mo j k_fs rL.2 rF.1.2 ∧
          ((rL.1 = none ∧ rF.1.1 = none) ∨
           (rL.1 = some none ∧ rF.1.1 = some none ∧ rL.2.sessions = sL.sessions) ∨
           (∃ σ' kL kF idx? ext,
             rL.1 = some (some ((cka.receive γ Tn).1, σ', (fs.initReceiver kL, idx?))) ∧
             rF.1.1 = some (some ((cka.receive γ Tn).1, σ',
               if ext then none else some (fs.initReceiver kF))) ∧
             ext = (idx? == some j) ∧
             (idx? = some j → kL = k_fs ∧ t = mo.tStar) ∧
             (idx? ≠ some j → kL = kF) ∧
             (t ≠ mo.tStar → idx? = none ∧ rL.2.sessions = sL.sessions) ∧
             ((∃ σc, sL.cache t = some (Tn, σc, kL, idx?) ∧ σ' = σc ∧ rL.2.sessions = sL.sessions) ∨
              (t = mo.tStar ∧ ¬ (mo.tL.isSome = true ∧ mo.tStar = mo.tH) ∧
               (∀ Tc σc k idx?, sL.cache t = some (Tc, σc, k, idx?) → Tc ≠ Tn) ∧
               ∃ idx, idx? = some idx ∧ (sL.sessions = [] → idx = 0))))))
        (simulateQ lImpl
          ((if mo.auth && t = mo.tStar then
              if mo.tL.isSome && mo.tStar = mo.tH then pure none
              else do
                let kk := cka.receive γ Tn
                let k' ← lookupFLFixed j k_fs kk.2
                let idx ← regSess kk.2
                pure (some (some (kk.1, (prng.up σ kk.2).1, (fs.initReceiver k', some idx))))
            else pure (some none)).run sL))
        ((simulateQ (implFS fs)
          ((if mo.auth && t = mo.tStar then
              if mo.tL.isSome && mo.tStar = mo.tH then pure none
              else do
                let kk := cka.receive γ Tn
                let k' ← lookupF kk.2
                let ext ← isExt j kk.2
                pure (some (some (kk.1, (prng.up σ kk.2).1,
                  if ext then none else some (fs.initReceiver k'))))
            else pure (some none)).run sF)).run st) := by
    intro hno_cache
    by_cases h1 : mo.auth = true ∧ t = mo.tStar
    · rcases h1 with ⟨hauth_eq, rfl⟩
      simp only [hauth_eq, Bool.true_and, ↓reduceIte]
      by_cases h2 : mo.tL.isSome = true ∧ mo.tStar = mo.tH
      · simp only [h2.1, h2.2, Bool.true_and, ↓reduceIte, StateT.run_pure, simulateQ_pure]
        exact LeComp.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hbs, Or.inl ⟨rfl, rfl⟩⟩
      · simp only [Bool.and_eq_true, decide_eq_true_eq, h2, ↓reduceIte,
          StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
        refine leComp_lookup_regSess_bind fs mo j k_fs (cka.receive γ Tn).2 hbs h2 st
          (fun rL => pure (some (some ((cka.receive γ Tn).1, (prng.up σ (cka.receive γ Tn).2).1,
            (fs.initReceiver rL.1.1, some rL.1.2))), rL.2))
          (fun rF => pure ((some (some ((cka.receive γ Tn).1, (prng.up σ (cka.receive γ Tn).2).1,
            if rF.1.1.2 = true then none else some (fs.initReceiver rF.1.1.1))), rF.1.2), rF.2)) ?_
        intro rL rF ⟨hr_st, hr_ext, hr_eq_j, hr_ne_j, hr_idx0, hr_cL, hr_cF, hr_tr, hr_cnt, hr_sc, hr_ex, hr_bs⟩
        refine LeComp.pure ⟨hr_st, hr_cL, hr_cF, hr_tr, hr_cnt, hr_sc, hr_ex, hr_bs,
          Or.inr (Or.inr ⟨(prng.up σ (cka.receive γ Tn).2).1, rL.1.1, rF.1.1.1,
            some rL.1.2, rF.1.1.2, rfl, rfl, ?_, ?_, ?_, fun hne => False.elim (hne rfl),
            Or.inr ⟨trivial, by simp [h2], hno_cache, rL.1.2, rfl, hr_idx0⟩⟩)⟩
        · rw [hr_ext]; rfl
        · intro hsome_eq
          injection hsome_eq with hidx_eq
          exact ⟨hr_eq_j hidx_eq, trivial⟩
        · intro hsome_ne
          exact hr_ne_j (fun h => hsome_ne (congrArg some h))
    · simp only [Bool.and_eq_true, decide_eq_true_eq, h1, ↓reduceIte,
        StateT.run_pure, simulateQ_pure]
      exact LeComp.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hbs, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
  rcases bookSync_cache mo hbs t with ⟨hL_c, hF_c⟩ | ⟨Tc, σc, kL, kF, idx?, ext, hL_c, hF_c, hext, h_eq_j, h_ne_j, h_ne_t⟩
  · have hL_eq :
        simulateQ lImpl (((hooksLocalFixed cka prng fs mo j k_fs).startRecv ctxL P t γ σ Tn).run sL) =
        simulateQ lImpl
          ((if mo.auth && t = mo.tStar then
              if mo.tL.isSome && mo.tStar = mo.tH then pure none
              else do
                let kk := cka.receive γ Tn
                let k' ← lookupFLFixed j k_fs kk.2
                let idx ← regSess kk.2
                pure (some (some (kk.1, (prng.up σ kk.2).1, (fs.initReceiver k', some idx))))
            else pure (some none)).run sL) := by
      dsimp only [hooksLocalFixed]
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hL_c]
    have hF_eq :
        ((simulateQ (implFS fs) (((hooksFS cka prng fs Δcka mo j).startRecv ctxF P t γ σ Tn).run sF)).run st) =
        ((simulateQ (implFS fs)
          ((if mo.auth && t = mo.tStar then
              if mo.tL.isSome && mo.tStar = mo.tH then pure none
              else do
                let kk := cka.receive γ Tn
                let k' ← lookupF kk.2
                let ext ← isExt j kk.2
                pure (some (some (kk.1, (prng.up σ kk.2).1,
                  if ext then none else some (fs.initReceiver k'))))
            else pure (some none)).run sF)).run st) := by
      dsimp only [hooksFS]
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hF_c]
    rw [hL_eq, hF_eq]
    exact hnone_case (fun _ _ _ _ h => by rw [hL_c] at h; cases h)
  · by_cases hTc : Tc = Tn
    · subst hTc
      dsimp only [hooksLocalFixed, hooksFS]
      simp only [StateT.run_bind, StateT.run_get, pure_bind,
        hL_c, hF_c, ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact LeComp.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hbs,
        Or.inr (Or.inr ⟨σc, kL, kF, idx?, ext, rfl, rfl, hext, h_eq_j, h_ne_j,
          fun ht => ⟨h_ne_t ht, rfl⟩, Or.inl ⟨σc, rfl, rfl, rfl⟩⟩)⟩
    · have hL_eq :
          simulateQ lImpl (((hooksLocalFixed cka prng fs mo j k_fs).startRecv ctxL P t γ σ Tn).run sL) =
          simulateQ lImpl
            ((if mo.auth && t = mo.tStar then
                if mo.tL.isSome && mo.tStar = mo.tH then pure none
                else do
                  let kk := cka.receive γ Tn
                  let k' ← lookupFLFixed j k_fs kk.2
                  let idx ← regSess kk.2
                  pure (some (some (kk.1, (prng.up σ kk.2).1, (fs.initReceiver k', some idx))))
              else pure (some none)).run sL) := by
        dsimp only [hooksLocalFixed]
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hL_c, hTc, ↓reduceIte]
      have hF_eq :
          ((simulateQ (implFS fs) (((hooksFS cka prng fs Δcka mo j).startRecv ctxF P t γ σ Tn).run sF)).run st) =
          ((simulateQ (implFS fs)
            ((if mo.auth && t = mo.tStar then
                if mo.tL.isSome && mo.tStar = mo.tH then pure none
                else do
                  let kk := cka.receive γ Tn
                  let k' ← lookupF kk.2
                  let ext ← isExt j kk.2
                  pure (some (some (kk.1, (prng.up σ kk.2).1,
                    if ext then none else some (fs.initReceiver k'))))
              else pure (some none)).run sF)).run st) := by
        dsimp only [hooksFS]
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hF_c, hTc, ↓reduceIte]
      rw [hL_eq, hF_eq]
      refine hnone_case ?_
      intro Tc' σc' k' idx?' h
      rw [hL_c] at h
      injection h with h1
      injection h1 with hTc'
      exact hTc' ▸ hTc

theorem senderOf_eq_of_sendsIn {P : Party} {t : ℕ} (h : P.sendsIn t = true) :
    Party.senderOf t = P :=
  (eq_senderOf_of_sendsIn h).symm

theorem syncLFS_fsSend_corrupt (j : ℕ) (k_fs : K) (P : Party)
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st)
    (hsends : P.sendsIn (esL.g.st P).tcur = true)
    (htcur_s : (esL.g.st P).tcur = mo.tStar)
    (hsJ : SenderIsJ mo j esL)
    (hlast : st.lastSentIdx = esL.g.idx P)
    (hnsafe : esL.g.safeCh (2 + Δcka) P = false) :
    SyncLFS fs Δcka qep mo j k_fs esL
      { esF with h := { esF.h with fsSCorr := true } }
      { st with senderCorruptedAt := some (st.senderCorruptedAt.getD st.lastSentIdx) } := by
  refine { hs with
    hendedFS := hs.hendedFS
    hextF := hs.hextF
    hfsSCorr := rfl
    hnot_senderJ := fun hnot => False.elim (hnot hsJ)
    hcorr_sync := ?_ }
  intro corrAt hcorr
  dsimp only at hcorr
  injection hcorr with hcorr_eq
  subst hcorr_eq
  have hqep : mo.tStar ≤ qep := by
    have := hs.htcur_le_qep P hsends
    rwa [htcur_s] at this
  have hheal : healedBy esL.g.tL (2 + Δcka) mo.tStar = false := by
    have h1 := hnsafe
    simp only [GameState.safeCh, ← hs.htcur_epoch P, htcur_s] at h1
    exact h1
  refine ⟨hsJ, hqep, hheal, ?_⟩
  intro r hr hepoch_r hlt_r
  cases hsc : st.senderCorruptedAt with
  | none =>
    rw [hsc, Option.getD_none] at hlt_r
    have hle_idx := (hs.htrans_wf r hr).2.2.2.2 hepoch_r hsJ
    omega
  | some c₀ =>
    rw [hsc, Option.getD_some] at hlt_r
    exact (hs.hcorr_sync c₀ hsc).2.2.2 r hr hepoch_r hlt_r

def vSendTail {tspec : OracleSpec.{0, 0} ι} {Γv Sv SSv RSv HS : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (ctx : Ctx Γv T Sv SSv RSv M E) (P : Party) (vp₁ : VP Γv T Sv SSv RSv) (m : M) :
    HM tspec HS (Option (VP Γv T Sv SSv RSv × (Header T × E))) := do
  let h : Header T := (vp₁.tcur, vp₁.curCkaMsg)
  match vp₁.vS with
  | none => return some (vp₁, (h, default))
  | some v =>
    match ← hk.fsSend ctx P vp₁.tcur v h m none with
    | none => return none
    | some (v', e) => return some ({ vp₁ with vS := some v' }, (h, e))

def transmitTail {tspec : OracleSpec.{0, 0} ι} {Γv Sv SSv RSv HS : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (P : Party) (m : M)
    (g_abort : Ctx Γv T Sv SSv RSv M E)
    (es₁ : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    TComp tspec (Option (Header T × E) × EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :=
  (do
    match ← liftH (vSendTail hk es₁.g P (es₁.g.st P) m) with
    | none =>
      modify fun (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) =>
        { es with g := g_abort, abort := true }
      return none
    | some (st', c) =>
      modify fun (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) =>
        { es with
          g := es.g.record (2 + Δcka) P st' ⟨⟨P, es.g.epoch P, es.g.idx P + 1⟩, m, c⟩ false }
      return some c).run es₁

theorem leComp_transmitTail_ext_send (j : ℕ) (k_fs : K) (P : Party) (m : M)
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st)
    (hsends : P.sendsIn (esL.g.st P).tcur = true)
    (hP_s : P = Party.senderOf mo.tStar)
    (htcur_s : (esL.g.st P).tcur = mo.tStar)
    (hsJ : SenderIsJ mo j esL)
    (hvSL : (esL.g.st P).vS = some (st.senderState, some j))
    (hvSF : (esF.g.st P).vS = some none)
    (hlast : st.lastSentIdx = esL.g.idx P)
    (hcorr_if_nsafe : esL.g.safeCh (2 + Δcka) P = false → st.senderCorruptedAt.isSome = true) :
    let hdr : Header T := ((esL.g.st P).tcur, (esL.g.st P).curCkaMsg)
    let hdrF : Header T := ((esF.g.st P).tcur, (esF.g.st P).curCkaMsg)
    let o := fs.send st.senderState hdr m
    StepRelFS fs Δcka qep mo j k_fs
      (some (hdr, o.2),
        { esL with
          g := esL.g.record (2 + Δcka) P { esL.g.st P with vS := some (o.1, some j) }
            ⟨⟨P, esL.g.epoch P, esL.g.idx P + 1⟩, m, (hdr, o.2)⟩ false })
      ((some (hdrF, (fs.send st.senderState hdrF m).2),
        { esF with
          g := esF.g.record (2 + Δcka) P { esF.g.st P with vS := some none }
            ⟨⟨P, esF.g.epoch P, esF.g.idx P + 1⟩, m, (hdrF, (fs.send st.senderState hdrF m).2)⟩ false,
          h := { esF.h with
            fsCount := esF.h.fsCount + 1,
            fsTrans := (esF.h.fsCount + 1, hdrF, (fs.send st.senderState hdrF m).2) :: esF.h.fsTrans } }),
        { st with
          senderState := (fs.send st.senderState hdrF m).1,
          lastSentIdx := st.lastSentIdx + 1,
          inTransit := ⟨st.lastSentIdx + 1, hdrF, m, (fs.send st.senderState hdrF m).2⟩ :: st.inTransit }) := by
  intro hdr hdrF o
  have hhdr : hdrF = hdr := Prod.ext (hs.htcur P).symm (hs.hTcur P).symm
  refine Or.inr (Or.inr ⟨by simp [hhdr, o], ?_⟩)
  have hepoch_P : esL.g.epoch P = mo.tStar := by rw [← hs.htcur_epoch P, htcur_s]
  refine {
    habortL := hs.habortL
    habortF := hs.habortF
    hwinL := hs.hwinL
    hwinF := hs.hwinF
    hwinFS := hs.hwinFS
    hendedFS := hs.hendedFS
    hchallFS := hs.hchallFS
    hextF := hs.hextF
    hepoch := hs.hepoch
    hidx := by dsimp only [GameState.record]; rw [hs.hidx]
    htL := hs.htL
    htrans := by
      dsimp only [GameState.record]
      rw [hs.htrans, hs.hepoch, hs.hidx, hhdr]
    hchall := hs.hchall
    hchallF := hs.hchallF
    hcomp := by
      have hsafe_eq : esL.g.safeCh (2 + Δcka) P = esF.g.safeCh (2 + Δcka) P := by
        simp only [GameState.safeCh, hs.htL, hs.hepoch]
      dsimp only [GameState.record]
      rw [hsafe_eq, hs.hepoch, hs.hidx, hs.hcomp]
    hcomp_inv := comp_inv_record esL.g (2 + Δcka) P _ _ false rfl hs.hcomp_inv
    hmaxAcc := hs.hmaxAcc
    hb := hs.hb
    hleaks := hs.hleaks
    hcorrs := hs.hcorrs
    hbs := hs.hbs
    hcache_zero := hs.hcache_zero
    hcache_gt := fun t ht => by
      dsimp only [GameState.record] at ht
      by_cases hQ : Party.senderOf t = P
      · rw [hQ, Function.update_self] at ht
        exact hs.hcache_gt t (by rwa [hQ])
      · rw [Function.update_of_ne hQ] at ht
        exact hs.hcache_gt t ht
    hsess_before := fun hlt => by
      dsimp only [GameState.record] at hlt
      rw [← hP_s, Function.update_self] at hlt
      exact hs.hsess_before (by rwa [← hP_s])
    hidL := fun Q => by
      dsimp only [GameState.record]
      by_cases hQ : Q = P <;> simp [hQ, hs.hidL]
    hidF := fun Q => by
      dsimp only [GameState.record]
      by_cases hQ : Q = P <;> simp [hQ, hs.hidF]
    hroot := fun Q => by
      dsimp only [GameState.record]
      by_cases hQ : Q = P <;> simp [hQ, hs.hroot]
    hγ := fun Q => by
      dsimp only [GameState.record]
      by_cases hQ : Q = P <;> simp [hQ, hs.hγ]
    hTcur := fun Q => by
      dsimp only [GameState.record]
      by_cases hQ : Q = P <;> simp [hQ, hs.hTcur]
    htcur := fun Q => by
      dsimp only [GameState.record]
      by_cases hQ : Q = P <;> simp [hQ, hs.htcur]
    htcur_epoch := fun Q => by
      dsimp only [GameState.record]
      by_cases hQ : Q = P <;> simp [hQ, hs.htcur_epoch]
    htcur_le_qep := fun Q hQ_s => by
      dsimp only [GameState.record] at hQ_s ⊢
      by_cases hQ : Q = P
      · subst hQ; simp only [Function.update_self] at hQ_s ⊢; exact hs.htcur_le_qep Q hQ_s
      · simp only [Function.update_of_ne hQ] at hQ_s ⊢; exact hs.htcur_le_qep Q hQ_s
    hTcur_sender := fun Q hQ_s hpos => by
      dsimp only [GameState.record] at hQ_s hpos ⊢
      by_cases hQ : Q = P
      · subst hQ; simp only [Function.update_self] at hQ_s hpos ⊢; exact hs.hTcur_sender Q hQ_s hpos
      · simp only [Function.update_of_ne hQ] at hQ_s hpos ⊢; exact hs.hTcur_sender Q hQ_s hpos
    hvS_some := fun Q hQ_s => by
      dsimp only [GameState.record] at hQ_s ⊢
      by_cases hQ : Q = P
      · subst hQ; simp
      · simp only [Function.update_of_ne hQ] at hQ_s ⊢; exact hs.hvS_some Q hQ_s
    hvS := fun Q => by
      dsimp only [GameState.record]
      by_cases hQ : Q = P
      · subst hQ
        have hqep_s : mo.tStar ≤ qep := by
          rw [← htcur_s]
          exact hs.htcur_le_qep Q hsends
        refine Or.inr (Or.inr ⟨hP_s, by simp [htcur_s], hqep_s,
          fun _ => ⟨by simp [htcur_s], by simp [hlast]⟩, hsJ, ?_, by simp⟩)
        simp [hhdr, o]
      · simp only [Function.update_of_ne hQ]
        rcases hs.hvS Q with ⟨h1, h2⟩ | ⟨ss, idx?, h1, h2, h3, h4⟩ | ⟨hQ_s, _⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr (Or.inl ⟨ss, idx?, h1, h2, h3, h4⟩)
        · exact False.elim (hQ (hQ_s.trans hP_s.symm))
    hvR_other := fun Q t hne => by
      dsimp only [GameState.record]
      by_cases hQ : Q = P
      · subst hQ; simp only [Function.update_self]; exact hs.hvR_other Q t hne
      · simp only [Function.update_of_ne hQ]; exact hs.hvR_other Q t hne
    hvR_target_lt := fun hlt => by
      dsimp only [GameState.record] at hlt ⊢
      by_cases hQ : Party.receiverOf mo.tStar = P
      · have hlt' : (esL.g.st (Party.receiverOf mo.tStar)).tcur < mo.tStar := by
          simpa only [hQ, Function.update_self] using hlt
        simpa only [hQ, Function.update_self] using hs.hvR_target_lt hlt'
      · have hlt' : (esL.g.st (Party.receiverOf mo.tStar)).tcur < mo.tStar := by
          simpa only [Function.update_of_ne hQ] using hlt
        simpa only [Function.update_of_ne hQ] using hs.hvR_target_lt hlt'
    hvR_target_ge := fun hge => by
      dsimp only [GameState.record, SenderIsJ] at hge ⊢
      by_cases hQ : Party.receiverOf mo.tStar = P
      · have hge' : mo.tStar ≤ (esL.g.st (Party.receiverOf mo.tStar)).tcur := by
          simpa only [hQ, Function.update_self] using hge
        simpa only [hQ, Function.update_self, SenderIsJ] using hs.hvR_target_ge hge'
      · have hge' : mo.tStar ≤ (esL.g.st (Party.receiverOf mo.tStar)).tcur := by
          simpa only [Function.update_of_ne hQ] using hge
        simpa only [Function.update_of_ne hQ, SenderIsJ] using hs.hvR_target_ge hge'
    hfsCount := by dsimp only; rw [hs.hfsCount]
    hfsTrans := by dsimp only [List.map]; rw [hs.hfsCount, hs.hfsTrans]
    hfsSCorr := hs.hfsSCorr
    htrans_wf := fun r hr => by
      dsimp only [GameState.record] at hr ⊢
      rcases List.mem_cons.mp hr with rfl | hr'
      · refine ⟨(hs.htcur_epoch P).symm, by rw [hepoch_P, hP_s], ?_, ?_, ?_⟩
        · simp [hs.htcur_epoch P]
        · intro hpos
          dsimp only at hpos ⊢
          rw [← hs.htcur_epoch P] at hpos ⊢
          obtain ⟨Tc, σc, k, idx?, h1, h2⟩ := hs.hTcur_sender P hsends hpos
          exact ⟨Tc, σc, k, idx?, h1, by simp [hdr, h2]⟩
        · intro _ _
          dsimp only
          omega
      · obtain ⟨h1, h2, h3, h4, h5⟩ := hs.htrans_wf r hr'
        refine ⟨h1, h2, ?_, h4, fun he hsJ' => ?_⟩
        · by_cases hQ : r.pos.sender = P
          · rw [hQ, Function.update_self]; exact hQ ▸ h3
          · rw [Function.update_of_ne hQ]; exact h3
        · have := h5 he hsJ'
          omega
    hnot_senderJ := fun hnot => False.elim (hnot hsJ)
    hsenderJ_trans := fun _ => by
      dsimp only [GameState.record, List.filter]
      have hbeq : (esL.g.epoch P == mo.tStar) = true := beq_iff_eq.mpr hepoch_P
      rw [hbeq]
      dsimp only [↓reduceIte, List.map]
      rw [hs.hsenderJ_trans hsJ, hlast, hhdr]
    hcorr_sync := fun corrAt hcorr => by
      obtain ⟨_, hqep, hheal, hcomp_mem⟩ := hs.hcorr_sync corrAt hcorr
      refine ⟨hsJ, hqep, hheal, ?_⟩
      intro r hr hepoch_r hlt_r
      dsimp only [GameState.record] at hr ⊢
      have hnsafe_P : esL.g.safeCh (2 + Δcka) P = false := by
        simp only [GameState.safeCh, hepoch_P]
        exact hheal
      simp only [hnsafe_P, Bool.false_eq_true, ↓reduceIte]
      rcases List.mem_cons.mp hr with rfl | hr'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hcomp_mem r hr' hepoch_r hlt_r) }

theorem leComp_transmitTail_nonext_send (j : ℕ) (k_fs : K) (P : Party) (m : M)
    (ss : SS) (idx? : Option ℕ)
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st)
    (hsends : P.sendsIn (esL.g.st P).tcur = true)
    (hvSL : (esL.g.st P).vS = some (ss, idx?))
    (hvSF : (esF.g.st P).vS = some (some ss))
    (hne_j : idx? ≠ some j)
    (hnot_sJ : P = Party.senderOf mo.tStar → (esL.g.st P).tcur = mo.tStar → ¬ SenderIsJ mo j esL) :
    let hdr : Header T := ((esL.g.st P).tcur, (esL.g.st P).curCkaMsg)
    let hdrF : Header T := ((esF.g.st P).tcur, (esF.g.st P).curCkaMsg)
    let o := fs.send ss hdr m
    let oF := fs.send ss hdrF m
    StepRelFS fs Δcka qep mo j k_fs
      (some (hdr, o.2),
        { esL with
          g := esL.g.record (2 + Δcka) P { esL.g.st P with vS := some (o.1, idx?) }
            ⟨⟨P, esL.g.epoch P, esL.g.idx P + 1⟩, m, (hdr, o.2)⟩ false })
      ((some (hdrF, oF.2),
        { esF with
          g := esF.g.record (2 + Δcka) P { esF.g.st P with vS := some (some oF.1) }
            ⟨⟨P, esF.g.epoch P, esF.g.idx P + 1⟩, m, (hdrF, oF.2)⟩ false }),
        st) := by
  intro hdr hdrF o oF
  have hhdr : hdrF = hdr := Prod.ext (hs.htcur P).symm (hs.hTcur P).symm
  have ho : oF = o := by dsimp only [o, oF]; rw [hhdr]
  refine Or.inr (Or.inr ⟨by simp [hhdr, ho], ?_⟩)
  have hepoch_sends : P.sendsIn (esL.g.epoch P) = true := by rw [← hs.htcur_epoch P]; exact hsends
  have hsender_ep : Party.senderOf (esL.g.epoch P) = P := senderOf_eq_of_sendsIn hepoch_sends
  have hnot_ep_sJ : esL.g.epoch P = mo.tStar → ¬ SenderIsJ mo j esL := by
    intro hep
    apply hnot_sJ
    · rw [← hep, hsender_ep]
    · rw [hs.htcur_epoch P, hep]
  refine {
    habortL := hs.habortL
    habortF := hs.habortF
    hwinL := hs.hwinL
    hwinF := hs.hwinF
    hwinFS := hs.hwinFS
    hendedFS := hs.hendedFS
    hchallFS := hs.hchallFS
    hextF := hs.hextF
    hepoch := hs.hepoch
    hidx := by dsimp only [GameState.record]; rw [hs.hidx]
    htL := hs.htL
    htrans := by
      dsimp only [GameState.record]
      rw [hs.htrans, hs.hepoch, hs.hidx, hhdr, ho]
    hchall := hs.hchall
    hchallF := hs.hchallF
    hcomp := by
      have hsafe_eq : esL.g.safeCh (2 + Δcka) P = esF.g.safeCh (2 + Δcka) P := by
        simp only [GameState.safeCh, hs.htL, hs.hepoch]
      dsimp only [GameState.record]
      rw [hsafe_eq, hs.hepoch, hs.hidx, hs.hcomp]
    hcomp_inv := comp_inv_record esL.g (2 + Δcka) P _ _ false rfl hs.hcomp_inv
    hmaxAcc := hs.hmaxAcc
    hb := hs.hb
    hleaks := hs.hleaks
    hcorrs := hs.hcorrs
    hbs := hs.hbs
    hcache_zero := hs.hcache_zero
    hcache_gt := fun t ht => by
      dsimp only [GameState.record] at ht
      by_cases hQ : Party.senderOf t = P
      · rw [hQ, Function.update_self] at ht
        exact hs.hcache_gt t (by rwa [hQ])
      · rw [Function.update_of_ne hQ] at ht
        exact hs.hcache_gt t ht
    hsess_before := fun hlt => by
      dsimp only [GameState.record] at hlt
      by_cases hQ : Party.senderOf mo.tStar = P
      · rw [hQ, Function.update_self] at hlt
        exact hs.hsess_before (by rwa [hQ])
      · rw [Function.update_of_ne hQ] at hlt
        exact hs.hsess_before hlt
    hidL := fun Q => by
      dsimp only [GameState.record]
      by_cases hQ : Q = P <;> simp [hQ, hs.hidL]
    hidF := fun Q => by
      dsimp only [GameState.record]
      by_cases hQ : Q = P <;> simp [hQ, hs.hidF]
    hroot := fun Q => by
      dsimp only [GameState.record]
      by_cases hQ : Q = P <;> simp [hQ, hs.hroot]
    hγ := fun Q => by
      dsimp only [GameState.record]
      by_cases hQ : Q = P <;> simp [hQ, hs.hγ]
    hTcur := fun Q => by
      dsimp only [GameState.record]
      by_cases hQ : Q = P <;> simp [hQ, hs.hTcur]
    htcur := fun Q => by
      dsimp only [GameState.record]
      by_cases hQ : Q = P <;> simp [hQ, hs.htcur]
    htcur_epoch := fun Q => by
      dsimp only [GameState.record]
      by_cases hQ : Q = P <;> simp [hQ, hs.htcur_epoch]
    htcur_le_qep := fun Q hQ_s => by
      dsimp only [GameState.record] at hQ_s ⊢
      by_cases hQ : Q = P
      · subst hQ; simp only [Function.update_self] at hQ_s ⊢; exact hs.htcur_le_qep Q hQ_s
      · simp only [Function.update_of_ne hQ] at hQ_s ⊢; exact hs.htcur_le_qep Q hQ_s
    hTcur_sender := fun Q hQ_s hpos => by
      dsimp only [GameState.record] at hQ_s hpos ⊢
      by_cases hQ : Q = P
      · subst hQ; simp only [Function.update_self] at hQ_s hpos ⊢; exact hs.hTcur_sender Q hQ_s hpos
      · simp only [Function.update_of_ne hQ] at hQ_s hpos ⊢; exact hs.hTcur_sender Q hQ_s hpos
    hvS_some := fun Q hQ_s => by
      dsimp only [GameState.record] at hQ_s ⊢
      by_cases hQ : Q = P
      · subst hQ; simp
      · simp only [Function.update_of_ne hQ] at hQ_s ⊢; exact hs.hvS_some Q hQ_s
    hvS := fun Q => by
      dsimp only [GameState.record]
      by_cases hQ : Q = P
      · subst hQ
        refine Or.inr (Or.inl ⟨o.1, idx?, by simp, by simp [ho], hne_j, ?_⟩)
        intro hQ_s htcur_Q
        simp only [Function.update_self] at htcur_Q
        exact hnot_sJ hQ_s htcur_Q
      · simp only [Function.update_of_ne hQ]
        rcases hs.hvS Q with ⟨h1, h2⟩ | ⟨ss', idx'?, h1, h2, h3, h4⟩ |
          ⟨hQ_s, h1, h2, h3, h4, h5, h6⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr (Or.inl ⟨ss', idx'?, h1, h2, h3, h4⟩)
        · exact Or.inr (Or.inr ⟨hQ_s, h1, h2, fun hQ_send => by simp [hQ, h3 hQ_send], h4, h5, h6⟩)
    hvR_other := fun Q t hne => by
      dsimp only [GameState.record]
      by_cases hQ : Q = P
      · subst hQ; simp only [Function.update_self]; exact hs.hvR_other Q t hne
      · simp only [Function.update_of_ne hQ]; exact hs.hvR_other Q t hne
    hvR_target_lt := fun hlt => by
      dsimp only [GameState.record] at hlt ⊢
      by_cases hQ : Party.receiverOf mo.tStar = P
      · have hlt' : (esL.g.st (Party.receiverOf mo.tStar)).tcur < mo.tStar := by
          simpa only [hQ, Function.update_self] using hlt
        simpa only [hQ, Function.update_self] using hs.hvR_target_lt hlt'
      · have hlt' : (esL.g.st (Party.receiverOf mo.tStar)).tcur < mo.tStar := by
          simpa only [Function.update_of_ne hQ] using hlt
        simpa only [Function.update_of_ne hQ] using hs.hvR_target_lt hlt'
    hvR_target_ge := fun hge => by
      dsimp only [GameState.record, SenderIsJ] at hge ⊢
      by_cases hQ : Party.receiverOf mo.tStar = P
      · have hge' : mo.tStar ≤ (esL.g.st (Party.receiverOf mo.tStar)).tcur := by
          simpa only [hQ, Function.update_self] using hge
        simpa only [hQ, Function.update_self, SenderIsJ] using hs.hvR_target_ge hge'
      · have hge' : mo.tStar ≤ (esL.g.st (Party.receiverOf mo.tStar)).tcur := by
          simpa only [Function.update_of_ne hQ] using hge
        simpa only [Function.update_of_ne hQ, SenderIsJ] using hs.hvR_target_ge hge'
    hfsCount := hs.hfsCount
    hfsTrans := hs.hfsTrans
    hfsSCorr := hs.hfsSCorr
    htrans_wf := fun r hr => by
      dsimp only [GameState.record] at hr ⊢
      rcases List.mem_cons.mp hr with rfl | hr'
      · refine ⟨(hs.htcur_epoch P).symm, hsender_ep.symm, ?_, ?_, ?_⟩
        · simp [hs.htcur_epoch P]
        · intro hpos
          dsimp only at hpos ⊢
          rw [← hs.htcur_epoch P] at hpos ⊢
          obtain ⟨Tc, σc, k, idx?, h1, h2⟩ := hs.hTcur_sender P hsends hpos
          exact ⟨Tc, σc, k, idx?, h1, by simp [hdr, h2]⟩
        · intro hep hsJ'
          exact False.elim (hnot_ep_sJ hep hsJ')
      · obtain ⟨h1, h2, h3, h4, h5⟩ := hs.htrans_wf r hr'
        refine ⟨h1, h2, ?_, h4, fun he hsJ' => h5 he hsJ'⟩
        by_cases hQ : r.pos.sender = P
        · rw [hQ, Function.update_self]; exact hQ ▸ h3
        · rw [Function.update_of_ne hQ]; exact h3
    hnot_senderJ := hs.hnot_senderJ
    hsenderJ_trans := fun hsJ => by
      dsimp only [GameState.record, List.filter]
      have hne_ep : (esL.g.epoch P == mo.tStar) = false :=
        beq_eq_false_iff_ne.mpr (fun hep => hnot_ep_sJ hep hsJ)
      rw [hne_ep]
      dsimp only [Bool.false_eq_true, ↓reduceIte]
      exact hs.hsenderJ_trans hsJ
    hcorr_sync := fun corrAt hcorr => by
      obtain ⟨hsJ, hqep, hheal, hcomp_mem⟩ := hs.hcorr_sync corrAt hcorr
      refine ⟨hsJ, hqep, hheal, ?_⟩
      intro r hr hepoch_r hlt_r
      dsimp only [GameState.record] at hr ⊢
      rcases List.mem_cons.mp hr with rfl | hr'
      · exact False.elim (hnot_ep_sJ hepoch_r hsJ)
      · have hmem := hcomp_mem r hr' hepoch_r hlt_r
        by_cases hsafe : esL.g.safeCh (2 + Δcka) P = true
        · rw [hsafe]; exact hmem
        · rw [Bool.not_eq_true] at hsafe
          rw [hsafe]; exact List.mem_cons_of_mem _ hmem }

theorem leComp_transmitTail (j : ℕ) (k_fs : K) (P : Party) (m : M)
    (gL : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E)
    (gF : Ctx Γ T Sig (Option SS) (Option RS) M E)
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st)
    (hsends : P.sendsIn (esL.g.st P).tcur = true) :
    LeComp (StepRelFS fs Δcka qep mo j k_fs)
      (simulateQ lImpl (transmitTail Δcka (hooksLocalFixed cka prng fs mo j k_fs) P m gL esL))
      ((simulateQ (implFS fs) (transmitTail Δcka (hooksFS cka prng fs Δcka mo j) P m gF esF)).run st) := by
  have hsome := hs.hvS_some P hsends
  rcases hs.hvS P with ⟨hnone, _⟩ | ⟨ss, idx?, hvSL, hvSF, hne_j, hnot_sJ⟩ |
    ⟨hP_s, _, _, hsend_s, hsJ, hvSL, hvSF⟩
  · rw [hnone] at hsome; exact absurd hsome (by simp)
  · have hL_eq : simulateQ lImpl (transmitTail Δcka (hooksLocalFixed cka prng fs mo j k_fs) P m gL esL) =
        pure (some (((esL.g.st P).tcur, (esL.g.st P).curCkaMsg),
            (fs.send ss ((esL.g.st P).tcur, (esL.g.st P).curCkaMsg) m).2),
          { esL with
            g := esL.g.record (2 + Δcka) P
              { esL.g.st P with vS := some ((fs.send ss ((esL.g.st P).tcur, (esL.g.st P).curCkaMsg) m).1, idx?) }
              ⟨⟨P, esL.g.epoch P, esL.g.idx P + 1⟩, m,
                (((esL.g.st P).tcur, (esL.g.st P).curCkaMsg),
                  (fs.send ss ((esL.g.st P).tcur, (esL.g.st P).curCkaMsg) m).2)⟩ false }) := by
      dsimp only [transmitTail, vSendTail, hooksLocalFixed]
      simp only [run_liftH, hvSL, StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind,
        simulateQ_pure]
    have hF_eq : (simulateQ (implFS fs) (transmitTail Δcka (hooksFS cka prng fs Δcka mo j) P m gF esF)).run st =
        pure ((some (((esF.g.st P).tcur, (esF.g.st P).curCkaMsg),
            (fs.send ss ((esF.g.st P).tcur, (esF.g.st P).curCkaMsg) m).2),
          { esF with
            g := esF.g.record (2 + Δcka) P
              { esF.g.st P with vS := some (some (fs.send ss ((esF.g.st P).tcur, (esF.g.st P).curCkaMsg) m).1) }
              ⟨⟨P, esF.g.epoch P, esF.g.idx P + 1⟩, m,
                (((esF.g.st P).tcur, (esF.g.st P).curCkaMsg),
                  (fs.send ss ((esF.g.st P).tcur, (esF.g.st P).curCkaMsg) m).2)⟩ false }),
          st) := by
      dsimp only [transmitTail, vSendTail, hooksFS]
      simp only [run_liftH, hvSF, StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind,
        simulateQ_pure]
    rw [hL_eq, hF_eq]
    exact LeComp.pure (leComp_transmitTail_nonext_send fs Δcka qep mo j k_fs P m ss idx?
      hs hsends hvSL hvSF hne_j hnot_sJ)
  · obtain ⟨htcur_s, hlast⟩ := hsend_s hsends
    have hsafe_eq : esF.g.safeCh (2 + Δcka) P = esL.g.safeCh (2 + Δcka) P := by
      simp only [GameState.safeCh, hs.htL, hs.hepoch]
    have hL_eq : simulateQ lImpl (transmitTail Δcka (hooksLocalFixed cka prng fs mo j k_fs) P m gL esL) =
        pure (some (((esL.g.st P).tcur, (esL.g.st P).curCkaMsg),
            (fs.send st.senderState ((esL.g.st P).tcur, (esL.g.st P).curCkaMsg) m).2),
          { esL with
            g := esL.g.record (2 + Δcka) P
              { esL.g.st P with vS := some ((fs.send st.senderState ((esL.g.st P).tcur, (esL.g.st P).curCkaMsg) m).1, some j) }
              ⟨⟨P, esL.g.epoch P, esL.g.idx P + 1⟩, m,
                (((esL.g.st P).tcur, (esL.g.st P).curCkaMsg),
                  (fs.send st.senderState ((esL.g.st P).tcur, (esL.g.st P).curCkaMsg) m).2)⟩ false }) := by
      dsimp only [transmitTail, vSendTail, hooksLocalFixed]
      simp only [run_liftH, hvSL, StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind,
        simulateQ_pure]
    by_cases hcond : (!(esL.g.safeCh (2 + Δcka) P) && !esF.h.fsSCorr) = true
    · obtain ⟨hnsafe_b, hnscorr_b⟩ := Bool.and_eq_true_iff.mp hcond
      have hnsafe : esL.g.safeCh (2 + Δcka) P = false := by simpa using hnsafe_b
      have hF_eq : (simulateQ (implFS fs) (transmitTail Δcka (hooksFS cka prng fs Δcka mo j) P m gF esF)).run st =
          pure ((some (((esF.g.st P).tcur, (esF.g.st P).curCkaMsg),
              (fs.send st.senderState ((esF.g.st P).tcur, (esF.g.st P).curCkaMsg) m).2),
            { esF with
              g := esF.g.record (2 + Δcka) P
                { esF.g.st P with vS := some none }
                ⟨⟨P, esF.g.epoch P, esF.g.idx P + 1⟩, m,
                  (((esF.g.st P).tcur, (esF.g.st P).curCkaMsg),
                    (fs.send st.senderState ((esF.g.st P).tcur, (esF.g.st P).curCkaMsg) m).2)⟩ false,
              h := { esF.h with
                fsSCorr := true,
                fsCount := esF.h.fsCount + 1,
                fsTrans := (esF.h.fsCount + 1, ((esF.g.st P).tcur, (esF.g.st P).curCkaMsg),
                  (fs.send st.senderState ((esF.g.st P).tcur, (esF.g.st P).curCkaMsg) m).2) :: esF.h.fsTrans } }),
            { st with
              senderState := (fs.send st.senderState ((esF.g.st P).tcur, (esF.g.st P).curCkaMsg) m).1,
              senderCorruptedAt := some (st.senderCorruptedAt.getD st.lastSentIdx),
              lastSentIdx := st.lastSentIdx + 1,
              inTransit := ⟨st.lastSentIdx + 1, ((esF.g.st P).tcur, (esF.g.st P).curCkaMsg), m,
                (fs.send st.senderState ((esF.g.st P).tcur, (esF.g.st P).curCkaMsg) m).2⟩ :: st.inTransit }) := by
        dsimp only [transmitTail, vSendTail, hooksFS]
        simp only [run_liftH, hvSF, StateT.run_bind, StateT.run_get, StateT.run_pure,
          StateT.run_modify, hs.hextF, hsafe_eq, hcond, ↓reduceIte, pure_bind,
          bind_assoc, simulateQ_bind, simulateQ_pure, simulateQ_implFS_corruptSenderQuery,
          simulateQ_implFS_transmitQuery, FSAEAD.corruptSender, FSAEAD.transmit, hs.hendedFS,
          Bool.false_eq_true, Bool.not_true]
      rw [hL_eq, hF_eq]
      have hs' := syncLFS_fsSend_corrupt fs Δcka qep mo j k_fs P hs hsends htcur_s hsJ hlast hnsafe
      exact LeComp.pure (leComp_transmitTail_ext_send fs Δcka qep mo j k_fs P m
        hs' hsends hP_s htcur_s hsJ hvSL hvSF hlast (fun _ => rfl))
    · rw [Bool.not_eq_true] at hcond
      have hcorr_if_nsafe : esL.g.safeCh (2 + Δcka) P = false → st.senderCorruptedAt.isSome = true := by
        intro hnsafe
        have hscorr : esF.h.fsSCorr = true := by
          cases hsc : esF.h.fsSCorr
          · rw [hnsafe, hsc] at hcond; exact absurd hcond (by decide)
          · rfl
        rwa [← hs.hfsSCorr]
      have hF_eq : (simulateQ (implFS fs) (transmitTail Δcka (hooksFS cka prng fs Δcka mo j) P m gF esF)).run st =
          pure ((some (((esF.g.st P).tcur, (esF.g.st P).curCkaMsg),
              (fs.send st.senderState ((esF.g.st P).tcur, (esF.g.st P).curCkaMsg) m).2),
            { esF with
              g := esF.g.record (2 + Δcka) P
                { esF.g.st P with vS := some none }
                ⟨⟨P, esF.g.epoch P, esF.g.idx P + 1⟩, m,
                  (((esF.g.st P).tcur, (esF.g.st P).curCkaMsg),
                    (fs.send st.senderState ((esF.g.st P).tcur, (esF.g.st P).curCkaMsg) m).2)⟩ false,
              h := { esF.h with
                fsCount := esF.h.fsCount + 1,
                fsTrans := (esF.h.fsCount + 1, ((esF.g.st P).tcur, (esF.g.st P).curCkaMsg),
                  (fs.send st.senderState ((esF.g.st P).tcur, (esF.g.st P).curCkaMsg) m).2) :: esF.h.fsTrans } }),
            { st with
              senderState := (fs.send st.senderState ((esF.g.st P).tcur, (esF.g.st P).curCkaMsg) m).1,
              lastSentIdx := st.lastSentIdx + 1,
              inTransit := ⟨st.lastSentIdx + 1, ((esF.g.st P).tcur, (esF.g.st P).curCkaMsg), m,
                (fs.send st.senderState ((esF.g.st P).tcur, (esF.g.st P).curCkaMsg) m).2⟩ :: st.inTransit }) := by
        dsimp only [transmitTail, vSendTail, hooksFS]
        simp only [run_liftH, hvSF, StateT.run_bind, StateT.run_get, StateT.run_pure,
          StateT.run_modify, hs.hextF, hsafe_eq, hcond, Bool.false_eq_true, Bool.not_true,
          ↓reduceIte, pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure,
          simulateQ_implFS_transmitQuery, FSAEAD.transmit, hs.hendedFS]
      rw [hL_eq, hF_eq]
      exact LeComp.pure (leComp_transmitTail_ext_send fs Δcka qep mo j k_fs P m
        hs hsends hP_s htcur_s hsJ hvSL hvSF hlast hcorr_if_nsafe)

theorem not_senderIsJ_of_lt (j : ℕ) (k_fs : K)
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st)
    (hlt : (esL.g.st (Party.senderOf mo.tStar)).tcur < mo.tStar) :
    ¬ SenderIsJ mo j esL := by
  rintro (⟨h0, _⟩ | ⟨Tc, σc, k, hc⟩)
  · omega
  · rw [hs.hcache_gt mo.tStar hlt] at hc
    cases hc

theorem syncLFS_after_startSend (j : ℕ) (k_fs : K) (P : Party)
    (coins : CCoins) (σ' : Sig) (kL kF : K) (idx? : Option ℕ) (ext : Bool)
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st)
    (s₁L : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E)
    (s₁F : Ctx Γ T Sig (Option SS) (Option RS) M E)
    (hs₁_stL : s₁L.st = esL.g.st)
    (hs₁_stF : s₁F.st = esF.g.st)
    (hs₁_epL : s₁L.epoch = Function.update esL.g.epoch P (esL.g.epoch P + 1))
    (hs₁_epF : s₁F.epoch = Function.update esF.g.epoch P (esF.g.epoch P + 1))
    (hs₁_idxL : s₁L.idx = Function.update esL.g.idx P 0)
    (hs₁_idxF : s₁F.idx = Function.update esF.g.idx P 0)
    (hs₁_tL : s₁L.tL = s₁F.tL)
    (hs₁_heal : ∀ t, healedBy esL.g.tL (2 + Δcka) t = false → healedBy s₁L.tL (2 + Δcka) t = false)
    (hs₁_leaks : s₁L.leaks = s₁F.leaks)
    (hs₁_restL : s₁L.trans = esL.g.trans ∧ s₁L.chall = esL.g.chall ∧ s₁L.comp = esL.g.comp ∧
      s₁L.maxAcc = esL.g.maxAcc ∧ s₁L.b = esL.g.b ∧ s₁L.win = esL.g.win ∧ s₁L.corrs = esL.g.corrs)
    (hs₁_restF : s₁F.trans = esF.g.trans ∧ s₁F.chall = esF.g.chall ∧ s₁F.comp = esF.g.comp ∧
      s₁F.maxAcc = esF.g.maxAcc ∧ s₁F.b = esF.g.b ∧ s₁F.win = esF.g.win ∧ s₁F.corrs = esF.g.corrs)
    (hsends_next : P.sendsIn ((esL.g.st P).tcur + 1) = true)
    (hqep_next : (esL.g.st P).tcur + 1 ≤ qep)
    (hL' : LState T Sig K I) (hF' : FSState T Sig K I SS RS E)
    (hr_tstar : (esL.g.st P).tcur + 1 = mo.tStar →
      ∃ idx,
        idx? = some idx ∧
        ext = (idx == j) ∧
        (idx = j → kL = k_fs) ∧
        (idx ≠ j → kL = kF) ∧
        (esL.h.sessions = [] → idx = 0))
    (hr_ne : (esL.g.st P).tcur + 1 ≠ mo.tStar →
      idx? = none ∧
      ext = false ∧
      kL = kF ∧
      hL'.sessions = esL.h.sessions)
    (hr_cL : hL'.cache = Function.update esL.h.cache ((esL.g.st P).tcur + 1)
      (some ((cka.send (esL.g.st P).γ coins).2.1, σ', kL, idx?)))
    (hr_tr : hF'.fsTrans = esF.h.fsTrans)
    (hr_cnt : hF'.fsCount = esF.h.fsCount)
    (hr_sc : hF'.fsSCorr = esF.h.fsSCorr)
    (hr_ex : hF'.ext = esF.h.ext)
    (hr_bs : BookSync mo j k_fs hL' hF') :
    let c := cka.send (esL.g.st P).γ coins
    let t := (esL.g.st P).tcur + 1
    let vp₁L : VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ) :=
      { esL.g.st P with
        γ := c.1, curCkaMsg := some c.2.1, root := σ',
        vS := some (fs.initSender kL, idx?), tcur := t }
    let vp₁F : VP Γ T Sig (Option SS) (Option RS) :=
      { esF.g.st P with
        γ := c.1, curCkaMsg := some c.2.1, root := σ',
        vS := some (if ext then none else some (fs.initSender kF)),
        tcur := (esF.g.st P).tcur + 1 }
    SyncLFS fs Δcka qep mo j k_fs
      { esL with g := { s₁L with st := Function.update s₁L.st P vp₁L }, h := hL' }
      { esF with g := { s₁F with st := Function.update s₁F.st P vp₁F }, h := hF' }
      st := by
  intro c t vp₁L vp₁F
  have hsender_t : Party.senderOf t = P := senderOf_eq_of_sendsIn hsends_next
  have ht_pos : 0 < t := Nat.succ_pos _
  have hsJ_iff_of_ne : ∀ (g' : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E),
      t ≠ mo.tStar →
      (SenderIsJ mo j { esL with g := g', h := hL' } ↔ SenderIsJ mo j esL) := by
    intro g' ht_ne
    have hne' : mo.tStar ≠ (esL.g.st P).tcur + 1 := Ne.symm ht_ne
    simp only [SenderIsJ, hr_cL, Function.update_of_ne hne']
  refine {
    habortL := hs.habortL
    habortF := hs.habortF
    hwinL := by dsimp only; rw [hs₁_restL.2.2.2.2.2.1, hs.hwinL]
    hwinF := by dsimp only; rw [hs₁_restF.2.2.2.2.2.1, hs.hwinF]
    hwinFS := hs.hwinFS
    hendedFS := hs.hendedFS
    hchallFS := hs.hchallFS
    hextF := by dsimp only; rw [hr_ex, hs.hextF]
    hepoch := by dsimp only; rw [hs₁_epL, hs₁_epF, hs.hepoch]
    hidx := by dsimp only; rw [hs₁_idxL, hs₁_idxF, hs.hidx]
    htL := hs₁_tL
    htrans := by dsimp only; rw [hs₁_restL.1, hs₁_restF.1, hs.htrans]
    hchall := by dsimp only; rw [hs₁_restL.2.1, hs.hchall]
    hchallF := by dsimp only; rw [hs₁_restF.2.1, hs.hchallF]
    hcomp := by dsimp only; rw [hs₁_restL.2.2.1, hs₁_restF.2.2.1, hs.hcomp]
    hcomp_inv := fun pos hpos => by
      dsimp only at hpos ⊢
      rw [hs₁_restL.2.2.1] at hpos
      exact hs₁_heal pos.epoch (hs.hcomp_inv pos hpos)
    hmaxAcc := by dsimp only; rw [hs₁_restL.2.2.2.1, hs₁_restF.2.2.2.1, hs.hmaxAcc]
    hb := by dsimp only; rw [hs₁_restL.2.2.2.2.1, hs₁_restF.2.2.2.2.1, hs.hb]
    hleaks := hs₁_leaks
    hcorrs := by dsimp only; rw [hs₁_restL.2.2.2.2.2.2, hs₁_restF.2.2.2.2.2.2, hs.hcorrs]
    hbs := hr_bs
    hcache_zero := by
      dsimp only
      rw [hr_cL, Function.update_of_ne (by omega : 0 ≠ (esL.g.st P).tcur + 1)]
      exact hs.hcache_zero
    hcache_gt := fun t' ht' => by
      dsimp only at ht' ⊢
      rw [hs₁_stL] at ht'
      by_cases heq : t' = (esL.g.st P).tcur + 1
      · subst heq
        rw [hsender_t, Function.update_self] at ht'
        dsimp only [vp₁L] at ht'
        omega
      · rw [hr_cL, Function.update_of_ne heq]
        apply hs.hcache_gt t'
        by_cases hQ : Party.senderOf t' = P
        · rw [hQ, Function.update_self] at ht'
          dsimp only [vp₁L, t] at ht'
          rw [hQ]; omega
        · rwa [Function.update_of_ne hQ] at ht'
    hsess_before := fun hlt hsome hstar => by
      dsimp only at hlt ⊢
      rw [hs₁_stL] at hlt
      have ht_ne : t ≠ mo.tStar := by
        intro heq
        have hP_s : Party.senderOf mo.tStar = P := by rw [← heq, hsender_t]
        rw [hP_s, Function.update_self] at hlt
        dsimp only [vp₁L] at hlt
        omega
      rw [(hr_ne ht_ne).2.2.2]
      apply hs.hsess_before _ hsome hstar
      by_cases hQ : Party.senderOf mo.tStar = P
      · rw [hQ, Function.update_self] at hlt
        dsimp only [vp₁L, t] at hlt
        rw [hQ]; omega
      · rwa [Function.update_of_ne hQ] at hlt
    hidL := fun Q => by
      dsimp only; rw [hs₁_stL]
      by_cases hQ : Q = P <;> simp [hQ, vp₁L, hs.hidL]
    hidF := fun Q => by
      dsimp only; rw [hs₁_stF]
      by_cases hQ : Q = P <;> simp [hQ, vp₁F, hs.hidF]
    hroot := fun Q => by
      dsimp only; rw [hs₁_stL, hs₁_stF]
      by_cases hQ : Q = P <;> simp [hQ, vp₁L, vp₁F, hs.hroot]
    hγ := fun Q => by
      dsimp only; rw [hs₁_stL, hs₁_stF]
      by_cases hQ : Q = P <;> simp [hQ, vp₁L, vp₁F, hs.hγ]
    hTcur := fun Q => by
      dsimp only; rw [hs₁_stL, hs₁_stF]
      by_cases hQ : Q = P <;> simp [hQ, vp₁L, vp₁F, hs.hTcur]
    htcur := fun Q => by
      dsimp only; rw [hs₁_stL, hs₁_stF]
      by_cases hQ : Q = P <;> simp [hQ, vp₁L, vp₁F, t, hs.htcur]
    htcur_epoch := fun Q => by
      dsimp only; rw [hs₁_stL, hs₁_epL]
      by_cases hQ : Q = P <;> simp [hQ, vp₁L, t, hs.htcur_epoch]
    htcur_le_qep := fun Q hQ_s => by
      dsimp only at hQ_s ⊢; rw [hs₁_stL] at hQ_s ⊢
      by_cases hQ : Q = P
      · subst hQ; simp only [Function.update_self, vp₁L, t]; exact hqep_next
      · simp only [Function.update_of_ne hQ] at hQ_s ⊢; exact hs.htcur_le_qep Q hQ_s
    hTcur_sender := fun Q hQ_s hpos => by
      dsimp only at hQ_s hpos ⊢; rw [hs₁_stL] at hQ_s hpos ⊢
      by_cases hQ : Q = P
      · subst hQ
        simp only [Function.update_self, vp₁L]
        exact ⟨c.2.1, σ', kL, idx?, by rw [hr_cL, Function.update_self], rfl⟩
      · simp only [Function.update_of_ne hQ] at hQ_s hpos ⊢
        have hne_t : (esL.g.st Q).tcur ≠ (esL.g.st P).tcur + 1 := by
          intro heq
          have hsender_Q := senderOf_eq_of_sendsIn hQ_s
          rw [heq, hsender_t] at hsender_Q
          exact hQ hsender_Q.symm
        rw [hr_cL, Function.update_of_ne hne_t]
        exact hs.hTcur_sender Q hQ_s hpos
    hvS_some := fun Q hQ_s => by
      dsimp only at hQ_s ⊢; rw [hs₁_stL] at hQ_s ⊢
      by_cases hQ : Q = P
      · subst hQ; simp [vp₁L]
      · simp only [Function.update_of_ne hQ] at hQ_s ⊢; exact hs.hvS_some Q hQ_s
    hvS := fun Q => by
      dsimp only; rw [hs₁_stL, hs₁_stF, hs₁_idxL]
      by_cases hQ : Q = P
      · subst hQ
        simp only [Function.update_self]
        by_cases ht_star : t = mo.tStar
        · obtain ⟨idx, hidx?, hext, h_eq_j, h_ne_j, _⟩ := hr_tstar ht_star
          have hP_s : Q = Party.senderOf mo.tStar := by rw [← ht_star, hsender_t]
          have hlt_before : (esL.g.st (Party.senderOf mo.tStar)).tcur < mo.tStar := by
            rw [← hP_s]; dsimp only [t] at ht_star; omega
          have hnot_before : ¬ SenderIsJ mo j esL := not_senderIsJ_of_lt fs Δcka qep mo j k_fs hs hlt_before
          by_cases hidx_j : idx = j
          · subst hidx_j
            have hkL_eq : kL = k_fs := h_eq_j rfl
            have hext_true : ext = true := by simp [hext]
            obtain ⟨hst_ss, hst_last, _, _⟩ := hs.hnot_senderJ hnot_before
            have hqep_s : mo.tStar ≤ qep := by rw [← ht_star]; exact hqep_next
            refine Or.inr (Or.inr ⟨hP_s, by simp [vp₁L, ht_star], hqep_s,
              fun _ => ⟨ht_star, hst_last⟩, ?_, ?_, ?_⟩)
            · refine Or.inr ⟨c.2.1, σ', kL, ?_⟩
              dsimp only
              have ht_star' : (esL.g.st Q).tcur + 1 = mo.tStar := ht_star
              rw [hr_cL, ← ht_star', Function.update_self, hidx?]
            · simp [vp₁L, hidx?, hkL_eq, hst_ss]
            · simp [vp₁F, hext_true]
          · have hkL_eq : kL = kF := h_ne_j hidx_j
            have hext_false : ext = false := by simp [hext, hidx_j]
            have hne_some : idx? ≠ some j := by rw [hidx?]; simpa using hidx_j
            refine Or.inr (Or.inl ⟨fs.initSender kL, idx?, rfl, by simp [vp₁F, hext_false, hkL_eq],
              hne_some, ?_⟩)
            intro _ _
            rintro (⟨h0, _⟩ | ⟨Tc, σc, k, hc⟩)
            · omega
            · dsimp only at hc
              have ht_star' : (esL.g.st Q).tcur + 1 = mo.tStar := ht_star
              rw [hr_cL, ← ht_star', Function.update_self] at hc
              simp only [Option.some.injEq, Prod.mk.injEq] at hc
              exact hne_some hc.2.2.2
        · obtain ⟨hidx?, hext, hkL_eq, _⟩ := hr_ne ht_star
          refine Or.inr (Or.inl ⟨fs.initSender kL, idx?, rfl, by simp [vp₁F, hext, hkL_eq],
            by simp [hidx?], ?_⟩)
          intro _ htcur_eq
          dsimp only [vp₁L] at htcur_eq
          exact False.elim (ht_star htcur_eq)
      · simp only [Function.update_of_ne hQ]
        rcases hs.hvS Q with ⟨h1, h2⟩ | ⟨ss', idx'?, h1, h2, h3, h4⟩ |
          ⟨hQ_s, h1, h2, h3, h4, h5, h6⟩
        · exact Or.inl ⟨h1, h2⟩
        · refine Or.inr (Or.inl ⟨ss', idx'?, h1, h2, h3, ?_⟩)
          intro hQ_s htcur_Q
          have ht_ne : t ≠ mo.tStar := by
            intro heq
            apply hQ
            rw [hQ_s, ← heq, hsender_t]
          rw [hsJ_iff_of_ne _ ht_ne]
          exact h4 hQ_s htcur_Q
        · refine Or.inr (Or.inr ⟨hQ_s, h1, h2, fun hQ_send => by simp [hQ, h3 hQ_send], ?_, h5, h6⟩)
          have ht_ne : t ≠ mo.tStar := by
            intro heq
            apply hQ
            rw [hQ_s, ← heq, hsender_t]
          exact (hsJ_iff_of_ne _ ht_ne).mpr h4
    hvR_other := fun Q t' hne => by
      dsimp only; rw [hs₁_stL, hs₁_stF]
      by_cases hQ : Q = P
      · subst hQ; simp only [Function.update_self, vp₁L, vp₁F]; exact hs.hvR_other Q t' hne
      · simp only [Function.update_of_ne hQ]; exact hs.hvR_other Q t' hne
    hvR_target_lt := fun hlt => by
      dsimp only at hlt ⊢; rw [hs₁_stL] at hlt ⊢; rw [hs₁_stF]
      by_cases hQ : Party.receiverOf mo.tStar = P
      · rw [hQ, Function.update_self] at hlt ⊢
        rw [Function.update_self]
        dsimp only [vp₁L, vp₁F, t] at hlt ⊢
        have hlt' : (esL.g.st (Party.receiverOf mo.tStar)).tcur < mo.tStar := by rw [hQ]; omega
        simpa only [hQ] using hs.hvR_target_lt hlt'
      · rw [Function.update_of_ne hQ] at hlt ⊢
        rw [Function.update_of_ne hQ]
        exact hs.hvR_target_lt hlt
    hvR_target_ge := fun hge => by
      dsimp only at hge ⊢; rw [hs₁_stL] at hge ⊢; rw [hs₁_stF]
      have ht_ne_if_PR : Party.receiverOf mo.tStar = P → t ≠ mo.tStar := by
        intro hPR heq
        have hPS : Party.senderOf mo.tStar = P := by rw [← heq, hsender_t]
        have hne : Party.receiverOf mo.tStar ≠ Party.senderOf mo.tStar := by
          dsimp only [Party.receiverOf]
          cases Party.senderOf mo.tStar <;> decide
        exact hne (hPR.trans hPS.symm)
      have hge' : mo.tStar ≤ (esL.g.st (Party.receiverOf mo.tStar)).tcur := by
        by_cases hQ : Party.receiverOf mo.tStar = P
        · have ht_ne := ht_ne_if_PR hQ
          rw [hQ, Function.update_self] at hge
          dsimp only [vp₁L, t] at hge
          rw [hQ]; omega
        · rwa [Function.update_of_ne hQ] at hge
      obtain ⟨hsJ_before, hvRL, hvRF⟩ := hs.hvR_target_ge hge'
      have ht_ne : t ≠ mo.tStar := by
        intro heq
        have hlt_s : (esL.g.st (Party.senderOf mo.tStar)).tcur < mo.tStar := by
          have hPS : Party.senderOf mo.tStar = P := by rw [← heq, hsender_t]
          rw [hPS]; dsimp only [t] at heq; omega
        exact not_senderIsJ_of_lt fs Δcka qep mo j k_fs hs hlt_s hsJ_before
      refine ⟨(hsJ_iff_of_ne _ ht_ne).mpr hsJ_before, ?_, ?_⟩
      · by_cases hQ : Party.receiverOf mo.tStar = P
        · rw [hQ, Function.update_self]; dsimp only [vp₁L]; rwa [← hQ]
        · rw [Function.update_of_ne hQ]; exact hvRL
      · by_cases hQ : Party.receiverOf mo.tStar = P
        · rw [hQ, Function.update_self]; dsimp only [vp₁F]; rwa [← hQ]
        · rw [Function.update_of_ne hQ]; exact hvRF
    hfsCount := by dsimp only; rw [hr_cnt, hs.hfsCount]
    hfsTrans := by dsimp only; rw [hr_tr, hs.hfsTrans]
    hfsSCorr := by dsimp only; rw [hr_sc, hs.hfsSCorr]
    htrans_wf := fun r hr => by
      dsimp only at hr ⊢
      rw [hs₁_restL.1] at hr
      rw [hs₁_stL]
      obtain ⟨h1, h2, h3, h4, h5⟩ := hs.htrans_wf r hr
      have hr_ne_t : r.pos.epoch ≠ (esL.g.st P).tcur + 1 := by
        intro heq
        have hsender_r : r.pos.sender = P := by rw [h2, heq, hsender_t]
        rw [hsender_r] at h3
        omega
      refine ⟨h1, h2, ?_, ?_, ?_⟩
      · by_cases hQ : r.pos.sender = P
        · rw [hQ, Function.update_self]; dsimp only [vp₁L, t]; rw [hQ] at h3; omega
        · rw [Function.update_of_ne hQ]; exact h3
      · intro hpos
        rw [hr_cL, Function.update_of_ne hr_ne_t]
        exact h4 hpos
      · intro he hsJ'
        have ht_ne : t ≠ mo.tStar := he ▸ hr_ne_t.symm
        exact h5 he ((hsJ_iff_of_ne _ ht_ne).mp hsJ')
    hnot_senderJ := fun hnot => by
      apply hs.hnot_senderJ
      intro hsJ_before
      apply hnot
      have ht_ne : t ≠ mo.tStar := by
        intro heq
        have hlt_s : (esL.g.st (Party.senderOf mo.tStar)).tcur < mo.tStar := by
          have hPS : Party.senderOf mo.tStar = P := by rw [← heq, hsender_t]
          rw [hPS]; dsimp only [t] at heq; omega
        exact not_senderIsJ_of_lt fs Δcka qep mo j k_fs hs hlt_s hsJ_before
      exact (hsJ_iff_of_ne _ ht_ne).mpr hsJ_before
    hsenderJ_trans := fun hsJ_after => by
      dsimp only
      rw [hs₁_restL.1]
      by_cases ht_star : t = mo.tStar
      · have hlt_s : (esL.g.st (Party.senderOf mo.tStar)).tcur < mo.tStar := by
          have hPS : Party.senderOf mo.tStar = P := by rw [← ht_star, hsender_t]
          rw [hPS]; dsimp only [t] at ht_star; omega
        have hnot_before := not_senderIsJ_of_lt fs Δcka qep mo j k_fs hs hlt_s
        obtain ⟨_, _, _, hinT⟩ := hs.hnot_senderJ hnot_before
        rw [hinT]
        have hfilter : esL.g.trans.filter (fun r => r.pos.epoch == mo.tStar) = [] := by
          rw [List.filter_eq_nil_iff]
          intro r hr
          obtain ⟨_, h2, h3, _, _⟩ := hs.htrans_wf r hr
          simp only [beq_iff_eq]
          intro heq
          rw [heq] at h2 h3
          rw [h2] at h3
          omega
        rw [hfilter, List.map_nil]
      · exact hs.hsenderJ_trans ((hsJ_iff_of_ne _ ht_star).mp hsJ_after)
    hcorr_sync := fun corrAt hcorr => by
      obtain ⟨hsJ_before, hqep_s, hheal_s, hcomp_mem⟩ := hs.hcorr_sync corrAt hcorr
      have ht_ne : t ≠ mo.tStar := by
        intro heq
        have hlt_s : (esL.g.st (Party.senderOf mo.tStar)).tcur < mo.tStar := by
          have hPS : Party.senderOf mo.tStar = P := by rw [← heq, hsender_t]
          rw [hPS]; dsimp only [t] at heq; omega
        exact not_senderIsJ_of_lt fs Δcka qep mo j k_fs hs hlt_s hsJ_before
      refine ⟨(hsJ_iff_of_ne _ ht_ne).mpr hsJ_before, hqep_s, hs₁_heal mo.tStar hheal_s, ?_⟩
      intro r hr hepoch_r hlt_r
      dsimp only at hr ⊢
      rw [hs₁_restL.1] at hr
      rw [hs₁_restL.2.2.1]
      exact hcomp_mem r hr hepoch_r hlt_r }

theorem vSend_eq_vSendTail_of_false {tspec : OracleSpec.{0, 0} ι} {Γv Sv SSv RSv HS : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (ctx : Ctx Γv T Sv SSv RSv M E) (P : Party) (vp : VP Γv T Sv SSv RSv) (m : M)
    (r : Option CCoins)
    (h : vp.id.sendsIn (vp.tcur + 1) = false) :
    vSend hk ctx P vp m none r = vSendTail hk ctx P vp m := by
  dsimp only [vSend, vSendTail]
  simp only [h, Bool.false_eq_true, ↓reduceIte, pure_bind]
  rfl

theorem vSend_eq_bind_vSendTail_of_true {tspec : OracleSpec.{0, 0} ι} {Γv Sv SSv RSv HS : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (ctx : Ctx Γv T Sv SSv RSv M E) (P : Party) (vp : VP Γv T Sv SSv RSv) (m : M)
    (r : Option CCoins)
    (h : vp.id.sendsIn (vp.tcur + 1) = true) :
    vSend hk ctx P vp m none r =
      (do
        match ← hk.startSend ctx P (vp.tcur + 1) vp.γ vp.root r with
        | none => return none
        | some (γ', T', σ', ss) =>
          vSendTail hk ctx P
            { vp with tcur := vp.tcur + 1, γ := γ', curCkaMsg := some T', root := σ', vS := some ss } m) := by
  dsimp only [vSend, vSendTail]
  simp only [h, ↓reduceIte, bind_assoc, pure_bind]
  rfl

theorem vSendTail_update_eq {tspec : OracleSpec.{0, 0} ι} {Γv Sv SSv RSv HS : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (P : Party) (m : M)
    (s₁ : Ctx Γv T Sv SSv RSv M E) (vp₁ : VP Γv T Sv SSv RSv)
    (hfs : ∀ v h,
      hk.fsSend { s₁ with st := Function.update s₁.st P vp₁ } P vp₁.tcur v h m none =
      hk.fsSend s₁ P vp₁.tcur v h m none) :
    vSendTail hk { s₁ with st := Function.update s₁.st P vp₁ } P vp₁ m =
    vSendTail hk s₁ P vp₁ m := by
  dsimp only [vSendTail]
  cases vp₁.vS with
  | none => rfl
  | some v => dsimp only; rw [hfs]

theorem leComp_transmitE (j : ℕ) (k_fs : K)
    (q : Party × M × Option CCoins)
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st) :
    LeComp (StepRelFS fs Δcka qep mo j k_fs)
      (simulateQ lImpl
        ((transmitE (hooksLocalFixed cka prng fs mo j k_fs) (2 + Δcka) qep mo.policy q).run esL))
      ((simulateQ (implFS fs)
        ((transmitE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.policy q).run esF)).run st) := by
  rcases q with ⟨P, m, r⟩
  unfold transmitE
  simp only [StateT.run_bind, StateT.run_get, pure_bind,
    hs.habortL, hs.habortF, hs.hwinL, hs.hwinF, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  have hsends_next_eq : P.sendsIn (esF.g.epoch P + 1) = P.sendsIn (esL.g.epoch P + 1) := by
    rw [hs.hepoch]
  by_cases hsends_next : P.sendsIn (esL.g.epoch P + 1) = true
  · by_cases hgt : qep < esL.g.epoch P + 1
    · have hgtF : qep < esF.g.epoch P + 1 := by rwa [← hs.hepoch]
      simp only [GameState.epMgmt, hsends_next_eq, hsends_next, hgt, hgtF, ↓reduceIte,
        StateT.run_pure, simulateQ_pure]
      exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
    · have hgtF : ¬ (qep < esF.g.epoch P + 1) := by rwa [← hs.hepoch]
      have hqep : esL.g.epoch P + 1 ≤ qep := Nat.le_of_not_lt hgt
      have hqep_tcur : (esL.g.st P).tcur + 1 ≤ qep := by rw [hs.htcur_epoch P]; exact hqep
      have hsends_next_tcur : P.sendsIn ((esL.g.st P).tcur + 1) = true := by
        rw [hs.htcur_epoch P]; exact hsends_next
      have hsends_next_tcurF : P.sendsIn ((esF.g.st P).tcur + 1) = true := by
        rw [← hs.htcur P]; exact hsends_next_tcur
      have hsafe_eq : esF.g.safeCh (2 + Δcka) P = esL.g.safeCh (2 + Δcka) P := by
        simp only [GameState.safeCh, hs.htL, hs.hepoch]
      let cond := r.isSome && !(esL.g.safeCh (2 + Δcka) P)
      let s₀L := if cond then esL.g.leak (esL.g.epoch P + 1) else esL.g
      let s₀F := if cond then esF.g.leak (esF.g.epoch P + 1) else esF.g
      let s₁L : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E :=
        { s₀L with
          epoch := Function.update s₀L.epoch P (s₀L.epoch P + 1),
          idx := Function.update s₀L.idx P 0 }
      let s₁F : Ctx Γ T Sig (Option SS) (Option RS) M E :=
        { s₀F with
          epoch := Function.update s₀F.epoch P (s₀F.epoch P + 1),
          idx := Function.update s₀F.idx P 0 }
      have hepL : esL.g.epMgmt (2 + Δcka) qep P r.isSome = some s₁L := by
        simp only [GameState.epMgmt, hsends_next, hgt, ↓reduceIte]
        rfl
      have hepF : esF.g.epMgmt (2 + Δcka) qep P r.isSome = some s₁F := by
        simp only [GameState.epMgmt, hsends_next_eq, hsends_next, hgtF, hsafe_eq, ↓reduceIte]
        rfl
      rw [hepL, hepF]
      dsimp only
      have hs₁_stL : s₁L.st = esL.g.st := by dsimp only [s₁L, s₀L]; split <;> rfl
      have hs₁_stF : s₁F.st = esF.g.st := by dsimp only [s₁F, s₀F]; split <;> rfl
      have hs₁_epL : s₁L.epoch = Function.update esL.g.epoch P (esL.g.epoch P + 1) := by
        dsimp only [s₁L, s₀L]; split <;> rfl
      have hs₁_epF : s₁F.epoch = Function.update esF.g.epoch P (esF.g.epoch P + 1) := by
        dsimp only [s₁F, s₀F]; split <;> rfl
      have hs₁_idxL : s₁L.idx = Function.update esL.g.idx P 0 := by
        dsimp only [s₁L, s₀L]; split <;> rfl
      have hs₁_idxF : s₁F.idx = Function.update esF.g.idx P 0 := by
        dsimp only [s₁F, s₀F]; split <;> rfl
      have hs₁_tL : s₁L.tL = s₁F.tL := by
        dsimp only [s₁L, s₁F, s₀L, s₀F]
        split <;> simp [GameState.leak, hs.htL, hs.hepoch]
      have hs₁_heal : ∀ t, healedBy esL.g.tL (2 + Δcka) t = false →
          healedBy s₁L.tL (2 + Δcka) t = false := by
        intro t h
        dsimp only [s₁L, s₀L]
        split
        · exact healedBy_leak_false_of_false h
        · exact h
      have hs₁_leaks : s₁L.leaks = s₁F.leaks := by
        dsimp only [s₁L, s₁F, s₀L, s₀F]
        split <;> simp [GameState.leak, hs.hleaks, hs.htL, hs.hepoch]
      have hs₁_restL : s₁L.trans = esL.g.trans ∧ s₁L.chall = esL.g.chall ∧ s₁L.comp = esL.g.comp ∧
          s₁L.maxAcc = esL.g.maxAcc ∧ s₁L.b = esL.g.b ∧ s₁L.win = esL.g.win ∧ s₁L.corrs = esL.g.corrs := by
        dsimp only [s₁L, s₀L]; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have hs₁_restF : s₁F.trans = esF.g.trans ∧ s₁F.chall = esF.g.chall ∧ s₁F.comp = esF.g.comp ∧
          s₁F.maxAcc = esF.g.maxAcc ∧ s₁F.b = esF.g.b ∧ s₁F.win = esF.g.win ∧ s₁F.corrs = esF.g.corrs := by
        dsimp only [s₁F, s₀F]; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have hdoom_eq : mo.policy.leakDoom esF.g s₁F = mo.policy.leakDoom esL.g s₁L := by
        simp only [Policy.leakDoom, ← hs.hepoch, ← hs.htL, ← hs₁_leaks]
      rw [hdoom_eq]
      by_cases hdoom : mo.policy.leakDoom esL.g s₁L = true
      · simp only [hdoom, ↓reduceIte, abortE, StateT.run_modify, pure_bind,
          StateT.run_pure, simulateQ_pure]
        exact LeComp.pure (Or.inl (lhsDead_of_abort Δcka mo j esL))
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte]
        have hsess_empty :
            (esL.g.st P).tcur + 1 = mo.tStar → mo.tL.isSome = true →
            (esL.g.st P).tcur + 1 = mo.tH → esL.h.sessions = [] := by
          intro ht_star hsome hth
          have hPS : Party.senderOf mo.tStar = P := by
            rw [← ht_star, senderOf_eq_of_sendsIn hsends_next_tcur]
          apply hs.hsess_before _ hsome (ht_star.symm.trans hth)
          rw [hPS]; omega
        have hstart := leComp_startSend cka prng fs Δcka mo j k_fs s₁L s₁F P
          ((esL.g.st P).tcur + 1) (esL.g.st P).γ (esL.g.st P).root r hs.hbs hsess_empty st
        have hstart_eq :
            ((hooksFS cka prng fs Δcka mo j).startSend s₁F P ((esF.g.st P).tcur + 1)
              (esF.g.st P).γ (esF.g.st P).root r) =
            ((hooksFS cka prng fs Δcka mo j).startSend s₁F P ((esL.g.st P).tcur + 1)
              (esL.g.st P).γ (esL.g.st P).root r) := by
          rw [hs.htcur P, hs.hγ P, hs.hroot P]
        have hvSendL := vSend_eq_bind_vSendTail_of_true (hooksLocalFixed cka prng fs mo j k_fs)
          s₁L P (esL.g.st P) m r (by rw [hs.hidL P]; exact hsends_next_tcur)
        have hvSendF := vSend_eq_bind_vSendTail_of_true (hooksFS cka prng fs Δcka mo j)
          s₁F P (esF.g.st P) m r (by rw [hs.hidF P]; exact hsends_next_tcurF)
        simp only [hs₁_stL, hs₁_stF, hvSendL, hvSendF,
          run_liftH, StateT.run_bind, bind_assoc, simulateQ_bind, hstart_eq]
        refine LeComp.bind hstart fun rL rF hrel => ?_
        rcases hrel with ⟨coins, σ', kL, kF, idx?, ext, hrL1, hrF1, hr_st,
          hr_tstar, hr_ne, hr_cL, hr_cF, hr_tr, hr_cnt, hr_sc, hr_ex, hr_bs⟩
        subst hr_st
        rw [hrL1, hrF1]
        dsimp only
        let c := cka.send (esL.g.st P).γ coins
        let t := (esL.g.st P).tcur + 1
        let vp₁L : VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ) :=
          { esL.g.st P with
            γ := c.1, curCkaMsg := some c.2.1, root := σ',
            vS := some (fs.initSender kL, idx?), tcur := t }
        let vp₁F : VP Γ T Sig (Option SS) (Option RS) :=
          { esF.g.st P with
            γ := c.1, curCkaMsg := some c.2.1, root := σ',
            vS := some (if ext then none else some (fs.initSender kF)),
            tcur := (esF.g.st P).tcur + 1 }
        let es₁L : EStateL Γ T Sig SS RS M E K I :=
          { esL with g := { s₁L with st := Function.update s₁L.st P vp₁L }, h := rL.2 }
        let es₁F : EStateF Γ T Sig SS RS M E K I :=
          { esF with g := { s₁F with st := Function.update s₁F.st P vp₁F }, h := rF.1.2 }
        have hs₁ : SyncLFS fs Δcka qep mo j k_fs es₁L es₁F rF.2 :=
          syncLFS_after_startSend cka fs Δcka qep mo j k_fs P coins σ' kL kF idx? ext hs
            s₁L s₁F hs₁_stL hs₁_stF hs₁_epL hs₁_epF hs₁_idxL hs₁_idxF hs₁_tL hs₁_heal hs₁_leaks
            hs₁_restL hs₁_restF hsends_next_tcur hqep_tcur rL.2 rF.1.2 hr_tstar hr_ne hr_cL
            hr_tr hr_cnt hr_sc hr_ex hr_bs
        have hsends_es₁L : P.sendsIn (es₁L.g.st P).tcur = true := by
          dsimp only [es₁L]; rw [Function.update_self]; exact hsends_next_tcur
        convert leComp_transmitTail cka prng fs Δcka qep mo j k_fs P m esL.g esF.g hs₁ hsends_es₁L using 1
        · dsimp only [transmitTail, es₁L]
          rw [Function.update_self,
            vSendTail_update_eq (hooksLocalFixed cka prng fs mo j k_fs) P m s₁L vp₁L (fun _ _ => rfl)]
          simp only [run_liftH, StateT.run_bind, StateT.run_pure, bind_assoc,
            simulateQ_bind, simulateQ_pure, pure_bind]
          congr 1; funext x
          cases x.1 with
          | none =>
            simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          | some val =>
            rcases val with ⟨st', ct⟩
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              GameState.record, GameState.safeCh, Function.update_idem]
            rfl
        · dsimp only [transmitTail, es₁F]
          rw [Function.update_self,
            vSendTail_update_eq (hooksFS cka prng fs Δcka mo j) P m s₁F vp₁F (fun _ _ => rfl)]
          simp only [run_liftH, StateT.run_bind, StateT.run_pure, bind_assoc,
            simulateQ_bind, simulateQ_pure, pure_bind]
          congr 1; funext x
          cases x.1.1 with
          | none =>
            simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          | some val =>
            rcases val with ⟨st', ct⟩
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              GameState.record, GameState.safeCh, Function.update_idem]
            rfl
  · rw [Bool.not_eq_true] at hsends_next
    by_cases hgt : qep < esL.g.epoch P
    · have hgtF : qep < esF.g.epoch P := by rwa [← hs.hepoch]
      simp only [GameState.epMgmt, hsends_next_eq, hsends_next, Bool.false_eq_true, hgt, hgtF,
        ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
    · have hgtF : ¬ (qep < esF.g.epoch P) := by rwa [← hs.hepoch]
      simp only [GameState.epMgmt, hsends_next_eq, hsends_next, Bool.false_eq_true, hgt, hgtF,
        ↓reduceIte]
      have hdoom_eq : mo.policy.leakDoom esF.g esF.g = mo.policy.leakDoom esL.g esL.g := by
        simp only [Policy.leakDoom, ← hs.hepoch, ← hs.htL, ← hs.hleaks]
      rw [hdoom_eq]
      by_cases hdoom : mo.policy.leakDoom esL.g esL.g = true
      · simp only [hdoom, ↓reduceIte, abortE, StateT.run_modify, pure_bind,
          StateT.run_pure, simulateQ_pure]
        exact LeComp.pure (Or.inl (lhsDead_of_abort Δcka mo j esL))
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte]
        have hsends_cur : P.sendsIn (esL.g.epoch P) = true := by
          cases P <;> simp [Party.sendsIn] at hsends_next ⊢ <;> omega
        have hsends_tcur : P.sendsIn (esL.g.st P).tcur = true := by
          rw [hs.htcur_epoch P]; exact hsends_cur
        have hvSendL := vSend_eq_vSendTail_of_false (hooksLocalFixed cka prng fs mo j k_fs)
          esL.g P (esL.g.st P) m r (by rw [hs.hidL P, hs.htcur_epoch P]; exact hsends_next)
        have hvSendF := vSend_eq_vSendTail_of_false (hooksFS cka prng fs Δcka mo j)
          esF.g P (esF.g.st P) m r (by rw [hs.hidF P, ← hs.htcur P, hs.htcur_epoch P]; exact hsends_next)
        convert leComp_transmitTail cka prng fs Δcka qep mo j k_fs P m esL.g esF.g hs hsends_tcur using 1
        · dsimp only [transmitTail]
          simp only [hvSendL, run_liftH, StateT.run_bind, bind_assoc, abortE]
          congr 2; funext x; cases x.1 <;> rfl
        · dsimp only [transmitTail]
          simp only [hvSendF, run_liftH, StateT.run_bind, bind_assoc, abortE]
          congr 3; funext x; cases x.1 <;> rfl

theorem filter_filter_ne_epoch {M C : Type} (xs : List (Record M C)) (pos : Pos) (t : ℕ)
    (hne : pos.epoch ≠ t) :
    (xs.filter (fun r => r.pos != pos)).filter (fun r => r.pos.epoch == t) =
      xs.filter (fun r => r.pos.epoch == t) := by
  induction xs with
  | nil => rfl
  | cons r rs ih =>
    rw [List.filter_cons]
    by_cases h1 : (r.pos != pos) = true
    · simp only [h1, ↓reduceIte, List.filter_cons, ih]
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      rw [Bool.not_eq_true, bne_eq_false_iff_eq] at h1
      subst h1
      have h2 : (r.pos.epoch == t) = false := beq_eq_false_iff_ne.mpr hne
      rw [List.filter_cons]
      simp only [h2, Bool.false_eq_true, ↓reduceIte, ih]

theorem filter_map_filter_delete (xs : List (Record M (Header T × E)))
    (P : Party) (t drop : ℕ)
    (hwf : ∀ r ∈ xs, r.pos.epoch = t → r.pos.sender = P) :
    (((xs.filter (fun r => r.pos != (⟨P, t, drop⟩ : Pos))).filter
        (fun r => r.pos.epoch == t)).map
        (fun r => (⟨r.pos.idx, r.ct.1, r.msg, r.ct.2⟩ : FSAEAD.Record (Header T) M E))) =
      ((xs.filter (fun r => r.pos.epoch == t)).map
        (fun r => (⟨r.pos.idx, r.ct.1, r.msg, r.ct.2⟩ : FSAEAD.Record (Header T) M E))).filter
        (fun r' => r'.idx != drop) := by
  induction xs with
  | nil => rfl
  | cons r rs ih =>
    have ih' := ih (fun r' hr' => hwf r' (List.mem_cons_of_mem r hr'))
    by_cases he : (r.pos.epoch == t) = true
    · have het : r.pos.epoch = t := of_decide_eq_true he
      have hs : r.pos.sender = P := hwf r List.mem_cons_self het
      have hpos_eq : (r.pos != (⟨P, t, drop⟩ : Pos)) = (r.pos.idx != drop) := by
        cases rpos : r.pos with
        | mk s ep i =>
          have hs' : s = P := by simpa [rpos] using hs
          have het' : ep = t := by simpa [rpos] using het
          subst s ep
          by_cases hi : i = drop
          · subst i; simp
          · have hne1 : (⟨P, t, i⟩ : Pos) ≠ ⟨P, t, drop⟩ := by intro h; cases h; exact hi rfl
            rw [bne_iff_ne.mpr hne1, bne_iff_ne.mpr hi]
      rw [List.filter_cons, hpos_eq]
      by_cases hi : (r.pos.idx != drop) = true
      · simp only [hi, ↓reduceIte, List.filter_cons, he, List.map_cons, ih']
      · simp only [hi, Bool.false_eq_true, ↓reduceIte, List.filter_cons, he, List.map_cons, ih']
    · simp only [Bool.not_eq_true] at he
      rw [List.filter_cons]
      by_cases hp : (r.pos != (⟨P, t, drop⟩ : Pos)) = true
      · simp only [hp, ↓reduceIte, List.filter_cons, he, Bool.false_eq_true, ih']
      · simp only [hp, Bool.false_eq_true, ↓reduceIte, List.filter_cons, he, ih']

theorem map_filter_removeFromTransit (xs : List (FSAEAD.Record (Header T) M E)) (drop : ℕ) :
    (xs.filter (fun r => r.idx != drop)).map (fun r => (r.idx, r.ad, r.ct)) =
      (xs.map (fun r => (r.idx, r.ad, r.ct))).filter (fun x => x.1 != drop) := by
  induction xs with
  | nil => rfl
  | cons r rs ih =>
    rw [List.filter_cons, List.map_cons, List.filter_cons]
    by_cases h : (r.idx != drop) = true
    · simp only [h, ↓reduceIte, List.map_cons, ih]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, ih]

theorem find?_map_eq (xs : List (FSAEAD.Record (Header T) M E)) (c : Header T × E) :
    (xs.map (fun r => (r.idx, r.ad, r.ct))).find? (fun x => x.2 == c) =
      (xs.find? (fun r => r.ad == c.1 && r.ct == c.2)).map (fun r => (r.idx, r.ad, r.ct)) := by
  induction xs with
  | nil => rfl
  | cons r rs ih =>
    have hpred : (((r.idx, r.ad, r.ct).2 == c) : Bool) = (r.ad == c.1 && r.ct == c.2) := by
      rcases c with ⟨h, e⟩
      by_cases h1 : r.ad = h
      · subst h1
        by_cases h2 : r.ct = e
        · subst h2; simp
        · have hne : (r.ad, r.ct) ≠ (r.ad, e) := by intro heq; cases heq; exact h2 rfl
          rw [beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr h2, Bool.and_false]
      · have hne : (r.ad, r.ct) ≠ (h, e) := by intro heq; cases heq; exact h1 rfl
        rw [beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr h1, Bool.false_and]
    rw [List.map_cons, List.find?_cons, List.find?_cons, hpred]
    cases (r.ad == c.1 && r.ct == c.2) <;> simp [ih]

theorem find?_map_filter (xs : List (Record M (Header T × E))) (S : Party) (t : ℕ)
    (c : Header T × E) (hc : c.1.1 = t)
    (hwf : ∀ r ∈ xs, r.pos.epoch = r.ct.1.1 ∧ (r.pos.epoch = t → r.pos.sender = S)) :
    ((xs.filter (fun r => r.pos.epoch == t)).map
        (fun r => (⟨r.pos.idx, r.ct.1, r.msg, r.ct.2⟩ : FSAEAD.Record (Header T) M E))).find?
        (fun r' => r'.ad == c.1 && r'.ct == c.2) =
      (xs.find? (fun r => r.pos.sender == S && decide (r.ct = c))).map
        (fun r => (⟨r.pos.idx, r.ct.1, r.msg, r.ct.2⟩ : FSAEAD.Record (Header T) M E)) := by
  induction xs with
  | nil => rfl
  | cons r rs ih =>
    have ih' := ih (fun r' hr' => hwf r' (List.mem_cons_of_mem r hr'))
    have hr := hwf r List.mem_cons_self
    rw [List.filter_cons]
    by_cases he : (r.pos.epoch == t) = true
    · have het : r.pos.epoch = t := of_decide_eq_true he
      have hs : r.pos.sender = S := hr.2 het
      have hpred : ((r.ct.1 == c.1 && r.ct.2 == c.2) : Bool) =
          (r.pos.sender == S && decide (r.ct = c)) := by
        rw [hs, beq_self_eq_true, Bool.true_and]
        rcases rct : r.ct with ⟨h1, e1⟩
        rcases c with ⟨h2, e2⟩
        by_cases hh : h1 = h2
        · subst hh
          by_cases heq : e1 = e2
          · subst heq; simp
          · have hne : (h1, e1) ≠ (h1, e2) := by intro h; cases h; exact heq rfl
            rw [beq_self_eq_true, Bool.true_and, beq_eq_false_iff_ne.mpr heq,
              decide_eq_false hne]
        · have hne : (h1, e1) ≠ (h2, e2) := by intro h; cases h; exact hh rfl
          rw [beq_eq_false_iff_ne.mpr hh, Bool.false_and, decide_eq_false hne]
      simp only [he, ↓reduceIte]
      rw [List.map_cons, List.find?_cons, List.find?_cons]
      dsimp only
      rw [hpred]
      cases (r.pos.sender == S && decide (r.ct = c)) <;> simp [ih']
    · simp only [he, Bool.false_eq_true, ↓reduceIte]
      have hne_ep : r.pos.epoch ≠ t := by
        intro h; exact absurd (decide_eq_true h) (by simpa using he)
      have hne_ct : r.ct ≠ c := by
        intro hct
        apply hne_ep
        rw [hr.1, hct, hc]
      have hpred_false : (r.pos.sender == S && decide (r.ct = c)) = false := by
        rw [decide_eq_false hne_ct, Bool.and_false]
      rw [List.find?_cons, hpred_false, ih']

theorem syncLFS_accept_local (j : ℕ) (k_fs : K) (P : Party) (t i' : ℕ)
    (rs' : RS) (idx? : Option ℕ)
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st)
    (hsends_false : P.sendsIn t = false)
    (ht_le : t ≤ (esL.g.st P).tcur + 1)
    (ht_ne : t ≠ mo.tStar)
    (hidx_ne : idx? ≠ some j)
    (vpL' : PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ))
    (vpF' : VP Γ T Sig (Option SS) (Option RS))
    (hidL' : vpL'.id = P) (hidF' : vpF'.id = P)
    (hγ' : vpL'.γ = vpF'.γ) (hroot' : vpL'.root = vpF'.root)
    (hTcurL' : vpL'.curCkaMsg = (esL.g.st P).curCkaMsg) (hTcurF' : vpF'.curCkaMsg = (esF.g.st P).curCkaMsg)
    (htcurL' : vpL'.tcur = max (esL.g.st P).tcur t)
    (htcurF' : vpF'.tcur = max (esF.g.st P).tcur t)
    (hvSL' : vpL'.vS = (esL.g.st P).vS) (hvSF' : vpF'.vS = (esF.g.st P).vS)
    (hvRL' : vpL'.vR = Function.update (esL.g.st P).vR t (some (rs', idx?)))
    (hvRF' : vpF'.vR = Function.update (esF.g.st P).vR t (some (some rs'))) :
    SyncLFS fs Δcka qep mo j k_fs
      { esL with g := esL.g.accept P vpL' ⟨P.other, t, i'⟩, h := { esL.h with lastIdx := idx? } }
      { esF with g := esF.g.accept P vpF' ⟨P.other, t, i'⟩, h := esF.h }
      st := by
  have hmax_choice : max (esL.g.st P).tcur t = (esL.g.st P).tcur ∨ max (esL.g.st P).tcur t = t := by
    omega
  have hle_tcur : ∀ Q, (esL.g.st Q).tcur ≤ ((esL.g.accept P vpL' ⟨P.other, t, i'⟩).st Q).tcur := by
    intro Q
    simp only [GameState.accept, GameState.delete]
    by_cases hQ : Q = P
    · subst Q; rw [Function.update_self, htcurL']; exact Nat.le_max_left _ _
    · rw [Function.update_of_ne hQ]
  have hSenderJ_iff :
      SenderIsJ mo j { esL with g := esL.g.accept P vpL' ⟨P.other, t, i'⟩, h := { esL.h with lastIdx := idx? } } ↔
        SenderIsJ mo j esL := Iff.rfl
  refine
    { habortL := hs.habortL
      habortF := hs.habortF
      hwinL := hs.hwinL
      hwinF := hs.hwinF
      hwinFS := hs.hwinFS
      hendedFS := hs.hendedFS
      hchallFS := hs.hchallFS
      hextF := hs.hextF
      hepoch := by simp only [GameState.accept, GameState.delete, hs.hepoch]
      hidx := hs.hidx
      htL := hs.htL
      htrans := by simp only [GameState.accept, GameState.delete, hs.htrans]
      hchall := by simp only [GameState.accept, GameState.delete, hs.hchall, List.filter_nil]
      hchallF := by simp only [GameState.accept, GameState.delete, hs.hchallF, List.filter_nil]
      hcomp := by simp only [GameState.accept, GameState.delete, hs.hcomp]
      hcomp_inv := comp_inv_accept esL.g (2 + Δcka) P vpL' ⟨P.other, t, i'⟩ hs.hcomp_inv
      hmaxAcc := by simp only [GameState.accept, GameState.delete, hs.hmaxAcc]
      hb := hs.hb
      hleaks := hs.hleaks
      hcorrs := hs.hcorrs
      hbs := hs.hbs
      hcache_zero := hs.hcache_zero
      hcache_gt := fun t' ht' => hs.hcache_gt t' (lt_of_le_of_lt (hle_tcur _) ht')
      hsess_before := fun ht' h1 h2 => hs.hsess_before (lt_of_le_of_lt (hle_tcur _) ht') h1 h2
      hidL := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst Q; rw [Function.update_self]; exact hidL'
        · rw [Function.update_of_ne hQ]; exact hs.hidL Q
      hidF := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst Q; rw [Function.update_self]; exact hidF'
        · rw [Function.update_of_ne hQ]; exact hs.hidF Q
      hroot := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst Q; simp only [Function.update_self, hroot']
        · simp only [Function.update_of_ne hQ, hs.hroot Q]
      hγ := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst Q; simp only [Function.update_self, hγ']
        · simp only [Function.update_of_ne hQ, hs.hγ Q]
      hTcur := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst Q; simp only [Function.update_self, hTcurL', hTcurF', hs.hTcur P]
        · simp only [Function.update_of_ne hQ, hs.hTcur Q]
      htcur := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst Q; simp only [Function.update_self, htcurL', htcurF', hs.htcur P]
        · simp only [Function.update_of_ne hQ, hs.htcur Q]
      htcur_epoch := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst Q; simp only [Function.update_self, htcurL', hs.htcur_epoch P]
        · simp only [Function.update_of_ne hQ, hs.htcur_epoch Q]
      htcur_le_qep := fun Q hQs => by
        simp only [GameState.accept, GameState.delete] at hQs ⊢
        by_cases hQ : Q = P
        · subst Q
          rw [Function.update_self, htcurL'] at hQs ⊢
          rcases hmax_choice with hmax | hmax
          · rw [hmax] at hQs ⊢; exact hs.htcur_le_qep P hQs
          · rw [hmax, hsends_false] at hQs; cases hQs
        · rw [Function.update_of_ne hQ] at hQs ⊢
          exact hs.htcur_le_qep Q hQs
      hTcur_sender := fun Q hQs hpos => by
        simp only [GameState.accept, GameState.delete] at hQs hpos ⊢
        by_cases hQ : Q = P
        · subst Q
          rw [Function.update_self] at hQs hpos ⊢
          rw [htcurL'] at hQs hpos ⊢
          rw [hTcurL']
          rcases hmax_choice with hmax | hmax
          · rw [hmax] at hQs hpos ⊢; exact hs.hTcur_sender P hQs hpos
          · rw [hmax, hsends_false] at hQs; cases hQs
        · rw [Function.update_of_ne hQ] at hQs hpos ⊢
          exact hs.hTcur_sender Q hQs hpos
      hvS_some := fun Q hQs => by
        simp only [GameState.accept, GameState.delete] at hQs ⊢
        by_cases hQ : Q = P
        · subst Q
          rw [Function.update_self] at hQs ⊢
          rw [htcurL'] at hQs
          rw [hvSL']
          rcases hmax_choice with hmax | hmax
          · rw [hmax] at hQs; exact hs.hvS_some P hQs
          · rw [hmax, hsends_false] at hQs; cases hQs
        · rw [Function.update_of_ne hQ] at hQs ⊢
          exact hs.hvS_some Q hQs
      hvS := fun Q => by
        simp only [GameState.accept, GameState.delete, hSenderJ_iff]
        by_cases hQ : Q = P
        · subst Q
          simp only [Function.update_self, hvSL', hvSF', htcurL']
          rcases hs.hvS P with ⟨h1, h2⟩ | ⟨ss, idx₀, h1, h2, hne, hnotJ⟩ |
            ⟨hP, hle, hqep, hsends_imp, hsJ, h1, h2⟩
          · exact Or.inl ⟨h1, h2⟩
          · right; left
            refine ⟨ss, idx₀, h1, h2, hne, fun hPs hmax => hnotJ hPs ?_⟩
            omega
          · right; right
            refine ⟨hP, le_trans hle (Nat.le_max_left _ _), hqep, fun hPs => ?_, hsJ, h1, h2⟩
            rcases hmax_choice with hm | hm
            · rw [hm] at hPs ⊢; exact hsends_imp hPs
            · rw [hm, hsends_false] at hPs; cases hPs
        · simp only [Function.update_of_ne hQ]
          exact hs.hvS Q
      hvR_other := fun Q t' hne => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst Q
          simp only [Function.update_self, hvRL', hvRF']
          by_cases ht' : t' = t
          · subst t'
            simp only [Function.update_self]
            exact Or.inr ⟨rs', idx?, rfl, rfl, hidx_ne⟩
          · simp only [Function.update_of_ne ht']
            exact hs.hvR_other P t' hne
        · simp only [Function.update_of_ne hQ]
          exact hs.hvR_other Q t' hne
      hvR_target_lt := fun hlt => by
        have hlt₀ : (esL.g.st (Party.receiverOf mo.tStar)).tcur < mo.tStar :=
          lt_of_le_of_lt (hle_tcur _) hlt
        have ⟨h1, h2, h3⟩ := hs.hvR_target_lt hlt₀
        simp only [GameState.accept, GameState.delete]
        by_cases hR : Party.receiverOf mo.tStar = P
        · rw [hR, Function.update_self, Function.update_self, hvRL', hvRF',
            Function.update_of_ne (Ne.symm ht_ne), Function.update_of_ne (Ne.symm ht_ne)]
          exact ⟨hR ▸ h1, hR ▸ h2, h3⟩
        · rw [Function.update_of_ne hR, Function.update_of_ne hR]
          exact ⟨h1, h2, h3⟩
      hvR_target_ge := fun hge => by
        simp only [GameState.accept, GameState.delete, hSenderJ_iff] at hge ⊢
        by_cases hR : Party.receiverOf mo.tStar = P
        · rw [hR, Function.update_self, htcurL'] at hge
          have hge₀ : mo.tStar ≤ (esL.g.st (Party.receiverOf mo.tStar)).tcur := by
            rw [hR]; omega
          have ⟨h1, h2, h3⟩ := hs.hvR_target_ge hge₀
          rw [hR, Function.update_self, Function.update_self, hvRL', hvRF',
            Function.update_of_ne (Ne.symm ht_ne), Function.update_of_ne (Ne.symm ht_ne)]
          exact ⟨h1, hR ▸ h2, hR ▸ h3⟩
        · rw [Function.update_of_ne hR] at hge ⊢
          rw [Function.update_of_ne hR]
          exact hs.hvR_target_ge hge
      hfsCount := hs.hfsCount
      hfsTrans := hs.hfsTrans
      hfsSCorr := hs.hfsSCorr
      htrans_wf := fun r hr => by
        simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
        obtain ⟨h1, h2, h3, h4, h5⟩ := hs.htrans_wf r hr.1
        refine ⟨h1, h2, le_trans h3 (hle_tcur _), h4, fun he hsJ => h5 he hsJ⟩
      hnot_senderJ := fun hnotJ => hs.hnot_senderJ hnotJ
      hsenderJ_trans := fun hsJ => by
        simp only [GameState.accept, GameState.delete]
        rw [filter_filter_ne_epoch esL.g.trans ⟨P.other, t, i'⟩ mo.tStar ht_ne]
        exact hs.hsenderJ_trans hsJ
      hcorr_sync := fun corrAt hcorr => by
        obtain ⟨h1, h2, h3, h4⟩ := hs.hcorr_sync corrAt hcorr
        refine ⟨h1, h2, h3, fun r hr he hlt => ?_⟩
        simp only [GameState.accept, GameState.delete, List.mem_filter] at hr ⊢
        exact ⟨h4 r hr.1 he hlt, hr.2⟩ }

theorem syncLFS_accept_ext (j : ℕ) (k_fs : K) (P : Party) (drop i' : ℕ) (rs' : RS)
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st)
    (hP : P = Party.receiverOf mo.tStar)
    (hsJ : SenderIsJ mo j esL)
    (vpL' : PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ))
    (vpF' : VP Γ T Sig (Option SS) (Option RS))
    (hidL' : vpL'.id = P) (hidF' : vpF'.id = P)
    (hγ' : vpL'.γ = vpF'.γ) (hroot' : vpL'.root = vpF'.root)
    (hTcurL' : vpL'.curCkaMsg = (esL.g.st P).curCkaMsg) (hTcurF' : vpF'.curCkaMsg = (esF.g.st P).curCkaMsg)
    (htcurL' : vpL'.tcur = max (esL.g.st P).tcur mo.tStar)
    (htcurF' : vpF'.tcur = max (esF.g.st P).tcur mo.tStar)
    (hvSL' : vpL'.vS = (esL.g.st P).vS) (hvSF' : vpF'.vS = (esF.g.st P).vS)
    (hvRL' : vpL'.vR = Function.update (esL.g.st P).vR mo.tStar (some (rs', some j)))
    (hvRF' : vpF'.vR = Function.update (esF.g.st P).vR mo.tStar (some none)) :
    SyncLFS fs Δcka qep mo j k_fs
      { esL with g := esL.g.accept P vpL' ⟨P.other, mo.tStar, drop⟩, h := { esL.h with lastIdx := some j } }
      { esF with g := esF.g.accept P vpF' ⟨P.other, mo.tStar, drop⟩,
                 h := { esF.h with fsTrans := esF.h.fsTrans.filter (·.1 != drop) } }
      (({ st with receiverState := rs', receiverIdx := max st.receiverIdx i', win := false } :
        FSGameState SS RS T M E).removeFromTransit drop) := by
  have hsends_false : P.sendsIn mo.tStar = false := hP ▸ sendsIn_receiverOf mo.tStar
  have hPother_sender : P.other = Party.senderOf mo.tStar := by
    rw [hP]; unfold Party.receiverOf; cases Party.senderOf mo.tStar <;> rfl
  have hmax_choice : max (esL.g.st P).tcur mo.tStar = (esL.g.st P).tcur ∨
      max (esL.g.st P).tcur mo.tStar = mo.tStar := by omega
  have hle_tcur : ∀ Q, (esL.g.st Q).tcur ≤ ((esL.g.accept P vpL' ⟨P.other, mo.tStar, drop⟩).st Q).tcur := by
    intro Q
    simp only [GameState.accept, GameState.delete]
    by_cases hQ : Q = P
    · subst Q; rw [Function.update_self, htcurL']; exact Nat.le_max_left _ _
    · rw [Function.update_of_ne hQ]
  have hSenderJ_iff :
      SenderIsJ mo j { esL with g := esL.g.accept P vpL' ⟨P.other, mo.tStar, drop⟩, h := { esL.h with lastIdx := some j } } ↔
        SenderIsJ mo j esL := Iff.rfl
  refine
    { habortL := hs.habortL
      habortF := hs.habortF
      hwinL := hs.hwinL
      hwinF := hs.hwinF
      hwinFS := rfl
      hendedFS := hs.hendedFS
      hchallFS := by simp only [FSAEAD.State.removeFromTransit, hs.hchallFS, List.filter_nil]
      hextF := hs.hextF
      hepoch := by simp only [GameState.accept, GameState.delete, hs.hepoch]
      hidx := hs.hidx
      htL := hs.htL
      htrans := by simp only [GameState.accept, GameState.delete, hs.htrans]
      hchall := by simp only [GameState.accept, GameState.delete, hs.hchall, List.filter_nil]
      hchallF := by simp only [GameState.accept, GameState.delete, hs.hchallF, List.filter_nil]
      hcomp := by simp only [GameState.accept, GameState.delete, hs.hcomp]
      hcomp_inv := comp_inv_accept esL.g (2 + Δcka) P vpL' ⟨P.other, mo.tStar, drop⟩ hs.hcomp_inv
      hmaxAcc := by simp only [GameState.accept, GameState.delete, hs.hmaxAcc]
      hb := hs.hb
      hleaks := hs.hleaks
      hcorrs := hs.hcorrs
      hbs := hs.hbs
      hcache_zero := hs.hcache_zero
      hcache_gt := fun t' ht' => hs.hcache_gt t' (lt_of_le_of_lt (hle_tcur _) ht')
      hsess_before := fun ht' h1 h2 => hs.hsess_before (lt_of_le_of_lt (hle_tcur _) ht') h1 h2
      hidL := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst Q; rw [Function.update_self]; exact hidL'
        · rw [Function.update_of_ne hQ]; exact hs.hidL Q
      hidF := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst Q; rw [Function.update_self]; exact hidF'
        · rw [Function.update_of_ne hQ]; exact hs.hidF Q
      hroot := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst Q; simp only [Function.update_self, hroot']
        · simp only [Function.update_of_ne hQ, hs.hroot Q]
      hγ := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst Q; simp only [Function.update_self, hγ']
        · simp only [Function.update_of_ne hQ, hs.hγ Q]
      hTcur := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst Q; simp only [Function.update_self, hTcurL', hTcurF', hs.hTcur P]
        · simp only [Function.update_of_ne hQ, hs.hTcur Q]
      htcur := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst Q; simp only [Function.update_self, htcurL', htcurF', hs.htcur P]
        · simp only [Function.update_of_ne hQ, hs.htcur Q]
      htcur_epoch := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst Q; simp only [Function.update_self, htcurL', hs.htcur_epoch P]
        · simp only [Function.update_of_ne hQ, hs.htcur_epoch Q]
      htcur_le_qep := fun Q hQs => by
        simp only [GameState.accept, GameState.delete] at hQs ⊢
        by_cases hQ : Q = P
        · subst Q
          rw [Function.update_self, htcurL'] at hQs ⊢
          rcases hmax_choice with hmax | hmax
          · rw [hmax] at hQs ⊢; exact hs.htcur_le_qep P hQs
          · rw [hmax, hsends_false] at hQs; cases hQs
        · rw [Function.update_of_ne hQ] at hQs ⊢
          exact hs.htcur_le_qep Q hQs
      hTcur_sender := fun Q hQs hpos => by
        simp only [GameState.accept, GameState.delete] at hQs hpos ⊢
        by_cases hQ : Q = P
        · subst Q
          rw [Function.update_self] at hQs hpos ⊢
          rw [htcurL'] at hQs hpos ⊢
          rw [hTcurL']
          rcases hmax_choice with hmax | hmax
          · rw [hmax] at hQs hpos ⊢; exact hs.hTcur_sender P hQs hpos
          · rw [hmax, hsends_false] at hQs; cases hQs
        · rw [Function.update_of_ne hQ] at hQs hpos ⊢
          exact hs.hTcur_sender Q hQs hpos
      hvS_some := fun Q hQs => by
        simp only [GameState.accept, GameState.delete] at hQs ⊢
        by_cases hQ : Q = P
        · subst Q
          rw [Function.update_self] at hQs ⊢
          rw [htcurL'] at hQs
          rw [hvSL']
          rcases hmax_choice with hmax | hmax
          · rw [hmax] at hQs; exact hs.hvS_some P hQs
          · rw [hmax, hsends_false] at hQs; cases hQs
        · rw [Function.update_of_ne hQ] at hQs ⊢
          exact hs.hvS_some Q hQs
      hvS := fun Q => by
        simp only [GameState.accept, GameState.delete, FSAEAD.State.removeFromTransit, hSenderJ_iff]
        by_cases hQ : Q = P
        · subst Q
          simp only [Function.update_self, hvSL', hvSF', htcurL']
          rcases hs.hvS P with ⟨h1, h2⟩ | ⟨ss, idx₀, h1, h2, hne, hnotJ⟩ |
            ⟨hPs, hle, hqep, hsends_imp, _, h1, h2⟩
          · exact Or.inl ⟨h1, h2⟩
          · right; left
            refine ⟨ss, idx₀, h1, h2, hne, fun hPs _ => ?_⟩
            have : P.sendsIn mo.tStar = true := hPs ▸ sendsIn_senderOf mo.tStar
            rw [hsends_false] at this; cases this
          · exfalso
            have : P.sendsIn mo.tStar = true := hPs ▸ sendsIn_senderOf mo.tStar
            rw [hsends_false] at this; cases this
        · simp only [Function.update_of_ne hQ]
          exact hs.hvS Q
      hvR_other := fun Q t' hne => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst Q
          simp only [Function.update_self, hvRL', hvRF']
          have ht' : t' ≠ mo.tStar := fun h => hne (by rw [hP, h])
          simp only [Function.update_of_ne ht']
          exact hs.hvR_other P t' hne
        · simp only [Function.update_of_ne hQ]
          exact hs.hvR_other Q t' hne
      hvR_target_lt := fun hlt => by
        exfalso
        simp only [GameState.accept, GameState.delete, ← hP, Function.update_self, htcurL'] at hlt
        omega
      hvR_target_ge := fun _ => by
        simp only [GameState.accept, GameState.delete, ← hP, Function.update_self, hvRL', hvRF',
          FSAEAD.State.removeFromTransit, hSenderJ_iff]
        exact ⟨hsJ, trivial, trivial⟩
      hfsCount := hs.hfsCount
      hfsTrans := by
        simp only [FSAEAD.State.removeFromTransit, hs.hfsTrans]
        exact (map_filter_removeFromTransit st.inTransit drop).symm
      hfsSCorr := hs.hfsSCorr
      htrans_wf := fun r hr => by
        simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
        obtain ⟨h1, h2, h3, h4, h5⟩ := hs.htrans_wf r hr.1
        refine ⟨h1, h2, le_trans h3 (hle_tcur _), h4, fun he hsJ' => h5 he hsJ'⟩
      hnot_senderJ := fun hnotJ => absurd hsJ hnotJ
      hsenderJ_trans := fun _ => by
        simp only [GameState.accept, GameState.delete, FSAEAD.State.removeFromTransit,
          hs.hsenderJ_trans hsJ]
        refine (filter_map_filter_delete esL.g.trans P.other mo.tStar drop ?_).symm
        intro r hr he
        rw [(hs.htrans_wf r hr).2.1, he, hPother_sender]
      hcorr_sync := fun corrAt hcorr => by
        obtain ⟨h1, h2, h3, h4⟩ := hs.hcorr_sync corrAt hcorr
        refine ⟨h1, h2, h3, fun r hr he hlt => ?_⟩
        simp only [GameState.accept, GameState.delete, List.mem_filter] at hr ⊢
        exact ⟨h4 r hr.1 he hlt, hr.2⟩ }

theorem syncLFS_with_book (j : ℕ) (k_fs : K)
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st)
    (hL' : LState T Sig K I)
    (hF' : FSState T Sig K I SS RS E)
    (hbs' : BookSync mo j k_fs hL' hF')
    (hcL : hL'.cache = esL.h.cache)
    (hsess : mo.tL.isSome = true → mo.tStar = mo.tH → hL'.sessions = esL.h.sessions)
    (hext : hF'.ext = esF.h.ext)
    (hcnt : hF'.fsCount = esF.h.fsCount)
    (htr : hF'.fsTrans = esF.h.fsTrans)
    (hsc : hF'.fsSCorr = esF.h.fsSCorr) :
    SyncLFS fs Δcka qep mo j k_fs { esL with h := hL' } { esF with h := hF' } st := by
  have hSenderJ_iff : SenderIsJ mo j { esL with h := hL' } ↔ SenderIsJ mo j esL := by
    simp only [SenderIsJ, hcL]
  refine
    { habortL := hs.habortL
      habortF := hs.habortF
      hwinL := hs.hwinL
      hwinF := hs.hwinF
      hwinFS := hs.hwinFS
      hendedFS := hs.hendedFS
      hchallFS := hs.hchallFS
      hextF := hext.trans hs.hextF
      hepoch := hs.hepoch
      hidx := hs.hidx
      htL := hs.htL
      htrans := hs.htrans
      hchall := hs.hchall
      hchallF := hs.hchallF
      hcomp := hs.hcomp
      hcomp_inv := hs.hcomp_inv
      hmaxAcc := hs.hmaxAcc
      hb := hs.hb
      hleaks := hs.hleaks
      hcorrs := hs.hcorrs
      hbs := hbs'
      hcache_zero := by rw [hcL]; exact hs.hcache_zero
      hcache_gt := fun t ht => by rw [hcL]; exact hs.hcache_gt t ht
      hsess_before := fun ht h1 h2 => by rw [hsess h1 h2]; exact hs.hsess_before ht h1 h2
      hidL := hs.hidL
      hidF := hs.hidF
      hroot := hs.hroot
      hγ := hs.hγ
      hTcur := hs.hTcur
      htcur := hs.htcur
      htcur_epoch := hs.htcur_epoch
      htcur_le_qep := hs.htcur_le_qep
      hTcur_sender := fun P h1 h2 => by rw [hcL]; exact hs.hTcur_sender P h1 h2
      hvS_some := hs.hvS_some
      hvS := fun P => by rw [hSenderJ_iff]; exact hs.hvS P
      hvR_other := hs.hvR_other
      hvR_target_lt := hs.hvR_target_lt
      hvR_target_ge := fun hge => by rw [hSenderJ_iff]; exact hs.hvR_target_ge hge
      hfsCount := hcnt.trans hs.hfsCount
      hfsTrans := htr.trans hs.hfsTrans
      hfsSCorr := hsc.trans hs.hfsSCorr
      htrans_wf := fun r hr => by
        rw [hcL, hSenderJ_iff]
        exact hs.htrans_wf r hr
      hnot_senderJ := fun hnot => hs.hnot_senderJ (fun h => hnot (hSenderJ_iff.mpr h))
      hsenderJ_trans := fun hsJ => hs.hsenderJ_trans (hSenderJ_iff.mp hsJ)
      hcorr_sync := fun corrAt hcorr => by
        rw [hSenderJ_iff]
        exact hs.hcorr_sync corrAt hcorr }

def vRecvTail {tspec : OracleSpec.{0, 0} ι} {Γv Sv SSv RSv HS : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (ctx : Ctx Γv T Sv SSv RSv M E) (P : Party) (s₁ : VP Γv T Sv SSv RSv)
    (c : Header T × E) (rec : Option (Record M (Header T × E))) :
    HM tspec HS (Option (Option (VP Γv T Sv SSv RSv × ℕ × ℕ × M))) := do
  let t := c.1.1
  match s₁.vR t with
  | none => return some none
  | some v =>
    match ← hk.fsRecv ctx P t v c.1 c.2 rec with
    | none => return none
    | some none => return some none
    | some (some (v', i, m)) =>
      return some (some ({ s₁ with vR := Function.update s₁.vR t (some v') }, t, i, m))

theorem vRecv_eq_vRecvTail_of_ne {tspec : OracleSpec.{0, 0} ι} {Γv Sv SSv RSv HS : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (ctx : Ctx Γv T Sv SSv RSv M E) (P : Party) (vp : VP Γv T Sv SSv RSv)
    (c : Header T × E) (rec : Option (Record M (Header T × E)))
    (hcond : (vp.id.sendsIn c.1.1 || decide (vp.tcur + 1 < c.1.1)) = false)
    (hne : c.1.1 ≠ vp.tcur + 1) :
    vRecv hk ctx P vp c rec = vRecvTail hk ctx P vp c rec := by
  dsimp only [vRecv, vRecvTail]
  simp only [hcond, Bool.false_eq_true, hne, ↓reduceIte, pure_bind]
  rfl

theorem vRecv_eq_bind_vRecvTail_of_eq {tspec : OracleSpec.{0, 0} ι} {Γv Sv SSv RSv HS : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (ctx : Ctx Γv T Sv SSv RSv M E) (P : Party) (vp : VP Γv T Sv SSv RSv)
    (c : Header T × E) (rec : Option (Record M (Header T × E))) (Tn : T)
    (hcond : (vp.id.sendsIn c.1.1 || decide (vp.tcur + 1 < c.1.1)) = false)
    (heq : c.1.1 = vp.tcur + 1)
    (hTn : c.1.2 = some Tn) :
    vRecv hk ctx P vp c rec =
      (do
        match ← hk.startRecv ctx P c.1.1 vp.γ vp.root Tn with
        | none => return none
        | some none => return some none
        | some (some (γ', σ', rs)) =>
          vRecvTail hk ctx P
            { vp with tcur := c.1.1, γ := γ', root := σ',
                      vR := Function.update vp.vR c.1.1 (some rs) } c rec) := by
  dsimp only [vRecv, vRecvTail]
  simp only [hcond, Bool.false_eq_true, ↓reduceIte]
  simp only [heq, hTn, ↓reduceIte, bind_assoc, pure_bind]
  rfl

@[simp]
theorem beq_header_eq_instBEqOfDecidableEq (a b : Header T) :
    @BEq.beq (Header T) instBEqOfDecidableEq a b = (a == b) := by
  by_cases h : a = b <;> simp [h]

theorem fs_deliver_of_ended_false (st : FSGameState SS RS T M E) (c : Header T × E)
    (r_tr : FSAEAD.Record (Header T) M E)
    (hended : st.ended = false)
    (hchall : st.challengesInTransit = [])
    (hfind : st.inTransit.find? (fun r' => r'.ad == c.1 && r'.ct == c.2) = some r_tr) :
    FSAEAD.deliver fs st c.1 c.2 =
      match fs.receive st.receiverState c.1 c.2 with
      | none =>
        let missed := !st.isCompromised r_tr.idx && decide (r_tr.idx ≤ st.receiverIdx + fs.maxSkip + 1)
        (some FSAEAD.ReceiveResult.rejected, { st with win := st.win || missed })
      | some (rs', i', m') =>
        let forged := (!st.isCompromised r_tr.idx && decide (r_tr.idx ≤ st.receiverIdx + fs.maxSkip + 1)) &&
                      (i' != r_tr.idx || m' != r_tr.msg)
        let st' := { st with receiverState := rs',
                             receiverIdx := max st.receiverIdx i',
                             win := st.win || forged }
        (some (FSAEAD.ReceiveResult.accepted i' (some m')), st'.removeFromTransit r_tr.idx) := by
  unfold FSAEAD.deliver
  split
  · rename_i h
    exfalso; rw [hended] at h; exact Bool.false_ne_true h
  · simp only [beq_header_eq_instBEqOfDecidableEq, hfind]
    cases fs.receive st.receiverState c.1 c.2 with
    | none => rfl
    | some val =>
      rcases val with ⟨rs', i', m'⟩
      simp only [hchall, List.contains_nil, Bool.false_eq_true, ↓reduceIte]

theorem fs_inject_of_ended_false (st : FSGameState SS RS T M E) (c : Header T × E)
    (hended : st.ended = false)
    (hany : st.inTransit.any (fun r' => r'.ad == c.1 && r'.ct == c.2) = false) :
    FSAEAD.inject fs st c.1 c.2 =
      match fs.receive st.receiverState c.1 c.2 with
      | none => (some FSAEAD.ReceiveResult.rejected, st)
      | some (rs', i', m') =>
        let forged := !st.isCompromised i'
        let st' := { st with receiverState := rs',
                             receiverIdx := max st.receiverIdx i',
                             win := st.win || forged }
        (some (FSAEAD.ReceiveResult.accepted i' (some m')), st'.removeFromTransit i') := by
  unfold FSAEAD.inject
  split
  · rename_i h
    exfalso
    simp [beq_header_eq_instBEqOfDecidableEq, hended, hany] at h
  · rfl

theorem accept_update_self {St Msg C : Type} (s : GameState St Msg C) (P : Party) (st' : St) (pos : Pos) :
    { s.accept P st' pos with st := Function.update (s.accept P st' pos).st P st' } = s.accept P st' pos := by
  simp [GameState.accept]

def deliverTail {tspec : OracleSpec.{0, 0} ι} {Γv Sv SSv RSv HS : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (P : Party) (c : Header T × E) (r : Record M (Header T × E))
    (s₁ : VP Γv T Sv SSv RSv)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    TComp tspec (Option (RecvResult M) × EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :=
  (do
    let s := es.g
    let must := (mo.cfg (M := M)).deliverWin && s.mustBeCorrect fs.maxSkip P r
    match ← liftH (vRecvTail hk s P s₁ c (some r)) with
    | none =>
      abortE
      return none
    | some none =>
      if must then
        modify fun (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) =>
          { es with g := { es.g with win := true } }
      return some RecvResult.rejected
    | some (some (st', t', i', m')) =>
      match ← commitE hk s P (s.st P) st' r.pos with
      | none => return none
      | some s₂ =>
        let bad := must && !(decide ((t', i', m') = (r.pos.epoch, r.pos.idx, r.msg)))
        modify fun (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) =>
          { es with g := if bad then { s₂ with win := true } else s₂ }
        return some (RecvResult.accepted t' i' (if s.chall.contains r.pos then none else some m'))).run es

theorem inTransit_some_props
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    {j : ℕ} {k_fs : K}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st)
    (P : Party) (c : Header T × E) (r : Record M (Header T × E))
    (hin : esL.g.inTransit P.other c = some r) :
    r ∈ esL.g.trans ∧
    r.ct = c ∧
    r.pos = ⟨P.other, c.1.1, r.pos.idx⟩ ∧
    P.other = Party.senderOf c.1.1 ∧
    P = Party.receiverOf c.1.1 ∧
    P.sendsIn c.1.1 = false := by
  have hmem := List.mem_of_find?_eq_some hin
  have hpred := List.find?_some hin
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpred
  obtain ⟨hsender, hct⟩ := hpred
  obtain ⟨hepoch_eq, hsender_of, _⟩ := hs.htrans_wf r hmem
  have hepoch_c : r.pos.epoch = c.1.1 := by rw [hepoch_eq, hct]
  have hPother_s : P.other = Party.senderOf c.1.1 := by
    rw [← hsender, hsender_of, hepoch_c]
  have hP_recv : P = Party.receiverOf c.1.1 := by
    unfold Party.receiverOf
    rw [← hPother_s]
    cases P <;> rfl
  have hsends_f : P.sendsIn c.1.1 = false := hP_recv ▸ sendsIn_receiverOf c.1.1
  have hpos_eq : r.pos = ⟨P.other, c.1.1, r.pos.idx⟩ := by
    cases rpos : r.pos with
    | mk s ep idx =>
      have hs' : s = P.other := by simpa [rpos] using hsender
      have hep' : ep = c.1.1 := by simpa [rpos] using hepoch_c
      subst s ep; rfl
  exact ⟨hmem, hct, hpos_eq, hPother_s, hP_recv, hsends_f⟩

theorem leComp_deliverTail (j : ℕ) (k_fs : K) (hauth : mo.auth = true)
    (P : Party) (c : Header T × E) (r : Record M (Header T × E))
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st)
    (hin : esL.g.inTransit P.other c = some r)
    (ht_le : c.1.1 ≤ (esL.g.st P).tcur + 1)
    (s₁L : PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ))
    (s₁F : VP Γ T Sig (Option SS) (Option RS))
    (hidL' : s₁L.id = P) (hidF' : s₁F.id = P)
    (hγ' : s₁L.γ = s₁F.γ) (hroot' : s₁L.root = s₁F.root)
    (hTcurL' : s₁L.curCkaMsg = (esL.g.st P).curCkaMsg) (hTcurF' : s₁F.curCkaMsg = (esF.g.st P).curCkaMsg)
    (htcurL' : s₁L.tcur = max (esL.g.st P).tcur c.1.1)
    (htcurF' : s₁F.tcur = max (esF.g.st P).tcur c.1.1)
    (hvSL' : s₁L.vS = (esL.g.st P).vS) (hvSF' : s₁F.vS = (esF.g.st P).vS)
    (hvR_other' : ∀ t', t' ≠ c.1.1 → s₁L.vR t' = (esL.g.st P).vR t' ∧ s₁F.vR t' = (esF.g.st P).vR t')
    (hvR_c :
      (s₁L.vR c.1.1 = none ∧ s₁F.vR c.1.1 = none) ∨
      (∃ rs idx?, s₁L.vR c.1.1 = some (rs, idx?) ∧ s₁F.vR c.1.1 = some (some rs) ∧ idx? ≠ some j) ∨
      (c.1.1 = mo.tStar ∧ SenderIsJ mo j esL ∧
        s₁L.vR c.1.1 = some (st.receiverState, some j) ∧ s₁F.vR c.1.1 = some none)) :
    LeComp (StepRelFS fs Δcka qep mo j k_fs)
      (simulateQ lImpl
        (deliverTail fs mo (hooksLocalFixed cka prng fs mo j k_fs) P c r s₁L esL))
      ((simulateQ (implFS fs)
        (deliverTail fs mo (hooksFS cka prng fs Δcka mo j) P c r s₁F esF)).run st) := by
  obtain ⟨hmem, hct, hpos_eq, hPother_s, hP_recv, hsends_f⟩ := inTransit_some_props fs Δcka qep mo hs P c r hin
  have hdelWin : (mo.cfg (M := M)).deliverWin = false := by
    simp [Mode.cfg, hauth, Config.auth]
  have hvRL_upd : ∀ v, Function.update s₁L.vR c.1.1 v = Function.update (esL.g.st P).vR c.1.1 v := by
    intro v; funext t'
    by_cases ht' : t' = c.1.1
    · subst t'; simp
    · simp [Function.update_of_ne ht', (hvR_other' t' ht').1]
  have hvRF_upd : ∀ v, Function.update s₁F.vR c.1.1 v = Function.update (esF.g.st P).vR c.1.1 v := by
    intro v; funext t'
    by_cases ht' : t' = c.1.1
    · subst t'; simp
    · simp [Function.update_of_ne ht', (hvR_other' t' ht').2]
  rcases hvR_c with ⟨hnoneL, hnoneF⟩ | ⟨rs, idx?, hsomeL, hsomeF, hidx_ne⟩ |
    ⟨ht_star, hsJ, hsomeL, hsomeF⟩
  · dsimp only [deliverTail, vRecvTail]
    simp only [StateT.run_bind, StateT.run_pure, pure_bind, run_liftH,
      hnoneL, hnoneF, hdelWin, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      simulateQ_pure]
    exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
  · dsimp only [deliverTail, vRecvTail, hooksLocalFixed, hooksFS]
    simp only [StateT.run_bind, StateT.run_pure, pure_bind, run_liftH,
      hsomeL, hsomeF, hdelWin, Bool.false_and]
    cases hrcv : fs.receive rs c.1 c.2 with
    | none =>
      simp only [hrcv, Option.map_none, StateT.run_pure, pure_bind, Bool.false_eq_true,
        ↓reduceIte, simulateQ_pure]
      exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
    | some val =>
      rcases val with ⟨rs', i', m'⟩
      dsimp only [commitE, hooksLocalFixed, hooksFS]
      simp only [hrcv, Option.map_some, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        pure_bind, run_liftH, accept_update_self, Bool.false_and, Bool.false_eq_true,
        ↓reduceIte, hs.hchall, hs.hchallF, List.contains_nil, simulateQ_pure]
      by_cases ht_star : c.1.1 = mo.tStar
      · refine LeComp.pure (Or.inl (Or.inr ⟨hs.habortL, hs.hwinL, ?_, ?_⟩))
        · intro Q
          simp only [GameState.accept, GameState.delete]
          by_cases hQ : Q = P
          · subst Q; rw [Function.update_self]; exact hidL'
          · rw [Function.update_of_ne hQ]; exact hs.hidL Q
        · dsimp only [RWrongSession]
          have hP_tstar : P = Party.receiverOf mo.tStar := ht_star ▸ hP_recv
          simp only [GameState.accept, GameState.delete, ← hP_tstar, Function.update_self,
            htcurL', ht_star, Nat.le_max_right, true_and]
          intro rs₀ hrs₀
          injection hrs₀ with hpair
          injection hpair with _ hidx_eq
          exact hidx_ne hidx_eq
      · refine LeComp.pure (Or.inr (Or.inr ⟨rfl, ?_⟩))
        rw [hpos_eq]
        exact syncLFS_accept_local fs Δcka qep mo j k_fs P c.1.1 r.pos.idx rs' idx? hs
          hsends_f ht_le ht_star hidx_ne
          { s₁L with vR := Function.update s₁L.vR c.1.1 (some (rs', idx?)) }
          { s₁F with vR := Function.update s₁F.vR c.1.1 (some (some rs')) }
          hidL' hidF' hγ' hroot' hTcurL' hTcurF' htcurL' htcurF' hvSL' hvSF'
          (hvRL_upd _) (hvRF_upd _)
  · have hfind_tr :
        st.inTransit.find? (fun r' => r'.ad == c.1 && r'.ct == c.2) =
          some ⟨r.pos.idx, r.ct.1, r.msg, r.ct.2⟩ := by
      rw [hs.hsenderJ_trans hsJ,
        find?_map_filter esL.g.trans P.other mo.tStar c ht_star
          (fun r' hr' => ⟨(hs.htrans_wf r' hr').1, fun he => by
            rw [(hs.htrans_wf r' hr').2.1, he, ← ht_star, hPother_s]⟩)]
      have hin' : esL.g.trans.find? (fun r' => r'.pos.sender == P.other && decide (r'.ct = c)) = some r := hin
      rw [hin', Option.map_some]
    have hmatched :
        esF.h.fsTrans.find? (fun x => x.2 == c) = some (r.pos.idx, r.ct.1, r.ct.2) := by
      rw [hs.hfsTrans, find?_map_eq, hfind_tr, Option.map_some]
    dsimp only [deliverTail, vRecvTail, commitE, hooksLocalFixed, hooksFS]
    simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
      run_liftH, hsomeL, hsomeF, hs.hextF, hmatched, Option.isSome_some, ↓reduceIte,
      hdelWin, Bool.false_and, bind_assoc, simulateQ_bind, simulateQ_pure,
      simulateQ_implFS_deliverQuery,
      fs_deliver_of_ended_false fs st c ⟨r.pos.idx, r.ct.1, r.msg, r.ct.2⟩ hs.hendedFS hs.hchallFS hfind_tr]
    cases hrcv : fs.receive st.receiverState c.1 c.2 with
    | none =>
      simp only [hrcv, StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
        pure_bind, Bool.false_eq_true, ↓reduceIte]
      by_cases hwin' : (st.win || (!st.isCompromised r.pos.idx && decide (r.pos.idx ≤ st.receiverIdx + fs.maxSkip + 1))) = true
      · exact LeComp.pure (Or.inr (Or.inl hwin'))
      · rw [Bool.not_eq_true] at hwin'
        have hst_eq :
            { st with win := st.win || (!st.isCompromised r.pos.idx && decide (r.pos.idx ≤ st.receiverIdx + fs.maxSkip + 1)) } = st := by
          have hwin0 := hs.hwinFS
          cases st; dsimp only at hwin' hwin0 ⊢; congr; exact hwin'.trans hwin0.symm
        rw [hst_eq]
        exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
    | some val =>
      rcases val with ⟨rs', i', m'⟩
      simp only [hrcv, StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_bind, simulateQ_pure,
        pure_bind, Option.map_some, Option.getD_some, run_liftH, accept_update_self,
        hs.hchall, hs.hchallF, List.contains_nil, Bool.false_eq_true, ↓reduceIte]
      by_cases hwin' : (st.win || ((!st.isCompromised r.pos.idx && decide (r.pos.idx ≤ st.receiverIdx + fs.maxSkip + 1)) && (i' != r.pos.idx || m' != r.msg))) = true
      · refine LeComp.pure (Or.inr (Or.inl ?_))
        simp [FSAEAD.State.removeFromTransit, hwin']
      · rw [Bool.not_eq_true] at hwin'
        refine LeComp.pure (Or.inr (Or.inr ⟨rfl, ?_⟩))
        rw [hpos_eq, ht_star, hwin']
        exact syncLFS_accept_ext fs Δcka qep mo j k_fs P r.pos.idx i' rs' hs
          (ht_star ▸ hP_recv) hsJ
          { s₁L with vR := Function.update s₁L.vR mo.tStar (some (rs', some j)) }
          { s₁F with vR := Function.update s₁F.vR mo.tStar (some none) }
          hidL' hidF' hγ' hroot' hTcurL' hTcurF'
          (ht_star ▸ htcurL') (ht_star ▸ htcurF') hvSL' hvSF'
          (ht_star ▸ hvRL_upd _) (ht_star ▸ hvRF_upd _)

theorem leComp_deliverE (j : ℕ) (k_fs : K) (hauth : mo.auth = true)
    (q : Party × (Header T × E))
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st) :
    LeComp (StepRelFS fs Δcka qep mo j k_fs)
      (simulateQ lImpl
        ((deliverE (hooksLocalFixed cka prng fs mo j k_fs) fs.maxSkip mo.cfg q).run esL))
      ((simulateQ (implFS fs)
        ((deliverE (hooksFS cka prng fs Δcka mo j) fs.maxSkip mo.cfg q).run esF)).run st) := by
  rcases q with ⟨P, c⟩
  unfold deliverE
  simp only [StateT.run_bind, StateT.run_get, pure_bind,
    hs.habortL, hs.habortF, hs.hwinL, hs.hwinF, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  have hin_eq : esF.g.inTransit P.other c = esL.g.inTransit P.other c := by
    simp only [GameState.inTransit, hs.htrans]
  rw [hin_eq]
  cases hin : esL.g.inTransit P.other c with
  | none =>
    simp only [StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
  | some r =>
    obtain ⟨hmem, hct, hpos_eq, hPother_s, hP_recv, hsends_f⟩ :=
      inTransit_some_props fs Δcka qep mo hs P c r hin
    have hdelWin : (mo.cfg (M := M)).deliverWin = false := by
      simp [Mode.cfg, hauth, Config.auth]
    have hcondL_eq :
        ((esL.g.st P).id.sendsIn c.1.1 || decide ((esL.g.st P).tcur + 1 < c.1.1)) =
          decide ((esL.g.st P).tcur + 1 < c.1.1) := by
      rw [hs.hidL P, hsends_f, Bool.false_or]
    have hcondF_eq :
        ((esF.g.st P).id.sendsIn c.1.1 || decide ((esF.g.st P).tcur + 1 < c.1.1)) =
          decide ((esL.g.st P).tcur + 1 < c.1.1) := by
      rw [hs.hidF P, ← hs.htcur P, hsends_f, Bool.false_or]
    by_cases hgt : (esL.g.st P).tcur + 1 < c.1.1
    · have hcondL : ((esL.g.st P).id.sendsIn c.1.1 || decide ((esL.g.st P).tcur + 1 < c.1.1)) = true := by
        rw [hcondL_eq, decide_eq_true_eq]; exact hgt
      have hcondF : ((esF.g.st P).id.sendsIn c.1.1 || decide ((esF.g.st P).tcur + 1 < c.1.1)) = true := by
        rw [hcondF_eq, decide_eq_true_eq]; exact hgt
      dsimp only [vRecv]
      simp only [hcondL, hcondF, ↓reduceIte, run_liftH, StateT.run_pure, pure_bind,
        hdelWin, Bool.false_and, Bool.false_eq_true, simulateQ_pure]
      exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
    · have ht_le : c.1.1 ≤ (esL.g.st P).tcur + 1 := Nat.le_of_not_lt hgt
      have hcondL : ((esL.g.st P).id.sendsIn c.1.1 || decide ((esL.g.st P).tcur + 1 < c.1.1)) = false := by
        rw [hcondL_eq, decide_eq_false_iff_not]; exact hgt
      have hcondF : ((esF.g.st P).id.sendsIn c.1.1 || decide ((esF.g.st P).tcur + 1 < c.1.1)) = false := by
        rw [hcondF_eq, decide_eq_false_iff_not]; exact hgt
      by_cases heq : c.1.1 = (esL.g.st P).tcur + 1
      · have heqF : c.1.1 = (esF.g.st P).tcur + 1 := by rw [← hs.htcur P]; exact heq
        have hpos_c : 0 < c.1.1 := by omega
        obtain ⟨hepoch_r, _, _, hcache_r, _⟩ := hs.htrans_wf r hmem
        have hepoch_c : r.pos.epoch = c.1.1 := by rw [hepoch_r, hct]
        obtain ⟨Tc, σc, k_c, idx_c, hcache_c, hct1⟩ := hcache_r (hepoch_c ▸ hpos_c)
        have hTn : c.1.2 = some Tc := by
          have : c.1 = (r.pos.epoch, some Tc) := by rw [← hct, hct1]
          rw [this]
        have hvRecvL := vRecv_eq_bind_vRecvTail_of_eq (hooksLocalFixed cka prng fs mo j k_fs)
          esL.g P (esL.g.st P) c (some r) Tc hcondL heq hTn
        have hvRecvF := vRecv_eq_bind_vRecvTail_of_eq (hooksFS cka prng fs Δcka mo j)
          esF.g P (esF.g.st P) c (some r) Tc hcondF heqF hTn
        simp only [hvRecvL, hvRecvF, run_liftH, StateT.run_bind, bind_assoc,
          simulateQ_bind]
        rw [← hs.hγ P, ← hs.hroot P]
        refine LeComp.bind (leComp_startRecv cka prng fs Δcka mo j k_fs esL.g esF.g P c.1.1
          (esL.g.st P).γ (esL.g.st P).root Tc hs.hbs st) ?_
        intro rL rF ⟨hr_st, hr_cL, hr_cF, hr_tr, hr_cnt, hr_sc, hr_ex, hr_bs, hcases⟩
        rw [hr_st]
        rcases hcases with ⟨hL_none, hF_none⟩ | ⟨hL_snone, hF_snone, hr_sess⟩ |
          ⟨σ', kL, kF, idx?, ext, hL_some, hF_some, hext_eq, h_eq_j, h_ne_j, h_ne_t, h_origin⟩
        · simp only [hL_none, hF_none, StateT.run_pure, pure_bind, abortE,
            StateT.run_modify, simulateQ_pure]
          exact LeComp.pure (Or.inl (lhsDead_of_abort Δcka mo j _))
        · simp only [hL_snone, hF_snone, StateT.run_pure, pure_bind,
            hdelWin, Bool.false_and, Bool.false_eq_true, ↓reduceIte, simulateQ_pure]
          exact LeComp.pure (Or.inr (Or.inr ⟨rfl,
            syncLFS_with_book fs Δcka qep mo j k_fs hs rL.2 rF.1.2 hr_bs hr_cL
              (fun _ _ => hr_sess) hr_ex hr_cnt hr_tr hr_sc⟩))
        · simp only [hL_some, hF_some]
          have horigin_cache : ∃ σc', esL.h.cache c.1.1 = some (Tc, σc', kL, idx?) ∧
              σ' = σc' ∧ rL.2.sessions = esL.h.sessions := by
            rcases h_origin with h1 | ⟨_, _, hno_c, _⟩
            · exact h1
            · exfalso; exact hno_c Tc σc k_c idx_c (hepoch_c ▸ hcache_c) rfl
          obtain ⟨σc', hcache_c', hσ', hr_sess⟩ := horigin_cache
          have hs₁ : SyncLFS fs Δcka qep mo j k_fs { esL with h := rL.2 } { esF with h := rF.1.2 } st :=
            syncLFS_with_book fs Δcka qep mo j k_fs hs rL.2 rF.1.2 hr_bs hr_cL
              (fun _ _ => hr_sess) hr_ex hr_cnt hr_tr hr_sc
          let s₁L : PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ) :=
            { esL.g.st P with tcur := c.1.1, γ := (cka.receive (esL.g.st P).γ Tc).1, root := σ',
                              vR := Function.update (esL.g.st P).vR c.1.1 (some (fs.initReceiver kL, idx?)) }
          let s₁F : VP Γ T Sig (Option SS) (Option RS) :=
            { esF.g.st P with tcur := c.1.1, γ := (cka.receive (esL.g.st P).γ Tc).1, root := σ',
                              vR := Function.update (esF.g.st P).vR c.1.1
                                (some (if ext then none else some (fs.initReceiver kF))) }
          have hvR_c :
              (s₁L.vR c.1.1 = none ∧ s₁F.vR c.1.1 = none) ∨
              (∃ rs idx₀, s₁L.vR c.1.1 = some (rs, idx₀) ∧ s₁F.vR c.1.1 = some (some rs) ∧ idx₀ ≠ some j) ∨
              (c.1.1 = mo.tStar ∧ SenderIsJ mo j { esL with h := rL.2 } ∧
                s₁L.vR c.1.1 = some (st.receiverState, some j) ∧ s₁F.vR c.1.1 = some none) := by
            by_cases hj : idx? = some j
            · obtain ⟨hkL, ht_star⟩ := h_eq_j hj
              right; right
              have hsJ : SenderIsJ mo j { esL with h := rL.2 } := by
                right
                refine ⟨Tc, σc', kL, ?_⟩
                dsimp only
                rw [hr_cL, ← ht_star, ← hj]
                exact hcache_c'
              have hlt_tstar : (esL.g.st (Party.receiverOf mo.tStar)).tcur < mo.tStar := by
                rw [← ht_star, ← hP_recv]; omega
              have hrs_init : st.receiverState = fs.initReceiver k_fs :=
                (hs.hvR_target_lt hlt_tstar).2.2
              have hext_true : ext = true := by rw [hext_eq, hj, beq_self_eq_true]
              refine ⟨ht_star, hsJ, ?_, ?_⟩
              · dsimp only [s₁L]; rw [Function.update_self, hj, hkL, hrs_init]
              · dsimp only [s₁F]; rw [Function.update_self, hext_true]; rfl
            · right; left
              have hkL : kL = kF := h_ne_j hj
              have hext_false : ext = false := by
                rw [hext_eq, beq_eq_false_iff_ne]; exact hj
              refine ⟨fs.initReceiver kL, idx?, ?_, ?_, hj⟩
              · dsimp only [s₁L]; rw [Function.update_self]
              · dsimp only [s₁F]; rw [Function.update_self, hext_false, hkL]; rfl
          convert leComp_deliverTail cka prng fs Δcka qep mo j k_fs hauth P c r hs₁ hin ht_le s₁L s₁F
            (hs.hidL P) (hs.hidF P) rfl rfl rfl rfl
            (by dsimp only [s₁L]; omega)
            (by dsimp only [s₁F]; have := hs.htcur P; omega)
            rfl rfl
            (fun t' ht' => ⟨by dsimp only [s₁L]; rw [Function.update_of_ne ht'],
                            by dsimp only [s₁F]; rw [Function.update_of_ne ht']⟩)
            hvR_c using 1
          · dsimp only [deliverTail, s₁L]
            simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure]
            rfl
          · dsimp only [deliverTail, s₁F]
            simp only [StateT.run_bind, run_liftH, bind_assoc, simulateQ_bind]
            rfl
      · have heqF : c.1.1 ≠ (esF.g.st P).tcur + 1 := by rw [← hs.htcur P]; exact heq
        have ht_le_cur : c.1.1 ≤ (esL.g.st P).tcur := by omega
        have hvRecvL := vRecv_eq_vRecvTail_of_ne (hooksLocalFixed cka prng fs mo j k_fs)
          esL.g P (esL.g.st P) c (some r) hcondL heq
        have hvRecvF := vRecv_eq_vRecvTail_of_ne (hooksFS cka prng fs Δcka mo j)
          esF.g P (esF.g.st P) c (some r) hcondF heqF
        have hvR_c :
            ((esL.g.st P).vR c.1.1 = none ∧ (esF.g.st P).vR c.1.1 = none) ∨
            (∃ rs idx₀, (esL.g.st P).vR c.1.1 = some (rs, idx₀) ∧ (esF.g.st P).vR c.1.1 = some (some rs) ∧ idx₀ ≠ some j) ∨
            (c.1.1 = mo.tStar ∧ SenderIsJ mo j esL ∧
              (esL.g.st P).vR c.1.1 = some (st.receiverState, some j) ∧ (esF.g.st P).vR c.1.1 = some none) := by
          by_cases ht_star : c.1.1 = mo.tStar
          · right; right
            have hP_tstar : P = Party.receiverOf mo.tStar := ht_star ▸ hP_recv
            have hge : mo.tStar ≤ (esL.g.st (Party.receiverOf mo.tStar)).tcur := by
              rw [← hP_tstar, ← ht_star]; exact ht_le_cur
            obtain ⟨hsJ, h1, h2⟩ := hs.hvR_target_ge hge
            exact ⟨ht_star, hsJ, ht_star ▸ hP_tstar ▸ h1, ht_star ▸ hP_tstar ▸ h2⟩
          · rcases hs.hvR_other P c.1.1 (fun h => ht_star (congrArg Prod.snd h)) with h1 | h2
            · exact Or.inl h1
            · exact Or.inr (Or.inl h2)
        convert leComp_deliverTail cka prng fs Δcka qep mo j k_fs hauth P c r hs hin ht_le
          (esL.g.st P) (esF.g.st P) (hs.hidL P) (hs.hidF P) (hs.hγ P) (hs.hroot P) rfl rfl
          (by omega) (by have := hs.htcur P; omega) rfl rfl (fun _ _ => ⟨rfl, rfl⟩) hvR_c using 1
        · dsimp only [deliverTail]
          simp only [hvRecvL, StateT.run_bind]
          congr 2
        · dsimp only [deliverTail]
          simp only [hvRecvF, StateT.run_bind]
          congr 3

def injectTail {tspec : OracleSpec.{0, 0} ι} {Γv Sv SSv RSv HS : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (P : Party) (c : Header T × E) (s₁ : VP Γv T Sv SSv RSv)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    TComp tspec (Option (RecvResult M) × EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :=
  (do
    let s := es.g
    match ← liftH (vRecvTail hk s P s₁ c none) with
    | none =>
      abortE
      return none
    | some none => return some RecvResult.rejected
    | some (some (st', t', i', m')) =>
      if qep + 1 < t' then return some RecvResult.rejected
      let pos : Pos := ⟨P.other, t', i'⟩
      if s.trivial (2 + Δcka) pos then
        match ← commitE hk s P (s.st P) st' pos with
        | none => return none
        | some s₂ =>
          modify fun (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) =>
            { es with g := s₂ }
          return some (RecvResult.accepted t' i' (some m'))
      else
        if (mo.cfg (M := M)).injectFull t' then
          modify fun (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) =>
            { es with g := { es.g with win := true } }
        return some RecvResult.rejected).run es

omit [SampleableType KR] [SampleableType KC] in
theorem leComp_injectTail (j : ℕ) (k_fs : K) (hauth : mo.auth = true)
    (P : Party) (c : Header T × E)
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st)
    (hin : esL.g.inTransit P.other c = none)
    (hsends_f : P.sendsIn c.1.1 = false)
    (ht_le : c.1.1 ≤ (esL.g.st P).tcur + 1)
    (s₁L : PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ))
    (s₁F : VP Γ T Sig (Option SS) (Option RS))
    (hidL' : s₁L.id = P) (hidF' : s₁F.id = P)
    (hγ' : s₁L.γ = s₁F.γ) (hroot' : s₁L.root = s₁F.root)
    (hTcurL' : s₁L.curCkaMsg = (esL.g.st P).curCkaMsg) (hTcurF' : s₁F.curCkaMsg = (esF.g.st P).curCkaMsg)
    (htcurL' : s₁L.tcur = max (esL.g.st P).tcur c.1.1)
    (htcurF' : s₁F.tcur = max (esF.g.st P).tcur c.1.1)
    (hvSL' : s₁L.vS = (esL.g.st P).vS) (hvSF' : s₁F.vS = (esF.g.st P).vS)
    (hvR_other' : ∀ t', t' ≠ c.1.1 →
      s₁L.vR t' = (esL.g.st P).vR t' ∧ s₁F.vR t' = (esF.g.st P).vR t')
    (hvR_c :
      (s₁L.vR c.1.1 = none ∧ s₁F.vR c.1.1 = none) ∨
      (∃ rs idx?, s₁L.vR c.1.1 = some (rs, idx?) ∧ s₁F.vR c.1.1 = some (some rs) ∧ idx? ≠ some j) ∨
      (c.1.1 = mo.tStar ∧
        s₁L.vR c.1.1 = some (st.receiverState, some j) ∧ s₁F.vR c.1.1 = some none)) :
    LeComp (StepRelFS fs Δcka qep mo j k_fs)
      (simulateQ lImpl
        (injectTail Δcka qep mo (hooksLocalFixed cka prng fs mo j k_fs) P c s₁L esL))
      ((simulateQ (implFS fs)
        (injectTail Δcka qep mo (hooksFS cka prng fs Δcka mo j) P c s₁F esF)).run st) := by
  have hPother_s : P.other = Party.senderOf c.1.1 := by
    have hother_sends : P.other.sendsIn c.1.1 = true := by
      cases P <;> cases h : Nat.beq (c.1.1 % 2) 1 <;> simp_all [Party.other, Party.sendsIn]
    exact eq_senderOf_of_sendsIn hother_sends
  have hP_recv : P = Party.receiverOf c.1.1 := by
    unfold Party.receiverOf
    rw [← hPother_s]
    cases P <;> rfl
  have hvRL_upd : ∀ v, Function.update s₁L.vR c.1.1 v = Function.update (esL.g.st P).vR c.1.1 v := by
    intro v; funext t'
    by_cases ht' : t' = c.1.1
    · subst t'; simp
    · simp [Function.update_of_ne ht', (hvR_other' t' ht').1]
  have hvRF_upd : ∀ v, Function.update s₁F.vR c.1.1 v = Function.update (esF.g.st P).vR c.1.1 v := by
    intro v; funext t'
    by_cases ht' : t' = c.1.1
    · subst t'; simp
    · simp [Function.update_of_ne ht', (hvR_other' t' ht').2]
  rcases hvR_c with ⟨hnoneL, hnoneF⟩ | ⟨rs, idx?, hsomeL, hsomeF, hidx_ne⟩ |
      ⟨ht_star, hsomeL, hsomeF⟩
  ·
    dsimp only [injectTail, vRecvTail]
    simp only [StateT.run_bind, StateT.run_pure, pure_bind, run_liftH,
      hnoneL, hnoneF, simulateQ_pure]
    exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
  ·
    dsimp only [injectTail, vRecvTail, hooksLocalFixed, hooksFS]
    simp only [StateT.run_bind, StateT.run_pure, pure_bind, run_liftH, hsomeL, hsomeF]
    cases hrcv : fs.receive rs c.1 c.2 with
    | none =>
      simp only [hrcv, Option.map_none, StateT.run_pure, pure_bind, simulateQ_pure]
      exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
    | some val =>
      rcases val with ⟨rs', i', m'⟩
      have hs_book : SyncLFS fs Δcka qep mo j k_fs
          { esL with h := { esL.h with lastIdx := idx? } } esF st :=
        syncLFS_with_book fs Δcka qep mo j k_fs hs { esL.h with lastIdx := idx? } esF.h
          hs.hbs rfl (fun _ _ => rfl) rfl rfl rfl rfl
      by_cases hqep : qep + 1 < c.1.1
      · simp only [hrcv, Option.map_some, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, hqep, ↓reduceIte, simulateQ_pure]
        exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs_book⟩))
      · have htriv_eq : esF.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ =
            esL.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ := by
          unfold GameState.trivial
          rw [← hs.hcomp, ← hs.htrans, ← hs.htL]
        by_cases htriv : esL.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
        · have htrivF : esF.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true := htriv_eq.trans htriv
          dsimp only [commitE, hooksLocalFixed, hooksFS]
          simp only [hrcv, Option.map_some, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, run_liftH, accept_update_self, hqep, ↓reduceIte, htriv, htrivF, simulateQ_pure]
          by_cases ht_star : c.1.1 = mo.tStar
          · refine LeComp.pure (Or.inl (Or.inr ⟨hs.habortL, hs.hwinL, ?_, ?_⟩))
            · intro Q
              simp only [GameState.accept, GameState.delete]
              by_cases hQ : Q = P
              · subst Q; rw [Function.update_self]; exact hidL'
              · rw [Function.update_of_ne hQ]; exact hs.hidL Q
            · dsimp only [RWrongSession]
              have hP_tstar : P = Party.receiverOf mo.tStar := ht_star ▸ hP_recv
              simp only [GameState.accept, GameState.delete, ← hP_tstar, Function.update_self,
                htcurL', ht_star, Nat.le_max_right, true_and]
              intro rs₀ hrs₀
              injection hrs₀ with hpair
              injection hpair with _ hidx_eq
              exact hidx_ne hidx_eq
          · refine LeComp.pure (Or.inr (Or.inr ⟨rfl, ?_⟩))
            exact syncLFS_accept_local fs Δcka qep mo j k_fs P c.1.1 i' rs' idx? hs
              hsends_f ht_le ht_star hidx_ne
              { s₁L with vR := Function.update s₁L.vR c.1.1 (some (rs', idx?)) }
              { s₁F with vR := Function.update s₁F.vR c.1.1 (some (some rs')) }
              hidL' hidF' hγ' hroot' hTcurL' hTcurF'
              htcurL' htcurF' hvSL' hvSF'
              (hvRL_upd _) (hvRF_upd _)
        · have htrivL_f : esL.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = false :=
            Bool.eq_false_iff.mpr htriv
          have htrivF_f : esF.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = false :=
            htriv_eq.trans htrivL_f
          by_cases hinjFull : (mo.cfg (M := M)).injectFull c.1.1 = true
          · simp only [hrcv, Option.map_some, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, hqep, ↓reduceIte, htrivL_f, htrivF_f, Bool.false_eq_true, hinjFull,
              simulateQ_pure]
            exact LeComp.pure (Or.inl (LHSDead.of_win_ne Δcka mo j rfl hidx_ne))
          · have hinjFull_f : (mo.cfg (M := M)).injectFull c.1.1 = false :=
              Bool.eq_false_iff.mpr hinjFull
            simp only [hrcv, Option.map_some, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, hqep, ↓reduceIte, htrivL_f, htrivF_f, Bool.false_eq_true, hinjFull_f,
              simulateQ_pure]
            exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs_book⟩))
  ·
    have hfind_tr :
        st.inTransit.find? (fun r' => r'.ad == c.1 && r'.ct == c.2) = none := by
      by_cases hsJ : SenderIsJ mo j esL
      · rw [hs.hsenderJ_trans hsJ,
          find?_map_filter esL.g.trans P.other mo.tStar c ht_star
            (fun r' hr' => ⟨(hs.htrans_wf r' hr').1, fun he => by
              rw [(hs.htrans_wf r' hr').2.1, he, ← ht_star, hPother_s]⟩)]
        have hin' : esL.g.trans.find? (fun r' => r'.pos.sender == P.other && decide (r'.ct = c)) = none := hin
        rw [hin', Option.map_none]
      · rw [(hs.hnot_senderJ hsJ).2.2.2]
        rfl
    have hany_tr : st.inTransit.any (fun r' => r'.ad == c.1 && r'.ct == c.2) = false := by
      rw [Bool.eq_false_iff]
      intro hany
      rw [List.any_eq_true] at hany
      obtain ⟨x, hx, hpx⟩ := hany
      exact List.find?_eq_none.mp hfind_tr x hx hpx
    have hmatched : esF.h.fsTrans.find? (fun x => x.2 == c) = none := by
      rw [hs.hfsTrans, find?_map_eq, hfind_tr, Option.map_none]
    dsimp only [injectTail, vRecvTail, commitE, hooksLocalFixed, hooksFS]
    simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
      run_liftH, hsomeL, hsomeF, hs.hextF, hmatched, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte, bind_assoc, simulateQ_bind, simulateQ_pure,
      simulateQ_implFS_injectQuery,
      fs_inject_of_ended_false fs st c hs.hendedFS hany_tr]
    cases hrcv : fs.receive st.receiverState c.1 c.2 with
    | none =>
      simp only [hrcv, StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, pure_bind]
      exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
    | some val =>
      rcases val with ⟨rs', i', m'⟩
      simp only [hrcv, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        simulateQ_bind, simulateQ_pure,
        pure_bind, Option.map_none, Option.getD_none, run_liftH, accept_update_self]
      by_cases hcomp_i : st.isCompromised i' = true
      ·
        have hforged : (!st.isCompromised i') = false := by rw [hcomp_i]; rfl
        have hwin_f : (st.win || !st.isCompromised i') = false := by
          rw [hs.hwinFS, hforged]; rfl
        have hcorr_ex : ∃ corrAt, st.senderCorruptedAt = some corrAt ∧ corrAt < i' := by
          unfold FSAEAD.State.isCompromised at hcomp_i
          cases hsc : st.senderCorruptedAt with
          | none => simp [hsc] at hcomp_i
          | some corrAt =>
            simp only [hsc, decide_eq_true_eq] at hcomp_i
            exact ⟨corrAt, rfl, hcomp_i⟩
        obtain ⟨corrAt, hcorr_at, hcorr_lt⟩ := hcorr_ex
        obtain ⟨hsJ, hqep_le, hheal, hcomp_mem⟩ := hs.hcorr_sync corrAt hcorr_at
        have hqep_f : ¬ (qep + 1 < c.1.1) := by omega
        have htrivL : esL.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true := by
          unfold GameState.trivial
          by_cases hany_tr' : esL.g.trans.any (fun r => r.pos == ⟨P.other, c.1.1, i'⟩) = true
          · rw [List.any_eq_true] at hany_tr'
            obtain ⟨r_tr, hr_tr, hpos_tr⟩ := hany_tr'
            rw [beq_iff_eq] at hpos_tr
            have hmem_comp : (⟨P.other, c.1.1, i'⟩ : Pos) ∈ esL.g.comp := by
              rw [← hpos_tr]
              exact hcomp_mem r_tr hr_tr (by rw [hpos_tr, ht_star]) (by rw [hpos_tr]; exact hcorr_lt)
            have hcont : esL.g.comp.contains ⟨P.other, c.1.1, i'⟩ = true :=
              List.contains_iff_mem.mpr hmem_comp
            rw [hcont, Bool.true_or]
          · have hany_f : esL.g.trans.any (fun r => r.pos == ⟨P.other, c.1.1, i'⟩) = false :=
              Bool.eq_false_iff.mpr hany_tr'
            rw [hany_f, ht_star, hheal]
            cases esL.g.comp.contains ⟨P.other, mo.tStar, i'⟩ <;> rfl
        have htrivF : esF.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true := by
          unfold GameState.trivial
          rw [← hs.hcomp, ← hs.htrans, ← hs.htL]
          exact htrivL
        simp only [hqep_f, ↓reduceIte, htrivL, htrivF, StateT.run_bind, StateT.run_modify,
          StateT.run_pure, pure_bind, run_liftH, accept_update_self, simulateQ_pure]
        refine LeComp.pure (Or.inr (Or.inr ⟨rfl, ?_⟩))
        rw [ht_star, hwin_f]
        exact syncLFS_accept_ext fs Δcka qep mo j k_fs P i' i' rs' hs
          (ht_star ▸ hP_recv) hsJ
          { s₁L with vR := Function.update s₁L.vR mo.tStar (some (rs', some j)) }
          { s₁F with vR := Function.update s₁F.vR mo.tStar (some none) }
          hidL' hidF' hγ' hroot' hTcurL' hTcurF'
          (ht_star ▸ htcurL') (ht_star ▸ htcurF') hvSL' hvSF'
          (ht_star ▸ hvRL_upd _) (ht_star ▸ hvRF_upd _)
      ·
        have hcomp_f : st.isCompromised i' = false := Bool.eq_false_iff.mpr hcomp_i
        have hwin_t : (st.win || !st.isCompromised i') = true := by
          rw [hcomp_f]; simp
        by_cases hqep : qep + 1 < c.1.1
        · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure]
          exact LeComp.pure (Or.inr (Or.inl (by simp [FSAEAD.State.removeFromTransit, hwin_t])))
        · by_cases htrivL : esL.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
          · have htrivF : esF.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true := by
              unfold GameState.trivial
              rw [← hs.hcomp, ← hs.htrans, ← hs.htL]
              exact htrivL
            simp only [hqep, ↓reduceIte, htrivL, htrivF, StateT.run_bind, StateT.run_modify,
              StateT.run_pure, pure_bind, run_liftH, accept_update_self, simulateQ_pure]
            exact LeComp.pure (Or.inr (Or.inl (by simp [FSAEAD.State.removeFromTransit, hwin_t])))
          · have htrivL_f : esL.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = false :=
              Bool.eq_false_iff.mpr htrivL
            have htrivF_f : esF.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = false := by
              unfold GameState.trivial
              rw [← hs.hcomp, ← hs.htrans, ← hs.htL]
              exact htrivL_f
            by_cases hinjFull : (mo.cfg (M := M)).injectFull c.1.1 = true
            · simp only [hqep, ↓reduceIte, htrivL_f, htrivF_f, Bool.false_eq_true, hinjFull,
                StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure]
              exact LeComp.pure (Or.inr (Or.inl (by simp [FSAEAD.State.removeFromTransit, hwin_t])))
            · have hinjFull_f : (mo.cfg (M := M)).injectFull c.1.1 = false :=
                Bool.eq_false_iff.mpr hinjFull
              simp only [hqep, ↓reduceIte, htrivL_f, htrivF_f, Bool.false_eq_true, hinjFull_f,
                StateT.run_pure, simulateQ_pure]
              exact LeComp.pure (Or.inr (Or.inl (by simp [FSAEAD.State.removeFromTransit, hwin_t])))

set_option maxHeartbeats 400000 in
theorem leComp_injectE (j : ℕ) (k_fs : K) (hauth : mo.auth = true)
    (q : Party × (Header T × E))
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st) :
    LeComp (StepRelFS fs Δcka qep mo j k_fs)
      (simulateQ lImpl
        ((injectE (hooksLocalFixed cka prng fs mo j k_fs) (2 + Δcka) qep mo.cfg q).run esL))
      ((simulateQ (implFS fs)
        ((injectE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.cfg q).run esF)).run st) := by
  rcases q with ⟨P, c⟩
  unfold injectE
  rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, StateT.run_get, pure_bind]
  simp only [hs.habortL, hs.habortF, hs.hwinL, hs.hwinF, Bool.false_or]
  have hin_eq : esF.g.inTransit P.other c = esL.g.inTransit P.other c := by
    simp only [GameState.inTransit, hs.htrans]
  have hsafe_eq : esF.g.safeInj (2 + Δcka) = esL.g.safeInj (2 + Δcka) := by
    simp only [GameState.safeInj, hs.htL, hs.hepoch]
  rw [hin_eq, hsafe_eq]
  cases hin : esL.g.inTransit P.other c with
  | some r =>
    simp only [Option.isSome_some, Bool.true_or, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
  | none =>
    simp only [Option.isSome_none, Bool.false_or]
    by_cases hsafe : esL.g.safeInj (2 + Δcka) = true
    · simp only [hsafe, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hcond_eq :
          ((esF.g.st P).id.sendsIn c.1.1 || decide ((esF.g.st P).tcur + 1 < c.1.1)) =
            ((esL.g.st P).id.sendsIn c.1.1 || decide ((esL.g.st P).tcur + 1 < c.1.1)) := by
        rw [hs.hidF P, hs.hidL P, ← hs.htcur P]
      by_cases hcondL : ((esL.g.st P).id.sendsIn c.1.1 || decide ((esL.g.st P).tcur + 1 < c.1.1)) = true
      · have hcondF : ((esF.g.st P).id.sendsIn c.1.1 || decide ((esF.g.st P).tcur + 1 < c.1.1)) = true :=
          hcond_eq.trans hcondL
        dsimp only [vRecv]
        simp only [hcondL, hcondF, ↓reduceIte, StateT.run_bind, run_liftH, StateT.run_pure, pure_bind, simulateQ_pure]
        exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
      · have hcondL_f : ((esL.g.st P).id.sendsIn c.1.1 || decide ((esL.g.st P).tcur + 1 < c.1.1)) = false :=
          Bool.eq_false_iff.mpr hcondL
        have hcondF_f : ((esF.g.st P).id.sendsIn c.1.1 || decide ((esF.g.st P).tcur + 1 < c.1.1)) = false :=
          hcond_eq.trans hcondL_f
        have hsends_f : P.sendsIn c.1.1 = false := by
          have h := hcondL_f
          rw [hs.hidL P, Bool.or_eq_false_iff] at h
          exact h.1
        have ht_le : c.1.1 ≤ (esL.g.st P).tcur + 1 := by
          have h := hcondL_f
          rw [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
          omega
        have hPother_s : P.other = Party.senderOf c.1.1 := by
          have hother_sends : P.other.sendsIn c.1.1 = true := by
            cases P <;> cases h : Nat.beq (c.1.1 % 2) 1 <;> simp_all [Party.other, Party.sendsIn]
          exact eq_senderOf_of_sendsIn hother_sends
        have hP_recv : P = Party.receiverOf c.1.1 := by
          unfold Party.receiverOf
          rw [← hPother_s]
          cases P <;> rfl
        by_cases heq : c.1.1 = (esL.g.st P).tcur + 1
        · have heqF : c.1.1 = (esF.g.st P).tcur + 1 := by rw [← hs.htcur P]; exact heq
          cases hTn : c.1.2 with
          | none =>
            have hvL : vRecv (hooksLocalFixed cka prng fs mo j k_fs) esL.g P (esL.g.st P) c none = pure (some none) := by
              simp [vRecv, hcondL_f, heq, hTn]
            have hvF : vRecv (hooksFS cka prng fs Δcka mo j) esF.g P (esF.g.st P) c none = pure (some none) := by
              simp [vRecv, hcondF_f, heqF, hTn]
            simp only [hvL, hvF, run_liftH, StateT.run_bind, StateT.run_pure, pure_bind, simulateQ_pure]
            exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
          | some Tc =>
            have hvRecvL := vRecv_eq_bind_vRecvTail_of_eq (hooksLocalFixed cka prng fs mo j k_fs)
              esL.g P (esL.g.st P) c none Tc hcondL_f heq hTn
            have hvRecvF := vRecv_eq_bind_vRecvTail_of_eq (hooksFS cka prng fs Δcka mo j)
              esF.g P (esF.g.st P) c none Tc hcondF_f heqF hTn
            simp only [hvRecvL, hvRecvF, run_liftH, StateT.run_bind, bind_assoc, simulateQ_bind]
            rw [← hs.hγ P, ← hs.hroot P]
            refine LeComp.bind (leComp_startRecv cka prng fs Δcka mo j k_fs esL.g esF.g P c.1.1
              (esL.g.st P).γ (esL.g.st P).root Tc hs.hbs st) ?_
            intro rL rF ⟨hr_st, hr_cL, hr_cF, hr_tr, hr_cnt, hr_sc, hr_ex, hr_bs, hcases⟩
            rw [hr_st]
            rcases hcases with ⟨hL_none, hF_none⟩ | ⟨hL_snone, hF_snone, hr_sess⟩ |
              ⟨σ', kL, kF, idx?, ext, hL_some, hF_some, hext_eq, h_eq_j, h_ne_j, h_ne_t, h_origin⟩
            · simp only [hL_none, hF_none, StateT.run_pure, pure_bind, abortE,
                StateT.run_modify, simulateQ_pure]
              exact LeComp.pure (Or.inl (lhsDead_of_abort Δcka mo j _))
            · simp only [hL_snone, hF_snone, StateT.run_pure, pure_bind, simulateQ_pure]
              exact LeComp.pure (Or.inr (Or.inr ⟨rfl,
                syncLFS_with_book fs Δcka qep mo j k_fs hs rL.2 rF.1.2 hr_bs hr_cL
                  (fun _ _ => hr_sess) hr_ex hr_cnt hr_tr hr_sc⟩))
            · simp only [hL_some, hF_some]
              have hs₁ : SyncLFS fs Δcka qep mo j k_fs
                  { esL with h := rL.2 } { esF with h := rF.1.2 } st := by
                refine syncLFS_with_book fs Δcka qep mo j k_fs hs rL.2 rF.1.2 hr_bs
                  hr_cL ?_ hr_ex hr_cnt hr_tr hr_sc
                intro h1 h2
                rcases h_origin with ⟨_, _, _, hsess⟩ | ⟨_, hnot, _, _⟩
                · exact hsess
                · exact absurd ⟨h1, h2⟩ hnot
              let s₁L : PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ) :=
                { esL.g.st P with tcur := c.1.1, γ := (cka.receive (esL.g.st P).γ Tc).1, root := σ',
                                  vR := Function.update (esL.g.st P).vR c.1.1 (some (fs.initReceiver kL, idx?)) }
              let s₁F : VP Γ T Sig (Option SS) (Option RS) :=
                { esF.g.st P with tcur := c.1.1, γ := (cka.receive (esL.g.st P).γ Tc).1, root := σ',
                                  vR := Function.update (esF.g.st P).vR c.1.1
                                    (some (if ext then none else some (fs.initReceiver kF))) }
              have hvR_c :
                  (s₁L.vR c.1.1 = none ∧ s₁F.vR c.1.1 = none) ∨
                  (∃ rs idx₀, s₁L.vR c.1.1 = some (rs, idx₀) ∧ s₁F.vR c.1.1 = some (some rs) ∧ idx₀ ≠ some j) ∨
                  (c.1.1 = mo.tStar ∧
                    s₁L.vR c.1.1 = some (st.receiverState, some j) ∧ s₁F.vR c.1.1 = some none) := by
                by_cases hj : idx? = some j
                · obtain ⟨hkL, ht_star⟩ := h_eq_j hj
                  right; right
                  have hlt_tstar : (esL.g.st (Party.receiverOf mo.tStar)).tcur < mo.tStar := by
                    rw [← ht_star, ← hP_recv]; omega
                  have hrs_init : st.receiverState = fs.initReceiver k_fs :=
                    (hs.hvR_target_lt hlt_tstar).2.2
                  have hext_true : ext = true := by rw [hext_eq, hj, beq_self_eq_true]
                  refine ⟨ht_star, ?_, ?_⟩
                  · dsimp only [s₁L]; rw [Function.update_self, hj, hkL, hrs_init]
                  · dsimp only [s₁F]; rw [Function.update_self, hext_true]; rfl
                · right; left
                  have hkL : kL = kF := h_ne_j hj
                  have hext_false : ext = false := by
                    rw [hext_eq, beq_eq_false_iff_ne]; exact hj
                  refine ⟨fs.initReceiver kL, idx?, ?_, ?_, hj⟩
                  · dsimp only [s₁L]; rw [Function.update_self]
                  · dsimp only [s₁F]; rw [Function.update_self, hext_false, hkL]; rfl
              convert leComp_injectTail cka prng fs Δcka qep mo j k_fs hauth P c hs₁ hin hsends_f ht_le
                s₁L s₁F (hs.hidL P) (hs.hidF P) rfl rfl rfl rfl
                (by dsimp only [s₁L]; omega)
                (by dsimp only [s₁F]; have := hs.htcur P; omega)
                rfl rfl
                (fun t' ht' => ⟨by dsimp only [s₁L]; rw [Function.update_of_ne ht'],
                                by dsimp only [s₁F]; rw [Function.update_of_ne ht']⟩)
                hvR_c using 1
              · dsimp only [injectTail, s₁L]
                simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure]
                congr 1
              · dsimp only [injectTail, s₁F]
                simp only [StateT.run_bind, run_liftH, bind_assoc, simulateQ_bind]
                congr 1
        · have heqF : c.1.1 ≠ (esF.g.st P).tcur + 1 := by rw [← hs.htcur P]; exact heq
          have ht_le_cur : c.1.1 ≤ (esL.g.st P).tcur := by omega
          have hvRecvL := vRecv_eq_vRecvTail_of_ne (hooksLocalFixed cka prng fs mo j k_fs)
            esL.g P (esL.g.st P) c none hcondL_f heq
          have hvRecvF := vRecv_eq_vRecvTail_of_ne (hooksFS cka prng fs Δcka mo j)
            esF.g P (esF.g.st P) c none hcondF_f heqF
          have hvR_c :
              ((esL.g.st P).vR c.1.1 = none ∧ (esF.g.st P).vR c.1.1 = none) ∨
              (∃ rs idx₀, (esL.g.st P).vR c.1.1 = some (rs, idx₀) ∧ (esF.g.st P).vR c.1.1 = some (some rs) ∧ idx₀ ≠ some j) ∨
              (c.1.1 = mo.tStar ∧
                (esL.g.st P).vR c.1.1 = some (st.receiverState, some j) ∧ (esF.g.st P).vR c.1.1 = some none) := by
            by_cases ht_star : c.1.1 = mo.tStar
            · right; right
              have hP_tstar : P = Party.receiverOf mo.tStar := ht_star ▸ hP_recv
              have hge : mo.tStar ≤ (esL.g.st (Party.receiverOf mo.tStar)).tcur := by
                rw [← hP_tstar, ← ht_star]; exact ht_le_cur
              obtain ⟨_, h1, h2⟩ := hs.hvR_target_ge hge
              exact ⟨ht_star, ht_star ▸ hP_tstar ▸ h1, ht_star ▸ hP_tstar ▸ h2⟩
            · rcases hs.hvR_other P c.1.1 (fun h => ht_star (congrArg Prod.snd h)) with h1 | h2
              · exact Or.inl h1
              · exact Or.inr (Or.inl h2)
          convert leComp_injectTail cka prng fs Δcka qep mo j k_fs hauth P c hs hin hsends_f ht_le
            (esL.g.st P) (esF.g.st P) (hs.hidL P) (hs.hidF P) (hs.hγ P) (hs.hroot P) rfl rfl
            (by omega) (by have := hs.htcur P; omega) rfl rfl (fun _ _ => ⟨rfl, rfl⟩) hvR_c using 1
          · dsimp only [injectTail]
            simp only [hvRecvL, StateT.run_bind]
            congr 2
          · dsimp only [injectTail]
            simp only [hvRecvF, StateT.run_bind]
            congr 3
    · have hsafe_f : esL.g.safeInj (2 + Δcka) = false := Bool.eq_false_iff.mpr hsafe
      simp only [hsafe_f, Bool.not_false, ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))

theorem leComp_stepLFixed_stepF (j : ℕ) (k_fs : K)
    (hauth : mo.auth = true)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st) :
    LeComp (StepRelFS fs Δcka qep mo j k_fs)
      (stepLFixed cka prng fs Δcka qep mo j k_fs q esL)
      (stepF cka prng fs Δcka qep mo j q esF st) := by
  rcases q with n | ((((q1 | q2) | q3) | q4) | P)
  · rw [stepLFixed_coinsE, stepF_coinsE]
    simp only [map_eq_bind_pure_comp, Function.comp_def]
    refine LeComp.sample_bind (query (spec := unifSpec) n) fun x _ => ?_
    exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
  · unfold stepLFixed stepF implE; dsimp only [QueryImpl.add_apply]
    exact leComp_transmitE cka prng fs Δcka qep mo j k_fs q1 hs
  · unfold stepLFixed stepF implE; dsimp only [QueryImpl.add_apply]
    exact leComp_challE cka prng fs Δcka qep mo j k_fs hauth q2 hs
  · unfold stepLFixed stepF implE; dsimp only [QueryImpl.add_apply]
    exact leComp_deliverE cka prng fs Δcka qep mo j k_fs hauth q3 hs
  · unfold stepLFixed stepF implE; dsimp only [QueryImpl.add_apply]
    exact leComp_injectE cka prng fs Δcka qep mo j k_fs hauth q4 hs
  · unfold stepLFixed stepF implE; dsimp only [QueryImpl.add_apply]
    exact leComp_corrE cka prng fs Δcka qep mo j k_fs hauth hvg P hs

theorem runLocAtFixed_le_runF (j : ℕ) (k_fs : K)
    (hauth : mo.auth = true)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    (oa : SMComp Γ T Sig SS RS M CCoins E Bool)
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st) :
    𝒟[runLocAtFixed cka prng fs Δcka qep mo j k_fs oa esL] {true} ≤
      𝒟[runF cka prng fs Δcka qep mo j oa esF st] {true} := by
  induction oa using OracleComp.inductionOn generalizing esL esF st with
  | pure b' =>
    have hwinL := hs.hwinL
    have hout : (authOut (2 + Δcka) mo.policy esL && (esL.h.lastIdx == some j)) = false := by
      simp [authOut, hwinL]
    simp only [runLocAtFixed, simulateQ_pure, StateT.run_pure, pure_bind, hout]
    have hzero : 𝒟[(pure false : ProbComp Bool)] {true} = 0 := by simp
    rw [hzero]
    exact zero_le
  | query_bind q k ih =>
    rw [runLocAtFixed_query_bind, runF_query_bind]
    refine leComp_stepLFixed_stepF cka prng fs Δcka qep mo j k_fs hauth hvg q hs
      (fun rL => runLocAtFixed cka prng fs Δcka qep mo j k_fs (k rL.1) rL.2)
      (fun rF => runF cka prng fs Δcka qep mo j (k rF.1.1) rF.1.2 rF.2) ?_
    intro rL rF hrel
    rcases hrel with hdead | hwin | ⟨heq_ans, hs'⟩
    · rw [evalDist_runLocAtFixed_eq_zero_of_dead cka prng fs Δcka qep mo hauth j k_fs (k rL.1) rL.2 hdead]
      exact zero_le
    · rw [evalDist_runF_eq_one_of_win cka prng fs Δcka qep mo j (k rF.1.1) rF.1.2 rF.2 hwin]
      exact prob_le_one
    · rw [heq_ans]
      exact ih rF.1.1 hs'

/-! ### Proof of `lemma11` -/

theorem localAuthAtFixed_le_runFS (j : ℕ) (k_fs : K) (b_fs : Bool) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[localAuthAtFixed cka prng fs lam Δcka qep j k_fs tL t A] {true} ≤
      𝒟[(simulateQ (implFS fs) (runFS cka prng fs lam Δcka qep ⟨true, tL, t⟩ j false A)).run
          (FSAEAD.initState fs k_fs b_fs) >>= fun z => pure z.2.win] {true} := by
  by_cases hvg : lastLeakGuessAdmissible (2 + Δcka) tL t = true
  · unfold localAuthAtFixed runFS engRun
    simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
    refine leComp_init cka prng fs lam Δcka qep ⟨true, tL, t⟩ j k_fs b_fs _ _ ?_
    intro rL rF ⟨vAL, vBL, vAF, vBF, hrL1, hrF1, hrel⟩
    rcases rL with ⟨vsL, hL⟩
    rcases rF with ⟨⟨vsF, hF⟩, stF⟩
    dsimp only at hrL1 hrF1 ⊢
    subst hrL1 hrF1
    dsimp only at hrel ⊢
    rcases hrel with hdead | hs
    · rw [evalDist_runLocAtFixed_eq_zero_of_dead cka prng fs Δcka qep ⟨true, tL, t⟩ rfl j k_fs A _ hdead]
      exact zero_le
    · refine le_trans (runLocAtFixed_le_runF cka prng fs Δcka qep ⟨true, tL, t⟩ j k_fs rfl hvg A hs) ?_
      refine le_of_eq (congrArg (fun p => 𝒟[p] {true}) ?_)
      simp only [runF, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc,
        pure_bind, map_eq_bind_pure_comp, Function.comp_def]
      rfl
  · have hvg_f : lastLeakGuessAdmissible (2 + Δcka) tL t = false := Bool.eq_false_iff.mpr hvg
    have hzero : 𝒟[localAuthAtFixed cka prng fs lam Δcka qep j k_fs tL t A] {true} = 0 := by
      unfold localAuthAtFixed
      refine evalDist_bind_eq_zero _ _ fun r hr => ?_
      rcases r with ⟨vs, h⟩
      cases vs with
      | none => simp
      | some vp =>
        rcases vp with ⟨vA, vB⟩
        exact evalDist_runLocAtFixed_eq_zero_of_not_validGuess cka prng fs Δcka qep ⟨true, tL, t⟩ j k_fs hvg_f A _
    rw [hzero]
    exact zero_le

theorem localAuthAt_le_fsWin (j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[localAuthAt cka prng fs lam Δcka qep j tL t A] {true} ≤
      FSAEAD.advantage fs (redFSAuth cka prng fs lam Δcka qep j tL t A) := by
  rw [redFSAuth, advantage_bind_sampleT_bool]
  refine le_trans (localAuthAt_le_localAuthAtFixed cka prng fs lam Δcka qep j tL t A) ?_
  unfold fsWin
  rw [← OracleComp.evalDist_bind_const ($ᵗ Bool)
        (($ᵗ K : ProbComp K) >>= fun k_fs => localAuthAtFixed cka prng fs lam Δcka qep j k_fs tL t A)]
  refine evalDist_bind_mono ($ᵗ Bool) _ _ fun b_fs _ => ?_
  refine evalDist_bind_mono ($ᵗ K) _ _ fun k_fs _ => ?_
  exact localAuthAtFixed_le_runFS cka prng fs lam Δcka qep j k_fs b_fs tL t A

theorem lemma11_proof (tL : Option ℕ) (t q : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (hq : MakesAtMostQueries A q) :
    𝒟[PRFPRNG.branch prng true (redPRNGAuth cka prng fs lam Δcka qep tL t A)] {true} ≤
      ∑ j ∈ Finset.range q, FSAEAD.advantage fs (redFSAuth cka prng fs lam Δcka qep j tL t A) := by
  refine le_trans (branch_redPRNGAuth_le_localAuth cka prng fs lam Δcka qep tL t A) ?_
  refine le_trans (localAuth_le_sum_localAuthAt cka prng fs lam Δcka qep tL t q A hq) ?_
  exact Finset.sum_le_sum fun j _ => localAuthAt_le_fsWin cka prng fs lam Δcka qep j tL t A

end HalfB

end CryptoGames.SM.Construction.AuthL11
