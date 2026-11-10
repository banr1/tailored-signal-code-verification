/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedFS
import ProofLib.SepLogic.WP.StateNorm

/-!
# Shifted-Paper Lemma 11 at `Δ = 2`, Part 1

First half of `lemma11_df_shifted_dir2_paper`: couples `redPRNGAuthDFShiftedDir2Paper` (`b = true`)
with `localAuthDFShiftedDir2Paper`, indexes sessions over `j < q`, and sets up the fixed-key game.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory CryptoGames.Lazy

namespace CryptoGames.SM.Construction.DeliverForge

open CryptoGames.SM.Construction
open Engine
open SM

section AuthL11ShiftedDir2Paper

open AuthL11

variable {ι : Type} {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

abbrev moAuth (mo : Mode) : Mode := ⟨true, mo.tL, mo.tStar⟩

@[simp] theorem eraseSt_trivB1_l11 {St₁ St₂ Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    {g₁ : SM.GameState St₁ Msg C} {g₂ : SM.GameState St₂ Msg C}
    (h : eraseSt g₁ = eraseSt g₂) (tStar : ℕ) (pos : SM.Pos) :
    trivB1 tStar g₁ pos = trivB1 tStar g₂ pos := by
  simp [trivB1, eraseSt_trivial h, eraseSt_epoch h]

abbrev implEDFShiftedB1 {tspec : OracleSpec.{0, 0} ι} {HS Γv Sv SSv RSv : Type}
    (l : ℕ) (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip tStar : ℕ) (cfg : SM.Config M) (π : Policy) :
    QueryImpl (unifSpec + DeliverForge.specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (EM tspec Γv T Sv SSv RSv M E HS) :=
  let i₀ : QueryImpl unifSpec (EM tspec Γv T Sv SSv RSv M E HS) := coinsE
  let i₁ : QueryImpl (SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (EM tspec Γv T Sv SSv RSv M E HS) :=
    HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (transmitE hk Δ qep π) (challE hk Δ qep cfg π))
      (deliverE hk maxSkip cfg)) (injectEB1 hk qep tStar cfg)) (corrEShiftedPaper l hk π)
  let i₂ : QueryImpl ((Party × (Header T × E) × (Header T × E)) →ₒ Option (SM.RecvResult M))
      (EM tspec Γv T Sv SSv RSv M E HS) := deliverForgeEB1 hk qep tStar cfg
  HAdd.hAdd i₀ (HAdd.hAdd i₁ i₂)

def stepPDFShiftedDir2Paper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    ProbComp (((SMSpecDF Γ T Sig SS RS M CCoins E).Range q × EStateP Γ T Sig SS RS M E K) ×
      PRFPRNG.GameState Sig I K) :=
  (simulateQ (pImpl prng)
    ((implEDFShiftedB1 l (hooksPRNG cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.tStar
      (moAuth mo).cfg (moAuth mo).policy q).run esP)).run sp

def stepLDFShiftedDir2Paper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    ProbComp ((SMSpecDF Γ T Sig SS RS M CCoins E).Range q × EStateL Γ T Sig SS RS M E K I) :=
  simulateQ lImpl
    ((implEDFShiftedB1 l (hooksLocal cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.tStar
      (moAuth mo).cfg (moAuth mo).policy q).run esL)

def runPDFShiftedDir2Paper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) : ProbComp Bool := do
  let r ← (simulateQ (pImpl prng)
    ((simulateQ (implEDFShiftedB1 l (hooksPRNG cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.tStar
      (moAuth mo).cfg (moAuth mo).policy) oa).run esP)).run sp
  pure (authOut (2 + Δcka) (moAuth mo).policy r.1.2)

def runLocDFShiftedDir2Paper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) : ProbComp Bool := do
  let r ← simulateQ lImpl
    ((simulateQ (implEDFShiftedB1 l (hooksLocal cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.tStar
      (moAuth mo).cfg (moAuth mo).policy) oa).run esL)
  pure (authOut (2 + Δcka) (moAuth mo).policy r.2)

def runLocAtDFShiftedDir2Paper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode) (j : ℕ)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) : ProbComp Bool := do
  let r ← simulateQ lImpl
    ((simulateQ (implEDFShiftedB1 l (hooksLocal cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.tStar
      (moAuth mo).cfg (moAuth mo).policy) oa).run esL)
  pure (authOut (2 + Δcka) (moAuth mo).policy r.2 && (r.2.h.lastIdx == some j))

def localAuthDFShiftedDir2Paper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep l : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) : ProbComp Bool := do
  let mo : Mode := ⟨false, tL, t⟩
  let (vs, h) ← simulateQ lImpl ((initLocal cka prng fs lam mo).run {})
  match vs with
  | none => return false
  | some (vA, vB) =>
    let g : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := false }
    runLocDFShiftedDir2Paper cka prng fs Δcka qep l mo A { g, h }

def localAuthAtDFShiftedDir2Paper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep j l : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) : ProbComp Bool := do
  let mo : Mode := ⟨false, tL, t⟩
  let (vs, h) ← simulateQ lImpl ((initLocal cka prng fs lam mo).run {})
  match vs with
  | none => return false
  | some (vA, vB) =>
    let g : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := false }
    runLocAtDFShiftedDir2Paper cka prng fs Δcka qep l mo j A { g, h }

def stepLFixedDFShiftedDir2Paper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode) (j : ℕ) (k_fs : K)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    ProbComp ((SMSpecDF Γ T Sig SS RS M CCoins E).Range q × EStateL Γ T Sig SS RS M E K I) :=
  simulateQ lImpl
    ((implEDFShiftedB1 l (hooksLocalFixed cka prng fs mo j k_fs)
      (2 + Δcka) qep fs.maxSkip mo.tStar (moAuth mo).cfg (moAuth mo).policy q).run esL)

def runLocAtFixedDFShiftedDir2Paper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode) (j : ℕ) (k_fs : K)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) : ProbComp Bool := do
  let r ← simulateQ lImpl
    ((simulateQ (implEDFShiftedB1 l (hooksLocalFixed cka prng fs mo j k_fs)
      (2 + Δcka) qep fs.maxSkip mo.tStar (moAuth mo).cfg (moAuth mo).policy) oa).run esL)
  pure (authOut (2 + Δcka) (moAuth mo).policy r.2 && (r.2.h.lastIdx == some j))

def localAuthAtFixedDFShiftedDir2Paper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep j l : ℕ) (k_fs : K)
    (tL : Option ℕ) (t : ℕ) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) : ProbComp Bool := do
  let mo : Mode := ⟨false, tL, t⟩
  let (vs, h) ← simulateQ lImpl ((initLocalFixed cka prng fs lam mo j k_fs).run {})
  match vs with
  | none => return false
  | some (vA, vB) =>
    let g : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := false }
    runLocAtFixedDFShiftedDir2Paper cka prng fs Δcka qep l mo j k_fs A { g, h }

omit [SampleableType KR] [SampleableType KC] in
theorem runPDFShiftedDir2Paper_pure (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode) (b' : Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    runPDFShiftedDir2Paper cka prng fs Δcka qep l mo (pure b') esP sp =
      pure (authOut (2 + Δcka) (moAuth mo).policy esP) := by
  simp [runPDFShiftedDir2Paper, map_eq_bind_pure_comp]

omit [SampleableType KR] [SampleableType KC] in
theorem runLocDFShiftedDir2Paper_pure (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode) (b' : Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    runLocDFShiftedDir2Paper cka prng fs Δcka qep l mo (pure b') esL =
      pure (authOut (2 + Δcka) (moAuth mo).policy esL) := by
  simp [runLocDFShiftedDir2Paper, map_eq_bind_pure_comp]

omit [SampleableType KR] [SampleableType KC] in
theorem runLocAtDFShiftedDir2Paper_pure (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep l : ℕ) (mo : Mode) (j : ℕ) (b' : Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    runLocAtDFShiftedDir2Paper cka prng fs Δcka qep l mo j (pure b') esL =
      pure (authOut (2 + Δcka) (moAuth mo).policy esL && (esL.h.lastIdx == some j)) := by
  simp [runLocAtDFShiftedDir2Paper, map_eq_bind_pure_comp]

omit [SampleableType KR] [SampleableType KC] in
theorem runLocAtFixedDFShiftedDir2Paper_pure (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep l : ℕ) (mo : Mode) (j : ℕ) (k_fs : K)
    (b' : Bool) (esL : EStateL Γ T Sig SS RS M E K I) :
    runLocAtFixedDFShiftedDir2Paper cka prng fs Δcka qep l mo j k_fs (pure b') esL =
      pure (authOut (2 + Δcka) (moAuth mo).policy esL && (esL.h.lastIdx == some j)) := by
  simp [runLocAtFixedDFShiftedDir2Paper, map_eq_bind_pure_comp]

omit [SampleableType KR] [SampleableType KC] in
theorem runPDFShiftedDir2Paper_query_bind (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    runPDFShiftedDir2Paper cka prng fs Δcka qep l mo (liftM (OracleSpec.query q) >>= k) esP sp =
      stepPDFShiftedDir2Paper cka prng fs Δcka qep l mo q esP sp >>= fun r =>
        runPDFShiftedDir2Paper cka prng fs Δcka qep l mo (k r.1.1) r.1.2 r.2 := by
  simp [runPDFShiftedDir2Paper, stepPDFShiftedDir2Paper, simulateQ_bind, StateT.run_bind,
    map_eq_bind_pure_comp, bind_assoc]

omit [SampleableType KR] [SampleableType KC] in
theorem runLocDFShiftedDir2Paper_query_bind (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    runLocDFShiftedDir2Paper cka prng fs Δcka qep l mo (liftM (OracleSpec.query q) >>= k) esL =
      stepLDFShiftedDir2Paper cka prng fs Δcka qep l mo q esL >>= fun r =>
        runLocDFShiftedDir2Paper cka prng fs Δcka qep l mo (k r.1) r.2 := by
  simp [runLocDFShiftedDir2Paper, stepLDFShiftedDir2Paper, simulateQ_bind, StateT.run_bind,
    map_eq_bind_pure_comp, bind_assoc]

omit [SampleableType KR] [SampleableType KC] in
theorem runLocAtDFShiftedDir2Paper_query_bind (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (j : ℕ) (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    runLocAtDFShiftedDir2Paper cka prng fs Δcka qep l mo j (liftM (OracleSpec.query q) >>= k) esL =
      stepLDFShiftedDir2Paper cka prng fs Δcka qep l mo q esL >>= fun r =>
        runLocAtDFShiftedDir2Paper cka prng fs Δcka qep l mo j (k r.1) r.2 := by
  simp [runLocAtDFShiftedDir2Paper, stepLDFShiftedDir2Paper, simulateQ_bind, StateT.run_bind,
    map_eq_bind_pure_comp, bind_assoc]

omit [SampleableType KR] [SampleableType KC] in
theorem runLocAtFixedDFShiftedDir2Paper_query_bind (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (j : ℕ) (k_fs : K) (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    runLocAtFixedDFShiftedDir2Paper cka prng fs Δcka qep l mo j k_fs
        (liftM (OracleSpec.query q) >>= k) esL =
      stepLFixedDFShiftedDir2Paper cka prng fs Δcka qep l mo j k_fs q esL >>= fun r =>
        runLocAtFixedDFShiftedDir2Paper cka prng fs Δcka qep l mo j k_fs (k r.1) r.2 := by
  simp [runLocAtFixedDFShiftedDir2Paper, stepLFixedDFShiftedDir2Paper, simulateQ_bind,
    StateT.run_bind, map_eq_bind_pure_comp, bind_assoc]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem vSend_congr {tspec : OracleSpec.{0, 0} ι} {Γv Sv SSv RSv HS : Type}
    {hk₁ hk₂ : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv}
    (h1 : hk₁.startSend = hk₂.startSend) (h2 : hk₁.fsSend = hk₂.fsSend)
    (ctx : Ctx Γv T Sv SSv RSv M E) (P : Party) (vp : VP Γv T Sv SSv RSv)
    (m : M) (pair : Option (M × M)) (r : Option CCoins) :
    vSend hk₁ ctx P vp m pair r = vSend hk₂ ctx P vp m pair r := by
  unfold vSend; rw [h1, h2]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem transmitE_congr {tspec : OracleSpec.{0, 0} ι} {Γv Sv SSv RSv HS : Type}
    {hk₁ hk₂ : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv}
    (h1 : hk₁.startSend = hk₂.startSend) (h2 : hk₁.fsSend = hk₂.fsSend)
    (Δ qep : ℕ) (π : Policy) :
    transmitE hk₁ Δ qep π = transmitE hk₂ Δ qep π := by
  funext ⟨P, m, r⟩; unfold transmitE; simp only [vSend_congr h1 h2]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem challE_congr {tspec : OracleSpec.{0, 0} ι} {Γv Sv SSv RSv HS : Type}
    {hk₁ hk₂ : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv}
    (h1 : hk₁.startSend = hk₂.startSend) (h2 : hk₁.fsSend = hk₂.fsSend)
    (Δ qep : ℕ) (cfg : SM.Config M) (π : Policy) :
    challE hk₁ Δ qep cfg π = challE hk₂ Δ qep cfg π := by
  funext ⟨P, m0, m1, r⟩; unfold challE; simp only [vSend_congr h1 h2]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem corrEShiftedPaper_congr {tspec : OracleSpec.{0, 0} ι} {Γv Sv SSv RSv HS : Type}
    {hk₁ hk₂ : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv}
    (h : hk₁.reveal = hk₂.reveal) (l : ℕ) (π : Policy) :
    corrEShiftedPaper l hk₁ π = corrEShiftedPaper l hk₂ π := by
  funext P; unfold corrEShiftedPaper; rw [h]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem implEDFShiftedPaper_q12_congr {tspec : OracleSpec.{0, 0} ι} {Γv Sv SSv RSv HS : Type}
    (l : ℕ) (hk₁ hk₂ : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (h1 : hk₁.startSend = hk₂.startSend) (h2 : hk₁.fsSend = hk₂.fsSend)
    (Δ qep maxSkip tStar : ℕ) (cfg : SM.Config M) (π : Policy)
    (q12 : (Party × M × Option CCoins) ⊕ (Party × M × M × Option CCoins)) :
    implEDFShiftedB1 l hk₁ Δ qep maxSkip tStar cfg π (.inr (.inl (.inl (.inl (.inl q12))))) =
      implEDFShiftedPaper l hk₂ Δ qep maxSkip cfg π (.inr (.inl (.inl (.inl (.inl q12))))) := by
  cases q12
  · simp only [implEDFShiftedB1, implEDFShiftedPaper, QueryImpl.add_apply, transmitE_congr h1 h2]
  · simp only [implEDFShiftedB1, implEDFShiftedPaper, QueryImpl.add_apply, challE_congr h1 h2]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem implEDFShiftedPaper_corr_congr {tspec : OracleSpec.{0, 0} ι} {Γv Sv SSv RSv HS : Type}
    (l : ℕ) (hk₁ hk₂ : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (h : hk₁.reveal = hk₂.reveal)
    (Δ qep maxSkip tStar : ℕ) (cfg : SM.Config M) (π : Policy) (P : Party) :
    implEDFShiftedB1 l hk₁ Δ qep maxSkip tStar cfg π (.inr (.inl (.inr P))) =
      implEDFShiftedPaper l hk₂ Δ qep maxSkip cfg π (.inr (.inl (.inr P))) := by
  simp only [implEDFShiftedB1, implEDFShiftedPaper, QueryImpl.add_apply, corrEShiftedPaper_congr h]

omit [SampleableType KR] [SampleableType KC] in
theorem stepPDFShiftedDir2Paper_inl (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode)
    (n : unifSpec.Domain) (esP : EStateP Γ T Sig SS RS M E K)
    (sp : PRFPRNG.GameState Sig I K) :
    stepPDFShiftedDir2Paper cka prng fs Δcka qep l mo (.inl n) esP sp =
      stepPDFShiftedPaper cka prng fs Δcka qep l (moAuth mo) (.inl n) esP sp := by
  simp only [stepPDFShiftedDir2Paper, stepPDFShiftedPaper, implEDFShiftedB1, implEDFShiftedPaper,
    QueryImpl.add_apply]

omit [SampleableType KR] [SampleableType KC] in
theorem stepLDFShiftedDir2Paper_inl (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode)
    (n : unifSpec.Domain) (esL : EStateL Γ T Sig SS RS M E K I) :
    stepLDFShiftedDir2Paper cka prng fs Δcka qep l mo (.inl n) esL =
      stepLDFShiftedPaper cka prng fs Δcka qep l (moAuth mo) (.inl n) esL := by
  simp only [stepLDFShiftedDir2Paper, stepLDFShiftedPaper, implEDFShiftedB1, implEDFShiftedPaper,
    QueryImpl.add_apply]

omit [SampleableType KR] [SampleableType KC] in
theorem stepLFixedDFShiftedDir2Paper_inl (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep l : ℕ) (mo : Mode) (j : ℕ) (k_fs : K)
    (n : unifSpec.Domain) (esL : EStateL Γ T Sig SS RS M E K I) :
    stepLFixedDFShiftedDir2Paper cka prng fs Δcka qep l mo j k_fs (.inl n) esL =
      stepLFixedDFShiftedPaper cka prng fs Δcka qep l (moAuth mo) j k_fs (.inl n) esL := by
  simp only [stepLFixedDFShiftedDir2Paper, stepLFixedDFShiftedPaper, implEDFShiftedB1,
    implEDFShiftedPaper, QueryImpl.add_apply]

theorem stepPDFShiftedDir2Paper_abort (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) (hab : esP.abort = true) :
    ∀ r ∈ support (stepPDFShiftedDir2Paper cka prng fs Δcka qep l mo q esP sp),
      r.1.2.abort = true := by
  intro r hr
  rcases q with n | ((((q12 | q3) | q4) | P) | ⟨P, c, c'⟩)
  · rw [stepPDFShiftedDir2Paper_inl] at hr
    exact stepPDFShiftedPaper_abort cka prng fs Δcka qep l (moAuth mo) (.inl n) esP sp hab r hr
  · rw [stepPDFShiftedDir2Paper,
      implEDFShiftedPaper_q12_congr l (hooksPRNG cka prng fs mo)
        (hooksPRNG cka prng fs (moAuth mo)) rfl rfl] at hr
    exact stepPDFShiftedPaper_abort cka prng fs Δcka qep l (moAuth mo)
      (.inr (.inl (.inl (.inl (.inl q12))))) esP sp hab r hr
  · simp only [stepPDFShiftedDir2Paper, implEDFShiftedB1, QueryImpl.add_apply, deliverE,
      StateT.run_bind, StateT.run_get, pure_bind, hab, Bool.true_or, ↓reduceIte, StateT.run_pure,
      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hab
  · simp only [stepPDFShiftedDir2Paper, implEDFShiftedB1, QueryImpl.add_apply, injectEB1,
      StateT.run_bind, StateT.run_get, pure_bind, hab, Bool.true_or, ↓reduceIte, StateT.run_pure,
      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hab
  · rw [stepPDFShiftedDir2Paper,
      implEDFShiftedPaper_corr_congr l (hooksPRNG cka prng fs mo)
        (hooksPRNG cka prng fs (moAuth mo)) rfl] at hr
    exact stepPDFShiftedPaper_abort cka prng fs Δcka qep l (moAuth mo)
      (.inr (.inl (.inr P))) esP sp hab r hr
  · simp only [stepPDFShiftedDir2Paper, implEDFShiftedB1, QueryImpl.add_apply, deliverForgeEB1,
      StateT.run_bind, StateT.run_get, pure_bind, hab, Bool.true_or, ↓reduceIte, StateT.run_pure,
      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hab

theorem runPDFShiftedDir2Paper_abort (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K} (hab : esP.abort = true) :
    𝒟[runPDFShiftedDir2Paper cka prng fs Δcka qep l mo oa esP sp] {true} = 0 := by
  induction oa using OracleComp.inductionOn generalizing esP sp with
  | pure b' =>
    rw [runPDFShiftedDir2Paper_pure]
    simp [authOut, hab]
  | query_bind q k ih =>
    rw [runPDFShiftedDir2Paper_query_bind]
    exact evalDist_bind_eq_zero _ _ fun r hr =>
      ih r.1.1 (stepPDFShiftedDir2Paper_abort cka prng fs Δcka qep l mo q esP sp hab r hr)

theorem runPDFShiftedDir2Paper_abort_le (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K} (hab : esP.abort = true)
    (rhs : ℝ≥0∞) :
    𝒟[runPDFShiftedDir2Paper cka prng fs Δcka qep l mo oa esP sp] {true} ≤ rhs := by
  rw [runPDFShiftedDir2Paper_abort cka prng fs Δcka qep l mo oa hab]
  exact zero_le

theorem leComp_injectE_PRNG_local_dir2 (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ)
    (mo : Mode) (hΔ : Δcka = 0) (arg : Party × (Header T × E))
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    {esL : EStateL Γ T Sig SS RS M E K I} (hsync : SyncPL Δcka mo esP sp esL) :
    LeComp (StepRel Δcka mo)
      ((simulateQ (pImpl prng)
        ((injectEB1 (hooksPRNG cka prng fs mo) qep mo.tStar (moAuth mo).cfg arg).run esP)).run sp)
      (simulateQ lImpl
        ((injectEB1 (hooksLocal cka prng fs mo) qep mo.tStar (moAuth mo).cfg arg).run esL)) := by
  subst hΔ
  rcases arg with ⟨P, c⟩
  unfold injectEB1
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abort_eq, eraseSt_win hsync.g_eq, eraseSt_inTransit hsync.g_eq,
    eraseSt_safeInj hsync.g_eq]
  by_cases hguard : (esL.abort || esL.g.win || (esL.g.inTransit P.other c).isSome ||
      !esL.g.safeInj 2) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, run_liftH, simulateQ_bind, bind_assoc]
    have hsafe : esL.g.safeInj 2 = true := by
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at hguard
      exact Bool.eq_true_of_not_eq_false hguard.2
    have hσ_tStar : P.sendsIn (esL.g.epoch P + 1) = false → esL.g.epoch P + 1 = mo.tStar →
        ¬ (mo.tL.isSome = true ∧ mo.tStar = mo.tH) → sp.σ = (esL.g.st P).root := by
      intro _ he1 hnot_th
      exact (hsync.root_pred (by omega) P (by omega) hnot_th).symm
    refine (leComp_vRecv_PRNG_local cka prng fs mo (hsync.vp_rel P) hsync.cache_rel
      hsync.sp_b hsync.table_eq hsync.corr_tH hσ_tStar).bind ?_
    rintro ⟨⟨res_vrP, hP1⟩, sp1⟩ ⟨res_vrL, hL1⟩ hvr
    rcases hvr with hnone | ⟨hP_none, hL_none, hhP1, hc1, hb1, htab1, hcorr1, hσ1⟩ |
      ⟨vpP', vpL', i', m', hP_some, hL_some, htle, hns, hvp', hhP1, hc1, hb1, htab1, hcorr1,
        hσ1, hroot_le, _⟩
    · dsimp only at hnone; subst hnone
      simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        simulateQ_pure]
      exact LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · dsimp only at hP_none hL_none hhP1; subst hP_none hL_none hhP1
      simp only [pure_bind, StateT.run_pure, simulateQ_pure]
      refine LeComp.pure (Or.inr ⟨rfl, ⟨hsync.abort_eq, hsync.g_eq, hsync.vp_rel,
        fun t' => by rw [hc1]; exact hsync.cache_rel t', hb1, htab1, hcorr1, hsync.comp_inv,
        hsync.trans_epoch, hsync.epoch_le, hsync.epoch_sends,
        fun Q h1 h2 => (hsync.root_max Q h1 h2).trans hσ1.symm,
        fun hpos Q h1 h2 => (hsync.root_pred hpos Q h1 h2).trans hσ1.symm,
        fun Tc σc k idx? h1 h2 => (hsync.cache_max Tc σc k idx? (hc1 ▸ h1) h2).trans hσ1.symm⟩⟩)
    · dsimp only at hP_some hL_some hhP1; subst hP_some hL_some hhP1
      simp only [StateT.run_pure, simulateQ_pure, pure_bind]
      by_cases hqep : qep + 1 < c.1.1
      · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure]
        refine LeComp.pure (Or.inr ⟨rfl, ⟨hsync.abort_eq, hsync.g_eq, hsync.vp_rel,
          fun t' => by rw [hc1]; exact hsync.cache_rel t', hb1, htab1, hcorr1, hsync.comp_inv,
          hsync.trans_epoch, hsync.epoch_le, hsync.epoch_sends,
          fun Q h1 h2 => (hsync.root_max Q h1 h2).trans hσ1.symm,
          fun hpos Q h1 h2 => (hsync.root_pred hpos Q h1 h2).trans hσ1.symm,
          fun Tc σc k idx? h1 h2 => (hsync.cache_max Tc σc k idx? (hc1 ▸ h1) h2).trans hσ1.symm⟩⟩)
      · simp only [hqep, ↓reduceIte]
        rw [eraseSt_trivB1_l11 hsync.g_eq]
        by_cases htriv : trivB1 mo.tStar esL.g ⟨P.other, c.1.1, i'⟩ = true
        · have hne_e1 : c.1.1 ≠ esL.g.epoch P + 1 := by
            intro heq
            rw [trivB1_eq_trivial_of_new_epoch mo.tStar esL.g P _ heq, heq,
              trivial_false_of_safeInj esL.g 2 P i' hsafe hsync.comp_inv] at htriv
            cases htriv
          have htle_e : c.1.1 ≤ esL.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hne_e1)
          have hmax_e : max (esL.g.epoch P) c.1.1 = esL.g.epoch P := Nat.max_eq_left htle_e
          simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_PRNG, run_commitE_local,
            StateT.run_pure, StateT.run_modify, pure_bind, simulateQ_pure]
          have hacc_ep : (esL.g.accept P vpL' ⟨P.other, c.1.1, i'⟩).epoch = esL.g.epoch := by
            dsimp only [SM.GameState.accept, SM.GameState.delete]
            rw [hmax_e, Function.update_eq_self]
          refine LeComp.pure (Or.inr ⟨rfl, ⟨hsync.abort_eq,
            eraseSt_accept hsync.g_eq P vpP' vpL' _, ?_,
            fun t' => by rw [hc1]; exact hsync.cache_rel t', hb1, htab1, hcorr1,
            comp_inv_accept esL.g 2 P vpL' _ hsync.comp_inv, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩)
          · intro Q; dsimp only; rw [hacc_ep]; dsimp only [SM.GameState.accept]
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self]; rw [← hmax_e]; exact hvp'
            · simp only [Function.update_of_ne hQ]; exact hsync.vp_rel Q
          · intro r hr; dsimp only at hr ⊢; rw [hacc_ep]
            simp only [SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hr
            exact hsync.trans_epoch r hr.1
          · intro Q; dsimp only; rw [hacc_ep]; exact hsync.epoch_le Q
          · intro Q; dsimp only; rw [hacc_ep]; exact hsync.epoch_sends Q
          · intro Q hQ_max hQ_lt; dsimp only at hQ_max hQ_lt ⊢
            rw [hacc_ep] at hQ_max hQ_lt; rw [hσ1]; dsimp only [SM.GameState.accept]
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self, hroot_le htle_e]
              exact hsync.root_max P hQ_max hQ_lt
            · simp only [Function.update_of_ne hQ]; exact hsync.root_max Q hQ_max hQ_lt
          · intro hpos Q hQ_pred hnot_th; dsimp only at hQ_pred ⊢
            rw [hacc_ep] at hQ_pred; rw [hσ1]; dsimp only [SM.GameState.accept]
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self, hroot_le htle_e]
              exact hsync.root_pred hpos P hQ_pred hnot_th
            · simp only [Function.update_of_ne hQ]; exact hsync.root_pred hpos Q hQ_pred hnot_th
          · intro Tc σc k idx? hc_max hmax_lt; dsimp only at hc_max hmax_lt ⊢
            rw [hacc_ep, hc1] at hc_max; rw [hacc_ep] at hmax_lt; rw [hσ1]
            exact hsync.cache_max Tc σc k idx? hc_max hmax_lt
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
          by_cases hfull : ((moAuth mo).cfg : SM.Config M).injectFull c.1.1 = true
          · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
              StateT.run_pure, simulateQ_pure]
            refine LeComp.pure (Or.inr ⟨rfl, ⟨hsync.abort_eq, ?_, hsync.vp_rel,
              fun t' => by rw [hc1]; exact hsync.cache_rel t', hb1, htab1, hcorr1, hsync.comp_inv,
              hsync.trans_epoch, hsync.epoch_le, hsync.epoch_sends,
              fun Q h1 h2 => (hsync.root_max Q h1 h2).trans hσ1.symm,
              fun hpos Q h1 h2 => (hsync.root_pred hpos Q h1 h2).trans hσ1.symm,
              fun Tc σc k idx? h1 h2 =>
                (hsync.cache_max Tc σc k idx? (hc1 ▸ h1) h2).trans hσ1.symm⟩⟩)
            have hg := hsync.g_eq
            simp [eraseSt, eraseSt_epoch hg, eraseSt_idx hg, eraseSt_tL hg, eraseSt_trans hg,
              eraseSt_chall hg, eraseSt_comp hg, eraseSt_maxAcc hg, eraseSt_b hg,
              eraseSt_leaks hg, eraseSt_corrs hg]
          · simp only [hfull, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
            refine LeComp.pure (Or.inr ⟨rfl, ⟨hsync.abort_eq, hsync.g_eq, hsync.vp_rel,
              fun t' => by rw [hc1]; exact hsync.cache_rel t', hb1, htab1, hcorr1, hsync.comp_inv,
              hsync.trans_epoch, hsync.epoch_le, hsync.epoch_sends,
              fun Q h1 h2 => (hsync.root_max Q h1 h2).trans hσ1.symm,
              fun hpos Q h1 h2 => (hsync.root_pred hpos Q h1 h2).trans hσ1.symm,
              fun Tc σc k idx? h1 h2 =>
                (hsync.cache_max Tc σc k idx? (hc1 ▸ h1) h2).trans hσ1.symm⟩⟩)

theorem leComp_deliverForgeE_PRNG_local_dir2 (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ)
    (mo : Mode) (arg : Party × (Header T × E) × (Header T × E))
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    {esL : EStateL Γ T Sig SS RS M E K I} (hsync : SyncPL Δcka mo esP sp esL) :
    LeComp (StepRel Δcka mo)
      ((simulateQ (pImpl prng)
        ((deliverForgeEB1 (hooksPRNG cka prng fs mo) qep mo.tStar (moAuth mo).cfg arg).run
          esP)).run sp)
      (simulateQ lImpl
        ((deliverForgeEB1 (hooksLocal cka prng fs mo) qep mo.tStar (moAuth mo).cfg arg).run
          esL)) := by
  rcases arg with ⟨P, c, c'⟩
  unfold deliverForgeEB1
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abort_eq, eraseSt_win hsync.g_eq]
  by_cases habw : (esL.abort || esL.g.win) = true
  · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [habw, Bool.false_eq_true, ↓reduceIte]
    rw [eraseSt_inTransit hsync.g_eq]
    cases htr : esL.g.inTransit P.other c with
    | none =>
      simp only [StateT.run_pure, simulateQ_pure]
      exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)
    | some r =>
      have hr_mem : r ∈ esL.g.trans ∧ r.pos.sender = P.other ∧ r.ct = c := by
        unfold SM.GameState.inTransit at htr
        have hfind := List.find?_some htr
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfind
        exact ⟨List.mem_of_find?_eq_some htr, hfind.1, hfind.2⟩
      rw [eraseSt_inTransit hsync.g_eq, eraseSt_comp hsync.g_eq]
      by_cases hguard :
          ((esL.g.inTransit P.other c').isSome || esL.g.comp.contains r.pos || c.1 != c'.1) = true
      · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
        exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)
      · simp only [hguard, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, run_liftH, simulateQ_bind, bind_assoc]
        simp only [Bool.not_eq_true, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hguard
        have hhdr : c.1 = c'.1 := hguard.2
        have hr_ep := hsync.trans_epoch r hr_mem.1
        have hr_pos_ep : r.pos.epoch = c'.1.1 := by rw [← hhdr, ← hr_ep.2, hr_mem.2.2]
        have hc_le_other : c'.1.1 ≤ esL.g.epoch P.other := by
          rw [← hr_pos_ep, ← hr_mem.2.1]; exact hr_ep.1
        have hσ_tStar : P.sendsIn (esL.g.epoch P + 1) = false → esL.g.epoch P + 1 = mo.tStar →
            ¬ (mo.tL.isSome = true ∧ mo.tStar = mo.tH) → sp.σ = (esL.g.st P).root := by
          intro _ he1 hnot_th; exact (hsync.root_pred (by omega) P (by omega) hnot_th).symm
        refine (leComp_vRecv_PRNG_local cka prng fs mo (hsync.vp_rel P) hsync.cache_rel
          hsync.sp_b hsync.table_eq hsync.corr_tH hσ_tStar).bind ?_
        rintro ⟨⟨res_vrP, hP1⟩, sp1⟩ ⟨res_vrL, hL1⟩ hvr
        rcases hvr with hnone | ⟨hP_none, hL_none, hhP1, hc1, hb1, htab1, hcorr1, hσ1⟩ |
          ⟨vpP', vpL', i', m', hP_some, hL_some, htle, hns, hvp', hhP1, hc1, hb1, htab1, hcorr1,
            hσ1, hroot_le, hcache_e1⟩
        · dsimp only at hnone; subst hnone
          simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            simulateQ_pure]
          exact LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · dsimp only at hP_none hL_none hhP1; subst hP_none hL_none hhP1
          simp only [pure_bind, StateT.run_pure, simulateQ_pure]
          refine LeComp.pure (Or.inr ⟨rfl, ⟨hsync.abort_eq, hsync.g_eq, hsync.vp_rel,
            fun t' => by rw [hc1]; exact hsync.cache_rel t', hb1, htab1, hcorr1, hsync.comp_inv,
            hsync.trans_epoch, hsync.epoch_le, hsync.epoch_sends,
            fun Q h1 h2 => (hsync.root_max Q h1 h2).trans hσ1.symm,
            fun hpos Q h1 h2 => (hsync.root_pred hpos Q h1 h2).trans hσ1.symm,
            fun Tc σc k idx? h1 h2 =>
              (hsync.cache_max Tc σc k idx? (hc1 ▸ h1) h2).trans hσ1.symm⟩⟩)
        · dsimp only at hP_some hL_some hhP1; subst hP_some hL_some hhP1
          have hne_ep : (c'.1.1 != r.pos.epoch) = false := by simp [hr_pos_ep]
          simp only [StateT.run_pure, simulateQ_pure, pure_bind, hne_ep, Bool.or_false]
          by_cases hqep : decide (qep + 1 < c'.1.1) = true
          · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure]
            refine LeComp.pure (Or.inr ⟨rfl, ⟨hsync.abort_eq, hsync.g_eq, hsync.vp_rel,
              fun t' => by rw [hc1]; exact hsync.cache_rel t', hb1, htab1, hcorr1, hsync.comp_inv,
              hsync.trans_epoch, hsync.epoch_le, hsync.epoch_sends,
              fun Q h1 h2 => (hsync.root_max Q h1 h2).trans hσ1.symm,
              fun hpos Q h1 h2 => (hsync.root_pred hpos Q h1 h2).trans hσ1.symm,
              fun Tc σc k idx? h1 h2 =>
                (hsync.cache_max Tc σc k idx? (hc1 ▸ h1) h2).trans hσ1.symm⟩⟩)
          · simp only [hqep, Bool.false_eq_true, ↓reduceIte]
            rw [eraseSt_trivB1_l11 hsync.g_eq]
            by_cases htriv : trivB1 mo.tStar esL.g ⟨P.other, c'.1.1, i'⟩ = true
            · simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_PRNG, run_commitE_local,
                StateT.run_pure, StateT.run_modify, pure_bind, simulateQ_pure]
              let pos : Pos := ⟨P.other, c'.1.1, i'⟩
              have hacc_ep_L : (esL.g.accept P vpL' pos).epoch =
                  Function.update esL.g.epoch P (max (esL.g.epoch P) c'.1.1) := rfl
              refine LeComp.pure (Or.inr ⟨rfl, ⟨hsync.abort_eq,
                eraseSt_accept hsync.g_eq P vpP' vpL' pos, ?_,
                fun t' => by rw [hc1]; exact hsync.cache_rel t', hb1, htab1, hcorr1,
                comp_inv_accept esL.g (2 + Δcka) P vpL' pos hsync.comp_inv,
                ?_, ?_, ?_, ?_, ?_, ?_⟩⟩)
              · intro Q; dsimp only; rw [hacc_ep_L]; dsimp only [SM.GameState.accept]
                by_cases hQ : Q = P
                · subst Q; simp only [Function.update_self]; exact hvp'
                · simp only [Function.update_of_ne hQ]; exact hsync.vp_rel Q
              · intro r' hr'; dsimp only at hr' ⊢; rw [hacc_ep_L]
                simp only [SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hr' ⊢
                obtain ⟨h1, h2⟩ := hsync.trans_epoch r' hr'.1
                refine ⟨?_, h2⟩
                by_cases hQ : r'.pos.sender = P
                · rw [hQ, Function.update_self]; rw [hQ] at h1; omega
                · rw [Function.update_of_ne hQ]; exact h1
              · intro Q; dsimp only; rw [hacc_ep_L]
                have hle_P := hsync.epoch_le P; have hle_other := hsync.epoch_le P.other
                cases Q <;> cases P <;>
                  simp [Party.other] at hc_le_other htle hle_P hle_other ⊢ <;> omega
              · intro Q hlt_Q; dsimp only at hlt_Q ⊢; rw [hacc_ep_L] at hlt_Q ⊢
                by_cases hnew : c'.1.1 = esL.g.epoch P + 1
                · have heq_other : esL.g.epoch P.other = esL.g.epoch P + 1 := by
                    have := hsync.epoch_le P.other; rw [Party.other_other] at this; omega
                  cases Q <;> cases P <;> simp [Party.other, hnew] at heq_other hlt_Q <;> omega
                · have htle_e : c'.1.1 ≤ esL.g.epoch P :=
                    Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
                  rw [Nat.max_eq_left htle_e, Function.update_eq_self] at hlt_Q ⊢
                  exact hsync.epoch_sends Q hlt_Q
              · intro Q hQ_max hQ_lt; dsimp only at hQ_max hQ_lt ⊢
                rw [hacc_ep_L] at hQ_max hQ_lt; rw [hσ1]
                dsimp only [SM.GameState.accept] at hQ_max hQ_lt ⊢
                by_cases hnew : c'.1.1 = esL.g.epoch P + 1
                · have heq_other : esL.g.epoch P.other = esL.g.epoch P + 1 := by
                    have := hsync.epoch_le P.other; rw [Party.other_other] at this; omega
                  have hmax_old : max (esL.g.epoch .A) (esL.g.epoch .B) = esL.g.epoch P + 1 := by
                    cases P <;> simp [Party.other] at heq_other ⊢ <;> omega
                  have hmax_new :
                      max (Function.update esL.g.epoch P (max (esL.g.epoch P) c'.1.1) .A)
                        (Function.update esL.g.epoch P (max (esL.g.epoch P) c'.1.1) .B) =
                        esL.g.epoch P + 1 := by
                    rw [hnew]; exact max_epoch_accept_succ (by omega) (by omega)
                  by_cases hQ : Q = P
                  · subst Q; simp only [Function.update_self] at hQ_lt ⊢
                    have he1_lt : esL.g.epoch P + 1 < mo.tStar := by omega
                    obtain ⟨Tc, k, idx?, hc_eq⟩ := hcache_e1 hnew (by omega)
                    rw [← hmax_old] at hc_eq he1_lt
                    exact hsync.cache_max Tc vpL'.root k idx? hc_eq he1_lt
                  · simp only [Function.update_of_ne hQ] at hQ_max hQ_lt ⊢
                    exact hsync.root_max Q (by rw [hmax_old, ← hmax_new, hQ_max]) hQ_lt
                · have htle_e : c'.1.1 ≤ esL.g.epoch P :=
                    Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
                  rw [Nat.max_eq_left htle_e, Function.update_eq_self] at hQ_max hQ_lt
                  by_cases hQ : Q = P
                  · subst Q; simp only [Function.update_self, hroot_le htle_e]
                    exact hsync.root_max P hQ_max hQ_lt
                  · simp only [Function.update_of_ne hQ]; exact hsync.root_max Q hQ_max hQ_lt
              · intro hpos Q hQ_pred hnot_th; dsimp only at hQ_pred ⊢
                rw [hacc_ep_L] at hQ_pred; rw [hσ1]; dsimp only [SM.GameState.accept] at hQ_pred ⊢
                by_cases hnew : c'.1.1 = esL.g.epoch P + 1
                · have heq_other : esL.g.epoch P.other = esL.g.epoch P + 1 := by
                    have := hsync.epoch_le P.other; rw [Party.other_other] at this; omega
                  have hmax_old : max (esL.g.epoch .A) (esL.g.epoch .B) = esL.g.epoch P + 1 := by
                    cases P <;> simp [Party.other] at heq_other ⊢ <;> omega
                  by_cases hQ : Q = P
                  · subst Q; simp only [Function.update_self] at hQ_pred ⊢
                    have he1_lt : esL.g.epoch P + 1 < mo.tStar := by omega
                    obtain ⟨Tc, k, idx?, hc_eq⟩ := hcache_e1 hnew (by omega)
                    rw [← hmax_old] at hc_eq he1_lt
                    exact hsync.cache_max Tc vpL'.root k idx? hc_eq he1_lt
                  · simp only [Function.update_of_ne hQ] at hQ_pred ⊢
                    exact hsync.root_pred hpos Q hQ_pred hnot_th
                · have htle_e : c'.1.1 ≤ esL.g.epoch P :=
                    Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
                  rw [Nat.max_eq_left htle_e, Function.update_eq_self] at hQ_pred
                  by_cases hQ : Q = P
                  · subst Q; simp only [Function.update_self, hroot_le htle_e]
                    exact hsync.root_pred hpos P hQ_pred hnot_th
                  · simp only [Function.update_of_ne hQ]
                    exact hsync.root_pred hpos Q hQ_pred hnot_th
              · intro Tc σc k idx? hc_max hmax_lt; dsimp only at hc_max hmax_lt ⊢
                rw [hacc_ep_L, hc1] at hc_max; rw [hacc_ep_L] at hmax_lt; rw [hσ1]
                have hmax_eq : max (Function.update esL.g.epoch P (max (esL.g.epoch P) c'.1.1) .A)
                    (Function.update esL.g.epoch P (max (esL.g.epoch P) c'.1.1) .B) =
                    max (esL.g.epoch .A) (esL.g.epoch .B) := by
                  cases P <;> simp [Party.other] at hc_le_other ⊢ <;> omega
                rw [hmax_eq] at hc_max hmax_lt
                exact hsync.cache_max Tc σc k idx? hc_max hmax_lt
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
              by_cases hfull : ((moAuth mo).cfg : SM.Config M).injectFull c'.1.1 = true
              · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
                  StateT.run_pure, simulateQ_pure]
                refine LeComp.pure (Or.inr ⟨rfl, ⟨hsync.abort_eq, ?_, hsync.vp_rel,
                  fun t' => by rw [hc1]; exact hsync.cache_rel t', hb1, htab1, hcorr1,
                  hsync.comp_inv, hsync.trans_epoch, hsync.epoch_le, hsync.epoch_sends,
                  fun Q h1 h2 => (hsync.root_max Q h1 h2).trans hσ1.symm,
                  fun hpos Q h1 h2 => (hsync.root_pred hpos Q h1 h2).trans hσ1.symm,
                  fun Tc σc k idx? h1 h2 =>
                    (hsync.cache_max Tc σc k idx? (hc1 ▸ h1) h2).trans hσ1.symm⟩⟩)
                have hg := hsync.g_eq
                simp [eraseSt, eraseSt_epoch hg, eraseSt_idx hg, eraseSt_tL hg, eraseSt_trans hg,
                  eraseSt_chall hg, eraseSt_comp hg, eraseSt_maxAcc hg, eraseSt_b hg,
                  eraseSt_leaks hg, eraseSt_corrs hg]
              · simp only [hfull, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
                refine LeComp.pure (Or.inr ⟨rfl, ⟨hsync.abort_eq, hsync.g_eq, hsync.vp_rel,
                  fun t' => by rw [hc1]; exact hsync.cache_rel t', hb1, htab1, hcorr1,
                  hsync.comp_inv, hsync.trans_epoch, hsync.epoch_le, hsync.epoch_sends,
                  fun Q h1 h2 => (hsync.root_max Q h1 h2).trans hσ1.symm,
                  fun hpos Q h1 h2 => (hsync.root_pred hpos Q h1 h2).trans hσ1.symm,
                  fun Tc σc k idx? h1 h2 =>
                    (hsync.cache_max Tc σc k idx? (hc1 ▸ h1) h2).trans hσ1.symm⟩⟩)

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem syncPL_moAuth {Δcka : ℕ} {mo : Mode}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    {esL : EStateL Γ T Sig SS RS M E K I} :
    SyncPL Δcka (moAuth mo) esP sp esL ↔ SyncPL Δcka mo esP sp esL :=
  ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ =>
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩,
   fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ =>
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩⟩

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem stepRel_moAuth {α : Type} (Δcka : ℕ) (mo : Mode) :
    StepRel (Γ := Γ) (T := T) (Sig := Sig) (SS := SS) (RS := RS) (M := M) (E := E) (K := K) (I := I)
      (α := α) Δcka (moAuth mo) = StepRel Δcka mo := by
  funext rP rL; exact propext (or_congr_right (and_congr_right fun _ => syncPL_moAuth))

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem sessInv_moAuth {mo : Mode} {q rem : ℕ} {esL : EStateL Γ T Sig SS RS M E K I} :
    SessInv (moAuth mo) q rem esL ↔ SessInv mo q rem esL :=
  ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩

omit [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem deliverE_cfg_moAuth {tspec : OracleSpec.{0, 0} ι} {HS Γv Sv SSv RSv : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv) (maxSkip : ℕ) (mo : Mode) :
    deliverE hk maxSkip (moAuth mo).cfg = deliverE hk maxSkip mo.cfg := by
  funext arg
  cases h : mo.auth <;> simp [deliverE, Mode.cfg, h, SM.Config.auth, SM.Config.priv]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem implEDFShiftedPaper_q3_moAuth {tspec : OracleSpec.{0, 0} ι} {Γv Sv SSv RSv HS : Type}
    (l : ℕ) (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip tStar : ℕ) (mo : Mode) (q3 : Party × (Header T × E)) :
    implEDFShiftedB1 l hk Δ qep maxSkip tStar (moAuth mo).cfg (moAuth mo).policy
      (.inr (.inl (.inl (.inl (.inr q3))))) =
    implE hk Δ qep maxSkip mo.cfg mo.policy (.inr (.inl (.inl (.inr q3)))) := by
  simp only [implEDFShiftedB1, implE, QueryImpl.add_apply, deliverE_cfg_moAuth]

theorem leComp_stepPDFShiftedDir2Paper_stepLDFShiftedDir2Paper (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (hΔ : Δcka = 0) (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    {esL : EStateL Γ T Sig SS RS M E K I} (hsync : SyncPL Δcka mo esP sp esL) :
    LeComp (StepRel Δcka mo)
      (stepPDFShiftedDir2Paper cka prng fs Δcka qep l mo q esP sp)
      (stepLDFShiftedDir2Paper cka prng fs Δcka qep l mo q esL) := by
  rcases q with n | ((((q12 | q3) | q4) | P) | df)
  · rw [← stepRel_moAuth, stepPDFShiftedDir2Paper_inl, stepLDFShiftedDir2Paper_inl]
    exact leComp_stepPDFShiftedPaper_stepLDFShiftedPaper cka prng fs Δcka qep l (moAuth mo) rfl
      (.inl n) (syncPL_moAuth.mpr hsync)
  · rw [← stepRel_moAuth, stepPDFShiftedDir2Paper, stepLDFShiftedDir2Paper,
      implEDFShiftedPaper_q12_congr l (hooksPRNG cka prng fs mo)
        (hooksPRNG cka prng fs (moAuth mo)) rfl rfl,
      implEDFShiftedPaper_q12_congr l (hooksLocal cka prng fs mo)
        (hooksLocal cka prng fs (moAuth mo)) rfl rfl]
    exact leComp_stepPDFShiftedPaper_stepLDFShiftedPaper cka prng fs Δcka qep l (moAuth mo) rfl
      (.inr (.inl (.inl (.inl (.inl q12))))) (syncPL_moAuth.mpr hsync)
  · simp only [stepPDFShiftedDir2Paper, stepLDFShiftedDir2Paper, implEDFShiftedB1,
      QueryImpl.add_apply, deliverE_cfg_moAuth]
    exact leComp_deliverE_PRNG_local (cka := cka) (prng := prng) (fs := fs)
      (Δcka := Δcka) (mo := mo) q3 hsync
  · exact leComp_injectE_PRNG_local_dir2 cka prng fs Δcka qep mo hΔ q4 hsync
  · rw [← stepRel_moAuth, stepPDFShiftedDir2Paper, stepLDFShiftedDir2Paper,
      implEDFShiftedPaper_corr_congr l (hooksPRNG cka prng fs mo)
        (hooksPRNG cka prng fs (moAuth mo)) rfl,
      implEDFShiftedPaper_corr_congr l (hooksLocal cka prng fs mo)
        (hooksLocal cka prng fs (moAuth mo)) rfl]
    exact leComp_stepPDFShiftedPaper_stepLDFShiftedPaper cka prng fs Δcka qep l (moAuth mo) rfl
      (.inr (.inl (.inr P))) (syncPL_moAuth.mpr hsync)
  · exact leComp_deliverForgeE_PRNG_local_dir2 cka prng fs Δcka qep mo df hsync

theorem runPDFShiftedDir2Paper_le_runLocDFShiftedDir2Paper (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (hΔ : Δcka = 0) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    {esL : EStateL Γ T Sig SS RS M E K I} (hsync : SyncPL Δcka mo esP sp esL) :
    𝒟[runPDFShiftedDir2Paper cka prng fs Δcka qep l mo oa esP sp] {true} ≤
      𝒟[runLocDFShiftedDir2Paper cka prng fs Δcka qep l mo oa esL] {true} := by
  induction oa using OracleComp.inductionOn generalizing esP sp esL with
  | pure b' =>
    rw [runPDFShiftedDir2Paper_pure, runLocDFShiftedDir2Paper_pure]
    have hout : authOut (2 + Δcka) (moAuth mo).policy esP =
        authOut (2 + Δcka) (moAuth mo).policy esL := by
      unfold authOut
      rw [hsync.abort_eq, eraseSt_win hsync.g_eq,
        eraseSt_authOK hsync.g_eq (2 + Δcka) (moAuth mo).policy.tL (moAuth mo).policy.tStar]
    rw [hout]
  | query_bind q k ih =>
    rw [runPDFShiftedDir2Paper_query_bind, runLocDFShiftedDir2Paper_query_bind]
    refine leComp_stepPDFShiftedDir2Paper_stepLDFShiftedDir2Paper cka prng fs Δcka qep l mo hΔ q
      hsync _ _ ?_
    rintro ⟨⟨uP, esP'⟩, sp'⟩ ⟨uL, esL'⟩ (hab | ⟨rfl, hsync'⟩)
    · exact runPDFShiftedDir2Paper_abort_le cka prng fs Δcka qep l mo (k uP) hab _
    · exact ih uP hsync'

omit [SampleableType KR] [SampleableType KC] in
theorem evalDist_runPDFShiftedDir2Paper_eq (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (qep l : ℕ)
    (tL : Option ℕ) (t : ℕ) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    𝒟[do
      let x ← (simulateQ (pImpl prng)
        ((simulateQ (implEDFShiftedDir2Paper l (hooksPRNG cka prng fs ⟨false, tL, t⟩) qep
          fs.maxSkip t (Config.auth t) ⟨true, tL, t⟩) oa).run esP)).run sp
      pure (authOut 2 ⟨true, tL, t⟩ x.1.2)] =
    𝒟[runPDFShiftedDir2Paper cka prng fs 0 qep l ⟨false, tL, t⟩ oa esP sp] := by
  simp [runPDFShiftedDir2Paper, implEDFShiftedB1, implEDFShiftedDir2Paper, Mode.cfg, Mode.policy,
    map_eq_bind_pure_comp]

theorem branch_redPRNGAuthDFShiftedDir2Paper_le_localAuthDFShiftedDir2Paper
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) ( qep l t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng true
      (redPRNGAuthDFShiftedDir2Paper cka prng fs lam qep l t A)] {true} ≤
      𝒟[localAuthDFShiftedDir2Paper cka prng fs lam 0 qep l (some (l - 1)) t A] {true} := by
  let tL : Option ℕ := some (l - 1)
  have hpImpl : (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (PRFPRNG.GameState Sig I K) ProbComp) + prng.oracleImpl = pImpl prng := rfl
  unfold PRFPRNG.branch redPRNGAuthDFShiftedDir2Paper authSimDFShiftedDir2Paper
    engRunDFShiftedDir2Paper localAuthDFShiftedDir2Paper initPRNG initLocal
  simp only [hpImpl, StateT.run'_eq, map_eq_bind_pure_comp, StateT.run_bind, simulateQ_bind,
    bind_assoc, simulateQ_pImpl_run_lift_sampleT, simulateQ_lImpl_run_lift_sampleT, pure_bind]
  refine evalDist_bind_mono ($ᵗ KR) _ _ fun kr _ => evalDist_bind_mono ($ᵗ KC) _ _ fun kc _ => ?_
  have hroot0 := leComp_rootPRNG_rootL prng ⟨false, tL, t⟩
    (t := 0) (Ik := lam) (σv := none) (σ := prng.init kr)
    (hP := ({} : PRNGState T Sig K)) (sp := { σ := prng.init kr, b := true })
    (hL := ({} : LState T Sig K I))
    rfl rfl (fun h1 _ => Or.inr (by simp [tL, Mode.tH, healEpoch] at h1 ⊢)) (by omega)
    (fun _ => rfl)
  refine hroot0 _ _ ?_
  rintro ⟨⟨res0, hP0⟩, sp0⟩ ⟨⟨σL, kL, sid0⟩, hL0⟩ hrel0
  rcases hrel0 with hnone | ⟨σP, hres_eq, hhP0, hb0, htab0, hcorr0', hc0, _, hσ_rel, hlt0, _⟩
  · dsimp only at hnone; subst hnone; simp
  · dsimp only at hres_eq hhP0; subst hres_eq hhP0
    have hreg_det : ∃ (idx? : Option ℕ) (hL1 : LState T Sig K I),
        simulateQ lImpl ((regSessOf (T := T) (Sig := Sig) (K := K) sid0).run hL0) =
          pure (idx?, hL1) ∧ hL1.table = hL0.table ∧ hL1.cache = hL0.cache := by
      cases sid0 with
      | none => exact ⟨none, hL0, rfl, rfl, rfl⟩
      | some Ik =>
        unfold regSessOf regSess
        simp only [StateT.run_map, StateT.run_bind, StateT.run_get, pure_bind]
        split
        · exact ⟨some (hL0.sessions.idxOf Ik), hL0, rfl, rfl, rfl⟩
        · exact ⟨some hL0.sessions.length, { hL0 with sessions := hL0.sessions ++ [Ik] },
            rfl, rfl, rfl⟩
    obtain ⟨idx?, hL1, hreg_eq, htab1, hc1⟩ := hreg_det
    simp only [StateT.run_pure, simulateQ_pure, StateT.run_bind, simulateQ_bind, hreg_eq,
      pure_bind, bind_assoc, Function.comp_apply]
    rw [evalDist_runPDFShiftedDir2Paper_eq]
    refine runPDFShiftedDir2Paper_le_runLocDFShiftedDir2Paper cka prng fs 0 qep l
      ⟨false, tL, t⟩ rfl A ?_
    refine ⟨rfl, rfl, ?_, ?_, hb0, htab0.trans htab1.symm, hcorr0', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro P; cases P
      · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun t' => ?_, hσ_rel⟩
        dsimp only [mkParties]; split <;> rfl
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, hσ_rel⟩
    · intro t'; rw [hc1, hc0]; exact Or.inl ⟨rfl, rfl⟩
    · intro _ h; cases h
    · intro _ h; cases h
    · intro P; simp
    · intro P h; simp at h
    · intro P _ h; cases P <;> exact (hlt0 h).symm
    · intro h P _ _; cases P <;> exact (hlt0 h).symm
    · intro Tc σc k idx' hc_eq _; rw [hc1, hc0] at hc_eq; cases hc_eq

theorem stepLDFShiftedDir2Paper_sessInv (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) {q rem : ℕ} (q_sm : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I) (hS : SessInv mo q rem esL) :
    (∀ t, q_sm = .inl t →
      ∀ r ∈ support (stepLDFShiftedDir2Paper cka prng fs Δcka qep l mo (.inl t) esL),
        SessInv mo q rem r.2) ∧
    (∀ q_inr, q_sm = .inr q_inr → 0 < rem →
      ∀ r ∈ support (stepLDFShiftedDir2Paper cka prng fs Δcka qep l mo (.inr q_inr) esL),
        SessInv mo q (rem - 1) r.2) := by
  constructor
  · intro t ht r hr
    rw [stepLDFShiftedDir2Paper_inl] at hr
    exact sessInv_moAuth.mp ((stepLDFShiftedPaper_sessInv cka prng fs Δcka qep l (moAuth mo) rfl
      (.inl t) esL (sessInv_moAuth.mpr hS)).1 t rfl r hr)
  · intro q_inr hq_sm hrem r hr
    have hrem_mono :
        (esL.g.win = true ∧ ∃ j, j < q ∧ esL.h.lastIdx = some j) ∨
        (esL.g.win = false ∧
          ((mo.tStar = 0 ∧ esL.h.sessions.length ≤ 1 ∧ rem - 1 ≤ q) ∨
           (0 < mo.tStar ∧ esL.h.sessions.length + (rem - 1) ≤ q))) := by
      rcases hS.bound with hwin | ⟨hnw, ⟨ht0, hle1, _⟩ | hpos⟩
      · exact Or.inl hwin
      · exact Or.inr ⟨hnw, Or.inl ⟨ht0, hle1, by omega⟩⟩
      · exact Or.inr ⟨hnw, Or.inr ⟨hpos.1, by omega⟩⟩
    have hS_noop : SessInv mo q (rem - 1) esL := ⟨hS.vR_idx, hS.cache_idx, hrem_mono⟩
    rcases q_inr with ((((q12 | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
    · rw [stepLDFShiftedDir2Paper,
        implEDFShiftedPaper_q12_congr l (hooksLocal cka prng fs mo)
          (hooksLocal cka prng fs (moAuth mo)) rfl rfl] at hr
      exact sessInv_moAuth.mp ((stepLDFShiftedPaper_sessInv cka prng fs Δcka qep l (moAuth mo) rfl
        (.inr (.inl (.inl (.inl (.inl q12))))) esL (sessInv_moAuth.mpr hS)).2 _ rfl hrem r hr)
    · simp only [stepLDFShiftedDir2Paper, implEDFShiftedB1,
        QueryImpl.add_apply, deliverE, moAuth, Mode.cfg, ↓reduceIte, SM.Config.auth,
        Bool.false_and, Bool.false_eq_true, StateT.run_bind, StateT.run_get, pure_bind] at hr
      split at hr
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact hS_noop
      · rename_i hnot_ab_win
        simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hnot_ab_win
        rcases hS.bound with ⟨hwin, _⟩ | ⟨_, hlen_bound⟩
        · rw [hwin] at hnot_ab_win; cases hnot_ab_win.2
        · split at hr
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact hS_noop
          · simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind,
              MonadAttach.mem_support_bind] at hr
            rcases hr with ⟨⟨res_vr, h'⟩, hvr, hr2⟩
            obtain ⟨hl1, hl2, h0, hcache', hvp'⟩ :=
              mem_support_vRecv_local cka prng fs mo hvr (hS.vR_idx P) hS.cache_idx
            have hbound' :
                (esL.g.win = true ∧ ∃ j, j < q ∧ h'.lastIdx = some j) ∨
                (esL.g.win = false ∧
                  ((mo.tStar = 0 ∧ h'.sessions.length ≤ 1 ∧ rem - 1 ≤ q) ∨
                   (0 < mo.tStar ∧ h'.sessions.length + (rem - 1) ≤ q))) := by
              refine Or.inr ⟨hnot_ab_win.2, ?_⟩
              rcases hlen_bound with ⟨ht0, hle1, _⟩ | ⟨htpos, _⟩
              · exact Or.inl ⟨ht0, by rw [h0 ht0]; exact hle1, by omega⟩
              · exact Or.inr ⟨htpos, by omega⟩
            have hc' : ∀ Tc σ k idx?, h'.cache mo.tStar = some (Tc, σ, k, idx?) →
                ∃ idx, idx < h'.sessions.length ∧ idx? = some idx := by
              intro Tc σ k idx? hc; rw [hcache'] at hc
              obtain ⟨idx, hlt, heq⟩ := hS.cache_idx Tc σ k idx? hc
              exact ⟨idx, lt_of_lt_of_le hlt hl1, heq⟩
            cases res_vr with
            | none =>
              simp only [abortE, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
              subst hr2
              exact ⟨fun Q rsv hq => let ⟨i, h1, h2⟩ := hS.vR_idx Q rsv hq
                ⟨i, lt_of_lt_of_le h1 hl1, h2⟩, hc', hbound'⟩
            | some res_vr' =>
              cases res_vr' with
              | none =>
                simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hr2
                subst hr2
                exact ⟨fun Q rsv hq => let ⟨i, h1, h2⟩ := hS.vR_idx Q rsv hq
                  ⟨i, lt_of_lt_of_le h1 hl1, h2⟩, hc', hbound'⟩
              | some val =>
                rcases val with ⟨st', t', i', m'⟩
                simp only [commitE, hooksLocal, run_liftH, pure_bind, StateT.run_bind,
                  StateT.run_pure, StateT.run_modify, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hr2
                subst hr2
                obtain ⟨_, hvR_st', _⟩ := hvp' st' t' i' m' rfl
                refine ⟨fun Q rsv hq => ?_, hc', hbound'⟩
                dsimp only [SM.GameState.accept, SM.GameState.delete] at hq
                rw [Function.update_idem] at hq
                exact hS.mono_sessions mo hl1 hvR_st' Q rsv hq
    · simp only [stepLDFShiftedDir2Paper, implEDFShiftedB1,
        QueryImpl.add_apply, injectEB1, moAuth, Mode.cfg, ↓reduceIte, SM.Config.auth,
        StateT.run_bind, StateT.run_get, pure_bind] at hr
      split at hr
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact hS_noop
      · rename_i hnot_guard
        simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hnot_guard
        have hnw : esL.g.win = false := hnot_guard.1.1.2
        rcases hS.bound with ⟨hwin, _⟩ | ⟨_, hlen_bound⟩
        · rw [hwin] at hnw; cases hnw
        · simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind,
            MonadAttach.mem_support_bind] at hr
          rcases hr with ⟨⟨res_vr, h'⟩, hvr, hr2⟩
          obtain ⟨hl1, hl2, h0, hcache', hvp'⟩ :=
            mem_support_vRecv_local cka prng fs mo hvr (hS.vR_idx P) hS.cache_idx
          have hbound' :
              (esL.g.win = true ∧ ∃ j, j < q ∧ h'.lastIdx = some j) ∨
              (esL.g.win = false ∧
                ((mo.tStar = 0 ∧ h'.sessions.length ≤ 1 ∧ rem - 1 ≤ q) ∨
                 (0 < mo.tStar ∧ h'.sessions.length + (rem - 1) ≤ q))) := by
            refine Or.inr ⟨hnw, ?_⟩
            rcases hlen_bound with ⟨ht0, hle1, _⟩ | ⟨htpos, _⟩
            · exact Or.inl ⟨ht0, by rw [h0 ht0]; exact hle1, by omega⟩
            · exact Or.inr ⟨htpos, by omega⟩
          have hc' : ∀ Tc σ k idx?, h'.cache mo.tStar = some (Tc, σ, k, idx?) →
              ∃ idx, idx < h'.sessions.length ∧ idx? = some idx := by
            intro Tc σ k idx? hc; rw [hcache'] at hc
            obtain ⟨idx, hlt, heq⟩ := hS.cache_idx Tc σ k idx? hc
            exact ⟨idx, lt_of_lt_of_le hlt hl1, heq⟩
          cases res_vr with
          | none =>
            simp only [abortE, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
            subst hr2
            exact ⟨fun Q rsv hq => let ⟨i, h1, h2⟩ := hS.vR_idx Q rsv hq
              ⟨i, lt_of_lt_of_le h1 hl1, h2⟩, hc', hbound'⟩
          | some res_vr' =>
            cases res_vr' with
            | none =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hr2
              subst hr2
              exact ⟨fun Q rsv hq => let ⟨i, h1, h2⟩ := hS.vR_idx Q rsv hq
                ⟨i, lt_of_lt_of_le h1 hl1, h2⟩, hc', hbound'⟩
            | some val =>
              rcases val with ⟨st', t', i', m'⟩
              obtain ⟨_, hvR_st', hlast_tStar⟩ := hvp' st' t' i' m' rfl
              simp only at hr2
              split at hr2
              · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hr2
                subst hr2
                exact ⟨fun Q rsv hq => let ⟨i, h1, h2⟩ := hS.vR_idx Q rsv hq
                  ⟨i, lt_of_lt_of_le h1 hl1, h2⟩, hc', hbound'⟩
              · split at hr2
                · simp only [commitE, hooksLocal, run_liftH, pure_bind, StateT.run_bind,
                    StateT.run_pure, StateT.run_modify, simulateQ_pure, support_pure,
                    Set.mem_singleton_iff] at hr2
                  subst hr2
                  refine ⟨fun Q rsv hq => ?_, hc', hbound'⟩
                  dsimp only [SM.GameState.accept, SM.GameState.delete] at hq
                  rw [Function.update_idem] at hq
                  exact hS.mono_sessions mo hl1 hvR_st' Q rsv hq
                · split at hr2
                  · rename_i ht'; simp only [beq_iff_eq] at ht'
                    simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
                    subst hr2
                    obtain ⟨idx, hidx_lt, hlast_eq⟩ := hlast_tStar ht'
                    have hidx_q : idx < q := by
                      rcases hlen_bound with ⟨ht0, hle1, _⟩ | ⟨_, _⟩
                      · rw [h0 ht0] at hidx_lt; omega
                      · omega
                    exact ⟨fun Q rsv hq => let ⟨i, h1, h2⟩ := hS.vR_idx Q rsv hq
                      ⟨i, lt_of_lt_of_le h1 hl1, h2⟩, hc', Or.inl ⟨rfl, ⟨idx, hidx_q, hlast_eq⟩⟩⟩
                  · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                      Set.mem_singleton_iff] at hr2
                    subst hr2
                    exact ⟨fun Q rsv hq => let ⟨i, h1, h2⟩ := hS.vR_idx Q rsv hq
                      ⟨i, lt_of_lt_of_le h1 hl1, h2⟩, hc', hbound'⟩
    · rw [stepLDFShiftedDir2Paper,
        implEDFShiftedPaper_corr_congr l (hooksLocal cka prng fs mo)
          (hooksLocal cka prng fs (moAuth mo)) rfl] at hr
      exact sessInv_moAuth.mp ((stepLDFShiftedPaper_sessInv cka prng fs Δcka qep l (moAuth mo) rfl
        (.inr (.inl (.inr P))) esL (sessInv_moAuth.mpr hS)).2 _ rfl hrem r hr)
    · simp only [stepLDFShiftedDir2Paper, implEDFShiftedB1,
        QueryImpl.add_apply, deliverForgeEB1, moAuth, Mode.cfg, ↓reduceIte, SM.Config.auth,
        StateT.run_bind, StateT.run_get, pure_bind] at hr
      split at hr
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact hS_noop
      · rename_i hnot_ab_win
        simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hnot_ab_win
        have hnw : esL.g.win = false := hnot_ab_win.2
        rcases hS.bound with ⟨hwin, _⟩ | ⟨_, hlen_bound⟩
        · rw [hwin] at hnw; cases hnw
        · split at hr
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact hS_noop
          · split at hr
            · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
              subst hr; exact hS_noop
            · simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind,
                MonadAttach.mem_support_bind] at hr
              rcases hr with ⟨⟨res_vr, h'⟩, hvr, hr2⟩
              obtain ⟨hl1, hl2, h0, hcache', hvp'⟩ :=
                mem_support_vRecv_local cka prng fs mo hvr (hS.vR_idx P) hS.cache_idx
              have hbound' :
                  (esL.g.win = true ∧ ∃ j, j < q ∧ h'.lastIdx = some j) ∨
                  (esL.g.win = false ∧
                    ((mo.tStar = 0 ∧ h'.sessions.length ≤ 1 ∧ rem - 1 ≤ q) ∨
                     (0 < mo.tStar ∧ h'.sessions.length + (rem - 1) ≤ q))) := by
                refine Or.inr ⟨hnw, ?_⟩
                rcases hlen_bound with ⟨ht0, hle1, _⟩ | ⟨htpos, _⟩
                · exact Or.inl ⟨ht0, by rw [h0 ht0]; exact hle1, by omega⟩
                · exact Or.inr ⟨htpos, by omega⟩
              have hc' : ∀ Tc σ k idx?, h'.cache mo.tStar = some (Tc, σ, k, idx?) →
                  ∃ idx, idx < h'.sessions.length ∧ idx? = some idx := by
                intro Tc σ k idx? hc; rw [hcache'] at hc
                obtain ⟨idx, hlt, heq⟩ := hS.cache_idx Tc σ k idx? hc
                exact ⟨idx, lt_of_lt_of_le hlt hl1, heq⟩
              have hvR' : ∀ Q rsv, (esL.g.st Q).vR mo.tStar = some rsv →
                  ∃ idx, idx < h'.sessions.length ∧ rsv.2 = some idx :=
                fun Q rsv hq =>
                  let ⟨i, h1, h2⟩ := hS.vR_idx Q rsv hq; ⟨i, lt_of_lt_of_le h1 hl1, h2⟩
              cases res_vr with
              | none =>
                simp only [abortE, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                  simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
                subst hr2; exact ⟨hvR', hc', hbound'⟩
              | some res_vr' =>
                cases res_vr' with
                | none =>
                  simp only [StateT.run_pure, simulateQ_pure, support_pure,
                    Set.mem_singleton_iff] at hr2
                  subst hr2; exact ⟨hvR', hc', hbound'⟩
                | some val =>
                  rcases val with ⟨st', t', i', m'⟩
                  obtain ⟨_, hvR_st', hlast_tStar⟩ := hvp' st' t' i' m' rfl
                  simp only at hr2
                  split at hr2
                  · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                      Set.mem_singleton_iff] at hr2
                    subst hr2; exact ⟨hvR', hc', hbound'⟩
                  · split at hr2
                    · simp only [commitE, hooksLocal, run_liftH, pure_bind, StateT.run_bind,
                        StateT.run_pure, StateT.run_modify, simulateQ_pure, support_pure,
                        Set.mem_singleton_iff] at hr2
                      subst hr2
                      refine ⟨fun Q rsv hq => ?_, hc', hbound'⟩
                      dsimp only [SM.GameState.accept, SM.GameState.delete] at hq
                      rw [Function.update_idem] at hq
                      exact hS.mono_sessions mo hl1 hvR_st' Q rsv hq
                    · split at hr2
                      · rename_i ht'; simp only [beq_iff_eq] at ht'
                        simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
                        subst hr2
                        obtain ⟨idx, hidx_lt, hlast_eq⟩ := hlast_tStar ht'
                        have hidx_q : idx < q := by
                          rcases hlen_bound with ⟨ht0, hle1, _⟩ | ⟨_, _⟩
                          · rw [h0 ht0] at hidx_lt; omega
                          · omega
                        exact ⟨hvR', hc', Or.inl ⟨rfl, ⟨idx, hidx_q, hlast_eq⟩⟩⟩
                      · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                          Set.mem_singleton_iff] at hr2
                        subst hr2; exact ⟨hvR', hc', hbound'⟩

theorem runLocDFShiftedDir2Paper_le_sum_runLocAtDFShiftedDir2Paper (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) {q rem : ℕ}
    {p : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain → Prop} [DecidablePred p]
    (hp_inl : ∀ t, ¬ p (.inl t)) (hp_inr : ∀ t, p (.inr t))
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool) (hq : oa.IsQueryBoundP p rem)
    (esL : EStateL Γ T Sig SS RS M E K I) (hS : SessInv mo q rem esL) :
    𝒟[runLocDFShiftedDir2Paper cka prng fs Δcka qep l mo oa esL] {true} ≤
      ∑ j ∈ Finset.range q,
        𝒟[runLocAtDFShiftedDir2Paper cka prng fs Δcka qep l mo j oa esL] {true} := by
  induction oa using OracleComp.inductionOn generalizing rem esL with
  | pure a =>
    simp only [runLocDFShiftedDir2Paper, runLocAtDFShiftedDir2Paper, simulateQ_pure,
      StateT.run_pure, pure_bind, evalDist_pure]
    by_cases hwin : authOut (2 + Δcka) (moAuth mo).policy esL = true
    · rw [hwin]; simp only [Bool.true_and]
      have hwin_g : esL.g.win = true := by
        unfold authOut at hwin; simp only [Bool.and_eq_true] at hwin; exact hwin.1.2
      rcases hS.bound with ⟨_, j, hj, hlast⟩ | ⟨hnw, _⟩
      · refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_range.mpr hj))
        simp [hlast]
      · rw [hwin_g] at hnw; cases hnw
    · simp [Bool.eq_false_iff.mpr hwin]
  | query_bind t r ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    dsimp only [runLocDFShiftedDir2Paper, runLocAtDFShiftedDir2Paper]
    rw [simulateQ_query_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind,
      simulateQ_bind, bind_assoc]
    change 𝒟[stepLDFShiftedDir2Paper cka prng fs Δcka qep l mo t esL >>= fun x =>
        runLocDFShiftedDir2Paper cka prng fs Δcka qep l mo (r x.1) x.2] {true} ≤
      ∑ j ∈ Finset.range q, 𝒟[stepLDFShiftedDir2Paper cka prng fs Δcka qep l mo t esL >>= fun x =>
        runLocAtDFShiftedDir2Paper cka prng fs Δcka qep l mo j (r x.1) x.2] {true}
    refine evalDist_bind_le_sum _ _ _ _ (fun x hx => ?_)
    have hstep := stepLDFShiftedDir2Paper_sessInv cka prng fs Δcka qep l mo t esL hS
    cases t with
    | inl c => exact ih x.1 (by simpa [hp_inl c] using hq.2 x.1) x.2 (hstep.1 c rfl x hx)
    | inr q_sm =>
      have hpos : 0 < rem := hq.1.resolve_left (not_not.mpr (hp_inr q_sm))
      exact ih x.1 (by simpa [hp_inr q_sm] using hq.2 x.1) x.2 (hstep.2 q_sm rfl hpos x hx)

theorem localAuthDFShiftedDir2Paper_le_sum_localAuthAtDFShiftedDir2Paper
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep l : ℕ) (tL : Option ℕ)
    (t q : ℕ) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) (hq : MakesAtMostQueriesDF A q) :
    𝒟[localAuthDFShiftedDir2Paper cka prng fs lam Δcka qep l tL t A] {true} ≤
      ∑ j ∈ Finset.range q,
        𝒟[localAuthAtDFShiftedDir2Paper cka prng fs lam Δcka qep j l tL t A] {true} := by
  rw [MakesAtMostQueriesDF] at hq
  dsimp only [localAuthDFShiftedDir2Paper, localAuthAtDFShiftedDir2Paper]
  refine evalDist_bind_le_sum
    (simulateQ lImpl ((initLocal cka prng fs lam ⟨false, tL, t⟩).run {})) q
    (fun x => match x.1 with
      | none => pure false
      | some (vA, vB) => runLocDFShiftedDir2Paper cka prng fs Δcka qep l ⟨false, tL, t⟩ A
          { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := x.2 })
    (fun j x => match x.1 with
      | none => pure false
      | some (vA, vB) => runLocAtDFShiftedDir2Paper cka prng fs Δcka qep l ⟨false, tL, t⟩ j A
          { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := x.2 })
    (fun x hx => ?_)
  rcases x with ⟨vs, h⟩; cases vs with
  | none => simp
  | some vAB =>
    rcases vAB with ⟨vA, vB⟩
    let mo : Mode := ⟨false, tL, t⟩
    have hS : SessInv mo q q
        ({ g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h } :
          EStateL Γ T Sig SS RS M E K I) := by
      simp only [initLocal, StateT.run_bind, simulateQ_bind, simulateQ_lImpl_run_lift_sampleT,
        MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨⟨kr, s1⟩, ⟨_, _, hs1⟩, ⟨kc, s2⟩, ⟨_, _, hs2⟩,
        ⟨⟨σ, k, sid⟩, s3⟩, hroot, ⟨idx?, s4⟩, hreg, hpure⟩
      injection hs1 with _ hs1; subst hs1; injection hs2 with _ hs2; subst hs2
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hpure
      injection hpure with hvAB hh; injection hvAB with hvAB; injection hvAB with hvA hvB
      subst hvA hvB hh
      obtain ⟨hl_r, hc_r, _, hsid_r1, hsid_r2⟩ := mem_support_rootL prng mo hroot
      obtain ⟨hnone_reg, hsome_reg⟩ := mem_support_regSessOf hreg
      refine ⟨?_, ?_, Or.inr ⟨rfl, ?_⟩⟩
      · intro P rsv hrsv; cases P <;> dsimp only [mkParties] at hrsv
        · split at hrsv
          · rename_i ht0; injection hrsv with hrsv; subst hrsv
            obtain ⟨I', hsid_some⟩ := hsid_r1 ht0.symm
            obtain ⟨⟨idx, hlt, heq⟩, _⟩ := hsome_reg I' hsid_some
            exact ⟨idx, hlt, heq⟩
          · cases hrsv
        · cases hrsv
      · intro Tc σ' k' idx' hc; rcases sid with _ | Ik
        · obtain ⟨_, hs4⟩ := hnone_reg rfl; rw [hs4, hc_r] at hc; cases hc
        · obtain ⟨_, _, _, hc_reg, _⟩ := hsome_reg Ik rfl; rw [hc_reg, hc_r] at hc; cases hc
      · by_cases ht0 : mo.tStar = 0
        · refine Or.inl ⟨ht0, ?_, le_rfl⟩
          obtain ⟨I', hsid_some⟩ := hsid_r1 ht0.symm
          obtain ⟨_, _, hl2, _, _⟩ := hsome_reg I' hsid_some
          have : h.sessions.length ≤ ({} : LState T Sig K I).sessions.length + 1 := by
            rw [← hl_r]; exact hl2
          exact this
        · obtain ⟨_, hs4⟩ := hnone_reg (hsid_r2 (Ne.symm ht0))
          have hlen0 : h.sessions.length = 0 := by rw [hs4, hl_r]; rfl
          exact Or.inr ⟨Nat.pos_of_ne_zero ht0, by rw [hlen0, Nat.zero_add]⟩
    exact runLocDFShiftedDir2Paper_le_sum_runLocAtDFShiftedDir2Paper cka prng fs Δcka qep l mo
      (fun _ => by simp) (fun _ => by simp) A hq _ hS

theorem stepLFixedDFShiftedDir2Paper_eq_of_lt (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep l : ℕ) (mo : Mode) {j : ℕ} (k_fs : K)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    {esL : EStateL Γ T Sig SS RS M E K I} (hlt : j < esL.h.sessions.length) :
    stepLFixedDFShiftedDir2Paper cka prng fs Δcka qep l mo j k_fs q esL =
      stepLDFShiftedDir2Paper cka prng fs Δcka qep l mo q esL := by
  rcases q with n | ((((q12 | q3) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
  · rw [stepLFixedDFShiftedDir2Paper_inl, stepLDFShiftedDir2Paper_inl]
    exact stepLFixedDFShiftedPaper_eq_of_lt cka prng fs Δcka qep l (moAuth mo) (j := j) k_fs
      (.inl n) hlt
  · rw [stepLFixedDFShiftedDir2Paper, stepLDFShiftedDir2Paper,
      implEDFShiftedPaper_q12_congr l (hooksLocalFixed cka prng fs mo j k_fs)
        (hooksLocalFixed cka prng fs (moAuth mo) j k_fs) rfl rfl,
      implEDFShiftedPaper_q12_congr l (hooksLocal cka prng fs mo)
        (hooksLocal cka prng fs (moAuth mo)) rfl rfl]
    exact stepLFixedDFShiftedPaper_eq_of_lt cka prng fs Δcka qep l (moAuth mo) (j := j) k_fs
      (.inr (.inl (.inl (.inl (.inl q12))))) hlt
  · rw [stepLFixedDFShiftedDir2Paper, stepLDFShiftedDir2Paper,
      implEDFShiftedPaper_q3_moAuth, implEDFShiftedPaper_q3_moAuth]
    exact stepLFixed_eq_of_lt cka prng fs Δcka qep mo k_fs (.inr (.inl (.inl (.inr q3)))) hlt
  · simp only [stepLFixedDFShiftedDir2Paper, stepLDFShiftedDir2Paper, implEDFShiftedB1,
      QueryImpl.add_apply, injectEB1, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · rfl
    · simp only [StateT.run_bind, run_liftH,
        vRecv_fixed_eq_of_lt cka prng fs mo k_fs esL.g P (esL.g.st P) c none hlt]
      rfl
  · rw [stepLFixedDFShiftedDir2Paper, stepLDFShiftedDir2Paper,
      implEDFShiftedPaper_corr_congr l (hooksLocalFixed cka prng fs mo j k_fs)
        (hooksLocalFixed cka prng fs (moAuth mo) j k_fs) rfl,
      implEDFShiftedPaper_corr_congr l (hooksLocal cka prng fs mo)
        (hooksLocal cka prng fs (moAuth mo)) rfl]
    exact stepLFixedDFShiftedPaper_eq_of_lt cka prng fs Δcka qep l (moAuth mo) (j := j) k_fs
      (.inr (.inl (.inr P))) hlt
  · simp only [stepLFixedDFShiftedDir2Paper, stepLDFShiftedDir2Paper, implEDFShiftedB1,
      QueryImpl.add_apply, deliverForgeEB1, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · simp only [StateT.run_bind, run_liftH,
            vRecv_fixed_eq_of_lt cka prng fs mo k_fs esL.g P (esL.g.st P) c' none hlt]
          rfl

theorem mem_support_stepLDFShiftedDir2Paper_sessions_le (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I)
    {r : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q × EStateL Γ T Sig SS RS M E K I}
    (hr : r ∈ support (stepLDFShiftedDir2Paper cka prng fs Δcka qep l mo q esL)) :
    esL.h.sessions.length ≤ r.2.h.sessions.length := by
  rcases q with n | ((((q12 | q3) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
  · rw [stepLDFShiftedDir2Paper_inl] at hr
    exact mem_support_stepLDFShiftedPaper_sessions_le cka prng fs Δcka qep l (moAuth mo)
      (.inl n) esL hr
  · rw [stepLDFShiftedDir2Paper,
      implEDFShiftedPaper_q12_congr l (hooksLocal cka prng fs mo)
        (hooksLocal cka prng fs (moAuth mo)) rfl rfl] at hr
    exact mem_support_stepLDFShiftedPaper_sessions_le cka prng fs Δcka qep l (moAuth mo)
      (.inr (.inl (.inl (.inl (.inl q12))))) esL hr
  · rw [stepLDFShiftedDir2Paper, implEDFShiftedPaper_q3_moAuth] at hr
    exact mem_support_stepL_sessions_le cka prng fs Δcka qep mo (.inr (.inl (.inl (.inr q3))))
      esL hr
  · simp only [stepLDFShiftedDir2Paper, implEDFShiftedB1,
      QueryImpl.add_apply, injectEB1, StateT.run_bind, StateT.run_get, pure_bind] at hr
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
          simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
          subst hr2; exact hl
        | some val =>
          rcases val with ⟨st', t', i', m'⟩; simp only at hr2
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
  · rw [stepLDFShiftedDir2Paper,
      implEDFShiftedPaper_corr_congr l (hooksLocal cka prng fs mo)
        (hooksLocal cka prng fs (moAuth mo)) rfl] at hr
    exact mem_support_stepLDFShiftedPaper_sessions_le cka prng fs Δcka qep l (moAuth mo)
      (.inr (.inl (.inr P))) esL hr
  · simp only [stepLDFShiftedDir2Paper, implEDFShiftedB1,
      QueryImpl.add_apply, deliverForgeEB1, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact le_rfl
    · split at hr
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
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hr2
              subst hr2; exact hl
            | some val =>
              rcases val with ⟨st', t', i', m'⟩; simp only at hr2
              split at hr2
              · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hr2
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

theorem evalDist_runLocAtDFShiftedDir2Paper_eq_fixed_of_lt (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) {j : ℕ} (k_fs : K) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esL : EStateL Γ T Sig SS RS M E K I} (hlt : j < esL.h.sessions.length) :
    𝒟[runLocAtDFShiftedDir2Paper cka prng fs Δcka qep l mo j oa esL] {true} =
      𝒟[runLocAtFixedDFShiftedDir2Paper cka prng fs Δcka qep l mo j k_fs oa esL] {true} := by
  induction oa using OracleComp.inductionOn generalizing esL with
  | pure b' => rw [runLocAtDFShiftedDir2Paper_pure, runLocAtFixedDFShiftedDir2Paper_pure]
  | query_bind q k ih =>
    rw [runLocAtDFShiftedDir2Paper_query_bind, runLocAtFixedDFShiftedDir2Paper_query_bind,
      stepLFixedDFShiftedDir2Paper_eq_of_lt cka prng fs Δcka qep l mo k_fs q hlt]
    refine evalDist_bind_congr_true _ _ _ fun r hr => ih r.1 (lt_of_lt_of_le hlt
      (mem_support_stepLDFShiftedDir2Paper_sessions_le cka prng fs Δcka qep l mo q esL hr))

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I] in
theorem shiftLe_moAuth {α : Type} {mo : Mode} {j : ℕ} {getH : α → LState T Sig K I} :
    ShiftLe (moAuth mo) j getH = ShiftLe mo j getH := rfl

end AuthL11ShiftedDir2Paper
end CryptoGames.SM.Construction.DeliverForge
