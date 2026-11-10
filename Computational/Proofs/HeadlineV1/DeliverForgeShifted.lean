/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma9 -- shake: keep
public import Computational.Proofs.HeadlineV1.HiddenSaltV1
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeFS
public import Computational.Proofs.HeadlineV1.DeliverForgeDir2
public import Computational.Proofs.HeadlineV1.SendShortC
public import Computational.Proofs.HeadlineV1.SignedRefineC
import Computational.Proofs.SpqrV1Sync.SendTotal
import ProofLib.SepLogic.WP.StateNorm
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.StateInv -- shake: keep

/-!
# Shifted-Cell `DeliverForge` CKA Reduction

**Checked by Lean.** Defines the shifted-heal CKA reduction hooks (`hooksCKAShifted`,
`initCKAShifted`) and own-epoch leak transition (`afterCorrShifted`, `implEDFShifted`) at
challenge epoch `t_CKA = l + 1` with `Δ_CKA = 1`, proves step preservation of `Sync9Shifted` and
`DoomedAuthShifted`, and establishes `LeakCorrInv` and `spqrCLocal_and_topState_v1`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Construction.DeliverForge

open CryptoGames.SM CryptoGames.SM.Engine CryptoGames.SM.Construction.AuthL9

/-! ## Shifted-heal CKA hooks -/

section RedCKAShifted

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

/-- Bookkeeping state for `hooksCKAShifted`, extending `CKAState T I` with eagerly cached
pre-challenge CKA states `γPre`. -/
structure CKAStateShifted (Γ T I : Type) where
  base : CKAState T I := {}
  γPre : Party → Option Γ := fun _ => none

local notation "CSpec" => CKA.spec Γ CCoins T I
local notation "CHMShifted" => HM CSpec (CKAStateShifted Γ T I)

def liftCShifted {α : Type} (x : CKA.AdversaryComp Γ CCoins T I α) : CHMShifted α :=
  StateT.lift x

def cacheCShifted (t : ℕ) (x : T × I) : CHMShifted Unit :=
  modify fun s =>
    { s with base := { s.base with cache := Function.update s.base.cache t (some x) } }

def setγPreShifted (P : Party) (γ? : Option Γ) : CHMShifted Unit :=
  modify fun s => { s with γPre := Function.update s.γPre P γ? }

/-- Shifted CKA hooks at challenge epoch `l + 1` (`Δ_CKA = 1`), eagerly caching `CKA.corrQuery` in
`γPre` for `t ≤ l - 1` and populating `vp.γ` for `t ≥ l + 2`. -/
def hooksCKAShifted (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (l tStar : ℕ) :
    Hooks CSpec (CKAStateShifted Γ T I) Γ T Sig SS RS M E CCoins (Option Γ) Sig SS RS where
  startSend _ P t γv σ r := do
    match γv with
    | some γ =>
      let coins ← match r with
        | some c => pure c
        | none => StateT.lift (sampleT CCoins)
      let c := cka.send γ coins
      cacheCShifted t (c.2.1, c.2.2)
      let p := prng.up σ c.2.2
      return some (some c.1, c.2.1, p.1, fs.initSender p.2)
    | none =>
      let ans ← match r with
        | some c => liftCShifted (CKA.sendWithAdversaryCoinsQuery P c)
        | none =>
          if t = l + 1 then liftCShifted (CKA.challQuery P) else liftCShifted (CKA.sendQuery P)
      match ans with
      | none => return none
      | some (T', Ik) =>
        cacheCShifted t (T', Ik)
        let p := prng.up σ Ik
        if l + 2 ≤ t then
          match ← liftCShifted (CKA.corrQuery P) with
          | none => return none
          | some γ => return some (some γ, T', p.1, fs.initSender p.2)
        else if t + 1 ≤ l then
          match ← liftCShifted (CKA.corrQuery P) with
          | none => return none
          | some γ =>
            setγPreShifted P (some γ)
            return some (none, T', p.1, fs.initSender p.2)
        else
          return some (none, T', p.1, fs.initSender p.2)
  startRecv _ _ t γv σ Tn := do
    let honest := match (← get).base.cache t with
      | some (Tc, Ik) => if Tc = Tn then some Ik else none
      | none => none
    match honest with
    | some Ik =>
      let p := prng.up σ Ik
      return some (some (γv.map fun γ => (cka.receive γ Tn).1, p.1, fs.initReceiver p.2))
    | none =>
      if t = tStar then
        match γv with
        | some γ =>
          let k := cka.receive γ Tn
          let p := prng.up σ k.2
          return some (some (some k.1, p.1, fs.initReceiver p.2))
        | none => return none
      else return some none
  fsSend _ _ _ ss h m _ := pure (some (fs.send ss h m))
  fsRecv _ _ _ rs h e _ := pure (some (fs.receive rs h e))
  commit _ P old new := do
    if old.tcur < new.tcur && old.γ.isNone then
      match ← liftCShifted (CKA.receiveQuery P) with
      | none => return none
      | some () =>
        if l + 2 ≤ new.tcur then
          match ← liftCShifted (CKA.corrQuery P) with
          | none => return none
          | some γ => return some { new with γ := some γ }
        else if new.tcur + 1 ≤ l then
          match ← liftCShifted (CKA.corrQuery P) with
          | none => return none
          | some γ =>
            setγPreShifted P (some γ)
            return some new
        else
          return some new
    else return some new
  reveal _ P vp := do
    let γ? ← match vp.γ with
      | some γ => pure (some γ)
      | none =>
        if vp.tcur + 1 ≤ l then pure ((← get).γPre P)
        else liftCShifted (CKA.corrQuery P)
    match γ? with
    | none => return none
    | some γ => return some (realParty vp γ vp.root vp.vS vp.vR)

/-- Initializer for `hooksCKAShifted`, eagerly populating `γPre` at epoch `0` when `1 ≤ l`. -/
def initCKAShifted (_cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (l : ℕ) :
    CHMShifted (Option (PartyState (Option Γ) T Sig SS RS × PartyState (Option Γ) T Sig SS RS)) :=
  do
  let kr ← StateT.lift (sampleT KR)
  let out := prng.up (prng.init kr) lam
  let _ ← liftCShifted (pure () : CKA.AdversaryComp Γ CCoins T I Unit)
  if 1 ≤ l then
    let γA? ← liftCShifted (CKA.corrQuery (State := Γ) (Coins := CCoins) (Msg := T) (CKey := I) .A)
    let γB? ← liftCShifted (CKA.corrQuery (State := Γ) (Coins := CCoins) (Msg := T) (CKey := I) .B)
    setγPreShifted .A γA?
    setγPreShifted .B γB?
  return some (mkParties (T := T) none none out.1 (fs.initSender out.2) (fs.initReceiver out.2))

/-- Own-epoch leak transition at boundary `l`, recording the leak at `s.epoch P` instead of
`max (s.epoch .A) (s.epoch .B)` when `P` lags below `l`. -/
def afterCorrShifted {St Msg C : Type} (l : ℕ) (s : GameState St Msg C) (P : Party) :
    GameState St Msg C :=
  let s₁ : GameState St Msg C :=
    { s with comp := (s.trans.filter (fun r : Record Msg C => r.pos.sender == P.other)).map
                       (fun r : Record Msg C => r.pos) ++ s.comp }
  let e_leak :=
    if max (s.epoch .A) (s.epoch .B) = l ∧ s.epoch P + 1 ≤ l then l - 1
    else max (s.epoch .A) (s.epoch .B)
  { s₁.leak e_leak with corrs := (P, s.epoch P) :: s.corrs }

def corrEShifted {ι : Type} {tspec : OracleSpec.{0, 0} ι} {HS Γv Sv SSv RSv : Type}
    (l : ℕ) (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv) (π : Policy) :
    QueryImpl (Party →ₒ Option (PartyState Γ T Sig SS RS))
      (EM tspec Γv T Sv SSv RSv M E HS) := fun P => do
  let es ← get
  if es.abort || es.g.win || !(es.g.corrAllowed P) then return none
  let s₁ := afterCorrShifted l es.g P
  if π.leakDoom es.g s₁ || π.corrDoom es.g P then
    abortE
    return none
  match ← liftH (hk.reveal es.g P (es.g.st P)) with
  | none =>
    abortE
    return none
  | some st =>
    modify fun es => { es with g := s₁ }
    return some st

def implEShifted {ι : Type} {tspec : OracleSpec.{0, 0} ι} {HS Γv Sv SSv RSv : Type}
    (l : ℕ) (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy) :
    QueryImpl (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (EM tspec Γv T Sv SSv RSv M E HS) :=
  let i₀ : QueryImpl unifSpec (EM tspec Γv T Sv SSv RSv M E HS) := coinsE
  let i₁ :=
    HAdd.hAdd
      (HAdd.hAdd
        (HAdd.hAdd
          (HAdd.hAdd (transmitE hk Δ qep π) (challE hk Δ qep cfg π))
          (deliverE hk maxSkip cfg))
        (injectE hk Δ qep cfg))
      (corrEShifted l hk π)
  HAdd.hAdd i₀ i₁

def implEDFShifted {ι : Type} {tspec : OracleSpec.{0, 0} ι} {HS Γv Sv SSv RSv : Type}
    (l : ℕ) (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy) :
    QueryImpl (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (EM tspec Γv T Sv SSv RSv M E HS) :=
  let i₀ : QueryImpl unifSpec (EM tspec Γv T Sv SSv RSv M E HS) := coinsE
  let i₁ : QueryImpl (spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (EM tspec Γv T Sv SSv RSv M E HS) :=
    HAdd.hAdd
      (HAdd.hAdd
        (HAdd.hAdd
          (HAdd.hAdd (transmitE hk Δ qep π) (challE hk Δ qep cfg π))
          (deliverE hk maxSkip cfg))
        (injectE hk Δ qep cfg))
      (corrEShifted l hk π)
  let i₂ : QueryImpl ((Party × (Header T × E) × (Header T × E)) →ₒ Option (RecvResult M))
      (EM tspec Γv T Sv SSv RSv M E HS) :=
    deliverForgeE hk Δ qep cfg
  HAdd.hAdd i₀ (HAdd.hAdd i₁ i₂)

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem allowCorr_initState_of_one_le (cka : CKAScheme KC Γ CCoins T I) (kc : KC) (b : Bool)
    {l : ℕ} (hl : 1 ≤ l) :
    (CKA.initState cka kc b).allowCorr (l + 1) = true := by
  unfold CKA.GameState.allowCorr CKA.initState
  dsimp only
  rw [decide_eq_true_eq]
  omega

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem allowCorr_afterSend_of_le {sc : CKA.GameState Γ T} {P : Party} (γ' : Γ) (T' : T)
    {l : ℕ} (heq : sc.epoch P = sc.epoch P.other) (hle : (sc.epoch P + 1) + 1 ≤ l) :
    (sc.afterSend P γ' T').allowCorr (l + 1) = true := by
  unfold CKA.GameState.allowCorr CKA.GameState.afterSend
  dsimp only
  rw [decide_eq_true_eq]
  cases P <;> simp [Party.other, Function.update] at heq ⊢ <;> omega

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem allowCorr_afterReceive_of_le {sc : CKA.GameState Γ T} {P : Party} (γ' : Γ)
    {l : ℕ} (heq : sc.epoch P + 1 = sc.epoch P.other) (hle : (sc.epoch P + 1) + 1 ≤ l) :
    (sc.afterReceive P γ').allowCorr (l + 1) = true := by
  unfold CKA.GameState.allowCorr CKA.GameState.afterReceive
  dsimp only
  rw [decide_eq_true_eq]
  cases P <;> simp [Party.other, Function.update] at heq ⊢ <;> omega

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem finished_afterSend_of_ge {sc : CKA.GameState Γ T} {P : Party} (γ' : Γ) (T' : T)
    {l : ℕ} (hge : l + 2 ≤ sc.epoch P + 1) :
    (sc.afterSend P γ' T').finished 1 (l + 1) P = true := by
  unfold CKA.GameState.finished CKA.GameState.afterSend
  simp only [Function.update_self, decide_eq_true_eq]
  omega

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem finished_afterReceive_of_ge {sc : CKA.GameState Γ T} {P : Party} (γ' : Γ)
    {l : ℕ} (hge : l + 2 ≤ sc.epoch P + 1) :
    (sc.afterReceive P γ').finished 1 (l + 1) P = true := by
  unfold CKA.GameState.finished CKA.GameState.afterReceive
  simp only [Function.update_self, decide_eq_true_eq]
  omega

/-! ## Synchronization invariant -/

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem validGuess_three_sub_one_eq_validGuess_two {l tStar : ℕ} (hl : 1 ≤ l) :
    lastLeakGuessAdmissible (2 + 1) (some (l - 1)) tStar = lastLeakGuessAdmissible 2 (some l) tStar := by
  simp only [lastLeakGuessAdmissible, healedBy, decide_eq_decide]
  omega

/-- Synchronization invariant for `hooksCKAShifted` at `t_CKA = l + 1`, pairing
`Sync9 cka 1 (some (l - 1)) tStar` with the `γPre` cache invariant. -/
structure Sync9Shifted (cka : CKAScheme KC Γ CCoins T I) (l tStar : ℕ)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E))
    (esS : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I))
    (sc : CKA.GameState Γ T) : Prop where
  hl : 1 ≤ l
  baseSync : AuthL9.Sync9 cka 1 (some (l - 1)) tStar s
    { g := esS.g, h := esS.h.base, abort := esS.abort } sc
  γPre_eq : ∀ P, esS.g.epoch P + 1 ≤ l → esS.h.γPre P = some (s.st P).γ

theorem sync9Shifted_init (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) {l tStar : ℕ}
    (hc : cka.Correct) (hl : 1 ≤ l) (hvg : lastLeakGuessAdmissible 2 (some l) tStar = true)
    (kr : KR) (kc : KC) :
    let out := prng.up (prng.init kr) lam
    let vp := mkParties (T := T) none none out.1 (fs.initSender out.2) (fs.initReceiver out.2)
    let g₀ : Ctx (Option Γ) T Sig SS RS M E :=
      { st := fun P => match P with | .A => vp.1 | .B => vp.2, b := false }
    let h₀ : CKAStateShifted Γ T I :=
      { base := {}
        γPre := fun P => match P with | .A => some (cka.initA kc) | .B => some (cka.initB kc) }
    Sync9Shifted cka l tStar
      (initState (scheme cka prng fs lam) (kr, kc) false)
      { g := g₀, h := h₀ }
      (CKA.initState cka kc false) := by
  intro out vp g₀ h₀
  have hvg' : lastLeakGuessAdmissible (2 + 1) (some (l - 1)) tStar = true := by
    rwa [validGuess_three_sub_one_eq_validGuess_two hl]
  refine ⟨hl, AuthL9.Sync9.sync9_init prng fs lam hc hvg' kr kc, ?_⟩
  intro P _
  cases P <;> rfl

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
def HasUncompTransAt {St Msg C : Type} (l : ℕ) (s : GameState St Msg C) : Prop :=
  healedBy s.tL (2 + 1) (l - 1) = true ∧
    ∃ r ∈ s.trans, r.pos.epoch = l ∧ s.epoch r.pos.sender = l ∧ r.pos ∉ s.comp

/-- Shifted-cell Condition 4 refining `Doomed4 (some (l - 1))` with `HasUncompTransAt l s` when
epochs straddle `l`. -/
def Doomed4Shifted {St Msg C : Type} (l tStar : ℕ) (s : GameState St Msg C) : Prop :=
  1 ≤ l ∧ l < tStar ∧ l - 1 ∉ s.leaks ∧
    l - 1 ≤ min (s.epoch .A) (s.epoch .B) ∧
    l - 1 < max (s.epoch .A) (s.epoch .B) ∧
    (min (s.epoch .A) (s.epoch .B) < l ∧ max (s.epoch .A) (s.epoch .B) = l →
      HasUncompTransAt l s)

def DoomedAuthShifted {St Msg C : Type} (l tStar : ℕ) (s : GameState St Msg C) : Prop :=
  Doomed1 (some (l - 1)) tStar s ∨ Doomed2 tStar s ∨
    Doomed3 (some (l - 1)) tStar s ∨ Doomed4Shifted l tStar s

theorem doomedAuthShifted_imp_doomedAuth {St Msg C : Type} {l tStar : ℕ}
    {s : GameState St Msg C} (hd : DoomedAuthShifted l tStar s) :
    DoomedAuth (some (l - 1)) tStar s := by
  rcases hd with h1 | h2 | h3 | ⟨_, _, hnl, hmin, hmax, _⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr ⟨l - 1, rfl, hnl, hmin, hmax⟩))

theorem doomedAuthShifted_not_win {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (Δ l tStar : ℕ) (s : GameState St Msg C) (hd : DoomedAuthShifted l tStar s) :
    (s.win && authLosingConditionsAvoided Δ (some (l - 1)) tStar s) = false :=
  doomedAuth_not_win Δ (some (l - 1)) tStar s (doomedAuthShifted_imp_doomedAuth hd)

theorem afterCorrShifted_eq_afterCorr_of_not {St Msg C : Type} (l : ℕ)
    (s : GameState St Msg C) (P : Party)
    (h : ¬(max (s.epoch .A) (s.epoch .B) = l ∧ s.epoch P + 1 ≤ l)) :
    afterCorrShifted l s P = s.afterCorr P := by
  simp only [afterCorrShifted, GameState.afterCorr, h, ↓reduceIte]

local notation "ASpecDF" =>
  unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)

theorem sync9Shifted_win {cka : CKAScheme KC Γ CCoins T I} {l tStar : ℕ}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9Shifted cka l tStar s es sc) (w : Bool) :
    Sync9Shifted cka l tStar
      { s with win := w }
      { es with g := { es.g with win := w } }
      sc :=
  ⟨hs.hl, hs.baseSync.sync9_win w, hs.γPre_eq⟩

theorem sync9Shifted_accept_same {cka : CKAScheme KC Γ CCoins T I} {l tStar : ℕ}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9Shifted cka l tStar s es sc) {P : Party}
    (vR' : ℕ → Option RS) {pos : Pos} (hpos_le : pos.epoch ≤ es.g.epoch P) :
    let st_v' := { es.g.st P with vR := vR' }
    let st_r' := { s.st P with vR := vR' }
    Sync9Shifted cka l tStar
      (s.accept P st_r' pos)
      { es with g := es.g.accept P st_v' pos }
      sc := by
  intro st_v' st_r'
  refine ⟨hs.hl, hs.baseSync.sync9_accept_same vR' hpos_le, fun Q hQ => ?_⟩
  simp only [GameState.accept, GameState.delete] at hQ
  have hQ' : es.g.epoch Q + 1 ≤ l := by
    by_cases hQP : Q = P
    · subst Q; simp [Function.update, Nat.max_eq_left hpos_le] at hQ; exact hQ
    · simp [Function.update_of_ne hQP] at hQ; exact hQ
  have hγ : ((s.accept P st_r' pos).st Q).γ = (s.st Q).γ := by
    by_cases hQP : Q = P
    · subst Q; simp [GameState.accept, GameState.delete, Function.update, st_r']
    · simp [GameState.accept, GameState.delete, Function.update_of_ne hQP]
  rw [hγ]
  exact hs.γPre_eq Q hQ'

theorem sync9Shifted_accept_new {cka : CKAScheme KC Γ CCoins T I} {l tStar : ℕ}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9Shifted cka l tStar s es sc) {P : Party}
    (σ' : Sig) (vR' : ℕ → Option RS) {pos : Pos}
    (ht : pos.epoch = es.g.epoch P + 1)
    (heq_other : es.g.epoch P + 1 = es.g.epoch P.other)
    (hnsend : P.sendsIn pos.epoch = false)
    (T_t : T)
    (hagr_step : ∀ rs, cka.AgreesFrom (cka.receive (s.st P).γ T_t).1 (s.st P.other).γ rs) :
    let t := pos.epoch
    let γ_r' := (cka.receive (s.st P).γ T_t).1
    let γ_v' : Option Γ := if AuthL9.isLocal (some (l - 1)) 1 t then some γ_r' else none
    let st_v' : PartyState (Option Γ) T Sig SS RS :=
      { es.g.st P with tcur := t, γ := γ_v', root := σ', vR := vR' }
    let st_r' : PartyState Γ T Sig SS RS :=
      { s.st P with tcur := t, γ := γ_r', root := σ', vR := vR' }
    let h' : CKAStateShifted Γ T I :=
      if t + 1 ≤ l then { es.h with γPre := Function.update es.h.γPre P (some γ_r') } else es.h
    let sc' : CKA.GameState Γ T :=
      if AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P) then sc else sc.afterReceive P γ_r'
    Sync9Shifted cka l tStar
      (s.accept P st_r' pos)
      { es with g := es.g.accept P st_v' pos, h := h' }
      sc' := by
  intro t γ_r' γ_v' st_v' st_r' h' sc'
  have hbase_eq : h'.base = es.h.base := by dsimp only [h']; split_ifs <;> rfl
  refine ⟨hs.hl, ?_, fun Q hQ => ?_⟩
  · rw [hbase_eq]
    exact hs.baseSync.sync9_accept_new σ' vR' ht heq_other hnsend T_t hagr_step
  · have hepQ : (es.g.accept P st_v' pos).epoch Q = t := by
      simp only [GameState.accept, GameState.delete]
      by_cases hQP : Q = P
      · subst Q; simp [Function.update, t, ht]
      · have hQo : Q = P.other := by cases P <;> cases Q <;> first | contradiction | rfl
        subst Q; simp [Function.update_of_ne hQP, t, ← heq_other, ht]
    rw [hepQ] at hQ
    dsimp only [h']
    simp only [hQ, ↓reduceIte]
    by_cases hQP : Q = P
    · subst Q; simp [GameState.accept, GameState.delete, Function.update, st_r']
    · have hQo : Q = P.other := by cases P <;> cases Q <;> first | contradiction | rfl
      subst Q
      simp only [GameState.accept, GameState.delete, Function.update_of_ne hQP]
      exact hs.γPre_eq P.other (by omega)

theorem sync9Shifted_send_same {cka : CKAScheme KC Γ CCoins T I} {l tStar : ℕ}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9Shifted cka l tStar s es sc) {P : Party}
    (hnsend : P.sendsIn (es.g.epoch P + 1) = false) (vS' : Option SS) (m : M) (e : E)
    (isChall : Bool) :
    let h : Header T := (es.g.epoch P, (es.g.st P).curCkaMsg)
    let st_v' := { es.g.st P with vS := vS' }
    let st_r' := { s.st P with vS := vS' }
    let rec_P : Record M (Header T × E) := ⟨⟨P, es.g.epoch P, es.g.idx P + 1⟩, m, (h, e)⟩
    Sync9Shifted cka l tStar
      (s.record (2 + 1) P st_r' rec_P isChall)
      { es with g := es.g.record (2 + 1) P st_v' rec_P isChall }
      sc := by
  intro h st_v' st_r' rec_P
  refine ⟨hs.hl, hs.baseSync.sync9_send_same hnsend vS' m e isChall, fun Q hQ => ?_⟩
  have hγ : ((s.record (2 + 1) P st_r' rec_P isChall).st Q).γ = (s.st Q).γ := by
    by_cases hQP : Q = P
    · subst Q; simp [GameState.record, Function.update, st_r']
    · simp [GameState.record, Function.update_of_ne hQP]
  rw [hγ]
  exact hs.γPre_eq Q hQ

theorem sync9Shifted_send_new (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {cka : CKAScheme KC Γ CCoins T I} {l tStar : ℕ}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9Shifted cka l tStar s es sc) {qep : ℕ} {P : Party} {bad : Bool}
    (hsend : P.sendsIn (es.g.epoch P + 1) = true)
    {s₁ : GameState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)}
    (hep : es.g.epMgmt (2 + 1) qep P bad = some s₁)
    (coins : CCoins) (m : M) (isChall : Bool) :
    let t := es.g.epoch P + 1
    let c_cka := cka.send (s.st P).γ coins
    let p := prng.up (es.g.st P).root c_cka.2.2
    let ss := fs.initSender p.2
    let h : Header T := (t, some c_cka.2.1)
    let out_fs := fs.send ss h m
    let γv' : Option Γ := if AuthL9.isLocal (some (l - 1)) 1 t then some c_cka.1 else none
    let st_v' : PartyState (Option Γ) T Sig SS RS :=
      { es.g.st P with
        tcur := t, γ := γv', curCkaMsg := some c_cka.2.1, root := p.1, vS := some out_fs.1 }
    let st_r' : PartyState Γ T Sig SS RS :=
      { s.st P with
        tcur := t, γ := c_cka.1, curCkaMsg := some c_cka.2.1, root := p.1, vS := some out_fs.1 }
    let rec_P : Record M (Header T × E) := ⟨⟨P, t, 1⟩, m, (h, out_fs.2)⟩
    let h' : CKAStateShifted Γ T I :=
      { base := { cache := Function.update es.h.base.cache t (some (c_cka.2.1, c_cka.2.2)) }
        γPre := if t + 1 ≤ l then Function.update es.h.γPre P (some c_cka.1) else es.h.γPre }
    let sc' : CKA.GameState Γ T :=
      if AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P) then sc
      else sc.afterSend P c_cka.1 c_cka.2.1
    Sync9Shifted cka l tStar
      ((AuthL9.realGS sc s₁).record (2 + 1) P st_r' rec_P isChall)
      { es with g := s₁.record (2 + 1) P st_v' rec_P isChall, h := h' }
      sc' := by
  intro t c_cka p ss h out_fs γv' st_v' st_r' rec_P h' sc'
  have hq : ¬qep < es.g.epoch P + 1 := by intro hq; simp [GameState.epMgmt, hsend, hq] at hep
  have hs₁_epoch : s₁.epoch = Function.update es.g.epoch P t := by
    by_cases h3 : (bad && !(es.g.safeCh (2 + 1) P)) = true
    · simp only [GameState.epMgmt, hsend, hq, h3, ↓reduceIte, Option.some.injEq] at hep
      subst hep; rfl
    · simp only [Bool.not_eq_true] at h3
      simp [GameState.epMgmt, hsend, hq, h3] at hep
      subst hep; rfl
  have hs₁_st : s₁.st = es.g.st := by
    by_cases h3 : (bad && !(es.g.safeCh (2 + 1) P)) = true
    · simp only [GameState.epMgmt, hsend, hq, h3, ↓reduceIte, Option.some.injEq] at hep
      subst hep; rfl
    · simp only [Bool.not_eq_true] at h3
      simp [GameState.epMgmt, hsend, hq, h3] at hep
      subst hep; rfl
  refine ⟨hs.hl, hs.baseSync.sync9_send_new prng fs hsend hep coins m isChall, fun Q hQ => ?_⟩
  simp only [GameState.record, hs₁_epoch] at hQ ⊢
  by_cases hQP : Q = P
  · subst Q
    simp only [Function.update_self] at hQ
    simp [h', hQ, Function.update, st_r']
  · simp only [Function.update_of_ne hQP] at hQ
    have hγQ : (Function.update (AuthL9.realGS sc s₁).st P st_r' Q).γ = (s.st Q).γ := by
      simp [Function.update_of_ne hQP, hs.baseSync.s_eq, AuthL9.realGS, hs₁_st]
    rw [hγQ]
    dsimp only [h']
    split_ifs <;> simp [Function.update_of_ne hQP, hs.γPre_eq Q hQ]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KC] [SampleableType CCoins] [SampleableType I] in
theorem sync9Shifted_corr {cka : CKAScheme KC Γ CCoins T I} {l tStar : ℕ}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9Shifted cka l tStar s es sc) (P : Party) :
    Sync9Shifted cka l tStar
      (afterCorrShifted l s P)
      { es with g := afterCorrShifted l es.g P }
      sc := by
  refine ⟨hs.hl, ?_, hs.γPre_eq⟩
  refine
    { valid := hs.baseSync.valid
      s_eq := by rw [hs.baseSync.s_eq]; rfl
      no_abort := hs.baseSync.no_abort
      b_eq := hs.baseSync.b_eq
      sc_b := hs.baseSync.sc_b
      st_id := hs.baseSync.st_id
      st_tcur := hs.baseSync.st_tcur
      γ_eq := hs.baseSync.γ_eq
      sc_epoch := hs.baseSync.sc_epoch
      tL_none := by simp [afterCorrShifted, GameState.leak]
      tL_some := ?_
      leaks_ub := ?_
      comp_unhealed := ?_
      epoch_le := hs.baseSync.epoch_le
      epoch_step_sends := hs.baseSync.epoch_step_sends
      trans_inv := hs.baseSync.trans_inv
      cache_gt := hs.baseSync.cache_gt
      cka_eq := hs.baseSync.cka_eq
      cka_step := hs.baseSync.cka_step }
  · intro m hm
    simp only [afterCorrShifted, GameState.leak, Option.some.injEq] at hm
    subst hm
    refine ⟨by simp [afterCorrShifted, GameState.leak], ?_⟩
    intro x hx
    simp only [afterCorrShifted, GameState.leak, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact le_rfl
    · cases hstL : es.g.tL with
      | none =>
        rw [hs.baseSync.tL_none hstL] at hx
        nomatch hx
      | some m₀ =>
        have hle := (hs.baseSync.tL_some m₀ hstL).2 x hx
        simp [maxOpt]; omega
  · intro x hx
    simp only [afterCorrShifted, GameState.leak, List.mem_cons] at hx ⊢
    have he_le : (if max (es.g.epoch .A) (es.g.epoch .B) = l ∧ es.g.epoch P + 1 ≤ l
        then l - 1 else max (es.g.epoch .A) (es.g.epoch .B)) ≤
        max (es.g.epoch .A) (es.g.epoch .B) := by
      split_ifs <;> omega
    rcases hx with rfl | hx
    · cases hstL : es.g.tL with
      | none => simpa [maxOpt] using he_le
      | some m₀ =>
        have hm₀ := hs.baseSync.leaks_ub m₀ (hs.baseSync.tL_some m₀ hstL).1
        dsimp only at hm₀
        simp only [maxOpt]; omega
    · exact hs.baseSync.leaks_ub x hx
  · intro pos hpos
    simp only [afterCorrShifted, GameState.leak, List.mem_append, List.mem_map,
      List.mem_filter] at hpos
    have he_ge : max (es.g.epoch .A) (es.g.epoch .B) ≤
        (if max (es.g.epoch .A) (es.g.epoch .B) = l ∧ es.g.epoch P + 1 ≤ l
         then l - 1 else max (es.g.epoch .A) (es.g.epoch .B)) + 1 := by
      split_ifs <;> omega
    rcases hpos with ⟨r, ⟨hr, _⟩, rfl⟩ | hpos
    · have hinv := (hs.baseSync.trans_inv r hr).2.2.1
      dsimp only at hinv
      have hmax : es.g.epoch r.pos.sender ≤ max (es.g.epoch .A) (es.g.epoch .B) := by
        cases r.pos.sender <;> simp
      cases hstL : es.g.tL <;>
        simp only [afterCorrShifted, GameState.leak, hstL, maxOpt, healedBy,
          decide_eq_false_iff_not] <;> omega
    · have hun := hs.baseSync.comp_unhealed pos hpos
      dsimp only at hun
      cases hstL : es.g.tL with
      | none => simp [hstL, healedBy] at hun
      | some m₀ =>
        simp only [hstL, healedBy, decide_eq_false_iff_not] at hun
        simp only [afterCorrShifted, GameState.leak, hstL, maxOpt, healedBy,
          decide_eq_false_iff_not]
        omega

omit [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E] [SampleableType KR]
  [SampleableType KC] [SampleableType I] [SampleableType K] in
theorem vRecv_hooksCKAShifted_run
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (l tStar : ℕ)
    (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party) (vp : VP (Option Γ) T Sig SS RS)
    (c : Header T × E) (rec : Option (Record M (Header T × E)))
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)) :
    (liftH (vRecv (hooksCKAShifted cka prng fs l tStar) ctx P vp c rec)).run es =
      ((liftH (vRecv (hooksCKA cka prng fs 1 ⟨true, some (l - 1), tStar⟩)
        ctx P vp c rec)).run { g := es.g, h := es.h.base, abort := es.abort } >>=
        fun (res, _) => pure (res, es)) := by
  unfold vRecv hooksCKAShifted hooksCKA
  dsimp only [liftH_run]
  by_cases hg : (vp.id.sendsIn c.1.1 || decide (vp.tcur + 1 < c.1.1)) = true
  · simp [hg]
  · simp only [hg, Bool.false_eq_true, ↓reduceIte, pure_bind]
    by_cases ht : c.1.1 = vp.tcur + 1
    · simp only [ht, ↓reduceIte]
      cases hc2 : c.1.2 with
      | none => simp
      | some Tn =>
        simp only [StateT.run_bind, StateT.run_get, pure_bind]
        cases hcache : es.h.base.cache (vp.tcur + 1) with
        | none =>
          simp only [Bool.true_and, decide_eq_true_eq]
          split_ifs with hne
          · cases vp.γ <;> simp [StateT.run_pure, pure_bind]
            rename_i γ
            cases fs.receive (fs.initReceiver (prng.up vp.root (cka.receive γ Tn).2).2) c.1 c.2 <;>
              simp
          · simp
        | some pair =>
          rcases pair with ⟨Tc, Ik⟩
          by_cases hTc : Tc = Tn
          · simp only [hTc, ↓reduceIte, StateT.run_pure, pure_bind, Function.update_self]
            cases fs.receive (fs.initReceiver (prng.up vp.root Ik).2) c.1 c.2 <;> simp
          · simp only [hTc, ↓reduceIte, Bool.true_and, decide_eq_true_eq]
            split_ifs with hne
            · cases vp.γ <;> simp [StateT.run_pure, pure_bind]
              rename_i γ
              cases fs.receive
                (fs.initReceiver (prng.up vp.root (cka.receive γ Tn).2).2) c.1 c.2 <;>
                simp
            · simp
    · simp only [ht, ↓reduceIte]
      cases vp.vR c.1.1 with
      | none => simp
      | some v =>
        dsimp only
        cases fs.receive v c.1 c.2 <;> simp

omit [DecidableEq I] [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem commitE_same_shifted (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (l tStar : ℕ)
    {P : Party} {new : VP (Option Γ) T Sig SS RS} {pos : Pos}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (ht : new.tcur = (es.g.st P).tcur) :
    ((simulateQ
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
        CKA.oracleImpl cka 1 (l + 1))
      ((commitE (hooksCKAShifted cka prng fs l tStar)
        es.g P (es.g.st P) new pos).run es)).run sc) =
      pure ((some (es.g.accept P new pos), es), sc) := by
  simp [commitE, hooksCKAShifted, ht]

omit [DecidableEq I] [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem commitE_new_shifted (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) {l tStar : ℕ}
    {P : Party} (σ' : Sig) (vR' : ℕ → Option RS) {pos : Pos}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9Shifted cka l tStar s es sc)
    (ht : pos.epoch = es.g.epoch P + 1)
    (heq_other : es.g.epoch P + 1 = es.g.epoch P.other)
    (T_t : T)
    (hl_msg : es.g.epoch P.other ≤ (l - 1) + 2 + 1 → sc.lastMsg = some T_t) :
    let t := pos.epoch
    let γ_r' := (cka.receive (s.st P).γ T_t).1
    let γ_v' : Option Γ := if AuthL9.isLocal (some (l - 1)) 1 t then some γ_r' else none
    let new : PartyState (Option Γ) T Sig SS RS :=
      { es.g.st P with tcur := t, γ := (es.g.st P).γ.map (fun γ => (cka.receive γ T_t).1),
                       root := σ', vR := vR' }
    let st_v' : PartyState (Option Γ) T Sig SS RS :=
      { es.g.st P with tcur := t, γ := γ_v', root := σ', vR := vR' }
    let h' : CKAStateShifted Γ T I :=
      if t + 1 ≤ l then { es.h with γPre := Function.update es.h.γPre P (some γ_r') } else es.h
    let sc' : CKA.GameState Γ T :=
      if AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P) then sc else sc.afterReceive P γ_r'
    ((simulateQ
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
        CKA.oracleImpl cka 1 (l + 1))
      ((commitE (hooksCKAShifted cka prng fs l tStar)
        es.g P (es.g.st P) new pos).run es)).run sc) =
      pure ((some (es.g.accept P st_v' pos), { es with h := h' }), sc') := by
  intro t γ_r' γ_v' new st_v' h' sc'
  have hγ := hs.baseSync.γ_eq P
  dsimp only at hγ
  have htcur := hs.baseSync.st_tcur P
  dsimp only at htcur
  have hhl := hs.hl
  by_cases hloc : AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P) = true
  · simp only [hloc, ↓reduceIte] at hγ
    have hloc_t : AuthL9.isLocal (some (l - 1)) 1 t = true := by
      simp only [AuthL9.isLocal, decide_eq_true_eq] at hloc ⊢
      dsimp only [t]; omega
    have hnot_pre : ¬(t + 1 ≤ l) := by
      simp only [AuthL9.isLocal, decide_eq_true_eq] at hloc
      dsimp only [t]; omega
    have hh' : h' = es.h := by simp [h', hnot_pre]
    have hnew_eq : new = st_v' := by simp [new, st_v', γ_v', γ_r', hγ, hloc_t]
    simp [commitE, hooksCKAShifted, hγ, hloc, hnew_eq, hh', sc']
  · simp only [hloc, Bool.false_eq_true, ↓reduceIte] at hγ
    have hloc' : es.g.epoch P < (l - 1) + 2 + 1 := by
      simpa [AuthL9.isLocal] using hloc
    have hnew_tcur : new.tcur = t := rfl
    have hlt_tcur : (es.g.st P).tcur < t := by dsimp only [t]; rw [htcur, ht]; omega
    have hsc_P := hs.baseSync.sc_epoch (l - 1) rfl P
    have hsc_Po := hs.baseSync.sc_epoch (l - 1) rfl P.other
    dsimp only at hsc_P hsc_Po
    have hcan : sc.canReceive P = true := by
      simp only [CKA.GameState.canReceive, hsc_P, hsc_Po, ← heq_other, beq_iff_eq]
      omega
    have hmsg : sc.lastMsg = some T_t := hl_msg (by omega)
    have hstP : sc.st P = (s.st P).γ := by
      rw [hs.baseSync.s_eq]
      simp [AuthL9.realGS, AuthL9.realVP, hγ]
    have hafter_st : (sc.afterReceive P γ_r').st P = γ_r' := by
      simp [CKA.GameState.afterReceive]
    by_cases hpre : t + 1 ≤ l
    · have hloc_t : AuthL9.isLocal (some (l - 1)) 1 t = false := by
        simp only [AuthL9.isLocal, decide_eq_false_iff_not]; omega
      have hfin_lt : ¬(l + 2 ≤ t) := by omega
      have hall : (sc.afterReceive P γ_r').allowCorr (l + 1) = true := by
        apply allowCorr_afterReceive_of_le
        · rw [hsc_P, hsc_Po]; omega
        · rw [hsc_P]; dsimp only [t] at hpre; omega
      have hst_v_eq : new = st_v' := by simp [new, st_v', γ_v', hγ, hloc_t]
      simp only [commitE, hooksCKAShifted, hnew_tcur, hγ, hlt_tcur, decide_true, Option.isNone,
        Bool.and_self, ↓reduceIte, liftH_run, liftCShifted, setγPreShifted, CKA.receiveQuery,
        CKA.corrQuery, StateT.run_bind, StateT.run_lift, simulateQ_bind, AuthL9.simulateQ_query_eq,
        QueryImpl.add_apply, CKA.oracleImpl, CKA.receiveImpl, CKA.corrImpl,
        StateT.run_get, pure_bind, hcan, Bool.not_true, Bool.false_eq_true, hmsg,
        StateT.run_set, StateT.run_modify, StateT.run_pure, simulateQ_pure, bind_assoc, hstP, γ_r',
        hfin_lt, hpre, hall, Bool.true_or, hafter_st, AuthL9.accept_update_st, h', sc', hloc]
      rw [hst_v_eq]
    · by_cases hloc_t : AuthL9.isLocal (some (l - 1)) 1 t = true
      · have hfin_le : l + 2 ≤ t := by
          simp only [AuthL9.isLocal, decide_eq_true_eq] at hloc_t; omega
        have hfin : (sc.afterReceive P γ_r').finished 1 (l + 1) P = true := by
          apply finished_afterReceive_of_ge
          rw [hsc_P]; dsimp only [t] at hfin_le; omega
        have hst_v_eq : { new with γ := some γ_r' } = st_v' := by
          simp [new, st_v', γ_v', hloc_t]
        simp only [commitE, hooksCKAShifted, hnew_tcur, hγ, hlt_tcur, decide_true, Option.isNone,
          Bool.and_self, ↓reduceIte, liftH_run, liftCShifted, CKA.receiveQuery, CKA.corrQuery,
          StateT.run_bind, StateT.run_lift, simulateQ_bind, AuthL9.simulateQ_query_eq,
          QueryImpl.add_apply, CKA.oracleImpl, CKA.receiveImpl, CKA.corrImpl,
          StateT.run_get, pure_bind, hcan, Bool.not_true, Bool.false_eq_true, hmsg,
          StateT.run_set, StateT.run_pure, simulateQ_pure, bind_assoc, hstP, γ_r',
          hpre, hfin_le, hfin, Bool.or_true, hafter_st, AuthL9.accept_update_st, h', sc', hloc]
        rw [← hnew_tcur, hst_v_eq]
      · have hfin_lt : ¬(l + 2 ≤ t) := by
          simp only [AuthL9.isLocal, Bool.not_eq_true, decide_eq_false_iff_not] at hloc_t; omega
        have hst_v_eq : new = st_v' := by simp [new, st_v', γ_v', hγ, hloc_t]
        simp only [commitE, hooksCKAShifted, hnew_tcur, hγ, hlt_tcur, decide_true, Option.isNone,
          Bool.and_self, ↓reduceIte, liftH_run, liftCShifted, CKA.receiveQuery,
          StateT.run_bind, StateT.run_lift, simulateQ_bind, AuthL9.simulateQ_query_eq,
          QueryImpl.add_apply, CKA.oracleImpl, CKA.receiveImpl,
          StateT.run_get, pure_bind, hcan, Bool.not_true, Bool.false_eq_true, hmsg,
          StateT.run_set, StateT.run_pure, simulateQ_pure, bind_assoc, hstP, γ_r',
          hpre, hfin_lt, AuthL9.accept_update_st, h', sc', hloc]
        rw [hst_v_eq]

theorem vSend_same_epoch_shifted (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) {l tStar : ℕ}
    {P : Party} {m : M} {r : Option CCoins}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9Shifted cka l tStar s es sc)
    (hnsend : P.sendsIn (es.g.epoch P + 1) = false) :
    let h : Header T := (es.g.epoch P, (es.g.st P).curCkaMsg)
    let vS_e : Option SS × E :=
      match (es.g.st P).vS with
      | some v => (some (fs.send v h m).1, (fs.send v h m).2)
      | none => (none, default)
    (∀ coins, send cka prng fs (s.st P) m coins =
      ({ s.st P with vS := vS_e.1 }, (h, vS_e.2))) ∧
    ((liftH (vSend (hooksCKAShifted cka prng fs l tStar)
      es.g P (es.g.st P) m none r)).run es =
      pure (some ({ es.g.st P with vS := vS_e.1 }, (h, vS_e.2)), es)) := by
  intro h vS_e
  have hbase := AuthL9.vSend_same_epoch cka prng fs 1 (some (l - 1)) tStar
    (m := m) (r := r) hs.baseSync hnsend
  dsimp only at hbase
  refine ⟨hbase.1, ?_⟩
  have hid_v := hs.baseSync.st_id P
  have htcur_v := hs.baseSync.st_tcur P
  dsimp only at hid_v htcur_v
  unfold vSend
  have hcond : ((es.g.st P).id.sendsIn ((es.g.st P).tcur + 1)) = false := by
    rw [hid_v, htcur_v, hnsend]
  dsimp only [vS_e]
  rw [hcond]
  simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, liftH_run]
  cases hvS : (es.g.st P).vS with
  | none =>
    simp only [StateT.run_pure, pure_bind, htcur_v, h]
    congr 3
    cases hp : es.g.st P
    simp_all
  | some v =>
    simp [hooksCKAShifted, htcur_v, h]

omit [DecidableEq M] [DecidableEq E] [DecidableEq I] [SampleableType KR] [SampleableType KC]
  [SampleableType K] in
theorem vSend_new_local_shifted (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) {l tStar : ℕ}
    {P : Party} {m : M} {r : Option CCoins}
    {s₁ : GameState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9Shifted cka l tStar s es sc)
    (hsend : P.sendsIn (es.g.epoch P + 1) = true)
    (hloc : AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P) = true) :
    ((simulateQ
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
        CKA.oracleImpl cka 1 (l + 1))
      ((liftH (vSend (hooksCKAShifted cka prng fs l tStar)
        s₁ P (es.g.st P) m none r)).run es)).run sc) =
      ((match r with | none => $ᵗ CCoins | some c => pure c) >>= fun coins =>
        let t := es.g.epoch P + 1
        let c_cka := cka.send (s.st P).γ coins
        let p := prng.up (es.g.st P).root c_cka.2.2
        let ss := fs.initSender p.2
        let h : Header T := (t, some c_cka.2.1)
        let out_fs := fs.send ss h m
        let γv' : Option Γ := if AuthL9.isLocal (some (l - 1)) 1 t then some c_cka.1 else none
        let st_v' : PartyState (Option Γ) T Sig SS RS :=
          { es.g.st P with tcur := t, γ := γv', curCkaMsg := some c_cka.2.1, root := p.1,
                           vS := some out_fs.1 }
        let h' : CKAStateShifted Γ T I :=
          { base := { cache := Function.update es.h.base.cache t (some (c_cka.2.1, c_cka.2.2)) }
            γPre := if t + 1 ≤ l then Function.update es.h.γPre P (some c_cka.1) else es.h.γPre }
        let sc' : CKA.GameState Γ T :=
          if AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P) then sc
          else sc.afterSend P c_cka.1 c_cka.2.1
        pure ((some (st_v', (h, out_fs.2)), { es with h := h' }), sc')) := by
  have hid_v := hs.baseSync.st_id P
  have htcur_v := hs.baseSync.st_tcur P
  have hγ := hs.baseSync.γ_eq P
  dsimp only at hid_v htcur_v hγ
  simp only [hloc, ↓reduceIte] at hγ
  have hloc_t : AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P + 1) = true := by
    simp only [AuthL9.isLocal, decide_eq_true_eq] at hloc ⊢; omega
  have hnot_pre : ¬((es.g.epoch P + 1) + 1 ≤ l) := by
    simp only [AuthL9.isLocal, decide_eq_true_eq] at hloc; omega
  unfold vSend
  simp only [hid_v, htcur_v, hsend, ↓reduceIte, hooksCKAShifted, hγ, cacheCShifted, liftH_run]
  cases r with
  | some c =>
    simp [hloc, hloc_t, hnot_pre]
  | none =>
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_modify, pure_bind, StateT.run_pure,
      simulateQ_bind, simulateQ_pure, bind_assoc, AuthL9.simulateQ_sampleT_run, hloc, hloc_t,
      hnot_pre, ↓reduceIte]

omit [SampleableType KR] [SampleableType K] in
theorem vSend_new_nonlocal_none_shifted (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) {l tStar : ℕ}
    {P : Party} {m : M}
    {s₁ : GameState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9Shifted cka l tStar s es sc)
    (hsend : P.sendsIn (es.g.epoch P + 1) = true)
    (hloc : AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P) = false) :
    ((simulateQ
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
        CKA.oracleImpl cka 1 (l + 1))
      ((liftH (vSend (hooksCKAShifted cka prng fs l tStar)
        s₁ P (es.g.st P) m none none)).run es)).run sc) =
      (($ᵗ CCoins : ProbComp CCoins) >>= fun coins =>
        let t := es.g.epoch P + 1
        let c_cka := cka.send (s.st P).γ coins
        let p := prng.up (es.g.st P).root c_cka.2.2
        let ss := fs.initSender p.2
        let h : Header T := (t, some c_cka.2.1)
        let out_fs := fs.send ss h m
        let γv' : Option Γ := if AuthL9.isLocal (some (l - 1)) 1 t then some c_cka.1 else none
        let st_v' : PartyState (Option Γ) T Sig SS RS :=
          { es.g.st P with tcur := t, γ := γv', curCkaMsg := some c_cka.2.1, root := p.1,
                           vS := some out_fs.1 }
        let h' : CKAStateShifted Γ T I :=
          { base := { cache := Function.update es.h.base.cache t (some (c_cka.2.1, c_cka.2.2)) }
            γPre := if t + 1 ≤ l then Function.update es.h.γPre P (some c_cka.1) else es.h.γPre }
        let sc' : CKA.GameState Γ T :=
          if AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P) then sc
          else sc.afterSend P c_cka.1 c_cka.2.1
        pure ((some (st_v', (h, out_fs.2)), { es with h := h' }), sc')) := by
  have hid_v := hs.baseSync.st_id P
  have htcur_v := hs.baseSync.st_tcur P
  have hγ := hs.baseSync.γ_eq P
  dsimp only at hid_v htcur_v hγ
  simp only [hloc, Bool.false_eq_true, ↓reduceIte] at hγ
  have hhl := hs.hl
  have hloc' : es.g.epoch P < (l - 1) + 2 + 1 := by simpa [AuthL9.isLocal] using hloc
  have heq := hs.baseSync.epoch_eq_of_sendsIn_succ hsend
  dsimp only at heq
  have hsc_P : sc.epoch P = es.g.epoch P := by
    have h := hs.baseSync.sc_epoch (l - 1) rfl P; dsimp only at h; omega
  have hsc_Po : sc.epoch P.other = es.g.epoch P := by
    have h := hs.baseSync.sc_epoch (l - 1) rfl P.other; dsimp only at h; omega
  have hcan : sc.canSend P = true := by
    simp [CKA.GameState.canSend, hsc_P, hsc_Po, hsend]
  have hstP : sc.st P = (s.st P).γ := by
    rw [hs.baseSync.s_eq]
    simp [AuthL9.realGS, AuthL9.realVP, hγ]
  unfold vSend
  simp only [hid_v, htcur_v, hsend, ↓reduceIte, hooksCKAShifted, hγ, cacheCShifted, setγPreShifted,
    liftH_run, liftCShifted]
  by_cases htH : es.g.epoch P + 1 = l + 1
  · have heq_tH : sc.epoch P + 1 = l + 1 := by rw [hsc_P]; exact htH
    simp only [eq_true htH, ↓reduceIte, CKA.challQuery, StateT.run_bind, StateT.run_lift,
      StateT.run_monadLift, monadLift_self, StateT.run_modify, simulateQ_bind,
      AuthL9.simulateQ_query_eq, simulateQ_pure, QueryImpl.add_apply, CKA.oracleImpl, CKA.challImpl,
      hcan, heq_tH, bne_self_eq_false, Bool.not_true, Bool.or_self, Bool.false_eq_true,
      StateT.run_get, pure_bind, StateT.run_set, hs.baseSync.sc_b, StateT.run_pure,
      hstP, bind_assoc]
    refine bind_congr fun coins => ?_
    have hnot_pre : ¬((es.g.epoch P + 1) + 1 ≤ l) := by omega
    have hnot_loc2 : ¬(l + 2 ≤ es.g.epoch P + 1) := by omega
    have hloc_t : AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P + 1) = false := by
      simp only [AuthL9.isLocal, decide_eq_false_iff_not]; omega
    simp [hnot_loc2, hnot_pre, hloc_t, hloc]
  · have hne_tH : (sc.epoch P + 1 == l + 1) = false := by
      rw [hsc_P, beq_eq_false_iff_ne]; exact htH
    simp only [eq_false htH, ↓reduceIte, CKA.sendQuery, StateT.run_bind, StateT.run_lift,
      StateT.run_monadLift, monadLift_self, StateT.run_modify, simulateQ_bind,
      AuthL9.simulateQ_query_eq, simulateQ_pure, QueryImpl.add_apply, CKA.oracleImpl, CKA.sendImpl,
      hcan, hne_tH, Bool.not_true, Bool.or_self, Bool.false_eq_true,
      StateT.run_get, pure_bind, StateT.run_set, StateT.run_pure, hstP, bind_assoc]
    refine bind_congr fun coins => ?_
    have hafter_st :
        (sc.afterSend P (cka.send (s.st P).γ coins).1 (cka.send (s.st P).γ coins).2.1).st P =
          (cka.send (s.st P).γ coins).1 := by
      simp [CKA.GameState.afterSend]
    by_cases hpre : (es.g.epoch P + 1) + 1 ≤ l
    · have hloc_t : AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P + 1) = false := by
        simp only [AuthL9.isLocal, decide_eq_false_iff_not]; omega
      have hfin_lt : ¬(l + 2 ≤ es.g.epoch P + 1) := by omega
      have hall : (sc.afterSend P (cka.send (s.st P).γ coins).1
          (cka.send (s.st P).γ coins).2.1).allowCorr (l + 1) = true := by
        apply allowCorr_afterSend_of_le
        · rw [hsc_P, hsc_Po]
        · rw [hsc_P]; exact hpre
      simp [hfin_lt, hpre, hloc_t, hloc, CKA.corrQuery, QueryImpl.add_apply,
        CKA.corrImpl, hall, hafter_st]
    · by_cases hloc_t : AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P + 1) = true
      · have hfin_le : l + 2 ≤ es.g.epoch P + 1 := by
          simp only [AuthL9.isLocal, decide_eq_true_eq] at hloc_t; omega
        have hfin : (sc.afterSend P (cka.send (s.st P).γ coins).1
            (cka.send (s.st P).γ coins).2.1).finished 1 (l + 1) P = true := by
          apply finished_afterSend_of_ge
          rw [hsc_P]; exact hfin_le
        simp [hfin_le, hpre, hloc_t, hloc, CKA.corrQuery, QueryImpl.add_apply,
          CKA.corrImpl, hfin, hafter_st]
      · have hfin_lt : ¬(l + 2 ≤ es.g.epoch P + 1) := by
          simp only [AuthL9.isLocal, Bool.not_eq_true, decide_eq_false_iff_not] at hloc_t; omega
        simp [hfin_lt, hpre, hloc_t, hloc]

section AuthL11Shifted

open AuthL11

theorem eraseSt_afterCorrShifted {St₁ St₂ Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    {g₁ : SM.GameState St₁ Msg C} {g₂ : SM.GameState St₂ Msg C}
    (h : eraseSt g₁ = eraseSt g₂) (l : ℕ) (P : Party) :
    eraseSt (afterCorrShifted l g₁ P) = eraseSt (afterCorrShifted l g₂ P) := by
  simp [eraseSt, afterCorrShifted, SM.GameState.leak, eraseSt_epoch h, eraseSt_idx h,
    eraseSt_tL h, eraseSt_trans h, eraseSt_chall h, eraseSt_comp h, eraseSt_maxAcc h,
    eraseSt_b h, eraseSt_win h, eraseSt_leaks h, eraseSt_corrs h]

theorem comp_inv_afterCorrShifted {St Msg C : Type} (g : SM.GameState St Msg C) (l Δ : ℕ)
    (hΔ : 2 ≤ Δ) (P : Party) (htrans : ∀ r ∈ g.trans, r.pos.epoch ≤ g.epoch r.pos.sender)
    (hcomp : ∀ pos ∈ g.comp, SM.healedBy g.tL Δ pos.epoch = false) :
    ∀ pos ∈ (afterCorrShifted l g P).comp,
      SM.healedBy (afterCorrShifted l g P).tL Δ pos.epoch = false := by
  intro pos hpos
  simp only [afterCorrShifted, SM.GameState.leak, List.mem_append, List.mem_map,
    List.mem_filter] at hpos ⊢
  rcases hpos with ⟨r, ⟨hr_mem, _⟩, rfl⟩ | hpos'
  · have hle : r.pos.epoch ≤ g.epoch r.pos.sender := htrans r hr_mem
    have h_max : g.epoch r.pos.sender ≤ max (g.epoch .A) (g.epoch .B) := by
      cases r.pos.sender <;> simp
    have he_ge : max (g.epoch .A) (g.epoch .B) ≤
        (if max (g.epoch .A) (g.epoch .B) = l ∧ g.epoch P + 1 ≤ l then l - 1
         else max (g.epoch .A) (g.epoch .B)) + 1 := by
      split_ifs <;> omega
    have h_opt :
        (if max (g.epoch .A) (g.epoch .B) = l ∧ g.epoch P + 1 ≤ l then l - 1
         else max (g.epoch .A) (g.epoch .B)) ≤
        SM.maxOpt g.tL
          (if max (g.epoch .A) (g.epoch .B) = l ∧ g.epoch P + 1 ≤ l then l - 1
           else max (g.epoch .A) (g.epoch .B)) := by
      cases g.tL <;> simp [SM.maxOpt]
    dsimp only [SM.healedBy]
    rw [decide_eq_false_iff_not]
    omega
  · exact healedBy_leak_false_of_false (hcomp pos hpos')

end AuthL11Shifted

namespace AuthL10Shifted

open CryptoGames.SM.Construction.AuthL10 CryptoGames.SM.Construction.DeliverForge.AuthL10DF

omit [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType I]
  [SampleableType K] in
@[simp]
lemma hooksCKAShifted_fsRecv (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (l tStar : ℕ)
    (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party) (t : ℕ)
    (rs : RS) (h : Header T) (e : E) (rec : Option (SM.Record M (Header T × E))) :
    (hooksCKAShifted cka prng fs l tStar).fsRecv ctx P t rs h e rec =
      pure (some (fs.receive rs h e)) := rfl

omit [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType I]
  [SampleableType K] in
@[simp]
lemma hooksCKAShifted_commit (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (l tStar : ℕ)
    (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party)
    (old new : VP (Option Γ) T Sig SS RS) :
    (hooksCKAShifted cka prng fs l tStar).commit ctx P old new =
      (if old.tcur < new.tcur && old.γ.isNone then do
        match ← liftCShifted (CKA.receiveQuery P) with
        | none => return none
        | some () =>
          if l + 2 ≤ new.tcur then
            match ← liftCShifted (CKA.corrQuery P) with
            | none => return none
            | some γ => return some { new with γ := some γ }
          else if new.tcur + 1 ≤ l then
            match ← liftCShifted (CKA.corrQuery P) with
            | none => return none
            | some γ =>
              setγPreShifted P (some γ)
              return some new
          else return some new
      else return some new) := rfl

omit [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType I]
  [SampleableType K] in
lemma startRecv_CKAShifted_unhonest (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (l tStar : ℕ)
    (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party)
    (t : ℕ) (γv : Option Γ) (σ : Sig) (Tn : T) (hc : CKAStateShifted Γ T I)
    (h : ∀ Im, hc.base.cache t ≠ some (Tn, Im)) :
    ((hooksCKAShifted cka prng fs l tStar).startRecv ctx P t γv σ Tn).run hc =
      (if t = tStar then
        match γv with
        | some γ =>
          let k := cka.receive γ Tn
          let p := prng.up σ k.2
          pure (some (some (some k.1, p.1, fs.initReceiver p.2)), hc)
        | none => pure (none, hc)
      else pure (some none, hc)) := by
  rcases hcache : hc.base.cache t with _ | ⟨Tc, Ik⟩
  · simp only [hooksCKAShifted, hcache, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · split <;> rfl
    · rfl
  · have hne : Tc ≠ Tn := fun heq => h Ik (by rw [← heq, hcache])
    simp only [hooksCKAShifted, hcache, hne, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · split <;> rfl
    · rfl

omit [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType I]
  [SampleableType K] in
lemma hooksCKAShifted_startRecv_honest (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (l tStar : ℕ)
    (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party)
    (t : ℕ) (γv : Option Γ) (σ : Sig) (Tm : T) (Im : I) (hc : CKAStateShifted Γ T I)
    (hcache : hc.base.cache t = some (Tm, Im)) :
    ((hooksCKAShifted cka prng fs l tStar).startRecv ctx P t γv σ Tm).run hc =
      pure (some (some (γv.map fun γ => (cka.receive γ Tm).1,
        (prng.up σ Im).1, fs.initReceiver (prng.up σ Im).2)), hc) := by
  simp [hooksCKAShifted, hcache, StateT.run_bind, StateT.run_get, StateT.run_pure]

end AuthL10Shifted

end RedCKAShifted

section ShiftCoupling

/-- Reachable-state invariant relating `s.tL` and every `m ∈ s.leaks` to a corruption in `s.corrs`. -/
def LeakCorrInv {St Msg C : Type} (s : GameState St Msg C) : Prop :=
  (s.tL = none → s.leaks = []) ∧
  (∀ m, s.tL = some m → m ∈ s.leaks ∧ ∀ x ∈ s.leaks, x ≤ m) ∧
  (∀ m ∈ s.leaks, ∃ R e, (R, e) ∈ s.corrs ∧ e ≤ m ∧ m ≤ e + 1 ∧
    (m = e + 1 → R = Party.receiverOf m))

theorem LeakCorrInv.init {Key St Msg Coins C : Type}
    (sm : SMScheme Key St Msg Coins C) (k : Key) (b : Bool) :
    LeakCorrInv (initState sm k b) := by
  refine ⟨fun _ => rfl, fun m hm => by simp [initState] at hm,
    fun m hm => by simp [initState] at hm⟩

theorem LeakCorrInv.afterCorr {St Msg C : Type} {s : GameState St Msg C}
    (h : LeakCorrInv s) (P : Party)
    (hep_le : s.epoch P ≤ max (s.epoch .A) (s.epoch .B))
    (hep_step : max (s.epoch .A) (s.epoch .B) ≤ s.epoch P + 1)
    (hrcv : max (s.epoch .A) (s.epoch .B) = s.epoch P + 1 →
      P = Party.receiverOf (max (s.epoch .A) (s.epoch .B))) :
    LeakCorrInv (s.afterCorr P) := by
  let M := max (s.epoch .A) (s.epoch .B)
  have hM_orig : ∃ R e, (R, e) ∈ (P, s.epoch P) :: s.corrs ∧ e ≤ M ∧ M ≤ e + 1 ∧
      (M = e + 1 → R = Party.receiverOf M) :=
    ⟨P, s.epoch P, List.mem_cons_self, hep_le, hep_step, hrcv⟩
  have hmaxOpt_orig : ∃ R e, (R, e) ∈ (P, s.epoch P) :: s.corrs ∧
      e ≤ maxOpt s.tL M ∧ maxOpt s.tL M ≤ e + 1 ∧
      (maxOpt s.tL M = e + 1 → R = Party.receiverOf (maxOpt s.tL M)) := by
    cases htL : s.tL with
    | none => simpa [maxOpt, htL] using hM_orig
    | some k =>
      dsimp only [maxOpt]
      by_cases hkM : k ≤ M
      · rw [Nat.max_eq_right hkM]
        exact hM_orig
      · rw [Nat.max_eq_left (by omega)]
        obtain ⟨R, e, hce, h1, h2, h3⟩ := h.2.2 k (h.2.1 k htL).1
        exact ⟨R, e, List.mem_cons_of_mem _ hce, h1, h2, h3⟩
  refine ⟨by simp [GameState.afterCorr, GameState.leak], ?_, ?_⟩
  · intro m hm
    simp only [GameState.afterCorr, GameState.leak, Option.some.injEq] at hm
    subst hm
    refine ⟨List.mem_cons_self, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact Nat.le_refl _
    · cases htL : s.tL with
      | none =>
        rw [h.1 htL] at hx'
        nomatch hx'
      | some k =>
        have hxk := (h.2.1 k htL).2 x hx'
        simp only [maxOpt]
        omega
  · intro m hm
    rcases List.mem_cons.mp hm with rfl | hm'
    · exact hmaxOpt_orig
    · obtain ⟨R, e, hce, h1, h2, h3⟩ := h.2.2 m hm'
      exact ⟨R, e, List.mem_cons_of_mem _ hce, h1, h2, h3⟩

theorem LeakCorrInv.afterCorr_of_wfState {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    {Δ : ℕ} {s : GameState St Msg C}
    (hwf : CryptoGames.SM.Thm1L17.WFState Δ s)
    (h : LeakCorrInv s) (P : Party) :
    LeakCorrInv (s.afterCorr P) := by
  refine LeakCorrInv.afterCorr h P (hwf.epoch_le_max P) ?_ ?_
  · exact max_le (hwf.epoch_le_any_add_one .A P) (hwf.epoch_le_any_add_one .B P)
  · intro hmax
    have hEq : s.epoch P.other = s.epoch P + 1 := by
      cases P with
      | A =>
        have hA : max (s.epoch .A) (s.epoch .B) = s.epoch .B :=
          max_eq_right_of_lt (by omega)
        dsimp only [Party.other]
        omega
      | B =>
        have hB : max (s.epoch .A) (s.epoch .B) = s.epoch .A :=
          max_eq_left_of_lt (by omega)
        dsimp only [Party.other]
        omega
    have hsends : P.other.sendsIn (s.epoch P.other) = true := by
      have hb := hwf.epoch_bound P.other
      have hPP : P.other.other = P := by cases P <;> rfl
      rw [hPP] at hb
      cases hs : P.other.sendsIn (s.epoch P.other)
      · rw [hs] at hb; simp at hb; omega
      · rfl
    have hrcv :=
      CryptoGames.SM.Thm1L17.receiverOf_eq_other_of_sendsIn (hEq ▸ hsends)
    calc
      P = P.other.other := by cases P <;> rfl
      _ = Party.receiverOf (max (s.epoch .A) (s.epoch .B)) := by rw [hmax, hrcv]

end ShiftCoupling

end CryptoGames.SM.Construction.DeliverForge

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Construction.DeliverForge
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs.Correctness
open CryptoVerification.LibsignalSession
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
@[simp] theorem authOKDir2_with_win {St Msg C : Type} (tL : Option ℕ) (tStar : ℕ)
    (s : SM.GameState St Msg C) (w : Bool) :
    authOKDir2 tL tStar { s with win := w } = authOKDir2 tL tStar s := rfl

end CryptoGames.LibsignalSM.Proofs.Refinement

namespace CryptoVerification.LibsignalSession.HeadlineV1

open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.Construction.DeliverForge
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC CryptoGames.LibsignalSM.Proofs
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

section RedFSAuthDFShifted

open ReductionsQueries

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E Pub : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [DecidableEq Pub] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

end RedFSAuthDFShifted

section RedFSHiddenSaltShifted

variable {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  [Inhabited PQ] [SampleableType PQC]

end RedFSHiddenSaltShifted

end CryptoVerification.LibsignalSession.HeadlineV1

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM
open CryptoGames.SM.Construction CryptoGames.SM.Engine CryptoGames.SM.Thm1
open CryptoGames.LibsignalSM.Inst CryptoGames.LibsignalSession
open CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC CryptoVerification.LibsignalSession
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

variable {PQ PQC Pt : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt]
  [Inhabited PQ] [SampleableType PQC]

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM
open CryptoGames.SM.Construction CryptoGames.SM.Engine CryptoGames.SM.Thm1
open CryptoGames.LibsignalSM.Inst CryptoGames.LibsignalSession
open CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC CryptoVerification.LibsignalSession
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

variable {Key St Msg Coins C : Type}
  [DecidableEq Msg] [DecidableEq C]
  [SampleableType Key] [SampleableType Coins]

end CryptoGames.LibsignalSM.Proofs.Refinement

namespace CryptoVerification.LibsignalSession.HeadlineV1

open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Thm1
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs CryptoGames.LibsignalSM.Proofs.Refinement
open CryptoVerification.LibsignalSession
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

section KemFailSimCouplingShifted

open CryptoVerification.LibsignalProtoCodec
open CryptoGames.SM.Construction.DeliverForge

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-- Combines `spqrV1SessionB_sendCorrectQ` and `TopState` preservation into a graded SPQR invariant
satisfying `SpqrCLocal`. -/
theorem spqrCLocal_and_topState_v1
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = CryptoVerification.LibsignalSpqrV1.spqrV1SessionUniformCoins P.C.F K)
    (hK_tot : CryptoVerification.SpqrV1Sync.SendTotal.Encaps1Total K) (q : ℕ) (hq : q < 2 ^ 32) :
    ∃ InvPQ : ℕ → List (BitVec 8) → Prop,
      Proofs.Refinement.SpqrCLocal P.spqr q InvPQ ∧
      ∀ n pq, InvPQ n pq → CryptoVerification.SpqrV1Sync.SendTotal.TopState P.C.F K pq := by
  obtain ⟨Inv₀, ⟨hinit₀, hsend₀, hrecv₀⟩, htot₀, hnop₀⟩ :=
    CryptoVerification.SpqrV1Sync.SendTotal.spqrV1SessionB_sendCorrectQ P.C.F K hK_tot q hq
  refine ⟨fun n pq => Inv₀ n pq ∧ CryptoVerification.SpqrV1Sync.SendTotal.TopState P.C.F K pq,
    ⟨⟨fun dir k => ?_, fun n st r st' salt msg h hs => ?_, fun n st msg st' salt h hr => ?_⟩,
     fun n st r hn h => hspqr_eq ▸ htot₀ n st r hn h.1,
     fun n st r hn h => hspqr_eq ▸ hnop₀ n st r hn h.1⟩,
    fun _ _ h => h.2⟩
  · rw [hspqr_eq]
    exact ⟨hinit₀ dir k, CryptoVerification.SpqrV1Sync.SendTotal.topState_init P.C.F K dir k⟩
  · rw [hspqr_eq] at hs
    obtain ⟨w, hw⟩ := h.2
    obtain ⟨w', hw', -⟩ := CryptoVerification.SpqrV1Sync.SendTotal.topStateW_send P.C.F K hw hs
    exact ⟨hsend₀ n st r st' salt msg h.1 hs, w', hw'⟩
  · rw [hspqr_eq] at hr
    obtain ⟨w, hw⟩ := h.2
    obtain ⟨_, w', _, _, _, hw', -⟩ :=
      CryptoVerification.SpqrV1Sync.SendTotal.topStateW_recv P.C.F K hw hr
    exact ⟨hrecv₀ n st msg st' salt h.1 hr, w', hw'⟩

end KemFailSimCouplingShifted

end CryptoVerification.LibsignalSession.HeadlineV1

namespace CryptoVerification.E2E.Signed

open MeasureTheory
open CryptoGames CryptoGames.SM CryptoGames.SM.Construction CryptoGames.Ratchet
  CryptoGames.Ratchet.LibsignalInst CryptoGames.LibsignalSM.Proofs CryptoVerification.E2E
  CryptoGames.LibsignalSession CryptoGames.CKA LibsignalProtoCodec CryptoGames.LibsignalSM
  CryptoGames.LibsignalSM.Proofs.Refinement CryptoGames.Ratchet.LibsignalSim
  CryptoGames.Ratchet.LibsignalSimC CryptoGames.SM.Construction.DeliverForge
  CryptoVerification.E2E.RefuseCorrB0 CryptoVerification.E2E.HeadlineU
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1Sync.SendTotal
  CryptoVerification.LibsignalSession.HeadlineV1

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

end CryptoVerification.E2E.Signed

