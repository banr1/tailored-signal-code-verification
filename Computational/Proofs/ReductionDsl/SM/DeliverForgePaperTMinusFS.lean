/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperTMinusSim
import Computational.Proofs.ReductionDsl.SM.DeliverForgeShifted
import ProofLib.BV.WidthNorm

/-!
# Receiver-Table, FS-Hook, and Unified Handler Lemmas for `B1(tStar)`

Proves `SMVRInv`, `FSEngineInv`, `fsClamp`, and query-bound lemmas for `injectEB1` and
`deliverForgeEB1`, and defines the `b1`-parameterized unified handlers `injectEGen`,
`deliverForgeEGen`, `injectECGen`, and `deliverForgeECGen`.
-/

@[expose] public section

set_option autoImplicit false

open ReductionDsl OracleSpec OracleComp
open CryptoGames CryptoGames.CKA CryptoGames.PRFPRNG CryptoGames.FSAEAD CryptoGames.SM
open CryptoGames.SM.Engine CryptoGames.SM.Engine.RedPRNG CryptoGames.SM.Construction
open CryptoGames.SM.Construction.DeliverForge

namespace CryptoGames.SM.Engine

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "S" => ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "rrTy" => ckaRrTy KC Γ CCoins T I KR RSt K SS RS M E

theorem injectEB1_vrInv [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    {VROkStep : ℕ → rsV → Prop}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (hVRHk : HooksVRInv VROkStep hk)
    {L B q qep tStar : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × (Header T × E))
    (hInv : SMEngineInv L B (q + 1) es.g)
    (hVR : SMVRInv VROkStep B (q + 1) es.g) :
    ∀ res ∈ support ((DeliverForge.injectEB1 hk qep tStar cfg arg).run es),
      SMVRInv VROkStep B q res.2.g := by
  rcases arg with ⟨P, c⟩
  have hVRQ : SMVRInv VROkStep B q es.g :=
    SMVRInv.mono (VROkStep := VROkStep) hVRHk.mono (Nat.le_succ q) hVR
  have hBq : B - (q + 1) + 1 = B - q := by have := hInv.trans_le; omega
  intro ⟨out, es'⟩ hmem
  unfold DeliverForge.injectEB1 abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj 2))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hVRQ
  · simp only [href, Bool.false_eq_true, ↓reduceIte,
      run_liftH_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
    rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hVRQ
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hVRQ
    · by_cases hqep : qep + 1 < t'
      · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hVRQ
      · simp only [hqep, ↓reduceIte] at hmem
        by_cases htriv : DeliverForge.trivB1 tStar es.g ⟨P.other, t', i'⟩
        · simp only [htriv, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨cmRes, es''⟩, hcm, hmem⟩ := hmem
          have hSt'VR : ∀ t₀ v₀, st'.vR t₀ = some v₀ → VROkStep (B - q) v₀ := by
            rw [← hBq]
            exact vRecv_vrInv hk hVRHk es.g P (es.g.st P) c none es.h (hVR P)
              (some (some (st', t', i', m')), h') hvr st' t' i' m' rfl
          have ⟨hEs'', hAcc⟩ := commitE_vrInv hk hVRHk { es with h := h' } es.g P (es.g.st P)
            st' ⟨P.other, t', i'⟩ hVRQ hVRQ hSt'VR (cmRes, es'') hcm
          rcases cmRes with _ | s₁
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hEs''
          · have hs₁ : SMVRInv VROkStep B q s₁ := hAcc s₁ rfl
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hs₁
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
          by_cases hf : cfg.injectFull t'
          · simp only [hf, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hVRQ
          · simp only [hf, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hVRQ

theorem deliverForgeEB1_vrInv [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    {VROkStep : ℕ → rsV → Prop}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (hVRHk : HooksVRInv VROkStep hk)
    {L B q qep tStar : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × (Header T × E) × (Header T × E))
    (hInv : SMEngineInv L B (q + 1) es.g)
    (hVR : SMVRInv VROkStep B (q + 1) es.g) :
    ∀ res ∈ support ((DeliverForge.deliverForgeEB1 hk qep tStar cfg arg).run es),
      SMVRInv VROkStep B q res.2.g := by
  rcases arg with ⟨P, c, c'⟩
  have hVRQ : SMVRInv VROkStep B q es.g :=
    SMVRInv.mono (VROkStep := VROkStep) hVRHk.mono (Nat.le_succ q) hVR
  have hBq : B - (q + 1) + 1 = B - q := by have := hInv.trans_le; omega
  intro ⟨out, es'⟩ hmem
  unfold DeliverForge.deliverForgeEB1 abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hVRQ
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases htr : es.g.inTransit P.other c with _ | r
    · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hVRQ
    · simp only [htr] at hmem
      by_cases hbad :
          ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1)
      · simp only [hbad, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hVRQ
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte,
          run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
        rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hVRQ
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hVRQ
        · by_cases hqep : (decide (qep + 1 < t') || (t' != r.pos.epoch))
          · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hVRQ
          · simp only [hqep, Bool.false_eq_true, ↓reduceIte] at hmem
            by_cases htriv : DeliverForge.trivB1 tStar es.g ⟨P.other, t', i'⟩
            · simp only [htriv, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
              obtain ⟨⟨cmRes, es''⟩, hcm, hmem⟩ := hmem
              have hSt'VR : ∀ t₀ v₀, st'.vR t₀ = some v₀ → VROkStep (B - q) v₀ := by
                rw [← hBq]
                exact vRecv_vrInv hk hVRHk es.g P (es.g.st P) c' none es.h (hVR P)
                  (some (some (st', t', i', m')), h') hvr st' t' i' m' rfl
              have ⟨hEs'', hAcc⟩ := commitE_vrInv hk hVRHk { es with h := h' } es.g P (es.g.st P)
                st' ⟨P.other, t', i'⟩ hVRQ hVRQ hSt'VR (cmRes, es'') hcm
              rcases cmRes with _ | s₁
              · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
                  Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hEs''
              · have hs₁ : SMVRInv VROkStep B q s₁ := hAcc s₁ rfl
                simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                  support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hs₁
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
              by_cases hf : cfg.injectFull t'
              · simp only [hf, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                  pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hVRQ
              · simp only [hf, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                  support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hVRQ

theorem injectEB1_b_eq [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {qep tStar : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × (Header T × E)) :
    ∀ res ∈ support ((DeliverForge.injectEB1 hk qep tStar cfg arg).run es), res.2.g.b = es.g.b := by
  rcases arg with ⟨P, c⟩
  intro ⟨out, es'⟩ hmem
  unfold DeliverForge.injectEB1 abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj 2))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; rfl
  · simp only [href, Bool.false_eq_true, ↓reduceIte,
      run_liftH_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨vrRes, h'⟩, _, hmem⟩ := hmem
    rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; rfl
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; rfl
    · by_cases hqep : qep + 1 < t'
      · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; rfl
      · simp only [hqep, ↓reduceIte] at hmem
        by_cases htriv : DeliverForge.trivB1 tStar es.g ⟨P.other, t', i'⟩
        · simp only [htriv, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨cmRes, es''⟩, hcm, hmem⟩ := hmem
          have ⟨hEs'', hAcc⟩ := commitE_b_eq hk { es with h := h' } es.g P (es.g.st P) st'
            ⟨P.other, t', i'⟩ (cmRes, es'') hcm
          rcases cmRes with _ | s₁
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hEs''
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hAcc s₁ rfl
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
          by_cases hf : cfg.injectFull t' <;>
            (simp only [hf, ↓reduceIte, Bool.false_eq_true, StateT.run_bind, StateT.run_modify,
               StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff,
               Prod.mk.injEq] at hmem;
             rcases hmem with ⟨_, rfl⟩; rfl)

theorem deliverForgeEB1_b_eq [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {qep tStar : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × (Header T × E) × (Header T × E)) :
    ∀ res ∈ support ((DeliverForge.deliverForgeEB1 hk qep tStar cfg arg).run es),
      res.2.g.b = es.g.b := by
  rcases arg with ⟨P, c, c'⟩
  intro ⟨out, es'⟩ hmem
  unfold DeliverForge.deliverForgeEB1 abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; rfl
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases htr : es.g.inTransit P.other c with _ | r
    · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; rfl
    · simp only [htr] at hmem
      by_cases hbad :
          ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1)
      · simp only [hbad, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; rfl
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte,
          run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vrRes, h'⟩, _, hmem⟩ := hmem
        rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; rfl
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; rfl
        · by_cases hqep : (decide (qep + 1 < t') || (t' != r.pos.epoch))
          · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; rfl
          · simp only [hqep, Bool.false_eq_true, ↓reduceIte] at hmem
            by_cases htriv : DeliverForge.trivB1 tStar es.g ⟨P.other, t', i'⟩
            · simp only [htriv, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
              obtain ⟨⟨cmRes, es''⟩, hcm, hmem⟩ := hmem
              have ⟨hEs'', hAcc⟩ := commitE_b_eq hk { es with h := h' } es.g P (es.g.st P) st'
                ⟨P.other, t', i'⟩ (cmRes, es'') hcm
              rcases cmRes with _ | s₁
              · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
                  Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hEs''
              · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                  support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hAcc s₁ rfl
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
              by_cases hf : cfg.injectFull t' <;>
                (simp only [hf, ↓reduceIte, Bool.false_eq_true, StateT.run_bind, StateT.run_modify,
                   StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff,
                   Prod.mk.injEq] at hmem;
                 rcases hmem with ⟨_, rfl⟩; rfl)

/-- Unified `b1 : Bool` shallow `inject` handler (`b1 = true` uses `trivB1 tStar` with `Δ = 2`,
`b1 = false` uses `s.trivial Δ pos`). -/
def injectEGen {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {Γ T Sig SS RS M CCoins E HS Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (b1 : Bool) (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep tStar : ℕ) (cfg : SM.Config M) :
    QueryImpl ((Party × (Header T × E)) →ₒ Option (SM.RecvResult M))
      (EM tspec Γv T Sv SSv RSv M E HS) :=
  if b1 then DeliverForge.injectEB1 hk qep tStar cfg else injectE hk Δ qep cfg

def deliverForgeEGen {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {Γ T Sig SS RS M CCoins E HS Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (b1 : Bool) (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep tStar : ℕ) (cfg : SM.Config M) :
    QueryImpl ((Party × (Header T × E) × (Header T × E)) →ₒ Option (SM.RecvResult M))
      (EM tspec Γv T Sv SSv RSv M E HS) :=
  if b1 then DeliverForge.deliverForgeEB1 hk qep tStar cfg
  else DeliverForge.deliverForgeE hk Δ qep cfg

section UnifiedCostedHandlers

variable
  {ckaInitA : KC → Γ} {ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I} {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E}

local notation "OO" =>
  ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

def injectECGen
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (b1 : Bool) (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L Δ qep tStar : ℕ) (cfg : ConfigEC OO)
    {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO Γ' (.prod .bool hdrCtTy)) :
    Comp OO I' Γ'
      (.prod (.opt rrTy)
        (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)) :=
  if b1 then injectECB1 hk L qep tStar cfg es arg else injectEC hk L Δ qep cfg es arg

def deliverForgeECGen
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (b1 : Bool) (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L Δ qep tStar : ℕ) (cfg : ConfigEC OO)
    {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO Γ' (.prod .bool (.prod hdrCtTy hdrCtTy))) :
    Comp OO I' Γ'
      (.prod (.opt rrTy)
        (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)) :=
  if b1 then deliverForgeECB1 hk L qep tStar cfg es arg else deliverForgeEC hk L Δ qep cfg es arg

theorem injectECGen_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (b1 : Bool) (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    (L Δ qep tStar : ℕ) (cfgC : ConfigEC OO) (cfg : Config M)
    (hCfg : ConfigECAgrees cfgC cfg)
    (heqT : eqT = (· == ·))
    (heqE : eqE = (· == ·))
    {Γ'} (esE : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (argE : Expr OO Γ' (.prod .bool hdrCtTy))
    (ρ : Env Γ')
    (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
    (P : Party) (c : Header T × E)
    (hHB : HBounded es.h) (hBound : SMStateBoundedEngine L es.g)
    (hVR : ∀ t v, (es.g.st P).vR t = some v → VROk v)
    (hes : esE.eval ρ = esEnc vpTblEnc hsEncFn es)
    (harg : argE.eval ρ = (partyEnc P, c)) :
    (injectECGen b1 hkC L Δ qep tStar cfgC esE argE).eval ρ =
      Prod.map (Option.map smRrEnc) (esEnc vpTblEnc hsEncFn) <$>
        (injectEGen b1 hk Δ qep tStar cfg (P, c)).run es := by
  cases b1
  · exact injectEC_eval hsEncFn HBounded hkC hk hHk L Δ qep cfgC cfg hCfg heqT heqE
      esE argE ρ es P c hHB hBound hVR hes harg
  · exact injectECB1_eval hsEncFn HBounded hkC hk hHk L qep tStar cfgC cfg hCfg heqT heqE
      esE argE ρ es P c hHB hBound hVR hes harg

theorem deliverForgeECGen_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (b1 : Bool) (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    (L Δ qep tStar : ℕ) (cfgC : ConfigEC OO) (cfg : Config M)
    (hCfg : ConfigECAgrees cfgC cfg)
    (heqT : eqT = (· == ·))
    (heqE : eqE = (· == ·))
    {Γ'} (esE : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (argE : Expr OO Γ' (.prod .bool (.prod hdrCtTy hdrCtTy)))
    (ρ : Env Γ')
    (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
    (P : Party) (c c' : Header T × E)
    (hHB : HBounded es.h) (hBound : SMStateBoundedEngine L es.g)
    (hVR : ∀ t v, (es.g.st P).vR t = some v → VROk v)
    (hes : esE.eval ρ = esEnc vpTblEnc hsEncFn es)
    (harg : argE.eval ρ = (partyEnc P, c, c')) :
    (deliverForgeECGen b1 hkC L Δ qep tStar cfgC esE argE).eval ρ =
      Prod.map (Option.map smRrEnc) (esEnc vpTblEnc hsEncFn) <$>
        (deliverForgeEGen b1 hk Δ qep tStar cfg (P, c, c')).run es := by
  cases b1
  · exact deliverForgeEC_eval hsEncFn HBounded hkC hk hHk L Δ qep cfgC cfg hCfg heqT heqE
      esE argE ρ es P c c' hHB hBound hVR hes harg
  · exact deliverForgeECB1_eval hsEncFn HBounded hkC hk hHk L qep tStar cfgC cfg hCfg heqT heqE
      esE argE ρ es P c c' hHB hBound hVR hes harg

end UnifiedCostedHandlers

theorem injectEGen_inv [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (b1 : Bool) (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {L B q Δ qep tStar : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × (Header T × E))
    (hInv : SMEngineInv L B (q + 1) es.g) :
    ∀ res ∈ support ((injectEGen b1 hk Δ qep tStar cfg arg).run es),
      SMEngineInv L B q res.2.g := by
  cases b1
  · exact injectE_inv hk cfg es arg hInv
  · exact injectEB1_inv hk cfg es arg hInv

theorem deliverForgeEGen_inv [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (b1 : Bool) (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {L B q Δ qep tStar : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × (Header T × E) × (Header T × E))
    (hInv : SMEngineInv L B (q + 1) es.g) :
    ∀ res ∈ support ((deliverForgeEGen b1 hk Δ qep tStar cfg arg).run es),
      SMEngineInv L B q res.2.g := by
  cases b1
  · exact deliverForgeE_inv hk cfg es arg hInv
  · exact deliverForgeEB1_inv hk cfg es arg hInv

theorem injectEGen_vrInv [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    {VROkStep : ℕ → rsV → Prop}
    (b1 : Bool) (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (hVRHk : HooksVRInv VROkStep hk)
    {L B q Δ qep tStar : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × (Header T × E))
    (hInv : SMEngineInv L B (q + 1) es.g)
    (hVR : SMVRInv VROkStep B (q + 1) es.g) :
    ∀ res ∈ support ((injectEGen b1 hk Δ qep tStar cfg arg).run es),
      SMVRInv VROkStep B q res.2.g := by
  cases b1
  · exact implEDFShifted_vrInv (maxSkip := 0) (Δ := Δ) (qep := qep) hk hVRHk 0 cfg
      (⟨true, none, 0⟩ : Mode).policy es (.inl (.inl (.inr arg))) hInv hVR
  · exact injectEB1_vrInv hk hVRHk cfg es arg hInv hVR

theorem deliverForgeEGen_vrInv [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    {VROkStep : ℕ → rsV → Prop}
    (b1 : Bool) (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (hVRHk : HooksVRInv VROkStep hk)
    {L B q Δ qep tStar : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × (Header T × E) × (Header T × E))
    (hInv : SMEngineInv L B (q + 1) es.g)
    (hVR : SMVRInv VROkStep B (q + 1) es.g) :
    ∀ res ∈ support ((deliverForgeEGen b1 hk Δ qep tStar cfg arg).run es),
      SMVRInv VROkStep B q res.2.g := by
  cases b1
  · exact deliverForgeE_vrInv hk hVRHk cfg es arg hInv hVR
  · exact deliverForgeEB1_vrInv hk hVRHk cfg es arg hInv hVR

theorem injectEGen_b_eq [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (b1 : Bool) (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {Δ qep tStar : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × (Header T × E)) :
    ∀ res ∈ support ((injectEGen b1 hk Δ qep tStar cfg arg).run es), res.2.g.b = es.g.b := by
  cases b1
  · exact injectE_b_eq hk cfg es arg
  · exact injectEB1_b_eq hk cfg es arg

theorem deliverForgeEGen_b_eq [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (b1 : Bool) (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {Δ qep tStar : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × (Header T × E) × (Header T × E)) :
    ∀ res ∈ support ((deliverForgeEGen b1 hk Δ qep tStar cfg arg).run es),
      res.2.g.b = es.g.b := by
  cases b1
  · exact deliverForgeE_b_eq hk cfg es arg
  · exact deliverForgeEB1_b_eq hk cfg es arg

end CryptoGames.SM.Engine

namespace CryptoGames.SM.Construction

open Engine Engine.RedPRNG CKA PRFPRNG

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

@[simp] theorem injectEB1_hooksFSL_eq [DecidableEq T] [DecidableEq I] [DecidableEq M]
    [DecidableEq E] [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L qep tStar : ℕ) (cfg : Config M) (Δcka : ℕ) (mo : Mode) (j : ℕ) :
    DeliverForge.injectEB1 (hooksFSL cka prng fs L Δcka mo j) qep tStar cfg =
      DeliverForge.injectEB1 (hooksFS cka prng fs Δcka mo j) qep tStar cfg := by
  funext q; unfold DeliverForge.injectEB1; rw [vRecv_hooksFSL_eq, commitE_hooksFSL_eq]

@[simp] theorem deliverForgeEB1_hooksFSL_eq [DecidableEq T] [DecidableEq I] [DecidableEq M]
    [DecidableEq E] [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L qep tStar : ℕ) (cfg : Config M) (Δcka : ℕ) (mo : Mode) (j : ℕ) :
    DeliverForge.deliverForgeEB1 (hooksFSL cka prng fs L Δcka mo j) qep tStar cfg =
      DeliverForge.deliverForgeEB1 (hooksFS cka prng fs Δcka mo j) qep tStar cfg := by
  funext q; unfold DeliverForge.deliverForgeEB1; rw [vRecv_hooksFSL_eq, commitE_hooksFSL_eq]

@[simp] theorem injectEGen_hooksFSL_eq [DecidableEq T] [DecidableEq I] [DecidableEq M]
    [DecidableEq E] [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (b1 : Bool) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δ qep tStar : ℕ) (cfg : Config M) (Δcka : ℕ) (mo : Mode) (j : ℕ) :
    injectEGen b1 (hooksFSL cka prng fs L Δcka mo j) Δ qep tStar cfg =
      injectEGen b1 (hooksFS cka prng fs Δcka mo j) Δ qep tStar cfg := by
  cases b1 <;> simp [injectEGen]

@[simp] theorem deliverForgeEGen_hooksFSL_eq [DecidableEq T] [DecidableEq I] [DecidableEq M]
    [DecidableEq E] [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (b1 : Bool) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δ qep tStar : ℕ) (cfg : Config M) (Δcka : ℕ) (mo : Mode) (j : ℕ) :
    deliverForgeEGen b1 (hooksFSL cka prng fs L Δcka mo j) Δ qep tStar cfg =
      deliverForgeEGen b1 (hooksFS cka prng fs Δcka mo j) Δ qep tStar cfg := by
  cases b1
  · simp only [deliverForgeEGen, Bool.false_eq_true, ↓reduceIte, deliverForgeE_hooksFSL_eq]
  · simp [deliverForgeEGen]

theorem injectEB1_fs_inv [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q qep tStar : ℕ} (cfg : Config M) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (arg : Party × (Header T × E))
    (hInv : FSEngineInv L B (q + 1) es) :
    ∀ res ∈ support
        ((DeliverForge.injectEB1 (hooksFS cka prng fs Δcka mo j) qep tStar cfg arg).run es),
      FSEngineInv L B q res.2 := by
  rcases arg with ⟨P, c⟩
  intro ⟨out, es'⟩ hmem
  have hInvQ : FSEngineInv L B q es := hInv.mono (Nat.le_succ q)
  have hSm := injectEB1_inv (hooksFS cka prng fs Δcka mo j) cfg es (P, c) hInv.sm (out, es') hmem
  unfold DeliverForge.injectEB1 abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj 2))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
    rw [run_liftH_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
    have hPres := vRecv_fs_preserve cka prng fs Δcka mo j es.g P (es.g.st P) c none es.h
      (hInv.vR_none_of_gt P) (vrRes, h') hvr
    dsimp only at hPres
    rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩
      exact ⟨hSm,
        by dsimp only; have := hInv.table_le; have := hPres.1; omega,
        by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
        by dsimp only; have := hInv.fsTrans_le; have := hPres.2.2.1; omega,
        hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩
      exact ⟨hSm,
        by dsimp only; have := hInv.table_le; have := hPres.1; omega,
        by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
        by dsimp only; have := hInv.fsTrans_le; have := hPres.2.2.1; omega,
        hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
    · by_cases hqep : qep + 1 < t'
      · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        exact ⟨hSm,
          by dsimp only; have := hInv.table_le; have := hPres.1; omega,
          by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
          by dsimp only; have := hInv.fsTrans_le; have := hPres.2.2.1; omega,
          hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
      · simp only [hqep, ↓reduceIte] at hmem
        by_cases htriv : DeliverForge.trivB1 tStar es.g ⟨P.other, t', i'⟩
        · simp only [htriv, ↓reduceIte, StateT.run_bind, commitE_fs_eq, pure_bind,
            StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          have hst' := hPres.2.2.2 st' t' i' m' rfl
          refine ⟨hSm,
            by dsimp only; have := hInv.table_le; have := hPres.1; omega,
            by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
            by dsimp only; have := hInv.fsTrans_le; have := hPres.2.2.1; omega,
            fun Q => ?_, fun Q t ht => ?_⟩
          · dsimp only [SM.GameState.accept]
            by_cases hQ : Q = P
            · subst hQ; simp only [Function.update_self]
              have := hInv.tcur_le Q; have := hst'.1; omega
            · simp only [Function.update_of_ne hQ]; exact hInvQ.tcur_le Q
          · dsimp only [SM.GameState.accept] at ht ⊢
            by_cases hQ : Q = P
            · subst hQ; simp only [Function.update_self] at ht ⊢; exact hst'.2 t ht
            · simp only [Function.update_of_ne hQ] at ht ⊢; exact hInv.vR_none_of_gt Q t ht
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
          by_cases hf : cfg.injectFull t' <;>
            (simp only [hf, ↓reduceIte, Bool.false_eq_true, StateT.run_bind, StateT.run_modify,
               StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff,
               Prod.mk.injEq] at hmem;
             rcases hmem with ⟨_, rfl⟩;
             exact ⟨hSm,
               by dsimp only; have := hInv.table_le; have := hPres.1; omega,
               by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
               by dsimp only; have := hInv.fsTrans_le; have := hPres.2.2.1; omega,
               hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩)

theorem deliverForgeEB1_fs_inv [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q qep tStar : ℕ} (cfg : Config M) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (arg : Party × (Header T × E) × (Header T × E))
    (hInv : FSEngineInv L B (q + 1) es) :
    ∀ res ∈ support
      ((DeliverForge.deliverForgeEB1 (hooksFS cka prng fs Δcka mo j) qep tStar cfg arg).run es),
      FSEngineInv L B q res.2 := by
  rcases arg with ⟨P, c, c'⟩
  intro ⟨out, es'⟩ hmem
  have hInvQ : FSEngineInv L B q es := hInv.mono (Nat.le_succ q)
  have hSm := deliverForgeEB1_inv (hooksFS cka prng fs Δcka mo j) cfg es (P, c, c') hInv.sm
    (out, es') hmem
  unfold DeliverForge.deliverForgeEB1 abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases htr : es.g.inTransit P.other c with _ | r
    · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [htr] at hmem
      by_cases hbad :
          ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1)
      · simp only [hbad, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInvQ
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte,
          run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
        have hPres := vRecv_fs_preserve cka prng fs Δcka mo j es.g P (es.g.st P) c' none es.h
          (hInv.vR_none_of_gt P) (vrRes, h') hvr
        dsimp only at hPres
        rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          exact ⟨hSm,
            by dsimp only; have := hInv.table_le; have := hPres.1; omega,
            by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
            by dsimp only; have := hInv.fsTrans_le; have := hPres.2.2.1; omega,
            hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          exact ⟨hSm,
            by dsimp only; have := hInv.table_le; have := hPres.1; omega,
            by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
            by dsimp only; have := hInv.fsTrans_le; have := hPres.2.2.1; omega,
            hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
        · by_cases hqep : (decide (qep + 1 < t') || (t' != r.pos.epoch))
          · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩
            exact ⟨hSm,
              by dsimp only; have := hInv.table_le; have := hPres.1; omega,
              by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
              by dsimp only; have := hInv.fsTrans_le; have := hPres.2.2.1; omega,
              hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
          · simp only [hqep, Bool.false_eq_true, ↓reduceIte] at hmem
            by_cases htriv : DeliverForge.trivB1 tStar es.g ⟨P.other, t', i'⟩
            · simp only [htriv, ↓reduceIte, StateT.run_bind, commitE_fs_eq, pure_bind,
                StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩
              have hst' := hPres.2.2.2 st' t' i' m' rfl
              refine ⟨hSm,
                by dsimp only; have := hInv.table_le; have := hPres.1; omega,
                by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
                by dsimp only; have := hInv.fsTrans_le; have := hPres.2.2.1; omega,
                fun Q => ?_, fun Q t ht => ?_⟩
              · dsimp only [SM.GameState.accept]
                by_cases hQ : Q = P
                · subst hQ; simp only [Function.update_self]
                  have := hInv.tcur_le Q; have := hst'.1; omega
                · simp only [Function.update_of_ne hQ]; exact hInvQ.tcur_le Q
              · dsimp only [SM.GameState.accept] at ht ⊢
                by_cases hQ : Q = P
                · subst hQ; simp only [Function.update_self] at ht ⊢; exact hst'.2 t ht
                · simp only [Function.update_of_ne hQ] at ht ⊢; exact hInv.vR_none_of_gt Q t ht
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
              by_cases hf : cfg.injectFull t' <;>
                (simp only [hf, ↓reduceIte, Bool.false_eq_true, StateT.run_bind, StateT.run_modify,
                   StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff,
                   Prod.mk.injEq] at hmem;
                 rcases hmem with ⟨_, rfl⟩;
                 exact ⟨hSm,
                   by dsimp only; have := hInv.table_le; have := hPres.1; omega,
                   by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
                   by dsimp only; have := hInv.fsTrans_le; have := hPres.2.2.1; omega,
                   hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩)

theorem injectEGen_fs_inv [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (b1 : Bool) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q Δ qep tStar : ℕ} (cfg : Config M) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (arg : Party × (Header T × E))
    (hInv : FSEngineInv L B (q + 1) es) :
    ∀ res ∈ support ((injectEGen b1 (hooksFS cka prng fs Δcka mo j) Δ qep tStar cfg arg).run es),
      FSEngineInv L B q res.2 := by
  cases b1
  · exact injectE_fs_inv cka prng fs cfg Δcka mo j es arg hInv
  · exact injectEB1_fs_inv cka prng fs cfg Δcka mo j es arg hInv

theorem deliverForgeEGen_fs_inv [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (b1 : Bool) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q Δ qep tStar : ℕ} (cfg : Config M) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (arg : Party × (Header T × E) × (Header T × E))
    (hInv : FSEngineInv L B (q + 1) es) :
    ∀ res ∈ support
      ((deliverForgeEGen b1 (hooksFS cka prng fs Δcka mo j) Δ qep tStar cfg arg).run es),
      FSEngineInv L B q res.2 := by
  cases b1
  · exact deliverForgeE_fs_inv cka prng fs cfg Δcka mo j es arg hInv
  · exact deliverForgeEB1_fs_inv cka prng fs cfg Δcka mo j es arg hInv

section FromAEADPRGB1

variable {MK C : Type}

theorem injectEB1_fsClamp_eq [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C]
    [Inhabited C] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip B B_q q Δcka qep tStar : ℕ)
    (cfg : Config M) (mo : Mode) (j : ℕ)
    (hB : (B_q + 1) * (maxSkip + 1) ≤ B)
    (es : EState (VP Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK))) M (Header T × (ℕ × C))
      (FSState T RSt K I (FSAEAD.RatchetSenderState K)
        (FSAEAD.RatchetReceiverState K MK) (ℕ × C)))
    (arg : Party × (Header T × (ℕ × C)))
    (hVR : SMVRInv (FSVROkStep maxSkip) B_q (q + 1) es.g)
    (hExt : FSVROkStep maxSkip (B_q - (q + 1)) (es.h.ext.map Prod.snd)) :
    (DeliverForge.injectEB1
        (hooksFS cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo j)
        qep tStar cfg arg).run es =
      (DeliverForge.injectEB1
        (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
        qep tStar cfg arg).run es := by
  have hkB : (B_q - (q + 1) + 1) * (maxSkip + 1) ≤ B :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB
  rcases arg with ⟨P, c⟩
  unfold DeliverForge.injectEB1
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj 2))
  · simp [href]
  · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind]
    rw [vRecv_fsClamp_eq cka prng ae G maxSkip B (B_q - (q + 1)) Δcka mo j hkB
      es.g P (es.g.st P) c none es.h (hVR P) hExt]
    rfl

theorem deliverForgeEB1_fsClamp_eq [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C]
    [Inhabited C] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip B B_q q Δcka qep tStar : ℕ)
    (cfg : Config M) (mo : Mode) (j : ℕ)
    (hB : (B_q + 1) * (maxSkip + 1) ≤ B)
    (es : EState (VP Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK))) M (Header T × (ℕ × C))
      (FSState T RSt K I (FSAEAD.RatchetSenderState K)
        (FSAEAD.RatchetReceiverState K MK) (ℕ × C)))
    (arg : Party × (Header T × (ℕ × C)) × (Header T × (ℕ × C)))
    (hVR : SMVRInv (FSVROkStep maxSkip) B_q (q + 1) es.g)
    (hExt : FSVROkStep maxSkip (B_q - (q + 1)) (es.h.ext.map Prod.snd)) :
    (DeliverForge.deliverForgeEB1
        (hooksFS cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo j)
        qep tStar cfg arg).run es =
      (DeliverForge.deliverForgeEB1
        (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
        qep tStar cfg arg).run es := by
  have hkB : (B_q - (q + 1) + 1) * (maxSkip + 1) ≤ B :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB
  rcases arg with ⟨P, c, c'⟩
  unfold DeliverForge.deliverForgeEB1
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte]
  · simp only [hab, Bool.false_eq_true, ↓reduceIte]
    rcases htr : es.g.inTransit P.other c with _ | r
    · rfl
    · dsimp only
      by_cases hbad :
          ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1)
      · simp only [hbad, ↓reduceIte]
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte, run_liftH_bind]
        rw [vRecv_fsClamp_eq cka prng ae G maxSkip B (B_q - (q + 1)) Δcka mo j hkB
          es.g P (es.g.st P) c' none es.h (hVR P) hExt]
        rfl

theorem injectEB1_ext_snd [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C]
    [Inhabited C] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip k Δcka qep tStar : ℕ)
    (cfg : Config M) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK))) M (Header T × (ℕ × C))
      (FSState T RSt K I (FSAEAD.RatchetSenderState K)
        (FSAEAD.RatchetReceiverState K MK) (ℕ × C)))
    (arg : Party × (Header T × (ℕ × C)))
    (hVR : ∀ P t₀ v, (es.g.st P).vR t₀ = some v → FSVROkStep maxSkip k v)
    (hExt : FSVROkStep maxSkip k (es.h.ext.map Prod.snd)) :
    ∀ res ∈ support
      ((DeliverForge.injectEB1
        (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
        qep tStar cfg arg).run es),
      FSVROkStep maxSkip (k + 1) (res.2.h.ext.map Prod.snd) := by
  have hExt1 : FSVROkStep maxSkip (k + 1) (es.h.ext.map Prod.snd) := hExt.mono (Nat.le_succ k)
  rcases arg with ⟨P, c⟩
  intro ⟨out, es'⟩ hmem
  unfold DeliverForge.injectEB1 abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj 2))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hExt1
  · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
    have hExt' := vRecv_ext_snd cka prng ae G maxSkip k Δcka mo j
      es.g P (es.g.st P) c none es.h (hVR P) hExt (vrRes, h') hvr
    rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hExt'
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hExt'
    · by_cases hqep : qep + 1 < t'
      · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hExt'
      · simp only [hqep, ↓reduceIte] at hmem
        by_cases htriv : DeliverForge.trivB1 tStar es.g ⟨P.other, t', i'⟩
        · simp only [htriv, ↓reduceIte, StateT.run_bind, commitE_fs_eq, pure_bind,
            StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hExt'
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
          split_ifs at hmem <;>
            (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
               support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
             rcases hmem with ⟨_, rfl⟩; exact hExt')

theorem deliverForgeEB1_ext_snd [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C]
    [Inhabited C] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip k Δcka qep tStar : ℕ)
    (cfg : Config M) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK))) M (Header T × (ℕ × C))
      (FSState T RSt K I (FSAEAD.RatchetSenderState K)
        (FSAEAD.RatchetReceiverState K MK) (ℕ × C)))
    (arg : Party × (Header T × (ℕ × C)) × (Header T × (ℕ × C)))
    (hVR : ∀ P t₀ v, (es.g.st P).vR t₀ = some v → FSVROkStep maxSkip k v)
    (hExt : FSVROkStep maxSkip k (es.h.ext.map Prod.snd)) :
    ∀ res ∈ support
      ((DeliverForge.deliverForgeEB1
        (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
        qep tStar cfg arg).run es),
      FSVROkStep maxSkip (k + 1) (res.2.h.ext.map Prod.snd) := by
  have hExt1 : FSVROkStep maxSkip (k + 1) (es.h.ext.map Prod.snd) := hExt.mono (Nat.le_succ k)
  rcases arg with ⟨P, c, c'⟩
  intro ⟨out, es'⟩ hmem
  unfold DeliverForge.deliverForgeEB1 abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hExt1
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases htr : es.g.inTransit P.other c with _ | r
    · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hExt1
    · simp only [htr] at hmem
      by_cases hbad :
          ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1)
      · simp only [hbad, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hExt1
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
          mem_support_bind_iff] at hmem
        obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
        have hExt' := vRecv_ext_snd cka prng ae G maxSkip k Δcka mo j
          es.g P (es.g.st P) c' none es.h (hVR P) hExt (vrRes, h') hvr
        rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hExt'
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hExt'
        · by_cases hqep : (decide (qep + 1 < t') || (t' != r.pos.epoch))
          · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hExt'
          · simp only [hqep, Bool.false_eq_true, ↓reduceIte] at hmem
            by_cases htriv : DeliverForge.trivB1 tStar es.g ⟨P.other, t', i'⟩
            · simp only [htriv, ↓reduceIte, StateT.run_bind, commitE_fs_eq, pure_bind,
                StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact hExt'
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
              split_ifs at hmem <;>
                (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                   support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
                 rcases hmem with ⟨_, rfl⟩; exact hExt')

theorem qb_injectEB1_one
    {Q : (ReductionsQueries.RSpec SS RS T M E).Domain → Prop} [DecidablePred Q]
    (hQu : ∀ u, ¬ Q (.inl u))
    [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep tStar : ℕ)
    (cfg : Config M) (mo : Mode) (j : ℕ)
    (q : Party × (Header T × E)) :
    ReductionsQueries.QB Q
      (DeliverForge.injectEB1 (hooksFS cka prng fs Δcka mo j) qep tStar cfg q) 1 := by
  rcases q with ⟨P, c⟩
  unfold DeliverForge.injectEB1
  refine ReductionsQueries.qb_bind0 ReductionsQueries.qb_get fun es => ?_
  dsimp only
  by_cases href :
      (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj 2)) = true
  · simp only [href, ↓reduceIte]
    exact ReductionsQueries.qb_pure none 1
  · simp only [href, Bool.false_eq_true, ↓reduceIte]
    refine ReductionsQueries.qb_bind_r
      (ReductionsQueries.qb_liftH
        (ReductionsQueries.qb_vRecv_one hQu cka prng fs Δcka mo j es.g P (es.g.st P) c none))
      fun res => ?_
    cases res with
    | none => exact ReductionsQueries.qb_bind0 ReductionsQueries.qb_abortE fun _ =>
        ReductionsQueries.qb_pure none 0
    | some inner =>
      cases inner with
      | none => exact ReductionsQueries.qb_pure (some RecvResult.rejected) 0
      | some stim =>
        rcases stim with ⟨st', t', i', m'⟩
        dsimp only
        by_cases h2 : qep + 1 < t'
        · simp only [h2, ↓reduceIte]
          exact ReductionsQueries.qb_pure (some RecvResult.rejected) 0
        · simp only [h2, ↓reduceIte]
          by_cases h3 : DeliverForge.trivB1 tStar es.g ⟨P.other, t', i'⟩ = true
          · simp only [h3, ↓reduceIte]
            refine ReductionsQueries.qb_bind0
              (ReductionsQueries.qb_commitE cka prng fs Δcka mo j es.g P (es.g.st P) st'
                ⟨P.other, t', i'⟩)
              fun s₁? => ?_
            cases s₁? with
            | none => exact ReductionsQueries.qb_pure none 0
            | some s₁ =>
              exact ReductionsQueries.qb_bind0 (ReductionsQueries.qb_modify _) fun _ =>
                ReductionsQueries.qb_pure _ 0
          · simp only [h3, Bool.false_eq_true, ↓reduceIte]
            split_ifs
            · exact ReductionsQueries.qb_bind0 (ReductionsQueries.qb_modify _) fun _ =>
                ReductionsQueries.qb_pure (some RecvResult.rejected) 0
            · exact ReductionsQueries.qb_pure (some RecvResult.rejected) 0

theorem qb_deliverForgeEB1_one
    {Q : (ReductionsQueries.RSpec SS RS T M E).Domain → Prop} [DecidablePred Q]
    (hQu : ∀ u, ¬ Q (.inl u))
    [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep tStar : ℕ)
    (cfg : Config M) (mo : Mode) (j : ℕ)
    (q : Party × (Header T × E) × (Header T × E)) :
    ReductionsQueries.QB Q
      (DeliverForge.deliverForgeEB1 (hooksFS cka prng fs Δcka mo j) qep tStar cfg q) 1 := by
  rcases q with ⟨P, c, c'⟩
  unfold DeliverForge.deliverForgeEB1
  refine ReductionsQueries.qb_bind0 ReductionsQueries.qb_get fun es => ?_
  dsimp only
  by_cases hab : (es.abort || es.g.win) = true
  · simp only [hab, ↓reduceIte]
    exact ReductionsQueries.qb_pure none 1
  · simp only [hab, Bool.false_eq_true, ↓reduceIte]
    rcases htr : es.g.inTransit P.other c with _ | r
    · exact ReductionsQueries.qb_pure none 1
    · dsimp only
      by_cases hbad :
          ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1) = true
      · simp only [hbad, ↓reduceIte]
        exact ReductionsQueries.qb_pure none 1
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte]
        refine ReductionsQueries.qb_bind_r
          (ReductionsQueries.qb_liftH
            (ReductionsQueries.qb_vRecv_one hQu cka prng fs Δcka mo j es.g P (es.g.st P) c' none))
          fun res => ?_
        cases res with
        | none => exact ReductionsQueries.qb_bind0 ReductionsQueries.qb_abortE fun _ =>
            ReductionsQueries.qb_pure none 0
        | some inner =>
          cases inner with
          | none => exact ReductionsQueries.qb_pure (some RecvResult.rejected) 0
          | some stim =>
            rcases stim with ⟨st', t', i', m'⟩
            dsimp only
            by_cases h2 : (decide (qep + 1 < t') || (t' != r.pos.epoch)) = true
            · simp only [h2, ↓reduceIte]
              exact ReductionsQueries.qb_pure (some RecvResult.rejected) 0
            · simp only [h2, Bool.false_eq_true, ↓reduceIte]
              by_cases h3 : DeliverForge.trivB1 tStar es.g ⟨P.other, t', i'⟩ = true
              · simp only [h3, ↓reduceIte]
                refine ReductionsQueries.qb_bind0
                  (ReductionsQueries.qb_commitE cka prng fs Δcka mo j es.g P (es.g.st P) st'
                    ⟨P.other, t', i'⟩)
                  fun s₁? => ?_
                cases s₁? with
                | none => exact ReductionsQueries.qb_pure none 0
                | some s₁ =>
                  exact ReductionsQueries.qb_bind0 (ReductionsQueries.qb_modify _) fun _ =>
                    ReductionsQueries.qb_pure _ 0
              · simp only [h3, Bool.false_eq_true, ↓reduceIte]
                split_ifs
                · exact ReductionsQueries.qb_bind0 (ReductionsQueries.qb_modify _) fun _ =>
                    ReductionsQueries.qb_pure (some RecvResult.rejected) 0
                · exact ReductionsQueries.qb_pure (some RecvResult.rejected) 0

end FromAEADPRGB1

end CryptoGames.SM.Construction
