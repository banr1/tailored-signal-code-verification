/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeCKA
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePRNG
public import Computational.Proofs.SpecLemmas.Session.ACD19.SM.CostedTables
public import ProofLib.Lemmas
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma9
import ProofLib.SepLogic.WP.StateNorm

/-!
# Healing-Epoch Boundary Authenticity (`Dir2`)

Defines the K4-free healing-epoch authenticity predicate `authOKDir2`, the CKA synchronization
invariant `Sync9Dir2` at `(some l, l + 2)` (`Δ_CKA = 1`, `Δ_eng = 2`), and the `NoBadCoinsDF`
adversary predicate.
-/

@[expose] public section

open OracleSpec OracleComp MeasureTheory
open scoped ENNReal BigOperators

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.SM
open CryptoGames.SM.Construction

/-- Authenticity predicate at `Δ = 2` requiring `SM.authLosingConditionsAvoided 2 tL tStar s` and
no sender corruption at `tStar`. -/
def authOKDir2 {St Msg C : Type} (tL : Option ℕ) (tStar : ℕ) (s : SM.GameState St Msg C) : Bool :=
  SM.authLosingConditionsAvoided 2 tL tStar s && !s.corrs.contains (Party.senderOf tStar, tStar)

end CryptoGames.LibsignalSM.Proofs.Refinement

namespace CryptoGames.SM.Construction.DeliverForge

open CryptoGames.SM
open CryptoGames.SM.Engine
open CryptoGames.SM.Construction
open CryptoGames.LibsignalSM.Proofs.Refinement

variable {KC Γ CCoins T I KR Sig K SS RS M E : Type}
  [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
  [Inhabited E]
  [SampleableType KC] [SampleableType CCoins] [SampleableType KR]
  [SampleableType I] [SampleableType K]

end CryptoGames.SM.Construction.DeliverForge

namespace CryptoGames.SM.Construction.AuthL9DFDir2

open CryptoGames.SM
open CryptoGames.SM.Engine
open CryptoGames.SM.Construction
open CryptoGames.SM.Construction.AuthL9
open CryptoGames.SM.Construction.DeliverForge
open CryptoGames.SM.Construction.DeliverForge.AuthL9DF
open CryptoGames.LibsignalSM.Proofs.Refinement

variable {KC Γ CCoins T I KR Sig K SS RS M E : Type}
  [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
  [Inhabited E]
  [SampleableType KC] [SampleableType CCoins] [SampleableType KR]
  [SampleableType I] [SampleableType K]

lemma healedBy_three_of_healedBy_two {tL : Option ℕ} {t : ℕ}
    (h : healedBy tL 2 t = false) : healedBy tL (2 + 1) t = false := by
  cases tL with
  | none => nomatch h
  | some m =>
    simp only [healedBy, decide_eq_false_iff_not] at h ⊢
    omega

def clearMetaG {St Msg C : Type} (g : GameState St Msg C) : GameState St Msg C :=
  { g with tL := none, comp := [], leaks := [] }

def clearMetaE {VPt Msg C HS : Type} (es : EState VPt Msg C HS) : EState VPt Msg C HS :=
  { es with g := clearMetaG es.g }

/-- CKA synchronization invariant at `(some l, l + 2)` (`Δ_CKA = 1`, `Δ_eng = 2`), pairing `Sync9`
at `(some l, l + 3)` with two-epoch unhealedness of compromised records. -/
structure Sync9Dir2 (cka : CKAScheme KC Γ CCoins T I) (l : ℕ)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E))
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (sc : CKA.GameState Γ T) : Prop where
  base : Sync9 cka 1 (some l) (l + 3) s es sc
  comp_unhealed2 : ∀ pos ∈ es.g.comp, healedBy es.g.tL 2 pos.epoch = false

namespace Sync9Dir2

variable {cka : CKAScheme KC Γ CCoins T I} {l : ℕ}
  {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
  {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
  {sc : CKA.GameState Γ T}

omit [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
  [Inhabited E] [SampleableType KC] [SampleableType CCoins] [SampleableType I] in
lemma sync9_clearMeta (hs : Sync9 cka 1 (some l) (l + 3) s es sc) :
    Sync9 cka 1 (some l) (l + 3) (clearMetaG s) (clearMetaE es) sc where
  valid := hs.valid
  s_eq := by rw [hs.s_eq]; rfl
  no_abort := hs.no_abort
  b_eq := hs.b_eq
  sc_b := hs.sc_b
  st_id := hs.st_id
  st_tcur := hs.st_tcur
  γ_eq := hs.γ_eq
  sc_epoch := hs.sc_epoch
  tL_none := fun _ => rfl
  tL_some := fun _ hm => by nomatch hm
  leaks_ub := fun _ hx => by nomatch hx
  comp_unhealed := fun _ hpos => by nomatch hpos
  epoch_le := hs.epoch_le
  epoch_step_sends := hs.epoch_step_sends
  trans_inv := hs.trans_inv
  cache_gt := hs.cache_gt
  cka_eq := hs.cka_eq
  cka_step := hs.cka_step

omit [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
  [Inhabited E] [SampleableType KC] [SampleableType CCoins] [SampleableType I] in
lemma of_clearMeta
    (hc : Sync9 cka 1 (some l) (l + 3) (clearMetaG s) (clearMetaE es) sc)
    (htL_eq : s.tL = es.g.tL) (hcomp_eq : s.comp = es.g.comp) (hleaks_eq : s.leaks = es.g.leaks)
    (htL_none : es.g.tL = none → es.g.leaks = [])
    (htL_some : ∀ m, es.g.tL = some m → m ∈ es.g.leaks ∧ ∀ x ∈ es.g.leaks, x ≤ m)
    (hleaks_ub : ∀ x ∈ es.g.leaks, x ≤ max (es.g.epoch .A) (es.g.epoch .B))
    (hcomp2 : ∀ pos ∈ es.g.comp, healedBy es.g.tL 2 pos.epoch = false) :
    Sync9Dir2 cka l s es sc where
  base :=
    { valid := hc.valid
      s_eq := by
        have h := hc.s_eq
        cases s; cases es with | mk g h_st abort =>
        cases g
        dsimp only [clearMetaG, clearMetaE, realGS] at h htL_eq hcomp_eq hleaks_eq ⊢
        injection h with hst hep hidx _ htr hch _ hmax hb hwin _ hcorrs
        subst htL_eq hcomp_eq hleaks_eq hst hep hidx htr hch hmax hb hwin hcorrs
        rfl
      no_abort := hc.no_abort
      b_eq := hc.b_eq
      sc_b := hc.sc_b
      st_id := hc.st_id
      st_tcur := hc.st_tcur
      γ_eq := hc.γ_eq
      sc_epoch := hc.sc_epoch
      tL_none := htL_none
      tL_some := htL_some
      leaks_ub := hleaks_ub
      comp_unhealed := fun pos hpos => healedBy_three_of_healedBy_two (hcomp2 pos hpos)
      epoch_le := hc.epoch_le
      epoch_step_sends := hc.epoch_step_sends
      trans_inv := hc.trans_inv
      cache_gt := hc.cache_gt
      cka_eq := hc.cka_eq
      cka_step := hc.cka_step }
  comp_unhealed2 := hcomp2

theorem sync9_win (hs : Sync9Dir2 cka l s es sc) (w : Bool) :
    Sync9Dir2 cka l { s with win := w } { es with g := { es.g with win := w } } sc :=
  ⟨hs.base.sync9_win w, hs.comp_unhealed2⟩

theorem sync9_accept_same (hs : Sync9Dir2 cka l s es sc) {P : Party}
    (vR' : ℕ → Option RS) {pos : Pos} (hpos_le : pos.epoch ≤ es.g.epoch P) :
    let st_v' := { es.g.st P with vR := vR' }
    let st_r' := { s.st P with vR := vR' }
    Sync9Dir2 cka l (s.accept P st_r' pos) { es with g := es.g.accept P st_v' pos } sc := by
  intro st_v' st_r'
  refine ⟨hs.base.sync9_accept_same vR' hpos_le, fun pos' hpos' => ?_⟩
  simp only [GameState.accept, GameState.delete, List.mem_filter] at hpos'
  exact hs.comp_unhealed2 pos' hpos'.1

theorem sync9_accept_new (hs : Sync9Dir2 cka l s es sc) {P : Party}
    (σ' : Sig) (vR' : ℕ → Option RS) {pos : Pos}
    (ht : pos.epoch = es.g.epoch P + 1)
    (heq_other : es.g.epoch P + 1 = es.g.epoch P.other)
    (hnsend : P.sendsIn pos.epoch = false)
    (T_t : T)
    (hagr_step : ∀ rs, cka.AgreesFrom (cka.receive (s.st P).γ T_t).1 (s.st P.other).γ rs) :
    let t := pos.epoch
    let γ_r' := (cka.receive (s.st P).γ T_t).1
    let γ_v' : Option Γ := if isLocal (some l) 1 t then some γ_r' else none
    let st_v' : PartyState (Option Γ) T Sig SS RS :=
      { es.g.st P with tcur := t, γ := γ_v', root := σ', vR := vR' }
    let st_r' : PartyState Γ T Sig SS RS :=
      { s.st P with tcur := t, γ := γ_r', root := σ', vR := vR' }
    let sc' : CKA.GameState Γ T :=
      if isLocal (some l) 1 (es.g.epoch P) then sc else sc.afterReceive P γ_r'
    Sync9Dir2 cka l (s.accept P st_r' pos) { es with g := es.g.accept P st_v' pos } sc' := by
  intro t γ_r' γ_v' st_v' st_r' sc'
  refine ⟨hs.base.sync9_accept_new σ' vR' ht heq_other hnsend T_t hagr_step, fun pos' hpos' => ?_⟩
  simp only [GameState.accept, GameState.delete, List.mem_filter] at hpos'
  exact hs.comp_unhealed2 pos' hpos'.1

theorem sync9_send_same (hs : Sync9Dir2 cka l s es sc) {P : Party}
    (hnsend : P.sendsIn (es.g.epoch P + 1) = false) (vS' : Option SS) (m : M) (e : E)
    (isChall : Bool) :
    let h : Header T := (es.g.epoch P, (es.g.st P).curCkaMsg)
    let st_v' := { es.g.st P with vS := vS' }
    let st_r' := { s.st P with vS := vS' }
    let rec_P : Record M (Header T × E) := ⟨⟨P, es.g.epoch P, es.g.idx P + 1⟩, m, (h, e)⟩
    Sync9Dir2 cka l
      (s.record 2 P st_r' rec_P isChall)
      { es with g := es.g.record 2 P st_v' rec_P isChall }
      sc := by
  intro h st_v' st_r' rec_P
  refine of_clearMeta
    ((sync9_clearMeta hs.base).sync9_send_same hnsend vS' m e isChall)
    (by rw [hs.base.s_eq]; rfl) (by rw [hs.base.s_eq]; rfl) (by rw [hs.base.s_eq]; rfl)
    hs.base.tL_none hs.base.tL_some hs.base.leaks_ub ?_
  intro pos hpos
  simp only [GameState.record] at hpos ⊢
  split_ifs at hpos with hsafe
  · exact hs.comp_unhealed2 pos hpos
  · simp only [List.mem_cons] at hpos
    rcases hpos with rfl | hpos
    · simpa [GameState.safeCh] using hsafe
    · exact hs.comp_unhealed2 pos hpos

omit [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
  [Inhabited E] [SampleableType KC] [SampleableType CCoins] [SampleableType I] in
theorem epMgmt_tL_inv (hs : Sync9Dir2 cka l s es sc) {qep : ℕ} {P : Party} {bad : Bool}
    {s₁ : GameState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)}
    (hep : es.g.epMgmt 2 qep P bad = some s₁) :
    s₁.win = es.g.win ∧ s₁.trans = es.g.trans ∧ s₁.comp = es.g.comp ∧
    (s₁.tL = none → s₁.leaks = []) ∧
    (∀ m, s₁.tL = some m → m ∈ s₁.leaks ∧ ∀ x ∈ s₁.leaks, x ≤ m) := by
  by_cases h1 : P.sendsIn (es.g.epoch P + 1) = true
  · have h2 : ¬qep < es.g.epoch P + 1 := by intro h; simp [GameState.epMgmt, h1, h] at hep
    by_cases h3 : (bad && !(es.g.safeCh 2 P)) = true
    · simp only [GameState.epMgmt, h1, h2, h3, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      refine ⟨rfl, rfl, rfl, by simp [GameState.leak], ?_⟩
      intro m hm
      simp only [GameState.leak, Option.some.injEq] at hm
      subst hm
      refine ⟨by simp [GameState.leak], ?_⟩
      intro x hx
      simp only [GameState.leak, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact le_rfl
      · cases hstL : es.g.tL with
        | none =>
          rw [hs.base.tL_none hstL] at hx
          nomatch hx
        | some m₀ =>
          have hle := (hs.base.tL_some m₀ hstL).2 x hx
          simp [maxOpt]
          omega
    · simp only [Bool.not_eq_true] at h3
      simp [GameState.epMgmt, h1, h2, h3] at hep
      subst hep
      exact ⟨rfl, rfl, rfl, hs.base.tL_none, hs.base.tL_some⟩
  · simp only [Bool.not_eq_true] at h1
    have h2 : ¬qep < es.g.epoch P := by intro h; simp [GameState.epMgmt, h1, h] at hep
    simp [GameState.epMgmt, h1, h2] at hep
    subst hep
    exact ⟨rfl, rfl, rfl, hs.base.tL_none, hs.base.tL_some⟩

theorem sync9_send_new (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (hs : Sync9Dir2 cka l s es sc) {qep : ℕ} {P : Party} {bad : Bool}
    (hsend : P.sendsIn (es.g.epoch P + 1) = true)
    {s₁ : GameState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)}
    (hep : es.g.epMgmt 2 qep P bad = some s₁)
    (coins : CCoins) (m : M) (isChall : Bool) :
    let t := es.g.epoch P + 1
    let c_cka := cka.send (s.st P).γ coins
    let p := prng.up (es.g.st P).root c_cka.2.2
    let ss := fs.initSender p.2
    let h : Header T := (t, some c_cka.2.1)
    let out_fs := fs.send ss h m
    let γv' : Option Γ := if isLocal (some l) 1 t then some c_cka.1 else none
    let st_v' : PartyState (Option Γ) T Sig SS RS :=
      { es.g.st P with tcur := t, γ := γv', curCkaMsg := some c_cka.2.1, root := p.1,
                       vS := some out_fs.1 }
    let st_r' : PartyState Γ T Sig SS RS :=
      { s.st P with tcur := t, γ := c_cka.1, curCkaMsg := some c_cka.2.1, root := p.1,
                    vS := some out_fs.1 }
    let rec_P : Record M (Header T × E) := ⟨⟨P, t, 1⟩, m, (h, out_fs.2)⟩
    let h' : CKAState T I :=
      { cache := Function.update es.h.cache t (some (c_cka.2.1, c_cka.2.2)) }
    let sc' : CKA.GameState Γ T :=
      if isLocal (some l) 1 (es.g.epoch P) then sc else sc.afterSend P c_cka.1 c_cka.2.1
    Sync9Dir2 cka l
      ((realGS sc s₁).record 2 P st_r' rec_P isChall)
      { es with g := s₁.record 2 P st_v' rec_P isChall, h := h' }
      sc' := by
  intro t c_cka p ss h out_fs γv' st_v' st_r' rec_P h' sc'
  have heq := hs.base.epoch_eq_of_sendsIn_succ hsend
  have hq : ¬qep < es.g.epoch P + 1 := by intro hq; simp [GameState.epMgmt, hsend, hq] at hep
  obtain ⟨_, _, hcomp1, htL1, htL2⟩ := hs.epMgmt_tL_inv hep
  have hs₁_epoch : s₁.epoch = Function.update es.g.epoch P t := by
    by_cases h3 : (bad && !(es.g.safeCh 2 P)) = true
    · simp only [GameState.epMgmt, hsend, hq, h3, ↓reduceIte, Option.some.injEq] at hep
      subst hep; rfl
    · simp only [Bool.not_eq_true] at h3
      simp [GameState.epMgmt, hsend, hq, h3] at hep
      subst hep; rfl
  have hep_clear : (clearMetaE es).g.epMgmt (2 + 1) qep P false = some (clearMetaG s₁) := by
    by_cases h3 : (bad && !(es.g.safeCh 2 P)) = true
    · simp only [GameState.epMgmt, hsend, hq, h3, ↓reduceIte, Option.some.injEq] at hep
      subst hep; simp [clearMetaE, clearMetaG, GameState.epMgmt, hsend, hq, GameState.leak]
    · simp only [Bool.not_eq_true] at h3
      simp only [GameState.epMgmt, hsend, hq, h3, ↓reduceIte, Option.some.injEq] at hep
      subst hep; simp [clearMetaE, clearMetaG, GameState.epMgmt, hsend, hq]
  refine of_clearMeta
    ((sync9_clearMeta hs.base).sync9_send_new prng fs hsend hep_clear coins m isChall)
    rfl rfl rfl htL1 htL2 ?_ ?_
  · intro x hx
    simp only [GameState.record, hs₁_epoch] at hx ⊢
    have hmax1 : es.g.epoch P + 1 ≤
        max (Function.update es.g.epoch P t .A) (Function.update es.g.epoch P t .B) := by
      cases P <;> simp [Function.update, t]
    have hmax2 : max (es.g.epoch .A) (es.g.epoch .B) ≤
        max (Function.update es.g.epoch P t .A) (Function.update es.g.epoch P t .B) := by
      cases P <;> simp [Function.update, Party.other, t] at heq ⊢ <;> omega
    by_cases h3 : (bad && !(es.g.safeCh 2 P)) = true
    · simp only [GameState.epMgmt, hsend, hq, h3, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      simp only [GameState.leak, List.mem_cons] at hx
      rcases hx with rfl | hx
      · cases hstL : es.g.tL with
        | none => simp only [maxOpt]; omega
        | some m₀ =>
          have hm₀ := hs.base.leaks_ub m₀ (hs.base.tL_some m₀ hstL).1
          simp only [maxOpt]; omega
      · have hle := hs.base.leaks_ub x hx; omega
    · simp only [Bool.not_eq_true] at h3
      simp [GameState.epMgmt, hsend, hq, h3] at hep
      subst hep
      have hle := hs.base.leaks_ub x hx; omega
  · intro pos hpos
    simp only [GameState.record, hcomp1] at hpos ⊢
    have hun_pres : ∀ pos ∈ es.g.comp, healedBy s₁.tL 2 pos.epoch = false := by
      intro pos' hpos'
      have hun := hs.comp_unhealed2 pos' hpos'
      by_cases h3 : (bad && !(es.g.safeCh 2 P)) = true
      · simp only [GameState.epMgmt, hsend, hq, h3, ↓reduceIte, Option.some.injEq] at hep
        subst hep
        cases hstL : es.g.tL with
        | none => simp [hstL, healedBy] at hun
        | some m₀ =>
          simp only [hstL, healedBy, decide_eq_false_iff_not] at hun
          simp only [GameState.leak, hstL, maxOpt, healedBy, decide_eq_false_iff_not]
          omega
      · simp only [Bool.not_eq_true] at h3
        simp [GameState.epMgmt, hsend, hq, h3] at hep
        subst hep; exact hun
    split_ifs at hpos with hsafe
    · exact hun_pres pos hpos
    · simp only [List.mem_cons] at hpos
      rcases hpos with rfl | hpos
      · simpa [GameState.safeCh, realGS, hs₁_epoch, Function.update_self, rec_P] using hsafe
      · exact hun_pres pos hpos

theorem sync9_init (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (hc : cka.Correct) (kr : KR) (kc : KC) :
    let out := prng.up (prng.init kr) lam
    let γv : PartyState (Option Γ) T Sig SS RS × PartyState (Option Γ) T Sig SS RS :=
      mkParties none none out.1 (fs.initSender out.2) (fs.initReceiver out.2)
    let g₀ : Ctx (Option Γ) T Sig SS RS M E :=
      { st := fun P => match P with | .A => γv.1 | .B => γv.2, b := false }
    Sync9Dir2 cka l
      (initState (scheme cka prng fs lam) (kr, kc) false)
      { g := g₀, h := {} }
      (CKA.initState cka kc false) := by
  have hvg3 : lastLeakGuessAdmissible (2 + 1) (some l) (l + 3) = true := by
    simp [lastLeakGuessAdmissible, healedBy]
  exact ⟨Sync9.sync9_init prng fs lam hc hvg3 kr kc, fun _ hpos => by nomatch hpos⟩

end Sync9Dir2

local notation "ASpecDF" =>
  unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)

omit [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
  [Inhabited E] [SampleableType KC] [SampleableType CCoins] [SampleableType I] in
theorem trivial_false_of_safeInj_dir2 {cka : CKAScheme KC Γ CCoins T I} {l : ℕ}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9Dir2 cka l s es sc)
    (hsafe : es.g.safeInj 2 = true) {P : Party} {pos : Pos}
    (ht : es.g.epoch P < pos.epoch) :
    es.g.trivial 2 pos = false := by
  unfold GameState.safeInj at hsafe
  unfold GameState.trivial
  rw [Bool.or_eq_false_iff]
  have hmin : min (es.g.epoch .A) (es.g.epoch .B) ≤ es.g.epoch P := by
    cases P <;> simp
  have hheal : healedBy es.g.tL 2 pos.epoch = true := by
    cases htL : es.g.tL with
    | none => rfl
    | some m =>
      simp only [htL, healedBy, decide_eq_true_eq] at hsafe ⊢
      omega
  refine ⟨?_, by simp [hheal]⟩
  rw [List.contains_eq_mem, decide_eq_false_iff_not]
  intro hmem
  have hun := hs.comp_unhealed2 pos hmem
  rw [hheal] at hun
  contradiction

omit [DecidableEq I]
  [SampleableType KC] [SampleableType KR] [SampleableType I] [SampleableType K] in
theorem transmitImpl_run_eq_dir2 (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (qep : ℕ)
    {l : ℕ} {P : Party} {m : M} {r : Option CCoins}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9Dir2 cka l s es sc)
    (hw : es.g.win = false) :
    ((transmitImpl (scheme cka prng fs lam) 2 qep (P, m, r)).run s) =
      ((match r with | none => $ᵗ CCoins | some c => pure c) >>= fun coins =>
        match es.g.epMgmt 2 qep P r.isSome with
        | none => pure (none, s)
        | some s₁ =>
          let out := send cka prng fs (s.st P) m coins
          pure (some out.2,
            (realGS sc s₁).record 2 P out.1
              ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ false)) := by
  have hwin : s.win = false := by rw [hs.base.s_eq]; exact hw
  have hep : ∀ bad, s.epMgmt 2 qep P bad =
      (es.g.epMgmt 2 qep P bad).map (realGS sc) := by
    intro bad
    rw [hs.base.s_eq, realGS_epMgmt]
  have hst1 : ∀ bad s₁, es.g.epMgmt 2 qep P bad = some s₁ →
      realVP (sc.st P) (s₁.st P) = s.st P := by
    intro bad s₁ h1
    have hst_eq : s₁.st = es.g.st := by
      unfold GameState.epMgmt at h1
      split_ifs at h1 <;> (injection h1 with h1; subst h1; simp [GameState.leak])
    rw [hs.base.s_eq]
    simp [realGS, hst_eq]
  unfold transmitImpl samIfNec
  cases r with
  | none =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, Bool.false_eq_true, ↓reduceIte,
      StateT.run_monadLift, monadLift_self, bind_assoc, Option.isSome_none,
      hep false]
    refine bind_congr fun coins => ?_
    cases h1 : es.g.epMgmt 2 qep P false with
    | none => simp
    | some s₁ =>
      simp [realGS, hst1 false s₁ h1, scheme]
  | some c =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, Bool.false_eq_true, ↓reduceIte,
      StateT.run_monadLift, monadLift_self, Option.isSome_some,
      hep true]
    cases h1 : es.g.epMgmt 2 qep P true with
    | none => simp
    | some s₁ =>
      simp [realGS, hst1 true s₁ h1, scheme]

/-- Predicate asserting that an `AdversaryCompDF` computation never supplies explicit coins to a
`transmit` query. -/
inductive NoBadCoinsDF {St Msg Coins C : Type} {α : Type} :
    AdversaryCompDF St Msg Coins C α → Prop
  | pure (a : α) : NoBadCoinsDF (pure a)
  | query_bind (q : (unifSpec + specDF St Msg Coins C).Domain)
      (k : (unifSpec + specDF St Msg Coins C).Range q → AdversaryCompDF St Msg Coins C α) :
      (∀ P m r, q = Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (P, m, r)))))) →
        r = none) →
      (∀ u, NoBadCoinsDF (k u)) →
      NoBadCoinsDF (query (spec := unifSpec + specDF St Msg Coins C) q >>= k)

theorem NoBadCoinsDF.bind {St Msg Coins C α β : Type}
    {oa : AdversaryCompDF St Msg Coins C α}
    {f : α → AdversaryCompDF St Msg Coins C β}
    (hoa : NoBadCoinsDF oa) (hf : ∀ a, NoBadCoinsDF (f a)) :
    NoBadCoinsDF (oa >>= f) := by
  induction hoa with
  | pure a => simpa using hf a
  | query_bind q k hno _ ih =>
    rw [bind_assoc]
    exact NoBadCoinsDF.query_bind q (fun u => k u >>= f) hno ih

end CryptoGames.SM.Construction.AuthL9DFDir2

namespace CryptoGames.SM.Construction.DeliverForge.AuthL10DFDir2

open CryptoGames.SM
open CryptoGames.SM.Engine
open CryptoGames.SM.Construction
open CryptoGames.SM.Construction.AuthL10
open CryptoGames.SM.Construction.DeliverForge
open CryptoGames.SM.Construction.DeliverForge.AuthL10DF

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}

section Sync10Dir2Props

variable {prng : PRFPRNG KR Sig I K} {mo : Mode}
  {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
  {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}

variable [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

end Sync10Dir2Props

variable [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (qep : ℕ)

end CryptoGames.SM.Construction.DeliverForge.AuthL10DFDir2
