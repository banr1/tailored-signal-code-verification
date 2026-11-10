/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.DeliverForge
public import Computational.Proofs.HeadlineV1.DeliverForgeShifted
import Computational.Proofs.GameHop.ReductionDsl.CostUB
import Computational.Proofs.SessionCostedBase
import ProofLib.SepLogic.WP.StepsCore
import Computational.Proofs.ReductionDsl.Notation
import Computational.Proofs.ReductionDsl.Fig8SourceCosts

/-!
# Costed Shifted Reductions for `DeliverForge`

Defines the shifted engine dispatcher `implECDFShifted` and `CostedReduction` programs
`redCKAAuthDFShiftedProg`, `redPRNGAuthDFShiftedProg`, and `redFSAuthDFShiftedProg`, with
evaluation agreement, query, and cost bounds.
-/

@[expose] public section

set_option autoImplicit false

open ReductionDsl OracleSpec OracleComp
open scoped Computational.Proofs.ReductionDsl.Notation
open CryptoGames CryptoGames.CKA CryptoGames.PRFPRNG CryptoGames.FSAEAD CryptoGames.SM
open CryptoGames.SM.Engine CryptoGames.SM.Engine.RedPRNG CryptoGames.SM.Construction
open CryptoGames.SM.Construction.DeliverForge
open Computational.Proofs.ReductionDsl.Fig8SourceCosts

namespace CryptoGames.SM.Engine

local macro_rules
  | `(rdsl_pat| .transmit $p:term) => `(rdsl_pat| .inl (.inl (.inl (.inl $p))))
  | `(rdsl_pat| .challenge $p:term) => `(rdsl_pat| .inl (.inl (.inl (.inr $p))))
  | `(rdsl_pat| .deliver $p:term) => `(rdsl_pat| .inl (.inl (.inr $p)))
  | `(rdsl_pat| .inject $p:term) => `(rdsl_pat| .inl (.inr $p))
  | `(rdsl_pat| .corrupt $p:term) => `(rdsl_pat| .inr $p)

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "S" => ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "rrTy" => ckaRrTy KC Γ CCoins T I KR RSt K SS RS M E

/-! ## Shifted engine dispatch -/

def cAfterCorrShiftedE
    {O' : Ops S} {vpT : Ty S} {Γ'} (L l : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (p : Expr O' Γ' .bool) : Expr O' Γ' (cGsTy vpT) :=
  rdslExpr =>
    letE (s, p) fun (s0, p0) =>
      let comp' :=
        foldrB L (cGsTrans s0) (cGsComp s0) fun rec_ acc =>
          if boolEq (posSender (cRecPos rec_)) (otherE p0) then
            cCompInsertE acc (cRecPos rec_)
          else
            acc
      let s1 :=
        cGsMk (cGsSt s0) (cGsB s0) (cGsWin s0) (cGsEpoch s0) (cGsIdx s0) (cGsTL s0)
          (cGsTrans s0) (cGsChall s0) comp' (cGsMaxAcc s0) (cGsLeaks s0) (cGsCorrs s0)
      let maxEp := maxN (cGsEpoch s0).1 (cGsEpoch s0).2
      let eLeak :=
        if (maxEp == nat l) && leN (pGet (cGsEpoch s0) p0 + 1) (nat l) then
          nat (l - 1)
        else
          maxEp
      let s2 := cLeakE s1 eLeak
      cGsMk (cGsSt s2) (cGsB s2) (cGsWin s2) (cGsEpoch s2) (cGsIdx s2) (cGsTL s2)
        (cGsTrans s2) (cGsChall s2) (cGsComp s2) (cGsMaxAcc s2) (cGsLeaks s2)
        (cons (p0, pGet (cGsEpoch s0) p0) (cGsCorrs s2))

theorem cAfterCorrShiftedE_eval {O' : Ops S} {vpT : Ty S} {VPt : Type}
    (vpEncFn : VPt → vpT.denote) {Γ'} (L l : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (p : Expr O' Γ' .bool) (ρ : Env Γ') (st : GameState VPt M (Header T × E)) (P : Party)
    (hTrans : st.trans.length ≤ L)
    (hCompU : ∃ U : List Pos, U.length ≤ L ∧ (∀ r ∈ st.trans, r.pos ∈ U) ∧ (∀ p ∈ st.comp, p ∈ U))
    (hs_eq : s.eval ρ = cGsEnc (vpT := vpT) vpEncFn st) (hp_eq : p.eval ρ = partyEnc P) :
    (cAfterCorrShiftedE L l s p).eval ρ =
      cGsEnc (vpT := vpT) vpEncFn (afterCorrShifted l st P) := by
  let _ := hCompU
  unfold cAfterCorrShiftedE
  rw [letE_eval]
  have h0 : (Expr.pair s p).eval ρ = (cGsEnc (vpT := vpT) vpEncFn st, partyEnc P) := by
    simp [Expr.eval, hs_eq, hp_eq]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod (cGsTy vpT) .bool) (cGsEnc (vpT := vpT) vpEncFn st, partyEnc P) ρ
  have ht : (st.trans.map cRecEnc).take L = st.trans.map cRecEnc :=
    List.take_of_length_le (by simpa using hTrans)
  have hfold := foldr_cCompInsert_map (O' := O') (.snd .v2) ρ₁ P
    (fun _ _ => rfl) st.trans st.comp
  simp only [cLeakE, maxOptE, cGsMk, cGsSt, cGsB, cGsWin, cGsEpoch, cGsIdx, cGsTL,
    cGsTrans, cGsChall, cGsComp, cGsMaxAcc, cGsLeaks, cGsCorrs,
    Expr.eval, maxN_eval, leN_eval]
  have hTr0 : ((Expr.v0 (O := O')).eval ρ₁).1.2.2.2.2.2.2.1 = st.trans.map cRecEnc := rfl
  have hCp0 : ((Expr.v0 (O := O')).eval ρ₁).1.2.2.2.2.2.2.2.2.1 = compTblEnc st.comp := rfl
  rw [hTr0, ht, hCp0, hfold]
  cases P
  · simp only [ρ₁, afterCorrShifted, GameState.leak, maxOpt, pGet, partyEnc, cGsEnc, compTblEnc,
      Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
    cases st.tL <;>
    · by_cases h1 : max (st.epoch .A) (st.epoch .B) = l
      · by_cases h2 : st.epoch .A + 1 ≤ l <;> simp [h1, h2]
      · simp [h1]
  · simp only [ρ₁, afterCorrShifted, GameState.leak, maxOpt, pGet, partyEnc, cGsEnc, compTblEnc,
      Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
    cases st.tL <;>
    · by_cases h1 : max (st.epoch .A) (st.epoch .B) = l
      · by_cases h3 : st.epoch .B + 1 ≤ l <;> simp [h1, h3]
      · simp [h1]

theorem afterCorrShifted_leaks_eq {St Msg C : Type} (l : ℕ) (s : GameState St Msg C) (P : Party) :
    (afterCorrShifted l s P).leaks.length = s.leaks.length + 1 := by
  simp [afterCorrShifted, GameState.leak]

theorem afterCorrShifted_leaks_le {St Msg C : Type} {L : ℕ} (l : ℕ) {s : GameState St Msg C}
    (hBound : SMStateBoundedEngine L s) (P : Party) :
    (afterCorrShifted l s P).leaks.length ≤ L := by
  rw [afterCorrShifted_leaks_eq]
  exact hBound.leaks_succ_le

theorem SMEngineInv.afterCorrShifted {St Msg C : Type} {L B q : ℕ} (l : ℕ)
    {s : GameState St Msg C} (hInv : SMEngineInv L B (q + 1) s) (P : Party) :
    SMEngineInv L B q (DeliverForge.afterCorrShifted l s P) := by
  obtain ⟨U, hU, hTrU, hCpU⟩ := hInv.comp_u
  refine ⟨?_, ?_, ?_, ?_, ?_, hInv.b_succ_le, hInv.bb_le⟩
  · simp only [DeliverForge.afterCorrShifted, GameState.leak]; have := hInv.trans_le; omega
  · simp only [DeliverForge.afterCorrShifted, GameState.leak]; have := hInv.chall_le; omega
  · simp only [DeliverForge.afterCorrShifted, GameState.leak, List.length_cons]
    have := hInv.leaks_le; omega
  · simp only [DeliverForge.afterCorrShifted, List.length_cons]
    have := hInv.corrs_le; omega
  · refine ⟨U, by omega, ?_, ?_⟩
    · intro r hr
      exact hTrU r hr
    · intro p hp
      simp only [DeliverForge.afterCorrShifted, GameState.leak, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨r, hr, rfl⟩ | hp
      · exact hTrU r (List.mem_of_mem_filter hr)
      · exact hCpU p hp

section ShiftedHandlers

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

local notation "OO" =>
  ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

def corrECShifted
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L l : ℕ) (π : Policy)
    {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (p : Expr OO Γ' .bool) :
    Comp OO I' Γ'
      (.prod (.opt psTy)
        (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)) :=
  rdsl do
    (es0, p0) ← return (es, p)
    let s0 := esG es0
    let refuse := orE (esAbort es0) (orE (cGsWin s0) (!(cCorrAllowedE L s0 p0)))
    if refuse then
      return (none, es0)
    else
      let s1 := cAfterCorrShiftedE L l s0 p0
      if orE (leakDoomE L π s0 s1) (corrDoomE π s0 p0) then
        return (none, esSetAbort es0 true)
      else
        (optSt, h') ← hk.reveal (esH es0) s0 p0 (pGet (cGsSt s0) p0)
        match optSt with
        | none => return (none, esMk (esG es0) h' true)
        | some st =>
          let s1_2 := cAfterCorrShiftedE L l (esG es0) p0
          return (some st, esMk s1_2 h' (esAbort es0))

def implECShifted
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L l Δ qep maxSkip : ℕ) (cfg : ConfigEC OO) (π : Policy)
    {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) :
    Comp OO I' Γ'
      (.prod (ckaSMR KC Γ CCoins T I KR RSt K SS RS M E)
        (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)) :=
  rdsl do
    (es0, q0) ← return (es, q)
    match q0 with
    | .transmit qTx =>
      (ans, es') ← transmitEC hk L Δ qep π es0 qTx
      return (inl (inl (inl (inl ans))), es')
    | .challenge qCh =>
      (ans, es') ← challEC hk L Δ qep cfg π es0 qCh
      return (inl (inl (inl (inr ans))), es')
    | .deliver qDel =>
      (ans, es') ← deliverEC hk L maxSkip cfg es0 qDel
      return (inl (inl (inr ans)), es')
    | .inject qInj =>
      (ans, es') ← injectEC hk L Δ qep cfg es0 qInj
      return (inl (inr ans), es')
    | .corrupt qCr =>
      (ans, es') ← corrECShifted hk L l π es0 qCr
      return (inr ans, es')

/-- Six-oracle costed engine dispatcher for `DeliverForge.implEDFShifted`. -/
def implECDFShifted
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L l Δ qep maxSkip : ℕ) (cfg : ConfigEC OO) (π : Policy)
    {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    Comp OO I' Γ'
      (.prod (ckaSMRDF KC Γ CCoins T I KR RSt K SS RS M E)
        (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)) :=
  rdsl do
    (es0, q0) ← return (es, q)
    match q0 with
    | .inl qBase =>
      (ans, es') ← implECShifted hk L l Δ qep maxSkip cfg π es0 qBase
      return (inl ans, es')
    | .inr qDf =>
      (ans, es') ← deliverForgeEC hk L Δ qep cfg es0 qDf
      return (inr ans, es')

theorem corrEShifted_inv {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {L B q : ℕ} (l : ℕ) (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (P : Party)
    (hInv : SMEngineInv L B (q + 1) es.g) :
    ∀ res ∈ support ((corrEShifted l hk π P).run es), SMEngineInv L B q res.2.g := by
  intro ⟨out, es'⟩ hmem
  have hInvQ : SMEngineInv L B q es.g := hInv.mono (Nat.le_succ q)
  unfold corrEShifted abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases hdoom : (π.leakDoom es.g (afterCorrShifted l es.g P) || π.corrDoom es.g P)
    · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte] at hmem
      rw [run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, h'⟩, _, hmem⟩ := hmem
      rcases revRes with _ | st
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInvQ
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        exact hInv.afterCorrShifted l P

theorem implEShifted_inv [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {L B q Δ qep maxSkip : ℕ} (l : ℕ) (cfg : Config M) (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : SMEngineInv L B (q + 1) es.g) :
    ∀ res ∈ support ((implEShifted l hk Δ qep maxSkip cfg π (.inr t)).run es),
      SMEngineInv L B q res.2.g := by
  rcases t with (((arg | arg) | arg) | arg) | P
  · exact transmitE_inv hk π es arg hInv
  · exact challE_inv hk cfg π es arg hInv
  · exact deliverE_inv hk cfg es arg hInv
  · exact injectE_inv hk cfg es arg hInv
  · exact corrEShifted_inv hk l π es P hInv

theorem implEDFShifted_inv [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {L B q Δ qep maxSkip : ℕ} (l : ℕ) (cfg : Config M) (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : SMEngineInv L B (q + 1) es.g) :
    ∀ res ∈ support ((implEDFShifted l hk Δ qep maxSkip cfg π (.inr t)).run es),
      SMEngineInv L B q res.2.g := by
  rcases t with t | arg
  · exact implEShifted_inv hk l cfg π es t hInv
  · exact deliverForgeE_inv hk cfg es arg hInv

theorem corrEShifted_vrInv {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    {VROkStep : ℕ → rsV → Prop}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (hVRHk : HooksVRInv VROkStep hk)
    {B q : ℕ} (l : ℕ) (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (P : Party)
    (hVR : SMVRInv VROkStep B (q + 1) es.g) :
    ∀ res ∈ support ((corrEShifted l hk π P).run es), SMVRInv VROkStep B q res.2.g := by
  have hVRQ : SMVRInv VROkStep B q es.g :=
    SMVRInv.mono (VROkStep := VROkStep) hVRHk.mono (Nat.le_succ q) hVR
  intro ⟨out, es'⟩ hmem
  unfold corrEShifted abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hVRQ
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases hdoom : (π.leakDoom es.g (afterCorrShifted l es.g P) || π.corrDoom es.g P)
    · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hVRQ
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte,
        run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, h'⟩, _, hmem⟩ := hmem
      rcases revRes with _ | st
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hVRQ
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hVRQ

theorem implEShifted_vrInv [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    {VROkStep : ℕ → rsV → Prop}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (hVRHk : HooksVRInv VROkStep hk)
    {L B q Δ qep maxSkip : ℕ} (l : ℕ) (cfg : Config M) (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : SMEngineInv L B (q + 1) es.g)
    (hVR : SMVRInv VROkStep B (q + 1) es.g) :
    ∀ res ∈ support ((implEShifted l hk Δ qep maxSkip cfg π (.inr t)).run es),
      SMVRInv VROkStep B q res.2.g := by
  rcases t with q4 | P
  · exact implE_vrInv hk hVRHk cfg π es (.inl q4) hInv hVR
  · exact corrEShifted_vrInv hk hVRHk l π es P hVR

theorem implEDFShifted_vrInv [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    {VROkStep : ℕ → rsV → Prop}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (hVRHk : HooksVRInv VROkStep hk)
    {L B q Δ qep maxSkip : ℕ} (l : ℕ) (cfg : Config M) (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : SMEngineInv L B (q + 1) es.g)
    (hVR : SMVRInv VROkStep B (q + 1) es.g) :
    ∀ res ∈ support ((implEDFShifted l hk Δ qep maxSkip cfg π (.inr t)).run es),
      SMVRInv VROkStep B q res.2.g := by
  rcases t with t | arg
  · exact implEShifted_vrInv hk hVRHk l cfg π es t hInv hVR
  · exact deliverForgeE_vrInv hk hVRHk cfg es arg hInv hVR

theorem corrEShifted_b_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (l : ℕ) (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (P : Party) :
    ∀ res ∈ support ((corrEShifted l hk π P).run es), res.2.g.b = es.g.b := by
  intro ⟨out, es'⟩ hmem
  unfold corrEShifted abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; rfl
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases hdoom : (π.leakDoom es.g (afterCorrShifted l es.g P) || π.corrDoom es.g P)
    · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; rfl
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte,
        run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, h'⟩, _, hmem⟩ := hmem
      rcases revRes with _ | st <;>
        (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
           support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
         rcases hmem with ⟨_, rfl⟩; rfl)

theorem implEShifted_b_eq [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {Δ qep maxSkip : ℕ} (l : ℕ) (cfg : Config M) (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain) :
    ∀ res ∈ support ((implEShifted l hk Δ qep maxSkip cfg π (.inr t)).run es),
      res.2.g.b = es.g.b := by
  rcases t with q4 | P
  · exact implE_b_eq hk cfg π es (.inl q4)
  · exact corrEShifted_b_eq hk l π es P

theorem implEDFShifted_b_eq [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {Δ qep maxSkip : ℕ} (l : ℕ) (cfg : Config M) (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain) :
    ∀ res ∈ support ((implEDFShifted l hk Δ qep maxSkip cfg π (.inr t)).run es),
      res.2.g.b = es.g.b := by
  rcases t with t | arg
  · exact implEShifted_b_eq hk l cfg π es t
  · exact deliverForgeE_b_eq hk cfg es arg

end ShiftedHandlers

end CryptoGames.SM.Engine

namespace CryptoGames.SM.Construction

open Engine Engine.RedPRNG CKA PRFPRNG DeliverForge

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "S" => ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "rrTy" => ckaRrTy KC Γ CCoins T I KR RSt K SS RS M E

/-! ## Shifted reductions -/

section HooksPRNGCDFShifted

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

/-- Costed `DeliverForge.redPRNGAuthDFShifted` reduction over `SM.specDF`. -/
def redPRNGAuthDFShiftedProg (L B Δcka qep maxSkip l tStar : ℕ) :
    CostedReduction OO II
      (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := prngEsTy
  init := rdsl [_u] do
    es ← initPRNGEStateC (raw ⟨true, some (l - 1), tStar⟩) false
    return ((), es)
  handle := rdsl [es, q] do
    implECDFShifted (hooksPRNGC B (raw ⟨true, some (l - 1), tStar⟩)) L l (raw (2 + Δcka)) qep maxSkip
      (modeCfgEC OO (raw ⟨true, some (l - 1), tStar⟩))
      (raw (⟨true, some (l - 1), tStar⟩ : Mode).policy) es q
  finish := rdsl [es, _b] do
    return authOutE L (raw (2 + Δcka)) (raw (⟨true, some (l - 1), tStar⟩ : Mode).policy) es

theorem redPRNGAuthDFShiftedProg_totalCost (L B Δcka qep maxSkip l tStar q : ℕ) :
    (redPRNGAuthDFShiftedProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip l tStar).totalCost q =
      (initPRNGEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        ⟨true, some (l - 1), tStar⟩ (.bool false : Expr OO [.unit] .bool)).cost + 6 +
        q * ((implECDFShifted (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (I' := II)
          (Γ' := [prngEsTy, ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E])
          (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
            (sampI := sampI) (sampK := sampK) B ⟨true, some (l - 1), tStar⟩)
          L l (2 + Δcka) qep maxSkip (modeCfgEC OO ⟨true, some (l - 1), tStar⟩)
          (⟨true, some (l - 1), tStar⟩ : Mode).policy .v0 .v1).cost + 13) +
        (authOutE (O' := OO) L (2 + Δcka) (⟨true, some (l - 1), tStar⟩ : Mode).policy
          (Expr.v0 : Expr OO [prngEsTy, .bool] prngEsTy)).cost := by
  simp only [CostedReduction.totalCost, redPRNGAuthDFShiftedProg, prngSMCodecDF, ckaSMCodecDF, prngIface,
    Comp.cost, Expr.cost]
  have hV0 : (Expr.v0 : Expr OO [prngEsTy, .unit] prngEsTy).cost = 1 := rfl
  rw [hV0, max_eq_right (by omega)]
  omega

end HooksPRNGCDFShifted

section HooksFSCDFShifted

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

theorem corrEShifted_hooksFSL_eq [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L l : ℕ) (π : Policy) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (P : Party)
    (hvR : ∀ t, L ≤ t → (es.g.st P).vR t = none) :
    (DeliverForge.corrEShifted l (hooksFSL cka prng fs L Δcka mo j) π P).run es =
      (DeliverForge.corrEShifted l (hooksFS cka prng fs Δcka mo j) π P).run es := by
  unfold DeliverForge.corrEShifted
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases href : (es.abort || es.g.win || !es.g.corrAllowed P)
  · simp [href]
  · simp only [href, Bool.false_eq_true, ↓reduceIte]
    by_cases hdoom : (π.leakDoom es.g (DeliverForge.afterCorrShifted l es.g P) ||
      π.corrDoom es.g P)
    · simp [hdoom]
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
        hooksFSL_reveal_eq cka prng fs L Δcka mo j es.g P (es.g.st P) hvR]

theorem implEShifted_hooksFSL_eq [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L l Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (q : (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hvR : ∀ P t, L ≤ t → (es.g.st P).vR t = none) :
    (DeliverForge.implEShifted l (hooksFSL cka prng fs L Δcka mo j) Δ qep maxSkip cfg π
        (.inr q)).run es =
      (DeliverForge.implEShifted l (hooksFS cka prng fs Δcka mo j) Δ qep maxSkip cfg π
        (.inr q)).run es := by
  rcases q with (((arg | arg) | arg) | arg) | P
  · change (transmitE (hooksFSL cka prng fs L Δcka mo j) Δ qep π arg).run es =
      (transmitE (hooksFS cka prng fs Δcka mo j) Δ qep π arg).run es
    rw [transmitE_hooksFSL_eq]
  · change (challE (hooksFSL cka prng fs L Δcka mo j) Δ qep cfg π arg).run es =
      (challE (hooksFS cka prng fs Δcka mo j) Δ qep cfg π arg).run es
    rw [challE_hooksFSL_eq]
  · change (deliverE (hooksFSL cka prng fs L Δcka mo j) maxSkip cfg arg).run es =
      (deliverE (hooksFS cka prng fs Δcka mo j) maxSkip cfg arg).run es
    rw [deliverE_hooksFSL_eq]
  · change (injectE (hooksFSL cka prng fs L Δcka mo j) Δ qep cfg arg).run es =
      (injectE (hooksFS cka prng fs Δcka mo j) Δ qep cfg arg).run es
    rw [injectE_hooksFSL_eq]
  · exact corrEShifted_hooksFSL_eq cka prng fs L l π Δcka mo j es P (hvR P)

theorem implEDFShifted_hooksFSL_eq [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L l Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (q : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hVR : ∀ P t, L ≤ t → (es.g.st P).vR t = none) :
    (DeliverForge.implEDFShifted l (hooksFSL cka prng fs L Δcka mo j) Δ qep maxSkip cfg π
        (.inr q)).run es =
      (DeliverForge.implEDFShifted l (hooksFS cka prng fs Δcka mo j)
        Δ qep maxSkip cfg π (.inr q)).run es := by
  rcases q with t | arg
  · exact implEShifted_hooksFSL_eq cka prng fs L l Δ qep maxSkip cfg π Δcka mo j es t hVR
  · change (DeliverForge.deliverForgeE (hooksFSL cka prng fs L Δcka mo j) Δ qep cfg arg).run es =
      (DeliverForge.deliverForgeE (hooksFS cka prng fs Δcka mo j) Δ qep cfg arg).run es
    rw [deliverForgeE_hooksFSL_eq]

theorem corrEShifted_fs_inv [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q : ℕ} (l : ℕ) (π : Policy) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (P : Party)
    (hInv : FSEngineInv L B (q + 1) es) :
    ∀ res ∈ support ((DeliverForge.corrEShifted l (hooksFS cka prng fs Δcka mo j) π P).run es),
      FSEngineInv L B q res.2 := by
  intro ⟨out, es'⟩ hmem
  have hInvQ : FSEngineInv L B q es := hInv.mono (Nat.le_succ q)
  have hSm := corrEShifted_inv (hooksFS cka prng fs Δcka mo j) l π es P hInv.sm
    (out, es') hmem
  unfold DeliverForge.corrEShifted abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases hdoom :
        (π.leakDoom es.g (DeliverForge.afterCorrShifted l es.g P) || π.corrDoom es.g P)
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

theorem implEShifted_fs_inv [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q Δ qep maxSkip : ℕ} (l : ℕ) (cfg : Config M) (π : Policy)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (t : (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : FSEngineInv L B (q + 1) es) :
    ∀ res ∈ support
      ((DeliverForge.implEShifted l (hooksFS cka prng fs Δcka mo j) Δ qep maxSkip cfg π
        (.inr t)).run es),
      FSEngineInv L B q res.2 := by
  rcases t with (((arg | arg) | arg) | arg) | P
  · exact transmitE_fs_inv cka prng fs π Δcka mo j es arg hInv
  · exact challE_fs_inv cka prng fs cfg π Δcka mo j es arg hInv
  · exact deliverE_fs_inv cka prng fs cfg Δcka mo j es arg hInv
  · exact injectE_fs_inv cka prng fs cfg Δcka mo j es arg hInv
  · exact corrEShifted_fs_inv cka prng fs l π Δcka mo j es P hInv

theorem implEDFShifted_fs_inv [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q Δ qep maxSkip : ℕ} (l : ℕ) (cfg : Config M) (π : Policy)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (q_df : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : FSEngineInv L B (q + 1) es) :
    ∀ res ∈ support
      ((DeliverForge.implEDFShifted l (hooksFS cka prng fs Δcka mo j)
        Δ qep maxSkip cfg π (.inr q_df)).run es),
      FSEngineInv L B q res.2 := by
  rcases q_df with t | arg
  · exact implEShifted_fs_inv cka prng fs l cfg π Δcka mo j es t hInv
  · exact deliverForgeE_fs_inv cka prng fs cfg Δcka mo j es arg hInv

/-- Costed `DeliverForge.redFSAuthDFShifted` reduction over `SM.specDF`. -/
def redFSAuthDFShiftedProg (L B Δcka qep maxSkip j l tStar : ℕ) :
    CostedReduction OO II
      (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := esTyFS
  init := rdsl [_u] do
    es ← initFSEStateC L (raw ⟨true, some (l - 1), tStar⟩) j false
    return ((), es)
  handle := rdsl [es, q] do
    implECDFShifted (hooksFSC L B Δcka (raw ⟨true, some (l - 1), tStar⟩) j) L l (raw (2 + Δcka)) qep maxSkip
      (modeCfgEC OO (raw ⟨true, some (l - 1), tStar⟩))
      (raw (⟨true, some (l - 1), tStar⟩ : Mode).policy) es q
  finish := rdsl [_es, _b] do
    sample (O := OO) (I := II) CKASamp.bit ()

theorem redFSAuthDFShiftedProg_totalCost (L B Δcka qep maxSkip j l tStar q : ℕ) :
    (redFSAuthDFShiftedProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip j l tStar).totalCost q =
      (initFSEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L ⟨true, some (l - 1), tStar⟩ j (.bool false : Expr OO [.unit] .bool)).cost + 7 +
        q * ((implECDFShifted (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (I' := II)
          (Γ' := [esTyFS, ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E])
          (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
            (sampI := sampI) (sampK := sampK) L B Δcka ⟨true, some (l - 1), tStar⟩ j)
          L l (2 + Δcka) qep maxSkip (modeCfgEC OO ⟨true, some (l - 1), tStar⟩)
          (⟨true, some (l - 1), tStar⟩ : Mode).policy .v0 .v1).cost + 13) := by
  simp only [CostedReduction.totalCost, redFSAuthDFShiftedProg, prngSMCodecDF, ckaSMCodecDF, fsaeadHeaderAdIface,
    prngSamplers, ckaSamplers, Comp.cost, Expr.cost]
  have hV0 : (Expr.v0 : Expr OO [esTyFS, .unit] esTyFS).cost = 1 := rfl
  rw [hV0, max_eq_right (by omega)]
  omega

end HooksFSCDFShifted
section FromAEADPRGDFShifted

variable {MK C : Type}

end FromAEADPRGDFShifted

/-! ### Shifted CKA hooks -/

@[reducible] def ckaShiftedHsTy : Ty S :=
  .prod ckaHsTy (.prod (.opt (.base .γ)) (.opt (.base .γ)))

def ckaShiftedHsEnc (s : DeliverForge.CKAStateShifted Γ T I) :
    (@ckaShiftedHsTy KC Γ CCoins T I KR RSt K SS RS M E).denote :=
  (s.base.cache, s.γPre .A, s.γPre .B)

@[reducible] def ckaShiftedEsTy : Ty S :=
  esTy ckaVpTy ckaShiftedHsTy

section HooksCKACDFShifted

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
  ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

local notation "II" =>
  ckaIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

def ckaShiftedSetCache {Γ'}
    (hE : Expr OO Γ' ckaShiftedHsTy)
    (tE : Expr OO Γ' .nat)
    (vE : Expr OO Γ' (.opt (.prod (.base .t) (.base .i)))) :
    Expr OO Γ' ckaShiftedHsTy :=
  rdslExpr => (tset hE.1 tE vE, hE.2)

def ckaShiftedSetΓPre {Γ'}
    (hE : Expr OO Γ' ckaShiftedHsTy)
    (pE : Expr OO Γ' .bool)
    (γE : Expr OO Γ' (.opt (.base .γ))) :
    Expr OO Γ' ckaShiftedHsTy :=
  rdslExpr => (hE.1, pSet hE.2 pE γE)

def ckaShiftedStartSendC (l : ℕ) {Γ'}
    (hE : Expr OO Γ' ckaShiftedHsTy)
    (_ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (γvE : Expr OO Γ' (.opt (.base .γ)))
    (σE : Expr OO Γ' (.base .sig))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) :
    Comp OO II Γ'
      (.prod (.opt (.prod (.opt (.base .γ)) (.prod (.base .t) (.prod (.base .sig) (.base .ss)))))
        ckaShiftedHsTy) :=
  rdsl do
    (h0, p0, t0, γv0, σ0, r0) ← return (hE, pE, tE, γvE, σE, rE)
    match γv0 with
    | none =>
      tiOpt ← (match r0 with
        | none =>
          if t0 == nat (l + 1) then
            query (I := II) CKATag.chall p0
          else
            query (I := II) CKATag.send p0
        | some coins =>
          query (I := II) CKATag.sendBad (p0, coins) :
          Comp OO II _ (.opt (.prod (.base .t) (.base .i))))
      match tiOpt with
      | none => return (none, h0)
      | some (T', Ik) =>
        let h1 := ckaShiftedSetCache h0 t0 (some (T', Ik))
        let pOut := Expr.op (O := OO) CKAOp.prngUp (σ0, Ik)
        let ss := Expr.op (O := OO) CKAOp.fsInitSender pOut.2
        if leN (nat (l + 2)) t0 then
          γOpt ← query (I := II) CKATag.corr p0
          match γOpt with
          | none => return (none, h1)
          | some γ' => return (some (some γ', T', pOut.1, ss), h1)
        else if leN (t0 + 1) (nat l) then
          γOpt ← query (I := II) CKATag.corr p0
          match γOpt with
          | none => return (none, h1)
          | some γ' => return (some (none, T', pOut.1, ss), ckaShiftedSetΓPre h1 p0 (some γ'))
        else
          return (some (none, T', pOut.1, ss), h1)
    | some γ =>
      coins ← (match r0 with
        | none => sample (I := II) CKASamp.ccoins ()
        | some c => pure c :
        Comp OO II _ (.base .ccoins))
      let cOut := Expr.op (O := OO) CKAOp.ckaSend (γ, coins)
      let T' := cOut.2.1
      let Ik := cOut.2.2
      let h1 := ckaShiftedSetCache h0 t0 (some (T', Ik))
      let pOut := Expr.op (O := OO) CKAOp.prngUp (σ0, Ik)
      let ss := Expr.op (O := OO) CKAOp.fsInitSender pOut.2
      return (some (some cOut.1, T', pOut.1, ss), h1)

def ckaShiftedStartRecvC (tStar : ℕ) {Γ'}
    (hE : Expr OO Γ' ckaShiftedHsTy)
    (_ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (_pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (γvE : Expr OO Γ' (.opt (.base .γ)))
    (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) :
    Comp OO II Γ'
      (.prod (.opt (.opt (.prod (.opt (.base .γ)) (.prod (.base .sig) (.base .rs)))))
        ckaShiftedHsTy) :=
  rdsl do
    return (ckaStartRecvAnsE (raw ⟨true, none, tStar⟩) hE.1 tE γvE σE tnE, hE)

def ckaShiftedFsSendC {Γ'}
    (hE : Expr OO Γ' ckaShiftedHsTy)
    (_ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (_pE : Expr OO Γ' .bool)
    (_tE : Expr OO Γ' .nat)
    (ssE : Expr OO Γ' (.base .ss))
    (hdrE : Expr OO Γ' hdrTy)
    (mE : Expr OO Γ' (.base .msg))
    (_pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))) :
    Comp OO II Γ' (.prod (.opt (.prod (.base .ss) (.base .ct))) ckaShiftedHsTy) :=
  rdsl do
    return (some (Expr.op (O := OO) CKAOp.fsSend (ssE, hdrE, mE)), hE)

def ckaShiftedFsRecvC (B : ℕ) {Γ'}
    (hE : Expr OO Γ' ckaShiftedHsTy)
    (_ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (_pE : Expr OO Γ' .bool)
    (_tE : Expr OO Γ' .nat)
    (rsE : Expr OO Γ' (.base .rs))
    (hdrE : Expr OO Γ' hdrTy)
    (eE : Expr OO Γ' (.base .ct))
    (_recE : Expr OO Γ' (.opt cRecTy)) :
    Comp OO II Γ'
      (.prod (.opt (.opt (.prod (.base .rs) (.prod .nat (.base .msg))))) ckaShiftedHsTy) :=
  rdsl do
    return (some (Expr.op (O := OO) (raw (CKAOp.fsReceive B)) (rsE, hdrE, eE)), hE)

def ckaShiftedCommitC (l : ℕ) {Γ'}
    (hE : Expr OO Γ' ckaShiftedHsTy)
    (_ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool)
    (oldE newE : Expr OO Γ' ckaVpTy) :
    Comp OO II Γ' (.prod (.opt ckaVpTy) ckaShiftedHsTy) :=
  rdsl do
    (h0, p0, old0, new0) ← return (hE, pE, oldE, newE)
    if lt (vpTcurNat old0) (vpTcurNat new0) && (!(isSomeE (vpΓ old0))) then
      rOpt ← query (I := II) CKATag.receive p0
      match rOpt with
      | none => return (none, h0)
      | some _ =>
        if leN (nat (l + 2)) (vpTcurNat new0) then
          γOpt ← query (I := II) CKATag.corr p0
          match γOpt with
          | none => return (none, h0)
          | some γ' => return (some (vpSetΓ new0 (some γ')), h0)
        else if leN (vpTcurNat new0 + 1) (nat l) then
          γOpt ← query (I := II) CKATag.corr p0
          match γOpt with
          | none => return (none, h0)
          | some γ' => return (some new0, ckaShiftedSetΓPre h0 p0 (some γ'))
        else
          return (some new0, h0)
    else
      return (some new0, h0)

def ckaShiftedRevealC (l : ℕ) {Γ'}
    (hE : Expr OO Γ' ckaShiftedHsTy)
    (_ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool)
    (vpE : Expr OO Γ' ckaVpTy) :
    Comp OO II Γ' (.prod (.opt psTy) ckaShiftedHsTy) :=
  rdsl do
    (h0, p0, vp0) ← return (hE, pE, vpE)
    optΓ ← (match vpΓ vp0 with
      | none =>
        if leN (vpTcurNat vp0 + 1) (nat l) then
          pure (pGet h0.2 p0)
        else
          query (I := II) CKATag.corr p0
      | some γ0 =>
        pure (some γ0) :
        Comp OO II _ (.opt (.base .γ)))
    match optΓ with
    | none => return (none, h0)
    | some γ => return (some (realPartyE vp0 γ (vpRoot vp0) (vpVS vp0) (vpVR vp0)), h0)

/-- Costed `HooksC` bundle for `redCKAAuthDFShifted`. -/
def hooksCKAShiftedC (B l tStar : ℕ) :
    HooksC OO II (.opt (.base .γ)) (.base .sig) (.base .ss) (.base .rs) ckaShiftedHsTy where
  startSend := ckaShiftedStartSendC l
  startRecv := ckaShiftedStartRecvC tStar
  fsSend := ckaShiftedFsSendC
  fsRecv := ckaShiftedFsRecvC B
  commit := ckaShiftedCommitC l
  reveal := ckaShiftedRevealC l

@[simp] theorem run_liftCShifted_bind {α β : Type}
    (x : CKA.AdversaryComp Γ CCoins T I α)
    (k : α → HM (CKA.spec Γ CCoins T I) (DeliverForge.CKAStateShifted Γ T I) β)
    (h : DeliverForge.CKAStateShifted Γ T I) :
    (DeliverForge.liftCShifted x >>= k).run h = x >>= fun a => (k a).run h := by
  simp [DeliverForge.liftCShifted, StateT.run_bind, StateT.run_lift, bind_map_left]

@[simp] theorem run_lift_bind_shifted {α β : Type}
    (x : CKA.AdversaryComp Γ CCoins T I α)
    (k : α → HM (CKA.spec Γ CCoins T I) (DeliverForge.CKAStateShifted Γ T I) β)
    (h : DeliverForge.CKAStateShifted Γ T I) :
    (StateT.lift x >>= k).run h = x >>= fun a => (k a).run h :=
  run_liftCShifted_bind x k h

private theorem caseOpt_eval {S' : Sig} {O' : Ops S'} {Γ' : List (Ty S')} {a b : Ty S'}
    (e : Expr O' Γ' (.opt a)) (n : Expr O' Γ' b) (s : Expr O' (a :: Γ') b) (ρ : Env Γ') :
    (Expr.caseOpt e n s).eval ρ =
      match e.eval ρ with
      | none => n.eval ρ
      | some x => s.eval (.cons x ρ) := rfl

@[simp] private theorem v0_eval_cons {S' : Sig} {O' : Ops S'} {Γ' : List (Ty S')} {a : Ty S'}
    (x : a.denote) (ρ : Env Γ') :
    (Expr.v0 (O := O')).eval (Env.cons x ρ) = x := rfl

theorem ckaShiftedSetCache_eval {Γ'}
    (hE : Expr OO Γ' ckaShiftedHsTy) (tE : Expr OO Γ' .nat)
    (vE : Expr OO Γ' (.opt (.prod (.base .t) (.base .i)))) (ρ : Env Γ')
    (h : DeliverForge.CKAStateShifted Γ T I)
    (hh : hE.eval ρ = ckaShiftedHsEnc h) :
    (ckaShiftedSetCache (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      hE tE vE).eval ρ =
      ckaShiftedHsEnc
        { h with base :=
            { h.base with cache := Function.update h.base.cache (tE.eval ρ) (vE.eval ρ) } } := by
  unfold ckaShiftedSetCache ckaShiftedHsEnc
  rw [pair_eval, tset_eval_eq_update (.fst hE) tE vE ρ]
  have h1 : (Expr.fst hE).eval ρ = h.base.cache := by simp [Expr.eval, hh, ckaShiftedHsEnc]
  have h2 : (Expr.snd hE).eval ρ = (h.γPre .A, h.γPre .B) := by
    simp [Expr.eval, hh, ckaShiftedHsEnc]
  rw [h1, h2]

theorem ckaShiftedSetΓPre_eval {Γ'}
    (hE : Expr OO Γ' ckaShiftedHsTy) (pE : Expr OO Γ' .bool)
    (γE : Expr OO Γ' (.opt (.base .γ))) (ρ : Env Γ')
    (h : DeliverForge.CKAStateShifted Γ T I) (P : Party)
    (hh : hE.eval ρ = ckaShiftedHsEnc h) (hp : pE.eval ρ = partyEnc P) :
    (ckaShiftedSetΓPre (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      hE pE γE).eval ρ =
      ckaShiftedHsEnc { h with γPre := Function.update h.γPre P (γE.eval ρ) } := by
  unfold ckaShiftedSetΓPre ckaShiftedHsEnc
  have h1 : (Expr.fst hE).eval ρ = h.base.cache := by simp [Expr.eval, hh, ckaShiftedHsEnc]
  have h2 : (Expr.snd hE).eval ρ = (h.γPre .A, h.γPre .B) := by
    simp [Expr.eval, hh, ckaShiftedHsEnc]
  rw [pair_eval, h1, pSet_eval (.snd hE) pE γE ρ h.γPre P h2 hp]

theorem ckaShiftedStartSendC_eval [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hSend : ckaSend = cka.send)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (l tStar : ℕ)
    {Γ'} (hE : Expr OO Γ' ckaShiftedHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γvE : Expr OO Γ' (.opt (.base .γ))) (σE : Expr OO Γ' (.base .sig))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ')
    (h : DeliverForge.CKAStateShifted Γ T I)
    (ctx : Ctx (Option Γ) T RSt SS RS M E) (P : Party)
    (hh : hE.eval ρ = ckaShiftedHsEnc h) (hp : pE.eval ρ = partyEnc P) :
    (ckaShiftedStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) l hE ctxE pE tE γvE σE rE).eval ρ =
      Prod.map id ckaShiftedHsEnc <$>
        ((DeliverForge.hooksCKAShifted cka prng fs l tStar).startSend ctx P
          (tE.eval ρ) (γvE.eval ρ) (σE.eval ρ) (rE.eval ρ)).run h := by
  dsimp only [ckaShiftedStartSendC, DeliverForge.hooksCKAShifted]
  rw [eval_bind_ret]
  set t := tE.eval ρ
  set γv := γvE.eval ρ
  set σ := σE.eval ρ
  set r := rE.eval ρ
  have h0 : (Expr.pair hE (.pair pE (.pair tE (.pair γvE (.pair σE rE))))).eval ρ =
      (ckaShiftedHsEnc h, partyEnc P, t, γv, σ, r) := by
    simp [Expr.eval, hh, hp, t, γv, σ, r]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod ckaShiftedHsTy (.prod .bool (.prod .nat
      (.prod (.opt (.base CKASort.γ)) (.prod (.base CKASort.sig) (.opt (.base CKASort.ccoins)))))))
    (ckaShiftedHsEnc h, partyEnc P, t, γv, σ, r) ρ
  rw [eval_caseOpt]
  have hγv : (Expr.fst (.snd (.snd (.snd (Expr.v0 (O := OO)))))).eval ρ₁ = γv := rfl
  rw [hγv]
  rcases γv with _ | γ
  ·
    dsimp only
    have hCont (ans : Option (T × I)) :
        (Comp.caseOpt (O := OO) (I := II) .v0
          (.ret (.pair .none (.fst .v1)))
          (let T' : Expr OO _ (.base .t) := .fst .v0
           let Ik : Expr OO _ (.base .i) := .snd .v0
           let h_2 : Expr OO _ ckaShiftedHsTy := .fst .v2
           let p_2 : Expr OO _ .bool := .fst (.snd .v2)
           let t_2 : Expr OO _ .nat := .fst (.snd (.snd .v2))
           let σ_2 : Expr OO _ (.base .sig) := .fst (.snd (.snd (.snd (.snd .v2))))
           let h1 : Expr OO _ ckaShiftedHsTy :=
             ckaShiftedSetCache h_2 t_2 (.some (.pair T' Ik))
           let pOut : Expr OO _ (.prod (.base .sig) (.base .k)) :=
             Expr.op (O := OO) CKAOp.prngUp (.pair σ_2 Ik)
           let ss : Expr OO _ (.base .ss) :=
             Expr.op (O := OO) CKAOp.fsInitSender (.snd pOut)
           .ite (leN (.nat (l + 2)) t_2)
             (.bind (Comp.query (I := II) CKATag.corr p_2)
               (.caseOpt .v0
                 (.ret (.pair .none (ckaShiftedSetCache (.fst .v3) (.fst (.snd (.snd .v3)))
                   (.some (.pair (.fst .v1) (.snd .v1))))))
                 (let γ' : Expr OO _ (.base .γ) := .v0
                  let T'_4 : Expr OO _ (.base .t) := .fst .v2
                  let Ik_4 : Expr OO _ (.base .i) := .snd .v2
                  let h_4 : Expr OO _ ckaShiftedHsTy := .fst .v4
                  let t_4 : Expr OO _ .nat := .fst (.snd (.snd .v4))
                  let σ_4 : Expr OO _ (.base .sig) := .fst (.snd (.snd (.snd (.snd .v4))))
                  let h1_4 : Expr OO _ ckaShiftedHsTy :=
                    ckaShiftedSetCache h_4 t_4 (.some (.pair T'_4 Ik_4))
                  let pOut_4 : Expr OO _ (.prod (.base .sig) (.base .k)) :=
                    Expr.op (O := OO) CKAOp.prngUp (.pair σ_4 Ik_4)
                  let ss_4 : Expr OO _ (.base .ss) :=
                    Expr.op (O := OO) CKAOp.fsInitSender (.snd pOut_4)
                  .ret (.pair
                    (.some (.pair (.some γ') (.pair T'_4 (.pair (.fst pOut_4) ss_4))))
                    h1_4))))
             (.ite (leN (.add t_2 (.nat 1)) (.nat l))
               (.bind (Comp.query (I := II) CKATag.corr p_2)
                 (.caseOpt .v0
                   (.ret (.pair .none (ckaShiftedSetCache (.fst .v3) (.fst (.snd (.snd .v3)))
                     (.some (.pair (.fst .v1) (.snd .v1))))))
                   (let γ' : Expr OO _ (.base .γ) := .v0
                    let T'_4 : Expr OO _ (.base .t) := .fst .v2
                    let Ik_4 : Expr OO _ (.base .i) := .snd .v2
                    let h_4 : Expr OO _ ckaShiftedHsTy := .fst .v4
                    let p_4 : Expr OO _ .bool := .fst (.snd .v4)
                    let t_4 : Expr OO _ .nat := .fst (.snd (.snd .v4))
                    let σ_4 : Expr OO _ (.base .sig) := .fst (.snd (.snd (.snd (.snd .v4))))
                    let h1_4 : Expr OO _ ckaShiftedHsTy :=
                      ckaShiftedSetΓPre
                        (ckaShiftedSetCache h_4 t_4 (.some (.pair T'_4 Ik_4)))
                        p_4 (.some γ')
                    let pOut_4 : Expr OO _ (.prod (.base .sig) (.base .k)) :=
                      Expr.op (O := OO) CKAOp.prngUp (.pair σ_4 Ik_4)
                    let ss_4 : Expr OO _ (.base .ss) :=
                      Expr.op (O := OO) CKAOp.fsInitSender (.snd pOut_4)
                    .ret (.pair
                      (.some (.pair .none (.pair T'_4 (.pair (.fst pOut_4) ss_4))))
                      h1_4))))
               (.ret (.pair
                 (.some (.pair .none (.pair T' (.pair (.fst pOut) ss))))
                 h1))))).eval
          (Env.cons (t := .opt (.prod (.base CKASort.t) (.base CKASort.i))) ans ρ₁) =
        Prod.map id ckaShiftedHsEnc <$>
          (match ans with
          | none => pure none
          | some (T', Ik) => do
            DeliverForge.cacheCShifted t (T', Ik)
            let p := prng.up σ Ik
            if l + 2 ≤ t then do
              let γ? : Option Γ ← DeliverForge.liftCShifted (CKA.corrQuery P)
              match γ? with
              | none => pure none
              | some γ => pure (some (some γ, T', p.1, fs.initSender p.2))
            else if t + 1 ≤ l then do
              let γ? : Option Γ ← DeliverForge.liftCShifted (CKA.corrQuery P)
              match γ? with
              | none => pure none
              | some γ => do
                DeliverForge.setγPreShifted P (some γ)
                pure (some (none, T', p.1, fs.initSender p.2))
            else pure (some (none, T', p.1, fs.initSender p.2))).run h := by
      dsimp only
      rcases ans with _ | ⟨T', Ik⟩
      · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
      · simp only [eval_caseOpt, DeliverForge.cacheCShifted, StateT.run_bind,
          StateT.run_modify, pure_bind]
        set ρ₂ := Env.cons (t := .prod (.base CKASort.t) (.base CKASort.i)) (T', Ik)
          (Env.cons (t := .opt (.prod (.base CKASort.t) (.base CKASort.i))) (some (T', Ik)) ρ₁)
        change (Comp.ite _ _ _).eval ρ₂ = _
        rw [eval_ite]
        have hle1 : (leN (.nat (l + 2)) (.fst (.snd (.snd (Expr.v2 (O := OO)))))).eval ρ₂ =
            decide (l + 2 ≤ t) := by rw [leN_eval]; rfl
        rw [hle1]
        by_cases hfin : l + 2 ≤ t
        · simp only [hfin, decide_true, ↓reduceIte, eval_bind, run_liftCShifted_bind, map_bind]
          rw [query_corr_eval _ ρ₂ P rfl]
          refine bind_congr fun γ? => ?_
          rcases γ? with _ | γ'
          · simp only [eval_caseOpt, v0_eval_cons, eval_ret, pair_eval, StateT.run_pure, map_pure,
              Prod.map, id_eq]
            congr 2
            exact ckaShiftedSetCache_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
              (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
              (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
              (.fst .v3) (.fst (.snd (.snd .v3)))
              (.some (.pair (.fst .v1) (.snd .v1)))
              (Env.cons (t := .opt (.base CKASort.γ)) none ρ₂) h rfl
          · simp only [eval_caseOpt, v0_eval_cons, eval_ret, StateT.run_pure, map_pure, Prod.map,
              id_eq]
            set ρ₃ := Env.cons (t := .base CKASort.γ) γ'
              (Env.cons (t := .opt (.base CKASort.γ)) (some γ') ρ₂)
            have hCache := ckaShiftedSetCache_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
              (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
              (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
              (.fst .v4) (.fst (.snd (.snd .v4)))
              (.some (.pair (.fst .v2) (.snd .v2))) ρ₃ h rfl
            simp only [pair_eval, some_eval, hCache]
            simp [ρ₃, ρ₂, ρ₁, ckaOps, hPrngUp, hFsInitS, Expr.eval, Expr.v0, Expr.v2, Expr.v4]
        · simp only [hfin, decide_false, Bool.false_eq_true, ↓reduceIte, eval_ite]
          have hle2 : (leN (.add (.fst (.snd (.snd (Expr.v2 (O := OO))))) (.nat 1))
              (.nat l)).eval ρ₂ = decide (t + 1 ≤ l) := by rw [leN_eval]; rfl
          rw [hle2]
          by_cases hpre : t + 1 ≤ l
          · simp only [hpre, decide_true, ↓reduceIte, eval_bind, run_liftCShifted_bind, map_bind]
            rw [query_corr_eval _ ρ₂ P rfl]
            refine bind_congr fun γ? => ?_
            rcases γ? with _ | γ'
            · simp only [eval_caseOpt, v0_eval_cons, eval_ret, pair_eval, StateT.run_pure,
                map_pure, Prod.map, id_eq]
              congr 2
              exact ckaShiftedSetCache_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
                (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
                (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
                (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
                (.fst .v3) (.fst (.snd (.snd .v3)))
                (.some (.pair (.fst .v1) (.snd .v1)))
                (Env.cons (t := .opt (.base CKASort.γ)) none ρ₂) h rfl
            · simp only [eval_caseOpt, v0_eval_cons, eval_ret, DeliverForge.setγPreShifted,
                StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, map_pure,
                Prod.map, id_eq]
              set ρ₃ := Env.cons (t := .base CKASort.γ) γ'
                (Env.cons (t := .opt (.base CKASort.γ)) (some γ') ρ₂)
              have hCache := ckaShiftedSetCache_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
                (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
                (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
                (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
                (.fst .v4) (.fst (.snd (.snd .v4)))
                (.some (.pair (.fst .v2) (.snd .v2))) ρ₃ h rfl
              have hΓPre := ckaShiftedSetΓPre_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
                (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
                (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
                (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
                (ckaShiftedSetCache (.fst .v4) (.fst (.snd (.snd .v4)))
                  (.some (.pair (.fst .v2) (.snd .v2))))
                (.fst (.snd .v4)) (.some .v0) ρ₃
                { h with base :=
                    { h.base with cache := Function.update h.base.cache t (some (T', Ik)) } }
                P hCache rfl
              simp only [pair_eval, some_eval, hΓPre]
              simp [ρ₃, ρ₂, ρ₁, ckaOps, hPrngUp, hFsInitS, Expr.eval, Expr.v0, Expr.v2, Expr.v4]
          · simp only [hpre, decide_false, Bool.false_eq_true, ↓reduceIte, eval_ret,
              StateT.run_pure, map_pure, Prod.map, id_eq]
            have hCache := ckaShiftedSetCache_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
              (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
              (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
              (.fst .v2) (.fst (.snd (.snd .v2)))
              (.some (.pair (.fst .v0) (.snd .v0))) ρ₂ h rfl
            simp only [pair_eval, some_eval, hCache]
            simp [ρ₂, ρ₁, ckaOps, hPrngUp, hFsInitS, Expr.eval, Expr.v0, Expr.v2]
    have hp1 : (Expr.fst (.snd (Expr.v0 (O := OO)))).eval ρ₁ = partyEnc P := rfl
    have hr : (Expr.snd (.snd (.snd (.snd (.snd (Expr.v0 (O := OO))))))).eval ρ₁ = r := rfl
    rw [eval_bind, eval_caseOpt, hr]
    rcases r with _ | c
    · rw [eval_ite]
      have htH : (Expr.eqN (.fst (.snd (.snd (Expr.v0 (O := OO))))) (.nat (l + 1))).eval ρ₁ =
          decide (t = l + 1) := rfl
      rw [htH]
      by_cases hteq : t = l + 1
      · rw [ite_eq_left (decide_eq_true hteq), ite_eq_left hteq]
        simp only [query_chall_eval _ ρ₁ P hp1, run_liftCShifted_bind, map_bind]
        exact bind_congr hCont
      · rw [ite_eq_right (by simp [hteq]), ite_eq_right hteq]
        simp only [query_send_eval _ ρ₁ P hp1, run_liftCShifted_bind, map_bind]
        exact bind_congr hCont
    · have hbad : (Expr.pair (.fst (.snd (Expr.v1 (O := OO)))) .v0).eval
          (Env.cons (t := .base CKASort.ccoins) c ρ₁) = (partyEnc P, c) := rfl
      simp only [query_sendBad_eval _ _ P c hbad, run_liftCShifted_bind, map_bind]
      exact bind_congr hCont
  ·
    dsimp only
    set ρ₂ := Env.cons (t := .base CKASort.γ) γ ρ₁
    have hCoinsCont (coins : CCoins) :
        (Comp.ret (O := OO) (I := II)
          (.pair
            (.some (.pair (.some (.fst (Expr.op (O := OO) CKAOp.ckaSend (.pair .v1 .v0))))
              (.pair (.fst (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair .v1 .v0))))
                (.pair
                  (.fst (Expr.op (O := OO) CKAOp.prngUp
                    (.pair (.fst (.snd (.snd (.snd (.snd .v2)))))
                      (.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair .v1 .v0)))))))
                  (Expr.op (O := OO) CKAOp.fsInitSender
                    (.snd (Expr.op (O := OO) CKAOp.prngUp
                      (.pair (.fst (.snd (.snd (.snd (.snd .v2)))))
                        (.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair .v1 .v0))))))))))))
            (ckaShiftedSetCache (.fst .v2) (.fst (.snd (.snd .v2)))
              (.some (.pair
                (.fst (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair .v1 .v0))))
                (.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair .v1 .v0))))))))).eval
          (Env.cons (t := .base CKASort.ccoins) coins ρ₂) =
        Prod.map id ckaShiftedHsEnc <$>
          (do
            let c := cka.send γ coins
            DeliverForge.cacheCShifted t (c.2.1, c.2.2)
            let p := prng.up σ c.2.2
            pure (some (some c.1, c.2.1, p.1, fs.initSender p.2))).run h := by
      dsimp only
      simp only [DeliverForge.cacheCShifted, StateT.run_bind, StateT.run_modify,
        StateT.run_pure, pure_bind, map_pure, Prod.map, id_eq]
      set ρ₃ := Env.cons (t := .base CKASort.ccoins) coins ρ₂
      have hCache := ckaShiftedSetCache_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (.fst .v2) (.fst (.snd (.snd .v2)))
        (.some (.pair (.fst (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair .v1 .v0))))
          (.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair .v1 .v0)))))) ρ₃ h rfl
      simp only [eval_ret, pair_eval, some_eval, hCache]
      simp [ρ₃, ρ₂, ρ₁, ckaOps, hSend, hPrngUp, hFsInitS, Expr.eval, Expr.v0, Expr.v1, Expr.v2]
    have hr2 : (Expr.snd (.snd (.snd (.snd (.snd (Expr.v1 (O := OO))))))).eval ρ₂ = r := rfl
    rw [eval_bind, eval_caseOpt, hr2]
    rcases r with _ | c
    · have hSamp : (Comp.sample (O := OO) (I := II) CKASamp.ccoins .unit).eval ρ₂ =
          sampleT CCoins := by
        simp only [Comp.eval, ckaIface, ckaSamplers, hSampCCoins, sampleT]
        exact Engine.liftP_eq_liftM II (fun _ => rfl) ($ᵗ CCoins)
      simp only [hSamp, run_lift_bind_shifted, map_bind]
      exact bind_congr hCoinsCont
    · simp only [eval_ret, v0_eval_cons, pure_bind]
      exact hCoinsCont c
theorem ckaShiftedStartRecvC_eval [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (heqT : eqT = (· == ·))
    (l tStar : ℕ)
    {Γ'} (hE : Expr OO Γ' ckaShiftedHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γvE : Expr OO Γ' (.opt (.base .γ))) (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) (ρ : Env Γ')
    (h : DeliverForge.CKAStateShifted Γ T I)
    (ctx : Ctx (Option Γ) T RSt SS RS M E) (P : Party)
    (hh : hE.eval ρ = ckaShiftedHsEnc h) :
    (ckaShiftedStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) tStar hE ctxE pE tE γvE σE tnE).eval ρ =
      Prod.map id ckaShiftedHsEnc <$>
        ((DeliverForge.hooksCKAShifted cka prng fs l tStar).startRecv ctx P
          (tE.eval ρ) (γvE.eval ρ) (σE.eval ρ) (tnE.eval ρ)).run h := by
  dsimp only [ckaShiftedStartRecvC, ckaStartRecvAnsE, DeliverForge.hooksCKAShifted]
  have hBase : (Expr.fst hE).eval ρ = ckaHsEnc h.base := by
    simp [Expr.eval, hh, ckaShiftedHsEnc, ckaHsEnc]
  simp only [eval_ret, pair_eval, letE_eval, hh, hBase, StateT.run_bind, StateT.run_get, pure_bind]
  set t : ℕ := tE.eval ρ
  set γv : Option Γ := γvE.eval ρ
  set σ : RSt := σE.eval ρ
  set Tn : T := tnE.eval ρ
  set ρ₁ := Env.cons
    (t := .prod ckaHsTy (.prod .nat (.prod (.opt (.base CKASort.γ))
      (.prod (.base CKASort.sig) (.base CKASort.t)))))
    (ckaHsEnc h.base, t, γv, σ, Tn) ρ
  change (pure ((Expr.caseOpt _ _ _).eval ρ₁, ckaShiftedHsEnc h) :
      TComp (CKA.spec Γ CCoins T I) _) = _
  have hHonest :
      (Expr.caseOpt (.tget (.fst (Expr.v0 (O := OO))) (.fst (.snd .v0))) .none
        (.ite (Expr.op (O := OO) CKAOp.eqT (.pair (.fst .v0) (.snd (.snd (.snd (.snd .v1))))))
          (.some (.snd .v0)) .none)).eval ρ₁ =
      (match h.base.cache t with
        | some (Tc, Ik) => if Tc = Tn then some Ik else none
        | none => none) := by
    have hGet : (Expr.tget (.fst (Expr.v0 (O := OO))) (.fst (.snd .v0))).eval ρ₁ =
        h.base.cache t := rfl
    rw [caseOpt_eval, hGet]
    rcases h.base.cache t with _ | ⟨Tc, Ik⟩
    · rfl
    · simp only [ρ₁, ckaOps, heqT, Expr.eval, Expr.v0, Expr.v1, BEq.beq]
      by_cases hEq : Tc = Tn <;> simp [hEq]
  rw [caseOpt_eval, hHonest]
  rcases h.base.cache t with _ | ⟨Tc, Ik⟩
  · dsimp only
    rw [ite_eval]
    have hCond :
        (Expr.and (.bool true)
          (.eqN (.fst (.snd (Expr.v0 (O := OO)))) (.nat tStar))).eval ρ₁ =
        (true && decide (t = tStar)) := rfl
    rw [hCond, Bool.true_and]
    by_cases ht : t = tStar
    · simp only [ht, decide_true, ↓reduceIte]
      rcases γv with _ | γ
      · simp only [StateT.run_pure, map_pure]; rfl
      · simp only [StateT.run_pure, map_pure, Prod.map, id_eq]
        congr 1; congr 1
        simp [ρ₁, ckaOps, hRecv, hPrngUp, hFsInitR, Expr.eval, Expr.v0, Expr.v1]
    · simp only [ht, decide_false, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, map_pure]; rfl
  · dsimp only
    by_cases hEq : Tc = Tn
    · simp only [hEq, ↓reduceIte]
      rcases γv with _ | γ <;>
      · simp only [StateT.run_pure, map_pure, Prod.map, id_eq]
        congr 1; congr 1
        simp [ρ₁, ckaOps, hRecv, hPrngUp, hFsInitR, Expr.eval, Expr.v0, Expr.v1, Expr.v2]
    · simp only [hEq, ↓reduceIte]
      rw [ite_eval]
      have hCond :
          (Expr.and (.bool true)
            (.eqN (.fst (.snd (Expr.v0 (O := OO)))) (.nat tStar))).eval ρ₁ =
          (true && decide (t = tStar)) := rfl
      rw [hCond, Bool.true_and]
      by_cases ht : t = tStar
      · simp only [ht, decide_true, ↓reduceIte]
        rcases γv with _ | γ
        · simp only [StateT.run_pure, map_pure]; rfl
        · simp only [StateT.run_pure, map_pure, Prod.map, id_eq]
          congr 1; congr 1
          simp [ρ₁, ckaOps, hRecv, hPrngUp, hFsInitR, Expr.eval, Expr.v0, Expr.v1]
      · simp only [ht, decide_false, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, map_pure]; rfl

theorem ckaShiftedCommitC_eval [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (l tStar : ℕ)
    {Γ'} (hE : Expr OO Γ' ckaShiftedHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (oldE newE : Expr OO Γ' ckaVpTy) (ρ : Env Γ')
    (h : DeliverForge.CKAStateShifted Γ T I) (ctx : Ctx (Option Γ) T RSt SS RS M E) (P : Party)
    (old new : VP (Option Γ) T RSt SS RS)
    (hh : hE.eval ρ = ckaShiftedHsEnc h) (hp : pE.eval ρ = partyEnc P)
    (hold : oldE.eval ρ = ckaVpEnc old) (hnew : newE.eval ρ = ckaVpEnc new) :
    (ckaShiftedCommitC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) l hE ctxE pE oldE newE).eval ρ =
      Prod.map (Option.map ckaVpEnc) ckaShiftedHsEnc <$>
        ((DeliverForge.hooksCKAShifted cka prng fs l tStar).commit ctx P old new).run h := by
  unfold ckaShiftedCommitC DeliverForge.hooksCKAShifted
  dsimp only
  rw [eval_bind_ret]
  have h0 : (Expr.pair hE (.pair pE (.pair oldE newE))).eval ρ =
      (ckaShiftedHsEnc h, partyEnc P, ckaVpEnc old, ckaVpEnc new) := by
    simp [Expr.eval, hh, hp, hold, hnew]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod ckaShiftedHsTy (.prod .bool (.prod ckaVpTy ckaVpTy)))
    (ckaShiftedHsEnc h, partyEnc P, ckaVpEnc old, ckaVpEnc new) ρ
  rw [eval_ite]
  have hCond :
      (Expr.and (.lt (vpTcurNat (.fst (.snd (.snd (Expr.v0 (O := OO))))))
          (vpTcurNat (.snd (.snd (.snd .v0)))))
        (.not (isSomeE (vpΓ (.fst (.snd (.snd .v0))))))).eval ρ₁ =
      (decide (old.tcur < new.tcur) && old.γ.isNone) := by
    rcases old with ⟨id_o, root_o, vS_o, vR_o, _ | γ_o, Tcur_o, tcur_o⟩
    · simp [ρ₁, isSomeE, vpTcurNat, vpΓ, ckaVpEnc, vpTblEnc, vpEnc, Expr.eval, Expr.v0]; rfl
    · simp [ρ₁, isSomeE, vpTcurNat, vpΓ, ckaVpEnc, vpTblEnc, vpEnc, Expr.eval, Expr.v0]
  rw [hCond]
  by_cases hc : (decide (old.tcur < new.tcur) && old.γ.isNone) = true
  · simp only [hc, ↓reduceIte, eval_bind, run_liftCShifted_bind, map_bind]
    rw [query_receive_eval _ ρ₁ P rfl]
    refine bind_congr fun rcvRes => ?_
    rcases rcvRes with _ | ⟨⟩
    · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
    · simp only [eval_caseOpt, v0_eval_cons]
      set ρ₂ := Env.cons (t := .unit) ()
        (Env.cons (t := .opt .unit) (some ()) ρ₁)
      change (Comp.ite _ _ _).eval ρ₂ = _
      rw [eval_ite]
      have hle1 : (leN (.nat (l + 2))
          (vpTcurNat (.snd (.snd (.snd (Expr.v2 (O := OO))))))).eval ρ₂ =
          decide (l + 2 ≤ new.tcur) := by rw [leN_eval]; rfl
      rw [hle1]
      by_cases hfin : l + 2 ≤ new.tcur
      · simp only [hfin, decide_true, ↓reduceIte, eval_bind, run_liftCShifted_bind, map_bind]
        rw [query_corr_eval _ ρ₂ P rfl]
        refine bind_congr fun γ? => ?_
        rcases γ? with _ | γ'
        · simp [ρ₂, ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v3]
        · simp only [eval_caseOpt, v0_eval_cons, eval_ret,
            StateT.run_pure, map_pure, Prod.map, Option.map_some]
          set ρ₃ := Env.cons (t := .base CKASort.γ) γ'
            (Env.cons (t := .opt (.base CKASort.γ)) (some γ') ρ₂)
          have hSetΓ := vpSetΓ_eval (O' := OO)
            (.snd (.snd (.snd (Expr.v4 (O := OO))))) (.some .v0) ρ₃ new rfl
          simp only [pair_eval, some_eval, hSetΓ]; rfl
      · simp only [hfin, decide_false, Bool.false_eq_true, ↓reduceIte, eval_ite]
        have hle2 : (leN (.add (vpTcurNat (.snd (.snd (.snd (Expr.v2 (O := OO)))))) (.nat 1))
            (.nat l)).eval ρ₂ = decide (new.tcur + 1 ≤ l) := by rw [leN_eval]; rfl
        rw [hle2]
        by_cases hpre : new.tcur + 1 ≤ l
        · simp only [hpre, decide_true, ↓reduceIte, eval_bind, run_liftCShifted_bind, map_bind]
          rw [query_corr_eval _ ρ₂ P rfl]
          refine bind_congr fun γ? => ?_
          rcases γ? with _ | γ'
          · simp [ρ₂, ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v3]
          · simp only [eval_caseOpt, v0_eval_cons, eval_ret, DeliverForge.setγPreShifted,
              StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              map_pure, Prod.map, Option.map_some]
            set ρ₃ := Env.cons (t := .base CKASort.γ) γ'
              (Env.cons (t := .opt (.base CKASort.γ)) (some γ') ρ₂)
            have hΓPre := ckaShiftedSetΓPre_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
              (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
              (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
              (.fst .v4) (.fst (.snd .v4)) (.some .v0) ρ₃ h P rfl rfl
            simp only [pair_eval, some_eval, hΓPre]; rfl
        · simp [ρ₂, ρ₁, hpre, eval_ret, StateT.run_pure, Prod.map, Expr.eval, Expr.v2]
  · simp [ρ₁, hc, eval_ret, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
theorem ckaShiftedRevealC_eval [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (l tStar : ℕ)
    {Γ'} (hE : Expr OO Γ' ckaShiftedHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' ckaVpTy) (ρ : Env Γ')
    (h : DeliverForge.CKAStateShifted Γ T I) (ctx : Ctx (Option Γ) T RSt SS RS M E) (P : Party)
    (vp : VP (Option Γ) T RSt SS RS)
    (hh : hE.eval ρ = ckaShiftedHsEnc h) (hp : pE.eval ρ = partyEnc P)
    (hvp : vpE.eval ρ = ckaVpEnc vp) :
    (ckaShiftedRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) l hE ctxE pE vpE).eval ρ =
      Prod.map (Option.map ckaPsEnc) ckaShiftedHsEnc <$>
        ((DeliverForge.hooksCKAShifted cka prng fs l tStar).reveal ctx P vp).run h := by
  unfold ckaShiftedRevealC DeliverForge.hooksCKAShifted
  dsimp only
  rw [eval_bind_ret]
  have h0 : (Expr.pair hE (.pair pE vpE)).eval ρ =
      (ckaShiftedHsEnc h, partyEnc P, ckaVpEnc vp) := by
    simp [Expr.eval, hh, hp, hvp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod ckaShiftedHsTy (.prod .bool ckaVpTy))
    (ckaShiftedHsEnc h, partyEnc P, ckaVpEnc vp) ρ
  have hCont (γ? : Option Γ) :
      (Comp.caseOpt (O := OO) (I := II) .v0
        (.ret (.pair .none (.fst .v1)))
        (let γ : Expr OO _ (.base .γ) := .v0
         let h_2 : Expr OO _ ckaShiftedHsTy := .fst .v2
         let vp_2 : Expr OO _ ckaVpTy := .snd (.snd .v2)
         .ret (.pair
           (.some (realPartyE vp_2 γ (vpRoot vp_2) (vpVS vp_2) (vpVR vp_2)))
           h_2))).eval
        (Env.cons (t := .opt (.base CKASort.γ)) γ? ρ₁) =
      Prod.map (Option.map ckaPsEnc) ckaShiftedHsEnc <$>
        ((match γ? with
        | none => pure none
        | some γ => pure (some (realParty vp γ vp.root vp.vS vp.vR)) :
          HM (CKA.spec Γ CCoins T I) (DeliverForge.CKAStateShifted Γ T I) _)).run h := by
    rcases γ? with _ | γ'
    · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
    · simp only [eval_caseOpt, v0_eval_cons, eval_ret, StateT.run_pure, map_pure, Prod.map,
        Option.map_some]
      set ρ₂ := Env.cons (t := .base CKASort.γ) γ'
        (Env.cons (t := .opt (.base CKASort.γ)) (some γ') ρ₁)
      have hReal := realPartyE_eval (O' := OO)
        (.snd (.snd .v2)) .v0 (vpRoot (.snd (.snd .v2)))
        (vpVS (.snd (.snd .v2))) (vpVR (.snd (.snd .v2))) ρ₂ vp rfl
      simp only [pair_eval, some_eval, hReal]; rfl
  rw [eval_bind, eval_caseOpt]
  have hγ : (vpΓ (.snd (.snd (Expr.v0 (O := OO))))).eval ρ₁ = vp.γ := rfl
  rw [hγ]
  rcases vp.γ with _ | γ
  · rw [eval_ite]
    have hle : (leN (.add (vpTcurNat (.snd (.snd (Expr.v0 (O := OO))))) (.nat 1))
        (.nat l)).eval ρ₁ = decide (vp.tcur + 1 ≤ l) := by rw [leN_eval]; rfl
    rw [hle]
    by_cases hpre : vp.tcur + 1 ≤ l
    · simp only [hpre, decide_true, ↓reduceIte, eval_ret, pure_bind,
        StateT.run_bind, StateT.run_get]
      have hpGet : (pGet (.snd (.fst (Expr.v0 (O := OO)))) (.fst (.snd .v0))).eval ρ₁ =
          h.γPre P := by
        cases P <;> simp [ρ₁, pGet, partyEnc, ckaShiftedHsEnc, Expr.eval, Expr.v0]
      rw [hpGet]
      exact hCont (h.γPre P)
    · simp only [hpre, decide_false, Bool.false_eq_true, ↓reduceIte,
        run_liftCShifted_bind, map_bind]
      rw [query_corr_eval _ ρ₁ P rfl]
      exact bind_congr hCont
  · simp only [eval_ret, some_eval, v0_eval_cons, pure_bind, StateT.run_pure]
    exact hCont (some γ)

theorem hooksCKAShifted_startRecv_rs [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (l tStar : ℕ)
    {VROk : RS → Prop} (hInitR : ∀ k, VROk (fs.initReceiver k))
    (ctx : Ctx (Option Γ) T RSt SS RS M E) (P : Party) (t : ℕ)
    (γv : Option Γ) (σ : RSt) (Tn : T) (h : DeliverForge.CKAStateShifted Γ T I) :
    ∀ res ∈ support (((DeliverForge.hooksCKAShifted cka prng fs l tStar).startRecv
        ctx P t γv σ Tn).run h),
      ∀ γ' σ' rs, res.1 = some (some (γ', σ', rs)) → VROk rs := by
  intro ⟨ans, h'⟩ hmem γ' σ' rs hEq
  subst hEq
  unfold DeliverForge.hooksCKAShifted at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  revert hmem
  rcases h.base.cache t with _ | ⟨Tc, Ik⟩
  · intro hmem
    split_ifs at hmem
    · rcases γv with _ | γ
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨h, _⟩; cases h
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq, Option.some.injEq] at hmem
        rcases hmem with ⟨⟨rfl, rfl, rfl⟩, rfl⟩; exact hInitR _
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some.injEq] at hmem
      rcases hmem with ⟨h, _⟩; cases h
  · intro hmem
    by_cases hEq : Tc = Tn
    · simp only [hEq, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some.injEq] at hmem
      rcases hmem with ⟨⟨rfl, rfl, rfl⟩, rfl⟩; exact hInitR _
    · simp only [hEq, ↓reduceIte] at hmem
      split_ifs at hmem
      · rcases γv with _ | γ
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨h, _⟩; cases h
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq, Option.some.injEq] at hmem
          rcases hmem with ⟨⟨rfl, rfl, rfl⟩, rfl⟩; exact hInitR _
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq, Option.some.injEq] at hmem
        rcases hmem with ⟨h, _⟩; cases h

theorem hooksCKAShiftedC_agrees_vr [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (B l tStar : ℕ)
    {VROk : RS → Prop}
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hInitR : ∀ k, VROk (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROk rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B) :
    HooksCAgrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      ckaShiftedHsEnc (fun _ => True) (HBoundedPost := fun _ => True) (VROk := VROk)
      (hooksCKAShiftedC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B l tStar)
      (DeliverForge.hooksCKAShifted cka prng fs l tStar) where
  hBounded_post _ _ := trivial
  startSend_eval hE ctxE pE tE γE σE rE ρ h ctx P _ hh _ hp :=
    ckaShiftedStartSendC_eval cka prng fs hSend hPrngUp hFsInitS hSampCCoins l tStar
      hE ctxE pE tE γE σE rE ρ h ctx P hh hp
  startSend_bounded _ _ _ _ _ _ _ _ _ _ := trivial
  startRecv_eval hE ctxE pE tE γE σE tnE ρ h ctx P _ hh _ _ :=
    ckaShiftedStartRecvC_eval cka prng fs hRecv hPrngUp hFsInitR heqT l tStar
      hE ctxE pE tE γE σE tnE ρ h ctx P hh
  startRecv_bounded _ _ _ _ _ _ _ _ _ _ := trivial
  startRecv_vrOk ctx P t γ σ Tn h _ :=
    hooksCKAShifted_startRecv_rs cka prng fs l tStar hInitR ctx P t γ σ Tn h
  fsSend_eval hE _ _ _ ssE hdrE mE _ ρ h _ _ _ hh _ _ := by
    simp [hooksCKAShiftedC, ckaShiftedFsSendC, DeliverForge.hooksCKAShifted, ckaOps, hFsSend, hh,
      StateT.run_pure, Prod.map, Expr.eval]
  fsRecv_eval hE _ _ _ rsE hdrE eE _ ρ h _ _ _ _ hVR hh _ _ _ := by
    simp only [hooksCKAShiftedC, ckaShiftedFsRecvC, DeliverForge.hooksCKAShifted, eval_ret,
      ckaOps, hFsRecv, hh, StateT.run_pure, map_pure, Prod.map, id_eq, Expr.eval]
    congr 2
    rcases hrc : fs.receive (rsE.eval ρ) (hdrE.eval ρ) (eE.eval ρ) with _ | ⟨rs', i, m⟩
    · rfl
    · simp [Nat.min_eq_left (hFsB _ _ _ _ _ _ hVR hrc)]
  fsRecv_bounded _ _ _ _ _ _ _ _ _ _ _ := trivial
  commit_eval hE ctxE pE oldE newE ρ h ctx P old new _ hh _ hp hold hnew :=
    ckaShiftedCommitC_eval cka prng fs l tStar hE ctxE pE oldE newE ρ h ctx P old new
      hh hp hold hnew
  reveal_eval hE ctxE pE vpE ρ h ctx P vp _ hh _ hp hvp :=
    ckaShiftedRevealC_eval cka prng fs l tStar hE ctxE pE vpE ρ h ctx P vp hh hp hvp

def initCKAShiftedEStateC (l : ℕ) {Γ'} (bE : Expr OO Γ' .bool) : Comp OO II Γ' ckaShiftedEsTy :=
  rdsl do
    b0 ← return bE
    kr ← sample (I := II) CKASamp.kr ()
    γPreAB ← (if bool (decide (1 ≤ l)) then
      do
        γA ← query (I := II) CKATag.corr (bool (partyEnc .A))
        γB ← query (I := II) CKATag.corr (bool (partyEnc .B))
        return (γA, γB)
    else
      pure (none, none))
    let out := Expr.op (O := OO) CKAOp.prngUp
      (Expr.op (O := OO) CKAOp.prngInit kr, Expr.op (O := OO) CKAOp.lamI ())
    let parties := mkPartiesE none none out.1
      (Expr.op (O := OO) CKAOp.fsInitSender out.2)
      (Expr.op (O := OO) CKAOp.fsInitReceiver out.2)
    let g0 := cGsInitE parties.1 parties.2 b0
    let h0 := (tconst none, γPreAB)
    return esMk g0 h0 false

def initCKAShiftedRaw [SampleableType KR]
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (l : ℕ) (b : Bool) :
    CKA.AdversaryComp Γ CCoins T I
      (EState (VP (Option Γ) T RSt SS RS) M (Header T × E)
        (DeliverForge.CKAStateShifted Γ T I)) :=
  sampleT KR >>= fun kr =>
  (if 1 ≤ l then do
    let γA? ← CKA.corrQuery (State := Γ) (Coins := CCoins) (Msg := T) (CKey := I) .A
    let γB? ← CKA.corrQuery (State := Γ) (Coins := CCoins) (Msg := T) (CKey := I) .B
    pure (γA?, γB?)
   else pure (none, none)) >>= fun γPreAB =>
  let out := prng.up (prng.init kr) lam
  let (vA, vB) := mkParties (T := T) none none out.1 (fs.initSender out.2) (fs.initReceiver out.2)
  pure
    { g := { st := fun | .A => vA | .B => vB, b := b }
      h := { base := {}, γPre := fun | .A => γPreAB.1 | .B => γPreAB.2 } }

theorem initCKAShiftedEStateC_eval [SampleableType KR]
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hPrngInit : prngInit = prng.init)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR))
    (l : ℕ) {Γ'} (bE : Expr OO Γ' .bool) (ρ : Env Γ') :
    (initCKAShiftedEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) l bE).eval ρ =
      esEnc ckaVpEnc ckaShiftedHsEnc <$> initCKAShiftedRaw prng fs lam l (bE.eval ρ) := by
  unfold initCKAShiftedEStateC initCKAShiftedRaw
  rw [eval_bind_ret]
  set b := bE.eval ρ
  set ρ₁ := Env.cons (t := .bool) b ρ
  rw [eval_bind, map_bind]
  have hKR : (Comp.sample (O := OO) (I := II) CKASamp.kr .unit).eval ρ₁ = sampleT KR := by
    simp only [Comp.eval, ckaIface, ckaSamplers, hSampKR, sampleT]
    exact Engine.liftP_eq_liftM II (fun _ => rfl) ($ᵗ KR)
  rw [hKR]
  refine bind_congr fun kr => ?_
  set ρ₂ := Env.cons (t := .base CKASort.kr) kr ρ₁
  rw [eval_bind, eval_ite, map_bind]
  have hBranch :
      (if (Expr.bool (O := OO) (decide (1 ≤ l))).eval ρ₂ then
        (Comp.bind (Comp.query (O := OO) (I := II) CKATag.corr (.bool (partyEnc .A)))
          (.bind (Comp.query (O := OO) (I := II) CKATag.corr (.bool (partyEnc .B)))
            (.ret (.pair .v1 .v0)))).eval ρ₂
       else (Comp.ret (O := OO) (I := II) (.pair .none .none)).eval ρ₂) =
      (if 1 ≤ l then do
        let γA? ← CKA.corrQuery (State := Γ) (Coins := CCoins) (Msg := T) (CKey := I) .A
        let γB? ← CKA.corrQuery (State := Γ) (Coins := CCoins) (Msg := T) (CKey := I) .B
        pure (γA?, γB?)
       else pure (none, none)) := by
    by_cases hl : 1 ≤ l
    · simp only [hl, decide_true, ↓reduceIte, Expr.eval, eval_bind]
      rw [query_corr_eval (.bool (partyEnc .A)) ρ₂ .A rfl]
      refine bind_congr fun γA? => ?_
      rw [query_corr_eval (.bool (partyEnc .B))
        (Env.cons (t := .opt (.base CKASort.γ)) γA? ρ₂) .B rfl]
      simp [Expr.eval, Expr.v0, Expr.v1]
    · simp [hl, Expr.eval]
  rw [hBranch]
  refine bind_congr fun ⟨γA, γB⟩ => ?_
  set ρ₃ := Env.cons (t := .prod (.opt (.base CKASort.γ)) (.opt (.base CKASort.γ))) (γA, γB) ρ₂
  change (Comp.ret _).eval ρ₃ = _
  rw [eval_ret, map_pure]
  have hMkP := mkPartiesE_eval (γvT := .opt (.base CKASort.γ)) (O' := OO)
    .none .none
    (.fst (Expr.op (O := OO) CKAOp.prngUp
      (.pair (Expr.op (O := OO) CKAOp.prngInit .v1) (Expr.op (O := OO) CKAOp.lamI .unit))))
    (Expr.op (O := OO) CKAOp.fsInitSender
      (.snd (Expr.op (O := OO) CKAOp.prngUp
        (.pair (Expr.op (O := OO) CKAOp.prngInit .v1) (Expr.op (O := OO) CKAOp.lamI .unit)))))
    (Expr.op (O := OO) CKAOp.fsInitReceiver
      (.snd (Expr.op (O := OO) CKAOp.prngUp
        (.pair (Expr.op (O := OO) CKAOp.prngInit .v1) (Expr.op (O := OO) CKAOp.lamI .unit)))))
    ρ₃
  set out := prng.up (prng.init kr) lam
  set pAB := mkParties (T := T) (none : Option Γ) (none : Option Γ) out.1
    (fs.initSender out.2) (fs.initReceiver out.2)
  have hMkP' :
      (mkPartiesE (γvT := .opt (.base CKASort.γ)) (O' := OO) .none .none
        (.fst (Expr.op (O := OO) CKAOp.prngUp
          (.pair (Expr.op (O := OO) CKAOp.prngInit .v1) (Expr.op (O := OO) CKAOp.lamI .unit))))
        (Expr.op (O := OO) CKAOp.fsInitSender
          (.snd (Expr.op (O := OO) CKAOp.prngUp
            (.pair (Expr.op (O := OO) CKAOp.prngInit .v1) (Expr.op (O := OO) CKAOp.lamI .unit)))))
        (Expr.op (O := OO) CKAOp.fsInitReceiver
          (.snd (Expr.op (O := OO) CKAOp.prngUp
            (.pair (Expr.op (O := OO) CKAOp.prngInit .v1)
              (Expr.op (O := OO) CKAOp.lamI .unit)))))).eval
        ρ₃ = (ckaVpEnc pAB.1, ckaVpEnc pAB.2) := by
    simpa [ρ₃, ρ₂, ρ₁, ckaOps, hPrngInit, hPrngUp, hFsInitS, hFsInitR, out, pAB, Prod.map,
      Expr.eval, Expr.v0, Expr.v1] using hMkP
  have hGs := cGsInitE_eval ckaVpEnc (O' := OO)
    (.fst (mkPartiesE (γvT := .opt (.base CKASort.γ)) .none .none
      (.fst (Expr.op (O := OO) CKAOp.prngUp
        (.pair (Expr.op (O := OO) CKAOp.prngInit .v1) (Expr.op (O := OO) CKAOp.lamI .unit))))
      (Expr.op (O := OO) CKAOp.fsInitSender
        (.snd (Expr.op (O := OO) CKAOp.prngUp
          (.pair (Expr.op (O := OO) CKAOp.prngInit .v1) (Expr.op (O := OO) CKAOp.lamI .unit)))))
      (Expr.op (O := OO) CKAOp.fsInitReceiver
        (.snd (Expr.op (O := OO) CKAOp.prngUp
          (.pair (Expr.op (O := OO) CKAOp.prngInit .v1) (Expr.op (O := OO) CKAOp.lamI .unit)))))))
    (.snd (mkPartiesE (γvT := .opt (.base CKASort.γ)) .none .none
      (.fst (Expr.op (O := OO) CKAOp.prngUp
        (.pair (Expr.op (O := OO) CKAOp.prngInit .v1) (Expr.op (O := OO) CKAOp.lamI .unit))))
      (Expr.op (O := OO) CKAOp.fsInitSender
        (.snd (Expr.op (O := OO) CKAOp.prngUp
          (.pair (Expr.op (O := OO) CKAOp.prngInit .v1) (Expr.op (O := OO) CKAOp.lamI .unit)))))
      (Expr.op (O := OO) CKAOp.fsInitReceiver
        (.snd (Expr.op (O := OO) CKAOp.prngUp
          (.pair (Expr.op (O := OO) CKAOp.prngInit .v1) (Expr.op (O := OO) CKAOp.lamI .unit)))))))
    .v2 ρ₃ pAB.1 pAB.2
    (by simp [Expr.eval, hMkP']) (by simp [Expr.eval, hMkP'])
  simp only [esMk, pair_eval, hGs]
  simp [ρ₃, ρ₂, ρ₁, esEnc, ckaShiftedHsEnc, Expr.eval, Expr.v0, Expr.v2]; rfl

theorem initCKAShiftedRaw_inv [SampleableType KR]
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (l : ℕ) (b : Bool)
    {L B qAdv : ℕ} (hqB : qAdv ≤ B) (hB1 : B + 1 ≤ L) (hBB : B * B ≤ L * L) :
    ∀ es₀ ∈ support (initCKAShiftedRaw (Γ := Γ) (CCoins := CCoins) prng fs lam l b),
      SMEngineInv L B qAdv es₀.g ∧ es₀.g.b = b := by
  intro es₀ hmem
  unfold initCKAShiftedRaw at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨kr, _, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨γA, γB⟩, _, hmem⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hmem
  subst hmem
  exact ⟨(SMEngineInv.init _ b hB1 hBB).mono hqB, rfl⟩

theorem initCKAShiftedRaw_vrInv [SampleableType KR]
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (l : ℕ) (b : Bool)
    {VROkStep : ℕ → RS → Prop} {B qAdv : ℕ}
    (hInitR : ∀ k, VROkStep (B - qAdv) (fs.initReceiver k)) :
    ∀ es₀ ∈ support (initCKAShiftedRaw (Γ := Γ) (CCoins := CCoins) prng fs lam l b),
      SMVRInv VROkStep B qAdv es₀.g := by
  intro es₀ hmem P t v hv
  unfold initCKAShiftedRaw at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨kr, _, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨γA, γB⟩, _, hmem⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hmem
  subst hmem
  cases P <;> simp only [mkParties] at hv
  · split_ifs at hv with ht0
    · cases hv; exact hInitR _
  · cases hv

/-- Costed `DeliverForge.redCKAAuthDFShifted` reduction over `SM.specDF`. -/
def redCKAAuthDFShiftedProg (L B qep maxSkip l tStar : ℕ) :
    CostedReduction OO II
      (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := ckaShiftedEsTy
  init := rdsl [_u] do
    es ← initCKAShiftedEStateC l false
    return ((), es)
  handle := rdsl [es, q] do
    implECDFShifted (hooksCKAShiftedC B l tStar) L l (raw 3) qep maxSkip
      (modeCfgEC OO (raw ⟨true, some (l - 1), tStar⟩))
      (raw (⟨true, some (l - 1), tStar⟩ : Mode).policy) es q
  finish := rdsl [es, _b] do
    return authOutE L (raw 3) (raw (⟨true, some (l - 1), tStar⟩ : Mode).policy) es

@[simp] theorem ckaShiftedStartSendC_queries (l : ℕ) {Γ'}
    (hE : Expr OO Γ' ckaShiftedHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γvE : Expr OO Γ' (.opt (.base .γ))) (σE : Expr OO Γ' (.base .sig))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) :
    (ckaShiftedStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) l hE ctxE pE tE γvE σE rE).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  simp [ckaShiftedStartSendC, Comp.queries]

@[simp] theorem ckaShiftedStartRecvC_queries (tStar : ℕ) {Γ'}
    (hE : Expr OO Γ' ckaShiftedHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γvE : Expr OO Γ' (.opt (.base .γ))) (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) :
    (ckaShiftedStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) tStar hE ctxE pE tE γvE σE tnE).queries
      (fun _ => 1) (fun _ => 0) = 0 := by
  simp [ckaShiftedStartRecvC, Comp.queries]

@[simp] theorem ckaShiftedFsSendC_queries {Γ'}
    (hE : Expr OO Γ' ckaShiftedHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (ssE : Expr OO Γ' (.base .ss)) (hdrE : Expr OO Γ' hdrTy)
    (mE : Expr OO Γ' (.base .msg)) (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))) :
    (ckaShiftedFsSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) hE ctxE pE tE ssE hdrE mE pairE).queries
      (fun _ => 1) (fun _ => 0) = 0 := by
  simp [ckaShiftedFsSendC, Comp.queries]

@[simp] theorem ckaShiftedFsRecvC_queries (B : ℕ) {Γ'}
    (hE : Expr OO Γ' ckaShiftedHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (rsE : Expr OO Γ' (.base .rs)) (hdrE : Expr OO Γ' hdrTy)
    (eE : Expr OO Γ' (.base .ct)) (recE : Expr OO Γ' (.opt cRecTy)) :
    (ckaShiftedFsRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B hE ctxE pE tE rsE hdrE eE recE).queries
      (fun _ => 1) (fun _ => 0) = 0 := by
  simp [ckaShiftedFsRecvC, Comp.queries]

@[simp] theorem ckaShiftedCommitC_queries (l : ℕ) {Γ'}
    (hE : Expr OO Γ' ckaShiftedHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (oldE newE : Expr OO Γ' ckaVpTy) :
    (ckaShiftedCommitC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) l hE ctxE pE oldE newE).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  simp [ckaShiftedCommitC, Comp.queries]

@[simp] theorem ckaShiftedRevealC_queries (l : ℕ) {Γ'}
    (hE : Expr OO Γ' ckaShiftedHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' ckaVpTy) :
    (ckaShiftedRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) l hE ctxE pE vpE).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [ckaShiftedRevealC, Comp.queries]

@[simp] theorem initCKAShiftedEStateC_queries (l : ℕ) {Γ'} (bE : Expr OO Γ' .bool) :
    (initCKAShiftedEStateC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) l bE).queries (fun _ => 1) (fun _ => 0) = 2 := by
  simp [initCKAShiftedEStateC, Comp.queries]

theorem redCKAAuthDFShiftedProg_totalCost (L B qep maxSkip l tStar q : ℕ) :
    (redCKAAuthDFShiftedProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B qep maxSkip l tStar).totalCost q =
      (initCKAShiftedEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        l (.bool false : Expr OO [.unit] .bool)).cost + 6 +
        q * ((implECDFShifted (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (I' := II)
          (Γ' := [ckaShiftedEsTy, ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E])
          (hooksCKAShiftedC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
            (sampI := sampI) (sampK := sampK) B l tStar)
          L l 3 qep maxSkip (modeCfgEC OO ⟨true, some (l - 1), tStar⟩)
          (⟨true, some (l - 1), tStar⟩ : Mode).policy .v0 .v1).cost + 13) +
        (authOutE (O' := OO) L 3 (⟨true, some (l - 1), tStar⟩ : Mode).policy
          (Expr.v0 : Expr OO [ckaShiftedEsTy, .bool] ckaShiftedEsTy)).cost := by
  simp only [CostedReduction.totalCost, redCKAAuthDFShiftedProg, ckaSMCodecDF, ckaIface, Comp.cost,
    Expr.cost]
  have hV0 : (Expr.v0 : Expr OO [ckaShiftedEsTy, .unit] ckaShiftedEsTy).cost = 1 := rfl
  rw [hV0, max_eq_right (by omega)]
  omega

end HooksCKACDFShifted

end CryptoGames.SM.Construction

namespace CryptoGames.SM.Construction

open ReductionDsl
open Engine
open CryptoGames.SM.Engine

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

section HooksCKACDFDir2

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

local notation "S" => ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E

local notation "OO" =>
  ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

local notation "II" =>
  ckaIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

end HooksCKACDFDir2

section HooksPRNGCDFDir2

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

end HooksPRNGCDFDir2

section HooksFSCDFDir2

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

end HooksFSCDFDir2

end CryptoGames.SM.Construction

/-! ## Cost bounds and case-split wrappers -/

namespace CryptoVerification.LibsignalSession

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession ReductionDsl

section ShiftedDeliverForgeCost

variable
  {KC Γ CCoins T I KR RSt K SS RS M E : Type}
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

local notation "S_cka" => CKA.ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO_cka" =>
  CKA.ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

private lemma hdrEqE_cost_le {Γ'}
    (c₁ c₂ : ReductionDsl.Expr OO_cka Γ' (CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    (SM.Engine.hdrEqE c₁ c₂).cost ≤ c₁.cost + c₂.cost + 40 := by
  have hmax11 : max 1 1 = 1 := rfl
  have hmax14 : max 1 4 = 4 := rfl
  simp only [SM.Engine.hdrEqE, SM.Engine.optTEqE, CKA.ckaOps, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, hmax11, hmax14, Nat.reduceAdd]
  omega

private lemma deliverForgeEC_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : ReductionDsl.Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L qep : ℕ)
    (mo : SM.Construction.Mode) (hhk : HooksCostBounded hk H)
    {Γ'} (es : ReductionDsl.Expr OO_cka Γ'
      (SM.Engine.esTy
        (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : ReductionDsl.Expr OO_cka Γ'
      (.prod .bool (.prod (CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)
        (CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)))) :
    (SM.Engine.deliverForgeEC hk L 3 qep (SM.Engine.modeCfgEC OO_cka mo) es arg).cost ≤
      es.cost + arg.cost + 3 * H + 650 * L +
        ReductionDsl.bits qep + ReductionDsl.bits mo.tStar + 5010 := by
  have hqep1 := bits_succ_le qep
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let hdrCtT := CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let decT : ReductionDsl.Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ0 : List (ReductionDsl.Ty S_cka) :=
    .prod (SM.Engine.esTy vpT hsT) (.prod .bool (.prod hdrCtT hdrCtT)) :: Γ'
  let Γ1 : List (ReductionDsl.Ty S_cka) := SM.Engine.cRecTy :: Γ0
  let Γ2 : List (ReductionDsl.Ty S_cka) :=
    decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ1
  have hit0 := cInTransitE_cost_le (vpT := vpT) L (Γ' := Γ0)
    (SM.Engine.esG (O' := OO_cka) (.fst .v0)) (SM.otherE (.fst (.snd .v0)))
    (.fst (.snd (.snd .v0)))
  have hit1 := cInTransitE_cost_le (vpT := vpT) L (Γ' := Γ1)
    (SM.Engine.esG (O' := OO_cka) (.fst .v1)) (SM.otherE (.fst (.snd .v1)))
    (.snd (.snd (.snd .v1)))
  have hcc1 := cCompContainsE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ1)
    (SM.Engine.esG (.fst .v1)) (SM.Engine.cRecPos .v0)
  have hhe1 := hdrEqE_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (Γ' := Γ1) (.fst (.snd (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hvr := vRecvC_cost_le hk H hhk (Γ' := Γ1)
    (SM.Engine.esH (.fst .v1)) (SM.Engine.esG (.fst .v1)) (.fst (.snd .v1))
    (SM.pGet (SM.Engine.cGsSt (SM.Engine.esG (.fst .v1))) (.fst (.snd .v1)))
    (.snd (.snd (.snd .v1))) .none
  have htr := cTrivialE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ2)
    (SM.Engine.esG (.fst .v4))
    (.pair (SM.otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hcm := commitEC_cost_le hk H L hhk (Γ' := Γ2)
    (SM.Engine.esSetH (.fst .v4) (.snd .v2)) (SM.Engine.esG (.fst .v4)) (.fst (.snd .v4))
    (SM.pGet (SM.Engine.cGsSt (SM.Engine.esG (.fst .v4))) (.fst (.snd .v4)))
    (.fst .v0)
    (.pair (SM.otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hij := modeCfgEC_injectFullE_cost_le (O' := OO_cka) mo (Γ' := Γ2) (.fst (.snd .v0))
  simp only [esG_cost, esH_cost, esSetH_cost, pGet_cost, cGsSt_cost, cRecPos_cost, otherE_cost,
    ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v2_cost, v4_cost, Nat.reduceAdd] at hit0 hit1 hcc1 hhe1 hvr htr hcm hij
  simp only [SM.Engine.deliverForgeEC, SM.orE, SM.isSomeE, SM.Engine.cGsWin, SM.Engine.esMk,
    SM.posEpoch, cRecPos_cost, esG_cost, esAbort_cost, esSetH_cost, esSetG_cost, cGsSetWin_cost,
    ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, Nat.reduceAdd]
  omega

private lemma implECDF_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : ReductionDsl.Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L qep maxSkip : ℕ)
    (mo : SM.Construction.Mode) (hhk : HooksCostBounded hk H)
    {Γ'} (es : ReductionDsl.Expr OO_cka Γ'
      (SM.Engine.esTy
        (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : ReductionDsl.Expr OO_cka Γ' (CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    (SM.Engine.implECDF hk L 3 qep maxSkip (SM.Engine.modeCfgEC OO_cka mo) mo.policy es q).cost ≤
      es.cost + q.cost + 19000 * L +
        L * (ReductionDsl.bits (mo.tL.getD 0) + 2 * ReductionDsl.bits mo.tStar + 40) +
        3 * H + 5 * ReductionDsl.bits qep + (ReductionDsl.bits (mo.tL.getD 0) + 3) +
        5 * ReductionDsl.bits mo.tStar +
        11 * (maxSkip + 1) + 20050 := by
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let hdrCtT := CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let esT := SM.Engine.esTy vpT hsT
  let smqT := CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let dfqT : ReductionDsl.Ty S_cka := .prod .bool (.prod hdrCtT hdrCtT)
  let smqDFT := CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E
  let Γ0 : List (ReductionDsl.Ty S_cka) := .prod esT smqDFT :: Γ'
  let Γ_sm : List (ReductionDsl.Ty S_cka) := smqT :: Γ0
  let Γ_df : List (ReductionDsl.Ty S_cka) := dfqT :: Γ0
  have himpl := implEC_cost_le hk H L qep maxSkip mo hhk (Γ' := Γ_sm) (.fst .v1) .v0
  have hdf := deliverForgeEC_cost_le hk H L qep mo hhk (Γ' := Γ_df) (.fst .v1) .v0
  simp only [v0_cost, v1_cost, ReductionDsl.Expr.cost, Nat.reduceAdd] at himpl hdf
  simp only [SM.Engine.implECDF, ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
    v0_cost, Nat.reduceAdd]
  omega

private lemma cAfterCorrShiftedE_cost_le_cAfterCorrE
    {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka}
    (L l : ℕ) {Γ'} (s : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT))
    (p : ReductionDsl.Expr O' Γ' .bool) :
    (SM.Engine.cAfterCorrShiftedE L l s p).cost ≤
      (SM.Engine.cAfterCorrE L s p).cost + 36 * ReductionDsl.bits l + 650 := by
  have hl1 := ReductionDsl.bits_mono (Nat.sub_le l 1)
  have hb1 : ReductionDsl.bits 1 = 1 := rfl
  simp only [SM.Engine.cAfterCorrShiftedE, SM.Engine.cAfterCorrE,
    SM.Engine.cGsMk, SM.Engine.cLeakE,
    SM.maxOptE, SM.maxN, SM.leN, SM.boolEq, SM.otherE, SM.pGet,
    SM.Engine.cRecPos, SM.posSender,
    SM.Engine.cGsSt, SM.Engine.cGsB, SM.Engine.cGsWin, SM.Engine.cGsEpoch, SM.Engine.cGsIdx,
    SM.Engine.cGsTL, SM.Engine.cGsTrans, SM.Engine.cGsChall, SM.Engine.cGsComp,
    SM.Engine.cGsMaxAcc, SM.Engine.cGsLeaks, SM.Engine.cGsCorrs,
    ReductionDsl.Expr.cost, v0_cost, v1_cost, v2_cost, hb1, Nat.reduceAdd]
  omega

private lemma leakDoomE_cost_le_add {O' : ReductionDsl.Ops S_cka} {vpT : ReductionDsl.Ty S_cka}
    (L : ℕ) (π : SM.Engine.Policy) {Γ'}
    (g g₁ g₂ : ReductionDsl.Expr O' Γ' (SM.Engine.cGsTy vpT)) {d : ℕ}
    (h : g₁.cost ≤ g₂.cost + d) :
    (SM.Engine.leakDoomE L π g g₁).cost ≤ (SM.Engine.leakDoomE L π g g₂).cost + d := by
  simp only [SM.Engine.leakDoomE, ReductionDsl.Expr.cost]
  omega

private lemma corrECShifted_cost_le_corrEC {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : ReductionDsl.Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (L l : ℕ)
    (π : SM.Engine.Policy)
    {Γ'} (es : ReductionDsl.Expr OO_cka Γ'
      (SM.Engine.esTy
        (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (p : ReductionDsl.Expr OO_cka Γ' .bool) :
    (SM.Engine.corrECShifted hk L l π es p).cost ≤
      (SM.Engine.corrEC hk L π es p).cost + 72 * ReductionDsl.bits l + 1300 := by
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let psT := CKA.ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
  let Γ0 : List (ReductionDsl.Ty S_cka) := .prod (SM.Engine.esTy vpT hsT) .bool :: Γ'
  let Γ1 : List (ReductionDsl.Ty S_cka) := psT :: .prod (.opt psT) hsT :: Γ0
  have hac0 := cAfterCorrShiftedE_cost_le_cAfterCorrE (O' := OO_cka) (vpT := vpT) L l (Γ' := Γ0)
    (SM.Engine.esG (.fst .v0)) (.snd .v0)
  have hld := leakDoomE_cost_le_add (O' := OO_cka) (vpT := vpT) L π (Γ' := Γ0)
    (SM.Engine.esG (.fst .v0))
    (SM.Engine.cAfterCorrShiftedE L l (SM.Engine.esG (.fst .v0)) (.snd .v0))
    (SM.Engine.cAfterCorrE L (SM.Engine.esG (.fst .v0)) (.snd .v0))
    (Nat.add_assoc _ _ _ ▸ hac0)
  have hac1 := cAfterCorrShiftedE_cost_le_cAfterCorrE (O' := OO_cka) (vpT := vpT) L l (Γ' := Γ1)
    (SM.Engine.esG (.fst .v2)) (.snd .v2)
  simp only [SM.Engine.corrECShifted, SM.Engine.corrEC, SM.orE, SM.Engine.esMk,
    ReductionDsl.Comp.cost, ReductionDsl.Expr.cost]
  omega

private lemma implECShifted_cost_le_implEC {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : ReductionDsl.Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L l Δ qep maxSkip : ℕ) (cfg : SM.Engine.ConfigEC OO_cka) (π : SM.Engine.Policy)
    {Γ'} (es : ReductionDsl.Expr OO_cka Γ'
      (SM.Engine.esTy
        (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : ReductionDsl.Expr OO_cka Γ' (CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) :
    (SM.Engine.implECShifted hk L l Δ qep maxSkip cfg π es q).cost ≤
      (SM.Engine.implEC hk L Δ qep maxSkip cfg π es q).cost + 72 * ReductionDsl.bits l + 1300 := by
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := SM.Engine.esTy vpT hsT
  let smqT := CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let Γ_cr : List (ReductionDsl.Ty S_cka) := .bool :: .prod esT smqT :: Γ'
  have hcr := corrECShifted_cost_le_corrEC hk L l π (Γ' := Γ_cr) (.fst .v1) .v0
  simp only [SM.Engine.implECShifted, SM.Engine.implEC, ReductionDsl.Comp.cost, ReductionDsl.Expr.cost]
  omega

private lemma implECDFShifted_cost_le_implECDF {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : ReductionDsl.Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L l Δ qep maxSkip : ℕ) (cfg : SM.Engine.ConfigEC OO_cka) (π : SM.Engine.Policy)
    {Γ'} (es : ReductionDsl.Expr OO_cka Γ'
      (SM.Engine.esTy
        (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : ReductionDsl.Expr OO_cka Γ' (CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    (SM.Engine.implECDFShifted hk L l Δ qep maxSkip cfg π es q).cost ≤
      (SM.Engine.implECDF hk L Δ qep maxSkip cfg π es q).cost + 72 * ReductionDsl.bits l + 1300 := by
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := SM.Engine.esTy vpT hsT
  let smqT := CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let smqDFT := CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E
  let Γ_sm : List (ReductionDsl.Ty S_cka) := smqT :: .prod esT smqDFT :: Γ'
  have himpl := implECShifted_cost_le_implEC hk L l Δ qep maxSkip cfg π (Γ' := Γ_sm) (.fst .v1) .v0
  simp only [SM.Engine.implECDFShifted, SM.Engine.implECDF,
    ReductionDsl.Comp.cost, ReductionDsl.Expr.cost]
  omega

section HooksCKAShiftedCCost

open Computational.Proofs.GameHop.ReductionDsl.CostUB

private lemma cost_bind_ret_le_costUB {S : ReductionDsl.Sig} {O : ReductionDsl.Ops S}
    {ι : Type} {T : OracleSpec ι} {I : ReductionDsl.Iface S T}
    {Γ : List (ReductionDsl.Ty S)} {t u : ReductionDsl.Ty S}
    (e : ReductionDsl.Expr O Γ t) (k : ReductionDsl.Comp O I (t :: Γ) u) :
    (ReductionDsl.Comp.bind (.ret e) k).cost ≤ e.cost + compCostUB k + 2 := by
  have hk := compCost_le_costUB k
  simp only [ReductionDsl.Comp.cost]; omega

private lemma ret_pair_letE_cost_le_costUB {S : ReductionDsl.Sig} {O : ReductionDsl.Ops S}
    {ι : Type} {T : OracleSpec ι} {I : ReductionDsl.Iface S T}
    {Γ : List (ReductionDsl.Ty S)} {t u v : ReductionDsl.Ty S}
    (e : ReductionDsl.Expr O Γ t) (k : ReductionDsl.Expr O (t :: Γ) u)
    (r : ReductionDsl.Expr O Γ v) :
    (ReductionDsl.Comp.ret (I := I) (.pair (.letE e k) r)).cost ≤
      e.cost + r.cost + exprCostUB k + 3 := by
  have hk := exprCost_le_costUB k
  simp only [ReductionDsl.Comp.cost, ReductionDsl.Expr.cost]; omega

variable
  {sampKR : ProbComp KR}
  {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I}
  {sampK : ProbComp K}

private lemma hooksCKAShiftedC_costBounded (B l tStar : ℕ) :
    HooksCostBounded
      (SM.Construction.hooksCKAShiftedC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B l tStar)
      (5 * ReductionDsl.bits l + ReductionDsl.bits tStar + (B + 1) + 2030) where
  startSend_le h ctx p t γv σ r := by
    have hl1 := bits_succ_le l
    have hl2 : ReductionDsl.bits (l + 2) ≤ ReductionDsl.bits (l + 1) + 1 := bits_succ_le (l + 1)
    have hb1 : ReductionDsl.bits 1 = 1 := rfl
    dsimp only [SM.Construction.hooksCKAShiftedC, SM.Construction.ckaShiftedStartSendC]
    refine (cost_bind_ret_le_costUB _ _).trans ?_
    simp only [SM.Construction.ckaShiftedSetCache, SM.Construction.ckaShiftedSetΓPre,
      SM.pSet, SM.leN, CKA.ckaIface, CKA.ckaSamplers, CKA.ckaOps,
      ReductionDsl.Expr.cost, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1,
      ReductionDsl.Expr.v2, ReductionDsl.Expr.v3, ReductionDsl.Expr.v4,
      dsl_cost, compCostUB, exprCostUB, hb1, Nat.reduceAdd]
    omega
  startRecv_le h ctx p t γv σ tn := by
    dsimp only [SM.Construction.hooksCKAShiftedC, SM.Construction.ckaShiftedStartRecvC,
      SM.Construction.ckaStartRecvAnsE]
    refine (ret_pair_letE_cost_le_costUB _ _ _).trans ?_
    simp only [CKA.ckaOps, ReductionDsl.Expr.cost,
      ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2,
      dsl_cost, exprCostUB, Nat.reduceAdd]
    omega
  fsSend_le h ctx p t ss hdr m pair := by
    simp only [SM.Construction.hooksCKAShiftedC, SM.Construction.ckaShiftedFsSendC, CKA.ckaOps,
      ReductionDsl.Comp.cost, ReductionDsl.Expr.cost]
    omega
  fsRecv_le h ctx p t rs hdr e rec_ := by
    have hB := ReductionDsl.bits_le_succ B
    simp only [SM.Construction.hooksCKAShiftedC, SM.Construction.ckaShiftedFsRecvC, CKA.ckaOps,
      ReductionDsl.Comp.cost, ReductionDsl.Expr.cost]
    omega
  commit_le h ctx p old new := by
    have hl1 := bits_succ_le l
    have hl2 : ReductionDsl.bits (l + 2) ≤ ReductionDsl.bits (l + 1) + 1 := bits_succ_le (l + 1)
    have hb1 : ReductionDsl.bits 1 = 1 := rfl
    dsimp only [SM.Construction.hooksCKAShiftedC, SM.Construction.ckaShiftedCommitC]
    refine (cost_bind_ret_le_costUB _ _).trans ?_
    simp only [SM.Construction.ckaShiftedSetΓPre, SM.pSet, SM.isSomeE, SM.leN,
      SM.Engine.vpTcurNat, SM.Engine.vpΓ, SM.Engine.vpSetΓ,
      SM.Engine.vpMk, SM.Engine.vpId, SM.Engine.vpRoot, SM.Engine.vpVS, SM.Engine.vpVR,
      SM.Engine.vpTcur, CKA.ckaIface, ReductionDsl.Expr.cost,
      ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2,
      ReductionDsl.Expr.v3, ReductionDsl.Expr.v4,
      dsl_cost, compCostUB, exprCostUB, hb1, Nat.reduceAdd]
    omega
  reveal_le h ctx p vp := by
    have hb1 : ReductionDsl.bits 1 = 1 := rfl
    dsimp only [SM.Construction.hooksCKAShiftedC, SM.Construction.ckaShiftedRevealC]
    refine (cost_bind_ret_le_costUB _ _).trans ?_
    simp only [SM.Engine.realPartyE,
      SM.Engine.vpMk, SM.Engine.vpId, SM.Engine.vpRoot, SM.Engine.vpVS, SM.Engine.vpVR,
      SM.Engine.vpΓ, SM.Engine.vpTcur, SM.Engine.vpTcurNat, SM.leN, SM.pGet,
      CKA.ckaIface, ReductionDsl.Expr.cost,
      ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2,
      dsl_cost, compCostUB, exprCostUB, hb1, Nat.reduceAdd]
    omega

private lemma initCKAShiftedEStateC_cost_le (l : ℕ) {Γ'}
    (bE : ReductionDsl.Expr OO_cka Γ' .bool) :
    (SM.Construction.initCKAShiftedEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) l bE).cost ≤ bE.cost + 800 := by
  dsimp only [SM.Construction.initCKAShiftedEStateC]
  refine (cost_bind_ret_le_costUB _ _).trans ?_
  simp only [SM.Engine.mkPartiesE, SM.Engine.cGsInitE,
    SM.Engine.cGsMk, SM.Engine.vpMk, SM.Engine.esMk,
    CKA.ckaIface, CKA.ckaSamplers, CKA.ckaOps,
    ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2,
    dsl_cost, Nat.reduceAdd]
  omega

end HooksCKAShiftedCCost

private abbrev dfStepBound (q qep : ℕ) : ℕ :=
  let L := q + 1
  let B := (q + 1) * (maxForwardJumps + 1)
  25000 * L + L * (3 * ReductionDsl.bits qep + 60) + 3 * B +
    200 * ReductionDsl.bits qep + 350000

private lemma df_poly_le_ratchetCostBudget (q qep : ℕ) :
    (q + 1) * dfStepBound q qep ≤ ratchetCostBudget q qep := by
  unfold ratchetCostBudget dfStepBound
  dsimp only
  set M := maxForwardJumps + ReductionDsl.bits qep
  set L := q + 1
  set B := (q + 1) * (maxForwardJumps + 1)
  have hmfj : maxForwardJumps = 25000 := rfl
  have hbq : 1 ≤ ReductionDsl.bits qep := ReductionDsl.one_le_bits qep
  have hL_pos : 1 ≤ L := by omega
  have hM_lb : 25001 ≤ M := by omega
  have hm_le : maxForwardJumps + 1 ≤ M := by omega
  have hB_le : B ≤ L * M := Nat.mul_le_mul_left L hm_le
  have h25000L : 25000 * L ≤ L * M := by
    calc 25000 * L = L * 25000 := Nat.mul_comm _ _
      _ ≤ L * M := Nat.mul_le_mul_left L (by omega)
  have h3b : 3 * ReductionDsl.bits qep + 60 ≤ 4 * M := by omega
  have hL3b : L * (3 * ReductionDsl.bits qep + 60) ≤ 4 * (L * M) :=
    (Nat.mul_le_mul_left L h3b).trans_eq (by ring)
  have hb_LM : ReductionDsl.bits qep ≤ L * M := by
    calc ReductionDsl.bits qep ≤ M := by omega
      _ = 1 * M := (Nat.one_mul M).symm
      _ ≤ L * M := Nat.mul_le_mul_right M hL_pos
  have h1_LM : 25001 ≤ L * M := by
    calc 25001 = 1 * 25001 := (Nat.one_mul _).symm
      _ ≤ L * M := Nat.mul_le_mul hL_pos hM_lb
  have hsum :
      25000 * L + L * (3 * ReductionDsl.bits qep + 60) + 3 * B +
        200 * ReductionDsl.bits qep + 350000 ≤
        2 ^ 12 * (L * M) := by
    omega
  calc (q + 1) * (25000 * L + L * (3 * ReductionDsl.bits qep + 60) +
          3 * B + 200 * ReductionDsl.bits qep + 350000)
      ≤ (q + 1) * (2 ^ 12 * (L * M)) := Nat.mul_le_mul_left (q + 1) hsum
    _ = 2 ^ 12 * (q + 1) ^ 2 * M := by
      change (q + 1) * (2 ^ 12 * ((q + 1) * M)) = 2 ^ 12 * (q + 1) ^ 2 * M
      ring

private lemma add_mul_le_ratchetCostBudget_df {q qep a b : ℕ}
    (ha : a ≤ dfStepBound q qep) (hb : b ≤ dfStepBound q qep) :
    a + q * b ≤ ratchetCostBudget q qep := by
  have hmul : q * b ≤ q * dfStepBound q qep := Nat.mul_le_mul_left q hb
  have hring : (q + 1) * dfStepBound q qep = q * dfStepBound q qep + dfStepBound q qep := by
    rw [Nat.add_mul, Nat.one_mul]
  have h1 : a + q * b ≤ (q + 1) * dfStepBound q qep := by omega
  exact h1.trans (df_poly_le_ratchetCostBudget q qep)

private lemma implECDF_step_le_dfStepBound {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : ReductionDsl.Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (q qep : ℕ)
    (mo : SM.Construction.Mode)
    (htStar : mo.tStar < qep + 2)
    (htL : mo.tL.getD 0 ≤ mo.tStar)
    (hhk : HooksCostBounded hk
      (let L := q + 1
       let B := (q + 1) * (maxForwardJumps + 1)
       320 * L + 10 * ReductionDsl.bits qep + B + 2500)) :
    (SM.Engine.implECDF
      (Γ' := [SM.Engine.esTy
        (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
        CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E])
      hk (q + 1) 3 qep maxForwardJumps
      (SM.Engine.modeCfgEC OO_cka mo) mo.policy .v0 .v1).cost + 13 ≤
      dfStepBound q qep := by
  let L := q + 1
  let B := (q + 1) * (maxForwardJumps + 1)
  have hmfj : maxForwardJumps = 25000 := rfl
  have htStar_bits := bits_le_bits_qep_add (x := mo.tStar) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add (x := mo.tL.getD 0) (qep := qep) (by omega)
  have himpl := implECDF_cost_le hk
    (320 * L + 10 * ReductionDsl.bits qep + B + 2500)
    L qep maxForwardJumps mo hhk
    (Γ' := [SM.Engine.esTy
      (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
      CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  simp only [v0_cost, v1_cost] at himpl
  have hmul :
      L * (ReductionDsl.bits (mo.tL.getD 0) + 2 * ReductionDsl.bits mo.tStar + 40) ≤
        L * (3 * ReductionDsl.bits qep + 60) :=
    Nat.mul_le_mul_left L (by omega)
  dsimp only [L, B, dfStepBound] at himpl hmul ⊢
  omega

private lemma implECDFShifted_step_le_dfStepBound {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : ReductionDsl.Iface S_cka (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : ReductionDsl.Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (q qep l : ℕ)
    (mo : SM.Construction.Mode)
    (htStar : mo.tStar < qep + 2)
    (htL : mo.tL.getD 0 ≤ mo.tStar)
    (hl : l ≤ mo.tStar)
    (hhk : HooksCostBounded hk
      (let L := q + 1
       let B := (q + 1) * (maxForwardJumps + 1)
       320 * L + 10 * ReductionDsl.bits qep + B + 2500)) :
    (SM.Engine.implECDFShifted
      (Γ' := [SM.Engine.esTy
        (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
        CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E])
      hk (q + 1) l 3 qep maxForwardJumps
      (SM.Engine.modeCfgEC OO_cka mo) mo.policy .v0 .v1).cost + 13 ≤
      dfStepBound q qep := by
  let L := q + 1
  let B := (q + 1) * (maxForwardJumps + 1)
  have hmfj : maxForwardJumps = 25000 := rfl
  have htStar_bits := bits_le_bits_qep_add (x := mo.tStar) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add (x := mo.tL.getD 0) (qep := qep) (by omega)
  have hl_bits := bits_le_bits_qep_add (x := l) (qep := qep) (by omega)
  have hsh := implECDFShifted_cost_le_implECDF hk L l 3 qep maxForwardJumps
    (SM.Engine.modeCfgEC OO_cka mo) mo.policy
    (Γ' := [SM.Engine.esTy
      (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
      CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  have himpl := implECDF_cost_le hk
    (320 * L + 10 * ReductionDsl.bits qep + B + 2500)
    L qep maxForwardJumps mo hhk
    (Γ' := [SM.Engine.esTy
      (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
      CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  simp only [v0_cost, v1_cost] at himpl
  have hmul :
      L * (ReductionDsl.bits (mo.tL.getD 0) + 2 * ReductionDsl.bits mo.tStar + 40) ≤
        L * (3 * ReductionDsl.bits qep + 60) :=
    Nat.mul_le_mul_left L (by omega)
  dsimp only [L, B, dfStepBound] at hsh himpl hmul ⊢
  omega

private lemma healEpoch_le_of_getD_le {t : ℕ} {tL : Option ℕ} (htL : tL.getD 0 ≤ t) :
    healEpoch tL ≤ t + 2 := by
  rcases tL with _ | l <;> simp only [Option.getD_none, Option.getD_some, healEpoch] at htL ⊢ <;>
    omega

theorem redCKAAuthDFProg_totalCost_le
    {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
    {sampI : ProbComp I} {sampK : ProbComp K}
    (q qep t : ℕ) (tL : Option ℕ) (ht : t < qep + 2) (htL : tL.getD 0 ≤ t) :
    (SM.Construction.redCKAAuthDFProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 qep maxForwardJumps tL t).totalCost q ≤
      ratchetCostBudget q qep := by
  have htL2 := healEpoch_le_of_getD_le htL
  let L := q + 1
  let B := (q + 1) * (maxForwardJumps + 1)
  let mo : SM.Construction.Mode := ⟨true, tL, t⟩
  have hmfj : maxForwardJumps = 25000 := rfl
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add (x := tL.getD 0) (qep := qep) (by omega)
  have htH_bits := bits_le_bits_qep_add (x := healEpoch tL) (qep := qep) (by omega)
  have hhk := (hooksCKAC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B mo).mono
    (H' := 320 * L + 10 * ReductionDsl.bits qep + B + 2500)
    (by dsimp only [L, B, mo, SM.Construction.Mode.tH]; omega)
  have hstep := implECDF_step_le_dfStepBound _ q qep mo ht htL hhk
  have hout := authOutE_cost_le (O' := OO_cka)
    (vpT := @SM.Construction.ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E)
    (hsT := @SM.Construction.ckaHsTy KC Γ CCoins T I KR RSt K SS RS M E)
    L mo.policy (Γ' := [SM.Construction.ckaEsTy, .bool]) .v0
  simp only [v0_cost] at hout
  rw [SM.Construction.redCKAAuthDFProg_totalCost, add_right_comm]
  refine add_mul_le_ratchetCostBudget_df ?_ hstep
  simp only [Nat.reduceAdd] at hout ⊢
  dsimp only [L, B, mo, SM.Construction.Mode.tH, SM.Construction.Mode.policy, dfStepBound]
    at hout ⊢
  omega

theorem redPRNGAuthDFProg_totalCost_le
    {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
    {sampI : ProbComp I} {sampK : ProbComp K}
    (q qep t : ℕ) (tL : Option ℕ) (ht : t < qep + 2) (htL : tL.getD 0 ≤ t) :
    (SM.Construction.redPRNGAuthDFProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 qep maxForwardJumps tL t).totalCost q ≤
      ratchetCostBudget q qep := by
  have htL2 := healEpoch_le_of_getD_le htL
  let L := q + 1
  let B := (q + 1) * (maxForwardJumps + 1)
  let mo : SM.Construction.Mode := ⟨true, tL, t⟩
  have hmfj : maxForwardJumps = 25000 := rfl
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add (x := tL.getD 0) (qep := qep) (by omega)
  have htH_bits := bits_le_bits_qep_add (x := healEpoch tL) (qep := qep) (by omega)
  have hhk := (hooksPRNGC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B mo).mono
    (H' := 320 * L + 10 * ReductionDsl.bits qep + B + 2500)
    (by dsimp only [L, B, mo, SM.Construction.Mode.tH]; omega)
  have hstep := implECDF_step_le_dfStepBound _ q qep mo ht htL hhk
  have hinit := initPRNGEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) mo (Γ' := [.unit]) (.bool false)
  have hout := authOutE_cost_le (O' := OO_cka)
    (vpT := @SM.Construction.prngVpTy KC Γ CCoins T I KR RSt K SS RS M E)
    (hsT := @SM.Construction.prngHsTy KC Γ CCoins T I KR RSt K SS RS M E)
    L mo.policy (Γ' := [SM.Construction.prngEsTy, .bool]) .v0
  simp only [v0_cost, ReductionDsl.Expr.cost] at hinit hout
  rw [SM.Construction.redPRNGAuthDFProg_totalCost, add_right_comm]
  refine add_mul_le_ratchetCostBudget_df ?_ hstep
  simp only [Nat.reduceAdd] at hinit hout ⊢
  dsimp only [L, B, mo, SM.Construction.Mode.tH, SM.Construction.Mode.policy, dfStepBound]
    at hinit hout ⊢
  omega

theorem redFSAuthDFProg_totalCost_le
    {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
    {sampI : ProbComp I} {sampK : ProbComp K}
    (q qep j t : ℕ) (tL : Option ℕ) (ht : t < qep + 2)
    (htL : tL.getD 0 ≤ t) (hj : j < q) :
    (SM.Construction.redFSAuthDFProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 qep maxForwardJumps j tL t).totalCost q ≤
      ratchetCostBudget q qep := by
  have htL2 := healEpoch_le_of_getD_le htL
  let L := q + 1
  let B := (q + 1) * (maxForwardJumps + 1)
  let mo : SM.Construction.Mode := ⟨true, tL, t⟩
  have hmfj : maxForwardJumps = 25000 := rfl
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add (x := tL.getD 0) (qep := qep) (by omega)
  have htH_bits := bits_le_bits_qep_add (x := healEpoch tL) (qep := qep) (by omega)
  have hhk := (hooksFSC_costBounded_linear (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B mo j).mono
    (H' := 320 * L + 10 * ReductionDsl.bits qep + B + 2500)
    (by dsimp only [L, B, mo, SM.Construction.Mode.tH]; omega)
  have hstep := implECDF_step_le_dfStepBound _ q qep mo ht htL hhk
  have hinit := initFSEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L mo j (Γ' := [.unit]) (.bool false)
  simp only [ReductionDsl.Expr.cost] at hinit
  rw [SM.Construction.redFSAuthDFProg_totalCost]
  refine add_mul_le_ratchetCostBudget_df ?_ hstep
  dsimp only [L, B, mo, SM.Construction.Mode.tH, dfStepBound] at hinit ⊢
  omega

theorem redCKAAuthDFShiftedProg_totalCost_le
    {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
    {sampI : ProbComp I} {sampK : ProbComp K}
    (q qep l t : ℕ) (ht : t < qep + 2) (hl : l ≤ t) :
    (SM.Construction.redCKAAuthDFShiftedProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) qep maxForwardJumps l t).totalCost q ≤
      ratchetCostBudget q qep := by
  let L := q + 1
  let B := (q + 1) * (maxForwardJumps + 1)
  let mo : SM.Construction.Mode := ⟨true, some (l - 1), t⟩
  have hmfj : maxForwardJumps = 25000 := rfl
  have hmo_tL : mo.tL.getD 0 ≤ mo.tStar := by dsimp [mo]; omega
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have hl_bits := bits_le_bits_qep_add (x := l) (qep := qep) (by omega)
  have hl1_bits := bits_le_bits_qep_add (x := l - 1) (qep := qep) (by omega)
  have hhk := (hooksCKAShiftedC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B l t).mono
    (H' := 320 * L + 10 * ReductionDsl.bits qep + B + 2500)
    (by dsimp only [L, B]; omega)
  have hstep := implECDFShifted_step_le_dfStepBound _ q qep l mo ht hmo_tL hl hhk
  have hinit := initCKAShiftedEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) l (Γ' := [.unit]) (.bool false)
  have hout := authOutE_cost_le (O' := OO_cka)
    (vpT := @SM.Construction.ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E)
    (hsT := @SM.Construction.ckaShiftedHsTy KC Γ CCoins T I KR RSt K SS RS M E)
    L mo.policy (Γ' := [SM.Construction.ckaShiftedEsTy, .bool]) .v0
  simp only [v0_cost, ReductionDsl.Expr.cost] at hinit hout
  rw [SM.Construction.redCKAAuthDFShiftedProg_totalCost, add_right_comm]
  refine add_mul_le_ratchetCostBudget_df ?_ hstep
  dsimp only [L, B, mo, SM.Construction.Mode.tH, SM.Construction.Mode.policy, dfStepBound]
    at hinit hout ⊢
  simp only [Option.getD_some, Nat.reduceAdd] at hinit hout ⊢
  omega

theorem redPRNGAuthDFShiftedProg_totalCost_le
    {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
    {sampI : ProbComp I} {sampK : ProbComp K}
    (q qep l t : ℕ) (ht : t < qep + 2) (hl : l ≤ t) :
    (SM.Construction.redPRNGAuthDFShiftedProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 qep maxForwardJumps l t).totalCost q ≤
      ratchetCostBudget q qep := by
  let L := q + 1
  let B := (q + 1) * (maxForwardJumps + 1)
  let mo : SM.Construction.Mode := ⟨true, some (l - 1), t⟩
  have hmfj : maxForwardJumps = 25000 := rfl
  have hmo_tL : mo.tL.getD 0 ≤ mo.tStar := by dsimp [mo]; omega
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have hl_bits := bits_le_bits_qep_add (x := l) (qep := qep) (by omega)
  have hl1_bits := bits_le_bits_qep_add (x := l - 1) (qep := qep) (by omega)
  have htH_bits := bits_le_bits_qep_add (x := healEpoch (some (l - 1))) (qep := qep)
    (by dsimp [healEpoch]; omega)
  have hhk := (hooksPRNGC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B mo).mono
    (H' := 320 * L + 10 * ReductionDsl.bits qep + B + 2500)
    (by dsimp only [L, B, mo, SM.Construction.Mode.tH]; omega)
  have hstep := implECDFShifted_step_le_dfStepBound _ q qep l mo ht hmo_tL hl hhk
  have hinit := initPRNGEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) mo (Γ' := [.unit]) (.bool false)
  have hout := authOutE_cost_le (O' := OO_cka)
    (vpT := @SM.Construction.prngVpTy KC Γ CCoins T I KR RSt K SS RS M E)
    (hsT := @SM.Construction.prngHsTy KC Γ CCoins T I KR RSt K SS RS M E)
    L mo.policy (Γ' := [SM.Construction.prngEsTy, .bool]) .v0
  simp only [v0_cost, ReductionDsl.Expr.cost] at hinit hout
  rw [SM.Construction.redPRNGAuthDFShiftedProg_totalCost, add_right_comm]
  refine add_mul_le_ratchetCostBudget_df ?_ hstep
  dsimp only [L, B, mo, SM.Construction.Mode.tH, SM.Construction.Mode.policy, dfStepBound]
    at hinit hout ⊢
  simp only [Option.getD_some, Nat.reduceAdd] at hinit hout ⊢
  omega

theorem redFSAuthDFShiftedProg_totalCost_le
    {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
    {sampI : ProbComp I} {sampK : ProbComp K}
    (q qep j l t : ℕ) (ht : t < qep + 2) (hl : l ≤ t) (hj : j < q) :
    (SM.Construction.redFSAuthDFShiftedProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 qep maxForwardJumps j l t).totalCost q ≤
      ratchetCostBudget q qep := by
  let L := q + 1
  let B := (q + 1) * (maxForwardJumps + 1)
  let mo : SM.Construction.Mode := ⟨true, some (l - 1), t⟩
  have hmfj : maxForwardJumps = 25000 := rfl
  have hmo_tL : mo.tL.getD 0 ≤ mo.tStar := by dsimp [mo]; omega
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have hl_bits := bits_le_bits_qep_add (x := l) (qep := qep) (by omega)
  have hl1_bits := bits_le_bits_qep_add (x := l - 1) (qep := qep) (by omega)
  have htH_bits := bits_le_bits_qep_add (x := healEpoch (some (l - 1))) (qep := qep)
    (by dsimp [healEpoch]; omega)
  have hhk := (hooksFSC_costBounded_linear (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B mo j).mono
    (H' := 320 * L + 10 * ReductionDsl.bits qep + B + 2500)
    (by dsimp only [L, B, mo, SM.Construction.Mode.tH]; omega)
  have hstep := implECDFShifted_step_le_dfStepBound _ q qep l mo ht hmo_tL hl hhk
  have hinit := initFSEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L mo j (Γ' := [.unit]) (.bool false)
  simp only [ReductionDsl.Expr.cost] at hinit
  rw [SM.Construction.redFSAuthDFShiftedProg_totalCost]
  refine add_mul_le_ratchetCostBudget_df ?_ hstep
  dsimp only [L, B, mo, SM.Construction.Mode.tH, dfStepBound] at hinit ⊢
  omega

end ShiftedDeliverForgeCost

end CryptoVerification.LibsignalSession
