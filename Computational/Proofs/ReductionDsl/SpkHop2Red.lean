/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SpkLeakRed
public import Computational.Specifications.Session.StatementSpkModel
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.Bridge
import Computational.Proofs.ReductionDsl.Notation
import Computational.Proofs.GameHop.ReductionDsl.CostUB
import Computational.Proofs.GameHop.ReductionDsl.MapIface

/-!
# Costed `hop2PrgRedK` and `hop2PrfRedK` Reductions

Defines `hop2PrgRedKProg` and `hop2PrfRedKProg` as `ReductionDsl.CostedReduction` programs for the
hop-2 PRG and PRF reductions, with evaluation bridges, query and cost bounds, and `spkHopBudget`
combinators.
-/

@[expose] public section

namespace CryptoVerification.E2E.Costed

open ReductionDsl OracleComp OracleSpec CryptoGames CryptoGames.SM CryptoGames.PRF.Costed
  CryptoGames.PRG.Costed CryptoGames.LibsignalSM CryptoGames.Ratchet
  CryptoGames.Ratchet.LibsignalInst CryptoGames.LibsignalSession CryptoGames.CKA
  CryptoGames.MACScheme CryptoGames.HKDF CryptoGames.HMAC CBC
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E
open scoped Computational.Proofs.ReductionDsl.Notation

local macro_rules
  | `(rdsl_pat| .transmit $p:term)  => `(rdsl_pat| .inl (.inl (.inl (.inl $p))))
  | `(rdsl_pat| .challenge $p:term) => `(rdsl_pat| .inl (.inl (.inl (.inr $p))))
  | `(rdsl_pat| .deliver $p:term)   => `(rdsl_pat| .inl (.inl (.inr $p)))
  | `(rdsl_pat| .inject $p:term)    => `(rdsl_pat| .inl (.inr $p))
  | `(rdsl_pat| .corrupt $p:term)   => `(rdsl_pat| .inr $p)

/-! ## Lifting `e2ePrgIface` computations to `e2ePrfIface` -/

section ToPrf

variable {Pt : Type} {PQC : Type} [SampleableType PQC] {ℓ : ℕ}

local notation "S" => spkLeakSessionSig Pt ℓ PQC

def _root_.ReductionDsl.Comp.toPrf
    {O' : Ops S} :
    {Γ : List (Ty S)} → {t : Ty S} →
    Comp O' (e2ePrgIface Pt ℓ PQC) Γ t → Comp O' (e2ePrfIface Pt ℓ PQC) Γ t
  | _, _, .ret e => .ret e
  | _, _, .bind c k => .bind c.toPrf k.toPrf
  | _, _, .ite b c d => .ite b c.toPrf d.toPrf
  | _, _, .caseOpt e n s => .caseOpt e n.toPrf s.toPrf
  | _, _, .caseSum e l r => .caseSum e l.toPrf r.toPrf
  | _, _, .sample s e => .sample (I := e2ePrfIface Pt ℓ PQC) s e
  | _, _, .query g _ => g.elim
  | _, _, .iter n e body => .iter n e body.toPrf
  | _, _, .findM K l p => .findM K l p.toPrf
  | _, _, .anyM K l p => .anyM K l p.toPrf
  | _, _, .mapM K l f => .mapM K l f.toPrf
  | _, _, .consumeFirstM K l p mark => .consumeFirstM K l p.toPrf mark
  | _, _, .foldM K l z f => .foldM K l z f.toPrf

@[reducible] def _root_.ReductionDsl.CostedReduction.toPrf
    {O' : Ops S} {κ : Type} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (R : CostedReduction O' (e2ePrgIface Pt ℓ PQC) G C rIn aIn aOut out) :
    CostedReduction O' (e2ePrfIface Pt ℓ PQC) G C rIn aIn aOut out where
  σ := R.σ
  init := R.init.toPrf
  handle := R.handle.toPrf
  finish := R.finish.toPrf

open Computational.Proofs.GameHop.ReductionDsl.MapIface
  (simulateQ_iterM simulateQ_findML simulateQ_anyML simulateQ_mapML
   simulateQ_consumeFirstML simulateQ_foldML simulateQ_liftP_eq_self)
open Computational.Proofs.GameHop.ReductionDsl.CostUB

@[simp] theorem simulateQ_ofLift_add_liftM
    (prfImpl : QueryImpl (MACScheme.prfSpec Pt (BitVec 256)) ProbComp)
    {α : Type} (p : ProbComp α) :
    simulateQ (QueryImpl.ofLift unifSpec ProbComp + prfImpl)
      (liftM p : Hop2Comp Pt α) = p := by
  have h := simulateQ_liftP_eq_self (e2ePrfIface Pt 0 Unit)
    (QueryImpl.ofLift unifSpec ProbComp + prfImpl) (fun _ => rfl) p
  rwa [e2ePrfIface_liftP] at h

@[simp] theorem _root_.ReductionDsl.Comp.eval_toPrf {O' : Ops S}
    (prfImpl : QueryImpl (MACScheme.prfSpec Pt (BitVec 256)) ProbComp)
    {Γ : List (Ty S)} {t : Ty S}
    (c : Comp O' (e2ePrgIface Pt ℓ PQC) Γ t) (ρ : Env Γ) :
    simulateQ (QueryImpl.ofLift unifSpec ProbComp + prfImpl) (c.toPrf.eval ρ) = c.eval ρ := by
  induction c with
  | ret e => simp [Comp.toPrf, Comp.eval]
  | bind m k ihm ihk =>
    simp only [Comp.toPrf, Comp.eval, simulateQ_bind, ihm]
    exact bind_congr fun x => ihk (.cons x ρ)
  | ite b th el ihth ihel =>
    simp only [Comp.toPrf, Comp.eval]; split <;> [exact ihth ρ; exact ihel ρ]
  | caseOpt e n s ihn ihs =>
    simp only [Comp.toPrf, Comp.eval]; cases e.eval ρ <;> [exact ihn ρ; exact ihs _]
  | caseSum e l r ihl ihr =>
    simp only [Comp.toPrf, Comp.eval]; cases e.eval ρ <;> [exact ihl _; exact ihr _]
  | sample s e =>
    dsimp only [Comp.toPrf, Comp.eval, e2ePrfIface]
    rw [prfIface_withSamp_liftP, prgIface_withSamp_liftP]
    exact simulateQ_ofLift_add_liftM prfImpl _
  | query g _ => exact g.elim
  | iter _ _ _ ih =>
    simp only [Comp.toPrf, Comp.eval, simulateQ_iterM]; congr 1; funext a; exact ih (.cons a ρ)
  | findM _ _ _ ih =>
    simp only [Comp.toPrf, Comp.eval, simulateQ_findML]; congr 1; funext x; exact ih (.cons x ρ)
  | anyM _ _ _ ih =>
    simp only [Comp.toPrf, Comp.eval, simulateQ_anyML]; congr 1; funext x; exact ih (.cons x ρ)
  | mapM _ _ _ ih =>
    simp only [Comp.toPrf, Comp.eval, simulateQ_mapML]; congr 1; funext x; exact ih (.cons x ρ)
  | consumeFirstM _ _ _ _ ih =>
    simp only [Comp.toPrf, Comp.eval, simulateQ_consumeFirstML]; congr 1; funext x; exact ih (.cons x ρ)
  | foldM _ _ _ _ ih =>
    simp only [Comp.toPrf, Comp.eval, simulateQ_foldML]
    congr 1; funext x; funext acc; exact ih (.cons x (.cons acc ρ))

@[simp] theorem _root_.ReductionDsl.Comp.queries_empty_zero {O' : Ops S} {Γ : List (Ty S)} {t : Ty S}
    (c : Comp O' (e2ePrgIface Pt ℓ PQC) Γ t) :
    c.queries Empty.elim (fun _ => 0) = 0 := by
  induction c with
  | query g _ => exact g.elim
  | _ => simp [Comp.queries, *]

theorem simulateQ_run_toPrf_impl {O' : Ops S} {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S}
    (R : CostedReduction O' (e2ePrgIface Pt ℓ PQC) G C rIn aIn aOut out)
    (prfImpl : QueryImpl (MACScheme.prfSpec Pt (BitVec 256)) ProbComp)
    {α : Type} (oa : OracleComp (unifSpec + G) α) (st : R.σ.denote) :
    simulateQ (QueryImpl.ofLift unifSpec ProbComp + prfImpl)
      ((simulateQ R.toPrf.impl oa).run st) =
      (simulateQ R.impl oa).run st := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a => simp [simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind, simulateQ_bind]
    cases q with
    | inl n =>
      have hinl : (R.toPrf.impl (.inl n)).run st = liftM ((R.impl (.inl n)).run st) := by
        dsimp only [CostedReduction.toPrf, CostedReduction.impl, handlerImpl, StateT.run_lift,
          e2ePrfIface, e2ePrgIface, Iface.withSamp, prfIface, prgIface]
        exact (liftM_unif_query_bind n (fun a => pure (a, st))).symm
      rw [hinl, simulateQ_ofLift_add_liftM]
      exact bind_congr fun p => ih p.1 p.2
    | inr t =>
      dsimp only [CostedReduction.toPrf, CostedReduction.impl, handlerImpl, StateT.run_mk]
      rw [simulateQ_bind, Comp.eval_toPrf]
      simp only [bind_assoc, pure_bind, simulateQ_pure]
      exact bind_congr fun p => ih (C.rdec t p.1) p.2

theorem _root_.ReductionDsl.CostedReduction.eval_toPrf {O' : Ops S} {κ : Type} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (R : CostedReduction O' (e2ePrgIface Pt ℓ PQC) G C rIn aIn aOut out)
    (prfImpl : QueryImpl (MACScheme.prfSpec Pt (BitVec 256)) ProbComp)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (x : rIn.denote) :
    R.eval A x =
      simulateQ (QueryImpl.ofLift unifSpec ProbComp + prfImpl) (R.toPrf.eval A x) := by
  dsimp only [CostedReduction.eval, CostedReduction.toPrf]
  rw [simulateQ_bind, Comp.eval_toPrf]
  refine bind_congr fun ⟨x0, s0⟩ => ?_
  rw [simulateQ_bind, simulateQ_run_toPrf_impl]
  refine bind_congr fun ⟨y, sF⟩ => ?_
  exact (Comp.eval_toPrf prfImpl R.finish (.cons sF (.cons y .nil))).symm
end ToPrf

/-! ## State representation and DSL definitions -/

section Hop2Types

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type} {ℓ : ℕ}

local notation "S" => spkLeakSessionSig Pt ℓ PQC
local notation "GS" => @gsTy Pt (GhostState Bytes) Unit (CBC.Plain ℓ) PQC (BitVec 256) Bytes

@[reducible] def hop2EntryTy : Ty S :=
  .prod (.prod .nat (.base .key)) (.base .rcoins)

@[reducible] def hop2AuxTy : Ty S :=
  .prod (.list hop2EntryTy)
    (.prod (.list hop2EntryTy)
      (.prod (.prod (.opt .nat) (.opt .nat))
        (.prod (.prod (.base .rcoins) (.base .rcoins)) .bool)))

@[reducible] def hop2ChallTy : Ty S :=
  .prod (.base .rcoins) (.base .rcoins)

@[reducible] def hop2StTy : Ty S :=
  .prod GS (.prod hop2AuxTy hop2ChallTy)

@[reducible] def hop2UpdTy : Ty S :=
  .prod (.opt .nat) (.prod (.base .rcoins) (.opt hop2EntryTy))

@[reducible] def hop2RecvResTy : Ty S :=
  .prod (.base .st) (.prod .nat (.prod .nat (.base .msg)))

@[reducible] def hop2OutTy : Ty S :=
  .opt (.prod hop2RecvResTy (.opt hop2UpdTy))

@[reducible] def hop2SendHalfResTy : Ty S :=
  .opt (.prod (.opt .nat)
    (.prod (.base .rcoins) (.prod (.base .rcoins) (.opt hop2EntryTy))))

def hop2AuxEnc (a : Hop2Aux Pt) : (hop2AuxTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ)).denote :=
  (a.lazy, a.made, (a.idx .A, a.idx .B), (a.coins .A, a.coins .B), a.bad)

def hop2AuxDec (v : (hop2AuxTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ)).denote) : Hop2Aux Pt where
  lazy := v.1
  made := v.2.1
  idx := fun | .A => v.2.2.1.1 | .B => v.2.2.1.2
  coins := fun | .A => v.2.2.2.1.1 | .B => v.2.2.2.1.2
  bad := v.2.2.2.2

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem hop2AuxDec_hop2AuxEnc (a : Hop2Aux Pt) :
    hop2AuxDec (PQC := PQC) (ℓ := ℓ) (hop2AuxEnc (PQC := PQC) (ℓ := ℓ) a) = a := by
  cases a
  simp only [hop2AuxEnc, hop2AuxDec, Hop2Aux.mk.injEq, true_and, and_true]
  exact ⟨funext fun | .A => rfl | .B => rfl, funext fun | .A => rfl | .B => rfl⟩

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem hop2AuxEnc_hop2AuxDec (v : (hop2AuxTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ)).denote) :
    hop2AuxEnc (PQC := PQC) (ℓ := ℓ) (hop2AuxDec (PQC := PQC) (ℓ := ℓ) v) = v := rfl

def hop2StDec (v : (hop2StTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ)).denote) :
    SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt :=
  (gsDec v.1, hop2AuxDec (PQC := PQC) (ℓ := ℓ) v.2.1)

def hop2StEnc (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt)
    (chall : Ratchet.RootKey × BitVec 256) : (hop2StTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ)).denote :=
  (gsEnc st.1, hop2AuxEnc (PQC := PQC) (ℓ := ℓ) st.2, chall)

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem hop2StDec_hop2StEnc
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt)
    (chall : Ratchet.RootKey × BitVec 256) :
    hop2StDec (PQC := PQC) (hop2StEnc (PQC := PQC) st chall) = st := by
  cases st
  simp [hop2StDec, hop2StEnc]

omit [DecidableEq Pt] [Zero Pt] in
theorem hop2StEnc_hop2StDec (v : (hop2StTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ)).denote) :
    hop2StEnc (PQC := PQC) (hop2StDec (PQC := PQC) v) v.2.2 = v := by
  rcases v with ⟨g, a, c⟩
  simp [hop2StDec, hop2StEnc]

def hop2UpdDec (v : (hop2UpdTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ)).denote) : Hop2Upd Pt :=
  ⟨v.1, v.2.1, v.2.2⟩

def hop2OutDec (v : (hop2OutTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ)).denote) : Hop2Out Pt ℓ :=
  v.map fun (r, u) => (r, u.map (hop2UpdDec (PQC := PQC) (ℓ := ℓ)))

def auxLazy
    {O' : Ops S} {Γ : List (Ty S)} (a : Expr O' Γ hop2AuxTy) :
    Expr O' Γ (.list hop2EntryTy) := .fst a
def auxMade
    {O' : Ops S} {Γ : List (Ty S)} (a : Expr O' Γ hop2AuxTy) :
    Expr O' Γ (.list hop2EntryTy) := .fst (.snd a)
def auxIdx
    {O' : Ops S} {Γ : List (Ty S)} (a : Expr O' Γ hop2AuxTy) :
    Expr O' Γ (.prod (.opt .nat) (.opt .nat)) := .fst (.snd (.snd a))
def auxCoins
    {O' : Ops S} {Γ : List (Ty S)} (a : Expr O' Γ hop2AuxTy) :
    Expr O' Γ (.prod (.base .rcoins) (.base .rcoins)) := .fst (.snd (.snd (.snd a)))
def auxBad
    {O' : Ops S} {Γ : List (Ty S)} (a : Expr O' Γ hop2AuxTy) :
    Expr O' Γ .bool := .snd (.snd (.snd (.snd a)))

def auxMk
    {O' : Ops S} {Γ : List (Ty S)}
    (lazy made : Expr O' Γ (.list hop2EntryTy))
    (idx : Expr O' Γ (.prod (.opt .nat) (.opt .nat)))
    (coins : Expr O' Γ (.prod (.base .rcoins) (.base .rcoins)))
    (bad : Expr O' Γ .bool) : Expr O' Γ hop2AuxTy :=
  .pair lazy (.pair made (.pair idx (.pair coins bad)))

def auxSetBad
    {O' : Ops S} {Γ : List (Ty S)} (auxE : Expr O' Γ hop2AuxTy)
    (badE : Expr O' Γ .bool) : Expr O' Γ hop2AuxTy :=
  .letE (.pair auxE badE)
    (auxMk (auxLazy (.fst .v0)) (auxMade (.fst .v0)) (auxIdx (.fst .v0)) (auxCoins (.fst .v0))
      (.snd .v0))

def auxConsLazy
    {O' : Ops S} {Γ : List (Ty S)} (auxE : Expr O' Γ hop2AuxTy)
    (eE : Expr O' Γ hop2EntryTy) : Expr O' Γ hop2AuxTy :=
  .letE (.pair auxE eE)
    (auxMk (.cons (.snd .v0) (auxLazy (.fst .v0))) (auxMade (.fst .v0))
      (auxIdx (.fst .v0)) (auxCoins (.fst .v0)) (auxBad (.fst .v0)))

def hop2CommitE
    {O' : Ops S} {Γ : List (Ty S)}
    (auxE : Expr O' Γ hop2AuxTy) (qE : Expr O' Γ .bool)
    (updOptE : Expr O' Γ (.opt hop2UpdTy)) : Expr O' Γ hop2AuxTy :=
  .letE (.pair auxE (.pair qE updOptE))
    (.caseOpt (.snd (.snd .v0))
      (.fst .v0)
      (let u : Expr O' _ hop2UpdTy := .v0
       let aux1 : Expr O' _ hop2AuxTy := .fst .v1
       let q1 : Expr O' _ .bool := .fst (.snd .v1)
       let made' : Expr O' _ (.list hop2EntryTy) :=
         .caseOpt (.snd (.snd u)) (auxMade aux1) (.cons .v0 (auxMade (.fst .v2)))
       auxMk (auxLazy aux1) made'
         (pSet (auxIdx aux1) q1 (.fst u))
         (pSet (auxCoins aux1) q1 (.fst (.snd u)))
         (auxBad aux1)))

end Hop2Types

section Hop2Prog

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type} [SampleableType PQC]
  (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (s : BitVec 256) (K B qep : ℕ)

local notation "S" => spkLeakSessionSig Pt ℓ PQC
local notation "OSM" => spkLeakSessionSmOps P ℓ decT encT
local notation "OO" => spkLeakSessionOps P ℓ Dh encPt encT decT s
local notation "II" => e2ePrfIface Pt ℓ PQC
local notation "IPRG" => e2ePrgIface Pt ℓ PQC
local notation "GS" => @gsTy Pt (GhostState Bytes) Unit (CBC.Plain ℓ) PQC (BitVec 256) Bytes
local notation "RR" => @smRrTy Pt (GhostState Bytes) Unit (CBC.Plain ℓ) PQC (BitVec 256) Bytes

def prgDrawBool {Γ : List (Ty S)} : Comp OO IPRG Γ .bool :=
  rdsl do sample (I := IPRG) (Sum.inr .bool) ()

def prgDrawBv {Γ : List (Ty S)} : Comp OO IPRG Γ (.base .rcoins) :=
  rdsl do sample (I := IPRG) (Sum.inr (.base true)) ()

def prgDrawCoins
    {O' : Ops S} {Γ : List (Ty S)} : Comp O' IPRG Γ (.opt (.base .coins)) :=
  rdsl do
    r ← sample (I := IPRG) (Sum.inr (.base false)) ()
    return some r

def hop2LookupE {Γ : List (Ty S)} (L : ℕ)
    (l : Expr OO Γ (.list hop2EntryTy))
    (tE : Expr OO Γ .nat) (qE : Expr OO Γ (.base .key)) :
    Expr OO Γ (.opt (.base .rcoins)) :=
  rdslExpr =>
    letE (l, (tE, qE)) (fun (xs, t0, q0) =>
      foldrB L xs none (fun ((tEnt, qEnt), val) acc =>
        if (t0 == tEnt) && opEqPt P ℓ Dh encPt encT decT s q0 qEnt then
          some val
        else
          acc))

def hop2LazyC
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (drawBv : ∀ {Γ}, Comp OO I Γ (.base .rcoins))
    {Γ : List (Ty S)}
    (auxE : Expr OO Γ hop2AuxTy) (tE : Expr OO Γ .nat) (qE : Expr OO Γ (.base .key)) :
    Comp OO I Γ (.prod (.base .rcoins) hop2AuxTy) :=
  rdsl do
    (aux0, tq0@(t0, q0)) ← return (auxE, (tE, qE))
    match hop2LookupE P ℓ Dh encPt encT decT s K (auxLazy aux0) t0 q0 with
    | none =>
      u ← drawBv
      return (u, auxConsLazy aux0 (tq0, u))
    | some u =>
      return (u, aux0)

def hop2FinishNoneC
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)}
    (aux1E : Expr OO Γ hop2AuxTy)
    (gE : Expr OO Γ (.base .st)) (cE : Expr OO Γ (.base .ct)) (rcE : Expr OO Γ (.base .rcoins))
    (rkckE : Expr OO Γ (.prod (.base .rcoins) (.base .rcoins))) :
    Comp OO I Γ (.prod hop2OutTy hop2AuxTy) :=
  rdsl do
    (aux1, g0, c0, rc0, rkM, ckR) ← return (aux1E, gE, cE, rcE, rkckE)
    match opSendHalfReal P ℓ Dh encPt encT decT s rkM c0 rc0 with
    | none => return (none, aux1)
    | some (rk2, ckS) =>
      match opFinishHop2DH P ℓ Dh encPt encT decT s B g0 c0 rc0 rk2 ckR ckS with
      | none => return (none, aux1)
      | some res =>
        return (some (res, some (none, (rc0, none))), aux1)

def hop2SendHalfC
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (k : ℕ)
    (drawBv : ∀ {Γ}, Comp OO I Γ (.base .rcoins))
    (stepC : ∀ {Γ}, Expr OO Γ (.base .rcoins) → Expr OO Γ (.base .key) →
      Comp OO I Γ (.base .rcoins))
    {Γ : List (Ty S)}
    (challE : Expr OO Γ hop2ChallTy) (idx1E : Expr OO Γ (.opt .nat))
    (rkME : Expr OO Γ (.base .rcoins)) (cE : Expr OO Γ (.base .ct))
    (rcE : Expr OO Γ (.base .rcoins)) (q'E : Expr OO Γ (.base .key)) :
    Comp OO I Γ hop2SendHalfResTy :=
  rdsl do
    ((chall1, chall2), idx1, rkM, c0, rc0, q'0) ← return (challE, idx1E, rkME, cE, rcE, q'E)
    match idx1 with
    | none =>
      match opSendHalfReal P ℓ Dh encPt encT decT s rkM c0 rc0 with
      | none => return none
      | some (rk', ck') => return some (none, (rk', (ck', none)))
    | some j0 =>
      if opIsZeroPt P ℓ Dh encPt encT decT s q'0 then
        return none
      else if j0 < nat k then
        ck ← drawBv
        let zeroBv := opZeroBv P ℓ Dh encPt encT decT s
        return some (some (j0 + 1), (zeroBv, (ck, some ((j0, q'0), ck))))
      else if j0 == nat k then
        let zeroBv := opZeroBv P ℓ Dh encPt encT decT s
        return some (some (j0 + 1), (zeroBv, (chall2, some ((j0, q'0), chall2))))
      else
        u ← stepC chall1 q'0
        let rkck := opRootExpand P ℓ Dh encPt encT decT s u
        return some (none, (rkck.1, (rkck.2, none)))

/-- Costed `hop2DH` handler, fusing the `idx1 = none` branch into `hop2FinishNoneC` so each branch makes at most one `stepC` query. -/
def hop2DHC
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (k : ℕ)
    (drawBv : ∀ {Γ}, Comp OO I Γ (.base .rcoins))
    (stepC : ∀ {Γ}, Expr OO Γ (.base .rcoins) → Expr OO Γ (.base .key) →
      Comp OO I Γ (.base .rcoins))
    {Γ : List (Ty S)}
    (auxE : Expr OO Γ hop2AuxTy) (challE : Expr OO Γ hop2ChallTy)
    (tE : Expr OO Γ .nat) (coinsE : Expr OO Γ (.base .rcoins))
    (gE : Expr OO Γ (.base .st)) (cE : Expr OO Γ (.base .ct))
    (rcE : Expr OO Γ (.base .rcoins)) :
    Comp OO I Γ (.prod hop2OutTy hop2AuxTy) :=
  rdsl do
    (aux0, chall0@(chall1_0, _), t0, coins0, g0, c0, rc0) ←
      return (auxE, challE, tE, coinsE, gE, cE, rcE)
    match opDhTargetPt P ℓ Dh encPt encT decT s g0 c0 with
    | none => return (none, aux0)
    | some targetPt =>
      let qPt := opDh P ℓ Dh encPt encT decT s coins0 targetPt
      if opIsZeroPt P ℓ Dh encPt encT decT s qPt then
        return (none, aux0)
      else if leN t0 (nat k) then
        match hop2LookupE P ℓ Dh encPt encT decT s (raw (K + 1)) (auxMade aux0) t0 qPt with
        | none =>
          (u, aux1) ← hop2LazyC P ℓ Dh encPt encT decT s K drawBv aux0 t0 qPt
          let rkck := opRootExpand P ℓ Dh encPt encT decT s u
          hop2FinishNoneC P ℓ Dh encPt encT decT s B aux1 g0 c0 rc0 rkck
        | some ck =>
          let zeroBv := opZeroBv P ℓ Dh encPt encT decT s
          let idx1E : Expr OO _ (.opt .nat) := .some (.add t0 (.nat 1))
          let q'Pt := opDh P ℓ Dh encPt encT decT s rc0 targetPt
          shOpt ← hop2SendHalfC P ℓ Dh encPt encT decT s k drawBv stepC
            chall0 idx1E zeroBv c0 rc0 q'Pt
          match shOpt with
          | none => return (none, aux0)
          | some (idx2, rk2, ckS, pend) =>
            match opFinishHop2DH P ℓ Dh encPt encT decT s B g0 c0 rc0 rk2 ck ckS with
            | none => return (none, aux0)
            | some res =>
              let upd := (idx2, (rc0, pend))
              return (some (res, some upd), aux0)
      else
        u ← stepC chall1_0 qPt
        let rkck := opRootExpand P ℓ Dh encPt encT decT s u
        hop2FinishNoneC P ℓ Dh encPt encT decT s B aux0 g0 c0 rc0 rkck

def hop2RecvC
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (k : ℕ)
    (drawBv : ∀ {Γ}, Comp OO I Γ (.base .rcoins))
    (stepC : ∀ {Γ}, Expr OO Γ (.base .rcoins) → Expr OO Γ (.base .key) →
      Comp OO I Γ (.base .rcoins))
    {Γ : List (Ty S)}
    (auxE : Expr OO Γ hop2AuxTy) (challE : Expr OO Γ hop2ChallTy)
    (gE : Expr OO Γ (.base .st)) (cE : Expr OO Γ (.base .ct))
    (rcE : Expr OO Γ (.base .rcoins)) :
    Comp OO I Γ (.prod hop2OutTy hop2AuxTy) :=
  rdsl do
    (aux0, chall0, g0, c0, rc0) ← return (auxE, challE, gE, cE, rcE)
    if opWireOk P ℓ Dh encPt encT decT s c0 then
      match pGet (auxIdx aux0) (opStParty P ℓ Dh encPt encT decT s g0) with
      | none =>
        match opReceive P ℓ Dh encPt encT decT s B g0 c0 rc0 with
        | none => return (none, aux0)
        | some recvRes => return (some (recvRes, none), aux0)
      | some tEpoch =>
        let coins1 := pGet (auxCoins aux0) (opStParty P ℓ Dh encPt encT decT s g0)
        if opNeedsDH P ℓ Dh encPt encT decT s g0 c0 then
          hop2DHC P ℓ Dh encPt encT decT s K B k drawBv stepC aux0 chall0 tEpoch coins1 g0 c0 rc0
        else
          match opReceive P ℓ Dh encPt encT decT s B g0 c0 rc0 with
          | none => return (none, aux0)
          | some recvRes => return (some (recvRes, none), aux0)
    else
      return (none, aux0)

def hop2DeliverC
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (k : ℕ)
    (drawBv : ∀ {Γ}, Comp OO I Γ (.base .rcoins))
    (stepC : ∀ {Γ}, Expr OO Γ (.base .rcoins) → Expr OO Γ (.base .key) →
      Comp OO I Γ (.base .rcoins))
    {Γ : List (Ty S)}
    (stE : Expr OO Γ hop2StTy) (argE : Expr OO Γ (.prod .bool (.base .ct))) :
    Comp OO I Γ (.prod (.opt RR) hop2StTy) :=
  rdsl do
    (st0@(gs0, aux0, chall0), pParty, c0) ← return (stE, argE)
    if gsWin gs0 then
      return (none, st0)
    else
      match ((inTransitE K gs0 (otherE pParty) c0 : Expr OSM _ (.opt recTy)).liftL) with
      | none => return (none, st0)
      | some rec0 =>
        rc ← drawBv
        let gQ := pGet (gsSt gs0) pParty
        (outOpt, auxAfter) ←
          hop2RecvC P ℓ Dh encPt encT decT s K B k drawBv stepC aux0 chall0 gQ c0 rc
        match outOpt with
        | none =>
          return (some (.inl ()), (gs0, (auxAfter, chall0)))
        | some ((st', t', i', m'), uOpt) =>
          let sSc := opSpkSc P ℓ Dh encPt encT decT s
          let badNow :=
            orE (auxBad auxAfter)
              (opBadAt P ℓ Dh encPt encT decT s sSc (pGet (gsSt gs0) pParty) c0)
          let auxFinal := auxSetBad (hop2CommitE auxAfter pParty uOpt) badNow
          let gsFinal := acceptE K gs0 pParty st' (recPos rec0)
          let msgOut := if challContainsE K gs0 (recPos rec0) then none else some m'
          return (some (.inr (t', i', msgOut)), (gsFinal, (auxFinal, chall0)))

def hop2InjectC
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (k : ℕ)
    (drawBv : ∀ {Γ}, Comp OO I Γ (.base .rcoins))
    (stepC : ∀ {Γ}, Expr OO Γ (.base .rcoins) → Expr OO Γ (.base .key) →
      Comp OO I Γ (.base .rcoins))
    {Γ : List (Ty S)}
    (stE : Expr OO Γ hop2StTy) (argE : Expr OO Γ (.prod .bool (.base .ct))) :
    Comp OO I Γ (.prod (.opt RR) hop2StTy) :=
  rdsl do
    (st0@(gs0, aux0, chall0), pParty, c0) ← return (stE, argE)
    let inTr0 := ((inTransitE K gs0 (otherE pParty) c0 : Expr OSM _ (.opt recTy)).liftL)
    let refuse :=
      orE (gsWin gs0)
        (orE (isSomeE inTr0)
          (orE (!(safeInjE (raw 3) gs0))
            (!(opInjOK P ℓ Dh encPt encT decT s c0))))
    if refuse then
      return (none, st0)
    else
      rc ← drawBv
      let gQ := pGet (gsSt gs0) pParty
      (outOpt, auxAfter) ←
        hop2RecvC P ℓ Dh encPt encT decT s K B k drawBv stepC aux0 chall0 gQ c0 rc
      match outOpt with
      | none =>
        return (some (.inl ()), (gs0, (auxAfter, chall0)))
      | some ((st', t', i', m'), uOpt) =>
        let sSc := opSpkSc P ℓ Dh encPt encT decT s
        let badNow :=
          orE (auxBad auxAfter)
            (opBadAt P ℓ Dh encPt encT decT s sSc (pGet (gsSt gs0) pParty) c0)
        let auxBadUpd := auxSetBad auxAfter badNow
        let pos := (otherE pParty, t', i')
        if nat (qep + 1) < t' then
          return (some (.inl ()), (gs0, (auxBadUpd, chall0)))
        else if trivialE K (raw 3) gs0 pos then
          return (some (.inr (t', i', some m')),
            (acceptE K gs0 pParty st' pos, (hop2CommitE auxBadUpd pParty uOpt, chall0)))
        else
          return (some (.inl ()), (gsSetWin gs0 true, (auxBadUpd, chall0)))

def hop2ImplC
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (k : ℕ)
    (drawCoins : ∀ {Γ}, Comp OSM I Γ (.opt (.base .coins)))
    (drawBv : ∀ {Γ}, Comp OO I Γ (.base .rcoins))
    (stepC : ∀ {Γ}, Expr OO Γ (.base .rcoins) → Expr OO Γ (.base .key) →
      Comp OO I Γ (.base .rcoins))
    {Γ : List (Ty S)}
    (stE : Expr OO Γ hop2StTy) (qE : Expr OO Γ (e2eCodec Pt ℓ PQC).Q) :
    Comp OO I Γ (.prod (e2eCodec Pt ℓ PQC).R hop2StTy) :=
  rdsl do
    (st0@(gs0, restSt), qry) ← return (stE, qE)
    match qry with
    | .transmit qTr =>
      res ← ((transmitRC (I := I) 3 qep (ConfigRC.spkS OSM) drawCoins gs0 qTr).liftL)
      return (.inl (.inl (.inl (.inl res.1))), (res.2, restSt))
    | .challenge qCh =>
      res ← ((challRC (I := I) 3 qep (ConfigRC.spkS OSM) drawCoins gs0 qCh).liftL)
      return (.inl (.inl (.inl (.inr res.1))), (res.2, restSt))
    | .deliver qDl =>
      res ← hop2DeliverC P ℓ Dh encPt encT decT s K B k drawBv stepC st0 qDl
      return (.inl (.inl (.inr res.1)), res.2)
    | .inject qIj =>
      res ← hop2InjectC P ℓ Dh encPt encT decT s K B qep k drawBv stepC st0 qIj
      return (.inl (.inr res.1), res.2)
    | .corrupt pCorr =>
      res ← ((corrRC (I := I) K (ConfigRC.spkS OSM) gs0 pCorr).liftL)
      return (.inr res.1, (res.2, restSt))

def hop2InitAfterChallC
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (k : ℕ)
    (drawBool : ∀ {Γ}, Comp OO I Γ .bool)
    (drawBv : ∀ {Γ}, Comp OO I Γ (.base .rcoins))
    {Γ : List (Ty S)}
    (challE : Expr OO Γ hop2ChallTy) :
    Comp OO I Γ (.prod .unit hop2StTy) :=
  rdsl do
    chall ← return challE
    b ← drawBool
    ck0 ← drawBv
    x ← drawBv
    alice ← drawBv
    pqr ← drawBv
    u1 ← drawBv
    let ck1 := if nat k == 0 then chall.2 else u1
    let zeroBv := opZeroBv P ℓ Dh encPt encT decT s
    let basePt := opBasePt P ℓ Dh encPt encT decT s
    let I0 := opDh P ℓ Dh encPt encT decT s x (opDh P ℓ Dh encPt encT decT s alice basePt)
    let stA := opInitA P ℓ Dh encPt encT decT s zeroBv ck0 x alice pqr ck1
    let stB := opInitB P ℓ Dh encPt encT decT s zeroBv ck0 x alice pqr
    let initGs :=
      gsMk (stA, stB) b false
        (0, 0) (0, 0)
        none [] [] []
        (tconst 0, tconst 0)
        [] []
    let initAux :=
      auxMk []
        [((0, I0), ck1)]
        (some 1, some 0)
        (alice, x)
        false
    return ((), (initGs, (initAux, chall)))

/-- Parameterized `CostedReduction` for `hop2Game`: takes `initChall` producing `chall` and `stepC` computing
table `k + 1`'s PRK. -/
def hop2GameRedProg
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (k : ℕ) {rIn : Ty S}
    (drawBool : ∀ {Γ}, Comp OO I Γ .bool)
    (drawCoins : ∀ {Γ}, Comp OSM I Γ (.opt (.base .coins)))
    (drawBv : ∀ {Γ}, Comp OO I Γ (.base .rcoins))
    (initChall : Comp OO I [rIn] hop2ChallTy)
    (stepC : ∀ {Γ}, Expr OO Γ (.base .rcoins) → Expr OO Γ (.base .key) →
      Comp OO I Γ (.base .rcoins)) :
    CostedReduction OO I (SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) (e2eCodec Pt ℓ PQC)
      rIn .unit .bool .bool where
  σ := hop2StTy
  init :=
    rdsl [_] do
      chall ← initChall
      hop2InitAfterChallC P ℓ Dh encPt encT decT s k drawBool drawBv chall
  handle :=
    rdsl [st0, qry] do
      hop2ImplC P ℓ Dh encPt encT decT s K B qep k drawCoins drawBv stepC st0 qry
  finish := rdsl [(_, aux0, _), _] do return auxBad aux0

/-- Costed `hop2PrgRedK` PRG reduction for hybrid `k`. -/
def hop2PrgRedKProg (k : ℕ) :
    CostedReduction (spkLeakSessionOps P ℓ Dh encPt encT decT s) (e2ePrgIface Pt ℓ PQC)
      (SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) (e2eCodec Pt ℓ PQC)
      (.prod (.base .rcoins) (.base .rcoins)) .unit .bool .bool :=
  hop2GameRedProg P ℓ Dh encPt encT decT s K B qep k
    (prgDrawBool P ℓ Dh encPt encT decT s)
    (prgDrawCoins ℓ (PQC := PQC))
    (prgDrawBv P ℓ Dh encPt encT decT s)
    (rdsl [rc] do return rc)
    (fun c1E qE => rdsl do return opExtractTag P ℓ Dh encPt encT decT s c1E qE)

/-- Costed `hop2PrfRedK` PRF reduction for hybrid `k`. -/
def hop2PrfRedKProg (k : ℕ) :
    CostedReduction (spkLeakSessionOps P ℓ Dh encPt encT decT s) (e2ePrfIface Pt ℓ PQC)
      (SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) (e2eCodec Pt ℓ PQC)
      .unit .unit .bool .bool :=
  hop2GameRedProg P ℓ Dh encPt encT decT s K B qep k
    (spkDrawBool P ℓ Dh encPt encT decT s)
    (spkDrawCoins ℓ (PQC := PQC))
    (spkDrawBv P ℓ Dh encPt encT decT s)
    (rdsl [_] do
      r ← spkDrawBv P ℓ Dh encPt encT decT s
      c ← spkDrawBv P ℓ Dh encPt encT decT s
      return (r, c))
    (fun _ qE => rdsl do query () qE)

end Hop2Prog

/-! ## Query-budget invariant `Hop2BudgetInv` -/

section Hop2BudgetInv

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type}
  (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (s : BitVec 256)

/-- Query-budget invariant for `hop2Game`: tracks `SMBudgetInv qAdv K q` on the `SM.GameState`
component together with `lazy.length + q ≤ K` and `made.length + q ≤ K + 1` on `Hop2Aux Pt`. -/
structure Hop2BudgetInv (qAdv K : ℕ) (q : ℕ)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt) : Prop where
  sm : SMBudgetInv qAdv K q st.1
  lazy_le : st.2.lazy.length + q ≤ K
  made_le : st.2.made.length + q ≤ K + 1

omit [DecidableEq Pt] [Zero Pt] in
theorem Hop2BudgetInv.mono {ℓ qAdv K m n : ℕ}
    {st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt}
    (hmn : m ≤ n) (h : Hop2BudgetInv (Pt := Pt) (ℓ := ℓ) qAdv K n st) :
    Hop2BudgetInv (Pt := Pt) (ℓ := ℓ) qAdv K m st := by
  have h1 := h.lazy_le
  have h2 := h.made_le
  exact ⟨h.sm.mono hmn, by omega, by omega⟩

omit [DecidableEq Pt] [Zero Pt] in
theorem Hop2BudgetInv.lazy_len_le {ℓ qAdv K q : ℕ}
    {st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt}
    (h : Hop2BudgetInv (Pt := Pt) (ℓ := ℓ) qAdv K q st) :
    st.2.lazy.length ≤ K := by
  have := h.lazy_le; omega

omit [DecidableEq Pt] [Zero Pt] in
theorem Hop2BudgetInv.made_len_le {ℓ qAdv K q : ℕ}
    {st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt}
    (h : Hop2BudgetInv (Pt := Pt) (ℓ := ℓ) qAdv K q st) :
    st.2.made.length ≤ K + 1 := by
  have := h.made_le; omega

omit [DecidableEq Pt] [Zero Pt] in
theorem Hop2BudgetInv.init {qAdv K : ℕ} (hK : qAdv * qAdv ≤ K * K)
    (stF : Party → GhostState Bytes) (b : Bool) (I0 : Pt) (ck1 alice x : BitVec 256) :
    Hop2BudgetInv (Pt := Pt) (ℓ := ℓ) qAdv K qAdv
      ({ st := stF, b := b },
       { made := [((0, I0), ck1)]
         idx := fun | .A => some 1 | .B => some 0
         coins := fun | .A => alice | .B => x }) := by
  have hsm := SMBudgetInv.init (Msg := CBC.Plain ℓ) (C := Bytes) hK stF b
  have hqK : qAdv ≤ K := hsm.qAdv_le
  exact ⟨hsm, by simp [hqK], by simp; omega⟩

omit [DecidableEq Pt] [Zero Pt] in
theorem mem_support_hop2Lift {α : Type}
    (m : StateT (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) ProbComp α)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt) (r : α × _) :
    r ∈ support ((hop2Lift (Pt := Pt) (ℓ := ℓ) m).run st) ↔
      (r.1, r.2.1) ∈ support (m.run st.1) ∧ r.2.2 = st.2 := by
  simp only [hop2Lift, StateT.run_mk, ← liftComp_eq_liftM, mem_support_bind_iff,
    support_liftComp, support_pure, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨a, gs'⟩, hmem, rfl⟩
    exact ⟨hmem, rfl⟩
  · rintro ⟨hmem, h2⟩
    refine ⟨(r.1, r.2.1), hmem, ?_⟩
    rcases r with ⟨a, gs', aux'⟩
    dsimp only at h2 ⊢
    subst h2; rfl

omit [Zero Pt] in
theorem hop2Lazy_support (t : ℕ) (Q : Pt)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt) :
    ∀ r ∈ support ((hop2Lazy (Pt := Pt) (ℓ := ℓ) t Q).run st),
      r.2.1 = st.1 ∧ r.2.2.lazy.length ≤ st.2.lazy.length + 1 ∧ r.2.2.made = st.2.made := by
  intro r hr
  unfold hop2Lazy at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  rcases hlk : st.2.lazy.lookup (t, Q) with _ | u
  · simp only [hlk, StateT.run_bind, StateT.run_set, StateT.run_pure,
      pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨u', -, rfl⟩ := hr
    exact ⟨rfl, le_rfl, rfl⟩
  · simp only [hlk, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨rfl, Nat.le_succ _, rfl⟩

theorem hop2RecvHalf_support (h : Hop2Hyb Pt) (idx : Option ℕ) (rk : Ratchet.RootKey)
    (their : PublicKey) (our : PrivateKey) (Q : Pt)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt) :
    ∀ r ∈ support ((hop2RecvHalf (ℓ := ℓ) P h idx rk their our Q).run st),
      r.2.1 = st.1 ∧ r.2.2.lazy.length ≤ st.2.lazy.length + 1 ∧ r.2.2.made = st.2.made := by
  intro r hr
  unfold hop2RecvHalf at hr
  rcases idx with _ | t
  · rcases hrc : rootCreateChain P.C rk their our with _ | ⟨rk', ck⟩ <;>
    · rw [hrc] at hr
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact ⟨rfl, Nat.le_succ _, rfl⟩
  · dsimp only at hr
    split_ifs at hr with hQ0 htk
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact ⟨rfl, Nat.le_succ _, rfl⟩
    · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
      rcases hlk : st.2.made.lookup (t, Q) with _ | ck
      · simp only [hlk, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hr
        obtain ⟨⟨u, s'⟩, hlazy, rfl⟩ := hr
        exact hop2Lazy_support ℓ t Q st (u, s') hlazy
      · simp only [hlk, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact ⟨rfl, Nat.le_succ _, rfl⟩
    · simp only [stateT_run_lift_bind, StateT.run_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨u, -, rfl⟩ := hr
      exact ⟨rfl, Nat.le_succ _, rfl⟩

theorem hop2DH_support (h : Hop2Hyb Pt) (idx : Option ℕ) (coins : BitVec 256)
    (g : GhostState Bytes) (msg : SignalMessage) (rc : BitVec 256)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt) :
    ∀ r ∈ support ((hop2DH (ℓ := ℓ) P Dh encT decT h idx coins g msg rc).run st),
      r.2.1 = st.1 ∧ r.2.2.lazy.length ≤ st.2.lazy.length + 1 ∧ r.2.2.made = st.2.made := by
  intro r hr
  unfold hop2DH at hr
  rcases hdec : decT msg.senderRatchetKey with _ | T
  · rw [hdec] at hr
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact ⟨rfl, Nat.le_succ _, rfl⟩
  · rw [hdec] at hr
    dsimp only at hr
    split_ifs at hr
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact ⟨rfl, Nat.le_succ _, rfl⟩
    · rcases hsc : g.session.senderChain with _ | sc
      · rw [hsc] at hr
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact ⟨rfl, Nat.le_succ _, rfl⟩
      · rw [hsc, StateT.run_bind] at hr
        simp only [mem_support_bind_iff] at hr
        obtain ⟨⟨rhRes, s1⟩, hrh, hr⟩ := hr
        have h1 := hop2RecvHalf_support P ℓ h idx g.session.rootKey msg.senderRatchetKey
          sc.ratchetKey.privateKey (Dh.dh coins T) st (rhRes, s1) hrh
        rcases rhRes with _ | ⟨idx1, rkM, ckR⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact h1
        · rw [stateT_run_lift_bind] at hr
          simp only [mem_support_bind_iff] at hr
          obtain ⟨shRes, -, hr⟩ := hr
          rcases shRes with _ | ⟨idx2, rk2, ckS, pend⟩
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact h1
          · dsimp only at hr
            rcases htry : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
                msg .whisper rc _ with ⟨_ | m, s_out⟩ <;>
            · rw [htry] at hr
              simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
              subst hr; exact h1

theorem hop2Recv_support (h : Hop2Hyb Pt) (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt) :
    ∀ r ∈ support ((hop2Recv (ℓ := ℓ) P Dh encT decT h g c rc).run st),
      r.2.1 = st.1 ∧ r.2.2.lazy.length ≤ st.2.lazy.length + 1 ∧ r.2.2.made = st.2.made := by
  intro r hr
  unfold hop2Recv at hr
  rcases htry : SignalMessage.tryFrom P.codec c with _ | msg
  · rw [htry] at hr
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact ⟨rfl, Nat.le_succ _, rfl⟩
  · rw [htry] at hr
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
    rcases hidx : st.2.idx g.party with _ | t
    · rw [hidx] at hr
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact ⟨rfl, Nat.le_succ _, rfl⟩
    · rw [hidx] at hr
      dsimp only at hr
      split_ifs at hr
      · exact hop2DH_support P ℓ Dh encT decT h (some t) (st.2.coins g.party) g msg rc st r hr
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact ⟨rfl, Nat.le_succ _, rfl⟩

omit [DecidableEq Pt] [Zero Pt] in
theorem hop2Commit_lengths (aux : Hop2Aux Pt) (Q : Party) (uOpt : Option (Hop2Upd Pt)) :
    (hop2Commit aux Q uOpt).lazy = aux.lazy ∧
      (hop2Commit aux Q uOpt).made.length ≤ aux.made.length + 1 := by
  rcases uOpt with _ | ⟨idx', coins', _ | e⟩ <;> simp [hop2Commit]

theorem hop2Deliver_inv (K : ℕ) (h : Hop2Hyb Pt)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt)
    (Q : Party) (c : Bytes) (qAdv m : ℕ)
    (hv : Hop2BudgetInv (Pt := Pt) (ℓ := ℓ) qAdv K (m + 1) st) :
    ∀ r ∈ support ((hop2Deliver (ℓ := ℓ) P Dh encT decT s h (Q, c)).run st),
      Hop2BudgetInv (Pt := Pt) (ℓ := ℓ) qAdv K m r.2 := by
  intro r hr
  unfold hop2Deliver at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  split_ifs at hr with hwin
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hv.mono (Nat.le_succ m)
  · rcases htr : st.1.inTransit Q.other c with _ | rec_
    · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hv.mono (Nat.le_succ m)
    · simp only [htr] at hr
      rw [stateT_run_lift_bind] at hr
      simp only [StateT.run_bind, mem_support_bind_iff] at hr
      obtain ⟨rc, -, ⟨out, st2⟩, hrec, hr⟩ := hr
      obtain ⟨hst2_1, hlazy2, hmade2⟩ :=
        hop2Recv_support P ℓ Dh encT decT h (st.1.st Q) c rc st (out, st2) hrec
      dsimp only at hst2_1 hlazy2 hmade2
      have hmade2_len : st2.2.made.length = st.2.made.length := by rw [hmade2]
      have hl_inv := hv.lazy_le
      have hm_inv := hv.made_le
      rcases out with _ | ⟨⟨st', t', i', m'⟩, uOpt⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr
        refine ⟨?_, by dsimp only; omega, by dsimp only; omega⟩
        dsimp only; rw [hst2_1]; exact hv.sm.mono (Nat.le_succ m)
      · simp only [StateT.run_get, StateT.run_bind, StateT.run_set, StateT.run_pure,
          pure_bind, support_pure, Set.mem_singleton_iff] at hr
        subst hr
        obtain ⟨hc_lazy, hc_made⟩ := hop2Commit_lengths st2.2 Q uOpt
        refine ⟨?_, ?_, ?_⟩
        · dsimp only; rw [hst2_1]; exact hv.sm.accept
        · dsimp only; rw [hc_lazy]; omega
        · dsimp only; omega

theorem hop2Inject_inv (K qep : ℕ) (h : Hop2Hyb Pt)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt)
    (Q : Party) (c : Bytes) (qAdv m : ℕ)
    (hv : Hop2BudgetInv (Pt := Pt) (ℓ := ℓ) qAdv K (m + 1) st) :
    ∀ r ∈ support ((hop2Inject (ℓ := ℓ) P Dh encT decT qep s h (Q, c)).run st),
      Hop2BudgetInv (Pt := Pt) (ℓ := ℓ) qAdv K m r.2 := by
  intro r hr
  unfold hop2Inject at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  by_cases href : (st.1.win || (st.1.inTransit Q.other c).isSome || !st.1.safeInj 3 ||
      !ratchetKeyAdmissible protoSignalCodec decT encT c)
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hv.mono (Nat.le_succ m)
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hr
    rw [stateT_run_lift_bind] at hr
    simp only [StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨rc, -, ⟨out, st2⟩, hrec, hr⟩ := hr
    obtain ⟨hst2_1, hlazy2, hmade2⟩ :=
      hop2Recv_support P ℓ Dh encT decT h (st.1.st Q) c rc st (out, st2) hrec
    dsimp only at hst2_1 hlazy2 hmade2
    have hmade2_len : st2.2.made.length = st.2.made.length := by rw [hmade2]
    have hl_inv := hv.lazy_le
    have hm_inv := hv.made_le
    rcases out with _ | ⟨⟨st', t', i', m'⟩, uOpt⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      refine ⟨?_, by dsimp only; omega, by dsimp only; omega⟩
      dsimp only; rw [hst2_1]; exact hv.sm.mono (Nat.le_succ m)
    · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
      split_ifs at hr with hqep htriv
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hr
        subst hr
        refine ⟨?_, by dsimp only; omega, by dsimp only; omega⟩
        dsimp only; rw [hst2_1]; exact hv.sm.mono (Nat.le_succ m)
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hr
        subst hr
        obtain ⟨hc_lazy, hc_made⟩ :=
          hop2Commit_lengths { st2.2 with bad := st2.2.bad || hop2BadAt P s (st.1.st Q) c } Q uOpt
        refine ⟨?_, ?_, ?_⟩
        · dsimp only; rw [hst2_1]; exact hv.sm.accept
        · dsimp only at hc_lazy ⊢; rw [hc_lazy]; omega
        · dsimp only at hc_made ⊢; omega
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hr
        subst hr
        refine ⟨?_, by dsimp only; omega, by dsimp only; omega⟩
        dsimp only; rw [hst2_1]; exact hv.sm.setWin

end Hop2BudgetInv

/-! ## Evaluation agreement -/

section Hop2Eval

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type} [SampleableType PQC]
  (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (s : BitVec 256) (K B qep : ℕ)

local notation "S" => spkLeakSessionSig Pt ℓ PQC
local notation "OSM" => spkLeakSessionSmOps P ℓ decT encT
local notation "OO" => spkLeakSessionOps P ℓ Dh encPt encT decT s
local notation "II" => e2ePrfIface Pt ℓ PQC
local notation "GS" => @gsTy Pt (GhostState Bytes) Unit (CBC.Plain ℓ) PQC (BitVec 256) Bytes
local notation "RR" => @smRrTy Pt (GhostState Bytes) Unit (CBC.Plain ℓ) PQC (BitVec 256) Bytes

omit [Zero Pt] in
theorem foldr_lookup_eq (t : ℕ) (Q : Pt) (es : List ((ℕ × Pt) × BitVec 256)) :
    es.foldr (fun x acc => if (decide (t = x.1.1) && (Q == x.1.2)) then some x.2 else acc) none =
      es.lookup (t, Q) := by
  induction es with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨⟨t', Q'⟩, u⟩
    have hcond : (decide (t = t') && (Q == Q')) = ((t, Q) == (t', Q')) := by
      change (decide (t = t') && (Q == Q')) = ((t == t') && (Q == Q'))
      by_cases ht : t = t' <;> simp [ht]
    simp only [List.foldr_cons, List.lookup, hcond]
    cases ((t, Q) == (t', Q'))
    · exact ih
    · rfl

omit [SampleableType PQC] in
theorem hop2LookupE_eval {Γ : List (Ty S)} (L : ℕ)
    (lE : Expr OO Γ (.list hop2EntryTy))
    (tE : Expr OO Γ .nat) (qE : Expr OO Γ (.base .key)) (ρ : Env Γ)
    (es : List ((ℕ × Pt) × BitVec 256)) (t : ℕ) (Q : Pt)
    (hlen : es.length ≤ L) (hl : lE.eval ρ = es) (ht : tE.eval ρ = t) (hq : qE.eval ρ = Q) :
    (hop2LookupE P ℓ Dh encPt encT decT s L lE tE qE).eval ρ = es.lookup (t, Q) := by
  have htake : es.take L = es := List.take_of_length_le hlen
  dsimp only [hop2LookupE, opEqPt, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
    Env.get_cons_zero, Env.get_cons_succ]
  rw [hl, ht, hq, htake]
  exact foldr_lookup_eq t Q es

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
@[simp] theorem hop2AuxDec_auxSetBad_eval {O' : Ops S} {Γ : List (Ty S)}
    (auxE : Expr O' Γ hop2AuxTy) (badE : Expr O' Γ .bool) (ρ : Env Γ) :
    hop2AuxDec (PQC := PQC) (ℓ := ℓ) ((auxSetBad auxE badE).eval ρ) =
      { hop2AuxDec (PQC := PQC) (ℓ := ℓ) (auxE.eval ρ) with bad := badE.eval ρ } := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem hop2AuxDec_auxSetBad {O' : Ops S} {Γ : List (Ty S)}
    (auxE : Expr O' Γ hop2AuxTy) (badE : Expr O' Γ .bool) (ρ : Env Γ)
    (aux : Hop2Aux Pt) (b : Bool)
    (haux : auxE.eval ρ = hop2AuxEnc (PQC := PQC) (ℓ := ℓ) aux) (hb : badE.eval ρ = b) :
    hop2AuxDec (PQC := PQC) (ℓ := ℓ) ((auxSetBad auxE badE).eval ρ) = { aux with bad := b } := by
  simp [haux, hb]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
@[simp] theorem hop2AuxDec_auxConsLazy_eval {O' : Ops S} {Γ : List (Ty S)}
    (auxE : Expr O' Γ hop2AuxTy) (eE : Expr O' Γ hop2EntryTy) (ρ : Env Γ) :
    hop2AuxDec (PQC := PQC) (ℓ := ℓ) ((auxConsLazy auxE eE).eval ρ) =
      { hop2AuxDec (PQC := PQC) (ℓ := ℓ) (auxE.eval ρ) with
        lazy := eE.eval ρ :: (hop2AuxDec (PQC := PQC) (ℓ := ℓ) (auxE.eval ρ)).lazy } := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
@[simp] theorem hop2CommitE_eval {O' : Ops S} {Γ : List (Ty S)}
    (auxE : Expr O' Γ hop2AuxTy) (qE : Expr O' Γ .bool)
    (updOptE : Expr O' Γ (.opt hop2UpdTy)) (ρ : Env Γ)
    (aux : Hop2Aux Pt) (Q : Party)
    (uOpt : Option (hop2UpdTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ)).denote)
    (haux : auxE.eval ρ = hop2AuxEnc (PQC := PQC) (ℓ := ℓ) aux)
    (hq : qE.eval ρ = partyEnc Q) (hu : updOptE.eval ρ = uOpt) :
    (hop2CommitE auxE qE updOptE).eval ρ =
      hop2AuxEnc (PQC := PQC) (ℓ := ℓ)
        (hop2Commit aux Q (uOpt.map (hop2UpdDec (PQC := PQC) (ℓ := ℓ)))) := by
  simp only [hop2CommitE, Expr.eval, haux, hq, hu]
  rcases uOpt with _ | ⟨idx', coins', _ | e⟩ <;> cases Q <;> rfl

theorem hop2LazyC_eval {Γ : List (Ty S)}
    (auxE : Expr OO Γ hop2AuxTy) (tE : Expr OO Γ .nat) (qE : Expr OO Γ (.base .key)) (ρ : Env Γ)
    (gs : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) (aux : Hop2Aux Pt)
    (t : ℕ) (Q : Pt)
    (hlazy : aux.lazy.length ≤ K)
    (haux : auxE.eval ρ = hop2AuxEnc (PQC := PQC) (ℓ := ℓ) aux)
    (ht : tE.eval ρ = t) (hq : qE.eval ρ = Q) :
    Prod.map id (fun aux' => (gs, hop2AuxDec (PQC := PQC) (ℓ := ℓ) aux')) <$>
      (hop2LazyC P ℓ Dh encPt encT decT s K (spkDrawBv P ℓ Dh encPt encT decT s)
        auxE tE qE).eval ρ =
      (hop2Lazy (Pt := Pt) (ℓ := ℓ) t Q).run (gs, aux) := by
  unfold hop2LazyC hop2Lazy
  rw [eval_bind_ret]
  have h0 : (Expr.pair auxE (.pair tE qE)).eval ρ =
      (hop2AuxEnc (PQC := PQC) (ℓ := ℓ) aux, t, Q) := by
    simp [Expr.eval, haux, ht, hq]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := (.prod hop2AuxTy (.prod .nat (.base .key)) : Ty S))
    (hop2AuxEnc (PQC := PQC) (ℓ := ℓ) aux, t, Q) ρ
  rw [eval_caseOpt]
  have hlk := hop2LookupE_eval P ℓ Dh encPt encT decT s K (auxLazy (.fst .v0))
    (.fst (.snd .v0)) (.snd (.snd .v0)) ρ₁ aux.lazy t Q hlazy rfl rfl rfl
  rw [hlk]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases aux.lazy.lookup (t, Q) with _ | u
  · simp only [eval_bind, spkDrawBv_eval, hop2Unif, stateT_run_lift_bind, map_bind]
    refine bind_congr fun u' => ?_
    simp [ρ₁, Comp.eval, StateT.run_set, Prod.map, Expr.eval, Expr.v0, Expr.v1]
  · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]

theorem hop2SendHalfC_eval (h : Hop2Hyb Pt)
    (stepC : ∀ {Γ}, Expr OO Γ (.base .rcoins) → Expr OO Γ (.base .key) →
      Comp OO II Γ (.base .rcoins))
    (hStep : ∀ {Γ} (c1E : Expr OO Γ (.base .rcoins)) (qE : Expr OO Γ (.base .key)) (ρ' : Env Γ),
      c1E.eval ρ' = h.chall.1 → (stepC c1E qE).eval ρ' = h.step (qE.eval ρ'))
    {Γ : List (Ty S)}
    (challE : Expr OO Γ hop2ChallTy) (idx1E : Expr OO Γ (.opt .nat))
    (rkME : Expr OO Γ (.base .rcoins)) (cE : Expr OO Γ (.base .ct))
    (rcE : Expr OO Γ (.base .rcoins)) (q'E : Expr OO Γ (.base .key)) (ρ : Env Γ)
    (idx1 : Option ℕ) (rkM : Ratchet.RootKey) (c : Bytes) (msg : SignalMessage)
    (rc : BitVec 256) (Q' : Pt)
    (htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (hchall : challE.eval ρ = h.chall) (hidx1 : idx1E.eval ρ = idx1)
    (hrkM : rkME.eval ρ = rkM) (hc : cE.eval ρ = c)
    (hrc : rcE.eval ρ = rc) (hq' : q'E.eval ρ = Q') :
    (hop2SendHalfC P ℓ Dh encPt encT decT s h.k (spkDrawBv P ℓ Dh encPt encT decT s) stepC
        challE idx1E rkME cE rcE q'E).eval ρ =
      hop2SendHalf P h idx1 rkM msg.senderRatchetKey
        (KeyPair.generate P.C rc).privateKey Q' := by
  unfold hop2SendHalfC hop2SendHalf
  rw [eval_bind_ret]
  have h0 : (Expr.pair challE (.pair idx1E (.pair rkME (.pair cE (.pair rcE q'E))))).eval ρ =
      (h.chall, idx1, rkM, c, rc, Q') := by
    simp [Expr.eval, hchall, hidx1, hrkM, hc, hrc, hq']
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := (.prod hop2ChallTy (.prod (.opt .nat) (.prod (.base .rcoins)
      (.prod (.base .ct) (.prod (.base .rcoins) (.base .key))))) : Ty S))
    (h.chall, idx1, rkM, c, rc, Q') ρ
  rw [eval_caseOpt]
  have hidx1_0 : (Expr.fst (.snd (Expr.v0 (O := OO)))).eval ρ₁ = idx1 := rfl
  rw [hidx1_0]
  rcases idx1 with _ | j
  · dsimp only
    rw [eval_caseOpt]
    have hshr : (opSendHalfReal P ℓ Dh encPt encT decT s
        (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
        (.fst (.snd (.snd (.snd (.snd .v0)))))).eval ρ₁ =
        sendHalfReal P rkM c rc := by
      simp [ρ₁, Expr.eval, Expr.v0]
    rw [hshr]
    unfold sendHalfReal
    rw [htry]
    dsimp only
    rcases rootCreateChain P.C rkM msg.senderRatchetKey
        (KeyPair.generate P.C rc).privateKey with _ | ⟨rk', ck⟩
    · rfl
    · rfl
  · dsimp only
    set ρ₂ := Env.cons (t := .nat) j ρ₁
    rw [eval_ite]
    have hZero : (opIsZeroPt P ℓ Dh encPt encT decT s
        (.snd (.snd (.snd (.snd (.snd (Expr.v1 (O := OO)))))))).eval ρ₂ = decide (Q' = 0) := rfl
    rw [hZero]
    by_cases hQ'0 : Q' = 0
    · simp [hQ'0, Comp.eval, Expr.eval]
    · simp only [hQ'0, decide_false, Bool.false_eq_true, ↓reduceIte, eval_ite]
      have hlt : (Expr.lt (Expr.v0 (O := OO)) (.nat h.k)).eval ρ₂ = decide (j < h.k) := rfl
      rw [hlt]
      by_cases hjk : j < h.k
      · simp only [hjk, decide_true, ↓reduceIte, eval_bind, spkDrawBv_eval, hop2Unif]
        refine bind_congr fun ck => ?_
        simp [ρ₂, ρ₁, Comp.eval, opZeroBv, spkLeakSessionOps, Ops.sum, spkLeakOps,
          Expr.eval, Expr.v0, Expr.v1, Expr.v2]
        rfl
      · simp only [hjk, decide_false, Bool.false_eq_true, ↓reduceIte]
        have heq : (Expr.eqN (Expr.v0 (O := OO)) (.nat h.k)).eval ρ₂ = decide (j = h.k) := rfl
        rw [heq]
        by_cases hjeq : j = h.k
        · simp [ρ₂, ρ₁, hjeq, Comp.eval, opZeroBv, spkLeakSessionOps, Ops.sum, spkLeakOps,
            Expr.eval, Expr.v0, Expr.v1]
          rfl
        · simp only [hjeq, decide_false, Bool.false_eq_true, ↓reduceIte, eval_bind]
          have hst := hStep (.fst (.fst .v1)) (.snd (.snd (.snd (.snd (.snd .v1))))) ρ₂ rfl
          have hq'2 : (Expr.snd (.snd (.snd (.snd (.snd (Expr.v1 (O := OO))))))).eval ρ₂ = Q' :=
            rfl
          rw [hq'2] at hst
          rw [hst]
          refine bind_congr fun u => ?_
          simp [Comp.eval, opRootExpand, expandPRG, spkLeakSessionOps, Ops.sum, spkLeakOps,
            Expr.eval, Expr.v0]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem eval_caseOpt_fst_v0_none {O' : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ : List (Ty S)} {t u v : Ty S} (y : u.denote)
    (noneB : Comp O' I ((Ty.prod (.opt t) u) :: Γ) v)
    (someB : Comp O' I (t :: (Ty.prod (.opt t) u) :: Γ) v) (ρ : Env Γ) :
    (Comp.caseOpt (.fst .v0) noneB someB).eval (.cons (none, y) ρ) =
      noneB.eval (.cons (none, y) ρ) := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem eval_caseOpt_fst_v0_some {O' : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ : List (Ty S)} {t u v : Ty S} (a : t.denote) (y : u.denote)
    (noneB : Comp O' I ((Ty.prod (.opt t) u) :: Γ) v)
    (someB : Comp O' I (t :: (Ty.prod (.opt t) u) :: Γ) v) (ρ : Env Γ) :
    (Comp.caseOpt (.fst .v0) noneB someB).eval (.cons (some a, y) ρ) =
      someB.eval (.cons a (.cons (some a, y) ρ)) := rfl

theorem hop2DeliverC_chall (k : ℕ)
    (stepC : ∀ {Γ}, Expr OO Γ (.base .rcoins) → Expr OO Γ (.base .key) →
      Comp OO II Γ (.base .rcoins))
    {Γ : List (Ty S)}
    (stE : Expr OO Γ hop2StTy) (argE : Expr OO Γ (.prod .bool (.base .ct))) (ρ : Env Γ) :
    ∀ r ∈ support ((hop2DeliverC P ℓ Dh encPt encT decT s K B k
        (spkDrawBv P ℓ Dh encPt encT decT s) stepC stE argE).eval ρ),
      r.2.2.2 = (stE.eval ρ).2.2 := by
  intro r hr
  unfold hop2DeliverC at hr
  rw [eval_bind_ret] at hr
  rw [eval_ite] at hr
  split_ifs at hr
  · simp only [Comp.eval, support_pure, Set.mem_singleton_iff] at hr
    subst hr; rfl
  · rw [eval_caseOpt] at hr
    rcases htr : ((inTransitE K (.fst (.fst .v0)) (otherE (.fst (.snd .v0))) (.snd (.snd .v0)) :
        Expr OSM _ (.opt recTy)).liftL).eval _ with _ | rec_
    · rw [htr] at hr
      simp only [Comp.eval, support_pure, Set.mem_singleton_iff] at hr
      subst hr; rfl
    · rw [htr] at hr
      simp only [eval_bind, mem_support_bind_iff] at hr
      obtain ⟨rc, -, ⟨outRaw, aux2⟩, -, hr⟩ := hr
      rcases outRaw with _ | ⟨⟨st', t', i', m'⟩, uOpt⟩
      · rw [eval_caseOpt_fst_v0_none] at hr
        simp only [Comp.eval, support_pure, Set.mem_singleton_iff] at hr
        subst hr; rfl
      · rw [eval_caseOpt_fst_v0_some] at hr
        simp only [Comp.eval, support_pure, Set.mem_singleton_iff] at hr
        subst hr; rfl

theorem hop2InjectC_chall (k : ℕ)
    (stepC : ∀ {Γ}, Expr OO Γ (.base .rcoins) → Expr OO Γ (.base .key) →
      Comp OO II Γ (.base .rcoins))
    {Γ : List (Ty S)}
    (stE : Expr OO Γ (hop2StTy (PQC := PQC)))
    (argE : Expr OO Γ (.prod .bool (.base .ct))) (ρ : Env Γ) :
    ∀ r ∈ support ((hop2InjectC P ℓ Dh encPt encT decT s K B qep k
        (spkDrawBv P ℓ Dh encPt encT decT s) stepC stE argE).eval ρ),
      r.2.2.2 = (stE.eval ρ).2.2 := by
  intro r hr
  unfold hop2InjectC at hr
  rw [eval_bind_ret] at hr
  rw [eval_ite] at hr
  split_ifs at hr
  · simp only [Comp.eval, support_pure, Set.mem_singleton_iff] at hr
    subst hr; rfl
  · simp only [eval_bind, mem_support_bind_iff] at hr
    obtain ⟨rc, -, ⟨outRaw, aux2⟩, -, hr⟩ := hr
    rcases outRaw with _ | ⟨⟨st', t', i', m'⟩, uOpt⟩
    · rw [eval_caseOpt_fst_v0_none] at hr
      simp only [Comp.eval, support_pure, Set.mem_singleton_iff] at hr
      subst hr; rfl
    · rw [eval_caseOpt_fst_v0_some] at hr
      rw [eval_ite] at hr
      split_ifs at hr
      · simp only [Comp.eval, support_pure, Set.mem_singleton_iff] at hr
        subst hr; rfl
      · rw [eval_ite] at hr
        split_ifs at hr <;>
        · simp only [Comp.eval, support_pure, Set.mem_singleton_iff] at hr
          subst hr; rfl

theorem hop2InitAfterChallC_eval (k : ℕ) {Γ : List (Ty S)}
    (challE : Expr OO Γ (hop2ChallTy (PQC := PQC))) (ρ : Env Γ)
    (chall : Ratchet.RootKey × BitVec 256)
    (hchall : challE.eval ρ = chall) :
    (Prod.map id (hop2StDec (PQC := PQC)) <$>
      (hop2InitAfterChallC P ℓ Dh encPt encT decT s k
        (spkDrawBool P ℓ Dh encPt encT decT s) (spkDrawBv P ℓ Dh encPt encT decT s)
        challE).eval ρ) =
      (do
        let b ← (liftM ($ᵗ Bool : ProbComp Bool) : Hop2Comp Pt Bool)
        let ck0 ← hop2Unif (Pt := Pt)
        let x ← hop2Unif (Pt := Pt)
        let alice ← hop2Unif (Pt := Pt)
        let pqr ← hop2Unif (Pt := Pt)
        let u1 ← hop2Unif (Pt := Pt)
        let ck1 := if k = 0 then chall.2 else u1
        let I0 := Dh.dh x (Dh.dh alice Dh.base)
        let spk := (KeyPair.generate P.C x).publicKey
        let sessA := ((SessionState.new currentVersion P.idA P.idB 0
          (P.spqr.init .a2b pqr)).addReceiverChain spk ⟨ck0, 0⟩).setSenderChain
          (KeyPair.generate P.C alice) ⟨ck1, 0⟩
        let stA : GhostState Bytes := ⟨.A, sessA.setUnacknowledgedPreKeyMessage, 0, [0]⟩
        let stB := P.initB ⟨0, ck0, x, alice, pqr⟩
        let initSt : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes :=
          { st := fun Q => match Q with | .A => stA | .B => stB, b := b }
        let aux0 : Hop2Aux Pt :=
          { made := [((0, I0), ck1)]
            idx := fun Q => match Q with | .A => some 1 | .B => some 0
            coins := fun Q => match Q with | .A => alice | .B => x }
        return ((), (initSt, aux0))) ∧
    ∀ r ∈ support ((hop2InitAfterChallC P ℓ Dh encPt encT decT s k
        (spkDrawBool P ℓ Dh encPt encT decT s) (spkDrawBv P ℓ Dh encPt encT decT s)
        challE).eval ρ),
      r.2.2.2 = chall := by
  refine ⟨?_, ?_⟩
  · unfold hop2InitAfterChallC
    rw [eval_bind_ret, hchall]
    simp only [eval_bind, spkDrawBool_eval, spkDrawBv_eval, hop2Unif, map_bind]
    refine bind_congr fun b => bind_congr fun ck0 => bind_congr fun x =>
      bind_congr fun alice => bind_congr fun pqr => bind_congr fun u1 => ?_
    simp only [eval_ret, map_pure, Prod.map, id_eq, hop2StDec, gsDec, hop2AuxDec, gsMk, auxMk,
      Expr.eval, opInitA_eval, opInitB_eval]
    simp only [opZeroBv_eval, opBasePt_eval, opDh_eval, e2eInitA, e2eInitB,
      Expr.eval,
      Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6,
      Env.get_cons_zero, Env.get_cons_succ]
    by_cases hk : k = 0 <;>
      simp only [hk, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
    all_goals
      congr 1; congr 1
      refine Prod.ext ?_ rfl
      simp only [SM.GameState.mk.injEq, List.map_nil, true_and, and_true]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> (funext Q; cases Q <;> rfl)
  · intro r hr
    unfold hop2InitAfterChallC at hr
    rw [eval_bind_ret, hchall] at hr
    simp only [eval_bind, eval_ret, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hr
    rcases hr with ⟨b, -, ck0, -, x, -, alice, -, pqr, -, u1, -, rfl⟩
    rfl

theorem map_bind_pure_fst {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β γ δ : Type} (f : α → β) (g : γ → δ) (x : m (α × γ)) :
    Prod.map id g <$> (x >>= fun p => pure (f p.1, p.2)) = Prod.map f g <$> x := by
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, Prod.map, id_eq]

set_option maxHeartbeats 800000 in

theorem hop2PrfRedKProg_eq (k : ℕ) :
    hop2PrfRedKProg P ℓ Dh encPt encT decT s K B qep k =
      hop2GameRedProg P ℓ Dh encPt encT decT s K B qep k
        (spkDrawBool P ℓ Dh encPt encT decT s) (spkDrawCoins ℓ (PQC := PQC))
        (spkDrawBv P ℓ Dh encPt encT decT s)
        (.bind (spkDrawBv P ℓ Dh encPt encT decT s)
          (.bind (spkDrawBv P ℓ Dh encPt encT decT s)
            (.ret (.pair .v1 .v0))))
        (fun _ qE => .query () qE) := rfl

theorem hop2PrgRedKProg_toPrf (k : ℕ) :
    (hop2PrgRedKProg P ℓ Dh encPt encT decT s K B qep k).toPrf =
      hop2GameRedProg P ℓ Dh encPt encT decT s K B qep k
        (spkDrawBool P ℓ Dh encPt encT decT s) (spkDrawCoins ℓ (PQC := PQC))
        (spkDrawBv P ℓ Dh encPt encT decT s) (.ret .v0)
        (fun c1E qE => .ret (opExtractTag P ℓ Dh encPt encT decT s c1E qE)) := rfl

/-! ## Cost and query bounds -/

theorem hop2PrgRedKProg_init_cost (k : ℕ) :
    (hop2PrgRedKProg P ℓ Dh encPt encT decT s K B qep k).init.cost = 2 * bits k + 128 := by
  simp [hop2PrgRedKProg, hop2GameRedProg, hop2InitAfterChallC, gsMk, auxMk,
    prgDrawBool, prgDrawBv, e2ePrgIface, Iface.withSamp, prgIface, Samplers.sum, unifSamplers,
    Comp.cost, Expr.cost, dsl_cost]
  omega

theorem hop2PrfRedKProg_init_cost (k : ℕ) :
    (hop2PrfRedKProg P ℓ Dh encPt encT decT s K B qep k).init.cost = 2 * bits k + 136 := by
  simp [hop2PrfRedKProg, hop2GameRedProg, hop2InitAfterChallC, gsMk, auxMk,
    spkDrawBool, spkDrawBv, e2ePrfIface, Iface.withSamp, prfIface, Samplers.sum, unifSamplers,
    Comp.cost, Expr.cost, dsl_cost]
  omega

theorem hop2PrgRedKProg_finish_cost (k : ℕ) :
    (hop2PrgRedKProg P ℓ Dh encPt encT decT s K B qep k).finish.cost = 8 := by
  simp [hop2PrgRedKProg, hop2GameRedProg, auxBad, Comp.cost, Expr.cost, Expr.v0]

theorem hop2PrfRedKProg_finish_cost (k : ℕ) :
    (hop2PrfRedKProg P ℓ Dh encPt encT decT s K B qep k).finish.cost = 8 := by
  simp [hop2PrfRedKProg, hop2GameRedProg, auxBad, Comp.cost, Expr.cost, Expr.v0]

theorem hop2PrgRedKProg_totalCost (k q : ℕ) :
    (hop2PrgRedKProg P ℓ Dh encPt encT decT s K B qep k).totalCost q =
      2 * bits k + 136 +
        q * ((hop2PrgRedKProg P ℓ Dh encPt encT decT s K B qep k).handle.cost + 6) := by
  simp only [CostedReduction.totalCost, hop2PrgRedKProg_init_cost, hop2PrgRedKProg_finish_cost]
  simp only [hop2PrgRedKProg, hop2GameRedProg, e2ePrgIface, Iface.withSamp, prgIface,
    e2eCodec, smCodec]
  rw [max_eq_right (by simp [hop2ImplC, Comp.cost])]
  omega

theorem hop2PrfRedKProg_totalCost (k q : ℕ) :
    (hop2PrfRedKProg P ℓ Dh encPt encT decT s K B qep k).totalCost q =
      2 * bits k + 144 +
        q * ((hop2PrfRedKProg P ℓ Dh encPt encT decT s K B qep k).handle.cost + 6) := by
  simp only [CostedReduction.totalCost, hop2PrfRedKProg_init_cost, hop2PrfRedKProg_finish_cost]
  simp only [hop2PrfRedKProg, hop2GameRedProg, e2ePrfIface, Iface.withSamp, prfIface,
    e2eCodec, smCodec]
  rw [max_eq_right (by simp [hop2ImplC, Comp.cost])]
  omega

theorem hop2PrgRedKProg_queries (k q : ℕ) :
    (hop2PrgRedKProg P ℓ Dh encPt encT decT s K B qep k).totalQueries
      Empty.elim (fun _ => 0) q = 0 := by
  simp [CostedReduction.totalQueries]

theorem hop2PrfRedKProg_queries (k q : ℕ) :
    (hop2PrfRedKProg P ℓ Dh encPt encT decT s K B qep k).totalQueries
      (fun _ => 1) (fun _ => 0) q ≤ q := by
  simp [CostedReduction.totalQueries, hop2PrfRedKProg, hop2GameRedProg, hop2InitAfterChallC,
    hop2ImplC, hop2DeliverC, hop2InjectC, hop2RecvC, hop2DHC, hop2FinishNoneC, hop2SendHalfC,
    hop2LazyC, spkDrawBool, spkDrawBv, spkDrawCoins, Comp.queries, Comp.queries_liftL]

end Hop2Eval

/-! ## `spkHopBudget` bounds and `GRedBounded` combinators -/

section SpkHopBudgets

theorem spkHopBudget_eq_min (q qep ℓ : ℕ) :
    spkHopBudget q qep ℓ = min (spkTier1Budget q qep) (spkTier2Budget q qep ℓ) := rfl

theorem spkHopBudget_le_tier1 (q qep ℓ : ℕ) :
    spkHopBudget q qep ℓ ≤ spkTier1Budget q qep :=
  Nat.min_le_left _ _

theorem spkHopBudget_le_tier2 (q qep ℓ : ℕ) :
    spkHopBudget q qep ℓ ≤ spkTier2Budget q qep ℓ :=
  Nat.min_le_right _ _

theorem spkTier1Budget_le_ratchetCostBudget (q qep : ℕ) :
    spkTier1Budget q qep ≤ ratchetCostBudget q qep := by
  unfold spkTier1Budget ratchetCostBudget maxForwardJumps
  set b := bits qep
  have hlhs : 2 ^ 10 * (q + 1) ^ 2 + 2 ^ 9 * 25000 * (q + 1) + 2 ^ 8 * (q + 1) * b =
      12801024 + 12802048 * q + 1024 * (q * q) + 256 * b + 256 * (q * b) := by ring
  have hrhs : 2 ^ 12 * (q + 1) ^ 2 * (25000 + b) =
      102400000 + 204800000 * q + 102400000 * (q * q) +
        4096 * b + 8192 * (q * b) + 4096 * (q * q * b) := by ring
  rw [hlhs, hrhs]
  omega

theorem spkHopBudget_le_ratchetCostBudget (q qep ℓ : ℕ) :
    spkHopBudget q qep ℓ ≤ ratchetCostBudget q qep :=
  Nat.le_trans (spkHopBudget_le_tier1 q qep ℓ) (spkTier1Budget_le_ratchetCostBudget q qep)

theorem spkLeakRedUBudget_le_tier1 (q qep : ℕ) :
    spkLeakRedUBudget q ≤ spkTier1Budget q qep := by
  unfold spkLeakRedUBudget spkTier1Budget maxForwardJumps
  have hq : 0 ≤ (q + 1) ^ 2 := Nat.zero_le _
  nlinarith

theorem spkLeakRedUBudget_le_ratchetCostBudget (q qep : ℕ) :
    spkLeakRedUBudget q ≤ ratchetCostBudget q qep :=
  Nat.le_trans (spkLeakRedUBudget_le_tier1 q qep) (spkTier1Budget_le_ratchetCostBudget q qep)

theorem spkHopBudget_lower_bound (q qep ℓ : ℕ) :
    12800000 * (q + 1) ≤ spkHopBudget q qep ℓ := by
  unfold spkHopBudget
  refine le_min ?_ ?_
  · unfold spkTier1Budget maxForwardJumps
    have hq : 0 ≤ (q + 1) ^ 2 := Nat.zero_le _
    nlinarith
  · unfold spkTier2Budget maxForwardJumps
    have h1 : 12800000 ≤
        64 * (ℓ + 512) + 64 * bits (q + 1) + 64 * bits qep + 2 ^ 9 * 25000 := by omega
    calc 12800000 * (q + 1)
      _ = (q + 1) * 12800000 := Nat.mul_comm _ _
      _ ≤ (q + 1) * (64 * (ℓ + 512) + 64 * bits (q + 1) + 64 * bits qep + 2 ^ 9 * 25000) :=
        Nat.mul_le_mul_left (q + 1) h1

theorem spkTier1Budget_mono {q₁ q₂ qep₁ qep₂ : ℕ} (hq : q₁ ≤ q₂) (hqep : qep₁ ≤ qep₂) :
    spkTier1Budget q₁ qep₁ ≤ spkTier1Budget q₂ qep₂ := by
  unfold spkTier1Budget
  have hsq : (q₁ + 1) ^ 2 ≤ (q₂ + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hb : bits qep₁ ≤ bits qep₂ := bits_mono hqep
  have hmul : (q₁ + 1) * bits qep₁ ≤ (q₂ + 1) * bits qep₂ := Nat.mul_le_mul (by omega) hb
  nlinarith

theorem spkTier2Budget_mono {q₁ q₂ qep₁ qep₂ ℓ₁ ℓ₂ : ℕ}
    (hq : q₁ ≤ q₂) (hqep : qep₁ ≤ qep₂) (hℓ : ℓ₁ ≤ ℓ₂) :
    spkTier2Budget q₁ qep₁ ℓ₁ ≤ spkTier2Budget q₂ qep₂ ℓ₂ := by
  unfold spkTier2Budget
  have hb1 : bits (q₁ + 1) ≤ bits (q₂ + 1) := bits_mono (by omega)
  have hb2 : bits qep₁ ≤ bits qep₂ := bits_mono hqep
  exact Nat.mul_le_mul (by omega) (by omega)

theorem spkHopBudget_mono {q₁ q₂ qep₁ qep₂ ℓ₁ ℓ₂ : ℕ}
    (hq : q₁ ≤ q₂) (hqep : qep₁ ≤ qep₂) (hℓ : ℓ₁ ≤ ℓ₂) :
    spkHopBudget q₁ qep₁ ℓ₁ ≤ spkHopBudget q₂ qep₂ ℓ₂ :=
  min_le_min (spkTier1Budget_mono hq hqep) (spkTier2Budget_mono hq hqep hℓ)

theorem gRedBounded_mono_costBudget {S : Sig} {O : Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S T} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    {R : CostedReduction O I G C rIn aIn aOut out}
    {wTag : I.Tag → ℕ} {wSamp : I.smp.Samp → ℕ}
    {q qOut B₁ B₂ : ℕ} (hB : B₁ ≤ B₂)
    (h : GRedBounded R wTag wSamp q qOut B₁) :
    GRedBounded R wTag wSamp q qOut B₂ := by
  rcases h with ⟨hCost, hSize, hQueries, hOps, hSamp, hRun⟩
  have hbits : bits B₁ ≤ bits B₂ := bits_mono hB
  refine ⟨Nat.le_trans hCost hB, by omega, hQueries, hOps, hSamp, ?_⟩
  intro B hA A hb hfit x hx
  have hRunB := hRun B hA A hb hfit x hx
  have hw : 2 * (B₁ + q + 1) * (B + 1) ≤ 2 * (B₂ + q + 1) * (B + 1) := by nlinarith
  refine ⟨fun y hy => ?_, fun r0 hr0 r1 hr1 => ?_⟩
  · exact (costedFits_iff_fits _ out y).2
      (Ty.fits_mono hw out y ((costedFits_iff_fits _ out y).1 (hRunB.1 y hy)))
  · exact (costedFits_iff_fits _ R.σ r1.2).2
      (Ty.fits_mono hw R.σ r1.2 ((costedFits_iff_fits _ R.σ r1.2).1 (hRunB.2 r0 hr0 r1 hr1)))

/-- Selects whichever of `R₁` or `R₂` has the smaller cost budget, preserving `GRedBounded` at `min B₁ B₂`. -/
theorem gRedBounded_select_min {S : Sig} {O : Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S T} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (R₁ R₂ : CostedReduction O I G C rIn aIn aOut out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ)
    (q qOut B₁ B₂ : ℕ)
    (h₁ : GRedBounded R₁ wTag wSamp q qOut B₁)
    (h₂ : GRedBounded R₂ wTag wSamp q qOut B₂) :
    GRedBounded (if B₂ ≤ B₁ then R₂ else R₁) wTag wSamp q qOut (min B₁ B₂) := by
  split_ifs with hle
  · rw [Nat.min_eq_right hle]
    exact h₂
  · rw [Nat.min_eq_left (Nat.le_of_not_ge hle)]
    exact h₁

theorem eval_select_min {S : Sig} {O : Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S T} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (R₁ R₂ : CostedReduction O I G C rIn aIn aOut out)
    (B₁ B₂ : ℕ)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (x : rIn.denote)
    {target : OracleComp T out.denote}
    (h₁ : R₁.eval A x = target) (h₂ : R₂.eval A x = target) :
    (if B₂ ≤ B₁ then R₂ else R₁).eval A x = target := by
  split_ifs
  · exact h₂
  · exact h₁

theorem gRedBounded_select_spkHopBudget {S : Sig} {O : Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S T} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (R₁ R₂ : CostedReduction O I G C rIn aIn aOut out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ)
    (q qOut qep ℓ : ℕ)
    (h₁ : GRedBounded R₁ wTag wSamp q qOut (spkTier1Budget q qep))
    (h₂ : GRedBounded R₂ wTag wSamp q qOut (spkTier2Budget q qep ℓ)) :
    GRedBounded
      (if spkTier2Budget q qep ℓ ≤ spkTier1Budget q qep then R₂ else R₁)
      wTag wSamp q qOut (spkHopBudget q qep ℓ) :=
  gRedBounded_select_min R₁ R₂ wTag wSamp q qOut
    (spkTier1Budget q qep) (spkTier2Budget q qep ℓ) h₁ h₂

theorem gRedBounded_select_min_left {S : Sig} {O : Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S T} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (R₁ R₂ : CostedReduction O I G C rIn aIn aOut out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ)
    (q qOut B₁ B₂ : ℕ)
    (h₁ : GRedBounded R₁ wTag wSamp q qOut B₁)
    (h₂ : GRedBounded R₂ wTag wSamp q qOut B₂) :
    GRedBounded (if B₁ ≤ B₂ then R₁ else R₂) wTag wSamp q qOut (min B₁ B₂) := by
  split_ifs with hle
  · rw [Nat.min_eq_left hle]
    exact h₁
  · rw [Nat.min_eq_right (Nat.le_of_not_ge hle)]
    exact h₂

theorem gRedBounded_select_spkHopBudget_tier1First {S : Sig} {O : Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S T} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (R₁ R₂ : CostedReduction O I G C rIn aIn aOut out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ)
    (q qOut qep ℓ : ℕ)
    (h₁ : GRedBounded R₁ wTag wSamp q qOut (spkTier1Budget q qep))
    (h₂ : GRedBounded R₂ wTag wSamp q qOut (spkTier2Budget q qep ℓ)) :
    GRedBounded
      (if spkTier1Budget q qep ≤ spkTier2Budget q qep ℓ then R₁ else R₂)
      wTag wSamp q qOut (spkHopBudget q qep ℓ) :=
  gRedBounded_select_min_left R₁ R₂ wTag wSamp q qOut
    (spkTier1Budget q qep) (spkTier2Budget q qep ℓ) h₁ h₂

end SpkHopBudgets

end CryptoVerification.E2E.Costed
