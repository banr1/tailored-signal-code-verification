/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeGapDh
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSim
import VCVio.EvalDist.Monad.Basic

/-!
# Shared infrastructure for the `Auth` Gap-DH evaluation equivalence

Defines the state encoding `fgSimToVal`, the generic runner bridge `agRunBridge`, and evaluation
lemmas for the Gap-DH patching helpers.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

set_option allowUnsafeReducibility true in
attribute [implicit_reducible] gapDhDdhOracle

/-! ## Runner bridge -/

/-- If a DSL step agrees with a shallow step through `enc` on `Inv (k + 1)` states and shallow
    successors satisfy `Inv k`, then runs on a `qTotal`-bounded adversary agree. -/
theorem agRunBridge {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI}
    {σD σS α β : Type}
    (stepD : (q : ιI) → σD → OracleComp (PrimBaseSpec + gapDhDdhOracle.spec) (GSpec.Range q × σD))
    (stepS : (q : ιI) → σS → OracleComp GdhSimSpec (GSpec.Range q × σS))
    (enc : σS → σD) (Inv : Nat → σS → Prop)
    (hMono : ∀ k s, Inv (k + 1) s → Inv k s)
    (hStep : ∀ k q s, Inv (k + 1) s →
      stepD q (enc s) = (fun x => (x.1, enc x.2)) <$> stepS q s)
    (hPres : ∀ k q s, Inv (k + 1) s → ∀ x ∈ support (stepS q s), Inv k x.2)
    (f : α × σD → OracleComp GdhSimSpec β) (g : α × σS → OracleComp GdhSimSpec β)
    (hfg : ∀ a s, Inv 0 s → f (a, enc s) = g (a, s))
    (mx : OracleComp (unifSpec + GSpec) α) (qTotal : Nat)
    (hMx : IsQueryBoundP mx (fun q : ℕ ⊕ ιI => q.isRight = true) qTotal)
    (s : σS) (hs : Inv qTotal s) :
    (runWithIfaceStep pqGapDhIface stepD mx (enc s) >>= f) = (runWithGdhStep stepS mx s >>= g) := by
  induction mx using OracleComp.inductionOn generalizing qTotal s with
  | pure a =>
    have h0 : Inv 0 s := by
      clear hMx
      induction qTotal with
      | zero => exact hs
      | succ n ih => exact ih (hMono n s hs)
    change (pure (a, enc s) >>= f) = (pure (a, s) >>= g)
    simp only [pure_bind]
    exact hfg a s h0
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hMx
    rcases q with uq | gq
    · rcases hMx with ⟨_, hCont⟩
      simp only [Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte] at hCont
      change ((pqGapDhIface.fwdU uq >>= fun u =>
          runWithIfaceStep pqGapDhIface stepD (k u) (enc s)) >>= f) =
        ((liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inl (Sum.inl uq))) >>= fun u =>
          runWithGdhStep stepS (k u) s) >>= g)
      simp only [bind_assoc]
      refine congrArg (fun h => _ >>= h) (funext fun u => ?_)
      exact ih u qTotal (hCont u) s hs
    · rcases hMx with ⟨hFirst, hCont⟩
      have hPos : 0 < qTotal := by
        rcases hFirst with hAbs | hPos
        · exact absurd rfl hAbs
        · exact hPos
      simp only [Sum.isRight_inr, ↓reduceIte] at hCont
      obtain ⟨n, rfl⟩ : ∃ n, qTotal = n + 1 := ⟨qTotal - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hCont
      change ((stepD gq (enc s) >>= fun x =>
          runWithIfaceStep pqGapDhIface stepD (k x.1) x.2) >>= f) =
        ((stepS gq s >>= fun p => runWithGdhStep stepS (k p.1) p.2) >>= g)
      rw [hStep n gq s hs]
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp, pure_bind]
      refine bind_congr_of_forall_mem_support _ (fun x hx => ?_)
      exact ih x.1 n (hCont x.1) x.2 (hPres n gq s hs x hx)

/-! ## Monadic list combinators -/

theorem agFindML_eq_findMGdh {α : Type} (p : α → OracleComp GdhSimSpec Bool) (L : List α) :
    findML p L = FgGapDh.findMGdh p L := by
  induction L with
  | nil => rfl
  | cons x xs ih => simp only [findML, FgGapDh.findMGdh, ih]

theorem agFindMGdh_map {α β : Type} (f : α → β) (p : β → OracleComp GdhSimSpec Bool)
    (L : List α) :
    FgGapDh.findMGdh p (L.map f) = Option.map f <$> FgGapDh.findMGdh (fun x => p (f x)) L := by
  induction L with
  | nil => simp only [List.map_nil, FgGapDh.findMGdh, map_pure, Option.map_none]
  | cons x xs ih =>
    simp only [List.map_cons, FgGapDh.findMGdh, ih, map_bind]
    refine congrArg (fun h => p (f x) >>= h) (funext fun b => ?_)
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, map_pure, Option.map_some]

/-! ## State encoding -/

@[simp] def rootEntryToVal (e : FgRootEntry) : rootEntryTy.denote :=
  (e.rk, (fgPosToVal e.dhPos, (e.rk1, e.ck1_0)))

@[simp] def valToRootEntry (x : rootEntryTy.denote) : FgRootEntry :=
  ⟨x.1, valToFgPos x.2.1, x.2.2.1, x.2.2.2⟩

@[simp] def respRecToVal (r : AuthRespRecord) : respRecTy.denote :=
  (r.bKey, (r.ikAPk, r.ekAPk))

@[simp] def fgSimToVal {S : Setup} (st : FgAuthSimState S) : fgSimTy.denote :=
  (authStateToVal st.base, (st.fgL.map fgPatchEntryToVal, (st.fgRootL.map rootEntryToVal,
    (st.rawRoCache.map (Prod.map id drKeyToVal), (st.advRoLog,
      (st.respRecs.map respRecToVal, st.advKeyPows))))))

@[simp] def paVal (U V : Bytes) (useDh1 : Bool) (t s : Nat) : paramsTy.denote :=
  (U, (V, (useDh1, (t, s))))

/-- Decodes `(useDh1, t)` into `(useDh1, targetPrinIdx, sendIsOpk, sendSubIdx)`, using sentinel
    `S.N_id` when `t` is out of range. -/
def paTargetChoice (S : Setup) (useDh1 : Bool) (t : Nat) : Bool × Nat × Bool × Nat :=
  if useDh1 then (true, (t, (false, 0)))
  else if t < S.N_send_opk_tot then (false, (t / S.N_send_opk, (true, t % S.N_send_opk)))
  else if t < S.N_send_tot then
    let r := t - S.N_send_opk_tot
    (false, (r / S.N_send_no_opk, (false, r % S.N_send_no_opk)))
  else (false, (S.N_id, (false, 0)))

def paSpkOpt (S : Setup) (sIdx : Nat) : Option (Nat × Nat) :=
  if sIdx < S.N_spk_tot then some (sIdx / S.N_recv, sIdx % S.N_recv) else none

@[simp] def fg2PaVal (S : Setup) (U V : Bytes) (useDh1 : Bool) (t sIdx : Nat) :
    fg2ParamsTy.denote :=
  let tc := paTargetChoice S useDh1 t
  (U, (V, (tc.1, (tc.2.1, (tc.2.2.1, (tc.2.2.2, paSpkOpt S sIdx))))))

theorem gdh_take_min_of_le {α : Type} (K N : Nat) (L : List α) (hL : L.length ≤ K) :
    L.take (min K N) = L.take N := by
  rw [Nat.min_comm, ← List.take_take, List.take_of_length_le hL]

private theorem div_mod_eq_iff {u j q m : Nat} (hj : j < m) :
    (u = q / m ∧ j = q % m) ↔ u * m + j = q := by
  have hm : 0 < m := Nat.zero_lt_of_lt hj
  constructor
  · rintro ⟨rfl, rfl⟩
    have hd := Nat.div_add_mod q m
    rw [Nat.mul_comm]
    exact hd
  · rintro rfl
    rw [Nat.mul_comm u m, Nat.mul_add_div hm, Nat.mul_add_mod,
      Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj, Nat.add_zero]
    exact ⟨rfl, rfl⟩

private theorem mul_add_lt_mul {u n j m : Nat} (hu : u < n) (hj : j < m) :
    u * m + j < n * m :=
  calc u * m + j < u * m + m := Nat.add_lt_add_left hj (u * m)
    _ = (u + 1) * m := (Nat.succ_mul u m).symm
    _ ≤ n * m := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hu)

theorem paSpkOpt_beq (S : Setup) (sIdx : Nat) (uf : Fin S.N_id) (jf : Fin S.N_recv) :
    (match paSpkOpt S sIdx with
      | none => false
      | some p => ((uf : Nat) == p.1) && ((jf : Nat) == p.2)) =
      ((uf : Nat) * S.N_recv + (jf : Nat) == sIdx) := by
  have hlt : (uf : Nat) * S.N_recv + (jf : Nat) < S.N_spk_tot :=
    mul_add_lt_mul uf.isLt jf.isLt
  by_cases hs : sIdx < S.N_spk_tot
  · simp only [paSpkOpt, hs, ↓reduceIte]
    exact Bool.eq_iff_iff.mpr (by
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact div_mod_eq_iff jf.isLt)
  · have hne : (uf : Nat) * S.N_recv + (jf : Nat) ≠ sIdx := by omega
    simp [paSpkOpt, hs, beq_false_of_ne hne]

theorem paTargetChoice_dh1 (S : Setup) (useDh1 : Bool) (t : Nat) :
    (paTargetChoice S useDh1 t).1 = useDh1 ∧
      (useDh1 = true → (paTargetChoice S useDh1 t).2.1 = t) := by
  cases useDh1 <;> simp [paTargetChoice]
  split <;> [simp; (split <;> simp)]

theorem paTargetChoice_opk_beq (S : Setup) (useDh1 : Bool) (t : Nat)
    (uf : Fin S.N_id) (i : Fin S.N_send_opk) :
    (!(paTargetChoice S useDh1 t).1 && ((paTargetChoice S useDh1 t).2.2.1 &&
      (((uf : Nat) == (paTargetChoice S useDh1 t).2.1) &&
        ((i : Nat) == (paTargetChoice S useDh1 t).2.2.2)))) =
      (!useDh1 && ((uf : Nat) * S.N_send_opk + (i : Nat) == t)) := by
  cases useDh1
  · have hlt : (uf : Nat) * S.N_send_opk + (i : Nat) < S.N_send_opk_tot :=
      mul_add_lt_mul uf.isLt i.isLt
    by_cases ht : t < S.N_send_opk_tot
    · simp only [paTargetChoice, Bool.false_eq_true, ht, ↓reduceIte, Bool.not_false, Bool.true_and]
      exact Bool.eq_iff_iff.mpr (by
        simp only [Bool.and_eq_true, beq_iff_eq]
        exact div_mod_eq_iff i.isLt)
    · have hne : (uf : Nat) * S.N_send_opk + (i : Nat) ≠ t := by omega
      by_cases ht2 : t < S.N_send_tot <;>
        simp [paTargetChoice, ht, ht2, beq_false_of_ne hne]
  · simp [paTargetChoice]

theorem paTargetChoice_noopk_beq (S : Setup) (useDh1 : Bool) (t : Nat)
    (uf : Fin S.N_id) (i : Fin S.N_send_no_opk) :
    (!(paTargetChoice S useDh1 t).1 && (!(paTargetChoice S useDh1 t).2.2.1 &&
      (((uf : Nat) == (paTargetChoice S useDh1 t).2.1) &&
        ((i : Nat) == (paTargetChoice S useDh1 t).2.2.2)))) =
      (!useDh1 && (S.N_send_opk_tot + ((uf : Nat) * S.N_send_no_opk + (i : Nat)) == t)) := by
  cases useDh1
  · have hlt : (uf : Nat) * S.N_send_no_opk + (i : Nat) < S.N_send_no_opk_tot :=
      mul_add_lt_mul uf.isLt i.isLt
    have htot : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
    by_cases ht : t < S.N_send_opk_tot
    · have hne : S.N_send_opk_tot + ((uf : Nat) * S.N_send_no_opk + (i : Nat)) ≠ t := by omega
      simp [paTargetChoice, ht, beq_false_of_ne hne]
    · by_cases ht2 : t < S.N_send_tot
      · simp only [paTargetChoice, Bool.false_eq_true, ht, ht2, ↓reduceIte, Bool.not_false,
          Bool.true_and]
        exact Bool.eq_iff_iff.mpr (by
          simp only [Bool.and_eq_true, beq_iff_eq]
          rw [div_mod_eq_iff i.isLt]
          omega)
      · have hne1 : (uf : Nat) ≠ S.N_id := Nat.ne_of_lt uf.isLt
        have hne2 : S.N_send_opk_tot + ((uf : Nat) * S.N_send_no_opk + (i : Nat)) ≠ t := by omega
        simp [paTargetChoice, ht, ht2, beq_false_of_ne hne1, beq_false_of_ne hne2]
  · simp [paTargetChoice]

theorem agFgPosToVal_valToFgPos (y : fgPosTy.denote) : fgPosToVal (valToFgPos y) = y := by
  rcases y with ⟨z, c⟩ | ⟨p1, p2, w1, w2⟩ <;> rfl

theorem agOptMap_fgPos_roundtrip (o : Option fgPosTy.denote) :
    (o.map valToFgPos).map fgPosToVal = o := by
  cases o <;> simp only [Option.map_none, Option.map_some, agFgPosToVal_valToFgPos]

theorem agFgPatchEntryToVal_valToFgPatchEntry (y : fgPatchEntryTy.denote) :
    fgPatchEntryToVal (valToFgPatchEntry y) = y := by
  rcases y with ⟨a, b, c, d, ss, dk⟩
  cases d <;> simp only [fgPatchEntryToVal, valToFgPatchEntry, agFgPosToVal_valToFgPos,
    Option.map_none, Option.map_some, drKeyToVal, valToDrKey, drKeyV, drKeyOfV]

theorem agValToFgPatchEntry_fgPatchEntryToVal (e : FgPatchEntry) :
    valToFgPatchEntry (fgPatchEntryToVal e) = e := fgPatchEntryIso.ofVal_toVal e

theorem agList_fgPatchEntry_roundtrip (L : List fgPatchEntryTy.denote) :
    (L.map valToFgPatchEntry).map fgPatchEntryToVal = L := by
  simp only [List.map_map, Function.comp_def, agFgPatchEntryToVal_valToFgPatchEntry, List.map_id']

theorem agList_fgPatchEntry_roundtrip' (L : List FgPatchEntry) :
    (L.map fgPatchEntryToVal).map valToFgPatchEntry = L := by
  simp only [List.map_map, Function.comp_def, agValToFgPatchEntry_fgPatchEntryToVal, List.map_id']

theorem agRootEntryToVal_valToRootEntry (y : rootEntryTy.denote) :
    rootEntryToVal (valToRootEntry y) = y := by
  rcases y with ⟨a, p, b, c⟩
  simp only [rootEntryToVal, valToRootEntry, agFgPosToVal_valToFgPos]

theorem agValToRootEntry_rootEntryToVal (e : FgRootEntry) :
    valToRootEntry (rootEntryToVal e) = e := by
  rcases e with ⟨a, p, b, c⟩
  simp only [rootEntryToVal, valToRootEntry, valToFgPos_fgPosToVal]

theorem agList_rootEntry_roundtrip (L : List rootEntryTy.denote) :
    (L.map valToRootEntry).map rootEntryToVal = L := by
  simp only [List.map_map, Function.comp_def, agRootEntryToVal_valToRootEntry, List.map_id']

theorem agList_rootEntry_roundtrip' (L : List FgRootEntry) :
    (L.map rootEntryToVal).map valToRootEntry = L := by
  simp only [List.map_map, Function.comp_def, agValToRootEntry_rootEntryToVal, List.map_id']

/-! ## Operator and query evaluation helpers -/

theorem agBytes_beq_nil (a : Bytes) : (a == []) = a.isEmpty := by
  cases a <;> rfl

@[simp] theorem eval_queryDdh {Γ : List (Ty pqSig)}
    (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B 32) (B 32)))) (env : Env Γ) :
    (Comp.queryDdh e).eval env =
      FgGapDh.ddhGdhQ (e.eval env).1 (e.eval env).2.1 (e.eval env).2.2 := by
  simp only [Comp.queryDdh, gapDhDdhOracle, FgGapDh.ddhGdhQ]; rfl

@[simp] theorem nRecvEff_mul_fin {S : Setup} (u : Fin S.N_id) :
    nRecvEff S * (u : Nat) = (u : Nat) * S.N_recv := by
  have hN : S.N_id ≠ 0 := Nat.ne_of_gt u.pos
  simp [nRecvEff, hN, Nat.mul_comm]

@[simp] theorem nSendOpkEff_mul_fin {S : Setup} (u : Fin S.N_id) :
    nSendOpkEff S * (u : Nat) = (u : Nat) * S.N_send_opk := by
  have hN : S.N_id ≠ 0 := Nat.ne_of_gt u.pos
  simp [nSendOpkEff, hN, Nat.mul_comm]

@[simp] theorem nSendNoOpkEff_mul_fin {S : Setup} (u : Fin S.N_id) :
    nSendNoOpkEff S * (u : Nat) = (u : Nat) * S.N_send_no_opk := by
  have hN : S.N_id ≠ 0 := Nat.ne_of_gt u.pos
  simp [nSendNoOpkEff, hN, Nat.mul_comm]

/-! ## Patching helpers -/

section FgEval

variable {Δ : List (Ty pqSig)}

theorem mkSecretPosC_eval (z : Expr pqxdhOps Δ (B 32)) (env : Env Δ) :
    (mkSecretPosC z).eval env = fgPosToVal <$> FgGapDh.mkSecretPos (z.eval env) := by
  simp only [mkSecretPosC, letV, bindV, v, Comp.eval_letC, eval_queryPrimC, Comp.eval,
    Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
    PTag.dec_isCanonical, SignalPqxdh.LegacyCosted.PTag.enc, id_map, FgGapDh.mkSecretPos, map_bind, map_pure, fgPosToVal]
  rfl

theorem mkPairPosC_eval (pk1 pk2 : Expr pqxdhOps Δ (B 32)) (env : Env Δ) :
    (mkPairPosC pk1 pk2).eval env =
      fgPosToVal <$> FgGapDh.mkPairPos (pk1.eval env) (pk2.eval env) := by
  simp only [mkPairPosC, letV, bindV, v, Comp.eval_letC, eval_queryPrimC, Comp.eval,
    Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
    PTag.dec_pow8, SignalPqxdh.LegacyCosted.PTag.enc, id_map, FgGapDh.mkPairPos, map_bind, map_pure, fgPosToVal]
  rfl

theorem twoSideC_eval (a : Expr pqxdhOps Δ quadTy) (env : Env Δ) :
    (twoSideC a).eval env =
      fgPosToVal <$> FgGapDh.computeTwoSideOrPairPos (a.eval env).1 (a.eval env).2.1
        (a.eval env).2.2.1 (a.eval env).2.2.2 := by
  simp only [twoSideC, letV, bindV, v, bytesEmpty, Comp.eval_letC, eval_queryPrimC, Comp.eval,
    Expr.eval_bytesBeq, Expr.eval_litBytes, Expr.eval, Ext.refl_wk, Env.get_vz,
    PTag.dec_x25519, SignalPqxdh.LegacyCosted.PTag.enc, id_map, mkSecretPosC_eval, mkPairPosC_eval,
    FgGapDh.computeTwoSideOrPairPos]
  rcases a.eval env with ⟨s1, s2, p1, p2⟩
  erw [agBytes_beq_nil s1, agBytes_beq_nil s2]
  cases s1.isEmpty <;> cases s2.isEmpty <;>
    simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, map_bind] <;> rfl

theorem twoSideOptC_eval (o : Expr pqxdhOps Δ (.opt quadTy)) (env : Env Δ) :
    (twoSideOptC o).eval env =
      Option.map fgPosToVal <$> (match o.eval env with
        | none => pure none
        | some a => some <$> FgGapDh.computeTwoSideOrPairPos a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  simp only [twoSideOptC, caseOptV, bindV, v, Comp.eval, Expr.eval, Ext.refl_wk, Env.get_vz]
  rcases o.eval env with _ | a
  · simp only [map_pure, Option.map_none]
  · simp only [twoSideC_eval, Expr.eval, Env.get_vz, bind_map_left, Option.map_some,
      Functor.map_map]
    rw [map_eq_bind_pure_comp]
    rfl

theorem ddhEqC_eval (p1 p2 : Expr pqxdhOps Δ fgPosTy) (env : Env Δ) :
    (ddhEqC p1 p2).eval env =
      FgGapDh.ddhEqGdh (valToFgPos (p1.eval env)) (valToFgPos (p2.eval env)) := by
  simp only [ddhEqC, letV, caseSumV, v, Comp.eval_letC, eval_queryDdh, Comp.eval,
    Expr.eval_bytesBeq, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz]
  rcases p1.eval env with ⟨z1, c1⟩ | ⟨a1, b1, w1, w2⟩ <;>
    rcases p2.eval env with ⟨z2, c2⟩ | ⟨a2, b2, w3, w4⟩ <;>
    (dsimp only; try erw [ite_true_eq_or]) <;> rfl

theorem ddhEqOptC_eval (p1 p2 : Expr pqxdhOps Δ (.opt fgPosTy)) (env : Env Δ) :
    (ddhEqOptC p1 p2).eval env =
      FgGapDh.ddhEqOptGdh ((p1.eval env).map valToFgPos) ((p2.eval env).map valToFgPos) := by
  simp only [ddhEqOptC, letV, caseOptV, eCaseOpt, v, Comp.eval_letC, Comp.eval, Expr.eval,
    Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, ddhEqC_eval]
  rcases p1.eval env with _ | q1 <;> rcases p2.eval env with _ | q2 <;> rfl

theorem entryMatchesC_eval {Γ₁ Γ₂ : List (Ty pqSig)} (k : Var Γ₁ patchKeyTy)
    (e : Var Γ₂ fgPatchEntryTy) [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ) :
    (entryMatchesC k e).eval env =
      FgGapDh.fgEntryMatches (valToFgPos (Env.get env (h₁.wk k)).1)
        (valToFgPos (Env.get env (h₁.wk k)).2.1) (valToFgPos (Env.get env (h₁.wk k)).2.2.1)
        ((Env.get env (h₁.wk k)).2.2.2.1.map valToFgPos) (Env.get env (h₁.wk k)).2.2.2.2
        (valToFgPatchEntry (Env.get env (h₂.wk e))) := by
  simp only [entryMatchesC, bindV, v, pkP1, pkP2, pkP3, pkP4, pkSs, feP1, feP2, feP3, feP4, feSs,
    Comp.eval, Expr.eval_bytesBeq, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
    ddhEqC_eval, ddhEqOptC_eval, FgGapDh.fgEntryMatches, valToFgPatchEntry]
  rfl

theorem patchC_eval {Γ₁ : List (Ty pqSig)} (K : Nat) (k : Var Γ₁ patchKeyTy) [h₁ : Ext Γ₁ Δ]
    (L : Expr pqxdhOps Δ (.list fgPatchEntryTy)) (env : Env Δ) :
    (patchC K k L).eval env =
      (fun r => (drKeyToVal r.1, r.2.map fgPatchEntryToVal)) <$>
        FgGapDh.fgPatch K (valToFgPos (Env.get env (h₁.wk k)).1)
          (valToFgPos (Env.get env (h₁.wk k)).2.1) (valToFgPos (Env.get env (h₁.wk k)).2.2.1)
          ((Env.get env (h₁.wk k)).2.2.2.1.map valToFgPos) (Env.get env (h₁.wk k)).2.2.2.2
          ((L.eval env).map valToFgPatchEntry) := by
  simp only [patchC, letV, bindV, caseOptV, findMV, v, pkP1, pkP2, pkP3, pkP4, pkSs, feDk,
    Comp.eval_letC, eval_sampleDrKey96C, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
    Env.get_vs, Env.get_vz, entryMatchesC_eval, FgGapDh.fgPatch, agFindML_eq_findMGdh,
    ← List.map_take, agFindMGdh_map, map_bind, bind_map_left]
  refine congrArg (fun h => _ >>= h) (funext fun o => ?_)
  rcases o with _ | e
  · simp only [Option.map_none, map_bind, map_pure, List.map_cons]
    rw [agList_fgPatchEntry_roundtrip]
    simp only [fgPatchEntryToVal]
    rw [agOptMap_fgPos_roundtrip]
    simp only [agFgPosToVal_valToFgPos]
    rfl
  · simp only [Option.map_some, map_pure]
    rw [agList_fgPatchEntry_roundtrip]
    rfl

theorem rootPatchC_eval (K : Nat) (rk : Expr pqxdhOps Δ (B 32)) (pos : Expr pqxdhOps Δ fgPosTy)
    (L : Expr pqxdhOps Δ (.list rootEntryTy)) (env : Env Δ) :
    (rootPatchC K rk pos L).eval env =
      (fun r => (r.1, r.2.map rootEntryToVal)) <$>
        fgRootPatch K (rk.eval env) (valToFgPos (pos.eval env))
          ((L.eval env).map valToRootEntry) := by
  simp only [rootPatchC, letV, bindV, caseOptV, findMV, v, reRk, rePos, reRk1, reCk,
    Comp.eval_letC, eval_sampleBytes32C, Comp.eval, Expr.eval_bytesBeq, Expr.eval,
    Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, ddhEqC_eval,
    fgRootPatch, agFindML_eq_findMGdh, ← List.map_take, agFindMGdh_map, map_bind,
    bind_map_left]
  have hp : (fun x : rootEntryTy.denote =>
      if (!rk.eval env == x.1) = true then (pure false : OracleComp GdhSimSpec Bool)
      else FgGapDh.ddhEqGdh (valToFgPos (pos.eval env)) (valToFgPos x.2.1)) =
      fun x => fgRootEntryMatches (rk.eval env) (valToFgPos (pos.eval env)) (valToRootEntry x) := by
    funext x; rfl
  rw [hp]
  refine congrArg (fun h => _ >>= h) (funext fun o => ?_)
  rcases o with _ | e
  · simp only [Option.map_none, map_bind, map_pure, List.map_cons]
    rw [agList_rootEntry_roundtrip]
    simp only [rootEntryToVal, agFgPosToVal_valToFgPos]
    rfl
  · simp only [Option.map_some, map_pure]
    rw [agList_rootEntry_roundtrip]
    rfl

end FgEval

end SignalPqxdh.Security.ReductionDsl.AuthHs
