/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepPows
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSimSend
import VCVio.EvalDist.Monad.Basic

/-!
# Extraction and RO-query evaluation for the `Auth` Gap-DH DSL

Proves evaluation equivalence for `.roQuery` (`fgRoC_eval`) and CDH candidate extraction
(`fgExtractC_eval` and `fg2ExtractC_eval`).
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

/-! ## Short-circuiting fold -/

theorem agFoldML_findMap_some {α : Type}
    (step : α → Option Bytes → OracleComp (PrimBaseSpec + gapDhDdhOracle.spec) (Option Bytes))
    (hs : ∀ x z, step x (some z) = pure (some z)) (z : Bytes) (L : List α) :
    foldML step (some z) L = pure (some z) := by
  induction L with
  | nil => rfl
  | cons x xs ih => simp only [foldML, hs, pure_bind, ih]

theorem agFoldML_findMap {α : Type} (f : α → OracleComp GdhSimSpec Bytes) (U V : Bytes)
    (step : α → Option Bytes → OracleComp (PrimBaseSpec + gapDhDdhOracle.spec) (Option Bytes))
    (hn : ∀ x, step x none = f x >>= fun z => FgGapDh.ddhGdhQ U V z >>= fun b =>
      pure (if b then some z else none))
    (hs : ∀ x z, step x (some z) = pure (some z)) (L : List α) :
    foldML step none L = FgGapDh.findMapMGdh f U V L := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [foldML, hn, FgGapDh.findMapMGdh, bind_assoc]
    refine congrArg (fun k => f x >>= k) (funext fun z => ?_)
    refine congrArg (fun k => FgGapDh.ddhGdhQ U V z >>= k) (funext fun b => ?_)
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, ih]
    · simp only [↓reduceIte, pure_bind, agFoldML_findMap_some step hs]

theorem agFoldML_map {α β γ : Type} (g : α → β)
    (step : β → γ → OracleComp (PrimBaseSpec + gapDhDdhOracle.spec) γ) (b : γ) (L : List α) :
    foldML step b (L.map g) = foldML (fun x acc => step (g x) acc) b L := by
  induction L generalizing b with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, foldML, ih]

theorem agFoldML_findMap_map {α β : Type} (g : α → β) (f : α → OracleComp GdhSimSpec Bytes)
    (U V : Bytes)
    (step : β → Option Bytes → OracleComp (PrimBaseSpec + gapDhDdhOracle.spec) (Option Bytes))
    (hn : ∀ x, step (g x) none = f x >>= fun z => FgGapDh.ddhGdhQ U V z >>= fun b =>
      pure (if b then some z else none))
    (hs : ∀ x z, step x (some z) = pure (some z)) (L : List α) :
    foldML step none (L.map g) = FgGapDh.findMapMGdh f U V L := by
  rw [agFoldML_map]
  exact agFoldML_findMap f U V (fun x acc => step (g x) acc) hn (fun x z => hs (g x) z) L

theorem agFoldML_findMap_take {α β : Type} (g : α → β) (f : α → OracleComp GdhSimSpec Bytes)
    (U V : Bytes)
    (step : β → Option Bytes → OracleComp (PrimBaseSpec + gapDhDdhOracle.spec) (Option Bytes))
    (hn : ∀ x, step (g x) none = f x >>= fun z => FgGapDh.ddhGdhQ U V z >>= fun b =>
      pure (if b then some z else none))
    (hs : ∀ x z, step x (some z) = pure (some z)) (N : Nat) (L : List α) :
    foldML step none ((L.map g).take N) = FgGapDh.findMapMGdh f U V (L.take N) := by
  rw [← List.map_take]
  exact agFoldML_findMap_map g f U V step hn hs _

theorem agRespCand_eq (S : Setup) (L : List ((Nat × Nat) × SpkBundleEntry)) (k : Nat × Nat)
    (pk : Bytes) :
    respAuthCandGdh S L k pk = FgGapDh.primGdhQ (.x25519
      (match (L.take S.N_dh).find? (fun x => x.1.1 == k.1 && x.1.2 == k.2) with
        | some e => e.2.spkSk
        | none => []) pk) := by
  simp only [respAuthCandGdh]
  split
  next fst b heq =>
    have h : List.find? (fun x => x.1.1 == k.1 && x.1.2 == k.2) (L.take S.N_dh) =
        some (fst, b) := by
      rw [← heq]; congr 1
    rw [h]
  next heq =>
    have h : List.find? (fun x => x.1.1 == k.1 && x.1.2 == k.2) (L.take S.N_dh) = none := by
      rw [← heq]; congr 1
    rw [h]

/-! ## SPK powers and initiator candidate -/

theorem agSpkPows_eq (L : List ((Nat × Nat) × SpkBundleEntry)) :
    FgGapDh.spkPowsGdh L = mapML (m := OracleComp (PrimBaseSpec + gapDhDdhOracle.spec))
      (fun x : (Ty.prod (.prod .nat .nat) spkBundleEntryTy).denote => do
        let w ← FgGapDh.primGdhQ (.pow8 x.2.2.1)
        pure (x.2.1, w))
      (L.map (Prod.map id spkBundleEntryToVal)) := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨k, b⟩ := x
    simp only [FgGapDh.spkPowsGdh, List.map_cons, mapML, ih, bind_assoc, pure_bind]
    rfl

theorem agMemSupport_mapML_length {α β : Type} (f : α → OracleComp GdhSimSpec β) (L : List α)
    (ys : List β) (h : ys ∈ support (mapML f L)) : ys.length = L.length := by
  induction L generalizing ys with
  | nil =>
    change ys ∈ support (pure [] : OracleComp GdhSimSpec (List β)) at h
    simp only [support_pure, Set.mem_singleton_iff] at h
    subst h; rfl
  | cons x xs ih =>
    change ys ∈ support (f x >>= fun y => mapML f xs >>= fun zs =>
      pure (y :: zs)) at h
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at h
    obtain ⟨y, _, zs, hzs, rfl⟩ := h
    simp only [List.length_cons, ih zs hzs]

theorem agSenderIdx_eq {S : Setup} (sid : SessionId S) :
    (match sessionIdToVal sid with
      | Sum.inl a => a.1
      | Sum.inr b => match b with
        | Sum.inl a => a.1
        | Sum.inr b => match b with
          | Sum.inl a => a.1
          | Sum.inr a => a.1 : Nat) = sessionSenderIdx sid := by
  cases sid <;> rfl

theorem queryPrimC_x25519_eval {Δ : List (Ty pqSig)}
    (a b : Expr pqxdhOps Δ (B 32)) (env : Env Δ) :
    (Comp.queryPrimC (C := gapDhDdhOracle) .x25519 (.pair a b)).eval env =
      FgGapDh.primGdhQ (.x25519 (a.eval env) (b.eval env)) := by
  simp only [eval_queryPrimC, PTag.dec_x25519, SignalPqxdh.LegacyCosted.PTag.enc, id_map, Expr.eval]
  rfl

theorem queryPrimC_pow8_eval {Δ : List (Ty pqSig)}
    (a : Expr pqxdhOps Δ (B 32)) (env : Env Δ) :
    (Comp.queryPrimC (C := gapDhDdhOracle) .pow8 a).eval env =
      FgGapDh.primGdhQ (.pow8 (a.eval env)) := by
  simp only [eval_queryPrimC, PTag.dec_pow8, SignalPqxdh.LegacyCosted.PTag.enc, id_map]
  rfl

/-! ## Handlers -/

section Fin

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
  [h₃ : Ext Γ₃ Δ] (env : Env Δ) (st : FgAuthSimState S) (U V : Bytes) (useDh1 : Bool)
  (t sIdx : Nat)

@[simp] private theorem take_pnat_32 (bs : Bytes) : List.take (32 : ℕ+) bs = List.take 32 bs := rfl

theorem fgRoC_eval (sim : Var Γ₁ fgSimTy) (sec : Var Γ₂ (B 192)) (secv : Bytes)
    (hsim : Env.get env (h₁.wk sim) = fgSimToVal st)
    (hsec : Env.get env (h₂.wk sec) = secv)
    (hB : AgBnd K st) :
    (fgRoC K sim sec).eval env =
      (fun r => (authRespToVal r.1, fgSimToVal r.2)) <$>
        fgAuthStep useDh1 t sIdx S K U V (.roQuery secv) st := by
  simp only [fgRoC, v, bindV, letV, caseOptV, eFind, slice32, eval_natEq, aDrKey,
    fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsUpd, fsMk,
    Comp.eval_letC, eval_sampleDrKey96C, Comp.eval,
    Expr.eval_litBytes, Expr.eval_bytesTakeK, take_pnat_32, Expr.eval_bytesDrop, Expr.eval_bytesLen,
    Expr.eval_bytesBeq, Expr.eval, ite_true_eq_or,
    Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
    hsim, hsec, mkSecretPosC_eval, patchC_eval, fgSimToVal]
  simp only [fgAuthStep, fgRoQueryAuthGdh, FgGapDh.parseRoSecrets]
  have hr : (st.rawRoCache.map (Prod.map id drKeyToVal)).take K =
      st.rawRoCache.map (Prod.map id drKeyToVal) :=
    List.take_of_length_le (by simpa using hB.raw_le)
  rw [hr, List.find?_map]
  by_cases hx : (List.take 32 secv == F_X25519) = true
  · by_cases h160 : (secv.length == 160) = true
    · have h192 : (secv.length == 192) = false := by
        rw [beq_iff_eq.mp h160]; rfl
      simp only [hx, h160, h192, bne, Bool.not_true, Bool.true_and, Bool.true_or,
        Bool.false_eq_true, ↓reduceIte, bind_map_left, valToFgPos_fgPosToVal, pure_bind,
        Option.map_none, map_bind, map_pure]
      erw [agList_fgPatchEntry_roundtrip']
      rfl
    · by_cases h192 : (secv.length == 192) = true
      · simp only [hx, h160, h192, bne, Bool.not_true, Bool.true_and, Bool.or_true,
          Bool.false_eq_true, ↓reduceIte, bind_map_left, valToFgPos_fgPosToVal,
          map_bind, map_pure]
        erw [agList_fgPatchEntry_roundtrip']
        rfl
      · simp only [hx, h160, h192, bne, Bool.not_true, Bool.true_and, Bool.or_self,
          Bool.false_eq_true, ↓reduceIte]
        simp only [Function.comp_def, Prod.map_fst, id_eq]
        rcases hf : List.find? (fun x => x.1 == secv) st.rawRoCache with _ | ⟨s, dk⟩
        · simp only [hf, Option.map_none, map_bind, map_pure]; rfl
        · simp only [hf, Option.map_some]; rfl
  · simp only [hx, bne, Bool.false_and, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    simp only [Function.comp_def, Prod.map_fst, id_eq]
    rcases hf : List.find? (fun x => x.1 == secv) st.rawRoCache with _ | ⟨s, dk⟩
    · simp only [hf, Option.map_none, map_bind, map_pure]; rfl
    · simp only [hf, Option.map_some]; rfl

theorem findMapC_eval (pa : Var Γ₁ paramsTy) (N : Nat) {τ : Ty pqSig} {α : Type}
    (g : α → τ.denote) (L : List α) (xs : Expr pqxdhOps Δ (.list τ))
    (f : (x : Var (τ :: .opt (B 32) :: Δ) τ) → CG (τ :: .opt (B 32) :: Δ) (B 32))
    (fS : α → OracleComp GdhSimSpec Bytes)
    (hU : (paU (v pa)).eval env = U)
    (hV : (paV (v pa)).eval env = V)
    (hxs : xs.eval env = L.map g)
    (hf : ∀ x : α, (f .vz).eval (.cons (g x) (.cons none env)) = fS x) :
    (findMapC pa N xs f).eval env = FgGapDh.findMapMGdh fS U V (L.take N) := by
  dsimp only [findMapC, foldMV, Comp.eval, Expr.eval]
  rw [hxs]
  apply agFoldML_findMap_take
  · intro x
    dsimp only [caseOptV, bindV, v, paU, paV, Comp.eval, Expr.eval,
      Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz]
    rw [hf x]
    simp only [v, Expr.eval] at hU hV
    simp only [eval_queryDdh, Expr.eval, Env.get_vs, Env.get_vz, hU, hV]
    rfl
  · intro _ _
    rfl

theorem logScanC_eval (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (off : Nat)
    (hpa : Env.get env (h₁.wk pa) = paVal U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st) :
    (logScanC K pa sim off).eval env =
      FgGapDh.findMGdh (fun cand => FgGapDh.ddhGdhQ U V cand)
        ((st.advRoLog.take K).map (fun s => List.take 32 (List.drop off s))) := by
  simp only [logScanC, findMV, eMap, fsLog, slice32, paU, paV, v,
    eval_queryDdh, Comp.eval, Expr.eval_bytesTakeK, take_pnat_32, Expr.eval_bytesDrop, Expr.eval,
    Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
    hpa, hsim, fgSimToVal, paVal, ← List.map_take, List.take_take, min_self, agFindML_eq_findMGdh]

theorem respCandC_eval (sim : Var Γ₁ fgSimTy) (r : Var Γ₂ respRecTy) (pk : Expr pqxdhOps Δ (B 32))
    (rv : AuthRespRecord)
    (hsim : Env.get env (h₁.wk sim) = fgSimToVal st)
    (hr : Env.get env (h₂.wk r) = respRecToVal rv) :
    (respCandC S sim r pk).eval env =
      respAuthCandGdh S st.base.spkBundles rv.bKey (pk.eval env) := by
  rw [respCandC, queryPrimC_x25519_eval, agRespCand_eq]
  congr 2
  simp only [eCaseOpt, eFind, stSpks, fsBase, nat2Eq, eval_natEq, sbSpkSk, v,
    Expr.eval_litBytes, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
    hsim, hr, fgSimToVal, authStateToVal, respRecToVal, ← List.map_take, List.find?_map,
    Function.comp_def, Prod.map_fst, id_eq]
  generalize List.find? (fun x => x.1.1 == rv.bKey.1 && x.1.2 == rv.bKey.2)
    (List.take S.N_dh st.base.spkBundles) = o
  rcases o with _ | ⟨k, b⟩ <;> rfl

theorem initDh1CandC_eval (sim : Var Γ₁ fgSimTy)
    (spkPows : Var Γ₂ (.list (.prod (B 32) (B 32))))
    (s : Var Γ₃ authSessionEntryTy) (pows : List (Bytes × Bytes)) (sv : AuthInitiatorEntry S)
    (hsim : Env.get env (h₁.wk sim) = fgSimToVal st)
    (hpows : Env.get env (h₂.wk spkPows) = pows)
    (hs : Env.get env (h₃.wk s) = authSessionEntryToVal sv)
    (hplen : pows.length ≤ S.N_dh) (hB : AgBnd K st) :
    (initDh1CandC S K sim spkPows s).eval env =
      initAuthDh1CandWithPowsGdh st.base.principals pows st.advKeyPows sv := by
  simp only [initDh1CandC, bindV, letV, Comp.eval_letC, Comp.eval,
    queryPrimC_pow8_eval, queryPrimC_x25519_eval,
    initAuthDh1CandWithPowsGdh]
  have hpeer : (sePeerSpk (v s)).eval env = sv.peerSpkPk := by
    simp [v, hs, authSessionEntryToVal, Expr.eval]
  rw [hpeer]
  refine bind_congr' rfl (fun w => ?_)
  congr 2
  · simp only [eCaseOpt, eFind, bytesEmpty, fsPows, v,
      Expr.eval_litBytes, Expr.eval_bytesBeq, Expr.eval,
      Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
      hsim, hpows, fgSimToVal, List.take_of_length_le hplen, List.take_of_length_le hB.pows_le,
      lookupAuthSpkSkFromPows]
    have hfn : (fun x : (B 32).denote × (B 32).denote => !(x.1 == ([] : Bytes)) && x.2 == w) =
        (fun x : Bytes × Bytes => !List.isEmpty x.1 && x.2 == w) := by
      funext x; rw [agBytes_beq_nil]
    erw [hfn]
    generalize List.find? (fun x => !List.isEmpty x.1 && x.2 == w) pows = o1
    generalize List.find? (fun x => x.2 == w) st.advKeyPows = o2
    rcases o1 with _ | ⟨a1, b1⟩ <;> rcases o2 with _ | ⟨a2, b2⟩ <;> rfl
  · simp only [eCaseOpt, eFind, eCaseSum, seSid, stPrin, fsBase, eval_natEq, peIkAPk, v,
      Expr.eval_litBytes, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
      hsim, hs, fgSimToVal, authStateToVal, authSessionEntryToVal,
      take_map_of_le _ _ hB.base.principals_le, List.find?_map,
      Function.comp_def, Prod.map_fst, id_eq, lookupSenderIkPk]
    have hi := agSenderIdx_eq sv.sid
    generalize sessionSenderIdx sv.sid = i at hi ⊢
    generalize sessionIdToVal sv.sid = sidv at hi ⊢
    rcases sidv with ⟨j, _⟩ | ⟨j, _⟩ | ⟨j, _⟩ | ⟨j, _⟩ <;> simp only at hi ⊢ <;> subst hi <;>
    · generalize List.find? (fun x => x.1 == j) st.base.principals = o3
      rcases o3 with _ | ⟨a3, b3⟩ <;> rfl

theorem spkPowsC_eval (sim : Var Γ₁ fgSimTy)
    (hsim : Env.get env (h₁.wk sim) = fgSimToVal st) :
    (mapMV S.N_dh (stSpks (fsBase (v sim))) (fun e =>
      bindV (Comp.queryPrimC (C := gapDhDdhOracle) .pow8 (sbSpkPk (.snd (v e)))) (fun w =>
      Comp.ret ((sbSpkSk (.snd (v e))).pair (v w))))).eval env =
      FgGapDh.spkPowsGdh (st.base.spkBundles.take S.N_dh) := by
  simp only [mapMV, bindV, sbSpkPk, sbSpkSk, stSpks, fsBase, v,
    queryPrimC_pow8_eval, Comp.eval, Expr.eval,
    Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
    hsim, fgSimToVal, authStateToVal, ← List.map_take]
  rw [agSpkPows_eq]

theorem eval_bindV {τ σ : Ty pqSig}
    (c : CG Δ τ) (k : (x : Var (τ :: Δ) τ) → CG (τ :: Δ) σ) :
    (bindV c k).eval env = (c.eval env >>= fun x => (k .vz).eval (.cons x env)) := rfl

theorem eval_bindV_caseOpt_ret {σ : Ty pqSig}
    (c : CG Δ (.opt σ)) (kNone : CG (Ty.opt σ :: Δ) σ) :
    (bindV c (fun f => caseOptV (v f) kNone (fun z => .ret (v z)))).eval env =
      (c.eval env >>= fun o => match o with
        | none => kNone.eval (.cons none env)
        | some z => pure z) := by
  dsimp only [bindV, Comp.eval]
  refine bind_congr' rfl (fun o => ?_)
  cases o <;> rfl

theorem fgExtractC_eval (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy)
    (hpa : Env.get env (h₁.wk pa) = paVal U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st)
    (hB : AgBnd K st) :
    (fgExtractC S K pa sim).eval env = extractCdhFromAuthSimState S useDh1 K U V st := by
  have hdh1 : (paDh1 (v pa)).eval env = useDh1 := by
    simp [v, hpa, paVal, Expr.eval]
  dsimp only [fgExtractC, Comp.eval]
  rw [hdh1]
  simp only [extractCdhFromAuthSimState]
  cases useDh1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [eval_bindV_caseOpt_ret, logScanC_eval (hpa := hpa) (hsim := hsim)]
    refine bind_congr' rfl (fun o => ?_)
    rcases o with _ | z
    swap
    · rfl
    rw [eval_bindV_caseOpt_ret,
      findMapC_eval (U := U) (V := V) (g := authSessionEntryToVal) (L := st.base.sessions)
        (fS := initAuthDh3CandGdh)]
    · refine bind_congr' rfl (fun o => ?_)
      rcases o with _ | z
      swap
      · rfl
      rw [eval_bindV, findMapC_eval (U := U) (V := V) (g := respRecToVal) (L := st.respRecs)
        (fS := respAuthDh3CandGdh S st.base.spkBundles)]
      · refine bind_congr' rfl (fun o => ?_)
        rcases o with _ | z <;> rfl
      · simp [v, hpa, paVal, Expr.eval]
      · simp [v, hpa, paVal, Expr.eval]
      · simp [v, hsim, fgSimToVal, Expr.eval]
      · intro r
        exact respCandC_eval (rv := r) (hsim := by simp [hsim]) (hr := rfl) ..
    · simp [v, hpa, paVal, Expr.eval]
    · simp [v, hpa, paVal, Expr.eval]
    · simp [v, hsim, fgSimToVal, authStateToVal, Expr.eval]
    · rintro ⟨_, _, _, _, _, _, _, _, _ | ⟨_, _⟩, _, _, _⟩
      · rfl
      · dsimp only [Comp.eval]
        rw [queryPrimC_x25519_eval]
        rfl
  · simp only [↓reduceIte]
    rw [eval_bindV_caseOpt_ret, logScanC_eval (hpa := hpa) (hsim := hsim)]
    refine bind_congr' rfl (fun o => ?_)
    rcases o with _ | z
    swap
    · rfl
    rw [eval_bindV, spkPowsC_eval (st := st)]
    swap
    · simp [hsim]
    refine bind_congr_of_forall_mem_support _ (fun pows hpows => ?_)
    rw [agSpkPows_eq] at hpows
    have hlen := agMemSupport_mapML_length _ _ _ hpows
    simp only [List.length_map, List.length_take] at hlen
    have hplen : pows.length ≤ S.N_dh := by omega
    rw [eval_bindV_caseOpt_ret,
      findMapC_eval (U := U) (V := V) (g := authSessionEntryToVal) (L := st.base.sessions)
        (fS := initAuthDh1CandWithPowsGdh st.base.principals pows st.advKeyPows)]
    · refine bind_congr' rfl (fun o => ?_)
      rcases o with _ | z
      swap
      · rfl
      rw [eval_bindV, findMapC_eval (U := U) (V := V) (g := respRecToVal) (L := st.respRecs)
        (fS := respAuthDh1CandGdh S st.base.spkBundles)]
      · refine bind_congr' rfl (fun o => ?_)
        rcases o with _ | z <;> rfl
      · simp [v, hpa, paVal, Expr.eval]
      · simp [v, hpa, paVal, Expr.eval]
      · simp [v, hsim, fgSimToVal, Expr.eval]
      · intro r
        exact respCandC_eval (rv := r) (hsim := by simp [hsim]) (hr := rfl) ..
    · simp [v, hpa, paVal, Expr.eval]
    · simp [v, hpa, paVal, Expr.eval]
    · simp [v, hsim, fgSimToVal, authStateToVal, Expr.eval]
    · intro s
      exact initDh1CandC_eval (pows := pows) (sv := s)
        (hsim := by simp [hsim]) (hpows := rfl) (hs := rfl) (hplen := hplen) (hB := hB) ..

theorem fg2FindMapC_eval (pa : Var Γ₁ fg2ParamsTy) (N : Nat) {τ : Ty pqSig} {α : Type}
    (g : α → τ.denote) (L : List α) (xs : Expr pqxdhOps Δ (.list τ))
    (f : (x : Var (τ :: .opt (B 32) :: Δ) τ) → CG (τ :: .opt (B 32) :: Δ) (B 32))
    (fS : α → OracleComp GdhSimSpec Bytes)
    (hU : (fg2PaU (v pa)).eval env = U)
    (hV : (fg2PaV (v pa)).eval env = V)
    (hxs : xs.eval env = L.map g)
    (hf : ∀ x : α, (f .vz).eval (.cons (g x) (.cons none env)) = fS x) :
    (fg2FindMapC pa N xs f).eval env = FgGapDh.findMapMGdh fS U V (L.take N) := by
  dsimp only [fg2FindMapC, foldMV, Comp.eval, Expr.eval]
  rw [hxs]
  apply agFoldML_findMap_take
  · intro x
    dsimp only [caseOptV, bindV, v, fg2PaU, fg2PaV, Comp.eval, Expr.eval,
      Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz]
    rw [hf x]
    simp only [v, Expr.eval] at hU hV
    simp only [eval_queryDdh, Expr.eval, Env.get_vs, Env.get_vz, hU, hV]
    rfl
  · intro _ _
    rfl

theorem fg2LogScanC_eval (pa : Var Γ₁ fg2ParamsTy) (sim : Var Γ₂ fgSimTy) (off : Nat)
    (hpa : Env.get env (h₁.wk pa) = fg2PaVal S U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st) :
    (fg2LogScanC K pa sim off).eval env =
      FgGapDh.findMGdh (fun cand => FgGapDh.ddhGdhQ U V cand)
        ((st.advRoLog.take K).map (fun s => List.take 32 (List.drop off s))) := by
  simp only [fg2LogScanC, findMV, eMap, fsLog, slice32, fg2PaU, fg2PaV, v,
    eval_queryDdh, Comp.eval, Expr.eval_bytesTakeK, take_pnat_32, Expr.eval_bytesDrop, Expr.eval,
    Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
    hpa, hsim, fgSimToVal, fg2PaVal, ← List.map_take, List.take_take, min_self, agFindML_eq_findMGdh]

theorem fg2RespCandC_eval (sim : Var Γ₁ fgSimTy) (r : Var Γ₂ respRecTy) (pk : Expr pqxdhOps Δ (B 32))
    (rv : AuthRespRecord)
    (hsim : Env.get env (h₁.wk sim) = fgSimToVal st)
    (hr : Env.get env (h₂.wk r) = respRecToVal rv)
    (hB : AgBnd K st) :
    (fg2RespCandC S K sim r pk).eval env =
      respAuthCandGdh S st.base.spkBundles rv.bKey (pk.eval env) := by
  rw [fg2RespCandC, queryPrimC_x25519_eval, agRespCand_eq]
  congr 2
  simp only [eCaseOpt, eFind, stSpks, fsBase, nat2Eq, eval_natEq, sbSpkSk, v,
    Expr.eval_litBytes, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
    hsim, hr, fgSimToVal, authStateToVal, respRecToVal, ← List.map_take, List.find?_map,
    Function.comp_def, Prod.map_fst, id_eq,
    take_min_of_le st.base.spkBundles hB.base.spkBundles_le]
  generalize List.find? (fun x => x.1.1 == rv.bKey.1 && x.1.2 == rv.bKey.2)
    (List.take S.N_dh st.base.spkBundles) = o
  rcases o with _ | ⟨k, b⟩ <;> rfl

theorem fg2InitDh1CandC_eval (sim : Var Γ₁ fgSimTy)
    (spkPows : Var Γ₂ (.list (.prod (B 32) (B 32))))
    (s : Var Γ₃ authSessionEntryTy) (pows : List (Bytes × Bytes)) (sv : AuthInitiatorEntry S)
    (hsim : Env.get env (h₁.wk sim) = fgSimToVal st)
    (hpows : Env.get env (h₂.wk spkPows) = pows)
    (hs : Env.get env (h₃.wk s) = authSessionEntryToVal sv)
    (hplen : pows.length ≤ min K S.N_dh) (hB : AgBnd K st) :
    (fg2InitDh1CandC S K sim spkPows s).eval env =
      initAuthDh1CandWithPowsGdh st.base.principals pows st.advKeyPows sv := by
  simp only [fg2InitDh1CandC, bindV, letV, Comp.eval_letC, Comp.eval,
    queryPrimC_pow8_eval, queryPrimC_x25519_eval,
    initAuthDh1CandWithPowsGdh]
  have hpeer : (sePeerSpk (v s)).eval env = sv.peerSpkPk := by
    simp [v, hs, authSessionEntryToVal, Expr.eval]
  rw [hpeer]
  refine bind_congr' rfl (fun w => ?_)
  congr 2
  · simp only [eCaseOpt, eFind, bytesEmpty, fsPows, v,
      Expr.eval_litBytes, Expr.eval_bytesBeq, Expr.eval,
      Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
      hsim, hpows, fgSimToVal, List.take_of_length_le hplen, List.take_of_length_le hB.pows_le,
      lookupAuthSpkSkFromPows]
    have hfn : (fun x : (B 32).denote × (B 32).denote => !(x.1 == ([] : Bytes)) && x.2 == w) =
        (fun x : Bytes × Bytes => !List.isEmpty x.1 && x.2 == w) := by
      funext x; rw [agBytes_beq_nil]
    erw [hfn]
    generalize List.find? (fun x => !List.isEmpty x.1 && x.2 == w) pows = o1
    generalize List.find? (fun x => x.2 == w) st.advKeyPows = o2
    rcases o1 with _ | ⟨a1, b1⟩ <;> rcases o2 with _ | ⟨a2, b2⟩ <;> rfl
  · simp only [eCaseOpt, eFind, eCaseSum, seSid, stPrin, fsBase, eval_natEq, peIkAPk, v,
      Expr.eval_litBytes, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
      hsim, hs, fgSimToVal, authStateToVal, authSessionEntryToVal,
      take_map_of_le _ _ hB.base.principals_le, List.find?_map,
      Function.comp_def, Prod.map_fst, id_eq, lookupSenderIkPk]
    have hi := agSenderIdx_eq sv.sid
    generalize sessionSenderIdx sv.sid = i at hi ⊢
    generalize sessionIdToVal sv.sid = sidv at hi ⊢
    rcases sidv with ⟨j, _⟩ | ⟨j, _⟩ | ⟨j, _⟩ | ⟨j, _⟩ <;> simp only at hi ⊢ <;> subst hi <;>
    · generalize List.find? (fun x => x.1 == j) st.base.principals = o3
      rcases o3 with _ | ⟨a3, b3⟩ <;> rfl

theorem fg2SpkPowsC_eval (sim : Var Γ₁ fgSimTy)
    (hsim : Env.get env (h₁.wk sim) = fgSimToVal st) (hB : AgBnd K st) :
    (mapMV (min K S.N_dh) (stSpks (fsBase (v sim))) (fun e =>
      bindV (Comp.queryPrimC (C := gapDhDdhOracle) .pow8 (sbSpkPk (.snd (v e)))) (fun w =>
      Comp.ret ((sbSpkSk (.snd (v e))).pair (v w))))).eval env =
      FgGapDh.spkPowsGdh (st.base.spkBundles.take S.N_dh) := by
  simp only [mapMV, bindV, sbSpkPk, sbSpkSk, stSpks, fsBase, v,
    queryPrimC_pow8_eval, Comp.eval, Expr.eval,
    Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
    hsim, fgSimToVal, authStateToVal, ← List.map_take,
    take_min_of_le st.base.spkBundles hB.base.spkBundles_le]
  rw [agSpkPows_eq]

theorem fg2ExtractC_eval (pa : Var Γ₁ fg2ParamsTy) (sim : Var Γ₂ fgSimTy)
    (hpa : Env.get env (h₁.wk pa) = fg2PaVal S U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st)
    (hB : AgBnd K st) (hresp : st.respRecs.length ≤ K) :
    (fg2ExtractC S K pa sim).eval env = extractCdhFromAuthSimState S useDh1 K U V st := by
  have hdh1 : (fg2PaDh1 (v pa)).eval env = useDh1 := by
    simp [v, hpa, fg2PaVal, (paTargetChoice_dh1 S useDh1 t).1, Expr.eval]
  dsimp only [fg2ExtractC, Comp.eval]
  rw [hdh1]
  simp only [extractCdhFromAuthSimState]
  cases useDh1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [eval_bindV_caseOpt_ret, fg2LogScanC_eval (hpa := hpa) (hsim := hsim)]
    refine bind_congr' rfl (fun o => ?_)
    rcases o with _ | z
    swap
    · rfl
    rw [eval_bindV_caseOpt_ret,
      fg2FindMapC_eval (U := U) (V := V) (g := authSessionEntryToVal) (L := st.base.sessions)
        (fS := initAuthDh3CandGdh),
      take_min_of_le st.base.sessions hB.base.sessions_le]
    · refine bind_congr' rfl (fun o => ?_)
      rcases o with _ | z
      swap
      · rfl
      rw [eval_bindV, fg2FindMapC_eval (U := U) (V := V) (g := respRecToVal) (L := st.respRecs)
        (fS := respAuthDh3CandGdh S st.base.spkBundles),
        take_min_of_le st.respRecs hresp]
      · refine bind_congr' rfl (fun o => ?_)
        rcases o with _ | z <;> rfl
      · simp [v, hpa, fg2PaVal, Expr.eval]
      · simp [v, hpa, fg2PaVal, Expr.eval]
      · simp [v, hsim, fgSimToVal, Expr.eval]
      · intro r
        exact fg2RespCandC_eval (rv := r) (hsim := by simp [hsim]) (hr := rfl) (hB := hB) ..
    · simp [v, hpa, fg2PaVal, Expr.eval]
    · simp [v, hpa, fg2PaVal, Expr.eval]
    · simp [v, hsim, fgSimToVal, authStateToVal, Expr.eval]
    · rintro ⟨_, _, _, _, _, _, _, _, _ | ⟨_, _⟩, _, _, _⟩
      · rfl
      · dsimp only [Comp.eval]
        rw [queryPrimC_x25519_eval]
        rfl
  · simp only [↓reduceIte]
    rw [eval_bindV_caseOpt_ret, fg2LogScanC_eval (hpa := hpa) (hsim := hsim)]
    refine bind_congr' rfl (fun o => ?_)
    rcases o with _ | z
    swap
    · rfl
    rw [eval_bindV, fg2SpkPowsC_eval (st := st) (hB := hB)]
    swap
    · simp [hsim]
    refine bind_congr_of_forall_mem_support _ (fun pows hpows => ?_)
    rw [agSpkPows_eq] at hpows
    have hlen := agMemSupport_mapML_length _ _ _ hpows
    simp only [List.length_map, List.length_take] at hlen
    have hBspk := hB.base.spkBundles_le
    have hplen : pows.length ≤ min K S.N_dh := by omega
    rw [eval_bindV_caseOpt_ret,
      fg2FindMapC_eval (U := U) (V := V) (g := authSessionEntryToVal) (L := st.base.sessions)
        (fS := initAuthDh1CandWithPowsGdh st.base.principals pows st.advKeyPows),
      take_min_of_le st.base.sessions hB.base.sessions_le]
    · refine bind_congr' rfl (fun o => ?_)
      rcases o with _ | z
      swap
      · rfl
      rw [eval_bindV, fg2FindMapC_eval (U := U) (V := V) (g := respRecToVal) (L := st.respRecs)
        (fS := respAuthDh1CandGdh S st.base.spkBundles),
        take_min_of_le st.respRecs hresp]
      · refine bind_congr' rfl (fun o => ?_)
        rcases o with _ | z <;> rfl
      · simp [v, hpa, fg2PaVal, Expr.eval]
      · simp [v, hpa, fg2PaVal, Expr.eval]
      · simp [v, hsim, fgSimToVal, Expr.eval]
      · intro r
        exact fg2RespCandC_eval (rv := r) (hsim := by simp [hsim]) (hr := rfl) (hB := hB) ..
    · simp [v, hpa, fg2PaVal, Expr.eval]
    · simp [v, hpa, fg2PaVal, Expr.eval]
    · simp [v, hsim, fgSimToVal, authStateToVal, Expr.eval]
    · intro s
      exact fg2InitDh1CandC_eval (pows := pows) (sv := s)
        (hsim := by simp [hsim]) (hpows := rfl) (hs := rfl) (hplen := hplen) (hB := hB) ..

end Fin

end SignalPqxdh.Security.ReductionDsl.AuthHs
