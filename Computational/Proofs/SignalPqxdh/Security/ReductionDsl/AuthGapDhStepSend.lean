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
# Send-branch evaluation for the `Auth` Gap-DH DSL

Proves that `fgSendC` and `fg2SendC` evaluate to the shallow `fgAuthStep` send branches under
`authRespToVal`, `fgSimToVal`, and `AgBnd`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

section SendEval

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
  [h₃ : Ext Γ₃ Δ] (env : Env Δ) (st : FgAuthSimState S) (U V : Bytes) (useDh1 : Bool)
  (t sIdx : Nat)

/-! ## Helpers -/

theorem agS_step_opk (uf : Fin S.N_id) (i : Fin S.N_send_opk) (b : PreKeyBundleInput)
    (m0 m1 : Bytes) :
    fgAuthStep useDh1 t sIdx S K U V (.sendOPK uf i b m0 m1) st =
      if b.opkB?.isNone then pure (.noneResp, st)
      else fgRunSendAuthGdh useDh1 t S K U (.sendOPK uf i) uf b m0 m1 st := by
  simp only [fgAuthStep]

theorem agS_step_noopk (uf : Fin S.N_id) (i : Fin S.N_send_no_opk) (b : PreKeyBundleInput)
    (m0 m1 : Bytes) :
    fgAuthStep useDh1 t sIdx S K U V (.sendNoOPK uf i b m0 m1) st =
      if b.opkB?.isSome then pure (.noneResp, st)
      else fgRunSendAuthGdh useDh1 t S K U (.sendNoOPK uf i) uf b m0 m1 st := by
  simp only [fgAuthStep]

theorem agS_usedS (s : AuthState S) :
    (authStateToVal s).2.2.2.2.2.2.1 = s.usedSendSessions.map sessionIdToVal := rfl
theorem agS_prin (s : AuthState S) :
    (authStateToVal s).2.2.1 = s.principals.map (Prod.map id principalEntryToVal) := rfl
theorem agS_spks (s : AuthState S) :
    (authStateToVal s).2.2.2.1 = s.spkBundles.map (Prod.map id spkBundleEntryToVal) := rfl
theorem agS_secb (s : AuthState S) : (authStateToVal s).1 = s.secb := rfl

@[simp] theorem agS_base (st : FgAuthSimState S) :
    (fgSimToVal st).1 = authStateToVal st.base := rfl
@[simp] theorem agS_pows (st : FgAuthSimState S) :
    (fgSimToVal st).2.2.2.2.2.2 = st.advKeyPows := rfl
@[simp] theorem agS_fgL (st : FgAuthSimState S) :
    (fgSimToVal st).2.1 = st.fgL.map fgPatchEntryToVal := rfl
@[simp] theorem agS_rootL (st : FgAuthSimState S) :
    (fgSimToVal st).2.2.1 = st.fgRootL.map rootEntryToVal := rfl

theorem agS_peel {m : Type → Type} [Monad m] [LawfulMonad m] {α α' γ δ : Type}
    (F : γ → δ) {x : m α} {x' : m α'} (h : α' → α) {g : α → m δ} {g' : α' → m γ}
    (hx : x = h <$> x') (hg : ∀ a, g (h a) = F <$> g' a) :
    x >>= g = F <$> (x' >>= g') := by
  subst hx; simp only [bind_map_left, map_bind, hg]

theorem agS_peelS {m : Type → Type} [Monad m] [LawfulMonad m] {α γ δ : Type}
    (F : γ → δ) {x x' : m α} {g : α → m δ} {g' : α → m γ}
    (hx : x = x') (hg : ∀ a, g a = F <$> g' a) :
    x >>= g = F <$> (x' >>= g') := by
  subst hx; rw [map_bind]; exact congrArg _ (funext hg)

theorem agS_ite {m : Type → Type} [Functor m] {γ δ : Type} (F : γ → δ) {c c' : Prop}
    [Decidable c] [Decidable c'] {a b : m δ} {a' b' : m γ} (hc : c ↔ c')
    (h1 : c' → a = F <$> a') (h2 : ¬ c' → b = F <$> b') :
    (if c then a else b) = F <$> (if c' then a' else b') := by
  by_cases h : c'
  · simp only [hc.mpr h, h, ↓reduceIte]; exact h1 h
  · have h' : ¬ c := fun h' => h (hc.mp h')
    simp only [h, h', ↓reduceIte]; exact h2 h

theorem agS_pure {m : Type → Type} [Monad m] [LawfulMonad m] {γ δ : Type} (F : γ → δ)
    {a : δ} {a' : γ} (h : a = F a') : (pure a : m δ) = F <$> pure a' := by
  rw [map_pure, h]

theorem agS_embedPrim_eq {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (mx : OracleComp PrimBaseSpec α) :
    FgGapDh.embedPrim (spec := spec) mx = Security.embedPrim (spec := spec) mx := rfl

theorem agS_sigV_congr {pk pk' m m' sg sg' : Bytes} (h1 : pk = pk') (h2 : m = m') (h3 : sg = sg') :
    (query (spec := PrimBaseSpec + gapDhOracleSpec)
      (Sum.inl (Sum.inr (PrimQuery.sigVerify pk m sg))) :
      OracleComp _ Bool) = FgGapDh.primGdhQ (.sigVerify pk' m' sg') := by subst h1 h2 h3; rfl

theorem agS_kem_congr {pk pk' c c' : Bytes} (h1 : pk = pk') (h2 : c = c') :
    query (spec := PrimBaseSpec + gapDhOracleSpec) (Sum.inl (Sum.inr (PrimQuery.kemEncaps pk c))) =
      FgGapDh.primGdhQ (.kemEncaps pk' c') := by subst h1 h2; rfl

theorem agS_x25519_congr {a a' c c' : Bytes} (h1 : a = a') (h2 : c = c') :
    query (spec := PrimBaseSpec + gapDhOracleSpec) (Sum.inl (Sum.inr (PrimQuery.x25519 a c))) =
      FgGapDh.primGdhQ (.x25519 a' c') := by subst h1 h2; rfl

theorem agS_aead_congr {mk mk' : MessageKeys} {ad ad' pt pt' : Bytes}
    (h1 : mk = mk') (h2 : ad = ad') (h3 : pt = pt') :
    query (spec := PrimBaseSpec + gapDhOracleSpec)
      (Sum.inl (Sum.inr (PrimQuery.aeadEnc mk ad pt))) =
      FgGapDh.primGdhQ (.aeadEnc mk' ad' pt') := by subst h1 h2 h3; rfl

theorem agS_optRT (o : Option FgPoS) : Option.map valToFgPos (Option.map fgPosToVal o) = o := by
  cases o with
  | none => rfl
  | some p => cases p <;> rfl

theorem agS_pure_ite {m : Type → Type} [Monad m] [LawfulMonad m] {γ δ : Type} (F : γ → δ)
    {c : Prop} [Decidable c] {a : δ} {a1 a2 : γ} (h : a = F (if c then a1 else a2)) :
    (pure a : m δ) = F <$> (if c then pure a1 else pure a2) := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte] at h ⊢; rw [map_pure, h]
  · simp only [hc, ↓reduceIte] at h ⊢; rw [map_pure, h]

/-! ## Send evaluation -/

set_option maxHeartbeats 4000000 in
theorem fgSendC_eval_opk (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ sendQTy)
    (uf : Fin S.N_id) (i : Fin S.N_send_opk) (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (hpa : Env.get env (h₁.wk pa) = paVal U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st)
    (hx : Env.get env (h₃.wk x) = (uf.val, (i.val, (preKeyBundleToVal b, (m0, m1)))))
    (hB : AgBnd K st) :
    (fgSendC S K true pa sim x).eval env =
      (fun r => (authRespToVal r.1, fgSimToVal r.2)) <$>
        fgAuthStep useDh1 t sIdx S K U V (.sendOPK uf i b m0 m1) st := by
  rw [agS_step_opk]
  rcases hb : b.opkB? with _ | ⟨oid, opk⟩
  · simp only [fgSendC, sendGuardE, ↓reduceIte, v, Comp.eval, Expr.eval, isSomeE, buOpkB, hx,
      preKeyBundleToVal, bundleV, hb, Bool.not_false, Option.isNone_none, map_pure, aNone, hsim]
    rfl
  simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  simp only [fgSendC, sendGuardE, ↓reduceIte, v, bindV, letV, caseOptV, eCaseOpt, eFind, eAny,
    eval_natEq, sidEq, eLet2, eLet, eCaseSum, nat2Eq, fsBase, fsPows, fsL, fsRootL, fsUpd, fsMk,
    paU, paDh1, paTI, q4, stSecb, stPrin, stSpks, stSess, stUsedS, stUpd, stMk, buIkB, buSpkB,
    buSpkSig, buSpkId, buOpkB, buPqspkB, buPqspkSig, buPqspkId, peSecIKA0, peIkAPk, peCorrupted,
    sbSpkPk, sbPqspkPk, encEC_eval, encKEM_eval, firstMsgADE_evalHs, seMk, hdMk, optFst, optSnd,
    aNone, aSendFresh, aSendUnfresh, isSomeE,
    Comp.eval_letC, Comp.eval_liftChal, eval_sampleBytes32C, eval_queryPrimC, Comp.eval,
    Expr.eval_litBytes, Expr.eval_bytesLen, Expr.eval_bytesBeq,
    Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, hx, hsim, hpa, hb,
    paVal, preKeyBundleToVal, bundleV,
    PTag.dec_x25519, PTag.dec_x25519Base, PTag.dec_sigVerify, PTag.dec_kemEncaps,
    PTag.dec_chainKdfSeed, PTag.dec_chainKdfNext, PTag.dec_deriveMsgKeys, PTag.dec_spqrInitSend,
    PTag.dec_aeadEnc, SignalPqxdh.LegacyCosted.PTag.enc, id_map,
    nSendOpkEff_mul_fin, agS_base, agS_pows, agS_fgL, agS_rootL,
    agS_usedS, agS_prin, agS_spks, agS_secb,
    twoSideC_eval, twoSideOptC_eval, patchC_eval, mkSecretPosC_eval, rootPatchC_eval]
  simp only [fgRunSendAuthGdh, initSessionSlotIdx, take_map_of_le _ _ hB.base.usedSendSessions_le,
    take_map_of_le _ _ hB.base.principals_le, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  by_cases hlen : m0.length = m1.length
  swap
  · simp only [hlen, beq_false_of_ne hlen, bne_iff_ne, ne_eq, not_false_eq_true, Bool.not_false,
      ↓reduceIte, map_pure]
    rfl
  simp only [hlen, beq_self_eq_true, bne_self_eq_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  rw [any_sid_iff _ _ (SessionId.sendOPK uf i)]
  swap
  · intro x; cases x with
    | sendOPK u i' =>
      dsimp only [sessionIdToVal, sidV]
      by_cases h1 : u = uf
      · subst h1
        by_cases h2 : i' = i
        · subst h2; simp
        · have h3 : ¬ (i'.val = i.val) := fun e => h2 (Fin.ext e)
          rw [beq_false_of_ne h3,
            beq_false_of_ne (a := SessionId.sendOPK u i) (b := SessionId.sendOPK u i')
              (fun e => h2 (SessionId.sendOPK.inj e).2.symm)]
          simp
      · have h3 : ¬ (u.val = uf.val) := fun e => h1 (Fin.ext e)
        rw [beq_false_of_ne h3,
          beq_false_of_ne (a := SessionId.sendOPK uf i) (b := SessionId.sendOPK u i')
            (fun e => h1 (SessionId.sendOPK.inj e).1.symm)]
        simp
    | _ => simp [sessionIdToVal, sidV]
  by_cases hsid : st.base.usedSendSessions.contains (SessionId.sendOPK uf i) = true
  · simp only [hsid, ↓reduceIte, map_pure]; rfl
  simp only [hsid, Bool.false_eq_true, ↓reduceIte, List.find?_map, Function.comp_def,
    Prod.map_fst, id_eq]
  by_cases hp : List.find? (fun x => x.1 == ↑uf) st.base.principals = none
  · simp only [hp, Option.map_none, map_pure]; rfl
  obtain ⟨⟨idx, uE⟩, hp'⟩ := Option.ne_none_iff_exists'.mp hp
  simp only [hp', Option.map_some, Prod.map, id_eq]
  refine agS_peel _ (Option.map (Prod.map id principalEntryToVal)) ?_ (fun peer => ?_)
  · rw [findHonestC_eval S _ st.base _ rfl _ hB.base.principals_le]
    simp only [Expr.eval, Env.get_vs, Env.get_vz, agFindHonest_eq, embedPrim_map, agS_embedPrim_eq]
  refine agS_ite _ ?_ (fun _ => agS_pure _ rfl) (fun _ => ?_)
  · rcases peer with _ | ⟨k, pE⟩ <;> simp [principalEntryToVal, bne]
  refine agS_peelS _ ?_ (fun ok => ?_)
  · rw [koskBundleOkPowsC_eval S K _ st.base _ st.advKeyPows _ rfl rfl hB.pows_le _ b
      (by simp [preKeyBundleToVal, bundleV, hb]) hB.base]
    rfl
  refine agS_ite _ Iff.rfl (fun _ => agS_pure _ rfl) (fun _ => ?_)
  refine agS_peelS _ rfl (fun ekASkRaw => ?_)
  refine agS_peelS _ rfl (fun kemCoins => ?_)
  refine agS_peelS _ rfl (fun ephASk => ?_)
  refine agS_peelS _ rfl (fun spqrCoins => ?_)
  refine agS_peelS _ ?_ (fun sigPk => ?_)
  · rw [resolveSigPkC_eval S _ st.base _ rfl _ hB.base.principals_le]
    simp only [Expr.eval, Env.get_vs, Env.get_vz, agResolveSigPk_eq, agS_embedPrim_eq]
  refine agS_peelS _ (agS_sigV_congr rfl rfl rfl) (fun v1 => ?_)
  refine agS_peelS _ (agS_sigV_congr rfl rfl rfl) (fun v2 => ?_)
  refine agS_ite _ Iff.rfl (fun _ => agS_pure _ rfl) (fun _ => ?_)
  refine agS_peelS _ (agS_kem_congr rfl rfl) (fun kr => ?_)
  rcases kr with _ | ⟨ss, kemCt⟩
  · exact agS_pure _ rfl
  dsimp only
  refine agS_peelS _ rfl (fun ekAPkRaw => ?_)
  refine agS_peelS _ ?_ (fun spkSk => ?_)
  · rw [lookupSpkSkC_eval S K _ st.base _ st.advKeyPows _ rfl rfl hB.pows_le _
      hB.base.spkBundles_le]
    rfl
  refine agS_peel _ fgPosToVal rfl (fun p1 => ?_)
  refine agS_peel _ fgPosToVal rfl (fun p2 => ?_)
  refine agS_peel _ fgPosToVal rfl (fun p3 => ?_)
  refine agS_peel _ (Option.map fgPosToVal) ?_ (fun p4 => ?_)
  · simp only [hb, Option.map_some, computeOptPos]
    rfl
  refine agS_peel _ (fun r => (drKeyToVal r.1, List.map fgPatchEntryToVal r.2)) ?_ (fun pr => ?_)
  · rw [agS_optRT, agList_fgPatchEntry_roundtrip', valToFgPos_fgPosToVal, valToFgPos_fgPosToVal,
      valToFgPos_fgPosToVal]
  refine agS_peelS _ rfl (fun ephAPk => ?_)
  refine agS_peelS _ (agS_x25519_congr rfl rfl) (fun dhR => ?_)
  refine agS_peel _ fgPosToVal rfl (fun posR => ?_)
  refine agS_peel _ (fun r => (r.1, List.map rootEntryToVal r.2)) ?_ (fun rr => ?_)
  · rw [valToFgPos_fgPosToVal, agList_rootEntry_roundtrip']
    rfl
  refine agS_peelS _ rfl (fun mkSeed => ?_)
  refine agS_peelS _ rfl (fun ck1 => ?_)
  refine agS_peelS _ rfl (fun sp => ?_)
  rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
  · exact agS_pure _ rfl
  dsimp only
  refine agS_peel _ msgKeysToVal rfl (fun mk => ?_)
  refine agS_peelS _ (agS_aead_congr rfl ?_ ?_) (fun ct => ?_)
  · simp [firstMsgAD, encodeEC, pbBytesField, principalEntryToVal]
  · rcases peer with _ | ⟨k, pE⟩ <;> (simp [principalEntryToVal]; try rfl)
  refine agS_pure_ite _ ?_
  rw [take_map_of_le _ _ hB.base.spkBundles_le]
  rcases peer with _ | ⟨k, pE⟩
  · simp [authRespToVal, fgSimToVal, authStateToVal, authSessionEntryToVal, sessionIdToVal, hb,
      principalEntryToVal]
  · simp [authRespToVal, fgSimToVal, authStateToVal, authSessionEntryToVal, sessionIdToVal, hb,
      principalEntryToVal, List.any_map, Function.comp_def, spkBundleEntryToVal, bne]

set_option maxHeartbeats 4000000 in
theorem fgSendC_eval_noopk (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ sendQTy)
    (uf : Fin S.N_id) (i : Fin S.N_send_no_opk) (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (hpa : Env.get env (h₁.wk pa) = paVal U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st)
    (hx : Env.get env (h₃.wk x) = (uf.val, (i.val, (preKeyBundleToVal b, (m0, m1)))))
    (hB : AgBnd K st) :
    (fgSendC S K false pa sim x).eval env =
      (fun r => (authRespToVal r.1, fgSimToVal r.2)) <$>
        fgAuthStep useDh1 t sIdx S K U V (.sendNoOPK uf i b m0 m1) st := by
  rw [agS_step_noopk]
  rcases hb : b.opkB? with _ | ⟨oid, opk⟩
  swap
  · simp only [fgSendC, sendGuardE, ↓reduceIte, v, Comp.eval, Expr.eval, isSomeE, buOpkB, hx,
      preKeyBundleToVal, bundleV, hb, Option.isSome_some, map_pure, aNone, hsim,
      Bool.false_eq_true]
    rfl
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  simp only [fgSendC, sendGuardE, Bool.false_eq_true, ↓reduceIte, v, bindV, letV, caseOptV,
    eCaseOpt, eFind, eAny, eval_natEq, sidEq, eLet2, eLet, eCaseSum, nat2Eq, fsBase, fsPows,
    fsL, fsRootL, fsUpd, fsMk, paU, paDh1, paTI, q4, stSecb, stPrin, stSpks, stSess, stUsedS,
    stUpd, stMk, buIkB, buSpkB, buSpkSig, buSpkId, buOpkB, buPqspkB, buPqspkSig, buPqspkId,
    peSecIKA0, peIkAPk, peCorrupted, sbSpkPk, sbPqspkPk, encEC_eval, encKEM_eval,
    firstMsgADE_evalHs, seMk, hdMk, optFst, optSnd, aNone, aSendFresh, aSendUnfresh, isSomeE,
    Comp.eval_letC, Comp.eval_liftChal, eval_sampleBytes32C, eval_queryPrimC, Comp.eval,
    Expr.eval_litBytes, Expr.eval_bytesLen, Expr.eval_bytesBeq,
    Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, hx, hsim, hpa, hb,
    paVal, preKeyBundleToVal, bundleV,
    PTag.dec_x25519, PTag.dec_x25519Base, PTag.dec_sigVerify, PTag.dec_kemEncaps,
    PTag.dec_chainKdfSeed, PTag.dec_chainKdfNext, PTag.dec_deriveMsgKeys, PTag.dec_spqrInitSend,
    PTag.dec_aeadEnc, SignalPqxdh.LegacyCosted.PTag.enc, id_map,
    nSendNoOpkEff_mul_fin, agS_base, agS_pows, agS_fgL, agS_rootL,
    agS_usedS, agS_prin, agS_spks, agS_secb,
    twoSideC_eval, twoSideOptC_eval, patchC_eval, mkSecretPosC_eval, rootPatchC_eval]
  simp only [fgRunSendAuthGdh, initSessionSlotIdx, take_map_of_le _ _ hB.base.usedSendSessions_le,
    take_map_of_le _ _ hB.base.principals_le]
  by_cases hlen : m0.length = m1.length
  swap
  · simp only [hlen, beq_false_of_ne hlen, bne_iff_ne, ne_eq, not_false_eq_true, Bool.not_false,
      ↓reduceIte, map_pure]
    rfl
  simp only [hlen, beq_self_eq_true, bne_self_eq_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  rw [any_sid_iff _ _ (SessionId.sendNoOPK uf i)]
  swap
  · intro x; cases x with
    | sendNoOPK u i' =>
      dsimp only [sessionIdToVal, sidV]
      by_cases h1 : u = uf
      · subst h1
        by_cases h2 : i' = i
        · subst h2; simp
        · have h3 : ¬ (i'.val = i.val) := fun e => h2 (Fin.ext e)
          rw [beq_false_of_ne h3,
            beq_false_of_ne (a := SessionId.sendNoOPK u i) (b := SessionId.sendNoOPK u i')
              (fun e => h2 (SessionId.sendNoOPK.inj e).2.symm)]
          simp
      · have h3 : ¬ (u.val = uf.val) := fun e => h1 (Fin.ext e)
        rw [beq_false_of_ne h3,
          beq_false_of_ne (a := SessionId.sendNoOPK uf i) (b := SessionId.sendNoOPK u i')
            (fun e => h1 (SessionId.sendNoOPK.inj e).1.symm)]
        simp
    | _ => simp [sessionIdToVal, sidV]
  by_cases hsid : st.base.usedSendSessions.contains (SessionId.sendNoOPK uf i) = true
  · simp only [hsid, ↓reduceIte, map_pure]; rfl
  simp only [hsid, Bool.false_eq_true, ↓reduceIte, List.find?_map, Function.comp_def,
    Prod.map_fst, id_eq]
  by_cases hp : List.find? (fun x => x.1 == ↑uf) st.base.principals = none
  · simp only [hp, Option.map_none, map_pure]; rfl
  obtain ⟨⟨idx, uE⟩, hp'⟩ := Option.ne_none_iff_exists'.mp hp
  simp only [hp', Option.map_some, Prod.map, id_eq]
  refine agS_peel _ (Option.map (Prod.map id principalEntryToVal)) ?_ (fun peer => ?_)
  · rw [findHonestC_eval S _ st.base _ rfl _ hB.base.principals_le]
    simp only [Expr.eval, Env.get_vs, Env.get_vz, agFindHonest_eq, embedPrim_map, agS_embedPrim_eq]
  refine agS_ite _ ?_ (fun _ => agS_pure _ rfl) (fun _ => ?_)
  · rcases peer with _ | ⟨k, pE⟩ <;> simp [principalEntryToVal, bne]
  refine agS_peelS _ ?_ (fun ok => ?_)
  · rw [koskBundleOkPowsC_eval S K _ st.base _ st.advKeyPows _ rfl rfl hB.pows_le _ b
      (by simp [preKeyBundleToVal, bundleV, hb]) hB.base]
    rfl
  refine agS_ite _ Iff.rfl (fun _ => agS_pure _ rfl) (fun _ => ?_)
  refine agS_peelS _ rfl (fun ekASkRaw => ?_)
  refine agS_peelS _ rfl (fun kemCoins => ?_)
  refine agS_peelS _ rfl (fun ephASk => ?_)
  refine agS_peelS _ rfl (fun spqrCoins => ?_)
  refine agS_peelS _ ?_ (fun sigPk => ?_)
  · rw [resolveSigPkC_eval S _ st.base _ rfl _ hB.base.principals_le]
    simp only [Expr.eval, Env.get_vs, Env.get_vz, agResolveSigPk_eq, agS_embedPrim_eq]
  refine agS_peelS _ (agS_sigV_congr rfl rfl rfl) (fun v1 => ?_)
  refine agS_peelS _ (agS_sigV_congr rfl rfl rfl) (fun v2 => ?_)
  refine agS_ite _ Iff.rfl (fun _ => agS_pure _ rfl) (fun _ => ?_)
  refine agS_peelS _ (agS_kem_congr rfl rfl) (fun kr => ?_)
  rcases kr with _ | ⟨ss, kemCt⟩
  · exact agS_pure _ rfl
  dsimp only
  refine agS_peelS _ rfl (fun ekAPkRaw => ?_)
  refine agS_peelS _ ?_ (fun spkSk => ?_)
  · rw [lookupSpkSkC_eval S K _ st.base _ st.advKeyPows _ rfl rfl hB.pows_le _
      hB.base.spkBundles_le]
    rfl
  refine agS_peel _ fgPosToVal rfl (fun p1 => ?_)
  refine agS_peel _ fgPosToVal rfl (fun p2 => ?_)
  refine agS_peel _ fgPosToVal rfl (fun p3 => ?_)
  refine agS_peel _ (Option.map fgPosToVal) ?_ (fun p4 => ?_)
  · simp only [hb, Option.map_none, computeOptPos, map_pure]
    try rfl
  refine agS_peel _ (fun r => (drKeyToVal r.1, List.map fgPatchEntryToVal r.2)) ?_ (fun pr => ?_)
  · rw [agS_optRT, agList_fgPatchEntry_roundtrip', valToFgPos_fgPosToVal, valToFgPos_fgPosToVal,
      valToFgPos_fgPosToVal]
  refine agS_peelS _ rfl (fun ephAPk => ?_)
  refine agS_peelS _ (agS_x25519_congr rfl rfl) (fun dhR => ?_)
  refine agS_peel _ fgPosToVal rfl (fun posR => ?_)
  refine agS_peel _ (fun r => (r.1, List.map rootEntryToVal r.2)) ?_ (fun rr => ?_)
  · rw [valToFgPos_fgPosToVal, agList_rootEntry_roundtrip']
    rfl
  refine agS_peelS _ rfl (fun mkSeed => ?_)
  refine agS_peelS _ rfl (fun ck1 => ?_)
  refine agS_peelS _ rfl (fun sp => ?_)
  rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
  · exact agS_pure _ rfl
  dsimp only
  refine agS_peel _ msgKeysToVal rfl (fun mk => ?_)
  refine agS_peelS _ (agS_aead_congr rfl ?_ ?_) (fun ct => ?_)
  · simp [firstMsgAD, encodeEC, pbBytesField, principalEntryToVal]
  · rcases peer with _ | ⟨k, pE⟩ <;> (simp [principalEntryToVal]; try rfl)
  refine agS_pure_ite _ ?_
  rw [take_map_of_le _ _ hB.base.spkBundles_le]
  rcases peer with _ | ⟨k, pE⟩
  · simp [authRespToVal, fgSimToVal, authStateToVal, authSessionEntryToVal, sessionIdToVal, hb,
      principalEntryToVal]
  · simp [authRespToVal, fgSimToVal, authStateToVal, authSessionEntryToVal, sessionIdToVal, hb,
      principalEntryToVal, List.any_map, Function.comp_def, spkBundleEntryToVal, bne]

set_option maxHeartbeats 4000000 in
theorem fg2SendC_eval_opk (pa : Var Γ₁ fg2ParamsTy) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ sendQTy)
    (uf : Fin S.N_id) (i : Fin S.N_send_opk) (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (hpa : Env.get env (h₁.wk pa) = fg2PaVal S U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st)
    (hx : Env.get env (h₃.wk x) = (uf.val, (i.val, (preKeyBundleToVal b, (m0, m1)))))
    (hB : AgBnd K st) :
    (fg2SendC S K true pa sim x).eval env =
      (fun r => (authRespToVal r.1, fgSimToVal r.2)) <$>
        fgAuthStep useDh1 t sIdx S K U V (.sendOPK uf i b m0 m1) st := by
  rw [agS_step_opk]
  rcases hb : b.opkB? with _ | ⟨oid, opk⟩
  · simp only [fg2SendC, sendGuardE, ↓reduceIte, v, Comp.eval, Expr.eval, isSomeE, buOpkB, hx,
      preKeyBundleToVal, bundleV, hb, Bool.not_false, Option.isNone_none, map_pure, aNone, hsim]
    rfl
  simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  simp only [fg2SendC, sendGuardE, ↓reduceIte, v, bindV, letV, caseOptV, eCaseOpt, eFind, eAny,
    eval_natEq, sidEq, eLet2, eLet, eCaseSum, nat2Eq, fsBase, fsPows, fsL, fsRootL, fsUpd, fsMk,
    fg2PaU, fg2PaDh1, fg2PaTI, fg2PaSendOpk, fg2PaSendIdx, q4, stSecb, stPrin, stSpks, stSess,
    stUsedS, stUpd, stMk, buIkB, buSpkB, buSpkSig, buSpkId, buOpkB, buPqspkB, buPqspkSig, buPqspkId,
    peSecIKA0, peIkAPk, peCorrupted, sbSpkPk, sbPqspkPk, encEC_eval, encKEM_eval, firstMsgADE_evalHs,
    seMk, hdMk, optFst, optSnd, aNone, aSendFresh, aSendUnfresh, isSomeE,
    Comp.eval_letC, Comp.eval_liftChal, eval_sampleBytes32C, eval_queryPrimC, Comp.eval,
    Expr.eval_litBytes, Expr.eval_bytesLen, Expr.eval_bytesBeq,
    Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, hx, hsim, hpa, hb,
    fg2PaVal, paTargetChoice_opk_beq, preKeyBundleToVal, bundleV,
    PTag.dec_x25519, PTag.dec_x25519Base, PTag.dec_sigVerify, PTag.dec_kemEncaps,
    PTag.dec_chainKdfSeed, PTag.dec_chainKdfNext, PTag.dec_deriveMsgKeys, PTag.dec_spqrInitSend,
    PTag.dec_aeadEnc, SignalPqxdh.LegacyCosted.PTag.enc, id_map,
    agS_base, agS_pows, agS_fgL, agS_rootL,
    agS_usedS, agS_prin, agS_spks, agS_secb,
    twoSideC_eval, twoSideOptC_eval, patchC_eval, mkSecretPosC_eval, rootPatchC_eval]
  simp only [fgRunSendAuthGdh, initSessionSlotIdx, take_map_of_le _ _ hB.base.usedSendSessions_le,
    take_map_of_le _ _ hB.base.principals_le, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  by_cases hlen : m0.length = m1.length
  swap
  · simp only [hlen, beq_false_of_ne hlen, bne_iff_ne, ne_eq, not_false_eq_true, Bool.not_false,
      ↓reduceIte, map_pure]
    rfl
  simp only [hlen, beq_self_eq_true, bne_self_eq_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  rw [any_sid_iff _ _ (SessionId.sendOPK uf i)]
  swap
  · intro x; cases x with
    | sendOPK u i' =>
      dsimp only [sessionIdToVal, sidV]
      by_cases h1 : u = uf
      · subst h1
        by_cases h2 : i' = i
        · subst h2; simp
        · have h3 : ¬ (i'.val = i.val) := fun e => h2 (Fin.ext e)
          rw [beq_false_of_ne h3,
            beq_false_of_ne (a := SessionId.sendOPK u i) (b := SessionId.sendOPK u i')
              (fun e => h2 (SessionId.sendOPK.inj e).2.symm)]
          simp
      · have h3 : ¬ (u.val = uf.val) := fun e => h1 (Fin.ext e)
        rw [beq_false_of_ne h3,
          beq_false_of_ne (a := SessionId.sendOPK uf i) (b := SessionId.sendOPK u i')
            (fun e => h1 (SessionId.sendOPK.inj e).1.symm)]
        simp
    | _ => simp [sessionIdToVal, sidV]
  by_cases hsid : st.base.usedSendSessions.contains (SessionId.sendOPK uf i) = true
  · simp only [hsid, ↓reduceIte, map_pure]; rfl
  simp only [hsid, Bool.false_eq_true, ↓reduceIte, List.find?_map, Function.comp_def,
    Prod.map_fst, id_eq]
  by_cases hp : List.find? (fun x => x.1 == ↑uf) st.base.principals = none
  · simp only [hp, Option.map_none, map_pure]; rfl
  obtain ⟨⟨idx, uE⟩, hp'⟩ := Option.ne_none_iff_exists'.mp hp
  simp only [hp', Option.map_some, Prod.map, id_eq]
  refine agS_peel _ (Option.map (Prod.map id principalEntryToVal)) ?_ (fun peer => ?_)
  · rw [findHonestC_eval S _ st.base _ rfl _ hB.base.principals_le]
    simp only [Expr.eval, Env.get_vs, Env.get_vz, agFindHonest_eq, embedPrim_map, agS_embedPrim_eq]
  refine agS_ite _ ?_ (fun _ => agS_pure _ rfl) (fun _ => ?_)
  · rcases peer with _ | ⟨k, pE⟩ <;> simp [principalEntryToVal, bne]
  refine agS_peelS _ ?_ (fun ok => ?_)
  · rw [koskBundleOkPowsC_eval S K _ st.base _ st.advKeyPows _ rfl rfl hB.pows_le _ b
      (by simp [preKeyBundleToVal, bundleV, hb]) hB.base]
    rfl
  refine agS_ite _ Iff.rfl (fun _ => agS_pure _ rfl) (fun _ => ?_)
  refine agS_peelS _ rfl (fun ekASkRaw => ?_)
  refine agS_peelS _ rfl (fun kemCoins => ?_)
  refine agS_peelS _ rfl (fun ephASk => ?_)
  refine agS_peelS _ rfl (fun spqrCoins => ?_)
  refine agS_peelS _ ?_ (fun sigPk => ?_)
  · rw [resolveSigPkC_eval S _ st.base _ rfl _ hB.base.principals_le]
    simp only [Expr.eval, Env.get_vs, Env.get_vz, agResolveSigPk_eq, agS_embedPrim_eq]
  refine agS_peelS _ (agS_sigV_congr rfl rfl rfl) (fun v1 => ?_)
  refine agS_peelS _ (agS_sigV_congr rfl rfl rfl) (fun v2 => ?_)
  refine agS_ite _ Iff.rfl (fun _ => agS_pure _ rfl) (fun _ => ?_)
  refine agS_peelS _ (agS_kem_congr rfl rfl) (fun kr => ?_)
  rcases kr with _ | ⟨ss, kemCt⟩
  · exact agS_pure _ rfl
  dsimp only
  refine agS_peelS _ rfl (fun ekAPkRaw => ?_)
  refine agS_peelS _ ?_ (fun spkSk => ?_)
  · rw [lookupSpkSkC_eval S K _ st.base _ st.advKeyPows _ rfl rfl hB.pows_le _
      hB.base.spkBundles_le]
    rfl
  refine agS_peel _ fgPosToVal rfl (fun p1 => ?_)
  refine agS_peel _ fgPosToVal rfl (fun p2 => ?_)
  refine agS_peel _ fgPosToVal rfl (fun p3 => ?_)
  refine agS_peel _ (Option.map fgPosToVal) ?_ (fun p4 => ?_)
  · simp only [hb, Option.map_some, computeOptPos]
    rfl
  refine agS_peel _ (fun r => (drKeyToVal r.1, List.map fgPatchEntryToVal r.2)) ?_ (fun pr => ?_)
  · rw [agS_optRT, agList_fgPatchEntry_roundtrip', valToFgPos_fgPosToVal, valToFgPos_fgPosToVal,
      valToFgPos_fgPosToVal]
  refine agS_peelS _ rfl (fun ephAPk => ?_)
  refine agS_peelS _ (agS_x25519_congr rfl rfl) (fun dhR => ?_)
  refine agS_peel _ fgPosToVal rfl (fun posR => ?_)
  refine agS_peel _ (fun r => (r.1, List.map rootEntryToVal r.2)) ?_ (fun rr => ?_)
  · rw [valToFgPos_fgPosToVal, agList_rootEntry_roundtrip']
    rfl
  refine agS_peelS _ rfl (fun mkSeed => ?_)
  refine agS_peelS _ rfl (fun ck1 => ?_)
  refine agS_peelS _ rfl (fun sp => ?_)
  rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
  · exact agS_pure _ rfl
  dsimp only
  refine agS_peel _ msgKeysToVal rfl (fun mk => ?_)
  refine agS_peelS _ (agS_aead_congr rfl ?_ ?_) (fun ct => ?_)
  · simp [firstMsgAD, encodeEC, pbBytesField, principalEntryToVal]
  · rcases peer with _ | ⟨k, pE⟩ <;> (simp [principalEntryToVal]; try rfl)
  refine agS_pure_ite _ ?_
  rw [take_map_of_le _ _ hB.base.spkBundles_le]
  rcases peer with _ | ⟨k, pE⟩
  · simp [authRespToVal, fgSimToVal, authStateToVal, authSessionEntryToVal, sessionIdToVal, hb,
      principalEntryToVal]
  · simp [authRespToVal, fgSimToVal, authStateToVal, authSessionEntryToVal, sessionIdToVal, hb,
      principalEntryToVal, List.any_map, Function.comp_def, spkBundleEntryToVal, bne]

set_option maxHeartbeats 4000000 in
theorem fg2SendC_eval_noopk (pa : Var Γ₁ fg2ParamsTy) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ sendQTy)
    (uf : Fin S.N_id) (i : Fin S.N_send_no_opk) (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (hpa : Env.get env (h₁.wk pa) = fg2PaVal S U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st)
    (hx : Env.get env (h₃.wk x) = (uf.val, (i.val, (preKeyBundleToVal b, (m0, m1)))))
    (hB : AgBnd K st) :
    (fg2SendC S K false pa sim x).eval env =
      (fun r => (authRespToVal r.1, fgSimToVal r.2)) <$>
        fgAuthStep useDh1 t sIdx S K U V (.sendNoOPK uf i b m0 m1) st := by
  rw [agS_step_noopk]
  rcases hb : b.opkB? with _ | ⟨oid, opk⟩
  swap
  · simp only [fg2SendC, sendGuardE, ↓reduceIte, v, Comp.eval, Expr.eval, isSomeE, buOpkB, hx,
      preKeyBundleToVal, bundleV, hb, Option.isSome_some, map_pure, aNone, hsim,
      Bool.false_eq_true]
    rfl
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  simp only [fg2SendC, sendGuardE, Bool.false_eq_true, ↓reduceIte, v, bindV, letV, caseOptV,
    eCaseOpt, eFind, eAny, eval_natEq, sidEq, eLet2, eLet, eCaseSum, nat2Eq, fsBase, fsPows,
    fsL, fsRootL, fsUpd, fsMk, fg2PaU, fg2PaDh1, fg2PaTI, fg2PaSendOpk, fg2PaSendIdx, q4,
    stSecb, stPrin, stSpks, stSess, stUsedS,
    stUpd, stMk, buIkB, buSpkB, buSpkSig, buSpkId, buOpkB, buPqspkB, buPqspkSig, buPqspkId,
    peSecIKA0, peIkAPk, peCorrupted, sbSpkPk, sbPqspkPk, encEC_eval, encKEM_eval,
    firstMsgADE_evalHs, seMk, hdMk, optFst, optSnd, aNone, aSendFresh, aSendUnfresh, isSomeE,
    Comp.eval_letC, Comp.eval_liftChal, eval_sampleBytes32C, eval_queryPrimC, Comp.eval,
    Expr.eval_litBytes, Expr.eval_bytesLen, Expr.eval_bytesBeq,
    Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, hx, hsim, hpa, hb,
    fg2PaVal, paTargetChoice_noopk_beq, preKeyBundleToVal, bundleV,
    PTag.dec_x25519, PTag.dec_x25519Base, PTag.dec_sigVerify, PTag.dec_kemEncaps,
    PTag.dec_chainKdfSeed, PTag.dec_chainKdfNext, PTag.dec_deriveMsgKeys, PTag.dec_spqrInitSend,
    PTag.dec_aeadEnc, SignalPqxdh.LegacyCosted.PTag.enc, id_map,
    agS_base, agS_pows, agS_fgL, agS_rootL,
    agS_usedS, agS_prin, agS_spks, agS_secb,
    twoSideC_eval, twoSideOptC_eval, patchC_eval, mkSecretPosC_eval, rootPatchC_eval]
  simp only [fgRunSendAuthGdh, initSessionSlotIdx, take_map_of_le _ _ hB.base.usedSendSessions_le,
    take_map_of_le _ _ hB.base.principals_le]
  by_cases hlen : m0.length = m1.length
  swap
  · simp only [hlen, beq_false_of_ne hlen, bne_iff_ne, ne_eq, not_false_eq_true, Bool.not_false,
      ↓reduceIte, map_pure]
    rfl
  simp only [hlen, beq_self_eq_true, bne_self_eq_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  rw [any_sid_iff _ _ (SessionId.sendNoOPK uf i)]
  swap
  · intro x; cases x with
    | sendNoOPK u i' =>
      dsimp only [sessionIdToVal, sidV]
      by_cases h1 : u = uf
      · subst h1
        by_cases h2 : i' = i
        · subst h2; simp
        · have h3 : ¬ (i'.val = i.val) := fun e => h2 (Fin.ext e)
          rw [beq_false_of_ne h3,
            beq_false_of_ne (a := SessionId.sendNoOPK u i) (b := SessionId.sendNoOPK u i')
              (fun e => h2 (SessionId.sendNoOPK.inj e).2.symm)]
          simp
      · have h3 : ¬ (u.val = uf.val) := fun e => h1 (Fin.ext e)
        rw [beq_false_of_ne h3,
          beq_false_of_ne (a := SessionId.sendNoOPK uf i) (b := SessionId.sendNoOPK u i')
            (fun e => h1 (SessionId.sendNoOPK.inj e).1.symm)]
        simp
    | _ => simp [sessionIdToVal, sidV]
  by_cases hsid : st.base.usedSendSessions.contains (SessionId.sendNoOPK uf i) = true
  · simp only [hsid, ↓reduceIte, map_pure]; rfl
  simp only [hsid, Bool.false_eq_true, ↓reduceIte, List.find?_map, Function.comp_def,
    Prod.map_fst, id_eq]
  by_cases hp : List.find? (fun x => x.1 == ↑uf) st.base.principals = none
  · simp only [hp, Option.map_none, map_pure]; rfl
  obtain ⟨⟨idx, uE⟩, hp'⟩ := Option.ne_none_iff_exists'.mp hp
  simp only [hp', Option.map_some, Prod.map, id_eq]
  refine agS_peel _ (Option.map (Prod.map id principalEntryToVal)) ?_ (fun peer => ?_)
  · rw [findHonestC_eval S _ st.base _ rfl _ hB.base.principals_le]
    simp only [Expr.eval, Env.get_vs, Env.get_vz, agFindHonest_eq, embedPrim_map, agS_embedPrim_eq]
  refine agS_ite _ ?_ (fun _ => agS_pure _ rfl) (fun _ => ?_)
  · rcases peer with _ | ⟨k, pE⟩ <;> simp [principalEntryToVal, bne]
  refine agS_peelS _ ?_ (fun ok => ?_)
  · rw [koskBundleOkPowsC_eval S K _ st.base _ st.advKeyPows _ rfl rfl hB.pows_le _ b
      (by simp [preKeyBundleToVal, bundleV, hb]) hB.base]
    rfl
  refine agS_ite _ Iff.rfl (fun _ => agS_pure _ rfl) (fun _ => ?_)
  refine agS_peelS _ rfl (fun ekASkRaw => ?_)
  refine agS_peelS _ rfl (fun kemCoins => ?_)
  refine agS_peelS _ rfl (fun ephASk => ?_)
  refine agS_peelS _ rfl (fun spqrCoins => ?_)
  refine agS_peelS _ ?_ (fun sigPk => ?_)
  · rw [resolveSigPkC_eval S _ st.base _ rfl _ hB.base.principals_le]
    simp only [Expr.eval, Env.get_vs, Env.get_vz, agResolveSigPk_eq, agS_embedPrim_eq]
  refine agS_peelS _ (agS_sigV_congr rfl rfl rfl) (fun v1 => ?_)
  refine agS_peelS _ (agS_sigV_congr rfl rfl rfl) (fun v2 => ?_)
  refine agS_ite _ Iff.rfl (fun _ => agS_pure _ rfl) (fun _ => ?_)
  refine agS_peelS _ (agS_kem_congr rfl rfl) (fun kr => ?_)
  rcases kr with _ | ⟨ss, kemCt⟩
  · exact agS_pure _ rfl
  dsimp only
  refine agS_peelS _ rfl (fun ekAPkRaw => ?_)
  refine agS_peelS _ ?_ (fun spkSk => ?_)
  · rw [lookupSpkSkC_eval S K _ st.base _ st.advKeyPows _ rfl rfl hB.pows_le _
      hB.base.spkBundles_le]
    rfl
  refine agS_peel _ fgPosToVal rfl (fun p1 => ?_)
  refine agS_peel _ fgPosToVal rfl (fun p2 => ?_)
  refine agS_peel _ fgPosToVal rfl (fun p3 => ?_)
  refine agS_peel _ (Option.map fgPosToVal) ?_ (fun p4 => ?_)
  · simp only [hb, Option.map_none, computeOptPos, map_pure]
    try rfl
  refine agS_peel _ (fun r => (drKeyToVal r.1, List.map fgPatchEntryToVal r.2)) ?_ (fun pr => ?_)
  · rw [agS_optRT, agList_fgPatchEntry_roundtrip', valToFgPos_fgPosToVal, valToFgPos_fgPosToVal,
      valToFgPos_fgPosToVal]
  refine agS_peelS _ rfl (fun ephAPk => ?_)
  refine agS_peelS _ (agS_x25519_congr rfl rfl) (fun dhR => ?_)
  refine agS_peel _ fgPosToVal rfl (fun posR => ?_)
  refine agS_peel _ (fun r => (r.1, List.map rootEntryToVal r.2)) ?_ (fun rr => ?_)
  · rw [valToFgPos_fgPosToVal, agList_rootEntry_roundtrip']
    rfl
  refine agS_peelS _ rfl (fun mkSeed => ?_)
  refine agS_peelS _ rfl (fun ck1 => ?_)
  refine agS_peelS _ rfl (fun sp => ?_)
  rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
  · exact agS_pure _ rfl
  dsimp only
  refine agS_peel _ msgKeysToVal rfl (fun mk => ?_)
  refine agS_peelS _ (agS_aead_congr rfl ?_ ?_) (fun ct => ?_)
  · simp [firstMsgAD, encodeEC, pbBytesField, principalEntryToVal]
  · rcases peer with _ | ⟨k, pE⟩ <;> (simp [principalEntryToVal]; try rfl)
  refine agS_pure_ite _ ?_
  rw [take_map_of_le _ _ hB.base.spkBundles_le]
  rcases peer with _ | ⟨k, pE⟩
  · simp [authRespToVal, fgSimToVal, authStateToVal, authSessionEntryToVal, sessionIdToVal, hb,
      principalEntryToVal]
  · simp [authRespToVal, fgSimToVal, authStateToVal, authSessionEntryToVal, sessionIdToVal, hb,
      principalEntryToVal, List.any_map, Function.comp_def, spkBundleEntryToVal, bne]

end SendEval

end SignalPqxdh.Security.ReductionDsl.AuthHs
