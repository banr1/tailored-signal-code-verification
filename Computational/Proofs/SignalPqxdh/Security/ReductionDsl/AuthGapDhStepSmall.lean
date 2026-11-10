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
# Small `Auth` Gap-DH Handlers

Evaluation lemmas for the non-handshake branches of `fgStepC`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

macro "ag_unfold" : tactic => `(tactic| simp only [
  v, bindV, letV, caseOptV, caseSumV, findMV, anyMV, eCaseOpt, eFind, eAny, eMap,
  eval_natEq, nat2Eq, nat3Eq, encEC_eval, encKEM_eval,
  stPrin, stSpks, stOpks, stAdv, stUpd, stMk,
  peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
  sbMk, oeMk, buMk, aNone, aInitPrin, aPk, aCorr, aBundle, aDrKey, aRootKdf,
  fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsUpd, fsMk, paU, paV, paDh1, paTI, paTS,
  fg2PaU, fg2PaV, fg2PaDh1, fg2PaTI, fg2PaSendOpk, fg2PaSendIdx, fg2PaTS,
  Comp.eval_letC, Comp.eval_liftChal, eval_sampleBoolC, eval_sampleBytes32C, eval_sampleRandom64C,
  eval_sampleDrKey96C, eval_sampleIndexC, eval_queryPrimC,
  eval_sampleBool, eval_sampleBytes32, eval_sampleRandom64,
  eval_sampleDrKey96,
  eval_sampleIndex, eval_queryPrim, Comp.eval,
  Expr.eval_litBytes, Expr.eval_bytesAppend, Expr.eval_bytesCons, Expr.eval_bytesWiden,
  Expr.eval_bytesTakeK, Expr.eval_bytesDrop, Expr.eval_bytesLen,
  Expr.eval_bytesBeq, Expr.eval_bytesVarint, Expr.eval_u32OfNat,
  Expr.eval_u32Beq,
  Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
  PTag.dec_x25519, PTag.dec_x25519Base, PTag.dec_isCanonical, PTag.dec_pow8, PTag.dec_sigPkGen,
  PTag.dec_sigSign, PTag.dec_sigVerify, PTag.dec_kemKeyGen, PTag.dec_kemEncaps, PTag.dec_kemDecaps,
  PTag.dec_hkdfDerive96, PTag.dec_rootCreateChain, PTag.dec_chainKdfSeed, PTag.dec_chainKdfNext,
  PTag.dec_deriveMsgKeys, PTag.dec_spqrInitSend, PTag.dec_spqrInitRecv, PTag.dec_aeadEnc,
  PTag.dec_aeadDec, SignalPqxdh.LegacyCosted.PTag.dec, SignalPqxdh.LegacyCosted.PTag.enc, id_map, id_map'])

section Small

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
  [h₃ : Ext Γ₃ Δ] (env : Env Δ) (st : FgAuthSimState S) (U V : Bytes) (useDh1 : Bool)
  (t sIdx : Nat)

theorem fgInitPrinC_eval (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (u : Var Γ₃ .nat)
    (uf : Fin S.N_id)
    (hpa : Env.get env (h₁.wk pa) = paVal U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st)
    (hu : Env.get env (h₃.wk u) = uf.val) (hB : AgBnd K st) :
    (fgInitPrinC K pa sim u).eval env =
      (fun r => (authRespToVal r.1, fgSimToVal r.2)) <$>
        fgAuthStep useDh1 t sIdx S K U V (.initPrin uf) st := by
  simp only [fgInitPrinC]
  ag_unfold
  simp only [hpa, hsim, hu, fgSimToVal, paVal, authStateToVal]
  rw [take_map_of_le _ _ hB.base.principals_le]
  simp only [fgAuthStep, List.any_map, Function.comp_def, Prod.map_fst, id_eq]
  cases ha : st.base.principals.any (fun x => x.1 == (uf : Nat))
  · simp only [Bool.false_eq_true, ↓reduceIte, map_bind, map_pure]
    cases hb : (useDh1 && (uf : Nat) == t) <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;> rfl
  · simp only [↓reduceIte, map_pure]; rfl

theorem fgGenSpkC_eval (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ (.prod .nat .nat))
    (uf : Fin S.N_id) (jf : Fin S.N_recv)
    (hpa : Env.get env (h₁.wk pa) = paVal U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st)
    (hx : Env.get env (h₃.wk x) = (uf.val, jf.val)) (hB : AgBnd K st) :
    (fgGenSpkC S K pa sim x).eval env =
      (fun r => (authRespToVal r.1, fgSimToVal r.2)) <$>
        fgAuthStep useDh1 t sIdx S K U V (.genSPK uf jf) st := by
  simp only [fgGenSpkC]
  ag_unfold
  simp only [hpa, hsim, hx, fgSimToVal, paVal, authStateToVal, nRecvEff_mul_fin]
  rw [take_map_of_le _ _ hB.base.spkBundles_le, take_map_of_le _ _ hB.base.principals_le]
  simp only [fgAuthStep, List.any_map, List.find?_map, Function.comp_def, Prod.map_fst, id_eq]
  have hp : (fun x : (Nat × Nat) × SpkBundleEntry => x.1.1 == (uf : Nat) && x.1.2 == (jf : Nat)) =
      (fun x => x.1 == ((uf : Nat), (jf : Nat))) := funext fun _ => rfl
  rw [hp]
  cases ha : st.base.spkBundles.any (fun x => x.1 == ((uf : Nat), (jf : Nat)))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases hf : List.find? (fun x => x.1 == (uf : Nat)) st.base.principals with _ | ⟨i, e⟩
    · simp only [hf, Option.map_none, map_pure]; rfl
    · simp only [hf, Option.map_some, map_bind, map_pure]
      rw [hx, hpa]
      simp only [paVal]
      rw [nRecvEff_mul_fin]
      rfl
  · simp only [↓reduceIte, map_pure]; rfl

theorem fgCorruptC_eval (sim : Var Γ₁ fgSimTy) (u : Var Γ₂ .nat) (uf : Fin S.N_id)
    (hsim : Env.get env (h₁.wk sim) = fgSimToVal st)
    (hu : Env.get env (h₂.wk u) = uf.val) (hB : AgBnd K st) :
    (onBaseF sim fun g => corruptB K g u).eval env =
      (fun r => (authRespToVal r.1, fgSimToVal r.2)) <$>
        fgAuthStep useDh1 t sIdx S K U V (.corruptIK uf) st := by
  simp only [onBaseF, corruptB, rs]
  ag_unfold
  simp only [hsim, hu, fgSimToVal, authStateToVal]
  rw [take_map_of_le _ _ hB.base.principals_le]
  simp only [fgAuthStep, List.find?_map, Function.comp_def, Prod.map_fst, id_eq]
  rcases hf : List.find? (fun x => x.1 == (uf : Nat)) st.base.principals with _ | ⟨i, e⟩
  · simp only [hf, Option.map_none, embedPrim_pure, pure_bind, map_pure]; rfl
  · simp only [hf, Option.map_some, embedPrim_pure, pure_bind, map_pure, List.map_map]
    refine congrArg pure ?_
    simp only [authRespToVal, Prod.mk.injEq, true_and, and_true]
    refine ⟨rfl, List.map_congr_left (fun x _ => ?_)⟩
    rcases x with ⟨a, e'⟩
    by_cases hx : (a == (uf : Nat)) = true
    · simp only [Function.comp_apply, Prod.map, id_eq, hx, ↓reduceIte]; rfl
    · simp only [Function.comp_apply, Prod.map, id_eq, hx, Bool.false_eq_true, ↓reduceIte]

theorem fgGenOpkC_eval (sim : Var Γ₁ fgSimTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat)))
    (uf : Fin S.N_id) (jf : Fin S.N_recv) (of : Fin S.N_opk)
    (hsim : Env.get env (h₁.wk sim) = fgSimToVal st)
    (hx : Env.get env (h₂.wk x) = (uf.val, (jf.val, of.val))) (hB : AgBnd K st) :
    (onBaseF sim fun g => genOpkB K g x).eval env =
      (fun r => (authRespToVal r.1, fgSimToVal r.2)) <$>
        fgAuthStep useDh1 t sIdx S K U V (.genOPK uf jf of) st := by
  simp only [onBaseF, genOpkB, rs]
  ag_unfold
  simp only [hsim, hx, fgSimToVal, authStateToVal]
  rw [take_map_of_le _ _ hB.base.opkEntries_le]
  simp only [fgAuthStep, List.any_map, Function.comp_def, Prod.map_fst]
  have hp : (fun x : (Nat × Nat × Nat) × OpkEntry =>
      x.1.1 == (uf : Nat) && (x.1.2.1 == (jf : Nat) && x.1.2.2 == (of : Nat))) =
      (fun x => x.1 == ((uf : Nat), (jf : Nat), (of : Nat))) := funext fun _ => rfl
  rw [hp]
  cases ha : st.base.opkEntries.any (fun x => x.1 == ((uf : Nat), (jf : Nat), (of : Nat)))
  · simp only [Bool.false_eq_true, ↓reduceIte, embedPrim_bind, embedPrim_pure, bind_assoc,
      pure_bind, map_bind, map_pure]
    rfl
  · simp only [↓reduceIte, embedPrim_pure, pure_bind, map_pure]; rfl

theorem fgRoRootC_eval (sim : Var Γ₁ fgSimTy) (x : Var Γ₂ (.prod (B 32) (B 32))) (rk dh : Bytes)
    (hsim : Env.get env (h₁.wk sim) = fgSimToVal st)
    (hx : Env.get env (h₂.wk x) = (rk, dh)) :
    (fgRoRootC K sim x).eval env =
      (fun r => (authRespToVal r.1, fgSimToVal r.2)) <$>
        fgAuthStep useDh1 t sIdx S K U V (.roRootQuery rk dh) st := by
  simp only [fgRoRootC, bindV, v, Comp.eval, mkSecretPosC_eval, rootPatchC_eval]
  simp only [Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, hsim, hx, fgSimToVal]
  rw [agList_rootEntry_roundtrip']
  simp only [fgAuthStep, fgRoRootQueryAuthGdh, bind_map_left, map_bind, map_pure]
  refine bind_congr' rfl (fun p => ?_)
  rw [valToFgPos_fgPosToVal]
  refine bind_congr' rfl (fun a => ?_)
  rfl

theorem fgRegisterC_eval (sim : Var Γ₁ fgSimTy) (sk : Var Γ₂ (B 32)) (skv : Bytes)
    (hsim : Env.get env (h₁.wk sim) = fgSimToVal st)
    (hsk : Env.get env (h₂.wk sk) = skv) :
    (fgRegisterC sim sk).eval env =
      (fun r => (authRespToVal r.1, fgSimToVal r.2)) <$>
        fgAuthStep useDh1 t sIdx S K U V (.registerKey skv) st := by
  subst hsk
  simp only [fgRegisterC]
  ag_unfold
  simp only [hsim, fgSimToVal, authStateToVal, fgAuthStep]
  split
  · rename_i hc
    simp only [bne, hc, ↓reduceIte, map_pure]; rfl
  · rename_i hc
    simp only [bne, hc, Bool.false_eq_true, ↓reduceIte, map_bind, map_pure]; rfl

theorem fg2InitPrinC_eval (pa : Var Γ₁ fg2ParamsTy) (sim : Var Γ₂ fgSimTy) (u : Var Γ₃ .nat)
    (uf : Fin S.N_id)
    (hpa : Env.get env (h₁.wk pa) = fg2PaVal S U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st)
    (hu : Env.get env (h₃.wk u) = uf.val) (hB : AgBnd K st) :
    (fg2InitPrinC K pa sim u).eval env =
      (fun r => (authRespToVal r.1, fgSimToVal r.2)) <$>
        fgAuthStep useDh1 t sIdx S K U V (.initPrin uf) st := by
  simp only [fg2InitPrinC]
  ag_unfold
  simp only [hpa, hsim, hu, fgSimToVal, fg2PaVal, authStateToVal]
  rw [take_map_of_le _ _ hB.base.principals_le]
  simp only [fgAuthStep, List.any_map, Function.comp_def, Prod.map_fst, id_eq]
  cases ha : st.base.principals.any (fun x => x.1 == (uf : Nat))
  · simp only [Bool.false_eq_true, ↓reduceIte, map_bind, map_pure]
    have hdh := paTargetChoice_dh1 S useDh1 t
    have hcond : ((paTargetChoice S useDh1 t).1 && ((uf : Nat) == (paTargetChoice S useDh1 t).2.1)) =
        (useDh1 && ((uf : Nat) == t)) := by
      rcases hdh with ⟨h1, h2⟩
      rw [h1]
      cases useDh1
      · rfl
      · rw [h2 rfl]
    rw [hcond]
    cases hb : (useDh1 && (uf : Nat) == t) <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;> rfl
  · simp only [↓reduceIte, map_pure]; rfl

theorem fg2GenSpkC_eval (pa : Var Γ₁ fg2ParamsTy) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ (.prod .nat .nat))
    (uf : Fin S.N_id) (jf : Fin S.N_recv)
    (hpa : Env.get env (h₁.wk pa) = fg2PaVal S U V useDh1 t sIdx)
    (hsim : Env.get env (h₂.wk sim) = fgSimToVal st)
    (hx : Env.get env (h₃.wk x) = (uf.val, jf.val)) (hB : AgBnd K st) :
    (fg2GenSpkC K pa sim x).eval env =
      (fun r => (authRespToVal r.1, fgSimToVal r.2)) <$>
        fgAuthStep useDh1 t sIdx S K U V (.genSPK uf jf) st := by
  simp only [fg2GenSpkC]
  ag_unfold
  simp only [hpa, hsim, hx, fgSimToVal, fg2PaVal, authStateToVal]
  rw [take_map_of_le _ _ hB.base.spkBundles_le, take_map_of_le _ _ hB.base.principals_le]
  simp only [fgAuthStep, List.any_map, List.find?_map, Function.comp_def, Prod.map_fst, id_eq]
  have hp : (fun x : (Nat × Nat) × SpkBundleEntry => x.1.1 == (uf : Nat) && x.1.2 == (jf : Nat)) =
      (fun x => x.1 == ((uf : Nat), (jf : Nat))) := funext fun _ => rfl
  rw [hp]
  cases ha : st.base.spkBundles.any (fun x => x.1 == ((uf : Nat), (jf : Nat)))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases hf : List.find? (fun x => x.1 == (uf : Nat)) st.base.principals with _ | ⟨i, e⟩
    · simp only [hf, Option.map_none, map_pure]; rfl
    · simp only [hf, Option.map_some, map_bind, map_pure]
      rw [hx, hpa]
      simp only [fg2PaVal]
      have hts := paSpkOpt_beq S sIdx uf jf
      refine bind_congr' rfl fun x => bind_congr' rfl fun x_1 => bind_congr' rfl fun x_2 => ?_
      have hSig {sk1 sk2 m1 m2 r : Bytes} (hsk : sk1 = sk2) (hm : m1 = m2) :
          (query (spec := PrimBaseSpec + gapDhOracleSpec)
            (Sum.inl (Sum.inr (PrimQuery.sigSign sk1 m1 r))) :
            OracleComp _ Bytes) =
          FgGapDh.primGdhQ (.sigSign sk2 m2 r) := by
        subst hsk hm; rfl
      refine bind_congr' (hSig rfl ?_) fun x_3 => ?_
      · congr 1
        by_cases hs : sIdx < S.N_spk_tot <;>
          simp only [paSpkOpt, FgGapDh.spkBundleFlatIdx, hs, ↓reduceIte] at hts ⊢ <;>
          simp only [hts] <;> rfl
      · by_cases hs : sIdx < S.N_spk_tot <;>
          simp only [paSpkOpt, FgGapDh.spkBundleFlatIdx, hs, ↓reduceIte] at hts ⊢ <;>
          simp only [hts] <;> rfl
  · simp only [↓reduceIte, map_pure]; rfl

end Small

end SignalPqxdh.Security.ReductionDsl.AuthHs
