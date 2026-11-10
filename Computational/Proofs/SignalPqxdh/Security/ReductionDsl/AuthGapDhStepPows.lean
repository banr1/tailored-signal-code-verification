/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSim
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeGapDh
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSimSend
import VCVio.EvalDist.Monad.Basic

/-!
# `advKeyPows` helper evaluation for the `Auth` Gap-DH DSL

Proves evaluation equivalence for `advKeyPows`-backed KOSK and SPK lookups and defines the
scan-bound invariant `AgBnd`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

theorem agFindMPrim_eq {α : Type} (p : α → OracleComp PrimBaseSpec Bool) (L : List α) :
    FgGapDh.findMPrim p L = SignalPqxdh.Security.findMPrim p L := by
  induction L with
  | nil => rfl
  | cons x xs ih => simp only [FgGapDh.findMPrim, SignalPqxdh.Security.findMPrim, ih]

theorem agAnyMPrim_eq {α : Type} (p : α → OracleComp PrimBaseSpec Bool) (L : List α) :
    FgGapDh.anyMPrim p L = SignalPqxdh.Security.anyMPrim p L := by
  induction L with
  | nil => rfl
  | cons x xs ih => simp only [FgGapDh.anyMPrim, SignalPqxdh.Security.anyMPrim, ih]

theorem agFindHonest_eq (S : Setup) (P : List (Nat × PrincipalEntry)) (ik : Bytes) :
    FgGapDh.findHonestPrincipalPrim S P ik =
      SignalPqxdh.Security.findHonestPrincipalPrim S P ik := by
  simp only [FgGapDh.findHonestPrincipalPrim, agFindMPrim_eq]
  rfl

theorem agResolveSigPk_eq (S : Setup) (P : List (Nat × PrincipalEntry)) (ik : Bytes) :
    FgGapDh.resolveSigPkPrim S P ik = SignalPqxdh.Security.resolveSigPkPrim S P ik := by
  simp only [FgGapDh.resolveSigPkPrim, agFindHonest_eq]
  rfl

theorem agIsGameSpk_eq (S : Setup) (L : List ((Nat × Nat) × SpkBundleEntry)) (pk : Bytes) :
    FgGapDh.isGameSpkPrim S L pk = SignalPqxdh.Security.isGameSpkPrim S L pk := by
  simp only [FgGapDh.isGameSpkPrim, agAnyMPrim_eq]
  rfl

theorem agIsGameOpk_eq (S : Setup) (L : List ((Nat × Nat × Nat) × OpkEntry)) (pk : Bytes) :
    FgGapDh.isGameOpkPrim S L pk = SignalPqxdh.Security.isGameOpkPrim S L pk := by
  simp only [FgGapDh.isGameOpkPrim, agAnyMPrim_eq]
  rfl

theorem agPow8_congr {a b : Bytes} (h : a = b) :
    FgGapDh.primQ (.pow8 a) = FgGapDh.primQ (.pow8 b) := by
  subst h; rfl

section PowsEval

variable (S : Setup) (K : Nat) {Γ Γ₂ Γ₃ Δ : List (Ty pqSig)} {h : Ext Γ Δ} {h₂ : Ext Γ₂ Δ}
  {h₃ : Ext Γ₃ Δ} (env : Env Δ) (s : AuthState S) (st : Var Γ authStateTy)
  (P : List (Bytes × Bytes)) (pows : Var Γ₂ (.list (.prod (B 32) (B 32))))

theorem isAdvPowsC_eval (hp : Env.get env (h₂.wk pows) = P) (hK : P.length ≤ K)
    (pk : Expr pqxdhOps Δ (B 32)) :
    (isAdvPowsC K pows pk).eval env =
      (FgGapDh.primQ (.pow8 (pk.eval env)) >>= fun w =>
        pure (FgGapDh.isAdvRegisteredPows P w)) := by
  simp only [isAdvPowsC, bindV, v, eAny, eval_queryPrim, Comp.eval, Expr.eval_bytesBeq, Expr.eval,
    Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, hp, List.take_of_length_le hK,
    PTag.dec_pow8, SignalPqxdh.LegacyCosted.PTag.enc, id_map]
  rfl

theorem koskSenderOkPowsC_eval (hst : Env.get env (h.wk st) = authStateToVal s)
    (hp : Env.get env (h₂.wk pows) = P) (hK : P.length ≤ K) (ik : Expr pqxdhOps Δ (B 32))
    (hBs : AuthBaseListsBounded K s) :
    (koskSenderOkPowsC S K st pows ik).eval env =
      FgGapDh.koskSenderOkPrim S s.principals P (ik.eval env) := by
  simp only [koskSenderOkPowsC, letV, bindV, v, Comp.eval_letC, Comp.eval, Expr.eval, Env.get_vz,
    Ext.step_wk, Ext.refl_wk]
  rw [findHonestC_eval S _ s st (by simpa using hst) _ hBs.principals_le]
  simp only [FgGapDh.koskSenderOkPrim, agFindHonest_eq, bind_map_left]
  refine congrArg (fun k => _ >>= k) (funext fun r => ?_)
  rw [isAdvPowsC_eval K _ P pows (by simpa using hp) hK]
  simp only [Expr.eval, bind_assoc, pure_bind, isSomeE]
  cases r <;> rfl

theorem koskBundleOkPowsC_eval (hst : Env.get env (h.wk st) = authStateToVal s)
    (hp : Env.get env (h₂.wk pows) = P) (hK : P.length ≤ K) (bu : Var Γ₃ preKeyBundleTy)
    (b : PreKeyBundleInput) (hbu : Env.get env (h₃.wk bu) = preKeyBundleToVal b)
    (hBs : AuthBaseListsBounded K s) :
    (koskBundleOkPowsC S K st pows bu).eval env =
      FgGapDh.koskBundleOkPrim S s.principals s.spkBundles s.opkEntries P b := by
  simp only [koskBundleOkPowsC, bindV, caseOptV, v, Comp.eval]
  rw [findHonestC_eval S _ s st hst _ hBs.principals_le]
  simp only [FgGapDh.koskBundleOkPrim, agFindHonest_eq, agIsGameSpk_eq, agIsGameOpk_eq,
    bind_map_left, pure_bind]
  refine bind_congr' (by simp [Expr.eval, hbu]) (fun r => ?_)
  rw [isAdvPowsC_eval K _ P pows (by simpa using hp) hK]
  simp only [bind_assoc, pure_bind]
  refine bind_congr' (by simp [Expr.eval]; exact agPow8_congr (by rw [hbu]; rfl)) (fun w1 => ?_)
  rw [isGameSpkC_eval S _ s st (by simpa using hst) _ hBs.spkBundles_le]
  refine bind_congr' (by simp [Expr.eval, hbu]) (fun spkG => ?_)
  rw [isAdvPowsC_eval K _ P pows (by simpa using hp) hK]
  simp only [bind_assoc, pure_bind]
  refine bind_congr' (by simp [Expr.eval]; exact agPow8_congr (by rw [hbu]; rfl)) (fun w2 => ?_)
  simp only [Expr.eval, Ext.step_wk, Env.get_vs, hbu, preKeyBundleToVal, bundleV]
  rcases hb : b.opkB? with _ | ⟨oid, opk⟩
  · simp only [Expr.eval, isSomeE, Ext.refl_wk, Env.get_vs, Env.get_vz]
    cases r <;> cases spkG <;> rfl
  · simp only
    rw [isGameOpkC_eval S _ s st (by simpa using hst) _ hBs.opkEntries_le]
    refine bind_congr' (by simp [Expr.eval]) (fun opkG => ?_)
    rw [isAdvPowsC_eval K _ P pows (by simpa using hp) hK]
    simp only [bind_assoc, pure_bind]
    refine bind_congr' (by simp [Expr.eval]) (fun w3 => ?_)
    simp only [Expr.eval, isSomeE, Ext.refl_wk, Env.get_vs, Env.get_vz]
    cases r <;> cases spkG <;> cases opkG <;> rfl

theorem lookupSpkSkC_eval (hst : Env.get env (h.wk st) = authStateToVal s)
    (hp : Env.get env (h₂.wk pows) = P) (hK : P.length ≤ K) (pk : Expr pqxdhOps Δ (B 32))
    (hSpk : s.spkBundles.length ≤ K) :
    (lookupSpkSkC S K st pows pk).eval env =
      FgGapDh.lookupSpkSkPrim S s.spkBundles P (pk.eval env) := by
  simp only [lookupSpkSkC, bindV, findMV, v, eCaseOpt, eFind, eval_queryPrim, Comp.eval,
    Expr.eval_bytesBeq, Expr.eval_litBytes, Expr.eval, Ext.step_wk, Ext.refl_wk,
    Env.get_vs, Env.get_vz, hst, hp, authStateToVal, stSpks, sbSpkPk, sbSpkSk,
    findML_eq_findMPrim, PTag.dec_pow8, SignalPqxdh.LegacyCosted.PTag.enc, id_map, FgGapDh.lookupSpkSkPrim,
    agFindMPrim_eq, List.take_of_length_le hK, take_min_map_of_le _ _ hSpk]
  refine congrArg (fun k => _ >>= k) (funext fun w => ?_)
  rw [← List.map_take]
  erw [findMPrim_map]
  simp only [bind_map_left]
  refine bind_congr' rfl (fun f => ?_)
  rcases f with _ | ⟨i, e⟩
  · simp only [Option.map_none]
    rcases hf : List.find? (fun x => x.2 == w) P with _ | ⟨a, c⟩ <;> simp only [hf]
  · rfl

end PowsEval

/-- All lists read by a bounded DSL scan are within the scan bound `K`. -/
structure AgBnd {S : Setup} (K : Nat) (st : FgAuthSimState S) : Prop where
  base    : AuthBaseListsBounded K st.base
  raw_le  : st.rawRoCache.length ≤ K
  pows_le : st.advKeyPows.length ≤ K

end SignalPqxdh.Security.ReductionDsl.AuthHs
