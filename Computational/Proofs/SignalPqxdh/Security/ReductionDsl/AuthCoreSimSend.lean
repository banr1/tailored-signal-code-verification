/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSim
import VCVio.EvalDist.Monad.Basic

/-!
# Send-branch evaluation equivalence for the `Auth` DSL

Proves that `sendB` evaluates to the shallow `pqxdhAuthSimImplPrim` send branches under
`authRespToVal`, `authStateToVal`, and `AuthBaseListsBounded`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

section HelperEval

variable (S : Setup) (K : Nat) {Γ Γ₂ Δ : List (Ty pqSig)} {h : Ext Γ Δ} {h₂ : Ext Γ₂ Δ}
  (env : Env Δ) (s : AuthState S) (st : Var Γ authStateTy)

theorem take_min_of_le {α : Type} {K N : Nat} (l : List α) (hl : l.length ≤ K) :
    l.take (min K N) = l.take N := by
  rw [← List.take_take]
  exact List.take_of_length_le (by simp only [List.length_take]; omega)

theorem take_min_map_of_le {α β : Type} {K N : Nat} (f : α → β) (l : List α)
    (hl : l.length ≤ K) : (l.map f).take (min K N) = (l.map f).take N :=
  take_min_of_le _ (by simpa using hl)

variable {K} in
theorem findHonestC_eval (hst : Env.get env (h.wk st) = authStateToVal s)
    (ik : Expr pqxdhOps Δ (B 32)) (hPrin : s.principals.length ≤ K) :
    (findHonestC S K st ik).eval env =
      Option.map (Prod.map id principalEntryToVal) <$>
        findHonestPrincipalPrim S s.principals (ik.eval env) := by
  simp only [findHonestC, findMV, letV, bindV, v, Comp.eval_letC,
    eval_queryPrim, Comp.eval, Expr.eval_bytesBeq, Expr.eval,
    Ext.step_wk, Env.get_vs, hst, authStateToVal, findML_eq_findMPrim,
    PTag.dec_pow8, SignalPqxdh.LegacyCosted.PTag.enc, id_map]
  rw [take_min_map_of_le _ _ hPrin, ← List.map_take, findMPrim_map]
  rfl

macro "help_unfold" h:term : tactic => `(tactic| simp only [$h:term, findHonestC, isAdvRegC,
  isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC, resolveSigPkC, honestPeerC, hkdfOrRoC,
  rootRoC, findMV, anyMV, letV, bindV, caseOptV, v, eFind, eAny, eCaseOpt, isSomeE, bytes2Eq,
  stPrin, stSpks, stOpks, stAdv, stRo, stRoot, sbSpkPk, oeOpkPk, peIkAPk, peIkSignPk, peCorrupted,
  buIkB, buSpkB, buOpkB,
  Comp.eval_letC, eval_sampleBool, eval_sampleBytes32, eval_sampleRandom64,
  eval_sampleDrKey96, eval_sampleIndex, eval_queryPrim, Comp.eval,
  Expr.eval_litBytes, Expr.eval_bytesAppend, Expr.eval_bytesCons, Expr.eval_bytesWiden,
  Expr.eval_bytesTakeK, Expr.eval_bytesDrop, Expr.eval_bytesLen,
  Expr.eval_bytesBeq, Expr.eval_bytesVarint, Expr.eval_u32OfNat,
  Expr.eval_u32Beq,
  Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
  pqPrimIface_liftP, pqPrimIface_smp, pqPrimIface_dec, pqPrimIface_enc_query,
  pqSamplers_run, PSamp.run, embedUnif_drKey96, embedUnif_msgKeys80,
  PTag.dec_x25519, PTag.dec_x25519Base, PTag.dec_isCanonical, PTag.dec_pow8, PTag.dec_sigPkGen,
  PTag.dec_sigSign, PTag.dec_sigVerify, PTag.dec_kemKeyGen, PTag.dec_kemEncaps, PTag.dec_kemDecaps,
  PTag.dec_hkdfDerive96, PTag.dec_rootCreateChain, PTag.dec_chainKdfSeed, PTag.dec_chainKdfNext,
  PTag.dec_deriveMsgKeys, PTag.dec_spqrInitSend, PTag.dec_spqrInitRecv, PTag.dec_aeadEnc,
  PTag.dec_aeadDec, SignalPqxdh.LegacyCosted.PTag.dec, SignalPqxdh.LegacyCosted.PTag.enc, id_map, id_map',
  authStateToVal, findML_eq_findMPrim, anyML_eq_anyMPrim, ite_true, ↓reduceIte])

theorem isAdvRegC_eval (hst : Env.get env (h.wk st) = authStateToVal s)
    (hK : s.advKeys.length ≤ K) (pk : Expr pqxdhOps Δ (B 32)) :
    (isAdvRegC K st pk).eval env = isAdvRegisteredPrim s.advKeys (pk.eval env) := by
  help_unfold hst
  rw [List.take_of_length_le hK]
  rfl

variable {K} in
theorem isGameSpkC_eval (hst : Env.get env (h.wk st) = authStateToVal s)
    (pk : Expr pqxdhOps Δ (B 32)) (hSpk : s.spkBundles.length ≤ K) :
    (isGameSpkC S K st pk).eval env = isGameSpkPrim S s.spkBundles (pk.eval env) := by
  help_unfold hst
  rw [take_min_map_of_le _ _ hSpk, ← List.map_take, anyMPrim_map]
  rfl

variable {K} in
theorem isGameOpkC_eval (hst : Env.get env (h.wk st) = authStateToVal s)
    (pk : Expr pqxdhOps Δ (B 32)) (hOpk : s.opkEntries.length ≤ K) :
    (isGameOpkC S K st pk).eval env = isGameOpkPrim S s.opkEntries (pk.eval env) := by
  help_unfold hst
  rw [take_min_map_of_le _ _ hOpk, ← List.map_take, anyMPrim_map]
  rfl

theorem koskSenderOkC_eval (hst : Env.get env (h.wk st) = authStateToVal s)
    (hK : s.advKeys.length ≤ K) (ik : Expr pqxdhOps Δ (B 32))
    (hPrin : s.principals.length ≤ K) :
    (koskSenderOkC S K st ik).eval env =
      koskSenderOkPrim S s.principals s.advKeys (ik.eval env) := by
  simp only [koskSenderOkC, letV, bindV, v, Comp.eval_letC, Comp.eval, Expr.eval, Env.get_vz,
    Ext.step_wk, Ext.refl_wk, ite_true_eq_or]
  rw [findHonestC_eval S _ s st (by simpa using hst) _ hPrin]
  simp only [koskSenderOkPrim, isGameIdKeyPrim, bind_map_left, bind_assoc, pure_bind]
  congr 1; funext r
  rw [isAdvRegC_eval S K _ s st (by simpa using hst) hK]
  cases r <;> rfl

variable {K} in
theorem resolveSigPkC_eval (hst : Env.get env (h.wk st) = authStateToVal s)
    (ik : Expr pqxdhOps Δ (B 32)) (hPrin : s.principals.length ≤ K) :
    (resolveSigPkC S K st ik).eval env = resolveSigPkPrim S s.principals (ik.eval env) := by
  simp only [resolveSigPkC, letV, bindV, v, Comp.eval_letC, Comp.eval,
    Ext.step_wk, Ext.refl_wk]
  rw [findHonestC_eval S _ s st (by simpa using hst) _ hPrin]
  simp only [resolveSigPkPrim, bind_map_left]
  congr 1; funext r
  rcases r with _ | ⟨_, _⟩ <;> rfl

theorem hkdfOrRoC_eval (hst : Env.get env (h.wk st) = authStateToVal s)
    (hK : s.roCache.length ≤ K) (sec : Expr pqxdhOps Δ (B 192)) :
    (hkdfOrRoC K true st sec).eval env =
      Prod.map drKeyToVal (List.map (Prod.map id drKeyToVal)) <$>
        evalHkdfOrRoPrim true s.roCache (sec.eval env) := by
  help_unfold hst
  rw [List.take_of_length_le (by simpa using hK)]
  simp only [evalHkdfOrRoPrim, List.find?_map, Function.comp_def]
  rcases hf : List.find? (fun x => x.1 == sec.eval env) s.roCache with _ | ⟨i, e⟩
  · simp [hf]
  · simp [hf]

theorem rootRoC_eval (hst : Env.get env (h.wk st) = authStateToVal s)
    (hK : s.rootRoCache.length ≤ K) (rk dh : Expr pqxdhOps Δ (B 32)) :
    (rootRoC K st rk dh).eval env =
      evalRootKdfOrRoPrim true s.rootRoCache (rk.eval env) (dh.eval env) := by
  help_unfold hst
  rw [List.take_of_length_le (by simpa using hK)]
  simp only [evalRootKdfOrRoPrim]
  rcases hf : List.find? (fun x => x.1.1 == rk.eval env && x.1.2 == dh.eval env) s.rootRoCache
    with _ | ⟨i, e⟩
  · simp [hf]
  · simp [hf]

theorem bind_congr' {m : Type → Type} [Monad m] {α β : Type} {x y : m α} {f g : α → m β}
    (hxy : x = y) (hfg : ∀ a, f a = g a) : x >>= f = y >>= g := by
  subst hxy; exact congrArg _ (funext hfg)

theorem koskBundleOkC_eval (hst : Env.get env (h.wk st) = authStateToVal s)
    (hK : s.advKeys.length ≤ K) (bu : Var Γ₂ preKeyBundleTy) (b : PreKeyBundleInput)
    (hbu : Env.get env (h₂.wk bu) = preKeyBundleToVal b) (hPrin : s.principals.length ≤ K)
    (hSpk : s.spkBundles.length ≤ K) (hOpk : s.opkEntries.length ≤ K) :
    (koskBundleOkC S K st bu).eval env =
      koskBundleOkPrim S s.principals s.spkBundles s.opkEntries s.advKeys b := by
  simp only [koskBundleOkC, bindV, caseOptV, v, Comp.eval]
  rw [findHonestC_eval S _ s st hst _ hPrin]
  simp only [Expr.eval, buIkB, buSpkB, Ext.step_wk, Env.get_vs, hbu,
    preKeyBundleToVal, bundleV]
  simp only [koskBundleOkPrim, isGameIdKeyPrim, bind_map_left, bind_assoc, pure_bind]
  refine bind_congr' (by simp []) (fun r => ?_)
  rw [isAdvRegC_eval S K _ s st (by simpa using hst) hK]
  refine bind_congr' (by simp [Expr.eval, hbu]) (fun idA => ?_)
  rw [isGameSpkC_eval S _ s st (by simpa using hst) _ hSpk]
  refine bind_congr' (by simp [Expr.eval, hbu]) (fun spkG => ?_)
  rw [isAdvRegC_eval S K _ s st (by simpa using hst) hK]
  refine bind_congr' (by simp [Expr.eval, hbu]) (fun spkA => ?_)
  try simp only [Expr.eval, buIkB, buSpkB, buOpkB, Ext.step_wk, Env.get_vs, Env.get_vz, hbu,
    preKeyBundleToVal, bundleV]
  rcases hb : b.opkB? with _ | ⟨oid, opk⟩
  · simp only [Expr.eval, isSomeE, Ext.refl_wk, Env.get_vs, Env.get_vz]
    cases r <;> cases spkG <;> rfl
  · simp only []
    rw [isGameOpkC_eval S _ s st (by simpa using hst) _ hOpk]
    refine bind_congr' (by simp [Expr.eval]) (fun opkG => ?_)
    rw [isAdvRegC_eval S K _ s st (by simpa using hst) hK]
    refine bind_congr' (by simp [Expr.eval]) (fun opkA => ?_)
    simp only [Expr.eval, isSomeE, Ext.refl_wk, Env.get_vs, Env.get_vz]
    cases r <;> cases spkG <;> cases opkG <;> rfl

theorem koskBundleOkC_eval' (hst : Env.get env (h.wk st) = authStateToVal s)
    (hK : s.advKeys.length ≤ K) (bu : Var Γ₂ preKeyBundleTy) (hPrin : s.principals.length ≤ K)
    (hSpk : s.spkBundles.length ≤ K) (hOpk : s.opkEntries.length ≤ K) :
    (koskBundleOkC S K st bu).eval env =
      koskBundleOkPrim S s.principals s.spkBundles s.opkEntries s.advKeys
        (valToPreKeyBundle (Env.get env (h₂.wk bu))) :=
  koskBundleOkC_eval S K env s st hst hK bu _ rfl hPrin hSpk hOpk

theorem preKeyBundle_mk_eta (b : PreKeyBundleInput) :
    (⟨b.ikB, b.spkId, b.spkB, b.spkSig, b.opkB?, b.pqspkId, b.pqspkB, b.pqspkSig⟩ :
      PreKeyBundleInput) = b := rfl

theorem take_map_of_le {α β : Type} {K : Nat} (f : α → β) (l : List α) (h : l.length ≤ K) :
    List.take K (List.map f l) = List.map f l := List.take_of_length_le (by simpa using h)

theorem any_sid_iff {S : Setup} (l : List (SessionId S)) (P : sessionIdTy.denote → Bool)
    (sid : SessionId S) (hP : ∀ x, P (sessionIdToVal x) = (sid == x)) :
    (l.map sessionIdToVal).any P = l.contains sid := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.any_cons, hP, ih, List.contains_cons]

theorem stRun_ite {σ α : Type} {m : Type → Type} [Monad m] {c : Prop} [Decidable c]
    (x y : StateT σ m α) (s : σ) :
    (if c then x else y).run s = if c then x.run s else y.run s := by split <;> rfl

theorem map_ite' {α β : Type} {m : Type → Type} [Functor m] (f : α → β) {c : Prop} [Decidable c]
    (x y : m α) : f <$> (if c then x else y) = if c then f <$> x else f <$> y := by split <;> rfl

end HelperEval

section ElimEval

variable {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}

theorem Comp.eval_caseOptC_elim {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Comp pqxdhOps I Γ τ₂)
    (ks : Comp pqxdhOps I (τ₁ :: Γ) τ₂) (env : Env Γ) :
    (Comp.caseOptC o kn ks).eval env =
      Option.elim (o.eval env) (kn.eval env) (fun a => ks.eval (.cons a env)) := by
  simp only [Comp.eval]; cases o.eval env <;> rfl

theorem Comp.eval_caseSumC_elim {Γ : List (Ty pqSig)} {τ₁ τ₂ τ : Ty pqSig}
    (o : Expr pqxdhOps Γ (.sum τ₁ τ₂)) (kl : Comp pqxdhOps I (τ₁ :: Γ) τ)
    (kr : Comp pqxdhOps I (τ₂ :: Γ) τ) (env : Env Γ) :
    (Comp.caseSumC o kl kr).eval env =
      Sum.elim (fun a => kl.eval (.cons a env))
        (fun a => kr.eval (.cons a env)) (o.eval env) := by
  simp only [Comp.eval]; cases o.eval env <;> rfl

theorem Expr.eval_caseOpt_elim {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Expr pqxdhOps Γ τ₂)
    (ks : Expr pqxdhOps (τ₁ :: Γ) τ₂) (env : Env Γ) :
    (Expr.caseOpt o kn ks).eval env =
      Option.elim (o.eval env) (kn.eval env) (fun a => ks.eval (.cons a env)) := by
  simp only [Expr.eval]; cases o.eval env <;> rfl

theorem Expr.eval_caseSum_elim {Γ : List (Ty pqSig)} {τ₁ τ₂ τ : Ty pqSig}
    (o : Expr pqxdhOps Γ (.sum τ₁ τ₂)) (kl : Expr pqxdhOps (τ₁ :: Γ) τ)
    (kr : Expr pqxdhOps (τ₂ :: Γ) τ) (env : Env Γ) :
    (Expr.caseSum o kl kr).eval env =
      Sum.elim (fun a => kl.eval (.cons a env))
        (fun a => kr.eval (.cons a env)) (o.eval env) := by
  simp only [Expr.eval]; cases o.eval env <;> rfl

end ElimEval

macro "send_unfold" : tactic => `(tactic| simp only [
  v, bindV, letV, caseOptV, caseSumV, findMV, anyMV, eLet, eLet2, eCaseOpt, eCaseSum, eFind, eAny,
  eMap, eval_natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32,
  buildSecretsE_eval, encEC_eval, encKEM_eval,
  stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN,
  stKyb, stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd, seSid, sePeerIk, sePeerSpk,
  sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon, sePqspkHon, seEkASk, seEphASk, seFresh, seChal, seMk,
  pmHdr, pmEphAPk, pmPqMsg, pmAeadCt, pmMk, pmUpd, peSecIKA0, peIkAPk, peSecIKAsign,
  peIkSignPk, peCorrupted, peMk, peUpd, sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk,
  sbPqspkSig, sbRevealed, sbMk, oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd, buIkB, buSpkId,
  buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk, buUpd, hdIkAPk, hdEkAPk,
  hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk, hdUpd, isSomeE, getDBytes, optFst, optSnd, dhOptNZ,
  guardE, kyberCheckE, aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh,
  aRecvHonest, aRecvUnfresh, aDrKey, aRootKdf, rs, firstMsgADE_evalHs, bytes2Eq, emptyAuthStE,
  sendC, sendB, recvTailC, recvB,
  Comp.eval_caseOptC_elim, Comp.eval_caseSumC_elim, Expr.eval_caseOpt_elim, Expr.eval_caseSum_elim,
  Comp.eval_letC, eval_sampleBool, eval_sampleBytes32, eval_sampleRandom64,
  eval_sampleDrKey96, eval_sampleIndex, eval_queryPrim, Comp.eval,
  Expr.eval_litBytes, Expr.eval_bytesAppend, Expr.eval_bytesCons, Expr.eval_bytesWiden,
  Expr.eval_bytesTakeK, Expr.eval_bytesDrop, Expr.eval_bytesLen,
  Expr.eval_bytesBeq, Expr.eval_bytesVarint, Expr.eval_u32OfNat,
  Expr.eval_u32Beq,
  Expr.eval, ite_ty_bool_true_eq_or, ite_true_eq_or, ite_ty_bool_not_eq_beq, ite_not_eq_beq,
  Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
  pqPrimIface_liftP, pqPrimIface_smp, pqPrimIface_dec, pqPrimIface_enc_query,
  pqSamplers_run, PSamp.run, embedUnif_drKey96, embedUnif_msgKeys80,
  PTag.dec_x25519, PTag.dec_x25519Base, PTag.dec_isCanonical, PTag.dec_pow8, PTag.dec_sigPkGen,
  PTag.dec_sigSign, PTag.dec_sigVerify, PTag.dec_kemKeyGen, PTag.dec_kemEncaps, PTag.dec_kemDecaps,
  PTag.dec_hkdfDerive96, PTag.dec_rootCreateChain, PTag.dec_chainKdfSeed, PTag.dec_chainKdfNext,
  PTag.dec_deriveMsgKeys, PTag.dec_spqrInitSend, PTag.dec_spqrInitRecv, PTag.dec_aeadEnc,
  PTag.dec_aeadDec, SignalPqxdh.LegacyCosted.PTag.dec, SignalPqxdh.LegacyCosted.PTag.enc, id_map, id_map',
  findML_eq_findMPrim, anyML_eq_anyMPrim, mapML_eq_mapMPrim,
  consumeFirstML_eq_consumeFirstMPrim,
  decide_ty_nat_eq_beq, decide_nat_eq_beq,
  ite_true, ite_false, ↓reduceIte, Bool.false_eq_true])

macro "peel" : tactic => `(tactic| refine bind_congr' rfl (fun _ => ?_))
macro "noneclose" : tactic => `(tactic| first | rfl | simp [authStateToVal])
macro "send_prefix" : tactic => `(tactic| (
  refine bind_congr' rfl (fun v => ?_)
  by_cases hv : v = false
  · rw [ite_eq_left hv, ite_eq_left hv]; noneclose
  rw [ite_eq_right hv, ite_eq_right hv]
  peel; peel; peel; peel; peel
  refine bind_congr' rfl (fun v5 => ?_)
  refine bind_congr' rfl (fun v6 => ?_)
  by_cases hv' : v5 = false ∨ v6 = false
  · rw [ite_eq_left hv', ite_eq_left hv']; noneclose
  rw [ite_eq_right hv', ite_eq_right hv']
  refine bind_congr' rfl (fun v7 => ?_)
  rcases v7 with _ | ⟨ss, kemCt⟩
  · noneclose
  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, map_bind, bind_assoc]))

macro "send_mid" : tactic => `(tactic| (
  simp only [pure_bind]
  peel; peel; peel; peel; peel
  refine bind_congr' (by simp only [buildSecrets, List.append_assoc]) (fun _ => ?_)
  peel; peel; peel; peel; peel; peel
  rename_i spq
  rcases spq with _ | ⟨pqst, salt, pqmsg⟩
  · noneclose
  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, map_bind, bind_assoc,
    StateT.run_set, StateT.run_pure, pure_bind]
  peel))

theorem primQ_aeadEnc_congr {mk mk' : MessageKeys} {ad ad' pt pt' : Bytes}
    (h1 : mk = mk') (h2 : ad = ad') (h3 : pt = pt') :
    primQ (.aeadEnc mk ad pt) = primQ (.aeadEnc mk' ad' pt') := by
  subst h1 h2 h3; rfl

section SendEval

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
  (env : Env Δ) (s : AuthState S)

set_option maxHeartbeats 2000000 in
theorem sendB_eval_opk (st : Var Γ₁ authStateTy) (x : Var Γ₂ sendQTy) (uf : Fin S.N_id)
    (i : Fin S.N_send_opk) (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : Env.get env (h₁.wk st) = authStateToVal s)
    (hx : Env.get env (h₂.wk x) = (uf.val, (i.val, (preKeyBundleToVal b, (m0, m1)))))
    (hK : AuthBaseListsBounded K s) :
    (sendB S K true st x).eval env =
      Prod.map authRespToVal authStateToVal <$>
        (pqxdhAuthSimImplPrim S (.sendOPK uf i b m0 m1)).run s := by
  have hx' : @Env.get pqSig Δ (.prod .nat (.prod .nat (.prod preKeyBundleTy (.prod (B 32) (B 32)))))
      env
      (@Ext.wk Γ₂ Δ h₂ (.prod .nat (.prod .nat (.prod preKeyBundleTy (.prod (B 32) (B 32))))) x) =
      (uf.val, (i.val, (preKeyBundleToVal b, (m0, m1)))) := hx
  send_unfold
  simp only [hx]
  simp only [findHonestC_eval S _ s st (hPrin := hK.principals_le),
    resolveSigPkC_eval S _ s st (hPrin := hK.principals_le),
    hkdfOrRoC_eval S K _ s st (hK := hK.roCache_le),
    rootRoC_eval S K _ s st (hK := hK.rootRoCache_le),
    buildSecretsE_eval, Ext.step_wk, Env.get_vs, hst, preKeyBundleToVal, bundleV]
  simp only [authStateToVal]
  rw [hx']
  dsimp only [preKeyBundleToVal, bundleV]
  simp only [koskBundleOkC_eval' S K _ s st _ hK.advKeys_le _ hK.principals_le
    hK.spkBundles_le hK.opkEntries_le, Ext.step_wk, Ext.refl_wk, Env.get_vs,
    Env.get_vz, hst, valToPreKeyBundle, bundleOfV, preKeyBundle_mk_eta]
  simp only [Expr.eval, Env.get_vs, Env.get_vz]
  try rw [hst]
  try dsimp only [authStateToVal]
  simp only [pqxdhAuthSimImplPrim, runAuthSendSimPrim]
  simp only [take_map_of_le _ _ hK.principals_le, take_map_of_le _ _ hK.usedSendSessions_le,
    take_map_of_le _ _ hK.spkBundles_le]
  have hsecb : (Env.get env (h₁.wk st)).1 = s.secb := by rw [hst]; rfl
  try simp only [hsecb]
  try rw [hsecb]
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
    | _ => simp
  rcases hb : b.opkB? with _ | ⟨oid, opk⟩
  · simp []
  · simp only []
    by_cases hlen : m0.length = m1.length
    swap
    · simp [hlen]
    by_cases hsid : SessionId.sendOPK uf i ∈ s.usedSendSessions
    · simp [hlen, hsid]
    rcases hp : List.find? (fun x => x.1 == ↑uf) s.principals with _ | ⟨idx, uE⟩
    · simp [hlen, hsid, hp]
    simp [hlen, hsid, hp, StateT.run_bind, StateT.run_monadLift,
      StateT.run_get, liftM, monadLift_self, List.find?_map, map_bind, bind_map_left]
    refine bind_congr' rfl (fun a => ?_)
    simp only [stRun_ite, map_ite', StateT.run_bind, StateT.run_monadLift, monadLift_self,
      map_bind, StateT.run_pure, bind_assoc, pure_bind]
    rcases a with _ | ⟨k, pE⟩
    · by_cases hm : m0 = m1
      swap
      · simp [hm, authStateToVal]
      subst hm
      simp only [Option.map_none, not_true_eq_false, and_false, ↓reduceIte]
      send_prefix
      send_mid
      rw [map_eq_bind_pure_comp]
      refine bind_congr' ?_ (fun ct => ?_)
      · exact primQ_aeadEnc_congr rfl (by simp [firstMsgAD, encodeEC, pbBytesField]) (by simp [])
      simp [StateT.run_pure, authStateToVal, authSessionEntryToVal]
    · cases hc : pE.corrupted
      · simp only [Option.map_some, Prod.map, principalEntryToVal, hc, Bool.not_false]
        simp only [Bool.true_eq_false, false_and, ↓reduceIte]
        send_prefix
        send_mid
        rw [map_eq_bind_pure_comp]
        refine bind_congr' ?_ (fun ct => ?_)
        · exact primQ_aeadEnc_congr rfl
            (by simp [firstMsgAD, encodeEC, pbBytesField]) (by simp [hsecb])
        simp [StateT.run_pure, authStateToVal, authSessionEntryToVal]
        all_goals simp [Function.comp_def, spkBundleEntryToVal, bne]
      · by_cases hm : m0 = m1
        swap
        · simp [hm, hc, principalEntryToVal, authStateToVal]
        subst hm
        simp only [Option.map_some, Prod.map, principalEntryToVal, hc, Bool.not_true,
          not_true_eq_false, and_false, ↓reduceIte]
        send_prefix
        send_mid
        rw [map_eq_bind_pure_comp]
        refine bind_congr' ?_ (fun ct => ?_)
        · exact primQ_aeadEnc_congr rfl
            (by simp [firstMsgAD, encodeEC, pbBytesField]) (by simp [hsecb])
        simp [StateT.run_pure, authStateToVal, authSessionEntryToVal]
        all_goals simp [Function.comp_def, spkBundleEntryToVal]

set_option maxHeartbeats 2000000 in
theorem sendB_eval_noopk (st : Var Γ₁ authStateTy) (x : Var Γ₂ sendQTy) (uf : Fin S.N_id)
    (i : Fin S.N_send_no_opk) (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : Env.get env (h₁.wk st) = authStateToVal s)
    (hx : Env.get env (h₂.wk x) = (uf.val, (i.val, (preKeyBundleToVal b, (m0, m1)))))
    (hK : AuthBaseListsBounded K s) :
    (sendB S K false st x).eval env =
      Prod.map authRespToVal authStateToVal <$>
        (pqxdhAuthSimImplPrim S (.sendNoOPK uf i b m0 m1)).run s := by
  have hx' : @Env.get pqSig Δ (.prod .nat (.prod .nat (.prod preKeyBundleTy (.prod (B 32) (B 32)))))
      env
      (@Ext.wk Γ₂ Δ h₂ (.prod .nat (.prod .nat (.prod preKeyBundleTy (.prod (B 32) (B 32))))) x) =
      (uf.val, (i.val, (preKeyBundleToVal b, (m0, m1)))) := hx
  send_unfold
  simp only [hx]
  simp only [findHonestC_eval S _ s st (hPrin := hK.principals_le),
    resolveSigPkC_eval S _ s st (hPrin := hK.principals_le),
    hkdfOrRoC_eval S K _ s st (hK := hK.roCache_le),
    rootRoC_eval S K _ s st (hK := hK.rootRoCache_le),
    buildSecretsE_eval, Ext.step_wk, Env.get_vs, hst, preKeyBundleToVal, bundleV]
  simp only [authStateToVal]
  rw [hx']
  dsimp only [preKeyBundleToVal, bundleV]
  simp only [koskBundleOkC_eval' S K _ s st _ hK.advKeys_le _ hK.principals_le
    hK.spkBundles_le hK.opkEntries_le, Ext.step_wk, Ext.refl_wk, Env.get_vs,
    Env.get_vz, hst, valToPreKeyBundle, bundleOfV, preKeyBundle_mk_eta]
  simp only [Expr.eval, Env.get_vs, Env.get_vz]
  try rw [hst]
  try dsimp only [authStateToVal]
  simp only [pqxdhAuthSimImplPrim, runAuthSendSimPrim]
  simp only [take_map_of_le _ _ hK.principals_le, take_map_of_le _ _ hK.usedSendSessions_le,
    take_map_of_le _ _ hK.spkBundles_le]
  have hsecb : (Env.get env (h₁.wk st)).1 = s.secb := by rw [hst]; rfl
  try simp only [hsecb]
  try rw [hsecb]
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
          rw [beq_false_of_ne (a := SessionId.sendNoOPK u i) (b := SessionId.sendNoOPK u i')
            (fun e => h2 (SessionId.sendNoOPK.inj e).2.symm)]
          simp [h3]
      · have h3 : ¬ (u.val = uf.val) := fun e => h1 (Fin.ext e)
        rw [beq_false_of_ne (a := SessionId.sendNoOPK uf i) (b := SessionId.sendNoOPK u i')
          (fun e => h1 (SessionId.sendNoOPK.inj e).1.symm)]
        simp [h3]
    | _ => simp
  rcases hb : b.opkB? with _ | ⟨oid, opk⟩
  swap
  · simp []
  · simp only []
    by_cases hlen : m0.length = m1.length
    swap
    · simp [hlen]
    by_cases hsid : SessionId.sendNoOPK uf i ∈ s.usedSendSessions
    · simp [hlen, hsid]
    rcases hp : List.find? (fun x => x.1 == ↑uf) s.principals with _ | ⟨idx, uE⟩
    · simp [hlen, hsid, hp]
    simp [hlen, hsid, hp, StateT.run_bind, StateT.run_monadLift,
      StateT.run_get, liftM, monadLift_self, List.find?_map, map_bind, bind_map_left]
    refine bind_congr' rfl (fun a => ?_)
    simp only [stRun_ite, map_ite', StateT.run_bind, StateT.run_monadLift, monadLift_self,
      map_bind, StateT.run_pure, bind_assoc, pure_bind]
    rcases a with _ | ⟨k, pE⟩
    · by_cases hm : m0 = m1
      swap
      · simp [hm, authStateToVal]
      subst hm
      simp only [Option.map_none, not_true_eq_false, and_false, ↓reduceIte]
      send_prefix
      send_mid
      rw [map_eq_bind_pure_comp]
      refine bind_congr' ?_ (fun ct => ?_)
      · exact primQ_aeadEnc_congr rfl (by simp [firstMsgAD, encodeEC, pbBytesField]) (by simp [])
      simp [StateT.run_pure, authStateToVal, authSessionEntryToVal]
    · cases hc : pE.corrupted
      · simp only [Option.map_some, Prod.map, principalEntryToVal, hc, Bool.not_false]
        simp only [Bool.true_eq_false, false_and, ↓reduceIte]
        send_prefix
        send_mid
        rw [map_eq_bind_pure_comp]
        refine bind_congr' ?_ (fun ct => ?_)
        · exact primQ_aeadEnc_congr rfl
            (by simp [firstMsgAD, encodeEC, pbBytesField]) (by simp [hsecb])
        simp [StateT.run_pure, authStateToVal, authSessionEntryToVal]
        all_goals simp [Function.comp_def, spkBundleEntryToVal, bne]
      · by_cases hm : m0 = m1
        swap
        · simp [hm, hc, principalEntryToVal, authStateToVal]
        subst hm
        simp only [Option.map_some, Prod.map, principalEntryToVal, hc, Bool.not_true,
          not_true_eq_false, and_false, ↓reduceIte]
        send_prefix
        send_mid
        rw [map_eq_bind_pure_comp]
        refine bind_congr' ?_ (fun ct => ?_)
        · exact primQ_aeadEnc_congr rfl
            (by simp [firstMsgAD, encodeEC, pbBytesField]) (by simp [hsecb])
        simp [StateT.run_pure, authStateToVal, authSessionEntryToVal]
        all_goals simp [Function.comp_def, spkBundleEntryToVal]

end SendEval

end SignalPqxdh.Security.ReductionDsl.AuthHs
