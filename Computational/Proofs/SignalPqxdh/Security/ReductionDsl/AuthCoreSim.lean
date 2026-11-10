/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshake
public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthHandshake
import VCVio.EvalDist.Monad.Basic

/-!
# Shared `Auth` simulation lemmas for `ReductionDsl`

Reduction-independent evaluation equivalence lemmas for the `Auth` handler branches against the
shallow `pqxdhAuthSimImplPrim` under `AuthBaseListsBounded`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

/-! ## Simp lemmas -/

@[simp] theorem Ext.step_wk {Γ Δ : List (Ty pqSig)} {σ τ : Ty pqSig}
    [h : Ext Γ Δ] (x : Var Γ τ) :
    (Ext.step (σ := σ) (Γ := Γ) (Δ := Δ)).wk x = .vs (h.wk x) := rfl

@[simp] theorem Ext.refl_wk {Γ : List (Ty pqSig)} {τ : Ty pqSig} (x : Var Γ τ) :
    (Ext.refl (Γ := Γ)).wk x = x := rfl

@[simp] theorem Env.get_vs {Γ : List (Ty pqSig)} {σ τ : Ty pqSig}
    (x : Var Γ τ) (a : σ.denote) (env : Env Γ) :
    Env.get (.cons a env) (.vs x) = Env.get env x := rfl

@[simp] theorem Env.get_vz {Γ : List (Ty pqSig)} {σ : Ty pqSig}
    (a : σ.denote) (env : Env Γ) :
    Env.get (.cons a env) .vz = a := rfl

@[simp] theorem pair_beq_split {α β : Type} [BEq α] [BEq β] (p : α × β) (c : α) (d : β) :
    (p == (c, d)) = (p.1 == c && p.2 == d) := by
  rcases p with ⟨a, b⟩; rfl

@[simp] theorem embedUnif_drKey96 :
    embedUnif (drKeyV <$> sampleDRKey96) =
      (do let dk ← embedUnif sampleDRKey96; pure (drKeyToVal dk)) := by
  rw [embedUnif_map]

@[simp] theorem embedUnif_msgKeys80 :
    embedUnif (msgKeysV <$> sampleMessageKeys80) =
      (do let mk ← embedUnif sampleMessageKeys80; pure (msgKeysToVal mk)) := by
  rw [embedUnif_map]

@[simp] theorem decide_nat_eq_beq (a b : Nat) : decide (a = b) = (a == b) := by
  cases h : a == b <;> simp_all

@[simp] theorem decide_ty_nat_eq_beq (a b : (Ty.nat : Ty pqSig).denote) :
    decide (a = b) = (a == b) :=
  decide_nat_eq_beq a b

@[simp] theorem eval_natEq {Γ : List (Ty pqSig)} (a b : Expr pqxdhOps Γ .nat) (env : Env Γ) :
    (natEq a b).eval env = (a.eval env == b.eval env) :=
  decide_nat_eq_beq (a.eval env) (b.eval env)

@[simp] theorem ite_true_eq_or (a b : Bool) : (if a = true then true else b) = (a || b) := by
  cases a <;> rfl

@[simp] theorem ite_ty_bool_true_eq_or (a b : (Ty.bool : Ty pqSig).denote) :
    (if a = true then true else b) = (a || b) :=
  ite_true_eq_or a b

@[simp] theorem ite_not_eq_beq (a b : Bool) : (if a = true then b else !b) = (a == b) := by
  cases a <;> cases b <;> rfl

@[simp] theorem ite_ty_bool_not_eq_beq (a b : (Ty.bool : Ty pqSig).denote) :
    (if a = true then b else !b) = (a == b) :=
  ite_not_eq_beq a b

attribute [simp] authRenc authRdec authQenc drKeyV drKeyOfV msgKeysV msgKeysOfV
  bundleV bundleOfV hdrV hdrOfV preKeyMsgV preKeyMsgOfV sidV
  authRespToVal valToAuthResp authQueryToVal drKeyToVal valToDrKey msgKeysToVal valToMsgKeys
  preKeyBundleToVal valToPreKeyBundle handshakeHdrToVal valToHandshakeHdr
  preKeyMsgToVal valToPreKeyMsg sessionIdToVal

@[simp] theorem PTag.dec_x25519 (x) : SignalPqxdh.LegacyCosted.PTag.x25519.dec x = id := rfl
@[simp] theorem PTag.dec_x25519Base (x) : SignalPqxdh.LegacyCosted.PTag.x25519Base.dec x = id := rfl
@[simp] theorem PTag.dec_isCanonical (x) : SignalPqxdh.LegacyCosted.PTag.isCanonical.dec x = id := rfl
@[simp] theorem PTag.dec_pow8 (x) : SignalPqxdh.LegacyCosted.PTag.pow8.dec x = id := rfl
@[simp] theorem PTag.dec_sigPkGen (x) : SignalPqxdh.LegacyCosted.PTag.sigPkGen.dec x = id := rfl
@[simp] theorem PTag.dec_sigSign (m x) : (SignalPqxdh.LegacyCosted.PTag.sigSign m).dec x = id := rfl
@[simp] theorem PTag.dec_sigVerify (m x) : (SignalPqxdh.LegacyCosted.PTag.sigVerify m).dec x = id := rfl
@[simp] theorem PTag.dec_kemKeyGen (x) : SignalPqxdh.LegacyCosted.PTag.kemKeyGen.dec x = id := rfl
@[simp] theorem PTag.dec_kemEncaps (x) : SignalPqxdh.LegacyCosted.PTag.kemEncaps.dec x = id := rfl
@[simp] theorem PTag.dec_kemDecaps (x) : SignalPqxdh.LegacyCosted.PTag.kemDecaps.dec x = id := rfl
@[simp] theorem PTag.dec_hkdfDerive96 (w x) : (SignalPqxdh.LegacyCosted.PTag.hkdfDerive96 w).dec x = drKeyV := rfl
@[simp] theorem PTag.dec_rootCreateChain (x) : SignalPqxdh.LegacyCosted.PTag.rootCreateChain.dec x = id := rfl
@[simp] theorem PTag.dec_chainKdfSeed (x) : SignalPqxdh.LegacyCosted.PTag.chainKdfSeed.dec x = id := rfl
@[simp] theorem PTag.dec_chainKdfNext (x) : SignalPqxdh.LegacyCosted.PTag.chainKdfNext.dec x = id := rfl
@[simp] theorem PTag.dec_deriveMsgKeys (s x) : (SignalPqxdh.LegacyCosted.PTag.deriveMsgKeys s).dec x = msgKeysV := rfl
@[simp] theorem PTag.dec_spqrInitSend (p c x) : (SignalPqxdh.LegacyCosted.PTag.spqrInitSend p c).dec x = id := rfl
@[simp] theorem PTag.dec_spqrInitRecv (p c x) : (SignalPqxdh.LegacyCosted.PTag.spqrInitRecv p c).dec x = id := rfl
@[simp] theorem PTag.dec_aeadEnc (k a c x) : (SignalPqxdh.LegacyCosted.PTag.aeadEnc k a c).dec x = id := rfl
@[simp] theorem PTag.dec_aeadDec (k a m x) : (SignalPqxdh.LegacyCosted.PTag.aeadDec k a m).dec x = id := rfl

/-! ## List-length invariant -/

/-- Every list of the `Auth` game state has length `≤ n`. -/
structure AuthBaseListsBounded {S : Setup} (n : Nat) (s : AuthState S) : Prop where
  principals_le       : s.principals.length ≤ n
  spkBundles_le       : s.spkBundles.length ≤ n
  opkEntries_le       : s.opkEntries.length ≤ n
  sessions_le         : s.sessions.length ≤ n
  usedSendSessions_le : s.usedSendSessions.length ≤ n
  usedRecvOPK_le      : s.usedRecvOPK.length ≤ n
  usedRecvNoOPK_le    : s.usedRecvNoOPK.length ≤ n
  usedKyberTriples_le : s.seenKyberBaseKeys.length ≤ n
  roCache_le          : s.roCache.length ≤ n
  rootRoCache_le      : s.rootRoCache.length ≤ n
  advKeys_le          : s.advKeys.length ≤ n

theorem AuthBaseListsBounded.mono {S : Setup} {n m : Nat} {s : AuthState S} (h : n ≤ m)
    (hB : AuthBaseListsBounded n s) : AuthBaseListsBounded m s :=
  ⟨by have := hB.1; omega, by have := hB.2; omega, by have := hB.3; omega,
   by have := hB.4; omega, by have := hB.5; omega, by have := hB.6; omega,
   by have := hB.7; omega, by have := hB.8; omega, by have := hB.9; omega,
   by have := hB.10; omega, by have := hB.11; omega⟩

theorem authBaseListsBounded_empty (S : Setup) (secb : Bool) :
    AuthBaseListsBounded 0 (AuthState.empty S secb) := by
  constructor <;> simp [AuthState.empty]

/-! ## Base handler branches -/

macro "dsl_unfold" : tactic => `(tactic| simp only [
  v, bindV, letV, caseOptV, caseSumV, findMV, anyMV, eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
  eval_natEq, nat2Eq, nat3Eq, encEC_eval, encKEM_eval,
  stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb, stSOE, stSNE,
  stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
  peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
  sbMk, oeMk, buMk, bytes2Eq,
  aNone, aInitPrin, aPk, aCorr, aBundle, aDrKey, aRootKdf, rs, hkdfOrRoC, rootRoC,
  initPrinB, corruptB, genSpkB, genOpkB, registerB, roB, roRootB,
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
  findML_eq_findMPrim, anyML_eq_anyMPrim, mapML_eq_mapMPrim,
  consumeFirstML_eq_consumeFirstMPrim,
  decide_ty_nat_eq_beq, decide_nat_eq_beq,
  ite_true, ite_false, ↓reduceIte, Bool.false_eq_true])

section BaseEval

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
  (env : Env Δ) (s : AuthState S)

theorem initPrinB_eval (st : Var Γ₁ authStateTy) (u : Var Γ₂ .nat) (uf : Fin S.N_id)
    (hst : Env.get env (h₁.wk st) = authStateToVal s) (hu : Env.get env (h₂.wk u) = uf.val)
    (hK : AuthBaseListsBounded K s) :
    (initPrinB K st u).eval env =
      Prod.map authRespToVal authStateToVal <$> (pqxdhAuthSimImplPrim S (.initPrin uf)).run s := by
  dsl_unfold
  simp only [hst, hu]
  rw [List.take_of_length_le (by simpa using hK.principals_le)]
  simp only [pqxdhAuthSimImplPrim, authStateToVal, List.any_map, StateT.run_bind, StateT.run_get,
    Function.comp_def, pure_bind, Prod.map_fst, id_eq]
  split
  · simp [*]
  · simp [*, sampleScalar32, map_bind, principalEntryToVal]

theorem corruptB_eval (st : Var Γ₁ authStateTy) (u : Var Γ₂ .nat) (uf : Fin S.N_id)
    (hst : Env.get env (h₁.wk st) = authStateToVal s) (hu : Env.get env (h₂.wk u) = uf.val)
    (hK : AuthBaseListsBounded K s) :
    (corruptB K st u).eval env =
      Prod.map authRespToVal authStateToVal <$> (pqxdhAuthSimImplPrim S (.corruptIK uf)).run s := by
  dsl_unfold
  simp only [hst, hu]
  rw [List.take_of_length_le (by simpa using hK.principals_le)]
  simp only [pqxdhAuthSimImplPrim, authStateToVal, List.find?_map, StateT.run_bind, StateT.run_get,
    Function.comp_def, pure_bind, Prod.map_fst, id_eq]
  rcases hf : List.find? (fun x => x.1 == uf.val) s.principals with _ | ⟨i, e⟩
  · simp [hf]
  · simp [hf, List.map_map, Function.comp_def]
    intro a b _
    split <;> rfl

theorem genSpkB_eval (st : Var Γ₁ authStateTy) (x : Var Γ₂ (.prod .nat .nat))
    (uf : Fin S.N_id) (jf : Fin S.N_recv)
    (hst : Env.get env (h₁.wk st) = authStateToVal s)
    (hx : Env.get env (h₂.wk x) = (uf.val, jf.val))
    (hK : AuthBaseListsBounded K s) :
    (genSpkB K st x).eval env =
      Prod.map authRespToVal authStateToVal <$>
        (pqxdhAuthSimImplPrim S (.genSPK uf jf)).run s := by
  dsl_unfold
  simp only [hst, hx]
  rw [List.take_of_length_le (by simpa using hK.spkBundles_le),
    List.take_of_length_le (by simpa using hK.principals_le)]
  simp only [pqxdhAuthSimImplPrim, authStateToVal, List.any_map, List.find?_map, StateT.run_bind,
    StateT.run_get, Function.comp_def, pure_bind, Prod.map_fst, id_eq, sampleKemKeyGenPrim]
  by_cases hc : (s.spkBundles.any fun x => x.1.1 == uf.val && x.1.2 == jf.val)
  · simp [hc]
  · rcases hf : List.find? (fun x => x.1 == uf.val) s.principals with _ | ⟨i, e⟩
    · simp [hc, hf]
    · simp [hc, hf, sampleScalar32, map_bind, encodeEC, encodeKEM]

theorem genOpkB_eval (st : Var Γ₁ authStateTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat)))
    (uf : Fin S.N_id) (jf : Fin S.N_recv) (of : Fin S.N_opk)
    (hst : Env.get env (h₁.wk st) = authStateToVal s)
    (hx : Env.get env (h₂.wk x) = (uf.val, (jf.val, of.val)))
    (hK : AuthBaseListsBounded K s) :
    (genOpkB K st x).eval env =
      Prod.map authRespToVal authStateToVal <$>
        (pqxdhAuthSimImplPrim S (.genOPK uf jf of)).run s := by
  dsl_unfold
  simp only [hst, hx]
  rw [List.take_of_length_le (by simpa using hK.opkEntries_le)]
  simp only [pqxdhAuthSimImplPrim, authStateToVal, List.any_map, StateT.run_bind, StateT.run_get,
    Function.comp_def, pure_bind, Prod.map_fst]
  by_cases hc :
      (s.opkEntries.any fun x => x.1.1 == uf.val && (x.1.2.1 == jf.val && x.1.2.2 == of.val))
  · simp [hc]
  · simp [hc, sampleScalar32, map_bind]

theorem registerB_eval (st : Var Γ₁ authStateTy) (sk : Var Γ₂ (B 32)) (skv : Bytes)
    (hst : Env.get env (h₁.wk st) = authStateToVal s) (hsk : Env.get env (h₂.wk sk) = skv) :
    (registerB st sk).eval env =
      Prod.map authRespToVal authStateToVal <$>
        (pqxdhAuthSimImplPrim S (.registerKey skv)).run s := by
  subst hsk
  dsl_unfold
  simp only [hst]
  simp only [pqxdhAuthSimImplPrim, authStateToVal, StateT.run_bind, StateT.run_get,
    pure_bind]
  by_cases hl : (Env.get env (h₂.wk sk)).length = 32
  · simp [hl, map_bind]
  · simp [hl]

theorem roB_eval (st : Var Γ₁ authStateTy) (sec : Var Γ₂ (B 192)) (secv : Bytes)
    (hst : Env.get env (h₁.wk st) = authStateToVal s) (hsec : Env.get env (h₂.wk sec) = secv)
    (hK : AuthBaseListsBounded K s) :
    (roB K st sec).eval env =
      Prod.map authRespToVal authStateToVal <$>
        (pqxdhAuthSimImplPrim S (.roQuery secv)).run s := by
  dsl_unfold
  simp only [hst, hsec]
  rw [List.take_of_length_le (by simpa using hK.roCache_le)]
  simp only [pqxdhAuthSimImplPrim, evalHkdfOrRoPrim, authStateToVal, List.find?_map,
    StateT.run_bind, StateT.run_get, Function.comp_def, pure_bind, Prod.map_fst, id_eq]
  rcases hf : List.find? (fun x => x.1 == secv) s.roCache with _ | ⟨i, e⟩
  · simp [hf]
  · simp [hf]

theorem roRootB_eval (st : Var Γ₁ authStateTy) (x : Var Γ₂ (.prod (B 32) (B 32))) (rk dh : Bytes)
    (hst : Env.get env (h₁.wk st) = authStateToVal s) (hx : Env.get env (h₂.wk x) = (rk, dh))
    (hK : AuthBaseListsBounded K s) :
    (roRootB K st x).eval env =
      Prod.map authRespToVal authStateToVal <$>
        (pqxdhAuthSimImplPrim S (.roRootQuery rk dh)).run s := by
  dsl_unfold
  simp only [hst, hx]
  rw [List.take_of_length_le (by simpa using hK.rootRoCache_le)]
  simp only [pqxdhAuthSimImplPrim, evalRootKdfOrRoPrim, authStateToVal,
    StateT.run_bind, StateT.run_get, pure_bind]
  rcases hf : List.find? (fun x => x.1.1 == rk && x.1.2 == dh) s.rootRoCache with _ | ⟨i, e⟩
  · simp [hf, map_bind]
  · simp [hf]

end BaseEval

/-! ## Per-query preservation -/

theorem evalHkdfOrRoPrim_hol (useRo : Bool) (c : List (Bytes × DRKey)) (sec : Bytes) :
    HoldsOnLeaves (fun x => x.2.length ≤ c.length + 1) (evalHkdfOrRoPrim useRo c sec) := by
  unfold evalHkdfOrRoPrim
  split
  · exact HoldsOnLeaves.bind_const _ (fun _ => HoldsOnLeaves.pure (by simp))
  · split
    · exact HoldsOnLeaves.pure (by simp)
    · exact HoldsOnLeaves.bind_const _ (fun _ => HoldsOnLeaves.pure (by simp))

theorem evalRootKdfOrRoPrim_hol (useRo : Bool)
    (c : List ((Bytes × Bytes) × (Bytes × Bytes))) (rk dh : Bytes) :
    HoldsOnLeaves (fun x => x.2.length ≤ c.length + 1) (evalRootKdfOrRoPrim useRo c rk dh) := by
  unfold evalRootKdfOrRoPrim
  split
  · exact HoldsOnLeaves.bind_const _ (fun _ => HoldsOnLeaves.pure (by simp))
  · split
    · exact HoldsOnLeaves.pure (by simp)
    · exact HoldsOnLeaves.bind_const _ (fun _ =>
        HoldsOnLeaves.bind_const _ (fun _ => HoldsOnLeaves.pure (by simp)))

theorem checkAndMarkKyberUsed_length (l : List (Nat × KeyId × KeyId × Bytes)) (k : Nat)
    (a b : KeyId) (e : Bytes) : (checkAndMarkKyberBaseKeySeen l k a b e).2.length ≤ l.length + 1 := by
  simp only [checkAndMarkKyberBaseKeySeen]; split <;> simp

section StApply
variable {σ α β : Type} {m : Type → Type} [Monad m]
theorem stApply_pure (a : α) (s : σ) : (pure a : StateT σ m α) s = pure (a, s) := rfl
theorem stApply_bind (x : StateT σ m α) (f : α → StateT σ m β) (s : σ) :
    (x >>= f) s = x s >>= fun p => f p.1 p.2 := rfl
theorem stApply_set (s' s : σ) : (set s' : StateT σ m PUnit) s = pure (⟨⟩, s') := rfl
theorem stApply_get (s : σ) : (get : StateT σ m σ) s = pure (s, s) := rfl
theorem stApply_lift (x : m α) (s : σ) :
    (monadLift x : StateT σ m α) s = x >>= fun a => pure (a, s) := rfl
end StApply

macro "hol_leaf" : tactic => `(tactic| (constructor <;>
  simp only [List.length_cons, List.length_map] <;>
  first | omega | exact le_trans (checkAndMarkKyberUsed_length _ _ _ _ _) (by omega)))

macro "hol_simp" : tactic => `(tactic| simp only [StateT.run_bind, StateT.run_monadLift,
  StateT.run_pure, StateT.run_set, StateT.run_get, bind_assoc, pure_bind, liftM, monadLift_self,
  stApply_pure, stApply_bind, stApply_set, stApply_get, stApply_lift])

macro "hol_crawl" : tactic => `(tactic| repeat (first
  | hol_simp
  | (refine HoldsOnLeaves.pure ?_; hol_leaf)
  | (refine HoldsOnLeaves.bind (evalHkdfOrRoPrim_hol _ _ _) (fun _ _ => ?_))
  | (refine HoldsOnLeaves.bind (evalRootKdfOrRoPrim_hol _ _ _ _) (fun _ _ => ?_))
  | (refine HoldsOnLeaves.bind_const _ (fun _ => ?_))
  | split))

macro "hol_full" : tactic => `(tactic| repeat (first
    | hol_simp
    | (refine HoldsOnLeaves.pure ?_; hol_leaf)
    | (refine HoldsOnLeaves.bind (evalHkdfOrRoPrim_hol _ _ _) (fun _ _ => ?_))
    | (refine HoldsOnLeaves.bind (evalRootKdfOrRoPrim_hol _ _ _ _) (fun _ _ => ?_))
    | (refine HoldsOnLeaves.bind_const _ (fun _ => ?_))
    | split))

set_option maxHeartbeats 1000000 in
theorem recvNoOPK_hol (S : Setup) (n : Nat) (s : AuthState S) (hK : AuthBaseListsBounded n s)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg) :
    HoldsOnLeaves (fun x => AuthBaseListsBounded (n + 1) x.2)
      ((runAuthRecvNoOPKSimPrim S k j l msg).run s) := by
  have hK' := hK
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hK'
  simp only [runAuthRecvNoOPKSimPrim, runAuthRecvFinishSimPrim, runAuthRecvStep2SimPrim]
  hol_full

set_option maxHeartbeats 1000000 in
theorem recvOPK_hol (S : Setup) (n : Nat) (s : AuthState S) (hK : AuthBaseListsBounded n s)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg) :
    HoldsOnLeaves (fun x => AuthBaseListsBounded (n + 1) x.2)
      ((runAuthRecvOPKSimPrim S k j o msg).run s) := by
  have hK' := hK
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hK'
  simp only [runAuthRecvOPKSimPrim, runAuthRecvFinishSimPrim, runAuthRecvStep2SimPrim]
  hol_full

set_option maxHeartbeats 1000000 in
theorem send_hol (S : Setup) (n : Nat) (s : AuthState S) (hK : AuthBaseListsBounded n s)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes) :
    HoldsOnLeaves (fun x => AuthBaseListsBounded (n + 1) x.2)
      ((runAuthSendSimPrim S sid u bundle m0 m1).run s) := by
  have hK' := hK
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hK'
  simp only [runAuthSendSimPrim]
  hol_full

set_option maxHeartbeats 1000000 in
theorem pqxdhAuthSimImplPrim_hol (S : Setup) (n : Nat) (q : (authSpec S).Domain)
    (s : AuthState S) (hK : AuthBaseListsBounded n s) :
    HoldsOnLeaves (fun x => AuthBaseListsBounded (n + 1) x.2)
      ((pqxdhAuthSimImplPrim S q).run s) := by
  have hK' := hK
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hK'
  cases q with
  | sendOPK u i bundle m0 m1 =>
    simp only [pqxdhAuthSimImplPrim]
    split
    · hol_full
    · exact (send_hol S n s hK _ u bundle m0 m1)
  | sendNoOPK u i bundle m0 m1 =>
    simp only [pqxdhAuthSimImplPrim]
    split
    · hol_full
    · exact (send_hol S n s hK _ u bundle m0 m1)
  | recvOPK k j o msg => exact recvOPK_hol S n s hK k j o msg
  | recvNoOPK k j l msg => exact recvNoOPK_hol S n s hK k j l msg
  | _ => simp only [pqxdhAuthSimImplPrim]; hol_full

end SignalPqxdh.Security.ReductionDsl.AuthHs
