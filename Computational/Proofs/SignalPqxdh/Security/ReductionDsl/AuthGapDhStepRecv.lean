/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepPows
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSimRecv
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSimSend
import VCVio.EvalDist.Monad.Basic

@[expose] public section

/-!
# Recv-branch evaluation for the `Auth` Gap-DH DSL

Proves that `fgRecvB` evaluates to the shallow `fgAuthStep` receive branches under `fgSimToVal`
and `AgBnd`.
-/

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

macro "rfl_hx" : tactic =>
  `(tactic| first | rfl | (rw [$(Lean.mkIdent `hx'):ident]; rfl))

theorem agR_aeadDec_congr {mk mk' : MessageKeys} {ad ad' ct ct' : Bytes} (h1 : mk = mk')
    (h2 : ad = ad') (h3 : ct = ct') :
    query (spec := PrimBaseSpec + gapDhOracleSpec)
      (Sum.inl (Sum.inr (PrimQuery.aeadDec mk ad ct))) =
      FgGapDh.primGdhQ (.aeadDec mk' ad' ct') := by subst h1 h2 h3; rfl

section Recv

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
  (env : Env Δ) (st : FgAuthSimState S)

theorem agR_fs_base (st : FgAuthSimState S) : (fgSimToVal st).1 = authStateToVal st.base := rfl
theorem agR_fs_fgL (st : FgAuthSimState S) :
    (fgSimToVal st).2.1 = st.fgL.map fgPatchEntryToVal := rfl
theorem agR_fs_rootL (st : FgAuthSimState S) :
    (fgSimToVal st).2.2.1 = st.fgRootL.map rootEntryToVal := rfl
theorem agR_fs_pows (st : FgAuthSimState S) : (fgSimToVal st).2.2.2.2.2.2 = st.advKeyPows := rfl
theorem agR_as_prin (s : AuthState S) :
    (authStateToVal s).2.2.1 = s.principals.map (Prod.map id principalEntryToVal) := rfl
theorem agR_as_spk (s : AuthState S) :
    (authStateToVal s).2.2.2.1 = s.spkBundles.map (Prod.map id spkBundleEntryToVal) := rfl
theorem agR_as_opk (s : AuthState S) :
    (authStateToVal s).2.2.2.2.1 =
      s.opkEntries.map (Prod.map (fun (u, j, o) => (u, (j, o))) opkEntryToVal) := rfl
theorem agR_as_usedO (s : AuthState S) :
    (authStateToVal s).2.2.2.2.2.2.2.1 = s.usedRecvOPK.map (fun (k, j, o) => (k, (j, o))) := rfl
theorem agR_as_usedN (s : AuthState S) :
    (authStateToVal s).2.2.2.2.2.2.2.2.1 =
      s.usedRecvNoOPK.map (fun (k, j, l) => (k, (j, l))) := rfl
theorem agR_as_kyb (s : AuthState S) :
    (authStateToVal s).2.2.2.2.2.2.2.2.2.1 =
      s.seenKyberBaseKeys.map (fun (k, p, s, e) => (k, (p, (s, e)))) := rfl

theorem agR_any_used3 (l : List (Nat × Nat × Nat)) (a b c : Nat) :
    (l.map (fun (k, j, o) => (k, (j, o)))).any
        (fun x => x.1 == a && (x.2.1 == b && x.2.2 == c)) =
      l.contains (a, b, c) := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    rcases y with ⟨y1, y2, y3⟩
    simp only [List.map_cons, List.any_cons, List.contains_cons, ih]
    congr 1
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq]
    constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1.symm, h2.symm, h3.symm⟩

theorem agR_any_kyb (l : List (Nat × KeyId × KeyId × Bytes)) (a : Nat) (b c : KeyId) (d : Bytes) :
    (l.map (fun (k, p, s, e) => (k, (p, (s, e))))).any
        (fun x => a == x.1 && (b == x.2.1 && (c == x.2.2.1 && d == x.2.2.2))) =
      l.contains (a, b, c, d) := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    rcases y with ⟨y1, y2, y3, y4⟩
    simp only [List.map_cons, List.any_cons, List.contains_cons, ih]
    congr 1

theorem agR_find_spk {β : Type} (l : List ((Nat × Nat) × β)) (a b : Nat) :
    l.find? (fun x => x.1 == (a, b)) = l.find? (fun x => x.1.1 == a && x.1.2 == b) := by
  congr 1

theorem agR_find_opk {β : Type} (l : List ((Nat × Nat × Nat) × β)) (a b c : Nat) :
    l.find? (fun x => x.1 == (a, b, c)) =
      l.find? (fun x => x.1.1 == a && (x.1.2.1 == b && x.1.2.2 == c)) := by
  congr 1

set_option maxHeartbeats 4000000 in
theorem agR_recvC_opk (sim : Var Γ₁ fgSimTy) (x : Var Γ₂ recvQTy)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hsim : Env.get env (h₁.wk sim) = fgSimToVal st)
    (hx : Env.get env (h₂.wk x) = (k.val, (j.val, (o.val, preKeyMsgToVal msg))))
    (hB : AgBnd K st) :
    (fgRecvC S K true sim x).eval env =
      (fun r => (authRespToVal r.1, fgSimToVal r.2)) <$>
        fgRunRecvOPKAuthGdh S K k j o msg st := by
  have hx' : @Env.get pqSig Δ (.prod .nat (.prod .nat (.prod .nat preKeyMsgTy))) env
      (@Ext.wk Γ₂ Δ h₂ (.prod .nat (.prod .nat (.prod .nat preKeyMsgTy))) x) =
      (k.val, (j.val, (o.val, preKeyMsgToVal msg))) := hx
  simp only [fgRecvC, letV, bindV, caseOptV, v, eCaseOpt, eFind, eAny, eMap, eval_natEq,
    nat2Eq, nat3Eq, optU32Eq, eLet2, eLet, kyberCheckE, kyberEq, stPrin, stSpks, stOpks,
    stUsedO, stUsedN, stKyb, stUpd, pmHdr, pmEphAPk, pmPqMsg, pmAeadCt, hdIkAPk, hdEkAPk,
    hdSpkId, hdOpkId, hdPqspkId, hdKemCt, peSecIKA0, peIkAPk, sbSpkSk, sbSpkPk, sbPqspkSk,
    oeOpkSk, oeOpkPk, oeConsumed, oeUpd, aNone, aRecvHonest, aRecvUnfresh, q4,
    fsUpd, fsMk, fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows,
    Comp.eval_letC, Comp.eval_liftChal, eval_queryPrimC, Comp.eval,
    Expr.eval_litBytes, Expr.eval_bytesLen, Expr.eval_bytesBeq,
    Expr.eval_u32OfNat, Expr.eval_u32Beq,
    Expr.eval, ite_true_eq_or,
    Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
    PTag.dec_isCanonical, PTag.dec_kemDecaps, PTag.dec_chainKdfSeed,
    PTag.dec_chainKdfNext, PTag.dec_deriveMsgKeys, PTag.dec_spqrInitRecv,
    PTag.dec_aeadDec, SignalPqxdh.LegacyCosted.PTag.enc, id_map,
    ↓reduceIte, twoSideOptC_eval, twoSideC_eval, patchC_eval, rootPatchC_eval,
    hsim, hx']
  rw [koskSenderOkPowsC_eval (s := st.base) (P := st.advKeyPows) (hK := hB.pows_le)
    (hst := by simp only [Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, fgSimToVal])
    (hp := by simp only [Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, fgSimToVal])
    (hBs := hB.base)]
  simp only [agR_fs_base, agR_fs_fgL, agR_fs_rootL, agR_fs_pows, agR_as_prin, agR_as_spk,
    agR_as_opk, agR_as_usedO, agR_as_usedN, agR_as_kyb, preKeyMsgToVal, preKeyMsgV,
    hdrV, Expr.eval, Env.get_vs, Env.get_vz,
    take_map_of_le _ _ hB.base.principals_le, take_map_of_le _ _ hB.base.spkBundles_le,
    take_map_of_le _ _ hB.base.usedRecvOPK_le, take_map_of_le _ _ hB.base.opkEntries_le,
    take_map_of_le _ _ hB.base.usedKyberTriples_le]
  simp only [fgRunRecvOPKAuthGdh, fgFinishRecvAuthGdh, fgFinishRecvStep2AuthGdh,
    checkAndMarkKyberBaseKeySeen]
  rw [agR_any_used3, agR_any_kyb]
  rcases ho : msg.hdr.opkId? with _ | oid
  · simp [authRespToVal]
  simp only [Option.some_beq_some]
  by_cases hg : (msg.hdr.spkId == UInt32.ofNat ↑j && msg.hdr.pqspkId == UInt32.ofNat ↑j &&
      oid == UInt32.ofNat ↑o && List.length msg.hdr.ikAPk == 32 &&
      List.length msg.hdr.ekAPk == 32 && List.length msg.ephAPk == 32) = true
  swap
  · simp only [Bool.not_eq_true] at hg
    simp [hg, authRespToVal]
  simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  by_cases hc : st.base.usedRecvOPK.contains (↑k, ↑j, ↑o) = true
  · have hm : ((k : Nat), (j : Nat), (o : Nat)) ∈ st.base.usedRecvOPK := by simpa using hc
    simp [hm, authRespToVal]
  simp only [hc, Bool.false_eq_true, ↓reduceIte, map_bind]
  refine bind_congr' (by rfl_hx) (fun ok => ?_)
  cases ok
  · simp [authRespToVal]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.find?_map, Function.comp_def,
    Prod.map_fst, id_eq, agR_find_spk, agR_find_opk]
  rcases hp : List.find? (fun x => x.1 == (k : Nat)) st.base.principals with _ | ⟨kidx, kE⟩
  · simp [hp, authRespToVal]
  rcases hb : List.find? (fun x => x.1.1 == (k : Nat) && x.1.2 == (j : Nat)) st.base.spkBundles
    with _ | ⟨kjidx, sb⟩
  · simp [hp, hb, authRespToVal]
  rcases hoe : List.find?
    (fun x => x.1.1 == (k : Nat) && (x.1.2.1 == (j : Nat) && x.1.2.2 == (o : Nat)))
    st.base.opkEntries with _ | ⟨oidx, oE⟩
  · simp [hp, hb, hoe, authRespToVal]
  simp only [hp, hb, hoe, Option.map_some, Prod.map, id_eq, opkEntryToVal, pure_bind]
  cases hcons : oE.consumed
  swap
  · simp [authRespToVal]
  simp only [Bool.false_eq_true, ↓reduceIte, map_bind]
  refine bind_congr' (by rfl_hx) (fun c1 => ?_)
  refine bind_congr' (by rfl_hx) (fun c2 => ?_)
  by_cases hkm : st.base.seenKyberBaseKeys.contains
      (↑k, msg.hdr.pqspkId, msg.hdr.spkId, msg.hdr.ekAPk) = true
  · have hkm' : ((k : Nat), msg.hdr.pqspkId, msg.hdr.spkId, msg.hdr.ekAPk) ∈
        st.base.seenKyberBaseKeys := by
      simpa using hkm
    simp [hkm', authRespToVal]
  simp only [hkm, Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.false_or]
  cases c1
  · simp [authRespToVal]
  cases c2
  · simp [authRespToVal]
  simp only [Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte, map_bind]
  refine bind_congr' (by rfl_hx) (fun ss? => ?_)
  rcases ss? with _ | ss
  · simp [authRespToVal]
  simp only [map_bind, bind_map_left, Option.map_some, valToFgPos_fgPosToVal]
  refine bind_congr' (by rfl_hx) (fun p4 => ?_)
  refine bind_congr' (by rfl_hx) (fun p1 => ?_)
  refine bind_congr' (by rfl_hx) (fun p2 => ?_)
  refine bind_congr' (by rfl_hx) (fun p3 => ?_)
  refine bind_congr' (by rw [agList_fgPatchEntry_roundtrip']) (fun dkL => ?_)
  refine bind_congr' (by rfl_hx) (fun pR => ?_)
  refine bind_congr' (by rw [agList_rootEntry_roundtrip']; rfl) (fun rkOut => ?_)
  refine bind_congr' (by rfl_hx) (fun mkSeed => ?_)
  refine bind_congr' (by rfl_hx) (fun ck1 => ?_)
  refine bind_congr' (by rfl_hx) (fun spqr? => ?_)
  rcases spqr? with _ | spqr
  · simp [authRespToVal]
  simp only [map_bind]
  refine bind_congr' (by rfl_hx) (fun mk => ?_)
  refine bind_congr'
    (agR_aeadDec_congr rfl
      (by rw [firstMsgADE_evalHs]; simp [Expr.eval, firstMsgAD, encodeEC, pbBytesField,
        principalEntryToVal])
      (by rfl_hx))
    (fun pt? => ?_)
  rcases pt? with _ | pt
  · simp [authRespToVal]
  simp only [map_bind]
  rw [findHonestC_eval S _ st.base _ (hst := by
    simp only [Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz]) (hPrin := hB.base.principals_le)]
  simp only [embedPrim_map, bind_map_left, Expr.eval, Env.get_vs, Env.get_vz]
  rw [← agFindHonest_eq]
  refine bind_congr' (by rfl_hx) (fun sp => ?_)
  rcases sp with _ | sp <;>
  · simp only [Option.map_none, Option.map_some, map_pure, authRespToVal, authRenc,
      drKeyToVal, drKeyV, fgSimToVal, authStateToVal, List.map_map, Function.comp_def]
    congr 1
    simp only [List.map_cons, Prod.mk.injEq, true_and, and_true]
    apply List.map_congr_left
    rintro ⟨⟨a, b, c⟩, e⟩ _
    rcases e with ⟨sk, pk, cs⟩
    simp only [Prod.map, opkEntryToVal, Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq]
    split_ifs <;> rfl

set_option maxHeartbeats 4000000 in
theorem agR_recvC_noopk (sim : Var Γ₁ fgSimTy) (x : Var Γ₂ recvQTy)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hsim : Env.get env (h₁.wk sim) = fgSimToVal st)
    (hx : Env.get env (h₂.wk x) = (k.val, (j.val, (l.val, preKeyMsgToVal msg))))
    (hB : AgBnd K st) :
    (fgRecvC S K false sim x).eval env =
      (fun r => (authRespToVal r.1, fgSimToVal r.2)) <$>
        fgRunRecvNoOPKAuthGdh S K k j l msg st := by
  have hx' : @Env.get pqSig Δ (.prod .nat (.prod .nat (.prod .nat preKeyMsgTy))) env
      (@Ext.wk Γ₂ Δ h₂ (.prod .nat (.prod .nat (.prod .nat preKeyMsgTy))) x) =
      (k.val, (j.val, (l.val, preKeyMsgToVal msg))) := hx
  simp only [fgRecvC, letV, bindV, caseOptV, v, eCaseOpt, eFind, eAny, eval_natEq,
    nat2Eq, nat3Eq, optU32Eq, eLet2, eLet, kyberCheckE, kyberEq, stPrin, stSpks, stOpks,
    stUsedO, stUsedN, stKyb, stUpd, pmHdr, pmEphAPk, pmPqMsg, pmAeadCt, hdIkAPk, hdEkAPk,
    hdSpkId, hdOpkId, hdPqspkId, hdKemCt, peSecIKA0, peIkAPk, sbSpkSk, sbSpkPk, sbPqspkSk,
    aNone, aRecvHonest, aRecvUnfresh, q4,
    fsUpd, fsMk, fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows,
    Comp.eval_letC, Comp.eval_liftChal, eval_queryPrimC, Comp.eval,
    Expr.eval_litBytes, Expr.eval_bytesLen, Expr.eval_bytesBeq,
    Expr.eval_u32OfNat, Expr.eval_u32Beq,
    Expr.eval, ite_true_eq_or,
    Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
    PTag.dec_isCanonical, PTag.dec_kemDecaps, PTag.dec_chainKdfSeed,
    PTag.dec_chainKdfNext, PTag.dec_deriveMsgKeys, PTag.dec_spqrInitRecv,
    PTag.dec_aeadDec, SignalPqxdh.LegacyCosted.PTag.enc, id_map,
    Bool.false_eq_true, ↓reduceIte,
    twoSideOptC_eval, twoSideC_eval, patchC_eval, rootPatchC_eval,
    hsim, hx']
  rw [koskSenderOkPowsC_eval (s := st.base) (P := st.advKeyPows) (hK := hB.pows_le)
    (hst := by simp only [Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, fgSimToVal])
    (hp := by simp only [Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, fgSimToVal])
    (hBs := hB.base)]
  simp only [agR_fs_base, agR_fs_fgL, agR_fs_rootL, agR_fs_pows, agR_as_prin, agR_as_spk,
    agR_as_opk, agR_as_usedO, agR_as_usedN, agR_as_kyb, preKeyMsgToVal, preKeyMsgV,
    hdrV, Expr.eval, Env.get_vs, Env.get_vz,
    take_map_of_le _ _ hB.base.principals_le, take_map_of_le _ _ hB.base.spkBundles_le,
    take_map_of_le _ _ hB.base.usedRecvNoOPK_le,
    take_map_of_le _ _ hB.base.usedKyberTriples_le]
  simp only [fgRunRecvNoOPKAuthGdh, fgFinishRecvAuthGdh, fgFinishRecvStep2AuthGdh,
    checkAndMarkKyberBaseKeySeen]
  rw [agR_any_used3, agR_any_kyb]
  rcases ho : msg.hdr.opkId? with _ | oid
  swap
  · simp [authRespToVal]
  have hnn : ((none : Option UInt32) == none) = true := rfl
  simp only [hnn, Bool.and_true]
  by_cases hg : (msg.hdr.spkId == UInt32.ofNat ↑j && msg.hdr.pqspkId == UInt32.ofNat ↑j &&
      List.length msg.hdr.ikAPk == 32 && List.length msg.hdr.ekAPk == 32 &&
      List.length msg.ephAPk == 32) = true
  swap
  · simp only [Bool.not_eq_true] at hg
    simp [hg, authRespToVal]
  simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  by_cases hc : st.base.usedRecvNoOPK.contains (↑k, ↑j, ↑l) = true
  · have hm : ((k : Nat), (j : Nat), (l : Nat)) ∈ st.base.usedRecvNoOPK := by simpa using hc
    simp [hm, authRespToVal]
  simp only [hc, Bool.false_eq_true, ↓reduceIte, map_bind]
  refine bind_congr' (by rfl_hx) (fun ok => ?_)
  cases ok
  · simp [authRespToVal]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.find?_map, Function.comp_def,
    Prod.map_fst, id_eq, agR_find_spk]
  rcases hp : List.find? (fun x => x.1 == (k : Nat)) st.base.principals with _ | ⟨kidx, kE⟩
  · simp [hp, authRespToVal]
  rcases hb : List.find? (fun x => x.1.1 == (k : Nat) && x.1.2 == (j : Nat)) st.base.spkBundles
    with _ | ⟨kjidx, sb⟩
  · simp [hp, hb, authRespToVal]
  simp only [hp, hb, Option.map_some, Prod.map, id_eq, pure_bind, map_bind]
  refine bind_congr' (by rfl_hx) (fun c1 => ?_)
  refine bind_congr' (by rfl_hx) (fun c2 => ?_)
  by_cases hkm : st.base.seenKyberBaseKeys.contains
      (↑k, msg.hdr.pqspkId, msg.hdr.spkId, msg.hdr.ekAPk) = true
  · have hkm' : ((k : Nat), msg.hdr.pqspkId, msg.hdr.spkId, msg.hdr.ekAPk) ∈
        st.base.seenKyberBaseKeys := by
      simpa using hkm
    simp [hkm', authRespToVal]
  simp only [hkm, Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.false_or]
  cases c1
  · simp [authRespToVal]
  cases c2
  · simp [authRespToVal]
  simp only [Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte, map_bind]
  refine bind_congr' (by rfl_hx) (fun ss? => ?_)
  rcases ss? with _ | ss
  · simp [authRespToVal]
  simp only [map_bind, bind_map_left, map_pure, pure_bind, Option.map_none,
    valToFgPos_fgPosToVal]
  refine bind_congr' (by rfl_hx) (fun p1 => ?_)
  refine bind_congr' (by rfl_hx) (fun p2 => ?_)
  refine bind_congr' (by rfl_hx) (fun p3 => ?_)
  refine bind_congr' (by rw [agList_fgPatchEntry_roundtrip']) (fun dkL => ?_)
  refine bind_congr' (by rfl_hx) (fun pR => ?_)
  refine bind_congr' (by rw [agList_rootEntry_roundtrip']; rfl) (fun rkOut => ?_)
  refine bind_congr' (by rfl_hx) (fun mkSeed => ?_)
  refine bind_congr' (by rfl_hx) (fun ck1 => ?_)
  refine bind_congr' (by rfl_hx) (fun spqr? => ?_)
  rcases spqr? with _ | spqr
  · simp [authRespToVal]
  simp only [map_bind]
  refine bind_congr' (by rfl_hx) (fun mk => ?_)
  refine bind_congr'
    (agR_aeadDec_congr rfl
      (by rw [firstMsgADE_evalHs]; simp [Expr.eval, firstMsgAD, encodeEC, pbBytesField,
        principalEntryToVal])
      (by rfl_hx))
    (fun pt? => ?_)
  rcases pt? with _ | pt
  · simp [authRespToVal]
  simp only [map_bind]
  rw [findHonestC_eval S _ st.base _ (hst := by
    simp only [Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz]) (hPrin := hB.base.principals_le)]
  simp only [embedPrim_map, bind_map_left, Expr.eval, Env.get_vs, Env.get_vz]
  rw [← agFindHonest_eq]
  refine bind_congr' (by rfl_hx) (fun sp => ?_)
  rcases sp with _ | sp <;>
  · simp only [Option.map_none, Option.map_some, map_pure, authRespToVal, authRenc,
      drKeyToVal, drKeyV, fgSimToVal, authStateToVal, List.map_cons]

theorem fgRecvB_eval_opk (U V : Bytes) (useDh1 : Bool) (t sIdx : Nat)
    (sim : Var Γ₁ fgSimTy) (x : Var Γ₂ recvQTy)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hsim : Env.get env (h₁.wk sim) = fgSimToVal st)
    (hx : Env.get env (h₂.wk x) = (k.val, (j.val, (o.val, preKeyMsgToVal msg))))
    (hB : AgBnd K st) :
    (fgRecvB S K true sim x).eval env =
      (fun r => (authRespToVal r.1, fgSimToVal r.2)) <$>
        fgAuthStep useDh1 t sIdx S K U V (.recvOPK k j o msg) st := by
  have hx' : @Env.get pqSig Δ (.prod .nat (.prod .nat (.prod .nat preKeyMsgTy))) env
      (@Ext.wk Γ₂ Δ h₂ (.prod .nat (.prod .nat (.prod .nat preKeyMsgTy))) x) =
      (k.val, (j.val, (o.val, preKeyMsgToVal msg))) := hx
  simp only [fgRecvB, letV, Comp.eval_letC]
  refine (agR_recvC_opk S K _
    { st with respRecs :=
        { bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk := msg.hdr.ekAPk } ::
        st.respRecs } Var.vz x k j o msg ?_ ?_ ⟨hB.base, hB.raw_le, hB.pows_le⟩).trans ?_
  · simp only [v, Expr.eval, Ext.refl_wk, Env.get_vz, hsim, hx', fgSimToVal,
      preKeyMsgToVal, preKeyMsgV, hdrV, respRecToVal, List.map_cons]
  · simp only [Ext.step_wk, Env.get_vs, hx']
  · simp only [fgAuthStep]

theorem fgRecvB_eval_noopk (U V : Bytes) (useDh1 : Bool) (t sIdx : Nat)
    (sim : Var Γ₁ fgSimTy) (x : Var Γ₂ recvQTy)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hsim : Env.get env (h₁.wk sim) = fgSimToVal st)
    (hx : Env.get env (h₂.wk x) = (k.val, (j.val, (l.val, preKeyMsgToVal msg))))
    (hB : AgBnd K st) :
    (fgRecvB S K false sim x).eval env =
      (fun r => (authRespToVal r.1, fgSimToVal r.2)) <$>
        fgAuthStep useDh1 t sIdx S K U V (.recvNoOPK k j l msg) st := by
  have hx' : @Env.get pqSig Δ (.prod .nat (.prod .nat (.prod .nat preKeyMsgTy))) env
      (@Ext.wk Γ₂ Δ h₂ (.prod .nat (.prod .nat (.prod .nat preKeyMsgTy))) x) =
      (k.val, (j.val, (l.val, preKeyMsgToVal msg))) := hx
  simp only [fgRecvB, letV, Comp.eval_letC]
  refine (agR_recvC_noopk S K _
    { st with respRecs :=
        { bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk := msg.hdr.ekAPk } ::
        st.respRecs } Var.vz x k j l msg ?_ ?_ ⟨hB.base, hB.raw_le, hB.pows_le⟩).trans ?_
  · simp only [v, Expr.eval, Ext.refl_wk, Env.get_vz, hsim, hx', fgSimToVal,
      preKeyMsgToVal, preKeyMsgV, hdrV, respRecToVal, List.map_cons]
  · simp only [Ext.step_wk, Env.get_vs, hx']
  · simp only [fgAuthStep]

end Recv

end SignalPqxdh.Security.ReductionDsl.AuthHs
