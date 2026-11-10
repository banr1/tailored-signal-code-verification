/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSim
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSimSend
import VCVio.EvalDist.Monad.Basic

/-!
# Recv-branch evaluation equivalence for the `Auth` DSL

Proves that `recvB` evaluates to the shallow `pqxdhAuthSimImplPrim` receive branches under
`authRespToVal`, `authStateToVal`, and `AuthBaseListsBounded`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

theorem any_map_contains {α β : Type} [BEq α] (f : α → β) (l : List α) (P : β → Bool) (a : α)
    (hP : ∀ x, P (f x) = (a == x)) : (l.map f).any P = l.contains a := by
  induction l with
  | nil => rfl
  | cons y ys ih => simp only [List.map_cons, List.any_cons, List.contains_cons, hP, ih]

theorem primQ_aeadDec_congr {mk mk' : MessageKeys} {ad ad' ct ct' : Bytes}
    (h1 : mk = mk') (h2 : ad = ad') (h3 : ct = ct') :
    primQ (.aeadDec mk ad ct) = primQ (.aeadDec mk' ad' ct') := by
  subst h1 h2 h3; rfl

section RecvEval

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
  (env : Env Δ) (s : AuthState S)

macro "rfl_hx" : tactic =>
  `(tactic| first | rfl | (rw [$(Lean.mkIdent `hx'):ident]; rfl))

set_option maxHeartbeats 4000000 in
theorem recvB_eval_noopk (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy) (k : Fin S.N_id)
    (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : Env.get env (h₁.wk st) = authStateToVal s)
    (hx : Env.get env (h₂.wk x) = (k.val, (j.val, (l.val, preKeyMsgToVal msg))))
    (hK : AuthBaseListsBounded K s) :
    (recvB S K false st x).eval env =
      Prod.map authRespToVal authStateToVal <$>
        (pqxdhAuthSimImplPrim S (.recvNoOPK k j l msg)).run s := by
  have hx' : Env.get (Γ := Δ) (t := recvQTy) env (Ext.wk (Γ := Γ₂) (Δ := Δ) x) =
      (k.val, (j.val, (l.val, preKeyMsgToVal msg))) := hx
  send_unfold
  simp only [hx]
  simp only [findHonestC_eval S _ s st (hPrin := hK.principals_le),
    koskSenderOkC_eval S K _ s st (hK := hK.advKeys_le) (hPrin := hK.principals_le),
    hkdfOrRoC_eval S K _ s st (hK := hK.roCache_le),
    rootRoC_eval S K _ s st (hK := hK.rootRoCache_le),
    buildSecretsE_eval, Ext.step_wk, Env.get_vs, hst, preKeyMsgToVal, preKeyMsgV, hdrV]
  simp only [Env.get_vs, Env.get_vz, authStateToVal, Expr.eval]
  simp only [pqxdhAuthSimImplPrim, runAuthRecvNoOPKSimPrim, runAuthRecvFinishSimPrim,
    runAuthRecvStep2SimPrim, StateT.run_bind, StateT.run_get, pure_bind, checkAndMarkKyberBaseKeySeen]
  simp only [take_map_of_le _ _ hK.principals_le, take_map_of_le _ _ hK.spkBundles_le,
    take_map_of_le _ _ hK.usedRecvNoOPK_le, take_map_of_le _ _ hK.usedKyberTriples_le]
  rw [any_map_contains _ _ _ (k.val, j.val, l.val)]
  swap
  · rintro ⟨a, b, c⟩
    simp only []
    rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq]
    constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1.symm, h2.symm, h3.symm⟩
  rw [any_map_contains _ _ _ (k.val, msg.hdr.pqspkId, msg.hdr.spkId, msg.hdr.ekAPk)]
  swap
  · rintro ⟨a, b, c, d⟩
    simp only []
    rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq]
  rcases ho : msg.hdr.opkId? with _ | oid
  swap
  · simp [authStateToVal]
  simp only []
  by_cases hg : (msg.hdr.spkId == UInt32.ofNat ↑j && msg.hdr.pqspkId == UInt32.ofNat ↑j && true &&
      List.length msg.hdr.ikAPk == 32 && List.length msg.hdr.ekAPk == 32 &&
      List.length msg.ephAPk == 32) = true
  swap
  · simp only [Bool.and_true] at hg
    simp [hg, authStateToVal]
  simp only [Bool.and_true] at hg
  simp only [Bool.and_true, hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
  by_cases hc : s.usedRecvNoOPK.contains (↑k, ↑j, ↑l) = true
  · have hm : ((k : Nat), (j : Nat), (l : Nat)) ∈ s.usedRecvNoOPK := by simpa using hc
    simp [hm, authStateToVal]
  simp only [hc, Bool.false_eq_true, ↓reduceIte]
  simp [StateT.run_bind, StateT.run_monadLift,
      liftM, monadLift_self, List.find?_map, map_bind, bind_map_left]
  refine bind_congr' (by rfl_hx) (fun ok => ?_)
  cases ok
  · simp [authStateToVal]
  simp only [stRun_ite, map_ite', StateT.run_pure]
  simp only [Bool.true_eq_false, ↓reduceIte]
  rcases hp : List.find? (fun x => x.1 == ↑k) s.principals with _ | ⟨kidx, kE⟩
  · simp [hp, authStateToVal]
  simp only [hp, Option.map_some, Prod.map]
  rcases hb : List.find? (fun x => x.1.1 == ↑k && x.1.2 == ↑j) s.spkBundles with _ | ⟨bidx, bE⟩
  · simp [hb, authStateToVal]
  simp [hb, StateT.run_bind, StateT.run_monadLift, monadLift_self, map_bind]
  refine bind_congr' (by rfl_hx) (fun c1 => ?_)
  refine bind_congr' (by rfl_hx) (fun c2 => ?_)
  by_cases hkm : ((k : Nat), msg.hdr.pqspkId, msg.hdr.spkId, msg.hdr.ekAPk) ∈ s.seenKyberBaseKeys
  · simp [hkm, authStateToVal]
  simp only [hkm, ↓reduceIte]
  by_cases hcc : c1 = false ∨ c2 = false
  · rcases hcc with h | h <;> simp [h, authStateToVal]
  have hcc' : ¬ ((true = false ∨ c1 = false) ∨ c2 = false) := by simpa [or_assoc] using hcc
  rw [ite_eq_right hcc', ite_eq_right hcc']
  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, map_bind, bind_assoc]
  refine bind_congr' (by rfl_hx) (fun ss? => ?_)
  rcases ss? with _ | ss
  · noneclose
  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, map_bind, bind_assoc, pure_bind]
  refine bind_congr' (by rfl_hx) (fun _ => ?_)
  refine bind_congr' (by rfl_hx) (fun _ => ?_)
  refine bind_congr' (by rfl_hx) (fun _ => ?_)
  refine bind_congr' (by simp only [buildSecrets, List.append_assoc]) (fun _ => ?_)
  refine bind_congr' (by rfl_hx) (fun _ => ?_)
  refine bind_congr' (by rfl_hx) (fun _ => ?_)
  refine bind_congr' (by rfl_hx) (fun _ => ?_)
  refine bind_congr' (by rfl_hx) (fun _ => ?_)
  refine bind_congr' (by rfl_hx) (fun _ => ?_)
  rename_i spq
  rcases spq with _ | ⟨pqst, salt⟩
  · noneclose
  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, map_bind, bind_assoc,
    pure_bind]
  refine bind_congr' (by rfl_hx) (fun _ => ?_)
  refine bind_congr'
    (primQ_aeadDec_congr rfl
      (by simp [Expr.eval, Env.get_vs, Env.get_vz, firstMsgAD, encodeEC, pbBytesField, hx'])
      (by rfl_hx))
    (fun pt? => ?_)
  rcases pt? with _ | pt
  · noneclose
  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc,
    pure_bind, map_eq_bind_pure_comp]
  refine bind_congr' (by rfl_hx) (fun snd? => ?_)
  rcases snd? with _ | ⟨sk, sE⟩
  · simp [StateT.run_set, authStateToVal, List.map_cons]
  · simp [StateT.run_set, authStateToVal, List.map_cons]

set_option maxHeartbeats 4000000 in
theorem recvB_eval_opk (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy) (k : Fin S.N_id)
    (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : Env.get env (h₁.wk st) = authStateToVal s)
    (hx : Env.get env (h₂.wk x) = (k.val, (j.val, (o.val, preKeyMsgToVal msg))))
    (hK : AuthBaseListsBounded K s) :
    (recvB S K true st x).eval env =
      Prod.map authRespToVal authStateToVal <$>
        (pqxdhAuthSimImplPrim S (.recvOPK k j o msg)).run s := by
  have hx' : Env.get (Γ := Δ) (t := recvQTy) env (Ext.wk (Γ := Γ₂) (Δ := Δ) x) =
      (k.val, (j.val, (o.val, preKeyMsgToVal msg))) := hx
  send_unfold
  simp only [hx]
  simp only [findHonestC_eval S _ s st (hPrin := hK.principals_le),
    koskSenderOkC_eval S K _ s st (hK := hK.advKeys_le) (hPrin := hK.principals_le),
    hkdfOrRoC_eval S K _ s st (hK := hK.roCache_le),
    rootRoC_eval S K _ s st (hK := hK.rootRoCache_le),
    buildSecretsE_eval, Ext.step_wk, Env.get_vs, hst, preKeyMsgToVal, preKeyMsgV, hdrV]
  simp only [Env.get_vs, Env.get_vz, authStateToVal, Expr.eval]
  simp only [pqxdhAuthSimImplPrim, runAuthRecvOPKSimPrim, runAuthRecvFinishSimPrim,
    runAuthRecvStep2SimPrim, StateT.run_bind, StateT.run_get, pure_bind, checkAndMarkKyberBaseKeySeen]
  simp only [take_map_of_le _ _ hK.principals_le, take_map_of_le _ _ hK.spkBundles_le,
    take_map_of_le _ _ hK.usedRecvOPK_le, take_map_of_le _ _ hK.opkEntries_le,
    take_map_of_le _ _ hK.usedKyberTriples_le]
  rw [any_map_contains _ _ _ (k.val, j.val, o.val)]
  swap
  · rintro ⟨a, b, c⟩
    simp only []
    rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq]
    constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1.symm, h2.symm, h3.symm⟩
  rw [any_map_contains _ _ _ (k.val, msg.hdr.pqspkId, msg.hdr.spkId, msg.hdr.ekAPk)]
  swap
  · rintro ⟨a, b, c, d⟩
    simp only []
    rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq]
  rcases ho : msg.hdr.opkId? with _ | oid
  · simp [authStateToVal]
  simp only []
  by_cases hg : (msg.hdr.spkId == UInt32.ofNat ↑j && msg.hdr.pqspkId == UInt32.ofNat ↑j &&
      oid == UInt32.ofNat ↑o && List.length msg.hdr.ikAPk == 32 &&
      List.length msg.hdr.ekAPk == 32 && List.length msg.ephAPk == 32) = true
  swap
  · have hg' : ((((¬msg.hdr.spkId = UInt32.ofNat ↑j ∨ ¬msg.hdr.pqspkId = UInt32.ofNat ↑j) ∨
        ¬oid = UInt32.ofNat ↑o) ∨ ¬List.length msg.hdr.ikAPk = 32) ∨
        ¬List.length msg.hdr.ekAPk = 32) ∨ ¬List.length msg.ephAPk = 32 := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hg; tauto
    simp [hg, authStateToVal]
  simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp only [Bool.and_eq_true, beq_iff_eq] at hg
  by_cases hc : s.usedRecvOPK.contains (↑k, ↑j, ↑o) = true
  · have hm : ((k : Nat), (j : Nat), (o : Nat)) ∈ s.usedRecvOPK := by simpa using hc
    simp [hm, hg, authStateToVal]
  simp only [hc, Bool.false_eq_true, ↓reduceIte]
  simp [StateT.run_bind, StateT.run_monadLift,
      liftM, monadLift_self, List.find?_map, map_bind, bind_map_left, hg]
  refine bind_congr' (by rfl_hx) (fun ok => ?_)
  cases ok
  · simp [authStateToVal]
  simp only [stRun_ite, map_ite', StateT.run_pure]
  simp only [Bool.true_eq_false, ↓reduceIte]
  rcases hp : List.find? (fun x => x.1 == ↑k) s.principals with _ | ⟨kidx, kE⟩
  · simp [hp, authStateToVal]
  simp only [hp, Option.map_some, Prod.map]
  rcases hb : List.find? (fun x => x.1.1 == ↑k && x.1.2 == ↑j) s.spkBundles with _ | ⟨bidx, bE⟩
  · simp [hb, authStateToVal]
  simp only [hb, Option.map_some, Prod.map]
  rcases hoe : List.find? (fun x => x.1.1 == ↑k && (x.1.2.1 == ↑j && x.1.2.2 == ↑o))
      s.opkEntries with _ | ⟨oidx, oE⟩
  · simp [hoe, authStateToVal]
  simp only [hoe, Option.map_some, Prod.map]
  cases hcons : oE.consumed
  swap
  · simp [hcons, opkEntryToVal, authStateToVal]
  simp [hcons, opkEntryToVal, StateT.run_bind, StateT.run_monadLift, monadLift_self, map_bind]
  refine bind_congr' (by rfl_hx) (fun c1 => ?_)
  refine bind_congr' (by rfl_hx) (fun c2 => ?_)
  by_cases hkm :
      ((k : Nat), UInt32.ofNat (j : Nat), UInt32.ofNat (j : Nat), msg.hdr.ekAPk) ∈
        s.seenKyberBaseKeys
  · simp [hkm, authStateToVal]
  simp only [hkm, ↓reduceIte]
  by_cases hcc : c1 = false ∨ c2 = false
  · rcases hcc with h | h <;> simp [h, authStateToVal]
  have hcc' : ¬ ((true = false ∨ c1 = false) ∨ c2 = false) := by simpa [or_assoc] using hcc
  rw [ite_eq_right hcc', ite_eq_right hcc']
  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, map_bind, bind_assoc]
  refine bind_congr' (by rfl_hx) (fun ss? => ?_)
  rcases ss? with _ | ss
  · noneclose
  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, map_bind, bind_assoc, pure_bind]
  refine bind_congr' (by rfl_hx) (fun _ => ?_)
  refine bind_congr' (by rfl_hx) (fun _ => ?_)
  refine bind_congr' (by rfl_hx) (fun _ => ?_)
  refine bind_congr' (by rfl_hx) (fun _ => ?_)
  refine bind_congr' (by simp only [buildSecrets, List.append_assoc]) (fun _ => ?_)
  refine bind_congr' (by rfl_hx) (fun _ => ?_)
  refine bind_congr' (by rfl_hx) (fun _ => ?_)
  refine bind_congr' (by rfl_hx) (fun _ => ?_)
  refine bind_congr' (by rfl_hx) (fun _ => ?_)
  refine bind_congr' (by rfl_hx) (fun _ => ?_)
  rename_i spq
  rcases spq with _ | ⟨pqst, salt⟩
  · noneclose
  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, map_bind, bind_assoc,
    pure_bind]
  refine bind_congr' (by rfl_hx) (fun _ => ?_)
  refine bind_congr'
    (primQ_aeadDec_congr rfl
      (by simp [Expr.eval, Env.get_vs, Env.get_vz, firstMsgAD, encodeEC, pbBytesField, hx'])
      (by rfl_hx))
    (fun pt? => ?_)
  rcases pt? with _ | pt
  · noneclose
  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc,
    pure_bind, map_eq_bind_pure_comp]
  refine bind_congr' (by rfl_hx) (fun snd? => ?_)
  rcases snd? with _ | ⟨sk, sE⟩
  · simp [StateT.run_set, authStateToVal, List.map_cons]
    intro a a1 b b1 _
    split <;> rfl
  · simp [StateT.run_set, authStateToVal, List.map_cons]
    intro a a1 b b1 _
    split <;> rfl

end RecvEval
end SignalPqxdh.Security.ReductionDsl.AuthHs
