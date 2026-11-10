/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndCoreSim
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Potential
import VCVio.EvalDist.Monad.Basic

/-!
# `KeyInd` Core Handler: Bounded-State Preservation

Proves that one shallow `pqxdhKeyIndImplPrim` query grows every state list by at most one entry.
-/

@[expose] public section

set_option autoImplicit false
open SignalPqxdh SignalPqxdh.Security
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyInd

theorem KeyIndListsBounded.mono {S : Setup} {n m : Nat} {s : KeyIndState S} (h : n ≤ m)
    (hB : KeyIndListsBounded s n) : KeyIndListsBounded s m :=
  ⟨le_trans hB.1 h, le_trans hB.2 h, le_trans hB.3 h, le_trans hB.4 h, le_trans hB.5 h,
    le_trans hB.6 h, le_trans hB.7 h, le_trans hB.8 h, le_trans hB.9 h, le_trans hB.10 h⟩

theorem evalHkdfOrRoPrim_hol' (useRo : Bool) (c : List (Bytes × DRKey)) (sec : Bytes) :
    HoldsOnLeaves (fun x => x.2.length ≤ c.length + 1) (evalHkdfOrRoPrim useRo c sec) := by
  unfold evalHkdfOrRoPrim
  split
  · exact HoldsOnLeaves.bind_const _ (fun _ => HoldsOnLeaves.pure (by simp))
  · split
    · exact HoldsOnLeaves.pure (by simp)
    · exact HoldsOnLeaves.bind_const _ (fun _ => HoldsOnLeaves.pure (by simp))

theorem checkAndMarkKyberUsed_length' (l : List (Nat × KeyId × KeyId × Bytes)) (k : Nat)
    (a b : KeyId) (e : Bytes) : (checkAndMarkKyberBaseKeySeen l k a b e).2.length ≤ l.length + 1 := by
  simp only [checkAndMarkKyberBaseKeySeen]; split <;> simp

section StApply
variable {σ α β : Type} {m : Type → Type} [Monad m]
theorem kstApply_pure (a : α) (s : σ) : (pure a : StateT σ m α) s = pure (a, s) := rfl
theorem kstApply_bind (x : StateT σ m α) (f : α → StateT σ m β) (s : σ) :
    (x >>= f) s = x s >>= fun p => f p.1 p.2 := rfl
theorem kstApply_set (s' s : σ) : (set s' : StateT σ m PUnit) s = pure (⟨⟩, s') := rfl
theorem kstApply_get (s : σ) : (get : StateT σ m σ) s = pure (s, s) := rfl
theorem kstApply_lift (x : m α) (s : σ) :
    (monadLift x : StateT σ m α) s = x >>= fun a => pure (a, s) := rfl
end StApply

theorem hol_run_pure {σ α : Type} {P : α × σ → Prop} (a : α) (s : σ) (h : P (a, s)) :
    HoldsOnLeaves P ((pure a : StateT σ (OracleComp PrimBaseSpec) α).run s) :=
  HoldsOnLeaves.pure h

macro "khol_leaf" : tactic => `(tactic| (constructor <;> (try dsimp only) <;>
  (try simp only [List.length_cons, List.length_map]) <;>
  first | omega | exact le_trans (checkAndMarkKyberUsed_length' _ _ _ _ _) (by omega)))

macro "khol_simp" : tactic => `(tactic| simp only [StateT.run_bind, StateT.run_monadLift,
  StateT.run_pure, StateT.run_set, StateT.run_get, bind_assoc, pure_bind, liftM, monadLift_self,
  kstApply_pure, kstApply_bind, kstApply_set, kstApply_get, kstApply_lift])

theorem recordKeyIndRespPrim_hol (S : Setup) (n : Nat) (s : KeyIndState S)
    (r : KeyIndRespEntry S) (hK : KeyIndListsBounded s (n + 1)) (hR : s.respSessions.length ≤ n) :
    HoldsOnLeaves (fun x => KeyIndListsBounded x.2 (n + 1))
      ((recordKeyIndRespPrim S r).run s) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hK
  simp only [recordKeyIndRespPrim]
  try khol_simp
  refine HoldsOnLeaves.bind_const _ (fun found => ?_)
  rcases found with _ | e <;> try khol_simp
  · refine HoldsOnLeaves.bind_const _ (fun _ => ?_)
    try khol_simp
    refine HoldsOnLeaves.pure ?_
    khol_leaf
  · refine HoldsOnLeaves.pure ?_
    khol_leaf

theorem recordKeyIndRespPrim_bind_hol {β : Type} (S : Setup) (m : Nat) (s : KeyIndState S)
    (r : KeyIndRespEntry S)
    (k : Unit × KeyIndState S → OracleComp PrimBaseSpec (β × KeyIndState S))
    (hK : KeyIndListsBounded s m) (hR : s.respSessions.length + 1 ≤ m)
    (hk : ∀ p, KeyIndListsBounded p.2 m →
      HoldsOnLeaves (fun x => KeyIndListsBounded x.2 m) (k p)) :
    HoldsOnLeaves (fun x => KeyIndListsBounded x.2 m) ((recordKeyIndRespPrim S r).run s >>= k) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact HoldsOnLeaves.bind (recordKeyIndRespPrim_hol S n s r hK (by omega)) hk

macro "khol_full" : tactic => `(tactic| repeat (first
    | khol_simp
    | (refine HoldsOnLeaves.pure ?_; first | assumption | khol_leaf)
    | (refine hol_run_pure _ _ ?_; first | assumption | khol_leaf)
    | (refine HoldsOnLeaves.bind (evalHkdfOrRoPrim_hol' _ _ _) (fun _ _ => ?_))
    | (refine recordKeyIndRespPrim_bind_hol _ _ _ _ _ (by khol_leaf) (by (try dsimp only); omega)
        (fun _ _ => ?_))
    | (refine HoldsOnLeaves.bind_const _ (fun _ => ?_))
    | split))

set_option maxHeartbeats 1000000 in
theorem runKeyIndInitiatePrim_hol (useRo : Bool) (S : Setup) (n : Nat) (s : KeyIndState S)
    (hK : KeyIndListsBounded s n) (sid : SessionId S) (u : Fin S.N_id) (b : PreKeyBundleInput) :
    HoldsOnLeaves (fun x => KeyIndListsBounded x.2 (n + 1))
      ((runKeyIndInitiatePrim useRo S sid u b).run s) := by
  have hK' := hK
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hK'
  simp only [runKeyIndInitiatePrim]
  khol_full

set_option maxHeartbeats 1000000 in
theorem pqxdhKeyIndImplPrim_hol (useRo : Bool) (S : Setup) (n : Nat) (q : KeyIndQuery S)
    (s : KeyIndState S) (hK : KeyIndListsBounded s n) :
    HoldsOnLeaves (fun x => KeyIndListsBounded x.2 (n + 1))
      ((pqxdhKeyIndImplPrim useRo S q).run s) := by
  have hK' := hK
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hK'
  cases q with
  | initiateOPK u i b =>
    simp only [pqxdhKeyIndImplPrim]
    khol_simp
    split
    · exact hol_run_pure _ _ (hK.mono (Nat.le_succ n))
    · exact runKeyIndInitiatePrim_hol useRo S n s hK _ u b
  | initiateNoOPK u i b =>
    simp only [pqxdhKeyIndImplPrim]
    khol_simp
    split
    · exact hol_run_pure _ _ (hK.mono (Nat.le_succ n))
    · exact runKeyIndInitiatePrim_hol useRo S n s hK _ u b
  | _ => simp only [pqxdhKeyIndImplPrim]; khol_full

end SignalPqxdh.Security.ReductionDsl.KeyInd
