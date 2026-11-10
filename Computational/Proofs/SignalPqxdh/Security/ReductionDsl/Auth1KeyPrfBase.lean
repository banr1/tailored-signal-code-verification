/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfSharedEval
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-Key `initPrin` Block for `Auth` `ReductionDsl` Programs

Defines the one-key `.initPrin` handler `initPrin1KeyFixedB` and proves its evaluation equivalence,
leaf invariant, and static cost and query bounds relative to the two-key block `initPrinFixedB`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
namespace SignalPqxdh.Security.ReductionDsl.AuthPrf

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh
open SignalPqxdh.LegacyCosted
open SignalPqxdh.Security
open SignalPqxdh.Security.AuthSubHops1to3
open RoKem
open FgGapDh
open OracleSpec OracleComp

def AuthQuery.NotInitPrin {S : Setup} (q : AuthQuery S) : Prop :=
  ∀ u, q ≠ .initPrin u

theorem stepAuthOtherPrim1Key_eq_of_ne {S : Setup} (q : AuthQuery S)
    (hq : AuthQuery.NotInitPrin q) (hst : AuthHybridStateFixed S) :
    AuthSubHops1to3.stepAuthOtherPrim1Key S q hst = AuthSubHops1to3.stepAuthOtherPrim S q hst := by
  cases q <;> first | rfl | exact absurd rfl (hq _)

theorem authCkStepWithPrim1Key_eq_of_ne {S : Setup}
    (sampAt : Nat → OracleComp PrimBaseSpec (Bytes × Bytes)) (q : AuthQuery S)
    (hq : AuthQuery.NotInitPrin q) (hst : AuthHybridStateFixed S) :
    AuthSubHops1to3.authCkStepWithPrim1Key S sampAt q hst =
      AuthSubHops1to3.authCkStepWithPrim S sampAt q hst := by
  cases q <;> first | rfl | exact absurd rfl (hq _)

section Auth1KeyInitPrin

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}

/-- One-key `initPrin` block using a single scalar for both identity and signing keys. -/
def initPrin1KeyFixedB (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ RSF :=
  letV (ahsBase (ahsfHybrid (v fhst))) fun st =>
  .ite (asHasWonAuth (v st)) (.ret (.pair aNone (v fhst))) <|
  .ite (eAny K (asPrincipals (v st)) fun e => natEq (.fst (v e)) (v u))
    (.ret (.pair aNone (v fhst))) <|
  bindV (samplePrim .bytes32) fun s0 => bindV (queryPrim .x25519Base (v s0)) fun ik =>
  .ret (.pair (aInitPrin (v ik) (v ik))
    (fhstSetBase (v fhst) (stUpd (v st) (prin := .cons
      (.pair (v u) (peMk (v s0) (v ik) (v s0) (v ik) (.bool false))) (asPrincipals (v st))))))

theorem initPrin1KeyFixedB_eval (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (s : AuthHybridStateFixed S) (uv : Fin S.N_id)
    (hs : Env.get env (h₁.wk fhst) = authHybridStateFixedToVal s)
    (hu : Env.get env (h₂.wk u) = uv.val)
    (hB : AuthListsBounded K s) :
    (initPrin1KeyFixedB K fhst u).eval env =
      Prod.map authRespToVal authHybridStateFixedToVal <$>
        AuthSubHops1to3.stepAuthOtherPrim1Key S (.initPrin uv) s := by
  have hTakeP :
      (s.toAuthHybridState.base.principals.map (Prod.map id principalEntryToVal)).take K =
      s.toAuthHybridState.base.principals.map (Prod.map id principalEntryToVal) := by
    apply List.take_of_length_le; simpa using hB.principals_le
  simp only [initPrin1KeyFixedB, letV, bindV, eAny, v, ahsBase, ahsfHybrid,
    asHasWonAuth, asPrincipals, aNone, aInitPrin, fhstSetBase, ahsfUpd, ahsfMkSlots,
    ahsfRecvCount, ahsfMkSaltCache, ahsfSlots, ahsUpd, ahsMk, ahsInitKemRecs, ahsRecvKemRecs,
    ahsIdealSessions, stUpd, stMk, asSecb, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys, peMk, natEq_eval, eval_letC,
    samplePrim_bytes32_eval, queryPrim_eval, evalPrimQ,
    Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
    hs, hu, authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal,
    authHybridStateToVal, authStateToVal,
    hTakeP, List.any_map, Function.comp_def, Prod.map, id_eq,
    AuthSubHops1to3.stepAuthOtherPrim1Key, sampleScalar32,
    map_eq_bind_pure_comp]
  cases hWon : s.toAuthHybridState.base.hasWonAuth with
  | true => simp [hWon, authRespToVal, authRenc]
  | false =>
    cases hAny : s.toAuthHybridState.base.principals.any (fun x => x.1 == uv.val) <;>
      simp [hWon, authRespToVal, authRenc]

theorem initPrin1KeyFixedB_cost_le (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initPrin1KeyFixedB (Δ := Δ) K fhst u).cost ≤ (initPrinFixedB (Δ := Δ) K fhst u).cost := by
  simp only [initPrin1KeyFixedB, initPrinFixedB, letV, bindV, Comp.letC, samplePrim, queryPrim,
    Comp.cost, fhstSetBase, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    ahsfMkSlots, ahsfUpd,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsMk, ahsUpd,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys, stMk, stUpd, peMk, aNone, aInitPrin, v, Expr.cost]
  omega

theorem initPrin1KeyFixedB_queries_le (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (w : pqPrimIface.Tag → ℕ) (ws : pqPrimIface.smp.Samp → ℕ) :
    (initPrin1KeyFixedB (Δ := Δ) K fhst u).queries w ws ≤
      (initPrinFixedB (Δ := Δ) K fhst u).queries w ws := by
  simp only [initPrin1KeyFixedB, initPrinFixedB, letV, bindV, Comp.letC, samplePrim, queryPrim,
    Comp.queries]
  omega

end Auth1KeyInitPrin

theorem stepAuthOtherPrim1Key_bounded {S : Setup} {n : Nat}
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (hB : AuthListsBounded n hst) :
    AllLeaves (fun p => AuthListsBounded (n + 1) p.2)
      (AuthSubHops1to3.stepAuthOtherPrim1Key S q hst) := by
  have hB' : AuthListsBounded (n + 1) hst := hB.mono (Nat.le_succ n)
  cases q with
  | initPrin u =>
    unfold AuthSubHops1to3.stepAuthOtherPrim1Key; dsimp only
    refine AllLeaves.ite hst.toAuthHybridState.base.hasWonAuth
      (fun _ => AllLeaves.pure hB') (fun _ => ?_)
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure hB') (fun _ => ?_)
    refine AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ => ?_))
    rcases hB' with ⟨hHB', hSalt'⟩
    cases hHB'
    refine AllLeaves.pure ⟨?_, hSalt'⟩
    constructor <;> first | (simp only [List.length_cons]; exact Nat.succ_le_succ hB.principals_le) | assumption
  | corruptIK u => exact stepAuthOtherPrim_bounded (.corruptIK u) hst hB
  | genSPK u j => exact stepAuthOtherPrim_bounded (.genSPK u j) hst hB
  | genOPK u j o => exact stepAuthOtherPrim_bounded (.genOPK u j o) hst hB
  | sendOPK u i bundle m0 m1 => exact stepAuthOtherPrim_bounded (.sendOPK u i bundle m0 m1) hst hB
  | sendNoOPK u i bundle m0 m1 =>
    exact stepAuthOtherPrim_bounded (.sendNoOPK u i bundle m0 m1) hst hB
  | recvOPK k j o msg => exact stepAuthOtherPrim_bounded (.recvOPK k j o msg) hst hB
  | recvNoOPK k j l msg => exact stepAuthOtherPrim_bounded (.recvNoOPK k j l msg) hst hB
  | roQuery sec => exact stepAuthOtherPrim_bounded (.roQuery sec) hst hB
  | roRootQuery rk dh => exact stepAuthOtherPrim_bounded (.roRootQuery rk dh) hst hB
  | revealDhSecrets => exact stepAuthOtherPrim_bounded .revealDhSecrets hst hB
  | registerKey sk => exact stepAuthOtherPrim_bounded (.registerKey sk) hst hB

end SignalPqxdh.Security.ReductionDsl.AuthPrf
