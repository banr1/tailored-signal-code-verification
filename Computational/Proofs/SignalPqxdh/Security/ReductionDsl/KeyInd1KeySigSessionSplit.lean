/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhSessionSplit
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeySigBounds

/-!
# Session-Split Primitive-Query Bound for `sigKeyInd1KeyProg`

**Checked by Lean.** Proves the `gdhPrimQueryBudget S b` primitive-query bound for
`sigKeyInd1KeyProg` via `CostedReduction.queryBound_eval₂`, separating the four session arms from
non-session arms that make at most `32` primitive queries.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyInd

open SignalPqxdh.Security.ReductionDsl.KeyIndGapDh

/-- Variant of `sig1KeyPreDispatchC` with the initiator signature-check arms replaced by `.inr ()`. -/
def sig1KeyPreDispatchNSC (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ sig1KeyStTy) (q : Var Γ₂ keyIndQueryTy) :
    Comp pqxdhOps pqSigAndDdhIface Δ (.sum S1RS .unit) :=
  .ite (isSomeE (s1Forgery (v s))) (.ret (.inl (.pair rNone (v s)))) <|
  caseSumV (v q) (fun u => bindV (sig1KeyInitPrinB K s u) fun r => .ret (.inl (v r))) fun q =>
  caseSumV (v q) (fun _ => .ret (.inr .unit)) fun q =>
  caseSumV (v q)
    (fun x => .ite (natEq (.fst (v x)) (s1Target (v s)))
      (bindV (sig1KeyTargetGenSpkB K s x) fun r => .ret (.inl (v r)))
      (.ret (.inr .unit))) fun q =>
  caseSumV (v q) (fun _ => .ret (.inr .unit)) fun q =>
  caseSumV (v q) (fun _ => .ret (.inr .unit)) fun q =>
  caseSumV (v q) (fun _ => .ret (.inr .unit)) fun _ =>
  .ret (.inr .unit)

/-- Variant of `gdhHandle2` with the four session arms replaced by no-ops. -/
def gdhHandle2NS (_S : Setup) (K : Nat) :
    Comp pqxdhOps pqGapDhIface [gdhState2Ty, keyIndQueryTy] (.prod keyIndRespTy gdhState2Ty) :=
  let st : Var [gdhState2Ty, keyIndQueryTy] gdhState2Ty := .zero
  let q : Var [gdhState2Ty, keyIndQueryTy] keyIndQueryTy := .succ .zero
  letV (.fst (v st)) fun pa =>
  letV (.snd (v st)) fun sm =>
  letV (smBase (v sm)) fun bSt =>
  caseSumV (v q) (fun u => wrapSim2 pa (initPrinGdh2B K pa sm bSt u)) fun r1 =>
  caseSumV (v r1) (fun u => wrapBase2 pa sm (corruptB K bSt u)) fun r2 =>
  caseSumV (v r2) (fun x => wrapSim2 pa (genSpkGdh2B K pa sm bSt x)) fun r3 =>
  caseSumV (v r3) (fun x => wrapSim2 pa (genOpkGdh2B K pa sm bSt x)) fun r4 =>
  caseSumV (v r4) (fun _ => .ret (.pair rNone (v st))) fun r5 =>
  caseSumV (v r5) (fun _ => .ret (.pair rNone (v st))) fun r6 =>
  caseSumV (v r6) (fun _ => .ret (.pair rNone (v st))) fun r7 =>
  caseSumV (v r7) (fun _ => .ret (.pair rNone (v st))) fun r8 =>
  caseSumV (v r8) (fun sid => wrapBase2 pa sm (testB K bSt sid)) fun r9 =>
  caseSumV (v r9) (fun sec => wrapSim2 pa (roParsedC K sm sec)) fun r10 =>
  caseSumV (v r10) (fun _ => .ret (.pair rNone (v st))) fun r11 =>
  caseSumV (v r11) (fun sid => wrapBase2 pa sm (revealB K bSt sid)) fun r12 =>
  caseSumV (v r12) (fun sk => wrapSim2 pa (registerGdhB sm bSt sk))
                   (fun x => wrapBase2 pa sm (revealSpkB K bSt x))

/-- `delegateFgC` with `gdhHandle2NS` in place of `gdhHandle2`. -/
def delegateFgNSC (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ sig1KeyStTy) (q : Var Γ₂ keyIndQueryTy) :
    Comp pqxdhOps pqSigAndDdhIface Δ S1RS :=
  letV (.pair (pa2Zero (s1Pk (v s))) (s1Fg (v s))) fun gdhSt =>
  bindV (liftGdhToSigDdh ((gdhHandle2NS S K).rename
      (renamePair gdhSt (.succ (Ext.wk q))))) fun r =>
  .ret (.pair (.fst (v r)) (s1Upd (v s) (fg := .snd (.snd (v r)))))

/-- Variant of `sig1KeyHandleC` with the session arms replaced by no-ops, used to bound
    non-session primitive queries. -/
def sig1KeyHandleNSC (S : Setup) (K : Nat) :
    Comp pqxdhOps pqSigAndDdhIface [sig1KeyStTy, keyIndQueryTy] S1RS :=
  let s : Var [sig1KeyStTy, keyIndQueryTy] sig1KeyStTy := .zero
  let q : Var [sig1KeyStTy, keyIndQueryTy] keyIndQueryTy := .succ .zero
  bindV (sig1KeyPreDispatchNSC K s q) fun pre =>
  caseSumV (v pre) (fun res => .ret (v res)) fun _ =>
  delegateFgNSC S K s q

theorem gdhHandleNS_primUB16 (S : Setup) (K : Nat) :
    (KeyInd1KeyGapDh.gdhHandleNS S K).queriesUB wPrimGdh KeyIndGapDh.wsZero ≤ 16 := by
  simp only [KeyInd1KeyGapDh.gdhHandleNS, initPrinGdhB, corruptB, genSpkGdhB, genOpkGdhB,
    testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    wrapBase_primUB, wrapSim_primUB,
    letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB, caseSumV_queriesUB,
    gPrim_queriesUB_wPrimGdh, mkSecretPosC_primUB, fgPatchC_primUB,
    sBytes32_queriesUB, sRandom64_queriesUB, sDrKey96_queriesUB,
    qX25519Base_queriesUB, qPow8_queriesUB, qSigPkGen_queriesUB, qSigSign_queriesUB,
    qKemKeyGen_queriesUB, Comp.queriesUB]
  omega

private theorem gdhHandle2NS_primUB16 (S : Setup) (K : Nat) :
    (gdhHandle2NS S K).queriesUB wPrimGdh KeyIndGapDh.wsZero ≤ 16 := by
  have hwBase : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
      (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
      (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)),
      (wrapBase2 pa sm c).queriesUB wPrimGdh KeyIndGapDh.wsZero =
        c.queriesUB wPrimBase KeyIndGapDh.wsZeroBase := by
    intro _ _ _ _ _ pa sm c
    simp [wrapBase2, bindV_queriesUB, gPrim_queriesUB_wPrimGdh, Comp.queriesUB]
  have hwSim : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
      (pa : Var Γ₁ params2Ty) (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)),
      (wrapSim2 pa c).queriesUB wPrimGdh KeyIndGapDh.wsZero =
        c.queriesUB wPrimGdh KeyIndGapDh.wsZero := by
    intro _ _ _ pa c
    simp [wrapSim2, bindV_queriesUB, Comp.queriesUB]
  simp only [gdhHandle2NS, initPrinGdh2B, corruptB, genSpkGdh2B, genOpkGdh2B,
    testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    hwBase, hwSim,
    letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB, caseSumV_queriesUB,
    gPrim_queriesUB_wPrimGdh, mkSecretPosC_primUB, fgPatchC_primUB,
    sBytes32_queriesUB, sRandom64_queriesUB, sDrKey96_queriesUB,
    qX25519Base_queriesUB, qPow8_queriesUB, qSigPkGen_queriesUB, qSigSign_queriesUB,
    qKemKeyGen_queriesUB, Comp.queriesUB]
  omega

section
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] pqChalIface pqPrimIface gapDhDdhOracle sigAndDdhOracle
  pqSamplers

theorem sig1KeyHandleNSC_primUB (S : Setup) (K : Nat) :
    (sig1KeyHandleNSC S K).queriesUB SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ≤ 32 := by
  have h16 := gdhHandle2NS_primUB16 S K
  simp only [sig1KeyHandleNSC, sig1KeyPreDispatchNSC, delegateFgNSC, sig1KeyInitPrinB,
    sig1KeyTargetGenSpkB,
    letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB, caseSumV_queriesUB,
    s1Prim_primUB, qSigDdhSign_primUB, liftGdhToSigDdh_primUB, Comp.rename_queriesUB,
    sBytes32_queriesUB, sRandom64_queriesUB, qX25519Base_queriesUB, qKemKeyGen_queriesUB,
    Comp.queriesUB]
  omega

theorem sig1KeyHandleNSC_primQueries_le (S : Setup) (K : Nat) :
    (sig1KeyHandleNSC S K).queries SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ≤ 32 :=
  (Comp.queries_le_queriesUB _ _ _).trans (sig1KeyHandleNSC_primUB S K)

theorem sigKeyInd1KeyProg_init_queries_prim (S : Setup) (K : Nat) :
    (sigKeyInd1KeyProg S K).init.queries SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 := by
  simp [sigKeyInd1KeyProg, sIndex, sBool, Comp.queries]

theorem sigKeyInd1KeyProg_finish_queries_prim (S : Setup) (K : Nat) :
    (sigKeyInd1KeyProg S K).finish.queries SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 := by
  simp [sigKeyInd1KeyProg, Comp.queries]

end

section
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] Env.get Ext.wk

theorem sig1KeyHandleC_eval_NS (S : Setup) (K : Nat) (q : KeyIndQuery S)
    (hq : KeyInd1KeyGapDh.isSessionQ q = false) (st : sig1KeyStTy.denote) :
    (sig1KeyHandleC S K).eval (.cons st (.cons (keyIndQenc q) .nil)) =
      (sig1KeyHandleNSC S K).eval (.cons st (.cons (keyIndQenc q) .nil)) := by
  cases q <;> simp only [KeyInd1KeyGapDh.isSessionQ, Bool.true_eq_false] at hq <;> rfl

set_option allowUnsafeReducibility true in
attribute [local semireducible] Env.get Ext.wk
end

theorem sig1KeyHandleC_primBound_heavy (S : Setup) (K : Nat) (s : sig1KeyStTy.denote)
    (t : KeyIndQuery S) :
    ((sig1KeyHandleC S K).eval (.cons s (.cons (keyIndQenc t) .nil))).IsQueryBoundP
      (fun q => isPrimQuery q = true) (16 * (5 * S.N_dh + S.N_sess_tot + 12)) :=
  KeyInd1KeyGapDh.comp_primBound _ _ ((sig1KeyHandleC_primQueries_le S K).trans (by omega))

theorem sig1KeyHandleC_primBound_light (S : Setup) (K : Nat) (s : sig1KeyStTy.denote)
    (t : KeyIndQuery S) (ht : KeyInd1KeyGapDh.isSessionQ t = false) :
    ((sig1KeyHandleC S K).eval (.cons s (.cons (keyIndQenc t) .nil))).IsQueryBoundP
      (fun q => isPrimQuery q = true) 32 := by
  rw [sig1KeyHandleC_eval_NS S K t ht s]
  exact KeyInd1KeyGapDh.comp_primBound _ _ (sig1KeyHandleNSC_primQueries_le S K)

private theorem split_arith_sig (q k X : ℕ) (hk : k ≤ q) (hX : 2 ≤ X) :
    0 + (q * 32 + k * (16 * X - 32)) + 0 ≤ 32 * (q - k) + 16 * (k + 1) * X := by
  obtain ⟨r, rfl⟩ : ∃ r, q = k + r := ⟨q - k, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d, 16 * X = 32 + d := ⟨16 * X - 32, by omega⟩
  have h1 : 16 * X - 32 = d := by omega
  have h2 : k + r - k = r := by omega
  have h3 : 16 * (k + 1) * X = (k + 1) * (32 + d) := by rw [← hd]; ring
  rw [h1, h2, h3]
  nlinarith

/-- Two-class primitive-query bound for `sigKeyInd1KeyProg` given `q` total game queries and
    `m` session queries. -/
theorem sigKeyInd1KeyProg_primBounded_split (S : Setup) (K q m : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (_root_.ReductionDsl.isGameQuery (G := keyIndSpec S)) q)
    (hAH : ∀ a, (A a).IsQueryBoundP
      (_root_.ReductionDsl.onGame (G := keyIndSpec S)
        (fun t => KeyInd1KeyGapDh.isSessionQ t = true)) m)
    (pk : Bytes) :
    ((sigKeyInd1KeyProg S K).eval A pk).IsQueryBoundP
      (fun q => isPrimQuery q = true)
      (32 * (q - min q m) + 16 * (min q m + 1) * (5 * S.N_dh + S.N_sess_tot + 12)) := by
  refine (CostedReduction.queryBound_eval₂ (sigKeyInd1KeyProg S K)
    (fun q => isPrimQuery q = true)
    SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
    SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ?_ ?_
    (fun t => KeyInd1KeyGapDh.isSessionQ t = true) (kL := 32)
    (kH := 16 * (5 * S.N_dh + S.N_sess_tot + 12))
    (by omega) (fun t s _ => sig1KeyHandleC_primBound_heavy S K s t)
    (fun t s ht => sig1KeyHandleC_primBound_light S K s t (by simpa using ht))
    A q m hA hAH pk).mono ?_
  · intro g x hx
    rcases g with t | c
    · simp [SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]
    · simp [pqSigAndDdhIface, pqChalIface, isPrimQuery] at hx
  · intro n
    change IsQueryBoundP
      (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhSpec) (.inl (.inl n))) :
        OracleComp (PrimBaseSpec + sigAndDdhSpec) _)
      (fun q => isPrimQuery q = true) 0
    rw [isQueryBoundP_query_iff]
    simp [isPrimQuery]
  · rw [sigKeyInd1KeyProg_init_queries_prim, sigKeyInd1KeyProg_finish_queries_prim]
    exact split_arith_sig q (min q m) _ (min_le_left _ _) (by omega)

/-- Evaluating `sigKeyInd1KeyProg S K` on a `b`-bounded `KeyInd` adversary makes at most
    `gdhPrimQueryBudget S b` primitive queries. -/
theorem sigKeyInd1KeyProg_primBounded_gdhPrimQueryBudget (S : Setup) (K : Nat)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) (pk : Bytes) :
    ((sigKeyInd1KeyProg S K).eval (fun _ => A.1.run) pk).IsQueryBoundP
      (fun q => isPrimQuery q = true) (gdhPrimQueryBudget S b) :=
  (sigKeyInd1KeyProg_primBounded_split S K b.q_total (min b.q_on S.N_sess_tot) (fun _ => A.1.run)
    (KeyInd1KeyGapDh.keyIndAdv_gameBound S b A)
    (fun _ => KeyInd1KeyGapDh.keyIndAdv_sessionBound_on S b A) pk).mono
    (le_of_eq (KeyInd1KeyGapDh.split_prim_eq_gdhPrimQueryBudget S b))

end SignalPqxdh.Security.ReductionDsl.KeyInd
