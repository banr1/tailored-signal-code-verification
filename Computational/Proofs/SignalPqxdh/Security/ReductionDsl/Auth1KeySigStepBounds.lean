/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeySigTotals
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeProofs

/-!
# Step-Level Bounds for the One-Key `Auth` Sig Program

**Checked by Lean.** Composes the dispatch-layer bounds of `Auth1KeySigBounds` with context-generic
bounds on `a1gStepC` into total cost and query bounds for `sigAuth1KeyProg`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

section
set_option allowUnsafeReducibility true
attribute [implicit_reducible] sigAndDdhOracle gapDhDdhOracle
end

/-- Context-generic cost bound on `a1gStepC`. -/
def A1gStepCostUB (S : Setup) (K c : Nat) : Prop :=
  ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ a1gStTy)
    (q : Var Γ₂ authQueryTy), (a1gStepC S K (Δ := Δ) st q).costUB ≤ c

/-- Context-generic query bound on `a1gStepC` for weight `w`. -/
def A1gStepQueries (S : Setup) (K : Nat) (w : pqSigAndDdhIface.Tag → ℕ) (c : Nat) : Prop :=
  ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ a1gStTy)
    (q : Var Γ₂ authQueryTy),
    (a1gStepC S K (Δ := Δ) st q).queries w SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ≤ c

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}

theorem a1sDelegateC_costUB_le {c : Nat} (hG : A1gStepCostUB S K c)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) :
    (a1sDelegateC S K (Δ := Δ) s q).costUB ≤ c + 1000 := by
  simp only [a1sDelegateC, bindV, letV, Comp.letC, a1sG, a1sMk, a1sTp, a1sTpk, a1sFg,
    v, Comp.costUB, Expr.costUB]
  have := hG (Γ₁ := a1gStTy :: Δ) (Γ₂ := Γ₂) (Δ := a1gStTy :: Δ) Var.vz q
  omega

theorem a1sDelegateC_queries_le (w : pqSigAndDdhIface.Tag → ℕ) {c : Nat}
    (hG : A1gStepQueries S K w c)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) :
    (a1sDelegateC S K (Δ := Δ) s q).queries w SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ≤ c := by
  simp only [a1sDelegateC, bindV, letV, Comp.letC, Comp.queries]
  have := hG (Γ₁ := a1gStTy :: Δ) (Γ₂ := Γ₂) (Δ := a1gStTy :: Δ) Var.vz q
  omega

theorem a1sStepC_costUB_le {c : Nat} (hG : A1gStepCostUB S K c)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) :
    (a1sStepC S K (Δ := Δ) s q).costUB ≤ c + 27000 + 412 * S.N_dh + 8000 * K := by
  have hP := a1sPreC_costUB_le S K (Δ := Δ) s q
  have hD := a1sDelegateC_costUB_le S K hG (Δ := .unit :: (.sum a1sRS .unit) :: Δ) s q
  simp only [a1sStepC, bindV, caseSumV, isSomeE, a1sFg, aNone, v, Comp.costUB, Expr.costUB]
  omega

theorem a1sStepC_queries_le (w : pqSigAndDdhIface.Tag → ℕ) {c p : Nat}
    (hG : A1gStepQueries S K w c)
    (hPre : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ a1sStTy)
      (q : Var Γ₂ authQueryTy),
      (a1sPreC S K (Δ := Δ) s q).queries w SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ≤ p)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) :
    (a1sStepC S K (Δ := Δ) s q).queries w SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ≤ p + c := by
  have hP := hPre (Δ := Δ) s q
  have hD := a1sDelegateC_queries_le S K w hG (Δ := .unit :: (.sum a1sRS .unit) :: Δ) s q
  simp only [a1sStepC, bindV, caseSumV, Comp.queries]
  omega

/-! ## Bridges from `a1gStep2C` to `a1gStepC` -/

section Step2Bridges

@[simp] private theorem liftGdhComp_costUB_local :
    ∀ {Γ : List (Ty pqSig)} {t : Ty pqSig} (c : Comp pqxdhOps pqGapDhIface Γ t),
      (KeyInd1KeyGapDh.liftGdhComp c).costUB = c.costUB := by
  intro Γ t c; induction c with
  | query q _ => rcases q with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [KeyInd1KeyGapDh.liftGdhComp, Comp.costUB]

@[simp] private theorem sigChalQ_dsl_costUB_local (m : ℕ+) {Γ : List (Ty pqSig)}
    (msg : Expr pqxdhOps Γ (B m)) :
    (KeyInd1KeyGapDh.sigChalQ_dsl m msg).costUB = msg.costUB + (1 + m.val + 0 + 64) := rfl

@[simp] private theorem liftGdhComp_queries_any {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqGapDhIface Γ t)
    (w : pqSigAndDdhIface.Tag → ℕ) (ws : PSamp → ℕ) :
    (KeyInd1KeyGapDh.liftGdhComp c).queries w ws =
      c.queries (fun g : pqGapDhIface.Tag => match g with
        | Sum.inl p => w (Sum.inl p)
        | Sum.inr () => w (Sum.inr (Sum.inr ()))) ws := by
  induction c <;> simp_all [KeyInd1KeyGapDh.liftGdhComp, Comp.queries]
  rename_i g _; rcases g with p | ⟨⟩ <;> rfl

@[simp] private theorem liftChal_queries_any {C : ChallengerOracle} {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface Γ t)
    (w : (pqChalIface C).Tag → ℕ) (ws : PSamp → ℕ) :
    (Comp.liftChal (C := C) c).queries w ws =
      c.queries (fun p => w (Sum.inl p)) ws := by
  induction c <;> simp_all [Comp.liftChal, Comp.queries, pqChalIface, pqPrimIface]

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
private theorem a1gStep2C_queries_eq_a1gStepC {Γs₁ Γq₁ Δ₁ Γs₂ Γq₂ Δ₂ : List (Ty pqSig)}
    [Ext Γs₁ Δ₁] [Ext Γq₁ Δ₁] [Ext Γs₂ Δ₂] [Ext Γq₂ Δ₂]
    (st2 : Var Γs₂ a1g2StTy) (q2 : Var Γq₂ authQueryTy)
    (st1 : Var Γs₁ a1gStTy) (q1 : Var Γq₁ authQueryTy)
    (w : pqSigAndDdhIface.Tag → ℕ) (ws : PSamp → ℕ) :
    (a1gStep2C S K (Δ := Δ₂) st2 q2).queries w ws =
      (a1gStepC S K (Δ := Δ₁) st1 q1).queries w ws := by
  simp only [a1gStep2C, a1gStepC, a1gPre2C, a1gPreC, a1gInitPrin2C, a1gInitPrinC,
    a1gGenSpk2C, a1gGenSpkC, Comp.letC, Comp.iteC,
    liftGdhComp_queries_any, liftChal_queries_any,
    fgStep2C, fgStepC, fgInitPrin2C, fgInitPrinC, fgGenSpk2C, fgGenSpkC, fgSend2C, fgSendC,
    fgRecvC, fgRecvB, fgRoC, fgRoRootC, fgRegisterC, onBaseF, corruptB, genOpkB,
    findHonestC, isGameSpkC, isGameOpkC, resolveSigPkC,
    mkSecretPosC, mkPairPosC, twoSideC, twoSideOptC, ddhEqC, ddhEqOptC, entryMatchesC, patchC,
    rootPatchC, isAdvPowsC, koskBundleOkPowsC, koskSenderOkPowsC, lookupSpkSkC,
    KeyInd1KeyGapDh.sigChalQ_dsl, Comp.queryDdh, Comp.queryChal,
    findMV, anyMV, mapMV, foldMV, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM, Comp.caseOptC, Comp.caseSumC,
    Comp.sampleBytes32, Comp.sampleRandom64, Comp.sampleDrKey96, Comp.sampleBool,
    Comp.sampleIndex, Comp.queryPrim,
    Comp.sampleBytes32C, Comp.sampleRandom64C, Comp.sampleDrKey96C, Comp.sampleBoolC,
    Comp.sampleIndexC, Comp.queryPrimC,
    bindV, letV, caseOptV, caseSumV,
    Comp.queries, ite_true, ite_false, Bool.false_eq_true]

local macro "a1s_gstep_cost_simp" : tactic => `(tactic|
  simp only [
    liftGdhComp_costUB_local, sigChalQ_dsl_costUB_local,
    findHonestC_costUB, isGameSpkC_costUB, isGameOpkC_costUB, resolveSigPkC_costUB,
    firstMsgADE_costUB, sidEq_costUB, optU32Eq_costUB, kyberCheckE_costUB,
    fgInitPrinC, fgGenSpkC, fgSendC, fgInitPrin2C, fgGenSpk2C, fgSend2C,
    a1gInitPrinC, a1gGenSpkC, a1gInitPrin2C, a1gGenSpk2C,
    fgRecvC, fgRecvB, fgRoC, fgRoRootC, fgRegisterC, onBaseF, corruptB, genOpkB, sendGuardE,
    mkSecretPosC, mkPairPosC, twoSideC, twoSideOptC, ddhEqC, ddhEqOptC, entryMatchesC, patchC,
    rootPatchC, isAdvPowsC, koskBundleOkPowsC, koskSenderOkPowsC, lookupSpkSkC,
    bindV, letV, caseOptV, caseSumV, findMV, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    natEq, nat2Eq, nat3Eq, isSomeE, optFst, optSnd, bytesEmpty, slice32, q4,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd, seMk,
    pmHdr, pmEphAPk, pmPqMsg, pmAeadCt, peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
    peMk, peUpd, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, sbMk, oeOpkSk, oeOpkPk, oeConsumed,
    oeMk, oeUpd, buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk,
    fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
    paU, paV, paDh1, paTI, paTS, pa2U, pa2V, pa2Role, pa2TS, pa2Dh1,
    feP1, feP2, feP3, feP4, feSs, feDk, pkP1, pkP2, pkP3, pkP4, pkSs, reRk, rePos, reRk1, reCk,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, rs, Comp.costUB_liftChal, Comp.letC, Comp.iteC,
    costUB_encEC, costUB_encKEM, costUB_bytesTakeK, costUB_bytesDrop, costUB_bytesLen,
    costUB_bytesBeq, costUB_litBytes, costUB_u32OfNat, costUB_u32Beq, costUB_sampleBytes32,
    costUB_sampleBytes32C, costUB_sampleRandom64C, costUB_sampleDrKey96C, costUB_queryPrim,
    costUB_queryPrimC, costUB_queryDdh, Ty.wd, v, Comp.costUB, Expr.costUB,
    PNat.val_ofNat, F_X25519_length, List.length_nil,
    bits_0, bits_1, bits_32, bits_64, bits_96, bits_128, bits_160, bits_192,
    ite_true, ite_false, Bool.false_eq_true])

set_option linter.unusedSimpArgs false in
private theorem fgInitPrin2C_costUB_le {Γp₁ Γs₁ Γu₁ Δ₁ Γp₂ Γs₂ Γu₂ Δ₂ : List (Ty pqSig)}
    [Ext Γp₁ Δ₁] [Ext Γs₁ Δ₁] [Ext Γu₁ Δ₁] [Ext Γp₂ Δ₂] [Ext Γs₂ Δ₂] [Ext Γu₂ Δ₂]
    (pa2 : Var Γp₂ a1gParams2Ty) (sim2 : Var Γs₂ fgSimTy) (u2 : Var Γu₂ .nat)
    (pa1 : Var Γp₁ paramsTy) (sim1 : Var Γs₁ fgSimTy) (u1 : Var Γu₁ .nat) :
    (fgInitPrin2C K (Δ := Δ₂) pa2 sim2 u2).costUB ≤
      (fgInitPrinC K (Δ := Δ₁) pa1 sim1 u1).costUB + 30 := by
  a1s_gstep_cost_simp; omega

set_option linter.unusedSimpArgs false in
private theorem fgGenSpk2C_costUB_le {Γp₁ Γs₁ Γx₁ Δ₁ Γp₂ Γs₂ Γx₂ Δ₂ : List (Ty pqSig)}
    [Ext Γp₁ Δ₁] [Ext Γs₁ Δ₁] [Ext Γx₁ Δ₁] [Ext Γp₂ Δ₂] [Ext Γs₂ Δ₂] [Ext Γx₂ Δ₂]
    (pa2 : Var Γp₂ a1gParams2Ty) (sim2 : Var Γs₂ fgSimTy) (x2 : Var Γx₂ (.prod .nat .nat))
    (pa1 : Var Γp₁ paramsTy) (sim1 : Var Γs₁ fgSimTy) (x1 : Var Γx₁ (.prod .nat .nat)) :
    (fgGenSpk2C K (Δ := Δ₂) pa2 sim2 x2).costUB ≤
      (fgGenSpkC S K (Δ := Δ₁) pa1 sim1 x1).costUB + 30 := by
  a1s_gstep_cost_simp; omega

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
private theorem fgSend2C_costUB_le (opk : Bool)
    {Γp₁ Γs₁ Γx₁ Δ₁ Γp₂ Γs₂ Γx₂ Δ₂ : List (Ty pqSig)}
    [Ext Γp₁ Δ₁] [Ext Γs₁ Δ₁] [Ext Γx₁ Δ₁] [Ext Γp₂ Δ₂] [Ext Γs₂ Δ₂] [Ext Γx₂ Δ₂]
    (pa2 : Var Γp₂ a1gParams2Ty) (sim2 : Var Γs₂ fgSimTy) (x2 : Var Γx₂ sendQTy)
    (pa1 : Var Γp₁ paramsTy) (sim1 : Var Γs₁ fgSimTy) (x1 : Var Γx₁ sendQTy) :
    (fgSend2C S K opk (Δ := Δ₂) pa2 sim2 x2).costUB ≤
      (fgSendC S K opk (Δ := Δ₁) pa1 sim1 x1).costUB + 40 := by
  cases opk <;> a1s_gstep_cost_simp <;> generalize min K S.N_dh = md <;> omega

set_option linter.unusedSimpArgs false in
private theorem fgCorrupt_costUB_eq {Γs₁ Γu₁ Δ₁ Γs₂ Γu₂ Δ₂ : List (Ty pqSig)}
    [Ext Γs₁ Δ₁] [Ext Γu₁ Δ₁] [Ext Γs₂ Δ₂] [Ext Γu₂ Δ₂]
    (sim2 : Var Γs₂ fgSimTy) (u2 : Var Γu₂ .nat)
    (sim1 : Var Γs₁ fgSimTy) (u1 : Var Γu₁ .nat) :
    (onBaseF (Δ := Δ₂) sim2 fun g => corruptB K g u2).costUB =
      (onBaseF (Δ := Δ₁) sim1 fun g => corruptB K g u1).costUB := by
  a1s_gstep_cost_simp

set_option linter.unusedSimpArgs false in
private theorem fgGenOpk_costUB_eq {Γs₁ Γx₁ Δ₁ Γs₂ Γx₂ Δ₂ : List (Ty pqSig)}
    [Ext Γs₁ Δ₁] [Ext Γx₁ Δ₁] [Ext Γs₂ Δ₂] [Ext Γx₂ Δ₂]
    (sim2 : Var Γs₂ fgSimTy) (x2 : Var Γx₂ (.prod .nat (.prod .nat .nat)))
    (sim1 : Var Γs₁ fgSimTy) (x1 : Var Γx₁ (.prod .nat (.prod .nat .nat))) :
    (onBaseF (Δ := Δ₂) sim2 fun g => genOpkB K g x2).costUB =
      (onBaseF (Δ := Δ₁) sim1 fun g => genOpkB K g x1).costUB := by
  a1s_gstep_cost_simp

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
private theorem fgRecvB_costUB_eq (opk : Bool) {Γs₁ Γx₁ Δ₁ Γs₂ Γx₂ Δ₂ : List (Ty pqSig)}
    [Ext Γs₁ Δ₁] [Ext Γx₁ Δ₁] [Ext Γs₂ Δ₂] [Ext Γx₂ Δ₂]
    (sim2 : Var Γs₂ fgSimTy) (x2 : Var Γx₂ recvQTy)
    (sim1 : Var Γs₁ fgSimTy) (x1 : Var Γx₁ recvQTy) :
    (fgRecvB S K opk (Δ := Δ₂) sim2 x2).costUB =
      (fgRecvB S K opk (Δ := Δ₁) sim1 x1).costUB := by
  cases opk <;> a1s_gstep_cost_simp

set_option linter.unusedSimpArgs false in
private theorem fgRoC_costUB_eq {Γs₁ Γx₁ Δ₁ Γs₂ Γx₂ Δ₂ : List (Ty pqSig)}
    [Ext Γs₁ Δ₁] [Ext Γx₁ Δ₁] [Ext Γs₂ Δ₂] [Ext Γx₂ Δ₂]
    (sim2 : Var Γs₂ fgSimTy) (sec2 : Var Γx₂ (B 192))
    (sim1 : Var Γs₁ fgSimTy) (sec1 : Var Γx₁ (B 192)) :
    (fgRoC K (Δ := Δ₂) sim2 sec2).costUB = (fgRoC K (Δ := Δ₁) sim1 sec1).costUB := by
  a1s_gstep_cost_simp

set_option linter.unusedSimpArgs false in
private theorem fgRoRootC_costUB_eq {Γs₁ Γx₁ Δ₁ Γs₂ Γx₂ Δ₂ : List (Ty pqSig)}
    [Ext Γs₁ Δ₁] [Ext Γx₁ Δ₁] [Ext Γs₂ Δ₂] [Ext Γx₂ Δ₂]
    (sim2 : Var Γs₂ fgSimTy) (x2 : Var Γx₂ (.prod (B 32) (B 32)))
    (sim1 : Var Γs₁ fgSimTy) (x1 : Var Γx₁ (.prod (B 32) (B 32))) :
    (fgRoRootC K (Δ := Δ₂) sim2 x2).costUB = (fgRoRootC K (Δ := Δ₁) sim1 x1).costUB := by
  a1s_gstep_cost_simp

set_option linter.unusedSimpArgs false in
private theorem fgRegisterC_costUB_eq {Γs₁ Γx₁ Δ₁ Γs₂ Γx₂ Δ₂ : List (Ty pqSig)}
    [Ext Γs₁ Δ₁] [Ext Γx₁ Δ₁] [Ext Γs₂ Δ₂] [Ext Γx₂ Δ₂]
    (sim2 : Var Γs₂ fgSimTy) (sk2 : Var Γx₂ (B 32))
    (sim1 : Var Γs₁ fgSimTy) (sk1 : Var Γx₁ (B 32)) :
    (fgRegisterC (Δ := Δ₂) sim2 sk2).costUB = (fgRegisterC (Δ := Δ₁) sim1 sk1).costUB := by
  a1s_gstep_cost_simp

private abbrev a1sDummyTail : List (Ty pqSig) :=
  [a1gParams2Ty, paramsTy, fgSimTy, .nat]

private def c_fgInitPrin2 (K : ℕ) : ℕ :=
  (fgInitPrin2C K (Δ := .nat :: a1sDummyTail)
    (.vs .vz : Var (.nat :: a1sDummyTail) a1gParams2Ty)
    (.vs (.vs (.vs .vz)) : Var (.nat :: a1sDummyTail) fgSimTy)
    (.vz : Var (.nat :: a1sDummyTail) .nat)).costUB

private def c_fgInitPrin (K : ℕ) : ℕ :=
  (fgInitPrinC K (Δ := .nat :: a1sDummyTail)
    (.vs (.vs .vz) : Var (.nat :: a1sDummyTail) paramsTy)
    (.vs (.vs (.vs .vz)) : Var (.nat :: a1sDummyTail) fgSimTy)
    (.vz : Var (.nat :: a1sDummyTail) .nat)).costUB

private def c_fgCorrupt (K : ℕ) : ℕ :=
  (onBaseF (Δ := .nat :: a1sDummyTail)
    (.vs (.vs (.vs .vz)) : Var (.nat :: a1sDummyTail) fgSimTy)
    fun g => corruptB K g (.vz : Var (.nat :: a1sDummyTail) .nat)).costUB

private def c_fgGenSpk2 (K : ℕ) : ℕ :=
  (fgGenSpk2C K (Δ := (.prod .nat .nat) :: a1sDummyTail)
    (.vs .vz : Var ((.prod .nat .nat) :: a1sDummyTail) a1gParams2Ty)
    (.vs (.vs (.vs .vz)) : Var ((.prod .nat .nat) :: a1sDummyTail) fgSimTy)
    (.vz : Var ((.prod .nat .nat) :: a1sDummyTail) (.prod .nat .nat))).costUB

private def c_fgGenSpk (S : Setup) (K : ℕ) : ℕ :=
  (fgGenSpkC S K (Δ := (.prod .nat .nat) :: a1sDummyTail)
    (.vs (.vs .vz) : Var ((.prod .nat .nat) :: a1sDummyTail) paramsTy)
    (.vs (.vs (.vs .vz)) : Var ((.prod .nat .nat) :: a1sDummyTail) fgSimTy)
    (.vz : Var ((.prod .nat .nat) :: a1sDummyTail) (.prod .nat .nat))).costUB

private def c_fgGenOpk (K : ℕ) : ℕ :=
  (onBaseF (Δ := (.prod .nat (.prod .nat .nat)) :: a1sDummyTail)
    (.vs (.vs (.vs .vz)) : Var ((.prod .nat (.prod .nat .nat)) :: a1sDummyTail) fgSimTy)
    fun g => genOpkB K g
      (.vz : Var ((.prod .nat (.prod .nat .nat)) :: a1sDummyTail) (.prod .nat (.prod .nat .nat)))).costUB

private def c_fgSend2 (S : Setup) (K : ℕ) (opk : Bool) : ℕ :=
  (fgSend2C S K opk (Δ := sendQTy :: a1sDummyTail)
    (.vs .vz : Var (sendQTy :: a1sDummyTail) a1gParams2Ty)
    (.vs (.vs (.vs .vz)) : Var (sendQTy :: a1sDummyTail) fgSimTy)
    (.vz : Var (sendQTy :: a1sDummyTail) sendQTy)).costUB

private def c_fgSend (S : Setup) (K : ℕ) (opk : Bool) : ℕ :=
  (fgSendC S K opk (Δ := sendQTy :: a1sDummyTail)
    (.vs (.vs .vz) : Var (sendQTy :: a1sDummyTail) paramsTy)
    (.vs (.vs (.vs .vz)) : Var (sendQTy :: a1sDummyTail) fgSimTy)
    (.vz : Var (sendQTy :: a1sDummyTail) sendQTy)).costUB

private def c_fgRecvB (S : Setup) (K : ℕ) (opk : Bool) : ℕ :=
  (fgRecvB S K opk (Δ := recvQTy :: a1sDummyTail)
    (.vs (.vs (.vs .vz)) : Var (recvQTy :: a1sDummyTail) fgSimTy)
    (.vz : Var (recvQTy :: a1sDummyTail) recvQTy)).costUB

private def c_fgRoC (K : ℕ) : ℕ :=
  (fgRoC K (Δ := (B 192) :: a1sDummyTail)
    (.vs (.vs (.vs .vz)) : Var ((B 192) :: a1sDummyTail) fgSimTy)
    (.vz : Var ((B 192) :: a1sDummyTail) (B 192))).costUB

private def c_fgRoRootC (K : ℕ) : ℕ :=
  (fgRoRootC K (Δ := (.prod (B 32) (B 32)) :: a1sDummyTail)
    (.vs (.vs (.vs .vz)) : Var ((.prod (B 32) (B 32)) :: a1sDummyTail) fgSimTy)
    (.vz : Var ((.prod (B 32) (B 32)) :: a1sDummyTail) (.prod (B 32) (B 32)))).costUB

private def c_fgRegisterC : ℕ :=
  (fgRegisterC (Δ := (B 32) :: a1sDummyTail)
    (.vs (.vs (.vs .vz)) : Var ((B 32) :: a1sDummyTail) fgSimTy)
    (.vz : Var ((B 32) :: a1sDummyTail) (B 32))).costUB

private def c_a1gInitPrin2 (K : ℕ) : ℕ :=
  (a1gInitPrin2C K (Δ := .nat :: a1sDummyTail)
    (.vs .vz : Var (.nat :: a1sDummyTail) a1gParams2Ty)
    (.vs (.vs (.vs .vz)) : Var (.nat :: a1sDummyTail) fgSimTy)
    (.vz : Var (.nat :: a1sDummyTail) .nat)).costUB

private def c_a1gInitPrin (K : ℕ) : ℕ :=
  (a1gInitPrinC K (Δ := .nat :: a1sDummyTail)
    (.vs (.vs .vz) : Var (.nat :: a1sDummyTail) paramsTy)
    (.vs (.vs (.vs .vz)) : Var (.nat :: a1sDummyTail) fgSimTy)
    (.vz : Var (.nat :: a1sDummyTail) .nat)).costUB

private def c_a1gGenSpk2 (K : ℕ) : ℕ :=
  (a1gGenSpk2C K (Δ := (.prod .nat .nat) :: a1sDummyTail)
    (.vs .vz : Var ((.prod .nat .nat) :: a1sDummyTail) a1gParams2Ty)
    (.vs (.vs (.vs .vz)) : Var ((.prod .nat .nat) :: a1sDummyTail) fgSimTy)
    (.vs (.vs (.vs (.vs .vz))) : Var ((.prod .nat .nat) :: a1sDummyTail) .nat)
    (.vz : Var ((.prod .nat .nat) :: a1sDummyTail) (.prod .nat .nat))).costUB

private def c_a1gGenSpk (S : Setup) (K : ℕ) : ℕ :=
  (a1gGenSpkC S K (Δ := (.prod .nat .nat) :: a1sDummyTail)
    (.vs (.vs .vz) : Var ((.prod .nat .nat) :: a1sDummyTail) paramsTy)
    (.vs (.vs (.vs .vz)) : Var ((.prod .nat .nat) :: a1sDummyTail) fgSimTy)
    (.vs (.vs (.vs (.vs .vz))) : Var ((.prod .nat .nat) :: a1sDummyTail) .nat)
    (.vz : Var ((.prod .nat .nat) :: a1sDummyTail) (.prod .nat .nat))).costUB

set_option linter.unusedSimpArgs false in
private theorem fgInitPrin2C_canon {Γp Γs Γu Δ : List (Ty pqSig)}
    [Ext Γp Δ] [Ext Γs Δ] [Ext Γu Δ]
    (pa : Var Γp a1gParams2Ty) (sim : Var Γs fgSimTy) (u : Var Γu .nat) :
    (fgInitPrin2C K (Δ := Δ) pa sim u).costUB = c_fgInitPrin2 K := by
  unfold c_fgInitPrin2; a1s_gstep_cost_simp

set_option linter.unusedSimpArgs false in
private theorem fgInitPrinC_canon {Γp Γs Γu Δ : List (Ty pqSig)}
    [Ext Γp Δ] [Ext Γs Δ] [Ext Γu Δ]
    (pa : Var Γp paramsTy) (sim : Var Γs fgSimTy) (u : Var Γu .nat) :
    (fgInitPrinC K (Δ := Δ) pa sim u).costUB = c_fgInitPrin K := by
  unfold c_fgInitPrin; a1s_gstep_cost_simp

private theorem c_fgInitPrin2_le : c_fgInitPrin2 K ≤ c_fgInitPrin K + 30 :=
  fgInitPrin2C_costUB_le K _ _ _ _ _ _

private theorem fgCorrupt_canon {Γs Γu Δ : List (Ty pqSig)} [Ext Γs Δ] [Ext Γu Δ]
    (sim : Var Γs fgSimTy) (u : Var Γu .nat) :
    (onBaseF (Δ := Δ) sim fun g => corruptB K g u).costUB = c_fgCorrupt K :=
  fgCorrupt_costUB_eq K sim u _ _

set_option linter.unusedSimpArgs false in
private theorem fgGenSpk2C_canon {Γp Γs Γx Δ : List (Ty pqSig)}
    [Ext Γp Δ] [Ext Γs Δ] [Ext Γx Δ]
    (pa : Var Γp a1gParams2Ty) (sim : Var Γs fgSimTy) (x : Var Γx (.prod .nat .nat)) :
    (fgGenSpk2C K (Δ := Δ) pa sim x).costUB = c_fgGenSpk2 K := by
  unfold c_fgGenSpk2; a1s_gstep_cost_simp

set_option linter.unusedSimpArgs false in
private theorem fgGenSpkC_canon {Γp Γs Γx Δ : List (Ty pqSig)}
    [Ext Γp Δ] [Ext Γs Δ] [Ext Γx Δ]
    (pa : Var Γp paramsTy) (sim : Var Γs fgSimTy) (x : Var Γx (.prod .nat .nat)) :
    (fgGenSpkC S K (Δ := Δ) pa sim x).costUB = c_fgGenSpk S K := by
  unfold c_fgGenSpk; a1s_gstep_cost_simp

private theorem c_fgGenSpk2_le : c_fgGenSpk2 K ≤ c_fgGenSpk S K + 30 :=
  fgGenSpk2C_costUB_le S K _ _ _ _ _ _

private theorem fgGenOpk_canon {Γs Γx Δ : List (Ty pqSig)} [Ext Γs Δ] [Ext Γx Δ]
    (sim : Var Γs fgSimTy) (x : Var Γx (.prod .nat (.prod .nat .nat))) :
    (onBaseF (Δ := Δ) sim fun g => genOpkB K g x).costUB = c_fgGenOpk K :=
  fgGenOpk_costUB_eq K sim x _ _

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
private theorem fgSend2C_canon (opk : Bool) {Γp Γs Γx Δ : List (Ty pqSig)}
    [Ext Γp Δ] [Ext Γs Δ] [Ext Γx Δ]
    (pa : Var Γp a1gParams2Ty) (sim : Var Γs fgSimTy) (x : Var Γx sendQTy) :
    (fgSend2C S K opk (Δ := Δ) pa sim x).costUB = c_fgSend2 S K opk := by
  unfold c_fgSend2; cases opk <;> a1s_gstep_cost_simp

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
private theorem fgSendC_canon (opk : Bool) {Γp Γs Γx Δ : List (Ty pqSig)}
    [Ext Γp Δ] [Ext Γs Δ] [Ext Γx Δ]
    (pa : Var Γp paramsTy) (sim : Var Γs fgSimTy) (x : Var Γx sendQTy) :
    (fgSendC S K opk (Δ := Δ) pa sim x).costUB = c_fgSend S K opk := by
  unfold c_fgSend; cases opk <;> a1s_gstep_cost_simp

private theorem c_fgSend2_le (opk : Bool) : c_fgSend2 S K opk ≤ c_fgSend S K opk + 40 :=
  fgSend2C_costUB_le S K opk _ _ _ _ _ _

private theorem fgRecvB_canon (opk : Bool) {Γs Γx Δ : List (Ty pqSig)} [Ext Γs Δ] [Ext Γx Δ]
    (sim : Var Γs fgSimTy) (x : Var Γx recvQTy) :
    (fgRecvB S K opk (Δ := Δ) sim x).costUB = c_fgRecvB S K opk :=
  fgRecvB_costUB_eq S K opk sim x _ _

private theorem fgRoC_canon {Γs Γx Δ : List (Ty pqSig)} [Ext Γs Δ] [Ext Γx Δ]
    (sim : Var Γs fgSimTy) (sec : Var Γx (B 192)) :
    (fgRoC K (Δ := Δ) sim sec).costUB = c_fgRoC K :=
  fgRoC_costUB_eq K sim sec _ _

private theorem fgRoRootC_canon {Γs Γx Δ : List (Ty pqSig)} [Ext Γs Δ] [Ext Γx Δ]
    (sim : Var Γs fgSimTy) (x : Var Γx (.prod (B 32) (B 32))) :
    (fgRoRootC K (Δ := Δ) sim x).costUB = c_fgRoRootC K :=
  fgRoRootC_costUB_eq K sim x _ _

private theorem fgRegisterC_canon {Γs Γx Δ : List (Ty pqSig)} [Ext Γs Δ] [Ext Γx Δ]
    (sim : Var Γs fgSimTy) (sk : Var Γx (B 32)) :
    (fgRegisterC (Δ := Δ) sim sk).costUB = c_fgRegisterC :=
  fgRegisterC_costUB_eq sim sk _ _

private theorem fgStep2C_costUB_le {Γp₁ Γs₁ Γq₁ Δ₁ Γp₂ Γs₂ Γq₂ Δ₂ : List (Ty pqSig)}
    [Ext Γp₁ Δ₁] [Ext Γs₁ Δ₁] [Ext Γq₁ Δ₁] [Ext Γp₂ Δ₂] [Ext Γs₂ Δ₂] [Ext Γq₂ Δ₂]
    (pa2 : Var Γp₂ a1gParams2Ty) (sim2 : Var Γs₂ fgSimTy) (q2 : Var Γq₂ authQueryTy)
    (pa1 : Var Γp₁ paramsTy) (sim1 : Var Γs₁ fgSimTy) (q1 : Var Γq₁ authQueryTy) :
    (fgStep2C S K (Δ := Δ₂) pa2 sim2 q2).costUB ≤
      (fgStepC S K (Δ := Δ₁) pa1 sim1 q1).costUB + 150 := by
  simp only [fgStep2C, fgStepC, caseSumV, aNone, v, Comp.costUB, Expr.costUB,
    fgInitPrin2C_canon, fgInitPrinC_canon, fgCorrupt_canon,
    fgGenSpk2C_canon, fgGenSpkC_canon, fgGenOpk_canon,
    fgSend2C_canon, fgSendC_canon, fgRecvB_canon,
    fgRoC_canon, fgRoRootC_canon, fgRegisterC_canon]
  have h0 := c_fgInitPrin2_le K
  have h2 := c_fgGenSpk2_le S K
  have h4 := c_fgSend2_le S K true
  have h5 := c_fgSend2_le S K false
  omega

set_option linter.unusedSimpArgs false in
private theorem a1gInitPrin2C_costUB_le {Γp₁ Γs₁ Γu₁ Δ₁ Γp₂ Γs₂ Γu₂ Δ₂ : List (Ty pqSig)}
    [Ext Γp₁ Δ₁] [Ext Γs₁ Δ₁] [Ext Γu₁ Δ₁] [Ext Γp₂ Δ₂] [Ext Γs₂ Δ₂] [Ext Γu₂ Δ₂]
    (pa2 : Var Γp₂ a1gParams2Ty) (sim2 : Var Γs₂ fgSimTy) (u2 : Var Γu₂ .nat)
    (pa1 : Var Γp₁ paramsTy) (sim1 : Var Γs₁ fgSimTy) (u1 : Var Γu₁ .nat) :
    (a1gInitPrin2C K (Δ := Δ₂) pa2 sim2 u2).costUB ≤
      (a1gInitPrinC K (Δ := Δ₁) pa1 sim1 u1).costUB + 30 := by
  a1s_gstep_cost_simp; omega

set_option linter.unusedSimpArgs false in
private theorem a1gInitPrin2C_canon {Γp Γs Γu Δ : List (Ty pqSig)}
    [Ext Γp Δ] [Ext Γs Δ] [Ext Γu Δ]
    (pa : Var Γp a1gParams2Ty) (sim : Var Γs fgSimTy) (u : Var Γu .nat) :
    (a1gInitPrin2C K (Δ := Δ) pa sim u).costUB = c_a1gInitPrin2 K := by
  unfold c_a1gInitPrin2; a1s_gstep_cost_simp

set_option linter.unusedSimpArgs false in
private theorem a1gInitPrinC_canon {Γp Γs Γu Δ : List (Ty pqSig)}
    [Ext Γp Δ] [Ext Γs Δ] [Ext Γu Δ]
    (pa : Var Γp paramsTy) (sim : Var Γs fgSimTy) (u : Var Γu .nat) :
    (a1gInitPrinC K (Δ := Δ) pa sim u).costUB = c_a1gInitPrin K := by
  unfold c_a1gInitPrin; a1s_gstep_cost_simp

private theorem c_a1gInitPrin2_le : c_a1gInitPrin2 K ≤ c_a1gInitPrin K + 30 :=
  a1gInitPrin2C_costUB_le K _ _ _ _ _ _

set_option linter.unusedSimpArgs false in
private theorem a1gGenSpk2C_costUB_le
    {Γp₁ Γs₁ Γb₁ Γx₁ Δ₁ Γp₂ Γs₂ Γb₂ Γx₂ Δ₂ : List (Ty pqSig)}
    [Ext Γp₁ Δ₁] [Ext Γs₁ Δ₁] [Ext Γb₁ Δ₁] [Ext Γx₁ Δ₁]
    [Ext Γp₂ Δ₂] [Ext Γs₂ Δ₂] [Ext Γb₂ Δ₂] [Ext Γx₂ Δ₂]
    (pa2 : Var Γp₂ a1gParams2Ty) (sim2 : Var Γs₂ fgSimTy) (sigB2 : Var Γb₂ .nat)
    (x2 : Var Γx₂ (.prod .nat .nat))
    (pa1 : Var Γp₁ paramsTy) (sim1 : Var Γs₁ fgSimTy) (sigB1 : Var Γb₁ .nat)
    (x1 : Var Γx₁ (.prod .nat .nat)) :
    (a1gGenSpk2C K (Δ := Δ₂) pa2 sim2 sigB2 x2).costUB ≤
      (a1gGenSpkC S K (Δ := Δ₁) pa1 sim1 sigB1 x1).costUB + 30 := by
  a1s_gstep_cost_simp; omega

set_option linter.unusedSimpArgs false in
private theorem a1gGenSpk2C_canon {Γp Γs Γb Γx Δ : List (Ty pqSig)}
    [Ext Γp Δ] [Ext Γs Δ] [Ext Γb Δ] [Ext Γx Δ]
    (pa : Var Γp a1gParams2Ty) (sim : Var Γs fgSimTy) (sigB : Var Γb .nat)
    (x : Var Γx (.prod .nat .nat)) :
    (a1gGenSpk2C K (Δ := Δ) pa sim sigB x).costUB = c_a1gGenSpk2 K := by
  unfold c_a1gGenSpk2; a1s_gstep_cost_simp

set_option linter.unusedSimpArgs false in
private theorem a1gGenSpkC_canon {Γp Γs Γb Γx Δ : List (Ty pqSig)}
    [Ext Γp Δ] [Ext Γs Δ] [Ext Γb Δ] [Ext Γx Δ]
    (pa : Var Γp paramsTy) (sim : Var Γs fgSimTy) (sigB : Var Γb .nat)
    (x : Var Γx (.prod .nat .nat)) :
    (a1gGenSpkC S K (Δ := Δ) pa sim sigB x).costUB = c_a1gGenSpk S K := by
  unfold c_a1gGenSpk; a1s_gstep_cost_simp

private theorem c_a1gGenSpk2_le : c_a1gGenSpk2 K ≤ c_a1gGenSpk S K + 30 :=
  a1gGenSpk2C_costUB_le S K _ _ _ _ _ _ _ _

private theorem a1gPre2C_costUB_le
    {Γp₁ Γs₁ Γb₁ Γq₁ Δ₁ Γp₂ Γs₂ Γb₂ Γq₂ Δ₂ : List (Ty pqSig)}
    [Ext Γp₁ Δ₁] [Ext Γs₁ Δ₁] [Ext Γb₁ Δ₁] [Ext Γq₁ Δ₁]
    [Ext Γp₂ Δ₂] [Ext Γs₂ Δ₂] [Ext Γb₂ Δ₂] [Ext Γq₂ Δ₂]
    (pa2 : Var Γp₂ a1gParams2Ty) (sim2 : Var Γs₂ fgSimTy) (sigB2 : Var Γb₂ .nat)
    (q2 : Var Γq₂ authQueryTy)
    (pa1 : Var Γp₁ paramsTy) (sim1 : Var Γs₁ fgSimTy) (sigB1 : Var Γb₁ .nat)
    (q1 : Var Γq₁ authQueryTy) :
    (a1gPre2C K (Δ := Δ₂) pa2 sim2 sigB2 q2).costUB ≤
      (a1gPreC S K (Δ := Δ₁) pa1 sim1 sigB1 q1).costUB + 70 := by
  simp only [a1gPre2C, a1gPreC, caseSumV, bindV, Comp.iteC,
    liftGdhComp_costUB_local, eCaseSum, pa2Role, paDh1, paTI, natEq,
    v, Comp.costUB, Expr.costUB,
    a1gInitPrin2C_canon, a1gInitPrinC_canon, a1gGenSpk2C_canon, a1gGenSpkC_canon]
  have hI := c_a1gInitPrin2_le K
  have hG := c_a1gGenSpk2_le S K
  omega

private theorem a1gStep2C_costUB_le_a1gStepC_add {Γs₁ Γq₁ Δ₁ Γs₂ Γq₂ Δ₂ : List (Ty pqSig)}
    [Ext Γs₁ Δ₁] [Ext Γq₁ Δ₁] [Ext Γs₂ Δ₂] [Ext Γq₂ Δ₂]
    (st2 : Var Γs₂ a1g2StTy) (q2 : Var Γq₂ authQueryTy)
    (st1 : Var Γs₁ a1gStTy) (q1 : Var Γq₁ authQueryTy) :
    (a1gStep2C S K (Δ := Δ₂) st2 q2).costUB ≤
      (a1gStepC S K (Δ := Δ₁) st1 q1).costUB + 300 := by
  simp only [a1gStep2C, a1gStepC, letV, Comp.letC, bindV, caseSumV, Comp.iteC,
    liftGdhComp_costUB_local, eCaseSum, eCaseOpt, eFind,
    stPrin, fsBase, peCorrupted, pa2Role, paDh1, paTI, natEq, aNone,
    v, Comp.costUB, Expr.costUB]
  let Δp₂ := .nat :: fgSimTy :: a1gParams2Ty :: Δ₂
  let Δp₁ := .nat :: fgSimTy :: paramsTy :: Δ₁
  have hP := a1gPre2C_costUB_le S K
    (Δ₂ := Δp₂) (Δ₁ := Δp₁)
    (Var.vz : Var (a1gParams2Ty :: Δ₂) a1gParams2Ty)
    (Var.vz : Var (fgSimTy :: a1gParams2Ty :: Δ₂) fgSimTy)
    (Var.vz : Var Δp₂ .nat) q2
    (Var.vz : Var (paramsTy :: Δ₁) paramsTy)
    (Var.vz : Var (fgSimTy :: paramsTy :: Δ₁) fgSimTy)
    (Var.vz : Var Δp₁ .nat) q1
  have hF := fgStep2C_costUB_le S K
    (Δ₂ := .unit :: (.sum RSB .unit) :: Δp₂)
    (Δ₁ := .unit :: (.sum RSB .unit) :: Δp₁)
    (Var.vz : Var (a1gParams2Ty :: Δ₂) a1gParams2Ty)
    (Var.vz : Var (fgSimTy :: a1gParams2Ty :: Δ₂) fgSimTy)
    q2
    (Var.vz : Var (paramsTy :: Δ₁) paramsTy)
    (Var.vz : Var (fgSimTy :: paramsTy :: Δ₁) fgSimTy)
    q1
  omega

end Step2Bridges

private theorem a1sDelegate2C_costUB_le {c : Nat} (hG : A1gStepCostUB S K c)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) :
    (a1sDelegate2C S K (Δ := Δ) s q).costUB ≤ c + 1000 := by
  simp only [a1sDelegate2C, a1sCaseAPa2, bindV, letV, Comp.letC, a1sG, a1sMk, a1sTp, a1sTpk, a1sFg,
    v, Comp.costUB, Expr.costUB]
  have hB := a1gStep2C_costUB_le_a1gStepC_add S K
    (Γs₂ := a1g2StTy :: Δ) (Γq₂ := Γ₂) (Δ₂ := a1g2StTy :: Δ)
    (Γs₁ := a1gStTy :: Δ) (Γq₁ := Γ₂) (Δ₁ := a1gStTy :: Δ)
    Var.vz q Var.vz q
  have hC := hG (Γ₁ := a1gStTy :: Δ) (Γ₂ := Γ₂) (Δ := a1gStTy :: Δ) Var.vz q
  omega

private theorem a1sDelegate2C_queries_le (w : pqSigAndDdhIface.Tag → ℕ) {c : Nat}
    (hG : A1gStepQueries S K w c)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) :
    (a1sDelegate2C S K (Δ := Δ) s q).queries w SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ≤ c := by
  simp only [a1sDelegate2C, bindV, letV, Comp.letC, Comp.queries]
  rw [a1gStep2C_queries_eq_a1gStepC S K
    (Γs₂ := a1g2StTy :: Δ) (Γq₂ := Γ₂) (Δ₂ := a1g2StTy :: Δ)
    (Γs₁ := a1gStTy :: Δ) (Γq₁ := Γ₂) (Δ₁ := a1gStTy :: Δ)
    Var.vz q Var.vz q]
  have := hG (Γ₁ := a1gStTy :: Δ) (Γ₂ := Γ₂) (Δ := a1gStTy :: Δ) Var.vz q
  omega

private theorem a1sStep2C_costUB_le {c : Nat} (hG : A1gStepCostUB S K c)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) :
    (a1sStep2C S K (Δ := Δ) s q).costUB ≤ c + 27000 + 412 * S.N_dh + 8000 * K := by
  have hP := a1sPreC_costUB_le S K (Δ := Δ) s q
  have hD := a1sDelegate2C_costUB_le S K hG (Δ := .unit :: (.sum a1sRS .unit) :: Δ) s q
  simp only [a1sStep2C, bindV, caseSumV, isSomeE, a1sFg, aNone, v, Comp.costUB, Expr.costUB]
  omega

private theorem a1sStep2C_queries_le (w : pqSigAndDdhIface.Tag → ℕ) {c p : Nat}
    (hG : A1gStepQueries S K w c)
    (hPre : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ a1sStTy)
      (q : Var Γ₂ authQueryTy),
      (a1sPreC S K (Δ := Δ) s q).queries w SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ≤ p)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) :
    (a1sStep2C S K (Δ := Δ) s q).queries w SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ≤ p + c := by
  have hP := hPre (Δ := Δ) s q
  have hD := a1sDelegate2C_queries_le S K w hG (Δ := .unit :: (.sum a1sRS .unit) :: Δ) s q
  simp only [a1sStep2C, bindV, caseSumV, Comp.queries]
  omega

/-! ## Handler and total bounds -/

theorem a1s_handle_cost_le {c : Nat} (hG : A1gStepCostUB S K c) :
    (sigAuth1KeyProg S K).handle.cost ≤ c + 27000 + 412 * S.N_dh + 8000 * K := by
  refine Nat.le_trans (Comp.cost_le_costUB _) ?_
  exact a1sStep2C_costUB_le S K hG (Δ := [a1sStTy, authQueryTy]) _ _

theorem a1s_handle_sig_le {c : Nat}
    (hG : A1gStepQueries S K SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight c) :
    (sigAuth1KeyProg S K).handle.queries
      SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ≤ c := by
  have := a1sStep2C_queries_le S K SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight (p := 0) hG
    (fun s q => (a1sPreC_sigQueries S K s q).le) (Δ := [a1sStTy, authQueryTy])
    (.vz : Var [a1sStTy, authQueryTy] a1sStTy) (.vs .vz : Var [a1sStTy, authQueryTy] authQueryTy)
  rw [Nat.zero_add] at this
  exact this

theorem a1s_handle_ddh_le {c : Nat}
    (hG : A1gStepQueries S K SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight c) :
    (sigAuth1KeyProg S K).handle.queries
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ≤ c := by
  have := a1sStep2C_queries_le S K SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight (p := 0) hG
    (fun s q => (a1sPreC_ddhQueries S K s q).le) (Δ := [a1sStTy, authQueryTy])
    (.vz : Var [a1sStTy, authQueryTy] a1sStTy) (.vs .vz : Var [a1sStTy, authQueryTy] authQueryTy)
  rw [Nat.zero_add] at this
  exact this

theorem a1s_handle_prim_le {c : Nat}
    (hG : A1gStepQueries S K SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight c) :
    (sigAuth1KeyProg S K).handle.queries
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ≤
      2 * S.N_dh + 2 + c := by
  have := a1sStep2C_queries_le S K SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
    (p := 2 * S.N_dh + 2) hG
    (fun s q => a1sPreC_primQueries_le S K s q) (Δ := [a1sStTy, authQueryTy])
    (.vz : Var [a1sStTy, authQueryTy] a1sStTy) (.vs .vz : Var [a1sStTy, authQueryTy] authQueryTy)
  exact this

theorem sigAuth1KeyProg_totalCost_le_of (b : QueryBudget)
    (hG : A1gStepCostUB S b.q_total (80000 + 30000 * b.q_total + 10000 * S.N_dh)) :
    (sigAuth1KeyProg S b.q_total).totalCost b.q_total ≤
      SignalPqxdh.LegacyCosted.stepCostBudget S b := by
  have hH := a1s_handle_cost_le S b.q_total hG
  have hF := a1s_finish_cost_le S b.q_total
  have hI := a1s_init_cost_le S b.q_total
  change (sigAuth1KeyProg S b.q_total).init.cost +
      b.q_total * max 1 ((sigAuth1KeyProg S b.q_total).handle.cost + 32) +
      (sigAuth1KeyProg S b.q_total).finish.cost ≤ SignalPqxdh.LegacyCosted.stepCostBudget S b
  generalize (sigAuth1KeyProg S b.q_total).init.cost = cI at hI ⊢
  generalize (sigAuth1KeyProg S b.q_total).handle.cost = cH at hH ⊢
  generalize (sigAuth1KeyProg S b.q_total).finish.cost = cF at hF ⊢
  have hMax : max 1 (cH + 32) = cH + 32 := by omega
  rw [hMax]
  unfold SignalPqxdh.LegacyCosted.stepCostBudget
  generalize b.q_total = q at *
  have hqH : q * (cH + 32) ≤ q * (107032 + 38000 * q + 10412 * S.N_dh) :=
    Nat.mul_le_mul_left q (by omega)
  nlinarith [Nat.zero_le (q * S.N_dh), Nat.zero_le (q * S.N_sess_tot),
    Nat.zero_le (S.N_dh * S.N_sess_tot)]

theorem sigAuth1KeyProg_totalSigQueries_le_of (b : QueryBudget)
    (hG : A1gStepQueries S b.q_total SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight 2) :
    (sigAuth1KeyProg S b.q_total).totalQueries
      SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight b.q_total ≤ 2 * b.q_total := by
  dsimp only [CostedReduction.totalQueries]
  have hI0 : (sigAuth1KeyProg S b.q_total).init.queries
      SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 :=
    a1s_init_queries S b.q_total _
  have hF0 : (sigAuth1KeyProg S b.q_total).finish.queries
      SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 :=
    a1s_finish_queries S b.q_total _
  rw [hI0, hF0]
  have hH := Nat.mul_le_mul_left b.q_total (a1s_handle_sig_le S b.q_total hG)
  omega

theorem sigAuth1KeyProg_totalDdhQueries_syn_le_of (b : QueryBudget)
    (hG : A1gStepQueries S b.q_total SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight (5 * b.q_total)) :
    (sigAuth1KeyProg S b.q_total).totalQueries
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight b.q_total ≤
        5 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot := by
  dsimp only [CostedReduction.totalQueries]
  have hI0 : (sigAuth1KeyProg S b.q_total).init.queries
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 :=
    a1s_init_queries S b.q_total _
  have hF0 : (sigAuth1KeyProg S b.q_total).finish.queries
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 :=
    a1s_finish_queries S b.q_total _
  rw [hI0, hF0]
  have hH := Nat.mul_le_mul_left b.q_total (a1s_handle_ddh_le S b.q_total hG)
  generalize b.q_total = q at *
  have : q * (5 * q) = 5 * q ^ 2 := by ring
  omega

theorem sigAuth1KeyProg_totalDdhQueries_le_of (b : QueryBudget)
    (hG : A1gStepQueries S b.q_total SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight (5 * b.q_total)) :
    (sigAuth1KeyProg S b.q_total).totalQueries
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight b.q_total ≤
        5 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot :=
  sigAuth1KeyProg_totalDdhQueries_syn_le_of S b hG

theorem sigAuth1KeyProg_totalPrimQueries_le_of (b : QueryBudget)
    (hG : A1gStepQueries S b.q_total SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight (174 + S.N_dh * 30)) :
    (sigAuth1KeyProg S b.q_total).totalQueries
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b := by
  dsimp only [CostedReduction.totalQueries]
  have hI0 : (sigAuth1KeyProg S b.q_total).init.queries
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 :=
    a1s_init_queries S b.q_total _
  have hF0 : (sigAuth1KeyProg S b.q_total).finish.queries
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 :=
    a1s_finish_queries S b.q_total _
  rw [hI0, hF0]
  rw [Nat.zero_add, Nat.add_zero]
  have hH := a1s_handle_prim_le S b.q_total hG
  generalize (sigAuth1KeyProg S b.q_total).handle.queries
    SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
    SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = qH at hH ⊢
  unfold primQueryBudget
  generalize b.q_total = q at *
  have h1 : q * qH ≤ q * (2 * S.N_dh + 2 + (174 + S.N_dh * 30)) := Nat.mul_le_mul_left q hH
  nlinarith

end SignalPqxdh.Security.ReductionDsl.AuthHs
