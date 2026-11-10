/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Headline
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeySigWire
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyGapDhWire
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyShCrEval
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfCk
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfMk
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfBounds
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyAeadCpa
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfHmac
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3E
public import Computational.Proofs.SignalPqxdh.Delta.Auth1KeyHeadline
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrProofs
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3D
import Computational.Proofs.SpecLemmas.SignalPqxdh.Game

/-!
# Atomic-Signature One-Key PQXDH `Auth` Reductions and Bounds

**Checked by Lean.** Lifts the seven one-key PQXDH `Auth` `ReductionDsl` reductions onto the shared
atomic operation table `pqAtomicOps` and `SignalPqxdh.Costed.authCodec` via `AtomicLift`, proving
their syntactic step-cost and size bounds, semantic `.Bounded` query compliance, and advantage
transfer equalities.
-/

@[expose] public section

set_option autoImplicit false

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

section Auth1KeyR64

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.Security
open _root_.SignalPqxdh.Security.ReductionDsl
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (liftBase)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
open Computational.Proofs.SignalPqxdh.AtomicLift

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible]
  SignalPqxdh.LegacyCosted.sigAndDdhOracle SignalPqxdh.LegacyCosted.gapDhDdhOracle

private def zSigDdh0W : SignalPqxdh.LegacyCosted.pqSigAndDdhIface.Tag → ℕ := fun _ => 0
private def zGdh0W : SignalPqxdh.LegacyCosted.pqGapDhIface.Tag → ℕ := fun _ => 0
private def zPrim0W : SignalPqxdh.LegacyCosted.pqPrimIface.Tag → ℕ := fun _ => 0
private def a1R64WS : SignalPqxdh.LegacyCosted.PSamp → ℕ := sampR64W tlAuthSigDdh.hsmp

@[simp] private theorem a1R64WS_bool : a1R64WS .bool = 0 := rfl
@[simp] private theorem a1R64WS_bytes32 : a1R64WS .bytes32 = 0 := rfl
@[simp] private theorem a1R64WS_random64 : a1R64WS .random64 = 1 := rfl
@[simp] private theorem a1R64WS_drKey96 : a1R64WS .drKey96 = 0 := rfl
@[simp] private theorem a1R64WS_msgKeys80 : a1R64WS .msgKeys80 = 0 := rfl
@[simp] private theorem a1R64WS_index (N : ℕ) : a1R64WS (.index N) = 0 := rfl

@[simp] private theorem liftGdhComp_r64
    {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} {t : Ty SignalPqxdh.LegacyCosted.pqSig}
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqGapDhIface Γ t) :
    (KeyInd1KeyGapDh.liftGdhComp c).queries zSigDdh0W a1R64WS = c.queries zGdh0W a1R64WS := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [KeyInd1KeyGapDh.liftGdhComp, Comp.queries]

@[simp] private theorem liftChal_gdh_r64
    {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} {t : Ty SignalPqxdh.LegacyCosted.pqSig}
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface Γ t) :
    (Comp.liftChal (C := SignalPqxdh.LegacyCosted.gapDhDdhOracle) c).queries
      zGdh0W a1R64WS = c.queries zPrim0W a1R64WS := by
  induction c with
  | query _ _ => rfl
  | sample _ _ => rfl
  | _ => simp_all [Comp.liftChal, Comp.queries]

@[simp] private theorem liftBase_r64
    {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} {t : Ty SignalPqxdh.LegacyCosted.pqSig}
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface Γ t) :
    (liftBase c).queries zSigDdh0W a1R64WS = c.queries zPrim0W a1R64WS := by
  induction c with
  | query _ _ => rfl
  | sample _ _ => rfl
  | _ => simp_all [liftBase, Comp.queries]

@[simp] private theorem sigChalQ_dsl_r64 (m : ℕ+)
    {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (msg : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B m)) :
    (KeyInd1KeyGapDh.sigChalQ_dsl m msg).queries zSigDdh0W a1R64WS = 0 := rfl

@[simp] private theorem findHonestC_r64 (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ Δ]
    (st : Var Γ authStateTy) (pk : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (findHonestC S K st pk).queries zPrim0W a1R64WS = 0 := by
  simp [findHonestC, letV, Comp.letC, findMV, bindV, Comp.queryPrim, zPrim0W, Comp.queries]

@[simp] private theorem isGameSpkC_r64 (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ Δ]
    (st : Var Γ authStateTy) (pk : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (isGameSpkC S K st pk).queries zPrim0W a1R64WS = 0 := by
  simp [isGameSpkC, letV, Comp.letC, anyMV, bindV, Comp.queryPrim, zPrim0W, Comp.queries]

@[simp] private theorem isGameOpkC_r64 (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ Δ]
    (st : Var Γ authStateTy) (pk : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (isGameOpkC S K st pk).queries zPrim0W a1R64WS = 0 := by
  simp [isGameOpkC, letV, Comp.letC, anyMV, bindV, Comp.queryPrim, zPrim0W, Comp.queries]

@[simp] private theorem resolveSigPkC_r64 (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ Δ]
    (st : Var Γ authStateTy) (pk : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (resolveSigPkC S K st pk).queries zPrim0W a1R64WS = 0 := by
  simp [resolveSigPkC, letV, Comp.letC, bindV, Comp.queries]

@[simp] private theorem honestPeerC_r64 (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ Δ]
    (st : Var Γ authStateTy) (pk : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (honestPeerC S K st pk).queries zPrim0W a1R64WS = 0 := by
  simp [honestPeerC, bindV, Comp.queries]

@[simp] private theorem isAdvPowsC_r64 (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ Δ]
    (pows : Var Γ (.list (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32))))
    (pk : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (isAdvPowsC K pows pk).queries zPrim0W a1R64WS = 0 := by
  simp [isAdvPowsC, bindV, Comp.queryPrim, zPrim0W, Comp.queries]

@[simp] private theorem koskBundleOkPowsC_r64 (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ]
    (st : Var Γ₁ authStateTy)
    (pows : Var Γ₂ (.list (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32))))
    (bu : Var Γ₃ preKeyBundleTy) :
    (koskBundleOkPowsC S K (Δ := Δ) st pows bu).queries zPrim0W a1R64WS = 0 := by
  simp [koskBundleOkPowsC, bindV, caseOptV, Comp.queries]

@[simp] private theorem koskSenderOkPowsC_r64 (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st : Var Γ₁ authStateTy)
    (pows : Var Γ₂ (.list (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32))))
    (ik : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (koskSenderOkPowsC S K st pows ik).queries zPrim0W a1R64WS = 0 := by
  simp [koskSenderOkPowsC, letV, Comp.letC, bindV, Comp.queries]

@[simp] private theorem lookupSpkSkC_r64 (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st : Var Γ₁ authStateTy)
    (pows : Var Γ₂ (.list (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32))))
    (pk : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (lookupSpkSkC S K st pows pk).queries zPrim0W a1R64WS = 0 := by
  simp [lookupSpkSkC, bindV, findMV, Comp.queryPrim, zPrim0W, Comp.queries]

@[simp] private theorem extractC_r64 (S : Setup) (K : Nat)
    {Γa Γb Γc Γd Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γa Δ] [Ext Γb Δ] [Ext Γc Δ] [Ext Γd Δ]
    (tp : Var Γa .nat) (tpk : Var Γb (SignalPqxdh.LegacyCosted.B 32))
    (st : Var Γc authStateTy) (bu : Var Γd preKeyBundleTy) :
    (extractC S K (Δ := Δ) tp tpk st bu).queries zPrim0W a1R64WS = 0 := by
  simp [extractC, bindV, Comp.queryPrim, zPrim0W, Comp.queries]

set_option linter.unusedSimpArgs false in
private theorem a1gStepC_r64_le (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st : Var Γ₁ a1gStTy) (q : Var Γ₂ authQueryTy) :
    (a1gStepC S K (Δ := Δ) st q).queries zSigDdh0W a1R64WS ≤ 4 := by
  simp only [
    a1gStepC, Comp.letC, a1gPreC, a1gInitPrinC, a1gGenSpkC,
    liftGdhComp_r64, sigChalQ_dsl_r64, liftChal_gdh_r64,
    findHonestC_r64, isGameSpkC_r64, isGameOpkC_r64, resolveSigPkC_r64,
    isAdvPowsC_r64, koskBundleOkPowsC_r64, koskSenderOkPowsC_r64, lookupSpkSkC_r64,
    fgStepC,
    fgInitPrinC, fgGenSpkC, fgSendC, fgRecvC, fgRecvB, fgRoC, fgRoRootC, fgRegisterC,
    onBaseF, corruptB, genOpkB,
    mkSecretPosC, mkPairPosC, twoSideC, twoSideOptC, ddhEqC, ddhEqOptC,
    entryMatchesC, patchC, rootPatchC,
    findMV, Comp.sampleBytes32, Comp.sampleBytes32C,
    Comp.sampleRandom64C, Comp.sampleDrKey96C,
    Comp.queryPrim, Comp.queryPrimC, Comp.queryDdh, Comp.queryChal,
    bindV, letV, caseOptV, caseSumV,
    zSigDdh0W, zGdh0W, zPrim0W,
    a1R64WS_bool, a1R64WS_bytes32, a1R64WS_random64, a1R64WS_drKey96, a1R64WS_msgKeys80,
    a1R64WS_index, Comp.queries,
    ite_true, ite_false, Bool.false_eq_true,
    Nat.zero_max, Nat.max_zero, max_self, Nat.add_zero, Nat.zero_add, Nat.mul_zero]
  omega

set_option linter.unusedSimpArgs false in
private theorem a1gStep2C_r64_le (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st : Var Γ₁ a1g2StTy) (q : Var Γ₂ authQueryTy) :
    (a1gStep2C S K (Δ := Δ) st q).queries zSigDdh0W a1R64WS ≤ 4 := by
  simp only [
    a1gStep2C, Comp.letC, a1gPre2C, a1gInitPrin2C, a1gGenSpk2C,
    liftGdhComp_r64, sigChalQ_dsl_r64, liftChal_gdh_r64,
    findHonestC_r64, isGameSpkC_r64, isGameOpkC_r64, resolveSigPkC_r64,
    isAdvPowsC_r64, koskBundleOkPowsC_r64, koskSenderOkPowsC_r64, lookupSpkSkC_r64,
    fgStep2C,
    fgInitPrin2C, fgGenSpk2C, fgSend2C, fgRecvC, fgRecvB, fgRoC, fgRoRootC, fgRegisterC,
    onBaseF, corruptB, genOpkB,
    mkSecretPosC, mkPairPosC, twoSideC, twoSideOptC, ddhEqC, ddhEqOptC,
    entryMatchesC, patchC, rootPatchC,
    findMV, Comp.sampleBytes32, Comp.sampleBytes32C,
    Comp.sampleRandom64C, Comp.sampleDrKey96C,
    Comp.queryPrim, Comp.queryPrimC, Comp.queryDdh, Comp.queryChal,
    bindV, letV, caseOptV, caseSumV,
    zSigDdh0W, zGdh0W, zPrim0W,
    a1R64WS_bool, a1R64WS_bytes32, a1R64WS_random64, a1R64WS_drKey96, a1R64WS_msgKeys80,
    a1R64WS_index, Comp.queries,
    ite_true, ite_false, Bool.false_eq_true,
    Nat.zero_max, Nat.max_zero, max_self, Nat.add_zero, Nat.zero_add, Nat.mul_zero]
  omega

@[simp] private theorem renameComp_r64
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} {t : Ty SignalPqxdh.LegacyCosted.pqSig}
    (ρ : KeyInd1KeyGapDh.Ren Γ Δ)
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqSigAndDdhIface Γ t) :
    (KeyInd1KeyGapDh.renameComp ρ c).queries zSigDdh0W a1R64WS = c.queries zSigDdh0W a1R64WS := by
  induction c generalizing Δ <;> simp [KeyInd1KeyGapDh.renameComp, Comp.queries, *]

set_option linter.unusedSimpArgs false in
private theorem a1g_finish_r64 (S : Setup) (K : Nat) :
    (fgAuth1KeyGapDhProg S K).finish.queries zSigDdh0W a1R64WS = 0 := by
  simp only [fgAuth1KeyGapDhProg, a1g2FinishDsl, letV, Comp.letC,
    renameComp_r64, liftGdhComp_r64, Comp.queryChal,
    fgFinish2Dsl, fgExtract2C, logScan2C, findMap2C, respCand2C, initDh1Cand2C,
    foldMV, findMV, mapMV, bindV, caseOptV,
    Comp.queryPrimC, Comp.queryDdh, zGdh0W, Comp.queries,
    Nat.add_zero, Nat.zero_add, Nat.max_zero, max_self, Nat.mul_zero]

set_option linter.unusedSimpArgs false in
@[simp] private theorem bernoulliRatioC_r64
    {Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} (A B : Nat) :
    (bernoulliRatioC (Δ := Δ) A B).queries zGdh0W a1R64WS = 0 := by
  unfold bernoulliRatioC
  split_ifs <;> simp [bindV, Comp.sampleIndexC, Comp.queries]

set_option linter.unusedSimpArgs false in
@[simp] private theorem sampleSpkPair2C_r64 (S : Setup)
    {Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} :
    (sampleSpkPair2C S (Δ := Δ)).queries zGdh0W a1R64WS = 0 := by
  unfold sampleSpkPair2C
  split_ifs <;> simp [bindV, Comp.sampleIndexC, Comp.queries]

set_option linter.unusedSimpArgs false in
@[simp] private theorem sampleRole2C_r64 (S : Setup)
    {Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} :
    (sampleRole2C S (Δ := Δ)).queries zGdh0W a1R64WS = 0 := by
  unfold sampleRole2C
  split_ifs <;> simp [bindV, Comp.sampleIndexC, Comp.queries]

set_option linter.unusedSimpArgs false in
private theorem a1g_init_r64 (S : Setup) (K : Nat) :
    (fgAuth1KeyGapDhProg S K).init.queries zSigDdh0W a1R64WS = 0 := by
  simp only [fgAuth1KeyGapDhProg, a1g2InitDsl, liftGdhComp_r64, fgInit2Dsl,
    sampleRole2C_r64, sampleSpkPair2C_r64, bindV, letV, Comp.letC,
    Comp.sampleIndexC, Comp.sampleBoolC, a1R64WS_bool, a1R64WS_index, Comp.queries,
    Nat.zero_add, Nat.add_zero]

theorem fgAuth1KeyGapDhProg_r64_le (S : Setup) (K q : ℕ) :
    (fgAuth1KeyGapDhProg S K).totalQueries (fun _ => 0) (sampR64W tlAuthSigDdh.hsmp) q ≤ 4 * q := by
  change (fgAuth1KeyGapDhProg S K).totalQueries zSigDdh0W a1R64WS q ≤ 4 * q
  dsimp only [CostedReduction.totalQueries]
  rw [a1g_init_r64, a1g_finish_r64]
  have hH : (fgAuth1KeyGapDhProg S K).handle.queries zSigDdh0W a1R64WS ≤ 4 :=
    a1gStep2C_r64_le S K (Δ := [a1g2StTy, authQueryTy]) .vz (.vs .vz)
  have hMul := Nat.mul_le_mul_left q hH
  omega

private theorem a1sPreC_r64 (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) :
    (a1sPreC S K (Δ := Δ) s q).queries zSigDdh0W a1R64WS = 0 := by
  simp only [a1sPreC, a1sSendCheckC, liftBase_r64, extractC_r64,
    caseSumV, Comp.caseSumC, Comp.iteC, bindV, letV, Comp.letC, Comp.queries,
    Nat.add_zero, Nat.max_zero]

private theorem a1sDelegate2C_r64_le (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) :
    (a1sDelegate2C S K (Δ := Δ) s q).queries zSigDdh0W a1R64WS ≤ 4 := by
  simp only [a1sDelegate2C, bindV, letV, Comp.letC, Comp.queries]
  have := a1gStep2C_r64_le S K (Γ₁ := a1g2StTy :: Δ) (Γ₂ := Γ₂) (Δ := a1g2StTy :: Δ) Var.vz q
  omega

private theorem a1sStep2C_r64_le (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) :
    (a1sStep2C S K (Δ := Δ) s q).queries zSigDdh0W a1R64WS ≤ 4 := by
  have hP := a1sPreC_r64 S K (Δ := Δ) s q
  have hD := a1sDelegate2C_r64_le S K (Δ := .unit :: (.sum a1sRS .unit) :: Δ) s q
  simp only [a1sStep2C, Comp.iteC, Comp.caseSumC, bindV, caseSumV, Comp.queries]
  omega

theorem sigAuth1KeyProg_r64_le (S : Setup) (K q : ℕ) :
    (sigAuth1KeyProg S K).totalQueries (fun _ => 0) (sampR64W tlAuthSigDdh.hsmp) q ≤ 4 * q := by
  change (sigAuth1KeyProg S K).totalQueries zSigDdh0W a1R64WS q ≤ 4 * q
  have hI : (sigAuth1KeyProg S K).init.queries zSigDdh0W a1R64WS = 0 := by
    simp only [sigAuth1KeyProg, a1sInit2Dsl, bindV, letV, Comp.letC,
      Comp.sampleIndexC, Comp.sampleBoolC, a1R64WS_bool, a1R64WS_index, Comp.queries,
      Nat.add_zero]
  have hF : (sigAuth1KeyProg S K).finish.queries zSigDdh0W a1R64WS = 0 := by
    simp only [sigAuth1KeyProg, a1sFinishDsl, Comp.queries]
  have hH : (sigAuth1KeyProg S K).handle.queries zSigDdh0W a1R64WS ≤ 4 :=
    a1sStep2C_r64_le S K (Δ := [a1sStTy, authQueryTy])
      (.vz : Var [a1sStTy, authQueryTy] a1sStTy) (.vs .vz : Var [a1sStTy, authQueryTy] authQueryTy)
  dsimp only [CostedReduction.totalQueries]
  rw [hI, hF]
  have hMul := Nat.mul_le_mul_left q hH
  omega

end Auth1KeyR64

section ShCr1KeySize

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.LegacyCosted
open _root_.SignalPqxdh.Security
open _root_.SignalPqxdh.Security.ReductionDsl
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
open Computational.Proofs.SignalPqxdh.AtomicLift

private theorem initPrin1KeyB_size_le (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initPrin1KeyB (Δ := Δ) K st u).size ≤ (initPrinB (Δ := Δ) K st u).size := by
  simp only [initPrin1KeyB, initPrinB, bindV, rs, aNone, aInitPrin, stUpd, stMk, peMk,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb, stSOE,
    stSNE, stROE, stRNE, stRo, stRoot, stAdv, v, Comp.iteC, Comp.sampleBytes32, Comp.queryPrim,
    Expr.litBool, Expr.listCons, Comp.size, Expr.size]
  omega

private theorem onBase_size_le {Γ₁ Δ : List (Ty pqSig)} (s : Var Γ₁ shcrStTy) [Ext Γ₁ Δ]
    (br₁ br₂ : (g : Var (authStateTy :: Δ) authStateTy) →
      Comp pqxdhOps pqPrimIface (authStateTy :: Δ) RS)
    (h : (br₁ .vz).size ≤ (br₂ .vz).size) :
    (onBase (Δ := Δ) s br₁).size ≤ (onBase (Δ := Δ) s br₂).size := by
  dsimp only [onBase, bindV, letV, Comp.letC, Comp.size]
  omega

private theorem caseSumV_size_le_left {τ₁ τ₂ τ : Ty pqSig} {Γ : List (Ty pqSig)}
    (e : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (l₁ l₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ)
    (r : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps pqPrimIface (τ₂ :: Γ) τ)
    (hl : (l₁ .vz).size ≤ (l₂ .vz).size) :
    (caseSumV e l₁ r).size ≤ (caseSumV e l₂ r).size := by
  dsimp only [caseSumV, Comp.caseSumC, Comp.size]
  omega

private theorem shcrPost1KeyC_size_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrPost1KeyC (Δ := Δ) S K s q).size ≤ (shcrPostC (Δ := Δ) S K s q).size := by
  rw [shcrPost1KeyC_eq_tail, shcrPostC_eq_tail]
  refine caseSumV_size_le_left _ _ _ (shcrPostTailC S K s) ?_
  exact onBase_size_le s _ _ (initPrin1KeyB_size_le K (Γ₁ := authStateTy :: .nat :: Δ)
    (Γ₂ := .nat :: Δ) (Δ := authStateTy :: .nat :: Δ) .vz .vz)

private theorem shcrPre1KeyC_size_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrPre1KeyC (Δ := Δ) S K s q).size ≤ (shcrPreC (Δ := Δ) S K s q).size := by
  have h := shcrPost1KeyC_size_le S K (Γ₁ := Γ₁) (Γ₂ := Γ₂) (Δ := (.opt pauseTy) :: Δ) s q
  dsimp only [shcrPre1KeyC, shcrPreC, bindV, caseOptV, Comp.caseOptC, Comp.size]
  omega

private theorem shcrReductionAuthProg1Key_size_le (S : Setup) (Q K : Nat) :
    (shcrReductionAuthProg1Key S Q K).size ≤ (shcrReductionAuthProg S Q K).size := by
  have hPre : (shcrReductionAuthProg1Key S Q K).handlePre.size ≤
      (shcrReductionAuthProg S Q K).handlePre.size :=
    shcrPre1KeyC_size_le S K (Γ₁ := [shcrStTy, authQueryTy]) (Γ₂ := [authQueryTy])
      (Δ := [shcrStTy, authQueryTy]) .vz .vz
  have hPost : (shcrReductionAuthProg1Key S Q K).handlePost.size ≤
      (shcrReductionAuthProg S Q K).handlePost.size :=
    shcrPost1KeyC_size_le S K (Γ₁ := [shcrStTy, authQueryTy]) (Γ₂ := [authQueryTy])
      (Δ := [shcrStTy, authQueryTy]) .vz .vz
  unfold TwoStageCostedReduction.size
  change (shcrReductionAuthProg S Q K).init.size + _ +
      (shcrReductionAuthProg S Q K).chDone.size + (shcrReductionAuthProg S Q K).resume.size +
      _ + (shcrReductionAuthProg S Q K).finish.size ≤ _
  omega

private theorem initPrin1KeyB_litSize_le (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    compLitSize (initPrin1KeyB (Δ := Δ) K st u) ≤ compLitSize (initPrinB (Δ := Δ) K st u) := by
  simp only [initPrin1KeyB, initPrinB, bindV, rs, aNone, aInitPrin, stUpd, stMk, peMk,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb, stSOE,
    stSNE, stROE, stRNE, stRo, stRoot, stAdv, v, Comp.iteC, Comp.sampleBytes32, Comp.queryPrim,
    Expr.litBool, Expr.listCons, compLitSize, exprLitSize]
  omega

private theorem shcrPost1KeyC_litSize_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    compLitSize (shcrPost1KeyC (Δ := Δ) S K s q) ≤ compLitSize (shcrPostC (Δ := Δ) S K s q) := by
  rw [shcrPost1KeyC_eq_tail, shcrPostC_eq_tail]
  have h := initPrin1KeyB_litSize_le K (Γ₁ := authStateTy :: .nat :: Δ)
    (Γ₂ := .nat :: Δ) (Δ := authStateTy :: .nat :: Δ) .vz .vz
  dsimp only [caseSumV, Comp.caseSumC, onBase, bindV, letV, Comp.letC, compLitSize]
  omega

private theorem shcrPre1KeyC_litSize_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    compLitSize (shcrPre1KeyC (Δ := Δ) S K s q) ≤ compLitSize (shcrPreC (Δ := Δ) S K s q) := by
  have h := shcrPost1KeyC_litSize_le S K (Γ₁ := Γ₁) (Γ₂ := Γ₂) (Δ := (.opt pauseTy) :: Δ) s q
  dsimp only [shcrPre1KeyC, shcrPreC, bindV, caseOptV, Comp.caseOptC, compLitSize]
  omega

private theorem shcrReductionAuthProg1Key_litSize_le (S : Setup) (Q K : Nat) :
    red2LitSize (shcrReductionAuthProg1Key S Q K) ≤ red2LitSize (shcrReductionAuthProg S Q K) := by
  have hPre : compLitSize (shcrReductionAuthProg1Key S Q K).handlePre ≤
      compLitSize (shcrReductionAuthProg S Q K).handlePre :=
    shcrPre1KeyC_litSize_le S K (Γ₁ := [shcrStTy, authQueryTy]) (Γ₂ := [authQueryTy])
      (Δ := [shcrStTy, authQueryTy]) .vz .vz
  have hPost : compLitSize (shcrReductionAuthProg1Key S Q K).handlePost ≤
      compLitSize (shcrReductionAuthProg S Q K).handlePost :=
    shcrPost1KeyC_litSize_le S K (Γ₁ := [shcrStTy, authQueryTy]) (Γ₂ := [authQueryTy])
      (Δ := [shcrStTy, authQueryTy]) .vz .vz
  unfold red2LitSize
  change compLitSize (shcrReductionAuthProg S Q K).init + _ +
      compLitSize (shcrReductionAuthProg S Q K).chDone +
      compLitSize (shcrReductionAuthProg S Q K).resume +
      _ + compLitSize (shcrReductionAuthProg S Q K).finish ≤ _
  omega

end ShCr1KeySize

section GapDhSig1KeyLitSize

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.LegacyCosted
open _root_.SignalPqxdh.Security
open _root_.SignalPqxdh.Security.ReductionDsl
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
open Computational.Proofs.SignalPqxdh.AtomicLift

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] sigAndDdhOracle gapDhDdhOracle

@[simp] private theorem a1_v_litSize {Γ Δ : List (Ty pqSig)}
    {τ : Ty pqSig} [Ext Γ Δ] (x : Var Γ τ) :
    exprLitSize (v (Δ := Δ) x) = 0 := rfl

@[simp] private theorem a1_liftGdhComp_litSize
    {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    compLitSize (KeyInd1KeyGapDh.liftGdhComp c) = compLitSize c := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [KeyInd1KeyGapDh.liftGdhComp, compLitSize]

@[simp] private theorem a1_liftChal_gdh_litSize
    {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    compLitSize (Comp.liftChal (C := gapDhDdhOracle) c) = compLitSize c := by
  induction c with
  | query _ _ => rfl
  | sample _ _ => rfl
  | _ => simp_all [Comp.liftChal, compLitSize]

@[simp] private theorem a1_liftBase_litSize
    {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    compLitSize (KeyInd.liftBase (C := sigAndDdhOracle) c) = compLitSize c := by
  induction c with
  | query _ _ => rfl
  | sample _ _ => rfl
  | _ => simp_all [KeyInd.liftBase, compLitSize]

@[simp] private theorem a1_liftBase_sigDdh_litSize
    {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    compLitSize (I := pqSigAndDdhIface) (KeyInd.liftBase (C := sigAndDdhOracle) c) =
      compLitSize c :=
  a1_liftBase_litSize c

@[simp] private theorem a1_renameExpr_litSize
    {Γ Δ : List (Ty pqSig)} {τ : Ty pqSig}
    (ρ : KeyInd1KeyGapDh.Ren Γ Δ) (e : Expr pqxdhOps Γ τ) :
    exprLitSize (KeyInd1KeyGapDh.renameExpr ρ e) = exprLitSize e := by
  induction e generalizing Δ <;> simp only [KeyInd1KeyGapDh.renameExpr, exprLitSize, *]

@[simp] private theorem a1_renameComp_litSize {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T}
    {Γ Δ : List (Ty pqSig)} {τ : Ty pqSig}
    (ρ : KeyInd1KeyGapDh.Ren Γ Δ) (c : Comp pqxdhOps I Γ τ) :
    compLitSize (KeyInd1KeyGapDh.renameComp ρ c) = compLitSize c := by
  induction c generalizing Δ <;>
    simp only [KeyInd1KeyGapDh.renameComp, compLitSize, a1_renameExpr_litSize, *]

private theorem a1_F_X25519_length : F_X25519.length = 32 := rfl


set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem a1_fgStep2C_litSize_le (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (pa : Var Γ₁ a1gParams2Ty) (sim : Var Γ₂ fgSimTy) (q : Var Γ₃ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    compLitSize (AuthHs.fgStep2C (Δ := Δ) S K pa sim q) ≤ 18500 := by
  simp (config := { maxSteps := 1000000 }) only [fgStep2C, fgInitPrin2C, fgGenSpk2C, fgSend2C,
    fgRecvC, fgRecvB, fgRoC, fgRoRootC, fgRegisterC, onBaseF,
    isAdvPowsC, koskBundleOkPowsC, koskSenderOkPowsC, lookupSpkSkC,
    mkSecretPosC, mkPairPosC, twoSideC, twoSideOptC, ddhEqC, ddhEqOptC, entryMatchesC,
    patchC, rootPatchC, sendGuardE,
    fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
    pa2U, pa2V, pa2Role, pa2TS, pa2Dh1, feP1, feP2, feP3, feP4, feSs, feDk,
    pkP1, pkP2, pkP3, pkP4, pkSs, reRk, rePos, reRk1, reCk,
    q4, bytesEmpty, slice32, zero32, emptySimE,
    initPrinB, corruptB, genSpkB, genOpkB, registerB, sendC, sendB, recvTailC, recvB, roB, roRootB,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, honestPeerC, hkdfOrRoC, rootRoC,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    seSid, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon, sePqspkHon,
    seEkASk, seEphASk, seFresh, seChal, seMk,
    pmHdr, pmEphAPk, pmPqMsg, pmAeadCt, pmMk, pmUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk,
    oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk, buUpd,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk, hdUpd,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, rs, firstMsgADE, bytes2Eq, emptyAuthStE,
    isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE, kyberCheckE,
    natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32, buildSecretsE, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM,
    a1_liftChal_gdh_litSize, a1_v_litSize, v, Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, anyMV, mapMV,
    foldMV, eLet, eCaseOpt, eCaseSum,
    eFind, eAny, eMap,
    Expr.litBytes, Expr.bytesAppend, Expr.bytesCons, Expr.bytesWiden,
    Expr.bytesTakeK, Expr.bytesDrop, Expr.bytesLen, Expr.bytesBeq, Expr.bytesVarint,
    Expr.u32OfNat, Expr.u32Beq,
    Comp.sampleBool, Comp.sampleBytes32, Comp.sampleRandom64, Comp.sampleDrKey96,
    Comp.sampleIndex, Comp.queryPrim,
    Comp.sampleBoolC, Comp.sampleBytes32C, Comp.sampleRandom64C, Comp.sampleDrKey96C,
    Comp.sampleIndexC, Comp.queryPrimC, Comp.queryChal, AuthHs.Comp.queryDdh,
    encEC, encKEM,
    compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, List.length_replicate, a1_F_X25519_length,
    Nat.add_zero, Nat.zero_add,
    ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
  omega

set_option linter.unusedSimpArgs false in
private theorem a1gStep2C_litSize_le (S : Setup) (K : Nat)
    {Γs Γq Δ : List (Ty pqSig)} [Ext Γs Δ] [Ext Γq Δ]
    (st : Var Γs a1g2StTy) (q : Var Γq authQueryTy) :
    compLitSize (a1gStep2C S K (Δ := Δ) st q) ≤ 20000 := by
  have hFg := a1_fgStep2C_litSize_le S K
    (Γ₁ := a1gParams2Ty :: Δ)
    (Γ₂ := fgSimTy :: a1gParams2Ty :: Δ)
    (Γ₃ := Γq)
    (Δ := .unit :: (.sum RSB .unit) :: .nat :: fgSimTy :: a1gParams2Ty :: Δ)
    .vz .vz q
  simp only [a1gStep2C, a1gPre2C, a1gInitPrin2C, a1gGenSpk2C,
    a1_liftGdhComp_litSize, KeyInd1KeyGapDh.sigChalQ_dsl,
    fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
    pa2U, pa2V, pa2Role, pa2TS, pa2Dh1,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
    aNone, aInitPrin, aBundle,
    natEq, nat2Eq,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Comp.iteC, Comp.caseOptC, Comp.caseSumC,
    Expr.findBounded, Expr.anyBounded,
    a1_v_litSize, v, Comp.letC, bindV, letV, caseOptV, caseSumV,
    eCaseOpt, eCaseSum, eFind, eAny,
    Expr.litBytes, Expr.bytesCons, Expr.u32OfNat,
    Comp.sampleBytes32C, Comp.sampleRandom64C, Comp.queryPrimC,
    encEC, encKEM,
    compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, Nat.add_zero, Nat.zero_add]
  omega

set_option linter.unusedSimpArgs false in
private theorem bernoulliRatioC_litSize_le {Δ : List (Ty pqSig)} (A B : Nat) :
    compLitSize (bernoulliRatioC (Δ := Δ) A B) ≤ 20 := by
  unfold bernoulliRatioC
  split_ifs <;> simp [bindV, Comp.sampleIndexC, Expr.litBool, Expr.litNat, Expr.boolNot,
    a1_v_litSize, v, compLitSize, exprLitSize, pqOpLitSize]

set_option linter.unusedSimpArgs false in
private theorem sampleSpkPair2C_litSize_le (S : Setup) {Δ : List (Ty pqSig)} :
    compLitSize (sampleSpkPair2C S (Δ := Δ)) ≤ 20 := by
  unfold sampleSpkPair2C
  split_ifs <;> simp [bindV, Comp.sampleIndexC, Expr.noneE, Expr.someE,
    a1_v_litSize, v, compLitSize, exprLitSize, pqOpLitSize]

set_option linter.unusedSimpArgs false in
private theorem sampleRole2C_litSize_le (S : Setup) {Δ : List (Ty pqSig)} :
    compLitSize (sampleRole2C S (Δ := Δ)) ≤ 50 := by
  unfold sampleRole2C
  split_ifs <;>
  · have hb := bernoulliRatioC_litSize_le (Δ := .nat :: .nat :: Δ) S.N_send_opk S.N_send_no_opk
    simp only [bindV, Comp.sampleIndexC, Comp.iteC, natEq, Expr.litNat,
      a1_v_litSize, v, compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]
    omega

set_option linter.unusedSimpArgs false in
private theorem fgFinish2Dsl_litSize_le (S : Setup) (K : Nat) :
    compLitSize (fgFinish2Dsl S K) ≤ 1050 := by
  simp only [fgFinish2Dsl, fgExtract2C, findMap2C, logScan2C, respCand2C, initDh1Cand2C,
    fsBase, fsLog, fsResp, fsPows, pa2U, pa2V, pa2Role, pa2Dh1,
    stPrin, stSpks, stSess, seSid, sePeerSpk, seEkASk, peIkAPk, sbSpkSk, sbSpkPk,
    natEq, nat2Eq, bytesEmpty, slice32, zero32,
    Expr.litBool, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.mapBoundedM, Comp.foldBoundedM,
    Expr.findBounded, Expr.mapBounded,
    a1_v_litSize, v, Comp.letC, bindV, letV, caseOptV, findMV, mapMV, foldMV,
    eCaseOpt, eCaseSum, eFind, eMap,
    Expr.litBytes, Expr.bytesTakeK, Expr.bytesDrop, Expr.bytesBeq,
    Comp.queryPrimC, Comp.queryDdh, Comp.queryChal,
    compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_replicate, Nat.add_zero, Nat.zero_add]
  omega

set_option linter.unusedSimpArgs false in
private theorem fgAuth1KeyGapDhProg_litSize_le (S : Setup) (K : Nat) :
    red1LitSize (fgAuth1KeyGapDhProg S K) ≤ 22000 := by
  have hR := sampleRole2C_litSize_le S (Δ := [.prod (B 32) (B 32)])
  have hSpk := sampleSpkPair2C_litSize_le S (Δ := a1gRole2Ty :: [.prod (B 32) (B 32)])
  have hI : compLitSize (a1g2InitDsl S K) ≤ 250 := by
    simp only [a1g2InitDsl, fgInit2Dsl, emptySimE, emptyAuthStE, fsMk, stMk,
      Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.listNil,
      a1_liftGdhComp_litSize, a1_v_litSize, v, bindV, Comp.sampleBoolC,
      compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]
    omega
  have hH : compLitSize (a1g2HandleDsl S K) ≤ 20000 :=
    a1gStep2C_litSize_le S K (Δ := [a1g2StTy, authQueryTy]) .vz (.vs .vz)
  have hF0 := fgFinish2Dsl_litSize_le S K
  have hF : compLitSize (a1g2FinishDsl S K) ≤ 1050 := by
    simp only [a1g2FinishDsl, letV, Comp.letC, a1_renameComp_litSize, a1_liftGdhComp_litSize,
      compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]
    omega
  change compLitSize (a1g2InitDsl S K) + compLitSize (a1g2HandleDsl S K) +
    compLitSize (a1g2FinishDsl S K) ≤ _
  omega

set_option linter.unusedSimpArgs false in
private theorem a1sPreC_litSize_le (S : Setup) (K : Nat)
    {Γs Γq Δ : List (Ty pqSig)}
    [Ext Γs Δ] [Ext Γq Δ] (s : Var Γs a1sStTy) (q : Var Γq authQueryTy) :
    compLitSize (a1sPreC S K (Δ := Δ) s q) ≤ 900 := by
  simp only [a1sPreC, a1sSendCheckC, a1sTp, a1sTpk, a1sBase, a1sG, a1sMk, fsBase,
    a1_liftBase_litSize, a1_liftBase_sigDdh_litSize, extractC, honestPeerC, findHonestC,
    stPrin, stSpks, peIkAPk, peCorrupted, sbSpkPk, sbPqspkPk,
    buIkB, buSpkB, buSpkSig, buPqspkB, buPqspkSig,
    natEq, isSomeE, aNone,
    Expr.litUnit, Expr.litBool, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.bytesWiden, Expr.bytesCons, Expr.bytesBeq, encEC, encKEM,
    Comp.iteC, Comp.caseSumC, Comp.findBoundedM,
    Expr.findBounded, Expr.anyBounded,
    a1_v_litSize, v, Comp.letC, bindV, letV, caseSumV, findMV,
    eCaseOpt, eAny,
    Comp.queryPrim,
    compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, Nat.add_zero, Nat.zero_add]
  omega

set_option linter.unusedSimpArgs false in
private theorem sigAuth1KeyProg_litSize_le (S : Setup) (K : Nat) :
    red1LitSize (sigAuth1KeyProg S K) ≤ 22000 := by
  have hD : ∀ {Γs Γq Δ : List (Ty pqSig)} [Ext Γs Δ] [Ext Γq Δ]
      (s : Var Γs a1sStTy) (q : Var Γq authQueryTy),
      compLitSize (a1sDelegate2C S K (Δ := Δ) s q) ≤ 20100 := by
    intro Γs Γq Δ _ _ s q
    have := a1gStep2C_litSize_le S K (Γs := a1g2StTy :: Δ) (Γq := Γq) (Δ := a1g2StTy :: Δ) Var.vz q
    simp only [a1sDelegate2C, a1sCaseAPa2, a1sG, a1sMk, a1sTp, a1sTpk, a1sFg, Expr.noneE,
      a1_v_litSize, v, Comp.letC, bindV, letV, compLitSize, exprLitSize, pqOpLitSize,
      Nat.add_zero, Nat.zero_add]
    omega
  have hH : compLitSize (a1sHandle2Dsl S K) ≤ 21100 := by
    have hP := a1sPreC_litSize_le S K
      (Γs := [a1sStTy, authQueryTy]) (Γq := [a1sStTy, authQueryTy])
      (Δ := [a1sStTy, authQueryTy]) .vz (.vs .vz)
    have hDel := hD
      (Γs := [a1sStTy, authQueryTy]) (Γq := [a1sStTy, authQueryTy])
      (Δ := .unit :: (.sum a1sRS .unit) :: [a1sStTy, authQueryTy]) .vz (.vs .vz)
    dsimp only [a1sHandle2Dsl]
    simp only [a1sStep2C, a1sFg, isSomeE, aNone, Expr.litUnit, Expr.litBool, Comp.iteC,
      Comp.caseSumC, a1_v_litSize, v, bindV, caseSumV,
      compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]
    omega
  have hI : compLitSize (a1sInit2Dsl S K) ≤ 200 := by
    simp only [a1sInit2Dsl, a1sDummyPa, a1sMk, emptySimE, emptyAuthStE, fsMk, stMk,
      Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.listNil,
      a1_v_litSize, v, Comp.letC, bindV, letV,
      Comp.sampleIndexC, Comp.sampleBoolC, compLitSize, exprLitSize, pqOpLitSize,
      Nat.add_zero, Nat.zero_add]
    omega
  have hF : compLitSize a1sFinishDsl ≤ 100 := by
    simp only [a1sFinishDsl, a1sFg, eCaseOpt, Expr.litBytes,
      a1_v_litSize, v, compLitSize, exprLitSize, pqOpLitSize,
      List.length_nil, Nat.add_zero, Nat.zero_add]
    omega
  change compLitSize (a1sInit2Dsl S K) + compLitSize (a1sHandle2Dsl S K) + compLitSize a1sFinishDsl ≤ _
  omega

end GapDhSig1KeyLitSize

section Prf1KeySize

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.LegacyCosted
open _root_.SignalPqxdh.Security
open _root_.SignalPqxdh.Security.ReductionDsl
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
open Computational.Proofs.SignalPqxdh.AtomicLift

private theorem size_liftPrimComp {C : ChallengerOracle} :
    ∀ {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t),
      (liftPrimComp (C := C) c).size = c.size
  | _, _, .ret _ | _, _, .sample _ _ | _, _, .query _ _ => rfl
  | _, _, .bind m k => by simp [liftPrimComp, Comp.size, size_liftPrimComp m, size_liftPrimComp k]
  | _, _, .ite _ t e => by simp [liftPrimComp, Comp.size, size_liftPrimComp t, size_liftPrimComp e]
  | _, _, .caseOpt _ n s => by
    simp [liftPrimComp, Comp.size, size_liftPrimComp n, size_liftPrimComp s]
  | _, _, .caseSum _ l r => by
    simp [liftPrimComp, Comp.size, size_liftPrimComp l, size_liftPrimComp r]
  | _, _, .iter _ _ b | _, _, .findM _ _ b | _, _, .anyM _ _ b | _, _, .mapM _ _ b
  | _, _, .consumeFirstM _ _ b _ | _, _, .foldM _ _ _ b => by
    simp [liftPrimComp, Comp.size, size_liftPrimComp b]

private theorem size_liftPrimComp_mk {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    Comp.size (I := pqPrfMkIface) (liftPrimComp c) = c.size :=
  size_liftPrimComp c

private theorem size_liftPrimComp_hmac {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    Comp.size (I := pqPrfHmacIface) (liftPrimComp c) = c.size :=
  size_liftPrimComp c

private theorem litSize_liftPrimComp {C : ChallengerOracle} :
    ∀ {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t),
      compLitSize (liftPrimComp (C := C) c) = compLitSize c
  | _, _, .ret _ | _, _, .sample _ _ | _, _, .query _ _ => rfl
  | _, _, .bind m k => by
    simp [liftPrimComp, compLitSize, litSize_liftPrimComp m, litSize_liftPrimComp k]
  | _, _, .ite _ t e => by
    simp [liftPrimComp, compLitSize, litSize_liftPrimComp t, litSize_liftPrimComp e]
  | _, _, .caseOpt _ n s => by
    simp [liftPrimComp, compLitSize, litSize_liftPrimComp n, litSize_liftPrimComp s]
  | _, _, .caseSum _ l r => by
    simp [liftPrimComp, compLitSize, litSize_liftPrimComp l, litSize_liftPrimComp r]
  | _, _, .iter _ _ b | _, _, .findM _ _ b | _, _, .anyM _ _ b | _, _, .mapM _ _ b
  | _, _, .consumeFirstM _ _ b _ | _, _, .foldM _ _ _ b => by
    simp [liftPrimComp, compLitSize, litSize_liftPrimComp b]

private theorem litSize_liftPrimComp_mk {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    compLitSize (I := pqPrfMkIface) (liftPrimComp c) = compLitSize c :=
  litSize_liftPrimComp c

private theorem litSize_liftPrimComp_hmac {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    compLitSize (I := pqPrfHmacIface) (liftPrimComp c) = compLitSize c :=
  litSize_liftPrimComp c

private theorem initPrin1KeyFixedB_size_le (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initPrin1KeyFixedB (Δ := Δ) K fhst u).size ≤ (initPrinFixedB (Δ := Δ) K fhst u).size := by
  simp only [initPrin1KeyFixedB, initPrinFixedB, letV, bindV, AuthPrf.Comp.letC, samplePrim,
    queryPrim, Comp.size, fhstSetBase, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    ahsfMkSlots, ahsfUpd,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsMk, ahsUpd,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys, stMk, stUpd, peMk, aNone, aInitPrin, v, Expr.size]
  omega

private theorem initPrin1KeyFixedB_litSize_le (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    compLitSize (initPrin1KeyFixedB (Δ := Δ) K fhst u) ≤
      compLitSize (initPrinFixedB (Δ := Δ) K fhst u) := by
  simp only [initPrin1KeyFixedB, initPrinFixedB, letV, bindV, AuthPrf.Comp.letC, samplePrim,
    queryPrim, compLitSize, fhstSetBase, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    ahsfMkSlots, ahsfUpd,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsMk, ahsUpd,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys, stMk, stUpd, peMk, aNone, aInitPrin, v,
    exprLitSize]
  omega

private theorem prfCkRedProg1Key_size_le (S : Setup) (K : Nat) :
    (prfCkRedProg1Key S K).size ≤ (prfCkRedProg S K).size := by
  have hStep : ∀ {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT} (idx : Var Γ₁ .nat)
      (chalP : Var Γ₂ (.prod (B 32) (B 32))) (fhst : Var Γ₃ authHybridStateFixedTy)
      (q : Var Γ₄ AuthPrf.authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ],
      (authCkStep1KeyC (Δ := Δ) S K idx chalP fhst q).size ≤
        (authCkStepC (Δ := Δ) S K idx chalP fhst q).size := by
    intro _ _ _ _ _ idx chalP fhst q _ _ _ _
    simp only [authCkStep1KeyC, authCkStepC, caseSumV, Comp.size]
    gcongr
    exact initPrin1KeyFixedB_size_le K fhst _
  have hH : (prfCkHandle1KeyDsl S K).size ≤ (prfCkHandleDsl S K).size := by
    simp only [prfCkHandle1KeyDsl, prfCkHandleDsl, letV, bindV, AuthPrf.Comp.letC, Comp.size]
    gcongr
    exact hStep _ _ _ _
  simp only [CostedReduction.size, prfCkRedProg1Key, prfCkRedProg]
  omega

private def prfMkInitGen (N M : Nat)
    (k : Var ([.bool, .nat, .unit] : List PT) .bool → Var ([.nat, .unit] : List PT) .nat →
      Expr pqxdhOps ([.bool, .nat, .unit] : List PT) prfMkCoreTy) :
    Comp pqxdhOps pqPrfMkIface [.unit] (.prod .unit prfMkStTy) :=
  bindV (sampleChal (.index N)) fun idx =>
  bindV (sampleChal .bool) fun secb =>
  .ret (.pair .unit (.pair (.nat M) (k secb idx)))

private theorem prfMkInitGen_size_le {N₁ M₁ N₂ M₂ : Nat} (hN : N₁ ≤ N₂) (hM : M₁ ≤ M₂)
    (k : Var ([.bool, .nat, .unit] : List PT) .bool → Var ([.nat, .unit] : List PT) .nat →
      Expr pqxdhOps ([.bool, .nat, .unit] : List PT) prfMkCoreTy) :
    (prfMkInitGen N₁ M₁ k).size ≤ (prfMkInitGen N₂ M₂ k).size := by
  dsimp only [prfMkInitGen, bindV, sampleChal, Comp.size, Expr.size, _root_.ReductionDsl.bits]
  have hlN := Nat.log_mono_right (b := 2) hN
  have hlM := Nat.log_mono_right (b := 2) hM
  omega

private theorem prfMkInitGen_litSize_le {N₁ M₁ N₂ M₂ : Nat} (hN : N₁ ≤ N₂) (hM : M₁ ≤ M₂)
    (k : Var ([.bool, .nat, .unit] : List PT) .bool → Var ([.nat, .unit] : List PT) .nat →
      Expr pqxdhOps ([.bool, .nat, .unit] : List PT) prfMkCoreTy) :
    compLitSize (prfMkInitGen N₁ M₁ k) ≤ compLitSize (prfMkInitGen N₂ M₂ k) := by
  dsimp only [prfMkInitGen, bindV, sampleChal, compLitSize, exprLitSize, _root_.ReductionDsl.bits]
  have hlN := Nat.log_mono_right (b := 2) hN
  have hlM := Nat.log_mono_right (b := 2) hM
  omega

private theorem prfMsgKeysInitDslK_size_le (S : Setup) (K : Nat) :
    (prfMsgKeysInitDslK S K).size ≤ (prfMsgKeysInitDsl S).size :=
  prfMkInitGen_size_le (Nat.min_le_right K S.N_sess_tot)
    (Nat.add_le_add_right (Nat.min_le_right K S.N_recv_tot) 1) _

private theorem prfMsgKeysInitDslK_litSize_le (S : Setup) (K : Nat) :
    compLitSize (prfMsgKeysInitDslK S K) ≤ compLitSize (prfMsgKeysInitDsl S) :=
  prfMkInitGen_litSize_le (Nat.min_le_right K S.N_sess_tot)
    (Nat.add_le_add_right (Nat.min_le_right K S.N_recv_tot) 1) _

set_option linter.unusedSimpArgs false in
private theorem prfMsgKeysRedProg1Key_size_le (S : Setup) (K : Nat) :
    (prfMsgKeysRedProg1Key S K).size ≤ (prfMsgKeysRedProg S K).size := by
  have hPre : ∀ {Γ₁ Γ₂ Δ : List PT} (core : Var Γ₁ prfMkCoreTy) (q : Var Γ₂ AuthPrf.authQueryTy)
      [Ext Γ₁ Δ] [Ext Γ₂ Δ],
      (prfMkStepPre1KeyC (Δ := Δ) S K core q).size ≤
        (prfMkStepPreC (Δ := Δ) S K core q).size := by
    intro _ _ _ core q _ _
    simp only [prfMkStepPre1KeyC, prfMkStepPreC, letV, bindV, AuthPrf.Comp.letC, caseSumV,
      wrapMkBase, Comp.size]
    gcongr
    exact initPrin1KeyFixedB_size_le K _ _
  have hH : (prfMsgKeysHandle1KeyDsl S K).size ≤ (prfMsgKeysHandleDsl S K).size := by
    simp only [prfMsgKeysHandle1KeyDsl, prfMsgKeysHandleDsl, letV, bindV, AuthPrf.Comp.letC,
      size_liftPrimComp, size_liftPrimComp_mk, Comp.size]
    have := hPre (Γ₁ := [prfMkCoreTy, .nat, prfMkStTy, prfMkStTy, AuthPrf.authQueryTy])
      (Γ₂ := [prfMkStTy, AuthPrf.authQueryTy])
      (Δ := [prfMkCoreTy, .nat, prfMkStTy, prfMkStTy, AuthPrf.authQueryTy])
      .zero (.succ .zero)
    omega
  have hI := prfMsgKeysInitDslK_size_le S K
  dsimp only [CostedReduction.size, prfMsgKeysRedProg1Key, prfMsgKeysRedProg]
  omega

private theorem aeadCpaRedProg1Key_size_le (S : Setup) (K : Nat) :
    (aeadCpaRedProg1Key S K).size ≤ (aeadCpaRedProg S K).size := by
  have hStep : ∀ (allowPause : Bool),
      (cpaStep1KeyC S K allowPause).size ≤ (cpaStepC S K allowPause).size := by
    intro allowPause
    simp only [cpaStep1KeyC, cpaStepC, cpaNonSendSlot1KeyC, cpaNonSendSlotC,
      letV, bindV, AuthPrf.Comp.letC, caseSumV, wrapCpaSlot, Comp.size]
    have := initPrin1KeyFixedB_size_le K
      (Γ₁ := [authHybridStateFixedTy, .nat, .nat, cpaStTy, AuthPrf.authQueryTy])
      (Γ₂ := .nat :: [authHybridStateFixedTy, .nat, .nat, cpaStTy, AuthPrf.authQueryTy])
      (Δ := .nat :: [authHybridStateFixedTy, .nat, .nat, cpaStTy, AuthPrf.authQueryTy])
      .zero .zero
    omega
  have hPre : (cpaPre1KeyC S K).size ≤ (cpaPreC S K).size := hStep true
  have hPost : (cpaPost1KeyC S K).size ≤ (cpaPostC S K).size := by
    have := hStep false
    simp only [cpaPost1KeyC, cpaPostC, bindV, Comp.size]
    omega
  simp only [TwoStageCostedReduction.size, aeadCpaRedProg1Key, aeadCpaRedProg]
  omega

set_option linter.unusedSimpArgs false in
private theorem prfHmacRedProg1Key_size_le (S : Setup) (K : Nat) :
    (prfHmacRedProg1Key S K).size ≤ (prfHmacRedProg S K).size := by
  have hPre : (hmPre1KeyC S K).size ≤ (hmPreC S K).size := by
    simp only [hmPre1KeyC, hmPreC, hmDispatch1KeyC, hmDispatchC,
      letV, bindV, AuthPrf.Comp.letC, caseSumV, hmOther, Comp.size]
    have := initPrin1KeyFixedB_size_le K
      (Γ₁ := authHybridStateFixedTy :: .nat :: hmStTy :: [hmStTy, AuthPrf.authQueryTy])
      (Γ₂ := .nat :: muStTy :: authHybridStateFixedTy :: .nat :: hmStTy :: [hmStTy, AuthPrf.authQueryTy])
      (Δ := .nat :: muStTy :: authHybridStateFixedTy :: .nat :: hmStTy :: [hmStTy, AuthPrf.authQueryTy])
      .zero .zero
    omega
  have hH : (hmHandle1KeyC S K).size ≤ (hmHandleC S K).size := by
    simp only [hmHandle1KeyC, hmHandleC, bindV, size_liftPrimComp, size_liftPrimComp_hmac, Comp.size]
    omega
  simp only [CostedReduction.size, prfHmacRedProg1Key, prfHmacRedProg]
  omega

private theorem prfCkRedProg1Key_litSize_le (S : Setup) (K : Nat) :
    red1LitSize (prfCkRedProg1Key S K) ≤ red1LitSize (prfCkRedProg S K) := by
  have hStep : ∀ {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT} (idx : Var Γ₁ .nat)
      (chalP : Var Γ₂ (.prod (B 32) (B 32))) (fhst : Var Γ₃ authHybridStateFixedTy)
      (q : Var Γ₄ AuthPrf.authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ],
      compLitSize (authCkStep1KeyC (Δ := Δ) S K idx chalP fhst q) ≤
        compLitSize (authCkStepC (Δ := Δ) S K idx chalP fhst q) := by
    intro _ _ _ _ _ idx chalP fhst q _ _ _ _
    simp only [authCkStep1KeyC, authCkStepC, caseSumV, compLitSize]
    gcongr
    exact initPrin1KeyFixedB_litSize_le K fhst _
  have hH : compLitSize (prfCkHandle1KeyDsl S K) ≤ compLitSize (prfCkHandleDsl S K) := by
    simp only [prfCkHandle1KeyDsl, prfCkHandleDsl, letV, bindV, AuthPrf.Comp.letC, compLitSize]
    gcongr
    exact hStep _ _ _ _
  simp only [red1LitSize, prfCkRedProg1Key, prfCkRedProg]
  omega

set_option linter.unusedSimpArgs false in
private theorem prfMsgKeysRedProg1Key_litSize_le (S : Setup) (K : Nat) :
    red1LitSize (prfMsgKeysRedProg1Key S K) ≤ red1LitSize (prfMsgKeysRedProg S K) := by
  have hPre : ∀ {Γ₁ Γ₂ Δ : List PT} (core : Var Γ₁ prfMkCoreTy) (q : Var Γ₂ AuthPrf.authQueryTy)
      [Ext Γ₁ Δ] [Ext Γ₂ Δ],
      compLitSize (prfMkStepPre1KeyC (Δ := Δ) S K core q) ≤
        compLitSize (prfMkStepPreC (Δ := Δ) S K core q) := by
    intro _ _ _ core q _ _
    simp only [prfMkStepPre1KeyC, prfMkStepPreC, letV, bindV, AuthPrf.Comp.letC, caseSumV,
      wrapMkBase, compLitSize]
    gcongr
    exact initPrin1KeyFixedB_litSize_le K _ _
  have hH : compLitSize (prfMsgKeysHandle1KeyDsl S K) ≤ compLitSize (prfMsgKeysHandleDsl S K) := by
    simp only [prfMsgKeysHandle1KeyDsl, prfMsgKeysHandleDsl, letV, bindV, AuthPrf.Comp.letC,
      litSize_liftPrimComp, litSize_liftPrimComp_mk, compLitSize]
    have := hPre (Γ₁ := [prfMkCoreTy, .nat, prfMkStTy, prfMkStTy, AuthPrf.authQueryTy])
      (Γ₂ := [prfMkStTy, AuthPrf.authQueryTy])
      (Δ := [prfMkCoreTy, .nat, prfMkStTy, prfMkStTy, AuthPrf.authQueryTy])
      .zero (.succ .zero)
    omega
  have hI := prfMsgKeysInitDslK_litSize_le S K
  dsimp only [red1LitSize, prfMsgKeysRedProg1Key, prfMsgKeysRedProg]
  omega

private theorem aeadCpaRedProg1Key_litSize_le (S : Setup) (K : Nat) :
    red2LitSize (aeadCpaRedProg1Key S K) ≤ red2LitSize (aeadCpaRedProg S K) := by
  have hStep : ∀ (allowPause : Bool),
      compLitSize (cpaStep1KeyC S K allowPause) ≤ compLitSize (cpaStepC S K allowPause) := by
    intro allowPause
    simp only [cpaStep1KeyC, cpaStepC, cpaNonSendSlot1KeyC, cpaNonSendSlotC,
      letV, bindV, AuthPrf.Comp.letC, caseSumV, wrapCpaSlot, compLitSize]
    have := initPrin1KeyFixedB_litSize_le K
      (Γ₁ := [authHybridStateFixedTy, .nat, .nat, cpaStTy, AuthPrf.authQueryTy])
      (Γ₂ := .nat :: [authHybridStateFixedTy, .nat, .nat, cpaStTy, AuthPrf.authQueryTy])
      (Δ := .nat :: [authHybridStateFixedTy, .nat, .nat, cpaStTy, AuthPrf.authQueryTy])
      .zero .zero
    omega
  have hPre : compLitSize (cpaPre1KeyC S K) ≤ compLitSize (cpaPreC S K) := hStep true
  have hPost : compLitSize (cpaPost1KeyC S K) ≤ compLitSize (cpaPostC S K) := by
    have := hStep false
    simp only [cpaPost1KeyC, cpaPostC, bindV, compLitSize]
    omega
  simp only [red2LitSize, aeadCpaRedProg1Key, aeadCpaRedProg]
  omega

set_option linter.unusedSimpArgs false in
private theorem prfHmacRedProg1Key_litSize_le (S : Setup) (K : Nat) :
    red1LitSize (prfHmacRedProg1Key S K) ≤ red1LitSize (prfHmacRedProg S K) := by
  have hPre : compLitSize (hmPre1KeyC S K) ≤ compLitSize (hmPreC S K) := by
    simp only [hmPre1KeyC, hmPreC, hmDispatch1KeyC, hmDispatchC,
      letV, bindV, AuthPrf.Comp.letC, caseSumV, hmOther, compLitSize]
    have := initPrin1KeyFixedB_litSize_le K
      (Γ₁ := authHybridStateFixedTy :: .nat :: hmStTy :: [hmStTy, AuthPrf.authQueryTy])
      (Γ₂ := .nat :: muStTy :: authHybridStateFixedTy :: .nat :: hmStTy :: [hmStTy, AuthPrf.authQueryTy])
      (Δ := .nat :: muStTy :: authHybridStateFixedTy :: .nat :: hmStTy :: [hmStTy, AuthPrf.authQueryTy])
      .zero .zero
    omega
  have hH : compLitSize (hmHandle1KeyC S K) ≤ compLitSize (hmHandleC S K) := by
    simp only [hmHandle1KeyC, hmHandleC, bindV, litSize_liftPrimComp, litSize_liftPrimComp_hmac,
      compLitSize]
    omega
  simp only [red1LitSize, prfHmacRedProg1Key, prfHmacRedProg]
  omega

end Prf1KeySize

section ClampedShCrSize
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.Security
open _root_.SignalPqxdh.LegacyCosted
open _root_.SignalPqxdh.Security.ReductionDsl
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
private theorem ah_bits_mono {x y : ℕ} (h : x ≤ y) : bits x ≤ bits y := by
  unfold bits
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem ah_shcrReductionAuthProg_size_le_clamped (S : Setup) (Q K : Nat) :
    (shcrReductionAuthProg S Q K).size ≤
      bits Q + 175 * bits K + 21000 := by
  have hInit : (shcrReductionAuthProg S Q K).init.size ≤ 200 := by
    dsimp only [shcrReductionAuthProg]
    split_ifs <;>
      (simp only [v, bindV, scMk, emptyAuthStE, stMk,
        Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.listNil,
        Comp.sampleBool, Comp.sampleIndex,
        Comp.size, Expr.size]
       have hb0 : bits 0 = 1 := by decide
       omega)
  have hRest :
      (shcrReductionAuthProg S Q K).handlePre.size +
      (shcrReductionAuthProg S Q K).chDone.size +
      (shcrReductionAuthProg S Q K).resume.size +
      (shcrReductionAuthProg S Q K).handlePost.size +
      (shcrReductionAuthProg S Q K).finish.size ≤
      bits Q + 175 * bits K + 20800 := by
    dsimp only [shcrReductionAuthProg]
    simp (config := { maxSteps := 1000000 }) only [
      shcrPreC, pauseCheckC, tryPauseC, shcrPostC, shcrGenSpkB, sendGuardE, shcrSendC, shcrAcceptB,
      shcrResumeC, shcrExtractC, shcrFinC, onBase, preCheckC, checkSigsC, finishC,
      scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd, rrCt,
      pdSid, pdBu, pdM0, pdM1, pdUI,
      initPrinB, corruptB, genSpkB, genOpkB, registerB, sendC, sendB, recvTailC, recvB, roB, roRootB,
      findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
      resolveSigPkC, honestPeerC, hkdfOrRoC, rootRoC,
      stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
      stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
      seSid, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon, sePqspkHon,
      seEkASk, seEphASk, seFresh, seChal, seMk,
      pmHdr, pmEphAPk, pmPqMsg, pmAeadCt, pmMk, pmUpd,
      peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
      sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk,
      oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
      buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk, buUpd,
      hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk, hdUpd,
      aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
      aDrKey, aRootKdf, rs, firstMsgADE, bytes2Eq, emptyAuthStE,
      isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE, kyberCheckE,
      natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32, buildSecretsE, eLet2,
      v, Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, caseSumV,
      findMV, anyMV, mapMV, foldMV,
      eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
      Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
      Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
      Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
      Comp.foldBoundedM,
      Expr.litBytes, Expr.bytesAppend, Expr.bytesCons, Expr.bytesWiden,
      Expr.bytesTakeK, Expr.bytesDrop, Expr.bytesLen, Expr.bytesBeq, Expr.bytesVarint,
      Expr.u32OfNat, Expr.u32Beq,
      Comp.sampleBool, Comp.sampleBytes32, Comp.sampleRandom64, Comp.sampleDrKey96,
      Comp.sampleIndex, Comp.queryPrim, encEC, encKEM,
      Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
    dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
      _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
    have hb0 : bits 0 = 1 := by decide
    have hb1 : bits 1 = 1 := by decide
    have hb32 : bits 32 = 6 := by decide
    have hb64 : bits 64 = 7 := by decide
    have hb96 : bits 96 = 7 := by decide
    have hb128 : bits 128 = 8 := by decide
    have hb160 : bits 160 = 8 := by decide
    have hb192 : bits 192 = 8 := by decide
    have hmdh : bits (min K S.N_dh) ≤ bits K := ah_bits_mono (Nat.min_le_left _ _)
    have hmsess : bits (min K S.N_sess_tot) ≤ bits K := ah_bits_mono (Nat.min_le_left _ _)
    omega
  unfold TwoStageCostedReduction.size
  omega

end ClampedShCrSize

section AuthPrfCpaSizeBounds


open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.Security
open _root_.SignalPqxdh.LegacyCosted
open _root_.SignalPqxdh.Security.ReductionDsl
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead
open Computational.Proofs.SignalPqxdh.AtomicLift (pqOpLitSize exprLitSize compLitSize red1LitSize red2LitSize)

set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem hl_F_X25519_length : _root_.SignalPqxdh.F_X25519.length = 32 := by decide


set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
@[simp] private theorem ap_liftPrimComp_size {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (liftPrimComp (C := C) c).size = c.size := by
  induction c <;> simp_all [liftPrimComp, Comp.size, pqChalIface, pqPrimIface]

set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
@[simp] private theorem ap_liftPrimComp_mk_size {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    Comp.size (I := pqPrfMkIface) (liftPrimComp c) = c.size := ap_liftPrimComp_size c

set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem ap_bits_mono {x y : ℕ} (h : x ≤ y) : bits x ≤ bits y := by
  unfold bits
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
@[simp] private theorem ap_recvFinishTagRunC_size (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (tag : Var Γ₁ recvFinishTagTy) (res? : Expr pqxdhOps Δ recvFinishResTy) {inst : Ext Γ₁ Δ} :
    (@recvFinishTagRunC S K Γ₁ Δ tag res? inst).size =
      res?.size + bits K + 4 * bits (min K S.N_dh) + 1864 := by
  simp only [recvFinishTagRunC, findHonestC, matchSentOPKC, matchSentNoOPKC,
    natEq, nat2Eq, nat3Eq, oeMk, oeUpd, roMk, rnoMk, stMk, stUpd, ahsMk, ahsUpd,
    aNone, aRecvHonest, aRecvUnfresh, peIkAPk, peCorrupted,
    sbSpkPk, sbPqspkPk, oeOpkSk, oeOpkPk, hdrIkAPk, hdrEkAPk, hdrKemCt,
    pkmHdr, soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched, snoA0, snoB0,
    snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched, roBCorr, roA0, roB0, roSb, roOb,
    roA1, roPk1, roCt, roM, rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM, asSecb,
    asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions, asUsedSendSessions,
    asUsedRecvOPK, asUsedRecvNoOPK, asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents,
    asRecvdNoOPKEvents, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    boolOr, Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, consumeFirstMV, eMap,
    bytesBeq, queryPrim, Comp.size, Expr.size]
  dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
    _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
@[simp] private theorem ap_prepareAuthHybridRecvC_true_size (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (x : Var Γ₂ recvQTy) {inst₁ : Ext Γ₁ Δ} {inst₂ : Ext Γ₂ Δ} :
    (@prepareAuthHybridRecvC S K Γ₁ Γ₂ Δ true hst x inst₁ inst₂ :
      Comp pqxdhOps pqPrimIface Δ (.opt preparedAuthRecvTy)).size =
      6 * bits K + 3 * bits (min K S.N_dh) + 875 := by
  simp only [prepareAuthHybridRecvC, koskSenderOkC, findHonestC, isAdvRegC,
    matchIdealAuthHandshakeC, natEq, nat2Eq, nat3Eq, optU32Eq, kyberCheckE, buildSecretsE,
    kyberEq, isSomeE, eLet2, boolOr, rkrMk,
    ahsMk, ahsUpd, peSecIKA0, peIkAPk, peCorrupted, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk,
    oeOpkSk, oeOpkPk, oeConsumed, hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
    pkmHdr, pkmEphAPk, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk,
    iasPeerPqspkPk, iasKemCt, iasEphAPk, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries,
    asUsedRecvOPK, asUsedKyberTriples, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs,
    ahsIdealSessions,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, findMV,
    eLet, eFind, eAny, eCaseOpt,
    litB, catB, bytesCons, widenB, takeKB, bytesLen, bytesBeq, u32OfNat, u32Beq,
    queryPrim, encEC, encKEM, Comp.size, Expr.size, ↓reduceIte]
  dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
    _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  have hb32 : bits 32 = 6 := by decide
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
@[simp] private theorem ap_prepareAuthHybridRecvC_false_size (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (x : Var Γ₂ recvQTy) {inst₁ : Ext Γ₁ Δ} {inst₂ : Ext Γ₂ Δ} :
    (@prepareAuthHybridRecvC S K Γ₁ Γ₂ Δ false hst x inst₁ inst₂ :
      Comp pqxdhOps pqPrimIface Δ (.opt preparedAuthRecvTy)).size =
      5 * bits K + 3 * bits (min K S.N_dh) + 813 := by
  simp only [prepareAuthHybridRecvC, koskSenderOkC, findHonestC, isAdvRegC,
    matchIdealAuthHandshakeC, natEq, nat2Eq, nat3Eq, optU32Eq, kyberCheckE, buildSecretsE,
    kyberEq, isSomeE, eLet2, boolOr, rkrMk,
    ahsMk, ahsUpd, peSecIKA0, peIkAPk, peCorrupted, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk,
    hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt, pkmHdr, pkmEphAPk,
    iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk, iasKemCt,
    iasEphAPk, asHasWonAuth, asPrincipals, asSpkBundles, asUsedRecvNoOPK,
    asUsedKyberTriples, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, findMV,
    eLet, eFind, eAny, eCaseOpt,
    litB, catB, bytesCons, widenB, takeKB, bytesLen, bytesBeq, u32OfNat, u32Beq,
    queryPrim, encEC, encKEM, Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true]
  dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
    _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  have hb32 : bits 32 = 6 := by decide
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
@[simp] private theorem ap_finishAuthHybridSendC_size (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (args : Expr pqxdhOps Δ finishSendArgsTy) {inst : Ext Γ₁ Δ} :
    (@finishAuthHybridSendC S K Γ₁ Δ hst args inst).size =
      args.size + 4 * bits (min K S.N_dh) + 2 * bits K + 1040 := by
  simp only [finishAuthHybridSendC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
    findHonestC, natEq, isSomeE, boolOr,
    optFst, optSnd, hdMk, pmMk, seMk, iasMk, soMk, snoMk, ikrMk, stMk, stUpd, ahsMk, ahsUpd,
    aSendFresh, aSendUnfresh, peIkAPk, peCorrupted, sbSpkPk, sbPqspkPk, oeOpkPk, pkbIkB, pkbSpkId,
    pkbSpkB, pkbOpkB?, pkbPqspkId, pkbPqspkB, asSecb, asHasWonAuth, asPrincipals, asSpkBundles,
    asOpkEntries, asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK,
    asUsedKyberTriples, asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, findMV, anyMV,
    eCaseOpt, eAny, bytesBeq, queryPrim, Comp.size, Expr.size]
  dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
    _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
@[simp] private theorem ap_finalizeAuthFixedDsl_size (S : Setup) (K : Nat) {Γ : List PT} :
    (finalizeAuthFixedDsl S K (Γ := Γ)).size =
      4 * bits (min K S.N_dh) + 5 * bits (4 * min K S.N_dh) + 7 * bits K + 292 := by
  simp only [finalizeAuthFixedDsl, finalizeAuthFixedBodyDsl, allHonestEcPksAuthDsl,
    allHonestEcPksAuthDslK,
    hasDuplicateBytesDsl, hasBadSigAuthDsl, hasKemPkCollisionAuthDsl,
    hasBadKemShCrRecordsDsl, notAllChallengedCleanDsl,
    asHasWonAuth, asSessions, asSpkBundles, asPrincipals, asOpkEntries,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs,
    aseFresh, aseSpkHonest, asePqspkHonest, aseChallenged, aseEkASk,
    peIkAPk, sbSpkPk, sbPqspkPk, oeOpkPk,
    rkrKemSs, ikrKemSs, rkrKemCt, ikrKemCt, ikrPqspkPk, rkrPqspkPk,
    boolOr, boolBeq,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
    eLet, eAny, eMap, bytesBeq, samplePrim, queryPrim, Comp.size, Expr.size]
  dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
    _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  omega

@[irreducible] private def opaqueSize {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {t : PT} (c : Comp pqxdhOps I Γ t) : Nat :=
  c.size

private def sizeClamp {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {t : PT} (c : Comp pqxdhOps I Γ t) (b : Nat) : Nat :=
  min (opaqueSize c) b

set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
@[congr] private theorem sizeClamp_congr {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {t : PT} (c : Comp pqxdhOps I Γ t) {b₁ b₂ : Nat} (hb : b₁ = b₂) :
    sizeClamp c b₁ = sizeClamp c b₂ := hb ▸ rfl

set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem eq_sizeClamp_of_le {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {t : PT} {c : Comp pqxdhOps I Γ t} {b : Nat} (h : c.size ≤ b) :
    c.size = sizeClamp c b := by
  unfold sizeClamp opaqueSize
  exact (Nat.min_eq_left h).symm

set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem sizeClamp_eq_imp_le {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {t : PT} {c : Comp pqxdhOps I Γ t} {b sc : Nat}
    (h : sizeClamp c b = sc) : sc ≤ b :=
  h ▸ Nat.min_le_right _ _

private def clampLe (n b : Nat) : Nat := min n b

set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
@[congr] private theorem clampLe_congr (n : Nat) {b₁ b₂ : Nat} (hb : b₁ = b₂) :
    clampLe n b₁ = clampLe n b₂ := hb ▸ rfl

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem ap_authCkSendB_size_le (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT} (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    {inst₁ : Ext Γ₁ Δ} {inst₂ : Ext Γ₂ Δ} {inst₃ : Ext Γ₃ Δ} {inst₄ : Ext Γ₄ Δ} :
    (@authCkSendB S K Γ₁ Γ₂ Γ₃ Γ₄ Δ opk idx chalP fhst x inst₁ inst₂ inst₃ inst₄).size ≤
      35 * bits K + 6000 := by
  cases opk <;> {
    simp only [authCkSendB, sampCkPairC, sampAtCkC,
      ap_finishAuthHybridSendC_size,
      findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
      resolveSigPkC, hkdfRoC, rootRoC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
      parKEntry, parSecrets, parDhRatchet, parIsUncorrSender,
      parMatchedSess?, parSameEph, parHstDec, parFinishTag, fhstSetBase,
      peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
      sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, oeOpkSk, oeOpkPk, oeConsumed,
      pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkId, pkbPqspkB, pkbPqspkSig,
      hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
      pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
      soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched,
      snoA0, snoB0, snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched,
      roBCorr, roA0, roB0, roSb, roOb, roA1, roPk1, roCt, roM,
      rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM,
      aseSpkHonest, asePqspkHonest, aseEkASk, aseFresh, aseChallenged,
      ikrPqspkPk, ikrKemCt, ikrKemSs, rkrPqspkPk, rkrKemCt, rkrKemSs,
      iasSid, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk,
      iasKemCt, iasEphAPk, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys,
      asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
      asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
      asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
      asAdvKeys, asRoCache, asRootRoCache,
      ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
      ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
      assNext, assSendOpk, assSendNoOpk, assRecv, assMk, emptyAuthSlotStE,
      lookupSendSlotE, lookupSendSlotOrZeroE, allocSendSlotE,
      lookupRecvSlotE, lookupRecvSlotOrZeroE, allocRecvSlotE,
      ahsfMkSlots, ahsfUpdSlots,
      natEq, natLt, nat2Eq, nat3Eq, bytes2Eq, optU32Eq, sidEq, saltBytesE, sameSaltKeyE, kyberEq,
      isSomeE, optFst, optSnd, firstMsgADE, buildSecretsE, kyberCheckE, sessionSlotIndexE,
      peMk, peUpd, sbMk, oeMk, oeUpd, buMk, hdMk, pmMk, seMk, iasMk, soMk, snoMk, roMk, rnoMk,
      ikrMk, rkrMk, stMk, stUpd, ahsMk, ahsUpd, ahsfMk, ahsfUpd,
      aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
      aDrKey, aRootKdf, sendGuardE, boolOr, boolBeq, eLet2,
      Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
      Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
      Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
      Comp.foldBoundedM,
      v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
      caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
      eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
      litB, catB, bytesCons, widenB, takeKB,
      bytesLen, bytesBeq, bytesVarint, u32OfNat, u32Beq,
      samplePrim, queryPrim, encEC, encKEM,
      Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
    dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
      _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
    have hb0 : bits 0 = 1 := by decide
    have hb1 : bits 1 = 1 := by decide
    have hb32 : bits 32 = 6 := by decide
    have hb64 : bits 64 = 7 := by decide
    have hb96 : bits 96 = 7 := by decide
    have hb128 : bits 128 = 8 := by decide
    have hb160 : bits 160 = 8 := by decide
    have hb192 : bits 192 = 8 := by decide
    have hmdh : bits (min K S.N_dh) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
    have hmsess : bits (min K S.N_sess_tot) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
    omega
  }

set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem ap_authCkSendB_size_clamp (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT} (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    {inst₁ : Ext Γ₁ Δ} {inst₂ : Ext Γ₂ Δ} {inst₃ : Ext Γ₃ Δ} {inst₄ : Ext Γ₄ Δ} :
    (@authCkSendB S K Γ₁ Γ₂ Γ₃ Γ₄ Δ opk idx chalP fhst x inst₁ inst₂ inst₃ inst₄).size =
      sizeClamp (@authCkSendB S K Γ₁ Γ₂ Γ₃ Γ₄ Δ opk idx chalP fhst x inst₁ inst₂ inst₃ inst₄)
        (35 * bits K + 6000) :=
  eq_sizeClamp_of_le (ap_authCkSendB_size_le S K opk idx chalP fhst x)

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem ap_authCkRecvB_size_le (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT} (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ recvQTy)
    {inst₁ : Ext Γ₁ Δ} {inst₂ : Ext Γ₂ Δ} {inst₃ : Ext Γ₃ Δ} {inst₄ : Ext Γ₄ Δ} :
    (@authCkRecvB S K Γ₁ Γ₂ Γ₃ Γ₄ Δ opk idx chalP fhst x inst₁ inst₂ inst₃ inst₄).size ≤
      60 * bits K + 18000 := by
  cases opk <;> {
    simp only [authCkRecvB, finishAuthRecvCkC, sampCkPairC, sampAtCkC,
      ap_prepareAuthHybridRecvC_true_size, ap_prepareAuthHybridRecvC_false_size, ap_recvFinishTagRunC_size,
      findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
      resolveSigPkC, hkdfRoC, rootRoC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
      parKEntry, parSecrets, parDhRatchet, parIsUncorrSender,
      parMatchedSess?, parSameEph, parHstDec, parFinishTag, fhstSetBase,
      peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
      sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, oeOpkSk, oeOpkPk, oeConsumed,
      pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkId, pkbPqspkB, pkbPqspkSig,
      hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
      pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
      soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched,
      snoA0, snoB0, snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched,
      roBCorr, roA0, roB0, roSb, roOb, roA1, roPk1, roCt, roM,
      rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM,
      aseSpkHonest, asePqspkHonest, aseEkASk, aseFresh, aseChallenged,
      ikrPqspkPk, ikrKemCt, ikrKemSs, rkrPqspkPk, rkrKemCt, rkrKemSs,
      iasSid, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk,
      iasKemCt, iasEphAPk, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys,
      asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
      asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
      asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
      asAdvKeys, asRoCache, asRootRoCache,
      ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
      ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
      assNext, assSendOpk, assSendNoOpk, assRecv, assMk, emptyAuthSlotStE,
      lookupSendSlotE, lookupSendSlotOrZeroE, allocSendSlotE,
      lookupRecvSlotE, lookupRecvSlotOrZeroE, allocRecvSlotE,
      ahsfMkSlots, ahsfUpdSlots,
      natEq, natLt, nat2Eq, nat3Eq, bytes2Eq, optU32Eq, sidEq, saltBytesE, sameSaltKeyE, kyberEq,
      isSomeE, optFst, optSnd, firstMsgADE, buildSecretsE, kyberCheckE, sessionSlotIndexE,
      peMk, peUpd, sbMk, oeMk, oeUpd, buMk, hdMk, pmMk, seMk, iasMk, soMk, snoMk, roMk, rnoMk,
      ikrMk, rkrMk, stMk, stUpd, ahsMk, ahsUpd, ahsfMk, ahsfUpd,
      aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
      aDrKey, aRootKdf, sendGuardE, boolOr, boolBeq, eLet2,
      Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
      Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
      Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
      Comp.foldBoundedM,
      v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
      caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
      eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
      litB, catB, bytesCons, widenB, takeKB,
      bytesLen, bytesBeq, bytesVarint, u32OfNat, u32Beq,
      samplePrim, queryPrim, encEC, encKEM,
      Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
    dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
      _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
    have hb0 : bits 0 = 1 := by decide
    have hb1 : bits 1 = 1 := by decide
    have hb32 : bits 32 = 6 := by decide
    have hb64 : bits 64 = 7 := by decide
    have hb96 : bits 96 = 7 := by decide
    have hb128 : bits 128 = 8 := by decide
    have hb160 : bits 160 = 8 := by decide
    have hb192 : bits 192 = 8 := by decide
    have hmdh : bits (min K S.N_dh) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
    have hmsess : bits (min K S.N_sess_tot) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
    omega
  }

set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem ap_authCkRecvB_size_clamp (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT} (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ recvQTy)
    {inst₁ : Ext Γ₁ Δ} {inst₂ : Ext Γ₂ Δ} {inst₃ : Ext Γ₃ Δ} {inst₄ : Ext Γ₄ Δ} :
    (@authCkRecvB S K Γ₁ Γ₂ Γ₃ Γ₄ Δ opk idx chalP fhst x inst₁ inst₂ inst₃ inst₄).size =
      sizeClamp (@authCkRecvB S K Γ₁ Γ₂ Γ₃ Γ₄ Δ opk idx chalP fhst x inst₁ inst₂ inst₃ inst₄)
        (60 * bits K + 18000) :=
  eq_sizeClamp_of_le (ap_authCkRecvB_size_le S K opk idx chalP fhst x)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 800000 in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem ap_prfCkRedProg_size_le_clamped (S : Setup) (K : Nat) :
    (prfCkRedProg S K).size ≤ 235 * bits K + 60000 := by
  dsimp only [prfCkRedProg, CostedReduction.size]
  simp only [
    prfCkInitDsl, prfCkInitDslK, prfCkHandleDsl, prfCkFinishDsl,
    ckSecb, ckIdx, ckChal, ckFhst,
    sampCkPairC, authCkStepC,
    sizeClamp_congr,
    ap_authCkSendB_size_clamp, ap_authCkRecvB_size_clamp, ap_finalizeAuthFixedDsl_size,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, hkdfRoC, rootRoC, fhstSetBase,
    initPrinFixedB, corruptFixedB, genSpkFixedB, genOpkFixedB, roFixedB, roRootFixedB,
    registerFixedB,
    pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkId, pkbPqspkB, pkbPqspkSig,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
    sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, oeOpkSk, oeOpkPk, oeConsumed,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asAdvKeys, asRoCache, asRootRoCache,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    assNext, assSendOpk, assSendNoOpk, assRecv, assMk, emptyAuthSlotStE,
    ahsfMkSlots, ahsfUpdSlots,
    natEq, natLt, nat2Eq, nat3Eq, bytes2Eq, optU32Eq, sidEq,
    isSomeE, optFst, optSnd,
    peMk, peUpd, sbMk, oeMk, oeUpd, buMk, stMk, stUpd, ahsMk, ahsUpd, ahsfMk, ahsfUpd,
    emptyAuthStE, emptyAuthHybridStE, emptyAuthHybridStFixedE,
    aNone, aInitPrin, aPk, aCorr, aBundle, aDrKey, aRootKdf, boolOr, boolBeq, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    litB, catB, bytesCons, widenB, takeKB,
    bytesLen, bytesBeq, bytesVarint, u32OfNat, u32Beq,
    samplePrim, queryPrim, encEC, encKEM,
    Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
  dsimp only [clampLe, _root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
    _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  repeat (
    generalize h_sc_eq : sizeClamp _ _ = sc
    fail_if_success (clear h_sc_eq; clear sc)
    have _ := sizeClamp_eq_imp_le h_sc_eq
    clear h_sc_eq)
  have b4Dh : bits (4 * min K S.N_dh) ≤ bits K + 3 := by
    have h := _root_.ReductionDsl.bits_mul 4 (min K S.N_dh)
    have h1 : bits (min K S.N_dh) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
    have : bits 4 = 3 := by decide
    omega
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb32 : bits 32 = 6 := by decide
  have hb64 : bits 64 = 7 := by decide
  have hb96 : bits 96 = 7 := by decide
  have hb128 : bits 128 = 8 := by decide
  have hb160 : bits 160 = 8 := by decide
  have hb192 : bits 192 = 8 := by decide
  have hmdh : bits (min K S.N_dh) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
  have hmsess : bits (min K S.N_sess_tot) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem ap_authMkSendPreB_size_le (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Δ : List PT} (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ sendQTy)
    {inst₁ : Ext Γ₁ Δ} {inst₂ : Ext Γ₂ Δ} :
    (@authMkSendPreB S K Γ₁ Γ₂ Δ opk core x inst₁ inst₂).size ≤ 50 * bits K + 8000 := by
  cases opk <;> {
    simp only [authMkSendPreB, finishAuthSendMkC, mkcSecb, mkcIdx, mkcSentChal, mkcFhst, mkcMk,
      ap_finishAuthHybridSendC_size,
      findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
      resolveSigPkC, hkdfRoC, rootRoC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
      parKEntry, parSecrets, parDhRatchet, parIsUncorrSender,
      parMatchedSess?, parSameEph, parHstDec, parFinishTag, fhstSetBase,
      peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
      sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, oeOpkSk, oeOpkPk, oeConsumed,
      pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkId, pkbPqspkB, pkbPqspkSig,
      hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
      pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
      soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched,
      snoA0, snoB0, snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched,
      roBCorr, roA0, roB0, roSb, roOb, roA1, roPk1, roCt, roM,
      rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM,
      aseSpkHonest, asePqspkHonest, aseEkASk, aseFresh, aseChallenged,
      ikrPqspkPk, ikrKemCt, ikrKemSs, rkrPqspkPk, rkrKemCt, rkrKemSs,
      iasSid, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk,
      iasKemCt, iasEphAPk, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys,
      asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
      asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
      asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
      asAdvKeys, asRoCache, asRootRoCache,
      ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
      ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
      assNext, assSendOpk, assSendNoOpk, assRecv, assMk, emptyAuthSlotStE,
      lookupSendSlotE, lookupSendSlotOrZeroE, allocSendSlotE,
      lookupRecvSlotE, lookupRecvSlotOrZeroE, allocRecvSlotE,
      ahsfMkSlots, ahsfUpdSlots,
      natEq, natLt, nat2Eq, nat3Eq, bytes2Eq, optU32Eq, sidEq, saltBytesE, sameSaltKeyE, kyberEq,
      isSomeE, optFst, optSnd, firstMsgADE, buildSecretsE, kyberCheckE, sessionSlotIndexE,
      peMk, peUpd, sbMk, oeMk, oeUpd, buMk, hdMk, pmMk, seMk, iasMk, soMk, snoMk, roMk, rnoMk,
      ikrMk, rkrMk, stMk, stUpd, ahsMk, ahsUpd, ahsfMk, ahsfUpd,
      aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
      aDrKey, aRootKdf, sendGuardE, boolOr, boolBeq, eLet2,
      Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
      Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
      Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
      Comp.foldBoundedM,
      v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
      caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
      eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
      litB, catB, bytesCons, widenB, takeKB,
      bytesLen, bytesBeq, bytesVarint, u32OfNat, u32Beq,
      samplePrim, queryPrim, encEC, encKEM,
      Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
    dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
      _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
    have hb0 : bits 0 = 1 := by decide
    have hb1 : bits 1 = 1 := by decide
    have hb32 : bits 32 = 6 := by decide
    have hb64 : bits 64 = 7 := by decide
    have hb96 : bits 96 = 7 := by decide
    have hb128 : bits 128 = 8 := by decide
    have hb160 : bits 160 = 8 := by decide
    have hb192 : bits 192 = 8 := by decide
    have hmdh : bits (min K S.N_dh) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
    have hmsess : bits (min K S.N_sess_tot) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
    omega
  }

set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem ap_authMkSendPreB_size_clamp (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Δ : List PT} (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ sendQTy)
    {inst₁ : Ext Γ₁ Δ} {inst₂ : Ext Γ₂ Δ} :
    (@authMkSendPreB S K Γ₁ Γ₂ Δ opk core x inst₁ inst₂).size =
      sizeClamp (@authMkSendPreB S K Γ₁ Γ₂ Δ opk core x inst₁ inst₂) (50 * bits K + 8000) :=
  eq_sizeClamp_of_le (ap_authMkSendPreB_size_le S K opk core x)

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem ap_authMkRecvPreB_size_le (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Δ : List PT} (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ recvQTy)
    {inst₁ : Ext Γ₁ Δ} {inst₂ : Ext Γ₂ Δ} :
    (@authMkRecvPreB S K Γ₁ Γ₂ Δ opk core x inst₁ inst₂).size ≤ 98 * bits K + 38000 := by
  cases opk <;> {
    simp only [authMkRecvPreB, finishAuthRecvMkC, finishRecvUnmatchedMkPreC,
      mkcSecb, mkcIdx, mkcSentChal, mkcFhst, mkcMk,
      ap_prepareAuthHybridRecvC_true_size, ap_prepareAuthHybridRecvC_false_size, ap_recvFinishTagRunC_size,
      findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
      resolveSigPkC, hkdfRoC, rootRoC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
      parKEntry, parSecrets, parDhRatchet, parIsUncorrSender,
      parMatchedSess?, parSameEph, parHstDec, parFinishTag, fhstSetBase,
      peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
      sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, oeOpkSk, oeOpkPk, oeConsumed,
      pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkId, pkbPqspkB, pkbPqspkSig,
      hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
      pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
      soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched,
      snoA0, snoB0, snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched,
      roBCorr, roA0, roB0, roSb, roOb, roA1, roPk1, roCt, roM,
      rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM,
      aseSpkHonest, asePqspkHonest, aseEkASk, aseFresh, aseChallenged,
      ikrPqspkPk, ikrKemCt, ikrKemSs, rkrPqspkPk, rkrKemCt, rkrKemSs,
      iasSid, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk,
      iasKemCt, iasEphAPk, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys,
      asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
      asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
      asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
      asAdvKeys, asRoCache, asRootRoCache,
      ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
      ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
      assNext, assSendOpk, assSendNoOpk, assRecv, assMk, emptyAuthSlotStE,
      lookupSendSlotE, lookupSendSlotOrZeroE, allocSendSlotE,
      lookupRecvSlotE, lookupRecvSlotOrZeroE, allocRecvSlotE,
      ahsfMkSlots, ahsfUpdSlots,
      natEq, natLt, nat2Eq, nat3Eq, bytes2Eq, optU32Eq, sidEq, saltBytesE, sameSaltKeyE, kyberEq,
      isSomeE, optFst, optSnd, firstMsgADE, buildSecretsE, kyberCheckE, sessionSlotIndexE,
      peMk, peUpd, sbMk, oeMk, oeUpd, buMk, hdMk, pmMk, seMk, iasMk, soMk, snoMk, roMk, rnoMk,
      ikrMk, rkrMk, stMk, stUpd, ahsMk, ahsUpd, ahsfMk, ahsfUpd,
      aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
      aDrKey, aRootKdf, sendGuardE, boolOr, boolBeq, eLet2,
      Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
      Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
      Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
      Comp.foldBoundedM,
      v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
      caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
      eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
      litB, catB, bytesCons, widenB, takeKB,
      bytesLen, bytesBeq, bytesVarint, u32OfNat, u32Beq,
      samplePrim, queryPrim, encEC, encKEM,
      Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
    dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
      _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
    have hb0 : bits 0 = 1 := by decide
    have hb1 : bits 1 = 1 := by decide
    have hb32 : bits 32 = 6 := by decide
    have hb64 : bits 64 = 7 := by decide
    have hb96 : bits 96 = 7 := by decide
    have hb128 : bits 128 = 8 := by decide
    have hb160 : bits 160 = 8 := by decide
    have hb192 : bits 192 = 8 := by decide
    have hmdh : bits (min K S.N_dh) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
    have hmsess : bits (min K S.N_sess_tot) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
    omega
  }

set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem ap_authMkRecvPreB_size_clamp (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Δ : List PT} (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ recvQTy)
    {inst₁ : Ext Γ₁ Δ} {inst₂ : Ext Γ₂ Δ} :
    (@authMkRecvPreB S K Γ₁ Γ₂ Δ opk core x inst₁ inst₂).size =
      sizeClamp (@authMkRecvPreB S K Γ₁ Γ₂ Δ opk core x inst₁ inst₂) (98 * bits K + 38000) :=
  eq_sizeClamp_of_le (ap_authMkRecvPreB_size_le S K opk core x)

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem ap_prfMkStepPostC_size_le (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List PT} (cont : Var Γ₁ prfMkChalContTy) (mk : Var Γ₂ AuthPrf.msgKeysTy)
    {inst₁ : Ext Γ₁ Δ} {inst₂ : Ext Γ₂ Δ} :
    (@prfMkStepPostC S K Γ₁ Γ₂ Δ cont mk inst₁ inst₂).size ≤ 65 * bits K + 12000 := by
  simp only [prfMkStepPostC, finishAuthSendMkC, finishAuthRecvMkC,
    mkcSecb, mkcIdx, mkcSentChal, mkcFhst, mkcMk,
    ap_finishAuthHybridSendC_size, ap_recvFinishTagRunC_size,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, hkdfRoC, rootRoC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
    parKEntry, parSecrets, parDhRatchet, parIsUncorrSender,
    parMatchedSess?, parSameEph, parHstDec, parFinishTag, fhstSetBase,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
    sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, oeOpkSk, oeOpkPk, oeConsumed,
    pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkId, pkbPqspkB, pkbPqspkSig,
    hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
    pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
    soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched,
    snoA0, snoB0, snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched,
    roBCorr, roA0, roB0, roSb, roOb, roA1, roPk1, roCt, roM,
    rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM,
    aseSpkHonest, asePqspkHonest, aseEkASk, aseFresh, aseChallenged,
    ikrPqspkPk, ikrKemCt, ikrKemSs, rkrPqspkPk, rkrKemCt, rkrKemSs,
    iasSid, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk,
    iasKemCt, iasEphAPk, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asAdvKeys, asRoCache, asRootRoCache,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    assNext, assSendOpk, assSendNoOpk, assRecv, assMk, emptyAuthSlotStE,
    lookupSendSlotE, lookupSendSlotOrZeroE, allocSendSlotE,
    lookupRecvSlotE, lookupRecvSlotOrZeroE, allocRecvSlotE,
    ahsfMkSlots, ahsfUpdSlots,
    natEq, natLt, nat2Eq, nat3Eq, bytes2Eq, optU32Eq, sidEq, saltBytesE, sameSaltKeyE, kyberEq,
    isSomeE, optFst, optSnd, firstMsgADE, buildSecretsE, kyberCheckE, sessionSlotIndexE,
    peMk, peUpd, sbMk, oeMk, oeUpd, buMk, hdMk, pmMk, seMk, iasMk, soMk, snoMk, roMk, rnoMk,
    ikrMk, rkrMk, stMk, stUpd, ahsMk, ahsUpd, ahsfMk, ahsfUpd,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, sendGuardE, boolOr, boolBeq, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    litB, catB, bytesCons, widenB, takeKB,
    bytesLen, bytesBeq, bytesVarint, u32OfNat, u32Beq,
    samplePrim, queryPrim, encEC, encKEM,
    Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
  dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
    _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb32 : bits 32 = 6 := by decide
  have hb64 : bits 64 = 7 := by decide
  have hb96 : bits 96 = 7 := by decide
  have hb128 : bits 128 = 8 := by decide
  have hb160 : bits 160 = 8 := by decide
  have hb192 : bits 192 = 8 := by decide
  have hmdh : bits (min K S.N_dh) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
  have hmsess : bits (min K S.N_sess_tot) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
  omega

set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem ap_prfMkStepPostC_size_clamp (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List PT} (cont : Var Γ₁ prfMkChalContTy) (mk : Var Γ₂ AuthPrf.msgKeysTy)
    {inst₁ : Ext Γ₁ Δ} {inst₂ : Ext Γ₂ Δ} :
    (@prfMkStepPostC S K Γ₁ Γ₂ Δ cont mk inst₁ inst₂).size =
      sizeClamp (@prfMkStepPostC S K Γ₁ Γ₂ Δ cont mk inst₁ inst₂) (65 * bits K + 12000) :=
  eq_sizeClamp_of_le (ap_prfMkStepPostC_size_le S K cont mk)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 800000 in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem ap_prfMsgKeysRedProg_size_le_clamped (S : Setup) (K : Nat) :
    (prfMsgKeysRedProg S K).size ≤ 405 * bits K + 150000 := by
  dsimp only [prfMsgKeysRedProg, CostedReduction.size, prfMsgKeysHandleDsl]
  simp only [bindV, letV, caseSumV, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC,
    Comp.iteC, Comp.caseSumC, Comp.size, ap_liftPrimComp_mk_size]
  simp only [
    prfMsgKeysInitDsl, prfMsgKeysInitDslK, prfMsgKeysFinishDsl,
    mkcSecb, mkcIdx, mkcSentChal, mkcFhst, mkcMk,
    wrapMkBase, prfMkStepPreC,
    sizeClamp_congr,
    ap_authMkSendPreB_size_clamp, ap_authMkRecvPreB_size_clamp,
    ap_prfMkStepPostC_size_clamp, ap_finalizeAuthFixedDsl_size,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, hkdfRoC, rootRoC, fhstSetBase,
    initPrinFixedB, corruptFixedB, genSpkFixedB, genOpkFixedB, roFixedB, roRootFixedB,
    registerFixedB,
    pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkId, pkbPqspkB, pkbPqspkSig,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
    sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, oeOpkSk, oeOpkPk, oeConsumed,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asAdvKeys, asRoCache, asRootRoCache,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    assNext, assSendOpk, assSendNoOpk, assRecv, assMk, emptyAuthSlotStE,
    ahsfMkSlots, ahsfUpdSlots,
    natEq, natLt, nat2Eq, nat3Eq, bytes2Eq, optU32Eq, sidEq,
    isSomeE, optFst, optSnd,
    peMk, peUpd, sbMk, oeMk, oeUpd, buMk, stMk, stUpd, ahsMk, ahsUpd, ahsfMk, ahsfUpd,
    emptyAuthStE, emptyAuthHybridStE, emptyAuthHybridStFixedE,
    aNone, aInitPrin, aPk, aCorr, aBundle, aDrKey, aRootKdf, boolOr, boolBeq, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM,
    ap_liftPrimComp_size, ap_liftPrimComp_mk_size,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    litB, catB, bytesCons, widenB, takeKB,
    bytesLen, bytesBeq, bytesVarint, u32OfNat, u32Beq,
    samplePrim, sampleChal, queryPrim, queryDeriveMk,
    encEC, encKEM,
    Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
  dsimp only [clampLe, _root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
    _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  repeat (
    generalize h_sc_eq : sizeClamp _ _ = sc
    fail_if_success (clear h_sc_eq; clear sc)
    have _ := sizeClamp_eq_imp_le h_sc_eq
    clear h_sc_eq)
  have b4Dh : bits (4 * min K S.N_dh) ≤ bits K + 3 := by
    have h := _root_.ReductionDsl.bits_mul 4 (min K S.N_dh)
    have h1 : bits (min K S.N_dh) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
    have : bits 4 = 3 := by decide
    omega
  have bRecvK : bits (min K S.N_recv_tot + 1) ≤ bits K + 2 := by
    rcases Nat.eq_zero_or_pos K with rfl | hpos
    · simp
    · have hle : min K S.N_recv_tot + 1 ≤ 2 * K := by
        have := Nat.min_le_left K S.N_recv_tot; omega
      have h1 := ap_bits_mono hle
      have hm := _root_.ReductionDsl.bits_mul 2 K
      have hb2 : bits 2 = 2 := by decide
      omega
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb32 : bits 32 = 6 := by decide
  have hb64 : bits 64 = 7 := by decide
  have hb96 : bits 96 = 7 := by decide
  have hb128 : bits 128 = 8 := by decide
  have hb160 : bits 160 = 8 := by decide
  have hb192 : bits 192 = 8 := by decide
  have hmdh : bits (min K S.N_dh) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
  have hmsess : bits (min K S.N_sess_tot) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem ap_cpaSendSlotB_size_le (S : Setup) (K : Nat) (opk allowPause : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT} (idx : Var Γ₁ .nat) (ns : Var Γ₂ .nat)
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    {inst₁ : Ext Γ₁ Δ} {inst₂ : Ext Γ₂ Δ} {inst₃ : Ext Γ₃ Δ} {inst₄ : Ext Γ₄ Δ} :
    (@cpaSendSlotB S K Γ₁ Γ₂ Γ₃ Γ₄ Δ opk allowPause idx ns fhst x inst₁ inst₂ inst₃ inst₄).size ≤
      35 * bits K + 6000 := by
  cases opk <;> cases allowPause <;> {
    simp only [cpaSendSlotB, cpaSendB, finishCpaC, spkHonIdealFromPeerC,
      getDBytes, defaultMsgKeysE, iasAdE, iasAeadCtE, iasMsgPlainE, iasCk1_0E,
      ap_finishAuthHybridSendC_size,
      findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
      resolveSigPkC, hkdfRoC, rootRoC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
      parKEntry, parSecrets, parDhRatchet, parIsUncorrSender,
      parMatchedSess?, parSameEph, parHstDec, parFinishTag, fhstSetBase,
      peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
      sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, oeOpkSk, oeOpkPk, oeConsumed,
      pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkId, pkbPqspkB, pkbPqspkSig,
      hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
      pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
      soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched,
      snoA0, snoB0, snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched,
      roBCorr, roA0, roB0, roSb, roOb, roA1, roPk1, roCt, roM,
      rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM,
      aseSpkHonest, asePqspkHonest, aseEkASk, aseFresh, aseChallenged,
      ikrPqspkPk, ikrKemCt, ikrKemSs, rkrPqspkPk, rkrKemCt, rkrKemSs,
      iasSid, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk,
      iasKemCt, iasEphAPk, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys,
      asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
      asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
      asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
      asAdvKeys, asRoCache, asRootRoCache,
      ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
      ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
      assNext, assSendOpk, assSendNoOpk, assRecv, assMk, emptyAuthSlotStE,
      lookupSendSlotE, lookupSendSlotOrZeroE, allocSendSlotE,
      lookupRecvSlotE, lookupRecvSlotOrZeroE, allocRecvSlotE,
      ahsfMkSlots, ahsfUpdSlots,
      natEq, natLt, nat2Eq, nat3Eq, bytes2Eq, optU32Eq, sidEq, saltBytesE, sameSaltKeyE, kyberEq,
      isSomeE, optFst, optSnd, firstMsgADE, buildSecretsE, kyberCheckE, sessionSlotIndexE,
      peMk, peUpd, sbMk, oeMk, oeUpd, buMk, hdMk, pmMk, seMk, iasMk, soMk, snoMk, roMk, rnoMk,
      ikrMk, rkrMk, stMk, stUpd, ahsMk, ahsUpd, ahsfMk, ahsfUpd,
      aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
      aDrKey, aRootKdf, sendGuardE, boolOr, boolBeq, eLet2,
      Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
      Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
      Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
      Comp.foldBoundedM,
      v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
      caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
      eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
      litB, catB, bytesCons, widenB, takeKB,
      bytesLen, bytesBeq, bytesVarint, u32OfNat, u32Beq,
      samplePrim, queryPrim, encEC, encKEM,
      Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false, id_eq]
    dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
      _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
    have hb0 : bits 0 = 1 := by decide
    have hb1 : bits 1 = 1 := by decide
    have hb32 : bits 32 = 6 := by decide
    have hb64 : bits 64 = 7 := by decide
    have hb96 : bits 96 = 7 := by decide
    have hb128 : bits 128 = 8 := by decide
    have hb160 : bits 160 = 8 := by decide
    have hb192 : bits 192 = 8 := by decide
    have hmdh : bits (min K S.N_dh) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
    have hmsend : bits (min K S.N_send_tot) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
    have hmsess : bits (min K S.N_sess_tot) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
    omega
  }

set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem ap_cpaSendSlotB_size_clamp (S : Setup) (K : Nat) (opk allowPause : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT} (idx : Var Γ₁ .nat) (ns : Var Γ₂ .nat)
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    {inst₁ : Ext Γ₁ Δ} {inst₂ : Ext Γ₂ Δ} {inst₃ : Ext Γ₃ Δ} {inst₄ : Ext Γ₄ Δ} :
    (@cpaSendSlotB S K Γ₁ Γ₂ Γ₃ Γ₄ Δ opk allowPause idx ns fhst x inst₁ inst₂ inst₃ inst₄).size =
      sizeClamp (@cpaSendSlotB S K Γ₁ Γ₂ Γ₃ Γ₄ Δ opk allowPause idx ns fhst x inst₁ inst₂ inst₃ inst₄)
        (35 * bits K + 6000) :=
  eq_sizeClamp_of_le (ap_cpaSendSlotB_size_le S K opk allowPause idx ns fhst x)

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem ap_cpaRecvC_size_le (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Δ : List PT} (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy)
    {inst₁ : Ext Γ₁ Δ} {inst₂ : Ext Γ₂ Δ} :
    (@cpaRecvC S K Γ₁ Γ₂ Δ opk fhst x inst₁ inst₂).size ≤ 58 * bits K + 7000 := by
  cases opk <;> {
    simp only [cpaRecvC, spkHonIdealFromPeerC,
      getDBytes, defaultMsgKeysE, iasAdE, iasAeadCtE, iasMsgPlainE, iasCk1_0E,
      ap_prepareAuthHybridRecvC_true_size, ap_prepareAuthHybridRecvC_false_size, ap_recvFinishTagRunC_size,
      findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
      resolveSigPkC, hkdfRoC, rootRoC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
      matchSentOPKC, matchSentNoOPKC, matchIdealAuthHandshakeC,
      parKEntry, parSecrets, parDhRatchet, parIsUncorrSender,
      parMatchedSess?, parSameEph, parHstDec, parFinishTag, fhstSetBase,
      peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
      sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, oeOpkSk, oeOpkPk, oeConsumed,
      pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkId, pkbPqspkB, pkbPqspkSig,
      hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
      pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
      soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched,
      snoA0, snoB0, snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched,
      roBCorr, roA0, roB0, roSb, roOb, roA1, roPk1, roCt, roM,
      rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM,
      aseSpkHonest, asePqspkHonest, aseEkASk, aseFresh, aseChallenged,
      ikrPqspkPk, ikrKemCt, ikrKemSs, rkrPqspkPk, rkrKemCt, rkrKemSs,
      iasSid, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk,
      iasKemCt, iasEphAPk, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys,
      asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
      asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
      asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
      asAdvKeys, asRoCache, asRootRoCache,
      ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
      ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
      assNext, assSendOpk, assSendNoOpk, assRecv, assMk, emptyAuthSlotStE,
      lookupSendSlotE, lookupSendSlotOrZeroE, allocSendSlotE,
      lookupRecvSlotE, lookupRecvSlotOrZeroE, allocRecvSlotE,
      ahsfMkSlots, ahsfUpdSlots,
      natEq, natLt, nat2Eq, nat3Eq, bytes2Eq, optU32Eq, sidEq, saltBytesE, sameSaltKeyE, kyberEq,
      isSomeE, optFst, optSnd, firstMsgADE, buildSecretsE, kyberCheckE, sessionSlotIndexE,
      peMk, peUpd, sbMk, oeMk, oeUpd, buMk, hdMk, pmMk, seMk, iasMk, soMk, snoMk, roMk, rnoMk,
      ikrMk, rkrMk, stMk, stUpd, ahsMk, ahsUpd, ahsfMk, ahsfUpd,
      aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
      aDrKey, aRootKdf, sendGuardE, boolOr, boolBeq, eLet2,
      Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
      Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
      Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
      Comp.foldBoundedM,
      v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
      caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
      eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
      litB, catB, bytesCons, widenB, takeKB,
      bytesLen, bytesBeq, bytesVarint, u32OfNat, u32Beq,
      samplePrim, queryPrim, encEC, encKEM,
      Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false, id_eq]
    dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
      _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
    have hb0 : bits 0 = 1 := by decide
    have hb1 : bits 1 = 1 := by decide
    have hb32 : bits 32 = 6 := by decide
    have hb64 : bits 64 = 7 := by decide
    have hb96 : bits 96 = 7 := by decide
    have hb128 : bits 128 = 8 := by decide
    have hb160 : bits 160 = 8 := by decide
    have hb192 : bits 192 = 8 := by decide
    have hmdh : bits (min K S.N_dh) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
    have hmsend : bits (min K S.N_send_tot) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
    have hmsess : bits (min K S.N_sess_tot) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
    omega
  }

set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem ap_cpaRecvC_size_clamp (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Δ : List PT} (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy)
    {inst₁ : Ext Γ₁ Δ} {inst₂ : Ext Γ₂ Δ} :
    (@cpaRecvC S K Γ₁ Γ₂ Δ opk fhst x inst₁ inst₂).size =
      sizeClamp (@cpaRecvC S K Γ₁ Γ₂ Δ opk fhst x inst₁ inst₂) (58 * bits K + 7000) :=
  eq_sizeClamp_of_le (ap_cpaRecvC_size_le S K opk fhst x)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 800000 in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem ap_aeadCpaRedProg_size_le_clamped (S : Setup) (K : Nat) :
    (aeadCpaRedProg S K).size ≤ 405 * bits K + 60000 := by
  dsimp only [aeadCpaRedProg, TwoStageCostedReduction.size]
  simp only [
    cpaInitC, cpaPreC, cpaDefaultChC, cpaResumeC, cpaPostC, cpaFinishC,
    cpaStepC, cpaNonSendC, cpaNonSendSlotC, wrapCpa, wrapCpaSlot, finishCpaC,
    getDBytes, defaultMsgKeysE, iasAdE, iasAeadCtE, iasMsgPlainE, iasCk1_0E,
    sizeClamp_congr,
    ap_cpaSendSlotB_size_clamp, ap_cpaRecvC_size_clamp,
    ap_finishAuthHybridSendC_size, ap_finalizeAuthFixedDsl_size,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, hkdfRoC, rootRoC, fhstSetBase,
    initPrinFixedB, corruptFixedB, genSpkFixedB, genOpkFixedB, roFixedB, roRootFixedB,
    registerFixedB,
    pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkId, pkbPqspkB, pkbPqspkSig,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
    sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, oeOpkSk, oeOpkPk, oeConsumed,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asAdvKeys, asRoCache, asRootRoCache,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    assNext, assSendOpk, assSendNoOpk, assRecv, assMk, emptyAuthSlotStE,
    ahsfMkSlots, ahsfUpdSlots,
    natEq, natLt, nat2Eq, nat3Eq, bytes2Eq, optU32Eq, sidEq,
    isSomeE, optFst, optSnd,
    peMk, peUpd, sbMk, oeMk, oeUpd, buMk, hdMk, pmMk, seMk, iasMk, soMk, snoMk, roMk, rnoMk,
    ikrMk, rkrMk, stMk, stUpd, ahsMk, ahsUpd, ahsfMk, ahsfUpd,
    emptyAuthStE, emptyAuthHybridStE, emptyAuthHybridStFixedE,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, sendGuardE, boolOr, boolBeq, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    litB, catB, bytesCons, widenB, takeKB,
    bytesLen, bytesBeq, bytesVarint, u32OfNat, u32Beq,
    samplePrim, queryPrim, encEC, encKEM,
    Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false, id_eq]
  dsimp only [clampLe, _root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
    _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  repeat (
    generalize h_sc_eq : sizeClamp _ _ = sc
    fail_if_success (clear h_sc_eq; clear sc)
    have _ := sizeClamp_eq_imp_le h_sc_eq
    clear h_sc_eq)
  have b4Dh : bits (4 * min K S.N_dh) ≤ bits K + 3 := by
    have h := _root_.ReductionDsl.bits_mul 4 (min K S.N_dh)
    have h1 : bits (min K S.N_dh) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
    have : bits 4 = 3 := by decide
    omega
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb32 : bits 32 = 6 := by decide
  have hb64 : bits 64 = 7 := by decide
  have hb96 : bits 96 = 7 := by decide
  have hb128 : bits 128 = 8 := by decide
  have hb160 : bits 160 = 8 := by decide
  have hb192 : bits 192 = 8 := by decide
  have hmdh : bits (min K S.N_dh) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
  have hmsend : bits (min K S.N_send_tot) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
  have hmsess : bits (min K S.N_sess_tot) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
  omega
end AuthPrfCpaSizeBounds

section AuthPrfHmacSizeBounds


open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.Security
open _root_.SignalPqxdh.LegacyCosted
open _root_.SignalPqxdh.Security.ReductionDsl
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
open Computational.Proofs.SignalPqxdh.AtomicLift (pqOpLitSize exprLitSize compLitSize red1LitSize red2LitSize)


set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
@[simp] private theorem hm_liftPrimComp_hmac_size {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    Comp.size (I := pqPrfHmacIface) (liftPrimComp c) = c.size := ap_liftPrimComp_size c

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem hm_prfHmacRedProg_size_le_clamped (S : Setup) (K : Nat) :
    (prfHmacRedProg S K).size ≤ 225 * bits K + 35000 := by
  dsimp only [prfHmacRedProg, CostedReduction.size]
  simp (config := { maxSteps := 1000000 }) only [
    hmInitC, hmHandleC, hmFinishC, hmPreC, hmContX0E, hmPostC, hmDispatchC, hmOther,
    hmKeyIdC, hmKeyC, encPostC, hmEncPreIdC, hmEncPreC, hmForgeIdC, hmForgeC,
    finishIntC, intSendPrepC, sendSidE, hmSendTailC, hmSendC,
    hmRecvPrepC, hmSchedPrepC, forgeRetIdC, forgeRetC, hmSchedFinC, hmSchedC, finErasedE,
    hmRecvTailC, hmRecvC,
    natLe, muKeys, muChal, muPend, muBad, muMk, emptyMuE,
    etmBodyE, etmBody24E, etmTagE, macInputE, initSlotE, muKeyIdEq, initKeyIdE, pendFilterE, pendHitE, dedupE,
    ipUEntry, ipPeer, ipFim, ipFresh, ipIdeal, ipMsgPlain, ipT3, ipKeys6, ipDrKey, ipRks4,
    ipSalt, ipPqMsg, ipAd, ipProv, ipRoC, ipRootC,
    getDBytes, defaultMsgKeysE, iasAdE, iasAeadCtE, iasMsgPlainE, iasCk1_0E,
    spkHonIdealFromPeerC,
    ap_recvFinishTagRunC_size, ap_finishAuthHybridSendC_size,
    ap_prepareAuthHybridRecvC_true_size,
    ap_prepareAuthHybridRecvC_false_size, ap_finalizeAuthFixedDsl_size,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, hkdfRoC, rootRoC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
    matchSentOPKC, matchSentNoOPKC, matchIdealAuthHandshakeC,
    parKEntry, parSecrets, parDhRatchet, parIsUncorrSender,
    parMatchedSess?, parSameEph, parHstDec, parFinishTag, fhstSetBase,
    initPrinFixedB, corruptFixedB, genSpkFixedB, genOpkFixedB, roFixedB, roRootFixedB,
    registerFixedB,
    pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkId, pkbPqspkB, pkbPqspkSig,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
    sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, oeOpkSk, oeOpkPk, oeConsumed,
    pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkId, pkbPqspkB, pkbPqspkSig,
    hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
    pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
    soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched,
    snoA0, snoB0, snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched,
    roBCorr, roA0, roB0, roSb, roOb, roA1, roPk1, roCt, roM,
    rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM,
    aseSpkHonest, asePqspkHonest, aseEkASk, aseFresh, aseChallenged,
    ikrPqspkPk, ikrKemCt, ikrKemSs, rkrPqspkPk, rkrKemCt, rkrKemSs,
    iasSid, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk,
    iasKemCt, iasEphAPk, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    assNext, assSendOpk, assSendNoOpk, assRecv, assMk, emptyAuthSlotStE,
    lookupSendSlotE, lookupSendSlotOrZeroE, allocSendSlotE,
    lookupRecvSlotE, lookupRecvSlotOrZeroE, allocRecvSlotE,
    ahsfMkSlots, ahsfUpdSlots,
    natEq, natLt, nat2Eq, nat3Eq, bytes2Eq, optU32Eq, sidEq, saltBytesE, sameSaltKeyE, kyberEq,
    isSomeE, optFst, optSnd, firstMsgADE, buildSecretsE, kyberCheckE, sessionSlotIndexE,
    peMk, peUpd, sbMk, oeMk, oeUpd, buMk, hdMk, pmMk, seMk, iasMk, soMk, snoMk, roMk, rnoMk,
    ikrMk, rkrMk, stMk, stUpd, ahsMk, ahsUpd, ahsfMk, ahsfUpd,
    emptyAuthStE, emptyAuthHybridStE, emptyAuthHybridStFixedE,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, sendGuardE, boolOr, boolBeq, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM,
    ap_liftPrimComp_size, hm_liftPrimComp_hmac_size,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    litB, catB, bytesCons, widenB, takeKB,
    bytesLen, bytesBeq, bytesVarint, u32OfNat, u32Beq,
    samplePrim, sampleChal, queryPrim,
    encEC, encKEM,
    AuthPrfHmac.bytesTake, AuthPrfHmac.bytesDrop, queryHmacEval, AuthPrfHmac.mapMV,
    Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false, id_eq]
  dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
    _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  have b4Dh : bits (4 * min K S.N_dh) ≤ bits K + 3 := by
    have h := _root_.ReductionDsl.bits_mul 4 (min K S.N_dh)
    have h1 : bits (min K S.N_dh) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
    have : bits 4 = 3 := by decide
    omega
  have bHdr : bits firstMsgHdrLen ≤ 16 := by decide
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb8 : bits 8 = 4 := by decide
  have hb24 : bits 24 = 5 := by decide
  have hb32 : bits 32 = 6 := by decide
  have hb64 : bits 64 = 7 := by decide
  have hb96 : bits 96 = 7 := by decide
  have hb128 : bits 128 = 8 := by decide
  have hb160 : bits 160 = 8 := by decide
  have hb192 : bits 192 = 8 := by decide
  have hmdh : bits (min K S.N_dh) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
  have hmsess : bits (min K S.N_sess_tot) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
  omega
end AuthPrfHmacSizeBounds

open OracleSpec OracleComp
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.Costed
  (pqAuthPrimIface pqAuthSigAndDdhIface pqPrfMkIface pqPrfHmacIface authCodec)
open _root_.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security
open _root_.SignalPqxdh.Security.AuthSubHops1to3
open _root_.SignalPqxdh.Security.ReductionDsl
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
open Computational.Proofs.ReductionDsl.AtomicSizeHonest
open Computational.Proofs.SignalPqxdh.AtomicLift

def sigAuth1KeyAtomicProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqAuthSigAndDdhIface (authSpec S) (authCodec S)
      (PB 32) .unit .bool (.prod (PB 1569) (PB 64)) :=
  liftAuth1Stage tlAuthSigDdh S (sigAuth1KeyDslProg S b)

def shcrAuth1KeyAtomicProg (S : Setup) (b : QueryBudget) :
    TwoStageCostedReduction pqAtomicOps pqAuthPrimIface (authSpec S) (authCodec S)
      (.prod (PB 1568) (PB 3168)) .unit .bool (PB 1568)
      (.prod (PB 32) (PB 1568)) (PB 1568) :=
  liftAuth2Stage tlAuthPrim S (shcrAuth1KeyDslProg S b)

def fgAuth1KeyGapDhAtomicProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqAuthSigAndDdhIface (authSpec S) (authCodec S)
      (.prod (PB 32) (PB 32)) .unit .bool (PB 32) :=
  liftAuth1Stage tlAuthSigDdh S (fgAuth1KeyGapDhProg S b.q_total)

def prfCk1KeyAtomicProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqAuthPrimIface (authSpec S) (authCodec S)
      (.prod (PB 32) (PB 32)) .unit .bool .bool :=
  liftAuth1Stage tlAuthPrim S (prfCkRedProg1Key S b.q_total)

def prfMsgKeys1KeyAtomicProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqPrfMkIface (authSpec S) (authCodec S)
      .unit .unit .bool .bool :=
  liftAuth1Stage tlPrfMk S (prfMsgKeysRedProg1Key S b.q_total)

def aeadCpa1KeyAtomicProg (S : Setup) (b : QueryBudget) :
    TwoStageCostedReduction pqAtomicOps pqAuthPrimIface (authSpec S) (authCodec S)
      .unit .unit .bool (.prod (PB 158) (.prod (PB 32) (PB 32)))
      (.opt (PB 32)) .bool :=
  liftAuth2Stage tlAuthPrim S (aeadCpaRedProg1Key S b.q_total)

def prfHmac1KeyAtomicProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqPrfHmacIface (authSpec S) (authCodec S)
      .unit .unit .bool .bool :=
  liftAuth1Stage tlPrfHmac S (prfHmacRedProg1Key S b.q_total)

private theorem a1_eleven_mul_clamped_le_stepCostBudget {c : ℕ} (S : Setup) (b : QueryBudget)
    (h11 : 11 * c ≤ 720896 + 1441792 * b.q_total +
      360448 * min b.q_total S.N_dh + 360448 * min b.q_total S.N_sess_tot +
      11264 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
      720896 * (b.q_total * b.q_total) +
      360448 * (b.q_total * min b.q_total S.N_dh) +
      360448 * (b.q_total * min b.q_total S.N_sess_tot) +
      22528 * (min b.q_total S.N_dh * min b.q_total S.N_dh) +
      2816 * (min b.q_total S.N_dh * min b.q_total S.N_sess_tot)) :
    c ≤ _root_.SignalPqxdh.Security.stepCostBudget S b := by
  unfold _root_.SignalPqxdh.Security.stepCostBudget
  dsimp only
  have hEq : 11 * (2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) +
      2 ^ 15 * (b.q_total + 1) * (min b.q_total S.N_dh + min b.q_total S.N_sess_tot) +
      2 ^ 10 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
      2 ^ 11 * min b.q_total S.N_dh ^ 2 +
      2 ^ 8 * min b.q_total S.N_dh * min b.q_total S.N_sess_tot) =
      720896 + 1441792 * b.q_total +
        360448 * min b.q_total S.N_dh + 360448 * min b.q_total S.N_sess_tot +
        11264 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
        720896 * (b.q_total * b.q_total) +
        360448 * (b.q_total * min b.q_total S.N_dh) +
        360448 * (b.q_total * min b.q_total S.N_sess_tot) +
        22528 * (min b.q_total S.N_dh * min b.q_total S.N_dh) +
        2816 * (min b.q_total S.N_dh * min b.q_total S.N_sess_tot) := by ring
  exact Nat.le_of_mul_le_mul_left (h11.trans_eq hEq.symm) (by omega)

private theorem a1_two_mul_clamped_le_stepCostBudget {c : ℕ} (S : Setup) (b : QueryBudget)
    (h2 : 2 * c ≤ 131072 + 262144 * b.q_total +
      65536 * min b.q_total S.N_dh + 65536 * min b.q_total S.N_sess_tot +
      2048 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
      131072 * (b.q_total * b.q_total) +
      65536 * (b.q_total * min b.q_total S.N_dh) +
      65536 * (b.q_total * min b.q_total S.N_sess_tot) +
      4096 * (min b.q_total S.N_dh * min b.q_total S.N_dh) +
      512 * (min b.q_total S.N_dh * min b.q_total S.N_sess_tot)) :
    c ≤ _root_.SignalPqxdh.Security.stepCostBudget S b := by
  unfold _root_.SignalPqxdh.Security.stepCostBudget
  dsimp only
  have hEq : 2 * (2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) +
      2 ^ 15 * (b.q_total + 1) * (min b.q_total S.N_dh + min b.q_total S.N_sess_tot) +
      2 ^ 10 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
      2 ^ 11 * min b.q_total S.N_dh ^ 2 +
      2 ^ 8 * min b.q_total S.N_dh * min b.q_total S.N_sess_tot) =
      131072 + 262144 * b.q_total +
        65536 * min b.q_total S.N_dh + 65536 * min b.q_total S.N_sess_tot +
        2048 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
        131072 * (b.q_total * b.q_total) +
        65536 * (b.q_total * min b.q_total S.N_dh) +
        65536 * (b.q_total * min b.q_total S.N_sess_tot) +
        4096 * (min b.q_total S.N_dh * min b.q_total S.N_dh) +
        512 * (min b.q_total S.N_dh * min b.q_total S.N_sess_tot) := by ring
  exact Nat.le_of_mul_le_mul_left (h2.trans_eq hEq.symm) (by omega)

private theorem a1_log_le_budget (c q ld ls : ℕ) (hc : c ≤ 2048) :
    c * ld + c * ls ≤ 2048 * (q + 1) * (ld + ls) := by
  calc c * ld + c * ls = c * (ld + ls) := by ring
    _ ≤ (2048 * (q + 1)) * (ld + ls) := Nat.mul_le_mul_right _ (by omega)

private theorem a1_log11_le_budget (c q ld ls : ℕ) (hc : c ≤ 11264) :
    c * (q + 1) * ls ≤ 11264 * (q + 1) * (ld + ls) := by
  calc (c * (q + 1)) * ls ≤ (c * (q + 1)) * (ld + ls) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ (11264 * (q + 1)) * (ld + ls) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc)

open _root_.SignalPqxdh.LegacyCosted _root_.SignalPqxdh.Security.ReductionDsl _root_.SignalPqxdh.Security.ReductionDsl.AuthHs _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf _root_.SignalPqxdh.Security.ReductionDsl.AuthAead _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac _root_.Proofs.SignalPqxdh.Security _root_.Proofs.SignalPqxdh.Security.PqxdhDelta Computational.Proofs.SignalPqxdh.AtomicLift in
theorem a1g_finish_cost_le_tight (S : Setup) (K : Nat) :
    (fgAuth1KeyGapDhProg S K).finish.cost ≤
      1100 + 1100 * K + 1000 * S.N_dh + 1000 * S.N_sess_tot +
        200 * (K * S.N_dh) + 200 * (S.N_dh * S.N_dh) + 50 * (S.N_dh * S.N_sess_tot) := by
  refine le_trans (a1g_finish_cost_le_v2 S K) ?_
  have hd : min K S.N_dh ≤ S.N_dh := Nat.min_le_right K S.N_dh
  have hs : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right K S.N_sess_tot
  have h1 : K * min K S.N_dh ≤ K * S.N_dh := Nat.mul_le_mul_left K hd
  have h2 : min K S.N_dh * min K S.N_dh ≤ S.N_dh * S.N_dh := Nat.mul_le_mul hd hd
  have h3 : min K S.N_dh * min K S.N_sess_tot ≤ S.N_dh * S.N_sess_tot := Nat.mul_le_mul hd hs
  omega

theorem fgAuth1KeyGapDhAtomicProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (fgAuth1KeyGapDhAtomicProg S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  refine a1_two_mul_clamped_le_stepCostBudget S b
    (le_trans (liftAuth1Stage_totalCost_two_mul_le tlAuthSigDdh rfl S
      (fgAuth1KeyGapDhProg S b.q_total) b.q_total) ?_)
  have hr64 := fgAuth1KeyGapDhProg_r64_le S b.q_total b.q_total
  have hInit := a1g_init_cost_le_v2 S b.q_total
  have hHdl := a1g_handle_cost_le_v2 S b.q_total
  have hFin := a1g_finish_cost_le_v2 S b.q_total
  have hU : LegacyCosted.pqSigAndDdhIface.uCost = 1 := rfl
  have hC : (LegacyCosted.authCodec S).codecCost = 32 := rfl
  dsimp only [CostedReduction.totalCost]
  rw [hU, hC]
  generalize (fgAuth1KeyGapDhProg S b.q_total).init.cost = cInit at *
  generalize (fgAuth1KeyGapDhProg S b.q_total).handle.cost = cHdl at *
  generalize (fgAuth1KeyGapDhProg S b.q_total).finish.cost = cFin at *
  generalize (fgAuth1KeyGapDhProg S b.q_total).totalQueries
    (fun _ => 0) (sampR64W tlAuthSigDdh.hsmp) b.q_total = qr64 at *
  generalize b.q_total = q at *
  generalize min q S.N_dh = md at *
  generalize min q S.N_sess_tot = ms at *
  generalize Nat.log 2 S.N_dh = ld at *
  generalize Nat.log 2 S.N_sess_tot = ls at *
  have hMax : max 1 (cHdl + 32) ≤ 80032 + 30000 * q + 10000 * md := by omega
  have hMul : q * max 1 (cHdl + 32) ≤
      80032 * q + 30000 * (q * q) + 10000 * (q * md) := by
    calc q * max 1 (cHdl + 32)
        ≤ q * (80032 + 30000 * q + 10000 * md) := Nat.mul_le_mul_left q hMax
      _ = 80032 * q + 30000 * (q * q) + 10000 * (q * md) := by ring
  have hLog := a1_log_le_budget 30 q ld ls (by omega)
  generalize 2048 * (q + 1) * (ld + ls) = ql at *
  generalize q * q = qq at *
  generalize q * md = qmd at *
  generalize q * ms = qms at *
  generalize md * md = md2 at *
  generalize md * ms = mdms at *
  omega

end Proofs.SignalPqxdh.Security.PqxdhDelta

namespace Proofs.SignalPqxdh.Security.PqxdhDelta.Auth1KeyCostHelpers

section Hs
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh _root_.SignalPqxdh.LegacyCosted _root_.SignalPqxdh.Security _root_.SignalPqxdh.Security.ReductionDsl _root_.SignalPqxdh.Security.ReductionDsl.AuthHs

private theorem a1s_handle2_cost_le (S : Setup) (K : Nat) :
    (sigAuth1KeyProg S K).handle.cost ≤ 107000 + 38000 * K + 10500 * min K S.N_dh := by
  refine le_trans (Comp.cost_le_costUB _) ?_
  dsimp only [sigAuth1KeyProg, a1sHandle2Dsl]
  have hP := a1sPreC_costUB_le_tight S K
    (Δ := [a1sStTy, authQueryTy])
    (.vz : Var [a1sStTy, authQueryTy] a1sStTy)
    (.vs .vz : Var [a1sStTy, authQueryTy] authQueryTy)
  have hG := a1gStep2C_costUB_le S K
    (Γ₁ := a1g2StTy :: .unit :: (.sum a1sRS .unit) :: [a1sStTy, authQueryTy])
    (Γ₂ := [a1sStTy, authQueryTy])
    (Δ := a1g2StTy :: .unit :: (.sum a1sRS .unit) :: [a1sStTy, authQueryTy])
    Var.vz (.vs .vz : Var [a1sStTy, authQueryTy] authQueryTy)
  simp only [a1sStep2C, a1sDelegate2C, a1sCaseAPa2, bindV, letV, caseSumV, Comp.letC,
    isSomeE, a1sG, a1sMk, a1sTp, a1sTpk, a1sFg, aNone, v, Comp.costUB, Expr.costUB]
  generalize min K S.N_dh = md at *
  omega

end Hs

end Proofs.SignalPqxdh.Security.PqxdhDelta.Auth1KeyCostHelpers

namespace Proofs.SignalPqxdh.Security.PqxdhDelta
open OracleSpec OracleComp
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.Costed
  (pqAuthPrimIface pqAuthSigAndDdhIface pqPrfMkIface pqPrfHmacIface authCodec)
open _root_.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security
open _root_.SignalPqxdh.Security.AuthSubHops1to3
open _root_.SignalPqxdh.Security.ReductionDsl
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
open Computational.Proofs.ReductionDsl.AtomicSizeHonest
open Computational.Proofs.SignalPqxdh.AtomicLift
open Auth1KeyCostHelpers

theorem sigAuth1KeyAtomicProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (sigAuth1KeyAtomicProg S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  refine a1_two_mul_clamped_le_stepCostBudget S b
    (le_trans (liftAuth1Stage_totalCost_two_mul_le tlAuthSigDdh rfl S
      (sigAuth1KeyDslProg S b) b.q_total) ?_)
  dsimp only [sigAuth1KeyDslProg]
  have hr64 := sigAuth1KeyProg_r64_le S b.q_total b.q_total
  have hInit := a1s_init_cost_le_tight S b.q_total
  have hHdl := a1s_handle2_cost_le S b.q_total
  have hFin := a1s_finish_cost_le S b.q_total
  have hU : LegacyCosted.pqSigAndDdhIface.uCost = 1 := rfl
  have hC : (LegacyCosted.authCodec S).codecCost = 32 := rfl
  dsimp only [CostedReduction.totalCost]
  rw [hU, hC]
  generalize (sigAuth1KeyProg S b.q_total).init.cost = cInit at *
  generalize (sigAuth1KeyProg S b.q_total).handle.cost = cHdl at *
  generalize (sigAuth1KeyProg S b.q_total).finish.cost = cFin at *
  generalize (sigAuth1KeyProg S b.q_total).totalQueries
    (fun _ => 0) (sampR64W tlAuthSigDdh.hsmp) b.q_total = qr64 at *
  generalize b.q_total = q at *
  generalize min q S.N_dh = md at *
  generalize min q S.N_sess_tot = ms at *
  generalize Nat.log 2 S.N_dh = ld at *
  generalize Nat.log 2 S.N_sess_tot = ls at *
  have hMax : max 1 (cHdl + 32) ≤ 107032 + 38000 * q + 10500 * md := by omega
  have hMul : q * max 1 (cHdl + 32) ≤
      107032 * q + 38000 * (q * q) + 10500 * (q * md) := by
    calc q * max 1 (cHdl + 32)
        ≤ q * (107032 + 38000 * q + 10500 * md) := Nat.mul_le_mul_left q hMax
      _ = 107032 * q + 38000 * (q * q) + 10500 * (q * md) := by ring
  have hLog := a1_log_le_budget 3 q ld ls (by omega)
  generalize 2048 * (q + 1) * (ld + ls) = ql at *
  generalize q * md = qmd at *
  generalize q * ms = qms at *
  generalize md * md = md2 at *
  generalize md * ms = mdms at *
  rcases q with _ | _ | n
  · omega
  · omega
  · have hqq : 4 + 4 * n ≤ (n + 2) * (n + 2) := by
      have : (n + 2) * (n + 2) = n * n + 4 * n + 4 := by ring
      omega
    have hGap : 3 * (38000 * ((n + 2) * (n + 2))) + 17072 * (4 + 4 * n) ≤
        131072 * ((n + 2) * (n + 2)) := by
      have hSub : 131072 * ((n + 2) * (n + 2)) =
          114000 * ((n + 2) * (n + 2)) + 17072 * ((n + 2) * (n + 2)) := by ring
      have := Nat.mul_le_mul_left 17072 hqq
      omega
    generalize (n + 2) * (n + 2) = qq at *
    omega

theorem shcrAuth1KeyAtomicProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (shcrAuth1KeyAtomicProg S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  refine a1_two_mul_clamped_le_stepCostBudget S b
    (le_trans (liftAuth2Stage_totalCost_two_mul_le tlAuthPrim rfl S
      (shcrAuth1KeyDslProg S b) b.q_total) ?_)
  dsimp only [shcrAuth1KeyDslProg]
  have hCost12 := shcrReductionAuthProg1Key_totalCost_le_twoKey S b.q_total b.q_total b.q_total
  have hr64_12 := shcrReductionAuthProg1Key_totalQueries_le_twoKey S b.q_total b.q_total b.q_total
    (fun _ => 0) (sampR64W tlAuthPrim.hsmp)
  have hr64 : (shcrReductionAuthProg S b.q_total b.q_total).totalQueries
      (fun _ => 0) (sampR64W tlAuthPrim.hsmp) b.q_total ≤ 4 * b.q_total :=
    shcrReductionAuthProg_r64_le S b.q_total
  have hInit := shcr_init_cost_le_tight S b.q_total b.q_total
  have hPre := shcr_handlePre_cost_le_tight S b.q_total b.q_total
  have hPost := shcr_handlePost_cost_le_tight S b.q_total b.q_total
  have hCh := shcr_chDone_cost_le S b.q_total b.q_total
  have hRes := shcr_resume_cost_le S b.q_total b.q_total
  have hFin := shcr_finish_cost_le S b.q_total b.q_total
  have hU : LegacyCosted.pqPrimIface.uCost = 1 := rfl
  have hC : (LegacyCosted.authCodec S).codecCost = 32 := rfl
  have hTot : (shcrReductionAuthProg S b.q_total b.q_total).totalCost b.q_total =
      (shcrReductionAuthProg S b.q_total b.q_total).init.cost +
      b.q_total * max 1 (max (shcrReductionAuthProg S b.q_total b.q_total).handlePre.cost
        (shcrReductionAuthProg S b.q_total b.q_total).handlePost.cost + 32) +
      max (shcrReductionAuthProg S b.q_total b.q_total).chDone.cost
        (shcrReductionAuthProg S b.q_total b.q_total).resume.cost +
      (shcrReductionAuthProg S b.q_total b.q_total).finish.cost := by
    simp only [TwoStageCostedReduction.totalCost, hU, hC]
  rw [hTot] at hCost12
  generalize (shcrReductionAuthProg1Key S b.q_total b.q_total).totalCost b.q_total = c1 at *
  generalize (shcrReductionAuthProg1Key S b.q_total b.q_total).totalQueries
    (fun _ => 0) (sampR64W tlAuthPrim.hsmp) b.q_total = qr1 at *
  generalize (shcrReductionAuthProg S b.q_total b.q_total).totalQueries
    (fun _ => 0) (sampR64W tlAuthPrim.hsmp) b.q_total = qr2 at *
  generalize (shcrReductionAuthProg S b.q_total b.q_total).init.cost = cInit at *
  generalize (shcrReductionAuthProg S b.q_total b.q_total).handlePre.cost = cPre at *
  generalize (shcrReductionAuthProg S b.q_total b.q_total).handlePost.cost = cPost at *
  generalize (shcrReductionAuthProg S b.q_total b.q_total).chDone.cost = cCh at *
  generalize (shcrReductionAuthProg S b.q_total b.q_total).resume.cost = cRes at *
  generalize (shcrReductionAuthProg S b.q_total b.q_total).finish.cost = cFin at *
  generalize b.q_total = q at *
  generalize min q S.N_dh = md at *
  generalize min q S.N_sess_tot = ms at *
  generalize Nat.log 2 S.N_dh = ld at *
  generalize Nat.log 2 S.N_sess_tot = ls at *
  have hMax : max 1 (max cPre cPost + 32) ≤ 120032 + 22000 * q + 6000 * md := by omega
  have hMul : q * max 1 (max cPre cPost + 32) ≤
      120032 * q + 22000 * (q * q) + 6000 * (q * md) := by
    calc q * max 1 (max cPre cPost + 32)
        ≤ q * (120032 + 22000 * q + 6000 * md) := Nat.mul_le_mul_left q hMax
      _ = 120032 * q + 22000 * (q * q) + 6000 * (q * md) := by ring
  have hMaxCh : max cCh cRes ≤ 10000 + 4500 * q := by omega
  have hLog := a1_log_le_budget 12 q ld ls (by omega)
  generalize 2048 * (q + 1) * (ld + ls) = ql at *
  generalize q * md = qmd at *
  generalize q * ms = qms at *
  generalize md * md = md2 at *
  generalize md * ms = mdms at *
  rcases q with _ | _ | n
  · omega
  · omega
  · have hqq : 4 + 4 * n ≤ (n + 2) * (n + 2) := by
      have : (n + 2) * (n + 2) = n * n + 4 * n + 4 := by ring
      omega
    have hGap : 3 * (22000 * ((n + 2) * (n + 2))) + 65072 * (4 + 4 * n) ≤
        131072 * ((n + 2) * (n + 2)) := by
      have hSub : 131072 * ((n + 2) * (n + 2)) =
          66000 * ((n + 2) * (n + 2)) + 65072 * ((n + 2) * (n + 2)) := by ring
      have := Nat.mul_le_mul_left 65072 hqq
      omega
    generalize (n + 2) * (n + 2) = qq at *
    omega

end Proofs.SignalPqxdh.Security.PqxdhDelta

namespace Proofs.SignalPqxdh.Security.PqxdhDelta.Auth1KeyCostHelpers

section Auth1KeyPrfCost
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh _root_.SignalPqxdh.LegacyCosted _root_.SignalPqxdh.Security
open _root_.SignalPqxdh.Security.ReductionDsl hiding sessionIdTy msgKeysTy authRespTy
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
open OracleSpec OracleComp

attribute [local simp] Expr.cost Comp.cost

private theorem a1_lookupSendSlotE_cost {Γ : List PT}
    (ss : Expr pqxdhOps Γ authSlotStateTy) (sid : Expr pqxdhOps Γ sessionIdTy) :
    (lookupSendSlotE ss sid).cost = ss.cost + sid.cost + 148 := by
  simp only [lookupSendSlotE, eLet2, eLet, eCaseSum, assSendOpk, assSendNoOpk, v, Expr.cost]
  omega

private theorem a1_allocSendSlotE_cost {Γ : List PT}
    (ss : Expr pqxdhOps Γ authSlotStateTy) (sid : Expr pqxdhOps Γ sessionIdTy) :
    (allocSendSlotE ss sid).cost = ss.cost + sid.cost + 436 := by
  simp only [allocSendSlotE, eLet2, eLet, eCaseSum, eCaseOpt, assMk, assNext, assSendOpk,
    assSendNoOpk, assRecv, v, Expr.cost, AuthPrf.bits_0, AuthPrf.bits_1]
  omega

private theorem a1_allocRecvSlotE_cost {Γ : List PT}
    (ss : Expr pqxdhOps Γ authSlotStateTy) (rc : Expr pqxdhOps Γ .nat) :
    (allocRecvSlotE ss rc).cost = ss.cost + rc.cost + 231 := by
  simp only [allocRecvSlotE, eLet2, eLet, eCaseOpt, assMk, assNext, assSendOpk,
    assSendNoOpk, assRecv, v, Expr.cost, AuthPrf.bits_1]
  omega

private theorem a1_prfCkInitDslK_cost_eq (S : Setup) (K : Nat) :
    (prfCkInitDslK S K).cost = 71 + bits (min K S.N_sess_tot) := by
  simp only [prfCkInitDslK, bindV, emptyAuthHybridStFixedE, emptyAuthHybridStE, emptyAuthStE,
    ahsfMk, ahsfMkSlots, emptyAuthSlotStE, assMk, ahsMk, stMk, cost_samplePrim, PSamp.cost,
    Ty.wd, v, Comp.cost, Expr.cost, AuthPrf.bits_0]
  omega

private theorem a1_prfMsgKeysInitDslK_cost_eq (S : Setup) (K : Nat) :
    (prfMsgKeysInitDslK S K).cost =
      72 + bits (min K S.N_sess_tot) + bits (min K S.N_recv_tot + 1) := by
  simp only [prfMsgKeysInitDslK, bindV, mkcMk, emptyAuthHybridStFixedE, emptyAuthHybridStE,
    emptyAuthStE, ahsfMk, ahsfMkSlots, emptyAuthSlotStE, assMk, ahsMk, stMk,
    cost_sampleChal, PSamp.cost, Ty.wd, v, Comp.cost, Expr.cost, AuthPrf.bits_0]
  omega

private theorem a1_recvFinishTagRunC_cost_tight (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (tag : Var Γ₁ recvFinishTagTy) (res? : Expr pqxdhOps Δ recvFinishResTy) [Ext Γ₁ Δ] :
    (recvFinishTagRunC S K tag res?).cost =
      res?.cost + 350 + K * 39 + min K S.N_dh * 7786 := by
  simp only [recvFinishTagRunC, findHonestC, matchSentOPKC, matchSentNoOPKC, bindV, letV,
    caseOptV, caseSumV, findMV, consumeFirstMV, eMap, natEq, nat2Eq, nat3Eq, oeMk, oeUpd, roMk,
    rnoMk, stMk, stUpd, ahsMk, ahsUpd, aNone, aRecvHonest, aRecvUnfresh, peIkAPk, peCorrupted,
    sbSpkPk, sbPqspkPk, oeOpkSk, oeOpkPk, hdrIkAPk, hdrEkAPk, hdrKemCt,
    pkmHdr, soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched, snoA0, snoB0,
    snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched, roBCorr, roA0, roB0, roSb, roOb,
    roA1, roPk1, roCt, roM, rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM, asSecb,
    asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions, asUsedSendSessions,
    asUsedRecvOPK, asUsedRecvNoOPK, asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents,
    asRecvdNoOPKEvents, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    cost_letC, cost_queryPrim, cost_bytesBeq, cost_boolOr, v, Comp.cost, Expr.cost, Ty.wd,
    PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  omega

private theorem a1_prepareAuthHybridRecvC_true_cost_tight (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prepareAuthHybridRecvC S K true hst x :
      Comp pqxdhOps pqPrimIface Δ (.opt preparedAuthRecvTy)).cost =
      6826 + K * 246 + min K S.N_dh * 7753 := by
  simp only [prepareAuthHybridRecvC, koskSenderOkC, findHonestC, isAdvRegC,
    matchIdealAuthHandshakeC, bindV, letV, caseOptV, findMV, eFind, eAny, eCaseOpt,
    natEq, nat2Eq, nat3Eq, optU32Eq_cost, kyberCheckE_cost, buildSecretsE_cost, isSomeE, rkrMk,
    ahsMk, ahsUpd, peSecIKA0, peIkAPk, peCorrupted, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk,
    oeOpkSk, oeOpkPk, oeConsumed, hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
    pkmHdr, pkmEphAPk, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk,
    iasPeerPqspkPk, iasKemCt, iasEphAPk, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries,
    asUsedRecvOPK, asUsedKyberTriples, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs,
    ahsIdealSessions, cost_letC, cost_queryPrim, cost_bytesBeq, cost_bytesLen, cost_u32OfNat,
    cost_u32Beq, cost_boolOr, v, Comp.cost, Expr.cost, Ty.wd, PNat.val_ofNat, AuthPrf.bits_32, ite_true]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  omega

private theorem a1_prepareAuthHybridRecvC_false_cost_tight (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prepareAuthHybridRecvC S K false hst x :
      Comp pqxdhOps pqPrimIface Δ (.opt preparedAuthRecvTy)).cost =
      6696 + K * 221 + min K S.N_dh * 7753 := by
  simp only [prepareAuthHybridRecvC, koskSenderOkC, findHonestC, isAdvRegC,
    matchIdealAuthHandshakeC, bindV, letV, caseOptV, findMV, eFind, eAny, eCaseOpt,
    natEq, nat2Eq, nat3Eq, optU32Eq_cost, kyberCheckE_cost, buildSecretsE_cost, isSomeE, rkrMk,
    ahsMk, ahsUpd, peSecIKA0, peIkAPk, peCorrupted, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk,
    hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt, pkmHdr, pkmEphAPk,
    iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk, iasKemCt,
    iasEphAPk, asHasWonAuth, asPrincipals, asSpkBundles, asUsedRecvNoOPK,
    asUsedKyberTriples, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    cost_letC, cost_queryPrim, cost_bytesBeq, cost_bytesLen, cost_u32OfNat,
    cost_u32Beq, cost_boolOr, v, Comp.cost, Expr.cost, Ty.wd, PNat.val_ofNat, AuthPrf.bits_32,
    Bool.false_eq_true, ite_false]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  omega

private theorem a1_finalizeAuthFixedDsl_cost_tight (S : Setup) (K : Nat) {Γ : List PT} :
    (finalizeAuthFixedDsl S K (Γ := Γ)).cost =
      100 + min K S.N_dh * 413 + min K S.N_dh ^ 2 * 1088 + K * 97 + K ^ 2 * 9511 := by
  have hbody : (finalizeAuthFixedBodyDsl S K (Γ := Γ)).cost =
      57 + min K S.N_dh * 48 + (4 * min K S.N_dh) ^ 2 * 68 + K * 97 + K ^ 2 * 9511 := by
    simp only [finalizeAuthFixedBodyDsl, hasDuplicateBytesDsl_cost, hasBadSigAuthDsl_cost,
      hasKemPkCollisionAuthDsl_cost, hasBadKemShCrRecordsDsl_cost, notAllChallengedCleanDsl_cost,
      asHasWonAuth, cost_boolOr, cost_boolBeq, cost_samplePrim, PSamp.cost, Ty.wd,
      Comp.cost, Expr.cost, PNat.val_ofNat]
    omega
  simp only [finalizeAuthFixedDsl, hbody, ahsBase, asPrincipals,
    asSpkBundles, asOpkEntries, asSessions, peIkAPk, sbSpkPk, oeOpkPk, aseEkASk,
    cost_letC, cost_queryPrim, Ty.wd, Comp.cost, Expr.cost, PNat.val_ofNat]
  ring

private theorem a1_prfCkFinishDsl_cost_tight (S : Setup) (K : Nat) :
    (prfCkFinishDsl S K).cost =
      114 + min K S.N_dh * 413 + min K S.N_dh ^ 2 * 1088 + K * 97 + K ^ 2 * 9511 := by
  simp only [prfCkFinishDsl, letV, ckSecb, ckFhst, ahsfHybrid, cost_letC,
    a1_finalizeAuthFixedDsl_cost_tight, Expr.cost]
  ring

private theorem a1_prfMsgKeysFinishDsl_cost_tight (S : Setup) (K : Nat) :
    (prfMsgKeysFinishDsl S K).cost =
      118 + min K S.N_dh * 413 + min K S.N_dh ^ 2 * 1088 + K * 97 + K ^ 2 * 9511 := by
  simp only [prfMsgKeysFinishDsl, letV, mkcSecb, mkcFhst, ahsfHybrid, cost_liftPrimComp,
    cost_letC, a1_finalizeAuthFixedDsl_cost_tight, v, Expr.cost]
  ring

private theorem a1_finishAuthRecvCkC_cost_tight (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (msg : Var Γ₁ AuthPrf.preKeyMsgTy) (prep : Var Γ₂ preparedAuthRecvTy)
    (drKey : Expr pqxdhOps Δ AuthPrf.drKeyTy) (rk1 : Expr pqxdhOps Δ (B 32))
    (spqrSalt? : Expr pqxdhOps Δ (.opt (B 32))) (rc' : Expr pqxdhOps Δ .nat)
    (p : Expr pqxdhOps Δ (.prod (B 32) (B 32))) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (finishAuthRecvCkC S K msg prep drKey rk1 spqrSalt? rc' p).cost =
      drKey.cost + rk1.cost + spqrSalt?.cost + rc'.cost + p.cost +
      1827 + K * 39 + min K S.N_dh * 7786 := by
  simp only [finishAuthRecvCkC, bindV, letV, eCaseOpt, firstMsgADE_cost,
    a1_recvFinishTagRunC_cost_tight, ahsBase, parHstDec, parFinishTag, parKEntry,
    hdrIkAPk, pkmHdr, peIkAPk, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
    asRoCache, asRootRoCache, ahsfMk, ahsfMkSlots, emptyAuthSlotStE, assMk,
    cost_letC, cost_queryPrim, v, Comp.cost, Expr.cost, Ty.wd, PNat.val_ofNat, AuthPrf.bits_0]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  omega

private theorem a1_finishAuthSendMkC_cost_tight (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy)
    (sid : Expr pqxdhOps Δ sessionIdTy) (uE : Expr pqxdhOps Δ AuthPrf.principalEntryTy)
    (pp : Expr pqxdhOps Δ (.opt (.prod .nat AuthPrf.principalEntryTy))) (isFresh : Expr pqxdhOps Δ .bool)
    (bu : Expr pqxdhOps Δ AuthPrf.preKeyBundleTy) (m01 : Expr pqxdhOps Δ (.prod (B 32) (B 32)))
    (keys6 : Expr pqxdhOps Δ keys6Ty) (drKey : Expr pqxdhOps Δ AuthPrf.drKeyTy)
    (rk1 mkSeed ck1_1 : Expr pqxdhOps Δ (B 32)) (spqrSalt? : Expr pqxdhOps Δ (.opt (B 32)))
    (pqMsg msgPlain : Expr pqxdhOps Δ (B 32)) (mks : Expr pqxdhOps Δ msgKeysTy) [Ext Γ₁ Δ] :
    (finishAuthSendMkC S K fhst sid uE pp isFresh bu m01 keys6 drKey rk1 mkSeed ck1_1
      spqrSalt? pqMsg msgPlain mks).cost =
      sid.cost + uE.cost + pp.cost + isFresh.cost + bu.cost + m01.cost + keys6.cost +
      drKey.cost + rk1.cost + mkSeed.cost + ck1_1.cost + spqrSalt?.cost + pqMsg.cost +
      msgPlain.cost + mks.cost + 2354 + min K S.N_dh * 920 + K * 3239 := by
  simp only [finishAuthSendMkC, bindV, letV, firstMsgADE_cost, finishAuthHybridSendC_cost,
    ahsfHybrid, ahsBase, peIkAPk, pkbIkB, asRoCache, asRootRoCache, ahsfUpd, ahsfMkSlots,
    ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    cost_letC, cost_queryPrim, cost_litB, v, Comp.cost, Expr.cost,
    Ty.wd, PNat.val_ofNat, List.length_nil]
  omega

private theorem a1_finishAuthRecvMkC_cost_tight (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (msg : Var Γ₁ AuthPrf.preKeyMsgTy) (prep : Var Γ₂ preparedAuthRecvTy)
    (drKey : Expr pqxdhOps Δ AuthPrf.drKeyTy) (rk1 ck1_1 : Expr pqxdhOps Δ (B 32)) (rc' : Expr pqxdhOps Δ .nat)
    (cache' : Expr pqxdhOps Δ authMkSaltCacheTy) (mks : Expr pqxdhOps Δ msgKeysTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (finishAuthRecvMkC S K msg prep drKey rk1 ck1_1 rc' cache' mks).cost =
      drKey.cost + rk1.cost + ck1_1.cost + rc'.cost + cache'.cost + mks.cost +
      1679 + K * 39 + min K S.N_dh * 7786 := by
  simp only [finishAuthRecvMkC, bindV, letV, eCaseOpt, firstMsgADE_cost,
    a1_recvFinishTagRunC_cost_tight, ahsBase, parHstDec, parFinishTag, parKEntry,
    hdrIkAPk, pkmHdr, peIkAPk, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
    asRoCache, asRootRoCache, ahsfMk, ahsfMkSlots, emptyAuthSlotStE, assMk,
    cost_letC, cost_queryPrim, v, Comp.cost, Expr.cost, Ty.wd, PNat.val_ofNat, AuthPrf.bits_0]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  omega

private theorem a1_finishRecvUnmatchedMkPreC_cost_tight (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) (msg : Var Γ₂ AuthPrf.preKeyMsgTy)
    (prep : Var Γ₃ preparedAuthRecvTy) (drKey : Expr pqxdhOps Δ AuthPrf.drKeyTy) (rk1 : Expr pqxdhOps Δ (B 32))
    (spqrSalt? : Expr pqxdhOps Δ (.opt (B 32))) (rSlot rc' : Expr pqxdhOps Δ .nat)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (finishRecvUnmatchedMkPreC S K core msg prep drKey rk1 spqrSalt? rSlot rc').cost =
      drKey.cost + rk1.cost + spqrSalt?.cost + rSlot.cost + rc'.cost +
      2008 + K * 39 + min K S.N_dh * 7786 := by
  simp only [finishRecvUnmatchedMkPreC, bindV, letV, natEq, natLt, a1_finishAuthRecvMkC_cost_tight,
    mkcSecb, mkcIdx, mkcSentChal, mkcFhst, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    ahsfUpdSlots, ahsfMkSlots, mkcMk,
    cost_letC, cost_samplePrim, cost_queryPrim, PSamp.cost, Ty.wd, v,
    Comp.cost, Expr.cost, PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  omega

private theorem a1_authCkSendB_cost_tight_le (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (authCkSendB S K opk idx chalP fhst x : Comp pqxdhOps pqPrimIface Δ RSF).cost ≤
      19000 + K * 14000 + min K S.N_dh * 16000 := by
  cases opk <;>
  · simp only [authCkSendB, sampAtCkC, sampCkPairC, koskBundleOkC_cost, finishAuthHybridSendC_cost,
      hkdfRoC_cost, rootRoC_cost, a1_allocSendSlotE_cost, sidEq_cost, firstMsgADE_cost,
      buildSecretsE_cost, resolveSigPkC, checkBundleSpkHonIdealC, findHonestC, sendGuardE,
      cost_encEC, cost_encKEM, bindV, letV, caseOptV, findMV, anyMV, eFind, eAny, eCaseOpt,
      natEq, natLt, isSomeE, ahsfHybrid, ahsfRecvCount, ahsfSlots, ahsfMkSlots,
      ahsBase, asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asUsedSendSessions,
      asRoCache, asRootRoCache, peSecIKA0, peIkAPk, peIkSignPk, peCorrupted,
      sbSpkPk, sbPqspkPk, pkbIkB, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkB, pkbPqspkSig,
      aNone, cost_letC, cost_samplePrim, cost_queryPrim, cost_bytesLen, cost_bytesBeq,
      cost_boolOr, cost_litB, PSamp.cost, Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, List.length_nil, AuthPrf.bits_32, ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem a1_authCkRecvB_cost_tight_le (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (authCkRecvB S K opk idx chalP fhst x : Comp pqxdhOps pqPrimIface Δ RSF).cost ≤
      19000 + K * 14000 + min K S.N_dh * 16000 := by
  cases opk <;>
  · simp only [authCkRecvB, sampAtCkC, sampCkPairC, a1_recvFinishTagRunC_cost_tight,
      a1_prepareAuthHybridRecvC_true_cost_tight, a1_prepareAuthHybridRecvC_false_cost_tight,
      a1_finishAuthRecvCkC_cost_tight, a1_allocRecvSlotE_cost, hkdfRoC_cost, rootRoC_cost, firstMsgADE_cost,
      bindV, letV, caseOptV, eCaseOpt, natEq, natLt, isSomeE,
      ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots, ahsfMkSlots,
      ahsfUpd, ahsfUpdSlots, ahsBase,
      peIkAPk, hdrIkAPk, pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
      iasDrKey, iasRk1, iasMkSeed, iasCk1_1,
      parKEntry, parSecrets, parDhRatchet, parIsUncorrSender, parMatchedSess?, parSameEph,
      parHstDec, parFinishTag, aNone,
      cost_letC, cost_samplePrim, cost_queryPrim, cost_boolOr,
      PSamp.cost, Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, AuthPrf.bits_1]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem a1_authCkStepC_cost_tight_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (q : Var Γ₄ AuthPrf.authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (authCkStepC S K idx chalP fhst q : Comp pqxdhOps pqPrimIface Δ RSF).cost ≤
      19500 + K * 15000 + min K S.N_dh * 16000 := by
  unfold authCkStepC
  refine le_trans
    (caseSumV_cost_le _ _ _ (initPrinFixedB_cost_le K _ _) <|
     caseSumV_cost_le _ _ _ (corruptFixedB_cost_le K _ _) <|
     caseSumV_cost_le _ _ _ (genSpkFixedB_cost_le K _ _) <|
     caseSumV_cost_le _ _ _ (genOpkFixedB_cost_le K _ _) <|
     caseSumV_cost_le _ _ _ (a1_authCkSendB_cost_tight_le S K true _ _ _ _) <|
     caseSumV_cost_le _ _ _ (a1_authCkSendB_cost_tight_le S K false _ _ _ _) <|
     caseSumV_cost_le _ _ _ (a1_authCkRecvB_cost_tight_le S K true _ _ _ _) <|
     caseSumV_cost_le _ _ _ (a1_authCkRecvB_cost_tight_le S K false _ _ _ _) <|
     caseSumV_cost_le _ _ _ (roFixedB_cost_le K _ _) <|
     caseSumV_cost_le _ _ _ (roRootFixedB_cost_le K _ _) <|
     caseSumV_cost_le _ _ _ (by simp only [aNone, v, Comp.cost, Expr.cost]; exact le_rfl) <|
     registerFixedB_cost_le _ _)
    (by omega)

private theorem a1_prfCkHandleDsl_cost_tight_le (S : Setup) (K : Nat) :
    (prfCkHandleDsl S K).cost ≤ 20000 + K * 15000 + min K S.N_dh * 16000 := by
  unfold prfCkHandleDsl
  have h := a1_authCkStepC_cost_tight_le S K
    (Δ := authHybridStateFixedTy :: .prod (B 32) (B 32) :: .nat :: .bool ::
      prfCkStTy :: [prfCkStTy, AuthPrf.authQueryTy])
    (.zero : Var (.nat :: .bool :: prfCkStTy :: [prfCkStTy, AuthPrf.authQueryTy]) .nat)
    (.zero : Var (.prod (B 32) (B 32) :: .nat :: .bool :: prfCkStTy :: [prfCkStTy, AuthPrf.authQueryTy]) _)
    (.zero : Var (authHybridStateFixedTy :: .prod (B 32) (B 32) :: .nat :: .bool :: prfCkStTy ::
      [prfCkStTy, AuthPrf.authQueryTy]) _)
    (.succ .zero : Var [prfCkStTy, AuthPrf.authQueryTy] AuthPrf.authQueryTy)
  simp only [bindV, letV, ckSecb, ckIdx, ckChal, ckFhst, cost_letC, v, Comp.cost, Expr.cost]
  omega

private theorem a1_prfCkRedProg_totalCost_le_clamped (S : Setup) (K q : Nat) :
    (prfCkRedProg S K).totalCost q ≤
      71 + bits (min K S.N_sess_tot) +
      q * (20032 + K * 15000 + min K S.N_dh * 16000) +
      (114 + min K S.N_dh * 413 + (min K S.N_dh) ^ 2 * 1088 + K * 97 + K ^ 2 * 9511) := by
  simp only [CostedReduction.totalCost, prfCkRedProg, _root_.SignalPqxdh.LegacyCosted.authCodec,
    a1_prfCkInitDslK_cost_eq, a1_prfCkFinishDsl_cost_tight]
  have hH := a1_prfCkHandleDsl_cost_tight_le S K
  have hMax : max pqPrimIface.uCost ((prfCkHandleDsl S K).cost + 32) =
      (prfCkHandleDsl S K).cost + 32 := by
    change max 1 ((prfCkHandleDsl S K).cost + 32) = (prfCkHandleDsl S K).cost + 32
    omega
  rw [hMax]
  have hMul : q * ((prfCkHandleDsl S K).cost + 32) ≤
      q * (20032 + K * 15000 + min K S.N_dh * 16000) :=
    Nat.mul_le_mul_left q (by omega)
  omega

private theorem a1_wrapMkBase_cost_le {Γ₁ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) [Ext Γ₁ Δ] (m : Comp pqxdhOps pqPrimIface Δ RSF)
    {M : Nat} (hm : m.cost ≤ M) :
    (wrapMkBase core m).cost ≤ M + 30 := by
  simp only [wrapMkBase, bindV, mkcMk, mkcSecb, mkcIdx, mkcSentChal, v, Comp.cost, Expr.cost]
  omega

private theorem a1_authMkSendPreB_cost_le_clamped (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (authMkSendPreB S K opk core x : Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy).cost ≤
      15000 + K * 10000 + min K S.N_dh * 20000 := by
  cases opk <;>
  · simp only [authMkSendPreB, koskBundleOkC_cost, finishAuthHybridSendC_cost,
      a1_finishAuthSendMkC_cost_tight, hkdfRoC_cost, rootRoC_cost, a1_allocSendSlotE_cost, sidEq_cost,
      firstMsgADE_cost, buildSecretsE_cost, resolveSigPkC, checkBundleSpkHonIdealC, findHonestC,
      sendGuardE, cost_encEC, cost_encKEM, bindV, letV, caseOptV, findMV, anyMV, eFind, eAny,
      eCaseOpt, natEq, natLt, isSomeE, mkcSecb, mkcIdx, mkcSentChal, mkcFhst, mkcMk,
      ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots, ahsfMkSlots, ahsfUpd,
      ahsfUpdSlots, ahsBase,
      asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asUsedSendSessions,
      peSecIKA0, peIkAPk, peIkSignPk, peCorrupted,
      sbSpkPk, sbPqspkPk, pkbIkB, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkB, pkbPqspkSig,
      aNone, cost_letC, cost_samplePrim, cost_queryPrim, cost_bytesLen, cost_bytesBeq,
      cost_boolOr, cost_litB, PSamp.cost, Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, List.length_nil, AuthPrf.bits_32, ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem a1_authMkRecvPreB_cost_le_clamped (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (authMkRecvPreB S K opk core x : Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy).cost ≤
      15000 + K * 10000 + min K S.N_dh * 20000 := by
  cases opk <;>
  · simp only [authMkRecvPreB, a1_recvFinishTagRunC_cost_tight,
      a1_prepareAuthHybridRecvC_true_cost_tight, a1_prepareAuthHybridRecvC_false_cost_tight,
      a1_finishAuthRecvMkC_cost_tight, a1_finishRecvUnmatchedMkPreC_cost_tight, hkdfRoC_cost, rootRoC_cost,
      a1_allocRecvSlotE_cost, a1_lookupSendSlotE_cost, sidEq_cost, sameSaltKeyE_cost, firstMsgADE_cost,
      bindV, letV, caseOptV, eFind, eCaseOpt, natEq, natLt, isSomeE,
      mkcSecb, mkcIdx, mkcSentChal, mkcFhst, mkcMk,
      ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots, ahsfMkSlots, ahsfUpd,
      ahsfUpdSlots, ahsBase,
      peIkAPk, hdrIkAPk, pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
      iasSid, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys,
      parKEntry, parSecrets, parDhRatchet, parIsUncorrSender, parMatchedSess?, parSameEph,
      parHstDec, parFinishTag, aNone,
      cost_letC, cost_samplePrim, cost_queryPrim, cost_boolOr,
      PSamp.cost, Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, AuthPrf.bits_0, AuthPrf.bits_1]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem a1_prfMkStepPreC_cost_le_clamped (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) (q : Var Γ₂ AuthPrf.authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prfMkStepPreC S K core q : Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy).cost ≤
      16000 + K * 11000 + min K S.N_dh * 22000 := by
  unfold prfMkStepPreC
  refine le_trans
    (letV_cost_le _ _
      (caseSumV_cost_le _ _ _ (a1_wrapMkBase_cost_le _ _ (initPrinFixedB_cost_le K _ _)) <|
       caseSumV_cost_le _ _ _ (a1_wrapMkBase_cost_le _ _ (corruptFixedB_cost_le K _ _)) <|
       caseSumV_cost_le _ _ _ (a1_wrapMkBase_cost_le _ _ (genSpkFixedB_cost_le K _ _)) <|
       caseSumV_cost_le _ _ _ (a1_wrapMkBase_cost_le _ _ (genOpkFixedB_cost_le K _ _)) <|
       caseSumV_cost_le _ _ _ (a1_authMkSendPreB_cost_le_clamped S K true _ _) <|
       caseSumV_cost_le _ _ _ (a1_authMkSendPreB_cost_le_clamped S K false _ _) <|
       caseSumV_cost_le _ _ _ (a1_authMkRecvPreB_cost_le_clamped S K true _ _) <|
       caseSumV_cost_le _ _ _ (a1_authMkRecvPreB_cost_le_clamped S K false _ _) <|
       caseSumV_cost_le _ _ _ (a1_wrapMkBase_cost_le _ _ (roFixedB_cost_le K _ _)) <|
       caseSumV_cost_le _ _ _ (a1_wrapMkBase_cost_le _ _ (roRootFixedB_cost_le K _ _)) <|
       caseSumV_cost_le _ _ _ (by simp only [aNone, v, Comp.cost, Expr.cost]; exact le_rfl) <|
       a1_wrapMkBase_cost_le _ _ (registerFixedB_cost_le _ _)))
    ?_
  simp only [v, Expr.cost]
  omega

private theorem a1_prfMkStepPostC_cost_le_clamped (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (cont : Var Γ₁ prfMkChalContTy) (mk : Var Γ₂ msgKeysTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prfMkStepPostC S K cont mk : Comp pqxdhOps pqPrimIface Δ (.prod authRespTy prfMkCoreTy)).cost ≤
      3500 + K * 4000 + min K S.N_dh * 9000 := by
  simp only [prfMkStepPostC, a1_finishAuthSendMkC_cost_tight, a1_finishAuthRecvMkC_cost_tight,
    bindV, letV, caseSumV, eCaseOpt, mkcMk, ahsfUpdSlots, ahsfMkSlots,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, cost_letC, cost_litB,
    v, Comp.cost, Expr.cost, PNat.val_ofNat, List.length_nil]
  repeat' first
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

private theorem a1_prfMsgKeysHandleDsl_cost_le_clamped (S : Setup) (K : Nat) :
    (prfMsgKeysHandleDsl S K).cost ≤ 25000 + K * 20000 + min K S.N_dh * 35000 := by
  unfold prfMsgKeysHandleDsl
  have hPre := a1_prfMkStepPreC_cost_le_clamped S K
    (Δ := prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, AuthPrf.authQueryTy])
    (.zero : Var (prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, AuthPrf.authQueryTy]) prfMkCoreTy)
    (.succ .zero : Var [prfMkStTy, AuthPrf.authQueryTy] AuthPrf.authQueryTy)
  have hPost := a1_prfMkStepPostC_cost_le_clamped S K
    (Δ := msgKeysTy :: prfMkChalContTy :: .opt (B 32) :: (.prod (.opt (B 32)) prfMkChalContTy) ::
      prfMkStepPreTy :: prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, AuthPrf.authQueryTy])
    (.zero : Var (prfMkChalContTy :: .opt (B 32) :: (.prod (.opt (B 32)) prfMkChalContTy) ::
      prfMkStepPreTy :: prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, AuthPrf.authQueryTy]) prfMkChalContTy)
    (.zero : Var (msgKeysTy :: prfMkChalContTy :: .opt (B 32) :: (.prod (.opt (B 32)) prfMkChalContTy) ::
      prfMkStepPreTy :: prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, AuthPrf.authQueryTy]) msgKeysTy)
  simp only [bindV, letV, caseSumV, natEq, aNone,
    cost_liftPrimComp, cost_letC, cost_queryDeriveMk,
    v, Comp.cost, Expr.cost, AuthPrf.bits_0, AuthPrf.bits_1]
  omega

private theorem a1_prfMsgKeysRedProg_totalCost_le_clamped (S : Setup) (K q : Nat) :
    (prfMsgKeysRedProg S K).totalCost q ≤
      72 + bits (min K S.N_sess_tot) + bits (min K S.N_recv_tot + 1) +
      q * (25032 + K * 20000 + min K S.N_dh * 35000) +
      (118 + min K S.N_dh * 413 + (min K S.N_dh) ^ 2 * 1088 + K * 97 + K ^ 2 * 9511) := by
  simp only [CostedReduction.totalCost, prfMsgKeysRedProg, _root_.SignalPqxdh.LegacyCosted.authCodec,
    a1_prfMsgKeysInitDslK_cost_eq, a1_prfMsgKeysFinishDsl_cost_tight]
  have hH := a1_prfMsgKeysHandleDsl_cost_le_clamped S K
  have hMax : max pqPrfMkIface.uCost ((prfMsgKeysHandleDsl S K).cost + 32) =
      (prfMsgKeysHandleDsl S K).cost + 32 := by
    change max 1 ((prfMsgKeysHandleDsl S K).cost + 32) = (prfMsgKeysHandleDsl S K).cost + 32
    omega
  rw [hMax]
  have hMul : q * ((prfMsgKeysHandleDsl S K).cost + 32) ≤
      q * (25032 + K * 20000 + min K S.N_dh * 35000) :=
    Nat.mul_le_mul_left q (by omega)
  omega

end Auth1KeyPrfCost

end Proofs.SignalPqxdh.Security.PqxdhDelta.Auth1KeyCostHelpers

namespace Proofs.SignalPqxdh.Security.PqxdhDelta
open OracleSpec OracleComp
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.Costed
  (pqAuthPrimIface pqAuthSigAndDdhIface pqPrfMkIface pqPrfHmacIface authCodec)
open _root_.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security
open _root_.SignalPqxdh.Security.AuthSubHops1to3
open _root_.SignalPqxdh.Security.ReductionDsl
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
open Computational.Proofs.ReductionDsl.AtomicSizeHonest
open Computational.Proofs.SignalPqxdh.AtomicLift
open Auth1KeyCostHelpers

theorem prfCk1KeyAtomicProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (prfCk1KeyAtomicProg S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  refine a1_two_mul_clamped_le_stepCostBudget S b
    (le_trans (liftAuth1Stage_totalCost_two_mul_le tlAuthPrim rfl S
      (prfCkRedProg1Key S b.q_total) b.q_total) ?_)
  have hCost12 := prfCkRedProg1Key_totalCost_le S b.q_total b.q_total
  have hr64_12 := prfCkRedProg1Key_totalQueries_le S b.q_total
    (fun _ => 0) (sampR64W tlAuthPrim.hsmp) b.q_total
  have hr64 : (prfCkRedProg S b.q_total).totalQueries
      (fun _ => 0) (sampR64W tlAuthPrim.hsmp) b.q_total ≤ 4 * b.q_total :=
    prfCkRedProg_r64_le S b.q_total b.q_total
  have hPoly := a1_prfCkRedProg_totalCost_le_clamped S b.q_total b.q_total
  have hbSess : ReductionDsl.bits (min b.q_total S.N_sess_tot) ≤ min b.q_total S.N_sess_tot + 1 :=
    AuthAead.bits_le_succ _
  generalize (prfCkRedProg1Key S b.q_total).totalCost b.q_total = c1 at *
  generalize (prfCkRedProg S b.q_total).totalCost b.q_total = c2 at *
  generalize (prfCkRedProg1Key S b.q_total).totalQueries
    (fun _ => 0) (sampR64W tlAuthPrim.hsmp) b.q_total = qr1 at *
  generalize (prfCkRedProg S b.q_total).totalQueries
    (fun _ => 0) (sampR64W tlAuthPrim.hsmp) b.q_total = qr2 at *
  generalize ReductionDsl.bits (min b.q_total S.N_sess_tot) = bms at *
  generalize b.q_total = q at *
  generalize min q S.N_dh = md at *
  generalize min q S.N_sess_tot = ms at *
  generalize Nat.log 2 S.N_dh = ld at *
  generalize Nat.log 2 S.N_sess_tot = ls at *
  have hMulExp : q * (20032 + q * 15000 + md * 16000) =
      20032 * q + 15000 * (q * q) + 16000 * (q * md) := by ring
  have hFinExp : md ^ 2 * 1088 + q ^ 2 * 9511 =
      1088 * (md * md) + 9511 * (q * q) := by ring
  generalize 2048 * (q + 1) * (ld + ls) = ql at *
  generalize q * q = qq at *
  generalize q * md = qmd at *
  generalize q * ms = qms at *
  generalize md * md = md2 at *
  generalize md * ms = mdms at *
  omega

theorem prfMsgKeys1KeyAtomicProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (prfMsgKeys1KeyAtomicProg S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  refine a1_two_mul_clamped_le_stepCostBudget S b
    (le_trans (liftAuth1Stage_totalCost_two_mul_le tlPrfMk rfl S
      (prfMsgKeysRedProg1Key S b.q_total) b.q_total) ?_)
  have hCost12 := prfMsgKeysRedProg1Key_totalCost_le S b.q_total b.q_total
  have hr64_12 := prfMsgKeysRedProg1Key_totalQueries_le S b.q_total
    (fun _ => 0) (sampR64W tlPrfMk.hsmp) b.q_total
  have hr64 : (prfMsgKeysRedProg S b.q_total).totalQueries
      (fun _ => 0) (sampR64W tlPrfMk.hsmp) b.q_total ≤ 4 * b.q_total :=
    prfMsgKeysRedProg_r64_le S b.q_total b.q_total
  have hPoly := a1_prfMsgKeysRedProg_totalCost_le_clamped S b.q_total b.q_total
  have hRecvLe : min b.q_total S.N_recv_tot ≤ min b.q_total S.N_sess_tot := by
    unfold Setup.N_sess_tot; omega
  have hbSess : ReductionDsl.bits (min b.q_total S.N_sess_tot) ≤ min b.q_total S.N_sess_tot + 1 :=
    AuthAead.bits_le_succ _
  have hbRecv : ReductionDsl.bits (min b.q_total S.N_recv_tot + 1) ≤ min b.q_total S.N_sess_tot + 2 := by
    have h1 := AuthAead.bits_le_succ (min b.q_total S.N_recv_tot + 1)
    omega
  have hQMd : b.q_total * min b.q_total S.N_dh ≤ b.q_total * b.q_total :=
    Nat.mul_le_mul_left b.q_total (Nat.min_le_left b.q_total S.N_dh)
  generalize (prfMsgKeysRedProg1Key S b.q_total).totalCost b.q_total = c1 at *
  generalize (prfMsgKeysRedProg S b.q_total).totalCost b.q_total = c2 at *
  generalize (prfMsgKeysRedProg1Key S b.q_total).totalQueries
    (fun _ => 0) (sampR64W tlPrfMk.hsmp) b.q_total = qr1 at *
  generalize (prfMsgKeysRedProg S b.q_total).totalQueries
    (fun _ => 0) (sampR64W tlPrfMk.hsmp) b.q_total = qr2 at *
  generalize ReductionDsl.bits (min b.q_total S.N_sess_tot) = bms at *
  generalize ReductionDsl.bits (min b.q_total S.N_recv_tot + 1) = bmr at *
  generalize min b.q_total S.N_recv_tot = mr at *
  generalize b.q_total = q at *
  generalize min q S.N_dh = md at *
  generalize min q S.N_sess_tot = ms at *
  generalize Nat.log 2 S.N_dh = ld at *
  generalize Nat.log 2 S.N_sess_tot = ls at *
  have hMulExp : q * (25032 + q * 20000 + md * 35000) =
      25032 * q + 20000 * (q * q) + 35000 * (q * md) := by ring
  have hFinExp : md ^ 2 * 1088 + q ^ 2 * 9511 =
      1088 * (md * md) + 9511 * (q * q) := by ring
  generalize 2048 * (q + 1) * (ld + ls) = ql at *
  generalize q * q = qq at *
  generalize q * md = qmd at *
  generalize q * ms = qms at *
  generalize md * md = md2 at *
  generalize md * ms = mdms at *
  omega

theorem aeadCpa1KeyAtomicProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (aeadCpa1KeyAtomicProg S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  refine a1_two_mul_clamped_le_stepCostBudget S b
    (le_trans (liftAuth2Stage_totalCost_two_mul_le tlAuthPrim rfl S
      (aeadCpaRedProg1Key S b.q_total) b.q_total) ?_)
  have hCost12 := aeadCpaRedProg1Key_totalCost_le S b.q_total b.q_total
  have hr64_12 := aeadCpaRedProg1Key_totalQueries_le S b.q_total
    (fun _ => 0) (sampR64W tlAuthPrim.hsmp) b.q_total
  have hr64 : (aeadCpaRedProg S b.q_total).totalQueries
      (fun _ => 0) (sampR64W tlAuthPrim.hsmp) b.q_total ≤ 4 * b.q_total :=
    aeadCpaRedProg_r64_le S b.q_total b.q_total
  have hPoly := aeadCpaRedProg_totalCost_poly_le_clamped S b.q_total b.q_total
  have hSendLe : min b.q_total S.N_send_tot ≤ min b.q_total S.N_sess_tot := by
    unfold Setup.N_sess_tot; omega
  have hbSend : ReductionDsl.bits (min b.q_total S.N_send_tot) ≤ min b.q_total S.N_sess_tot + 1 :=
    (AuthAead.bits_le_succ _).trans (Nat.add_le_add_right hSendLe 1)
  generalize (aeadCpaRedProg1Key S b.q_total).totalCost b.q_total = c1 at *
  generalize (aeadCpaRedProg S b.q_total).totalCost b.q_total = c2 at *
  generalize (aeadCpaRedProg1Key S b.q_total).totalQueries
    (fun _ => 0) (sampR64W tlAuthPrim.hsmp) b.q_total = qr1 at *
  generalize (aeadCpaRedProg S b.q_total).totalQueries
    (fun _ => 0) (sampR64W tlAuthPrim.hsmp) b.q_total = qr2 at *
  generalize ReductionDsl.bits (min b.q_total S.N_send_tot) = bmsd at *
  generalize min b.q_total S.N_send_tot = msd at *
  generalize b.q_total = q at *
  generalize min q S.N_dh = md at *
  generalize min q S.N_sess_tot = ms at *
  generalize Nat.log 2 S.N_dh = ld at *
  generalize Nat.log 2 S.N_sess_tot = ls at *
  have hMulExp : q * (12032 + q * 5000 + md * 1550 + ms * 7500) =
      12032 * q + 5000 * (q * q) + 1550 * (q * md) + 7500 * (q * ms) := by ring
  have hFinExp : md ^ 2 * 1088 + q ^ 2 * 9511 =
      1088 * (md * md) + 9511 * (q * q) := by ring
  generalize 2048 * (q + 1) * (ld + ls) = ql at *
  generalize q * q = qq at *
  generalize q * md = qmd at *
  generalize q * ms = qms at *
  generalize md * md = md2 at *
  generalize md * ms = mdms at *
  omega

end Proofs.SignalPqxdh.Security.PqxdhDelta

namespace Proofs.SignalPqxdh.Security.PqxdhDelta.Auth1KeyCostHelpers

section Auth1KeyHmCost
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh _root_.SignalPqxdh.LegacyCosted _root_.SignalPqxdh.Security
open _root_.SignalPqxdh.Security.ReductionDsl hiding sessionIdTy msgKeysTy authRespTy
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
open OracleSpec OracleComp

attribute [local simp] Expr.cost Comp.cost

private theorem a1_muKeyIdEq_cost {Γ : List PT} (a b : Expr pqxdhOps Γ muKeyIdTy) :
    (muKeyIdEq a b).cost = a.cost + b.cost + 55 := by
  simp only [muKeyIdEq, eLet2, eLet, eCaseSum, sidEq_cost, natEq, v, Expr.cost]
  omega

private theorem a1_initKeyIdE_cost (S : Setup) {Γ : List PT}
    (sid : Expr pqxdhOps Γ sessionIdTy) :
    (initKeyIdE S sid).cost = sid.cost + 7 := by
  simp only [initKeyIdE, eCaseSum, v, Expr.cost, AuthPrf.bits_0]
  omega

private theorem a1_hmKeyIdC_cost (K : Nat) {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod muKeyIdTy muStTy)) :
    (hmKeyIdC K a).cost = a.cost + 127 + K * 59 := by
  simp only [hmKeyIdC, letV, caseOptV, bindV, eFind, a1_muKeyIdEq_cost, muKeys, muChal, muPend, muBad,
    muMk, cost_letC, cost_samplePrim, PSamp.cost, PSamp.ty, Ty.wd, v, Comp.cost, Expr.cost,
    PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

private theorem a1_hmEncPreIdC_cost (K : Nat) {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod .nat (.prod muKeyIdTy (.prod (B 158) (.prod (B 32) muStTy))))) :
    (hmEncPreIdC K a).cost = a.cost + 1968 + K * 1700 := by
  simp only [hmEncPreIdC, letV, caseOptV, bindV, eFind, a1_muKeyIdEq_cost, natEq, natLt,
    a1_hmKeyIdC_cost, encPostC_cost, muKeys, muChal, muPend, muBad, muMk,
    cost_letC, cost_samplePrim, cost_queryPrim, cost_widenB_32,
    PSamp.cost, PSamp.ty, Ty.wd, v, Comp.cost, Expr.cost, PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  omega

private theorem a1_hmForgeIdC_cost (K : Nat) {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod .nat (.prod muKeyIdTy (.prod (B 158) (.prod (B 32) muStTy))))) :
    (hmForgeIdC K a).cost = a.cost + 3855 + K * 177 := by
  simp only [hmForgeIdC, letV, bindV, eCaseOpt, eFind, a1_muKeyIdEq_cost, cost_natLe, isSomeE,
    a1_hmKeyIdC_cost, macInputE_cost, etmBodyE_cost, etmTagE_cost,
    muKeys, muChal, muPend, muBad, muMk,
    cost_letC, cost_queryPrim, cost_bytesBeq, cost_bytesLen, cost_boolOr,
    Ty.wd, v, Comp.cost, Expr.cost, PNat.val_ofNat, bits_24, AuthPrf.bits_32]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  omega

private theorem a1_intSendPrepC_cost_le (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (intSendPrepC S K opk fhst x : Comp pqxdhOps pqPrimIface Δ (.opt intPrepTy)).cost ≤
      10500 + K * 4100 + min K S.N_dh * 1540 := by
  cases opk <;>
  · simp only [intSendPrepC,
      koskBundleOkC_cost, spkHonIdealFromPeerC_cost, checkBundleProvenanceExactC_cost,
      hkdfRoC_cost, rootRoC_cost, firstMsgADE_cost, buildSecretsE_cost, sidEq_cost,
      findHonestC, getDBytes, optSnd,
      bindV, letV, caseOptV, findMV, eFind, eAny, eCaseOpt,
      natEq, isSomeE,
      ahsfHybrid, ahsBase, asSecb, asPrincipals, asUsedSendSessions, asRoCache, asRootRoCache,
      peSecIKA0, peIkAPk, peIkSignPk, peCorrupted,
      pkbIkB, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkB, pkbPqspkSig,
      cost_encEC, cost_encKEM, cost_letC, cost_samplePrim, cost_queryPrim,
      cost_bytesLen, cost_bytesBeq, cost_boolOr, cost_litB,
      PSamp.cost, PSamp.ty, Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, List.length_nil, AuthPrf.bits_32, ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem a1_hmSendTailC_cost_le (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy) (mst : Var Γ₃ muStTy)
    (x : Var Γ₄ sendQTy) (p : Var Γ₅ intPrepTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] :
    (hmSendTailC S K opk jt fhst mst x p : Comp pqxdhOps pqPrimIface Δ hmPreTy).cost ≤
      3500 + K * 1750 := by
  cases opk <;>
  · simp only [hmSendTailC, sendSidE,
      a1_hmEncPreIdC_cost, finishIntC_cost, a1_initKeyIdE_cost,
      getDBytes, defaultMsgKeysE,
      defaultMsgKeys_cipherKey_length, defaultMsgKeys_macKey_length, defaultMsgKeys_iv_length,
      ipAd, ipMsgPlain, ipIdeal, ipRks4, ipSalt, ipT3, ipFim,
      bindV, letV, caseSumV, eCaseOpt,
      cost_letC, cost_queryPrim, cost_litB,
      Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, List.length_nil, ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem a1_hmSendC_cost_le (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy) (mst : Var Γ₃ muStTy)
    (x : Var Γ₄ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (hmSendC S K opk jt fhst mst x : Comp pqxdhOps pqPrimIface Δ hmPreTy).cost ≤
      14100 + K * 5850 + min K S.N_dh * 1540 := by
  unfold hmSendC
  have hPrep := a1_intSendPrepC_cost_le S K opk (Δ := Δ) fhst x
  have hTail := a1_hmSendTailC_cost_le S K opk (Δ := intPrepTy :: .opt intPrepTy :: Δ)
    jt fhst mst x (.zero : Var (intPrepTy :: .opt intPrepTy :: Δ) intPrepTy)
  cases opk <;>
  · simp only [sendGuardE, isSomeE, pkbOpkB?, aNone, bindV, caseOptV,
      v, Comp.cost, Expr.cost, ite_true, ite_false, Bool.false_eq_true]
    omega

private theorem a1_hmRecvPrepC_cost_le (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (hmRecvPrepC S K opk fhst x : Comp pqxdhOps pqPrimIface Δ (.opt hmRecvDataTy)).cost ≤
      7000 + K * 300 + min K S.N_dh * 420 := by
  cases opk <;>
  · simp only [hmRecvPrepC,
      koskSenderOkC_cost, optU32Eq_cost, kyberCheckE_cost, buildSecretsE_cost,
      findHonestC, bindV, letV, caseOptV, caseSumV, findMV, eFind, eAny, eCaseOpt,
      natEq, nat2Eq, nat3Eq, isSomeE,
      ahsfHybrid, ahsBase, ahsRecvKemRecs, ahsMk, ahsUpd, ahsInitKemRecs, ahsIdealSessions,
      asPrincipals, asSpkBundles, asOpkEntries, asUsedRecvOPK, asUsedRecvNoOPK,
      asUsedKyberTriples, peSecIKA0, peIkAPk, sbSpkSk, sbPqspkSk, sbPqspkPk,
      oeOpkSk, oeOpkPk, oeConsumed, rkrMk,
      hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt, pkmHdr, pkmEphAPk,
      cost_u32OfNat, cost_u32Beq, cost_letC, cost_queryPrim,
      cost_bytesLen, cost_bytesBeq, cost_boolOr,
      Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, AuthPrf.bits_32, ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem a1_hmSchedPrepC_cost_le (S : Setup) (K : Nat) {Δ : List PT}
    (a : Expr pqxdhOps Δ schedPrepArgsTy) :
    (hmSchedPrepC S K a).cost ≤
      a.cost + 1500 + K * 600 + min K S.N_dh * 210 + min K S.N_sess_tot * 7350 := by
  simp only [hmSchedPrepC,
    matchIdealAuthHandshakeC_cost, hkdfRoC_cost, rootRoC_cost, findHonestC, iasCk1_0E,
    bindV, letV, caseOptV, findMV, eCaseOpt, isSomeE,
    ahsBase, ahsIdealSessions, asPrincipals, asRoCache, asRootRoCache,
    peIkAPk, peCorrupted, sbSpkSk, sbSpkPk, sbPqspkPk,
    hdrIkAPk, pkmHdr, pkmEphAPk, pkmPqRatchetMsg,
    iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasEphAPk,
    cost_letC, cost_samplePrim, cost_queryPrim, cost_bytesBeq, cost_boolOr,
    PSamp.cost, PSamp.ty, Ty.wd, v, Comp.cost, Expr.cost, PNat.val_ofNat]
  repeat' first
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

private theorem a1_hmSchedFinC_cost_le (S : Setup) (K : Nat) {Δ : List PT}
    (a : Expr pqxdhOps Δ schedFinArgsTy) :
    (hmSchedFinC S K a).cost ≤
      a.cost + 6500 + K * 900 := by
  simp only [hmSchedFinC, forgeRetIdC,
    a1_hmForgeIdC_cost, a1_initKeyIdE_cost, firstMsgADE_cost, sidEq_cost, sameSaltKeyE_cost,
    iasAdE, iasAeadCtE, iasMsgPlainE,
    defaultMsgKeysE, defaultMsgKeys_cipherKey_length, defaultMsgKeys_macKey_length,
    defaultMsgKeys_iv_length,
    bindV, letV, caseOptV, eFind, eCaseOpt,
    peIkAPk, hdrIkAPk, pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
    iasSid, iasSpqrSalt?,
    cost_letC, cost_queryPrim, cost_bytesBeq, cost_litB,
    Ty.wd, v, Comp.cost, Expr.cost, PNat.val_ofNat]
  repeat' first
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

private theorem a1_hmSchedC_cost_le (S : Setup) (K : Nat) {Δ : List PT}
    (a : Expr pqxdhOps Δ schedArgsTy) :
    (hmSchedC S K a).cost ≤
      a.cost + 8100 + K * 1500 + min K S.N_dh * 210 + min K S.N_sess_tot * 7350 := by
  unfold hmSchedC
  refine le_trans
    (letV_cost_le _ _ <| letV_cost_le _ _ <| letV_cost_le _ _ <|
     letV_cost_le _ _ <| letV_cost_le _ _ <| letV_cost_le _ _ <|
     bindV_cost_le _ _ (a1_hmSchedPrepC_cost_le S K _) <|
     caseOptV_cost_le _ _ _
       (by simp only [v, Comp.cost, Expr.cost]; exact le_rfl)
       (a1_hmSchedFinC_cost_le S K _))
    ?_
  simp only [v, Expr.cost]
  omega

private theorem a1_hmRecvTailC_cost_le (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy) (mst : Var Γ₃ muStTy)
    (x : Var Γ₄ recvQTy) (d : Var Γ₅ hmRecvDataTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] :
    (hmRecvTailC S K opk jt fhst mst x d : Comp pqxdhOps pqPrimIface Δ hmResTy).cost ≤
      9000 + K * 1650 + min K S.N_dh * 210 + min K S.N_sess_tot * 7350 := by
  unfold hmRecvTailC
  refine le_trans
    (letV_cost_le _ _ <| letV_cost_le _ _ <| letV_cost_le _ _ <|
     letV_cost_le _ _ <| letV_cost_le _ _ <| letV_cost_le _ _ <|
     letV_cost_le _ _ <| letV_cost_le _ _ <| letV_cost_le _ _ <|
     bindV_cost_le (N := 500 + K * 40) _ _ (a1_hmSchedC_cost_le S K _) ?_)
    ?_
  · cases opk <;>
    · simp only [finErasedE, letV, eMap, eCaseOpt, natEq, nat2Eq, nat3Eq,
        ahsfRecvCount, ahsfMk, ahsfMkSlots, emptyAuthSlotStE, assMk,
        ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsMk, ahsUpd,
        asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
        asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK,
        asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
        asAdvKeys, stMk, stUpd, oeOpkSk, oeOpkPk, oeMk, oeUpd,
        aNone, aRecvHonest, aRecvUnfresh,
        cost_letC, v, Comp.cost, Expr.cost, AuthPrf.bits_0, AuthPrf.bits_1,
        ite_true, ite_false, Bool.false_eq_true]
      repeat' first
        | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
        | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
      omega
  · simp only [ahsfRecvCount, ahsfMkSaltCache, v, Expr.cost]
    omega

private theorem a1_hmRecvC_cost_le (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy) (mst : Var Γ₃ muStTy)
    (x : Var Γ₄ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (hmRecvC S K opk jt fhst mst x : Comp pqxdhOps pqPrimIface Δ hmPreTy).cost ≤
      16200 + K * 2000 + min K S.N_dh * 630 + min K S.N_sess_tot * 7350 := by
  unfold hmRecvC
  refine le_trans
    (bindV_cost_le _ _ (a1_hmRecvPrepC_cost_le S K opk fhst x) <|
     caseOptV_cost_le _ _ _
       (by simp only [aNone, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache,
         v, Comp.cost, Expr.cost, AuthPrf.bits_1]; exact le_rfl)
       (bindV_cost_le _ _ (a1_hmRecvTailC_cost_le S K opk jt fhst mst x .zero)
         (by simp only [v, Comp.cost, Expr.cost]; exact le_rfl)))
    (by simp only [v, Expr.cost]; omega)

private theorem a1_hmOther_cost_le {Γ₁ Δ : List PT} (mst : Var Γ₁ muStTy) [Ext Γ₁ Δ]
    (m : Comp pqxdhOps pqPrimIface Δ RSF) {M : Nat} (hm : m.cost ≤ M) :
    (hmOther mst m).cost ≤ M + 10 := by
  simp only [hmOther, bindV, v, Comp.cost, Expr.cost]
  omega

private theorem a1_hmDispatchC_cost_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy) (mst : Var Γ₃ muStTy)
    (q : Var Γ₄ AuthPrf.authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (hmDispatchC S K jt fhst mst q : Comp pqxdhOps pqPrimIface Δ hmPreTy).cost ≤
      16250 + K * 5900 + min K S.N_dh * 1550 + min K S.N_sess_tot * 7350 := by
  unfold hmDispatchC
  refine le_trans
    (caseSumV_cost_le _ _ _ (a1_hmOther_cost_le _ _ (initPrinFixedB_cost_le K _ _)) <|
     caseSumV_cost_le _ _ _ (a1_hmOther_cost_le _ _ (corruptFixedB_cost_le K _ _)) <|
     caseSumV_cost_le _ _ _ (a1_hmOther_cost_le _ _ (genSpkFixedB_cost_le K _ _)) <|
     caseSumV_cost_le _ _ _ (a1_hmOther_cost_le _ _ (genOpkFixedB_cost_le K _ _)) <|
     caseSumV_cost_le _ _ _ (a1_hmSendC_cost_le S K true _ _ _ _) <|
     caseSumV_cost_le _ _ _ (a1_hmSendC_cost_le S K false _ _ _ _) <|
     caseSumV_cost_le _ _ _ (a1_hmRecvC_cost_le S K true _ _ _ _) <|
     caseSumV_cost_le _ _ _ (a1_hmRecvC_cost_le S K false _ _ _ _) <|
     caseSumV_cost_le _ _ _ (a1_hmOther_cost_le _ _ (roFixedB_cost_le K _ _)) <|
     caseSumV_cost_le _ _ _ (a1_hmOther_cost_le _ _ (roRootFixedB_cost_le K _ _)) <|
     caseSumV_cost_le _ _ _ (by simp only [aNone, v, Comp.cost, Expr.cost]; exact le_rfl) <|
     a1_hmOther_cost_le _ _ (registerFixedB_cost_le _ _))
    (by omega)

private theorem a1_hmPreC_cost_le (S : Setup) (K : Nat) :
    (hmPreC S K).cost ≤
      16300 + K * 5900 + min K S.N_dh * 1550 + min K S.N_sess_tot * 7350 := by
  unfold hmPreC
  refine le_trans
    (letV_cost_le _ _ <| letV_cost_le _ _ <| letV_cost_le _ _ <| letV_cost_le _ _ <|
     a1_hmDispatchC_cost_le S K _ _ _ _)
    (by simp only [v, Expr.cost]; omega)

private theorem a1_hm_handle_cost_clamped_le (S : Setup) (K : Nat) :
    (prfHmacRedProg S K).handle.cost ≤
      24000 + K * 7500 + min K S.N_dh * 1550 + min K S.N_sess_tot * 7350 := by
  dsimp only [prfHmacRedProg, LegacyCosted.authCodec]
  unfold hmHandleC
  have hPre := a1_hmPreC_cost_le S K
  simp only [bindV, letV, caseSumV, hmContX0E_cost, hmPostC_cost,
    cost_liftPrimComp, cost_queryHmacEval, cost_letC, v, Comp.cost, Expr.cost]
  repeat' first
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

end Auth1KeyHmCost

end Proofs.SignalPqxdh.Security.PqxdhDelta.Auth1KeyCostHelpers

namespace Proofs.SignalPqxdh.Security.PqxdhDelta
open OracleSpec OracleComp
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.Costed
  (pqAuthPrimIface pqAuthSigAndDdhIface pqPrfMkIface pqPrfHmacIface authCodec)
open _root_.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security
open _root_.SignalPqxdh.Security.AuthSubHops1to3
open _root_.SignalPqxdh.Security.ReductionDsl
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
open Computational.Proofs.ReductionDsl.AtomicSizeHonest
open Computational.Proofs.SignalPqxdh.AtomicLift
open Auth1KeyCostHelpers

theorem prfHmac1KeyAtomicProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (prfHmac1KeyAtomicProg S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  refine a1_eleven_mul_clamped_le_stepCostBudget S b
    (le_trans (liftAuth1Stage_totalCost_eleven_mul_le tlPrfHmac rfl S
      (prfHmacRedProg1Key S b.q_total) b.q_total) ?_)
  have hCost12 := prfHmacRedProg1Key_totalCost_le S b.q_total b.q_total
  have hU : LegacyCosted.pqPrfHmacIface.uCost = 1 := rfl
  have hC : (LegacyCosted.authCodec S).codecCost = 32 := rfl
  have hTot : (prfHmacRedProg S b.q_total).totalCost b.q_total =
      (prfHmacRedProg S b.q_total).init.cost +
      b.q_total * max 1 ((prfHmacRedProg S b.q_total).handle.cost + 32) +
      (prfHmacRedProg S b.q_total).finish.cost := by
    simp only [CostedReduction.totalCost, hU, hC]
  rw [hTot, AuthPrfHmac.hm_init_cost, AuthPrfHmac.hm_finish_cost] at hCost12
  have hHdl := a1_hm_handle_cost_clamped_le S b.q_total
  have hbSess : ReductionDsl.bits (S.N_send_tot + S.N_recv_tot) ≤ Nat.log 2 S.N_sess_tot + 1 := by
    have hs : S.N_send_tot + S.N_recv_tot = S.N_sess_tot := rfl
    rw [hs]; exact le_rfl
  generalize (prfHmacRedProg1Key S b.q_total).totalCost b.q_total = c1 at *
  generalize (prfHmacRedProg S b.q_total).handle.cost = cHdl at *
  generalize ReductionDsl.bits (S.N_send_tot + S.N_recv_tot) = bss at *
  generalize b.q_total = q at *
  generalize min q S.N_dh = md at *
  generalize min q S.N_sess_tot = ms at *
  generalize Nat.log 2 S.N_dh = ld at *
  generalize Nat.log 2 S.N_sess_tot = ls at *
  have hMax : max 1 (cHdl + 32) ≤ 24032 + q * 7500 + md * 1550 + ms * 7350 := by omega
  have hMul : q * max 1 (cHdl + 32) ≤
      24032 * q + 7500 * (q * q) + 1550 * (q * md) + 7350 * (q * ms) := by
    calc q * max 1 (cHdl + 32)
        ≤ q * (24032 + q * 7500 + md * 1550 + ms * 7350) := Nat.mul_le_mul_left q hMax
      _ = 24032 * q + 7500 * (q * q) + 1550 * (q * md) + 7350 * (q * ms) := by ring
  have hFinExp : q ^ 2 * 1575 = 1575 * (q * q) := by ring
  have hLog : 23 * ls ≤ 11264 * (q + 1) * (ld + ls) := by
    have := a1_log11_le_budget 23 q ld ls (by omega)
    have hls : 23 * ls ≤ (23 * (q + 1)) * ls := Nat.mul_le_mul_right ls (by omega)
    omega
  generalize 11264 * (q + 1) * (ld + ls) = ql at *
  generalize q * q = qq at *
  generalize q * md = qmd at *
  generalize q * ms = qms at *
  generalize md * md = md2 at *
  generalize md * ms = mdms at *
  omega

private theorem sigAuth1KeyAtomicProg_eval_eq (S : Setup) (b : QueryBudget)
    (adv : Unit → OracleComp (unifSpec + authSpec S) Bool) (pk : Bytes) :
    (sigAuth1KeyAtomicProg S b).eval adv pk = (sigAuth1KeyDslProg S b).eval adv pk := by
  have h := liftAuth1Stage_eval tlAuthSigDdh S (fun _ => rfl) (sigAuth1KeyDslProg S b) adv pk
  have hId : embedVal (.prod (SignalPqxdh.LegacyCosted.B 1569) (SignalPqxdh.LegacyCosted.B 64)) =
      id := by
    funext ⟨x, y⟩; rfl
  rw [hId, id_map] at h
  exact h

private theorem fgAuth1KeyGapDhAtomicProg_eval_eq (S : Setup) (b : QueryBudget)
    (adv : Unit → OracleComp (unifSpec + authSpec S) Bool) (U V : Bytes) :
    (fgAuth1KeyGapDhAtomicProg S b).eval adv (U, V) =
      (fgAuth1KeyGapDhProg S b.q_total).eval adv (U, V) := by
  have h := liftAuth1Stage_eval tlAuthSigDdh S (fun _ => rfl)
    (fgAuth1KeyGapDhProg S b.q_total) adv (U, V)
  have hId : embedVal (SignalPqxdh.LegacyCosted.B 32) = id := rfl
  rw [hId, id_map] at h
  exact h

private theorem prfCk1KeyAtomicProg_eval_eq (S : Setup) (b : QueryBudget)
    (adv : Unit → OracleComp (unifSpec + authSpec S) Bool) (mkSeed ck1 : Bytes) :
    (prfCk1KeyAtomicProg S b).eval adv (mkSeed, ck1) =
      (prfCkRedProg1Key S b.q_total).eval adv (mkSeed, ck1) := by
  have h := liftAuth1Stage_eval tlAuthPrim S (fun _ => rfl)
    (prfCkRedProg1Key S b.q_total) adv (mkSeed, ck1)
  have hId : embedVal .bool = id := rfl
  rw [hId, id_map] at h
  exact h

private theorem prfMsgKeys1KeyAtomicProg_eval_eq (S : Setup) (b : QueryBudget)
    (adv : Unit → OracleComp (unifSpec + authSpec S) Bool) :
    (prfMsgKeys1KeyAtomicProg S b).eval adv () =
      (prfMsgKeysRedProg1Key S b.q_total).eval adv () := by
  have h := liftAuth1Stage_eval tlPrfMk S (fun _ => rfl)
    (prfMsgKeysRedProg1Key S b.q_total) adv ()
  have hId : embedVal .bool = id := rfl
  rw [hId, id_map] at h
  exact h

private theorem prfHmac1KeyAtomicProg_eval_eq (S : Setup) (b : QueryBudget)
    (adv : Unit → OracleComp (unifSpec + authSpec S) Bool) :
    (prfHmac1KeyAtomicProg S b).eval adv () =
      (prfHmacRedProg1Key S b.q_total).eval adv () := by
  have h := liftAuth1Stage_eval tlPrfHmac S (fun _ => rfl)
    (prfHmacRedProg1Key S b.q_total) adv ()
  have hId : embedVal .bool = id := rfl
  rw [hId, id_map] at h
  exact h

private theorem a1_size_le_budget {sz : ℕ} (S : Setup) (b : QueryBudget)
    (hSz : sz ≤ 2 ^ 24 + 2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b)) :
    sz ≤ _root_.ReductionDsl.reductionSizeBudget +
      2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hB : _root_.ReductionDsl.reductionSizeBudget = 2 ^ 24 := rfl
  rwa [hB]

private theorem a1_bits_mono {x y : ℕ} (h : x ≤ y) :
    _root_.ReductionDsl.bits x ≤ _root_.ReductionDsl.bits y := by
  unfold _root_.ReductionDsl.bits
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

private theorem a1_bits_params_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    _root_.ReductionDsl.bits b.q_total ≤
      _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) ∧
    _root_.ReductionDsl.bits (min b.q_total S.N_dh) ≤
      _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) ∧
    _root_.ReductionDsl.bits (min b.q_total S.N_sess_tot) ≤
      _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) ∧
    _root_.ReductionDsl.bits (min b.q_total S.N_send_tot) ≤
      _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hq1 : b.q_total + 1 ≤ _root_.SignalPqxdh.Security.stepCostBudget S b := by
    unfold _root_.SignalPqxdh.Security.stepCostBudget
    dsimp only
    have hpos : 0 < b.q_total + 1 := Nat.succ_pos b.q_total
    have hmul : 2 ^ 16 * (b.q_total + 1) ≤ 2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) :=
      Nat.le_mul_of_pos_right _ hpos
    omega
  have hq : b.q_total ≤ _root_.SignalPqxdh.Security.stepCostBudget S b := by omega
  exact ⟨a1_bits_mono hq,
    a1_bits_mono ((Nat.min_le_left _ _).trans hq),
    a1_bits_mono ((Nat.min_le_left _ _).trans hq),
    a1_bits_mono ((Nat.min_le_left _ _).trans hq)⟩

theorem sigAuth1KeyAtomicProg_size_le_budget (S : Setup) (b : QueryBudget) :
    (sigAuth1KeyAtomicProg S b).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hL := liftAuth1Stage_size_le tlAuthSigDdh tlAuthSigDdh_sizeLe S (sigAuth1KeyDslProg S b)
  have hLit : red1LitSize (sigAuth1KeyDslProg S b) ≤ 22000 := sigAuth1KeyProg_litSize_le S b.q_total
  have hP := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sigAuth1KeyDslProg_size_le_stepCostBudget S b
  exact a1_size_le_budget S b
    (by change (liftAuth1Stage tlAuthSigDdh S (sigAuth1KeyDslProg S b)).size ≤ _; omega)

theorem shcrAuth1KeyAtomicProg_size_le_budget (S : Setup) (b : QueryBudget) :
    (shcrAuth1KeyAtomicProg S b).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hL := liftAuth2Stage_size_le tlAuthPrim tlAuthPrim_sizeLe S
    (shcrReductionAuthProg1Key S b.q_total b.q_total)
  have hLit : red2LitSize (shcrReductionAuthProg1Key S b.q_total b.q_total) ≤ 20000 :=
    (shcrReductionAuthProg1Key_litSize_le S b.q_total b.q_total).trans
      (_root_.Proofs.SignalPqxdh.Security.ah_shcrReductionAuthProg_litSize_le S b.q_total b.q_total)
  have h1 := shcrReductionAuthProg1Key_size_le S b.q_total b.q_total
  have hP := ah_shcrReductionAuthProg_size_le_clamped S b.q_total b.q_total
  have hq := (a1_bits_params_le_stepCostBudget S b).1
  exact a1_size_le_budget S b
    (by change (liftAuth2Stage tlAuthPrim S (shcrReductionAuthProg1Key S b.q_total b.q_total)).size ≤ _; omega)

theorem fgAuth1KeyGapDhAtomicProg_size_le_budget (S : Setup) (b : QueryBudget) :
    (fgAuth1KeyGapDhAtomicProg S b).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hL := liftAuth1Stage_size_le tlAuthSigDdh tlAuthSigDdh_sizeLe S (fgAuth1KeyGapDhProg S b.q_total)
  have hLit : red1LitSize (fgAuth1KeyGapDhProg S b.q_total) ≤ 22000 :=
    fgAuth1KeyGapDhProg_litSize_le S b.q_total
  have hP := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.fgAuth1KeyGapDhProg_size_le_stepCostBudget S b
  exact a1_size_le_budget S b
    (by change (liftAuth1Stage tlAuthSigDdh S (fgAuth1KeyGapDhProg S b.q_total)).size ≤ _; omega)

theorem prfCk1KeyAtomicProg_size_le_budget (S : Setup) (b : QueryBudget) :
    (prfCk1KeyAtomicProg S b).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hL := liftAuth1Stage_size_le tlAuthPrim tlAuthPrim_sizeLe S (prfCkRedProg1Key S b.q_total)
  have hLit : red1LitSize (prfCkRedProg1Key S b.q_total) ≤ 20000 :=
    (prfCkRedProg1Key_litSize_le S b.q_total).trans
      (_root_.Proofs.SignalPqxdh.Security.ap_prfCkRedProg_litSize_le S b.q_total)
  have h1 := prfCkRedProg1Key_size_le S b.q_total
  have hP := ap_prfCkRedProg_size_le_clamped S b.q_total
  have hq := (a1_bits_params_le_stepCostBudget S b).1
  exact a1_size_le_budget S b
    (by change (liftAuth1Stage tlAuthPrim S (prfCkRedProg1Key S b.q_total)).size ≤ _; omega)

theorem prfMsgKeys1KeyAtomicProg_size_le_budget (S : Setup) (b : QueryBudget) :
    (prfMsgKeys1KeyAtomicProg S b).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hL := liftAuth1Stage_size_le tlPrfMk tlPrfMk_sizeLe S (prfMsgKeysRedProg1Key S b.q_total)
  have hLit : red1LitSize (prfMsgKeysRedProg1Key S b.q_total) ≤ 20000 :=
    (prfMsgKeysRedProg1Key_litSize_le S b.q_total).trans
      (_root_.Proofs.SignalPqxdh.Security.ap_prfMsgKeysRedProg_litSize_le S b.q_total)
  have h1 := prfMsgKeysRedProg1Key_size_le S b.q_total
  have hP := ap_prfMsgKeysRedProg_size_le_clamped S b.q_total
  have hq := (a1_bits_params_le_stepCostBudget S b).1
  exact a1_size_le_budget S b
    (by change (liftAuth1Stage tlPrfMk S (prfMsgKeysRedProg1Key S b.q_total)).size ≤ _; omega)

theorem aeadCpa1KeyAtomicProg_size_le_budget (S : Setup) (b : QueryBudget) :
    (aeadCpa1KeyAtomicProg S b).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hL := liftAuth2Stage_size_le tlAuthPrim tlAuthPrim_sizeLe S (aeadCpaRedProg1Key S b.q_total)
  have hLit : red2LitSize (aeadCpaRedProg1Key S b.q_total) ≤ 20000 :=
    (aeadCpaRedProg1Key_litSize_le S b.q_total).trans
      (_root_.Proofs.SignalPqxdh.Security.ap_aeadCpaRedProg_litSize_le S b.q_total)
  have h1 := aeadCpaRedProg1Key_size_le S b.q_total
  have hP := ap_aeadCpaRedProg_size_le_clamped S b.q_total
  have hq := (a1_bits_params_le_stepCostBudget S b).1
  exact a1_size_le_budget S b
    (by change (liftAuth2Stage tlAuthPrim S (aeadCpaRedProg1Key S b.q_total)).size ≤ _; omega)

theorem prfHmac1KeyAtomicProg_size_le_budget (S : Setup) (b : QueryBudget) :
    (prfHmac1KeyAtomicProg S b).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hL := liftAuth1Stage_size_le tlPrfHmac tlPrfHmac_sizeLe S (prfHmacRedProg1Key S b.q_total)
  have hLit : red1LitSize (prfHmacRedProg1Key S b.q_total) ≤ 20000 :=
    (prfHmacRedProg1Key_litSize_le S b.q_total).trans
      (_root_.Proofs.SignalPqxdh.Security.hm_prfHmacRedProg_litSize_le S b.q_total)
  have h1 := prfHmacRedProg1Key_size_le S b.q_total
  have hP := hm_prfHmacRedProg_size_le_clamped S b.q_total
  have hq := (a1_bits_params_le_stepCostBudget S b).1
  exact a1_size_le_budget S b
    (by change (liftAuth1Stage tlPrfHmac S (prfHmacRedProg1Key S b.q_total)).size ≤ _; omega)

/-- The one-key `ReductionDsl` authentication reduction bundle over `pqAtomicOps`. -/
def pqxdhAuth1KeyCostedSims (S : Setup) : Auth1KeyCostedReductionFamily S where
  sig  b := sigAuth1KeyAtomicProg S b
  shcr b := shcrAuth1KeyAtomicProg S b
  gdh  b := fgAuth1KeyGapDhAtomicProg S b
  ck   b := prfCk1KeyAtomicProg S b
  mk   b := prfMsgKeys1KeyAtomicProg S b
  cpa  b := aeadCpa1KeyAtomicProg S b
  int  b := prfHmac1KeyAtomicProg S b

theorem primBounded_authCkStepWithPrim1Key (S : Setup)
    (sampAt : Nat → OracleComp PrimBaseSpec (Bytes × Bytes))
    (hSamp : ∀ s, PrimBounded (sampAt s) 2)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    PrimBounded (AuthSubHops1to3.authCkStepWithPrim1Key S sampAt q hst) (S.N_dh * 26 + 21) := by
  by_cases hI : AuthPrf.AuthQuery.NotInitPrin q
  · rw [AuthPrf.authCkStepWithPrim1Key_eq_of_ne sampAt q hI hst]
    exact AuthSubHops1to3.primBounded_authCkStepWithPrim S sampAt hSamp q hst
  · obtain ⟨u, rfl⟩ : ∃ u, q = .initPrin u := by
      by_contra hne; push Not at hne; exact hI hne
    exact (AuthPrf.primBounded_stepAuthOtherPrim1Key S (.initPrin u) hst).mono (by omega)

theorem primBounded_authCkPreSampleRunPrim1Key (S : Setup) (idx : Nat)
    (p : Bytes × Bytes) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    PrimBounded (AuthSubHops1to3.authCkPreSampleRunPrim1Key S idx p A.1)
      (b.q_total * (S.N_dh * 26 + 21) + S.N_dh * 5) := by
  unfold AuthSubHops1to3.authCkPreSampleRunPrim1Key
  refine primBounded_bind_le (b.q_total * (S.N_dh * 26 + 21) + S.N_dh * 5)
    (primBounded_embedUnif ($ᵗ Bool) 0)
    (fun secb => ?_) (by omega)
  refine primBounded_bind_le (S.N_dh * 5)
    (primBounded_runWithPrimStep
      (AuthSubHops1to3.authCkStepWithPrim1Key S (sampAtCkPrim idx p))
      (S.N_dh * 26 + 21)
      (fun q s => primBounded_authCkStepWithPrim1Key S (sampAtCkPrim idx p)
        (primBounded_sampAtCkPrim idx p) q s)
      A.1.run b.q_total (SignalPqxdh.QueryBounded.auth_total A.2)
      (AuthHybridStateFixed.empty S secb))
    (fun ⟨b', finalSt⟩ => primBounded_finalizeAuthFixedPrim S secb b' finalSt.toAuthHybridState)
    (by omega)

theorem prfCkReductionAuthFixed1Key_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (AuthSubHops1to3.prfCkReductionAuthFixed1Key S b A).Bounded := fun mkSeedChal ck1_1Chal =>
  primBounded_bind_le (b.q_total * (S.N_dh * 26 + 21) + S.N_dh * 5)
    (primBounded_embedUnif _ 0)
    (fun idx => primBounded_authCkPreSampleRunPrim1Key S idx (mkSeedChal, ck1_1Chal) b A)
    (by dsimp [AuthSubHops1to3.prfCkReductionAuthFixed1Key]; omega)


theorem prfCkReductionAuthFixed1Key_prim_queries (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (AuthSubHops1to3.prfCkReductionAuthFixed1Key S b A).q_prim ≤ primQueryBudget S b := by
  dsimp [AuthSubHops1to3.prfCkReductionAuthFixed1Key, primQueryBudget]
  nlinarith

private def shcrAuth1KeyLegacyAdv (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : KemShCrAdv where
  State := Mid (authSpec S) Bool (shcrAuth1KeyDslProg S b).π.denote
    (shcrAuth1KeyDslProg S b).σ.denote Bytes
  choosePk pk sk := (shcrAuth1KeyDslProg S b).eval1 (fun _ => A.1.run) (pk, sk) b.q_total false
  findCollision st ss ct := (shcrAuth1KeyDslProg S b).eval2 st (ss, ct) b.q_total false
  q_prim := primQueryBudget S b

private theorem shcrAuth1KeyLegacyAdv_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : (shcrAuth1KeyLegacyAdv S b A).Bounded := by
  refine ⟨fun pk sk => ?_, fun st ss ct => ?_⟩
  · exact (AuthAead.queryBound_eval1 (shcrAuth1KeyDslProg S b)
      (fun q => isPrimQuery₀ q = true) AuthAead.primW AuthAead.primWS
      AuthAead.pqPrimIface_hw AuthAead.pqPrimIface_hU
      (fun _ => A.1.run) (pk, sk) b.q_total false).mono
      (shcrAuth1KeyDslProg_totalQueries_le S b)
  · exact (AuthAead.queryBound_eval2 (shcrAuth1KeyDslProg S b)
      (fun q => isPrimQuery₀ q = true) AuthAead.primW AuthAead.primWS
      AuthAead.pqPrimIface_hw AuthAead.pqPrimIface_hU
      st (ss, ct) b.q_total false).mono
      (shcrAuth1KeyDslProg_totalQueries_le S b)

private theorem cpa1Key_choose_map_eq {S : Setup} {b : QueryBudget}
    (m1 : OracleComp PrimBaseSpec ((embedTy cpaChOutTy).denote ×
      Mid (authSpec S) Bool (embedTy (aeadCpaRedProg1Key S b.q_total).π).denote
        (embedTy (aeadCpaRedProg1Key S b.q_total).σ).denote (embedTy cpaChOutTy).denote))
    (m2 : OracleComp PrimBaseSpec (cpaChOutTy.denote ×
      Mid (authSpec S) Bool (aeadCpaRedProg1Key S b.q_total).π.denote
        (aeadCpaRedProg1Key S b.q_total).σ.denote cpaChOutTy.denote))
    (h : m1 = Prod.map (embedVal cpaChOutTy) (embedMid (ch := cpaChOutTy)) <$> m2) :
    (do let r ← m1; pure (r.1.1, r.1.2.1, r.1.2.2, r.2)) =
      (fun (ad, m0, m1, st) => (ad, m0, m1, embedMid (ch := cpaChOutTy) st)) <$>
        (do let r ← m2; pure (r.1.1, r.1.2.1, r.1.2.2, r.2)) := by
  subst h
  rw [bind_map_left, map_bind]
  refine bind_congr fun ⟨⟨ad, m0, m1⟩, st⟩ => ?_
  simp [embedVal]


private theorem pqxdhAuth1KeyCostedSims_sig_adv_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (pqxdhAuth1KeyCostedSims S).eval.sig b A = sigAuth1KeyDslAdv S b A :=
  congrArg (fun r =>
    ({ run := r, q_sig := 2 * min S.N_spk_tot S.N_recv, q_ddh := authGdhQueryBudget S b,
       q_prim := gdhPrimQueryBudget S b } : GapSigEufCmaAdv))
    (funext fun pk => sigAuth1KeyAtomicProg_eval_eq S b (fun _ => A.1.run) pk)

private theorem pqxdhAuth1KeyCostedSims_gdh_adv_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (pqxdhAuth1KeyCostedSims S).eval.gdh b A = fgAuth1KeyGapDhDslAdv S b A :=
  congrArg (fun r =>
    ({ run := r, q_ddh := authGdhQueryBudget S b, q_sig := 2 * min S.N_spk_tot S.N_recv,
       q_prim := gdhPrimQueryBudget S b } : GapDhWithSignAdv))
    (funext fun U => funext fun V => fgAuth1KeyGapDhAtomicProg_eval_eq S b (fun _ => A.1.run) U V)

private theorem pqxdhAuth1KeyCostedSims_ck_adv_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (pqxdhAuth1KeyCostedSims S).eval.ck b A =
      ({ dist := fun mkSeed ck1 =>
          (prfCkRedProg1Key S b.q_total).eval (fun _ => A.1.run) (mkSeed, ck1),
         q_prf := 1, q_prim := primQueryBudget S b } : PrfCkAdv) :=
  congrArg (fun r => ({ dist := r, q_prf := 1, q_prim := primQueryBudget S b } : PrfCkAdv))
    (funext fun mkSeed => funext fun ck1 =>
      prfCk1KeyAtomicProg_eval_eq S b (fun _ => A.1.run) mkSeed ck1)

private theorem pqxdhAuth1KeyCostedSims_mk_adv_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (pqxdhAuth1KeyCostedSims S).eval.mk b A =
      ({ run := (prfMsgKeysRedProg1Key S b.q_total).eval (fun _ => A.1.run) (),
         q_prf := S.N_recv_tot + 1, q_prim := primQueryBudget S b } : PrfMsgKeysAdv) :=
  congrArg (fun r =>
    ({ run := r, q_prf := S.N_recv_tot + 1, q_prim := primQueryBudget S b } : PrfMsgKeysAdv))
    (prfMsgKeys1KeyAtomicProg_eval_eq S b (fun _ => A.1.run))

private theorem pqxdhAuth1KeyCostedSims_int_adv_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (pqxdhAuth1KeyCostedSims S).eval.int b A = prfHmac1KeyDslAdv S b A :=
  congrArg (fun r =>
    ({ run := r, q_prf := S.N_recv_tot + 1, q_prim := primQueryBudget S b } : PrfHmacAdv))
    (prfHmac1KeyAtomicProg_eval_eq S b (fun _ => A.1.run))

/-- Semantic query bounds for `(pqxdhAuth1KeyCostedSims S).eval`. -/
theorem pqxdhAuth1KeyCostedSims_simBounds (S : Setup) :
    Auth1KeyReductionQueryBounds S (pqxdhAuth1KeyCostedSims S).eval := {
  sig_bounded  := fun b A => by
    rw [pqxdhAuth1KeyCostedSims_sig_adv_eq]
    exact sigAuth1KeyDslAdv_bounded S b A
  shcr_bounded := fun b A => by
    refine kemShCrAdv_bounded_of_state_retract (A := shcrAuth1KeyLegacyAdv S b A) rfl
      (embedMid (π := (shcrAuth1KeyDslProg S b).π) (σ := (shcrAuth1KeyDslProg S b).σ)
        (ch := SignalPqxdh.LegacyCosted.B 1568))
      (projMid (π := (shcrAuth1KeyDslProg S b).π) (σ := (shcrAuth1KeyDslProg S b).σ)
        (ch := SignalPqxdh.LegacyCosted.B 1568))
      (fun pk sk => ?_) (fun st' ss ct => ?_) (shcrAuth1KeyLegacyAdv_bounded S b A)
    · exact liftAuth2Stage_eval1 tlAuthPrim S (fun _ => rfl) (shcrAuth1KeyDslProg S b)
        (fun _ => A.1.run) (pk, sk) b.q_total false
    · have hId : embedVal (SignalPqxdh.LegacyCosted.B 1568) = id := rfl
      have hRet := embedMid_projMid
        (π := (shcrAuth1KeyDslProg S b).π) (σ := (shcrAuth1KeyDslProg S b).σ)
        (ch := SignalPqxdh.LegacyCosted.B 1568) st'
      have h := liftAuth2Stage_eval2 tlAuthPrim S (fun _ => rfl) (shcrAuth1KeyDslProg S b)
        (projMid (π := (shcrAuth1KeyDslProg S b).π) (σ := (shcrAuth1KeyDslProg S b).σ)
          (ch := SignalPqxdh.LegacyCosted.B 1568) st') (ss, ct) b.q_total false
      rw [hRet, hId, id_map] at h
      exact h
  gdh_bounded  := fun b A => by
    rw [pqxdhAuth1KeyCostedSims_gdh_adv_eq]
    exact fgAuth1KeyGapDhDslAdv_bounded S b A
  ck_bounded   := fun b A => by
    rw [pqxdhAuth1KeyCostedSims_ck_adv_eq]
    intro mkSeed ck1
    change ((prfCkReductionAuthFixed1KeyDslAdv S b A).dist mkSeed ck1).IsQueryBoundP
      (fun q => isPrimQuery₀ q = true) (primQueryBudget S b)
    rw [prfCkReductionAuthFixed1KeyDslAdv_eq]
    exact (prfCkReductionAuthFixed1Key_bounded S b A mkSeed ck1).mono
      (prfCkReductionAuthFixed1Key_prim_queries S b A)
  mk_bounded   := fun b A => by
    rw [pqxdhAuth1KeyCostedSims_mk_adv_eq]
    exact ⟨(prfMsgKeys1KeyDslAdv_bounded S b A).1,
      (prfMsgKeys1KeyDslAdv_bounded S b A).2.mono (prfMsgKeys1KeyDslAdv_prim_queries S b A)⟩
  cpa_bounded  := fun b A => by
    refine aeadIndCpaAdv_bounded_of_state_retract (A := aeadCpaDsl1KeyAdv S b A.1) rfl
      (embedMid (π := (aeadCpaRedProg1Key S b.q_total).π)
        (σ := (aeadCpaRedProg1Key S b.q_total).σ) (ch := cpaChOutTy))
      (projMid (π := (aeadCpaRedProg1Key S b.q_total).π)
        (σ := (aeadCpaRedProg1Key S b.q_total).σ) (ch := cpaChOutTy))
      ?_ (fun st' c? => ?_) (aeadCpaDsl1KeyAdv_bounded S b A.1)
    · exact cpa1Key_choose_map_eq _ _ (liftAuth2Stage_eval1 tlAuthPrim S (fun _ => rfl)
        (aeadCpaRedProg1Key S b.q_total) (fun _ => A.1.run) () b.q_total false)
    · have hc : embedVal (.opt (SignalPqxdh.LegacyCosted.B 32)) c? = c? := by cases c? <;> rfl
      have hId : embedVal .bool = id := rfl
      have hRet := embedMid_projMid (π := (aeadCpaRedProg1Key S b.q_total).π)
        (σ := (aeadCpaRedProg1Key S b.q_total).σ) (ch := cpaChOutTy) st'
      have h : (aeadCpa1KeyAtomicProg S b).eval2
          (embedMid (π := (aeadCpaRedProg1Key S b.q_total).π)
            (σ := (aeadCpaRedProg1Key S b.q_total).σ) (ch := cpaChOutTy)
            (projMid (π := (aeadCpaRedProg1Key S b.q_total).π)
              (σ := (aeadCpaRedProg1Key S b.q_total).σ) (ch := cpaChOutTy) st'))
          (embedVal (.opt (SignalPqxdh.LegacyCosted.B 32)) c?) b.q_total false =
          embedVal .bool <$> (aeadCpaRedProg1Key S b.q_total).eval2
            (projMid (π := (aeadCpaRedProg1Key S b.q_total).π)
              (σ := (aeadCpaRedProg1Key S b.q_total).σ) (ch := cpaChOutTy) st')
            c? b.q_total false :=
        liftAuth2Stage_eval2 tlAuthPrim S (fun _ => rfl) (aeadCpaRedProg1Key S b.q_total)
          (projMid (π := (aeadCpaRedProg1Key S b.q_total).π)
            (σ := (aeadCpaRedProg1Key S b.q_total).σ) (ch := cpaChOutTy) st') c? b.q_total false
      rw [hRet, hc, hId, id_map] at h
      exact h
  int_bounded  := fun b A => by
    rw [pqxdhAuth1KeyCostedSims_int_adv_eq]
    exact prfHmac1KeyDslAdv_bounded S b A
}

theorem pqxdhAuth1KeyCostedSims_shcr_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    KemShCr P ((pqxdhAuth1KeyCostedSims S).eval.shcr b A) =
      KemShCr P (shcrReductionAuth1Key S b A) := by
  refine Eq.trans (kemShCr_eq_of_state_map P (shcrAuth1KeyDslAdv S b A.1)
    ((pqxdhAuth1KeyCostedSims S).eval.shcr b A)
    (embedMid (ch := SignalPqxdh.LegacyCosted.B 1568))
    (fun pk sk => ?_) (fun st ss ct => ?_))
    (shcrAuth1KeyDslAdv_kemShCr_eq P S b A)
  · exact liftAuth2Stage_eval1 tlAuthPrim S (fun _ => rfl) (shcrAuth1KeyDslProg S b)
      (fun _ => A.1.run) (pk, sk) b.q_total false
  · have hId : embedVal (SignalPqxdh.LegacyCosted.B 1568) = id := rfl
    have h := liftAuth2Stage_eval2 tlAuthPrim S (fun _ => rfl) (shcrAuth1KeyDslProg S b)
      st (ss, ct) b.q_total false
    rw [hId, id_map] at h
    exact h

theorem pqxdhAuth1KeyCostedSims_cpa_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    AeadIndCpa P ((pqxdhAuth1KeyCostedSims S).eval.cpa b A) =
      AeadIndCpa P (aeadCpaReductionAuthFixed1Key S b A) := by
  refine Eq.trans (aeadIndCpa_eq_of_state_map P (aeadCpaDsl1KeyAdv S b A.1)
    ((pqxdhAuth1KeyCostedSims S).eval.cpa b A) (embedMid (ch := cpaChOutTy))
    ?_ (fun st c? => ?_))
    (aeadCpaDsl1KeyAdv_aeadIndCpa_eq P S b A)
  · exact cpa1Key_choose_map_eq _ _ (liftAuth2Stage_eval1 tlAuthPrim S (fun _ => rfl)
      (aeadCpaRedProg1Key S b.q_total) (fun _ => A.1.run) () b.q_total false)
  · have hc : embedVal (.opt (SignalPqxdh.LegacyCosted.B 32)) c? = c? := by cases c? <;> rfl
    have hId : embedVal .bool = id := rfl
    have h : (aeadCpa1KeyAtomicProg S b).eval2 (embedMid (ch := cpaChOutTy) st)
        (embedVal (.opt (SignalPqxdh.LegacyCosted.B 32)) c?) b.q_total false =
        embedVal .bool <$> (aeadCpaRedProg1Key S b.q_total).eval2 st c? b.q_total false :=
      liftAuth2Stage_eval2 tlAuthPrim S (fun _ => rfl) (aeadCpaRedProg1Key S b.q_total)
        st c? b.q_total false
    rw [hc, hId, id_map] at h
    exact h

end Proofs.SignalPqxdh.Security.PqxdhDelta
