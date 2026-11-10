/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeySig
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeProofs
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeySigBounds

/-!
# Syntactic Bounds for the One-Key `Auth` Sig Dispatch Layer

**Checked by Lean.** Proves cost and query-count bounds for the forgery-extraction and
pre-dispatch blocks (`extractC`, `a1sSendCheckC`, and `a1sPreC`) of `sigAuth1KeyProg`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

section
set_option allowUnsafeReducibility true
attribute [implicit_reducible] sigAndDdhOracle
end

section Pre

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}

theorem extractC_costUB_le_tight {Γa Γb Γc Γd : List (Ty pqSig)}
    [Ext Γa Δ] [Ext Γb Δ] [Ext Γc Δ] [Ext Γd Δ]
    (tp : Var Γa .nat) (tpk : Var Γb (B 32)) (st : Var Γc authStateTy) (bu : Var Γd preKeyBundleTy) :
    (extractC S K (Δ := Δ) tp tpk st bu).costUB ≤ 9000 + 206 * min K S.N_dh + 4000 * K := by
  simp only [extractC, honestPeerC_costUB,
    bindV, eAny, eCaseOpt,
    natEq,
    stSpks, sbSpkPk, sbPqspkPk,
    buIkB, buSpkB, buSpkSig, buPqspkB, buPqspkSig,
    costUB_encEC, costUB_encKEM, costUB_bytesWiden_33_1536, costUB_bytesBeq,
    costUB_queryPrim,
    Ty.wd, v, Comp.costUB, Expr.costUB,
    PNat.val_ofNat]
  omega

theorem extractC_costUB_le {Γa Γb Γc Γd : List (Ty pqSig)}
    [Ext Γa Δ] [Ext Γb Δ] [Ext Γc Δ] [Ext Γd Δ]
    (tp : Var Γa .nat) (tpk : Var Γb (B 32)) (st : Var Γc authStateTy) (bu : Var Γd preKeyBundleTy) :
    (extractC S K (Δ := Δ) tp tpk st bu).costUB ≤ 9000 + 206 * S.N_dh + 4000 * K := by
  have h := extractC_costUB_le_tight S K (Δ := Δ) tp tpk st bu
  have := Nat.min_le_right K S.N_dh
  omega

theorem extractC_queries_prim {Γa Γb Γc Γd : List (Ty pqSig)}
    [Ext Γa Δ] [Ext Γb Δ] [Ext Γc Δ] [Ext Γd Δ]
    (tp : Var Γa .nat) (tpk : Var Γb (B 32)) (st : Var Γc authStateTy) (bu : Var Γd preKeyBundleTy) :
    (extractC S K (Δ := Δ) tp tpk st bu).queries KeyIndGapDh.wPrimBase KeyIndGapDh.wsZeroBase =
      2 * min K S.N_dh + 2 := by
  show (extractC S K (Δ := Δ) tp tpk st bu).queries primW primWS = _
  simp only [extractC, honestPeerC_queries, bindV, Comp.queryPrim,
    primW, Comp.queries]
  omega

theorem a1sSendCheckC_costUB_le_tight [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ a1sStTy) (x : Var Γ₂ sendQTy) :
    (a1sSendCheckC S K (Δ := Δ) s x).costUB ≤ 12000 + 206 * min K S.N_dh + 4000 * K := by
  simp only [a1sSendCheckC, a1sTp, a1sTpk, a1sBase, a1sG, a1sMk, fsBase,
    KeyIndGapDh.liftBase_costUB, extractC, honestPeerC_costUB,
    bindV, letV, eAny, eCaseOpt,
    natEq, isSomeE, aNone,
    stSpks, sbSpkPk, sbPqspkPk,
    buIkB, buSpkB, buSpkSig, buPqspkB, buPqspkSig,
    Comp.letC,
    costUB_encEC, costUB_encKEM, costUB_bytesWiden_33_1536, costUB_bytesBeq,
    costUB_queryPrim,
    Ty.wd, v, Comp.costUB, Expr.costUB,
    PNat.val_ofNat]
  omega

theorem a1sSendCheckC_costUB_le [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ a1sStTy) (x : Var Γ₂ sendQTy) :
    (a1sSendCheckC S K (Δ := Δ) s x).costUB ≤ 12000 + 206 * S.N_dh + 4000 * K := by
  have h := a1sSendCheckC_costUB_le_tight S K (Δ := Δ) s x
  have := Nat.min_le_right K S.N_dh
  omega

theorem a1sSendCheckC_sigQueries [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ a1sStTy) (x : Var Γ₂ sendQTy) :
    (a1sSendCheckC S K (Δ := Δ) s x).queries
      SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 := by
  simp [a1sSendCheckC, bindV, letV, Comp.letC, Comp.queries]

theorem a1sSendCheckC_ddhQueries [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ a1sStTy) (x : Var Γ₂ sendQTy) :
    (a1sSendCheckC S K (Δ := Δ) s x).queries
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 := by
  simp [a1sSendCheckC, bindV, letV, Comp.letC, Comp.queries]

theorem a1sSendCheckC_primQueries [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ a1sStTy) (x : Var Γ₂ sendQTy) :
    (a1sSendCheckC S K (Δ := Δ) s x).queries
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight =
      2 * min K S.N_dh + 2 := by
  simp [a1sSendCheckC, bindV, letV, Comp.letC, Comp.queries, extractC_queries_prim]

theorem a1sPreC_costUB_le_tight [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) :
    (a1sPreC S K (Δ := Δ) s q).costUB ≤ 25000 + 412 * min K S.N_dh + 8000 * K := by
  simp only [a1sPreC, a1sSendCheckC, a1sTp, a1sTpk, a1sBase, a1sG, a1sMk, fsBase,
    KeyIndGapDh.liftBase_costUB, extractC, honestPeerC_costUB,
    bindV, letV, caseSumV, eAny, eCaseOpt,
    natEq, isSomeE, aNone,
    stSpks, sbSpkPk, sbPqspkPk,
    buIkB, buSpkB, buSpkSig, buPqspkB, buPqspkSig,
    Comp.letC,
    costUB_encEC, costUB_encKEM, costUB_bytesWiden_33_1536, costUB_bytesBeq,
    costUB_queryPrim,
    Ty.wd, v, Comp.costUB, Expr.costUB,
    PNat.val_ofNat]
  omega

theorem a1sPreC_costUB_le [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) :
    (a1sPreC S K (Δ := Δ) s q).costUB ≤ 25000 + 412 * S.N_dh + 8000 * K := by
  have h := a1sPreC_costUB_le_tight S K (Δ := Δ) s q
  have := Nat.min_le_right K S.N_dh
  omega

theorem a1sPreC_sigQueries [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) :
    (a1sPreC S K (Δ := Δ) s q).queries
      SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 := by
  simp [a1sPreC, caseSumV, a1sSendCheckC_sigQueries, Comp.queries]

theorem a1sPreC_ddhQueries [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) :
    (a1sPreC S K (Δ := Δ) s q).queries
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 := by
  simp [a1sPreC, caseSumV, a1sSendCheckC_ddhQueries, Comp.queries]

theorem a1sPreC_primQueries_le_tight [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) :
    (a1sPreC S K (Δ := Δ) s q).queries
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ≤
      2 * min K S.N_dh + 2 := by
  simp [a1sPreC, caseSumV, a1sSendCheckC_primQueries, Comp.queries]

theorem a1sPreC_primQueries_le [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) :
    (a1sPreC S K (Δ := Δ) s q).queries
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ≤
      2 * S.N_dh + 2 := by
  have h := a1sPreC_primQueries_le_tight S K (Δ := Δ) s q
  have := Nat.min_le_right K S.N_dh
  omega

end Pre

end SignalPqxdh.Security.ReductionDsl.AuthHs
