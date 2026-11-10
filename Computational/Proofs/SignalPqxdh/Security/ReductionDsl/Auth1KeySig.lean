/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyGapDh
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeSig
public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuth1KeySig

/-!
# One-Key `Auth` `GapSigEufCma` `ReductionDsl` Program

Defines `sigAuth1KeyProg`, the `CostedReduction` over `pqSigAndDdhIface` corresponding to the
shallow one-key `GapSigEufCma` reduction `sigReductionAuth1Key`: `.sendOPK` and `.sendNoOPK` check
for bundle forgeries via `extractC`, and non-forging queries delegate to the one-key
`GapDhWithSign` handler.
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

abbrev a1sFgTy : Ty pqSig := .opt (.prod (B 1569) (B 64))

abbrev a1sStTy : Ty pqSig := .prod a1gStTy (.prod .nat (.prod (B 32) a1sFgTy))

abbrev a1sRS : Ty pqSig := .prod authRespTy a1sStTy

@[reducible] def a1sG {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ a1sStTy) :
    Expr pqxdhOps Γ a1gStTy := .fst e
@[reducible] def a1sTp {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ a1sStTy) :
    Expr pqxdhOps Γ .nat := .fst (.snd e)
@[reducible] def a1sTpk {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ a1sStTy) :
    Expr pqxdhOps Γ (B 32) := .fst (.snd (.snd e))
@[reducible] def a1sFg {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ a1sStTy) :
    Expr pqxdhOps Γ a1sFgTy := .snd (.snd (.snd e))
@[reducible] def a1sMk {Γ : List (Ty pqSig)} (g : Expr pqxdhOps Γ a1gStTy)
    (tp : Expr pqxdhOps Γ .nat) (tpk : Expr pqxdhOps Γ (B 32)) (fg : Expr pqxdhOps Γ a1sFgTy) :
    Expr pqxdhOps Γ a1sStTy :=
  .pair g (.pair tp (.pair tpk fg))
@[reducible] def a1sBase {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ a1sStTy) :
    Expr pqxdhOps Γ authStateTy := fsBase (.snd (.fst (a1sG e)))

@[reducible] def a1sDummyPa {Γ : List (Ty pqSig)} (pk : Expr pqxdhOps Γ (B 32))
    (tp : Expr pqxdhOps Γ .nat) : Expr pqxdhOps Γ paramsTy :=
  .pair pk (.pair pk (.pair (.litBool true) (.pair tp (.litNat 0))))

@[reducible] def a1sCaseAPa2 {Γ : List (Ty pqSig)} (pk : Expr pqxdhOps Γ (B 32))
    (tp : Expr pqxdhOps Γ .nat) : Expr pqxdhOps Γ a1gParams2Ty :=
  .pair pk (.pair pk (.pair (.inl tp) .noneE))

section Branches

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}

def a1sSendCheckC (s : Var Γ₁ a1sStTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    CS Δ (.sum a1sRS .unit) :=
  letV (a1sTp (v s)) fun tp =>
  letV (a1sTpk (v s)) fun tpk =>
  letV (a1sBase (v s)) fun st =>
  letV (.fst (.snd (.snd (v x)))) fun bu =>
  bindV (KeyInd.liftBase (C := sigAndDdhOracle) (extractC S K tp tpk st bu)) fun fg =>
  .iteC (isSomeE (v fg))
    (.ret (.inl (.pair aNone (a1sMk (a1sG (v s)) (a1sTp (v s)) (a1sTpk (v s)) (v fg)))))
    (.ret (.inr .litUnit))

def a1sPreC (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    CS Δ (.sum a1sRS .unit) :=
  caseSumV (v q) (fun _ => .ret (.inr .litUnit)) fun q =>
  caseSumV (v q) (fun _ => .ret (.inr .litUnit)) fun q =>
  caseSumV (v q) (fun _ => .ret (.inr .litUnit)) fun q =>
  caseSumV (v q) (fun _ => .ret (.inr .litUnit)) fun q =>
  caseSumV (v q) (fun x => a1sSendCheckC S K s x) fun q =>
  caseSumV (v q) (fun x => a1sSendCheckC S K s x) fun _ =>
  .ret (.inr .litUnit)

def a1sDelegateC (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    CS Δ a1sRS :=
  letV (a1sG (v s)) fun g =>
  bindV (a1gStepC S K g q) fun r =>
  .ret (.pair (.fst (v r)) (a1sMk (.snd (v r)) (a1sTp (v s)) (a1sTpk (v s)) (a1sFg (v s))))

def a1sStepC (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    CS Δ a1sRS :=
  .iteC (isSomeE (a1sFg (v s))) (.ret (.pair aNone (v s))) <|
  bindV (a1sPreC S K s q) fun pre =>
  caseSumV (v pre) (fun r => .ret (v r)) fun _ =>
  a1sDelegateC S K s q

def a1sDelegate2C (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    CS Δ a1sRS :=
  letV (.pair (.pair (a1sCaseAPa2 (a1sTpk (v s)) (a1sTp (v s))) (.snd (.fst (a1sG (v s)))))
      (.snd (a1sG (v s)))) fun g2 =>
  bindV (a1gStep2C S K g2 q) fun r =>
  .ret (.pair (.fst (v r))
    (a1sMk (.pair (.pair (.fst (.fst (a1sG (v s)))) (.snd (.fst (.snd (v r)))))
        (.snd (.snd (v r))))
      (a1sTp (v s)) (a1sTpk (v s)) (a1sFg (v s))))

def a1sStep2C (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    CS Δ a1sRS :=
  .iteC (isSomeE (a1sFg (v s))) (.ret (.pair aNone (v s))) <|
  bindV (a1sPreC S K s q) fun pre =>
  caseSumV (v pre) (fun r => .ret (v r)) fun _ =>
  a1sDelegate2C S K s q

end Branches

def a1sHandleDsl (S : Setup) (K : Nat) : CS [a1sStTy, authQueryTy] a1sRS :=
  a1sStepC S K (.vz : Var [a1sStTy, authQueryTy] a1sStTy)
    (.vs .vz : Var [a1sStTy, authQueryTy] authQueryTy)

def a1sHandle2Dsl (S : Setup) (K : Nat) : CS [a1sStTy, authQueryTy] a1sRS :=
  a1sStep2C S K (.vz : Var [a1sStTy, authQueryTy] a1sStTy)
    (.vs .vz : Var [a1sStTy, authQueryTy] authQueryTy)

def a1sInitDsl (S : Setup) : CS [B 32] (.prod .unit a1sStTy) :=
  bindV (.sampleIndexC S.N_id) fun k => bindV .sampleBoolC fun b =>
  letV (.var (.vs (.vs .vz)) : Expr pqxdhOps [.bool, .nat, B 32] (B 32)) fun pk =>
  .ret (.pair .litUnit (a1sMk
    (.pair (.pair (.pair (v pk) (.pair (v pk) (.pair (.litBool true) (.pair (v k)
        (.litNat S.N_spk_tot))))) (emptySimE (v b)))
      (.litNat (min S.N_spk_tot S.N_recv)))
    (v k) (v pk) .noneE))

def a1sInit2Dsl (S : Setup) (K : Nat) : CS [B 32] (.prod .unit a1sStTy) :=
  bindV (.sampleIndexC S.N_id) fun k => bindV .sampleBoolC fun b =>
  letV (.var (.vs (.vs .vz)) : Expr pqxdhOps [.bool, .nat, B 32] (B 32)) fun pk =>
  .ret (.pair .litUnit (a1sMk
    (.pair (.pair (a1sDummyPa (v pk) (v k)) (emptySimE (v b)))
      (.litNat (min K (min S.N_spk_tot S.N_recv))))
    (v k) (v pk) .noneE))

def a1sFinishDsl : CS [a1sStTy, .bool] (.prod (B 1569) (B 64)) :=
  .ret (eCaseOpt (a1sFg (.var .vz)) (.pair (.litBytes 1569 []) (.litBytes 64 [])) fun f => v f)

/-- `ReductionDsl` program for `sigReductionAuth1Key S b` (with list bound `K`). -/
def sigAuth1KeyProg (S : Setup) (K : Nat) :
    CostedReduction pqxdhOps pqSigAndDdhIface (authSpec S) (authCodec S)
      (B 32) .unit .bool (.prod (B 1569) (B 64)) where
  σ      := a1sStTy
  init   := a1sInit2Dsl S K
  handle := a1sHandle2Dsl S K
  finish := a1sFinishDsl

abbrev sigAuth1KeyDslProg (S : Setup) (b : QueryBudget) :=
  sigAuth1KeyProg S b.q_total

end SignalPqxdh.Security.ReductionDsl.AuthHs
