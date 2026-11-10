/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables
public import Computational.Proofs.E2E.Dsl.TablesHonest
public import Computational.Proofs.E2E.Dsl.ClampsLossless
public import Computational.Proofs.GameHop.ReductionDsl.CostUB

/-!
# Shared Types, Hooks, and Helpers for E2E PQXDH Simulation

Defines `ReductionDsl` value encodings and bijections for `SignalPqxdh.KeyIndState S`, the
inductive list-length invariants `KeyIndSetupBounded` and `stListBounded`, and primitive/sampling
hooks (`E2EPqxdhHooks`) and helper programs for simulating `SignalPqxdh.pqxdhKeyIndImpl1KeyReal`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.PqxdhSimTypes

open Classical
open OracleSpec OracleComp

open ReductionDsl (Ty Ops Samplers Var Expr Comp Iface Env UniformSamplerTag unifSamplers bits
  findML anyML mapML)
open CryptoVerification.E2E.Costed (E2ESort E2EUnifBase E2EPureOp E2ECryptoOp e2eSig e2eSamplers
  e2ePureOps e2eCryptoOps e2eOps PB PU32 B U8 U32 U64 BV128 BV256 BV512 FinT PK IdKey PlainT
  GhostStT BinStT drKeyT drKeyV drKeyOfV bundleT bundleV bundleOfV hdrT hdrV hdrOfV sidT sidV
  sidOfV dhSecretsT keyIndQT keyIndQenc keyIndQdec keyIndRT keyIndRenc keyIndRdec)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp eval_e2ePureOp cost_e2ePureOp
  e2eCryptoOp eval_e2eCryptoOp cost_e2eCryptoOp drKeyOfV_drKeyV drKeyV_drKeyOfV
  bundleOfV_bundleV bundleV_bundleOfV hdrOfV_hdrV hdrV_hdrOfV sidOfV_sidV sidV_sidOfV
  keyIndQdec_keyIndQenc keyIndQenc_keyIndQdec keyIndRdec_keyIndRenc keyIndRenc_keyIndRdec)
open Computational.Proofs.E2E.Dsl.ClampsLossless (e2eCryptoOps_eval_x25519_lossless
  e2eCryptoOps_eval_x25519Base_lossless e2eCryptoOps_eval_pow8_lossless
  e2eCryptoOps_eval_sigSign_lossless e2eCryptoOps_eval_kemKeyGen_lossless
  e2eCryptoOps_eval_kemEncaps_lossless e2eCryptoOps_eval_kemDecaps_lossless
  e2eCryptoOps_eval_hkdfDerive96_lossless)
open Computational.Proofs.GameHop.ReductionDsl.CostUB (exprCostUB compCostUB compQueriesUB
  exprCost_le_costUB compCost_le_costUB compQueries_le_queriesUB)
open CryptoGames.LibsignalSession (Crypto PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open SignalPqxdh (Setup Primitives WellFormedPrimitivesδ DRKey PreKeyBundleInput HandshakeHdr
  SessionId PrincipalEntry SpkBundleEntry OpkEntry KeyIndInitiatorEntry KeyIndRespEntry
  KeyIndQuery KeyIndResponse KeyIndState AcceptKeysInput TAG_EC_DJB TAG_KYBER_1024 F_X25519
  kyberCtLen encodeEC encodeKEM buildSecrets dhOptNonZero sampleBytes32 sampleScalar32 sampleCoins32
  sampleRandom64 sampleDRKey96 sampleKemKeyGen word256ToBytes findHonestPrincipal resolveSigPk
  isHonestUncorruptedPeer checkBundleProvenance isAdvRegistered isGameIdKey isGameSpk isGameOpk
  koskBundleOk koskSenderOk registerAdvKey evalHkdfOrRo checkAndMarkKyberBaseKeySeen keyIndPartner
  isKeyIndSessionTestable recordKeyIndResp keyIndPartnerRandKey? runKeyIndInitiate
  pqxdhKeyIndImpl pqxdhKeyIndImpl1KeyReal)
open SignalPqxdh.Model (acceptKeys)

/-! ## Context weakening and binder combinators -/

@[simp] theorem env_get_zero {ℓ : ℕ} {Γ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)}
    (x : τ.denote) (ρ : Env Γ) :
    Env.get (.cons x ρ) .zero = x := rfl

@[simp] theorem env_get_succ {ℓ : ℕ} {Γ : List (Ty (e2eSig ℓ))} {σ τ : Ty (e2eSig ℓ)}
    (x : σ.denote) (ρ : Env Γ) (i : Var Γ τ) :
    Env.get (.cons x ρ) (.succ i) = Env.get ρ i := rfl

/-- Witnesses that context `Δ` extends `Γ` by innermost binders. -/
class Ext {ℓ : ℕ} (Γ Δ : List (Ty (e2eSig ℓ))) where
  wk : {τ : Ty (e2eSig ℓ)} → Var Γ τ → Var Δ τ

instance (priority := high) Ext.refl {ℓ : ℕ} {Γ : List (Ty (e2eSig ℓ))} : Ext Γ Γ :=
  ⟨fun x => x⟩

instance Ext.step {ℓ : ℕ} {Γ Δ : List (Ty (e2eSig ℓ))} {σ : Ty (e2eSig ℓ)} [h : Ext Γ Δ] :
    Ext Γ (σ :: Δ) :=
  ⟨fun x => .succ (h.wk x)⟩

def v {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ Δ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)}
    [h : Ext Γ Δ] (x : Var Γ τ) : Expr O Δ τ :=
  .var (h.wk x)

theorem v_def {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ Δ : List (Ty (e2eSig ℓ))}
    {τ : Ty (e2eSig ℓ)} [h : Ext Γ Δ] (x : Var Γ τ) :
    v (O := O) (Δ := Δ) x = .var (h.wk x) := rfl

theorem ext_refl_wk {ℓ : ℕ} {Γ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)}
    (x : Var Γ τ) : (Ext.refl (ℓ := ℓ) (Γ := Γ)).wk x = x := rfl

theorem ext_step_wk {ℓ : ℕ} {Γ Δ : List (Ty (e2eSig ℓ))} {σ τ : Ty (e2eSig ℓ)}
    [h : Ext Γ Δ] (x : Var Γ τ) :
    (Ext.step (ℓ := ℓ) (Γ := Γ) (Δ := Δ) (σ := σ)).wk x = .succ (h.wk x) := rfl

@[simp] theorem eval_v_refl {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {τ : Ty (e2eSig ℓ)} (x : Var Γ τ) (ρ : Env Γ) :
    (v (O := O) (Δ := Γ) x).eval ρ = ρ.get x := rfl

@[simp] theorem eval_v_cons {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ Δ : List (Ty (e2eSig ℓ))}
    {σ τ : Ty (e2eSig ℓ)} [h : Ext Γ Δ] (x : Var Γ τ) (a : σ.denote) (ρ : Env Δ) :
    (v (O := O) (Δ := σ :: Δ) x).eval (.cons a ρ) = (v (O := O) (Δ := Δ) x).eval ρ := rfl

@[dsl_cost, simp] theorem cost_v {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ Δ : List (Ty (e2eSig ℓ))}
    {τ : Ty (e2eSig ℓ)} [h : Ext Γ Δ] (x : Var Γ τ) :
    (v (O := O) (Δ := Δ) x).cost = 1 := rfl

@[dsl_cost, simp] theorem exprCostUB_v {ℓ : ℕ} {O : Ops (e2eSig ℓ)}
    {Γ Δ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)} [h : Ext Γ Δ] (x : Var Γ τ) :
    exprCostUB (v (O := O) (Δ := Δ) x) = 1 := rfl

section Binders

variable {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}

def eLet {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ τ) (k : Var (τ :: Γ) τ → Expr O (τ :: Γ) υ) : Expr O Γ υ :=
  .letE e (k .zero)

def eLet2 {Γ : List (Ty (e2eSig ℓ))} {α β υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.prod α β))
    (k : Var (α :: .prod α β :: Γ) α →
         Var (β :: α :: .prod α β :: Γ) β →
         Expr O (β :: α :: .prod α β :: Γ) υ) : Expr O Γ υ :=
  eLet e fun p => eLet (.fst (v p)) fun a => eLet (.snd (v p)) fun b => k a b

def eCaseOpt {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt τ)) (n : Expr O Γ υ)
    (s : Var (τ :: Γ) τ → Expr O (τ :: Γ) υ) : Expr O Γ υ :=
  .caseOpt e n (s .zero)

def eCaseSum {Γ : List (Ty (e2eSig ℓ))} {α β υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.sum α β))
    (l : Var (α :: Γ) α → Expr O (α :: Γ) υ)
    (r : Var (β :: Γ) β → Expr O (β :: Γ) υ) : Expr O Γ υ :=
  .caseSum e (l .zero) (r .zero)

def eFind {Γ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)} (K : ℕ)
    (l : Expr O Γ (.list τ)) (p : Var (τ :: Γ) τ → Expr O (τ :: Γ) .bool) :
    Expr O Γ (.opt τ) :=
  .findB K l (p .zero)

def eAny {Γ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)} (K : ℕ)
    (l : Expr O Γ (.list τ)) (p : Var (τ :: Γ) τ → Expr O (τ :: Γ) .bool) :
    Expr O Γ .bool :=
  .anyB K l (p .zero)

def eMap {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)} (K : ℕ)
    (l : Expr O Γ (.list τ)) (f : Var (τ :: Γ) τ → Expr O (τ :: Γ) υ) :
    Expr O Γ (.list υ) :=
  .mapB K l (f .zero)

def bindV {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    (c : Comp O I Γ τ) (k : Var (τ :: Γ) τ → Comp O I (τ :: Γ) υ) : Comp O I Γ υ :=
  .bind c (k .zero)

def letV {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ τ) (k : Var (τ :: Γ) τ → Comp O I (τ :: Γ) υ) : Comp O I Γ υ :=
  .bind (.ret e) (k .zero)

def bindV2 {Γ : List (Ty (e2eSig ℓ))} {α β υ : Ty (e2eSig ℓ)}
    (c : Comp O I Γ (.prod α β))
    (k : Var (α :: .prod α β :: Γ) α →
         Var (β :: α :: .prod α β :: Γ) β →
         Comp O I (β :: α :: .prod α β :: Γ) υ) : Comp O I Γ υ :=
  bindV c fun p => letV (.fst (v p)) fun a => letV (.snd (v p)) fun b => k a b

def caseOptV {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt τ)) (n : Comp O I Γ υ)
    (s : Var (τ :: Γ) τ → Comp O I (τ :: Γ) υ) : Comp O I Γ υ :=
  .caseOpt e n (s .zero)

def caseSumV {Γ : List (Ty (e2eSig ℓ))} {α β υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.sum α β))
    (l : Var (α :: Γ) α → Comp O I (α :: Γ) υ)
    (r : Var (β :: Γ) β → Comp O I (β :: Γ) υ) : Comp O I Γ υ :=
  .caseSum e (l .zero) (r .zero)

def findMV {Γ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)} (K : ℕ)
    (l : Expr O Γ (.list τ)) (p : Var (τ :: Γ) τ → Comp O I (τ :: Γ) .bool) :
    Comp O I Γ (.opt τ) :=
  .findM K l (p .zero)

def anyMV {Γ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)} (K : ℕ)
    (l : Expr O Γ (.list τ)) (p : Var (τ :: Γ) τ → Comp O I (τ :: Γ) .bool) :
    Comp O I Γ .bool :=
  .anyM K l (p .zero)

def mapMV {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)} (K : ℕ)
    (l : Expr O Γ (.list τ)) (f : Var (τ :: Γ) τ → Comp O I (τ :: Γ) υ) :
    Comp O I Γ (.list υ) :=
  .mapM K l (f .zero)

@[dsl_cost, simp] theorem exprCostUB_eLet {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ τ) (k : Var (τ :: Γ) τ → Expr O (τ :: Γ) υ) :
    exprCostUB (eLet e k) = exprCostUB e + exprCostUB (k .zero) + 1 := rfl

@[dsl_cost, simp] theorem exprCostUB_eLet2 {Γ : List (Ty (e2eSig ℓ))} {α β υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.prod α β))
    (k : Var (α :: .prod α β :: Γ) α → Var (β :: α :: .prod α β :: Γ) β →
         Expr O (β :: α :: .prod α β :: Γ) υ) :
    exprCostUB (eLet2 e k) = exprCostUB e + (2 + (2 + exprCostUB (k .zero .zero) + 1) + 1) + 1 := rfl

@[dsl_cost, simp] theorem exprCostUB_eCaseOpt {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt τ)) (n : Expr O Γ υ) (s : Var (τ :: Γ) τ → Expr O (τ :: Γ) υ) :
    exprCostUB (eCaseOpt e n s) = exprCostUB e + (exprCostUB n + exprCostUB (s .zero)) + 1 := rfl

@[dsl_cost, simp] theorem exprCostUB_eCaseSum {Γ : List (Ty (e2eSig ℓ))} {α β υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.sum α β))
    (l : Var (α :: Γ) α → Expr O (α :: Γ) υ) (r : Var (β :: Γ) β → Expr O (β :: Γ) υ) :
    exprCostUB (eCaseSum e l r) = exprCostUB e + (exprCostUB (l .zero) + exprCostUB (r .zero)) + 1 := rfl

@[dsl_cost, simp] theorem exprCostUB_eFind {Γ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)} (K : ℕ)
    (l : Expr O Γ (.list τ)) (p : Var (τ :: Γ) τ → Expr O (τ :: Γ) .bool) :
    exprCostUB (eFind K l p) = exprCostUB l + K * (exprCostUB (p .zero) + 1) + 1 := rfl

@[dsl_cost, simp] theorem exprCostUB_eAny {Γ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)} (K : ℕ)
    (l : Expr O Γ (.list τ)) (p : Var (τ :: Γ) τ → Expr O (τ :: Γ) .bool) :
    exprCostUB (eAny K l p) = exprCostUB l + K * (exprCostUB (p .zero) + 1) + 1 := rfl

@[dsl_cost, simp] theorem exprCostUB_eMap {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)} (K : ℕ)
    (l : Expr O Γ (.list τ)) (f : Var (τ :: Γ) τ → Expr O (τ :: Γ) υ) :
    exprCostUB (eMap K l f) = exprCostUB l + K * (exprCostUB (f .zero) + 1) + 1 := rfl

@[dsl_cost, simp] theorem compCostUB_bindV {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    (c : Comp O I Γ τ) (k : Var (τ :: Γ) τ → Comp O I (τ :: Γ) υ) :
    compCostUB (bindV c k) = compCostUB c + compCostUB (k .zero) + 1 := rfl

@[dsl_cost, simp] theorem compCostUB_letV {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ τ) (k : Var (τ :: Γ) τ → Comp O I (τ :: Γ) υ) :
    compCostUB (letV (I := I) e k) = exprCostUB e + 1 + compCostUB (k .zero) + 1 := rfl

@[dsl_cost, simp] theorem compCostUB_bindV2 {Γ : List (Ty (e2eSig ℓ))} {α β υ : Ty (e2eSig ℓ)}
    (c : Comp O I Γ (.prod α β))
    (k : Var (α :: .prod α β :: Γ) α → Var (β :: α :: .prod α β :: Γ) β →
         Comp O I (β :: α :: .prod α β :: Γ) υ) :
    compCostUB (bindV2 c k) =
      compCostUB c + (2 + 1 + (2 + 1 + compCostUB (k .zero .zero) + 1) + 1) + 1 := rfl

@[dsl_cost, simp] theorem compCostUB_caseOptV {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt τ)) (n : Comp O I Γ υ) (s : Var (τ :: Γ) τ → Comp O I (τ :: Γ) υ) :
    compCostUB (caseOptV e n s) = exprCostUB e + (compCostUB n + compCostUB (s .zero)) + 1 := rfl

@[dsl_cost, simp] theorem compCostUB_caseSumV {Γ : List (Ty (e2eSig ℓ))} {α β υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.sum α β))
    (l : Var (α :: Γ) α → Comp O I (α :: Γ) υ) (r : Var (β :: Γ) β → Comp O I (β :: Γ) υ) :
    compCostUB (caseSumV e l r) = exprCostUB e + (compCostUB (l .zero) + compCostUB (r .zero)) + 1 := rfl

@[dsl_cost, simp] theorem compCostUB_findMV {Γ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)} (K : ℕ)
    (l : Expr O Γ (.list τ)) (p : Var (τ :: Γ) τ → Comp O I (τ :: Γ) .bool) :
    compCostUB (findMV K l p) = exprCostUB l + K * (compCostUB (p .zero) + 1) + 1 := rfl

@[dsl_cost, simp] theorem compCostUB_anyMV {Γ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)} (K : ℕ)
    (l : Expr O Γ (.list τ)) (p : Var (τ :: Γ) τ → Comp O I (τ :: Γ) .bool) :
    compCostUB (anyMV K l p) = exprCostUB l + K * (compCostUB (p .zero) + 1) + 1 := rfl

@[dsl_cost, simp] theorem compCostUB_mapMV {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)} (K : ℕ)
    (l : Expr O Γ (.list τ)) (f : Var (τ :: Γ) τ → Comp O I (τ :: Γ) υ) :
    compCostUB (mapMV K l f) = exprCostUB l + K * (compCostUB (f .zero) + 1) + 1 := rfl

@[dsl_cost, simp] theorem compQueriesUB_bindV (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    (c : Comp O I Γ τ) (k : Var (τ :: Γ) τ → Comp O I (τ :: Γ) υ) :
    compQueriesUB w ws (bindV c k) = compQueriesUB w ws c + compQueriesUB w ws (k .zero) := rfl

@[dsl_cost, simp] theorem compQueriesUB_letV (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ τ) (k : Var (τ :: Γ) τ → Comp O I (τ :: Γ) υ) :
    compQueriesUB w ws (letV (I := I) e k) = compQueriesUB w ws (k .zero) :=
  Nat.zero_add _

@[dsl_cost, simp] theorem compQueriesUB_bindV2 (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    {Γ : List (Ty (e2eSig ℓ))} {α β υ : Ty (e2eSig ℓ)}
    (c : Comp O I Γ (.prod α β))
    (k : Var (α :: .prod α β :: Γ) α → Var (β :: α :: .prod α β :: Γ) β →
         Comp O I (β :: α :: .prod α β :: Γ) υ) :
    compQueriesUB w ws (bindV2 c k) = compQueriesUB w ws c + compQueriesUB w ws (k .zero .zero) := by
  simp [bindV2]

@[dsl_cost, simp] theorem compQueriesUB_caseOptV (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt τ)) (n : Comp O I Γ υ) (s : Var (τ :: Γ) τ → Comp O I (τ :: Γ) υ) :
    compQueriesUB w ws (caseOptV e n s) = compQueriesUB w ws n + compQueriesUB w ws (s .zero) := rfl

@[dsl_cost, simp] theorem compQueriesUB_caseSumV (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    {Γ : List (Ty (e2eSig ℓ))} {α β υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.sum α β))
    (l : Var (α :: Γ) α → Comp O I (α :: Γ) υ) (r : Var (β :: Γ) β → Comp O I (β :: Γ) υ) :
    compQueriesUB w ws (caseSumV e l r) =
      compQueriesUB w ws (l .zero) + compQueriesUB w ws (r .zero) := rfl

@[dsl_cost, simp] theorem compQueriesUB_findMV (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    {Γ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)} (K : ℕ)
    (l : Expr O Γ (.list τ)) (p : Var (τ :: Γ) τ → Comp O I (τ :: Γ) .bool) :
    compQueriesUB w ws (findMV K l p) = K * compQueriesUB w ws (p .zero) := rfl

@[dsl_cost, simp] theorem compQueriesUB_anyMV (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    {Γ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)} (K : ℕ)
    (l : Expr O Γ (.list τ)) (p : Var (τ :: Γ) τ → Comp O I (τ :: Γ) .bool) :
    compQueriesUB w ws (anyMV K l p) = K * compQueriesUB w ws (p .zero) := rfl

@[dsl_cost, simp] theorem compQueriesUB_mapMV (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)} (K : ℕ)
    (l : Expr O Γ (.list τ)) (f : Var (τ :: Γ) τ → Comp O I (τ :: Γ) υ) :
    compQueriesUB w ws (mapMV K l f) = K * compQueriesUB w ws (f .zero) := rfl

end Binders

/-! ## Bounded list monadic helpers -/

theorem findML_pure {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (p : α → Bool) : ∀ (l : List α), findML (fun x => (pure (p x) : m Bool)) l = pure (l.find? p)
  | [] => rfl
  | x :: xs => by
    simp only [findML, List.find?]
    cases p x <;> simp [findML_pure p xs]

theorem anyML_pure {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (p : α → Bool) : ∀ (l : List α), anyML (fun x => (pure (p x) : m Bool)) l = pure (l.any p)
  | [] => rfl
  | x :: xs => by
    simp only [anyML, List.any_cons]
    cases p x <;> simp [anyML_pure p xs]

theorem mapML_pure {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (f : α → β) : ∀ (l : List α), mapML (fun x => (pure (f x) : m β)) l = pure (l.map f)
  | [] => rfl
  | x :: xs => by
    simp [mapML, mapML_pure f xs]

theorem findML_map {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (g : α → β) (p : β → m Bool) :
    ∀ (l : List α), findML p (l.map g) = Option.map g <$> findML (fun x => p (g x)) l
  | [] => by simp [findML]
  | x :: xs => by
    simp only [List.map_cons, findML, map_eq_bind_pure_comp, LawfulMonad.bind_assoc]
    congr 1
    funext b
    cases b
    · simpa [map_eq_bind_pure_comp] using findML_map g p xs
    · simp

theorem anyML_map {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (g : α → β) (p : β → m Bool) :
    ∀ (l : List α), anyML p (l.map g) = anyML (fun x => p (g x)) l
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, anyML]
    congr 1
    funext b
    cases b
    · exact anyML_map g p xs
    · rfl

theorem findML_congr {m : Type → Type} [Monad m] {α : Type}
    {p q : α → m Bool} {l : List α} (h : ∀ x ∈ l, p x = q x) :
    findML p l = findML q l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [findML, h x List.mem_cons_self]
    congr 1
    funext b
    cases b
    · exact ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    · rfl

theorem anyML_congr {m : Type → Type} [Monad m] {α : Type}
    {p q : α → m Bool} {l : List α} (h : ∀ x ∈ l, p x = q x) :
    anyML p l = anyML q l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [anyML, h x List.mem_cons_self]
    congr 1
    funext b
    cases b
    · exact ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    · rfl

@[simp] theorem liftP_pure {S : ReductionDsl.Sig} {ι : Type} {T : OracleSpec ι}
    (I : Iface S T) {α : Type} (x : α) :
    I.liftP (pure x) = pure x := by
  simp [Iface.liftP]

@[simp] theorem liftP_bind {S : ReductionDsl.Sig} {ι : Type} {T : OracleSpec ι}
    (I : Iface S T) {α β : Type} (p : ProbComp α) (k : α → ProbComp β) :
    I.liftP (p >>= k) = I.liftP p >>= fun x => I.liftP (k x) := by
  simp [Iface.liftP]

@[simp] theorem liftP_map {S : ReductionDsl.Sig} {ι : Type} {T : OracleSpec ι}
    (I : Iface S T) {α β : Type} (f : α → β) (p : ProbComp α) :
    I.liftP (f <$> p) = f <$> I.liftP p := by
  simp [Iface.liftP]

/-! ## Direct `ProbComp` interface and primitive hooks -/

/-- Coin-only `ReductionDsl` interface into `unifSpec` with uniform samplers `e2eSamplers ℓ`. -/
@[reducible] def e2eProbIface (ℓ : ℕ) : Iface (e2eSig ℓ) unifSpec where
  fwdU n := query (spec := unifSpec) n
  uCost := 1
  Tag := Empty
  dom := Empty.elim
  cod := Empty.elim
  enc := fun g => g.elim
  dec := fun g => g.elim
  qCost := Empty.elim
  smp := e2eSamplers ℓ

@[simp] theorem e2eProbIface_liftP {ℓ : ℕ} {α : Type} (p : ProbComp α) :
    (e2eProbIface ℓ).liftP p = p := by
  unfold Iface.liftP e2eProbIface
  exact simulateQ_id' p

@[reducible] def stepAIface (ℓ : ℕ) {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) :
    Iface (e2eSig ℓ) T :=
  { I₀ with smp := e2eSamplers ℓ }

/-- Hook bundle abstracting pure expressions, `E2ECryptoOp` calls, and uniform coin draws for
PQXDH branch programs. -/
structure E2EPqxdhHooks (ℓ : ℕ) (O : Ops (e2eSig ℓ)) {ι : Type} {T : OracleSpec ι}
    (I : Iface (e2eSig ℓ) T) where
  pureOp : ∀ {Γ : List (Ty (e2eSig ℓ))} (o : E2EPureOp),
    Expr O Γ (o.dom ℓ) → Expr O Γ (o.cod ℓ)
  callPrim : ∀ {Γ : List (Ty (e2eSig ℓ))} (o : E2ECryptoOp),
    Expr O Γ (o.dom ℓ) → Comp O I Γ (o.cod ℓ)
  sampBv256 : ∀ {Γ : List (Ty (e2eSig ℓ))}, Comp O I Γ BV256
  sampBool : ∀ {Γ : List (Ty (e2eSig ℓ))}, Comp O I Γ .bool

/-- Asserts that `H` issues zero target oracle queries under weight `w`. -/
structure HooksNoTargetQueries {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (e2eSig ℓ) T} (H : E2EPqxdhHooks ℓ O I) (w : I.Tag → ℕ) : Prop where
  callPrim_q : ∀ {Γ : List (Ty (e2eSig ℓ))} (o : E2ECryptoOp) (e : Expr O Γ (o.dom ℓ)),
    compQueriesUB w (fun _ => 0) (H.callPrim o e) = 0
  sampBv256_q : ∀ {Γ : List (Ty (e2eSig ℓ))},
    compQueriesUB w (fun _ => 0) (H.sampBv256 (Γ := Γ)) = 0
  sampBool_q : ∀ {Γ : List (Ty (e2eSig ℓ))},
    compQueriesUB w (fun _ => 0) (H.sampBool (Γ := Γ)) = 0

@[reducible] def mkStepAPqxdhHooks (ℓ : ℕ) {Pt : Type} (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) :
    E2EPqxdhHooks ℓ (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) where
  pureOp o e := e2ePureOp o e
  callPrim o e := .ret (e2eCryptoOp o e)
  sampBv256 :=
    Comp.sample (I := stepAIface ℓ I₀)
      (UniformSamplerTag.base E2EUnifBase.bv256) .unit
  sampBool :=
    Comp.sample (I := stepAIface ℓ I₀)
      UniformSamplerTag.bool .unit

theorem mkStepAPqxdhHooks_noQueries (ℓ : ℕ) {Pt : Type} (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (w : I₀.Tag → ℕ) :
    HooksNoTargetQueries (mkStepAPqxdhHooks ℓ P C K decT encT I₀) w :=
  ⟨fun _ _ => rfl, rfl, rfl⟩

@[dsl_cost, simp] theorem exprCostUB_e2ePureOp {ℓ : ℕ} {Pt : Type} {P : Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} (o : E2EPureOp)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (o.dom ℓ)) :
    exprCostUB (e2ePureOp o a) = exprCostUB a + o.cost ℓ := rfl

@[dsl_cost, simp] theorem exprCostUB_e2eCryptoOp {ℓ : ℕ} {Pt : Type} {P : Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} (o : E2ECryptoOp)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (o.dom ℓ)) :
    exprCostUB (e2eCryptoOp o a) = exprCostUB a + o.cost ℓ := rfl

/-! ## Value representations for `KeyIndState` -/

@[reducible] def e2ePrincipalEntryTy {ℓ : ℕ} : Ty (e2eSig ℓ) :=
  .prod (PB 32) (.prod (PB 32) (.prod (PB 32) (.prod (PB 32) .bool)))

@[simp] def e2ePrincipalEntryToVal {ℓ : ℕ} (p : PrincipalEntry) :
    (e2ePrincipalEntryTy (ℓ := ℓ)).denote :=
  (p.secIKA0, (p.ikAPk, (p.secIKAsign, (p.ikSignPk, p.corrupted))))

@[simp] def e2eValToPrincipalEntry {ℓ : ℕ} (v : (e2ePrincipalEntryTy (ℓ := ℓ)).denote) :
    PrincipalEntry :=
  ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2⟩

@[simp] theorem e2eValToPrincipalEntry_toVal {ℓ : ℕ} (p : PrincipalEntry) :
    e2eValToPrincipalEntry (e2ePrincipalEntryToVal (ℓ := ℓ) p) = p := by
  cases p; rfl

@[simp] theorem e2ePrincipalEntryToVal_ofVal {ℓ : ℕ} (v : (e2ePrincipalEntryTy (ℓ := ℓ)).denote) :
    e2ePrincipalEntryToVal (ℓ := ℓ) (e2eValToPrincipalEntry (ℓ := ℓ) v) = v := by
  rcases v with ⟨_, _, _, _, _⟩; rfl

@[reducible] def e2eSpkBundleEntryTy {ℓ : ℕ} : Ty (e2eSig ℓ) :=
  .prod (PB 32) (.prod (PB 32) (.prod (PB 64)
    (.prod (PB 3168) (.prod (PB 1568) (.prod (PB 64) .bool)))))

@[simp] def e2eSpkBundleEntryToVal {ℓ : ℕ} (b : SpkBundleEntry) :
    (e2eSpkBundleEntryTy (ℓ := ℓ)).denote :=
  (b.spkSk, (b.spkPk, (b.spkSig, (b.pqspkSk, (b.pqspkPk, (b.pqspkSig, b.revealed))))))

@[simp] def e2eValToSpkBundleEntry {ℓ : ℕ} (v : (e2eSpkBundleEntryTy (ℓ := ℓ)).denote) :
    SpkBundleEntry :=
  ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2⟩

@[simp] theorem e2eValToSpkBundleEntry_toVal {ℓ : ℕ} (b : SpkBundleEntry) :
    e2eValToSpkBundleEntry (e2eSpkBundleEntryToVal (ℓ := ℓ) b) = b := by
  cases b; rfl

@[simp] theorem e2eSpkBundleEntryToVal_ofVal {ℓ : ℕ} (v : (e2eSpkBundleEntryTy (ℓ := ℓ)).denote) :
    e2eSpkBundleEntryToVal (ℓ := ℓ) (e2eValToSpkBundleEntry (ℓ := ℓ) v) = v := by
  rcases v with ⟨_, _, _, _, _, _, _⟩; rfl

@[reducible] def e2eOpkEntryTy {ℓ : ℕ} : Ty (e2eSig ℓ) :=
  .prod (PB 32) (.prod (PB 32) .bool)

@[simp] def e2eOpkEntryToVal {ℓ : ℕ} (o : OpkEntry) : (e2eOpkEntryTy (ℓ := ℓ)).denote :=
  (o.opkSk, (o.opkPk, o.consumed))

@[simp] def e2eValToOpkEntry {ℓ : ℕ} (v : (e2eOpkEntryTy (ℓ := ℓ)).denote) : OpkEntry :=
  ⟨v.1, v.2.1, v.2.2⟩

@[simp] theorem e2eValToOpkEntry_toVal {ℓ : ℕ} (o : OpkEntry) :
    e2eValToOpkEntry (e2eOpkEntryToVal (ℓ := ℓ) o) = o := by
  cases o; rfl

@[simp] theorem e2eOpkEntryToVal_ofVal {ℓ : ℕ} (v : (e2eOpkEntryTy (ℓ := ℓ)).denote) :
    e2eOpkEntryToVal (ℓ := ℓ) (e2eValToOpkEntry (ℓ := ℓ) v) = v := by
  rcases v with ⟨_, _, _⟩; rfl

@[reducible] def e2eInitiatorEntryTy (ℓ : ℕ) (S : Setup) : Ty (e2eSig ℓ) :=
  .prod (sidT S) (.prod (.opt .nat) (.prod (PB 32) (.prod (PB 32) (.prod (.opt (PB 32))
    (.prod (PB 1568) (.prod .bool (.prod .bool (.prod .bool (.prod (PB 32) (.prod .bool
      (.prod drKeyT (.prod drKeyT (.prod hdrT (.prod .bool .bool))))))))))))))

@[simp] def e2eInitiatorEntryToVal {ℓ : ℕ} {S : Setup} (s : KeyIndInitiatorEntry S) :
    (e2eInitiatorEntryTy ℓ S).denote :=
  (sidV s.sid, (s.honestPeer, (s.peerIkPk, (s.peerSpkPk, (s.peerOpkPk?,
    (s.peerPqspkPk, (s.spkHonest, (s.opkHonest, (s.pqspkHonest, (s.ekASk, (s.fresh,
      (drKeyV s.drKeyReal, (drKeyV s.drKeyRand,
        (hdrV s.hdr, (s.tested, s.revealed)))))))))))))))

@[simp] def e2eValToInitiatorEntry {ℓ : ℕ} {S : Setup}
    (v : (e2eInitiatorEntryTy ℓ S).denote) : KeyIndInitiatorEntry S :=
  ⟨sidOfV v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1,
   v.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2.2.2.1,
   v.2.2.2.2.2.2.2.2.2.2.1, drKeyOfV (ℓ := ℓ) v.2.2.2.2.2.2.2.2.2.2.2.1,
   drKeyOfV (ℓ := ℓ) v.2.2.2.2.2.2.2.2.2.2.2.2.1,
   hdrOfV (ℓ := ℓ) v.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   v.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

@[simp] theorem e2eValToInitiatorEntry_toVal {ℓ : ℕ} {S : Setup} (s : KeyIndInitiatorEntry S) :
    e2eValToInitiatorEntry (e2eInitiatorEntryToVal (ℓ := ℓ) s) = s := by
  cases s
  simp

@[simp] theorem e2eInitiatorEntryToVal_ofVal {ℓ : ℕ} {S : Setup}
    (v : (e2eInitiatorEntryTy ℓ S).denote) :
    e2eInitiatorEntryToVal (ℓ := ℓ) (e2eValToInitiatorEntry v) = v := by
  rcases v with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  simp

@[reducible] def e2eRespEntryTy (ℓ : ℕ) (S : Setup) : Ty (e2eSig ℓ) :=
  .prod (sidT S) (.prod (PB 32) (.prod (PB 32) (.prod (.opt (PB 32)) (.prod (PB 1568)
    (.prod hdrT (.prod .bool (.prod drKeyT (.prod drKeyT (.prod .bool .bool)))))))))

@[simp] def e2eRespEntryToVal {ℓ : ℕ} {S : Setup} (r : KeyIndRespEntry S) :
    (e2eRespEntryTy ℓ S).denote :=
  (sidV r.sid, (r.respIkPk, (r.spkPk, (r.opkPk?, (r.pqspkPk,
    (hdrV r.hdr, (r.senderHonest,
      (drKeyV r.drKeyReal, (drKeyV r.drKeyRand, (r.tested, r.revealed))))))))))

@[simp] def e2eValToRespEntry {ℓ : ℕ} {S : Setup}
    (v : (e2eRespEntryTy ℓ S).denote) : KeyIndRespEntry S :=
  ⟨sidOfV v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1,
   hdrOfV (ℓ := ℓ) v.2.2.2.2.2.1, v.2.2.2.2.2.2.1,
   drKeyOfV (ℓ := ℓ) v.2.2.2.2.2.2.2.1, drKeyOfV (ℓ := ℓ) v.2.2.2.2.2.2.2.2.1,
   v.2.2.2.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2.2.2.2⟩

@[simp] theorem e2eValToRespEntry_toVal {ℓ : ℕ} {S : Setup} (r : KeyIndRespEntry S) :
    e2eValToRespEntry (e2eRespEntryToVal (ℓ := ℓ) r) = r := by
  cases r
  simp

@[simp] theorem e2eRespEntryToVal_ofVal {ℓ : ℕ} {S : Setup}
    (v : (e2eRespEntryTy ℓ S).denote) :
    e2eRespEntryToVal (ℓ := ℓ) (e2eValToRespEntry v) = v := by
  rcases v with ⟨_, _, _, _, _, _, _, _, _, _, _⟩
  simp

/-- `ReductionDsl` value representation of `SignalPqxdh.KeyIndState S`. -/
@[reducible] def e2eKeyIndStateTy (ℓ : ℕ) (S : Setup) : Ty (e2eSig ℓ) :=
  .prod .bool (.prod (.list (.prod .nat e2ePrincipalEntryTy))
    (.prod (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy))
      (.prod (.list (.prod (.prod .nat (.prod .nat .nat)) e2eOpkEntryTy))
        (.prod (.list (e2eInitiatorEntryTy ℓ S)) (.prod (.list (e2eRespEntryTy ℓ S))
          (.prod (.list (.prod .nat (.prod .nat .nat)))
            (.prod (.list (.prod .nat (.prod .nat .nat)))
              (.prod (.list (.prod .nat (.prod PU32 (.prod PU32 (PB 32)))))
                (.prod (.list (.prod (PB 192) drKeyT))
                       (.list (.prod (PB 32) (PB 32))))))))))))

@[simp] def e2eKeyIndStateToVal {ℓ : ℕ} {S : Setup} (st : KeyIndState S) :
    (e2eKeyIndStateTy ℓ S).denote :=
  (st.secb,
   (st.principals.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ))),
    (st.spkBundles.map (Prod.map id (e2eSpkBundleEntryToVal (ℓ := ℓ))),
     (st.opkEntries.map (Prod.map id (e2eOpkEntryToVal (ℓ := ℓ))),
      (st.sessions.map (e2eInitiatorEntryToVal (ℓ := ℓ)),
       (st.respSessions.map (e2eRespEntryToVal (ℓ := ℓ)),
        (st.usedRecvOPK,
         (st.usedRecvNoOPK,
          (st.seenKyberBaseKeys,
           (st.roCache.map (Prod.map id (drKeyV (ℓ := ℓ))),
            st.advKeys))))))))))

@[simp] def e2eValToKeyIndState {ℓ : ℕ} {S : Setup}
    (v : (e2eKeyIndStateTy ℓ S).denote) : KeyIndState S :=
  { secb := v.1
    principals := v.2.1.map (Prod.map id (e2eValToPrincipalEntry (ℓ := ℓ)))
    spkBundles := v.2.2.1.map (Prod.map id (e2eValToSpkBundleEntry (ℓ := ℓ)))
    opkEntries := v.2.2.2.1.map (Prod.map id (e2eValToOpkEntry (ℓ := ℓ)))
    sessions := v.2.2.2.2.1.map (e2eValToInitiatorEntry (ℓ := ℓ))
    respSessions := v.2.2.2.2.2.1.map (e2eValToRespEntry (ℓ := ℓ))
    usedRecvOPK := v.2.2.2.2.2.2.1
    usedRecvNoOPK := v.2.2.2.2.2.2.2.1
    seenKyberBaseKeys := v.2.2.2.2.2.2.2.2.1
    roCache := v.2.2.2.2.2.2.2.2.2.1.map (Prod.map id (drKeyOfV (ℓ := ℓ)))
    advKeys := v.2.2.2.2.2.2.2.2.2.2 }

@[simp] theorem e2eValToKeyIndState_toVal {ℓ : ℕ} {S : Setup} (st : KeyIndState S) :
    e2eValToKeyIndState (e2eKeyIndStateToVal (ℓ := ℓ) st) = st := by
  cases st
  simp [List.map_map, Function.comp_def, Prod.map]

@[simp] theorem e2eKeyIndStateToVal_ofVal {ℓ : ℕ} {S : Setup}
    (v : (e2eKeyIndStateTy ℓ S).denote) :
    e2eKeyIndStateToVal (ℓ := ℓ) (e2eValToKeyIndState v) = v := by
  rcases v with ⟨_, _, _, _, _, _, _, _, _, _, _⟩
  simp [List.map_map, Function.comp_def, Prod.map]

/-! ## State-length invariants -/

def isInitSid {S : Setup} : SessionId S → Bool
  | .sendOPK _ _ => true
  | .sendNoOPK _ _ => true
  | .recvOPK _ _ _ => false
  | .recvNoOPK _ _ _ => false

/-- Inductive replication-bound invariant on `KeyIndState S` along `pqxdhKeyIndImpl1KeyReal`. -/
structure KeyIndSetupBounded (S : Setup) (st : KeyIndState S) : Prop where
  principals_nodup : (st.principals.map Prod.fst).Nodup
  principals_lt : ∀ p ∈ st.principals, p.1 < S.N_id
  spkBundles_nodup : (st.spkBundles.map Prod.fst).Nodup
  spkBundles_lt : ∀ b ∈ st.spkBundles, b.1.1 < S.N_id ∧ b.1.2 < S.N_recv
  opkEntries_nodup : (st.opkEntries.map Prod.fst).Nodup
  opkEntries_lt : ∀ o ∈ st.opkEntries, o.1.1 < S.N_id ∧ o.1.2.1 < S.N_recv ∧ o.1.2.2 < S.N_opk
  sessions_nodup : (st.sessions.map KeyIndInitiatorEntry.sid).Nodup
  sessions_init : ∀ s ∈ st.sessions, isInitSid s.sid = true
  usedRecvOPK_nodup : st.usedRecvOPK.Nodup
  usedRecvOPK_lt : ∀ x ∈ st.usedRecvOPK, x.1 < S.N_id ∧ x.2.1 < S.N_recv ∧ x.2.2 < S.N_opk
  usedRecvNoOPK_nodup : st.usedRecvNoOPK.Nodup
  usedRecvNoOPK_lt : ∀ x ∈ st.usedRecvNoOPK, x.1 < S.N_id ∧ x.2.1 < S.N_recv ∧ x.2.2 < S.N_no_opk
  resp_le : st.respSessions.length ≤ st.usedRecvOPK.length + st.usedRecvNoOPK.length
  seen_le : st.seenKyberBaseKeys.length ≤ st.usedRecvOPK.length + st.usedRecvNoOPK.length
  roCache_nil : st.roCache = []

private theorem mul_add_lt {u j A B : ℕ} (hu : u < A) (hj : j < B) : u * B + j < A * B := by
  have h1 : (u + 1) * B ≤ A * B := Nat.mul_le_mul_right B hu
  rw [Nat.add_one_mul] at h1
  omega

private theorem mul_add_inj {u₁ j₁ u₂ j₂ B : ℕ} (hj₁ : j₁ < B) (hj₂ : j₂ < B)
    (heq : u₁ * B + j₁ = u₂ * B + j₂) : u₁ = u₂ ∧ j₁ = j₂ := by
  rcases Nat.lt_trichotomy u₁ u₂ with hlt | rfl | hgt
  · have h1 : (u₁ + 1) * B ≤ u₂ * B := Nat.mul_le_mul_right B hlt
    rw [Nat.add_one_mul] at h1
    omega
  · exact ⟨rfl, by omega⟩
  · have h1 : (u₂ + 1) * B ≤ u₁ * B := Nat.mul_le_mul_right B hgt
    rw [Nat.add_one_mul] at h1
    omega

private theorem nodup_lt_length_le {l : List ℕ} {N : ℕ}
    (hnd : l.Nodup) (hlt : ∀ x ∈ l, x < N) : l.length ≤ N := by
  have hmap : (l.attach.map fun ⟨x, hx⟩ => (⟨x, hlt x hx⟩ : Fin N)).Nodup := by
    rw [List.nodup_map_iff_inj_on (l.nodup_attach.mpr hnd)]
    intro ⟨a, _⟩ _ ⟨b, _⟩ _ hab
    exact Subtype.ext (Fin.mk.inj hab)
  simpa using hmap.length_le_card

private theorem nodup_pair_length_le {l : List (ℕ × ℕ)} {A B : ℕ}
    (hnd : l.Nodup) (hlt : ∀ p ∈ l, p.1 < A ∧ p.2 < B) : l.length ≤ A * B := by
  let enc : ℕ × ℕ → ℕ := fun p => p.1 * B + p.2
  have hnd' : (l.map enc).Nodup := by
    rw [List.nodup_map_iff_inj_on hnd]
    intro ⟨u₁, j₁⟩ h₁ ⟨u₂, j₂⟩ h₂ heq
    obtain ⟨eu, ej⟩ := mul_add_inj (hlt _ h₁).2 (hlt _ h₂).2 heq
    exact Prod.ext eu ej
  have hlt' : ∀ n ∈ l.map enc, n < A * B := by
    intro n hn
    rcases List.mem_map.mp hn with ⟨p, hp, rfl⟩
    exact mul_add_lt (hlt p hp).1 (hlt p hp).2
  simpa using nodup_lt_length_le hnd' hlt'

private theorem nodup_triple_length_le {l : List (ℕ × ℕ × ℕ)} {A B C : ℕ}
    (hnd : l.Nodup) (hlt : ∀ t ∈ l, t.1 < A ∧ t.2.1 < B ∧ t.2.2 < C) :
    l.length ≤ (A * B) * C := by
  let toPair : ℕ × ℕ × ℕ → ℕ × ℕ := fun t => (t.1 * B + t.2.1, t.2.2)
  have hnd' : (l.map toPair).Nodup := by
    rw [List.nodup_map_iff_inj_on hnd]
    intro ⟨u₁, j₁, o₁⟩ h₁ ⟨u₂, j₂, o₂⟩ h₂ heq
    have hp := Prod.mk.inj heq
    obtain ⟨eu, ej⟩ := mul_add_inj (hlt _ h₁).2.1 (hlt _ h₂).2.1 hp.1
    exact Prod.ext eu (Prod.ext ej hp.2)
  have hlt' : ∀ p ∈ l.map toPair, p.1 < A * B ∧ p.2 < C := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨t, ht, rfl⟩
    exact ⟨mul_add_lt (hlt t ht).1 (hlt t ht).2.1, (hlt t ht).2.2⟩
  simpa using nodup_pair_length_le hnd' hlt'

namespace KeyIndSetupBounded

theorem empty (S : Setup) (secb : Bool) : KeyIndSetupBounded S (KeyIndState.empty S secb) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
    simp [KeyIndState.empty]

theorem principals_le {S : Setup} {st : KeyIndState S} (h : KeyIndSetupBounded S st) :
    st.principals.length ≤ S.N_id := by
  have hlt : ∀ x ∈ st.principals.map Prod.fst, x < S.N_id := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
    exact h.principals_lt p hp
  simpa using nodup_lt_length_le h.principals_nodup hlt

theorem spkBundles_le {S : Setup} {st : KeyIndState S} (h : KeyIndSetupBounded S st) :
    st.spkBundles.length ≤ S.N_spk_tot := by
  have hlt : ∀ x ∈ st.spkBundles.map Prod.fst, x.1 < S.N_id ∧ x.2 < S.N_recv := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨b, hb, rfl⟩
    exact h.spkBundles_lt b hb
  simpa [Setup.N_spk_tot] using nodup_pair_length_le h.spkBundles_nodup hlt

theorem opkEntries_le {S : Setup} {st : KeyIndState S} (h : KeyIndSetupBounded S st) :
    st.opkEntries.length ≤ S.N_opk_tot := by
  have hlt : ∀ x ∈ st.opkEntries.map Prod.fst, x.1 < S.N_id ∧ x.2.1 < S.N_recv ∧ x.2.2 < S.N_opk := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨o, ho, rfl⟩
    exact h.opkEntries_lt o ho
  simpa [Setup.N_opk_tot, Setup.N_spk_tot] using nodup_triple_length_le h.opkEntries_nodup hlt

theorem usedRecvOPK_le {S : Setup} {st : KeyIndState S} (h : KeyIndSetupBounded S st) :
    st.usedRecvOPK.length ≤ S.N_opk_tot := by
  simpa [Setup.N_opk_tot, Setup.N_spk_tot] using
    nodup_triple_length_le h.usedRecvOPK_nodup h.usedRecvOPK_lt

theorem usedRecvNoOPK_le {S : Setup} {st : KeyIndState S} (h : KeyIndSetupBounded S st) :
    st.usedRecvNoOPK.length ≤ S.N_no_opk_tot := by
  simpa [Setup.N_no_opk_tot, Setup.N_spk_tot] using
    nodup_triple_length_le h.usedRecvNoOPK_nodup h.usedRecvNoOPK_lt

theorem respSessions_le {S : Setup} {st : KeyIndState S} (h : KeyIndSetupBounded S st) :
    st.respSessions.length ≤ S.N_recv_tot := by
  have h1 := h.usedRecvOPK_le
  have h2 := h.usedRecvNoOPK_le
  have h3 := h.resp_le
  unfold Setup.N_recv_tot
  omega

theorem seenKyberBaseKeys_le {S : Setup} {st : KeyIndState S} (h : KeyIndSetupBounded S st) :
    st.seenKyberBaseKeys.length ≤ S.N_recv_tot := by
  have h1 := h.usedRecvOPK_le
  have h2 := h.usedRecvNoOPK_le
  have h3 := h.seen_le
  unfold Setup.N_recv_tot
  omega

theorem sessions_le {S : Setup} {st : KeyIndState S} (h : KeyIndSetupBounded S st) :
    st.sessions.length ≤ S.N_send_tot := by
  let encSid : SessionId S → ℕ := fun
    | .sendOPK u i => u.val * S.N_send_opk + i.val
    | .sendNoOPK u i => S.N_send_opk_tot + (u.val * S.N_send_no_opk + i.val)
    | .recvOPK _ _ _ => 0
    | .recvNoOPK _ _ _ => 0
  have hinit : ∀ sid ∈ st.sessions.map KeyIndInitiatorEntry.sid, isInitSid sid = true := by
    intro sid hsid
    rcases List.mem_map.mp hsid with ⟨s, hs, rfl⟩
    exact h.sessions_init s hs
  have hnd' : ((st.sessions.map KeyIndInitiatorEntry.sid).map encSid).Nodup := by
    rw [List.nodup_map_iff_inj_on h.sessions_nodup]
    intro a ha b hb heq
    have hia := hinit a ha
    have hib := hinit b hb
    cases a with
    | recvOPK _ _ _ => simp [isInitSid] at hia
    | recvNoOPK _ _ _ => simp [isInitSid] at hia
    | sendOPK ua ia =>
      have hlt_a : ua.val * S.N_send_opk + ia.val < S.N_send_opk_tot :=
        mul_add_lt ua.isLt ia.isLt
      cases b with
      | recvOPK _ _ _ => simp [isInitSid] at hib
      | recvNoOPK _ _ _ => simp [isInitSid] at hib
      | sendOPK ub ib =>
        dsimp [encSid] at heq
        obtain ⟨eu, ei⟩ := mul_add_inj ia.isLt ib.isLt heq
        exact congrArg₂ SessionId.sendOPK (Fin.ext eu) (Fin.ext ei)
      | sendNoOPK ub ib =>
        dsimp [encSid] at heq
        omega
    | sendNoOPK ua ia =>
      cases b with
      | recvOPK _ _ _ => simp [isInitSid] at hib
      | recvNoOPK _ _ _ => simp [isInitSid] at hib
      | sendOPK ub ib =>
        have hlt_b : ub.val * S.N_send_opk + ib.val < S.N_send_opk_tot :=
          mul_add_lt ub.isLt ib.isLt
        dsimp [encSid] at heq
        omega
      | sendNoOPK ub ib =>
        dsimp [encSid] at heq
        have heq' : ua.val * S.N_send_no_opk + ia.val = ub.val * S.N_send_no_opk + ib.val := by
          omega
        obtain ⟨eu, ei⟩ := mul_add_inj ia.isLt ib.isLt heq'
        exact congrArg₂ SessionId.sendNoOPK (Fin.ext eu) (Fin.ext ei)
  have hlt' : ∀ n ∈ (st.sessions.map KeyIndInitiatorEntry.sid).map encSid, n < S.N_send_tot := by
    intro n hn
    rcases List.mem_map.mp hn with ⟨sid, hsid, rfl⟩
    have hi := hinit sid hsid
    cases sid with
    | recvOPK _ _ _ => simp [isInitSid] at hi
    | recvNoOPK _ _ _ => simp [isInitSid] at hi
    | sendOPK u i =>
      have h1 : u.val * S.N_send_opk + i.val < S.N_send_opk_tot := mul_add_lt u.isLt i.isLt
      dsimp [encSid, Setup.N_send_tot]
      omega
    | sendNoOPK u i =>
      have h1 : u.val * S.N_send_no_opk + i.val < S.N_send_no_opk_tot := mul_add_lt u.isLt i.isLt
      dsimp [encSid, Setup.N_send_tot]
      omega
  simpa using nodup_lt_length_le hnd' hlt'

theorem roCache_length {S : Setup} {st : KeyIndState S} (h : KeyIndSetupBounded S st) :
    st.roCache.length = 0 := by
  simp [h.roCache_nil]

end KeyIndSetupBounded

private theorem checkAndMark_length_le (used : List (ℕ × UInt32 × UInt32 × SignalPqxdh.Bytes))
    (k : ℕ) (p s : UInt32) (ek : SignalPqxdh.Bytes) :
    (checkAndMarkKyberBaseKeySeen used k p s ek).2.length ≤ used.length + 1 := by
  unfold checkAndMarkKyberBaseKeySeen
  dsimp only
  split_ifs <;> simp

private theorem st_run_pure {σ : Type} {m : Type → Type} [Monad m] {α : Type}
    (a : α) (s : σ) :
    (pure a : StateT σ m α).run s = pure (a, s) := rfl

private theorem st_run_get_bind {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (k : σ → StateT σ m α) (s : σ) :
    (MonadState.get >>= k).run s = (k s).run s := by
  change (pure (s, s) >>= fun x => (k x.1).run x.2) = (k s).run s
  exact pure_bind (s, s) _

private theorem st_run_getOf_bind {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α : Type} (k : σ → StateT σ m α) (s : σ) :
    (MonadStateOf.get >>= k).run s = (k s).run s := by
  change (pure (s, s) >>= fun x => (k x.1).run x.2) = (k s).run s
  exact pure_bind (s, s) _

private theorem st_run_set_bind {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (s' : σ) (k : PUnit → StateT σ m α) (s : σ) :
    (MonadStateOf.set s' >>= k).run s = (k PUnit.unit).run s' := by
  change (pure (PUnit.unit, s') >>= fun x => (k x.1).run x.2) = (k PUnit.unit).run s'
  exact pure_bind (PUnit.unit, s') (fun x => (k x.1).run x.2)

private theorem st_run_set {σ : Type} {m : Type → Type} [Monad m]
    (s' s : σ) :
    (MonadStateOf.set s' : StateT σ m PUnit).run s = pure (PUnit.unit, s') := rfl

private theorem st_run_lift {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α : Type} (x : m α) (s : σ) :
    (liftM x : StateT σ m α).run s = (fun a => (a, s)) <$> x := by
  change (x >>= fun a => pure (a, s)) = (fun a => (a, s)) <$> x
  rw [map_eq_bind_pure_comp]; rfl

private theorem st_run_lift_bind {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (x : m α) (k : α → StateT σ m β) (s : σ) :
    ((liftM x : StateT σ m α) >>= k).run s = (x >>= fun a => (k a).run s) := by
  change ((x >>= fun a => pure (a, s)) >>= fun p => (k p.1).run p.2) =
    (x >>= fun a => (k a).run s)
  simp only [LawfulMonad.bind_assoc, pure_bind]

private theorem st_run_bind {σ : Type} {m : Type → Type} [Monad m]
    {α β : Type} (x : StateT σ m α) (k : α → StateT σ m β) (s : σ) :
    (x >>= k).run s = (x.run s >>= fun p => (k p.1).run p.2) := rfl

private theorem st_run_ite {σ : Type} {m : Type → Type} {α : Type}
    (c : Prop) [Decidable c] (a b : StateT σ m α) (s : σ) :
    (if c then a else b).run s = if c then a.run s else b.run s := by
  split_ifs <;> rfl

set_option linter.unusedSimpArgs false in
private theorem runKeyIndInitiate_false_preserves {S : Setup} {P : Primitives}
    {sid : SessionId S} (hsid : isInitSid sid = true) {u : Fin S.N_id}
    {bundle : PreKeyBundleInput} {st : KeyIndState S} (hst : KeyIndSetupBounded S st)
    {out : KeyIndResponse × KeyIndState S}
    (hmem : out ∈ support ((runKeyIndInitiate false S P sid u bundle).run st)) :
    KeyIndSetupBounded S out.2 ∧ out.2.advKeys.length = st.advKeys.length := by
  unfold runKeyIndInitiate evalHkdfOrRo at hmem
  simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
    LawfulMonad.bind_assoc] at hmem
  by_cases hdup : (st.sessions.any (fun e => e.sid == sid)) = true
  · simp only [hdup, ite_true, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact ⟨hst, rfl⟩
  · simp only [hdup, ite_false] at hmem
    rcases hfind : st.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨_, uEntry⟩
    · rw [hfind] at hmem; dsimp only at hmem
      simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨hst, rfl⟩
    · rw [hfind] at hmem; dsimp only at hmem
      simp only [st_run_ite, st_run_pure] at hmem
      by_cases hkosk : (!koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle) = true
      · simp only [hkosk, ite_true, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact ⟨hst, rfl⟩
      · simp only [hkosk, Bool.false_eq_true, ↓reduceIte, ite_false, st_run_lift_bind, st_run_ite,
          st_run_pure, LawfulMonad.bind_assoc, MonadAttach.mem_support_bind] at hmem
        rcases hmem with ⟨ekASk, _, kemCoins, _, hmem⟩
        by_cases hsig : (!(P.sigVerify (resolveSigPk P st.principals bundle.ikB)
            (encodeEC bundle.spkB) bundle.spkSig &&
            P.sigVerify (resolveSigPk P st.principals bundle.ikB)
            (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
        · simp only [hsig, ↓reduceIte, ite_true, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact ⟨hst, rfl⟩
        · simp only [hsig, Bool.false_eq_true, ↓reduceIte, ite_false] at hmem
          rcases henc : P.kemEncaps bundle.pqspkB kemCoins with _ | ⟨ss, kemCt⟩
          · rw [henc] at hmem; dsimp only at hmem
            simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
            subst hmem; exact ⟨hst, rfl⟩
          · rw [henc] at hmem; dsimp only at hmem
            simp only [Bool.not_false, ↓reduceIte, ite_true, LawfulMonad.bind_assoc, pure_bind,
              st_run_get_bind, st_run_getOf_bind, st_run_lift_bind, st_run_lift, st_run_set_bind,
              st_run_pure, map_pure, MonadAttach.mem_support_bind, support_pure,
              Set.mem_singleton_iff, exists_eq_left] at hmem
            have hnotmem : sid ∉ st.sessions.map KeyIndInitiatorEntry.sid := by
              intro hm
              rcases List.mem_map.mp hm with ⟨e, he, rfl⟩
              exact hdup (List.any_eq_true.mpr ⟨e, he, by simp⟩)
            have hex :
                ∃ drKeyRand,
                  out.2 =
                    { st with
                      sessions :=
                        { sid := sid,
                          honestPeer := isHonestUncorruptedPeer P st.principals bundle.ikB,
                          peerIkPk := bundle.ikB, peerSpkPk := bundle.spkB,
                          peerOpkPk? := bundle.opkB?.map Prod.snd,
                          peerPqspkPk := bundle.pqspkB,
                          spkHonest :=
                            (checkBundleProvenance P st.principals st.spkBundles
                              st.opkEntries bundle).1,
                          opkHonest :=
                            (checkBundleProvenance P st.principals st.spkBundles
                              st.opkEntries bundle).2.1,
                          pqspkHonest :=
                            (checkBundleProvenance P st.principals st.spkBundles
                              st.opkEntries bundle).2.2,
                          ekASk := ekASk,
                          fresh := (isHonestUncorruptedPeer P st.principals bundle.ikB).isSome,
                          drKeyReal := P.hkdfDerive96
                            (buildSecrets (P.x25519 uEntry.secIKA0 bundle.spkB)
                              (P.x25519 ekASk bundle.ikB)
                              (P.x25519 ekASk bundle.spkB)
                              (bundle.opkB?.map fun x => P.x25519 ekASk x.2) ss),
                          drKeyRand := drKeyRand,
                          hdr := { ikAPk := uEntry.ikAPk, ekAPk := P.x25519Base ekASk,
                                   spkId := bundle.spkId, opkId? := bundle.opkB?.map Prod.fst,
                                   pqspkId := bundle.pqspkId, kemCt := kemCt },
                          tested := false } :: st.sessions,
                      roCache := st.roCache } := by
              rcases hkr : keyIndPartnerRandKey? P st.respSessions _ with _ | drKeyRand
              · rw [hkr] at hmem; dsimp only at hmem
                simp only [st_run_lift_bind, st_run_set_bind, LawfulMonad.bind_assoc,
                  MonadAttach.mem_support_bind] at hmem
                rcases hmem with ⟨dkR, _, hmem⟩
                refine ⟨dkR, ?_⟩
                split at hmem <;>
                  · simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
                    rw [hmem]
              · rw [hkr] at hmem; dsimp only at hmem
                simp only [pure_bind, st_run_set_bind, LawfulMonad.bind_assoc] at hmem
                refine ⟨drKeyRand, ?_⟩
                split at hmem <;>
                  · simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
                    rw [hmem]
            rcases hex with ⟨drKeyRand, hst_out⟩
            rw [hst_out]
            refine ⟨{ hst with
              sessions_nodup := by
                simp only [List.map_cons]
                exact List.nodup_cons.mpr ⟨hnotmem, hst.sessions_nodup⟩
              sessions_init := by
                intro s hs
                rcases List.mem_cons.mp hs with rfl | hs'
                · exact hsid
                · exact hst.sessions_init s hs'
              roCache_nil := hst.roCache_nil }, rfl⟩

set_option linter.unusedSimpArgs false in
/-- Every `pqxdhKeyIndImpl1KeyReal` query preserves `KeyIndSetupBounded` and grows `advKeys` by at
most `1`. -/
theorem pqxdhKeyIndImpl1KeyReal_preserves_setupBounded {S : Setup} {P : Primitives}
    (q : KeyIndQuery S) {st : KeyIndState S} (hst : KeyIndSetupBounded S st)
    {out : KeyIndResponse × KeyIndState S}
    (hmem : out ∈ support ((pqxdhKeyIndImpl1KeyReal S P q).run st)) :
    KeyIndSetupBounded S out.2 ∧
      out.2.advKeys.length ≤ st.advKeys.length + 1 ∧
      ((∀ sk, q ≠ .registerKey sk) → out.2.advKeys.length = st.advKeys.length) := by
  cases q with
  | initPrin u =>
    unfold pqxdhKeyIndImpl1KeyReal at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
      LawfulMonad.bind_assoc] at hmem
    by_cases hdup : (st.principals.any (fun (idx, _) => idx == u.val)) = true
    · simp only [hdup, ite_true, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
    · simp only [hdup, Bool.false_eq_true, ↓reduceIte, ite_false, st_run_lift_bind, st_run_set_bind,
        st_run_pure, LawfulMonad.bind_assoc, MonadAttach.mem_support_bind, support_pure,
        Set.mem_singleton_iff] at hmem
      rcases hmem with ⟨sec, _, rfl⟩
      have hnotmem : u.val ∉ st.principals.map Prod.fst := by
        intro hm
        rcases List.mem_map.mp hm with ⟨⟨idx, e⟩, he, hEq⟩
        dsimp only at hEq
        subst hEq
        exact hdup (List.any_eq_true.mpr ⟨(u.val, e), he, by simp⟩)
      refine ⟨{ hst with
        principals_nodup := List.nodup_cons.mpr ⟨hnotmem, hst.principals_nodup⟩
        principals_lt := fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact u.isLt
          · exact hst.principals_lt p hp' }, Nat.le_succ _, fun _ => rfl⟩
  | roQuery secrets =>
    unfold pqxdhKeyIndImpl1KeyReal evalHkdfOrRo at hmem
    simp only [Bool.not_false, ↓reduceIte, ite_true, LawfulMonad.bind_assoc, pure_bind,
      st_run_get_bind, st_run_getOf_bind, st_run_lift_bind, st_run_lift, st_run_set_bind,
      st_run_pure, map_pure, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff, exists_eq_left] at hmem
    subst hmem
    exact ⟨{ hst with roCache_nil := hst.roCache_nil }, Nat.le_succ _, fun _ => rfl⟩
  | revealDhSecrets =>
    unfold pqxdhKeyIndImpl1KeyReal at hmem
    simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
  | corruptIK u =>
    unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, LawfulMonad.bind_assoc] at hmem
    rcases hfind : st.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨_, entry⟩
    · rw [hfind] at hmem; dsimp only at hmem
      simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
    · rw [hfind] at hmem; dsimp only at hmem
      simp only [st_run_set_bind, st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      have hfst :
          (st.principals.map (fun (idx, e) =>
            if idx == u.val then (idx, { e with corrupted := true }) else (idx, e))).map Prod.fst =
          st.principals.map Prod.fst := by
        rw [List.map_map]
        apply List.map_congr_left
        intro ⟨idx, e⟩ _; dsimp; split_ifs <;> rfl
      refine ⟨{ hst with
        principals_nodup := by rw [hfst]; exact hst.principals_nodup
        principals_lt := fun p hp => by
          rcases List.mem_map.mp hp with ⟨⟨idx, e⟩, he, hpEq⟩
          split_ifs at hpEq <;> subst hpEq <;> exact hst.principals_lt (idx, e) he },
        Nat.le_succ _, fun _ => rfl⟩
  | genSPK u j =>
    unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
      LawfulMonad.bind_assoc] at hmem
    by_cases hdup : (st.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
    · simp only [hdup, ↓reduceIte, ite_true, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
    · simp only [hdup, Bool.false_eq_true, ↓reduceIte, ite_false] at hmem
      rcases hfind : st.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨_, uEntry⟩
      · rw [hfind] at hmem; dsimp only at hmem
        simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
      · rw [hfind] at hmem; dsimp only at hmem
        simp only [st_run_lift_bind, st_run_lift, st_run_set_bind, st_run_pure,
          LawfulMonad.bind_assoc, map_eq_bind_pure_comp, Function.comp_def,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hmem
        rcases hmem with ⟨spkSk, _, rSpk, _, ⟨pqPk, pqSk⟩, _, rPq, _, rfl⟩
        have hnotmem : (u.val, j.val) ∉ st.spkBundles.map Prod.fst := by
          intro hm
          rcases List.mem_map.mp hm with ⟨⟨k, b⟩, hb, hEq⟩
          dsimp only at hEq
          subst hEq
          exact hdup (List.any_eq_true.mpr ⟨((u.val, j.val), b), hb, by simp⟩)
        refine ⟨{ hst with
          spkBundles_nodup := List.nodup_cons.mpr ⟨hnotmem, hst.spkBundles_nodup⟩
          spkBundles_lt := fun b hb => by
            rcases List.mem_cons.mp hb with rfl | hb'
            · exact ⟨u.isLt, j.isLt⟩
            · exact hst.spkBundles_lt b hb' }, Nat.le_succ _, fun _ => rfl⟩
  | genOPK u j o =>
    unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
      LawfulMonad.bind_assoc] at hmem
    by_cases hdup : (st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))) = true
    · simp only [hdup, ↓reduceIte, ite_true, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
    · simp only [hdup, Bool.false_eq_true, ↓reduceIte, ite_false, st_run_lift_bind, st_run_set_bind,
        st_run_pure, LawfulMonad.bind_assoc, MonadAttach.mem_support_bind, support_pure,
        Set.mem_singleton_iff] at hmem
      rcases hmem with ⟨opkSk, _, rfl⟩
      have hnotmem : (u.val, j.val, o.val) ∉ st.opkEntries.map Prod.fst := by
        intro hm
        rcases List.mem_map.mp hm with ⟨⟨k, e⟩, he, hEq⟩
        dsimp only at hEq
        subst hEq
        exact hdup (List.any_eq_true.mpr ⟨((u.val, j.val, o.val), e), he, by simp⟩)
      refine ⟨{ hst with
        opkEntries_nodup := List.nodup_cons.mpr ⟨hnotmem, hst.opkEntries_nodup⟩
        opkEntries_lt := fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact ⟨u.isLt, j.isLt, o.isLt⟩
          · exact hst.opkEntries_lt x hx' }, Nat.le_succ _, fun _ => rfl⟩
  | initiateOPK u i bundle =>
    unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
      LawfulMonad.bind_assoc] at hmem
    by_cases hopk : bundle.opkB?.isNone = true
    · simp only [hopk, ite_true, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
    · simp only [hopk, ite_false] at hmem
      obtain ⟨hb, hadv⟩ := runKeyIndInitiate_false_preserves (sid := .sendOPK u i) rfl hst hmem
      exact ⟨hb, by omega, fun _ => hadv⟩
  | initiateNoOPK u i bundle =>
    unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
      LawfulMonad.bind_assoc] at hmem
    by_cases hopk : bundle.opkB?.isSome = true
    · simp only [hopk, ite_true, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
    · simp only [hopk, ite_false] at hmem
      obtain ⟨hb, hadv⟩ := runKeyIndInitiate_false_preserves (sid := .sendNoOPK u i) rfl hst hmem
      exact ⟨hb, by omega, fun _ => hadv⟩
  | acceptOPK k j o hdr =>
    unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl evalHkdfOrRo recordKeyIndResp at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
      LawfulMonad.bind_assoc] at hmem
    by_cases hhdr : (!(hdr.spkId == UInt32.ofNat j.val &&
         hdr.pqspkId == UInt32.ofNat j.val &&
         hdr.opkId? == some (UInt32.ofNat o.val) &&
         hdr.ikAPk.length == 32 &&
         hdr.ekAPk.length == 32)) = true
    · simp only [hhdr, ite_true, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
    · simp only [hhdr, ite_false] at hmem
      by_cases hused : (st.usedRecvOPK.contains (k.val, j.val, o.val)) = true
      · simp only [hused, ite_true, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
      · simp only [hused, ite_false] at hmem
        by_cases hkosk : (!koskSenderOk P st.principals st.advKeys hdr.ikAPk) = true
        · simp only [hkosk, ite_true, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
        · simp only [hkosk, ite_false] at hmem
          rcases hp : st.principals.find? (fun (idx, _) => idx == k.val) with _ | ⟨_, kEntry⟩
          · rw [hp] at hmem; dsimp only at hmem
            simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
            subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
          · rw [hp] at hmem; dsimp only at hmem
            rcases hb : st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with _ | ⟨_, bEntry⟩
            · rw [hb] at hmem; dsimp only at hmem
              simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
              subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
            · rw [hb] at hmem; dsimp only at hmem
              rcases ho : st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
                  _ | ⟨_, oEntry⟩
              · rw [ho] at hmem; dsimp only at hmem
                simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
                subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
              · rw [ho] at hmem; dsimp only at hmem
                simp only [st_run_ite, st_run_pure] at hmem
                by_cases hcons : oEntry.consumed = true
                · simp only [hcons, ite_true, support_pure, Set.mem_singleton_iff] at hmem
                  subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
                · simp only [hcons, ite_false] at hmem
                  rcases hacc : acceptKeys P _ with _ | dk0
                  · rw [hacc] at hmem; dsimp only at hmem
                    simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
                    subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
                  · rw [hacc] at hmem; dsimp only at hmem
                    rcases hdec : P.kemDecaps bEntry.pqspkSk hdr.kemCt with _ | ss
                    · rw [hdec] at hmem; dsimp only at hmem
                      simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
                      subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
                    · rw [hdec] at hmem; dsimp only at hmem
                      simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false,
                        LawfulMonad.bind_assoc, pure_bind, st_run_get_bind, st_run_getOf_bind,
                        st_run_lift_bind, st_run_lift, st_run_set_bind, st_run_set,
                        st_run_pure, map_pure, MonadAttach.mem_support_bind, support_pure,
                        Set.mem_singleton_iff, exists_eq_left] at hmem
                      set stR : KeyIndState S :=
                        { st with
                          opkEntries := st.opkEntries.map (fun (idx, e) =>
                            if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true })
                            else (idx, e))
                          usedRecvOPK := (k.val, j.val, o.val) :: st.usedRecvOPK
                          seenKyberBaseKeys :=
                            (checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys
                              k.val hdr.pqspkId hdr.spkId hdr.ekAPk).2
                          roCache := st.roCache }
                      have hex :
                          ∃ drKeyRand,
                            out.2 =
                              { stR with
                                respSessions :=
                                  { sid := .recvOPK k j o, respIkPk := kEntry.ikAPk,
                                    spkPk := bEntry.spkPk, opkPk? := some oEntry.opkPk,
                                    pqspkPk := bEntry.pqspkPk, hdr := hdr,
                                    senderHonest := (findHonestPrincipal P st.principals hdr.ikAPk).isSome,
                                    drKeyReal := P.hkdfDerive96
                                      (buildSecrets (P.x25519 bEntry.spkSk hdr.ikAPk)
                                        (P.x25519 kEntry.secIKA0 hdr.ekAPk)
                                        (P.x25519 bEntry.spkSk hdr.ekAPk)
                                        (some (P.x25519 oEntry.opkSk hdr.ekAPk)) ss),
                                    drKeyRand := drKeyRand } :: stR.respSessions } := by
                        rcases hpart : stR.sessions.find? (fun s => keyIndPartner P s _) with
                          _ | partner
                        · rw [hpart] at hmem; dsimp only at hmem
                          simp only [st_run_lift_bind, st_run_set_bind, LawfulMonad.bind_assoc,
                            MonadAttach.mem_support_bind] at hmem
                          rcases hmem with ⟨dkR, _, hmem⟩
                          refine ⟨dkR, ?_⟩
                          split at hmem <;>
                            · simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
                              rw [hmem]
                        · rw [hpart] at hmem; dsimp only at hmem
                          simp only [pure_bind, st_run_set_bind, LawfulMonad.bind_assoc] at hmem
                          refine ⟨partner.drKeyRand, ?_⟩
                          split at hmem <;>
                            · simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
                              rw [hmem]
                      rcases hex with ⟨drKeyRand, hout⟩
                      rw [hout]
                      have hnotmem : (k.val, j.val, o.val) ∉ st.usedRecvOPK := by
                        intro hm
                        exact hused (List.contains_iff_mem.mpr hm)
                      have hopk_fst :
                          (st.opkEntries.map (fun (idx, e) =>
                            if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true })
                            else (idx, e))).map Prod.fst =
                          st.opkEntries.map Prod.fst := by
                        rw [List.map_map]
                        apply List.map_congr_left
                        intro ⟨idx, e⟩ _; dsimp; split_ifs <;> rfl
                      have hseen := checkAndMark_length_le st.seenKyberBaseKeys
                        k.val hdr.pqspkId hdr.spkId hdr.ekAPk
                      have hresp_prev := hst.resp_le
                      have hseen_prev := hst.seen_le
                      refine ⟨{ hst with
                        opkEntries_nodup := by
                          dsimp only [stR]; rw [hopk_fst]; exact hst.opkEntries_nodup
                        opkEntries_lt := fun x hx => by
                          dsimp only [stR] at hx
                          rcases List.mem_map.mp hx with ⟨⟨idx, e⟩, he, hxEq⟩
                          split_ifs at hxEq <;> subst hxEq <;> exact hst.opkEntries_lt (idx, e) he
                        usedRecvOPK_nodup := List.nodup_cons.mpr ⟨hnotmem, hst.usedRecvOPK_nodup⟩
                        usedRecvOPK_lt := fun x hx => by
                          dsimp only [stR] at hx
                          rcases List.mem_cons.mp hx with rfl | hx'
                          · exact ⟨k.isLt, j.isLt, o.isLt⟩
                          · exact hst.usedRecvOPK_lt x hx'
                        resp_le := by dsimp only [stR]; simp only [List.length_cons]; omega
                        seen_le := by dsimp only [stR]; simp only [List.length_cons]; omega
                        roCache_nil := hst.roCache_nil }, Nat.le_succ _, fun _ => rfl⟩
  | acceptNoOPK k j l hdr =>
    unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl evalHkdfOrRo recordKeyIndResp at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
      LawfulMonad.bind_assoc] at hmem
    by_cases hhdr : (!(hdr.spkId == UInt32.ofNat j.val &&
         hdr.pqspkId == UInt32.ofNat j.val &&
         hdr.opkId? == none &&
         hdr.ikAPk.length == 32 &&
         hdr.ekAPk.length == 32)) = true
    · simp only [hhdr, ite_true, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
    · simp only [hhdr, ite_false] at hmem
      by_cases hused : (st.usedRecvNoOPK.contains (k.val, j.val, l.val)) = true
      · simp only [hused, ite_true, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
      · simp only [hused, ite_false] at hmem
        by_cases hkosk : (!koskSenderOk P st.principals st.advKeys hdr.ikAPk) = true
        · simp only [hkosk, ite_true, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
        · simp only [hkosk, ite_false] at hmem
          rcases hp : st.principals.find? (fun (idx, _) => idx == k.val) with _ | ⟨_, kEntry⟩
          · rw [hp] at hmem; dsimp only at hmem
            simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
            subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
          · rw [hp] at hmem; dsimp only at hmem
            rcases hb : st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with _ | ⟨_, bEntry⟩
            · rw [hb] at hmem; dsimp only at hmem
              simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
              subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
            · rw [hb] at hmem; dsimp only at hmem
              rcases hacc : acceptKeys P _ with _ | dk0
              · rw [hacc] at hmem; dsimp only at hmem
                simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
                subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
              · rw [hacc] at hmem; dsimp only at hmem
                rcases hdec : P.kemDecaps bEntry.pqspkSk hdr.kemCt with _ | ss
                · rw [hdec] at hmem; dsimp only at hmem
                  simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
                  subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
                · rw [hdec] at hmem; dsimp only at hmem
                  simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false,
                    LawfulMonad.bind_assoc, pure_bind, st_run_get_bind, st_run_getOf_bind,
                    st_run_lift_bind, st_run_lift, st_run_set_bind, st_run_set,
                    st_run_pure, map_pure, MonadAttach.mem_support_bind, support_pure,
                    Set.mem_singleton_iff, exists_eq_left] at hmem
                  set stR : KeyIndState S :=
                    { st with
                      usedRecvNoOPK := (k.val, j.val, l.val) :: st.usedRecvNoOPK
                      seenKyberBaseKeys :=
                        (checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys
                          k.val hdr.pqspkId hdr.spkId hdr.ekAPk).2
                      roCache := st.roCache }
                  have hex :
                      ∃ drKeyRand,
                        out.2 =
                          { stR with
                            respSessions :=
                              { sid := .recvNoOPK k j l, respIkPk := kEntry.ikAPk,
                                spkPk := bEntry.spkPk, opkPk? := none,
                                pqspkPk := bEntry.pqspkPk, hdr := hdr,
                                senderHonest := (findHonestPrincipal P st.principals hdr.ikAPk).isSome,
                                drKeyReal := P.hkdfDerive96
                                  (buildSecrets (P.x25519 bEntry.spkSk hdr.ikAPk)
                                    (P.x25519 kEntry.secIKA0 hdr.ekAPk)
                                    (P.x25519 bEntry.spkSk hdr.ekAPk) none ss),
                                drKeyRand := drKeyRand } :: stR.respSessions } := by
                    rcases hpart : stR.sessions.find? (fun s => keyIndPartner P s _) with
                      _ | partner
                    · rw [hpart] at hmem; dsimp only at hmem
                      simp only [st_run_lift_bind, st_run_set_bind, LawfulMonad.bind_assoc,
                        MonadAttach.mem_support_bind] at hmem
                      rcases hmem with ⟨dkR, _, hmem⟩
                      refine ⟨dkR, ?_⟩
                      split at hmem <;>
                        · simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
                          rw [hmem]
                    · rw [hpart] at hmem; dsimp only at hmem
                      simp only [pure_bind, st_run_set_bind, LawfulMonad.bind_assoc] at hmem
                      refine ⟨partner.drKeyRand, ?_⟩
                      split at hmem <;>
                        · simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
                          rw [hmem]
                  rcases hex with ⟨drKeyRand, hout⟩
                  rw [hout]
                  have hnotmem : (k.val, j.val, l.val) ∉ st.usedRecvNoOPK := by
                    intro hm
                    exact hused (List.contains_iff_mem.mpr hm)
                  have hseen := checkAndMark_length_le st.seenKyberBaseKeys
                    k.val hdr.pqspkId hdr.spkId hdr.ekAPk
                  have hresp_prev := hst.resp_le
                  have hseen_prev := hst.seen_le
                  refine ⟨{ hst with
                    usedRecvNoOPK_nodup := List.nodup_cons.mpr ⟨hnotmem, hst.usedRecvNoOPK_nodup⟩
                    usedRecvNoOPK_lt := fun x hx => by
                      dsimp only [stR] at hx
                      rcases List.mem_cons.mp hx with rfl | hx'
                      · exact ⟨k.isLt, j.isLt, l.isLt⟩
                      · exact hst.usedRecvNoOPK_lt x hx'
                    resp_le := by dsimp only [stR]; simp only [List.length_cons]; omega
                    seen_le := by dsimp only [stR]; simp only [List.length_cons]; omega
                    roCache_nil := hst.roCache_nil }, Nat.le_succ _, fun _ => rfl⟩
  | testSession sid =>
    unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
      LawfulMonad.bind_assoc] at hmem
    by_cases htest : (!isKeyIndSessionTestable st sid) = true
    · simp only [htest, ite_true, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
    · simp only [htest, ite_false] at hmem
      rcases hs : st.sessions.find? (fun e => e.sid == sid) with _ | e
      · rw [hs] at hmem; dsimp only at hmem
        rcases hr : st.respSessions.find? (fun r => r.sid == sid) with _ | r
        · rw [hr] at hmem; dsimp only at hmem
          simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
        · rw [hr] at hmem; dsimp only at hmem
          simp only [st_run_set_bind, st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem
          refine ⟨{ hst with resp_le := by simpa using hst.resp_le },
            Nat.le_succ _, fun _ => rfl⟩
      · rw [hs] at hmem; dsimp only at hmem
        simp only [st_run_set_bind, st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem
        have hsid_map :
            (st.sessions.map (fun s => if s.sid == sid then { s with tested := true } else s)).map
              KeyIndInitiatorEntry.sid =
            st.sessions.map KeyIndInitiatorEntry.sid := by
          rw [List.map_map]
          apply List.map_congr_left
          intro s _; dsimp; split_ifs <;> rfl
        refine ⟨{ hst with
          sessions_nodup := by rw [hsid_map]; exact hst.sessions_nodup
          sessions_init := fun s hs' => by
            rcases List.mem_map.mp hs' with ⟨s₀, hs₀, hEq⟩
            split_ifs at hEq <;> subst hEq <;> exact hst.sessions_init s₀ hs₀ },
          Nat.le_succ _, fun _ => rfl⟩
  | revealSessionKey sid =>
    unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, LawfulMonad.bind_assoc] at hmem
    rcases hs : st.sessions.find? (fun e => e.sid == sid) with _ | e
    · rw [hs] at hmem; dsimp only at hmem
      rcases hr : st.respSessions.find? (fun r => r.sid == sid) with _ | r
      · rw [hr] at hmem; dsimp only at hmem
        simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
      · rw [hr] at hmem; dsimp only at hmem
        simp only [st_run_ite, st_run_pure] at hmem
        by_cases hrt : r.tested = true
        · simp only [hrt, ite_true, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
        · simp only [hrt, ite_false, st_run_set_bind, st_run_pure,
            support_pure, Set.mem_singleton_iff] at hmem
          subst hmem
          refine ⟨{ hst with resp_le := by simpa using hst.resp_le },
            Nat.le_succ _, fun _ => rfl⟩
    · rw [hs] at hmem; dsimp only at hmem
      simp only [st_run_ite, st_run_pure] at hmem
      by_cases het : e.tested = true
      · simp only [het, ite_true, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
      · simp only [het, ite_false, st_run_set_bind, st_run_pure,
          support_pure, Set.mem_singleton_iff] at hmem
        subst hmem
        have hsid_map :
            (st.sessions.map (fun s => if s.sid == sid then { s with revealed := true } else s)).map
              KeyIndInitiatorEntry.sid =
            st.sessions.map KeyIndInitiatorEntry.sid := by
          rw [List.map_map]
          apply List.map_congr_left
          intro s _; dsimp; split_ifs <;> rfl
        refine ⟨{ hst with
          sessions_nodup := by rw [hsid_map]; exact hst.sessions_nodup
          sessions_init := fun s hs' => by
            rcases List.mem_map.mp hs' with ⟨s₀, hs₀, hEq⟩
            split_ifs at hEq <;> subst hEq <;> exact hst.sessions_init s₀ hs₀ },
          Nat.le_succ _, fun _ => rfl⟩
  | revealSpkSk u j =>
    unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, LawfulMonad.bind_assoc] at hmem
    rcases hb : st.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with _ | ⟨_, bEntry⟩
    · rw [hb] at hmem; dsimp only at hmem
      simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨hst, Nat.le_succ _, fun _ => rfl⟩
    · rw [hb] at hmem; dsimp only at hmem
      simp only [st_run_set_bind, st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      have hfst :
          (st.spkBundles.map (fun (idx, b) =>
            if idx == (u.val, j.val) then (idx, { b with revealed := true }) else (idx, b))).map
              Prod.fst =
          st.spkBundles.map Prod.fst := by
        rw [List.map_map]
        apply List.map_congr_left
        intro ⟨idx, b⟩ _; dsimp; split_ifs <;> rfl
      refine ⟨{ hst with
        spkBundles_nodup := by rw [hfst]; exact hst.spkBundles_nodup
        spkBundles_lt := fun b hb' => by
          rcases List.mem_map.mp hb' with ⟨⟨idx, b₀⟩, hb₀, hEq⟩
          split_ifs at hEq <;> subst hEq <;> exact hst.spkBundles_lt (idx, b₀) hb₀ },
        Nat.le_succ _, fun _ => rfl⟩
  | registerKey sk =>
    unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, LawfulMonad.bind_assoc] at hmem
    rcases hreg : registerAdvKey P st.advKeys sk with _ | ⟨pk, advKeys'⟩
    · rw [hreg] at hmem; dsimp only at hmem
      simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      exact ⟨hst, Nat.le_succ _, fun hne => absurd rfl (hne sk)⟩
    · rw [hreg] at hmem; dsimp only at hmem
      simp only [st_run_set_bind, st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      have hlen : advKeys'.length ≤ st.advKeys.length + 1 := by
        unfold registerAdvKey at hreg
        split_ifs at hreg
        injection hreg with hpair
        injection hpair with _ hadv
        subst hadv
        simp
      exact ⟨{ hst with roCache_nil := hst.roCache_nil },
        hlen, fun hne => absurd rfl (hne sk)⟩

/-- Reachable list-length invariant on `KeyIndState S` after at most `nFuel` queries of
`pqxdhKeyIndImpl1KeyReal`. -/
structure stListBounded (S : Setup) (nFuel : ℕ) (st : KeyIndState S) : Prop where
  setup : KeyIndSetupBounded S st
  principals_fuel_le : st.principals.length ≤ nFuel
  spkBundles_fuel_le : st.spkBundles.length ≤ nFuel
  opkEntries_fuel_le : st.opkEntries.length ≤ nFuel
  sessions_fuel_le : st.sessions.length ≤ nFuel
  respSessions_fuel_le : st.respSessions.length ≤ nFuel
  usedRecvOPK_fuel_le : st.usedRecvOPK.length ≤ nFuel
  usedRecvNoOPK_fuel_le : st.usedRecvNoOPK.length ≤ nFuel
  seenKyberBaseKeys_fuel_le : st.seenKyberBaseKeys.length ≤ nFuel
  advKeys_le : st.advKeys.length ≤ nFuel

namespace stListBounded

theorem empty (S : Setup) (nFuel : ℕ) (secb : Bool) :
    stListBounded S nFuel (KeyIndState.empty S secb) := by
  refine ⟨KeyIndSetupBounded.empty S secb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [KeyIndState.empty]

theorem mono {S : Setup} {nFuel nFuel' : ℕ} {st : KeyIndState S}
    (h : stListBounded S nFuel st) (hle : nFuel ≤ nFuel') :
    stListBounded S nFuel' st :=
  ⟨h.setup,
   h.principals_fuel_le.trans hle,
   h.spkBundles_fuel_le.trans hle,
   h.opkEntries_fuel_le.trans hle,
   h.sessions_fuel_le.trans hle,
   h.respSessions_fuel_le.trans hle,
   h.usedRecvOPK_fuel_le.trans hle,
   h.usedRecvNoOPK_fuel_le.trans hle,
   h.seenKyberBaseKeys_fuel_le.trans hle,
   h.advKeys_le.trans hle⟩

theorem principals_le {S : Setup} {nFuel : ℕ} {st : KeyIndState S}
    (h : stListBounded S nFuel st) :
    st.principals.length ≤ min nFuel S.N_id :=
  Nat.le_min.mpr ⟨h.principals_fuel_le, h.setup.principals_le⟩

theorem spkBundles_le {S : Setup} {nFuel : ℕ} {st : KeyIndState S}
    (h : stListBounded S nFuel st) :
    st.spkBundles.length ≤ min nFuel S.N_spk_tot :=
  Nat.le_min.mpr ⟨h.spkBundles_fuel_le, h.setup.spkBundles_le⟩

theorem opkEntries_le {S : Setup} {nFuel : ℕ} {st : KeyIndState S}
    (h : stListBounded S nFuel st) :
    st.opkEntries.length ≤ min nFuel S.N_opk_tot :=
  Nat.le_min.mpr ⟨h.opkEntries_fuel_le, h.setup.opkEntries_le⟩

theorem sessions_le {S : Setup} {nFuel : ℕ} {st : KeyIndState S}
    (h : stListBounded S nFuel st) :
    st.sessions.length ≤ min nFuel S.N_send_tot :=
  Nat.le_min.mpr ⟨h.sessions_fuel_le, h.setup.sessions_le⟩

theorem respSessions_le {S : Setup} {nFuel : ℕ} {st : KeyIndState S}
    (h : stListBounded S nFuel st) :
    st.respSessions.length ≤ min nFuel S.N_recv_tot :=
  Nat.le_min.mpr ⟨h.respSessions_fuel_le, h.setup.respSessions_le⟩

theorem usedRecvOPK_le {S : Setup} {nFuel : ℕ} {st : KeyIndState S}
    (h : stListBounded S nFuel st) :
    st.usedRecvOPK.length ≤ min nFuel S.N_opk_tot :=
  Nat.le_min.mpr ⟨h.usedRecvOPK_fuel_le, h.setup.usedRecvOPK_le⟩

theorem usedRecvNoOPK_le {S : Setup} {nFuel : ℕ} {st : KeyIndState S}
    (h : stListBounded S nFuel st) :
    st.usedRecvNoOPK.length ≤ min nFuel S.N_no_opk_tot :=
  Nat.le_min.mpr ⟨h.usedRecvNoOPK_fuel_le, h.setup.usedRecvNoOPK_le⟩

theorem seenKyberBaseKeys_le {S : Setup} {nFuel : ℕ} {st : KeyIndState S}
    (h : stListBounded S nFuel st) :
    st.seenKyberBaseKeys.length ≤ min nFuel S.N_recv_tot :=
  Nat.le_min.mpr ⟨h.seenKyberBaseKeys_fuel_le, h.setup.seenKyberBaseKeys_le⟩

end stListBounded

def KeyIndSetupBounded.maxFuel (S : Setup) (st : KeyIndState S) : ℕ :=
  max st.advKeys.length
    (max S.N_id (max S.N_spk_tot (max S.N_opk_tot
      (max S.N_send_tot (max S.N_recv_tot S.N_no_opk_tot)))))

theorem KeyIndSetupBounded.toStListBounded {S : Setup} {st : KeyIndState S}
    (h : KeyIndSetupBounded S st) :
    stListBounded S (KeyIndSetupBounded.maxFuel S st) st := by
  refine ⟨h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.principals_le.trans (by unfold maxFuel; omega)
  · exact h.spkBundles_le.trans (by unfold maxFuel; omega)
  · exact h.opkEntries_le.trans (by unfold maxFuel; omega)
  · exact h.sessions_le.trans (by unfold maxFuel; omega)
  · exact h.respSessions_le.trans (by unfold maxFuel; omega)
  · exact h.usedRecvOPK_le.trans (by unfold maxFuel; omega)
  · exact h.usedRecvNoOPK_le.trans (by unfold maxFuel; omega)
  · exact h.seenKyberBaseKeys_le.trans (by unfold maxFuel; omega)
  · unfold maxFuel; omega

private def stepListLengthsLe {S : Setup} (st st' : KeyIndState S) : Prop :=
  st'.principals.length ≤ st.principals.length + 1 ∧
  st'.spkBundles.length ≤ st.spkBundles.length + 1 ∧
  st'.opkEntries.length ≤ st.opkEntries.length + 1 ∧
  st'.sessions.length ≤ st.sessions.length + 1 ∧
  st'.respSessions.length ≤ st.respSessions.length + 1 ∧
  st'.usedRecvOPK.length ≤ st.usedRecvOPK.length + 1 ∧
  st'.usedRecvNoOPK.length ≤ st.usedRecvNoOPK.length + 1 ∧
  st'.seenKyberBaseKeys.length ≤ st.seenKyberBaseKeys.length + 1

private theorem stepListLengthsLe_refl {S : Setup} (st : KeyIndState S) :
    stepListLengthsLe st st := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

set_option linter.unusedSimpArgs false in
private theorem runKeyIndInitiate_false_stepLengths {S : Setup} {P : Primitives}
    {sid : SessionId S} {u : Fin S.N_id} {bundle : PreKeyBundleInput} {st : KeyIndState S}
    {out : KeyIndResponse × KeyIndState S}
    (hmem : out ∈ support ((runKeyIndInitiate false S P sid u bundle).run st)) :
    stepListLengthsLe st out.2 := by
  unfold runKeyIndInitiate evalHkdfOrRo at hmem
  simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
    LawfulMonad.bind_assoc] at hmem
  by_cases hdup : (st.sessions.any (fun e => e.sid == sid)) = true
  · simp only [hdup, ite_true, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact stepListLengthsLe_refl st
  · simp only [hdup, ite_false] at hmem
    rcases hfind : st.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨_, uEntry⟩
    · rw [hfind] at hmem; dsimp only at hmem
      simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact stepListLengthsLe_refl st
    · rw [hfind] at hmem; dsimp only at hmem
      simp only [st_run_ite, st_run_pure] at hmem
      by_cases hkosk : (!koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle) = true
      · simp only [hkosk, ite_true, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact stepListLengthsLe_refl st
      · simp only [hkosk, Bool.false_eq_true, ↓reduceIte, ite_false, st_run_lift_bind, st_run_ite,
          st_run_pure, LawfulMonad.bind_assoc, MonadAttach.mem_support_bind] at hmem
        rcases hmem with ⟨ekASk, _, kemCoins, _, hmem⟩
        by_cases hsig : (!(P.sigVerify (resolveSigPk P st.principals bundle.ikB)
            (encodeEC bundle.spkB) bundle.spkSig &&
            P.sigVerify (resolveSigPk P st.principals bundle.ikB)
            (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
        · simp only [hsig, ↓reduceIte, ite_true, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact stepListLengthsLe_refl st
        · simp only [hsig, Bool.false_eq_true, ↓reduceIte, ite_false] at hmem
          rcases henc : P.kemEncaps bundle.pqspkB kemCoins with _ | ⟨ss, kemCt⟩
          · rw [henc] at hmem; dsimp only at hmem
            simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
            subst hmem; exact stepListLengthsLe_refl st
          · rw [henc] at hmem; dsimp only at hmem
            simp only [Bool.not_false, ↓reduceIte, ite_true, LawfulMonad.bind_assoc, pure_bind,
              st_run_get_bind, st_run_getOf_bind, st_run_lift_bind, st_run_lift, st_run_set_bind,
              st_run_pure, map_pure, MonadAttach.mem_support_bind, support_pure,
              Set.mem_singleton_iff, exists_eq_left] at hmem
            rcases hkr : keyIndPartnerRandKey? P st.respSessions _ with _ | drKeyRand
            · rw [hkr] at hmem; dsimp only at hmem
              simp only [st_run_lift_bind, st_run_set_bind, LawfulMonad.bind_assoc,
                MonadAttach.mem_support_bind] at hmem
              rcases hmem with ⟨dkR, _, hmem⟩
              split at hmem <;>
                · simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
                  subst hmem
                  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
            · rw [hkr] at hmem; dsimp only at hmem
              simp only [pure_bind, st_run_set_bind, LawfulMonad.bind_assoc] at hmem
              split at hmem <;>
                · simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
                  subst hmem
                  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp

set_option linter.unusedSimpArgs false in
private theorem pqxdhKeyIndImpl1KeyReal_stepLengths {S : Setup} {P : Primitives}
    (q : KeyIndQuery S) {st : KeyIndState S}
    {out : KeyIndResponse × KeyIndState S}
    (hmem : out ∈ support ((pqxdhKeyIndImpl1KeyReal S P q).run st)) :
    stepListLengthsLe st out.2 := by
  cases q with
  | initPrin u =>
    unfold pqxdhKeyIndImpl1KeyReal at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
      LawfulMonad.bind_assoc] at hmem
    by_cases hdup : (st.principals.any (fun (idx, _) => idx == u.val)) = true
    · simp only [hdup, ite_true, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact stepListLengthsLe_refl st
    · simp only [hdup, Bool.false_eq_true, ↓reduceIte, ite_false, st_run_lift_bind, st_run_set_bind,
        st_run_pure, LawfulMonad.bind_assoc, MonadAttach.mem_support_bind, support_pure,
        Set.mem_singleton_iff] at hmem
      rcases hmem with ⟨sec, _, rfl⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  | roQuery secrets =>
    unfold pqxdhKeyIndImpl1KeyReal evalHkdfOrRo at hmem
    simp only [Bool.not_false, ↓reduceIte, ite_true, LawfulMonad.bind_assoc, pure_bind,
      st_run_get_bind, st_run_getOf_bind, st_run_lift_bind, st_run_lift, st_run_set_bind,
      st_run_pure, map_pure, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff, exists_eq_left] at hmem
    subst hmem
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  | revealDhSecrets =>
    unfold pqxdhKeyIndImpl1KeyReal at hmem
    simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact stepListLengthsLe_refl st
  | corruptIK u =>
    unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, LawfulMonad.bind_assoc] at hmem
    rcases hfind : st.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨_, entry⟩
    · rw [hfind] at hmem; dsimp only at hmem
      simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact stepListLengthsLe_refl st
    · rw [hfind] at hmem; dsimp only at hmem
      simp only [st_run_set_bind, st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  | genSPK u j =>
    unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
      LawfulMonad.bind_assoc] at hmem
    by_cases hdup : (st.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
    · simp only [hdup, ↓reduceIte, ite_true, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact stepListLengthsLe_refl st
    · simp only [hdup, Bool.false_eq_true, ↓reduceIte, ite_false] at hmem
      rcases hfind : st.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨_, uEntry⟩
      · rw [hfind] at hmem; dsimp only at hmem
        simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact stepListLengthsLe_refl st
      · rw [hfind] at hmem; dsimp only at hmem
        simp only [st_run_lift_bind, st_run_lift, st_run_set_bind, st_run_pure,
          LawfulMonad.bind_assoc, map_eq_bind_pure_comp, Function.comp_def,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hmem
        rcases hmem with ⟨spkSk, _, rSpk, _, ⟨pqPk, pqSk⟩, _, rPq, _, rfl⟩
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  | genOPK u j o =>
    unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
      LawfulMonad.bind_assoc] at hmem
    by_cases hdup : (st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))) = true
    · simp only [hdup, ↓reduceIte, ite_true, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact stepListLengthsLe_refl st
    · simp only [hdup, Bool.false_eq_true, ↓reduceIte, ite_false, st_run_lift_bind, st_run_set_bind,
        st_run_pure, LawfulMonad.bind_assoc, MonadAttach.mem_support_bind, support_pure,
        Set.mem_singleton_iff] at hmem
      rcases hmem with ⟨opkSk, _, rfl⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  | initiateOPK u i bundle =>
    unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
      LawfulMonad.bind_assoc] at hmem
    by_cases hopk : bundle.opkB?.isNone = true
    · simp only [hopk, ite_true, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact stepListLengthsLe_refl st
    · simp only [hopk, ite_false] at hmem
      exact runKeyIndInitiate_false_stepLengths hmem
  | initiateNoOPK u i bundle =>
    unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
      LawfulMonad.bind_assoc] at hmem
    by_cases hopk : bundle.opkB?.isSome = true
    · simp only [hopk, ite_true, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact stepListLengthsLe_refl st
    · simp only [hopk, ite_false] at hmem
      exact runKeyIndInitiate_false_stepLengths hmem
  | acceptOPK k j o hdr =>
    unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl evalHkdfOrRo recordKeyIndResp at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
      LawfulMonad.bind_assoc] at hmem
    by_cases hhdr : (!(hdr.spkId == UInt32.ofNat j.val &&
         hdr.pqspkId == UInt32.ofNat j.val &&
         hdr.opkId? == some (UInt32.ofNat o.val) &&
         hdr.ikAPk.length == 32 &&
         hdr.ekAPk.length == 32)) = true
    · simp only [hhdr, ite_true, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact stepListLengthsLe_refl st
    · simp only [hhdr, ite_false] at hmem
      by_cases hused : (st.usedRecvOPK.contains (k.val, j.val, o.val)) = true
      · simp only [hused, ite_true, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact stepListLengthsLe_refl st
      · simp only [hused, ite_false] at hmem
        by_cases hkosk : (!koskSenderOk P st.principals st.advKeys hdr.ikAPk) = true
        · simp only [hkosk, ite_true, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact stepListLengthsLe_refl st
        · simp only [hkosk, ite_false] at hmem
          rcases hp : st.principals.find? (fun (idx, _) => idx == k.val) with _ | ⟨_, kEntry⟩
          · rw [hp] at hmem; dsimp only at hmem
            simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
            subst hmem; exact stepListLengthsLe_refl st
          · rw [hp] at hmem; dsimp only at hmem
            rcases hb : st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with _ | ⟨_, bEntry⟩
            · rw [hb] at hmem; dsimp only at hmem
              simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
              subst hmem; exact stepListLengthsLe_refl st
            · rw [hb] at hmem; dsimp only at hmem
              rcases ho : st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
                  _ | ⟨_, oEntry⟩
              · rw [ho] at hmem; dsimp only at hmem
                simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
                subst hmem; exact stepListLengthsLe_refl st
              · rw [ho] at hmem; dsimp only at hmem
                simp only [st_run_ite, st_run_pure] at hmem
                by_cases hcons : oEntry.consumed = true
                · simp only [hcons, ite_true, support_pure, Set.mem_singleton_iff] at hmem
                  subst hmem; exact stepListLengthsLe_refl st
                · simp only [hcons, ite_false] at hmem
                  rcases hacc : acceptKeys P _ with _ | dk0
                  · rw [hacc] at hmem; dsimp only at hmem
                    simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
                    subst hmem; exact stepListLengthsLe_refl st
                  · rw [hacc] at hmem; dsimp only at hmem
                    rcases hdec : P.kemDecaps bEntry.pqspkSk hdr.kemCt with _ | ss
                    · rw [hdec] at hmem; dsimp only at hmem
                      simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
                      subst hmem; exact stepListLengthsLe_refl st
                    · rw [hdec] at hmem; dsimp only at hmem
                      simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false,
                        LawfulMonad.bind_assoc, pure_bind, st_run_get_bind, st_run_getOf_bind,
                        st_run_lift_bind, st_run_lift, st_run_set_bind, st_run_set,
                        st_run_pure, map_pure, MonadAttach.mem_support_bind, support_pure,
                        Set.mem_singleton_iff, exists_eq_left] at hmem
                      set stR : KeyIndState S :=
                        { st with
                          opkEntries := st.opkEntries.map (fun (idx, e) =>
                            if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true })
                            else (idx, e))
                          usedRecvOPK := (k.val, j.val, o.val) :: st.usedRecvOPK
                          seenKyberBaseKeys :=
                            (checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys
                              k.val hdr.pqspkId hdr.spkId hdr.ekAPk).2
                          roCache := st.roCache }
                      have hseen := checkAndMark_length_le st.seenKyberBaseKeys
                        k.val hdr.pqspkId hdr.spkId hdr.ekAPk
                      rcases hpart : stR.sessions.find? (fun s => keyIndPartner P s _) with
                        _ | partner
                      · rw [hpart] at hmem; dsimp only at hmem
                        simp only [st_run_lift_bind, st_run_set_bind, LawfulMonad.bind_assoc,
                          MonadAttach.mem_support_bind] at hmem
                        rcases hmem with ⟨dkR, _, hmem⟩
                        split at hmem <;>
                          · simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
                            subst hmem
                            dsimp only [stepListLengthsLe, stR]
                            exact ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, hseen⟩
                      · rw [hpart] at hmem; dsimp only at hmem
                        simp only [pure_bind, st_run_set_bind, LawfulMonad.bind_assoc] at hmem
                        split at hmem <;>
                          · simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
                            subst hmem
                            dsimp only [stepListLengthsLe, stR]
                            exact ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, hseen⟩
  | acceptNoOPK k j l hdr =>
    unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl evalHkdfOrRo recordKeyIndResp at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
      LawfulMonad.bind_assoc] at hmem
    by_cases hhdr : (!(hdr.spkId == UInt32.ofNat j.val &&
         hdr.pqspkId == UInt32.ofNat j.val &&
         hdr.opkId? == none &&
         hdr.ikAPk.length == 32 &&
         hdr.ekAPk.length == 32)) = true
    · simp only [hhdr, ite_true, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact stepListLengthsLe_refl st
    · simp only [hhdr, ite_false] at hmem
      by_cases hused : (st.usedRecvNoOPK.contains (k.val, j.val, l.val)) = true
      · simp only [hused, ite_true, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact stepListLengthsLe_refl st
      · simp only [hused, ite_false] at hmem
        by_cases hkosk : (!koskSenderOk P st.principals st.advKeys hdr.ikAPk) = true
        · simp only [hkosk, ite_true, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact stepListLengthsLe_refl st
        · simp only [hkosk, ite_false] at hmem
          rcases hp : st.principals.find? (fun (idx, _) => idx == k.val) with _ | ⟨_, kEntry⟩
          · rw [hp] at hmem; dsimp only at hmem
            simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
            subst hmem; exact stepListLengthsLe_refl st
          · rw [hp] at hmem; dsimp only at hmem
            rcases hb : st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with _ | ⟨_, bEntry⟩
            · rw [hb] at hmem; dsimp only at hmem
              simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
              subst hmem; exact stepListLengthsLe_refl st
            · rw [hb] at hmem; dsimp only at hmem
              rcases hacc : acceptKeys P _ with _ | dk0
              · rw [hacc] at hmem; dsimp only at hmem
                simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
                subst hmem; exact stepListLengthsLe_refl st
              · rw [hacc] at hmem; dsimp only at hmem
                rcases hdec : P.kemDecaps bEntry.pqspkSk hdr.kemCt with _ | ss
                · rw [hdec] at hmem; dsimp only at hmem
                  simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
                  subst hmem; exact stepListLengthsLe_refl st
                · rw [hdec] at hmem; dsimp only at hmem
                  simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false,
                    LawfulMonad.bind_assoc, pure_bind, st_run_get_bind, st_run_getOf_bind,
                    st_run_lift_bind, st_run_lift, st_run_set_bind, st_run_set,
                    st_run_pure, map_pure, MonadAttach.mem_support_bind, support_pure,
                    Set.mem_singleton_iff, exists_eq_left] at hmem
                  set stR : KeyIndState S :=
                    { st with
                      usedRecvNoOPK := (k.val, j.val, l.val) :: st.usedRecvNoOPK
                      seenKyberBaseKeys :=
                        (checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys
                          k.val hdr.pqspkId hdr.spkId hdr.ekAPk).2
                      roCache := st.roCache }
                  have hseen := checkAndMark_length_le st.seenKyberBaseKeys
                    k.val hdr.pqspkId hdr.spkId hdr.ekAPk
                  rcases hpart : stR.sessions.find? (fun s => keyIndPartner P s _) with
                    _ | partner
                  · rw [hpart] at hmem; dsimp only at hmem
                    simp only [st_run_lift_bind, st_run_set_bind, LawfulMonad.bind_assoc,
                      MonadAttach.mem_support_bind] at hmem
                    rcases hmem with ⟨dkR, _, hmem⟩
                    split at hmem <;>
                      · simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
                        subst hmem
                        dsimp only [stepListLengthsLe, stR]
                        exact ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, hseen⟩
                  · rw [hpart] at hmem; dsimp only at hmem
                    simp only [pure_bind, st_run_set_bind, LawfulMonad.bind_assoc] at hmem
                    split at hmem <;>
                      · simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
                        subst hmem
                        dsimp only [stepListLengthsLe, stR]
                        exact ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, hseen⟩
  | testSession sid =>
    unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
      LawfulMonad.bind_assoc] at hmem
    by_cases htest : (!isKeyIndSessionTestable st sid) = true
    · simp only [htest, ite_true, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact stepListLengthsLe_refl st
    · simp only [htest, ite_false] at hmem
      rcases hs : st.sessions.find? (fun e => e.sid == sid) with _ | e
      · rw [hs] at hmem; dsimp only at hmem
        rcases hr : st.respSessions.find? (fun r => r.sid == sid) with _ | r
        · rw [hr] at hmem; dsimp only at hmem
          simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact stepListLengthsLe_refl st
        · rw [hr] at hmem; dsimp only at hmem
          simp only [st_run_set_bind, st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
      · rw [hs] at hmem; dsimp only at hmem
        simp only [st_run_set_bind, st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  | revealSessionKey sid =>
    unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, LawfulMonad.bind_assoc] at hmem
    rcases hs : st.sessions.find? (fun e => e.sid == sid) with _ | e
    · rw [hs] at hmem; dsimp only at hmem
      rcases hr : st.respSessions.find? (fun r => r.sid == sid) with _ | r
      · rw [hr] at hmem; dsimp only at hmem
        simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact stepListLengthsLe_refl st
      · rw [hr] at hmem; dsimp only at hmem
        simp only [st_run_ite, st_run_pure] at hmem
        by_cases hrt : r.tested = true
        · simp only [hrt, ite_true, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact stepListLengthsLe_refl st
        · simp only [hrt, ite_false, st_run_set_bind, st_run_pure,
            support_pure, Set.mem_singleton_iff] at hmem
          subst hmem
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
    · rw [hs] at hmem; dsimp only at hmem
      simp only [st_run_ite, st_run_pure] at hmem
      by_cases het : e.tested = true
      · simp only [het, ite_true, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact stepListLengthsLe_refl st
      · simp only [het, ite_false, st_run_set_bind, st_run_pure,
          support_pure, Set.mem_singleton_iff] at hmem
        subst hmem
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  | revealSpkSk u j =>
    unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, LawfulMonad.bind_assoc] at hmem
    rcases hb : st.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with _ | ⟨_, bEntry⟩
    · rw [hb] at hmem; dsimp only at hmem
      simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact stepListLengthsLe_refl st
    · rw [hb] at hmem; dsimp only at hmem
      simp only [st_run_set_bind, st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  | registerKey sk =>
    unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, LawfulMonad.bind_assoc] at hmem
    rcases hreg : registerAdvKey P st.advKeys sk with _ | ⟨pk, advKeys'⟩
    · rw [hreg] at hmem; dsimp only at hmem
      simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact stepListLengthsLe_refl st
    · rw [hreg] at hmem; dsimp only at hmem
      simp only [st_run_set_bind, st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp

/-- Every `pqxdhKeyIndImpl1KeyReal` query advances `stListBounded S nFuel` to
`stListBounded S (nFuel + 1)`. -/
theorem pqxdhKeyIndImpl1KeyReal_preserves_stListBounded {S : Setup} {P : Primitives} {nFuel : ℕ}
    (q : KeyIndQuery S) {st : KeyIndState S} (hst : stListBounded S nFuel st)
    {out : KeyIndResponse × KeyIndState S}
    (hmem : out ∈ support ((pqxdhKeyIndImpl1KeyReal S P q).run st)) :
    stListBounded S (nFuel + 1) out.2 := by
  obtain ⟨hsetup, hadv, _⟩ := pqxdhKeyIndImpl1KeyReal_preserves_setupBounded q hst.setup hmem
  obtain ⟨hprin, hspk, hopk, hsess, hresp, huopk, huno, hseen⟩ :=
    pqxdhKeyIndImpl1KeyReal_stepLengths q hmem
  exact
    { setup := hsetup
      principals_fuel_le := Nat.le_trans hprin (Nat.succ_le_succ hst.principals_fuel_le)
      spkBundles_fuel_le := Nat.le_trans hspk (Nat.succ_le_succ hst.spkBundles_fuel_le)
      opkEntries_fuel_le := Nat.le_trans hopk (Nat.succ_le_succ hst.opkEntries_fuel_le)
      sessions_fuel_le := Nat.le_trans hsess (Nat.succ_le_succ hst.sessions_fuel_le)
      respSessions_fuel_le := Nat.le_trans hresp (Nat.succ_le_succ hst.respSessions_fuel_le)
      usedRecvOPK_fuel_le := Nat.le_trans huopk (Nat.succ_le_succ hst.usedRecvOPK_fuel_le)
      usedRecvNoOPK_fuel_le := Nat.le_trans huno (Nat.succ_le_succ hst.usedRecvNoOPK_fuel_le)
      seenKyberBaseKeys_fuel_le := Nat.le_trans hseen (Nat.succ_le_succ hst.seenKyberBaseKeys_fuel_le)
      advKeys_le := Nat.le_trans hadv (Nat.succ_le_succ hst.advKeys_le) }

theorem stListBounded.pqxdhStep {S : Setup} {P : Primitives} {nFuel : ℕ}
    {q : KeyIndQuery S} {st : KeyIndState S} (hst : stListBounded S nFuel st)
    {out : KeyIndResponse × KeyIndState S}
    (hmem : out ∈ support ((pqxdhKeyIndImpl1KeyReal S P q).run st)) :
    stListBounded S (nFuel + 1) out.2 :=
  pqxdhKeyIndImpl1KeyReal_preserves_stListBounded q hst hmem

set_option linter.unusedSimpArgs false in
theorem pqxdhKeyIndImpl1KeyReal_testSession_preserves_stListBounded {S : Setup} {P : Primitives}
    {nFuel : ℕ} (sid : SessionId S) {st : KeyIndState S} (hst : stListBounded S nFuel st)
    {out : KeyIndResponse × KeyIndState S}
    (hmem : out ∈ support ((pqxdhKeyIndImpl1KeyReal S P (.testSession sid)).run st)) :
    stListBounded S nFuel out.2 := by
  obtain ⟨hsetup, _, _⟩ :=
    pqxdhKeyIndImpl1KeyReal_preserves_setupBounded (.testSession sid) hst.setup hmem
  unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl at hmem
  simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure,
    LawfulMonad.bind_assoc] at hmem
  by_cases htest : (!isKeyIndSessionTestable st sid) = true
  · simp only [htest, ite_true, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact hst
  · simp only [htest, ite_false] at hmem
    rcases hs : st.sessions.find? (fun e => e.sid == sid) with _ | e
    · rw [hs] at hmem; dsimp only at hmem
      rcases hr : st.respSessions.find? (fun r => r.sid == sid) with _ | r
      · rw [hr] at hmem; dsimp only at hmem
        simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact hst
      · rw [hr] at hmem; dsimp only at hmem
        simp only [st_run_set_bind, st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem
        exact { hst with setup := hsetup, respSessions_fuel_le := by simpa using hst.respSessions_fuel_le }
    · rw [hs] at hmem; dsimp only at hmem
      simp only [st_run_set_bind, st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      exact { hst with setup := hsetup, sessions_fuel_le := by simpa using hst.sessions_fuel_le }

set_option linter.unusedSimpArgs false in
theorem pqxdhKeyIndImpl1KeyReal_revealSpkSk_preserves_stListBounded {S : Setup} {P : Primitives}
    {nFuel : ℕ} (u : Fin S.N_id) (j : Fin S.N_recv) {st : KeyIndState S}
    (hst : stListBounded S nFuel st) {out : KeyIndResponse × KeyIndState S}
    (hmem : out ∈ support ((pqxdhKeyIndImpl1KeyReal S P (.revealSpkSk u j)).run st)) :
    stListBounded S nFuel out.2 := by
  obtain ⟨hsetup, _, _⟩ :=
    pqxdhKeyIndImpl1KeyReal_preserves_setupBounded (.revealSpkSk u j) hst.setup hmem
  unfold pqxdhKeyIndImpl1KeyReal pqxdhKeyIndImpl at hmem
  simp only [st_run_get_bind, st_run_getOf_bind, LawfulMonad.bind_assoc] at hmem
  rcases hb : st.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with _ | ⟨_, bEntry⟩
  · rw [hb] at hmem; dsimp only at hmem
    simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact hst
  · rw [hb] at hmem; dsimp only at hmem
    simp only [st_run_set_bind, st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact { hst with setup := hsetup, spkBundles_fuel_le := by simpa using hst.spkBundles_fuel_le }

/-! ## Expression and monadic helpers -/

section Helpers

variable {ℓ : ℕ} {S : Setup} {O : Ops (e2eSig ℓ)} {ι : Type} {T : OracleSpec ι}
  {I : Iface (e2eSig ℓ) T}

def orE {Γ : List (Ty (e2eSig ℓ))} (a b : Expr O Γ .bool) : Expr O Γ .bool :=
  .not (.and (.not a) (.not b))

@[simp] theorem eval_orE {Γ : List (Ty (e2eSig ℓ))} (a b : Expr O Γ .bool) (ρ : Env Γ) :
    (orE a b).eval ρ = (a.eval ρ || b.eval ρ) := by
  simp [orE, Expr.eval]

def isSomeE {Γ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)} (e : Expr O Γ (.opt τ)) :
    Expr O Γ .bool :=
  .caseOpt e (.bool false) (.bool true)

@[simp] theorem eval_isSomeE {Γ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt τ)) (ρ : Env Γ) :
    (isSomeE e).eval ρ = (e.eval ρ).isSome := by
  simp only [isSomeE, Expr.eval]
  cases e.eval ρ <;> rfl

def isNoneE {Γ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)} (e : Expr O Γ (.opt τ)) :
    Expr O Γ .bool :=
  .caseOpt e (.bool true) (.bool false)

@[simp] theorem eval_isNoneE {Γ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt τ)) (ρ : Env Γ) :
    (isNoneE e).eval ρ = (e.eval ρ).isNone := by
  simp only [isNoneE, Expr.eval]
  cases e.eval ρ <;> rfl

def optMapE {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt τ)) (f : Var (τ :: Γ) τ → Expr O (τ :: Γ) υ) : Expr O Γ (.opt υ) :=
  eCaseOpt e .none fun x => .some (f x)

@[simp] theorem eval_optMapE {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt τ)) (f : Var (τ :: Γ) τ → Expr O (τ :: Γ) υ) (ρ : Env Γ) :
    (optMapE e f).eval ρ = (e.eval ρ).map (fun x => (f .zero).eval (.cons x ρ)) := by
  simp only [optMapE, eCaseOpt, Expr.eval]
  cases e.eval ρ <;> rfl

def nat2EqE {Γ : List (Ty (e2eSig ℓ))}
    (a b : Expr O Γ (.prod .nat .nat)) : Expr O Γ .bool :=
  .and (.eqN (.fst a) (.fst b)) (.eqN (.snd a) (.snd b))

@[simp] theorem eval_nat2EqE {Γ : List (Ty (e2eSig ℓ))}
    (a b : Expr O Γ (.prod .nat .nat)) (ρ : Env Γ) :
    (nat2EqE a b).eval ρ = (a.eval ρ == b.eval ρ) := by
  rcases ha : a.eval ρ with ⟨a1, a2⟩
  rcases hb : b.eval ρ with ⟨b1, b2⟩
  simp only [nat2EqE, Expr.eval, ha, hb]
  by_cases h1 : a1 = b1
  · by_cases h2 : a2 = b2 <;> simp [h1, h2, BEq.beq]
  · simp [h1, BEq.beq]

def nat3EqE {Γ : List (Ty (e2eSig ℓ))}
    (a b : Expr O Γ (.prod .nat (.prod .nat .nat))) : Expr O Γ .bool :=
  .and (.eqN (.fst a) (.fst b)) (nat2EqE (.snd a) (.snd b))

@[simp] theorem eval_nat3EqE {Γ : List (Ty (e2eSig ℓ))}
    (a b : Expr O Γ (.prod .nat (.prod .nat .nat))) (ρ : Env Γ) :
    (nat3EqE a b).eval ρ = (a.eval ρ == b.eval ρ) := by
  rcases ha : a.eval ρ with ⟨a1, a2, a3⟩
  rcases hb : b.eval ρ with ⟨b1, b2, b3⟩
  simp only [nat3EqE, Expr.eval, eval_nat2EqE, ha, hb]
  by_cases h1 : a1 = b1
  · by_cases h2 : a2 = b2
    · by_cases h3 : a3 = b3 <;> simp [h1, h2, h3, BEq.beq]
    · simp [h1, h2, BEq.beq]
  · simp [h1, BEq.beq]

def nat4EqE {Γ : List (Ty (e2eSig ℓ))}
    (a b : Expr O Γ (.prod .nat (.prod .nat (.prod .nat .nat)))) : Expr O Γ .bool :=
  .and (.eqN (.fst a) (.fst b)) (nat3EqE (.snd a) (.snd b))

@[simp] theorem eval_nat4EqE {Γ : List (Ty (e2eSig ℓ))}
    (a b : Expr O Γ (.prod .nat (.prod .nat (.prod .nat .nat)))) (ρ : Env Γ) :
    (nat4EqE a b).eval ρ = (a.eval ρ == b.eval ρ) := by
  rcases ha : a.eval ρ with ⟨a1, a2, a3, a4⟩
  rcases hb : b.eval ρ with ⟨b1, b2, b3, b4⟩
  simp only [nat4EqE, Expr.eval, eval_nat3EqE, ha, hb]
  by_cases h1 : a1 = b1
  · by_cases h2 : a2 = b2
    · by_cases h3 : a3 = b3
      · by_cases h4 : a4 = b4 <;> simp [h1, h2, h3, h4, BEq.beq]
      · simp [h1, h2, h3, BEq.beq]
    · simp [h1, h2, BEq.beq]
  · simp [h1, BEq.beq]

def finValE (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))} {n : ℕ}
    (e : Expr O Γ (FinT n)) : Expr O Γ .nat :=
  H.pureOp (.finVal n) e

def sidKeyE (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (s : Expr O Γ (sidT S)) : Expr O Γ (.prod .nat (.prod .nat (.prod .nat .nat))) :=
  eCaseSum s
    (fun p => .pair (.nat 0) (.pair (finValE H (.fst (v p)))
      (.pair (finValE H (.snd (v p))) (.nat 0))))
    (fun r1 => eCaseSum (v r1)
      (fun p => .pair (.nat 1) (.pair (finValE H (.fst (v p)))
        (.pair (finValE H (.snd (v p))) (.nat 0))))
      (fun r2 => eCaseSum (v r2)
        (fun p => .pair (.nat 2) (.pair (finValE H (.fst (v p)))
          (.pair (finValE H (.fst (.snd (v p)))) (finValE H (.snd (.snd (v p)))))))
        (fun p => .pair (.nat 3) (.pair (finValE H (.fst (v p)))
          (.pair (finValE H (.fst (.snd (v p)))) (finValE H (.snd (.snd (v p)))))))))

def sidEqE (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (a b : Expr O Γ (sidT S)) : Expr O Γ .bool :=
  nat4EqE (sidKeyE H a) (sidKeyE H b)

def optEqByE {Γ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)}
    (eqElem : ∀ {Δ : List (Ty (e2eSig ℓ))}, Expr O Δ τ → Expr O Δ τ → Expr O Δ .bool)
    (a b : Expr O Γ (.opt τ)) : Expr O Γ .bool :=
  eLet (.pair a b) fun ab =>
    eCaseOpt (.fst (v ab))
      (isNoneE (.snd (v ab)))
      (fun x => eCaseOpt (.snd (v ab)) (.bool false)
        (fun y => eqElem (v x) (v y)))

def optPu32EqE (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (a b : Expr O Γ (.opt PU32)) : Expr O Γ .bool :=
  optEqByE (fun x y => H.pureOp .pu32Eq (.pair x y)) a b

def optPb32EqE (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (a b : Expr O Γ (.opt (PB 32))) : Expr O Γ .bool :=
  optEqByE (fun x y => H.pureOp (.pbytesEq 32 32) (.pair x y)) a b

/-! ### Record projections and updaters -/

def peSec0 {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ e2ePrincipalEntryTy) : Expr O Γ (PB 32) :=
  .fst e
def peIkPk {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ e2ePrincipalEntryTy) : Expr O Γ (PB 32) :=
  .fst (.snd e)
def peSecSign {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ e2ePrincipalEntryTy) : Expr O Γ (PB 32) :=
  .fst (.snd (.snd e))
def peSignPk {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ e2ePrincipalEntryTy) : Expr O Γ (PB 32) :=
  .fst (.snd (.snd (.snd e)))
def peCorr {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ e2ePrincipalEntryTy) : Expr O Γ .bool :=
  .snd (.snd (.snd (.snd e)))

def peSetCorrE {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ e2ePrincipalEntryTy) :
    Expr O Γ e2ePrincipalEntryTy :=
  eLet e fun x =>
    .pair (peSec0 (v x)) (.pair (peIkPk (v x)) (.pair (peSecSign (v x))
      (.pair (peSignPk (v x)) (.bool true))))

def beSpkSk {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ e2eSpkBundleEntryTy) : Expr O Γ (PB 32) :=
  .fst e
def beSpkPk {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ e2eSpkBundleEntryTy) : Expr O Γ (PB 32) :=
  .fst (.snd e)
def beSpkSig {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ e2eSpkBundleEntryTy) : Expr O Γ (PB 64) :=
  .fst (.snd (.snd e))
def bePqSk {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ e2eSpkBundleEntryTy) : Expr O Γ (PB 3168) :=
  .fst (.snd (.snd (.snd e)))
def bePqPk {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ e2eSpkBundleEntryTy) : Expr O Γ (PB 1568) :=
  .fst (.snd (.snd (.snd (.snd e))))
def bePqSig {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ e2eSpkBundleEntryTy) : Expr O Γ (PB 64) :=
  .fst (.snd (.snd (.snd (.snd (.snd e)))))
def beRev {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ e2eSpkBundleEntryTy) : Expr O Γ .bool :=
  .snd (.snd (.snd (.snd (.snd (.snd e)))))

def beSetRevE {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ e2eSpkBundleEntryTy) :
    Expr O Γ e2eSpkBundleEntryTy :=
  eLet e fun x =>
    .pair (beSpkSk (v x)) (.pair (beSpkPk (v x)) (.pair (beSpkSig (v x))
      (.pair (bePqSk (v x)) (.pair (bePqPk (v x)) (.pair (bePqSig (v x)) (.bool true))))))

def oeSk {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ e2eOpkEntryTy) : Expr O Γ (PB 32) := .fst e
def oePk {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ e2eOpkEntryTy) : Expr O Γ (PB 32) :=
  .fst (.snd e)
def oeCons {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ e2eOpkEntryTy) : Expr O Γ .bool :=
  .snd (.snd e)

def oeSetConsE {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ e2eOpkEntryTy) : Expr O Γ e2eOpkEntryTy :=
  eLet e fun x => .pair (oeSk (v x)) (.pair (oePk (v x)) (.bool true))

def bndIkB {Γ : List (Ty (e2eSig ℓ))} (b : Expr O Γ bundleT) : Expr O Γ (PB 32) := .fst b
def bndSpkId {Γ : List (Ty (e2eSig ℓ))} (b : Expr O Γ bundleT) : Expr O Γ PU32 := .fst (.snd b)
def bndSpkB {Γ : List (Ty (e2eSig ℓ))} (b : Expr O Γ bundleT) : Expr O Γ (PB 32) :=
  .fst (.snd (.snd b))
def bndSpkSig {Γ : List (Ty (e2eSig ℓ))} (b : Expr O Γ bundleT) : Expr O Γ (PB 64) :=
  .fst (.snd (.snd (.snd b)))
def bndOpkB {Γ : List (Ty (e2eSig ℓ))} (b : Expr O Γ bundleT) :
    Expr O Γ (.opt (.prod PU32 (PB 32))) :=
  .fst (.snd (.snd (.snd (.snd b))))
def bndPqId {Γ : List (Ty (e2eSig ℓ))} (b : Expr O Γ bundleT) : Expr O Γ PU32 :=
  .fst (.snd (.snd (.snd (.snd (.snd b)))))
def bndPqB {Γ : List (Ty (e2eSig ℓ))} (b : Expr O Γ bundleT) : Expr O Γ (PB 1568) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd b))))))
def bndPqSig {Γ : List (Ty (e2eSig ℓ))} (b : Expr O Γ bundleT) : Expr O Γ (PB 64) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd b))))))

def hdrIkA {Γ : List (Ty (e2eSig ℓ))} (h : Expr O Γ hdrT) : Expr O Γ (PB 32) := .fst h
def hdrEkA {Γ : List (Ty (e2eSig ℓ))} (h : Expr O Γ hdrT) : Expr O Γ (PB 32) := .fst (.snd h)
def hdrSpkId {Γ : List (Ty (e2eSig ℓ))} (h : Expr O Γ hdrT) : Expr O Γ PU32 :=
  .fst (.snd (.snd h))
def hdrOpkId {Γ : List (Ty (e2eSig ℓ))} (h : Expr O Γ hdrT) : Expr O Γ (.opt PU32) :=
  .fst (.snd (.snd (.snd h)))
def hdrPqId {Γ : List (Ty (e2eSig ℓ))} (h : Expr O Γ hdrT) : Expr O Γ PU32 :=
  .fst (.snd (.snd (.snd (.snd h))))
def hdrKemCt {Γ : List (Ty (e2eSig ℓ))} (h : Expr O Γ hdrT) : Expr O Γ (PB 1568) :=
  .snd (.snd (.snd (.snd (.snd h))))

def ieSid {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    Expr O Γ (sidT S) := .fst e
def ieHonPeer {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    Expr O Γ (.opt .nat) := .fst (.snd e)
def iePeerIk {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    Expr O Γ (PB 32) := .fst (.snd (.snd e))
def iePeerSpk {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    Expr O Γ (PB 32) := .fst (.snd (.snd (.snd e)))
def iePeerOpk {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    Expr O Γ (.opt (PB 32)) := .fst (.snd (.snd (.snd (.snd e))))
def iePeerPq {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    Expr O Γ (PB 1568) := .fst (.snd (.snd (.snd (.snd (.snd e)))))
def ieSpkHon {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    Expr O Γ .bool := .fst (.snd (.snd (.snd (.snd (.snd (.snd e))))))
def ieOpkHon {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    Expr O Γ .bool := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))
def iePqHon {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    Expr O Γ .bool := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e))))))))
def ieEkSk {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    Expr O Γ (PB 32) := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))))
def ieFresh {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    Expr O Γ .bool := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e))))))))))
def ieReal {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    Expr O Γ drKeyT :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))))))
def ieRand {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    Expr O Γ drKeyT :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e))))))))))))
def ieHdr {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    Expr O Γ hdrT :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))))))))
def ieTested {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    Expr O Γ .bool :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd e))))))))))))))
def ieRev {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    Expr O Γ .bool :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd e))))))))))))))

def ieSetTestedE {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    Expr O Γ (e2eInitiatorEntryTy ℓ S) :=
  eLet e fun x =>
    .pair (ieSid (v x)) (.pair (ieHonPeer (v x)) (.pair (iePeerIk (v x))
      (.pair (iePeerSpk (v x)) (.pair (iePeerOpk (v x)) (.pair (iePeerPq (v x))
        (.pair (ieSpkHon (v x)) (.pair (ieOpkHon (v x)) (.pair (iePqHon (v x))
          (.pair (ieEkSk (v x)) (.pair (ieFresh (v x)) (.pair (ieReal (v x))
            (.pair (ieRand (v x)) (.pair (ieHdr (v x))
              (.pair (.bool true) (ieRev (v x))))))))))))))))

def ieSetRevE {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    Expr O Γ (e2eInitiatorEntryTy ℓ S) :=
  eLet e fun x =>
    .pair (ieSid (v x)) (.pair (ieHonPeer (v x)) (.pair (iePeerIk (v x))
      (.pair (iePeerSpk (v x)) (.pair (iePeerOpk (v x)) (.pair (iePeerPq (v x))
        (.pair (ieSpkHon (v x)) (.pair (ieOpkHon (v x)) (.pair (iePqHon (v x))
          (.pair (ieEkSk (v x)) (.pair (ieFresh (v x)) (.pair (ieReal (v x))
            (.pair (ieRand (v x)) (.pair (ieHdr (v x))
              (.pair (ieTested (v x)) (.bool true)))))))))))))))

def ieSetRandE {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eInitiatorEntryTy ℓ S))
    (rk : Expr O Γ drKeyT) : Expr O Γ (e2eInitiatorEntryTy ℓ S) :=
  eLet (.pair e rk) fun p =>
    .pair (ieSid (.fst (v p))) (.pair (ieHonPeer (.fst (v p))) (.pair (iePeerIk (.fst (v p)))
      (.pair (iePeerSpk (.fst (v p))) (.pair (iePeerOpk (.fst (v p)))
        (.pair (iePeerPq (.fst (v p))) (.pair (ieSpkHon (.fst (v p)))
          (.pair (ieOpkHon (.fst (v p))) (.pair (iePqHon (.fst (v p)))
            (.pair (ieEkSk (.fst (v p))) (.pair (ieFresh (.fst (v p)))
              (.pair (ieReal (.fst (v p))) (.pair (.snd (v p))
                (.pair (ieHdr (.fst (v p)))
                  (.pair (ieTested (.fst (v p))) (ieRev (.fst (v p)))))))))))))))))

def reSid {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    Expr O Γ (sidT S) := .fst e
def reIk {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    Expr O Γ (PB 32) := .fst (.snd e)
def reSpk {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    Expr O Γ (PB 32) := .fst (.snd (.snd e))
def reOpk {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    Expr O Γ (.opt (PB 32)) := .fst (.snd (.snd (.snd e)))
def rePq {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    Expr O Γ (PB 1568) := .fst (.snd (.snd (.snd (.snd e))))
def reHdr {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    Expr O Γ hdrT := .fst (.snd (.snd (.snd (.snd (.snd e)))))
def reSendHon {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    Expr O Γ .bool := .fst (.snd (.snd (.snd (.snd (.snd (.snd e))))))
def reReal {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    Expr O Γ drKeyT := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))
def reRand {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    Expr O Γ drKeyT := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e))))))))
def reTested {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    Expr O Γ .bool := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))))
def reRev {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    Expr O Γ .bool := .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))))

def reSetTestedE {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    Expr O Γ (e2eRespEntryTy ℓ S) :=
  eLet e fun x =>
    .pair (reSid (v x)) (.pair (reIk (v x)) (.pair (reSpk (v x)) (.pair (reOpk (v x))
      (.pair (rePq (v x)) (.pair (reHdr (v x)) (.pair (reSendHon (v x))
        (.pair (reReal (v x)) (.pair (reRand (v x))
          (.pair (.bool true) (reRev (v x)))))))))))

def reSetRevE {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    Expr O Γ (e2eRespEntryTy ℓ S) :=
  eLet e fun x =>
    .pair (reSid (v x)) (.pair (reIk (v x)) (.pair (reSpk (v x)) (.pair (reOpk (v x))
      (.pair (rePq (v x)) (.pair (reHdr (v x)) (.pair (reSendHon (v x))
        (.pair (reReal (v x)) (.pair (reRand (v x))
          (.pair (reTested (v x)) (.bool true))))))))))

def reSetRandE {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (e2eRespEntryTy ℓ S))
    (rk : Expr O Γ drKeyT) : Expr O Γ (e2eRespEntryTy ℓ S) :=
  eLet (.pair e rk) fun p =>
    .pair (reSid (.fst (v p))) (.pair (reIk (.fst (v p))) (.pair (reSpk (.fst (v p)))
      (.pair (reOpk (.fst (v p))) (.pair (rePq (.fst (v p))) (.pair (reHdr (.fst (v p)))
        (.pair (reSendHon (.fst (v p))) (.pair (reReal (.fst (v p)))
          (.pair (.snd (v p)) (.pair (reTested (.fst (v p))) (reRev (.fst (v p))))))))))))

def stSecb {Γ : List (Ty (e2eSig ℓ))} (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    Expr O Γ .bool := .fst st
def stPrin {Γ : List (Ty (e2eSig ℓ))} (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    Expr O Γ (.list (.prod .nat e2ePrincipalEntryTy)) := .fst (.snd st)
def stSpk {Γ : List (Ty (e2eSig ℓ))} (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    Expr O Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)) := .fst (.snd (.snd st))
def stOpk {Γ : List (Ty (e2eSig ℓ))} (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    Expr O Γ (.list (.prod (.prod .nat (.prod .nat .nat)) e2eOpkEntryTy)) :=
  .fst (.snd (.snd (.snd st)))
def stSess {Γ : List (Ty (e2eSig ℓ))} (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    Expr O Γ (.list (e2eInitiatorEntryTy ℓ S)) := .fst (.snd (.snd (.snd (.snd st))))
def stResp {Γ : List (Ty (e2eSig ℓ))} (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    Expr O Γ (.list (e2eRespEntryTy ℓ S)) := .fst (.snd (.snd (.snd (.snd (.snd st)))))
def stUsedOpk {Γ : List (Ty (e2eSig ℓ))} (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    Expr O Γ (.list (.prod .nat (.prod .nat .nat))) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd st))))))
def stUsedNoOpk {Γ : List (Ty (e2eSig ℓ))} (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    Expr O Γ (.list (.prod .nat (.prod .nat .nat))) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd st)))))))
def stSeen {Γ : List (Ty (e2eSig ℓ))} (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    Expr O Γ (.list (.prod .nat (.prod PU32 (.prod PU32 (PB 32))))) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd st))))))))
def stRo {Γ : List (Ty (e2eSig ℓ))} (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    Expr O Γ (.list (.prod (PB 192) drKeyT)) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd st)))))))))
def stAdv {Γ : List (Ty (e2eSig ℓ))} (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    Expr O Γ (.list (.prod (PB 32) (PB 32))) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd st)))))))))

def setPrinE {Γ : List (Ty (e2eSig ℓ))} (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (ps : Expr O Γ (.list (.prod .nat e2ePrincipalEntryTy))) :
    Expr O Γ (e2eKeyIndStateTy ℓ S) :=
  eLet (.pair st ps) fun p =>
    .pair (stSecb (.fst (v p))) (.pair (.snd (v p)) (.snd (.snd (.fst (v p)))))

def setSpkE {Γ : List (Ty (e2eSig ℓ))} (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (bs : Expr O Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy))) :
    Expr O Γ (e2eKeyIndStateTy ℓ S) :=
  eLet (.pair st bs) fun p =>
    .pair (stSecb (.fst (v p))) (.pair (stPrin (.fst (v p)))
      (.pair (.snd (v p)) (.snd (.snd (.snd (.fst (v p)))))))

def setOpkE {Γ : List (Ty (e2eSig ℓ))} (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (os : Expr O Γ (.list (.prod (.prod .nat (.prod .nat .nat)) e2eOpkEntryTy))) :
    Expr O Γ (e2eKeyIndStateTy ℓ S) :=
  eLet (.pair st os) fun p =>
    .pair (stSecb (.fst (v p))) (.pair (stPrin (.fst (v p))) (.pair (stSpk (.fst (v p)))
      (.pair (.snd (v p)) (.snd (.snd (.snd (.snd (.fst (v p)))))))))

def setSessE {Γ : List (Ty (e2eSig ℓ))} (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (ss : Expr O Γ (.list (e2eInitiatorEntryTy ℓ S))) :
    Expr O Γ (e2eKeyIndStateTy ℓ S) :=
  eLet (.pair st ss) fun p =>
    .pair (stSecb (.fst (v p))) (.pair (stPrin (.fst (v p))) (.pair (stSpk (.fst (v p)))
      (.pair (stOpk (.fst (v p))) (.pair (.snd (v p))
        (.snd (.snd (.snd (.snd (.snd (.fst (v p)))))))))))

def setRespE {Γ : List (Ty (e2eSig ℓ))} (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (rs : Expr O Γ (.list (e2eRespEntryTy ℓ S))) :
    Expr O Γ (e2eKeyIndStateTy ℓ S) :=
  eLet (.pair st rs) fun p =>
    .pair (stSecb (.fst (v p))) (.pair (stPrin (.fst (v p))) (.pair (stSpk (.fst (v p)))
      (.pair (stOpk (.fst (v p))) (.pair (stSess (.fst (v p)))
        (.pair (.snd (v p)) (.snd (.snd (.snd (.snd (.snd (.snd (.fst (v p)))))))))))))

def setAdvE {Γ : List (Ty (e2eSig ℓ))} (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (ak : Expr O Γ (.list (.prod (PB 32) (PB 32)))) :
    Expr O Γ (e2eKeyIndStateTy ℓ S) :=
  eLet (.pair st ak) fun p =>
    .pair (stSecb (.fst (v p))) (.pair (stPrin (.fst (v p))) (.pair (stSpk (.fst (v p)))
      (.pair (stOpk (.fst (v p))) (.pair (stSess (.fst (v p))) (.pair (stResp (.fst (v p)))
        (.pair (stUsedOpk (.fst (v p))) (.pair (stUsedNoOpk (.fst (v p)))
          (.pair (stSeen (.fst (v p))) (.pair (stRo (.fst (v p))) (.snd (v p)))))))))))

def setAcceptOpkE {Γ : List (Ty (e2eSig ℓ))} (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (os : Expr O Γ (.list (.prod (.prod .nat (.prod .nat .nat)) e2eOpkEntryTy)))
    (used : Expr O Γ (.list (.prod .nat (.prod .nat .nat))))
    (seen : Expr O Γ (.list (.prod .nat (.prod PU32 (.prod PU32 (PB 32)))))) :
    Expr O Γ (e2eKeyIndStateTy ℓ S) :=
  eLet (.pair st (.pair os (.pair used seen))) fun p =>
    .pair (stSecb (.fst (v p))) (.pair (stPrin (.fst (v p))) (.pair (stSpk (.fst (v p)))
      (.pair (.fst (.snd (v p))) (.pair (stSess (.fst (v p))) (.pair (stResp (.fst (v p)))
        (.pair (.fst (.snd (.snd (v p)))) (.pair (stUsedNoOpk (.fst (v p)))
          (.pair (.snd (.snd (.snd (v p))))
            (.pair (stRo (.fst (v p))) (stAdv (.fst (v p))))))))))))

def setAcceptNoOpkE {Γ : List (Ty (e2eSig ℓ))} (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (used : Expr O Γ (.list (.prod .nat (.prod .nat .nat))))
    (seen : Expr O Γ (.list (.prod .nat (.prod PU32 (.prod PU32 (PB 32)))))) :
    Expr O Γ (e2eKeyIndStateTy ℓ S) :=
  eLet (.pair st (.pair used seen)) fun p =>
    .pair (stSecb (.fst (v p))) (.pair (stPrin (.fst (v p))) (.pair (stSpk (.fst (v p)))
      (.pair (stOpk (.fst (v p))) (.pair (stSess (.fst (v p))) (.pair (stResp (.fst (v p)))
        (.pair (stUsedOpk (.fst (v p))) (.pair (.fst (.snd (v p)))
          (.pair (.snd (.snd (v p)))
            (.pair (stRo (.fst (v p))) (stAdv (.fst (v p))))))))))))

def rNoneE {Γ : List (Ty (e2eSig ℓ))} : Expr O Γ keyIndRT := .inl .unit
def rInitPrinE {Γ : List (Ty (e2eSig ℓ))} (ik s : Expr O Γ (PB 32)) : Expr O Γ keyIndRT :=
  .inr (.inl (.pair ik s))
def rPkE {Γ : List (Ty (e2eSig ℓ))} (pk : Expr O Γ (PB 32)) : Expr O Γ keyIndRT :=
  .inr (.inr (.inl pk))
def rCorrE {Γ : List (Ty (e2eSig ℓ))} (ik s : Expr O Γ (PB 32)) : Expr O Γ keyIndRT :=
  .inr (.inr (.inr (.inl (.pair ik s))))
def rBundleE {Γ : List (Ty (e2eSig ℓ))} (b : Expr O Γ bundleT) : Expr O Γ keyIndRT :=
  .inr (.inr (.inr (.inr (.inl b))))
def rHdrE {Γ : List (Ty (e2eSig ℓ))} (h : Expr O Γ hdrT) : Expr O Γ keyIndRT :=
  .inr (.inr (.inr (.inr (.inr (.inl h)))))
def rInitUnfreshE {Γ : List (Ty (e2eSig ℓ))} (dk : Expr O Γ drKeyT) (h : Expr O Γ hdrT) :
    Expr O Γ keyIndRT :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inl (.pair dk h)))))))
def rAcceptFreshE {Γ : List (Ty (e2eSig ℓ))} : Expr O Γ keyIndRT :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl .unit)))))))
def rDrKeyE {Γ : List (Ty (e2eSig ℓ))} (dk : Expr O Γ drKeyT) : Expr O Γ keyIndRT :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl dk))))))))
def rDhSecretsE {Γ : List (Ty (e2eSig ℓ))}
    (l1 l2 l3 l4 : Expr O Γ (.list (PB 32))) : Expr O Γ keyIndRT :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
    (.inl (.pair l1 (.pair l2 (.pair l3 l4))))))))))))
def rSpkSkE {Γ : List (Ty (e2eSig ℓ))} (sk : Expr O Γ (PB 32)) : Expr O Γ keyIndRT :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr sk)))))))))

def rsE {Γ : List (Ty (e2eSig ℓ))} (r : Expr O Γ keyIndRT)
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    Expr O Γ (.prod keyIndRT (e2eKeyIndStateTy ℓ S)) :=
  .pair r st

/-! ### Protocol encoding and bookkeeping -/

def encECWideE (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (pk : Expr O Γ (PB 32)) : Expr O Γ (PB 1569) :=
  H.pureOp (.pbytesWiden 33 1536) (H.pureOp (.pbytesCons TAG_EC_DJB 32) pk)

def encKEME (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (pk : Expr O Γ (PB 1568)) : Expr O Γ (PB 1569) :=
  H.pureOp (.pbytesCons TAG_KYBER_1024 1568) pk

def zero32E (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))} : Expr O Γ (PB 32) :=
  H.pureOp (.pbytesLit 32 (List.replicate 32 0)) .unit

def dhNonZeroE (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (dh : Expr O Γ (PB 32)) : Expr O Γ .bool :=
  .not (H.pureOp (.pbytesEq 32 32) (.pair dh (zero32E H)))

def dhOptNonZeroE (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (dh4? : Expr O Γ (.opt (PB 32))) : Expr O Γ .bool :=
  eCaseOpt dh4? (.bool true) fun dh => dhNonZeroE H (v dh)

def buildSecretsE (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (dh1 dh2 dh3 : Expr O Γ (PB 32)) (dh4? : Expr O Γ (.opt (PB 32)))
    (ss : Expr O Γ (PB 32)) : Expr O Γ (PB 192) :=
  eLet (.pair (H.pureOp (.pbytesCat (32 + 32 + 32) 32)
        (.pair (H.pureOp (.pbytesCat (32 + 32) 32)
          (.pair (H.pureOp (.pbytesCat 32 32)
            (.pair (H.pureOp (.pbytesLit 32 F_X25519) .unit) dh1)) dh2)) dh3))
      (.pair dh4? ss)) fun p =>
    eCaseOpt (.fst (.snd (v p)))
      (H.pureOp (.pbytesWiden (32 + 32 + 32 + 32 + 32) 32)
        (H.pureOp (.pbytesCat (32 + 32 + 32 + 32) 32) (.pair (.fst (v p)) (.snd (.snd (v p))))))
      (fun dh4 =>
        H.pureOp (.pbytesCat (32 + 32 + 32 + 32 + 32) 32)
          (.pair (H.pureOp (.pbytesCat (32 + 32 + 32 + 32) 32) (.pair (.fst (v p)) (v dh4)))
            (.snd (.snd (v p)))))

def checkSeenEFuel (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (used : Expr O Γ (.list (.prod .nat (.prod PU32 (.prod PU32 (PB 32))))))
    (k : Expr O Γ .nat) (pqspkId spkId : Expr O Γ PU32) (ekAPk : Expr O Γ (PB 32)) :
    Expr O Γ (.prod .bool (.list (.prod .nat (.prod PU32 (.prod PU32 (PB 32)))))) :=
  eLet (.pair used (.pair k (.pair pqspkId (.pair spkId ekAPk)))) fun p =>
    .ite
      (eAny (min nFuel S.N_recv_tot) (.fst (v p)) fun e =>
        .and (.eqN (.fst (v e)) (.fst (.snd (v p))))
          (.and (H.pureOp .pu32Eq (.pair (.fst (.snd (v e))) (.fst (.snd (.snd (v p))))))
            (.and (H.pureOp .pu32Eq (.pair (.fst (.snd (.snd (v e))))
                    (.fst (.snd (.snd (.snd (v p)))))))
              (H.pureOp (.pbytesEq 32 32)
                (.pair (.snd (.snd (.snd (v e)))) (.snd (.snd (.snd (.snd (v p))))))))))
      (.pair (.bool false) (.fst (v p)))
      (.pair (.bool true) (.cons (.snd (v p)) (.fst (v p))))

def checkSeenE (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (used : Expr O Γ (.list (.prod .nat (.prod PU32 (.prod PU32 (PB 32))))))
    (k : Expr O Γ .nat) (pqspkId spkId : Expr O Γ PU32) (ekAPk : Expr O Γ (PB 32)) :
    Expr O Γ (.prod .bool (.list (.prod .nat (.prod PU32 (.prod PU32 (PB 32)))))) :=
  eLet (.pair used (.pair k (.pair pqspkId (.pair spkId ekAPk)))) fun p =>
    .ite
      (eAny S.N_recv_tot (.fst (v p)) fun e =>
        .and (.eqN (.fst (v e)) (.fst (.snd (v p))))
          (.and (H.pureOp .pu32Eq (.pair (.fst (.snd (v e))) (.fst (.snd (.snd (v p))))))
            (.and (H.pureOp .pu32Eq (.pair (.fst (.snd (.snd (v e))))
                    (.fst (.snd (.snd (.snd (v p)))))))
              (H.pureOp (.pbytesEq 32 32)
                (.pair (.snd (.snd (.snd (v e)))) (.snd (.snd (.snd (.snd (v p))))))))))
      (.pair (.bool false) (.fst (v p)))
      (.pair (.bool true) (.cons (.snd (v p)) (.fst (v p))))

def isTestableEFuel (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) (sid : Expr O Γ (sidT S)) : Expr O Γ .bool :=
  eLet (.pair st sid) fun p =>
    eCaseOpt
      (eFind (min nFuel S.N_send_tot) (stSess (.fst (v p))) fun e =>
        sidEqE H (ieSid (v e)) (.snd (v p)))
      (eCaseOpt
        (eFind (min nFuel S.N_recv_tot) (stResp (.fst (v p))) fun r =>
          sidEqE H (reSid (v r)) (.snd (v p)))
        (.bool false)
        (fun r => .and (.and (reSendHon (v r)) (.not (reTested (v r)))) (.not (reRev (v r)))))
      (fun e => .and (.and (ieFresh (v e)) (.not (ieTested (v e)))) (.not (ieRev (v e))))

def isTestableE (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) (sid : Expr O Γ (sidT S)) : Expr O Γ .bool :=
  eLet (.pair st sid) fun p =>
    eCaseOpt
      (eFind S.N_send_tot (stSess (.fst (v p))) fun e =>
        sidEqE H (ieSid (v e)) (.snd (v p)))
      (eCaseOpt
        (eFind S.N_recv_tot (stResp (.fst (v p))) fun r =>
          sidEqE H (reSid (v r)) (.snd (v p)))
        (.bool false)
        (fun r => .and (.and (reSendHon (v r)) (.not (reTested (v r)))) (.not (reRev (v r)))))
      (fun e => .and (.and (ieFresh (v e)) (.not (ieTested (v e)))) (.not (ieRev (v e))))

/-! ### Monadic sampling and primitive helpers -/

def sBytes32C (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))} : Comp O I Γ (PB 32) :=
  bindV H.sampBv256 fun w => .ret (H.pureOp .bv256ToPbytes32 (v w))

def sRandom64C (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))} : Comp O I Γ (PB 64) :=
  bindV (sBytes32C H) fun b1 =>
    bindV (sBytes32C H) fun b2 =>
      .ret (H.pureOp (.pbytesCat 32 32) (.pair (v b1) (v b2)))

def sDrKey96C (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))} : Comp O I Γ drKeyT :=
  bindV (sBytes32C H) fun rk =>
    bindV (sBytes32C H) fun ck =>
      bindV (sBytes32C H) fun pk =>
        .ret (.pair (v rk) (.pair (v ck) (v pk)))

def sKemKeyGenC (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))} :
    Comp O I Γ (.prod (PB 1568) (PB 3168)) :=
  bindV (sRandom64C H) fun seed => H.callPrim .kemKeyGen (v seed)

def findHonestCFuel (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (principals : Expr O Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (ikB : Expr O Γ (PB 32)) :
    Comp O I Γ (.opt (.prod .nat e2ePrincipalEntryTy)) :=
  letV (.pair principals ikB) fun pi =>
    bindV (H.callPrim .pow8 (.snd (v pi))) fun pIk =>
      findMV (min nFuel S.N_id) (.fst (v pi)) fun e =>
        bindV (H.callPrim .pow8 (peIkPk (.snd (v e)))) fun pEnt =>
          .ret (H.pureOp (.pbytesEq 32 32) (.pair (v pIk) (v pEnt)))

def findHonestC (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (principals : Expr O Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (ikB : Expr O Γ (PB 32)) :
    Comp O I Γ (.opt (.prod .nat e2ePrincipalEntryTy)) :=
  letV (.pair principals ikB) fun pi =>
    bindV (H.callPrim .pow8 (.snd (v pi))) fun pIk =>
      findMV S.N_id (.fst (v pi)) fun e =>
        bindV (H.callPrim .pow8 (peIkPk (.snd (v e)))) fun pEnt =>
          .ret (H.pureOp (.pbytesEq 32 32) (.pair (v pIk) (v pEnt)))

def isAdvRegC (H : E2EPqxdhHooks ℓ O I) (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (advKeys : Expr O Γ (.list (.prod (PB 32) (PB 32))))
    (pk : Expr O Γ (PB 32)) : Comp O I Γ .bool :=
  letV (.pair advKeys pk) fun ap =>
    bindV (H.callPrim .pow8 (.snd (v ap))) fun pPk =>
      anyMV nAdv (.fst (v ap)) fun e =>
        bindV (H.callPrim .pow8 (.snd (v e))) fun pEnt =>
          .ret (H.pureOp (.pbytesEq 32 32) (.pair (v pPk) (v pEnt)))

def isGameSpkCFuel (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (spkBundles : Expr O Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)))
    (pk : Expr O Γ (PB 32)) : Comp O I Γ .bool :=
  letV (.pair spkBundles pk) fun bp =>
    bindV (H.callPrim .pow8 (.snd (v bp))) fun pPk =>
      anyMV (min nFuel S.N_spk_tot) (.fst (v bp)) fun b =>
        bindV (H.callPrim .pow8 (beSpkPk (.snd (v b)))) fun pB =>
          .ret (H.pureOp (.pbytesEq 32 32) (.pair (v pB) (v pPk)))

def isGameSpkC (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (spkBundles : Expr O Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)))
    (pk : Expr O Γ (PB 32)) : Comp O I Γ .bool :=
  letV (.pair spkBundles pk) fun bp =>
    bindV (H.callPrim .pow8 (.snd (v bp))) fun pPk =>
      anyMV S.N_spk_tot (.fst (v bp)) fun b =>
        bindV (H.callPrim .pow8 (beSpkPk (.snd (v b)))) fun pB =>
          .ret (H.pureOp (.pbytesEq 32 32) (.pair (v pB) (v pPk)))

def isGameOpkCFuel (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (opkEntries : Expr O Γ (.list (.prod (.prod .nat (.prod .nat .nat)) e2eOpkEntryTy)))
    (pk : Expr O Γ (PB 32)) : Comp O I Γ .bool :=
  letV (.pair opkEntries pk) fun op =>
    bindV (H.callPrim .pow8 (.snd (v op))) fun pPk =>
      anyMV (min nFuel S.N_opk_tot) (.fst (v op)) fun o =>
        bindV (H.callPrim .pow8 (oePk (.snd (v o)))) fun pO =>
          .ret (H.pureOp (.pbytesEq 32 32) (.pair (v pO) (v pPk)))

def isGameOpkC (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (opkEntries : Expr O Γ (.list (.prod (.prod .nat (.prod .nat .nat)) e2eOpkEntryTy)))
    (pk : Expr O Γ (PB 32)) : Comp O I Γ .bool :=
  letV (.pair opkEntries pk) fun op =>
    bindV (H.callPrim .pow8 (.snd (v op))) fun pPk =>
      anyMV S.N_opk_tot (.fst (v op)) fun o =>
        bindV (H.callPrim .pow8 (oePk (.snd (v o)))) fun pO =>
          .ret (H.pureOp (.pbytesEq 32 32) (.pair (v pO) (v pPk)))

def koskBundleOkCFuel (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) (bundle : Expr O Γ bundleT) : Comp O I Γ .bool :=
  letV (.pair st bundle) fun sb =>
    bindV (findHonestCFuel (S := S) H nFuel (stPrin (.fst (v sb))) (bndIkB (.snd (v sb)))) fun hIk =>
      bindV (isAdvRegC H nFuel (stAdv (.fst (v sb))) (bndIkB (.snd (v sb)))) fun aIk =>
        bindV (isGameSpkCFuel (S := S) H nFuel (stSpk (.fst (v sb))) (bndSpkB (.snd (v sb)))) fun gSpk =>
          bindV (isAdvRegC H nFuel (stAdv (.fst (v sb))) (bndSpkB (.snd (v sb)))) fun aSpk =>
            bindV
              (caseOptV (bndOpkB (.snd (v sb)))
                (.ret (.bool true))
                (fun opk =>
                  bindV (isGameOpkCFuel (S := S) H nFuel (stOpk (.fst (v sb))) (.snd (v opk))) fun gOpk =>
                    bindV (isAdvRegC H nFuel (stAdv (.fst (v sb))) (.snd (v opk))) fun aOpk =>
                      .ret (orE (v gOpk) (v aOpk))))
              fun okOpk =>
                .ret (.and (.and (orE (isSomeE (v hIk)) (v aIk))
                                 (orE (v gSpk) (v aSpk)))
                           (v okOpk))

def koskBundleOkC (H : E2EPqxdhHooks ℓ O I) (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) (bundle : Expr O Γ bundleT) : Comp O I Γ .bool :=
  letV (.pair st bundle) fun sb =>
    bindV (findHonestC (S := S) H (stPrin (.fst (v sb))) (bndIkB (.snd (v sb)))) fun hIk =>
      bindV (isAdvRegC H nAdv (stAdv (.fst (v sb))) (bndIkB (.snd (v sb)))) fun aIk =>
        bindV (isGameSpkC (S := S) H (stSpk (.fst (v sb))) (bndSpkB (.snd (v sb)))) fun gSpk =>
          bindV (isAdvRegC H nAdv (stAdv (.fst (v sb))) (bndSpkB (.snd (v sb)))) fun aSpk =>
            bindV
              (caseOptV (bndOpkB (.snd (v sb)))
                (.ret (.bool true))
                (fun opk =>
                  bindV (isGameOpkC (S := S) H (stOpk (.fst (v sb))) (.snd (v opk))) fun gOpk =>
                    bindV (isAdvRegC H nAdv (stAdv (.fst (v sb))) (.snd (v opk))) fun aOpk =>
                      .ret (orE (v gOpk) (v aOpk))))
              fun okOpk =>
                .ret (.and (.and (orE (isSomeE (v hIk)) (v aIk))
                                 (orE (v gSpk) (v aSpk)))
                           (v okOpk))

def koskSenderOkCFuel (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) (ikAPk : Expr O Γ (PB 32)) : Comp O I Γ .bool :=
  letV (.pair st ikAPk) fun si =>
    bindV (findHonestCFuel (S := S) H nFuel (stPrin (.fst (v si))) (.snd (v si))) fun hIk =>
      bindV (isAdvRegC H nFuel (stAdv (.fst (v si))) (.snd (v si))) fun aIk =>
        .ret (orE (isSomeE (v hIk)) (v aIk))

def koskSenderOkC (H : E2EPqxdhHooks ℓ O I) (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) (ikAPk : Expr O Γ (PB 32)) : Comp O I Γ .bool :=
  letV (.pair st ikAPk) fun si =>
    bindV (findHonestC (S := S) H (stPrin (.fst (v si))) (.snd (v si))) fun hIk =>
      bindV (isAdvRegC H nAdv (stAdv (.fst (v si))) (.snd (v si))) fun aIk =>
        .ret (orE (isSomeE (v hIk)) (v aIk))

def resolveSigPkCFuel (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (principals : Expr O Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (ikB : Expr O Γ (PB 32)) : Comp O I Γ (PB 32) :=
  letV (.pair principals ikB) fun pi =>
    bindV (findHonestCFuel (S := S) H nFuel (.fst (v pi)) (.snd (v pi))) fun h =>
      .ret (eCaseOpt (v h) (.snd (v pi)) fun e => peSignPk (.snd (v e)))

def resolveSigPkC (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (principals : Expr O Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (ikB : Expr O Γ (PB 32)) : Comp O I Γ (PB 32) :=
  letV (.pair principals ikB) fun pi =>
    bindV (findHonestC (S := S) H (.fst (v pi)) (.snd (v pi))) fun h =>
      .ret (eCaseOpt (v h) (.snd (v pi)) fun e => peSignPk (.snd (v e)))

def honestPeerCFuel (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (principals : Expr O Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (ikB : Expr O Γ (PB 32)) : Comp O I Γ (.opt .nat) :=
  bindV (findHonestCFuel (S := S) H nFuel principals ikB) fun h =>
    .ret (eCaseOpt (v h) .none fun e =>
      .ite (.not (peCorr (.snd (v e)))) (.some (.fst (v e))) .none)

def honestPeerC (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (principals : Expr O Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (ikB : Expr O Γ (PB 32)) : Comp O I Γ (.opt .nat) :=
  bindV (findHonestC (S := S) H principals ikB) fun h =>
    .ret (eCaseOpt (v h) .none fun e =>
      .ite (.not (peCorr (.snd (v e)))) (.some (.fst (v e))) .none)

def checkProvCFuel (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) (bundle : Expr O Γ bundleT) :
    Comp O I Γ (.prod .bool (.prod .bool .bool)) :=
  letV (.pair st bundle) fun sb =>
    bindV (findHonestCFuel (S := S) H nFuel (stPrin (.fst (v sb))) (bndIkB (.snd (v sb)))) fun h =>
      caseOptV (v h)
        (.ret (.pair (.bool false) (.pair (.bool false) (.bool false))))
        (fun ke =>
          bindV (H.callPrim .pow8 (bndSpkB (.snd (v sb)))) fun pBndSpk =>
            bindV
              (anyMV (min nFuel S.N_spk_tot) (stSpk (.fst (v sb))) fun b =>
                bindV (H.callPrim .pow8 (beSpkPk (.snd (v b)))) fun pB =>
                  .ret (.and (.eqN (.fst (.fst (v b))) (.fst (v ke)))
                             (H.pureOp (.pbytesEq 32 32) (.pair (v pB) (v pBndSpk)))))
              fun spkHon =>
                letV
                  (eAny (min nFuel S.N_spk_tot) (stSpk (.fst (v sb))) fun b =>
                    .and (.eqN (.fst (.fst (v b))) (.fst (v ke)))
                         (H.pureOp (.pbytesEq 1568 1568)
                           (.pair (bePqPk (.snd (v b))) (bndPqB (.snd (v sb))))))
                  fun pqHon =>
                    bindV
                      (caseOptV (bndOpkB (.snd (v sb)))
                        (.ret (.bool false))
                        (fun opk =>
                          bindV (H.callPrim .pow8 (.snd (v opk))) fun pOpk =>
                            anyMV (min nFuel S.N_opk_tot) (stOpk (.fst (v sb))) fun o =>
                              bindV (H.callPrim .pow8 (oePk (.snd (v o)))) fun pO =>
                                .ret (.and (.eqN (.fst (.fst (v o))) (.fst (v ke)))
                                           (H.pureOp (.pbytesEq 32 32) (.pair (v pO) (v pOpk))))))
                      fun opkHon =>
                        .ret (.pair (v spkHon) (.pair (v opkHon) (v pqHon))))

def checkProvC (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) (bundle : Expr O Γ bundleT) :
    Comp O I Γ (.prod .bool (.prod .bool .bool)) :=
  letV (.pair st bundle) fun sb =>
    bindV (findHonestC (S := S) H (stPrin (.fst (v sb))) (bndIkB (.snd (v sb)))) fun h =>
      caseOptV (v h)
        (.ret (.pair (.bool false) (.pair (.bool false) (.bool false))))
        (fun ke =>
          bindV (H.callPrim .pow8 (bndSpkB (.snd (v sb)))) fun pBndSpk =>
            bindV
              (anyMV S.N_spk_tot (stSpk (.fst (v sb))) fun b =>
                bindV (H.callPrim .pow8 (beSpkPk (.snd (v b)))) fun pB =>
                  .ret (.and (.eqN (.fst (.fst (v b))) (.fst (v ke)))
                             (H.pureOp (.pbytesEq 32 32) (.pair (v pB) (v pBndSpk)))))
              fun spkHon =>
                letV
                  (eAny S.N_spk_tot (stSpk (.fst (v sb))) fun b =>
                    .and (.eqN (.fst (.fst (v b))) (.fst (v ke)))
                         (H.pureOp (.pbytesEq 1568 1568)
                           (.pair (bePqPk (.snd (v b))) (bndPqB (.snd (v sb))))))
                  fun pqHon =>
                    bindV
                      (caseOptV (bndOpkB (.snd (v sb)))
                        (.ret (.bool false))
                        (fun opk =>
                          bindV (H.callPrim .pow8 (.snd (v opk))) fun pOpk =>
                            anyMV S.N_opk_tot (stOpk (.fst (v sb))) fun o =>
                              bindV (H.callPrim .pow8 (oePk (.snd (v o)))) fun pO =>
                                .ret (.and (.eqN (.fst (.fst (v o))) (.fst (v ke)))
                                           (H.pureOp (.pbytesEq 32 32) (.pair (v pO) (v pOpk))))))
                      fun opkHon =>
                        .ret (.pair (v spkHon) (.pair (v opkHon) (v pqHon))))

def optPow8C (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (pk? : Expr O Γ (.opt (PB 32))) : Comp O I Γ (.opt (PB 32)) :=
  caseOptV pk?
    (.ret .none)
    (fun pk => bindV (H.callPrim .pow8 (v pk)) fun p => .ret (.some (v p)))

def partnerC (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (s : Expr O Γ (e2eInitiatorEntryTy ℓ S))
    (r : Expr O Γ (e2eRespEntryTy ℓ S)) : Comp O I Γ .bool :=
  letV (.pair s r) fun sr =>
    bindV (H.callPrim .pow8 (hdrIkA (ieHdr (.fst (v sr))))) fun sIkA =>
    bindV (H.callPrim .pow8 (hdrIkA (reHdr (.snd (v sr))))) fun rIkA =>
    bindV (H.callPrim .pow8 (iePeerIk (.fst (v sr)))) fun sIkB =>
    bindV (H.callPrim .pow8 (reIk (.snd (v sr)))) fun rIkB =>
    bindV (H.callPrim .pow8 (iePeerSpk (.fst (v sr)))) fun sSpk =>
    bindV (H.callPrim .pow8 (reSpk (.snd (v sr)))) fun rSpk =>
    bindV (optPow8C H (iePeerOpk (.fst (v sr)))) fun sOpk =>
    bindV (optPow8C H (reOpk (.snd (v sr)))) fun rOpk =>
      .ret (.and
        (.and
          (.and
            (.and
              (.and
                (.and
                  (H.pureOp (.pbytesEq 32 32) (.pair (v sIkA) (v rIkA)))
                  (H.pureOp (.pbytesEq 32 32) (.pair (v sIkB) (v rIkB))))
                (H.pureOp (.pbytesEq 32 32) (.pair (v sSpk) (v rSpk))))
              (optPb32EqE H (v sOpk) (v rOpk)))
            (H.pureOp (.pbytesEq 32 32)
              (.pair (hdrEkA (ieHdr (.fst (v sr)))) (hdrEkA (reHdr (.snd (v sr)))))))
          (H.pureOp (.pbytesEq 1568 1568)
            (.pair (iePeerPq (.fst (v sr))) (rePq (.snd (v sr))))))
        (H.pureOp (.pbytesEq 1568 1568)
          (.pair (hdrKemCt (ieHdr (.fst (v sr)))) (hdrKemCt (reHdr (.snd (v sr)))))))

def partnerRandKeyCFuel (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (respSessions : Expr O Γ (.list (e2eRespEntryTy ℓ S)))
    (s : Expr O Γ (e2eInitiatorEntryTy ℓ S)) : Comp O I Γ (.opt drKeyT) :=
  letV (.pair respSessions s) fun rs =>
    bindV (findMV (min nFuel S.N_recv_tot) (.fst (v rs)) fun r =>
      partnerC H (.snd (v rs)) (v r)) fun found =>
      .ret (optMapE (v found) fun r => reRand (v r))

def partnerRandKeyC (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (respSessions : Expr O Γ (.list (e2eRespEntryTy ℓ S)))
    (s : Expr O Γ (e2eInitiatorEntryTy ℓ S)) : Comp O I Γ (.opt drKeyT) :=
  letV (.pair respSessions s) fun rs =>
    bindV (findMV S.N_recv_tot (.fst (v rs)) fun r =>
      partnerC H (.snd (v rs)) (v r)) fun found =>
      .ret (optMapE (v found) fun r => reRand (v r))

def recordRespCFuel (H : E2EPqxdhHooks ℓ O I) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (r : Expr O Γ (e2eRespEntryTy ℓ S)) : Comp O I Γ (e2eKeyIndStateTy ℓ S) :=
  letV (.pair st r) fun sr =>
    bindV (findMV (min nFuel S.N_send_tot) (stSess (.fst (v sr))) fun s =>
      partnerC H (v s) (.snd (v sr))) fun found =>
      bindV
        (caseOptV (v found)
          (sDrKey96C H)
          (fun s => .ret (ieRand (v s))))
        fun rk =>
          .ret (setRespE (.fst (v sr))
            (.cons (reSetRandE (.snd (v sr)) (v rk)) (stResp (.fst (v sr)))))

def recordRespC (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (r : Expr O Γ (e2eRespEntryTy ℓ S)) : Comp O I Γ (e2eKeyIndStateTy ℓ S) :=
  letV (.pair st r) fun sr =>
    bindV (findMV S.N_send_tot (stSess (.fst (v sr))) fun s =>
      partnerC H (v s) (.snd (v sr))) fun found =>
      bindV
        (caseOptV (v found)
          (sDrKey96C H)
          (fun s => .ret (ieRand (v s))))
        fun rk =>
          .ret (setRespE (.fst (v sr))
            (.cons (reSetRandE (.snd (v sr)) (v rk)) (stResp (.fst (v sr)))))

abbrev accInpTy (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (PB 32) (.prod (PB 32) (.prod (.opt (PB 32))
    (.prod (PB 3168) (.prod .bool (.prod .bool hdrT)))))

def accIkSk {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (accInpTy ℓ)) : Expr O Γ (PB 32) :=
  .fst e
def accSpkSk {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (accInpTy ℓ)) : Expr O Γ (PB 32) :=
  .fst (.snd e)
def accOpkSk {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (accInpTy ℓ)) :
    Expr O Γ (.opt (PB 32)) :=
  .fst (.snd (.snd e))
def accPqSk {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (accInpTy ℓ)) : Expr O Γ (PB 3168) :=
  .fst (.snd (.snd (.snd e)))
def accTp {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (accInpTy ℓ)) : Expr O Γ .bool :=
  .fst (.snd (.snd (.snd (.snd e))))
def accRp {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (accInpTy ℓ)) : Expr O Γ .bool :=
  .fst (.snd (.snd (.snd (.snd (.snd e)))))
def accHdr {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (accInpTy ℓ)) : Expr O Γ hdrT :=
  .snd (.snd (.snd (.snd (.snd (.snd e)))))

/-- Simulates `Model.acceptKeys P` in `Comp`. -/
def acceptKeysC (H : E2EPqxdhHooks ℓ O I) {Γ : List (Ty (e2eSig ℓ))}
    (ikBSk spkBSk : Expr O Γ (PB 32))
    (opkBSk? : Expr O Γ (.opt (PB 32)))
    (pqspkBSk : Expr O Γ (PB 3168))
    (trustedPeer replayOk : Expr O Γ .bool)
    (hdr : Expr O Γ hdrT) : Comp O I Γ (.opt drKeyT) :=
  letV (.pair ikBSk (.pair spkBSk (.pair opkBSk?
      (.pair pqspkBSk (.pair trustedPeer (.pair replayOk hdr)))))) fun inp =>
    .ite
      (.not (.and (accTp (v inp)) (.and (accRp (v inp))
        (.and (.eqN (H.pureOp (.pbytesLen 32) (hdrIkA (accHdr (v inp)))) (.nat 32))
              (.eqN (H.pureOp (.pbytesLen 32) (hdrEkA (accHdr (v inp)))) (.nat 32))))))
      (.ret .none)
      (bindV (H.callPrim .isCanonical (hdrEkA (accHdr (v inp)))) fun can =>
        .ite (.not (v can)) (.ret .none)
          (bindV (H.callPrim .x25519 (.pair (accSpkSk (v inp)) (hdrIkA (accHdr (v inp))))) fun dh1 =>
            .ite (.not (dhNonZeroE H (v dh1))) (.ret .none)
              (bindV (H.callPrim .x25519 (.pair (accIkSk (v inp)) (hdrEkA (accHdr (v inp))))) fun dh2 =>
                .ite (.not (dhNonZeroE H (v dh2))) (.ret .none)
                  (bindV (H.callPrim .x25519 (.pair (accSpkSk (v inp)) (hdrEkA (accHdr (v inp))))) fun dh3 =>
                    .ite (.not (dhNonZeroE H (v dh3))) (.ret .none)
                      (bindV
                        (caseOptV (hdrOpkId (accHdr (v inp)))
                          (caseOptV (accOpkSk (v inp))
                            (.ret (.some (.none : Expr O _ (.opt (PB 32)))))
                            (fun _ => .ret .none))
                          (fun _ =>
                            caseOptV (accOpkSk (v inp))
                              (.ret .none)
                              (fun osk =>
                                bindV (H.callPrim .x25519 (.pair (v osk) (hdrEkA (accHdr (v inp)))))
                                  fun dh4 =>
                                    .ret (.some (.some (v dh4))))))
                        fun dh4Opt? =>
                          caseOptV (v dh4Opt?)
                            (.ret .none)
                            (fun dh4? =>
                              .ite (.not (dhOptNonZeroE H (v dh4?))) (.ret .none)
                                (.ite (.not (.eqN (H.pureOp (.pbytesLen 1568)
                                    (hdrKemCt (accHdr (v inp)))) (.nat 1568)))
                                  (.ret .none)
                                  (bindV (H.callPrim .kemDecaps
                                      (.pair (accPqSk (v inp)) (hdrKemCt (accHdr (v inp)))))
                                    fun ss? =>
                                      caseOptV (v ss?)
                                        (.ret .none)
                                        (fun ss =>
                                          bindV
                                            (H.callPrim .hkdfDerive96
                                              (buildSecretsE H (v dh1) (v dh2) (v dh3)
                                                (v dh4?) (v ss)))
                                            fun dk => .ret (.some (v dk)))))))))))

end Helpers

/-! ## Helper evaluation and zero-query lemmas -/

section HelperProofs

variable {ℓ : ℕ} {S : Setup} {Pt : Type} {P : Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
  {ι : Type} {T : OracleSpec ι} {I₀ : Iface (e2eSig ℓ) T}

private def sidTuple {S : Setup} : SessionId S → ℕ × ℕ × ℕ × ℕ
  | .sendOPK u i => (0, (u.val, (i.val, 0)))
  | .sendNoOPK u i => (1, (u.val, (i.val, 0)))
  | .recvOPK k j o => (2, (k.val, (j.val, o.val)))
  | .recvNoOPK k j l => (3, (k.val, (j.val, l.val)))

set_option linter.unusedSimpArgs false in
private theorem eval_sidKeyE {Γ : List (Ty (e2eSig ℓ))}
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) (ρ : Env Γ) :
    (sidKeyE (I := stepAIface ℓ I₀) (mkStepAPqxdhHooks ℓ P C K decT encT I₀) a).eval ρ =
      sidTuple (sidOfV (a.eval ρ)) := by
  rcases ha : a.eval ρ with ⟨ua, ia⟩ | ⟨ua, ia⟩ | ⟨ka, ja, oa⟩ | ⟨ka, ja, la⟩ <;>
    simp only [sidKeyE, eCaseSum, finValE, mkStepAPqxdhHooks, Expr.eval,
      eval_e2ePureOp, E2EPureOp.eval, eval_v_refl, eval_v_cons, env_get_zero, env_get_succ,
      sidOfV, sidTuple, ha]

theorem eval_sidEqE {Γ : List (Ty (e2eSig ℓ))}
    (a b : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) (ρ : Env Γ) :
    (sidEqE (I := stepAIface ℓ I₀) (mkStepAPqxdhHooks ℓ P C K decT encT I₀) a b).eval ρ =
      (sidOfV (a.eval ρ) == sidOfV (b.eval ρ)) := by
  simp only [sidEqE, eval_nat4EqE, eval_sidKeyE]
  cases sa : sidOfV (a.eval ρ) <;> cases sb : sidOfV (b.eval ρ) <;>
    simp [sidTuple, Fin.ext_iff]

set_option linter.unusedSimpArgs false in
theorem eval_optPu32EqE {Γ : List (Ty (e2eSig ℓ))}
    (a b : Expr (e2eOps ℓ P C K decT encT) Γ (.opt PU32)) (ρ : Env Γ) :
    (optPu32EqE (I := stepAIface ℓ I₀) (mkStepAPqxdhHooks ℓ P C K decT encT I₀) a b).eval ρ =
      (a.eval ρ == b.eval ρ) := by
  rcases ha : a.eval ρ with _ | xa <;> rcases hb : b.eval ρ with _ | xb <;>
    simp [optPu32EqE, optEqByE, eLet, eCaseOpt, mkStepAPqxdhHooks, Expr.eval, eval_e2ePureOp,
      E2EPureOp.eval, ha, hb]

set_option linter.unusedSimpArgs false in
theorem eval_optPb32EqE {Γ : List (Ty (e2eSig ℓ))}
    (a b : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (PB 32))) (ρ : Env Γ) :
    (optPb32EqE (I := stepAIface ℓ I₀) (mkStepAPqxdhHooks ℓ P C K decT encT I₀) a b).eval ρ =
      (a.eval ρ == b.eval ρ) := by
  rcases ha : a.eval ρ with _ | xa <;> rcases hb : b.eval ρ with _ | xb <;>
    simp [optPb32EqE, optEqByE, eLet, eCaseOpt, mkStepAPqxdhHooks, Expr.eval, eval_e2ePureOp,
      E2EPureOp.eval, ha, hb]

@[simp] theorem eval_encECWideE {Γ : List (Ty (e2eSig ℓ))}
    (pk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) (ρ : Env Γ) :
    (encECWideE (I := stepAIface ℓ I₀) (mkStepAPqxdhHooks ℓ P C K decT encT I₀) pk).eval ρ =
      encodeEC (pk.eval ρ) := by
  simp [encECWideE, e2ePureOp, e2eOps, e2ePureOps, Ops.sum, Expr.eval, E2EPureOp.eval, encodeEC]

@[simp] theorem eval_encKEME {Γ : List (Ty (e2eSig ℓ))}
    (pk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 1568)) (ρ : Env Γ) :
    (encKEME (I := stepAIface ℓ I₀) (mkStepAPqxdhHooks ℓ P C K decT encT I₀) pk).eval ρ =
      encodeKEM (pk.eval ρ) := by
  simp [encKEME, e2ePureOp, e2eOps, e2ePureOps, Ops.sum, Expr.eval, E2EPureOp.eval, encodeKEM]

@[simp] theorem eval_dhNonZeroE {Γ : List (Ty (e2eSig ℓ))}
    (dh : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) (ρ : Env Γ) :
    (dhNonZeroE (I := stepAIface ℓ I₀) (mkStepAPqxdhHooks ℓ P C K decT encT I₀) dh).eval ρ =
      (dh.eval ρ != List.replicate 32 0) := by
  simp [dhNonZeroE, zero32E, Expr.eval, eval_e2ePureOp, E2EPureOp.eval, bne]

@[simp] theorem eval_dhOptNonZeroE {Γ : List (Ty (e2eSig ℓ))}
    (dh4? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (PB 32))) (ρ : Env Γ) :
    (dhOptNonZeroE (I := stepAIface ℓ I₀) (mkStepAPqxdhHooks ℓ P C K decT encT I₀) dh4?).eval ρ =
      dhOptNonZero (dh4?.eval ρ) := by
  rcases h : dh4?.eval ρ with _ | dh <;>
    simp [dhOptNonZeroE, eCaseOpt, dhOptNonZero, Expr.eval, h]

private theorem eval_pbytesLit_aux (w : ℕ+) (bs : SignalPqxdh.Bytes) {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ .unit) (ρ : Env Γ) :
    (e2ePureOp (.pbytesLit w bs) e).eval ρ = bs := rfl

private theorem eval_pbytesCat_aux (m n : ℕ+) {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (PB m) (PB n))) (ρ : Env Γ) :
    (e2ePureOp (.pbytesCat m n) e).eval ρ = (e.eval ρ).1 ++ (e.eval ρ).2 := rfl

private theorem eval_pbytesWiden192_aux {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (PB (32 + 32 + 32 + 32 + 32))) (ρ : Env Γ) :
    Expr.eval (t := PB 192) (e2ePureOp (.pbytesWiden (32 + 32 + 32 + 32 + 32) 32) e) ρ =
      e.eval ρ := rfl

private theorem eval_pbytesCat192_aux {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (PB (32 + 32 + 32 + 32 + 32)) (PB 32)))
    (ρ : Env Γ) :
    Expr.eval (t := PB 192) (e2ePureOp (.pbytesCat (32 + 32 + 32 + 32 + 32) 32) e) ρ =
      (e.eval ρ).1 ++ (e.eval ρ).2 := rfl

set_option linter.unusedSimpArgs false in
@[simp] theorem eval_buildSecretsE {Γ : List (Ty (e2eSig ℓ))}
    (dh1 dh2 dh3 : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32))
    (dh4? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (PB 32)))
    (ss : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) (ρ : Env Γ) :
    (buildSecretsE (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) dh1 dh2 dh3 dh4? ss).eval ρ =
      buildSecrets (dh1.eval ρ) (dh2.eval ρ) (dh3.eval ρ) (dh4?.eval ρ) (ss.eval ρ) := by
  unfold buildSecretsE eLet eCaseOpt mkStepAPqxdhHooks v Ext.refl Ext.step Ext.wk
  rcases ho : dh4?.eval ρ with _ | dh4 <;>
    simp only [eval_pbytesLit_aux, eval_pbytesCat_aux, eval_pbytesWiden192_aux,
      eval_pbytesCat192_aux, Expr.eval, env_get_zero, env_get_succ, ho, buildSecrets]

set_option linter.unusedSimpArgs false in
theorem eval_checkSeenEFuel (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (used : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod .nat (.prod PU32 (.prod PU32 (PB 32))))))
    (k : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (pqspkId spkId : Expr (e2eOps ℓ P C K decT encT) Γ PU32)
    (ekAPk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32))
    (ρ : Env Γ) (hused : (used.eval ρ).length ≤ min nFuel S.N_recv_tot) :
    (checkSeenEFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel used k pqspkId spkId ekAPk).eval ρ =
      checkAndMarkKyberBaseKeySeen (used.eval ρ) (k.eval ρ) (pqspkId.eval ρ)
        (spkId.eval ρ) (ekAPk.eval ρ) := by
  simp only [checkSeenEFuel, eLet, eAny, mkStepAPqxdhHooks, v, ext_refl_wk, ext_step_wk,
    Expr.eval, env_get_zero, env_get_succ, eval_e2ePureOp, E2EPureOp.eval,
    List.take_of_length_le hused, checkAndMarkKyberBaseKeySeen]
  apply congrArg (fun b : Bool =>
    if b then (false, used.eval ρ)
    else (true, (k.eval ρ, pqspkId.eval ρ, spkId.eval ρ, ekAPk.eval ρ) :: used.eval ρ))
  rw [List.contains_eq_any_beq]
  apply List.any_congr rfl
  rintro ⟨e1, e2, e3, e4⟩
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq, and_assoc]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨(of_decide_eq_true h1).symm, h2.symm, h3.symm, h4.symm⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨decide_eq_true h1.symm, h2.symm, h3.symm, h4.symm⟩

theorem eval_checkSeenE {Γ : List (Ty (e2eSig ℓ))}
    (used : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod .nat (.prod PU32 (.prod PU32 (PB 32))))))
    (k : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (pqspkId spkId : Expr (e2eOps ℓ P C K decT encT) Γ PU32)
    (ekAPk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32))
    (ρ : Env Γ) (hused : (used.eval ρ).length ≤ S.N_recv_tot) :
    (checkSeenE (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) used k pqspkId spkId ekAPk).eval ρ =
      checkAndMarkKyberBaseKeySeen (used.eval ρ) (k.eval ρ) (pqspkId.eval ρ)
        (spkId.eval ρ) (ekAPk.eval ρ) := by
  have heq : checkSeenE (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) used k pqspkId spkId ekAPk =
    checkSeenEFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) S.N_recv_tot used k pqspkId spkId ekAPk := by
    simp only [checkSeenE, checkSeenEFuel, Nat.min_self]
  rw [heq]
  exact eval_checkSeenEFuel S.N_recv_tot used k pqspkId spkId ekAPk ρ
    (by simpa [Nat.min_self] using hused)

set_option linter.unusedSimpArgs false in
theorem eval_isTestableEFuel (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (ρ : Env Γ) {st : KeyIndState S} (hst_eq : stE.eval ρ = e2eKeyIndStateToVal st)
    (hst : stListBounded S nFuel st) :
    (isTestableEFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel stE sidE).eval ρ =
      isKeyIndSessionTestable st (sidOfV (sidE.eval ρ)) := by
  simp only [isTestableEFuel, eLet, eCaseOpt, eFind, v, ext_refl_wk, ext_step_wk, Expr.eval,
    env_get_zero, env_get_succ, stSess, stResp, hst_eq, e2eKeyIndStateToVal]
  have hs_len : (st.sessions.map (e2eInitiatorEntryToVal (ℓ := ℓ))).length ≤ min nFuel S.N_send_tot := by
    simpa using hst.sessions_le
  have hr_len : (st.respSessions.map (e2eRespEntryToVal (ℓ := ℓ))).length ≤ min nFuel S.N_recv_tot := by
    simpa using hst.respSessions_le
  rw [List.take_of_length_le hs_len, List.take_of_length_le hr_len,
    List.find?_map, List.find?_map]
  rw [show st.sessions.find? _ =
        st.sessions.find? (fun x => x.sid == sidOfV (sidE.eval ρ)) by
      congr 1; funext x; dsimp only [Function.comp_def]
      rw [eval_sidEqE]
      simp [ieSid, e2eInitiatorEntryToVal, v, ext_refl_wk, ext_step_wk, Expr.eval,
        env_get_zero, env_get_succ]]
  rw [show st.respSessions.find? _ =
        st.respSessions.find? (fun r => r.sid == sidOfV (sidE.eval ρ)) by
      congr 1; funext r; dsimp only [Function.comp_def]
      rw [eval_sidEqE]
      simp [reSid, e2eRespEntryToVal, v, ext_refl_wk, ext_step_wk, Expr.eval,
        env_get_zero, env_get_succ]]
  unfold isKeyIndSessionTestable
  rcases h1 : st.sessions.find? (fun x => x.sid == sidOfV (sidE.eval ρ)) with _ | e
  · rcases h2 : st.respSessions.find? (fun r => r.sid == sidOfV (sidE.eval ρ)) with _ | r
    · simp [h1, h2]
    · simp [h1, h2, reSendHon, reTested, reRev, e2eRespEntryToVal, v, ext_refl_wk, ext_step_wk,
        Expr.eval, env_get_zero, env_get_succ]
  · simp [h1, ieFresh, ieTested, ieRev, e2eInitiatorEntryToVal, v, ext_refl_wk, ext_step_wk,
      Expr.eval, env_get_zero, env_get_succ]

theorem eval_isTestableE {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (ρ : Env Γ) {st : KeyIndState S} (hst_eq : stE.eval ρ = e2eKeyIndStateToVal st)
    (hst : KeyIndSetupBounded S st) :
    (isTestableE (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) stE sidE).eval ρ =
      isKeyIndSessionTestable st (sidOfV (sidE.eval ρ)) := by
  let N := KeyIndSetupBounded.maxFuel S st
  have hmin1 : min N S.N_send_tot = S.N_send_tot := by unfold N KeyIndSetupBounded.maxFuel; omega
  have hmin2 : min N S.N_recv_tot = S.N_recv_tot := by unfold N KeyIndSetupBounded.maxFuel; omega
  have heq : isTestableE (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) stE sidE =
    isTestableEFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) N stE sidE := by
    simp only [isTestableE, isTestableEFuel, hmin1, hmin2]
  rw [heq]
  exact eval_isTestableEFuel N stE sidE ρ hst_eq hst.toStListBounded

set_option linter.unusedSimpArgs false in
theorem eval_sBytes32C {Γ : List (Ty (e2eSig ℓ))} (ρ : Env Γ) :
    (sBytes32C (I := stepAIface ℓ I₀) (mkStepAPqxdhHooks ℓ P C K decT encT I₀)).eval ρ =
      (stepAIface ℓ I₀).liftP sampleBytes32 := by
  have hsamp : (stepAIface ℓ I₀).smp.samp (.base .bv256) () = ($ᵗ BitVec 256) := rfl
  simp only [sBytes32C, bindV, mkStepAPqxdhHooks, Comp.eval, v, ext_refl_wk, ext_step_wk,
    Expr.eval, eval_e2ePureOp, E2EPureOp.eval, env_get_zero, hsamp, sampleBytes32,
    liftP_bind, liftP_pure, liftP_map, map_eq_bind_pure_comp, Function.comp_def]
  rfl

set_option linter.unusedSimpArgs false in
theorem eval_sRandom64C {Γ : List (Ty (e2eSig ℓ))} (ρ : Env Γ) :
    (sRandom64C (I := stepAIface ℓ I₀) (mkStepAPqxdhHooks ℓ P C K decT encT I₀)).eval ρ =
      (stepAIface ℓ I₀).liftP sampleRandom64 := by
  simp only [sRandom64C, bindV, Comp.eval, eval_sBytes32C]
  simp only [mkStepAPqxdhHooks, Expr.eval, e2ePureOp, e2eOps, e2ePureOps, Ops.sum, E2EPureOp.eval,
    eval_v_refl, eval_v_cons, env_get_zero, env_get_succ, sampleRandom64, liftP_bind, liftP_pure,
    map_eq_bind_pure_comp, Function.comp_def, LawfulMonad.bind_assoc, pure_bind]

set_option linter.unusedSimpArgs false in
theorem eval_sDrKey96C {Γ : List (Ty (e2eSig ℓ))} (ρ : Env Γ) :
    (sDrKey96C (I := stepAIface ℓ I₀) (mkStepAPqxdhHooks ℓ P C K decT encT I₀)).eval ρ =
      (stepAIface ℓ I₀).liftP (drKeyV <$> sampleDRKey96) := by
  simp only [sDrKey96C, bindV, Comp.eval, eval_sBytes32C]
  simp only [Expr.eval, eval_v_refl, eval_v_cons, env_get_zero, env_get_succ, sampleDRKey96,
    drKeyV, liftP_map, liftP_bind, liftP_pure, map_eq_bind_pure_comp, Function.comp_def,
    LawfulMonad.bind_assoc, pure_bind]

set_option linter.unusedSimpArgs false in
theorem eval_sKemKeyGenC (hP : WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))} (ρ : Env Γ) :
    (sKemKeyGenC (I := stepAIface ℓ I₀) (mkStepAPqxdhHooks ℓ P C K decT encT I₀)).eval ρ =
      (stepAIface ℓ I₀).liftP (sampleKemKeyGen P) := by
  simp only [sKemKeyGenC, bindV, Comp.eval, eval_sRandom64C]
  simp only [mkStepAPqxdhHooks, Comp.eval, Expr.eval, eval_e2eCryptoOp, eval_v_refl, env_get_zero,
    sampleKemKeyGen, liftP_bind, liftP_pure]
  congr 1
  funext seed
  exact congrArg pure (e2eCryptoOps_eval_kemKeyGen_lossless ℓ hP C K seed)

set_option linter.unusedSimpArgs false in
theorem eval_findHonestCFuel (hP : WellFormedPrimitivesδ P) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (psE : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (ikBE : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) (ρ : Env Γ)
    {principals : List (ℕ × PrincipalEntry)}
    (hps : psE.eval ρ = principals.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ))))
    (hlen : principals.length ≤ min nFuel S.N_id) :
    (findHonestCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel psE ikBE).eval ρ =
      pure ((findHonestPrincipal P principals (ikBE.eval ρ)).map
        (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ)))) := by
  have hlen' :
      (principals.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ)))).length ≤ min nFuel S.N_id := by
    simp [hlen]
  simp only [findHonestCFuel, letV, bindV, findMV, mkStepAPqxdhHooks, Comp.eval, Expr.eval,
    eval_e2eCryptoOp, eval_e2ePureOp, E2EPureOp.eval, eval_v_refl, eval_v_cons,
    env_get_zero, env_get_succ, pure_bind, peIkPk, hps, List.take_of_length_le hlen']
  have hp1 := e2eCryptoOps_eval_pow8_lossless ℓ hP C K (ikBE.eval ρ)
  dsimp only [e2eCryptoOps] at hp1
  rw [hp1, findML_map]
  rw [show findML _ principals =
        findML (fun x => pure (P.pow8 (ikBE.eval ρ) == P.pow8 x.2.ikAPk)) principals from
      findML_congr fun ⟨idx, ent⟩ _ => by
        dsimp only [Prod.map, id, e2ePrincipalEntryToVal]
        have hp2 := e2eCryptoOps_eval_pow8_lossless ℓ hP C K ent.ikAPk
        dsimp only [e2eCryptoOps] at hp2
        rw [hp2]]
  rw [findML_pure, map_pure]
  rfl

theorem eval_findHonestC (hP : WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (psE : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (ikBE : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) (ρ : Env Γ)
    {principals : List (ℕ × PrincipalEntry)}
    (hps : psE.eval ρ = principals.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ))))
    (hlen : principals.length ≤ S.N_id) :
    (findHonestC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) psE ikBE).eval ρ =
      pure ((findHonestPrincipal P principals (ikBE.eval ρ)).map
        (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ)))) := by
  have heq : findHonestC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) psE ikBE =
    findHonestCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) S.N_id psE ikBE := by
    simp only [findHonestC, findHonestCFuel, Nat.min_self]
  rw [heq]
  exact eval_findHonestCFuel hP S.N_id psE ikBE ρ hps (by simpa [Nat.min_self] using hlen)

set_option linter.unusedSimpArgs false in
theorem eval_isAdvRegC (hP : WellFormedPrimitivesδ P) (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (akE : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod (PB 32) (PB 32))))
    (pkE : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) (ρ : Env Γ)
    (hlen : (akE.eval ρ).length ≤ nAdv) :
    (isAdvRegC (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv akE pkE).eval ρ =
      pure (isAdvRegistered P (akE.eval ρ) (pkE.eval ρ)) := by
  simp only [isAdvRegC, letV, bindV, anyMV, mkStepAPqxdhHooks, Comp.eval, Expr.eval,
    eval_e2eCryptoOp, eval_e2ePureOp, E2EPureOp.eval, eval_v_refl, eval_v_cons,
    env_get_zero, env_get_succ, pure_bind, List.take_of_length_le hlen]
  have hp1 := e2eCryptoOps_eval_pow8_lossless ℓ hP C K (pkE.eval ρ)
  dsimp only [e2eCryptoOps] at hp1
  rw [hp1]
  rw [show anyML _ (akE.eval ρ) =
        anyML (fun x => pure (P.pow8 (pkE.eval ρ) == P.pow8 x.2)) (akE.eval ρ) from
      anyML_congr fun ⟨sk, pk'⟩ _ => by
        have hp2 := e2eCryptoOps_eval_pow8_lossless ℓ hP C K pk'
        dsimp only [e2eCryptoOps] at hp2
        rw [hp2]]
  rw [anyML_pure]
  rfl

set_option linter.unusedSimpArgs false in
theorem eval_isGameSpkCFuel (hP : WellFormedPrimitivesδ P) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (bsE : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)))
    (pkE : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) (ρ : Env Γ)
    {spkBundles : List ((ℕ × ℕ) × SpkBundleEntry)}
    (hbs : bsE.eval ρ = spkBundles.map (Prod.map id (e2eSpkBundleEntryToVal (ℓ := ℓ))))
    (hlen : spkBundles.length ≤ min nFuel S.N_spk_tot) :
    (isGameSpkCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel bsE pkE).eval ρ =
      pure (isGameSpk P spkBundles (pkE.eval ρ)) := by
  have hlen' :
      (spkBundles.map (Prod.map id (e2eSpkBundleEntryToVal (ℓ := ℓ)))).length ≤ min nFuel S.N_spk_tot := by
    simp [hlen]
  simp only [isGameSpkCFuel, letV, bindV, anyMV, mkStepAPqxdhHooks, Comp.eval, Expr.eval,
    eval_e2eCryptoOp, eval_e2ePureOp, E2EPureOp.eval, eval_v_refl, eval_v_cons,
    env_get_zero, env_get_succ, pure_bind, beSpkPk, hbs, List.take_of_length_le hlen']
  have hp1 := e2eCryptoOps_eval_pow8_lossless ℓ hP C K (pkE.eval ρ)
  dsimp only [e2eCryptoOps] at hp1
  rw [hp1, anyML_map]
  rw [show anyML _ spkBundles =
        anyML (fun b => pure (P.pow8 b.2.spkPk == P.pow8 (pkE.eval ρ))) spkBundles from
      anyML_congr fun ⟨_, b⟩ _ => by
        dsimp only [Prod.map, id, e2eSpkBundleEntryToVal]
        have hp2 := e2eCryptoOps_eval_pow8_lossless ℓ hP C K b.spkPk
        dsimp only [e2eCryptoOps] at hp2
        rw [hp2]]
  rw [anyML_pure]
  rfl

theorem eval_isGameSpkC (hP : WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (bsE : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)))
    (pkE : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) (ρ : Env Γ)
    {spkBundles : List ((ℕ × ℕ) × SpkBundleEntry)}
    (hbs : bsE.eval ρ = spkBundles.map (Prod.map id (e2eSpkBundleEntryToVal (ℓ := ℓ))))
    (hlen : spkBundles.length ≤ S.N_spk_tot) :
    (isGameSpkC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) bsE pkE).eval ρ =
      pure (isGameSpk P spkBundles (pkE.eval ρ)) := by
  have heq : isGameSpkC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) bsE pkE =
    isGameSpkCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) S.N_spk_tot bsE pkE := by
    simp only [isGameSpkC, isGameSpkCFuel, Nat.min_self]
  rw [heq]
  exact eval_isGameSpkCFuel hP S.N_spk_tot bsE pkE ρ hbs (by simpa [Nat.min_self] using hlen)

set_option linter.unusedSimpArgs false in
theorem eval_isGameOpkCFuel (hP : WellFormedPrimitivesδ P) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (osE : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod (.prod .nat (.prod .nat .nat)) e2eOpkEntryTy)))
    (pkE : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) (ρ : Env Γ)
    {opkEntries : List ((ℕ × ℕ × ℕ) × OpkEntry)}
    (hos : osE.eval ρ = opkEntries.map (Prod.map id (e2eOpkEntryToVal (ℓ := ℓ))))
    (hlen : opkEntries.length ≤ min nFuel S.N_opk_tot) :
    (isGameOpkCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel osE pkE).eval ρ =
      pure (isGameOpk P opkEntries (pkE.eval ρ)) := by
  have hlen' :
      (opkEntries.map (Prod.map id (e2eOpkEntryToVal (ℓ := ℓ)))).length ≤ min nFuel S.N_opk_tot := by
    simp [hlen]
  simp only [isGameOpkCFuel, letV, bindV, anyMV, mkStepAPqxdhHooks, Comp.eval, Expr.eval,
    eval_e2eCryptoOp, eval_e2ePureOp, E2EPureOp.eval, eval_v_refl, eval_v_cons,
    env_get_zero, env_get_succ, pure_bind, oePk, hos, List.take_of_length_le hlen']
  have hp1 := e2eCryptoOps_eval_pow8_lossless ℓ hP C K (pkE.eval ρ)
  dsimp only [e2eCryptoOps] at hp1
  rw [hp1, anyML_map]
  rw [show anyML _ opkEntries =
        anyML (fun o => pure (P.pow8 o.2.opkPk == P.pow8 (pkE.eval ρ))) opkEntries from
      anyML_congr fun ⟨_, o⟩ _ => by
        dsimp only [Prod.map, id, e2eOpkEntryToVal]
        have hp2 := e2eCryptoOps_eval_pow8_lossless ℓ hP C K o.opkPk
        dsimp only [e2eCryptoOps] at hp2
        rw [hp2]]
  rw [anyML_pure]
  rfl

theorem eval_isGameOpkC (hP : WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (osE : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod (.prod .nat (.prod .nat .nat)) e2eOpkEntryTy)))
    (pkE : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) (ρ : Env Γ)
    {opkEntries : List ((ℕ × ℕ × ℕ) × OpkEntry)}
    (hos : osE.eval ρ = opkEntries.map (Prod.map id (e2eOpkEntryToVal (ℓ := ℓ))))
    (hlen : opkEntries.length ≤ S.N_opk_tot) :
    (isGameOpkC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) osE pkE).eval ρ =
      pure (isGameOpk P opkEntries (pkE.eval ρ)) := by
  have heq : isGameOpkC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) osE pkE =
    isGameOpkCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) S.N_opk_tot osE pkE := by
    simp only [isGameOpkC, isGameOpkCFuel, Nat.min_self]
  rw [heq]
  exact eval_isGameOpkCFuel hP S.N_opk_tot osE pkE ρ hos (by simpa [Nat.min_self] using hlen)

set_option linter.unusedSimpArgs false in
theorem eval_koskBundleOkCFuel (hP : WellFormedPrimitivesδ P) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (bndE : Expr (e2eOps ℓ P C K decT encT) Γ bundleT) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : stE.eval ρ = e2eKeyIndStateToVal st)
    (hst : stListBounded S nFuel st) :
    (koskBundleOkCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel stE bndE).eval ρ =
      pure (koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys
        (bundleOfV (bndE.eval ρ))) := by
  set bnd := bundleOfV (bndE.eval ρ)
  have hbnd : bndE.eval ρ = bundleV bnd := (bundleV_bundleOfV (bndE.eval ρ)).symm
  simp only [koskBundleOkCFuel, letV, bindV, Comp.eval, Expr.eval, eval_v_refl, eval_v_cons,
    env_get_zero, env_get_succ, pure_bind, hst_eq, hbnd]
  rw [eval_findHonestCFuel hP nFuel _ _ _ (by simp [stPrin, e2eKeyIndStateToVal, Expr.eval])
        hst.principals_le, pure_bind,
    eval_isAdvRegC hP nFuel _ _ _ (by simpa [stAdv, e2eKeyIndStateToVal, Expr.eval] using hst.advKeys_le),
    pure_bind,
    eval_isGameSpkCFuel hP nFuel _ _ _ (by simp [stSpk, e2eKeyIndStateToVal, Expr.eval])
      hst.spkBundles_le, pure_bind,
    eval_isAdvRegC hP nFuel _ _ _ (by simpa [stAdv, e2eKeyIndStateToVal, Expr.eval] using hst.advKeys_le),
    pure_bind]
  rw [show (caseOptV _ _ _).eval _ =
        pure (match bnd.opkB? with
              | none => true
              | some (_, opkPk) =>
                isGameOpk P st.opkEntries opkPk || isAdvRegistered P st.advKeys opkPk) by
      simp only [caseOptV, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, bndOpkB,
        bundleV, env_get_zero, env_get_succ]
      rcases bnd.opkB? with _ | ⟨oid, opkPk⟩
      · rfl
      · simp only [bindV, Comp.eval]
        rw [eval_isGameOpkCFuel hP nFuel _ _ _
              (by simp [stOpk, e2eKeyIndStateToVal, v, ext_refl_wk, ext_step_wk, Expr.eval,
                env_get_zero, env_get_succ])
              hst.opkEntries_le, pure_bind,
          eval_isAdvRegC hP nFuel _ _ _
            (by simpa [stAdv, e2eKeyIndStateToVal, v, ext_refl_wk, ext_step_wk, Expr.eval,
              env_get_zero, env_get_succ] using hst.advKeys_le),
          pure_bind]
        simp [stAdv, e2eKeyIndStateToVal, v, Ext.wk, Ext.refl, Ext.step, Expr.eval, eval_orE,
          env_get_zero, env_get_succ]]
  rw [pure_bind]
  simp only [koskBundleOk, isGameIdKey, bndIkB, bndSpkB, bundleV, stAdv, e2eKeyIndStateToVal,
    v, Ext.wk, Ext.refl, Ext.step, Expr.eval, eval_orE, eval_isSomeE, env_get_zero, env_get_succ,
    Comp.eval]
  rcases bnd.opkB? with _ | ⟨_, opkPk⟩ <;> simp

set_option linter.unusedSimpArgs false in
theorem eval_koskBundleOkC (hP : WellFormedPrimitivesδ P) (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (bndE : Expr (e2eOps ℓ P C K decT encT) Γ bundleT) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : stE.eval ρ = e2eKeyIndStateToVal st)
    (hst : KeyIndSetupBounded S st) (hadv : st.advKeys.length ≤ nAdv) :
    (koskBundleOkC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv stE bndE).eval ρ =
      pure (koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys
        (bundleOfV (bndE.eval ρ))) := by
  set bnd := bundleOfV (bndE.eval ρ)
  have hbnd : bndE.eval ρ = bundleV bnd := (bundleV_bundleOfV (bndE.eval ρ)).symm
  simp only [koskBundleOkC, letV, bindV, Comp.eval, Expr.eval, eval_v_refl, eval_v_cons,
    env_get_zero, env_get_succ, pure_bind, hst_eq, hbnd]
  rw [eval_findHonestC hP _ _ _ (by simp [stPrin, e2eKeyIndStateToVal, Expr.eval])
        hst.principals_le, pure_bind,
    eval_isAdvRegC hP nAdv _ _ _ (by simpa [stAdv, e2eKeyIndStateToVal, Expr.eval] using hadv),
    pure_bind,
    eval_isGameSpkC hP _ _ _ (by simp [stSpk, e2eKeyIndStateToVal, Expr.eval])
      hst.spkBundles_le, pure_bind,
    eval_isAdvRegC hP nAdv _ _ _ (by simpa [stAdv, e2eKeyIndStateToVal, Expr.eval] using hadv),
    pure_bind]
  rw [show (caseOptV _ _ _).eval _ =
        pure (match bnd.opkB? with
              | none => true
              | some (_, opkPk) =>
                isGameOpk P st.opkEntries opkPk || isAdvRegistered P st.advKeys opkPk) by
      simp only [caseOptV, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, bndOpkB,
        bundleV, env_get_zero, env_get_succ]
      rcases bnd.opkB? with _ | ⟨oid, opkPk⟩
      · rfl
      · simp only [bindV, Comp.eval]
        rw [eval_isGameOpkC hP _ _ _
              (by simp [stOpk, e2eKeyIndStateToVal, v, ext_refl_wk, ext_step_wk, Expr.eval,
                env_get_zero, env_get_succ])
              hst.opkEntries_le, pure_bind,
          eval_isAdvRegC hP nAdv _ _ _
            (by simpa [stAdv, e2eKeyIndStateToVal, v, ext_refl_wk, ext_step_wk, Expr.eval,
              env_get_zero, env_get_succ] using hadv),
          pure_bind]
        simp [stAdv, e2eKeyIndStateToVal, v, Ext.wk, Ext.refl, Ext.step, Expr.eval, eval_orE,
          env_get_zero, env_get_succ]]
  rw [pure_bind]
  simp only [koskBundleOk, isGameIdKey, bndIkB, bndSpkB, bundleV, stAdv, e2eKeyIndStateToVal,
    v, Ext.wk, Ext.refl, Ext.step, Expr.eval, eval_orE, eval_isSomeE, env_get_zero, env_get_succ,
    Comp.eval]
  rcases bnd.opkB? with _ | ⟨_, opkPk⟩ <;> simp

set_option linter.unusedSimpArgs false in
theorem eval_koskSenderOkCFuel (hP : WellFormedPrimitivesδ P) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (ikE : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : stE.eval ρ = e2eKeyIndStateToVal st)
    (hst : stListBounded S nFuel st) :
    (koskSenderOkCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel stE ikE).eval ρ =
      pure (koskSenderOk P st.principals st.advKeys (ikE.eval ρ)) := by
  simp only [koskSenderOkCFuel, letV, bindV, Comp.eval, Expr.eval, eval_v_refl, eval_v_cons,
    env_get_zero, env_get_succ, pure_bind, hst_eq]
  rw [eval_findHonestCFuel hP nFuel _ _ _ (by simp [stPrin, e2eKeyIndStateToVal, Expr.eval])
        hst.principals_le, pure_bind,
    eval_isAdvRegC hP nFuel _ _ _ (by simpa [stAdv, e2eKeyIndStateToVal, Expr.eval] using hst.advKeys_le),
    pure_bind]
  simp [koskSenderOk, isGameIdKey, stAdv, e2eKeyIndStateToVal, Expr.eval, eval_orE, eval_isSomeE,
    eval_v_cons, eval_v_refl, env_get_zero, env_get_succ]

set_option linter.unusedSimpArgs false in
theorem eval_koskSenderOkC (hP : WellFormedPrimitivesδ P) (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (ikE : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : stE.eval ρ = e2eKeyIndStateToVal st)
    (hst : KeyIndSetupBounded S st) (hadv : st.advKeys.length ≤ nAdv) :
    (koskSenderOkC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv stE ikE).eval ρ =
      pure (koskSenderOk P st.principals st.advKeys (ikE.eval ρ)) := by
  simp only [koskSenderOkC, letV, bindV, Comp.eval, Expr.eval, eval_v_refl, eval_v_cons,
    env_get_zero, env_get_succ, pure_bind, hst_eq]
  rw [eval_findHonestC hP _ _ _ (by simp [stPrin, e2eKeyIndStateToVal, Expr.eval])
        hst.principals_le, pure_bind,
    eval_isAdvRegC hP nAdv _ _ _ (by simpa [stAdv, e2eKeyIndStateToVal, Expr.eval] using hadv),
    pure_bind]
  simp [koskSenderOk, isGameIdKey, stAdv, e2eKeyIndStateToVal, Expr.eval, eval_orE, eval_isSomeE,
    eval_v_cons, eval_v_refl, env_get_zero, env_get_succ]

set_option linter.unusedSimpArgs false in
theorem eval_resolveSigPkCFuel (hP : WellFormedPrimitivesδ P) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (psE : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (ikE : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) (ρ : Env Γ)
    {principals : List (ℕ × PrincipalEntry)}
    (hps : psE.eval ρ = principals.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ))))
    (hlen : principals.length ≤ min nFuel S.N_id) :
    (resolveSigPkCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel psE ikE).eval ρ =
      pure (resolveSigPk P principals (ikE.eval ρ)) := by
  simp only [resolveSigPkCFuel, letV, bindV, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval,
    env_get_zero, env_get_succ, pure_bind]
  rw [eval_findHonestCFuel hP nFuel _ _ _
        (by simpa [Expr.eval, env_get_zero] using hps) hlen, pure_bind]
  unfold resolveSigPk
  rcases h : findHonestPrincipal P principals (ikE.eval ρ) with _ | ⟨k, ent⟩ <;>
    simp [h, eCaseOpt, peSignPk, e2ePrincipalEntryToVal, v, ext_refl_wk, ext_step_wk, Expr.eval,
      env_get_zero, env_get_succ]

theorem eval_resolveSigPkC (hP : WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (psE : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (ikE : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) (ρ : Env Γ)
    {principals : List (ℕ × PrincipalEntry)}
    (hps : psE.eval ρ = principals.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ))))
    (hlen : principals.length ≤ S.N_id) :
    (resolveSigPkC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) psE ikE).eval ρ =
      pure (resolveSigPk P principals (ikE.eval ρ)) := by
  have heq : resolveSigPkC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) psE ikE =
    resolveSigPkCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) S.N_id psE ikE := by
    simp only [resolveSigPkC, resolveSigPkCFuel, findHonestC, findHonestCFuel, Nat.min_self]
  rw [heq]
  exact eval_resolveSigPkCFuel hP S.N_id psE ikE ρ hps (by simpa [Nat.min_self] using hlen)

set_option linter.unusedSimpArgs false in
theorem eval_honestPeerCFuel (hP : WellFormedPrimitivesδ P) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (psE : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (ikE : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) (ρ : Env Γ)
    {principals : List (ℕ × PrincipalEntry)}
    (hps : psE.eval ρ = principals.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ))))
    (hlen : principals.length ≤ min nFuel S.N_id) :
    (honestPeerCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel psE ikE).eval ρ =
      pure (isHonestUncorruptedPeer P principals (ikE.eval ρ)) := by
  simp only [honestPeerCFuel, bindV, Comp.eval]
  rw [eval_findHonestCFuel hP nFuel _ _ _ hps hlen, pure_bind]
  unfold isHonestUncorruptedPeer
  rcases h : findHonestPrincipal P principals (ikE.eval ρ) with _ | ⟨k, ent⟩ <;>
    simp [h, eCaseOpt, peCorr, e2ePrincipalEntryToVal, v, ext_refl_wk, ext_step_wk, Expr.eval,
      env_get_zero, env_get_succ]

theorem eval_honestPeerC (hP : WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (psE : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (ikE : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) (ρ : Env Γ)
    {principals : List (ℕ × PrincipalEntry)}
    (hps : psE.eval ρ = principals.map (Prod.map id (e2ePrincipalEntryToVal (ℓ := ℓ))))
    (hlen : principals.length ≤ S.N_id) :
    (honestPeerC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) psE ikE).eval ρ =
      pure (isHonestUncorruptedPeer P principals (ikE.eval ρ)) := by
  have heq : honestPeerC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) psE ikE =
    honestPeerCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) S.N_id psE ikE := by
    simp only [honestPeerC, honestPeerCFuel, findHonestC, findHonestCFuel, Nat.min_self]
  rw [heq]
  exact eval_honestPeerCFuel hP S.N_id psE ikE ρ hps (by simpa [Nat.min_self] using hlen)

set_option linter.unusedSimpArgs false in
theorem eval_checkProvCFuel (hP : WellFormedPrimitivesδ P) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (bndE : Expr (e2eOps ℓ P C K decT encT) Γ bundleT) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : stE.eval ρ = e2eKeyIndStateToVal st)
    (hst : stListBounded S nFuel st) :
    (checkProvCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel stE bndE).eval ρ =
      pure (let (a, b, c) :=
              checkBundleProvenance P st.principals st.spkBundles st.opkEntries
                (bundleOfV (bndE.eval ρ))
            (a, (b, c))) := by
  set bnd := bundleOfV (bndE.eval ρ)
  have hbnd : bndE.eval ρ = bundleV bnd := (bundleV_bundleOfV (bndE.eval ρ)).symm
  simp only [checkProvCFuel, letV, bindV, Comp.eval, Expr.eval, eval_v_refl, eval_v_cons,
    env_get_zero, env_get_succ, pure_bind, hst_eq, hbnd]
  rw [eval_findHonestCFuel hP nFuel _ _ _ (by simp [stPrin, e2eKeyIndStateToVal, Expr.eval])
        hst.principals_le, pure_bind]
  unfold checkBundleProvenance
  simp only [caseOptV, Comp.eval, Expr.eval, eval_v_refl, eval_v_cons, env_get_zero, env_get_succ,
    bndIkB, bundleV]
  rcases h : findHonestPrincipal P st.principals bnd.ikB with _ | ⟨k, ent⟩
  · simp [h]
  · have hspk_len :
        (st.spkBundles.map (Prod.map id (e2eSpkBundleEntryToVal (ℓ := ℓ)))).length ≤
          min nFuel S.N_spk_tot := by simpa using hst.spkBundles_le
    have hopk_len :
        (st.opkEntries.map (Prod.map id (e2eOpkEntryToVal (ℓ := ℓ)))).length ≤
          min nFuel S.N_opk_tot := by simpa using hst.opkEntries_le
    simp only [h, Option.map, Prod.map, id, bindV, letV, anyMV, eAny, mkStepAPqxdhHooks, Comp.eval,
      Expr.eval, eval_e2eCryptoOp, eval_e2ePureOp, E2EPureOp.eval, v, ext_refl_wk, ext_step_wk,
      env_get_zero, env_get_succ, pure_bind, stSpk, stOpk, e2eKeyIndStateToVal,
      beSpkPk, bePqPk, bndSpkB, bndPqB, bndOpkB, bundleV, List.take_of_length_le hspk_len]
    have hp_bspk := e2eCryptoOps_eval_pow8_lossless ℓ hP C K bnd.spkB
    dsimp only [e2eCryptoOps] at hp_bspk
    rw [hp_bspk, anyML_map]
    rw [show anyML _ st.spkBundles =
          anyML (fun x => pure ((x.1.1 == k) && (P.pow8 x.2.spkPk == P.pow8 bnd.spkB)))
            st.spkBundles from
        anyML_congr fun ⟨⟨u, _⟩, b⟩ _ => by
          dsimp only [Prod.map, id, e2eSpkBundleEntryToVal]
          have hp := e2eCryptoOps_eval_pow8_lossless ℓ hP C K b.spkPk
          dsimp only [e2eCryptoOps] at hp
          rw [hp]
          by_cases hk : u = k <;> by_cases hs : P.pow8 b.spkPk = P.pow8 bnd.spkB <;>
            simp [hk, hs]]
    rw [anyML_pure, pure_bind]
    rw [show (st.spkBundles.map _).any _ =
          st.spkBundles.any (fun ((u, _), b) => (u == k) && (b.pqspkPk == bnd.pqspkB)) by
        rw [List.any_map]
        apply List.any_congr rfl
        rintro ⟨⟨u, _⟩, b⟩
        dsimp only [Function.comp_def, Prod.map, id, e2eSpkBundleEntryToVal]
        by_cases hk : u = k <;> by_cases hpq : b.pqspkPk = bnd.pqspkB <;>
          simp [hk, hpq]]
    rcases bnd.opkB? with _ | ⟨_, opkPk⟩
    · simp [caseOptV, Comp.eval, v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ]
    · simp only [caseOptV, bindV, anyMV, mkStepAPqxdhHooks, Comp.eval, v, ext_refl_wk, ext_step_wk,
        Expr.eval, eval_e2eCryptoOp, eval_e2ePureOp, E2EPureOp.eval,
        env_get_zero, env_get_succ, pure_bind, stOpk, oePk, e2eKeyIndStateToVal,
        List.take_of_length_le hopk_len]
      have hp_opk := e2eCryptoOps_eval_pow8_lossless ℓ hP C K opkPk
      dsimp only [e2eCryptoOps] at hp_opk
      rw [hp_opk, anyML_map]
      rw [show anyML _ st.opkEntries =
            anyML (fun x => pure ((x.1.1 == k) && (P.pow8 x.2.opkPk == P.pow8 opkPk)))
              st.opkEntries from
          anyML_congr fun ⟨⟨u, _, _⟩, o⟩ _ => by
            dsimp only [Prod.map, id, e2eOpkEntryToVal]
            have hp := e2eCryptoOps_eval_pow8_lossless ℓ hP C K o.opkPk
            dsimp only [e2eCryptoOps] at hp
            rw [hp]
            by_cases hk : u = k <;> by_cases ho : P.pow8 o.opkPk = P.pow8 opkPk <;>
              simp [hk, ho]]
      rw [anyML_pure]
      simp [v, ext_refl_wk, ext_step_wk, Expr.eval, env_get_zero, env_get_succ]

theorem eval_checkProvC (hP : WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (bndE : Expr (e2eOps ℓ P C K decT encT) Γ bundleT) (ρ : Env Γ)
    {st : KeyIndState S} (hst_eq : stE.eval ρ = e2eKeyIndStateToVal st)
    (hst : KeyIndSetupBounded S st) :
    (checkProvC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) stE bndE).eval ρ =
      pure (let (a, b, c) :=
              checkBundleProvenance P st.principals st.spkBundles st.opkEntries
                (bundleOfV (bndE.eval ρ))
            (a, (b, c))) := by
  let N := KeyIndSetupBounded.maxFuel S st
  have hmin1 : min N S.N_id = S.N_id := by unfold N KeyIndSetupBounded.maxFuel; omega
  have hmin2 : min N S.N_spk_tot = S.N_spk_tot := by unfold N KeyIndSetupBounded.maxFuel; omega
  have hmin3 : min N S.N_opk_tot = S.N_opk_tot := by unfold N KeyIndSetupBounded.maxFuel; omega
  have heq : checkProvC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) stE bndE =
    checkProvCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) N stE bndE := by
    simp only [checkProvC, checkProvCFuel, findHonestC, findHonestCFuel, hmin1, hmin2, hmin3]
  rw [heq]
  exact eval_checkProvCFuel hP N stE bndE ρ hst_eq hst.toStListBounded

set_option linter.unusedSimpArgs false in
theorem eval_optPow8C (hP : WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (pk? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (PB 32))) (ρ : Env Γ) :
    (optPow8C (I := stepAIface ℓ I₀) (mkStepAPqxdhHooks ℓ P C K decT encT I₀) pk?).eval ρ =
      pure ((pk?.eval ρ).map P.pow8) := by
  rcases h : pk?.eval ρ with _ | pk
  · simp [optPow8C, caseOptV, Comp.eval, Expr.eval, h]
  · simp only [optPow8C, caseOptV, bindV, mkStepAPqxdhHooks, Comp.eval, Expr.eval,
      eval_e2eCryptoOp, eval_v_refl, env_get_zero, pure_bind, h, Option.map]
    have hp := e2eCryptoOps_eval_pow8_lossless ℓ hP C K pk
    dsimp only [e2eCryptoOps] at hp
    rw [hp]

set_option linter.unusedSimpArgs false in
theorem eval_partnerC (hP : WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (sE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eInitiatorEntryTy ℓ S))
    (rE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eRespEntryTy ℓ S)) (ρ : Env Γ)
    {s : KeyIndInitiatorEntry S} {r : KeyIndRespEntry S}
    (hs : sE.eval ρ = e2eInitiatorEntryToVal s)
    (hr : rE.eval ρ = e2eRespEntryToVal r) :
    (partnerC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) sE rE).eval ρ =
      pure (keyIndPartner P s r) := by
  have hp1 := e2eCryptoOps_eval_pow8_lossless ℓ hP C K s.hdr.ikAPk
  have hp2 := e2eCryptoOps_eval_pow8_lossless ℓ hP C K r.hdr.ikAPk
  have hp3 := e2eCryptoOps_eval_pow8_lossless ℓ hP C K s.peerIkPk
  have hp4 := e2eCryptoOps_eval_pow8_lossless ℓ hP C K r.respIkPk
  have hp5 := e2eCryptoOps_eval_pow8_lossless ℓ hP C K s.peerSpkPk
  have hp6 := e2eCryptoOps_eval_pow8_lossless ℓ hP C K r.spkPk
  dsimp only [e2eCryptoOps] at hp1 hp2 hp3 hp4 hp5 hp6
  simp only [partnerC, letV, bindV, Comp.eval, Expr.eval, eval_v_refl, eval_v_cons,
    env_get_zero, env_get_succ, pure_bind, hs, hr]
  rw [eval_optPow8C hP, pure_bind, eval_optPow8C hP, pure_bind]
  simp only [mkStepAPqxdhHooks, Comp.eval, Expr.eval, eval_e2eCryptoOp, eval_e2ePureOp,
    E2EPureOp.eval, eval_optPb32EqE, eval_v_refl, eval_v_cons, env_get_zero, env_get_succ,
    pure_bind, ieHdr, iePeerIk, iePeerSpk, iePeerOpk, iePeerPq, e2eInitiatorEntryToVal,
    reHdr, reIk, reSpk, reOpk, rePq, e2eRespEntryToVal,
    hdrIkA, hdrEkA, hdrKemCt, hdrV, hp1, hp2, hp3, hp4, hp5, hp6, keyIndPartner]

set_option linter.unusedSimpArgs false in
theorem eval_partnerRandKeyCFuel (hP : WellFormedPrimitivesδ P) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (rsE : Expr (e2eOps ℓ P C K decT encT) Γ (.list (e2eRespEntryTy ℓ S)))
    (sE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eInitiatorEntryTy ℓ S)) (ρ : Env Γ)
    {respSessions : List (KeyIndRespEntry S)} {s : KeyIndInitiatorEntry S}
    (hrs : rsE.eval ρ = respSessions.map (e2eRespEntryToVal (ℓ := ℓ)))
    (hs : sE.eval ρ = e2eInitiatorEntryToVal s)
    (hlen : respSessions.length ≤ min nFuel S.N_recv_tot) :
    (partnerRandKeyCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel rsE sE).eval ρ =
      pure ((keyIndPartnerRandKey? P respSessions s).map drKeyV) := by
  have hlen' : (respSessions.map (e2eRespEntryToVal (ℓ := ℓ))).length ≤ min nFuel S.N_recv_tot := by
    simp [hlen]
  simp only [partnerRandKeyCFuel, letV, bindV, findMV, Comp.eval, Expr.eval, eval_v_refl, eval_v_cons,
    env_get_zero, env_get_succ, pure_bind, hrs, hs, List.take_of_length_le hlen']
  rw [findML_map]
  rw [show findML _ respSessions = findML (fun r => pure (keyIndPartner P s r)) respSessions from
      findML_congr fun r _ => eval_partnerC hP _ _ _
        (by simp [Expr.eval, eval_v_refl, eval_v_cons, env_get_zero, env_get_succ])
        (by simp [Expr.eval, eval_v_refl, eval_v_cons, env_get_zero, env_get_succ])]
  rw [findML_pure, map_pure, pure_bind]
  unfold keyIndPartnerRandKey?
  rcases h : respSessions.find? (fun r => keyIndPartner P s r) with _ | r <;>
    simp [h, eval_optMapE, reRand, e2eRespEntryToVal, v, ext_refl_wk, ext_step_wk, Expr.eval,
      env_get_zero, env_get_succ]

theorem eval_partnerRandKeyC (hP : WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (rsE : Expr (e2eOps ℓ P C K decT encT) Γ (.list (e2eRespEntryTy ℓ S)))
    (sE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eInitiatorEntryTy ℓ S)) (ρ : Env Γ)
    {respSessions : List (KeyIndRespEntry S)} {s : KeyIndInitiatorEntry S}
    (hrs : rsE.eval ρ = respSessions.map (e2eRespEntryToVal (ℓ := ℓ)))
    (hs : sE.eval ρ = e2eInitiatorEntryToVal s)
    (hlen : respSessions.length ≤ S.N_recv_tot) :
    (partnerRandKeyC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) rsE sE).eval ρ =
      pure ((keyIndPartnerRandKey? P respSessions s).map drKeyV) := by
  have heq : partnerRandKeyC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) rsE sE =
    partnerRandKeyCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) S.N_recv_tot rsE sE := by
    simp only [partnerRandKeyC, partnerRandKeyCFuel, Nat.min_self]
  rw [heq]
  exact eval_partnerRandKeyCFuel hP S.N_recv_tot rsE sE ρ hrs hs
    (by simpa [Nat.min_self] using hlen)

set_option linter.unusedSimpArgs false in
theorem eval_recordRespCFuel (hP : WellFormedPrimitivesδ P) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (rE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eRespEntryTy ℓ S)) (ρ : Env Γ)
    {st : KeyIndState S} {r : KeyIndRespEntry S}
    (hst_eq : stE.eval ρ = e2eKeyIndStateToVal st)
    (hr_eq : rE.eval ρ = e2eRespEntryToVal r)
    (hlen : st.sessions.length ≤ min nFuel S.N_send_tot) :
    (recordRespCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel stE rE).eval ρ =
      (stepAIface ℓ I₀).liftP
        ((fun p => e2eKeyIndStateToVal p.2) <$> ((recordKeyIndResp S P r).run st)) := by
  have hlen' : (st.sessions.map (e2eInitiatorEntryToVal (ℓ := ℓ))).length ≤ min nFuel S.N_send_tot := by
    simpa using hlen
  simp only [recordRespCFuel, letV, bindV, findMV, Comp.eval, Expr.eval, eval_v_refl, eval_v_cons,
    env_get_zero, env_get_succ, pure_bind, hst_eq, hr_eq, stSess, e2eKeyIndStateToVal,
    List.take_of_length_le hlen']
  rw [findML_map]
  rw [show findML _ st.sessions = findML (fun s => pure (keyIndPartner P s r)) st.sessions from
      findML_congr fun s _ => eval_partnerC hP _ _ _
        (by simp [Expr.eval, eval_v_refl, eval_v_cons, env_get_zero, env_get_succ])
        (by simp [Expr.eval, eval_v_refl, eval_v_cons, env_get_zero, env_get_succ])]
  rw [findML_pure, map_pure, pure_bind]
  unfold recordKeyIndResp
  simp only [st_run_get_bind, st_run_getOf_bind, LawfulMonad.bind_assoc]
  rcases h : st.sessions.find? (fun s => keyIndPartner P s r) with _ | s
  · simp only [h, Option.map, caseOptV, Comp.eval, v, Ext.wk, Ext.refl, Ext.step, Expr.eval,
      env_get_zero, env_get_succ, eval_sDrKey96C, st_run_lift_bind, st_run_set,
      liftP_map, liftP_bind, liftP_pure, map_eq_bind_pure_comp, map_bind, map_pure,
      Function.comp_def, LawfulMonad.bind_assoc, pure_bind]
    congr 1
  · simp only [h, Option.map, caseOptV, Comp.eval, v, Ext.wk, Ext.refl, Ext.step, Expr.eval,
      env_get_zero, env_get_succ, pure_bind, st_run_pure, st_run_set, liftP_map, liftP_pure,
      map_pure, ieRand, e2eInitiatorEntryToVal]
    cases st; cases r
    simp [setRespE, reSetRandE, eLet, v, Ext.wk, Ext.refl, Ext.step, Expr.eval,
      env_get_zero, env_get_succ,
      e2eKeyIndStateToVal, e2eRespEntryToVal, stSecb, stPrin, stSpk, stOpk, stSess, stResp,
      reSid, reIk, reSpk, reOpk, rePq, reHdr, reSendHon, reReal, reTested, reRev]

theorem eval_recordRespC (hP : WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (rE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eRespEntryTy ℓ S)) (ρ : Env Γ)
    {st : KeyIndState S} {r : KeyIndRespEntry S}
    (hst_eq : stE.eval ρ = e2eKeyIndStateToVal st)
    (hr_eq : rE.eval ρ = e2eRespEntryToVal r)
    (hlen : st.sessions.length ≤ S.N_send_tot) :
    (recordRespC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) stE rE).eval ρ =
      (stepAIface ℓ I₀).liftP
        ((fun p => e2eKeyIndStateToVal p.2) <$> ((recordKeyIndResp S P r).run st)) := by
  have heq : recordRespC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) stE rE =
    recordRespCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) S.N_send_tot stE rE := by
    simp only [recordRespC, recordRespCFuel, Nat.min_self]
  rw [heq]
  exact eval_recordRespCFuel hP S.N_send_tot stE rE ρ hst_eq hr_eq
    (by simpa [Nat.min_self] using hlen)

private def zero32 : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem replicate32_zero_eq : List.replicate 32 (0 : UInt8) = zero32 := rfl

set_option linter.unusedSimpArgs false in
theorem eval_acceptKeysC (hP : WellFormedPrimitivesδ P) {Γ : List (Ty (e2eSig ℓ))}
    (ikBSk spkBSk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32))
    (opkBSk? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (PB 32)))
    (pqspkBSk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 3168))
    (trustedPeer replayOk : Expr (e2eOps ℓ P C K decT encT) Γ .bool)
    (hdrE : Expr (e2eOps ℓ P C K decT encT) Γ hdrT) (ρ : Env Γ) :
    (acceptKeysC (I := stepAIface ℓ I₀) (mkStepAPqxdhHooks ℓ P C K decT encT I₀)
      ikBSk spkBSk opkBSk? pqspkBSk trustedPeer replayOk hdrE).eval ρ =
      pure ((acceptKeys P {
        ikBSk := ikBSk.eval ρ
        ikBPk := []
        spkBSk := spkBSk.eval ρ
        spkBPk := []
        opkBSk? := opkBSk?.eval ρ
        pqspkBSk := pqspkBSk.eval ρ
        pqspkBPk := []
        trustedPeer := trustedPeer.eval ρ
        replayOk := replayOk.eval ρ
        hdr := hdrOfV (hdrE.eval ρ) }).map drKeyV) := by
  set hdr := hdrOfV (hdrE.eval ρ)
  have hhdr : hdrE.eval ρ = hdrV hdr := (hdrV_hdrOfV (hdrE.eval ρ)).symm
  have hican : E2ECryptoOp.eval ℓ P C K .isCanonical hdr.ekAPk = P.isCanonical hdr.ekAPk := rfl
  have hdh1 := e2eCryptoOps_eval_x25519_lossless ℓ hP C K (spkBSk.eval ρ) hdr.ikAPk
  have hdh2 := e2eCryptoOps_eval_x25519_lossless ℓ hP C K (ikBSk.eval ρ) hdr.ekAPk
  have hdh3 := e2eCryptoOps_eval_x25519_lossless ℓ hP C K (spkBSk.eval ρ) hdr.ekAPk
  have hdec := e2eCryptoOps_eval_kemDecaps_lossless ℓ hP C K (pqspkBSk.eval ρ) hdr.kemCt
  dsimp only [e2eCryptoOps] at hdh1 hdh2 hdh3 hdec
  simp only [acceptKeysC, accIkSk, accSpkSk, accOpkSk, accPqSk, accTp, accRp, accHdr,
    letV, bindV, caseOptV, mkStepAPqxdhHooks, Comp.eval, v, Ext.wk, Ext.refl, Ext.step,
    Expr.eval, eval_e2eCryptoOp, eval_e2ePureOp, E2EPureOp.eval, env_get_zero, env_get_succ,
    pure_bind, hhdr, hdrIkA, hdrEkA, hdrOpkId, hdrKemCt, hdrV, hican, hdh1, hdh2, hdh3]
  by_cases htp : trustedPeer.eval ρ = true
  · by_cases hrp : replayOk.eval ρ = true
    · by_cases hik : hdr.ikAPk.length = 32
      · by_cases hek : hdr.ekAPk.length = 32
        · by_cases hcan : P.isCanonical hdr.ekAPk = true
          · simp only [htp, hrp, hik, hek, hcan, decide_true, Bool.and_self, Bool.not_true,
              ↓reduceIte, ite_false, eval_dhNonZeroE, Expr.eval, env_get_zero, env_get_succ,
              replicate32_zero_eq]
            by_cases h1 : P.x25519 (spkBSk.eval ρ) hdr.ikAPk = zero32
            · simp [acceptKeys, «guard», replicate32_zero_eq, htp, hrp, hik, hek, hcan, h1]
            · by_cases h2 : P.x25519 (ikBSk.eval ρ) hdr.ekAPk = zero32
              · simp [acceptKeys, «guard», replicate32_zero_eq, htp, hrp, hik, hek, hcan, h1, h2]
              · by_cases h3 : P.x25519 (spkBSk.eval ρ) hdr.ekAPk = zero32
                · simp [acceptKeys, «guard», replicate32_zero_eq, htp, hrp, hik, hek, hcan,
                    h1, h2, h3]
                · rcases hopkId : hdr.opkId? with _ | oid <;>
                    rcases hopkSk : opkBSk?.eval ρ with _ | osk
                  · by_cases hct : hdr.kemCt.length = 1568
                    · simp only [h1, h2, h3, hct, bne_iff_ne, ne_eq, not_false_eq_true,
                        decide_true, Bool.not_true, ↓reduceIte, ite_false, Comp.eval, Expr.eval,
                        eval_e2ePureOp, E2EPureOp.eval, env_get_zero, env_get_succ, pure_bind,
                        eval_dhOptNonZeroE, dhOptNonZero, hdec]
                      rcases hkd : P.kemDecaps (pqspkBSk.eval ρ) hdr.kemCt with _ | ss
                      · simp [acceptKeys, kyberCtLen, «guard», replicate32_zero_eq, htp, hrp, hik,
                          hek, hcan, h1, h2, h3, hopkId, hopkSk, dhOptNonZero, hct, hkd]
                      · have hhk := e2eCryptoOps_eval_hkdfDerive96_lossless ℓ hP C K
                          (buildSecrets (P.x25519 (spkBSk.eval ρ) hdr.ikAPk)
                            (P.x25519 (ikBSk.eval ρ) hdr.ekAPk)
                            (P.x25519 (spkBSk.eval ρ) hdr.ekAPk) none ss)
                        dsimp only [e2eCryptoOps] at hhk
                        simp [acceptKeys, kyberCtLen, «guard», replicate32_zero_eq, htp, hrp, hik,
                          hek, hcan, h1, h2, h3, hopkId, hopkSk, dhOptNonZero, hct, hkd, Comp.eval,
                          Expr.eval, eval_e2eCryptoOp, eval_buildSecretsE, env_get_zero,
                          env_get_succ, hhk, drKeyV]
                    · simp [acceptKeys, kyberCtLen, «guard», replicate32_zero_eq, Comp.eval,
                        Expr.eval, eval_e2ePureOp, E2EPureOp.eval, eval_dhOptNonZeroE,
                        dhOptNonZero, htp, hrp, hik, hek, hcan, h1, h2, h3, hopkId, hopkSk, hct]
                  · simp [acceptKeys, «guard», replicate32_zero_eq, htp, hrp, hik, hek, hcan,
                      h1, h2, h3, hopkId, hopkSk]
                  · simp [acceptKeys, «guard», replicate32_zero_eq, htp, hrp, hik, hek, hcan,
                      h1, h2, h3, hopkId, hopkSk]
                  · have hdh4 := e2eCryptoOps_eval_x25519_lossless ℓ hP C K osk hdr.ekAPk
                    dsimp only [e2eCryptoOps] at hdh4
                    simp only [h1, h2, h3, bne_iff_ne, ne_eq, not_false_eq_true,
                      decide_true, Bool.not_true, ↓reduceIte, ite_false, Comp.eval, Expr.eval,
                      eval_e2eCryptoOp, env_get_zero, env_get_succ, pure_bind, hdh4,
                      eval_dhOptNonZeroE]
                    by_cases h4 : dhOptNonZero (some (P.x25519 osk hdr.ekAPk)) = true
                    · by_cases hct : hdr.kemCt.length = 1568
                      · simp only [h4, hct, decide_true, Bool.not_true, ↓reduceIte, ite_false,
                          Comp.eval, Expr.eval, eval_e2ePureOp, E2EPureOp.eval, eval_e2eCryptoOp,
                          env_get_zero, env_get_succ, pure_bind, hdec]
                        rcases hkd : P.kemDecaps (pqspkBSk.eval ρ) hdr.kemCt with _ | ss
                        · simp [acceptKeys, kyberCtLen, «guard», replicate32_zero_eq, htp, hrp, hik,
                            hek, hcan, h1, h2, h3, hopkId, hopkSk, h4, hct, hkd]
                        · have hhk := e2eCryptoOps_eval_hkdfDerive96_lossless ℓ hP C K
                            (buildSecrets (P.x25519 (spkBSk.eval ρ) hdr.ikAPk)
                              (P.x25519 (ikBSk.eval ρ) hdr.ekAPk)
                              (P.x25519 (spkBSk.eval ρ) hdr.ekAPk)
                              (some (P.x25519 osk hdr.ekAPk)) ss)
                          dsimp only [e2eCryptoOps] at hhk
                          simp [acceptKeys, kyberCtLen, «guard», replicate32_zero_eq, htp, hrp, hik,
                            hek, hcan, h1, h2, h3, hopkId, hopkSk, h4, hct, hkd, Comp.eval,
                            Expr.eval, eval_e2eCryptoOp, eval_buildSecretsE, env_get_zero,
                            env_get_succ, hhk, drKeyV]
                      · simp [acceptKeys, kyberCtLen, «guard», replicate32_zero_eq, Comp.eval,
                          Expr.eval, eval_e2ePureOp, E2EPureOp.eval, htp, hrp, hik, hek, hcan,
                          h1, h2, h3, hopkId, hopkSk, h4, hct]
                    · simp [acceptKeys, «guard», replicate32_zero_eq, Comp.eval, Expr.eval,
                        htp, hrp, hik, hek, hcan, h1, h2, h3, hopkId, hopkSk, h4]
          · simp [acceptKeys, «guard», htp, hrp, hik, hek, hcan]
        · simp [acceptKeys, «guard», htp, hrp, hik, hek]
      · simp [acceptKeys, «guard», htp, hrp, hik]
    · simp [acceptKeys, «guard», htp, hrp]
  · simp [acceptKeys, «guard», htp]

set_option linter.unusedSimpArgs false in
theorem acceptKeys_some_matched {P : Primitives} {inp : AcceptKeysInput} {dk : DRKey}
    (hacc : acceptKeys P inp = some dk)
    (hmatch : (inp.hdr.opkId? = none ∧ inp.opkBSk? = none) ∨
              (∃ oid osk, inp.hdr.opkId? = some oid ∧ inp.opkBSk? = some osk)) :
    ∃ ss, P.kemDecaps inp.pqspkBSk inp.hdr.kemCt = some ss ∧
      dk = P.hkdfDerive96 (buildSecrets
        (P.x25519 inp.spkBSk inp.hdr.ikAPk)
        (P.x25519 inp.ikBSk inp.hdr.ekAPk)
        (P.x25519 inp.spkBSk inp.hdr.ekAPk)
        (inp.opkBSk?.map fun osk => P.x25519 osk inp.hdr.ekAPk)
        ss) := by
  by_cases htp : inp.trustedPeer = true
  · by_cases hrp : inp.replayOk = true
    · by_cases hik : inp.hdr.ikAPk.length = 32
      · by_cases hek : inp.hdr.ekAPk.length = 32
        · by_cases hcan : P.isCanonical inp.hdr.ekAPk = true
          · by_cases h1 : P.x25519 inp.spkBSk inp.hdr.ikAPk = zero32
            · simp [acceptKeys, «guard», replicate32_zero_eq, h1] at hacc
            · by_cases h2 : P.x25519 inp.ikBSk inp.hdr.ekAPk = zero32
              · simp [acceptKeys, «guard», replicate32_zero_eq, h2] at hacc
              · by_cases h3 : P.x25519 inp.spkBSk inp.hdr.ekAPk = zero32
                · simp [acceptKeys, «guard», replicate32_zero_eq, h3] at hacc
                · rcases hmatch with ⟨ho1, ho2⟩ | ⟨oid, osk, ho1, ho2⟩
                  · by_cases hct : inp.hdr.kemCt.length = 1568
                    · rcases hdec : P.kemDecaps inp.pqspkBSk inp.hdr.kemCt with _ | ss
                      · simp [acceptKeys, kyberCtLen, «guard», replicate32_zero_eq, htp, hrp, hik,
                          hek, hcan, h1, h2, h3, ho1, ho2, dhOptNonZero, hct, hdec] at hacc
                      · simp [acceptKeys, kyberCtLen, «guard», replicate32_zero_eq, htp, hrp, hik,
                          hek, hcan, h1, h2, h3, ho1, ho2, dhOptNonZero, hct, hdec] at hacc
                        simp only [ho2, Option.map]
                        exact ⟨ss, rfl, hacc.symm⟩
                    · simp [acceptKeys, kyberCtLen, «guard», replicate32_zero_eq, htp, hrp, hik,
                        hek, hcan, h1, h2, h3, ho1, ho2, dhOptNonZero, hct] at hacc
                  · by_cases h4 : dhOptNonZero (some (P.x25519 osk inp.hdr.ekAPk)) = true
                    · by_cases hct : inp.hdr.kemCt.length = 1568
                      · rcases hdec : P.kemDecaps inp.pqspkBSk inp.hdr.kemCt with _ | ss
                        · simp [acceptKeys, kyberCtLen, «guard», replicate32_zero_eq, htp, hrp, hik,
                            hek, hcan, h1, h2, h3, ho1, ho2, h4, hct, hdec] at hacc
                        · simp [acceptKeys, kyberCtLen, «guard», replicate32_zero_eq, htp, hrp, hik,
                            hek, hcan, h1, h2, h3, ho1, ho2, h4, hct, hdec] at hacc
                          simp only [ho2, Option.map]
                          exact ⟨ss, rfl, hacc.symm⟩
                      · simp [acceptKeys, kyberCtLen, «guard», replicate32_zero_eq, htp, hrp, hik,
                          hek, hcan, h1, h2, h3, ho1, ho2, h4, hct] at hacc
                    · simp [acceptKeys, «guard», replicate32_zero_eq, htp, hrp, hik, hek, hcan,
                        h1, h2, h3, ho1, ho2, h4] at hacc
          · simp [acceptKeys, «guard», hcan] at hacc
        · simp [acceptKeys, «guard», hek] at hacc
      · simp [acceptKeys, «guard», hik] at hacc
    · simp [acceptKeys, «guard», hrp] at hacc
  · simp [acceptKeys, «guard», htp] at hacc

end HelperProofs

section HelperZeroQueries

variable {ℓ : ℕ} {S : Setup} {O : Ops (e2eSig ℓ)} {ι : Type} {T : OracleSpec ι}
  {I : Iface (e2eSig ℓ) T}

theorem queriesUB_sBytes32C {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) {Γ : List (Ty (e2eSig ℓ))} :
    compQueriesUB w (fun _ => 0) (sBytes32C H (Γ := Γ)) = 0 := by
  simp [sBytes32C, hw.sampBv256_q]

theorem queriesUB_sRandom64C {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) {Γ : List (Ty (e2eSig ℓ))} :
    compQueriesUB w (fun _ => 0) (sRandom64C H (Γ := Γ)) = 0 := by
  simp [sRandom64C, queriesUB_sBytes32C hw, compQueriesUB]

theorem queriesUB_sDrKey96C {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) {Γ : List (Ty (e2eSig ℓ))} :
    compQueriesUB w (fun _ => 0) (sDrKey96C H (Γ := Γ)) = 0 := by
  simp [sDrKey96C, queriesUB_sBytes32C hw]

theorem queriesUB_sKemKeyGenC {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) {Γ : List (Ty (e2eSig ℓ))} :
    compQueriesUB w (fun _ => 0) (sKemKeyGenC H (Γ := Γ)) = 0 := by
  simp [sKemKeyGenC, queriesUB_sRandom64C hw, hw.callPrim_q]

theorem queriesUB_findHonestCFuel {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (ps : Expr O Γ (.list (.prod .nat e2ePrincipalEntryTy))) (ik : Expr O Γ (PB 32)) :
    compQueriesUB w (fun _ => 0) (findHonestCFuel (S := S) H nFuel ps ik) = 0 := by
  simp [findHonestCFuel, hw.callPrim_q]

theorem queriesUB_findHonestC {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) {Γ : List (Ty (e2eSig ℓ))}
    (ps : Expr O Γ (.list (.prod .nat e2ePrincipalEntryTy))) (ik : Expr O Γ (PB 32)) :
    compQueriesUB w (fun _ => 0) (findHonestC (S := S) H ps ik) = 0 := by
  simp [findHonestC, hw.callPrim_q]

theorem queriesUB_isAdvRegC {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (ak : Expr O Γ (.list (.prod (PB 32) (PB 32)))) (pk : Expr O Γ (PB 32)) :
    compQueriesUB w (fun _ => 0) (isAdvRegC H nAdv ak pk) = 0 := by
  simp [isAdvRegC, hw.callPrim_q]

theorem queriesUB_isGameSpkCFuel {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (bs : Expr O Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy))) (pk : Expr O Γ (PB 32)) :
    compQueriesUB w (fun _ => 0) (isGameSpkCFuel (S := S) H nFuel bs pk) = 0 := by
  simp [isGameSpkCFuel, hw.callPrim_q]

theorem queriesUB_isGameSpkC {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) {Γ : List (Ty (e2eSig ℓ))}
    (bs : Expr O Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy))) (pk : Expr O Γ (PB 32)) :
    compQueriesUB w (fun _ => 0) (isGameSpkC (S := S) H bs pk) = 0 := by
  simp [isGameSpkC, hw.callPrim_q]

theorem queriesUB_isGameOpkCFuel {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (os : Expr O Γ (.list (.prod (.prod .nat (.prod .nat .nat)) e2eOpkEntryTy)))
    (pk : Expr O Γ (PB 32)) :
    compQueriesUB w (fun _ => 0) (isGameOpkCFuel (S := S) H nFuel os pk) = 0 := by
  simp [isGameOpkCFuel, hw.callPrim_q]

theorem queriesUB_isGameOpkC {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) {Γ : List (Ty (e2eSig ℓ))}
    (os : Expr O Γ (.list (.prod (.prod .nat (.prod .nat .nat)) e2eOpkEntryTy)))
    (pk : Expr O Γ (PB 32)) :
    compQueriesUB w (fun _ => 0) (isGameOpkC (S := S) H os pk) = 0 := by
  simp [isGameOpkC, hw.callPrim_q]

theorem queriesUB_koskBundleOkCFuel {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) (bnd : Expr O Γ bundleT) :
    compQueriesUB w (fun _ => 0) (koskBundleOkCFuel (S := S) H nFuel st bnd) = 0 := by
  simp [koskBundleOkCFuel, queriesUB_findHonestCFuel hw, queriesUB_isAdvRegC hw,
    queriesUB_isGameSpkCFuel hw, queriesUB_isGameOpkCFuel hw]

theorem queriesUB_koskBundleOkC {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) (bnd : Expr O Γ bundleT) :
    compQueriesUB w (fun _ => 0) (koskBundleOkC (S := S) H nAdv st bnd) = 0 := by
  simp [koskBundleOkC, queriesUB_findHonestC hw, queriesUB_isAdvRegC hw,
    queriesUB_isGameSpkC hw, queriesUB_isGameOpkC hw]

theorem queriesUB_koskSenderOkCFuel {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) (ik : Expr O Γ (PB 32)) :
    compQueriesUB w (fun _ => 0) (koskSenderOkCFuel (S := S) H nFuel st ik) = 0 := by
  simp [koskSenderOkCFuel, queriesUB_findHonestCFuel hw, queriesUB_isAdvRegC hw]

theorem queriesUB_koskSenderOkC {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) (nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) (ik : Expr O Γ (PB 32)) :
    compQueriesUB w (fun _ => 0) (koskSenderOkC (S := S) H nAdv st ik) = 0 := by
  simp [koskSenderOkC, queriesUB_findHonestC hw, queriesUB_isAdvRegC hw]

theorem queriesUB_resolveSigPkCFuel {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (ps : Expr O Γ (.list (.prod .nat e2ePrincipalEntryTy))) (ik : Expr O Γ (PB 32)) :
    compQueriesUB w (fun _ => 0) (resolveSigPkCFuel (S := S) H nFuel ps ik) = 0 := by
  simp [resolveSigPkCFuel, queriesUB_findHonestCFuel hw]

theorem queriesUB_resolveSigPkC {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) {Γ : List (Ty (e2eSig ℓ))}
    (ps : Expr O Γ (.list (.prod .nat e2ePrincipalEntryTy))) (ik : Expr O Γ (PB 32)) :
    compQueriesUB w (fun _ => 0) (resolveSigPkC (S := S) H ps ik) = 0 := by
  simp [resolveSigPkC, queriesUB_findHonestC hw]

theorem queriesUB_honestPeerCFuel {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (ps : Expr O Γ (.list (.prod .nat e2ePrincipalEntryTy))) (ik : Expr O Γ (PB 32)) :
    compQueriesUB w (fun _ => 0) (honestPeerCFuel (S := S) H nFuel ps ik) = 0 := by
  simp [honestPeerCFuel, queriesUB_findHonestCFuel hw]

theorem queriesUB_honestPeerC {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) {Γ : List (Ty (e2eSig ℓ))}
    (ps : Expr O Γ (.list (.prod .nat e2ePrincipalEntryTy))) (ik : Expr O Γ (PB 32)) :
    compQueriesUB w (fun _ => 0) (honestPeerC (S := S) H ps ik) = 0 := by
  simp [honestPeerC, queriesUB_findHonestC hw]

theorem queriesUB_checkProvCFuel {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) (bnd : Expr O Γ bundleT) :
    compQueriesUB w (fun _ => 0) (checkProvCFuel (S := S) H nFuel st bnd) = 0 := by
  simp [checkProvCFuel, queriesUB_findHonestCFuel hw, hw.callPrim_q]

theorem queriesUB_checkProvC {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) (bnd : Expr O Γ bundleT) :
    compQueriesUB w (fun _ => 0) (checkProvC (S := S) H st bnd) = 0 := by
  simp [checkProvC, queriesUB_findHonestC hw, hw.callPrim_q]

theorem queriesUB_optPow8C {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) {Γ : List (Ty (e2eSig ℓ))}
    (pk? : Expr O Γ (.opt (PB 32))) :
    compQueriesUB w (fun _ => 0) (optPow8C H pk?) = 0 := by
  simp [optPow8C, hw.callPrim_q]

theorem queriesUB_partnerC {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) {Γ : List (Ty (e2eSig ℓ))}
    (s : Expr O Γ (e2eInitiatorEntryTy ℓ S)) (r : Expr O Γ (e2eRespEntryTy ℓ S)) :
    compQueriesUB w (fun _ => 0) (partnerC (S := S) H s r) = 0 := by
  simp [partnerC, queriesUB_optPow8C hw, hw.callPrim_q]

theorem queriesUB_partnerRandKeyCFuel {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (rs : Expr O Γ (.list (e2eRespEntryTy ℓ S))) (s : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    compQueriesUB w (fun _ => 0) (partnerRandKeyCFuel (S := S) H nFuel rs s) = 0 := by
  simp [partnerRandKeyCFuel, queriesUB_partnerC hw]

theorem queriesUB_partnerRandKeyC {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) {Γ : List (Ty (e2eSig ℓ))}
    (rs : Expr O Γ (.list (e2eRespEntryTy ℓ S))) (s : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    compQueriesUB w (fun _ => 0) (partnerRandKeyC (S := S) H rs s) = 0 := by
  simp [partnerRandKeyC, queriesUB_partnerC hw]

theorem queriesUB_recordRespCFuel {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) (nFuel : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) (r : Expr O Γ (e2eRespEntryTy ℓ S)) :
    compQueriesUB w (fun _ => 0) (recordRespCFuel (S := S) H nFuel st r) = 0 := by
  simp [recordRespCFuel, queriesUB_partnerC hw, queriesUB_sDrKey96C hw]

theorem queriesUB_recordRespC {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) {Γ : List (Ty (e2eSig ℓ))}
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) (r : Expr O Γ (e2eRespEntryTy ℓ S)) :
    compQueriesUB w (fun _ => 0) (recordRespC (S := S) H st r) = 0 := by
  simp [recordRespC, queriesUB_partnerC hw, queriesUB_sDrKey96C hw]

theorem queriesUB_acceptKeysC {H : E2EPqxdhHooks ℓ O I} {w : I.Tag → ℕ}
    (hw : HooksNoTargetQueries H w) {Γ : List (Ty (e2eSig ℓ))}
    (ikBSk spkBSk : Expr O Γ (PB 32)) (opkBSk? : Expr O Γ (.opt (PB 32)))
    (pqspkBSk : Expr O Γ (PB 3168)) (trustedPeer replayOk : Expr O Γ .bool)
    (hdr : Expr O Γ hdrT) :
    compQueriesUB w (fun _ => 0)
      (acceptKeysC H ikBSk spkBSk opkBSk? pqspkBSk trustedPeer replayOk hdr) = 0 := by
  simp [acceptKeysC, hw.callPrim_q]

end HelperZeroQueries

end Computational.Proofs.E2E.Dsl.PqxdhSimTypes

