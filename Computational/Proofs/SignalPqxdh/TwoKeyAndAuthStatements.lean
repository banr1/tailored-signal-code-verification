/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.TwoKeyAndAuthGames
public import Computational.Specifications.Pqxdh.Security.HeadlineDelta
public import Computational.Proofs.SpecLemmas.Pqxdh.Security.BoundProofDefs

/-!
# Standalone two-key `KeyInd` and `Auth` costed reduction bundles and δ-statements

**Checked by Lean.** Equips the standalone two-key `KeyInd` (`pqxdhKeyIndExp`, DEV-PQ13) and
first-message `Auth` (`pqxdhAuthExp`) games with `ReductionDsl` challenger interfaces and defines
`KeyInd2KeyCostedReductionFamily`, `AuthCostedReductionFamily`, and `Pqxdh2KeyCorrectAndSecureδ`.
No theorem of `Computational/Theorems/` imports this file; see `Computational/docs/TRUSTED_BASE.md`.
-/

@[expose] public section

set_option autoImplicit false

/-! ## Challenger interfaces -/

namespace SignalPqxdh.Costed

open _root_.ReductionDsl (Ty Iface)
open OracleSpec OracleComp

local notation "PT" => Ty pqAtomicSig

/-- Handshake challenger interface on `PrimBaseSpec + C.spec`. -/
@[reducible] def pqChalIface (C : ChallengerOracle) : Iface pqAtomicSig (PrimBaseSpec + C.spec) where
  fwdU n := query (spec := PrimBaseSpec + C.spec) (.inl (.inl n))
  uCost := 1
  Tag := PTag ⊕ C.Tag
  dom | .inl t => t.dom (ℓ := 0) (Pt := Empty) | .inr t => C.dom t
  cod | .inl t => t.cod (ℓ := 0) (Pt := Empty) | .inr t => C.cod t
  enc | .inl t, x => .inl (.inr (t.enc (ℓ := 0) (Pt := Empty) x)) | .inr t, x => .inr (C.enc t x)
  dec | .inl t, x, r => t.dec (ℓ := 0) (Pt := Empty) x r | .inr t, x, r => C.dec t x r
  qCost | .inl t => t.qCost | .inr t => C.qCost t
  smp := pqAtomicSamplers

/-- EUF-CMA signing challenger oracle on messages of byte width `m`. -/
def eufCmaSignOracle : ChallengerOracle where
  ι := SigQuery
  spec := sigOracleSpec
  Tag := ℕ+
  dom := fun m => PB m
  cod := fun _ => PB 64
  enc := fun _ msg => .sign msg
  dec := fun _ _ r => r
  qCost := fun m => 65 + m.val

/-- DDH challenger oracle on triples of 32-byte points. -/
def gapDhDdhOracle : ChallengerOracle where
  ι := DdhQuery
  spec := gapDhOracleSpec
  Tag := Unit
  dom := fun _ => .prod (PB 32) (.prod (PB 32) (PB 32))
  cod := fun _ => .bool
  enc := fun _ x => x
  dec := fun _ _ r => r
  qCost := fun _ => 97

abbrev pqxdhEufCmaIface := pqChalIface eufCmaSignOracle
abbrev pqGapDhIface := pqChalIface gapDhDdhOracle
abbrev pqAuthEufCmaIface := pqAuthChalIface eufCmaSignOracle
abbrev pqAuthGapDhIface := pqAuthChalIface gapDhDdhOracle

end SignalPqxdh.Costed

/-! ## Costed reduction bundles and δ-security statements -/

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.ReductionDsl (Ty CostedReduction TwoStageCostedReduction Mid)
open SignalPqxdh.Costed

def chalIfaceChalQueryWeight {PrimTag ChalTag : Type} : PrimTag ⊕ ChalTag → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- `ReductionDsl` reduction family for standalone two-key `KeyInd`. -/
structure KeyInd2KeyCostedReductionFamily (S : Setup) where
  sig  : QueryBudget → CostedReduction pqAtomicOps pqxdhEufCmaIface (keyIndSpec S) (pqKeyIndCodec S)
           (PB 32) .unit .bool (.prod (PB 1569) (PB 64))
  shcr : QueryBudget → TwoStageCostedReduction pqAtomicOps pqPrimIface (keyIndSpec S) (pqKeyIndCodec S)
           (.prod (PB 1568) (PB 3168)) .unit .bool (PB 1568)
           (.prod (PB 32) (PB 1568)) (PB 1568)
  gdh  : QueryBudget → CostedReduction pqAtomicOps pqGapDhIface (keyIndSpec S) (pqKeyIndCodec S)
           (.prod (PB 32) (PB 32)) .unit .bool (PB 32)

def KeyInd2KeyCostedReductionFamily.eval {S : Setup} (R : KeyInd2KeyCostedReductionFamily S) :
    KeyInd2KeyReductionFamily S where
  sig b A :=
    { run := fun pk => (R.sig b).eval (fun _ => A.1.run) pk
      q_sig := 2 * S.N_spk_tot
      q_prim := primQueryBudget S b }
  shcr b A :=
    { State := Mid (keyIndSpec S) Bool (R.shcr b).π.denote (R.shcr b).σ.denote (PB 1568).denote
      choosePk := fun pk sk =>
        (R.shcr b).eval1 (fun _ => A.1.run) (pk, sk) b.q_total false
      findCollision := fun st ss ct =>
        (R.shcr b).eval2 st (ss, ct) b.q_total false
      q_prim := primQueryBudget S b }
  gdh b A :=
    { run := fun U V => (R.gdh b).eval (fun _ => A.1.run) (U, V)
      q_ddh := gdhQueryBudget S b
      q_prim := primQueryBudget S b }

structure KeyInd2KeyCostedReductionBounds (S : Setup) (R : KeyInd2KeyCostedReductionFamily S) : Prop where
  ops_sizeHonest  : PqOpsSizeHonest pqAtomicOps
  samp_sizeHonest : PqSampSizeHonest pqAtomicSamplers
  sig_cost        : ∀ (b : QueryBudget), (R.sig b).totalCost b.q_total ≤ stepCostBudget S b
  shcr_cost       : ∀ (b : QueryBudget), (R.shcr b).totalCost b.q_total ≤ stepCostBudget S b
  gdh_cost        : ∀ (b : QueryBudget), (R.gdh b).totalCost b.q_total ≤ stepCostBudget S b
  sig_q_prim      : ∀ (b : QueryBudget),
    (R.sig b).totalQueries chalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b
  shcr_q_prim     : ∀ (b : QueryBudget),
    (R.shcr b).totalQueries primIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b
  gdh_q_ddh       : ∀ (b : QueryBudget),
    (R.gdh b).totalQueries chalIfaceChalQueryWeight samplerZeroQueryWeight b.q_total ≤
      4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot
  gdh_q_prim      : ∀ (b : QueryBudget),
    (R.gdh b).totalQueries chalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b
  sig_blocks      : ∀ (b : QueryBudget) (ℓ : Nat), GRedBlockBounded S b ℓ (R.sig b)
  shcr_blocks     : ∀ (b : QueryBudget) (ℓ : Nat), GRed2BlockBounded S b ℓ (R.shcr b)
  gdh_blocks      : ∀ (b : QueryBudget) (ℓ : Nat), GRedBlockBounded S b ℓ (R.gdh b)

/-- `ReductionDsl` reduction family for two-key authentication and first-message privacy. -/
structure AuthCostedReductionFamily (S : Setup) where
  mk' ::
  sig  : QueryBudget → CostedReduction pqAtomicOps pqAuthEufCmaIface (authSpec S) (authCodec S)
           (PB 32) .unit .bool (.prod (PB 1569) (PB 64))
  shcr : QueryBudget → TwoStageCostedReduction pqAtomicOps pqAuthPrimIface (authSpec S) (authCodec S)
           (.prod (PB 1568) (PB 3168)) .unit .bool (PB 1568)
           (.prod (PB 32) (PB 1568)) (PB 1568)
  gdh  : QueryBudget → CostedReduction pqAtomicOps pqAuthGapDhIface (authSpec S) (authCodec S)
           (.prod (PB 32) (PB 32)) .unit .bool (PB 32)
  ck   : QueryBudget → CostedReduction pqAtomicOps pqAuthPrimIface (authSpec S) (authCodec S)
           (.prod (PB 32) (PB 32)) .unit .bool .bool
  mk   : QueryBudget → CostedReduction pqAtomicOps pqPrfMkIface (authSpec S) (authCodec S)
           .unit .unit .bool .bool
  cpa  : QueryBudget → TwoStageCostedReduction pqAtomicOps pqAuthPrimIface (authSpec S) (authCodec S)
           .unit .unit .bool (.prod (PB 158) (.prod (PB 32) (PB 32)))
           (.opt (PB 32)) .bool
  int  : QueryBudget → CostedReduction pqAtomicOps pqPrfHmacIface (authSpec S) (authCodec S)
           .unit .unit .bool .bool

def AuthCostedReductionFamily.eval {S : Setup} (R : AuthCostedReductionFamily S) : AuthReductionFamily S where
  sig b A :=
    { run := fun pk => (R.sig b).eval (fun _ => A.1.run) pk
      q_sig := 2 * S.N_spk_tot
      q_prim := primQueryBudget S b }
  shcr b A :=
    { State := Mid (authSpec S) Bool (R.shcr b).π.denote (R.shcr b).σ.denote (PB 1568).denote
      choosePk := fun pk sk =>
        (R.shcr b).eval1 (fun _ => A.1.run) (pk, sk) b.q_total false
      findCollision := fun st ss ct =>
        (R.shcr b).eval2 st (ss, ct) b.q_total false
      q_prim := primQueryBudget S b }
  gdh b A :=
    { run := fun U V => (R.gdh b).eval (fun _ => A.1.run) (U, V)
      q_ddh := 5 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot
      q_prim := primQueryBudget S b }
  ck b A :=
    { dist := fun mkSeedChal ck1_1Chal =>
        (R.ck b).eval (fun _ => A.1.run) (mkSeedChal, ck1_1Chal)
      q_prf := 1
      q_prim := primQueryBudget S b }
  mk b A :=
    { run := (R.mk b).eval (fun _ => A.1.run) ()
      q_prf := S.N_recv_tot + 1
      q_prim := primQueryBudget S b }
  cpa b A :=
    { State := Mid (authSpec S) Bool (R.cpa b).π.denote (R.cpa b).σ.denote
        (Ty.prod (PB 158) (Ty.prod (PB 32) (PB 32))).denote
      choose := do
        let r ← (R.cpa b).eval1 (fun _ => A.1.run) () b.q_total false
        pure (r.1.1, r.1.2.1, r.1.2.2, r.2)
      dist := fun st c? =>
        (R.cpa b).eval2 st c? b.q_total false
      q_prim := primQueryBudget S b }
  int b A :=
    { run := (R.int b).eval (fun _ => A.1.run) ()
      q_prf := S.N_recv_tot + 1
      q_prim := primQueryBudget S b }

structure AuthCostedReductionBounds (S : Setup) (R : AuthCostedReductionFamily S) : Prop where
  ops_sizeHonest  : PqOpsSizeHonest pqAtomicOps
  samp_sizeHonest : PqSampSizeHonest pqAtomicSamplers
  sig_cost        : ∀ (b : QueryBudget), (R.sig b).totalCost b.q_total ≤ stepCostBudget S b
  shcr_cost       : ∀ (b : QueryBudget), (R.shcr b).totalCost b.q_total ≤ stepCostBudget S b
  gdh_cost        : ∀ (b : QueryBudget), (R.gdh b).totalCost b.q_total ≤ stepCostBudget S b
  ck_cost         : ∀ (b : QueryBudget), (R.ck b).totalCost b.q_total ≤ stepCostBudget S b
  mk_cost         : ∀ (b : QueryBudget), (R.mk b).totalCost b.q_total ≤ stepCostBudget S b
  cpa_cost        : ∀ (b : QueryBudget), (R.cpa b).totalCost b.q_total ≤ stepCostBudget S b
  int_cost        : ∀ (b : QueryBudget), (R.int b).totalCost b.q_total ≤ stepCostBudget S b
  sig_q_prim      : ∀ (b : QueryBudget),
    (R.sig b).totalQueries authChalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b
  shcr_q_prim     : ∀ (b : QueryBudget),
    (R.shcr b).totalQueries authPrimIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b
  gdh_q_ddh       : ∀ (b : QueryBudget),
    (R.gdh b).totalQueries chalIfaceChalQueryWeight samplerZeroQueryWeight b.q_total ≤
      5 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot
  gdh_q_prim      : ∀ (b : QueryBudget),
    (R.gdh b).totalQueries authChalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b
  ck_q_prim       : ∀ (b : QueryBudget),
    (R.ck b).totalQueries authPrimIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b
  mk_q_prim       : ∀ (b : QueryBudget),
    (R.mk b).totalQueries authChalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b
  cpa_q_prim      : ∀ (b : QueryBudget),
    (R.cpa b).totalQueries authPrimIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b
  int_q_prim      : ∀ (b : QueryBudget),
    (R.int b).totalQueries authChalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b
  sig_blocks      : ∀ (b : QueryBudget) (ℓ : Nat), GRedBlockBounded S b ℓ (R.sig b)
  shcr_blocks     : ∀ (b : QueryBudget) (ℓ : Nat), GRed2BlockBounded S b ℓ (R.shcr b)
  gdh_blocks      : ∀ (b : QueryBudget) (ℓ : Nat), GRedBlockBounded S b ℓ (R.gdh b)
  ck_blocks       : ∀ (b : QueryBudget) (ℓ : Nat), GRedBlockBounded S b ℓ (R.ck b)
  mk_blocks       : ∀ (b : QueryBudget) (ℓ : Nat), GRedBlockBounded S b ℓ (R.mk b)
  cpa_blocks      : ∀ (b : QueryBudget) (ℓ : Nat), GRed2BlockBounded S b ℓ (R.cpa b)
  int_blocks      : ∀ (b : QueryBudget) (ℓ : Nat), GRedBlockBounded S b ℓ (R.int b)

/-- Standalone two-key `KeyInd` advantage bound under a δ-correct KEM for reduction family `R`. -/
def Pqxdh2KeyKeyIndReductionBoundδ (S : Setup) (R : KeyInd2KeyReductionFamily S) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (δ : ℝ), KemDeltaCorrectReal P δ →
    ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
      KeyIndAdvantage S P A.1 ≤
        pqxdhKeyIndAdvantageBoundδReal S δ
          (SigEufCma P (R.sig b A))
          (KemShCrReal P (R.shcr b A))
          (GapDH P P.isValidDhTriple P.pow8 (R.gdh b A))

/-- Authentication advantage bound under a δ-correct KEM for reduction family `R`. -/
def PqxdhAuthReductionBoundδ (S : Setup) (R : AuthReductionFamily S) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (δ : ℝ), KemDeltaCorrectReal P δ →
    ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      AuthAdvantageReal S P A.1 ≤
        pqxdhAuthAdvantageBoundδReal S b.q_roRoot δ
          (SigEufCma P (R.sig b A))
          (KemShCrReal P (R.shcr b A))
          (GapDH P P.isValidDhTriple P.pow8 (R.gdh b A))
          (PrfChainKeyReal P (R.ck b A))
          (PrfMsgKeysReal P (R.mk b A))
          (AeadIndCpaReal P (R.cpa b A))
          (PrfHmacReal P (R.int b A))

def Pqxdh2KeyKeyIndSecureδ (S : Setup) : Prop :=
  ∃ R : KeyInd2KeyCostedReductionFamily S,
    KeyInd2KeyCostedReductionBounds S R ∧
    KeyInd2KeyReductionQueryBounds S R.eval ∧
    Pqxdh2KeyKeyIndReductionBoundδ S R.eval

def PqxdhAuthSecureδ (S : Setup) : Prop :=
  ∃ R : AuthCostedReductionFamily S,
    AuthCostedReductionBounds S R ∧
    AuthReductionQueryBounds S R.eval ∧
    PqxdhAuthReductionBoundδ S R.eval

def Pqxdh2KeySecureδ (S : Setup) : Prop :=
  Pqxdh2KeyKeyIndSecureδ S ∧
  PqxdhAuthSecureδ S

/-- Standalone two-key δ-headline statement: correctness and two-key security across all setups. -/
def Pqxdh2KeyCorrectAndSecureδ : Prop :=
  (∀ (P : Primitives), WellFormedPrimitivesδ P → PqxdhCorrect P) ∧
  (∀ (S : Setup), Pqxdh2KeySecureδ S)

end SignalPqxdh.Security

namespace SignalPqxdh

export Security (
  chalIfaceChalQueryWeight authPrimIfacePrimQueryWeight authChalIfacePrimQueryWeight
  KeyInd2KeyCostedReductionFamily KeyInd2KeyCostedReductionBounds
  Pqxdh2KeyKeyIndReductionBoundδ Pqxdh2KeyKeyIndSecureδ
  AuthCostedReductionFamily AuthCostedReductionBounds
  pqxdhAuthAdvantageBoundδ PqxdhAuthReductionBoundδ PqxdhAuthSecureδ
  Pqxdh2KeySecureδ Pqxdh2KeyCorrectAndSecureδ
)

end SignalPqxdh

namespace SignalPqxdh.Costed

export SignalPqxdh.Security (
  chalIfaceChalQueryWeight authPrimIfacePrimQueryWeight authChalIfacePrimQueryWeight
  KeyInd2KeyCostedReductionFamily KeyInd2KeyCostedReductionBounds
  AuthCostedReductionFamily AuthCostedReductionBounds
)

end SignalPqxdh.Costed

namespace SignalPqxdh.Security.Costed

export SignalPqxdh.Security (
  chalIfaceChalQueryWeight authPrimIfacePrimQueryWeight authChalIfacePrimQueryWeight
  KeyInd2KeyCostedReductionFamily KeyInd2KeyCostedReductionBounds
  AuthCostedReductionFamily AuthCostedReductionBounds
)

end SignalPqxdh.Security.Costed
