/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.Pqxdh.StatementPqReds
public import Computational.Proofs.LibsignalCli.MainHaltedKeyInd -- proof-setup: allow-public-import
public import Computational.Proofs.LibsignalCli.MainHaltedPrefixCore -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.CompositionHaltedWitness -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.HaltedDrSessionSim -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.HaltedDrSessionSimSteps -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.HaltedPrefixSubprogs -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.KindRedHalted -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.KindRedHaltedInst -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.M3PqxdhSize -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.PrefixRedHalted -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.PrefixRedHaltedInst -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.SizeBudgetBridge
import Computational.Proofs.E2E.Dsl.FreshnessSim
import Computational.Proofs.E2E.Dsl.PrefixRedHaltedEval
import Computational.Proofs.E2E.Dsl.StartAndExtSm
import Computational.Proofs.E2E.Dsl.PqxdhSim
import Computational.Proofs.E2E.CompositionHaltedKindReal
import Computational.Proofs.E2E.Dsl.CompositionHaltedPrefixEval
import Computational.Proofs.E2E.Dsl.CompositionHaltedRedsCost
import Computational.Proofs.E2E.Dsl.CompositionHaltedRedsKindSim
import Computational.Proofs.E2E.Dsl.CompositionHaltedRedsPrefixSim

/-!
# Concrete Halted Multi-Session Composition Reductions

Assembles the atomic `ReductionDsl` handshake reduction (`kindRedHalted`) and two-stage prefix
reduction family (`prefixRedHalted`) into the `CompositionCostedReductionFamily` witness
`redsHalted`, together with its cost, query, and simulation-equivalence theorems.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Computational.Proofs.E2E.Dsl.CompositionHaltedReds

export Computational.Proofs.E2E.Dsl.CompositionHaltedWitness (kemFailSessionTracker)

open scoped BigOperators
open OracleComp OracleSpec
open _root_.ReductionDsl (Sig Ops Iface Ty Env Expr Comp GameCodec Mid TwoStageCostedReduction
  atomicSig atomicE2EOps bits e2eKeyIndTargetIface e2eSessionTargetIface prefixCtxT smQT smQenc)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (MakesAtMostQueries)
open CryptoGames.LibsignalSession (Crypto GhostState PublicKey maxForwardJumps)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open Computational.Proofs.E2E.Dsl.M3Interfaces (bhPromoteSlotK)
open CryptoVerification.E2E (BHE2EDrvState BHModelInst Bytes CompositionCostedReductionFamily
  CompositionCostedReductionFamilyBounded bhE2ECostBudget bhTargetGameSpec
  configRefuseEarlyBobCorr e2eTargetGameCodec isSmTargetQuery keyIndReductionBudget
  paramsIdsWithSpqr sessionSchemeFixedSpk stageOneAsProbComp)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge (KemFailSessionTrack)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono)
open Computational.Proofs.LibsignalCli.MainHaltedKeyInd (bhKindRedWithTracked)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore (bhE2EStepLocalSmSessionTracked
  bhPrefixRedWithSessionTracked gameRSessionTracked oracleImplRSessionTracked)
open Computational.Proofs.E2E.Dsl.KindRedHaltedEval (packAtomicSmRespEnc)
open Computational.Proofs.E2E.Dsl.CompositionHaltedWitness (HaltedSimInv
  HaltedTargetAdvPerInstanceBounded bhE2ECostBudget_eq_factors e2eFreshScanInnerFactor
  e2ePerStepWeightedFactor params_bits_le_budget)

private theorem maxForwardJumps_eq : maxForwardJumps = 25000 := rfl

private theorem bits_qTotal_succ_le_budget
    (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) (qStart qDR qInst qep ℓ : ℕ) :
    bits (b.q_total + 1) ≤ bits (bhE2ECostBudget S b qStart qDR qInst qep ℓ) := by
  apply bits_mono
  rw [bhE2ECostBudget_eq_factors]
  set W := e2ePerStepWeightedFactor S b qStart qInst qep ℓ
  have h1 : b.q_total + 1 ≤ 1 * W := by
    dsimp only [W, e2ePerStepWeightedFactor]
    omega
  have h2 : 1 * W ≤ 2 ^ 10 * (b.q_total + qStart + qDR + 1) * W :=
    Nat.mul_le_mul_right W (by omega)
  omega

private theorem prefix_endpointCost_le
    (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) (qStart qInst qep ℓ : ℕ) :
    40 + 150 + 80 + (HaltedPrefixSubprogs.finishPrefixHaltedClampedCost S b qStart) + 60 ≤
      2 ^ 10 * e2ePerStepWeightedFactor S b qStart qInst qep ℓ +
        2 ^ 13 * min qStart (min b.q_total S.N_send_tot) * e2eFreshScanInnerFactor S b := by
  dsimp only [HaltedPrefixSubprogs.finishPrefixHaltedClampedCost,
    FreshnessSim.finishPrefixClampedCost]
  set F := e2eFreshScanInnerFactor S b
  set W := e2ePerStepWeightedFactor S b qStart qInst qep ℓ
  set nInst := min qStart (min b.q_total S.N_send_tot)
  have hj := maxForwardJumps_eq
  have hInitStep :
      FreshnessSim.initStillFreshStepCost
        (min b.q_total S.N_id) (min b.q_total S.N_spk_tot) (min b.q_total S.N_recv_tot) ≤
        2 ^ 13 * F := by
    dsimp only [FreshnessSim.initStillFreshStepCost, F, e2eFreshScanInnerFactor]
    omega
  have hSendMul :
      nInst * FreshnessSim.initStillFreshStepCost
          (min b.q_total S.N_id) (min b.q_total S.N_spk_tot) (min b.q_total S.N_recv_tot) ≤
        2 ^ 13 * nInst * F := by
    have hm := Nat.mul_le_mul_left nInst hInitStep
    have hring : nInst * (2 ^ 13 * F) = 2 ^ 13 * nInst * F := by ring
    omega
  have hTail :
      24 * min b.q_total S.N_send_tot + 2 * FreshnessSim.drvWonCost nInst + 510 ≤
        2 ^ 10 * W := by
    dsimp only [FreshnessSim.drvWonCost, nInst, W, e2ePerStepWeightedFactor]
    omega
  omega

private theorem prefix_tightStepCost_le
    (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) (qStart qInst qep ℓ : ℕ) :
    let nInst := min qStart (min b.q_total S.N_send_tot)
    max
      (max
        (HaltedPrefixSubprogs.kiStepHaltedClampedCost S qStart b)
        (HaltedPrefixSubprogs.localStartHaltedClampedCost S b qStart +
          (HaltedPrefixSubprogs.promoteSlotKHaltedCost nInst + nInst + 30)))
      (max
        (HaltedPrefixSubprogs.extSmStepHaltedCost ℓ b nInst)
        (HaltedDrSessionSim.haltedStepLocalSmCost ℓ b qStart qInst qep)) +
      2 * nInst + 184 ≤
      2 ^ 10 * e2ePerStepWeightedFactor S b qStart qInst qep ℓ := by
  dsimp only
  have hdiv : ℓ / 32 ≤ ℓ := Nat.div_le_self ℓ 32
  have hj := maxForwardJumps_eq
  have hsm := HaltedDrSessionSim.haltedStepLocalSmCost_le ℓ b qStart qInst qep
  unfold HaltedPrefixSubprogs.kiStepHaltedClampedCost
    HaltedPrefixSubprogs.localStartHaltedClampedCost
    HaltedPrefixSubprogs.promoteSlotKHaltedCost
    HaltedPrefixSubprogs.extSmStepHaltedCost
    PqxdhSim.pqxdh1KeyRealStepClampedCost
    PqxdhSim.pqxdhTestStepCost
    PqxdhSim.pqxdhRevealSpkStepCost
    StartAndExtSm.promoteSlotKCost
    StartAndExtSm.extSmStepCost
    e2ePerStepWeightedFactor
  set nId := min b.q_total S.N_id
  set nSpk := min b.q_total S.N_spk_tot
  set nOpk := min b.q_total S.N_opk_tot
  set nSend := min b.q_total S.N_send_tot
  set nRecv := min b.q_total S.N_recv_tot
  set nInst := min qStart nSend
  set lq := Nat.log 2 qep
  set M := 920 * b.q_total + 300 * nOpk + 700 * nInst + 800 * qInst + 4 * lq +
    9000 * (nId + nSpk + nSend + nRecv) + 10 * ℓ + 19000000
  have hm :
      max
        (max
          (168 * b.q_total + 24 * nInst +
            (600 * nId + 3500 * nSpk + 300 * nOpk + 7100 * nSend + 7200 * nRecv +
              300 * b.q_total + 12200) + 1600)
          (600 * nInst + 920 * b.q_total + 6600 * nSpk + (1750 * nSend + 1750 * nRecv + 600) +
            (200 * nSpk + 300) + 100000 + (68 * nInst + 700 + 20 + nInst + 30)))
        (max
          (220 * nInst + 300 * b.q_total + 310 * b.q_total + 2 * (ℓ / 32) + 37100 + 20)
          (HaltedDrSessionSim.haltedStepLocalSmCost ℓ b qStart qInst qep)) ≤ M :=
    max_le (max_le (by dsimp only [M]; omega) (by dsimp only [M]; omega))
      (max_le (by dsimp only [M]; omega) (by dsimp only [M]; omega))
  dsimp only [M] at hm
  omega

private theorem prefix_sizeBound_le
    (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) (qStart qDR qInst qep ℓ : ℕ) :
    let nInst := min qStart (min b.q_total S.N_send_tot)
    40 + 50 + 80 +
      HaltedPrefixSubprogs.finishPrefixHaltedClampedSize S b qStart +
      2 * HaltedPrefixSubprogs.kiStepHaltedClampedSize S qStart b +
      2 * HaltedPrefixSubprogs.localStartHaltedClampedSize S b qStart +
      (HaltedPrefixSubprogs.promoteSlotKHaltedSize nInst + bits nInst + 30) +
      HaltedPrefixSubprogs.extSmStepHaltedSize b nInst +
      2 * HaltedDrSessionSim.haltedStepLocalSmSize b qStart qInst qep +
      3 * bits qStart + 200 ≤
      1100000 + 1300 * bits (bhE2ECostBudget S b qStart qDR qInst qep ℓ) := by
  dsimp only
  have hsm := HaltedDrSessionSim.haltedStepLocalSmSize_le S ℓ b qStart qDR qInst qep
  obtain ⟨hbTot, hbSt, _, _, _, hbId, hbSpk, hbOpk, hbSend, hbRecv, hbInst, -⟩ :=
    params_bits_le_budget S b qStart qDR qInst qep ℓ
  dsimp only [HaltedPrefixSubprogs.finishPrefixHaltedClampedSize,
    FreshnessSim.finishPrefixClampedSize,
    HaltedPrefixSubprogs.kiStepHaltedClampedSize,
    HaltedPrefixSubprogs.localStartHaltedClampedSize,
    HaltedPrefixSubprogs.promoteSlotKHaltedSize,
    HaltedPrefixSubprogs.extSmStepHaltedSize]
  generalize bits (bhE2ECostBudget S b qStart qDR qInst qep ℓ) = bB at *
  omega

@[expose] def haltedDrStepOps {Pt : Type} (ℓ : ℕ) (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    HaltedDrSessionSim.HaltedDrStepOps ℓ Pt P C K decT encT :=
  HaltedDrSessionSim.mkHaltedDrStepOps
    HaltedDrSessionSimSteps.haltedDrTrStepC
    HaltedDrSessionSimSteps.haltedDrTrStepC_queries
    HaltedDrSessionSimSteps.haltedDrTrStepC_cost
    HaltedDrSessionSimSteps.haltedDrTrStepC_size
    HaltedDrSessionSimSteps.haltedDrTrStepC_eval
    HaltedDrSessionSimSteps.haltedDrChStepC
    HaltedDrSessionSimSteps.haltedDrChStepC_queries
    HaltedDrSessionSimSteps.haltedDrChStepC_cost
    HaltedDrSessionSimSteps.haltedDrChStepC_size
    HaltedDrSessionSimSteps.haltedDrChStepC_eval

private def haltedLocalSmKindStep {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    KindRedHaltedInst.HaltedLocalSmKindStepInst S ℓ Pt P C K decT encT
      (PrefixRedHaltedInst.KemBridgeTrackInvLocal C.F K) where
  stepC b qSt qI qep {_} σHE idxE sqE :=
    HaltedDrSessionSim.haltedStepLocalSmGenC
      (haltedDrStepOps (Pt := Pt) ℓ P C K decT encT)
      (e2eKeyIndTargetIface S ℓ Pt) rfl b qSt qI qep σHE idxE sqE
  stepCost := HaltedDrSessionSim.haltedStepLocalSmCost ℓ
  stepSize := HaltedDrSessionSim.haltedStepLocalSmSize
  stepC_cost b qSt qI qep {_} σHE idxE sqE :=
    HaltedDrSessionSim.haltedStepLocalSmGenC_cost
      (haltedDrStepOps (Pt := Pt) ℓ P C K decT encT)
      (e2eKeyIndTargetIface S ℓ Pt) rfl b qSt qI qep σHE idxE sqE
  stepC_size b qSt qI qep {_} σHE idxE sqE :=
    HaltedDrSessionSim.haltedStepLocalSmGenC_size
      (haltedDrStepOps (Pt := Pt) ℓ P C K decT encT)
      (e2eKeyIndTargetIface S ℓ Pt) rfl b qSt qI qep σHE idxE sqE
  stepC_queries b qSt qI qep {_} σHE idxE sqE w :=
    HaltedDrSessionSim.haltedStepLocalSmGenC_queries
      (haltedDrStepOps (Pt := Pt) ℓ P C K decT encT)
      (e2eKeyIndTargetIface S ℓ Pt) rfl b qSt qI qep σHE idxE sqE w
  stepCost_bound b qSt qI qep :=
    HaltedDrSessionSim.haltedStepLocalSmCost_le ℓ b qSt qI qep
  stepSize_bound b qSt qDR qI qep :=
    HaltedDrSessionSim.haltedStepLocalSmSize_le S ℓ b qSt qDR qI qep
  stepC_eval b qSt qI qep {_} hInstLen hMeta hCorr hRev hPrin hSess hEp hTrLen hTrInv
      {_} σHE idxE sqE ρ i sq hσH hidx hsq :=
    HaltedDrSessionSim.haltedStepLocalSmGenC_eval
      (haltedDrStepOps (Pt := Pt) ℓ P C K decT encT)
      (e2eKeyIndTargetIface S ℓ Pt) rfl b qSt qI qep σHE idxE sqE ρ _ i sq
      hσH hidx hsq hInstLen hMeta hCorr hRev hPrin hSess hEp hTrLen
      (fun st hst => ⟨(hTrInv st hst).1, (hTrInv st hst).2, (hTrInv st hst).3, (hTrInv st hst).4⟩)

private def kindSubprogramsHalted {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (b : SignalPqxdh.QueryBudget) :
    KindRedHalted.HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT
      (KemFailSessionTrack C.F Bytes) :=
  KindRedHaltedInst.mkKindSubprogramsHaltedClamped
    (haltedLocalSmKindStep (Pt := Pt) S ℓ P C K decT encT) b

@[expose] def prefixSubprogramsHalted {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (qStart : ℕ) :
    PrefixRedHalted.HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT
      (KemFailSessionTrack C.F Bytes) where
  drvTy := HaltedPrefixSubprogs.drvTy S ℓ Pt
  sessHTy := HaltedPrefixSubprogs.sessHTy ℓ Pt
  drvEnc := HaltedPrefixSubprogs.drvEnc
  sessHEnc := HaltedPrefixSubprogs.sessHEnc
  emptyDrvStateE := fun {_} bE => HaltedPrefixSubprogs.emptyDrvStateHaltedE bE
  emptyDrvStateCost := 40
  emptyDrvStateSize := 40
  emptyDrvStateE_cost := fun {_} bE => HaltedPrefixSubprogs.emptyDrvStateHaltedE_cost bE
  emptyDrvStateE_size := fun {_} bE => HaltedPrefixSubprogs.emptyDrvStateHaltedE_size bE
  emptyDrvStateE_eval := fun {_} bE ρ => HaltedPrefixSubprogs.emptyDrvStateHaltedE_eval bE ρ
  drvSetBitE := fun {_} σE bE => HaltedPrefixSubprogs.drvSetBitHaltedE σE bE
  drvSetBitCost := 80
  drvSetBitSize := 80
  drvSetBitE_cost := fun {_} σE bE => HaltedPrefixSubprogs.drvSetBitHaltedE_cost σE bE
  drvSetBitE_size := fun {_} σE bE => HaltedPrefixSubprogs.drvSetBitHaltedE_size σE bE
  drvSetBitE_eval := fun {_} σE bE ρ σ hσ =>
    HaltedPrefixSubprogs.drvSetBitHaltedE_eval σE bE ρ σ hσ
  defaultPrefixCtxE := fun {_} => HaltedPrefixSubprogs.defaultPrefixCtxHaltedE
  defaultPrefixCtxCost := 150
  defaultPrefixCtxSize := 50
  defaultPrefixCtxE_cost := fun {_} => HaltedPrefixSubprogs.defaultPrefixCtxHaltedE_cost
  defaultPrefixCtxE_size := fun {_} => HaltedPrefixSubprogs.defaultPrefixCtxHaltedE_size
  defaultPrefixCtxE_eval := fun {_} ρ => HaltedPrefixSubprogs.defaultPrefixCtxHaltedE_eval ρ
  kiStepC := fun b {_} σE kqE => HaltedPrefixSubprogs.kiStepHaltedClampedC qStart b σE kqE
  kiStepCost := HaltedPrefixSubprogs.kiStepHaltedClampedCost S qStart
  kiStepSize := HaltedPrefixSubprogs.kiStepHaltedClampedSize S qStart
  kiStepC_cost := fun b {_} σE kqE =>
    HaltedPrefixSubprogs.kiStepHaltedClampedC_cost qStart b σE kqE
  kiStepC_size := fun b {_} σE kqE =>
    HaltedPrefixSubprogs.kiStepHaltedClampedC_size qStart b σE kqE
  kiStepC_queries := fun b {_} σE kqE w =>
    HaltedPrefixSubprogs.kiStepHaltedClampedC_queries qStart b σE kqE w
  localStartHaltedC := fun b qSt bm {_} σHE sidE =>
    HaltedPrefixSubprogs.localStartHaltedClampedC b qSt bm σHE sidE
  localStartHaltedCost := HaltedPrefixSubprogs.localStartHaltedClampedCost S
  localStartHaltedSize := HaltedPrefixSubprogs.localStartHaltedClampedSize S
  localStartHaltedC_cost := fun b qSt bm {_} σHE sidE =>
    HaltedPrefixSubprogs.localStartHaltedClampedC_cost b qSt bm σHE sidE
  localStartHaltedC_size := fun b qSt bm {_} σHE sidE =>
    HaltedPrefixSubprogs.localStartHaltedClampedC_size b qSt bm σHE sidE
  localStartHaltedC_queries := fun b qSt bm {_} σHE sidE w =>
    HaltedPrefixSubprogs.localStartHaltedClampedC_queries b qSt bm σHE sidE w
  promoteSlotKC := fun qSt {_} kE idxOptE σE =>
    .bind (.ret (.pair kE (.pair idxOptE σE)))
      (.ite (.lt (.fst .v0) (.nat qSt))
        (HaltedPrefixSubprogs.promoteSlotKHaltedC qSt
          (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0)))
        (.ret (.inl (.pair (.fst (.snd .v0)) (.snd (.snd .v0))))))
  promoteSlotKCost := fun qSt =>
    HaltedPrefixSubprogs.promoteSlotKHaltedCost qSt + qSt + 30
  promoteSlotKSize := fun qSt =>
    HaltedPrefixSubprogs.promoteSlotKHaltedSize qSt + bits qSt + 30
  promoteSlotKC_cost := fun qSt {Γ} kE idxOptE σE => by
    dsimp only [Comp.cost, Expr.cost, Expr.v0]
    have hbits := CryptoVerification.E2E.Costed.bits_le_self_add_one qSt
    have hp := HaltedPrefixSubprogs.promoteSlotKHaltedC_cost (S := S) (ℓ := ℓ) (Pt := Pt)
      (P := P) (C := C) (K := K) (decT := decT) (encT := encT) qSt
      (Γ := .prod .nat (.prod (.opt .nat) (HaltedPrefixSubprogs.drvTy S ℓ Pt)) :: Γ)
      (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0))
    dsimp only [Expr.cost, Expr.v0] at hp
    omega
  promoteSlotKC_size := fun qSt {Γ} kE idxOptE σE => by
    dsimp only [Comp.size, Expr.size, Expr.v0]
    have hp := HaltedPrefixSubprogs.promoteSlotKHaltedC_size (S := S) (ℓ := ℓ) (Pt := Pt)
      (P := P) (C := C) (K := K) (decT := decT) (encT := encT) qSt
      (Γ := .prod .nat (.prod (.opt .nat) (HaltedPrefixSubprogs.drvTy S ℓ Pt)) :: Γ)
      (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0))
    dsimp only [Expr.size, Expr.v0] at hp
    omega
  promoteSlotKC_queries := fun qSt {_} kE idxOptE σE w => by
    simp only [Comp.queries, HaltedPrefixSubprogs.promoteSlotKHaltedC_queries,
      Nat.add_zero, Nat.max_self]
  extSmStepC := fun b qSt {_} kE σE sqE =>
    HaltedPrefixSubprogs.extSmStepHaltedC b (min qSt (min b.q_total S.N_send_tot)) kE σE sqE
  extSmStepCost := fun b qSt =>
    HaltedPrefixSubprogs.extSmStepHaltedCost ℓ b (min qSt (min b.q_total S.N_send_tot))
  extSmStepSize := fun b qSt =>
    HaltedPrefixSubprogs.extSmStepHaltedSize b (min qSt (min b.q_total S.N_send_tot))
  extSmStepC_cost := fun b qSt {_} kE σE sqE =>
    HaltedPrefixSubprogs.extSmStepHaltedC_cost b (min qSt (min b.q_total S.N_send_tot)) kE σE sqE
  extSmStepC_size := fun b qSt {_} kE σE sqE =>
    HaltedPrefixSubprogs.extSmStepHaltedC_size b (min qSt (min b.q_total S.N_send_tot)) kE σE sqE
  extSmStepC_queries_one := fun b qSt {_} kE σE sqE =>
    HaltedPrefixSubprogs.extSmStepHaltedC_queries_one b
      (min qSt (min b.q_total S.N_send_tot)) kE σE sqE
  haltedStepLocalSmC := fun b qSt qDR qep {_} σHE idxE sqE =>
    HaltedDrSessionSim.haltedStepLocalSmGenC
      (haltedDrStepOps (Pt := Pt) ℓ P C K decT encT)
      (e2eSessionTargetIface ℓ Pt) rfl b qSt qDR qep σHE idxE sqE
  haltedStepLocalSmCost := HaltedDrSessionSim.haltedStepLocalSmCost ℓ
  haltedStepLocalSmSize := HaltedDrSessionSim.haltedStepLocalSmSize
  haltedStepLocalSmC_cost := fun b qSt qDR qep {_} σHE idxE sqE =>
    HaltedDrSessionSim.haltedStepLocalSmGenC_cost
      (haltedDrStepOps (Pt := Pt) ℓ P C K decT encT)
      (e2eSessionTargetIface ℓ Pt) rfl b qSt qDR qep σHE idxE sqE
  haltedStepLocalSmC_size := fun b qSt qDR qep {_} σHE idxE sqE =>
    HaltedDrSessionSim.haltedStepLocalSmGenC_size
      (haltedDrStepOps (Pt := Pt) ℓ P C K decT encT)
      (e2eSessionTargetIface ℓ Pt) rfl b qSt qDR qep σHE idxE sqE
  haltedStepLocalSmC_queries := fun b qSt qDR qep {_} σHE idxE sqE w =>
    HaltedDrSessionSim.haltedStepLocalSmGenC_queries
      (haltedDrStepOps (Pt := Pt) ℓ P C K decT encT)
      (e2eSessionTargetIface ℓ Pt) rfl b qSt qDR qep σHE idxE sqE w
  finishPrefixC := fun b qSt {_} σE bOutE flipE =>
    HaltedPrefixSubprogs.finishPrefixHaltedClampedC b qSt σE bOutE flipE
  finishPrefixCost := HaltedPrefixSubprogs.finishPrefixHaltedClampedCost S
  finishPrefixSize := HaltedPrefixSubprogs.finishPrefixHaltedClampedSize S
  finishPrefixC_cost := fun b qSt {_} σE bOutE flipE =>
    HaltedPrefixSubprogs.finishPrefixHaltedClampedC_cost b qSt σE bOutE flipE
  finishPrefixC_size := fun b qSt {_} σE bOutE flipE =>
    HaltedPrefixSubprogs.finishPrefixHaltedClampedC_size b qSt σE bOutE flipE
  finishPrefixC_queries := fun b qSt {_} σE bOutE flipE w =>
    HaltedPrefixSubprogs.finishPrefixHaltedClampedC_queries b qSt σE bOutE flipE w

private abbrev prefixSubprogramsHaltedB {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b0 : SignalPqxdh.QueryBudget) (qStart0 : ℕ) :
    PrefixRedHalted.HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT
      (KemFailSessionTrack C.F Bytes) :=
  let nInst := min qStart0 (min b0.q_total S.N_send_tot)
  let subs0 := prefixSubprogramsHalted (Pt := Pt) S ℓ P C K decT encT qStart0
  { subs0 with
    promoteSlotKC := fun _ {_} kE idxOptE σE => subs0.promoteSlotKC nInst kE idxOptE σE
    promoteSlotKCost := fun _ => subs0.promoteSlotKCost nInst
    promoteSlotKSize := fun _ => subs0.promoteSlotKSize nInst
    promoteSlotKC_cost := fun _ {_} kE idxOptE σE => subs0.promoteSlotKC_cost nInst kE idxOptE σE
    promoteSlotKC_size := fun _ {_} kE idxOptE σE => subs0.promoteSlotKC_size nInst kE idxOptE σE
    promoteSlotKC_queries := fun _ {_} kE idxOptE σE w =>
      subs0.promoteSlotKC_queries nInst kE idxOptE σE w }

private theorem promoteSlotKClamped_eval_noPromote {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b0 : SignalPqxdh.QueryBudget) (qStart0 : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (idxOptE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt .nat))
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (HaltedPrefixSubprogs.drvTy S ℓ Pt))
    (ρ : Env Γ) :
    ((prefixSubprogramsHaltedB (Pt := Pt) S ℓ P C K decT encT b0 qStart0).promoteSlotKC qStart0
      (.nat (min qStart0 (min b0.q_total S.N_send_tot))) idxOptE σE).eval ρ =
      pure (.inl (idxOptE.eval ρ, σE.eval ρ)) := by
  dsimp only [prefixSubprogramsHaltedB, prefixSubprogramsHalted]
  simp only [Comp.eval, Expr.eval, Expr.v0, Env.get, pure_bind,
    lt_self_iff_false, decide_false, Bool.false_eq_true, ↓reduceIte]

private theorem prefixSubprogramsHaltedB_valid {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) :
    PrefixRedHaltedInst.ValidHaltedPrefixSubprogramsInst
      (prefixSubprogramsHaltedB (Pt := Pt) S ℓ P C K decT encT b qStart)
      (kemFailSessionTracker (ℓ := ℓ) C.F K)
      (PrefixRedHaltedInst.KemBridgeTrackInvLocal C.F K) b qStart qInst qep where
  track_valid := PrefixRedHaltedInst.kemBridgeTrackInvLocal_validSimTrackInv C.F K
  endpointCost_le := prefix_endpointCost_le S b qStart qInst qep ℓ
  stepCost_le := prefix_tightStepCost_le S b qStart qInst qep ℓ
  sizeBound_le := fun qDR =>
    ⟨1100000, 1300, by omega, by omega, prefix_sizeBound_le S b qStart qDR qInst qep ℓ⟩
  kiStepC_eval := fun hP {_} hPrins hMeta hst {_} σE kqE ρ kq hσ hkq =>
    HaltedPrefixSubprogs.kiStepHaltedClampedC_eval qStart qep b hP σE kqE ρ _ kq
      hσ hkq hPrins hMeta hst
  localStartHaltedC_eval := fun bm {_} hMir hst hTracks {_} σHE sidE ρ sid hσH hsid =>
    HaltedPrefixSubprogs.localStartHaltedClampedC_eval b qStart bm σHE sidE ρ _ sid
      hσH hsid hMir hst hTracks
  promoteSlotKC_eval := fun {σH} hInstLen {Γ} kE idxOptE σE ρ k idx? hk hkE hidx hσ => by
    dsimp only [prefixSubprogramsHaltedB, prefixSubprogramsHalted] at σE hσ ⊢
    set nInst := min qStart (min b.q_total S.N_send_tot)
    have htrue : decide (k < nInst) = true := decide_eq_true hk
    simp only [Comp.eval, Expr.eval, Expr.v0, Env.get, pure_bind, hkE, hidx, htrue, ↓reduceIte]
    have hp := HaltedPrefixSubprogs.promoteSlotKHaltedC_eval (S := S) (ℓ := ℓ) (Pt := Pt)
      (P := P) (C := C) (K := K) (decT := decT) (encT := encT) nInst
      (Γ := .prod .nat (.prod (.opt .nat) (HaltedPrefixSubprogs.drvTy S ℓ Pt)) :: Γ)
      (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0))
      (.cons (k, (idx?, σE.eval ρ)) ρ) σH.1 hσ hInstLen
    dsimp only [Expr.eval, Expr.v0, Env.get] at hp
    refine hp.trans ?_
    change pure (HaltedPrefixSubprogs.promoteSlotKHaltedEnc (bhPromoteSlotK k idx? σH.1)) = _
    rcases bhPromoteSlotK k idx? σH.1 with ⟨idx', σ'⟩ | ⟨ctx, p, σ_p⟩ <;> rfl
  extSmStepC_eval := fun {_ _} hMir hMeta _hPaused {_} kE σE sqE ρ sq _hk hkE hσ hsq =>
    HaltedPrefixSubprogs.extSmStepHaltedC_eval b (min qStart (min b.q_total S.N_send_tot))
      kE σE sqE ρ _ _ sq hkE hσ hsq hMir hMeta
  haltedStepLocalSmC_eval := fun {_} hInstLen hMeta hCorr hRev hPrin hSess hEp hTrLen hTrInv
      {_} σHE idxE sqE ρ i sq hσH hidx hsq =>
    HaltedDrSessionSim.haltedStepLocalSmGenC_eval
      (haltedDrStepOps (Pt := Pt) ℓ P C K decT encT)
      (e2eSessionTargetIface ℓ Pt) rfl b qStart qInst qep σHE idxE sqE ρ _ i sq
      hσH hidx hsq hInstLen hMeta hCorr hRev hPrin hSess hEp hTrLen
      (fun st hst => ⟨(hTrInv st hst).1, (hTrInv st hst).2, (hTrInv st hst).3, (hTrInv st hst).4⟩)
  finishPrefixC_eval := fun hP {_} hInsts hTested hResp hst {_} σE bOutE flipE ρ bOut flip
      hσ hbOut hflip => by
    have hf := HaltedPrefixSubprogs.finishPrefixHaltedClampedC_eval b qStart hP σE bOutE flipE ρ _
      hσ hInsts hTested hResp hst
    rw [hbOut, hflip] at hf
    exact hf

private theorem run1_not_paused_of_handlePre_inl
    {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C0 rIn aIn aOut ch rIn2 out)
    (hInl : ∀ (s : R.σ.denote) (q : C0.Q.denote)
      (res : (Ty.sum (.prod C0.R R.σ) (.prod ch (.prod R.π R.σ))).denote),
      res ∈ support (R.handlePre.eval (.cons s (.cons q .nil))) →
      ∃ v, res = .inl v)
    (dflt : aOut.denote) (oa : OracleComp (unifSpec + G) aOut.denote) :
    ∀ (f : ℕ) (s : R.σ.denote)
      (m : Mid G aOut.denote R.π.denote R.σ.denote ch.denote),
      m ∈ support (R.run1 dflt oa f s) →
      ∃ b_out s_out, m = .done b_out s_out := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro f s m hm
    simp only [TwoStageCostedReduction.run1, construct_pure, mem_support_pure_iff] at hm
    exact ⟨a, s, hm⟩
  | query_bind q mx ih =>
    intro f s m hm
    cases q with
    | inl n =>
      simp only [TwoStageCostedReduction.run1, construct_query_bind, mem_support_bind_iff] at hm
      rcases hm with ⟨u, -, hm'⟩
      exact ih u f s m hm'
    | inr t =>
      cases f with
      | zero =>
        simp only [TwoStageCostedReduction.run1, construct_query_bind, mem_support_pure_iff] at hm
        exact ⟨dflt, s, hm⟩
      | succ f' =>
        have hstep :
            R.run1 dflt (liftM (OracleSpec.query (spec := unifSpec + G) (.inr t)) >>= mx) (f' + 1) s =
            (R.handlePre.eval (.cons s (.cons (C0.qenc t) .nil)) >>= fun res =>
              match res with
              | .inl (v, s') => R.run1 dflt (mx (C0.rdec t v)) f' s'
              | .inr (c, p, s') => pure (.paused t c p s' mx)) := by
          simp only [TwoStageCostedReduction.run1, construct_query_bind]
          refine bind_congr fun res => ?_
          rcases res with ⟨v, s'⟩ | ⟨c, p, s'⟩ <;> rfl
        rw [hstep, mem_support_bind_iff] at hm
        rcases hm with ⟨res, hres, hm'⟩
        rcases hInl s (C0.qenc t) res hres with ⟨⟨v, s'⟩, rfl⟩
        exact ih (C0.rdec t v) f' s' m hm'

private theorem prefixRedHalted_makesAtMostQueries_noPause
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    (subs : PrefixRedHalted.HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep qTot k qsK : ℕ)
    (hNoPromote : ∀ {Γ : List (Ty (atomicSig ℓ Pt))}
      (idxOptE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt .nat))
      (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy)
      (ρ : Env Γ),
      (subs.promoteSlotKC qStart (.nat k) idxOptE σE).eval ρ =
        pure (.inl (idxOptE.eval ρ, σE.eval ρ)))
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (o : (prefixCtxT (ℓ := ℓ) (Pt := Pt)).denote ×
      Mid (bhTargetGameSpec S ℓ (BitVec 512)) Bool
        (Option ℕ) (PrefixRedHalted.drvHaltedTy subs).denote
        (prefixCtxT (ℓ := ℓ) (Pt := Pt)).denote)
    (ho : o ∈ support (stageOneAsProbComp
      ((PrefixRedHalted.prefixRedHalted subs b qStart qDR qep k).eval1
        (fun _ => B_A) () qTot false)))
    (flip : Bool) :
    MakesAtMostQueries
      ((PrefixRedHalted.prefixRedHalted subs b qStart qDR qep k).eval2 o.2 flip qTot false)
      qsK := by
  set R := PrefixRedHalted.prefixRedHalted subs b qStart qDR qep k
  have hU : ∀ n, ((e2eSessionTargetIface ℓ Pt).fwdU n).IsQueryBoundP (isSmTargetQuery ℓ) 0 :=
    fun n => (isQueryBoundP_query_iff
      (spec := unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (isSmTargetQuery ℓ) (Sum.inl n) 0).2 (by simp [isSmTargetQuery])
  have hw : ∀ (g : (e2eSessionTargetIface ℓ Pt).Tag)
      (x : ((e2eSessionTargetIface ℓ Pt).dom g).denote),
      isSmTargetQuery ℓ ((e2eSessionTargetIface ℓ Pt).enc g x) → 1 ≤ (fun _ => 1) g :=
    fun _ _ _ => le_rfl
  have hq0 : (R.eval1 (fun _ => B_A) () qTot false).IsQueryBoundP (isSmTargetQuery ℓ) 0 := by
    have hst1 : R.init.queries (fun _ => 1) (fun _ => 0) +
        R.handlePre.queries (fun _ => 1) (fun _ => 0) +
        R.chDone.queries (fun _ => 1) (fun _ => 0) = 0 :=
      PrefixRedHalted.prefixRedHalted_stage1Queries subs b qStart qDR qep k
    exact (TwoStageCostedReduction.eval1_queryBound R (isSmTargetQuery ℓ)
      (fun _ => 1) (fun _ => 0) hw hU (fun _ => B_A) () qTot false).mono
      (by
        have hinit : R.init.queries (fun _ => 1) (fun _ => 0) = 0 := by omega
        have hpre : R.handlePre.queries (fun _ => 1) (fun _ => 0) = 0 := by omega
        have hch : R.chDone.queries (fun _ => 1) (fun _ => 0) = 0 := by omega
        simp [hinit, hpre, hch])
  have ho_raw := PrefixRedHaltedEval.mem_support_of_mem_support_stageOneAsProbComp _ ho hq0
  have hInl : ∀ (s : R.σ.denote) (q : (e2eTargetGameCodec S ℓ Pt).Q.denote)
      (res : (Ty.sum (.prod (e2eTargetGameCodec S ℓ Pt).R R.σ)
        (.prod (prefixCtxT (ℓ := ℓ) (Pt := Pt)) (.prod (.opt .nat) R.σ))).denote),
      res ∈ support (R.handlePre.eval (.cons s (.cons q .nil))) →
      ∃ v, res = .inl v := by
    intro s q res hres
    rcases q with (kq | sid) | ⟨i, sq⟩
    · simp only [R, PrefixRedHalted.prefixRedHalted, PrefixRedHalted.prefixHandlePreHalted,
        Comp.eval, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, mem_support_bind_iff,
        mem_support_pure_iff] at hres
      rcases hres with ⟨v, -, rfl⟩
      exact ⟨_, rfl⟩
    · simp only [R, PrefixRedHalted.prefixRedHalted, PrefixRedHalted.prefixHandlePreHalted,
        Comp.eval, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, mem_support_bind_iff] at hres
      rcases hres with ⟨x, -, x1, hx1, hres⟩
      rw [hNoPromote, mem_support_pure_iff] at hx1
      subst hx1
      simp only [mem_support_pure_iff] at hres
      exact ⟨_, hres⟩
    · simp only [R, PrefixRedHalted.prefixRedHalted, PrefixRedHalted.prefixHandlePreHalted,
        Comp.eval, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, mem_support_bind_iff,
        mem_support_pure_iff] at hres
      rcases hres with ⟨v, -, rfl⟩
      exact ⟨_, rfl⟩
  dsimp only [TwoStageCostedReduction.eval1] at ho_raw
  rw [mem_support_bind_iff] at ho_raw
  rcases ho_raw with ⟨⟨a0, s0⟩, -, ho_raw⟩
  rw [mem_support_bind_iff] at ho_raw
  rcases ho_raw with ⟨m0, hm0, ho_raw⟩
  rcases run1_not_paused_of_handlePre_inl R hInl false B_A qTot s0 m0 hm0 with ⟨b_out, s_out, rfl⟩
  dsimp only at ho_raw
  rw [mem_support_bind_iff] at ho_raw
  rcases ho_raw with ⟨c_done, -, ho_raw⟩
  rw [mem_support_pure_iff] at ho_raw
  subst ho_raw
  dsimp only [TwoStageCostedReduction.eval2, R, PrefixRedHalted.prefixRedHalted]
  rw [pure_bind]
  dsimp only
  have hq_fin := subs.finishPrefixC_queries b qStart
    (Γ := [PrefixRedHalted.drvHaltedTy subs, .bool, .bool]) (.fst .v0) .v1 .v2 (fun _ => 1)
  have hfin0 := ((Comp.queryBound_eval (isSmTargetQuery ℓ) (fun _ => 1) (fun _ => 0) hw hU
    (subs.finishPrefixC b qStart
      (Γ := [PrefixRedHalted.drvHaltedTy subs, .bool, .bool]) (.fst .v0) .v1 .v2)
    (.cons s_out (.cons b_out (.cons flip .nil)))).mono (by rw [hq_fin])).mono (Nat.zero_le qsK)
  unfold MakesAtMostQueries IsQueryBoundP at hfin0 ⊢
  convert hfin0 using 1 <;>
    (funext x qb; rcases x with _ | _ <;> simp [isSmTargetQuery])

/-- Concrete halted multi-session composition reduction family (`kindRedHalted` + `prefixRedHalted`)
over `atomicE2EOps` and coin-only `atomicBaseSamplers`. -/
@[expose] def redsHalted {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CompositionCostedReductionFamily S (Pt := Pt) ℓ P C K qep decT encT :=
  fun b qStart _qDR qInst =>
    let b_on : SignalPqxdh.QueryBudget := { b with q_total := min b.q_on b.q_total }
    let nInst := min qStart (min b_on.q_total S.N_send_tot)
    let subs0 := prefixSubprogramsHalted (Pt := Pt) S ℓ P C K decT encT qStart
    { kindRed :=
        KindRedHalted.kindRedHalted
          (KindRedHaltedInst.mkKindSubprogramsHaltedClamped
            (TrackInv := PrefixRedHaltedInst.KemBridgeTrackInvLocal C.F K)
            { stepC := fun b qSt qI qep {_} σHE idxE sqE =>
                HaltedDrSessionSim.haltedStepLocalSmGenC
                  (haltedDrStepOps (Pt := Pt) ℓ P C K decT encT)
                  (e2eKeyIndTargetIface S ℓ Pt) rfl b qSt qI qep σHE idxE sqE
              stepCost := HaltedDrSessionSim.haltedStepLocalSmCost ℓ
              stepSize := HaltedDrSessionSim.haltedStepLocalSmSize
              stepC_cost := fun b qSt qI qep {_} σHE idxE sqE =>
                HaltedDrSessionSim.haltedStepLocalSmGenC_cost
                  (haltedDrStepOps (Pt := Pt) ℓ P C K decT encT)
                  (e2eKeyIndTargetIface S ℓ Pt) rfl b qSt qI qep σHE idxE sqE
              stepC_size := fun b qSt qI qep {_} σHE idxE sqE =>
                HaltedDrSessionSim.haltedStepLocalSmGenC_size
                  (haltedDrStepOps (Pt := Pt) ℓ P C K decT encT)
                  (e2eKeyIndTargetIface S ℓ Pt) rfl b qSt qI qep σHE idxE sqE
              stepC_queries := fun b qSt qI qep {_} σHE idxE sqE w =>
                HaltedDrSessionSim.haltedStepLocalSmGenC_queries
                  (haltedDrStepOps (Pt := Pt) ℓ P C K decT encT)
                  (e2eKeyIndTargetIface S ℓ Pt) rfl b qSt qI qep σHE idxE sqE w
              stepCost_bound := fun b qSt qI qep =>
                HaltedDrSessionSim.haltedStepLocalSmCost_le ℓ b qSt qI qep
              stepSize_bound := fun b qSt qDR qI qep =>
                HaltedDrSessionSim.haltedStepLocalSmSize_le S ℓ b qSt qDR qI qep
              stepC_eval := fun b qSt qI qep {_} hInstLen hMeta hCorr hRev hPrin hSess hEp
                  hTrLen hTrInv {_} σHE idxE sqE ρ i sq hσH hidx hsq =>
                HaltedDrSessionSim.haltedStepLocalSmGenC_eval
                  (haltedDrStepOps (Pt := Pt) ℓ P C K decT encT)
                  (e2eKeyIndTargetIface S ℓ Pt) rfl b qSt qI qep σHE idxE sqE ρ _ i sq
                  hσH hidx hsq hInstLen hMeta hCorr hRev hPrin hSess hEp hTrLen
                  (fun st hst =>
                    ⟨(hTrInv st hst).1, (hTrInv st hst).2, (hTrInv st hst).3, (hTrInv st hst).4⟩) }
            b_on)
          b_on qStart qInst qep
      prefixRed := fun k =>
        PrefixRedHalted.prefixRedHalted
          { subs0 with
            promoteSlotKC := fun _ {_} kE idxOptE σE =>
              subs0.promoteSlotKC nInst kE idxOptE σE
            promoteSlotKCost := fun _ => subs0.promoteSlotKCost nInst
            promoteSlotKSize := fun _ => subs0.promoteSlotKSize nInst
            promoteSlotKC_cost := fun _ {_} kE idxOptE σE =>
              subs0.promoteSlotKC_cost nInst kE idxOptE σE
            promoteSlotKC_size := fun _ {_} kE idxOptE σE =>
              subs0.promoteSlotKC_size nInst kE idxOptE σE
            promoteSlotKC_queries := fun _ {_} kE idxOptE σE w =>
              subs0.promoteSlotKC_queries nInst kE idxOptE σE w }
          b_on qStart qInst qep (min k nInst) }

/-- Total and per-kind cost bounds (`CompositionCostedReductionFamilyBounded`) for `redsHalted`. -/
theorem redsHalted_familyBounded {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CompositionCostedReductionFamilyBounded P C K qep decT encT
       (redsHalted (Pt := Pt) S ℓ P C K qep decT encT) := by
  intro b qStart qs
  dsimp only [CompositionCostedReductionFamilyBounded,
    CryptoVerification.E2E.CompositionCostedReductionsBounded, redsHalted]
  let b_on : SignalPqxdh.QueryBudget := { b with q_total := min b.q_on b.q_total }
  refine ⟨⟨CompositionHaltedRedsCost.kindRedHalted_bOn_gRedBounded _ b qStart
        (∑ k ∈ Finset.range qStart, qs k) (Finset.sup (Finset.range qStart) qs) qep,
      fun k hk =>
        CompositionHaltedRedsCost.prefixRedHalted_bOn_gRed2Bounded
          (prefixSubprogramsHaltedB_valid (Pt := Pt) S ℓ P C K decT encT
            b_on qStart (Finset.sup (Finset.range qStart) qs) qep)
          (lt_of_le_of_lt (Nat.min_le_left _ _) hk)
          (Nat.min_le_right _ _)⟩,
    ⟨CompositionHaltedRedsCost.kindRedHalted_bOn_gRedCostByKind _ b qStart
        (∑ k ∈ Finset.range qStart, qs k) (Finset.sup (Finset.range qStart) qs) qep,
      fun k hk =>
        CompositionHaltedRedsCost.prefixRedHalted_bOn_gRed2CostByKind
          (prefixSubprogramsHaltedB_valid (Pt := Pt) S ℓ P C K decT encT
            b_on qStart (Finset.sup (Finset.range qStart) qs) qep)
          (fun σE kqE ρ sec hkq =>
            CompositionHaltedRedsCost.kiStepHaltedClampedC_roQuery_costAt_le
              qStart b_on σE kqE ρ sec hkq)
          (lt_of_le_of_lt (Nat.min_le_left _ _) hk)
          (Nat.min_le_right _ _)⟩⟩

/-- Per-instance `SignalPqxdh.QueryBounded` and Stage-2 `MakesAtMostQueries` bounds for
`redsHalted`. -/
theorem makesAtMostQueries {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : HaltedTargetAdvPerInstanceBounded B_A b qStart qs) :
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    let qInst := Finset.sup (Finset.range qStart) qs
    let qTot := b.q_total + qStart + qDR
    let Re := redsHalted (Pt := Pt) S ℓ P C K qep decT encT b qStart qDR qInst
    SignalPqxdh.QueryBounded (⟨Re.kindRed.eval (fun _ => B_A) ()⟩ : SignalPqxdh.KeyIndAdversary S)
        (keyIndReductionBudget S qStart b) ∧
      (∀ k < qStart,
        ∀ o ∈ support (stageOneAsProbComp ((Re.prefixRed k).eval1 (fun _ => B_A) () qTot false)),
        ∀ flip,
          CryptoGames.SM.MakesAtMostQueries
            ((Re.prefixRed k).eval2 o.2 flip qTot false) (qs k)) := by
  dsimp only [redsHalted]
  let b_on : SignalPqxdh.QueryBudget := { b with q_total := min b.q_on b.q_total }
  refine
    ⟨CompositionHaltedRedsCost.kindRedHalted_queryBounded_inst_fuel _
        b_on b qStart (Finset.sup (Finset.range qStart) qs) qep qs B_A hB,
      fun k hk o ho flip => ?_⟩
  let nInst := min qStart (min b_on.q_total S.N_send_tot)
  by_cases hkInst : k < nInst
  · have hmin : min k nInst = k := Nat.min_eq_left (Nat.le_of_lt hkInst)
    dsimp only [nInst, b_on] at hmin
    rw [hmin] at ho ⊢
    exact PrefixRedHaltedInst.prefixRedHalted_makesAtMostQueries_of_inst
      (prefixSubprogramsHaltedB (Pt := Pt) S ℓ P C K decT encT b_on qStart)
      b_on qStart (Finset.sup (Finset.range qStart) qs) qep
      (b.q_total + qStart + ∑ j ∈ Finset.range qStart, qs j) k (qs k)
      B_A (hB.2.2.2.2.2.2.2.2 k hk) o ho flip
  · have hmin : min k nInst = nInst := Nat.min_eq_right (Nat.not_lt.mp hkInst)
    dsimp only [nInst, b_on] at hmin
    rw [hmin] at ho ⊢
    exact prefixRedHalted_makesAtMostQueries_noPause
      (prefixSubprogramsHaltedB (Pt := Pt) S ℓ P C K decT encT b_on qStart)
      b_on qStart (Finset.sup (Finset.range qStart) qs) qep
      (b.q_total + qStart + ∑ j ∈ Finset.range qStart, qs j)
      (min qStart (min b_on.q_total S.N_send_tot)) (qs k)
      (fun idxOptE σE ρ =>
        promoteSlotKClamped_eval_noPromote S ℓ P C K decT encT b_on qStart idxOptE σE ρ)
      B_A o ho flip

/-- Exact `pqxdhKeyInd1KeyRealExp` `ProbComp` equivalence between `(redsHalted ...).kindRed` and
`MainHaltedKeyInd.bhKindRedWithTracked` under `SignalPqxdh.pqxdhKeyIndImpl1KeyReal`. -/
theorem kindRealExp_eq {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : HaltedTargetAdvPerInstanceBounded B_A b qStart qs) :
    SignalPqxdh.pqxdhKeyInd1KeyRealExp S P
        ⟨(redsHalted (Pt := Pt) S ℓ P C K qep decT encT b qStart
            (∑ k ∈ Finset.range qStart, qs k)
            (Finset.sup (Finset.range qStart) qs)).kindRed.eval (fun _ => B_A) ()⟩ =
      SignalPqxdh.pqxdhKeyInd1KeyRealExp S P
        ⟨(bhKindRedWithTracked (kemFailSessionTracker (ℓ := ℓ) C.F K).init
            (fun d : BHModelInst S ℓ =>
              oracleImplRSessionTracked (kemFailSessionTracker (ℓ := ℓ) C.F K)
                (sessionSchemeFixedSpk
                  (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB)
                  ℓ d.spkCoins)
                (2 + 1) qep (configRefuseEarlyBobCorr decT encT))
            P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K).eval (fun _ => B_A) ()⟩ := by
  dsimp only [redsHalted]
  exact CompositionHaltedRedsKindSim.clamped_bOn_kindRealExp_eq
    (Pt := Pt) S ℓ P C K qep decT encT _ hP b qStart qs B_A hB

/-- Exact Stage-1 + Stage-2 `ProbComp` equivalence between `(redsHalted ...).prefixRed k` and
`MainHaltedPrefixCore.bhPrefixRedWithSessionTracked`. -/
theorem prefixEval_eq {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : HaltedTargetAdvPerInstanceBounded B_A b qStart qs)
    {k : ℕ} (hk : k < qStart) (flip : Bool) :
    let qDR := ∑ j ∈ Finset.range qStart, qs j
    let qInst := Finset.sup (Finset.range qStart) qs
    let qTot := b.q_total + qStart + qDR
    let Re := redsHalted (Pt := Pt) S ℓ P C K qep decT encT b qStart qDR qInst
    (stageOneAsProbComp ((Re.prefixRed k).eval1 (fun _ => B_A) () qTot false) >>= fun o =>
        Prod.fst <$> gameRSessionTracked (kemFailSessionTracker (ℓ := ℓ) C.F K)
          (sessionSchemeFixedSpk
            (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) o.1.1 o.1.2.1)
            ℓ o.1.2.2)
          (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
          ((Re.prefixRed k).eval2 o.2 flip qTot false)) =
      (stageOneAsProbComp
          ((bhPrefixRedWithSessionTracked (kemFailSessionTracker (ℓ := ℓ) C.F K)
              P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K qep decT encT k).eval1
            (fun _ => B_A) () qTot false) >>=
        fun o =>
          Prod.fst <$> gameRSessionTracked (kemFailSessionTracker (ℓ := ℓ) C.F K)
            (sessionSchemeFixedSpk
              (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) o.1.idA o.1.idB)
              ℓ o.1.spkCoins)
            (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
            ((bhPrefixRedWithSessionTracked (kemFailSessionTracker (ℓ := ℓ) C.F K)
                P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K qep decT encT k).eval2
              o.2 flip qTot false)) := by
  have _ := hk
  dsimp only [redsHalted]
  let b_on : SignalPqxdh.QueryBudget := { b with q_total := min b.q_on b.q_total }
  exact CompositionHaltedRedsPrefixSim.prefixEval_clamped_bOn_eq_of_valid_inst
    (subs := prefixSubprogramsHaltedB (Pt := Pt) S ℓ P C K decT encT b_on qStart)
    (prefixSubprogramsHaltedB_valid (Pt := Pt) S ℓ P C K decT encT b_on qStart
      (Finset.sup (Finset.range qStart) qs) qep)
    le_rfl hP
    (fun {σH} hInstLen {Γ} kE idxOptE σE ρ idx? hkE hidx hσ => by
      dsimp only [prefixSubprogramsHaltedB, prefixSubprogramsHalted] at σE hσ ⊢
      rw [show PrefixRedHaltedByKind.onlineClampedBudget b = b_on from rfl] at hInstLen hkE ⊢
      have hfalse : decide (min qStart (min b_on.q_total S.N_send_tot) <
          min qStart (min b_on.q_total S.N_send_tot)) = false := by simp
      have hnotlt : ¬ min qStart (min b_on.q_total S.N_send_tot) < σH.1.insts.length :=
        Nat.not_lt.mpr hInstLen
      simp only [Comp.eval, Expr.eval, Expr.v0, Env.get, pure_bind, hkE, hidx, hσ,
        hfalse, Bool.false_eq_true, ↓reduceIte, bhPromoteSlotK, hnotlt])
    B_A hB
    (fun idA idB spkCoins comp =>
      Prod.fst <$> gameRSessionTracked (kemFailSessionTracker (ℓ := ℓ) C.F K)
        (sessionSchemeFixedSpk
          (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
          ℓ spkCoins)
        (2 + 1) qep (configRefuseEarlyBobCorr decT encT) comp)
    (b.q_total + qStart + ∑ j ∈ Finset.range qStart, qs j) flip

end Computational.Proofs.E2E.Dsl.CompositionHaltedReds
