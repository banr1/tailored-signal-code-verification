/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.Pqxdh.StatementPqReds

/-!
# End-to-End Composition and CLI Adapter Reduction Guards

Definitional (`rfl`) guards for the `ReductionDsl.atomicSig` codecs, oracle interfaces,
`CompositionCostedReductions` and `CliToModelAdapterProg` program types, boundedness predicates,
step-cost budgets (`bhAdapterCostBudget`, `bhE2ECostBudget`), and per-kind query classifier,
counts, and budgets (`bhQueryKind`, `bhKindCounts`, `bhAdapterCostBudgetByKind`,
`bhE2ECostBudgetByKind`) from `StatementBinaryHarnessCore` and `StatementPqReds`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Computational.Tests.Guards.StatementPqRedsGuard

public section

open OracleComp OracleSpec MeasureTheory ENNReal
open CryptoVerification CryptoVerification.E2E CryptoGames CryptoGames.LibsignalSM Ratchet
  LibsignalInst LibsignalSession CryptoGames.LibsignalSessionApi CBC SM
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.LibsignalSession

theorem bhCtlUnStart_startDR {S : SignalPqxdh.Setup} (sid : SignalPqxdh.SessionId S) :
    bhCtlUnStart (.startDR sid) = sid := rfl

theorem e2eTargetGameCodec_eq (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type) :
    e2eTargetGameCodec S ℓ Pt = ReductionDsl.e2eGameCodec S ℓ Pt bhCtlUnStart := rfl

theorem e2eTargetGameCodec_codecCost (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type) :
    (e2eTargetGameCodec S ℓ Pt).codecCost = 64 := rfl

theorem e2eBhAdapterIface_eq (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type) :
    e2eBhAdapterIface S ℓ Pt = ReductionDsl.e2eAdapterIface S ℓ Pt BHDRCtlQuery.startDR := rfl

theorem e2eBhAdapterCodec_eq (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type) :
    e2eBhAdapterCodec S ℓ Pt = ReductionDsl.e2eAdapterCodec S ℓ Pt bhCtlUnStart := rfl

theorem e2eBhAdapterCodec_codecCost (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type) :
    (e2eBhAdapterCodec S ℓ Pt).codecCost = 64 := rfl

theorem atomicSort_blocks_plain (ℓ : ℕ) (Pt : Type) (m : Plain ℓ) :
    ReductionDsl.AtomicSort.blocks ℓ Pt .plain m = ℓ / 32 + 1 := rfl

theorem cliToModelAdapterProg_eq (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CliToModelAdapterProg S ℓ decT encT =
      ReductionDsl.CostedReduction (ReductionDsl.atomicAdapterOps ℓ decT encT)
        (e2eBhAdapterIface S ℓ Pt)
        (bhGameSpec S ℓ (BitVec 512)) (e2eBhAdapterCodec S ℓ Pt) .unit .unit .bool .bool := rfl

theorem bhAdapterCostBudget_eq (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR ℓ : ℕ) :
    bhAdapterCostBudget S b qStart qDR ℓ =
      (let M_id := min b.q_total S.N_id
       let M_spk := min b.q_total S.N_spk_tot
       let M_opk := min b.q_total S.N_opk_tot
       let M_send := min b.q_total S.N_send_tot
       2 ^ 6 * (b.q_total + qStart + qDR + 1) *
         (2 * M_id + 56 * M_spk + 3 * M_opk + 2 * M_send +
           2 * Nat.log 2 S.N_id + 8 * Nat.log 2 S.N_spk_tot +
           2 * Nat.log 2 S.N_opk_tot + 2 * Nat.log 2 S.N_send_tot +
           4 * qStart + 4 * ℓ + 2 ^ 12)) := rfl

theorem bhQueryKind_roQuery {S : SignalPqxdh.Setup} {ι : Type} (x : SignalPqxdh.Bytes) :
    bhQueryKind (S := S) (ι := ι) (.inl (.inl (.roQuery x))) = 1 := rfl

theorem bhQueryKind_testSession {S : SignalPqxdh.Setup} {ι : Type} (sid : SignalPqxdh.SessionId S) :
    bhQueryKind (S := S) (ι := ι) (.inl (.inl (.testSession sid))) = 0 := rfl

theorem bhQueryKind_startDR {S : SignalPqxdh.Setup} {ι : Type} (sid : SignalPqxdh.SessionId S) :
    bhQueryKind (S := S) (ι := ι) (.inl (.inr (.startDR sid))) = 0 := rfl

theorem bhQueryKind_inr {S : SignalPqxdh.Setup} {ι : Type} (j : ι) :
    bhQueryKind (S := S) (ι := ι) (.inr j) = 0 := rfl

theorem bhKindCounts_eq (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    bhKindCounts b qStart qDR 0 = min b.q_on b.q_total + qStart + qDR ∧
      bhKindCounts b qStart qDR 1 = min b.q_ro b.q_total := ⟨rfl, rfl⟩

theorem bhAdapterCostBudgetByKind_eq (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR ℓ : ℕ) :
    bhAdapterCostBudgetByKind S b qStart qDR ℓ =
      (let M_on := min b.q_on b.q_total
       let M_ro := min b.q_ro b.q_total
       let M_id := min M_on S.N_id
       let M_spk := min M_on S.N_spk_tot
       let M_opk := min M_on S.N_opk_tot
       let M_send := min M_on S.N_send_tot
       2 ^ 6 * (M_on + qStart + qDR + 1) *
           (2 * M_id + 56 * M_spk + 3 * M_opk + 2 * M_send +
             2 * Nat.log 2 S.N_id + 8 * Nat.log 2 S.N_spk_tot +
             2 * Nat.log 2 S.N_opk_tot + 2 * Nat.log 2 S.N_send_tot +
             4 * qStart + 4 * ℓ + 2 ^ 12) +
         2 ^ 12 * M_ro) := rfl

theorem cliAdapterCostBounded_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ)
    (L : CliToModelAdapterProg S ℓ decT encT) :
    CliAdapterCostBounded decT encT b qStart qDR L =
      (let qTot := b.q_total + qStart + qDR
       let qKind := bhKindCounts b qStart qDR
       GRedBounded L (fun _ => 1) (fun _ => 0) qTot qTot
         (bhAdapterCostBudget S b qStart qDR ℓ) ∧
       GRedCostByKind L (fun _ => 1) (fun _ => 0) bhQueryKind qKind (List.ofFn qKind).sum
         (bhAdapterCostBudgetByKind S b qStart qDR ℓ) ∧
       CliAdapterForwardsKinds L qKind) := rfl

theorem cliAdapterForwardsKinds_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (L : CliToModelAdapterProg S ℓ decT encT) (qKind : Fin 2 → ℕ) :
    CliAdapterForwardsKinds L qKind =
      (∀ (A : Unit → OracleComp (unifSpec + bhGameSpec S ℓ (BitVec 512)) Bool),
        (∀ a i, (A a).IsQueryBoundP
          (fun t => SignalPqxdh.isGameQueryOfKind bhQueryKind i t = true) (qKind i)) →
        ∀ i, (L.eval A ()).IsQueryBoundP
          (fun t => SignalPqxdh.isGameQueryOfKind bhQueryKind i t = true) (qKind i)) := rfl

theorem bhE2ECostBudget_eq (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qInst qep ℓ : ℕ) :
    bhE2ECostBudget S b qStart qDR qInst qep ℓ =
      (let nId := min b.q_total S.N_id
       let nSpk := min b.q_total S.N_spk_tot
       let nOpk := min b.q_total S.N_opk_tot
       let nSend := min b.q_total S.N_send_tot
       let nRecv := min b.q_total S.N_recv_tot
       let nInst := min qStart nSend
       2 ^ 10 * (b.q_total + qStart + qDR + 1) *
           (b.q_total + nOpk + nInst + qInst + Nat.log 2 qep +
             10 * (nId + nSpk + nSend + nRecv) + maxForwardJumps + ℓ + 1) +
         2 ^ 13 * nInst * (nId + nSpk + nRecv + 1)) := rfl

theorem bhE2ECostBudgetByKind_eq (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qInst qep ℓ : ℕ) :
    bhE2ECostBudgetByKind S b qStart qDR qInst qep ℓ =
      (let M_on := min b.q_on b.q_total
       let M_ro := min b.q_ro b.q_total
       let Q_on := M_on + qStart + qDR
       let nId := min M_on S.N_id
       let nSpk := min M_on S.N_spk_tot
       let nOpk := min M_on S.N_opk_tot
       let nSend := min M_on S.N_send_tot
       let nRecv := min M_on S.N_recv_tot
       let nInst := min qStart nSend
       2 ^ 10 * (Q_on + 1) *
           (M_on + nOpk + nInst + qInst + Nat.log 2 qep +
             10 * (nId + nSpk + nSend + nRecv) + maxForwardJumps + ℓ + 1) +
         2 ^ 13 * (M_ro + Q_on) * (ReductionDsl.bits (M_ro + 2 * Q_on + 1) + 4) +
         2 ^ 13 * nInst * (nId + nSpk + nRecv + 1)) := rfl

@[expose] def compositionCostedReductionsKindRed {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : LibsignalSpqrV1.MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (R : CompositionCostedReductions S ℓ P C K qep decT encT) :
    ReductionDsl.CostedReduction (ReductionDsl.atomicE2EOps ℓ P C K decT encT)
      (ReductionDsl.e2eKeyIndTargetIface S ℓ Pt)
      (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ Pt)
      .unit .unit .bool .bool :=
  R.kindRed

@[expose] def compositionCostedReductionsPrefixRed {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : LibsignalSpqrV1.MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (R : CompositionCostedReductions S ℓ P C K qep decT encT) (k : ℕ) :
    ReductionDsl.TwoStageCostedReduction (ReductionDsl.atomicE2EOps ℓ P C K decT encT)
      (ReductionDsl.e2eSessionTargetIface ℓ Pt)
      (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ Pt)
      .unit .unit .bool (ReductionDsl.prefixCtxT (ℓ := ℓ) (Pt := Pt)) .bool .bool :=
  R.prefixRed k

@[expose] def mkCompositionCostedReductions {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : LibsignalSpqrV1.MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (kindRed :
      ReductionDsl.CostedReduction (ReductionDsl.atomicE2EOps ℓ P C K decT encT)
        (ReductionDsl.e2eKeyIndTargetIface S ℓ Pt)
        (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ Pt)
        .unit .unit .bool .bool)
    (prefixRed : (k : ℕ) →
      ReductionDsl.TwoStageCostedReduction (ReductionDsl.atomicE2EOps ℓ P C K decT encT)
        (ReductionDsl.e2eSessionTargetIface ℓ Pt)
        (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ Pt)
        .unit .unit .bool (ReductionDsl.prefixCtxT (ℓ := ℓ) (Pt := Pt)) .bool .bool) :
    CompositionCostedReductions S ℓ P C K qep decT encT :=
  { kindRed := kindRed, prefixRed := prefixRed }

theorem mkCompositionCostedReductions_eta {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : LibsignalSpqrV1.MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (R : CompositionCostedReductions S ℓ P C K qep decT encT) :
    mkCompositionCostedReductions
      (compositionCostedReductionsKindRed R)
      (compositionCostedReductionsPrefixRed R) = R := rfl

theorem compositionCostedReductionFamily_eq (S : SignalPqxdh.Setup) {Pt : Type} (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CompositionCostedReductionFamily S ℓ P C K qep decT encT =
      ((b : SignalPqxdh.QueryBudget) → (qStart qDR qInst : ℕ) →
        CompositionCostedReductions S ℓ P C K qep decT encT) := rfl

theorem compositionCostedReductionsBounded_eq {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (R : CompositionCostedReductions S ℓ P C K qep decT encT) :
    CompositionCostedReductionsBounded P C K qep decT encT b qStart qs R =
      (let qDR := ∑ k ∈ Finset.range qStart, qs k
       let qInst := Finset.sup (Finset.range qStart) qs
       let qTot := b.q_total + qStart + qDR
       let B := bhE2ECostBudget S b qStart qDR qInst qep ℓ
       let qKind := bhKindCounts b qStart qDR
       let qSum := (List.ofFn qKind).sum
       let Bk := bhE2ECostBudgetByKind S b qStart qDR qInst qep ℓ
       (GRedBounded R.kindRed (fun _ => 1) (fun _ => 0) qTot (2 * qTot) B ∧
       (∀ k < qStart,
         GRed2Bounded (R.prefixRed k) (fun _ => 1) (fun _ => 0) qTot qTot B false)) ∧
       (GRedCostByKind R.kindRed (fun _ => 1) (fun _ => 0) bhQueryKind qKind (2 * qSum) Bk ∧
       (∀ k < qStart,
         GRed2CostByKind (R.prefixRed k) (fun _ => 1) (fun _ => 0) bhQueryKind qKind qSum
           Bk))) := rfl

theorem compositionCostedReductionFamilyBounded_eq {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (reds : CompositionCostedReductionFamily S ℓ P C K qep decT encT) :
    CompositionCostedReductionFamilyBounded P C K qep decT encT reds =
      (∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ),
        CompositionCostedReductionsBounded P C K qep decT encT b qStart qs
          (reds b qStart (∑ k ∈ Finset.range qStart, qs k) (Finset.sup (Finset.range qStart) qs))) := rfl

theorem compositionLocalStart_type (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (bMode? : Option Bool)
    (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S) :
    compositionLocalStart ki C K bMode? σ sid =
      (do
        match bhE2EGuard σ sid with
        | none => return (none, σ)
        | some (_, _, (u, j)) =>
          let (kr1, st1) ← (ki (.testSession sid)).run σ.st
          let (kr2, st2) ← (ki (.revealSpkSk u j)).run st1
          let ac ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
          return bhE2EFinishStartSpk C K bMode? { σ with st := st2 } sid kr1 kr2 ac) := rfl

end
end Computational.Tests.Guards.StatementPqRedsGuard
