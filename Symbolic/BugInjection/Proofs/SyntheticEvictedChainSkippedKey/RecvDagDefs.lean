/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.I0Laws
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.ShaMacLaws
public import Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj

/-!
# Concrete DAG Certificate Types and Evaluator

Defines `DagOp`, the fuel-bounded symbolic shape evaluator `evalDagShapeAux`, the per-node byte
certificate `dagNodeOk`, and the bucketed collision check `bucketNoCollision`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs

open DY (Bytes)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (canonicalVariation sha256CompressFunction FieldItem PbValue)
open DY.Libsignal.Composed.Refinement
  (OpaqueSymbolSemantics Ghost gamma gamma' randTerm litOf clamp trWireBytes
   assumedInjective MemoCollisionOn prefixTerms plaintextTerms)
open ByteSpecs (hmacWith)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compKyberEncaps bytesToNat)
open Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj (eq_of_bytesToNat_eq)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedLookupPub evictedLookupDh evictedAesPerm)

/-- Structural constructor of a deduplicated concrete DAG node. -/
inductive DagOp where
  | rand (ts sz : Nat)
  | lit (bs : HwBytes)
  | concat (l r : Nat)
  | dhPk (s : Nat)
  | dh (pk sk : Nat)
  | kdf (a b : Nat)
  | symEncPt (k iv ptTs : Nat) (ptBs : HwBytes)
  | trunc8 (a : Nat)
  | trWire (ver : UInt8) (rk : Nat) (cnt prev : UInt32) (ct pq : Nat) (addr : HwBytes)
  | kemEncap (p e : Nat)
  | kemSS (p e : Nat)

/-- Whether a `DagOp` head has `assumedInjective = true`. -/
def DagOp.isAI : DagOp → Bool
  | .lit _ | .concat _ _ | .trWire .. => false
  | _ => true

/-- Checks that every child index of `op` is strictly less than `id`. -/
def DagOp.childrenLt (id : Nat) : DagOp → Bool
  | .rand _ _ | .lit _ => true
  | .concat l r => decide (l < id) && decide (r < id)
  | .dhPk s => decide (s < id)
  | .dh s1 s2 => decide (s1 < id) && decide (s2 < id)
  | .kdf a b => decide (a < id) && decide (b < id)
  | .symEncPt k iv _ _ => decide (k < id) && decide (iv < id)
  | .trunc8 a => decide (a < id)
  | .trWire _ rk _ _ ct pq _ => decide (rk < id) && decide (ct < id) && decide (pq < id)
  | .kemEncap p e => decide (p < id) && decide (e < id)
  | .kemSS p e => decide (p < id) && decide (e < id)

/-- Concrete byte evaluation check for a single `DagOp` node `id`. -/
def dagOpBytesOk (bytesOf : Nat → HwBytes) (id : Nat) (op : DagOp) : Bool :=
  let v := bytesOf id
  match op with
  | .rand _ sz => decide (sz ≠ 0)
  | .lit bs => v == bs
  | .concat l r => v == bytesOf l ++ bytesOf r
  | .dhPk s => v == evictedLookupPub (clamp (bytesOf s))
  | .dh pk sk => v == evictedLookupDh (clamp (bytesOf sk)) (bytesOf pk)
  | .kdf a b => v == hmacWith (sha256CompressFunction evictedI0) (bytesOf a) (bytesOf b)
  | .symEncPt k iv _ ptBs => v == evictedAesPerm (bytesOf k) ((bytesOf iv).take 16) ptBs
  | .trunc8 a => v == (bytesOf a).take 8
  | .trWire ver rk cnt prev ct pq addr =>
      v == trWireBytes addr canonicalVariation
        { version := ver.toNat, ratchetKey := bytesOf rk, counter := cnt.toNat,
          previousCounter := prev.toNat, ciphertext := bytesOf ct } (bytesOf pq)
  | .kemEncap _ e =>
      decide ((bytesOf e).length = 32) && v == (compKyberEncaps (bytesOf e)).take 1568
  | .kemSS _ e =>
      decide ((bytesOf e).length = 32) && v == (compKyberEncaps (bytesOf e)).drop 1568

/-- Full per-node certificate: topological order, byte evaluation, length bound `< 2048`,
and for `isAI = true`, length `≥ 8` and non-matching `TRState` `[0x01, 0x00]` spine suffix. -/
def dagNodeOk (opOf : Nat → DagOp) (bytesOf : Nat → HwBytes) (id : Nat) : Bool :=
  let op := opOf id
  let v := bytesOf id
  op.childrenLt id &&
  decide (v.length < 2048) &&
  dagOpBytesOk bytesOf id op &&
  (!op.isAI || (decide (8 ≤ v.length) &&
    !(decide (38 ≤ v.length) && (v.drop (v.length - 2) == [0x01#8, 0x00#8]))))

/-- Fuel-bounded evaluator reconstructing the symbolic `ConcretizedTerm.shape` of `id`. -/
def evalDagShapeAux (opOf : Nat → DagOp) : Nat → Nat → Bytes
  | 0, _ => litOf []
  | fuel + 1, id =>
    match opOf id with
    | .rand ts sz => randTerm ts sz
    | .lit bs => litOf bs
    | .concat l r => DY.Concat.concat (evalDagShapeAux opOf fuel l) (evalDagShapeAux opOf fuel r)
    | .dhPk s => DY.DiffieHellman.dhPk (evalDagShapeAux opOf fuel s)
    | .dh pk sk => DY.DiffieHellman.dh (evalDagShapeAux opOf fuel pk) (evalDagShapeAux opOf fuel sk)
    | .kdf a b => DY.KdfExtract.kdfExtract (evalDagShapeAux opOf fuel a) (evalDagShapeAux opOf fuel b)
    | .symEncPt k iv ptTs _ =>
        DY.SymEnc.symEnc (evalDagShapeAux opOf fuel k) (evalDagShapeAux opOf fuel iv) (randTerm ptTs 32)
    | .trunc8 a => DY.Trunc.trunc8 (evalDagShapeAux opOf fuel a)
    | .trWire ver rk cnt prev ct pq addr =>
        DY.TrWire.trWireMsg ver (evalDagShapeAux opOf fuel rk) cnt prev
          (evalDagShapeAux opOf fuel ct) (evalDagShapeAux opOf fuel pq)
          { canonicalVariation with
            fields := .extra 6 (.bytes addr) 0 0 :: canonicalVariation.fields }
    | .kemEncap p e =>
        ({ pk := evalDagShapeAux opOf fuel p, entropy := evalDagShapeAux opOf fuel e } :
          DY.PQKem.Encap.SubF Bytes).pack
    | .kemSS p e =>
        ({ pk := evalDagShapeAux opOf fuel p, entropy := evalDagShapeAux opOf fuel e } :
          DY.PQKem.SharedSecret.SubF Bytes).pack

/-- Fuel-independence of `evalDagShapeAux` once fuel exceeds `id` on a topologically ordered DAG. -/
theorem evalDagShapeAux_irrel (opOf : Nat → DagOp)
    (htopo : ∀ i, (opOf i).childrenLt i = true) :
    ∀ (f₁ f₂ id : Nat), id < f₁ → id < f₂ →
      evalDagShapeAux opOf f₁ id = evalDagShapeAux opOf f₂ id
  | 0, _, _, h1, _ => absurd h1 (Nat.not_lt_zero _)
  | _, 0, _, _, h2 => absurd h2 (Nat.not_lt_zero _)
  | f₁ + 1, f₂ + 1, id, h1, h2 => by
    have hc := htopo id
    have ih : ∀ c, c < id → evalDagShapeAux opOf f₁ c = evalDagShapeAux opOf f₂ c :=
      fun c hlt => evalDagShapeAux_irrel opOf htopo f₁ f₂ c (by omega) (by omega)
    cases hop : opOf id <;> rw [hop] at hc <;>
      simp only [DagOp.childrenLt, Bool.and_eq_true, decide_eq_true_eq] at hc <;>
      simp only [evalDagShapeAux, hop]
    · rw [ih _ hc.1, ih _ hc.2]
    · rw [ih _ hc]
    · rw [ih _ hc.1, ih _ hc.2]
    · rw [ih _ hc.1, ih _ hc.2]
    · rw [ih _ hc.1, ih _ hc.2]
    · rw [ih _ hc]
    · rw [ih _ hc.1.1, ih _ hc.1.2, ih _ hc.2]
    · rw [ih _ hc.1, ih _ hc.2]
    · rw [ih _ hc.1, ih _ hc.2]

/-- Injective integer key for `HwBytes` of length `< 2048`. -/
def packBytesKey (bs : HwBytes) : Nat :=
  bs.length + 2048 * bytesToNat bs

theorem packBytesKey_inj {a b : HwBytes}
    (ha : a.length < 2048) (hb : b.length < 2048)
    (heq : packBytesKey a = packBytesKey b) : a = b := by
  unfold packBytesKey at heq
  have hlen : a.length = b.length := by omega
  have hnat : bytesToNat a = bytesToNat b := by omega
  exact eq_of_bytesToNat_eq hlen hnat

/-- Bucket index `0..255` from first byte (`0` on empty). -/
def bytesBucketIdx (bs : HwBytes) : Nat :=
  match bs with
  | [] => 0
  | b :: _ => b.toNat

/-- Checks that within a bucket of `(id, isAI, packedKey)` triples, no `isAI = true` entry
shares `packedKey` with any distinct `id' ≠ id`. -/
def bucketNoCollision (entries : List (Nat × Bool × Nat)) : Bool :=
  entries.all fun (id₁, ai₁, k₁) =>
    !ai₁ || entries.all fun (id₂, _, k₂) =>
      decide (k₁ ≠ k₂) || decide (id₁ = id₂)

theorem bucketNoCollision_sound {entries : List (Nat × Bool × Nat)}
    (h : bucketNoCollision entries = true)
    {id₁ id₂ : Nat} {ai₁ ai₂ : Bool} {k : Nat}
    (h₁ : (id₁, ai₁, k) ∈ entries) (h₂ : (id₂, ai₂, k) ∈ entries)
    (hai : ai₁ = true ∨ ai₂ = true) : id₁ = id₂ := by
  unfold bucketNoCollision at h
  rcases hai with rfl | rfl
  · have h1 := List.all_eq_true.mp h (id₁, true, k) h₁
    simp only [Bool.not_true, Bool.false_or] at h1
    have h2 := List.all_eq_true.mp h1 (id₂, ai₂, k) h₂
    simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_or, decide_eq_true_eq] at h2
    exact h2
  · have h1 := List.all_eq_true.mp h (id₂, true, k) h₂
    simp only [Bool.not_true, Bool.false_or] at h1
    have h2 := List.all_eq_true.mp h1 (id₁, ai₁, k) h₁
    simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_or, decide_eq_true_eq] at h2
    exact h2.symm

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs
