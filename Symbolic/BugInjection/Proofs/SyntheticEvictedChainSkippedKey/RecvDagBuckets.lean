/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagBucketData
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert0
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert1
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert2
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert3
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert4
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert5
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert6
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert7
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert8
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert9
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert10
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert11
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert12
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert13
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert14
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert15
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert16
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert17

/-!
# Certified Node Validity and Bucket Collision Freedom

Combines the 18 node-certificate slices (`RecvDagCert0`–`RecvDagCert17`) into `dag_nodes_ok`,
checks bucket coverage (`id_covered`) and per-bucket non-collision (`bucket_collision_free`)
across all 251 hash buckets, and proves `dag_no_collision`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagBuckets

open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs
  (DagOp dagNodeOk bucketNoCollision bucketNoCollision_sound)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagSize dagOp dagBytes fastBytesKey fastBucketIdx)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagBucketData (dagBucketIds)

theorem dag_nodes_ok : ∀ id < dagSize, dagNodeOk dagOp dagBytes id = true := by
  intro id hid
  if h0 : id < 384 then
    exact RecvDagCert0.certRangeOk_0 (by omega) h0
  else
  if h1 : id < 768 then
    exact RecvDagCert1.certRangeOk_1 (by omega) h1
  else
  if h2 : id < 1152 then
    exact RecvDagCert2.certRangeOk_2 (by omega) h2
  else
  if h3 : id < 1536 then
    exact RecvDagCert3.certRangeOk_3 (by omega) h3
  else
  if h4 : id < 1920 then
    exact RecvDagCert4.certRangeOk_4 (by omega) h4
  else
  if h5 : id < 2304 then
    exact RecvDagCert5.certRangeOk_5 (by omega) h5
  else
  if h6 : id < 2688 then
    exact RecvDagCert6.certRangeOk_6 (by omega) h6
  else
  if h7 : id < 3072 then
    exact RecvDagCert7.certRangeOk_7 (by omega) h7
  else
  if h8 : id < 3456 then
    exact RecvDagCert8.certRangeOk_8 (by omega) h8
  else
  if h9 : id < 3840 then
    exact RecvDagCert9.certRangeOk_9 (by omega) h9
  else
  if h10 : id < 4224 then
    exact RecvDagCert10.certRangeOk_10 (by omega) h10
  else
  if h11 : id < 4608 then
    exact RecvDagCert11.certRangeOk_11 (by omega) h11
  else
  if h12 : id < 4992 then
    exact RecvDagCert12.certRangeOk_12 (by omega) h12
  else
  if h13 : id < 5376 then
    exact RecvDagCert13.certRangeOk_13 (by omega) h13
  else
  if h14 : id < 5760 then
    exact RecvDagCert14.certRangeOk_14 (by omega) h14
  else
  if h15 : id < 6144 then
    exact RecvDagCert15.certRangeOk_15 (by omega) h15
  else
  if h16 : id < 6528 then
    exact RecvDagCert16.certRangeOk_16 (by omega) h16
  else
    exact RecvDagCert17.certRangeOk_17 (by omega) hid

def dagBucketEntries (b : Nat) : List (Nat × Bool × Nat) :=
  (dagBucketIds b).map fun id => (id, (dagOp id).isAI, fastBytesKey (dagBytes id))

def covRangeOk (lo count : Nat) : Bool :=
  (List.range count).all fun k =>
    (dagBucketIds (fastBucketIdx (fastBytesKey (dagBytes (lo + k))))).elem (lo + k)

theorem idCovered_of_covRangeOk {lo count : Nat} (h : covRangeOk lo count = true)
    {id : Nat} (hlo : lo ≤ id) (hhi : id < lo + count) :
    (dagBucketIds (fastBucketIdx (fastBytesKey (dagBytes id)))).elem id = true := by
  unfold covRangeOk at h
  have hmem : id - lo ∈ List.range count := List.mem_range.mpr (by omega)
  have hk := List.all_eq_true.mp h (id - lo) hmem
  have heq : lo + (id - lo) = id := by omega
  rwa [heq] at hk

def bktRangeOk (lo count : Nat) : Bool :=
  (List.range count).all fun k => bucketNoCollision (dagBucketEntries (lo + k))

theorem bktOk_of_bktRangeOk {lo count : Nat} (h : bktRangeOk lo count = true)
    {b : Nat} (hlo : lo ≤ b) (hhi : b < lo + count) :
    bucketNoCollision (dagBucketEntries b) = true := by
  unfold bktRangeOk at h
  have hmem : b - lo ∈ List.range count := List.mem_range.mpr (by omega)
  have hk := List.all_eq_true.mp h (b - lo) hmem
  have heq : lo + (b - lo) = b := by omega
  rwa [heq] at hk

private theorem covSlice_0 : covRangeOk 0 512 = true := by decide +kernel
private theorem covSlice_1 : covRangeOk 512 512 = true := by decide +kernel
private theorem covSlice_2 : covRangeOk 1024 512 = true := by decide +kernel
private theorem covSlice_3 : covRangeOk 1536 512 = true := by decide +kernel
private theorem covSlice_4 : covRangeOk 2048 512 = true := by decide +kernel
private theorem covSlice_5 : covRangeOk 2560 512 = true := by decide +kernel
private theorem covSlice_6 : covRangeOk 3072 512 = true := by decide +kernel
private theorem covSlice_7 : covRangeOk 3584 512 = true := by decide +kernel
private theorem covSlice_8 : covRangeOk 4096 512 = true := by decide +kernel
private theorem covSlice_9 : covRangeOk 4608 512 = true := by decide +kernel
private theorem covSlice_10 : covRangeOk 5120 512 = true := by decide +kernel
private theorem covSlice_11 : covRangeOk 5632 512 = true := by decide +kernel
private theorem covSlice_12 : covRangeOk 6144 512 = true := by decide +kernel
private theorem covSlice_13 : covRangeOk 6656 64 = true := by decide +kernel

theorem id_covered : ∀ id < dagSize,
    (dagBucketIds (fastBucketIdx (fastBytesKey (dagBytes id)))).elem id = true := by
  intro id hid
  if hc0 : id < 512 then
    exact idCovered_of_covRangeOk covSlice_0 (by omega) hc0
  else
  if hc1 : id < 1024 then
    exact idCovered_of_covRangeOk covSlice_1 (by omega) hc1
  else
  if hc2 : id < 1536 then
    exact idCovered_of_covRangeOk covSlice_2 (by omega) hc2
  else
  if hc3 : id < 2048 then
    exact idCovered_of_covRangeOk covSlice_3 (by omega) hc3
  else
  if hc4 : id < 2560 then
    exact idCovered_of_covRangeOk covSlice_4 (by omega) hc4
  else
  if hc5 : id < 3072 then
    exact idCovered_of_covRangeOk covSlice_5 (by omega) hc5
  else
  if hc6 : id < 3584 then
    exact idCovered_of_covRangeOk covSlice_6 (by omega) hc6
  else
  if hc7 : id < 4096 then
    exact idCovered_of_covRangeOk covSlice_7 (by omega) hc7
  else
  if hc8 : id < 4608 then
    exact idCovered_of_covRangeOk covSlice_8 (by omega) hc8
  else
  if hc9 : id < 5120 then
    exact idCovered_of_covRangeOk covSlice_9 (by omega) hc9
  else
  if hc10 : id < 5632 then
    exact idCovered_of_covRangeOk covSlice_10 (by omega) hc10
  else
  if hc11 : id < 6144 then
    exact idCovered_of_covRangeOk covSlice_11 (by omega) hc11
  else
  if hc12 : id < 6656 then
    exact idCovered_of_covRangeOk covSlice_12 (by omega) hc12
  else
    exact idCovered_of_covRangeOk covSlice_13 (by omega) hid

private theorem bktSlice_0 : bktRangeOk 0 64 = true := by decide +kernel
private theorem bktSlice_1 : bktRangeOk 64 64 = true := by decide +kernel
private theorem bktSlice_2 : bktRangeOk 128 64 = true := by decide +kernel
private theorem bktSlice_3 : bktRangeOk 192 59 = true := by decide +kernel

theorem bucket_collision_free : ∀ b < 251,
    bucketNoCollision (dagBucketEntries b) = true := by
  intro b hb
  if hb0 : b < 64 then
    exact bktOk_of_bktRangeOk bktSlice_0 (by omega) hb0
  else
  if hb1 : b < 128 then
    exact bktOk_of_bktRangeOk bktSlice_1 (by omega) hb1
  else
  if hb2 : b < 192 then
    exact bktOk_of_bktRangeOk bktSlice_2 (by omega) hb2
  else
    exact bktOk_of_bktRangeOk bktSlice_3 (by omega) hb

/-- Distinct nodes below `dagSize` cannot share `dagBytes` when at least one has `isAI = true`. -/
theorem dag_no_collision : ∀ id₁ < dagSize, ∀ id₂ < dagSize,
    ((dagOp id₁).isAI = true ∨ (dagOp id₂).isAI = true) →
    dagBytes id₁ = dagBytes id₂ → id₁ = id₂ := by
  intro id₁ h₁ id₂ h₂ hai hbs
  have hcov₁ := id_covered id₁ h₁
  have hcov₂ := id_covered id₂ h₂
  have hid₁ := List.mem_of_elem_eq_true hcov₁
  have hid₂ := List.mem_of_elem_eq_true hcov₂
  rw [← hbs] at hid₂
  let f := fun id : Nat => (id, (dagOp id).isAI, fastBytesKey (dagBytes id))
  have hmem₁ : f id₁ ∈ dagBucketEntries (fastBucketIdx (fastBytesKey (dagBytes id₁))) :=
    List.mem_map_of_mem hid₁
  have hmem₂' : f id₂ ∈ dagBucketEntries (fastBucketIdx (fastBytesKey (dagBytes id₁))) :=
    List.mem_map_of_mem hid₂
  have hmem₂ : (id₂, (dagOp id₂).isAI, fastBytesKey (dagBytes id₁)) ∈
      dagBucketEntries (fastBucketIdx (fastBytesKey (dagBytes id₁))) := by
    dsimp only [f] at hmem₂'; rwa [← hbs] at hmem₂'
  have hlt : fastBucketIdx (fastBytesKey (dagBytes id₁)) < 251 := Nat.mod_lt _ (by decide)
  have hb := bucket_collision_free (fastBucketIdx (fastBytesKey (dagBytes id₁))) hlt
  exact bucketNoCollision_sound hb hmem₁ hmem₂ hai

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagBuckets
