/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagFastShaData0
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagFastShaData1

/-!
# Fast `BinTree` Evaluator for `evictedSha256` and `dagNodeOk`

Replaces integer-decoded bucket scans in `evictedSha256` with depth-6 `BinTree` byte-bucket lookup
(`fastEvictedSha256`, `dagNodeFastOk`) and proves pointwise equality with `dagNodeOk`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagFastSha

open ByteSpecs (ShaState hmacWith)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (sha256CompressFunction shaStateBytes shaStateOfBytes)
open DY.Libsignal.Composed.Refinement (leBytes)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
  (bytesToNat compTag4 compTag4Ipad compTag4Opad compDefaultSha256)
open Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
  (leBytes_bytesToNat bytesToNat_leBytes)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsShaRows
  (evictedSha256Bucket evictedSha256Rows evictedSha256)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0 (evictedI0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.ShaMacLaws (FE_eq)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagTree (BinTree btGet)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs
  (DagOp dagOpBytesOk dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagFastShaData0 (fastSubTree0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagFastShaData1 (fastSubTree1)

def fastShaTree : BinTree (List (HwBytes × HwBytes × HwBytes)) :=
  .branch fastSubTree0 fastSubTree1

def fastShaBucket (b : Nat) : List (HwBytes × HwBytes × HwBytes) :=
  (btGet 6 fastShaTree b).getD []

def fastBlkBucketIdx : HwBytes → Nat
  | [] => 0
  | b :: _ => b.toNat % 64

theorem fastBlkBucketIdx_eq (blk : HwBytes) : fastBlkBucketIdx blk = bytesToNat blk % 64 := by
  rcases blk with _ | ⟨b, bs⟩
  · rfl
  · simp [fastBlkBucketIdx, bytesToNat]; omega

def shaBucketSliceOk (lo count : Nat) : Bool :=
  (List.range count).all fun k =>
    let b := lo + k
    decide (fastShaBucket b = (evictedSha256Bucket b).map
      (fun r => (leBytes 32 r.1, leBytes 64 r.2.1, leBytes 32 r.2.2)))

private theorem shaBktSlice_0 : shaBucketSliceOk 0 16 = true := by decide +kernel
private theorem shaBktSlice_1 : shaBucketSliceOk 16 16 = true := by decide +kernel
private theorem shaBktSlice_2 : shaBucketSliceOk 32 16 = true := by decide +kernel
private theorem shaBktSlice_3 : shaBucketSliceOk 48 16 = true := by decide +kernel

private theorem fastShaBucket_of_slice {lo count : Nat} (h : shaBucketSliceOk lo count = true)
    {b : Nat} (hlo : lo ≤ b) (hhi : b < lo + count) :
    fastShaBucket b = (evictedSha256Bucket b).map
      (fun r => (leBytes 32 r.1, leBytes 64 r.2.1, leBytes 32 r.2.2)) := by
  unfold shaBucketSliceOk at h
  have hmem : b - lo ∈ List.range count := List.mem_range.mpr (by omega)
  have hk := List.all_eq_true.mp h (b - lo) hmem
  simp only [decide_eq_true_eq] at hk
  have heq : lo + (b - lo) = b := by omega
  rwa [heq] at hk

theorem fastShaBucket_eq (b : Nat) (hb : b < 64) :
    fastShaBucket b = (evictedSha256Bucket b).map
      (fun r => (leBytes 32 r.1, leBytes 64 r.2.1, leBytes 32 r.2.2)) := by
  if h0 : b < 16 then exact fastShaBucket_of_slice shaBktSlice_0 (by omega) h0
  else if h1 : b < 32 then exact fastShaBucket_of_slice shaBktSlice_1 (by omega) h1
  else if h2 : b < 48 then exact fastShaBucket_of_slice shaBktSlice_2 (by omega) h2
  else exact fastShaBucket_of_slice shaBktSlice_3 (by omega) hb

private theorem rows_in_bounds :
    (evictedSha256Rows.all fun r =>
      decide (r.1 < 2 ^ (8 * 32)) && decide (r.2.1 < 2 ^ (8 * 64))) = true := by
  decide +kernel

private theorem find?_congr_mem {α : Type} {p q : α → Bool} :
    ∀ {xs : List α}, (∀ x ∈ xs, p x = q x) → xs.find? p = xs.find? q
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.find?]
    rw [h x (.head _)]
    cases q x
    · exact find?_congr_mem (fun y hy => h y (.tail _ hy))
    · rfl

/-- Fast SHA-256 compression oracle lookup using `fastShaBucket`. -/
def fastEvictedSha256 (st blk : HwBytes) : HwBytes :=
  if st.take 4 == compTag4 || blk.take 4 == compTag4 ||
     blk.take 4 == compTag4Ipad || blk.take 4 == compTag4Opad then
    compDefaultSha256 st blk
  else if st.length == 32 && blk.length == 64 then
    match (fastShaBucket (fastBlkBucketIdx blk)).find? (fun r => r.1 == st && r.2.1 == blk) with
    | some (_, _, outBs) => outBs
    | none => compDefaultSha256 st blk
  else
    compDefaultSha256 st blk

theorem fastEvictedSha256_eq (st blk : HwBytes) :
    fastEvictedSha256 st blk = evictedSha256 st blk := by
  unfold fastEvictedSha256 evictedSha256
  split
  · rfl
  · split
    · rename_i htag hlen
      simp only [Bool.and_eq_true, beq_iff_eq] at hlen
      obtain ⟨hst, hblk⟩ := hlen
      dsimp only
      rw [fastBlkBucketIdx_eq]
      have hb : bytesToNat blk % 64 < 64 := Nat.mod_lt _ (by decide)
      rw [fastShaBucket_eq _ hb]
      let f : Nat × Nat × Nat → HwBytes × HwBytes × HwBytes :=
        fun r => (leBytes 32 r.1, leBytes 64 r.2.1, leBytes 32 r.2.2)
      let p : HwBytes × HwBytes × HwBytes → Bool :=
        fun r => r.1 == st && r.2.1 == blk
      let q : Nat × Nat × Nat → Bool :=
        fun r => r.1 == bytesToNat st && r.2.1 == bytesToNat blk
      change (match ((evictedSha256Bucket (bytesToNat blk % 64)).map f).find? p with
        | some (_, _, outBs) => outBs
        | none => compDefaultSha256 st blk) =
        (match (evictedSha256Bucket (bytesToNat blk % 64)).find? q with
        | some (_, _, outNat) => leBytes 32 outNat
        | none => compDefaultSha256 st blk)
      rw [List.find?_map]
      have hcongr : List.find? (p ∘ f) (evictedSha256Bucket (bytesToNat blk % 64)) =
          List.find? q (evictedSha256Bucket (bytesToNat blk % 64)) := by
        apply find?_congr_mem
        intro r hr
        have hmem : r ∈ evictedSha256Rows :=
          List.mem_flatMap.mpr ⟨bytesToNat blk % 64, List.mem_range.mpr hb, hr⟩
        have hbd := List.all_eq_true.mp rows_in_bounds r hmem
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hbd
        dsimp only [Function.comp_apply, f, p, q]
        have h1 : (leBytes 32 r.1 == st) = (r.1 == bytesToNat st) := by
          apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]; constructor
          · intro he; rw [← he, bytesToNat_leBytes 32 r.1 hbd.1]
          · intro he; rw [he, ← hst, leBytes_bytesToNat]
        have h2 : (leBytes 64 r.2.1 == blk) = (r.2.1 == bytesToNat blk) := by
          apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]; constructor
          · intro he; rw [← he, bytesToNat_leBytes 64 r.2.1 hbd.2]
          · intro he; rw [he, ← hblk, leBytes_bytesToNat]
        rw [h1, h2]
      rw [hcongr]
      cases List.find? q (evictedSha256Bucket (bytesToNat blk % 64)) with
      | none => rfl
      | some r => rfl
    · rfl

def fastCompress (s : ShaState) (b : HwBytes) : ShaState :=
  shaStateOfBytes (fastEvictedSha256 (shaStateBytes s) b)

theorem fastCompress_eq : fastCompress = sha256CompressFunction evictedI0 := by
  funext s b
  have hfe : sha256CompressFunction evictedI0 s b =
      shaStateOfBytes (evictedSha256 (shaStateBytes s) b) := FE_eq s b
  rw [hfe, ← fastEvictedSha256_eq]
  rfl

def dagOpBytesFastOk (bytesOf : Nat → HwBytes) (id : Nat) (op : DagOp) : Bool :=
  match op with
  | .kdf a b => bytesOf id == hmacWith fastCompress (bytesOf a) (bytesOf b)
  | _ => dagOpBytesOk bytesOf id op

theorem dagOpBytesFastOk_eq (bytesOf : Nat → HwBytes) (id : Nat) (op : DagOp) :
    dagOpBytesFastOk bytesOf id op = dagOpBytesOk bytesOf id op := by
  cases op <;> try rfl
  simp only [dagOpBytesFastOk, dagOpBytesOk, fastCompress_eq]

/-- Equivalent of `dagNodeOk` evaluating `.kdf` nodes via `fastCompress`. -/
def dagNodeFastOk (opOf : Nat → DagOp) (bytesOf : Nat → HwBytes) (id : Nat) : Bool :=
  let op := opOf id
  let v := bytesOf id
  op.childrenLt id &&
  decide (v.length < 2048) &&
  dagOpBytesFastOk bytesOf id op &&
  (!op.isAI || (decide (8 ≤ v.length) &&
    !(decide (38 ≤ v.length) && (v.drop (v.length - 2) == [0x01#8, 0x00#8]))))

theorem dagNodeFastOk_eq (opOf : Nat → DagOp) (bytesOf : Nat → HwBytes) (id : Nat) :
    dagNodeFastOk opOf bytesOf id = dagNodeOk opOf bytesOf id := by
  simp only [dagNodeFastOk, dagNodeOk, dagOpBytesFastOk_eq]

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagFastSha
