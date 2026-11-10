/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagFastSha
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagTree
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData0
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData1
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData2
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData3
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData4
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData5
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData6
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData7
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData8
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData9
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData10
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData11
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData12
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData13
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData14
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData15
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData16
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData17
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData18
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData19
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData20
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData21
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData22
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData23
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData24
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData25
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData26
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData27
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData28
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData29
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData30
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData31

/-! # Concrete DAG Dispatch and Named Node IDs

Combines the 32 low-bit `BinTree` stripes into `dagTree`, defines `dagOp` and `dagBytes` node
lookup together with `certRangeOk` range checks, and names root and protocol node IDs. -/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData

open DY.Libsignal (HwBytes)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (bytesToNat)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs
  (DagOp dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagFastSha
  (dagNodeFastOk dagNodeFastOk_eq)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagTree (BinTree btGet)

def dagSize : Nat := 6720

def dagTree : BinTree (DagOp × HwBytes) :=
  .branch (.branch (.branch (.branch (.branch (RecvDagData0.subTree0) (RecvDagData16.subTree16)) (.branch (RecvDagData8.subTree8) (RecvDagData24.subTree24))) (.branch (.branch (RecvDagData4.subTree4) (RecvDagData20.subTree20)) (.branch (RecvDagData12.subTree12) (RecvDagData28.subTree28)))) (.branch (.branch (.branch (RecvDagData2.subTree2) (RecvDagData18.subTree18)) (.branch (RecvDagData10.subTree10) (RecvDagData26.subTree26))) (.branch (.branch (RecvDagData6.subTree6) (RecvDagData22.subTree22)) (.branch (RecvDagData14.subTree14) (RecvDagData30.subTree30))))) (.branch (.branch (.branch (.branch (RecvDagData1.subTree1) (RecvDagData17.subTree17)) (.branch (RecvDagData9.subTree9) (RecvDagData25.subTree25))) (.branch (.branch (RecvDagData5.subTree5) (RecvDagData21.subTree21)) (.branch (RecvDagData13.subTree13) (RecvDagData29.subTree29)))) (.branch (.branch (.branch (RecvDagData3.subTree3) (RecvDagData19.subTree19)) (.branch (RecvDagData11.subTree11) (RecvDagData27.subTree27))) (.branch (.branch (RecvDagData7.subTree7) (RecvDagData23.subTree23)) (.branch (RecvDagData15.subTree15) (RecvDagData31.subTree31)))))

def dagOp (id : Nat) : DagOp :=
  match btGet 13 dagTree id with
  | some p => p.1
  | none => .lit []

def dagBytes (id : Nat) : HwBytes :=
  match btGet 13 dagTree id with
  | some p => p.2
  | none => []

/-- 64-byte prefix hash key, collision-free on `isAI` nodes in `dagTree`. -/
def fastBytesKey (bs : HwBytes) : Nat :=
  bs.length + 2048 * bytesToNat (bs.take 64)

def fastBucketIdx (hk : Nat) : Nat := hk % 251

def certRangeOk (lo count : Nat) : Bool :=
  (List.range count).all fun k => dagNodeFastOk dagOp dagBytes (lo + k)

theorem dagNodeOk_of_certRangeOk {lo count : Nat} (h : certRangeOk lo count = true)
    {i : Nat} (hlo : lo ≤ i) (hhi : i < lo + count) :
    dagNodeOk dagOp dagBytes i = true := by
  unfold certRangeOk at h
  have hmem : i - lo ∈ List.range count := List.mem_range.mpr (by omega)
  have hk := List.all_eq_true.mp h (i - lo) hmem
  have heq : lo + (i - lo) = i := by omega
  rw [heq, dagNodeFastOk_eq] at hk
  exact hk

def emptyId : Nat := 0
def b00Id : Nat := 1
def b01Id : Nat := 2
def b02Id : Nat := 3
def b03Id : Nat := 4
def b05Id : Nat := 5
def b08Id : Nat := 6
def ff32Id : Nat := 7
def zero32Id : Nat := 8
def wrLblId : Nat := 10
def wmkLblId : Nat := 11
def pqxdhLblId : Nat := 12
def wmkInfo1Id : Nat := 13
def wmkInfo2Id : Nat := 14
def wmkInfo3Id : Nat := 15
def wrInfo1Id : Nat := 16
def wrInfo2Id : Nat := 17
def pqxdhInfo1Id : Nat := 18
def pqxdhInfo2Id : Nat := 19
def pqxdhInfo3Id : Nat := 20
def sk0Id : Nat := 21
def sk1Id : Nat := 22
def sk2Id : Nat := 23
def pqskId : Nat := 25
def pk0Id : Nat := 27
def pk1Id : Nat := 28
def pk2Id : Nat := 29
def sk3Id : Nat := 65
def kemEntId : Nat := 66
def sk4Id : Nat := 67
def pk3Id : Nat := 68
def pk4Id : Nat := 69
def ik0SerId : Nat := 30
def ik1SerId : Nat := 31
def spkSerId : Nat := 32
def ek0SerId : Nat := 70
def pqpkId : Nat := 71
def pqpkSerId : Nat := 72
def kctId : Nat := 73
def kssId : Nat := 74
def rkInitId : Nat := 83
def ckInitId : Nat := 85
def pqrId : Nat := 87
def sidSessionId : Nat := 88
def rkAId : Nat := 93
def cksAId : Nat := 95
def honestSaltIds : List Nat := [8, 100, 120, 165, 258, 414, 649, 979, 1420, 1988, 2699, 3569, 4614]
def pqSecretRootIds : List Nat := [42, 50, 57, 64]

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
