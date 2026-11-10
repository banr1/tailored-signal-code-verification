/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData

/-!
# Per-Node DAG Certificate Slice 1

Kernel-checked `dagNodeOk` certificates (`certRangeOk_1`) for receive-DAG nodes `384 ≤ id < 768`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert1

open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs (dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagOp dagBytes certRangeOk dagNodeOk_of_certRangeOk)

private theorem certSlice_1_0 : certRangeOk 384 32 = true := by decide +kernel
private theorem certSlice_1_1 : certRangeOk 416 32 = true := by decide +kernel
private theorem certSlice_1_2 : certRangeOk 448 32 = true := by decide +kernel
private theorem certSlice_1_3 : certRangeOk 480 32 = true := by decide +kernel
private theorem certSlice_1_4 : certRangeOk 512 32 = true := by decide +kernel
private theorem certSlice_1_5 : certRangeOk 544 32 = true := by decide +kernel
private theorem certSlice_1_6 : certRangeOk 576 32 = true := by decide +kernel
private theorem certSlice_1_7 : certRangeOk 608 32 = true := by decide +kernel
private theorem certSlice_1_8 : certRangeOk 640 32 = true := by decide +kernel
private theorem certSlice_1_9 : certRangeOk 672 32 = true := by decide +kernel
private theorem certSlice_1_10 : certRangeOk 704 32 = true := by decide +kernel
private theorem certSlice_1_11 : certRangeOk 736 32 = true := by decide +kernel

theorem certRangeOk_1 {id : Nat} (hlo : 384 ≤ id) (hhi : id < 768) :
    dagNodeOk dagOp dagBytes id = true := by
  if hs0 : id < 416 then
    exact dagNodeOk_of_certRangeOk certSlice_1_0 (by omega) hs0
  else
  if hs1 : id < 448 then
    exact dagNodeOk_of_certRangeOk certSlice_1_1 (by omega) hs1
  else
  if hs2 : id < 480 then
    exact dagNodeOk_of_certRangeOk certSlice_1_2 (by omega) hs2
  else
  if hs3 : id < 512 then
    exact dagNodeOk_of_certRangeOk certSlice_1_3 (by omega) hs3
  else
  if hs4 : id < 544 then
    exact dagNodeOk_of_certRangeOk certSlice_1_4 (by omega) hs4
  else
  if hs5 : id < 576 then
    exact dagNodeOk_of_certRangeOk certSlice_1_5 (by omega) hs5
  else
  if hs6 : id < 608 then
    exact dagNodeOk_of_certRangeOk certSlice_1_6 (by omega) hs6
  else
  if hs7 : id < 640 then
    exact dagNodeOk_of_certRangeOk certSlice_1_7 (by omega) hs7
  else
  if hs8 : id < 672 then
    exact dagNodeOk_of_certRangeOk certSlice_1_8 (by omega) hs8
  else
  if hs9 : id < 704 then
    exact dagNodeOk_of_certRangeOk certSlice_1_9 (by omega) hs9
  else
  if hs10 : id < 736 then
    exact dagNodeOk_of_certRangeOk certSlice_1_10 (by omega) hs10
  else
    exact dagNodeOk_of_certRangeOk certSlice_1_11 (by omega) hhi

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert1
