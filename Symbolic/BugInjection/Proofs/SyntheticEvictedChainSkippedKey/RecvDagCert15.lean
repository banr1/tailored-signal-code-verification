/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData

/-!
# Per-Node DAG Certificate Slice 15

Kernel-checked `dagNodeOk` certificates (`certRangeOk_15`) for receive-DAG nodes `5760 ≤ id < 6144`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert15

open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs (dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagOp dagBytes certRangeOk dagNodeOk_of_certRangeOk)

private theorem certSlice_15_0 : certRangeOk 5760 32 = true := by decide +kernel
private theorem certSlice_15_1 : certRangeOk 5792 32 = true := by decide +kernel
private theorem certSlice_15_2 : certRangeOk 5824 32 = true := by decide +kernel
private theorem certSlice_15_3 : certRangeOk 5856 32 = true := by decide +kernel
private theorem certSlice_15_4 : certRangeOk 5888 32 = true := by decide +kernel
private theorem certSlice_15_5 : certRangeOk 5920 32 = true := by decide +kernel
private theorem certSlice_15_6 : certRangeOk 5952 32 = true := by decide +kernel
private theorem certSlice_15_7 : certRangeOk 5984 32 = true := by decide +kernel
private theorem certSlice_15_8 : certRangeOk 6016 32 = true := by decide +kernel
private theorem certSlice_15_9 : certRangeOk 6048 32 = true := by decide +kernel
private theorem certSlice_15_10 : certRangeOk 6080 32 = true := by decide +kernel
private theorem certSlice_15_11 : certRangeOk 6112 32 = true := by decide +kernel

theorem certRangeOk_15 {id : Nat} (hlo : 5760 ≤ id) (hhi : id < 6144) :
    dagNodeOk dagOp dagBytes id = true := by
  if hs0 : id < 5792 then
    exact dagNodeOk_of_certRangeOk certSlice_15_0 (by omega) hs0
  else
  if hs1 : id < 5824 then
    exact dagNodeOk_of_certRangeOk certSlice_15_1 (by omega) hs1
  else
  if hs2 : id < 5856 then
    exact dagNodeOk_of_certRangeOk certSlice_15_2 (by omega) hs2
  else
  if hs3 : id < 5888 then
    exact dagNodeOk_of_certRangeOk certSlice_15_3 (by omega) hs3
  else
  if hs4 : id < 5920 then
    exact dagNodeOk_of_certRangeOk certSlice_15_4 (by omega) hs4
  else
  if hs5 : id < 5952 then
    exact dagNodeOk_of_certRangeOk certSlice_15_5 (by omega) hs5
  else
  if hs6 : id < 5984 then
    exact dagNodeOk_of_certRangeOk certSlice_15_6 (by omega) hs6
  else
  if hs7 : id < 6016 then
    exact dagNodeOk_of_certRangeOk certSlice_15_7 (by omega) hs7
  else
  if hs8 : id < 6048 then
    exact dagNodeOk_of_certRangeOk certSlice_15_8 (by omega) hs8
  else
  if hs9 : id < 6080 then
    exact dagNodeOk_of_certRangeOk certSlice_15_9 (by omega) hs9
  else
  if hs10 : id < 6112 then
    exact dagNodeOk_of_certRangeOk certSlice_15_10 (by omega) hs10
  else
    exact dagNodeOk_of_certRangeOk certSlice_15_11 (by omega) hhi

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert15
