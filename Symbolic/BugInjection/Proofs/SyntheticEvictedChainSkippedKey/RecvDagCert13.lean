/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData

/-!
# Per-Node DAG Certificate Slice 13

Kernel-checked `dagNodeOk` certificates (`certRangeOk_13`) for receive-DAG nodes `4992 ≤ id < 5376`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert13

open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs (dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagOp dagBytes certRangeOk dagNodeOk_of_certRangeOk)

private theorem certSlice_13_0 : certRangeOk 4992 32 = true := by decide +kernel
private theorem certSlice_13_1 : certRangeOk 5024 32 = true := by decide +kernel
private theorem certSlice_13_2 : certRangeOk 5056 32 = true := by decide +kernel
private theorem certSlice_13_3 : certRangeOk 5088 32 = true := by decide +kernel
private theorem certSlice_13_4 : certRangeOk 5120 32 = true := by decide +kernel
private theorem certSlice_13_5 : certRangeOk 5152 32 = true := by decide +kernel
private theorem certSlice_13_6 : certRangeOk 5184 32 = true := by decide +kernel
private theorem certSlice_13_7 : certRangeOk 5216 32 = true := by decide +kernel
private theorem certSlice_13_8 : certRangeOk 5248 32 = true := by decide +kernel
private theorem certSlice_13_9 : certRangeOk 5280 32 = true := by decide +kernel
private theorem certSlice_13_10 : certRangeOk 5312 32 = true := by decide +kernel
private theorem certSlice_13_11 : certRangeOk 5344 32 = true := by decide +kernel

theorem certRangeOk_13 {id : Nat} (hlo : 4992 ≤ id) (hhi : id < 5376) :
    dagNodeOk dagOp dagBytes id = true := by
  if hs0 : id < 5024 then
    exact dagNodeOk_of_certRangeOk certSlice_13_0 (by omega) hs0
  else
  if hs1 : id < 5056 then
    exact dagNodeOk_of_certRangeOk certSlice_13_1 (by omega) hs1
  else
  if hs2 : id < 5088 then
    exact dagNodeOk_of_certRangeOk certSlice_13_2 (by omega) hs2
  else
  if hs3 : id < 5120 then
    exact dagNodeOk_of_certRangeOk certSlice_13_3 (by omega) hs3
  else
  if hs4 : id < 5152 then
    exact dagNodeOk_of_certRangeOk certSlice_13_4 (by omega) hs4
  else
  if hs5 : id < 5184 then
    exact dagNodeOk_of_certRangeOk certSlice_13_5 (by omega) hs5
  else
  if hs6 : id < 5216 then
    exact dagNodeOk_of_certRangeOk certSlice_13_6 (by omega) hs6
  else
  if hs7 : id < 5248 then
    exact dagNodeOk_of_certRangeOk certSlice_13_7 (by omega) hs7
  else
  if hs8 : id < 5280 then
    exact dagNodeOk_of_certRangeOk certSlice_13_8 (by omega) hs8
  else
  if hs9 : id < 5312 then
    exact dagNodeOk_of_certRangeOk certSlice_13_9 (by omega) hs9
  else
  if hs10 : id < 5344 then
    exact dagNodeOk_of_certRangeOk certSlice_13_10 (by omega) hs10
  else
    exact dagNodeOk_of_certRangeOk certSlice_13_11 (by omega) hhi

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert13
