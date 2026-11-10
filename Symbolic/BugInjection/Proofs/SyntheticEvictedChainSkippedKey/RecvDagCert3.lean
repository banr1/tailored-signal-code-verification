/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData

/-!
# Per-Node DAG Certificate Slice 3

Kernel-checked `dagNodeOk` certificates (`certRangeOk_3`) for receive-DAG nodes `1152 ≤ id < 1536`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert3

open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs (dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagOp dagBytes certRangeOk dagNodeOk_of_certRangeOk)

private theorem certSlice_3_0 : certRangeOk 1152 32 = true := by decide +kernel
private theorem certSlice_3_1 : certRangeOk 1184 32 = true := by decide +kernel
private theorem certSlice_3_2 : certRangeOk 1216 32 = true := by decide +kernel
private theorem certSlice_3_3 : certRangeOk 1248 32 = true := by decide +kernel
private theorem certSlice_3_4 : certRangeOk 1280 32 = true := by decide +kernel
private theorem certSlice_3_5 : certRangeOk 1312 32 = true := by decide +kernel
private theorem certSlice_3_6 : certRangeOk 1344 32 = true := by decide +kernel
private theorem certSlice_3_7 : certRangeOk 1376 32 = true := by decide +kernel
private theorem certSlice_3_8 : certRangeOk 1408 32 = true := by decide +kernel
private theorem certSlice_3_9 : certRangeOk 1440 32 = true := by decide +kernel
private theorem certSlice_3_10 : certRangeOk 1472 32 = true := by decide +kernel
private theorem certSlice_3_11 : certRangeOk 1504 32 = true := by decide +kernel

theorem certRangeOk_3 {id : Nat} (hlo : 1152 ≤ id) (hhi : id < 1536) :
    dagNodeOk dagOp dagBytes id = true := by
  if hs0 : id < 1184 then
    exact dagNodeOk_of_certRangeOk certSlice_3_0 (by omega) hs0
  else
  if hs1 : id < 1216 then
    exact dagNodeOk_of_certRangeOk certSlice_3_1 (by omega) hs1
  else
  if hs2 : id < 1248 then
    exact dagNodeOk_of_certRangeOk certSlice_3_2 (by omega) hs2
  else
  if hs3 : id < 1280 then
    exact dagNodeOk_of_certRangeOk certSlice_3_3 (by omega) hs3
  else
  if hs4 : id < 1312 then
    exact dagNodeOk_of_certRangeOk certSlice_3_4 (by omega) hs4
  else
  if hs5 : id < 1344 then
    exact dagNodeOk_of_certRangeOk certSlice_3_5 (by omega) hs5
  else
  if hs6 : id < 1376 then
    exact dagNodeOk_of_certRangeOk certSlice_3_6 (by omega) hs6
  else
  if hs7 : id < 1408 then
    exact dagNodeOk_of_certRangeOk certSlice_3_7 (by omega) hs7
  else
  if hs8 : id < 1440 then
    exact dagNodeOk_of_certRangeOk certSlice_3_8 (by omega) hs8
  else
  if hs9 : id < 1472 then
    exact dagNodeOk_of_certRangeOk certSlice_3_9 (by omega) hs9
  else
  if hs10 : id < 1504 then
    exact dagNodeOk_of_certRangeOk certSlice_3_10 (by omega) hs10
  else
    exact dagNodeOk_of_certRangeOk certSlice_3_11 (by omega) hhi

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert3
