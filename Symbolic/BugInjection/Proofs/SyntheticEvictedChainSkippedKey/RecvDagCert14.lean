/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData

/-!
# Per-Node DAG Certificate Slice 14

Kernel-checked `dagNodeOk` certificates (`certRangeOk_14`) for receive-DAG nodes `5376 ≤ id < 5760`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert14

open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs (dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagOp dagBytes certRangeOk dagNodeOk_of_certRangeOk)

private theorem certSlice_14_0 : certRangeOk 5376 32 = true := by decide +kernel
private theorem certSlice_14_1 : certRangeOk 5408 32 = true := by decide +kernel
private theorem certSlice_14_2 : certRangeOk 5440 32 = true := by decide +kernel
private theorem certSlice_14_3 : certRangeOk 5472 32 = true := by decide +kernel
private theorem certSlice_14_4 : certRangeOk 5504 32 = true := by decide +kernel
private theorem certSlice_14_5 : certRangeOk 5536 32 = true := by decide +kernel
private theorem certSlice_14_6 : certRangeOk 5568 32 = true := by decide +kernel
private theorem certSlice_14_7 : certRangeOk 5600 32 = true := by decide +kernel
private theorem certSlice_14_8 : certRangeOk 5632 32 = true := by decide +kernel
private theorem certSlice_14_9 : certRangeOk 5664 32 = true := by decide +kernel
private theorem certSlice_14_10 : certRangeOk 5696 32 = true := by decide +kernel
private theorem certSlice_14_11 : certRangeOk 5728 32 = true := by decide +kernel

theorem certRangeOk_14 {id : Nat} (hlo : 5376 ≤ id) (hhi : id < 5760) :
    dagNodeOk dagOp dagBytes id = true := by
  if hs0 : id < 5408 then
    exact dagNodeOk_of_certRangeOk certSlice_14_0 (by omega) hs0
  else
  if hs1 : id < 5440 then
    exact dagNodeOk_of_certRangeOk certSlice_14_1 (by omega) hs1
  else
  if hs2 : id < 5472 then
    exact dagNodeOk_of_certRangeOk certSlice_14_2 (by omega) hs2
  else
  if hs3 : id < 5504 then
    exact dagNodeOk_of_certRangeOk certSlice_14_3 (by omega) hs3
  else
  if hs4 : id < 5536 then
    exact dagNodeOk_of_certRangeOk certSlice_14_4 (by omega) hs4
  else
  if hs5 : id < 5568 then
    exact dagNodeOk_of_certRangeOk certSlice_14_5 (by omega) hs5
  else
  if hs6 : id < 5600 then
    exact dagNodeOk_of_certRangeOk certSlice_14_6 (by omega) hs6
  else
  if hs7 : id < 5632 then
    exact dagNodeOk_of_certRangeOk certSlice_14_7 (by omega) hs7
  else
  if hs8 : id < 5664 then
    exact dagNodeOk_of_certRangeOk certSlice_14_8 (by omega) hs8
  else
  if hs9 : id < 5696 then
    exact dagNodeOk_of_certRangeOk certSlice_14_9 (by omega) hs9
  else
  if hs10 : id < 5728 then
    exact dagNodeOk_of_certRangeOk certSlice_14_10 (by omega) hs10
  else
    exact dagNodeOk_of_certRangeOk certSlice_14_11 (by omega) hhi

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert14
