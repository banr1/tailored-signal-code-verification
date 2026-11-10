/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData

/-!
# Per-Node DAG Certificate Slice 11

Kernel-checked `dagNodeOk` certificates (`certRangeOk_11`) for receive-DAG nodes `4224 ≤ id < 4608`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert11

open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs (dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagOp dagBytes certRangeOk dagNodeOk_of_certRangeOk)

private theorem certSlice_11_0 : certRangeOk 4224 32 = true := by decide +kernel
private theorem certSlice_11_1 : certRangeOk 4256 32 = true := by decide +kernel
private theorem certSlice_11_2 : certRangeOk 4288 32 = true := by decide +kernel
private theorem certSlice_11_3 : certRangeOk 4320 32 = true := by decide +kernel
private theorem certSlice_11_4 : certRangeOk 4352 32 = true := by decide +kernel
private theorem certSlice_11_5 : certRangeOk 4384 32 = true := by decide +kernel
private theorem certSlice_11_6 : certRangeOk 4416 32 = true := by decide +kernel
private theorem certSlice_11_7 : certRangeOk 4448 32 = true := by decide +kernel
private theorem certSlice_11_8 : certRangeOk 4480 32 = true := by decide +kernel
private theorem certSlice_11_9 : certRangeOk 4512 32 = true := by decide +kernel
private theorem certSlice_11_10 : certRangeOk 4544 32 = true := by decide +kernel
private theorem certSlice_11_11 : certRangeOk 4576 32 = true := by decide +kernel

theorem certRangeOk_11 {id : Nat} (hlo : 4224 ≤ id) (hhi : id < 4608) :
    dagNodeOk dagOp dagBytes id = true := by
  if hs0 : id < 4256 then
    exact dagNodeOk_of_certRangeOk certSlice_11_0 (by omega) hs0
  else
  if hs1 : id < 4288 then
    exact dagNodeOk_of_certRangeOk certSlice_11_1 (by omega) hs1
  else
  if hs2 : id < 4320 then
    exact dagNodeOk_of_certRangeOk certSlice_11_2 (by omega) hs2
  else
  if hs3 : id < 4352 then
    exact dagNodeOk_of_certRangeOk certSlice_11_3 (by omega) hs3
  else
  if hs4 : id < 4384 then
    exact dagNodeOk_of_certRangeOk certSlice_11_4 (by omega) hs4
  else
  if hs5 : id < 4416 then
    exact dagNodeOk_of_certRangeOk certSlice_11_5 (by omega) hs5
  else
  if hs6 : id < 4448 then
    exact dagNodeOk_of_certRangeOk certSlice_11_6 (by omega) hs6
  else
  if hs7 : id < 4480 then
    exact dagNodeOk_of_certRangeOk certSlice_11_7 (by omega) hs7
  else
  if hs8 : id < 4512 then
    exact dagNodeOk_of_certRangeOk certSlice_11_8 (by omega) hs8
  else
  if hs9 : id < 4544 then
    exact dagNodeOk_of_certRangeOk certSlice_11_9 (by omega) hs9
  else
  if hs10 : id < 4576 then
    exact dagNodeOk_of_certRangeOk certSlice_11_10 (by omega) hs10
  else
    exact dagNodeOk_of_certRangeOk certSlice_11_11 (by omega) hhi

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert11
