/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData

/-!
# Per-Node DAG Certificate Slice 2

Kernel-checked `dagNodeOk` certificates (`certRangeOk_2`) for receive-DAG nodes `768 ≤ id < 1152`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert2

open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs (dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagOp dagBytes certRangeOk dagNodeOk_of_certRangeOk)

private theorem certSlice_2_0 : certRangeOk 768 32 = true := by decide +kernel
private theorem certSlice_2_1 : certRangeOk 800 32 = true := by decide +kernel
private theorem certSlice_2_2 : certRangeOk 832 32 = true := by decide +kernel
private theorem certSlice_2_3 : certRangeOk 864 32 = true := by decide +kernel
private theorem certSlice_2_4 : certRangeOk 896 32 = true := by decide +kernel
private theorem certSlice_2_5 : certRangeOk 928 32 = true := by decide +kernel
private theorem certSlice_2_6 : certRangeOk 960 32 = true := by decide +kernel
private theorem certSlice_2_7 : certRangeOk 992 32 = true := by decide +kernel
private theorem certSlice_2_8 : certRangeOk 1024 32 = true := by decide +kernel
private theorem certSlice_2_9 : certRangeOk 1056 32 = true := by decide +kernel
private theorem certSlice_2_10 : certRangeOk 1088 32 = true := by decide +kernel
private theorem certSlice_2_11 : certRangeOk 1120 32 = true := by decide +kernel

theorem certRangeOk_2 {id : Nat} (hlo : 768 ≤ id) (hhi : id < 1152) :
    dagNodeOk dagOp dagBytes id = true := by
  if hs0 : id < 800 then
    exact dagNodeOk_of_certRangeOk certSlice_2_0 (by omega) hs0
  else
  if hs1 : id < 832 then
    exact dagNodeOk_of_certRangeOk certSlice_2_1 (by omega) hs1
  else
  if hs2 : id < 864 then
    exact dagNodeOk_of_certRangeOk certSlice_2_2 (by omega) hs2
  else
  if hs3 : id < 896 then
    exact dagNodeOk_of_certRangeOk certSlice_2_3 (by omega) hs3
  else
  if hs4 : id < 928 then
    exact dagNodeOk_of_certRangeOk certSlice_2_4 (by omega) hs4
  else
  if hs5 : id < 960 then
    exact dagNodeOk_of_certRangeOk certSlice_2_5 (by omega) hs5
  else
  if hs6 : id < 992 then
    exact dagNodeOk_of_certRangeOk certSlice_2_6 (by omega) hs6
  else
  if hs7 : id < 1024 then
    exact dagNodeOk_of_certRangeOk certSlice_2_7 (by omega) hs7
  else
  if hs8 : id < 1056 then
    exact dagNodeOk_of_certRangeOk certSlice_2_8 (by omega) hs8
  else
  if hs9 : id < 1088 then
    exact dagNodeOk_of_certRangeOk certSlice_2_9 (by omega) hs9
  else
  if hs10 : id < 1120 then
    exact dagNodeOk_of_certRangeOk certSlice_2_10 (by omega) hs10
  else
    exact dagNodeOk_of_certRangeOk certSlice_2_11 (by omega) hhi

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert2
