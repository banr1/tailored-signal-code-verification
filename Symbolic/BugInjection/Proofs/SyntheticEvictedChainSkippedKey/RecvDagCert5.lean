/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData

/-!
# Per-Node DAG Certificate Slice 5

Kernel-checked `dagNodeOk` certificates (`certRangeOk_5`) for receive-DAG nodes `1920 ≤ id < 2304`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert5

open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs (dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagOp dagBytes certRangeOk dagNodeOk_of_certRangeOk)

private theorem certSlice_5_0 : certRangeOk 1920 32 = true := by decide +kernel
private theorem certSlice_5_1 : certRangeOk 1952 32 = true := by decide +kernel
private theorem certSlice_5_2 : certRangeOk 1984 32 = true := by decide +kernel
private theorem certSlice_5_3 : certRangeOk 2016 32 = true := by decide +kernel
private theorem certSlice_5_4 : certRangeOk 2048 32 = true := by decide +kernel
private theorem certSlice_5_5 : certRangeOk 2080 32 = true := by decide +kernel
private theorem certSlice_5_6 : certRangeOk 2112 32 = true := by decide +kernel
private theorem certSlice_5_7 : certRangeOk 2144 32 = true := by decide +kernel
private theorem certSlice_5_8 : certRangeOk 2176 32 = true := by decide +kernel
private theorem certSlice_5_9 : certRangeOk 2208 32 = true := by decide +kernel
private theorem certSlice_5_10 : certRangeOk 2240 32 = true := by decide +kernel
private theorem certSlice_5_11 : certRangeOk 2272 32 = true := by decide +kernel

theorem certRangeOk_5 {id : Nat} (hlo : 1920 ≤ id) (hhi : id < 2304) :
    dagNodeOk dagOp dagBytes id = true := by
  if hs0 : id < 1952 then
    exact dagNodeOk_of_certRangeOk certSlice_5_0 (by omega) hs0
  else
  if hs1 : id < 1984 then
    exact dagNodeOk_of_certRangeOk certSlice_5_1 (by omega) hs1
  else
  if hs2 : id < 2016 then
    exact dagNodeOk_of_certRangeOk certSlice_5_2 (by omega) hs2
  else
  if hs3 : id < 2048 then
    exact dagNodeOk_of_certRangeOk certSlice_5_3 (by omega) hs3
  else
  if hs4 : id < 2080 then
    exact dagNodeOk_of_certRangeOk certSlice_5_4 (by omega) hs4
  else
  if hs5 : id < 2112 then
    exact dagNodeOk_of_certRangeOk certSlice_5_5 (by omega) hs5
  else
  if hs6 : id < 2144 then
    exact dagNodeOk_of_certRangeOk certSlice_5_6 (by omega) hs6
  else
  if hs7 : id < 2176 then
    exact dagNodeOk_of_certRangeOk certSlice_5_7 (by omega) hs7
  else
  if hs8 : id < 2208 then
    exact dagNodeOk_of_certRangeOk certSlice_5_8 (by omega) hs8
  else
  if hs9 : id < 2240 then
    exact dagNodeOk_of_certRangeOk certSlice_5_9 (by omega) hs9
  else
  if hs10 : id < 2272 then
    exact dagNodeOk_of_certRangeOk certSlice_5_10 (by omega) hs10
  else
    exact dagNodeOk_of_certRangeOk certSlice_5_11 (by omega) hhi

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert5
