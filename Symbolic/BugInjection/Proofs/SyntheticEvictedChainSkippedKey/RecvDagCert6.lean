/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData

/-! # Per-Node DAG Certificate Slice 6

Proves `dagNodeOk dagOp dagBytes id = true` for `2304 ≤ id < 2688` (`certRangeOk_6`) via
32-node kernel-checked slices. -/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert6

open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs (dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagOp dagBytes certRangeOk dagNodeOk_of_certRangeOk)

private theorem certSlice_6_0 : certRangeOk 2304 32 = true := by decide +kernel
private theorem certSlice_6_1 : certRangeOk 2336 32 = true := by decide +kernel
private theorem certSlice_6_2 : certRangeOk 2368 32 = true := by decide +kernel
private theorem certSlice_6_3 : certRangeOk 2400 32 = true := by decide +kernel
private theorem certSlice_6_4 : certRangeOk 2432 32 = true := by decide +kernel
private theorem certSlice_6_5 : certRangeOk 2464 32 = true := by decide +kernel
private theorem certSlice_6_6 : certRangeOk 2496 32 = true := by decide +kernel
private theorem certSlice_6_7 : certRangeOk 2528 32 = true := by decide +kernel
private theorem certSlice_6_8 : certRangeOk 2560 32 = true := by decide +kernel
private theorem certSlice_6_9 : certRangeOk 2592 32 = true := by decide +kernel
private theorem certSlice_6_10 : certRangeOk 2624 32 = true := by decide +kernel
private theorem certSlice_6_11 : certRangeOk 2656 32 = true := by decide +kernel

theorem certRangeOk_6 {id : Nat} (hlo : 2304 ≤ id) (hhi : id < 2688) :
    dagNodeOk dagOp dagBytes id = true := by
  if hs0 : id < 2336 then
    exact dagNodeOk_of_certRangeOk certSlice_6_0 (by omega) hs0
  else
  if hs1 : id < 2368 then
    exact dagNodeOk_of_certRangeOk certSlice_6_1 (by omega) hs1
  else
  if hs2 : id < 2400 then
    exact dagNodeOk_of_certRangeOk certSlice_6_2 (by omega) hs2
  else
  if hs3 : id < 2432 then
    exact dagNodeOk_of_certRangeOk certSlice_6_3 (by omega) hs3
  else
  if hs4 : id < 2464 then
    exact dagNodeOk_of_certRangeOk certSlice_6_4 (by omega) hs4
  else
  if hs5 : id < 2496 then
    exact dagNodeOk_of_certRangeOk certSlice_6_5 (by omega) hs5
  else
  if hs6 : id < 2528 then
    exact dagNodeOk_of_certRangeOk certSlice_6_6 (by omega) hs6
  else
  if hs7 : id < 2560 then
    exact dagNodeOk_of_certRangeOk certSlice_6_7 (by omega) hs7
  else
  if hs8 : id < 2592 then
    exact dagNodeOk_of_certRangeOk certSlice_6_8 (by omega) hs8
  else
  if hs9 : id < 2624 then
    exact dagNodeOk_of_certRangeOk certSlice_6_9 (by omega) hs9
  else
  if hs10 : id < 2656 then
    exact dagNodeOk_of_certRangeOk certSlice_6_10 (by omega) hs10
  else
    exact dagNodeOk_of_certRangeOk certSlice_6_11 (by omega) hhi

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert6
