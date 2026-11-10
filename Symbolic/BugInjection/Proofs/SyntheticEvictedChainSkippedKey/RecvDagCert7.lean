/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData

/-! # Per-Node DAG Certificate Slice 7

Proves `dagNodeOk dagOp dagBytes id = true` for `2688 ≤ id < 3072` (`certRangeOk_7`) via
32-node kernel-checked slices. -/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert7

open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs (dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagOp dagBytes certRangeOk dagNodeOk_of_certRangeOk)

private theorem certSlice_7_0 : certRangeOk 2688 32 = true := by decide +kernel
private theorem certSlice_7_1 : certRangeOk 2720 32 = true := by decide +kernel
private theorem certSlice_7_2 : certRangeOk 2752 32 = true := by decide +kernel
private theorem certSlice_7_3 : certRangeOk 2784 32 = true := by decide +kernel
private theorem certSlice_7_4 : certRangeOk 2816 32 = true := by decide +kernel
private theorem certSlice_7_5 : certRangeOk 2848 32 = true := by decide +kernel
private theorem certSlice_7_6 : certRangeOk 2880 32 = true := by decide +kernel
private theorem certSlice_7_7 : certRangeOk 2912 32 = true := by decide +kernel
private theorem certSlice_7_8 : certRangeOk 2944 32 = true := by decide +kernel
private theorem certSlice_7_9 : certRangeOk 2976 32 = true := by decide +kernel
private theorem certSlice_7_10 : certRangeOk 3008 32 = true := by decide +kernel
private theorem certSlice_7_11 : certRangeOk 3040 32 = true := by decide +kernel

theorem certRangeOk_7 {id : Nat} (hlo : 2688 ≤ id) (hhi : id < 3072) :
    dagNodeOk dagOp dagBytes id = true := by
  if hs0 : id < 2720 then
    exact dagNodeOk_of_certRangeOk certSlice_7_0 (by omega) hs0
  else
  if hs1 : id < 2752 then
    exact dagNodeOk_of_certRangeOk certSlice_7_1 (by omega) hs1
  else
  if hs2 : id < 2784 then
    exact dagNodeOk_of_certRangeOk certSlice_7_2 (by omega) hs2
  else
  if hs3 : id < 2816 then
    exact dagNodeOk_of_certRangeOk certSlice_7_3 (by omega) hs3
  else
  if hs4 : id < 2848 then
    exact dagNodeOk_of_certRangeOk certSlice_7_4 (by omega) hs4
  else
  if hs5 : id < 2880 then
    exact dagNodeOk_of_certRangeOk certSlice_7_5 (by omega) hs5
  else
  if hs6 : id < 2912 then
    exact dagNodeOk_of_certRangeOk certSlice_7_6 (by omega) hs6
  else
  if hs7 : id < 2944 then
    exact dagNodeOk_of_certRangeOk certSlice_7_7 (by omega) hs7
  else
  if hs8 : id < 2976 then
    exact dagNodeOk_of_certRangeOk certSlice_7_8 (by omega) hs8
  else
  if hs9 : id < 3008 then
    exact dagNodeOk_of_certRangeOk certSlice_7_9 (by omega) hs9
  else
  if hs10 : id < 3040 then
    exact dagNodeOk_of_certRangeOk certSlice_7_10 (by omega) hs10
  else
    exact dagNodeOk_of_certRangeOk certSlice_7_11 (by omega) hhi

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert7
