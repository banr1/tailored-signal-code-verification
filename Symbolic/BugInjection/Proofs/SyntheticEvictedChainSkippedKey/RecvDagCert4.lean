/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData

/-!
# Per-Node DAG Certificate Slice 4

Kernel-checked `dagNodeOk` certificates (`certRangeOk_4`) for receive-DAG nodes `1536 ≤ id < 1920`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert4

open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs (dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagOp dagBytes certRangeOk dagNodeOk_of_certRangeOk)

private theorem certSlice_4_0 : certRangeOk 1536 32 = true := by decide +kernel
private theorem certSlice_4_1 : certRangeOk 1568 32 = true := by decide +kernel
private theorem certSlice_4_2 : certRangeOk 1600 32 = true := by decide +kernel
private theorem certSlice_4_3 : certRangeOk 1632 32 = true := by decide +kernel
private theorem certSlice_4_4 : certRangeOk 1664 32 = true := by decide +kernel
private theorem certSlice_4_5 : certRangeOk 1696 32 = true := by decide +kernel
private theorem certSlice_4_6 : certRangeOk 1728 32 = true := by decide +kernel
private theorem certSlice_4_7 : certRangeOk 1760 32 = true := by decide +kernel
private theorem certSlice_4_8 : certRangeOk 1792 32 = true := by decide +kernel
private theorem certSlice_4_9 : certRangeOk 1824 32 = true := by decide +kernel
private theorem certSlice_4_10 : certRangeOk 1856 32 = true := by decide +kernel
private theorem certSlice_4_11 : certRangeOk 1888 32 = true := by decide +kernel

theorem certRangeOk_4 {id : Nat} (hlo : 1536 ≤ id) (hhi : id < 1920) :
    dagNodeOk dagOp dagBytes id = true := by
  if hs0 : id < 1568 then
    exact dagNodeOk_of_certRangeOk certSlice_4_0 (by omega) hs0
  else
  if hs1 : id < 1600 then
    exact dagNodeOk_of_certRangeOk certSlice_4_1 (by omega) hs1
  else
  if hs2 : id < 1632 then
    exact dagNodeOk_of_certRangeOk certSlice_4_2 (by omega) hs2
  else
  if hs3 : id < 1664 then
    exact dagNodeOk_of_certRangeOk certSlice_4_3 (by omega) hs3
  else
  if hs4 : id < 1696 then
    exact dagNodeOk_of_certRangeOk certSlice_4_4 (by omega) hs4
  else
  if hs5 : id < 1728 then
    exact dagNodeOk_of_certRangeOk certSlice_4_5 (by omega) hs5
  else
  if hs6 : id < 1760 then
    exact dagNodeOk_of_certRangeOk certSlice_4_6 (by omega) hs6
  else
  if hs7 : id < 1792 then
    exact dagNodeOk_of_certRangeOk certSlice_4_7 (by omega) hs7
  else
  if hs8 : id < 1824 then
    exact dagNodeOk_of_certRangeOk certSlice_4_8 (by omega) hs8
  else
  if hs9 : id < 1856 then
    exact dagNodeOk_of_certRangeOk certSlice_4_9 (by omega) hs9
  else
  if hs10 : id < 1888 then
    exact dagNodeOk_of_certRangeOk certSlice_4_10 (by omega) hs10
  else
    exact dagNodeOk_of_certRangeOk certSlice_4_11 (by omega) hhi

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert4
