/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData

/-!
# Per-Node DAG Certificate Slice 16

Kernel-checked `dagNodeOk` certificates (`certRangeOk_16`) for receive-DAG nodes `6144 ≤ id < 6528`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert16

open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs (dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagOp dagBytes certRangeOk dagNodeOk_of_certRangeOk)

private theorem certSlice_16_0 : certRangeOk 6144 32 = true := by decide +kernel
private theorem certSlice_16_1 : certRangeOk 6176 32 = true := by decide +kernel
private theorem certSlice_16_2 : certRangeOk 6208 32 = true := by decide +kernel
private theorem certSlice_16_3 : certRangeOk 6240 32 = true := by decide +kernel
private theorem certSlice_16_4 : certRangeOk 6272 32 = true := by decide +kernel
private theorem certSlice_16_5 : certRangeOk 6304 32 = true := by decide +kernel
private theorem certSlice_16_6 : certRangeOk 6336 32 = true := by decide +kernel
private theorem certSlice_16_7 : certRangeOk 6368 32 = true := by decide +kernel
private theorem certSlice_16_8 : certRangeOk 6400 32 = true := by decide +kernel
private theorem certSlice_16_9 : certRangeOk 6432 32 = true := by decide +kernel
private theorem certSlice_16_10 : certRangeOk 6464 32 = true := by decide +kernel
private theorem certSlice_16_11 : certRangeOk 6496 32 = true := by decide +kernel

theorem certRangeOk_16 {id : Nat} (hlo : 6144 ≤ id) (hhi : id < 6528) :
    dagNodeOk dagOp dagBytes id = true := by
  if hs0 : id < 6176 then
    exact dagNodeOk_of_certRangeOk certSlice_16_0 (by omega) hs0
  else
  if hs1 : id < 6208 then
    exact dagNodeOk_of_certRangeOk certSlice_16_1 (by omega) hs1
  else
  if hs2 : id < 6240 then
    exact dagNodeOk_of_certRangeOk certSlice_16_2 (by omega) hs2
  else
  if hs3 : id < 6272 then
    exact dagNodeOk_of_certRangeOk certSlice_16_3 (by omega) hs3
  else
  if hs4 : id < 6304 then
    exact dagNodeOk_of_certRangeOk certSlice_16_4 (by omega) hs4
  else
  if hs5 : id < 6336 then
    exact dagNodeOk_of_certRangeOk certSlice_16_5 (by omega) hs5
  else
  if hs6 : id < 6368 then
    exact dagNodeOk_of_certRangeOk certSlice_16_6 (by omega) hs6
  else
  if hs7 : id < 6400 then
    exact dagNodeOk_of_certRangeOk certSlice_16_7 (by omega) hs7
  else
  if hs8 : id < 6432 then
    exact dagNodeOk_of_certRangeOk certSlice_16_8 (by omega) hs8
  else
  if hs9 : id < 6464 then
    exact dagNodeOk_of_certRangeOk certSlice_16_9 (by omega) hs9
  else
  if hs10 : id < 6496 then
    exact dagNodeOk_of_certRangeOk certSlice_16_10 (by omega) hs10
  else
    exact dagNodeOk_of_certRangeOk certSlice_16_11 (by omega) hhi

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert16
