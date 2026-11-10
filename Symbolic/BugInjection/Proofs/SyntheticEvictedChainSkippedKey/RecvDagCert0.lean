/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData

/-!
# Per-Node DAG Certificate Slice 0

Kernel-checked `dagNodeOk` certificates (`certRangeOk_0`) for receive-DAG nodes `0 ≤ id < 384`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert0

open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs (dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagOp dagBytes certRangeOk dagNodeOk_of_certRangeOk)

private theorem certSlice_0_0 : certRangeOk 0 32 = true := by decide +kernel
private theorem certSlice_0_1 : certRangeOk 32 32 = true := by decide +kernel
private theorem certSlice_0_2 : certRangeOk 64 32 = true := by decide +kernel
private theorem certSlice_0_3 : certRangeOk 96 32 = true := by decide +kernel
private theorem certSlice_0_4 : certRangeOk 128 32 = true := by decide +kernel
private theorem certSlice_0_5 : certRangeOk 160 32 = true := by decide +kernel
private theorem certSlice_0_6 : certRangeOk 192 32 = true := by decide +kernel
private theorem certSlice_0_7 : certRangeOk 224 32 = true := by decide +kernel
private theorem certSlice_0_8 : certRangeOk 256 32 = true := by decide +kernel
private theorem certSlice_0_9 : certRangeOk 288 32 = true := by decide +kernel
private theorem certSlice_0_10 : certRangeOk 320 32 = true := by decide +kernel
private theorem certSlice_0_11 : certRangeOk 352 32 = true := by decide +kernel

theorem certRangeOk_0 {id : Nat} (hlo : 0 ≤ id) (hhi : id < 384) :
    dagNodeOk dagOp dagBytes id = true := by
  if hs0 : id < 32 then
    exact dagNodeOk_of_certRangeOk certSlice_0_0 (by omega) hs0
  else
  if hs1 : id < 64 then
    exact dagNodeOk_of_certRangeOk certSlice_0_1 (by omega) hs1
  else
  if hs2 : id < 96 then
    exact dagNodeOk_of_certRangeOk certSlice_0_2 (by omega) hs2
  else
  if hs3 : id < 128 then
    exact dagNodeOk_of_certRangeOk certSlice_0_3 (by omega) hs3
  else
  if hs4 : id < 160 then
    exact dagNodeOk_of_certRangeOk certSlice_0_4 (by omega) hs4
  else
  if hs5 : id < 192 then
    exact dagNodeOk_of_certRangeOk certSlice_0_5 (by omega) hs5
  else
  if hs6 : id < 224 then
    exact dagNodeOk_of_certRangeOk certSlice_0_6 (by omega) hs6
  else
  if hs7 : id < 256 then
    exact dagNodeOk_of_certRangeOk certSlice_0_7 (by omega) hs7
  else
  if hs8 : id < 288 then
    exact dagNodeOk_of_certRangeOk certSlice_0_8 (by omega) hs8
  else
  if hs9 : id < 320 then
    exact dagNodeOk_of_certRangeOk certSlice_0_9 (by omega) hs9
  else
  if hs10 : id < 352 then
    exact dagNodeOk_of_certRangeOk certSlice_0_10 (by omega) hs10
  else
    exact dagNodeOk_of_certRangeOk certSlice_0_11 (by omega) hhi

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert0
