/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData

/-!
# Per-Node DAG Certificate Slice 10

Kernel-checked `dagNodeOk` certificates (`certRangeOk_10`) for receive-DAG nodes `3840 ≤ id < 4224`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert10

open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs (dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagOp dagBytes certRangeOk dagNodeOk_of_certRangeOk)

private theorem certSlice_10_0 : certRangeOk 3840 32 = true := by decide +kernel
private theorem certSlice_10_1 : certRangeOk 3872 32 = true := by decide +kernel
private theorem certSlice_10_2 : certRangeOk 3904 32 = true := by decide +kernel
private theorem certSlice_10_3 : certRangeOk 3936 32 = true := by decide +kernel
private theorem certSlice_10_4 : certRangeOk 3968 32 = true := by decide +kernel
private theorem certSlice_10_5 : certRangeOk 4000 32 = true := by decide +kernel
private theorem certSlice_10_6 : certRangeOk 4032 32 = true := by decide +kernel
private theorem certSlice_10_7 : certRangeOk 4064 32 = true := by decide +kernel
private theorem certSlice_10_8 : certRangeOk 4096 32 = true := by decide +kernel
private theorem certSlice_10_9 : certRangeOk 4128 32 = true := by decide +kernel
private theorem certSlice_10_10 : certRangeOk 4160 32 = true := by decide +kernel
private theorem certSlice_10_11 : certRangeOk 4192 32 = true := by decide +kernel

theorem certRangeOk_10 {id : Nat} (hlo : 3840 ≤ id) (hhi : id < 4224) :
    dagNodeOk dagOp dagBytes id = true := by
  if hs0 : id < 3872 then
    exact dagNodeOk_of_certRangeOk certSlice_10_0 (by omega) hs0
  else
  if hs1 : id < 3904 then
    exact dagNodeOk_of_certRangeOk certSlice_10_1 (by omega) hs1
  else
  if hs2 : id < 3936 then
    exact dagNodeOk_of_certRangeOk certSlice_10_2 (by omega) hs2
  else
  if hs3 : id < 3968 then
    exact dagNodeOk_of_certRangeOk certSlice_10_3 (by omega) hs3
  else
  if hs4 : id < 4000 then
    exact dagNodeOk_of_certRangeOk certSlice_10_4 (by omega) hs4
  else
  if hs5 : id < 4032 then
    exact dagNodeOk_of_certRangeOk certSlice_10_5 (by omega) hs5
  else
  if hs6 : id < 4064 then
    exact dagNodeOk_of_certRangeOk certSlice_10_6 (by omega) hs6
  else
  if hs7 : id < 4096 then
    exact dagNodeOk_of_certRangeOk certSlice_10_7 (by omega) hs7
  else
  if hs8 : id < 4128 then
    exact dagNodeOk_of_certRangeOk certSlice_10_8 (by omega) hs8
  else
  if hs9 : id < 4160 then
    exact dagNodeOk_of_certRangeOk certSlice_10_9 (by omega) hs9
  else
  if hs10 : id < 4192 then
    exact dagNodeOk_of_certRangeOk certSlice_10_10 (by omega) hs10
  else
    exact dagNodeOk_of_certRangeOk certSlice_10_11 (by omega) hhi

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert10
