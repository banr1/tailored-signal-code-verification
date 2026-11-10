/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData

/-!
# Per-Node DAG Certificate Slice 12

Kernel-checked `dagNodeOk` certificates (`certRangeOk_12`) for receive-DAG nodes `4608 ≤ id < 4992`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert12

open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs (dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagOp dagBytes certRangeOk dagNodeOk_of_certRangeOk)

private theorem certSlice_12_0 : certRangeOk 4608 32 = true := by decide +kernel
private theorem certSlice_12_1 : certRangeOk 4640 32 = true := by decide +kernel
private theorem certSlice_12_2 : certRangeOk 4672 32 = true := by decide +kernel
private theorem certSlice_12_3 : certRangeOk 4704 32 = true := by decide +kernel
private theorem certSlice_12_4 : certRangeOk 4736 32 = true := by decide +kernel
private theorem certSlice_12_5 : certRangeOk 4768 32 = true := by decide +kernel
private theorem certSlice_12_6 : certRangeOk 4800 32 = true := by decide +kernel
private theorem certSlice_12_7 : certRangeOk 4832 32 = true := by decide +kernel
private theorem certSlice_12_8 : certRangeOk 4864 32 = true := by decide +kernel
private theorem certSlice_12_9 : certRangeOk 4896 32 = true := by decide +kernel
private theorem certSlice_12_10 : certRangeOk 4928 32 = true := by decide +kernel
private theorem certSlice_12_11 : certRangeOk 4960 32 = true := by decide +kernel

theorem certRangeOk_12 {id : Nat} (hlo : 4608 ≤ id) (hhi : id < 4992) :
    dagNodeOk dagOp dagBytes id = true := by
  if hs0 : id < 4640 then
    exact dagNodeOk_of_certRangeOk certSlice_12_0 (by omega) hs0
  else
  if hs1 : id < 4672 then
    exact dagNodeOk_of_certRangeOk certSlice_12_1 (by omega) hs1
  else
  if hs2 : id < 4704 then
    exact dagNodeOk_of_certRangeOk certSlice_12_2 (by omega) hs2
  else
  if hs3 : id < 4736 then
    exact dagNodeOk_of_certRangeOk certSlice_12_3 (by omega) hs3
  else
  if hs4 : id < 4768 then
    exact dagNodeOk_of_certRangeOk certSlice_12_4 (by omega) hs4
  else
  if hs5 : id < 4800 then
    exact dagNodeOk_of_certRangeOk certSlice_12_5 (by omega) hs5
  else
  if hs6 : id < 4832 then
    exact dagNodeOk_of_certRangeOk certSlice_12_6 (by omega) hs6
  else
  if hs7 : id < 4864 then
    exact dagNodeOk_of_certRangeOk certSlice_12_7 (by omega) hs7
  else
  if hs8 : id < 4896 then
    exact dagNodeOk_of_certRangeOk certSlice_12_8 (by omega) hs8
  else
  if hs9 : id < 4928 then
    exact dagNodeOk_of_certRangeOk certSlice_12_9 (by omega) hs9
  else
  if hs10 : id < 4960 then
    exact dagNodeOk_of_certRangeOk certSlice_12_10 (by omega) hs10
  else
    exact dagNodeOk_of_certRangeOk certSlice_12_11 (by omega) hhi

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert12
