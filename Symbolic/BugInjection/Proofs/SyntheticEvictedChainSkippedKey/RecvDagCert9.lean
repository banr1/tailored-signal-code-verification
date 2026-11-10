/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData

/-! # Per-Node DAG Certificate Slice 9

Proves `dagNodeOk dagOp dagBytes id = true` for `3456 ≤ id < 3840` (`certRangeOk_9`) via
32-node kernel-checked slices. -/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert9

open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs (dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagOp dagBytes certRangeOk dagNodeOk_of_certRangeOk)

private theorem certSlice_9_0 : certRangeOk 3456 32 = true := by decide +kernel
private theorem certSlice_9_1 : certRangeOk 3488 32 = true := by decide +kernel
private theorem certSlice_9_2 : certRangeOk 3520 32 = true := by decide +kernel
private theorem certSlice_9_3 : certRangeOk 3552 32 = true := by decide +kernel
private theorem certSlice_9_4 : certRangeOk 3584 32 = true := by decide +kernel
private theorem certSlice_9_5 : certRangeOk 3616 32 = true := by decide +kernel
private theorem certSlice_9_6 : certRangeOk 3648 32 = true := by decide +kernel
private theorem certSlice_9_7 : certRangeOk 3680 32 = true := by decide +kernel
private theorem certSlice_9_8 : certRangeOk 3712 32 = true := by decide +kernel
private theorem certSlice_9_9 : certRangeOk 3744 32 = true := by decide +kernel
private theorem certSlice_9_10 : certRangeOk 3776 32 = true := by decide +kernel
private theorem certSlice_9_11 : certRangeOk 3808 32 = true := by decide +kernel

theorem certRangeOk_9 {id : Nat} (hlo : 3456 ≤ id) (hhi : id < 3840) :
    dagNodeOk dagOp dagBytes id = true := by
  if hs0 : id < 3488 then
    exact dagNodeOk_of_certRangeOk certSlice_9_0 (by omega) hs0
  else
  if hs1 : id < 3520 then
    exact dagNodeOk_of_certRangeOk certSlice_9_1 (by omega) hs1
  else
  if hs2 : id < 3552 then
    exact dagNodeOk_of_certRangeOk certSlice_9_2 (by omega) hs2
  else
  if hs3 : id < 3584 then
    exact dagNodeOk_of_certRangeOk certSlice_9_3 (by omega) hs3
  else
  if hs4 : id < 3616 then
    exact dagNodeOk_of_certRangeOk certSlice_9_4 (by omega) hs4
  else
  if hs5 : id < 3648 then
    exact dagNodeOk_of_certRangeOk certSlice_9_5 (by omega) hs5
  else
  if hs6 : id < 3680 then
    exact dagNodeOk_of_certRangeOk certSlice_9_6 (by omega) hs6
  else
  if hs7 : id < 3712 then
    exact dagNodeOk_of_certRangeOk certSlice_9_7 (by omega) hs7
  else
  if hs8 : id < 3744 then
    exact dagNodeOk_of_certRangeOk certSlice_9_8 (by omega) hs8
  else
  if hs9 : id < 3776 then
    exact dagNodeOk_of_certRangeOk certSlice_9_9 (by omega) hs9
  else
  if hs10 : id < 3808 then
    exact dagNodeOk_of_certRangeOk certSlice_9_10 (by omega) hs10
  else
    exact dagNodeOk_of_certRangeOk certSlice_9_11 (by omega) hhi

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert9
