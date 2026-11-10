/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData

/-!
# Per-Node DAG Certificate Slice 17

Kernel-checked `dagNodeOk` certificates (`certRangeOk_17`) for receive-DAG nodes `6528 ≤ id < 6720`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert17

open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs (dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagOp dagBytes certRangeOk dagNodeOk_of_certRangeOk)

private theorem certSlice_17_0 : certRangeOk 6528 32 = true := by decide +kernel
private theorem certSlice_17_1 : certRangeOk 6560 32 = true := by decide +kernel
private theorem certSlice_17_2 : certRangeOk 6592 32 = true := by decide +kernel
private theorem certSlice_17_3 : certRangeOk 6624 32 = true := by decide +kernel
private theorem certSlice_17_4 : certRangeOk 6656 32 = true := by decide +kernel
private theorem certSlice_17_5 : certRangeOk 6688 32 = true := by decide +kernel

theorem certRangeOk_17 {id : Nat} (hlo : 6528 ≤ id) (hhi : id < 6720) :
    dagNodeOk dagOp dagBytes id = true := by
  if hs0 : id < 6560 then
    exact dagNodeOk_of_certRangeOk certSlice_17_0 (by omega) hs0
  else
  if hs1 : id < 6592 then
    exact dagNodeOk_of_certRangeOk certSlice_17_1 (by omega) hs1
  else
  if hs2 : id < 6624 then
    exact dagNodeOk_of_certRangeOk certSlice_17_2 (by omega) hs2
  else
  if hs3 : id < 6656 then
    exact dagNodeOk_of_certRangeOk certSlice_17_3 (by omega) hs3
  else
  if hs4 : id < 6688 then
    exact dagNodeOk_of_certRangeOk certSlice_17_4 (by omega) hs4
  else
    exact dagNodeOk_of_certRangeOk certSlice_17_5 (by omega) hhi

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert17
