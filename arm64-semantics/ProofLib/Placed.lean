/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.Fetch
public import ProofLib.Placed.Pair
public import ProofLib.Placed.AdrpLdst
public import ProofLib.Placed.Interned
public import ProofLib.Placed.CheckText
public import ProofLib.Placed.Check
public import ProofLib.Placed.Transfer
public import ProofLib.Placed.Multi
public import ProofLib.Placed.LabelsCheck
public import ProofLib.Placed.LabelsInterned
public import ProofLib.Placed.LabelsCoverage
public import ProofLib.Placed.SharedCode

/-!
# Placed Libraries

Re-exports proof infrastructure for relocatable libraries modeled as `Obj.PlacedLib` and
`Obj.MultiPlacedLib`: patched-word instruction fetch and relaxable `ADRP` pairs, `Nat`-indexed
interned checkers for `Placeable` and `LinkedIn`, ELF transfer into `Program.pureMem`, object
label certification, and shared relocated code contracts (`Obj.RelocCodeAt`).
See [`ProofLib/Placed/README.md`](Placed/README.md) for module-by-module details.
-/
