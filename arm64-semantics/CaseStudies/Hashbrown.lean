/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import CaseStudies.Hashbrown.Spec
import CaseStudies.Hashbrown.SpecExamples
import CaseStudies.Hashbrown.Proofs.Top
import CaseStudies.Hashbrown.Proofs.StdCli.Top
import CaseStudies.Hashbrown.Proofs.CliProof
import VerifiedLibraries.SwissTable

/-!
# `hashbrown` v0.17.1

Umbrella module re-exporting the whole-binary `hashbrown_cli.elf` specification and executable
examples (`CaseStudies.Hashbrown.Spec`, `CaseStudies.Hashbrown.SpecExamples`), the relocatable
SwissTable library contracts (`CaseStudies.Hashbrown.Proofs.Top`), the `std` and `mallocng` CLI
driver proofs (`CaseStudies.Hashbrown.Proofs.StdCli.Top`, `CaseStudies.Hashbrown.Proofs.CliProof`),
and the underlying SwissTable model (`VerifiedLibraries.SwissTable`).
-/
