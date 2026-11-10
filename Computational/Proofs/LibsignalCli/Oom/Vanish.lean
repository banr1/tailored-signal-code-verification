/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.StatementPqOomGame

@[expose] public section

set_option autoImplicit false

/-!
# Vanishing Bad-Input Probability

**Checked by Lean.** Proves `cli_pq_bad_prob_vanishes_proof : CliPqBadProbVanishes`, showing that
`CliPqxdhFlagProb` is `0` whenever `bad` holds on no input.
-/

namespace Computational.Proofs.LibsignalCli.Oom.Vanish

open CryptoVerification.E2E (CliPqBadProbVanishes CliPqxdhFlagProb)

theorem cli_pq_bad_prob_vanishes_proof : CliPqBadProbVanishes := by
  intro Pt S run X W l qep decT encT A bad hbad
  unfold CliPqxdhFlagProb
  exact prEvent_eq_zero_of_forall_not _ _ fun ⟨_, w⟩ ⟨i, _, hi⟩ => hbad i hi

end Computational.Proofs.LibsignalCli.Oom.Vanish
