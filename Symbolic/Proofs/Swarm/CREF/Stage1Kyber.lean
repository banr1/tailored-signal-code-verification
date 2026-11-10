/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber

/-!
# Kyber 32-Byte Packing and Inversion Re-exports

Re-exports the KEM packing, concretization, and shape-inversion lemmas from
`Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber` under `Symbolic.Swarm.CREF.Stage1Kyber`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Stage1Kyber

export Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber (
  kemEncap_fst_eq_pack
  kemEncap_snd_eq_pack
  view_kemEncap_pack
  view_kemSS_pack
  kemEncap_pack_inj
  kemSS_pack_inj
  kemEncap_fst_inj
  kemEncap_snd_inj
  randTerm_inj
  kemDecap_kemEncap
  kemDecap_eq_some_iff
  errToOption_kemDecap_eq_some_iff
  view_litOf_kemPk_eq_none
  view_litOf_kemEncap_eq_none
  view_litOf_kemSS_eq_none
  view_litOf_random_eq_none
  litOf_ne_kemEncap_pack
  litOf_ne_kemSS_pack
  kemPk_eq_pack
  kemRejKey_eq_pack
  view_kemRejKey_pack
  kemRejKey_pack_inj
  kemRejKey_inj
  view_litOf_kemRejKey_eq_none
  litOf_ne_kemRejKey_pack
  rejKey_length_eq_32
  view?_kemRejKey_disjoint
  subKemRej
  gamma'_pack_kemEncap
  gamma'_pack_kemSS
  gamma'_pack_kemPk
  gamma'_pack_kemRej
  gamma'_pack_random
  gamma'_kemEncap_of_len32
  gamma'_kemEncap_of_len_ne32
  gamma'_kemSS_of_len32
  gamma'_kemSS_of_len_ne32
  gamma_kemEncap_fst
  gamma_kemEncap_snd
  gamma_kemPk_eq
  gamma'_kemRejKey_eq
  gamma_kemRejKey_eq
  mem_memo_kemEncap_self_of_len32
  mem_memo_kemSS_self_of_len32
  mem_memo_kemRejKey_self
  self_mem_memo_kemEncap_of_shape_eq_self
  self_mem_memo_kemSS_of_shape_eq_self
  assumedInjective_kemPk_eq_false
  assumedInjective_litOf_eq_false
  assumedInjective_eq_true_iff
  shape_kemEncap_heads_none
  shape_kemSS_heads_none
  shape_kemSS_ne_concat
  shape_kemRejKey_heads_none
  shape_kemRejKey_ne_concat
  Gamma'ShapeClass
  gamma'_shape_cases
  shape_eq_kemEncap_pack_iff
  shape_eq_kemSS_pack_iff
  shape_eq_kemRejKey_pack_iff
  shape_eq_randTerm_iff
  eq_kemSS_of_shape_eq_kemSS_len32
  kemSS_rand32_twin_ts_eq
  gamma_bobKemShare
)

end Symbolic.Swarm.CREF.Stage1Kyber
