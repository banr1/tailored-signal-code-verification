/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import Symbolic.Proofs.Swarm.Leaves.IC14_Stage1Trials
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredTraceExplanation

/-!
# Receiver Trials and MAC Forgery Algebra Re-exports

Re-exports the receiver-trial membership and `MacTagForgeryOrCollision` lemmas from
`Symbolic.Proofs.Swarm.Leaves.IC14_Stage1Trials` under `Symbolic.Swarm.CREF.Stage1Trials`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Stage1Trials

export Symbolic.Swarm.Stage1Trials (
  trialTerms_seed_some
  mem_trialTerms_of_mem_extra
  computeMac_mem_trialTerms
  mem_flatMap_trialTerms_of_mem_extra
  MacTagForgeryOrCollision.of_ownSaltGuess
  MacTagForgeryOrCollision.of_crossSeedBytes
  MacTagForgeryOrCollision.of_crossSeedTerm
  MacTagForgeryOrCollision.of_crossSeedTerm_exact
  exists_honestSalt_of_not_ownSaltMacCollision
  MacTagForgeryOrCollision.mono_ctxs
  MacTagForgeryOrCollision.congr_gamma
  sinfo_exists_iff
  whisperTrials_mem_of_byteChain_some
  whisperTrials_mem_of_recvChainFor_none
  whisperTrials_mem_of_recvChainFor_some
  whisperTrials_mem_of_skippedKeyStored
  whisperTrials_mem_of_skippedKeyStored_owner
  chainKey_mem_whisperTrialTerms_of_recvChainFor
  computeMac_mem_whisperTrialTerms_of_recvChainFor
  computeMac_mem_whisperTrialTerms_of_byteChain
  computeMac_mem_whisperTrialTerms_of_skippedKeyStored
  whisperTrials_congr_gamma
  bobOpk?
  bobTrialGuard
  bobHandshakeKeys
  bobInitChain
  bobTrials_some_some
  computeMac_mem_bobTrialTerms
  MemoCollisionOn.mono_quiet
  RecvCollision.of_ownSaltMacCollision
)

end Symbolic.Swarm.CREF.Stage1Trials
