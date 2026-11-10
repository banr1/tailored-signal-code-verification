/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitChain
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitPack
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitWp
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitEvict
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep3
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep5
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMain

/-!
# Decrypt DH Step Commit Sub-Segment (`DhCommitSpec`)

Umbrella module re-exporting the DH commit submodules:
- `DhCommitChain`: `chainAt` byte-slice lemmas, `DhCommitState`, and `DhCommitSpec`
- `DhCommitPack`: packing/unpacking helpers, address lemmas, and `ReachesOrPanic` combinators
- `DhCommitWp`: basic-block `SepWP` lemmas `commit_step1_wp` .. `commit_step5_wp`
- `DhCommitEvict`: receiver-chain eviction loop (`dhCommit_evict_one`, `dhCommit_evict_loop`, `dhCommit_step4`)
- `DhCommitStep3`: receiver-chain push and box free (`dhCommit_step3a`, `dhCommit_step3`)
- `DhCommitStep12`: state commit, `PublicKey::serialize`, and `ChainKey::to_pb` (`dhCommit_step1_2`)
- `DhCommitStep5`: `sender_chain` commit and `ConsumeMsgKeyState` staging (`dhCommit_step5`)
- `DhCommitMain`: top-level `dhCommit_spec` and relocatable seams
-/

@[expose] public section
