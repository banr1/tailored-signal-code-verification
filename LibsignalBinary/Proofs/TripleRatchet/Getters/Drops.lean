/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError

/-!
# Drop Glue Proofs Umbrella

Re-exports the four drop-glue verification modules:
- `drop_vec_message_key_ok`: `core::ptr::drop_glue::<Vec<chain::MessageKey>>` (`0x1f28`)
- `drop_chain_ok`: `core::ptr::drop_glue::<session_structure::Chain>` (`0x35dc8`)
- `drop_vec_chain_ok`: `core::ptr::drop_glue::<Vec<session_structure::Chain>>` (`0x1e74`)
- `drop_spe_ok`: `core::ptr::drop_glue::<SignalProtocolError>` (`0x2374`)
-/

@[expose] public section
