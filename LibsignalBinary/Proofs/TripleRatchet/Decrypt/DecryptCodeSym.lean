/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym130
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym433
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSymCalleesA
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSymCalleesB

/-!
# Relocatable Per-Block Decode & Fetch Lemmas for `Decrypt`

Umbrella module re-exporting per-block instruction decode and fetch lemmas for blocks `130`
(`try_decrypt_with_state::<HookRng>`), `433` (`try_decrypt_with_state::<Coins>`), and callee blocks
`4, 40, 60, 62, 69, 125, 200, 205, 207, 215, 329`.
-/

@[expose] public section
