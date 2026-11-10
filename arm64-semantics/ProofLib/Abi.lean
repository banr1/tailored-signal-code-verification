/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Abi.Aapcs
public import ProofLib.Abi.Rust
import Arm64.Trusted.Spec.SepLogic

/-!
# Calling Convention and ABI Proof Rules

Re-exports proof-side AAPCS64 and Rust ABI contract combinators, consequence rules, and framing
lemmas from `ProofLib.Abi.Aapcs` and `ProofLib.Abi.Rust`.
-/

@[expose] public section
