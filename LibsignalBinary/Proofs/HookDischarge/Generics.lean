/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Generics.BlackBoxU8
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop

/-!
# Umbrella Module for Generics / Zeroize Hook Discharges (`LibsignalBinary.Proofs.HookDischarge.Generics`)

Re-exports placement-generic (`hasWords` / `hasInstrs`) real-bytes bridge modules verified against
the exact instruction words emitted by pinned `rustc 1.98.1` (`aarch64-unknown-linux-musl` release
profile; matching `arm64-semantics/CaseStudies/Curve25519NeonEquiv/Proofs/Serial/Code.lean`):

| Symbol | Bridge Module | Real Machine Code |
|---|---|---|
| `subtle::black_box::<u8>` | `Generics.BlackBoxU8` | `blackBoxU8Words` / `blackBoxU8Instrs` (`5` words = `20` B, `16` B stack) |
| `<x25519_dalek::x25519::StaticSecret as Drop>::drop` | `Generics.ZeroizeDrop` | `zeroize32Words` / `zeroize32Instrs` (`63` words = `252` B, `0` B stack) |
| `<x25519_dalek::x25519::SharedSecret as Drop>::drop` | `Generics.ZeroizeDrop` | `sharedSecretDropInstrs addr targetAddr` (`1`-insn `b` tail-jump) + `zeroize32Words` / `zeroize32Instrs` at `targetAddr` (`<MontgomeryPoint as Zeroize>::zeroize`) |
-/

public section
