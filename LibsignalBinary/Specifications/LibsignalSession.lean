/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSessionRepr
public import LibsignalBinary.Specifications.LibsignalHmac
public import ProofLib.Hoare.LibcHooks

/-!
# Session Image Extern Hooks (`LibsignalSession`)

**Trusted in part.** `Computational/Theorems/Main.lean` unfolds `blackBoxHook` (installed in
`cliHookTablePlaced`); `sessionExterns` and `logFilterAddr` belong to the non-ELF session-image
harness. See `Computational/docs/TRUSTED_BASE.md`.

Extern hook table for the loaded session image:
* `blackBoxHook` models `subtle::black_box::<u8>` as the identity on the low byte of `x0`.
* `sessionExterns` maps `sha2::sha256::compress256` to `LibsignalHmac.compress256Hook F`,
  `memcpy` / `memmove` / `memset` to `ProofLib`'s libc hooks,
  `__rust_no_alloc_shim_is_unstable_v2` to `hookNoop`, `subtle::black_box::<u8>` to `blackBoxHook`,
  `<alloc::vec::Vec<_, _>>::remove::assert_failed` to `Rust.panicked`, and the three Rust
  allocator entry points to `alloc`.
* `logFilterAddr` is the extern-data address of `log::MAX_LOG_LEVEL_FILTER` (pinned by
  `LibsignalSessionGuards.lean`); holding `0` disables `log::Log::log`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSession

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

/-- `subtle::black_box::<u8>(input = w0) -> u8`: `x0 :=` the low byte of `x0`; `pc := lr`. -/
def blackBoxHook (s : State) : State :=
  retHook (fun s => s.writeReg64 .x0 (((s.readReg64 .x0).setWidth 8).zeroExtend 64)) s

/-- Extern hook map for the session image, parameterized by SHA-256 compression `F` and allocator
hooks `alloc`. -/
def sessionExterns (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State)) : String → Option (State → State) := fun sym =>
  if sym = "sha2::sha256::compress256" then some (LibsignalHmac.compress256Hook F)
  else if sym = "memcpy" then some hookMemcpy
  else if sym = "memmove" then some hookMemmove
  else if sym = "memset" then some hookMemset
  else if sym = "__rustc::__rust_no_alloc_shim_is_unstable_v2" then some hookNoop
  else if sym = "subtle::black_box::<u8>" then some blackBoxHook
  else if sym = "<alloc::vec::Vec<_, _>>::remove::assert_failed" then some Rust.panicked
  else if sym = "__rustc::__rust_alloc" ∨ sym = "__rustc::__rust_dealloc" ∨
      sym = "__rustc::__rust_realloc" then alloc sym
  else none

/-- Address of `log::MAX_LOG_LEVEL_FILTER` in the loaded session image (`img.base + 0x9a160`). -/
abbrev logFilterAddr (img : Obj.Image) : BitVec 64 := img.base + 0x9a160#64

end CryptoVerification.LibsignalSession
