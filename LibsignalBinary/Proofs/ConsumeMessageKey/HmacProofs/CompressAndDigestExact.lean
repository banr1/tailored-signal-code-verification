/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlockExact

/-!
# `HookSatExactMemcpy` Sibling of `hmac_placed_runsTo` (`CompressAndDigestExact`, Block `73`)

- **Role:** `Role::Proof` (untrusted proof module outside the TCB; #1255 mc2 Cone 2).
- **Overview:**
  Composes `seg0_placed_runsTo_exact` and `seg1b_placed_runsTo_exact` from `EntryAndKeyBlockExact`
  with `seg1a_placed_runsTo`, `seg2_placed_runsTo`, `seg3_placed_runsTo`, and `seg4_placed_runsTo`
  from `EntryAndKeyBlock` / `CompressAndDigest` under `(h_memcpy : HookSatExactMemcpy H lsMemcpySym)`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigestExact

open Arm64
open CryptoGames.HMAC (ShaState)
open CryptoVerification (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement lsProg_73 lsmpl)
open CryptoVerification.LibsignalAesCbc (memsetHook)
open CryptoVerification.LibsignalHmac (compress256Hook)
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (
  HmacPlacedPre RunsTo StateH5 lsCompress256Sym lsMemcpySym lsMemsetSym seg1a_placed_runsTo
  seg2_placed_runsTo seg3_placed_runsTo seg4_placed_runsTo
)
open LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlockExact (
  seg0_placed_runsTo_exact seg1b_placed_runsTo_exact
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (HookSatExactMemcpy)

/-- `HookSatExactMemcpy` sibling of `hmac_placed_runsTo` (`CompressAndDigest.lean:1148`). -/
theorem hmac_placed_runsTo_exact [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
    (h_memset : H lsMemsetSym = some memsetHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {key : List (BitVec 8)} {byte : BitVec 8} {s₀ : State}
    (hcl : LibsignalCodeLoaded lsmpl s₀.mem) (hpre : HmacPlacedPre F key [byte] s₀)
    (hread_key : s₀.mem.Readable (s₀.readReg64 .x1) 32) :
    RunsTo (lsProg_73 H) s₀ (StateH5 F key byte s₀) :=
  (seg0_placed_runsTo_exact h_memcpy h_compress hcl hpre hread_key).trans fun _ h1 =>
  (seg1a_placed_runsTo hpre h1).trans fun _ h1m =>
  (seg1b_placed_runsTo_exact h_memcpy h_memset hpre h1m).trans fun _ h2 =>
  (seg2_placed_runsTo h_compress hpre h2).trans fun _ h3 =>
  (seg3_placed_runsTo h_compress hpre h3).trans fun _ h4 =>
  seg4_placed_runsTo hpre h4

end LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigestExact
