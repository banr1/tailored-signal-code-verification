/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Instances -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer

/-!
# `HookSat`-Parameterized Relocatable Contracts for `crypto::hmac_sha256`

Provides relocatable `[LibsignalPlacement]` contracts for `crypto::hmac_sha256` (Block `73`) under
`HookSatExactMemcpy H lsMemcpySym` and `HookSat H lsMemsetSym sessionMemsetRegionSpec`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesSat

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement LibsignalRoLoaded blkPC_73 blkPl_73 lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer
  (ls_subroutine_ok_transfer)
open CryptoVerification.LibsignalHmac (compress256Hook)
open CryptoVerification.LibsignalSession (hmacSpec)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
  (hmacPlacedSpec lsCompress256Sym lsMemcpySym lsMemsetSym)
open CryptoVerification.LibsignalTripleRatchet (sessionMemsetRegionSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.HmacSat
  (hmac_sha256_placed_ok_sat hmac_sha256_placed_ro_ok_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (HookSatExactMemcpy)

section Placed

variable [LibsignalPlacement]

/-- Relocatable `[LibsignalPlacement]` contract for `crypto::hmac_sha256` (Block `73`)
with `hmacPlacedSpec F` under `HookSatExactMemcpy H lsMemcpySym` and
`HookSat H lsMemsetSym sessionMemsetRegionSpec`. -/
theorem hmac_placed_ok_sat (F : ShaCompress)
    {H : String → Option (State → State)}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_ms : HookSat H lsMemsetSym sessionMemsetRegionSpec)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) :
    subroutine_ok ((blkPC_73).rebase (blkPl_73).base H) (blkPl_73).base
      (withLsCodeLoaded lsmpl (hmacPlacedSpec F)) :=
  hmac_sha256_placed_ok_sat F h_mc h_ms h_c256

theorem hmac_placed_ro_ok_sat (F : ShaCompress)
    {H : String → Option (State → State)}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_ms : HookSat H lsMemsetSym sessionMemsetRegionSpec)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) :
    subroutine_ok ((blkPC_73).rebase (blkPl_73).base H) (blkPl_73).base
      (withLsCodeLoaded lsmpl
        { hmacSpec F with
          pre := fun g s => sepConj ((hmacSpec F).pre g s) ⌜LibsignalRoLoaded lsmpl s.mem⌝ }) :=
  hmac_sha256_placed_ro_ok_sat F h_mc h_ms h_c256

theorem hmac_placed_ro_ok_at_block_sat {callerProg : Program} {i : Nat}
    (F : ShaCompress) {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_ms : HookSat H lsMemsetSym sessionMemsetRegionSpec)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 73)
      (withLsCodeLoaded lsmpl
        { hmacSpec F with
          pre := fun g s => sepConj ((hmacSpec F).pre g s) ⌜LibsignalRoLoaded lsmpl s.mem⌝ }) :=
  ls_subroutine_ok_transfer (hmac_placed_ro_ok_sat F h_mc h_ms h_c256) hi

end Placed

end LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesSat
