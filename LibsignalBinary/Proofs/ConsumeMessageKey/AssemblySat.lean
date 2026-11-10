/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.Assembly -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import

/-!
# `HookSat`-Backed Placed Refinement for `RatchetState::consume_message_key`

Placed `.rodata`-backed `consume_message_key` refinement (Block 24) parameterized by
`HookSatExactMemcpy H lsMemcpySym` and `HookSat H lsMemsetSym sessionMemsetRegionSpec`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.ConsumeMessageKey.AssemblySat

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState)
open CryptoVerification
  (LibsignalPlacement lsBlackBoxU8Sym lsNoAllocShimSym lsRustReallocSym ls_subroutine_ok_of_block)
open CryptoVerification.RustHeap (RustAlloc rustReallocSpec)
open CryptoVerification.LibsignalHmac (compress256Hook)
open CryptoVerification.LibsignalSession
  (CmkPlacedRunStmt HmacPlacedRoOk blackBoxHook consume_message_key_placed_ro_run_of
   find_receiver_chain_index_placed_ok_at_cmk grow_one_placed_ok_at_cmk)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
  (lsCompress256Sym lsMemcpySym lsMemsetSym)
open CryptoVerification.LibsignalTripleRatchet (sessionMemsetRegionSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.HmacSat (hmac_sha256_placed_ro_ok_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (HookSatExactMemcpy)

theorem hmac_sha256_placed_ro_ok_at_cmk_sat [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState)
    {H : String → Option (State → State)}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_ms : HookSat H lsMemsetSym sessionMemsetRegionSpec)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) :
    HmacPlacedRoOk H F :=
  ls_subroutine_ok_of_block (i := 24) (j := 73) (hmac_sha256_placed_ro_ok_sat F h_mc h_ms h_c256)

/-- `.rodata`-backed placed refinement for `consume_message_key` under `HookSatExactMemcpy H lsMemcpySym` and `HookSat H lsMemsetSym sessionMemsetRegionSpec` (sibling of `consume_message_key_placed_ro_run`). -/
theorem consume_message_key_placed_ro_run_sat [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_realloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_ms : HookSat H lsMemsetSym sessionMemsetRegionSpec)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) :
    CmkPlacedRunStmt F A H := by
  intro hA hmm
  exact consume_message_key_placed_ro_run_of F A H
    (find_receiver_chain_index_placed_ok_at_cmk A h_bb)
    (hmac_sha256_placed_ro_ok_at_cmk_sat F h_mc h_ms h_c256)
    (grow_one_placed_ok_at_cmk A h_shim h_realloc hA) hA hmm

end LibsignalBinary.Proofs.ConsumeMessageKey.AssemblySat
