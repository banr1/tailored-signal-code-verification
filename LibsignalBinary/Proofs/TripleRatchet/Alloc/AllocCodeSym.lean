/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.PlacedCallSym
public import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym -- shake: keep

/-!
# Relocatable Per-Block Fetches for `TripleRatchet/Alloc`

Generated instruction-fetch definitions for blocks `13` (`do_reserve_and_handle`), `22`
(`ChainKey::to_pb`), `23` (`Box<[u8]>::try_clone_from_ref_in`), `45` (`RawVecInner::finish_grow`),
`56` (`Vec<u8>::into_boxed_slice`), `200` (`PrivateKey::derive_public_key_bytes`), and `205`
(`PublicKey::serialize`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification

open Arm64 ProofLib

abbrev lsRustDeallocSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"

abbrev lsRustNoAllocShimSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2"

abbrev lsMemcpySym : String :=
  "memcpy"

abbrev lsPubFromSecretSym : String :=
  "_RNvXs8_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_9PublicKeyINtNtCskxtBwYRO61I_4core7convert4FromRNtB5_12StaticSecretE4from"

theorem ls_hook_ok_of_mem [LibsignalPlacement] {α : Type} {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} {spec : Spec α} (hsat : HookSat H sym spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ sym) spec := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem
  exact ls_hook_ok (k := k) (by simp [hk, hget]) hsat hi hunmut

gen_ls_blk 13
gen_ls_blk 22
gen_ls_blk 23
gen_ls_blk 56
gen_ls_blk 200
gen_ls_blk 205

end CryptoVerification
