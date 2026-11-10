/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.RunOfCallees
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogue
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndex
import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOne
import LibsignalBinary.Proofs.ConsumeMessageKey.Hmac
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.Defs

/-!
# Binary Refinement for `RatchetState::consume_message_key`

Composes the seam proofs for `RatchetState::consume_message_key` (`0xded8`, Block 24) with its
out-of-line callees `find_receiver_chain_index`, `hmac_sha256`, and `RawVec<MessageKey>::grow_one`
to establish `ConsumeMessageKeyMeetsSpec` as well as placed `[LibsignalPlacement]` variants.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSession

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

/-- Compiled `RatchetState::consume_message_key` refines `RatchetState.consumeMessageKey`. -/
theorem consume_message_key_run (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image) :
    ConsumeMessageKeyMeetsSpec F A alloc img := by
  intro hA himg
  exact consume_message_key_run_of F A alloc img
    (find_receiver_chain_index_ok img F alloc A himg)
    (hmac_sha256_ok img F alloc himg)
    (grow_one_ok img F alloc himg A hA) hA himg

example : ∀ F A alloc img, ConsumeMessageKeyMeetsSpec F A alloc img := consume_message_key_run

theorem find_receiver_chain_index_placed_ok_at_cmk [LibsignalPlacement]
    {H : String → Option (State → State)} (A : RustAlloc)
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    FindIndexPlacedOk H A := by
  refine subroutine_ok_outcome_intro fun ⟨p, cs, theirA, their⟩ R s0 hpc hrun hpre hsp => ?_
  have h1 : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 26)
      (withLsCodeLoaded lsmpl (FindReceiverChainIndex.findPlacedSpec A)) :=
    ls_subroutine_ok_of_block (i := 24) (j := 26) (find_receiver_chain_index_placed_ok A h_bb)
  refine h1.mono_outcome (p, cs, theirA, their) R s0 hpc hrun ?_ hsp fun _ hout => hout
  have ⟨hcl, hp⟩ := extract_withLsCodeLoaded hpre
  refine AdvanceEpilogue.introduce_withLsCodeLoaded hcl ?_
  dsimp only [FindReceiverChainIndex.findPlacedSpec, findIndexPlacedSpec] at hp ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2, hsp⟩, hp.2⟩

theorem grow_one_placed_ok_at_cmk [LibsignalPlacement]
    {H : String → Option (State → State)} (A : RustAlloc)
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_realloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hA : CmkAllocHooks A H) :
    GrowOnePlacedOk H A :=
  ls_subroutine_ok_of_block (i := 24) (j := 43)
    (grow_one_placed_ok h_shim hA.1 h_realloc hA.2.2.2.1)

/-- Placed correctness of `RatchetState::consume_message_key` (Block 24). -/
theorem consume_message_key_placed_run [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_realloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hhmac : HmacPlacedOk H F) :
    CmkPlacedRunStmt F A H := by
  intro hA hmm
  exact consume_message_key_placed_run_of F A H
    (find_receiver_chain_index_placed_ok_at_cmk A h_bb)
    hhmac
    (grow_one_placed_ok_at_cmk A h_shim h_realloc hA) hA hmm

theorem hmac_sha256_placed_ro_ok_at_cmk [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState)
    {H : String → Option (State → State)}
    (h_mc : H CryptoHmacSha256.lsMemcpySym = some hookMemcpy)
    (h_ms : H CryptoHmacSha256.lsMemsetSym = some hookMemset)
    (h_c256 : H CryptoHmacSha256.lsCompress256Sym = some (LibsignalHmac.compress256Hook F)) :
    HmacPlacedRoOk H F :=
  ls_subroutine_ok_of_block (i := 24) (j := 73) (hmac_sha256_placed_ro_ok F h_mc h_ms h_c256)

/-- Placed correctness of `RatchetState::consume_message_key` (Block 24) discharging `hmac_sha256` from `.rodata`. -/
theorem consume_message_key_placed_ro_run [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_realloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (h_mc : H CryptoHmacSha256.lsMemcpySym = some hookMemcpy)
    (h_ms : H CryptoHmacSha256.lsMemsetSym = some hookMemset)
    (h_c256 : H CryptoHmacSha256.lsCompress256Sym = some (LibsignalHmac.compress256Hook F)) :
    CmkPlacedRunStmt F A H := by
  intro hA hmm
  exact consume_message_key_placed_ro_run_of F A H
    (find_receiver_chain_index_placed_ok_at_cmk A h_bb)
    (hmac_sha256_placed_ro_ok_at_cmk F h_mc h_ms h_c256)
    (grow_one_placed_ok_at_cmk A h_shim h_realloc hA) hA hmm

end CryptoVerification.LibsignalSession
