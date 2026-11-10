/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.TrapRng
public import LibsignalBinary.Proofs.Placed.PlacedCallSym
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Defs
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Calls
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceId
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ProtocolAddressDisplay

/-!
# Trap-at-RNG and Cross-Block Call-Site Lemmas for In-Image Callees

Call-site transport lemmas on `trTrapProgAt` for `ServiceId::parse_from_service_id_string`
and `<ProtocolAddress as Display>::fmt`, plus generic `[LibsignalPlacement]` cross-block lifting.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr

/-- An in-image callee's contract, moved from its entry to `fnAddr name + k` on `trTrapProgAt`. -/
theorem inImage_ok_at_trap {α : Type} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {spec : Spec α}
    {name callee : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff callee)
    (h : subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr callee) spec) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) spec :=
  inImage_ok_at_rebase hk h

theorem parse_sid_ok_at_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff parseSidName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (parseSidCodeSpec uuidTryParse) :=
  inImage_ok_at_trap hk (parseSid_ok_trap b C abs)

theorem addr_display_ok_at_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hW : HookSat abs fmtWriteName (fmtWriteSpec A)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff addrDisplayName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (addrDisplaySpec A) :=
  inImage_ok_at_trap hk (addrDisplay_ok_trap b C A abs hW)

/-! ## Relocatable Cross-Block Call-Site Lemmas (`[LibsignalPlacement]`) -/

/-- Relocatable cross-block lift from block `j` to caller block `i`. -/
theorem inImage_placed_ok_at [LibsignalPlacement] {α : Type} {prog calleeProg : Program}
    {i j : Nat} {H : String → Option (State → State)} {spec : Spec α}
    [IsLsBlockProg prog i H] [IsLsBlockProg calleeProg j H]
    (h : subroutine_ok calleeProg (lsmpl.base j) (withLsCodeLoaded lsmpl spec))
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide)
    (hj : j < 619 := by decide) (hunmut_j : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base j) (withLsCodeLoaded lsmpl spec) :=
  ls_subroutine_ok_of_block (callerProg := prog) h hi hj hunmut_j

end CryptoVerification.LibsignalTripleRatchet
