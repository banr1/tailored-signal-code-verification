/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.TripleRatchet.Prog
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Stage P3 Callee Contracts and `STATIC_MAX_LEVEL` Address Lemma

Defines the isolated Stage P3 callee contract bundle (`StageP3CalleeContracts`) and the `adrp`
address calculation for `log::STATIC_MAX_LEVEL` in `message_decrypt_prekey::<PqxdhRng>::{closure#0}`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")

/-! ## 1. Isolated Callee Contracts for Stage P3 (`+0x1778..+0x1e00`) -/

/-- Isolated external callee contracts for Stage P3 (`Chain::clone` at `b + 0x766c8#64`,
`try_decrypt_with_state::<PqxdhRng>` at `b + 0x6eff8#64`, and
`SessionRecord::set_session_state` at `b + 0x174d4#64`). -/
structure StageP3CalleeContracts (A : RustAlloc) (b : BitVec 64) (C : Crypto)
    (ctl : BitVec 64) (abs : String → Option (State → State))
    (chainCloneSpec tryDecryptWithStateSpec setSessionStateSpec : Spec) : Prop where
  alloc : AllocHooks A abs
  chainClone : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + 0x766c8#64) chainCloneSpec
  tryDecryptWithState : subroutine_ok (tripleRatchetProgAt b C ctl abs)
    (b + 0x6eff8#64) tryDecryptWithStateSpec
  setSessionState : subroutine_ok (tripleRatchetProgAt b C ctl abs)
    (b + 0x174d4#64) setSessionStateSpec

/-- Address of `log::STATIC_MAX_LEVEL` (`b + 0xaa080#64`) computed by `adrp x8, +0xf000; ldr x8,
[x8, #0x810]`
at `0x4cdb8` (`+0x1cec`). -/
theorem adrp_logMaxLevel_0x1cec {b entry : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (hentry : entry = b + 0x7200c#64) :
    (((entry + 0x1cec#64) &&& 18446744073709547520#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - 0x73000) = b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) ∧
    ((((entry + 0x1cec#64) &&& 18446744073709547520#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - 0x73000)) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) =
      b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) := by
  subst hentry
  have hp : ((b + 0x7200c#64 + 0x1cec#64) &&& 18446744073709547520#64) = b + 0x73000#64 := by
    rw [BitVec.add_assoc, ProofLib.ObjectLoad.adrp_page_of_aligned hb]
    rfl
  rw [hp]
  constructor <;> bv_omega

end CryptoVerification.E2E.Pqxdh.ResponderClosure
