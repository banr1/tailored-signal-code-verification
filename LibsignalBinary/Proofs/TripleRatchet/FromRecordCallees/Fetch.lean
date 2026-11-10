/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# Instruction Decode and Fetch Lemmas for `FromRecordCallees`

Provides `code_fetches_from` and `rfl_kernel` decode lemmas for `drop_glue<SessionStructure>`
(`[local#1]`, `[local#2]`), `SessionRecord::set_session_state`,
`RawVec<SignalProtocolError>::grow_one`, and `try_decrypt_from_record::{closure#0}`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open Arm64 ProofLib ProofLib.ProgramReflection

set_option maxHeartbeats 0
set_option maxRecDepth 2000000

open Lean Elab Tactic in
/-- `code_fetches_from <code> <decPrefix> b H hfn off k0 len` adds `<code>_fetch_fnAddr`
    hypotheses for the instructions `k = k0, k0 + 4, …, k0 + len - 4` of the function at offset
    `off` (`hfn : <code>.fnOff name = off`), using `<decPrefix>_decode_0x<off+k>`. -/
elab "code_fetches_from " codeId:ident decPrefix:ident b:term:max H:term:max hfn:term:max
    off:term:max k0:num len:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat off "fetches"
  let k0 := k0.getNat
  let len := len.getNat
  let codeBase := codeId.getId.eraseMacroScopes
  let decBase := decPrefix.getId.eraseMacroScopes
  let fetchEntry := mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := mkIdent (decBase.appendAfter s!"_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

/-! ## `drop_glue<SessionStructure> [local#2]` (`0x35958`, 69 insns) -/

gen_decodes libsignalSessionCode_tree fromRecordCalleesBin [(ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#2]") → (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#2]" + 272)]

/-! ## `drop_glue<SessionStructure> [local#1]` (`0x25b4`, 68 insns) -/

gen_decodes libsignalSessionCode_tree fromRecordCalleesBin [(ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") → (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]" + 268)]

/-! ## `SessionRecord::set_session_state` (`0x174d4`, 15 insns) -/

gen_decodes libsignalSessionCode_tree fromRecordCalleesBin [(ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state") → (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state" + 56)]

/-! ## `RawVec<SignalProtocolError>::grow_one` (`0x15c44`, 26 insns) -/

gen_decodes libsignalSessionCode_tree fromRecordCalleesBin [(ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one") → (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one" + 100)]

/-! ## `try_decrypt_from_record::{closure#0}` prologue + log check (`0x381ac..0x381d8`, 12 insns) -/

gen_decodes libsignalSessionCode_tree fromRecordCalleesBin [(ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_session::HookRng>::{closure#0}") → (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_session::HookRng>::{closure#0}" + 44)]

/-! ## `try_decrypt_from_record::{closure#0}` epilogue (`0x38348..0x3835c`, 6 insns) -/

gen_decodes libsignalSessionCode_tree fromRecordCalleesBin [(ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_session::HookRng>::{closure#0}" + 412) → (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_session::HookRng>::{closure#0}" + 432)]

end CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
