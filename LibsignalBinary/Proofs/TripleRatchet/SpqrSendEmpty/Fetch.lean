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
# Instruction Fetches for `spqr::send::<HookRng>` on the Empty-State Path

Decode lemmas and range-fetch tactics (`code_fetches_from`, `spqr_fetches`) for the 61 instructions
executed by `spqr::send::<libsignal_session::HookRng>` (`0x3085c`) when the post-quantum state is empty.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty

open Arm64 ProofLib ProofLib.ProgramReflection

open Lean Elab Tactic in
/-- Adds `<code>_fetch_fnAddr` hypotheses for `len / 4` consecutive instructions starting at
function-relative byte offset `k0` (`hfn : <code>.fnOff name = off`). -/
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

/-- Fetch hypotheses for `spqr::send::<HookRng>` (`hfn : fnOff spqrSendName = 0x3085c`), from
    fn-relative offset `k0`, `len` bytes. -/
macro "spqr_fetches " b:term:max H:term:max hfn:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_from CryptoVerification.libsignalSessionCode libsignalSessionBin $b $H
    $hfn (num% (ls_off% "spqr::send::<libsignal_session::HookRng>")) $k0 $len)

gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "spqr::send::<libsignal_session::HookRng>") → (ls_off% "spqr::send::<libsignal_session::HookRng>" + 104), (ls_off% "spqr::send::<libsignal_session::HookRng>" + 136) → (ls_off% "spqr::send::<libsignal_session::HookRng>" + 220),
    (ls_off% "spqr::send::<libsignal_session::HookRng>" + 4608) → (ls_off% "spqr::send::<libsignal_session::HookRng>" + 4616), (ls_off% "spqr::send::<libsignal_session::HookRng>" + 4632) → (ls_off% "spqr::send::<libsignal_session::HookRng>" + 4664)]

end CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty
