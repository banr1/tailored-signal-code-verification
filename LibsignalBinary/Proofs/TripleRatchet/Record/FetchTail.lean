/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public meta import Aesop.BuiltinRules
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.Simps
public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Record

open Arm64 ProofLib ProofLib.ProgramReflection

open Lean Elab Tactic in
/-- Adds `<code>_fetch_fnAddr` hypotheses for `len / 4` consecutive instructions starting at
function-relative byte offset `k0` (`hfn : <code>.fnOff name = off`). -/
elab "segTail_code_fetches_from " codeId:ident decPrefix:ident b:term:max H:term:max hfn:term:max
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

/-- Fetch hypotheses for `session_message_decrypt_signal` (`hfn : fnOff msgDecryptName = 238760`),
    from fn-relative offset `k0`, `len` bytes. -/
macro "segTail_fetches " b:term:max H:term:max hfn:term:max k0:num len:num : tactic =>
  `(tactic| segTail_code_fetches_from CryptoVerification.libsignalSessionCode segTailBin $b $H
    $hfn (num% (ls_off% "session_message_decrypt_signal")) $k0 $len)

gen_decodes libsignalSessionCode_tree segTailBin [(ls_off% "session_message_decrypt_signal" + 2128), raw (ls_off% "session_message_decrypt_signal" + 2132), (ls_off% "session_message_decrypt_signal" + 2136) → (ls_off% "session_message_decrypt_signal" + 2152),
    (ls_off% "session_message_decrypt_signal" + 5860) → (ls_off% "session_message_decrypt_signal" + 5872), (ls_off% "session_message_decrypt_signal" + 6836) → (ls_off% "session_message_decrypt_signal" + 6864), (ls_off% "session_message_decrypt_signal" + 7408) → (ls_off% "session_message_decrypt_signal" + 7412), (ls_off% "session_message_decrypt_signal" + 7636) → (ls_off% "session_message_decrypt_signal" + 7720), (ls_off% "session_message_decrypt_signal" + 7820) → (ls_off% "session_message_decrypt_signal" + 7868),
    raw (ls_off% "session_message_decrypt_signal" + 7872), (ls_off% "session_message_decrypt_signal" + 7876) → (ls_off% "session_message_decrypt_signal" + 7888), raw (ls_off% "session_message_decrypt_signal" + 7892), raw (ls_off% "session_message_decrypt_signal" + 7896), (ls_off% "session_message_decrypt_signal" + 7900) → (ls_off% "session_message_decrypt_signal" + 7908), raw (ls_off% "session_message_decrypt_signal" + 7912),
    raw (ls_off% "session_message_decrypt_signal" + 7916), (ls_off% "session_message_decrypt_signal" + 7920), raw (ls_off% "session_message_decrypt_signal" + 7924), (ls_off% "session_message_decrypt_signal" + 7988) → (ls_off% "session_message_decrypt_signal" + 8012), (ls_off% "session_message_decrypt_signal" + 9792) → (ls_off% "session_message_decrypt_signal" + 9800)]

end CryptoVerification.LibsignalTripleRatchet.Record
