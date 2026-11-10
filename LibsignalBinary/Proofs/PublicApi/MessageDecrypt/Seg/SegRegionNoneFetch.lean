/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Specifications.LibsignalTripleRatchet

/-!
# Instruction Decode and Fetch Helpers for `SegRegionNone`

Instruction decode lemmas and `messageDecryptRegionNone_fetches` tactic for the 69 instructions on
the no-current-session path (`+0x1a8 → +0x1f50` of `session_message_decrypt_signal_with_stores`,
`fnOff = 0x3a4a8`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionNone

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000 in
/-- `session_message_decrypt_signal_with_stores` (`msgDecryptName`) starts at image offset `0x3a4a8`
(= 238760). -/
theorem libsignalSessionCode_fnOff_sym_3a4a8 :
    libsignalSessionCode.fnOff msgDecryptName = num% (ls_off% "session_message_decrypt_signal") := by
  exact (ls_lemma% fnOff "session_message_decrypt_signal")

open Lean Elab Tactic in
/-- `messageDecryptRegionNone_code_fetches_from <code> <decPrefix> b H hfn off k0 len` adds `<code>_fetch_fnAddr`
    hypotheses for the instructions `k = k0, k0 + 4, …, k0 + len - 4` of the function at offset
    `off` (`hfn : <code>.fnOff name = off`), using `<decPrefix>_decode_0x<off+k>`. -/
elab "messageDecryptRegionNone_code_fetches_from " codeId:ident decPrefix:ident b:term:max H:term:max hfn:term:max
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

/-- Fetch hypotheses for `session_message_decrypt_signal_with_stores`
(`hfn : fnOff msgDecryptName = 238760`), from fn-relative offset `k0`, `len` bytes. -/
macro "messageDecryptRegionNone_fetches " b:term:max H:term:max hfn:term:max k0:num len:num : tactic =>
  `(tactic| messageDecryptRegionNone_code_fetches_from CryptoVerification.libsignalSessionCode messageDecryptRegionNoneBin $b $H
    $hfn (num% (ls_off% "session_message_decrypt_signal")) $k0 $len)

gen_decodes libsignalSessionCode_tree messageDecryptRegionNoneBin [(ls_off% "session_message_decrypt_signal" + 424) → (ls_off% "session_message_decrypt_signal" + 504), (ls_off% "session_message_decrypt_signal" + 2140) → (ls_off% "session_message_decrypt_signal" + 2152), (ls_off% "session_message_decrypt_signal" + 5860) → (ls_off% "session_message_decrypt_signal" + 5872),
    (ls_off% "session_message_decrypt_signal" + 6836) → (ls_off% "session_message_decrypt_signal" + 6852), (ls_off% "session_message_decrypt_signal" + 6912) → (ls_off% "session_message_decrypt_signal" + 6920), (ls_off% "session_message_decrypt_signal" + 7408) → (ls_off% "session_message_decrypt_signal" + 7412), (ls_off% "session_message_decrypt_signal" + 7636) → (ls_off% "session_message_decrypt_signal" + 7720), (ls_off% "session_message_decrypt_signal" + 9792) → (ls_off% "session_message_decrypt_signal" + 9800),
    (ls_off% "session_message_decrypt_signal" + 7820) → (ls_off% "session_message_decrypt_signal" + 7828), (ls_off% "session_message_decrypt_signal" + 7988) → (ls_off% "session_message_decrypt_signal" + 7992)]

end CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionNone
