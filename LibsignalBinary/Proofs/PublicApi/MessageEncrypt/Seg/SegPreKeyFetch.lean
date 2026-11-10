/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Specifications.LibsignalPublicApi
import ProofLib.GenDecodes

/-!
# Instruction Decode and Fetch Lemmas for `segPreKey_ok`

Kernel-checked decode lemmas and fetch tactics across the `segPreKey` code ranges (`+0x344..+0x390`,
`+0x680..+0x730`, `+0x78c..+0x7ec`, and `+0x880..+0xa70`) of `session_message_encrypt_with_stores`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi

set_option maxRecDepth 200000 in
theorem libsignalSessionCode_fnOff_0x3cbd8 :
    libsignalSessionCode.fnOff encryptWithStoresName = 248792 := by
  exact CryptoVerification.libsignalSessionCode_fnOff_0x3cbd8

open Lean Elab Tactic in
elab "messageEncryptPreKey_code_fetches_from " codeId:ident decPrefix:ident b:term:max H:term:max hfn:ident
    off:num k0:num len:num : tactic => do
  let off := off.getNat
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

macro "messageEncryptPreKey_fetches " b:term:max H:term:max hfn:ident k0:num len:num : tactic =>
  `(tactic| messageEncryptPreKey_code_fetches_from CryptoVerification.libsignalSessionCode messageEncryptPreKeyBin $b $H
    $hfn 0x3cbd8 $k0 $len)

/-! ## Unacknowledged Items Check (`+0x344..+0x390`) -/

gen_decodes libsignalSessionCode_tree messageEncryptPreKeyBin [0x3cf1c → 0x3cf64]

/-! ## Staleness Check (`+0x680..+0x730`) -/

gen_decodes libsignalSessionCode_tree messageEncryptPreKeyBin [0x3d258 → 0x3d304]

/-! ## Stale `SessionNotFound` Builder (`+0x78c..+0x7d0`) -/

gen_decodes libsignalSessionCode_tree messageEncryptPreKeyBin [0x3d364 → 0x3d3a4]

/-! ## Registration ID Load (`+0x7d0..+0x7ec`) -/

gen_decodes libsignalSessionCode_tree messageEncryptPreKeyBin [0x3d3a8 → 0x3d3c0]

/-! ## Kyber Closure and `OTR::encrypt` (`+0x880..+0x8f0`) -/

gen_decodes libsignalSessionCode_tree messageEncryptPreKeyBin [0x3d458 → 0x3d4c4]

/-! ## `PreKeySignalMessage::new` Call (`+0x8f0..+0x9b8`) -/

gen_decodes libsignalSessionCode_tree messageEncryptPreKeyBin [0x3d4c8 → 0x3d58c]

/-! ## 248-Byte Result Copy (`+0x9b8..+0xa70`) -/

gen_decodes libsignalSessionCode_tree messageEncryptPreKeyBin [0x3d590 → 0x3d644]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
