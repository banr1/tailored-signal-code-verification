/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.CodeLayout
public meta import Lean -- shake: keep

/-!
# Instruction Fetch Elaborators for CLI Responder Store Callees

Metaprogramming helpers and fetch-decode macros for CLI PQXDH responder store subroutines.
-/

@[expose] public section

/-- Resolves `<P>Cli_decode_…` in the current scope when present, falling back to `<P>_decode_…`. -/
private meta def portCliPickCli (env : Lean.Environment) (opts : Lean.Options) (ns : Lean.Name)
    (od : List Lean.OpenDecl) (n : Lean.Name) : Lean.Name :=
  if (Lean.ResolveName.resolveGlobalName env opts ns od n).any (fun r => r.2.isEmpty) then n
  else match n with
    | .str q s => .str q (((s.replace "Cli_decode_" "_decode_").replace "Cli_rebase_fetch_" "_rebase_fetch_").replace "Cli_fetch_" "_fetch_")
    | _ => n


namespace CryptoVerification.E2E.Pqxdh.ResponderStore

section Fetch

open Lean Meta Elab Command Tactic Arm64 ProofLib ProofLib.ProgramReflection

set_option maxHeartbeats 0

gen_decodes libsignalSessionCode_tree responderBinCli [(ls_off% "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>" + 0) → (ls_off% "core::ptr::drop_glue::<alloc::string::String> [local#8]" + 20), (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}" + 0) → (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}" + 832), (ls_off% "<str as alloc::borrow::ToOwned>::to_owned" + 0) → (ls_off% "<str as alloc::borrow::ToOwned>::to_owned" + 100)]

elab "responder_fetches_from_cli " b:term:max H:term:max hfn:term:max
    off:term:max k0:num len:num : tactic => do
  let portEnv ← Lean.getEnv
  let portOpts ← Lean.getOptions
  let portNs ← Lean.getCurrNamespace
  let portOd ← Lean.getOpenDecls
  let off := (← CryptoVerification.CodeLayout.evalNat off "fetches")
  let k0 := k0.getNat
  let len := len.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := mkIdent (portCliPickCli portEnv portOpts portNs portOd (.str `CryptoVerification.E2E.Pqxdh.ResponderStore
      s!"responderBinCli_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}"))
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

end Fetch

end CryptoVerification.E2E.Pqxdh.ResponderStore
