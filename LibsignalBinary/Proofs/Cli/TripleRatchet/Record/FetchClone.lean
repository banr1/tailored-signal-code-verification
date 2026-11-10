/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Aesop.BuiltinRules
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.Simps
public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual
import LibsignalBinary.Proofs.CodeLayout
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core
public meta import Lean -- shake: keep

/-!
# Instruction Decode Fetches for CLI `SegClone`

Provides `segClone_fetches_cli` and rebase decode lemmas for the `SessionStructure::clone` segment
(`+0x1a8 .. +0x698`, `+0x18f4 .. +0x1934`, `+0x25f8 .. +0x263c`) of CLI
`signal_session_ratchet::decrypt_signal`.
-/

@[expose] public section

/-- Resolves `<P>Cli_decode_…` at the call site when available, falling back to `<P>_decode_…`. -/
private meta def portCliPickCli (env : Lean.Environment) (opts : Lean.Options) (ns : Lean.Name)
    (od : List Lean.OpenDecl) (n : Lean.Name) : Lean.Name :=
  if (Lean.ResolveName.resolveGlobalName env opts ns od n).any (fun r => r.2.isEmpty) then n
  else match n with
    | .str q s => .str q (((s.replace "Cli_decode_" "_decode_").replace "Cli_rebase_fetch_" "_rebase_fetch_").replace "Cli_fetch_" "_fetch_")
    | _ => n


namespace CryptoVerification.LibsignalTripleRatchet.Record

open Arm64 ProofLib ProofLib.ProgramReflection

open Lean Elab Tactic in
/-- Adds `libsignalSessionCode_fetch_fnAddr` hypotheses for offsets `k0, k0 + 4, …, k0 + len - 4`
of `signal_session_ratchet::decrypt_signal`. -/
elab "segClone_fetches_cli " b:term:max H:term:max hfn:term:max k0:num len:num : tactic => do
  let portEnv ← Lean.getEnv
  let portOpts ← Lean.getOptions
  let portNs ← Lean.getCurrNamespace
  let portOd ← Lean.getOpenDecls
  let off := num% (ls_off% "libsignal_cli_ratchet::decrypt_signal")
  let k0 := k0.getNat
  let len := len.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := mkIdent (portCliPickCli portEnv portOpts portNs portOd (Name.mkSimple s!"segCloneBinCli_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}"))
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

gen_decodes libsignalSessionCode_tree segCloneBinCli [(ls_off% "libsignal_cli_ratchet::decrypt_signal" + 424) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 688), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 692), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 696) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 844), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 848), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 852) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 904), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 908), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 912) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1188)]

gen_decodes libsignalSessionCode_tree segCloneBinCli [(ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1272) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1276), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1280), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1284) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1288), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1292), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1296) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1320), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1324), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1328) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1340), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1344), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1348) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1356), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1360), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1364) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1376), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1380), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1384) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1400), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1404), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1408) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1416), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1420), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1424) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1688)]

gen_decodes libsignalSessionCode_tree segCloneBinCli [(ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6388) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6412), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6416), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6420), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6424) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6444), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6448), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 6452)]

gen_decodes libsignalSessionCode_tree segCloneBinCli [(ls_off% "libsignal_cli_ratchet::decrypt_signal" + 9720) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 9800)]

end CryptoVerification.LibsignalTripleRatchet.Record
