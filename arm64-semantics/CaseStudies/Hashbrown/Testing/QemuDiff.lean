/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Std.Data.HashMap
public import Arm64.Trusted.Process
public import ProofLib.Process
public import CaseStudies.Hashbrown.Spec.Top
public import CaseStudies.Hashbrown.Testing.StdCliExecCheck

/-!
# Differential `qemu-aarch64` Conformance for `hashbrown_cli.elf` (`CaseStudies.Hashbrown.Testing.QemuDiff`)

- **Layer / Role**: Campaign E2E differential test (`Lib::Testing`, `Role::Test`).
- **Purpose & Key Exports**: Compares `CaseStudies/Hashbrown/Implementation/hashbrown_cli.elf`
  against `qemu-aarch64` and a pure `Std.HashMap` oracle across all 8 CLI commands (`insert`, `get`,
  `remove`, `contains`, `with_capacity`, `len`, `is_empty`, `clear`), malformed command skipping
  (including `with_capacity 4097`), overlong line rejection (`> 4096` B), and multi-resize table
  growth (`checkHashbrownCliVsQemuIO`, `buildHashbrownGrowthWorkload`).
-/

@[expose] public section

namespace CaseStudies.Hashbrown.Testing

open Arm64
open Arm64.Process
open ProofLib

def resolveRepoFilePath (rel : System.FilePath) : IO System.FilePath := do
  if rel.isAbsolute then return rel
  if ← rel.pathExists then return rel
  let fromSubpkg := System.FilePath.mk "../.." / rel
  if ← fromSubpkg.pathExists then return fromSubpkg
  return rel

def closeInheritedFdsCmd : String :=
  "for fd in /proc/self/fd/*; do f=\"${fd##*/}\"; case \"$f\" in 0|1|2) ;; *) eval \"exec ${f}>&-\" 2>/dev/null || true ;; esac; done"

/-- Run `elfPath` under `qemu-aarch64` inside a fresh temporary directory with `stdinStr` piped to
    `fd 0`, capturing `(exitCode, stdoutBytes, stderrBytes)` cleanly with core dumps disabled. -/
def runQemuWithStdin (elfPath : String) (extraArgs : List String) (stdinStr : String) :
    IO (Option (Nat × List (BitVec 8) × List (BitVec 8))) := do
  let absElf ← IO.FS.realPath (← resolveRepoFilePath elfPath)
  let absFetchQemu ← IO.FS.realPath (← resolveRepoFilePath "scripts/fetch-qemu-aarch64")
  let quotedArgs := String.intercalate " " ((absElf.toString :: extraArgs).map fun s => "\"" ++ s ++ "\"")
  let tmpDirRes ← IO.Process.output { cmd := "mktemp", args := #["-d"] }
  let tmpDir := tmpDirRes.stdout.trimAscii.toString
  if tmpDir.isEmpty then return none
  let inFile := tmpDir ++ "/stdin.bin"
  let outFile := tmpDir ++ "/stdout.bin"
  let errFile := tmpDir ++ "/stderr.bin"
  IO.FS.writeFile inFile stdinStr
  let script :=
    s!"cd \"{tmpDir}\" && ulimit -c 0 && {closeInheritedFdsCmd} && " ++
    s!"QEMU=\"$(command -v qemu-aarch64 || \"{absFetchQemu}\")\" && " ++
    s!"\"$QEMU\" {quotedArgs} <\"{inFile}\" >\"{outFile}\" 2>\"{errFile}\"; printf '%u' \"$?\""
  let res ← IO.Process.output { cmd := "bash", args := #["-c", script] }
  let outBytes ← IO.FS.readBinFile outFile
  let errBytes ← IO.FS.readBinFile errFile
  let _ ← IO.Process.output { cmd := "rm", args := #["-rf", tmpDir] }
  match res.stdout.trimAscii.toString.toNat? with
  | some code =>
    return some (
      code,
      outBytes.toList.map fun b => BitVec.ofNat 8 b.toNat,
      errBytes.toList.map fun b => BitVec.ofNat 8 b.toNat)
  | none =>
    return none

/-- Construct a deterministic multi-resize `hashbrown_cli` workload (`1,950` `insert`s, `650`
    `remove`s, and `350` `get`s across `1,600` distinct 64-bit keys) together with the exact
    reference `stdout` byte stream computed against a pure `Std.HashMap UInt64 UInt64` oracle. -/
def buildHashbrownGrowthWorkload : String × List (BitVec 8) := Id.run do
  let keyOf (i : Nat) : UInt64 :=
    match i with
    | 0 => 0
    | 1 => 1
    | 2 => 0x100000000
    | 3 => 0x8000000000000000
    | 4 => 0xffffffffffffffff
    | _ => (((i * 79193 + 123457) % 10000000) + 2).toUInt64
  let mut inLines : Array String := Array.mkEmpty 3000
  let mut outLines : Array String := Array.mkEmpty 400
  let mut refMap : Std.HashMap UInt64 UInt64 := {}
  for i in [0:950] do
    let k := keyOf i
    let v := (i * 131 + 7).toUInt64
    inLines := inLines.push s!"insert {k} {v}\n"
    refMap := refMap.insert k v
  for i in [0:50] do
    let k := keyOf i
    let v := (i * 977 + 50000).toUInt64
    inLines := inLines.push s!"insert {k} {v}\n"
    refMap := refMap.insert k v
  for i in [150:750] do
    let k := keyOf i
    inLines := inLines.push s!"remove {k}\n"
    refMap := refMap.erase k
  for i in [1550:1600] do
    let k := keyOf i
    inLines := inLines.push s!"remove {k}\n"
    refMap := refMap.erase k
  for i in [125:175] do
    let k := keyOf i
    inLines := inLines.push s!"get {k}\n"
    match refMap.get? k with
    | some v => outLines := outLines.push s!"{v}\n"
    | none   => outLines := outLines.push "none\n"
  for i in [150:450] do
    let k := keyOf i
    let v := (i * 353 + 900000).toUInt64
    inLines := inLines.push s!"insert {k} {v}\n"
    refMap := refMap.insert k v
  for i in [950:1550] do
    let k := keyOf i
    let v := (i * 257 + 19).toUInt64
    inLines := inLines.push s!"insert {k} {v}\n"
    refMap := refMap.insert k v
  for i in [750:800] do
    let k := keyOf i
    let v := (i * 613 + 700000).toUInt64
    inLines := inLines.push s!"insert {k} {v}\n"
    refMap := refMap.insert k v
  for step in [0:300] do
    let i := (step * 5) + (step % 5)
    let k := keyOf i
    inLines := inLines.push s!"get {k}\n"
    match refMap.get? k with
    | some v => outLines := outLines.push s!"{v}\n"
    | none   => outLines := outLines.push "none\n"
  let stdinStr := String.intercalate "" inLines.toList
  let expectedOut := bytesOfString (String.intercalate "" outLines.toList)
  (stdinStr, expectedOut)

/-- Differential conformance test comparing `hashbrown_cli.elf` under `qemu-aarch64` against the
    expected `HashbrownCliPost` outputs across all 8 CLI commands, malformed command skipping
    (including `with_capacity 4097`), overlong line rejection (`> 4096` bytes -> `exit 1`), and
    `1,950`-insert multi-resize table growth. -/
def checkHashbrownCliVsQemuIO : IO Bool := do
  let elfPath ← resolveRepoFilePath "CaseStudies/Hashbrown/Implementation/hashbrown_cli.elf"
  let validStr :=
    "is_empty\nlen\nwith_capacity 16\nis_empty\ninsert 42 100\nis_empty\nlen\n" ++
    "contains 42\ncontains 7\nget 42\ninsert 42 999\nget 42\nremove 42\n" ++
    "contains 42\nget 42\nremove 7\ninsert 1 10\ninsert 2 20\nlen\nclear\nlen\nis_empty\nget 1\n"
  let expectedValidOut :=
    bytesOfString "true\n0\ntrue\nfalse\n1\ntrue\nfalse\n100\n999\nfalse\nnone\n2\n0\ntrue\nnone\n"
  let badStr := "insert 42 100\nnot_a_cmd\nwith_capacity 4097\nget 42\n"
  let expectedBadOut := bytesOfString "100\n"
  let expectedBadErr := bytesOfString "error: invalid command\nerror: invalid command\n"
  let overlongStr := "insert 42 100\nget 42\n" ++ String.ofList (List.replicate 4097 'x') ++ "\n"
  let expectedOverlongErr := bytesOfString "error: line too long\n"
  let (growthStr, expectedGrowthOut) := buildHashbrownGrowthWorkload
  let qValid?  ← runQemuWithStdin elfPath.toString [] validStr
  let qBad?    ← runQemuWithStdin elfPath.toString [] badStr
  let qLong?   ← runQemuWithStdin elfPath.toString [] overlongStr
  let qGrowth? ← runQemuWithStdin elfPath.toString [] growthStr
  match qValid?, qBad?, qLong?, qGrowth? with
  | some (qvCode, qvOut, qvErr), some (qbCode, qbOut, qbErr),
    some (qlCode, qlOut, qlErr), some (qgCode, qgOut, qgErr) =>
    return (
      qvCode == 0 && qvOut == expectedValidOut && qvErr == [] &&
      qbCode == 0 && qbOut == expectedBadOut && qbErr == expectedBadErr &&
      qlCode == 1 && qlOut == [] && qlErr == expectedOverlongErr &&
      qgCode == 0 && qgOut == expectedGrowthOut && qgErr == [])
  | _, _, _, _ =>
    return false

end CaseStudies.Hashbrown.Testing
