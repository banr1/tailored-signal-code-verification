/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Testing.Harness.ElfRun

/-!
# `elf_run` Executable Entry Point

Standalone CLI wrapper around `Testing.ElfRun.main`, kept separate so `Arm64.Testing.Harness.ElfRun`
can be imported as a library without defining a top-level `main`.
-/

public def main (args : List String) : IO UInt32 :=
  Testing.ElfRun.main args
