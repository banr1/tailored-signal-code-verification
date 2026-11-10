/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common
public import LibsignalBinary.Proofs.HookDischarge.RustStd.AllocShim
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Memrchr
public import LibsignalBinary.Proofs.HookDischarge.RustStd.FromUtf8
public import LibsignalBinary.Proofs.HookDischarge.RustStd.TimeDurationSince
public import LibsignalBinary.Proofs.HookDischarge.RustStd.TimeAdd

/-!
# Rust `core` / `std` CLI hook-discharge bridges

Umbrella module re-exporting bridge lemmas from `VerifiedLibraries.RustStd` (`core::slice::memchr::memrchr`,
`core::str::converts::from_utf8`, `<SystemTime>::duration_since`, and `<SystemTime as Add<Duration>>::add`)
to the `signal-session` CLI external hook contracts (`CliExt.*` and `LibsignalPublicApi.*`).

For `from_utf8` and `SystemTime::duration_since`, the compiled functions read immutable `.rodata`
tables (`corePlacedData1` and `timePlacedData0`), captured via `withRoData` / `withRoDataSep`.
-/
