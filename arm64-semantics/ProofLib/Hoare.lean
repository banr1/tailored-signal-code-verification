/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.Loop
public import ProofLib.Hoare.Safety
public import ProofLib.Hoare.SafeReaches
public import ProofLib.Hoare.Hooks
public import ProofLib.Hoare.SubroutineHook
public import ProofLib.LibcHooks
public import ProofLib.Hoare.LibcHooks
public import ProofLib.Hoare.HookMap
public import ProofLib.Hoare.FnPtr
public import ProofLib.Hoare.SubroutineOk
public import ProofLib.Hoare.TraceEq
public import ProofLib.Hoare.WithPure

/-!
# Hoare Logic Infrastructure

Re-exports loop invariants, step-indexed partial-correctness safety, reachability combinators,
external-hook combinators, subroutine-to-hook lifting, function-pointer reasoning, and standard
libc and allocator hook contracts.
-/

@[expose] public section
