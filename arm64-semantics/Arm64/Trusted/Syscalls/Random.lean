/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Syscalls.Common
public import Arm64.Trusted.Syscalls.Drivers.Random

/-!
# Entropy Syscalls

Re-exports `Arm64.Trusted.Syscalls.Drivers.Random` (`drivers/char/random.c`: `getrandom`) and
defines the single-syscall dispatch table `Syscall.randomTable` and handler `Syscall.random`.
-/

@[expose] public section

namespace Arm64

namespace Syscall

/-- Dispatch table for kernel randomness (`getrandom`). -/
def randomTable : List (BitVec 64 × (State → State)) :=
  [(SYS_GETRANDOM, execGetrandom)]

/-- Syscall bundle permitting `getrandom`. -/
def random : State → State := dispatch randomTable

end Syscall

end Arm64
