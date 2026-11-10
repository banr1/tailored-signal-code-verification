/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.ISA.State
public import Arm64.Trusted.Syscalls.Include.Errno

/-!
# Shared UAPI Helpers & Syscall Table Dispatcher (`Arm64.Trusted.Syscalls.Include.Uapi`)

- **Layer / Role**: `Arm64` Trusted Computing Base (`Role::Spec`, definitions only, 0 theorems).
- **Linux `7.3` Upstream Sources**:
  - `arch/arm64/kernel/syscall.c:55` (`el0_svc_common`: reads `X8` syscall number, `X0..X5` args,
    writes return value to `X0`)
  - `include/uapi/asm-generic/unistd.h` (AArch64 generic syscall numbering)
- **Purpose & Key Exports**: Single-thread process/thread ID (`SIM_TID`), 48-bit user virtual
  address space ceiling (`USER_VA_LIMIT`), per-call transfer cap (`MAX_RW_COUNT`), little-endian byte encoders (`leBytes32`, `leBytes64`),
  and explicit `(nr, handler)` table dispatch (`Syscall.dispatch`).
-/

@[expose] public section

namespace Arm64

/-- Deterministic process and thread ID (`1`) returned by single-thread identity syscalls
    (`[INTENTIONAL_SCOPE]`: `kernel/sys.c:966` `sys_getpid`, `kernel/sys.c:979` `sys_gettid`). -/
def SIM_TID : BitVec 64 := 1#64

/-- Upper bound of the 48-bit Linux AArch64 user virtual address space
    (`TASK_SIZE_64 = 2 ^ 48` under `CONFIG_ARM64_VA_BITS=48` / `TCR_EL1.T0SZ = 16` with 4 KiB
    pages, `arch/arm64/include/asm/memory.h:100`, `include/asm-generic/access_ok.h:31`
    `__access_ok`; `[INTENTIONAL_SCOPE]`: assumes a `VA_BITS=48` kernel rather than 39/42/47-bit VA
    configurations where `access_ok` rejects addresses in `[2 ^ VA_BITS, 2 ^ 48)` with `-EFAULT`). -/
def USER_VA_LIMIT : Nat := 2 ^ 48

/-- Largest byte count a single read or write transfers (`MAX_RW_COUNT = INT_MAX & PAGE_MASK =
    0x7ffff000`, `include/linux/fs.h:2447`). -/
def MAX_RW_COUNT : Nat := 0x7ffff000

/-- Serialize a 32-bit unsigned integer into 4 little-endian bytes. -/
def leBytes32 (v : BitVec 32) : List (BitVec 8) :=
  [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8]

/-- Serialize a 64-bit unsigned integer into 8 little-endian bytes. -/
def leBytes64 (v : BitVec 64) : List (BitVec 8) :=
  [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8,
   v.extractLsb' 32 8, v.extractLsb' 40 8, v.extractLsb' 48 8, v.extractLsb' 56 8]

namespace Syscall

/-- Dispatch a Linux AArch64 supervisor call (`SVC #0`, `arch/arm64/kernel/syscall.c:55`
    `el0_svc_common`) on `X8` over an explicit `(nr, handler)` table.
    - `[INTENTIONAL_SCOPE]`: Any syscall number absent from `table` fails closed with
      `.Exception "unmodeled syscall (svc)"`. -/
def dispatch (table : List (BitVec 64 × (State → State))) (s : State) : State :=
  match table.find? (·.1 == s.readReg64 Reg.x8) with
  | some (_, h) => h s
  | none        => s.setStatus (.Exception "unmodeled syscall (svc)")

end Syscall

end Arm64
