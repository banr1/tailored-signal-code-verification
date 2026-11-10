/*
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
*/

// Unusual ELF layout: an `rw-` segment starting mid-page whose `.data` (`p_filesz`) ends mid-page
// and whose `.bss` is padded so that `p_vaddr + p_memsz` ends exactly on a 4 KiB page boundary
// (no fractional `.bss` page after the last anonymous page).
.section .text, "ax", @progbits
.balign 4
.global _start
.type _start, %function
_start:
    adrp x1, pe_data
    add x1, x1, :lo12:pe_data
    ldr x2, [x1]
    adrp x3, pe_bss
    add x3, x3, :lo12:pe_bss
    str x2, [x3]
    mov x0, #0
    mov x8, #94
    svc #0
.size _start, . - _start

.section .data, "aw", @progbits
.balign 16
.global pe_data
pe_data:
    .quad 0x1122334455667788
    .fill 45, 4, 0x3c3c3c3c

.section .bss, "aw", @nobits
.balign 16
.global pe_bss
pe_bss:
    .space 4100
