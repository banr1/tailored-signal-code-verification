/*
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
*/

// Unusual ELF layout: an `rw-` segment whose `.data` (`p_offset + p_filesz`, filled with a
// non-zero pattern) ends exactly on a 4 KiB page boundary, followed by a 24-byte `.bss` that
// spills just past it, so `padzero` has no fractional file page to clear and the single `.bss`
// page is purely anonymous.
.section .text, "ax", @progbits
.balign 4
.global _start
.type _start, %function
_start:
    adrp x1, fe_data
    add x1, x1, :lo12:fe_data
    ldr x2, [x1]
    adrp x3, fe_bss
    add x3, x3, :lo12:fe_bss
    str x2, [x3]
    mov x0, #0
    mov x8, #94
    svc #0
.size _start, . - _start

.section .data, "aw", @progbits
.balign 16
.global fe_data
fe_data:
    .quad 0x8877665544332211
    .fill 100, 4, 0x6d6d6d6d

.section .bss, "aw", @nobits
.balign 8
.global fe_bss
fe_bss:
    .space 24
