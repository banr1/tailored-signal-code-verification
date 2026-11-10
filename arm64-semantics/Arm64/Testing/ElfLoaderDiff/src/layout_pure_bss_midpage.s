/*
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
*/

// Unusual ELF layout: a pure-`.bss` `rw-` `PT_LOAD` (`p_filesz == 0 < p_memsz`) whose `p_vaddr`
// starts mid-page (`0x...a40`) and ends mid-page, separate from a page-aligned `rw-` `.data`
// segment (`p_filesz == p_memsz`), with an unmapped page between them.
.section .text, "ax", @progbits
.balign 4
.global _start
.type _start, %function
_start:
    adrp x1, pb_data
    add x1, x1, :lo12:pb_data
    ldr x2, [x1]
    adrp x3, pb_bss
    add x3, x3, :lo12:pb_bss
    str x2, [x3]
    mov x0, #0
    mov x8, #94
    svc #0
.size _start, . - _start

.section .data, "aw", @progbits
.balign 16
.global pb_data
pb_data:
    .quad 0x0badc0de0badc0de
    .fill 6, 4, 0x01020304

.section .pure_bss, "aw", @nobits
.balign 16
.global pb_bss
pb_bss:
    .space 0x2345
