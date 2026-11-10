/*
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
*/

// Unusual ELF layout: eight `PT_LOAD` segments in alternating permissions (`r--`, `r-x`, `r--`,
// `rw-`, `r--`, `r-x`, `rw-` data+bss, `rw-` pure bss) on distinct 4 KiB pages, several of which
// share a file page, with unmapped gap pages between some of them; `e_entry` is in the second
// `r-x` segment.
.section .ro1, "a", @progbits
.balign 8
    .quad 0x1010101010101010

.section .text1, "ax", @progbits
.balign 4
.global helper1
helper1:
    ret

.section .ro2, "a", @progbits
.balign 8
.global ml_ro2
ml_ro2:
    .quad 0x2020202020202020
    .fill 13, 4, 0x2a2a2a2a

.section .rw1, "aw", @progbits
.balign 8
.global ml_rw1
ml_rw1:
    .quad 0x3030303030303030

.section .ro3, "a", @progbits
.balign 8
    .fill 33, 4, 0x40404040

.section .text2, "ax", @progbits
.balign 4
.global _start
.type _start, %function
_start:
    bl helper1
    adrp x1, ml_ro2
    add x1, x1, :lo12:ml_ro2
    ldr x2, [x1]
    adrp x3, ml_rw1
    add x3, x3, :lo12:ml_rw1
    str x2, [x3]
    adrp x4, ml_bss2
    add x4, x4, :lo12:ml_bss2
    str x2, [x4]
    mov x0, #0
    mov x8, #94
    svc #0
.size _start, . - _start

.section .rw2, "aw", @progbits
.balign 8
    .fill 5, 4, 0x50505050

.section .bss2, "aw", @nobits
.balign 8
.global ml_bss2
ml_bss2:
    .space 300

.section .bss3, "aw", @nobits
.balign 16
    .space 5000
