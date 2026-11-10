/*
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
*/

// Unusual ELF layout: an `rw-` segment starting mid-page with a small `.data` and a large
// (1 MiB + 0x234 B) `.bss`, so `p_memsz` spans 258 pages of which 257 are anonymous and the
// segment ends mid-page.
.section .rodata, "a", @progbits
.balign 8
lb_ro:
    .quad 0x00000000deadf00d

.section .text, "ax", @progbits
.balign 4
.global _start
.type _start, %function
_start:
    adrp x1, lb_data
    add x1, x1, :lo12:lb_data
    ldr x2, [x1]
    adrp x3, lb_bss_end
    add x3, x3, :lo12:lb_bss_end
    str x2, [x3, #-8]
    mov x0, #0
    mov x8, #94
    svc #0
.size _start, . - _start

.section .data, "aw", @progbits
.balign 16
.global lb_data
lb_data:
    .quad 0x0f0e0d0c0b0a0908
    .fill 20, 4, 0x11223344

.section .bss, "aw", @nobits
.balign 16
lb_bss:
    .space 0x100234
.global lb_bss_end
lb_bss_end:
