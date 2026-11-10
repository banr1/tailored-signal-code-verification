/*
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
*/

// Unusual ELF layout: a 3-page `r-x` segment whose `e_entry` is on its third page (not at the
// segment start), preceded by a separate `r--` header + `.rodata` segment and followed by an `rw-`
// segment.
.section .rodata, "a", @progbits
.balign 8
.global deep_ro
deep_ro:
    .quad 0x7e7e7e7e00c0ffee

.section .text.cold, "ax", @progbits
.balign 4
.global cold_path
cold_path:
    ret
    // 2.5 pages of filler (`nop`) pushing `_start` onto the third text page.
    .fill 2560, 4, 0xd503201f

.section .text.entry, "ax", @progbits
.balign 4
.global _start
.type _start, %function
_start:
    bl cold_path
    adrp x1, deep_data
    add x1, x1, :lo12:deep_data
    ldr x2, [x1]
    str x2, [x1, #8]
    mov x0, #0
    mov x8, #94
    svc #0
.size _start, . - _start

.section .data, "aw", @progbits
.balign 16
.global deep_data
deep_data:
    .quad 0x0123456789abcdef
    .quad 0
    .fill 60, 4, 0x5a5a5a5a

.section .bss, "aw", @nobits
.balign 16
deep_bss:
    .space 1000
