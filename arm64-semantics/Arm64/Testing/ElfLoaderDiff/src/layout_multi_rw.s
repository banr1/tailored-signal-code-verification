/*
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
*/

// Unusual ELF layout #1: three separate RW PT_LOAD segments (pure data, mixed data+bss, pure bss)
// with unmapped multi-page gaps between them.
.section .rodata, "a", @progbits
.balign 16
.global ro_header
ro_header:
    .quad 0x1111222233334444
    .quad 0x5555666677778888

.section .text, "ax", @progbits
.balign 4
.global _start
.type _start, %function
_start:
    adrp x1, rw1_data
    add x1, x1, :lo12:rw1_data
    ldr x2, [x1]
    adrp x3, rw2_bss
    add x3, x3, :lo12:rw2_bss
    str x2, [x3]
    adrp x4, rw3_pure_bss
    add x4, x4, :lo12:rw3_pure_bss
    str x2, [x4]
    mov x0, #0
    mov x8, #94
    svc #0

.section .rw1_data, "aw", @progbits
.balign 16
.global rw1_data
rw1_data:
    .quad 0xaaaa0001bbbb0002
    .quad 0xcccc0003dddd0004
    .fill 60, 8, 0x0101010101010101

.section .rw2_data, "aw", @progbits
.balign 16
.global rw2_data
rw2_data:
    .quad 0xeeee0005ffff0006
    .fill 46, 8, 0x0202020202020202

.section .rw2_bss, "aw", @nobits
.balign 16
.global rw2_bss
rw2_bss:
    .space 5760

.section .rw3_bss, "aw", @nobits
.balign 16
.global rw3_pure_bss
rw3_pure_bss:
    .space 8192
