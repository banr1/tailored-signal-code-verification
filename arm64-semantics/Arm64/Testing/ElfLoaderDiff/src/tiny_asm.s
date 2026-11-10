/*
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
*/

// Tiny hand-written AArch64 static ET_EXEC assembly program for ELF loader differential testing.
.section .rodata, "a", @progbits
.balign 16
.global ro_magic
ro_magic:
    .quad 0x0102030405060708
    .quad 0x1122334455667788

.section .text, "ax", @progbits
.balign 4
.global _start
.type _start, %function
_start:
    ldr x1, [sp]
    adrp x2, ro_magic
    add x2, x2, :lo12:ro_magic
    ldr x3, [x2]
    adrp x4, rw_slot
    add x4, x4, :lo12:rw_slot
    str x3, [x4]
    adrp x5, bss_slot
    add x5, x5, :lo12:bss_slot
    str x1, [x5]
    mov x0, #0
    mov x8, #94
    svc #0
.size _start, . - _start

.section .data, "aw", @progbits
.balign 8
.global rw_slot
rw_slot:
    .quad 0xcafebabedeadbeef

.section .bss, "aw", @nobits
.balign 16
.global bss_slot
bss_slot:
    .space 64
