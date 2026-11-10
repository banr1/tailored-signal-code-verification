/*
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
*/

// Unusual ELF layout #3: explicit `PT_PHDR`, `PT_NOTE`, `PT_TLS` (`.tdata` + `.tbss`),
// `PT_GNU_RELRO`, and `PT_GNU_STACK`.
.section .note.ABI-tag, "a", @note
.balign 4
    .long 4
    .long 16
    .long 1
    .asciz "GNU"
    .long 0
    .long 4
    .long 18
    .long 0

.section .rodata, "a", @progbits
.balign 16
.global ro_const
ro_const:
    .quad 0x9988776655443322

.section .text, "ax", @progbits
.balign 4
.global _start
.type _start, %function
_start:
    adrp x1, relro_const
    add x1, x1, :lo12:relro_const
    ldr x2, [x1]
    adrp x3, rw_var
    add x3, x3, :lo12:rw_var
    str x2, [x3]
    mov x0, #0
    mov x8, #94
    svc #0

.section .tdata, "awT", @progbits
.balign 16
.global tls_init_var
tls_init_var:
    .quad 0xaabbccddeeff0011
    .quad 0x2233445566778899
    .quad 0xdeadbeef00000001
    .quad 0xdeadbeef00000002

.section .tbss, "awT", @nobits
.balign 16
.global tls_zero_var
tls_zero_var:
    .space 96

.section .data.rel.ro, "aw", @progbits
.balign 16
.global relro_const
relro_const:
    .quad 0x4242424242424242
    .quad 0x2424242424242424

.section .data, "aw", @progbits
.balign 16
.global rw_var
rw_var:
    .quad 0x1000200030004000

.section .bss, "aw", @nobits
.balign 16
.global bss_var
bss_var:
    .space 128
