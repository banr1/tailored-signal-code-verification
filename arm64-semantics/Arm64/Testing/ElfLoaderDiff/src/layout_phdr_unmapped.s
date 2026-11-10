/*
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
*/

// Unusual ELF layout: the ELF header and program header table (`e_phoff`) are not covered by any
// `PT_LOAD` (no `FILEHDR`/`PHDRS`, no `PT_PHDR`); every segment is page-aligned and the
// read-only data segment (`r--`) comes after the text segment (`r-x`) rather than before it.
.section .text, "ax", @progbits
.balign 4
.global _start
.type _start, %function
_start:
    adrp x1, pu_ro
    add x1, x1, :lo12:pu_ro
    ldr x2, [x1]
    adrp x3, pu_data
    add x3, x3, :lo12:pu_data
    str x2, [x3, #8]
    mov x0, #0
    mov x8, #94
    svc #0
.size _start, . - _start

.section .rodata, "a", @progbits
.balign 16
.global pu_ro
pu_ro:
    .quad 0x5555aaaa5555aaaa
    .fill 40, 4, 0x0c0c0c0c

.section .data, "aw", @progbits
.balign 16
.global pu_data
pu_data:
    .quad 0x1234
    .quad 0
