/*
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
*/

// Unusual ELF layout: every `PT_LOAD` has a non-page-aligned `p_vaddr` (congruent to `p_offset`
// mod 4 KiB) and straddles a 4 KiB page boundary: `r-x` `.text` and `r--` `.rodata` each cross
// one boundary, and the `rw-` segment's `.data` (`p_filesz`) crosses one boundary while its
// `.bss` (`p_memsz`) crosses another, so its last file page is partially zeroed by `padzero`.
.section .text, "ax", @progbits
.balign 4
.global _start
.type _start, %function
_start:
    adrp x1, st_ro
    add x1, x1, :lo12:st_ro
    ldr x2, [x1]
    adrp x3, st_bss
    add x3, x3, :lo12:st_bss
    str x2, [x3]
    mov x0, #0
    mov x8, #94
    svc #0
    .fill 120, 4, 0xd503201f
.size _start, . - _start

.section .rodata, "a", @progbits
.balign 8
.global st_ro
st_ro:
    .fill 48, 4, 0x77665544

.section .data, "aw", @progbits
.balign 8
.global st_data
st_data:
    .fill 96, 4, 0x13579bdf

.section .bss, "aw", @nobits
.balign 8
.global st_bss
st_bss:
    .space 4200
