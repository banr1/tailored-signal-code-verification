/*
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
*/

// Unusual ELF layout #2: mid-page `p_vaddr` (`p_vaddr % 0x1000 != 0`) for both an `r-x` segment
// (`p_filesz == p_memsz`, where trailing file bytes in the same 4 KiB page are mapped) and an
// `rw-` segment (`p_filesz < p_memsz` ending mid-page and spanning multiple pages, where trailing
// file bytes in the file are zeroed by `padzero` / `zero_bss`).
.section .text, "ax", @progbits
.balign 4
.global _start
.type _start, %function
_start:
    adrp x1, mid_data
    add x1, x1, :lo12:mid_data
    ldr x2, [x1]
    adrp x3, mid_bss
    add x3, x3, :lo12:mid_bss
    str x2, [x3]
    mov x0, #0
    mov x8, #94
    svc #0
    .fill 64, 4, 0xd503201f

.section .mid_data, "aw", @progbits
.balign 8
.global mid_data
mid_data:
    .quad 0xdeadd00dcafef00d
    .quad 0x123456789abcdef0
    .fill 34, 8, 0x7777777777777777

.section .mid_bss, "aw", @nobits
.balign 8
.global mid_bss
mid_bss:
    .space 8928

// Non-alloc section placed immediately after `.mid_data` in the file so the file page containing
// `.mid_data` has non-zero bytes after `p_offset + p_filesz` that `padzero` must zero in memory.
.section .file_tail_marker, "", @progbits
    .fill 64, 8, 0xdeadbeefdeadbeef
