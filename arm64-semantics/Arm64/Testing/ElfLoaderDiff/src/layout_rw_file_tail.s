/*
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
*/

// Unusual ELF layout: an `rw-` segment with `p_filesz == p_memsz` (no `.bss`) ending mid-page,
// immediately followed in the file by a non-allocated `.rw_tail_marker` section (`0xfeedface`),
// so the trailing file bytes of the last page are mapped into the writable segment (no `padzero`).
.section .text, "ax", @progbits
.balign 4
.global _start
.type _start, %function
_start:
    adrp x1, ft_data
    add x1, x1, :lo12:ft_data
    ldr x2, [x1]
    str x2, [x1, #8]
    mov x0, #0
    mov x8, #94
    svc #0
.size _start, . - _start

.section .data, "aw", @progbits
.balign 8
.global ft_data
ft_data:
    .quad 0x7a7a7a7a01010101
    .quad 0
    .fill 18, 4, 0x3e3e3e3e

// Non-alloc section placed immediately after `.data` in the file.
.section .rw_tail_marker, "", @progbits
    .fill 64, 4, 0xfeedface
