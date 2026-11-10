/*
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
*/

// Unusual ELF layout: a single `r-x` `PT_LOAD` (ELF header + program headers + `.rodata` +
// `.text`, `p_vaddr == p_offset == 0`) with no writable segment at all, so `brk` starts right after
// the only text page; `e_entry` lies in the middle of the segment, not at its start.
.section .rodata, "a", @progbits
.balign 8
.global text_only_msg
text_only_msg:
    .ascii "text-only static ET_EXEC\n"

.section .text, "ax", @progbits
.balign 4
helper:
    ret
    .fill 30, 4, 0xd503201f
.global _start
.type _start, %function
_start:
    ldr x1, [sp]
    adrp x2, text_only_msg
    add x2, x2, :lo12:text_only_msg
    ldrb w3, [x2]
    bl helper
    mov x0, #0
    mov x8, #94
    svc #0
.size _start, . - _start
