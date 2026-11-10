/*
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
*/

// Linker-default (no linker script) four-segment layout (`r--` headers + `.rodata`, `r-x`
// `.text`, `rw-` `.data` + `.bss`) linked three times with different `-z max-page-size` values
// (`0x1000`, `0x4000`, `0x200000`), which changes `p_align`, the `p_vaddr` of every segment after
// the first, and how many file pages segments share.
.section .rodata, "a", @progbits
.balign 16
.global pa_ro
pa_ro:
    .quad 0x0a0b0c0d0e0f1011
    .fill 70, 4, 0x2f2f2f2f

.section .text, "ax", @progbits
.balign 4
.global _start
.type _start, %function
_start:
    adrp x1, pa_ro
    add x1, x1, :lo12:pa_ro
    ldr x2, [x1]
    adrp x3, pa_data
    add x3, x3, :lo12:pa_data
    str x2, [x3]
    adrp x4, pa_bss
    add x4, x4, :lo12:pa_bss
    str x2, [x4]
    mov x0, #0
    mov x8, #94
    svc #0
.size _start, . - _start

.section .data, "aw", @progbits
.balign 16
.global pa_data
pa_data:
    .quad 0
    .fill 90, 4, 0x4b4b4b4b

.section .bss, "aw", @nobits
.balign 16
.global pa_bss
pa_bss:
    .space 6000
