/*
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
*/

// Unusual ELF layout: `r-x` text at the lowest `mmap_min_addr`-compatible address (`0x10000`) and
// `rw-` data + `.bss` above 4 GiB (`0x100002000`), leaving a ~4 GiB unmapped gap between them, so
// `brk` starts above 4 GiB.
.section .text, "ax", @progbits
.balign 4
.global _start
.type _start, %function
_start:
    movz x1, #0x0001, lsl #32
    movk x1, #0x2000
    ldr x2, [x1]
    str x2, [x1, #0x80]
    mov x0, #0
    mov x8, #94
    svc #0
.size _start, . - _start

.section .data, "aw", @progbits
.balign 16
hv_data:
    .quad 0x4849474856414444
    .fill 20, 4, 0x68686868

.section .bss, "aw", @nobits
.balign 16
hv_bss:
    .space 0x1800
