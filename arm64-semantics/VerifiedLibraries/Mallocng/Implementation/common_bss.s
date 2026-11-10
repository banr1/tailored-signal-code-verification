/*
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
*/

/* Zero-initialized .bss definitions for the five SHN_COMMON tentative symbols
 * referenced by musl 1.2.5's mallocng object members in Rust 1.98.1's bundled
 * aarch64-unknown-linux-musl self-contained/libc.a.
 *
 * Sizes, alignments, types, and HIDDEN visibility match readelf -sW libc.a
 * verbatim (no C code or instructions are compiled here). */

.section .bss.__libc,"aw",@nobits
.p2align 3
.globl __libc
.hidden __libc
.type __libc,@object
.size __libc,104
__libc:
.zero 104

.section .bss.__hwcap,"aw",@nobits
.p2align 3
.globl __hwcap
.hidden __hwcap
.type __hwcap,@object
.size __hwcap,8
__hwcap:
.zero 8

.section .bss.__malloc_lock,"aw",@nobits
.p2align 3
.globl __malloc_lock
.hidden __malloc_lock
.type __malloc_lock,@object
.size __malloc_lock,4
__malloc_lock:
.zero 4

.section .bss.__malloc_replaced,"aw",@nobits
.p2align 2
.globl __malloc_replaced
.hidden __malloc_replaced
.type __malloc_replaced,@object
.size __malloc_replaced,4
__malloc_replaced:
.zero 4

.section .bss.__aligned_alloc_replaced,"aw",@nobits
.p2align 2
.globl __aligned_alloc_replaced
.hidden __aligned_alloc_replaced
.type __aligned_alloc_replaced,@object
.size __aligned_alloc_replaced,4
__aligned_alloc_replaced:
.zero 4
