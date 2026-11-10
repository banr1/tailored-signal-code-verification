/*
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
*/

.section .text.aux,"ax",@progbits
.globl adler32
.type adler32, @function
adler32:
  ret
.size adler32, .-adler32

.type dummy, @function
dummy:
  ret
.size dummy, .-dummy

.section .text.main,"ax",@progbits
.globl _start
.type _start, @function
_start:
  mov x8, #94
  mov x0, #0
  svc #0
.size _start, 0

.type __do_init, @function
__do_init:
  ret
.size __do_init, .-__do_init

.globl main
.type main, @function
main:
  mov w0, #0
  ret
.size main, .-main

.type __libc_malloc_impl, @function
__libc_malloc_impl:
  ret
.size __libc_malloc_impl, .-__libc_malloc_impl

.section .data,"aw",@progbits
.globl __malloc_context
.type __malloc_context, @object
.balign 8
__malloc_context:
  .quad 0
.size __malloc_context, 8
