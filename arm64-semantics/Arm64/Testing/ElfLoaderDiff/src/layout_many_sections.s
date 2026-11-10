/*
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
*/

// Many small input sections: 40 one-function `.fnNN` sections (each a distinct output section and
// an `STT_FUNC` symbol in the unstripped `.symtab`) and 30 odd-sized `.dNN` data/rodata sections
// with mixed alignments, linked without a linker script (`ld.lld` default orphan placement).

.section .fn00, "ax", @progbits
.balign 4
.global fn00
.type fn00, %function
fn00:
    ret
.size fn00, . - fn00

.section .fn01, "ax", @progbits
.balign 8
.global fn01
.type fn01, %function
fn01:
    nop
    ret
.size fn01, . - fn01

.section .fn02, "ax", @progbits
.balign 16
.global fn02
.type fn02, %function
fn02:
    nop
    nop
    ret
.size fn02, . - fn02

.section .fn03, "ax", @progbits
.balign 32
.global fn03
.type fn03, %function
fn03:
    nop
    nop
    nop
    ret
.size fn03, . - fn03

.section .fn04, "ax", @progbits
.balign 4
.global fn04
.type fn04, %function
fn04:
    nop
    nop
    nop
    nop
    ret
.size fn04, . - fn04

.section .fn05, "ax", @progbits
.balign 8
.global fn05
.type fn05, %function
fn05:
    ret
.size fn05, . - fn05

.section .fn06, "ax", @progbits
.balign 16
.global fn06
.type fn06, %function
fn06:
    nop
    ret
.size fn06, . - fn06

.section .fn07, "ax", @progbits
.balign 32
.global fn07
.type fn07, %function
fn07:
    nop
    nop
    ret
.size fn07, . - fn07

.section .fn08, "ax", @progbits
.balign 4
.global fn08
.type fn08, %function
fn08:
    nop
    nop
    nop
    ret
.size fn08, . - fn08

.section .fn09, "ax", @progbits
.balign 8
.global fn09
.type fn09, %function
fn09:
    nop
    nop
    nop
    nop
    ret
.size fn09, . - fn09

.section .fn10, "ax", @progbits
.balign 16
.global fn10
.type fn10, %function
fn10:
    ret
.size fn10, . - fn10

.section .fn11, "ax", @progbits
.balign 32
.global fn11
.type fn11, %function
fn11:
    nop
    ret
.size fn11, . - fn11

.section .fn12, "ax", @progbits
.balign 4
.global fn12
.type fn12, %function
fn12:
    nop
    nop
    ret
.size fn12, . - fn12

.section .fn13, "ax", @progbits
.balign 8
.global fn13
.type fn13, %function
fn13:
    nop
    nop
    nop
    ret
.size fn13, . - fn13

.section .fn14, "ax", @progbits
.balign 16
.global fn14
.type fn14, %function
fn14:
    nop
    nop
    nop
    nop
    ret
.size fn14, . - fn14

.section .fn15, "ax", @progbits
.balign 32
.global fn15
.type fn15, %function
fn15:
    ret
.size fn15, . - fn15

.section .fn16, "ax", @progbits
.balign 4
.global fn16
.type fn16, %function
fn16:
    nop
    ret
.size fn16, . - fn16

.section .fn17, "ax", @progbits
.balign 8
.global fn17
.type fn17, %function
fn17:
    nop
    nop
    ret
.size fn17, . - fn17

.section .fn18, "ax", @progbits
.balign 16
.global fn18
.type fn18, %function
fn18:
    nop
    nop
    nop
    ret
.size fn18, . - fn18

.section .fn19, "ax", @progbits
.balign 32
.global fn19
.type fn19, %function
fn19:
    nop
    nop
    nop
    nop
    ret
.size fn19, . - fn19

.section .fn20, "ax", @progbits
.balign 4
.global fn20
.type fn20, %function
fn20:
    ret
.size fn20, . - fn20

.section .fn21, "ax", @progbits
.balign 8
.global fn21
.type fn21, %function
fn21:
    nop
    ret
.size fn21, . - fn21

.section .fn22, "ax", @progbits
.balign 16
.global fn22
.type fn22, %function
fn22:
    nop
    nop
    ret
.size fn22, . - fn22

.section .fn23, "ax", @progbits
.balign 32
.global fn23
.type fn23, %function
fn23:
    nop
    nop
    nop
    ret
.size fn23, . - fn23

.section .fn24, "ax", @progbits
.balign 4
.global fn24
.type fn24, %function
fn24:
    nop
    nop
    nop
    nop
    ret
.size fn24, . - fn24

.section .fn25, "ax", @progbits
.balign 8
.global fn25
.type fn25, %function
fn25:
    ret
.size fn25, . - fn25

.section .fn26, "ax", @progbits
.balign 16
.global fn26
.type fn26, %function
fn26:
    nop
    ret
.size fn26, . - fn26

.section .fn27, "ax", @progbits
.balign 32
.global fn27
.type fn27, %function
fn27:
    nop
    nop
    ret
.size fn27, . - fn27

.section .fn28, "ax", @progbits
.balign 4
.global fn28
.type fn28, %function
fn28:
    nop
    nop
    nop
    ret
.size fn28, . - fn28

.section .fn29, "ax", @progbits
.balign 8
.global fn29
.type fn29, %function
fn29:
    nop
    nop
    nop
    nop
    ret
.size fn29, . - fn29

.section .fn30, "ax", @progbits
.balign 16
.global fn30
.type fn30, %function
fn30:
    ret
.size fn30, . - fn30

.section .fn31, "ax", @progbits
.balign 32
.global fn31
.type fn31, %function
fn31:
    nop
    ret
.size fn31, . - fn31

.section .fn32, "ax", @progbits
.balign 4
.global fn32
.type fn32, %function
fn32:
    nop
    nop
    ret
.size fn32, . - fn32

.section .fn33, "ax", @progbits
.balign 8
.global fn33
.type fn33, %function
fn33:
    nop
    nop
    nop
    ret
.size fn33, . - fn33

.section .fn34, "ax", @progbits
.balign 16
.global fn34
.type fn34, %function
fn34:
    nop
    nop
    nop
    nop
    ret
.size fn34, . - fn34

.section .fn35, "ax", @progbits
.balign 32
.global fn35
.type fn35, %function
fn35:
    ret
.size fn35, . - fn35

.section .fn36, "ax", @progbits
.balign 4
.global fn36
.type fn36, %function
fn36:
    nop
    ret
.size fn36, . - fn36

.section .fn37, "ax", @progbits
.balign 8
.global fn37
.type fn37, %function
fn37:
    nop
    nop
    ret
.size fn37, . - fn37

.section .fn38, "ax", @progbits
.balign 16
.global fn38
.type fn38, %function
fn38:
    nop
    nop
    nop
    ret
.size fn38, . - fn38

.section .fn39, "ax", @progbits
.balign 32
.global fn39
.type fn39, %function
fn39:
    nop
    nop
    nop
    nop
    ret
.size fn39, . - fn39

.section .d00, "a", @progbits
.balign 1
ro00:
    .fill 3, 1, 17

.section .d01, "aw", @progbits
.balign 2
data01:
    .fill 10, 1, 18

.section .d02, "aw", @progbits
.balign 4
data02:
    .fill 17, 1, 19

.section .d03, "a", @progbits
.balign 8
ro03:
    .fill 24, 1, 20

.section .d04, "aw", @progbits
.balign 16
data04:
    .fill 31, 1, 21

.section .d05, "aw", @progbits
.balign 1
data05:
    .fill 38, 1, 22

.section .d06, "a", @progbits
.balign 2
ro06:
    .fill 45, 1, 23

.section .d07, "aw", @progbits
.balign 4
data07:
    .fill 52, 1, 24

.section .d08, "aw", @progbits
.balign 8
data08:
    .fill 59, 1, 25

.section .d09, "a", @progbits
.balign 16
ro09:
    .fill 66, 1, 26

.section .d10, "aw", @progbits
.balign 1
data10:
    .fill 73, 1, 27

.section .d11, "aw", @progbits
.balign 2
data11:
    .fill 80, 1, 28

.section .d12, "a", @progbits
.balign 4
ro12:
    .fill 87, 1, 29

.section .d13, "aw", @progbits
.balign 8
data13:
    .fill 94, 1, 30

.section .d14, "aw", @progbits
.balign 16
data14:
    .fill 101, 1, 31

.section .d15, "a", @progbits
.balign 1
ro15:
    .fill 108, 1, 32

.section .d16, "aw", @progbits
.balign 2
data16:
    .fill 115, 1, 33

.section .d17, "aw", @progbits
.balign 4
data17:
    .fill 122, 1, 34

.section .d18, "a", @progbits
.balign 8
ro18:
    .fill 129, 1, 35

.section .d19, "aw", @progbits
.balign 16
data19:
    .fill 136, 1, 36

.section .d20, "aw", @progbits
.balign 1
data20:
    .fill 143, 1, 37

.section .d21, "a", @progbits
.balign 2
ro21:
    .fill 150, 1, 38

.section .d22, "aw", @progbits
.balign 4
data22:
    .fill 157, 1, 39

.section .d23, "aw", @progbits
.balign 8
data23:
    .fill 164, 1, 40

.section .d24, "a", @progbits
.balign 16
ro24:
    .fill 171, 1, 41

.section .d25, "aw", @progbits
.balign 1
data25:
    .fill 178, 1, 42

.section .d26, "aw", @progbits
.balign 2
data26:
    .fill 185, 1, 43

.section .d27, "a", @progbits
.balign 4
ro27:
    .fill 192, 1, 44

.section .d28, "aw", @progbits
.balign 8
data28:
    .fill 199, 1, 45

.section .d29, "aw", @progbits
.balign 16
data29:
    .fill 206, 1, 46

.section .bss, "aw", @nobits
.balign 16
ms_bss:
    .space 777

.section .text, "ax", @progbits
.balign 4
.global _start
.type _start, %function
_start:
    bl fn00
    bl fn07
    bl fn14
    bl fn21
    bl fn28
    bl fn35
    mov x0, #0
    mov x8, #94
    svc #0
.size _start, . - _start
