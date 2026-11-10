// Copyright (c) The Rust Project Contributors.
// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Disassembly of code compiled from the Rust standard library 1.98.1
// (https://github.com/rust-lang/rust/tree/1.98.1/library/std): the `__rdl_*` functions of
// `std::alloc::__default_lib_allocator` (`library/std/src/alloc.rs`), inlining
// `std::sys::alloc::unix` (`library/std/src/sys/alloc/{unix,mod}.rs`), plus 1-instruction
// `b __rdl_*` thunks for rustc's `__rust_*` allocator-shim symbols. See
// `third_party/libsignal/README.md`.
//
// Exact rustc 1.98.1 libstd::sys::alloc::unix rdl shims + 1-insn B thunks
// Matches VerifiedLibraries.RustStd.Proofs.MallocngBridgeCommon (rdlAllocInstrs, rdlDeallocInstrs, rdlReallocInstrs)
// and VerifiedLibraries.RustStd.Proofs.MallocngBridge (RustStdThunkCode).

.section .text.__rdl_alloc,"ax",@progbits
.p2align 2
.globl __rdl_alloc
.type __rdl_alloc, @function
__rdl_alloc:
    cmp x1, #0x10
    mov x2, x0
    b.hi .Lalloc_aligned
    cmp x1, x2
    b.hi .Lalloc_aligned
    mov x0, x2
    b malloc
.Lalloc_aligned:
    sub sp, sp, #0x20
    stp x29, x30, [sp, #0x10]
    add x29, sp, #0x10
    cmp x1, #0x8
    mov w8, #0x8
    add x0, sp, #0x8
    csel x1, x1, x8, hi
    str xzr, [sp, #0x8]
    bl posix_memalign
    ldr x8, [sp, #0x8]
    cmp w0, #0x0
    csel x0, x8, xzr, eq
    ldp x29, x30, [sp, #0x10]
    add sp, sp, #0x20
    ret
.size __rdl_alloc, .-__rdl_alloc

.section .text.__rdl_dealloc,"ax",@progbits
.p2align 2
.globl __rdl_dealloc
.type __rdl_dealloc, @function
__rdl_dealloc:
    b free
.size __rdl_dealloc, .-__rdl_dealloc

.section .text.__rdl_realloc,"ax",@progbits
.p2align 2
.globl __rdl_realloc
.type __rdl_realloc, @function
__rdl_realloc:
    sub sp, sp, #0x40
    stp x29, x30, [sp, #0x10]
    stp x22, x21, [sp, #0x20]
    stp x20, x19, [sp, #0x30]
    add x29, sp, #0x10
    mov x19, x3
    mov x20, x1
    cmp x2, #0x10
    b.hi .Lrealloc_aligned
    cmp x2, x19
    b.hi .Lrealloc_aligned
    mov x1, x19
    ldp x20, x19, [sp, #0x30]
    ldp x22, x21, [sp, #0x20]
    ldp x29, x30, [sp, #0x10]
    add sp, sp, #0x40
    b realloc
.Lrealloc_aligned:
    cmp x2, #0x8
    mov w8, #0x8
    mov x22, x0
    csel x1, x2, x8, hi
    add x0, sp, #0x8
    mov x2, x19
    str xzr, [sp, #0x8]
    bl posix_memalign
    mov w8, w0
    mov x0, xzr
    cbnz w8, .Lrealloc_done
    ldr x21, [sp, #0x8]
    cbz x21, .Lrealloc_done
    cmp x19, x20
    mov x0, x21
    mov x1, x22
    csel x2, x19, x20, lo
    bl memcpy
    mov x0, x22
    bl free
    mov x0, x21
.Lrealloc_done:
    ldp x20, x19, [sp, #0x30]
    ldp x22, x21, [sp, #0x20]
    ldp x29, x30, [sp, #0x10]
    add sp, sp, #0x40
    ret
.size __rdl_realloc, .-__rdl_realloc

.section .text.__rdl_alloc_zeroed,"ax",@progbits
.p2align 2
.globl __rdl_alloc_zeroed
.type __rdl_alloc_zeroed, @function
__rdl_alloc_zeroed:
    sub sp, sp, #0x30
    stp x29, x30, [sp, #0x10]
    stp x20, x19, [sp, #0x20]
    add x29, sp, #0x10
    cmp x1, #0x10
    mov x19, x0
    b.hi .Lzeroed_aligned
    cmp x1, x19
    b.hi .Lzeroed_aligned
    mov x0, x19
    mov w1, #0x1
    ldp x20, x19, [sp, #0x20]
    ldp x29, x30, [sp, #0x10]
    add sp, sp, #0x30
    b calloc
.Lzeroed_aligned:
    cmp x1, #0x8
    mov w8, #0x8
    add x0, sp, #0x8
    csel x1, x1, x8, hi
    mov x2, x19
    str xzr, [sp, #0x8]
    bl posix_memalign
    mov w8, w0
    mov x0, xzr
    cbnz w8, .Lzeroed_done
    ldr x20, [sp, #0x8]
    cbz x20, .Lzeroed_done
    mov x0, x20
    mov w1, wzr
    mov x2, x19
    bl memset
    mov x0, x20
.Lzeroed_done:
    ldp x20, x19, [sp, #0x20]
    ldp x29, x30, [sp, #0x10]
    add sp, sp, #0x30
    ret
.size __rdl_alloc_zeroed, .-__rdl_alloc_zeroed

.section .text._RNvCs1njKG4L9aB3_7___rustc12___rust_alloc,"ax",@progbits
.p2align 2
.globl _RNvCs1njKG4L9aB3_7___rustc12___rust_alloc
.type _RNvCs1njKG4L9aB3_7___rustc12___rust_alloc, @function
_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc:
    b __rdl_alloc
.size _RNvCs1njKG4L9aB3_7___rustc12___rust_alloc, .-_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc

.section .text._RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc,"ax",@progbits
.p2align 2
.globl _RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc
.type _RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc, @function
_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc:
    b __rdl_dealloc
.size _RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc, .-_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc

.section .text._RNvCs1njKG4L9aB3_7___rustc14___rust_realloc,"ax",@progbits
.p2align 2
.globl _RNvCs1njKG4L9aB3_7___rustc14___rust_realloc
.type _RNvCs1njKG4L9aB3_7___rustc14___rust_realloc, @function
_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc:
    b __rdl_realloc
.size _RNvCs1njKG4L9aB3_7___rustc14___rust_realloc, .-_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc

.section .text._RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed,"ax",@progbits
.p2align 2
.globl _RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed
.type _RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed, @function
_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed:
    b __rdl_alloc_zeroed
.size _RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed, .-_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed

.section .text._RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2,"ax",@progbits
.p2align 2
.globl _RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2
.type _RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2, @function
_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2:
    ret
.size _RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2, .-_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2
