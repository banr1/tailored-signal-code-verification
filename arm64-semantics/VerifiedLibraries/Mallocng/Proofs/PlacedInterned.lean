/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.Placed
public meta import ProofLib.Process
public meta import ProofLib.ProgramReflection
public import VerifiedLibraries.Mallocng.Spec

/-!
# Interned Multi-Block Representation of `mallocngLib`

Defines `mallocngMultiL : Obj.Interned.MultiLib`, the index-keyed 24-block, 9-data-object
representation of `VerifiedLibraries.mallocngLib`, together with the kernel-checked identities
`mallocngMultiL_toMultiPlacedLib` and `mallocngMultiL_names`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
  ProofLib.ObjectLoad VerifiedLibraries.Mallocng

set_option maxRecDepth 200000

def mallocngNameChars : List (List Char) := [
  str_chars% "___errno_location",
  str_chars% "__aligned_alloc_replaced",
  str_chars% "__errno_location",
  str_chars% "__libc",
  str_chars% "__libc_free",
  str_chars% "__libc_malloc",
  str_chars% "__libc_malloc_impl",
  str_chars% "__libc_realloc",
  str_chars% "__lock",
  str_chars% "__malloc_alloc_meta",
  str_chars% "__malloc_allzerop",
  str_chars% "__malloc_context",
  str_chars% "__malloc_lock",
  str_chars% "__malloc_replaced",
  str_chars% "__malloc_size_classes",
  str_chars% "__mmap",
  str_chars% "__mprotect",
  str_chars% "__mremap",
  str_chars% "__munmap",
  str_chars% "__syscall_ret",
  str_chars% "__unlock",
  str_chars% "__vm_wait",
  str_chars% "aligned_alloc",
  str_chars% "alloc_slot",
  str_chars% "calloc",
  str_chars% "debruijn32.4681",
  str_chars% "debruijn32.5048",
  str_chars% "default_malloc",
  str_chars% "free",
  str_chars% "malloc",
  str_chars% "med_cnt_tab",
  str_chars% "memcpy",
  str_chars% "memset",
  str_chars% "mmap",
  str_chars% "mmap64",
  str_chars% "mprotect",
  str_chars% "mremap",
  str_chars% "munmap",
  str_chars% "nontrivial_free",
  str_chars% "posix_memalign",
  str_chars% "realloc",
  str_chars% "small_cnt_tab"]

def blk00_errno_location : Obj.Interned.Block where
  code := VerifiedLibraries.mallocng_blk00_errno_location.code
  align := 4
  symbols := [(2, 0), (0, 0)]
  relocs := []

def blk01_syscall_ret : Obj.Interned.Block where
  code := VerifiedLibraries.mallocng_blk01_syscall_ret.code
  align := 4
  symbols := [(19, 0)]
  relocs := [
    { off := 36, kind := .call26, sym := 0 }]

def blk02_calloc : Obj.Interned.Block where
  code := VerifiedLibraries.mallocng_blk02_calloc.code
  align := 4
  symbols := [(24, 0)]
  relocs := [
    { off := 32, kind := .call26, sym := 29 },
    { off := 44, kind := .adrpHi21, sym := 13 },
    { off := 48, kind := .ldst32Lo12, sym := 13 },
    { off := 88, kind := .call26, sym := 32 },
    { off := 152, kind := .call26, sym := 0 },
    { off := 172, kind := .call26, sym := 10 },
    { off := 220, kind := .jump26, sym := 32 }]

def blk03_free : Obj.Interned.Block where
  code := VerifiedLibraries.mallocng_blk03_free.code
  align := 4
  symbols := [(28, 0)]
  relocs := [
    { off := 0, kind := .jump26, sym := 4 }]

def blk04_default_malloc : Obj.Interned.Block where
  code := VerifiedLibraries.mallocng_blk04_default_malloc.code
  align := 4
  symbols := [(27, 0), (29, 0), (5, 0)]
  relocs := [
    { off := 0, kind := .jump26, sym := 6 }]

def blk05_nontrivial_free : Obj.Interned.Block where
  code := VerifiedLibraries.mallocng_blk05_nontrivial_free.code
  align := 4
  symbols := [(38, 0)]
  relocs := [
    { off := 148, kind := .adrpHi21, sym := 14 },
    { off := 152, kind := .addLo12, sym := 14 },
    { off := 188, kind := .adrpHi21, sym := 11 },
    { off := 192, kind := .addLo12, sym := 11 },
    { off := 244, kind := .adrpHi21, sym := 11 },
    { off := 248, kind := .addLo12, sym := 11 },
    { off := 264, kind := .adrpHi21, sym := 11 },
    { off := 276, kind := .addLo12, sym := 11 },
    { off := 288, kind := .addLo12, sym := 11 },
    { off := 304, kind := .addLo12, sym := 11 },
    { off := 384, kind := .adrpHi21, sym := 11 },
    { off := 388, kind := .addLo12, sym := 11 },
    { off := 408, kind := .addLo12, sym := 11 },
    { off := 480, kind := .adrpHi21, sym := 11 },
    { off := 484, kind := .addLo12, sym := 11 },
    { off := 520, kind := .addLo12, sym := 11 },
    { off := 548, kind := .addLo12, sym := 11 },
    { off := 616, kind := .addLo12, sym := 11 },
    { off := 732, kind := .adrpHi21, sym := 11, addend := 848 },
    { off := 740, kind := .addLo12, sym := 11, addend := 848 },
    { off := 756, kind := .addLo12, sym := 11 },
    { off := 916, kind := .adrpHi21, sym := 11 },
    { off := 920, kind := .ldst64Lo12, sym := 11 },
    { off := 952, kind := .adrpHi21, sym := 14 },
    { off := 956, kind := .addLo12, sym := 14 },
    { off := 1064, kind := .adrpHi21, sym := 11 },
    { off := 1072, kind := .addLo12, sym := 11 }]

def blk06_libc_free : Obj.Interned.Block where
  code := VerifiedLibraries.mallocng_blk06_libc_free.code
  align := 4
  symbols := [(4, 0)]
  relocs := [
    { off := 224, kind := .adrpHi21, sym := 11 },
    { off := 228, kind := .ldst64Lo12, sym := 11 },
    { off := 272, kind := .adrpHi21, sym := 14 },
    { off := 276, kind := .addLo12, sym := 14 },
    { off := 524, kind := .adrpHi21, sym := 3 },
    { off := 532, kind := .addLo12, sym := 3 },
    { off := 672, kind := .adrpHi21, sym := 3 },
    { off := 676, kind := .addLo12, sym := 3 },
    { off := 680, kind := .adrpHi21, sym := 12 },
    { off := 704, kind := .call26, sym := 38 },
    { off := 716, kind := .addLo12, sym := 12 },
    { off := 720, kind := .call26, sym := 20 },
    { off := 728, kind := .call26, sym := 0 },
    { off := 748, kind := .call26, sym := 37 },
    { off := 760, kind := .addLo12, sym := 12 },
    { off := 764, kind := .call26, sym := 8 },
    { off := 784, kind := .adrpHi21, sym := 14 },
    { off := 788, kind := .addLo12, sym := 14 }]

def blk07_malloc_alloc_meta : Obj.Interned.Block where
  code := VerifiedLibraries.mallocng_blk07_malloc_alloc_meta.code
  align := 4
  symbols := [(9, 0)]
  relocs := [
    { off := 12, kind := .adrpHi21, sym := 11 },
    { off := 16, kind := .addLo12, sym := 11 },
    { off := 28, kind := .addLo12, sym := 11 },
    { off := 108, kind := .adrpHi21, sym := 3 },
    { off := 112, kind := .addLo12, sym := 3 },
    { off := 160, kind := .call26, sym := 31 },
    { off := 192, kind := .addLo12, sym := 11 },
    { off := 204, kind := .ldst64Lo12, sym := 11 },
    { off := 228, kind := .adrpHi21, sym := 3, addend := 48 },
    { off := 244, kind := .ldst64Lo12, sym := 3, addend := 48 },
    { off := 304, kind := .addLo12, sym := 11 },
    { off := 324, kind := .addLo12, sym := 11 },
    { off := 364, kind := .call26, sym := 15 },
    { off := 504, kind := .call26, sym := 15 },
    { off := 508, kind := .addLo12, sym := 11 },
    { off := 560, kind := .call26, sym := 35 },
    { off := 568, kind := .call26, sym := 0 },
    { off := 620, kind := .addLo12, sym := 11 },
    { off := 672, kind := .addLo12, sym := 11 },
    { off := 708, kind := .addLo12, sym := 11 },
    { off := 716, kind := .ldst64Lo12, sym := 11 }]

def blk08_alloc_slot : Obj.Interned.Block where
  code := VerifiedLibraries.mallocng_blk08_alloc_slot.code
  align := 4
  symbols := [(23, 0)]
  relocs := [
    { off := 20, kind := .adrpHi21, sym := 11 },
    { off := 24, kind := .addLo12, sym := 11 },
    { off := 116, kind := .addLo12, sym := 11 },
    { off := 248, kind := .addLo12, sym := 11 },
    { off := 312, kind := .addLo12, sym := 11 },
    { off := 340, kind := .adrpHi21, sym := 14 },
    { off := 344, kind := .addLo12, sym := 14 },
    { off := 556, kind := .adrpHi21, sym := 25 },
    { off := 560, kind := .addLo12, sym := 25 },
    { off := 596, kind := .addLo12, sym := 11 },
    { off := 640, kind := .adrpHi21, sym := 14 },
    { off := 644, kind := .addLo12, sym := 14 },
    { off := 660, kind := .call26, sym := 9 },
    { off := 672, kind := .addLo12, sym := 11 },
    { off := 680, kind := .adrpHi21, sym := 3, addend := 48 },
    { off := 688, kind := .ldst64Lo12, sym := 3, addend := 48 },
    { off := 704, kind := .adrpHi21, sym := 41 },
    { off := 708, kind := .addLo12, sym := 41 },
    { off := 760, kind := .adrpHi21, sym := 30 },
    { off := 764, kind := .addLo12, sym := 30 },
    { off := 860, kind := .addLo12, sym := 11 },
    { off := 988, kind := .addLo12, sym := 11 },
    { off := 1108, kind := .call26, sym := 15 },
    { off := 1132, kind := .addLo12, sym := 11 },
    { off := 1188, kind := .addLo12, sym := 11 },
    { off := 1352, kind := .addLo12, sym := 11 },
    { off := 1372, kind := .addLo12, sym := 11 },
    { off := 1584, kind := .addLo12, sym := 11 },
    { off := 1664, kind := .adrpHi21, sym := 25 },
    { off := 1672, kind := .addLo12, sym := 25 },
    { off := 1680, kind := .addLo12, sym := 14 },
    { off := 1784, kind := .addLo12, sym := 11 },
    { off := 1792, kind := .addLo12, sym := 14 },
    { off := 1856, kind := .addLo12, sym := 11 },
    { off := 1920, kind := .addLo12, sym := 14 }]

def blk09_libc_malloc_impl : Obj.Interned.Block where
  code := VerifiedLibraries.mallocng_blk09_libc_malloc_impl.code
  align := 4
  symbols := [(6, 0)]
  relocs := [
    { off := 88, kind := .adrpHi21, sym := 25 },
    { off := 96, kind := .addLo12, sym := 25 },
    { off := 104, kind := .adrpHi21, sym := 14 },
    { off := 108, kind := .addLo12, sym := 14 },
    { off := 196, kind := .adrpHi21, sym := 3 },
    { off := 200, kind := .addLo12, sym := 3 },
    { off := 204, kind := .adrpHi21, sym := 12 },
    { off := 224, kind := .adrpHi21, sym := 11 },
    { off := 228, kind := .addLo12, sym := 11 },
    { off := 372, kind := .adrpHi21, sym := 25 },
    { off := 376, kind := .addLo12, sym := 25 },
    { off := 380, kind := .addLo12, sym := 11 },
    { off := 412, kind := .addLo12, sym := 12 },
    { off := 416, kind := .call26, sym := 20 },
    { off := 456, kind := .call26, sym := 0 },
    { off := 508, kind := .call26, sym := 15 },
    { off := 524, kind := .adrpHi21, sym := 3 },
    { off := 528, kind := .addLo12, sym := 3 },
    { off := 532, kind := .adrpHi21, sym := 12 },
    { off := 548, kind := .adrpHi21, sym := 11 },
    { off := 552, kind := .addLo12, sym := 11 },
    { off := 576, kind := .call26, sym := 9 },
    { off := 588, kind := .addLo12, sym := 11 },
    { off := 652, kind := .addLo12, sym := 12 },
    { off := 656, kind := .call26, sym := 8 },
    { off := 684, kind := .addLo12, sym := 11 },
    { off := 700, kind := .addLo12, sym := 12 },
    { off := 704, kind := .call26, sym := 20 },
    { off := 716, kind := .call26, sym := 37 },
    { off := 744, kind := .addLo12, sym := 12 },
    { off := 748, kind := .call26, sym := 8 },
    { off := 764, kind := .call26, sym := 23 },
    { off := 776, kind := .addLo12, sym := 11 },
    { off := 800, kind := .addLo12, sym := 12 },
    { off := 804, kind := .call26, sym := 20 },
    { off := 816, kind := .adrpHi21, sym := 14 },
    { off := 820, kind := .addLo12, sym := 14 }]

def blk10_malloc_allzerop : Obj.Interned.Block where
  code := VerifiedLibraries.mallocng_blk10_malloc_allzerop.code
  align := 4
  symbols := [(10, 0)]
  relocs := [
    { off := 144, kind := .adrpHi21, sym := 11 },
    { off := 148, kind := .ldst64Lo12, sym := 11 },
    { off := 180, kind := .adrpHi21, sym := 14 },
    { off := 184, kind := .addLo12, sym := 14 },
    { off := 232, kind := .addLo12, sym := 14 }]

def blk11_posix_memalign : Obj.Interned.Block where
  code := VerifiedLibraries.mallocng_blk11_posix_memalign.code
  align := 4
  symbols := [(39, 0)]
  relocs := [
    { off := 36, kind := .call26, sym := 22 },
    { off := 68, kind := .call26, sym := 0 }]

def blk12_aligned_alloc : Obj.Interned.Block where
  code := VerifiedLibraries.mallocng_blk12_aligned_alloc.code
  align := 4
  symbols := [(22, 0)]
  relocs := [
    { off := 52, kind := .adrpHi21, sym := 13 },
    { off := 56, kind := .ldst32Lo12, sym := 13 },
    { off := 64, kind := .adrpHi21, sym := 1 },
    { off := 68, kind := .ldst32Lo12, sym := 1 },
    { off := 96, kind := .call26, sym := 6 },
    { off := 144, kind := .call26, sym := 0 },
    { off := 172, kind := .call26, sym := 0 },
    { off := 304, kind := .adrpHi21, sym := 11 },
    { off := 308, kind := .ldst64Lo12, sym := 11 },
    { off := 340, kind := .adrpHi21, sym := 14 },
    { off := 344, kind := .addLo12, sym := 14 },
    { off := 420, kind := .adrpHi21, sym := 14 },
    { off := 424, kind := .addLo12, sym := 14 }]

def blk13_realloc : Obj.Interned.Block where
  code := VerifiedLibraries.mallocng_blk13_realloc.code
  align := 4
  symbols := [(40, 0)]
  relocs := [
    { off := 0, kind := .jump26, sym := 7 }]

def blk14_libc_realloc : Obj.Interned.Block where
  code := VerifiedLibraries.mallocng_blk14_libc_realloc.code
  align := 4
  symbols := [(7, 0)]
  relocs := [
    { off := 104, kind := .jump26, sym := 6 },
    { off := 212, kind := .adrpHi21, sym := 11 },
    { off := 216, kind := .ldst64Lo12, sym := 11 },
    { off := 248, kind := .adrpHi21, sym := 14 },
    { off := 252, kind := .addLo12, sym := 14 },
    { off := 328, kind := .adrpHi21, sym := 14 },
    { off := 332, kind := .addLo12, sym := 14 },
    { off := 496, kind := .adrpHi21, sym := 26 },
    { off := 504, kind := .addLo12, sym := 26 },
    { off := 512, kind := .adrpHi21, sym := 14 },
    { off := 516, kind := .addLo12, sym := 14 },
    { off := 584, kind := .addLo12, sym := 14 },
    { off := 612, kind := .call26, sym := 6 },
    { off := 640, kind := .call26, sym := 31 },
    { off := 648, kind := .call26, sym := 4 },
    { off := 696, kind := .call26, sym := 0 },
    { off := 988, kind := .call26, sym := 17 }]

def blk15_vm_wait : Obj.Interned.Block where
  code := VerifiedLibraries.mallocng_blk15_vm_wait.code
  align := 4
  symbols := [(21, 0)]
  relocs := []

def blk16_mmap : Obj.Interned.Block where
  code := VerifiedLibraries.mallocng_blk16_mmap.code
  align := 4
  symbols := [(15, 0), (33, 0), (34, 0)]
  relocs := [
    { off := 120, kind := .jump26, sym := 19 },
    { off := 124, kind := .call26, sym := 0 },
    { off := 148, kind := .call26, sym := 0 },
    { off := 172, kind := .call26, sym := 21 }]

def blk17_mprotect : Obj.Interned.Block where
  code := VerifiedLibraries.mallocng_blk17_mprotect.code
  align := 4
  symbols := [(16, 0), (35, 0)]
  relocs := [
    { off := 4, kind := .adrpHi21, sym := 3, addend := 48 },
    { off := 16, kind := .ldst64Lo12, sym := 3, addend := 48 },
    { off := 60, kind := .call26, sym := 19 }]

def blk18_mremap : Obj.Interned.Block where
  code := VerifiedLibraries.mallocng_blk18_mremap.code
  align := 4
  symbols := [(17, 0), (36, 0)]
  relocs := [
    { off := 52, kind := .call26, sym := 19 },
    { off := 68, kind := .call26, sym := 0 },
    { off := 100, kind := .call26, sym := 21 }]

def blk19_munmap : Obj.Interned.Block where
  code := VerifiedLibraries.mallocng_blk19_munmap.code
  align := 4
  symbols := [(18, 0), (37, 0)]
  relocs := [
    { off := 20, kind := .call26, sym := 21 },
    { off := 40, kind := .call26, sym := 19 }]

def blk20_memcpy : Obj.Interned.Block where
  code := VerifiedLibraries.mallocng_blk20_memcpy.code
  align := 4
  symbols := [(31, 0)]
  relocs := []

def blk21_memset : Obj.Interned.Block where
  code := VerifiedLibraries.mallocng_blk21_memset.code
  align := 4
  symbols := [(32, 0)]
  relocs := []

def blk22_lock : Obj.Interned.Block where
  code := VerifiedLibraries.mallocng_blk22_lock.code
  align := 4
  symbols := [(8, 0)]
  relocs := [
    { off := 0, kind := .adrpHi21, sym := 3 },
    { off := 4, kind := .addLo12, sym := 3 },
    { off := 48, kind := .addLo12, sym := 3 },
    { off := 84, kind := .addLo12, sym := 3 }]

def blk23_unlock : Obj.Interned.Block where
  code := VerifiedLibraries.mallocng_blk23_unlock.code
  align := 4
  symbols := [(20, 0)]
  relocs := []

def mallocngMultiDataL : List Obj.Interned.Data := [
  { sym := 14, align := 4, readOnly := true, bytes := mallocngSizeClassBytes, zeroTail := 0 },
  { sym := 25, align := 1, readOnly := true, bytes := mallocngDebruijn32Table, zeroTail := 0 },
  { sym := 30, align := 1, readOnly := true, bytes := mallocngMedCntTabBytes, zeroTail := 0 },
  { sym := 41, align := 1, readOnly := true, bytes := mallocngSmallCntTabBytes, zeroTail := 0 },
  { sym := 26, align := 1, readOnly := true, bytes := mallocngDebruijn32Table, zeroTail := 0 },
  { sym := 12, align := 4, readOnly := false, bytes := [], zeroTail := 4 },
  { sym := 1, align := 4, readOnly := false, bytes := [], zeroTail := 4 },
  { sym := 13, align := 4, readOnly := false, bytes := [], zeroTail := 4 },
  { sym := 11, align := 8, readOnly := false, bytes := [], zeroTail := 928 }]

def mallocngMultiL : Obj.Interned.MultiLib where
  name := "mallocng_multi"
  names := ["___errno_location", "__aligned_alloc_replaced", "__errno_location", "__libc", "__libc_free", "__libc_malloc", "__libc_malloc_impl", "__libc_realloc", "__lock", "__malloc_alloc_meta", "__malloc_allzerop", "__malloc_context", "__malloc_lock", "__malloc_replaced", "__malloc_size_classes", "__mmap", "__mprotect", "__mremap", "__munmap", "__syscall_ret", "__unlock", "__vm_wait", "aligned_alloc", "alloc_slot", "calloc", "debruijn32.4681", "debruijn32.5048", "default_malloc", "free", "malloc", "med_cnt_tab", "memcpy", "memset", "mmap", "mmap64", "mprotect", "mremap", "munmap", "nontrivial_free", "posix_memalign", "realloc", "small_cnt_tab"]
  blocks := [blk00_errno_location, blk01_syscall_ret, blk02_calloc, blk03_free, blk04_default_malloc, blk05_nontrivial_free, blk06_libc_free, blk07_malloc_alloc_meta, blk08_alloc_slot, blk09_libc_malloc_impl, blk10_malloc_allzerop, blk11_posix_memalign, blk12_aligned_alloc, blk13_realloc, blk14_libc_realloc, blk15_vm_wait, blk16_mmap, blk17_mprotect, blk18_mremap, blk19_munmap, blk20_memcpy, blk21_memset, blk22_lock, blk23_unlock]
  data := mallocngMultiDataL
  exports := [29, 28, 24, 40, 22, 39]

theorem mallocngMultiL_toMultiPlacedLib :
    mallocngMultiL.toMultiPlacedLib = VerifiedLibraries.mallocngLib := by rfl_kernel

theorem mallocngMultiL_names :
    mallocngMultiL.names = mallocngNameChars.map String.ofList := by rfl_kernel

end VerifiedLibraries.Mallocng.Proofs
