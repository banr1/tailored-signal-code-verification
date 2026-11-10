/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public import GeneratedLean.LibsignalSessionObj

/-!
# SPQR V1: image-offset guards for `Hooks.lean`

**Checked by Lean.** No proof imports this leaf module. It pins the raw offsets that `Hooks.lean`
writes down by hand (from the disassembly) to the linker output `libsignalSessionImage`, so a relink
that moves them fails the build instead of silently changing what `TokenInit` and the stub tables
refer to. Build it with
`lake build --no-ansi LibsignalBinary.Specifications.LibsignalSpqrV1.Guards`.

Glossary: SPQR = Sparse Post-Quantum Ratchet; `TOKEN` = spqr's
`encoding::gf::check_accelerated::TOKEN` (a `LazyLock<cpufeatures InitToken>`); `STORAGE.0` = the
cpufeatures detection cache `use_accelerated::STORAGE` (1 byte, `0xff` = not yet detected); PMULL =
the AArch64 polynomial multiply instruction; `.data` = the read-write data section; rodata = the
read-only data ranges (`roData`), which `Image.FrozenLoaded` freezes to their image bytes; GOT =
global offset table; bss = zero-initialized data.

## Main statements

What the guards establish:

* `tokenStorage_symtab` / `tokenOnce_symtab`: in every loaded image, the machine's symbol table
  (`s.symtab = img.symtab`, from `Spec.inImage`) resolves `STORAGE.0` to `tokenStorageAddr img`
  (offset `0x9a038`) and `TOKEN` to `tokenOnceAddr img - 8` (offset `0x9a040`; the `futex::Once`
  state word is at `+8`). `token_symbols_unique` / `token_cells_owned`: each name has exactly one
  symbol entry, and no other symbol starts inside the cells `TokenInit` uses.
* `token_cells_rw_data`: the 5 bytes `TokenInit` constrains (`0x9a038` and `0x9a048..0x9a04c`)
  lie in the initialized data of the image (not bss, extern data, GOT or code), outside every
  rodata range and every load-time relocation. `token_cells_not_roData`: the same at the level of a
  loaded image, the form `Image.FrozenLoaded` / `Image.RoDataLoaded` uses. So `FrozenLoaded` does
  not pin these bytes, and `TokenInit` (which needs `0` there) is consistent with it.
* `token_cells_initial`: the image's initial bytes there are `STORAGE.0 = 0xff` (cpufeatures:
  not yet detected) and `Once` state `3` (`futex::Once` `INCOMPLETE`). So `TokenInit` is **not**
  the load-time state: it is the runtime state after `TOKEN`'s first use found no `aes`/PMULL
  (DEV-SPQR1 in `Computational/docs/DEVIATIONS.md`).
* `token_region_disjoint_roData`: every rodata range lies in `.img.rodata` (`[0x89000, 0x9a000)`),
  so the token cells at `[0x9a038, 0x9a050)` are outside all of them.
* `spqrStubs_offsets`: each extern stub that `Hooks.lean` names (the 8 `SpqrHooks` stubs and
  `Once::call`, listed in `spqrStubOffs`) is a stub of the image, at the offset `Hooks.lean`
  gives, and is not a defined symbol (so `Image.symtab` resolves it to that stub).
* `growOne_defined_in_image`: all 3 `RawVec<T>::grow_one` instantiations (`u8`, `Vec<u8>`,
  `String`) resolve uniquely as defined symbols in `libsignalSessionImage.symbols` and are absent
  from `libsignalSessionImage.stubs`.

Not covered: that the SPQR V1 `Once::call` sites address these cells is a property of the code. On
the pinned stock `ld.lld` CLI ELF (`2f20c8363424…`, where `--gc-sections` retains `10` `bl 0x468930`
`<Once>::call` sites in `.text.crate`, all in `spqr::encoding::*`, and places `STORAGE.0` at
`0x46f000` and `TOKEN` at `0x46f008` in `.data.crate`, anchored on the placed route by
`CliProbeLabelsAnchored` and `Placed.cliTokenPatchPlaced`), `llvm-objdump -d -C` on
`spqr::encoding::gf::mul2_u16` (`0x442f38`) shows:
* `442f4c: b0000168  adrp x8, 0x46f000` / `442f50: 91004108  add x8, x8, #0x10` (`TOKEN + 8`)
* `442f5c: b0000168  adrp x8, 0x46f000` / `442f60: 39400108  ldrb w8, [x8]` (`STORAGE.0`)
(On `libsignalSessionImage` / pre-stock `snapshot-link` ELF `e35abe2a39b2…`, whose fixed offsets this
file checks, the 14 SPQR V1 sites out of 15 `bl 0x4885fc` sites read `0x49a048` / `0x49a038`, e.g.
`45e628` / `45e638` in `mul2_u16`.) A proof that executes those instructions can use `TokenInit` only
if they do.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

open Arm64 ProofLib CryptoVerification.LibsignalSession

/-! ## `TOKEN` / `STORAGE.0` -/

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
/-- Guard: `STORAGE.0` and `TOKEN` each have exactly one entry in the image's symbols, at
`tokenStorageOff` and `tokenOff`; the `Once` state word is `TOKEN + 8`. -/
theorem token_symbols_unique :
    Obj.lookupUnique tokenStorageName libsignalSessionImage.symbols = some tokenStorageOff.toNat ∧
      Obj.lookupUnique tokenName libsignalSessionImage.symbols = some tokenOff.toNat ∧
      tokenOnceOff = tokenOff + 8#64 := by
  refine ⟨?_, ?_, rfl⟩ <;> rfl_kernel

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
/-- Guard (kernel-checked): in every loaded image, the symbol table resolves `STORAGE.0` to
`tokenStorageAddr img`. -/
theorem tokenStorage_symtab {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img) :
    img.symtab "" tokenStorageName = some (tokenStorageAddr img) := by
  obtain ⟨_, _, _, _, _, himg⟩ := ProofLib.ObjectLoad.load_eq_ok h
  rw [himg]
  rfl_kernel

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
/-- Guard (kernel-checked): in every loaded image, the symbol table resolves `TOKEN` to
`img.base + tokenOff`, and its `Once` state word `tokenOnceAddr img` is at `+8`. -/
theorem tokenOnce_symtab {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img) :
    img.symtab "" tokenName = some (img.base + tokenOff) ∧
      tokenOnceAddr img = img.base + tokenOff + 8#64 := by
  obtain ⟨_, _, _, _, _, himg⟩ := ProofLib.ObjectLoad.load_eq_ok h
  refine ⟨?_, ?_⟩
  · rw [himg]
    rfl_kernel
  · simp only [tokenOnceAddr, tokenOnceOff, tokenOff]
    bv_omega

/-- The image offsets of the 5 bytes `TokenInit` constrains: `STORAGE.0`, then the 4 bytes of the
`Once` state word. -/
def tokenCellOffs : List Nat :=
  [tokenStorageOff.toNat] ++ (List.range 4).map (tokenOnceOff.toNat + ·)

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
/-- Guard: no symbol other than `STORAGE.0` starts at `0x9a038`, and no symbol other than `TOKEN`
starts in `TOKEN`'s 16 bytes `0x9a040..0x9a050` (which hold the `Once` word at `+8`). -/
theorem token_cells_owned :
    libsignalSessionImage.symbols.all (fun (n, o) =>
      (o != tokenStorageOff.toNat || n == tokenStorageName) &&
        (!(tokenOff.toNat ≤ o && o < tokenOff.toNat + 16) || n == tokenName)) = true := by
  rfl_kernel

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
/-- Guard: each byte of `tokenCellOffs` is in the initialized `.data` of the image (`dataOff ≤ o <
dataOff + data.length`; the image's 8 bss bytes follow it), outside every rodata range, before
every extern datum (hence before the GOT), and not written by any load-time relocation. -/
theorem token_cells_rw_data :
    libsignalSessionImage.bss = 8 ∧
      tokenCellOffs.all (fun o =>
        decide (libsignalSessionImage.dataOff ≤ o) &&
        decide (o < libsignalSessionImage.dataOff + libsignalSessionImage.data.length) &&
        libsignalSessionImage.roData.all (fun (ro, n) => decide (o < ro ∨ ro + n ≤ o)) &&
        libsignalSessionImage.externData.all (fun (_, eo, _) => decide (o < eo)) &&
        libsignalSessionImage.relocs.all (fun r =>
          decide (o < libsignalSessionImage.dataOff + r.off ∨
            libsignalSessionImage.dataOff + r.off + r.width ≤ o))) = true := by
  refine ⟨rfl, ?_⟩
  rfl_kernel

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
/-- Guard: the initial bytes of the cells are `STORAGE.0 = 0xff` (cpufeatures `u8::MAX`, not yet
detected) and `Once` state `3` (`futex::Once` `INCOMPLETE`): `TokenInit` (`0` and `0`) is a runtime
state reached after detection, not the load-time state. -/
theorem token_cells_initial :
    tokenCellOffs.map (fun o =>
        libsignalSessionImage.data.getD (o - libsignalSessionImage.dataOff) 0) =
      [0xff#8, 3#8, 0#8, 0#8, 0#8] := by
  rfl_kernel

/-- `isRoData` of a loaded image at `base + o`, computed on the linked image's offsets. -/
private theorem isRoData_rebase (b : BitVec 64) (o : Nat) (ro : List (Nat × Nat)) :
    (ro.map fun (x, n) => (b + BitVec.ofNat 64 x, n)).any
        (fun r => decide ((b + BitVec.ofNat 64 o - r.1).toNat < r.2)) =
      ro.any (fun r => decide ((BitVec.ofNat 64 o - BitVec.ofNat 64 r.1).toNat < r.2)) := by
  induction ro with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, List.any_cons, ih]
    congr 2
    have : b + BitVec.ofNat 64 o - (b + BitVec.ofNat 64 r.1) =
        BitVec.ofNat 64 o - BitVec.ofNat 64 r.1 := by bv_omega
    rw [this]

/-- Whether image offset `o` is in a rodata range of the linked image (the test `Image.isRoData`
makes on a loaded image, rebased; `isRoData_rebase`). -/
private noncomputable def roHit (o : Nat) : Bool :=
  libsignalSessionImage.roData.any
    (fun r => decide ((BitVec.ofNat 64 o - BitVec.ofNat 64 r.1).toNat < r.2))

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
private theorem roHit_cells :
    roHit 0x9a038 = false ∧ roHit 0x9a048 = false ∧ roHit 0x9a049 = false ∧
      roHit 0x9a04a = false ∧ roHit 0x9a04b = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rfl_kernel

/-- Guard (kernel-checked): in every loaded image, no byte that `TokenInit` constrains is rodata, so
`Image.FrozenLoaded` / `Image.RoDataLoaded` leave them free (they get `Perm.rw` in
`Image.Loaded`). -/
theorem token_cells_not_roData {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img) :
    img.isRoData (tokenStorageAddr img) = false ∧
      ∀ i < 4, img.isRoData (tokenOnceAddr img + BitVec.ofNat 64 i) = false := by
  obtain ⟨_, _, _, _, _, himg⟩ := ProofLib.ObjectLoad.load_eq_ok h
  obtain ⟨h0, h1, h2, h3, h4⟩ := roHit_cells
  have key : ∀ o : Nat, img.isRoData (img.base + BitVec.ofNat 64 o) = roHit o := by
    intro o
    rw [himg]
    exact isRoData_rebase img.base o _
  have hstor : tokenStorageAddr img = img.base + BitVec.ofNat 64 0x9a038 := rfl
  have honce : ∀ j : Nat, tokenOnceAddr img + BitVec.ofNat 64 j =
      img.base + (0x9a048#64 + BitVec.ofNat 64 j) := fun j => BitVec.add_assoc _ _ _
  refine ⟨by rw [hstor]; exact (key _).trans h0, ?_⟩
  intro i hi
  rw [honce i]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · exact (key 0x9a048).trans h1
  · exact (key 0x9a049).trans h2
  · exact (key 0x9a04a).trans h3
  · exact (key 0x9a04b).trans h4

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
/-- Guard: every read-only range of `libsignalSessionImage` lies in `.img.rodata`
(`[0x89000, 0x9a000)`), hence `[0x9a038, 0x9a050)` lies strictly outside every `roData` range. -/
theorem token_region_disjoint_roData :
    libsignalSessionImage.roData.all
      (fun (ro, n) => decide (0x89000 ≤ ro ∧ ro + n ≤ 0x9a000)) = true := by
  rfl_kernel

/-! ## Extern stubs -/

/-- The extern stubs `Hooks.lean` names, with the offsets it gives. -/
def spqrStubOffs : List (String × BitVec 64) :=
  [(mlkemFromSeedName, mlkemFromSeedOff), (mlkemPk1Name, mlkemPk1Off),
   (mlkemPk2Name, mlkemPk2Off), (mlkemEncaps1Name, mlkemEncaps1Off),
   (mlkemEncaps2Name, mlkemEncaps2Off), (mlkemDecapsName, mlkemDecapsOff),
   (mlkemValidatePkName, mlkemValidatePkOff), (libcruxHmacName, libcruxHmacOff),
   (onceCallName, onceCallOff)]

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
/-- Guard: each of them is exactly one extern stub of the image, at the offset `Hooks.lean` gives,
and not a defined symbol (so `Image.symtab` and `fnAddr` resolve it to that stub). -/
theorem spqrStubs_offsets :
    spqrStubOffs.all (fun (n, off) =>
      Obj.lookupUnique n libsignalSessionImage.stubs == some off.toNat &&
        !libsignalSessionImage.symbols.any (·.1 == n)) = true := by
  rfl_kernel

/-- Demangled `RawVec<T>::grow_one` instantiations linked as in-image functions. -/
def growOneInImageNames : List String :=
  ["<alloc::raw_vec::RawVec<u8>>::grow_one",
   "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one",
   "<alloc::raw_vec::RawVec<alloc::string::String>>::grow_one"]

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
/-- Each `RawVec<T>::grow_one` name resolves uniquely as a defined symbol in
`libsignalSessionImage.symbols` and is absent from `libsignalSessionImage.stubs`. -/
theorem growOne_defined_in_image :
    growOneInImageNames.all (fun n =>
      (Obj.lookupUnique n libsignalSessionImage.symbols).isSome &&
        !libsignalSessionImage.stubs.any (·.1 == n)) = true := by
  rfl_kernel

end CryptoVerification.LibsignalSpqrV1
