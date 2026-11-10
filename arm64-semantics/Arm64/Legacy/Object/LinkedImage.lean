/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Object.Reloc

/-!
# Legacy Linked AArch64 Images and Relocating Loader

Position-independent linked image representation (`Obj.LinkedImage`, `Obj.DataReloc`,
`Obj.GotEntry`, `Obj.ObjectInfo`), loaded image representation (`Obj.Image`), structural
well-formedness check (`Obj.LinkedImage.wellFormed`), and base-relocating loader
(`Obj.LinkedImage.load`).

## Layout

PC-relative code relocations are pre-resolved at base 0 and remain valid under any page-aligned
`base`. `LinkedImage.load base` checks `wellFormed` (non-overlapping, page-aligned, non-wrapping
regions and per-object `ObjectInfo` consistency) and shifts offsets by `base`:
- `[0, code.length)`: text sections and 4-byte extern stubs (`r-x`).
- `[dataOff, dataEnd)`: read-only data (`roData`, `r--`) and read-write data/bss (`rw-`),
  patched by `DataReloc`.
- `externData` (before `gotOff`): unconstrained extern data objects.
- `[gotOff, gotOff + 8 * got.length)`: 8-byte GOT slots (`r--`) holding `base + off` or TLS
  TP-offsets (`GotEntry`).
-/

@[expose] public section

namespace Arm64.Obj

/-! ## Linked images -/

/-- An absolute address the loader writes into the data region: the `width`-byte
    little-endian encoding of `base + target` at offset `off` of `LinkedImage.data`
    (`R_AARCH64_ABS64` for `width = 8`, `R_AARCH64_ABS32` for `width = 4`). -/
structure DataReloc where
  off : Nat
  width : Nat := 8
  target : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A GOT slot: the absolute address `base + off` (`R_AARCH64_ADR_GOT_PAGE` /
    `LD64_GOT_LO12_NC`), or the base-independent offset `v` of an extern thread-local variable
    from the thread pointer (`R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21` /
    `TLSIE_LD64_GOTTPREL_LO12_NC`; the Rust linker lays out the extern TLS symbols in a TLS block
    at TP offset 16, as AArch64 TLS variant 1 specifies for an executable). -/
inductive GotEntry where
  | addr (off : Nat)
  | tpoff (v : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The 64-bit value of a GOT slot when the image is loaded at `base`. -/
def GotEntry.value (base : BitVec 64) : GotEntry → BitVec 64
  | .addr off => base + BitVec.ofNat 64 off
  | .tpoff v => BitVec.ofNat 64 v

/-- Link-independent facts about one input object, recorded by the linker:
    - `fns`: the functions `(symbol, code bytes)` it defines in relocation-free text sections;
    - `callFns`: the functions `(symbol, code bytes, calls)` it defines in text sections whose
      relocations are only direct branches (`B`/`BL`, addend 0) to external symbols
      `calls : List (Nat × String)` (`(offset_in_fn, target_sym)`);
    - `relocFns`: the functions `SymCodeInfo` it defines in text sections with general code
      relocations (`RelocEntry`);
    - `dataSyms`: the data symbols `SymDataInfo` it defines in `.rodata`, `.data`, `.data.rel.ro`,
      or `.bss`.
    A library specification can name its object by its `ObjectInfo` (see `Arm64.LibrarySpec`). -/
structure ObjectInfo where
  name : String
  fns : List (String × List (BitVec 8)) := []
  callFns : List (String × List (BitVec 8) × List (Nat × String)) := []
  relocFns : List SymCodeInfo := []
  dataSyms : List SymDataInfo := []
  deriving DecidableEq, Repr, Inhabited

/-- Base-independent linked image produced by statically linking a set of objects
    (see the module docstring for the memory layout). -/
structure LinkedImage where
  /-- Text sections with all relocations applied, then a zero 4-byte stub per extern function. -/
  code : List (BitVec 8)
  /-- Offset of the data region (page-aligned, after `code`). -/
  dataOff : Nat
  /-- rodata and data sections, with every base-independent relocation applied. -/
  data : List (BitVec 8)
  /-- Number of zero bytes (bss sections) following `data`. -/
  bss : Nat := 0
  /-- rodata sections `(offset, size)`, inside the data region; mapped read-only. -/
  roData : List (Nat × Nat) := []
  /-- Extern data objects `(name, offset, size)`, between the data region and the GOT. -/
  externData : List (String × Nat × Nat) := []
  /-- Offset of the GOT (8-byte aligned, after the extern data objects). -/
  gotOff : Nat
  /-- GOT slots: slot `i` holds `got[i].value base`. -/
  got : List GotEntry := []
  /-- Absolute addresses written into the data region at load time. -/
  relocs : List DataReloc := []
  /-- Defined function and object symbols (demangled) and their offsets. -/
  symbols : List (String × Nat)
  /-- Defined function and object symbols grouped by defining object name. -/
  objSymbols : List (String × List (String × Nat)) := []
  /-- Extern functions and the offsets of their stubs. -/
  stubs : List (String × Nat)
  /-- What the linker records about each input object. -/
  objects : List ObjectInfo := []
  deriving Repr, Inhabited

/-- End of the data region (`data`, then `bss` zero bytes). -/
def LinkedImage.dataEnd (li : LinkedImage) : Nat := li.dataOff + li.data.length + li.bss

/-- Offset of defined symbol or extern stub `name` in `li`. -/
def LinkedImage.resolveSym (li : LinkedImage) (name : String) : Option Nat :=
  (lookup name li.symbols).orElse fun _ => lookup name li.stubs

/-- Offset of symbol `sym` resolved in the context of object `objName` within `li`:
    if `localOnly = true`, looks up `sym` uniquely in `objName`'s symbol table in `li.objSymbols`;
    otherwise checks `objName`'s symbol table first, then `li.resolveSym sym` (`li.symbols` or
    `li.stubs`), then `li.externData`. -/
def LinkedImage.resolveObjSym (li : LinkedImage) (objName sym : String)
    (localOnly : Bool := false) : Option Nat :=
  let localLookup := (lookup objName li.objSymbols).bind (lookupUnique sym)
  if localOnly then
    localLookup
  else
    localLookup <|> li.resolveSym sym <|> (lookup sym li.externData).map (·.1)

/-- Target offset `S + A` of relocation `r` in object `objName` within `li`. -/
def LinkedImage.resolveRelocTarget (li : LinkedImage) (objName : String) (r : RelocEntry) :
    Option Nat :=
  (li.resolveObjSym objName r.sym r.localSym).bind fun s => addSignedOff s r.addend

/-- Every function and data symbol recorded by `o` is placed at an aligned offset `off` that `o`'s
    symbol table in `li` gives it uniquely (and `li.symbols` resolves to), its code/data bytes in
    `li` match the recorded template bytes with relocations patched (`callFns`, `relocFns`,
    `dataSyms`), and no extern stub lies inside any function. -/
def LinkedImage.honours (li : LinkedImage) (o : ObjectInfo) : Bool :=
  match lookup o.name li.objSymbols with
  | none => false
  | some syms =>
    (o.fns.all fun (f, bs) =>
      match lookupUnique f syms with
      | none => false
      | some off =>
        lookup f li.symbols == some off &&
        off % 4 == 0 && bytesAt li.code off bs &&
          li.stubs.all fun (_, s) => !(off ≤ s && s < off + bs.length)) &&
    (o.callFns.all fun (f, bs, calls) =>
      match lookupUnique f syms with
      | none => false
      | some off =>
        lookup f li.symbols == some off &&
        off % 4 == 0 && bs.length % 4 == 0 && off + bs.length ≤ li.code.length &&
        (calls.all fun (roff, sym) =>
          match li.resolveSym sym with
          | some t => branchInRange (off + roff) t
          | none => false) &&
        ((List.range (bs.length / 4)).all fun j =>
          let w := (bs.drop (4 * j)).take 4
          let expected := match calls.find? (·.1 == 4 * j) with
            | some (_, sym) => patchBranchBytes w (off + 4 * j) ((li.resolveSym sym).getD 0)
            | none => w
          (li.code.drop (off + 4 * j)).take 4 == expected) &&
        li.stubs.all fun (_, s) => !(off ≤ s && s < off + bs.length)) &&
    (o.relocFns.all fun fn =>
      match lookupUnique fn.sym syms with
      | none => false
      | some off =>
        lookup fn.sym li.symbols == some off &&
        off % 4 == 0 && fn.code.length % 4 == 0 && off + fn.code.length ≤ li.code.length &&
        (fn.relocs.all fun r =>
          match li.resolveRelocTarget o.name r with
          | some t => codeRelocInRange r.kind (off + r.off) t
          | none => false) &&
        ((List.range (fn.code.length / 4)).all fun j =>
          let w := wordOfBytesLE fn.code (4 * j)
          let expected := match fn.relocs.find? (·.off == 4 * j) with
            | some r =>
              let t := (li.resolveRelocTarget o.name r).getD 0
              bytesOfWordLE (patchCodeRelocWord r.kind w (off + 4 * j) t)
            | none => (fn.code.drop (4 * j)).take 4
          (li.code.drop (off + 4 * j)).take 4 == expected) &&
        li.stubs.all fun (_, s) => !(off ≤ s && s < off + fn.code.length)) &&
    (o.dataSyms.all fun d =>
      match lookupUnique d.sym syms with
      | none => false
      | some off =>
        let totalLen := d.bytes.length + d.zeroTail
        let relOff := off - li.dataOff
        lookup d.sym li.symbols == some off &&
        d.align > 0 && off % d.align == 0 &&
        li.dataOff ≤ off &&
        (d.bytes.length == 0 || relOff + d.bytes.length ≤ li.data.length) &&
        relOff + totalLen ≤ li.data.length + li.bss &&
        (if d.readOnly then
          li.roData.any fun (rOff, rLen) =>
            rOff ≤ off && off + totalLen ≤ rOff + rLen && rOff + rLen < 2 ^ 64
        else
          li.roData.all fun (rOff, rLen) => rOff + rLen ≤ off || off + totalLen ≤ rOff) &&
        (d.relocs.all fun r =>
          match li.resolveRelocTarget o.name r with
          | some t =>
            match r.kind with
            | .abs64 => r.off + 8 ≤ d.bytes.length && relOff + r.off + 8 ≤ li.data.length
            | .abs32 => r.off + 4 ≤ d.bytes.length && relOff + r.off + 4 ≤ li.data.length
            | .prel32 =>
              r.off + 4 ≤ d.bytes.length && relOff + r.off + 4 ≤ li.data.length &&
              prel32InRange (off + r.off) t &&
              (li.data.drop (relOff + r.off)).take 4 ==
                bytesOfWordLE ((BitVec.ofNat 64 t - BitVec.ofNat 64 (off + r.off)).setWidth 32)
            | _ => false
          | none => false) &&
        (let windowRelocs := li.relocs.filter fun lr =>
          !(lr.off + lr.width ≤ relOff || relOff + totalLen ≤ lr.off)
        let expectedDataRelocs := d.relocs.filterMap fun r =>
          let t := (li.resolveRelocTarget o.name r).getD 0
          match r.kind with
          | .abs64 => some { off := relOff + r.off, width := 8, target := t }
          | .abs32 => some { off := relOff + r.off, width := 4, target := t }
          | _ => none
        windowRelocs == expectedDataRelocs) &&
        ((List.range totalLen).all fun i =>
          if d.relocs.any (fun r =>
              let w := if r.kind == .abs32 || r.kind == .prel32 then 4 else 8
              r.off ≤ i && i < r.off + w) then
            true
          else if i < d.bytes.length then
            li.data.getD (relOff + i) 0#8 == d.bytes.getD i 0#8
          else
            relOff + i ≥ li.data.length || li.data.getD (relOff + i) 0#8 == 0#8))

/-- Structural invariants checked by `LinkedImage.load` (region ordering, alignment,
    relocation and stub bounds, and per-object `honours` consistency). -/
def LinkedImage.wellFormed (li : LinkedImage) : Bool :=
  li.code.length ≤ li.dataOff && li.dataOff % pageSize == 0 &&
  li.dataEnd ≤ li.gotOff && li.gotOff % 8 == 0 &&
  li.roData.all (fun (o, n) => li.dataOff ≤ o && o + n ≤ li.dataEnd) &&
  li.externData.all (fun (_, o, n) => li.dataEnd ≤ o && o + n ≤ li.gotOff) &&
  li.relocs.all (fun r => (r.width == 8 || r.width == 4) && r.off + r.width ≤ li.data.length) &&
  li.stubs.all (fun (_, s) => s + 4 ≤ li.code.length) &&
  li.objects.all li.honours

/-! ## Images -/

/-- A loaded program image. Symbol and stub locations are offsets from `base`; other
    addresses are absolute. -/
structure Image where
  /-- Load address; code is at `[base, base + code.length)`. -/
  base : BitVec 64
  /-- Text sections with relocations applied, then zero-filled extern stubs. -/
  code : List (BitVec 8)
  /-- rodata/data/bss, relocated, at `dataAddr`. -/
  dataAddr : BitVec 64
  data : List (BitVec 8)
  /-- The rodata sections `(addr, size)`, inside `[dataAddr, dataAddr + data.length)`. They are
      mapped read-only; the rest of `data` is read-write. -/
  roData : List (BitVec 64 × Nat)
  /-- Extern data objects `(name, addr, size)`. Their contents are unconstrained. -/
  externData : List (String × BitVec 64 × Nat)
  /-- GOT slots, 8 bytes each, at `gotAddr`. -/
  gotAddr : BitVec 64
  got : List (BitVec 64)
  /-- Defined function and object symbols (demangled) and their offsets from `base`. -/
  symbols : List (String × Nat)
  /-- Defined function and object symbols grouped by defining object name. -/
  objSymbols : List (String × List (String × Nat)) := []
  /-- Extern functions and the offsets of their stubs from `base`. -/
  stubs : List (String × Nat)
  deriving Repr, Inhabited

/-- Write the absolute address `base + r.target` into `data`. -/
def DataReloc.apply (base : BitVec 64) (data : List (BitVec 8)) (r : DataReloc) :
    Except String (List (BitVec 8)) := do
  let v := base + BitVec.ofNat 64 r.target
  if r.width == 4 && !(-(2 ^ 31 : Int) ≤ v.toInt && v.toInt < (2 ^ 32 : Int)) then
    .error "ABS32 out of range"
  pure (data.take r.off ++ bytesLE r.width v ++ data.drop (r.off + r.width))

/-- Load `li` at `base`. Requires `base` to be page-aligned, the image not to wrap around the
    address space, and `li.wellFormed`. -/
def LinkedImage.load (li : LinkedImage) (base : BitVec 64) : Except String Image := do
  if base.toNat % pageSize != 0 then .error "base is not page-aligned"
  if base.toNat + li.gotOff + 8 * li.got.length > 2 ^ 64 then .error "image wraps around"
  if !li.wellFormed then .error "malformed linked image"
  let data ← li.relocs.foldlM (DataReloc.apply base) (li.data ++ List.replicate li.bss 0)
  let addr (off : Nat) := base + BitVec.ofNat 64 off
  pure {
    base, code := li.code
    dataAddr := addr li.dataOff
    data
    roData := li.roData.map fun (o, n) => (addr o, n)
    externData := li.externData.map fun (x, o, n) => (x, addr o, n)
    gotAddr := addr li.gotOff
    got := li.got.map (GotEntry.value base)
    symbols := li.symbols
    objSymbols := li.objSymbols
    stubs := li.stubs }

/-- Page-aligned end of the loaded data/bss region (`[dataAddr, dataAddr + data.length)`):
    the initial program break (`State.brkStart` and initial `State.brk`) when `img` is loaded. -/
def Image.brkStart (img : Image) : BitVec 64 :=
  BitVec.ofNat 64 (((img.dataAddr.toNat + img.data.length + (pageSize - 1)) / pageSize) * pageSize)

/-- Per-object symbol address table of `img` (for `State.symtab`):
    if `objName` is a loaded object in `img.objSymbols`, looks up `sym` uniquely in `objName`;
    otherwise looks up `sym` in `img.symbols`, `img.stubs`, or `img.externData`. -/
def Image.symtab (img : Image) (objName sym : String) : Option (BitVec 64) :=
  match lookup objName img.objSymbols with
  | some syms => (lookupUnique sym syms).map fun off => img.base + BitVec.ofNat 64 off
  | none =>
    (((lookup sym img.symbols).orElse fun _ => lookup sym img.stubs).map
      fun off => img.base + BitVec.ofNat 64 off) <|>
      (lookup sym img.externData).map (·.1)

end Arm64.Obj
