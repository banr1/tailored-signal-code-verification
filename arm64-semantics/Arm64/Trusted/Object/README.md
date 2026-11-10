# `Arm64/Trusted/Object/` — Relocations and Placed Libraries

Proofs about compiled libraries are stated over layout-generic placed objects (`Obj.PlacedLib` and `Obj.MultiPlacedLib`) rather than a fixed static-linker layout. This directory defines (in the trusted computing base) the AArch64 static relocation encodings and the placed-library model.

| File | Key definitions | Read when |
| --- | --- | --- |
| [`Reloc.lean`](Reloc.lean) | `Obj.RelocKind`, `Obj.RelocEntry`, `Obj.SymCodeInfo`, `Obj.SymDataInfo`, `pageSize`, `bytesLE`, `pageOf`, `lo12Of`, `wordOfBytesLE`, `bytesOfWordLE`, `lookup`, `lookupUnique`, `branchWord` / `BranchInRange`, `adrpWord` / `AdrpInRange`, `adrWord` / `AdrInRange`, `lo12Word` / `Lo12Aligned`, `imm19Word` / `Imm19InRange`, `tstbr14Word` / `TstBr14InRange`, `Prel32InRange`, `Abs32InRange`, `TlsIeInRange`, `tlsieMovzWord`, `tlsieMovkWord`, `ldrToAddWord`, `isLdr64UnsignedWord` | auditing AArch64 static relocation word patchers, linker relaxation encodings, and immediate range predicates |
| [`Placed.lean`](Placed.lean) | `Obj.HoldsBytes`, `Obj.CodeBlock`, `Obj.PlacedLib`, `Obj.MultiPlacedLib`, `Obj.Placement`, `patchRelocWord`, `CodeRelocInRange`, `addSignedAddr`, `CodeBlock.relaxableAt` / `relaxedAt` / `gotPairAt` / `tlsieRelaxableAt` / `b2bNext?` / `patchedWord` / `patched`, `CodeBlock.Placeable`, `PlacedLib.Placeable`, `PlacedLib.program`, `PlacedLib.fnAddr` | writing or auditing layout-generic library contracts that hold for every link by a standard static linker (relaxation included) |
| [`Labels.lean`](Labels.lean) | `Obj.SymKind`, `Obj.SymBind`, `Obj.SymSec`, `Obj.RawReloc`, `Obj.RawSec`, `Obj.RawSym`, `Obj.RawGroup`, `Obj.ExtractedObj`, `Obj.SliceOrigin`, `Obj.Discarded`, `Obj.Resolves`, `Obj.SymNameDerived`, `Obj.UnclaimedSymName`, `Obj.CoversDataSlice`, `Obj.ValidTextSlice`, `Obj.ValidDataSlice`, `Obj.RelocMatches`, `Obj.SliceRelocsMatch`, `Obj.WeakOnlyUndef`, `Obj.LabelsFromObjects` | auditing pre-link `.o` symbol, data-slice, extern-table, and relocation provenance of an `Obj.MultiPlacedLib` directly against `trusted_extractor` output without invoking any static linker |

Deprecated `[OUTSIDE TCB]` legacy fixed-base `LinkedImage` compatibility modules live under [`Arm64/Legacy/Object/`](../../Legacy/Object/LinkedImage.lean) (used only by allowlisted `ProofLib/` and `Arm64/Testing/` files via [`ProofLib/ObjectLoad.lean`](../../../ProofLib/ObjectLoad.lean) and [`tools/rust-obj2lean/src/untrusted_legacy_linker/`](../../../tools/rust-obj2lean/src/untrusted_legacy_linker/mod.rs)).

## Layout-generic placed objects (`Placed.lean`)

[`Placed.lean`](Placed.lean) models relocatable code blocks (`Obj.CodeBlock`) and libraries
(`Obj.PlacedLib` / `Obj.MultiPlacedLib`) placed at arbitrary linker-chosen addresses via a
`Placement` (`base`, `ρ`, `relax`, `b2b`, `undefWeak`). The symbol map `Placement.ρ : String → BitVec 64`
provides the resolved value `ρ sym` according to the relocation site class:

- **Direct code/data relocations, relaxed GOT (`GotToNopAdr` / `GotToAdrpAdd`) sites, data objects,
  and extern stubs**: `ρ sym` is the virtual address of `sym` in the linked image.
- **Unrelaxed GOT (`adrGotPage` / `ld64GotLo12Nc`) and unrelaxed initial-exec TLS
  (`tlsieAdrGottprelPage21` / `tlsieLd64GottprelLo12Nc`) sites**: `ρ sym` is the virtual address of
  `sym`'s 8-byte GOT slot.
- **Relaxed initial-exec TLS (`TLSIE` → `MOVZ`/`MOVK`), `TLSDESC` → `TLSLE`, and direct local-exec
  TLS (`TLSLE`) sites**: `ρ sym` is `sym`'s AArch64 Variant I thread-pointer (`TPIDR_EL0`) offset.

Because `Placement.ρ` is a single function `String → BitVec 64`, all references to a given symbol
within a placement share the same `ρ sym` interpretation; supporting mixed relaxed and unrelaxed
GOT accesses to the same symbol, or GOT-loading a symbol also listed in `PlacedLib.data`, would
require a separate GOT-slot map if ever needed.

A placement also says, through `Placement.undefWeak`, which of a block's undefined `STB_WEAK`
references (`CodeBlock.weakRefs`) the linker left undefined. As `ld.lld -static` does
(AAELF64 §5.7.11.2), a direct `call26`/`jump26` to such a symbol is patched to branch to the
next instruction (`CodeBlock.undefWeakBranch`). Its unrelaxed GOT sites still load the slot at
`ρ sym`, and that slot holds `0`.

An export of a `MultiPlacedLib` is named as in the blocks' `symbols` (for Rust, the demangled
path). `MultiPlacedLib.exportSyms` records its raw `.symtab` name when the two differ
(`MultiPlacedLib.elfSym`), and `MultiPlacedLib.InElf` looks the export up under that raw name.
The generator records these names and checks each one against
`rustc_demangle`.

## Differential testing

`Placed.lean` (`CodeBlock.Placeable`, `CodeBlock.patched`, and `MultiPlacedLib.Placeable`) is
differential-tested byte-for-byte against stock `ld.lld` (with relaxation enabled) and the Rust
mirror (`untrusted_placed`) by
[`tools/rust-obj2lean/src/test_infra/placed_lld_diff.rs`](../../../tools/rust-obj2lean/src/test_infra/placed_lld_diff.rs),
driving the Lean TCB through `placed_eval`
([`Arm64/Testing/Harness/PlacedEval.lean`](../../Testing/Harness/PlacedEval.lean)).
