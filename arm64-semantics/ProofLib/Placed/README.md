# `ProofLib/Placed`: Proofs About Layout-Generic Placed Libraries

`ProofLib/Placed/` is untrusted (`Role::Proof`) infrastructure for libraries modeled as
`Obj.PlacedLib`. That model is a relocatable code block plus data objects with symbolic relocations,
defined in [`Arm64/Trusted/Object/Placed.lean`](../../Arm64/Trusted/Object/Placed.lean). The library
contract `PlacedLib.subroutineOk` is proved once, for every placement `pl` with `lib.Placeable pl`
([`Arm64/Trusted/Spec/Placed.lean`](../../Arm64/Trusted/Spec/Placed.lean)). A kernel-checked link
check then ties it to a real stock-linked ELF (`PlacedLib.InElf` / `PlacedLib.LinkedIn`,
[`Arm64/Trusted/Process/Placed.lean`](../../Arm64/Trusted/Process/Placed.lean)). Import the barrel
`ProofLib.Placed`.

## Which file to read for X

| I want to … | Read | Key names |
|---|---|---|
| Fetch an instruction word of `lib.program pl X O` at a code offset, with or without a relocation | [`Fetch.lean`](Fetch.lean) | `readWordOff_patched`, `patchedWord_of_relocAt_none`, `patchedWord_of_notRelaxed`, `patchedWord_of_plain`, `patchedWord_of_relaxed`, `patchedWord_of_relaxedPrev`, `relaxedAtFast`, `relocTarget_of_b2bNext_none` |
| Reuse a proof that steps through concrete words: `hasWords` for a whole reloc-free (or reloc-checked) range in one kernel check | [`Fetch.lean`](Fetch.lean) | `checkSegment`, `hasWords_of_checkSegment`, `hookFree_program`, `fnAddr_program` |
| Step through an `adrp xd, sym; add xd, xd, :lo12:sym` pair that the linker may relax to `nop; adr` | [`Pair.lean`](Pair.lean) | `sepWP_relaxablePair`, `sepWP_relaxablePair_of_hookFree`, `relaxableAt_false_of_kind` |
| Step through a plain `adrp xd, sym+k` (not a relaxable pair) and fetch its far-away `ldr`/`ldrb`/`str` `[xd, :lo12:sym+k]` for every placement | [`AdrpLdst.lean`](AdrpLdst.lean) | `sepWP_adrpPlain`, `PlacedLib.sepWP_rebase_adrpPlain`, `fetch_ldstLo12`, `PlacedLib.fetch_rebase_ldstLo12`, `PlacedLib.fetch_rebase_ldstLo12_of_placeable`, `ldstLo12Scale` |
| Work with a `Nat`-indexed library (`Obj.Interned.Lib` + `Layout`) whose decidable facts reduce fast in the kernel | [`Interned.lean`](Interned.lean) | `Interned.Lib.toLib`, `Layout.toPlacement`, `namesNodup` / `nodup_of_namesNodup`, `Lib.idsOk_spec` |
| Prove `Placeable` and extern-address distinctness `(lib.text.externs.map pl.ρ).Nodup` without a linked ELF in one `decide +kernel` (or split across per-conjunct `decide +kernel` lemmas) | [`Check.lean`](Check.lean) | `Interned.checkPlaceable`, `Interned.checkPlaceableExt`, `Interned.placeable_of_checkPlaceable`, `Interned.exists_placeable_of_checkPlaceable`, `Interned.placeable_and_externs_of_checkPlaceable`, `Interned.exists_placeable_and_externs_of_checkPlaceable`, `Interned.placeable_of_split_checks`, `Interned.placeable_and_externs_of_split_checks`, `Interned.exists_placeable_and_externs_of_split_checks`, `Interned.externsDisjointB` |
| Prove `Placeable ∧ InElf` (or `LinkedIn`) for a concrete ELF with one `decide +kernel` | [`Check.lean`](Check.lean), [`CheckText.lean`](CheckText.lean) | `Interned.check`, `Interned.check_spec`, `Interned.linkedIn_of_check` |
| Prove that a linked layout's extern addresses are the ELF's unique `.symtab` values (`lookupUnique s img.symbols = some (pl.ρ s)`) with one `decide +kernel` | [`ExternSymtab.lean`](ExternSymtab.lean) | `Interned.externSymtabOk`, `Interned.externSymtab_of` |
| Prove a multi-megabyte ELF's `checkMultiDisjoint_spec` conclusion within the CI memory cap, from separate kernel facts per segment-traversal chunk and per segment-free check (`split_check_module`) | [`Split.lean`](Split.lean) | `seg_lens%`, `rLen`, `lMultiTextWalk`, `lDataWalk`, `lTextChunks`, `lDataChunks`, `restOk`, `checkMultiDisjoint_spec_split`, `checkMultiDisjoint_spec_chunks`, `multiPlaceableB_of`, `dataDisjointFastB`, `rGetD`, `toMultiPlacedLib_of_r`, `allIdxChunk`, `allIdx_of_chunks` |
| Prove a single-block library's `checkDisjoint_spec` conclusion when its text is too large for one `decide +kernel`, from separate kernel facts per text-walk chunk (split at word offsets), per data-walk chunk and per segment-free check, with a read-only-aware `DataDisjoint` check (linear in address order, pairwise otherwise) | [`SplitSingle.lean`](SplitSingle.lean) | `walkTo`, `walkTo_spec`, `walk_append`, `textOkChunks`, `dataOkChunks`, `textPlaceableR`, `dataPlaceableR`, `dataDisjointROB`, `checkDisjoint_spec_chunks` |
| Make each `SplitSingle` text chunk cheap for a library with thousands of names: resolve relocation targets through a literal balanced symbol tree checked once by index chunks, instead of linear `lookupId` / `List.getD` scans per relocation | [`SplitSingleFast.lean`](SplitSingleFast.lean) | `SymTreeOk`, `symTreeOkChunks`, `symTreeOk_of_chunks`, `walkT`, `walkToT`, `walkT_eq`, `walkToT_eq`, `textOkChunksT`, `checkDisjoint_spec_chunksT` |
| Make the `rfl` fact `lib = L.toLib` cheap for a library with thousands of names: resolve names through a literal balanced `VecTree String` checked once by index chunks, instead of a linear `List.getD` walk of the names table per name | [`NamesTree.lean`](NamesTree.lean) | `Lib.toLibWith`, `nameT`, `Lib.toLibT`, `namesFrom`, `NamesTreeOkChunks`, `namesTreeOkChunks_cons`, `namesTreeOkChunks_nil`, `Lib.toLibT_eq` |
| Get `Placeable ∧ InElf ∧ DataDisjoint` from one `decide +kernel` (what a whole-ELF proof needs) | [`Transfer.lean`](Transfer.lean) | `Interned.checkDisjoint`, `Interned.checkDisjoint_spec` |
| Move `InElf` facts into the executable's initial state (`img.loadState inputs = .ok s`) | [`Transfer.lean`](Transfer.lean) | `PlacedLib.codeLoaded_of_inElf`, `PlacedLib.satisfies_dataInit_of_inElf`, `PlacedLib.satisfies_dataRO_of_inElf`, `ElfImage.loadState_cell` |
| Discharge an extern of the library with the executable's own code at `pl.ρ e` | [`Transfer.lean`](Transfer.lean) | `PlacedLib.externAt?_program`, `PlacedLib.externAt?_program_inv`, `Interned.externsNodup_of_check` |
| Lower `lib.subroutineOk` at a concrete placement to a `Steps Program.pureMem` run in the executable (also when a hook may panic) | [`Transfer.lean`](Transfer.lean) | `PlacedLib.subroutineOk_toPureMem`, `PlacedLib.subroutineOk_toPureMem_or_hookPanic` |
| Prove that no placement of a library contains `SVC #0` or `MSR TPIDR_EL0, Xt` (or any masked word pattern), with one `decide +kernel` over the template code and relocations (not imported by `ProofLib.Placed`) | [`OpcodeExclusion.lean`](OpcodeExclusion.lean) | `CodeBlock.patchSafe`, `svc0Pat`, `msrTpidrEl0Pat`, `PlacedLib.program_noSvc0_of_patchSafe`, `PlacedLib.program_noMsrTpidrEl0_of_patchSafe`, `PlacedLib.program_allInstrs_of_patchSafe` |
| Verify a multi-block placed library (`Obj.MultiPlacedLib`), index block and `.rodata` symbols in $O(\log S)$ (`MultiPlacedLib.SymIndex`, `gen_multi_sym_index`), call across blocks, transfer symbol/address facts across binary variants (`SameSymbolLayout`), or check `MultiPlacedLib.Placeable` / `InElf` / `DataDisjoint` by `decide +kernel` (monolithic or split) | [`Multi.lean`](Multi.lean) | `MultiPlacedLib.SymIndex`, `gen_multi_sym_index`, `lookupSymInLists`, `MultiPlacedLib.SameSymbolLayout`, `MultiPlacedLib.resolve_block`, `MultiPlacedLib.hasWords_of_checkSegment`, `MultiPlacedLib.sepWP_relaxablePair`, `MultiPlacedLib.sepWP_call_block`, `wp_cut_codeLoaded`, `wp_call_block`, `MultiPlacedLib.placeable_of_checkPlaceable`, `MultiPlacedLib.placeable_of_split_checks`, `MultiPlacedLib.checkMultiDisjoint_spec`, `MultiPlacedLib.subroutineOk_toPureMem` |
| Prove a contract once for a function whose bytes are identical in several placed libraries (`Program`-generic over its patched words, with text **and** data relocation targets via an explicit resolver), then discharge it per library by one kernel check | [`SharedCode.lean`](SharedCode.lean) ([test](../Testing/PlacedSharedCode.lean)) | `RelocCodeAtWith`, `RelocCodeAt`, `relocCodeAtWith_congr`, `PlacedLib.resolve_data`, `PlacedLib.resolve_eq_fnAddr`, `PlacedLib.relocCodeAtWith_of_checkSegment`, `PlacedLib.relocCodeAt_of_checkSegment`, `PlacedLib.relocCodeAtWith_of_checkSegmentB2b`, `CodeBlock.checkSegmentB2b`, `placed_code_at%`, `placed_reloc_code_at_with%`, `placed_reloc_code_at%` |
| Certify that a `MultiPlacedLib`'s blocks, data slices, relocations, exports, externs, and weak references derive faithfully from pre-link `.o` files (`Obj.ExtractedObj`) — directly via `decide +kernel` or at crate scale via `gen_labels_from_objects` | [`LabelsCheck.lean`](LabelsCheck.lean), [`LabelsInterned.lean`](LabelsInterned.lean) ([test](../Testing/LabelsCoverage.lean), [precedence test](../Testing/LabelsPrecedence.lean)) | `LabelsFromObjects`, `checkLabelsFromObjectsB`, `labelsFromObjects_of_check`, `checkResolvesB`, `resolves_of_check`, `Resolves.unique`, `checkDiscardedB`, `checkNoDiscardedB`, `gen_labels_from_objects`, `LabelsFromObjects.externAt?_blockProgram`, `LabelsFromObjects.data_reloc_sym_eq`, `LabelsFromObjects.sole_data_reloc_sym_eq`, `LabelsFromObjects.resolve_data_eq_rho` |
| Anchor hook/stub tags, the extern table, Rust panic-name sets (`isPanic` soundness & completeness), external data symbols, and `STB_LOCAL` RW/RO statics directly to `Obj.ExtractedObj` in one `decide +kernel` check | [`LabelsCoverage.lean`](LabelsCoverage.lean) ([test](../Testing/LabelsCoverage.lean)) | `GateALabelsAnchored`, `checkGateALabelsB`, `gateALabels_of_check`, `CoveredDataSpec`, `DataLabelAnchored`, `checkCoveredDataSpecB`, `dataLabelAnchored_of_check`, `checkExternDataUndefB`, `checkReferencedExternsB`, `isPanicSymbolFast`, `isRustPanicPlus`, `GateALabelsAnchored.hookFirst_eq_panicFirst`, `GateALabelsAnchored.externAt?_blockProgram_active`, `GateALabelsAnchored.externAt?_at_active`, `GateALabelsAnchored.externAt?_outside_active` |

## Typical whole-ELF composition

1. Prove `my_lib.subroutineOk …` for every `pl` with `my_lib.Placeable pl`. Use `Fetch` / `Pair`
   lemmas to step through the patched code.
2. State the library as `L : Interned.Lib` with `my_lib = L.toLib`. Read the stock-linked ELF's
   layout `ly`. Prove
   `Interned.checkDisjoint L ly nameChars img (prepareCharAssocVal symChars) = true` by
   `decide +kernel`, then apply `Interned.checkDisjoint_spec` to get `Placeable`, `InElf` and
   `DataDisjoint`.
3. Use `codeLoaded_of_inElf` and `satisfies_dataInit_of_inElf` to get the contract's code and data
   preconditions in the loaded state. Then lower with `subroutineOk_toPureMem` (or
   `_or_hookPanic`). Discharge each extern hook with the ELF's code at `pl.ρ e`
   (`externAt?_program`).

## Multi-block placed libraries (`Obj.MultiPlacedLib`)

When `--gc-sections` or linker ordering places a library's `.text.<fn>` sections at independent
addresses across binaries, use `Obj.MultiPlacedLib` (`blocks : List CodeBlock` + `MultiPlacement`
with `bases : Nat → BitVec 64` and `ρ : String → BitVec 64`):

1. **Code generation:** Pass `--multi-placed` (or `multi = true` under `[placed]` in
   `translation.toml`) to `rust-obj2lean` to emit one `CodeBlock` per `.text.<fn>` section and one
   `SymDataInfo` entry per data symbol.
2. **Indexed symbol and block lookup (`gen_multi_sym_index`):** For libraries with many blocks or
   long symbol names, run `gen_multi_sym_index myLibIdx my_lib` once in an untrusted proof file to
   build a kernel-certified `my_lib.SymIndex` (`IdxTree`-backed $O(\log B)$ block projections plus
   hash-bucketed $O(\log S)$ symbol and `.rodata` lookups). Discharge relocation targets, entry
   addresses, extern side conditions, and read-only globals with `myLibIdx.resolve_eq_base`,
   `myLibIdx.fnAddr_eq_base`, `myLibIdx.resolve_eq_rho`, and `myLibIdx.satisfies_dataRO_of_findDataSym`
   without kernel traversal of `my_lib.blocks` or `my_lib.data`. When multiple binary variants share
   identical per-block symbol tables, factor symbol/address facts via `lookupSymInLists` and
   `MultiPlacedLib.SameSymbolLayout`.
3. **Per-block proofs and cross-block `BL` calls:** Project block `i` as a single-block library via
   `my_lib.blockLib i` at `my_lib.blockPlacement mpl i` so `gen_placed_fetches`, `wp_steps`, and
   `sepWP_relaxablePair` work unchanged. State multi-block subroutine contracts over
   `my_lib.withCodeLoaded mpl spec`, expose `hcode : my_lib.CodeLoaded mpl s0.mem` after `wp_init`
   with `wp_cut_codeLoaded`, and dispatch cross-block `BL` calls with `wp_call_block callee_ok args`
   (wrapping `MultiPlacedLib.sepWP_call_block` / `subroutine_ok_of_block`).
4. **Whole-ELF check:** Prove `my_lib.checkMultiDisjoint mpl img = true` by `decide +kernel` and
   apply `MultiPlacedLib.checkMultiDisjoint_spec` to obtain `Placeable mpl`, `InElf mpl img`, and
   `DataDisjoint mpl img`, then lower with `MultiPlacedLib.subroutineOk_toPureMem`.

Regression tests: [`ProofLib/Testing/PlacedCheck.lean`](../Testing/PlacedCheck.lean)
covers the checker and the Transfer lemmas;
[`ProofLib/Testing/PlacedAdrpLdst.lean`](../Testing/PlacedAdrpLdst.lean)
covers the plain `ADRP` step and the `:lo12:` load fetch;
[`ProofLib/Testing/PlacedMulti.lean`](../Testing/PlacedMulti.lean)
covers `MultiPlacedLib`, `wp_call_block`, and `checkMultiDisjoint_spec`;
[`ProofLib/Testing/PlacedExternSymtab.lean`](../Testing/PlacedExternSymtab.lean)
covers `externSymtab_of`;
[`ProofLib/Testing/PlacedSplit.lean`](../Testing/PlacedSplit.lean)
covers the split check `checkMultiDisjoint_spec_chunks`;
[`ProofLib/Testing/PlacedSplitSingle.lean`](../Testing/PlacedSplitSingle.lean)
covers the chunked single-block check `checkDisjoint_spec_chunks`;
[`ProofLib/Testing/PlacedSplitSingleFast.lean`](../Testing/PlacedSplitSingleFast.lean)
covers its symbol-tree variant `checkDisjoint_spec_chunksT`;
[`ProofLib/Testing/PlacedNamesTree.lean`](../Testing/PlacedNamesTree.lean)
covers the names-tree projection `Lib.toLibT_eq`;
[`ProofLib/Testing/LabelsCoverage.lean`](../Testing/LabelsCoverage.lean)
covers `LabelsFromObjects`, `gen_labels_from_objects`, `GateALabelsAnchored`, and `DataLabelAnchored`.

## Anchoring labels to pre-link `.o` files (`Obj.ExtractedObj`)

When an executable's `.symtab` omits `STB_LOCAL` RW/RO statics or when hook tags, extern tables,
and Rust panic-name sets should be anchored directly to the trusted `.o` extractor rather than a
legacy object linker:

1. **Code generation:** Pass `--extracted-obj` (and `--placed-only` when no legacy object image is
   needed; or `emit_extracted_obj = true`, `placed_only = true` under `[placed]` in
   `translation.toml`) to `rust-obj2lean` to emit `<Stem>ExtractedObj.{lean,bin}` via
   `trusted_extractor::emit_extracted_objs_module`.
2. **Object-to-placed provenance (`LabelsFromObjects`):** Run
   `gen_labels_from_objects my_lbl myObjs my_lib` in an untrusted proof file to synthesize
   `my_lbl_bO`, `my_lbl_dO`, and `my_lbl_spec : LabelsFromObjects myObjs my_lib my_lbl_bO my_lbl_dO`
   (or prove `checkLabelsFromObjectsB` by `decide +kernel` on small libraries).
3. **Hook, extern, panic, and RW-static label anchoring (`GateALabelsAnchored`):** Prove
   `checkGateALabelsB myObjs my_lib my_lbl_dO allExterns hookSpecs prunedStubs externData panicSyms extraPanicDemangled isPanic expectedUnhookedCount dataSpecs = true`
   by `decide +kernel` and apply `gateALabels_of_check`. Use
   `GateALabelsAnchored.externAt?_blockProgram_active` / `externAt?_at_active` /
   `externAt?_outside_active` to evaluate `externAt?`, and `DataLabelAnchored.resolve_eq_rho` +
   `DataLabelAnchored.sole_reloc_sym_eq` + `MultiPlacedLib.satisfies_dataInit_of_inElf` to connect
   `STB_LOCAL` RW statics to their placed addresses.
