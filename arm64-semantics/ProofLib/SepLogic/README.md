# `ProofLib/SepLogic/` — Separation Logic, Symbolic Execution, and Weakest Preconditions

This directory provides the separation logic assertions, memory region/byte/stack algebra, reflective AC frame solver, and weakest-precondition (`SepWP` / `SepWPp`) tactics used to specify and verify ARM64 machine code.

## Architecture & Layering (`Spec` vs `Proof`)

Every specification file (campaign `Spec/Top.lean` files such as `Examples/<Group>/<Campaign>/Spec/Top.lean` or `CaseStudies/<Campaign>/Spec/Top.lean`, and other `Spec*.lean` modules) is restricted by `trust-guard` to `Role::Spec` (definitions and Hoare triple statements only; zero theorems/lemmas) and may import only `Arm64.*` and other `Spec` modules (never `ProofLib.*`). To keep specifications small and auditable, the trusted separation-logic vocabulary lives in [`Arm64/Trusted/Spec/SepLogic.lean`](../../Arm64/Trusted/Spec/SepLogic.lean) (see [`Arm64/Trusted/README.md`](../../Arm64/Trusted/README.md)), and `ProofLib/SepLogic/` (entirely `Role::Proof`) holds the proof machinery:

### `Role::Spec` Vocabulary (Zero Theorems, in `Arm64/Trusted/Spec/`)
```text
Arm64/Trusted/Spec/SepLogic.lean   (SepProp, ∗, memRegion, InRegion, OutsideRegion, typed points-to ↦₈..↦₁₂₈, read-only ↦ᵣ, stackFrame*)
  ├── ProofLib/SepLogic/Defs.lean      (untrusted: StackPreserved, Memory.RW, Heap.complement, complementSep, memMapped)
  ├── ProofLib/PrologueFrame.lean      (untrusted: prologue frame inference, Obj.funcTable, stackFrameFor)
  ├── ProofLib/SepLogic/WP/Defs.lean   (untrusted: `export Arm64 (...)` into `ProofLib`)
  └── ProofLib/SepLogic/Frame.lean     (untrusted: AgreesOutside + frame lemmas)
```
Spec files get this vocabulary (alongside `c_spec` / `rust_spec`) from `import Arm64`.

### `Role::Proof` Lemmas, Solvers, and Tactics
- **Weakest-Precondition & Proof-Only Definitions**:
  - `ProofLib/SepLogic/Defs.lean`: Untrusted separation-logic metatheory (`StackPreserved`, `Memory.RW`, `Heap.complement`, `complementSep`, `mappedHeap`, `memMapped`) used by `ProofLib` adequacy and frame proofs.
  - `ProofLib/PrologueFrame.lean`: Untrusted prologue disassembler (`inferPrologueFrameBytes?`), $O(n \log n)$ symbol table (`Obj.funcTable`, `Obj.fnSize`), and symbol-keyed `stackFrameFor`.
  - `ProofLib/SepLogic/WP/Defs.lean`: Untrusted `SepWP`, `SepWPp`, `SepLoad*` / `SepStore*`, `SepFrame`, and `applyWriteback` definitions underlying the `wp_*` tactics (built on `Arm64.Trusted.Spec.SepLogic`; not imported by any `Spec.lean` file).
- **Core Separation Logic & Memory Algebra**:
  - `ProofLib/SepLogic/Exists.lean`: Propositional extensionality (`sepProp_ext` / `Entails.antisymm`), `∃∗` combinators (`sepExists_congr`, `Entails.sepExists_mono`, `sepExists_pure_sepConj`, `Entails.sepExists_intro`/`_right`/`_elim`, `sepExists_sepConj_left`/`_right`, `satisfies_sepExists`), partial-heap destructuring (`Satisfies.sepConj_elim`), per-byte ownership (`OwnsRW`/`OwnsRO`, `ownsRW_sepConj_left`/`_right`, `OwnsRW.of_entails`, `ownsRW_pointsToBytes_at`), value-carrying per-byte ownership (`OwnsCell`, `ownsCell_sepConj_left`/`_right`, `ownsCell_pointsToBytes`, `OwnsCell.of_entails`), satisfiable conjuncts (`SepProp.sat_of_sepConj_left`/`_right`), and bounded footprint support (`SupportedOn`).
  - `ProofLib/SepLogic/Fresh.lean`: Address freshness from `∗`: a separated 64-bit cell lies outside a separated `memRegion` (`pointsTo64_byte_not_inRegion`, wrap-safe `Nat`-interval `pointsTo64_outside_memRegion` and its `Satisfies.` / `Entails.` forms), `ownsRW_pointsTo32_at`, `Entails.extract_heap_fact` and `entails_pure_keep` (`Entails.pure_keep`) / `entails_pure_in_frame` to extract or retain pure conjuncts across frames, and universal physical/mapped footprint bounds (`SepProp.FootprintIn`, `SepProp.BoundedFootprint`, `SepProp.holds_sepExists`, `SepProp.holds_pure_sepConj`).
  - `ProofLib/SepLogic/Cells.lean`: Exact ownership of a physical cell map `ownCells c` (no ghost slots, no mapping tokens) for byte footprints described pointwise: cut or rejoin one cell (`ownCells_cut_rw` / `ownCells_cut_ro`), duplicate a read-only cell (`ownCells_dup_ro`), split by an address predicate (`ownCells_split`) or join disjoint maps (`ownCells_union`), `ownCells_none = emp`, read a cell back from an entailment (`ownCells_rw_of_entails` / `_ro_of_entails`), and iterated address-set separating conjunctions (`BigSep`, `SetSep`, `WordMap`, `upd` with focus, unfocus, insert, split, and `NoRO` laws). Imported directly, not through the `ProofLib` umbrella.
  - `ProofLib/SepLogic/FreshRO.lean`: Heap-level read-only/read-write byte disjointness across `∗` (`ownsRO_ownsRW_disjoint_sepConj`, `ownsRW_ownsRO_disjoint_sepConj`), for `Entails` proofs that a read-write owned byte is not a read-only byte of a separated assertion.
  - `ProofLib/SepLogic.lean`: Core `SepProp` combinators (`Std.Associative`/`Std.Commutative` instances, `pure_true_sepConj`, `sepConj_pure_true`, `pure_sepConj_of_true`, `pure_false_sepConj`, `sepConj_pure_false`, `pure_sepConj_congr`, `extract_pure`), typed points-to (`↦₈`..`↦₁₂₈`) and read-only (`↦ᵣ`) lemmas, `IsBlock` / `SepBlock` reflection.
  - `ProofLib/SepLogic/Basic.lean`: Partial-heap extension order (`Heap.Subheap`), persistent read-only core (`Heap.core`), bi-entailment equality (`SepProp.eq_of_entails`), step-indexed upward-closed `ISepProp` with monoidal embedding `⌈P⌉ᵢ` (`satisfiesAt_ofSepProp_iff`, `satisfies_ofSepProp_iff`), `Satisfies.of_entails`, and frame-preserving freeze updates (`bupd_sep`, `Satisfies.of_bupd_entails`, `Satisfies.of_bupd_frame_left`, `pointsTo8_freeze_ro`, `pointsTo64_freeze_ro`).
  - `ProofLib/SepLogic/Frame.lean`: Frame preservation theorems (`AgreesOutside`, `InRegion`, disjointness) and the proof-side byte predicates `BytesAgree` / `MemMatchesBytes`.
  - `ProofLib/SepLogic/Region.lean`: Contiguous byte region splitting and multi-offset partitioning (`memRegion_split`, `memRegion_split_le`, `memRegion_split_sub`, `memRegion_split3`, `memRegion_split3_ord`, `memRegion_merge3`, `memRegion_byte_merge`, `memRegion_partition`, `memRegion_partition_at`, `memRegion_succ_off`), read-only region properties (`memRO_subregion`, `memRO_perm_ro`, `memRO_frozen`), and 64-bit word list region bridges (`pointsToWords64_append`, `pointsToWords64_entails_memRegion`, `memRegion_entails_pointsToWords64`).
  - `ProofLib/SepLogic/ImageData.lean`: Per-byte decomposition of the trusted image segments `imageInitialDataBss` / `imageDataBss` into `byteCells (dataCell …)` / `byteCells (dataCellAny …)` (`imageInitialDataBss_entails`, `imageInitialDataBss_entails_byteCells`, `byteCells_dataCellAny_entails_imageDataBss`, `load_data_length_le`), splitting at section boundaries (`byteCells_append_off`, `byteCells_take_drop`), and uniform slices as `↦ᵣ` / `↦ₛ` / `memRegion` (`byteCells_dataCell_ro`/`_rw`, `byteCells_dataCellAny_ro`/`_rw`, `memRegion_entails_byteCells_dataCellAny`). Use it to build a library's `Env` invariant from the freshly loaded image and to hand the segment back after the run.
  - `ProofLib/SepLogic/ImageDataAny.lean`: The remaining directions (`imageDataBss_entails_byteCells_dataCellAny`, `imageDataBss_entails`, `byteCells_dataCell_entails_imageInitialDataBss`) and read-only cell duplication out of either segment (`imageDataBss_dup_pointsTo8RO` / `_pointsToBytesRO` / `_pointsTo64RO`, `imageInitialDataBss_dup_*`, `imageInitialDataBss_roByte`).
  - `ProofLib/SepLogic/Bytes.lean`: Byte-slice points-to algebra (`pointsToBytes_append`, `pointsToBytes_singleton`, `pointsToBytes_snoc`, `pointsToBytes_take_drop`, `pointsToBytes_cons_off`, `pointsToBytes_append_off`, `pointsToBytes_split_last`, `pointsToBytes_split3`, `pointsToBytesRO_split3`, `pointsToBytes_focus8`..`focus64`, `pointsToBytes_split_at`, `pointsToBytes_merge_at`, `pointsToBytes_split_at32`, `pointsTo64_outside_pointsToBytes`), LE/BE word unpacking/packing (`unpack64`, `unpack32`, `unpackL`, `unpack32BE`, `unpack64BE`, `pack16`, `pack32`, `pack64`, `pointsTo8_pair`, `pointsTo16_split8`, `pointsTo16_pair`, `pointsTo32_split16`, `pointsTo8_quad`, `pointsTo32_split8`, `pointsTo16_quad`, `pointsTo64_split16`, `pointsTo64_split32_at`, `pointsTo32_merge64_lo`, `pointsTo64_pair`, `pointsTo128_split64`), and `Memory.writeBytes` / `Memory.readBytes` bridges (`satisfies_writeBytes`, `Memory.readBytes_add`, `Memory.readBytes_take_drop`, `Memory.read8_of_readBytes`..`read64_of_readBytes`).
  - `ProofLib/SepLogic/SliceArray.lean`: Window-first sub-slice extraction and functional byte writes (`ByteSlice.slice`, `ByteSlice.write`, `pointsToBytes_focus`, `pointsToBytesRO_focus`, `pointsToBytes_write`, `pointsToBytes_write_len`), compositional little-endian byte accumulation (`ByteSlice.readLE`, `ByteSlice.readLE_add`, `pointsToBytes_focus64_le`), typed word updates inside byte slices (`ByteSlice.write8`..`write64`, `pointsToBytes_update8`..`update64`), function-indexed separating ranges (`sepRange`, `sepRange_add`, `sepRange_focus`, `sepRange_update`, `sepRange_congr`), and `getD`-indexed fixed-stride typed element arrays and bridges (`pointsToArray`, `pointsToArray_eq_sepRange`, `pointsToWords64_eq_pointsToArray`, `pointsToBytes_eq_pointsToArray`, `pointsToArray_focus`, `pointsToArray_update`, `pointsToArray_focus_shift`, `pointsToArray_update_shift`, `pointsToArray_focus_mul`, `pointsToArray_entails_memRegion`, `pointsToBytes_replicate_eq_pointsToArray`).
  - `ProofLib/SepLogic/ByteSliceAttr.lean`: Registers the `[byteslice]` simp attribute used by `SliceArray.lean` to normalize `ByteSlice` window extraction, splicing, little-endian unpacking, and indexing algebra.
  - `ProofLib/SepLogic/ByteRegion.lean`: Byte-region loop invariant models (`ByteSlice.fillSet`, `ByteSlice.copySet`, `fillPrefix`, `copyPrefix`, `copySuffix`, `bcast64`), pointwise `getD` lemmas, write-collapse lemmas (`write8_fillSet`, `writeLE_fillSet`, `writeLE_copySet`, `write64_copySet_readLE`, …), end-of-loop lemmas (`fillPrefix_full`, `copyPrefix_full`, …), and the tactics `byte_region_len`, `byte_region_eq`, `byte_region_entails`.
  - `ProofLib/SepLogic/Stack.lean`: Stack cell lists (`cells`, `cells_split`, `cells_split_sub`, `cells_sub_succ_entails`, `stackAt_eq_cells`), `stackAt` splitting (`stackAt_split_cells`, `stackAt_split_bottom`), `spAligned_sub` / `spAligned_sub_beq`, and `stackFrameFor` frame automation.
- **Entailment & Symbolic Execution**:
  - `ProofLib/SepLogic/Solver.lean`: Reflective AC entailment and frame-cancellation solver (`sep_entail`, `sep_eq`, `sep_focus`, linear `.consumeMData`, `canRead_of_words`, `canWrite_of_words`, `canRead_of_wordsRO`).
  - `ProofLib/SepLogic/WP.lean` (and `ProofLib/SepLogic/WP/{StateNorm,Access,StepsCore,StepsSimd,StepsSubword,Syscalls,StepsProcess,Structural,ProjGuardAttr,TacticCore,PairStep,StepTactic,StateTransport,FrameTransportAttr,ControlTactics,FrameAuto}.lean`): Interactive weakest-precondition engine (`wp_init`, `wp_step`, `wp_steps`, `wp_steps_to_call`, `wp_steps_to_ret`, `wp_steps_to_insn`, `wp_cut_call`, `wp_call`, `wpp_call`, `wpp_call_frozen`, `wp_frame_transport`, `wp_tailcall`, `wp_if`, `wp_loop`, `wp_done`, `split_callee_saved`, `wp_simp_pre`, `wp_conv_pre`, `wp_focus_close`), table-projection guard simp set (`[wp_proj_guard]`), subword/load-acquire/store-release step lemmas (`SepWP.step_ldar32`, `SepWP.step_ldar32_64`, `SepWP.step_stlr32`, `SepWP.step_stlr64`, `SepWP.step_ldar64`), Linux `SVC #0` syscall rules (`SepWP.step_svc_openat_ro`, `SepWP.step_svc_read`, `SepWP.step_svc_close`, `SepWP.step_svc_clock_gettime`, `SepWP.step_svc_brk_query`, `SepWP.step_svc_brk_grow`, `SepWP.step_svc_brk_grow_bytes`, `SepWP.step_svc_brk_grow_page`, `UnmappedBetween`, `pageMask_toNat`, `SepWP.step_svc_mmap_page`, `SepWP.step_svc_write_stdio`, `traceStreamBytes_append`, `traceStreamBytes_ofBytes_stdout`, `traceStreamBytes_ofBytes_stderr`, `traceStreamBytes_stdout_ofBytes`, `traceStreamBytes_stderr_ofBytes_stdout`, `exit_ok_of_sepWP_svc`, `SepWP.carve_bytes`), and process-level step/preservation/stripping/focusing lemmas (`ProcessFieldsPreserved`, `ProofLib.NonSyscallPreserved`, `ProofLib.NonSyscallPreserved_mk`, `ProofLib.NonSyscallPreserved_setTpidrEl0`, `ProofLib.setMem_setTpidrEl0_NonSyscallPreserved`, `SepWP.lift_noSyscalls`, `steps_lift_noSyscalls`, `execInst_mrs_tpidr_el0`, `SepWP.step_mrs_tpidr_el0`, `SepWP.step_msr_tpidr_el0`, `execSetTidAddress_eq`, `pointsToWords64_focus`, `pointsToWords64_focus_idx`, `pointsToWords64_focus_pair`, `execInst_brk_oracle_of_not_isSvc0`, `stripS`, `execInst_stripS`, `steps_pureMem_lift_stripS`, `ProofLib.noSvc0Window`, `ProofLib.holdsBytes_rx_not_isSvc0`).
  - `ProofLib/SepLogic/WP/PairStep.lean`: pair-step hook for placed code. When the instruction at `b + off` of `(C a₁ … aₙ).rebase b X` cannot be fetched (e.g. a relaxable `ADRP`+`ADD` pair that the linker may rewrite to `NOP`+`ADR`), `wp_step` / `wp_steps` / `wp_sym_step(s)` apply a user lemma `C_pairStep_0x<off>` that steps both words for every encoding. It fails loudly if a side condition cannot be discharged.
  - `ProofLib/SepLogic/CodeLookup.lean`: Compile-time code/relocation lookup and symbol-relative cut-point elaborators (`code_off%`, `code_rel%`, `code_lemma%`, `reloc_call_off%`, `reloc_call_insns%`, `words_ret_off%`, `words_condbr_off%`, `words_insn_off%`, `code_call_off%`, `code_call_addr%`).
  - `ProofLib/SepLogic/SymWP/InsnSteps.lean`: Per-instruction symbolic step lemmas and `Sym.Simp` rewrite rules (primary review surface for Lean symbolic execution).
  - `ProofLib/SepLogic/SymWP.lean`: Fast `SymM` hash-consed symbolic execution tactics (`wp_sym_step`, `wp_sym_steps`, `wp_clear_temps`).
  - `ProofLib/SepLogic/SymBlock/`: Reflective whole-block symbolic execution (`sym_block`); see its README.
  - `ProofLib/SepLogic/BlockSummary.lean`: Segment summaries (`block_summary`, `wp_block`): symbolically execute a straight-line instruction range once and save it as a reusable continuation-style `SepWP` lemma, generic in the program, code address, values and frame.
  - `ProofLib/SepLogic/CondClassify.lean`: Branch condition classifier (`decideCond?`) for `wp_steps` / `wp_if`.
  - `ProofLib/SepLogic/Entry.lean`: Symbol-keyed function entry setup (`wp_entry`, `wpp_entry`, `wp_init_fn`, `EntrySafe`). Default to `wp_entry` (pure `SepWP`, `onPanic = ⌜False⌝`) and weaken if needed with `subroutine_ok_mono` / `SepWPp.of_sepWP_ret`; use `wpp_entry` (`SepWPp`) only when a panic is genuinely reachable under `pre` (see `docs/dev/guides/writing-proofs.md` §2.1).
  - `ProofLib/SepLogic/SafeSepWP.lean`: Framed partial-correctness weakest precondition (`SafeSepWP`, `SafeSepWP1`) for proving `safe_subroutine_ok`: total `SepWP` segments (`SafeSepWP.of_sepWP`), partial callees (`SafeSepWP.call_subroutine_frame`), loops without a termination measure (`SafeSepWP.loop`), and the entry / return rules (`safe_subroutine_ok_of_safeSepWP`, `SafeSepWP.ret_of_sepWP`).
  - `ProofLib/SepLogic/WPp.lean`: Panic-aware weakest preconditions (`SepWPp`) for code with genuinely reachable panic/trap paths (e.g. fallible allocation via `allocFailedIn` / `Rust.withPanics`); cut straight-line segments into pure `SepWP` with `SepWPp.of_sepWP` (`wp_cut_call` / `sepWPp_cut_call` in `WP/Structural.lean` & `WP/ControlTactics.lean`).
  - `ProofLib/SepLogic/WPFrozen.lean`: `SepWP` / `SepWPp` composition and call rules that thread `img.FrozenLoaded` and `symtab = img.symtab` across segments and calls (`SepWP.seq_frozen`, `SepWP.of_sepWP_frozen`, `SepWPp.of_sepWP_frozen`, `SepWP.call_subroutine_frame_frozen`, `SepWPp.call_wpp_frozen`, `SepWPp.call_frame_frozen`, `SepWPp.call_inImage_frame`, powering `wpp_call_frozen`).
  - `ProofLib/SepLogic/CFG.lean`: Step-indexed CFG cutpoint fixpoints (`SepWP.CFGStep`, `SepWP.cfg_fixpoint_tree`, `SepWP.cfg_fixpoint_sep`), DAG join points (`SepWP.join`, `SepWP.ite_join`, `wp_join`, `wp_if_join`), and loop combinators (`SepWP.loop_fuel`, `SepWP.loop_measure`, `SepWP.loop_multi_exit`, `SepWP.loop_latch`, `SepWP.nested_loop`).
  - `ProofLib/SepLogic/LoopTactics.lean`: Loop tactic front-ends `wp_loop_measure`, `wp_loop_list`, `wp_nested_loop` (with `frame` variants threading `LoopFrame` via `SepWP.loop_measure_framed` / `SepWP.loop_list_framed`) and `SepWP.nested_loop_simple`. See the decision table in `docs/dev/guides/writing-proofs.md` §4.
  - `ProofLib/SepLogic/Tests.lean`: Unit and regression tests for `SepLogic` tactics and lemmas.

---

## Quick Lookup Table ("Which file to import/read for X")

| Topic / Tactic / Definition | File | Role |
| :--- | :--- | :--- |
| Interactive WP tactics (`wp_init`, `wp_step`, `wp_steps`, `wp_steps_to_call`, `wp_steps_to_ret`, `wp_cut_call`, `wp_call`, `wpp_call`, `wpp_call_frozen`, `wp_if`, `wp_loop`, `wp_done`, `wp_simp_pre`, `wp_conv_pre`, `wp_focus_close`), load-acquire/store-release (`SepWP.step_stlr32`, `SepWP.step_stlr64`, `SepWP.step_ldar64`), syscall (`SepWP.step_svc_*`, `UnmappedBetween`, `pageMask_toNat`, `traceStreamBytes_*`, `exit_ok_of_sepWP_svc`, `SepWP.carve_bytes`), and process-preservation/lifting/focusing (`ProcessFieldsPreserved`, `ProofLib.NonSyscallPreserved`, `SepWP.lift_noSyscalls`, `execInst_mrs_tpidr_el0`, `SepWP.step_msr_tpidr_el0`, `pointsToWords64_focus`, `pointsToWords64_focus_pair`, `execInst_stripS`, `steps_pureMem_lift_stripS`) rules | `ProofLib/SepLogic/WP.lean` (`ProofLib/SepLogic/WP/*.lean`) | `Proof` |
| Compile-time code/relocation lookup & call-site cut points (`code_off%`, `code_rel%`, `code_lemma%`, `reloc_call_off%`, `reloc_call_insns%`, `words_ret_off%`, `code_call_off%`, `code_call_addr%`) | `ProofLib/SepLogic/CodeLookup.lean` | `Proof` |
| Partial-heap `Subheap`, `SepProp.eq_of_entails`, step-indexed `ISepProp` (`⌈P⌉ᵢ`), `Satisfies.of_entails`, and freeze updates (`pointsTo8_freeze_ro`, `pointsTo64_freeze_ro`, `Satisfies.of_bupd_frame_left`) | `ProofLib/SepLogic/Basic.lean` | `Proof` |
| Step-indexed CFG fixpoints, diamond join points, and loop combinators (`SepWP.CFGStep`, `SepWP.cfg_fixpoint_tree`, `SepWP.cfg_fixpoint_sep`, `SepWP.loop_fuel`, `SepWP.loop_measure`, `wp_join`, `wp_if_join`) | `ProofLib/SepLogic/CFG.lean` | `Proof` |
| Loop tactic front-ends (`wp_loop_measure`, `wp_loop_list`, `wp_nested_loop`, `LoopFrame`) | `ProofLib/SepLogic/LoopTactics.lean` | `Proof` |
| Contract lookup at call sites (`@[wp_spec]` address-indexed contract database, `wp_apply`, `wp_apply using h`, `wp_apply?`, `wp_apply (frame := P)` frame-procedure hook, `wp_spec_intro`); `import ProofLib.SepLogic.WP.Apply` | `ProofLib/SepLogic/WP/Apply.lean` | `Proof` |
| Symbol-keyed function entry setup, local `fnAddr` / `b + off#64` callee bridging, & symbol-relative call helpers (`wp_entry`, `wpp_entry`, `wp_init_fn`, `wp_code_init`, `fn_rebase%`, `callee_call%`, `callee_call_back%`, `hook_call%`, `fnAddr_callee_of_fnOff`, `base_add_callee_of_fnOff`, `callee_ok_at_of_fnOff`, `subroutine_ok_of_trampoline`, `EntrySafe`) | `ProofLib/SepLogic/Entry.lean` | `Proof` |
| Fast `SymM` hash-consed symbolic execution (`wp_sym_step`, `wp_sym_steps`, `wp_clear_temps`) | `ProofLib/SepLogic/SymWP.lean` | `Proof` |
| Per-instruction symbolic step & `Sym.Simp` rewrite rules (primary review surface for Lean symexec) | `ProofLib/SepLogic/SymWP/InsnSteps.lean` | `Proof` |
| Reflective whole-block symbolic execution (`sym_block`): advisor + one kernel-evaluated block rule (`SepWP` and `SepWPp`, left-nested `∗` flattening, associative address normalization, `↦₈`..`↦₁₂₈` and `↦ᵣ` cells, 128-bit `Q` struct copies, and 32/64-bit flag & scalar ALU/branch coverage) | [`ProofLib/SepLogic/SymBlock/`](SymBlock/README.md) | `Proof` |
| Segment summaries: prove a straight-line range once (`block_summary name binders : BlockSegment prog s P stop [using tac]`) and reuse it under any target/postcondition/frame (`wp_block name`) | `ProofLib/SepLogic/BlockSummary.lean` | `Proof` |
| Panic-aware weakest preconditions (`SepWPp`, `wpp_call`) and `FrozenLoaded`-threading call rules (`wpp_call_frozen`, `SepWPp.of_sepWP_frozen`, `SepWPp.call_wpp_frozen`) | `ProofLib/SepLogic/WPp.lean`, `ProofLib/SepLogic/WPFrozen.lean` | `Proof` |
| Branch condition classification (`decideCond?`) | `ProofLib/SepLogic/CondClassify.lean` | `Proof` |
| Bounded `omega` / `bv_omega` for the automation's arithmetic side goals: relevance-pruned contexts (`omegaPruneGoal`, `OmegaTier`), `Nat`-subtraction gate, heartbeat-capped and runtime-guarded attempts that never admit a goal (`runTacClosed`, `runTacCapped`, `proveOmegaBounded?`, tactic `wp_omega_bounded`) | `ProofLib/SepLogic/OmegaBounded.lean` | `Proof` |
| Backtracking frame inference & cancellation (`sep_frame`, `sep_frame?`, `sep_frame_apply`; frame-procedure hook `SepFrameInfer.frameProc` for contract-application tactics), frame-inferring `SepWP` rules (`SepWP.frame_auto`, `SepWP.call_subroutine_frame_auto`, `SepWP.weaken_left`), and `SepWP` region/slice/cell view-shift combinators (`SepWP.region_split`, `SepWP.region_merge`, `SepWP.region_split3`, `SepWP.region_merge3`, `SepWP.byte_merge`, `SepWP.region_head`, `SepWP.region_last`, `SepWP.words_bytes16`, `SepWP.bytes16_words`, `SepWP.open_cells`, `SepWP.reframe`, `SepWP.memRegion_bytes`, `SepWP.bytes_memRegion`, `SepWP.bytes_congr`, `SepWP.bytes_word`, `SepWP.bytes8_cell`, `SepWP.memRegion8_cell`, `SepWP.memRegion4_cell`, `SepWP.memRegion_join`, `SepWP.bytes_join`, `SepWP.unshrink_stack`, `SepWP.to_offset2`, `SepWP.from_offset2`) | `ProofLib/SepLogic/FrameInfer.lean`, `ProofLib/SepLogic/WP/FrameAuto.lean` | `Proof` |
| Reflective AC entailment & frame solver (`sep_entail`, `sep_focus`, `canRead_of_words`, `canWrite_of_words`, `canRead_of_wordsRO`) | `ProofLib/SepLogic/Solver.lean` | `Proof` |
| Typed points-to (`↦₈`, `↦₁₆`, `↦₃₂`, `↦₆₄`, `↦₁₂₈`, `↦ₛ`), read-only assertions (`↦ᵣ`, `↦₆₄ᵣ`, `↦₃₂ᵣ`, `↦₁₆ᵣ`, `↦₈ᵣ`, `↦₁₂₈ᵣ`, `↦₆₄ᵣ*`), proof-only predicates (`StackPreserved`, `Memory.RW`, `Heap.complement`, `complementSep`, `memMapped`), and pure-`sepConj` combinators (`extract_pure`, `pure_sepConj_congr`) | `Arm64/Trusted/Spec/SepLogic.lean`, `ProofLib/SepLogic/Defs.lean`, & `ProofLib/SepLogic.lean` | `Spec` / `Proof` |
| Byte-slice algebra, indexed focus, LE/BE word packing/unpacking, & `writeBytes`/`readBytes` bridges (`pointsToBytes_append`, `pointsToBytes_split3`, `pointsToBytes_focus8`..`focus64`, `pointsToBytes_split_at`, `pointsToBytes_merge_at`, `unpack64`/`unpack32`/`unpackL`/`unpack32BE`/`unpack64BE`, `pack16`/`pack32`/`pack64`, `satisfies_writeBytes`, `Memory.readBytes_take_drop`, `Memory.read8_of_readBytes`..`read64_of_readBytes`) | `ProofLib/SepLogic/Bytes.lean` | `Proof` |
| Memory regions, multi-offset partitioning, `memRO` properties, & `pointsToWords64` bridges (`InRegion`, `AgreesOutside`, `BytesAgree`, `memRegion_split_le`, `memRegion_split3`, `memRegion_partition`, `memRegion_partition_at`, `memRO_subregion`, `pointsToWords64_entails_memRegion`, `memRegion_entails_pointsToWords64`) | `ProofLib/SepLogic/Frame.lean`, `ProofLib/SepLogic/Region.lean` | `Spec` / `Proof` |
| Stack frames, prologue frame inference, & cell splitting (`cells`, `cells_split`, `cells_split_sub`, `stackAt_eq_cells`, `stackAt_split_cells`, `spAligned_sub`, `spAligned_sub_beq`, `stackFrameFor`) | `ProofLib/SepLogic/Stack.lean`, `ProofLib/PrologueFrame.lean` | `Proof` |

---

## Navigation Rule

Several files in `ProofLib/SepLogic/` are large tactic or lemma libraries (`WP.lean`, `SymWP.lean`, `Solver.lean`, `Bytes.lean`, `ProofLib/SepLogic.lean`). **Never read these files end-to-end with `view_file`**:

1. **Read the top-of-file `/-! ... -/` header first** (`view_file` with `StartLine=1, EndLine=35`) to check the module's role and exported interface.
2. **Query lemma signatures by name or pattern** using `.agents/skills/lean-signatures/lean-sig lookup <pattern>` (e.g., `.agents/skills/lean-signatures/lean-sig lookup pointsToBytes_split`).
3. **List all declarations and line numbers in a file** using `.agents/skills/lean-signatures/scripts/lean-outline <File.lean>` (or `.agents/skills/lean-signatures/lean-sig outline <File.lean>`), then `view_file` only the target 50–150 line window before editing.

---

## Which Lemma / Tactic for Which Goal Shape

| Goal Shape | Reach For | Notes |
| :--- | :--- | :--- |
| Carve `[off, off + n)` out of `base ↦ₛ bs` before a call / `wp_steps` | `rw [pointsToBytes_focus base bs off n (by omega)]` | Window comes first; surrounding frame is `(prefix ∗ suffix)`. Never hand-unfold `take`/`drop`. |
| Reassemble window after `(base + off) ↦ₛ src` changes | `rw [pointsToBytes_write base bs src off (by omega)]` (or `_write_len`) | Produces `base ↦ₛ ByteSlice.write bs off src`; use `ByteSlice.write_length` for lengths. |
| Multiple non-overlapping windows inside a region | `rw [memRegion_partition base total [o₁, …]]` | Automatically computes slice lengths and discharges bounds. |
| 64/32/16/8-bit load or store inside `base ↦ₛ bs` | `pointsToBytes_focus64/32/16/8` (load), `pointsToBytes_update64/32/16/8` (store) | 64-bit value can be folded to `ByteSlice.readLE bs off 8` via `pointsToBytes_focus64_le`. |
| `SepLoad*` / `SepStore*` into `base ↦ₛ bs` / `base ↦ᵣ bs` with symbolic `bs` or offset (`dst + ofNat 64 k + 32#64`, `dst + n - 16#64`) | `wp_sep_access` (automatic inside `wp_steps` / `wp_sym_steps`); lemmas `SepStore8/16/32/64.of_pointsToBytes`, `SepLoad64.of_pointsToBytes_readLE` | Needs the bound `off + w ≤ bs.length` provable by `byte_region_len` from context (e.g. `bs.length = n`, `k + 8 ≤ n`). Stores give `base ↦ₛ ByteSlice.writeW bs off v`; 64-bit loads give `ByteSlice.readLE bs off 8`. For a proof that steps such accesses by hand, turn this off with `set_option proofLib.wpSymbolicBytes false`. |
| Spatial invariant of a byte-fill / byte-copy loop | `ByteSlice.fillPrefix bs b k`, `ByteSlice.copyPrefix old src k`, `ByteSlice.copySuffix old src k` (general: `fillSet` / `copySet`) in `ProofLib/SepLogic/ByteRegion.lean` | `P_inv k _ := dst ↦ₛ ByteSlice.fillPrefix bs0 b (n - (k + 1))` with `wp_loop_measure`; close the initial entailment with `byte_region_entails`; see `Examples/Testing/ProofLib/ByteRegion.lean`. |
| Loop step ending in a conditional back-edge (`b.ne head`) to the `SepWP` target | `wp_steps; wp_done` (or `wp_sym_steps; wp_done`) | Once the branch is decided towards the target, the stepper stops at the target and adds the decided condition as `hcond`. To resolve the branch and keep stepping instead (the old behavior), use `set_option proofLib.wpStopAtBranchTarget false`. |
| `ByteSlice.write* (fillSet/copySet …) off v = fillSet/copySet … p'` | `write8_fillSet`, `writeLE_fillSet`, `write64_fillSet_bcast64`, `write8_copySet`, `writeLE_copySet`, `write64_copySet_readLE`, `write16_copySet_pack16`, `write32_copySet_pack32` (prefix forms `write8_fillPrefix`, `write8_copyPrefix`, `write64_copyPrefix_readLE`, `write16_copyPrefix_pack16`, `write32_copyPrefix_pack32`) | Or `byte_region_eq` (extensionality on `getD` + `omega`); `wp_done` tries it on `↦ₛ` / `↦ᵣ` byte lists. 16/32-bit loads from a byte list come out as `pack16` / `pack32`. |
| Store of a byte broadcast (`bcast64 b`, or its `truncate 16/32/8` for `strh` / `str w` / `strb`) into a byte region | `write16/32/64_fillSet_bcast64`, `write16/32/64_fillPrefix_bcast64`, `write16/32/64_bcast64` (plain list), `extractLsb'_bcast64_trunc`, `bcast64_truncate8` | `byte_region_eq` knows the truncated-broadcast byte lemmas, so `wp_done` closes these directly. |
| Byte-region invariant at loop exit (`fillPrefix bs b n`, `copyPrefix old src n`) | `fillPrefix_full`, `copyPrefix_full`, `copySuffix_zero`, `fillSet_all`, `copySet_all` | Identities at entry: `fillPrefix_zero`, `copyPrefix_zero`, `copySuffix_len`. |
| `off + w ≤ (ByteSlice.write* (fillSet …) …).length` | `byte_region_len` | `omega` after the `fillSet` / `copySet` / `write*` / `replicate` length lemmas. |
| Partial tail `k < 8` bytes accumulated in an `X` register | `ByteSlice.readLE_add`, `ByteSlice.readLE_succ`, `ByteSlice.readLE_one` | Composes any `(k + j)`-byte little-endian tail directly in machine `\|\|\|` / `<<< (8 * k)` order. |
| Fixed-stride array element `i` (`ptr + stride * i` or `ptr + (idx <<< k)`) | `pointsToArray_focus`, `pointsToArray_focus_shift` (load); `_update`, `_update_shift` (store); `pointsToWords64_focus`, `pointsToWords64_focus_pair` (for `↦₆₄*` word lists) | Element value is `xs.getD i default` (`[Inhabited α]`), avoiding proof-carrying list indices. |
| Zero-initialized byte region as a fixed-stride array | `pointsToBytes_replicate_eq_pointsToArray` | Converts `(ptr ↦ₛ List.replicate (stride * n) b)` directly to `pointsToArray`. |
| Chained symbolic offsets `base + ofNat w a + ofNat w b` / `- ofNat w b` | `simp only [addr_norm]` (`BitVec.add_ofNat_add_ofNat`, `BitVec.add_ofNat_sub_ofNat_of_le`) | Normal form is `base + BitVec.ofNat w (Nat expr)`. |
| Case split on a Boolean or `Prop` condition in precondition/postcondition | `wp_by_cases hc : cond` | Splits on `cond` and simplifies `ite`/`dite` across precondition and goal in both branches. |
| Stack frame as region or 64-bit word slice | `stackFrameAt_eq_memRegion`, `stackFrameAt_eq_pointsToWords64`, `stackFrameAt_eq_exists_pointsToWords64` | Directly bridges downward-growing `stackFrameAt` frames to `memRegion` and `↦₆₄*`. |
| `P = Q` between SepProps | `sepProp_ext (h₁ : P ⊢ Q) (h₂ : Q ⊢ P)` | Never unseal `Entails`. |
| `∃∗` in goal / hyp / under `=` | `Entails.sepExists_right x`, `Entails.sepExists_elim`, `sepExists_congr`, `simp [satisfies_sepExists]` | Never `unfold`/`simp only [sepExists]`. |
| Split `m ⊨ P ∗ Q` / footprint facts | `Satisfies.sepConj_elim`, `OwnsRW`/`OwnsRO`/`OwnsCell`, `SupportedOn`, `IsBlock`/`SepBlock`, `SepProp.FootprintIn`, `SepProp.BoundedFootprint`, `sep_entail` | Never unseal `Heap.*`/`SepProp.*`. |
| `m ⊨ addr ↦ₛ bs` or a `SupportedOn` footprint from `Obj.HoldsBytes m addr bs perm` (loaded image bytes) | `Satisfies.pointsToBytes_of_holdsBytes_rw`, `SupportedOn.of_holdsBytes_rw` / `_ro`, `SupportedOn.of_pointsToBytes` (in `ProofLib/SepLogic/Exists.lean`) | Combine disjoint footprints with `SupportedOn.sepConj` and close with `SupportedOn.satisfies`. Never unseal `regionHeap` / `SepProp.Satisfies`. |
| Cut one byte cell out of (or back into) an invariant that owns an irregular byte footprint described pointwise (`c a = some (.rw b)` / `some (.ro b)` / `none`) | State it as (or prove it equal to) `ownCells c`, then `ownCells_cut_rw` / `ownCells_cut_ro` / `ownCells_dup_ro` / `ownCells_split` (in `ProofLib/SepLogic/Cells.lean`) | Read a cell back from `ownCells c ⊢ (a ↦₈ b) ∗ R` with `ownCells_rw_of_entails` / `_ro_of_entails`. Never unseal `Heap.*` / `SepProp.sepConj`. |
| Extract pure/heap fact or lift `reaches_pc` under `SepWP` | `SepWP.with_pre`, `SepWP.weaken_pre`, `SepWP.of_reaches_pc`, `SepWP.to_reaches_pc` | Never unseal `SepWP`. |
| Weaken a `SepWP` precondition through a frame-preserving update (`P ⊢ \|==> Q`, e.g. `pointsTo64_freeze_ro`) | `SepWP.bupd_pre` | Never unseal `SepWP` / `bupd`. |
| Weaken a panic-free `SepWP` / `subroutine_ok` proof to `SepWPp` / `Spec.allowPanicWhen`, or step a pure `SepWP` segment inside `SepWPp` | `subroutine_ok_mono`, `SepWPp.of_sepWP_ret`, `SepWPp.of_sepWP` (`SepWPp.of_sepWP_frozen`), `wp_cut_call` / `sepWPp_cut_call`, `SepWPp.call_allowPanic_ret` | Prove the strongest panic-free `SepWP` spec first (`wp_entry`); use `SepWPp` only for reachable panics and cut straight-line work into `SepWP` (`docs/dev/guides/writing-proofs.md` §2.1). |
| Keep `imageDataBss obj base` / `imageInitialDataBss obj base` and also hand out a read-only image cell (`a ↦₈ᵣ v`, `a ↦ᵣ bs`, `a ↦₆₄ᵣ w`) | `imageDataBss_dup_pointsTo8RO` / `_pointsToBytesRO` / `_pointsTo64RO` (and `imageInitialDataBss_dup_*`) in `ProofLib/SepLogic/ImageDataAny.lean` | Per-byte hypothesis: `h.phys (a + ofNat j) = some (.ro bs[j])` for every `h` satisfying `imageInitialDataBss` (from `imageInitialDataBss_holds`). For the whole segment as cells, use `imageDataBss_entails` / `imageDataBss_entails_byteCells_dataCellAny`. Never unseal `imageDataBss`. |

---

## `wp_*` Failure Modes

### 1. Unresolved Conditional Branch (`wp_done`, `wp_call`, `wp_step`, `wp_sym_step`, `wp_loop_*`)

- **Symptoms (exact error texts):**
  - `wp_done` / `wp_call` (`ProofLib/SepLogic/WP/ControlTactics.lean`):
    ``wp_done: current PC is an unresolved conditional branch: condition: <cond> | then PC: <then_pc> | else PC: <else_pc> | hint: if both branches are reachable, split with `wp_if hcond` (or `wp_if_join <join_pc> <inv>` for diamond control flow); if only one branch is feasible, prove `have hcond : <cond> = true := by bv_omega` (or `= false`) before `wp_steps` / `wp_sym_steps`, or simplify the current PC with `wp_simp_pre [hcond]` `` (same format for `wp_call`).
  - `wp_step` (`ProofLib/SepLogic/WP/StepTactic.lean`) / `wp_sym_step` (`ProofLib/SepLogic/SymWP.lean`):
    ``wp_step: current PC is an unresolved conditional branch: condition: <cond> | then PC: <then_pc> | else PC: <else_pc>; use `wp_if hcond` or prove the branch condition before stepping`` (and the corresponding `wp_sym_step:` message; `wp_steps` / `wp_sym_steps` stop at the `ite` PC and under `set_option proofLib.wpVerbose true` emit an `info` diagnostic ``wp_steps: stopped at pc … (target …): branch condition unresolved at pc (condition: …); next: use `wp_if hcond` …``).
  - `wp_loop_measure` / `wp_loop_list` / `wp_nested_loop` (`ProofLib/SepLogic/LoopTactics.lean`):
    ``loop tactic: the current PC is an unresolved conditional branch, so the loop header cannot be determined: condition: <cond> | then PC: <then_pc> | else PC: <else_pc> | hint: `wp_step` / `wp_steps` already stepped the loop header's entry branch (`cbz` / `b.cond`), so `wp_loop_measure` / `wp_loop_list` / `wp_nested_loop` must be called at `head_pc` before stepping the header branch; otherwise, if both branches are reachable, split with `wp_if hcond` …``
- **Cause:** Stepping a conditional branch (`B.cond`, `CBZ`, `CBNZ`, `TBZ`, `TBNZ`) sets `s.pc` to `if <cond> then <then_pc> else <else_pc>`. If `<cond>` cannot be decided from local hypotheses (e.g. both arms are reachable, or a non-zero / no-overflow bound needed to decide `== 0#64` / `ult` / `ule` is missing from context), the stepper halts at the `ite` PC.
- **Fix:**
  1. **Both branches reachable:** split with `wp_if hcond` (or `wp_if_join <join_pc> <inv>` for a diamond):
     ```lean
     wp_steps
     wp_if h_z
     · wp_steps; wp_done
     · wp_steps; wp_done
     ```
  2. **Only one branch reachable (e.g. loop step or guarded path):** prove the branch condition or its arithmetic prerequisite (`≠ 0#64`, `base.toNat + 8 * (m + 1) < 2 ^ 64`) *before* `wp_steps` so the stepper auto-resolves the branch:
     ```lean
     have hk_nz : BitVec.ofNat 64 (m' + 1) ≠ 0#64 := by bv_omega
     wp_steps
     wp_done
     ```

### 2. Deprecated `if_pos` / `if_neg` / `cond_true` / `cond_false`

- **Symptoms (exact error texts):**
  - ``error: `if_pos` has been deprecated: Use `ite_eq_left` instead`` / ``error: `if_neg` has been deprecated: Use `ite_eq_right` instead``
  - ``error: `cond_true` has been deprecated: Use `Bool.cond_true` instead`` / ``error: `cond_false` has been deprecated: Use `Bool.cond_false` instead`` (plus ``Tactic `rewrite` failed: Did not find an occurrence of the pattern bif false then ?a else ?b`` when applied to `if … then … else …`).
- **Cause:** Lean 4 deprecated `if_pos`/`if_neg` and `cond_true`/`cond_false`; under `warningAsError` (enabled on the `ProofLib` and `Arm64` library targets, though not necessarily all `Examples/` targets) they fail the build. Furthermore, `Bool.cond_true`/`Bool.cond_false` rewrite boolean `bif b then x else y` (`cond`), not propositional `if b = true then x else y` (`ite`).
- **Fix:** Use `ite_eq_left` / `ite_eq_right` (or `dite_eq_left` / `dite_eq_right` for dependent `if h : c then …`), `simp only [hc, ↓reduceIte]`, or `wp_by_cases hc : cond` to split and reduce `ite`/`dite` in both precondition and goal:
  ```lean
  rw [ite_eq_left hc]           -- replaces `rw [if_pos hc]` on `if c then a else b`
  rw [ite_eq_right hnc]         -- replaces `rw [if_neg hnc]` (use `dite_eq_left`/`_right` for `if h : c`)
  simp only [hc, ↓reduceIte]    -- or reduce via `simp` (use `Bool.cond_false` only on `bif`)
  wp_by_cases hc : (n == 0#64)  -- splits `hc` and simplifies `ite`/`dite` in pre and post
  ```

### 3. Unsolved Goals After Symbolic Execution

| Symptom (Exact Error Text) | Cause | Fix |
| :--- | :--- | :--- |
| ``wp_done: current PC `<pc>` does not match target PC `<target_pc>` `` (with `hint:` for `BL`/`BLR`, `RET`, load/store, remaining step count before `target_pc` / `RET`, or `stepped <delta> bytes past target PC`) or ``wp_step: no step rule succeeded for instruction `<op>` … at PC `<pc>` spatial context points-to atoms: …`` (or `frame_split: no match for <atom> in precondition; candidates: …`) | `wp_steps` / `wp_sym_steps` stopped early before `target_pc` (or at a load/store missing a spatial points-to atom or slice bound `off + w ≤ bs.length`). | Run `wp_steps` for straight-line remaining steps, or add the byte-slice bound before stepping so `byte_region_len` closes `off + w ≤ bs.length`, or carve the window with `pointsToBytes_focus` / `memRegion_split_le` (enable `set_option proofLib.wpStrict true` to fail immediately at the stuck instruction). |
| `wp_done: closed current goal, but <n> unfocused goal(s) remain open: …` | An earlier tactic (`rw`, `by_cases`, `wp_if`, `constructor`) left unfocused side conditions, open `SepWP` / `SepWPp` execution goals, or `case pos` / `case neg` branch subgoals in the goal list. | Focus earlier subgoals with `·` and apply the suggested tactic (`omega`, `bv_arith`, `byte_region_len`, `wp_steps`, `wp_if`), or use `wp_done?` / `set_option proofLib.wpDoneAllowResidualGoals true` when intentionally leaving sibling goals open. |
| ``frame_split: no match for <target> in precondition`` followed by ``near-miss: target expects `<target>`, context has `<cand>`; remaining equality: `<lhs = rhs>` `` and ``hint: `have h : <lhs> = <rhs> := by bv_arith` `` | Target and context contain the same spatial predicate with address or length expressions that bounded `zetaDelta` / `subst_vars` / `arm64_norm` / `bv_lin` / `bv_arith` / `proveOmegaBounded?` normalization could not equate automatically (disable automatic rewriting with `set_option proofLib.frameSplitNearMiss false`). | Paste and discharge the emitted `have h : <lhs> = <rhs> := by bv_arith` (or `by omega` / lemma rewrite) right before `wp_frame_split` / `wp_call` / `wp_done`. |
| ``wp_done: postcondition value mismatch: actual: if (<cond>) = true then … expected: … | hint: actual value contains an unreduced conditional or width cast; use `wp_by_cases hc : <cond>` or `simp only [wp_norm, width_norm]` before `wp_done` `` (or `unsolved goals` with unreduced `(BitVec.zeroExtend 64 b).ule …` / `BitVec.setWidth`) | A `CSEL`/`CCMP` or narrow 8/32-bit comparison left a value-level `if` or width-cast (`zeroExtend`/`setWidth`) that `wp_norm` alone does not fold from `Nat` hypotheses. | Normalize width round-trips with `simp only [wp_norm, width_norm]`, split with `wp_by_cases hc : <cond>`, or prove the `BitVec` condition with `bv_omega` / `bv_solve` before `wp_done`. |
| ``arm64_norm: maximum recursion depth (`maxRecDepth`) reached while normalizing <loc>`` / ``wp_step: maximum recursion depth (`maxRecDepth`) reached while stepping instruction `<op>` at pc <pc>`` / info ``wp_steps: stopped before instruction #<k> (<k-1> stepped): it fails with `maxRecDepth` `` (the `arm64_norm` / `wp_step` errors are followed by `deepest term: <loc> (term depth N, most frequent head …)` and `hint:` lines), or a bare `maximum recursion depth has been reached` from a hand-written `simp [..., arm64_norm]` | A very deep term (long `writeReg64` / `writeBytes` state tower, long `x + c₁ + c₂ + …` chain, deep `let` value that is zeta-delta unfolded) is traversed by `simp` / unification, or, when no term is deep, extra lemmas or simp sets combined with `arm64_norm` (e.g. width / literal normalization) rewrite the same subterm back and forth. `wp_step` also rewrites with register / PC equations in context (`s.readReg64 r = v`), so a deep `v` breaks the step. | Shrink the reported term: `generalize hs : <tower> = s'` (or `obtain ⟨s', hs⟩ : ∃ s', s' = <tower> := ⟨_, rfl⟩`), a `writeReg64_comm`-style commutation lemma, `clear_value` on a deep `let`, or restate / `clear` the deep hypothesis; target one location (`simp only [...] at h`) instead of `at *`; for a rewrite loop, drop the extra simp set or apply it in a separate `simp only`. Raising `set_option maxRecDepth` only moves the limit and is not the fix. After the `wp_steps` note, run `wp_step` at that point for the deepest term and remedies. |
| ``Tactic `rfl` failed`` / `unsolved goals` after `decide`, or ``(deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached`` | `decide` and `rfl` only close ground literals; on symbolic `BitVec`s, `List.getD`, or `State` projections (`(s0.setPC _).mem = s0.mem`), `rfl`/`decide` fails or triggers $O(2^N)$ `State` eta-expansion in the kernel. | Use `bv_omega` / `bv_solve` ([`ProofLib/BV/README.md`](../BV/README.md)) for symbolic `BitVec` goals, `byte_region_eq` for byte slices, and `simp only [wp_norm, arm64_norm]` on `State` projections. |

```lean
-- (a) Prove slice bound before `wp_steps` so `wp_sep_access` steps symbolic `base ↦ₛ bs` accesses:
have h_bound : idx + 8 ≤ bs.length := by omega
wp_steps
-- (b) Fold narrow width-cast condition and close symbolic BitVec / State goals without `rfl`/`decide`:
have h_cmp : (BitVec.zeroExtend 64 b).ule 34#64 = false := by simp only [wp_norm, width_norm]; bv_omega
```

### 4. Loop-Invariant & Cutpoint Mismatches (`LoopTactics`)

| Symptom (Exact Error Text) | Cause | Fix |
| :--- | :--- | :--- |
| ``loop tactic: the current PC is an unresolved conditional branch, so the loop header cannot be determined: condition: <cond> | then PC: <then_pc> | else PC: <else_pc>`` | `wp_step` / `wp_steps` stepped the loop header's entry branch (`cbz`, `b.hs`) *before* `wp_loop_measure` / `wp_loop_list` / `wp_nested_loop` was called. | Stop at `head_pc` (before stepping the header branch) and invoke `wp_loop_measure` while `s.pc = head_pc`. |
| `unsolved goals \| case init \| … ⊢ P ⊢ P_inv m s0` (or `⊢ Inv m s0`) | The initial spatial entailment `P ⊢ P_inv m s0` or an initial invariant conjunct was not closed within `loopTryCloseInit`'s 20k-heartbeat cap and stayed as a `case init` goal. | Discharge `case init =>` explicitly with `byte_region_entails`, `sep_entail`, `omega`, or `bv_omega`. |
| ``wp_done: current PC `<head_pc>` does not match target PC `<target_pc>` `` in `case step` / `case cons` / `case enter` | `wp_steps` was run directly on the disjunction `SepWP prog target_pc … ∨ SepWP prog head_pc …` without selecting an arm first. | Start `case step` / `case cons` with `right` (back-edge to `head_pc`) or `left` (early exit to `target_pc`); in `wp_nested_loop`'s `case enter`, use `left` (exit), `right; left` (outer back-edge), or `right; right` (enter `inner_pc`). |
| `wp_done: postcondition value mismatch` on `sp` / `lr` / `x19`..`x28` / `q8`..`q15` in `case base` or `case step` (with ``hint: destructure local callee-saved hypothesis `<hcc>` (e.g. `rcases <hcc> with ⟨...⟩`) before `wp_done` ``) | Without `frame`, `Inv` omitted `st.sp = s0.sp` / `st.readReg64 .lr = s0.readReg64 .lr`, or a local `CalleeSaved*` / `ILCalleeSaved*` hypothesis `<hcc>` was not destructured; or `frame` (`LoopFrame`) was used on a loop that mutates a callee-saved register (`x19`..`x28`). | Destructure `<hcc>` (`rcases <hcc> with ⟨...⟩`) before `wp_done`, or pass `frame` (`wp_loop_measure frame m Inv`) when the loop only mutates caller-saved registers; if the loop mutates `x19`..`x28`, omit `frame` and state `st.sp = s0.sp ∧ st.readReg64 .lr = s0.readReg64 .lr` in `Inv`. |

```lean
-- At `s0.pc = head_pc` (before stepping the header `cbz`):
wp_loop_measure frame rem (fun k st =>
  k < 2 ^ 63 ∧ st.readReg64 .x1 = BitVec.ofNat 64 k ∧
    iterAdd k (st.readReg64 .x0) stride = iterAdd rem acc stride)
-- Note: `loopTryCloseInit` closes `init` automatically when all initial conjuncts follow from context;
-- use `try case init => omega` (or only include `case init =>` when `init` remains open).
try case init => omega
case base => simp only [iterAdd] at *; wp_steps; wp_done
case step =>
  right -- select back-edge arm (`head_pc`, measure `m'`) before stepping
  have hk_nz : BitVec.ofNat 64 (m' + 1) ≠ 0#64 := by bv_omega
  simp only [iterAdd] at *; wp_steps; wp_done
```

### 5. Control / Loop Tactic Automation Options (`ControlTactics` / `LoopTactics`)

| Option (Default `true`) | Automatic Behavior |
| :--- | :--- |
| `proofLib.wpCallAutoStep` | When `wp_call`'s current PC precedes the callee entry, runs a bounded straight-line `wp_steps` (and steps `BL`) to reach the call target before failing. |
| `proofLib.wpCallRegistry` | Enables bare `wp_call` (no argument) to resolve contracts from local `subroutine_ok` hypotheses and `@[callee_spec]`-registered theorems, and suggests matching contracts on PC mismatch. |
| `proofLib.wpDoneAutoDisjAndCalleeSaved` | In `wp_done`, automatically selects the PC-matching `SepWP` arm of an `Or` goal (`P ∨ Q`) and unfolds custom `*CalleeSaved*` / `calleeSavedVRegs` hypotheses. |
| `proofLib.wpBranchAutoDecide` | Before throwing an unresolved conditional branch error in `wp_done`, `wp_call`, or `wp_loop_*`, tries a bounded arithmetic/BitVec decision on the branch condition (and `wp_steps (split := true)` splits and steps both arms automatically). |
| `proofLib.wpCallFrameTransport` | After `wp_call` / `wpp_call`, moves framed state-indexed spatial atoms `f … s_pre` to the post-call state using `@[frame_transport]` lemmas (`∀ …, Rel s s' → f … s' = f … s`) whose side condition `Rel s_pre sf` is closed from the callee's postcondition by `wp_frame_transport_discharge` (`WP/StateTransport.lean`; standalone tactic `wp_frame_transport`). |
| `proofLib.wpCallAutoSpAlign` | In `wp_call`, discharges `s.spAligned = true` from local `s.sp = s0.sp ± k#64` (with `16 ∣ k`) and `s0.spAligned = true` hypotheses (including inside `And` invariants). |
| `proofLib.wpDoneAllowResidualGoals` (`false`) | When `true` (or via `wp_done?`), allows `wp_done` to leave unfocused sibling subgoals open instead of throwing a structured diagnostic error. |



## Performance Regression Tests

The suite in [`ProofLib/Testing/Perf/`](../Testing/Perf.lean) runs
the WP/SepLogic automation under deterministic heartbeat budgets, on complete proofs and on the
intermediate goals seen while a proof is being developed (wrong postcondition value, stopped short
of the return, residual side goals, failing frame splits). Failing cases must end with their
actionable diagnostic, not a heartbeat timeout. It is part of `ProofLib.Testing`, which
CI ("Build Testing & Executables") and `scripts/pre-push-check` build whenever a `ProofLib` module
changes. Build it directly with
`timeout 600 lake build --no-ansi Examples.Testing.ProofLib.Perf`.

**When to add a case**: a tactic took far more heartbeats than expected (a `maxHeartbeats` bump,
a `deterministic timeout`, or a slow failure on a goal it should reject quickly), in a final proof
or on an intermediate goal.

**How to add a case**:

1. Minimize the goal to a ProofLib-level repro, without case-study imports: a small `FnCode`
   fixture plus `wp_init` / `wp_steps`, or a direct `SepWP prog pc s P Q` / `m ⊨ …` goal.
2. Wrap it in `#perf_budget N in` (from `Perf/Budget.lean`). Measure with
   `set_option perfTest.report true`, which logs `perf_budget: … used X heartbeats` (Lean core has
   no `count_heartbeats`). Set `N` to about 2–3× `X`.
3. For a failing case, put `/-- error: … -/ #guard_msgs (error, drop info) in` in front of
   `#perf_budget`, so the test pins the actionable message. Use `(substring := true)` if the
   message contains unstable names.
4. If the case currently blows up and a fix is in flight, keep the suite green: budget it at its
   current cost with a comment, and tighten the budget in the fix.

`#perf_budget` measures the whole command, so it also catches automation that stays inside its
own per-phase caps (`withHeartbeatCap` restarts its counter for each phase) while the declaration
as a whole costs more than its budget.
