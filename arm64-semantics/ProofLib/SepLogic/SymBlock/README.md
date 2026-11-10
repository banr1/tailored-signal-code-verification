# `ProofLib/SepLogic/SymBlock/`: Reflective Whole-Block Symbolic Execution (`sym_block`)

`sym_block` is an **untrusted advisor + reflective kernel checker** for straight-line and
branching ARM64 code. Instead of stepping `SepWP` or `SepWPp` one instruction at a time (rewriting
the `State` spine and re-running the separation-logic solver on every load/store), it

1. **reifies** a `SepWP prog tgt s P post` or `SepWPp prog ret s P Q Qp` goal into a symbolic
   state `SState` (31 GPRs + SP + optional 32 SIMD `V` registers + `TPIDR_EL0` as symbolic
   expressions, flags, PC as `base + offset`, local `Program.fetch` hypotheses pre-indexed in
   $O(1)$, and the spatial atoms of `P`—flattened across arbitrary left- and right-nested `∗`
   trees via `sepConj_assoc`—as an indexed `Cell` list);
2. **advises** natively: runs the same `lower` / `stepOp` / `stepSymInsn` the kernel will run,
   choosing, for each memory access, the cell index(es) by comparing addresses modulo
   associative/commutative 64-bit linear normalization (`matchCanon`) and, for each conditional
   branch, the direction whose side condition is provable (or the one forced by `(hints := "t n …")`);
3. **verifies** with one application of `SepWP_block_spine` or `SepWPp_block_spine`: the kernel
   evaluates `run base tbl hints ss₀ = some (ssF, obl)` by `Eq.refl`, the residual obligations `obl`
   (address equalities, SP alignment, branch conditions) are closed by `Eq.refl` /
   `ProofLib.BV.Lin.proveEq?` / `proveNe?` / `assumption` / `decide` / `bv_lin` /
   `wp_omega_bounded` / `bv_bits` / `bv_solve` / `simp_all`, and the continuation goal is an
   ordinary `writeReg64` / `writeVReg128` / `setTpidrEl0` / `setPC` / `setMem` spine, so
   `wp_sym_steps` / `wp_steps` / `wp_done` continue unchanged.

Nothing here is trusted: the advisor only produces data (hints, cell indices) that the kernel
re-checks; a wrong hint makes the proof fail, never succeed wrongly.

## Layer hierarchy and which file to read for X

| Need | File |
|---|---|
| Symbolic expressions `SExpr`, 128-bit `VExpr`, `Env`, smart constructors (`mkAdd`, `mkOff`, `mkMovk`, `mkDataProc3`, …), cells (`Cell`, `CW`, `ro`, `cellsProp`, `cellsProp_load64` / `store64` / `loadN` / `storeN` / `load128` / `store128`), `SState.toState` | [`Core.lean`](Core.lean) |
| Micro-ops `MOp` (one per ISA evaluation helper), `lower : Instr → Option MOp`, `lower_sound` | [`Lower.lean`](Lower.lean) |
| Hints (`cell`, `cell2`, `cell4`, `br`), obligations `SProp`, flag-condition classifier `flagsCond?` (`SUBS`/`ADDS`/`ANDS`/`BICS` at `.W32`/`.W64`), symbolic step `stepOp` / `stepSymInsn`, and soundness | [`Step.lean`](Step.lean) |
| Instruction tables `Tbl` / `TblOK`, the checker `run` (cursor-based $O(1)$ fetch for code in execution order), `run_sound`, and block rules `SepWP_block` / `SepWPp_block` | [`Block.lean`](Block.lean) |
| Final-state spine (`spine`, `SepWP_block_spine`, `SepWPp_block_spine`) presented to the user | [`Spine.lean`](Spine.lean) |
| Expr → native `Instr` reification used by the advisor (no `evalExpr`) | [`Reify.lean`](Reify.lean) |
| The `sym_block` tactic ($O(1)$ `FetchIndex`, left-nested `flattenSepWithProof`, `matchCanon`, advisor loop, obligation discharge, `symBlock.kcheck` diagnostics) | [`Tactic.lean`](Tactic.lean) |
| `timed "label" tac` (ms / heartbeats), `#proof_stats c` (DAG size, tree size, kernel re-check µs), and `#timed_decl cmd` (both, per theorem of a command; used by `tools/lean-bench --per-decl`) | [`Profile.lean`](Profile.lean) |
| Tests (`#guard_msgs` negatives included) | [`ProofLib/Testing/SymBlock.lean`](../../Testing/SymBlock.lean) |

## Usage

```lean
  wp_init a s0          -- or `wp_entry "fn" a s0` (or `wpp_init` / `wpp_entry` for `SepWPp`)
  sym_block             -- run until ret / unsupported instruction / unprovable branch
  wp_sym_steps          -- (optional) continue with the per-instruction engine
  wp_done
```

`sym_block n` caps the block at `n` instructions; `sym_block (hints := "t n")` forces the
directions of the first conditional branches (from an external advisor such as
`rust-obj2lean symexec --block-hints`).

Obligations are discharged eagerly at each step. An obligation that can't be proved ends the
block before that step, unless the branch direction was forced by a hint, in which case it is an
error.

Each advisor attempt to decide a branch or discharge an obligation runs `assumption | decide |
bv_lin | wp_omega_bounded | bv_bits | bv_solve | simp_all` within a heartbeat budget,
`set_option symBlock.probeBudget <kHB>` (default 300; 0 means no limit beyond `maxHeartbeats`).
Without the budget, failing probes over a large local context can cost seconds, even on a block of
one or two instructions.

`set_option symBlock.report true` makes the tactic log, for each block, its source line, how many
instructions it executed, why the advisor stopped (computed jump, undecided branch, no matching
cell, cannot store to read-only cell, unsupported instruction, unprovable obligation), and a time
split: setup, advisor (with fetch and reification shown separately), and proof assembly.
`set_option symBlock.kcheck true` kernel-checks each proof component separately and prints its
time (use with `set_option Elab.async false`).

## Supported Instructions, Cells & Goals

Supported:
- **Goals & framing**: both pure `SepWP` and panic-aware `SepWPp` goals; arbitrary left- and
  right-nested `∗` trees (`flattenSepWithProof` via `sepConj_assoc`); associative/commutative
  64-bit linear offset normalization (`matchCanon`, e.g. `(sp - 96) + 16` matching `sp - 80`);
  initial `sp` seeding from `s.sp = e` or `s.readReg64 .sp = e` hypotheses (standalone or inside
  `∧` conjuncts, on state variables or write spines without an `.sp` write); named offset `abbrev`
  reduction on `s.pc` and `Program.fetch` hypotheses; target-PC stopping after `≥ 1` step
  (including loop back-edges where `start == target` has a fetchable instruction, while staying a
  0-step no-op when no instruction is fetchable at `target`); and $O(1)$ pre-indexed `Program.fetch`
  lookup (`FetchIndex`) with `entry` / `entry + 0#64` normalization, `fnAddr` local alias
  resolution, and `HasCode` / `wp_assumption` / `rfl` fallbacks;
- **Spatial cells**: `↦₆₄` (`Cell.pt64`), `↦₈` / `↦₁₆` / `↦₃₂` / `↦₁₂₈` (`Cell.ptN`), and
  read-only `↦₆₄ᵣ` / `↦₈ᵣ` / `↦₁₆ᵣ` / `↦₃₂ᵣ` / `↦₁₂₈ᵣ` cells (`ro := true`; loads succeed,
  stores stop the block with a diagnostic);
- **Loads & stores**:
  - 64-bit `ldr`/`str`/`ldp`/`stp` (immediate offsets, unscaled offsets, pre/post-index, and
    `AddrMode.RegOffset` with `UXTW`/`SXTW`/`UXTX`/`SXTX` scaling) against `↦₆₄` cells;
  - 32-bit `ldp w`/`stp w` and sign-extending `ldpsw` against `↦₃₂` cells;
  - narrow `ldrb`/`strb`, `ldrh`/`strh`, `ldr w`/`str w`, and sign-extending `ldrsw`/`ldrsb`/`ldrsh`
    (to `.W32` or `.W64`) against `↦₈` / `↦₁₆` / `↦₃₂` cells;
  - 128-bit SIMD struct copies `ldr q`/`str q`/`ldp q`/`stp q` against either `↦₁₂₈` cells or
    adjacent `↦₆₄` cell pairs/quads;
- **ALU, bitfield, move-wide, conditional select & system registers**:
  - add/sub (`ADD`/`SUB`/`ADDS`/`SUBS`: immediate, shifted register, extended register `addSubExt`);
  - logical (`AND`/`ORR`/`EOR`/`BIC`/`ORN`/`EON`/`ANDS`/`BICS`: immediate, shifted register);
  - bitfield (`UBFM`/`SBFM`/`BFM`, including `ubfx`/`sbfx`/`bfi`/`lsl`/`lsr`/`asr`/`ror`);
  - `movz`/`movn`/`movk`;
  - conditional select (`csel`/`csinc`/`csinv`/`csneg`);
  - 1-source bit/byte ops (`rbit`/`rev16`/`rev32`/`rev`/`clz`/`cls`);
  - 3-source multiply-accumulate / high-multiply (`madd`/`msub`/`smaddl`/`smsubl`/`umaddl`/`umsubl`/`smulh`/`umulh`);
  - `adr` and `adrp` (including relocated `pageOf target - pageOf pc` and `:lo12:` offsets);
  - `nop`, `hint`, `barrier`, `prfm`, `prfmLit`;
  - `mrs`/`msr` on `TPIDR_EL0` (`0x5e82#15`) and `mrs` on `DCZID_EL0` (`0x5807#15`);
- **Branches & condition codes**:
  - `b`, `b.cond` for all 16 `CondCode`s (`EQ`, `NE`, `CS`, `CC`, `MI`, `PL`, `VS`, `VC`, `HI`,
    `LS`, `GE`, `LT`, `GT`, `LE`, `AL`, `NV`) after 32-bit or 64-bit `SUBS`/`CMP`, `ADDS`/`CMN`
    (both unsigned range checks and carry/signed-overflow checks), and `ANDS`/`BICS`/`TST`;
  - `cbz`/`cbnz` (32/64-bit), `tbz`/`tbnz`, and `ret`.

The goal state can be a variable or a `writeReg64` / `writeVReg128` / `setTpidrEl0` / `setPC` /
`setMem` / `setPState` spine over one, as left behind by `wp_sym_steps` or a previous `sym_block`,
so blocks can be resumed.

Not supported (stops the block and hands over to `wp_sym_steps` / `wp_steps` / `wp_call`):
- `BL`/`BLR` calls and hooks;
- floating-point and vector lane arithmetic (`FADD`, `FMUL`, etc.);
- `LDAR`/`STLR` / LSE atomics and `SVC #0` syscalls;
- byte-array (`↦ₛ`) and region (`memRegion`) atoms. These are kept as opaque frame atoms, and
  accessing one stops the block.

## Benchmarks

Synthetic 60-instruction fixture (`perf_60_steps` in `ProofLib/Testing/WpPerf.lean`: pointer
loads/stores, `cbz`, moves, add/eor), same machine, same spec:

| Engine | Symbolic execution (ms / kHB) | Proof DAG objects | Proof tree size | Kernel re-check |
|---|---|---|---|---|
| `wp_steps` | 655 / 4772 | 23 076 | 3.92 M | 1.69 s |
| `wp_sym_steps` | 415 / 2742 | 20 709 | 2.56 M | 0.86 s |
| `sym_block` | **162 / 1063** | **6 555** | **1.15 M** | **0.73 s** |
