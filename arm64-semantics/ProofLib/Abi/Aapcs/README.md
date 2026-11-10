# `ProofLib/Abi/Aapcs`: AAPCS64 Calling-Convention Specifications (`c_spec`)

- **Parent subsystem guide:** [`ProofLib/Abi/README.md`](../README.md)
- **User-facing specification authoring guide:** `docs/dev/guides/writing-specs.md`

## Files

| File | Role | Purpose |
| :--- | :---: | :--- |
| [`Arm64/Trusted/Surface/Abi.lean`](../../../Arm64/Trusted/Surface/Abi.lean) | `Role::Spec` (trusted, in `Arm64`) | Pure, theorem-free `c_spec` macro DSL. Re-exported by `import Arm64`, so available in any `Examples/*/Spec.lean`. |
| [`../Aapcs.lean`](../Aapcs.lean) | `Role::Proof` (untrusted) | Typed combinators (`Spec.split`, `Spec.fn1`..`fn3`, `Spec.withPreserves`, `Spec.withStack*`, `Spec.withGuard`, `Spec.withPanicWhen`), and introduction, monotonicity, and framing theorems (`subroutine_ok_mono_entails`, `Spec.split.intro`, `Spec.withPreserves.frame`) for AAPCS64 contracts. |

## `c_spec` Parameter Binder Reference

| Binder Syntax | C Type | Lean Type in `Spec α` | Advances `.x0`..`.x7`? | Register Precondition Emitted in `pre` |
| :--- | :--- | :--- | :---: | :--- |
| `(x : u64)` / `(x : i64)` / `(n : usize)` / `(n : isize)` / `(p : ptr)` | `uint64_t`, `size_t`, `T *` | `BitVec 64` | Yes (`+1`) | `s0.readReg64 .xN = x` |
| `(w : u32)` / `(w : i32)` | `uint32_t`, `int32_t`, `int` | `BitVec 32` | Yes (`+1`) | `s0.readReg32 .xN = w` |
| `(h : u16)` / `(h : i16)` | `uint16_t`, `int16_t` | `BitVec 16` | Yes (`+1`) | `(s0.readReg32 .xN).truncate 16 = h` |
| `(b : u8)` / `(b : i8)` | `uint8_t`, `int8_t`, `char` | `BitVec 8` | Yes (`+1`) | `(s0.readReg32 .xN).truncate 8 = b` |
| `(flag : bool)` | `_Bool`, `bool` (AAPCS64 8-bit `W[7:0]`) | `Bool` | Yes (`+1`) | `(s0.readReg32 .xN).truncate 8 = if flag then 1#8 else 0#8` |
| `(flag : rust_bool)` / `(flag : bool32)` | `bool` (32-bit zero-extended `W`, e.g. `rustc` `i1 zeroext`) | `Bool` | Yes (`+1`) | `s0.readReg32 .xN = if flag then 1#32 else 0#32` |
| `(flag : bool64)` | `bool` (64-bit zero-extended `X`) | `Bool` | Yes (`+1`) | `s0.readReg64 .xN = if flag then 1 else 0` |
| `(sp : sp)` | *(Entry stack pointer)* | `BitVec 64` | **No** | `s0.sp = sp` |
| `(ghost v : T)` | *(Logical ghost variable)* | `T` (or ABI type) | **No** | *(None — bound in `α` only)* |
| `[a : ArgsStruct]` + `(a.field : ty)` | *(Struct-backed ghost bundle)* | `ArgsStruct` | Per `(a.f : ty)` | Binds `s0.readReg* .xN = a.field` |
| `{α : Type}` / `(ctx x : T)` | *(Outer Lean parameter)* | Outside `Spec α` | **No** | *(Parameterizes the Lean `def`)* |
| `load_addr b` clause / `(load_addr b)` | *(Image load / base address)* | `BitVec 64`, last `def` parameter (`BaseSpec α`) | **No** | *(Instantiated at `prog.base` by `Program.subroutineOk` etc.; see `docs/guides/writing-specs.md` §1.1)* |
| `(x : ty @ .xK)` | *(Explicit register `.xK`)* | Resolved `ty` | **No** | Register equality on `.xK` |
| `(_ : ty := expr)` | *(Computed/constant arg)* | *(Omitted from `α`)* | Yes (`+1`) | `s0.readReg* .xN = expr` |
| `(_ : ty)` | *(Ignored parameter)* | *(Omitted from `α`)* | Yes (`+1`) | *(None — skips `.xN`)* |

## `c_spec` Return & Body Clause Reference

| Header Return / Body Clause | Expansion in `Spec` |
| :--- | :--- |
| `: u64` / `: usize` / `: ptr` + `returns e` | `sf.readReg64 .x0 = e` |
| `: u32` / `: i32` + `returns e` | `sf.readReg32 .x0 = e` |
| `: u16` / `: u8` + `returns e` | `(sf.readReg32 .x0).truncate 16/8 = e` |
| `: bool` + `returns e` | `(sf.readReg32 .x0).truncate 8 = if e then 1#8 else 0#8` (AAPCS64 C `_Bool` low 8 bits `W0[7:0] ∈ {0, 1}`) |
| `: rust_bool` / `: bool32` / `: bool64` + `returns e` | `sf.readReg32/64 .x0 = if e then 1 else 0` (32/64-bit zero-extended `0`/`1`, e.g. `rustc` `i1 zeroext`) |
| `: (ret : bool)` / `: (ret : rust_bool)` / `: (ret : bool32)` / `: (ret : bool64)` | Binds `ret : Bool` to `(sf.readReg32 .x0).truncate 8 != 0#8`, `sf.readReg32 .x0 != 0#32`, or `sf.readReg64 .x0 != 0#64` **and** constrains the return slice in `post` to the canonical `0` or `1` value (`raw = if ret then 1 else 0`), so named and unnamed returns agree |
| `: (ret : <retType>)` | Binds `ret` to the return register inside `ensures` / `ensures_pure` |
| `guard P` / `requires_pure P` / `requires_cond P` | Adds pure proposition `P` to `pre` (`guard` before, `requires_cond` after register equalities) |
| `requires S` / `ensures S` / `preserves S` | Adds spatial assertion `S` to `pre`, `post`, or both (`preserves`) |
| `ensures_pure P` | Prepends `⌜P⌝` to `post` |
| `stack N` / `stack16` / `stack32` | Appends `stackFrame s0 N` to `pre` and `stackFrame sf N` to `post` |
| `let x := val` | Scopes `let x := val` over `pre` and/or `post` |
| `panics_when P` / `on_panic S` / `on_exit S` | Sets `onPanic` or `onExit` outcome clauses |
