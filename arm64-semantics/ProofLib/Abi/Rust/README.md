# `ProofLib/Abi/Rust`: AArch64 `extern "Rust"` Calling-Convention Specifications (`rust_spec`)

- **Parent subsystem guide:** [`ProofLib/Abi/README.md`](../README.md)
- **User-facing specification authoring guide:** `docs/dev/guides/writing-specs.md`

## Files

| File | Role | Purpose |
| :--- | :---: | :--- |
| [`Arm64/Trusted/Surface/Abi.lean`](../../../Arm64/Trusted/Surface/Abi.lean) | `Role::Spec` (trusted, in `Arm64`) | Pure, theorem-free `rust_spec` macro DSL (extending `c_spec` with fat slices `slice8`/`slice64`, indirect return pointer `sret` in `Reg.x8`, two-word `ScalarPair` returns `pair_u64`/`option_u64`/`option_u8`/`result_u64`, niche returns `niche_u64`, and `panics_when`/`on_panic`). Re-exported by `import Arm64`, so available in any `Examples/*/Spec.lean`. |
| [`../Rust.lean`](../Rust.lean) | `Role::Proof` (untrusted) | Typed combinators (`Spec.rustPair`, `Spec.rustOption64`, `Spec.rustOption8`, `Spec.rustResult64`, `Spec.rustNiche64`, `Spec.rustSret`, `Spec.rustSliceFn1`; not usable in `Spec.lean` files) and introduction (`.intro`), monotonicity (`.mono`), and elimination (`.apply`) theorems for `Spec.rust*` contracts. |

## `rust_spec` Additional Parameter & Return Binders

`rust_spec` supports all [`c_spec` binders and clauses](../Aapcs/README.md) plus Rust-specific ABI forms:

| Binder / Return Syntax | Rust Type | Registers Used | Expansion in `Spec` |
| :--- | :--- | :--- | :--- |
| `(b : rust_bool)` / `: rust_bool` / `: (ret : rust_bool)` | `bool` (`rustc` `i1 noundef zeroext`, alias of `bool32`) | `.xN` (`+1`) / `W0` | `s0.readReg32 .xN = if b then 1#32 else 0#32` / `sf.readReg32 .x0 = if e then 1#32 else 0#32` (with canonical `{0#32, 1#32}` constraint for named `: (ret : rust_bool)`) |
| `(s : slice8 bs)` | `&[u8]`, `&mut [u8]`, `&str` | `.xN`, `.x(N+1)` (`+2`) | `s0.readReg64 .xN = s ∧ s0.readReg64 .x(N+1) = BitVec.ofNat 64 bs.length` |
| `(s : slice64 ws)` | `&[u64]`, `&mut [u64]` | `.xN`, `.x(N+1)` (`+2`) | `s0.readReg64 .xN = s ∧ s0.readReg64 .x(N+1) = BitVec.ofNat 64 ws.length` |
| `(s : slice8)` / `(s : slice64)` | Raw fat pointer `(ptr, len)` | `.xN`, `.x(N+1)` (`+2`) | Binds `s : BitVec 64 × BitVec 64` to `(.xN, .x(N+1))` |
| `(out : sret)` | Aggregate return (`Vec<T>`, `String`, large `Result`) | `.x8` (`+0` on `.x0`..`.x7`) | `s0.readReg64 .x8 = out` |
| `: pair_u64` / `: result_u64` | `(u64, u64)`, `Box<[u8]>`, `Result<u64, u64>` | `(X0, X1)` | `sf.readReg64 .x0 = a ∧ sf.readReg64 .x1 = b` |
| `: option_u64` | `Option<u64>`, `Option<usize>` | `(W0, X1)` | `sf.readReg32 .x0 = tag32 ∧ sf.readReg64 .x1 = val64` |
| `: option_u8` | `Option<u8>`, `Option<bool>` | `(W0, W1[7:0])` | `sf.readReg32 .x0 = tag32 ∧ (sf.readReg32 .x1).truncate 8 = val8` |
| `: niche_u64` | `Option<NonZeroU64>`, `Option<&T>` | `X0` | `ProofLib.decodeNiche64 (sf.readReg64 .x0) = optVal` |
| `: RustAbi.<enc>` ([`RustAbi.lean`](../../../Arm64/Trusted/Spec/RustAbi.lean)) | `Option<u64/u32/u16/u8>` (`optionU64`…`optionU8`), `Option<&T>`/`Box`/`NonNull`/`NonZeroU64` (`optionNonNull64`), `Option<&[T]>` (`optionSlice`), `Result<u64,u64>`/`<u64,()>`/`<u32,u32>`/`<(),u32>`/`<u8,E>` (`resultU64`, `resultU64Unit`, `resultU32`, `resultUnitU32`, `resultU8`) | fixed by the encoder | `RustAbi.<enc>.holds sf e` for `returns e` with `e : Option α` / `Except ε α`; payload unconstrained on `None`/unit `Err`. Prefer over `option_u64`/`option_u8` (which pin the payload register on `None`). `Option<bool>` is a single `i8` (`None = 2`) under `rustc 1.98.1`, not `option_u8`'s pair |
| `panics_when P` / `on_panic S` | `panic!(...)` / bounds check / OOM | `sf.status = .Panicked` | Sets `onPanic := fun ... => ⌜P⌝` or `S` (default is `⌜False⌝`) |
