# `ProofLib/Abi`: AAPCS64 and Rust ABI Calling-Convention Proof Rules

`ProofLib/Abi/` (untrusted, `Role::Proof`) provides the typed `Arm64.Spec` combinators (`Spec.split`, `Spec.fn*`, `Spec.rust*`, ...) and their introduction/consequence/framing theorems, for use in proofs about specs written with the declarative DSLs (`c_spec`, `rust_spec`). Only the DSL macros themselves are trusted, in [`Arm64/Trusted/Surface/Abi.lean`](../../Arm64/Trusted/Surface/Abi.lean) (re-exported by `import Arm64`; see [`Arm64/Trusted/README.md`](../../Arm64/Trusted/README.md)); the combinators here are untrusted and cannot be used in `Spec.lean` files. Both cover AArch64 procedure calls under the standard C/AAPCS64 ABI and `rustc`'s native `extern "Rust"` ABI.

All specifications in this directory target `Arm64.subroutine_ok prog entry spec` (or partial-correctness `Arm64.safe_subroutine_ok`), which enforces:
1. **AAPCS64 callee-saved register preservation (`x19`–`x29`, `sp`)** and 16-byte entry `sp` alignment (`s0.spAligned = true`).
2. **Return to `lr` (`x30`)** with `sf.status = .Running` (or explicit `onPanic` / `onExit` outcome clauses when enabled).
3. **Universal separation-logic framing (`∀ R, {pre ∗ R} code {post ∗ R}`)** so any verified callee composes via `wp_call` without re-proving frame preservation.

## Quick Lookup: Which File to Read or Import for `X`

| Goal / Task | Import in `Spec.lean` (`Role::Spec`) | Import in `Proof.lean` (`Role::Proof`) | Primary Source File |
| :--- | :--- | :--- | :--- |
| **Import the ABI spec DSLs (`c_spec`, `rust_spec`) and combinators (`Spec.*`)** | `import Arm64` (DSLs only) | `import ProofLib.Abi` (or `import ProofLib`) | `Arm64/Trusted/Surface/Abi.lean`, `ProofLib/Abi.lean` |
| **Write a C / AAPCS64 contract (`c_spec`, `c_type_spec`)** | `import Arm64` | `import ProofLib.Abi.Aapcs` / `import ProofLib.CType` (or `import ProofLib`) | `Arm64/Trusted/Surface/Abi.lean`, `Arm64/Trusted/Surface/CType.lean`, `ProofLib/CType.lean` (`docs/dev/c-type-specs.md`) |
| **Use typed AAPCS64 combinators (`Spec.split`, `Spec.fn1`..`fn3`, `Spec.withStack*`) in proofs** | — (define a local helper in the `Spec.lean` if needed) | `import ProofLib.Abi.Aapcs` | `ProofLib/Abi/Aapcs.lean` |
| **Write a Rust ABI contract (`rust_spec`, `slice8`/`slice64`, `sret` in `X8`, `option_u64`, `result_u64`, `panics_when`)** | `import Arm64` | `import ProofLib.Abi.Rust` (or `import ProofLib.Abi`) | `Arm64/Trusted/Surface/Abi.lean` |
| **Use typed Rust combinators (`Spec.rustPair`, `Spec.rustOption*`, `Spec.rustSret`, `Spec.rustSliceFn1`) in proofs** | — | `import ProofLib.Abi.Rust` | `ProofLib/Abi/Rust.lean` |
| **Prove or weaken an AAPCS64 `Spec.split` contract (`Spec.split.intro`, `subroutine_ok_mono_entails`)** | — | `import ProofLib.Abi.Aapcs` | `ProofLib/Abi/Aapcs.lean` |
| **Prove or weaken a `Spec.rustPair` / `Spec.rustOption*` / `Spec.rustSret` contract (`.intro`, `.mono`, `.apply`)** | — | `import ProofLib.Abi.Rust` | `ProofLib/Abi/Rust.lean` |
| **Model Rust global allocator hooks (`__rust_alloc`, `__rust_dealloc`, `__rust_realloc`, `__rust_alloc_zeroed`, `RustAlloc`, `ByteAlloc`, `AllocHooks`) and `Vec<T>` / `Vec<u8>` / `Box<[T]>` heap representation (`vecHeader`, `vecBuf`, `vecAt`, `vecU8At`, `boxAt`)** | — | `import ProofLib.Abi.Rust.Heap` | `ProofLib/Abi/Rust/Heap/Alloc.lean`, `ProofLib/Abi/Rust/Heap/Vec.lean` |
| **User-facing guide for `c_spec` and `rust_spec`** | `import Arm64` | — | `docs/dev/guides/writing-specs.md` |

> **Trust-Guard Rule (`check-trust-guards`):** `Examples/*/Spec.lean` files (`Role::Spec`) get the DSLs from `import Arm64` — never `ProofLib.Abi`, `ProofLib.Abi.Aapcs`, or `ProofLib.Abi.Rust` (`Role::Proof`). Since `ProofLib` has no `Role::Spec` modules, no trusted spec file may import any `ProofLib.*` module.

## Module Overview

### 1. `Arm64/Trusted/Surface/Abi.lean` (`Role::Spec`, trusted) — `c_spec`
The declarative `c_spec` macro DSL for AAPCS64 functions (expands directly to a plain `Spec α`):
- **Declarative `c_spec` DSL:**
  - Supports named GP/pointer/scalar parameters `(x : u64)`, `(w : u32)`, `(b : u8)`, `(p : ptr)`, `(n : usize)`, ghost parameters `(ghost v : T)`, and struct-backed ghost bundles `[a : ArgsStruct]`.
  - Clauses: `requires <SepProp>`, `preserves <SepProp>`, `guard <Prop>`, `stack <bytes>` / `stack16` / `stack32`, `returns <expr>`, `ensures <SepProp>`, `panics_when <Prop>`, `on_panic <SepProp>`.

### 2. `ProofLib/Abi/Aapcs.lean` (`Role::Proof`, untrusted)
Typed AAPCS64 combinators and their introduction, consequence, and framing rules:
- **Typed Combinators:** `Spec.split`, `Spec.fn1`..`fn3`, `Spec.withPreserves`, `Spec.withStack`, `Spec.withStack16`, `Spec.withStack32`, `Spec.withGuard`, `Spec.withPanicWhen`.
- `subroutine_ok_mono_entails`: Weakens/strengthens `subroutine_ok` via separation-logic entailments (`⊢`) on `pre` and `post`.
- `Spec.split.intro`, `Spec.split.mono`, `Spec.split.apply`: Core rules used by `wp_init` / `wp_start` and `wp_call` on `Spec.split` contracts.
- `Spec.withPreserves.frame` framing rule.

### 3. `Arm64/Trusted/Surface/Abi.lean` (`Role::Spec`, trusted) — `rust_spec`
The `rust_spec` macro DSL (same expander as `c_spec`) for `rustc`'s AArch64 `extern "Rust"` calling convention:
- **Declarative `rust_spec` DSL:** Extends `c_spec` with Rust-specific ABI forms:
  - Fat-pointer slices `(s : slice8 bs)` and `(s : slice64 ws)` passed across two consecutive GP registers `(ptr, len)`.
  - Indirect aggregate returns `(out : sret)` passed in `Reg.x8` without consuming `x0`–`x7`.
  - Multi-register `ScalarPair` returns: `: pair_u64` (`(X0, X1)`), `: option_u64` (`(W0, X1)`), `: option_u8` (`(W0, W1[7:0])`), `: result_u64` (`(W0, X1)`), and `: niche_u64` (`Option<NonZeroU64>` in `X0`).
  - Panic clauses: `panics_when <Prop>` / `on_panic <SepProp>` for functions with genuinely reachable panic paths (keep the default `onPanic = ⌜False⌝` otherwise; see `docs/dev/guides/writing-specs.md` §1.2 and `docs/dev/guides/writing-proofs.md` §2.1).

### 4. `ProofLib/Abi/Rust.lean` (`Role::Proof`, untrusted)
Typed combinators `Spec.rustPair`, `Spec.rustOption64`, `Spec.rustOption8`, `Spec.rustResult64`, `Spec.rustNiche64`, `Spec.rustSret`, `Spec.rustSliceFn1`, and their introduction (`.intro`), monotonicity (`.mono`), and elimination (`.apply`) theorems for `Spec.rustPair`, `Spec.rustOption64`, `Spec.rustOption8`, `Spec.rustNiche64`, and `Spec.rustSret` (`Spec.rustResult64` and `Spec.rustSliceFn1` are reducible abbreviations).

### 5. `ProofLib/Abi/Rust/Heap.lean` (`Role::Proof`, untrusted)
Parametric separation-logic model of the Rust global allocator (`alloc::alloc::Global`) and standard heap containers (`Vec<T>`, `Vec<u8>`, `Box<[T]>`, `Box<[u8]>`):
- **`ProofLib/Abi/Rust/Heap/Alloc.lean`:** `RustAlloc` (`pool` + `(ptr, size, align)`-indexed `live` token), `ByteAlloc` (`align = 1` specialization), `LayoutOk`, `SmallLen`, OOM trace marker `allocFailedEvent` / `allocFailedIn`, ideal/simple `Spec` contracts (`rustAllocIdealSpec`, `rustDeallocIdealSpec`, `rustReallocIdealSpec`, `rustShimIdealSpec`, `rustAllocSimpleSpec`, `rustReallocSimpleSpec`), and hook bundles (`AllocHooksIdeal`, `AllocHooksSimple`).
- **`ProofLib/Abi/Rust/Heap/Vec.lean`:** 24-byte `vecHeader v cap ptr len` (`{cap, ptr, len}` on AArch64 `rustc`), `vecHeaderBytes`, `arrayAt` (`pointsToBytes_eq_arrayAt` for bytes), `vecBuf`, `vecAt`, `vecU8Buf`, `vecU8At`, `boxAt`, `boxU8At`, plus element focus/update (`arrayAt_split_at`, `vecBuf_split_at`, `vecBuf_set`) and deallocation entailments (`vecHeader_entails_memRegion`, `vecU8Buf_entails_dealloc`, `vecU8At_entails_dealloc`).
