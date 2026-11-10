# LibsignalBinary: specifications and proofs about the libsignal ARM64 binary, shared

This folder holds the specifications and proofs about libsignal v0.105.4's compiled AArch64 session
code that **both** the symbolic proof ([`Symbolic/`](../Symbolic/)) and the
computational proof ([`Computational/docs/README.md`](../Computational/docs/README.md)) use. Each
module was moved here once, unchanged apart from its imports, and exists only here: nothing is
copied. Namespaces did not change, so every definition and theorem keeps its fully qualified name
(e.g. `CryptoGames.LibsignalSession.SignalMessage.tryFrom`).

## What is where

"Moved from" gives the top-level directories before the `Computational/` move; what stayed
in them is now under `Computational/Specifications/`, `Computational/Proofs/` and `Computational/Tests/`.

| Directory | Contents | Moved from |
|---|---|---|
| [`Specifications/`](Specifications/) | the `Libsignal*.lean` hook models, layouts and session programs (`LibsignalTripleRatchet.lean`, `LibsignalSession.lean`, `LibsignalHmac.lean`, ...) and [`LibsignalSignalMessage.lean`](Specifications/LibsignalSignalMessage.lean) | `Specifications/Libsignal*.lean` |
| [`Specifications/CryptoGames/`](Specifications/CryptoGames/) | the definitions both sides use: `Primitives.lean`, `PRNG/Defs.lean`, `FSAEAD/{Defs,Construction,Security}.lean`, the `AEAD/*Defs.lean` files and `AEAD/LibsignalAead.lean`, and the session model `Ratchet/LibsignalSession.lean` with `Ratchet/{RootKdfDefs,ChainDefs,CreateChainDefs}.lean` | `CryptoGames/` |
| [`Proofs/`](Proofs/) | the per-function contracts of the binary and their proofs: `TripleRatchet/` (the five session entry points, `Statements.lean`), `ConsumeMessageKey/`, `AesCbc/`, `Hmac/`, `Common/`, `CodeLayout.lean`, `VarintBridge.lean`, `ProtoCodecRoundTrip.lean` | `Proofs/libsignal/` |
| [`Proofs/CryptoGames/`](Proofs/CryptoGames/) | `Ratchet/RootStepProof.lean` | `CryptoGames/Ratchet/` |
| [`Specifications/RustHeap/`](Specifications/RustHeap/), [`Proofs/RoDataReloc.lean`](Proofs/RoDataReloc.lean) | the Rust heap vocabulary (`Alloc.lean`: the global allocator contracts; `Vec.lean`: the `Vec<T>` layout) and the relocated `.rodata` pointer slots | `CryptoProofLib/` |
| [`Specifications/LibsignalSpqrV1/`](Specifications/LibsignalSpqrV1/), [`SpecAudit/SpqrV1.lean`](SpecAudit/SpqrV1.lean), [`Proofs/SpqrV1/Vectors/`](Proofs/SpqrV1/Vectors/) | the SPQR V1 model and binary statements, their spec audit, and differential vectors from real `spqr` | new, not moved |
| [`Heap/`](Heap/) | the untrusted state-indexed Rust global-allocator interface (`RustCliAlloc`) and its stock `musl` `mallocng` instance ([`Heap/README.md`](Heap/README.md)) | new, not moved |

Module names follow the paths: `Specifications.LibsignalX` → `LibsignalBinary.Specifications.LibsignalX`,
`CryptoGames.X` → `LibsignalBinary.Specifications.CryptoGames.X` (`CryptoGames.Ratchet.RootStepProof` →
`LibsignalBinary.Proofs.CryptoGames.Ratchet.RootStepProof`), `Proofs.libsignal.X` → `LibsignalBinary.Proofs.X`,
`CryptoProofLib.RustHeap.X` → `LibsignalBinary.Specifications.RustHeap.X` and `CryptoProofLib.RoDataReloc` →
`LibsignalBinary.Proofs.RoDataReloc` (their namespaces, `CryptoVerification.RustHeap` and
`CryptoProofLib.RoDataReloc`, did not change).
Comments in the moved files still cite the old code paths (only references to the moved symbolic
docs were updated); use this table to map them.

## `LibsignalSignalMessage`: the wire format, without CryptoGames

[`Specifications/LibsignalSignalMessage.lean`](Specifications/LibsignalSignalMessage.lean)
(module `LibsignalBinary.Specifications.LibsignalSignalMessage`) holds libsignal's `SignalMessage`
wire format (`SignalMessage`, `SignalMessage.tryFrom`, its errors, `PublicKey.deserialize`) and
prost's protobuf codec `protoSignalCodec`, with the minimal definitions they need. Both the
computational statement and the symbolic refinement statement parse received bytes with
`SignalMessage.tryFrom protoSignalCodec`, so these definitions are trusted by both.

This file imports only Mathlib's `List.Vector`, so the symbolic statement depends on no
CryptoGames module and not on VCVio. The session model
[`Specifications/CryptoGames/Ratchet/LibsignalSession.lean`](Specifications/CryptoGames/Ratchet/LibsignalSession.lean)
and [`Specifications/LibsignalProtoCodec.lean`](Specifications/LibsignalProtoCodec.lean) (both in
this folder) import it, so their importers see the same declarations. `LibsignalProtoCodec.lean`
holds only kernel-checked `decide` guards on the codec.

## Trust

- `Specifications/`: each file's module docstring starts with a trust banner (**Trusted: definitions
  used by the statement**, **Trusted in part**, or **Checked by Lean**) that says which of its
  definitions the computational statement uses; see
  `Computational/docs/TRUSTED_BASE.md` §3. The symbolic
  statement trusts only `LibsignalSignalMessage.lean` from this folder.
- `Proofs/`: nothing here is trusted. Neither statement uses a module under `Proofs/`; Lean checks
  every proof.
- `LibsignalBinary/Heap/`: untrusted proof library; denied by module (group 5) to the symbolic statement's machine-free check.

## Lake libraries

- `LibsignalBinary` (default target): root is the umbrella `LibsignalBinary.lean`, which imports
  the maximal modules; everything else is reached transitively. Plain `lake build` builds it.
- `LibsignalSpqrV1Spec` (default target): roots `Specifications/LibsignalSpqrV1/Guards.lean`,
  `SpecAudit/SpqrV1.lean` and the `Proofs/SpqrV1/Vectors/*Check.lean` modules, so CI builds the
  whole SPQR V1 model, its spec audit and its differential checks; the umbrella does not import
  them.
- `LibsignalBinaryCryptoGames` (no roots, not a default target): only gives the modules under
  `LibsignalBinary/{Specifications,Proofs}/CryptoGames/` and `LibsignalSignalMessage` the same strict
  options as the `ComputationalCryptoGames` library (`autoImplicit false`, `relaxedAutoImplicit false`,
  `warningAsError true`).

## Import rules

Checked in CI by [`Symbolic/scripts/check_symbolic_deps.py`](../Symbolic/scripts/check_symbolic_deps.py)
(Python and `git` only, no build):

1. A `LibsignalBinary.*` module imports only `LibsignalBinary.*`, `GeneratedLean.*` and external
   packages. In particular it never imports `Symbolic.*` or computational-only modules.
2. A `Symbolic.*` module imports only `Symbolic.*`, `LibsignalBinary.*`, `GeneratedLean.*` and
   external packages.
3. Nothing outside `Symbolic/` imports `Symbolic.*`.
4. Computational code imports `LibsignalBinary.*` directly.

A change here affects both proofs: build both (plain `lake build` does).
