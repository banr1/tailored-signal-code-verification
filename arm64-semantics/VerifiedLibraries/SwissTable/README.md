# `VerifiedLibraries.SwissTable` — Generic SwissTable Invariants

Untrusted (`Role::Proof`), binary-free Lean math for SwissTable-style open-addressing hash tables
(8-byte control groups, 7-bit tags, triangular probing) on 64-bit AArch64. The companion
[`Spec.lean`](./Spec.lean) is intentionally empty: nothing here is part of a trusted contract. Case studies prove their machine code against these
definitions and keep their own representation predicates (placement, addresses, slot layout).

| Module | Contents |
|---|---|
| [`Proofs/Control.lean`](./Proofs/Control.lean) | Control tags (`tagEmpty`, `tagDeleted`, `isFullTag`, `ValidTag`, `tagOfHash`), `ValidBucketMask`, `bucketMaskToCapacity`, `triGroupIdx` / `triByteOff`, `CtrlMirrorInv`, `numGroups`, `ctrlGroupAt` |
| [`Proofs/Group.lean`](./Proofs/Group.lean) | 8-byte group words (`ctrlGroupWord`, `getLane8`, `SepLoad64` bridges), `ValidBucketMask` modular arithmetic, `CtrlMirrorInv` lane bridges |
| [`Proofs/Neon.lean`](./Proofs/Neon.lean) | NEON `v.8b` `cmeq` / `umaxv` / `cmlt` / `cmge` and `BitMask` (`rbit` + `clz`, clear-lowest) lemmas |
| [`Proofs/Probe.lean`](./Proofs/Probe.lean) | `probePos bm h step` over a 64-bit hash, `ProbeReachable`, and probe-chain completeness (`exists_empty_probe_group_of_empty_slot`) |
| [`Proofs/Inv.lean`](./Proofs/Inv.lean) | Generic `SwissTableInv hashOf keyOf bm growthLeft items ctrl slots S` over a slot type `α`, its initial state, and lookup soundness/completeness consequences |

## Instantiating

A table whose slots hold values `x : α` probed with hash `hashOf x` and identified by `keyOf x`
instantiates `SwissTableInv hashOf keyOf` with its abstract contents `S : List α`. A case study can
use it directly, or keep its own invariant and prove a bridge to the generic one so it can reuse
the generic lemmas.

```bash
timeout 1200 lake -d VerifiedLibraries build --no-ansi VerifiedLibraries.SwissTable
```
