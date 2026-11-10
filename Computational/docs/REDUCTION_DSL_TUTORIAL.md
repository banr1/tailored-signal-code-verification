# ReductionDsl tutorial

ReductionDsl is the small, deeply embedded language in which every reduction named by a headline
statement is written. This page explains what the language can express, how its costs are
counted, how a program is connected to a cryptographic argument, and how to write and prove
things about your own programs. The examples are checked by Lean: they live in
[`Computational/Tests/Docs/Tutorial.lean`](../Tests/Docs/Tutorial.lean), which the default
`lake build` compiles.

| File | Role | Trusted? |
|---|---|---|
| [`Computational/Specifications/Reductions/ReductionDsl/Core.lean`](../Specifications/Reductions/ReductionDsl/Core.lean) | syntax, semantics (`eval`), cost, query count, `CostedReduction`/`TwoStageCostedReduction` | yes |
| [`Computational/Specifications/Reductions/ReductionDsl/Samplers.lean`](../Specifications/Reductions/ReductionDsl/Samplers.lean) | shared uniform samplers | yes |
| `…/CostedTables.lean` (one per primitive or protocol) | op tables, oracle interfaces, game codecs | yes |
| [`Computational/Proofs/ReductionDsl/Soundness.lean`](../Proofs/ReductionDsl/Soundness.lean) | `queries` really bounds the oracle calls | no |
| [`Computational/Proofs/ReductionDsl/Size.lean`](../Proofs/ReductionDsl/Size.lean) | every value's size is bounded by the cost | no |
| [`Computational/Proofs/ReductionDsl/Bridge.lean`](../Proofs/ReductionDsl/Bridge.lean) | relating `CostedReduction.eval` to a hand-written `simulateQ` reduction | no |

## 1. Why a deep embedding

A security statement of the form "for every adversary `A`, `Adv(A) ≤ Adv(R(A)) + ε`" is
meaningful only if `R` is efficient. In a shallow embedding (`R` an arbitrary Lean function into
`OracleComp`), pure Lean computation is free and invisible. A reduction could brute-force a
discrete log, call `Classical.choose`, or inspect the bytes of a key, and Lean would not notice.
One way out is to name concrete trusted reductions in the statement and ask the reader to check
by hand that each "runs the adversary once with small overhead".

ReductionDsl replaces that reading obligation with a syntactic one:

* a reduction is a **value of an inductive type** (`CostedReduction` / `TwoStageCostedReduction`), not a Lean function;
* the language is **first-order**: no Lean functions are embedded in a program, abstract values
  (keys, ciphertexts, byte strings) can be touched **only** through a declared op table, and every
  loop has a **static bound** written in the program;
* `Comp.cost` and `Comp.queries` are **structural recursions on the syntax**, so the cost of a
  reduction is a closed-form number you can compute with `simp`;
* `CostedReduction.eval` runs the adversary **exactly once**, with no rewinding.

Only `Core.lean`, `Samplers.lean` and the shared tables are trusted (about 6.7k lines in total).
The reductions themselves (tens of thousands of lines) and their proofs live under `Computational/Proofs/`.

## 2. The language in one page

### Sorts and types

A signature `S : Sig` names the **abstract sorts** (`S.Base`), their carriers (`S.den`) and
their sizes in blocks (`S.sz`). Types are abstract sorts plus inspectable data:

```lean
inductive Ty (S : Sig) where
  | base (b : S.Base)           -- abstract: only ops may touch it
  | unit | bool | nat
  | opt (t : Ty S) | prod (t u : Ty S) | sum (t u : Ty S)
  | list (t : Ty S)             -- finite list
  | tbl (t : Ty S)              -- total map ℕ → t (counters, party indices)
```

For PQXDH (`Computational/Specifications/Reductions/ReductionDsl/AtomicOps.lean`) the sorts include `pbytes w` / `bytes w`
(byte strings of nominal width `w`, measured in blocks of `w` bytes) and `pu32` / `u32`.

### Expressions (`Expr O Γ t`): pure

Variables are de Bruijn indices into the context `Γ`; `Expr.v0`, `Expr.v1`, … are shorthands
for the innermost binders. The constructors are:

* data: `unit`, `bool b`, `nat n`, `pair`/`fst`/`snd`, `inl`/`inr`/`caseSum`,
  `none`/`some`/`caseOpt`, `letE`, `ite`;
* arithmetic: `add`, `sub`, `lt`, `eqN`, `not`, `and`, and **constant-operand** `mulK k`,
  `divK k`, `modK k` (there is no `x * y`: products of two variables could square a size);
* lists: `nil`, `cons`, `len`, `take`, `appendL K`, and the bounded loops `findB K`, `anyB K`,
  `mapB K`, `foldrB K`, which look only at the first `K` entries;
* tables: `tconst`, `tget`, `tset`;
* **`op o e`**: the only way to compute on an abstract sort, using op `o` of the table `O`.

### Programs (`Comp O I Γ t`): effects

* `ret e`, `bind c k`, `ite`, `caseOpt`, `caseSum`;
* `sample s e`: a coin-only sampler from `I.smp` (e.g. a uniform bit, a uniform index `< N`, a
  uniform key);
* `query g e`: one query with tag `g` to the target oracle, through the interface `I`;
* bounded loops: `iter n`, `findM K`, `anyM K`, `mapM K`, `consumeFirstM K`, `foldM K`.

### Tables, interfaces, codecs (all trusted, all shared)

* `Ops S`: the op table, with `dom`, `cod`, `eval` and a declared `cost` per op.
* `Iface S T`: the oracle interface into the target spec `T`. It has query tags with `dom`/`cod`,
  an encoding into `T`, `qCost`, coin forwarding `fwdU` with cost `uCost`, and the samplers
  `smp`.
* `GameCodec S G`: how a query of the source game `G` is presented to the handler (`qenc`) and
  how the handler's answer is read back (`rdec`), with `codecCost`.

**One table per primitive.** Each primitive or assumption has exactly one `Ops`, one `Iface`
and one `GameCodec`, in a shared trusted `CostedTables.lean`. A reduction file only writes a
program. Several primitives are combined with `Ops.sum` and `Iface.withSamp`.

**The headline fixes the tables in its type.** A headline does not quantify over tables: its
reduction bundle names them. For example, `KeyIndCostedReductionFamily` in
`Computational/Specifications/Pqxdh/Security/Headline.lean` has fields such as
`sig : QueryBudget → CostedReduction pqxdhOps pqSigAndDdhIface (keyIndSpec S) (keyIndCodec S) …`. A program written
over any other table, such as one with a cheaper or more powerful op, has a different type and
cannot be the witness, so the proof of the headline would not typecheck. Its cost is
`CostedReduction.totalCost`, computed from the declared costs in that trusted table. So the soundness of the
cost accounting rests on Lean's type checker plus the reader's check of the trusted tables (their
`eval`, `cost` and size honesty), not on review of reduction files.

### Reductions

```lean
structure CostedReduction (O : Ops S) (I : Iface S T) (G : OracleSpec κ) (C : GameCodec S G)
    (rIn aIn aOut out : Ty S) where
  σ : Ty S                                    -- the simulator's state
  init   : Comp O I [rIn] (.prod aIn σ)       -- A's input and the first state
  handle : Comp O I [σ, C.Q] (.prod C.R σ)    -- answer one G-query of A
  finish : Comp O I [σ, aOut] out             -- the reduction's output
```

`CostedReduction.eval R A x` runs `init`, then runs `A` **once**, answering each `G`-query with `handle`
(and forwarding `A`'s coins), then runs `finish`. `TwoStageCostedReduction` is the two-stage version for targets
with a challenge phase. Its handler may pause at one query, hand a value to the target's first
stage, and resume in the second stage with the target's answer.

## 3. Costs

Costs are structural, and every constructor costs at least 1:

| Construct | Cost |
|---|---|
| `var`, `unit`, `bool`, `nil`, `none` | `1` |
| `nat n` | `bits n = log₂ n + 1` |
| `mulK k a`, `divK k a`, `modK k a` | `cost a + bits k` |
| unary/binary ops (`not`, `fst`, `snd`, `inl`, `inr`, `some`, `len`, `add`, `sub`, `lt`, `eqN`, `and`, `pair`, `cons`, `take`, `letE`), tables (`tconst`, `tget`, `tset`) | sum of the arguments `+ 1` |
| `appendL K a b` | `cost a + cost b + K + 1` |
| `ite c a b`, `caseOpt`, `caseSum` (`Expr` and `Comp`) | test `+ max` of the arms `+ 1` (only one arm runs) |
| `op o a` | `cost a + O.cost o` |
| `findB K l p`, `anyB K l p`, `mapB K l p`, `findM K l p`, `anyM K l p`, `mapM K l p` | `cost l + K · (cost p + 1) + 1` |
| `foldrB K l z f`, `foldM K l z f` | `cost l + cost z + K · (cost f + 1) + 1` |
| `consumeFirstM K l p mk` | `cost l + K · (cost p + cost mk + 1) + 1` |
| `iter n e body` | `cost e + n · (cost body + 1) + 1` |
| `sample s e` / `query g e` | `cost e + I.smp.sCost s` / `cost e + I.qCost g` |
| `ret e` / `bind c k` | `cost e + 1` / `cost c + cost k + 1` |

For a whole reduction, with `A` making at most `q` oracle queries:

```
CostedReduction.totalCost R q = cost init + q · max uCost (cost handle + codecCost) + cost finish
CostedReduction.totalQueries R w ws q = queries init + q · queries handle + queries finish
```

`Comp.queries w ws` is a weighted count. Each query tag `g` counts `w g` and each sampler
`ws s`; branches take the max; loops multiply by their bound. Choosing `w` picks which oracle you
count: for example `w := 1` on the challenger's tags and `0` on primitive tags.

**What the numbers mean.** Each table entry satisfies the rule "the real work of op `o` is at
most `O.cost o × (largest block count of its inputs)`". So the real running time of a reduction
is at most `totalCost × max blocks`. The size theorem `Comp.fits_eval` (`Computational/Proofs/ReductionDsl/Size.lean`)
bounds `max blocks` by the input sizes plus `totalCost` plus the headline's answer-size bound
`ℓ`. Together these give a polynomial running-time bound without trusting any invariant of the
reduction.

## 4. Example 1: a forwarding reduction

The simplest reduction answers each PRF query of `A` by one query to the target PRF oracle. It
uses the shared PRF tables of
[`PRF/CostedTables.lean`](../Proofs/SpecLemmas/Reductions/Primitives/PRF/CostedTables.lean):

```lean
abbrev S := prfSig Inp Tg                                   -- sorts: inp, tag
abbrev O := prfConstantInputOps (S := S Inp Tg) (.base .inp) (Empty.elim : Empty → Inp)  -- no constants
abbrev I := prfIface (S := S Inp Tg) (.base .inp) (.base .tag)  -- one tag `()`, cost 1
abbrev C := prfCodec (S := S Inp Tg) (.base .inp) (.base .tag)  -- Q = inp, R = tag

def fwdRed : CostedReduction (O Inp Tg) (I Inp Tg) (MACScheme.prfSpec Inp Tg) (C Inp Tg)
    .unit .unit .bool .bool where
  σ := .unit
  init := .ret (.pair .unit .unit)                    -- A gets (), state ()
  handle := .bind (.query () .v1) (.ret (.pair .v0 .v1))
  finish := .ret .v1                                  -- output A's bit
```

Read `handle` with its context `[σ, Q] = [unit, inp]`:
* `.v1` is the query `x : inp`, and `.query () .v1` asks the target PRF at `x`;
* `bind` pushes the answer, so the context becomes `[tag, unit, inp]`;
* `.pair .v0 .v1` returns `(answer, state)`.

In `finish` the context is `[σ, aOut] = [unit, bool]`, so `.v1` is `A`'s output.

**Cost.** `simp` computes it, and `omega` closes the arithmetic:

```lean
example (q : ℕ) : (fwdRed Inp Tg).totalCost q = q * 8 + 6 := by
  simp [CostedReduction.totalCost, fwdRed, I, C, prfCodec, prfIface, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1]
  omega
```

The `8` per query is the handler (`bind` 1, `query` 1 for the argument + 1 for `qCost`, `ret` 1,
`pair` 3) plus the codec's 1. The `6` is `init` (4) plus `finish` (2).

**Queries.** The handler makes one query, so the reduction makes `q`:

```lean
example (q : ℕ) :
    (fwdRed Inp Tg).totalQueries (fun _ => 1) (fun s => nomatch s) q = q := by
  simp [CostedReduction.totalQueries, fwdRed, Comp.queries]
```

**From syntax to semantics.** The generic theorem `CostedReduction.queryBound_eval`
(`Computational/Proofs/ReductionDsl/Soundness.lean`) turns the syntactic count into the VCVio predicate
`IsQueryBoundP` on the actual run:

```lean
example (A : Unit → OracleComp (unifSpec + MACScheme.prfSpec Inp Tg) Bool) (q : ℕ)
    (hA : ∀ a, (A a).IsQueryBoundP (isGameQuery (G := MACScheme.prfSpec Inp Tg)) q) :
    ((fwdRed Inp Tg).eval A ()).IsQueryBoundP
      (isGameQuery (G := MACScheme.prfSpec Inp Tg)) q := by
  have := CostedReduction.queryBound_eval (fwdRed Inp Tg)
    (isGameQuery (G := MACScheme.prfSpec Inp Tg)) (fun _ => 1) (fun s => nomatch s)
    (fun _ _ _ => le_rfl) (fun n => by simp [prfIface, I, isGameQuery]) A q hA ()
  refine this.mono (le_of_eq ?_)
  simp [CostedReduction.totalQueries, fwdRed, Comp.queries]
```

**Semantics of one step.** `Comp.eval` is definitional, so small facts hold by `rfl`:

```lean
example (x : Inp) :
    (fwdRed Inp Tg).handle.eval (.cons () (.cons x .nil)) =
      (fun t => (t, ())) <$>
        (query (spec := unifSpec + MACScheme.prfSpec Inp Tg) (.inr x)) := rfl
```

## 5. Example 2: state, arithmetic and branching

This reduction counts `A`'s queries in its state and keeps `A`'s bit only if there were fewer
than 10:

```lean
def countRed : CostedReduction (O Inp Tg) (I Inp Tg) (MACScheme.prfSpec Inp Tg) (C Inp Tg)
    .unit .unit .bool .bool where
  σ := .nat
  init := .ret (.pair .unit (.nat 0))
  handle := .bind (.query () .v1) (.ret (.pair .v0 (.add .v1 (.nat 1))))
  finish := .ret (.ite (.lt .v0 (.nat 10)) .v1 (.bool false))

example (q : ℕ) : (countRed Inp Tg).totalCost q = q * 10 + 13 := by
  have h10 : Nat.log 2 10 = 3 := by decide
  simp [CostedReduction.totalCost, countRed, I, C, h10, prfCodec, prfIface, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, bits]
  omega
```

Note `bits 10 = 4`: a literal is charged by its bit length, so a reduction cannot hide a huge
constant.

## 6. A real example

[`Computational/Tests/Docs/RootKdf.lean`](../Tests/Docs/RootKdf.lean) is the shortest
reduction in a headline (about 90 lines): the PRF → PRG step for the Double Ratchet root KDF. It
shows the four pieces every reduction file has:

1. **the program** `rootStepRedProg`, over `Ops.sum` of the shared PRF and PRG tables: one PRF
   query, one `expandPRG` op, a pair handed to the adversary;
2. **size honesty** of the combined table (`rootStepOps_sizeHonest`, via `OpsSizeHonest.sum`);
3. **the bridge theorem** `rootStepRedProg_eval`: evaluating the program equals the hand-written
   shallow reduction `rootStepRed`. Every existing game-hop proof about `rootStepRed` then
   applies to the program unchanged;
4. **cost** (`q * 5 + k + 10`) and **query** bounds (one PRF query).

The PQXDH headline reductions follow the same pattern at a larger scale: the witness
`pqxdhKeyInd1KeyCostedSims` (`Computational/Proofs/SignalPqxdh/Delta/KeyInd1KeyStatements.lean`) packages
`sigKeyInd1KeyDslProg`, `shcrKeyInd1KeyDslProg`, and `fgKeyInd1KeyGapDhDslProg` (see
`Computational/Proofs/SignalPqxdh/Security/ReductionDsl/KeyInd1KeySigWire.lean`,
`KeyInd1KeyShcr.lean`, and `KeyInd1KeyGapDhWire.lean`, built on the shared helpers in
`KeyIndSigKem.lean` and `KeyIndSigKemBounds.lean`).

## 7. What you cannot write (and why that is the point)

* **Inspect an abstract value.** No `Expr` constructor eliminates `.base b` except `op`. A
  reduction holding a key `k : .base (.bytes 32)` can pass it to an op of the table, store it,
  compare it with an op the table provides, or send it in a query. It cannot read its bytes.
* **Embed a Lean function.** There is no constructor taking a `Lean` function, so
  `Classical.choose` or a brute-force search cannot appear in a program.
* **Loop without a bound.** Every list loop and `iter` carries a static `K`/`n` and is charged
  `K ·` its body. If the real list can be longer than `K`, the program sees only the first `K`
  entries. The bridge proof must then show, from the game's query bound, that this never cuts
  anything off.
* **Multiply two variables.** Only `mulK k` (constant operand). This keeps sizes linear in the
  cost.
* **Use its own table.** The headline's bundle type fixes the shared tables (§2, "Tables,
  interfaces, codecs"), so a program over a locally defined `Ops`, `Iface`, `GameCodec` or
  `Samplers` does not typecheck as the witness. If an op is missing, add it to the shared
  trusted table for that primitive, with a docstring stating its real cost. That is a trusted
  change and is reviewed as one.

## 8. Writing a new reduction: checklist

1. Find the shared table for each primitive you need (`git grep -l "CostedTables" --
   '*.lean'`). Combine them with `Ops.sum` / `Iface.withSamp`. If an op is missing, propose it
   for the shared table (trusted change) rather than defining it locally.
2. Write the program as a `CostedReduction` (or `TwoStageCostedReduction`). Keep the state type `σ` small, and write helpers
   as `def`s returning `Comp`/`Expr` with a generic context (see `KeyIndSigKem.lean`).
3. Prove the **bridge**: `R.eval A x = shallowRed A x`, or equal advantage. The lemmas in
   `Computational/Proofs/ReductionDsl/Bridge.lean` (`CostedReduction.eval_eq_simulateQ`, `…_of_abs`) reduce this to a
   per-query agreement of handlers. Bounded loops need a list-length invariant.
4. Prove **cost** and **queries** with `simp [CostedReduction.totalCost, …, Comp.cost, Expr.cost]` plus
   `omega`, and lift the query count with `CostedReduction.queryBound_eval` / `TwoStageCostedReduction.queryBound_eval`.
5. Prove **size honesty** of any new table entry (`OpsSizeHonest`, `SampSizeHonest`).

## 9. Proof engineering tips

* **Simp first, `omega` last.** Cost and query goals are sums, products by constants, and `max`
  from branches. Unfold with `simp only [...]` and close with `omega`.
* **Many-branch handlers can exhaust memory.** A handler with dozens of branches produces deeply
  nested `max (a + max b c) …` terms, and one `omega` call on such a goal can need more than
  12 GiB in the kernel. Split by cases into separate lemmas. Distribute first with
  `simp only [← Nat.add_max_add_left, ← Nat.add_max_add_right, Nat.max_le]`, then `and_intros`
  and `all_goals omega` (see `sigHandleC_queries_le_*` in `KeyIndSigKemBounds.lean`).
* **Build with `CI=1`.** CI runs Lean with `-M 12288`. Locally, `lakefile.lean` may allow up to
  32 GiB. Set `CI=1` so local builds use the same 12 GiB cap.
* **Write per-construct `@[simp]` cost lemmas** for your helpers (`fooC_cost`, `fooC_queries`).
  Then the top-level `simp` never has to unfold a large term.
* **`rfl` for semantics of small steps.** `Env.get` is a dependent match that `simp` does not
  always reduce; `rfl` does.

## 10. Where the costs enter the headlines

Lemma 1 (`PqxdhCorrectAndSecureδ` and `PqxdhKeyIndSecureδ` in
`Computational/Specifications/Pqxdh/Security/HeadlineDelta.lean` and `Headline.lean`) covers
one-key `KeyInd` and one-key first-message `Auth`: it asks for `ReductionDsl` programs
(`KeyIndCostedReductionFamily`, and `Auth1KeyCostedReductionFamily` in `Auth/Headline.lean`) whose
evaluations satisfy the shallow security and semantic query-compliance bounds
(`PqxdhKeyIndReductionBoundδ` and `KeyIndReductionQueryBounds`; `PqxdhAuth1KeyReductionBoundδ` and
`Auth1KeyReductionQueryBounds`). Standalone two-key `KeyInd` and `Auth` reduction families
(`KeyInd2KeyCostedReductionFamily` and `AuthCostedReductionFamily`) live outside the trusted base in
`Computational/Proofs/SignalPqxdh/TwoKeyAndAuthStatements.lean`. Lemma 1 also asks that each
program's `totalCost` be at most `stepCostBudget S b`, its `totalQueries` at most the assumption
query budgets, and its value sizes at most `outputSizeBudget S b ℓ`
(`Computational/Specifications/Pqxdh/Security/CostedBudgets.lean`). The libsignal end-to-end
headlines use the atomic operation tables in `Computational/Specifications/Reductions/ReductionDsl/AtomicOps.lean` (with proof-side
per-game and E2E tables in `Computational/Proofs/SpecLemmas/{Reductions/E2E,Reductions/Primitives,Session/ACD19}/*`).

## 11. FAQ for cryptographers

**Why does `noncomputable` in Lean not undermine the cost bound?**
`Expr.cost`, `Comp.cost`, and `CostedReduction.totalCost` are structural recursions on the
first-order syntax tree (`Core.lean`), which embeds no Lean functions. In Lean, `noncomputable`
only means no native code is emitted (for example when real-valued probabilities appear in nearby
definitions); most `ReductionDsl` program definitions do not carry `noncomputable` anyway. Moreover,
in `PqxdhKeyIndSecureδ` the reduction family `R : KeyIndCostedReductionFamily S` is chosen before
`∀ (P : Primitives)`, and `Expr` has no constructor for arbitrary constants of abstract primitive
sorts, so `R` cannot embed `P`-specific advice.

**Can a reduction invent a huge number or value for free?**
No. Numeric literals `nat n` pay `bits n = log₂ n + 1`, constant multipliers `mulK k` pay `bits k`,
there is no general multiplication `x * y` or exponentiation, addition increases bit width by at
most `1`, `appendL K` truncates to `K` entries and pays `K`, and every loop bound `K` (or `n`) pays
`K` times its body cost. `Comp.fits_eval` (`Computational/Proofs/ReductionDsl/Size.lean`) proves
that every value's block, bit, and list size is bounded by input size plus accumulated cost (plus
the headline's answer-size bound `ℓ`), and `stepCostBudget S b` is a closed polynomial in `(S, b)`.
Three caveats are part of reading the trusted specification: (1) the per-op costs, query weights,
and coin-sampler widths in the shared `CostedTables.lean` files are trusted; (2) `R` is indexed by
`QueryBudget`, so the program may differ per budget `b`; and (3) `A`'s own running time is outside
`totalCost`.

**Why is the adversary unbounded?**
`BoundedAdv` restricts only `A`'s oracle queries (`QueryBudget`), not `A`'s internal running time:
`A` is an arbitrary `OracleComp`. Because the theorem states a concrete reduction rather than an
unconditional bound, quantifying `∀ A` with no time restriction is strictly stronger than
restricting `A` to a time class. Running time enters when instantiating the assumptions:
`CostedReduction.eval R A` runs `A` as a black box once (with no rewinding) plus at most
`totalCost` steps of its own (`≤ stepCostBudget S b`), so `time(R(A))` is `time(A)` plus the
reduction's bounded overhead, matching the standard black-box concrete-security reading.
