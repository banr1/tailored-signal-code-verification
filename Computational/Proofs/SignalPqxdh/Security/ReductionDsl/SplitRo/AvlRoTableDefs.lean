/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.TargetCodecs

/-!
# Persistent AVL Random-Oracle Cache Definitions over `Ty.tbl`

**Checked by Lean.** Defines the persistent balanced binary search (AVL) table representation
`avlTy K V` in `Comp pqAtomicOps`, single-pass downward searches (`avlSearchB192C`,
`avlSearchPair32C`), upward shape-only rebalancing (`avlRebalanceStepE`, `avlInsertAtPathC`),
lookup-or-sample combinators (`avlRoQueryDrKeyC`, `avlRoRootQueryPairC`), and the inductive subtree
predicate `AvlTree`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs

open OracleSpec OracleComp
open _root_.ReductionDsl (
  Ty Var Expr Comp Env Iface Samplers
  pqAtomicSig pqAtomicOps pqAtomicSamplers
  AtomicPureOp atomicPureOps atomicBaseSamplers unifSamplers AtomicBaseUnif
  B PB BV256 drKeyT bits
)

/-- `(left, (right, height))` shape record for a node in `shapeTbl` (`0` = empty sentinel). -/
@[reducible, expose] def avlShapeTy : Ty pqAtomicSig :=
  .prod .nat (.prod .nat .nat)

/-- One step `(parentId, wentLeft)` recorded along a downward search path (head = bottommost). -/
@[reducible, expose] def avlPathItemTy : Ty pqAtomicSig :=
  .prod .nat .bool

/-- Result `(hit?, downwardPath)` of a single-pass AVL search. -/
@[reducible, expose] def avlSearchResTy (V : Ty pqAtomicSig) : Ty pqAtomicSig :=
  .prod (.opt V) (.list avlPathItemTy)

/-- Persistent AVL map `(root, (count, (kvTbl, shapeTbl)))` over `pqAtomicSig`. -/
@[reducible, expose] def avlTy (K V : Ty pqAtomicSig) : Ty pqAtomicSig :=
  .prod .nat (.prod .nat (.prod (.tbl (.prod K V)) (.tbl avlShapeTy)))

/-- Static loop bound `2 * bits cap` strictly exceeding the height of any AVL tree of size `≤ cap`. -/
@[reducible, expose] def avlHeightCap (cap : ℕ) : ℕ :=
  2 * bits cap

section ExprHelpers

variable {Γ : List (Ty pqAtomicSig)}

@[reducible, expose] def aop (o : AtomicPureOp) (a : Expr pqAtomicOps Γ (o.dom 0 Empty)) :
    Expr pqAtomicOps Γ (o.cod 0 Empty) :=
  Expr.op (O := pqAtomicOps) o a

@[reducible, expose] def avlRootE {K V : Ty pqAtomicSig} (t : Expr pqAtomicOps Γ (avlTy K V)) :
    Expr pqAtomicOps Γ .nat := .fst t

@[reducible, expose] def avlCountE {K V : Ty pqAtomicSig} (t : Expr pqAtomicOps Γ (avlTy K V)) :
    Expr pqAtomicOps Γ .nat := .fst (.snd t)

@[reducible, expose] def avlKvE {K V : Ty pqAtomicSig} (t : Expr pqAtomicOps Γ (avlTy K V)) :
    Expr pqAtomicOps Γ (.tbl (.prod K V)) := .fst (.snd (.snd t))

@[reducible, expose] def avlShapeE {K V : Ty pqAtomicSig} (t : Expr pqAtomicOps Γ (avlTy K V)) :
    Expr pqAtomicOps Γ (.tbl avlShapeTy) := .snd (.snd (.snd t))

@[reducible, expose] def avlMkE {K V : Ty pqAtomicSig}
    (r cnt : Expr pqAtomicOps Γ .nat)
    (kv : Expr pqAtomicOps Γ (.tbl (.prod K V)))
    (sh : Expr pqAtomicOps Γ (.tbl avlShapeTy)) :
    Expr pqAtomicOps Γ (avlTy K V) :=
  .pair r (.pair cnt (.pair kv sh))

/-- Empty AVL map expression `(0, (0, (tconst (dfltK, dfltV), tconst (0, (0, 0)))))`. -/
@[expose] def avlEmptyE {K V : Ty pqAtomicSig}
    (dfltK : Expr pqAtomicOps Γ K) (dfltV : Expr pqAtomicOps Γ V) :
    Expr pqAtomicOps Γ (avlTy K V) :=
  avlMkE (.nat 0) (.nat 0)
    (.tconst (.pair dfltK dfltV))
    (.tconst (.pair (.nat 0) (.pair (.nat 0) (.nat 0))))

@[expose] def dfltB192E : Expr pqAtomicOps Γ (B 192) :=
  aop (.bytesLit 192 []) .unit

@[expose] def dfltPair32E : Expr pqAtomicOps Γ (.prod (B 32) (B 32)) :=
  .pair (aop (.bytesLit 32 []) .unit) (aop (.bytesLit 32 []) .unit)

@[expose] def dfltDrKeyE : Expr pqAtomicOps Γ (drKeyT (ℓ := 0) (Pt := Empty)) :=
  .pair (aop (.pbytesLit 32 []) .unit)
    (.pair (aop (.pbytesLit 32 []) .unit) (aop (.pbytesLit 32 []) .unit))

@[expose] def dfltPbytesPair32E : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32)) :=
  .pair (aop (.pbytesLit 32 []) .unit) (aop (.pbytesLit 32 []) .unit)

@[expose] def maxNatE (a b : Expr pqAtomicOps Γ .nat) : Expr pqAtomicOps Γ .nat :=
  .ite (.lt a b) b a

@[expose] def nodeHeightE (sh : Expr pqAtomicOps Γ (.tbl avlShapeTy))
    (idE : Expr pqAtomicOps Γ .nat) : Expr pqAtomicOps Γ .nat :=
  .snd (.snd (.tget sh idE))

@[expose] def mkShapeNodeE (l r h : Expr pqAtomicOps Γ .nat) : Expr pqAtomicOps Γ avlShapeTy :=
  .pair l (.pair r h)

@[expose] def joinHeightE (h1 h2 : Expr pqAtomicOps Γ .nat) : Expr pqAtomicOps Γ .nat :=
  .add (maxNatE h1 h2) (.nat 1)

@[expose] def orBoolE (a b : Expr pqAtomicOps Γ .bool) : Expr pqAtomicOps Γ .bool :=
  .ite a (.bool true) b

/-- Pure upward AVL rebalance step performing single or double rotations on `shapeTbl` without
    modifying `kvTbl`. -/
@[expose] def avlRebalanceStepE
    (item : Expr pqAtomicOps Γ avlPathItemTy)
    (acc : Expr pqAtomicOps Γ (.prod .nat (.tbl avlShapeTy))) :
    Expr pqAtomicOps Γ (.prod .nat (.tbl avlShapeTy)) :=
  let T0 : Ty pqAtomicSig := .prod avlPathItemTy (.prod .nat (.tbl avlShapeTy))
  let Γ1 : List (Ty pqAtomicSig) := T0 :: Γ
  let Γ2 : List (Ty pqAtomicSig) := avlShapeTy :: Γ1
  let Γ3 : List (Ty pqAtomicSig) := .prod .nat .nat :: Γ2
  let Γ4 : List (Ty pqAtomicSig) := .prod avlShapeTy avlShapeTy :: Γ3
  let Γ5 : List (Ty pqAtomicSig) := .prod .nat .nat :: Γ4
  let Γ6 : List (Ty pqAtomicSig) := avlShapeTy :: Γ5
  .letE (.pair item acc)
    (let p1  : Expr pqAtomicOps Γ1 .nat := .fst (.fst .v0)
     let sh1 : Expr pqAtomicOps Γ1 (.tbl avlShapeTy) := .snd (.snd .v0)
     .letE (.tget sh1 p1)
       (let wl2 : Expr pqAtomicOps Γ2 .bool := .snd (.fst .v1)
        let c2  : Expr pqAtomicOps Γ2 .nat := .fst (.snd .v1)
        let l0  : Expr pqAtomicOps Γ2 .nat := .fst .v0
        let r0  : Expr pqAtomicOps Γ2 .nat := .fst (.snd .v0)
        .letE (.pair (.ite wl2 c2 l0) (.ite wl2 r0 c2))
          (let sh3 : Expr pqAtomicOps Γ3 (.tbl avlShapeTy) := .snd (.snd .v2)
           let l3  : Expr pqAtomicOps Γ3 .nat := .fst .v0
           let r3  : Expr pqAtomicOps Γ3 .nat := .snd .v0
           .letE (.pair (.tget sh3 l3) (.tget sh3 r3))
             (let p4   : Expr pqAtomicOps Γ4 .nat := .fst (.fst .v3)
              let sh4  : Expr pqAtomicOps Γ4 (.tbl avlShapeTy) := .snd (.snd .v3)
              let l4   : Expr pqAtomicOps Γ4 .nat := .fst .v1
              let r4   : Expr pqAtomicOps Γ4 .nat := .snd .v1
              let ll4  : Expr pqAtomicOps Γ4 .nat := .fst (.fst .v0)
              let lr4  : Expr pqAtomicOps Γ4 .nat := .fst (.snd (.fst .v0))
              let lh4  : Expr pqAtomicOps Γ4 .nat := .snd (.snd (.fst .v0))
              let rl4  : Expr pqAtomicOps Γ4 .nat := .fst (.snd .v0)
              let rr4  : Expr pqAtomicOps Γ4 .nat := .fst (.snd (.snd .v0))
              let rh4  : Expr pqAtomicOps Γ4 .nat := .snd (.snd (.snd .v0))
              .ite (.lt (.add rh4 (.nat 1)) lh4)
                (.letE (.pair (nodeHeightE sh4 ll4) (nodeHeightE sh4 lr4))
                  (let p5   : Expr pqAtomicOps Γ5 .nat := .fst (.fst .v4)
                   let sh5  : Expr pqAtomicOps Γ5 (.tbl avlShapeTy) := .snd (.snd .v4)
                   let l5   : Expr pqAtomicOps Γ5 .nat := .fst .v2
                   let r5   : Expr pqAtomicOps Γ5 .nat := .snd .v2
                   let ll5  : Expr pqAtomicOps Γ5 .nat := .fst (.fst .v1)
                   let lr5  : Expr pqAtomicOps Γ5 .nat := .fst (.snd (.fst .v1))
                   let rh5  : Expr pqAtomicOps Γ5 .nat := .snd (.snd (.snd .v1))
                   let llh5 : Expr pqAtomicOps Γ5 .nat := .fst .v0
                   let lrh5 : Expr pqAtomicOps Γ5 .nat := .snd .v0
                   .ite (.lt llh5 lrh5)
                     (.letE (.tget sh5 lr5)
                       (let p6   : Expr pqAtomicOps Γ6 .nat := .fst (.fst .v5)
                        let sh6  : Expr pqAtomicOps Γ6 (.tbl avlShapeTy) := .snd (.snd .v5)
                        let l6   : Expr pqAtomicOps Γ6 .nat := .fst .v3
                        let r6   : Expr pqAtomicOps Γ6 .nat := .snd .v3
                        let ll6  : Expr pqAtomicOps Γ6 .nat := .fst (.fst .v2)
                        let lr6  : Expr pqAtomicOps Γ6 .nat := .fst (.snd (.fst .v2))
                        let rh6  : Expr pqAtomicOps Γ6 .nat := .snd (.snd (.snd .v2))
                        let llh6 : Expr pqAtomicOps Γ6 .nat := .fst .v1
                        let lrl6 : Expr pqAtomicOps Γ6 .nat := .fst .v0
                        let lrr6 : Expr pqAtomicOps Γ6 .nat := .fst (.snd .v0)
                        let hl'  := joinHeightE llh6 (nodeHeightE sh6 lrl6)
                        let hp'  := joinHeightE (nodeHeightE sh6 lrr6) rh6
                        let shA  := Expr.tset sh6 l6 (mkShapeNodeE ll6 lrl6 hl')
                        let shB  := Expr.tset shA p6 (mkShapeNodeE lrr6 r6 hp')
                        let shC  := Expr.tset shB lr6 (mkShapeNodeE l6 p6 (joinHeightE hl' hp'))
                        .pair lr6 shC))
                     (let hp' := joinHeightE lrh5 rh5
                      let shA := Expr.tset sh5 p5 (mkShapeNodeE lr5 r5 hp')
                      let shB := Expr.tset shA l5 (mkShapeNodeE ll5 p5 (joinHeightE llh5 hp'))
                      .pair l5 shB)))
                (.ite (.lt (.add lh4 (.nat 1)) rh4)
                  (.letE (.pair (nodeHeightE sh4 rl4) (nodeHeightE sh4 rr4))
                    (let p5   : Expr pqAtomicOps Γ5 .nat := .fst (.fst .v4)
                     let sh5  : Expr pqAtomicOps Γ5 (.tbl avlShapeTy) := .snd (.snd .v4)
                     let l5   : Expr pqAtomicOps Γ5 .nat := .fst .v2
                     let r5   : Expr pqAtomicOps Γ5 .nat := .snd .v2
                     let lh5  : Expr pqAtomicOps Γ5 .nat := .snd (.snd (.fst .v1))
                     let rl5  : Expr pqAtomicOps Γ5 .nat := .fst (.snd .v1)
                     let rr5  : Expr pqAtomicOps Γ5 .nat := .fst (.snd (.snd .v1))
                     let rlh5 : Expr pqAtomicOps Γ5 .nat := .fst .v0
                     let rrh5 : Expr pqAtomicOps Γ5 .nat := .snd .v0
                     .ite (.lt rrh5 rlh5)
                       (.letE (.tget sh5 rl5)
                         (let p6   : Expr pqAtomicOps Γ6 .nat := .fst (.fst .v5)
                          let sh6  : Expr pqAtomicOps Γ6 (.tbl avlShapeTy) := .snd (.snd .v5)
                          let l6   : Expr pqAtomicOps Γ6 .nat := .fst .v3
                          let r6   : Expr pqAtomicOps Γ6 .nat := .snd .v3
                          let lh6  : Expr pqAtomicOps Γ6 .nat := .snd (.snd (.fst .v2))
                          let rl6  : Expr pqAtomicOps Γ6 .nat := .fst (.snd .v2)
                          let rr6  : Expr pqAtomicOps Γ6 .nat := .fst (.snd (.snd .v2))
                          let rrh6 : Expr pqAtomicOps Γ6 .nat := .snd .v1
                          let rll6 : Expr pqAtomicOps Γ6 .nat := .fst .v0
                          let rlr6 : Expr pqAtomicOps Γ6 .nat := .fst (.snd .v0)
                          let hp'  := joinHeightE lh6 (nodeHeightE sh6 rll6)
                          let hr'  := joinHeightE (nodeHeightE sh6 rlr6) rrh6
                          let shA  := Expr.tset sh6 p6 (mkShapeNodeE l6 rll6 hp')
                          let shB  := Expr.tset shA r6 (mkShapeNodeE rlr6 rr6 hr')
                          let shC  := Expr.tset shB rl6 (mkShapeNodeE p6 r6 (joinHeightE hp' hr'))
                          .pair rl6 shC))
                       (let hp' := joinHeightE lh5 rlh5
                        let shA := Expr.tset sh5 p5 (mkShapeNodeE l5 rl5 hp')
                        let shB := Expr.tset shA r5 (mkShapeNodeE p5 rr5 (joinHeightE hp' rrh5))
                        .pair r5 shB)))
                  (.pair p4 (.tset sh4 p4 (mkShapeNodeE l4 r4 (joinHeightE lh4 rh4)))))))))

end ExprHelpers

section Programs

variable {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}

/-- Accumulator `(cur, (candId, path))` for the downward search loop. -/
@[reducible, expose] def avlLoopAccTy : Ty pqAtomicSig :=
  .prod .nat (.prod .nat (.list avlPathItemTy))

/-- Single-pass downward AVL search on `B 192` keys. -/
@[expose] def avlSearchB192C (cap : ℕ) {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy (B 192) V))
    (keyE : Expr pqAtomicOps Γ (B 192)) :
    Comp pqAtomicOps I Γ (avlSearchResTy V) :=
  let TK  : Ty pqAtomicSig := .prod (avlTy (B 192) V) (B 192)
  let Γ1  : List (Ty pqAtomicSig) := TK :: Γ
  let Γ2  : List (Ty pqAtomicSig) := avlLoopAccTy :: Γ1
  let Γ2s : List (Ty pqAtomicSig) := avlShapeTy :: Γ2
  let Γ2e : List (Ty pqAtomicSig) := .prod (B 192) V :: Γ2
  .bind (.ret (.pair tblE keyE))
    (let tbl1 : Expr pqAtomicOps Γ1 (avlTy (B 192) V) := .fst .v0
     let init : Expr pqAtomicOps Γ1 avlLoopAccTy :=
       .pair (avlRootE tbl1) (.pair (.nat 0) .nil)
     .bind
       (.iter (avlHeightCap cap) init
         (let cur2 : Expr pqAtomicOps Γ2 .nat := .fst .v0
          let tbl2 : Expr pqAtomicOps Γ2 (avlTy (B 192) V) := .fst .v1
          .ite (.eqN cur2 (.nat 0))
            (.ret .v0)
            (.ret
              (.letE (.tget (avlShapeE tbl2) cur2)
                (let curS  : Expr pqAtomicOps Γ2s .nat := .fst .v1
                 let candS : Expr pqAtomicOps Γ2s .nat := .fst (.snd .v1)
                 let pathS : Expr pqAtomicOps Γ2s (.list avlPathItemTy) := .snd (.snd .v1)
                 let tblS  : Expr pqAtomicOps Γ2s (avlTy (B 192) V) := .fst .v2
                 let keyS  : Expr pqAtomicOps Γ2s (B 192) := .snd .v2
                 let lS    : Expr pqAtomicOps Γ2s .nat := .fst .v0
                 let rS    : Expr pqAtomicOps Γ2s .nat := .fst (.snd .v0)
                 let goL   : Expr pqAtomicOps Γ2s .bool :=
                   aop (.bytesLtOp 192 192) (.pair keyS (.fst (.tget (avlKvE tblS) curS)))
                 .ite goL
                   (.pair lS (.pair candS (.cons (.pair curS (.bool true)) pathS)))
                   (.pair rS (.pair curS (.cons (.pair curS (.bool false)) pathS))))))))
       (let cand2 : Expr pqAtomicOps Γ2 .nat := .fst (.snd .v0)
        let path2 : Expr pqAtomicOps Γ2 (.list avlPathItemTy) := .snd (.snd .v0)
        let tbl2  : Expr pqAtomicOps Γ2 (avlTy (B 192) V) := .fst .v1
        .ret
          (.ite (.eqN cand2 (.nat 0))
            (.pair .none path2)
            (.letE (.tget (avlKvE tbl2) cand2)
              (let candK : Expr pqAtomicOps Γ2e (B 192) := .fst .v0
               let candV : Expr pqAtomicOps Γ2e V := .snd .v0
               let keyE' : Expr pqAtomicOps Γ2e (B 192) := .snd .v2
               let path' : Expr pqAtomicOps Γ2e (.list avlPathItemTy) := .snd (.snd .v1)
               .ite (aop (.bytesEq 192 192) (.pair keyE' candK))
                 (.pair (.some candV) path')
                 (.pair .none path'))))))

/-- Single-pass downward search on `(B 32 × B 32)` keys using collision-free lexicographic order. -/
@[expose] def avlSearchPair32C (cap : ℕ) {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy (.prod (B 32) (B 32)) V))
    (keyE : Expr pqAtomicOps Γ (.prod (B 32) (B 32))) :
    Comp pqAtomicOps I Γ (avlSearchResTy V) :=
  let KP  : Ty pqAtomicSig := .prod (B 32) (B 32)
  let TK  : Ty pqAtomicSig := .prod (avlTy KP V) KP
  let Γ1  : List (Ty pqAtomicSig) := TK :: Γ
  let Γ2  : List (Ty pqAtomicSig) := avlLoopAccTy :: Γ1
  let Γ2s : List (Ty pqAtomicSig) := .prod avlShapeTy KP :: Γ2
  let Γ2e : List (Ty pqAtomicSig) := .prod KP V :: Γ2
  .bind (.ret (.pair tblE keyE))
    (let tbl1 : Expr pqAtomicOps Γ1 (avlTy KP V) := .fst .v0
     let init : Expr pqAtomicOps Γ1 avlLoopAccTy :=
       .pair (avlRootE tbl1) (.pair (.nat 0) .nil)
     .bind
       (.iter (avlHeightCap cap) init
         (let cur2 : Expr pqAtomicOps Γ2 .nat := .fst .v0
          let tbl2 : Expr pqAtomicOps Γ2 (avlTy KP V) := .fst .v1
          .ite (.eqN cur2 (.nat 0))
            (.ret .v0)
            (.ret
              (.letE (.pair (.tget (avlShapeE tbl2) cur2) (.fst (.tget (avlKvE tbl2) cur2)))
                (let curS  : Expr pqAtomicOps Γ2s .nat := .fst .v1
                 let candS : Expr pqAtomicOps Γ2s .nat := .fst (.snd .v1)
                 let pathS : Expr pqAtomicOps Γ2s (.list avlPathItemTy) := .snd (.snd .v1)
                 let keyS  : Expr pqAtomicOps Γ2s KP := .snd .v2
                 let lS    : Expr pqAtomicOps Γ2s .nat := .fst (.fst .v0)
                 let rS    : Expr pqAtomicOps Γ2s .nat := .fst (.snd (.fst .v0))
                 let curK  : Expr pqAtomicOps Γ2s KP := .snd .v0
                 let lt1   := aop (.bytesLtOp 32 32) (.pair (.fst keyS) (.fst curK))
                 let eq1   := aop (.bytesEq 32 32) (.pair (.fst keyS) (.fst curK))
                 let lt2   := aop (.bytesLtOp 32 32) (.pair (.snd keyS) (.snd curK))
                 let goL   := orBoolE lt1 (.and eq1 lt2)
                 .ite goL
                   (.pair lS (.pair candS (.cons (.pair curS (.bool true)) pathS)))
                   (.pair rS (.pair curS (.cons (.pair curS (.bool false)) pathS))))))))
       (let cand2 : Expr pqAtomicOps Γ2 .nat := .fst (.snd .v0)
        let path2 : Expr pqAtomicOps Γ2 (.list avlPathItemTy) := .snd (.snd .v0)
        let tbl2  : Expr pqAtomicOps Γ2 (avlTy KP V) := .fst .v1
        .ret
          (.ite (.eqN cand2 (.nat 0))
            (.pair .none path2)
            (.letE (.tget (avlKvE tbl2) cand2)
              (let candK : Expr pqAtomicOps Γ2e KP := .fst .v0
               let candV : Expr pqAtomicOps Γ2e V := .snd .v0
               let keyE' : Expr pqAtomicOps Γ2e KP := .snd .v2
               let path' : Expr pqAtomicOps Γ2e (.list avlPathItemTy) := .snd (.snd .v1)
               let eqK   := Expr.and
                 (aop (.bytesEq 32 32) (.pair (.fst keyE') (.fst candK)))
                 (aop (.bytesEq 32 32) (.pair (.snd keyE') (.snd candK)))
               .ite eqK
                 (.pair (.some candV) path')
                 (.pair .none path'))))))

/-- Inserts a fresh `(key, val)` at the leaf reached by `path` and rebalances `shapeTbl` upward. -/
@[expose] def avlInsertAtPathC (cap : ℕ) {Γ : List (Ty pqAtomicSig)} {K V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy K V))
    (pathE : Expr pqAtomicOps Γ (.list avlPathItemTy))
    (keyE : Expr pqAtomicOps Γ K)
    (valE : Expr pqAtomicOps Γ V) :
    Comp pqAtomicOps I Γ (avlTy K V) :=
  let T1 : Ty pqAtomicSig := .prod (.prod (avlTy K V) (.list avlPathItemTy)) (.prod K V)
  let T2 : Ty pqAtomicSig :=
    .prod .nat (.prod (.tbl (.prod K V)) (.prod (.tbl avlShapeTy) (.list avlPathItemTy)))
  let Γ1 : List (Ty pqAtomicSig) := T1 :: Γ
  let Γ2 : List (Ty pqAtomicSig) := T2 :: Γ1
  let Γ3 : List (Ty pqAtomicSig) := .prod .nat (.tbl avlShapeTy) :: Γ2
  .bind (.ret (.pair (.pair tblE pathE) (.pair keyE valE)))
    (let tbl1  : Expr pqAtomicOps Γ1 (avlTy K V) := .fst (.fst .v0)
     let path1 : Expr pqAtomicOps Γ1 (.list avlPathItemTy) := .snd (.fst .v0)
     let key1  : Expr pqAtomicOps Γ1 K := .fst (.snd .v0)
     let val1  : Expr pqAtomicOps Γ1 V := .snd (.snd .v0)
     let newId : Expr pqAtomicOps Γ1 .nat := .add (avlCountE tbl1) (.nat 1)
     let kv1   : Expr pqAtomicOps Γ1 (.tbl (.prod K V)) :=
       .tset (avlKvE tbl1) newId (.pair key1 val1)
     let sh1   : Expr pqAtomicOps Γ1 (.tbl avlShapeTy) :=
       .tset (avlShapeE tbl1) newId (mkShapeNodeE (.nat 0) (.nat 0) (.nat 1))
     .bind (.ret (.pair newId (.pair kv1 (.pair sh1 path1))))
       (let newId2 : Expr pqAtomicOps Γ2 .nat := .fst .v0
        let sh2    : Expr pqAtomicOps Γ2 (.tbl avlShapeTy) := .fst (.snd (.snd .v0))
        let path2  : Expr pqAtomicOps Γ2 (.list avlPathItemTy) := .snd (.snd (.snd .v0))
        .bind
          (.foldM (avlHeightCap cap) path2 (.pair newId2 sh2)
            (.ret (avlRebalanceStepE .v0 .v1)))
          (let newRoot : Expr pqAtomicOps Γ3 .nat := .fst .v0
           let shFinal : Expr pqAtomicOps Γ3 (.tbl avlShapeTy) := .snd .v0
           let newCnt  : Expr pqAtomicOps Γ3 .nat := .fst .v1
           let kvFinal : Expr pqAtomicOps Γ3 (.tbl (.prod K V)) := .fst (.snd .v1)
           .ret (avlMkE newRoot newCnt kvFinal shFinal))))

end Programs

section ConcreteSamplers

@[expose] def samplePbytes32C {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) {Γ : List (Ty pqAtomicSig)} :
    Comp pqAtomicOps I Γ (PB 32) :=
  let tag : I.smp.Samp := cast (congrArg Samplers.Samp hSmp.symm) (.base .bv256)
  let domCast : (I.smp.sDom tag) = .unit := by
    rcases I with ⟨_, _, _, _, _, _, _, _, smp⟩; dsimp only at hSmp; cases hSmp; rfl
  let tyCast : (I.smp.sTy tag) = BV256 := by
    rcases I with ⟨_, _, _, _, _, _, _, _, smp⟩; dsimp only at hSmp; cases hSmp; rfl
  let uE : Expr pqAtomicOps Γ (I.smp.sDom tag) :=
    cast (congrArg (Expr pqAtomicOps Γ) domCast.symm) Expr.unit
  let vE : Expr pqAtomicOps (I.smp.sTy tag :: Γ) BV256 :=
    cast (congrArg (Expr pqAtomicOps (I.smp.sTy tag :: Γ)) tyCast)
      (Expr.v0 : Expr pqAtomicOps (I.smp.sTy tag :: Γ) (I.smp.sTy tag))
  .bind (.sample tag uE) (.ret (aop .bv256ToPbytes32 vE))

@[expose] def sampleDrKey96AtomicC {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) {Γ : List (Ty pqAtomicSig)} :
    Comp pqAtomicOps I Γ (drKeyT (ℓ := 0) (Pt := Empty)) :=
  .bind (samplePbytes32C hSmp)
    (.bind (samplePbytes32C hSmp)
      (.bind (samplePbytes32C hSmp)
        (.ret (.pair .v2 (.pair .v1 .v0)))))

@[expose] def sampleRootPair64AtomicC {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) {Γ : List (Ty pqAtomicSig)} :
    Comp pqAtomicOps I Γ (.prod (PB 32) (PB 32)) :=
  .bind (samplePbytes32C hSmp)
    (.bind (samplePbytes32C hSmp)
      (.ret (.pair .v1 .v0)))

/-- Logarithmic-cost random-oracle lookup-or-sample on `PB 192 → drKeyT`. -/
@[expose] def avlRoQueryDrKeyC {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (tblE : Expr pqAtomicOps Γ (avlTy (B 192) (drKeyT (ℓ := 0) (Pt := Empty))))
    (secE : Expr pqAtomicOps Γ (PB 192)) :
    Comp pqAtomicOps I Γ
      (.prod (drKeyT (ℓ := 0) (Pt := Empty)) (avlTy (B 192) (drKeyT (ℓ := 0) (Pt := Empty)))) :=
  .bind (.ret (.pair tblE (aop (.pbytesToBytes 192) secE)))
    (.bind (avlSearchB192C cap (.fst .v0) (.snd .v0))
      (.caseOpt (.fst .v0)
        (.bind (sampleDrKey96AtomicC hSmp)
          (.bind (avlInsertAtPathC cap (.fst .v2) (.snd .v1) (.snd .v2) .v0)
            (.ret (.pair .v1 .v0))))
        (.ret (.pair .v0 (.fst .v2)))))

/-- Logarithmic-cost root-KDF random-oracle lookup-or-sample on
    `(PB 32 × PB 32) → (PB 32 × PB 32)`. -/
@[expose] def avlRoRootQueryPairC {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (tblE : Expr pqAtomicOps Γ (avlTy (.prod (B 32) (B 32)) (.prod (PB 32) (PB 32))))
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    Comp pqAtomicOps I Γ
      (.prod (.prod (PB 32) (PB 32))
        (avlTy (.prod (B 32) (B 32)) (.prod (PB 32) (PB 32)))) :=
  let keyPairE : Expr pqAtomicOps Γ (.prod (B 32) (B 32)) :=
    .letE inpE (.pair (aop (.pbytesToBytes 32) (.fst .v0)) (aop (.pbytesToBytes 32) (.snd .v0)))
  .bind (.ret (.pair tblE keyPairE))
    (.bind (avlSearchPair32C cap (.fst .v0) (.snd .v0))
      (.caseOpt (.fst .v0)
        (.bind (sampleRootPair64AtomicC hSmp)
          (.bind (avlInsertAtPathC cap (.fst .v2) (.snd .v1) (.snd .v2) .v0)
            (.ret (.pair .v1 .v0))))
        (.ret (.pair .v0 (.fst .v2)))))

end ConcreteSamplers

/-- Inductive AVL subtree witness on `(kvTbl, shapeTbl)` certifying bounded node IDs, strict BST
    ordering under `ltK`, exact cached heights, and AVL balance, projecting to `kvs`. -/
inductive AvlTree {K V : Type} (ltK : K → K → Prop)
    (kvTbl : ℕ → K × V) (shapeTbl : ℕ → ℕ × (ℕ × ℕ)) (maxId : ℕ) :
    ℕ → ℕ → List (K × V) → Prop
  | leaf :
      shapeTbl 0 = (0, (0, 0)) →
      AvlTree ltK kvTbl shapeTbl maxId 0 0 []
  | node {id l r h lh rh : ℕ} {k : K} {v : V} {kvsL kvsR : List (K × V)} :
      0 < id → id ≤ maxId →
      kvTbl id = (k, v) →
      shapeTbl id = (l, (r, h)) →
      h = max lh rh + 1 →
      lh ≤ rh + 1 → rh ≤ lh + 1 →
      AvlTree ltK kvTbl shapeTbl maxId l lh kvsL →
      AvlTree ltK kvTbl shapeTbl maxId r rh kvsR →
      (∀ kv ∈ kvsL, ltK kv.1 k) →
      (∀ kv ∈ kvsR, ltK k kv.1) →
      AvlTree ltK kvTbl shapeTbl maxId id h (kvsL ++ (k, v) :: kvsR)

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs
