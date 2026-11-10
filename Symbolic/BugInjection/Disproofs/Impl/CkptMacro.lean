/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import Symbolic.BugInjection.Proofs.CliExec.TreePatch
public meta import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux

/-!
# Elaboration-Time Constructor Macros for CLI Mutant Checkpoints

Elaborates compact string-chunk encodings directly into constructor-form `Expr` trees with no
kernel reduction overhead: `fast_hex`, `fast_hex_chunks`, `ckpt_regs`, `ckpt_patch`, `ckpt_lines`,
`ckpt_line_tree`, `ckpt_hooks`, and `ckpt_trace`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.CkptMacro

open Arm64 (OutputStream TraceEvent)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux (BinTree Cell FastRegs Line64 btSet)
open Symbolic.BugInjection.Proofs.CliExec.TreePatch (TreePatch)

section ElabHelpers
open Lean (Expr TSyntax mkApp mkApp2 mkApp3 mkApp4 mkApp5 mkConst mkNatLit mkStrLit)

private meta def hexNib (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

private meta def mkBVExpr (w val : Nat) : Expr :=
  mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit w) (mkNatLit val)

private meta def mkBoolExpr (b : Bool) : Expr :=
  mkConst (if b then ``Bool.true else ``Bool.false)

meta def mkByteListFromHex (s : String) : Expr := Id.run do
  let bv8 := mkApp (mkConst ``BitVec) (mkNatLit 8)
  let mut acc := mkApp (mkConst ``List.nil [0]) bv8
  let arr := s.toByteArray
  let n := arr.size / 2
  for idx in [0:n] do
    let revIdx := n - 1 - idx
    let hi := hexNib (Char.ofNat (arr.get! (2 * revIdx)).toNat)
    let lo := hexNib (Char.ofNat (arr.get! (2 * revIdx + 1)).toNat)
    let v := 16 * hi + lo
    acc := mkApp3 (mkConst ``List.cons [0]) bv8 (mkBVExpr 8 v) acc
  return acc

private meta def parseNatSemi (arr : ByteArray) (pos : Nat) : Nat × Nat := Id.run do
  let mut i := pos
  let mut acc : Nat := 0
  while i < arr.size do
    let b := arr.get! i
    i := i + 1
    if b == ';'.toNat.toUInt8 then
      break
    acc := acc * 10 + (b.toNat - '0'.toNat)
  return (acc, i)

private meta def parseHexByteAt (arr : ByteArray) (pos : Nat) : Nat × Nat :=
  let hi := hexNib (Char.ofNat (arr.get! pos).toNat)
  let lo := hexNib (Char.ofNat (arr.get! (pos + 1)).toNat)
  (16 * hi + lo, pos + 2)

private meta def decodeOptPerm (b : UInt8) : Option Arm64.Perm :=
  if b == '-'.toNat.toUInt8 then none
  else
    let code := b.toNat - 'A'.toNat
    some {
      r        := (code &&& 1) != 0
      w        := (code &&& 2) != 0
      x        := (code &&& 4) != 0
      lazyFree := (code &&& 8) != 0
      anon     := (code &&& 16) != 0
    }

private meta def quoteOptPerm (cp : Option Arm64.Perm) : Expr :=
  let permTy := mkConst ``Arm64.Perm
  match cp with
  | none => mkApp (mkConst ``Option.none [0]) permTy
  | some p =>
    let pe := mkApp5 (mkConst ``Arm64.Perm.mk)
      (mkBoolExpr p.r) (mkBoolExpr p.w) (mkBoolExpr p.x)
      (mkBoolExpr p.lazyFree) (mkBoolExpr p.anon)
    mkApp2 (mkConst ``Option.some [0]) permTy pe

private meta def cellTyExpr : Expr :=
  mkApp2 (mkConst ``Prod [0, 0])
    (mkApp (mkConst ``Option [0]) (mkConst ``Arm64.Perm))
    (mkApp (mkConst ``BitVec) (mkNatLit 8))

private meta def line64TyExpr : Expr :=
  mkApp (mkConst ``BinTree) cellTyExpr

private meta def quoteCell (c : Cell) : Expr :=
  mkApp4 (mkConst ``Prod.mk [0, 0])
    (mkApp (mkConst ``Option [0]) (mkConst ``Arm64.Perm))
    (mkApp (mkConst ``BitVec) (mkNatLit 8))
    (quoteOptPerm c.1)
    (mkBVExpr 8 c.2.toNat)

private meta def quoteLine64 : Line64 → Expr
  | .empty => mkApp (mkConst ``BinTree.empty) cellTyExpr
  | .twig k c => mkApp3 (mkConst ``BinTree.twig) cellTyExpr (mkNatLit k) (quoteCell c)
  | .branch l r => mkApp3 (mkConst ``BinTree.branch) cellTyExpr (quoteLine64 l) (quoteLine64 r)

private meta partial def parseLine64Expr (arr : ByteArray) (pos : Nat) : Expr × Nat := Id.run do
  let tag := Char.ofNat (arr.get! pos).toNat
  if tag == 'E' then
    return (mkApp (mkConst ``BinTree.empty) cellTyExpr, pos + 1)
  else if tag == 'B' then
    let (l, p1) := parseLine64Expr arr (pos + 1)
    let (r, p2) := parseLine64Expr arr p1
    return (mkApp3 (mkConst ``BinTree.branch) cellTyExpr l r, p2)
  else if tag == 'T' then
    let (j, p1) := parseNatSemi arr (pos + 1)
    let cp := decodeOptPerm (arr.get! p1)
    let (bv, p2) := parseHexByteAt arr (p1 + 1)
    let ce := mkApp4 (mkConst ``Prod.mk [0, 0])
      (mkApp (mkConst ``Option [0]) (mkConst ``Arm64.Perm))
      (mkApp (mkConst ``BitVec) (mkNatLit 8))
      (quoteOptPerm cp)
      (mkBVExpr 8 bv)
    return (mkApp3 (mkConst ``BinTree.twig) cellTyExpr (mkNatLit j) ce, p2)
  else if tag == 'Z' then
    -- 'Z' + permChar (all-zero 64-byte uniform-perm line)
    let cp := decodeOptPerm (arr.get! (pos + 1))
    let mut ln : Line64 := .empty
    for j in [0:64] do
      ln := btSet 6 ln j (cp, 0#8)
    return (quoteLine64 ln, pos + 2)
  else
    -- 'F' + permChar + 128 hex nibbles (full 64-byte uniform-perm line)
    let cp := decodeOptPerm (arr.get! (pos + 1))
    let mut ln : Line64 := .empty
    let mut p := pos + 2
    for j in [0:64] do
      let (bv, p') := parseHexByteAt arr p
      p := p'
      ln := btSet 6 ln j (cp, BitVec.ofNat 8 bv)
    return (quoteLine64 ln, p)

private meta partial def parseLineTreeExpr (arr : ByteArray) (pos : Nat) : Expr × Nat :=
  let tag := Char.ofNat (arr.get! pos).toNat
  if tag == 'E' then
    (mkApp (mkConst ``BinTree.empty) line64TyExpr, pos + 1)
  else if tag == 'B' then
    let (l, p1) := parseLineTreeExpr arr (pos + 1)
    let (r, p2) := parseLineTreeExpr arr p1
    (mkApp3 (mkConst ``BinTree.branch) line64TyExpr l r, p2)
  else
    -- 'L' + k; + <line64>
    let (k, p1) := parseNatSemi arr (pos + 1)
    let (le, p2) := parseLine64Expr arr p1
    (mkApp3 (mkConst ``BinTree.twig) line64TyExpr (mkNatLit k) le, p2)

private meta partial def parsePatchExpr (arr : ByteArray) (pos : Nat) : Expr × Nat :=
  let tag := Char.ofNat (arr.get! pos).toNat
  if tag == 'K' then
    (mkApp (mkConst ``TreePatch.keep) line64TyExpr, pos + 1)
  else if tag == 'P' then
    let (l, p1) := parsePatchExpr arr (pos + 1)
    let (r, p2) := parsePatchExpr arr p1
    (mkApp3 (mkConst ``TreePatch.branch) line64TyExpr l r, p2)
  else
    -- 'S' + <lineTree>
    let (te, p1) := parseLineTreeExpr arr (pos + 1)
    (mkApp2 (mkConst ``TreePatch.set) line64TyExpr te, p1)

private meta partial def parseRegTreeExpr (w : Nat) (arr : ByteArray) (pos : Nat) : Expr × Nat :=
  let bvTy := mkApp (mkConst ``BitVec) (mkNatLit w)
  let tag := Char.ofNat (arr.get! pos).toNat
  if tag == 'E' then
    (mkApp (mkConst ``BinTree.empty) bvTy, pos + 1)
  else if tag == 'B' then
    let (l, p1) := parseRegTreeExpr w arr (pos + 1)
    let (r, p2) := parseRegTreeExpr w arr p1
    (mkApp3 (mkConst ``BinTree.branch) bvTy l r, p2)
  else
    -- 'T' + k; + val;
    let (k, p1) := parseNatSemi arr (pos + 1)
    let (val, p2) := parseNatSemi arr p1
    (mkApp3 (mkConst ``BinTree.twig) bvTy (mkNatLit k) (mkBVExpr w val), p2)

private meta def parseRegsExpr (s : String) : Expr :=
  let arr := s.toByteArray
  let (g, p1) := parseRegTreeExpr 64 arr 0
  let (v, _) := parseRegTreeExpr 128 arr p1
  mkApp2 (mkConst ``FastRegs.mk) g v

private meta def parseTraceExpr (s : String) : Expr := Id.run do
  let arr := s.toByteArray
  let mut evs : Array Expr := #[]
  let mut pos : Nat := 0
  while pos < arr.size do
    let tag := Char.ofNat (arr.get! pos).toNat
    if tag == 'O' then
      let (bv, p') := parseHexByteAt arr (pos + 1)
      pos := p'
      evs := evs.push (mkApp2 (mkConst ``TraceEvent.writeByte)
        (mkConst ``OutputStream.stdout) (mkBVExpr 8 bv))
    else if tag == 'E' then
      let (bv, p') := parseHexByteAt arr (pos + 1)
      pos := p'
      evs := evs.push (mkApp2 (mkConst ``TraceEvent.writeByte)
        (mkConst ``OutputStream.stderr) (mkBVExpr 8 bv))
    else if tag == 'F' then
      let (fd, p1) := parseNatSemi arr (pos + 1)
      let (bv, p2) := parseHexByteAt arr p1
      pos := p2
      let stm := mkApp (mkConst ``OutputStream.fd) (mkBVExpr 64 fd)
      evs := evs.push (mkApp2 (mkConst ``TraceEvent.writeByte) stm (mkBVExpr 8 bv))
    else
      -- 'C' + len; + utf8PathBytes
      let (plen, p1) := parseNatSemi arr (pos + 1)
      let pstr := String.fromUTF8! (arr.extract p1 (p1 + plen))
      pos := p1 + plen
      evs := evs.push (mkApp (mkConst ``TraceEvent.fileChanged) (mkStrLit pstr))
  let evTy := mkConst ``TraceEvent
  let mut acc := mkApp (mkConst ``List.nil [0]) evTy
  for idx in [0:evs.size] do
    let e := evs[evs.size - 1 - idx]!
    acc := mkApp3 (mkConst ``List.cons [0]) evTy e acc
  return acc

private meta def parseLineUpdatesExpr (s : String) : Expr := Id.run do
  let arr := s.toByteArray
  let natTy := mkConst ``Nat
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) natTy line64TyExpr
  let mut items : Array Expr := #[]
  let mut pos : Nat := 0
  while pos < arr.size do
    let (hi, p1) := parseNatSemi arr pos
    let (le, p2) := parseLine64Expr arr p1
    pos := p2
    items := items.push (mkApp4 (mkConst ``Prod.mk [0, 0]) natTy line64TyExpr (mkNatLit hi) le)
  let mut acc := mkApp (mkConst ``List.nil [0]) pairTy
  for idx in [0:items.size] do
    let e := items[items.size - 1 - idx]!
    acc := mkApp3 (mkConst ``List.cons [0]) pairTy e acc
  return acc

private meta partial def parseHookTreeExpr (arr : ByteArray) (pos : Nat) : Expr × Nat :=
  let strTy := mkConst ``String
  let tag := Char.ofNat (arr.get! pos).toNat
  if tag == 'E' then
    (mkApp (mkConst ``BinTree.empty) strTy, pos + 1)
  else if tag == 'B' then
    let (l, p1) := parseHookTreeExpr arr (pos + 1)
    let (r, p2) := parseHookTreeExpr arr p1
    (mkApp3 (mkConst ``BinTree.branch) strTy l r, p2)
  else
    -- 'H' + k; + len; + utf8Bytes
    let (k, p1) := parseNatSemi arr (pos + 1)
    let (slen, p2) := parseNatSemi arr p1
    let nm := String.fromUTF8! (arr.extract p2 (p2 + slen))
    (mkApp3 (mkConst ``BinTree.twig) strTy (mkNatLit k) (mkStrLit nm), p2 + slen)

scoped elab "fast_hex " s:str : term => return mkByteListFromHex s.getString

scoped elab "fast_hex_chunks " "[" ss:str,* "]" : term => do
  let joined := String.join (ss.getElems.toList.map TSyntax.getString)
  return mkByteListFromHex joined

scoped elab "ckpt_regs " "[" ss:str,* "]" : term => do
  let joined := String.join (ss.getElems.toList.map TSyntax.getString)
  return parseRegsExpr joined

scoped elab "ckpt_patch " "[" ss:str,* "]" : term => do
  let joined := String.join (ss.getElems.toList.map TSyntax.getString)
  let (e, _) := parsePatchExpr joined.toByteArray 0
  return e

scoped elab "ckpt_lines " "[" ss:str,* "]" : term => do
  let joined := String.join (ss.getElems.toList.map TSyntax.getString)
  return parseLineUpdatesExpr joined

scoped elab "ckpt_line_tree " "[" ss:str,* "]" : term => do
  let joined := String.join (ss.getElems.toList.map TSyntax.getString)
  let (e, _) := parseLineTreeExpr joined.toByteArray 0
  return e

scoped elab "ckpt_hooks " "[" ss:str,* "]" : term => do
  let joined := String.join (ss.getElems.toList.map TSyntax.getString)
  let (e, _) := parseHookTreeExpr joined.toByteArray 0
  return e

scoped elab "ckpt_trace " "[" ss:str,* "]" : term => do
  let joined := String.join (ss.getElems.toList.map TSyntax.getString)
  return parseTraceExpr joined

end ElabHelpers

end Symbolic.BugInjection.Disproofs.Impl.CkptMacro
