/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionObj
public import GeneratedLean.LibsignalSessionPlacedObj
public import LibsignalBinary.Proofs.Placed.Bridge
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Top
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfFrozen
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMultiHelpers
public import ProofLib.Placed.Multi
public import ProofLib.ObjectLoad
public import ProofLib.ProgramReflection
public meta import Lean
public meta import Arm64
public meta import ProofLib.ProgramReflection
public meta import GeneratedLean.LibsignalSessionObj
public meta import GeneratedLean.LibsignalSessionPlacedObj
public meta import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public meta import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMultiHelpers

/-!
# Relocatable `[LibsignalFullPlacement]` Instantiation from `Obj.Loads libsignalSessionImage img`

Constructs `LibsignalFullPlacement`, `LibsignalFrozen`, `LibsignalCodeRoLoaded`, and static/entry
address equalities for any `img : Obj.Image` satisfying `Obj.Loads libsignalSessionImage img`,
by verifying `libsignalSessionLib` at base `0` via `Obj.Interned.checkMultiSliced_spec` and
transporting across page-aligned non-wrapping base shifts `shiftMultiPlacement img.base`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 400000
set_option maxRecDepth 2000000

namespace CryptoVerification.SignalSession.Cli.MainHops.CliImgPlacement

open Arm64
open Arm64.Obj
open ProofLib
open ProofLib.ProgramReflection
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet (entryOf tripleRatchetProgAtExt)
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.ElfFrozen

/-! ## Symbolic Relocation Bytes (`SymByte`) -/

inductive SymByte where
  | lit (v : BitVec 8)
  | rel (target : Nat) (byteIdx : Nat)
  deriving DecidableEq, Inhabited

def evalSymByte (b : BitVec 64) : SymByte → BitVec 8
  | .lit v => v
  | .rel t i => (b + BitVec.ofNat 64 t).extractLsb' (8 * i) 8

def symByteBeq : SymByte → SymByte → Bool
  | .lit v1, .lit v2 => Obj.Interned.bv8Beq v1 v2
  | .rel t1 i1, .rel t2 i2 => Nat.beq t1 t2 && Nat.beq i1 i2
  | _, _ => false

theorem symByteBeq_eq (a b : SymByte) : symByteBeq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [symByteBeq, Obj.Interned.bv8Beq_eq, Nat.beq_eq]

def symRelocBytes (t : Nat) : List SymByte :=
  [.rel t 0, .rel t 1, .rel t 2, .rel t 3, .rel t 4, .rel t 5, .rel t 6, .rel t 7]

theorem map_evalSymByte_symRelocBytes (b : BitVec 64) (t : Nat) :
    (symRelocBytes t).map (evalSymByte b) = bytesLE 8 (b + BitVec.ofNat 64 t) :=
  rfl

def stepSymRaw (k : List (BitVec 8) → List SymByte) : Nat → List (BitVec 8) → List SymByte
  | 0, d => k d
  | _ + 1, [] => k []
  | n + 1, b :: d => .lit b :: stepSymRaw k n d

theorem stepSymRaw_eval (b : BitVec 64) (k : List (BitVec 8) → List SymByte) :
    ∀ (n : Nat) (d : List (BitVec 8)),
      (stepSymRaw k n d).map (evalSymByte b) = d.take n ++ (k (d.drop n)).map (evalSymByte b)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, x :: d => congrArg (x :: ·) (stepSymRaw_eval b k n d)

def stepSymDrop (k : List (BitVec 8) → List SymByte) : Nat → List (BitVec 8) → List SymByte
  | 0, d => k d
  | _ + 1, [] => k []
  | n + 1, _ :: d => stepSymDrop k n d

theorem stepSymDrop_eval (b : BitVec 64) (k : List (BitVec 8) → List SymByte) :
    ∀ (n : Nat) (d : List (BitVec 8)),
      (stepSymDrop k n d).map (evalSymByte b) = (k (d.drop n)).map (evalSymByte b)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, _ :: d => stepSymDrop_eval b k n d

def fastSymPieces : List (BitVec 8) → List Piece → List SymByte
  | _, [] => []
  | d, .raw n :: ps => stepSymRaw (fun d' => fastSymPieces d' ps) n d
  | d, .abs64 t :: ps => stepSymDrop (fun d' => symRelocBytes t ++ fastSymPieces d' ps) 8 d

theorem fastSymPieces_eval (b : BitVec 64) :
    ∀ (ps : List Piece) (d : List (BitVec 8)),
      (fastSymPieces d ps).map (evalSymByte b) = piecesBytes b d ps
  | [], _ => rfl
  | .raw n :: ps, d => by
    simp only [fastSymPieces, piecesBytes, stepSymRaw_eval, fastSymPieces_eval b ps]
  | .abs64 t :: ps, d => by
    simp only [fastSymPieces, piecesBytes, stepSymDrop_eval, List.map_append,
      map_evalSymByte_symRelocBytes, fastSymPieces_eval b ps]

def fastListLen {α : Type} : List α → Nat → Nat
  | [], acc => acc
  | _ :: xs, acc => fastListLen xs (acc + 1)

theorem fastListLen_eq {α : Type} :
    ∀ (xs : List α) (acc : Nat), fastListLen xs acc = xs.length + acc
  | [], acc => by simp [fastListLen]
  | _ :: xs, acc => by simp only [fastListLen, fastListLen_eq xs, List.length_cons]; omega

def fastMergeAux {α : Type} (le : α → α → Bool) : Nat → List α → List α → List α
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | fuel + 1, x :: xs, y :: ys =>
    Bool.casesOn (le x y)
      (y :: fastMergeAux le fuel (x :: xs) ys)
      (x :: fastMergeAux le fuel xs (y :: ys))

theorem fastMergeAux_perm {α : Type} (le : α → α → Bool) :
    ∀ (fuel : Nat) (xs ys : List α),
      List.Perm (fastMergeAux le fuel xs ys) (xs ++ ys)
  | 0, _, _ => List.Perm.refl _
  | _ + 1, [], _ => by simp [fastMergeAux]
  | _ + 1, _ :: _, [] => by simp [fastMergeAux]
  | fuel + 1, x :: xs, y :: ys => by
    unfold fastMergeAux
    cases le x y
    · exact (List.Perm.cons y (fastMergeAux_perm le fuel (x :: xs) ys)).trans List.perm_middle.symm
    · exact List.Perm.cons x (fastMergeAux_perm le fuel xs (y :: ys))

def fastMergePairs {α : Type} (le : α → α → Bool) :
    Option (List α) → List (List α) → List (List α)
  | none, [] => []
  | some xs, [] => [xs]
  | none, xs :: rest => fastMergePairs le (some xs) rest
  | some xs, ys :: rest => fastMergeAux le 16384 xs ys :: fastMergePairs le none rest

theorem fastMergePairs_perm {α : Type} (le : α → α → Bool) :
    ∀ (xss : List (List α)),
      List.Perm (fastMergePairs le none xss).flatten xss.flatten ∧
        ∀ (xs : List α),
          List.Perm (fastMergePairs le (some xs) xss).flatten (xs ++ xss.flatten)
  | [] => ⟨List.Perm.refl _, fun _ => by simp [fastMergePairs]⟩
  | ys :: rest => by
    obtain ⟨ihNone, ihSome⟩ := fastMergePairs_perm le rest
    refine ⟨?_, fun xs => ?_⟩
    · simp only [fastMergePairs, List.flatten_cons]
      exact ihSome ys
    · simp only [fastMergePairs, List.flatten_cons, ← List.append_assoc]
      exact (fastMergeAux_perm le 16384 xs ys).append ihNone

def fastMergeAll {α : Type} (le : α → α → Bool) : Nat → List (List α) → List α
  | 0, xss => xss.flatten
  | fuel + 1, xss =>
    List.casesOn xss [] fun xs rest =>
    List.casesOn rest xs fun ys rest' =>
    fastMergeAll le fuel (fastMergePairs le none (xs :: ys :: rest'))

theorem fastMergeAll_perm {α : Type} (le : α → α → Bool) :
    ∀ (fuel : Nat) (xss : List (List α)),
      List.Perm (fastMergeAll le fuel xss) xss.flatten
  | 0, _ => List.Perm.refl _
  | _ + 1, [] => List.Perm.refl _
  | _ + 1, [_] => by simp [fastMergeAll]
  | fuel + 1, a :: b :: rest =>
    (fastMergeAll_perm le fuel (fastMergePairs le none (a :: b :: rest))).trans
      (fastMergePairs_perm le (a :: b :: rest)).1

theorem flatten_map_singleton {α : Type} :
    ∀ (xs : List α), (xs.map (fun x => [x])).flatten = xs
  | [] => rfl
  | _ :: xs => by simp [flatten_map_singleton xs]

def fastMergeSort {α : Type} (le : α → α → Bool) (xs : List α) : List α :=
  fastMergeAll le 20 (xs.map (fun x => [x]))

theorem fastMergeSort_perm {α : Type} (le : α → α → Bool) (xs : List α) :
    List.Perm (fastMergeSort le xs) xs := by
  unfold fastMergeSort
  simpa only [flatten_map_singleton] using fastMergeAll_perm le 20 (xs.map (fun x => [x]))

def strictSortedBy {α : Type} (key : α → Nat) : List α → Bool
  | [] | [_] => true
  | x :: y :: xs => Nat.blt (key x) (key y) && strictSortedBy key (y :: xs)

theorem strictSortedBy_head_lt {α : Type} (key : α → Nat) :
    ∀ {x y : α} {xs : List α},
      key x < key y → strictSortedBy key (y :: xs) = true →
      ∀ z ∈ y :: xs, key x < key z
  | _, _, [], hxy, _, _, hz => by
    rcases List.mem_cons.mp hz with rfl | hnil
    · exact hxy
    · nomatch hnil
  | _, y, w :: ws, hxy, hw, z, hz => by
    simp only [strictSortedBy, Bool.and_eq_true, Nat.blt_eq] at hw
    rcases List.mem_cons.mp hz with rfl | hzw
    · exact hxy
    · exact strictSortedBy_head_lt key (Nat.lt_trans hxy hw.1) hw.2 z hzw

theorem nodup_of_strictSortedBy {α : Type} (key : α → Nat) :
    ∀ (xs : List α), strictSortedBy key xs = true → xs.Nodup
  | [], _ => .nil
  | [_], _ => .cons (by simp) .nil
  | x :: y :: xs, h => by
    simp only [strictSortedBy, Bool.and_eq_true, Nat.blt_eq] at h
    refine List.Nodup.cons (fun hmem => ?_) (nodup_of_strictSortedBy key (y :: xs) h.2)
    have hlt := strictSortedBy_head_lt key h.1 h.2 x hmem
    omega

private theorem loads_fields {li : LinkedImage} {img : Image} (h : Obj.Loads li img) :
    img.code = li.code ∧
    img.stubs = li.stubs ∧
    img.dataAddr = img.base + BitVec.ofNat 64 li.dataOff ∧
    img.roData = li.roData.map (fun (o, m) => (img.base + BitVec.ofNat 64 o, m)) ∧
    img.base.toNat % 4096 = 0 ∧
    img.base.toNat + li.gotOff + 8 * li.got.length ≤ 2 ^ 64 := by
  obtain ⟨_, _, hal, _, hwrap, himg_eq⟩ := ProofLib.ObjectLoad.load_eq_ok h
  exact ⟨congrArg Image.code himg_eq, congrArg Image.stubs himg_eq,
    congrArg Image.dataAddr himg_eq, congrArg Image.roData himg_eq,
    by simpa only [pageSize] using hal, hwrap⟩

/-! ## Base-`0` Interned Multi-Library and Relocation Witnesses -/

section MetaGenImg0

open Lean Meta Elab Command Term ProofLib.ProgramReflection

private meta def whnfAllM (e : Expr) : MetaM Expr := withTransparency .all (whnf e)

private meta def evalStrLitEp (e : Expr) : MetaM String := do
  if let .lit (.strVal s) := e then return s
  let r ← whnfAllM e
  if let .lit (.strVal s) := r then return s
  let r2 ← withTransparency .all (reduce e)
  if let .lit (.strVal s) := r2 then return s
  throwError "gen_img0_interned: expected String literal, got {r2}"

private meta def mkListExprEp (elemTy : Expr) (elems : Array Expr) : Expr :=
  let nilE := mkApp (Lean.mkConst ``List.nil [Level.zero]) elemTy
  let consFn := mkApp (Lean.mkConst ``List.cons [Level.zero]) elemTy
  elems.foldr (fun x acc => mkApp2 consFn x acc) nilE

private meta def addSafeDefEp (nm : Name) (ty val : Expr) : TermElabM Unit := do
  let env ← getEnv
  addDecl <| Declaration.defnDecl {
    name := nm
    levelParams := []
    type := ty
    value := val
    hints := .regular (getMaxHeight env val + 1)
    safety := .safe
  }
  modifyEnv (addNoncomputable · nm)

private meta def evalNatM (e : Expr) : MetaM Nat := do
  if let .lit (.natVal n) := e then return n
  if let some n := e.rawNatLit? then return n
  let r ← whnfAllM e
  if let .lit (.natVal n) := r then return n
  if let some n := r.rawNatLit? then return n
  let r2 ← withTransparency .all (reduce e)
  if let .lit (.natVal n) := r2 then return n
  if let some n := r2.rawNatLit? then return n
  throwError "gen_img0_interned: expected Nat, got {r2}"

private meta def evalBv8Arr (listE : Expr) : MetaM (Array UInt8) := do
  let elems ← listElemsWhnf listE
  elems.mapM fun e => do
    let e' ← whnfAllM e
    let finE ← whnfAllM (e'.getArg! 1)
    let n ← evalNatM (finE.getArg! 1)
    return n.toUInt8

private meta def word32At (arr : Array UInt8) (off : Nat) : UInt32 :=
  if off + 4 ≤ arr.size then
    arr[off]!.toUInt32 |||
    (arr[off + 1]!.toUInt32 <<< 8) |||
    (arr[off + 2]!.toUInt32 <<< 16) |||
    (arr[off + 3]!.toUInt32 <<< 24)
  else 0

private meta def signExt64 (val : UInt64) (bits : Nat) : Int :=
  let m : UInt64 := 1 <<< (bits - 1).toUInt64
  let v := val &&& ((1 <<< bits.toUInt64) - 1)
  if (v &&& m) != 0 then
    Int.ofNat v.toNat - Int.ofNat (1 <<< bits)
  else
    Int.ofNat v.toNat

private meta def lo12ScaleOf : RelocKind → Option Nat
  | .addLo12 | .ldst8Lo12 => some 0
  | .ldst16Lo12 => some 1
  | .ldst32Lo12 => some 2
  | .ldst64Lo12 | .ld64GotLo12Nc => some 3
  | .ldst128Lo12 => some 4
  | _ => none

private meta def mkBv64Expr (n : Nat) : Expr :=
  mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit n)

private meta def mkBv8Expr (n : Nat) : Expr :=
  mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 8) (mkNatLit n)

private meta def mkCharListExprM (s : String) : Expr :=
  let charTy := Lean.mkConst ``Char
  mkListExprEp charTy (s.toList.toArray.map toExpr)

syntax "gen_img0_interned" : command

elab_rules : command
  | `(command| gen_img0_interned) => liftTermElabM do
  let currNs ← getCurrNamespace
  let lib := CryptoVerification.libsignalSessionMultiLib
  let liE ← whnfAllM (Lean.mkConst ``CryptoVerification.libsignalSessionImage)
  let codeArr ← evalBv8Arr (liE.getArg! 0)
  let dataOff ← evalNatM (liE.getArg! 1)
  let dataBytesArr ← evalBv8Arr (liE.getArg! 2)
  let bss ← evalNatM (liE.getArg! 3)
  let extDataRaw ← listElemsWhnf (liE.getArg! 5)
  let relocsRaw ← listElemsWhnf (liE.getArg! 8)
  let symsRaw ← listElemsWhnf (liE.getArg! 9)
  let objSymsRaw ← listElemsWhnf (liE.getArg! 10)
  let stubsRaw ← listElemsWhnf (liE.getArg! 11)

  let mut symLookup : Std.HashMap String Nat := {}
  for pRaw in symsRaw do
    let p ← whnfAllM pRaw
    symLookup := symLookup.insertIfNew (← evalStrLitEp (p.getArg! 2)) (← evalNatM (p.getArg! 3))
  for opRaw in objSymsRaw do
    let op ← whnfAllM opRaw
    let obj ← evalStrLitEp (op.getArg! 2)
    let osyms ← listElemsWhnf (op.getArg! 3)
    for pRaw in osyms do
      let p ← whnfAllM pRaw
      let s ← evalStrLitEp (p.getArg! 2)
      let o ← evalNatM (p.getArg! 3)
      symLookup := symLookup.insertIfNew s o
      symLookup := symLookup.insertIfNew (obj ++ ":" ++ s) o

  let mut stubMap : Std.HashMap String Nat := {}
  let mut stubByOff : Std.HashMap Nat String := {}
  for pRaw in stubsRaw do
    let p ← whnfAllM pRaw
    let stName ← evalStrLitEp (p.getArg! 2)
    let stOff ← evalNatM (p.getArg! 3)
    stubMap := stubMap.insertIfNew stName stOff
    stubByOff := stubByOff.insertIfNew stOff stName

  let mut extDataMap : Std.HashMap String Nat := {}
  for tRaw in extDataRaw do
    let t ← whnfAllM tRaw
    let s ← evalStrLitEp (t.getArg! 2)
    let p2 ← whnfAllM (t.getArg! 3)
    extDataMap := extDataMap.insertIfNew s (← evalNatM (p2.getArg! 2))

  let mut blkBases : Array Nat := #[]
  for i in [:lib.blocks.length] do
    let b := lib.blocks[i]!
    let (s0, off0) := b.symbols[0]!
    let some a0 := symLookup[s0]? | throwError "gen_img0_interned: missing block {i} symbol {s0}"
    blkBases := blkBases.push (a0 - off0)

  let mut resolvedSym : Std.HashMap String Nat := {}
  for (s, o) in stubMap.toArray do resolvedSym := resolvedSym.insertIfNew s o
  for (s, o) in extDataMap.toArray do resolvedSym := resolvedSym.insertIfNew s o
  for i in [:lib.blocks.length] do
    let base := blkBases[i]!
    for (s, off) in lib.blocks[i]!.symbols do
      resolvedSym := resolvedSym.insertIfNew s (base + off)

  let hookNamesPlaced ← withLocalDeclD `W (Lean.mkConst ``CryptoVerification.SignalSession.CliHooks) fun wE => do
    let rows ← listElemsWhnf (mkApp (Lean.mkConst ``CryptoVerification.SignalSession.cliHookTablePlaced) wE)
    rows.mapM fun row => do let p ← whnfAllM row; evalStrLitEp (p.getArg! 2)
  let hookNamesImg ← withLocalDeclD `W (Lean.mkConst ``CryptoVerification.SignalSession.CliHooks) fun wE => do
    let rows ← listElemsWhnf (mkApp (Lean.mkConst ``CryptoVerification.SignalSession.cliHookTable) wE)
    rows.mapM fun row => do let p ← whnfAllM row; evalStrLitEp (p.getArg! 2)
  for k in [:hookNamesPlaced.size] do
    if let some o := stubMap[hookNamesImg[k]!]? then
      resolvedSym := resolvedSym.insert hookNamesPlaced[k]! o

  let mask26 : UInt32 := (67108863 : Nat).toUInt32
  let adrpMask : UInt32 := (2667577344 : Nat).toUInt32
  let adrpOp : UInt32 := (2415919104 : Nat).toUInt32
  let adrOp : UInt32 := (268435456 : Nat).toUInt32
  let mask19 : UInt32 := (524287 : Nat).toUInt32
  let mask12 : UInt32 := (4095 : Nat).toUInt32
  let mask8 : UInt64 := (255 : Nat).toUInt64

  for i in [:lib.blocks.length] do
    let base := blkBases[i]!
    let b := lib.blocks[i]!
    let mut pages : Std.HashMap (String × Int) Int := {}
    let mut lo12s : Std.HashMap (String × Int) Nat := {}
    for r in b.relocs do
      let place : Int := Int.ofNat (base + r.off)
      let w := word32At codeArr (base + r.off)
      if r.kind == .call26 || r.kind == .jump26 then
        let imm26 := (w &&& mask26).toUInt64
        let delta := signExt64 imm26 26 * 4
        let tgt := place + delta - r.addend
        if tgt ≥ 0 then resolvedSym := resolvedSym.insertIfNew r.sym tgt.toNat
      else if r.kind == .adrpHi21 || r.kind == .adrGotPage then
        if (w &&& adrpMask) == adrpOp then
          let immlo := ((w >>> 29) &&& 3).toUInt64
          let immhi := ((w >>> 5) &&& mask19).toUInt64
          let imm21 := (immhi <<< 2) ||| immlo
          let pageDelta := signExt64 imm21 21 * 4096
          let placePage : Int := Int.ofNat ((base + r.off) / 4096 * 4096)
          pages := pages.insert (r.sym, r.addend) (placePage + pageDelta)
      else if let some sh := lo12ScaleOf r.kind then
        if (w &&& adrpMask) == adrOp then
          let immlo := ((w >>> 29) &&& 3).toUInt64
          let immhi := ((w >>> 5) &&& mask19).toUInt64
          let imm21 := (immhi <<< 2) ||| immlo
          let delta := signExt64 imm21 21
          let tgt := place + delta - r.addend
          if tgt ≥ 0 then resolvedSym := resolvedSym.insertIfNew r.sym tgt.toNat
        else
          let imm12 := ((w >>> 10) &&& mask12).toNat
          lo12s := lo12s.insert (r.sym, r.addend) (imm12 <<< sh)
    for ((sym, addend), pg) in pages.toArray do
      if let some lo := lo12s[(sym, addend)]? then
        let tgt := pg + Int.ofNat lo - addend
        if tgt ≥ 0 then resolvedSym := resolvedSym.insertIfNew sym tgt.toNat

  let mut fullData0 : Array UInt8 := dataBytesArr ++ Array.mk (List.replicate bss (0 : UInt8))
  for rRaw in relocsRaw do
    let r ← whnfAllM rRaw
    let off ← evalNatM (r.getArg! 0)
    let width ← evalNatM (r.getArg! 1)
    let target ← evalNatM (r.getArg! 2)
    let mut v : UInt64 := target.toUInt64
    for bIdx in [:width] do
      if off + bIdx < fullData0.size then
        fullData0 := fullData0.set! (off + bIdx) (v &&& mask8).toUInt8
      v := v >>> 8

  for _ in [:4] do
    for d in lib.data do
      if let some dAddr := resolvedSym[d.sym]? then
        if dAddr ≥ dataOff then
          let dOff := dAddr - dataOff
          for r in d.relocs do
            if r.kind == .abs64 && dOff + r.off + 8 ≤ fullData0.size then
              let mut v : UInt64 := 0
              for bIdx in [:8] do
                v := v ||| (fullData0[dOff + r.off + bIdx]!.toUInt64 <<< (8 * bIdx).toUInt64)
              let tgt := Int.ofNat v.toNat - r.addend
              if tgt ≥ 0 then resolvedSym := resolvedSym.insertIfNew r.sym tgt.toNat

  let mut allNamesSet : Std.HashSet String := {}
  for b in lib.blocks do
    for (s, _) in b.symbols do allNamesSet := allNamesSet.insert s
    for r in b.relocs do allNamesSet := allNamesSet.insert r.sym
    for e in b.externs do allNamesSet := allNamesSet.insert e
    for w in b.weakRefs do allNamesSet := allNamesSet.insert w
  for d in lib.data do
    allNamesSet := allNamesSet.insert d.sym
    for r in d.relocs do allNamesSet := allNamesSet.insert r.sym
  for e in lib.exports do allNamesSet := allNamesSet.insert e
  for (a, b) in lib.exportSyms do
    allNamesSet := allNamesSet.insert a
    allNamesSet := allNamesSet.insert b
  let sortedNames := allNamesSet.toArray.qsort (· < ·)
  let mut symMap : Std.HashMap String Nat := {}
  for idx in [:sortedNames.size] do
    symMap := symMap.insert sortedNames[idx]! idx

  let strTy := Lean.mkConst ``String
  let natTy := Lean.mkConst ``Nat
  let charTy := Lean.mkConst ``Char
  let listCharTy := mkApp (Lean.mkConst ``List [Level.zero]) charTy
  let bv64Ty := mkApp (Lean.mkConst ``BitVec) (mkNatLit 64)
  let bv8Ty := mkApp (Lean.mkConst ``BitVec) (mkNatLit 8)

  let namesExprArr := sortedNames.map mkStrLit
  let lsNamesNm := currNs ++ `lsNames
  addSafeDefEp lsNamesNm (mkApp (Lean.mkConst ``List [Level.zero]) strTy)
    (mkListExprEp strTy namesExprArr)

  let nameCharsArr := sortedNames.map mkCharListExprM
  addSafeDefEp (currNs ++ `lsNameChars)
    (mkApp (Lean.mkConst ``List [Level.zero]) listCharTy)
    (mkListExprEp listCharTy nameCharsArr)

  let addrsExprArr := sortedNames.map fun s => mkBv64Expr (resolvedSym.getD s 0)
  addSafeDefEp (currNs ++ `img0SymAddrs)
    (mkApp (Lean.mkConst ``List [Level.zero]) bv64Ty)
    (mkListExprEp bv64Ty addrsExprArr)

  let basesExprArr := blkBases.map mkBv64Expr
  addSafeDefEp (currNs ++ `img0BlockBases)
    (mkApp (Lean.mkConst ``List [Level.zero]) bv64Ty)
    (mkListExprEp bv64Ty basesExprArr)

  let prodCharsBvTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) listCharTy bv64Ty
  let prodCharsBvMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) listCharTy bv64Ty
  let symCharsArr := lib.exports.toArray.map fun e =>
    let sym := lib.elfSym e
    mkApp2 prodCharsBvMk (mkCharListExprM sym) (mkBv64Expr (resolvedSym.getD e 0))
  addSafeDefEp (currNs ++ `img0SymChars)
    (mkApp (Lean.mkConst ``List [Level.zero]) prodCharsBvTy)
    (mkListExprEp prodCharsBvTy symCharsArr)

  let fullDataExprArr := fullData0.map fun b => mkBv8Expr b.toNat
  addSafeDefEp (currNs ++ `img0FullDataBytes)
    (mkApp (Lean.mkConst ``List [Level.zero]) bv8Ty)
    (mkListExprEp bv8Ty fullDataExprArr)

  let lookupSymIdx (strE : Expr) : MetaM Expr := do
    let s ← evalStrLitEp strE
    let some idx := symMap[s]? | throwError "gen_img0_interned: unknown symbol {s}"
    return mkNatLit idx

  addSafeDefEp (currNs ++ `lsCoinsNextIdx) natTy
    (← lookupSymIdx (Lean.mkConst ``CryptoVerification.SignalSession.Coins.coinsNextSym))
  addSafeDefEp (currNs ++ `lsCoinsLeftIdx) natTy
    (← lookupSymIdx (Lean.mkConst ``CryptoVerification.SignalSession.Coins.coinsLeftSym))
  addSafeDefEp (currNs ++ `lsTokenStorageIdx) natTy
    (← lookupSymIdx (Lean.mkConst ``CryptoVerification.LibsignalSpqrV1.tokenStorageName))
  addSafeDefEp (currNs ++ `lsTokenIdx) natTy
    (← lookupSymIdx (Lean.mkConst ``CryptoVerification.LibsignalSpqrV1.tokenName))
  addSafeDefEp (currNs ++ `lsLogFilterIdx) natTy
    (← lookupSymIdx (Lean.mkConst ``CryptoVerification.lsLogFilterSym))

  let relocTy := Lean.mkConst ``Arm64.Obj.Interned.Reloc
  let relocMk := Lean.mkConst ``Arm64.Obj.Interned.Reloc.mk
  let internRelocs (relocsListE : Expr) : MetaM Expr := do
    let rElems ← listElemsWhnf relocsListE
    let mut out : Array Expr := #[]
    for rRaw in rElems do
      let rE ← whnfAllM rRaw
      let symIdxE ← lookupSymIdx (rE.getArg! 2)
      out := out.push (mkApp5 relocMk (rE.getArg! 0) (rE.getArg! 1) symIdxE (rE.getArg! 3) (rE.getArg! 4))
    return mkListExprEp relocTy out

  let libE ← whnfAllM (Lean.mkConst ``CryptoVerification.libsignalSessionMultiLib)
  let partyAddressName := libE.getArg! 0
  let blocksRaw ← listElemsWhnf (libE.getArg! 1)
  let dataRaw ← listElemsWhnf (libE.getArg! 2)
  let exportsRaw ← listElemsWhnf (libE.getArg! 3)
  let exportSymsRaw ← listElemsWhnf (libE.getArg! 4)

  let b0E ← whnfAllM blocksRaw[0]!
  let extsRaw ← listElemsWhnf (b0E.getArg! 4)
  let mut sharedExtsArr : Array Expr := #[]
  for extStrE in extsRaw do
    sharedExtsArr := sharedExtsArr.push (← lookupSymIdx extStrE)
  let lsSharedExternsNm := currNs ++ `lsSharedExterns
  addSafeDefEp lsSharedExternsNm (mkApp (Lean.mkConst ``List [Level.zero]) natTy)
    (mkListExprEp natTy sharedExtsArr)
  let sharedExtsConst := Lean.mkConst lsSharedExternsNm

  let prodNatNatTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) natTy natTy
  let prodNatNatMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) natTy natTy
  let blkTy := Lean.mkConst ``Arm64.Obj.Interned.Block
  let blkMk := Lean.mkConst ``Arm64.Obj.Interned.Block.mk
  let mut blksArr : Array Expr := #[]
  for bRaw in blocksRaw do
    let bE ← whnfAllM bRaw
    let codeE := bE.getArg! 0
    let alignE := bE.getArg! 1
    let symsRawB ← listElemsWhnf (bE.getArg! 2)
    let mut symsArr : Array Expr := #[]
    for sRaw in symsRawB do
      let sE ← whnfAllM sRaw
      let symIdxE ← lookupSymIdx (sE.getArg! 2)
      symsArr := symsArr.push (mkApp2 prodNatNatMk symIdxE (sE.getArg! 3))
    let symsInternedE := mkListExprEp prodNatNatTy symsArr
    let relocsInternedE ← internRelocs (bE.getArg! 3)
    let weakRefsRaw ← listElemsWhnf (bE.getArg! 5)
    let mut weakRefsArr : Array Expr := #[]
    for wStrE in weakRefsRaw do
      weakRefsArr := weakRefsArr.push (← lookupSymIdx wStrE)
    let weakRefsInternedE := mkListExprEp natTy weakRefsArr
    blksArr := blksArr.push (mkApp6 blkMk codeE alignE symsInternedE relocsInternedE sharedExtsConst weakRefsInternedE)

  let dataTy := Lean.mkConst ``Arm64.Obj.Interned.Data
  let dataMk := Lean.mkConst ``Arm64.Obj.Interned.Data.mk
  let mut dataArr : Array Expr := #[]
  for dRaw in dataRaw do
    let dE ← whnfAllM dRaw
    let symIdxE ← lookupSymIdx (dE.getArg! 0)
    let alignE := dE.getArg! 1
    let roE := dE.getArg! 2
    let bytesE := dE.getArg! 3
    let ztE := dE.getArg! 4
    let relocsInternedE ← internRelocs (dE.getArg! 5)
    dataArr := dataArr.push (mkApp6 dataMk symIdxE alignE roE bytesE ztE relocsInternedE)

  let mut exportsArr : Array Expr := #[]
  for expStrE in exportsRaw do
    exportsArr := exportsArr.push (← lookupSymIdx expStrE)

  let mut exportSymsArr : Array Expr := #[]
  for esRaw in exportSymsRaw do
    let esE ← whnfAllM esRaw
    let kIdxE ← lookupSymIdx (esE.getArg! 2)
    let vIdxE ← lookupSymIdx (esE.getArg! 3)
    exportSymsArr := exportSymsArr.push (mkApp2 prodNatNatMk kIdxE vIdxE)

  let multiLibVal := mkApp6 (Lean.mkConst ``Arm64.Obj.Interned.MultiLib.mk)
    partyAddressName
    (Lean.mkConst lsNamesNm)
    (mkListExprEp blkTy blksArr)
    (mkListExprEp dataTy dataArr)
    (mkListExprEp natTy exportsArr)
    (mkListExprEp prodNatNatTy exportSymsArr)
  addSafeDefEp (currNs ++ `lsInternedMultiLib) (Lean.mkConst ``Arm64.Obj.Interned.MultiLib) multiLibVal

  addSafeDefEp (currNs ++ `lsHookNamesPlaced)
    (mkApp (Lean.mkConst ``List [Level.zero]) strTy)
    (mkListExprEp strTy (hookNamesPlaced.map mkStrLit))
  addSafeDefEp (currNs ++ `lsHookNamesImg)
    (mkApp (Lean.mkConst ``List [Level.zero]) strTy)
    (mkListExprEp strTy (hookNamesImg.map mkStrLit))

  let prodStrNatTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) strTy natTy
  let prodStrNatMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) strTy natTy
  let stubsExprArr ← stubsRaw.mapM fun pRaw => do
    let p ← whnfAllM pRaw
    let s ← evalStrLitEp (p.getArg! 2)
    return mkApp2 prodStrNatMk (mkStrLit s) (p.getArg! 3)
  addSafeDefEp (currNs ++ `lsImgStubs)
    (mkApp (Lean.mkConst ``List [Level.zero]) prodStrNatTy)
    (mkListExprEp prodStrNatTy stubsExprArr)

  let prodStrBvTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) strTy bv64Ty
  let prodStrBvMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) strTy bv64Ty
  let optStrTy := mkApp (Lean.mkConst ``Option [Level.zero]) strTy
  let someStrFn := mkApp (Lean.mkConst ``Option.some [Level.zero]) strTy
  let prodStrOptStrTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) strTy optStrTy
  let prodStrOptStrMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) strTy optStrTy
  let tripleTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) strTy prodStrNatTy
  let tripleMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) strTy prodStrNatTy
  let mut placedStubPairsArr : Array Expr := #[]
  let mut extToImgStubArr : Array Expr := #[]
  let mut extStubTriplesArr : Array Expr := #[]
  let mut placedOffSet : Std.HashSet Nat := {}
  for extStrE in extsRaw do
    let s ← evalStrLitEp extStrE
    let some idx := symMap[s]? | throwError "gen_img0_interned: extern not in symMap: {s}"
    placedStubPairsArr := placedStubPairsArr.push (mkApp2 prodStrBvMk namesExprArr[idx]! addrsExprArr[idx]!)
    let off0 := resolvedSym.getD s 0
    placedOffSet := placedOffSet.insert off0
    let some stNm := stubByOff[off0]?
      | throwError "gen_img0_interned: extern {s} at {off0} missing from stubByOff"
    let stNmLit := mkStrLit stNm
    extToImgStubArr := extToImgStubArr.push (mkApp2 prodStrOptStrMk namesExprArr[idx]! (mkApp someStrFn stNmLit))
    extStubTriplesArr := extStubTriplesArr.push
      (mkApp2 tripleMk namesExprArr[idx]! (mkApp2 prodStrNatMk stNmLit (mkNatLit off0)))
  addSafeDefEp (currNs ++ `lsPlacedStubPairs0)
    (mkApp (Lean.mkConst ``List [Level.zero]) prodStrBvTy)
    (mkListExprEp prodStrBvTy placedStubPairsArr)
  addSafeDefEp (currNs ++ `lsExternToImgStub)
    (mkApp (Lean.mkConst ``List [Level.zero]) prodStrOptStrTy)
    (mkListExprEp prodStrOptStrTy extToImgStubArr)
  Lean.withExporting (isExporting := true) <|
    addSafeDefEp (currNs ++ `lsExternStubTriples)
      (mkApp (Lean.mkConst ``List [Level.zero]) tripleTy)
      (mkListExprEp tripleTy extStubTriplesArr)

  let mut deadStubOffsArr : Array Expr := #[]
  for pRaw in stubsRaw do
    let p ← whnfAllM pRaw
    let stOff ← evalNatM (p.getArg! 3)
    if !placedOffSet.contains stOff then
      deadStubOffsArr := deadStubOffsArr.push (mkNatLit stOff)
  addSafeDefEp (currNs ++ `lsDeadImgStubOffs)
    (mkApp (Lean.mkConst ``List [Level.zero]) natTy)
    (mkListExprEp natTy deadStubOffsArr)

gen_img0_interned

end MetaGenImg0

/-! ## Base-`0` `checkMultiSliced_spec` Verification -/

noncomputable def img0MultiLayout : Obj.Interned.MultiLayout where
  bases := img0BlockBases
  addrs := img0SymAddrs

noncomputable def img0MultiPlacement : MultiPlacement :=
  img0MultiLayout.toMultiPlacement lsInternedMultiLib.names

noncomputable def img0Elf : Process.ElfImage where
  entry := 0#64
  phdrVaddr := 0#64
  phnum := 0
  brkStart := 0#64
  segments := [
    { start := 0#64, perm := Perm.rx, bytes := libsignalSessionImage.code },
    { start := BitVec.ofNat 64 libsignalSessionImage.dataOff, perm := Perm.rw, bytes := img0FullDataBytes }
  ]
  symbols := ProofLib.ProgramReflection.toStringAssoc img0SymChars

theorem ls_names_eq : lsInternedMultiLib.names = lsNameChars.map String.ofList := by
  rfl_kernel

theorem img0Elf_symbols_eq :
    img0Elf.symbols = ProofLib.ProgramReflection.toStringAssoc img0SymChars :=
  rfl

theorem ls_fast_eq :
    libsignalSessionLib = lsInternedMultiLib.toMultiPlacedLibFast lsSharedExterns := by
  rfl_kernel

theorem ls_ids_ok : Obj.Interned.multiIdsOkFast lsInternedMultiLib = true := by
  rfl_kernel

theorem ls_names_len : Nat.blt lsInternedMultiLib.names.length 1048576 = true := by
  rfl_kernel

theorem ls_ext_ok :
    Obj.Interned.blocksSharedExternsOk lsInternedMultiLib lsSharedExterns = true := by
  rfl_kernel

theorem ls_toMultiPlacedLib_eq : libsignalSessionLib = lsInternedMultiLib.toMultiPlacedLib :=
  Obj.Interned.toMultiPlacedLib_of_fast ls_fast_eq ls_ids_ok ls_names_len ls_ext_ok

theorem ls_sharedExterns_lt :
    lsSharedExterns.all (fun idx => Nat.blt idx lsInternedMultiLib.names.length) = true := by
  rfl_kernel

theorem img0_metaCore_ok :
    Obj.Interned.checkMultiMetaCoreFastB lsInternedMultiLib img0MultiLayout lsNameChars = true := by
  rfl_kernel

theorem img0_metaData_ok :
    Obj.Interned.checkMultiMetaDataFastB lsInternedMultiLib img0MultiLayout = true := by
  rfl_kernel

theorem img0_metaExports_ok :
    Obj.Interned.checkMultiMetaExportsFastB lsInternedMultiLib img0MultiLayout
      lsNameChars img0SymChars = true := by
  rfl_kernel

theorem img0_meta_ok :
    Obj.Interned.checkMultiMetaFastB lsInternedMultiLib img0MultiLayout
      lsNameChars img0SymChars = true :=
  Obj.Interned.checkMultiMetaFastB_of_parts img0_metaCore_ok img0_metaData_ok img0_metaExports_ok

theorem img0_dataWalk_ok :
    Obj.Interned.checkMultiDataWalkFastB lsInternedMultiLib img0MultiLayout img0Elf = true := by
  rfl_kernel

theorem img0_blocks_bound :
    Nat.ble lsInternedMultiLib.blocks.length 640 = true := by
  rfl_kernel

theorem img0_textWalk_00 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib img0MultiLayout img0Elf 0 40 = true := by
  rfl_kernel
theorem img0_textWalk_01 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib img0MultiLayout img0Elf 40 40 = true := by
  rfl_kernel
theorem img0_textWalk_02 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib img0MultiLayout img0Elf 80 40 = true := by
  rfl_kernel
theorem img0_textWalk_03 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib img0MultiLayout img0Elf 120 40 = true := by
  rfl_kernel
theorem img0_textWalk_04 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib img0MultiLayout img0Elf 160 40 = true := by
  rfl_kernel
theorem img0_textWalk_05 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib img0MultiLayout img0Elf 200 40 = true := by
  rfl_kernel
theorem img0_textWalk_06 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib img0MultiLayout img0Elf 240 40 = true := by
  rfl_kernel
theorem img0_textWalk_07 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib img0MultiLayout img0Elf 280 40 = true := by
  rfl_kernel
theorem img0_textWalk_08 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib img0MultiLayout img0Elf 320 40 = true := by
  rfl_kernel
theorem img0_textWalk_09 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib img0MultiLayout img0Elf 360 40 = true := by
  rfl_kernel
theorem img0_textWalk_10 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib img0MultiLayout img0Elf 400 40 = true := by
  rfl_kernel
theorem img0_textWalk_11 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib img0MultiLayout img0Elf 440 40 = true := by
  rfl_kernel
theorem img0_textWalk_12 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib img0MultiLayout img0Elf 480 40 = true := by
  rfl_kernel
theorem img0_textWalk_13 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib img0MultiLayout img0Elf 520 40 = true := by
  rfl_kernel
theorem img0_textWalk_14 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib img0MultiLayout img0Elf 560 40 = true := by
  rfl_kernel
theorem img0_textWalk_15 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib img0MultiLayout img0Elf 600 40 = true := by
  rfl_kernel

theorem img0_slicesTextOk :
    Obj.Interned.SlicesTextOk lsInternedMultiLib img0MultiLayout img0Elf 40 640 :=
  ((((((((((((((((Obj.Interned.SlicesTextOk.zero.step
    img0_textWalk_00).step
    img0_textWalk_01).step
    img0_textWalk_02).step
    img0_textWalk_03).step
    img0_textWalk_04).step
    img0_textWalk_05).step
    img0_textWalk_06).step
    img0_textWalk_07).step
    img0_textWalk_08).step
    img0_textWalk_09).step
    img0_textWalk_10).step
    img0_textWalk_11).step
    img0_textWalk_12).step
    img0_textWalk_13).step
    img0_textWalk_14).step
    img0_textWalk_15)

theorem img0_codeMatchesPlaced :
    libsignalSessionLib.Placeable img0MultiPlacement ∧
    libsignalSessionLib.InElf img0Elf img0MultiPlacement ∧
    libsignalSessionLib.DataDisjoint img0MultiPlacement :=
  Obj.Interned.checkMultiSliced_spec ls_toMultiPlacedLib_eq ls_names_eq img0Elf_symbols_eq
    img0_meta_ok img0_dataWalk_ok img0_blocks_bound img0_slicesTextOk

/-! ## Base-Shift Invariance and `LibsignalFullPlacement` from `Obj.Loads` -/

def shiftMultiPlacement (b : BitVec 64) (mpl : MultiPlacement) : MultiPlacement where
  base := fun i => b + mpl.base i
  ρ := fun s => b + mpl.ρ s
  relax := mpl.relax
  b2b := mpl.b2b
  undefWeak := mpl.undefWeak

noncomputable def imgMultiPlacement (img : Obj.Image) : MultiPlacement :=
  shiftMultiPlacement img.base img0MultiPlacement

theorem img0_relax_false (i o : Nat) : img0MultiPlacement.relax i o = false := by
  cases i <;> rfl

theorem img0_b2b_false (i o : Nat) : img0MultiPlacement.b2b i o = false := by
  cases i <;> rfl

theorem img0_undefWeak_false (s : String) : img0MultiPlacement.undefWeak s = false :=
  rfl

def isShiftInvCodeReloc : RelocKind → Bool
  | .call26 | .jump26
  | .adrpHi21 | .adrpHi21Nc | .adrGotPage | .tlsieAdrGottprelPage21
  | .addLo12 | .ldst8Lo12 | .ldst16Lo12 | .ldst32Lo12 | .ldst64Lo12
  | .ld64GotLo12Nc | .tlsieLd64GottprelLo12Nc | .ldst128Lo12
  | .condbr19 | .ldPrelLo19 | .tstbr14 | .adrPrelLo21 | .prel32 => true
  | _ => false

def goShiftBlocks (tBases : Obj.Interned.VecTree (BitVec 64)) (gotOff : Nat) :
    Nat → List Obj.Interned.Block → Bool
  | _, [] => true
  | i, b :: bs =>
    Nat.beq (4096 % b.align) 0 &&
    Nat.beq ((tBases.getD 0#64 i).toNat % 4) 0 &&
    Nat.ble ((tBases.getD 0#64 i).toNat + b.code.length) gotOff &&
    (b.relocs.all fun r => isShiftInvCodeReloc r.kind) &&
    goShiftBlocks tBases gotOff (i + 1) bs

def checkShiftBoundsFast (ML : Obj.Interned.MultiLib) (mly : Obj.Interned.MultiLayout)
    (gotOff : Nat) : Bool :=
  Obj.Interned.withVecTree 0#64 mly.bases fun tBases =>
    Obj.Interned.withVecTree 0#64 mly.addrs fun tAddrs =>
      goShiftBlocks tBases gotOff 0 ML.blocks &&
      (ML.data.all fun d =>
        Nat.beq (4096 % d.align) 0 &&
        Nat.ble ((tAddrs.getD 0#64 d.sym).toNat + d.bytes.length + d.zeroTail) gotOff &&
        (d.relocs.all fun r => r.kind == .abs64))

theorem img0_shiftBounds_ok :
    checkShiftBoundsFast lsInternedMultiLib img0MultiLayout libsignalSessionImage.gotOff = true := by
  rfl_kernel

private theorem bv_add_sub_add_left (b x y : BitVec 64) : (b + x) - (b + y) = x - y := by
  bv_lin

private theorem mask4095_of_mod4096 {b : BitVec 64} (hb : b.toNat % 4096 = 0) :
    b &&& 4095#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (4095#64).toNat = 2 ^ 12 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  simpa using hb

private theorem pageOf_add_aligned {b x : BitVec 64} (hb : b &&& 4095#64 = 0#64) :
    pageOf (b + x) = b + pageOf x := by
  unfold pageOf
  revert hb; bv_bits

private theorem and4095_add_aligned {b x : BitVec 64} (hb : b &&& 4095#64 = 0#64) :
    (b + x) &&& 4095#64 = x &&& 4095#64 := by
  revert hb; bv_bits

private theorem lo12AlignMask_add_aligned {b x : BitVec 64} (hb : b &&& 4095#64 = 0#64)
    (scale : Nat) :
    (b + x) &&& lo12AlignMask scale = x &&& lo12AlignMask scale := by
  rcases scale with _ | _ | _ | _ | _ <;> (unfold lo12AlignMask; revert hb; bv_bits)

private theorem lo12Aligned_add_iff {b x : BitVec 64} (hb : b &&& 4095#64 = 0#64) (scale : Nat) :
    Lo12Aligned scale (b + x) ↔ Lo12Aligned scale x := by
  unfold Lo12Aligned
  rw [lo12AlignMask_add_aligned hb scale]

private theorem lo12Word_add_aligned {b t : BitVec 64} (hb : b &&& 4095#64 = 0#64)
    (scale : Nat) (w : BitVec 32) :
    lo12Word scale w (b + t) = lo12Word scale w t := by
  unfold lo12Word
  rw [and4095_add_aligned hb]

private theorem codeRelocInRange_shift_iff {b p t : BitVec 64} (hb : b &&& 4095#64 = 0#64)
    {k : RelocKind} (hk : isShiftInvCodeReloc k = true) :
    CodeRelocInRange k (b + p) (b + t) ↔ CodeRelocInRange k p t := by
  cases k <;> first | exact absurd hk (by decide) | skip
  all_goals
    dsimp only [CodeRelocInRange, BranchInRange, AdrpInRange, Imm19InRange, TstBr14InRange,
      AdrInRange, Prel32InRange]
    try rw [pageOf_add_aligned hb (x := t), pageOf_add_aligned hb (x := p)]
    try rw [bv_add_sub_add_left]
    try exact lo12Aligned_add_iff hb _
    try exact Iff.rfl

private theorem patchRelocWord_shift_eq {b p t : BitVec 64} (hb : b &&& 4095#64 = 0#64)
    {k : RelocKind} (hk : isShiftInvCodeReloc k = true) (w : BitVec 32) :
    patchRelocWord k w (b + p) (b + t) = patchRelocWord k w p t := by
  cases k <;> first | exact absurd hk (by decide) | skip
  all_goals
    dsimp only [patchRelocWord, branchWord, adrpWord, imm19Word, tstbr14Word, adrWord]
    try rw [pageOf_add_aligned hb (x := t), pageOf_add_aligned hb (x := p)]
    try rw [bv_add_sub_add_left]
    try exact lo12Word_add_aligned hb _ w
    try rfl

theorem resolve_shift (lib : MultiPlacedLib) (b : BitVec 64) (mpl : MultiPlacement) (s : String) :
    lib.resolve (shiftMultiPlacement b mpl) s = b + lib.resolve mpl s := by
  unfold MultiPlacedLib.resolve shiftMultiPlacement
  cases lookupBlockSym s lib.blocks with
  | none => rfl
  | some p => dsimp only; rw [BitVec.add_assoc]

theorem blk_resolve_shift (blk : CodeBlock) (lib : MultiPlacedLib) (b : BitVec 64)
    (mpl : MultiPlacement) (i : Nat) (s : String) :
    blk.resolve (lib.blockPlacement (shiftMultiPlacement b mpl) i) s =
      b + blk.resolve (lib.blockPlacement mpl i) s := by
  unfold CodeBlock.resolve MultiPlacedLib.blockPlacement shiftMultiPlacement
  cases lookup s blk.symbols with
  | none => exact resolve_shift lib b mpl s
  | some off => dsimp only; rw [BitVec.add_assoc]

theorem addSignedAddr_add (b a : BitVec 64) (addend : Int) :
    addSignedAddr (b + a) addend = b + addSignedAddr a addend := by
  unfold addSignedAddr
  cases addend == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.add_assoc]
  · rfl

theorem blk_target_shift (blk : CodeBlock) (lib : MultiPlacedLib) (b : BitVec 64)
    (mpl : MultiPlacement) (i : Nat) (r : RelocEntry) :
    blk.target (lib.blockPlacement (shiftMultiPlacement b mpl) i) r =
      b + blk.target (lib.blockPlacement mpl i) r := by
  unfold CodeBlock.target
  rw [blk_resolve_shift, addSignedAddr_add]

theorem blk_relocTarget_shift (blk : CodeBlock) (lib : MultiPlacedLib) (b : BitVec 64)
    (mpl : MultiPlacement) (i off : Nat) (r : RelocEntry) :
    blk.relocTarget (lib.blockPlacement (shiftMultiPlacement b mpl) i) off r =
      b + blk.relocTarget (lib.blockPlacement mpl i) off r := by
  unfold CodeBlock.relocTarget
  have hb2b : (lib.blockPlacement (shiftMultiPlacement b mpl) i).b2b =
      (lib.blockPlacement mpl i).b2b := rfl
  rw [hb2b]
  cases (if (lib.blockPlacement mpl i).b2b off then blk.b2bNext? r else none) with
  | none => exact blk_target_shift blk lib b mpl i r
  | some r2 => exact blk_target_shift blk lib b mpl i r2

private theorem toNat_add_noWrap {b x : BitVec 64} (h : b.toNat + x.toNat < 2 ^ 64) :
    (b + x).toNat = b.toNat + x.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

private theorem mod_add_of_dvd {a x k : Nat} (ha : a % 4096 = 0) (hk : 4096 % k = 0)
    (hx : x % k = 0) : (a + x) % k = 0 := by
  have hd1 : k ∣ 4096 := Nat.dvd_of_mod_eq_zero hk
  have hd2 : 4096 ∣ a := Nat.dvd_of_mod_eq_zero ha
  have hd3 : k ∣ x := Nat.dvd_of_mod_eq_zero hx
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_trans hd1 hd2) hd3)

theorem got_len_pos : 0 < libsignalSessionImage.got.length :=
  Nat.blt_eq.mp (by rfl_kernel)

theorem bases_len_lt : img0MultiLayout.bases.length < 2 ^ 20 :=
  Nat.blt_eq.mp (by rfl_kernel)

theorem addrs_len_lt : img0MultiLayout.addrs.length < 2 ^ 20 :=
  Nat.blt_eq.mp (by rfl_kernel)

theorem ls_names_nodup : lsInternedMultiLib.names.Nodup := by
  have h : Obj.Interned.namesNodup lsNameChars = true := by rfl_kernel
  exact Obj.Interned.nodup_of_namesNodup ls_names_eq h

private theorem block_props_of_eq {b : Obj.CodeBlock} {bi : Obj.Interned.Block}
    {names : List String} {base : BitVec 64} {gotOff : Nat}
    (heq : b = bi.toCodeBlock names)
    (h1 : 4096 % bi.align = 0)
    (h2 : base.toNat % 4 = 0)
    (h3 : base.toNat + bi.code.length ≤ gotOff)
    (h4 : ∀ r ∈ bi.relocs, isShiftInvCodeReloc r.kind = true) :
    4096 % b.align = 0 ∧
    base.toNat % 4 = 0 ∧
    base.toNat + b.code.length ≤ gotOff ∧
    (∀ r ∈ b.relocs, isShiftInvCodeReloc r.kind = true) := by
  subst heq
  refine ⟨h1, h2, h3, ?_⟩
  intro r hr
  simp only [Obj.Interned.Block.toCodeBlock, List.mem_map] at hr
  obtain ⟨ri, hri, rfl⟩ := hr
  exact h4 ri hri

private theorem extract_shiftBounds_blocks :
    ∀ (i : Nat) (hi : i < libsignalSessionLib.blocks.length),
      4096 % libsignalSessionLib.blocks[i].align = 0 ∧
      (img0MultiPlacement.base i).toNat % 4 = 0 ∧
      (img0MultiPlacement.base i).toNat + libsignalSessionLib.blocks[i].code.length ≤
        libsignalSessionImage.gotOff ∧
      (∀ r ∈ libsignalSessionLib.blocks[i].relocs, isShiftInvCodeReloc r.kind = true) := by
  have hok := img0_shiftBounds_ok
  unfold checkShiftBoundsFast at hok
  simp only [Obj.Interned.withVecTree_eq, Bool.and_eq_true] at hok
  have hgetB := Obj.Interned.toVecTree_getD_all 0#64 img0MultiLayout.bases bases_len_lt
  have hgo : ∀ (k : Nat) (bs : List Obj.Interned.Block),
      goShiftBlocks (Obj.Interned.toVecTree 0#64 img0MultiLayout.bases)
        libsignalSessionImage.gotOff k bs = true →
      ∀ (j : Nat) (hj : j < bs.length),
        4096 % bs[j].align = 0 ∧
        (img0MultiLayout.bases.getD (k + j) 0#64).toNat % 4 = 0 ∧
        (img0MultiLayout.bases.getD (k + j) 0#64).toNat + bs[j].code.length ≤
          libsignalSessionImage.gotOff ∧
        (∀ r ∈ bs[j].relocs, isShiftInvCodeReloc r.kind = true) := by
    intro k bs
    induction bs generalizing k with
    | nil => intro _ j hj; nomatch hj
    | cons b bs ih =>
      intro h j hj
      simp only [goShiftBlocks, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq,
        List.all_eq_true] at h
      cases j with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [hgetB k] at h
        exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2⟩
      | succ j' =>
        have hstep := ih (k + 1) h.2 j' (Nat.lt_of_succ_lt_succ hj)
        have hadd : k + 1 + j' = k + (j' + 1) := by omega
        rw [hadd] at hstep
        simpa only [List.getElem_cons_succ] using hstep
  intro i hi
  have hlen : libsignalSessionLib.blocks.length = lsInternedMultiLib.blocks.length := by
    rw [ls_toMultiPlacedLib_eq]; simp
  have hi' : i < lsInternedMultiLib.blocks.length := hlen ▸ hi
  have hbi := hgo 0 lsInternedMultiLib.blocks hok.1 i hi'
  simp only [Nat.zero_add] at hbi
  have hblk_eq : libsignalSessionLib.blocks[i] =
      (lsInternedMultiLib.blocks[i]'hi').toCodeBlock lsInternedMultiLib.names := by
    have h1 : libsignalSessionLib.blocks[i]? =
        (lsInternedMultiLib.blocks[i]?).map
          (Obj.Interned.Block.toCodeBlock lsInternedMultiLib.names) := by
      rw [ls_toMultiPlacedLib_eq]
      simp [Obj.Interned.MultiLib.toMultiPlacedLib]
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi', Option.map_some,
      Option.some.injEq] at h1
    exact h1
  exact block_props_of_eq hblk_eq hbi.1 hbi.2.1 hbi.2.2.1 hbi.2.2.2

private theorem extract_shiftBounds_data :
    ∀ d ∈ libsignalSessionLib.data,
      4096 % d.align = 0 ∧
      (img0MultiPlacement.ρ d.sym).toNat + d.bytes.length + d.zeroTail ≤
        libsignalSessionImage.gotOff ∧
      (∀ r ∈ d.relocs, r.kind = .abs64) := by
  have hok := img0_shiftBounds_ok
  unfold checkShiftBoundsFast at hok
  simp only [Obj.Interned.withVecTree_eq, Bool.and_eq_true, List.all_eq_true,
    Nat.beq_eq, Nat.ble_eq, beq_iff_eq] at hok
  have hgetA := Obj.Interned.toVecTree_getD_all 0#64 img0MultiLayout.addrs addrs_len_lt
  have hgetN := Obj.Interned.toVecTree_getD_all "" lsInternedMultiLib.names
    (by have h := ls_names_len; rw [Nat.blt_eq] at h; exact h)
  have hids := ls_ids_ok
  unfold Obj.Interned.multiIdsOkFast at hids
  simp only [Obj.Interned.withNat_eq, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at hids
  intro d hd
  rw [ls_fast_eq] at hd
  simp only [Obj.Interned.MultiLib.toMultiPlacedLibFast, Obj.Interned.withVecTree_eq, List.mem_map] at hd
  obtain ⟨di, hdi, rfl⟩ := hd
  have hd_ok := hok.2 di hdi
  have hdsym_lt : di.sym < lsInternedMultiLib.names.length := (hids.2 di hdi).1
  have hidx : lsInternedMultiLib.names.idxOf
      ((Obj.Interned.toVecTree "" lsInternedMultiLib.names).getD "" di.sym) = di.sym := by
    rw [hgetN di.sym]
    exact Obj.Interned.idxOf_getD ls_names_nodup hdsym_lt
  refine ⟨hd_ok.1.1, ?_, ?_⟩
  · simp only [Obj.Interned.Data.toInfoTree, img0MultiPlacement,
      Obj.Interned.MultiLayout.toMultiPlacement, hidx]
    rw [← hgetA di.sym]
    exact hd_ok.1.2
  · intro r hr
    simp only [Obj.Interned.Data.toInfoTree, List.mem_map] at hr
    obtain ⟨ri, hri, rfl⟩ := hr
    exact hd_ok.2 ri hri

theorem blk_patchedWord_shift {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (i : Nat) (hi : i < libsignalSessionLib.blocks.length) (off : Nat) :
    let blk := libsignalSessionLib.blocks[i]
    blk.patchedWord (libsignalSessionLib.blockPlacement (imgMultiPlacement img) i) off =
      blk.patchedWord (libsignalSessionLib.blockPlacement img0MultiPlacement i) off := by
  have hb_mask : img.base &&& 4095#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hsb := (extract_shiftBounds_blocks i hi).2.2.2
  dsimp only [imgMultiPlacement]
  unfold CodeBlock.patchedWord CodeBlock.relaxedAt
  have hrx : ∀ k, (libsignalSessionLib.blockPlacement (shiftMultiPlacement img.base img0MultiPlacement) i).relax k =
      false := fun k => img0_relax_false i k
  have hrx0 : ∀ k, (libsignalSessionLib.blockPlacement img0MultiPlacement i).relax k = false :=
    fun k => img0_relax_false i k
  have huw : ∀ s, (libsignalSessionLib.blockPlacement (shiftMultiPlacement img.base img0MultiPlacement) i).undefWeak s =
      false := img0_undefWeak_false
  have huw0 : ∀ s, (libsignalSessionLib.blockPlacement img0MultiPlacement i).undefWeak s = false :=
    img0_undefWeak_false
  cases hrel : libsignalSessionLib.blocks[i].relocAt? off with
  | none => rfl
  | some r =>
    have hmem : r ∈ libsignalSessionLib.blocks[i].relocs :=
      List.mem_of_find?_eq_some hrel
    have hkind := hsb r hmem
    simp only [hrx, hrx0, Bool.and_false, CodeBlock.undefWeakBranch, huw, huw0]
    have hpl : (libsignalSessionLib.blockPlacement (shiftMultiPlacement img.base img0MultiPlacement) i).base +
        BitVec.ofNat 64 off =
        img.base + ((libsignalSessionLib.blockPlacement img0MultiPlacement i).base + BitVec.ofNat 64 off) := by
      dsimp only [MultiPlacedLib.blockPlacement, shiftMultiPlacement]
      rw [BitVec.add_assoc]
    rw [hpl, blk_relocTarget_shift]
    exact patchRelocWord_shift_eq hb_mask hkind _

theorem blk_patched_shift {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (i : Nat) (hi : i < libsignalSessionLib.blocks.length) :
    let blk := libsignalSessionLib.blocks[i]
    blk.patched (libsignalSessionLib.blockPlacement (imgMultiPlacement img) i) =
      blk.patched (libsignalSessionLib.blockPlacement img0MultiPlacement i) := by
  dsimp only [CodeBlock.patched]
  refine List.flatMap_congr fun j _ => ?_
  rw [blk_patchedWord_shift himg i hi (4 * j)]

private theorem relocInRange_eq_of_relax_false (blk : CodeBlock) (pl : Placement)
    (hrx : ∀ k, pl.relax k = false) (kind : RelocKind) (off : Nat)
    (place target : BitVec 64) :
    blk.relocInRange pl kind off place target ↔ CodeRelocInRange kind place target := by
  cases kind <;> simp [CodeBlock.relocInRange, CodeRelocInRange, hrx]

theorem img_placeable {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img) :
    libsignalSessionLib.Placeable (imgMultiPlacement img) := by
  have hpl0 := img0_codeMatchesPlaced.1
  obtain ⟨-, -, -, -, hal', hwrap⟩ := loads_fields himg
  have hgot_pos := got_len_pos
  have hb_got : img.base.toNat + libsignalSessionImage.gotOff < 2 ^ 64 := by omega
  have hb_mask : img.base &&& 4095#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  refine {
    blocks_ok := fun i hi => ?_
    blocks_disjoint := fun i j hi hj hij => ?_
    symbols_nodup := hpl0.symbols_nodup
    data_nodup := hpl0.data_nodup
    data_ok := fun d hd => ?_
    data_relocs_ok := fun d hd r hr => ?_
  }
  · have hb0 := hpl0.blocks_ok i hi
    obtain ⟨hal_b, _, hle_b, hrel_b⟩ := extract_shiftBounds_blocks i hi
    have hbase_nw : (img.base + img0MultiPlacement.base i).toNat =
        img.base.toNat + (img0MultiPlacement.base i).toNat :=
      toNat_add_noWrap (by omega)
    refine {
      align_pos := hb0.align_pos
      base_aligned := by
        dsimp only [MultiPlacedLib.blockPlacement, imgMultiPlacement, shiftMultiPlacement]
        rw [hbase_nw]
        exact mod_add_of_dvd hal' hal_b hb0.base_aligned
      no_wrap := by
        dsimp only [MultiPlacedLib.blockPlacement, imgMultiPlacement, shiftMultiPlacement]
        rw [hbase_nw]; omega
      len_aligned := hb0.len_aligned
      relocs_nodup := hb0.relocs_nodup
      relocs_ok := fun r hr => ?_
      relaxed_ok := fun off r hrx _ => by
        unfold CodeBlock.relaxedAt at hrx
        have : (libsignalSessionLib.blockPlacement (imgMultiPlacement img) i).relax off = false :=
          img0_relax_false i off
        simp [this] at hrx
      symbols_ok := hb0.symbols_ok
      externs_ok := fun e he => ?_
    }
    · obtain ⟨ho4, holen, hrr0⟩ := hb0.relocs_ok r hr
      refine ⟨ho4, holen, ?_⟩
      have hkind := hrel_b r hr
      have hpl_add : (libsignalSessionLib.blockPlacement (imgMultiPlacement img) i).base +
          BitVec.ofNat 64 r.off =
          img.base + ((libsignalSessionLib.blockPlacement img0MultiPlacement i).base + BitVec.ofNat 64 r.off) := by
        dsimp only [MultiPlacedLib.blockPlacement, imgMultiPlacement, shiftMultiPlacement]
        rw [BitVec.add_assoc]
      have hrx : ∀ k, (libsignalSessionLib.blockPlacement (imgMultiPlacement img) i).relax k = false :=
        fun k => img0_relax_false i k
      have hrx0 : ∀ k, (libsignalSessionLib.blockPlacement img0MultiPlacement i).relax k = false :=
        fun k => img0_relax_false i k
      rw [hpl_add, relocInRange_eq_of_relax_false _ _ hrx]
      dsimp only [imgMultiPlacement]
      rw [blk_relocTarget_shift]
      rw [relocInRange_eq_of_relax_false _ _ hrx0] at hrr0
      exact (codeRelocInRange_shift_iff hb_mask hkind).mpr hrr0
    · obtain ⟨hlk, hext0⟩ := hb0.externs_ok e he
      refine ⟨hlk, ?_⟩
      dsimp only [MultiPlacedLib.blockPlacement, imgMultiPlacement]
      rw [resolve_shift]
      change _ ≤ ((img.base + _) - (img.base + _)).toNat
      rw [bv_add_sub_add_left]
      exact hext0
  · have hdisj0 := hpl0.blocks_disjoint i j hi hj hij
    obtain ⟨_, _, hle_i, _⟩ := extract_shiftBounds_blocks i hi
    obtain ⟨_, _, hle_j, _⟩ := extract_shiftBounds_blocks j hj
    dsimp only [imgMultiPlacement, shiftMultiPlacement]
    rw [toNat_add_noWrap (by omega), toNat_add_noWrap (by omega)]
    unfold RangesDisjoint at hdisj0 ⊢
    omega
  · obtain ⟨hnone, hal_pos, hal_d0, _⟩ := hpl0.data_ok d hd
    obtain ⟨hal_d, hle_d, _⟩ := extract_shiftBounds_data d hd
    have hnw_d : (img.base + img0MultiPlacement.ρ d.sym).toNat =
        img.base.toNat + (img0MultiPlacement.ρ d.sym).toNat :=
      toNat_add_noWrap (by omega)
    refine ⟨hnone, hal_pos, ?_, ?_⟩
    · dsimp only [imgMultiPlacement, shiftMultiPlacement]
      rw [hnw_d]
      exact mod_add_of_dvd hal' hal_d hal_d0
    · dsimp only [imgMultiPlacement, shiftMultiPlacement]
      rw [hnw_d]; omega
  · obtain ⟨hw_pos, hw_le, _, _⟩ := hpl0.data_relocs_ok d hd r hr
    have hk_abs := (extract_shiftBounds_data d hd).2.2 r hr
    refine ⟨hw_pos, hw_le, ?_, ?_⟩
    · intro h32; rw [hk_abs] at h32; nomatch h32
    · intro hp32; rw [hk_abs] at hp32; nomatch hp32

private theorem img0_externs_nodup_check :
    strictSortedBy BitVec.toNat
      (fastMergeSort (fun a b => Nat.ble a.toNat b.toNat) (lsPlacedStubPairs0.map Prod.snd)) =
      true := by
  rfl_kernel

private theorem ls_sharedExterns_eq_tree :
    libsignalSessionExterns =
      Obj.Interned.withVecTree "" lsInternedMultiLib.names
        (fun t => lsSharedExterns.map (fun idx => t.getD "" idx)) := by
  rfl_kernel

private theorem lsPlacedStubPairs0_snd_eq_tree :
    lsPlacedStubPairs0.map Prod.snd =
      Obj.Interned.withVecTree 0#64 img0MultiLayout.addrs
        (fun t => lsSharedExterns.map (fun idx => t.getD 0#64 idx)) := by
  rfl_kernel

private theorem lsPlacedStubPairs0_snd_eq :
    lsPlacedStubPairs0.map Prod.snd = libsignalSessionExterns.map img0MultiPlacement.ρ := by
  have hn_lt : lsInternedMultiLib.names.length < 2 ^ 20 := Nat.blt_eq.mp ls_names_len
  have hgetN := Obj.Interned.toVecTree_getD_all "" lsInternedMultiLib.names hn_lt
  have hgetA := Obj.Interned.toVecTree_getD_all 0#64 img0MultiLayout.addrs addrs_len_lt
  rw [lsPlacedStubPairs0_snd_eq_tree, ls_sharedExterns_eq_tree]
  simp only [Obj.Interned.withVecTree_eq, List.map_map]
  refine List.map_congr_left fun idx hidx => ?_
  dsimp only [Function.comp_def, img0MultiPlacement, Obj.Interned.MultiLayout.toMultiPlacement]
  have hlt : idx < lsInternedMultiLib.names.length :=
    Nat.blt_eq.mp (List.all_eq_true.mp ls_sharedExterns_lt idx hidx)
  rw [hgetN idx, Obj.Interned.idxOf_getD ls_names_nodup hlt, hgetA idx]

theorem img0_externs_nodup :
    (libsignalSessionExterns.map img0MultiPlacement.ρ).Nodup := by
  rw [← lsPlacedStubPairs0_snd_eq]
  exact (List.Perm.nodup_iff (fastMergeSort_perm _ _)).mp
    (nodup_of_strictSortedBy BitVec.toNat _ img0_externs_nodup_check)

theorem img_externs_nodup (img : Obj.Image) :
    (libsignalSessionExterns.map (imgMultiPlacement img).ρ).Nodup := by
  have heq : libsignalSessionExterns.map (imgMultiPlacement img).ρ =
      (libsignalSessionExterns.map img0MultiPlacement.ρ).map (img.base + ·) := by
    simp [List.map_map, Function.comp_def, imgMultiPlacement, shiftMultiPlacement]
  rw [heq]
  refine List.Nodup.map (fun a b hab => ?_) img0_externs_nodup
  have hsub := congrArg (· - img.base) hab
  rw [show (img.base + a) - img.base = a by bv_lin,
      show (img.base + b) - img.base = b by bv_lin] at hsub
  exact hsub

/-- Canonical `[LibsignalFullPlacement]` constructed from `Obj.Loads libsignalSessionImage img`. -/
@[instance_reducible]
noncomputable def instLibsignalFullPlacementOfLoads (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img) : LibsignalFullPlacement :=
  LibsignalFullPlacement.ofPlaceable (imgMultiPlacement img) (img_placeable himg)
    (img_externs_nodup img)

/-! ## `LibsignalFrozen` from `img.FrozenLoaded` -/

theorem img_codeLoaded {img : Obj.Image} {s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hf : img.FrozenLoaded s) :
    libsignalSessionLib.CodeLoaded (imgMultiPlacement img) s.mem := by
  obtain ⟨hcode_eq, -, -, -, hal', hwrap⟩ := loads_fields himg
  have hgot_pos := got_len_pos
  have hb_got : img.base.toNat + libsignalSessionImage.gotOff < 2 ^ 64 := by omega
  have hcl_img := (Image.frozenLoaded_iff.mp hf).1
  obtain ⟨_, _, hholds_img⟩ := Program.codeLoaded_iff.mp hcl_img
  dsimp only [Program.ofImageWithSvc, Program.ofImage] at hholds_img
  rw [hcode_eq] at hholds_img
  intro i hi
  have hin0 := img0_codeMatchesPlaced.2.1.blocks i hi
  have hpl_i := (img_placeable himg).blocks_ok i hi
  obtain ⟨_, hb0_mod4, hle_i, _⟩ := extract_shiftBounds_blocks i hi
  have hlen_patched :
      (libsignalSessionLib.blocks[i].patched
        (libsignalSessionLib.blockPlacement (imgMultiPlacement img) i)).length =
      libsignalSessionLib.blocks[i].code.length := by
    rw [blk_patched_shift himg i hi]
    unfold CodeBlock.patched
    have h4 := (img0_codeMatchesPlaced.1.blocks_ok i hi).len_aligned
    have hlen_map : ∀ n (f : Nat → List (BitVec 8)), (∀ j, (f j).length = 4) →
        ((List.range n).flatMap f).length = 4 * n := by
      intro n f hf4
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [List.range_succ, List.flatMap_append, List.length_append, ih,
          List.flatMap_singleton, hf4 n]
        omega
    rw [hlen_map _ _ (fun _ => by simp [bytesOfWordLE, bytesLE])]
    omega
  refine Program.codeLoaded_iff.mpr ⟨?_, ?_, ?_⟩
  · dsimp only [MultiPlacedLib.blockProgram, PlacedLib.program, MultiPlacedLib.blockPlacement,
      imgMultiPlacement, shiftMultiPlacement]
    rw [toNat_add_noWrap (by omega)]
    exact mod_add_of_dvd hal' (by decide : 4096 % 4 = 0) hb0_mod4
  · dsimp only [MultiPlacedLib.blockProgram, PlacedLib.program, MultiPlacedLib.blockLib]
    rw [Obj.Interned.getD_of_lt (d := { code := [] }) hi, hlen_patched]
    exact hpl_i.no_wrap
  · dsimp only [MultiPlacedLib.blockProgram, PlacedLib.program, MultiPlacedLib.blockLib]
    rw [Obj.Interned.getD_of_lt (d := { code := [] }) hi, blk_patched_shift himg i hi]
    dsimp only [MultiPlacedLib.blockPlacement, imgMultiPlacement, shiftMultiPlacement]
    intro k hk
    have hlen0 : (libsignalSessionLib.blocks[i].patched
        (libsignalSessionLib.blockPlacement img0MultiPlacement i)).length =
        libsignalSessionLib.blocks[i].code.length := by
      rw [← blk_patched_shift himg i hi]; exact hlen_patched
    have hk_code : k < libsignalSessionLib.blocks[i].code.length := hlen0 ▸ hk
    obtain ⟨p, hcell, hp_rx⟩ := hin0 k hk
    have had_tn : (img0MultiPlacement.base i + BitVec.ofNat 64 k).toNat =
        (img0MultiPlacement.base i).toNat + k := by
      rw [toNat_add_noWrap (by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        omega)]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    by_cases hidx_lt : (img0MultiPlacement.base i).toNat + k < libsignalSessionImage.code.length
    · unfold img0Elf Snapshot.cellAt at hcell
      simp only [List.findSome?_cons, BitVec.sub_zero, had_tn, dite_eq_left hidx_lt,
        Option.some.injEq, Prod.mk.injEq] at hcell
      have haddr_eq : img.base + img0MultiPlacement.base i + BitVec.ofNat 64 k =
          img.base + BitVec.ofNat 64 ((img0MultiPlacement.base i).toNat + k) := by
        rw [BitVec.add_assoc]
        congr 1
        apply BitVec.eq_of_toNat_eq
        rw [had_tn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hh := hholds_img ((img0MultiPlacement.base i).toNat + k) hidx_lt
      rw [← haddr_eq, hcell.2] at hh
      exact hh
    · unfold img0Elf Snapshot.cellAt at hcell
      simp only [List.findSome?_cons, List.findSome?_nil, BitVec.sub_zero, had_tn,
        dite_eq_right hidx_lt] at hcell
      by_cases hd_lt : ((img0MultiPlacement.base i + BitVec.ofNat 64 k) -
          BitVec.ofNat 64 libsignalSessionImage.dataOff).toNat < img0FullDataBytes.length
      · simp only [dite_eq_left hd_lt, Option.some.injEq, Prod.mk.injEq] at hcell
        rw [← hcell.1] at hp_rx
        nomatch hp_rx
      · simp only [dite_eq_right hd_lt] at hcell
        nomatch hcell

def sortRelocs (rs : List Obj.DataReloc) : List Obj.DataReloc :=
  fastMergeSort (fun x y => Nat.ble x.off y.off) rs

theorem sortRelocs_perm (rs : List Obj.DataReloc) :
    List.Perm (sortRelocs rs) rs := by
  unfold sortRelocs
  exact fastMergeSort_perm (fun x y => Nat.ble x.off y.off) rs

def allRelocsFrom (lo dataLen : Nat) : List Obj.DataReloc → Bool
  | [] => true
  | r :: rs =>
    Bool.and (Nat.ble lo r.off)
      (Bool.and (Nat.ble (r.off + r.width) dataLen) (allRelocsFrom lo dataLen rs))

theorem allRelocsFrom_spec {lo dataLen : Nat} :
    ∀ {rs : List Obj.DataReloc},
      allRelocsFrom lo dataLen rs = true →
      ∀ r ∈ rs, lo ≤ r.off ∧ r.off + r.width ≤ dataLen
  | [], _, _, hr => by cases hr
  | _ :: _, h, r, hr => by
    simp only [allRelocsFrom, Bool.and_eq_true, Nat.ble_eq] at h
    rcases List.mem_cons.mp hr with rfl | hmem
    · exact ⟨h.1, h.2.1⟩
    · exact allRelocsFrom_spec h.2.2 r hmem

def sortedRoRelocs (endOff dataLen : Nat) : Nat → List Obj.DataReloc → Bool
  | cur, [] => Nat.ble cur endOff
  | cur, r :: rs =>
    Bool.casesOn (Nat.ble (r.off + 1) endOff)
      (Bool.and (Nat.ble cur endOff) (allRelocsFrom endOff dataLen (r :: rs)))
      (Bool.and (Nat.ble cur r.off)
        (Bool.and (Nat.beq r.width 8)
          (Bool.and (Nat.ble (r.off + 8) endOff)
            (Bool.and (Nat.ble (r.off + 8) dataLen)
              (sortedRoRelocs endOff dataLen (r.off + 8) rs)))))

theorem sortedRoRelocs_all_ge {endOff dataLen : Nat} :
    ∀ {cur : Nat} {rs : List Obj.DataReloc},
      sortedRoRelocs endOff dataLen cur rs = true →
      ∀ r ∈ rs, cur ≤ r.off ∧ r.off + r.width ≤ dataLen
  | _, [], _, _, hr => by cases hr
  | cur, r0 :: rs, h, r, hr => by
    revert h
    unfold sortedRoRelocs
    cases Nat.ble (r0.off + 1) endOff <;> intro h
    · simp only [Bool.and_eq_true, Nat.ble_eq] at h
      have hall := allRelocsFrom_spec h.2 r hr
      exact ⟨by omega, hall.2⟩
    · simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
      obtain ⟨hcur, hw, _, hd, htail⟩ := h
      rcases List.mem_cons.mp hr with rfl | hmem
      · exact ⟨hcur, by omega⟩
      · obtain ⟨hge, hbd⟩ := sortedRoRelocs_all_ge htail r hmem
        exact ⟨by omega, hbd⟩

def buildRoPieces (endOff : Nat) : Nat → List Obj.DataReloc → List Piece
  | cur, [] => [.raw (endOff - cur)]
  | cur, r :: rs =>
    Bool.casesOn (Nat.ble (r.off + 1) endOff)
      [.raw (endOff - cur)]
      (.raw (r.off - cur) :: .abs64 r.target :: buildRoPieces endOff (r.off + 8) rs)

theorem piecesLen_buildRoPieces {endOff dataLen : Nat} :
    ∀ {cur : Nat} {rs : List Obj.DataReloc},
      sortedRoRelocs endOff dataLen cur rs = true →
      piecesLen (buildRoPieces endOff cur rs) = endOff - cur
  | cur, [], _ => by
    simp only [buildRoPieces, piecesLen]; omega
  | cur, r :: rs, h => by
    revert h
    unfold sortedRoRelocs buildRoPieces
    cases Nat.ble (r.off + 1) endOff <;> intro h
    · simp only [piecesLen]; omega
    · simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
      obtain ⟨hcur, _, hend, _, htail⟩ := h
      simp only [piecesLen]
      rw [piecesLen_buildRoPieces htail]
      omega

private theorem reloc64At_append_cons {dataLen : Nat} (r : Obj.DataReloc) (rs : List Obj.DataReloc)
    (hr_bd : r.off + r.width ≤ dataLen) (hr_w : r.width = 8)
    (hno : ProofLib.ObjectLoad.noRelocInRange rs dataLen r.off 8 = true) :
    ∀ (pre : List Obj.DataReloc),
      (∀ p ∈ pre, p.off + p.width ≤ dataLen) →
      CryptoProofLib.RoDataReloc.reloc64At (pre ++ r :: rs) dataLen r.off r.target = true
  | [], _ => by
    simp only [List.nil_append, CryptoProofLib.RoDataReloc.reloc64At,
      Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨hr_bd, Or.inl ⟨⟨trivial, hr_w, trivial⟩, hno⟩⟩
  | p :: pre, hpre => by
    simp only [List.cons_append, CryptoProofLib.RoDataReloc.reloc64At,
      Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨hpre p (by simp),
      Or.inr (reloc64At_append_cons r rs hr_bd hr_w hno pre (fun q hq => hpre q (by simp [hq])))⟩

private theorem piecesOk_buildRoPieces_perm {endOff dataLen : Nat} {allRs : List Obj.DataReloc} :
    ∀ (suf pre : List Obj.DataReloc) (cur : Nat),
      List.Perm (pre ++ suf) allRs →
      (∀ p ∈ pre, p.off + p.width ≤ cur ∧ p.off + p.width ≤ dataLen) →
      sortedRoRelocs endOff dataLen cur suf = true →
      piecesOk allRs dataLen cur (buildRoPieces endOff cur suf) = true
  | [], pre, cur, hperm, hpre, _ => by
    simp only [buildRoPieces, piecesOk, Bool.and_true,
      ProofLib.ObjectLoad.noRelocInRange, List.all_eq_true, decide_eq_true_eq]
    intro q hq
    have hq' : q ∈ pre := by
      have hm := hperm.symm.subset hq
      rwa [List.append_nil] at hm
    exact ⟨(hpre q hq').2, Or.inl (hpre q hq').1⟩
  | r :: rs, pre, cur, hperm, hpre, hsuf => by
    revert hsuf
    unfold sortedRoRelocs buildRoPieces
    cases Nat.ble (r.off + 1) endOff <;> intro hsuf
    · simp only [Bool.and_eq_true, Nat.ble_eq] at hsuf
      simp only [piecesOk, Bool.and_true,
        ProofLib.ObjectLoad.noRelocInRange, List.all_eq_true, decide_eq_true_eq]
      intro q hq
      rcases List.mem_append.mp (hperm.symm.subset hq) with hqp | hqs
      · exact ⟨(hpre q hqp).2, Or.inl (hpre q hqp).1⟩
      · obtain ⟨hge, hbd⟩ := allRelocsFrom_spec hsuf.2 q hqs
        exact ⟨hbd, Or.inr (by omega)⟩
    · simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at hsuf
      obtain ⟨hcur, hrw, _, hrd, htail⟩ := hsuf
      have hrs_ge := sortedRoRelocs_all_ge htail
      have hno1 :
          ProofLib.ObjectLoad.noRelocInRange allRs dataLen cur (r.off - cur) = true := by
        simp only [ProofLib.ObjectLoad.noRelocInRange, List.all_eq_true, decide_eq_true_eq]
        intro q hq
        rcases List.mem_append.mp (hperm.symm.subset hq) with hqp | hqs
        · exact ⟨(hpre q hqp).2, Or.inl (hpre q hqp).1⟩
        · rcases List.mem_cons.mp hqs with rfl | hqrs
          · exact ⟨by omega, Or.inr (by omega)⟩
          · obtain ⟨hge, hbd⟩ := hrs_ge q hqrs
            exact ⟨hbd, Or.inr (by omega)⟩
      have hr_in : r ∈ allRs := hperm.subset (by simp)
      obtain ⟨aPre, aSuf, hall_eq⟩ := List.append_of_mem hr_in
      have hrest : List.Perm (pre ++ rs) (aPre ++ aSuf) := by
        have hp1 : List.Perm (pre ++ r :: rs) (aPre ++ r :: aSuf) := hall_eq ▸ hperm
        exact (List.perm_middle.symm.trans (hp1.trans List.perm_middle)).cons_inv
      have hno_aSuf : ProofLib.ObjectLoad.noRelocInRange aSuf dataLen r.off 8 = true := by
        simp only [ProofLib.ObjectLoad.noRelocInRange, List.all_eq_true, decide_eq_true_eq]
        intro q hq
        rcases List.mem_append.mp (hrest.symm.subset (List.mem_append.mpr (Or.inr hq))) with
          hqp | hqrs
        · have h1 := (hpre q hqp).1
          exact ⟨(hpre q hqp).2, Or.inl (by omega)⟩
        · obtain ⟨hge, hbd⟩ := hrs_ge q hqrs
          exact ⟨hbd, Or.inr hge⟩
      have haPre_bd : ∀ p ∈ aPre, p.off + p.width ≤ dataLen := by
        intro p hp
        rcases List.mem_append.mp (hrest.symm.subset (List.mem_append.mpr (Or.inl hp))) with
          hpp | hprs
        · exact (hpre p hpp).2
        · exact (hrs_ge p hprs).2
      have hrel :
          CryptoProofLib.RoDataReloc.reloc64At allRs dataLen r.off r.target = true := by
        rw [hall_eq]
        exact reloc64At_append_cons r aSuf (by omega) hrw hno_aSuf aPre haPre_bd
      have hadd : cur + (r.off - cur) = r.off := by omega
      have hperm' : List.Perm ((pre ++ [r]) ++ rs) allRs := by
        simpa only [List.append_assoc, List.singleton_append] using hperm
      have hpre' :
          ∀ p ∈ pre ++ [r], p.off + p.width ≤ r.off + 8 ∧ p.off + p.width ≤ dataLen := by
        intro p hp
        rcases List.mem_append.mp hp with hpp | hpr
        · obtain ⟨h1, h2⟩ := hpre p hpp
          exact ⟨by omega, h2⟩
        · simp only [List.mem_singleton] at hpr
          subst hpr
          exact ⟨by omega, by omega⟩
      simp only [piecesOk, hadd, hno1, hrel, Bool.true_and]
      exact piecesOk_buildRoPieces_perm rs (pre ++ [r]) (r.off + 8) hperm' hpre' htail

noncomputable def lsSortedRelocs : List Obj.DataReloc :=
  sortRelocs libsignalSessionImage.relocs

theorem lsDataLen_eq : libsignalSessionImage.data.length = 69720 := by
  have h : fastListLen libsignalSessionImage.data 0 = 69720 := by rfl_kernel
  simpa [fastListLen_eq] using h

theorem lsBss_eq : libsignalSessionImage.bss = 8 := by rfl_kernel

theorem lsSortedAllRelocs_ok : sortedRoRelocs 69728 69728 0 lsSortedRelocs = true := by
  rfl_kernel

noncomputable def lsAllPieces : List Piece :=
  buildRoPieces 69728 0 lsSortedRelocs

noncomputable def lsSymAllData : List SymByte :=
  fastSymPieces (libsignalSessionImage.data ++ List.replicate libsignalSessionImage.bss 0#8) lsAllPieces

private theorem loads_fold_data {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img) :
    ∃ data,
      List.foldlM (DataReloc.apply img.base)
        (libsignalSessionImage.data ++ List.replicate libsignalSessionImage.bss 0#8)
        libsignalSessionImage.relocs = .ok data ∧
      libsignalSessionImage.wellFormed = true ∧
      img.data = data := by
  obtain ⟨data, hfold, -, hwfli, -, himg_eq⟩ := ProofLib.ObjectLoad.load_eq_ok himg
  exact ⟨data, hfold, hwfli, congrArg Image.data himg_eq⟩

theorem loads_img_data_eq_sym {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img) :
    img.data = lsSymAllData.map (evalSymByte img.base) := by
  obtain ⟨data, hfold, hwfli, hdata⟩ := loads_fold_data himg
  have hlen0 : (libsignalSessionImage.data ++ List.replicate libsignalSessionImage.bss 0#8).length =
      69728 := by
    rw [List.length_append, List.length_replicate, lsDataLen_eq, lsBss_eq]
  have hrel : libsignalSessionImage.relocs.all
      (fun r => decide (r.off + r.width ≤ 69728)) = true := by
    have h : libsignalSessionImage.relocs.all (fun r => (r.width == 8 || r.width == 4) &&
        decide (r.off + r.width ≤ libsignalSessionImage.data.length)) = true := by
      simp only [Obj.LinkedImage.wellFormed, Bool.and_eq_true] at hwfli
      exact hwfli.1.1.2
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    intro r hr
    have := (h r hr).2
    have := lsDataLen_eq
    omega
  have hdl : data.length = 69728 :=
    (ProofLib.ObjectLoad.RoDataFactsAux.foldlM_dataReloc_length _ _ _ hfold hrel
      (Nat.le_of_eq hlen0.symm)).trans hlen0
  have hok_ps : piecesOk libsignalSessionImage.relocs 69728 0 lsAllPieces = true :=
    piecesOk_buildRoPieces_perm lsSortedRelocs [] 0
      (by simpa only [List.nil_append, lsSortedRelocs] using sortRelocs_perm libsignalSessionImage.relocs)
      (by intro _ hp; nomatch hp)
      lsSortedAllRelocs_ok
  have hp_len : piecesLen lsAllPieces = 69728 := by
    simpa only [lsAllPieces, Nat.sub_zero] using piecesLen_buildRoPieces lsSortedAllRelocs_ok
  have hfp := ElfFrozen.fold_pieces libsignalSessionImage.relocs _ data 69728 hlen0 hfold
    lsAllPieces 0 hok_ps
  simp only [List.drop_zero, hp_len] at hfp
  rw [List.take_of_length_le (Nat.le_of_eq hdl)] at hfp
  rw [hdata, hfp, ← fastSymPieces_eval]
  rfl

def symPatchRelocFast (tSym : Obj.Interned.VecTree (Option (Nat × Nat)))
    (tBases tAddrs : Obj.Interned.VecTree (BitVec 64))
    (sbs : List SymByte) (r : Obj.Interned.Reloc) : List SymByte :=
  let resolved := match tSym.getD none r.sym with
    | some (bi, off) => tBases.getD 0#64 bi + BitVec.ofNat 64 off
    | none => tAddrs.getD 0#64 r.sym
  let t0 := (addSignedAddr resolved r.addend).toNat
  match r.kind with
  | .abs64 => sbs.take r.off ++ symRelocBytes t0 ++ sbs.drop (r.off + 8)
  | _ => sbs

def symPatchedDataFast (tSym : Obj.Interned.VecTree (Option (Nat × Nat)))
    (tBases tAddrs : Obj.Interned.VecTree (BitVec 64)) (d : Obj.Interned.Data) : List SymByte :=
  d.relocs.foldl (symPatchRelocFast tSym tBases tAddrs) (d.bytes.map SymByte.lit) ++
    List.replicate d.zeroTail (SymByte.lit 0#8)

def withForcedSymList {α : Type} (bs : List SymByte) (k : List SymByte → α) : α :=
  match bs with
  | [] => k []
  | b :: rest => k (b :: rest)

@[simp] theorem withForcedSymList_eq {α : Type} (bs : List SymByte) (k : List SymByte → α) :
    withForcedSymList bs k = k bs := by
  cases bs <;> rfl

def dropSym8 (bs : List SymByte) : List SymByte :=
  List.casesOn bs [] fun _ bs1 =>
  List.casesOn bs1 [] fun _ bs2 =>
  List.casesOn bs2 [] fun _ bs3 =>
  List.casesOn bs3 [] fun _ bs4 =>
  List.casesOn bs4 [] fun _ bs5 =>
  List.casesOn bs5 [] fun _ bs6 =>
  List.casesOn bs6 [] fun _ bs7 =>
  List.casesOn bs7 [] fun _ bs8 => bs8

@[simp] theorem dropSym8_eq_drop (bs : List SymByte) : dropSym8 bs = bs.drop 8 := by
  rcases bs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩ <;> rfl

def dropSym64 (bs : List SymByte) : List SymByte :=
  dropSym8 (dropSym8 (dropSym8 (dropSym8 (dropSym8 (dropSym8 (dropSym8 (dropSym8 bs)))))))

@[simp] theorem dropSym64_eq_drop (bs : List SymByte) : dropSym64 bs = bs.drop 64 := by
  simp [dropSym64, List.drop_drop]

def dropSym512 (bs : List SymByte) : List SymByte :=
  dropSym64 (dropSym64 (dropSym64 (dropSym64 (dropSym64 (dropSym64 (dropSym64 (dropSym64 bs)))))))

@[simp] theorem dropSym512_eq_drop (bs : List SymByte) : dropSym512 bs = bs.drop 512 := by
  simp [dropSym512, List.drop_drop]

def dropSym64Blocks : Nat → List SymByte → List SymByte
  | 0, bs => bs
  | q + 1, bs => withForcedSymList (dropSym64 bs) (dropSym64Blocks q)

@[simp] theorem dropSym64Blocks_eq_drop (q : Nat) (bs : List SymByte) :
    dropSym64Blocks q bs = bs.drop (q * 64) := by
  induction q generalizing bs with
  | zero => simp [dropSym64Blocks]
  | succ q ih => simp [dropSym64Blocks, ih, List.drop_drop, Nat.add_mul, Nat.add_comm]

def dropSym512Blocks : Nat → List SymByte → List SymByte
  | 0, bs => bs
  | q + 1, bs => withForcedSymList (dropSym512 bs) (dropSym512Blocks q)

@[simp] theorem dropSym512Blocks_eq_drop (q : Nat) (bs : List SymByte) :
    dropSym512Blocks q bs = bs.drop (q * 512) := by
  induction q generalizing bs with
  | zero => simp [dropSym512Blocks]
  | succ q ih => simp [dropSym512Blocks, ih, List.drop_drop, Nat.add_mul, Nat.add_comm]

def fastSymDrop (n : Nat) (bs : List SymByte) : List SymByte :=
  (dropSym64Blocks ((n % 512) / 64) (dropSym512Blocks (n / 512) bs)).drop (n % 64)

@[simp] theorem fastSymDrop_eq_drop (n : Nat) (bs : List SymByte) :
    fastSymDrop n bs = bs.drop n := by
  simp only [fastSymDrop, dropSym64Blocks_eq_drop, dropSym512Blocks_eq_drop, List.drop_drop]
  congr 1
  omega

def isSymPrefixOf : List SymByte → List SymByte → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => symByteBeq x y && isSymPrefixOf xs ys

def symPrefixAndLen : Nat → List SymByte → List SymByte → Option Nat
  | acc, [], _ => some acc
  | _, _ :: _, [] => none
  | acc, x :: xs, y :: ys =>
    if symByteBeq x y then symPrefixAndLen (acc + 1) xs ys else none

private theorem symPrefixAndLen_spec :
    ∀ (acc : Nat) (xs ys : List SymByte) {n : Nat},
      symPrefixAndLen acc xs ys = some n →
      n = acc + xs.length ∧ isSymPrefixOf xs ys = true
  | acc, [], _, _, h => by
    simp only [symPrefixAndLen, Option.some.injEq] at h
    simp only [List.length_nil, Nat.add_zero]
    exact ⟨h.symm, rfl⟩
  | _, _ :: _, [], _, h => nomatch h
  | acc, x :: xs, y :: ys, _, h => by
    unfold symPrefixAndLen at h
    cases hxy : symByteBeq x y
    · rw [hxy] at h; nomatch h
    · simp only [hxy, ↓reduceIte] at h
      obtain ⟨hn, hp⟩ := symPrefixAndLen_spec (acc + 1) xs ys h
      simp only [List.length_cons, isSymPrefixOf, hxy, Bool.true_and]
      exact ⟨by omega, hp⟩

private theorem drop_eq_cons_imp {α : Type} :
    ∀ (off : Nat) (l : List α) {y : α} {ys : List α},
      l.drop off = y :: ys →
      ∃ (hlt : off < l.length), l[off]'hlt = y ∧ l.drop (off + 1) = ys
  | 0, [], _, _, h => nomatch h
  | 0, x :: xs, _, _, h => by
    simp only [List.drop, List.cons.injEq] at h
    exact ⟨Nat.zero_lt_succ _, h.1, h.2⟩
  | n + 1, [], _, _, h => nomatch h
  | n + 1, _ :: xs, _, _, h => by
    obtain ⟨hlt, hy, hys⟩ := drop_eq_cons_imp n xs h
    exact ⟨Nat.succ_lt_succ hlt, hy, hys⟩

private theorem isSymPrefixOf_drop_spec :
    ∀ (off : Nat) (expected sfinal : List SymByte),
      isSymPrefixOf expected (sfinal.drop off) = true →
      ∀ (k : Nat) (hk : k < expected.length),
        ∃ (hs : off + k < sfinal.length), sfinal[off + k]'hs = expected[k]'hk
  | _, [], _, _, _, hk => nomatch hk
  | off, sb :: rest, sfinal, hp, k, hk => by
    cases hd : sfinal.drop off with
    | nil => rw [hd] at hp; nomatch hp
    | cons y ys =>
      rw [hd] at hp
      simp only [isSymPrefixOf, Bool.and_eq_true, symByteBeq_eq] at hp
      obtain ⟨hoff_lt, hy_eq, hdrop1⟩ := drop_eq_cons_imp off sfinal hd
      cases k with
      | zero =>
        refine ⟨by simpa only [Nat.add_zero] using hoff_lt, ?_⟩
        simpa only [Nat.add_zero, List.getElem_cons_zero, hp.1] using hy_eq
      | succ k' =>
        rw [← hdrop1] at hp
        obtain ⟨hs', heq'⟩ := isSymPrefixOf_drop_spec (off + 1) rest sfinal hp.2 k'
          (Nat.lt_of_succ_lt_succ hk)
        have hadd : (off + 1) + k' = off + (k' + 1) := by omega
        refine ⟨hadd ▸ hs', ?_⟩
        have h1 : sfinal[off + (k' + 1)]? = sfinal[(off + 1) + k']? :=
          congrArg (sfinal[·]?) hadd.symm
        rw [List.getElem?_eq_getElem (hadd ▸ hs'), List.getElem?_eq_getElem hs',
          Option.some.injEq] at h1
        exact h1.trans heq'

def inRoDataFast (ro : List (Nat × Nat)) (off len : Nat) : Bool :=
  ro.any fun r =>
    Nat.ble r.1 off && Nat.ble (off + len) (r.1 + r.2) && Nat.blt (r.1 + r.2) (2 ^ 64)

def roSymWalkSorted (tSym : Obj.Interned.VecTree (Option (Nat × Nat)))
    (tBases tAddrs : Obj.Interned.VecTree (BitVec 64))
    (ro : List (Nat × Nat)) (dataOff : Nat) :
    Nat → List SymByte → List Obj.Interned.Data → Bool
  | _, _, [] => true
  | cur, bs, d :: ds =>
    let addr0 := (tAddrs.getD 0#64 d.sym).toNat
    Nat.ble dataOff addr0 &&
    Obj.Interned.withNat (addr0 - dataOff) fun off =>
      Nat.ble cur off &&
      withForcedSymList (fastSymDrop (off - cur) bs) fun bs' =>
        match symPrefixAndLen 0 (symPatchedDataFast tSym tBases tAddrs d) bs' with
        | none => false
        | some expLen =>
          inRoDataFast ro addr0 expLen &&
          roSymWalkSorted tSym tBases tAddrs ro dataOff off bs' ds

def checkRoSymDataAll (ML : Obj.Interned.MultiLib) (mly : Obj.Interned.MultiLayout)
    (ro : List (Nat × Nat)) (dataOff : Nat) (sfinal : List SymByte) : Bool :=
  Obj.Interned.withVecTree 0#64 mly.bases fun tBases =>
    Obj.Interned.withVecTree 0#64 mly.addrs fun tAddrs =>
      match Obj.Interned.insertAllBlocks 0 ML.blocks (Obj.Interned.mkNoneTree 20 ML.names.length) with
      | none => false
      | some tSym =>
        let roSorted := fastMergeSort
          (fun d1 d2 => Nat.ble (tAddrs.getD 0#64 d1.sym).toNat (tAddrs.getD 0#64 d2.sym).toNat)
          (ML.data.filter (·.readOnly))
        roSymWalkSorted tSym tBases tAddrs ro dataOff 0 sfinal roSorted

theorem img0_roSymData_ok :
    checkRoSymDataAll lsInternedMultiLib img0MultiLayout
      libsignalSessionImage.roData libsignalSessionImage.dataOff lsSymAllData = true := by
  rfl_kernel

private theorem roSymWalkSorted_spec {tSym : Obj.Interned.VecTree (Option (Nat × Nat))}
    {tBases tAddrs : Obj.Interned.VecTree (BitVec 64)}
    {ro : List (Nat × Nat)} {dataOff : Nat} {sfinal : List SymByte} :
    ∀ {cur : Nat} {ds : List Obj.Interned.Data},
      roSymWalkSorted tSym tBases tAddrs ro dataOff cur (sfinal.drop cur) ds = true →
      ∀ di ∈ ds,
        let addr0 := (tAddrs.getD 0#64 di.sym).toNat
        let expected := symPatchedDataFast tSym tBases tAddrs di
        dataOff ≤ addr0 ∧
        (∃ r ∈ ro, r.1 ≤ addr0 ∧ addr0 + expected.length ≤ r.1 + r.2 ∧ r.1 + r.2 < 2 ^ 64) ∧
        isSymPrefixOf expected (sfinal.drop (addr0 - dataOff)) = true
  | _, [], _, _, hmem => nomatch hmem
  | cur, d :: ds, h, di, hmem => by
    unfold roSymWalkSorted at h
    simp only [Obj.Interned.withNat_eq, withForcedSymList_eq, fastSymDrop_eq_drop,
      List.drop_drop, Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨hd_off, hcur_le, hmatch⟩ := h
    have hadd_cur : cur + ( (tAddrs.getD 0#64 d.sym).toNat - dataOff - cur ) =
        (tAddrs.getD 0#64 d.sym).toNat - dataOff := by omega
    rw [hadd_cur] at hmatch
    cases hsp : symPrefixAndLen 0 (symPatchedDataFast tSym tBases tAddrs d)
        (sfinal.drop ((tAddrs.getD 0#64 d.sym).toNat - dataOff)) with
    | none => rw [hsp] at hmatch; nomatch hmatch
    | some expLen =>
      rw [hsp] at hmatch
      simp only [Bool.and_eq_true] at hmatch
      obtain ⟨hro, htail⟩ := hmatch
      obtain ⟨hexp_len, hpref⟩ := symPrefixAndLen_spec 0 _ _ hsp
      rw [Nat.zero_add] at hexp_len
      subst hexp_len
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · simp only [inRoDataFast, List.any_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hro
        obtain ⟨r, hr_mem, ⟨hr1, hr2⟩, hr3⟩ := hro
        exact ⟨hd_off, ⟨r, hr_mem, hr1, hr2, hr3⟩, hpref⟩
      · exact roSymWalkSorted_spec htail di hmem'

private theorem checkRoSymDataAll_spec {ML : Obj.Interned.MultiLib}
    {mly : Obj.Interned.MultiLayout} {ro : List (Nat × Nat)} {dataOff : Nat}
    {sfinal : List SymByte}
    (hok : checkRoSymDataAll ML mly ro dataOff sfinal = true) :
    ∃ tSym,
      Obj.Interned.insertAllBlocks 0 ML.blocks (Obj.Interned.mkNoneTree 20 ML.names.length) =
        some tSym ∧
      ∀ di ∈ ML.data, di.readOnly = true →
        let addr0 := ((Obj.Interned.toVecTree 0#64 mly.addrs).getD 0#64 di.sym).toNat
        let expected := symPatchedDataFast tSym
          (Obj.Interned.toVecTree 0#64 mly.bases)
          (Obj.Interned.toVecTree 0#64 mly.addrs) di
        dataOff ≤ addr0 ∧
        (∃ r ∈ ro, r.1 ≤ addr0 ∧ addr0 + expected.length ≤ r.1 + r.2 ∧ r.1 + r.2 < 2 ^ 64) ∧
        isSymPrefixOf expected (sfinal.drop (addr0 - dataOff)) = true := by
  unfold checkRoSymDataAll at hok
  simp only [Obj.Interned.withVecTree_eq] at hok
  cases hsym : Obj.Interned.insertAllBlocks 0 ML.blocks (Obj.Interned.mkNoneTree 20 ML.names.length) with
  | none => rw [hsym] at hok; nomatch hok
  | some tSym =>
    rw [hsym] at hok
    dsimp only at hok
    have hwalk := roSymWalkSorted_spec (sfinal := sfinal) (cur := 0) (by simpa using hok)
    refine ⟨tSym, rfl, fun di hdi hrd => ?_⟩
    have hmem_filt : di ∈ ML.data.filter (·.readOnly) := List.mem_filter.mpr ⟨hdi, hrd⟩
    let le : Obj.Interned.Data → Obj.Interned.Data → Bool := fun d1 d2 =>
      Nat.ble ((Obj.Interned.toVecTree 0#64 mly.addrs).getD 0#64 d1.sym).toNat
        ((Obj.Interned.toVecTree 0#64 mly.addrs).getD 0#64 d2.sym).toNat
    have hmem_sort : di ∈ fastMergeSort le (ML.data.filter (·.readOnly)) :=
      (fastMergeSort_perm le (ML.data.filter (·.readOnly))).symm.subset hmem_filt
    exact hwalk di hmem_sort

theorem img_roLoaded {img : Obj.Image} {s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hf : img.FrozenLoaded s) :
    LibsignalRoLoaded (imgMultiPlacement img) s.mem := by
  have hro_m := (Image.frozenLoaded_iff.mp hf).2.1
  have hdata_sym := loads_img_data_eq_sym himg
  obtain ⟨-, -, hda, hro_map, -, hwrap_ro⟩ := loads_fields himg
  obtain ⟨tSym, hsym, hrest⟩ := checkRoSymDataAll_spec img0_roSymData_ok
  obtain ⟨_, _, hget_sym⟩ := Obj.Interned.insertAllBlocks_spec 0 lsInternedMultiLib.blocks _ tSym hsym
  have hlookup : ∀ q, tSym.getD none q = Obj.Interned.lookupBlockSymId q lsInternedMultiLib.blocks := by
    intro q; rw [hget_sym q, Obj.Interned.getD_mkNoneTree]; rfl
  have hids_ok : lsInternedMultiLib.idsOk = true :=
    (Obj.Interned.multiIdsOkFast_eq lsInternedMultiLib).symm.trans ls_ids_ok
  have hn_lt : lsInternedMultiLib.names.length < 2 ^ 20 := by
    have h := ls_names_len; rw [Nat.blt_eq] at h; exact h
  have hgetN := Obj.Interned.toVecTree_getD_all "" lsInternedMultiLib.names hn_lt
  have hgetB := Obj.Interned.toVecTree_getD_all 0#64 img0MultiLayout.bases bases_len_lt
  have hgetA := Obj.Interned.toVecTree_getD_all 0#64 img0MultiLayout.addrs addrs_len_lt
  have hids_data : ∀ di ∈ lsInternedMultiLib.data,
      di.sym < lsInternedMultiLib.names.length ∧
      (∀ r ∈ di.relocs, r.sym < lsInternedMultiLib.names.length) := by
    have h := ls_ids_ok
    unfold Obj.Interned.multiIdsOkFast at h
    simp only [Obj.Interned.withNat_eq, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at h
    exact h.2
  intro d hd hrd
  change d ∈ libsignalSessionLib.data at hd
  change HoldsBytes s.mem ((imgMultiPlacement img).ρ d.sym)
    (libsignalSessionLib.patchedData (imgMultiPlacement img) d) (fun _ => Perm.ro)
  have hsb_d := extract_shiftBounds_data d hd
  have hk_abs := hsb_d.2.2
  have haddr0_bound : (img0MultiPlacement.ρ d.sym).toNat + d.bytes.length + d.zeroTail ≤
      libsignalSessionImage.gotOff := hsb_d.2.1
  rw [ls_fast_eq] at hd
  simp only [Obj.Interned.MultiLib.toMultiPlacedLibFast, Obj.Interned.withVecTree_eq, List.mem_map] at hd
  obtain ⟨di, hdi, rfl⟩ := hd
  have hro_di : di.readOnly = true := hrd
  obtain ⟨hoff_le, ⟨⟨rOff, rLen⟩, hr_mem, hr_le1, hr_le2, hr_lt⟩, hslice⟩ :=
    hrest di hdi hro_di
  obtain ⟨hdsym_lt, hdrel_lt⟩ := hids_data di hdi
  have hidx_d : lsInternedMultiLib.names.idxOf
      ((Obj.Interned.toVecTree "" lsInternedMultiLib.names).getD "" di.sym) = di.sym := by
    rw [hgetN di.sym]; exact Obj.Interned.idxOf_getD ls_names_nodup hdsym_lt
  have hρ0 : img0MultiPlacement.ρ (di.toInfoTree (Obj.Interned.toVecTree "" lsInternedMultiLib.names)).sym =
      (Obj.Interned.toVecTree 0#64 img0MultiLayout.addrs).getD 0#64 di.sym := by
    simp only [Obj.Interned.Data.toInfoTree, img0MultiPlacement,
      Obj.Interned.MultiLayout.toMultiPlacement, hidx_d, hgetA di.sym]
  have hpatched_eq :
      (symPatchedDataFast tSym
        (Obj.Interned.toVecTree 0#64 img0MultiLayout.bases)
        (Obj.Interned.toVecTree 0#64 img0MultiLayout.addrs) di).map (evalSymByte img.base) =
      libsignalSessionLib.patchedData (imgMultiPlacement img)
        (di.toInfoTree (Obj.Interned.toVecTree "" lsInternedMultiLib.names)) := by
    unfold symPatchedDataFast MultiPlacedLib.patchedData
    simp only [Obj.Interned.Data.toInfoTree, List.map_append, List.map_replicate, evalSymByte]
    congr 1
    have hfold_eq : ∀ (rs : List Obj.Interned.Reloc) (sbs : List SymByte),
        (∀ r ∈ rs, r.sym < lsInternedMultiLib.names.length) →
        (∀ r ∈ rs, (r.toEntryTree (Obj.Interned.toVecTree "" lsInternedMultiLib.names)).kind = .abs64) →
        (rs.foldl (symPatchRelocFast tSym
          (Obj.Interned.toVecTree 0#64 img0MultiLayout.bases)
          (Obj.Interned.toVecTree 0#64 img0MultiLayout.addrs)) sbs).map (evalSymByte img.base) =
        (rs.map (Obj.Interned.Reloc.toEntryTree (Obj.Interned.toVecTree "" lsInternedMultiLib.names))).foldl
          (libsignalSessionLib.patchDataReloc (imgMultiPlacement img)
            ((imgMultiPlacement img).ρ ((Obj.Interned.toVecTree "" lsInternedMultiLib.names).getD "" di.sym)))
          (sbs.map (evalSymByte img.base)) := by
      intro rs
      induction rs with
      | nil => intro _ _ _; rfl
      | cons r rs ih =>
        intro sbs hrs_lt hrs_abs
        simp only [List.foldl_cons, List.map_cons]
        rw [ih _ (fun r' hr' => hrs_lt r' (.tail _ hr')) (fun r' hr' => hrs_abs r' (.tail _ hr'))]
        congr 1
        have hr_lt := hrs_lt r (.head _)
        have hr_abs : r.kind = .abs64 := hrs_abs r (.head _)
        unfold symPatchRelocFast MultiPlacedLib.patchDataReloc
        simp only [Obj.Interned.Reloc.toEntryTree, hr_abs, List.map_append, List.map_take,
          List.map_drop, map_evalSymByte_symRelocBytes]
        congr 2; congr 1; congr 1
        dsimp only [imgMultiPlacement]
        rw [resolve_shift, addSignedAddr_add]
        congr 1
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
        congr 1
        rw [hlookup r.sym, hgetN r.sym, ls_toMultiPlacedLib_eq]
        have hidx_r : lsInternedMultiLib.names.idxOf (lsInternedMultiLib.names.getD r.sym "") = r.sym :=
          Obj.Interned.idxOf_getD ls_names_nodup hr_lt
        unfold MultiPlacedLib.resolve
        rw [Obj.Interned.lookupBlockSym_toMultiPlacedLib ls_names_nodup hids_ok hr_lt]
        cases Obj.Interned.lookupBlockSymId r.sym lsInternedMultiLib.blocks with
        | none =>
          simp only [img0MultiPlacement, Obj.Interned.MultiLayout.toMultiPlacement, hidx_r, hgetA r.sym]
        | some p =>
          simp only [img0MultiPlacement, Obj.Interned.MultiLayout.toMultiPlacement, hgetB p.1]
    have hinit_map : (di.bytes.map SymByte.lit).map (evalSymByte img.base) = di.bytes := by
      induction di.bytes with
      | nil => rfl
      | cons b bs ih => exact congrArg (b :: ·) ih
    rw [hfold_eq di.relocs (di.bytes.map SymByte.lit) hdrel_lt
      (fun r hr => hk_abs _ (List.mem_map.mpr ⟨r, hr, rfl⟩)), hinit_map]
  rw [← hpatched_eq]
  set expected := symPatchedDataFast tSym
    (Obj.Interned.toVecTree 0#64 img0MultiLayout.bases)
    (Obj.Interned.toVecTree 0#64 img0MultiLayout.addrs) di
  set addr0 := ((Obj.Interned.toVecTree 0#64 img0MultiLayout.addrs).getD 0#64 di.sym).toNat
  intro k hk
  rw [List.length_map] at hk
  obtain ⟨hs_lt, hslice_k⟩ := isSymPrefixOf_drop_spec (addr0 - libsignalSessionImage.dataOff)
    expected lsSymAllData hslice k hk
  have hi_data : (addr0 - libsignalSessionImage.dataOff) + k < img.data.length := by
    rw [hdata_sym, List.length_map]; exact hs_lt
  have hρ_bv : (imgMultiPlacement img).ρ
      (di.toInfoTree (Obj.Interned.toVecTree "" lsInternedMultiLib.names)).sym =
      img.base + BitVec.ofNat 64 addr0 := by
    dsimp only [imgMultiPlacement, shiftMultiPlacement]
    rw [hρ0]
    congr 1
    dsimp only [addr0]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have ha_eq : img.dataAddr + BitVec.ofNat 64 ((addr0 - libsignalSessionImage.dataOff) + k) =
      (imgMultiPlacement img).ρ
        (di.toInfoTree (Obj.Interned.toVecTree "" lsInternedMultiLib.names)).sym +
      BitVec.ofNat 64 k := by
    rw [hda, hρ_bv, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    congr 2; omega
  have ha_eq' : img.dataAddr + BitVec.ofNat 64 ((addr0 - libsignalSessionImage.dataOff) + k) =
      img.base + BitVec.ofNat 64 (addr0 + k) := by
    rw [ha_eq, hρ_bv, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hisRo : img.isRoData
      (img.dataAddr + BitVec.ofNat 64 ((addr0 - libsignalSessionImage.dataOff) + k)) = true := by
    have hgot_pos := got_len_pos
    have had_lt : addr0 + k < 2 ^ 64 := by omega
    have hro_lt : rOff < 2 ^ 64 := by omega
    have hle_ro : BitVec.ofNat 64 rOff ≤ BitVec.ofNat 64 (addr0 + k) := by
      rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hro_lt, Nat.mod_eq_of_lt had_lt]
      omega
    simp only [Image.isRoData, hro_map, List.any_map, List.any_eq_true]
    refine ⟨(rOff, rLen), hr_mem, ?_⟩
    simp only [Function.comp_apply, decide_eq_true_eq, ha_eq']
    rw [bv_add_sub_add_left, BitVec.toNat_sub_of_le hle_ro,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt had_lt, Nat.mod_eq_of_lt hro_lt]
    omega
  obtain ⟨hread, hperm, hlf⟩ := hro_m ((addr0 - libsignalSessionImage.dataOff) + k) hi_data hisRo
  have hbyte_eq : (expected.map (evalSymByte img.base))[k]'(by rw [List.length_map]; exact hk) =
      img.data[(addr0 - libsignalSessionImage.dataOff) + k] := by
    simp only [List.getElem_map, hdata_sym, ← hslice_k]
  rw [← ha_eq, hbyte_eq]
  exact ⟨hread, hperm, hlf⟩

theorem img_libsignalFrozen {img : Obj.Image} {s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hf : img.FrozenLoaded s) :
    LibsignalFrozen (imgMultiPlacement img) s.mem :=
  ⟨img_roLoaded himg hf, img_codeLoaded himg hf⟩

/-! ## Concrete Symbol and Entry Address Equalities -/

theorem img0MultiPlacement_rho_of_getD {idx : Nat} {s : String}
    (hlt : Nat.blt idx lsInternedMultiLib.names.length = true)
    (hname : lsInternedMultiLib.names.getD idx "" = s) :
    img0MultiPlacement.ρ s = img0SymAddrs.getD idx 0#64 := by
  have hlt' : idx < lsInternedMultiLib.names.length := Nat.blt_eq.mp hlt
  have hidx : lsInternedMultiLib.names.idxOf s = idx := by
    rw [← hname]
    exact Obj.Interned.idxOf_getD ls_names_nodup hlt'
  unfold img0MultiPlacement Obj.Interned.MultiLayout.toMultiPlacement img0MultiLayout
  dsimp only
  rw [hidx]

theorem img0_coinsNext_eq :
    img0MultiPlacement.ρ Coins.coinsNextSym = coinsNextOff :=
  (img0MultiPlacement_rho_of_getD (idx := lsCoinsNextIdx) (by rfl_kernel) (by rfl_kernel)).trans
    (by rfl_kernel)

theorem img0_coinsLeft_eq :
    img0MultiPlacement.ρ Coins.coinsLeftSym = coinsLeftOff :=
  (img0MultiPlacement_rho_of_getD (idx := lsCoinsLeftIdx) (by rfl_kernel) (by rfl_kernel)).trans
    (by rfl_kernel)

theorem img0_tokenStorage_eq :
    img0MultiPlacement.ρ CryptoVerification.LibsignalSpqrV1.tokenStorageName =
      CryptoVerification.LibsignalSpqrV1.tokenStorageOff :=
  (img0MultiPlacement_rho_of_getD (idx := lsTokenStorageIdx) (by rfl_kernel) (by rfl_kernel)).trans
    (by rfl_kernel)

theorem img0_tokenOnce_eq :
    img0MultiPlacement.ρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 =
      CryptoVerification.LibsignalSpqrV1.tokenOnceOff :=
  (congrArg (· + 8#64)
    (img0MultiPlacement_rho_of_getD (idx := lsTokenIdx) (by rfl_kernel) (by rfl_kernel))).trans
    (by rfl_kernel)

theorem img0_logFilter_eq :
    img0MultiPlacement.ρ CryptoVerification.lsLogFilterSym =
      BitVec.ofNat 64 631136 :=
  (img0MultiPlacement_rho_of_getD (idx := lsLogFilterIdx) (by rfl_kernel) (by rfl_kernel)).trans
    (by rfl_kernel)

theorem logFilterAddr_eq_add (img : Obj.Image) :
    CryptoVerification.LibsignalSession.logFilterAddr img =
      img.base + BitVec.ofNat 64 631136 :=
  rfl

theorem coinsInstalledPlaced_eq_coinsInstalled (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img)
    (p : BitVec 64) (coins : List (BitVec 8)) :
    @coinsInstalledPlaced (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement p coins =
      coinsInstalled img p coins := by
  letI : LibsignalFullPlacement := instLibsignalFullPlacementOfLoads img himg
  have h1 : Coins.coinsNextPlaced = img.base + coinsNextOff := by
    change img.base + img0MultiPlacement.ρ Coins.coinsNextSym = _
    rw [img0_coinsNext_eq]
  have h2 : Coins.coinsLeftPlaced = img.base + coinsLeftOff := by
    change img.base + img0MultiPlacement.ρ Coins.coinsLeftSym = _
    rw [img0_coinsLeft_eq]
  unfold coinsInstalledPlaced coinsInstalled
  rw [h1, h2]

theorem tokenInitPlacedAt_eq_tokenInit (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img) :
    @SpqrV1.GF.Mul2U16.tokenInitPlacedAt
        (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement =
      CryptoVerification.LibsignalSpqrV1.TokenInit img := by
  letI : LibsignalFullPlacement := instLibsignalFullPlacementOfLoads img himg
  unfold SpqrV1.GF.Mul2U16.tokenInitPlacedAt CryptoVerification.LibsignalSpqrV1.TokenInit
  have hs1 : lsρ CryptoVerification.LibsignalSpqrV1.tokenStorageName =
      img.base + CryptoVerification.LibsignalSpqrV1.tokenStorageOff := by
    change img.base + img0MultiPlacement.ρ _ = _
    rw [img0_tokenStorage_eq]
  have hs2 : lsρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 =
      img.base + CryptoVerification.LibsignalSpqrV1.tokenOnceOff := by
    change (img.base + img0MultiPlacement.ρ _) + 8#64 = _
    rw [BitVec.add_assoc, img0_tokenOnce_eq]
  rw [hs1, hs2]

theorem lsLogOff_eq_logOff (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img) :
    @CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff
        (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement =
      CryptoVerification.LibsignalTripleRatchet.logOff img := by
  letI : LibsignalFullPlacement := instLibsignalFullPlacementOfLoads img himg
  unfold CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff
    CryptoVerification.LibsignalTripleRatchet.logOff
  have hs3 : CryptoVerification.lsLogFilterAddr =
      CryptoVerification.LibsignalSession.logFilterAddr img := by
    change img.base + img0MultiPlacement.ρ _ = _
    rw [img0_logFilter_eq, logFilterAddr_eq_add]
  rw [hs3]

theorem cliStaticsPlaced_eq_cliStatics (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img) :
    @cliStaticsPlaced (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement =
      cliStatics img := by
  letI : LibsignalFullPlacement := instLibsignalFullPlacementOfLoads img himg
  have h1 : Coins.coinsNextPlaced = img.base + coinsNextOff := by
    change img.base + img0MultiPlacement.ρ Coins.coinsNextSym = _
    rw [img0_coinsNext_eq]
  have h2 : Coins.coinsLeftPlaced = img.base + coinsLeftOff := by
    change img.base + img0MultiPlacement.ρ Coins.coinsLeftSym = _
    rw [img0_coinsLeft_eq]
  unfold cliStaticsPlaced cliStatics coinsStaticsPlaced coinsStatics
  rw [h1, h2, tokenInitPlacedAt_eq_tokenInit img himg, lsLogOff_eq_logOff img himg]

private theorem img0_base617_eq_main_off :
    img0MultiPlacement.base 617 =
      BitVec.ofNat 64 (num% (ls_off% "main")) := by
  rfl_kernel

private theorem img0_base579_eq_run_off :
    img0MultiPlacement.base 579 =
      BitVec.ofNat 64 (num% (ls_off% "libsignal_cli::run")) := by
  rfl_kernel

theorem cliProg_eq_mProg {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    cliProg img ext = mProg img ext :=
  Program.ofImage_eq_rebase (P := libsignalSessionCode) rfl himg

theorem mPcPlaced_zero_eq_entryOf {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) :
    @mPcPlaced (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement 0 =
      entryOf img mainName := by
  letI : LibsignalFullPlacement := instLibsignalFullPlacementOfLoads img himg
  rw [mPcPlaced_zero]
  change img.base + img0MultiPlacement.base 617 = (Program.ofImage img).fnAddr mainName
  rw [Program.ofImage_eq_rebase (P := libsignalSessionCode) rfl himg,
    Program.fnAddr_rebase, main_fnOff, img0_base617_eq_main_off]

theorem base579_eq_run_fnAddr {img : Obj.Image}
    (_himg : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    (imgMultiPlacement img).base 579 = (mProg img ext).fnAddr runName := by
  change img.base + img0MultiPlacement.base 579 = (mProg img ext).fnAddr runName
  rw [mProg, tripleRatchetProgAtExt, Program.fnAddr_rebase, run_fnOff, img0_base579_eq_run_off]

/-! ## Extern/Stub Bijection Between `mProgPlaced` and `Program.ofImage` -/

noncomputable def liftHooksToPlaced (Y : String → Option (State → State)) : LibsignalHooks :=
  fun extSym => (lookup extSym (lsExternStubTriples.map fun t => (t.1, t.2.1))).bind Y

theorem lsImgStubs_eq : libsignalSessionImage.stubs = lsImgStubs := by
  rfl_kernel

theorem lsTriples_to_placed :
    lsExternStubTriples.map (fun t => (t.1, BitVec.ofNat 64 t.2.2)) = lsPlacedStubPairs0 := by
  rfl_kernel

private def checkPairwiseNeStr : List String → Bool
  | [] => true
  | s :: ss => !(ss.any (· == s)) && checkPairwiseNeStr ss

private theorem nodup_of_checkPairwiseNeStr :
    ∀ {ss : List String}, checkPairwiseNeStr ss = true → ss.Nodup
  | [], _ => .nil
  | s :: ss, h => by
    simp only [checkPairwiseNeStr, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.Nodup.cons (fun hmem => ?_) (nodup_of_checkPairwiseNeStr h.2)
    have hany : ss.any (· == s) = true := List.any_eq_true.mpr ⟨s, hmem, beq_self_eq_true s⟩
    rw [h.1] at hany
    nomatch hany

private theorem lsTriples_fst_nodup_check :
    checkPairwiseNeStr (lsExternStubTriples.map Prod.fst) = true := by
  rfl_kernel

theorem lsTriples_fst_nodup : (lsExternStubTriples.map Prod.fst).Nodup :=
  nodup_of_checkPairwiseNeStr lsTriples_fst_nodup_check

private theorem lookup_of_mem_nodup_str {α : Type} :
    ∀ (L : List (String × α)) (n : String) (v : α),
      (L.map Prod.fst).Nodup → (n, v) ∈ L → lookup n L = some v
  | [], _, _, _, hm => nomatch hm
  | (k, val) :: rest, n, v, hnd, hm => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hm with hhead | htail
    · cases hhead
      unfold lookup
      simp
    · have hne : (k == n) = false := by
        rw [beq_eq_false_iff_ne]
        intro heq
        subst heq
        exact hnd.1 (List.mem_map.mpr ⟨(k, v), htail, rfl⟩)
      unfold lookup
      simp only [List.find?_cons, hne]
      exact lookup_of_mem_nodup_str rest n v hnd.2 htail

theorem liftHooksToPlaced_on_triple (Y : String → Option (State → State))
    {t : String × (String × Nat)} (ht : t ∈ lsExternStubTriples) :
    liftHooksToPlaced Y t.1 = Y t.2.1 := by
  unfold liftHooksToPlaced
  have hl : lookup t.1 (lsExternStubTriples.map fun q => (q.1, q.2.1)) = some t.2.1 :=
    lookup_of_mem_nodup_str _ t.1 t.2.1
      (by simpa [List.map_map, Function.comp_def] using lsTriples_fst_nodup)
      (List.mem_map.mpr ⟨t, ht, rfl⟩)
  rw [hl]
  rfl

theorem liftHooksToPlaced_of_lookup (Y : String → Option (State → State))
    {extSym stSym : String}
    (hl : lookup extSym (lsExternStubTriples.map fun t => (t.1, t.2.1)) = some stSym) :
    liftHooksToPlaced Y extSym = Y stSym := by
  unfold liftHooksToPlaced
  rw [hl]
  rfl

private theorem lsTriples_off_sorted_check :
    strictSortedBy id
      (fastMergeSort Nat.ble ((lsExternStubTriples.map Prod.snd).map Prod.snd)) = true := by
  rfl_kernel

theorem lsTriples_off_nodup : ((lsExternStubTriples.map Prod.snd).map Prod.snd).Nodup :=
  (List.Perm.nodup_iff (fastMergeSort_perm _ _)).mp
    (nodup_of_strictSortedBy id _ lsTriples_off_sorted_check)

private theorem lsTriples_sorted_eq_filtered_sorted :
    fastMergeSort (fun a b => Nat.ble a.2 b.2) (lsExternStubTriples.map Prod.snd) =
      fastMergeSort (fun a b => Nat.ble a.2 b.2)
        (lsImgStubs.filter (fun p => !(lsDeadImgStubOffs.any (· == p.2)))) := by
  rfl_kernel

private theorem lsTriples_perm_filtered :
    List.Perm (lsExternStubTriples.map Prod.snd)
      (lsImgStubs.filter (fun p => !(lsDeadImgStubOffs.any (· == p.2)))) := by
  have h1 := (fastMergeSort_perm (fun a b => Nat.ble a.2 b.2)
    (lsExternStubTriples.map Prod.snd)).symm
  have h2 := fastMergeSort_perm (fun a b => Nat.ble a.2 b.2)
    (lsImgStubs.filter (fun p => !(lsDeadImgStubOffs.any (· == p.2))))
  rw [lsTriples_sorted_eq_filtered_sorted] at h1
  exact h1.trans h2

private theorem lsTriples_disjoint_dead :
    (lsExternStubTriples.all fun t => !(lsDeadImgStubOffs.any (· == t.2.2))) = true := by
  rfl_kernel

private theorem blk617_externs_eq :
    (libsignalSessionLib.blocks.getD 617 { code := [] }).externs = libsignalSessionExterns := by
  rw [ls_fast_eq]
  rfl_kernel

private theorem lsSharedExterns_not_blockSym :
    (match Obj.Interned.insertAllBlocks 0 lsInternedMultiLib.blocks
        (Obj.Interned.mkNoneTree 20 lsInternedMultiLib.names.length) with
      | none => false
      | some tSym => lsSharedExterns.all fun idx => (tSym.getD none idx).isNone) = true := by
  rfl_kernel

private theorem resolve_img0_on_extern {e : String} (he : e ∈ libsignalSessionExterns) :
    libsignalSessionLib.resolve img0MultiPlacement e = img0MultiPlacement.ρ e := by
  have hchk := lsSharedExterns_not_blockSym
  cases hsym : Obj.Interned.insertAllBlocks 0 lsInternedMultiLib.blocks
      (Obj.Interned.mkNoneTree 20 lsInternedMultiLib.names.length) with
  | none => rw [hsym] at hchk; nomatch hchk
  | some tSym =>
    rw [hsym] at hchk
    dsimp only at hchk
    rw [List.all_eq_true] at hchk
    obtain ⟨_, _, hget_sym⟩ := Obj.Interned.insertAllBlocks_spec 0 lsInternedMultiLib.blocks _ tSym hsym
    have hn_lt : lsInternedMultiLib.names.length < 2 ^ 20 := Nat.blt_eq.mp ls_names_len
    have hgetN := Obj.Interned.toVecTree_getD_all "" lsInternedMultiLib.names hn_lt
    have hids_ok : lsInternedMultiLib.idsOk = true :=
      (Obj.Interned.multiIdsOkFast_eq lsInternedMultiLib).symm.trans ls_ids_ok
    rw [ls_sharedExterns_eq_tree, Obj.Interned.withVecTree_eq, List.mem_map] at he
    obtain ⟨idx, hidx_mem, rfl⟩ := he
    have hlt : idx < lsInternedMultiLib.names.length :=
      Nat.blt_eq.mp (List.all_eq_true.mp ls_sharedExterns_lt idx hidx_mem)
    have hnone_t : (tSym.getD none idx).isNone = true := hchk idx hidx_mem
    have hlookup : Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks = none := by
      have h1 : tSym.getD none idx = Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks := by
        rw [hget_sym idx, Obj.Interned.getD_mkNoneTree]; rfl
      rw [← h1]
      exact Option.isNone_iff_eq_none.mp hnone_t
    rw [hgetN idx, ls_toMultiPlacedLib_eq]
    unfold MultiPlacedLib.resolve
    rw [Obj.Interned.lookupBlockSym_toMultiPlacedLib ls_names_nodup hids_ok hlt, hlookup]

private theorem lsPlacedStubPairs0_fst_eq_tree :
    lsPlacedStubPairs0.map Prod.fst =
      Obj.Interned.withVecTree "" lsInternedMultiLib.names
        (fun t => lsSharedExterns.map (fun idx => t.getD "" idx)) := by
  rfl_kernel

private theorem lsPlacedStubPairs0_fst_eq :
    lsPlacedStubPairs0.map Prod.fst = libsignalSessionExterns :=
  lsPlacedStubPairs0_fst_eq_tree.trans ls_sharedExterns_eq_tree.symm

private theorem lsTriples_off_lt_2pow64 :
    (lsExternStubTriples.all fun t => Nat.blt t.2.2 (2 ^ 64)) = true := by
  rfl_kernel

private theorem list_eq_map_graph {α β : Type} (f : α → β) :
    ∀ (ps : List (α × β)) (es : List α),
      ps.map Prod.fst = es → ps.map Prod.snd = es.map f →
      ps = es.map (fun e => (e, f e))
  | [], [], _, _ => rfl
  | _ :: _, [], h1, _ => nomatch h1
  | [], _ :: _, h1, _ => nomatch h1
  | (a, b) :: ps, e :: es, h1, h2 => by
    simp only [List.map_cons, List.cons.injEq] at h1 h2
    obtain ⟨rfl, h1'⟩ := h1
    obtain ⟨rfl, h2'⟩ := h2
    exact congrArg ((a, f a) :: ·) (list_eq_map_graph f ps es h1' h2')

private theorem lsExterns_eq_triples :
    libsignalSessionExterns.map (fun e => (e, (img0MultiPlacement.ρ e).toNat)) =
      lsExternStubTriples.map (fun t => (t.1, t.2.2)) := by
  have hpairs : lsPlacedStubPairs0 = libsignalSessionExterns.map (fun e => (e, img0MultiPlacement.ρ e)) :=
    list_eq_map_graph img0MultiPlacement.ρ lsPlacedStubPairs0 libsignalSessionExterns
      lsPlacedStubPairs0_fst_eq lsPlacedStubPairs0_snd_eq
  have h1 := congrArg (List.map (fun p : String × BitVec 64 => (p.1, p.2.toNat)))
    (lsTriples_to_placed.trans hpairs).symm
  simp only [List.map_map, Function.comp_def] at h1
  refine h1.trans (List.map_congr_left fun t ht => ?_)
  have hlt : t.2.2 < 2 ^ 64 := Nat.blt_eq.mp (List.all_eq_true.mp lsTriples_off_lt_2pow64 t ht)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

private theorem toNat_beq_eq_beq (x y : BitVec 64) : (x.toNat == y.toNat) = (x == y) := by
  cases h : (x == y)
  · rw [beq_eq_false_iff_ne] at h ⊢
    intro heq
    exact h (BitVec.eq_of_toNat_eq heq)
  · rw [beq_iff_eq] at h
    subst h
    exact beq_self_eq_true x.toNat

private theorem sub_beq_sub_right (x y c : BitVec 64) : ((x - c) == (y - c)) = (x == y) := by
  cases h : (x == y)
  · rw [beq_eq_false_iff_ne] at h ⊢
    intro heq
    apply h
    have hadd := congrArg (· + c) heq
    simpa [BitVec.sub_add_cancel] using hadd
  · rw [beq_iff_eq] at h
    subst h
    exact beq_self_eq_true (x - c)

private theorem bv_sub_toNat_beq_iff (b r0 b617 pc : BitVec 64) :
    (((b + r0) - (b + b617)).toNat == (pc - (b + b617)).toNat) =
      (r0.toNat == (pc - b).toNat) := by
  rw [bv_add_sub_add_left, show pc - (b + b617) = (pc - b) - b617 by bv_lin,
    toNat_beq_eq_beq, sub_beq_sub_right, ← toNat_beq_eq_beq]

private theorem findSome?_const_none {α β : Type} (p : α → Bool) :
    ∀ (xs : List α), (xs.findSome? fun x => if p x then (none : Option β) else none) = none
  | [] => rfl
  | _ :: xs => by
    unfold List.findSome?
    rw [ite_self]
    exact findSome?_const_none p xs

private theorem findSome?_eq_none_of_forall {α β : Type} {f : α → Option β} :
    ∀ {xs : List α}, (∀ x ∈ xs, f x = none) → xs.findSome? f = none
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.findSome?_cons, h x (.head _)]
    exact findSome?_eq_none_of_forall fun y hy => h y (.tail _ hy)

private theorem opt_or_none {α : Type} (o : Option α) : o.or none = o := by
  cases o <;> rfl

private theorem findSome?_map_eq {α β γ : Type} (f : α → β) (g : β → Option γ) :
    ∀ (xs : List α), (xs.map f).findSome? g = xs.findSome? (fun x => g (f x))
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.findSome?_cons]
    cases g (f x) <;> simp [findSome?_map_eq f g xs]

private theorem findSome?_congr {α β : Type} {f g : α → Option β} :
    ∀ {xs : List α}, (∀ x ∈ xs, f x = g x) → xs.findSome? f = xs.findSome? g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.findSome?_cons, h x (.head _)]
    cases g x
    · exact findSome?_congr fun y hy => h y (.tail _ hy)
    · rfl

private theorem findSome?_eq_of_perm_nodup {α : Type} (off : Nat) (Y : String → Option α) :
    ∀ {xs ys : List (String × Nat)},
      List.Perm xs ys →
      (xs.map Prod.snd).Nodup →
      (xs.findSome? fun p => if p.2 == off then Y p.1 else none) =
        (ys.findSome? fun p => if p.2 == off then Y p.1 else none)
  | _, _, hperm, hnd => by
    induction hperm with
    | nil => rfl
    | cons p hp ih =>
      rw [List.map_cons, List.nodup_cons] at hnd
      simp only [List.findSome?_cons]
      cases (if p.2 == off then Y p.1 else none)
      · exact ih hnd.2
      · rfl
    | swap x y l =>
      simp only [List.findSome?_cons]
      cases hx : (x.2 == off) <;> cases hy : (y.2 == off)
      · rfl
      · simp
      · simp
      · have hxy : x.2 = y.2 := (eq_of_beq hx).trans (eq_of_beq hy).symm
        simp only [List.map_cons, List.nodup_cons, List.mem_cons] at hnd
        omega
    | trans h1 _ ih1 ih2 =>
      exact (ih1 hnd).trans (ih2 ((h1.map Prod.snd).nodup_iff.mp hnd))

private theorem findSome?_filter_keep {α : Type} (keep : Nat → Bool) (off : Nat)
    (Y : String → Option α) (hk : keep off = true) :
    ∀ (ps : List (String × Nat)),
      ((ps.filter (fun p => keep p.2)).findSome? fun p => if p.2 == off then Y p.1 else none) =
        (ps.findSome? fun p => if p.2 == off then Y p.1 else none)
  | [] => rfl
  | p :: ps => by
    cases hp : (p.2 == off)
    · simp only [List.filter_cons, List.findSome?_cons, hp, Bool.false_eq_true, ↓reduceIte]
      cases keep p.2
      · exact findSome?_filter_keep keep off Y hk ps
      · simp only [List.findSome?_cons, hp, Bool.false_eq_true, ↓reduceIte]
        exact findSome?_filter_keep keep off Y hk ps
    · have hoff : p.2 = off := eq_of_beq hp
      have hkp : keep p.2 = true := hoff ▸ hk
      simp only [List.filter_cons, hkp, ↓reduceIte, List.findSome?_cons, hp]
      cases Y p.1
      · exact findSome?_filter_keep keep off Y hk ps
      · rfl

private theorem mProgPlaced_externAt_eq_triples {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (Y : String → Option (State → State)) (pc : BitVec 64) :
    (@mProgPlaced (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement
      (liftHooksToPlaced Y)).externAt? pc =
      (lsExternStubTriples.map Prod.snd).findSome?
        (fun p => if p.2 == (pc - img.base).toNat then Y p.1 else none) := by
  letI : LibsignalFullPlacement := instLibsignalFullPlacementOfLoads img himg
  have hprog : mProgPlaced (liftHooksToPlaced Y) =
      libsignalSessionLib.blockProgram (imgMultiPlacement img) 617 (liftHooksToPlaced Y) :=
    IsLsBlockProg.eq_blockProgram (prog := lsProg_617 (liftHooksToPlaced Y))
      (i := 617) (H := liftHooksToPlaced Y)
  rw [hprog]
  unfold MultiPlacedLib.blockProgram PlacedLib.program MultiPlacedLib.blockLib
    MultiPlacedLib.blockPlacement Program.externAt? Program.hookAtOff?
  dsimp only
  rw [findSome?_const_none, opt_or_none, blk617_externs_eq, findSome?_map_eq]
  have hstep1 :
      (libsignalSessionExterns.findSome? fun e =>
        if ((libsignalSessionLib.resolve (imgMultiPlacement img) e -
            (imgMultiPlacement img).base 617).toNat ==
            (pc - (imgMultiPlacement img).base 617).toNat) then
          liftHooksToPlaced Y e
        else none) =
      (libsignalSessionExterns.findSome? fun e =>
        if (img0MultiPlacement.ρ e).toNat == (pc - img.base).toNat then
          liftHooksToPlaced Y e
        else none) := by
    refine findSome?_congr fun e he => ?_
    have hr : libsignalSessionLib.resolve (imgMultiPlacement img) e =
        img.base + img0MultiPlacement.ρ e := by
      dsimp only [imgMultiPlacement]
      rw [resolve_shift, resolve_img0_on_extern he]
    have hb : (imgMultiPlacement img).base 617 = img.base + img0MultiPlacement.base 617 := rfl
    rw [hr, hb, bv_sub_toNat_beq_iff]
  rw [hstep1, ← findSome?_map_eq (fun e => (e, (img0MultiPlacement.ρ e).toNat))
    (fun p => if p.2 == (pc - img.base).toNat then liftHooksToPlaced Y p.1 else none),
    lsExterns_eq_triples, findSome?_map_eq, findSome?_map_eq]
  refine findSome?_congr fun t ht => ?_
  rw [liftHooksToPlaced_on_triple Y ht]

theorem mProgPlaced_externAt_eq_of_not_dead {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (Y : String → Option (State → State)) (pc : BitVec 64)
    (hnd : lsDeadImgStubOffs.any (· == (pc - img.base).toNat) = false) :
    (@mProgPlaced (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement
      (liftHooksToPlaced Y)).externAt? pc =
      (Program.ofImage img Y).externAt? pc := by
  rw [mProgPlaced_externAt_eq_triples himg Y pc,
    findSome?_eq_of_perm_nodup _ Y lsTriples_perm_filtered lsTriples_off_nodup,
    findSome?_filter_keep (fun o => !(lsDeadImgStubOffs.any (· == o))) _ Y
      (by rw [hnd]; rfl)]
  obtain ⟨-, hstubs_eq, -, -, -, -⟩ := loads_fields himg
  have hstubs : img.stubs = lsImgStubs := hstubs_eq.trans lsImgStubs_eq
  unfold Program.ofImage Program.externAt? Program.hookAtOff?
  dsimp only
  rw [findSome?_const_none, opt_or_none, hstubs]

def checkZeroWordsAtSorted : Nat → List (BitVec 8) → List Nat → Bool
  | _, _, [] => true
  | cur, bs, o :: os =>
    Nat.ble cur o &&
    Nat.beq (o % 4) 0 &&
    match Process.fastDrop (o - cur) bs with
    | b0 :: b1 :: b2 :: b3 :: rest =>
      Obj.Interned.bv8Beq b0 0#8 &&
      Obj.Interned.bv8Beq b1 0#8 &&
      Obj.Interned.bv8Beq b2 0#8 &&
      Obj.Interned.bv8Beq b3 0#8 &&
      checkZeroWordsAtSorted (o + 4) rest os
    | _ => false

private theorem checkZeroWordsAtSorted_spec {code : List (BitVec 8)} :
    ∀ {cur : Nat} {os : List Nat},
      checkZeroWordsAtSorted cur (code.drop cur) os = true →
      ∀ o ∈ os,
        o % 4 = 0 ∧ o + 4 ≤ code.length ∧
        code.getD o 1#8 = 0#8 ∧
        code.getD (o + 1) 1#8 = 0#8 ∧
        code.getD (o + 2) 1#8 = 0#8 ∧
        code.getD (o + 3) 1#8 = 0#8
  | _, [], _, _, hmem => nomatch hmem
  | cur, o :: os, h, q, hmem => by
    unfold checkZeroWordsAtSorted at h
    simp only [Process.fastDrop_eq_drop, List.drop_drop, Bool.and_eq_true,
      Nat.ble_eq, Nat.beq_eq] at h
    obtain ⟨⟨hcur, hm4⟩, hmatch⟩ := h
    have hadd_cur : cur + (o - cur) = o := by omega
    rw [hadd_cur] at hmatch
    cases hd0 : code.drop o with
    | nil => rw [hd0] at hmatch; nomatch hmatch
    | cons b0 r1 =>
      cases hd1 : r1 with
      | nil => rw [hd0, hd1] at hmatch; nomatch hmatch
      | cons b1 r2 =>
        cases hd2 : r2 with
        | nil => rw [hd0, hd1, hd2] at hmatch; nomatch hmatch
        | cons b2 r3 =>
          cases hd3 : r3 with
          | nil => rw [hd0, hd1, hd2, hd3] at hmatch; nomatch hmatch
          | cons b3 rest =>
            rw [hd0, hd1, hd2, hd3] at hmatch
            simp only [Bool.and_eq_true, Obj.Interned.bv8Beq_eq, beq_iff_eq] at hmatch
            obtain ⟨⟨⟨⟨hb0, hb1⟩, hb2⟩, hb3⟩, htail⟩ := hmatch
            rw [hd1, hd2, hd3] at hd0
            obtain ⟨hlt0, he0, hdr1⟩ := drop_eq_cons_imp o code hd0
            obtain ⟨hlt1, he1, hdr2⟩ := drop_eq_cons_imp (o + 1) code hdr1
            obtain ⟨hlt2, he2, hdr3⟩ := drop_eq_cons_imp (o + 2) code hdr2
            obtain ⟨hlt3, he3, hdr4⟩ := drop_eq_cons_imp (o + 3) code hdr3
            rcases List.mem_cons.mp hmem with rfl | hmem'
            · refine ⟨hm4, by omega, ?_, ?_, ?_, ?_⟩
              · rw [Obj.Interned.getD_of_lt hlt0, he0, hb0]
              · rw [Obj.Interned.getD_of_lt hlt1, he1, hb1]
              · rw [Obj.Interned.getD_of_lt hlt2, he2, hb2]
              · rw [Obj.Interned.getD_of_lt hlt3, he3, hb3]
            · rw [← hdr4] at htail
              exact checkZeroWordsAtSorted_spec htail q hmem'

def checkDeadStubZeroWords (code : List (BitVec 8)) (offs : List Nat) : Bool :=
  checkZeroWordsAtSorted 0 code (fastMergeSort Nat.ble offs)

private theorem checkDeadStubZeroWords_spec {code : List (BitVec 8)} {offs : List Nat}
    (hok : checkDeadStubZeroWords code offs = true) :
    ∀ o ∈ offs,
      o % 4 = 0 ∧ o + 4 ≤ code.length ∧
      code.getD o 1#8 = 0#8 ∧
      code.getD (o + 1) 1#8 = 0#8 ∧
      code.getD (o + 2) 1#8 = 0#8 ∧
      code.getD (o + 3) 1#8 = 0#8 := by
  intro o ho
  have hwalk := checkZeroWordsAtSorted_spec (code := code) (cur := 0) (by simpa [checkDeadStubZeroWords] using hok)
  exact hwalk o ((fastMergeSort_perm Nat.ble offs).symm.subset ho)

private theorem lsDeadStubZeroWords_ok :
    checkDeadStubZeroWords libsignalSessionImage.code lsDeadImgStubOffs = true := by
  rfl_kernel

private theorem decode_zero_word_eq_none : Arm64.decode 0#32 = none := by
  decide

theorem mProgPlaced_dead_stub_none {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (Y : String → Option (State → State)) {m : Memory} (pc : BitVec 64)
    (hcl : (Program.ofImageWithSvc noSyscalls img).CodeLoaded m)
    (hdead : lsDeadImgStubOffs.any (· == (pc - img.base).toNat) = true) :
    (@mProgPlaced (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement
      (liftHooksToPlaced Y)).externAt? pc = none ∧
    (@mProgPlaced (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement
      (liftHooksToPlaced Y)).fetchMem m pc = none := by
  have hext_none :
      (@mProgPlaced (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement
        (liftHooksToPlaced Y)).externAt? pc = none := by
    rw [mProgPlaced_externAt_eq_triples himg Y pc, findSome?_map_eq]
    refine findSome?_eq_none_of_forall fun t ht => ?_
    have hdisj := List.all_eq_true.mp lsTriples_disjoint_dead t ht
    have hne : (t.2.2 == (pc - img.base).toNat) = false := by
      cases h : (t.2.2 == (pc - img.base).toNat)
      · rfl
      · have heq : t.2.2 = (pc - img.base).toNat := eq_of_beq h
        rw [heq, hdead] at hdisj
        nomatch hdisj
    rw [hne]
    rfl
  refine ⟨hext_none, ?_⟩
  obtain ⟨hcode_eq, -, -, -, -, -⟩ := loads_fields himg
  obtain ⟨_, _, hholds⟩ := Program.codeLoaded_iff.mp hcl
  dsimp only [Program.ofImageWithSvc] at hholds
  rw [hcode_eq] at hholds
  obtain ⟨o', ho'_mem, ho'_eq⟩ := List.any_eq_true.mp hdead
  have ho_mem : (pc - img.base).toNat ∈ lsDeadImgStubOffs := (eq_of_beq ho'_eq) ▸ ho'_mem
  set o := (pc - img.base).toNat
  obtain ⟨_, hle4, hb0, hb1, hb2, hb3⟩ := checkDeadStubZeroWords_spec lsDeadStubZeroWords_ok o ho_mem
  have hpc_eq : img.base + BitVec.ofNat 64 o = pc := by
    dsimp only [o]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_lin
  have hread_at : ∀ j (hj : o + j < libsignalSessionImage.code.length),
      libsignalSessionImage.code.getD (o + j) 1#8 = 0#8 →
      m.read8 (pc + BitVec.ofNat 64 j) = 0#8 := by
    intro j hj hgetd
    have haddr : pc + BitVec.ofNat 64 j = img.base + BitVec.ofNat 64 (o + j) := by
      rw [← hpc_eq, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [haddr, (hholds (o + j) hj).1, ← Obj.Interned.getD_of_lt (d := 1#8) hj, hgetd]
  have hr0 := hread_at 0 (by omega) (by simpa using hb0)
  have hr1 := hread_at 1 (by omega) hb1
  have hr2 := hread_at 2 (by omega) hb2
  have hr3 := hread_at 3 (by omega) hb3
  have hr32 : m.read32 pc = 0#32 := by
    unfold Memory.read32
    change m.read8 (pc + BitVec.ofNat 64 3) ++ m.read8 (pc + BitVec.ofNat 64 2) ++
        m.read8 (pc + BitVec.ofNat 64 1) ++ m.read8 (pc + BitVec.ofNat 64 0) = 0#32
    rw [hr3, hr2, hr1, hr0]
    rfl
  have hdec : Arm64.decode (m.read32 pc) = none := by
    rw [hr32]; exact decode_zero_word_eq_none
  unfold Program.fetchMem
  split_ifs <;> simp [hdec]

end CryptoVerification.SignalSession.Cli.MainHops.CliImgPlacement
