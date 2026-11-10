/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Tests.AEAD.HMACTest
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import GeneratedLean.LibsignalSessionObj
public meta import Computational.Tests.AEAD.HMACTest -- shake: keep
public meta import LibsignalBinary.Specifications.LibsignalTripleRatchet -- shake: keep
public meta import GeneratedLean.LibsignalSessionObj -- shake: keep

/-!
# Executable Run Tests for the Triple-Ratchet Session Entry Points

Executes the linked session image `CryptoVerification.libsignalSessionImage` (loaded at `0x400000`)
as `Program.ofImage img (Rust.withPanics (tripleRatchetExterns C ctl abs))` on an Alice/Bob
scenario and checks every output byte and heap block against the `LibsignalTripleRatchet`
specifications and `LibsignalSession` model. Uses reference SHA-256, AES-256, and X25519
primitives, an empty-state SPQR model, and concrete allocator/prost/CBC/format hook witnesses
emitting `userDefined` trace events for heap-balance verification.
-/

@[expose] public section

namespace CryptoVerification.TripleRatchetRun

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HMAC.Tests CryptoGames.HKDF
open CryptoGames.CBC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec

open Lean Meta in
/-- Extracts bytes from a `List (BitVec 8)` literal `[BitVec.ofNat 8 b, …]`. -/
meta partial def byteLits (e : Expr) (acc : Array UInt8 := #[]) : MetaM (Array UInt8) := do
  match e.consumeMData.getAppFnArgs with
  | (``List.nil, _) => return acc
  | (``List.cons, #[_, hd, tl]) =>
    match hd.consumeMData.getAppFnArgs with
    | (``BitVec.ofNat, #[_, n]) =>
      match n.consumeMData.rawNatLit? <|> n.consumeMData.nat? with
      | some v => byteLits tl (acc.push v.toUInt8)
      | none => throwError "byteLits: not a literal {n}"
    | _ => throwError "byteLits: unexpected element {hd}"
  | _ => throwError "byteLits: unexpected {e}"

open Lean in
private meta partial def inlineNoncomputable (env : Environment) (e : Expr) : Expr :=
  e.replace fun
    | .const c [] =>
      if isNoncomputable env c then
        match env.find? c with
        | some (.defnInfo d) => some (inlineNoncomputable env d.value)
        | _ => none
      else none
    | _ => none

/-- The nearest ancestor directory of `f` that contains `lakefile.lean` (the package root), or
`.` if there is none. -/
private meta partial def lakeRootOf (f : System.FilePath) : IO System.FilePath := do
  match f.parent with
  | none => return "."
  | some d => if (← (d / "lakefile.lean").pathExists) then return d else lakeRootOf d

open Lean Elab Term in
/-- The directory of the generated image files, `<package>/.GeneratedLean/GeneratedLean`. -/
elab "s2run_gen_dir%" : term => do
  let f ← IO.FS.realPath (← getFileName)
  let root ← lakeRootOf f
  return Lean.mkStrLit (root / ".GeneratedLean" / "GeneratedLean").toString

open Lean Meta Elab Term in
/-- `s2run_image_with_bins% li "code.bin" "data.bin"`: the value of the `noncomputable` linked
image `li` as a computable function of its `code` and `data` fields. Fails to elaborate unless
the `code` / `data` literals of `li` are byte-for-byte the two files. -/
elab "s2run_image_with_bins% " id:ident codeF:str dataF:str : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let some (.defnInfo d) := (← getEnv).find? n | throwError "`{n}` is not a definition"
  let v := d.value.consumeMData
  let args := v.getAppArgs
  unless v.getAppFn.isConstOf ``Obj.LinkedImage.mk && args.size == 13 do
    throwError "unexpected shape of {n}"
  let f ← IO.FS.realPath (← getFileName)
  let root ← lakeRootOf f
  let dir := root / ".GeneratedLean" / "GeneratedLean"
  for (i, file) in [(0, codeF.getString), (2, dataF.getString)] do
    let lit ← byteLits args[i]!
    let bytes ← IO.FS.readBinFile (dir / file)
    unless lit == bytes.data do
      throwError "s2run_image_with_bins%: field {i} of {n} differs from {file}"
  let env ← getEnv
  let ty := mkApp (mkConst ``List [Level.zero]) (mkApp (mkConst ``BitVec) (mkNatLit 8))
  withLocalDeclD `code ty fun c => withLocalDeclD `data ty fun dt => do
    let args' := args.mapIdx fun i a =>
      if i == 0 then c else if i == 2 then dt else inlineNoncomputable env a
    mkLambdaFVars #[c, dt] (mkAppN v.getAppFn args')

set_option maxRecDepth 100000 in
/-- `libsignalSessionImage` as a function of its `code` / `data` (checked against the `.bin`s). -/
def mkImage : List (BitVec 8) → List (BitVec 8) → Obj.LinkedImage :=
  s2run_image_with_bins% CryptoVerification.libsignalSessionImage
    "LibsignalSessionObj.code.bin" "LibsignalSessionObj.data.bin"

def testBase : BitVec 64 := 0x400000#64

def readBin (f : String) : IO (List (BitVec 8)) := do
  let b ← IO.FS.readBinFile (System.FilePath.mk s2run_gen_dir% / f)
  return b.data.toList.map fun x => BitVec.ofNat 8 x.toNat

def loadImg : IO Obj.Image := do
  let li := mkImage (← readBin "LibsignalSessionObj.code.bin")
    (← readBin "LibsignalSessionObj.data.bin")
  match li.load testBase with
  | .ok img => return img
  | .error e => throw (IO.userError s!"load failed: {e}")

def progress (msg : String) : IO Unit := do
  let h ← IO.FS.Handle.mk "/tmp/s2run.progress" .append
  h.putStrLn msg
  h.flush

def le (n : ℕ) (v : ℕ) : List (BitVec 8) := (List.range n).map fun i => BitVec.ofNat 8 (v / 256 ^ i)
def le64 (v : BitVec 64) : List (BitVec 8) := le 8 v.toNat

def hexOf (l : List (BitVec 8)) : String :=
  String.join (l.map fun b =>
    let d (n : ℕ) : Char := "0123456789abcdef".toList[n]!
    String.ofList [d (b.toNat / 16), d (b.toNat % 16)])

def hexDigit (c : Char) : ℕ :=
  if c.isDigit then c.toNat - 48 else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 87 else 0

def hexStr (s : String) : List (BitVec 8) :=
  let rec go : List Char → List (BitVec 8)
    | a :: b :: r => BitVec.ofNat 8 (16 * hexDigit a + hexDigit b) :: go r
    | _ => []
  go s.toList

/-- Converts a byte list to a 32-byte vector, defaulting to zero if `l.length ≠ 32`. -/
def vec32 (l : List (BitVec 8)) : List.Vector (BitVec 8) 32 :=
  if h : l.length = 32 then ⟨l, h⟩ else ⟨List.replicate 32 0, by simp⟩

/-- Multiplication by `x` in GF(2⁸) modulo `x⁸ + x⁴ + x³ + x + 1` (FIPS 197). -/
def xtime (a : ℕ) : ℕ := let b := (a <<< 1) &&& 0xff; if a &&& 0x80 ≠ 0 then b ^^^ 0x1b else b

def gmul (a b : ℕ) : ℕ := Id.run do
  let mut a := a; let mut b := b; let mut p := 0
  for _ in [0:8] do
    if b &&& 1 ≠ 0 then p := p ^^^ a
    a := xtime a; b := b >>> 1
  return p

/-- Multiplicative inverse in GF(2⁸) with `0 ↦ 0`. -/
def ginv (a : ℕ) : ℕ := ((List.range 256).find? fun b => gmul a b == 1).getD 0

def rotl8 (b n : ℕ) : ℕ := ((b <<< n) ||| (b >>> (8 - n))) &&& 0xff

/-- AES S-box (FIPS 197 §5.1.1). -/
def sbox : Array ℕ := (Array.range 256).map fun x =>
  let b := ginv x; b ^^^ rotl8 b 1 ^^^ rotl8 b 2 ^^^ rotl8 b 3 ^^^ rotl8 b 4 ^^^ 0x63

def invSbox : Array ℕ := (Array.range 256).foldl (fun acc x => acc.set! sbox[x]! x) (Array.replicate 256 0)

/-- AES-256 key expansion (FIPS 197 §5.2, `Nk = 8`, `Nr = 14`), producing 240 bytes. -/
def expandKey (key : Array ℕ) : Array ℕ := Id.run do
  let rcon := #[0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40]
  let mut w := key
  for i in [8:60] do
    let t0 := w[4 * (i - 1)]!; let t1 := w[4 * (i - 1) + 1]!
    let t2 := w[4 * (i - 1) + 2]!; let t3 := w[4 * (i - 1) + 3]!
    let (a, b, c, d) :=
      if i % 8 == 0 then (sbox[t1]! ^^^ rcon[i / 8 - 1]!, sbox[t2]!, sbox[t3]!, sbox[t0]!)
      else if i % 8 == 4 then (sbox[t0]!, sbox[t1]!, sbox[t2]!, sbox[t3]!)
      else (t0, t1, t2, t3)
    w := ((((w.push (w[4 * (i - 8)]! ^^^ a)).push (w[4 * (i - 8) + 1]! ^^^ b)).push
      (w[4 * (i - 8) + 2]! ^^^ c)).push (w[4 * (i - 8) + 3]! ^^^ d))
  return w

def addRK (s w : Array ℕ) (r : ℕ) : Array ℕ := (Array.range 16).map fun i => s[i]! ^^^ w[16 * r + i]!
def subB (s : Array ℕ) : Array ℕ := s.map fun x => sbox[x]!
def invSubB (s : Array ℕ) : Array ℕ := s.map fun x => invSbox[x]!
/-- ShiftRows on column-major state (`s[r + 4c]`). -/
def shiftR (s : Array ℕ) : Array ℕ := (Array.range 16).map fun i =>
  let r := i % 4; let c := i / 4; s[r + 4 * ((c + r) % 4)]!
def invShiftR (s : Array ℕ) : Array ℕ := (Array.range 16).map fun i =>
  let r := i % 4; let c := i / 4; s[r + 4 * ((c + 4 - r) % 4)]!
def mixC (s : Array ℕ) : Array ℕ := (Array.range 16).map fun i =>
  let r := i % 4; let c := i / 4; let a := fun k => s[(r + k) % 4 + 4 * c]!
  gmul 2 (a 0) ^^^ gmul 3 (a 1) ^^^ a 2 ^^^ a 3
def invMixC (s : Array ℕ) : Array ℕ := (Array.range 16).map fun i =>
  let r := i % 4; let c := i / 4; let a := fun k => s[(r + k) % 4 + 4 * c]!
  gmul 14 (a 0) ^^^ gmul 11 (a 1) ^^^ gmul 13 (a 2) ^^^ gmul 9 (a 3)

/-- AES-256 block encryption with expanded key `w` (FIPS 197 §5.1). -/
def aesEnc (w s : Array ℕ) : Array ℕ := Id.run do
  let mut s := addRK s w 0
  for r in [1:14] do s := addRK (mixC (shiftR (subB s))) w r
  return addRK (shiftR (subB s)) w 14

/-- AES-256 block decryption (FIPS 197 §5.3). -/
def aesDec (w s : Array ℕ) : Array ℕ := Id.run do
  let mut s := addRK s w 14
  for j in [0:13] do s := invMixC (addRK (invSubB (invShiftR s)) w (13 - j))
  return addRK (invSubB (invShiftR s)) w 0

def toNats (l : List (BitVec 8)) : Array ℕ := (l.map BitVec.toNat).toArray
def ofNats (a : Array ℕ) : List (BitVec 8) := a.toList.map (BitVec.ofNat 8)

/-- AES-256 block encryption with little-endian 32-byte key and 16-byte block conventions. -/
def aesE (k : AesKey) (b : Block) : Block :=
  bytesToBlock (ofNats (aesEnc (expandKey (toNats (keyToBytes32 k))) (toNats (blockToBytesLE b))))
def aesD (k : AesKey) (b : Block) : Block :=
  bytesToBlock (ofNats (aesDec (expandKey (toNats (keyToBytes32 k))) (toNats (blockToBytesLE b))))

def P : ℕ := 2 ^ 255 - 19
def powMod (b e m : ℕ) : ℕ :=
  ((List.range 256).foldl (fun (acc, sq) i =>
    (if e.testBit i then acc * sq % m else acc, sq * sq % m)) (1, b % m)).1
def leNat (l : List (BitVec 8)) : ℕ := l.foldr (fun b acc => b.toNat + 256 * acc) 0
def natLE32 (n : ℕ) : List (BitVec 8) := (List.range 32).map fun i => BitVec.ofNat 8 (n / 256 ^ i)

/-- RFC 7748 §5 Montgomery ladder `X25519(k, u)`. -/
def x25519Nat (k u : List (BitVec 8)) : ℕ := Id.run do
  let kc := leNat k
  let kc := (kc - kc % 8) % 2 ^ 255 ||| 2 ^ 254
  let x1 := leNat u % 2 ^ 255
  let mut x2 := 1; let mut z2 := 0; let mut x3 := x1; let mut z3 := 1; let mut swap := false
  for j in List.range 255 do
    let t := 254 - j
    let kt := kc.testBit t
    if swap != kt then
      (x2, x3) := (x3, x2); (z2, z3) := (z3, z2)
    swap := kt
    let a := (x2 + z2) % P; let b := (x2 + P - z2) % P
    let aa := a * a % P; let bb := b * b % P
    let e := (aa + P - bb) % P
    let c := (x3 + z3) % P; let d := (x3 + P - z3) % P
    let da := d * a % P; let cb := c * b % P
    x3 := (da + cb) * (da + cb) % P
    z3 := x1 * ((da + P - cb) * (da + P - cb) % P) % P
    x2 := aa * bb % P
    z2 := e * ((aa + 121665 * e) % P) % P
  if swap then
    (x2, x3) := (x3, x2); (z2, z3) := (z3, z2)
  return x2 * powMod z2 (P - 2) P % P

def x25519Ref : Ratchet.X25519Fn := fun k u => ⟨natLE32 (x25519Nat k.toList u.toList), by simp [natLE32]⟩

def pubKeyRef : PubKeyFn := fun k => x25519Ref k (vec32 (9 :: List.replicate 31 0))

/-- Bump allocator base address; cursor offset is stored at `heapCur`. -/
def heapBase : BitVec 64 := 0x50000000#64
def heapCap : ℕ := 0x1000000
def heapCur : BitVec 64 := 0x4fff0000#64

def heapEv (tag : String) (p : BitVec 64) (n a : ℕ) : TraceEvent :=
  .userDefined tag (le64 p ++ le 8 n ++ le 8 a)

def bump (s : State) (n a : ℕ) : State × BitVec 64 :=
  let cur := (s.mem.read64 heapCur).toNat
  let off := (cur + a - 1) / a * a
  if off + n ≤ heapCap then
    let p := heapBase + BitVec.ofNat 64 off
    ({ s.setMem (s.mem.write64 heapCur (BitVec.ofNat 64 (off + n))) with
        trace := s.trace ++ [heapEv "alloc" p n a] }, p)
  else (s, 0#64)

def allocHook (s : State) : State :=
  let (s', p) := bump s (s.readReg64 .x0).toNat (s.readReg64 .x1).toNat
  retHook (fun _ => s'.writeReg64 .x0 p) s

def deallocHook (s : State) : State :=
  retHook (fun s => { s with trace := s.trace ++
    [heapEv "dealloc" (s.readReg64 .x0) (s.readReg64 .x1).toNat (s.readReg64 .x2).toNat] }) s

def reallocHook (s : State) : State :=
  let p := s.readReg64 .x0
  let old := (s.readReg64 .x1).toNat
  let a := (s.readReg64 .x2).toNat
  let new := (s.readReg64 .x3).toNat
  let (s1, q) := bump s new a
  if q = 0 then retHook (fun _ => s.writeReg64 .x0 0) s else
  let s2 := s1.setMem (s1.mem.writeBytes q (s1.mem.readBytes p (min old new)))
  retHook (fun _ => { s2 with trace := s2.trace ++ [heapEv "dealloc" p old a] }.writeReg64 .x0 q) s

def mark (s : State) (tag : String) (pl : List (BitVec 8) := []) : State :=
  { s with trace := s.trace ++ [.userDefined tag pl] }

/-- Allocator block `(ptr, size, align)`. -/
abbrev Buf := BitVec 64 × ℕ × ℕ

def decEv (tag : String) : TraceEvent → Option Buf
  | .userDefined t pl =>
    if t = tag then
      let w (i : ℕ) : ℕ := (pl.drop (8 * i)).take 8 |>.foldr (fun b acc => b.toNat + 256 * acc) 0
      some (BitVec.ofNat 64 (w 0), w 1, w 2)
    else none
  | _ => none

def sameBufs (a b : List Buf) : Bool :=
  a.length == b.length && a.all fun x => a.count x == b.count x

/-- Allocates a `Box<Inner>` (72 bytes, align 8) holding `kind` (48 bytes) and an empty stack
`Vec { cap: 0, ptr: 8, len: 0 }`. -/
def newDecodeError (s : State) (kind : List (BitVec 8)) : State × BitVec 64 :=
  let (s1, p) := bump s 72 8
  let m := ((((s1.mem.write64 p 0).write64 (p + 8) 8).write64 (p + 16) 0)).writeBytes (p + 24) kind
  (s1.setMem m, p)

/-- Hook for `<DecodeError as From<DecodeErrorKind>>::from(x0 = &kind)`. -/
def decodeErrorFromHook (s : State) : State :=
  let kind := s.mem.readBytes (s.readReg64 .x0) 48
  let s := mark s "decode_error" (kind.take 8)
  let (s1, e) := newDecodeError s kind
  retHook (fun _ => s1.writeReg64 .x0 e) s

/-- Hook for `<DecodeError>::push(x0 = &mut DecodeError, (x1, x2) = message, (x3, x4) = field)`. -/
def decodeErrorPushHook (s : State) : State :=
  let inner := s.mem.read64 (s.readReg64 .x0)
  let cap := (s.mem.read64 inner).toNat
  let ptr := s.mem.read64 (inner + 8)
  let len := (s.mem.read64 (inner + 16)).toNat
  let field := s.mem.readBytes (s.readReg64 .x3) (s.readReg64 .x4).toNat
  let msg := s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat
  let s := mark s "push" (msg ++ [0x2e] ++ field)
  let entry := le64 (s.readReg64 .x1) ++ le64 (s.readReg64 .x2) ++ le64 (s.readReg64 .x3) ++
    le64 (s.readReg64 .x4)
  let (s1, cap', ptr') :=
    if len < cap then (s, cap, ptr) else
      let nc := max 4 (2 * cap)
      let (s1, q) := bump s (nc * 32) 8
      let s1 := s1.setMem (s1.mem.writeBytes q (s1.mem.readBytes ptr (len * 32)))
      let s1 := if cap = 0 then s1 else
        { s1 with trace := s1.trace ++ [heapEv "dealloc" ptr (cap * 32) 8] }
      (s1, nc, q)
  let m := (((s1.mem.writeBytes (ptr' + BitVec.ofNat 64 (len * 32)) entry).write64 inner
    (BitVec.ofNat 64 cap')).write64 (inner + 8) ptr').write64 (inner + 16)
    (BitVec.ofNat 64 (len + 1))
  retHook (fun _ => s1.setMem m) s

/-- Image memory: code `r-x`, data with its permissions, GOT `r--`, and all other bytes zero and
read-write (so `log::MAX_LOG_LEVEL_FILTER` reads `0` = `Off`). -/
def imgMem (img : Obj.Image) : Memory :=
  let code := img.code.toArray
  let data := img.data.toArray
  let got := img.gotBytes.toArray
  Memory.ofFn
    (fun a =>
      let i := (a - img.base).toNat
      let j := (a - img.dataAddr).toNat
      let k := (a - img.gotAddr).toNat
      if i < code.size then code[i]! else if j < data.size then data[j]!
      else if k < got.size then got[k]! else 0)
    (fun a =>
      if (a - img.base).toNat < code.size then some .rx
      else if (a - img.dataAddr).toNat < data.size then img.dataPerm a
      else if (a - img.gotAddr).toNat < got.size then some .ro else some .rw)

def retAddr : BitVec 64 := 0x00dead00#64
def stackTop : BitVec 64 := 0x70000000#64

def callState (img : Obj.Image) (entry : BitVec 64) (m : Memory) (regs : List (Reg × BitVec 64)) :
    State :=
  let s : State := { sp := stackTop, pc := entry, mem := m, symtab := img.symtab }
  (regs.foldl (fun s (r, v) => s.writeReg64 r v) s).writeReg64 .lr retAddr

def returned (sf : State) : Bool := sf.pc == retAddr && sf.status == .Running
def snap (m : Memory) (a : BitVec 64) (n : ℕ) : Array (BitVec 8) := Id.run do
  let mut r : Array (BitVec 8) := Array.mkEmpty n
  for i in [0:n] do
    r := r.push (m.read8 (a + BitVec.ofNat 64 i))
  return r

/-- Overlays `base` with the bytes of `m` on `regions` at closure depth 1. -/
def compact (base m : Memory) (regions : List (BitVec 64 × ℕ)) : Memory :=
  let snaps := regions.map fun (a, n) => (a, snap m a n)
  Memory.ofFn
    (fun x =>
      match snaps.find? (fun (a, arr) => (x - a).toNat < arr.size) with
      | some (a, arr) => arr[(x - a).toNat]!
      | none => base.read8 x)
    base.perm

/-- Writes a fresh owned `Vec<u8>` holding `bs` at header `hdr` (`cap = len`; empty is `{0, 1, 0}`
with no allocation). -/
def newVecAt (s : State) (hdr : BitVec 64) (bs : List (BitVec 8)) : State :=
  if bs = [] then s.setMem (((s.mem.write64 hdr 0).write64 (hdr + 8) 1).write64 (hdr + 16) 0)
  else
    let (s1, p) := bump s bs.length 1
    s1.setMem ((((s1.mem.writeBytes p bs).write64 hdr (BitVec.ofNat 64 bs.length)).write64
      (hdr + 8) p).write64 (hdr + 16) (BitVec.ofNat 64 bs.length))

/-- Marks violations of the `AesCall.pre` register shape (`x3 = 32`, `x5 = 16`) in the trace. -/
def aesShapeMark (s : State) : State :=
  if s.readReg64 .x3 = 32 ∧ s.readReg64 .x5 = 16 then s else mark s "aes_pre_violated"

/-- Hook for AES-256-CBC encrypt (`aesEncSpec`). -/
def aesEncHook (E : AesKey → Block → Block) (s : State) : State :=
  let input := s.mem.readBytes (s.readReg64 .x0) (s.readReg64 .x1).toNat
  let key := s.mem.readBytes (s.readReg64 .x2) 32
  let iv := s.mem.readBytes (s.readReg64 .x4) 16
  let ct := aesCbcEncrypt E (bytesToKey32 key) (bytesToBlock iv) input
  let s := mark (aesShapeMark s) "aes_enc"
  retHook (fun s => newVecAt s (s.readReg64 .x8) ct) s

/-- Non-null `&'static str` pointer for decrypt failure (`BadCiphertext`). -/
def aesFailStrA : BitVec 64 := 0x4ffe0000#64

/-- Hook for AES-256-CBC decrypt (`aesDecSpec`): writes a fresh `Vec` on `some pt`, or `errTag` at
word 0 and `(aesFailStrA, 6)` at `+8..+24` on `none`. -/
def aesDecHook (D : AesKey → Block → Block) (s : State) : State :=
  let input := s.mem.readBytes (s.readReg64 .x0) (s.readReg64 .x1).toNat
  let key := s.mem.readBytes (s.readReg64 .x2) 32
  let iv := s.mem.readBytes (s.readReg64 .x4) 16
  let s := mark (aesShapeMark s) "aes_dec"
  match aesCbcDecrypt D (bytesToKey32 key) (bytesToBlock iv) input with
  | some pt => retHook (fun s => newVecAt s (s.readReg64 .x8) pt) s
  | none => retHook (fun s =>
      let r := s.readReg64 .x8
      s.setMem (((s.mem.write64 r errTag).write64 (r + 8) aesFailStrA).write64 (r + 16) 6)) s

/-- Hook for `spqr::recv(x0 = &Vec state, x1 = &Vec msg)` (`spqrRecvSpec`, `spqrRecvResultAt`). -/
def spqrRecvHook (recv : List (BitVec 8) → List (BitVec 8) → Except Bool (List (BitVec 8) × Salt))
    (s : State) : State :=
  let rv (h : BitVec 64) := s.mem.readBytes (s.mem.read64 (h + 8)) (s.mem.read64 (h + 16)).toNat
  let s := mark s "spqr_recv"
  match recv (rv (s.readReg64 .x0)) (rv (s.readReg64 .x1)) with
  | .ok (st', key) => retHook (fun s =>
      let r := s.readReg64 .x8
      let s := newVecAt s r st'
      match key with
      | none => s.setMem (s.mem.write64 (r + 24) noneCap)
      | some k => newVecAt s (r + 24) k.toList) s
  | .error sd => retHook (fun s =>
      let r := s.readReg64 .x8
      s.setMem ((s.mem.write64 r errTag).write8 (r + 8) (if sd then 0 else 1))) s

/-- Hook for `format_inner` (`formatInnerSpec`), writing a fresh `String` `"fmt"`. -/
def formatInnerHook (s : State) : State :=
  retHook (fun s => newVecAt s (s.readReg64 .x8) (utf8 "fmt")) (mark s "format_inner")

/-- Hook for `core::fmt::write` (`fmtWriteSpec`), writing `"addr"` if empty and returning `w0 = 0`. -/
def fmtWriteHook (s : State) : State :=
  let s := mark s "fmt_write"
  retHook (fun s =>
    let v := s.readReg64 .x0
    let s := if s.mem.read64 v = 0 then newVecAt s v (utf8 "addr") else s
    s.writeReg64 .x0 0) s

/-- Hook for `spqr::decode_state(x0 = &Vec state)` on the empty state (`spqr/src/lib.rs:495–501`),
writing `Ok(PqRatchetState { inner: None, version_negotiation: None, chain: None })` (word 0 = `-1`,
word `+0x30` = `-1`, word `+0x80` = `-3`); halts on non-empty input. -/
def decodeStateHook (s : State) : State :=
  if (s.mem.read64 (s.readReg64 .x0 + 16)) ≠ 0 then { s with status := .Halted } else
  retHook (fun s =>
    let r := s.readReg64 .x8
    s.setMem (((s.mem.write64 r noneCap).write64 (r + 0x30) noneCap).write64 (r + 0x80)
      0xFFFFFFFFFFFFFFFD#64)) (mark s "decode_state")

/-- Empty-state SPQR 1.6.0 model (`V0`). -/
def S : SpqrModel where
  send := fun st _ => if st = [] then some ([], none, []) else none
  draws := fun _ _ => 0
  recv := fun st msg => if st = [] ∧ msg = [] then .ok ([], none) else .error false
  recvPanics := fun _ _ => false
  sendPanics := fun _ _ => false

/-- Hook for `__rust_alloc_zeroed(size = x0, align = x1)` (`rustAllocZeroedSpec`). -/
def allocZeroedHook (s : State) : State :=
  let n := (s.readReg64 .x0).toNat
  let (s', p) := bump (mark s "alloc_zeroed") n (s.readReg64 .x1).toNat
  let s' := if p = 0 then s' else s'.setMem (s'.mem.writeBytes p (List.replicate n 0))
  retHook (fun _ => s'.writeReg64 .x0 p) s

def Cr : Crypto := ⟨sha256Compress, aesE, aesD, x25519Ref, pubKeyRef⟩

def abs : String → Option (State → State) := fun sym =>
  if sym = "__rustc::__rust_alloc" then some allocHook
  else if sym = "__rustc::__rust_dealloc" then some deallocHook
  else if sym = "__rustc::__rust_realloc" then some reallocHook
  else if sym = allocZeroedName then some allocZeroedHook
  else if sym = decodeErrorFromName then some decodeErrorFromHook
  else if sym = decodeErrorPushName then some decodeErrorPushHook
  else if sym = aesEncName then some (aesEncHook Cr.E)
  else if sym = aesDecName then some (aesDecHook Cr.D)
  else if sym = spqrRecvName then some (spqrRecvHook S.recv)
  else if sym = formatInnerName then some formatInnerHook
  else if sym = fmtWriteName then some fmtWriteHook
  else if sym = decodeStateName then some decodeStateHook
  else none

def hexVal? (c : Char) : Option ℕ :=
  if c.isDigit then some (c.toNat - 48) else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87) else none

def hexPairs : List Char → Option (List (BitVec 8))
  | [] => some []
  | a :: b :: r => do
    let x ← hexVal? a; let y ← hexVal? b
    return BitVec.ofNat 8 (16 * x + y) :: (← hexPairs r)
  | _ => none

/-- Parses a lowercase hyphenated UUID string `8-4-4-4-12`. -/
def parseUuid (cs : List Char) : Option (List.Vector (BitVec 8) 16) := do
  unless cs.length = 36 ∧ [8, 13, 18, 23].all (fun i => cs[i]? = some '-') do none
  let bs ← hexPairs (cs.filter (· ≠ '-'))
  if h : bs.length = 16 then some ⟨bs, h⟩ else none

def parse : UuidParser := fun name =>
  parseUuid (name.map fun b => Char.ofNat b.toNat)

/-- Tape control block address (`tapeAt`); tape bytes start at `tapeA`. -/
def ctlA : BitVec 64 := 0x4ffd0000#64
def tapeA : BitVec 64 := 0x4ffd0100#64

def progOf (img : Obj.Image) : Program := tripleRatchetProg img Cr ctlA abs

/-- Pre-decoded instruction words, hooks, and stub names of `progOf img`, indexed by word offset. -/
structure Runner where
  prog : Program
  words : Array (BitVec 32)
  hooks : Array (Option (State → State))
  stubName : Array (Option String)
  sendA : BitVec 64

def Runner.ofImage (img : Obj.Image) : Runner :=
  let P := progOf img
  let code := img.code.toArray
  let nw := code.size / 4
  let words := Id.run do
    let mut w : Array (BitVec 32) := Array.mkEmpty nw
    for i in [0:nw] do
      w := w.push (code[4 * i + 3]! ++ code[4 * i + 2]! ++ code[4 * i + 1]! ++ code[4 * i]!)
    return w
  -- `Program.ofImage` has no overrides, so `hookAtOff?` only returns hooks at stub offsets.
  let (hooks, names) := Id.run do
    let mut h : Array (Option (State → State)) := Array.replicate nw none
    let mut n : Array (Option String) := Array.replicate nw none
    for (name, o) in img.stubs do
      if o % 4 = 0 ∧ o / 4 < nw then
        h := h.set! (o / 4) (P.hookAtOff? o)
        n := n.set! (o / 4) (some name)
    return (h, n)
  { prog := P, words, hooks, stubName := names, sendA := entryOf img spqrSendName }

def Runner.step (R : Runner) (s : State) : State :=
  let off := (s.pc - R.prog.base).toNat
  let inCode := off < 4 * R.words.size
  match (if inCode ∧ off % 4 = 0 then R.hooks[off / 4]! else none) with
  | some f => f s
  | none =>
    if inCode then
      if off % 4 ≠ 0 then { s with status := .Halted } else
      match Arm64.decode R.words[off / 4]! with
      | some inst => execInst inst s
      | none => { s with status := .Halted }
    else
      match R.prog.fetchMem s.mem s.pc with
      | some inst => execInst inst s
      | none => { s with status := .Halted }

/-- Execution trace summary of the in-image `spqr::send::<HookRng>` call: entry registers, input
state `Vec` and tape state, 72-byte sret and return tape state, minimum `sp`, step count, and
reached stubs. -/
structure SendObs where
  sp0 : BitVec 64
  lr0 : BitVec 64
  ret : BitVec 64
  stHdr : BitVec 64
  stBytes : List (BitVec 8)
  ctl0 : BitVec 64 × BitVec 64
  k0 : ℕ
  minSp : BitVec 64
  stubs : List String := []
  done : Bool := false
  steps : ℕ := 0
  retBytes : List (BitVec 8) := []
  ctl1 : BitVec 64 × BitVec 64 := (0, 0)
  framed : Bool := false

def SendObs.start (s : State) (k : ℕ) : SendObs :=
  let st := s.readReg64 .x1
  let bytes := s.mem.readBytes (s.mem.read64 (st + 8)) (s.mem.read64 (st + 16)).toNat
  { sp0 := s.sp, lr0 := s.readReg64 .lr, ret := s.readReg64 .x0, stHdr := st, stBytes := bytes
    ctl0 := (s.mem.read64 ctlA, s.mem.read64 (ctlA + 8)), k0 := k, minSp := s.sp }

/-- Run outcome: final state, step count, lowest `sp`, distinct stubs reached in order, halting
stub (if any), and `spqr::send` observation. -/
structure RunOut where
  sf : State
  steps : ℕ
  minSp : BitVec 64
  stubs : List String
  haltStub : Option String
  send : Option SendObs

def calleeSaved : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .fp]

def SendObs.finish (o : SendObs) (s : State) (k : ℕ) (cs0 : List (BitVec 64)) : SendObs :=
  { o with done := true, steps := k - o.k0, retBytes := s.mem.readBytes o.ret 72
           ctl1 := (s.mem.read64 ctlA, s.mem.read64 (ctlA + 8))
           framed := calleeSaved.map s.readReg64 == cs0 }

/-- Steps until `retAddr`, panic, or halt, compacting `regions s` every `every` steps (`0` = never). -/
def fastRun (R : Runner) (base : Memory) (regions : State → List (BitVec 64 × ℕ)) (every : ℕ)
    (fuel : ℕ) (s : State) : RunOut := Id.run do
  let mut s := s
  let mut k := 0
  let mut minSp := s.sp
  let mut stubs : List String := []
  let mut haltStub : Option String := none
  let mut send : Option SendObs := none
  let mut sendCs : List (BitVec 64) := []
  for _ in [0:fuel] do
    if s.pc == retAddr || s.status != .Running then break
    let off := (s.pc - R.prog.base).toNat
    let name := if off % 4 = 0 ∧ off / 4 < R.stubName.size then R.stubName[off / 4]! else none
    if let some n := name then
      unless stubs.contains n do stubs := stubs ++ [n]
      if let some o := send then
        unless o.done || o.stubs.contains n do send := some { o with stubs := o.stubs ++ [n] }
      if R.hooks[off / 4]!.isNone then
        haltStub := some n
        s := { s with status := .Halted }
        break
    if s.pc == R.sendA ∧ send.isNone then
      send := some (SendObs.start s k)
      sendCs := calleeSaved.map s.readReg64
    s := R.step s
    k := k + 1
    if s.sp.toNat < minSp.toNat then minSp := s.sp
    if let some o := send then
      unless o.done do
        let o := if s.sp.toNat < o.minSp.toNat then { o with minSp := s.sp } else o
        if s.pc == o.lr0 ∧ s.sp == o.sp0 then
          send := some (o.finish s k sendCs)
        else send := some o
    if every ≠ 0 ∧ k % every = 0 then
      s := { s with mem := compact base s.mem (regions s) }
  return { sf := s, steps := k, minSp, stubs, haltStub, send }

def RunOut.depth (r : RunOut) : ℕ := stackTop.toNat - r.minSp.toNat

/-- Input arena tracking memory, next free address, and live input allocator blocks `(ptr, size, align)`. -/
structure Arena where
  mem : Memory
  cur : BitVec 64
  live : List Buf := []

def arenaA : BitVec 64 := 0x30000000#64

/-- Reserves `n` raw 8-aligned bytes outside the allocator block list. -/
def Arena.raw (a : Arena) (n : ℕ) : Arena × BitVec 64 :=
  let p := a.cur
  ({ a with cur := p + BitVec.ofNat 64 ((n + 7) / 8 * 8 + 8) }, p)

/-- Allocates a live block of `n` bytes (`n = 0` returns dangling pointer `align` without recording a block). -/
def Arena.block (a : Arena) (n align : ℕ) : Arena × BitVec 64 :=
  if n = 0 then (a, BitVec.ofNat 64 align) else
  let (a, p) := a.raw n
  ({ a with live := a.live ++ [(p, n, align)] }, p)

def Arena.w64 (a : Arena) (p : BitVec 64) (v : BitVec 64) : Arena := { a with mem := a.mem.write64 p v }
def Arena.w32 (a : Arena) (p : BitVec 64) (v : BitVec 32) : Arena := { a with mem := a.mem.write32 p v }
def Arena.w8 (a : Arena) (p : BitVec 64) (v : BitVec 8) : Arena := { a with mem := a.mem.write8 p v }
def Arena.wb (a : Arena) (p : BitVec 64) (bs : List (BitVec 8)) : Arena :=
  { a with mem := a.mem.writeBytes p bs }

/-- Writes a `Vec<u8>` header at `hdr` holding `bs` with `slack` spare capacity. -/
def Arena.vecU8 (a : Arena) (hdr : BitVec 64) (bs : List (BitVec 8)) (slack : ℕ := 0) : Arena :=
  let cap := bs.length + slack
  let (a, p) := a.block cap 1
  ((a.wb p bs).w64 hdr (BitVec.ofNat 64 cap) |>.w64 (hdr + 8) p).w64 (hdr + 16)
    (BitVec.ofNat 64 bs.length)

/-- Writes a `Box<[u8]>` `(ptr, len)` at `a0`. -/
def Arena.boxU8 (a : Arena) (a0 : BitVec 64) (bs : List (BitVec 8)) : Arena :=
  let (a, p) := a.block bs.length 1
  ((a.wb p bs).w64 a0 p).w64 (a0 + 8) (BitVec.ofNat 64 bs.length)

/-- Writes `chain::MessageKey` (104 bytes) in seed form (`messageKeyAt`). -/
def Arena.msgKey (a : Arena) (at_ : BitVec 64) (k : MessageKeyGenerator) : Arena :=
  let a := ((a.vecU8 at_ []).vecU8 (at_ + 24) []).vecU8 (at_ + 48) []
  (a.vecU8 (at_ + 72) k.seed).w32 (at_ + 96) k.counter

/-- Writes `Option<chain::ChainKey>` (32 bytes) at `at_` (`optChainKeyAt`). -/
def Arena.optCk (a : Arena) (at_ : BitVec 64) : Option ChainKey → Arena
  | none => a.w64 at_ optChainKeyNone
  | some ck => (a.vecU8 at_ (keyToBytes32 ck.key)).w32 (at_ + 24) ck.index

/-- Writes a receiver chain (104 bytes, `chainAt`) with `srkExtra` trailing bytes on the serialized key. -/
def Arena.chain (a : Arena) (at_ : BitVec 64) (c : ReceiverChain)
    (srkExtra : List (BitVec 8) := []) : Arena := Id.run do
  let mut a := (a.vecU8 at_ (c.senderRatchetKey.serialize ++ srkExtra)).vecU8 (at_ + 24) []
  let n := c.messageKeys.length
  let (a1, p) := a.block (104 * n) 8
  a := ((a1.w64 (at_ + 48) (BitVec.ofNat 64 n)).w64 (at_ + 56) p).w64 (at_ + 64) (BitVec.ofNat 64 n)
  let mut i : ℕ := 0
  for k in c.messageKeys do
    a := a.msgKey (p + BitVec.ofNat 64 (104 * i)) k
    i := i + 1
  return a.optCk (at_ + 72) c.chainKey

/-- Writes `sender_chain: Option<Chain>` (104 bytes, `optSenderChainAt`). -/
def Arena.sender (a : Arena) (at_ : BitVec 64) : Option SenderChain → Arena
  | none => a.w64 at_ noneCap
  | some sc =>
    let a := (a.vecU8 at_ sc.ratchetKey.publicKey.serialize).vecU8 (at_ + 24)
      sc.ratchetKey.privateKey.bytes.toList
    let a := ((a.w64 (at_ + 48) 0).w64 (at_ + 56) 8).w64 (at_ + 64) 0
    a.optCk (at_ + 72) (some sc.chainKey)

/-- Writes `Option<{ Vec<u8>, tail }>` (`optTailVecAt`). -/
def Arena.optTail (a : Arena) (at_ : BitVec 64) : Option (List (BitVec 8) × List (BitVec 8)) → Arena
  | none => a.w64 at_ noneCap
  | some (v, tail) => (a.vecU8 at_ v).wb (at_ + 24) tail

/-- Unmodeled fields of `SessionStructure`. -/
structure SSExtra where
  alice : List (BitVec 8) := 0x05 :: List.replicate 32 0xbb
  pendingTail : List (BitVec 8) := List.replicate 24 0x11
  kyber : Option (List (BitVec 8) × List (BitVec 8)) := none
  regIds : List (BitVec 8) := [1, 0, 0, 0, 2, 0, 0, 0]
  pqSlack : ℕ := 0

/-- Writes a 344-byte `SessionStructure` holding `st` (`sessionStateAt`) and returns its address. -/
def Arena.ss (a : Arena) (st : SessionState (List (BitVec 8))) (x : SSExtra := {}) :
    Arena × BitVec 64 := Id.run do
  let (a, ss) := a.raw 344
  let mut a := a.vecU8 ss st.localIdentity.serialize
  a := a.vecU8 (ss + 0x18) ((st.remoteIdentity.map IdentityKey.serialize).getD [])
  a := a.vecU8 (ss + 0x30) (keyToBytes32 st.rootKey)
  let n := st.receiverChains.length
  let (a1, p) := a.block (104 * n) 8
  a := ((a1.w64 (ss + 0x48) (BitVec.ofNat 64 n)).w64 (ss + 0x50) p).w64 (ss + 0x58)
    (BitVec.ofNat 64 n)
  let mut i : ℕ := 0
  for c in st.receiverChains do
    a := a.chain (p + BitVec.ofNat 64 (104 * i)) c
    i := i + 1
  a := a.vecU8 (ss + 0x60) x.alice
  a := a.vecU8 (ss + 0x78) st.pqRatchetState x.pqSlack
  a := a.sender (ss + 0x90) st.senderChain
  a := a.optTail (ss + 0xf8)
    (if st.pendingPreKey then some (0x05 :: List.replicate 32 0xbb, x.pendingTail) else none)
  a := a.optTail (ss + 0x128) x.kyber
  a := (a.w32 (ss + 0x148) st.sessionVersion).w32 (ss + 0x14c) st.previousCounter
  return (a.wb (ss + 0x150) x.regIds, ss)

/-- Writes a 200-byte `OutgoingTripleRatchet` holding `ot` (`otrAt`) and returns its address. -/
def Arena.otr (a : Arena) (ot : OutgoingTripleRatchet (List (BitVec 8))) (pqSlack : ℕ := 0) :
    Arena × BitVec 64 :=
  let (a, o) := a.raw 200
  let a := a.vecU8 o ot.pqrState pqSlack
  let a := (a.wb (o + 0x18) ot.senderRatchetKey.publicKey.bytes.toList).wb (o + 0x38)
    ot.senderRatchetKey.privateKey.bytes.toList
  let a := (a.wb (o + 0x58) ot.localIdentityKey.publicKey.bytes.toList).wb (o + 0x78)
    ot.remoteIdentityKey.publicKey.bytes.toList
  let a := (a.wb (o + 0x98) (chainKeyBytes ot.senderChainKey)).w32 (o + 0xbc) ot.previousCounter
  (a.w8 (o + 0xc0) ot.sessionVersion, o)

/-- Writes a 120-byte `SignalMessage` holding `m` (`signalMessageAt`) and returns its address. -/
def Arena.msg (a : Arena) (m : SignalMessage) : Arena × BitVec 64 :=
  let (a, r) := a.raw 120
  let a := ((a.vecU8 r m.pqRatchet).boxU8 (r + 0x18) m.ciphertext).boxU8 (r + 0x28) m.serialized
  let a := a.wb (r + 0x38) m.senderRatchetKey.bytes.toList
  let a := match m.addresses with
    | none => (a.w64 (r + 0x58) 0).w64 (r + 0x60) 0
    | some ad => a.boxU8 (r + 0x58) ad
  let a := ((a.w32 (r + 0x68) m.counter).w32 (r + 0x6c) m.previousCounter).w8 (r + 0x70)
    m.messageVersion
  (a, r)

/-- Writes a 32-byte `ProtocolAddress` (`protocolAddressAt`) and returns its address. -/
def Arena.addr (a : Arena) (name : String) (device : BitVec 8) : Arena × BitVec 64 :=
  let (a, r) := a.raw 32
  ((a.vecU8 r (utf8 name)).w8 (r + 0x18) device, r)

def Arena.bytes (a : Arena) (bs : List (BitVec 8)) : Arena × BitVec 64 :=
  let (a, p) := a.raw bs.length
  (a.wb p bs, p)

def Arena.tape (a : Arena) (rest : List (BitVec 8)) : Arena :=
  ((a.w64 ctlA tapeA).w64 (ctlA + 8) (BitVec.ofNat 64 rest.length)).wb tapeA rest

def idA : IdentityKey := ⟨⟨vec32 (List.replicate 32 0xa1)⟩⟩
def idB : IdentityKey := ⟨⟨vec32 (List.replicate 32 0xb2)⟩⟩

/-- RFC 7748 §6.1 private keys used as coin material (`KeyPair.generate` clamps). -/
def alicePrivC : BitVec 256 :=
  bytesToKey32 (hexStr "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a")
def bobPrivC : BitVec 256 :=
  bytesToKey32 (hexStr "5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb")
def bobSpk : KeyPair := KeyPair.generate Cr bobPrivC

def rk0 : RootKey := bytesToKey32 (bs (List.range 32))
def ck0 : BitVec 256 := bytesToKey32 (bs (List.range' 0x20 32))

def stB : SessionState (List (BitVec 8)) := initializeRecipientSession S.spqr idB idA bobSpk rk0 ck0 0

def stA : SessionState (List (BitVec 8)) :=
  match initializeInitiatorSession Cr S.spqr idA idB bobSpk.publicKey rk0 ck0 0 alicePrivC with
  | .ok s => s.setUnacknowledgedPreKeyMessage
  | .error _ => stB

def stA0 : SessionState (List (BitVec 8)) := { stA with senderChain := none }

def nameA : String := "9d0652a3-dcc3-4d11-975f-74d61598733f"
def nameB : String := "796abedb-ca4e-4f18-8803-1fde5b921f9f"

def tape0 : List (BitVec 8) := (List.range 64).map fun i => BitVec.ofNat 8 (0x40 + i)

def ptext0 : List (BitVec 8) := utf8 "hello bob"
def ptext1 : List (BitVec 8) := utf8 "second message, no addresses"

def addrGhost (m : Memory) (a : BitVec 64) : AddrGhost :=
  ⟨⟨m.read64 a, m.read64 (a + 8), m.readBytes (m.read64 (a + 8)) (m.read64 (a + 16)).toNat⟩,
   m.read8 (a + 0x18)⟩

/-- Upper bound above which decoded lengths are rejected as garbage. -/
def lenCap : ℕ := 1 <<< 16

/-- Reads a `Vec<u8>` header at `h` (`none` if invalid) along with its owned block. -/
def rdVec (m : Memory) (h : BitVec 64) : Option (List (BitVec 8)) × List Buf :=
  let cap := (m.read64 h).toNat
  let p := m.read64 (h + 8)
  let n := (m.read64 (h + 16)).toNat
  if n > cap ∨ cap > lenCap ∨ p = 0 then (none, []) else
  (some (m.readBytes p n), if cap = 0 then [] else [(p, cap, 1)])

/-- Reads a `Box<[u8]>` `(ptr, len)` at `a` along with its owned block. -/
def rdBox (m : Memory) (a : BitVec 64) : Option (List (BitVec 8)) × List Buf :=
  let p := m.read64 a
  let n := (m.read64 (a + 8)).toNat
  if n > lenCap ∨ p = 0 then (none, []) else
  (some (m.readBytes p n), if n = 0 then [] else [(p, n, 1)])

def rdKey32 (m : Memory) (a : BitVec 64) : List.Vector (BitVec 8) 32 :=
  ⟨m.readBytes a 32, Memory.readBytes_length m a 32⟩

/-- Reads `Option<chain::ChainKey>` at `a` (`none` if invalid, `some none` at the niche). -/
def rdOptCk (m : Memory) (a : BitVec 64) : Option (Option ChainKey) × List Buf :=
  if m.read64 a = optChainKeyNone then (some none, []) else
  match rdVec m a with
  | (some k, b) => (if k.length = 32 then some (some ⟨bytesToKey32 k, m.read32 (a + 24)⟩) else none, b)
  | (none, b) => (none, b)

/-- Reads a stored `chain::MessageKey` (104 bytes) in seed form. -/
def rdMsgKey (m : Memory) (a : BitVec 64) : Option MessageKeyGenerator × List Buf :=
  let (c, b1) := rdVec m a
  let (k, b2) := rdVec m (a + 24)
  let (i, b3) := rdVec m (a + 48)
  let (s, b4) := rdVec m (a + 72)
  let bufs := b1 ++ b2 ++ b3 ++ b4
  match c, k, i, s with
  | some [], some [], some [], some seed => (some ⟨seed, m.read32 (a + 96)⟩, bufs)
  | _, _, _, _ => (none, bufs)

def rdChain (m : Memory) (a : BitVec 64) : Option ReceiverChain × List Buf := Id.run do
  let (srk, b1) := rdVec m a
  let (_, b2) := rdVec m (a + 24)
  let mkCap := (m.read64 (a + 48)).toNat
  let mkPtr := m.read64 (a + 56)
  let n := (m.read64 (a + 64)).toNat
  if n > mkCap ∨ mkCap > 2000 then return (none, b1 ++ b2)
  let mut bufs := b1 ++ b2 ++ (if mkCap = 0 then [] else [(mkPtr, 104 * mkCap, 8)])
  let mut keys : List MessageKeyGenerator := []
  let mut ok := true
  for i in [0:n] do
    let (k, b) := rdMsgKey m (mkPtr + BitVec.ofNat 64 (104 * i))
    bufs := bufs ++ b
    match k with
    | some k => keys := keys ++ [k]
    | none => ok := false
  let (ck, b) := rdOptCk m (a + 72)
  bufs := bufs ++ b
  match srk.map PublicKey.deserialize, ck with
  | some (.ok pk), some ck => return (if ok then some ⟨pk, ck, keys⟩ else none, bufs)
  | _, _ => return (none, bufs)

def rdSender (m : Memory) (a : BitVec 64) : Option (Option SenderChain) × List Buf :=
  if m.read64 a = noneCap then (some none, []) else
  let (srk, b1) := rdVec m a
  let (pv, b2) := rdVec m (a + 24)
  let mkCap := (m.read64 (a + 48)).toNat
  let n := (m.read64 (a + 64)).toNat
  let b3 := if mkCap = 0 then [] else [(m.read64 (a + 56), 104 * mkCap, 8)]
  let (ck, b4) := rdOptCk m (a + 72)
  let bufs := b1 ++ b2 ++ b3 ++ b4
  match srk.map PublicKey.deserialize, pv, ck with
  | some (.ok pk), some p, some (some ck) =>
    if h : p.length = 32 then
      (if n = 0 then some (some ⟨⟨pk, ⟨⟨p, h⟩⟩⟩, ck⟩) else none, bufs)
    else (none, bufs)
  | _, _, _ => (none, bufs)

/-- Decoded `SessionStructure`: session-model state (`none` if invalid), owned heap blocks, and
unchanged bytes pinned by `SessionGhost.Keeps`. -/
structure SSRead where
  st : Option (SessionState (List (BitVec 8)))
  bufs : List Buf
  kept : List (BitVec 8)
  pqHdr : List (BitVec 8)

def rdRemote (r : Option (List (BitVec 8))) : Option (Option IdentityKey) :=
  match r with
  | some [] => some none
  | some bs => match PublicKey.deserialize bs with
    | .ok pk => some (some ⟨pk⟩)
    | .error _ => none
  | none => none

def rdSS (m : Memory) (ss : BitVec 64) : SSRead := Id.run do
  let (lik, b1) := rdVec m ss
  let (rik, b2) := rdVec m (ss + 0x18)
  let (rk, b3) := rdVec m (ss + 0x30)
  let cCap := (m.read64 (ss + 0x48)).toNat
  let cPtr := m.read64 (ss + 0x50)
  let n := (m.read64 (ss + 0x58)).toNat
  let mut bufs := b1 ++ b2 ++ b3 ++ (if cCap = 0 then [] else [(cPtr, 104 * cCap, 8)])
  let mut chains : List ReceiverChain := []
  let mut ok : Bool := decide (n ≤ cCap ∧ cCap ≤ 64)
  if ok then
    for i in [0:n] do
      let (c, b) := rdChain m (cPtr + BitVec.ofNat 64 (104 * i))
      bufs := bufs ++ b
      match c with
      | some c => chains := chains ++ [c]
      | none => ok := false
  let (_, b4) := rdVec m (ss + 0x60)
  let (pq, b5) := rdVec m (ss + 0x78)
  let (sc, b6) := rdSender m (ss + 0x90)
  let pending := m.read64 (ss + 0xf8) ≠ noneCap
  let b7 := if pending then (rdVec m (ss + 0xf8)).2 else []
  let b8 := if m.read64 (ss + 0x128) ≠ noneCap then (rdVec m (ss + 0x128)).2 else []
  bufs := bufs ++ b4 ++ b5 ++ b6 ++ b7 ++ b8
  let kept := m.readBytes ss 0x30 ++ m.readBytes (ss + 0x60) 24 ++ m.readBytes (ss + 0x150) 8 ++
    (if pending then m.readBytes (ss + 0xf8) 48 else []) ++
    (if m.read64 (ss + 0x128) ≠ noneCap then m.readBytes (ss + 0x128) 32 else [])
  let st : Option (SessionState (List (BitVec 8))) :=
    match lik.map PublicKey.deserialize, rdRemote rik, rk, pq, sc with
    | some (.ok lpk), some rem, some rkb, some pqb, some sc =>
      if ok ∧ rkb.length = 32 then
        some { sessionVersion := m.read32 (ss + 0x148), localIdentity := ⟨lpk⟩,
               remoteIdentity := rem, rootKey := bytesToKey32 rkb,
               previousCounter := m.read32 (ss + 0x14c), senderChain := sc,
               receiverChains := chains, pendingPreKey := pending, pqRatchetState := pqb }
      else none
    | _, _, _, _, _ => none
  return ⟨st, bufs, kept, m.readBytes (ss + 0x78) 24⟩

/-- Decodes a 200-byte `OutgoingTripleRatchet` and its PQ block. -/
def rdOtr (m : Memory) (o : BitVec 64) : Option (OutgoingTripleRatchet (List (BitVec 8))) × List Buf :=
  match rdVec m o with
  | (some pq, b) =>
    (some { senderRatchetKey := ⟨⟨rdKey32 m (o + 0x18)⟩, ⟨rdKey32 m (o + 0x38)⟩⟩,
            senderChainKey := ⟨bytesToKey32 (m.readBytes (o + 0x98) 32), m.read32 (o + 0xb8)⟩,
            previousCounter := m.read32 (o + 0xbc), pqrState := pq,
            sessionVersion := m.read8 (o + 0xc0), localIdentityKey := ⟨⟨rdKey32 m (o + 0x58)⟩⟩,
            remoteIdentityKey := ⟨⟨rdKey32 m (o + 0x78)⟩⟩ }, b)
  | (none, b) => (none, b)

/-- Decodes a 120-byte `SignalMessage` and its owned blocks. -/
def rdMsg (m : Memory) (r : BitVec 64) : Option SignalMessage × List Buf :=
  let (pq, b1) := rdVec m r
  let (ct, b2) := rdBox m (r + 0x18)
  let (ser, b3) := rdBox m (r + 0x28)
  let (ad, b4) : Option (Option (List (BitVec 8))) × List Buf :=
    if m.read64 (r + 0x58) = 0 then (some none, []) else
    let (x, b) := rdBox m (r + 0x58); (x.map some, b)
  let bufs := b1 ++ b2 ++ b3 ++ b4
  match pq, ct, ser, ad with
  | some pq, some ct, some ser, some ad =>
    (some { messageVersion := m.read8 (r + 0x70), senderRatchetKey := ⟨rdKey32 m (r + 0x38)⟩,
            counter := m.read32 (r + 0x68), previousCounter := m.read32 (r + 0x6c),
            ciphertext := ct, pqRatchet := pq, addresses := ad, serialized := ser }, bufs)
  | _, _, _, _ => (none, bufs)

def strRefIs (m : Memory) (a : BitVec 64) (lit : List (BitVec 8)) : Bool :=
  (m.read64 (a + 8)).toNat == lit.length && m.readBytes (m.read64 a) lit.length == lit

/-- Checks `speAt A fnName a e` on memory bytes and returns the blocks owned by the error value. -/
def speIs (m : Memory) (fnName : List (BitVec 8)) (a : BitVec 64) :
    SignalProtocolError → Bool × List Buf
  | .invalidState =>
    let (v, b) := rdVec m (a + 8)
    (m.read64 a == speWord 1 && v.isSome && strRefIs m (a + 32) fnName, b)
  | .ciphertextMessageTooShort n =>
    (m.read64 a == speWord 3 && m.read64 (a + 8) == BitVec.ofNat 64 n, [])
  | .legacyCiphertextVersion v => (m.read64 a == speWord 4 && m.read8 (a + 8) == v, [])
  | .unrecognizedCiphertextVersion v => (m.read64 a == speWord 5 && m.read8 (a + 8) == v, [])
  | .invalidProtobufEncoding => (m.read64 a == speWord 2, [])
  | .noKeyTypeIdentifier => (m.read64 a == speWord 7, [])
  | .badKeyType t => (m.read64 a == speWord 8 && m.read8 (a + 8) == t, [])
  | .badKeyLength n => (m.read64 a == speWord 9 && m.read64 (a + 8) == BitVec.ofNat 64 n, [])
  | .invalidKeyAgreement => (m.read64 a == speWord 10, [])
  | .invalidSessionStructure r => (m.read64 a == speWord 20 && strRefIs m (a + 8) (invalidSessionStructureStr r), [])
  | .duplicatedMessage i c =>
    (m.read64 a == speWord 23 && m.read32 (a + 8) == i && m.read32 (a + 12) == c, [])
  | .invalidMessage t r =>
    let (v, b) := rdVec m (a + 8)
    let strOk := match r with
      | .tooFarInFuture => v == some tooFarInFutureStr
      | .macFailed => v == some macFailedStr
      | .pqRatchet | .badCiphertext => v.isSome
      | .decryptionFailed => false
    (m.read64 a == speWord 24 && strOk && m.read8 (a + 32) == msgTypeByte t, b)
  | .panic => (false, [])

def speShow (m : Memory) (a : BitVec 64) : String :=
  let w (i : ℕ) := hexOf (le64 (m.read64 (a + BitVec.ofNat 64 (8 * i)))).reverse
  let s := match rdVec m (a + 8) with
    | (some v, _) => if v.length ≤ 64 then String.ofList (v.map fun (b : BitVec 8) => Char.ofNat b.toNat) else "?"
    | _ => "-"
  s!"[{w 0} {w 1} {w 2} {w 3} {w 4}] str?={s.quote}"

def msgShow (m : SignalMessage) : String :=
  s!"v={m.messageVersion.toNat} ctr={m.counter.toNat} prev={m.previousCounter.toNat} " ++
    s!"key={hexOf (m.senderRatchetKey.bytes.toList.take 4)}.. ct={m.ciphertext.length}B " ++
    s!"pq={m.pqRatchet.length}B addr={m.addresses.map List.length} ser={m.serialized.length}B"

/-- Verifies allocator trace events against input blocks `pre` and output blocks `post`: every free
is of a live block at most once, and `pre + allocs = post + frees` as multisets. -/
def heapCheck (trace : List TraceEvent) (pre post : List Buf) : Option String := Id.run do
  let mut live := pre
  for e in trace do
    if let some b := decEv "alloc" e then live := live ++ [b]
    if let some b := decEv "dealloc" e then
      if live.contains b then live := live.erase b
      else return some s!"free of a non-live block {hexOf (le64 b.1).reverse} size {b.2.1}"
  if sameBufs live post then return none
  let leaked := live.filter (!post.contains ·)
  let unknown := post.filter (!live.contains ·)
  return some s!"leaked {leaked.map fun b => (hexOf (le64 b.1).reverse, b.2.1)}; output blocks not allocated {unknown.map fun b => (hexOf (le64 b.1).reverse, b.2.1)}"

def runFuel : ℕ := 3000000
def compactEvery : ℕ := 1000

/-- Live memory regions preserved across periodic compaction: stack, heap, arena, and tape. -/
def liveRegions (aEnd : BitVec 64) (s : State) : List (BitVec 64 × ℕ) :=
  let sp := s.sp - 256
  [(sp, (stackTop - sp).toNat), (heapCur, 8), (heapBase, (s.mem.read64 heapCur).toNat),
   (arenaA, (aEnd - arenaA).toNat), (ctlA, 16), (tapeA, 256)]

def runCall (R : Runner) (img : Obj.Image) (base : Memory) (aEnd : BitVec 64) (name : String)
    (m : Memory) (regs : List (Reg × BitVec 64)) : IO (RunOut × ℕ) := do
  let t0 ← IO.monoMsNow
  let r ← IO.lazyPure fun _ => fastRun R base (liveRegions aEnd) compactEvery runFuel
    (callState img (entryOf img name) m regs)
  let t1 ← IO.monoMsNow
  pure (r, if r.steps = 0 then 0 else t1 - t0)

def results : String := "/tmp/tr_run_test/results.md"

def say (msg : String) : IO Unit := do
  IO.println msg
  progress msg
  let h ← IO.FS.Handle.mk results .append
  h.putStrLn msg
  h.flush

def check (name : String) (b : Bool) (detail : String := "") : IO Unit :=
  say s!"{if b then "ok  " else "FAIL"} {name}{if b || detail.isEmpty then "" else " — " ++ detail}"

def runLine (root : String) (r : RunOut) (ms budget : ℕ) : IO Unit :=
  say s!"  [{root}] steps {r.steps}, depth {r.depth} (budget {budget}), returned {returned r.sf}, status {repr r.sf.status}, halt stub {r.haltStub}, {ms} ms\n    stubs {r.stubs}"

/-- Arena addresses of all scenario inputs and output buffers. -/
structure Layout where
  a : Arena
  ssA : BitVec 64
  ssB : BitVec 64
  ssA0 : BitVec 64
  addrA : BitVec 64
  addrB : BitVec 64
  pt0 : BitVec 64
  pt1 : BitVec 64
  otr : BitVec 64
  enc0 : BitVec 64
  enc1 : BitVec 64
  otrErr : BitVec 64
  msg : BitVec 64
  dec : BitVec 64
  dec2 : BitVec 64
  msg2 : BitVec 64
  dec3 : BitVec 64
  msgE : BitVec 64
  decE : BitVec 64
  retE : BitVec 64
  scratch : BitVec 64

def mkLayout (m0 : Memory) : Layout :=
  let a : Arena := { mem := m0, cur := arenaA }
  let a := a.tape tape0
  let (a, ssA) := a.ss stA
  let (a, ssB) := a.ss stB
  let (a, ssA0) := a.ss stA0
  let (a, addrA) := a.addr nameA 1
  let (a, addrB) := a.addr nameB 2
  let (a, pt0) := a.bytes ptext0
  let (a, pt1) := a.bytes ptext1
  let (a, otr) := a.raw 200
  let (a, enc0) := a.raw 120
  let (a, enc1) := a.raw 120
  let (a, otrErr) := a.raw 200
  let (a, msg) := a.raw 120
  let (a, dec) := a.raw 48
  let (a, dec2) := a.raw 48
  let (a, msg2) := a.raw 120
  let (a, dec3) := a.raw 48
  let (a, msgE) := a.raw 120
  let (a, decE) := a.raw 48
  let (a, retE) := a.raw 120
  let (a, scratch) := a.raw 1024
  { a, ssA, ssB, ssA0, addrA, addrB, pt0, pt1, otr, enc0, enc1, otrErr, msg, dec, dec2, msg2, dec3,
    msgE, decE, retE, scratch }

def addrsAB : Option (List (BitVec 8)) := serializeAddresses (serviceIdParse parse)
  ⟨⟨0, 0, utf8 nameA⟩, 1⟩ ⟨⟨0, 0, utf8 nameB⟩, 2⟩
def mFrom := Mut.exec OutgoingTripleRatchet.fromSessionState stA
def otrM : OutgoingTripleRatchet (List (BitVec 8)) :=
  match mFrom.1 with | .ok o => o | .error _ => ⟨bobSpk, ⟨0, 0⟩, 0, [], 0, idA, idB⟩
def mEnc0 := Mut.exec (OutgoingTripleRatchet.encrypt Cr protoSignalCodec S.spqr ptext0 addrsAB tape0) otrM
def mEnc1 := Mut.exec (OutgoingTripleRatchet.encrypt Cr protoSignalCodec S.spqr ptext1 none tape0) mEnc0.2

structure Ctx where
  img : Obj.Image
  R : Runner
  base : Memory
  L : Layout
  aEnd : BitVec 64

def Ctx.run (c : Ctx) (name : String) (m : Memory) (regs : List (Reg × BitVec 64)) :
    IO (RunOut × ℕ) :=
  runCall c.R c.img c.base c.aEnd name m regs

def Ctx.settle (c : Ctx) (r : RunOut) : Memory := compact c.base r.sf.mem (liveRegions c.aEnd r.sf)

def caseRow (root case_ : String) (ok : Bool) (r : RunOut) : IO Unit :=
  say s!"| {root} | {case_} | {if ok then "match" else "MISMATCH"} | {r.depth} | {r.steps} | {r.haltStub.getD "-"} |"

def addrSnap (m : Memory) (a : BitVec 64) : List (BitVec 8) :=
  m.readBytes a 25 ++ m.readBytes (m.read64 (a + 8)) (m.read64 (a + 16)).toNat

def word (bs : List (BitVec 8)) (i : ℕ) : BitVec 64 := BitVec.ofNat 64 (leNat ((bs.drop (8 * i)).take 8))

def hex64 (w : BitVec 64) : String := hexOf (le64 w).reverse

/-- Checks the observed execution of the in-image `spqr::send::<HookRng>` call against `S.send`. -/
def sendReport (o : SendObs) : IO Unit := do
  let w := word o.retBytes
  let d := (o.sp0 - o.minSp).toNat
  say s!"  spqr::send: entered at step {o.k0}, done {o.done}, callee-saved restored {o.framed}, steps {o.steps}, own depth {d} (budget spqrSendStack {spqrSendStack})"
  say s!"    state arg {o.stBytes.length} B at hdr {hex64 o.stHdr}; sret words {(List.range 9).map fun i => hex64 (w i)}"
  say s!"    tape ctl before ({hex64 o.ctl0.1}, {o.ctl0.2.toNat}) after ({hex64 o.ctl1.1}, {o.ctl1.2.toNat}); stubs {o.stubs}"
  check "D1: spqr::send returned to its caller (lr, sp) with callee-saved registers restored"
    (o.done && o.framed)
  check "D1: sret = Ok { state: empty Vec, msg: empty Vec, key: None }, i.e. S.send [] _ = some ([], none, [])"
    ((w 0) ≠ errTag && (w 0).toNat < 2 ^ 63 && (w 1) ≠ 0 && (w 2) == 0 && (w 3).toNat < 2 ^ 63 &&
      (w 4) ≠ 0 && (w 5) == 0 && (w 6) == noneCap)
  check "D1: tape cursor and count unchanged (S.draws [] _ = 0)" (o.ctl1 == o.ctl0)
  check "D1: stubs reached ⊆ {spqr::decode_state, memcpy, __rust_dealloc}"
    (o.stubs.all fun n => n ∈ [decodeStateName, "memcpy", "__rustc::__rust_dealloc"])
  check s!"D1: own stack depth {d} ≤ spqrSendStack" (d ≤ spqrSendStack)

/-- Checks a `Result<SignalMessage, SPE>` at `r` against `model` and returns its owned blocks. -/
def checkMsgResult (tag : String) (fnName : List (BitVec 8)) (m : Memory) (r : BitVec 64)
    (ok : Bool) (model : Except SignalProtocolError SignalMessage) : IO (Bool × List Buf) := do
  match model with
  | .ok msg =>
    let (b, bufs) := rdMsg m r
    let good := ok && m.read64 r ≠ errTag && b == some msg
    check s!"{tag} Ok: sret = model SignalMessage (signalMessageResultAt)" good
      s!"binary {b.map msgShow} word0 {hex64 (m.read64 r)}; model {msgShow msg}"
    pure (good, bufs)
  | .error e =>
    let (good, bufs) := speIs m fnName (r + 8) e
    let good := ok && m.read64 r == errTag && good
    check s!"{tag} Err {reprStr e}: sret = errResultAt" good
      s!"binary word0 {hex64 (m.read64 r)} spe {speShow m (r + 8)}"
    pure (good, bufs)

def heapLine (tag : String) (r : RunOut) (pre post : List Buf) : IO Unit := do
  let h := heapCheck r.sf.trace pre post
  check s!"{tag} heap: frees of live blocks only, allocs + inputs' blocks = frees + outputs' blocks"
    h.isNone (h.getD "")

/-- Runs `from_session_state(x0 = ss, x8 = ret)` and checks the result against `otrFromSpec`. -/
def stageFrom (c : Ctx) (m : Memory) (ss ret : BitVec 64) (st : SessionState (List (BitVec 8)))
    (case_ : String) : IO Memory := do
  let pre := rdSS m ss
  let (r, ms) ← c.run otrFromName m [(.x0, ss), (.x8, ret)]
  runLine "OTR::from_session_state" r ms smallRootStack
  let mf := r.sf.mem
  let model := Mut.exec OutgoingTripleRatchet.fromSessionState st
  let post := rdSS mf ss
  let (resOk, resBufs) : Bool × List Buf := match model.1 with
    | .ok o =>
      let (b, bs) := rdOtr mf ret
      (mf.read64 ret ≠ errTag && b == some o && mf.readBytes ret 16 == pre.pqHdr.take 16, bs)
    | .error e =>
      let (g, bs) := speIs mf [] (ret + 8) e
      (mf.read64 ret == errTag && g, bs)
  let tag := s!"[from: {case_}]"
  check s!"{tag} sret = otrResultAt (model {match model.1 with | .ok _ => "Ok" | .error e => reprStr e}), Ok pq Vec = SS's old one"
    resOk s!"word0 {hex64 (mf.read64 ret)} spe {speShow mf (ret + 8)}"
  let ssOk := post.st == some model.2 && post.kept == pre.kept
  check s!"{tag} SS = model final state; IK / alice / reg-id / pending bytes unchanged" ssOk
  heapLine tag r pre.bufs (post.bufs ++ resBufs)
  caseRow "from_session_state" case_ (returned r.sf && resOk && ssOk) r
  pure (c.settle r)

/-- Runs `encrypt(x0 = ret, x1 = otr, x2/x3 = plaintext, x4 = local or 0, x5 = remote, x6 = rng)`
and checks the result against `otrEncryptSpec`. -/
def stageEnc (c : Ctx) (m : Memory) (ret : BitVec 64) (ptA : BitVec 64) (pt : List (BitVec 8))
    (loc : Bool) (ot : OutgoingTripleRatchet (List (BitVec 8))) (case_ : String) : IO Memory := do
  let L := c.L
  let (_, otrBufs) := rdOtr m L.otr
  let snap0 := (m.readBytes ptA pt.length, addrSnap m L.addrA, addrSnap m L.addrB,
    m.readBytes ctlA 16, m.readBytes tapeA tape0.length)
  let (r, ms) ← c.run otrEncryptName m
    [(.x0, ret), (.x1, L.otr), (.x2, ptA), (.x3, BitVec.ofNat 64 pt.length),
     (.x4, if loc then L.addrA else 0), (.x5, L.addrB), (.x6, L.scratch)]
  runLine "OTR::encrypt" r ms rootStack
  let tag := s!"[encrypt: {case_}]"
  match r.send with
  | some o => sendReport o
  | none => check s!"{tag} D1: spqr::send was reached" false
  let mf := r.sf.mem
  let x : OtrEncryptGhost := ⟨ret, L.otr, 0, 0, ot, ptA, pt, L.addrA,
    if loc then some (addrGhost m L.addrA) else none, L.addrB, addrGhost m L.addrB, tapeA, tape0⟩
  let model := x.model Cr S parse
  let (resOk, resBufs) ← checkMsgResult tag (utf8 "encrypt") mf ret (returned r.sf) model.1
  let (o', otrBufs') := rdOtr mf L.otr
  let otrOk := o' == some model.2
  check s!"{tag} OTR = model final value (counter {model.2.senderChainKey.index.toNat})" otrOk
  let k := S.draws ot.pqrState tape0
  let snap1 := (mf.readBytes ptA pt.length, addrSnap mf L.addrA, addrSnap mf L.addrB,
    mf.readBytes ctlA 16, mf.readBytes tapeA tape0.length)
  let tapeOk := mf.read64 ctlA == tapeA + BitVec.ofNat 64 k &&
    mf.read64 (ctlA + 8) == BitVec.ofNat 64 (tape0.length - k)
  check s!"{tag} tape advanced by S.draws = {k}; plaintext, addresses, tape bytes unchanged"
    (tapeOk && snap1.1 == snap0.1 && snap1.2.1 == snap0.2.1 && snap1.2.2.1 == snap0.2.2.1 &&
      snap1.2.2.2.2 == snap0.2.2.2.2)
  heapLine tag r otrBufs (otrBufs' ++ resBufs)
  caseRow "OTR::encrypt" case_ (resOk && otrOk && tapeOk) r
  pure (c.settle r)

def mkCtx : IO Ctx := do
  let img ← loadImg
  let m0 := imgMem img
  let L := mkLayout m0
  let aEnd := L.a.cur
  let base := compact m0 L.a.mem [(arenaA, (aEnd - arenaA).toNat), (ctlA, 16), (tapeA, 256),
    (heapCur, 8)]
  pure { img, R := Runner.ofImage img, base, L, aEnd }

def scenarioChecks (c : Ctx) : IO Unit := do
  let L := c.L
  check "writer ↔ reader: the SSs of Alice, Bob, Alice-without-sender-chain read back as the 7a states"
    ((rdSS c.base L.ssA).st == some stA && (rdSS c.base L.ssB).st == some stB &&
      (rdSS c.base L.ssA0).st == some stA0)
  check "scenario: Alice has a sender chain, a pending pre-key, an empty pq state, remote IK ≠ local IK"
    (stA.senderChain.isSome && stA.pendingPreKey && stA.pqRatchetState == [] &&
      stA.remoteIdentity != some stA.localIdentity && stB.remoteIdentity != some stB.localIdentity)
  check "scenario: serialize_addresses(Alice, Bob) parses (36 bytes)" (addrsAB.map List.length == some 36)

/-- Runs `try_from(x0/x1 = bytes, x8 = ret)` and checks the result against `tryFromSpec`. -/
def stageTryFrom (c : Ctx) (m : Memory) (bA : BitVec 64) (n : ℕ) (ret : BitVec 64) (case_ : String) :
    IO Memory := do
  let bytes := m.readBytes bA n
  let (r, ms) ← c.run tryFromName m [(.x0, bA), (.x1, BitVec.ofNat 64 n), (.x8, ret)]
  runLine "try_from" r ms smallRootStack
  let tag := s!"[try_from: {case_}]"
  let (resOk, bufs) ← checkMsgResult tag [] r.sf.mem ret (returned r.sf)
    (SignalMessage.tryFrom protoSignalCodec bytes)
  check s!"{tag} input bytes unchanged" (r.sf.mem.readBytes bA n == bytes)
  heapLine tag r [] bufs
  caseRow "try_from" case_ (resOk && r.sf.mem.readBytes bA n == bytes) r
  pure (c.settle r)

/-- Bytes of `SessionStructure` pinned by `SessionGhost.Keeps`: IK headers, `alice_base_key` header, and registration IDs. -/
def ssFixed (m : Memory) (ss : BitVec 64) : List (BitVec 8) :=
  m.readBytes ss 0x30 ++ m.readBytes (ss + 0x60) 24 ++ m.readBytes (ss + 0x150) 8

def msgSnap (m : Memory) (a : BitVec 64) : List (BitVec 8) × Option SignalMessage :=
  (m.readBytes a 0x71, (rdMsg m a).1)

/-- Runs `try_decrypt_with_state(x0 = ret, x1 = ss, x2 = remote, x3 = local, x4 = msg, w5 = type)`
and checks the result against `tryDecryptSpec`. -/
def stageDec (c : Ctx) (m : Memory) (ss msgA ret : BitVec 64) (st : SessionState (List (BitVec 8)))
    (case_ : String) : IO (Memory × SessionState (List (BitVec 8))) := do
  let L := c.L
  let pre := rdSS m ss
  let some msg := (rdMsg m msgA).1
    | do check s!"[decrypt: {case_}] input message decodes" false; pure (m, st)
  let rest := m.readBytes (m.read64 ctlA) (m.read64 (ctlA + 8)).toNat
  let cur := m.read64 ctlA
  let snap0 := (addrSnap m L.addrA, addrSnap m L.addrB, msgSnap m msgA)
  let (r, ms) ← c.run tryDecryptName m
    [(.x0, ret), (.x1, ss), (.x2, L.addrA), (.x3, L.addrB), (.x4, msgA), (.x5, 2), (.x6, 1),
     (.x7, L.scratch)]
  runLine "try_decrypt_with_state" r ms rootStack
  let tag := s!"[decrypt: {case_}]"
  let mf := r.sf.mem
  let model := Mut.exec (SessionState.tryDecryptWithState Cr S.spqr
    (serializeAddresses (serviceIdParse parse) (addrGhost m L.addrA) (addrGhost m L.addrB)) msg .whisper
    (coinsOf rest)) st
  let (resOk, resBufs) : Bool × List Buf := match model.1 with
    | .ok pt =>
      let (v, b) := rdVec mf (ret + 8)
      (mf.read64 ret == okTagVec && v == some pt, b)
    | .error e => speIs mf (utf8 "decrypt") ret e
  check s!"{tag} sret = vecResultAt (model {match model.1 with | .ok pt => s!"Ok {pt.length} B" | .error e => reprStr e})"
    (returned r.sf && resOk) s!"word0 {hex64 (mf.read64 ret)} spe {speShow mf ret}"
  let post := rdSS mf ss
  let ok := match model.1 with | .ok _ => true | .error _ => false
  let relOk := ssFixed mf ss == ssFixed m ss &&
    (if ok then mf.read64 (ss + 0xf8) == noneCap && mf.read64 (ss + 0x128) == noneCap
     else post.kept == pre.kept && mf.readBytes (ss + 0x30) 24 == m.readBytes (ss + 0x30) 24 &&
       mf.readBytes (ss + 0x90) 0x60 == m.readBytes (ss + 0x90) 0x60)
  check s!"{tag} SS = model final state; AfterTryDecrypt {ok} on the ghost bytes" (post.st == some model.2 && relOk)
    s!"SS decodes {post.st.isSome}; relation {relOk}"
  let k := decryptDraws Cr st msg.senderRatchetKey rest
  let tapeOk := mf.read64 ctlA == cur + BitVec.ofNat 64 k &&
    mf.read64 (ctlA + 8) == BitVec.ofNat 64 (rest.length - k) && mf.readBytes cur rest.length == rest
  let snap1 := (addrSnap mf L.addrA, addrSnap mf L.addrB, msgSnap mf msgA)
  let borrowOk := snap1.1 == snap0.1 && snap1.2.1 == snap0.2.1 && snap1.2.2.1 == snap0.2.2.1 &&
    snap1.2.2.2 == snap0.2.2.2
  check s!"{tag} tape advanced by decryptDraws = {k}; addresses and message unchanged" (tapeOk && borrowOk)
  heapLine tag r pre.bufs (post.bufs ++ resBufs)
  caseRow "try_decrypt_with_state" case_
    (returned r.sf && resOk && post.st == some model.2 && relOk && tapeOk && borrowOk) r
  pure (c.settle r, model.2)

/-- Runs `apply_to_session_state(x0 = otr, x1 = ss)` and checks the result against `otrApplySpec`. -/
def stageApply (c : Ctx) (m : Memory) (o ss : BitVec 64) (ot : OutgoingTripleRatchet (List (BitVec 8)))
    (st : SessionState (List (BitVec 8))) (case_ : String) : IO Memory := do
  let pre := rdSS m ss
  let (_, otrBufs) := rdOtr m o
  let pqPin := m.readBytes o 16
  let (r, ms) ← c.run otrApplyName m [(.x0, o), (.x1, ss)]
  runLine "OTR::apply_to_session_state" r ms smallRootStack
  let tag := s!"[apply: {case_}]"
  let mf := r.sf.mem
  let post := rdSS mf ss
  let model := ot.applyToSessionState st
  let relOk := ssFixed mf ss == ssFixed m ss && post.kept == pre.kept &&
    mf.readBytes (ss + 0x30) 0x48 == m.readBytes (ss + 0x30) 0x48 &&
    mf.readBytes (ss + 0x90) 0x48 == m.readBytes (ss + 0x90) 0x48 &&
    mf.readBytes (ss + 0x78) 16 == pqPin && mf.readBytes (ss + 0x148) 8 == m.readBytes (ss + 0x148) 8
  let good := returned r.sf && post.st == some model && relOk
  check s!"{tag} SS = model applyToSessionState; AfterOutgoingRatchetApply on the ghost bytes (pq pin = OTR's)" good
    s!"returned {returned r.sf}; SS decodes {post.st.isSome}, = model {post.st == some model}; relation {relOk}"
  heapLine tag r (pre.bufs ++ otrBufs) post.bufs
  caseRow "OTR::apply_to_session_state" case_ good r
  pure (c.settle r)

def memCopy (m : Memory) (dst src : BitVec 64) (n : ℕ) : Memory :=
  m.writeBytes dst (m.readBytes src n)

/-- Wire `SignalMessage` with a 5-byte ratchet key (`0x34 ‖ {1: 05 01 02 03 04, 2: 0, 4: 16 B} ‖ 8-byte MAC`). -/
def badKeyLenBytes : List (BitVec 8) :=
  [0x34, 0x0a, 0x05, 0x05, 1, 2, 3, 4, 0x10, 0x00, 0x22, 0x10] ++ List.replicate 16 0x77 ++
    List.replicate 8 0x55

/-- Wire `SignalMessage` with key type `0x06` and 32 key bytes. -/
def badKeyTypeBytes : List (BitVec 8) :=
  [0x34, 0x0a, 0x21, 0x06] ++ List.replicate 32 0x09 ++ [0x10, 0x00, 0x22, 0x10] ++
    List.replicate 16 0x77 ++ List.replicate 8 0x55

def main : IO Unit := do
  IO.FS.createDirAll "/tmp/tr_run_test"
  IO.FS.writeFile results "# TripleRatchetRunTest results\n\nCases table rows start with `| `.\n\n"
  let t0 ← IO.monoMsNow
  let c ← mkCtx
  scenarioChecks c
  let L := c.L
  let m1 ← stageFrom c c.base L.ssA L.otr stA "Alice, empty pq state"
  let m2 ← stageEnc c m1 L.enc0 L.pt0 ptext0 true otrM "local address some"
  let m2 ← stageEnc c m2 L.enc1 L.pt1 ptext1 false mEnc0.2 "local address none"
  say s!"stage 1 done at {(← IO.monoMsNow) - t0} ms"
  let ser0 := m2.read64 (L.enc0 + 0x28)
  let n0 := (m2.read64 (L.enc0 + 0x30)).toNat
  let m3 ← stageTryFrom c m2 ser0 n0 L.msg "message 1 (counter 0, addresses)"
  let m3 ← stageTryFrom c m3 (m3.read64 (L.enc1 + 0x28)) (m3.read64 (L.enc1 + 0x30)).toNat L.msg2
    "message 2 (counter 1, no addresses)"
  let (m4, stB1) ← stageDec c m3 L.ssB L.msg L.dec stB "message 1: DH step"
  let (m4, stB2) ← stageDec c m4 L.ssB L.msg2 L.dec2 stB1 "message 2: same chain, no DH step"
  let (m4, _) ← stageDec c m4 L.ssB L.msg L.dec3 stB2 "replay of message 1"
  say s!"stages 2-3 done at {(← IO.monoMsNow) - t0} ms"
  let stA1 := mFrom.2
  let _ ← stageApply c m4 L.otr L.ssA mEnc1.2 stA1 "after two encrypts"
  let sc := L.scratch
  let flipA := sc
  let mE := (memCopy m3 flipA ser0 n0).write8 (flipA + BitVec.ofNat 64 (n0 - 1))
    (m3.read8 (ser0 + BitVec.ofNat 64 (n0 - 1)) ^^^ 1)
  let mE := ((memCopy mE L.msgE L.msg 120).write64 (L.msgE + 0x28) flipA)
  let _ ← stageDec c mE L.ssB L.msgE L.decE stB "flipped MAC byte"
  let mE := (memCopy m3 L.msgE L.msg 120).write32 (L.msgE + 0x68) 30000
  let _ ← stageDec c mE L.ssB L.msgE L.decE stB "counter 30000 (> 25000 ahead)"
  let vA := sc + 256
  for (case_, b) in [("version byte 0x24 (legacy v2)", (0x24 : BitVec 8)),
                     ("version byte 0x54 (unrecognized v5)", 0x54)] do
    let mV := (memCopy m3 vA ser0 n0).write8 vA b
    let _ ← stageTryFrom c mV vA n0 L.retE case_
  for (case_, bs) in [("ratchet key 5 bytes (bad key length)", badKeyLenBytes),
                      ("ratchet key type 0x06 (bad key type)", badKeyTypeBytes),
                      ("8 bytes (too short)", List.replicate 8 0x34)] do
    let _ ← stageTryFrom c (m3.writeBytes vA bs) vA bs.length L.retE case_
  let _ ← stageFrom c c.base L.ssA0 L.otrErr stA0 "no sender chain"
  say s!"all done in {(← IO.monoMsNow) - t0} ms"

#eval main

