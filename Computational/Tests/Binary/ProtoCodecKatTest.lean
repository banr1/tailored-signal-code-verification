/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionObj -- shake: keep
public import LibsignalBinary.Specifications.LibsignalTripleRatchetProst
public meta import LibsignalBinary.Specifications.LibsignalProtoCodec -- shake: keep
public meta import LibsignalBinary.Specifications.LibsignalTripleRatchetProst -- shake: keep
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
import LibsignalBinary.Proofs.CodeLayout

/-!
# Binary Known-Answer Tests for `SignalMessage::try_from`

Executes the compiled `<SignalMessage as TryFrom<&[u8]>>::try_from` in
`CryptoVerification.libsignalSessionImage` at `0x400000` and checks that its `sret` output matches
`SignalMessage.tryFrom protoSignalCodec` across canonical messages, duplicate and unknown fields,
nested groups, fast/slow-path and malformed varints, version/length errors, and `PublicKey` errors.
Verifies multiset heap balance on every call (`allocs = deallocs + result-owned buffers`) and
cross-checks the `DecodeError` and slow-varint hooks against `drop_glue::<DecodeError>` and the
in-image `decode_varint_slow::<&[u8]>`.
-/

@[expose] public section

namespace CryptoVerification.ProtoCodecKat

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession

open Lean Meta in
/-- Extracts raw bytes from a `List (BitVec 8)` literal expression. -/
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

private meta partial def lakeRootOf (f : System.FilePath) : IO System.FilePath := do
  match f.parent with
  | none => return "."
  | some d => if (← (d / "lakefile.lean").pathExists) then return d else lakeRootOf d

open Lean Elab Term in
elab "pckat_gen_dir%" : term => do
  let f ← IO.FS.realPath (← getFileName)
  let root ← lakeRootOf f
  return Lean.mkStrLit (root / ".GeneratedLean" / "GeneratedLean").toString

open Lean Meta Elab Term in
/-- Reconstructs the `noncomputable` linked image `id` as a computable function of `code` and `data`,
verifying at elaboration time that both fields match the on-disk `.bin` files. -/
elab "pckat_image_with_bins% " id:ident codeF:str dataF:str : term => do
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
      throwError "pckat_image_with_bins%: field {i} of {n} differs from {file}"
  let env ← getEnv
  let ty := mkApp (mkConst ``List [Level.zero]) (mkApp (mkConst ``BitVec) (mkNatLit 8))
  withLocalDeclD `code ty fun c => withLocalDeclD `data ty fun dt => do
    let args' := args.mapIdx fun i a =>
      if i == 0 then c else if i == 2 then dt else inlineNoncomputable env a
    mkLambdaFVars #[c, dt] (mkAppN v.getAppFn args')

set_option maxRecDepth 100000 in
def mkImage : List (BitVec 8) → List (BitVec 8) → Obj.LinkedImage :=
  pckat_image_with_bins% CryptoVerification.libsignalSessionImage
    "LibsignalSessionObj.code.bin" "LibsignalSessionObj.data.bin"

def testBase : BitVec 64 := 0x400000#64

def readBin (f : String) : IO (List (BitVec 8)) := do
  let b ← IO.FS.readBinFile (System.FilePath.mk pckat_gen_dir% / f)
  return b.data.toList.map fun x => BitVec.ofNat 8 x.toNat

def loadImg : IO Obj.Image := do
  let li := mkImage (← readBin "LibsignalSessionObj.code.bin")
    (← readBin "LibsignalSessionObj.data.bin")
  match li.load testBase with
  | .ok img => return img
  | .error e => throw (IO.userError s!"load failed: {e}")

def progress (msg : String) : IO Unit := do
  let h ← IO.FS.Handle.mk "/tmp/pckat.progress" .append
  h.putStrLn msg
  h.flush

def le (n : ℕ) (v : ℕ) : List (BitVec 8) := (List.range n).map fun i => BitVec.ofNat 8 (v / 256 ^ i)
def le64 (v : BitVec 64) : List (BitVec 8) := le 8 v.toNat

def hexStr (l : List (BitVec 8)) : String :=
  String.join (l.map fun b =>
    let d (n : ℕ) : Char := "0123456789abcdef".toList[n]!
    String.ofList [d (b.toNat / 16), d (b.toNat % 16)])

/-- Bump-allocator pool base, capacity, and cursor address. -/
def heapBase : BitVec 64 := 0x50000000#64
def heapCap : ℕ := 0x100000
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

/-- Allocates a 72-byte `DecodeError` `Box<Inner>` with empty stack `Vec` (`{0, 8, 0}`) and 48-byte
`kind` at `+24`. -/
def newDecodeError (s : State) (kind : List (BitVec 8)) : State × BitVec 64 :=
  let (s1, p) := bump s 72 8
  let m := ((((s1.mem.write64 p 0).write64 (p + 8) 8).write64 (p + 16) 0)).writeBytes (p + 24) kind
  (s1.setMem m, p)

def decodeErrorFromHook (s : State) : State :=
  let kind := s.mem.readBytes (s.readReg64 .x0) 48
  let s := mark s "decode_error" (kind.take 8)
  let (s1, e) := newDecodeError s kind
  retHook (fun _ => s1.writeReg64 .x0 e) s

/-- Wraps `LibsignalTripleRatchet.decodeVarintSlowHook` with a `varint_slow` coverage trace event. -/
def decodeVarintSlowHook (s : State) : State :=
  let slot := s.mem.read64 (s.readReg64 .x0)
  let bytes := s.mem.readBytes (s.mem.read64 slot) (min 10 (s.mem.read64 (slot + 8)).toNat)
  LibsignalTripleRatchet.decodeVarintSlowHook decodeErrorFromHook (mark s "varint_slow" bytes)

/-- Hook for `<DecodeError>::push`: appends a 32-byte `(message, field)` pair, doubling stack
capacity from `4` as in `RawVec`. -/
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

def externs : String → Option (State → State) := fun sym =>
  if sym == "memcpy" then some hookMemcpy
  else if sym == "memmove" then some hookMemmove
  else if sym == "memset" then some hookMemset
  else if sym == "__rustc::__rust_alloc" then some allocHook
  else if sym == "__rustc::__rust_dealloc" then some deallocHook
  else if sym == "__rustc::__rust_realloc" then some reallocHook
  else if sym == "__rustc::__rust_no_alloc_shim_is_unstable_v2" then some hookNoop
  else if sym == "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" then
    some decodeVarintSlowHook
  else if sym == "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" then
    some decodeErrorFromHook
  else if sym == "<prost::error::DecodeError>::push" then some decodeErrorPushHook
  else if sym == "bytes::panic_advance" then some Rust.panicked
  else none

def prog (img : Obj.Image) : Program :=
  Program.ofImage img (Rust.withPanics externs) externs

/-- Initial image memory: `r-x` code, image data permissions, `r--` GOT, and zeroed `rw` elsewhere
(`log::MAX_LOG_LEVEL_FILTER = 0`). -/
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

/-- Instruction words and hooks of `prog img`, indexed by 32-bit word offset. -/
structure Runner where
  prog : Program
  words : Array (BitVec 32)
  hooks : Array (Option (State → State))

def Runner.ofImage (img : Obj.Image) : Runner :=
  let P := ProtoCodecKat.prog img
  let code := img.code.toArray
  let nw := code.size / 4
  let words := Id.run do
    let mut w : Array (BitVec 32) := Array.mkEmpty nw
    for i in [0:nw] do
      w := w.push (code[4 * i + 3]! ++ code[4 * i + 2]! ++ code[4 * i + 1]! ++ code[4 * i]!)
    return w
  let hooks := Id.run do
    let mut h : Array (Option (State → State)) := Array.replicate nw none
    for (_, o) in img.stubs ++ img.symbols do
      if o % 4 = 0 ∧ o / 4 < nw then h := h.set! (o / 4) (P.hookAtOff? o)
    return h
  { prog := P, words, hooks }

/-- Array-indexed fast path for `stepState R.prog s` over immutable `r-x` code. -/
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

def snap (m : Memory) (a : BitVec 64) (n : ℕ) : Array (BitVec 8) := Id.run do
  let mut r : Array (BitVec 8) := Array.mkEmpty n
  for i in [0:n] do
    r := r.push (m.read8 (a + BitVec.ofNat 64 i))
  return r

/-- Rebuilds `m` as a depth-1 overlay of `regions` onto `base` to avoid quadratic closure chains. -/
def compact (base m : Memory) (regions : List (BitVec 64 × ℕ)) : Memory :=
  let snaps := regions.map fun (a, n) => (a, snap m a n)
  Memory.ofFn
    (fun x =>
      match snaps.find? (fun (a, arr) => (x - a).toNat < arr.size) with
      | some (a, arr) => arr[(x - a).toNat]!
      | none => base.read8 x)
    base.perm

def inputA : BitVec 64 := 0x13000000#64
def sretA : BitVec 64 := 0x13100000#64

def regions (n : ℕ) (s : State) : List (BitVec 64 × ℕ) :=
  let sp := s.sp - 64
  [(sp, (stackTop - sp).toNat + 64), (heapCur, 8),
   (heapBase, (s.mem.read64 heapCur).toNat), (inputA, n), (sretA, 128)]

/-- Executes `R.step` up to `fuel` steps until `retAddr` or non-`Running` status, compacting memory
every `every` steps (`0` disables compaction). -/
def fastRun (R : Runner) (base : Memory) (n : ℕ) (every : ℕ) (fuel : ℕ) (s : State) :
    State × ℕ := Id.run do
  let mut s := s
  let mut k := 0
  for _ in [0:fuel] do
    if s.pc == retAddr || s.status != .Running then break
    s := R.step s
    k := k + 1
    if every ≠ 0 ∧ k % every = 0 then
      s := { s with mem := compact base s.mem (regions n s) }
  return (s, k)

structure Msg where
  version : BitVec 8
  key : List (BitVec 8)
  counter : BitVec 32
  previousCounter : BitVec 32
  ciphertext : List (BitVec 8)
  pqRatchet : List (BitVec 8)
  addresses : Option (List (BitVec 8))
  serialized : List (BitVec 8)
  deriving DecidableEq, Repr

def Msg.ofModel (m : SignalMessage) : Msg :=
  { version := m.messageVersion, key := m.senderRatchetKey.bytes.toList, counter := m.counter,
    previousCounter := m.previousCounter, ciphertext := m.ciphertext, pqRatchet := m.pqRatchet,
    addresses := m.addresses, serialized := m.serialized }

inductive Out where
  | ok (m : Msg)
  | err (e : SignalProtocolError)
  | panicked
  | bad (why : String)
  deriving DecidableEq, Repr

def Out.show : Out → String
  | .ok m => s!"ok v={m.version.toNat} counter={m.counter.toNat} prev={m.previousCounter.toNat} " ++
      s!"key={hexStr (m.key.take 4)}.. ct={m.ciphertext.length}B pq={m.pqRatchet.length}B " ++
      s!"addr={(m.addresses.map List.length)} ser={m.serialized.length}B"
  | .err e => s!"error {repr e}"
  | .panicked => "panicked"
  | .bad w => s!"bad: {w}"

/-- Heap buffer descriptor `(ptr, size, align)`. -/
abbrev Buf := BitVec 64 × ℕ × ℕ

/-- Decodes the 120-byte `Result<SignalMessage, SignalProtocolError>` `sret` at `r` and collects
its owned heap buffers. -/
def decResult (m : Memory) (r : BitVec 64) : Out × List Buf :=
  let w0 := m.read64 r
  if w0 = 0xffffffffffffffff#64 then
    let k := m.read64 (r + 8)
    let p := m.read64 (r + 16)
    let e : Option SignalProtocolError :=
      if k = 0x8000000000000002#64 then some .invalidProtobufEncoding
      else if k = 0x8000000000000003#64 then some (.ciphertextMessageTooShort p.toNat)
      else if k = 0x8000000000000004#64 then some (.legacyCiphertextVersion (p.setWidth 8))
      else if k = 0x8000000000000005#64 then some (.unrecognizedCiphertextVersion (p.setWidth 8))
      else if k = 0x8000000000000007#64 then some .noKeyTypeIdentifier
      else if k = 0x8000000000000008#64 then some (.badKeyType (p.setWidth 8))
      else if k = 0x8000000000000009#64 then some (.badKeyLength p.toNat)
      else none
    match e with
    | some e => (.err e, [])
    | none => (.bad s!"unknown error word {k.toHex}", [])
  else
    let pqCap := w0.toNat
    let pqPtr := m.read64 (r + 8)
    let pqLen := (m.read64 (r + 16)).toNat
    let ctPtr := m.read64 (r + 24)
    let ctLen := (m.read64 (r + 32)).toNat
    let serPtr := m.read64 (r + 40)
    let serLen := (m.read64 (r + 48)).toNat
    let adPtr := m.read64 (r + 88)
    let adLen := (m.read64 (r + 96)).toNat
    let msg : Msg :=
      { version := m.read8 (r + 112), key := m.readBytes (r + 56) 32,
        counter := m.read32 (r + 104), previousCounter := m.read32 (r + 108),
        ciphertext := m.readBytes ctPtr ctLen, pqRatchet := m.readBytes pqPtr pqLen,
        addresses := if adPtr = 0 then none else some (m.readBytes adPtr adLen),
        serialized := m.readBytes serPtr serLen }
    let bufs : List Buf :=
      (if pqCap = 0 then [] else [(pqPtr, pqCap, 1)]) ++
      (if ctLen = 0 then [] else [(ctPtr, ctLen, 1)]) ++
      (if serLen = 0 then [] else [(serPtr, serLen, 1)]) ++
      (if adPtr = 0 ∨ adLen = 0 then [] else [(adPtr, adLen, 1)])
    (.ok msg, bufs)

def decEv (tag : String) : TraceEvent → Option Buf
  | .userDefined t pl =>
    if t = tag then
      let w (i : ℕ) : ℕ := (pl.drop (8 * i)).take 8 |>.foldr (fun b acc => b.toNat + 256 * acc) 0
      some (BitVec.ofNat 64 (w 0), w 1, w 2)
    else none
  | _ => none

def sameBufs (a b : List Buf) : Bool :=
  a.length == b.length && a.all fun x => a.count x == b.count x

/-- Multiset heap balance: `allocs = deallocs + resBufs`. -/
def heapOk (sf : State) (resBufs : List Buf) : Bool :=
  sameBufs (sf.trace.filterMap (decEv "alloc"))
    (resBufs ++ sf.trace.filterMap (decEv "dealloc"))

def model (bytes : List (BitVec 8)) : Out :=
  match SignalMessage.tryFrom LibsignalProtoCodec.protoSignalCodec bytes with
  | .ok m => .ok (Msg.ofModel m)
  | .error e => .err e

def Out.cls : Out → String
  | .ok _ => "ok"
  | .err .invalidProtobufEncoding => "proto"
  | .err (.ciphertextMessageTooShort _) => "short"
  | .err (.legacyCiphertextVersion _) => "legacy"
  | .err (.unrecognizedCiphertextVersion _) => "unrec"
  | .err .noKeyTypeIdentifier => "nokeytype"
  | .err (.badKeyType _) => "badkeytype"
  | .err (.badKeyLength _) => "badkeylen"
  | _ => "other"

def bs (l : List ℕ) : List (BitVec 8) := l.map (BitVec.ofNat 8)

/-- Unsigned LEB128 encoding with fuel `f`. -/
def viAux : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, v => if v < 128 then [v] else (v % 128 + 128) :: viAux f (v / 128)

def vi (v : ℕ) : List ℕ := viAux 20 v
def key (t w : ℕ) : List ℕ := vi (8 * t + w)
def fv (t v : ℕ) : List ℕ := key t 0 ++ vi v
def fb (t : ℕ) (b : List ℕ) : List ℕ := key t 2 ++ vi b.length ++ b
def f64 (t : ℕ) : List ℕ := key t 1 ++ [1, 2, 3, 4, 5, 6, 7, 8]
def f32 (t : ℕ) : List ℕ := key t 5 ++ [9, 10, 11, 12]
def grp (t : ℕ) (body : List ℕ) : List ℕ := key t 3 ++ body ++ key t 4
def nest (t : ℕ) : ℕ → List ℕ → List ℕ
  | 0, b => b
  | d + 1, b => grp t (nest t d b)

def macB : List ℕ := [0xa0, 0xa1, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7]
def wire (v : ℕ) (body : List ℕ) (mac : List ℕ := macB) : List (BitVec 8) := bs (v :: body ++ mac)

def k33 : List ℕ := 5 :: List.range' 0x40 32
def ct16 : List ℕ := List.range' 0xc0 16
def base4 : List ℕ := fb 1 k33 ++ fv 2 7 ++ fv 3 6 ++ fb 4 ct16

def modelBuilt : List (BitVec 8) :=
  let pk : PublicKey := ⟨⟨bs (List.range' 0x11 32), by simp [bs]⟩⟩
  serializeContent LibsignalProtoCodec.protoSignalCodec 4 pk 0x12345678 0xfffffffe
    (bs (List.range 40)) (bs [1, 2, 3]) (some (bs [0x0a, 0x00])) ++ bs macB

def cases : List (String × String × List (BitVec 8)) :=
  [ -- canonical
    ("canonical v4", "ok", wire 0x44 base4),
    ("canonical v3 + pq_ratchet + addresses", "ok",
      wire 0x33 (base4 ++ fb 5 [0xee, 0xef, 0xf0] ++ fb 6 [0x0a, 0x02, 0x41, 0x42])),
    ("serializeContent (model encoder) + MAC", "ok", modelBuilt),
    ("previous_counter absent: 0", "ok", wire 0x44 (fb 1 k33 ++ fv 2 7 ++ fb 4 ct16)),
    ("empty ciphertext, empty pq_ratchet / addresses present", "ok",
      wire 0x44 (fb 1 k33 ++ fv 2 0 ++ fb 4 [] ++ fb 5 [] ++ fb 6 [])),
    ("long ciphertext (2-byte length)", "ok",
      wire 0x44 (fb 1 k33 ++ fv 2 1 ++ fb 4 ((List.range 300).map (· % 256)))),
    -- duplicates and order
    ("reverse order, duplicates (last wins), shrinking duplicate", "ok",
      wire 0x44 (fb 4 (List.range 40) ++ fv 3 1 ++ fv 2 2 ++ fb 1 [6] ++ fb 6 [1, 2, 3, 4, 5] ++
        fb 5 [9, 9] ++ fb 4 [7, 7, 7] ++ fv 2 3 ++ fb 1 k33 ++ fv 3 4 ++ fb 6 [8])),
    -- unknown fields
    ("unknown fields of every wire type, nested groups", "ok",
      wire 0x44 (fv 7 300 ++ f64 8 ++ base4 ++ f32 9 ++ fb 10 [1, 2, 3] ++
        grp 11 (fv 2 99 ++ grp 12 (f32 13 ++ fb 2 [5]) ++ f64 14) ++ fv 536870911 1)),
    -- varints
    ("multi-byte varints, u32::MAX", "ok",
      wire 0x44 (fb 1 k33 ++ fv 2 0xffffffff ++ fv 3 0x80000000 ++ fb 4 ct16)),
    ("u32 field truncated (2^32 + 5, 2^64 - 1)", "ok",
      wire 0x44 (fb 1 k33 ++ fv 2 (2 ^ 32 + 5) ++ fv 3 (2 ^ 64 - 1) ++ fb 4 ct16)),
    ("non-minimal varints (key and value)", "ok",
      wire 0x44 (fb 1 k33 ++ [0x90, 0x80, 0x00] ++ [0x87, 0x80, 0x80, 0x00] ++ fb 4 ct16)),
    ("slow path: int32::merge value", "ok",
      wire 0x44 (fb 1 k33 ++ fb 4 [1] ++ key 2 0 ++ [0xac, 0x02] ++ fb 10 [0xff])),
    ("slow path: field key", "ok",
      wire 0x44 (fb 1 k33 ++ fv 2 5 ++ fb 4 [1] ++ [0xc8, 0x80, 0x80, 0x00, 0x05] ++ fb 10 [0xff])),
    ("slow path: skip_field length", "ok",
      wire 0x44 (base4 ++ key 11 2 ++ [0x81, 0x80, 0x00] ++ [0xff])),
    ("slow path: bytes::merge length", "ok",
      wire 0x44 (fb 1 k33 ++ fv 2 5 ++ key 4 2 ++ [0x81, 0x80, 0x00] ++ [0xff])),
    ("slow path: InvalidVarint (truncated counter)", "proto",
      wire 0x44 (fb 1 k33 ++ fb 4 [1] ++ key 2 0 ++ [0xff, 0xff, 0xff])),
    ("slow path: truncated key", "proto", wire 0x44 (base4 ++ [0x80, 0x80])),
    ("10-byte varint overflow in skip_field", "proto",
      wire 0x44 (fb 1 k33 ++ fb 4 [1] ++ key 7 0 ++ List.replicate 9 0xff ++ [0x02] ++ fv 7 0 ++ [0xff])),
    ("fast path: 11-byte varint (InvalidVarint)", "proto",
      wire 0x44 (base4 ++ key 2 0 ++ List.replicate 10 0xff ++ [0x01])),
    ("fast path: 10-byte varint overflow", "proto",
      wire 0x44 (base4 ++ key 2 0 ++ List.replicate 9 0xff ++ [0x02])),
    ("fast path: 10-byte varint 2^64 - 1 (u32 truncation)", "ok",
      wire 0x44 (base4 ++ key 2 0 ++ List.replicate 9 0xff ++ [0x01])),
    -- lengths
    ("ciphertext length > remaining", "proto", wire 0x44 (fb 1 k33 ++ fv 2 1 ++ key 4 2 ++ [5, 1, 2])),
    ("ciphertext length 2^63", "proto", wire 0x44 (fb 1 k33 ++ fv 2 1 ++ key 4 2 ++ vi (2 ^ 63))),
    ("unknown field length > remaining", "proto", wire 0x44 (base4 ++ key 9 2 ++ [3, 1])),
    ("ciphertext length runs into the MAC", "proto",
      wire 0x44 (fb 1 k33 ++ fv 2 1 ++ key 4 2 ++ [4, 1, 2])),
    -- wire types and tags
    ("counter with wire type 2", "proto", wire 0x44 (fb 1 k33 ++ fb 2 [1] ++ fb 4 ct16)),
    ("ratchet_key with wire type 0", "proto", wire 0x44 (fv 1 5 ++ fv 2 1 ++ fb 4 ct16)),
    ("ciphertext with wire type 3 (StartGroup)", "proto", wire 0x44 (fb 1 k33 ++ fv 2 1 ++ grp 4 [])),
    ("addresses with wire type 5", "proto", wire 0x44 (base4 ++ f32 6)),
    ("previous_counter with wire type 1", "proto", wire 0x44 (base4 ++ f64 3)),
    ("tag 0", "proto", wire 0x44 (base4 ++ [0x00, 0x00])),
    ("wire type 6", "proto", wire 0x44 (base4 ++ key 9 6)),
    ("wire type 7", "proto", wire 0x44 (base4 ++ key 9 7)),
    ("key > u32::MAX", "proto", wire 0x44 (base4 ++ vi (2 ^ 32) ++ [0])),
    ("key = u32::MAX (tag 2^29 - 1, wire type 7)", "proto", wire 0x44 (base4 ++ vi (2 ^ 32 - 1))),
    -- groups
    ("top-level EndGroup", "proto", wire 0x44 (base4 ++ key 9 4)),
    ("group end tag mismatch", "proto", wire 0x44 (base4 ++ key 9 3 ++ key 10 4)),
    ("unterminated group", "proto", wire 0x44 (base4 ++ key 9 3 ++ fv 1 1)),
    ("group nesting depth 100", "ok", wire 0x44 (base4 ++ nest 9 100 [])),
    ("group nesting depth 101", "proto", wire 0x44 (base4 ++ nest 9 101 [])),
    ("group depth 100 with a field inside", "proto", wire 0x44 (base4 ++ nest 9 100 (fv 2 1))),
    ("group depth 99 with a field inside", "ok", wire 0x44 (base4 ++ nest 9 99 (fv 2 1))),
    -- length and version
    ("length 0", "short", []),
    ("length 8", "short", bs [0x44, 1, 2, 3, 4, 5, 6, 7]),
    ("length 9 (empty protobuf: no ratchet_key)", "proto", wire 0x44 []),
    ("version byte 0x2f (legacy)", "legacy", wire 0x2f base4),
    ("version byte 0x00 (legacy)", "legacy", wire 0x00 base4),
    ("version byte 0x30 (v3)", "ok", wire 0x30 base4),
    ("version byte 0x4f (v4)", "ok", wire 0x4f base4),
    ("version byte 0x50 (unrecognized)", "unrec", wire 0x50 base4),
    ("version byte 0xff (unrecognized)", "unrec", wire 0xff base4),
    ("MAC bytes 0xff are not parsed", "ok", wire 0x44 base4 (List.replicate 8 0xff)),
    -- missing fields
    ("missing ratchet_key", "proto", wire 0x44 (fv 2 7 ++ fb 4 ct16)),
    ("missing counter", "proto", wire 0x44 (fb 1 k33 ++ fv 3 1 ++ fb 4 ct16)),
    ("missing ciphertext", "proto", wire 0x44 (fb 1 k33 ++ fv 2 7 ++ fb 5 [1])),
    -- PublicKey::deserialize
    ("key type 0x06", "badkeytype", wire 0x44 (fb 1 (6 :: List.range 32) ++ fv 2 1 ++ fb 4 ct16)),
    ("empty key", "nokeytype", wire 0x44 (fb 1 [] ++ fv 2 1 ++ fb 4 ct16)),
    ("key = type byte only", "badkeylen", wire 0x44 (fb 1 [5] ++ fv 2 1 ++ fb 4 ct16)),
    ("key 31 bytes", "badkeylen", wire 0x44 (fb 1 (5 :: List.range 31) ++ fv 2 1 ++ fb 4 ct16)),
    ("key with 3 trailing bytes (accepted)", "ok",
      wire 0x44 (fb 1 (k33 ++ [0xd1, 0xd2, 0xd3]) ++ fv 2 1 ++ fb 4 ct16)),
    -- error order
    ("protobuf error before key error", "proto", wire 0x44 (fb 1 [6] ++ fv 2 1 ++ fb 4 ct16 ++ [0])),
    ("key error before missing counter", "badkeytype", wire 0x44 (fb 1 [6] ++ fb 4 ct16)),
    ("key error before missing ciphertext", "badkeylen", wire 0x44 (fb 1 [5, 1] ++ fv 2 1)) ]

/-!
Checks `decodeErrorFromHook` and `decodeErrorPushHook` against the `decodeErrorAtStackLen` memory
shape and `drop_glue::<DecodeError>`, and differentially tests `decodeVarintSlowHook` against
`decode_varint_slow::<&[u8]>` and `varintSlow`.
-/

def calleeSaved : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .fp]

def hookState (img : Obj.Image) (m : Memory) (regs : List (Reg × BitVec 64)) : State :=
  let marks := (calleeSaved.zip (List.range 11)).map fun (r, i) =>
    (r, 0x5a5a000000000000#64 + BitVec.ofNat 64 i)
  callState img 0 m (marks ++ regs)

def framed (s0 sf : State) : Bool :=
  returned sf && sf.sp == s0.sp && calleeSaved.all fun r => sf.readReg64 r == s0.readReg64 r

def outstandingIs (sf : State) (exp : List Buf) : Bool :=
  sameBufs (sf.trace.filterMap (decEv "alloc")) (exp ++ sf.trace.filterMap (decEv "dealloc"))

/-- Expected heap blocks of a `DecodeError` box at `e` (72-byte header plus stack buffer when `cap ≠ 0`). -/
def errBlocks (m : Memory) (e : BitVec 64) : List Buf :=
  let cap := (m.read64 e).toNat
  (e, 72, 8) :: (if cap = 0 then [] else [(m.read64 (e + 8), cap * 32, 8)])

def kindA : BitVec 64 := 0x13200000#64
def slotA : BitVec 64 := 0x13300000#64
def sliceA : BitVec 64 := 0x13300100#64
def strA : BitVec 64 := 0x13400000#64

def kindBytes (w : BitVec 64) : List (BitVec 8) :=
  le64 w ++ (List.range 40).map fun i => BitVec.ofNat 8 (0xc0 + i)

def strBytes (s : String) : List (BitVec 8) := s.toList.map fun c => BitVec.ofNat 8 c.toNat

def varintInputs : List (List ℕ) :=
  [[0x00], [0x05, 0xff], [0x7f], [0x80, 0x00], [0xac, 0x02, 0x01], [0xff, 0x7f],
    [0x80, 0x80, 0x80, 0x80, 0x01], List.replicate 9 0x80 ++ [0x01],
    List.replicate 10 0x80 ++ [0x00], List.replicate 12 0xff] ++
  ([0x00, 0x01, 0x02, 0x7f, 0x80, 0xff].map fun b => List.replicate 9 0xff ++ [b, 0x33]) ++
  ((List.range 10).map fun k => List.replicate k 0xff) ++
  ((List.range 9).map fun k => List.replicate (k + 1) 0xff ++ [0x7f, 0x55])

def compactEvery : ℕ := 1000
def runFuel : ℕ := 400000

#eval show IO Unit from do
  IO.FS.writeFile "/tmp/pckat.progress" ""
  let t0 ← IO.monoMsNow
  let img ← loadImg
  let failures ← IO.mkRef ([] : List String)
  let check (name : String) (b : Bool) : IO Unit := do
    let line := s!"{if b then "ok  " else "FAIL"} {name}"
    IO.println line
    progress line
    unless b do failures.modify (· ++ [name])
  check "image loads at 0x400000 (code and data + bss lengths)"
    (img.code.length == num% (ls_field% codeLen) &&
      img.data.length == num% (ls_field% dataLen) + (mkImage [] []).bss)
  let entryName := "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from"
  let entry := (Program.ofImage img).fnAddr entryName
  check s!"try_from at image offset 0x2591c" (entry == testBase + 0x2591c)
  let R := Runner.ofImage img
  let m0 := imgMem img
  progress s!"setup {(← IO.monoMsNow) - t0} ms"
  let setup (input : List (BitVec 8)) : Memory × State :=
    let base := compact m0 (m0.writeBytes inputA input) [(inputA, input.length)]
    (base, callState img entry base
      [(.x0, inputA), (.x1, BitVec.ofNat 64 input.length), (.x8, sretA)])
  let outcome (sf : State) : Out × Bool :=
    if sf.status == .Panicked then (.panicked, true)
    else if !returned sf then
      let off := (sf.pc - img.base).toNat
      let stub := (img.stubs.find? fun (_, o) => o == off).map (·.1)
      (.bad s!"did not return: pc={sf.pc.toHex} (stub {stub}) status={repr sf.status}", false)
    else
      let (o, bufs) := decResult sf.mem sretA
      (o, heapOk sf bufs)
  let tags (sf : State) : List String :=
    sf.trace.filterMap fun | .userDefined t _ => some t | _ => none
  let pushes (sf : State) : List String :=
    sf.trace.filterMap fun
      | .userDefined "push" pl => some (String.ofList (pl.map fun b => Char.ofNat b.toNat))
      | _ => none
  let mut seen : List String := []
  let mut maxSteps := 0
  for (name, cls, input) in cases do
    let t1 ← IO.monoMsNow
    let (base, s0) := setup input
    let (sf, k) := fastRun R base input.length compactEvery runFuel s0
    let (ob, heap) := outcome sf
    let om := model input
    maxSteps := max maxSteps k
    seen := seen ++ tags sf
    let line := s!"     [{name}] {k} steps, {(← IO.monoMsNow) - t1} ms; binary: {ob.show}; " ++
      s!"model: {om.show}; pushes {pushes sf}"
    IO.println line
    progress line
    check s!"[{name}] model class = {cls}" (om.cls == cls)
    check s!"[{name}] binary = model" (ob == om)
    check s!"[{name}] heap discipline" heap
    if cls == "ok" then
      check s!"[{name}] serialized = input" (match ob with | .ok m => m.serialized == input | _ => false)
  for t in ["varint_slow", "decode_error", "push", "alloc", "dealloc"] do
    check s!"hook / event `{t}` exercised" (seen.contains t)
  -- Cross-check `fastRun` without compaction and against `execUntilPC`.
  let obs (sf : State) : String :=
    s!"{sf.pc.toHex} {repr sf.status} {sf.sp.toHex} {(sf.readReg64 .x0).toHex} " ++
    s!"{(sf.readReg64 .x19).toHex} {hexStr (sf.mem.readBytes sretA 120)} {repr sf.trace}"
  for name in ["canonical v4", "unknown fields of every wire type, nested groups",
      "group nesting depth 101", "reverse order, duplicates (last wins), shrinking duplicate"] do
    match cases.find? (·.1 == name) with
    | none => check s!"[cross-check {name}] case exists" false
    | some (_, _, input) =>
      let t1 ← IO.monoMsNow
      let (base, s0) := setup input
      let (a, _) := fastRun R base input.length compactEvery runFuel s0
      let (b, _) := fastRun R base input.length 0 runFuel s0
      check s!"[cross-check {name}] compaction does not change the run ({(← IO.monoMsNow) - t1} ms)"
        (obs a == obs b)
  for name in ["canonical v4", "slow path: InvalidVarint (truncated counter)"] do
    match cases.find? (·.1 == name) with
    | none => check s!"[cross-check {name}] case exists" false
    | some (_, _, input) =>
      let t1 ← IO.monoMsNow
      let (base, s0) := setup input
      let (a, _) := fastRun R base input.length compactEvery runFuel s0
      let b := execUntilPC runFuel R.prog retAddr s0
      check s!"[cross-check {name}] fastRun = execUntilPC ({(← IO.monoMsNow) - t1} ms)"
        (obs a == obs b)
  let dropE := (Program.ofImage img).fnAddr
    "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]"
  check "drop_glue::<DecodeError> at image offset 0x230c" (dropE == testBase + 0x230c)
  let msg := strBytes "SignalMessage"
  let fld := strBytes "counter"
  let mStr := (m0.writeBytes strA msg).writeBytes (strA + 0x100) fld
  for w in LibsignalTripleRatchet.decodeErrorKindWords do
    let s0 := hookState img (mStr.writeBytes kindA (kindBytes w)) [(.x0, kindA)]
    let s1 := decodeErrorFromHook s0
    let e := s1.readReg64 .x0
    check s!"[from {w.toHex}] returns (sp, callee-saved kept), x0 = e ≠ 0, 8-aligned, header (0, 8, 0), kind word at e+24, outstanding = [(e, 72, 8)]"
      (framed s0 s1 && e != 0 && e.toNat % 8 == 0 && s1.mem.read64 e == 0 &&
        s1.mem.read64 (e + 8) == 8 && s1.mem.read64 (e + 16) == 0 && s1.mem.read64 (e + 24) == w &&
        outstandingIs s1 [(e, 72, 8)])
    let mut states : List State := [s1]
    let mut caps : List ℕ := []
    let mut okPush := true
    let mut s := s1
    for n in [0:5] do
      let p0 := hookState img (s.mem.write64 slotA e) [(.x0, slotA), (.x1, strA),
        (.x2, BitVec.ofNat 64 msg.length), (.x3, strA + 0x100), (.x4, BitVec.ofNat 64 fld.length)]
      let p0 := { p0 with trace := s.trace }
      let p1 := decodeErrorPushHook p0
      let cap := (p1.mem.read64 e).toNat
      caps := caps ++ [cap]
      okPush := okPush && framed p0 p1 && p1.mem.read64 slotA == e &&
        p1.mem.read64 (e + 16) == BitVec.ofNat 64 (n + 1) && decide (n + 1 ≤ cap) &&
        p1.mem.read64 (e + 24) == w && outstandingIs p1 (errBlocks p1.mem e)
      states := states ++ [p1]
      s := p1
    check s!"[from {w.toHex}] 5 pushes: each returns (frame kept), slot = e, len = n + 1 ≤ cap, kind kept, outstanding = box + buffer; caps {caps}"
      (okPush && caps == [4, 4, 4, 4, 8])
    for n in [0, 1, 4, 5] do
      let sn := (states[n]?).getD s1
      let blocks := errBlocks sn.mem e
      let d0 := hookState img sn.mem [(.x0, e)]
      let d0 := { d0 with pc := dropE }
      let (d1, _) := fastRun R sn.mem 0 0 1000 d0
      check s!"[from {w.toHex}, {n} pushes] in-image drop_glue frees exactly the {blocks.length} outstanding blocks"
        (framed d0 d1 && sameBufs (d1.trace.filterMap (decEv "dealloc")) blocks &&
          (d1.trace.filterMap (decEv "alloc")).isEmpty)
  let vsE := (Program.ofImage img).fnAddr "prost::encoding::varint::decode_varint_slow::<&[u8]>"
  check "decode_varint_slow::<&[u8]> at image offset 0x34c8" (vsE == testBase + 0x34c8)
  let heapEvs (sf : State) : List String :=
    sf.trace.filterMap fun
      | .userDefined t pl =>
        if t == "alloc" || t == "dealloc" || t == "decode_error" then some s!"{t} {hexStr pl}"
        else none
      | _ => none
  let view (sf : State) : String :=
    s!"x0={(sf.readReg64 .x0).toHex} x1={(sf.readReg64 .x1).toHex} " ++
    s!"slice=({(sf.mem.read64 sliceA).toHex}, {(sf.mem.read64 (sliceA + 8)).toHex}) " ++
    (if sf.readReg64 .x0 == 1 then s!"box={hexStr (sf.mem.readBytes (sf.readReg64 .x1) 72)} "
     else "") ++ s!"{heapEvs sf}"
  let mut nDiff := 0
  let mut nOk := 0
  for l in varintInputs do
    let input := bs l
    let m := (((mStr.writeBytes inputA input).write64 sliceA inputA).write64 (sliceA + 8)
      (BitVec.ofNat 64 input.length)).write64 slotA sliceA
    let a0 := hookState img m [(.x0, sliceA)]
    let a0 := { a0 with pc := vsE }
    let (a1, _) := fastRun R m 0 0 10000 a0
    let b0 := hookState img m [(.x0, slotA)]
    let b1 := LibsignalTripleRatchet.decodeVarintSlowHook decodeErrorFromHook b0
    let advanced (k : ℕ) : Bool :=
      b1.mem.read64 sliceA == inputA + BitVec.ofNat 64 k &&
        b1.mem.read64 (sliceA + 8) == BitVec.ofNat 64 (input.length - k)
    let modelOk : Bool :=
      match LibsignalTripleRatchet.varintSlow input with
      | some (v, k) => b1.readReg64 .x0 == 0 && b1.readReg64 .x1 == v && advanced k
      | none =>
        let e := b1.readReg64 .x1
        b1.readReg64 .x0 == 1 && b1.mem.read64 (e + 24) == LibsignalTripleRatchet.invalidVarintWord &&
          advanced (min 10 input.length) && outstandingIs b1 [(e, 72, 8)]
    if b1.readReg64 .x0 == 0 then nOk := nOk + 1
    unless framed a0 a1 && framed b0 b1 && view a1 == view b1 && modelOk do
      nDiff := nDiff + 1
      IO.println s!"     [varint {hexStr input}] image: {view a1}; hook: {view b1}; model: {modelOk}"
  check s!"varint hook = in-image decode_varint_slow::<&[u8]> = varintSlow on {varintInputs.length} inputs ({nOk} Ok, {varintInputs.length - nOk} Err)"
    (nDiff == 0)
  IO.println s!"{cases.length} cases, max {maxSteps} steps, all checks done in {(← IO.monoMsNow) - t0} ms"
  progress s!"done in {(← IO.monoMsNow) - t0} ms"
  let fs ← failures.get
  unless fs.isEmpty do throw (IO.userError s!"{fs.length} FAILED: {fs}")

end CryptoVerification.ProtoCodecKat
