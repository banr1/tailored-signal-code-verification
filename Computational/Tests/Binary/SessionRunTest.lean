/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionObj -- shake: keep
public import ProofLib.Hoare.LibcHooks
public import Computational.Tests.AEAD.HMACTest
public import LibsignalBinary.Specifications.LibsignalHmac
public import LibsignalBinary.Specifications.LibsignalSessionRepr
public meta import ProofLib.Hoare.LibcHooks -- shake: keep
public meta import Computational.Tests.AEAD.HMACTest -- shake: keep
public meta import LibsignalBinary.Specifications.LibsignalHmac -- shake: keep
public meta import LibsignalBinary.Specifications.LibsignalSessionRepr -- shake: keep
public import LibsignalTestVectors.ChainKeyDerivation
public meta import LibsignalTestVectors.ChainKeyDerivation -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
public import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# Binary Run Tests for Double-Ratchet Chain and Message-Key Methods

Executes `ChainKey::next_chain_key`, `ChainKey::message_keys`,
`RatchetState::consume_message_key`, and `RatchetState::find_receiver_chain_key` in
`CryptoVerification.libsignalSessionImage` at `0x400000` with `sha256Compress` and a trace-recording
bump allocator. Verifies that final memory states and `sret` results decode to the exact outcomes
of `CryptoGames.LibsignalSession`, that multiset heap balance holds without leaks or double frees,
and that bytes pinned by `RatchetGhost.AgreeExcept` outside the touched receiver chain remain
unchanged.
-/

@[expose] public section

namespace CryptoVerification.SessionBin.RunTest

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HMAC.Tests CryptoGames.HKDF
open CryptoGames.LibsignalSession

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
elab "gen_dir%" : term => do
  let f ← IO.FS.realPath (← getFileName)
  let root ← lakeRootOf f
  return Lean.mkStrLit (root / ".GeneratedLean" / "GeneratedLean").toString

open Lean Meta Elab Term in
/-- Reconstructs the `noncomputable` linked image `id` as a computable function of `code` and `data`,
verifying at elaboration time that both fields match the on-disk `.bin` files. -/
elab "image_with_bins% " id:ident codeF:str dataF:str : term => do
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
      throwError "image_with_bins%: field {i} of {n} differs from {file}"
  let env ← getEnv
  let ty := mkApp (mkConst ``List [Level.zero]) (mkApp (mkConst ``BitVec) (mkNatLit 8))
  withLocalDeclD `code ty fun c => withLocalDeclD `data ty fun dt => do
    let args' := args.mapIdx fun i a =>
      if i == 0 then c else if i == 2 then dt else inlineNoncomputable env a
    mkLambdaFVars #[c, dt] (mkAppN v.getAppFn args')

set_option maxRecDepth 100000 in
def mkImage : List (BitVec 8) → List (BitVec 8) → Obj.LinkedImage :=
  image_with_bins% CryptoVerification.libsignalSessionImage
    "LibsignalSessionObj.code.bin" "LibsignalSessionObj.data.bin"

def testBase : BitVec 64 := 0x400000#64

def readBin (f : String) : IO (List (BitVec 8)) := do
  let b ← IO.FS.readBinFile (System.FilePath.mk gen_dir% / f)
  return b.data.toList.map fun x => BitVec.ofNat 8 x.toNat

def loadImg : IO Obj.Image := do
  let li := mkImage (← readBin "LibsignalSessionObj.code.bin")
    (← readBin "LibsignalSessionObj.data.bin")
  match li.load testBase with
  | .ok img => return img
  | .error e => throw (IO.userError s!"load failed: {e}")

def progress (msg : String) : IO Unit := do
  let h ← IO.FS.Handle.mk "/tmp/srt.progress" .append
  h.putStrLn msg
  h.flush

def check (name : String) (b : Bool) : IO Unit :=
  if b then do IO.println s!"ok   {name}"; progress s!"ok   {name}"
  else do progress s!"FAIL {name}"; throw (IO.userError s!"FAIL {name}")

def le (n : ℕ) (v : ℕ) : List (BitVec 8) := (List.range n).map fun i => BitVec.ofNat 8 (v / 256 ^ i)
def le64 (v : BitVec 64) : List (BitVec 8) := le 8 v.toNat
def le32 (v : BitVec 32) : List (BitVec 8) := le 4 v.toNat

/-- Bump-allocator pool base, capacity, and cursor address. -/
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

/-- Witness for extern stub `subtle::black_box::<u8>`: zero-extends `w0` (`u8` identity). -/
def blackBoxHook : State → State :=
  retHook fun s => s.writeReg64 .x0 ((s.readReg64 .x0) &&& 0xff#64)

def externs (F : ShaState → List (BitVec 8) → ShaState) : String → Option (State → State) :=
  fun sym =>
    if sym == "sha2::sha256::compress256" then some (LibsignalHmac.compress256Hook F)
    else if sym == "memcpy" then some hookMemcpy
    else if sym == "memmove" then some hookMemmove
    else if sym == "memset" then some hookMemset
    else if sym == "__rustc::__rust_alloc" then some allocHook
    else if sym == "__rustc::__rust_dealloc" then some deallocHook
    else if sym == "__rustc::__rust_realloc" then some reallocHook
    else if sym == "__rustc::__rust_no_alloc_shim_is_unstable_v2" then some hookNoop
    else if sym == "subtle::black_box::<u8>" then some blackBoxHook
    else if sym == "<alloc::vec::Vec<_, _>>::remove::assert_failed" then some Rust.panicked
    else none

def prog (img : Obj.Image) : Program :=
  Program.ofImage img (Rust.withPanics (externs sha256Compress))

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

def fuel : ℕ := 60000

def run (img : Obj.Image) (s : State) : State := execUntilPC fuel (prog img) retAddr s

def returned (sf : State) : Bool := sf.pc == retAddr && sf.status == .Running

def entry (img : Obj.Image) (name : String) : BitVec 64 := (Program.ofImage img).fnAddr name

def writeVec (m : Memory) (hdr : BitVec 64) (cap : ℕ) (ptr : BitVec 64) (len : ℕ) : Memory :=
  ((m.write64 hdr (BitVec.ofNat 64 cap)).write64 (hdr + 8) ptr).write64 (hdr + 16)
    (BitVec.ofNat 64 len)

def readVecHdr (m : Memory) (hdr : BitVec 64) : ℕ × BitVec 64 × ℕ :=
  ((m.read64 hdr).toNat, m.read64 (hdr + 8), (m.read64 (hdr + 16)).toNat)

def readVecU8 (m : Memory) (hdr : BitVec 64) : List (BitVec 8) :=
  let (_, p, n) := readVecHdr m hdr
  m.readBytes p n

/-- Heap buffer descriptor `(ptr, size, align)` for non-empty allocations. -/
abbrev Buf := BitVec 64 × ℕ × ℕ

def vecBuf (m : Memory) (hdr : BitVec 64) (stride align : ℕ) : List Buf :=
  let (c, p, _) := readVecHdr m hdr
  if c = 0 then [] else [(p, c * stride, align)]

/-- Byte stride of `session_structure::Chain` and `chain::MessageKey` (104 bytes, align 8). -/
def stride : ℕ := 104

/-- Memory placement parameters for an encoded `RatchetState`, with optional vector capacity slack
and trailing `sender_ratchet_key` bytes. -/
structure Placement where
  selfA : BitVec 64 := 0x30000000#64
  arena : BitVec 64 := 0x31000000#64
  capSlack : ℕ := 0
  srkExtra : List (BitVec 8) := []

/-- Encodes `st` into `m` according to `Placement` `P`, using `LibsignalSessionRepr.optChainKeyNone`
for `Option<ChainKey>::None` at chain offset `+72`. -/
def encode (P : Placement) (st : RatchetState) (m : Memory) : Memory := Id.run do
  let chainsP := P.arena
  let nc := st.receiverChains.length
  let mut m := writeVec m P.selfA (nc + P.capSlack) chainsP nc
  let mut slot := P.arena + 0x10000#64
  let mut i := 0
  for c in st.receiverChains do
    let ca := chainsP + BitVec.ofNat 64 (stride * i)
    let srk := c.senderRatchetKey.serialize ++ P.srkExtra
    m := (writeVec m ca srk.length slot srk.length).writeBytes slot srk
    slot := slot + 0x100#64
    -- `sender_ratchet_key_private` at `+24`: empty `Vec`, dangling pointer `1`.
    m := writeVec m (ca + 24) 0 1 0
    let mks := slot
    slot := slot + 0x10000#64
    let nk := c.messageKeys.length
    m := writeVec m (ca + 48) (if nk + P.capSlack = 0 then 0 else nk + P.capSlack)
      (if nk + P.capSlack = 0 then 8 else mks) nk
    let mut j := 0
    for k in c.messageKeys do
      let ka := mks + BitVec.ofNat 64 (stride * j)
      m := writeVec (writeVec (writeVec m ka 0 1 0) (ka + 24) 0 1 0) (ka + 48) 0 1 0
      m := (writeVec m (ka + 72) k.seed.length slot k.seed.length).writeBytes slot k.seed
      m := (m.write32 (ka + 96) k.counter).write32 (ka + 100) 0
      slot := slot + 0x100#64
      j := j + 1
    match c.chainKey with
    | none => m := m.write64 (ca + 72) (LibsignalSessionRepr.optChainKeyNone)
    | some ck =>
      m := (writeVec m (ca + 72) 32 slot 32).writeBytes slot (keyToBytes32 ck.key)
      m := m.write32 (ca + 96) ck.index
      slot := slot + 0x100#64
    i := i + 1
  -- `sender_chain`: `Option` tag (`u32`) at `+24`, `SenderChain` (100 bytes, align 4) at `+28`.
  match st.senderChain with
  | none => m := (m.write32 (P.selfA + 24) 0).writeBytes (P.selfA + 28) (List.replicate 100 0)
  | some sc =>
    m := (m.write32 (P.selfA + 24) 1).writeBytes (P.selfA + 28)
      (sc.ratchetKey.publicKey.bytes.toList ++ sc.ratchetKey.privateKey.bytes.toList ++
        keyToBytes32 sc.chainKey.key ++ le32 sc.chainKey.index)
  m := m.writeBytes (P.selfA + 128) (keyToBytes32 st.rootKey)
  m := m.write64 (P.selfA + 160) (BitVec.ofNat 64 st.maxForwardJumps)
  m := (m.write32 (P.selfA + 168) st.previousCounter).write32 (P.selfA + 172) 0
  return m

def vec32 (l : List (BitVec 8)) : List.Vector (BitVec 8) 32 :=
  if h : l.length = 32 then ⟨l, h⟩ else ⟨List.replicate 32 0, by simp⟩

def decMsgKey (m : Memory) (ka : BitVec 64) : MessageKeyGenerator :=
  ⟨readVecU8 m (ka + 72), m.read32 (ka + 96)⟩

/-- Decodes a 104-byte receiver `Chain` at `ca`, returning `none` if key deserialization, empty
auxiliary vectors, or 32-byte chain-key invariants fail. -/
def decChain (m : Memory) (ca : BitVec 64) : Option ReceiverChain := do
  let srk ← (PublicKey.deserialize (readVecU8 m ca)).toOption
  unless (readVecU8 m (ca + 24)).isEmpty do failure
  let (_, kp, nk) := readVecHdr m (ca + 48)
  let keys := (List.range nk).map fun j => kp + BitVec.ofNat 64 (stride * j)
  unless keys.all (fun ka => (readVecU8 m ka).isEmpty && (readVecU8 m (ka + 24)).isEmpty &&
      (readVecU8 m (ka + 48)).isEmpty && !(readVecU8 m (ka + 72)).isEmpty) do failure
  let ck : Option ChainKey :=
    if m.read64 (ca + 72) = LibsignalSessionRepr.optChainKeyNone then none
    else some ⟨bytesToKey32 (readVecU8 m (ca + 72)), m.read32 (ca + 96)⟩
  unless ck.isNone || (readVecU8 m (ca + 72)).length == 32 do failure
  return ⟨srk, ck, keys.map (decMsgKey m)⟩

def decState (selfA : BitVec 64) (m : Memory) : Option RatchetState := do
  let (_, cp, nc) := readVecHdr m selfA
  let chains ← (List.range nc).mapM fun i => decChain m (cp + BitVec.ofNat 64 (stride * i))
  let sc : Option SenderChain ← match (m.read32 (selfA + 24)).toNat with
    | 0 => pure none
    | 1 =>
      let b := m.readBytes (selfA + 28) 100
      pure (some ⟨⟨⟨vec32 (b.take 32)⟩, ⟨vec32 ((b.drop 32).take 32)⟩⟩,
        ⟨bytesToKey32 ((b.drop 64).take 32), m.read32 (selfA + 124)⟩⟩)
    | _ => failure
  return { rootKey := bytesToKey32 (m.readBytes (selfA + 128) 32), senderChain := sc,
           receiverChains := chains, previousCounter := m.read32 (selfA + 168),
           maxForwardJumps := (m.read64 (selfA + 160)).toNat }

/-- Collects all non-empty heap buffers reachable from the `RatchetState` at `selfA`. -/
def stateBufs (selfA : BitVec 64) (m : Memory) : List Buf := Id.run do
  let (_, cp, nc) := readVecHdr m selfA
  let mut out := vecBuf m selfA stride 8
  for i in List.range nc do
    let ca := cp + BitVec.ofNat 64 (stride * i)
    out := out ++ vecBuf m ca 1 1 ++ vecBuf m (ca + 24) 1 1 ++ vecBuf m (ca + 48) stride 8
    let (_, kp, nk) := readVecHdr m (ca + 48)
    for j in List.range nk do
      let ka := kp + BitVec.ofNat 64 (stride * j)
      out := out ++ vecBuf m ka 1 1 ++ vecBuf m (ka + 24) 1 1 ++ vecBuf m (ka + 48) 1 1 ++
        vecBuf m (ka + 72) 1 1
    if m.read64 (ca + 72) ≠ LibsignalSessionRepr.optChainKeyNone then out := out ++ vecBuf m (ca + 72) 1 1
  return out

/-- Reads all byte slices of the receiver chain at `ca` pinned by `RatchetGhost.AgreeExcept` when
the chain is untouched (104-byte header, key vectors, stored `MessageKey`s, and `ChainKey` bytes). -/
def chainPinBytes (m : Memory) (ca : BitVec 64) : List (List (BitVec 8)) := Id.run do
  let mut out := [m.readBytes ca 104, readVecU8 m ca, readVecU8 m (ca + 24)]
  let (_, kp, nk) := readVecHdr m (ca + 48)
  for j in List.range nk do
    let ka := kp + BitVec.ofNat 64 (stride * j)
    out := out ++ [m.readBytes ka 104, readVecU8 m ka, readVecU8 m (ka + 24),
      readVecU8 m (ka + 48), readVecU8 m (ka + 72)]
  if m.read64 (ca + 72) ≠ LibsignalSessionRepr.optChainKeyNone then out := out ++ [readVecU8 m (ca + 72)]
  return out

/-- Reads the state bytes pinned by `ConsumeMessageKeyGhost` across a call that may touch chain
`skip`: the `receiver_chains` header, `chainPinBytes` of untouched chains, and the ratchet-key
fields of chain `skip`. -/
def ghostBytes (selfA : BitVec 64) (m : Memory) (skip : Option ℕ) : List (List (BitVec 8)) :=
  Id.run do
  let (_, cp, nc) := readVecHdr m selfA
  let mut out := [m.readBytes selfA 24]
  for i in List.range nc do
    let ca := cp + BitVec.ofNat 64 (stride * i)
    if skip = some i then
      out := out ++ [m.readBytes ca 48, readVecU8 m ca, readVecU8 m (ca + 24)]
    else out := out ++ chainPinBytes m ca
  return out

def tooFarStr : List (BitVec 8) :=
  "message from too far into the future".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat

/-- `CiphertextMessageType` (`#[repr(u8)]`): `Whisper = 2`, `PreKey = 3`. -/
def msgTypeByte : MessageType → BitVec 8
  | .whisper => 2
  | .preKey => 3

/-- Decodes the 88-byte `Result<MessageKeyGenerator, SignalProtocolError>` `sret` at `r` and
collects its owned heap buffers. -/
def decResult (m : Memory) (r : BitVec 64) (t : MessageType) :
    Option (Except SignalProtocolError MessageKeyGenerator × List Buf) :=
  match (m.read32 r).toNat with
  | 1 =>
    let (c, p, _) := readVecHdr m (r + 8)
    some (.ok ⟨readVecU8 m (r + 8), m.read32 (r + 32)⟩, if c = 0 then [] else [(p, c, 1)])
  | 2 =>
    let w := m.read64 (r + 8)
    if w = 0x8000000000000017#64 then
      some (.error (.duplicatedMessage (m.read32 (r + 16)) (m.read32 (r + 20))), [])
    else if w = 0x8000000000000018#64 then
      let (c, p, n) := readVecHdr m (r + 16)
      if m.readBytes p n = tooFarStr && m.read8 (r + 40) = msgTypeByte t then
        some (.error (.invalidMessage t .tooFarInFuture), if c = 0 then [] else [(p, c, 1)])
      else none
    else none
  | _ => none

def decEv (tag : String) : TraceEvent → Option Buf
  | .userDefined t pl =>
    if t = tag then
      let w (i : ℕ) : ℕ := (pl.drop (8 * i)).take 8 |>.foldr (fun b acc => b.toNat + 256 * acc) 0
      some (BitVec.ofNat 64 (w 0), w 1, w 2)
    else none
  | _ => none

def sameBufs (a b : List Buf) : Bool :=
  a.length == b.length && a.all fun x => a.count x == b.count x

/-- Multiset heap balance across `s0 → sf`: initial state buffers plus allocations equal final
state and result buffers plus deallocations. -/
def heapOk (selfA : BitVec 64) (s0 sf : State) (resBufs : List Buf) : Bool :=
  let evs := sf.trace.drop s0.trace.length
  sameBufs (stateBufs selfA s0.mem ++ evs.filterMap (decEv "alloc"))
    (stateBufs selfA sf.mem ++ resBufs ++ evs.filterMap (decEv "dealloc"))

inductive Outcome where
  | ret (r : Except SignalProtocolError MessageKeyGenerator) (st : RatchetState)
  | panicked
  | bad (why : String)

instance : BEq (Except SignalProtocolError MessageKeyGenerator) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

def Outcome.beq : Outcome → Outcome → Bool
  | .ret r st, .ret r' st' => r == r' && st == st'
  | .panicked, .panicked => true
  | _, _ => false

def Outcome.show : Outcome → String
  | .ret (.ok k) st => s!"ok counter={k.counter.toNat} seed={k.seed.length}B chains={st.receiverChains.length}"
  | .ret (.error e) _ => s!"error {repr e}"
  | .panicked => "panicked"
  | .bad w => s!"bad: {w}"

def modelCmk (st : RatchetState) (their : PublicKey) (ck : ChainKey) (counter : BitVec 32)
    (t : MessageType) : Outcome :=
  match (RatchetState.consumeMessageKey sha256Compress their ck counter t).exec st with
  | (.error .panic, _) => .panicked
  | (r, st') => .ret r st'

/-- Index of the receiver chain modified on `Ok`, or `none` on `Err` (`ConsumeMessageKeyGhost.touched`). -/
def touchedIdx (st : RatchetState) (their : PublicKey) (ck : ChainKey) (counter : BitVec 32)
    (t : MessageType) : Option ℕ :=
  match (RatchetState.consumeMessageKey sha256Compress their ck counter t).exec st with
  | (.ok _, _) => st.findReceiverChainIndex their
  | (.error _, _) => none

/-- Argument scratch addresses for `their_ephemeral` (32B), `chain_key` (36B), `remote_address`,
and `sret` (88B). -/
def theirA : BitVec 64 := 0x13000000#64
def ckA : BitVec 64 := 0x13000100#64
def addrA : BitVec 64 := 0x13000200#64
def sretA : BitVec 64 := 0x13000300#64

/-- Executes compiled `RatchetState::consume_message_key` and decodes its `sret`, post-state, and
heap balance. -/
def binCmk (img : Obj.Image) (P : Placement) (m : Memory) (their : PublicKey) (ck : ChainKey)
    (counter : BitVec 32) (t : MessageType) : Outcome × State × Bool :=
  let m := ((m.writeBytes theirA their.bytes.toList).writeBytes ckA
    (keyToBytes32 ck.key ++ le32 ck.index)).writeBytes addrA (le 4 0x41414141)
  let s0 := callState img (entry img "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") m
    [(.x0, P.selfA), (.x1, theirA), (.x2, ckA), (.x3, counter.zeroExtend 64),
     (.x4, (msgTypeByte t).zeroExtend 64), (.x5, addrA), (.x6, 4), (.x8, sretA)]
  let sf := run img s0
  if sf.status == .Panicked then (.panicked, sf, true)
  else if !returned sf then
    let stub := (img.stubs.find? fun (_, o) => img.base + BitVec.ofNat 64 o == sf.pc).map (·.1)
    (.bad s!"did not return: pc={sf.pc} (stub {stub}) status={repr sf.status}", sf, false)
  else match decResult sf.mem sretA t, decState P.selfA sf.mem with
    | some (r, rb), some st => (.ret r st, sf, heapOk P.selfA s0 sf rb)
    | none, _ => (.bad "result not decodable", sf, false)
    | _, none => (.bad "final state not decodable", sf, false)

def pk (b : ℕ) : PublicKey := ⟨vec32 (List.replicate 32 (BitVec.ofNat 8 b))⟩

/-- Chain key `seed` of libsignal's `test_chain_key_derivation` (`ratchet/keys.rs:231-277`), from
`LibsignalTestVectors.ChainKeyDerivation` (`third_party/libsignal/test-vectors/`). -/
def ck0Bytes : List (BitVec 8) :=
  hex 32 LibsignalTestVectors.ChainKeyDerivation.seed

def mk (i : ℕ) (c : ℕ) : MessageKeyGenerator := ⟨bs (List.replicate 32 i), BitVec.ofNat 32 c⟩

/-- Two-chain test state targeting the second receiver chain so the chain-lookup loop executes. -/
def st0 (ckB : Option ChainKey) (keysB : List MessageKeyGenerator) (mfj : ℕ := 25000) : RatchetState :=
  { rootKey := bytesToKey32 (bs (List.range' 100 32))
    senderChain := some ⟨⟨pk 7, ⟨vec32 (bs (List.range' 200 32))⟩⟩,
      ⟨bytesToKey32 (bs (List.range' 50 32)), 41⟩⟩
    receiverChains := [⟨pk 1, some ⟨bytesToKey32 (bs (List.replicate 32 9)), 3⟩, [mk 1 0]⟩,
                       ⟨pk 2, ckB, keysB⟩]
    previousCounter := 17
    maxForwardJumps := mfj }

def ckAt (i : ℕ) : ChainKey := ⟨bytesToKey32 ck0Bytes, BitVec.ofNat 32 i⟩

#eval show IO Unit from do
  let t0 ← IO.monoMsNow
  let img ← loadImg
  check "image loads at 0x400000 (code and data + bss lengths, data address)"
    (img.code.length == num% (ls_field% codeLen) &&
      img.data.length == num% (ls_field% dataLen) + (mkImage [] []).bss &&
      img.dataAddr == testBase + num% (ls_xref% 0x2440 0x2444))
  check "log::MAX_LOG_LEVEL_FILTER is extern data outside the image data (reads 0 = Off)"
    (img.externData.any fun (n, a, w) => n == "log::MAX_LOG_LEVEL_FILTER" && w == 8 &&
      img.dataAddr.toNat + img.data.length ≤ a.toNat)
  let m0 := imgMem img
  let s := callState img (entry img "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key")
    ((m0.writeBytes ckA (ck0Bytes ++ le32 5))) [(.x0, ckA), (.x8, sretA)]
  let sf := run img s
  check "next_chain_key returns" (returned sf)
  check "next_chain_key = libsignal's test_chain_key_derivation next_chain_key and the model"
    (sf.mem.readBytes sretA 32 ==
        hex 32 LibsignalTestVectors.ChainKeyDerivation.nextChainKey &&
      (ChainKey.nextChainKey sha256Compress (ckAt 5)) ==
        .ok ⟨bytesToKey32 (sf.mem.readBytes sretA 32), sf.mem.read32 (sretA + 32)⟩)
  let sf := run img (callState img (entry img "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key")
    ((m0.writeBytes ckA (ck0Bytes ++ le32 0xffffffff))) [(.x0, ckA), (.x8, sretA)])
  check "next_chain_key panics at index u32::MAX (model: .error .panic)"
    (sf.status == .Panicked && ChainKey.nextChainKey sha256Compress (ckAt 0xffffffff) == .error .panic)
  let sf := run img (callState img (entry img "<libsignal_protocol::ratchet::keys::ChainKey>::message_keys")
    ((m0.writeBytes ckA (ck0Bytes ++ le32 5))) [(.x0, ckA), (.x8, sretA)])
  check "message_keys returns Seed(HMAC(ck, 0x01) = fae95235…, index) = model"
    (returned sf && sf.mem.read32 sretA == 1 &&
      readVecU8 sf.mem (sretA + 8) ==
        hex 32 0xfae95235beda3d2e00b41cf2e655dada2405b4388cae0d251a51bcd2ebdd2e40 &&
      ChainKey.messageKeys sha256Compress (ckAt 5) ==
        ⟨readVecU8 sf.mem (sretA + 8), sf.mem.read32 (sretA + 32)⟩)
  IO.println s!"chain-key checks done in {(← IO.monoMsNow) - t0} ms"
  progress s!"chain-key checks done in {(← IO.monoMsNow) - t0} ms"
  let cases : List (String × Placement × RatchetState × PublicKey × ChainKey × ℕ × MessageType) :=
    [ ("in order (counter = index, no skip)", {}, st0 (some (ckAt 3)) [], pk 2, ckAt 3, 3, .whisper),
      ("skip 2 keys, grow_one from cap 0 (alloc)", {}, st0 (some (ckAt 3)) [], pk 2, ckAt 3, 5, .whisper),
      ("skip 3 keys, grow_one from cap 1 (realloc)", {}, st0 (some (ckAt 3)) [mk 5 2], pk 2, ckAt 3, 6, .preKey),
      ("skip 1 key, spare capacity (no grow), trailing srk bytes",
        { capSlack := 2, srkExtra := bs [0xaa, 0xbb] }, st0 (some (ckAt 3)) [mk 5 2], pk 2, ckAt 3, 4, .whisper),
      ("past counter, stored key taken (remove at 1 of 3)", { capSlack := 1 },
        st0 (some (ckAt 9)) [mk 6 8, mk 5 4, mk 4 2], pk 2, ckAt 9, 4, .whisper),
      ("past counter, not stored: DuplicatedMessage", {}, st0 (some (ckAt 9)) [mk 6 8], pk 2, ckAt 9, 5, .whisper),
      ("past counter, no chain for key: DuplicatedMessage", {}, st0 (some (ckAt 9)) [], pk 3, ckAt 9, 5, .preKey),
      ("jump = max_forward_jumps is allowed", {}, st0 (some (ckAt 3)) [] 2, pk 2, ckAt 3, 5, .whisper),
      ("jump > max_forward_jumps: InvalidMessage(too far)", {}, st0 (some (ckAt 3)) [] 2, pk 2, ckAt 3, 6, .preKey),
      ("no chain for key, skip: panic (store_skipped_key expect)", {}, st0 (some (ckAt 3)) [], pk 3, ckAt 3, 5, .whisper),
      ("no chain for key, no skip: panic (set_receiver_chain_key expect)", {}, st0 (some (ckAt 3)) [], pk 3, ckAt 3, 3, .whisper),
      ("chain key index u32::MAX: panic (u32 overflow)", {}, st0 (some (ckAt 0xffffffff)) [], pk 2,
        ckAt 0xffffffff, 0xffffffff, .whisper),
      ("chain key None in state (set overwrites the niche)", {}, st0 none [], pk 2, ckAt 3, 4, .whisper) ]
  for (name, P, st, their, ck, counter, t) in cases do
    let t1 ← IO.monoMsNow
    let m := (encode P st m0)
    check s!"[{name}] encoding decodes back to the model state" (decState P.selfA m == some st)
    let (ob, sf, heap) := binCmk img P m their ck (BitVec.ofNat 32 counter) t
    let om := modelCmk st their ck (BitVec.ofNat 32 counter) t
    IO.println s!"     binary: {ob.show}; model: {om.show}"
    progress s!"{name}: binary {ob.show}; model {om.show}; {(← IO.monoMsNow) - t1} ms"
    check s!"[{name}] binary = model" (ob.beq om)
    check s!"[{name}] heap discipline" heap
    if returned sf then
      check s!"[{name}] sender chain, root key, counters byte-identical"
        (sf.mem.readBytes (P.selfA + 24) 104 == m.readBytes (P.selfA + 24) 104 &&
          sf.mem.readBytes (P.selfA + 128) 48 == m.readBytes (P.selfA + 128) 48)
      let tk := touchedIdx st their ck (BitVec.ofNat 32 counter) t
      check s!"[{name}] ghost pins outside touched chain {tk} identical (untouched chains exact)"
        (ghostBytes P.selfA sf.mem tk == ghostBytes P.selfA m tk)
    IO.println s!"     ({(← IO.monoMsNow) - t1} ms)"
  -- `sret` layout: tag `0` = `Ok(None)`, `1` = `Ok(Some)` (key `+4..+36`, index `+36`), `2` = `Err`.
  let findReceiverChainKeyName := "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_key"
  let missingStr : List (BitVec 8) :=
    "missing receiver chain key".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat
  let findReceiverChainKeyCases : List (String × RatchetState × PublicKey) :=
    [ ("chain found, key present: Ok(Some)", st0 (some (ckAt 3)) [], pk 2),
      ("chain found, key None (niche word): Err(missing receiver chain key)", st0 none [], pk 2),
      ("no chain for key: Ok(None)", st0 (some (ckAt 3)) [], pk 3) ]
  for (name, st, their) in findReceiverChainKeyCases do
    let P : Placement := {}
    let m := (encode P st m0).writeBytes theirA their.bytes.toList
    let sf := run img (callState img (entry img findReceiverChainKeyName) m
      [(.x0, P.selfA), (.x1, theirA), (.x8, sretA)])
    let tag := (sf.mem.read32 sretA).toNat
    let ok := match st.findReceiverChainKey their with
      | .ok none => tag == 0
      | .ok (some ck) => tag == 1 &&
          bytesToKey32 (sf.mem.readBytes (sretA + 4) 32) == ck.key &&
          sf.mem.read32 (sretA + 36) == ck.index
      | .error (.invalidSessionStructure .missingReceiverChainKey) => tag == 2 &&
          (sf.mem.read64 (sretA + 16)).toNat == missingStr.length &&
          sf.mem.readBytes (sf.mem.read64 (sretA + 8)) missingStr.length == missingStr
      | .error _ => false
    check s!"[findReceiverChainKey: {name}] binary = model" (returned sf && ok)
  let P : Placement := {}
  let st := st0 (some (ckAt 3)) []
  let m1 := encode P st m0
  let (o1, sf1, h1) := binCmk img P m1 (pk 2) (ckAt 3) 5 .whisper
  let (st1, ck1) := match (RatchetState.consumeMessageKey sha256Compress (pk 2) (ckAt 3) 5 .whisper).exec st with
    | (_, s) => (s, (s.receiverChains[1]?.bind (·.chainKey)).getD (ckAt 0))
  check "[sequence] call 1 (skip 2) = model" (o1.beq (modelCmk st (pk 2) (ckAt 3) 5 .whisper) && h1)
  let (o2, sf2, h2) := binCmk img P sf1.mem (pk 2) ck1 4 .whisper
  check "[sequence] call 2 (take stored key 4) = model on the model's state" (o2.beq (modelCmk st1 (pk 2) ck1 4 .whisper) && h2)
  let tk1 := touchedIdx st (pk 2) (ckAt 3) 5 .whisper
  let tk2 := touchedIdx st1 (pk 2) ck1 4 .whisper
  check "[sequence] both calls touch chain 1; ghost pins outside it identical across both calls"
    (tk1 == some 1 && tk2 == some 1 &&
      ghostBytes P.selfA sf1.mem tk1 == ghostBytes P.selfA m1 tk1 &&
      ghostBytes P.selfA sf2.mem tk2 == ghostBytes P.selfA sf1.mem tk2 &&
      ghostBytes P.selfA sf2.mem tk2 == ghostBytes P.selfA m1 tk2)
  IO.println s!"all checks done in {(← IO.monoMsNow) - t0} ms"

end CryptoVerification.SessionBin.RunTest
