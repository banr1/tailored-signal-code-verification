/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import Arm64.Testing.Harness.TestCase

/-!
# Framed Binary Oracle Server

Implements the length-prefixed little-endian stdin/stdout wire protocol for `diff_eval --serve`,
backing `LeanOracle` in `tools/run-trusted-tests/src/lean_oracle.rs`. Supports `CMD_LOAD` (`0x01`),
`CMD_STEP` (`0x02`), `CMD_RUN` (`0x03`), `CMD_READ` (`0x04`), and parallel `CMD_RUN_BATCH` (`0x05`).
-/

@[expose] public section

namespace Testing.Harness

open Arm64

/-- Sentinel `exit_pc` (`u64::MAX`) indicating no early-exit PC stop condition. -/
def noExitPC : UInt64 := 0xffffffffffffffff

def readU32LE (ba : ByteArray) (off : Nat) : UInt32 :=
  (ba.get! (off + 0)).toUInt32 |||
  ((ba.get! (off + 1)).toUInt32 <<< 8) |||
  ((ba.get! (off + 2)).toUInt32 <<< 16) |||
  ((ba.get! (off + 3)).toUInt32 <<< 24)

def pushU32LE (ba : ByteArray) (v : UInt32) : ByteArray :=
  ba.push (v &&& 0xff).toUInt8
  |> (·.push ((v >>> 8) &&& 0xff).toUInt8)
  |> (·.push ((v >>> 16) &&& 0xff).toUInt8)
  |> (·.push ((v >>> 24) &&& 0xff).toUInt8)

/-- Loaded session state for `diff_eval --serve`. -/
structure ServedSession where
  state    : State := {}
  fpcr     : UInt64 := 0
  fpsr     : UInt64 := 0
  watch    : Array (UInt64 × Nat) := #[]
  exitPC   : UInt64 := noExitPC
  maxSteps : Nat := 1
  deriving Inhabited

/-- Execution outcome returned by a `STEP`, `RUN`, `READ`, or `RUN_BATCH` command. -/
inductive ServedOutcome where
  | ok (state : State) (fpcr fpsr : UInt64) (watch : Array (UInt64 × Nat)) (steps : Nat)
  | unmodeled (pc : UInt64) (word : UInt32)
  | fault (pc : UInt64) (kind : UInt8)
  | stepLimit (pc : UInt64)
  | oracleError (msg : String)

/-- Lookup a code byte across `(base, codeBytes)` blocks. -/
def lookupCodeByte (codeBlocks : Array (UInt64 × ByteArray)) (au : UInt64) : Option UInt8 := Id.run do
  for (base, cbytes) in codeBlocks do
    if au >= base then
      let idx := (au - base).toNat
      if idx < cbytes.size then
        return some (cbytes.get! idx)
  return none

/-- Lookup an initial data byte across `(addr, memBytes)` writes (later writes win). -/
def lookupDataByte (memWrites : Array (UInt64 × ByteArray)) (au : UInt64) : UInt8 := Id.run do
  let mut res : UInt8 := 0
  for (addr, mbytes) in memWrites do
    if au >= addr then
      let idx := (au - addr).toNat
      if idx < mbytes.size then
        res := mbytes.get! idx
  return res

/-- Check whether `au` lies in any mapped range `[s, e)` or initial data write. -/
def isDataMapped (mapped : Array (UInt64 × UInt64)) (memWrites : Array (UInt64 × ByteArray))
    (au : UInt64) : Bool := Id.run do
  for (s, e) in mapped do
    if au >= s && au < e then
      return true
  for (addr, mbytes) in memWrites do
    if au >= addr && (au - addr).toNat < mbytes.size then
      return true
  return false

/-- Decode one `TestInput` record from `ba` starting at `off0`, returning `(ServedSession, nextOff)`. -/
def decodeTestInput (ba : ByteArray) (off0 : Nat) : Option (ServedSession × Nat) := Id.run do
  if off0 + 817 > ba.size then
    return none
  let mut gprArr : Array (BitVec 64) := Array.mkEmpty 31
  for i in [0:31] do
    let v := readU64LE ba (off0 + i * 8)
    gprArr := gprArr.push (BitVec.ofNat 64 v.toNat)
  let vBase := off0 + 248
  let mut vregArr : Array (BitVec 128) := Array.mkEmpty 32
  for i in [0:32] do
    let lo := readU64LE ba (vBase + i * 16)
    let hi := readU64LE ba (vBase + i * 16 + 8)
    vregArr := vregArr.push ((BitVec.ofNat 64 hi.toNat) ++ (BitVec.ofNat 64 lo.toNat))
  let sp := readU64LE ba (off0 + 760)
  let pc := readU64LE ba (off0 + 768)
  let nzcv := ba.get! (off0 + 776) &&& 0xf
  let fpcr := readU64LE ba (off0 + 777)
  let fpsr := readU64LE ba (off0 + 785)
  let tpidr := readU64LE ba (off0 + 793)
  let exitPC := readU64LE ba (off0 + 801)
  let maxSteps := (readU64LE ba (off0 + 809)).toNat
  let mut off := off0 + 817

  if off + 4 > ba.size then return none
  let numCode := (readU32LE ba off).toNat
  off := off + 4
  let mut codeBlocks : Array (UInt64 × ByteArray) := Array.mkEmpty numCode
  for _ in [0:numCode] do
    if off + 12 > ba.size then return none
    let base := readU64LE ba off
    let nWords := (readU32LE ba (off + 8)).toNat
    off := off + 12
    let byteLen := nWords * 4
    if off + byteLen > ba.size then return none
    codeBlocks := codeBlocks.push (base, ba.extract off (off + byteLen))
    off := off + byteLen

  if off + 4 > ba.size then return none
  let numMem := (readU32LE ba off).toNat
  off := off + 4
  let mut memWrites : Array (UInt64 × ByteArray) := Array.mkEmpty numMem
  for _ in [0:numMem] do
    if off + 12 > ba.size then return none
    let addr := readU64LE ba off
    let len := (readU32LE ba (off + 8)).toNat
    off := off + 12
    if off + len > ba.size then return none
    memWrites := memWrites.push (addr, ba.extract off (off + len))
    off := off + len

  if off + 4 > ba.size then return none
  let numMapped := (readU32LE ba off).toNat
  off := off + 4
  let mut mapped : Array (UInt64 × UInt64) := Array.mkEmpty numMapped
  for _ in [0:numMapped] do
    if off + 16 > ba.size then return none
    let s := readU64LE ba off
    let e := readU64LE ba (off + 8)
    off := off + 16
    mapped := mapped.push (s, e)

  if off + 4 > ba.size then return none
  let numWatch := (readU32LE ba off).toNat
  off := off + 4
  let mut watch : Array (UInt64 × Nat) := Array.mkEmpty numWatch
  for _ in [0:numWatch] do
    if off + 16 > ba.size then return none
    let s := readU64LE ba off
    let e := readU64LE ba (off + 8)
    off := off + 16
    let len := if e >= s then (e - s).toNat else 0
    watch := watch.push (s, len)

  let initMem : Memory := Memory.ofFn
    (fun a =>
      let au := a.toNat.toUInt64
      match lookupCodeByte codeBlocks au with
      | some b => BitVec.ofNat 8 b.toNat
      | none => BitVec.ofNat 8 (lookupDataByte memWrites au).toNat)
    (fun a =>
      let au := a.toNat.toUInt64
      if (lookupCodeByte codeBlocks au).isSome then
        some Perm.rx
      else if isDataMapped mapped memWrites au then
        some Perm.rw
      else
        none)

  let st : State := {
    pc := BitVec.ofNat 64 pc.toNat
    sp := BitVec.ofNat 64 sp.toNat
    regs := ⟨fun idx => if idx.toNat < 31 then gprArr[idx.toNat]! else 0#64⟩
    vregs := ⟨fun idx => vregArr[idx.toNat]!⟩
    pstate := PState.ofBits4 (BitVec.ofNat 4 nzcv.toNat)
    fpsr := BitVec.ofNat 32 (fpsr.toNat &&& 0x0800009f)
    tpidrEl0 := BitVec.ofNat 64 tpidr.toNat
    mem := initMem
    status := .Running
  }
  return some ({
    state := st
    fpcr := fpcr
    fpsr := (fpsr.toNat &&& 0x0800009f).toUInt64
    watch := watch
    exitPC := exitPC
    maxSteps := maxSteps
  }, off)

/-- Classify an `ExecStatus` fault message and instruction word into a `FaultKind` tag (`0..4`). -/
def classifyFaultKind (w : BitVec 32) (status : ExecStatus) : UInt8 :=
  if (w &&& 0xffe0001f#32) == 0xd4000001#32 then
    3 -- FaultKind::Svc
  else match status with
  | .Exception msg =>
    if (msg.splitOn "permission").length > 1 then 0 -- FaultKind::Unmapped
    else if (msg.splitOn "alignment").length > 1 then 1 -- FaultKind::Misaligned
    else if msg == "udf" || (msg.splitOn "brk").length > 1 then 2 -- FaultKind::Undefined
    else 4 -- FaultKind::Other
  | _ => 4

/-- Step a single instruction in `sess`, updating `sess.state` on success and returning `ServedOutcome`. -/
def stepSession (sess : ServedSession) : ServedSession × ServedOutcome :=
  let st := sess.state
  let pcU64 := st.pc.toNat.toUInt64
  if sess.fpcr != 0 then
    (sess, .fault pcU64 4)
  else if st.pc.toNat % 4 != 0 then
    (sess, .fault pcU64 1)
  else if !st.mem.canExec st.pc 4 then
    (sess, .fault pcU64 0)
  else
    let w := st.mem.read32 st.pc
    if (w &&& 0xffe0001f#32) == 0xd4000001#32 then
      (sess, .fault pcU64 3)
    else
      match decode w with
      | none => (sess, .unmodeled pcU64 w.toNat.toUInt32)
      | some inst =>
        let sf := execInst inst st
        if sf.status != .Running then
          (sess, .fault pcU64 (classifyFaultKind w sf.status))
        else
          let fpsrOut := sf.fpsr.toNat.toUInt64
          let sess' := { sess with state := sf, fpsr := fpsrOut }
          (sess', .ok sf sess.fpcr fpsrOut sess.watch 1)

/-- Run `sess` up to `sess.maxSteps` instructions until `PC == sess.exitPC`. -/
def runSession (sess : ServedSession) : ServedOutcome := Id.run do
  let mut cur := sess
  let mut steps := 0
  if cur.fpcr != 0 then
    return .fault cur.state.pc.toNat.toUInt64 4
  if cur.maxSteps == 0 then
    let pcU64 := cur.state.pc.toNat.toUInt64
    if pcU64 == cur.exitPC then
      return .ok cur.state cur.fpcr cur.state.fpsr.toNat.toUInt64 cur.watch 0
    else
      return .stepLimit pcU64
  while steps < cur.maxSteps do
    let (nextSess, out) := stepSession cur
    cur := nextSess
    match out with
    | .ok sf fpcr fpsr watch _ =>
      steps := steps + 1
      let pcU64 := sf.pc.toNat.toUInt64
      if pcU64 == cur.exitPC || (cur.exitPC == noExitPC && steps >= cur.maxSteps) then
        return .ok sf fpcr fpsr watch steps
    | other =>
      return other
  return .stepLimit cur.state.pc.toNat.toUInt64

/-- Append the 801-byte serialized `CpuState` to `ba`. -/
def pushCpuState (ba : ByteArray) (st : State) (fpcr fpsr : UInt64) : ByteArray := Id.run do
  let mut out := ba
  for i in [0:31] do
    let r := (st.readReg64 (.gpr (BitVec.ofNat 5 i))).toNat.toUInt64
    out := pushU64LE out r
  for i in [0:32] do
    let v := st.readVReg128 (BitVec.ofNat 5 i)
    let lo := (v.truncate 64).toNat.toUInt64
    let hi := (v.extractLsb' 64 64).toNat.toUInt64
    out := pushU64LE (pushU64LE out lo) hi
  out := pushU64LE out st.sp.toNat.toUInt64
  out := pushU64LE out st.pc.toNat.toUInt64
  out := out.push (pstateToBits4 st.pstate).toNat.toUInt8
  out := pushU64LE out fpcr
  out := pushU64LE out fpsr
  out := pushU64LE out st.tpidrEl0.toNat.toUInt64
  return out

/-- Append a serialized `ServedOutcome` to `ba`. -/
def pushOutcome (ba : ByteArray) (out : ServedOutcome) : ByteArray := Id.run do
  match out with
  | .ok st fpcr fpsr watch steps =>
    let mut res := ba.push 0
    res := pushCpuState res st fpcr fpsr
    res := pushU64LE res steps.toUInt64
    res := pushU32LE res watch.size.toUInt32
    for (addr, len) in watch do
      res := pushU64LE res addr
      res := pushU32LE res len.toUInt32
      let baseBv := BitVec.ofNat 64 addr.toNat
      for j in [0:len] do
        let b := st.mem.read8 (baseBv + BitVec.ofNat 64 j)
        res := res.push b.toNat.toUInt8
    return res
  | .unmodeled pc word =>
    let res := ba.push 1
    let res := pushU64LE res pc
    return pushU32LE res word
  | .fault pc kind =>
    let res := ba.push 2
    let res := pushU64LE res pc
    return res.push kind
  | .stepLimit pc =>
    let res := ba.push 3
    return pushU64LE res pc
  | .oracleError msg =>
    let utf8 := msg.toUTF8
    let res := ba.push 4
    let res := pushU32LE res utf8.size.toUInt32
    return res ++ utf8

def encodeOutcome (out : ServedOutcome) : ByteArray :=
  pushOutcome (ByteArray.emptyWithCapacity 832) out

/-- Evaluate a `CMD_RUN_BATCH` payload (`u32 count` followed by `count` serialized `TestInput`s)
    in parallel across up to 32 tasks. -/
def evalRunBatchPayload (payload : ByteArray) : ByteArray := Id.run do
  if payload.size < 5 then
    return encodeOutcome (.oracleError "truncated RUN_BATCH header")
  let count := (readU32LE payload 1).toNat
  let mut sessions : Array ServedSession := Array.mkEmpty count
  let mut off := 5
  for _ in [0:count] do
    match decodeTestInput payload off with
    | some (sess, nextOff) =>
      sessions := sessions.push sess
      off := nextOff
    | none =>
      return pushU32LE ByteArray.empty 0
  let numTasks := 32
  let chunk := (count + numTasks - 1) / numTasks
  let mut tasks : Array (Task ByteArray) := Array.mkEmpty numTasks
  for t in [0:numTasks] do
    let startIdx := t * chunk
    let endIdx := Nat.min count ((t + 1) * chunk)
    if startIdx < endIdx then
      tasks := tasks.push <| Task.spawn fun () => Id.run do
        let mut sub := ByteArray.emptyWithCapacity ((endIdx - startIdx) * 832)
        for i in [startIdx:endIdx] do
          let res := runSession sessions[i]!
          sub := pushOutcome sub res
        return sub
  let mut out := pushU32LE (ByteArray.emptyWithCapacity (4 + count * 832)) count.toUInt32
  for task in tasks do
    out := out ++ task.get
  return out

/-- Read `n` bytes from `s`, returning `none` on EOF before `n` bytes. -/
def readExact (s : IO.FS.Stream) (n : Nat) : IO (Option ByteArray) := do
  if n == 0 then
    return some ByteArray.empty
  let mut acc := ByteArray.emptyWithCapacity n
  while acc.size < n do
    let rem := n - acc.size
    let chunk ← s.read (USize.ofNat rem)
    if chunk.isEmpty then
      return none
    acc := acc ++ chunk
  return some acc

/-- Write a length-prefixed frame (`u32 len` + `payload`) to `s` and flush. -/
def writeFrame (s : IO.FS.Stream) (payload : ByteArray) : IO Unit := do
  let hdr := pushU32LE ByteArray.empty payload.size.toUInt32
  s.write hdr
  s.write payload
  s.flush

/-- Run the `diff_eval --serve` loop on `stdin`/`stdout` until EOF or `CMD_QUIT` (`0x00`). -/
def serveLoop : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut sess : ServedSession := {}
  while true do
    let some hdr ← readExact stdin 4 | break
    let frameLen := (readU32LE hdr 0).toNat
    if frameLen == 0 then
      break
    let some payload ← readExact stdin frameLen | break
    let cmd := payload.get! 0
    if cmd == 0 then
      break
    else if cmd == 1 then
      -- CMD_LOAD
      match decodeTestInput payload 1 with
      | some (loaded, _) =>
        sess := loaded
        writeFrame stdout (ByteArray.mk #[0])
      | none =>
        writeFrame stdout (ByteArray.mk #[1])
    else if cmd == 2 then
      -- CMD_STEP
      let (nextSess, out) := stepSession sess
      sess := nextSess
      writeFrame stdout (encodeOutcome out)
    else if cmd == 3 then
      -- CMD_RUN
      match decodeTestInput payload 1 with
      | some (loaded, _) =>
        sess := loaded
        let out := runSession loaded
        writeFrame stdout (encodeOutcome out)
      | none =>
        writeFrame stdout (encodeOutcome (.oracleError "CMD_RUN failed to decode TestInput"))
    else if cmd == 4 then
      -- CMD_READ
      let out := ServedOutcome.ok sess.state sess.fpcr sess.state.fpsr.toNat.toUInt64 sess.watch 0
      writeFrame stdout (encodeOutcome out)
    else if cmd == 5 then
      -- CMD_RUN_BATCH
      writeFrame stdout (evalRunBatchPayload payload)
    else
      writeFrame stdout (encodeOutcome (.oracleError s!"unknown command byte {cmd}"))
  return 0

end Testing.Harness
