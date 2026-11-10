/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Invariant
public import ProofLib.Hoare.LibcHooks
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Proofs.CliExec.RadixMem
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksRows

/-!
# Closure-Free Extern Hook Dispatcher for Placed CLI Images

Core-cone (`0` `GeneratedLean.*`, `0` `CliBinaryPq`, `0` `CompFitsSatisfiable`, `0` `CliProcessFixed`)
computable `FastState` counterpart of `cliExternsPlacedSig mmpl W`:
- `MallocngCallAddrs` and `fastCallMallocngSubroutine` for replaying linked `mallocng` (`calloc`,
  `malloc`, `free`) in `aesEncHookMallocng`, `aesDecHookMallocng`, and `libcruxHmacHookMallocng`;
- `fastHookTablePlaced` (`37` mangled symbol rows matching `CliBinaryPq.cliHookTablePlaced`);
- `cliPanicSymbolsPlacedList` (`18` mangled panic symbols matching `CliBinaryPq.cliPanicSymbolsPlaced`),
  `fastIsCliPanicSymbolPlacedBs`, `hasCliHookPlaced`, and `fastExecExternPlaced`.
-/

@[expose] public section

namespace Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced

set_option autoImplicit false

open Arm64 Arm64.Memory ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification
open CryptoVerification.E2E
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.SignalSession
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
open Symbolic.BugInjection.Proofs.CliExec.RadixMem
open Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
open Symbolic.BugInjection.Proofs.CliExec.FastHooksRows

export Symbolic.BugInjection.Proofs.CliExec.FastHooksRows (FastState FastHookPost)

def fastPanicked (fs : FastState) : Option FastState := some (fs.setStatus .Panicked)

def fastMemcpy (fs : FastState) : Option FastState :=
  fastWriteBytesRet (fs.readReg64 .x0)
    (fs.mem.readBytes (fs.readReg64 .x1) (fs.readReg64 .x2).toNat) fs

def fastCliBcmp (bcmp : List (BitVec 8) → List (BitVec 8) → BitVec 64)
    (fs : FastState) : Option FastState :=
  let n := (fs.readReg64 .x2).toNat
  some ((fs.writeReg64 .x0 (bcmp (fs.mem.readBytes (fs.readReg64 .x0) n)
    (fs.mem.readBytes (fs.readReg64 .x1) n))).setPC (fs.readReg64 .lr))

def fastStrlen (fs : FastState) : Option FastState :=
  match fastStrlenScan fs.mem (fs.readReg64 .x0) 0 strlenFuel with
  | some (some len) => some ((fs.writeReg64 .x0 (BitVec.ofNat 64 len)).setPC (fs.readReg64 .lr))
  | some none => some (fs.setStatus (.Exception "strlen: no readable NUL"))
  | none => none

open Classical in
theorem fastStrlen_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastStrlen fs = some fs') :
    FastHookPost strlenHook s fs' := by
  unfold fastStrlen at hsome
  dsimp only [FastHookPost, strlenHook, retHook, unmodelled]
  rw [FastState.readReg64_eq hag .x0] at hsome
  set p := s.readReg64 .x0
  cases hscan : fastStrlenScan fs.mem p 0 strlenFuel with
  | none => rw [hscan] at hsome; cases hsome
  | some res =>
    cases res with
    | some len =>
      rw [hscan] at hsome; injection hsome with hsome; subst hsome
      obtain ⟨hex, hfind⟩ := fastStrlenScan_some_sound hag.mem hscan
      simp only [hex, ↓reduceDIte, hfind, FastState.readReg64_eq hag .lr]
      exact ⟨FastState.setPC_agrees (FastState.writeReg64_agrees hag .x0 _) (s.readReg64 .lr),
        KeepsFrozen.refl s.mem, rfl⟩
    | none =>
      rw [hscan] at hsome; injection hsome with hsome; subst hsome
      have hno := fastStrlenScan_none_sound hag.mem hscan
      simp only [hno, ↓reduceDIte]
      exact ⟨FastState.setStatus_agrees hag _, KeepsFrozen.refl s.mem, rfl⟩

def fastVecErr (fs : FastState) : Option FastState :=
  let r := fs.readReg64 .x8
  if fs.mem.canWrite r 8 then
    some ((fs.setMem (fs.mem.write64 r (BitVec.allOnes 64))).setPC (fs.readReg64 .lr))
  else none

def fastVecEmptyOk (fs : FastState) : Option FastState :=
  let r := fs.readReg64 .x8
  if fs.mem.canWrite r 24 then
    some ((fs.setMem (fastWriteVecHeader fs.mem r 0#64 1#64 0#64)).setPC (fs.readReg64 .lr))
  else none

def fastVecOk (bs : List (BitVec 8)) (fs : FastState) : Option FastState :=
  if bs.isEmpty then fastVecEmptyOk fs
  else fastReturnFreshVecU8 bs fs

def fastUnitResult (ok : Bool) (fs : FastState) : FastState :=
  (fs.writeReg64 .x0 (if ok then 0#64 else 1#64)).setPC (fs.readReg64 .lr)

def fastReadPath (fm : FastMem) (ptr len : BitVec 64) : String :=
  String.ofList ((fm.readBytes ptr len.toNat).map fun b => Char.ofNat b.toNat)

def fastWriteFile (fs : FastState) : Option FastState :=
  let ptr := fs.readReg64 .x0
  let len := fs.readReg64 .x1
  let buf := fs.readReg64 .x2
  let n := fs.readReg64 .x3
  if !(fs.mem.canRead ptr len.toNat && fs.mem.canRead buf n.toNat) then
    some (fs.setStatus (.Exception "write_file: unreadable path or bytes"))
  else
    let raw := fs.mem.readBytes ptr len.toNat
    if cliPathMaxBytes ≤ len.toNat || raw.contains 0#8 then
      some (fastUnitResult false fs)
    else
      let p := fastReadPath fs.mem ptr len
      if !fastPathOk p then
        some (fs.setStatus (.Exception "write_file: path outside the model"))
      else
        let fs1 := fs.appendTrace [.fileChanged p]
        match fs1.fs.blockingAncestor? p, fs1.fs.files p with
        | some _, _ => some (fastUnitResult false fs1)
        | none, some .dir => some (fastUnitResult false fs1)
        | none, _ =>
          some (fastUnitResult true
            (fs1.setFs (fs1.fs.setFile p (some (.file (fs1.mem.readBytes buf n.toNat))))))

def fastWriteStdout (fs : FastState) : Option FastState :=
  let buf := fs.readReg64 .x0
  let n := fs.readReg64 .x1
  if !fs.mem.canRead buf n.toNat then
    some (fs.setStatus (.Exception "write_stdout: unreadable bytes"))
  else
    some (fastUnitResult true (fs.appendTrace (TraceEvent.ofBytes .stdout (fs.mem.readBytes buf n.toNat))))

def fastMemrchr (fs : FastState) : Option FastState :=
  let x := (fs.readReg64 .x0).setWidth 8
  let ptr := fs.readReg64 .x1
  let len := fs.readReg64 .x2
  if !fs.mem.canRead ptr len.toNat then
    some (fs.setStatus (.Exception "memrchr: unreadable bytes"))
  else
    let bs := fs.mem.readBytes ptr len.toNat
    let lr := fs.readReg64 .lr
    match ((List.range bs.length).filter fun i => bs[i]? == some x).getLast? with
    | some i =>
      some (((fs.writeReg64 .x0 1#64).writeReg64 .x1 (BitVec.ofNat 64 i)).setPC lr)
    | none =>
      some ((fs.writeReg64 .x0 0#64).setPC lr)

def fastFromUtf8 (err : List (BitVec 8) → BitVec 64 × BitVec 16)
    (fs : FastState) : Option FastState :=
  let ptr := fs.readReg64 .x0
  let len := fs.readReg64 .x1
  let r := fs.readReg64 .x8
  if !(fs.mem.canRead ptr len.toNat && fs.mem.canWrite r 24) then
    some (fs.setStatus (.Exception "from_utf8: unreadable bytes or unwritable result"))
  else
    let bs := fs.mem.readBytes ptr len.toNat
    let lr := fs.readReg64 .lr
    if fastCheckUtf8 bs then
      let fm' := ((fs.mem.write64 r 0#64).write64 (r + 8#64) ptr).write64 (r + 16#64) len
      some ((fs.setMem fm').setPC lr)
    else
      let e := err bs
      let fm' := ((fs.mem.write64 r 1#64).write64 (r + 8#64) e.1).write16 (r + 16#64) e.2
      some ((fs.setMem fm').setPC lr)

open Classical in
theorem fastFromUtf8_post {err : List (BitVec 8) → BitVec 64 × BitVec 16}
    {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastFromUtf8 err fs = some fs') :
    FastHookPost (fromUtf8Hook err) s fs' := by
  unfold fastFromUtf8 at hsome
  dsimp only at hsome
  dsimp only [FastHookPost, fromUtf8Hook, retHook, unmodelled]
  rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1,
    FastState.readReg64_eq hag .x8, FastState.readReg64_eq hag .lr,
    FastMem.canRead_eq hag.mem, FastMem.canWrite_eq hag.mem,
    FastMem.readBytes_eq hag.mem] at hsome
  set ptr := s.readReg64 .x0
  set len := s.readReg64 .x1
  set r := s.readReg64 .x8
  cases hperm : (!(s.mem.canRead ptr len.toNat && s.mem.canWrite r 24)) with
  | true =>
    simp only [hperm, ↓reduceIte, Option.some.injEq] at hsome ⊢
    subst hsome
    exact ⟨FastState.setStatus_agrees hag _, KeepsFrozen.refl s.mem, rfl⟩
  | false =>
    simp only [hperm, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
    have hperm_true : (s.mem.canRead ptr len.toNat && s.mem.canWrite r 24) = true := by
      revert hperm; cases (s.mem.canRead ptr len.toNat && s.mem.canWrite r 24) <;> simp
    simp only [Bool.and_eq_true] at hperm_true
    obtain ⟨hw0, hw8, hw16⟩ := canWrite_split24 hperm_true.2
    set bs := s.mem.readBytes ptr len.toNat
    cases hutf : fastCheckUtf8 bs with
    | true =>
      simp only [hutf, ↓reduceIte, Option.some.injEq] at hsome
      subst hsome
      have huok : Utf8Ok bs := (fastCheckUtf8_iff bs).mp hutf
      simp only [huok, ↓reduceIte]
      have hm1 := FastMem.write64_agrees hag.mem r 0#64
      have hm2 := FastMem.write64_agrees hm1 (r + 8#64) ptr
      have hm3 := FastMem.write64_agrees hm2 (r + 16#64) len
      have hivs3 : HeapIntervalsAgree fs.heapIvs
          (((s.mem.write64 r 0#64).write64 (r + 8#64) ptr).write64 (r + 16#64) len) := by
        apply HeapIntervalsAgree.of_perm_eq hag.heapIvs
        intro a; rw [perm_write64_eq, perm_write64_eq, perm_write64_eq]
      exact ⟨FastState.setPC_agrees (FastState.setMem_agrees hag hm3 hivs3) (s.readReg64 .lr),
        keepsFrozen_writeVecHeader hperm_true.2 0#64 ptr len, rfl⟩
    | false =>
      simp only [hutf, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hsome
      subst hsome
      have hnuok : ¬ Utf8Ok bs := (fastCheckUtf8_eq_false_iff bs).mp hutf
      simp only [hnuok, ↓reduceIte]
      have hm1 := FastMem.write64_agrees hag.mem r 1#64
      have hm2 := FastMem.write64_agrees hm1 (r + 8#64) (err bs).1
      have hm3 := FastMem.write16_agrees hm2 (r + 16#64) (err bs).2
      have hivs3 : HeapIntervalsAgree fs.heapIvs
          (((s.mem.write64 r 1#64).write64 (r + 8#64) (err bs).1).write16 (r + 16#64) (err bs).2) := by
        apply HeapIntervalsAgree.of_perm_eq hag.heapIvs
        intro a; rw [perm_write16_eq, perm_write64_eq, perm_write64_eq]
      have kf1 := keepsFrozen_write64 hw0 1#64
      have hw8' : (s.mem.write64 r 1#64).canWrite (r + 8#64) 8 = true := by
        rw [canWrite_of_perm_eq (perm_write64_eq s.mem r 1#64)]; exact hw8
      have kf2 := keepsFrozen_write64 hw8' (err bs).1
      have hw16_2 : s.mem.canWrite (r + 16#64) 2 = true :=
        canWrite_mono_le (by decide) hw16
      have hw16' : ((s.mem.write64 r 1#64).write64 (r + 8#64) (err bs).1).canWrite
          (r + 16#64) 2 = true := by
        rw [canWrite_of_perm_eq (perm_write64_eq _ (r + 8#64) _),
          canWrite_of_perm_eq (perm_write64_eq s.mem r 1#64)]
        exact hw16_2
      have kf3 := keepsFrozen_write16 hw16' (err bs).2
      exact ⟨FastState.setPC_agrees (FastState.setMem_agrees hag hm3 hivs3) (s.readReg64 .lr),
        KeepsFrozen.trans (KeepsFrozen.trans kf1 kf2) kf3, rfl⟩

def fastFmtWrite (fs : FastState) : Option FastState :=
  some ((fs.writeReg64 .x0 0#64).setPC (fs.readReg64 .lr))

def fastFormatInner (fs : FastState) : Option FastState :=
  fastVecEmptyOk fs

def fastDurationSince (fs : FastState) : Option FastState :=
  let a := fs.readReg64 .x0
  let r := fs.readReg64 .x8
  if !(fs.mem.canRead a 12 && fs.mem.canWrite r 24) then
    some (fs.setStatus (.Exception "duration_since: unreadable self or unwritable result"))
  else
    let ns1 := (fs.mem.read32 (a + 8#64)).toNat
    let ns2 := ((fs.readReg64 .x2).setWidth 32).toNat
    if ns1 < 1000000000 ∧ ns2 < 1000000000 then
      let t1 : Int := (fs.mem.read64 a).toInt * 1000000000 + ns1
      let t2 : Int := (fs.readReg64 .x1).toInt * 1000000000 + ns2
      let d := (t1 - t2).natAbs
      let tag : BitVec 64 := if t2 ≤ t1 then 0#64 else 1#64
      let fm' := ((fs.mem.write64 r tag).write64 (r + 8#64)
        (BitVec.ofNat 64 (d / 1000000000))).write32 (r + 16#64)
        (BitVec.ofNat 32 (d % 1000000000))
      some ((fs.setMem fm').setPC (fs.readReg64 .lr))
    else
      some (fs.setStatus (.Exception "duration_since: tv_nsec out of range"))

def fastTimeAdd (fs : FastState) : Option FastState :=
  let sec := (fs.readReg64 .x0).toInt + ((fs.readReg64 .x2).toNat : Int)
  let ns : BitVec 32 := (fs.readReg64 .x3).setWidth 32 + (fs.readReg64 .x1).setWidth 32
  let carry : Bool := decide (1000000000 ≤ ns.toNat)
  let sec' := if carry then sec + 1 else sec
  let ns' := if carry then ns - 1000000000#32 else ns
  if sec' ≤ 2 ^ 63 - 1 then
    some (((fs.writeReg64 .x0 (BitVec.ofInt 64 sec')).writeReg64 .x1 (ns'.setWidth 64)).setPC
      (fs.readReg64 .lr))
  else
    some (fs.setStatus .Panicked)

def fastBlackBox (fs : FastState) : Option FastState :=
  some ((fs.writeReg64 .x0 (((fs.readReg64 .x0).setWidth 8).zeroExtend 64)).setPC
    (fs.readReg64 .lr))

def fastCompress256 (F : ShaState → List (BitVec 8) → ShaState) (fs : FastState) :
    Option FastState :=
  let x0 := fs.readReg64 .x0
  let st : ShaState := List.Vector.ofFn fun i : Fin 8 =>
    fs.mem.read32 (x0 + BitVec.ofNat 64 (4 * i.val))
  let bs := fs.mem.readBytes (fs.readReg64 .x1) (64 * (fs.readReg64 .x2).toNat)
  fastWriteBytesRet x0 (LibsignalHmac.shaStateBytes ((chunks64 bs).foldl F st)) fs

def fastAesEncOut (E : CBC.AesKey → CBC.Block → CBC.Block) (fs : FastState) : List (BitVec 8) :=
  aesCbcEncrypt E (bytesToKey32 (fs.mem.readBytes (fs.readReg64 .x2) 32))
    (CBC.bytesToBlock (fs.mem.readBytes (fs.readReg64 .x4) 16))
    (fs.mem.readBytes (fs.readReg64 .x0) (fs.readReg64 .x1).toNat)

def fastAesDecOut (D : CBC.AesKey → CBC.Block → CBC.Block) (fs : FastState) :
    Option (List (BitVec 8)) :=
  aesCbcDecrypt D (bytesToKey32 (fs.mem.readBytes (fs.readReg64 .x2) 32))
    (CBC.bytesToBlock (fs.mem.readBytes (fs.readReg64 .x4) 16))
    (fs.mem.readBytes (fs.readReg64 .x0) (fs.readReg64 .x1).toNat)

def fastPubFromSecret (pubKey : PubKeyFn) (fs : FastState) : Option FastState :=
  fastWriteBytesRet (fs.readReg64 .x8)
    (pubKey (fastReadVecN fs.mem (fs.readReg64 .x0) 32)).toList fs

def fastDiffieHellman (X : Ratchet.X25519Fn) (fs : FastState) : Option FastState :=
  fastWriteBytesRet (fs.readReg64 .x8)
    (X (fastReadVecN fs.mem (fs.readReg64 .x0) 32) (fastReadVecN fs.mem (fs.readReg64 .x1) 32)).toList fs

def fastZeroizeSecret (fs : FastState) : Option FastState :=
  fastWriteBytesRet (fs.readReg64 .x0) (List.replicate 32 0#8) fs

/-- Entry and return-sentinel addresses (`mmpl.base blkIdx + 1#64`) for the three linked
`VerifiedLibraries.mallocngLib` entrypoints replayed by `HooksMallocng`. -/
structure MallocngCallAddrs where
  callocAddr     : BitVec 64 := 0#64
  callocSentinel : BitVec 64 := 0#64
  mallocAddr     : BitVec 64 := 0#64
  mallocSentinel : BitVec 64 := 0#64
  freeAddr       : BitVec 64 := 0#64
  freeSentinel   : BitVec 64 := 0#64
  deriving DecidableEq, Repr, Inhabited

/-- Fuel bound for a single `mallocng` subroutine call (`calloc` / `malloc` / `free`). -/
abbrev mallocngSubFuel : Nat := 262144

/-- Caller stack-frame size subtracted from `sp` at the `aesEncHookMallocng` allocator call site. -/
abbrev aesEncFrameBytes : Nat := 0xcb0
abbrev aesDecFrameBytes : Nat := 0x950
abbrev libcruxHmacFrameBytes : Nat := 0xe0

/-- Decides the subroutine stopping condition (`SubroutineChoiceBridge.isSubroutineStopB`) for
return sentinel `sentinel` and entry stack pointer `spCall`. -/
def isSubroutineStopFast (sentinel spCall : BitVec 64) (st : ExecStatus) (pc sp : BitVec 64) : Bool :=
  match st with
  | .Running => (pc == sentinel) && (sp == spCall)
  | .Panicked | .Exited _ | .OutOfMemory => true
  | _ => false

/-- Iterates `subStep` within the fuel bound until `isSubroutineStopFast` holds. -/
def fastRunSubroutineLoop (subStep : FastState → Option FastState)
    (sentinel spCall : BitVec 64) : Nat → FastState → Option FastState
  | 0, fs =>
    if isSubroutineStopFast sentinel spCall fs.status fs.pc fs.sp then some fs else none
  | fuel + 1, fs =>
    if isSubroutineStopFast sentinel spCall fs.status fs.pc fs.sp then
      some fs
    else
      match subStep fs with
      | some fs' => fastRunSubroutineLoop subStep sentinel spCall fuel fs'
      | none => none

/-- Computable counterpart of `VerifiedLibraries.mallocngLib.codeROSubroutineHook`: runs `subStep`
from `entryAddr` with return sentinel `sentinel`, then restores caller `pc` and `lr` on normal return. -/
def fastCallMallocngSubroutine (subStep : FastState → Option FastState) (fuel : Nat)
    (entryAddr sentinel : BitVec 64) (fsCall : FastState) : Option FastState :=
  let lrCaller := fsCall.readReg64 .lr
  let spCall := fsCall.sp
  let fsEntry := (fsCall.writeReg64 .lr sentinel).setPC entryAddr
  match fastRunSubroutineLoop subStep sentinel spCall fuel fsEntry with
  | none => none
  | some fsOut =>
    let fs1 := if fsOut.pc == sentinel && fsOut.status == .Running then fsOut.setPC lrCaller else fsOut
    some (fs1.writeReg64 .lr lrCaller)

/-- Computable counterpart of `CryptoVerification.E2E.restoreCallerRegs` that copies caller CPU
registers (`regs`, `sp`, `pc`, `pstate`, `fpsr`) from `fsCaller` into `fsCallee`. -/
def fastRestoreCallerRegs (fsCaller fsCallee : FastState) : FastState :=
  fsCallee.withFields fun _ _ _ _ m ivs tp _ bs bk ph ffs orcl oi ex tr st sg =>
    fsCaller.withFields fun rCaller spCaller pcCaller psCaller _ _ _ fpCaller _ _ _ _ _ _ _ _ _ _ =>
      ⟨rCaller, spCaller, pcCaller, psCaller, m, ivs, tp, fpCaller, bs, bk, ph, ffs, orcl, oi, ex, tr, st, sg⟩

/-- Computable counterpart of `CryptoVerification.E2E.stepRustAlloc1`. -/
def fastStepRustAlloc1 (subStep : FastState → Option FastState) (addrs : MallocngCallAddrs)
    (zeroed : Bool) (frameBytes size : Nat)
    (k : FastState → BitVec 64 → Option FastState) (fs : FastState) : Option FastState :=
  let spCall := fs.sp - BitVec.ofNat 64 frameBytes
  let fsCall0 := (fs.writeReg64 .sp spCall).writeReg64 .x0 (BitVec.ofNat 64 size)
  let fsCall := if zeroed then fsCall0.writeReg64 .x1 1#64 else fsCall0
  let entryAddr := if zeroed then addrs.callocAddr else addrs.mallocAddr
  let sentinel := if zeroed then addrs.callocSentinel else addrs.mallocSentinel
  match fastCallMallocngSubroutine subStep mallocngSubFuel entryAddr sentinel fsCall with
  | none => none
  | some fs1 =>
    if fs1.status != .Running then
      some fs1
    else
      let p := fs1.readReg64 .x0
      let fsKeep := fastRestoreCallerRegs fs fs1
      if p == 0#64 then
        some (fsKeep.setStatus .Panicked)
      else
        k fsKeep p

/-- Computable counterpart of `CryptoVerification.E2E.stepRustDealloc1`. -/
def fastStepRustDealloc1 (subStep : FastState → Option FastState) (addrs : MallocngCallAddrs)
    (frameBytes : Nat) (ptr : BitVec 64)
    (k : FastState → Option FastState) (fs : FastState) : Option FastState :=
  let spCall := fs.sp - BitVec.ofNat 64 frameBytes
  let fsCall := (fs.writeReg64 .sp spCall).writeReg64 .x0 ptr
  match fastCallMallocngSubroutine subStep mallocngSubFuel addrs.freeAddr addrs.freeSentinel fsCall with
  | none => none
  | some fs1 =>
    if fs1.status != .Running then
      some fs1
    else
      k (fastRestoreCallerRegs fs fs1)

/-- Computable counterpart of `CryptoVerification.E2E.aesEncHookMallocng`. -/
def fastAesEncMallocng (subStep : FastState → Option FastState) (addrs : MallocngCallAddrs)
    (E : CBC.AesKey → CBC.Block → CBC.Block) (fs0 : FastState) : Option FastState :=
  if fs0.readReg64 .x3 != 32#64 || fs0.readReg64 .x5 != 16#64 then
    some (fs0.setStatus (.Exception "aes_256_cbc_encrypt: key.len != 32 or iv.len != 16"))
  else
    let ptLen := (fs0.readReg64 .x1).toNat
    let ctLen := (ptLen / 16 + 1) * 16
    if 2 ^ 63 ≤ ctLen then
      some (fs0.setStatus .Panicked)
    else
      fastStepRustAlloc1 subStep addrs true aesEncFrameBytes ctLen (fun fs1 p =>
        let ct := fastAesEncOut E fs1
        let n := BitVec.ofNat 64 ct.length
        let r := fs1.readReg64 .x8
        if fs1.mem.canWrite p ct.length && fs1.mem.canWrite r 24 then
          some ((fs1.setMem (fastWriteVecHeader (fs1.mem.writeBytes p ct) r n p n)).setPC
            (fs1.readReg64 .lr))
        else
          none) fs0

/-- Computable counterpart of `CryptoVerification.E2E.aesDecHookMallocng`. -/
def fastAesDecMallocng (subStep : FastState → Option FastState) (addrs : MallocngCallAddrs)
    (D : CBC.AesKey → CBC.Block → CBC.Block) (fs0 : FastState) : Option FastState :=
  if fs0.readReg64 .x3 != 32#64 || fs0.readReg64 .x5 != 16#64 then
    some (fs0.setStatus (.Exception "aes_256_cbc_decrypt: key.len != 32 or iv.len != 16"))
  else
    let ctLen := (fs0.readReg64 .x1).toNat
    if ctLen == 0 || ctLen % 16 != 0 then
      let r := fs0.readReg64 .x8
      if fs0.mem.canWrite r 8 && fs0.mem.canWrite (r + 8#64) 8 then
        some ((fs0.setMem ((fs0.mem.write64 r errTag).write64 (r + 8#64) 1#64)).setPC
          (fs0.readReg64 .lr))
      else
        none
    else
      fastStepRustAlloc1 subStep addrs true aesDecFrameBytes ctLen (fun fs1 p =>
        match fastAesDecOut D fs1 with
        | some pt =>
          let r := fs1.readReg64 .x8
          if fs1.mem.canWrite p pt.length && fs1.mem.canWrite r 24 then
            some ((fs1.setMem (fastWriteVecHeader (fs1.mem.writeBytes p pt) r
              (BitVec.ofNat 64 ctLen) p (BitVec.ofNat 64 pt.length))).setPC (fs1.readReg64 .lr))
          else
            none
        | none =>
          fastStepRustDealloc1 subStep addrs aesDecFrameBytes p (fun fs2 =>
            let r := fs2.readReg64 .x8
            if fs2.mem.canWrite r 8 && fs2.mem.canWrite (r + 8#64) 8 then
              some ((fs2.setMem ((fs2.mem.write64 r errTag).write64 (r + 8#64) 1#64)).setPC
                (fs2.readReg64 .lr))
            else
              none) fs1) fs0

/-- Computable counterpart of `CryptoVerification.E2E.libcruxHmacHookMallocng`. -/
def fastLibcruxHmacMallocng (subStep : FastState → Option FastState) (addrs : MallocngCallAddrs)
    (F : HMAC.ShaState → List (BitVec 8) → HMAC.ShaState) (fs0 : FastState) : Option FastState :=
  if (fs0.readReg64 .x0).setWidth 32 != 0#32 then
    some (fs0.setStatus (.Exception "libcrux_hmac::hmac: alg != Sha256"))
  else
    let keyLen := (fs0.readReg64 .x2).toNat
    let dataLen := (fs0.readReg64 .x4).toNat
    if 2 ^ 32 ≤ keyLen || 2 ^ 32 ≤ dataLen then
      some (fs0.setStatus .Panicked)
    else
      fastStepRustAlloc1 subStep addrs true libcruxHmacFrameBytes 64 (fun fs1 pKey =>
        let key := fs1.mem.readBytes (fs1.readReg64 .x1) keyLen
        fastStepRustAlloc1 subStep addrs false libcruxHmacFrameBytes 64 (fun fs2 pIpad =>
          fastStepRustAlloc1 subStep addrs false libcruxHmacFrameBytes 64 (fun fs3 pOpad =>
            let data := fs3.mem.readBytes (fs3.readReg64 .x3) dataLen
            let tag := HMAC.hmacWith F key data
            fastStepRustDealloc1 subStep addrs libcruxHmacFrameBytes pOpad (fun fs4 =>
              fastStepRustDealloc1 subStep addrs libcruxHmacFrameBytes pIpad (fun fs5 =>
                fastStepRustDealloc1 subStep addrs libcruxHmacFrameBytes pKey (fun fs6 =>
                  fastStepRustAlloc1 subStep addrs false libcruxHmacFrameBytes 32 (fun fs7 pOut =>
                    let outLen :=
                      if (fs7.readReg64 .x5).setWidth 32 &&& 1#32 != 0#32 then
                        min (fs7.readReg64 .x6).toNat 32
                      else
                        32
                    let r := fs7.readReg64 .x8
                    if fs7.mem.canWrite pOut tag.length && fs7.mem.canWrite r 24 then
                      some ((fs7.setMem (fastWriteVecHeader (fs7.mem.writeBytes pOut tag)
                        r 32#64 pOut (BitVec.ofNat 64 outLen))).setPC (fs7.readReg64 .lr))
                    else
                      none) fs6) fs5) fs4) fs3) fs2) fs1) fs0

/-- 37-row mangled-symbol hook table corresponding in order to `CliBinaryPq.cliHookTablePlaced`. -/
def fastHookTablePlaced (subStep : FastState → Option FastState) (addrs : MallocngCallAddrs)
    (W : CliHooks) : List (String × (FastState → Option FastState)) :=
  [("_RNvNtCsbvWyylYiyxg_4sha26sha51211compress512", fastCompress512 W.Q.F512),
   ("_RNvMs5_NtCs2wR8L9wiBdT_16curve25519_dalek10montgomeryNtB5_15MontgomeryPoint10to_edwards",
     fastToEdwards W.Q.montToEd),
   ("_RNvMsg_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint8compress",
     fastCompress W.Q.compress),
   ("_RNvXso_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPointNtNtNtCskxtBwYRO61I_4core3ops5arith3Neg3neg",
     fastEdNeg W.Q.edNeg),
   ("_RNvMsx_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint15is_torsion_free",
     fastTorsionFree W.Q.isTorsionFree),
   ("_RNvMsw_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint35vartime_double_scalar_mul_basepoint",
     fastDsmb W.Q.dsmb),
   ("_RNvMNtCs2wR8L9wiBdT_16curve25519_dalek6scalarNtB2_6Scalar20from_bytes_mod_order",
     fastScalarMod W.Q.scalarMod),
   ("_RNvMNtCs2wR8L9wiBdT_16curve25519_dalek6scalarNtB2_6Scalar25from_bytes_mod_order_wide",
     fastScalarWide W.Q.scalarWide),
   ("_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11encapsulate",
     fastKemEncaps W.Q.encaps),
   ("_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11decapsulate",
     fastKemDecaps W.Q.decaps),
   ("_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes9from_seed",
     fastMlkemFromSeed W.Q.K),
   ("_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes3pk1",
     fastMlkemPk1),
   ("_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes3pk2",
     fastMlkemPk2),
   ("_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate1",
     fastMlkemEncaps1 W.Q.K),
   ("_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate2",
     fastMlkemEncaps2 W.Q.K),
   ("_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental26decapsulate_compressed_key",
     fastMlkemDecaps W.Q.K),
   ("_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes",
     fastMlkemValidatePk W.Q.K),
   ("_RNvCs65XVORQObL2_12libcrux_hmac4hmac", fastLibcruxHmacMallocng subStep addrs W.C.F),
   ("memmove", fastMemcpy),
   ("bcmp", fastCliBcmp W.bcmp),
   ("strlen", fastStrlen),
   ("_RNvCs9Xul1Kjr0QF_16libsignal_cli_io10write_file", fastWriteFile),
   ("_RNvCs9Xul1Kjr0QF_16libsignal_cli_io12write_stdout", fastWriteStdout),
   ("_RNvNtNtCskxtBwYRO61I_4core5slice6memchr7memrchr", fastMemrchr),
   ("_RNvNtNtCskxtBwYRO61I_4core3str8converts9from_utf8", fastFromUtf8 W.utf8Err),
   ("_RNvNtCskxtBwYRO61I_4core3fmt5write", fastFmtWrite),
   ("_RNvNvNtCs69KKACWg7bl_5alloc3fmt6format12format_inner", fastFormatInner),
   ("_RNvMs5_NtCsfr5T3GFabw_3std4timeNtB5_10SystemTime14duration_since", fastDurationSince),
   ("_RNvXs6_NtCsfr5T3GFabw_3std4timeNtB5_10SystemTimeINtNtNtCskxtBwYRO61I_4core3ops5arith3AddNtNtBR_4time8DurationE3add",
     fastTimeAdd),
   ("_RINvCsdqpLrhraQXi_6subtle9black_boxhECs2wR8L9wiBdT_16curve25519_dalek", fastBlackBox),
   ("_RNvNtCsbvWyylYiyxg_4sha26sha25611compress256", fastCompress256 W.C.F),
   ("_RNvNtCsbKnPy0UR4Ui_13signal_crypto7aes_cbc19aes_256_cbc_encrypt",
     fastAesEncMallocng subStep addrs W.C.E),
   ("_RNvNtCsbKnPy0UR4Ui_13signal_crypto7aes_cbc19aes_256_cbc_decrypt",
     fastAesDecMallocng subStep addrs W.C.D),
   ("_RNvXs8_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_9PublicKeyINtNtCskxtBwYRO61I_4core7convert4FromRNtB5_12StaticSecretE4from",
     fastPubFromSecret W.C.pubKey),
   ("_RNvMs6_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12StaticSecret14diffie_hellman",
     fastDiffieHellman W.C.X),
   ("_RNvXsa_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12StaticSecretNtNtNtCskxtBwYRO61I_4core3ops4drop4Drop4drop",
     fastZeroizeSecret),
   ("_RNvXse_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12SharedSecretNtNtNtCskxtBwYRO61I_4core3ops4drop4Drop4drop",
     fastZeroizeSecret)]

/-- Mangled panic extern symbols corresponding to `CliBinaryPq.cliPanicSymbolsPlaced`. -/
def cliPanicSymbolsPlacedList : List String :=
  ["_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedjjEB4_",
   "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedyyEB4_",
   "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error",
   "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error",
   "_RNvNtCskxtBwYRO61I_4core6option13expect_failed",
   "_RNvNtCskxtBwYRO61I_4core6option13unwrap_failed",
   "_RNvNtCskxtBwYRO61I_4core6result13unwrap_failed",
   "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check",
   "_RNvNtCskxtBwYRO61I_4core9panicking19assert_failed_inner",
   "_RNvNtCskxtBwYRO61I_4core9panicking5panic",
   "_RNvNtCskxtBwYRO61I_4core9panicking9panic_fmt",
   "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail",
   "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow",
   "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_mul_overflow",
   "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_shl_overflow",
   "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_sub_overflow",
   "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const28panic_const_async_fn_resumed",
   "_RNvNvMs_NtCs69KKACWg7bl_5alloc3vecINtB6_3VecppE6remove13assert_failed"]

def panicPlacedExactNamesBs : List (List UInt8) :=
  (cliPanicSymbolsPlacedList ++ panicExactNames).map strUtf8Bytes

/-- UTF-8 byte-list counterpart of `CliBinaryPq.isCliPanicSymbolPlaced`. -/
def fastIsCliPanicSymbolPlacedBs (bs : List UInt8) : Bool :=
  listUInt8IsPrefix panicPrefixBs bs ||
  panicPlacedExactNamesBs.any (fun p => listUInt8Eq bs p)

def fastIsCliPanicSymbolPlaced (name : String) : Bool :=
  fastIsCliPanicSymbolPlacedBs (strUtf8Bytes name)

/-- Looks up the placed `FastState` hook for `name` prior to `abortOnPanic` wrapping. -/
def fastExternPlacedRaw? (subStep : FastState → Option FastState) (addrs : MallocngCallAddrs)
    (W : CliHooks) (name : String) : Option (FastState → Option FastState) :=
  let bs := strUtf8Bytes name
  if fastIsCliPanicSymbolPlacedBs bs then
    some fastPanicked
  else
    lookupStrUtf8 bs (fastHookTablePlaced subStep addrs W)

/-- Executes the hooked mangled extern symbol `name` on `fs` with `abortOnPanic` wrapping. -/
def fastExecExternPlaced (subStep : FastState → Option FastState) (addrs : MallocngCallAddrs)
    (W : CliHooks) (name : String) (fs : FastState) : Option FastState :=
  match fastExternPlacedRaw? subStep addrs W name with
  | some fh => (fh fs).map FastState.abortOnPanic
  | none    => none

/-- Returns `true` iff `name` is handled by `cliExternsPlacedSig mmpl W`. -/
def hasCliHookPlaced (W : CliHooks) (name : String) : Bool :=
  (fastExternPlacedRaw? (fun _ => none) {} W name).isSome

end Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced
