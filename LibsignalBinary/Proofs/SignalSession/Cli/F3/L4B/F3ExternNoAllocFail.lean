/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
public import LibsignalBinary.Specifications.LibsignalE2E.HooksMallocng
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
import Std.Tactic.BVDecide.Normalize.Prop
import LibsignalBinary.Proofs.SpecLemmas.SyscallReadWritev

/-!
# Shared-Allocator Hook Table and Whole-Process Non-`allocFailedEvent` Invariant

Proves that every instruction under `Syscall.standard`, every hook-free
`MultiPlacedLib.codeROSubroutineHook`, and every hook in the 39-row `cliExternsPlaced mmpl W`
table preserves `allocFailedEvent ∉ s.trace`, so `Placed.cliProgPlacedSig mpl mmpl W` never logs
`allocFailedEvent` from `Placed.cliTokenPatchPlaced mpl s0`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.CBC (AesKey Block)
open CryptoGames.HMAC (ShaState)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification.E2E
  (PqxdhPrims aesDecHookMallocng aesEncHookMallocng compress512Hook compressHook dsmbHook edNegHook
   fmtWriteHook0 formatInnerHook0 kemDecapsHook kemEncapsHook libcruxHmacHookMallocng
   mlkemDecapsHook mlkemEncaps1Hook mlkemEncaps2Hook mlkemFromSeedHook mlkemPk1Hook mlkemPk2Hook
   mlkemValidatePkHook restoreCallerRegs scalarModHook scalarWideHook stepRustAlloc1
   stepRustDealloc1 timeAddHook toEdwardsHook torsionFreeHook)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister)
open CryptoVerification.LibsignalHmac (compress256Hook)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalTripleRatchet
  (diffieHellmanHook pubFromSecretHook zeroizeSecretHook)
open CryptoVerification.RustHeap (allocFailedEvent)
open CryptoVerification.SignalSession
  (CliHooks Inputs abortOnPanic cliBcmpHook cliExternsPlaced cliExternsPlacedSig
   cliHookTablePlaced cliPqxdhHookTablePlaced cliProcessInputs durationSinceExactHook fromUtf8Hook
   isCliPanicSymbolPlaced lsAesDecSym lsAesEncSym lsBlackBoxSym lsCompress256Sym
   lsDiffieHellmanSym lsDurationSinceSym lsFmtWriteSym lsFormatInnerSym lsFromUtf8Sym lsMemrchrSym
   lsPubFromSecretSym lsSharedSecretDropSym lsStaticSecretDropSym lsTimeAddSym lsWriteFileSym
   lsWriteStdoutSym memrchrHook strlenHook unitResult unmodelled writeFileHook writeStdoutHook)
open CryptoVerification.SignalSession.Cli (cliInputs loadState_fs_trace)
open CryptoVerification.SignalSession.Placed (cliProgPlacedSig cliTokenPatchPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedSigAt)
open VerifiedLibraries (mallocngLib)

/-! ## `PreservesNoAllocFailed` and `State.trace` Helpers -/

/-- A state transformer `f` never introduces `allocFailedEvent` into `s.trace`. -/
def PreservesNoAllocFailed (f : State → State) : Prop :=
  ∀ s : State, allocFailedEvent ∉ s.trace → allocFailedEvent ∉ (f s).trace

/-- Every hooked function in `ext` satisfies `PreservesNoAllocFailed`. -/
def ExternPreservesNoAllocFailed (ext : String → Option (State → State)) : Prop :=
  ∀ name f, ext name = some f → PreservesNoAllocFailed f

theorem externPreservesNoAllocFailed_none :
    ExternPreservesNoAllocFailed (fun _ => none) := by
  intro _ _ h
  cases h

private theorem ite_no_allocFailed {c : Prop} [Decidable c] {a b : State}
    (ha : allocFailedEvent ∉ a.trace) (hb : allocFailedEvent ∉ b.trace) :
    allocFailedEvent ∉ (if c then a else b).trace := by
  split
  · exact ha
  · exact hb

private theorem tr_advancePC (s : State) : s.advancePC.trace = s.trace := rfl
private theorem tr_setPC (s : State) (x : BitVec 64) : (s.setPC x).trace = s.trace := rfl
private theorem tr_setPState (s : State) (x : PState) : (s.setPState x).trace = s.trace := rfl
private theorem tr_setMem (s : State) (m : Memory) : (s.setMem m).trace = s.trace := rfl
private theorem tr_setFpsr (s : State) (x : BitVec 32) : (s.setFpsr x).trace = s.trace := rfl
private theorem tr_orFpsr (s : State) (x : BitVec 32) : (s.orFpsr x).trace = s.trace := rfl
private theorem tr_setBrk (s : State) (x : BitVec 64) : (s.setBrk x).trace = s.trace := rfl
private theorem tr_setPhysMemAvail (s : State) (n : Nat) :
    (s.setPhysMemAvail n).trace = s.trace := rfl
private theorem tr_setFs (s : State) (x : FsState) : (s.setFs x).trace = s.trace := rfl
private theorem tr_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).trace = s.trace := rfl
private theorem tr_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).trace = s.trace := rfl
private theorem tr_appendTrace (s : State) (x : List TraceEvent) :
    (s.appendTrace x).trace = s.trace ++ x := rfl
private theorem tr_nextOracle (s : State) : s.nextOracle.trace = s.trace := rfl
private theorem tr_stepExclOracle (s : State) : s.stepExclOracle.trace = s.trace := rfl
private theorem tr_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).trace = s.trace := by unfold State.writeReg64; split <;> rfl
private theorem tr_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).trace = s.trace := tr_writeReg64 s r (BitVec.zeroExtend 64 v)
private theorem tr_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).trace = s.trace := by
  cases w
  · exact tr_writeReg32 s r (v.truncate 32)
  · exact tr_writeReg64 s r v
private theorem tr_writeVReg128 (s : State) (i : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).trace = s.trace := rfl
private theorem tr_writeVReg64 (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 i v).trace = s.trace := rfl
private theorem tr_writeVReg32 (s : State) (i : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 i v).trace = s.trace := rfl
private theorem tr_setStatus (s : State) (x : ExecStatus) : (s.setStatus x).trace = s.trace := rfl

private theorem not_mem_ofBytes (strm : OutputStream) (bs : List (BitVec 8)) :
    allocFailedEvent ∉ TraceEvent.ofBytes strm bs := by
  simp [TraceEvent.ofBytes, allocFailedEvent]

private theorem not_mem_fileChanged (p : String) :
    allocFailedEvent ∉ [TraceEvent.fileChanged p] := by
  simp [allocFailedEvent]

private theorem not_mem_append_ofBytes {s : State} {strm : OutputStream} {bs : List (BitVec 8)}
    (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ s.trace ++ TraceEvent.ofBytes strm bs := by
  rw [List.mem_append, not_or]
  exact ⟨hs, not_mem_ofBytes strm bs⟩

private theorem not_mem_append_fileChanged {s : State} {p : String}
    (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ s.trace ++ [TraceEvent.fileChanged p] := by
  rw [List.mem_append, not_or]
  exact ⟨hs, not_mem_fileChanged p⟩

private theorem advancePC_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ s.advancePC.trace := hs
private theorem setPC_no_allocFailed {s : State} {x : BitVec 64}
    (hs : allocFailedEvent ∉ s.trace) : allocFailedEvent ∉ (s.setPC x).trace := hs
private theorem setPState_no_allocFailed {s : State} {x : PState}
    (hs : allocFailedEvent ∉ s.trace) : allocFailedEvent ∉ (s.setPState x).trace := hs
private theorem setMem_no_allocFailed {s : State} {m : Memory}
    (hs : allocFailedEvent ∉ s.trace) : allocFailedEvent ∉ (s.setMem m).trace := hs
private theorem setFpsr_no_allocFailed {s : State} {x : BitVec 32}
    (hs : allocFailedEvent ∉ s.trace) : allocFailedEvent ∉ (s.setFpsr x).trace := hs
private theorem orFpsr_no_allocFailed {s : State} {x : BitVec 32}
    (hs : allocFailedEvent ∉ s.trace) : allocFailedEvent ∉ (s.orFpsr x).trace := hs
private theorem stepExclOracle_no_allocFailed {s : State}
    (hs : allocFailedEvent ∉ s.trace) : allocFailedEvent ∉ s.stepExclOracle.trace := hs
private theorem writeReg64_no_allocFailed {s : State} {r : Reg} {v : BitVec 64}
    (hs : allocFailedEvent ∉ s.trace) : allocFailedEvent ∉ (s.writeReg64 r v).trace := by
  rw [tr_writeReg64]; exact hs
private theorem writeReg32_no_allocFailed {s : State} {r : Reg} {v : BitVec 32}
    (hs : allocFailedEvent ∉ s.trace) : allocFailedEvent ∉ (s.writeReg32 r v).trace := by
  rw [tr_writeReg32]; exact hs
private theorem writeReg_no_allocFailed {s : State} {w : Width} {r : Reg} {v : BitVec 64}
    (hs : allocFailedEvent ∉ s.trace) : allocFailedEvent ∉ (s.writeReg w r v).trace := by
  rw [tr_writeReg]; exact hs
private theorem writeVReg128_no_allocFailed {s : State} {i : BitVec 5} {v : BitVec 128}
    (hs : allocFailedEvent ∉ s.trace) : allocFailedEvent ∉ (s.writeVReg128 i v).trace := hs
private theorem writeVReg64_no_allocFailed {s : State} {i : BitVec 5} {v : BitVec 64}
    (hs : allocFailedEvent ∉ s.trace) : allocFailedEvent ∉ (s.writeVReg64 i v).trace := hs
private theorem writeVReg32_no_allocFailed {s : State} {i : BitVec 5} {v : BitVec 32}
    (hs : allocFailedEvent ∉ s.trace) : allocFailedEvent ∉ (s.writeVReg32 i v).trace := hs
private theorem setStatus_no_allocFailed {s : State} {st : ExecStatus}
    (hs : allocFailedEvent ∉ s.trace) : allocFailedEvent ∉ (s.setStatus st).trace := hs

set_option linter.unusedSimpArgs false in
macro "trace_norm" : tactic => `(tactic|
  simp only [tr_advancePC, tr_setPC, tr_setPState, tr_setMem, tr_setFpsr, tr_orFpsr,
    tr_setBrk, tr_setPhysMemAvail, tr_setFs, tr_setSigAction, tr_setSigAltStack,
    tr_nextOracle, tr_stepExclOracle,
    tr_appendTrace, tr_writeReg64, tr_writeReg32, tr_writeReg, tr_writeVReg128, tr_writeVReg64,
    tr_writeVReg32, tr_setStatus])

macro "no_alloc_failed_close" h:ident : tactic => `(tactic|
  (repeat' split
   repeat' split
   all_goals
     try dsimp (config := { zeta := true, zetaHave := true }) only
     try trace_norm
     first
       | exact $h
       | exact not_mem_append_ofBytes $h
       | exact not_mem_append_fileChanged $h))

/-! ## Instruction and `Syscall.standard` Non-`allocFailedEvent` Preservation -/

private theorem execAddSubImm_no_allocFailed (w : Width) (op : AddSubOp) (rd rn : Reg)
    (imm12 : BitVec 12) (shift12 : Bool) {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execAddSubImm w op rd rn imm12 shift12 s).trace := by
  dsimp (config := { zetaHave := true }) only [execAddSubImm]; no_alloc_failed_close hs

private theorem execAddSubExt_no_allocFailed (w : Width) (op : AddSubOp) (rd rn rm : Reg)
    (ext : ExtendType) (amt : Nat) {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execAddSubExt w op rd rn rm ext amt s).trace := by
  dsimp (config := { zetaHave := true }) only [execAddSubExt]; no_alloc_failed_close hs

private theorem execAddSubShift_no_allocFailed (w : Width) (op : AddSubOp) (rd rn rm : Reg)
    (sh : ShiftType) (amt : Nat) {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execAddSubShift w op rd rn rm sh amt s).trace := by
  dsimp (config := { zetaHave := true }) only [execAddSubShift]; no_alloc_failed_close hs

private theorem execAddSubCarry_no_allocFailed (w : Width) (op : AddSubOp) (rd rn rm : Reg)
    {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execAddSubCarry w op rd rn rm s).trace := by
  dsimp (config := { zetaHave := true }) only [execAddSubCarry]; no_alloc_failed_close hs

private theorem execLogicalImm_no_allocFailed (w : Width) (op : LogicalOp) (rd rn : Reg)
    (imm : BitVec 64) {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execLogicalImm w op rd rn imm s).trace := by
  dsimp (config := { zetaHave := true }) only [execLogicalImm]; no_alloc_failed_close hs

private theorem execLogicalShift_no_allocFailed (w : Width) (op : LogicalOp) (rd rn rm : Reg)
    (sh : ShiftType) (amt : Nat) {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execLogicalShift w op rd rn rm sh amt s).trace := by
  dsimp (config := { zetaHave := true }) only [execLogicalShift]; no_alloc_failed_close hs

private theorem execMoveWide_no_allocFailed (w : Width) (op : MoveWideOp) (rd : Reg)
    (imm : BitVec 16) (hw : Nat) {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execMoveWide w op rd imm hw s).trace := by
  dsimp (config := { zetaHave := true }) only [execMoveWide]; no_alloc_failed_close hs

private theorem execBitfield_no_allocFailed (w : Width) (op : BitfieldOp) (rd rn : Reg)
    (immr imms : Nat) {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execBitfield w op rd rn immr imms s).trace := by
  dsimp (config := { zetaHave := true }) only [execBitfield]; no_alloc_failed_close hs

private theorem execCondSelect_no_allocFailed (w : Width) (op : CondSelectOp) (rd rn rm : Reg)
    (cond : CondCode) {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execCondSelect w op rd rn rm cond s).trace := by
  dsimp (config := { zetaHave := true }) only [execCondSelect]; no_alloc_failed_close hs

private theorem execCondCompare_no_allocFailed (w : Width) (isSub isImm : Bool) (rn : Reg)
    (rhs : BitVec 64) (rm : Reg) (nzcv : BitVec 4) (cond : CondCode)
    {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execCondCompare w isSub isImm rn rhs rm nzcv cond s).trace := by
  dsimp (config := { zetaHave := true }) only [execCondCompare]; no_alloc_failed_close hs

private theorem execDataProc1_no_allocFailed (w : Width) (op : DataProc1Op) (rd rn : Reg)
    {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execDataProc1 w op rd rn s).trace := by
  dsimp (config := { zetaHave := true }) only [execDataProc1]; no_alloc_failed_close hs

private theorem execDataProc2_no_allocFailed (w : Width) (op : DataProc2Op) (rd rn rm : Reg)
    {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execDataProc2 w op rd rn rm s).trace := by
  dsimp (config := { zetaHave := true }) only [execDataProc2]; no_alloc_failed_close hs

private theorem execDataProc3_no_allocFailed (w : Width) (op : DataProc3Op) (rd rn rm ra : Reg)
    {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execDataProc3 w op rd rn rm ra s).trace := by
  dsimp (config := { zetaHave := true }) only [execDataProc3]; no_alloc_failed_close hs

private theorem execLdr_no_allocFailed (w : Width) (size : MemWidth) (signed : Bool) (rt : Reg)
    (addr : AddrMode) {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execLdr w size signed rt addr s).trace := by
  dsimp (config := { zetaHave := true }) only [execLdr]
  generalize evalAddrMode s addr = ea
  no_alloc_failed_close hs

private theorem execLdrLit_no_allocFailed (w : Width) (size : MemWidth) (signed : Bool) (rt : Reg)
    (offset : BitVec 64) {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execLdrLit w size signed rt offset s).trace := by
  dsimp (config := { zetaHave := true }) only [execLdrLit]; no_alloc_failed_close hs

private theorem execStr_no_allocFailed (size : MemWidth) (rt : Reg) (addr : AddrMode)
    {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execStr size rt addr s).trace := by
  dsimp (config := { zetaHave := true }) only [execStr]
  generalize evalAddrMode s addr = ea
  no_alloc_failed_close hs

private theorem execLdp_no_allocFailed (w : Width) (signed : Bool) (rt1 rt2 : Reg) (addr : AddrMode)
    {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execLdp w signed rt1 rt2 addr s).trace := by
  unfold execLdp
  rcases evalAddrMode s addr with ⟨ea, wb⟩
  cases wb <;> dsimp (config := { zeta := true, zetaHave := true }) only <;> no_alloc_failed_close hs

private theorem execStp_no_allocFailed (w : Width) (rt1 rt2 : Reg) (addr : AddrMode)
    {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execStp w rt1 rt2 addr s).trace := by
  dsimp (config := { zetaHave := true }) only [execStp]
  generalize evalAddrMode s addr = ea
  no_alloc_failed_close hs

private theorem applySimdResult_no_allocFailed {rd : BitVec 5} {r : Except String (BitVec 128)}
    {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (applySimdResult s rd r).trace := by
  cases r <;> no_alloc_failed_close hs

private theorem applySimdSatResult_no_allocFailed {rd : BitVec 5} {r : Except String (BitVec 128)}
    {satFlags : Option (BitVec 32)} {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (applySimdSatResult s rd r satFlags).trace := by
  cases r <;> cases satFlags <;> no_alloc_failed_close hs

private theorem simdLoadRegs_trace (sz : SimdMemSize) (m : Memory) :
    ∀ (k : Nat) (vt : BitVec 5) (ea : BitVec 64) (s : State),
      (simdLoadRegs sz m k vt ea s).trace = s.trace
  | 0, _, _, _ => rfl
  | k + 1, vt, ea, s => by
    simp only [simdLoadRegs]
    rw [simdLoadRegs_trace sz m k, tr_writeVReg128]

private theorem simdLoadRegs_no_allocFailed {sz : SimdMemSize} {m : Memory} {k : Nat}
    {vt : BitVec 5} {ea : BitVec 64} {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (simdLoadRegs sz m k vt ea s).trace := by
  rw [simdLoadRegs_trace]; exact hs

private theorem execReadCommon_no_allocFailed (isPread : Bool) {s : State}
    (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execReadCommon s isPread).trace := by
  dsimp (config := { zetaHave := true }) only [execReadCommon]; no_alloc_failed_close hs

private theorem execRead_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execRead s).trace :=
  execReadCommon_no_allocFailed false hs

private theorem execPread64_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execPread64 s).trace :=
  execReadCommon_no_allocFailed true hs

private theorem execWrite_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execWrite s).trace := by
  dsimp (config := { zetaHave := true }) only [execWrite]
  cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0)) <;>
    (dsimp only
     repeat' apply ite_no_allocFailed
     repeat' apply ite_no_allocFailed
     all_goals no_alloc_failed_close hs)

private theorem execExit_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execExit s).trace := by
  dsimp (config := { zetaHave := true }) only [execExit]; no_alloc_failed_close hs

private theorem execFcntl_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execFcntl s).trace := by
  dsimp (config := { zetaHave := true }) only [execFcntl]; no_alloc_failed_close hs

private theorem execIoctl_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execIoctl s).trace := by
  dsimp (config := { zetaHave := true }) only [execIoctl]; no_alloc_failed_close hs

private theorem applyOpenVerdict_no_allocFailed {s : State} (v : OpenVerdict)
    (hs : allocFailedEvent ∉ s.trace) : allocFailedEvent ∉ (applyOpenVerdict s v).trace := by
  cases v with
  | opened _ _ chg => cases chg <;> no_alloc_failed_close hs
  | errno _ => no_alloc_failed_close hs
  | trap _ => no_alloc_failed_close hs

private theorem execOpenat_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execOpenat s).trace := by
  unfold execOpenat; dsimp only
  split
  · exact applyOpenVerdict_no_allocFailed _ hs
  · split <;> first | exact applyOpenVerdict_no_allocFailed _ hs | no_alloc_failed_close hs

private theorem execClose_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execClose s).trace := by
  dsimp (config := { zetaHave := true }) only [execClose]; no_alloc_failed_close hs

private theorem execLseek_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execLseek s).trace := by
  dsimp (config := { zetaHave := true }) only [execLseek]; no_alloc_failed_close hs

private theorem execFstat_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execFstat s).trace := by
  dsimp (config := { zetaHave := true }) only [execFstat]; no_alloc_failed_close hs

private theorem execPpoll_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execPpoll s).trace := by
  unfold execPpoll; dsimp only
  refine ite_no_allocFailed (setStatus_no_allocFailed hs) ?_
  refine ite_no_allocFailed (advancePC_no_allocFailed (writeReg64_no_allocFailed hs)) ?_
  refine ite_no_allocFailed (setStatus_no_allocFailed hs) ?_
  refine ite_no_allocFailed (advancePC_no_allocFailed (writeReg64_no_allocFailed hs)) ?_
  refine ite_no_allocFailed (setStatus_no_allocFailed hs) ?_
  refine ite_no_allocFailed (advancePC_no_allocFailed (writeReg64_no_allocFailed hs)) ?_
  refine ite_no_allocFailed (setStatus_no_allocFailed hs) ?_
  refine ite_no_allocFailed (advancePC_no_allocFailed (writeReg64_no_allocFailed hs)) ?_
  refine ite_no_allocFailed (advancePC_no_allocFailed (writeReg64_no_allocFailed hs)) ?_
  refine ite_no_allocFailed (advancePC_no_allocFailed (writeReg64_no_allocFailed hs)) ?_
  refine ite_no_allocFailed (setStatus_no_allocFailed hs) ?_
  cases evalPpollEntries s.fs s.mem (s.readReg64 Reg.x0) (s.readReg32 Reg.x1).toNat 0 0 with
  | none => exact setStatus_no_allocFailed hs
  | some mc =>
    rcases mc with ⟨m', count⟩; dsimp only
    exact ite_no_allocFailed (advancePC_no_allocFailed (writeReg64_no_allocFailed hs))
      (advancePC_no_allocFailed (writeReg64_no_allocFailed (setMem_no_allocFailed hs)))

private theorem execBrk_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execBrk s).trace := by
  dsimp (config := { zetaHave := true }) only [execBrk]; no_alloc_failed_close hs

private theorem execMunmap_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execMunmap s).trace := by
  dsimp (config := { zetaHave := true }) only [execMunmap]; no_alloc_failed_close hs

private theorem execMremap_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execMremap s).trace := by
  dsimp (config := { zetaHave := true }) only [execMremap]; no_alloc_failed_close hs

private theorem execMmap_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execMmap s).trace := by
  dsimp (config := { zetaHave := true }) only [execMmap]; no_alloc_failed_close hs

private theorem execMprotect_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execMprotect s).trace := by
  dsimp (config := { zetaHave := true }) only [execMprotect]; no_alloc_failed_close hs

private theorem execMadvise_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execMadvise s).trace := by
  dsimp (config := { zetaHave := true }) only [execMadvise]; no_alloc_failed_close hs

private theorem execTkill_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execTkill s).trace := by
  dsimp (config := { zetaHave := true }) only [execTkill]; no_alloc_failed_close hs

private theorem execTgkill_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execTgkill s).trace := by
  dsimp (config := { zetaHave := true }) only [execTgkill]; no_alloc_failed_close hs

private theorem execSigaltstack_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execSigaltstack s).trace := by
  dsimp (config := { zetaHave := true }) only [execSigaltstack]; no_alloc_failed_close hs

private theorem execRtSigaction_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execRtSigaction s).trace := by
  dsimp (config := { zetaHave := true }) only [execRtSigaction]; no_alloc_failed_close hs

private theorem execRtSigprocmask_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execRtSigprocmask s).trace := by
  dsimp (config := { zetaHave := true }) only [execRtSigprocmask]; no_alloc_failed_close hs

private theorem execClockGettime_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execClockGettime s).trace := by
  dsimp (config := { zetaHave := true }) only [execClockGettime]; no_alloc_failed_close hs

private theorem execGetrandom_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execGetrandom s).trace := by
  dsimp (config := { zetaHave := true }) only [execGetrandom]; no_alloc_failed_close hs

private theorem execSetTidAddress_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execSetTidAddress s).trace := by
  dsimp (config := { zetaHave := true }) only [execSetTidAddress]; no_alloc_failed_close hs

private theorem execSchedGetaffinity_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execSchedGetaffinity s).trace := by
  dsimp (config := { zetaHave := true }) only [execSchedGetaffinity]; no_alloc_failed_close hs

private theorem execGetpid_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execGetpid s).trace := by
  dsimp (config := { zetaHave := true }) only [execGetpid]; no_alloc_failed_close hs

private theorem standardEntry_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    ∀ p ∈ Syscall.standardTable, allocFailedEvent ∉ (p.2 s).trace := by
  simp only [Syscall.standardTable, Syscall.stdioTable, Syscall.fileIoOnlyTable,
    Syscall.pollTable, Syscall.allocTable, Syscall.signalsTable, Syscall.timeTable,
    Syscall.randomTable, Syscall.miscTable,
    List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact execRead_no_allocFailed hs
  · exact execWrite_no_allocFailed hs
  · exact LibsignalBinary.Proofs.SpecLemmas.SyscallReadWritev.execReadv_trace_not_mem
      (fun _ h => execRead_no_allocFailed h) hs
  · exact LibsignalBinary.Proofs.SpecLemmas.SyscallReadWritev.execWritev_trace_not_mem
      (fun _ h => execWrite_no_allocFailed h) hs
  · exact execExit_no_allocFailed hs
  · exact execExit_no_allocFailed hs
  · exact execFcntl_no_allocFailed hs
  · exact execIoctl_no_allocFailed hs
  · exact execOpenat_no_allocFailed hs
  · exact execClose_no_allocFailed hs
  · exact execLseek_no_allocFailed hs
  · exact execPread64_no_allocFailed hs
  · exact execFstat_no_allocFailed hs
  · exact execPpoll_no_allocFailed hs
  · exact execBrk_no_allocFailed hs
  · exact execMunmap_no_allocFailed hs
  · exact execMremap_no_allocFailed hs
  · exact execMmap_no_allocFailed hs
  · exact execMprotect_no_allocFailed hs
  · exact execMadvise_no_allocFailed hs
  · exact execTkill_no_allocFailed hs
  · exact execTgkill_no_allocFailed hs
  · exact execSigaltstack_no_allocFailed hs
  · exact execRtSigaction_no_allocFailed hs
  · exact execRtSigprocmask_no_allocFailed hs
  · exact execClockGettime_no_allocFailed hs
  · exact execGetrandom_no_allocFailed hs
  · exact execSetTidAddress_no_allocFailed hs
  · exact execSchedGetaffinity_no_allocFailed hs
  · exact execGetpid_no_allocFailed hs
  · exact execGetpid_no_allocFailed hs

private theorem syscallStandard_no_allocFailed {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (Syscall.standard s).trace := by
  unfold Syscall.standard Syscall.dispatch
  split
  · rename_i nr fn hfind
    exact standardEntry_no_allocFailed hs (nr, fn) (List.mem_of_find?_eq_some hfind)
  · exact hs

private theorem evalSvc_trace (svc : State → State) (s : State) :
    (evalSvc svc s).trace = (svc s).trace := rfl

macro "peel_trace_step" h:ident hsvc_s:ident : tactic => `(tactic|
  repeat' (first
    | with_reducible exact $h
    | with_reducible exact $hsvc_s
    | with_reducible apply ite_no_allocFailed
    | with_reducible apply advancePC_no_allocFailed
    | with_reducible apply setPC_no_allocFailed
    | with_reducible apply setPState_no_allocFailed
    | with_reducible apply setMem_no_allocFailed
    | with_reducible apply setFpsr_no_allocFailed
    | with_reducible apply orFpsr_no_allocFailed
    | with_reducible apply stepExclOracle_no_allocFailed
    | with_reducible apply writeReg64_no_allocFailed
    | with_reducible apply writeReg32_no_allocFailed
    | with_reducible apply writeReg_no_allocFailed
    | with_reducible apply writeVReg128_no_allocFailed
    | with_reducible apply writeVReg64_no_allocFailed
    | with_reducible apply writeVReg32_no_allocFailed
    | with_reducible apply simdLoadRegs_no_allocFailed
    | with_reducible apply applySimdResult_no_allocFailed
    | with_reducible apply applySimdSatResult_no_allocFailed
    | with_reducible apply setStatus_no_allocFailed))

private theorem exec_ldrSimd_no_allocFailed {svc : State → State}
    {sz : SimdMemSize} {vt : VReg} {addr : AddrMode} {s : State}
    (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execInstWithSvc svc (.ldrSimd sz vt addr) s).trace := by
  apply ite_no_allocFailed
  · exact setStatus_no_allocFailed hs
  · cases addr <;>
      (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
       peel_trace_step hs hs)

private theorem exec_strSimd_no_allocFailed {svc : State → State}
    {sz : SimdMemSize} {vt : VReg} {addr : AddrMode} {s : State}
    (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execInstWithSvc svc (.strSimd sz vt addr) s).trace := by
  apply ite_no_allocFailed
  · exact setStatus_no_allocFailed hs
  · cases addr <;>
      (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
       peel_trace_step hs hs)

private theorem exec_ldpSimd_no_allocFailed {svc : State → State}
    {sz : SimdMemSize} {vt1 vt2 : VReg} {addr : AddrMode} {s : State}
    (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execInstWithSvc svc (.ldpSimd sz vt1 vt2 addr) s).trace := by
  apply ite_no_allocFailed
  · exact setStatus_no_allocFailed hs
  · cases addr <;>
      (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
       peel_trace_step hs hs)

private theorem exec_stpSimd_no_allocFailed {svc : State → State}
    {sz : SimdMemSize} {vt1 vt2 : VReg} {addr : AddrMode} {s : State}
    (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execInstWithSvc svc (.stpSimd sz vt1 vt2 addr) s).trace := by
  apply ite_no_allocFailed
  · exact setStatus_no_allocFailed hs
  · cases addr <;>
      (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
       peel_trace_step hs hs)

private theorem exec_st1SinglePost_no_allocFailed {svc : State → State}
    {q : Bool} {rm : VReg} {opcode : BitVec 3} {sBit : Bool} {size : BitVec 2}
    {rn : Reg} {vt : VReg} {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execInstWithSvc svc (.st1SinglePost q rm opcode sBit size rn vt) s).trace := by
  apply ite_no_allocFailed
  · exact hs
  · try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
    peel_trace_step hs hs

private theorem exec_simdLdSt1Multi_no_allocFailed {svc : State → State}
    {isLoad q : Bool} {size : BitVec 2} {nregs : Nat} {rn : Reg} {postIdx : Bool} {rm vt : VReg}
    {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉
      (execInstWithSvc svc (.simdLdSt1Multi isLoad q size nregs rn postIdx rm vt) s).trace := by
  apply ite_no_allocFailed <;>
    (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
     peel_trace_step hs hs)

private theorem exec_simdLd1r_no_allocFailed {svc : State → State}
    {q : Bool} {size : BitVec 2} {rn : Reg} {postIdx : Bool} {rm vt : VReg}
    {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execInstWithSvc svc (.simdLd1r q size rn postIdx rm vt) s).trace := by
  apply ite_no_allocFailed <;>
    (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
     peel_trace_step hs hs)

private theorem exec_fmovGprVec_no_allocFailed {svc : State → State}
    {sf : Bool} {ftype rmode : BitVec 2} {opcode : BitVec 3} {rn rd : VReg}
    {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execInstWithSvc svc (.fmovGprVec sf ftype rmode opcode rn rd) s).trace := by
  apply ite_no_allocFailed <;>
    (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
     peel_trace_step hs hs)

private theorem exec_fpDataProc1_no_allocFailed {svc : State → State}
    {ftype : BitVec 2} {opcode : BitVec 6} {rn rd : VReg}
    {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execInstWithSvc svc (.fpDataProc1 ftype opcode rn rd) s).trace := by
  apply ite_no_allocFailed <;>
    (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
     peel_trace_step hs hs)

private theorem exec_fpFixedConv_no_allocFailed {svc : State → State}
    {sf : Bool} {ftype rmode : BitVec 2} {opcode : BitVec 3} {scale : BitVec 6} {rn rd : VReg}
    {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉
      (execInstWithSvc svc (.fpFixedConv sf ftype rmode opcode scale rn rd) s).trace := by
  apply ite_no_allocFailed <;>
    (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
     peel_trace_step hs hs)

private theorem exec_simdImmShift_no_allocFailed {svc : State → State}
    {q op : Bool} {immh : BitVec 4} {immb : BitVec 3} {opc : BitVec 5} {rn rd : VReg}
    {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉
      (execInstWithSvc svc (.simdImmShift q op immh immb opc rn rd) s).trace := by
  apply ite_no_allocFailed <;>
    (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
     peel_trace_step hs hs)

private theorem exec_simdInsDup_no_allocFailed {svc : State → State}
    {q op : Bool} {imm5 : BitVec 5} {imm4 : BitVec 4} {rn rd : VReg}
    {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execInstWithSvc svc (.simdInsDup q op imm5 imm4 rn rd) s).trace := by
  apply ite_no_allocFailed <;>
    (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
     peel_trace_step hs hs)

private theorem exec_simdThreeSame_no_allocFailed {svc : State → State}
    {q u : Bool} {size : BitVec 2} {rm : VReg} {opcode : BitVec 5} {rn rd : VReg}
    {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉
      (execInstWithSvc svc (.simdThreeSame q u size rm opcode rn rd) s).trace := by
  apply ite_no_allocFailed
  · try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
    split <;> peel_trace_step hs hs
  · try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
    peel_trace_step hs hs

private theorem exec_simdTwoRegMisc_no_allocFailed {svc : State → State}
    {q u : Bool} {size : BitVec 2} {opcode : BitVec 5} {rn rd : VReg}
    {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execInstWithSvc svc (.simdTwoRegMisc q u size opcode rn rd) s).trace := by
  apply ite_no_allocFailed <;>
    (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
     peel_trace_step hs hs)

private theorem exec_simdAcrossLanes_no_allocFailed {svc : State → State}
    {q u : Bool} {size : BitVec 2} {opcode : BitVec 5} {rn rd : VReg}
    {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execInstWithSvc svc (.simdAcrossLanes q u size opcode rn rd) s).trace := by
  apply ite_no_allocFailed <;>
    (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
     peel_trace_step hs hs)

private theorem exec_simdPermute_no_allocFailed {svc : State → State}
    {q : Bool} {size : BitVec 2} {rm : VReg} {opcode : BitVec 3} {rn rd : VReg}
    {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execInstWithSvc svc (.simdPermute q size rm opcode rn rd) s).trace := by
  apply ite_no_allocFailed <;>
    (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
     peel_trace_step hs hs)

private theorem exec_simdTbl_no_allocFailed {svc : State → State}
    {q : Bool} {rm : VReg} {len : BitVec 2} {isTbx : Bool} {rn rd : VReg}
    {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execInstWithSvc svc (.simdTbl q rm len isTbx rn rd) s).trace :=
  advancePC_no_allocFailed (writeVReg128_no_allocFailed hs)

/-- Executing any single decoded instruction `inst` under an `allocFailedEvent`-avoiding `svc`
handler preserves `allocFailedEvent ∉ s.trace`. -/
theorem execInstWithSvc_preserves_no_allocFailed {svc : State → State}
    (hsvc : ∀ {s : State}, allocFailedEvent ∉ s.trace → allocFailedEvent ∉ (svc s).trace)
    (inst : Instr) {s : State} (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (execInstWithSvc svc inst s).trace := by
  have hsvc_s : allocFailedEvent ∉ (svc s).trace := hsvc hs
  cases inst with
  | ldrSimd => exact exec_ldrSimd_no_allocFailed hs
  | strSimd => exact exec_strSimd_no_allocFailed hs
  | ldpSimd => exact exec_ldpSimd_no_allocFailed hs
  | stpSimd => exact exec_stpSimd_no_allocFailed hs
  | st1SinglePost => exact exec_st1SinglePost_no_allocFailed hs
  | simdLdSt1Multi => exact exec_simdLdSt1Multi_no_allocFailed hs
  | simdLd1r => exact exec_simdLd1r_no_allocFailed hs
  | fmovGprVec => exact exec_fmovGprVec_no_allocFailed hs
  | fpDataProc1 => exact exec_fpDataProc1_no_allocFailed hs
  | fpFixedConv => exact exec_fpFixedConv_no_allocFailed hs
  | simdImmShift => exact exec_simdImmShift_no_allocFailed hs
  | simdInsDup => exact exec_simdInsDup_no_allocFailed hs
  | simdThreeSame => exact exec_simdThreeSame_no_allocFailed hs
  | simdTwoRegMisc => exact exec_simdTwoRegMisc_no_allocFailed hs
  | simdAcrossLanes => exact exec_simdAcrossLanes_no_allocFailed hs
  | simdPermute => exact exec_simdPermute_no_allocFailed hs
  | simdTbl => exact exec_simdTbl_no_allocFailed hs
  | addSubImm => exact execAddSubImm_no_allocFailed _ _ _ _ _ _ hs
  | addSubShift => exact execAddSubShift_no_allocFailed _ _ _ _ _ _ _ hs
  | addSubExt => exact execAddSubExt_no_allocFailed _ _ _ _ _ _ _ hs
  | addSubCarry => exact execAddSubCarry_no_allocFailed _ _ _ _ _ hs
  | logicalImm => exact execLogicalImm_no_allocFailed _ _ _ _ _ hs
  | logicalShift => exact execLogicalShift_no_allocFailed _ _ _ _ _ _ _ hs
  | moveWide => exact execMoveWide_no_allocFailed _ _ _ _ _ hs
  | bitfield => exact execBitfield_no_allocFailed _ _ _ _ _ _ hs
  | condSelect => exact execCondSelect_no_allocFailed _ _ _ _ _ _ hs
  | condCompareReg => exact execCondCompare_no_allocFailed _ _ _ _ _ _ _ _ hs
  | condCompareImm => exact execCondCompare_no_allocFailed _ _ _ _ _ _ _ _ hs
  | dataProc1 => exact execDataProc1_no_allocFailed _ _ _ _ hs
  | dataProc2 => exact execDataProc2_no_allocFailed _ _ _ _ _ hs
  | dataProc3 => exact execDataProc3_no_allocFailed _ _ _ _ _ _ hs
  | ldr => exact execLdr_no_allocFailed _ _ _ _ _ hs
  | ldrLit => exact execLdrLit_no_allocFailed _ _ _ _ _ hs
  | str => exact execStr_no_allocFailed _ _ _ hs
  | ldp => exact execLdp_no_allocFailed _ _ _ _ _ hs
  | stp => exact execStp_no_allocFailed _ _ _ _ hs
  | ldnp => exact execLdp_no_allocFailed _ _ _ _ _ hs
  | stnp => exact execStp_no_allocFailed _ _ _ _ hs
  | cryptoSha2Reg => exact applySimdResult_no_allocFailed hs
  | cryptoSha3Reg => exact applySimdResult_no_allocFailed hs
  | udf => exact setStatus_no_allocFailed hs
  | _ =>
    first
      | apply ite_no_allocFailed
      | apply advancePC_no_allocFailed
    all_goals
      try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
      peel_trace_step hs hsvc_s

/-- `prog.evalInst inst s` under `Syscall.standard` never introduces `allocFailedEvent`. -/
theorem evalInst_standard_preserves_no_allocFailed {prog : Program}
    (hsvc : prog.svc = Syscall.standard) (inst : Instr) {s : State}
    (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ (prog.evalInst inst s).trace := by
  unfold Program.evalInst
  refine execInstWithSvc_preserves_no_allocFailed (fun {s'} hs' => ?_) inst hs
  rw [evalSvc_trace, hsvc]
  exact syscallStandard_no_allocFailed hs'

/-! ## `Step`, `Steps`, `StepsUntil`, and `codeROSubroutineHook` Preservation -/

private theorem findSome?_table_preserves
    (tbl : List (String × Nat))
    {ext : String → Option (State → State)}
    (hext : ExternPreservesNoAllocFailed ext)
    (off : Nat) {f : State → State}
    (h : (tbl.findSome? fun (n, o) => if o == off then ext n else none) = some f) :
    PreservesNoAllocFailed f := by
  induction tbl with
  | nil => simp at h
  | cons hd tl ih =>
    rcases hd with ⟨n, o⟩
    simp only [List.findSome?_cons] at h
    cases hoo : (o == off) with
    | false =>
      simp only [hoo, Bool.false_eq_true, ↓reduceIte] at h
      exact ih h
    | true =>
      simp only [hoo, ↓reduceIte] at h
      cases hfn : ext n with
      | none =>
        rw [hfn] at h
        exact ih h
      | some g =>
        rw [hfn] at h
        injection h with hgf
        subst hgf
        exact hext n g hfn

/-- If both `prog.externs` and `prog.overrides` satisfy `ExternPreservesNoAllocFailed`, then any
hook `f` returned by `prog.externAt? pc` satisfies `PreservesNoAllocFailed f`. -/
theorem externAt?_preserves_no_allocFailed {prog : Program}
    (hext : ExternPreservesNoAllocFailed prog.externs)
    (hovr : ExternPreservesNoAllocFailed prog.overrides)
    {pc : BitVec 64} {f : State → State}
    (h : prog.externAt? pc = some f) :
    PreservesNoAllocFailed f := by
  unfold Program.externAt? Program.hookAtOff? at h
  cases hs :
      (prog.stubs.findSome? fun (n, o) => if o == (pc - prog.base).toNat then prog.externs n else none) with
  | some g =>
    rw [hs] at h
    injection h with hgf
    subst hgf
    exact findSome?_table_preserves prog.stubs hext _ hs
  | none =>
    rw [hs] at h
    exact findSome?_table_preserves prog.symbols hovr _ h

/-- Single-step `allocFailedEvent ∉ s.trace` preservation for any `Program` with
`svc = Syscall.standard` and `allocFailedEvent`-preserving `externs` and `overrides`. -/
theorem step_preserves_no_allocFailed {prog : Program}
    (hsvc : prog.svc = Syscall.standard)
    (hext : ExternPreservesNoAllocFailed prog.externs)
    (hovr : ExternPreservesNoAllocFailed prog.overrides)
    {s s' : State}
    (hstep : Step prog s s')
    (hs : allocFailedEvent ∉ s.trace) :
    allocFailedEvent ∉ s'.trace := by
  cases hstep with
  | exec _ _ =>
    exact evalInst_standard_preserves_no_allocFailed hsvc _ hs
  | halt_unmapped _ _ _ =>
    exact hs
  | extern _ h_ext _ _ =>
    exact externAt?_preserves_no_allocFailed hext hovr h_ext _ hs
  | extern_fault _ _ _ =>
    exact hs

/-- Multi-step `allocFailedEvent ∉ s.trace` preservation along `Steps prog`. -/
theorem steps_preserves_no_allocFailed {prog : Program}
    (hsvc : prog.svc = Syscall.standard)
    (hext : ExternPreservesNoAllocFailed prog.externs)
    (hovr : ExternPreservesNoAllocFailed prog.overrides)
    {s0 sf : State}
    (hsteps : Steps prog s0 sf)
    (hs0 : allocFailedEvent ∉ s0.trace) :
    allocFailedEvent ∉ sf.trace := by
  induction hsteps with
  | refl _ => exact hs0
  | step h1 _ ih => exact ih (step_preserves_no_allocFailed hsvc hext hovr h1 hs0)

theorem stepsUntil_toSteps {prog : Program} {stop : State → Prop} {s0 sf : State}
    (h : StepsUntil prog stop s0 sf) :
    Steps prog s0 sf := by
  induction h with
  | refl s => exact Steps.refl s
  | step _ hstep _ ih => exact Steps.step hstep ih

private theorem multiCodeROHookEntry_trace (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (entryPc : BitVec 64) (s0 : State) :
    (multiCodeROHookEntry lib mpl i entryPc s0).trace = s0.trace := by
  unfold multiCodeROHookEntry
  rw [tr_setMem, tr_setPC, tr_writeReg64]

private theorem multiCodeROHookExit_trace (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (s0 sf' : State) :
    (multiCodeROHookExit lib mpl i s0 sf').trace = sf'.trace := by
  unfold multiCodeROHookExit
  dsimp only
  rw [tr_setMem, tr_writeReg64]
  split <;> rfl

/-- `lib.codeROSubroutineHook mpl fnName` (with `externs = none`, `overrides = none`,
`svc = Syscall.standard`) preserves `allocFailedEvent ∉ s.trace`. -/
theorem preservesNoAllocFailed_codeROSubroutineHook
    (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement) (fnName : String) :
    PreservesNoAllocFailed
      (lib.codeROSubroutineHook mpl fnName (fun _ => none) (fun _ => none) Syscall.standard) := by
  intro s0 hs0
  unfold Obj.MultiPlacedLib.codeROSubroutineHook
  cases hsym : Obj.lookupBlockSym fnName lib.blocks with
  | none => exact hs0
  | some p =>
    rcases p with ⟨i, off⟩
    dsimp only
    split
    · next hex =>
      rw [multiCodeROHookExit_trace]
      have hs0' :
          allocFailedEvent ∉
            (multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0).trace := by
        rw [multiCodeROHookEntry_trace]
        exact hs0
      exact steps_preserves_no_allocFailed rfl
        externPreservesNoAllocFailed_none externPreservesNoAllocFailed_none
        (stepsUntil_toSteps (Classical.choose_spec hex).1) hs0'
    · exact hs0

/-! ## `stepRustAlloc1`, `stepRustDealloc1`, and `mallocng` Crypto Hook Preservation -/

private theorem retHook_trace (f : State → State) (s : State) :
    (retHook f s).trace = (f s).trace := rfl

private theorem returnToLinkRegister_trace (s : State) :
    (returnToLinkRegister s).trace = s.trace := rfl

private theorem restoreCallerRegs_trace (sCaller sCallee : State) :
    (restoreCallerRegs sCaller sCallee).trace = sCallee.trace := rfl

private theorem rustPanicked_trace (s : State) :
    (Rust.panicked s).trace = s.trace := rfl

private theorem unitResult_trace (ok : Bool) (s : State) :
    (unitResult ok s).trace = s.trace := by
  unfold unitResult
  rw [retHook_trace, tr_writeReg64]

/-- `stepRustAlloc1 mpl zeroed frameBytes size k` preserves `allocFailedEvent ∉ s.trace` whenever
its continuation `k` preserves `allocFailedEvent ∉ s1.trace` for every `p`. -/
theorem preservesNoAllocFailed_stepRustAlloc1
    (mpl : Obj.MultiPlacement) (zeroed : Bool) (frameBytes size : Nat)
    {k : State → BitVec 64 → State}
    (hk : ∀ s1 p, allocFailedEvent ∉ s1.trace → allocFailedEvent ∉ (k s1 p).trace) :
    PreservesNoAllocFailed (stepRustAlloc1 mpl zeroed frameBytes size k) := by
  intro s hs
  cases zeroed <;> simp only [stepRustAlloc1, Bool.false_eq_true, ↓reduceIte]
  · have hsCall :
        allocFailedEvent ∉
          ((s.writeReg64 .sp (s.sp - BitVec.ofNat 64 frameBytes)).writeReg64 .x0
            (BitVec.ofNat 64 size)).trace := by
      rw [tr_writeReg64, tr_writeReg64]
      exact hs
    have hs1 :=
      preservesNoAllocFailed_codeROSubroutineHook mallocngLib mpl "malloc" _ hsCall
    split
    · exact hs1
    · split
      · rw [rustPanicked_trace, restoreCallerRegs_trace]
        exact hs1
      · refine hk _ _ ?_
        rw [restoreCallerRegs_trace]
        exact hs1
  · have hsCall :
        allocFailedEvent ∉
          (((s.writeReg64 .sp (s.sp - BitVec.ofNat 64 frameBytes)).writeReg64 .x0
            (BitVec.ofNat 64 size)).writeReg64 .x1 1#64).trace := by
      rw [tr_writeReg64, tr_writeReg64, tr_writeReg64]
      exact hs
    have hs1 :=
      preservesNoAllocFailed_codeROSubroutineHook mallocngLib mpl "calloc" _ hsCall
    split
    · exact hs1
    · split
      · rw [rustPanicked_trace, restoreCallerRegs_trace]
        exact hs1
      · refine hk _ _ ?_
        rw [restoreCallerRegs_trace]
        exact hs1

/-- `stepRustDealloc1 mpl frameBytes ptr k` preserves `allocFailedEvent ∉ s.trace` whenever `k`
preserves `allocFailedEvent ∉ s1.trace`. -/
theorem preservesNoAllocFailed_stepRustDealloc1
    (mpl : Obj.MultiPlacement) (frameBytes : Nat) (ptr : BitVec 64)
    {k : State → State}
    (hk : PreservesNoAllocFailed k) :
    PreservesNoAllocFailed (stepRustDealloc1 mpl frameBytes ptr k) := by
  intro s hs
  unfold stepRustDealloc1
  dsimp only
  have hsCall :
      allocFailedEvent ∉
        ((s.writeReg64 .sp (s.sp - BitVec.ofNat 64 frameBytes)).writeReg64 .x0 ptr).trace := by
    rw [tr_writeReg64, tr_writeReg64]
    exact hs
  have hs1 :=
    preservesNoAllocFailed_codeROSubroutineHook mallocngLib mpl "free" _ hsCall
  split
  · exact hs1
  · refine hk _ ?_
    rw [restoreCallerRegs_trace]
    exact hs1

theorem preservesNoAllocFailed_aesEncHookMallocng
    (mpl : Obj.MultiPlacement) (E : AesKey → Block → Block) :
    PreservesNoAllocFailed (aesEncHookMallocng mpl E) := by
  intro s0 hs0
  unfold aesEncHookMallocng
  split
  · exact hs0
  · dsimp only
    split
    · exact hs0
    · refine preservesNoAllocFailed_stepRustAlloc1 mpl true _ _ (fun s1 _ hs1 => ?_) s0 hs0
      rw [retHook_trace, tr_setMem]
      exact hs1

theorem preservesNoAllocFailed_aesDecHookMallocng
    (mpl : Obj.MultiPlacement) (D : AesKey → Block → Block) :
    PreservesNoAllocFailed (aesDecHookMallocng mpl D) := by
  intro s0 hs0
  unfold aesDecHookMallocng
  split
  · exact hs0
  · dsimp only
    split
    · rw [retHook_trace, tr_setMem]
      exact hs0
    · refine preservesNoAllocFailed_stepRustAlloc1 mpl true _ _ (fun s1 p hs1 => ?_) s0 hs0
      split
      · rw [retHook_trace, tr_setMem]
        exact hs1
      · refine preservesNoAllocFailed_stepRustDealloc1 mpl _ p (fun s2 hs2 => ?_) s1 hs1
        rw [retHook_trace, tr_setMem]
        exact hs2

theorem preservesNoAllocFailed_libcruxHmacHookMallocng
    (mpl : Obj.MultiPlacement)
    (F : ShaState → List (BitVec 8) → ShaState) :
    PreservesNoAllocFailed (libcruxHmacHookMallocng mpl F) := by
  intro s0 hs0
  unfold libcruxHmacHookMallocng
  split
  · exact hs0
  · dsimp only
    split
    · exact hs0
    · refine preservesNoAllocFailed_stepRustAlloc1 mpl true _ 64 (fun s1 pKey hs1 => ?_) s0 hs0
      refine preservesNoAllocFailed_stepRustAlloc1 mpl false _ 64 (fun s2 pIpad hs2 => ?_) s1 hs1
      refine preservesNoAllocFailed_stepRustAlloc1 mpl false _ 64 (fun s3 pOpad hs3 => ?_) s2 hs2
      refine preservesNoAllocFailed_stepRustDealloc1 mpl _ pOpad (fun s4 hs4 => ?_) s3 hs3
      refine preservesNoAllocFailed_stepRustDealloc1 mpl _ pIpad (fun s5 hs5 => ?_) s4 hs4
      refine preservesNoAllocFailed_stepRustDealloc1 mpl _ pKey (fun s6 hs6 => ?_) s5 hs5
      refine preservesNoAllocFailed_stepRustAlloc1 mpl false _ 32 (fun s7 _ hs7 => ?_) s6 hs6
      rw [retHook_trace, tr_setMem]
      exact hs7

private theorem preservesNoAllocFailed_rustPanicked :
    PreservesNoAllocFailed Rust.panicked :=
  fun _ hs => hs

private theorem preservesNoAllocFailed_hookMemset :
    PreservesNoAllocFailed hookMemset := by
  intro s hs
  unfold hookMemset
  rw [retHook_trace]
  dsimp (config := { zetaHave := true }) only
  rw [tr_setMem]
  exact hs

private theorem preservesNoAllocFailed_hookMemcpy :
    PreservesNoAllocFailed hookMemcpy := by
  intro s hs
  unfold hookMemcpy
  rw [retHook_trace]
  dsimp (config := { zetaHave := true }) only
  rw [tr_setMem]
  exact hs

private theorem preservesNoAllocFailed_hookMemmove :
    PreservesNoAllocFailed hookMemmove := by
  unfold hookMemmove
  exact preservesNoAllocFailed_hookMemcpy

private theorem preservesNoAllocFailed_cliBcmpHook
    (bcmp : List (BitVec 8) → List (BitVec 8) → BitVec 64) :
    PreservesNoAllocFailed (cliBcmpHook bcmp) := by
  intro s hs
  unfold cliBcmpHook
  rw [retHook_trace, tr_writeReg64]
  exact hs

private theorem preservesNoAllocFailed_strlenHook :
    PreservesNoAllocFailed strlenHook := by
  intro s hs
  unfold strlenHook
  dsimp only
  split
  · rw [retHook_trace, tr_writeReg64]; exact hs
  · exact hs

private theorem preservesNoAllocFailed_writeFileHook :
    PreservesNoAllocFailed writeFileHook := by
  intro s hs
  unfold writeFileHook
  dsimp only
  split
  · exact hs
  · split
    · rw [unitResult_trace]; exact hs
    · split
      · exact hs
      · split <;> simp only [unitResult_trace, tr_setFs] <;> exact not_mem_append_fileChanged hs

private theorem preservesNoAllocFailed_writeStdoutHook :
    PreservesNoAllocFailed writeStdoutHook := by
  intro s hs
  unfold writeStdoutHook
  dsimp only
  split
  · exact hs
  · rw [unitResult_trace]
    exact not_mem_append_ofBytes hs

private theorem preservesNoAllocFailed_memrchrHook :
    PreservesNoAllocFailed memrchrHook := by
  intro s hs
  unfold memrchrHook
  dsimp only
  split
  · exact hs
  · split
    · rw [retHook_trace, tr_writeReg64, tr_writeReg64]; exact hs
    · rw [retHook_trace, tr_writeReg64]; exact hs

private theorem preservesNoAllocFailed_fromUtf8Hook
    (err : List (BitVec 8) → BitVec 64 × BitVec 16) :
    PreservesNoAllocFailed (fromUtf8Hook err) := by
  intro s hs
  unfold fromUtf8Hook
  dsimp only
  split
  · exact hs
  · split <;> rw [retHook_trace, tr_setMem] <;> exact hs

private theorem preservesNoAllocFailed_fmtWriteHook0 :
    PreservesNoAllocFailed fmtWriteHook0 := by
  intro s hs
  unfold fmtWriteHook0
  rw [retHook_trace, tr_writeReg64]
  exact hs

private theorem preservesNoAllocFailed_formatInnerHook0 :
    PreservesNoAllocFailed formatInnerHook0 :=
  fun _ hs => hs

private theorem preservesNoAllocFailed_durationSinceExactHook :
    PreservesNoAllocFailed durationSinceExactHook := by
  intro s hs
  unfold durationSinceExactHook
  dsimp only
  split
  · exact hs
  · split
    · rw [retHook_trace, tr_setMem]; exact hs
    · exact hs

private theorem preservesNoAllocFailed_timeAddHook :
    PreservesNoAllocFailed timeAddHook := by
  intro s hs
  unfold timeAddHook
  dsimp only
  split <;> split
  · rw [tr_setPC, tr_writeReg64, tr_writeReg64]; exact hs
  · rw [rustPanicked_trace]; exact hs
  · rw [tr_setPC, tr_writeReg64, tr_writeReg64]; exact hs
  · rw [rustPanicked_trace]; exact hs

private theorem preservesNoAllocFailed_blackBoxHook :
    PreservesNoAllocFailed blackBoxHook := by
  intro s hs
  unfold blackBoxHook
  rw [retHook_trace, tr_writeReg64]
  exact hs

private theorem preservesNoAllocFailed_compress256Hook
    (F : ShaState → List (BitVec 8) → ShaState) :
    PreservesNoAllocFailed (compress256Hook F) :=
  fun _ hs => hs

private theorem preservesNoAllocFailed_pubFromSecretHook
    (pubKey : List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 32) :
    PreservesNoAllocFailed (pubFromSecretHook pubKey) :=
  fun _ hs => hs

private theorem preservesNoAllocFailed_diffieHellmanHook
    (X : List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 32) :
    PreservesNoAllocFailed (diffieHellmanHook X) :=
  fun _ hs => hs

private theorem preservesNoAllocFailed_zeroizeSecretHook :
    PreservesNoAllocFailed zeroizeSecretHook :=
  fun _ hs => hs

private theorem preservesNoAllocFailed_compress512Hook (Q : PqxdhPrims) :
    PreservesNoAllocFailed (compress512Hook Q.F512) :=
  fun _ hs => hs

private theorem preservesNoAllocFailed_toEdwardsHook (Q : PqxdhPrims) :
    PreservesNoAllocFailed (toEdwardsHook Q.montToEd) :=
  fun _ hs => hs

private theorem preservesNoAllocFailed_compressHook (Q : PqxdhPrims) :
    PreservesNoAllocFailed (compressHook Q.compress) :=
  fun _ hs => hs

private theorem preservesNoAllocFailed_edNegHook (Q : PqxdhPrims) :
    PreservesNoAllocFailed (edNegHook Q.edNeg) :=
  fun _ hs => hs

private theorem preservesNoAllocFailed_torsionFreeHook (Q : PqxdhPrims) :
    PreservesNoAllocFailed (torsionFreeHook Q.isTorsionFree) := by
  intro s hs
  unfold torsionFreeHook
  rw [returnToLinkRegister_trace, tr_writeReg64]
  exact hs

private theorem preservesNoAllocFailed_dsmbHook (Q : PqxdhPrims) :
    PreservesNoAllocFailed (dsmbHook Q.dsmb) :=
  fun _ hs => hs

private theorem preservesNoAllocFailed_scalarModHook (Q : PqxdhPrims) :
    PreservesNoAllocFailed (scalarModHook Q.scalarMod) :=
  fun _ hs => hs

private theorem preservesNoAllocFailed_scalarWideHook (Q : PqxdhPrims) :
    PreservesNoAllocFailed (scalarWideHook Q.scalarWide) :=
  fun _ hs => hs

private theorem preservesNoAllocFailed_kemEncapsHook (Q : PqxdhPrims) :
    PreservesNoAllocFailed (kemEncapsHook Q.encaps) :=
  fun _ hs => hs

private theorem preservesNoAllocFailed_kemDecapsHook (Q : PqxdhPrims) :
    PreservesNoAllocFailed (kemDecapsHook Q.decaps) :=
  fun _ hs => hs

private theorem preservesNoAllocFailed_mlkemFromSeedHook (Q : PqxdhPrims) :
    PreservesNoAllocFailed (mlkemFromSeedHook Q.K) :=
  fun _ hs => hs

private theorem preservesNoAllocFailed_mlkemPk1Hook :
    PreservesNoAllocFailed mlkemPk1Hook := by
  intro s hs
  unfold mlkemPk1Hook
  rw [retHook_trace, tr_writeReg64]
  exact hs

private theorem preservesNoAllocFailed_mlkemPk2Hook :
    PreservesNoAllocFailed mlkemPk2Hook := by
  intro s hs
  unfold mlkemPk2Hook
  rw [retHook_trace, tr_writeReg64]
  exact hs

private theorem preservesNoAllocFailed_mlkemEncaps1Hook (Q : PqxdhPrims) :
    PreservesNoAllocFailed (mlkemEncaps1Hook Q.K) := by
  intro s hs
  unfold mlkemEncaps1Hook
  rw [retHook_trace]
  dsimp only
  split <;> exact hs

private theorem preservesNoAllocFailed_mlkemEncaps2Hook (Q : PqxdhPrims) :
    PreservesNoAllocFailed (mlkemEncaps2Hook Q.K) :=
  fun _ hs => hs

private theorem preservesNoAllocFailed_mlkemDecapsHook (Q : PqxdhPrims) :
    PreservesNoAllocFailed (mlkemDecapsHook Q.K) :=
  fun _ hs => hs

private theorem preservesNoAllocFailed_mlkemValidatePkHook (Q : PqxdhPrims) :
    PreservesNoAllocFailed (mlkemValidatePkHook Q.K) := by
  intro s hs
  unfold mlkemValidatePkHook
  rw [retHook_trace, tr_writeReg64]
  exact hs

/-! ## `cliHookTablePlaced` and Whole-Process Non-`allocFailedEvent` Theorems -/

/-- Every `(name, f)` entry of a hook table whose hooks preserve `allocFailedEvent ∉ s.trace`
induces `ExternPreservesNoAllocFailed (fun name => tbl.lookup name)`. -/
theorem externPreserves_of_table {tbl : List (String × (State → State))}
    (htbl : ∀ p ∈ tbl, PreservesNoAllocFailed p.2) :
    ExternPreservesNoAllocFailed (fun name => tbl.lookup name) := by
  intro name f hlook
  dsimp only at hlook
  induction tbl with
  | nil => simp at hlook
  | cons hd tl ih =>
    rcases hd with ⟨k, g⟩
    simp only [List.lookup] at hlook
    cases hbeq : (name == k) with
    | true =>
      rw [hbeq] at hlook
      injection hlook with hgf
      subst hgf
      exact htbl (k, g) (List.Mem.head tl)
    | false =>
      rw [hbeq] at hlook
      exact ih (fun p hp => htbl p (List.Mem.tail _ hp)) hlook

theorem preservesNoAllocFailed_abortOnPanic {f : State → State}
    (hf : PreservesNoAllocFailed f) :
    PreservesNoAllocFailed (abortOnPanic f) := by
  intro s hs
  have htr : (abortOnPanic f s).trace = (f s).trace := by
    unfold abortOnPanic
    dsimp only
    split <;> rfl
  rw [htr]
  exact hf s hs

theorem externPreserves_map_abortOnPanic {ext : String → Option (State → State)}
    (hext : ExternPreservesNoAllocFailed ext) :
    ExternPreservesNoAllocFailed (fun name => (ext name).map abortOnPanic) := by
  intro name f hmap
  dsimp only at hmap
  cases he : ext name with
  | none => rw [he] at hmap; cases hmap
  | some g =>
    rw [he] at hmap
    injection hmap with hgf
    subst hgf
    exact preservesNoAllocFailed_abortOnPanic (hext name g he)

private theorem tablePreserves_cliPqxdhPlaced (mmpl : Obj.MultiPlacement)
    (C : Crypto) (Q : PqxdhPrims) :
    ∀ p ∈ cliPqxdhHookTablePlaced mmpl C Q, PreservesNoAllocFailed p.2 := by
  simp only [cliPqxdhHookTablePlaced, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact preservesNoAllocFailed_compress512Hook Q
  · exact preservesNoAllocFailed_toEdwardsHook Q
  · exact preservesNoAllocFailed_compressHook Q
  · exact preservesNoAllocFailed_edNegHook Q
  · exact preservesNoAllocFailed_torsionFreeHook Q
  · exact preservesNoAllocFailed_dsmbHook Q
  · exact preservesNoAllocFailed_scalarModHook Q
  · exact preservesNoAllocFailed_scalarWideHook Q
  · exact preservesNoAllocFailed_kemEncapsHook Q
  · exact preservesNoAllocFailed_kemDecapsHook Q
  · exact preservesNoAllocFailed_mlkemFromSeedHook Q
  · exact preservesNoAllocFailed_mlkemPk1Hook
  · exact preservesNoAllocFailed_mlkemPk2Hook
  · exact preservesNoAllocFailed_mlkemEncaps1Hook Q
  · exact preservesNoAllocFailed_mlkemEncaps2Hook Q
  · exact preservesNoAllocFailed_mlkemDecapsHook Q
  · exact preservesNoAllocFailed_mlkemValidatePkHook Q
  · exact preservesNoAllocFailed_libcruxHmacHookMallocng mmpl C.F

private theorem tablePreserves_cliHookTablePlaced (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    ∀ p ∈ cliHookTablePlaced mmpl W, PreservesNoAllocFailed p.2 := by
  intro p hp
  unfold cliHookTablePlaced at hp
  rw [List.mem_append] at hp
  rcases hp with hpq | hcli
  · exact tablePreserves_cliPqxdhPlaced mmpl W.C W.Q p hpq
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcli
    rcases hcli with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact preservesNoAllocFailed_hookMemmove
    · exact preservesNoAllocFailed_cliBcmpHook W.bcmp
    · exact preservesNoAllocFailed_strlenHook
    · exact preservesNoAllocFailed_writeFileHook
    · exact preservesNoAllocFailed_writeStdoutHook
    · exact preservesNoAllocFailed_memrchrHook
    · exact preservesNoAllocFailed_fromUtf8Hook W.utf8Err
    · exact preservesNoAllocFailed_fmtWriteHook0
    · exact preservesNoAllocFailed_formatInnerHook0
    · exact preservesNoAllocFailed_durationSinceExactHook
    · exact preservesNoAllocFailed_timeAddHook
    · exact preservesNoAllocFailed_blackBoxHook
    · exact preservesNoAllocFailed_compress256Hook W.C.F
    · exact preservesNoAllocFailed_aesEncHookMallocng mmpl W.C.E
    · exact preservesNoAllocFailed_aesDecHookMallocng mmpl W.C.D
    · exact preservesNoAllocFailed_pubFromSecretHook W.C.pubKey
    · exact preservesNoAllocFailed_diffieHellmanHook W.C.X
    · exact preservesNoAllocFailed_zeroizeSecretHook
    · exact preservesNoAllocFailed_zeroizeSecretHook

/-- Every hook in `cliExternsPlaced mmpl W` preserves `allocFailedEvent ∉ s.trace`. -/
theorem externPreservesNoAllocFailed_cliExternsPlaced
    (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    ExternPreservesNoAllocFailed (cliExternsPlaced mmpl W) := by
  intro name f h
  unfold cliExternsPlaced at h
  split at h
  · injection h with hrf
    subst hrf
    exact preservesNoAllocFailed_rustPanicked
  · exact externPreserves_of_table (tablePreserves_cliHookTablePlaced mmpl W) name f h

theorem externPreservesNoAllocFailed_cliExternsPlacedSig
    (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    ExternPreservesNoAllocFailed (cliExternsPlacedSig mmpl W) :=
  externPreserves_map_abortOnPanic (externPreservesNoAllocFailed_cliExternsPlaced mmpl W)

/-- Whole-process trace theorem for `cliProgExtPlacedSigAt mpl (cliExternsPlaced mmpl) idx W`: no
state reachable from `cliTokenPatchPlaced mpl s0` after `elf.loadState (cliProcessInputs i) = .ok s0`
ever contains `allocFailedEvent` in `s.trace`. -/
theorem cliF3_allocNeverFailsPlacedAt
    (mpl mmpl : Obj.MultiPlacement) (idx : Nat) (elf : ElfImage) (W : CliHooks) :
    ∀ i : Inputs, ∀ s0 s : State,
      elf.loadState (cliProcessInputs i) = .ok s0 →
      Steps (cliProgExtPlacedSigAt mpl (cliExternsPlaced mmpl) idx W)
        (cliTokenPatchPlaced mpl s0) s →
      allocFailedEvent ∉ s.trace := by
  intro i s0 s hload hsteps
  have hloadCli : elf.loadState (cliInputs i) = .ok s0 := hload
  have hs0 : allocFailedEvent ∉ (cliTokenPatchPlaced mpl s0).trace := by
    unfold cliTokenPatchPlaced
    rw [tr_setMem, (loadState_fs_trace hloadCli).2]
    simp
  exact steps_preserves_no_allocFailed rfl
    (externPreservesNoAllocFailed_cliExternsPlacedSig mmpl W)
    externPreservesNoAllocFailed_none hsteps hs0

/-- Whole-process trace theorem for `Placed.cliProgPlacedSig mpl mmpl W`: no state reachable from
`cliTokenPatchPlaced mpl s0` after `elf.loadState (cliProcessInputs i) = .ok s0` ever contains
`allocFailedEvent` in `s.trace`. -/
theorem cliF3_allocNeverFailsPlaced
    (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) (W : CliHooks) :
    ∀ i : Inputs, ∀ s0 s : State,
      elf.loadState (cliProcessInputs i) = .ok s0 →
      Steps (cliProgPlacedSig mpl mmpl W) (cliTokenPatchPlaced mpl s0) s →
      allocFailedEvent ∉ s.trace :=
  cliF3_allocNeverFailsPlacedAt mpl mmpl 617 elf W

end LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail
