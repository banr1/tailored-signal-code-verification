/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees

/-!
# Continuation Hop Contracts M1–M6 for `signal-session` `main`

Layout-independent `SepWPp` continuation contracts for the six hops of `main` (`M+k` = entry + `k`):
- **M1** (`M+0 → M+0xc0`): collect `(1..argc).map(strlen)` into `AtM1End` (early exit `2` if `argc = 1`).
- **M2** (`M+0xc0 → M+0x560`): `parse(&args)` into `AtCall` (early exit `2` if `parseArgs = none`).
- **M3** (`M+0x560 → M+0x5d0`): `read_stdin` and `read_file("coins")` into `AtM4` (early exit `2` on `Err`).
- **M4** (`M+0x5d0 → M+0x720`): `coins::install`, `Stores::open`, and `run` into `AtM4End` (early exit `1` on `Err`).
- **M5** (`M+0x720 → M+0xf34`): `Stores::commit` into `AtM6` (`w21 = 1` on write failure).
- **M6** (`M+0xf34 → M+0xb24`): `write_stdout(&output)`, buffer drops, and shared exit (`free_args`, `main_ret`).
-/

@[expose] public section

set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.LibsignalPublicApi.StoreKit

/-! ## Hop States and Shared Exit -/

/-- Alias for `runSpec` (which routes all allocation failures to `onPanic` with `onOom = False`). -/
abbrev runSpecTight := runSpec

theorem subroutine_ok_runSpec_of_tight {P : Program} {e : BitVec 64}
    {A : RustAlloc} {img : Obj.Image} {uuidParse : UuidParser}
    {Run : Inputs → RunAnswer → Prop} {wrOk : List (BitVec 8) → Prop} {resStack : Nat}
    (h : subroutine_ok P e ((runSpecTight A img uuidParse Run wrOk resStack).inImage img)) :
    subroutine_ok P e ((runSpec A img uuidParse Run wrOk resStack).inImage img) :=
  h

/-- Unreachable `OutOfMemory` continuation (`⌜False⌝`) for `main` hops under panic-on-OOM hooks. -/
def mainOom (_s0 : State) : State → SepProp := fun _ => ⌜False⌝

/-- Transitional `OutOfMemory` continuation (`⌜allocFailedIn s0 sf⌝ ∗ anyHeap`). -/
def mainOomLegacy (s0 : State) : State → SepProp :=
  fun sf => ⌜allocFailedIn s0 sf⌝ ∗ anyHeap

theorem sepWPp_of_mainOom {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ProofLib.SepWPp prog ret s P Q Qp (mainOom s0)) :
    ProofLib.SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  obtain ⟨sf, hsteps, hout⟩ := h R hm hL
  rcases hout with hq | hpan | ⟨_, hmo⟩
  · exact ⟨sf, hsteps, Or.inl hq⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact (ProofLib.not_satisfies_false_sepConj hmo).elim

/-- Frame invariant inside `main` (`sp = fp - 0x480 = s0.sp - 0x4e0`, `ImgCallInv`, `d8..d15`
preserved, and 16-byte stack alignment). -/
structure InMain (img : Obj.Image) (ext : String → Option (State → State)) (s0 s : State) (k : Nat) :
    Prop where
  pc : s.pc = mPc img ext k
  run : s.status = .Running
  sp : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize
  fp : s.readReg64 .fp = s0.sp - 0x60#64
  inv : ImgCallInv img s
  vregs : calleeSavedVRegs s = calleeSavedVRegs s0
  spAligned : s0.spAligned = true

/-- Shared return block `M+0xb24` (`mov w0, w23`; restore; `ret`) with exit code in `w23`. -/
structure AtRet (img : Obj.Image) (ext : String → Option (State → State)) (s0 s : State)
    (code : Nat) : Prop where
  base : InMain img ext s0 s 0xb24
  w23 : (s.readReg64 (.gpr 23#5)).setWidth 32 = BitVec.ofNat 32 code

/-- Separation-logic state at `M+0xb24`: saved callee registers, 0x480-byte local frame, caller stack,
allocator pool, and `anyHeap`. -/
def retMem (A : RustAlloc) (s0 : State) (stk : Nat) : SepProp :=
  mainSaved s0 ∗ memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
    stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ A.pool ∗ anyHeap

/-- Early-return continuation from `M+0xb24` carrying exit code `code` and history predicate `G`. -/
def ExitK (img : Obj.Image) (ext : String → Option (State → State)) (A : RustAlloc) (s0 : State)
    (stk : Nat) (G : Nat → State → Prop) (Q Qp : State → SepProp → Prop) : Prop :=
  ∀ (s : State) (code : Nat), AtRet img ext s0 s code → G code s →
    ProofLib.SepWPp (mProg img ext) (s0.readReg64 .lr) s (retMem A s0 stk) Q Qp (mainOom s0)

/-! ## M1: `args = (1..argc).map(strlen).collect()` (`M+0 → M+0xc0`) -/

/-- End of M1 (`M+0xc0`, `n = argc - 1 ≥ 1`): `x19 = buf`, `x24 = cap = n`, `x23 = x25 = n`,
`x22 = buf + 16 * n`. -/
structure AtM1End (img : Obj.Image) (ext : String → Option (State → State)) (s0 s : State)
    (n : Nat) (buf : BitVec 64) : Prop where
  base : InMain img ext s0 s 0xc0
  x19 : s.readReg64 (.gpr 19#5) = buf
  x22 : s.readReg64 (.gpr 22#5) = buf + BitVec.ofNat 64 (16 * n)
  x23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n
  x24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n
  x25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 n
  trace : s.trace = s0.trace
  fs : s.fs = s0.fs

/-- Entry state of `main` at `M+0` (`argc` in `w0`, `argv` in `x1`, 16-byte aligned `sp`). -/
structure AtEntry (img : Obj.Image) (ext : String → Option (State → State)) (i : Inputs)
    (s0 : State) : Prop where
  pc : s0.pc = mPc img ext 0
  run : s0.status = .Running
  inv : ImgCallInv img s0
  argc : (s0.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1)
  spAligned : s0.spAligned = true

/-! ## M2: `parse(&args)` (`M+0xc0 → M+0x560`) -/

/-- State at `M+0x560` (after freeing `parse`'s `Vec<&str>`): `Call` words in `x25`, `x22`, `x26`,
`[fsp+0x48]`, `[fsp+0x50]`, `x28 ||| zext x21`, and `[fsp+0x40]`; `args` in `x19`/`x24`. -/
structure AtCall (img : Obj.Image) (ext : String → Option (State → State)) (s0 s : State)
    (w : CallW) (n : Nat) (buf : BitVec 64) : Prop where
  base : InMain img ext s0 s 0x560
  x19 : s.readReg64 (.gpr 19#5) = buf
  x24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n
  w0 : s.readReg64 (.gpr 25#5) = w.w0
  w1 : s.readReg64 (.gpr 22#5) = w.w1
  w2 : s.readReg64 (.gpr 26#5) = w.w2
  w5 : (s.readReg64 (.gpr 28#5) ||| ((s.readReg64 (.gpr 21#5)).setWidth 32).setWidth 64) = w.w5
  x21lo : (s.readReg64 (.gpr 21#5)).toNat < 2 ^ 32
  trace : s.trace = s0.trace
  fs : s.fs = s0.fs

abbrev callCells (fsp : BitVec 64) (w : CallW) : List (Nat × Nat × SepProp) :=
  [cell fsp 0x40 w.w6, cell fsp 0x48 w.w3, cell fsp 0x50 w.w4]

/-! ## M3: `read_stdin` (send / recv), `read_file("coins")` (`M+0x560 → M+0x5d0`) -/

/-- History invariant after `run`: loaded initial files and empty stdout, or prior `allocFailedIn`. -/
def HistOk (i : Inputs) (s0 s : State) : Prop :=
  (s.fs.files = (initFsState (cliInputs i)).files ∧
    ProcessOutcome.traceStreamBytes .stdout s.trace = []) ∨ allocFailedIn s0 s

/-- Tightened post-`run` history invariant: exact initial files and empty stdout. -/
def HistOkTight (i : Inputs) (s : State) : Prop :=
  s.fs.files = (initFsState (cliInputs i)).files ∧
    ProcessOutcome.traceStreamBytes .stdout s.trace = []

/-- State at `M+0x5d0` (end of M3): coins `Vec` in `(x1, x0, [fsp+0x1c8])`, input `Vec` in
`(x23, [fsp+0x58], x27)`, `x20 = c.tag`, `w5` in `x21`, `args` in `x19`/`x24`, and unchanged files/stdout. -/
structure AtM4 (img : Obj.Image) (ext : String → Option (State → State)) (i : Inputs)
    (s0 s : State) (w : CallW) (c : CallV) (n : Nat) (buf coinsCap coinsPtr inCap : BitVec 64) :
    Prop where
  base : InMain img ext s0 s 0x5d0
  x0 : s.readReg64 .x0 = coinsPtr
  x1 : s.readReg64 .x1 = coinsCap
  x19 : s.readReg64 (.gpr 19#5) = buf
  x20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag
  x23 : s.readReg64 (.gpr 23#5) = inCap
  x24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n
  x27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (inputOf i c).length
  w0 : s.readReg64 (.gpr 25#5) = w.w0
  w1 : s.readReg64 (.gpr 22#5) = w.w1
  w2 : s.readReg64 (.gpr 26#5) = w.w2
  w5 : s.readReg64 (.gpr 21#5) = w.w5
  fs : s.fs.files = (initFsState (cliInputs i)).files
  trace : s.trace = s0.trace

abbrev m4Cells (fsp : BitVec 64) (w : CallW) (inPtr : BitVec 64) (coinsLen : Nat) :
    List (Nat × Nat × SepProp) :=
  [cell fsp 0x40 w.w6, cell fsp 0x48 w.w3, cell fsp 0x50 w.w4, cell fsp 0x58 inPtr,
    cell fsp 0x1c8 (BitVec.ofNat 64 coinsLen)]

/-! ## M4: `coins::install`, `Stores::open`, `run` (`M+0x5d0 → M+0x720`) -/

/-- State at `M+0x720` (`run` returned `Ok`): input `Vec` in `(x23, [fsp+0x58], x27)`, `args` in
`x19`/`x24`, and callee-saved frame pointers `x21 = fsp + 0x310` and `x22 = fsp + 0x78`. -/
structure AtM4End (img : Obj.Image) (ext : String → Option (State → State)) (i : Inputs)
    (s0 s : State) (c : CallV) (n : Nat) (buf inCap : BitVec 64) : Prop where
  base : InMain img ext s0 s 0x720
  x19 : s.readReg64 (.gpr 19#5) = buf
  x21 : s.readReg64 (.gpr 21#5) = s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64
  x22 : s.readReg64 (.gpr 22#5) = s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64
  x23 : s.readReg64 (.gpr 23#5) = inCap
  x24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n
  x27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (inputOf i c).length
  hist : HistOk i s0 s

/-- Tightened `AtM4End` carrying `HistOkTight i s`. -/
structure AtM4EndTight (img : Obj.Image) (ext : String → Option (State → State)) (i : Inputs)
    (s0 s : State) (c : CallV) (n : Nat) (buf inCap : BitVec 64) : Prop where
  base : InMain img ext s0 s 0x720
  x19 : s.readReg64 (.gpr 19#5) = buf
  x21 : s.readReg64 (.gpr 21#5) = s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64
  x22 : s.readReg64 (.gpr 22#5) = s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64
  x23 : s.readReg64 (.gpr 23#5) = inCap
  x24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n
  x27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (inputOf i c).length
  hist : HistOkTight i s

theorem AtM4EndTight.toAtM4End {img : Obj.Image} {ext : String → Option (State → State)}
    {i : Inputs} {s0 s : State} {c : CallV} {n : Nat} {buf inCap : BitVec 64}
    (h : AtM4EndTight img ext i s0 s c n buf inCap) :
    AtM4End img ext i s0 s c n buf inCap :=
  { base := h.base, x19 := h.x19, x21 := h.x21, x22 := h.x22, x23 := h.x23,
    x24 := h.x24, x27 := h.x27, hist := Or.inl h.hist }

/-- Owned stack slots at `M+0x720`: spilled input pointer and `run`'s `Ok` payload at `fsp + 0x1b8`. -/
abbrev m5Cells (A : RustAlloc) (fsp inPtr : BitVec 64) (g : StoresGhost) (out : List (BitVec 8)) :
    List (Nat × Nat × SepProp) :=
  [cell fsp 0x58 inPtr, (0x1b8, runResSize, runOkAt A (fsp + 0x1b8#64) g out)]

/-! ## M6: `write_stdout(&output)`, drops (`M+0xf34 → M+0xb24`) -/

/-- State at `M+0xf34` (after `Stores::commit`): bit 0 of `w21` is clear iff every write succeeded;
`args` in `x19`/`x24`. -/
structure AtM6 (img : Obj.Image) (ext : String → Option (State → State)) (s0 s : State)
    (ok : Bool) (n : Nat) (buf : BitVec 64) : Prop where
  base : InMain img ext s0 s 0xf34
  w21 : (s.readReg64 (.gpr 21#5)).getLsbD 0 = !ok
  x19 : s.readReg64 (.gpr 19#5) = buf
  x24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n

/-- Spill slots at `M+0xf34`: output `Vec` (`[fsp+0x18]`, `[fsp+0x10]`, `[fsp+0x8]`) and input
capacity/pointer (`[fsp+0x20]`, `[fsp+0x58]`). -/
abbrev m6Cells (fsp outCap outPtr outLen inCap inPtr : BitVec 64) : List (Nat × Nat × SepProp) :=
  [cell fsp 0x8 outLen, cell fsp 0x10 outPtr, cell fsp 0x18 outCap, cell fsp 0x20 inCap,
    cell fsp 0x58 inPtr]

end CryptoVerification.SignalSession.Cli.MainHops
