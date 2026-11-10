/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Hops
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.LitsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable Hop Contracts M1–M6 for `main` (`[LibsignalPlacement]`, Block `617`)

Relocatable `[LibsignalPlacement]` counterparts of `Hops.lean` on Block `617` (`mProgPlaced H` =
`lsProg_617 H`, `mPcPlaced k` = `lsmpl.base 617 + k`), parameterized over any frozen code and
`.rodata` invariant `[LsCodeInv CodeOk]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## Block `617` Syntactic Normalization Bridges -/

theorem mProgPlaced_eq [LibsignalPlacement] (H : LibsignalHooks) :
    mProgPlaced H = (blkPC_617).rebase (blkPl_617).base H := rfl

theorem mPcPlaced_eq [LibsignalPlacement] (k : Nat) :
    mPcPlaced k = (blkPl_617).base + BitVec.ofNat 64 k := rfl

theorem mPcPlaced_zero [LibsignalPlacement] :
    mPcPlaced 0 = (blkPl_617).base := by
  change lsmpl.base 617 + 0#64 = (blkPl_617).base
  exact BitVec.add_zero _

theorem blkPl_617_base_eq [LibsignalPlacement] :
    (blkPl_617).base = lsmpl.base 617 := rfl

/-! ## Frozen Code + `.rodata` Invariant Typeclass (`LsCodeInv`) -/

/-- Frozen code and `.rodata` memory invariant extending `LibsignalCodeRoLoaded lsmpl` and preserved
across `VmPreserved` hooks (instantiated by `LibsignalCodeRoLoaded`, `LibsignalFrozen`, or mutant
invariants). -/
class LsCodeInv [LibsignalPlacement] (CodeOk : Memory → Prop) : Prop where
  toRoCl : ∀ {m}, CodeOk m → LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl m
  of_keepsFrozen : ∀ {m m'}, CodeOk m → Memory.KeepsFrozen m m' → CodeOk m'

instance instLsCodeInvCodeRoLoaded [LibsignalPlacement] :
    LsCodeInv (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) where
  toRoCl h := h
  of_keepsFrozen h hkf := h.of_keepsFrozen hkf

instance instLsCodeInvFrozen [LibsignalPlacement] :
    LsCodeInv (LibsignalFrozen lsmpl) where
  toRoCl h := ⟨LibsignalCodeLoaded.of_codeLoaded h.2, h.1⟩
  of_keepsFrozen h hkf := libsignalFrozen_of_keepsFrozen h hkf

theorem LsCodeInv.codeLoaded_mProgPlaced [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk] {m : Memory} (h : CodeOk m) (H : LibsignalHooks) :
    (mProgPlaced H).CodeLoaded m := by
  have heq : mProgPlaced H = libsignalSessionLib.blockProgram lsmpl 617 H :=
    IsLsBlockProg.eq_blockProgram (prog := lsProg_617 H) (i := 617) (H := H)
  rw [heq]
  exact (hCI.toRoCl h).1 617 (by decide) (by decide) H (fun _ => none) Syscall.standard

/-! ## Block-`617` Callee Bundle (`MainCalleesBlk617`) -/

/-- Mangled symbol name for `alloc::raw_vec::handle_error` in Block `617` (`main`). -/
abbrev lsHandleErrorSymMain : String := "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"

/-- Relocatable `MainCallees` on Block `617` (`address` at Block `580`, `reserve16`/`reserve1` at
Block `561`, `tryAllocateIn3` at Block `588`, and `handle_error` panic stub). -/
structure MainCalleesBlk617 [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (uuidParse : UuidParser) (hookStack resStack : Nat) : Prop where
  alloc : AllocContractsXCliPlaced A H
  allocFs : AllocContractsFsPlaced A H
  strlen : subroutine_ok (lsProg_617 H) (lsρ "strlen")
    (withLsRoCl lsmpl (strlenSpec hookStack))
  fromUtf8 : subroutine_ok (lsProg_617 H) (lsρ lsFromUtf8Sym)
    (withLsRoCl lsmpl (fromUtf8AsciiSpec hookStack))
  address : subroutine_ok (lsProg_617 H) (lsmpl.base 580)
    (withLsRoCl lsmpl (addressSpec A uuidParse resStack))
  reserve16 : subroutine_ok (lsProg_617 H) (lsmpl.base 561)
    (withLsRoCl lsmpl (reserve16Spec A resStack))
  reserve1 : subroutine_ok (lsProg_617 H) (lsmpl.base 561)
    (withLsRoCl lsmpl
      (CryptoVerification.SpqrV1.Varint.doReserveSpecOf resStack A).keepsFs)
  tryAllocateIn3 : subroutine_ok (lsProg_617 H) (lsmpl.base 588)
    (withLsRoCl lsmpl (tryAllocateInSpecOf resStack A).keepsFs)
  handleErrorPanic : (lsProg_617 H).externAt? (lsρ lsHandleErrorSymMain) = some Rust.panicked

abbrev runSpecTightPlaced [LibsignalPlacement] := runSpecPlaced

theorem subroutine_ok_runSpecPlaced_of_tight [LibsignalPlacement] {P : Program} {e : BitVec 64}
    {CodeOk : Memory → Prop} {A : RustAlloc} {uuidParse : UuidParser}
    {Run : Inputs → RunAnswer → Prop} {wrOk : List (BitVec 8) → Prop} {resStack : Nat}
    (h : subroutine_ok P e (runSpecTightPlaced CodeOk A uuidParse Run wrOk resStack)) :
    subroutine_ok P e (runSpecPlaced CodeOk A uuidParse Run wrOk resStack) :=
  h

/-! ## Hop States and Shared Exit (`[LibsignalPlacement]`) -/

structure InMainPlaced [LibsignalPlacement] (CodeOk : Memory → Prop)
    (s0 s : State) (k : Nat) : Prop where
  pc : s.pc = mPcPlaced k
  run : s.status = .Running
  sp : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize
  fp : s.readReg64 .fp = s0.sp - 0x60#64
  inv : CodeOk s.mem
  vregs : calleeSavedVRegs s = calleeSavedVRegs s0
  spAligned : s0.spAligned = true

/-- Shared return block `M+0xb80` (`mov w0, w26`; restore; `ret`) with exit code in `w26`. -/
structure AtRetPlaced [LibsignalPlacement] (CodeOk : Memory → Prop)
    (s0 s : State) (code : Nat) : Prop where
  base : InMainPlaced CodeOk s0 s 0xb80
  w26 : (s.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code

def ExitKPlacedRet [LibsignalPlacement] (CodeOk : Memory → Prop) (H : LibsignalHooks)
    (A : RustAlloc) (s0 : State) (ret : BitVec 64) (stk : Nat) (G : Nat → State → Prop)
    (Q Qp : State → SepProp → Prop) : Prop :=
  ∀ (s : State) (code : Nat), AtRetPlaced CodeOk s0 s code → G code s →
    ProofLib.SepWPp (mProgPlaced H) ret s (retMem A s0 stk) Q Qp (mainOom s0)

abbrev ExitKPlaced [LibsignalPlacement] (CodeOk : Memory → Prop) (H : LibsignalHooks)
    (A : RustAlloc) (s0 : State) (stk : Nat) (G : Nat → State → Prop)
    (Q Qp : State → SepProp → Prop) : Prop :=
  ExitKPlacedRet CodeOk H A s0 (s0.readReg64 .lr) stk G Q Qp

structure AtM1EndPlaced [LibsignalPlacement] (CodeOk : Memory → Prop)
    (s0 s : State) (n : Nat) (buf : BitVec 64) : Prop where
  base : InMainPlaced CodeOk s0 s 0xc0
  x19 : s.readReg64 (.gpr 19#5) = buf
  x22 : s.readReg64 (.gpr 22#5) = buf + BitVec.ofNat 64 (16 * n)
  x23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n
  x24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n
  x25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 n
  trace : s.trace = s0.trace
  fs : s.fs = s0.fs

structure AtEntryPlaced [LibsignalPlacement] (CodeOk : Memory → Prop)
    (i : Inputs) (s0 : State) : Prop where
  pc : s0.pc = mPcPlaced 0
  run : s0.status = .Running
  inv : CodeOk s0.mem
  argc : (s0.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1)
  spAligned : s0.spAligned = true

/-- State at `M+0x568` (end of M2): `w0 = x25`, `w2 = x22`, `w6 = x26`, and `w3, w4, w1` spilled at
`[fsp+0x40], [fsp+0x48], [fsp+0x58]`. -/
structure AtCallPlaced [LibsignalPlacement] (CodeOk : Memory → Prop)
    (s0 s : State) (w : CallW) (n : Nat) (buf : BitVec 64) : Prop where
  base : InMainPlaced CodeOk s0 s 0x568
  x19 : s.readReg64 (.gpr 19#5) = buf
  x24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n
  w0 : s.readReg64 (.gpr 25#5) = w.w0
  w2 : s.readReg64 (.gpr 22#5) = w.w2
  w5 : (s.readReg64 (.gpr 28#5) ||| ((s.readReg64 (.gpr 21#5)).setWidth 32).setWidth 64) = w.w5
  x21lo : (s.readReg64 (.gpr 21#5)).toNat < 2 ^ 32
  w6 : s.readReg64 (.gpr 26#5) = w.w6
  trace : s.trace = s0.trace
  fs : s.fs = s0.fs

abbrev callCellsPlaced (fsp : BitVec 64) (w : CallW) : List (Nat × Nat × SepProp) :=
  [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x58 w.w1]

/-- State at `M+0x5dc` (end of M3): coins `Vec` in `(x1, x0, [fsp+0x1c8])`, input `Vec` in
`(x23, [fsp+0x50], x27)`, `x20 = c.tag`, `w0 = x25`, `w2 = x22`, `w5 = x21`, `w6 = x26`, and spills in
`m4CellsPlaced`. -/
structure AtM4Placed [LibsignalPlacement] (CodeOk : Memory → Prop) (i : Inputs)
    (s0 s : State) (w : CallW) (c : CallV) (n : Nat) (buf coinsCap coinsPtr inCap : BitVec 64) :
    Prop where
  base : InMainPlaced CodeOk s0 s 0x5dc
  x0 : s.readReg64 .x0 = coinsPtr
  x1 : s.readReg64 .x1 = coinsCap
  x19 : s.readReg64 (.gpr 19#5) = buf
  x20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag
  x23 : s.readReg64 (.gpr 23#5) = inCap
  x24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n
  x27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (inputOf i c).length
  w0 : s.readReg64 (.gpr 25#5) = w.w0
  w2 : s.readReg64 (.gpr 22#5) = w.w2
  w5 : s.readReg64 (.gpr 21#5) = w.w5
  w6 : s.readReg64 (.gpr 26#5) = w.w6
  fs : s.fs.files = (initFsState (cliInputs i)).files
  trace : s.trace = s0.trace

abbrev m4CellsPlaced (fsp : BitVec 64) (w : CallW) (inPtr : BitVec 64) (coinsLen : Nat) :
    List (Nat × Nat × SepProp) :=
  [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1,
    cell fsp 0x1c8 (BitVec.ofNat 64 coinsLen)]

/-- State at `M+0x7b0` (`run` returned `Ok`). -/
structure AtM4EndPlaced [LibsignalPlacement] (CodeOk : Memory → Prop) (i : Inputs)
    (s0 s : State) (c : CallV) (n : Nat) (buf inCap : BitVec 64) : Prop where
  base : InMainPlaced CodeOk s0 s 0x7b0
  x19 : s.readReg64 (.gpr 19#5) = buf
  x21 : s.readReg64 (.gpr 21#5) = s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64
  x22 : s.readReg64 (.gpr 22#5) = s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64
  x23 : s.readReg64 (.gpr 23#5) = inCap
  x24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n
  x27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (inputOf i c).length
  hist : HistOk i s0 s

/-- Tightened `AtM4EndPlaced` (`HistOkTight i s`) at `M+0x7b0`. -/
structure AtM4EndTightPlaced [LibsignalPlacement] (CodeOk : Memory → Prop) (i : Inputs)
    (s0 s : State) (c : CallV) (n : Nat) (buf inCap : BitVec 64) : Prop where
  base : InMainPlaced CodeOk s0 s 0x7b0
  x19 : s.readReg64 (.gpr 19#5) = buf
  x21 : s.readReg64 (.gpr 21#5) = s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64
  x22 : s.readReg64 (.gpr 22#5) = s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64
  x23 : s.readReg64 (.gpr 23#5) = inCap
  x24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n
  x27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (inputOf i c).length
  hist : HistOkTight i s

theorem AtM4EndTightPlaced.toAtM4EndPlaced [LibsignalPlacement] {CodeOk : Memory → Prop}
    {i : Inputs} {s0 s : State} {c : CallV} {n : Nat} {buf inCap : BitVec 64}
    (h : AtM4EndTightPlaced CodeOk i s0 s c n buf inCap) :
    AtM4EndPlaced CodeOk i s0 s c n buf inCap :=
  { base := h.base, x19 := h.x19, x21 := h.x21, x22 := h.x22, x23 := h.x23,
    x24 := h.x24, x27 := h.x27, hist := Or.inl h.hist }

abbrev m5CellsPlaced (A : RustAlloc) (fsp inPtr : BitVec 64) (g : StoresGhost)
    (out : List (BitVec 8)) : List (Nat × Nat × SepProp) :=
  [cell fsp 0x50 inPtr, (0x1b8, runResSize, runOkAt A (fsp + 0x1b8#64) g out)]

/-- State at `M+0xf70` (after `Stores::commit`): bit 0 of `w22` is clear iff every write succeeded;
`args` in `x19`/`x24`. -/
structure AtM6Placed [LibsignalPlacement] (CodeOk : Memory → Prop)
    (s0 s : State) (ok : Bool) (n : Nat) (buf : BitVec 64) : Prop where
  base : InMainPlaced CodeOk s0 s 0xf70
  w22 : (s.readReg64 (.gpr 22#5)).getLsbD 0 = !ok
  x19 : s.readReg64 (.gpr 19#5) = buf
  x24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n

abbrev m6CellsPlaced (fsp outCap outPtr outLen inCap inPtr : BitVec 64) :
    List (Nat × Nat × SepProp) :=
  [cell fsp 0x0 outLen, cell fsp 0x8 outCap, cell fsp 0x10 inCap, cell fsp 0x18 outPtr,
    cell fsp 0x50 inPtr]

end CryptoVerification.SignalSession.Cli.MainHops
