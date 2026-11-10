/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.PrevEncOKPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Inlined `SessionStructure::decode` Loop Definitions

Relocatable (`[LibsignalPlacement]`) loop and per-step contracts (`OverPrevDecodePlacedStmt`,
`OverDecRegsPlaced`, `OverDecEntryPlacedStmt`, `OverDecFieldPlacedStmt`, `OverDecHead*PlacedStmt`,
`OverDecKeyPlacedStmt`, `OverDecArmPlacedStmt`) on Block `518` (`lsProg_518 ext`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib ProofLib.ObjectLoad SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName)
open CryptoVerification.E2E.Record.DeserializeGeneral (GenField)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt ssgqOf genFieldsQ)
open CryptoVerification.CliHandshake.RespClosurePlaced

/-- Relocatable `[LibsignalPlacement]` inlined `SessionStructure::decode` of `enc`
(`(blkPl_518).base + 0x1ee8 → (blkPl_518).base + 0x2620`, closure frame `s.sp`) on `lsProg_518 ext`. -/
def OverPrevDecodePlacedStmt [LibsignalPlacement] : Prop :=
  ∀ (ext : String → Option (State → State)),
    ∀ (s0 s : State) (prevCap prevPtr encCap encPtr : BitVec 64) (enc : List (BitVec 8))
      (sess : Session (List (BitVec 8))),
    OverPrevEncOKAt enc sess →
    (lsProg_518 ext).CodeLoaded s.mem →
    s.pc = (blkPl_518).base + 0x1ee8#64 →
    s.status = .Running →
    (s.sp &&& 15#64 == 0#64) = true →
    s.trace = s0.trace →
    s.readReg64 .x21 = s.sp + 0x930#64 →
    s.readReg64 .x24 = 1#64 →
    s.readReg64 .x25 = 0xffffffffffffffff#64 →
    s.readReg64 .x27 = prevPtr →
    s.readReg64 .x29 = s.sp + 0xc70#64 →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2620#64) s
      (overPrevElemAt prevCap prevPtr encCap encPtr enc ∗ overDecScratchPre s.sp ∗
        stackAt s.sp overDecStackX ∗
        CryptoVerification.E2E.Record.A0.pool)
      (fun sf P_f =>
        (P_f ⊢ overPrevElemAt prevCap prevPtr encCap encPtr enc ∗
            overDecScratchPost s.sp (ssgqOf sess) ∗
            stackAt s.sp overDecStackX ∗
            CryptoVerification.E2E.Record.A0.pool ∗ anyHeap) ∧
        sf.sp = s.sp ∧ sf.trace = s0.trace ∧
        (lsProg_518 ext).CodeLoaded sf.mem ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.sp + 0x930#64 ∧ sf.readReg64 .x24 = 1#64 ∧
        sf.readReg64 .x25 = 0xffffffffffffffff#64 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = prevPtr ∧ sf.readReg64 .x29 = s.sp + 0xc70#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (PanicOomProp s0)

/-- Register and machine-state invariant at `(blkPl_518).base + off` inside the decode loop
under `[LibsignalPlacement]`. -/
def OverDecRegsPlaced [LibsignalPlacement] (ext : String → Option (State → State)) (s0 : State)
    (g : OverDecG) (off : BitVec 64) (s : State) : Prop :=
  s.pc = (blkPl_518).base + off ∧
  s.status = .Running ∧ s.sp = g.q ∧ (s.sp &&& 15#64 == 0#64) = true ∧ s.trace = s0.trace ∧
  (lsProg_518 ext).CodeLoaded s.mem ∧
  s.readReg64 .x19 = g.r19 ∧ s.readReg64 .x20 = g.r20 ∧ s.readReg64 .x26 = g.r26 ∧
  s.readReg64 .x21 = g.q + 0x930#64 ∧ s.readReg64 .x24 = 1#64 ∧
  s.readReg64 .x25 = 0xffffffffffffffff#64 ∧ s.readReg64 .x27 = g.prevPtr ∧
  s.readReg64 .x28 = g.q + 0xa90#64 ∧ s.readReg64 .x29 = g.q + 0xc70#64 ∧
  calleeSavedVRegs s = calleeSavedVRegs g.sv

/-- Relocatable `[LibsignalPlacement]` Entry (`+0x1ee8 → +0x216c`): from `OverPrevDecodePlacedStmt`'s
pre with `enc ≠ []` to the field body with `rest = enc` and `SSGQ.empty`. -/
def OverDecEntryPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ (ext : String → Option (State → State)),
    ∀ (s0 s : State) (g : OverDecG),
    g.enc ≠ [] → g.enc.length < 2 ^ 62 →
    (lsProg_518 ext).CodeLoaded s.mem →
    s.pc = (blkPl_518).base + 0x1ee8#64 →
    s.status = .Running → s.sp = g.q → (s.sp &&& 15#64 == 0#64) = true →
    s.trace = s0.trace →
    s.readReg64 .x19 = g.r19 → s.readReg64 .x20 = g.r20 → s.readReg64 .x26 = g.r26 →
    s.readReg64 .x21 = g.q + 0x930#64 → s.readReg64 .x24 = 1#64 →
    s.readReg64 .x25 = 0xffffffffffffffff#64 → s.readReg64 .x27 = g.prevPtr →
    s.readReg64 .x29 = g.q + 0xc70#64 →
    calleeSavedVRegs s = calleeSavedVRegs g.sv →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x216c#64) s
      (overPrevElemAt g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗ overDecScratchPre g.q ∗
        stackAt g.q overDecStackX ∗
        CryptoVerification.E2E.Record.A0.pool)
      (fun sf P_f => OverDecRegsPlaced ext s0 g 0x216c#64 sf ∧
        (P_f ⊢ overDecHeap g g.enc SSGQ.empty))
      (PanicOomProp s0)

/-- Relocatable `[LibsignalPlacement]` one field (`+0x216c → +0x2160`) restricted by `P`. -/
def OverDecFieldPlacedStmt [LibsignalPlacement] (P : GenFieldQ → Prop) : Prop :=
  ∀ (ext : String → Option (State → State)),
    ∀ (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8)),
    P fl → fl.Ok → fl.Fresh v →
    (fl.enc ++ rest) <:+ g.enc → g.enc.length < 2 ^ 62 →
    OverDecRegsPlaced ext s0 g 0x216c#64 s →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2160#64) s
      (overDecHeap g (fl.enc ++ rest) v)
      (fun sf P_f => OverDecRegsPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeap g rest (v.apply fl)))
      (PanicOomProp s0)

/-- Relocatable `[LibsignalPlacement]` loop head (`+0x2160 → +0x216c`) when `rest ≠ []`. -/
def OverDecHeadConsPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ (ext : String → Option (State → State)),
    ∀ (s0 s : State) (g : OverDecG) (v : SSGQ) (rest : List (BitVec 8)),
    rest ≠ [] → rest <:+ g.enc → g.enc.length < 2 ^ 62 →
    OverDecRegsPlaced ext s0 g 0x2160#64 s →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x216c#64) s
      (overDecHeap g rest v)
      (fun sf P_f => OverDecRegsPlaced ext s0 g 0x216c#64 sf ∧ (P_f ⊢ overDecHeap g rest v))
      (PanicOomProp s0)

/-- Relocatable `[LibsignalPlacement]` loop head (`+0x2160 → +0x2620`) when `rest = []`. -/
def OverDecHeadNilPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ (ext : String → Option (State → State)),
    ∀ (s0 s : State) (g : OverDecG) (v : SSGQ),
    g.enc.length < 2 ^ 62 →
    OverDecRegsPlaced ext s0 g 0x2160#64 s →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2620#64) s
      (overDecHeap g [] v)
      (fun sf P_f => OverDecRegsPlaced ext s0 g 0x2620#64 sf ∧ (P_f ⊢ overDecHeap g [] v))
      (PanicOomProp s0)

/-- Relocatable `[LibsignalPlacement]` Key (`+0x216c → overDecArmOff fl`). -/
def OverDecKeyPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ (ext : String → Option (State → State)),
    ∀ (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8)),
    OverDecAnyField fl → fl.Ok →
    (fl.enc ++ rest) <:+ g.enc → g.enc.length < 2 ^ 62 →
    OverDecRegsPlaced ext s0 g 0x216c#64 s →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + overDecArmOff fl) s
      (overDecHeap g (fl.enc ++ rest) v)
      (fun sf P_f => OverDecRegsPlaced ext s0 g (overDecArmOff fl) sf ∧
        sf.readReg64 .x0 = overDecWt fl ∧
        sf.readReg64 .x22 = BitVec.ofNat 64 (fl.tag * 8 + (overDecWt fl).toNat) ∧
        (P_f ⊢ overDecHeap g (fl.payload ++ rest) v))
      (PanicOomProp s0)

/-- Relocatable `[LibsignalPlacement]` Arm contract (`overDecArmOff fl → +0x2160`). -/
def OverDecArmPlacedStmt [LibsignalPlacement] (P : GenFieldQ → Prop) : Prop :=
  ∀ (ext : String → Option (State → State)),
    ∀ (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8)),
    P fl → fl.Ok → fl.Fresh v →
    (fl.enc ++ rest) <:+ g.enc → g.enc.length < 2 ^ 62 →
    OverDecRegsPlaced ext s0 g (overDecArmOff fl) s →
    s.readReg64 .x0 = overDecWt fl →
    s.readReg64 .x22 = BitVec.ofNat 64 (fl.tag * 8 + (overDecWt fl).toNat) →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2160#64) s
      (overDecHeap g (fl.payload ++ rest) v)
      (fun sf P_f => OverDecRegsPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeap g rest (v.apply fl)))
      (PanicOomProp s0)

abbrev OverDecArmPlacedStmtTR [LibsignalPlacement] (P : GenFieldQ → Prop) : Prop :=
  OverDecArmPlacedStmt P

theorem OverDecArmPlacedStmt.toTR [LibsignalPlacement] {P : GenFieldQ → Prop}
    (h : OverDecArmPlacedStmt P) : OverDecArmPlacedStmtTR P := h

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
