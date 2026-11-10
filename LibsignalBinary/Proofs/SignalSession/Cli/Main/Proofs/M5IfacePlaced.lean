/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.FramePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5Iface
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Loop Invariant and Error-Exit Interface for `main` Hop M5 (Block `617`)

Relocatable `[LibsignalPlacement]` counterparts of `AtM5LoopPlaced`, `m5LoopCellsPlaced`,
`m5LoopMemPlaced`, `M5ErrEntryPlaced`, and `M5LoopErrPlaced` on Block `617` (`M+0x7b0 → M+0xf70`),
re-exporting pure `DirGhost` and `commitFiles` lemmas from `M5Iface.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit

/-! ## 1. Spatial `Dir` Tail Predicates and `locals` Frames -/

/-- Owned pieces inside `locals fsp` at `AtM5LoopPlaced` after `k` `Dir`s (`k ≤ 8`):
`m6CellsPlaced` (`0x00 .. 0x20`, `0x50 .. 0x58`) plus the remaining `8 - k` `Dir`s at
`0x1c8 + 0x28 * k .. 0x308`. -/
def m5LoopCellsPlaced (A : RustAlloc) (fsp outCap outPtr outLen inCap inPtr : BitVec 64)
    (g : StoresGhost) (k : Nat) : List (Nat × Nat × SepProp) :=
  m6CellsPlaced fsp outCap outPtr outLen inCap inPtr ++
    [(0x1c8 + 0x28 * k, 0x28 * (8 - k),
      dirsAt A (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * k)) ((storesDirs g).drop k))]

theorem m5LoopCellsPlaced_zero_eq (A : RustAlloc)
    (fsp outCap outPtr outLen inCap inPtr : BitVec 64) (g : StoresGhost) :
    m5LoopCellsPlaced A fsp outCap outPtr outLen inCap inPtr g 0 =
      m6CellsPlaced fsp outCap outPtr outLen inCap inPtr ++
        [(0x1c8, 0x140, storesAt A (fsp + 0x1c8#64) g)] := by
  simp only [m5LoopCellsPlaced, Nat.mul_zero, Nat.add_zero, Nat.sub_zero, List.drop_zero,
    dirsAt_storesDirs]

theorem locals_m5LoopCellsPlaced_eight (A : RustAlloc)
    (fsp outCap outPtr outLen inCap inPtr : BitVec 64) (g : StoresGhost) :
    locals fsp (m5LoopCellsPlaced A fsp outCap outPtr outLen inCap inPtr g 8) =
      locals fsp (m6CellsPlaced fsp outCap outPtr outLen inCap inPtr) := by
  have h8 : (storesDirs g).drop 8 = [] :=
    List.drop_of_length_le (by simp [storesDirs_length])
  have hcarve := locals_carve_region fsp
    (m6CellsPlaced fsp outCap outPtr outLen inCap inPtr) 0x308 0 []
    (by simp [localsEnd]) (by simp [localsBound]) (by simp [localsBound])
  simp only [List.append_nil] at hcarve
  rw [hcarve]
  unfold m5LoopCellsPlaced
  simp only [h8, dirsAt_nil, Nat.sub_self, Nat.mul_zero, memRegion_zero]

/-- Advance `locals fsp` from `k` to `k + 1` once `Dir k`'s 40-byte stack header has become
`memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * k)) 0x28`. -/
theorem locals_m5LoopCellsPlaced_step (A : RustAlloc)
    (fsp outCap outPtr outLen inCap inPtr : BitVec 64) (g : StoresGhost)
    {k : Nat} (hk : k < 8) :
    locals fsp
      (m6CellsPlaced fsp outCap outPtr outLen inCap inPtr ++
        [(0x1c8 + 0x28 * k, 0x28 * (8 - k),
          memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * k)) 0x28 ∗
            dirsAt A (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1)))
              ((storesDirs g).drop (k + 1)))]) =
      locals fsp (m5LoopCellsPlaced A fsp outCap outPtr outLen inCap inPtr g (k + 1)) := by
  have hcarve := locals_carve_region fsp
    (m6CellsPlaced fsp outCap outPtr outLen inCap inPtr)
    (0x1c8 + 0x28 * k) 0x28
    [(0x1c8 + 0x28 * (k + 1), 0x28 * (8 - (k + 1)),
      dirsAt A (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1))) ((storesDirs g).drop (k + 1)))]
    (by simp [localsEnd]; omega)
    (by simp [localsBound]; omega)
    (by simp [localsBound]; omega)
  unfold m5LoopCellsPlaced at hcarve ⊢
  rw [hcarve]
  have hsub0 : 0x1c8 + 0x28 * (k + 1) - (0x1c8 + 0x28 * k + 0x28) = 0 := by omega
  have hend :
      0x1c8 + 0x28 * (k + 1) + 0x28 * (8 - (k + 1)) =
        0x1c8 + 0x28 * k + 0x28 * (8 - k) := by omega
  simp only [m6CellsPlaced, locals, localsFrom, List.cons_append, List.nil_append,
    Nat.sub_self, hsub0, hend, memRegion_zero]
  ac_rfl

/-- Full separation-logic memory at `AtM5LoopPlaced` after `k` `Dir`s (`k ≤ 8`). -/
def m5LoopMemPlaced (A : RustAlloc) (s0 : State) (stk n : Nat)
    (outCap outPtr inCap inPtr buf : BitVec 64)
    (out inp : List (BitVec 8))
    (ps : List (BitVec 64 × List (BitVec 8)))
    (g : StoresGhost) (k : Nat) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
    ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
    argsBuf A (BitVec.ofNat 64 n) buf ps ∗
    mainSaved s0 ∗
    locals fsp
      (m5LoopCellsPlaced A fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k) ∗
    stackAt fsp (stk - mainFrameSize) ∗
    A.pool ∗ anyHeap

/-! ## 2. Loop Invariant `AtM5LoopPlaced` (`M+0x8b8` for `k < 8`, `M+0xadc` for `k = 8`) -/

/-- Relocatable `[LibsignalPlacement]` state invariant of `main`'s M5 commit loop after `k` `Dir`s
(`k ≤ 8`, `x19 = buf`, `x23 = k`, `x25 = fsp + 0x1c8`, `x24 = n`, `x26 = 0x28`). -/
structure AtM5LoopPlaced [LibsignalPlacement] (CodeOk : Memory → Prop)
    (io : IoModel) (F0 : FsFiles) (tr0 : List TraceEvent)
    (g : StoresGhost) (s0 s : State) (n : Nat) (buf : BitVec 64) (k : Nat) : Prop where
  hk : k ≤ 8
  base : InMainPlaced CodeOk s0 s (if k < 8 then 0x8b8 else 0xadc)
  x19 : s.readReg64 (.gpr 19#5) = buf
  x23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 k
  x25 : s.readReg64 (.gpr 25#5) = s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64
  x24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n
  x26 : s.readReg64 (.gpr 26#5) = 0x28#64
  files : commitFiles io.wr F0 (writesBefore g k) = some s.fs.files
  trace : tr0 <+: s.trace
  stdout : ProcessOutcome.traceStreamBytes .stdout s.trace =
    ProcessOutcome.traceStreamBytes .stdout tr0

/-- Convenience constructor at `k = 0` for `m5_moves_placed`, when `s'.fs = s.fs` and
`s'.trace = s.trace`. -/
theorem AtM5LoopPlaced.of_zero [LibsignalPlacement] {CodeOk : Memory → Prop}
    {io : IoModel} {g : StoresGhost} {s0 s s' : State} {n : Nat} {buf : BitVec 64}
    (hbase : InMainPlaced CodeOk s0 s' 0x8b8)
    (hx19 : s'.readReg64 (.gpr 19#5) = buf)
    (hx23 : s'.readReg64 (.gpr 23#5) = 0#64)
    (hx25 : s'.readReg64 (.gpr 25#5) = s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64)
    (hx24 : s'.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx26 : s'.readReg64 (.gpr 26#5) = 0x28#64)
    (hfs : s'.fs.files = s.fs.files)
    (htr : s'.trace = s.trace) :
    AtM5LoopPlaced CodeOk io s.fs.files s.trace g s0 s' n buf 0 where
  hk := by decide
  base := hbase
  x19 := hx19
  x23 := hx23
  x25 := hx25
  x24 := hx24
  x26 := hx26
  files := by simp [writesBefore_zero, commitFiles_nil, hfs]
  trace := htr ▸ List.prefix_refl _
  stdout := by rw [htr]

/-! ## 3. Write-Error Exit Interface `M5LoopErrPlaced` (`M+0xbcc` / `M+0xbdc` / `M+0xbf4`) -/

/-- Which of the three `write_file` error exits in `main` was entered on `Err`. -/
inductive M5ErrEntryPlaced where
  /-- `M+0xbcc` (Loop A, non-empty `Dir.path`). -/
  | bcc (pathCap pathPtr : BitVec 64) (pathBs : List (BitVec 8))
  /-- `M+0xbdc` (Loop B, empty `Dir.path`, non-empty `name`). -/
  | bdc (pathCap pathPtr : BitVec 64) (pathBs : List (BitVec 8))
  /-- `M+0xbf4` (Loop B, empty `Dir.path`, empty `name`): nothing temporary to free. -/
  | bf4

/-- `main`-relative byte offset of an `M5ErrEntryPlaced`. -/
def M5ErrEntryPlaced.pcOff : M5ErrEntryPlaced → Nat
  | .bcc .. => 0xbcc
  | .bdc .. => 0xbdc
  | .bf4 => 0xbf4

/-- Entry register facts for `M5ErrEntryPlaced` (`x22 = ptr`, `x23 = cap` at `0xbcc`;
`x22 = ptr`, `x23 = cap`, `cap ≠ 0` at `0xbdc`). -/
def M5ErrEntryPlaced.regs : M5ErrEntryPlaced → State → Prop
  | .bcc cap ptr _, s => s.readReg64 (.gpr 22#5) = ptr ∧ s.readReg64 (.gpr 23#5) = cap
  | .bdc cap ptr _, s => s.readReg64 (.gpr 22#5) = ptr ∧ s.readReg64 (.gpr 23#5) = cap ∧ cap ≠ 0#64
  | .bf4, _ => True

/-- Heap ownership of the temporary path `String` (if any) at `M5ErrEntryPlaced`. -/
def M5ErrEntryPlaced.heap (A : RustAlloc) : M5ErrEntryPlaced → SepProp
  | .bcc cap ptr bs => ownedBytes A cap ptr (BitVec.ofNat 64 bs.length) bs
  | .bdc cap ptr bs => ownedBytes A cap ptr (BitVec.ofNat 64 bs.length) bs
  | .bf4 => emp

/-- Owned pieces inside `locals fsp` at `M5LoopErrPlaced` (`k < 8`):
`m6CellsPlaced` plus loop spills `0x20` (`curCap`), `0x28` (`curPtr`), `0x30` (`fsp + 0x1c8`),
`0x38` (`k + 1`), and remaining `Dir`s `k + 1 .. 7` at `0x1c8 + 0x28 * (k + 1) .. 0x308`. -/
def m5ErrCellsPlaced (A : RustAlloc) (fsp outCap outPtr outLen inCap inPtr curCap curPtr : BitVec 64)
    (g : StoresGhost) (k : Nat) : List (Nat × Nat × SepProp) :=
  [cell fsp 0x0 outLen,
   cell fsp 0x8 outCap,
   cell fsp 0x10 inCap,
   cell fsp 0x18 outPtr,
   cell fsp 0x20 curCap,
   cell fsp 0x28 curPtr,
   cell fsp 0x30 (fsp + 0x1c8#64),
   cell fsp 0x38 (BitVec.ofNat 64 (k + 1)),
   cell fsp 0x50 inPtr,
   (0x1c8 + 0x28 * (k + 1), 0x28 * (8 - (k + 1)),
     dirsAt A (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1))) ((storesDirs g).drop (k + 1)))]

/-- Collapse the loop spills `0x20`, `0x28`, `0x30`, `0x38` and an empty/freed tail `memRegion`
at `0x1c8 + 0x28 * m` (`m ≤ 8`) back into `locals fsp (m6CellsPlaced …)`. -/
theorem locals_m5ErrCellsPlaced_forget_to_m6CellsPlaced
    (fsp outCap outPtr outLen inCap inPtr v20 v28 v30 v38 : BitVec 64)
    {m : Nat} (hm : m ≤ 8) :
    locals fsp
      [cell fsp 0x0 outLen,
       cell fsp 0x8 outCap,
       cell fsp 0x10 inCap,
       cell fsp 0x18 outPtr,
       cell fsp 0x20 v20,
       cell fsp 0x28 v28,
       cell fsp 0x30 v30,
       cell fsp 0x38 v38,
       cell fsp 0x50 inPtr,
       (0x1c8 + 0x28 * m, 0x28 * (8 - m),
         memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * m)) (0x28 * (8 - m)))] ⊢
      locals fsp (m6CellsPlaced fsp outCap outPtr outLen inCap inPtr) := by
  have h1 := locals_forget_cell fsp
    [cell fsp 0x0 outLen, cell fsp 0x8 outCap, cell fsp 0x10 inCap, cell fsp 0x18 outPtr]
    0x20 v20
    [cell fsp 0x28 v28, cell fsp 0x30 v30, cell fsp 0x38 v38, cell fsp 0x50 inPtr,
     (0x1c8 + 0x28 * m, 0x28 * (8 - m),
       memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * m)) (0x28 * (8 - m)))]
    (by simp [localsEnd]) (by simp [localsBound]) (by simp [localsBound])
  have h2 := locals_forget_cell fsp
    [cell fsp 0x0 outLen, cell fsp 0x8 outCap, cell fsp 0x10 inCap, cell fsp 0x18 outPtr]
    0x28 v28
    [cell fsp 0x30 v30, cell fsp 0x38 v38, cell fsp 0x50 inPtr,
     (0x1c8 + 0x28 * m, 0x28 * (8 - m),
       memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * m)) (0x28 * (8 - m)))]
    (by simp [localsEnd]) (by simp [localsBound]) (by simp [localsBound])
  have h3 := locals_forget_cell fsp
    [cell fsp 0x0 outLen, cell fsp 0x8 outCap, cell fsp 0x10 inCap, cell fsp 0x18 outPtr]
    0x30 v30
    [cell fsp 0x38 v38, cell fsp 0x50 inPtr,
     (0x1c8 + 0x28 * m, 0x28 * (8 - m),
       memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * m)) (0x28 * (8 - m)))]
    (by simp [localsEnd]) (by simp [localsBound]) (by simp [localsBound])
  have h4 := locals_forget_cell fsp
    [cell fsp 0x0 outLen, cell fsp 0x8 outCap, cell fsp 0x10 inCap, cell fsp 0x18 outPtr]
    0x38 v38
    [cell fsp 0x50 inPtr,
     (0x1c8 + 0x28 * m, 0x28 * (8 - m),
       memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * m)) (0x28 * (8 - m)))]
    (by simp [localsEnd]) (by simp [localsBound]) (by simp [localsBound])
  have h5 := (locals_carve_region fsp
    (m6CellsPlaced fsp outCap outPtr outLen inCap inPtr)
    (0x1c8 + 0x28 * m) (0x28 * (8 - m)) []
    (by simp [localsEnd]; omega)
    (by simp [localsBound]; omega)
    (by simp [localsBound])).symm
  exact Entails.trans h1 (Entails.trans h2 (Entails.trans h3 (Entails.trans h4 (Entails.of_eq h5))))

/-- Full separation-logic memory at `M5LoopErrPlaced` (`M+0xbcc` / `M+0xbdc` / `M+0xbf4`). -/
def m5ErrMemPlaced (A : RustAlloc) (s0 : State) (stk n : Nat)
    (outCap outPtr inCap inPtr buf curCap curPtr : BitVec 64)
    (out inp : List (BitVec 8))
    (ps : List (BitVec 64 × List (BitVec 8)))
    (g : StoresGhost) (k : Nat)
    (curEntries : List (List (BitVec 8) × List (BitVec 8)))
    (e : M5ErrEntryPlaced) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  e.heap A ∗
    vecBuf A 48 8 (dirEntryAt A) curCap curPtr curEntries ∗
    ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
    ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
    argsBuf A (BitVec.ofNat 64 n) buf ps ∗
    mainSaved s0 ∗
    locals fsp
      (m5ErrCellsPlaced A fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr curCap curPtr g k) ∗
    stackAt fsp (stk - mainFrameSize) ∗
    A.pool ∗ anyHeap

/-- Relocatable `[LibsignalPlacement]` error-exit state at `M+0xbcc` / `M+0xbdc` / `M+0xbf4`
when a `write_file` call in `Dir k` (`k < 8`) returned `Err` (`x20 = curEntries.length`). -/
structure M5LoopErrPlaced [LibsignalPlacement] (CodeOk : Memory → Prop)
    (io : IoModel) (F0 : FsFiles) (tr0 : List TraceEvent)
    (g : StoresGhost) (s0 s : State) (n : Nat) (buf : BitVec 64)
    (k : Nat) (curEntries : List (List (BitVec 8) × List (BitVec 8)))
    (e : M5ErrEntryPlaced) : Prop where
  hk : k < 8
  hne : curEntries ≠ []
  errRegs : e.regs s
  base : InMainPlaced CodeOk s0 s e.pcOff
  x19 : s.readReg64 (.gpr 19#5) = buf
  x24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n
  x20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 curEntries.length
  commitNone : commitFiles io.wr F0 g.writes = none
  trace : tr0 <+: s.trace
  stdout : ProcessOutcome.traceStreamBytes .stdout s.trace =
    ProcessOutcome.traceStreamBytes .stdout tr0

end CryptoVerification.SignalSession.Cli.MainHops
