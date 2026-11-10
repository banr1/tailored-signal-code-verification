/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Frame

/-!
# Loop Invariant, Error-Exit Interface, and `commitFiles` Algebra for `main` Hop M5

Defines the ordered `storesDirs` / `commitFiles` algebra, the outer M5 loop invariant (`AtM5Loop`,
`m5LoopCells`, `m5LoopMem`), and the write-error exit interface (`M5ErrEntry`, `M5LoopErr`,
`m5ErrCells`, `m5ErrMem`) connecting M5's payload moves, 8-`Dir` commit loop, and error cleanup.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.LibsignalPublicApi.StoreKit

/-! ## 1. Ordered `DirGhost` List and `commitFiles` Algebra -/

/-- The eight `DirGhost`s of `g : StoresGhost`, in `Stores::commit` / `storesAt` order (`0 .. 7`). -/
def storesDirs (g : StoresGhost) : List DirGhost :=
  [g.identity.own, g.identity.peers, g.signed, g.kyber.oneTime,
    g.kyber.lastResort, g.oneTime, g.sessions, g.pub]

@[simp]
theorem storesDirs_length (g : StoresGhost) : (storesDirs g).length = 8 := rfl

/-- Writes of the first `k` directories (`0 .. k - 1`) of `g`. -/
def writesBefore (g : StoresGhost) (k : Nat) : List (List (BitVec 8) × List (BitVec 8)) :=
  ((storesDirs g).take k).flatMap DirGhost.writes

/-- Writes of the remaining directories (`k .. 7`) of `g`. -/
def writesFrom (g : StoresGhost) (k : Nat) : List (List (BitVec 8) × List (BitVec 8)) :=
  ((storesDirs g).drop k).flatMap DirGhost.writes

@[simp]
theorem writesBefore_zero (g : StoresGhost) : writesBefore g 0 = [] := rfl

@[simp]
theorem writesFrom_eight (g : StoresGhost) : writesFrom g 8 = [] := rfl

theorem storesDirs_writes (g : StoresGhost) :
    (storesDirs g).flatMap DirGhost.writes = g.writes := by
  simp only [storesDirs, StoresGhost.writes, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc]

@[simp]
theorem writesFrom_zero (g : StoresGhost) : writesFrom g 0 = g.writes :=
  storesDirs_writes g

@[simp]
theorem writesBefore_eight (g : StoresGhost) : writesBefore g 8 = g.writes := by
  change ((storesDirs g).take 8).flatMap DirGhost.writes = g.writes
  have htake : (storesDirs g).take 8 = storesDirs g :=
    List.take_of_length_le (by simp [storesDirs_length])
  rw [htake]
  exact storesDirs_writes g

theorem flatMap_append_eq {α β : Type} (f : α → List β) (xs ys : List α) :
    (xs ++ ys).flatMap f = xs.flatMap f ++ ys.flatMap f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, List.flatMap_cons, ih, List.append_assoc]

theorem writes_eq_writesBefore_append_writesFrom (g : StoresGhost) (k : Nat) :
    g.writes = writesBefore g k ++ writesFrom g k := by
  rw [← storesDirs_writes g]
  conv_lhs => rw [← List.take_append_drop k (storesDirs g)]
  exact flatMap_append_eq DirGhost.writes _ _

theorem take_succ_eq_append_getElem {α : Type} (xs : List α) {k : Nat} (hk : k < xs.length) :
    xs.take (k + 1) = xs.take k ++ [xs[k]] := by
  induction xs generalizing k with
  | nil => cases hk
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [List.length_cons] at hk
      simp only [List.take_succ_cons, List.getElem_cons_succ, List.cons_append]
      exact congrArg (x :: ·) (ih (by omega))

theorem drop_eq_getElem_cons_drop_succ {α : Type} (xs : List α) {k : Nat} (hk : k < xs.length) :
    xs.drop k = xs[k] :: xs.drop (k + 1) := by
  induction xs generalizing k with
  | nil => cases hk
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [List.length_cons] at hk
      simp only [List.drop_succ_cons, List.getElem_cons_succ]
      exact ih (by omega)

theorem writesBefore_succ {g : StoresGhost} {k : Nat} (hk : k < 8) :
    writesBefore g (k + 1) =
      writesBefore g k ++ ((storesDirs g)[k]'(by simp [hk])).writes := by
  have hlen : k < (storesDirs g).length := by simp [hk]
  unfold writesBefore
  rw [take_succ_eq_append_getElem (storesDirs g) hlen, flatMap_append_eq]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rfl

theorem writesFrom_eq_cons {g : StoresGhost} {k : Nat} (hk : k < 8) :
    writesFrom g k =
      ((storesDirs g)[k]'(by simp [hk])).writes ++ writesFrom g (k + 1) := by
  have hlen : k < (storesDirs g).length := by simp [hk]
  unfold writesFrom
  rw [drop_eq_getElem_cons_drop_succ (storesDirs g) hlen]
  rfl

theorem mem_writes_of_dir_entry {g : StoresGhost} {k : Nat} (hk : k < 8)
    {e : List (BitVec 8) × List (BitVec 8)}
    (he : e ∈ ((storesDirs g)[k]'(by simp [hk])).changed) :
    (pathOf ((storesDirs g)[k]'(by simp [hk])).path e.1, e.2) ∈ g.writes := by
  rw [writes_eq_writesBefore_append_writesFrom g k, writesFrom_eq_cons hk]
  apply List.mem_append_right
  apply List.mem_append_left
  unfold DirGhost.writes
  exact List.mem_map_of_mem he

@[simp]
theorem commitFiles_nil (wr : WriteRule) (F : FsFiles) :
    commitFiles wr F [] = some F := rfl

theorem commitFiles_cons (wr : WriteRule) (F : FsFiles)
    (pw : List (BitVec 8) × List (BitVec 8))
    (ws : List (List (BitVec 8) × List (BitVec 8))) :
    commitFiles wr F (pw :: ws) =
      (wr F pw.1 pw.2).bind (fun F' => commitFiles wr F' ws) := by
  rcases pw with ⟨p, bs⟩
  cases h : wr F p bs <;> simp [commitFiles, h]

theorem commitFiles_append (wr : WriteRule) (F : FsFiles)
    (xs ys : List (List (BitVec 8) × List (BitVec 8))) :
    commitFiles wr F (xs ++ ys) =
      (commitFiles wr F xs).bind (fun F' => commitFiles wr F' ys) := by
  induction xs generalizing F with
  | nil => rfl
  | cons pw xs ih =>
    rcases pw with ⟨p, bs⟩
    simp only [List.cons_append, commitFiles]
    cases wr F p bs with
    | none => rfl
    | some F' => exact ih F'

theorem commitFiles_step_ok {wr : WriteRule} {F0 F F' : FsFiles}
    {xs : List (List (BitVec 8) × List (BitVec 8))}
    {pw : List (BitVec 8) × List (BitVec 8)}
    (h1 : commitFiles wr F0 xs = some F)
    (h2 : wr F pw.1 pw.2 = some F') :
    commitFiles wr F0 (xs ++ [pw]) = some F' := by
  rw [commitFiles_append, h1]
  change commitFiles wr F [pw] = some F'
  rw [commitFiles_cons, h2]
  rfl

theorem commitFiles_step_err {wr : WriteRule} {F0 F : FsFiles}
    {xs ys : List (List (BitVec 8) × List (BitVec 8))}
    {pw : List (BitVec 8) × List (BitVec 8)}
    (h1 : commitFiles wr F0 xs = some F)
    (h2 : wr F pw.1 pw.2 = none) :
    commitFiles wr F0 (xs ++ pw :: ys) = none := by
  rw [commitFiles_append, h1]
  change commitFiles wr F (pw :: ys) = none
  rw [commitFiles_cons, h2]
  rfl

private theorem mem_of_mem_drop {α : Type} {x : α} {xs : List α} :
    ∀ {n : Nat}, x ∈ xs.drop n → x ∈ xs
  | 0, h => h
  | _ + 1, h => by
    cases xs with
    | nil => simp at h
    | cons _ xs => exact .tail _ (mem_of_mem_drop h)

/-- Propagate `allocFailedIn s1 sf` backward to `s0` whenever `s0.trace.length ≤ s1.trace.length`
(in particular whenever `s0.trace = []` or `s0.trace <+: s1.trace`). -/
theorem allocFailedIn_mono_left {s0 s1 sf : State}
    (hle : s0.trace.length ≤ s1.trace.length)
    (ha : allocFailedIn s1 sf) :
    allocFailedIn s0 sf := by
  unfold allocFailedIn at ha ⊢
  have heq : s1.trace.length = s0.trace.length + (s1.trace.length - s0.trace.length) := by omega
  rw [heq, ← List.drop_drop] at ha
  exact mem_of_mem_drop ha

/-- Propagate `allocFailedIn` forward along a trace prefix. -/
theorem allocFailedIn_of_prefix {s0 s1 s2 : State}
    (ha : allocFailedIn s0 s1) (hp : s1.trace <+: s2.trace) :
    allocFailedIn s0 s2 := by
  unfold allocFailedIn at ha ⊢
  rcases hp with ⟨extTr, htr2⟩
  rw [← htr2]
  have hle : s0.trace.length ≤ s1.trace.length := by
    by_contra hgt
    rw [List.drop_of_length_le (by omega)] at ha
    cases ha
  rw [List.drop_append_of_le_length hle]
  exact List.mem_append_left extTr ha

/-! ## 2. Spatial `Dir` Tail Predicates and `locals` Frames -/

/-- Contiguous array of `Dir` structs (`40 = 0x28` bytes each) starting at `a`. -/
def dirsAt (A : RustAlloc) (a : BitVec 64) : List DirGhost → SepProp
  | [] => emp
  | d :: ds => dirAt A a d ∗ dirsAt A (a + 0x28#64) ds

@[simp]
theorem dirsAt_nil (A : RustAlloc) (a : BitVec 64) :
    dirsAt A a [] = emp := rfl

@[simp]
theorem dirsAt_cons (A : RustAlloc) (a : BitVec 64) (d : DirGhost) (ds : List DirGhost) :
    dirsAt A a (d :: ds) = dirAt A a d ∗ dirsAt A (a + 0x28#64) ds := rfl

theorem dirsAt_storesDirs (A : RustAlloc) (a : BitVec 64) (g : StoresGhost) :
    dirsAt A a (storesDirs g) = storesAt A a g := by
  simp only [storesDirs, dirsAt, storesAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]

theorem dirsAt_drop_cons (A : RustAlloc) (fsp : BitVec 64) (g : StoresGhost)
    {k : Nat} (hk : k < 8) :
    dirsAt A (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * k)) ((storesDirs g).drop k) =
      dirAt A (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * k))
        ((storesDirs g)[k]'(by simp [hk])) ∗
        dirsAt A (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1)))
          ((storesDirs g).drop (k + 1)) := by
  have hlen : k < (storesDirs g).length := by simp [hk]
  rw [drop_eq_getElem_cons_drop_succ (storesDirs g) hlen, dirsAt_cons]
  have hnum : 0x1c8 + 0x28 * k + 0x28 = 0x1c8 + 0x28 * (k + 1) := by omega
  have haddr :
      fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * k) + 0x28#64 =
        fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hnum]
  rw [haddr]
  rfl

/-- Owned pieces inside `locals fsp` at `AtM5Loop` after `k` `Dir`s (`k ≤ 8`):
`m6Cells` (`0x08 .. 0x28`, `0x58 .. 0x60`) plus the remaining `8 - k` `Dir`s at
`0x1c8 + 0x28 * k .. 0x308`. -/
def m5LoopCells (A : RustAlloc) (fsp outCap outPtr outLen inCap inPtr : BitVec 64)
    (g : StoresGhost) (k : Nat) : List (Nat × Nat × SepProp) :=
  m6Cells fsp outCap outPtr outLen inCap inPtr ++
    [(0x1c8 + 0x28 * k, 0x28 * (8 - k),
      dirsAt A (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * k)) ((storesDirs g).drop k))]

theorem m5LoopCells_zero_eq (A : RustAlloc) (fsp outCap outPtr outLen inCap inPtr : BitVec 64)
    (g : StoresGhost) :
    m5LoopCells A fsp outCap outPtr outLen inCap inPtr g 0 =
      m6Cells fsp outCap outPtr outLen inCap inPtr ++
        [(0x1c8, 0x140, storesAt A (fsp + 0x1c8#64) g)] := by
  simp only [m5LoopCells, Nat.mul_zero, Nat.add_zero, Nat.sub_zero, List.drop_zero,
    dirsAt_storesDirs]

theorem locals_m5LoopCells_eight (A : RustAlloc)
    (fsp outCap outPtr outLen inCap inPtr : BitVec 64) (g : StoresGhost) :
    locals fsp (m5LoopCells A fsp outCap outPtr outLen inCap inPtr g 8) =
      locals fsp (m6Cells fsp outCap outPtr outLen inCap inPtr) := by
  have h8 : (storesDirs g).drop 8 = [] :=
    List.drop_of_length_le (by simp [storesDirs_length])
  have hcarve := locals_carve_region fsp
    (m6Cells fsp outCap outPtr outLen inCap inPtr) 0x308 0 []
    (by simp [localsEnd]) (by simp [localsBound]) (by simp [localsBound])
  simp only [List.append_nil] at hcarve
  rw [hcarve]
  unfold m5LoopCells
  simp only [h8, dirsAt_nil, Nat.sub_self, Nat.mul_zero, memRegion_zero]

/-- Advance `locals fsp` from `k` to `k + 1` once `Dir k`'s 40-byte stack header has become
`memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * k)) 0x28`. -/
theorem locals_m5LoopCells_step (A : RustAlloc)
    (fsp outCap outPtr outLen inCap inPtr : BitVec 64) (g : StoresGhost)
    {k : Nat} (hk : k < 8) :
    locals fsp
      (m6Cells fsp outCap outPtr outLen inCap inPtr ++
        [(0x1c8 + 0x28 * k, 0x28 * (8 - k),
          memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * k)) 0x28 ∗
            dirsAt A (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1)))
              ((storesDirs g).drop (k + 1)))]) =
      locals fsp (m5LoopCells A fsp outCap outPtr outLen inCap inPtr g (k + 1)) := by
  have hcarve := locals_carve_region fsp
    (m6Cells fsp outCap outPtr outLen inCap inPtr)
    (0x1c8 + 0x28 * k) 0x28
    [(0x1c8 + 0x28 * (k + 1), 0x28 * (8 - (k + 1)),
      dirsAt A (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1))) ((storesDirs g).drop (k + 1)))]
    (by simp [localsEnd]; omega)
    (by simp [localsBound]; omega)
    (by simp [localsBound]; omega)
  unfold m5LoopCells at hcarve ⊢
  rw [hcarve]
  have hsub0 : 0x1c8 + 0x28 * (k + 1) - (0x1c8 + 0x28 * k + 0x28) = 0 := by omega
  have hend :
      0x1c8 + 0x28 * (k + 1) + 0x28 * (8 - (k + 1)) =
        0x1c8 + 0x28 * k + 0x28 * (8 - k) := by omega
  simp only [m6Cells, locals, localsFrom, List.cons_append, List.nil_append,
    Nat.sub_self, hsub0, hend, memRegion_zero]
  ac_rfl

/-- Full separation-logic memory at `AtM5Loop` after `k` `Dir`s (`k ≤ 8`). -/
def m5LoopMem (A : RustAlloc) (s0 : State) (stk n : Nat)
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
      (m5LoopCells A fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k) ∗
    stackAt fsp (stk - mainFrameSize) ∗
    A.pool ∗ anyHeap

/-! ## 3. Loop Invariant `AtM5Loop` (`M+0x824` for `k < 8`, `M+0xa48` for `k = 8`) -/

/-- State invariant of `main`'s M5 commit loop after `k` `Dir`s (`k ≤ 8`):
- For `k < 8`: `pc = M+0x824` (outer loop header);
- For `k = 8`: `pc = M+0xa48` (`0xa40: cmp x22, #8; b.ne 0x824` falls through directly to `M+0xa48`
  when `Dir 7` finishes with `x22 = 8`);
- `x19 = buf`, `x22 = k`, `x23 = fsp + 0x1c8`, `x24 = n`, `x28 = 40` (`0x28`);
- `commitFiles io.wr F0 (writesBefore g k) = some s.fs.files`, `tr0 <+: s.trace`, and `stdout`
  bytes unchanged from `tr0`. -/
structure AtM5Loop (img : Obj.Image) (ext : String → Option (State → State))
    (io : IoModel) (F0 : FsFiles) (tr0 : List TraceEvent)
    (g : StoresGhost) (s0 s : State) (n : Nat) (buf : BitVec 64) (k : Nat) : Prop where
  hk : k ≤ 8
  base : InMain img ext s0 s (if k < 8 then 0x824 else 0xa48)
  x19 : s.readReg64 (.gpr 19#5) = buf
  x22 : s.readReg64 (.gpr 22#5) = BitVec.ofNat 64 k
  x23 : s.readReg64 (.gpr 23#5) = s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64
  x24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n
  x28 : s.readReg64 (.gpr 28#5) = 0x28#64
  files : commitFiles io.wr F0 (writesBefore g k) = some s.fs.files
  trace : tr0 <+: s.trace
  stdout : ProcessOutcome.traceStreamBytes .stdout s.trace =
    ProcessOutcome.traceStreamBytes .stdout tr0

/-- Constructor at `k = 0` after `m5_moves`, when `s'.fs = s.fs` and `s'.trace = s.trace`. -/
theorem AtM5Loop.of_zero {img : Obj.Image} {ext : String → Option (State → State)}
    {io : IoModel} {g : StoresGhost} {s0 s s' : State} {n : Nat} {buf : BitVec 64}
    (hbase : InMain img ext s0 s' 0x824)
    (hx19 : s'.readReg64 (.gpr 19#5) = buf)
    (hx22 : s'.readReg64 (.gpr 22#5) = 0#64)
    (hx23 : s'.readReg64 (.gpr 23#5) = s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64)
    (hx24 : s'.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx28 : s'.readReg64 (.gpr 28#5) = 0x28#64)
    (hfs : s'.fs.files = s.fs.files)
    (htr : s'.trace = s.trace) :
    AtM5Loop img ext io s.fs.files s.trace g s0 s' n buf 0 where
  hk := by decide
  base := hbase
  x19 := hx19
  x22 := hx22
  x23 := hx23
  x24 := hx24
  x28 := hx28
  files := by simp [writesBefore_zero, commitFiles_nil, hfs]
  trace := htr ▸ List.prefix_refl _
  stdout := by rw [htr]

/-! ## 4. Write-Error Exit Interface `M5LoopErr` (`M+0xb90` / `M+0xba0` / `M+0xbb8`) -/

/-- Which of the three `write_file` error exits in `main` was entered on `Err`. -/
inductive M5ErrEntry where
  /-- `M+0xb90` (Loop A, non-empty `Dir.path`): temporary `String` in `(x23 = pathCap, x22 = pathPtr)`. -/
  | b90 (pathCap pathPtr : BitVec 64) (pathBs : List (BitVec 8))
  /-- `M+0xba0` (Loop B, empty `Dir.path`, non-empty `name`): temporary `String` in
  `(x23 = pathCap ≠ 0, x22 = pathPtr)`. -/
  | ba0 (pathCap pathPtr : BitVec 64) (pathBs : List (BitVec 8))
  /-- `M+0xbb8` (Loop B, empty `Dir.path`, empty `name`): nothing temporary to free. -/
  | bb8

/-- `main`-relative byte offset of an `M5ErrEntry`. -/
def M5ErrEntry.pcOff : M5ErrEntry → Nat
  | .b90 .. => 0xb90
  | .ba0 .. => 0xba0
  | .bb8 => 0xbb8

/-- Entry register facts for `M5ErrEntry` (`x22 = ptr`, `x23 = cap`, plus `cap ≠ 0` at `0xba0`). -/
def M5ErrEntry.regs : M5ErrEntry → State → Prop
  | .b90 cap ptr _, s => s.readReg64 (.gpr 22#5) = ptr ∧ s.readReg64 (.gpr 23#5) = cap
  | .ba0 cap ptr _, s => s.readReg64 (.gpr 22#5) = ptr ∧ s.readReg64 (.gpr 23#5) = cap ∧ cap ≠ 0#64
  | .bb8, _ => True

/-- Heap ownership of the temporary path `String` (if any) at `M5ErrEntry`. -/
def M5ErrEntry.heap (A : RustAlloc) : M5ErrEntry → SepProp
  | .b90 cap ptr bs => ownedBytes A cap ptr (BitVec.ofNat 64 bs.length) bs
  | .ba0 cap ptr bs => ownedBytes A cap ptr (BitVec.ofNat 64 bs.length) bs
  | .bb8 => emp

/-- Owned pieces inside `locals fsp` at `M5LoopErr` (`k < 8`):
`m6Cells` plus loop spills `0x28` (`curPtr`), `0x30` (`fsp + 0x1c8`), `0x38` (`k + 1`),
`0x48` (`curCap`), and remaining `Dir`s `k + 1 .. 7` at `0x1c8 + 0x28 * (k + 1) .. 0x308`.
Note that `0x1b8 .. 0x1c0` sits cleanly inside the uninitialized `memRegion` gap
`0x60 .. 0x1c8 + 0x28 * (k + 1)` for every `k`. -/
def m5ErrCells (A : RustAlloc) (fsp outCap outPtr outLen inCap inPtr curCap curPtr : BitVec 64)
    (g : StoresGhost) (k : Nat) : List (Nat × Nat × SepProp) :=
  [cell fsp 0x8 outLen,
   cell fsp 0x10 outPtr,
   cell fsp 0x18 outCap,
   cell fsp 0x20 inCap,
   cell fsp 0x28 curPtr,
   cell fsp 0x30 (fsp + 0x1c8#64),
   cell fsp 0x38 (BitVec.ofNat 64 (k + 1)),
   cell fsp 0x48 curCap,
   cell fsp 0x58 inPtr,
   (0x1c8 + 0x28 * (k + 1), 0x28 * (8 - (k + 1)),
     dirsAt A (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1))) ((storesDirs g).drop (k + 1)))]

/-- Collapse the loop spills `0x28`, `0x30`, `0x38`, `0x48` and an empty/freed tail `memRegion`
at `0x1c8 + 0x28 * m` (`m ≤ 8`) back into `locals fsp (m6Cells …)`. -/
theorem locals_m5ErrCells_forget_to_m6Cells
    (fsp outCap outPtr outLen inCap inPtr v28 v30 v38 v48 : BitVec 64)
    {m : Nat} (hm : m ≤ 8) :
    locals fsp
      [cell fsp 0x8 outLen,
       cell fsp 0x10 outPtr,
       cell fsp 0x18 outCap,
       cell fsp 0x20 inCap,
       cell fsp 0x28 v28,
       cell fsp 0x30 v30,
       cell fsp 0x38 v38,
       cell fsp 0x48 v48,
       cell fsp 0x58 inPtr,
       (0x1c8 + 0x28 * m, 0x28 * (8 - m),
         memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * m)) (0x28 * (8 - m)))] ⊢
      locals fsp (m6Cells fsp outCap outPtr outLen inCap inPtr) := by
  have h1 := locals_forget_cell fsp
    [cell fsp 0x8 outLen, cell fsp 0x10 outPtr, cell fsp 0x18 outCap, cell fsp 0x20 inCap]
    0x28 v28
    [cell fsp 0x30 v30, cell fsp 0x38 v38, cell fsp 0x48 v48, cell fsp 0x58 inPtr,
     (0x1c8 + 0x28 * m, 0x28 * (8 - m),
       memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * m)) (0x28 * (8 - m)))]
    (by simp [localsEnd]) (by simp [localsBound]) (by simp [localsBound])
  have h2 := locals_forget_cell fsp
    [cell fsp 0x8 outLen, cell fsp 0x10 outPtr, cell fsp 0x18 outCap, cell fsp 0x20 inCap]
    0x30 v30
    [cell fsp 0x38 v38, cell fsp 0x48 v48, cell fsp 0x58 inPtr,
     (0x1c8 + 0x28 * m, 0x28 * (8 - m),
       memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * m)) (0x28 * (8 - m)))]
    (by simp [localsEnd]) (by simp [localsBound]) (by simp [localsBound])
  have h3 := locals_forget_cell fsp
    [cell fsp 0x8 outLen, cell fsp 0x10 outPtr, cell fsp 0x18 outCap, cell fsp 0x20 inCap]
    0x38 v38
    [cell fsp 0x48 v48, cell fsp 0x58 inPtr,
     (0x1c8 + 0x28 * m, 0x28 * (8 - m),
       memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * m)) (0x28 * (8 - m)))]
    (by simp [localsEnd]) (by simp [localsBound]) (by simp [localsBound])
  have h4 := locals_forget_cell fsp
    [cell fsp 0x8 outLen, cell fsp 0x10 outPtr, cell fsp 0x18 outCap, cell fsp 0x20 inCap]
    0x48 v48
    [cell fsp 0x58 inPtr,
     (0x1c8 + 0x28 * m, 0x28 * (8 - m),
       memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * m)) (0x28 * (8 - m)))]
    (by simp [localsEnd]) (by simp [localsBound]) (by simp [localsBound])
  have h5 := (locals_carve_region fsp
    (m6Cells fsp outCap outPtr outLen inCap inPtr)
    (0x1c8 + 0x28 * m) (0x28 * (8 - m)) []
    (by simp [localsEnd]; omega)
    (by simp [localsBound]; omega)
    (by simp [localsBound])).symm
  exact Entails.trans h1 (Entails.trans h2 (Entails.trans h3 (Entails.trans h4 (Entails.of_eq h5))))

/-- Full separation-logic memory at `M5LoopErr` (`M+0xb90` / `M+0xba0` / `M+0xbb8`). -/
def m5ErrMem (A : RustAlloc) (s0 : State) (stk n : Nat)
    (outCap outPtr inCap inPtr buf curCap curPtr : BitVec 64)
    (out inp : List (BitVec 8))
    (ps : List (BitVec 64 × List (BitVec 8)))
    (g : StoresGhost) (k : Nat)
    (curEntries : List (List (BitVec 8) × List (BitVec 8)))
    (e : M5ErrEntry) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  e.heap A ∗
    vecBuf A 48 8 (dirEntryAt A) curCap curPtr curEntries ∗
    ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
    ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
    argsBuf A (BitVec.ofNat 64 n) buf ps ∗
    mainSaved s0 ∗
    locals fsp
      (m5ErrCells A fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr curCap curPtr g k) ∗
    stackAt fsp (stk - mainFrameSize) ∗
    A.pool ∗ anyHeap

/-- Error-exit state at `M+0xb90` / `M+0xba0` / `M+0xbb8` when a `write_file` call in `Dir k`
(`k < 8`) returned `Err`:
- `curEntries ≠ []` with `x25 = curEntries.length` (the counter consumed by `M+0xbcc`);
- `x19 = buf`, `x24 = n`, and `e.regs s` (`x22 = pathPtr`, `x23 = pathCap`);
- `commitFiles io.wr F0 g.writes = none`, `tr0 <+: s.trace`, and `stdout` unchanged from `tr0`. -/
structure M5LoopErr (img : Obj.Image) (ext : String → Option (State → State))
    (io : IoModel) (F0 : FsFiles) (tr0 : List TraceEvent)
    (g : StoresGhost) (s0 s : State) (n : Nat) (buf : BitVec 64)
    (k : Nat) (curEntries : List (List (BitVec 8) × List (BitVec 8)))
    (e : M5ErrEntry) : Prop where
  hk : k < 8
  hne : curEntries ≠ []
  errRegs : e.regs s
  base : InMain img ext s0 s e.pcOff
  x19 : s.readReg64 (.gpr 19#5) = buf
  x24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n
  x25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 curEntries.length
  commitNone : commitFiles io.wr F0 g.writes = none
  trace : tr0 <+: s.trace
  stdout : ProcessOutcome.traceStreamBytes .stdout s.trace =
    ProcessOutcome.traceStreamBytes .stdout tr0

end CryptoVerification.SignalSession.Cli.MainHops
