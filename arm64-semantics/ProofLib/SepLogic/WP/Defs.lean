/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.SimpAttrs
public import ProofLib.PrologueFrame
public import ProofLib.SepLogic.Defs
public import ProofLib.Hoare.SubroutineOk
import Arm64.Trusted.Spec.SepLogic

/-!
# Weakest-Precondition Definitions

Defines the total-correctness separation-logic weakest precondition `SepWP`, its panic-aware
counterpart `SepWPp`, the spatial load/store/frame witness predicates (`SepLoad*`, `SepStore*`,
`SepFrame`), and `applyWriteback`.
-/

@[expose] public section

namespace ProofLib

open Arm64

-- Re-export the trusted separation-logic vocabulary (`Arm64/Trusted/Spec/SepLogic.lean`) and
-- region predicates into `ProofLib` so `ProofLib.*` callers can use them unqualified.
export Arm64 (
  HeapCell
  Heap
  SepProp
  Satisfies Entails emp sepConj sepImp sepExists complementSep
  pointsTo8 pointsToBytes pointsTo16 pointsTo32 pointsTo64 pointsTo128 pointsToWords64
  pointsTo8RO pointsToBytesRO pointsTo16RO pointsTo32RO pointsTo64RO pointsTo128RO pointsToWords64RO
  pointsTo8ProtNone pointsToBytesProtNone
  pointsTo8Lazy pointsTo16Lazy pointsTo32Lazy pointsTo64Lazy pointsTo128Lazy
  regionHeap regionHeapRO regionHeapProtNone regionHeapLazy mappedHeap
  regionBlock regionBlockRO regionBlockProtNone
  memRegion memRegionProtNone memRegionLazy memLazy memMapped memRO
  stackFrame stackFrame16At stackFrame16 stackFrame32At stackFrame32
  stackFrameSlotsCont stackFrameSlotsFrom stackFrameAt HasFnFrameBytes fnFrameBytes stackFrameFor
)

export Arm64 (InRegion instDecidableInRegion OutsideRegion DisjointRegions StackPreserved)

/-- Apply optional address-mode base register writeback `wb` to state `s`. -/
@[simp, arm64_norm]
def applyWriteback (s : State) (wb : Option (Reg × BitVec 64)) : State :=
  match wb with
  | some (base, newBase) => s.writeReg64 base newBase
  | none => s

/-- Separation-logic weakest precondition (`SepWP`) for total-correctness ARM64 forward symbolic
    execution with built-in framing:
    Starting from machine state `s` and spatial context `P`, for any frame assertion `R : SepProp`
    such that `s.mem ⊨ P ∗ R`, execution of `prog` reaches `target_pc` in a `.Running` state `sf`
    with an updated spatial context `P_f` such that `sf.mem ⊨ P_f ∗ R` and `post sf P_f` holds,
    or terminates in `.OutOfMemory` with `sf.mem ⊨ oom sf ∗ R` (defaulting to `oom = fun _ => ⌜False⌝`). -/
def SepWP (prog : Program) (target_pc : BitVec 64) (s : State) (P : SepProp)
    (post : State → SepProp → Prop) (oom : State → SepProp := fun _ => ⌜False⌝) : Prop :=
  ∀ R : SepProp, (s.mem ⊨ P ∗ R) →
    reaches_pc prog target_pc s
      (fun sf => ∃ P_f : SepProp, (sf.mem ⊨ P_f ∗ R) ∧ post sf P_f)
      (fun sf => sf.mem ⊨ oom sf ∗ R)

/-- Panic-aware `SepWP`: reach `ret` in `.Running` status with `Q`, reach a `.Panicked`
    state with `Qp` (preserving any frame `R`), or terminate in `.OutOfMemory` with
    `sf.mem ⊨ oom sf ∗ R` (defaulting to `oom = fun _ => ⌜False⌝`). -/
def SepWPp (prog : Program) (ret : BitVec 64) (s : State) (P : SepProp)
    (Q Qp : State → SepProp → Prop) (oom : State → SepProp := fun _ => ⌜False⌝) : Prop :=
  ∀ R : SepProp, (s.mem ⊨ P ∗ R) → prog.CodeLoaded s.mem →
    ∃ sf, Steps prog s sf ∧
      ((sf.pc = ret ∧ sf.status = .Running ∧ ∃ P_f, (sf.mem ⊨ P_f ∗ R) ∧ Q sf P_f) ∨
       (sf.status = .Panicked ∧ ∃ P_f, (sf.mem ⊨ P_f ∗ R) ∧ Qp sf P_f) ∨
       (sf.status = .OutOfMemory ∧ (sf.mem ⊨ oom sf ∗ R)))

/-- Witness that spatial context `P` owns the 8-bit cell at `a` with value `v`. -/
structure SepLoad8 (a : BitVec 64) (P : SepProp) (v : BitVec 8) : Prop where
  load : ∀ {m : Memory} {R : SepProp}, (m ⊨ P ∗ R) → m.read8 a = v
  readable : ∀ {m : Memory} {R : SepProp}, (m ⊨ P ∗ R) → m.canRead a 1 = true

/-- Witness that spatial context `P` owns the 16-bit cell at `a` with value `v`. -/
structure SepLoad16 (a : BitVec 64) (P : SepProp) (v : BitVec 16) : Prop where
  load : ∀ {m : Memory} {R : SepProp}, (m ⊨ P ∗ R) → m.read16 a = v
  readable : ∀ {m : Memory} {R : SepProp}, (m ⊨ P ∗ R) → m.canRead a 2 = true

/-- Witness that spatial context `P` owns the 32-bit cell at `a` with value `v`. -/
structure SepLoad32 (a : BitVec 64) (P : SepProp) (v : BitVec 32) : Prop where
  load : ∀ {m : Memory} {R : SepProp}, (m ⊨ P ∗ R) → m.read32 a = v
  readable : ∀ {m : Memory} {R : SepProp}, (m ⊨ P ∗ R) → m.canRead a 4 = true

/-- Witness that spatial context `P` owns the 64-bit cell at `a` with value `v`. -/
structure SepLoad64 (a : BitVec 64) (P : SepProp) (v : BitVec 64) : Prop where
  load : ∀ {m : Memory} {R : SepProp}, (m ⊨ P ∗ R) → m.read64 a = v
  readable : ∀ {m : Memory} {R : SepProp}, (m ⊨ P ∗ R) → m.canRead a 8 = true

/-- Witness that storing `v'` to the 8-bit cell at `a` updates `P` to `P'`. -/
structure SepStore8 (a : BitVec 64) (v' : BitVec 8) (P : SepProp) (P' : SepProp) : Prop where
  store : ∀ {m : Memory} {R : SepProp}, (m ⊨ P ∗ R) → ((m.write8 a v') ⊨ P' ∗ R)
  writable : ∀ {m : Memory} {R : SepProp}, (m ⊨ P ∗ R) → m.canWrite a 1 = true

/-- Witness that storing `v'` to the 16-bit cell at `a` updates `P` to `P'`. -/
structure SepStore16 (a : BitVec 64) (v' : BitVec 16) (P : SepProp) (P' : SepProp) : Prop where
  store : ∀ {m : Memory} {R : SepProp}, (m ⊨ P ∗ R) → ((m.write16 a v') ⊨ P' ∗ R)
  writable : ∀ {m : Memory} {R : SepProp}, (m ⊨ P ∗ R) → m.canWrite a 2 = true

/-- Witness that storing `v'` to the 32-bit cell at `a` updates `P` to `P'`. -/
structure SepStore32 (a : BitVec 64) (v' : BitVec 32) (P : SepProp) (P' : SepProp) : Prop where
  store : ∀ {m : Memory} {R : SepProp}, (m ⊨ P ∗ R) → ((m.write32 a v') ⊨ P' ∗ R)
  writable : ∀ {m : Memory} {R : SepProp}, (m ⊨ P ∗ R) → m.canWrite a 4 = true

/-- Witness that storing `v'` to the 64-bit cell at `a` updates `P` to `P'`. -/
structure SepStore64 (a : BitVec 64) (v' : BitVec 64) (P : SepProp) (P' : SepProp) : Prop where
  store : ∀ {m : Memory} {R : SepProp}, (m ⊨ P ∗ R) → ((m.write64 a v') ⊨ P' ∗ R)
  writable : ∀ {m : Memory} {R : SepProp}, (m ⊨ P ∗ R) → m.canWrite a 8 = true

/-- Witness decomposing `Full` into `Sub ∗ Frame`. -/
structure SepFrame (Sub : SepProp) (Full : SepProp) (Frame : SepProp) : Prop where
  eq : Full = Sub ∗ Frame

end ProofLib
