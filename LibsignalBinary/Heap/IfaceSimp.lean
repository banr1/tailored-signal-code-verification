/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.StdStartup.NonVmSteps
public import ProofLib.Hoare.LibcHooks
public import LibsignalBinary.Heap.Iface
import LibsignalBinary.Heap.IfaceLemmas

/-!
# Simp Lemmas, OOM Combinators, and Extern Leaf Wrappers for `Iface`

`@[simp, arm64_norm, wp_norm]` state-projection and two-sided preservation rules (`OomPreserved`,
`AllocCallPreserved`, `PoolPreserved`, `RustCliAlloc.pool`), OOM-polymorphic `SepWP`/`SepWPp` and
`ReachesOrPanicOom` composition lemmas, and `OomPreserved ∧ PoolPreserved` extern-hook wrappers.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Heap.IfaceSimp

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap (PoolPreserved AllocCallPreserved OomPreserved
  RustLayoutOk NullAllowed RustCliAlloc rustCliAllocSpec rustCliDeallocSpec
  rustCliReallocSpec RustCliAllocHooks RustAllocAddrs RustCliAllocEntries)

/-! ## `State` Field Projections -/

/-! ### `State.fs` -/

@[simp, arm64_norm, wp_norm] theorem fs_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by cases s; cases w <;> cases r <;> rfl
@[simp, arm64_norm, wp_norm] theorem fs_writeVReg64 (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 i v).fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem fs_writeVReg32 (s : State) (i : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 i v).fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem fs_setFpsr (s : State) (f : BitVec 32) :
    (s.setFpsr f).fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem fs_orFpsr (s : State) (f : BitVec 32) :
    (s.orFpsr f).fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem fs_setTpidrEl0 (s : State) (v : BitVec 64) :
    (setTpidrEl0 s v).fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem fs_panicked (s : State) :
    (Rust.panicked s).fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem fs_applyWriteback (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).fs = s.fs := by cases wb <;> simp [applyWriteback]

@[wp_norm] theorem fs_setFs_wp (s : State) (f : FsState) : (s.setFs f).fs = f :=
  State.fs_setFs s f
@[wp_norm] theorem fs_writeReg64_wp (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).fs = s.fs := State.fs_writeReg64 s r v
@[wp_norm] theorem fs_writeReg32_wp (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).fs = s.fs := State.fs_writeReg32 s r v
@[wp_norm] theorem fs_writeVReg128_wp (s : State) (i : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).fs = s.fs := State.fs_writeVReg128 s i v
@[wp_norm] theorem fs_advancePC_wp (s : State) : s.advancePC.fs = s.fs := State.fs_advancePC s
@[wp_norm] theorem fs_setPC_wp (s : State) (p : BitVec 64) : (s.setPC p).fs = s.fs :=
  State.fs_setPC s p
@[wp_norm] theorem fs_setPState_wp (s : State) (ps : PState) : (s.setPState ps).fs = s.fs :=
  State.fs_setPState s ps
@[wp_norm] theorem fs_setMem_wp (s : State) (m : Memory) : (s.setMem m).fs = s.fs :=
  State.fs_setMem s m
@[wp_norm] theorem fs_setStatus_wp (s : State) (st : ExecStatus) : (s.setStatus st).fs = s.fs :=
  State.fs_setStatus s st
@[wp_norm] theorem fs_setBrk_wp (s : State) (b : BitVec 64) : (s.setBrk b).fs = s.fs :=
  State.fs_setBrk s b
@[wp_norm] theorem fs_nextOracle_wp (s : State) : s.nextOracle.fs = s.fs := State.fs_nextOracle s
@[wp_norm] theorem fs_appendTrace_wp (s : State) (e : List TraceEvent) :
    (s.appendTrace e).fs = s.fs := State.fs_appendTrace s e
@[wp_norm] theorem fs_stepExclOracle_wp (s : State) : s.stepExclOracle.fs = s.fs :=
  State.fs_stepExclOracle s
@[wp_norm] theorem fs_stepExclLoop_wp (s : State) : s.stepExclLoop.fs = s.fs :=
  State.fs_stepExclLoop s
@[wp_norm] theorem fs_setPhysMemAvail_wp (s : State) (n : Nat) :
    (s.setPhysMemAvail n).fs = s.fs := State.fs_setPhysMemAvail s n

/-! ### `State.sigActions` -/

@[simp, arm64_norm, wp_norm] theorem sigActions_writeVReg128 (s : State) (i : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem sigActions_writeVReg64 (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 i v).sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem sigActions_writeVReg32 (s : State) (i : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 i v).sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem sigActions_setFpsr (s : State) (f : BitVec 32) :
    (s.setFpsr f).sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem sigActions_orFpsr (s : State) (f : BitVec 32) :
    (s.orFpsr f).sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem sigActions_setStatus (s : State) (st : ExecStatus) :
    (s.setStatus st).sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem sigActions_setBrk (s : State) (b : BitVec 64) :
    (s.setBrk b).sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem sigActions_setPhysMemAvail (s : State) (n : Nat) :
    (s.setPhysMemAvail n).sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem sigActions_stepExclOracle (s : State) :
    s.stepExclOracle.sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem sigActions_stepExclLoop (s : State) :
    s.stepExclLoop.sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem sigActions_setTpidrEl0 (s : State) (v : BitVec 64) :
    (setTpidrEl0 s v).sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem sigActions_panicked (s : State) :
    (Rust.panicked s).sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem sigActions_applyWriteback (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).sigActions = s.sigActions := by cases wb <;> simp [applyWriteback]

/-! ### `State.trace` -/

@[simp, arm64_norm, wp_norm] theorem trace_writeVReg64 (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 i v).trace = s.trace := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem trace_writeVReg32 (s : State) (i : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 i v).trace = s.trace := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem trace_setFpsr (s : State) (f : BitVec 32) :
    (s.setFpsr f).trace = s.trace := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem trace_orFpsr (s : State) (f : BitVec 32) :
    (s.orFpsr f).trace = s.trace := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem trace_panicked (s : State) :
    (Rust.panicked s).trace = s.trace := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem trace_applyWriteback (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).trace = s.trace := by cases wb <;> simp [applyWriteback]

@[wp_norm] theorem trace_appendTrace_wp (s : State) (evs : List TraceEvent) :
    (s.appendTrace evs).trace = s.trace ++ evs := State.trace_appendTrace s evs
@[wp_norm] theorem trace_setBrk_wp (s : State) (b : BitVec 64) :
    (s.setBrk b).trace = s.trace := State.trace_setBrk s b
@[wp_norm] theorem trace_setFs_wp (s : State) (f : FsState) :
    (s.setFs f).trace = s.trace := State.trace_setFs s f
@[wp_norm] theorem trace_nextOracle_wp (s : State) :
    s.nextOracle.trace = s.trace := State.trace_nextOracle s
@[wp_norm] theorem trace_setStatus_wp (s : State) (st : ExecStatus) :
    (s.setStatus st).trace = s.trace := State.trace_setStatus s st
@[wp_norm] theorem trace_advancePC_wp (s : State) :
    s.advancePC.trace = s.trace := State.trace_advancePC s
@[wp_norm] theorem trace_setPC_wp (s : State) (pc : BitVec 64) :
    (s.setPC pc).trace = s.trace := State.trace_setPC s pc
@[wp_norm] theorem trace_setMem_wp (s : State) (m : Memory) :
    (s.setMem m).trace = s.trace := State.trace_setMem s m
@[wp_norm] theorem trace_setPState_wp (s : State) (ps : PState) :
    (s.setPState ps).trace = s.trace := State.trace_setPState s ps
@[wp_norm] theorem trace_writeReg64_wp (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).trace = s.trace := State.trace_writeReg64 s r v
@[wp_norm] theorem trace_writeReg32_wp (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).trace = s.trace := State.trace_writeReg32 s r v
@[wp_norm] theorem trace_writeReg_wp (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).trace = s.trace := State.trace_writeReg s w r v
@[wp_norm] theorem trace_writeVReg128_wp (s : State) (i : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).trace = s.trace := State.trace_writeVReg128 s i v
@[wp_norm] theorem trace_setTpidrEl0_wp (s : State) (v : BitVec 64) :
    (setTpidrEl0 s v).trace = s.trace := State.trace_setTpidrEl0 s v
@[wp_norm] theorem trace_stepExclOracle_wp (s : State) :
    s.stepExclOracle.trace = s.trace := State.trace_stepExclOracle s
@[wp_norm] theorem trace_stepExclLoop_wp (s : State) :
    s.stepExclLoop.trace = s.trace := State.trace_stepExclLoop s
@[wp_norm] theorem trace_setPhysMemAvail_wp (s : State) (n : Nat) :
    (s.setPhysMemAvail n).trace = s.trace := State.trace_setPhysMemAvail s n

/-! ### `State.tpidrEl0`, `State.brk`, and `State.brkStart` -/

@[simp, arm64_norm, wp_norm] theorem tpidrEl0_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).tpidrEl0 = s.tpidrEl0 := by cases s; cases r <;> rfl
@[simp, arm64_norm, wp_norm] theorem tpidrEl0_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).tpidrEl0 = s.tpidrEl0 := by cases s; cases w <;> cases r <;> rfl
@[simp, arm64_norm, wp_norm] theorem tpidrEl0_writeVReg64 (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 i v).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem tpidrEl0_writeVReg32 (s : State) (i : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 i v).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem tpidrEl0_setFpsr (s : State) (f : BitVec 32) :
    (s.setFpsr f).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem tpidrEl0_orFpsr (s : State) (f : BitVec 32) :
    (s.orFpsr f).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem tpidrEl0_panicked (s : State) :
    (Rust.panicked s).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem tpidrEl0_applyWriteback (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).tpidrEl0 = s.tpidrEl0 := by cases wb <;> simp [applyWriteback]

@[wp_norm] theorem tpidrEl0_setTpidrEl0_wp (s : State) (v : BitVec 64) :
    (setTpidrEl0 s v).tpidrEl0 = v := tpidrEl0_setTpidrEl0 s v
@[wp_norm] theorem tpidrEl0_advancePC_wp (s : State) :
    s.advancePC.tpidrEl0 = s.tpidrEl0 := State.tpidrEl0_advancePC s
@[wp_norm] theorem tpidrEl0_setPC_wp (s : State) (pc : BitVec 64) :
    (s.setPC pc).tpidrEl0 = s.tpidrEl0 := State.tpidrEl0_setPC s pc
@[wp_norm] theorem tpidrEl0_setMem_wp (s : State) (m : Memory) :
    (s.setMem m).tpidrEl0 = s.tpidrEl0 := State.tpidrEl0_setMem s m
@[wp_norm] theorem tpidrEl0_setPState_wp (s : State) (ps : PState) :
    (s.setPState ps).tpidrEl0 = s.tpidrEl0 := State.tpidrEl0_setPState s ps
@[wp_norm] theorem tpidrEl0_writeReg64_wp (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).tpidrEl0 = s.tpidrEl0 := State.tpidrEl0_writeReg64 s r v
@[wp_norm] theorem tpidrEl0_writeVReg128_wp (s : State) (i : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).tpidrEl0 = s.tpidrEl0 := State.tpidrEl0_writeVReg128 s i v
@[wp_norm] theorem tpidrEl0_setFs_wp (s : State) (f : FsState) :
    (s.setFs f).tpidrEl0 = s.tpidrEl0 := State.tpidrEl0_setFs s f
@[wp_norm] theorem tpidrEl0_setBrk_wp (s : State) (b : BitVec 64) :
    (s.setBrk b).tpidrEl0 = s.tpidrEl0 := State.tpidrEl0_setBrk s b
@[wp_norm] theorem tpidrEl0_nextOracle_wp (s : State) :
    s.nextOracle.tpidrEl0 = s.tpidrEl0 := State.tpidrEl0_nextOracle s
@[wp_norm] theorem tpidrEl0_appendTrace_wp (s : State) (evs : List TraceEvent) :
    (s.appendTrace evs).tpidrEl0 = s.tpidrEl0 := State.tpidrEl0_appendTrace s evs
@[wp_norm] theorem tpidrEl0_setStatus_wp (s : State) (st : ExecStatus) :
    (s.setStatus st).tpidrEl0 = s.tpidrEl0 := State.tpidrEl0_setStatus s st
@[wp_norm] theorem tpidrEl0_stepExclOracle_wp (s : State) :
    s.stepExclOracle.tpidrEl0 = s.tpidrEl0 := State.tpidrEl0_stepExclOracle s
@[wp_norm] theorem tpidrEl0_stepExclLoop_wp (s : State) :
    s.stepExclLoop.tpidrEl0 = s.tpidrEl0 := State.tpidrEl0_stepExclLoop s
@[wp_norm] theorem tpidrEl0_setPhysMemAvail_wp (s : State) (n : Nat) :
    (s.setPhysMemAvail n).tpidrEl0 = s.tpidrEl0 := State.tpidrEl0_setPhysMemAvail s n

@[simp, arm64_norm, wp_norm] theorem brk_setFpsr (s : State) (f : BitVec 32) :
    (s.setFpsr f).brk = s.brk := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem brk_orFpsr (s : State) (f : BitVec 32) :
    (s.orFpsr f).brk = s.brk := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem brk_panicked (s : State) :
    (Rust.panicked s).brk = s.brk := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem brk_applyWriteback (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).brk = s.brk := by cases wb <;> simp [applyWriteback]

@[simp, arm64_norm, wp_norm] theorem brkStart_setFpsr (s : State) (f : BitVec 32) :
    (s.setFpsr f).brkStart = s.brkStart := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem brkStart_orFpsr (s : State) (f : BitVec 32) :
    (s.orFpsr f).brkStart = s.brkStart := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem brkStart_panicked (s : State) :
    (Rust.panicked s).brkStart = s.brkStart := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem brkStart_applyWriteback (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).brkStart = s.brkStart := by cases wb <;> simp [applyWriteback]

@[wp_norm] theorem brk_setBrk_wp (s : State) (b : BitVec 64) :
    (s.setBrk b).brk = b := State.brk_setBrk s b
@[wp_norm] theorem brk_setFs_wp (s : State) (f : FsState) :
    (s.setFs f).brk = s.brk := State.brk_setFs s f
@[wp_norm] theorem brk_nextOracle_wp (s : State) :
    s.nextOracle.brk = s.brk := State.brk_nextOracle s
@[wp_norm] theorem brk_appendTrace_wp (s : State) (evs : List TraceEvent) :
    (s.appendTrace evs).brk = s.brk := State.brk_appendTrace s evs
@[wp_norm] theorem brk_setStatus_wp (s : State) (st : ExecStatus) :
    (s.setStatus st).brk = s.brk := State.brk_setStatus s st
@[wp_norm] theorem brk_advancePC_wp (s : State) :
    s.advancePC.brk = s.brk := State.brk_advancePC s
@[wp_norm] theorem brk_setPC_wp (s : State) (pc : BitVec 64) :
    (s.setPC pc).brk = s.brk := State.brk_setPC s pc
@[wp_norm] theorem brk_setMem_wp (s : State) (m : Memory) :
    (s.setMem m).brk = s.brk := State.brk_setMem s m
@[wp_norm] theorem brk_setPState_wp (s : State) (ps : PState) :
    (s.setPState ps).brk = s.brk := State.brk_setPState s ps
@[wp_norm] theorem brk_writeReg64_wp (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).brk = s.brk := State.brk_writeReg64 s r v
@[wp_norm] theorem brk_writeReg32_wp (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).brk = s.brk := State.brk_writeReg32 s r v
@[wp_norm] theorem brk_writeReg_wp (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).brk = s.brk := State.brk_writeReg s w r v
@[wp_norm] theorem brk_writeVReg128_wp (s : State) (i : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).brk = s.brk := State.brk_writeVReg128 s i v
@[wp_norm] theorem brk_writeVReg64_wp (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 i v).brk = s.brk := State.brk_writeVReg64 s i v
@[wp_norm] theorem brk_writeVReg32_wp (s : State) (i : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 i v).brk = s.brk := State.brk_writeVReg32 s i v
@[wp_norm] theorem brk_setTpidrEl0_wp (s : State) (v : BitVec 64) :
    (setTpidrEl0 s v).brk = s.brk := State.brk_setTpidrEl0 s v
@[wp_norm] theorem brk_stepExclOracle_wp (s : State) :
    s.stepExclOracle.brk = s.brk := State.brk_stepExclOracle s
@[wp_norm] theorem brk_stepExclLoop_wp (s : State) :
    s.stepExclLoop.brk = s.brk := State.brk_stepExclLoop s
@[wp_norm] theorem brk_setPhysMemAvail_wp (s : State) (n : Nat) :
    (s.setPhysMemAvail n).brk = s.brk := State.brk_setPhysMemAvail s n

@[wp_norm] theorem brkStart_setBrk_wp (s : State) (b : BitVec 64) :
    (s.setBrk b).brkStart = s.brkStart := State.brkStart_setBrk s b
@[wp_norm] theorem brkStart_setFs_wp (s : State) (f : FsState) :
    (s.setFs f).brkStart = s.brkStart := State.brkStart_setFs s f
@[wp_norm] theorem brkStart_nextOracle_wp (s : State) :
    s.nextOracle.brkStart = s.brkStart := State.brkStart_nextOracle s
@[wp_norm] theorem brkStart_appendTrace_wp (s : State) (evs : List TraceEvent) :
    (s.appendTrace evs).brkStart = s.brkStart := State.brkStart_appendTrace s evs
@[wp_norm] theorem brkStart_setStatus_wp (s : State) (st : ExecStatus) :
    (s.setStatus st).brkStart = s.brkStart := State.brkStart_setStatus s st
@[wp_norm] theorem brkStart_advancePC_wp (s : State) :
    s.advancePC.brkStart = s.brkStart := State.brkStart_advancePC s
@[wp_norm] theorem brkStart_setPC_wp (s : State) (pc : BitVec 64) :
    (s.setPC pc).brkStart = s.brkStart := State.brkStart_setPC s pc
@[wp_norm] theorem brkStart_setMem_wp (s : State) (m : Memory) :
    (s.setMem m).brkStart = s.brkStart := State.brkStart_setMem s m
@[wp_norm] theorem brkStart_setPState_wp (s : State) (ps : PState) :
    (s.setPState ps).brkStart = s.brkStart := State.brkStart_setPState s ps
@[wp_norm] theorem brkStart_writeReg64_wp (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).brkStart = s.brkStart := State.brkStart_writeReg64 s r v
@[wp_norm] theorem brkStart_writeReg32_wp (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).brkStart = s.brkStart := State.brkStart_writeReg32 s r v
@[wp_norm] theorem brkStart_writeReg_wp (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).brkStart = s.brkStart := State.brkStart_writeReg s w r v
@[wp_norm] theorem brkStart_writeVReg128_wp (s : State) (i : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).brkStart = s.brkStart := State.brkStart_writeVReg128 s i v
@[wp_norm] theorem brkStart_writeVReg64_wp (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 i v).brkStart = s.brkStart := State.brkStart_writeVReg64 s i v
@[wp_norm] theorem brkStart_writeVReg32_wp (s : State) (i : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 i v).brkStart = s.brkStart := State.brkStart_writeVReg32 s i v
@[wp_norm] theorem brkStart_setTpidrEl0_wp (s : State) (v : BitVec 64) :
    (setTpidrEl0 s v).brkStart = s.brkStart := State.brkStart_setTpidrEl0 s v
@[wp_norm] theorem brkStart_stepExclOracle_wp (s : State) :
    s.stepExclOracle.brkStart = s.brkStart := State.brkStart_stepExclOracle s
@[wp_norm] theorem brkStart_stepExclLoop_wp (s : State) :
    s.stepExclLoop.brkStart = s.brkStart := State.brkStart_stepExclLoop s
@[wp_norm] theorem brkStart_setPhysMemAvail_wp (s : State) (n : Nat) :
    (s.setPhysMemAvail n).brkStart = s.brkStart := State.brkStart_setPhysMemAvail s n

/-! ## Two-Sided Step Lemmas for `OomPreserved`, `AllocCallPreserved`, and `PoolPreserved` -/

/-! ### `OomPreserved` -/

@[simp, arm64_norm, wp_norm] theorem oomPreserved_self (s : State) : OomPreserved s s :=
  ⟨rfl, rfl, rfl⟩

theorem oomPreserved_fs_eq {s0 sf : State} (h : OomPreserved s0 sf) : sf.fs = s0.fs := h.1
theorem oomPreserved_trace_eq {s0 sf : State} (h : OomPreserved s0 sf) : sf.trace = s0.trace :=
  h.2.1
theorem oomPreserved_sigActions_eq {s0 sf : State} (h : OomPreserved s0 sf) :
    sf.sigActions = s0.sigActions := h.2.2

@[simp, arm64_norm, wp_norm] theorem oomPreserved_writeReg64 (s0 s : State) (r : Reg) (v : BitVec 64) :
    OomPreserved s0 (s.writeReg64 r v) ↔ OomPreserved s0 s := by cases s; cases r <;> exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_writeReg32 (s0 s : State) (r : Reg) (v : BitVec 32) :
    OomPreserved s0 (s.writeReg32 r v) ↔ OomPreserved s0 s := by cases s; cases r <;> exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_writeReg (s0 s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    OomPreserved s0 (s.writeReg w r v) ↔ OomPreserved s0 s := by
  cases s; cases w <;> cases r <;> exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_writeVReg128 (s0 s : State) (i : BitVec 5) (v : BitVec 128) :
    OomPreserved s0 (s.writeVReg128 i v) ↔ OomPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_writeVReg64 (s0 s : State) (i : BitVec 5) (v : BitVec 64) :
    OomPreserved s0 (s.writeVReg64 i v) ↔ OomPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_writeVReg32 (s0 s : State) (i : BitVec 5) (v : BitVec 32) :
    OomPreserved s0 (s.writeVReg32 i v) ↔ OomPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_setMem (s0 s : State) (m : Memory) :
    OomPreserved s0 (s.setMem m) ↔ OomPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_setPC (s0 s : State) (pc : BitVec 64) :
    OomPreserved s0 (s.setPC pc) ↔ OomPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_advancePC (s0 s : State) :
    OomPreserved s0 s.advancePC ↔ OomPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_setPState (s0 s : State) (ps : PState) :
    OomPreserved s0 (s.setPState ps) ↔ OomPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_setFpsr (s0 s : State) (f : BitVec 32) :
    OomPreserved s0 (s.setFpsr f) ↔ OomPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_orFpsr (s0 s : State) (f : BitVec 32) :
    OomPreserved s0 (s.orFpsr f) ↔ OomPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_setStatus (s0 s : State) (st : ExecStatus) :
    OomPreserved s0 (s.setStatus st) ↔ OomPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_setBrk (s0 s : State) (b : BitVec 64) :
    OomPreserved s0 (s.setBrk b) ↔ OomPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_setPhysMemAvail (s0 s : State) (n : Nat) :
    OomPreserved s0 (s.setPhysMemAvail n) ↔ OomPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_nextOracle (s0 s : State) :
    OomPreserved s0 s.nextOracle ↔ OomPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_stepExclOracle (s0 s : State) :
    OomPreserved s0 s.stepExclOracle ↔ OomPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_stepExclLoop (s0 s : State) :
    OomPreserved s0 s.stepExclLoop ↔ OomPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_setTpidrEl0 (s0 s : State) (v : BitVec 64) :
    OomPreserved s0 (setTpidrEl0 s v) ↔ OomPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_panicked (s0 s : State) :
    OomPreserved s0 (Rust.panicked s) ↔ OomPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_applyWriteback (s0 s : State) (wb : Option (Reg × BitVec 64)) :
    OomPreserved s0 (applyWriteback s wb) ↔ OomPreserved s0 s := by
  cases wb <;> simp [applyWriteback, oomPreserved_writeReg64]

@[simp, arm64_norm, wp_norm] theorem oomPreserved_writeReg64_left (s0 sf : State) (r : Reg) (v : BitVec 64) :
    OomPreserved (s0.writeReg64 r v) sf ↔ OomPreserved s0 sf := by cases s0; cases r <;> exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_writeReg32_left (s0 sf : State) (r : Reg) (v : BitVec 32) :
    OomPreserved (s0.writeReg32 r v) sf ↔ OomPreserved s0 sf := by cases s0; cases r <;> exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_writeReg_left (s0 sf : State) (w : Width) (r : Reg) (v : BitVec 64) :
    OomPreserved (s0.writeReg w r v) sf ↔ OomPreserved s0 sf := by
  cases s0; cases w <;> cases r <;> exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_writeVReg128_left (s0 sf : State) (i : BitVec 5) (v : BitVec 128) :
    OomPreserved (s0.writeVReg128 i v) sf ↔ OomPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_writeVReg64_left (s0 sf : State) (i : BitVec 5) (v : BitVec 64) :
    OomPreserved (s0.writeVReg64 i v) sf ↔ OomPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_writeVReg32_left (s0 sf : State) (i : BitVec 5) (v : BitVec 32) :
    OomPreserved (s0.writeVReg32 i v) sf ↔ OomPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_setMem_left (s0 sf : State) (m : Memory) :
    OomPreserved (s0.setMem m) sf ↔ OomPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_setPC_left (s0 sf : State) (pc : BitVec 64) :
    OomPreserved (s0.setPC pc) sf ↔ OomPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_advancePC_left (s0 sf : State) :
    OomPreserved s0.advancePC sf ↔ OomPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_setPState_left (s0 sf : State) (ps : PState) :
    OomPreserved (s0.setPState ps) sf ↔ OomPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_setFpsr_left (s0 sf : State) (f : BitVec 32) :
    OomPreserved (s0.setFpsr f) sf ↔ OomPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_orFpsr_left (s0 sf : State) (f : BitVec 32) :
    OomPreserved (s0.orFpsr f) sf ↔ OomPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_setStatus_left (s0 sf : State) (st : ExecStatus) :
    OomPreserved (s0.setStatus st) sf ↔ OomPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_setBrk_left (s0 sf : State) (b : BitVec 64) :
    OomPreserved (s0.setBrk b) sf ↔ OomPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_setPhysMemAvail_left (s0 sf : State) (n : Nat) :
    OomPreserved (s0.setPhysMemAvail n) sf ↔ OomPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_nextOracle_left (s0 sf : State) :
    OomPreserved s0.nextOracle sf ↔ OomPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_stepExclOracle_left (s0 sf : State) :
    OomPreserved s0.stepExclOracle sf ↔ OomPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_stepExclLoop_left (s0 sf : State) :
    OomPreserved s0.stepExclLoop sf ↔ OomPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_setTpidrEl0_left (s0 sf : State) (v : BitVec 64) :
    OomPreserved (setTpidrEl0 s0 v) sf ↔ OomPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_panicked_left (s0 sf : State) :
    OomPreserved (Rust.panicked s0) sf ↔ OomPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem oomPreserved_applyWriteback_left (s0 sf : State) (wb : Option (Reg × BitVec 64)) :
    OomPreserved (applyWriteback s0 wb) sf ↔ OomPreserved s0 sf := by
  cases wb <;> simp [applyWriteback, oomPreserved_writeReg64_left]

/-! ### `AllocCallPreserved` -/

@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_self (s : State) : AllocCallPreserved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_writeReg64 (s0 s : State) (r : Reg) (v : BitVec 64) :
    AllocCallPreserved s0 (s.writeReg64 r v) ↔ AllocCallPreserved s0 s := by
  cases s; cases r <;> exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_writeReg32 (s0 s : State) (r : Reg) (v : BitVec 32) :
    AllocCallPreserved s0 (s.writeReg32 r v) ↔ AllocCallPreserved s0 s := by
  cases s; cases r <;> exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_writeReg (s0 s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    AllocCallPreserved s0 (s.writeReg w r v) ↔ AllocCallPreserved s0 s := by
  cases s; cases w <;> cases r <;> exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_writeVReg128 (s0 s : State) (i : BitVec 5) (v : BitVec 128) :
    AllocCallPreserved s0 (s.writeVReg128 i v) ↔ AllocCallPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_writeVReg64 (s0 s : State) (i : BitVec 5) (v : BitVec 64) :
    AllocCallPreserved s0 (s.writeVReg64 i v) ↔ AllocCallPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_writeVReg32 (s0 s : State) (i : BitVec 5) (v : BitVec 32) :
    AllocCallPreserved s0 (s.writeVReg32 i v) ↔ AllocCallPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_setMem (s0 s : State) (m : Memory) :
    AllocCallPreserved s0 (s.setMem m) ↔ AllocCallPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_setPC (s0 s : State) (pc : BitVec 64) :
    AllocCallPreserved s0 (s.setPC pc) ↔ AllocCallPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_advancePC (s0 s : State) :
    AllocCallPreserved s0 s.advancePC ↔ AllocCallPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_setPState (s0 s : State) (ps : PState) :
    AllocCallPreserved s0 (s.setPState ps) ↔ AllocCallPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_setFpsr (s0 s : State) (f : BitVec 32) :
    AllocCallPreserved s0 (s.setFpsr f) ↔ AllocCallPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_orFpsr (s0 s : State) (f : BitVec 32) :
    AllocCallPreserved s0 (s.orFpsr f) ↔ AllocCallPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_setStatus (s0 s : State) (st : ExecStatus) :
    AllocCallPreserved s0 (s.setStatus st) ↔ AllocCallPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_setBrk (s0 s : State) (b : BitVec 64) :
    AllocCallPreserved s0 (s.setBrk b) ↔ AllocCallPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_setPhysMemAvail (s0 s : State) (n : Nat) :
    AllocCallPreserved s0 (s.setPhysMemAvail n) ↔ AllocCallPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_panicked (s0 s : State) :
    AllocCallPreserved s0 (Rust.panicked s) ↔ AllocCallPreserved s0 s := by cases s; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_applyWriteback (s0 s : State) (wb : Option (Reg × BitVec 64)) :
    AllocCallPreserved s0 (applyWriteback s wb) ↔ AllocCallPreserved s0 s := by
  cases wb <;> simp [applyWriteback, allocCallPreserved_writeReg64]

@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_writeReg64_left (s0 sf : State) (r : Reg) (v : BitVec 64) :
    AllocCallPreserved (s0.writeReg64 r v) sf ↔ AllocCallPreserved s0 sf := by
  cases s0; cases r <;> exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_writeReg32_left (s0 sf : State) (r : Reg) (v : BitVec 32) :
    AllocCallPreserved (s0.writeReg32 r v) sf ↔ AllocCallPreserved s0 sf := by
  cases s0; cases r <;> exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_writeReg_left (s0 sf : State) (w : Width) (r : Reg) (v : BitVec 64) :
    AllocCallPreserved (s0.writeReg w r v) sf ↔ AllocCallPreserved s0 sf := by
  cases s0; cases w <;> cases r <;> exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_writeVReg128_left (s0 sf : State) (i : BitVec 5) (v : BitVec 128) :
    AllocCallPreserved (s0.writeVReg128 i v) sf ↔ AllocCallPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_writeVReg64_left (s0 sf : State) (i : BitVec 5) (v : BitVec 64) :
    AllocCallPreserved (s0.writeVReg64 i v) sf ↔ AllocCallPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_writeVReg32_left (s0 sf : State) (i : BitVec 5) (v : BitVec 32) :
    AllocCallPreserved (s0.writeVReg32 i v) sf ↔ AllocCallPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_setMem_left (s0 sf : State) (m : Memory) :
    AllocCallPreserved (s0.setMem m) sf ↔ AllocCallPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_setPC_left (s0 sf : State) (pc : BitVec 64) :
    AllocCallPreserved (s0.setPC pc) sf ↔ AllocCallPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_advancePC_left (s0 sf : State) :
    AllocCallPreserved s0.advancePC sf ↔ AllocCallPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_setPState_left (s0 sf : State) (ps : PState) :
    AllocCallPreserved (s0.setPState ps) sf ↔ AllocCallPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_setFpsr_left (s0 sf : State) (f : BitVec 32) :
    AllocCallPreserved (s0.setFpsr f) sf ↔ AllocCallPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_orFpsr_left (s0 sf : State) (f : BitVec 32) :
    AllocCallPreserved (s0.orFpsr f) sf ↔ AllocCallPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_setStatus_left (s0 sf : State) (st : ExecStatus) :
    AllocCallPreserved (s0.setStatus st) sf ↔ AllocCallPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_setBrk_left (s0 sf : State) (b : BitVec 64) :
    AllocCallPreserved (s0.setBrk b) sf ↔ AllocCallPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_setPhysMemAvail_left (s0 sf : State) (n : Nat) :
    AllocCallPreserved (s0.setPhysMemAvail n) sf ↔ AllocCallPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_panicked_left (s0 sf : State) :
    AllocCallPreserved (Rust.panicked s0) sf ↔ AllocCallPreserved s0 sf := by cases s0; exact Iff.rfl
@[simp, arm64_norm, wp_norm] theorem allocCallPreserved_applyWriteback_left (s0 sf : State) (wb : Option (Reg × BitVec 64)) :
    AllocCallPreserved (applyWriteback s0 wb) sf ↔ AllocCallPreserved s0 sf := by
  cases wb <;> simp [applyWriteback, allocCallPreserved_writeReg64_left]

/-! ### `PoolPreserved` -/

theorem poolPreserved_self (s : State) : PoolPreserved s s := ⟨rfl, rfl, rfl⟩

/-- Bridge `ProofLib.StdStartup.VmFieldsPreserved` + `tpidrEl0` equality to `PoolPreserved`. -/
theorem poolPreserved_of_vmFields_tpidr {s0 sf : State}
    (hvm : ProofLib.StdStartup.VmFieldsPreserved s0 sf) (htp : sf.tpidrEl0 = s0.tpidrEl0) :
    PoolPreserved s0 sf :=
  ⟨hvm.brkStart_eq, hvm.brk_eq, htp⟩

/-! ## `RustCliAlloc` Pool, `atState`, and `repAlloc` Normalization -/

/-- `A.repAlloc` has `pool = emp`; contracts that read `.pool` must use `A.atState s` or `rustCli*Spec`. -/
@[simp, arm64_norm, wp_norm] theorem repAlloc_pool (A : RustCliAlloc) : A.repAlloc.pool = emp := rfl

@[arm64_norm, wp_norm] theorem repAlloc_live_norm (A : RustCliAlloc) : A.repAlloc.live = A.live := rfl
@[arm64_norm, wp_norm] theorem atState_pool_norm (A : RustCliAlloc) (s : State) :
    (A.atState s).pool = A.pool s := rfl
@[arm64_norm, wp_norm] theorem atState_live_norm (A : RustCliAlloc) (s : State) :
    (A.atState s).live = A.live := rfl

@[simp, arm64_norm, wp_norm] theorem pool_setStatus (A : RustCliAlloc) (s : State) (st : ExecStatus) :
    A.pool (s.setStatus st) = A.pool s := A.pool_transport _ _ ⟨rfl, rfl, rfl⟩
@[simp, arm64_norm, wp_norm] theorem pool_appendTrace (A : RustCliAlloc) (s : State) (evs : List TraceEvent) :
    A.pool (s.appendTrace evs) = A.pool s := A.pool_transport _ _ ⟨rfl, rfl, rfl⟩
@[simp, arm64_norm, wp_norm] theorem pool_setFs (A : RustCliAlloc) (s : State) (f : FsState) :
    A.pool (s.setFs f) = A.pool s := A.pool_transport _ _ ⟨rfl, rfl, rfl⟩
@[simp, arm64_norm, wp_norm] theorem pool_setPhysMemAvail (A : RustCliAlloc) (s : State) (n : Nat) :
    A.pool (s.setPhysMemAvail n) = A.pool s := A.pool_transport _ _ ⟨rfl, rfl, rfl⟩
@[simp, arm64_norm, wp_norm] theorem pool_stepExclLoop (A : RustCliAlloc) (s : State) :
    A.pool s.stepExclLoop = A.pool s := A.pool_transport _ _ ⟨rfl, rfl, rfl⟩
@[simp, arm64_norm, wp_norm] theorem pool_panicked (A : RustCliAlloc) (s : State) :
    A.pool (Rust.panicked s) = A.pool s := A.pool_transport _ _ ⟨rfl, rfl, rfl⟩
@[simp, arm64_norm, wp_norm] theorem pool_applyWriteback (A : RustCliAlloc) (s : State) (wb : Option (Reg × BitVec 64)) :
    A.pool (applyWriteback s wb) = A.pool s := by cases wb <;> simp [applyWriteback]

@[arm64_norm, wp_norm] theorem pool_setMem_norm (A : RustCliAlloc) (s : State) (m : Memory) :
    A.pool (s.setMem m) = A.pool s := A.pool_setMem s m
@[arm64_norm, wp_norm] theorem pool_setPC_norm (A : RustCliAlloc) (s : State) (pc : BitVec 64) :
    A.pool (s.setPC pc) = A.pool s := A.pool_setPC s pc
@[arm64_norm, wp_norm] theorem pool_advancePC_norm (A : RustCliAlloc) (s : State) :
    A.pool s.advancePC = A.pool s := A.pool_advancePC s
@[arm64_norm, wp_norm] theorem pool_setPState_norm (A : RustCliAlloc) (s : State) (ps : PState) :
    A.pool (s.setPState ps) = A.pool s := A.pool_setPState s ps
@[arm64_norm, wp_norm] theorem pool_writeReg64_norm (A : RustCliAlloc) (s : State) (r : Reg) (v : BitVec 64) :
    A.pool (s.writeReg64 r v) = A.pool s := A.pool_writeReg64 s r v
@[arm64_norm, wp_norm] theorem pool_writeReg32_norm (A : RustCliAlloc) (s : State) (r : Reg) (v : BitVec 32) :
    A.pool (s.writeReg32 r v) = A.pool s := A.pool_writeReg32 s r v
@[arm64_norm, wp_norm] theorem pool_writeReg_norm (A : RustCliAlloc) (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    A.pool (s.writeReg w r v) = A.pool s := A.pool_writeReg s w r v
@[arm64_norm, wp_norm] theorem pool_writeVReg128_norm (A : RustCliAlloc) (s : State) (i : BitVec 5) (v : BitVec 128) :
    A.pool (s.writeVReg128 i v) = A.pool s := A.pool_writeVReg128 s i v
@[arm64_norm, wp_norm] theorem pool_writeVReg64_norm (A : RustCliAlloc) (s : State) (i : BitVec 5) (v : BitVec 64) :
    A.pool (s.writeVReg64 i v) = A.pool s := A.pool_writeVReg64 s i v
@[arm64_norm, wp_norm] theorem pool_writeVReg32_norm (A : RustCliAlloc) (s : State) (i : BitVec 5) (v : BitVec 32) :
    A.pool (s.writeVReg32 i v) = A.pool s := A.pool_writeVReg32 s i v

/-! ## OOM-Polymorphic `SepWP`/`SepWPp`, `ReachesOrPanicOom`, and Leaf Wrappers -/

/-! ### Frozen-Memory and `symtab` Composition -/

/-- `{oom}`-polymorphic generalization of `ProofLib.SepWP.seq_frozen`: split a `SepWP` proof at
`mid`, re-establish any `KeepsFrozen`-stable memory fact `Φ` at `mid`, and propagate `oom`. -/
theorem sepWP_seq_frozen_oom {prog : Program} {mid target : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {Φ : Memory → Prop}
    (hst : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m') (hΦ : Φ s.mem)
    (h : SepWP prog mid s P (fun sm Pm => Φ sm.mem → SepWP prog target sm Pm post oom) oom) :
    SepWP prog target s P post oom := by
  refine SepWP.of_reaches_pc fun R hm hL => ?_
  rcases h.elim hm hL with ⟨sm, hst1, ⟨-, -, Pm, hmm, hcont⟩ | ⟨hoom, hf⟩⟩
  · rcases (hcont (hst _ _ hΦ hst1.keepsFrozen)).elim hmm (hst1.codeLoaded hL) with
      ⟨sf, hst2, ⟨hpc, hrun, Pf, hmf, hpost⟩ | ⟨hoom, hf⟩⟩
    · exact ⟨sf, hst1.trans hst2, Or.inl ⟨hpc, hrun, Pf, hmf, hpost⟩⟩
    · exact ⟨sf, hst1.trans hst2, Or.inr ⟨hoom, hf⟩⟩
  · exact ⟨sm, hst1, Or.inr ⟨hoom, hf⟩⟩

/-- `{oom}`-polymorphic `SepWP` segment composition threading `img.FrozenLoaded` and
`s.symtab = img.symtab` to the midpoint `sm` (generalizing `CallInv.lean`'s `SepWP.of_sepWP_inv`). -/
theorem sepWP_of_sepWP_inv_oom {prog : Program} {img : Obj.Image} {mid target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog mid s P
      (fun sm Pm => img.FrozenLoaded sm → sm.symtab = img.symtab →
        SepWP prog target_pc sm Pm post oom) oom) :
    SepWP prog target_pc s P post oom := by
  refine SepWP.of_reaches_pc fun R hm hL => ?_
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨hoom, hf⟩⟩
  · rcases (hnext (hsteps.frozenLoaded hfl) (hsteps.symtab_eq.trans hsym)).elim hmm
        (hsteps.codeLoaded hL) with ⟨sf, hsteps', ⟨hpc, hrun, Pf, hmf, hpost⟩ | ⟨hoom, hf⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpc, hrun, Pf, hmf, hpost⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr ⟨hoom, hf⟩⟩
  · exact ⟨sm, hsteps, Or.inr ⟨hoom, hf⟩⟩

/-- `{oom}`-polymorphic `SepWP` → `SepWPp` composition threading `img.FrozenLoaded` and
`s.symtab = img.symtab` to the midpoint `sm` (generalizing `CallInv.lean`'s
`SepWPp.of_sepWP_frozen`). -/
theorem sepWPp_of_sepWP_frozen_oom {prog : Program} {img : Obj.Image} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog mid s P
      (fun sm Pm => img.FrozenLoaded sm → sm.symtab = img.symtab →
        SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨hoom, hf⟩⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext (hsteps.frozenLoaded hF) (hsteps.symtab_eq.trans hsym) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom, hf⟩)⟩

/-- Alias of `sepWPp_of_sepWP_frozen_oom` with `{mid ret}` argument order (`SepWPp.of_sepWP_inv`). -/
theorem sepWPp_of_sepWP_inv_oom {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog mid s P
      (fun sm Pm => img.FrozenLoaded sm → sm.symtab = img.symtab →
        SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom :=
  sepWPp_of_sepWP_frozen_oom hfl hsym h

/-! ### Postcondition Entailment Strengthening -/

/-- State-indexed, `{oom}`-polymorphic generalization of `SepWP.strengthen_entails`: strengthen
`Pm ⊢ Q₁ sm` to `Pm ⊢ Q₂ sm` when `Q₁ sm` depends on the exit state `sm` (e.g. `A.pool sm ∗ ...`). -/
theorem sepWP_strengthen_entails_oom {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : SepProp} {Q₁ Q₂ : State → SepProp} {φ : State → Prop} {oom : State → SepProp}
    (himp : ∀ sm, Q₁ sm ⊢ Q₂ sm)
    (h : SepWP prog target_pc s P (fun sm Pm => (Pm ⊢ Q₁ sm) ∧ φ sm) oom) :
    SepWP prog target_pc s P (fun sm Pm => (Pm ⊢ Q₂ sm) ∧ φ sm) oom :=
  SepWP.mono h fun sm _ _ _ ⟨h1, h2⟩ => ⟨Entails.trans h1 (himp sm), h2⟩

/-- Constant-spatial, `{oom}`-polymorphic specialization of `sepWP_strengthen_entails_oom`. -/
theorem sepWP_strengthen_entails_const_oom {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P₁ P₂ : SepProp} {φ : State → Prop} {oom : State → SepProp}
    (himp : P₁ ⊢ P₂)
    (h : SepWP prog target_pc s P (fun sm Pm => (Pm ⊢ P₁) ∧ φ sm) oom) :
    SepWP prog target_pc s P (fun sm Pm => (Pm ⊢ P₂) ∧ φ sm) oom :=
  sepWP_strengthen_entails_oom (fun _ => himp) h

/-- Panic-aware (`SepWPp`) counterpart of `sepWP_strengthen_entails_oom`. -/
theorem sepWPp_strengthen_entails_oom {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q₁ Q₂ : State → SepProp} {φ : State → Prop}
    {Qp : State → SepProp → Prop} {oom : State → SepProp}
    (himp : ∀ sm, Q₁ sm ⊢ Q₂ sm)
    (h : SepWPp prog ret s P (fun sm Pm => (Pm ⊢ Q₁ sm) ∧ φ sm) Qp oom) :
    SepWPp prog ret s P (fun sm Pm => (Pm ⊢ Q₂ sm) ∧ φ sm) Qp oom := by
  intro R hm hL
  rcases h R hm hL with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, h1, h2⟩ | hpan | hoom⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, Entails.trans h1 (himp sf), h2⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-! ### Frame-Dropping OOM and Panic Helpers -/

/-- Discharge `hoom` on `SepWP`/`SepWPp` call lemmas when the caller reached `s` from `s0` with
`OomPreserved s0 s` and the callee stops in `.OutOfMemory` with `⌜OomPreserved s sf⌝`. -/
theorem oom_frame_trans {s0 s sf : State} {F R' : SepProp}
    (h0 : OomPreserved s0 s := by simp)
    (hm : sf.mem ⊨ ⌜OomPreserved s sf⌝ ∗ (F ∗ R')) :
    sf.mem ⊨ ⌜OomPreserved s0 sf⌝ ∗ R' :=
  IfaceLemmas.satisfies_oomPreserved_frame h0 hm

/-- Absorb a carved call frame `F` into `anyHeap` and compose `OomPreserved s0 s` with
`OomPreserved s sf` on a panicking callee branch (`⌜φ sf ∧ OomPreserved s sf⌝ ∗ anyHeap`). -/
theorem satisfies_oom_panic_frame {s0 s sf : State} {φ ψ : State → Prop} {F R : SepProp}
    (h0 : OomPreserved s0 s := by simp)
    (hφ : φ sf → ψ sf := by exact id)
    (hm : sf.mem ⊨ (⌜φ sf ∧ OomPreserved s sf⌝ ∗ anyHeap) ∗ (F ∗ R)) :
    sf.mem ⊨ (⌜ψ sf ∧ OomPreserved s0 sf⌝ ∗ anyHeap) ∗ R :=
  ProofLib.satisfies_allowPanicWhen_frame (fun ⟨hp, ho⟩ => ⟨hφ hp, h0.trans ho⟩) hm

/-- Derive `subroutine_ok` from `SepWPp` with a split local frame `F0 ∗ R` and pure
`spec.onOom x s0 sf = ⌜φ x s0 sf⌝` (such as `⌜OomPreserved s0 sf⌝`), dropping `F0` on
`.OutOfMemory` via `Satisfies.drop_left`. -/
theorem subroutine_ok_of_sepWPp_pure_oom {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} {φ : α → State → State → Prop}
    (hoom_eq : ∀ x s0 sf, spec.onOom x s0 sf = ⌜φ x s0 sf⌝ := by intros; rfl)
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      ∃ P F0 : SepProp, (s0.mem ⊨ P ∗ (F0 ∗ R)) ∧
        SepWPp prog (s0.readReg64 Reg.lr) s0 P
          (fun sf P_f => ((sf.mem ⊨ P_f ∗ (F0 ∗ R)) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f => (sf.mem ⊨ P_f ∗ (F0 ∗ R)) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))
          (fun sf => ⌜φ x s0 sf⌝)) :
    subroutine_ok prog entry spec := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  obtain ⟨P, F0, hm, hwp⟩ := h x R s0 hpc hrun hpre hsp
  obtain ⟨sf, hsteps, hout⟩ := hwp (F0 ∗ R) hm hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, hq, hspf, hcsf⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨ho, hmo⟩
  · exact Or.inl ⟨⟨hpcf, hspf, hrunf⟩, ⟨hspf, hcsf⟩, hq hmf⟩
  · exact Or.inr (Or.inl ⟨hpan, hqp hmf⟩)
  · refine Or.inr (Or.inr (Or.inr ⟨ho, ?_⟩))
    rw [satisfies_pure_sepConj] at hmo
    rw [hoom_eq x s0 sf, satisfies_pure_sepConj]
    exact ⟨hmo.1, Satisfies.drop_left hmo.2⟩

/-! ### Three-Outcome `reaches_outcome` and `ReachesOrPanicOom` Combinators -/

/-- Lift a `.Panicked` state reached via `Steps prog s s'` into `reaches_outcome prog spec x R s0 s`. -/
theorem reaches_outcome_of_panic_steps {α : Type} {prog : Program} {spec : Spec α}
    {x : α} {R : SepProp} {s0 s s' : State}
    (hsteps : Steps prog s s') (hpan : s'.status = .Panicked)
    (hq : s'.mem ⊨ spec.onPanic x s0 s' ∗ R) :
    reaches_outcome prog spec x R s0 s :=
  reaches_outcome_steps hsteps (reaches_outcome_refl_panic hpan hq)

/-- Lift an `.OutOfMemory` state reached via `Steps prog s s'` into `reaches_outcome prog spec x R s0 s`. -/
theorem reaches_outcome_of_oom_steps {α : Type} {prog : Program} {spec : Spec α}
    {x : α} {R : SepProp} {s0 s s' : State}
    (hsteps : Steps prog s s') (hoom : s'.status = .OutOfMemory)
    (hq : s'.mem ⊨ spec.onOom x s0 s' ∗ R) :
    reaches_outcome prog spec x R s0 s :=
  reaches_outcome_steps hsteps (reaches_outcome_refl_oom hoom hq)

/-- Drop a carved middle frame `F` under `onPanic = ⌜φ⌝ ∗ anyHeap`. -/
theorem onPanic_drop_frame_anyHeap {φ ψ : Prop} {F R : SepProp} {m : Memory}
    (himp : φ → ψ := by exact id) (h : m ⊨ (⌜φ⌝ ∗ anyHeap) ∗ (F ∗ R)) :
    m ⊨ (⌜ψ⌝ ∗ anyHeap) ∗ R :=
  ProofLib.satisfies_allowPanicWhen_frame himp h

/-- Drop a carved middle frame `F` under a pure `onOom = ⌜φ⌝`. -/
theorem onOom_drop_frame_pure {φ ψ : Prop} {F R : SepProp} {m : Memory}
    (himp : φ → ψ := by exact id) (h : m ⊨ ⌜φ⌝ ∗ (F ∗ R)) :
    m ⊨ ⌜ψ⌝ ∗ R := by
  rw [satisfies_pure_sepConj] at h ⊢
  exact ⟨himp h.1, Satisfies.drop_left h.2⟩

/-- Spec-parametric frame-dropping consequence rule on `reaches_outcome` for non-exiting contracts
whose `onPanic` and `onOom` absorb an intermediate frame `F`. -/
theorem reaches_outcome_drop_frame_oom {α β : Type} {prog : Program}
    {spec : Spec α} {spec' : Spec β} {x : α} {y : β} {F R : SepProp} {s0 s : State}
    (h : reaches_outcome prog spec x (F ∗ R) s0 s)
    (hpost : ∀ sf, Returned s0 sf → CallingConventionPreserved s0 sf →
      (sf.mem ⊨ spec.post x s0 sf ∗ (F ∗ R)) → (sf.mem ⊨ spec'.post y s0 sf ∗ R))
    (hpan : ∀ sf, sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s0 sf ∗ (F ∗ R)) → (sf.mem ⊨ spec'.onPanic y s0 sf ∗ R))
    (hoom : ∀ sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s0 sf ∗ (F ∗ R)) → (sf.mem ⊨ spec'.onOom y s0 sf ∗ R))
    (h_no_exit : ∀ code sf, sf.status = .Exited code →
      ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ (F ∗ R)) := by
        intro _ _ _ he; exact not_satisfies_false_sepConj he) :
    reaches_outcome prog spec' y R s0 s :=
  h.mono_outcome fun sf hout => by
    rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨code, hex_st, hq⟩ | ⟨ho_st, hq⟩
    · exact Or.inl ⟨hret, hcc, hpost sf hret hcc hq⟩
    · exact Or.inr (Or.inl ⟨hp_st, hpan sf hp_st hq⟩)
    · exact False.elim (h_no_exit code sf hex_st hq)
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, hoom sf ho_st hq⟩))

/-- Generic 3-outcome intermediate execution relation from `s` (for entry state `s0` and outer
caller frame `R`): execution reaches `s'` satisfying either normal continuation predicate `Q s'`,
panic postcondition `Pan s0 s' ∗ R`, or out-of-memory `⌜OomPreserved s0 s'⌝ ∗ R`. -/
def ReachesOrPanicOom (prog : Program) (Pan : State → State → SepProp)
    (R : SepProp) (s0 s : State) (Q : State → Prop) : Prop :=
  ∃ s', Steps prog s s' ∧
    (Q s' ∨
      (s'.status = .Panicked ∧ (s'.mem ⊨ Pan s0 s' ∗ R)) ∨
      (s'.status = .OutOfMemory ∧ (s'.mem ⊨ ⌜OomPreserved s0 s'⌝ ∗ R)))

namespace ReachesOrPanicOom

theorem done {prog : Program} {Pan : State → State → SepProp}
    {R : SepProp} {s0 s : State} {Q : State → Prop} (hQ : Q s) :
    ReachesOrPanicOom prog Pan R s0 s Q :=
  ⟨s, Steps.refl s, Or.inl hQ⟩

theorem mono {prog : Program} {Pan : State → State → SepProp}
    {R : SepProp} {s0 s : State} {P Q : State → Prop}
    (h : ReachesOrPanicOom prog Pan R s0 s P) (himp : ∀ s', P s' → Q s') :
    ReachesOrPanicOom prog Pan R s0 s Q := by
  obtain ⟨s', hsteps, hP | hPan | hOom⟩ := h
  · exact ⟨s', hsteps, Or.inl (himp s' hP)⟩
  · exact ⟨s', hsteps, Or.inr (Or.inl hPan)⟩
  · exact ⟨s', hsteps, Or.inr (Or.inr hOom)⟩

theorem seq {prog : Program} {Pan : State → State → SepProp}
    {R : SepProp} {s0 s : State} {P Q : State → Prop}
    (h1 : ReachesOrPanicOom prog Pan R s0 s P)
    (h2 : ∀ s1, s.mem.KeepsFrozen s1.mem → s1.symtab = s.symtab → P s1 →
      ReachesOrPanicOom prog Pan R s0 s1 Q) :
    ReachesOrPanicOom prog Pan R s0 s Q := by
  obtain ⟨s1, hsteps1, hP | hPan | hOom⟩ := h1
  · obtain ⟨s2, hsteps2, hQ⟩ := h2 s1 hsteps1.keepsFrozen hsteps1.symtab_eq hP
    exact ⟨s2, hsteps1.trans hsteps2, hQ⟩
  · exact ⟨s1, hsteps1, Or.inr (Or.inl hPan)⟩
  · exact ⟨s1, hsteps1, Or.inr (Or.inr hOom)⟩

/-- Run a `SepWP` segment and continue in `ReachesOrPanicOom`. -/
theorem of_sepWP {prog : Program} {Pan : State → State → SepProp}
    {R : SepProp} {s0 s : State} {target : BitVec 64} {Pre Frame : SepProp}
    {PostWP : State → SepProp → Prop} {oom : State → SepProp} {Q : State → Prop}
    (hwp : SepWP prog target s Pre PostWP oom)
    (hmem : s.mem ⊨ Pre ∗ (Frame ∗ R)) (hL : prog.CodeLoaded s.mem)
    (hcont : ∀ s1 P_out, s1.pc = target → s1.status = .Running →
      s.mem.KeepsFrozen s1.mem → s1.symtab = s.symtab → prog.CodeLoaded s1.mem →
      (s1.mem ⊨ P_out ∗ (Frame ∗ R)) → PostWP s1 P_out →
      ReachesOrPanicOom prog Pan R s0 s1 Q)
    (hoom : ∀ s1, s1.status = .OutOfMemory →
      (s1.mem ⊨ oom s1 ∗ (Frame ∗ R)) → (s1.mem ⊨ ⌜OomPreserved s0 s1⌝ ∗ R) := by
        intro _ _ hm; exact False.elim (not_satisfies_false_sepConj hm)) :
    ReachesOrPanicOom prog Pan R s0 s Q := by
  obtain ⟨s1, hsteps1, ⟨hpc1, hrun1, P_out, hm1, hpost1⟩ | ⟨ho1, hmo1⟩⟩ := hwp.elim hmem hL
  · have hkf1 := hsteps1.keepsFrozen
    have hL1 := hL.of_keepsFrozen hkf1
    obtain ⟨s2, hsteps2, hQ⟩ := hcont s1 P_out hpc1 hrun1 hkf1 hsteps1.symtab_eq hL1 hm1 hpost1
    exact ⟨s2, hsteps1.trans hsteps2, hQ⟩
  · exact ⟨s1, hsteps1, Or.inr (Or.inr ⟨ho1, hoom s1 ho1 hmo1⟩)⟩

/-- Call a non-panicking, OOM-free subroutine and continue in `ReachesOrPanicOom`. -/
theorem of_call_no_panic {α : Type} {prog : Program} {Pan : State → State → SepProp}
    {R : SepProp} {s0 s : State} {entry ret_pc : BitVec 64}
    {spec : Spec α} {arg : α} {Frame : SepProp} {Q : State → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (hpre : s.mem ⊨ spec.pre arg s ∗ (Frame ∗ R)) (hL : prog.CodeLoaded s.mem)
    (hpan_false : ∀ sf, spec.onPanic arg s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit arg code s sf = ⌜False⌝ := by intros; rfl)
    (hcont : ∀ s1, s1.pc = ret_pc → s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      CalleeSavedPreserved s s1 → s.mem.KeepsFrozen s1.mem → s1.symtab = s.symtab →
      prog.CodeLoaded s1.mem → (s1.mem ⊨ spec.post arg s s1 ∗ (Frame ∗ R)) →
      ReachesOrPanicOom prog Pan R s0 s1 Q)
    (hoom_false : ∀ sf, spec.onOom arg s sf = ⌜False⌝ := by intro _; rfl) :
    ReachesOrPanicOom prog Pan R s0 s Q := by
  obtain ⟨s1, hsteps1, hout, -⟩ :=
    hcall.no_fault_before_outcome arg (Frame ∗ R) s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpc1, hsp1, hrun1⟩, ⟨_, hcs1⟩, hpost1⟩ | ⟨_, hpost1⟩ | ⟨code, _, hpost1⟩ | ⟨_, hpost1⟩
  · rw [show Reg.lr = Reg.x30 from rfl, hlr] at hpc1
    have hkf1 := hsteps1.keepsFrozen
    have hsp_align1 : s1.spAligned = true := by unfold State.spAligned at hsp ⊢; rw [hsp1]; exact hsp
    obtain ⟨s2, hsteps2, hQ⟩ :=
      hcont s1 hpc1 hrun1 hsp1 hsp_align1 hcs1 hkf1 hsteps1.symtab_eq (hL.of_keepsFrozen hkf1) hpost1
    exact ⟨s2, hsteps1.trans hsteps2, hQ⟩
  · rw [hpan_false s1, satisfies_pure_sepConj] at hpost1; exact False.elim hpost1.1
  · rw [hexit_false code s1, satisfies_pure_sepConj] at hpost1; exact False.elim hpost1.1
  · rw [hoom_false s1, satisfies_pure_sepConj] at hpost1; exact False.elim hpost1.1

/-- Call a non-panicking subroutine with `onOom = ⌜OomPreserved s sf⌝` and continue in
`ReachesOrPanicOom`. -/
theorem of_call_oom {α : Type} {prog : Program} {Pan : State → State → SepProp}
    {R : SepProp} {s0 s : State} {entry ret_pc : BitVec 64}
    {spec : Spec α} {arg : α} {Frame : SepProp} {Q : State → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 .x30 = ret_pc) (hoom0 : OomPreserved s0 s)
    (hpre : s.mem ⊨ spec.pre arg s ∗ (Frame ∗ R)) (hL : prog.CodeLoaded s.mem)
    (hpan_false : ∀ sf, spec.onPanic arg s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit arg code s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom arg s sf = ⌜OomPreserved s sf⌝ := by intro _; rfl)
    (hcont : ∀ s1, s1.pc = ret_pc → s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      CalleeSavedPreserved s s1 → s.mem.KeepsFrozen s1.mem → s1.symtab = s.symtab →
      prog.CodeLoaded s1.mem → (s1.mem ⊨ spec.post arg s s1 ∗ (Frame ∗ R)) →
      ReachesOrPanicOom prog Pan R s0 s1 Q) :
    ReachesOrPanicOom prog Pan R s0 s Q := by
  obtain ⟨s1, hsteps1, hout, -⟩ :=
    hcall.no_fault_before_outcome arg (Frame ∗ R) s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpc1, hsp1, hrun1⟩, ⟨_, hcs1⟩, hpost1⟩ | ⟨_, hpost1⟩ | ⟨code, _, hpost1⟩ | ⟨hoom1, hpost1⟩
  · rw [show Reg.lr = Reg.x30 from rfl, hlr] at hpc1
    have hkf1 := hsteps1.keepsFrozen
    have hsp_align1 : s1.spAligned = true := by unfold State.spAligned at hsp ⊢; rw [hsp1]; exact hsp
    obtain ⟨s2, hsteps2, hQ⟩ :=
      hcont s1 hpc1 hrun1 hsp1 hsp_align1 hcs1 hkf1 hsteps1.symtab_eq (hL.of_keepsFrozen hkf1) hpost1
    exact ⟨s2, hsteps1.trans hsteps2, hQ⟩
  · rw [hpan_false s1, satisfies_pure_sepConj] at hpost1; exact False.elim hpost1.1
  · rw [hexit_false code s1, satisfies_pure_sepConj] at hpost1; exact False.elim hpost1.1
  · rw [hoom_eq s1] at hpost1
    exact ⟨s1, hsteps1, Or.inr (Or.inr ⟨hoom1, oom_frame_trans hoom0 hpost1⟩)⟩

/-- Call a subroutine that may both panic and stop in `.OutOfMemory` (e.g. `grow_one`). -/
theorem of_call_alloc_panic {α : Type} {prog : Program} {Pan : State → State → SepProp}
    {R : SepProp} {s0 s : State} {entry ret_pc : BitVec 64}
    {spec : Spec α} {arg : α} {Frame : SepProp} {Q : State → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 .x30 = ret_pc) (hoom0 : OomPreserved s0 s)
    (hpre : s.mem ⊨ spec.pre arg s ∗ (Frame ∗ R)) (hL : prog.CodeLoaded s.mem)
    (hpan : ∀ s1, s1.status = .Panicked →
      (s1.mem ⊨ spec.onPanic arg s s1 ∗ (Frame ∗ R)) → (s1.mem ⊨ Pan s0 s1 ∗ R))
    (hexit_false : ∀ code sf, spec.onExit arg code s sf = ⌜False⌝ := by intros; rfl)
    (hcont : ∀ s1, s1.pc = ret_pc → s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      CalleeSavedPreserved s s1 → s.mem.KeepsFrozen s1.mem → s1.symtab = s.symtab →
      prog.CodeLoaded s1.mem → (s1.mem ⊨ spec.post arg s s1 ∗ (Frame ∗ R)) →
      ReachesOrPanicOom prog Pan R s0 s1 Q)
    (hoom_eq : ∀ sf, spec.onOom arg s sf = ⌜OomPreserved s sf⌝ := by intro _; rfl) :
    ReachesOrPanicOom prog Pan R s0 s Q := by
  obtain ⟨s1, hsteps1, hout, -⟩ :=
    hcall.no_fault_before_outcome arg (Frame ∗ R) s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpc1, hsp1, hrun1⟩, ⟨_, hcs1⟩, hpost1⟩ | ⟨hpan1, hpost1⟩ | ⟨code, _, hpost1⟩ | ⟨hoom1, hpost1⟩
  · rw [show Reg.lr = Reg.x30 from rfl, hlr] at hpc1
    have hkf1 := hsteps1.keepsFrozen
    have hsp_align1 : s1.spAligned = true := by unfold State.spAligned at hsp ⊢; rw [hsp1]; exact hsp
    obtain ⟨s2, hsteps2, hQ⟩ :=
      hcont s1 hpc1 hrun1 hsp1 hsp_align1 hcs1 hkf1 hsteps1.symtab_eq (hL.of_keepsFrozen hkf1) hpost1
    exact ⟨s2, hsteps1.trans hsteps2, hQ⟩
  · exact ⟨s1, hsteps1, Or.inr (Or.inl ⟨hpan1, hpan s1 hpan1 hpost1⟩)⟩
  · rw [hexit_false code s1, satisfies_pure_sepConj] at hpost1; exact False.elim hpost1.1
  · rw [hoom_eq s1] at hpost1
    exact ⟨s1, hsteps1, Or.inr (Or.inr ⟨hoom1, oom_frame_trans hoom0 hpost1⟩)⟩

/-- Close `ReachesOrPanicOom` at a `Rust.panicked` extern hook. -/
theorem of_panic_extern {prog : Program} {Pan : State → State → SepProp}
    {R : SepProp} {s0 s : State} {Q : State → Prop}
    (hrun : s.status = .Running) (hext : prog.externAt? s.pc = some Rust.panicked)
    (hpan : (Rust.panicked s).mem ⊨ Pan s0 (Rust.panicked s) ∗ R) :
    ReachesOrPanicOom prog Pan R s0 s Q :=
  ⟨Rust.panicked s,
    Steps.step (Step.extern hrun hext (Memory.KeepsFrozen.refl _)) (Steps.refl _),
    Or.inr (Or.inl ⟨rfl, hpan⟩)⟩

/-- Convert a completed `ReachesOrPanicOom` proof into `reaches_outcome prog spec x R s0 s`. -/
theorem to_reaches_outcome {α : Type} {prog : Program} {spec : Spec α} {x : α}
    {R : SepProp} {s0 s : State} {Q : State → Prop}
    (h : prog.CodeLoaded s.mem → ReachesOrPanicOom prog (spec.onPanic x) R s0 s Q)
    (hret : ∀ sf, Q sf → Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
      (sf.mem ⊨ spec.post x s0 sf ∗ R))
    (hoom : ∀ sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ ⌜OomPreserved s0 sf⌝ ∗ R) → (sf.mem ⊨ spec.onOom x s0 sf ∗ R) := by
        intro _ _ hm; exact hm) :
    reaches_outcome prog spec x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  rcases h hL with ⟨sf, hsteps, hQ | ⟨hp, hmp⟩ | ⟨ho, hmo⟩⟩
  · obtain ⟨hr, hcc, hmp⟩ := hret sf hQ
    exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inl ⟨hr, hcc, hmp⟩))
  · exact reaches_outcome_of_panic_steps hsteps hp hmp
  · exact reaches_outcome_of_oom_steps hsteps ho (hoom sf ho hmo)

end ReachesOrPanicOom

/-! ### `OomPreserved ∧ PoolPreserved` Extern-Hook Leaf Wrappers -/

/-- Enrich any `Spec α` with `⌜OomPreserved s0 sf ∧ PoolPreserved s0 sf⌝` on normal return,
leaving `pre`, `onPanic`, `onExit`, and `onOom` unchanged. -/
def withOomPoolPreserved {α : Type} (spec : Spec α) : Spec α where
  pre := spec.pre
  post := fun x s0 sf => ⌜OomPreserved s0 sf ∧ PoolPreserved s0 sf⌝ ∗ spec.post x s0 sf
  onPanic := spec.onPanic
  onExit := spec.onExit
  onOom := spec.onOom

@[simp] theorem withOomPoolPreserved_pre {α : Type} (spec : Spec α) (x : α) (s : State) :
    (withOomPoolPreserved spec).pre x s = spec.pre x s := rfl
@[simp] theorem withOomPoolPreserved_post {α : Type} (spec : Spec α) (x : α) (s0 sf : State) :
    (withOomPoolPreserved spec).post x s0 sf =
      (⌜OomPreserved s0 sf ∧ PoolPreserved s0 sf⌝ ∗ spec.post x s0 sf) := rfl
@[simp] theorem withOomPoolPreserved_onPanic {α : Type} (spec : Spec α) :
    (withOomPoolPreserved spec).onPanic = spec.onPanic := rfl
@[simp] theorem withOomPoolPreserved_onExit {α : Type} (spec : Spec α) :
    (withOomPoolPreserved spec).onExit = spec.onExit := rfl
@[simp] theorem withOomPoolPreserved_onOom {α : Type} (spec : Spec α) :
    (withOomPoolPreserved spec).onOom = spec.onOom := rfl

/-- Upgrade any `HookOk f spec` witness to `HookOk f (withOomPoolPreserved spec)` whenever `f`
preserves `OomPreserved` and `PoolPreserved` pointwise. -/
theorem hookOk_withOomPoolPreserved {α : Type} {f : State → State} {spec : Spec α}
    (hok : HookOk f spec)
    (hpres : ∀ s0, OomPreserved s0 (f s0) ∧ PoolPreserved s0 (f s0)) :
    HookOk f (withOomPoolPreserved spec) := by
  intro x R s0 hrun hpre hsp
  obtain ⟨hkf, hsym, hout⟩ := hok x R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withOomPoolPreserved]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpres s0, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-- `retHook g` preserves `OomPreserved` and `PoolPreserved` whenever `g` does. -/
theorem retHook_preserves_oom_pool {g : State → State}
    (hg : ∀ s, OomPreserved s (g s) ∧ PoolPreserved s (g s)) (s : State) :
    OomPreserved s (retHook g s) ∧ PoolPreserved s (retHook g s) := by
  have ⟨ho, hp⟩ := hg s
  dsimp only [retHook]
  exact ⟨(oomPreserved_setPC s (g s) _).mpr ho, PoolPreserved.trans hp ⟨rfl, rfl, rfl⟩⟩

/-- No-op shim specification (`__rustc::__rust_no_alloc_shim_is_unstable_v2` / compiler barrier)
exporting `OomPreserved s0 sf ∧ PoolPreserved s0 sf`. -/
def shimCliSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜OomPreserved s0 sf ∧ PoolPreserved s0 sf⌝

theorem hookNoop_shimCliSpec_ok : HookOk hookNoop shimCliSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  change s0.mem ⊨ emp ∗ R at hpre
  rw [emp_sepConj] at hpre
  change s0.mem ⊨ ⌜OomPreserved s0 (hookNoop s0) ∧ PoolPreserved s0 (hookNoop s0)⌝ ∗ R
  rw [satisfies_pure_sepConj]
  exact ⟨⟨by simp [hookNoop, retHook], ⟨rfl, rfl, rfl⟩⟩, hpre⟩

theorem subroutine_ok_shimCliSpec {prog : Program} {entry : BitVec 64}
    (hext : prog.externAt? entry = some hookNoop) :
    subroutine_ok prog entry shimCliSpec :=
  subroutine_ok_of_hookOk hext hookNoop_shimCliSpec_ok

/-- `subtle::black_box::<u8>` extern hook (`x0 := (x0.setWidth 8).zeroExtend 64; pc := lr`) and its
`OomPreserved ∧ PoolPreserved` specification. -/
def blackBoxU8Hook : State → State :=
  retHook fun s => s.writeReg64 .x0 (((s.readReg64 .x0).setWidth 8).zeroExtend 64)

def blackBoxU8CliSpec : Spec (BitVec 64) where
  pre := fun v s0 => ⌜s0.readReg64 .x0 = v⌝
  post := fun v s0 sf =>
    ⌜sf.readReg64 .x0 = (v.setWidth 8).zeroExtend 64 ∧
      OomPreserved s0 sf ∧ PoolPreserved s0 sf⌝

theorem blackBoxU8Hook_cli_ok : HookOk blackBoxU8Hook blackBoxU8CliSpec := by
  refine regHook_ok (fun s => s.writeReg64 .x0 (((s.readReg64 .x0).setWidth 8).zeroExtend 64))
    fun v R s0 hpre => ?_
  change s0.mem ⊨ ⌜s0.readReg64 .x0 = v⌝ ∗ R at hpre
  change s0.mem ⊨
    ⌜(blackBoxU8Hook s0).readReg64 .x0 = (v.setWidth 8).zeroExtend 64 ∧
      OomPreserved s0 (blackBoxU8Hook s0) ∧ PoolPreserved s0 (blackBoxU8Hook s0)⌝ ∗ R
  rw [satisfies_pure_sepConj] at hpre ⊢
  refine ⟨⟨?_, ?_, ⟨rfl, rfl, rfl⟩⟩, hpre.2⟩
  · dsimp only [blackBoxU8Hook]
    rw [retHook_writeReg64_x0, hpre.1]
  · simp [blackBoxU8Hook, retHook]

/-- Thin `OomPreserved ∧ PoolPreserved` wrappers around `ProofLib.Hoare.LibcHooks`'s `memcpy`,
`memmove`, `memset`, and `fieldHook` / `fieldHook64` contracts. -/
abbrev memcpyRegionCliSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  withOomPoolPreserved memcpyRegionSpec

abbrev libcMemcpyCliSpec (hookStack : Nat := 4096) : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  withOomPoolPreserved (libcMemcpySpec hookStack)

abbrev libcMemmoveCliSpec (hookStack : Nat := 4096) :
    Spec (BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) :=
  withOomPoolPreserved (libcMemmoveSpec hookStack)

/-- Flat-pure `memmove` specification preserving `OomPreserved` and `PoolPreserved`. -/
def sessionMemmoveCliSpec (hookStack : Nat := 4096) :
    Spec (BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) where
  pre := (libcMemmoveSpec hookStack).pre
  post := fun (base, buf, dst, src, len) s0 sf =>
    ⌜sf.readReg64 .x0 = base + BitVec.ofNat 64 dst ∧ OomPreserved s0 sf ∧ PoolPreserved s0 sf⌝ ∗
      (base ↦ₛ listMove buf dst src len) ∗ stackAt s0.sp hookStack

abbrev memsetRegionCliSpec : Spec (BitVec 64 × BitVec 8 × Nat) :=
  withOomPoolPreserved memsetRegionSpec

abbrev libcMemsetCliSpec (hookStack : Nat := 4096) : Spec (BitVec 64 × BitVec 8 × Nat) :=
  withOomPoolPreserved (libcMemsetSpec hookStack)

theorem hookMemcpy_preserves_oom_pool (s : State) :
    OomPreserved s (hookMemcpy s) ∧ PoolPreserved s (hookMemcpy s) :=
  retHook_preserves_oom_pool (fun s' => ⟨by simp, ⟨rfl, rfl, rfl⟩⟩) s

theorem hookMemset_preserves_oom_pool (s : State) :
    OomPreserved s (hookMemset s) ∧ PoolPreserved s (hookMemset s) :=
  retHook_preserves_oom_pool (fun s' => ⟨by simp, ⟨rfl, rfl, rfl⟩⟩) s

theorem hookMemcpy_region_cli_ok : HookOk hookMemcpy memcpyRegionCliSpec :=
  hookOk_withOomPoolPreserved hookMemcpy_region_ok hookMemcpy_preserves_oom_pool

theorem hookMemcpy_cli_ok (hookStack : Nat := 4096) :
    HookOk hookMemcpy (libcMemcpyCliSpec hookStack) :=
  hookOk_withOomPoolPreserved (hookMemcpy_ok hookStack) hookMemcpy_preserves_oom_pool

theorem hookMemmove_cli_ok (hookStack : Nat := 4096) :
    HookOk hookMemmove (libcMemmoveCliSpec hookStack) :=
  hookOk_withOomPoolPreserved (hookMemmove_ok hookStack) hookMemcpy_preserves_oom_pool

theorem hookMemmove_session_cli_ok (hookStack : Nat := 4096) :
    HookOk hookMemmove (sessionMemmoveCliSpec hookStack) := by
  intro ⟨base, buf, dst, src, len⟩ R s0 hrun hpre hsp
  obtain ⟨hkf, hsym, hout⟩ :=
    hookMemmove_cli_ok hookStack (base, buf, dst, src, len) R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change (hookMemmove s0).mem ⊨
      (⌜OomPreserved s0 (hookMemmove s0) ∧ PoolPreserved s0 (hookMemmove s0)⌝ ∗
        (⌜(hookMemmove s0).readReg64 .x0 = base + BitVec.ofNat 64 dst⌝ ∗
          (base ↦ₛ listMove buf dst src len) ∗ stackAt s0.sp hookStack)) ∗ R at hpost
    change (hookMemmove s0).mem ⊨
      (⌜(hookMemmove s0).readReg64 .x0 = base + BitVec.ofNat 64 dst ∧
        OomPreserved s0 (hookMemmove s0) ∧ PoolPreserved s0 (hookMemmove s0)⌝ ∗
        (base ↦ₛ listMove buf dst src len) ∗ stackAt s0.sp hookStack) ∗ R
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1.1, hpost.1.2⟩, hpost.2.2⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem hookMemset_region_cli_ok : HookOk hookMemset memsetRegionCliSpec :=
  hookOk_withOomPoolPreserved hookMemset_region_ok hookMemset_preserves_oom_pool

theorem hookMemset_cli_ok (hookStack : Nat := 4096) (hstack : 0 < hookStack := by decide) :
    HookOk hookMemset (libcMemsetCliSpec hookStack) :=
  hookOk_withOomPoolPreserved (hookMemset_ok hookStack hstack) hookMemset_preserves_oom_pool

theorem fieldHook_withOomPoolPreserved_ok {α : Type} {off : BitVec 64}
    {g : BitVec 32 → BitVec 32} {spec : Spec α} (hok : HookOk (fieldHook off g) spec) :
    HookOk (fieldHook off g) (withOomPoolPreserved spec) :=
  hookOk_withOomPoolPreserved hok <|
    retHook_preserves_oom_pool fun _ => ⟨by simp, ⟨rfl, rfl, rfl⟩⟩

theorem fieldHook64_withOomPoolPreserved_ok {α : Type} {off : BitVec 64}
    {g : BitVec 64 → BitVec 64} {spec : Spec α} (hok : HookOk (fieldHook64 off g) spec) :
    HookOk (fieldHook64 off g) (withOomPoolPreserved spec) :=
  hookOk_withOomPoolPreserved hok <|
    retHook_preserves_oom_pool fun _ => ⟨by simp, ⟨rfl, rfl, rfl⟩⟩

/-! ## Normalization Regression Checks -/

section SimpRegressionTests

private theorem test_oomPreserved_two_sided_wp (s0 : State) (m1 m2 : Memory)
    (v0 v1 pc : BitVec 64) (q0 : BitVec 128) (ps : PState) (f : BitVec 32) :
    OomPreserved
      ((((s0.writeReg64 .sp v0).setMem m1).writeReg64 .x0 v1).advancePC)
      ((((((s0.writeReg64 .x1 v0).writeVReg128 0#5 q0).setMem m2).setPState ps).orFpsr f).setPC pc) := by
  simp only [wp_norm]

private theorem test_oomPreserved_two_sided_simp (s0 : State) (m1 m2 : Memory)
    (v0 v1 pc : BitVec 64) (q0 : BitVec 128) (ps : PState) (f : BitVec 32) :
    OomPreserved
      ((((s0.writeReg64 .sp v0).setMem m1).writeReg64 .x0 v1).advancePC)
      ((((((s0.writeReg64 .x1 v0).writeVReg128 0#5 q0).setMem m2).setPState ps).orFpsr f).setPC pc) := by
  simp

private theorem test_oomPreserved_two_sided_arm64 (s0 : State) (m1 m2 : Memory)
    (v0 v1 pc : BitVec 64) (q0 : BitVec 128) (ps : PState) (f : BitVec 32) :
    OomPreserved
      ((((s0.writeReg64 .sp v0).setMem m1).writeReg64 .x0 v1).advancePC)
      ((((((s0.writeReg64 .x1 v0).writeVReg128 0#5 q0).setMem m2).setPState ps).orFpsr f).setPC pc) := by
  simp only [arm64_norm]

private theorem test_poolPreserved_two_sided (s0 : State) (m1 m2 : Memory)
    (v0 v1 pc : BitVec 64) (q0 : BitVec 128) (ps : PState) (f : BitVec 32) :
    PoolPreserved
      (((s0.writeReg64 .sp v0).setMem m1).advancePC)
      ((((((s0.writeReg64 .x0 v1).writeVReg128 1#5 q0).setMem m2).setPState ps).setFpsr f).setPC pc) := by
  simp only [PoolPreserved, wp_norm, and_self]

private theorem test_allocCallPreserved_step_both (s0 sf : State) (m1 m2 : Memory)
    (v0 v1 pc : BitVec 64) (q0 : BitVec 128) (f : BitVec 32)
    (h : AllocCallPreserved s0 sf) :
    AllocCallPreserved
      (((s0.writeReg64 .sp v0).setMem m1).advancePC)
      ((((sf.writeReg64 .x0 v1).writeVReg128 0#5 q0).setMem m2).orFpsr f |>.setPC pc) := by
  simpa only [wp_norm] using h

private theorem test_pool_and_repAlloc_wp_norm (A : RustCliAlloc) (s : State) (m : Memory)
    (v : BitVec 64) (q : BitVec 128) (f : BitVec 32) (evs : List TraceEvent) :
    A.pool (((((s.writeReg64 .x0 v).writeVReg128 0#5 q).setMem m).orFpsr f).appendTrace evs) = A.pool s ∧
      A.repAlloc.pool = emp ∧
      A.repAlloc.live = A.live ∧
      (A.atState s).pool = A.pool s := by
  simp only [wp_norm, and_self]

end SimpRegressionTests

end LibsignalBinary.Heap.IfaceSimp
