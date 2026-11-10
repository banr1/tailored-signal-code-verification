/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Exec
public import ProofLib.Disproof.StrictHook
import Arm64.Trusted.Spec.SepLogic

/-!
# Fault-Reachability Rules

Defines the `ReachesException` reachability predicate, single-step composition lemmas along
`Step` and `Steps` for refuting `safe_subroutine_ok`, and fault-introduction rules for non-writable
stores (`storeAccess?`) and invalid strict external hook calls.
-/

@[expose] public section

namespace ProofLib.Disproof

open Arm64 ProofLib

/-! ## `ReachesException` Judgment and Composition Rules -/

/-- Execution of `prog` starting from state `s` reaches a terminal `.Exception msg` state. -/
def ReachesException (prog : Program) (s : State) : Prop :=
  ∃ sf msg, Steps prog s sf ∧ sf.status = .Exception msg

/-- A state already in `.Exception msg` satisfies `ReachesException` in 0 steps. -/
theorem ReachesException.of_exception {prog : Program} {s : State} {msg : String}
    (h : s.status = .Exception msg) : ReachesException prog s :=
  ⟨s, msg, .refl s, h⟩

/-- Prepend a single `Step` to a `ReachesException` derivation. -/
theorem ReachesException.of_step {prog : Program} {s s' : State}
    (hstep : Step prog s s') (hrest : ReachesException prog s') :
    ReachesException prog s := by
  obtain ⟨sf, msg, hsteps, hexc⟩ := hrest
  exact ⟨sf, msg, .step hstep hsteps, hexc⟩

/-- Prepend a single instruction execution `Step.exec` (`prog.fetch s.pc = some inst`) to
    `ReachesException`. -/
theorem ReachesException.of_fetch_step {prog : Program} {s : State} {inst : Instr}
    (hrun : s.status = .Running)
    (hcode : prog.CodeLoaded s.mem)
    (hfetch : prog.fetch s.pc = some inst)
    (hrest : ReachesException prog (prog.evalInst inst s)) :
    ReachesException prog s :=
  ReachesException.of_step (Step.exec hrun (Program.fetchMem_of_fetch hcode hfetch)) hrest

/-- Prepend a single external hook execution `Step.extern` (`prog.externAt? s.pc = some hook`) to
    `ReachesException`. -/
theorem ReachesException.of_extern_step {prog : Program} {s : State} {hook : State → State}
    (hrun : s.status = .Running := by with_unfolding_all rfl)
    (hextern : prog.externAt? s.pc = some hook := by with_unfolding_all rfl)
    (hkeep : s.mem.KeepsFrozen (hook s).mem := by exact Memory.KeepsFrozen.refl _)
    (hsym : (hook s).symtab = s.symtab := by with_unfolding_all rfl)
    (hrest : ReachesException prog (hook s)) :
    ReachesException prog s :=
  ReachesException.of_step (Step.extern hrun hextern hkeep hsym) hrest

/-- Every instruction execution preserves `prog.CodeLoaded`. -/
theorem Program.CodeLoaded.evalInst {prog : Program} {s : State} (inst : Instr)
    (hL : prog.CodeLoaded s.mem) : prog.CodeLoaded (prog.evalInst inst s).mem :=
  hL.of_keepsFrozen (evalInst_keepsFrozen prog inst s)

/-- Every `execInst` execution preserves `prog.CodeLoaded`. -/
theorem Program.CodeLoaded.execInst {prog : Program} {s : State} (inst : Instr)
    (hL : prog.CodeLoaded s.mem) : prog.CodeLoaded (execInst inst s).mem :=
  hL.of_keepsFrozen (execInst_keepsFrozen inst s)

/-- Decode the instruction at `s.pc` with a default fallback (`NOP`), avoiding proof terms inside
    state expressions so `decide` and `rfl` reduce cleanly. -/
def fetchInstD (prog : Program) (s : State) : Instr :=
  (prog.fetch s.pc).getD .nop

theorem fetch_eq_some_fetchInstD {prog : Program} {s : State}
    (hsome : (prog.fetch s.pc).isSome = true) :
    prog.fetch s.pc = some (fetchInstD prog s) := by
  unfold fetchInstD
  cases h : prog.fetch s.pc with
  | none => rw [h] at hsome; contradiction
  | some inst => rfl

theorem stepInst_eq_evalInst_fetchInstD {prog : Program} {s : State}
    (hsome : (prog.fetch s.pc).isSome = true) :
    ProofLib.stepInst prog s = prog.evalInst (fetchInstD prog s) s := by
  unfold ProofLib.stepInst fetchInstD
  cases h : prog.fetch s.pc with
  | none => rw [h] at hsome; contradiction
  | some inst => rfl

abbrev stepInst_eq_execInst_fetchInstD := @stepInst_eq_evalInst_fetchInstD

/-- Every `ProofLib.stepInst` preserves `prog.CodeLoaded`. -/
theorem Program.CodeLoaded.stepInst {prog : Program} {s : State}
    (hL : prog.CodeLoaded s.mem) : prog.CodeLoaded (ProofLib.stepInst prog s).mem := by
  unfold ProofLib.stepInst
  split
  · exact Program.CodeLoaded.evalInst _ hL
  · exact hL

/-- Prepend a single instruction execution `Step.exec` (`ProofLib.stepInst prog s`) to
    `ReachesException`, automatically decoding `prog.fetch s.pc` (`by with_unfolding_all decide`)
    and threading `prog.CodeLoaded` into the continuation. -/
theorem ReachesException.of_exec_step {prog : Program} {s : State}
    (hrun : s.status = .Running := by with_unfolding_all rfl)
    (hcode : prog.CodeLoaded s.mem)
    (hsome : (prog.fetch s.pc).isSome = true := by with_unfolding_all decide)
    (hrest : prog.CodeLoaded (ProofLib.stepInst prog s).mem →
      ReachesException prog (ProofLib.stepInst prog s)) :
    ReachesException prog s := by
  have hrest' := hrest (Program.CodeLoaded.stepInst hcode)
  rw [stepInst_eq_evalInst_fetchInstD hsome] at hrest'
  exact ReachesException.of_fetch_step hrun hcode (fetch_eq_some_fetchInstD hsome) hrest'

/-- Prepend a single instruction execution `Step.exec` (`prog.fetch s.pc = some inst`) to `Steps`. -/
theorem Steps.of_fetch_step {prog : Program} {s sf : State} {inst : Instr}
    (hrun : s.status = .Running)
    (hcode : prog.CodeLoaded s.mem)
    (hfetch : prog.fetch s.pc = some inst)
    (hrest : Steps prog (prog.evalInst inst s) sf) :
    Steps prog s sf :=
  Steps.step (Step.exec hrun (Program.fetchMem_of_fetch hcode hfetch)) hrest

/-- Prepend a single instruction execution `Step.exec` (`ProofLib.stepInst prog s`) to `Steps`,
    automatically decoding `prog.fetch s.pc` (`by with_unfolding_all decide`) and threading
    `prog.CodeLoaded`. -/
theorem Steps.of_exec_step {prog : Program} {s sf : State}
    (hrun : s.status = .Running := by with_unfolding_all rfl)
    (hcode : prog.CodeLoaded s.mem)
    (hsome : (prog.fetch s.pc).isSome = true := by with_unfolding_all decide)
    (hrest : prog.CodeLoaded (ProofLib.stepInst prog s).mem →
      Steps prog (ProofLib.stepInst prog s) sf) :
    Steps prog s sf := by
  have hrest' := hrest (Program.CodeLoaded.stepInst hcode)
  rw [stepInst_eq_evalInst_fetchInstD hsome] at hrest'
  exact Steps.of_fetch_step hrun hcode (fetch_eq_some_fetchInstD hsome) hrest'

/-- Refute `safe_subroutine_ok prog entry_pc spec` from `ReachesException prog s0`. -/
theorem ReachesException.not_safe_subroutine_ok {α : Type}
    {prog : Program} {entry_pc : BitVec 64} {spec : Spec α}
    (x : α) (R : SepProp) {s0 : State}
    (hentry : AapcsEntry s0 entry_pc)
    (hcode : prog.CodeLoaded s0.mem)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R)
    (hexc : ReachesException prog s0)
    (hlr : HaltsAtReturn prog s0 := by
      first
      | exact HaltsAtReturn.of_unaligned (by decide) (by decide)
      | exact HaltsAtReturn.of_unaligned rfl (by decide)) :
    ¬ safe_subroutine_ok prog entry_pc spec := by
  obtain ⟨sf, msg, hsteps, hst⟩ := hexc
  exact not_safe_subroutine_ok_of_exception x R hentry hcode hpre hsteps hst hlr

/-! ## Permission Preservation Across Stores and Hooks -/

@[simp]
theorem perm_execStr (size : MemWidth) (rt : Reg) (addr : AddrMode) (s : State) :
    (execStr size rt addr s).mem.perm = s.mem.perm := by
  simp only [execStr]
  repeat' split
  all_goals simp [State.setStatus, State.advancePC, State.writeReg64, State.setMem]

@[simp]
theorem perm_execStp (w : Width) (rt1 rt2 : Reg) (addr : AddrMode) (s : State) :
    (execStp w rt1 rt2 addr s).mem.perm = s.mem.perm := by
  simp only [execStp]
  repeat' split
  all_goals simp [State.setStatus, State.advancePC, State.writeReg64, State.setMem]

@[simp]
theorem perm_retHook (f : State → State) (s : State) :
    (retHook f s).mem.perm = (f s).mem.perm := rfl

@[simp]
theorem perm_hookNoop (s : State) :
    (hookNoop s).mem.perm = s.mem.perm := rfl

@[simp]
theorem perm_hookReturnZero (s : State) :
    (hookReturnZero s).mem.perm = s.mem.perm := rfl

@[simp]
theorem perm_witnessAlloc (slotAddr : BitVec 64) (s : State) :
    (witnessAlloc slotAddr s).mem.perm = s.mem.perm := rfl

@[simp]
theorem perm_hookMemcpy (s : State) :
    (hookMemcpy s).mem.perm = s.mem.perm := by
  simp [hookMemcpy, retHook, State.setPC, State.setMem]

@[simp]
theorem perm_hookMemset (s : State) :
    (hookMemset s).mem.perm = s.mem.perm := by
  simp [hookMemset, retHook, State.setPC, State.setMem]

/-! ## Unmapped and Non-Writable Permission Refutation -/

theorem canWrite_false_of_offset_perm_not_w {m : Memory} {ea : BitVec 64} {n i : Nat}
    (hi : i < n) (hperm : (m.perm (ea + BitVec.ofNat 64 i)).w = false) :
    m.canWrite ea n = false := by
  rw [Bool.eq_false_iff]
  intro hcw
  unfold Memory.canWrite at hcw
  rw [Memory.allPerm_iff] at hcw
  have hi_ok := hcw i hi
  rw [hperm] at hi_ok
  cases hi_ok

theorem canWrite_false_of_inRegion_perm_not_w {m : Memory} {ea a : BitVec 64} {n : Nat}
    (ha : InRegion ea n a) (hperm : (m.perm a).w = false) :
    m.canWrite ea n = false := by
  have hi : (a - ea).toNat < n := ha
  have heq : ea + BitVec.ofNat 64 (a - ea).toNat = a := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_arith
  exact canWrite_false_of_offset_perm_not_w hi (by rwa [heq])

/-! ## Store and Hook Fault Introduction -/

/-- Effective address and total byte width of a general-purpose store instruction
    (`STR`, `STUR`, `STRB`, `STURB`, `STRH`, `STURH`, `STP`). -/
def storeAccess? (inst : Instr) (s : State) : Option (BitVec 64 × Nat) :=
  match inst with
  | .str sz _ dst   => some ((evalAddrMode s dst).1, sz.bytes)
  | .stp w _ _ dst  => some ((evalAddrMode s dst).1, 2 * (w : MemWidth).bytes)
  | _               => none

theorem execStr_exception_of_canWrite_false (size : MemWidth)
    (rt : Reg) (addr : AddrMode) (s : State)
    (hcw : s.mem.canWrite (evalAddrMode s addr).1 size.bytes = false) :
    ∃ msg, (execStr size rt addr s).status = .Exception msg := by
  unfold execStr
  by_cases hsp : (!checkAddrSPAligned s addr) = true
  · simp [hsp]
  · simp [hsp, hcw]

theorem execStp_exception_of_inRegion_perm_not_w (w : Width)
    (rt1 rt2 : Reg) (addr : AddrMode) (s : State) {a : BitVec 64}
    (ha : InRegion (evalAddrMode s addr).1 (2 * (w : MemWidth).bytes) a)
    (hperm : (s.mem.perm a).w = false) :
    ∃ msg, (execStp w rt1 rt2 addr s).status = .Exception msg := by
  unfold execStp
  by_cases hsp : (!checkAddrSPAligned s addr) = true
  · simp [hsp]
  · cases w with
    | W32 =>
      rcases (IsBlock.inRegion_append (a := (evalAddrMode s addr).1) (n := 4) (k := 4) (x := a) rfl (by decide)).1.mp ha with h1 | h2
      · have hcw := canWrite_false_of_inRegion_perm_not_w h1 hperm
        simp [hsp, hcw, MemWidth.bytes]
      · have hcw := canWrite_false_of_inRegion_perm_not_w h2 hperm
        simp [hsp, hcw, MemWidth.bytes]
    | W64 =>
      rcases (IsBlock.inRegion_append (a := (evalAddrMode s addr).1) (n := 8) (k := 8) (x := a) rfl (by decide)).1.mp ha with h1 | h2
      · have hcw := canWrite_false_of_inRegion_perm_not_w h1 hperm
        simp [hsp, hcw, MemWidth.bytes]
      · have hcw := canWrite_false_of_inRegion_perm_not_w h2 hperm
        simp [hsp, hcw, MemWidth.bytes]

theorem storeAccess_pos {inst : Instr} {s : State} {ea : BitVec 64} {n : Nat}
    (h : storeAccess? inst s = some (ea, n)) : 0 < n := by
  unfold storeAccess? at h
  split at h <;> (try cases h) <;> first | (cases ‹MemWidth› <;> decide) | (cases ‹Width› <;> decide)

theorem execInst_exception_of_store_inRegion_perm_not_w {prog : Program} {inst : Instr} {s : State}
    {ea a : BitVec 64} {n : Nat}
    (hstore : storeAccess? inst s = some (ea, n))
    (ha : InRegion ea n a)
    (hperm : (s.mem.perm a).w = false) :
    ∃ msg, (prog.evalInst inst s).status = .Exception msg := by
  unfold storeAccess? at hstore
  split at hstore
  all_goals try cases hstore
  · exact execStr_exception_of_canWrite_false _ _ _ _ (canWrite_false_of_inRegion_perm_not_w ha hperm)
  · exact execStp_exception_of_inRegion_perm_not_w _ _ _ _ _ ha hperm

/-- Introduce `ReachesException` from a store whose footprint contains a non-writable byte `a`. -/
theorem ReachesException.of_store_not_rw_inRegion {prog : Program} {s : State}
    {inst : Instr} {ea a : BitVec 64} {n : Nat}
    (hrun : s.status = .Running)
    (hcode : prog.CodeLoaded s.mem)
    (hfetch : prog.fetch s.pc = some inst)
    (hstore : storeAccess? inst s = some (ea, n))
    (ha : InRegion ea n a)
    (hperm : (s.mem.perm a).w = false) :
    ReachesException prog s := by
  have hfm : prog.fetchMem s.mem s.pc = some inst :=
    Program.fetchMem_of_fetch hcode hfetch
  obtain ⟨msg, hexc⟩ := execInst_exception_of_store_inRegion_perm_not_w hstore ha hperm
  exact ReachesException.of_step (Step.exec hrun hfm) (ReachesException.of_exception hexc)

/-- Introduce `ReachesException` from a store to a non-writable base address `ea`. -/
theorem ReachesException.of_store_not_rw {prog : Program} {s : State}
    {inst : Instr} {ea addr : BitVec 64} {n : Nat}
    (hrun : s.status = .Running)
    (hcode : prog.CodeLoaded s.mem)
    (hfetch : prog.fetch s.pc = some inst)
    (hstore : storeAccess? inst s = some (ea, n))
    (hperm : (s.mem.perm addr).w = false)
    (haddr : addr = ea := by rfl) :
    ReachesException prog s := by
  rw [haddr] at hperm
  have hpos : 0 < n := storeAccess_pos hstore
  have ha : InRegion ea n ea := by
    simp only [InRegion, BitVec.sub_self, BitVec.toNat_ofNat, Nat.zero_mod]
    exact hpos
  exact ReachesException.of_store_not_rw_inRegion hrun hcode hfetch hstore ha hperm

/-- Introduce `ReachesException` from a store to an unmapped base address `ea`. -/
theorem ReachesException.of_store_unmapped {prog : Program} {s : State}
    {inst : Instr} {ea addr : BitVec 64} {n : Nat}
    (hrun : s.status = .Running)
    (hcode : prog.CodeLoaded s.mem)
    (hfetch : prog.fetch s.pc = some inst)
    (hstore : storeAccess? inst s = some (ea, n))
    (hperm : s.mem.perm addr = .none)
    (haddr : addr = ea := by rfl) :
    ReachesException prog s := by
  refine ReachesException.of_store_not_rw hrun hcode hfetch hstore ?_ haddr
  rw [hperm]

/-- Introduce `ReachesException` from a store to an unmapped base address `ea`, decoding `prog.fetch s.pc` automatically. -/
theorem ReachesException.of_store_unmapped_at {prog : Program} {s : State}
    {m0 : Memory} {ea addr : BitVec 64} {n : Nat}
    (hrun : s.status = .Running := by with_unfolding_all rfl)
    (hcode : prog.CodeLoaded s.mem)
    (hsome : (prog.fetch s.pc).isSome = true := by with_unfolding_all decide)
    (hstore : storeAccess? (fetchInstD prog s) s = some (ea, n) := by with_unfolding_all rfl)
    (hperm : m0.perm addr = .none)
    (hmem : s.mem.perm addr = m0.perm addr := by with_unfolding_all rfl)
    (haddr : addr = ea := by with_unfolding_all rfl) :
    ReachesException prog s :=
  ReachesException.of_store_unmapped hrun hcode (fetch_eq_some_fetchInstD hsome) hstore
    (hmem.trans hperm) haddr

/-- Introduce `ReachesException` at a `strictHook` entry point when `¬ ValidHookCall calleeSpec s`. -/
theorem ReachesException.of_strict_hook_call {β : Type} {prog : Program} {s : State}
    {calleeSpec : Spec β} {fallback : State → State}
    (hrun : s.status = .Running := by with_unfolding_all rfl)
    (hextern : prog.externAt? s.pc = some (strictHook calleeSpec fallback) := by with_unfolding_all rfl)
    (hinvalid : ¬ ValidHookCall calleeSpec s) :
    ReachesException prog s := by
  have hstep := Step.of_strictHook_invalid hrun hextern hinvalid
  exact ReachesException.of_step hstep (ReachesException.of_exception rfl)

end ProofLib.Disproof
