/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64

/-!
# Frame Lemmas for Vectored `readv` and `writev`

Lifts invariants preserved by single-buffer `execRead` and `execWrite` across the `iovec` loop in
`execReadv` and `execWritev`. Any preorder `R : State → State → Prop` closed under register, `PC`,
and status updates (`RwvFrame R`) and preserved by the per-buffer step is preserved by the vectored
syscall.
-/

set_option autoImplicit false

@[expose] public section

namespace ProofLib

open Arm64

/-- Closure hypotheses for `execRwvCommon_preserves`: `R` is a preorder that tolerates every
    register / `PC` / status update `execRwvCommon` performs around its `step` calls. -/
structure RwvFrame (R : State → State → Prop) : Prop where
  refl   : ∀ s, R s s
  trans  : ∀ a b c, R a b → R b c → R a c
  reg    : ∀ s r v, R s (s.writeReg64 r v)
  pc     : ∀ s, R s s.advancePC
  status : ∀ s st, R s (s.setStatus st)
  regsPc : ∀ (s : State) regs pc, R s { s with regs := regs, pc := pc }

namespace RwvFrame

variable {R : State → State → Prop}

theorem retAdv (h : RwvFrame R) (s : State) (r : Reg) (v : BitVec 64) :
    R s ((s.writeReg64 r v).advancePC) :=
  h.trans _ _ _ (h.reg _ _ _) (h.pc _)

theorem restoreRet (h : RwvFrame R) (s : State) (regs : RegFile) (pc : BitVec 64)
    (r : Reg) (v : BitVec 64) :
    R s (({ s with regs := regs, pc := pc }.writeReg64 r v).advancePC) :=
  h.trans _ _ _ (h.regsPc _ _ _) (h.retAdv _ _ _)

theorem restoreSet (h : RwvFrame R) (s : State) (regs : RegFile) (pc : BitVec 64)
    (b l : BitVec 64) :
    R s (({ s with regs := regs, pc := pc }.writeReg64 Reg.x1 b).writeReg64 Reg.x2 l) :=
  h.trans _ _ _ (h.regsPc _ _ _) (h.trans _ _ _ (h.reg _ _ _) (h.reg _ _ _))

end RwvFrame

/-- `RwvFrame` for "projection `f` is unchanged", given that `f` ignores register writes, `PC`
    advance, status updates, and register-file / `PC` replacement. -/
theorem RwvFrame.eqOn {α : Sort _} (f : State → α)
    (hreg : ∀ s r v, f (s.writeReg64 r v) = f s) (hpc : ∀ s, f s.advancePC = f s)
    (hst : ∀ s st, f (s.setStatus st) = f s)
    (hrp : ∀ (s : State) regs pc, f { s with regs := regs, pc := pc } = f s) :
    RwvFrame (fun a b => f b = f a) where
  refl _ := rfl
  trans _ _ _ h1 h2 := h2.trans h1
  reg := hreg
  pc := hpc
  status := hst
  regsPc := hrp

/-- `execIovLoop` preserves any `RwvFrame` relation that `step` preserves. -/
theorem execIovLoop_preserves {R : State → State → Prop} (hR : RwvFrame R)
    (step : State → State) (hstep : ∀ s, R s (step s)) (s0 : State) :
    ∀ (segs : List (BitVec 64 × BitVec 64)) (s : State) (acc : Nat),
      R s (execIovLoop step s0 s acc segs) := by
  intro segs
  induction segs with
  | nil => intro s acc; exact hR.restoreRet _ _ _ _ _
  | cons seg rest ih =>
    intro s acc
    obtain ⟨base, len⟩ := seg
    have h1 := hR.trans _ _ _ (hR.restoreSet s s0.regs s0.pc base len) (hstep _)
    simp only [execIovLoop]
    split
    · split
      · split
        · exact hR.trans _ _ _ h1 (hR.restoreRet _ _ _ _ _)
        · exact hR.trans _ _ _ h1 (hR.status _ _)
      · split
        · exact hR.trans _ _ _ h1 (hR.restoreRet _ _ _ _ _)
        · exact hR.trans _ _ _ h1 (ih _ _)
    · exact h1

/-- An `.error` result of `readIovecs s vec n` is related to `s` by any `RwvFrame` relation. -/
theorem readIovecs_error_preserves {R : State → State → Prop} (hR : RwvFrame R) (s : State) :
    ∀ (n : Nat) (vec : BitVec 64) (s' : State), readIovecs s vec n = .error s' → R s s' := by
  intro n
  induction n with
  | zero => intro vec s' h; simp [readIovecs] at h
  | succ n ih =>
    intro vec s' h
    simp only [readIovecs] at h
    split at h
    · cases h; exact hR.retAdv _ _ _
    · split at h
      · cases h; exact hR.status _ _
      · split at h
        · cases h; exact hR.retAdv _ _ _
        · cases hrest : readIovecs s (vec + 16#64) n with
          | error e =>
            rw [hrest] at h
            simp only [Except.map] at h
            cases h
            exact ih _ _ hrest
          | ok l =>
            rw [hrest] at h
            simp [Except.map] at h

/-- `execRwvCommon step isRead` preserves any `RwvFrame` relation that `step` preserves. -/
theorem execRwvCommon_preserves {R : State → State → Prop} (hR : RwvFrame R)
    (step : State → State) (hstep : ∀ s, R s (step s)) (isRead : Bool) (s : State) :
    R s (execRwvCommon step isRead s) := by
  unfold execRwvCommon
  dsimp only
  repeat' split
  all_goals first
    | exact hR.retAdv _ _ _
    | exact hR.status _ _
    | exact readIovecs_error_preserves hR s _ _ _ ‹_›
    | exact execIovLoop_preserves hR step hstep s _ s 0

/-- `execReadv` preserves any `RwvFrame` relation that `execRead` preserves. -/
theorem execReadv_preserves {R : State → State → Prop} (hR : RwvFrame R)
    (hstep : ∀ s, R s (execRead s)) (s : State) : R s (execReadv s) :=
  execRwvCommon_preserves hR execRead hstep true s

/-- `execWritev` preserves any `RwvFrame` relation that `execWrite` preserves. -/
theorem execWritev_preserves {R : State → State → Prop} (hR : RwvFrame R)
    (hstep : ∀ s, R s (execWrite s)) (s : State) : R s (execWritev s) :=
  execRwvCommon_preserves hR execWrite hstep false s

end ProofLib
