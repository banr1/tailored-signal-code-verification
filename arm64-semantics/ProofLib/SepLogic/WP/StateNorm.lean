/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import Std.Tactic.BVDecide
public import Arm64
public import ProofLib.SimpAttrs
public import ProofLib.CoreLemmas
public import ProofLib.Lemmas
public import ProofLib.SepLogic.Frame
public import ProofLib.Abi.Aapcs
public import ProofLib.SepLogic
public import ProofLib.SepLogic.Bytes
public import ProofLib.ObjectLoad
public import ProofLib.Hoare.Safety
public import ProofLib.VCGen
public import ProofLib.LitNorm
public import ProofLib.BV.WidthNorm
public import ProofLib.SepLogic.WP.Defs
public import ProofLib.SepLogic.CondClassify
public import ProofLib.BV.Arith
public import ProofLib.Invariant
public import ProofLib.Library.CallInv

/-!
# State-Spine Canonicalization and Offset Normalization

Rewrite rules and `simproc`s for canonicalizing `State` write spines, pruning shadowed register
writes, resolving `ite` conditions, and normalizing memory and bitvector offsets during weakest-
precondition evaluation.
-/

namespace ProofLib

open Arm64

@[expose] public section

theorem State.advancePC_eq_setPC (s : State) :
    s.advancePC = s.setPC (s.pc + 4#64) := by
  cases s; simp [State.advancePC, State.setPC]

theorem State.advancePC_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).advancePC = s.setPC (pc + 4#64) := by
  cases s; simp [State.advancePC, State.setPC]

theorem State.setPC_setPC (s : State) (pc1 pc2 : BitVec 64) :
    (s.setPC pc1).setPC pc2 = s.setPC pc2 := by
  cases s; simp [State.setPC]

theorem State.writeReg64_setPC (s : State) (pc : BitVec 64) (r : Reg) (v : BitVec 64) :
    (s.setPC pc).writeReg64 r v = (s.writeReg64 r v).setPC pc := by
  cases s; cases r <;> simp [State.writeReg64, State.setPC]

theorem State.setPState_setPC (s : State) (pc : BitVec 64) (ps : PState) :
    (s.setPC pc).setPState ps = (s.setPState ps).setPC pc := by
  cases s; simp [State.setPState, State.setPC]

theorem State.setPState_setPState (s : State) (ps1 ps2 : PState) :
    (s.setPState ps1).setPState ps2 = s.setPState ps2 := by
  cases s; simp [State.setPState]

@[simp, arm64_norm]
theorem State.writeReg64_setPState (s : State) (ps : PState) (r : Reg) (v : BitVec 64) :
    (s.setPState ps).writeReg64 r v = (s.writeReg64 r v).setPState ps := by
  cases s; cases r <;> simp [State.writeReg64, State.setPState]

theorem State.writeReg64_setMem (s : State) (m : Memory) (r : Reg) (v : BitVec 64) :
    (s.setMem m).writeReg64 r v = (s.writeReg64 r v).setMem m := by
  cases s; cases r <;> simp [State.writeReg64, State.setMem]

theorem State.setPState_setMem (s : State) (m : Memory) (ps : PState) :
    (s.setMem m).setPState ps = (s.setPState ps).setMem m := by
  cases s; simp [State.setPState, State.setMem]

theorem State.writeVReg128_setPC (s : State) (pc : BitVec 64) (idx : BitVec 5) (v : BitVec 128) :
    (s.setPC pc).writeVReg128 idx v = (s.writeVReg128 idx v).setPC pc := by
  cases s; simp [State.writeVReg128, State.setPC]

@[simp, arm64_norm]
theorem State.writeVReg128_setPState (s : State) (ps : PState) (idx : BitVec 5) (v : BitVec 128) :
    (s.setPState ps).writeVReg128 idx v = (s.writeVReg128 idx v).setPState ps := by
  cases s; simp [State.writeVReg128, State.setPState]

theorem State.writeVReg128_setMem (s : State) (m : Memory) (idx : BitVec 5) (v : BitVec 128) :
    (s.setMem m).writeVReg128 idx v = (s.writeVReg128 idx v).setMem m := by
  cases s; simp [State.writeVReg128, State.setMem]

@[simp, arm64_norm]
theorem State.writeReg64_orFpsr (s : State) (f : BitVec 32) (r : Reg) (v : BitVec 64) :
    (s.orFpsr f).writeReg64 r v = (s.writeReg64 r v).orFpsr f := by
  cases s; cases r <;> simp [State.writeReg64, State.orFpsr]

@[simp, arm64_norm]
theorem State.writeReg64_setFpsr (s : State) (f : BitVec 32) (r : Reg) (v : BitVec 64) :
    (s.setFpsr f).writeReg64 r v = (s.writeReg64 r v).setFpsr f := by
  cases s; cases r <;> simp [State.writeReg64, State.setFpsr]

@[simp, arm64_norm]
theorem State.writeVReg128_orFpsr (s : State) (f : BitVec 32) (idx : BitVec 5) (v : BitVec 128) :
    (s.orFpsr f).writeVReg128 idx v = (s.writeVReg128 idx v).orFpsr f := by
  cases s; simp [State.writeVReg128, State.orFpsr]

@[simp, arm64_norm]
theorem State.writeVReg128_setFpsr (s : State) (f : BitVec 32) (idx : BitVec 5) (v : BitVec 128) :
    (s.setFpsr f).writeVReg128 idx v = (s.writeVReg128 idx v).setFpsr f := by
  cases s; simp [State.writeVReg128, State.setFpsr]

theorem State.orFpsr_setPC (s : State) (pc : BitVec 64) (f : BitVec 32) :
    (s.setPC pc).orFpsr f = (s.orFpsr f).setPC pc := by
  cases s; simp [State.orFpsr, State.setPC]

theorem State.orFpsr_setMem (s : State) (m : Memory) (f : BitVec 32) :
    (s.setMem m).orFpsr f = (s.orFpsr f).setMem m := by
  cases s; simp [State.orFpsr, State.setMem]

@[simp, arm64_norm]
theorem State.orFpsr_setPState (s : State) (ps : PState) (f : BitVec 32) :
    (s.setPState ps).orFpsr f = (s.orFpsr f).setPState ps := by
  cases s; simp [State.orFpsr, State.setPState]

theorem State.setFpsr_setPC (s : State) (pc : BitVec 64) (f : BitVec 32) :
    (s.setPC pc).setFpsr f = (s.setFpsr f).setPC pc := by
  cases s; simp [State.setFpsr, State.setPC]

theorem State.setFpsr_setMem (s : State) (m : Memory) (f : BitVec 32) :
    (s.setMem m).setFpsr f = (s.setFpsr f).setMem m := by
  cases s; simp [State.setFpsr, State.setMem]

@[simp, arm64_norm]
theorem State.setFpsr_setPState (s : State) (ps : PState) (f : BitVec 32) :
    (s.setPState ps).setFpsr f = (s.setFpsr f).setPState ps := by
  cases s; simp [State.setFpsr, State.setPState]

@[simp, arm64_norm]
theorem State.stepExclOracle_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).stepExclOracle = s.stepExclOracle.setPC pc := by cases s; rfl
@[simp, arm64_norm]
theorem State.stepExclOracle_setMem (s : State) (m : Memory) :
    (s.setMem m).stepExclOracle = s.stepExclOracle.setMem m := by cases s; rfl
@[simp, arm64_norm]
theorem State.stepExclOracle_setPState (s : State) (ps : PState) :
    (s.setPState ps).stepExclOracle = s.stepExclOracle.setPState ps := by cases s; rfl
@[simp, arm64_norm]
theorem State.stepExclOracle_orFpsr (s : State) (f : BitVec 32) :
    (s.orFpsr f).stepExclOracle = s.stepExclOracle.orFpsr f := by cases s; rfl
@[simp, arm64_norm]
theorem State.stepExclOracle_setFpsr (s : State) (f : BitVec 32) :
    (s.setFpsr f).stepExclOracle = s.stepExclOracle.setFpsr f := by cases s; rfl
@[simp, arm64_norm]
theorem State.stepExclOracle_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).stepExclOracle = s.stepExclOracle.writeReg64 r v := by cases s; cases r <;> rfl
@[simp, arm64_norm]
theorem State.stepExclOracle_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).stepExclOracle = s.stepExclOracle.writeVReg128 idx v := by cases s; rfl

@[simp, arm64_norm]
theorem State.stepExclLoop_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).stepExclLoop = s.stepExclLoop.setPC pc := by cases s; rfl
@[simp, arm64_norm]
theorem State.stepExclLoop_setMem (s : State) (m : Memory) :
    (s.setMem m).stepExclLoop = s.stepExclLoop.setMem m := by cases s; rfl
@[simp, arm64_norm]
theorem State.stepExclLoop_setPState (s : State) (ps : PState) :
    (s.setPState ps).stepExclLoop = s.stepExclLoop.setPState ps := by cases s; rfl
@[simp, arm64_norm]
theorem State.stepExclLoop_orFpsr (s : State) (f : BitVec 32) :
    (s.orFpsr f).stepExclLoop = s.stepExclLoop.orFpsr f := by cases s; rfl
@[simp, arm64_norm]
theorem State.stepExclLoop_setFpsr (s : State) (f : BitVec 32) :
    (s.setFpsr f).stepExclLoop = s.stepExclLoop.setFpsr f := by cases s; rfl
@[simp, arm64_norm]
theorem State.stepExclLoop_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).stepExclLoop = s.stepExclLoop.writeReg64 r v := by cases s; cases r <;> rfl
@[simp, arm64_norm]
theorem State.stepExclLoop_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).stepExclLoop = s.stepExclLoop.writeVReg128 idx v := by cases s; rfl

@[simp, arm64_norm]
theorem State.writeReg64_writeReg64_same (s : State) (r : Reg) (v1 v2 : BitVec 64) :
    (s.writeReg64 r v1).writeReg64 r v2 = s.writeReg64 r v2 := by
  cases s
  cases r with
  | gpr idx =>
    dsimp [State.writeReg64]
    by_cases h31 : idx == 31#5
    · simp [h31]
    · simp [h31, RegFile.write]
      funext i
      by_cases hi : i = idx <;> simp [hi]
  | sp => rfl
  | xzr => rfl

theorem State.writeReg64_comm_or_same (s : State) (r1 r2 : Reg) (v1 v2 : BitVec 64) :
    (s.writeReg64 r1 v1).writeReg64 r2 v2 =
      if r1 = r2 then s.writeReg64 r2 v2
      else (s.writeReg64 r2 v2).writeReg64 r1 v1 := by
  cases s
  cases r1 with
  | xzr =>
    cases r2 <;> simp [State.writeReg64]
  | sp =>
    cases r2 with
    | xzr => simp [State.writeReg64]
    | sp => simp [State.writeReg64]
    | gpr idx2 =>
      by_cases h2 : idx2 == 31#5 <;> simp [State.writeReg64, h2]
  | gpr idx1 =>
    by_cases h1 : idx1 == 31#5
    · cases r2 with
      | xzr => simp [State.writeReg64, h1]
      | sp => simp [State.writeReg64, h1]
      | gpr idx2 =>
        by_cases heq : idx1 = idx2
        · subst heq; simp [State.writeReg64, h1]
        · simp [State.writeReg64, h1, heq]
    · cases r2 with
      | xzr => simp [State.writeReg64, h1]
      | sp => simp [State.writeReg64, h1]
      | gpr idx2 =>
        by_cases h2 : idx2 == 31#5
        · have heq : idx1 ≠ idx2 := by intro h; subst h; exact h1 h2
          simp [State.writeReg64, h1, h2, heq]
        · by_cases heq : idx1 = idx2
          · subst heq
            simp [State.writeReg64, h1, RegFile.write]
            funext i
            by_cases hi : i = idx1 <;> simp [hi]
          · simp [State.writeReg64, h1, h2, heq, RegFile.write]
            funext i
            by_cases hi2 : i = idx2
            · subst hi2
              have hi1 : i ≠ idx1 := Ne.symm heq
              simp [hi1]
            · by_cases hi1 : i = idx1
              · subst hi1; simp [hi2]
              · simp [hi2, hi1]

theorem State.writeReg64_prune_step {s s' : State} {r1 r2 : Reg} {v1 v2 : BitVec 64}
    (h : s.writeReg64 r2 v2 = s'.writeReg64 r2 v2) :
    (s.writeReg64 r1 v1).writeReg64 r2 v2 = (s'.writeReg64 r1 v1).writeReg64 r2 v2 := by
  rw [State.writeReg64_comm_or_same s r1 r2, State.writeReg64_comm_or_same s' r1 r2]
  split
  · exact h
  · rw [h]

theorem State.writeReg64_prune_vreg128_step {s s' : State} {idx : BitVec 5} {vv : BitVec 128}
    {r2 : Reg} {v2 : BitVec 64}
    (h : s.writeReg64 r2 v2 = s'.writeReg64 r2 v2) :
    (s.writeVReg128 idx vv).writeReg64 r2 v2 = (s'.writeVReg128 idx vv).writeReg64 r2 v2 := by
  have comm : ∀ t : State, (t.writeVReg128 idx vv).writeReg64 r2 v2 = (t.writeReg64 r2 v2).writeVReg128 idx vv := by
    intro t; cases t; cases r2 <;> rfl
  rw [comm s, comm s', h]

end

public meta section WriteReg64PruneSimproc
open Lean Meta

/-- Pure check whether two `Reg` expressions denote the same architectural register,
    either by syntactic equality or via `evalRegKindPure?`. -/
def sameRegExpr (r1 r2 : Expr) : Bool :=
  r1 == r2 ||
    match evalRegKindPure? r1, evalRegKindPure? r2 with
    | some k1, some k2 => k1 == k2
    | _, _ => false

/-- Pure check whether `s` contains an earlier `State.writeReg64 _ r _` along its write spine. -/
partial def spineHasRegWrite (s r : Expr) : Bool :=
  if s.isAppOfArity ``State.writeReg64 3 then
    if sameRegExpr (s.getArg! 1) r then true
    else spineHasRegWrite (s.getArg! 0) r
  else if s.isAppOfArity ``State.writeVReg128 3 then
    spineHasRegWrite (s.getArg! 0) r
  else
    false

/-- Given `s` that contains an earlier write to `r`, construct `(s', prf)` where
    `prf : s.writeReg64 r v = s'.writeReg64 r v` and the shadowed write to `r` is pruned in `s'`. -/
partial def pruneShadowedRegWrite (s r v : Expr) : MetaM (Option (Expr × Expr)) := do
  if s.isAppOfArity ``State.writeReg64 3 then
    let s0 := s.getArg! 0
    let r1 := s.getArg! 1
    let v1 := s.getArg! 2
    if r1 == r then
      let prf := mkApp4 (mkConst ``State.writeReg64_writeReg64_same) s0 r v1 v
      return some (s0, prf)
    else if sameRegExpr r1 r && (← isDefEq r1 r) then
      let rawPrf := mkApp4 (mkConst ``State.writeReg64_writeReg64_same) s0 r v1 v
      let eqTy ← mkEq (mkApp3 (mkConst ``State.writeReg64) s r v)
                      (mkApp3 (mkConst ``State.writeReg64) s0 r v)
      let prf := mkApp2 (mkConst ``id [Level.zero]) eqTy rawPrf
      return some (s0, prf)
    else
      let some (s0', subPrf) ← pruneShadowedRegWrite s0 r v | return none
      let s' := mkApp3 (mkConst ``State.writeReg64) s0' r1 v1
      let prf := mkAppN (mkConst ``State.writeReg64_prune_step) #[s0, s0', r1, r, v1, v, subPrf]
      return some (s', prf)
  else if s.isAppOfArity ``State.writeVReg128 3 then
    let s0 := s.getArg! 0
    let idx := s.getArg! 1
    let vv := s.getArg! 2
    let some (s0', subPrf) ← pruneShadowedRegWrite s0 r v | return none
    let s' := mkApp3 (mkConst ``State.writeVReg128) s0' idx vv
    let prf := mkAppN (mkConst ``State.writeReg64_prune_vreg128_step) #[s0, s0', idx, vv, r, v, subPrf]
    return some (s', prf)
  else
    return none

/-- Post-`simproc` that prunes all shadowed `State.writeReg64` nodes at arbitrary spine depth,
    replacing fixed-depth nonlinear `State.writeReg64_*_same` rules. -/
simproc [simp, arm64_norm, wp_norm] reduceWriteReg64Prune (State.writeReg64 _ _ _) := fun e => do
  if !e.isAppOfArity ``State.writeReg64 3 then return .continue
  let s := e.getArg! 0
  let r := e.getArg! 1
  let v := e.getArg! 2
  if !spineHasRegWrite s r then return .continue
  let some (s0', prf0) ← pruneShadowedRegWrite s r v | return .continue
  let mut sCurr := s0'
  let mut prfCurr := prf0
  while spineHasRegWrite sCurr r do
    let some (sNext, prfNext) ← pruneShadowedRegWrite sCurr r v | break
    prfCurr ← mkEqTrans prfCurr prfNext
    sCurr := sNext
  return .done { expr := mkApp3 (mkConst ``State.writeReg64) sCurr r v, proof? := some prfCurr }

/-- Pre-`simproc` that commutes `State.writeReg64` past `State.setPC`, `State.setMem`, and
    `State.setPState` top-down before `simp` simplifies the value argument `v`, avoiding
    repeated re-traversals of `v` on post-rewrite `.visit` steps. -/
simproc ↓ [wp_norm] reduceWriteReg64PreComm (State.writeReg64 _ _ _) := fun e => do
  if !e.isAppOfArity ``State.writeReg64 3 then return .continue
  let s := e.getArg! 0
  let r := e.getArg! 1
  if evalRegKindPure? r == some .xzr then return .continue
  let v := e.getArg! 2
  if s.isAppOfArity ``State.setPC 2 then
    let s0 := s.getArg! 0
    let pc := s.getArg! 1
    let e' := mkApp2 (mkConst ``State.setPC) (mkApp3 (mkConst ``State.writeReg64) s0 r v) pc
    let prf := mkApp4 (mkConst ``State.writeReg64_setPC) s0 pc r v
    return .visit { expr := e', proof? := some prf }
  if s.isAppOfArity ``State.setMem 2 then
    let s0 := s.getArg! 0
    let m := s.getArg! 1
    let e' := mkApp2 (mkConst ``State.setMem) (mkApp3 (mkConst ``State.writeReg64) s0 r v) m
    let prf := mkApp4 (mkConst ``State.writeReg64_setMem) s0 m r v
    return .visit { expr := e', proof? := some prf }
  if s.isAppOfArity ``State.setPState 2 then
    let s0 := s.getArg! 0
    let ps := s.getArg! 1
    let e' := mkApp2 (mkConst ``State.setPState) (mkApp3 (mkConst ``State.writeReg64) s0 r v) ps
    let prf := mkApp4 (mkConst ``State.writeReg64_setPState) s0 ps r v
    return .visit { expr := e', proof? := some prf }
  if s.isAppOfArity ``State.orFpsr 2 then
    let s0 := s.getArg! 0
    let f := s.getArg! 1
    let e' := mkApp2 (mkConst ``State.orFpsr) (mkApp3 (mkConst ``State.writeReg64) s0 r v) f
    let prf := mkApp4 (mkConst ``State.writeReg64_orFpsr) s0 f r v
    return .visit { expr := e', proof? := some prf }
  if s.isAppOfArity ``State.setFpsr 2 then
    let s0 := s.getArg! 0
    let f := s.getArg! 1
    let e' := mkApp2 (mkConst ``State.setFpsr) (mkApp3 (mkConst ``State.writeReg64) s0 r v) f
    let prf := mkApp4 (mkConst ``State.writeReg64_setFpsr) s0 f r v
    return .visit { expr := e', proof? := some prf }
  return .continue

/-- Pre-`simproc` that commutes `State.orFpsr` past `State.setPC`, `State.setMem`, and
    `State.setPState` top-down before `simp` simplifies the flags argument `f`. -/
simproc ↓ [wp_norm] reduceOrFpsrPreComm (State.orFpsr _ _) := fun e => do
  if !e.isAppOfArity ``State.orFpsr 2 then return .continue
  let s := e.getArg! 0
  let f := e.getArg! 1
  if s.isAppOfArity ``State.setPC 2 then
    let s0 := s.getArg! 0
    let pc := s.getArg! 1
    let e' := mkApp2 (mkConst ``State.setPC) (mkApp2 (mkConst ``State.orFpsr) s0 f) pc
    let prf := mkApp3 (mkConst ``State.orFpsr_setPC) s0 pc f
    return .visit { expr := e', proof? := some prf }
  if s.isAppOfArity ``State.setMem 2 then
    let s0 := s.getArg! 0
    let m := s.getArg! 1
    let e' := mkApp2 (mkConst ``State.setMem) (mkApp2 (mkConst ``State.orFpsr) s0 f) m
    let prf := mkApp3 (mkConst ``State.orFpsr_setMem) s0 m f
    return .visit { expr := e', proof? := some prf }
  if s.isAppOfArity ``State.setPState 2 then
    let s0 := s.getArg! 0
    let ps := s.getArg! 1
    let e' := mkApp2 (mkConst ``State.setPState) (mkApp2 (mkConst ``State.orFpsr) s0 f) ps
    let prf := mkApp3 (mkConst ``State.orFpsr_setPState) s0 ps f
    return .visit { expr := e', proof? := some prf }
  return .continue

/-- Pre-`simproc` that commutes `State.setPState` past `State.setPC` and `State.setMem` (and absorbs
    shadowed `State.setPState`) top-down before `simp` simplifies the `PState` argument `ps`. -/
simproc ↓ [wp_norm] reduceSetPStatePreComm (State.setPState _ _) := fun e => do
  if !e.isAppOfArity ``State.setPState 2 then return .continue
  let s := e.getArg! 0
  let ps := e.getArg! 1
  if s.isAppOfArity ``State.setPC 2 then
    let s0 := s.getArg! 0
    let pc := s.getArg! 1
    let e' := mkApp2 (mkConst ``State.setPC) (mkApp2 (mkConst ``State.setPState) s0 ps) pc
    let prf := mkApp3 (mkConst ``State.setPState_setPC) s0 pc ps
    return .visit { expr := e', proof? := some prf }
  if s.isAppOfArity ``State.setMem 2 then
    let s0 := s.getArg! 0
    let m := s.getArg! 1
    let e' := mkApp2 (mkConst ``State.setMem) (mkApp2 (mkConst ``State.setPState) s0 ps) m
    let prf := mkApp3 (mkConst ``State.setPState_setMem) s0 m ps
    return .visit { expr := e', proof? := some prf }
  if s.isAppOfArity ``State.setPState 2 then
    let s0 := s.getArg! 0
    let ps1 := s.getArg! 1
    let e' := mkApp2 (mkConst ``State.setPState) s0 ps
    let prf := mkApp3 (mkConst ``State.setPState_setPState) s0 ps1 ps
    return .visit { expr := e', proof? := some prf }
  return .continue

end WriteReg64PruneSimproc

@[expose] public section

theorem State.setPC_setMem_setPC (s : State) (pc1 pc2 : BitVec 64) (m : Memory) :
    ((s.setPC pc1).setMem m).setPC pc2 = (s.setPC pc2).setMem m := by
  cases s; simp [State.setPC, State.setMem]

theorem State.applyWriteback_none_setPC (s : State) (pc pc1 pc2 : BitVec 64)
    (hpc : pc1 + 4#64 = pc2) :
    (applyWriteback (s.setPC pc) none).setPC (pc1 + 4#64) = s.setPC pc2 := by
  cases s; subst hpc; rfl

theorem State.applyWriteback_none_setMem_setPC (s : State) (pc pc1 pc2 : BitVec 64) (m : Memory)
    (hpc : pc1 + 4#64 = pc2) :
    (applyWriteback ((s.setPC pc).setMem m) none).setPC (pc1 + 4#64) = (s.setPC pc2).setMem m := by
  cases s; subst hpc; rfl


theorem State.ite_setPC (c : Prop) {inst : Decidable c} (s : State) (pc1 pc2 : BitVec 64) :
    @_root_.ite State c inst (s.setPC pc1) (s.setPC pc2) =
      s.setPC (@_root_.ite (BitVec 64) c inst pc1 pc2) := by
  letI := inst
  by_cases hc : c <;> simp [hc]

theorem State.ite_setMem (c : Prop) {inst : Decidable c} (s1 s2 : State) (m : Memory) :
    @_root_.ite State c inst (s1.setMem m) (s2.setMem m) =
      (@_root_.ite State c inst s1 s2).setMem m := by
  letI := inst
  by_cases hc : c <;> simp [hc]

@[simp, arm64_norm]
theorem bitvec_add8_add8 (x : BitVec 64) : (x + 8#64) + 8#64 = x + 16#64 := by
  bv_omega

@[simp, arm64_norm]
theorem bitvec_add8_add16 (x : BitVec 64) : (x + 8#64) + 16#64 = x + 24#64 := by
  bv_omega

@[simp, arm64_norm]
theorem bitvec_add16_add8 (x : BitVec 64) : (x + 16#64) + 8#64 = x + 24#64 := by
  bv_omega

theorem bitvec_add1_add_sub1 (x y : BitVec 64) :
    (x + 1#64) + (y - 1#64) = x + y := by
  bv_omega

theorem bitvec_toNat_eq_zero_iff (x : BitVec 64) :
    (x.toNat = 0) ↔ (x = 0#64) := by
  constructor <;> intro h <;> bv_omega

theorem bool_not_eq_true_iff (b : Bool) : ((!b) = true) ↔ ¬(b = true) := by
  cases b <;> simp

theorem bitvec_add_sub_self_left (a b : BitVec 64) : (a + b) - a = b := by bv_omega


@[simp, arm64_norm, wp_norm]
theorem RegWidth.ofBool_false : RegWidth.ofBool false = .W32 := rfl

@[simp, arm64_norm, wp_norm]
theorem RegWidth.ofBool_true : RegWidth.ofBool true = .W64 := rfl

attribute [wp_norm ↓]
  Program.evalInst execInst execInstWithSvc applyWriteback applySimdSatResult evalAddrMode
  State.writeReg32.eq_1
  execAddSubImm execAddSubExt execAddSubShift execAddSubCarry
  execLogicalImm execLogicalShift execMoveWide execBitfield
  execCondSelect execCondCompare
  execDataProc1 execDataProc2 execDataProc3

attribute [wp_norm]
  State.writeReg_w32 State.writeReg_w64 State.writeReg32.eq_1
  State.writeReg64_xzr
  State.writeVReg64.eq_1 State.writeVReg32.eq_1 State.readVReg64.eq_1 State.readVReg32.eq_1
  State.advancePC_eq_setPC State.advancePC_setPC State.setPC_setPC
  State.writeReg64_setPC State.writeVReg128_setPC State.setPState_setPC
  State.setPState_setPState State.writeReg64_setPState State.writeVReg128_setPState
  State.writeReg64_orFpsr State.writeReg64_setFpsr
  State.writeVReg128_orFpsr State.writeVReg128_setFpsr
  State.orFpsr_setPC State.orFpsr_setMem State.orFpsr_setPState
  State.setFpsr_setPC State.setFpsr_setMem State.setFpsr_setPState
  State.stepExclOracle_setPC State.stepExclOracle_setMem State.stepExclOracle_setPState
  State.stepExclOracle_orFpsr State.stepExclOracle_setFpsr
  State.stepExclOracle_writeReg64 State.stepExclOracle_writeVReg128
  State.stepExclLoop_setPC State.stepExclLoop_setMem State.stepExclLoop_setPState
  State.stepExclLoop_orFpsr State.stepExclLoop_setFpsr
  State.stepExclLoop_writeReg64 State.stepExclLoop_writeVReg128
  State.setMem_setPC State.setMem_setMem
  State.writeReg64_setMem State.writeVReg128_setMem State.setPState_setMem
  State.writeReg64_writeReg64_same State.writeVReg128_writeVReg128_same
  State.ite_setPC State.ite_setMem
  bitvec_add1_add_sub1 bitvec_toNat_eq_zero_iff bool_not_eq_true_iff

attribute [simp, arm64_norm] adrp_page_of_aligned

@[simp, arm64_norm]
theorem w32_aligned_of_page_aligned {b off : BitVec 64} (hb : b &&& 0xfff#64 = 0#64) :
    ((b + off) &&& 0b11#64) = (off &&& 0b11#64) := by
  revert hb; bv_bits

@[simp, arm64_norm]
theorem bitvec_truncate8_truncate32 (x : BitVec 64) :
    (x.truncate 32).truncate 8 = x.truncate 8 := by
  bv_bits

@[simp, arm64_norm]
theorem bitvec_truncate8_zeroExtend32 (b : BitVec 8) :
    (b.zeroExtend 32).truncate 8 = b := by
  bv_bits

@[simp, arm64_norm, wp_branch]
theorem bv8_zext32_and_sub_eq_zero_iff (b : BitVec 8) (m c : BitVec 32) :
    ((b.zeroExtend 32 &&& m) - c = 0#32) ↔ (b.zeroExtend 64 &&& m.zeroExtend 64 = c.zeroExtend 64) := by
  have hd : b.zeroExtend 64 &&& m.zeroExtend 64 = (b.zeroExtend 32 &&& m).zeroExtend 64 := by
    ext i hi; simp
  rw [hd]
  generalize b.zeroExtend 32 &&& m = x
  bv_bits

@[simp, arm64_norm]
theorem sext_trunc_zext_and_byte_mask (b : BitVec 8) (m : BitVec 64)
    (hm : decide (m ≤ 255#64) = true) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 b)) &&& m =
      BitVec.zeroExtend 64 b &&& m := by
  have hm' := of_decide_eq_true hm
  have hmm : m &&& 255#64 = m := by revert hm'; bv_bits
  have h1 : BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 b)) &&& 255#64 =
      BitVec.zeroExtend 64 b := by bv_bits
  rw [← hmm, BitVec.and_comm m, ← BitVec.and_assoc, h1, BitVec.and_comm 255#64 m, hmm]

@[simp, arm64_norm]
theorem zext64_and_255 (b : BitVec 8) :
    BitVec.zeroExtend 64 b &&& 255#64 = BitVec.zeroExtend 64 b := by
  bv_bits

@[simp, arm64_norm]
theorem zext64_32_and_trunc32_zext64 (x : BitVec 32) (m : BitVec 64) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 x &&& m)) =
      BitVec.zeroExtend 64 x &&& BitVec.zeroExtend 64 (BitVec.truncate 32 m) := by
  simp

@[simp, arm64_norm]
theorem zext64_and_trunc32_zext64 (b : BitVec 8) (m : BitVec 64) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 b &&& m)) =
      BitVec.zeroExtend 64 b &&& m := by
  bv_bits

@[simp, arm64_norm, wp_branch]
theorem zext64_and_trunc32_eq (b : BitVec 8) (m : BitVec 64) (c : BitVec 32) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 b &&& m) = c) ↔
      (BitVec.zeroExtend 64 b &&& m = BitVec.zeroExtend 64 c) := by
  bv_bits

@[simp, arm64_norm, wp_branch]
theorem zext64_and_trunc32_ult (b : BitVec 8) (m : BitVec 64) (c : BitVec 32) :
    BitVec.ult (BitVec.truncate 32 (BitVec.zeroExtend 64 b &&& m)) c =
      BitVec.ult (BitVec.zeroExtend 64 b &&& m) (BitVec.zeroExtend 64 c) := by
  bv_bits

@[simp, arm64_norm, wp_branch]
theorem zext64_and_trunc32_ule (b : BitVec 8) (m : BitVec 64) (c : BitVec 32) :
    BitVec.ule (BitVec.truncate 32 (BitVec.zeroExtend 64 b &&& m)) c =
      BitVec.ule (BitVec.zeroExtend 64 b &&& m) (BitVec.zeroExtend 64 c) := by
  bv_bits

@[simp, arm64_norm, wp_branch]
theorem zext64_and_trunc32_ult_right (c : BitVec 32) (b : BitVec 8) (m : BitVec 64) :
    BitVec.ult c (BitVec.truncate 32 (BitVec.zeroExtend 64 b &&& m)) =
      BitVec.ult (BitVec.zeroExtend 64 c) (BitVec.zeroExtend 64 b &&& m) := by
  bv_bits

@[simp, arm64_norm, wp_branch]
theorem zext64_and_trunc32_ule_right (c : BitVec 32) (b : BitVec 8) (m : BitVec 64) :
    BitVec.ule c (BitVec.truncate 32 (BitVec.zeroExtend 64 b &&& m)) =
      BitVec.ule (BitVec.zeroExtend 64 c) (BitVec.zeroExtend 64 b &&& m) := by
  bv_bits

@[simp, arm64_norm, wp_branch]
theorem zext64_and_trunc32_slt (b : BitVec 8) (m : BitVec 64) (c : BitVec 32)
    (hc : decide (BitVec.slt c 0#32 = false) = true) :
    BitVec.slt (BitVec.truncate 32 (BitVec.zeroExtend 64 b &&& m)) c =
      BitVec.ult (BitVec.zeroExtend 64 b &&& m) (BitVec.zeroExtend 64 c) := by
  have hc' := of_decide_eq_true hc
  revert hc'
  bv_bits

@[simp, arm64_norm, wp_branch]
theorem zext64_and_trunc32_sle (b : BitVec 8) (m : BitVec 64) (c : BitVec 32)
    (hc : decide (BitVec.slt c 0#32 = false) = true) :
    BitVec.sle (BitVec.truncate 32 (BitVec.zeroExtend 64 b &&& m)) c =
      BitVec.ule (BitVec.zeroExtend 64 b &&& m) (BitVec.zeroExtend 64 c) := by
  have hc' := of_decide_eq_true hc
  revert hc'
  bv_bits

@[simp, arm64_norm, wp_branch]
theorem zext64_and_trunc32_slt_right (c : BitVec 32) (b : BitVec 8) (m : BitVec 64)
    (hc : decide (BitVec.slt c 0#32 = false) = true) :
    BitVec.slt c (BitVec.truncate 32 (BitVec.zeroExtend 64 b &&& m)) =
      BitVec.ult (BitVec.zeroExtend 64 c) (BitVec.zeroExtend 64 b &&& m) := by
  have hc' := of_decide_eq_true hc
  revert hc'
  bv_bits

@[simp, arm64_norm, wp_branch]
theorem zext64_and_trunc32_sle_right (c : BitVec 32) (b : BitVec 8) (m : BitVec 64)
    (hc : decide (BitVec.slt c 0#32 = false) = true) :
    BitVec.sle c (BitVec.truncate 32 (BitVec.zeroExtend 64 b &&& m)) =
      BitVec.ule (BitVec.zeroExtend 64 c) (BitVec.zeroExtend 64 b &&& m) := by
  have hc' := of_decide_eq_true hc
  revert hc'
  bv_bits

@[simp, arm64_norm]
theorem sext64_trunc32_zext64_getLsbD_31 (b : BitVec 8) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 b))).getLsbD 31 =
      b.getLsbD 7 := by
  bv_bits

@[simp, arm64_norm]
theorem zext64_getLsbD_7 (b : BitVec 8) :
    (BitVec.zeroExtend 64 b).getLsbD 7 = b.getLsbD 7 := by
  bv_bits

@[simp, arm64_norm, wp_branch]
theorem zext64_and_trunc32_eq_right (c : BitVec 32) (b : BitVec 8) (m : BitVec 64) :
    (c = BitVec.truncate 32 (BitVec.zeroExtend 64 b &&& m)) ↔
      (BitVec.zeroExtend 64 c = BitVec.zeroExtend 64 b &&& m) := by
  bv_bits

@[simp, arm64_norm]
theorem bitvec_zero_or_32 (x : BitVec 32) :
    0#32 ||| x = x := by
  simp

@[simp, arm64_norm]
theorem zext64_ushiftRight_trunc32 (b : BitVec 8) (k : Nat) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 b >>> k) = BitVec.zeroExtend 32 (b >>> k) := by
  ext i hi
  by_cases hk : k + i < 8
  · simp [show k + i < 64 by omega, show k + i < 32 by omega]
  · simp [BitVec.getLsbD_of_ge b (k + i) (by omega)]

@[simp, arm64_norm]
theorem bv8_ushiftRight4_and1_of_not_ule32 (b : BitVec 8)
    (h : ¬(BitVec.ule 32#64 (BitVec.zeroExtend 64 b) = true)) :
    b >>> 4 &&& 1#8 = b >>> 4 := by
  revert h; bv_bits

@[simp, arm64_norm]
theorem bv8_ushiftRight4_zext32_add1 (b : BitVec 8) :
    BitVec.zeroExtend 64 (BitVec.zeroExtend 32 (b >>> 4) + 1#32) =
      BitVec.zeroExtend 64 (1#8 + (b >>> 4)) := by
  bv_bits

@[wp_branch]
theorem bv64_ule_34_iff_not_ule_33 (x : BitVec 64) :
    (BitVec.ule 34#64 x = true) ↔ ¬(BitVec.ule x 33#64 = true) := by
  bv_bits

theorem bv8_and_eq_iff_zext64 (b m c : BitVec 8) :
    (b &&& m = c) ↔ (BitVec.zeroExtend 64 b &&& BitVec.zeroExtend 64 m = BitVec.zeroExtend 64 c) := by
  rw [← BitVec.setWidth_and]; bv_bits

theorem bv8_eq_iff_zext64 (b c : BitVec 8) :
    (b = c) ↔ (BitVec.zeroExtend 64 b = BitVec.zeroExtend 64 c) := by
  bv_bits

theorem bv8_lt_iff_zext64_ult (b c : BitVec 8) :
    (b < c) ↔ (BitVec.ult (BitVec.zeroExtend 64 b) (BitVec.zeroExtend 64 c) = true) := by
  bv_bits

theorem bv8_le_iff_zext64_ule (b c : BitVec 8) :
    (b ≤ c) ↔ (BitVec.ule (BitVec.zeroExtend 64 b) (BitVec.zeroExtend 64 c) = true) := by
  bv_bits

theorem bv8_and_zext64 (b m : BitVec 8) :
    BitVec.zeroExtend 64 (b &&& m) = BitVec.zeroExtend 64 b &&& BitVec.zeroExtend 64 m := by
  simp

@[simp, arm64_norm]
theorem bv8_zext32_eq_iff_zext64 (b : BitVec 8) (c : BitVec 32) :
    (BitVec.zeroExtend 32 b = c) ↔ (BitVec.zeroExtend 64 b = BitVec.zeroExtend 64 c) := by
  bv_bits

@[simp, arm64_norm]
theorem bv8_zext32_eq_right_iff_zext64 (c : BitVec 32) (b : BitVec 8) :
    (c = BitVec.zeroExtend 32 b) ↔ (BitVec.zeroExtend 64 c = BitVec.zeroExtend 64 b) := by
  bv_bits

@[simp, arm64_norm]
theorem bv8_zext32_ult_iff_zext64 (b : BitVec 8) (c : BitVec 32) :
    BitVec.ult (BitVec.zeroExtend 32 b) c = BitVec.ult (BitVec.zeroExtend 64 b) (BitVec.zeroExtend 64 c) := by
  bv_bits

@[simp, arm64_norm]
theorem bv8_zext32_ule_iff_zext64 (b : BitVec 8) (c : BitVec 32) :
    BitVec.ule (BitVec.zeroExtend 32 b) c = BitVec.ule (BitVec.zeroExtend 64 b) (BitVec.zeroExtend 64 c) := by
  bv_bits

@[simp, arm64_norm]
theorem bv8_zext32_ult_right_iff_zext64 (c : BitVec 32) (b : BitVec 8) :
    BitVec.ult c (BitVec.zeroExtend 32 b) = BitVec.ult (BitVec.zeroExtend 64 c) (BitVec.zeroExtend 64 b) := by
  bv_bits

@[simp, arm64_norm]
theorem bv8_zext32_ule_right_iff_zext64 (c : BitVec 32) (b : BitVec 8) :
    BitVec.ule c (BitVec.zeroExtend 32 b) = BitVec.ule (BitVec.zeroExtend 64 c) (BitVec.zeroExtend 64 b) := by
  bv_bits

@[wp_branch]
theorem bv8_and_128_bne_zero (b : BitVec 8) :
    (b &&& 128#8 != 0#8) = b.getLsbD 7 := by
  revert b; decide

@[wp_branch]
theorem bv8_and_128_beq_zero (b : BitVec 8) :
    (b &&& 128#8 == 0#8) = !b.getLsbD 7 := by
  revert b; decide

@[wp_branch]
theorem bv8_and_128_eq_zero_iff (b : BitVec 8) :
    (b &&& 128#8 = 0#8) ↔ ¬(b.getLsbD 7 = true) := by
  bv_bits

@[wp_branch]
theorem bv8_zext64_and_192_eq_64_iff (b : BitVec 8) :
    (BitVec.zeroExtend 64 b &&& 192#64 = 64#64) ↔
      (BitVec.ule 64#64 (BitVec.zeroExtend 64 b) = true ∧ ¬(b.getLsbD 7 = true)) := by
  bv_bits

@[wp_branch]
theorem bv8_zext64_and_224_eq_32_iff (b : BitVec 8) :
    (BitVec.zeroExtend 64 b &&& 224#64 = 32#64) ↔
      (BitVec.ule 32#64 (BitVec.zeroExtend 64 b) = true ∧
       ¬(BitVec.ule 64#64 (BitVec.zeroExtend 64 b) = true) ∧
       ¬(b.getLsbD 7 = true)) := by
  bv_bits

@[simp, arm64_norm, wp_branch]
theorem bv64_and_ult_of_gt (x m c : BitVec 64) (h : decide (m < c) = true) :
    BitVec.ult (x &&& m) c = true := by
  have h' := of_decide_eq_true h
  revert h'
  bv_bits

@[simp, arm64_norm, wp_branch]
theorem bv8_and_lt_of_gt (b m c : BitVec 8) (h : decide (m < c) = true) :
    (b &&& m) < c := by
  have h' := of_decide_eq_true h
  revert h'
  bv_bits

@[simp, arm64_norm, wp_branch]
theorem zext64_and_trunc32_sub_ule (b : BitVec 8) (m : BitVec 64) (c1 c2 : BitVec 32)
    (hc : decide (BitVec.zeroExtend 64 c1 + BitVec.zeroExtend 64 c2 < 4294967296#64) = true) :
    BitVec.ule (BitVec.truncate 32 (BitVec.zeroExtend 64 b &&& m) - c1) c2 =
      (BitVec.ule (BitVec.zeroExtend 64 c1) (BitVec.zeroExtend 64 b &&& m) &&
       BitVec.ule (BitVec.zeroExtend 64 b &&& m) (BitVec.zeroExtend 64 c1 + BitVec.zeroExtend 64 c2)) := by
  have hc' := of_decide_eq_true hc
  have hz : (BitVec.zeroExtend 64 b &&& m).toNat < 256 := by
    rw [BitVec.toNat_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_left (by have := b.isLt; simp; omega)
  generalize BitVec.zeroExtend 64 b &&& m = z at hz ⊢
  have h1 := c1.isLt; have h2 := c2.isLt
  rw [Bool.eq_iff_iff]
  simp [BitVec.ule, BitVec.lt_def, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth] at hc' ⊢
  omega

@[wp_branch]
theorem bv64_and_ult_self_iff_ne (x m : BitVec 64) :
    (BitVec.ult (x &&& m) m = true) ↔ ¬(x &&& m = m) := by
  bv_bits

/-- Helper proposition for resolving an `ite` condition `c` to either `true` (`c`) or `false` (`¬c`)
    in a single `simp` pass. Defined as a `structure` so `apply IteResolved.mk_*` unifies against
    `IteResolved c ?b` without WHNF-unfolding `IteResolved c true` to `c` or `IteResolved c false`
    to `c → False`. -/
structure IteResolved (c : Prop) (b : Bool) : Prop where
  out : match b with
    | true => c
    | false => ¬c

@[congr]
theorem IteResolved.congr_c {c c' : Prop} (b : Bool) (h : c ↔ c') :
    IteResolved c b ↔ IteResolved c' b := by
  rw [propext h]

theorem IteResolved.of_true : IteResolved True true := ⟨trivial⟩
theorem IteResolved.of_false : IteResolved False false := ⟨not_false⟩
theorem IteResolved.mk_true {c : Prop} (h : c) : IteResolved c true := ⟨h⟩
theorem IteResolved.mk_false {c : Prop} (h : ¬c) : IteResolved c false := ⟨h⟩
theorem IteResolved.mk_false_not {c : Prop} (h : c) : IteResolved (¬c) false := ⟨fun hn => hn h⟩
theorem IteResolved.mk_true_beq {α : Type _} [BEq α] [LawfulBEq α] {a b : α} (h : a = b) :
    IteResolved ((a == b) = true) true :=
  ⟨beq_iff_eq.mpr h⟩
theorem IteResolved.mk_false_beq {α : Type _} [BEq α] [LawfulBEq α] {a b : α} (h : ¬(a = b)) :
    IteResolved ((a == b) = true) false :=
  ⟨fun hb => h (beq_iff_eq.mp hb)⟩
theorem IteResolved.mk_true_bne {α : Type _} [BEq α] [LawfulBEq α] {a b : α} (h : ¬(a = b)) :
    IteResolved ((a != b) = true) true :=
  ⟨bne_iff_ne.mpr h⟩
theorem IteResolved.mk_false_bne {α : Type _} [BEq α] [LawfulBEq α] {a b : α} (h : a = b) :
    IteResolved ((a != b) = true) false :=
  ⟨fun hb => bne_iff_ne.mp hb h⟩
theorem IteResolved.mk_true_of_beq_eq_true {α : Type _} [BEq α] [LawfulBEq α] {a b : α}
    (h : (a == b) = true) : IteResolved (a = b) true :=
  ⟨beq_iff_eq.mp h⟩
theorem IteResolved.mk_false_of_beq_eq_false {α : Type _} [BEq α] [LawfulBEq α] {a b : α}
    (h : (a == b) = false) : IteResolved (a = b) false :=
  ⟨fun hab => by rw [hab, beq_self_eq_true] at h; cases h⟩
theorem IteResolved.mk_false_not_of_beq_eq_true {α : Type _} [BEq α] [LawfulBEq α] {a b : α}
    (h : (a == b) = true) : IteResolved (¬(a = b)) false :=
  ⟨fun hne => hne (beq_iff_eq.mp h)⟩
theorem IteResolved.mk_true_not_of_beq_eq_false {α : Type _} [BEq α] [LawfulBEq α] {a b : α}
    (h : (a == b) = false) : IteResolved (¬(a = b)) true :=
  ⟨fun hab => by rw [hab, beq_self_eq_true] at h; cases h⟩
theorem IteResolved.not_eq_true_of_eq_false {b : Bool} (h : b = false) : ¬(b = true) := by
  rw [h]; decide
theorem IteResolved.to_true {c : Prop} (h : IteResolved c true) : c := h.out
theorem IteResolved.to_false {c : Prop} (h : IteResolved c false) : ¬c := h.out

theorem ite_prop_eq (c : Prop) {inst : Decidable c} (P Q : Prop) :
    @_root_.ite Prop c inst P Q = ((c → P) ∧ (¬ c → Q)) := by
  letI := inst
  by_cases hc : c <;> simp [hc]

@[simp, arm64_norm]
theorem List.length_ite {α : Type _} (c : Prop) {inst : Decidable c} (t e : List α) :
    (@_root_.ite (List α) c inst t e).length = @_root_.ite Nat c inst t.length e.length := by
  letI := inst
  by_cases hc : c <;> simp [hc]

@[simp, arm64_norm]
theorem BitVec.ofNat_ite (w : Nat) (c : Prop) {inst : Decidable c} (t e : Nat) :
    BitVec.ofNat w (@_root_.ite Nat c inst t e) =
      @_root_.ite (BitVec w) c inst (BitVec.ofNat w t) (BitVec.ofNat w e) := by
  letI := inst
  by_cases hc : c <;> simp [hc]

@[simp, arm64_norm]
theorem BitVec.truncate_ite (w w' : Nat) (c : Prop) {inst : Decidable c} (t e : BitVec w) :
    BitVec.truncate w' (@_root_.ite (BitVec w) c inst t e) =
      @_root_.ite (BitVec w') c inst (BitVec.truncate w' t) (BitVec.truncate w' e) := by
  letI := inst
  by_cases hc : c <;> simp [hc]

@[simp, arm64_norm]
theorem BitVec.zeroExtend_ite (w w' : Nat) (c : Prop) {inst : Decidable c} (t e : BitVec w) :
    BitVec.zeroExtend w' (@_root_.ite (BitVec w) c inst t e) =
      @_root_.ite (BitVec w') c inst (BitVec.zeroExtend w' t) (BitVec.zeroExtend w' e) := by
  letI := inst
  by_cases hc : c <;> simp [hc]

@[simp, arm64_norm]
theorem MemMatchesBytes_ite (m : Memory) (buf : BitVec 64) (c : Prop) {inst : Decidable c}
    (t e : List (BitVec 8)) :
    MemMatchesBytes m buf (@_root_.ite (List (BitVec 8)) c inst t e) =
      @_root_.ite Prop c inst (MemMatchesBytes m buf t) (MemMatchesBytes m buf e) := by
  letI := inst
  by_cases hc : c <;> simp [hc]

@[simp, arm64_norm]
theorem bv128_truncate_append (hi lo : BitVec 64) : (hi ++ lo).truncate 64 = lo := by
  bv_bits

@[simp, arm64_norm]
theorem bv128_extractLsb'_append (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by
  bv_bits

/-! ## Image Invariant State-Spine Normalization -/

@[simp, arm64_norm, wp_norm]
theorem State.symtab_applyWriteback (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).symtab = s.symtab := by
  cases wb <;> simp [applyWriteback]

@[simp, arm64_norm, wp_norm]
theorem State.symtab_setTpidrEl0 (s : State) (v : BitVec 64) :
    (setTpidrEl0 s v).symtab = s.symtab := by
  cases s; rfl

attribute [wp_norm] mem_setTpidrEl0

@[simp, arm64_norm, wp_norm]
theorem calleeSavedVRegs_applyWriteback (s : State) (wb : Option (Reg × BitVec 64)) :
    calleeSavedVRegs (applyWriteback s wb) = calleeSavedVRegs s := by
  cases wb <;> simp [applyWriteback]

attribute [wp_norm]
  Bool.true_and Bool.false_and Bool.and_true Bool.and_false
  Bool.true_or Bool.false_or Bool.or_true Bool.or_false
  Bool.not_true Bool.not_false
  Arm64.StackPreserved.refl_iff
  Arm64.CalleeSavedPreserved.rfl
  Arm64.CallingConventionPreserved.rfl
  calleeSavedVRegs_setTpidrEl0
  State.symtab_writeReg64 State.symtab_writeReg32 State.symtab_writeReg
  State.symtab_writeVReg128 State.symtab_writeVReg64 State.symtab_writeVReg32
  State.symtab_setPC State.symtab_advancePC State.symtab_setMem
  State.symtab_setPState State.symtab_setStatus State.symtab_setFpsr State.symtab_orFpsr
  State.symtab_setPhysMemAvail State.spAligned_setPhysMemAvail checkAddrSPAligned_setPhysMemAvail
  CalleeSavedPreserved_setPhysMemAvail CalleeSavedPreserved_setPhysMemAvail_left
  CallingConventionPreserved_setPhysMemAvail CallingConventionPreserved_setPhysMemAvail_left
  Returned_setPhysMemAvail Returned_setPhysMemAvail_left
  State.calleeSavedVRegs_setPhysMemAvail State.tpidrEl0_setPhysMemAvail State.exclFails_setPhysMemAvail
  State.fs_setPhysMemAvail State.trace_setPhysMemAvail

theorem _root_.Arm64.Obj.Image.FrozenLoaded.of_mem_eq {img : Obj.Image} {s s' : State}
    (h : img.FrozenLoaded s) (hmem : s'.mem = s.mem) : img.FrozenLoaded s' :=
  h.of_keepsFrozen (hmem ▸ Memory.KeepsFrozen.refl s.mem)

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.FrozenLoaded_writeReg64 (img : Obj.Image) (s : State) (r : Reg) (v : BitVec 64) :
    img.FrozenLoaded (s.writeReg64 r v) = img.FrozenLoaded s :=
  propext ⟨fun h => h.of_mem_eq (by simp), fun h => h.of_mem_eq (by simp)⟩

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.FrozenLoaded_writeReg32 (img : Obj.Image) (s : State) (r : Reg) (v : BitVec 32) :
    img.FrozenLoaded (s.writeReg32 r v) = img.FrozenLoaded s :=
  propext ⟨fun h => h.of_mem_eq (by simp), fun h => h.of_mem_eq (by simp)⟩

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.FrozenLoaded_writeReg (img : Obj.Image) (w : RegWidth) (s : State) (r : Reg) (v : BitVec 64) :
    img.FrozenLoaded (s.writeReg w r v) = img.FrozenLoaded s :=
  propext ⟨fun h => h.of_mem_eq (by simp), fun h => h.of_mem_eq (by simp)⟩

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.FrozenLoaded_writeVReg128 (img : Obj.Image) (s : State) (idx : BitVec 5) (v : BitVec 128) :
    img.FrozenLoaded (s.writeVReg128 idx v) = img.FrozenLoaded s :=
  propext ⟨fun h => h.of_mem_eq (by simp), fun h => h.of_mem_eq (by simp)⟩

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.FrozenLoaded_writeVReg64 (img : Obj.Image) (s : State) (idx : BitVec 5) (v : BitVec 64) :
    img.FrozenLoaded (s.writeVReg64 idx v) = img.FrozenLoaded s :=
  propext ⟨fun h => h.of_mem_eq (by simp), fun h => h.of_mem_eq (by simp)⟩

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.FrozenLoaded_writeVReg32 (img : Obj.Image) (s : State) (idx : BitVec 5) (v : BitVec 32) :
    img.FrozenLoaded (s.writeVReg32 idx v) = img.FrozenLoaded s :=
  propext ⟨fun h => h.of_mem_eq (by simp), fun h => h.of_mem_eq (by simp)⟩

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.FrozenLoaded_setPC (img : Obj.Image) (s : State) (pc : BitVec 64) :
    img.FrozenLoaded (s.setPC pc) = img.FrozenLoaded s :=
  propext ⟨fun h => h.of_mem_eq (by simp), fun h => h.of_mem_eq (by simp)⟩

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.FrozenLoaded_advancePC (img : Obj.Image) (s : State) :
    img.FrozenLoaded s.advancePC = img.FrozenLoaded s :=
  propext ⟨fun h => h.of_mem_eq (by simp), fun h => h.of_mem_eq (by simp)⟩

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.FrozenLoaded_setPState (img : Obj.Image) (s : State) (ps : PState) :
    img.FrozenLoaded (s.setPState ps) = img.FrozenLoaded s :=
  propext ⟨fun h => h.of_mem_eq (by simp), fun h => h.of_mem_eq (by simp)⟩

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.FrozenLoaded_setStatus (img : Obj.Image) (s : State) (st : ExecStatus) :
    img.FrozenLoaded (s.setStatus st) = img.FrozenLoaded s :=
  propext ⟨fun h => h.of_mem_eq (by simp), fun h => h.of_mem_eq (by simp)⟩

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.FrozenLoaded_applyWriteback (img : Obj.Image) (s : State) (wb : Option (Reg × BitVec 64)) :
    img.FrozenLoaded (applyWriteback s wb) = img.FrozenLoaded s := by
  cases wb <;> simp [applyWriteback]

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.FrozenLoaded_setTpidrEl0 (img : Obj.Image) (s : State) (v : BitVec 64) :
    img.FrozenLoaded (setTpidrEl0 s v) = img.FrozenLoaded s :=
  propext ⟨fun h => h.of_mem_eq (by simp), fun h => h.of_mem_eq (by simp)⟩

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.FrozenLoaded_setFpsr (img : Obj.Image) (s : State) (f : BitVec 32) :
    img.FrozenLoaded (s.setFpsr f) = img.FrozenLoaded s :=
  propext ⟨fun h => h.of_mem_eq (by simp), fun h => h.of_mem_eq (by simp)⟩

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.FrozenLoaded_orFpsr (img : Obj.Image) (s : State) (f : BitVec 32) :
    img.FrozenLoaded (s.orFpsr f) = img.FrozenLoaded s :=
  propext ⟨fun h => h.of_mem_eq (by simp), fun h => h.of_mem_eq (by simp)⟩

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.FrozenLoaded_setPhysMemAvail (img : Obj.Image) (s : State) (n : Nat) :
    img.FrozenLoaded (s.setPhysMemAvail n) = img.FrozenLoaded s :=
  propext ⟨fun h => h.of_mem_eq (by simp), fun h => h.of_mem_eq (by simp)⟩

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.FrozenLoaded_nextOracle (img : Obj.Image) (s : State) :
    img.FrozenLoaded s.nextOracle = img.FrozenLoaded s :=
  propext ⟨fun h => h.of_mem_eq (by simp), fun h => h.of_mem_eq (by simp)⟩

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.CallInv_writeReg64 (img : Obj.Image) (s : State) (r : Reg) (v : BitVec 64) :
    img.CallInv (s.writeReg64 r v) = img.CallInv s := by
  ext; simp [Obj.Image.CallInv]

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.CallInv_writeReg32 (img : Obj.Image) (s : State) (r : Reg) (v : BitVec 32) :
    img.CallInv (s.writeReg32 r v) = img.CallInv s := by
  ext; simp [Obj.Image.CallInv]

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.CallInv_writeReg (img : Obj.Image) (w : RegWidth) (s : State) (r : Reg) (v : BitVec 64) :
    img.CallInv (s.writeReg w r v) = img.CallInv s := by
  ext; simp [Obj.Image.CallInv]

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.CallInv_writeVReg128 (img : Obj.Image) (s : State) (idx : BitVec 5) (v : BitVec 128) :
    img.CallInv (s.writeVReg128 idx v) = img.CallInv s := by
  ext; simp [Obj.Image.CallInv]

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.CallInv_writeVReg64 (img : Obj.Image) (s : State) (idx : BitVec 5) (v : BitVec 64) :
    img.CallInv (s.writeVReg64 idx v) = img.CallInv s := by
  ext; simp [Obj.Image.CallInv]

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.CallInv_writeVReg32 (img : Obj.Image) (s : State) (idx : BitVec 5) (v : BitVec 32) :
    img.CallInv (s.writeVReg32 idx v) = img.CallInv s := by
  ext; simp [Obj.Image.CallInv]

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.CallInv_setPC (img : Obj.Image) (s : State) (pc : BitVec 64) :
    img.CallInv (s.setPC pc) = img.CallInv s := by
  ext; simp [Obj.Image.CallInv]

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.CallInv_advancePC (img : Obj.Image) (s : State) :
    img.CallInv s.advancePC = img.CallInv s := by
  ext; simp [Obj.Image.CallInv]

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.CallInv_setPState (img : Obj.Image) (s : State) (ps : PState) :
    img.CallInv (s.setPState ps) = img.CallInv s := by
  ext; simp [Obj.Image.CallInv]

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.CallInv_setStatus (img : Obj.Image) (s : State) (st : ExecStatus) :
    img.CallInv (s.setStatus st) = img.CallInv s := by
  ext; simp [Obj.Image.CallInv]

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.CallInv_applyWriteback (img : Obj.Image) (s : State) (wb : Option (Reg × BitVec 64)) :
    img.CallInv (applyWriteback s wb) = img.CallInv s := by
  cases wb <;> simp [applyWriteback]

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.CallInv_setTpidrEl0 (img : Obj.Image) (s : State) (v : BitVec 64) :
    img.CallInv (setTpidrEl0 s v) = img.CallInv s := by
  ext; simp [Obj.Image.CallInv]

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.CallInv_setFpsr (img : Obj.Image) (s : State) (f : BitVec 32) :
    img.CallInv (s.setFpsr f) = img.CallInv s := by
  ext; simp [Obj.Image.CallInv]

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.CallInv_orFpsr (img : Obj.Image) (s : State) (f : BitVec 32) :
    img.CallInv (s.orFpsr f) = img.CallInv s := by
  ext; simp [Obj.Image.CallInv]

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.CallInv_setPhysMemAvail (img : Obj.Image) (s : State) (n : Nat) :
    img.CallInv (s.setPhysMemAvail n) = img.CallInv s := by
  ext; simp [Obj.Image.CallInv]

@[simp, arm64_norm, wp_norm]
theorem Obj.Image.CallInv_nextOracle (img : Obj.Image) (s : State) :
    img.CallInv s.nextOracle = img.CallInv s := by
  ext; simp [Obj.Image.CallInv]

end

end ProofLib
