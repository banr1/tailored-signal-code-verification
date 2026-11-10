/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import ProofLib -- shake: keep
public import LibsignalBinary.Proofs.E2E.Bin.SpecsCommon
public import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Defs
import LibsignalBinary.Proofs.E2E.StoreNew.RoData
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.E2E.Bin.Fetch -- shake: keep
public meta import Lean -- shake: keep

/-!
# Segment Proofs for `libsignal_e2e::open` (`0x43a38..0x43d1c`)

Defines `binProg`, `BinEnv`, `SegExit`, `openSavedRegsAt`, and `OpenSeam`, and proves the 8
seam-to-seam segment obligations for `libsignal_e2e::open`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Bin

set_option warningAsError false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open Arm64 ProofLib ProofLib.ObjectLoad CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec

variable {C : Crypto} {A : RustAlloc} {S : SpqrModel}

abbrev binProg (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Program :=
  tripleRatchetProg img C ctl abs

structure BinEnv (C : Crypto) (A : RustAlloc) (S : SpqrModel) (img : Obj.Image)
    (_ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop where
  loads : Obj.Loads libsignalSessionImage img
  hooks : BinHooks C A S abs

def SegExit {α : Type} (prog : Program) (spec : Spec α) (g : α) (R : SepProp)
    (s0 s : State) (next : State → Prop) : Prop :=
  prog.CodeLoaded s.mem →
    ∃ sf, Steps prog s sf ∧ (next sf ∨ SubroutineOutcome spec g R s0 sf)

abbrev reaches_outcome_steps := @Arm64.reaches_outcome_steps

theorem segExit_chain {α : Type} {prog : Program} {spec : Spec α} {g : α} {R : SepProp}
    {s0 s : State} {next : State → Prop}
    (h1 : SegExit prog spec g R s0 s next)
    (h2 : ∀ s', next s' → reaches_outcome prog spec g R s0 s') :
    reaches_outcome prog spec g R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact reaches_outcome_steps hst (h2 sf hnext)
  · exact reaches_outcome_steps hst (reaches_outcome.of_outcome hout)

/-- Callee-saved registers `x19..x29` and link register `x30` spilled at the top of `open`'s
`0x3f0`-byte stack frame (`s0.sp - 0x60#64 .. s0.sp`, i.e., `s.sp + 0x390#64 .. s.sp + 0x3f0#64`). -/
def openSavedRegsAt (s0 : State) : SepProp :=
  ((s0.sp - 0x60#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 0x58#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((s0.sp - 0x50#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 0x48#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((s0.sp - 0x40#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 0x38#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 0x30#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 0x28#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 0x20#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 0x18#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 .x19)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section PreSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem tpidrEl0_setPC_pre_open (s : State) (pc : BitVec 64) :
    (s.setPC pc).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem tpidrEl0_setMem_setPC_pre_open (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_setPC_pre_open (s : State) (pc : BitVec 64) :
    (s.setPC pc).trace = s.trace := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_setMem_setPC_pre_open (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).trace = s.trace := by cases s; rfl

end PreSimp

theorem stackAt_split_bottom_open (sp : BitVec 64) (n d : Nat) (h : n + d ≤ 2 ^ 64) :
    stackAt sp (n + d) = memRegion (sp - BitVec.ofNat 64 (n + d)) d ∗ stackAt sp n := by
  simp only [stackAt]
  rw [show n + d = d + n by omega,
    memRegion_split' (n := d) (k := n) (by omega) rfl (by omega)]
  congr 2
  rw [BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 d), ← BitVec.sub_sub,
    BitVec.sub_add_cancel]

theorem stackAt_openStack_split (sp0 : BitVec 64) :
    stackAt sp0 openStack =
      memRegion (sp0 - openStack) (openStack - 0x3f0) ∗
      memRegion (sp0 - 0x3f0#64) 0x390 ∗
      cells (sp0 - 0x60#64) 12 := by
  have h1 := stackAt_split_bottom_open sp0 0x3f0 (openStack - 0x3f0) (by decide)
  rw [show 0x3f0 + (openStack - 0x3f0) = openStack by decide] at h1
  rw [h1]
  have h2 : stackAt sp0 0x3f0 = memRegion (sp0 - 0x3f0#64) 0x390 ∗ memRegion (sp0 - 0x60#64) 0x60 := by
    simp only [stackAt]
    rw [memRegion_split' (b := sp0 - 0x3f0#64) (b' := sp0 - 0x60#64)
      (N := 0x3f0) (n := 0x390) (k := 0x60) (by decide) (by bv_lin) (by decide)]
  rw [h2, show (0x60 : Nat) = 8 * 12 by rfl,
      LibsignalTripleRatchet.memRegion_cells (sp0 - 0x60#64) 12 (by decide)]
  rfl

theorem memRegion_232_head_split (out : BitVec 64) :
    memRegion out 232 = (∃∗ v : BitVec 64, out ↦₆₄ v) ∗ memRegion (out + 8#64) 224 := by
  rw [show (232 : Nat) = 8 + 224 from rfl,
      ProofLib.memRegion_split out 8 224 (by decide),
      StoreNew.memRegion_eight out]

theorem sepWP_done {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (hq : post s P) : SepWP prog target_pc s P post := by
  unfold SepWP
  exact fun _ hm => reaches_pc_refl hpc hrun ⟨P, hm, hq⟩

variable (C : Crypto) (A : RustAlloc) (S : SpqrModel) (img : Obj.Image) (ctl : BitVec 64)
  (abs : String → Option (State → State))

theorem who_ne_zero_zext {w : BitVec 32} (h0 : w ≠ 0#32) :
    (BitVec.zeroExtend 64 w == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  apply h0
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h1 ⊢
  have := w.isLt
  omega

theorem openSavedRegsAt_entails_cells (s0 : State) :
    Entails (openSavedRegsAt s0) (cells (s0.sp - 0x60#64) 12) := by
  dsimp only [openSavedRegsAt]
  apply cells_sub_succ_entails 96 12
  apply cells_sub_succ_entails 88 11
  apply cells_sub_succ_entails 80 10
  apply cells_sub_succ_entails 72 9
  apply cells_sub_succ_entails 64 8
  apply cells_sub_succ_entails 56 7
  apply cells_sub_succ_entails 48 6
  apply cells_sub_succ_entails 40 5
  apply cells_sub_succ_entails 32 4
  apply cells_sub_succ_entails 24 3
  apply cells_sub_succ_entails 16 2
  rw [cells_sub_succ s0.sp 8 1 (by decide) (by decide), ProofLib.cells_zero]
  exact Entails.sepExists_right _ (by rw [sepConj_emp]; exact Entails.refl _)

macro "ac_sat " h:term : tactic => `(tactic| (refine Satisfies.of_eq $h ?_; ac_rfl))

macro "cells_unfold_goal" : tactic =>
  `(tactic| simp (disch := decide) only [ProofLib.cells_sub_succ, Nat.reduceSub,
    ProofLib.cells_zero, sepConj_emp,
    sepExists_sepConj_right])

theorem readReg64_congr_reg (s : State) (r1 r2 : Reg) (h : r1 = r2) :
    s.readReg64 r1 = s.readReg64 r2 :=
  congrArg s.readReg64 h

theorem readReg64_writeReg64_sp_gpr (s : State) (r1 : Reg) (v : BitVec 64) (idx : BitVec 5)
    (hr1 : r1 = Reg.sp) :
    (s.writeReg64 r1 v).readReg64 (Reg.gpr idx) = s.readReg64 (Reg.gpr idx) := by
  subst hr1; rfl

theorem readReg64_writeReg64_gpr_same (s : State) (r1 : Reg) (idx : BitVec 5) (v : BitVec 64)
    (hr1 : r1 = Reg.gpr idx) (h31 : (idx == 31#5) = false) :
    (s.writeReg64 r1 v).readReg64 (Reg.gpr idx) = v := by
  subst hr1
  simp [State.writeReg64, State.readReg64, RegFile.read, RegFile.write, h31]

theorem readReg64_writeReg64_gpr_diff (s : State) (r1 : Reg) (idx1 idx2 : BitVec 5) (v : BitVec 64)
    (hr1 : r1 = Reg.gpr idx1) (hne : (idx2 == idx1) = false) :
    (s.writeReg64 r1 v).readReg64 (Reg.gpr idx2) = s.readReg64 (Reg.gpr idx2) := by
  subst hr1
  have hne' : idx2 ≠ idx1 := by intro h; subst h; simp at hne
  by_cases h1 : idx1 = 31#5 <;> by_cases h2 : idx2 = 31#5 <;>
    simp [State.writeReg64, State.readReg64, RegFile.read, RegFile.write, h1, h2, hne']

theorem sp_setMem_step (s : State) (m : Memory) : (s.setMem m).sp = s.sp := rfl
theorem sp_setPC_step (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := rfl
theorem sp_setPState_step (s : State) (ps : PState) : (s.setPState ps).sp = s.sp := rfl
theorem sp_advancePC_step (s : State) : s.advancePC.sp = s.sp := rfl

theorem sp_writeReg64_sp_step (s : State) (r1 : Reg) (v : BitVec 64) (hr1 : r1 = Reg.sp) :
    (s.writeReg64 r1 v).sp = v := by
  subst hr1; rfl

theorem sp_writeReg64_gpr_step (s : State) (r1 : Reg) (idx : BitVec 5) (v : BitVec 64)
    (hr1 : r1 = Reg.gpr idx) :
    (s.writeReg64 r1 v).sp = s.sp := by
  subst hr1; rfl

meta partial def proveStateSPSpine (s : Lean.Expr) : Lean.MetaM (Option (Lean.Expr × Lean.Expr)) := do
  if s.isAppOfArity ``State.setMem 2 then
    let s' := s.getArg! 0
    let step1 := Lean.mkApp2 (Lean.mkConst ``sp_setMem_step) s' (s.getArg! 1)
    if let some (val, prf') ← proveStateSPSpine s' then
      return some (val, ← Lean.Meta.mkEqTrans step1 prf')
    return some (Lean.mkApp (Lean.mkConst ``State.sp) s', step1)
  else if s.isAppOfArity ``State.setPC 2 then
    let s' := s.getArg! 0
    let step1 := Lean.mkApp2 (Lean.mkConst ``sp_setPC_step) s' (s.getArg! 1)
    if let some (val, prf') ← proveStateSPSpine s' then
      return some (val, ← Lean.Meta.mkEqTrans step1 prf')
    return some (Lean.mkApp (Lean.mkConst ``State.sp) s', step1)
  else if s.isAppOfArity ``State.setPState 2 then
    let s' := s.getArg! 0
    let step1 := Lean.mkApp2 (Lean.mkConst ``sp_setPState_step) s' (s.getArg! 1)
    if let some (val, prf') ← proveStateSPSpine s' then
      return some (val, ← Lean.Meta.mkEqTrans step1 prf')
    return some (Lean.mkApp (Lean.mkConst ``State.sp) s', step1)
  else if s.isAppOfArity ``State.advancePC 1 then
    let s' := s.getArg! 0
    let step1 := Lean.mkApp (Lean.mkConst ``sp_advancePC_step) s'
    if let some (val, prf') ← proveStateSPSpine s' then
      return some (val, ← Lean.Meta.mkEqTrans step1 prf')
    return some (Lean.mkApp (Lean.mkConst ``State.sp) s', step1)
  else if s.isAppOfArity ``State.writeReg64 3 then
    let s' := s.getArg! 0
    let r1 := s.getArg! 1
    let v := s.getArg! 2
    let some rk ← ProofLib.evalRegKind? r1 | return none
    match rk with
    | .sp =>
      let hr1 ← Lean.Meta.mkEqRefl (Lean.mkConst ``Reg.sp)
      return some (v, Lean.mkApp4 (Lean.mkConst ``sp_writeReg64_sp_step) s' r1 v hr1)
    | .gpr idx1 =>
      let idx1Expr := ProofLib.mkCanonBitVecLit 5 idx1.toNat
      let canonReg1 := Lean.mkApp (Lean.mkConst ``Reg.gpr) idx1Expr
      let hr1 ← Lean.Meta.mkEqRefl canonReg1
      let step1 := Lean.mkApp5 (Lean.mkConst ``sp_writeReg64_gpr_step) s' r1 idx1Expr v hr1
      if let some (val, prf') ← proveStateSPSpine s' then
        return some (val, ← Lean.Meta.mkEqTrans step1 prf')
      return some (Lean.mkApp (Lean.mkConst ``State.sp) s', step1)
    | .xzr => return none
  else
    return none

simproc ↓ [arm64_norm, wp_norm] fastStateSP (State.sp _) := fun e => do
  if e.getAppNumArgs != 1 then return .continue
  if let some (spExpr, prf) ← proveStateSPSpine (e.getArg! 0) then
    return .visit { expr := spExpr, proof? := some prf }
  return .continue

theorem readReg64_sp_of_sp_eq (s : State) (r : Reg) (v : BitVec 64)
    (hr : r = Reg.sp) (hv : s.sp = v) :
    s.readReg64 r = v := by
  subst hr
  exact hv

meta partial def proveReadReg64GprCanon (s : Lean.Expr) (idx : BitVec 5)
    (idxExpr canonReg : Lean.Expr) : Lean.MetaM (Option (Lean.Expr × Lean.Expr)) := do
  if s.isAppOfArity ``State.setMem 2 then
    let s' := s.getArg! 0
    let m := s.getArg! 1
    let step1 := Lean.mkApp3 (Lean.mkConst ``State.readReg64_setMem) s' m canonReg
    if let some (val, prf') ← proveReadReg64GprCanon s' idx idxExpr canonReg then
      return some (val, ← Lean.Meta.mkEqTrans step1 prf')
    return some (Lean.mkApp2 (Lean.mkConst ``State.readReg64) s' canonReg, step1)
  else if s.isAppOfArity ``State.setPC 2 then
    let s' := s.getArg! 0
    let pc := s.getArg! 1
    let step1 := Lean.mkApp3 (Lean.mkConst ``State.readReg64_setPC) s' pc canonReg
    if let some (val, prf') ← proveReadReg64GprCanon s' idx idxExpr canonReg then
      return some (val, ← Lean.Meta.mkEqTrans step1 prf')
    return some (Lean.mkApp2 (Lean.mkConst ``State.readReg64) s' canonReg, step1)
  else if s.isAppOfArity ``State.setPState 2 then
    let s' := s.getArg! 0
    let ps := s.getArg! 1
    let step1 := Lean.mkApp3 (Lean.mkConst ``State.readReg64_setPState) s' ps canonReg
    if let some (val, prf') ← proveReadReg64GprCanon s' idx idxExpr canonReg then
      return some (val, ← Lean.Meta.mkEqTrans step1 prf')
    return some (Lean.mkApp2 (Lean.mkConst ``State.readReg64) s' canonReg, step1)
  else if s.isAppOfArity ``State.advancePC 1 then
    let s' := s.getArg! 0
    let step1 := Lean.mkApp2 (Lean.mkConst ``State.readReg64_advancePC) s' canonReg
    if let some (val, prf') ← proveReadReg64GprCanon s' idx idxExpr canonReg then
      return some (val, ← Lean.Meta.mkEqTrans step1 prf')
    return some (Lean.mkApp2 (Lean.mkConst ``State.readReg64) s' canonReg, step1)
  else if s.isAppOfArity ``State.writeReg64 3 then
    let s' := s.getArg! 0
    let r1 := s.getArg! 1
    let v := s.getArg! 2
    let some rk ← ProofLib.evalRegKind? r1 | return none
    match rk with
    | .sp =>
      let hr1 ← Lean.Meta.mkEqRefl (Lean.mkConst ``Reg.sp)
      let step1 := Lean.mkApp5 (Lean.mkConst ``readReg64_writeReg64_sp_gpr) s' r1 v idxExpr hr1
      if let some (val, prf') ← proveReadReg64GprCanon s' idx idxExpr canonReg then
        return some (val, ← Lean.Meta.mkEqTrans step1 prf')
      return some (Lean.mkApp2 (Lean.mkConst ``State.readReg64) s' canonReg, step1)
    | .gpr idx1 =>
      if idx1 == idx then
        let hr1 ← Lean.Meta.mkEqRefl canonReg
        let h31 ← Lean.Meta.mkEqRefl (Lean.mkConst ``Bool.false)
        let prf := Lean.mkAppN (Lean.mkConst ``readReg64_writeReg64_gpr_same)
          #[s', r1, idxExpr, v, hr1, h31]
        return some (v, prf)
      else
        let idx1Expr := ProofLib.mkCanonBitVecLit 5 idx1.toNat
        let canonReg1 := Lean.mkApp (Lean.mkConst ``Reg.gpr) idx1Expr
        let hr1 ← Lean.Meta.mkEqRefl canonReg1
        let hne ← Lean.Meta.mkEqRefl (Lean.mkConst ``Bool.false)
        let step1 := Lean.mkAppN (Lean.mkConst ``readReg64_writeReg64_gpr_diff)
          #[s', r1, idx1Expr, idxExpr, v, hr1, hne]
        if let some (val, prf') ← proveReadReg64GprCanon s' idx idxExpr canonReg then
          return some (val, ← Lean.Meta.mkEqTrans step1 prf')
        return some (Lean.mkApp2 (Lean.mkConst ``State.readReg64) s' canonReg, step1)
    | .xzr => return none
  else
    return none

theorem readReg64_xzr_eq (s : State) (r : Reg) (hr : r = Reg.xzr) :
    s.readReg64 r = 0#64 := by
  subst hr; rfl

theorem readReg64_gpr31_eq (s : State) (r : Reg) (hr : r = Reg.gpr 31#5) :
    s.readReg64 r = 0#64 := by
  subst hr; rfl

@[local arm64_norm, local wp_norm]
theorem bv_add_neg_0x60 (x : BitVec 64) :
    x + bv% (2 ^ 64 - 96) = x - 96#64 := by bv_lin

meta def proveReadReg64Any (s r : Lean.Expr) : Lean.MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let some rk ← ProofLib.evalRegKind? r | return none
  match rk with
  | .xzr =>
    let z := ProofLib.mkCanonBitVecLit 64 0
    let hr ← Lean.Meta.mkEqRefl (Lean.mkConst ``Reg.xzr)
    let prf := Lean.mkApp3 (Lean.mkConst ``readReg64_xzr_eq) s r hr
    return some (z, prf)
  | .sp =>
    let hr ← Lean.Meta.mkEqRefl (Lean.mkConst ``Reg.sp)
    if let some (spExpr, hv) ← proveStateSPSpine s then
      let prf := Lean.mkAppN (Lean.mkConst ``readReg64_sp_of_sp_eq) #[s, r, spExpr, hr, hv]
      return some (spExpr, prf)
    let spExpr := Lean.mkApp (Lean.mkConst ``State.sp) s
    let hv ← Lean.Meta.mkEqRefl spExpr
    let prf := Lean.mkAppN (Lean.mkConst ``readReg64_sp_of_sp_eq) #[s, r, spExpr, hr, hv]
    return some (spExpr, prf)
  | .gpr idx =>
    if idx == 31#5 then return none
    let idxExpr := ProofLib.mkCanonBitVecLit 5 idx.toNat
    let canonReg := Lean.mkApp (Lean.mkConst ``Reg.gpr) idxExpr
    if let some (valExpr, prfCanon) ← proveReadReg64GprCanon s idx idxExpr canonReg then
      let prf ← if r == canonReg then pure prfCanon else do
        let hreg := Lean.mkApp4 (Lean.mkConst ``readReg64_congr_reg)
          s r canonReg (← Lean.Meta.mkEqRefl canonReg)
        Lean.Meta.mkEqTrans hreg prfCanon
      return some (valExpr, prf)
    if r != canonReg then
      let hreg := Lean.mkApp4 (Lean.mkConst ``readReg64_congr_reg)
        s r canonReg (← Lean.Meta.mkEqRefl canonReg)
      return some (Lean.mkApp2 (Lean.mkConst ``State.readReg64) s canonReg, hreg)
    return none

theorem readReg32_of_readReg64_eq (s : State) (r : Reg) (v : BitVec 64)
    (h : s.readReg64 r = v) :
    s.readReg32 r = v.truncate 32 :=
  congrArg (BitVec.truncate 32) h

theorem readReg_w64_of_readReg64_eq (s : State) (r : Reg) (w : RegWidth) (v : BitVec 64)
    (hw : w = .W64) (h : s.readReg64 r = v) :
    s.readReg w r = v := by
  subst hw; exact h

theorem readReg_w32_of_readReg64_eq (s : State) (r : Reg) (w : RegWidth) (v : BitVec 64)
    (hw : w = .W32) (h : s.readReg64 r = v) :
    s.readReg w r = (v.truncate 32).zeroExtend 64 := by
  subst hw; exact congrArg (fun x : BitVec 64 => (x.truncate 32).zeroExtend 64) h

simproc ↓ [arm64_norm, wp_norm] fastReadReg64 (State.readReg64 _ _) := fun e => do
  if e.getAppNumArgs != 2 then return .continue
  if let some (valExpr, prf) ← proveReadReg64Any (e.getArg! 0) (e.getArg! 1) then
    return .visit { expr := valExpr, proof? := some prf }
  return .continue

simproc ↓ [arm64_norm, wp_norm] fastReadReg32 (State.readReg32 _ _) := fun e => do
  if e.getAppNumArgs != 2 then return .continue
  let s := e.getArg! 0
  let r := e.getArg! 1
  if let some (val64, prf64) ← proveReadReg64Any s r then
    let target := Lean.mkApp3 (Lean.mkConst ``BitVec.truncate)
      (Lean.toExpr (64 : Nat)) (Lean.toExpr (32 : Nat)) val64
    let prf := Lean.mkApp4 (Lean.mkConst ``readReg32_of_readReg64_eq) s r val64 prf64
    return .visit { expr := target, proof? := some prf }
  return .continue

simproc ↓ [arm64_norm, wp_norm] fastReadReg (State.readReg _ _ _) := fun e => do
  if e.getAppNumArgs != 3 then return .continue
  let s := e.getArg! 0
  let w := e.getArg! 1
  let r := e.getArg! 2
  let some rw ← ProofLib.evalRegWidth? w | return .continue
  if let some (val64, prf64) ← proveReadReg64Any s r then
    match rw with
    | .W64 =>
      let hw ← Lean.Meta.mkEqRefl (Lean.mkConst ``RegWidth.W64)
      let prf := Lean.mkAppN (Lean.mkConst ``readReg_w64_of_readReg64_eq) #[s, r, w, val64, hw, prf64]
      return .visit { expr := val64, proof? := some prf }
    | .W32 =>
      let hw ← Lean.Meta.mkEqRefl (Lean.mkConst ``RegWidth.W32)
      let trunc := Lean.mkApp3 (Lean.mkConst ``BitVec.truncate)
        (Lean.toExpr (64 : Nat)) (Lean.toExpr (32 : Nat)) val64
      let target := Lean.mkApp3 (Lean.mkConst ``BitVec.zeroExtend)
        (Lean.toExpr (32 : Nat)) (Lean.toExpr (64 : Nat)) trunc
      let prf := Lean.mkAppN (Lean.mkConst ``readReg_w32_of_readReg64_eq) #[s, r, w, val64, hw, prf64]
      return .visit { expr := target, proof? := some prf }
  return .continue

attribute [-arm64_norm, -wp_norm]
  ProofLib.reduceStateSP
  ProofLib.reduceStateReadReg64
  ProofLib.reduceStateReadReg32
  ProofLib.reduceStateReadReg

theorem Satisfies.mono {m : Memory} {P Q : SepProp} (h : P ⊢ Q) (hm : m ⊨ P) : m ⊨ Q := by
  exact Arm64.Satisfies.mono h hm

theorem emp_entails_anyHeap : emp ⊢ anyHeap := by
  exact ProofLib.entails_anyHeap emp

theorem spAligned_sub_0x3f0 {s0 sf : State} (hal0 : s0.spAligned = true)
    (hsp : sf.sp = s0.sp - 0x3f0#64) : sf.spAligned = true := by
  rw [State.spAligned, hsp]
  exact spAligned_sub_beq hal0 rfl

theorem who_sub_one_ne_zero {w : BitVec 32} (h1 : w ≠ 1#32) :
    (w - 1#32 == 0#32) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  apply h1
  have := congrArg (· + 1#32) h
  simpa [BitVec.sub_add_cancel] using this

theorem subsPState32_z_false {w : BitVec 32} (h1 : w ≠ 1#32) :
    (subsPState32 w 1#32).z = false := by
  simp only [subsPState32, AddWithCarry32]
  rw [beq_eq_false_iff_ne]
  intro h
  apply h1
  apply BitVec.eq_of_toNat_eq
  have h2 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_ofNat, ite_true] at h2 ⊢
  have := w.isLt
  omega

theorem open_seg_parties_err_outcome {A : RustAlloc} {img : Obj.Image}
    {g : OpenGhost} {R : SepProp} {s0 sf : State}
    (hwho0 : g.who ≠ 0#32) (hwho1 : g.who ≠ 1#32)
    (hret : Returned s0 sf) (hcc : CallingConventionPreserved s0 sf)
    (htr : sf.trace = s0.trace) (_htpidr : sf.tpidrEl0 = s0.tpidrEl0)
    (hm_sf : sf.mem ⊨ (openSavedRegsAt s0 ∗ (g.outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
      (memRegion (g.outPtr + 8#64) 224 ∗
       memRegion (s0.sp - openStack) (openStack - 0x3f0) ∗
       memRegion (s0.sp - 0x3f0#64) 0x390 ∗
       (g.statePtr ↦ₛ g.stateBytes) ∗
       tlsKeysAt (s0.tpidrEl0 + tlsKeysTpoff) g.tlsInit ∗
       A.pool)) ∗ R) :
    SubroutineOutcome (openSpec A img) g R s0 sf := by
  left
  refine ⟨hret, hcc, ?_⟩
  have hrole : Role.ofWho g.who = none := by
    simp [Role.ofWho, hwho0, hwho1]
  have h1 : tlsKeysAt (s0.tpidrEl0 + tlsKeysTpoff) g.tlsInit ⊢
      (∃∗ tlsCur, tlsKeysAt (s0.tpidrEl0 + tlsKeysTpoff) tlsCur) :=
    Entails.sepExists_right g.tlsInit (Entails.refl _)
  have h2 := openSavedRegsAt_entails_cells s0
  have hm0 : sf.mem ⊨ (openSavedRegsAt s0 ∗ (g.outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
      (memRegion (g.outPtr + 8#64) 224 ∗
       memRegion (s0.sp - openStack) (openStack - 0x3f0) ∗
       memRegion (s0.sp - 0x3f0#64) 0x390 ∗
       (g.statePtr ↦ₛ g.stateBytes) ∗
       tlsKeysAt (s0.tpidrEl0 + tlsKeysTpoff) g.tlsInit ∗
       A.pool)) ∗ (R ∗ emp) := by
    rwa [sepConj_emp]
  have hm1 := Satisfies.mono
    (sepConj_mono
      (sepConj_mono h2 (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono h1 (Entails.refl _))))))))
      (sepConj_mono_right emp_entails_anyHeap)) hm0
  simp only [openSpec, Spec.inImage, evalOpen, openResultAt, hrole,
    stackAt_openStack_split s0.sp, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr, ?_⟩
  ac_sat hm1

/-! ## Segment 2: `open_seg_deserialize` (`+0x054..+0x080`) -/

def sessionRecordHeap (A : RustAlloc) (G : SessionGhost) (sess : Session (List (BitVec 8))) : SepProp :=
  ⌜PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
    G.alice.bytes = sess.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
    (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat⌝ ∗
    RawByteMove.sessionHeap A G sess.state

theorem vecAt_empty_0_8 (A : RustAlloc) (r : BitVec 64) :
    vecAt A 24 8 (fun (_ : Unit) _ => emp) r 0#64 8#64 [] =
      (r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ 8#64) ∗ ((r + 16#64) ↦₆₄ 0#64) := by
  simp [vecAt, vecBuf]
  ac_rfl

theorem sessionRecordAt_eq_word0_sep_tail_sep_heap (A : RustAlloc) (r : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) :
    sessionRecordAt A r ⟨0#64, 8#64, some G⟩ ⟨some sess⟩ =
      ∃∗ bs : List (BitVec 8),
        ⌜bs.length = 344 ∧ RawByteMove.SessionInline G sess.state bs⌝ ∗
        (r ↦₆₄ 0#64) ∗
        ((r + 8#64) ↦ₛ (unpack64 8#64 ++ unpack64 0#64 ++ bs)) ∗
        sessionRecordHeap A G sess := by
  dsimp only [sessionRecordAt, sessionStateReprAt, sessionRecordHeap]
  rw [vecAt_empty_0_8 A r, RawByteMove.sessionStateAt_eq_inline_sep_heap A (r + 0x18#64) G sess.state]
  apply RawByteMove.sepProp_eq_of_entails
  · rw [sepExists_sepConj_right, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs
    rw [← sepConj_assoc, ← sepConj_assoc,
        sepConj_comm _ ⌜bs.length = 344 ∧ RawByteMove.SessionInline G sess.state bs⌝,
        sepConj_assoc]
    apply Entails.pure_left; rintro ⟨hlen, hinl⟩
    refine Entails.sepExists_right bs ?_
    apply Entails.pure_right ⟨hlen, hinl⟩
    rw [pointsTo64_eq_pointsToBytes (r + 8#64) 8#64,
        pointsTo64_eq_pointsToBytes (r + 16#64) 0#64]
    have h8_16 : (r + 8#64) + BitVec.ofNat 64 (unpack64 8#64).length = r + 16#64 := by
      rw [unpack64_length]; bv_lin
    have h16_24 : (r + 16#64) + BitVec.ofNat 64 (unpack64 0#64).length = r + 0x18#64 := by
      rw [unpack64_length]; bv_lin
    rw [List.append_assoc, pointsToBytes_append, h8_16,
        pointsToBytes_append, h16_24]
    exact Entails.of_eq (by ac_rfl)
  · apply Entails.sepExists_elim; intro bs
    apply Entails.pure_left; rintro ⟨hlen, hinl⟩
    rw [sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_right bs ?_
    rw [pointsTo64_eq_pointsToBytes (r + 8#64) 8#64,
        pointsTo64_eq_pointsToBytes (r + 16#64) 0#64]
    have h8_16 : (r + 8#64) + BitVec.ofNat 64 (unpack64 8#64).length = r + 16#64 := by
      rw [unpack64_length]; bv_lin
    have h16_24 : (r + 16#64) + BitVec.ofNat 64 (unpack64 0#64).length = r + 0x18#64 := by
      rw [unpack64_length]; bv_lin
    rw [List.append_assoc, pointsToBytes_append, h8_16,
        pointsToBytes_append, h16_24]
    have hpull :
        ((r ↦₆₄ 0#64) ∗
          (((r + 8#64) ↦ₛ unpack64 8#64) ∗ ((r + 16#64) ↦ₛ unpack64 0#64) ∗ ((r + 0x18#64) ↦ₛ bs)) ∗
          (⌜PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
            G.alice.bytes = sess.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
            (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat⌝ ∗
           RawByteMove.sessionHeap A G sess.state)) =
        (((r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦ₛ unpack64 8#64) ∗ ((r + 16#64) ↦ₛ unpack64 0#64)) ∗
          ⌜PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
            G.alice.bytes = sess.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
            (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat⌝ ∗
          (((r + 0x18#64) ↦ₛ bs) ∗ RawByteMove.sessionHeap A G sess.state)) := by ac_rfl
    rw [hpull]
    apply sepConj_mono_right
    apply sepConj_mono_right
    exact Entails.pure_right ⟨hlen, hinl⟩ (Entails.refl _)

end CryptoVerification.E2E.Bin



