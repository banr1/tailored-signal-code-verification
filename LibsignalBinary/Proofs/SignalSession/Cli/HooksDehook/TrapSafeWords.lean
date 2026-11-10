/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost -- proof-setup: allow-public-import
public import VerifiedLibraries.Musl.Proofs.Code
public import ProofLib.StdStartup.Strlen
public import VerifiedLibraries.RustStd.Generated.CorePlacedObj
public import VerifiedLibraries.RustStd.Generated.TimePlacedObj
import ProofLib.OpcodeExclusion
import ProofLib.Placed.Pair
import ProofLib.ProgramReflection.Variant.TrapTransfer

/-!
# Generic `lr`-Trap Classifier over Multi-Block Word Lists (`HooksDehook.TrapSafeWords`)

Generalizes `HooksDehook.MemsetLrTrap` (`isBlk21SafeInstr`) and `HooksDehook.MemcpyLrTrap`
(`isBlk20SafeInstr`) to an arbitrary `TrapRegion := List (BitVec 64 × List (BitVec 32))`
(multi-block union of `(base, words)` blocks), discharging `keepOf region (u.readReg64 .lr) = false`
at ghost extern call sites and providing `decide`-checked `<row>_all_safe` certificates.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords

open Arm64 ProofLib
open VerifiedLibraries.Mallocng (mallocngBlockProg)
open VerifiedLibraries.Musl (memsetWordsSym memcpySymWords bcmpWords bcmpCalls memcmpLibcaWords
  memmoveLibcaWords memmoveLibcaCalls)
open ProofLib.StdStartup (muslStrlenWords)
open VerifiedLibraries.RustStd (coreMultiLib timeMultiLib)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ActiveRealPre ActiveRealRun
  keepFsTrace linkedCallHook)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (memsetWordsSym_length
  mallocngBlockProg21_hasWords)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (keepMemsetBlk21)

/-! ## 1. Multi-Block `TrapRegion`, `keepOf`, and Generic Syntactic Classifier (`isTrapSafeInstr`) -/

/-- A multi-block trap region: `(base, words)` blocks spanning `[base, base + 4 * words.length)`. -/
abbrev TrapRegion : Type := List (BitVec 64 × List (BitVec 32))
/-- Decidable check that `pc` lies in `[base, base + numBytes)`. -/
@[expose] def keepBlock (base : BitVec 64) (numBytes : Nat) (pc : BitVec 64) : Bool :=
  decide ((pc - base).toNat < numBytes)
/-- Decidable check that `pc` lies inside at least one block of `region`. -/
@[expose] def keepOf (region : TrapRegion) (pc : BitVec 64) : Bool :=
  region.any fun (base, ws) => keepBlock base (4 * ws.length) pc
/-- Decidable check that byte offset `o` lies in `[regionLo, regionHi)`. -/
@[expose] def inByteInterval (regionLo regionHi o : Nat) : Bool :=
  decide (regionLo ≤ o) && decide (o < regionHi)

/-- Generic syntactic `lr`-trap instruction classifier over `[regionLo, regionHi)` (40 `Instr`
    constructors: strict superset of `isBlk21SafeInstr` ∪ `isBlk20SafeInstr`). -/
@[expose] def isTrapSafeInstr (regionLo regionHi : Nat) (off : Nat) (inst : Instr) : Bool :=
  let nextOk := inByteInterval regionLo regionHi (off + 4)
  match inst with
  | .ret rn => decide (rn = .lr)
  | .nop => nextOk
  | .b relOff => inByteInterval regionLo regionHi (BitVec.ofNat 64 off + relOff).toNat
  | .bCond _ relOff => nextOk && inByteInterval regionLo regionHi (BitVec.ofNat 64 off + relOff).toNat
  | .cbz _ _ _ relOff => nextOk && inByteInterval regionLo regionHi (BitVec.ofNat 64 off + relOff).toNat
  | .tbz _ _ _ _ relOff => nextOk && inByteInterval regionLo regionHi (BitVec.ofNat 64 off + relOff).toNat
  | .adr _ rd _ => nextOk && decide (rd ≠ .lr)
  | .addSubImm _ _ rd _ _ _ => nextOk && decide (rd ≠ .lr)
  | .logicalImm _ _ rd _ _ => nextOk && decide (rd ≠ .lr)
  | .moveWide _ _ rd _ _ => nextOk && decide (rd ≠ .lr)
  | .bitfield _ _ rd _ _ _ => nextOk && decide (rd ≠ .lr)
  | .extr _ rd _ _ _ => nextOk && decide (rd ≠ .lr)
  | .logicalShift _ _ rd _ _ _ _ => nextOk && decide (rd ≠ .lr)
  | .addSubShift _ _ rd _ _ _ _ => nextOk && decide (rd ≠ .lr)
  | .addSubExt _ _ rd _ _ _ _ => nextOk && decide (rd ≠ .lr)
  | .addSubCarry _ _ rd _ _ => nextOk && decide (rd ≠ .lr)
  | .condCompareReg _ _ _ _ _ _ => nextOk
  | .condCompareImm _ _ _ _ _ _ => nextOk
  | .condSelect _ _ rd _ _ _ => nextOk && decide (rd ≠ .lr)
  | .dataProc1 _ _ rd _ => nextOk && decide (rd ≠ .lr)
  | .dataProc2 _ _ rd _ _ => nextOk && decide (rd ≠ .lr)
  | .dataProc3 _ _ rd _ _ _ => nextOk && decide (rd ≠ .lr)
  | .ldr _ _ _ rt addr => nextOk && decide (rt ≠ .lr) && decide (addr.baseReg ≠ .lr)
  | .ldrLit _ _ rt _ => nextOk && decide (rt ≠ .lr)
  | .str _ _ addr => nextOk && decide (addr.baseReg ≠ .lr)
  | .ldp _ _ rt1 rt2 addr =>
    nextOk && decide (rt1 ≠ .lr) && decide (rt2 ≠ .lr) && decide (addr.baseReg ≠ .lr)
  | .stp _ _ _ addr => nextOk && decide (addr.baseReg ≠ .lr)
  | .ldrSimd _ _ addr => nextOk && decide (addr.baseReg ≠ .lr)
  | .strSimd _ _ addr => nextOk && decide (addr.baseReg ≠ .lr)
  | .ldpSimd _ _ _ addr => nextOk && decide (addr.baseReg ≠ .lr)
  | .stpSimd _ _ _ addr => nextOk && decide (addr.baseReg ≠ .lr)
  | .fmovGprVec _ _ _ opcode _ rd =>
    nextOk && (decide (opcode = 0b111#3 ∨ opcode = 0b010#3 ∨ opcode = 0b011#3) ||
      decide (Reg.fromZRBits rd ≠ .lr))
  | .simdImmShift _ _ _ _ _ _ _ => nextOk
  | .simdInsDup _ _ _ _ _ rd => nextOk && decide (Reg.fromZRBits rd ≠ .lr)
  | .simdThreeSame _ _ _ _ _ _ _ => nextOk
  | .simdTwoRegMisc _ _ _ _ _ _ => nextOk
  | .simdAcrossLanes _ _ _ _ _ _ => nextOk
  | .sysReg isRead sysreg rt =>
    nextOk && isRead && decide (sysreg = 0x5807#15) && decide (rt ≠ .lr)
  | .dcZva _ => nextOk
  | .barrier _ _ => nextOk
  | _ => false

theorem isTrapSafeInstr_not_isSvc0 {regionLo regionHi off : Nat} {inst : Instr}
    (h : isTrapSafeInstr regionLo regionHi off inst = true) :
    inst.isSvc0 = false := by
  cases inst <;> simp [isTrapSafeInstr, Instr.isSvc0] at h ⊢

/-- Single-instruction outcome for an instruction inside `[regionLo, regionHi)` relative to `base`:
    either faults with `.Exception msg`, or remains `.Running` with unchanged `lr` and `pc`
    equal to `s.readReg64 .lr` or `base + off'` (`regionLo ≤ off' ∧ off' < regionHi`). -/
@[expose] def TrapStepOutcome (base : BitVec 64) (regionLo regionHi : Nat) (s s' : State) : Prop :=
  (∃ msg, s'.status = .Exception msg) ∨
  (s'.status = .Running ∧
   s'.readReg64 .lr = s.readReg64 .lr ∧
   (s'.pc = s.readReg64 .lr ∨
    ∃ off' : Nat, regionLo ≤ off' ∧ off' < regionHi ∧ s'.pc = base + BitVec.ofNat 64 off'))

private def SameRunLrPc (s s1 : State) : Prop :=
  s1.status = s.status ∧ s1.readReg64 .lr = s.readReg64 .lr ∧ s1.pc = s.pc

private theorem readReg64_lr_writeReg64_ne (s : State) {r : Reg} (hr : r ≠ .lr) (v : BitVec 64) :
    (s.writeReg64 r v).readReg64 .lr = s.readReg64 .lr := by
  cases r with
  | gpr idx =>
    unfold State.writeReg64 State.readReg64 RegFile.read RegFile.write
    have hne : 30#5 ≠ idx := fun h => hr (by subst h; rfl)
    by_cases h31 : idx == 31#5
    · simp [h31]
    · simp [h31, hne]
  | sp => rfl
  | xzr => rfl

private theorem sameRunLrPc_refl (s : State) : SameRunLrPc s s := ⟨rfl, rfl, rfl⟩
private theorem sameRunLrPc_writeReg64 {s s1 : State} (h : SameRunLrPc s s1) {r : Reg}
    (hr : r ≠ .lr) (v : BitVec 64) : SameRunLrPc s (s1.writeReg64 r v) :=
  ⟨h.1, (readReg64_lr_writeReg64_ne s1 hr v).trans h.2.1, h.2.2⟩
private theorem sameRunLrPc_writeReg32 {s s1 : State} (h : SameRunLrPc s s1) {r : Reg}
    (hr : r ≠ .lr) (v : BitVec 32) : SameRunLrPc s (s1.writeReg32 r v) :=
  sameRunLrPc_writeReg64 h hr _
private theorem sameRunLrPc_writeReg {s s1 : State} (h : SameRunLrPc s s1) (w : Width) {r : Reg}
    (hr : r ≠ .lr) (v : BitVec 64) : SameRunLrPc s (s1.writeReg w r v) :=
  sameRunLrPc_writeReg64 h hr _
private theorem sameRunLrPc_writeVReg128 {s s1 : State} (h : SameRunLrPc s s1) (vt : VReg)
    (v : BitVec 128) : SameRunLrPc s (s1.writeVReg128 vt v) := ⟨h.1, h.2.1, h.2.2⟩
private theorem sameRunLrPc_writeVReg64 {s s1 : State} (h : SameRunLrPc s s1) (vt : VReg)
    (v : BitVec 64) : SameRunLrPc s (s1.writeVReg64 vt v) := ⟨h.1, h.2.1, h.2.2⟩
private theorem sameRunLrPc_writeVReg32 {s s1 : State} (h : SameRunLrPc s s1) (vt : VReg)
    (v : BitVec 32) : SameRunLrPc s (s1.writeVReg32 vt v) := ⟨h.1, h.2.1, h.2.2⟩
private theorem sameRunLrPc_orFpsr {s s1 : State} (h : SameRunLrPc s s1) (flags : BitVec 32) :
    SameRunLrPc s (s1.orFpsr flags) := ⟨h.1, h.2.1, h.2.2⟩
private theorem sameRunLrPc_setPState {s s1 : State} (h : SameRunLrPc s s1) (ps : PState) :
    SameRunLrPc s (s1.setPState ps) := ⟨h.1, h.2.1, h.2.2⟩
private theorem sameRunLrPc_optPState {s s1 : State} (h : SameRunLrPc s s1)
    (optPs : Option PState) :
    SameRunLrPc s (match optPs with | some ps => s1.setPState ps | none => s1) := by
  cases optPs with | none => exact h | some ps => exact sameRunLrPc_setPState h ps
private theorem sameRunLrPc_setMem {s s1 : State} (h : SameRunLrPc s s1) (m : Memory) :
    SameRunLrPc s (s1.setMem m) := ⟨h.1, h.2.1, h.2.2⟩
private theorem sameRunLrPc_addrWb {s s1 : State} (s0 : State) (h : SameRunLrPc s s1)
    {addr : AddrMode} (hbr : addr.baseReg ≠ .lr) :
    SameRunLrPc s (match (evalAddrMode s0 addr).2 with
      | some (base, newBase) => s1.writeReg64 base newBase | none => s1) := by
  cases addr <;> dsimp only [evalAddrMode, AddrMode.baseReg] at hbr ⊢
  · exact h
  · exact h
  · exact sameRunLrPc_writeReg64 h hbr _
  · exact sameRunLrPc_writeReg64 h hbr _
  · exact h

private theorem band_true {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> cases h
  exact ⟨rfl, rfl⟩

private theorem inByteInterval_iff {lo hi o : Nat} :
    inByteInterval lo hi o = true ↔ lo ≤ o ∧ o < hi := by
  simp [inByteInterval, Bool.and_eq_true, decide_eq_true_eq]

private theorem outcome_of_advancePC {base : BitVec 64} {lo hi off : Nat} {s s1 : State}
    (hrun : s.status = .Running)
    (hpc : s.pc = base + BitVec.ofNat 64 off)
    (hoff : inByteInterval lo hi (off + 4) = true)
    (h1 : SameRunLrPc s s1) :
    TrapStepOutcome base lo hi s s1.advancePC := by
  obtain ⟨hlo, hhi⟩ := inByteInterval_iff.mp hoff
  refine Or.inr ⟨h1.1.trans hrun, h1.2.1, Or.inr ⟨off + 4, hlo, hhi, ?_⟩⟩
  change s1.pc + 4#64 = base + BitVec.ofNat 64 (off + 4)
  rw [h1.2.2, hpc, BitVec.add_assoc, ← BitVec.ofNat_add]

private theorem outcome_of_branchRel {base : BitVec 64} {lo hi off : Nat} {relOff : BitVec 64}
    {s : State}
    (hrun : s.status = .Running)
    (hpc : s.pc = base + BitVec.ofNat 64 off)
    (htgt : inByteInterval lo hi (BitVec.ofNat 64 off + relOff).toNat = true) :
    TrapStepOutcome base lo hi s (s.setPC (s.pc + relOff)) := by
  obtain ⟨hlo, hhi⟩ := inByteInterval_iff.mp htgt
  refine Or.inr ⟨hrun, rfl, Or.inr ⟨(BitVec.ofNat 64 off + relOff).toNat, hlo, hhi, ?_⟩⟩
  change s.pc + relOff = base + BitVec.ofNat 64 (BitVec.ofNat 64 off + relOff).toNat
  rw [hpc, BitVec.add_assoc, BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem outcome_ite {base : BitVec 64} {lo hi : Nat} {s : State}
    {c : Prop} [inst : Decidable c] {t e : State}
    (ht : TrapStepOutcome base lo hi s t) (he : TrapStepOutcome base lo hi s e) :
    TrapStepOutcome base lo hi s (if c then t else e) :=
  match inst with
  | isTrue _ => ht
  | isFalse _ => he

private theorem outcome_applySimdResult {base : BitVec 64} {lo hi off : Nat} {s : State}
    (hrun : s.status = .Running) (hpc : s.pc = base + BitVec.ofNat 64 off)
    (hoff : inByteInterval lo hi (off + 4) = true)
    (rd : BitVec 5) (r : Except String (BitVec 128)) :
    TrapStepOutcome base lo hi s (applySimdResult s rd r) := by
  cases r with
  | ok res =>
    exact outcome_of_advancePC hrun hpc hoff (sameRunLrPc_writeVReg128 (sameRunLrPc_refl s) rd res)
  | error msg =>
    exact Or.inl ⟨msg, rfl⟩

private theorem outcome_applySimdSatResult {base : BitVec 64} {lo hi off : Nat} {s : State}
    (hrun : s.status = .Running) (hpc : s.pc = base + BitVec.ofNat 64 off)
    (hoff : inByteInterval lo hi (off + 4) = true)
    (rd : BitVec 5) (r : Except String (BitVec 128)) (satFlags : Option (BitVec 32)) :
    TrapStepOutcome base lo hi s (applySimdSatResult s rd r satFlags) := by
  cases r with
  | ok res =>
    cases satFlags with
    | none =>
      exact outcome_of_advancePC hrun hpc hoff
        (sameRunLrPc_writeVReg128 (sameRunLrPc_refl s) rd res)
    | some flags =>
      exact outcome_of_advancePC hrun hpc hoff
        (sameRunLrPc_orFpsr (sameRunLrPc_writeVReg128 (sameRunLrPc_refl s) rd res) flags)
  | error msg =>
    exact Or.inl ⟨msg, rfl⟩

private theorem exec_fmovGprVec_safe {base : BitVec 64} {regionLo regionHi off : Nat}
    {sf : Bool} {ftype rmode : BitVec 2} {opcode : BitVec 3} {rn rd : VReg} {s : State}
    (hsafe : isTrapSafeInstr regionLo regionHi off (.fmovGprVec sf ftype rmode opcode rn rd) = true)
    (hrun : s.status = .Running)
    (hpc : s.pc = base + BitVec.ofNat 64 off) :
    TrapStepOutcome base regionLo regionHi s
      (execInst (.fmovGprVec sf ftype rmode opcode rn rd) s) := by
  unfold isTrapSafeInstr at hsafe
  obtain ⟨hoff, hor⟩ := band_true hsafe
  clear hsafe
  have hrd_of_not : ¬ (opcode = 0b111#3 ∨ opcode = 0b010#3 ∨ opcode = 0b011#3) →
      Reg.fromZRBits rd ≠ .lr := fun hn => by
    rcases Bool.or_eq_true_iff.mp hor with hc | hrd0
    · exact absurd (of_decide_eq_true hc) hn
    · exact of_decide_eq_true hrd0
  clear hor
  dsimp only [execInst, execInstWithSvc]
  cases h1 : (opcode == 0b110#3)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases h2 : (opcode == 0b111#3)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases h3 : (opcode == 0b000#3 || opcode == 0b001#3)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases h4 : (rmode == 0b00#2 && (opcode == 0b100#3 || opcode == 0b101#3))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases h5 : (rmode == 0b00#2 && (opcode == 0b010#3 || opcode == 0b011#3))
          · simp only [Bool.false_eq_true, ↓reduceIte]; exact Or.inl ⟨_, rfl⟩
          · simp only [↓reduceIte]
            refine outcome_ite ?_ (outcome_ite ?_ (outcome_ite ?_ (outcome_ite ?_ (Or.inl ⟨_, rfl⟩))))
            · exact outcome_of_advancePC hrun hpc hoff
                (sameRunLrPc_orFpsr (sameRunLrPc_writeVReg32 (sameRunLrPc_refl s) rd _) _)
            · exact outcome_of_advancePC hrun hpc hoff
                (sameRunLrPc_orFpsr (sameRunLrPc_writeVReg32 (sameRunLrPc_refl s) rd _) _)
            · exact outcome_of_advancePC hrun hpc hoff
                (sameRunLrPc_orFpsr (sameRunLrPc_writeVReg64 (sameRunLrPc_refl s) rd _) _)
            · exact outcome_of_advancePC hrun hpc hoff
                (sameRunLrPc_orFpsr (sameRunLrPc_writeVReg64 (sameRunLrPc_refl s) rd _) _)
        · simp only [↓reduceIte]
          have hrd := hrd_of_not (by
            rcases Bool.or_eq_true_iff.mp (band_true h4).2 with ha | hb <;>
              (have := beq_iff_eq.mp ‹_›; subst this; decide))
          refine outcome_ite ?_ (outcome_ite ?_ (outcome_ite ?_ (outcome_ite ?_ (Or.inl ⟨_, rfl⟩))))
          · exact outcome_of_advancePC hrun hpc hoff
              (sameRunLrPc_orFpsr (sameRunLrPc_writeReg32 (sameRunLrPc_refl s) hrd _) _)
          · exact outcome_of_advancePC hrun hpc hoff
              (sameRunLrPc_orFpsr (sameRunLrPc_writeReg64 (sameRunLrPc_refl s) hrd _) _)
          · exact outcome_of_advancePC hrun hpc hoff
              (sameRunLrPc_orFpsr (sameRunLrPc_writeReg32 (sameRunLrPc_refl s) hrd _) _)
          · exact outcome_of_advancePC hrun hpc hoff
              (sameRunLrPc_orFpsr (sameRunLrPc_writeReg64 (sameRunLrPc_refl s) hrd _) _)
      · simp only [↓reduceIte]
        have hrd := hrd_of_not (by
          rcases Bool.or_eq_true_iff.mp h3 with ha | hb <;>
            (have := beq_iff_eq.mp ‹_›; subst this; decide))
        refine outcome_ite ?_ (outcome_ite ?_ (outcome_ite ?_ (outcome_ite ?_ (Or.inl ⟨_, rfl⟩))))
        · exact outcome_of_advancePC hrun hpc hoff
            (sameRunLrPc_orFpsr (sameRunLrPc_writeReg32 (sameRunLrPc_refl s) hrd _) _)
        · exact outcome_of_advancePC hrun hpc hoff
            (sameRunLrPc_orFpsr (sameRunLrPc_writeReg64 (sameRunLrPc_refl s) hrd _) _)
        · exact outcome_of_advancePC hrun hpc hoff
            (sameRunLrPc_orFpsr (sameRunLrPc_writeReg32 (sameRunLrPc_refl s) hrd _) _)
        · exact outcome_of_advancePC hrun hpc hoff
            (sameRunLrPc_orFpsr (sameRunLrPc_writeReg64 (sameRunLrPc_refl s) hrd _) _)
    · simp only [↓reduceIte]
      refine outcome_ite ?_ (outcome_ite ?_ (outcome_ite ?_ (Or.inl ⟨_, rfl⟩)))
      · exact outcome_of_advancePC hrun hpc hoff (sameRunLrPc_writeVReg32 (sameRunLrPc_refl s) rd _)
      · exact outcome_of_advancePC hrun hpc hoff (sameRunLrPc_writeVReg64 (sameRunLrPc_refl s) rd _)
      · exact outcome_of_advancePC hrun hpc hoff (sameRunLrPc_writeVReg128 (sameRunLrPc_refl s) rd _)
  · simp only [↓reduceIte]
    have hrd := hrd_of_not (by have := beq_iff_eq.mp h1; subst this; decide)
    refine outcome_ite ?_ (outcome_ite ?_ (outcome_ite ?_ (Or.inl ⟨_, rfl⟩)))
    · exact outcome_of_advancePC hrun hpc hoff (sameRunLrPc_writeReg32 (sameRunLrPc_refl s) hrd _)
    · exact outcome_of_advancePC hrun hpc hoff (sameRunLrPc_writeReg64 (sameRunLrPc_refl s) hrd _)
    · exact outcome_of_advancePC hrun hpc hoff (sameRunLrPc_writeReg64 (sameRunLrPc_refl s) hrd _)

/-- Any `isTrapSafeInstr regionLo regionHi off inst = true` instruction executed from
    `s.status = .Running` and `s.pc = base + BitVec.ofNat 64 off` satisfies
    `TrapStepOutcome base regionLo regionHi s (execInst inst s)`, for **arbitrary** register and
    memory contents. -/
theorem execInst_of_isTrapSafeInstr {base : BitVec 64} {regionLo regionHi off : Nat}
    {inst : Instr} {s : State}
    (hsafe : isTrapSafeInstr regionLo regionHi off inst = true)
    (hrun : s.status = .Running)
    (hpc : s.pc = base + BitVec.ofNat 64 off) :
    TrapStepOutcome base regionLo regionHi s (execInst inst s) := by
  cases inst <;> try (unfold isTrapSafeInstr at hsafe; contradiction)
  case ret rn =>
    unfold isTrapSafeInstr at hsafe; have hrn : rn = .lr := of_decide_eq_true hsafe; subst hrn
    exact Or.inr ⟨hrun, rfl, Or.inl rfl⟩
  case nop =>
    unfold isTrapSafeInstr at hsafe; exact outcome_of_advancePC hrun hpc hsafe (sameRunLrPc_refl s)
  case b relOff =>
    unfold isTrapSafeInstr at hsafe; exact outcome_of_branchRel hrun hpc hsafe
  case bCond cond relOff =>
    unfold isTrapSafeInstr at hsafe; obtain ⟨hoff, htgt⟩ := band_true hsafe
    change TrapStepOutcome base regionLo regionHi s
      (if ConditionHolds cond s.pstate then s.setPC (s.pc + relOff) else s.advancePC)
    exact outcome_ite (outcome_of_branchRel hrun hpc htgt)
      (outcome_of_advancePC hrun hpc hoff (sameRunLrPc_refl s))
  case cbz w isNonZero rt relOff =>
    unfold isTrapSafeInstr at hsafe; obtain ⟨hoff, htgt⟩ := band_true hsafe
    let val := s.readReg w rt
    change TrapStepOutcome base regionLo regionHi s
      (if (if isNonZero then (val == 0#64) != true else val == 0#64)
        then s.setPC (s.pc + relOff) else s.advancePC)
    exact outcome_ite (outcome_of_branchRel hrun hpc htgt)
      (outcome_of_advancePC hrun hpc hoff (sameRunLrPc_refl s))
  case tbz w isNonZero rt bit relOff =>
    unfold isTrapSafeInstr at hsafe; obtain ⟨hoff, htgt⟩ := band_true hsafe
    change TrapStepOutcome base regionLo regionHi s
      (if (s.readReg64 rt).getLsbD bit == isNonZero then s.setPC (s.pc + relOff) else s.advancePC)
    exact outcome_ite (outcome_of_branchRel hrun hpc htgt)
      (outcome_of_advancePC hrun hpc hoff (sameRunLrPc_refl s))
  case adr page rd relOff =>
    unfold isTrapSafeInstr at hsafe; obtain ⟨hoff, hrd0⟩ := band_true hsafe
    exact outcome_of_advancePC hrun hpc hoff
      (sameRunLrPc_writeReg64 (sameRunLrPc_refl s) (of_decide_eq_true hrd0) _)
  case addSubImm w _ rd _ _ _ | logicalImm w _ rd _ _ | logicalShift w _ rd _ _ _ _
      | addSubShift w _ rd _ _ _ _ | addSubExt w _ rd _ _ _ _ | addSubCarry w _ rd _ _ =>
    unfold isTrapSafeInstr at hsafe; obtain ⟨hoff, hrd0⟩ := band_true hsafe
    exact outcome_of_advancePC hrun hpc hoff
      (sameRunLrPc_optPState (sameRunLrPc_writeReg (sameRunLrPc_refl s) w (of_decide_eq_true hrd0) _) _)
  case moveWide w _ rd _ _ | bitfield w _ rd _ _ _ | extr w rd _ _ _
      | condSelect w _ rd _ _ _ | dataProc1 w _ rd _ | dataProc2 w _ rd _ _
      | dataProc3 w _ rd _ _ _ =>
    unfold isTrapSafeInstr at hsafe; obtain ⟨hoff, hrd0⟩ := band_true hsafe
    exact outcome_of_advancePC hrun hpc hoff
      (sameRunLrPc_writeReg (sameRunLrPc_refl s) w (of_decide_eq_true hrd0) _)
  case condCompareReg w isSub rn rm nzcv cond =>
    unfold isTrapSafeInstr at hsafe
    change TrapStepOutcome base regionLo regionHi s
      (execCondCompare w isSub false rn 0#64 rm nzcv cond s)
    unfold execCondCompare
    exact outcome_ite
      (outcome_of_advancePC hrun hpc hsafe (sameRunLrPc_optPState (sameRunLrPc_refl s) _))
      (outcome_of_advancePC hrun hpc hsafe (sameRunLrPc_setPState (sameRunLrPc_refl s) _))
  case condCompareImm w isSub rn imm5 nzcv cond =>
    unfold isTrapSafeInstr at hsafe
    change TrapStepOutcome base regionLo regionHi s
      (execCondCompare w isSub true rn (imm5.zeroExtend 64) .xzr nzcv cond s)
    unfold execCondCompare
    exact outcome_ite
      (outcome_of_advancePC hrun hpc hsafe (sameRunLrPc_optPState (sameRunLrPc_refl s) _))
      (outcome_of_advancePC hrun hpc hsafe (sameRunLrPc_setPState (sameRunLrPc_refl s) _))
  case ldr w sz signed rt addr =>
    unfold isTrapSafeInstr at hsafe
    obtain ⟨h12, hbr0⟩ := band_true hsafe; obtain ⟨hoff, hrt0⟩ := band_true h12
    change TrapStepOutcome base regionLo regionHi s (execLdr w sz signed rt addr s); unfold execLdr
    exact outcome_ite (Or.inl ⟨_, rfl⟩) (outcome_ite (Or.inl ⟨_, rfl⟩)
      (outcome_of_advancePC hrun hpc hoff
        (sameRunLrPc_writeReg (sameRunLrPc_addrWb s (sameRunLrPc_refl s) (of_decide_eq_true hbr0))
          w (of_decide_eq_true hrt0) _)))
  case ldrLit w signed rt relOff =>
    unfold isTrapSafeInstr at hsafe; obtain ⟨hoff, hrt0⟩ := band_true hsafe
    change TrapStepOutcome base regionLo regionHi s
      (execLdrLit w (if signed then .W32 else (w : MemWidth)) signed rt relOff s); unfold execLdrLit
    exact outcome_ite (Or.inl ⟨_, rfl⟩)
      (outcome_of_advancePC hrun hpc hoff
        (sameRunLrPc_writeReg (sameRunLrPc_refl s) w (of_decide_eq_true hrt0) _))
  case str sz rt addr =>
    unfold isTrapSafeInstr at hsafe; obtain ⟨hoff, hbr0⟩ := band_true hsafe
    change TrapStepOutcome base regionLo regionHi s (execStr sz rt addr s); unfold execStr
    exact outcome_ite (Or.inl ⟨_, rfl⟩) (outcome_ite (Or.inl ⟨_, rfl⟩)
      (outcome_of_advancePC hrun hpc hoff
        (sameRunLrPc_addrWb s (sameRunLrPc_setMem (sameRunLrPc_refl s) _) (of_decide_eq_true hbr0))))
  case ldp w signed rt1 rt2 addr =>
    unfold isTrapSafeInstr at hsafe
    obtain ⟨h123, hbr0⟩ := band_true hsafe; obtain ⟨h12, hrt20⟩ := band_true h123
    obtain ⟨hoff, hrt10⟩ := band_true h12
    change TrapStepOutcome base regionLo regionHi s (execLdp w signed rt1 rt2 addr s); unfold execLdp
    exact outcome_ite (Or.inl ⟨_, rfl⟩) (outcome_ite (Or.inl ⟨_, rfl⟩)
      (outcome_of_advancePC hrun hpc hoff
        (sameRunLrPc_writeReg
          (sameRunLrPc_writeReg (sameRunLrPc_addrWb s (sameRunLrPc_refl s) (of_decide_eq_true hbr0))
            _ (of_decide_eq_true hrt10) _) _ (of_decide_eq_true hrt20) _)))
  case stp w rt1 rt2 addr =>
    unfold isTrapSafeInstr at hsafe; obtain ⟨hoff, hbr0⟩ := band_true hsafe
    change TrapStepOutcome base regionLo regionHi s (execStp w rt1 rt2 addr s); unfold execStp
    exact outcome_ite (Or.inl ⟨_, rfl⟩) (outcome_ite (Or.inl ⟨_, rfl⟩)
      (outcome_of_advancePC hrun hpc hoff
        (sameRunLrPc_addrWb s (sameRunLrPc_setMem (sameRunLrPc_refl s) _) (of_decide_eq_true hbr0))))
  case barrier _ _ =>
    unfold isTrapSafeInstr at hsafe; exact outcome_of_advancePC hrun hpc hsafe (sameRunLrPc_refl s)
  case sysReg isRead sysreg rt =>
    unfold isTrapSafeInstr at hsafe
    obtain ⟨h12, hrt0⟩ := band_true hsafe; obtain ⟨h1, hsr0⟩ := band_true h12
    obtain ⟨hoff, hisRead⟩ := band_true h1
    have hsr : sysreg = 0x5807#15 := of_decide_eq_true hsr0; subst hisRead hsr
    have hexec : execInst (.sysReg true 0x5807#15 rt) s = (s.writeReg64 rt 4#64).advancePC := rfl
    rw [hexec]
    exact outcome_of_advancePC hrun hpc hoff
      (sameRunLrPc_writeReg64 (sameRunLrPc_refl s) (of_decide_eq_true hrt0) 4#64)
  case dcZva rt =>
    unfold isTrapSafeInstr at hsafe
    have hexec : execInst (.dcZva rt) s =
        (let ea := s.readReg64 rt &&& ~~~63#64
         if !s.mem.canWrite ea 64 then s.setStatus (.Exception "permission fault")
         else (s.setMem (simdStoreRegs .Q128 (fun _ => 0#128) 4 0#5 ea s.mem)).advancePC) := rfl
    rw [hexec]
    exact outcome_ite (Or.inl ⟨_, rfl⟩)
      (outcome_of_advancePC hrun hpc hsafe (sameRunLrPc_setMem (sameRunLrPc_refl s) _))
  case ldrSimd sz vt addr =>
    unfold isTrapSafeInstr at hsafe; obtain ⟨hoff, hbr0⟩ := band_true hsafe
    dsimp only [execInst, execInstWithSvc]
    exact outcome_ite (Or.inl ⟨_, rfl⟩) (outcome_ite (Or.inl ⟨_, rfl⟩)
      (outcome_of_advancePC hrun hpc hoff
        (sameRunLrPc_writeVReg128
          (sameRunLrPc_addrWb s (sameRunLrPc_refl s) (of_decide_eq_true hbr0)) vt _)))
  case strSimd _ _ addr | stpSimd _ _ _ addr =>
    unfold isTrapSafeInstr at hsafe; obtain ⟨hoff, hbr0⟩ := band_true hsafe
    dsimp only [execInst, execInstWithSvc]
    exact outcome_ite (Or.inl ⟨_, rfl⟩) (outcome_ite (Or.inl ⟨_, rfl⟩)
      (outcome_of_advancePC hrun hpc hoff
        (sameRunLrPc_addrWb s (sameRunLrPc_setMem (sameRunLrPc_refl s) _) (of_decide_eq_true hbr0))))
  case ldpSimd _ vt1 vt2 addr =>
    unfold isTrapSafeInstr at hsafe; obtain ⟨hoff, hbr0⟩ := band_true hsafe
    dsimp only [execInst, execInstWithSvc]
    exact outcome_ite (Or.inl ⟨_, rfl⟩) (outcome_ite (Or.inl ⟨_, rfl⟩)
      (outcome_of_advancePC hrun hpc hoff
        (sameRunLrPc_writeVReg128
          (sameRunLrPc_writeVReg128
            (sameRunLrPc_addrWb s (sameRunLrPc_refl s) (of_decide_eq_true hbr0)) vt1 _) vt2 _)))
  case fmovGprVec sf ftype rmode opcode rn rd =>
    exact exec_fmovGprVec_safe hsafe hrun hpc
  case simdImmShift _ _ _ _ _ _ rd | simdTwoRegMisc _ _ _ _ _ rd | simdAcrossLanes _ _ _ _ _ rd =>
    unfold isTrapSafeInstr at hsafe; dsimp only [execInst, execInstWithSvc]
    repeat (first
      | apply outcome_ite
      | exact Or.inl ⟨_, rfl⟩
      | exact outcome_applySimdResult hrun hpc hsafe rd _
      | exact outcome_applySimdSatResult hrun hpc hsafe rd _ _
      | exact outcome_of_advancePC hrun hpc hsafe (sameRunLrPc_writeVReg128 (sameRunLrPc_refl s) rd _))
  case simdInsDup _ _ _ _ _ rd =>
    unfold isTrapSafeInstr at hsafe; obtain ⟨hoff, hrd0⟩ := band_true hsafe
    have hrd := of_decide_eq_true hrd0; dsimp only [execInst, execInstWithSvc]
    repeat (first
      | apply outcome_ite
      | exact Or.inl ⟨_, rfl⟩
      | exact outcome_of_advancePC hrun hpc hoff (sameRunLrPc_writeVReg128 (sameRunLrPc_refl s) rd _)
      | exact outcome_of_advancePC hrun hpc hoff (sameRunLrPc_writeReg (sameRunLrPc_refl s) _ hrd _))
  case simdThreeSame _ u size _ _ _ rd =>
    unfold isTrapSafeInstr at hsafe
    have hsz : ∀ v : BitVec 2, v = 0#2 ∨ v = 1#2 ∨ v = 2#2 ∨ v = 3#2 := by decide
    rcases hsz size with rfl | rfl | rfl | rfl <;> cases u <;>
      dsimp only [execInst, execInstWithSvc] <;>
      repeat (first
        | apply outcome_ite
        | exact outcome_applySimdSatResult hrun hpc hsafe rd _ _
        | exact outcome_of_advancePC hrun hpc hsafe
            (sameRunLrPc_writeVReg128 (sameRunLrPc_refl s) rd _))

/-! ## 2. Multi-Block `RegionWordsSafe`, Dynamic `fetchMem_trapSafe`, and `TrapHook` -/

theorem keepOf_singleton (base : BitVec 64) (ws : List (BitVec 32)) (pc : BitVec 64) :
    keepOf [(base, ws)] pc = keepBlock base (4 * ws.length) pc := by
  simp [keepOf]

theorem keepBlock_add_ofNat (base : BitVec 64) {numBytes off : Nat} (hoff : off < numBytes) :
    keepBlock base numBytes (base + BitVec.ofNat 64 off) = true := by
  unfold keepBlock
  have hsub : base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off := by
    rw [BitVec.add_comm base, BitVec.add_sub_cancel]
  rw [hsub, BitVec.toNat_ofNat]
  exact decide_eq_true (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hoff)

theorem keepOf_mem_offset {region : TrapRegion} {base : BitVec 64} {ws : List (BitVec 32)}
    (hmem : (base, ws) ∈ region) {off : Nat} (hoff : off < 4 * ws.length) :
    keepOf region (base + BitVec.ofNat 64 off) = true :=
  List.any_eq_true.mpr ⟨(base, ws), hmem, keepBlock_add_ofNat base hoff⟩

/-- Multi-block instruction safety at byte offset `off` inside a block `(base, ws)` of size
    `numBytes = 4 * ws.length`: either intra-block `isTrapSafeInstr 0 numBytes off inst = true`,
    or a cross-block unconditional branch `.b relOff` landing inside `keepOf region`. -/
@[expose] def InstrSafeInRegion (region : TrapRegion) (base : BitVec 64)
    (numBytes off : Nat) (inst : Instr) : Prop :=
  isTrapSafeInstr 0 numBytes off inst = true ∨
  (∃ relOff : BitVec 64, inst = .b relOff ∧
    keepOf region (base + BitVec.ofNat 64 off + relOff) = true)

theorem InstrSafeInRegion.not_isSvc0 {region : TrapRegion} {base : BitVec 64}
    {numBytes off : Nat} {inst : Instr}
    (h : InstrSafeInRegion region base numBytes off inst) :
    inst.isSvc0 = false := by
  rcases h with hsafe | ⟨relOff, rfl, _⟩
  · exact isTrapSafeInstr_not_isSvc0 hsafe
  · rfl

/-- Multi-block step outcome: either faults with `.Exception msg`, or remains `.Running` with
    unchanged `lr` and `pc` equal to `s.readReg64 .lr` or inside `keepOf region`. -/
@[expose] def RegionStepOutcome (region : TrapRegion) (s s' : State) : Prop :=
  (∃ msg, s'.status = .Exception msg) ∨
  (s'.status = .Running ∧
   s'.readReg64 .lr = s.readReg64 .lr ∧
   (s'.pc = s.readReg64 .lr ∨ keepOf region s'.pc = true))

theorem execInst_of_instrSafeInRegion {region : TrapRegion} {base : BitVec 64}
    {ws : List (BitVec 32)} {off : Nat} {inst : Instr} {s : State}
    (hmem : (base, ws) ∈ region)
    (hsafe : InstrSafeInRegion region base (4 * ws.length) off inst)
    (hrun : s.status = .Running)
    (hpc : s.pc = base + BitVec.ofNat 64 off) :
    RegionStepOutcome region s (execInst inst s) := by
  rcases hsafe with hintra | ⟨relOff, rfl, hkeep_tgt⟩
  · rcases execInst_of_isTrapSafeInstr hintra hrun hpc with
      ⟨msg, hex⟩ | ⟨hrun', hlr', hpc_next⟩
    · exact Or.inl ⟨msg, hex⟩
    · refine Or.inr ⟨hrun', hlr', ?_⟩
      rcases hpc_next with hret | ⟨off', _, hoff', hpc'⟩
      · exact Or.inl hret
      · exact Or.inr (hpc' ▸ keepOf_mem_offset hmem hoff')
  · refine Or.inr ⟨hrun, rfl, Or.inr ?_⟩
    change keepOf region (s.pc + relOff) = true
    rwa [hpc]

/-- Static/placement word-level safety of `region`: every word `k < ws.length` of every block
    `(base, ws) ∈ region` decodes to an instruction satisfying `InstrSafeInRegion`. -/
@[expose] def RegionWordsSafe (region : TrapRegion) : Prop :=
  ∀ blk ∈ region, ∀ (k : Nat) (hk : k < blk.2.length),
    ∃ inst : Instr, decode (blk.2[k]'hk) = some inst ∧
      InstrSafeInRegion region blk.1 (4 * blk.2.length) (4 * k) inst

/-- Every block `(base, ws) ∈ region` is backed by `P_sub.hasWords base ws` for some
    `P_sub ∈ progs`. -/
@[expose] def RegionHasWords (progs : List Program) (region : TrapRegion) : Prop :=
  ∀ blk ∈ region, ∃ P_sub ∈ progs, P_sub.hasWords blk.1 blk.2

/-- Dynamic memory witness: every backing program `P_sub ∈ progs` has `P_sub.CodeLoaded m`. -/
@[expose] def RegionCodeLoaded (progs : List Program) (m : Memory) : Prop :=
  ∀ P_sub ∈ progs, P_sub.CodeLoaded m

theorem RegionCodeLoaded.step {P : Program} {progs : List Program} {s1 s2 : State}
    (h1 : Step P s1 s2) (hCode : RegionCodeLoaded progs s1.mem) :
    RegionCodeLoaded progs s2.mem :=
  fun P_sub hmem => h1.codeLoaded (hCode P_sub hmem)

theorem RegionCodeLoaded.steps {P : Program} {progs : List Program} {s1 s2 : State}
    (h : Steps P s1 s2) (hCode : RegionCodeLoaded progs s1.mem) :
    RegionCodeLoaded progs s2.mem :=
  fun P_sub hmem => h.codeLoaded (hCode P_sub hmem)

theorem codeLoaded_stripExecOutside_of_keep
    {keep : BitVec 64 → Bool} {prog : Program} {m : Memory}
    (hkeep : ∀ off : Nat, off < prog.code.length → keep (prog.base + BitVec.ofNat 64 off) = true)
    (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (ProofLib.stripExecOutside keep m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep (hkeep i hi), ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

theorem regionCodeLoaded_stripExecOutside
    {keep : BitVec 64 → Bool} {progs : List Program} {m : Memory}
    (hkeep : ∀ P_sub ∈ progs, ∀ off : Nat, off < P_sub.code.length →
      keep (P_sub.base + BitVec.ofNat 64 off) = true)
    (hCode : RegionCodeLoaded progs m) :
    RegionCodeLoaded progs (ProofLib.stripExecOutside keep m) :=
  fun P_sub hmem => codeLoaded_stripExecOutside_of_keep (hkeep P_sub hmem) (hCode P_sub hmem)

private theorem readWordOff_some_bounds {prog : Program} {o : Nat} {w : BitVec 32}
    (h : prog.readWordOff o = some w) :
    o % 4 = 0 ∧ o + 4 ≤ prog.code.length := by
  unfold Program.readWordOff at h
  split at h
  · contradiction
  rename_i hmod
  have hal : o % 4 = 0 := Classical.not_not.mp hmod
  split at h
  · rename_i b0 b1 b2 b3 rest hdrop
    have hdlen : (prog.code.drop o).length = (b0 :: b1 :: b2 :: b3 :: rest).length :=
      congrArg List.length hdrop
    rw [List.length_drop] at hdlen
    simp only [List.length_cons] at hdlen
    exact ⟨hal, by omega⟩
  · contradiction

private theorem externAt_none_of_fetch_some {prog : Program} {pc : BitVec 64} {inst : Instr}
    (hf : prog.fetch pc = some inst) :
    prog.externAt? pc = none := by
  unfold Program.fetch at hf
  cases hext : prog.externAt? pc with
  | none => rfl
  | some _ => simp [hext] at hf

private theorem add_ofNat_sub_toNat (a b : BitVec 64) :
    a + BitVec.ofNat 64 (b - a).toNat = b := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

/-- **Dynamic multi-block `fetchMem` bridge (`fetchMem_trapSafe`):**
    Any instruction dynamically fetched by `P_ghost.fetchMem m pc = some inst` at `pc` with
    `keepOf region pc = true` comes from some block `(base, ws) ∈ region` at a 4-aligned offset
    `off < 4 * ws.length` and satisfies `InstrSafeInRegion region base (4 * ws.length) off inst`. -/
theorem fetchMem_trapSafe
    {P_ghost : Program} {progs : List Program} {region : TrapRegion} {m : Memory}
    {pc : BitVec 64} {inst : Instr}
    (hSafe : RegionWordsSafe region)
    (hHas : RegionHasWords progs region)
    (hCode : RegionCodeLoaded progs m)
    (hkeep : keepOf region pc = true)
    (hfm : P_ghost.fetchMem m pc = some inst) :
    ∃ (base : BitVec 64) (ws : List (BitVec 32)) (off : Nat),
      (base, ws) ∈ region ∧
      off < 4 * ws.length ∧
      pc = base + BitVec.ofNat 64 off ∧
      InstrSafeInRegion region base (4 * ws.length) off inst := by
  obtain ⟨⟨base, ws⟩, hmem, hkb⟩ := List.any_eq_true.mp hkeep
  have hoff_lt : (pc - base).toNat < 4 * ws.length := of_decide_eq_true hkb
  let off := (pc - base).toNat
  have hpc_eq : pc = base + BitVec.ofNat 64 off := (add_ofNat_sub_toNat base pc).symm
  have hws_pos : 0 < ws.length := by omega
  obtain ⟨P_sub, hPmem, hHasSub⟩ := hHas (base, ws) hmem
  have hHasBase : P_sub.hasWords base ws := hHasSub
  have hLSub : P_sub.CodeLoaded m := hCode P_sub hPmem
  let bOff := (base - P_sub.base).toNat
  have hrw0 : P_sub.readWordOff (bOff + 4 * 0) = some (ws[0]'hws_pos) := hHasBase.2.1 0 hws_pos
  rw [Nat.mul_zero, Nat.add_zero] at hrw0
  obtain ⟨hbOff_al, _⟩ := readWordOff_some_bounds hrw0
  have hlast_lt : ws.length - 1 < ws.length := by omega
  have hrw_last : P_sub.readWordOff (bOff + 4 * (ws.length - 1)) =
      some (ws[ws.length - 1]'hlast_lt) := hHasBase.2.1 (ws.length - 1) hlast_lt
  obtain ⟨_, hbOff_end⟩ := readWordOff_some_bounds hrw_last
  have hbOff_len : bOff + 4 * ws.length ≤ P_sub.code.length := by omega
  have hP_al : P_sub.base.toNat % 4 = 0 := hLSub.aligned
  have hP_nw : P_sub.base.toNat + P_sub.code.length ≤ 2 ^ 64 := hLSub.no_wrap
  have hbase_eq : base = P_sub.base + BitVec.ofNat 64 bOff :=
    (add_ofNat_sub_toNat P_sub.base base).symm
  have hbase_nat : base.toNat = P_sub.base.toNat + bOff := by
    rw [hbase_eq, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hbase_al : base.toNat % 4 = 0 := by omega
  have hbase_nw : base.toNat + 4 * ws.length ≤ 2 ^ 64 := by omega
  have hfm0 := hfm
  unfold Program.fetchMem at hfm0
  cases heg : P_ghost.externAt? pc with
  | some _ => simp [heg] at hfm0
  | none =>
    simp only [heg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm0
    split at hfm0
    · contradiction
    rename_i hal_neg
    have hpc_al : pc.toNat % 4 = 0 := Classical.not_not.mp hal_neg
    have hpc_nat : pc.toNat = base.toNat + off := by
      rw [hpc_eq, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hoff_al : off % 4 = 0 := by omega
    let k := off / 4
    have hoff_k : off = 4 * k := by omega
    have hk : k < ws.length := by omega
    obtain ⟨inst', hdec, hSafe_k⟩ := hSafe (base, ws) hmem k hk
    have hfetch_sub : P_sub.fetch pc = some inst' := by
      rw [hpc_eq, hoff_k, Program.fetch_of_hasWords hHasBase k hk, hdec]
    have hext_sub : P_sub.externAt? pc = none := externAt_none_of_fetch_some hfetch_sub
    have hfm_sub : P_sub.fetchMem m pc = some inst' := P_sub.fetchMem_of_fetch hLSub hfetch_sub
    have hfm_eq : P_ghost.fetchMem m pc = P_sub.fetchMem m pc :=
      ProofLib.Variant.fetchMem_eq_of_externAt_eq (heg.trans hext_sub.symm)
    rw [hfm_eq, hfm_sub] at hfm
    cases hfm
    exact ⟨base, ws, off, hmem, hoff_lt, hpc_eq, hoff_k ▸ hSafe_k⟩

/-- Hook-level trap preservation at `lr = L`: on any `.Running` state `w` with `w.readReg64 .lr = L`,
    `f w` either transitions to `.Exception _` or stays `.Running` at `pc = L` with `lr = L`. -/
@[expose] def TrapHook (L : BitVec 64) (f : State → State) : Prop :=
  ∀ w : State, w.status = .Running → w.readReg64 .lr = L →
    (∃ msg, (f w).status = .Exception msg) ∨
    ((f w).status = .Running ∧ (f w).pc = L ∧ (f w).readReg64 .lr = L)

theorem trapHook_of_exception_on_keepLr {L : BitVec 64} {f : State → State}
    (hex : ∀ w : State, w.status = .Running → w.readReg64 .lr = L →
      ∃ msg, (f w).status = .Exception msg) : TrapHook L f :=
  fun w hrun hlr => Or.inl (hex w hrun hlr)

theorem trapHook_linkedCallHook {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    {spec : Spec α} {fallback : State → State} {L : BitVec 64}
    (hkeepL : keep L = true) (hfb : TrapHook L (keepFsTrace fallback)) :
    TrapHook L (linkedCallHook keep P_real P_sub entryTarget spec fallback) := by
  classical
  intro w hrun hlr; unfold linkedCallHook
  by_cases hAct : ActiveRealPre spec w
  · have hnoReal : ¬ ActiveRealRun keep P_real P_sub entryTarget w := fun hR => by
      have hfalse := hR.2.1; rw [hlr, hkeepL] at hfalse; exact Bool.noConfusion hfalse
    simp only [hAct, hnoReal, ↓reduceDIte]; exact hfb w hrun hlr
  · refine Or.inl ⟨"ghost-hook precondition violated", ?_⟩; simp [hAct]

theorem trapHook_linkedCallHook_of_not_pre {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    {spec : Spec α} {fallback : State → State} {L : BitVec 64}
    (hnoPre : ∀ w : State, w.readReg64 .lr = L → ¬ ActiveRealPre spec w) :
    TrapHook L (linkedCallHook keep P_real P_sub entryTarget spec fallback) := by
  classical
  intro w _ hlr; have hnp := hnoPre w hlr
  refine Or.inl ⟨"ghost-hook precondition violated", ?_⟩
  unfold linkedCallHook; simp [hnp]

/-! ## 3. Closed-Trap Invariant, `trap_impossible`, and `lr_trap_at_call` -/

/-- Closed-trap invariant on `region` with pinned `lr = L`. -/
@[expose] def TrapInv (progs : List Program) (region : TrapRegion) (L : BitVec 64)
    (w : State) : Prop :=
  w.status = .Running ∧ keepOf region w.pc = true ∧ w.readReg64 .lr = L ∧
    RegionCodeLoaded progs w.mem

/-- **Closed-trap impossibility (`trap_impossible`):** no `Steps P_ghost w sf` from `TrapInv`
    can reach `sf` outside `region` without `.Exception _` or `.Halted`. -/
theorem trap_impossible
    {P_ghost : Program} {progs : List Program} {region : TrapRegion} {L : BitVec 64}
    (hSafe : RegionWordsSafe region) (hHas : RegionHasWords progs region)
    (hL_in : keepOf region L = true)
    (hreg_ext : ∀ pc, keepOf region pc = true →
      P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook L f)
    {w sf : State} (hsteps : Steps P_ghost w sf)
    (hout_sf : sf.status = .Running → keepOf region sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg) (hnhalt_sf : sf.status ≠ .Halted)
    (hInv : TrapInv progs region L w) : False := by
  induction hsteps with
  | refl s =>
    have hfalse := hout_sf hInv.1; rw [hInv.2.1] at hfalse; exact Bool.noConfusion hfalse
  | @step s1 s2 s3 h1 hrest ih =>
    rcases hInv with ⟨hrun1, hkeep1, hlr1, hCode1⟩
    have hCode2 : RegionCodeLoaded progs s2.mem := hCode1.step h1
    cases h1 with
    | halt_unmapped _ _ _ =>
      exact hnhalt_sf (by rw [ProofLib.Variant.Steps.eq_of_not_running hrest nofun])
    | extern_fault _ _ _ =>
      exact hnoex_sf _ (by rw [ProofLib.Variant.Steps.eq_of_not_running hrest nofun])
    | @extern f _ hext _ _ =>
      rcases hreg_ext s1.pc hkeep1 with hnone | ⟨f', hext', htrap⟩
      · rw [hnone] at hext; contradiction
      · rw [hext'] at hext; injection hext with hfeq; subst hfeq
        rcases htrap s1 hrun1 hlr1 with ⟨msg, hex⟩ | ⟨hrun2, hpc2, hlr2⟩
        · have heq := ProofLib.Variant.Steps.eq_of_not_running hrest (by rw [hex]; nofun)
          exact hnoex_sf msg (by rw [heq, hex])
        · exact ih hout_sf hnoex_sf hnhalt_sf ⟨hrun2, hpc2 ▸ hL_in, hlr2, hCode2⟩
    | @exec inst _ hfm =>
      obtain ⟨base, ws, off, hmem, _, hpc1, hsafe⟩ :=
        fetchMem_trapSafe hSafe hHas hCode1 hkeep1 hfm
      have heval : P_ghost.evalInst inst s1 = execInst inst s1 :=
        evalInst_eq_execInst_of_not_isSvc0 hsafe.not_isSvc0 s1
      rcases execInst_of_instrSafeInRegion hmem hsafe hrun1 hpc1 with
        ⟨msg, hex⟩ | ⟨hrun2, hlr_eq, hpc_next⟩
      · have hex' : (P_ghost.evalInst inst s1).status = .Exception msg := heval ▸ hex
        have heq := ProofLib.Variant.Steps.eq_of_not_running hrest (by rw [hex']; nofun)
        exact hnoex_sf msg (by rw [heq, hex'])
      · rw [heval] at ih hCode2
        have hkeep2 : keepOf region (execInst inst s1).pc = true := by
          rcases hpc_next with hpc_ret | hkp
          · rw [hpc_ret, hlr1]; exact hL_in
          · exact hkp
        exact ih hout_sf hnoex_sf hnhalt_sf ⟨hrun2, hkeep2, hlr_eq.trans hlr1, hCode2⟩

/-- **Call-point `lr = false` covering both non-`.Running` and subroutine `Returned` outcomes
    (`lr_trap_at_call_ret`):** generalizes `MemsetLrTrapRet.blk21_lr_trap_at_call_ret`. -/
theorem lr_trap_at_call_ret
    {P_ghost : Program} {progs : List Program} {region : TrapRegion} {f_u : State → State}
    {u sf : State} (hSafe : RegionWordsSafe region) (hHas : RegionHasWords progs region)
    (htrap_u : keepOf region (u.readReg64 .lr) = true → TrapHook (u.readReg64 .lr) f_u)
    (hreg_ext : keepOf region (u.readReg64 .lr) = true → ∀ pc, keepOf region pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook (u.readReg64 .lr) f)
    (hext_u : P_ghost.externAt? u.pc = some f_u) (hCode_u : RegionCodeLoaded progs u.mem)
    (hsteps_u_sf : Steps P_ghost u sf) (hrun_u : u.status = .Running)
    (hu_ne_sf : sf.status = .Running → sf.pc ≠ u.pc)
    (hout_sf : sf.status = .Running → keepOf region sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg) (hnhalt_sf : sf.status ≠ .Halted) :
    keepOf region (u.readReg64 .lr) = false := by
  cases hkeepL : keepOf region (u.readReg64 .lr) with
  | false => rfl
  | true =>
    exfalso; cases hsteps_u_sf with
    | refl => exact hu_ne_sf hrun_u rfl
    | @step _ v _ h1 hrest =>
      have hCode_v : RegionCodeLoaded progs v.mem := hCode_u.step h1
      cases h1 with
      | exec _ hfm => unfold Program.fetchMem at hfm; rw [hext_u] at hfm; contradiction
      | halt_unmapped _ _ hext0 => rw [hext_u] at hext0; contradiction
      | extern_fault _ _ _ =>
        exact hnoex_sf _ (by rw [ProofLib.Variant.Steps.eq_of_not_running hrest nofun])
      | @extern f _ hext _ _ =>
        rw [hext_u] at hext; injection hext with hfeq; subst hfeq
        rcases htrap_u hkeepL u hrun_u rfl with ⟨msg, hex⟩ | ⟨hrun_v, hpc_v, hlr_v⟩
        · have heq := ProofLib.Variant.Steps.eq_of_not_running hrest (by rw [hex]; nofun)
          exact hnoex_sf msg (by rw [heq, hex])
        · exact trap_impossible hSafe hHas hkeepL (hreg_ext hkeepL) hrest
            hout_sf hnoex_sf hnhalt_sf ⟨hrun_v, hpc_v ▸ hkeepL, hlr_v, hCode_v⟩

/-- **Call-point `lr = false` for non-`.Running` terminal states (`lr_trap_at_call`):**
    exact multi-block counterpart of `MemsetLrTrap.blk21_lr_trap_at_call`. -/
theorem lr_trap_at_call
    {P_ghost : Program} {progs : List Program} {region : TrapRegion} {f_hook : State → State}
    {u sf : State} (hSafe : RegionWordsSafe region) (hHas : RegionHasWords progs region)
    (htrap_of_in : keepOf region (u.readReg64 .lr) = true → TrapHook (u.readReg64 .lr) f_hook)
    (hreg_ext : ∀ pc, keepOf region pc = true →
      P_ghost.externAt? pc = none ∨ P_ghost.externAt? pc = some f_hook)
    (hext_u : P_ghost.externAt? u.pc = some f_hook) (hCode_u : RegionCodeLoaded progs u.mem)
    (hsteps_u_sf : Steps P_ghost u sf) (hrun_u : u.status = .Running)
    (hrun_sf : sf.status ≠ .Running) (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepOf region (u.readReg64 .lr) = false :=
  lr_trap_at_call_ret hSafe hHas htrap_of_in
    (fun hL pc hkp => (hreg_ext pc hkp).imp id fun hs => ⟨f_hook, hs, htrap_of_in hL⟩)
    hext_u hCode_u hsteps_u_sf hrun_u
    (fun hr => False.elim (hrun_sf hr)) (fun hr => False.elim (hrun_sf hr))
    hnoex_sf hnhalt_sf

/-- Entry-state `lr` guard at `s0` for `keepLr_false_at_stub_of_outcome`. -/
@[expose] def TrapEntryGuard (region : TrapRegion) (stubPc : BitVec 64) (s0 : State) : Prop :=
  keepOf region (s0.readReg64 .lr) = false ∧ s0.readReg64 .lr ≠ stubPc

/-- **`P_real`-independent per-stub `keepOf region lr = false` from subroutine outcome facts.** -/
theorem keepLr_false_at_stub_of_outcome
    {P_ghost : Program} {progs : List Program} {region : TrapRegion}
    {stubPc : BitVec 64} {f_stub : State → State}
    (hSafe : RegionWordsSafe region) (hHas : RegionHasWords progs region)
    (hreg_ext : ∀ pc : BitVec 64, keepOf region pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepOf region L = true → TrapHook L f)
    (hext_stub : P_ghost.externAt? stubPc = some f_stub)
    (htrap_stub : ∀ L : BitVec 64, keepOf region L = true → TrapHook L f_stub)
    {s0 sf : State} (hc_codeLoaded : RegionCodeLoaded progs s0.mem)
    (hGuard0 : TrapEntryGuard region stubPc s0)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg) (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State, Steps P_ghost s0 u → Steps P_ghost u sf →
      u.status = .Running → u.pc = stubPc → keepOf region (u.readReg64 .lr) = false := by
  intro u hsteps_s0_u hsteps_u_sf hrun_u hpc_u
  exact lr_trap_at_call_ret hSafe hHas (fun hL => htrap_stub _ hL)
    (fun hL pc hkp => (hreg_ext pc hkp).imp id fun ⟨f, hf, htf⟩ => ⟨f, hf, htf _ hL⟩)
    (hpc_u ▸ hext_stub) (hc_codeLoaded.steps hsteps_s0_u) hsteps_u_sf hrun_u
    (fun hrun_sf heq_pc => hGuard0.2 ((hret_pc hrun_sf).symm.trans (heq_pc.trans hpc_u)))
    (fun hrun_sf => hret_pc hrun_sf ▸ hGuard0.1) hnoex_sf hnhalt_sf

/-- Fixed-`L` adapter bridging entry-excluded `externAt? pc = none` (`pc ∉ entries`) plus per-entry
    `TrapHook L` witnesses into `trap_impossible` / `lr_trap_at_call_ret`. -/
theorem reg_ext_of_entry_excluded {P_ghost : Program} {region : TrapRegion}
    {entries : List (BitVec 64)} {L : BitVec 64}
    (hno_ext_outside : ∀ pc, keepOf region pc = true → pc ∉ entries → P_ghost.externAt? pc = none)
    (hentries : ∀ e ∈ entries,
      P_ghost.externAt? e = none ∨ ∃ f, P_ghost.externAt? e = some f ∧ TrapHook L f) :
    ∀ pc, keepOf region pc = true →
      P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook L f := by
  intro pc hkp; by_cases hmem : pc ∈ entries
  · exact hentries pc hmem
  · exact Or.inl (hno_ext_outside pc hkp hmem)

/-- `∀ L` adapter bridging entry-excluded `externAt? pc = none` (`pc ∉ entries`) plus uniform
    per-entry `TrapHook` witnesses directly into `keepLr_false_at_stub_of_outcome`. -/
theorem reg_ext_forall_of_entry_excluded {P_ghost : Program} {region : TrapRegion}
    {entries : List (BitVec 64)}
    (hno_ext_outside : ∀ pc, keepOf region pc = true → pc ∉ entries → P_ghost.externAt? pc = none)
    (hentries : ∀ e ∈ entries, P_ghost.externAt? e = none ∨
      ∃ f, P_ghost.externAt? e = some f ∧ ∀ L, keepOf region L = true → TrapHook L f) :
    ∀ pc, keepOf region pc = true → P_ghost.externAt? pc = none ∨
      ∃ f, P_ghost.externAt? pc = some f ∧ ∀ L, keepOf region L = true → TrapHook L f := by
  intro pc hkp; by_cases hmem : pc ∈ entries
  · exact hentries pc hmem
  · exact Or.inl (hno_ext_outside pc hkp hmem)

/-! ## 4. Decidable Word-List Classifier (`checkWordsTrapSafe`) & Milestone 1 `all_safe` Proofs -/

/-- Decidable check that `w` is an unconditional `B` template (`w &&& 0xfc000000 = 0x14000000`). -/
@[expose] def isBWord32 (w : BitVec 32) : Bool := (w &&& 0xfc000000#32) == 0x14000000#32

/-- Decidable per-word check at index `k` of a block of byte-size `numBytes`. -/
@[expose] def checkWordTrapSafeAt (numBytes : Nat) (jumpOffs : List Nat) (k : Nat)
    (w : BitVec 32) : Bool :=
  if (4 * k) ∈ jumpOffs then isBWord32 w
  else match decode w with | some inst => isTrapSafeInstr 0 numBytes (4 * k) inst | none => false

/-- Decidable classifier over a raw word list `ws` with optional cross-block `B` byte offsets. -/
@[expose] def checkWordsTrapSafe (ws : List (BitVec 32)) (jumpOffs : List Nat := []) : Bool :=
  (List.range ws.length).all fun k =>
    match ws[k]? with | some w => checkWordTrapSafeAt (4 * ws.length) jumpOffs k w | none => false

/-- Soundness of `checkWordsTrapSafe ws [] = true` for any reloc-free block `(base, ws) ∈ region`. -/
theorem blockSafe_of_checkWords {region : TrapRegion} {base : BitVec 64} {ws : List (BitVec 32)}
    (hchk : checkWordsTrapSafe ws [] = true) (k : Nat) (hk : k < ws.length) :
    ∃ inst : Instr, decode (ws[k]'hk) = some inst ∧
      InstrSafeInRegion region base (4 * ws.length) (4 * k) inst := by
  have hword := List.all_eq_true.mp hchk k (List.mem_range.mpr hk)
  rw [List.getElem?_eq_getElem hk] at hword
  dsimp only [checkWordTrapSafeAt] at hword; simp only [List.not_mem_nil, ↓reduceIte] at hword
  cases hdec : decode (ws[k]'hk) with
  | none => rw [hdec] at hword; contradiction
  | some inst => rw [hdec] at hword; exact ⟨inst, rfl, Or.inl hword⟩

/-- Single-block `RegionWordsSafe [(base, ws)]` from `checkWordsTrapSafe ws [] = true`. -/
theorem regionWordsSafe_single (base : BitVec 64) {ws : List (BitVec 32)}
    (hchk : checkWordsTrapSafe ws [] = true) : RegionWordsSafe [(base, ws)] := by
  intro blk hmem k hk; rw [List.mem_singleton] at hmem; subst hmem
  exact blockSafe_of_checkWords hchk k hk

/-- Soundness of `checkWordsTrapSafe ws (calls.map Prod.fst) = true` for `Obj.patchCalls`. -/
theorem blockSafe_of_patchCalls {region : TrapRegion} {base : BitVec 64}
    {calls : List (Nat × String)} {ws : List (BitVec 32)} {resolve : String → BitVec 64}
    (hchk : checkWordsTrapSafe ws (calls.map Prod.fst) = true)
    (hcalls : ∀ c ∈ calls,
      Obj.BranchInRange (base + BitVec.ofNat 64 c.1) (resolve c.2) ∧
      keepOf region (resolve c.2) = true)
    (k : Nat) (hk : k < (Obj.patchCalls calls ws base resolve).length) :
    ∃ inst : Instr, decode ((Obj.patchCalls calls ws base resolve)[k]'hk) = some inst ∧
      InstrSafeInRegion region base (4 * (Obj.patchCalls calls ws base resolve).length)
        (4 * k) inst := by
  have hlen : (Obj.patchCalls calls ws base resolve).length = ws.length := by simp [Obj.patchCalls]
  have hk' : k < ws.length := hlen ▸ hk
  have hword := List.all_eq_true.mp hchk k (List.mem_range.mpr hk')
  rw [List.getElem?_eq_getElem hk'] at hword; dsimp only [checkWordTrapSafeAt] at hword
  simp only [Obj.patchCalls, List.getElem_mapIdx, List.length_mapIdx]
  cases hfind : calls.find? (fun x : Nat × String => x.1 == 4 * k) with
  | some p =>
    rcases p with ⟨off_c, sym⟩
    have hmem_p : (off_c, sym) ∈ calls := List.mem_of_find?_eq_some hfind
    have hoff_eq : off_c = 4 * k := beq_iff_eq.mp
      (List.find?_some (p := fun x : Nat × String => x.1 == 4 * k) hfind)
    have hmem_j : 4 * k ∈ calls.map Prod.fst := List.mem_map.mpr ⟨(off_c, sym), hmem_p, hoff_eq⟩
    simp only [hmem_j, ↓reduceIte] at hword
    have hw : (ws[k]'hk') &&& 0xfc000000#32 = 0x14000000#32 := beq_iff_eq.mp hword
    obtain ⟨hrange, hkeep_tgt⟩ := hcalls (off_c, sym) hmem_p; rw [hoff_eq] at hrange
    refine ⟨.b (resolve sym - (base + BitVec.ofNat 64 (4 * k))),
      Obj.decode_branchWord_b hw hrange, Or.inr ⟨_, rfl, ?_⟩⟩
    have hcancel : base + BitVec.ofNat 64 (4 * k) +
        (resolve sym - (base + BitVec.ofNat 64 (4 * k))) = resolve sym := by
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    rwa [hcancel]
  | none =>
    have hnot_mem : 4 * k ∉ calls.map Prod.fst := fun hm => by
      obtain ⟨c, hc_mem, hc_eq⟩ := List.mem_map.mp hm
      have hnone := List.find?_eq_none.mp hfind c hc_mem; simp [hc_eq] at hnone
    simp only [hnot_mem, ↓reduceIte] at hword
    cases hdec : decode (ws[k]'hk') with
    | none => rw [hdec] at hword; contradiction
    | some inst => rw [hdec] at hword; exact ⟨inst, rfl, Or.inl hword⟩

/-- Sanity check: `memsetWordsSym` (65 words, `mallocng` block 21) passes `checkWordsTrapSafe`. -/
theorem memsetWords_all_safe : checkWordsTrapSafe memsetWordsSym [] = true := by decide

/-- Sanity check: re-deriving `MemsetLrTrap.blk21_lr_trap_at_call` from `lr_trap_at_call`. -/
theorem memset_lr_trap_at_call
    {P_ghost : Program} {mmpl : Obj.MultiPlacement} {f_ms : State → State} {u sf : State}
    (htrap_of_in : keepMemsetBlk21 mmpl (u.readReg64 .lr) = true →
      TrapHook (u.readReg64 .lr) f_ms)
    (hblk21_ext : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨ P_ghost.externAt? pc = some f_ms)
    (hext_u : P_ghost.externAt? u.pc = some f_ms)
    (hCode_u : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded u.mem)
    (hsteps_u_sf : Steps P_ghost u sf) (hrun_u : u.status = .Running)
    (hrun_sf : sf.status ≠ .Running) (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepMemsetBlk21 mmpl (u.readReg64 .lr) = false := by
  have hkeep_eq : ∀ pc, keepOf [(mmpl.base 21, memsetWordsSym)] pc = keepMemsetBlk21 mmpl pc := by
    intro pc; simp only [keepOf, List.any_cons, List.any_nil, Bool.or_false, keepBlock,
      memsetWordsSym_length, keepMemsetBlk21]; rfl
  rw [← hkeep_eq]
  exact lr_trap_at_call (regionWordsSafe_single (mmpl.base 21) memsetWords_all_safe)
    (fun blk hmem => by
      rw [List.mem_singleton] at hmem; subst hmem
      exact ⟨mallocngBlockProg mmpl 21 Syscall.standard, List.mem_singleton.mpr rfl,
        mallocngBlockProg21_hasWords mmpl Syscall.standard⟩)
    (fun hL => htrap_of_in (hkeep_eq _ ▸ hL)) (fun pc hkp => hblk21_ext pc (hkeep_eq _ ▸ hkp))
    hext_u (fun P hP => by rw [List.mem_singleton] at hP; subst hP; exact hCode_u)
    hsteps_u_sf hrun_u hrun_sf hnoex_sf hnhalt_sf

/-- `memcmp` (`memcmpLibcaWords`, 13 words, reloc-free) passes `checkWordsTrapSafe`. -/
theorem memcmp_all_safe : checkWordsTrapSafe memcmpLibcaWords [] = true := by decide

/-- `bcmp` (`bcmpWords`, 1 word `b memcmp` at byte offset `0`) passes `checkWordsTrapSafe`. -/
theorem bcmp_all_safe : checkWordsTrapSafe bcmpWords [0] = true := by decide

/-- Contiguous stock-order `memcmp ++ bcmp` (`13 + 1 = 14` words, `memcmp.lo` at `0` followed
    by `bcmp.lo` at `52` as in `stock.ld:62-67`) passes `checkWordsTrapSafe`. -/
theorem bcmp_memcmp_all_safe :
    checkWordsTrapSafe
      (memcmpLibcaWords ++ Obj.patchCalls bcmpCalls bcmpWords 52#64 (fun _ => 0#64)) [] = true := by
  decide

/-- Multi-block `RegionWordsSafe` for the 2-block `bcmp` + `memcmp` union. -/
theorem bcmp_memcmp_regionWordsSafe {bcmpBase memcmpBase : BitVec 64}
    (hrange : Obj.BranchInRange bcmpBase memcmpBase) :
    RegionWordsSafe
      [(bcmpBase, Obj.patchCalls bcmpCalls bcmpWords bcmpBase (fun _ => memcmpBase)),
       (memcmpBase, memcmpLibcaWords)] := by
  intro blk hmem
  rcases List.mem_cons.mp hmem with rfl | hmem2
  · dsimp only; intro k hk
    refine blockSafe_of_patchCalls (base := bcmpBase) (calls := bcmpCalls) (ws := bcmpWords)
      (resolve := fun _ => memcmpBase) bcmp_all_safe (fun c hc => ?_) k hk
    rw [show bcmpCalls = [(0, "memcmp")] from rfl, List.mem_singleton] at hc; subst hc
    refine ⟨by dsimp only; rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero], ?_⟩
    have h0 : keepOf
        [(bcmpBase, Obj.patchCalls bcmpCalls bcmpWords bcmpBase (fun _ => memcmpBase)),
         (memcmpBase, memcmpLibcaWords)] (memcmpBase + 0#64) = true :=
      keepOf_mem_offset (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))
        (show 0 < 4 * memcmpLibcaWords.length by decide)
    rwa [BitVec.add_zero] at h0
  · rw [List.mem_singleton] at hmem2; subst hmem2; dsimp only; intro k hk
    exact blockSafe_of_checkWords memcmp_all_safe k hk

/-! ## 5. Milestone 2 `all_safe` Proofs, `Obj.CodeBlock` Classifier, & Non-Leaf Negative Checks -/

/-- `strlen` (`muslStrlenWords`, 22 words, reloc-free) passes `checkWordsTrapSafe`. -/
theorem strlen_all_safe : checkWordsTrapSafe muslStrlenWords [] = true := by decide
/-- `memcpy` (`memcpySymWords`, 99 words, reloc-free) passes `checkWordsTrapSafe`. -/
theorem memcpy_all_safe : checkWordsTrapSafe memcpySymWords [] = true := by decide
/-- `memmove` (`memmoveLibcaWords`, 74 words, `b memcpy` at byte offset `104`) passes `checkWordsTrapSafe`. -/
theorem memmove_all_safe : checkWordsTrapSafe memmoveLibcaWords [104] = true := by decide

/-- Multi-block `RegionWordsSafe` for the 2-block `memmove` + `memcpy` union. -/
theorem memmove_memcpy_regionWordsSafe {memmoveBase memcpyBase : BitVec 64}
    (hrange : Obj.BranchInRange (memmoveBase + 104#64) memcpyBase) :
    RegionWordsSafe
      [(memmoveBase, Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords memmoveBase (fun _ => memcpyBase)),
       (memcpyBase, memcpySymWords)] := by
  intro blk hmem
  rcases List.mem_cons.mp hmem with rfl | hmem2
  · dsimp only; intro k hk
    refine blockSafe_of_patchCalls (base := memmoveBase) (calls := memmoveLibcaCalls)
      (ws := memmoveLibcaWords) (resolve := fun _ => memcpyBase)
      memmove_all_safe (fun c hc => ?_) k hk
    rw [show memmoveLibcaCalls = [(104, "memcpy")] from rfl, List.mem_singleton] at hc; subst hc
    refine ⟨hrange, ?_⟩
    have h0 : keepOf
        [(memmoveBase, Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords memmoveBase (fun _ => memcpyBase)),
         (memcpyBase, memcpySymWords)] (memcpyBase + 0#64) = true :=
      keepOf_mem_offset (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))
        (show 0 < 4 * memcpySymWords.length by decide)
    rwa [BitVec.add_zero] at h0
  · rw [List.mem_singleton] at hmem2; subst hmem2; dsimp only; intro k hk
    exact blockSafe_of_checkWords memcpy_all_safe k hk

/-- Placed word list of an `Obj.CodeBlock` under placement `pl`. -/
@[expose] def codeBlockPatchedWords (blk : Obj.CodeBlock) (pl : Obj.Placement) : List (BitVec 32) :=
  (List.range (blk.code.length / 4)).map fun k => blk.patchedWord pl (4 * k)
/-- Placement-independent per-word classifier for an `Obj.CodeBlock` (covers unrelocated words
    plus unrelaxed and linker-relaxed `.adrpHi21` / `.addLo12` symbol-address pairs). -/
@[expose] def checkCodeBlockWordTrapSafe (blk : Obj.CodeBlock) (off : Nat) : Bool :=
  let numBytes := blk.code.length; let w := blk.wordAt off
  match blk.relocAt? off with
  | none => match decode w with | some inst => isTrapSafeInstr 0 numBytes off inst | none => false
  | some r => match r.kind with
    | .adrpHi21 => inByteInterval 0 numBytes (off + 4) &&
        Obj.isAdrpWord w && decide (Reg.fromZRBits (w.extractLsb' 0 5) ≠ .lr)
    | .addLo12 => inByteInterval 0 numBytes (off + 4) && Obj.isAddImm64Word w &&
        decide (Reg.fromZRBits (w.extractLsb' 0 5) ≠ .lr) &&
        decide (Reg.fromSPBits (w.extractLsb' 0 5) ≠ .lr)
    | _ => false
/-- Placement-independent `lr`-trap classifier over all 32-bit words of an `Obj.CodeBlock`. -/
@[expose] def checkCodeBlockTrapSafe (blk : Obj.CodeBlock) : Bool :=
  (blk.code.length % 4 == 0) &&
    (List.range (blk.code.length / 4)).all fun k => checkCodeBlockWordTrapSafe blk (4 * k)
/-- Diagnostic helper returning `(byteOffset, decode (blk.wordAt off), relocKind?)` for rejected sites. -/
@[expose] def codeBlockUnsafeSites (blk : Obj.CodeBlock) :
    List (Nat × Option Instr × Option Obj.RelocKind) :=
  ((List.range (blk.code.length / 4)).filter fun k => !checkCodeBlockWordTrapSafe blk (4 * k)).map
    fun k => (4 * k, decode (blk.wordAt (4 * k)), (blk.relocAt? (4 * k)).map (·.kind))
private theorem decode_adrWord_nc {w : BitVec 32} (hw : w &&& 0x9f000000#32 = 0x10000000#32)
    (place target : BitVec 64) : ∃ imm, decode (Obj.adrWord w place target) =
      some (.adr false (Reg.fromZRBits (w.extractLsb' 0 5)) imm) := by
  have ⟨hm, hrd⟩ := Obj.adrp_mask_preserve (Obj.adrWordOff_mask w (target - place))
  have hv9 : Obj.adrWord w place target &&& 0x9f000000#32 = 0x10000000#32 := hm.trans hw
  have hv1 : Obj.adrWord w place target &&& 0x1f000000#32 = 0x10000000#32 := by
    have : 0x1f000000#32 = 0x9f000000#32 &&& 0x1f000000#32 := rfl
    rw [this, ← BitVec.and_assoc, hv9]; rfl
  have hp : (Obj.adrWord w place target).getLsbD 31 = false := by
    have h0 : (Obj.adrWord w place target &&& 0x9f000000#32).getLsbD 31 = false := by rw [hv9]; rfl
    simpa [BitVec.getLsbD_and] using h0
  change (Obj.adrWord w place target).extractLsb' 0 5 = w.extractLsb' 0 5 at hrd
  have hdec := Obj.decode_adr_or_adrp hv1; dsimp only at hdec; rw [hp, hrd] at hdec
  exact ⟨_, hdec⟩

/-- Soundness of `checkCodeBlockTrapSafe` for every placement `pl` (unrelaxed or relaxed). -/
theorem regionWordsSafe_codeBlock {blk : Obj.CodeBlock} (pl : Obj.Placement)
    (hchk : checkCodeBlockTrapSafe blk = true) :
    RegionWordsSafe [(pl.base, codeBlockPatchedWords blk pl)] := by
  obtain ⟨hmod0, hall⟩ := band_true hchk
  have hmod : blk.code.length % 4 = 0 := beq_iff_eq.mp hmod0
  have hlen : 4 * (codeBlockPatchedWords blk pl).length = blk.code.length := by
    simp only [codeBlockPatchedWords, List.length_map, List.length_range]; omega
  intro b hmem k hk; rw [List.mem_singleton] at hmem; subst hmem
  have hk' : k < blk.code.length / 4 := by simpa [codeBlockPatchedWords] using hk
  have hw_eq : (codeBlockPatchedWords blk pl)[k]'hk = blk.patchedWord pl (4 * k) := by
    simp [codeBlockPatchedWords]
  rw [hw_eq, hlen]
  have hword := List.all_eq_true.mp hall k (List.mem_range.mpr hk')
  unfold checkCodeBlockWordTrapSafe at hword; unfold Obj.CodeBlock.patchedWord
  cases hrel : blk.relocAt? (4 * k) with
  | none =>
    rw [hrel] at hword; dsimp only at hword ⊢
    cases hdec : decode (blk.wordAt (4 * k)) with
    | none => rw [hdec] at hword; contradiction
    | some inst => rw [hdec] at hword; exact ⟨inst, rfl, Or.inl hword⟩
  | some r =>
    rw [hrel] at hword; dsimp only at hword ⊢
    cases hkind : r.kind with
    | adrpHi21 =>
      rw [hkind] at hword; dsimp only at hword
      obtain ⟨h12, hrd0⟩ := band_true hword; obtain ⟨hoff, hadrp0⟩ := band_true h12
      have hnprev : (decide (4 ≤ 4 * k) && blk.relaxedAt pl (4 * k - 4)) = false := by
        by_cases h4 : 4 ≤ 4 * k
        · have hr2 : blk.relocAt? (4 * k - 4 + 4) = some r := by
            rw [show 4 * k - 4 + 4 = 4 * k by omega]; exact hrel
          simp [Obj.CodeBlock.relaxedAt,
            Obj.CodeBlock.relaxableAt_false_of_next_kind hr2 (by rw [hkind]; decide)]
        · simp [h4]
      cases hrel0 : blk.relaxedAt pl (4 * k)
      · simp only [hnprev, Bool.false_eq_true, Obj.RelocKind.isGotOrTlsIe, Bool.false_and,
          ↓reduceIte, Obj.patchRelocWord]
        exact ⟨_, Obj.decode_adrpWord_nc (beq_iff_eq.mp hadrp0) _ _,
          Or.inl (Bool.and_eq_true_iff.mpr ⟨hoff, hrd0⟩)⟩
      · simp only [↓reduceIte]; exact ⟨.nop, rfl, Or.inl hoff⟩
    | addLo12 =>
      rw [hkind] at hword; dsimp only at hword
      obtain ⟨h123, hrd_sp⟩ := band_true hword; obtain ⟨h12, hrd_zr⟩ := band_true h123
      obtain ⟨hoff, hadd0⟩ := band_true h12
      have hnr0 : blk.relaxedAt pl (4 * k) = false := by
        simp [Obj.CodeBlock.relaxedAt,
          Obj.CodeBlock.relaxableAt_false_of_kind hrel (by rw [hkind]; decide)]
      rw [hnr0]; simp only [Bool.false_eq_true, ↓reduceIte]
      cases hprev : (decide (4 ≤ 4 * k) && blk.relaxedAt pl (4 * k - 4))
      · simp only [Bool.false_eq_true, Obj.RelocKind.isGotOrTlsIe, Bool.false_and,
          ↓reduceIte, Obj.patchRelocWord]
        exact ⟨_, Obj.decode_addLo12Word (beq_iff_eq.mp hadd0) _,
          Or.inl (Bool.and_eq_true_iff.mpr ⟨hoff, hrd_sp⟩)⟩
      · simp only [↓reduceIte]
        obtain ⟨imm, hdec⟩ := decode_adrWord_nc (Obj.adrTemplate_mask (blk.wordAt (4 * k)))
          (pl.base + BitVec.ofNat 64 (4 * k)) (blk.target pl r)
        rw [Obj.adrTemplate_rd] at hdec
        exact ⟨_, hdec, Or.inl (Bool.and_eq_true_iff.mpr ⟨hoff, hrd_zr⟩)⟩
    | _ => rw [hkind] at hword; simp at hword
set_option maxRecDepth 200000 in
/-- `core::str::converts::from_utf8` (`(coreMultiLib.blockLib 1).text`, 156 words) passes `checkCodeBlockTrapSafe`. -/
theorem fromUtf8_all_safe : checkCodeBlockTrapSafe (coreMultiLib.blockLib 1).text = true := by decide
/-- Placement-generic `RegionWordsSafe` for `core::str::converts::from_utf8` under any `pl`. -/
theorem fromUtf8_regionWordsSafe (pl : Obj.Placement) :
    RegionWordsSafe [(pl.base, codeBlockPatchedWords (coreMultiLib.blockLib 1).text pl)] :=
  regionWordsSafe_codeBlock pl fromUtf8_all_safe
set_option maxRecDepth 200000 in
/-- Negative check 1: `memrchr` (`(coreMultiLib.blockLib 2).text`, 74 words) is rejected (`false`). -/
theorem memrchr_not_all_safe : checkCodeBlockTrapSafe (coreMultiLib.blockLib 2).text = false := by decide
set_option maxRecDepth 200000 in
/-- Negative check 2a: `Timespec::sub_timespec` (`(timeMultiLib.blockLib 0).text`, 60 words) is rejected (`false`). -/
theorem subTimespec_not_all_safe : checkCodeBlockTrapSafe (timeMultiLib.blockLib 0).text = false := by decide
set_option maxRecDepth 200000 in
/-- Negative check 2b: `SystemTime::duration_since` (`(timeMultiLib.blockLib 1).text`, 20 words) is rejected (`false`). -/
theorem durationSince_not_all_safe : checkCodeBlockTrapSafe (timeMultiLib.blockLib 1).text = false := by decide
set_option maxRecDepth 200000 in
/-- Negative check 3: `SystemTime::add` (`(timeMultiLib.blockLib 2).text`, 24 words) is rejected (`false`). -/
theorem timeAdd_not_all_safe : checkCodeBlockTrapSafe (timeMultiLib.blockLib 2).text = false := by decide

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords
