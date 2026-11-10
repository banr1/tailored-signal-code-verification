/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplays -- proof-setup: allow-public-import
import ProofLib.OpcodeExclusion
import ProofLib.ProgramReflection.Variant.TrapTransfer

/-!
# Closed-Trap Discharge of `keepMemsetBlk21 mmpl (u.readReg64 .lr) = false` (`HooksDehook.MemsetLrTrap`)

Global closed-trap proof over `mallocngLib` block 21 (`memsetWordsSym`, `65` instructions = `260`
bytes) discharging the per-call hypothesis `keepMemsetBlk21 mmpl (u.readReg64 .lr) = false` of
`ghostExternReplays_f3MemsetGhostHookNarrow` (`MemsetGhostReplays.lean:522`) **once, globally, with
zero per-caller `LsRetAddr624` obligations**, for **arbitrary** register and memory contents.

## Proof Architecture
1. **Syntactic 65-instruction trap classifier (`isBlk21SafeInstr`, `memsetWords_all_safe`)**:
   Kernel-verified (`decide +kernel`) check that every instruction `inst` at byte offset `4 * k`
   (`k < 65`) of `memsetWordsSym` is non-`svc`, never writes `Reg.lr` (`x30`), has sequential
   fallthrough `4 * k + 4 < 260` whenever it can `advancePC`, has PC-relative branch target inside
   `[0, 260)`, and returns exclusively via `ret x30`.
2. **Arbitrary-state instruction step (`execInst_of_isBlk21SafeInstr`) & `fetchMem` bridge (`fetchMem_blk21_safe`)**:
   For any `.Running` state `s` at `s.pc = base + off` (`off < 260`) with arbitrary registers and
   memory (including unmapped/garbage `x0`/`x2`/`sp`), `execInst inst s` either faults to
   `.Exception _` or stays `.Running` with unchanged `lr` and `pc ∈ {lr} ∪ [base, base + 260)`.
3. **Closed-trap contradiction (`blk21_trap_impossible`) & global `hlr_calls` (`blk21_lr_trap_false`, `blk21_lr_trap_false_gen`)**:
   Both strict `(a)` (`keepMemsetBlk21 mmpl pc = true → P_ghost.externAt? pc = none`, for
   `--branch-stubs`) and generalized `(a')` (allowing `memsetGhostHook` at offset `0` of `blk21`,
   for stock `ld.lld` direct links where `mpl.ρ "memset" = mmpl.base 21`) trap execution inside
   `blk21 ∪ {.Exception _, .Halted}`, contradicting any run reaching `.Exited _` or `.Panicked`
   (or any status outside `{.Running, .Exception _, .Halted}`).
4. **Specialized replay & cutover corollaries (`ghostExternReplays_f3MemsetGhostHookNarrow_of_trap*`, `steps_transfer_f3MemsetGhostHookNarrow*`)**:
   Eliminates `keepMemsetBlk21 mmpl (u.readReg64 .lr) = false` from
   `ghostExternReplays_f3MemsetGhostHookNarrow` and `steps_transfer_allocGhost`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrap

open Arm64 ProofLib
open VerifiedLibraries.Mallocng (mallocngBlockProg)
open VerifiedLibraries.Musl (memsetWordsSym)
open CryptoVerification.SignalSession (CliHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre ExecFrozen GhostExternReplays StubReachesTarget steps_transfer_allocGhost
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  masterMemsetSpec memsetWordsSym_length
  mallocngBlockProg21_hasWords mallocngBlockProg21_externAt_none
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (
  memsetGhostHook memsetGhostHookK keepMemsetBlk21
  keepCoversBlk21_keepMemsetBlk21
  memsetGhostHook_of_keepLr_true memsetGhostHookK_of_keepLr_true
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplays (
  mallocngBlockProg21_code_length
  f3RealProg617 f3RealProg617_svc_eq
  f3MemsetGhostHookNarrow f3MemsetGhostHookNarrowK
  ghostExternReplays_f3MemsetGhostHookNarrow
)

/-! ## 1. Syntactic 65-Instruction Trap Classifier & Arbitrary-State Step Lemma -/

/-- Syntactic safety classifier for an instruction `inst` at byte offset `off` inside `blk21`
    (`260` bytes = `65` words):
    - `inst` is never `svc`/`brk`/`bl`/`blr`/`br`,
    - `inst` never writes `Reg.lr` (`x30`),
    - `.ret rn` has `rn = .lr`,
    - sequential fallthrough (`advancePC`) has `off + 4 < 260`, and
    - PC-relative branch offsets `relOff` satisfy `(BitVec.ofNat 64 off + relOff).toNat < 260`. -/
def isBlk21SafeInstr (off : Nat) (inst : Instr) : Bool :=
  match inst with
  | .ret rn => decide (rn = .lr)
  | .nop => decide (off + 4 < 260)
  | .bCond _ relOff =>
    decide (off + 4 < 260) && decide ((BitVec.ofNat 64 off + relOff).toNat < 260)
  | .cbz _ _ _ relOff =>
    decide (off + 4 < 260) && decide ((BitVec.ofNat 64 off + relOff).toNat < 260)
  | .tbz _ _ _ _ relOff =>
    decide (off + 4 < 260) && decide ((BitVec.ofNat 64 off + relOff).toNat < 260)
  | .addSubImm _ _ rd _ _ _ =>
    decide (off + 4 < 260) && decide (rd ≠ .lr)
  | .addSubShift _ _ rd _ _ _ _ =>
    decide (off + 4 < 260) && decide (rd ≠ .lr)
  | .logicalImm _ _ rd _ _ =>
    decide (off + 4 < 260) && decide (rd ≠ .lr)
  | .bitfield _ _ rd _ _ _ =>
    decide (off + 4 < 260) && decide (rd ≠ .lr)
  | .condCompareImm _ _ _ _ _ _ =>
    decide (off + 4 < 260)
  | .str _ _ addr =>
    decide (off + 4 < 260) && decide (addr.baseReg ≠ .lr)
  | .strSimd _ _ addr =>
    decide (off + 4 < 260) && decide (addr.baseReg ≠ .lr)
  | .stpSimd _ _ _ addr =>
    decide (off + 4 < 260) && decide (addr.baseReg ≠ .lr)
  | .simdInsDup _ _ _ _ _ rd =>
    decide (off + 4 < 260) && decide (Reg.fromZRBits rd ≠ .lr)
  | .sysReg isRead sysreg rt =>
    decide (off + 4 < 260) && isRead && decide (sysreg = 0x5807#15) && decide (rt ≠ .lr)
  | .dcZva _ =>
    decide (off + 4 < 260)
  | _ => false

theorem memsetWords_all_safe :
    ((List.range 65).all fun k =>
      match memsetWordsSym[k]? with
      | some w =>
        match decode w with
        | some inst => isBlk21SafeInstr (4 * k) inst
        | none => false
      | none => false) = true := by
  decide +kernel

private theorem isBlk21SafeInstr_not_isSvc0 {off : Nat} {inst : Instr}
    (h : isBlk21SafeInstr off inst = true) :
    inst.isSvc0 = false := by
  cases inst <;> simp [isBlk21SafeInstr, Instr.isSvc0] at h ⊢

/-- Single-instruction outcome for an instruction inside `blk21` on arbitrary state `s`:
    either faults with `.Exception msg`, or remains `.Running` with unchanged `lr` and `pc`
    equal to `s.readReg64 .lr` or `base + off'` (`off' < 260`). -/
def Blk21StepOutcome (base : BitVec 64) (s s' : State) : Prop :=
  (∃ msg, s'.status = .Exception msg) ∨
  (s'.status = .Running ∧
   s'.readReg64 .lr = s.readReg64 .lr ∧
   (s'.pc = s.readReg64 .lr ∨ ∃ off' : Nat, off' < 260 ∧ s'.pc = base + BitVec.ofNat 64 off'))

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

private theorem sameRunLrPc_writeReg64 {s s1 : State} (h : SameRunLrPc s s1)
    {r : Reg} (hr : r ≠ .lr) (v : BitVec 64) :
    SameRunLrPc s (s1.writeReg64 r v) :=
  ⟨h.1, (readReg64_lr_writeReg64_ne s1 hr v).trans h.2.1, h.2.2⟩

private theorem sameRunLrPc_writeReg {s s1 : State} (h : SameRunLrPc s s1)
    (w : Width) {r : Reg} (hr : r ≠ .lr) (v : BitVec 64) :
    SameRunLrPc s (s1.writeReg w r v) :=
  sameRunLrPc_writeReg64 h hr _

private theorem sameRunLrPc_writeVReg128 {s s1 : State} (h : SameRunLrPc s s1)
    (vt : VReg) (v : BitVec 128) :
    SameRunLrPc s (s1.writeVReg128 vt v) :=
  ⟨h.1, h.2.1, h.2.2⟩

private theorem sameRunLrPc_setPState {s s1 : State} (h : SameRunLrPc s s1) (ps : PState) :
    SameRunLrPc s (s1.setPState ps) :=
  ⟨h.1, h.2.1, h.2.2⟩

private theorem sameRunLrPc_optPState {s s1 : State} (h : SameRunLrPc s s1)
    (optPs : Option PState) :
    SameRunLrPc s (match optPs with | some ps => s1.setPState ps | none => s1) := by
  cases optPs with
  | none => exact h
  | some ps => exact sameRunLrPc_setPState h ps

private theorem sameRunLrPc_setMem {s s1 : State} (h : SameRunLrPc s s1) (m : Memory) :
    SameRunLrPc s (s1.setMem m) :=
  ⟨h.1, h.2.1, h.2.2⟩

private theorem sameRunLrPc_addrWb {s s1 : State} (s0 : State) (h : SameRunLrPc s s1)
    {addr : AddrMode} (hbr : addr.baseReg ≠ .lr) :
    SameRunLrPc s (match (evalAddrMode s0 addr).2 with
      | some (base, newBase) => s1.writeReg64 base newBase
      | none => s1) := by
  cases addr <;> dsimp only [evalAddrMode, AddrMode.baseReg] at hbr ⊢
  · exact h
  · exact h
  · exact sameRunLrPc_writeReg64 h hbr _
  · exact sameRunLrPc_writeReg64 h hbr _
  · exact h

private theorem outcome_of_advancePC {base : BitVec 64} {off : Nat} {s s1 : State}
    (hrun : s.status = .Running)
    (hpc : s.pc = base + BitVec.ofNat 64 off)
    (hoff : off + 4 < 260)
    (h1 : SameRunLrPc s s1) :
    Blk21StepOutcome base s s1.advancePC := by
  refine Or.inr ⟨h1.1.trans hrun, h1.2.1, Or.inr ⟨off + 4, hoff, ?_⟩⟩
  change s1.pc + 4#64 = base + BitVec.ofNat 64 (off + 4)
  rw [h1.2.2, hpc, BitVec.add_assoc, ← BitVec.ofNat_add]

private theorem outcome_of_branchRel {base : BitVec 64} {off : Nat} {relOff : BitVec 64} {s : State}
    (hrun : s.status = .Running)
    (hpc : s.pc = base + BitVec.ofNat 64 off)
    (htgt : (BitVec.ofNat 64 off + relOff).toNat < 260) :
    Blk21StepOutcome base s (s.setPC (s.pc + relOff)) := by
  refine Or.inr ⟨hrun, rfl, Or.inr ⟨(BitVec.ofNat 64 off + relOff).toNat, htgt, ?_⟩⟩
  change s.pc + relOff = base + BitVec.ofNat 64 (BitVec.ofNat 64 off + relOff).toNat
  rw [hpc, BitVec.add_assoc, BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem band_true {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> cases h
  exact ⟨rfl, rfl⟩

private theorem blk21_ite {base : BitVec 64} {s : State} {c : Prop} [inst : Decidable c]
    {t e : State} (ht : Blk21StepOutcome base s t) (he : Blk21StepOutcome base s e) :
    Blk21StepOutcome base s (if c then t else e) :=
  match inst with
  | isTrue _ => ht
  | isFalse _ => he

/-- Any `isBlk21SafeInstr off inst = true` instruction executed from `s.status = .Running` and
    `s.pc = base + BitVec.ofNat 64 off` satisfies `Blk21StepOutcome base s (execInst inst s)`, for
    **arbitrary** register and memory contents. -/
theorem execInst_of_isBlk21SafeInstr {base : BitVec 64} {off : Nat} {inst : Instr} {s : State}
    (hsafe : isBlk21SafeInstr off inst = true)
    (hrun : s.status = .Running)
    (hpc : s.pc = base + BitVec.ofNat 64 off) :
    Blk21StepOutcome base s (execInst inst s) := by
  cases inst <;> try (unfold isBlk21SafeInstr at hsafe; contradiction)
  case ret rn =>
    unfold isBlk21SafeInstr at hsafe
    have hrn : rn = .lr := of_decide_eq_true hsafe
    subst hrn
    exact Or.inr ⟨hrun, rfl, Or.inl rfl⟩
  case nop =>
    unfold isBlk21SafeInstr at hsafe
    exact outcome_of_advancePC hrun hpc (of_decide_eq_true hsafe) (sameRunLrPc_refl s)
  case bCond cond relOff =>
    unfold isBlk21SafeInstr at hsafe
    obtain ⟨hoff0, htgt0⟩ := band_true hsafe
    have hoff := of_decide_eq_true hoff0
    have htgt := of_decide_eq_true htgt0
    change Blk21StepOutcome base s
      (if ConditionHolds cond s.pstate then s.setPC (s.pc + relOff) else s.advancePC)
    split
    · exact outcome_of_branchRel hrun hpc htgt
    · exact outcome_of_advancePC hrun hpc hoff (sameRunLrPc_refl s)
  case cbz w isNonZero rt relOff =>
    unfold isBlk21SafeInstr at hsafe
    obtain ⟨hoff0, htgt0⟩ := band_true hsafe
    have hoff := of_decide_eq_true hoff0
    have htgt := of_decide_eq_true htgt0
    let val := s.readReg w rt
    let c := if isNonZero then (val == 0#64) != true else val == 0#64
    change Blk21StepOutcome base s (if c then s.setPC (s.pc + relOff) else s.advancePC)
    split
    · exact outcome_of_branchRel hrun hpc htgt
    · exact outcome_of_advancePC hrun hpc hoff (sameRunLrPc_refl s)
  case tbz w isNonZero rt bit relOff =>
    unfold isBlk21SafeInstr at hsafe
    obtain ⟨hoff0, htgt0⟩ := band_true hsafe
    have hoff := of_decide_eq_true hoff0
    have htgt := of_decide_eq_true htgt0
    change Blk21StepOutcome base s
      (if (s.readReg64 rt).getLsbD bit == isNonZero then s.setPC (s.pc + relOff) else s.advancePC)
    split
    · exact outcome_of_branchRel hrun hpc htgt
    · exact outcome_of_advancePC hrun hpc hoff (sameRunLrPc_refl s)
  case addSubImm w op rd rn imm12 shift12 =>
    unfold isBlk21SafeInstr at hsafe
    obtain ⟨hoff0, hrd0⟩ := band_true hsafe
    exact outcome_of_advancePC hrun hpc (of_decide_eq_true hoff0)
      (sameRunLrPc_optPState
        (sameRunLrPc_writeReg (sameRunLrPc_refl s) w (of_decide_eq_true hrd0) _) _)
  case addSubShift w op rd rn rm shift amount =>
    unfold isBlk21SafeInstr at hsafe
    obtain ⟨hoff0, hrd0⟩ := band_true hsafe
    exact outcome_of_advancePC hrun hpc (of_decide_eq_true hoff0)
      (sameRunLrPc_optPState
        (sameRunLrPc_writeReg (sameRunLrPc_refl s) w (of_decide_eq_true hrd0) _) _)
  case logicalImm w op rd rn mask =>
    unfold isBlk21SafeInstr at hsafe
    obtain ⟨hoff0, hrd0⟩ := band_true hsafe
    exact outcome_of_advancePC hrun hpc (of_decide_eq_true hoff0)
      (sameRunLrPc_optPState
        (sameRunLrPc_writeReg (sameRunLrPc_refl s) w (of_decide_eq_true hrd0) _) _)
  case bitfield w op rd rn immr imms =>
    unfold isBlk21SafeInstr at hsafe
    obtain ⟨hoff0, hrd0⟩ := band_true hsafe
    exact outcome_of_advancePC hrun hpc (of_decide_eq_true hoff0)
      (sameRunLrPc_writeReg (sameRunLrPc_refl s) w (of_decide_eq_true hrd0) _)
  case condCompareImm w isSub rn imm5 nzcv cond =>
    unfold isBlk21SafeInstr at hsafe
    have hoff := of_decide_eq_true hsafe
    change Blk21StepOutcome base s
      (execCondCompare w isSub true rn (imm5.zeroExtend 64) .xzr nzcv cond s)
    unfold execCondCompare
    split
    · exact outcome_of_advancePC hrun hpc hoff (sameRunLrPc_optPState (sameRunLrPc_refl s) _)
    · exact outcome_of_advancePC hrun hpc hoff (sameRunLrPc_setPState (sameRunLrPc_refl s) _)
  case str sz rt addr =>
    unfold isBlk21SafeInstr at hsafe
    obtain ⟨hoff0, hbr0⟩ := band_true hsafe
    have hoff := of_decide_eq_true hoff0
    have hbr := of_decide_eq_true hbr0
    change Blk21StepOutcome base s (execStr sz rt addr s)
    unfold execStr
    split
    · exact Or.inl ⟨_, rfl⟩
    · dsimp only []
      split
      · exact Or.inl ⟨_, rfl⟩
      · exact outcome_of_advancePC hrun hpc hoff
          (sameRunLrPc_addrWb s (sameRunLrPc_setMem (sameRunLrPc_refl s) _) hbr)
  case strSimd sz vt addr =>
    unfold isBlk21SafeInstr at hsafe
    obtain ⟨hoff0, hbr0⟩ := band_true hsafe
    have hoff := of_decide_eq_true hoff0
    have hbr := of_decide_eq_true hbr0
    have hexec : execInst (.strSimd sz vt addr) s =
        (if !checkAddrSPAligned s addr then s.setStatus (.Exception "SP alignment fault")
         else
           let (ea, wb) := evalAddrMode s addr
           if !s.mem.canWrite ea sz.bytes then s.setStatus (.Exception "permission fault")
           else
             let s1 := s.setMem (s.mem.writeSimdSized sz ea (s.readVReg128 vt))
             let s2 := match wb with | some (base, newBase) => s1.writeReg64 base newBase | none => s1
             s2.advancePC) := rfl
    rw [hexec]
    split
    · exact Or.inl ⟨_, rfl⟩
    · dsimp only []
      split
      · exact Or.inl ⟨_, rfl⟩
      · exact outcome_of_advancePC hrun hpc hoff
          (sameRunLrPc_addrWb s (sameRunLrPc_setMem (sameRunLrPc_refl s) _) hbr)
  case stpSimd sz vt1 vt2 addr =>
    unfold isBlk21SafeInstr at hsafe
    obtain ⟨hoff0, hbr0⟩ := band_true hsafe
    have hoff := of_decide_eq_true hoff0
    have hbr := of_decide_eq_true hbr0
    clear hsafe hoff0 hbr0
    have hstp (stepBytes : BitVec 64) :
        Blk21StepOutcome base s
          (if !checkAddrSPAligned s addr then s.setStatus (.Exception "SP alignment fault")
           else
             let (ea, wb) := evalAddrMode s addr
             if !(s.mem.canWrite ea sz.bytes && s.mem.canWrite (ea + stepBytes) sz.bytes) then
               s.setStatus (.Exception "permission fault")
             else
               let v1 := s.readVReg128 vt1
               let v2 := s.readVReg128 vt2
               let m1 := s.mem.writeSimdSized sz ea v1
               let m2 := m1.writeSimdSized sz (ea + stepBytes) v2
               let s1 := s.setMem m2
               let s2 := match wb with | some (base, newBase) => s1.writeReg64 base newBase | none => s1
               s2.advancePC) :=
      blk21_ite (Or.inl ⟨_, rfl⟩)
        (blk21_ite (Or.inl ⟨_, rfl⟩)
          (outcome_of_advancePC hrun hpc hoff
            (sameRunLrPc_addrWb s (sameRunLrPc_setMem (sameRunLrPc_refl s) _) hbr)))
    cases sz
    · exact hstp 1#64
    · exact hstp 2#64
    · exact hstp 4#64
    · exact hstp 8#64
    · exact hstp 16#64
  case simdInsDup q op imm5 imm4 rn rd =>
    unfold isBlk21SafeInstr at hsafe
    obtain ⟨hoff0, hrd0⟩ := band_true hsafe
    have hoff := of_decide_eq_true hoff0
    have hrd := of_decide_eq_true hrd0
    clear hsafe hoff0 hrd0
    let esize : Nat :=
      if (imm5.extractLsb' 0 1) == 1#1 then 8
      else if (imm5.extractLsb' 0 2) == 2#2 then 16
      else if (imm5.extractLsb' 0 3) == 4#3 then 32
      else 64
    let dstIdx : Nat :=
      if esize == 8 then imm5.toNat >>> 1
      else if esize == 16 then imm5.toNat >>> 2
      else if esize == 32 then imm5.toNat >>> 3
      else imm5.toNat >>> 4
    let mask : BitVec 128 := (1#128 <<< esize) - 1#128
    have hexec : execInst (.simdInsDup q op imm5 imm4 rn rd) s =
        (if (imm5.extractLsb' 0 4) == 0#4 then
           { s with status := .Exception s!"unsupported AdvSIMD: simdInsDup (q={if q then 1 else 0} op={if op then 1 else 0} imm5={imm5.toNat} imm4={imm4.toNat}) — architecturally UNDEFINED" }
         else if !op && imm4 == 0b0001#4 && !(esize == 64 && !q) then
           let elem := ((s.readReg64 (Reg.fromZRBits rn)).zeroExtend 128) &&& mask
           let res := mapSimdLanes q esize 0#128 (fun _ => elem)
           (s.writeVReg128 rd res).advancePC
         else if !op && imm4 == 0b0000#4 && !(esize == 64 && !q) then
           let elem := getSimdLane (s.readVReg128 rn) esize dstIdx
           let res := mapSimdLanes q esize 0#128 (fun _ => elem)
           (s.writeVReg128 rd res).advancePC
         else if q && !op && imm4 == 0b0011#4 then
           let elem := ((s.readReg64 (Reg.fromZRBits rn)).zeroExtend 128) &&& mask
           let old := s.readVReg128 rd
           let clearMask := ~~~(mask <<< (dstIdx * esize))
           let res := (old &&& clearMask) ||| (elem <<< (dstIdx * esize))
           (s.writeVReg128 rd res).advancePC
         else if !op && imm4 == 0b0111#4 && ((q && esize == 64) || (!q && esize < 64)) then
           let elem := (getSimdLane (s.readVReg128 rn) esize dstIdx).truncate 64
           let w : Width := if q then .W64 else .W32
           (s.writeReg w (Reg.fromZRBits rd) elem).advancePC
         else if !op && imm4 == 0b0101#4 && ((q && esize < 64) || (!q && esize < 32)) then
           let elem := (getSimdLane (s.readVReg128 rn) esize dstIdx).truncate 64
           let signExt :=
             if elem.getLsbD (esize - 1) then elem ||| ~~~((1#64 <<< esize) - 1#64) else elem
           let w : Width := if q then .W64 else .W32
           (s.writeReg w (Reg.fromZRBits rd) signExt).advancePC
         else if q && op then
           let srcIdx : Nat :=
             if esize == 8 then imm4.toNat
             else if esize == 16 then imm4.toNat >>> 1
             else if esize == 32 then imm4.toNat >>> 2
             else imm4.toNat >>> 3
           let elem := getSimdLane (s.readVReg128 rn) esize srcIdx
           let old := s.readVReg128 rd
           let clearMask := ~~~(mask <<< (dstIdx * esize))
           let res := (old &&& clearMask) ||| (elem <<< (dstIdx * esize))
           (s.writeVReg128 rd res).advancePC
         else
           { s with status := .Exception s!"unsupported AdvSIMD: simdInsDup (q={if q then 1 else 0} op={if op then 1 else 0} imm5={imm5.toNat} imm4={imm4.toNat}) — architecturally UNDEFINED" }) := rfl
    rw [hexec]
    exact blk21_ite (Or.inl ⟨_, rfl⟩)
      (blk21_ite
        (outcome_of_advancePC hrun hpc hoff (sameRunLrPc_writeVReg128 (sameRunLrPc_refl s) rd _))
        (blk21_ite
          (outcome_of_advancePC hrun hpc hoff (sameRunLrPc_writeVReg128 (sameRunLrPc_refl s) rd _))
          (blk21_ite
            (outcome_of_advancePC hrun hpc hoff (sameRunLrPc_writeVReg128 (sameRunLrPc_refl s) rd _))
            (blk21_ite
              (outcome_of_advancePC hrun hpc hoff (sameRunLrPc_writeReg (sameRunLrPc_refl s) _ hrd _))
              (blk21_ite
                (outcome_of_advancePC hrun hpc hoff (sameRunLrPc_writeReg (sameRunLrPc_refl s) _ hrd _))
                (blk21_ite
                  (outcome_of_advancePC hrun hpc hoff (sameRunLrPc_writeVReg128 (sameRunLrPc_refl s) rd _))
                  (Or.inl ⟨_, rfl⟩)))))))
  case sysReg isRead sysreg rt =>
    unfold isBlk21SafeInstr at hsafe
    obtain ⟨h12, hrt0⟩ := band_true hsafe
    obtain ⟨h1, hsr0⟩ := band_true h12
    obtain ⟨hoff0, hisRead⟩ := band_true h1
    have hoff := of_decide_eq_true hoff0
    have hsr := of_decide_eq_true hsr0
    have hrt := of_decide_eq_true hrt0
    subst hisRead hsr
    have hexec : execInst (.sysReg true 0x5807#15 rt) s = (s.writeReg64 rt 4#64).advancePC := rfl
    rw [hexec]
    exact outcome_of_advancePC hrun hpc hoff (sameRunLrPc_writeReg64 (sameRunLrPc_refl s) hrt 4#64)
  case dcZva rt =>
    unfold isBlk21SafeInstr at hsafe
    have hoff := of_decide_eq_true hsafe
    have hexec : execInst (.dcZva rt) s =
        (let ea := s.readReg64 rt &&& ~~~63#64
         if !s.mem.canWrite ea 64 then s.setStatus (.Exception "permission fault")
         else (s.setMem (simdStoreRegs .Q128 (fun _ => 0#128) 4 0#5 ea s.mem)).advancePC) := rfl
    rw [hexec]
    dsimp only []
    split
    · exact Or.inl ⟨_, rfl⟩
    · exact outcome_of_advancePC hrun hpc hoff (sameRunLrPc_setMem (sameRunLrPc_refl s) _)

/-! ## 2. Dynamic `fetchMem` Bridge & Closed-Trap Contradiction -/

/-- Any instruction dynamically fetched by `P_ghost.fetchMem m pc = some inst` at an address `pc`
    with `keepMemsetBlk21 mmpl pc = true` when `mallocngBlockProg mmpl 21` is loaded in `m` lies at
    some offset `off < 260` from `mmpl.base 21` and satisfies `isBlk21SafeInstr off inst = true`. -/
theorem fetchMem_blk21_safe
    {P_ghost : Program} {mmpl : Obj.MultiPlacement} {m : Memory}
    {pc : BitVec 64} {inst : Instr}
    (hkeep : keepMemsetBlk21 mmpl pc = true)
    (hL : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m)
    (hfm : P_ghost.fetchMem m pc = some inst) :
    ∃ off : Nat, off < 260 ∧
      pc = mmpl.base 21 + BitVec.ofNat 64 off ∧
      isBlk21SafeInstr off inst = true := by
  have hoff_lt : (pc - mmpl.base 21).toNat < 260 := of_decide_eq_true hkeep
  let off := (pc - mmpl.base 21).toNat
  have hpc_eq : pc = mmpl.base 21 + BitVec.ofNat 64 off := by
    dsimp only [off]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm (mmpl.base 21),
      BitVec.sub_add_cancel]
  have hfm0 := hfm
  unfold Program.fetchMem at hfm0
  cases heg : P_ghost.externAt? pc with
  | some _ => simp [heg] at hfm0
  | none =>
    simp only [heg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm0
    split at hfm0
    · contradiction
    rename_i hal_neg
    have hal : pc.toNat % 4 = 0 := Classical.not_not.mp hal_neg
    have hbase_al : (mmpl.base 21).toNat % 4 = 0 := hL.aligned
    have hnowrap : (mmpl.base 21).toNat + 260 ≤ 2 ^ 64 := by
      have hnw := hL.no_wrap
      rwa [mallocngBlockProg21_code_length mmpl] at hnw
    have hpc_nat : pc.toNat = (mmpl.base 21).toNat + off := by
      rw [hpc_eq, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hoff_mod : off % 4 = 0 := by omega
    let k := off / 4
    have hoff_k : off = 4 * k := by omega
    have hk : k < 65 := by omega
    have hk_len : k < memsetWordsSym.length := by rw [memsetWordsSym_length]; exact hk
    have hall_k := List.all_eq_true.mp memsetWords_all_safe k (List.mem_range.mpr hk)
    rw [List.getElem?_eq_getElem hk_len] at hall_k
    dsimp only [] at hall_k
    cases hdec : decode memsetWordsSym[k] with
    | none =>
      rw [hdec] at hall_k
      contradiction
    | some inst' =>
      rw [hdec] at hall_k
      dsimp only [] at hall_k
      let P_sub := mallocngBlockProg mmpl 21 Syscall.standard
      have hrw := (mallocngBlockProg21_hasWords mmpl Syscall.standard).2.1 k hk_len
      change P_sub.readWordOff ((mmpl.base 21 - mmpl.base 21).toNat + 4 * k) =
        some memsetWordsSym[k] at hrw
      rw [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, ← hoff_k] at hrw
      have hext_sub : P_sub.externAt? pc = none :=
        mallocngBlockProg21_externAt_none mmpl Syscall.standard pc
      have hfetch_sub : P_sub.fetch pc = some inst' := by
        unfold Program.fetch
        have hbase_sub : (pc - P_sub.base).toNat = off := rfl
        rw [hext_sub, hbase_sub, hrw]
        exact hdec
      have hfm_sub : P_sub.fetchMem m pc = some inst' := P_sub.fetchMem_of_fetch hL hfetch_sub
      have hfm_eq : P_ghost.fetchMem m pc = P_sub.fetchMem m pc :=
        ProofLib.Variant.fetchMem_eq_of_externAt_eq (heg.trans hext_sub.symm)
      rw [hfm_eq, hfm_sub] at hfm
      cases hfm
      exact ⟨off, hoff_lt, hpc_eq, hoff_k ▸ hall_k⟩

/-- Hook-level trap preservation at `lr = L`: on any `.Running` state `w` with `w.readReg64 .lr = L`,
    `f w` either transitions to `.Exception _` or stays `.Running` at `pc = L` with `lr = L`. -/
@[expose] def Blk21TrapHook (L : BitVec 64) (f : State → State) : Prop :=
  ∀ w : State, w.status = .Running → w.readReg64 .lr = L →
    (∃ msg, (f w).status = .Exception msg) ∨
    ((f w).status = .Running ∧ (f w).pc = L ∧ (f w).readReg64 .lr = L)

theorem blk21TrapHook_hookMemset (L : BitVec 64) : Blk21TrapHook L hookMemset := by
  intro w hrun hlr
  exact Or.inr ⟨hrun, hlr, hlr⟩

/-- Plain `memsetGhostHook` satisfies `Blk21TrapHook L` whenever `keep L = true`: if
    `ActiveRealPre masterMemsetSpec w` holds, it takes the fallback `hookMemset w`
    (`memsetGhostHook_of_keepLr_true`, setting `pc := L` and keeping `lr = L`); otherwise (e.g. on
    garbage/unmapped `x0`/`x2` or misaligned `sp`), it faults with `.Exception _`. -/
theorem blk21TrapHook_memsetGhostHook
    {keep : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (hkeepL : keep L = true) :
    Blk21TrapHook L (memsetGhostHook keep P_real P_sub entryTarget) := by
  classical
  intro w hrun hlr
  by_cases hAct : ActiveRealPre masterMemsetSpec w
  · rw [memsetGhostHook_of_keepLr_true hAct (hlr ▸ hkeepL)]
    exact blk21TrapHook_hookMemset L w hrun hlr
  · refine Or.inl ⟨"ghost-hook precondition violated", ?_⟩
    unfold memsetGhostHook AllocGhostLinkTransfer.linkedCallHook
    simp [hAct]

/-- `K`-narrowed `memsetGhostHookK` also satisfies `Blk21TrapHook L` whenever `keep L = true`
    (it transitions immediately to `.Exception _`). -/
theorem blk21TrapHook_memsetGhostHookK
    {keep : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (hkeepL : keep L = true) :
    Blk21TrapHook L (memsetGhostHookK keep P_real P_sub entryTarget) := by
  intro w _ hlr
  rw [memsetGhostHookK_of_keepLr_true (hlr ▸ hkeepL)]
  exact Or.inl ⟨"ghost-hook precondition violated", rfl⟩

/-- Closed-trap invariant on `blk21` (`260` B at `mmpl.base 21`) with pinned `lr = L`. -/
@[expose] def Blk21TrapInv (mmpl : Obj.MultiPlacement) (L : BitVec 64) (w : State) : Prop :=
  w.status = .Running ∧
  keepMemsetBlk21 mmpl w.pc = true ∧
  w.readReg64 .lr = L ∧
  (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded w.mem

/-- **Closed-trap impossibility (`blk21_trap_impossible`):**
    No `Steps P_ghost w sf` starting in `Blk21TrapInv mmpl L w` (`keepMemsetBlk21 mmpl L = true`)
    can reach a terminal state `sf` whose status is outside `{.Running, .Exception _, .Halted}`
    (in particular, `sf.status = .Exited _` or `sf.status = .Panicked`), provided any extern inside
    `blk21` (none under `--branch-stubs`, or `memsetGhostHook` at offset `0` under stock `ld.lld`)
    satisfies `Blk21TrapHook L`. -/
theorem blk21_trap_impossible
    {P_ghost : Program} {mmpl : Obj.MultiPlacement} {L : BitVec 64}
    (hL_in : keepMemsetBlk21 mmpl L = true)
    (hblk21_ext : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ Blk21TrapHook L f)
    {w sf : State}
    (hsteps : Steps P_ghost w sf)
    (hrun_sf : sf.status ≠ .Running)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted)
    (hInv : Blk21TrapInv mmpl L w) :
    False := by
  induction hsteps with
  | refl s =>
    exact hrun_sf hInv.1
  | @step s1 s2 s3 h1 hrest ih =>
    rcases hInv with ⟨hrun1, hkeep1, hlr1, hCode1⟩
    have hCode2 : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded s2.mem :=
      h1.codeLoaded hCode1
    cases h1 with
    | halt_unmapped _ _ _ =>
      have heq := ProofLib.Variant.Steps.eq_of_not_running hrest nofun
      have hst : s3.status = .Halted := by rw [heq]
      exact hnhalt_sf hst
    | extern_fault _ _ _ =>
      have heq := ProofLib.Variant.Steps.eq_of_not_running hrest nofun
      have hst : s3.status = .Exception "extern hook modified read-only memory or symbol table" := by
        rw [heq]
      exact hnoex_sf _ hst
    | @extern f _ hext _ _ =>
      rcases hblk21_ext s1.pc hkeep1 with hnone | ⟨f', hext', htrap⟩
      · rw [hnone] at hext; contradiction
      · rw [hext'] at hext
        injection hext with hfeq
        subst hfeq
        rcases htrap s1 hrun1 hlr1 with ⟨msg, hex⟩ | ⟨hrun2, hpc2, hlr2⟩
        · have heq := ProofLib.Variant.Steps.eq_of_not_running hrest
            (by rw [hex]; nofun)
          have hst : s3.status = .Exception msg := by rw [heq, hex]
          exact hnoex_sf msg hst
        · exact ih hrun_sf hnoex_sf hnhalt_sf ⟨hrun2, hpc2 ▸ hL_in, hlr2, hCode2⟩
    | @exec inst _ hfm =>
      obtain ⟨off, _, hpc1, hsafe⟩ := fetchMem_blk21_safe hkeep1 hCode1 hfm
      have hnsvc0 := isBlk21SafeInstr_not_isSvc0 hsafe
      have heval : P_ghost.evalInst inst s1 = execInst inst s1 :=
        evalInst_eq_execInst_of_not_isSvc0 hnsvc0 s1
      rcases execInst_of_isBlk21SafeInstr hsafe hrun1 hpc1 with
        ⟨msg, hex⟩ | ⟨hrun2, hlr_eq, hpc_next⟩
      · have hex' : (P_ghost.evalInst inst s1).status = .Exception msg := heval ▸ hex
        have heq := ProofLib.Variant.Steps.eq_of_not_running hrest
          (by rw [hex']; nofun)
        have hst : s3.status = .Exception msg := by rw [heq, hex']
        exact hnoex_sf msg hst
      · rw [heval] at ih hCode2
        have hkeep2 : keepMemsetBlk21 mmpl (execInst inst s1).pc = true := by
          rcases hpc_next with hpc_ret | ⟨off', hoff', hpc_off⟩
          · rw [hpc_ret, hlr1]; exact hL_in
          · rw [hpc_off]; exact keepCoversBlk21_keepMemsetBlk21 mmpl off' hoff'
        exact ih hrun_sf hnoex_sf hnhalt_sf ⟨hrun2, hkeep2, hlr_eq.trans hlr1, hCode2⟩

/-! ## 3. Global `hlr_calls` Theorems & Specialized `f3MemsetGhostHookNarrow` Corollaries -/

theorem status_nonRunning_of_exited_or_panicked {sf : State}
    (hterm : (∃ code, sf.status = .Exited code) ∨ sf.status = .Panicked) :
    sf.status ≠ .Running ∧ (∀ msg, sf.status ≠ .Exception msg) ∧ sf.status ≠ .Halted := by
  rcases hterm with ⟨code, hex⟩ | hpan
  · rw [hex]; exact ⟨nofun, fun _ => nofun, nofun⟩
  · rw [hpan]; exact ⟨by decide, fun _ => nofun, by decide⟩

/-- Core per-call `lr ∉ blk21` contradiction over an opaque hook `f_ms` satisfying
    `Blk21TrapHook (u.readReg64 .lr) f_ms` whenever `keepMemsetBlk21 mmpl (u.readReg64 .lr) = true`. -/
theorem blk21_lr_trap_at_call
    {P_ghost : Program} {mmpl : Obj.MultiPlacement} {f_ms : State → State}
    {u sf : State}
    (htrap_of_in : keepMemsetBlk21 mmpl (u.readReg64 .lr) = true →
      Blk21TrapHook (u.readReg64 .lr) f_ms)
    (hblk21_ext : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨ P_ghost.externAt? pc = some f_ms)
    (hext_u : P_ghost.externAt? u.pc = some f_ms)
    (hCode_u : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded u.mem)
    (hsteps_u_sf : Steps P_ghost u sf)
    (hrun_u : u.status = .Running)
    (hrun_sf : sf.status ≠ .Running)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepMemsetBlk21 mmpl (u.readReg64 .lr) = false := by
  cases hkeepL : keepMemsetBlk21 mmpl (u.readReg64 .lr) with
  | false => rfl
  | true =>
    exfalso
    let L := u.readReg64 .lr
    have htrap_ms : Blk21TrapHook L f_ms := htrap_of_in hkeepL
    have hblk21_trap : ∀ pc, keepMemsetBlk21 mmpl pc = true →
        P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ Blk21TrapHook L f := by
      intro pc hkp
      rcases hblk21_ext pc hkp with hnone | hsome
      · exact Or.inl hnone
      · exact Or.inr ⟨f_ms, hsome, htrap_ms⟩
    cases hsteps_u_sf with
    | refl =>
      exact hrun_sf hrun_u
    | @step _ v _ h1 hrest =>
      have hCode_v : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded v.mem :=
        h1.codeLoaded hCode_u
      cases h1 with
      | exec _ hfm =>
        unfold Program.fetchMem at hfm
        rw [hext_u] at hfm
        contradiction
      | halt_unmapped _ _ hext0 =>
        rw [hext_u] at hext0; contradiction
      | extern_fault _ _ _ =>
        have heq := ProofLib.Variant.Steps.eq_of_not_running hrest nofun
        have hst : sf.status =
            .Exception "extern hook modified read-only memory or symbol table" := by rw [heq]
        exact hnoex_sf _ hst
      | @extern f _ hext _ _ =>
        rw [hext_u] at hext
        injection hext with hfeq
        subst hfeq
        rcases htrap_ms u hrun_u rfl with ⟨msg, hex⟩ | ⟨hrun_v, hpc_v, hlr_v⟩
        · have heq := ProofLib.Variant.Steps.eq_of_not_running hrest
            (by rw [hex]; nofun)
          have hst : sf.status = .Exception msg := by rw [heq, hex]
          exact hnoex_sf msg hst
        · exact blk21_trap_impossible hkeepL hblk21_trap hrest hrun_sf hnoex_sf hnhalt_sf
            ⟨hrun_v, hpc_v ▸ hkeepL, hlr_v, hCode_v⟩

/-- **Generalized global `hlr_calls` discharge (`blk21_lr_trap_false_nonRunning`):**
    Covers **both** `--branch-stubs` (no extern inside `blk21`) and **stock `ld.lld` direct links**
    (where `mpl.ρ "memset" = mmpl.base 21` hooks offset `0` of `blk21` with `memsetGhostHook`), and
    any terminal status outside `{.Running, .Exception _, .Halted}` (`.Exited _`, `.Panicked`,
    `.OutOfMemory`, `.Signaled _`). -/
theorem blk21_lr_trap_false_nonRunning
    {P_ghost P_real P_real' P_sub' : Program}
    {keep : BitVec 64 → Bool} {mmpl : Obj.MultiPlacement} {entryTarget : BitVec 64}
    (hkeep_cover : ∀ a, keepMemsetBlk21 mmpl a = true → keep a = true)
    (hghost_blk21 : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        P_ghost.externAt? pc = some (memsetGhostHook keep P_real' P_sub' entryTarget))
    (hmismatch_memset : ∀ pc, P_ghost.externAt? pc ≠ P_real.externAt? pc →
      P_ghost.externAt? pc = some (memsetGhostHook keep P_real' P_sub' entryTarget))
    {s0 sf : State}
    (hCode0 : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded s0.mem)
    (hrun_sf : sf.status ≠ .Running)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemsetBlk21 mmpl (u.readReg64 .lr) = false := by
  intro u hsteps_s0_u hsteps_u_sf hrun_u hmis
  exact blk21_lr_trap_at_call
    (fun hkeepL => blk21TrapHook_memsetGhostHook P_real' P_sub' entryTarget
      (hkeep_cover _ hkeepL))
    hghost_blk21
    (hmismatch_memset u.pc hmis)
    (hsteps_s0_u.codeLoaded hCode0)
    hsteps_u_sf hrun_u hrun_sf hnoex_sf hnhalt_sf

/-- **Card C5 Headline Theorem (`blk21_lr_trap_false`, strict `(a)` shape matching `c5.md`):**
    *Note: Superseded by `HooksDehook.MemsetLrTrapRet.blk21_lr_trap_false_ret` / `*_returned`
    (which cover `Returned` outcomes and mixed ghost passes; do not use this `.Exited ∨ .Panicked`
    single-hook form for the CLI Block-617 cutover).*
    Discharges `keepMemsetBlk21 mmpl (u.readReg64 .lr) = false` globally along any `Steps P_ghost`
    run reaching `.Exited _` or `.Panicked`, under generic hypotheses `(a)`, `(b)`, `(c)`. -/
theorem blk21_lr_trap_false
    {P_ghost P_real P_real' P_sub' : Program}
    {mmpl : Obj.MultiPlacement} {entryTarget : BitVec 64}
    (ha_no_ext_blk21 : ∀ pc, keepMemsetBlk21 mmpl pc = true → P_ghost.externAt? pc = none)
    (hb_mismatch_memset : ∀ pc, P_ghost.externAt? pc ≠ P_real.externAt? pc →
      P_ghost.externAt? pc =
        some (memsetGhostHook (keepMemsetBlk21 mmpl) P_real' P_sub' entryTarget))
    {s0 sf : State}
    (hc_codeLoaded : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded s0.mem)
    (hterm : (∃ code, sf.status = .Exited code) ∨ sf.status = .Panicked) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemsetBlk21 mmpl (u.readReg64 .lr) = false := by
  obtain ⟨hrun_sf, hnoex_sf, hnhalt_sf⟩ := status_nonRunning_of_exited_or_panicked hterm
  exact blk21_lr_trap_false_nonRunning
    (fun _ h => h)
    (fun pc hkp => Or.inl (ha_no_ext_blk21 pc hkp))
    hb_mismatch_memset
    hc_codeLoaded hrun_sf hnoex_sf hnhalt_sf

/-- Generalized `(a')` variant of `blk21_lr_trap_false` allowing `memsetGhostHook` at offset `0` of
    `blk21` (stock `ld.lld` direct-linked `mpl.ρ "memset" = mmpl.base 21` as well as `--branch-stubs`).
    *Superseded by `HooksDehook.MemsetLrTrapRet.blk21_lr_trap_false_ret` / `*_returned` (do not use
    for the CLI cutover).* -/
theorem blk21_lr_trap_false_gen
    {P_ghost P_real P_real' P_sub' : Program}
    {mmpl : Obj.MultiPlacement} {entryTarget : BitVec 64}
    (ha_blk21 : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        P_ghost.externAt? pc =
          some (memsetGhostHook (keepMemsetBlk21 mmpl) P_real' P_sub' entryTarget))
    (hb_mismatch_memset : ∀ pc, P_ghost.externAt? pc ≠ P_real.externAt? pc →
      P_ghost.externAt? pc =
        some (memsetGhostHook (keepMemsetBlk21 mmpl) P_real' P_sub' entryTarget))
    {s0 sf : State}
    (hc_codeLoaded : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded s0.mem)
    (hterm : (∃ code, sf.status = .Exited code) ∨ sf.status = .Panicked) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemsetBlk21 mmpl (u.readReg64 .lr) = false := by
  obtain ⟨hrun_sf, hnoex_sf, hnhalt_sf⟩ := status_nonRunning_of_exited_or_panicked hterm
  exact blk21_lr_trap_false_nonRunning
    (fun _ h => h) ha_blk21 hb_mismatch_memset hc_codeLoaded hrun_sf hnoex_sf hnhalt_sf

/-- **Card C5 Replay Corollary (`ghostExternReplays_f3MemsetGhostHookNarrow_of_trap`):**
    *Superseded by `HooksDehook.MemsetGhostReplaysOn.ghostExternReplaysOn_f3MemsetGhostHookNarrow_of_trap_ret`
    and `SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemset.h2k_memsetGhostHookNarrow_stub_replayOn_cli617`
    (this legacy corollary takes unguarded `StubReachesTarget`, `W`-dependent `f3RealProg617`, and
    `.Exited ∨ .Panicked`; do not use for the cutover).*
    Specializes `ghostExternReplays_f3MemsetGhostHookNarrow` (`MemsetGhostReplays.lean:522`) with
    `keepMemsetBlk21 mmpl (u.readReg64 .lr) = false` **discharged globally** via `blk21_lr_trap_at_call`
    on any `Steps P_ghost u sf` suffix reaching `.Exited _` or `.Panicked`. -/
theorem ghostExternReplays_f3MemsetGhostHookNarrow_of_trap
    {Inv : Memory → Prop}
    {P_ghost : Program} {mpl mmpl : Obj.MultiPlacement} {W : CliHooks} {stubPc : BitVec 64}
    (ha_no_ext_blk21 : ∀ pc, keepMemsetBlk21 mmpl pc = true → P_ghost.externAt? pc = none)
    (hb_ghost_stub : P_ghost.externAt? stubPc = some (f3MemsetGhostHookNarrow mpl mmpl W))
    (hreal_no : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTarget (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → Inv m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m) :
    (f3RealProg617 mpl mmpl W).externAt? stubPc = none ∧
    ∀ (u sf : State),
      Steps P_ghost u sf →
      ((∃ code, sf.status = .Exited code) ∨ sf.status = .Panicked) →
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3MemsetGhostHookNarrow mpl mmpl W u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      Inv u.mem →
      Steps (f3RealProg617 mpl mmpl W) u (f3MemsetGhostHookNarrow mpl mmpl W u) ∧
      ExecFrozen (f3MemsetGhostHookNarrow mpl mmpl W u).mem := by
  have hReplays := ghostExternReplays_f3MemsetGhostHookNarrow
    hreal_no hreal_stub_none hStub hInvLoaded
  refine ⟨hReplays.1, fun u sf hsteps_u_sf hterm hpc hrun hnoex hfr hinv => ?_⟩
  obtain ⟨hrun_sf, hnoex_sf, hnhalt_sf⟩ := status_nonRunning_of_exited_or_panicked hterm
  have hlr_false : keepMemsetBlk21 mmpl (u.readReg64 .lr) = false :=
    blk21_lr_trap_at_call
      (fun hkeepL => blk21TrapHook_memsetGhostHook _ _ _ hkeepL)
      (fun pc hkp => Or.inl (ha_no_ext_blk21 pc hkp))
      (hpc ▸ hb_ghost_stub)
      (hInvLoaded u.mem hfr hinv)
      hsteps_u_sf hrun hrun_sf hnoex_sf hnhalt_sf
  exact hReplays.2 u hpc hrun hnoex hfr hlr_false hinv

/-- Generalized `(a')` variant of `ghostExternReplays_f3MemsetGhostHookNarrow_of_trap` (also covers
    stock `ld.lld` direct-linked `stubPc = mmpl.base 21`).
    *Superseded by `HooksDehook.MemsetGhostReplaysOn.ghostExternReplaysOn_f3MemsetGhostHookNarrow_of_trap_ret`
    (takes unguarded `StubReachesTarget`; do not use for the cutover).* -/
theorem ghostExternReplays_f3MemsetGhostHookNarrow_of_trap_gen
    {Inv : Memory → Prop}
    {P_ghost : Program} {mpl mmpl : Obj.MultiPlacement} {W : CliHooks} {stubPc : BitVec 64}
    (ha_blk21 : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        P_ghost.externAt? pc = some (f3MemsetGhostHookNarrow mpl mmpl W))
    (hb_ghost_stub : P_ghost.externAt? stubPc = some (f3MemsetGhostHookNarrow mpl mmpl W))
    (hreal_no : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTarget (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → Inv m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m) :
    (f3RealProg617 mpl mmpl W).externAt? stubPc = none ∧
    ∀ (u sf : State),
      Steps P_ghost u sf →
      ((∃ code, sf.status = .Exited code) ∨ sf.status = .Panicked) →
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3MemsetGhostHookNarrow mpl mmpl W u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      Inv u.mem →
      Steps (f3RealProg617 mpl mmpl W) u (f3MemsetGhostHookNarrow mpl mmpl W u) ∧
      ExecFrozen (f3MemsetGhostHookNarrow mpl mmpl W u).mem := by
  have hReplays := ghostExternReplays_f3MemsetGhostHookNarrow
    hreal_no hreal_stub_none hStub hInvLoaded
  refine ⟨hReplays.1, fun u sf hsteps_u_sf hterm hpc hrun hnoex hfr hinv => ?_⟩
  obtain ⟨hrun_sf, hnoex_sf, hnhalt_sf⟩ := status_nonRunning_of_exited_or_panicked hterm
  have hlr_false : keepMemsetBlk21 mmpl (u.readReg64 .lr) = false :=
    blk21_lr_trap_at_call
      (fun hkeepL => blk21TrapHook_memsetGhostHook _ _ _ hkeepL)
      ha_blk21
      (hpc ▸ hb_ghost_stub)
      (hInvLoaded u.mem hfr hinv)
      hsteps_u_sf hrun hrun_sf hnoex_sf hnhalt_sf
  exact hReplays.2 u hpc hrun hnoex hfr hlr_false hinv

/-- **End-to-End Pass-1 Trace Cutover (`steps_transfer_f3MemsetGhostHookNarrow`):**
    *Superseded by `HooksDehook.MemsetGhostReplaysOn.steps_transfer_memsetGhostHookNarrow_On_ret` /
    `_On_returned` (for single-stub `memset`-only passes) and
    `SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemset.h2k_memsetGhostHookNarrow_stub_replayOn_cli617`
    (for the `W`-independent 8-row CLI K cutover); do not use this unguarded `StubReachesTarget`
    corollary for the cutover.*
    Combines `ghostExternReplays_f3MemsetGhostHookNarrow` + `blk21_lr_trap_false_gen` +
    `steps_transfer_allocGhost` to replay `Steps P_ghost s0 sf` as
    `Steps (f3RealProg617 mpl mmpl W) s0 sf` with **zero `lr` hypotheses** (covering both
    `--branch-stubs` and stock `ld.lld` direct links). -/
theorem steps_transfer_f3MemsetGhostHookNarrow
    {P_ghost : Program} {mpl mmpl : Obj.MultiPlacement} {W : CliHooks} {stubPc : BitVec 64}
    (hsvc_ghost : P_ghost.svc = Syscall.standard)
    (ha_blk21 : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        P_ghost.externAt? pc = some (f3MemsetGhostHookNarrow mpl mmpl W))
    (hb_ghost_stub : P_ghost.externAt? stubPc = some (f3MemsetGhostHookNarrow mpl mmpl W))
    (hb_other : ∀ pc, pc ≠ stubPc →
      P_ghost.externAt? pc = (f3RealProg617 mpl mmpl W).externAt? pc)
    (hreal_fr : ∀ pc f, (f3RealProg617 mpl mmpl W).externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hreal_no : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTarget (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 21))
    {s0 sf : State}
    (hsteps : Steps P_ghost s0 sf)
    (hterm : (∃ code, sf.status = .Exited code) ∨ sf.status = .Panicked)
    (hfr0 : ExecFrozen s0.mem)
    (hCode0 : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded s0.mem) :
    Steps (f3RealProg617 mpl mmpl W) s0 sf ∧ ExecFrozen sf.mem := by
  let Inv : Memory → Prop := fun m => (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m
  obtain ⟨hrun_sf, hnoex_sf, hnhalt_sf⟩ := status_nonRunning_of_exited_or_panicked hterm
  have hno_new_hooks : ∀ pc, P_ghost.externAt? pc = none →
      (f3RealProg617 mpl mmpl W).externAt? pc = none := by
    intro pc hgn
    by_cases hpc : pc = stubPc
    · subst hpc; exact hreal_stub_none
    · rw [← hb_other pc hpc]; exact hgn
  have hRepStub := ghostExternReplays_f3MemsetGhostHookNarrow (Inv := Inv)
    hreal_no hreal_stub_none hStub (fun _ _ h => h)
  have hReplays : GhostExternReplays (keepMemsetBlk21 mmpl) Inv P_ghost
      (f3RealProg617 mpl mmpl W) := by
    intro pc f hg
    by_cases hpc : pc = stubPc
    · subst hpc
      rw [hb_ghost_stub] at hg
      injection hg with hfeq
      subst hfeq
      exact Or.inr hRepStub
    · have hr : (f3RealProg617 mpl mmpl W).externAt? pc = some f := by
        rw [← hb_other pc hpc]; exact hg
      exact Or.inl ⟨hr, hreal_fr pc f hr⟩
  have hmis : ∀ pc, P_ghost.externAt? pc ≠ (f3RealProg617 mpl mmpl W).externAt? pc →
      P_ghost.externAt? pc = some (f3MemsetGhostHookNarrow mpl mmpl W) := by
    intro pc hne
    by_cases hpc : pc = stubPc
    · subst hpc; exact hb_ghost_stub
    · exact False.elim (hne (hb_other pc hpc))
  exact steps_transfer_allocGhost
    hsvc_ghost
    (f3RealProg617_svc_eq mpl mmpl W)
    hno_new_hooks
    hReplays
    (fun _ _ hL hk => hL.of_keepsFrozen hk)
    hsteps
    hnoex_sf
    hnhalt_sf
    hfr0
    hCode0
    (blk21_lr_trap_false_gen ha_blk21 hmis hCode0 hterm)

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrap
