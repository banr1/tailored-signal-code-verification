/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrap -- proof-setup: allow-public-import
import ProofLib.OpcodeExclusion
import ProofLib.ProgramReflection.Variant.TrapTransfer

/-!
# Generalized `blk21` Closed-Trap Entry Points (`HooksDehook.MemsetLrTrapRet`)

Implements follow-ups `(A1)` and `(A2)` from `rev_c5.md` §3a, §3b, & §4 without modifying
`HooksDehook/MemsetLrTrap.lean`:

1. **`(A1)` Generalized Terminal Hypothesis (`rev_c5.md` §3a + §4)**:
   Replaces `sf.status ≠ .Running` / `Exited ∨ Panicked` with:
   `hrun_sf' : sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false`,
   together with `∀ msg, sf.status ≠ .Exception msg` and `sf.status ≠ .Halted`.
   - `blk21_trap_impossible_ret` closes `Steps.refl` directly from `Blk21TrapInv`'s
     `w.status = .Running ∧ keepMemsetBlk21 mmpl w.pc = true` vs. `hrun_sf'`.
   - `blk21_lr_trap_after_hook_ret` discharges `keepMemsetBlk21 mmpl (u.readReg64 .lr) = false`
     from the post-hook continuation `Steps P_ghost (f_u u) sf` (the exact premise supplied by
     `GhostExternReplaysOn`, needing **only** `hrun_sf'`, `hnoex_sf`, `hnhalt_sf` and zero extra
     constraint on `sf.pc`).
   - Covers `.Exited _`, `.Panicked`, `.OutOfMemory`, `.Signaled _`, **and** subroutine `Returned`
     (`sf.status = .Running ∧ sf.pc = s0.readReg64 .lr`) given
     `keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false`.
2. **`(A2)` Mixed-Pass Per-PC `Blk21TrapHook` Existential (`rev_c5.md` §3b)**:
   Replaces single-hook `hb_mismatch_memset` with:
   `∀ pc, P_ghost.externAt? pc ≠ P_real.externAt? pc →
     ∃ f, P_ghost.externAt? pc = some f ∧ ∀ L, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f`,
   and proves that **every** K-narrowed `linkedCallHook` or `f3LinkedCallHook` whose precondition
   enforces `keep (w.readReg64 .lr) = false` for `keep ⊇ keepMemsetBlk21 mmpl` (covering both
   `h2k_withKeepLrFalse` and `h2k_withKeepLrAndFds` across all 7 K-route ghosts) satisfies
   `Blk21TrapHook L` via its `.Exception` guard branch, alongside plain `memsetGhostHook` via its
   `hookMemset` fallback branch.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrapRet

open Arm64 ProofLib
open VerifiedLibraries.Mallocng (mallocngBlockProg)
open VerifiedLibraries.Musl (memsetWordsSym)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre linkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks (
  ActiveF3CallPre f3LinkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  mallocngBlockProg21_externAt_none mallocngBlockProg21_hasWords
  memsetSpecK memsetWordsSym_length
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (
  keepCoversBlk21_keepMemsetBlk21 keepMemsetBlk21
  memsetGhostHook memsetGhostHookK
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplays (
  mallocngBlockProg21_code_length
)

/-! ## 0. Re-Exported `Blk21TrapHook` & `Blk21TrapInv` Aliases

`Blk21TrapHook` and `Blk21TrapInv` are defined once in `HooksDehook/MemsetLrTrap.lean` (`@[expose]`)
and aliased here as `abbrev`s so `MemsetLrTrap.Blk21TrapHook` and `MemsetLrTrapRet.Blk21TrapHook`
are definitionally (`rfl`) identical. -/

/-- Alias of `MemsetLrTrap.Blk21TrapHook`: on any `.Running` state `w` with `w.readReg64 .lr = L`,
    `f w` either transitions to `.Exception _` or stays `.Running` at `pc = L` with `lr = L`. -/
abbrev Blk21TrapHook : BitVec 64 → (State → State) → Prop :=
  LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrap.Blk21TrapHook

/-- Alias of `MemsetLrTrap.Blk21TrapInv`: closed-trap invariant on `blk21` (`260` B at
    `mmpl.base 21`) with pinned `lr = L`. -/
abbrev Blk21TrapInv : Obj.MultiPlacement → BitVec 64 → State → Prop :=
  LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrap.Blk21TrapInv

theorem blk21TrapHook_hookMemset (L : BitVec 64) : Blk21TrapHook L hookMemset :=
  LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrap.blk21TrapHook_hookMemset L

theorem blk21TrapHook_memsetGhostHook
    {keep : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (hkeepL : keep L = true) :
    Blk21TrapHook L (memsetGhostHook keep P_real P_sub entryTarget) :=
  LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrap.blk21TrapHook_memsetGhostHook
    P_real P_sub entryTarget hkeepL

theorem blk21TrapHook_memsetGhostHookK
    {keep : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (hkeepL : keep L = true) :
    Blk21TrapHook L (memsetGhostHookK keep P_real P_sub entryTarget) :=
  LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrap.blk21TrapHook_memsetGhostHookK
    P_real P_sub entryTarget hkeepL

/-! ## 1. `(A2)` `Blk21TrapHook` Instances for K-Narrowed & Plain Ghosts -/

/-- Generic `.Exception`-branch `Blk21TrapHook` constructor: any hook `f` that faults with
    `.Exception _` whenever `keep (w.readReg64 .lr) = true` satisfies `Blk21TrapHook L f` for every
    `L` with `keep L = true`. -/
theorem blk21TrapHook_of_exception_on_keepLr
    {keep : BitVec 64 → Bool} {L : BitVec 64} {f : State → State}
    (hkeepL : keep L = true)
    (hex_of_keep : ∀ w : State, keep (w.readReg64 .lr) = true →
      ∃ msg, (f w).status = .Exception msg) :
    Blk21TrapHook L f := by
  intro w _ hlr
  exact Or.inl (hex_of_keep w (hlr ▸ hkeepL))

/-- Any `linkedCallHook` whose `spec.pre` implies `keep (w.readReg64 .lr) = false` satisfies
    `Blk21TrapHook L` whenever `keep L = true` (via the `¬ ActiveRealPre` `.Exception` branch). -/
theorem blk21TrapHook_linkedCallHook_of_pre_keepFalse {α : Type}
    {keep keep' : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (spec : Spec α) (fallback : State → State)
    (hpre_lr : ∀ (x : α) (R : SepProp) (w : State),
      (w.mem ⊨ spec.pre x w ∗ R) → keep (w.readReg64 .lr) = false)
    (hkeepL : keep L = true) :
    Blk21TrapHook L (linkedCallHook keep' P_real P_sub entryTarget spec fallback) := by
  refine blk21TrapHook_of_exception_on_keepLr hkeepL fun w hkw => ?_
  classical
  have hnAct : ¬ ActiveRealPre spec w := by
    rintro ⟨_, _, x, R, hpre⟩
    have hfalse := hpre_lr x R w hpre
    rw [hkw] at hfalse
    exact Bool.noConfusion hfalse
  refine ⟨"ghost-hook precondition violated", ?_⟩
  unfold linkedCallHook
  simp [hnAct]

/-- Every `memsetSpecK keep spec`-narrowed `linkedCallHook` with `keep ⊇ keepMemsetBlk21 mmpl`
    satisfies `∀ L, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L (...)`. -/
theorem blk21TrapHook_linkedCallHook_memsetSpecK {α : Type}
    {mmpl : Obj.MultiPlacement} {keep keep' : BitVec 64 → Bool}
    (hcover : ∀ a, keepMemsetBlk21 mmpl a = true → keep a = true)
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (spec : Spec α) (fallback : State → State) :
    ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true →
      Blk21TrapHook L
        (linkedCallHook keep' P_real P_sub entryTarget (memsetSpecK keep spec) fallback) := by
  intro L hL
  refine blk21TrapHook_linkedCallHook_of_pre_keepFalse P_real P_sub entryTarget
    (memsetSpecK keep spec) fallback (fun x R w hpre => ?_) (hcover L hL)
  dsimp only [memsetSpecK] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.1

/-- Any `f3LinkedCallHook` whose `(specOf γ tp).pre` implies `keep (w.readReg64 .lr) = false`
    (covering **both** `h2k_withKeepLrFalse keep` and `h2k_withKeepLrAndFds keep` across all 7
    K-route ghosts in `h2k_ghFixedK`) satisfies `Blk21TrapHook L` whenever `keep L = true`. -/
theorem blk21TrapHook_f3LinkedCallHook_of_pre_keepFalse {α : Type}
    {keep keep' : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (specOf : GhostName → BitVec 64 → Spec α) (fallback : State → State)
    (hpre_lr : ∀ (γ : GhostName) (tp : BitVec 64) (x : α) (R : SepProp) (w : State),
      (w.mem ⊨ (specOf γ tp).pre x w ∗ R) → keep (w.readReg64 .lr) = false)
    (hkeepL : keep L = true) :
    Blk21TrapHook L (f3LinkedCallHook keep' P_real P_sub entryTarget specOf fallback) := by
  refine blk21TrapHook_of_exception_on_keepLr hkeepL fun w hkw => ?_
  classical
  have hnAct : ¬ ActiveF3CallPre specOf w := by
    rintro ⟨_, _, γ, tp, x, R, hpre⟩
    have hfalse := hpre_lr γ tp x R w hpre
    rw [hkw] at hfalse
    exact Bool.noConfusion hfalse
  refine ⟨"ghost-hook precondition violated", ?_⟩
  unfold f3LinkedCallHook
  simp [hnAct]

/-- Every `memsetSpecK keep`-narrowed `f3LinkedCallHook` (`rfl`-equal to `h2k_withKeepLrFalse keep`)
    with `keep ⊇ keepMemsetBlk21 mmpl` satisfies
    `∀ L, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L (...)`. -/
theorem blk21TrapHook_f3LinkedCallHook_memsetSpecK {α : Type}
    {mmpl : Obj.MultiPlacement} {keep keep' : BitVec 64 → Bool}
    (hcover : ∀ a, keepMemsetBlk21 mmpl a = true → keep a = true)
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (specOf : GhostName → BitVec 64 → Spec α) (fallback : State → State) :
    ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true →
      Blk21TrapHook L
        (f3LinkedCallHook keep' P_real P_sub entryTarget
          (fun γ tp => memsetSpecK keep (specOf γ tp)) fallback) := by
  intro L hL
  refine blk21TrapHook_f3LinkedCallHook_of_pre_keepFalse P_real P_sub entryTarget
    (fun γ tp => memsetSpecK keep (specOf γ tp)) fallback
    (fun γ tp x R w hpre => ?_) (hcover L hL)
  dsimp only [memsetSpecK] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.1

/-- Every `(⌜keep (w.readReg64 .lr) = false ∧ P w⌝ ∗ ...)`-narrowed `f3LinkedCallHook` (`rfl`-equal
    to `h2k_withKeepLrAndFds keep` when `P w := FdsGe3Closed w.fs`) with
    `keep ⊇ keepMemsetBlk21 mmpl` satisfies
    `∀ L, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L (...)`. -/
theorem blk21TrapHook_f3LinkedCallHook_keepAnd {α : Type}
    {mmpl : Obj.MultiPlacement} {keep keep' : BitVec 64 → Bool}
    (hcover : ∀ a, keepMemsetBlk21 mmpl a = true → keep a = true)
    (P : State → Prop)
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (specOf : GhostName → BitVec 64 → Spec α) (fallback : State → State) :
    ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true →
      Blk21TrapHook L
        (f3LinkedCallHook keep' P_real P_sub entryTarget
          (fun γ tp =>
            { (specOf γ tp) with
              pre := fun x s =>
                ⌜keep (s.readReg64 .lr) = false ∧ P s⌝ ∗ (specOf γ tp).pre x s })
          fallback) := by
  intro L hL
  refine blk21TrapHook_f3LinkedCallHook_of_pre_keepFalse P_real P_sub entryTarget _ fallback
    (fun γ tp x R w hpre => ?_) (hcover L hL)
  dsimp only [] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.1.1

/-- Plain `memsetGhostHook keep P_real P_sub entryTarget` with `keep ⊇ keepMemsetBlk21 mmpl`
    satisfies `∀ L, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L (...)` via its `hookMemset`
    fallback / `¬ ActiveRealPre` `.Exception` split. -/
theorem blk21TrapHook_memsetGhostHook_of_cover
    {mmpl : Obj.MultiPlacement} {keep : BitVec 64 → Bool}
    (hcover : ∀ a, keepMemsetBlk21 mmpl a = true → keep a = true)
    (P_real P_sub : Program) (entryTarget : BitVec 64) :
    ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true →
      Blk21TrapHook L (memsetGhostHook keep P_real P_sub entryTarget) :=
  fun L hL => blk21TrapHook_memsetGhostHook P_real P_sub entryTarget (hcover L hL)

/-! ## 2. `(A1)` + `(A2)` Generalized Closed-Trap Impossibility & Call-Point `lr = false` -/

private def isBlk21SafeInstr (off : Nat) (inst : Instr) : Bool :=
  match inst with
  | .ret rn => decide (rn = .lr)
  | .nop => decide (off + 4 < 260)
  | .bCond _ relOff =>
    decide (off + 4 < 260) && decide ((BitVec.ofNat 64 off + relOff).toNat < 260)
  | .cbz _ _ _ relOff =>
    decide (off + 4 < 260) && decide ((BitVec.ofNat 64 off + relOff).toNat < 260)
  | .tbz _ _ _ _ relOff =>
    decide (off + 4 < 260) && decide ((BitVec.ofNat 64 off + relOff).toNat < 260)
  | .addSubImm _ _ rd _ _ _ => decide (off + 4 < 260) && decide (rd ≠ .lr)
  | .addSubShift _ _ rd _ _ _ _ => decide (off + 4 < 260) && decide (rd ≠ .lr)
  | .logicalImm _ _ rd _ _ => decide (off + 4 < 260) && decide (rd ≠ .lr)
  | .bitfield _ _ rd _ _ _ => decide (off + 4 < 260) && decide (rd ≠ .lr)
  | .condCompareImm _ _ _ _ _ _ => decide (off + 4 < 260)
  | .str _ _ addr => decide (off + 4 < 260) && decide (addr.baseReg ≠ .lr)
  | .strSimd _ _ addr => decide (off + 4 < 260) && decide (addr.baseReg ≠ .lr)
  | .stpSimd _ _ _ addr => decide (off + 4 < 260) && decide (addr.baseReg ≠ .lr)
  | .simdInsDup _ _ _ _ _ rd => decide (off + 4 < 260) && decide (Reg.fromZRBits rd ≠ .lr)
  | .sysReg isRead sysreg rt =>
    decide (off + 4 < 260) && isRead && decide (sysreg = 0x5807#15) && decide (rt ≠ .lr)
  | .dcZva _ => decide (off + 4 < 260)
  | _ => false

private theorem memsetWords_all_safe :
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

private def Blk21StepOutcome (base : BitVec 64) (s s' : State) : Prop :=
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
    by_cases h31 : idx == 31#5 <;> simp [h31, hne]
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
    SameRunLrPc s (s1.writeVReg128 vt v) := ⟨h.1, h.2.1, h.2.2⟩

private theorem sameRunLrPc_setPState {s s1 : State} (h : SameRunLrPc s s1) (ps : PState) :
    SameRunLrPc s (s1.setPState ps) := ⟨h.1, h.2.1, h.2.2⟩

private theorem sameRunLrPc_optPState {s s1 : State} (h : SameRunLrPc s s1)
    (optPs : Option PState) :
    SameRunLrPc s (match optPs with | some ps => s1.setPState ps | none => s1) := by
  cases optPs <;> [exact h; exact sameRunLrPc_setPState h _]

private theorem sameRunLrPc_setMem {s s1 : State} (h : SameRunLrPc s s1) (m : Memory) :
    SameRunLrPc s (s1.setMem m) := ⟨h.1, h.2.1, h.2.2⟩

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
  cases a <;> cases b <;> cases h; exact ⟨rfl, rfl⟩

private theorem blk21_ite {base : BitVec 64} {s : State} {c : Prop} [inst : Decidable c]
    {t e : State} (ht : Blk21StepOutcome base s t) (he : Blk21StepOutcome base s e) :
    Blk21StepOutcome base s (if c then t else e) :=
  match inst with | isTrue _ => ht | isFalse _ => he

private theorem execInst_of_isBlk21SafeInstr {base : BitVec 64} {off : Nat} {inst : Instr} {s : State}
    (hsafe : isBlk21SafeInstr off inst = true)
    (hrun : s.status = .Running)
    (hpc : s.pc = base + BitVec.ofNat 64 off) :
    Blk21StepOutcome base s (execInst inst s) := by
  cases inst <;> try (unfold isBlk21SafeInstr at hsafe; contradiction)
  case ret rn =>
    unfold isBlk21SafeInstr at hsafe
    have hrn : rn = .lr := of_decide_eq_true hsafe
    subst hrn; exact Or.inr ⟨hrun, rfl, Or.inl rfl⟩
  case nop =>
    unfold isBlk21SafeInstr at hsafe
    exact outcome_of_advancePC hrun hpc (of_decide_eq_true hsafe) (sameRunLrPc_refl s)
  case bCond cond relOff =>
    unfold isBlk21SafeInstr at hsafe
    obtain ⟨hoff0, htgt0⟩ := band_true hsafe
    dsimp only [execInst]
    exact blk21_ite (outcome_of_branchRel hrun hpc (of_decide_eq_true htgt0))
      (outcome_of_advancePC hrun hpc (of_decide_eq_true hoff0) (sameRunLrPc_refl s))
  case cbz w isNonZero rt relOff =>
    unfold isBlk21SafeInstr at hsafe
    obtain ⟨hoff0, htgt0⟩ := band_true hsafe
    dsimp only [execInst]
    exact blk21_ite (outcome_of_branchRel hrun hpc (of_decide_eq_true htgt0))
      (outcome_of_advancePC hrun hpc (of_decide_eq_true hoff0) (sameRunLrPc_refl s))
  case tbz w isNonZero rt bit relOff =>
    unfold isBlk21SafeInstr at hsafe
    obtain ⟨hoff0, htgt0⟩ := band_true hsafe
    dsimp only [execInst]
    exact blk21_ite (outcome_of_branchRel hrun hpc (of_decide_eq_true htgt0))
      (outcome_of_advancePC hrun hpc (of_decide_eq_true hoff0) (sameRunLrPc_refl s))
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
    dsimp only [execInst, execCondCompare]
    exact blk21_ite
      (outcome_of_advancePC hrun hpc hoff (sameRunLrPc_optPState (sameRunLrPc_refl s) _))
      (outcome_of_advancePC hrun hpc hoff (sameRunLrPc_setPState (sameRunLrPc_refl s) _))
  case str sz rt addr =>
    unfold isBlk21SafeInstr at hsafe
    obtain ⟨hoff0, hbr0⟩ := band_true hsafe
    dsimp only [execInst, execStr]
    exact blk21_ite (Or.inl ⟨_, rfl⟩)
      (blk21_ite (Or.inl ⟨_, rfl⟩)
        (outcome_of_advancePC hrun hpc (of_decide_eq_true hoff0)
          (sameRunLrPc_addrWb s (sameRunLrPc_setMem (sameRunLrPc_refl s) _)
            (of_decide_eq_true hbr0))))
  case strSimd sz vt addr =>
    unfold isBlk21SafeInstr at hsafe
    obtain ⟨hoff0, hbr0⟩ := band_true hsafe
    dsimp only [execInst]
    exact blk21_ite (Or.inl ⟨_, rfl⟩)
      (blk21_ite (Or.inl ⟨_, rfl⟩)
        (outcome_of_advancePC hrun hpc (of_decide_eq_true hoff0)
          (sameRunLrPc_addrWb s (sameRunLrPc_setMem (sameRunLrPc_refl s) _)
            (of_decide_eq_true hbr0))))
  case stpSimd sz vt1 vt2 addr =>
    unfold isBlk21SafeInstr at hsafe
    obtain ⟨hoff0, hbr0⟩ := band_true hsafe
    have hoff := of_decide_eq_true hoff0
    have hbr := of_decide_eq_true hbr0
    clear hsafe hoff0 hbr0
    cases sz <;> dsimp only [execInst] <;>
      exact blk21_ite (Or.inl ⟨_, rfl⟩)
        (blk21_ite (Or.inl ⟨_, rfl⟩)
          (outcome_of_advancePC hrun hpc hoff
            (sameRunLrPc_addrWb s (sameRunLrPc_setMem (sameRunLrPc_refl s) _) hbr)))
  case simdInsDup q op imm5 imm4 rn rd =>
    unfold isBlk21SafeInstr at hsafe
    obtain ⟨hoff0, hrd0⟩ := band_true hsafe
    have hoff := of_decide_eq_true hoff0
    have hrd := of_decide_eq_true hrd0
    clear hsafe hoff0 hrd0
    dsimp only [execInst]
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
    dsimp only [execInst]
    exact outcome_of_advancePC hrun hpc hoff (sameRunLrPc_writeReg64 (sameRunLrPc_refl s) hrt 4#64)
  case dcZva rt =>
    unfold isBlk21SafeInstr at hsafe
    have hoff := of_decide_eq_true hsafe
    dsimp only [execInst]
    exact blk21_ite (Or.inl ⟨_, rfl⟩)
      (outcome_of_advancePC hrun hpc hoff (sameRunLrPc_setMem (sameRunLrPc_refl s) _))
private theorem fetchMem_blk21_safe
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
    | none => rw [hdec] at hall_k; contradiction
    | some inst' =>
      rw [hdec] at hall_k; dsimp only [] at hall_k
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
        rw [hext_sub, hbase_sub, hrw]; exact hdec
      have hfm_sub : P_sub.fetchMem m pc = some inst' := P_sub.fetchMem_of_fetch hL hfetch_sub
      have hfm_eq : P_ghost.fetchMem m pc = P_sub.fetchMem m pc :=
        ProofLib.Variant.fetchMem_eq_of_externAt_eq (heg.trans hext_sub.symm)
      rw [hfm_eq, hfm_sub] at hfm
      cases hfm
      exact ⟨off, hoff_lt, hpc_eq, hoff_k ▸ hall_k⟩

/-- **`(A1)` Generalized closed-trap impossibility (`blk21_trap_impossible_ret`):**
    Replaces `sf.status ≠ .Running` with
    `hrun_sf' : sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false`,
    covering `.Exited _`, `.Panicked`, `.OutOfMemory`, `.Signaled _`, **and** subroutine `Returned`
    (`sf.status = .Running ∧ sf.pc = s0.readReg64 .lr`) whenever
    `keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false`. -/
theorem blk21_trap_impossible_ret
    {P_ghost : Program} {mmpl : Obj.MultiPlacement} {L : BitVec 64}
    (hL_in : keepMemsetBlk21 mmpl L = true)
    (hblk21_ext : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ Blk21TrapHook L f)
    {w sf : State}
    (hsteps : Steps P_ghost w sf)
    (hrun_sf' : sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted)
    (hInv : Blk21TrapInv mmpl L w) :
    False := by
  induction hsteps with
  | refl s =>
    have hfalse := hrun_sf' hInv.1
    rw [hInv.2.1] at hfalse
    exact Bool.noConfusion hfalse
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
        · exact ih hrun_sf' hnoex_sf hnhalt_sf ⟨hrun2, hpc2 ▸ hL_in, hlr2, hCode2⟩
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
        exact ih hrun_sf' hnoex_sf hnhalt_sf ⟨hrun2, hkeep2, hlr_eq.trans hlr1, hCode2⟩

/-- **Post-hook continuation `lr = false` (`blk21_lr_trap_after_hook_ret`, `(A1)` + `(A2)`):**
    Given the post-hook continuation `hrest : Steps P_ghost (f_u u) sf` (the exact continuation
    provided in `GhostExternReplaysOn`), requires **only** `hrun_sf'`, `hnoex_sf`, and `hnhalt_sf`
    on `sf` (no extra assumption on `sf.pc` when `u = sf`, because `f_u u` has already stepped into
    `Blk21TrapInv` or `.Exception`). -/
theorem blk21_lr_trap_after_hook_ret
    {P_ghost : Program} {mmpl : Obj.MultiPlacement} {f_u : State → State}
    {u sf : State}
    (htrap_u : ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f_u)
    (hblk21_ext : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hCode_fu : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded (f_u u).mem)
    (hrest : Steps P_ghost (f_u u) sf)
    (hrun_u : u.status = .Running)
    (hrun_sf' : sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepMemsetBlk21 mmpl (u.readReg64 .lr) = false := by
  cases hkeepL : keepMemsetBlk21 mmpl (u.readReg64 .lr) with
  | false => rfl
  | true =>
    exfalso
    let L := u.readReg64 .lr
    have hblk21_L : ∀ pc, keepMemsetBlk21 mmpl pc = true →
        P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ Blk21TrapHook L f := by
      intro pc hkp
      rcases hblk21_ext pc hkp with hnone | ⟨f, hf, htf⟩
      · exact Or.inl hnone
      · exact Or.inr ⟨f, hf, htf L hkeepL⟩
    rcases htrap_u L hkeepL u hrun_u rfl with ⟨msg, hex⟩ | ⟨hrun_v, hpc_v, hlr_v⟩
    · have heq := ProofLib.Variant.Steps.eq_of_not_running hrest
        (by rw [hex]; nofun)
      have hst : sf.status = .Exception msg := by rw [heq, hex]
      exact hnoex_sf msg hst
    · exact blk21_trap_impossible_ret hkeepL hblk21_L hrest hrun_sf' hnoex_sf hnhalt_sf
        ⟨hrun_v, hpc_v ▸ hkeepL, hlr_v, hCode_fu⟩

/-- **Call-point `lr = false` on `Steps P_ghost u sf` (`blk21_lr_trap_at_call_ret`, `(A1)` + `(A2)`):**
    At `u = sf` (`Steps.refl`), `sf` has not executed `f_u`, so `hu_ne_sf` rules out stopping right
    on the unexecuted ghost stub `u.pc` while `.Running` (vacuously true whenever
    `sf.status ≠ .Running`, or when `sf.pc` is a non-hooked caller return address). -/
theorem blk21_lr_trap_at_call_ret
    {P_ghost : Program} {mmpl : Obj.MultiPlacement} {f_u : State → State}
    {u sf : State}
    (htrap_u : ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f_u)
    (hblk21_ext : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hext_u : P_ghost.externAt? u.pc = some f_u)
    (hCode_u : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded u.mem)
    (hsteps_u_sf : Steps P_ghost u sf)
    (hrun_u : u.status = .Running)
    (hu_ne_sf : sf.status = .Running → sf.pc ≠ u.pc)
    (hrun_sf' : sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepMemsetBlk21 mmpl (u.readReg64 .lr) = false := by
  cases hsteps_u_sf with
  | refl =>
    exact False.elim (hu_ne_sf hrun_u rfl)
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
      exact False.elim (hnoex_sf _ hst)
    | @extern f _ hext _ _ =>
      rw [hext_u] at hext
      injection hext with hfeq
      subst hfeq
      exact blk21_lr_trap_after_hook_ret htrap_u hblk21_ext hCode_v hrest
        hrun_u hrun_sf' hnoex_sf hnhalt_sf

/-- **`(A1)` + `(A2)` Global `hlr_calls` Theorem (`blk21_lr_trap_false_ret`):**
    Simultaneously generalizes:
    - `(A1)`: `hrun_sf' : sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false` (plus
      `hret_no_mis : sf.status = .Running → P_ghost.externAt? sf.pc = P_real.externAt? sf.pc` to
      rule out stopping at `u = sf` on an unexecuted mismatched stub; both are vacuous for every
      non-`.Running` terminal status `Exited` / `Panicked` / `OutOfMemory` / `Signaled`), and
    - `(A2)`: per-PC existential `hmis_trap` allowing a mixed ghost table (e.g. narrow `memset`
      alongside the 7 K-narrowed F3 ghosts). -/
theorem blk21_lr_trap_false_ret
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement}
    (hblk21_ext : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hmis_trap : ∀ pc, P_ghost.externAt? pc ≠ P_real.externAt? pc →
      ∃ f, P_ghost.externAt? pc = some f ∧
        ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    {s0 sf : State}
    (hc_codeLoaded : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded s0.mem)
    (hrun_sf' : sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false)
    (hret_no_mis : sf.status = .Running → P_ghost.externAt? sf.pc = P_real.externAt? sf.pc)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemsetBlk21 mmpl (u.readReg64 .lr) = false := by
  intro u hsteps_s0_u hsteps_u_sf hrun_u hmis
  obtain ⟨f_u, hext_u, htrap_u⟩ := hmis_trap u.pc hmis
  exact blk21_lr_trap_at_call_ret htrap_u hblk21_ext hext_u
    (hsteps_s0_u.codeLoaded hc_codeLoaded)
    hsteps_u_sf hrun_u
    (fun hrun_sf heq_pc => hmis (heq_pc ▸ hret_no_mis hrun_sf))
    hrun_sf' hnoex_sf hnhalt_sf

/-- Non-`.Running` specialization of `blk21_lr_trap_false_ret` (covers `.Exited _`, `.Panicked`,
    `.OutOfMemory`, and `.Signaled _` with `hrun_sf'` and `hret_no_mis` discharged vacuously). -/
theorem blk21_lr_trap_false_mixed_nonRunning
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement}
    (hblk21_ext : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hmis_trap : ∀ pc, P_ghost.externAt? pc ≠ P_real.externAt? pc →
      ∃ f, P_ghost.externAt? pc = some f ∧
        ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    {s0 sf : State}
    (hc_codeLoaded : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded s0.mem)
    (hrun_sf : sf.status ≠ .Running)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemsetBlk21 mmpl (u.readReg64 .lr) = false :=
  blk21_lr_trap_false_ret hblk21_ext hmis_trap hc_codeLoaded
    (fun hr => False.elim (hrun_sf hr))
    (fun hr => False.elim (hrun_sf hr))
    hnoex_sf hnhalt_sf

/-- Mixed-pass `(A2)` `Returned`-outcome specialization of `blk21_lr_trap_false_ret`:
    when `sf.status = .Running` at `sf.pc = s0.readReg64 .lr` with
    `keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false` and no extern mismatch at `s0.readReg64 .lr`,
    every mismatched call along `s0 →* u →* sf` has `keepMemsetBlk21 mmpl (u.readReg64 .lr) = false`
    (`hnoex_sf` and `hnhalt_sf` are discharged automatically from `hrun_sf`). -/
theorem blk21_lr_trap_false_mixed_returned
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement}
    (hblk21_ext : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hmis_trap : ∀ pc, P_ghost.externAt? pc ≠ P_real.externAt? pc →
      ∃ f, P_ghost.externAt? pc = some f ∧
        ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    {s0 sf : State}
    (hc_codeLoaded : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded s0.mem)
    (hrun_sf : sf.status = .Running)
    (hpc_sf : sf.pc = s0.readReg64 .lr)
    (hlr_s0 : keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false)
    (hlr_no_mis : P_ghost.externAt? (s0.readReg64 .lr) = P_real.externAt? (s0.readReg64 .lr)) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemsetBlk21 mmpl (u.readReg64 .lr) = false :=
  blk21_lr_trap_false_ret hblk21_ext hmis_trap hc_codeLoaded
    (fun _ => by rw [hpc_sf]; exact hlr_s0)
    (fun _ => by rw [hpc_sf]; exact hlr_no_mis)
    (fun _ h => by rw [hrun_sf] at h; cases h)
    (fun h => by rw [hrun_sf] at h; cases h)

/-- Single-stub `Returned`-outcome specialization of `blk21_lr_trap_false_ret`:
    given `sf.status = .Running`, `sf.pc = s0.readReg64 .lr`,
    `keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false`, and `s0.readReg64 .lr ≠ stubPc`,
    every mismatched call along `s0 →* u →* sf` has `keepMemsetBlk21 mmpl (u.readReg64 .lr) = false`.
    *Applicability note (`rev_c6` F2):* `hmis_stub` requires a single ghost/real mismatch (`stubPc`),
    covering a `memset`-only pass rather than the 8-row K CLI pass (`h2k_ghFixedK` + `memset`). For
    the multi-row CLI pass, use `blk21_lr_trap_false_mixed_returned` or the per-stub
    `ElfSlicesPqOomH2KMemset.h2k_memsetGhostHookNarrow_stub_replayOn_cli617` inside K's per-PC
    replay. -/
theorem blk21_lr_trap_false_single_returned
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement}
    {stubPc : BitVec 64} {f_stub : State → State}
    (hblk21_ext : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hmis_stub : ∀ pc, P_ghost.externAt? pc ≠ P_real.externAt? pc → pc = stubPc)
    (hext_stub : P_ghost.externAt? stubPc = some f_stub)
    (htrap_stub : ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded s0.mem)
    (hrun_sf : sf.status = .Running)
    (hpc_sf : sf.pc = s0.readReg64 .lr)
    (hlr_s0 : keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false)
    (hlr_ne_stub : s0.readReg64 .lr ≠ stubPc) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemsetBlk21 mmpl (u.readReg64 .lr) = false :=
  blk21_lr_trap_false_mixed_returned hblk21_ext
    (fun pc hmis => ⟨f_stub, hmis_stub pc hmis ▸ hext_stub, htrap_stub⟩)
    hc_codeLoaded hrun_sf hpc_sf hlr_s0
    (Classical.byContradiction fun hne => hlr_ne_stub (hmis_stub _ hne))

/-- `memsetGhostHook` `Returned`-outcome specialization (`blk21_lr_trap_false_memset_returned`):
    discharges `Blk21TrapHook` automatically for
    `memsetGhostHook (keepMemsetBlk21 mmpl) P_hookReal P_sub entryTarget`,
    leaving only `keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false` and `s0.readReg64 .lr ≠ stubPc`
    for the `Returned` terminal state (`sf.status = .Running`, `sf.pc = s0.readReg64 .lr`).
    *Applicability note (`rev_c6` F2):* `hmis_stub` requires a single ghost/real mismatch
    (`memset`-only pass, not the 8-row K CLI pass; for the 8-row CLI pass use
    `blk21_lr_trap_false_mixed_returned` or
    `ElfSlicesPqOomH2KMemset.h2k_memsetGhostHookNarrow_stub_replayOn_cli617`). -/
theorem blk21_lr_trap_false_memset_returned
    {P_ghost P_real P_hookReal P_sub : Program} {mmpl : Obj.MultiPlacement}
    {stubPc entryTarget : BitVec 64}
    (hblk21_ext : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hmis_stub : ∀ pc, P_ghost.externAt? pc ≠ P_real.externAt? pc → pc = stubPc)
    (hext_stub : P_ghost.externAt? stubPc =
      some (memsetGhostHook (keepMemsetBlk21 mmpl) P_hookReal P_sub entryTarget))
    {s0 sf : State}
    (hc_codeLoaded : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded s0.mem)
    (hrun_sf : sf.status = .Running)
    (hpc_sf : sf.pc = s0.readReg64 .lr)
    (hlr_s0 : keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false)
    (hlr_ne_stub : s0.readReg64 .lr ≠ stubPc) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemsetBlk21 mmpl (u.readReg64 .lr) = false :=
  blk21_lr_trap_false_single_returned hblk21_ext hmis_stub hext_stub
    (fun _ hL => blk21TrapHook_memsetGhostHook P_hookReal P_sub entryTarget hL)
    hc_codeLoaded hrun_sf hpc_sf hlr_s0 hlr_ne_stub

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrapRet
