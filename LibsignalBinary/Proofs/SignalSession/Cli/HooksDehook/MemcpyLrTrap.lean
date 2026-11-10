/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostK -- proof-setup: allow-public-import
import ProofLib.OpcodeExclusion
import ProofLib.ProgramReflection.Variant.TrapTransfer

/-!
# Closed-Trap Discharge of `keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false` (`HooksDehook.MemcpyLrTrap`)

Global closed-trap proof over `mallocngLib` block 20 (`memcpySymWords`, `99` instructions = `396`
bytes) discharging the per-call hypothesis `keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false` **once,
globally, with zero per-caller `LsRetAddr624` or `bl`-at-call-site assumptions** (covering all 6
tail-call `b memcpy` sites in `.img.text` as well as `bl memcpy` sites), for **arbitrary** register
and memory contents.

## Proof Architecture & Generalizations (`08:18Z` Addendum)
1. **Syntactic 99-instruction trap classifier & kernel census (`isBlk20SafeInstr`, `memcpyWords_all_safe`)**:
   Kernel-verified (`decide +kernel`) check that all `99` words of `memcpySymWords` (`[0, 396)`):
   - contain **7** `ret .lr`, **10** internal conditional branches (`bCond`/`cbz`/`tbz` with target
     in `[0, 396)`), **0** `bl`/`blr`/`br`/`b`/`svc`/`brk`, and **0** writes to `Reg.lr` (`x30`),
   - have sequential fallthrough `4 * k + 4 < 396` on every instruction that can `advancePC`.
2. **Arbitrary-state instruction step (`execInst_of_isBlk20SafeInstr`) & `fetchMem` bridge (`fetchMem_blk20_safe`)**:
   For any `.Running` state `s` at `s.pc = base + off` (`off < 396`) with arbitrary registers and
   memory (including unmapped/garbage `x0`/`x1`/`x2`/`sp`), `execInst inst s` either faults to
   `.Exception _` or stays `.Running` with unchanged `lr` and `pc ∈ {lr} ∪ [base, base + 396)`.
   Nothing in the step or trap lemma assumes `bl` at the call site: only `keepMemcpyBlk20 mmpl lr`
   is tracked, so tail-called `b memcpy` sites are covered identically to `bl memcpy` sites.
3. **General terminal & multi-ghost mismatch hypotheses (`blk20_trap_impossible`, `blk20_lr_trap_of_step`, `blk20_lr_trap_false_gen`)**:
   - **Terminal hypothesis (`hrun_sf`, `hnoex_sf`, `hnhalt_sf`)**: requires only
     `sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false`, `∀ msg, sf.status ≠ .Exception msg`,
     and `sf.status ≠ .Halted` (covering `.Exited _`, `.Panicked`, `.OutOfMemory`, `.Signaled _`,
     and subroutine `Returned` outcomes alike).
   - **Mismatch hypothesis (`hmis`)**: requires only
     `∀ pc, P_ghost.externAt? pc ≠ P_real.externAt? pc → ∃ f, P_ghost.externAt? pc = some f ∧ ∀ L, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f`,
     covering multi-ghost `K`-route programs (7 allocator/stdin `K`-ghosts + `memset` + `memcpy`)
     via `blk20TrapHook_linkedCallHook_of_not_pre` / `blk20TrapHook_linkedCallHook`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrap

open Arm64 ProofLib
open Arm64.Process (pureWordsProg)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngBlockProg)
open VerifiedLibraries.Musl (memcpySymWords)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre ActiveRealRun keepFsTrace linkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode (
  masterMemcpySpec
  mallocng_blk20_code_length mallocngLib_blockLib20_text
  memcpySymWords_length
  mallocngBlockProg20_hasWords mallocngBlockProg20_externAt_none
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost (
  memcpyGhostHook memcpyGhostHookK
  keepMemcpyBlk20 KeepCoversBlk20
  keepCoversBlk20_keepMemcpyBlk20
  keepFsTrace_hookMemcpy_eq
  memcpyGhostHook_of_keepLr_true memcpyGhostHookK_of_keepLr_true
)

/-! ## 1. Syntactic 99-Instruction Trap Classifier, Kernel Census & Arbitrary-State Step Lemma -/

/-- Syntactic safety classifier for an instruction `inst` at byte offset `off` inside `blk20`
    (`396` bytes = `99` words):
    - `inst` is never `svc`/`brk`/`bl`/`blr`/`br`/`b`,
    - `inst` never writes `Reg.lr` (`x30`), including GPR load destinations and address writebacks,
    - `.ret rn` has `rn = .lr`,
    - sequential fallthrough (`advancePC`) has `off + 4 < 396`, and
    - PC-relative branch offsets `relOff` satisfy `(BitVec.ofNat 64 off + relOff).toNat < 396`. -/
def isBlk20SafeInstr (off : Nat) (inst : Instr) : Bool :=
  match inst with
  | .ret rn => decide (rn = .lr)
  | .nop => decide (off + 4 < 396)
  | .bCond _ relOff =>
    decide (off + 4 < 396) && decide ((BitVec.ofNat 64 off + relOff).toNat < 396)
  | .cbz _ _ _ relOff =>
    decide (off + 4 < 396) && decide ((BitVec.ofNat 64 off + relOff).toNat < 396)
  | .tbz _ _ _ _ relOff =>
    decide (off + 4 < 396) && decide ((BitVec.ofNat 64 off + relOff).toNat < 396)
  | .addSubImm _ _ rd _ _ _ =>
    decide (off + 4 < 396) && decide (rd ≠ .lr)
  | .addSubShift _ _ rd _ _ _ _ =>
    decide (off + 4 < 396) && decide (rd ≠ .lr)
  | .logicalImm _ _ rd _ _ =>
    decide (off + 4 < 396) && decide (rd ≠ .lr)
  | .bitfield _ _ rd _ _ _ =>
    decide (off + 4 < 396) && decide (rd ≠ .lr)
  | .ldr _ _ _ rt addr =>
    decide (off + 4 < 396) && decide (rt ≠ .lr) && decide (addr.baseReg ≠ .lr)
  | .str _ _ addr =>
    decide (off + 4 < 396) && decide (addr.baseReg ≠ .lr)
  | .ldp _ _ rt1 rt2 addr =>
    decide (off + 4 < 396) && decide (rt1 ≠ .lr) && decide (rt2 ≠ .lr) &&
      decide (addr.baseReg ≠ .lr)
  | .stp _ _ _ addr =>
    decide (off + 4 < 396) && decide (addr.baseReg ≠ .lr)
  | _ => false

theorem memcpyWords_all_safe :
    ((List.range 99).all fun k =>
      match memcpySymWords[k]? with
      | some w =>
        match decode w with
        | some inst => isBlk20SafeInstr (4 * k) inst
        | none => false
      | none => false) = true := by
  decide +kernel

/-- Kernel census: `memcpySymWords` (`blk20`) contains exactly `7` `ret .lr` instructions. -/
theorem memcpyWords_ret_count :
    ((List.range 99).countP fun k =>
      match memcpySymWords[k]? >>= decode with
      | some (.ret .lr) => true
      | _ => false) = 7 := by
  decide +kernel

/-- Kernel census: `memcpySymWords` (`blk20`) contains exactly `10` internal conditional branches
    (`bCond`, `cbz`, `tbz`). -/
theorem memcpyWords_condBranch_count :
    ((List.range 99).countP fun k =>
      match memcpySymWords[k]? >>= decode with
      | some (.bCond _ _) | some (.cbz _ _ _ _) | some (.tbz _ _ _ _ _) => true
      | _ => false) = 10 := by
  decide +kernel

/-- Kernel census: `memcpySymWords` (`blk20`) contains `0` `bl`/`blr`/`br`/`b`/`system` (`svc`/`brk`)
    instructions. -/
theorem memcpyWords_callOrUncondBranchOrSystem_count :
    ((List.range 99).countP fun k =>
      match memcpySymWords[k]? >>= decode with
      | some (.bl _) | some (.blr _) | some (.br _) | some (.b _) | some (.system _ _) => true
      | _ => false) = 0 := by
  decide +kernel

private theorem isBlk20SafeInstr_not_isSvc0 {off : Nat} {inst : Instr}
    (h : isBlk20SafeInstr off inst = true) :
    inst.isSvc0 = false := by
  cases inst <;> simp [isBlk20SafeInstr, Instr.isSvc0] at h ⊢

/-- Single-instruction outcome for an instruction inside `blk20` (`396` B) on arbitrary state `s`:
    either faults with `.Exception msg`, or remains `.Running` with unchanged `lr` and `pc`
    equal to `s.readReg64 .lr` or `base + off'` (`off' < 396`). -/
def Blk20StepOutcome (base : BitVec 64) (s s' : State) : Prop :=
  (∃ msg, s'.status = .Exception msg) ∨
  (s'.status = .Running ∧
   s'.readReg64 .lr = s.readReg64 .lr ∧
   (s'.pc = s.readReg64 .lr ∨ ∃ off' : Nat, off' < 396 ∧ s'.pc = base + BitVec.ofNat 64 off'))

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
    (hoff : off + 4 < 396)
    (h1 : SameRunLrPc s s1) :
    Blk20StepOutcome base s s1.advancePC := by
  refine Or.inr ⟨h1.1.trans hrun, h1.2.1, Or.inr ⟨off + 4, hoff, ?_⟩⟩
  change s1.pc + 4#64 = base + BitVec.ofNat 64 (off + 4)
  rw [h1.2.2, hpc, BitVec.add_assoc, ← BitVec.ofNat_add]

private theorem outcome_of_branchRel {base : BitVec 64} {off : Nat} {relOff : BitVec 64} {s : State}
    (hrun : s.status = .Running)
    (hpc : s.pc = base + BitVec.ofNat 64 off)
    (htgt : (BitVec.ofNat 64 off + relOff).toNat < 396) :
    Blk20StepOutcome base s (s.setPC (s.pc + relOff)) := by
  refine Or.inr ⟨hrun, rfl, Or.inr ⟨(BitVec.ofNat 64 off + relOff).toNat, htgt, ?_⟩⟩
  change s.pc + relOff = base + BitVec.ofNat 64 (BitVec.ofNat 64 off + relOff).toNat
  rw [hpc, BitVec.add_assoc, BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem band_true {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> cases h
  exact ⟨rfl, rfl⟩

private theorem blk20_ite {base : BitVec 64} {s : State} {c : Prop} [inst : Decidable c]
    {t e : State} (ht : Blk20StepOutcome base s t) (he : Blk20StepOutcome base s e) :
    Blk20StepOutcome base s (if c then t else e) :=
  match inst with
  | isTrue _ => ht
  | isFalse _ => he

/-- Any `isBlk20SafeInstr off inst = true` instruction executed from `s.status = .Running` and
    `s.pc = base + BitVec.ofNat 64 off` satisfies `Blk20StepOutcome base s (execInst inst s)`, for
    **arbitrary** register and memory contents (zero assumptions on caller `bl`, `sp`, or memory). -/
theorem execInst_of_isBlk20SafeInstr {base : BitVec 64} {off : Nat} {inst : Instr} {s : State}
    (hsafe : isBlk20SafeInstr off inst = true)
    (hrun : s.status = .Running)
    (hpc : s.pc = base + BitVec.ofNat 64 off) :
    Blk20StepOutcome base s (execInst inst s) := by
  cases inst <;> try (unfold isBlk20SafeInstr at hsafe; contradiction)
  case ret rn =>
    unfold isBlk20SafeInstr at hsafe
    have hrn : rn = .lr := of_decide_eq_true hsafe
    subst hrn
    exact Or.inr ⟨hrun, rfl, Or.inl rfl⟩
  case nop =>
    unfold isBlk20SafeInstr at hsafe
    exact outcome_of_advancePC hrun hpc (of_decide_eq_true hsafe) (sameRunLrPc_refl s)
  case bCond cond relOff =>
    unfold isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, htgt0⟩ := band_true hsafe
    have hoff := of_decide_eq_true hoff0
    have htgt := of_decide_eq_true htgt0
    change Blk20StepOutcome base s
      (if ConditionHolds cond s.pstate then s.setPC (s.pc + relOff) else s.advancePC)
    split
    · exact outcome_of_branchRel hrun hpc htgt
    · exact outcome_of_advancePC hrun hpc hoff (sameRunLrPc_refl s)
  case cbz w isNonZero rt relOff =>
    unfold isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, htgt0⟩ := band_true hsafe
    have hoff := of_decide_eq_true hoff0
    have htgt := of_decide_eq_true htgt0
    let val := s.readReg w rt
    let c := if isNonZero then (val == 0#64) != true else val == 0#64
    change Blk20StepOutcome base s (if c then s.setPC (s.pc + relOff) else s.advancePC)
    split
    · exact outcome_of_branchRel hrun hpc htgt
    · exact outcome_of_advancePC hrun hpc hoff (sameRunLrPc_refl s)
  case tbz w isNonZero rt bit relOff =>
    unfold isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, htgt0⟩ := band_true hsafe
    have hoff := of_decide_eq_true hoff0
    have htgt := of_decide_eq_true htgt0
    change Blk20StepOutcome base s
      (if (s.readReg64 rt).getLsbD bit == isNonZero then s.setPC (s.pc + relOff) else s.advancePC)
    split
    · exact outcome_of_branchRel hrun hpc htgt
    · exact outcome_of_advancePC hrun hpc hoff (sameRunLrPc_refl s)
  case addSubImm w op rd rn imm12 shift12 =>
    unfold isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, hrd0⟩ := band_true hsafe
    exact outcome_of_advancePC hrun hpc (of_decide_eq_true hoff0)
      (sameRunLrPc_optPState
        (sameRunLrPc_writeReg (sameRunLrPc_refl s) w (of_decide_eq_true hrd0) _) _)
  case addSubShift w op rd rn rm shift amount =>
    unfold isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, hrd0⟩ := band_true hsafe
    exact outcome_of_advancePC hrun hpc (of_decide_eq_true hoff0)
      (sameRunLrPc_optPState
        (sameRunLrPc_writeReg (sameRunLrPc_refl s) w (of_decide_eq_true hrd0) _) _)
  case logicalImm w op rd rn mask =>
    unfold isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, hrd0⟩ := band_true hsafe
    exact outcome_of_advancePC hrun hpc (of_decide_eq_true hoff0)
      (sameRunLrPc_optPState
        (sameRunLrPc_writeReg (sameRunLrPc_refl s) w (of_decide_eq_true hrd0) _) _)
  case bitfield w op rd rn immr imms =>
    unfold isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, hrd0⟩ := band_true hsafe
    exact outcome_of_advancePC hrun hpc (of_decide_eq_true hoff0)
      (sameRunLrPc_writeReg (sameRunLrPc_refl s) w (of_decide_eq_true hrd0) _)
  case ldr w sz signed rt addr =>
    unfold isBlk20SafeInstr at hsafe
    obtain ⟨h12, hbr0⟩ := band_true hsafe
    obtain ⟨hoff0, hrt0⟩ := band_true h12
    have hoff := of_decide_eq_true hoff0
    have hrt := of_decide_eq_true hrt0
    have hbr := of_decide_eq_true hbr0
    change Blk20StepOutcome base s (execLdr w sz signed rt addr s)
    unfold execLdr
    split
    · exact Or.inl ⟨_, rfl⟩
    · dsimp only []
      split
      · exact Or.inl ⟨_, rfl⟩
      · exact outcome_of_advancePC hrun hpc hoff
          (sameRunLrPc_writeReg (sameRunLrPc_addrWb s (sameRunLrPc_refl s) hbr) w hrt _)
  case str sz rt addr =>
    unfold isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, hbr0⟩ := band_true hsafe
    have hoff := of_decide_eq_true hoff0
    have hbr := of_decide_eq_true hbr0
    change Blk20StepOutcome base s (execStr sz rt addr s)
    unfold execStr
    split
    · exact Or.inl ⟨_, rfl⟩
    · dsimp only []
      split
      · exact Or.inl ⟨_, rfl⟩
      · exact outcome_of_advancePC hrun hpc hoff
          (sameRunLrPc_addrWb s (sameRunLrPc_setMem (sameRunLrPc_refl s) _) hbr)
  case ldp w signed rt1 rt2 addr =>
    unfold isBlk20SafeInstr at hsafe
    obtain ⟨h123, hbr0⟩ := band_true hsafe
    obtain ⟨h12, hrt20⟩ := band_true h123
    obtain ⟨hoff0, hrt10⟩ := band_true h12
    have hoff := of_decide_eq_true hoff0
    have hrt1 := of_decide_eq_true hrt10
    have hrt2 := of_decide_eq_true hrt20
    have hbr := of_decide_eq_true hbr0
    change Blk20StepOutcome base s (execLdp w signed rt1 rt2 addr s)
    unfold execLdp
    exact blk20_ite (Or.inl ⟨_, rfl⟩)
      (blk20_ite (Or.inl ⟨_, rfl⟩)
        (outcome_of_advancePC hrun hpc hoff
          (sameRunLrPc_writeReg
            (sameRunLrPc_writeReg (sameRunLrPc_addrWb s (sameRunLrPc_refl s) hbr) _ hrt1 _)
            _ hrt2 _)))
  case stp w rt1 rt2 addr =>
    unfold isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, hbr0⟩ := band_true hsafe
    have hoff := of_decide_eq_true hoff0
    have hbr := of_decide_eq_true hbr0
    change Blk20StepOutcome base s (execStp w rt1 rt2 addr s)
    unfold execStp
    exact blk20_ite (Or.inl ⟨_, rfl⟩)
      (blk20_ite (Or.inl ⟨_, rfl⟩)
        (outcome_of_advancePC hrun hpc hoff
          (sameRunLrPc_addrWb s (sameRunLrPc_setMem (sameRunLrPc_refl s) _) hbr)))

/-! ## 2. `CodeLoaded` Helpers, Dynamic `fetchMem` Bridge & `Blk20TrapHook` -/

private theorem blockProgram_code_eq (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement) (i : Nat)
    (externs overrides : String → Option (State → State)) (svc : State → State) :
    (lib.blockProgram mpl i externs overrides svc).code =
      (lib.blockLib i).text.patched (lib.blockPlacement mpl i) := rfl

theorem mallocngBlockProg20_code_length (mmpl : Obj.MultiPlacement) (svc : State → State) :
    (mallocngBlockProg mmpl 20 svc).code.length = 396 := by
  have hcode : (mallocngBlockProg mmpl 20 svc).code =
      (mallocngLib.blockLib 20).text.patched (mallocngLib.blockPlacement mmpl 20) :=
    blockProgram_code_eq mallocngLib mmpl 20 _ _ svc
  rw [hcode, Obj.CodeBlock.length_patched, mallocngLib_blockLib20_text, mallocng_blk20_code_length]

private theorem codeLoaded_stripExecOutside_of_keep
    {keep : BitVec 64 → Bool} {prog : Program} {m : Memory}
    (hkeep : ∀ off : Nat, off < prog.code.length → keep (prog.base + BitVec.ofNat 64 off) = true)
    (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (stripExecOutside keep m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun off hoff => ?_
  have hk : keep (prog.base + BitVec.ofNat 64 off) = true := hkeep off hoff
  refine ⟨?_, ?_, ?_⟩
  · rw [strip_read8]; exact hL.byte_eq off hoff
  · rw [strip_perm, hk, hL.perm_eq off hoff]; rfl
  · rw [strip_isLazyFree]; exact hL.isLazyFree_eq off hoff

/-- Lift `(mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m` into `stripExecOutside keep m`
    whenever `KeepCoversBlk20 keep mmpl` holds (e.g. `keep = hole2_keepSub` or `keepMemcpyBlk20 mmpl`). -/
theorem codeLoaded_stripExecOutside_blk20
    {keep : BitVec 64 → Bool} {mmpl : Obj.MultiPlacement} {m : Memory}
    (hkeep : KeepCoversBlk20 keep mmpl)
    (hL : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m) :
    (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded (stripExecOutside keep m) := by
  refine codeLoaded_stripExecOutside_of_keep (fun off hoff => ?_) hL
  rw [mallocngBlockProg20_code_length] at hoff
  exact hkeep off hoff

/-- Lift `(pureWordsProg (mmpl.base 20) memcpySymWords).CodeLoaded m` into `stripExecOutside keep m`
    whenever `KeepCoversBlk20 keep mmpl` holds. -/
theorem codeLoaded_stripExecOutside_pure20
    {keep : BitVec 64 → Bool} {mmpl : Obj.MultiPlacement} {m : Memory}
    (hkeep : KeepCoversBlk20 keep mmpl)
    (hL : (pureWordsProg (mmpl.base 20) memcpySymWords).CodeLoaded m) :
    (pureWordsProg (mmpl.base 20) memcpySymWords).CodeLoaded (stripExecOutside keep m) := by
  refine codeLoaded_stripExecOutside_of_keep (fun off hoff => ?_) hL
  change off < (Program.ofWords 0#64 memcpySymWords).code.length at hoff
  have hlen : (Program.ofWords 0#64 memcpySymWords).code.length = 396 := by decide +kernel
  exact hkeep off (by omega)

/-- Any instruction dynamically fetched by `P_ghost.fetchMem m pc = some inst` at an address `pc`
    with `keepMemcpyBlk20 mmpl pc = true` when `mallocngBlockProg mmpl 20` is loaded in `m` lies at
    some offset `off < 396` from `mmpl.base 20` and satisfies `isBlk20SafeInstr off inst = true`. -/
theorem fetchMem_blk20_safe
    {P_ghost : Program} {mmpl : Obj.MultiPlacement} {m : Memory}
    {pc : BitVec 64} {inst : Instr}
    (hkeep : keepMemcpyBlk20 mmpl pc = true)
    (hL : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m)
    (hfm : P_ghost.fetchMem m pc = some inst) :
    ∃ off : Nat, off < 396 ∧
      pc = mmpl.base 20 + BitVec.ofNat 64 off ∧
      isBlk20SafeInstr off inst = true := by
  have hoff_lt : (pc - mmpl.base 20).toNat < 396 := of_decide_eq_true hkeep
  let off := (pc - mmpl.base 20).toNat
  have hpc_eq : pc = mmpl.base 20 + BitVec.ofNat 64 off := by
    dsimp only [off]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm (mmpl.base 20),
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
    have hbase_al : (mmpl.base 20).toNat % 4 = 0 := hL.aligned
    have hnowrap : (mmpl.base 20).toNat + 396 ≤ 2 ^ 64 := by
      have hnw := hL.no_wrap
      rwa [mallocngBlockProg20_code_length mmpl] at hnw
    have hpc_nat : pc.toNat = (mmpl.base 20).toNat + off := by
      rw [hpc_eq, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hoff_mod : off % 4 = 0 := by omega
    let k := off / 4
    have hoff_k : off = 4 * k := by omega
    have hk : k < 99 := by omega
    have hk_len : k < memcpySymWords.length := by rw [memcpySymWords_length]; exact hk
    have hall_k := List.all_eq_true.mp memcpyWords_all_safe k (List.mem_range.mpr hk)
    rw [List.getElem?_eq_getElem hk_len] at hall_k
    dsimp only [] at hall_k
    cases hdec : decode memcpySymWords[k] with
    | none =>
      rw [hdec] at hall_k
      contradiction
    | some inst' =>
      rw [hdec] at hall_k
      dsimp only [] at hall_k
      let P_sub := mallocngBlockProg mmpl 20 Syscall.standard
      have hrw := (mallocngBlockProg20_hasWords mmpl Syscall.standard).2.1 k hk_len
      change P_sub.readWordOff ((mmpl.base 20 - mmpl.base 20).toNat + 4 * k) =
        some memcpySymWords[k] at hrw
      rw [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, ← hoff_k] at hrw
      have hext_sub : P_sub.externAt? pc = none :=
        mallocngBlockProg20_externAt_none mmpl Syscall.standard pc
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
def Blk20TrapHook (L : BitVec 64) (f : State → State) : Prop :=
  ∀ w : State, w.status = .Running → w.readReg64 .lr = L →
    (∃ msg, (f w).status = .Exception msg) ∨
    ((f w).status = .Running ∧ (f w).pc = L ∧ (f w).readReg64 .lr = L)

theorem blk20TrapHook_hookMemcpy (L : BitVec 64) : Blk20TrapHook L hookMemcpy := by
  intro w hrun hlr
  exact Or.inr ⟨hrun, hlr, hlr⟩

/-- Any hook that faults with `.Exception _` whenever `w.readReg64 .lr = L` satisfies
    `Blk20TrapHook L` (covers all `K`-route narrowed ghost hooks when `keep` covers `blk20`). -/
theorem blk20TrapHook_of_exception_on_keepLr {L : BitVec 64} {f : State → State}
    (hex : ∀ w : State, w.status = .Running → w.readReg64 .lr = L →
      ∃ msg, (f w).status = .Exception msg) :
    Blk20TrapHook L f :=
  fun w hrun hlr => Or.inl (hex w hrun hlr)

/-- Generic `linkedCallHook` trap lemma when `keep L = true` and `keepFsTrace fallback` satisfies
    `Blk20TrapHook L`: since `ActiveRealRun` requires `keep (w.readReg64 .lr) = false`, `linkedCallHook`
    either faults with `.Exception _` or delegates to `keepFsTrace fallback`. -/
theorem blk20TrapHook_linkedCallHook {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    {spec : Spec α} {fallback : State → State} {L : BitVec 64}
    (hkeepL : keep L = true)
    (hfb : Blk20TrapHook L (keepFsTrace fallback)) :
    Blk20TrapHook L (linkedCallHook keep P_real P_sub entryTarget spec fallback) := by
  classical
  intro w hrun hlr
  unfold linkedCallHook
  by_cases hAct : ActiveRealPre spec w
  · have hnoReal : ¬ ActiveRealRun keep P_real P_sub entryTarget w := by
      intro hR
      have hfalse := hR.2.1
      rw [hlr, hkeepL] at hfalse
      exact Bool.noConfusion hfalse
    simp only [hAct, hnoReal, ↓reduceDIte]
    exact hfb w hrun hlr
  · refine Or.inl ⟨"ghost-hook precondition violated", ?_⟩
    simp [hAct]

/-- Generic `linkedCallHook` trap lemma for any `K`-narrowed contract (`¬ ActiveRealPre spec w` when
    `w.readReg64 .lr = L`), independent of `fallback` (covers all `K`-route ghost hooks when `keep`
    covers `blk20`). -/
theorem blk20TrapHook_linkedCallHook_of_not_pre {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    {spec : Spec α} {fallback : State → State} {L : BitVec 64}
    (hnoPre : ∀ w : State, w.readReg64 .lr = L → ¬ ActiveRealPre spec w) :
    Blk20TrapHook L (linkedCallHook keep P_real P_sub entryTarget spec fallback) := by
  classical
  intro w _ hlr
  have hnp := hnoPre w hlr
  refine Or.inl ⟨"ghost-hook precondition violated", ?_⟩
  unfold linkedCallHook
  simp [hnp]

/-- Plain `memcpyGhostHook` satisfies `Blk20TrapHook L` whenever `keep L = true`. -/
theorem blk20TrapHook_memcpyGhostHook
    {keep : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (hkeepL : keep L = true) :
    Blk20TrapHook L (memcpyGhostHook keep P_real P_sub entryTarget) := by
  refine blk20TrapHook_linkedCallHook hkeepL ?_
  intro w hrun hlr
  rw [keepFsTrace_hookMemcpy_eq]
  exact blk20TrapHook_hookMemcpy L w hrun hlr

/-- `K`-narrowed `memcpyGhostHookK` satisfies `Blk20TrapHook L` whenever `keep L = true`
    (it transitions immediately to `.Exception _`). -/
theorem blk20TrapHook_memcpyGhostHookK
    {keep : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (hkeepL : keep L = true) :
    Blk20TrapHook L (memcpyGhostHookK keep P_real P_sub entryTarget) := by
  intro w _ hlr
  rw [memcpyGhostHookK_of_keepLr_true (hlr ▸ hkeepL)]
  exact Or.inl ⟨"ghost-hook precondition violated", rfl⟩

/-! ## 3. Closed-Trap Impossibility & General Global `hlr_calls` Theorems -/

/-- Closed-trap invariant on `blk20` (`396` B at `mmpl.base 20`) with pinned `lr = L`. -/
def Blk20TrapInv (mmpl : Obj.MultiPlacement) (L : BitVec 64) (w : State) : Prop :=
  w.status = .Running ∧
  keepMemcpyBlk20 mmpl w.pc = true ∧
  w.readReg64 .lr = L ∧
  (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded w.mem

/-- **Closed-trap impossibility (`blk20_trap_impossible`, general terminal hypothesis):**
    No `Steps P_ghost w sf` starting in `Blk20TrapInv mmpl L w` (`keepMemcpyBlk20 mmpl L = true`)
    can reach a terminal state `sf` satisfying:
    - `sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false` (true vacuously for `.Exited _`,
      `.Panicked`, `.OutOfMemory`, `.Signaled _`, and true at subroutine `Returned` whenever the
      outer caller return PC lies outside `blk20`),
    - `∀ msg, sf.status ≠ .Exception msg`, and
    - `sf.status ≠ .Halted`,
    provided any extern inside `blk20` satisfies `Blk20TrapHook L`. -/
theorem blk20_trap_impossible
    {P_ghost : Program} {mmpl : Obj.MultiPlacement} {L : BitVec 64}
    (hL_in : keepMemcpyBlk20 mmpl L = true)
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ Blk20TrapHook L f)
    {w sf : State}
    (hsteps : Steps P_ghost w sf)
    (hrun_sf : sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted)
    (hInv : Blk20TrapInv mmpl L w) :
    False := by
  induction hsteps with
  | refl s =>
    exact Bool.noConfusion (hInv.2.1.symm.trans (hrun_sf hInv.1))
  | @step s1 s2 s3 h1 hrest ih =>
    rcases hInv with ⟨hrun1, hkeep1, hlr1, hCode1⟩
    have hCode2 : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded s2.mem :=
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
      rcases hblk20_ext s1.pc hkeep1 with hnone | ⟨f', hext', htrap⟩
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
      obtain ⟨off, _, hpc1, hsafe⟩ := fetchMem_blk20_safe hkeep1 hCode1 hfm
      have hnsvc0 := isBlk20SafeInstr_not_isSvc0 hsafe
      have heval : P_ghost.evalInst inst s1 = execInst inst s1 :=
        evalInst_eq_execInst_of_not_isSvc0 hnsvc0 s1
      rcases execInst_of_isBlk20SafeInstr hsafe hrun1 hpc1 with
        ⟨msg, hex⟩ | ⟨hrun2, hlr_eq, hpc_next⟩
      · have hex' : (P_ghost.evalInst inst s1).status = .Exception msg := heval ▸ hex
        have heq := ProofLib.Variant.Steps.eq_of_not_running hrest
          (by rw [hex']; nofun)
        have hst : s3.status = .Exception msg := by rw [heq, hex']
        exact hnoex_sf msg hst
      · rw [heval] at ih hCode2
        have hkeep2 : keepMemcpyBlk20 mmpl (execInst inst s1).pc = true := by
          rcases hpc_next with hpc_ret | ⟨off', hoff', hpc_off⟩
          · rw [hpc_ret, hlr1]; exact hL_in
          · rw [hpc_off]; exact keepCoversBlk20_keepMemcpyBlk20 mmpl off' hoff'
        exact ih hrun_sf hnoex_sf hnhalt_sf ⟨hrun2, hkeep2, hlr_eq.trans hlr1, hCode2⟩

/-- **Single-step call-site `lr ∉ blk20` discharge (`blk20_lr_trap_of_step`):**
    At any call step `Step P_ghost u v` followed by `Steps P_ghost v sf` where `P_ghost.externAt? u.pc`
    is some `f_call` satisfying `Blk20TrapHook L f_call` for `L ∈ blk20`, `keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false`
    holds under the general terminal hypotheses `sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false`,
    `∀ msg, sf.status ≠ .Exception msg`, and `sf.status ≠ .Halted` (with **zero** `bl`-at-call-site
    assumption, covering all 6 `b memcpy` tail-call sites). -/
theorem blk20_lr_trap_of_step
    {P_ghost : Program} {mmpl : Obj.MultiPlacement} {f_call : State → State}
    {u v sf : State}
    (htrap_call : ∀ L, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f_call)
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧ ∀ L, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hext_u : P_ghost.externAt? u.pc = some f_call)
    (hCode_u : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded u.mem)
    (h1 : Step P_ghost u v)
    (hrest : Steps P_ghost v sf)
    (hrun_u : u.status = .Running)
    (hrun_sf : sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false := by
  cases hkeepL : keepMemcpyBlk20 mmpl (u.readReg64 .lr) with
  | false => rfl
  | true =>
    exfalso
    let L := u.readReg64 .lr
    have hCode_v : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded v.mem :=
      h1.codeLoaded hCode_u
    have hblk20_trap : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
        P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ Blk20TrapHook L f := by
      intro pc hkp
      rcases hblk20_ext pc hkp with hnone | ⟨f, hf, htf⟩
      · exact Or.inl hnone
      · exact Or.inr ⟨f, hf, htf L hkeepL⟩
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
      rcases htrap_call L hkeepL u hrun_u rfl with ⟨msg, hex⟩ | ⟨hrun_v, hpc_v, hlr_v⟩
      · have heq := ProofLib.Variant.Steps.eq_of_not_running hrest
          (by rw [hex]; nofun)
        have hst : sf.status = .Exception msg := by rw [heq, hex]
        exact hnoex_sf msg hst
      · exact blk20_trap_impossible hkeepL hblk20_trap hrest hrun_sf hnoex_sf hnhalt_sf
          ⟨hrun_v, hpc_v ▸ hkeepL, hlr_v, hCode_v⟩

/-- **General multi-ghost `hlr_calls` discharge (`blk20_lr_trap_false_gen`, `08:18Z` addendum form):**
    Discharges `keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false` at every mismatching call step along
    `Steps P_ghost s0 u` + `Steps P_ghost u sf` (matching `steps_transfer_allocGhost`'s `hlr_calls`
    signature verbatim) under:
    1. `hblk20_ext`: every extern inside `blk20` (none under `--branch-stubs`, or `memcpyGhostHook[K]`
       at offset `0` under stock `ld.lld`) satisfies `Blk20TrapHook L` for `L ∈ blk20`,
    2. `hmis`: every mismatch `P_ghost.externAt? pc ≠ P_real.externAt? pc` is a ghost hook `f`
       satisfying `∀ L, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f` (supports multi-ghost
       `K`-route tables where 7+ allocator/stdin/`memset`/`memcpy` hooks differ simultaneously),
    3. `hrun_sf : sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false`,
       `hsf_nomis : sf.status = .Running → P_ghost.externAt? sf.pc = P_real.externAt? sf.pc`
       (ruling out `u = sf` in `Steps.refl u` when `sf.status = .Running`),
       `∀ msg, sf.status ≠ .Exception msg`, and `sf.status ≠ .Halted`. -/
theorem blk20_lr_trap_false_gen
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement}
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧ ∀ L, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hmis : ∀ pc, P_ghost.externAt? pc ≠ P_real.externAt? pc →
      ∃ f, P_ghost.externAt? pc = some f ∧ ∀ L, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    {s0 sf : State}
    (hCode0 : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded s0.mem)
    (hrun_sf : sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false)
    (hsf_nomis : sf.status = .Running → P_ghost.externAt? sf.pc = P_real.externAt? sf.pc)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false := by
  intro u hsteps_s0_u hsteps_u_sf hrun_u hne
  cases hsteps_u_sf with
  | refl =>
    exact False.elim (hne (hsf_nomis hrun_u))
  | @step _ v _ h1 hrest =>
    obtain ⟨f_call, hext_u, htrap_call⟩ := hmis u.pc hne
    exact blk20_lr_trap_of_step htrap_call hblk20_ext hext_u
      (hsteps_s0_u.codeLoaded hCode0) h1 hrest hrun_u hrun_sf hnoex_sf hnhalt_sf

/-- **Non-`.Running` terminal corollary (`blk20_lr_trap_false_nonRunning`):**
    Specializes `blk20_lr_trap_false_gen` when `sf.status ≠ .Running` (covering `.Exited _`,
    `.Panicked`, `.OutOfMemory`, and `.Signaled _` with zero PC conditions on `sf`). -/
theorem blk20_lr_trap_false_nonRunning
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement}
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧ ∀ L, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hmis : ∀ pc, P_ghost.externAt? pc ≠ P_real.externAt? pc →
      ∃ f, P_ghost.externAt? pc = some f ∧ ∀ L, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    {s0 sf : State}
    (hCode0 : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded s0.mem)
    (hrun_sf : sf.status ≠ .Running)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false :=
  blk20_lr_trap_false_gen hblk20_ext hmis hCode0
    (fun hr => False.elim (hrun_sf hr))
    (fun hr => False.elim (hrun_sf hr))
    hnoex_sf hnhalt_sf

/-- **Subroutine-outcome corollary (`blk20_lr_trap_false_subroutineOutcome`):**
    Specializes `blk20_lr_trap_false_gen` directly to any `SubroutineOutcome spec x R s0 sf`
    (`Returned`, `Panicked`, `Exited`, or `OutOfMemory`, e.g. Block 617 `CliElfHole2Assumption`):
    only entry-state hypotheses `keepMemcpyBlk20 mmpl (s0.readReg64 .lr) = false` and
    `P_ghost.externAt? (s0.readReg64 .lr) = P_real.externAt? (s0.readReg64 .lr)` on the outer caller
    return address `s0.readReg64 .lr` are needed! -/
theorem blk20_lr_trap_false_subroutineOutcome {α : Type} {spec : Spec α}
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement}
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧ ∀ L, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hmis : ∀ pc, P_ghost.externAt? pc ≠ P_real.externAt? pc →
      ∃ f, P_ghost.externAt? pc = some f ∧ ∀ L, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    {x : α} {R : SepProp} {s0 sf : State}
    (hCode0 : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded s0.mem)
    (hlr0_out : keepMemcpyBlk20 mmpl (s0.readReg64 .lr) = false)
    (hlr0_nomis : P_ghost.externAt? (s0.readReg64 .lr) = P_real.externAt? (s0.readReg64 .lr))
    (hout : SubroutineOutcome spec x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false := by
  have hrun_sf : sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false := by
    intro hrun
    rcases hout with ⟨⟨hpc, _, _⟩, _, _⟩ | ⟨hpan, _⟩ | ⟨_, hex, _⟩ | ⟨hoom, _⟩
    · rw [hpc]; exact hlr0_out
    · rw [hpan] at hrun; cases hrun
    · rw [hex] at hrun; cases hrun
    · rw [hoom] at hrun; cases hrun
  have hsf_nomis : sf.status = .Running → P_ghost.externAt? sf.pc = P_real.externAt? sf.pc := by
    intro hrun
    rcases hout with ⟨⟨hpc, _, _⟩, _, _⟩ | ⟨hpan, _⟩ | ⟨_, hex, _⟩ | ⟨hoom, _⟩
    · rw [hpc]; exact hlr0_nomis
    · rw [hpan] at hrun; cases hrun
    · rw [hex] at hrun; cases hrun
    · rw [hoom] at hrun; cases hrun
  have hnoex_sf : ∀ msg, sf.status ≠ .Exception msg := by
    intro msg hex0
    rcases hout with ⟨⟨_, _, hr⟩, _, _⟩ | ⟨hpan, _⟩ | ⟨_, hex, _⟩ | ⟨hoom, _⟩
    · rw [hex0] at hr; cases hr
    · rw [hex0] at hpan; cases hpan
    · rw [hex0] at hex; cases hex
    · rw [hex0] at hoom; cases hoom
  have hnhalt_sf : sf.status ≠ .Halted := by
    rcases hout with ⟨⟨_, _, hr⟩, _, _⟩ | ⟨hpan, _⟩ | ⟨_, hex, _⟩ | ⟨hoom, _⟩
    · rw [hr]; nofun
    · rw [hpan]; nofun
    · rw [hex]; nofun
    · rw [hoom]; nofun
  exact blk20_lr_trap_false_gen hblk20_ext hmis hCode0 hrun_sf hsf_nomis hnoex_sf hnhalt_sf

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrap
