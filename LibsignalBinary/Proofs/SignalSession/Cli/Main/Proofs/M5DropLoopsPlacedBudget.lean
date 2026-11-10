/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropLoopCorePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropLoopsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded Unrolled `Dir` Drop Blocks for `main` Hop M5 (Block `617`)

Budget-threaded verification of the unrolled `Dir` drop blocks (`m5_drop_dir_at_placed`,
`m5_drop_dirs_tail_placed`, `M+0xc70 → M+0xf70`) on Block `617`, advancing `A.pool` by `FreeOnlyEvs`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropLoopsPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.RustHeap (arrayAt vecAt vecBuf vecHeader vecOf)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (DirGhost dirEntryAt)
open CryptoVerification.SignalSession.Cli.Main.Placed
  (blkCodeEq_617 blkLib_617 blkPC_617 blkPl_617 blkTreeSize_617 lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (DropDirCmpCodePlaced DropDirCodePlaced DropLoopRegsPlaced InMainPlaced LsCodeInv codeOk_pure
   dirsAt mPcPlaced mPcPlaced_add mPcPlaced_add_sub mPcPlaced_bl_dealloc mProgPlaced
   mainFrameSize)
open CryptoVerification.SignalSession.Cli.MainHops.M5DropPlacedHelpers
  (calleeSaved_read_gpr dirVecAt dirsAt_absorb dirsVecAt layoutOk_dirBuf_of_cap_ne_zero
   mul48_toNat_of_lt ofNat_ne_of_ne_lt ofNat_ne_zero_of_pos_lt readReg64_setPC_st
   readReg64_setPState_st seq_sepWP_pl)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropLoopCorePlacedBudget
  (m5_drop_loop_body_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropPanicsPlacedBudget
  (step_dealloc_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsFsPlaced)

private theorem dropDir_freeOff_add_28_lt_4092 [LibsignalPlacement]
    {sOff freeOff dirOff : Nat} [d : DropDirCodePlaced sOff freeOff dirOff] :
    freeOff + 28 < 4092 := by
  by_contra hge
  have hfree := d.hfree
  by_cases h4064 : freeOff = 4064
  · subst h4064
    have hb16 : (lsProg_617 (fun _ => none)).fetch ((blkPl_617).base + BitVec.ofNat 64 4080) =
        some (Instr.moveWide RegWidth.W32 MoveWideOp.MOVZ (Reg.gpr 2#5) (8#16) 0) :=
      d.b16 (fun _ => none)
    simp only [arm64_norm] at hb16
    nomatch hb16
  · have hb24 := d.b24 (fun _ => none)
    have hlen : ∀ pl, ((blkLib_617).text.patched pl).length = 4092 := fun pl => by
      rw [Arm64.Obj.CodeBlock.length_patched, blkCodeEq_617,
        ProofLib.ProgramReflection.WordTree.length_toBytes_of_checkSize? blkTreeSize_617]
    unfold mProgPlaced lsProg_617 blkPC_617 PlacedLib.program Program.rebase
      mPcPlaced blkPl_617 MultiPlacedLib.blockPlacement Program.fetch at hb24
    dsimp only at hb24
    split at hb24
    · exact Option.some_ne_none _ hb24.symm
    · have hoff :
          ((lsmpl.base 617 + BitVec.ofNat 64 (freeOff + 24)) - lsmpl.base 617).toNat =
            freeOff + 24 := by
        rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega)]
      rw [hoff] at hb24
      unfold Program.readWordOff at hb24
      dsimp only at hb24
      split at hb24
      · exact Option.some_ne_none _ hb24.symm
      · have hge2 : 4092 ≤ freeOff + 24 := by omega
        have hdrop : ∀ pl, List.drop (freeOff + 24) ((blkLib_617).text.patched pl) = [] :=
          fun pl => List.drop_eq_nil_of_le (by rw [hlen]; exact hge2)
        rw [hdrop] at hb24
        exact Option.some_ne_none _ hb24.symm

private theorem dropDir_lsRetAddr624_freeOff_add_28 [LibsignalPlacement]
    {sOff freeOff dirOff : Nat} [d : DropDirCodePlaced sOff freeOff dirOff] :
    LsRetAddr624 (mPcPlaced freeOff + 28#64) :=
  ⟨617, by decide, freeOff + 28, dropDir_freeOff_add_28_lt_4092 (d := d),
    mPcPlaced_add freeOff 28⟩

attribute [local m5_st_pl ↓]
  RustCliAllocBudget.pool_setPC
  RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState
  RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32
  RustCliAllocBudget.pool_writeReg

/-! ## Unrolled `Dir` Drop Blocks (`m5_drop_dir_at_placed`, `m5_drop_dirs_tail_placed`) -/

private theorem mPcPlaced_add_eq [LibsignalPlacement] (a b c : Nat) (h : a + b = c) :
    mPcPlaced a + BitVec.ofNat 64 b = mPcPlaced c :=
  h ▸ mPcPlaced_add a b

private abbrev stateOf [LibsignalPlacement] {CodeOk : Memory → Prop} {s0 s : State} {off : Nat}
    (_ : InMainPlaced CodeOk s0 s off) : State := s

private theorem sub_cmp_eq (freeOff : Nat) :
    0xf50 - freeOff = 0xf70 - (freeOff + 32) := by omega

private theorem m5_drop_dir_freeBuf_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {sOff freeOff dirOff : Nat} [d : DropDirCodePlaced sOff freeOff dirOff]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {ret base cap ptr : BitVec 64} {s0 s : State} {stk : Nat}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hext : mainFrameSize + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hcap_lt : cap.toNat * 48 < 2 ^ 63)
    (hs : InMainPlaced CodeOk s0 s freeOff)
    (hx21 : s.readReg64 (.gpr 21#5) = ptr)
    (hx23 : s.readReg64 (.gpr 23#5) = base)
    (hnext : ∀ (sm : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      InMainPlaced CodeOk s0 sm (freeOff + 28) →
      (∀ r : BitVec 5, 19 ≤ r.toNat → r.toNat ≤ 29 → sm.readReg64 (.gpr r) = s.readReg64 (.gpr r)) →
      sm.fs = s.fs → sm.trace = s.trace →
      SepWPp (mProgPlaced H) ret sm
        (memRegion (base + BitVec.ofNat 64 dirOff) 8 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) Q Qp oom) :
    SepWPp (mProgPlaced H) ret s
      (((base + BitVec.ofNat 64 dirOff) ↦₆₄ cap) ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * 48) 8 ∗ memRegion ptr (cap.toNat * 48)) ∗
        A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) Q Qp oom := by
  have hpc := hs.pc
  have hrun := hs.run
  have hal := hs.spAligned_state
  let blBuf : BitVec 64 :=
    (lsρ lsRustDeallocSymCli - (blkPl_617).base) - BitVec.ofNat 64 (freeOff + 24)
  have b0 := d.b0 H
  have b4 := d.b4 H
  have b8 := d.b8 H
  have b12 := d.b12 H
  have b16 := d.b16 H
  have b20 := d.b20 H
  have b24 : (mProgPlaced H).fetch (mPcPlaced (freeOff + 24)) = some (Instr.bl blBuf) := d.b24 H
  have hbl : mPcPlaced freeOff + 24#64 + blBuf = lsρ lsRustDeallocSymCli := by
    rw [mPcPlaced_add freeOff 24]
    exact mPcPlaced_bl_dealloc (freeOff + 24)
  rw [← mPcPlaced_add freeOff 4] at b4
  rw [← mPcPlaced_add freeOff 8] at b8
  rw [← mPcPlaced_add freeOff 12] at b12
  rw [← mPcPlaced_add freeOff 16] at b16
  rw [← mPcPlaced_add freeOff 20] at b20
  rw [← mPcPlaced_add freeOff 24] at b24
  by_cases hcap0 : cap = 0
  · subst hcap0
    simp only [ite_true, emp_sepConj]
    apply seq_sepWP_pl (mid := mPcPlaced freeOff + 28#64)
    generalize hfBase : mPcPlaced freeOff = fBase at hpc b0 b4 b8 b12 b16 b20 b24 ⊢
    generalize hprog : mProgPlaced H = prog at b0 b4 b8 b12 b16 b20 b24 ⊢
    wp_steps
    apply SepWP.done
    · rfl
    · exact hrun
    clear b0 b4 b8 b12 b16 b20 b24
    subst hprog hfBase
    intro hpcm hrunm
    have hs1 := InMainPlaced.step_pure hs (hpcm.trans (mPcPlaced_add freeOff 28)) hrunm
    refine SepWPp.weaken_pre (P' :=
      memRegion (base + BitVec.ofNat 64 dirOff) 8 ∗
        A.pool lim (M.stepEvents [] st) (stateOf hs1) ∗ stackAt s.sp (stk - mainFrameSize) ∗ F)
      (Entails.trans
        (sepConj_mono_left (pointsTo64_entails_memRegion (base + BitVec.ofNat 64 dirOff) 0#64))
        (Entails.of_eq (by dsimp only [stateOf]; simp only [AllocCostModel.stepEvents_nil, m5_st_pl]))) ?_
    refine hnext _ [] FreeOnlyEvs.nil hs1
      ?_ (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    intro r hlo hhi
    m5_cs_pl hlo hhi
  · simp only [hcap0, ite_false]
    change cap ≠ 0#64 at hcap0
    have hlay := layoutOk_dirBuf_of_cap_ne_zero hcap0 hcap_lt
    have hsub1 : extHookStack ≤ stk - mainFrameSize := by omega
    have hsub2 : stk - mainFrameSize ≤ 2 ^ 64 := by omega
    apply seq_sepWP_pl (mid := mPcPlaced freeOff + 24#64 + blBuf)
    generalize hfBase : mPcPlaced freeOff = fBase at hpc b0 b4 b8 b12 b16 b20 b24 ⊢
    generalize hprog : mProgPlaced H = prog at b0 b4 b8 b12 b16 b20 b24 ⊢
    wp_steps
    apply SepWP.done
    · rfl
    · exact hrun
    clear b0 b4 b8 b12 b16 b20 b24
    subst hprog hfBase
    intro hpcm hrunm
    refine step_dealloc_placed (st := st) (sub := stk - mainFrameSize)
      (F := memRegion (base + BitVec.ofNat 64 dirOff) 8 ∗ F)
      hA hsub1 hsub2
      (codeOk_pure hs.inv) (hpcm.trans hbl) hrunm
      (by simpa only [State.spAligned, m5_st_pl] using hal)
      (by simp only [m5_st_pl] : _ = mPcPlaced freeOff + 28#64)
      (by simp only [m5_st_pl] : _ = ptr)
      (by
        simp only [m5_st_pl]
        have hsh : (cap + cap <<< 1) <<< 4 = cap * 48#64 := by bv_bits
        rw [hsh]
        exact mul48_toNat_of_lt cap hcap_lt)
      (by simp only [m5_st_pl]; decide)
      hlay
      (hP := ?_) (hnext := ?_)
      (hlr_ls := dropDir_lsRetAddr624_freeOff_add_28 (d := d))
    · have h0 : ((base + BitVec.ofNat 64 dirOff) ↦₆₄ cap) ⊢
          memRegion (base + BitVec.ofNat 64 dirOff) 8 :=
        pointsTo64_entails_memRegion (base + BitVec.ofNat 64 dirOff) cap
      have hpre_eq :
          ((base + BitVec.ofNat 64 dirOff) ↦₆₄ cap) ∗
            (A.live ptr (cap.toNat * 48) 8 ∗ memRegion ptr (cap.toNat * 48)) ∗
            A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗ F ⊢
          A.live ptr (cap.toNat * 48) 8 ∗ memRegion ptr (cap.toNat * 48) ∗ A.pool lim st s ∗
            stackAt s.sp (stk - mainFrameSize) ∗
            (memRegion (base + BitVec.ofNat 64 dirOff) 8 ∗ F) := by
        refine Entails.trans (sepConj_mono_left h0) ?_
        exact Entails.of_eq (by sep_ac_rfl)
      simpa only [sepConj_assoc, m5_st_pl] using hpre_eq
    · intro sm hpcm' hrunm' hspm' hcsm hinv' hfsm htrm
      have hsp_eq : sm.sp = s.sp := by simpa only [m5_st_pl] using hspm'
      have hfp_eq : sm.readReg64 .fp = s.readReg64 .fp := by
        simpa only [m5_st_pl] using hcsm.2.2.2.2.2.2.2.2.2.2.1
      have hvregs_eq : calleeSavedVRegs sm = calleeSavedVRegs s := by
        simpa only [calleeSavedVRegs, m5_st_pl] using hcsm.2.2.2.2.2.2.2.2.2.2.2
      refine SepWPp.weaken_pre (P' :=
        memRegion (base + BitVec.ofNat 64 dirOff) 8 ∗
          A.pool lim (M.stepEvents (rustDeallocEvents (cap.toNat * 48) 8) st) sm ∗
          stackAt s.sp (stk - mainFrameSize) ∗ F)
        (Entails.of_eq (by simp only [m5_st_pl]; sep_ac_rfl)) ?_
      refine hnext sm (rustDeallocEvents (cap.toNat * 48) 8)
        (FreeOnlyEvs.singleton 8 (cap.toNat * 48))
        (hs.mk_step (hpcm'.trans (mPcPlaced_add freeOff 28)) hrunm' hsp_eq hfp_eq hinv' hvregs_eq)
        ?_
        (by simpa only [m5_st_pl] using hfsm)
        (by simpa only [m5_st_pl] using htrm)
      intro r hlo hhi
      rw [calleeSaved_read_gpr hcsm r hlo hhi]
      m5_cs_pl hlo hhi

/-- Drop one `Dir` slot at `base + BitVec.ofNat 64 dirOff` (`x23 = base`), running uniformly from
`sOff` to `freeOff + 28` for ALL `j = 0 .. 6` (including `j = 6` at `0xef8 → 0xf54 → 0xf70`, skipping
`0xf40 .. 0xf50`), preserving `x19`, `x22`, `x23`, `x24`, `x26`, `sm.fs = s.fs`, and `sm.trace = s.trace`,
and advancing `A.pool lim st s` by `FreeOnlyEvs`. -/
theorem m5_drop_dir_at_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {sOff freeOff dirOff : Nat} [d : DropDirCodePlaced sOff freeOff dirOff]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {ret base : BitVec 64} {s0 s : State} {stk : Nat}
    {g : DirGhost}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hext : mainFrameSize + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hs : InMainPlaced CodeOk s0 s sOff)
    (hx23 : s.readReg64 (.gpr 23#5) = base)
    (hnext : ∀ (sm : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      InMainPlaced CodeOk s0 sm (freeOff + 28) →
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      sm.readReg64 (.gpr 23#5) = base →
      sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) →
      sm.fs = s.fs → sm.trace = s.trace →
      SepWPp (mProgPlaced H) ret sm
        (memRegion (base + BitVec.ofNat 64 dirOff) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) Q Qp oom) :
    SepWPp (mProgPlaced H) ret s
      (dirVecAt A.repAlloc (base + BitVec.ofNat 64 dirOff) g ∗
        A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) Q Qp oom := by
  unfold dirVecAt vecOf vecAt vecBuf
  simp only [sepExists_sepConj_left, RustCliAllocBudget.repAlloc_live]
  apply SepWPp.exists_elim; intro cap
  apply SepWPp.exists_elim; intro ptr
  simp only [sepConj_assoc]
  rw [show vecHeader (base + BitVec.ofNat 64 dirOff) cap ptr (BitVec.ofNat 64 g.changed.length) ∗
        ⌜g.changed.length ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * 48) 8 ∗ arrayAt (dirEntryAt A.repAlloc) 48 ptr g.changed ∗
           memRegion (ptr + BitVec.ofNat 64 (g.changed.length * 48))
             ((cap.toNat - g.changed.length) * 48)) ∗
        memRegion (base + BitVec.ofNat 64 dirOff + 0x18#64) 16 ∗
        A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗ F =
      ⌜g.changed.length ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (vecHeader (base + BitVec.ofNat 64 dirOff) cap ptr (BitVec.ofNat 64 g.changed.length) ∗
          (if cap = 0 then emp
           else A.live ptr (cap.toNat * 48) 8 ∗ arrayAt (dirEntryAt A.repAlloc) 48 ptr g.changed ∗
             memRegion (ptr + BitVec.ofNat 64 (g.changed.length * 48))
               ((cap.toNat - g.changed.length) * 48)) ∗
          memRegion (base + BitVec.ofNat 64 dirOff + 0x18#64) 16 ∗
          A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) by sep_ac_rfl]
  apply SepWPp.pure_elim
  rintro ⟨hlen, hcap_lt, _⟩
  have ho8 :
      (base + BitVec.ofNat 64 dirOff) + 8#64 = base + BitVec.ofNat 64 (dirOff + 8) := by
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
  have ho16 :
      (base + BitVec.ofNat 64 dirOff) + 16#64 =
        (base + BitVec.ofNat 64 (dirOff + 8)) + 8#64 := by
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
  have hpc := hs.pc
  have hrun := hs.run
  have s0_f := d.s0 H
  have s4_f := d.s4 H
  have s8_f := d.s8 H
  have s12_f := d.s12 H
  rw [← mPcPlaced_add sOff 4] at s4_f
  rw [← mPcPlaced_add sOff 8] at s8_f
  rw [← mPcPlaced_add sOff 12] at s12_f
  have htail32 :
      ((base + BitVec.ofNat 64 (dirOff + 8)) ↦₆₄ ptr) ∗
        (((base + BitVec.ofNat 64 (dirOff + 8)) + 8#64) ↦₆₄ BitVec.ofNat 64 g.changed.length) ∗
        memRegion (base + BitVec.ofNat 64 dirOff + 0x18#64) 16 ⊢
      memRegion (base + BitVec.ofNat 64 (dirOff + 8)) 32 := by
    have hp1 := pointsTo64_entails_memRegion (base + BitVec.ofNat 64 (dirOff + 8)) ptr
    have hp2 := pointsTo64_entails_memRegion
      ((base + BitVec.ofNat 64 (dirOff + 8)) + 8#64) (BitVec.ofNat 64 g.changed.length)
    refine Entails.trans (sepConj_mono hp1 (sepConj_mono_left hp2)) ?_
    have hm24 :
        memRegion ((base + BitVec.ofNat 64 (dirOff + 8)) + 8#64) 8 ∗
          memRegion (base + BitVec.ofNat 64 dirOff + 0x18#64) 16 =
          memRegion ((base + BitVec.ofNat 64 (dirOff + 8)) + 8#64) 24 :=
      (ProofLib.memRegion_split' rfl (by simp only [BitVec.add_assoc, ← BitVec.ofNat_add])
        (by decide)).symm
    have hm32 :
        memRegion (base + BitVec.ofNat 64 (dirOff + 8)) 8 ∗
          memRegion ((base + BitVec.ofNat 64 (dirOff + 8)) + 8#64) 24 =
          memRegion (base + BitVec.ofNat 64 (dirOff + 8)) 32 :=
      (ProofLib.memRegion_split' rfl rfl (by decide)).symm
    rw [hm24, hm32]
    exact Entails.refl _
  have hmerge40 :
      memRegion (base + BitVec.ofNat 64 dirOff) 8 ∗
        memRegion (base + BitVec.ofNat 64 (dirOff + 8)) 32 =
        memRegion (base + BitVec.ofNat 64 dirOff) 40 :=
    (ProofLib.memRegion_split' rfl ho8.symm (by decide)).symm
  cases hch : g.changed with
  | nil =>
    have hfree_le : sOff + 4 ≤ freeOff := by have := d.hfree; omega
    simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero,
      BitVec.add_zero, arrayAt, emp_sepConj]
    apply seq_sepWP_pl (mid := mPcPlaced sOff + 4#64 + BitVec.ofNat 64 (freeOff - (sOff + 4)))
    unfold vecHeader
    rw [ho8, ho16]
    generalize hsBase : mPcPlaced sOff = sBase at hpc s0_f s4_f s8_f s12_f ⊢
    generalize hprog : mProgPlaced H = prog at s0_f s4_f s8_f s12_f ⊢
    wp_steps
    apply SepWP.done
    · rfl
    · exact hrun
    clear s0_f s4_f s8_f s12_f
    subst hprog hsBase
    intro hpcm hrunm
    have hpc_eq :
        mPcPlaced sOff + 4#64 + BitVec.ofNat 64 (freeOff - (sOff + 4)) =
          mPcPlaced freeOff :=
      (congrArg (· + BitVec.ofNat 64 (freeOff - (sOff + 4)))
        (mPcPlaced_add sOff 4)).trans
        (mPcPlaced_add_sub hfree_le)
    have hs1 : InMainPlaced CodeOk s0 _ freeOff :=
      InMainPlaced.step_pure hs (hpcm.trans hpc_eq) hrunm
    refine SepWPp.weaken_pre (P' :=
        ((base + BitVec.ofNat 64 dirOff) ↦₆₄ cap) ∗
          (if cap = 0 then emp
           else A.live ptr (cap.toNat * 48) 8 ∗ memRegion ptr (cap.toNat * 48)) ∗
          A.pool lim st (stateOf hs1) ∗ stackAt s.sp (stk - mainFrameSize) ∗
          (memRegion (base + BitVec.ofNat 64 (dirOff + 8)) 32 ∗ F)) ?_ ?_
    · rw [hch] at htail32
      simp only [sepConj_assoc]
      refine Entails.trans (sepConj_mono_right (Entails.of_eq (show
        (((base + BitVec.ofNat 64 (dirOff + 8)) ↦₆₄ ptr) ∗
          (((base + BitVec.ofNat 64 (dirOff + 8)) + 8#64) ↦₆₄ 0#64) ∗
          (if cap = 0 then emp
           else A.live ptr (cap.toNat * 48) 8 ∗ memRegion ptr (cap.toNat * 48)) ∗
          memRegion (base + BitVec.ofNat 64 dirOff + 0x18#64) 16 ∗
          A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) =
        (((base + BitVec.ofNat 64 (dirOff + 8)) ↦₆₄ ptr) ∗
          (((base + BitVec.ofNat 64 (dirOff + 8)) + 8#64) ↦₆₄ 0#64) ∗
          memRegion (base + BitVec.ofNat 64 dirOff + 0x18#64) 16) ∗
          ((if cap = 0 then emp
            else A.live ptr (cap.toNat * 48) 8 ∗ memRegion ptr (cap.toNat * 48)) ∗
            A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) by sep_ac_rfl))) ?_
      refine Entails.trans (sepConj_mono_right (sepConj_mono_left htail32)) ?_
      exact Entails.of_eq (by dsimp only [stateOf]; simp only [m5_st_pl]; sep_ac_rfl)
    · rw [hs.sp.trans hs1.sp.symm]
      refine m5_drop_dir_freeBuf_placed (sOff := sOff) (st := st) hA hext hstk64 hcap_lt hs1
        (by simp only [m5_st_pl])
        (by simp only [m5_st_pl, hx23]) ?_
      intro sm evs hf hsm hcs hfsm htrm
      rw [hs1.sp.trans hs.sp.symm]
      refine SepWPp.weaken_pre (P' :=
        memRegion (base + BitVec.ofNat 64 dirOff) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt s.sp (stk - mainFrameSize) ∗ F)
        (Entails.of_eq (by
          rw [← hmerge40]
          sep_ac_rfl)) ?_
      exact hnext sm evs hf hsm
        (by simpa only [m5_st_pl] using hcs 19#5 (by decide) (by decide))
        (by simpa only [m5_st_pl] using hcs 22#5 (by decide) (by decide))
        (by simpa only [m5_st_pl, hx23] using hcs 23#5 (by decide) (by decide))
        (by simpa only [m5_st_pl] using hcs 24#5 (by decide) (by decide))
        (by simpa only [m5_st_pl] using hcs 26#5 (by decide) (by decide))
        (by simpa only [m5_st_pl] using hfsm)
        (by simpa only [m5_st_pl] using htrm)
  | cons e rest =>
    have hlen_pos : 0 < (e :: rest).length := by simp
    have hcap_ne : cap ≠ 0 := by
      intro hc0; subst hc0; rw [hch] at hlen; simp at hlen
    simp only [hcap_ne, ite_false]
    have hnez_len : BitVec.ofNat 64 (e :: rest).length ≠ 0#64 :=
      ofNat_ne_zero_of_pos_lt hlen_pos (by rw [hch] at hlen; omega)
    apply seq_sepWP_pl (mid := mPcPlaced sOff + 28#64)
    unfold vecHeader
    rw [ho8, ho16]
    generalize hsBase : mPcPlaced sOff = sBase at hpc s0_f s4_f s8_f s12_f ⊢
    generalize hprog : mProgPlaced H = prog at s0_f s4_f s8_f s12_f ⊢
    wp_steps
    apply SepWP.done
    · rfl
    · exact hrun
    clear s0_f s4_f s8_f s12_f
    subst hprog hsBase
    intro hpcm hrunm
    have hs1 : InMainPlaced CodeOk s0 _ ((sOff + 16) + 12) :=
      InMainPlaced.step_pure hs
        (hpcm.trans (mPcPlaced_add_eq sOff 28 ((sOff + 16) + 12) (by omega)))
        hrunm
    refine SepWPp.weaken_pre (P' :=
        arrayAt (dirEntryAt A.repAlloc) 48 ptr (e :: rest) ∗
          A.pool lim st (stateOf hs1) ∗ stackAt s.sp (stk - mainFrameSize) ∗
          (((base + BitVec.ofNat 64 dirOff) ↦₆₄ cap) ∗
            A.live ptr (cap.toNat * 48) 8 ∗
            memRegion (ptr + BitVec.ofNat 64 ((e :: rest).length * 48))
              ((cap.toNat - (e :: rest).length) * 48) ∗
            memRegion (base + BitVec.ofNat 64 (dirOff + 8)) 32 ∗ F)) ?_ ?_
    · rw [hch] at htail32
      simp only [sepConj_assoc]
      refine Entails.trans (sepConj_mono_right (Entails.of_eq (show
        (((base + BitVec.ofNat 64 (dirOff + 8)) ↦₆₄ ptr) ∗
          (((base + BitVec.ofNat 64 (dirOff + 8)) + 8#64) ↦₆₄ BitVec.ofNat 64 (e :: rest).length) ∗
          A.live ptr (cap.toNat * 48) 8 ∗ arrayAt (dirEntryAt A.repAlloc) 48 ptr (e :: rest) ∗
          memRegion (ptr + BitVec.ofNat 64 ((e :: rest).length * 48))
            ((cap.toNat - (e :: rest).length) * 48) ∗
          memRegion (base + BitVec.ofNat 64 dirOff + 0x18#64) 16 ∗
          A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) =
        (((base + BitVec.ofNat 64 (dirOff + 8)) ↦₆₄ ptr) ∗
          (((base + BitVec.ofNat 64 (dirOff + 8)) + 8#64) ↦₆₄ BitVec.ofNat 64 (e :: rest).length) ∗
          memRegion (base + BitVec.ofNat 64 dirOff + 0x18#64) 16) ∗
          (arrayAt (dirEntryAt A.repAlloc) 48 ptr (e :: rest) ∗
            A.live ptr (cap.toNat * 48) 8 ∗
            memRegion (ptr + BitVec.ofNat 64 ((e :: rest).length * 48))
              ((cap.toNat - (e :: rest).length) * 48) ∗
            A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) by sep_ac_rfl))) ?_
      refine Entails.trans (sepConj_mono_right (sepConj_mono_left htail32)) ?_
      exact Entails.of_eq (by dsimp only [stateOf]; simp only [m5_st_pl]; sep_ac_rfl)
    · rw [hs.sp.trans hs1.sp.symm]
      refine m5_drop_loop_body_placed (h := sOff + 16) (exit := freeOff) (regs := .r20_25)
        (ptr := ptr) (st := st) hA hext hstk64 (by simp) (by rw [hch] at hlen; omega) hs1
        (by dsimp only [DropLoopRegsPlaced.rc]; simp only [m5_st_pl])
        (by dsimp only [DropLoopRegsPlaced.rp]; simp only [m5_st_pl]) ?_
      intro s2 evs1 hf1 hs2 hkeeps hfs2 htr2
      have hx21_2 : s2.readReg64 (.gpr 21#5) = ptr := by
        rw [hkeeps 21#5 (by decide) (by decide) (by decide) (by decide)]
        simp only [m5_st_pl]
      have hx23_2 : s2.readReg64 (.gpr 23#5) = base := by
        rw [hkeeps 23#5 (by decide) (by decide) (by decide) (by decide)]
        simp only [m5_st_pl, hx23]
      have hsp2 : s2.sp = s.sp := hs2.sp.trans hs.sp.symm
      have hbuf_merge :
          memRegion ptr ((e :: rest).length * 48) ∗
            memRegion (ptr + BitVec.ofNat 64 ((e :: rest).length * 48))
              ((cap.toNat - (e :: rest).length) * 48) =
            memRegion ptr (cap.toNat * 48) :=
        (ProofLib.memRegion_split' (by rw [hch] at hlen; omega) rfl (by omega)).symm
      rw [hs1.sp.trans hs.sp.symm]
      refine SepWPp.weaken_pre (P' :=
          ((base + BitVec.ofNat 64 dirOff) ↦₆₄ cap) ∗
            (if cap = 0 then emp
             else A.live ptr (cap.toNat * 48) 8 ∗ memRegion ptr (cap.toNat * 48)) ∗
            A.pool lim (M.stepEvents evs1 st) s2 ∗ stackAt s2.sp (stk - mainFrameSize) ∗
            (memRegion (base + BitVec.ofNat 64 (dirOff + 8)) 32 ∗ F)) (by
        simp only [hcap_ne, ite_false, hsp2]
        exact Entails.of_eq (by rw [← hbuf_merge]; sep_ac_rfl)) ?_
      refine m5_drop_dir_freeBuf_placed (sOff := sOff) (st := M.stepEvents evs1 st)
        hA hext hstk64 hcap_lt hs2 hx21_2 hx23_2 ?_
      intro sm evs2 hf2 hsm hcs3 hfs3 htr3
      rw [hsp2, ← M.stepEvents_append evs1 evs2 st]
      refine SepWPp.weaken_pre (P' :=
        memRegion (base + BitVec.ofNat 64 dirOff) 40 ∗
          A.pool lim (M.stepEvents (evs1 ++ evs2) st) sm ∗
          stackAt s.sp (stk - mainFrameSize) ∗ F)
        (Entails.of_eq (by rw [← hmerge40]; sep_ac_rfl)) ?_
      exact hnext sm (evs1 ++ evs2) (hf1.append hf2) hsm
        ((hcs3 19#5 (by decide) (by decide)).trans
          ((hkeeps 19#5 (by decide) (by decide) (by decide) (by decide)).trans
            (by simp only [m5_st_pl])))
        ((hcs3 22#5 (by decide) (by decide)).trans
          ((hkeeps 22#5 (by decide) (by decide) (by decide) (by decide)).trans
            (by simp only [m5_st_pl])))
        ((hcs3 23#5 (by decide) (by decide)).trans hx23_2)
        ((hcs3 24#5 (by decide) (by decide)).trans
          ((hkeeps 24#5 (by decide) (by decide) (by decide) (by decide)).trans
            (by simp only [m5_st_pl])))
        ((hcs3 26#5 (by decide) (by decide)).trans
          ((hkeeps 26#5 (by decide) (by decide) (by decide) (by decide)).trans
            (by simp only [m5_st_pl])))
        (hfs3.trans (hfs2.trans (by simp only [m5_st_pl])))
        (htr3.trans (htr2.trans (by simp only [m5_st_pl])))

private theorem step_cmp_eq {prog : Program} {cmpBase : BitVec 64} {freeOff j : Nat}
    {s : State} {P : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = cmpBase) (hrun : s.status = .Running)
    (hx26 : s.readReg64 (.gpr 26#5) = BitVec.ofNat 64 (7 - j))
    (c0 : prog.fetch cmpBase =
      some (Instr.addSubImm RegWidth.W64 AddSubOp.SUBS Reg.xzr (Reg.gpr 26#5)
        (BitVec.ofNat 12 (7 - j)) false))
    (c4 : prog.fetch (cmpBase + 4#64) =
      some (Instr.bCond CondCode.EQ (BitVec.ofNat 64 (0xf70 - (freeOff + 32)))))
    (hdone : ∀ s' : State,
      s'.pc = cmpBase + 4#64 + BitVec.ofNat 64 (0xf50 - freeOff) →
      s'.status = .Running →
      s'.sp = s.sp → s'.mem = s.mem → s'.symtab = s.symtab →
      s'.vregs = s.vregs → s'.fs = s.fs → s'.trace = s.trace →
      (∀ r : Reg, s'.readReg64 r = s.readReg64 r) →
      (∀ (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ),
        A.pool lim st s' = A.pool lim st s) →
      Q s' P) :
    SepWP prog (cmpBase + 4#64 + BitVec.ofNat 64 (0xf50 - freeOff)) s P Q oom := by
  have hze : BitVec.zeroExtend 64 (BitVec.ofNat 12 (7 - j)) = BitVec.ofNat 64 (7 - j) := by
    apply BitVec.eq_of_toNat_eq; simp; omega
  wp_steps
  apply SepWP.done
  · rfl
  · exact hrun
  exact hdone _ rfl hrun (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (fun r => by simp only [m5_st_pl, readReg64_setPC_st, readReg64_setPState_st])
    (fun _ _ _ _ => by simp only [m5_st_pl])

private theorem step_cmp_ne {prog : Program} {cmpBase : BitVec 64} {freeOff m j : Nat}
    {s : State} {P : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = cmpBase) (hrun : s.status = .Running)
    (hx26 : s.readReg64 (.gpr 26#5) = BitVec.ofNat 64 m)
    (hne : BitVec.ofNat 64 m ≠ BitVec.ofNat 64 (7 - j))
    (c0 : prog.fetch cmpBase =
      some (Instr.addSubImm RegWidth.W64 AddSubOp.SUBS Reg.xzr (Reg.gpr 26#5)
        (BitVec.ofNat 12 (7 - j)) false))
    (c4 : prog.fetch (cmpBase + 4#64) =
      some (Instr.bCond CondCode.EQ (BitVec.ofNat 64 (0xf70 - (freeOff + 32)))))
    (hdone : ∀ s' : State,
      s'.pc = cmpBase + 8#64 →
      s'.status = .Running →
      s'.sp = s.sp → s'.mem = s.mem → s'.symtab = s.symtab →
      s'.vregs = s.vregs → s'.fs = s.fs → s'.trace = s.trace →
      (∀ r : Reg, s'.readReg64 r = s.readReg64 r) →
      (∀ (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ),
        A.pool lim st s' = A.pool lim st s) →
      Q s' P) :
    SepWP prog (cmpBase + 8#64) s P Q oom := by
  have hze : BitVec.zeroExtend 64 (BitVec.ofNat 12 (7 - j)) = BitVec.ofNat 64 (7 - j) := by
    apply BitVec.eq_of_toNat_eq; simp; omega
  wp_steps
  apply SepWP.done
  · rfl
  · exact hrun
  exact hdone _ rfl hrun (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (by simp only [m5_st_pl]) (by simp only [m5_st_pl])
    (fun r => by simp only [m5_st_pl, readReg64_setPC_st, readReg64_setPState_st])
    (fun _ _ _ _ => by simp only [m5_st_pl])

private theorem m5_drop_dir_stage_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {sOff freeOff dirOff j : Nat}
    [DropDirCodePlaced sOff freeOff dirOff] [cmp : DropDirCmpCodePlaced freeOff j]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {ret base : BitVec 64} {s0 s : State} {stk m : Nat}
    {ds : List DirGhost}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hdirOff : dirOff = 0x28 * j)
    (hj : j < 6)
    (hm_lo : 1 ≤ m) (hm_hi : m ≤ 7 - j)
    (hlen : ds.length = 8 - m - j)
    (hA : AllocContractsFsPlaced A lim H)
    (hext : mainFrameSize + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hs : InMainPlaced CodeOk s0 s sOff)
    (hx23 : s.readReg64 (.gpr 23#5) = base)
    (hx26 : s.readReg64 (.gpr 26#5) = BitVec.ofNat 64 m)
    (hstage_next : ∀ (s' : State) (ds' : List DirGhost) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      m ≤ 7 - (j + 1) →
      ds'.length = 8 - m - (j + 1) →
      InMainPlaced CodeOk s0 s' (freeOff + 36) →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      s'.readReg64 (.gpr 23#5) = base →
      s'.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      s'.readReg64 (.gpr 26#5) = BitVec.ofNat 64 m →
      s'.fs = s.fs → s'.trace = s.trace →
      SepWPp (mProgPlaced H) ret s'
        (dirsVecAt A.repAlloc (base + BitVec.ofNat 64 (0x28 * (j + 1))) ds' ∗
          A.pool lim (M.stepEvents evs st) s' ∗ stackAt s.sp (stk - mainFrameSize) ∗
          (memRegion (base + BitVec.ofNat 64 (0x28 * j)) 40 ∗ F)) Q Qp oom)
    (hdone : ∀ (sm : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      InMainPlaced CodeOk s0 sm 0xf70 →
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      sm.fs = s.fs → sm.trace = s.trace →
      SepWPp (mProgPlaced H) ret sm
        (memRegion (base + BitVec.ofNat 64 (0x28 * j)) (0x28 * (8 - m - j)) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) Q Qp oom) :
    SepWPp (mProgPlaced H) ret s
      (dirsVecAt A.repAlloc (base + BitVec.ofNat 64 (0x28 * j)) ds ∗
        A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) Q Qp oom := by
  cases ds with
  | nil => simp at hlen; omega
  | cons d0 ds' =>
    simp only [List.length_cons] at hlen
    dsimp only [dirsVecAt]
    have hnext_addr :
        (base + BitVec.ofNat 64 (0x28 * j)) + 0x28#64 =
          base + BitVec.ofNat 64 (0x28 * (j + 1)) := by
      simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
      apply congrArg (base + ·); apply congrArg (BitVec.ofNat 64); omega
    refine SepWPp.weaken_pre (P' :=
      dirVecAt A.repAlloc (base + BitVec.ofNat 64 dirOff) d0 ∗
        A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗
        (dirsVecAt A.repAlloc (base + BitVec.ofNat 64 (0x28 * (j + 1))) ds' ∗ F))
      (Entails.of_eq (by rw [hnext_addr, ← hdirOff]; sep_ac_rfl)) ?_
    refine m5_drop_dir_at_placed (sOff := sOff) (freeOff := freeOff) (st := st)
      hA hext hstk64 hs hx23 ?_
    intro s1 evs1 hf1 hs1 hx19_1 hx22_1 hx23_1 hx24_1 hx26_1 hfs1 htr1
    rw [hx26] at hx26_1
    have c4' : (mProgPlaced H).fetch (mPcPlaced (freeOff + 28) + 4#64) =
        some (Instr.bCond CondCode.EQ (BitVec.ofNat 64 (0xf70 - (freeOff + 32)))) :=
      (mPcPlaced_add_eq (freeOff + 28) 4 (freeOff + 32)
        (Nat.add_assoc _ _ _)).symm ▸ cmp.c4 H
    by_cases hmeq : m = 7 - j
    · subst hmeq
      have hds'_nil : ds' = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hds'_nil
      have hex : 8 - (7 - j) - j = 1 := by omega
      have hpc_eq :
          mPcPlaced (freeOff + 28) + 4#64 + BitVec.ofNat 64 (0xf50 - freeOff) =
            mPcPlaced 0xf70 :=
        (congrArg₂ (· + BitVec.ofNat 64 ·)
          (mPcPlaced_add_eq (freeOff + 28) 4 (freeOff + 32) (Nat.add_assoc _ _ _))
          (sub_cmp_eq freeOff)).trans
          (mPcPlaced_add_sub cmp.hcmp)
      simp only [dirsVecAt, emp_sepConj]
      apply seq_sepWP_pl
        (mid := mPcPlaced (freeOff + 28) + 4#64 + BitVec.ofNat 64 (0xf50 - freeOff))
      refine step_cmp_eq hs1.pc hs1.run hx26_1 (cmp.c0 H) c4' ?_
      intro s2 hpcm hrunm hsp2 hm2 hsym2 hv2 hfs2 htr2 hregs2 hpool2 _ _
      refine SepWPp.weaken_pre
        (P := memRegion (base + BitVec.ofNat 64 dirOff) 40 ∗
          A.pool lim (M.stepEvents evs1 st) s1 ∗ stackAt s.sp (stk - mainFrameSize) ∗ F)
        (P' := memRegion (base + BitVec.ofNat 64 (0x28 * j)) (0x28 * (8 - (7 - j) - j)) ∗
          A.pool lim (M.stepEvents evs1 st) s2 ∗ stackAt s.sp (stk - mainFrameSize) ∗ F)
        (Entails.of_eq (by rw [hdirOff, hpool2]; simp only [hex, Nat.mul_one])) ?_
      exact hdone s2 evs1 hf1
        (InMainPlaced.step_pure hs1 (hpcm.trans hpc_eq) hrunm hsp2 (hregs2 .fp) hm2
          (by simp only [calleeSavedVRegs, hv2]))
        ((hregs2 (.gpr 19#5)).trans hx19_1)
        ((hregs2 (.gpr 22#5)).trans hx22_1)
        ((hregs2 (.gpr 24#5)).trans hx24_1)
        (hfs2.trans hfs1)
        (htr2.trans htr1)
    · have hne_bv : BitVec.ofNat 64 m ≠ BitVec.ofNat 64 (7 - j) :=
        ofNat_ne_of_ne_lt hmeq (by omega) (by omega)
      have hm_next : m ≤ 7 - (j + 1) := by omega
      have hlen_next : ds'.length = 8 - m - (j + 1) := by omega
      have hpc_eq : mPcPlaced (freeOff + 28) + 8#64 = mPcPlaced (freeOff + 36) :=
        mPcPlaced_add_eq (freeOff + 28) 8 (freeOff + 36) (Nat.add_assoc _ _ _)
      apply seq_sepWP_pl (mid := mPcPlaced (freeOff + 28) + 8#64)
      refine step_cmp_ne hs1.pc hs1.run hx26_1 hne_bv (cmp.c0 H) c4' ?_
      intro s2 hpcm hrunm hsp2 hm2 hsym2 hv2 hfs2 htr2 hregs2 hpool2 _ _
      refine SepWPp.weaken_pre
        (P := memRegion (base + BitVec.ofNat 64 dirOff) 40 ∗
          A.pool lim (M.stepEvents evs1 st) s1 ∗ stackAt s.sp (stk - mainFrameSize) ∗
          (dirsVecAt A.repAlloc (base + BitVec.ofNat 64 (0x28 * (j + 1))) ds' ∗ F))
        (P' := dirsVecAt A.repAlloc (base + BitVec.ofNat 64 (0x28 * (j + 1))) ds' ∗
          A.pool lim (M.stepEvents evs1 st) s2 ∗ stackAt s.sp (stk - mainFrameSize) ∗
          (memRegion (base + BitVec.ofNat 64 (0x28 * j)) 40 ∗ F))
        (Entails.of_eq (by rw [hdirOff, hpool2]; sep_ac_rfl)) ?_
      exact hstage_next s2 ds' evs1 hf1
        hm_next hlen_next
        (InMainPlaced.step_pure hs1 (hpcm.trans hpc_eq) hrunm hsp2 (hregs2 .fp) hm2
          (by simp only [calleeSavedVRegs, hv2]))
        ((hregs2 (.gpr 19#5)).trans hx19_1)
        ((hregs2 (.gpr 22#5)).trans hx22_1)
        ((hregs2 (.gpr 23#5)).trans hx23_1)
        ((hregs2 (.gpr 24#5)).trans hx24_1)
        ((hregs2 (.gpr 26#5)).trans hx26_1)
        (hfs2.trans hfs1)
        (htr2.trans htr1)

private def DropStagePropPlaced [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    (j sOff : Nat) : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    {ret base : BitVec 64} {s0 s : State} {stk m : Nat}
    {ds : List DirGhost}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp},
    1 ≤ m → m ≤ 7 - j → ds.length = 8 - m - j →
    AllocContractsFsPlaced A lim H →
    mainFrameSize + extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    InMainPlaced CodeOk s0 s sOff →
    s.readReg64 (.gpr 23#5) = base →
    s.readReg64 (.gpr 26#5) = BitVec.ofNat 64 m →
    (∀ (sm : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      InMainPlaced CodeOk s0 sm 0xf70 →
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      sm.fs = s.fs → sm.trace = s.trace →
      SepWPp (mProgPlaced H) ret sm
        (memRegion (base + BitVec.ofNat 64 (0x28 * j)) (0x28 * (8 - m - j)) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) Q Qp oom) →
    SepWPp (mProgPlaced H) ret s
      (dirsVecAt A.repAlloc (base + BitVec.ofNat 64 (0x28 * j)) ds ∗
        A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) Q Qp oom

private theorem dropStage_6_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] :
    DropStagePropPlaced (CodeOk := CodeOk) 6 0xef8 := by
  intro M A lim st H ret base s0 s stk m ds F Q Qp oom hm_lo hm_hi hlen hA hext hstk64 hs hx23 _
    hdone
  have hm1 : m = 1 := by omega
  subst hm1
  cases ds with
  | nil => simp at hlen
  | cons d0 ds' =>
    cases ds' with
    | cons _ _ => simp at hlen
    | nil =>
      dsimp only [dirsVecAt]
      simp only [sepConj_emp]
      refine m5_drop_dir_at_placed (sOff := 0xef8) (freeOff := 0xf54) (st := st)
        hA hext hstk64 hs hx23 ?_
      intro sm evs hf hsm hx19 hx22 _ hx24 _ hfs htr
      exact hdone sm evs hf hsm hx19 hx22 hx24 hfs htr

private theorem dropStage_step_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {j sOff freeOff dirOff : Nat}
    [DropDirCodePlaced sOff freeOff dirOff] [DropDirCmpCodePlaced freeOff j]
    (hdirOff : dirOff = 0x28 * j) (hj : j < 6)
    (hnextStage : DropStagePropPlaced (CodeOk := CodeOk) (j + 1) (freeOff + 36)) :
    DropStagePropPlaced (CodeOk := CodeOk) j sOff := by
  intro M A lim st H ret base s0 s stk m ds F Q Qp oom hm_lo hm_hi hlen hA hext hstk64 hs hx23 hx26
    hdone
  refine m5_drop_dir_stage_placed (freeOff := freeOff) (st := st)
    hdirOff hj hm_lo hm_hi hlen hA hext hstk64 hs hx23 hx26 ?_ hdone
  intro s' ds' evs1 hf1 hm' hlen' hs' hx19' hx22' hx23' hx24' hx26' hfs' htr'
  have hsp' : s'.sp = s.sp := hs'.sp.trans hs.sp.symm
  rw [← hsp']
  refine hnextStage (st := M.stepEvents evs1 st) hm_lo hm' hlen' hA hext hstk64 hs' hx23' hx26' ?_
  intro sm evs2 hf2 hsm hx19m hx22m hx24m hfsm htrm
  rw [hsp', ← M.stepEvents_append evs1 evs2 st]
  have hmerge :
      memRegion (base + BitVec.ofNat 64 (0x28 * j)) 40 ∗
        memRegion (base + BitVec.ofNat 64 (0x28 * (j + 1))) (0x28 * (8 - m - (j + 1))) =
        memRegion (base + BitVec.ofNat 64 (0x28 * j)) (0x28 * (8 - m - j)) :=
    (ProofLib.memRegion_split' (by omega) (by
      simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
      apply congrArg (base + ·); apply congrArg (BitVec.ofNat 64); omega) (by omega)).symm
  refine SepWPp.weaken_pre (P' :=
    memRegion (base + BitVec.ofNat 64 (0x28 * j)) (0x28 * (8 - m - j)) ∗
      A.pool lim (M.stepEvents (evs1 ++ evs2) st) sm ∗
      stackAt s.sp (stk - mainFrameSize) ∗ F)
    (Entails.of_eq (by
      rw [← hmerge]
      sep_ac_rfl)) ?_
  exact hdone sm (evs1 ++ evs2) (hf1.append hf2) hsm
    (hx19m.trans hx19') (hx22m.trans hx22') (hx24m.trans hx24')
    (hfsm.trans hfs') (htrm.trans htr')

private theorem dropStage_5_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] :
    DropStagePropPlaced (CodeOk := CodeOk) 5 0xe8c :=
  dropStage_step_placed (freeOff := 0xed4) (dirOff := 0xc8) rfl (by decide) dropStage_6_placed
private theorem dropStage_4_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] :
    DropStagePropPlaced (CodeOk := CodeOk) 4 0xe20 :=
  dropStage_step_placed (freeOff := 0xe68) (dirOff := 0xa0) rfl (by decide) dropStage_5_placed
private theorem dropStage_3_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] :
    DropStagePropPlaced (CodeOk := CodeOk) 3 0xdb4 :=
  dropStage_step_placed (freeOff := 0xdfc) (dirOff := 0x78) rfl (by decide) dropStage_4_placed
private theorem dropStage_2_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] :
    DropStagePropPlaced (CodeOk := CodeOk) 2 0xd48 :=
  dropStage_step_placed (freeOff := 0xd90) (dirOff := 0x50) rfl (by decide) dropStage_3_placed
private theorem dropStage_1_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] :
    DropStagePropPlaced (CodeOk := CodeOk) 1 0xcdc :=
  dropStage_step_placed (freeOff := 0xd24) (dirOff := 0x28) rfl (by decide) dropStage_2_placed
private theorem dropStage_0_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] :
    DropStagePropPlaced (CodeOk := CodeOk) 0 0xc70 :=
  dropStage_step_placed (freeOff := 0xcb8) (dirOff := 0x0) rfl (by decide) dropStage_1_placed

/-- Drop all remaining `8 - m` `Dir` slots (`1 ≤ m ≤ 7`) starting at `0xc70` with `x23 = base` and
`x26 = BitVec.ofNat 64 m`, landing at `0xf70` with `memRegion base (0x28 * (8 - m))`, preserving
`x19`, `x22`, `x24`, `sm.fs = s.fs`, `sm.trace = s.trace`, and `anyHeap`, and advancing
`A.pool lim st s` by `FreeOnlyEvs`. -/
theorem m5_drop_dirs_tail_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {ret base : BitVec 64} {s0 s : State} {stk m : Nat}
    {ds : List DirGhost}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hm_lo : 1 ≤ m) (hm_hi : m ≤ 7)
    (hlen : ds.length = 8 - m)
    (hA : AllocContractsFsPlaced A lim H)
    (hext : mainFrameSize + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hs : InMainPlaced CodeOk s0 s 0xc70)
    (hx23 : s.readReg64 (.gpr 23#5) = base)
    (hx26 : s.readReg64 (.gpr 26#5) = BitVec.ofNat 64 m)
    (hdone : ∀ (sm : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      InMainPlaced CodeOk s0 sm 0xf70 →
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      sm.fs = s.fs → sm.trace = s.trace →
      SepWPp (mProgPlaced H) ret sm
        (memRegion base (0x28 * (8 - m)) ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          stackAt s.sp (stk - mainFrameSize) ∗ anyHeap ∗ F) Q Qp oom) :
    SepWPp (mProgPlaced H) ret s
      (dirsAt A.repAlloc base ds ∗
        A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗ anyHeap ∗ F) Q Qp oom := by
  refine SepWPp.weaken_pre (P' :=
      dirsVecAt A.repAlloc (base + BitVec.ofNat 64 (0x28 * 0)) ds ∗
        A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗ (anyHeap ∗ F)) ?_ ?_
  · simp only [Nat.mul_zero, BitVec.add_zero]
    have hpre1 :
        dirsAt A.repAlloc base ds ∗ A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗
          anyHeap ∗ F =
        (dirsAt A.repAlloc base ds ∗ anyHeap) ∗
          (A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) := by
      sep_ac_rfl
    have hpre2 :
        (dirsVecAt A.repAlloc base ds ∗ anyHeap) ∗
          (A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) =
        dirsVecAt A.repAlloc base ds ∗ A.pool lim st s ∗ stackAt s.sp (stk - mainFrameSize) ∗
          (anyHeap ∗ F) := by
      sep_ac_rfl
    rw [hpre1, ← hpre2]
    exact sepConj_mono_left (dirsAt_absorb A.repAlloc base ds)
  · refine dropStage_0_placed (st := st) hm_lo hm_hi (by simpa using hlen) hA hext hstk64
      hs hx23 hx26 ?_
    intro sm evs hf hsm hx19 hx22 hx24 hfs htr
    simp only [Nat.mul_zero, BitVec.add_zero, Nat.sub_zero]
    refine SepWPp.weaken_pre (P' :=
      memRegion base (0x28 * (8 - m)) ∗
        A.pool lim (M.stepEvents evs st) sm ∗ stackAt s.sp (stk - mainFrameSize) ∗ anyHeap ∗ F)
      (Entails.of_eq (by sep_ac_rfl)) ?_
    exact hdone sm evs hf hsm hx19 hx22 hx24 hfs htr

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropLoopsPlacedBudget
