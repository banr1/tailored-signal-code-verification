/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropPanicsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `(String, Vec<u8>)` Entry Drop Loops for `main` Hop M5 (Block `617`)

Verifies the generic 14-instruction `(String, Vec<u8>)` slice drop loop (`m5_drop_one_entry_placed`,
`m5_drop_loop_head_placed`, `m5_drop_loop_body_placed`) and its Block `617` instantiations at
`(0xa84, 0xabc)` and `(0xc04, 0xc3c)`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.CodeLayout
open M5DropPlacedHelpers

private theorem m5_drop_entry_field1_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {h exit : Nat} {regs : DropLoopRegsPlaced} [c : DropLoopCodePlaced h exit regs]
    {A : RustAlloc} {H : LibsignalHooks}
    {ret base : BitVec 64} {s0 s : State} {stk : Nat}
    {bs : List (BitVec 8)} {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A H)
    (hext : mainFrameSize + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hs : InMainPlaced CodeOk s0 s (h + 12))
    (hrp : s.readReg64 (.gpr regs.rp) = base + 32#64)
    (hnext : ∀ sm : State,
      InMainPlaced CodeOk s0 sm (h + 32) →
      (∀ r : BitVec 5, 19 ≤ r.toNat → r.toNat ≤ 29 → sm.readReg64 (.gpr r) = s.readReg64 (.gpr r)) →
      sm.fs = s.fs → sm.trace = s.trace →
      SepWPp (mProgPlaced H) ret sm
        (memRegion base 24 ∗ A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) Q Qp oom) :
    SepWPp (mProgPlaced H) ret s
      (vecU8 A base bs ∗ A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) Q Qp oom := by
  unfold vecU8 vecU8At
  simp only [sepExists_sepConj_left]
  apply SepWPp.exists_elim; intro cap
  apply SepWPp.exists_elim; intro ptr
  simp only [sepConj_assoc]
  rw [show vecHeader base cap ptr (BitVec.ofNat 64 bs.length) ∗
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
        A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (vecHeader base cap ptr (BitVec.ofNat 64 bs.length) ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
          A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) by ac_rfl]
  apply SepWPp.pure_elim
  rintro ⟨hlen, hcap_lt, _⟩
  have hpc := hs.pc
  have hrun := hs.run
  have hal := hs.spAligned_state
  let bl1 : BitVec 64 := (lsρ lsRustDeallocSymCli - (blkPl_617).base) - BitVec.ofNat 64 (h + 28)
  have f12 := c.f12 H
  have f16 := c.f16 H
  have f20 := c.f20 H
  have f24 := c.f24 H
  have f28 : (mProgPlaced H).fetch (mPcPlaced (h + 28)) = some (Instr.bl bl1) := c.f28 H
  have hbl1 : mPcPlaced h + 28#64 + bl1 = lsρ lsRustDeallocSymCli := by
    rw [mPcPlaced_add h 28]
    exact mPcPlaced_bl_dealloc (h + 28)
  rw [← mPcPlaced_add h 12] at hpc f12
  rw [← mPcPlaced_add h 16] at f16
  rw [← mPcPlaced_add h 20] at f20
  rw [← mPcPlaced_add h 24] at f24
  rw [← mPcPlaced_add h 28] at f28
  by_cases hcap0 : cap = 0
  · subst hcap0
    simp only [ite_true, emp_sepConj]
    apply seq_sepWP_pl (mid := mPcPlaced h + 32#64)
    unfold vecHeader
    cases regs <;>
      (dsimp only [DropLoopRegsPlaced.rpSp, DropLoopRegsPlaced.rp] at hrp f12 f16 f20 f24 f28;
       generalize hloop : mPcPlaced h = loopBase at hpc f12 f16 f20 f24 f28 ⊢;
       generalize hprog : mProgPlaced H = prog at f12 f16 f20 f24 f28 ⊢;
       wp_steps;
       apply SepWP.done;
       · rfl;
       · exact hrun;
       clear f12 f16 f20 f24 f28;
       subst hprog hloop;
       intro hpcm hrunm;
       rw [mPcPlaced_add h 32] at hpcm hrunm ⊢;
       refine SepWPp.weaken_pre
         (sepConj_mono_left (vecHeader_to_memRegion24 base 0#64 ptr (BitVec.ofNat 64 bs.length))) ?_;
       refine hnext _
         (InMainPlaced.step_pure hs hpcm hrunm)
         ?_ (by simp only [m5_st_pl]) (by simp only [m5_st_pl]);
       intro r hlo hhi;
       m5_cs_pl hlo hhi)
  · simp only [hcap0, ite_false]
    change cap ≠ 0#64 at hcap0
    have hlay := layoutOk_u8_of_cap_ne_zero hcap0 hcap_lt
    have hmerge :
        (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
          memRegion ptr cap.toNat :=
      ProofLib.pointsToBytes_memRegion_entails ptr bs cap.toNat hlen (by omega)
    apply seq_sepWP_pl (mid := mPcPlaced h + 28#64 + bl1)
    unfold vecHeader
    cases regs <;>
      (dsimp only [DropLoopRegsPlaced.rpSp, DropLoopRegsPlaced.rp] at hrp f12 f16 f20 f24 f28;
       generalize hloop : mPcPlaced h = loopBase at hpc f12 f16 f20 f24 f28 ⊢;
       generalize hprog : mProgPlaced H = prog at f12 f16 f20 f24 f28 ⊢;
       wp_steps;
       apply SepWP.done;
       · rfl;
       · exact hrun;
       clear f12 f16 f20 f24 f28;
       subst hprog hloop;
       intro hpcm hrunm;
       rw [hbl1] at hpcm hrunm ⊢;
       refine step_dealloc_placed (sub := stk - mainFrameSize) (F := memRegion base 24 ∗ F)
         hA (by omega) (by omega)
         (codeOk_pure hs.inv) hpcm hrunm
         (by simpa only [State.spAligned, m5_st_pl] using hal)
         (by simp only [m5_st_pl] : _ = mPcPlaced h + 32#64)
         (by simp only [m5_st_pl] : _ = ptr)
         (by simp only [m5_st_pl] : (_ : BitVec 64).toNat = cap.toNat)
         (by simp only [m5_st_pl]; decide)
         hlay
         ?_ ?_;
       · have hhdr :
             (base ↦₆₄ cap) ∗ ((base + 8#64) ↦₆₄ ptr) ∗
               ((base + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ⊢
               memRegion base 24 :=
           vecHeader_to_memRegion24 base cap ptr (BitVec.ofNat 64 bs.length)
         have hpre_eq :
             ((base ↦₆₄ cap) ∗ ((base + 8#64) ↦₆₄ ptr) ∗
               ((base + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
               (A.live ptr cap.toNat 1 ∗ ((ptr ↦ₛ bs) ∗
                 memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) ∗
               A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F ⊢
             A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗ A.pool ∗
               stackAt s.sp (stk - mainFrameSize) ∗ (memRegion base 24 ∗ F) := by
           refine Entails.trans (sepConj_mono hhdr (sepConj_mono_left (sepConj_mono_right hmerge))) ?_
           exact Entails.of_eq (by ac_rfl)
         simpa only [sepConj_assoc, m5_st_pl] using hpre_eq
       · intro sm hpcm' hrunm' hspm' hcsm hinv' hfsm htrm
         rw [mPcPlaced_add h 32] at hpcm'
         have hsp_eq : sm.sp = s.sp := by simpa only [m5_st_pl] using hspm'
         have hcs_s : ∀ r : BitVec 5, 19 ≤ r.toNat → r.toNat ≤ 29 →
             sm.readReg64 (.gpr r) = s.readReg64 (.gpr r) := by
           intro r hlo hhi
           rw [calleeSaved_read_gpr hcsm r hlo hhi]
           m5_cs_pl hlo hhi
         have hfp_eq : sm.readReg64 .fp = s.readReg64 .fp := by
           simpa only [m5_st_pl] using hcsm.2.2.2.2.2.2.2.2.2.2.1
         have hvregs_eq : calleeSavedVRegs sm = calleeSavedVRegs s := by
           simpa only [calleeSavedVRegs, m5_st_pl] using hcsm.2.2.2.2.2.2.2.2.2.2.2
         refine SepWPp.weaken_pre (P' :=
           memRegion base 24 ∗ A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F)
           (Entails.of_eq (by simp only [m5_st_pl]; ac_rfl)) ?_
         exact hnext sm
           (hs.mk_step hpcm' hrunm' hsp_eq hfp_eq hinv' hvregs_eq)
           hcs_s
           (by simpa only [m5_st_pl] using hfsm)
           (by simpa only [m5_st_pl] using htrm))

private theorem m5_drop_entry_field2_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {h exit : Nat} {regs : DropLoopRegsPlaced} [c : DropLoopCodePlaced h exit regs]
    {A : RustAlloc} {H : LibsignalHooks}
    {ret base : BitVec 64} {s0 s : State} {stk : Nat}
    {bs : List (BitVec 8)} {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A H)
    (hext : mainFrameSize + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hs : InMainPlaced CodeOk s0 s (h + 32))
    (hrp : s.readReg64 (.gpr regs.rp) = base + 32#64)
    (hnext : ∀ sm : State,
      InMainPlaced CodeOk s0 sm h →
      (∀ r : BitVec 5, 19 ≤ r.toNat → r.toNat ≤ 29 → sm.readReg64 (.gpr r) = s.readReg64 (.gpr r)) →
      sm.fs = s.fs → sm.trace = s.trace →
      SepWPp (mProgPlaced H) ret sm
        (memRegion (base + 24#64) 24 ∗ A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) Q Qp oom) :
    SepWPp (mProgPlaced H) ret s
      (vecU8 A (base + 24#64) bs ∗ A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) Q Qp oom := by
  unfold vecU8 vecU8At
  simp only [sepExists_sepConj_left]
  apply SepWPp.exists_elim; intro cap
  apply SepWPp.exists_elim; intro ptr
  simp only [sepConj_assoc]
  rw [show vecHeader (base + 24#64) cap ptr (BitVec.ofNat 64 bs.length) ∗
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
        A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (vecHeader (base + 24#64) cap ptr (BitVec.ofNat 64 bs.length) ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
          A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) by ac_rfl]
  apply SepWPp.pure_elim
  rintro ⟨hlen, hcap_lt, _⟩
  have hvh :
      vecHeader (base + 24#64) cap ptr (BitVec.ofNat 64 bs.length) =
        ((base + 24#64) ↦₆₄ cap) ∗ ((base + 32#64) ↦₆₄ ptr) ∗
          ((base + 40#64) ↦₆₄ BitVec.ofNat 64 bs.length) := by
    unfold vecHeader
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [hvh]
  have hpc := hs.pc
  have hrun := hs.run
  have hal := hs.spAligned_state
  let bl2 : BitVec 64 := (lsρ lsRustDeallocSymCli - (blkPl_617).base) - BitVec.ofNat 64 (h + 48)
  have f32 := c.f32 H
  have f36 := c.f36 H
  have f40 := c.f40 H
  have f44 := c.f44 H
  have f48 : (mProgPlaced H).fetch (mPcPlaced (h + 48)) = some (Instr.bl bl2) := c.f48 H
  have f52 := c.f52 H
  have hbl2 : mPcPlaced h + 48#64 + bl2 = lsρ lsRustDeallocSymCli := by
    rw [mPcPlaced_add h 48]
    exact mPcPlaced_bl_dealloc (h + 48)
  rw [← mPcPlaced_add h 32] at hpc f32
  rw [← mPcPlaced_add h 36] at f36
  rw [← mPcPlaced_add h 40] at f40
  rw [← mPcPlaced_add h 44] at f44
  rw [← mPcPlaced_add h 48] at f48
  rw [← mPcPlaced_add h 52] at f52
  by_cases hcap0 : cap = 0
  · subst hcap0
    simp only [ite_true, emp_sepConj]
    apply seq_sepWP_pl (mid := mPcPlaced h)
    cases regs <;>
      (dsimp only [DropLoopRegsPlaced.rpSp, DropLoopRegsPlaced.rp] at hrp f32 f36 f40 f44 f48 f52;
       generalize hloop : mPcPlaced h = loopBase at hpc f32 f36 f40 f44 f48 f52 ⊢;
       generalize hprog : mProgPlaced H = prog at f32 f36 f40 f44 f48 f52 ⊢;
       wp_steps;
       apply SepWP.done;
       · rfl;
       · exact hrun;
       clear f32 f36 f40 f44 f48 f52;
       subst hprog hloop;
       intro hpcm hrunm;
       have hhdr := vecHeader_to_memRegion24 (base + 24#64) 0 ptr (BitVec.ofNat 64 bs.length);
       rw [hvh] at hhdr;
       refine SepWPp.weaken_pre (sepConj_mono_left hhdr) ?_;
       refine hnext _
         (InMainPlaced.step_pure hs hpcm hrunm)
         ?_ (by simp only [m5_st_pl]) (by simp only [m5_st_pl]);
       intro r hlo hhi;
       m5_cs_pl hlo hhi)
  · simp only [hcap0, ite_false]
    change cap ≠ 0#64 at hcap0
    have hlay := layoutOk_u8_of_cap_ne_zero hcap0 hcap_lt
    have hmerge :
        (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
          memRegion ptr cap.toNat :=
      ProofLib.pointsToBytes_memRegion_entails ptr bs cap.toNat hlen (by omega)
    apply seq_sepWP_pl (mid := mPcPlaced h + 48#64 + bl2)
    cases regs <;>
      (dsimp only [DropLoopRegsPlaced.rpSp, DropLoopRegsPlaced.rp] at hrp f32 f36 f40 f44 f48 f52;
       generalize hloop : mPcPlaced h = loopBase at hpc f32 f36 f40 f44 f48 ⊢;
       generalize hprog : mProgPlaced H = prog at f32 f36 f40 f44 f48 ⊢;
       wp_steps;
       apply SepWP.done;
       · rfl;
       · exact hrun;
       clear f32 f36 f40 f44 f48;
       subst hprog hloop;
       intro hpcm hrunm;
       rw [hbl2] at hpcm hrunm ⊢;
       refine step_dealloc_placed (sub := stk - mainFrameSize) (F := memRegion (base + 24#64) 24 ∗ F)
         hA (by omega) (by omega)
         (codeOk_pure hs.inv) hpcm hrunm
         (by simpa only [State.spAligned, m5_st_pl] using hal)
         (by simp only [m5_st_pl] : _ = mPcPlaced h + 52#64)
         (by simp only [m5_st_pl] : _ = ptr)
         (by simp only [m5_st_pl] : (_ : BitVec 64).toNat = cap.toNat)
         (by simp only [m5_st_pl]; decide)
         hlay
         ?_ ?_;
       · have hhdr := vecHeader_to_memRegion24 (base + 24#64) cap ptr (BitVec.ofNat 64 bs.length)
         rw [hvh] at hhdr
         have hpre_eq :
             (((base + 24#64) ↦₆₄ cap) ∗ ((base + 32#64) ↦₆₄ ptr) ∗
               ((base + 40#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
               (A.live ptr cap.toNat 1 ∗ ((ptr ↦ₛ bs) ∗
                 memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) ∗
               A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F ⊢
             A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗ A.pool ∗
               stackAt s.sp (stk - mainFrameSize) ∗ (memRegion (base + 24#64) 24 ∗ F) := by
           refine Entails.trans (sepConj_mono hhdr (sepConj_mono_left (sepConj_mono_right hmerge))) ?_
           exact Entails.of_eq (by ac_rfl)
         simpa only [sepConj_assoc, m5_st_pl] using hpre_eq
       · intro sm hpcm' hrunm' hspm' hcsm hinv' hfsm htrm
         have hsp_eq : sm.sp = s.sp := by simpa only [m5_st_pl] using hspm'
         have hcs_s : ∀ r : BitVec 5, 19 ≤ r.toNat → r.toNat ≤ 29 →
             sm.readReg64 (.gpr r) = s.readReg64 (.gpr r) := by
           intro r hlo hhi
           rw [calleeSaved_read_gpr hcsm r hlo hhi]
           m5_cs_pl hlo hhi
         have hfp_eq : sm.readReg64 .fp = s.readReg64 .fp := by
           simpa only [m5_st_pl] using hcsm.2.2.2.2.2.2.2.2.2.2.1
         have hvregs_eq : calleeSavedVRegs sm = calleeSavedVRegs s := by
           simpa only [calleeSavedVRegs, m5_st_pl] using hcsm.2.2.2.2.2.2.2.2.2.2.2
         apply seq_sepWP_pl (mid := mPcPlaced h)
         generalize hloop2 : mPcPlaced h = loopBase at hpcm' f52 ⊢
         generalize hprog2 : mProgPlaced H = prog at f52 ⊢
         wp_steps
         apply SepWP.done
         · rfl
         · exact hrunm'
         clear f52
         subst hprog2 hloop2
         intro hpcm2 hrunm2
         refine SepWPp.weaken_pre (P' :=
           memRegion (base + 24#64) 24 ∗ A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F)
           (Entails.of_eq (by simp only [m5_st_pl]; ac_rfl)) ?_
         exact hnext _
           (hs.mk_step hpcm2 hrunm2
             (by simpa only [m5_st_pl] using hsp_eq)
             (by simpa only [m5_st_pl] using hfp_eq)
             (codeOk_pure hinv')
             (by simpa only [calleeSavedVRegs, m5_st_pl] using hvregs_eq))
           (fun r hlo hhi => by m5_cs_pl hlo hhi; exact hcs_s r hlo hhi)
           (by simpa only [m5_st_pl] using hfsm)
           (by simpa only [m5_st_pl] using htrm))

/-- Drop one 48-byte `(String, Vec<u8>)` entry at `base` (`rp = base + 32#64`), running from
`h + 12` back to `h` while preserving all callee-saved GPRs `x19 .. x29` (including `rc` and `rp`),
`sm.fs = s.fs`, and `sm.trace = s.trace`. -/
theorem m5_drop_one_entry_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {h exit : Nat} {regs : DropLoopRegsPlaced} [c : DropLoopCodePlaced h exit regs]
    {A : RustAlloc} {H : LibsignalHooks}
    {ret base : BitVec 64} {s0 s : State} {stk : Nat}
    {e : List (BitVec 8) × List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A H)
    (hext : mainFrameSize + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hs : InMainPlaced CodeOk s0 s (h + 12))
    (hrp : s.readReg64 (.gpr regs.rp) = base + 32#64)
    (hnext : ∀ sm : State,
      InMainPlaced CodeOk s0 sm h →
      (∀ r : BitVec 5, 19 ≤ r.toNat → r.toNat ≤ 29 → sm.readReg64 (.gpr r) = s.readReg64 (.gpr r)) →
      sm.fs = s.fs → sm.trace = s.trace →
      SepWPp (mProgPlaced H) ret sm
        (memRegion base 48 ∗ A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) Q Qp oom) :
    SepWPp (mProgPlaced H) ret s
      (dirEntryAt A e base ∗ A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) Q Qp oom := by
  unfold dirEntryAt
  refine SepWPp.weaken_pre (Entails.of_eq (show
    (vecU8 A base e.1 ∗ vecU8 A (base + 24#64) e.2) ∗
      A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F =
    vecU8 A base e.1 ∗ A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗
      (vecU8 A (base + 24#64) e.2 ∗ F) by ac_rfl)) ?_
  refine m5_drop_entry_field1_placed (h := h) (exit := exit) (regs := regs) hA hext hstk64 hs hrp ?_
  intro s1 hs1 hcs1 hfs1 htr1
  have hrp1 : s1.readReg64 (.gpr regs.rp) = base + 32#64 := by
    have hbounds : 19 ≤ regs.rp.toNat ∧ regs.rp.toNat ≤ 29 := by cases regs <;> decide
    rw [hcs1 regs.rp hbounds.1 hbounds.2, hrp]
  have hsp1 : s1.sp = s.sp := hs1.sp.trans hs.sp.symm
  rw [← hsp1]
  refine SepWPp.weaken_pre (Entails.of_eq (show
    memRegion base 24 ∗ A.pool ∗ stackAt s1.sp (stk - mainFrameSize) ∗
      (vecU8 A (base + 24#64) e.2 ∗ F) =
    vecU8 A (base + 24#64) e.2 ∗ A.pool ∗ stackAt s1.sp (stk - mainFrameSize) ∗
      (memRegion base 24 ∗ F) by ac_rfl)) ?_
  refine m5_drop_entry_field2_placed (h := h) (exit := exit) (regs := regs) hA hext hstk64 hs1 hrp1 ?_
  intro s2 hs2 hcs2 hfs2 htr2
  have hmerge48 : memRegion base 24 ∗ memRegion (base + 24#64) 24 = memRegion base 48 :=
    (ProofLib.memRegion_split' rfl rfl (by decide)).symm
  rw [hsp1]
  refine SepWPp.weaken_pre (P' :=
    memRegion base 48 ∗ A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F)
    (Entails.of_eq (by
      rw [← hmerge48]
      ac_rfl)) ?_
  exact hnext s2 hs2
    (fun r hlo hhi => (hcs2 r hlo hhi).trans (hcs1 r hlo hhi))
    (hfs2.trans hfs1)
    (htr2.trans htr1)

/-- Loop header of the 14-instruction `(String, Vec<u8>)` drop loop (`h → exit`) on Block `617`:
starting at `h` with `rc = BitVec.ofNat 64 (rest.length + 1)` and `rp = prevBase + 32#64`,
decrements `rc`, advances `rp` by `48`, exits to `exit` when `rest = []`, or drops all remaining
entries `rest` at `prevBase + 48#64` into `memRegion (prevBase + 48#64) (rest.length * 48)`. -/
theorem m5_drop_loop_head_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {h exit : Nat} {regs : DropLoopRegsPlaced} [c : DropLoopCodePlaced h exit regs]
    {A : RustAlloc} {H : LibsignalHooks}
    {ret : BitVec 64} {s0 : State} {stk : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A H)
    (hext : mainFrameSize + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (rest : List (List (BitVec 8) × List (BitVec 8))) :
    ∀ {prevBase : BitVec 64} {s : State} {F : SepProp},
      rest.length * 48 < 2 ^ 63 →
      InMainPlaced CodeOk s0 s h →
      s.readReg64 (.gpr regs.rc) = BitVec.ofNat 64 (rest.length + 1) →
      s.readReg64 (.gpr regs.rp) = prevBase + 32#64 →
      (∀ sm : State,
        InMainPlaced CodeOk s0 sm exit →
        regs.keeps s sm →
        sm.fs = s.fs → sm.trace = s.trace →
        SepWPp (mProgPlaced H) ret sm
          (memRegion (prevBase + 48#64) (rest.length * 48) ∗
            A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) Q Qp oom) →
      SepWPp (mProgPlaced H) ret s
        (arrayAt (dirEntryAt A) 48 (prevBase + 48#64) rest ∗
          A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) Q Qp oom := by
  induction rest with
  | nil =>
    intro prevBase s F _ hs hrc hrp hnext
    simp only [List.length_nil, Nat.zero_add, Nat.zero_mul, arrayAt, memRegion_zero] at hrc hnext ⊢
    have hpc := hs.pc
    have hrun := hs.run
    have f0 := c.f0 H
    have f4 := c.f4 H
    have f8 := c.f8 H
    rw [← mPcPlaced_add h 4] at f4
    rw [← mPcPlaced_add h 8] at f8
    apply seq_sepWP_pl (mid := mPcPlaced h + 8#64 + BitVec.ofNat 64 (exit - (h + 8)))
    cases regs <;>
      (dsimp only [DropLoopRegsPlaced.rcZr, DropLoopRegsPlaced.rcSp, DropLoopRegsPlaced.rpSp,
         DropLoopRegsPlaced.rc, DropLoopRegsPlaced.rp] at hrc hrp f0 f4 f8;
       generalize hloop : mPcPlaced h = loopBase at hpc f0 f4 f8 ⊢;
       generalize hprog : mProgPlaced H = prog at f0 f4 f8 ⊢;
       wp_steps;
       apply SepWP.done;
       · rfl;
       · exact hrun;
       clear f0 f4 f8;
       subst hprog hloop;
       intro hpcm hrunm;
       rw [mPcPlaced_add h 8, mPcPlaced_add_sub c.hexit.1] at hpcm hrunm ⊢;
       refine SepWPp.weaken_pre (P' :=
         emp ∗ A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F)
         (Entails.of_eq (by simp only [emp_sepConj, m5_st_pl])) ?_;
       refine hnext _
         (InMainPlaced.step_pure hs hpcm hrunm)
         ?_ (by simp only [m5_st_pl])
         (by simp only [m5_st_pl]);
       intro r hlo hhi hne_rc hne_rp;
       simp only [DropLoopRegsPlaced.rc, DropLoopRegsPlaced.rp] at hne_rc hne_rp;
       have hne_rc' : Reg.gpr r ≠ Reg.gpr _ := fun h => hne_rc (Reg.gpr.inj h);
       have hne_rp' : Reg.gpr r ≠ Reg.gpr _ := fun h => hne_rp (Reg.gpr.inj h);
       repeat first
         | rw [readReg64_setPC_st]
         | rw [readReg64_advancePC_st]
         | rw [readReg64_setPState_st]
         | rw [State.readReg64_writeReg64_ne _ _ _ _ hne_rc']
         | rw [State.readReg64_writeReg64_ne _ _ _ _ hne_rp'])
  | cons e rest ih =>
    intro prevBase s F hlen hs hrc hrp hnext
    simp only [List.length_cons] at hlen hrc
    have hsub :
        BitVec.ofNat 64 (rest.length + 1 + 1) - 1#64 = BitVec.ofNat 64 (rest.length + 1) :=
      ofNat_sub_one_eq
    have hne1 : BitVec.ofNat 64 (rest.length + 1 + 1) ≠ 1#64 :=
      ofNat_ne_of_ne_lt (by omega) (by omega) (by decide)
    have hpc := hs.pc
    have hrun := hs.run
    have f0 := c.f0 H
    have f4 := c.f4 H
    have f8 := c.f8 H
    rw [← mPcPlaced_add h 4] at f4
    rw [← mPcPlaced_add h 8] at f8
    apply seq_sepWP_pl (mid := mPcPlaced h + 12#64)
    cases regs <;>
      (dsimp only [DropLoopRegsPlaced.rcZr, DropLoopRegsPlaced.rcSp, DropLoopRegsPlaced.rpSp,
         DropLoopRegsPlaced.rc, DropLoopRegsPlaced.rp] at hrc hrp f0 f4 f8;
       generalize hloop : mPcPlaced h = loopBase at hpc f0 f4 f8 ⊢;
       generalize hprog : mProgPlaced H = prog at f0 f4 f8 ⊢;
       wp_steps;
       apply SepWP.done;
       · rfl;
       · exact hrun;
       clear f0 f4 f8;
       subst hprog hloop;
       intro hpcm hrunm;
       rw [mPcPlaced_add h 12] at hpcm hrunm ⊢;
       have hs1 := InMainPlaced.step_pure hs hpcm hrunm;
       dsimp only [arrayAt];
       have hsp1 := hs.sp.trans hs1.sp.symm;
       refine SepWPp.weaken_pre (P' :=
         dirEntryAt A e (prevBase + 48#64) ∗
           A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗
           (arrayAt (dirEntryAt A) 48 ((prevBase + 48#64) + 48#64) rest ∗ F))
         (Entails.of_eq (by ac_rfl)) ?_;
       rw [hsp1];
       refine m5_drop_one_entry_placed (c := c) hA hext hstk64 hs1
         (by simp only [DropLoopRegsPlaced.rp, m5_st_pl, BitVec.add_assoc]; rfl) ?_;
       intro s2 hs2 hcs2 hfs2 htr2;
       have hsp2 : s2.sp = s.sp := hs2.sp.trans hs.sp.symm;
       rw [← hsp1];
       refine SepWPp.weaken_pre (P' :=
         arrayAt (dirEntryAt A) 48 ((prevBase + 48#64) + 48#64) rest ∗
           A.pool ∗ stackAt s2.sp (stk - mainFrameSize) ∗
           (memRegion (prevBase + 48#64) 48 ∗ F))
         (Entails.of_eq (by rw [hsp2]; ac_rfl)) ?_;
       refine ih (prevBase := prevBase + 48#64) (by omega) hs2
         (by dsimp only [DropLoopRegsPlaced.rc]; rw [hcs2 _ (by decide) (by decide)]; simp only [m5_st_pl])
         (by dsimp only [DropLoopRegsPlaced.rp]; rw [hcs2 _ (by decide) (by decide)]; simp only [m5_st_pl, BitVec.add_assoc]; rfl) ?_;
       intro sm hsm hkeeps hfsm htrm;
       have hmerge :
           memRegion (prevBase + 48#64) 48 ∗
             memRegion ((prevBase + 48#64) + 48#64) (rest.length * 48) =
             memRegion (prevBase + 48#64) ((rest.length + 1) * 48) :=
         (ProofLib.memRegion_split' (by omega) rfl (by omega)).symm;
       rw [hsp2];
       refine SepWPp.weaken_pre (P' :=
         memRegion (prevBase + 48#64) ((rest.length + 1) * 48) ∗
           A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F)
         (Entails.of_eq (by
           rw [← hmerge]
           ac_rfl)) ?_;
       refine hnext sm hsm ?_
         (hfsm.trans (hfs2.trans (by simp only [m5_st_pl])))
         (htrm.trans (htr2.trans (by simp only [m5_st_pl])));
       intro r hlo hhi hne_rc hne_rp;
       rw [hkeeps r hlo hhi hne_rc hne_rp, hcs2 r hlo hhi];
       simp only [DropLoopRegsPlaced.rc, DropLoopRegsPlaced.rp] at hne_rc hne_rp;
       have hne_rc' : Reg.gpr r ≠ Reg.gpr _ := fun h => hne_rc (Reg.gpr.inj h);
       have hne_rp' : Reg.gpr r ≠ Reg.gpr _ := fun h => hne_rp (Reg.gpr.inj h);
       repeat first
         | rw [readReg64_setPC_st]
         | rw [readReg64_advancePC_st]
         | rw [readReg64_setPState_st]
         | rw [State.readReg64_writeReg64_ne _ _ _ _ hne_rc']
         | rw [State.readReg64_writeReg64_ne _ _ _ _ hne_rp'])

/-- Entry into the 14-instruction `(String, Vec<u8>)` drop loop at `h + 12 → exit` for a non-empty
slice `entries` (`entries ≠ []`, `entries.length * 48 < 2 ^ 63`,
`rc = BitVec.ofNat 64 entries.length`, `rp = ptr + 32#64`):
drops all elements of `entries` into `memRegion ptr (entries.length * 48)`. -/
theorem m5_drop_loop_body_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {h exit : Nat} {regs : DropLoopRegsPlaced} [DropLoopCodePlaced h exit regs]
    {A : RustAlloc} {H : LibsignalHooks}
    {ret ptr : BitVec 64} {s0 s : State} {stk : Nat}
    {entries : List (List (BitVec 8) × List (BitVec 8))}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A H)
    (hext : mainFrameSize + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hne : entries ≠ []) (hlen : entries.length * 48 < 2 ^ 63)
    (hs : InMainPlaced CodeOk s0 s (h + 12))
    (hrc : s.readReg64 (.gpr regs.rc) = BitVec.ofNat 64 entries.length)
    (hrp : s.readReg64 (.gpr regs.rp) = ptr + 32#64)
    (hnext : ∀ sm : State,
      InMainPlaced CodeOk s0 sm exit →
      regs.keeps s sm →
      sm.fs = s.fs → sm.trace = s.trace →
      SepWPp (mProgPlaced H) ret sm
        (memRegion ptr (entries.length * 48) ∗
          A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) Q Qp oom) :
    SepWPp (mProgPlaced H) ret s
      (arrayAt (dirEntryAt A) 48 ptr entries ∗
        A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F) Q Qp oom := by
  cases entries with
  | nil => exact (hne rfl).elim
  | cons e rest =>
    simp only [List.length_cons] at hlen hrc ⊢
    dsimp only [arrayAt]
    refine SepWPp.weaken_pre (P' :=
      dirEntryAt A e ptr ∗ A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗
        (arrayAt (dirEntryAt A) 48 (ptr + 48#64) rest ∗ F))
      (Entails.of_eq (by ac_rfl)) ?_
    refine m5_drop_one_entry_placed (h := h) (exit := exit) (regs := regs) hA hext hstk64 hs hrp ?_
    intro s1 hs1 hcs1 hfs1 htr1
    have hbounds_rc : 19 ≤ regs.rc.toNat ∧ regs.rc.toNat ≤ 29 := by cases regs <;> decide
    have hbounds_rp : 19 ≤ regs.rp.toNat ∧ regs.rp.toNat ≤ 29 := by cases regs <;> decide
    have hrc1 : s1.readReg64 (.gpr regs.rc) = BitVec.ofNat 64 (rest.length + 1) :=
      (hcs1 regs.rc hbounds_rc.1 hbounds_rc.2).trans hrc
    have hrp1 : s1.readReg64 (.gpr regs.rp) = ptr + 32#64 :=
      (hcs1 regs.rp hbounds_rp.1 hbounds_rp.2).trans hrp
    have hsp1 : s1.sp = s.sp := hs1.sp.trans hs.sp.symm
    refine SepWPp.weaken_pre (P' :=
      arrayAt (dirEntryAt A) 48 (ptr + 48#64) rest ∗
        A.pool ∗ stackAt s1.sp (stk - mainFrameSize) ∗
        (memRegion ptr 48 ∗ F))
      (Entails.of_eq (by rw [hsp1]; ac_rfl)) ?_
    refine m5_drop_loop_head_placed (h := h) (exit := exit) (regs := regs) hA hext hstk64 rest
      (prevBase := ptr) (by omega) hs1 hrc1 hrp1 ?_
    intro sm hsm hkeeps hfsm htrm
    rw [hsp1] at *
    have hmerge :
        memRegion ptr 48 ∗ memRegion (ptr + 48#64) (rest.length * 48) =
          memRegion ptr ((rest.length + 1) * 48) :=
      (ProofLib.memRegion_split' (by omega) rfl (by omega)).symm
    refine SepWPp.weaken_pre (P' :=
      memRegion ptr ((rest.length + 1) * 48) ∗
        A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗ F)
      (Entails.of_eq (by
        rw [← hmerge]
        ac_rfl)) ?_
    exact hnext sm hsm
      (fun r hlo hhi hne_rc hne_rp =>
        (hkeeps r hlo hhi hne_rc hne_rp).trans (hcs1 r hlo hhi))
      (hfsm.trans hfs1)
      (htrm.trans htr1)

abbrev m5_drop_loop_head_0xa84_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] :=
  @m5_drop_loop_head_placed _ CodeOk _ 0xa84 0xabc .r20_21 instDropLoopPlaced_0xa84

abbrev m5_drop_loop_body_0xa84_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] :=
  @m5_drop_loop_body_placed _ CodeOk _ 0xa84 0xabc .r20_21 instDropLoopPlaced_0xa84

abbrev m5_drop_loop_head_0xc04_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] :=
  @m5_drop_loop_head_placed _ CodeOk _ 0xc04 0xc3c .r20_21 instDropLoopPlaced_0xc04

abbrev m5_drop_loop_body_0xc04_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] :=
  @m5_drop_loop_body_placed _ CodeOk _ 0xc04 0xc3c .r20_21 instDropLoopPlaced_0xc04

end CryptoVerification.SignalSession.Cli.MainHops
