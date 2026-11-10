/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4LitsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.FreeArgsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable Post-`run` Discriminant Check & Error Exit for `main_m4` (Block `617`)

Verifies the post-`signal_session::run` discriminant check (`M+0x7a4 .. M+0x7ac` branching to
`M+0xb24` on `Err` or `M+0x7b0` on `Ok`) and the `M+0xb24` error cleanup block freeing `input` and
`args` before `ExitKPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.SignalSession.Cli.MainHops.M4Placed
open CryptoVerification.LibsignalPublicApi.StoreKit

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] ProofLib.bv_sub_add_lit
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem m4_argsBuf_zero_entails_emp_p (A : RustAlloc) (buf : BitVec 64)
    (ps : List (BitVec 64 × List (BitVec 8))) :
    argsBuf A 0 buf ps ⊢ emp := by
  unfold argsBuf vecBuf
  simp only [↓reduceIte]
  exact Entails.pure_left fun _ => Entails.refl emp

/-! ## 1. `M+0xb24` Error Exit Block (Free Input + Free `args` + `ExitKPlaced`) -/

private theorem m4_after_input_free_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser} {s0 s : State}
    {stk hookStack resStack : Nat} {capArgs buf : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {G : Nat → State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max extHookStack hookStack ≤ stk)
    (hs : InMainPlaced CodeOk s0 s 0xb3c)
    (hw26 : (s.readReg64 (.gpr 26#5)).setWidth 32 = 1#32)
    (hx24 : s.readReg64 (.gpr 24#5) = capArgs)
    (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hG : ∀ s', s'.trace = s.trace → s'.fs = s.fs → G 1 s')
    (hexit : ExitKPlaced CodeOk H A s0 stk G Q Qp) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (argsBuf A capArgs buf ps ∗ mainSaved s0 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool ∗ anyHeap)
      Q Qp (mainOom s0) := by
  have hpc : s.pc = (blkPl_617).base + 2876#64 := hs.pc
  have hrun : s.status = .Running := hs.run
  by_cases hcap : capArgs = 0
  · subst hcap
    refine sepWPp_weaken_pre (sepConj_mono_left (m4_argsBuf_zero_entails_emp_p A buf ps)) ?_
    rw [emp_sepConj, mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 2944#64) hs.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv_ret
    refine hexit _ 1
      ⟨InMainPlaced.mk_step hs
        (by simp only [mPcPlaced_eq, arm64_norm, *])
        (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        hinv_ret
        (by simp only [calleeSavedVRegs, arm64_norm]),
       by simpa only [arm64_norm] using hw26⟩
      (hG _ (by simp only [arm64_norm]) (by simp only [arm64_norm]))
  · have hcbnz : (capArgs != 0#64) = true := bne_iff_ne.mpr hcap
    have hbeq : (capArgs == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 2928#64) hs.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv_b70
    exact free_args_placed_proof hc hstk
      (Or.inr ⟨InMainPlaced.mk_step hs
        (by simp only [mPcPlaced_eq, arm64_norm, *])
        (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        hinv_b70
        (by simp only [calleeSavedVRegs, arm64_norm]), hcap⟩)
      (by simpa only [arm64_norm] using hw26)
      (by simpa only [arm64_norm] using hx24)
      (by simpa only [arm64_norm] using hx19)
      (fun s' htr' hfs' =>
        hG s' (htr'.trans (by simp only [arm64_norm])) (hfs'.trans (by simp only [arm64_norm])))
      hexit

/-- Full error block from `M+0xb24` (`cbz x23, 0xbc0`; dealloc input if `inCap ≠ 0`; set `w26 = 1`;
dealloc `args` if `capArgs ≠ 0`; enter `ExitKPlaced` at `M+0xb80`). -/
theorem m4_step_err_block_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser} {s0 s : State}
    {stk hookStack resStack : Nat} {inCap inPtr capArgs buf : BitVec 64}
    {inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {G : Nat → State → Prop} {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max extHookStack hookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 64)
    (hs : InMainPlaced CodeOk s0 s 0xb24)
    (hx23 : s.readReg64 (.gpr 23#5) = inCap)
    (hx24 : s.readReg64 (.gpr 24#5) = capArgs)
    (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hG : ∀ s', s'.trace = s.trace → s'.fs = s.fs → G 1 s')
    (hexit : ExitKPlaced CodeOk H A s0 stk G Q Qp) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr] ∗
        argsBuf A capArgs buf ps ∗ mainSaved s0 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool ∗ anyHeap)
      Q Qp (mainOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hext_le : extHookStack ≤ stk - mainFrameSize := by omega
  have hfsp_collapse :
      locals fsp [cell fsp 0x50 inPtr] ⊢ memRegion fsp 0x480 := by
    refine locals_to_memRegion fsp [cell fsp 0x50 inPtr] (by simp [LocalsWF]) ?_
    intro o n P hm
    simp only [cell, List.mem_singleton, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl, rfl⟩
    exact pointsTo64_entails_memRegion _ _
  by_cases hin : inCap = 0
  · subst hin
    have hpre0 :
        ownedBytes A 0 inPtr (BitVec.ofNat 64 inp.length) inp ∗
          locals fsp [cell fsp 0x50 inPtr] ∗
          argsBuf A capArgs buf ps ∗ mainSaved s0 ∗
          stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap ⊢
        argsBuf A capArgs buf ps ∗ mainSaved s0 ∗
          memRegion fsp 0x480 ∗
          stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap := by
      refine Entails.trans
        (sepConj_mono
          (ownedBytes_zero_entails_emp A inPtr (BitVec.ofNat 64 inp.length) inp)
          (sepConj_mono_left hfsp_collapse)) ?_
      rw [emp_sepConj]
      exact Entails.of_eq (by ac_rfl)
    refine sepWPp_weaken_pre hpre0 ?_
    have hpc : s.pc = (blkPl_617).base + 2852#64 := hs.pc
    have hrun : s.status = .Running := hs.run
    rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 3008#64) hs.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv_bc0
    let sbc0 : State := s.setPC ((blkPl_617).base + 3008#64)
    have hs_bc0 : InMainPlaced CodeOk s0 sbc0 0xbc0 :=
      InMainPlaced.mk_step hs
        (by simp only [sbc0, mPcPlaced_eq, arm64_norm])
        (by simp only [sbc0, arm64_norm, hrun])
        (by simp only [sbc0, arm64_norm])
        (by simp only [sbc0, arm64_norm])
        hinv_bc0
        (by simp only [sbc0, calleeSavedVRegs, arm64_norm])
    have hx24_bc0 : sbc0.readReg64 (.gpr 24#5) = capArgs := by
      simpa only [sbc0, arm64_norm] using hx24
    have hx19_bc0 : sbc0.readReg64 (.gpr 19#5) = buf := by
      simpa only [sbc0, arm64_norm] using hx19
    have htr_bc0 : sbc0.trace = s.trace := by simp only [sbc0, arm64_norm]
    have hfs_bc0 : sbc0.fs = s.fs := by simp only [sbc0, arm64_norm]
    have hpc_bc0 : sbc0.pc = (blkPl_617).base + 3008#64 := rfl
    have hrun_bc0 : sbc0.status = .Running := hs_bc0.run
    by_cases hcap : capArgs = 0
    · subst hcap
      refine sepWPp_weaken_pre (sepConj_mono_left (m4_argsBuf_zero_entails_emp_p A buf ps)) ?_
      rw [emp_sepConj]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 2944#64) hs_bc0.inv
      wp_steps
      apply SepWP.done
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hrun_bc0])
      intro hinv_ret
      refine hexit _ 1
        ⟨InMainPlaced.mk_step hs_bc0
          (by simp only [mPcPlaced_eq, arm64_norm])
          (by simp only [arm64_norm, hrun_bc0])
          (by simp only [arm64_norm])
          (by simp only [arm64_norm])
          hinv_ret
          (by simp only [calleeSavedVRegs, arm64_norm]),
         by simp only [arm64_norm]⟩
        (hG _
          ((by simp only [arm64_norm] : _ = sbc0.trace).trans htr_bc0)
          ((by simp only [arm64_norm] : _ = sbc0.fs).trans hfs_bc0))
    · have hcbnz : (capArgs != 0#64) = true := bne_iff_ne.mpr hcap
      have hbeq : (capArgs == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 2928#64) hs_bc0.inv
      wp_steps
      apply SepWP.done
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hrun_bc0])
      intro hinv_b70
      exact free_args_placed_proof hc hstk
        (Or.inr ⟨InMainPlaced.mk_step hs_bc0
          (by simp only [mPcPlaced_eq, arm64_norm])
          (by simp only [arm64_norm, hrun_bc0])
          (by simp only [arm64_norm])
          (by simp only [arm64_norm])
          hinv_b70
          (by simp only [calleeSavedVRegs, arm64_norm]), hcap⟩)
        (by simp only [arm64_norm])
        (by simpa only [arm64_norm] using hx24_bc0)
        (by simpa only [arm64_norm] using hx19_bc0)
        (fun s' htr' hfs' =>
          hG s'
            (htr'.trans ((by simp only [arm64_norm] : _ = sbc0.trace).trans htr_bc0))
            (hfs'.trans ((by simp only [arm64_norm] : _ = sbc0.fs).trans hfs_bc0)))
        hexit
  ·
    have hdealloc := main_dealloc_fs_placed_ok hc.allocFs
    have hbeq : (inCap == 0#64) = false := beq_eq_false_iff_ne.mpr hin
    refine sepWPp_weaken_pre (sepConj_mono_left (ownedBytes_dealloc A hin)) ?_
    rw [sepConj_assoc, sepConj_assoc]
    apply SepWPp.pure_left
    intro hlay
    have hfoc := locals_focus fsp [] 0x50 8 ((fsp + 0x50#64) ↦₆₄ inPtr) []
    change SepWPp _ _ _
      (A.live inPtr inCap.toNat 1 ∗ memRegion inPtr inCap.toNat ∗
        locals fsp ([] ++ (0x50, 8, (fsp + 0x50#64) ↦₆₄ inPtr) :: []) ∗
        argsBuf A capArgs buf ps ∗ mainSaved s0 ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap) _ _ _
    rw [hfoc]
    have hsp_split := stackAt_split_ge fsp hext_le (by omega)
    rw [hsp_split]
    have hpc : s.pc = (blkPl_617).base + 2852#64 := hs.pc
    have hrun : s.status = .Running := hs.run
    have hsp_al : s.spAligned = true := hs.spAligned_state
    have hsp_eq : s.sp = fsp := hs.sp
    rw [← hsp_eq, mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsρ lsRustDeallocSymCli) hs.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv_da
    refine main_call_rocl (inPtr, inCap.toNat, 1) hdealloc hinv_da
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm]; exact hsp_al)
      (ret_pc := (blkPl_617).base + 2876#64)
      (by simp only [arm64_norm])
      (F := (((fsp + 0x50#64) ↦₆₄ inPtr) ∗ localsCtx fsp 0 [] 0x50 8 []) ∗
        argsBuf A capArgs buf ps ∗ mainSaved s0 ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
          (stk - mainFrameSize - extHookStack) ∗
        anyHeap)
      ?_
      (hnext := fun sf hinv_f hpcm hrunm hspm hcsm => ?_)
    · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
      simp only [arm64_norm, sepConj_assoc]
      refine Entails.pure_right hlay ?_
      rw [hsp_eq]
      exact Entails.of_eq (by ac_rfl)
    · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
      rw [sepConj_assoc, sepConj_assoc]
      apply SepWPp.pure_left; intro hfs_f
      rw [sepConj_assoc]
      apply SepWPp.pure_left; intro htr_f
      have hs_b3c : InMainPlaced CodeOk s0 sf 0xb3c :=
        InMainPlaced.mk_step hs hpcm hrunm
          (hspm.trans (by simp only [arm64_norm]))
          (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm]))
          hinv_f
          (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, arm64_norm]))
      have hw26_f : (sf.readReg64 (.gpr 26#5)).setWidth 32 = 1#32 := by
        rw [hcsm.2.2.2.2.2.2.2.1]; simp only [arm64_norm]
      have hx24_f : sf.readReg64 (.gpr 24#5) = capArgs := by
        rw [hcsm.2.2.2.2.2.1]; simpa only [arm64_norm] using hx24
      have hx19_f : sf.readReg64 (.gpr 19#5) = buf := by
        rw [hcsm.1]; simpa only [arm64_norm] using hx19
      have htr_eq : sf.trace = s.trace := htr_f.trans (by simp only [arm64_norm])
      have hfs_eq : sf.fs = s.fs := hfs_f.trans (by simp only [arm64_norm])
      refine sepWPp_weaken_pre ?_
        (m4_after_input_free_placed (ps := ps) hc hstk hs_b3c hw26_f hx24_f hx19_f
          (fun s' htr' hfs' => hG s' (htr'.trans htr_eq) (hfs'.trans hfs_eq))
          hexit)
      simp only [arm64_norm]
      rw [hsp_eq]
      have hloc_collapse :
          ((fsp + 0x50#64) ↦₆₄ inPtr ∗ localsCtx fsp 0 [] 0x50 8 []) ⊢ memRegion fsp 0x480 :=
        hfoc ▸ hfsp_collapse
      refine Entails.trans (Entails.of_eq ?_)
        (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono hloc_collapse
              (sepConj_mono_left (Entails.of_eq hsp_split.symm)))))
      ac_rfl

/-! ## 2. `M+0x7a4 .. M+0x7ac` Discriminant Check (`Err` vs `Ok`) -/

/-- When `[sp + 0x1b8] = 0xffffffffffffffff#64`, `M+0x7a4 .. M+0x7ac` branches to `M+0xb24`. -/
theorem m4_step_check_err_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk]
    {H : LibsignalHooks} {s0 s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hs : InMainPlaced CodeOk s0 s 0x7a4)
    (hk : ∀ s' : State,
      InMainPlaced CodeOk s0 s' 0xb24 →
      CalleeSavedPreserved s s' →
      s'.trace = s.trace →
      s'.fs = s.fs →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (((s.sp + 0x1b8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ F)
        Q Qp (mainOom s0)) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (((s.sp + 0x1b8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ F)
      Q Qp (mainOom s0) := by
  have hpc : s.pc = (blkPl_617).base + 1956#64 := hs.pc
  have hrun : s.status = .Running := hs.run
  have hsp_al : s.spAligned = true := hs.spAligned_state
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 2852#64) hs.inv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  intro hinv'
  exact hk _
    (InMainPlaced.mk_step hs
      (by simp only [mPcPlaced_eq, arm64_norm])
      (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      hinv'
      (by simp only [calleeSavedVRegs, arm64_norm]))
    (calleeSavedPreserved_of_regs
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [calleeSavedVRegs, arm64_norm]))
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])

/-- When `[sp + 0x1b8] = cap` with `cap.toNat < 2 ^ 63`, `M+0x7a4 .. M+0x7ac` falls through to `M+0x7b0`. -/
theorem m4_step_check_ok_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk]
    {H : LibsignalHooks} {s0 s : State} {cap : BitVec 64} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hs : InMainPlaced CodeOk s0 s 0x7a4)
    (hcap : cap.toNat < 2 ^ 63)
    (hk : ∀ s' : State,
      InMainPlaced CodeOk s0 s' 0x7b0 →
      CalleeSavedPreserved s s' →
      s'.trace = s.trace →
      s'.fs = s.fs →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (((s.sp + 0x1b8#64) ↦₆₄ cap) ∗ F)
        Q Qp (mainOom s0)) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (((s.sp + 0x1b8#64) ↦₆₄ cap) ∗ F)
      Q Qp (mainOom s0) := by
  have hneq : (cap + 1#64 == 0#64) = false := by
    rw [beq_eq_false_iff_ne]
    bv_omega
  have hneq2 : (cap == 0xffffffffffffffff#64) = false := by
    rw [beq_eq_false_iff_ne]
    bv_omega
  have hpc : s.pc = (blkPl_617).base + 1956#64 := hs.pc
  have hrun : s.status = .Running := hs.run
  have hsp_al : s.spAligned = true := hs.spAligned_state
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 1968#64) hs.inv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  intro hinv'
  exact hk _
    (InMainPlaced.mk_step hs
      (by simp only [mPcPlaced_eq, arm64_norm])
      (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      hinv'
      (by simp only [calleeSavedVRegs, arm64_norm]))
    (calleeSavedPreserved_of_regs
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [calleeSavedVRegs, arm64_norm]))
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])

end CryptoVerification.SignalSession.Cli.MainHops
