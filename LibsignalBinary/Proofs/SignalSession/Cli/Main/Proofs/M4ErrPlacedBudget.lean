/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.FreeArgsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4ErrPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import ProofLib.SepLogic.WP.Structural

/-!
# Budget-Threaded Post-`run` Discriminant Check & Error Exit for `main_m4` (Block `617`)

Budget-threaded verification of the post-`signal_session::run` discriminant check (`M+0x7a4 .. M+0x7ac`)
and `M+0xb24` error cleanup block under `RustCliAllocBudget M`, threading `A.pool` into
`ExitKPoolPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsρ)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.RustHeap (RustAlloc vecBuf)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (InMainPlaced LocalsWF LsCodeInv argsBuf cell locals localsBound localsCtx localsEnd
   locals_focus locals_to_memRegion mPcPlaced_eq mProgPlaced mProgPlaced_eq mainFrameSize mainOom
   mainSaved main_call_rocl ownedBytes retMem sepWPp_seq_codeOk stackAt_split_ge)
open CryptoVerification.SignalSession.Cli.MainHops.M4Placed
  (ownedBytes_dealloc ownedBytes_zero_entails_emp)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4ErrPlacedBudget

open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget RustLayoutOk rustDeallocEvents)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
  (ExitKPlaced MainCalleesBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlacedBudget
  (main_dealloc_fs_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.FreeArgsPlacedBudget
  (free_args_pool_placed_proof)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget
  (ExitKPoolPlaced exitKPoolPlaced_of_exitKPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] ProofLib.bv_sub_add_lit
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem sepWPp_weaken_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P ⊢ P') (h : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  exact h R (Satisfies.mono (sepConj_mono_left hP) hm) hL

private theorem pool_congr_vm {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) {s' : State}
    (hbs : s'.brkStart = s.brkStart) (hbrk : s'.brk = s.brk)
    (htp : s'.tpidrEl0 = s.tpidrEl0) (hphys : s'.physMemAvail = s.physMemAvail)
    (hperm : ∀ a : BitVec 64, s'.mem.perm a = s.mem.perm a)
    (hfs : s'.fs = s.fs := by first | rfl | simp +zetaDelta only [wp_norm, arm64_norm]) :
    A.pool lim st s' = A.pool lim st s :=
  A.pool_of_vmPreserved ⟨⟨hbs, hbrk, htp⟩, hphys, hperm, LibsignalBinary.Heap.FdsHiFrame.of_fs_eq hfs⟩

private theorem m4_argsBuf_zero_entails_emp_p (A : RustAlloc) (buf : BitVec 64)
    (ps : List (BitVec 64 × List (BitVec 8))) :
    argsBuf A 0 buf ps ⊢ emp := by
  unfold argsBuf vecBuf
  simp only [↓reduceIte]
  exact Entails.pure_left fun _ => Entails.refl emp

/-! ## 1. `M+0xb24` Error Exit Block (Free Input + Free `args` + `ExitKPoolPlaced`) -/

private theorem m4_after_input_free_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {s0 s : State}
    {stk hookStack resStack : Nat} {capArgs buf : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {G : Nat → State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max extHookStack hookStack ≤ stk)
    (hs : InMainPlaced CodeOk s0 s 0xb3c)
    (hw26 : (s.readReg64 (.gpr 26#5)).setWidth 32 = 1#32)
    (hx24 : s.readReg64 (.gpr 24#5) = capArgs)
    (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hG : ∀ s', s'.trace = s.trace → s'.fs = s.fs → G 1 s')
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk G Q Qp) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (argsBuf A.repAlloc capArgs buf ps ∗ mainSaved s0 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ anyHeap)
      Q Qp (mainOom s0) := by
  have hpc : s.pc = (blkPl_617).base + 2876#64 := hs.pc
  have hrun : s.status = .Running := hs.run
  by_cases hcap : capArgs = 0
  · subst hcap
    refine sepWPp_weaken_pre (sepConj_mono_left (m4_argsBuf_zero_entails_emp_p A.repAlloc buf ps)) ?_
    rw [emp_sepConj, mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 2944#64) hs.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv_ret
    refine SepWPp.congr_pre ?_
      (hexit _ st 1
        ⟨InMainPlaced.mk_step hs
          (by simp only [mPcPlaced_eq, arm64_norm, *])
          (by simp only [arm64_norm, hrun])
          (by simp only [arm64_norm])
          (by simp only [arm64_norm])
          hinv_ret
          (by simp only [calleeSavedVRegs, arm64_norm]),
         by simpa only [arm64_norm] using hw26⟩
        (hG _ (by simp only [arm64_norm]) (by simp only [arm64_norm])))
    unfold retMem
    rw [RustCliAllocBudget.atState_pool]
    conv => rhs; rw [pool_congr_vm A lim st s (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
  · have hcbnz : (capArgs != 0#64) = true := bne_iff_ne.mpr hcap
    have hbeq : (capArgs == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 2928#64) hs.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv_b70
    refine SepWPp.congr_pre ?_
      (free_args_pool_placed_proof (st := st) (ps := ps) hc hstk
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
        hexit)
    conv => rhs; rw [pool_congr_vm A lim st s (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]

/-- Full error block from `M+0xb24` (`cbz x23, 0xbc0`; dealloc input if `inCap ≠ 0`; set `w26 = 1`;
dealloc `args` if `capArgs ≠ 0`; enter `ExitKPoolPlaced` at `M+0xb80`). -/
theorem m4_step_err_block_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {s0 s : State}
    {stk hookStack resStack : Nat} {inCap inPtr capArgs buf : BitVec 64}
    {inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {G : Nat → State → Prop} {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max extHookStack hookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 64)
    (hs : InMainPlaced CodeOk s0 s 0xb24)
    (hx23 : s.readReg64 (.gpr 23#5) = inCap)
    (hx24 : s.readReg64 (.gpr 24#5) = capArgs)
    (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hG : ∀ s', s'.trace = s.trace → s'.fs = s.fs → G 1 s')
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk G Q Qp) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr] ∗
        argsBuf A.repAlloc capArgs buf ps ∗ mainSaved s0 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ anyHeap)
      Q Qp (mainOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hext_le : extHookStack ≤ stk - mainFrameSize := by omega
  have hfsp_collapse :
      locals fsp [cell fsp 0x50 inPtr] ⊢ memRegion fsp 0x480 := by
    refine locals_to_memRegion fsp [cell fsp 0x50 inPtr] (by simp [LocalsWF]) ?_
    intro o n P hm
    simp only [cell, List.mem_singleton, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl, rfl⟩
    exact ProofLib.pointsTo64_entails_memRegion _ _
  by_cases hin : inCap = 0
  · subst hin
    have hpre0 :
        ownedBytes A.repAlloc 0 inPtr (BitVec.ofNat 64 inp.length) inp ∗
          locals fsp [cell fsp 0x50 inPtr] ∗
          argsBuf A.repAlloc capArgs buf ps ∗ mainSaved s0 ∗
          stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s ∗ anyHeap ⊢
        argsBuf A.repAlloc capArgs buf ps ∗ mainSaved s0 ∗
          memRegion fsp 0x480 ∗
          stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s ∗ anyHeap := by
      refine Entails.trans
        (sepConj_mono
          (ownedBytes_zero_entails_emp A.repAlloc inPtr (BitVec.ofNat 64 inp.length) inp)
          (sepConj_mono_left hfsp_collapse)) ?_
      rw [emp_sepConj]
      exact Entails.of_eq (by sep_ac_rfl)
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
    have hpool_bc0 : A.pool lim st s = A.pool lim st sbc0 :=
      (pool_congr_vm A lim st s (by simp only [sbc0, arm64_norm]) (by simp only [sbc0, arm64_norm])
        (by simp only [sbc0, arm64_norm]) (by simp only [sbc0, arm64_norm])
        (fun _ => by simp only [sbc0, arm64_norm])).symm
    have hpc_bc0 : sbc0.pc = (blkPl_617).base + 3008#64 := rfl
    have hrun_bc0 : sbc0.status = .Running := hs_bc0.run
    rw [hpool_bc0]
    by_cases hcap : capArgs = 0
    · subst hcap
      refine sepWPp_weaken_pre (sepConj_mono_left (m4_argsBuf_zero_entails_emp_p A.repAlloc buf ps)) ?_
      rw [emp_sepConj]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 2944#64) hs_bc0.inv
      wp_steps
      apply SepWP.done
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hrun_bc0])
      intro hinv_ret
      refine SepWPp.congr_pre ?_
        (hexit _ st 1
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
            ((by simp only [arm64_norm] : _ = sbc0.fs).trans hfs_bc0)))
      unfold retMem
      dsimp only [fsp, mainFrameSize]
      rw [RustCliAllocBudget.atState_pool]
      conv =>
        rhs
        rw [pool_congr_vm A lim st sbc0 (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (fun _ => by simp only [arm64_norm])]
    · have hcbnz : (capArgs != 0#64) = true := bne_iff_ne.mpr hcap
      have hbeq : (capArgs == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 2928#64) hs_bc0.inv
      wp_steps
      apply SepWP.done
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hrun_bc0])
      intro hinv_b70
      refine SepWPp.congr_pre ?_
        (free_args_pool_placed_proof (st := st) (ps := ps) hc hstk
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
          hexit)
      dsimp only [fsp, mainFrameSize]
      conv =>
        rhs
        rw [pool_congr_vm A lim st sbc0 (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (fun _ => by simp only [arm64_norm])]
  ·
    have hdealloc := main_dealloc_fs_placed_ok hc.allocFs
    have hbeq : (inCap == 0#64) = false := beq_eq_false_iff_ne.mpr hin
    refine sepWPp_weaken_pre (sepConj_mono_left (ownedBytes_dealloc A.repAlloc hin)) ?_
    rw [sepConj_assoc, sepConj_assoc]
    apply SepWPp.pure_left
    intro hlay
    have hrlay : RustLayoutOk inCap.toNat 1 := ⟨hlay, by decide⟩
    have hfoc := locals_focus fsp [] 0x50 8 ((fsp + 0x50#64) ↦₆₄ inPtr) []
    change SepWPp _ _ _
      (A.repAlloc.live inPtr inCap.toNat 1 ∗ memRegion inPtr inCap.toNat ∗
        locals fsp ([] ++ (0x50, 8, (fsp + 0x50#64) ↦₆₄ inPtr) :: []) ∗
        argsBuf A.repAlloc capArgs buf ps ∗ mainSaved s0 ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s ∗ anyHeap) _ _ _
    rw [hfoc, A.repAlloc_live_norm]
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
    refine main_call_rocl (inPtr, inCap.toNat, 1, st) hdealloc hinv_da
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm]; exact hsp_al)
      (ret_pc := (blkPl_617).base + 2876#64)
      (by simp only [arm64_norm])
      (F := (((fsp + 0x50#64) ↦₆₄ inPtr) ∗ localsCtx fsp 0 [] 0x50 8 []) ∗
        argsBuf A.repAlloc capArgs buf ps ∗ mainSaved s0 ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
          (stk - mainFrameSize - extHookStack) ∗
        anyHeap)
      ?_
      (hnext := fun sf hinv_f hpcm hrunm hspm hcsm => ?_)
    · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
        LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
      conv =>
        arg 2
        rw [pool_congr_vm A lim st s (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (fun _ => by simp only [arm64_norm])]
      have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
      have hls_2876 :
          LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 ((blkPl_617).base + 2876#64) :=
        LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_blockPlacement_base_add 617
          2876#64 (by decide) (by decide)
      simp only [arm64_norm, h1, hrlay, hls_2876, and_self, pure_true, emp_sepConj, sepConj_assoc]
      rw [hsp_eq]
      exact Entails.of_eq (by sep_ac_rfl)
    · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
        LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
      rw [sepConj_assoc, sepConj_assoc]
      apply SepWPp.pure_left; intro hfs_f
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
        (m4_after_input_free_pool_placed (st := M.stepEvents (rustDeallocEvents inCap.toNat 1) st)
          (ps := ps) hc hstk hs_b3c hw26_f hx24_f hx19_f
          (fun s' htr' hfs' => hG s' (htr'.trans htr_eq) (hfs'.trans hfs_eq))
          hexit)
      try simp only [arm64_norm]
      rw [hsp_eq]
      have hloc_collapse :
          ((fsp + 0x50#64) ↦₆₄ inPtr ∗ localsCtx fsp 0 [] 0x50 8 []) ⊢ memRegion fsp 0x480 :=
        hfoc ▸ hfsp_collapse
      refine Entails.trans (Entails.of_eq ?_)
        (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono hloc_collapse
              (sepConj_mono_left (Entails.of_eq hsp_split.symm)))))
      sep_ac_rfl

theorem m4_step_err_block_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {s0 s : State}
    {stk hookStack resStack : Nat} {inCap inPtr capArgs buf : BitVec 64}
    {inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {G : Nat → State → Prop} {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max extHookStack hookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 64)
    (hs : InMainPlaced CodeOk s0 s 0xb24)
    (hx23 : s.readReg64 (.gpr 23#5) = inCap)
    (hx24 : s.readReg64 (.gpr 24#5) = capArgs)
    (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hG : ∀ s', s'.trace = s.trace → s'.fs = s.fs → G 1 s')
    (hexit : ExitKPlaced CodeOk H A s0 stk G Q Qp) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr] ∗
        argsBuf A.repAlloc capArgs buf ps ∗ mainSaved s0 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ anyHeap)
      Q Qp (mainOom s0) :=
  m4_step_err_block_pool_placed hc hstk hstk64 hs hx23 hx24 hx19 hG
    (exitKPoolPlaced_of_exitKPlaced (lim := lim) hexit)

/-! ## 2. `M+0x7a4 .. M+0x7ac` Discriminant Check (`Err` vs `Ok`) -/

/-- When `[sp + 0x1b8] = 0xffff_ffff_ffff_ffff#64`, `M+0x7a4 .. M+0x7ac` branches to `M+0xb24`. -/
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
        (((s.sp + 0x1b8#64) ↦₆₄ 0xffff_ffff_ffff_ffff#64) ∗ F)
        Q Qp (mainOom s0)) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (((s.sp + 0x1b8#64) ↦₆₄ 0xffff_ffff_ffff_ffff#64) ∗ F)
      Q Qp (mainOom s0) :=
  CryptoVerification.SignalSession.Cli.MainHops.m4_step_check_err_placed hs hk

/-- When `[sp + 0x1b8] = cap` with `cap.toNat < 2 ^ 63`, `M+0x7a4 .. M+0x7ac` falls through to
`M+0x7b0`. -/
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
      Q Qp (mainOom s0) :=
  CryptoVerification.SignalSession.Cli.MainHops.m4_step_check_ok_placed hs hcap hk

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4ErrPlacedBudget
