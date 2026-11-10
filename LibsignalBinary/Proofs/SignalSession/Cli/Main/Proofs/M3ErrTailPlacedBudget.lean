/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.LitsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.FreeArgsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ErrTailPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import ProofLib.SepLogic.WP.Structural

/-!
# Budget-Threaded Error-Path Drop Continuations for `main` Hop M3 & Send-Cap (Block `617`)

Budget-threaded verification of Block `617`'s shared error-exit drop continuations (`M+0x650`
through `M+0xb6c`) under `RustCliAllocBudget M`, threading `A.pool` across `__rust_dealloc` calls
into `ExitKPoolPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsρ)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (utf8)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPl_617)
open CryptoVerification.RustHeap (vecBuf)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallV CallW InMainPlaced LocalsWF LsCodeInv addrWords argsBuf callHeap cell coinsLitSym
   locals localsCtx localsFrom locals_to_memRegion mPcPlaced mPcPlaced_eq mProgPlaced
   mProgPlaced_eq mainFrameSize mainLitsBlk617 mainOom mainSaved main_call_rocl ownedBytes
   sepWPp_seq_codeOk)
open CryptoVerification.SignalSession.Cli.MainHops.M3Helpers
  (entails_pure_intro_left ownedBytes_entails_emp_of_cap0 ownedBytes_pure
   ownedBytes_to_dealloc stackAt_sub_split)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ErrTailPlacedBudget

open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget RustLayoutOk rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
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

local macro "pool_eq" : tactic =>
  `(tactic| first |
    ((conv =>
        rhs
        pattern (RustCliAllocBudget.pool _ _ _ _)
        simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm]);
      try rfl))

/-- Focus the `"coins"` read-only literal in `mainLitsBlk617`. -/
abbrev mainLitsBlk617Rest [LibsignalPlacement] : SepProp :=
  CryptoVerification.SignalSession.Cli.MainHops.M3Helpers.mainLitsBlk617Rest

theorem mainLitsBlk617_eq [LibsignalPlacement] :
    mainLitsBlk617 = (lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗ mainLitsBlk617Rest :=
  CryptoVerification.SignalSession.Cli.MainHops.M3Helpers.mainLitsBlk617_eq

private theorem m3_argsBuf_zero_entails_emp_p {M : AllocCostModel} (A : RustCliAllocBudget M)
    (buf : BitVec 64) (ps : List (BitVec 64 × List (BitVec 8))) :
    argsBuf A.repAlloc 0 buf ps ⊢ emp := by
  unfold argsBuf vecBuf
  simp only [↓reduceIte]
  exact Entails.pure_left fun _ => Entails.refl emp

/-- Shared helper invoking `__rust_dealloc(ptr, cap.toNat, 1)` on Block `617` when `st_bl` is
already positioned at `lsρ lsRustDeallocSymCli` with `lr = mPcPlaced retOff` and `cap ≠ 0#64`. -/
theorem call_dealloc_ownedBytes_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {s0 st_bl : State} {stk hookStack resStack retOff : Nat}
    {cap ptr len : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hinv : CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsρ lsRustDeallocSymCli)
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = s0.sp - BitVec.ofNat 64 mainFrameSize)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = mPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = ptr)
    (hx1 : st_bl.readReg64 .x1 = cap)
    (hx2 : st_bl.readReg64 .x2 = 1#64)
    (hcap : cap ≠ 0#64)
    (hnext : ∀ sf : State,
      InMainPlaced CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.fs = st_bl.fs →
      sf.trace = st_bl.trace →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) sf
        (stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents cap.toNat 1) ms) sf ∗ F)
        Q Qp (mainOom s0))
    (hlr_ls : LsRetAddr624 (mPcPlaced retOff) := by
      dsimp only [mPcPlaced]; simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) st_bl
      (ownedBytes A.repAlloc cap ptr len bs ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st_bl ∗ F)
      Q Qp (mainOom s0) := by
  have hdealloc := main_dealloc_fs_placed_ok hc.allocFs
  have hal_bl : st_bl.spAligned = true := by
    simp only [State.spAligned, hsp, mainFrameSize]
    exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hsp0
  have hsub_le : extHookStack ≤ stk - mainFrameSize := by omega
  have hsub64 : stk - mainFrameSize ≤ 2 ^ 64 := by omega
  rw [ownedBytes_pure A.repAlloc cap ptr len bs, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨_, _, hlt_cap, _⟩ => ?_
  set fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  rw [mProgPlaced_eq]
  refine main_call_rocl (CodeOk := CodeOk) (s0 := s0) (ptr, cap.toNat, 1, ms) hdealloc hinv hpc hrun hal_bl
    (ret_pc := mPcPlaced retOff) hlr
    (F := memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
      (stk - mainFrameSize - extHookStack) ∗ F) ?_ (hnext := ?_)
  · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    have hpure : (st_bl.readReg64 .x0 = ptr ∧ (st_bl.readReg64 .x1).toNat = cap.toNat ∧
        (st_bl.readReg64 .x2).toNat = 1 ∧ RustLayoutOk cap.toNat 1 ∧
        LsRetAddr624 (st_bl.readReg64 .lr)) := by
      refine ⟨hx0, by rw [hx1], by rw [hx2]; decide,
        ⟨⟨Nat.pos_of_ne_zero fun h0 => hcap (BitVec.eq_of_toNat_eq (by simpa using h0)),
          ⟨0, rfl⟩, by omega⟩, by decide⟩, by rwa [hlr]⟩
    rw [hsp]
    change ownedBytes A.repAlloc cap ptr len bs ∗ stackAt fsp (stk - mainFrameSize) ∗
      A.pool lim ms st_bl ∗ F ⊢ _
    rw [stackAt_sub_split fsp hsub_le hsub64]
    refine Entails.trans (sepConj_mono_left (ownedBytes_to_dealloc A.repAlloc hcap)) ?_
    rw [A.repAlloc_live_norm]
    conv => rhs; rw [sepConj_assoc]
    apply entails_pure_intro_left hpure
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun hfs_f => ?_
    refine SepWPp.pure_elim fun htr_f => ?_
    have hin_f : InMainPlaced CodeOk s0 sf retOff := {
      inv := hinv_f
      pc := hpc_f
      run := hrun_f
      sp := hsp_f.trans hsp
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
      spAligned := hsp0
    }
    rw [← mProgPlaced_eq]
    refine SepWPp.weaken_pre ?_ (hnext sf hin_f hcs_f hfs_f htr_f)
    rw [hsp, stackAt_sub_split fsp hsub_le hsub64]
    exact Entails.of_eq (by sep_ac_rfl)

/-- `M+0xb6c`: `cbz x24, 0xb80` → `free_args_pool_placed_proof` (`w26 = code`). -/
theorem step_exit_0xb6c_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {s0 st : State}
    {stk hookStack resStack n code : Nat} {buf : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {G : Nat → State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hst : InMainPlaced CodeOk s0 st 0xb6c)
    (hw26 : (st.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hG : ∀ s', s'.trace = st.trace → s'.fs = st.fs → G code s')
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk G Q Qp) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) st
      (argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ anyHeap)
      Q Qp (mainOom s0) := by
  have hstk_free : mainFrameSize + max extHookStack hookStack ≤ stk := by omega
  exact free_args_pool_placed_proof (st := ms) (ps := ps) hc hstk_free (Or.inl hst) hw26 hx24 hx19
    hG hexit

theorem step_exit_0xb6c_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {s0 st : State}
    {stk hookStack resStack n code : Nat} {buf : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {G : Nat → State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hst : InMainPlaced CodeOk s0 st 0xb6c)
    (hw26 : (st.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hG : ∀ s', s'.trace = st.trace → s'.fs = st.fs → G code s')
    (hexit : ExitKPlaced CodeOk H A s0 stk G Q Qp) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) st
      (argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ anyHeap)
      Q Qp (mainOom s0) :=
  step_exit_0xb6c_pool_placed hc hstk hst hw26 hx19 hx24 hG (exitKPoolPlaced_of_exitKPlaced hexit)

/-- `M+0xb1c`: `cbnz x24, 0xb70; b 0xb80` → `free_args_pool_placed_proof` / `ExitKPoolPlaced`
(`w26 = code`). -/
theorem step_exit_0xb1c_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {s0 st : State}
    {stk hookStack resStack n code : Nat} {buf : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {G : Nat → State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hst : InMainPlaced CodeOk s0 st 0xb1c)
    (hw26 : (st.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hG : ∀ s', s'.trace = st.trace → s'.fs = st.fs → G code s')
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk G Q Qp) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) st
      (argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ anyHeap)
      Q Qp (mainOom s0) := by
  have hpc := hst.pc
  have hrun := hst.run
  have hinv := hst.inv
  have hstk_free : mainFrameSize + max extHookStack hookStack ≤ stk := by omega
  rw [mPcPlaced_eq] at hpc
  by_cases hcap : BitVec.ofNat 64 n = 0#64
  · rw [hcap] at hx24 ⊢
    refine SepWPp.weaken_pre (sepConj_mono_left (m3_argsBuf_zero_entails_emp_p A buf ps)) ?_
    rw [emp_sepConj, mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb80#64) hinv
    wp_steps
    apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
      (by (try simp only [arm64_norm, *]); try rfl)
    intro hinv_ret
    refine SepWPp.congr_pre ?_
      (hexit _ ms code
        ⟨{ inv := hinv_ret
           pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
           run := by (try simp only [arm64_norm, *])
           sp := by (try simp only [arm64_norm]); exact hst.sp
           fp := by (try simp only [arm64_norm]); exact hst.fp
           vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hst.vregs
           spAligned := hst.spAligned },
         by simpa only [arm64_norm] using hw26⟩
        (hG _ (by simp only [arm64_norm]) (by simp only [arm64_norm])))
    unfold CryptoVerification.SignalSession.Cli.MainHops.retMem
    rw [RustCliAllocBudget.atState_pool]
    pool_eq
  · have hcbnz : (BitVec.ofNat 64 n != 0#64) = true := bne_iff_ne.mpr hcap
    have hbeq : (BitVec.ofNat 64 n == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb70#64) hinv
    wp_steps
    apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
      (by (try simp only [arm64_norm, *]); try rfl)
    intro hinv_b70
    have hin_b70 : InMainPlaced CodeOk s0 _ 0xb70 := {
      inv := hinv_b70
      pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
      run := by (try simp only [arm64_norm, *])
      sp := by (try simp only [arm64_norm]); exact hst.sp
      fp := by (try simp only [arm64_norm]); exact hst.fp
      vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hst.vregs
      spAligned := hst.spAligned
    }
    refine SepWPp.congr_pre ?_
      (free_args_pool_placed_proof (st := ms) (ps := ps) hc hstk_free (Or.inr ⟨hin_b70, hcap⟩)
        (by simpa only [arm64_norm] using hw26)
        (by simpa only [arm64_norm] using hx24)
        (by simpa only [arm64_norm] using hx19)
        (fun s' htr' hfs' =>
          hG s' (htr'.trans (by simp only [arm64_norm])) (hfs'.trans (by simp only [arm64_norm])))
        hexit)
    pool_eq

theorem step_exit_0xb1c_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {s0 st : State}
    {stk hookStack resStack n code : Nat} {buf : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {G : Nat → State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hst : InMainPlaced CodeOk s0 st 0xb1c)
    (hw26 : (st.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hG : ∀ s', s'.trace = st.trace → s'.fs = st.fs → G code s')
    (hexit : ExitKPlaced CodeOk H A s0 stk G Q Qp) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) st
      (argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ anyHeap)
      Q Qp (mainOom s0) :=
  step_exit_0xb1c_pool_placed hc hstk hst hw26 hx19 hx24 hG (exitKPoolPlaced_of_exitKPlaced hexit)

/-- `M+0xb10`: `mov x0, x27; mov w2, #1; bl __rust_dealloc` → `step_exit_0xb1c_pool_placed`. -/
theorem step_drop_tail_0xb10_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {s0 st : State}
    {stk hookStack resStack n code : Nat} {buf cap ptr len : BitVec 64}
    {bs : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {G : Nat → State → Prop} {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hst : InMainPlaced CodeOk s0 st 0xb10)
    (hx1 : st.readReg64 .x1 = cap)
    (hx27 : st.readReg64 (.gpr 27#5) = ptr)
    (hcap : cap ≠ 0#64)
    (hw26 : (st.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hG : ∀ s', s'.trace = st.trace → s'.fs = st.fs → G code s')
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk G Q Qp) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) st
      (ownedBytes A.repAlloc cap ptr len bs ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ anyHeap)
      Q Qp (mainOom s0) := by
  have hpc := hst.pc
  have hrun := hst.run
  have hinv := hst.inv
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsρ lsRustDeallocSymCli) hinv
  wp_steps
  apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
    (by (try simp only [arm64_norm, *]); try rfl)
  intro hinv1
  refine SepWPp.weaken_pre ?_
    (call_dealloc_ownedBytes_placed (ms := ms) (len := len) (bs := bs)
      (F := argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗ anyHeap)
      hc hstk hstk64 hinv1
      (by (try simp only [arm64_norm, *]); try rfl)
      (by (try simp only [arm64_norm, *]); try rfl)
      (by (try simp only [arm64_norm]); exact hst.sp)
      (by (try simp only [arm64_norm]); exact hst.fp)
      (by (try simp only [calleeSavedVRegs, arm64_norm]); exact hst.vregs)
      hst.spAligned
      (retOff := 0xb1c)
      (by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl)
      (by (try simp only [arm64_norm, *]); try rfl)
      (by (try simp only [arm64_norm, hx1]); try rfl)
      (by (try simp only [arm64_norm]); try rfl)
      hcap fun sf hin_f hcs_f hfs_f htr_f => ?_)
  · pool_eq
    exact Entails.of_eq (by sep_ac_rfl)
  · have hx19_f : sf.readReg64 (.gpr 19#5) = buf := by
      rw [hcs_f.1]; simp only [arm64_norm, hx19]
    have hx24_f : sf.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n := by
      rw [hcs_f.2.2.2.2.2.1]; simp only [arm64_norm, hx24]
    have hw26_f : (sf.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code := by
      rw [hcs_f.2.2.2.2.2.2.2.1]; simpa only [arm64_norm] using hw26
    have htr_sf : sf.trace = st.trace := htr_f.trans (by simp only [arm64_norm])
    have hfs_sf : sf.fs = st.fs := hfs_f.trans (by simp only [arm64_norm])
    refine SepWPp.weaken_pre ?_
      (step_exit_0xb1c_pool_placed (ms := M.stepEvents (rustDeallocEvents cap.toNat 1) ms)
        (ps := ps) hc hstk hin_f hw26_f hx19_f hx24_f
        (fun s' htr' hfs' => hG s' (htr'.trans htr_sf) (hfs'.trans hfs_sf)) hexit)
    exact Entails.of_eq (by sep_ac_rfl)

theorem step_drop_tail_0xb10_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {s0 st : State}
    {stk hookStack resStack n code : Nat} {buf cap ptr len : BitVec 64}
    {bs : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {G : Nat → State → Prop} {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hst : InMainPlaced CodeOk s0 st 0xb10)
    (hx1 : st.readReg64 .x1 = cap)
    (hx27 : st.readReg64 (.gpr 27#5) = ptr)
    (hcap : cap ≠ 0#64)
    (hw26 : (st.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hG : ∀ s', s'.trace = st.trace → s'.fs = st.fs → G code s')
    (hexit : ExitKPlaced CodeOk H A s0 stk G Q Qp) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) st
      (ownedBytes A.repAlloc cap ptr len bs ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ anyHeap)
      Q Qp (mainOom s0) :=
  step_drop_tail_0xb10_pool_placed hc hstk hstk64 hst hx1 hx27 hcap hw26 hx19 hx24 hG
    (exitKPoolPlaced_of_exitKPlaced hexit)

/-- Continuation from `M+0xaf8` dropping `Init`'s bundle
`ownedBytes A.repAlloc w.w4 w.w5 w.w6 bundle`
(`ldr x1, [sp, #0x48]; mov x27, x21; cbnz x1, 0xb10; b 0xb6c`). -/
theorem step_drop_init_0xaf8_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {w : CallW} {s0 st : State}
    {stk hookStack resStack n code : Nat} {buf inPtr : BitVec 64} {bundle : List (BitVec 8)}
    {ps : List (BitVec 64 × List (BitVec 8))} {G : Nat → State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hst : InMainPlaced CodeOk s0 st 0xaf8)
    (hw26 : (st.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx21 : st.readReg64 (.gpr 21#5) = w.w5)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hG : ∀ s', s'.trace = st.trace → s'.fs = st.fs → G code s')
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk G Q Qp) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) st
      (ownedBytes A.repAlloc w.w4 w.w5 w.w6 bundle ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x40 w.w3,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x48 w.w4,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x58 w.w1] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ anyHeap)
      Q Qp (mainOom s0) := by
  set fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hal : st.spAligned = true := hst.spAligned_state
  have hsp : st.sp = fsp := hst.sp
  have hpc := hst.pc
  have hrun := hst.run
  have hinv := hst.inv
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  have hloc_to_mem :
      locals fsp [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1] ⊢
        memRegion fsp 0x480 := by
    refine locals_to_memRegion fsp _ (by simp [LocalsWF]) ?_
    intro o k P hm
    simp only [cell, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact ProofLib.pointsTo64_entails_memRegion _ _
  have hfocus48 : ∀ v : BitVec 64,
      locals fsp [cell fsp 0x40 w.w3, cell fsp 0x48 v, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1] =
      ((fsp + 0x48#64) ↦₆₄ v) ∗
        localsCtx fsp 0 [cell fsp 0x40 w.w3] 0x48 8 [cell fsp 0x50 inPtr, cell fsp 0x58 w.w1] := by
    intro v; simp only [locals, localsFrom, localsCtx]; sep_ac_rfl
  rw [hfocus48 w.w4]
  by_cases hw4 : w.w4 = 0#64
  · rw [hw4]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb6c#64) hinv
    wp_steps
    apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
      (by (try simp only [arm64_norm, *]); try rfl)
    intro hinv1
    have hin1 : InMainPlaced CodeOk s0 _ 0xb6c := {
      inv := hinv1
      pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
      run := by (try simp only [arm64_norm, *])
      sp := by (try simp only [arm64_norm]); exact hst.sp
      fp := by (try simp only [arm64_norm]); exact hst.fp
      vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hst.vregs
      spAligned := hst.spAligned
    }
    refine SepWPp.weaken_pre ?_
      (step_exit_0xb6c_pool_placed (ms := ms) (ps := ps) hc hstk hin1
        (by simpa only [arm64_norm] using hw26)
        (by (try simp only [arm64_norm, hx19]); try rfl)
        (by (try simp only [arm64_norm, hx24]); try rfl)
        (fun s' htr' hfs' =>
          hG s' (htr'.trans (by simp only [arm64_norm])) (hfs'.trans (by simp only [arm64_norm])))
        hexit)
    pool_eq
    have hmerge :
        ((fsp + 0x48#64) ↦₆₄ 0#64) ∗
          localsCtx fsp 0 [cell fsp 0x40 w.w3] 0x48 8 [cell fsp 0x50 inPtr, cell fsp 0x58 w.w1] ⊢
          memRegion fsp 0x480 := by
      rw [← hfocus48 0#64, ← hw4]
      exact hloc_to_mem
    refine Entails.trans (Entails.of_eq (show _ =
      (((fsp + 0x48#64) ↦₆₄ 0#64) ∗
        localsCtx fsp 0 [cell fsp 0x40 w.w3] 0x48 8 [cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]) ∗
      (argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool lim ms st ∗
        (ownedBytes A.repAlloc 0#64 w.w5 w.w6 bundle ∗ anyHeap)) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hmerge
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right
          (entails_anyHeap (ownedBytes A.repAlloc 0#64 w.w5 w.w6 bundle ∗ anyHeap))))))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · have hw4_bne : (w.w4 != 0#64) = true := bne_iff_ne.mpr hw4
    have hw4_beq : (w.w4 == 0#64) = false := beq_false_of_ne hw4
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb10#64) hinv
    wp_steps
    apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
      (by (try simp only [arm64_norm, *]); try rfl)
    intro hinv1
    have hin1 : InMainPlaced CodeOk s0 _ 0xb10 := {
      inv := hinv1
      pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
      run := by (try simp only [arm64_norm, *])
      sp := by (try simp only [arm64_norm]); exact hst.sp
      fp := by (try simp only [arm64_norm]); exact hst.fp
      vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hst.vregs
      spAligned := hst.spAligned
    }
    refine SepWPp.weaken_pre ?_
      (step_drop_tail_0xb10_pool_placed (ms := ms) (len := w.w6) (bs := bundle) (ps := ps)
        hc hstk hstk64 hin1
        (by (try simp only [arm64_norm]); try rfl)
        (by (try simp only [arm64_norm, *]); try rfl)
        hw4
        (by simpa only [arm64_norm] using hw26)
        (by (try simp only [arm64_norm, hx19]); try rfl)
        (by (try simp only [arm64_norm, hx24]); try rfl)
        (fun s' htr' hfs' =>
          hG s' (htr'.trans (by simp only [arm64_norm])) (hfs'.trans (by simp only [arm64_norm])))
        hexit)
    pool_eq
    have hmerge :
        ((fsp + 0x48#64) ↦₆₄ w.w4) ∗
          localsCtx fsp 0 [cell fsp 0x40 w.w3] 0x48 8 [cell fsp 0x50 inPtr, cell fsp 0x58 w.w1] ⊢
          memRegion fsp 0x480 := by
      rw [← hfocus48 w.w4]
      exact hloc_to_mem
    refine Entails.trans (Entails.of_eq (show _ =
      (((fsp + 0x48#64) ↦₆₄ w.w4) ∗
        localsCtx fsp 0 [cell fsp 0x40 w.w3] 0x48 8 [cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]) ∗
      (ownedBytes A.repAlloc w.w4 w.w5 w.w6 bundle ∗ argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim ms st ∗ anyHeap) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left hmerge) ?_
    exact Entails.of_eq (by sep_ac_rfl)

theorem step_drop_init_0xaf8_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {w : CallW} {s0 st : State}
    {stk hookStack resStack n code : Nat} {buf inPtr : BitVec 64} {bundle : List (BitVec 8)}
    {ps : List (BitVec 64 × List (BitVec 8))} {G : Nat → State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hst : InMainPlaced CodeOk s0 st 0xaf8)
    (hw26 : (st.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx21 : st.readReg64 (.gpr 21#5) = w.w5)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hG : ∀ s', s'.trace = st.trace → s'.fs = st.fs → G code s')
    (hexit : ExitKPlaced CodeOk H A s0 stk G Q Qp) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) st
      (ownedBytes A.repAlloc w.w4 w.w5 w.w6 bundle ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x40 w.w3,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x48 w.w4,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x58 w.w1] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ anyHeap)
      Q Qp (mainOom s0) :=
  step_drop_init_0xaf8_pool_placed hc hstk hstk64 hst hw26 hx19 hx21 hx24 hG
    (exitKPoolPlaced_of_exitKPlaced hexit)

/-- Continuation from `M+0xae4` dropping `Call::Init`. -/
theorem step_drop_init_0xae4_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {w : CallW} {s0 st : State}
    {stk hookStack resStack n code : Nat} {buf inPtr : BitVec 64} {peer : AddrV}
    {bundle : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {G : Nat → State → Prop} {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hst : InMainPlaced CodeOk s0 st 0xae4)
    (hw26 : (st.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx21 : st.readReg64 (.gpr 21#5) = w.w5)
    (hx22 : st.readReg64 (.gpr 22#5) = w.w1)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx25 : st.readReg64 (.gpr 25#5) = w.w0)
    (hG : ∀ s', s'.trace = st.trace → s'.fs = st.fs → G code s')
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk G Q Qp) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) st
      (addrWords A.repAlloc peer w.w0 w.w1 w.w2 w.w3 ∗
        ownedBytes A.repAlloc w.w4 w.w5 w.w6 bundle ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x40 w.w3,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x48 w.w4,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x58 w.w1] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ anyHeap)
      Q Qp (mainOom s0) := by
  dsimp only [addrWords]
  rw [sepConj_assoc]
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    ⌜w.w3.setWidth 8 = peer.device⌝ ∗
      (ownedBytes A.repAlloc w.w0 w.w1 w.w2 peer.name ∗
        (ownedBytes A.repAlloc w.w4 w.w5 w.w6 bundle ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x40 w.w3,
             cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x48 w.w4,
             cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr,
             cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x58 w.w1] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim ms st ∗ anyHeap)) by sep_ac_rfl)) ?_
  refine SepWPp.pure_elim fun _ => ?_
  have hpc := hst.pc
  have hrun := hst.run
  have hinv := hst.inv
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  by_cases hw0 : w.w0 = 0#64
  · apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xaf8#64) hinv
    wp_steps
    apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
      (by (try simp only [arm64_norm, *]); try rfl)
    intro hinv1
    have hin1 : InMainPlaced CodeOk s0 _ 0xaf8 := {
      inv := hinv1
      pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
      run := by (try simp only [arm64_norm, *])
      sp := by (try simp only [arm64_norm]); exact hst.sp
      fp := by (try simp only [arm64_norm]); exact hst.fp
      vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hst.vregs
      spAligned := hst.spAligned
    }
    refine SepWPp.weaken_pre ?_
      (step_drop_init_0xaf8_pool_placed (ms := ms) (w := w) (inPtr := inPtr) (bundle := bundle)
        (ps := ps) hc hstk hstk64 hin1
        (by simpa only [arm64_norm] using hw26)
        (by (try simp only [arm64_norm, hx19]); try rfl)
        (by (try simp only [arm64_norm, hx21]); try rfl)
        (by (try simp only [arm64_norm, hx24]); try rfl)
        (fun s' htr' hfs' =>
          hG s' (htr'.trans (by simp only [arm64_norm])) (hfs'.trans (by simp only [arm64_norm])))
        hexit)
    pool_eq
    exact Entails.trans (sepConj_mono_left (ownedBytes_entails_emp_of_cap0 A.repAlloc hw0))
      (Entails.of_eq (by rw [emp_sepConj]))
  · have hw0_beq : (w.w0 == 0#64) = false := beq_false_of_ne hw0
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsρ lsRustDeallocSymCli) hinv
    wp_steps
    apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
      (by (try simp only [arm64_norm, *]); try rfl)
    intro hinv1
    refine SepWPp.weaken_pre ?_
      (call_dealloc_ownedBytes_placed (ms := ms) (len := w.w2) (bs := peer.name)
        (F := ownedBytes A.repAlloc w.w4 w.w5 w.w6 bundle ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x40 w.w3,
             cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x48 w.w4,
             cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr,
             cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x58 w.w1] ∗ anyHeap)
        hc hstk hstk64 hinv1
        (by (try simp only [arm64_norm, *]); try rfl)
        (by (try simp only [arm64_norm, *]); try rfl)
        (by (try simp only [arm64_norm]); exact hst.sp)
        (by (try simp only [arm64_norm]); exact hst.fp)
        (by (try simp only [calleeSavedVRegs, arm64_norm]); exact hst.vregs)
        hst.spAligned (retOff := 0xaf8)
        (by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl)
        (by (try simp only [arm64_norm, *]); try rfl)
        (by (try simp only [arm64_norm, *]); try rfl)
        (by (try simp only [arm64_norm]); try rfl)
        hw0 fun sf hin_f hcs_f hfs_f htr_f => ?_)
    · pool_eq
      exact Entails.of_eq (by sep_ac_rfl)
    · have hx19_f : sf.readReg64 (.gpr 19#5) = buf := by
        rw [hcs_f.1]; simp only [arm64_norm, hx19]
      have hx21_f : sf.readReg64 (.gpr 21#5) = w.w5 := by
        rw [hcs_f.2.2.1]; simp only [arm64_norm, hx21]
      have hx24_f : sf.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n := by
        rw [hcs_f.2.2.2.2.2.1]; simp only [arm64_norm, hx24]
      have hw26_f : (sf.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code := by
        rw [hcs_f.2.2.2.2.2.2.2.1]; simpa only [arm64_norm] using hw26
      have htr_sf : sf.trace = st.trace := htr_f.trans (by simp only [arm64_norm])
      have hfs_sf : sf.fs = st.fs := hfs_f.trans (by simp only [arm64_norm])
      refine SepWPp.weaken_pre ?_
        (step_drop_init_0xaf8_pool_placed (ms := M.stepEvents (rustDeallocEvents w.w0.toNat 1) ms)
          (w := w) (inPtr := inPtr) (bundle := bundle) (ps := ps)
          hc hstk hstk64 hin_f hw26_f hx19_f hx21_f hx24_f
          (fun s' htr' hfs' => hG s' (htr'.trans htr_sf) (hfs'.trans hfs_sf)) hexit)
      exact Entails.of_eq (by sep_ac_rfl)

theorem step_drop_init_0xae4_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {w : CallW} {s0 st : State}
    {stk hookStack resStack n code : Nat} {buf inPtr : BitVec 64} {peer : AddrV}
    {bundle : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {G : Nat → State → Prop} {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hst : InMainPlaced CodeOk s0 st 0xae4)
    (hw26 : (st.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx21 : st.readReg64 (.gpr 21#5) = w.w5)
    (hx22 : st.readReg64 (.gpr 22#5) = w.w1)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx25 : st.readReg64 (.gpr 25#5) = w.w0)
    (hG : ∀ s', s'.trace = st.trace → s'.fs = st.fs → G code s')
    (hexit : ExitKPlaced CodeOk H A s0 stk G Q Qp) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) st
      (addrWords A.repAlloc peer w.w0 w.w1 w.w2 w.w3 ∗
        ownedBytes A.repAlloc w.w4 w.w5 w.w6 bundle ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x40 w.w3,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x48 w.w4,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x58 w.w1] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ anyHeap)
      Q Qp (mainOom s0) :=
  step_drop_init_0xae4_pool_placed hc hstk hstk64 hst hw26 hx19 hx21 hx22 hx24 hx25 hG
    (exitKPoolPlaced_of_exitKPlaced hexit)

set_option maxHeartbeats 800000 in
/-- Continuation dropping `callHeap A.repAlloc w c` from `M+0x660` (`w26 = code`). -/
theorem step_drop_call_0x660_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {c : CallV}
    {w : CallW} {s0 st : State} {stk hookStack resStack n code : Nat} {buf inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {G : Nat → State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hst : InMainPlaced CodeOk s0 st 0x660)
    (hw26 : (st.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx20 : st.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag)
    (hx21 : st.readReg64 (.gpr 21#5) = w.w5)
    (hx22 : st.readReg64 (.gpr 22#5) = w.w1)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx25 : st.readReg64 (.gpr 25#5) = w.w0)
    (hx27 : st.readReg64 (.gpr 27#5) = w.w2)
    (hG : ∀ s', s'.trace = st.trace → s'.fs = st.fs → G code s')
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk G Q Qp) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) st
      (callHeap A.repAlloc w c ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x40 w.w3,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x48 w.w4,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x58 w.w1] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ anyHeap)
      Q Qp (mainOom s0) := by
  set fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hloc_to_mem :
      locals fsp [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1] ⊢
        memRegion fsp 0x480 := by
    refine locals_to_memRegion fsp _ (by simp [LocalsWF]) ?_
    intro o k P hm
    simp only [cell, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact ProofLib.pointsTo64_entails_memRegion _ _
  have hpc := hst.pc
  have hrun := hst.run
  have hinv := hst.inv
  cases c with
  | keygen me k =>
    dsimp only [CallV.tag] at hx20
    dsimp only [callHeap, addrWords]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun _ => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      ⌜w.w4.setWidth 8 = me.device⌝ ∗
        (ownedBytes A.repAlloc w.w1 w.w2 w.w3 me.name ∗
          (argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
            locals fsp [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1] ∗
            stackAt fsp (stk - mainFrameSize) ∗ A.pool lim ms st ∗ anyHeap)) by sep_ac_rfl)) ?_
    refine SepWPp.pure_elim fun _ => ?_
    refine SepWPp.weaken_pre
      (P' := ownedBytes A.repAlloc w.w1 w.w2 w.w3 me.name ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        memRegion fsp 0x480 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim ms st ∗ anyHeap)
      (by
        refine Entails.trans (Entails.of_eq (show _ =
          locals fsp [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1] ∗
            (ownedBytes A.repAlloc w.w1 w.w2 w.w3 me.name ∗ argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
              mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim ms st ∗ anyHeap) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hloc_to_mem) (Entails.of_eq (by sep_ac_rfl))) ?_
    rw [mPcPlaced_eq] at hpc; rw [mProgPlaced_eq]
    by_cases hw1 : w.w1 = 0#64
    · apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb6c#64) hinv
      wp_steps
      apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
        (by (try simp only [arm64_norm, *]); try rfl)
      intro hinv1
      have hin1 : InMainPlaced CodeOk s0 _ 0xb6c := {
        inv := hinv1
        pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
        run := by (try simp only [arm64_norm, *])
        sp := by (try simp only [arm64_norm]); exact hst.sp
        fp := by (try simp only [arm64_norm]); exact hst.fp
        vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hst.vregs
        spAligned := hst.spAligned
      }
      refine SepWPp.weaken_pre ?_
        (step_exit_0xb6c_pool_placed (ms := ms) (ps := ps) hc hstk hin1
          (by simpa only [arm64_norm] using hw26)
          (by (try simp only [arm64_norm, hx19]); try rfl)
          (by (try simp only [arm64_norm, hx24]); try rfl)
          (fun s' htr' hfs' =>
            hG s' (htr'.trans (by simp only [arm64_norm])) (hfs'.trans (by simp only [arm64_norm])))
          hexit)
      pool_eq
      exact Entails.trans (sepConj_mono_left (ownedBytes_entails_emp_of_cap0 A.repAlloc hw1))
        (Entails.of_eq (by rw [emp_sepConj]))
    · have hw1_beq : (w.w1 == 0#64) = false := beq_false_of_ne hw1
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb10#64) hinv
      wp_steps
      apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
        (by (try simp only [arm64_norm, *]); try rfl)
      intro hinv1
      have hin1 : InMainPlaced CodeOk s0 _ 0xb10 := {
        inv := hinv1
        pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
        run := by (try simp only [arm64_norm, *])
        sp := by (try simp only [arm64_norm]); exact hst.sp
        fp := by (try simp only [arm64_norm]); exact hst.fp
        vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hst.vregs
        spAligned := hst.spAligned
      }
      refine SepWPp.congr_pre ?_
        (step_drop_tail_0xb10_pool_placed (ms := ms) (len := w.w3) (bs := me.name) (ps := ps)
          hc hstk hstk64 hin1
          (by (try simp only [arm64_norm, *]); try rfl)
          (by (try simp only [arm64_norm, hx27]); try rfl)
          hw1
          (by simpa only [arm64_norm] using hw26)
          (by (try simp only [arm64_norm, hx19]); try rfl)
          (by (try simp only [arm64_norm, hx24]); try rfl)
          (fun s' htr' hfs' =>
            hG s' (htr'.trans (by simp only [arm64_norm])) (hfs'.trans (by simp only [arm64_norm])))
          hexit)
      pool_eq
  | init peer bundle =>
    dsimp only [CallV.tag] at hx20
    dsimp only [callHeap]
    rw [mPcPlaced_eq] at hpc; rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xae4#64) hinv
    wp_steps
    apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
      (by (try simp only [arm64_norm, *]); try rfl)
    intro hinv1
    have hin1 : InMainPlaced CodeOk s0 _ 0xae4 := {
      inv := hinv1
      pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
      run := by (try simp only [arm64_norm, *])
      sp := by (try simp only [arm64_norm]); exact hst.sp
      fp := by (try simp only [arm64_norm]); exact hst.fp
      vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hst.vregs
      spAligned := hst.spAligned
    }
    refine SepWPp.weaken_pre ?_
      (step_drop_init_0xae4_pool_placed (ms := ms) (w := w) (peer := peer) (bundle := bundle)
        (inPtr := inPtr) (ps := ps) hc hstk hstk64 hin1
        (by simpa only [arm64_norm] using hw26)
        (by (try simp only [arm64_norm, hx19]); try rfl)
        (by (try simp only [arm64_norm, hx21]); try rfl)
        (by (try simp only [arm64_norm, hx22]); try rfl)
        (by (try simp only [arm64_norm, hx24]); try rfl)
        (by (try simp only [arm64_norm, hx25]); try rfl)
        (fun s' htr' hfs' =>
          hG s' (htr'.trans (by simp only [arm64_norm])) (hfs'.trans (by simp only [arm64_norm])))
        hexit)
    pool_eq
    exact Entails.of_eq (by sep_ac_rfl)
  | send peer =>
    dsimp only [CallV.tag] at hx20
    dsimp only [callHeap, addrWords]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun _ => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      ⌜w.w4.setWidth 8 = peer.device⌝ ∗
        (ownedBytes A.repAlloc w.w1 w.w2 w.w3 peer.name ∗
          (argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
            locals fsp [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1] ∗
            stackAt fsp (stk - mainFrameSize) ∗ A.pool lim ms st ∗ anyHeap)) by sep_ac_rfl)) ?_
    refine SepWPp.pure_elim fun _ => ?_
    refine SepWPp.weaken_pre
      (P' := ownedBytes A.repAlloc w.w1 w.w2 w.w3 peer.name ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        memRegion fsp 0x480 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim ms st ∗ anyHeap)
      (by
        refine Entails.trans (Entails.of_eq (show _ =
          locals fsp [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1] ∗
            (ownedBytes A.repAlloc w.w1 w.w2 w.w3 peer.name ∗ argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
              mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim ms st ∗ anyHeap) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hloc_to_mem) (Entails.of_eq (by sep_ac_rfl))) ?_
    rw [mPcPlaced_eq] at hpc; rw [mProgPlaced_eq]
    by_cases hw1 : w.w1 = 0#64
    · apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb6c#64) hinv
      wp_steps
      apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
        (by (try simp only [arm64_norm, *]); try rfl)
      intro hinv1
      have hin1 : InMainPlaced CodeOk s0 _ 0xb6c := {
        inv := hinv1
        pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
        run := by (try simp only [arm64_norm, *])
        sp := by (try simp only [arm64_norm]); exact hst.sp
        fp := by (try simp only [arm64_norm]); exact hst.fp
        vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hst.vregs
        spAligned := hst.spAligned
      }
      refine SepWPp.weaken_pre ?_
        (step_exit_0xb6c_pool_placed (ms := ms) (ps := ps) hc hstk hin1
          (by simpa only [arm64_norm] using hw26)
          (by (try simp only [arm64_norm, hx19]); try rfl)
          (by (try simp only [arm64_norm, hx24]); try rfl)
          (fun s' htr' hfs' =>
            hG s' (htr'.trans (by simp only [arm64_norm])) (hfs'.trans (by simp only [arm64_norm])))
          hexit)
      pool_eq
      exact Entails.trans (sepConj_mono_left (ownedBytes_entails_emp_of_cap0 A.repAlloc hw1))
        (Entails.of_eq (by rw [emp_sepConj]))
    · have hw1_beq : (w.w1 == 0#64) = false := beq_false_of_ne hw1
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb10#64) hinv
      wp_steps
      apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
        (by (try simp only [arm64_norm, *]); try rfl)
      intro hinv1
      have hin1 : InMainPlaced CodeOk s0 _ 0xb10 := {
        inv := hinv1
        pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
        run := by (try simp only [arm64_norm, *])
        sp := by (try simp only [arm64_norm]); exact hst.sp
        fp := by (try simp only [arm64_norm]); exact hst.fp
        vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hst.vregs
        spAligned := hst.spAligned
      }
      refine SepWPp.congr_pre ?_
        (step_drop_tail_0xb10_pool_placed (ms := ms) (len := w.w3) (bs := peer.name) (ps := ps)
          hc hstk hstk64 hin1
          (by (try simp only [arm64_norm, *]); try rfl)
          (by (try simp only [arm64_norm, hx27]); try rfl)
          hw1
          (by simpa only [arm64_norm] using hw26)
          (by (try simp only [arm64_norm, hx19]); try rfl)
          (by (try simp only [arm64_norm, hx24]); try rfl)
          (fun s' htr' hfs' =>
            hG s' (htr'.trans (by simp only [arm64_norm])) (hfs'.trans (by simp only [arm64_norm])))
          hexit)
      pool_eq
  | recv peer =>
    dsimp only [CallV.tag] at hx20
    dsimp only [callHeap, addrWords]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun _ => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      ⌜w.w4.setWidth 8 = peer.device⌝ ∗
        (ownedBytes A.repAlloc w.w1 w.w2 w.w3 peer.name ∗
          (argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
            locals fsp [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1] ∗
            stackAt fsp (stk - mainFrameSize) ∗ A.pool lim ms st ∗ anyHeap)) by sep_ac_rfl)) ?_
    refine SepWPp.pure_elim fun _ => ?_
    refine SepWPp.weaken_pre
      (P' := ownedBytes A.repAlloc w.w1 w.w2 w.w3 peer.name ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        memRegion fsp 0x480 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim ms st ∗ anyHeap)
      (by
        refine Entails.trans (Entails.of_eq (show _ =
          locals fsp [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1] ∗
            (ownedBytes A.repAlloc w.w1 w.w2 w.w3 peer.name ∗ argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
              mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim ms st ∗ anyHeap) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hloc_to_mem) (Entails.of_eq (by sep_ac_rfl))) ?_
    rw [mPcPlaced_eq] at hpc; rw [mProgPlaced_eq]
    by_cases hw1 : w.w1 = 0#64
    · apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb6c#64) hinv
      wp_steps
      apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
        (by (try simp only [arm64_norm, *]); try rfl)
      intro hinv1
      have hin1 : InMainPlaced CodeOk s0 _ 0xb6c := {
        inv := hinv1
        pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
        run := by (try simp only [arm64_norm, *])
        sp := by (try simp only [arm64_norm]); exact hst.sp
        fp := by (try simp only [arm64_norm]); exact hst.fp
        vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hst.vregs
        spAligned := hst.spAligned
      }
      refine SepWPp.weaken_pre ?_
        (step_exit_0xb6c_pool_placed (ms := ms) (ps := ps) hc hstk hin1
          (by simpa only [arm64_norm] using hw26)
          (by (try simp only [arm64_norm, hx19]); try rfl)
          (by (try simp only [arm64_norm, hx24]); try rfl)
          (fun s' htr' hfs' =>
            hG s' (htr'.trans (by simp only [arm64_norm])) (hfs'.trans (by simp only [arm64_norm])))
          hexit)
      pool_eq
      exact Entails.trans (sepConj_mono_left (ownedBytes_entails_emp_of_cap0 A.repAlloc hw1))
        (Entails.of_eq (by rw [emp_sepConj]))
    · have hw1_beq : (w.w1 == 0#64) = false := beq_false_of_ne hw1
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb10#64) hinv
      wp_steps
      apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
        (by (try simp only [arm64_norm, *]); try rfl)
      intro hinv1
      have hin1 : InMainPlaced CodeOk s0 _ 0xb10 := {
        inv := hinv1
        pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
        run := by (try simp only [arm64_norm, *])
        sp := by (try simp only [arm64_norm]); exact hst.sp
        fp := by (try simp only [arm64_norm]); exact hst.fp
        vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hst.vregs
        spAligned := hst.spAligned
      }
      refine SepWPp.congr_pre ?_
        (step_drop_tail_0xb10_pool_placed (ms := ms) (len := w.w3) (bs := peer.name) (ps := ps)
          hc hstk hstk64 hin1
          (by (try simp only [arm64_norm, *]); try rfl)
          (by (try simp only [arm64_norm, hx27]); try rfl)
          hw1
          (by simpa only [arm64_norm] using hw26)
          (by (try simp only [arm64_norm, hx19]); try rfl)
          (by (try simp only [arm64_norm, hx24]); try rfl)
          (fun s' htr' hfs' =>
            hG s' (htr'.trans (by simp only [arm64_norm])) (hfs'.trans (by simp only [arm64_norm])))
          hexit)
      pool_eq

theorem step_drop_call_0x660_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {c : CallV}
    {w : CallW} {s0 st : State} {stk hookStack resStack n code : Nat} {buf inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {G : Nat → State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hst : InMainPlaced CodeOk s0 st 0x660)
    (hw26 : (st.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx20 : st.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag)
    (hx21 : st.readReg64 (.gpr 21#5) = w.w5)
    (hx22 : st.readReg64 (.gpr 22#5) = w.w1)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx25 : st.readReg64 (.gpr 25#5) = w.w0)
    (hx27 : st.readReg64 (.gpr 27#5) = w.w2)
    (hG : ∀ s', s'.trace = st.trace → s'.fs = st.fs → G code s')
    (hexit : ExitKPlaced CodeOk H A s0 stk G Q Qp) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) st
      (callHeap A.repAlloc w c ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x40 w.w3,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x48 w.w4,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x58 w.w1] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ anyHeap)
      Q Qp (mainOom s0) :=
  step_drop_call_0x660_pool_placed hc hstk hstk64 hst hw26 hx19 hx20 hx21 hx22 hx24 hx25 hx27 hG
    (exitKPoolPlaced_of_exitKPlaced hexit)

/-- `M+0x650`: `ldr x0, [sp, #0x50]; mov x1, x23; mov w2, #1; bl __rust_dealloc` →
`step_drop_call_0x660_pool_placed` (`w26 = code`). Shared by M3 read-error cleanup (`code = 2`) and
M4 send-over-cap exit (`code = 1`). -/
theorem step_dealloc_in_0x650_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {c : CallV}
    {w : CallW} {s0 st : State} {stk hookStack resStack n code : Nat}
    {buf inCap inPtr inLen : BitVec 64} {inBs : List (BitVec 8)}
    {ps : List (BitVec 64 × List (BitVec 8))} {G : Nat → State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hst : InMainPlaced CodeOk s0 st 0x650)
    (hcap0 : inCap ≠ 0#64)
    (hw26 : (st.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx20 : st.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag)
    (hx21 : st.readReg64 (.gpr 21#5) = w.w5)
    (hx22 : st.readReg64 (.gpr 22#5) = w.w1)
    (hx23 : st.readReg64 (.gpr 23#5) = inCap)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx25 : st.readReg64 (.gpr 25#5) = w.w0)
    (hx27 : st.readReg64 (.gpr 27#5) = w.w2)
    (hG : ∀ s', s'.trace = st.trace → s'.fs = st.fs → G code s')
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk G Q Qp) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) st
      (ownedBytes A.repAlloc inCap inPtr inLen inBs ∗
        callHeap A.repAlloc w c ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x40 w.w3,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x48 w.w4,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x58 w.w1] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ anyHeap)
      Q Qp (mainOom s0) := by
  set fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hfocus50 :
      locals fsp [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1] =
      ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        localsCtx fsp 0 [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] 0x50 8 [cell fsp 0x58 w.w1] := by
    simp only [locals, localsFrom, localsCtx]; sep_ac_rfl
  rw [hfocus50]
  have hal : st.spAligned = true := hst.spAligned_state
  have hsp : st.sp = fsp := hst.sp
  have hpc := hst.pc; have hrun := hst.run; have hinv := hst.inv
  rw [mPcPlaced_eq] at hpc; rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsρ lsRustDeallocSymCli) hinv
  wp_steps
  apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
    (by (try simp only [arm64_norm, *]); try rfl)
  intro hinv1
  refine SepWPp.weaken_pre
    (P' := ownedBytes A.repAlloc inCap inPtr inLen inBs ∗
      stackAt fsp (stk - mainFrameSize) ∗ A.pool lim ms _ ∗
      (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        localsCtx fsp 0 [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] 0x50 8 [cell fsp 0x58 w.w1] ∗
        anyHeap))
    (by pool_eq; exact Entails.of_eq (by sep_ac_rfl))
    (call_dealloc_ownedBytes_placed (ms := ms) hc hstk hstk64 hinv1
      (by (try simp only [arm64_norm, *]); try rfl)
      (by (try simp only [arm64_norm, *]); try rfl)
      (by (try simp only [arm64_norm]); exact hst.sp)
      (by (try simp only [arm64_norm]); exact hst.fp)
      (by (try simp only [calleeSavedVRegs, arm64_norm]); exact hst.vregs)
      hst.spAligned (retOff := 0x660)
      (by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl)
      (by (try simp only [arm64_norm, *]); try rfl)
      (by (try simp only [arm64_norm, *]); try rfl)
      (by (try simp only [arm64_norm]); try rfl)
      hcap0 fun sf hin_f hcs_f hfs_f htr_f => ?_)
  have hx19_f : sf.readReg64 (.gpr 19#5) = buf := by rw [hcs_f.1]; simp only [arm64_norm, hx19]
  have hx20_f : sf.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag := by
    rw [hcs_f.2.1]; simp only [arm64_norm, hx20]
  have hx21_f : sf.readReg64 (.gpr 21#5) = w.w5 := by rw [hcs_f.2.2.1]; simp only [arm64_norm, hx21]
  have hx22_f : sf.readReg64 (.gpr 22#5) = w.w1 := by rw [hcs_f.2.2.2.1]; simp only [arm64_norm, hx22]
  have hx24_f : sf.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n := by
    rw [hcs_f.2.2.2.2.2.1]; simp only [arm64_norm, hx24]
  have hx25_f : sf.readReg64 (.gpr 25#5) = w.w0 := by
    rw [hcs_f.2.2.2.2.2.2.1]; simp only [arm64_norm, hx25]
  have hw26_f : (sf.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code := by
    rw [hcs_f.2.2.2.2.2.2.2.1]; simpa only [arm64_norm] using hw26
  have hx27_f : sf.readReg64 (.gpr 27#5) = w.w2 := by
    rw [hcs_f.2.2.2.2.2.2.2.2.1]; simp only [arm64_norm, hx27]
  have htr_sf : sf.trace = st.trace := htr_f.trans (by simp only [arm64_norm])
  have hfs_sf : sf.fs = st.fs := hfs_f.trans (by simp only [arm64_norm])
  refine SepWPp.weaken_pre ?_
    (step_drop_call_0x660_pool_placed (ms := M.stepEvents (rustDeallocEvents inCap.toNat 1) ms)
      (c := c) (w := w) (inPtr := inPtr) (ps := ps)
      hc hstk hstk64 hin_f hw26_f hx19_f hx20_f hx21_f hx22_f hx24_f hx25_f hx27_f
      (fun s' htr' hfs' => hG s' (htr'.trans htr_sf) (hfs'.trans hfs_sf)) hexit)
  rw [hfocus50]
  exact Entails.of_eq (by sep_ac_rfl)

theorem step_dealloc_in_0x650_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {c : CallV}
    {w : CallW} {s0 st : State} {stk hookStack resStack n code : Nat}
    {buf inCap inPtr inLen : BitVec 64} {inBs : List (BitVec 8)}
    {ps : List (BitVec 64 × List (BitVec 8))} {G : Nat → State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hst : InMainPlaced CodeOk s0 st 0x650)
    (hcap0 : inCap ≠ 0#64)
    (hw26 : (st.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx20 : st.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag)
    (hx21 : st.readReg64 (.gpr 21#5) = w.w5)
    (hx22 : st.readReg64 (.gpr 22#5) = w.w1)
    (hx23 : st.readReg64 (.gpr 23#5) = inCap)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx25 : st.readReg64 (.gpr 25#5) = w.w0)
    (hx27 : st.readReg64 (.gpr 27#5) = w.w2)
    (hG : ∀ s', s'.trace = st.trace → s'.fs = st.fs → G code s')
    (hexit : ExitKPlaced CodeOk H A s0 stk G Q Qp) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) st
      (ownedBytes A.repAlloc inCap inPtr inLen inBs ∗
        callHeap A.repAlloc w c ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x40 w.w3,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x48 w.w4,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x58 w.w1] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ anyHeap)
      Q Qp (mainOom s0) :=
  step_dealloc_in_0x650_pool_placed hc hstk hstk64 hst hcap0 hw26 hx19 hx20 hx21 hx22 hx23 hx24
    hx25 hx27 hG (exitKPoolPlaced_of_exitKPlaced hexit)

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ErrTailPlacedBudget
