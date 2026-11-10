/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.FramePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.FreeArgsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Relocatable `free_args` Block (`M+0xb6c .. M+0xb80`, Block `617`)

Verifies `main`'s `args` buffer deallocation block (`M+0xb6c .. M+0xb80`) under
`[LibsignalPlacement]` and `RustCliAllocBudget M`, threading `A.pool` across `__rust_dealloc` into
`ExitKPoolPlaced` (and `ExitKPlaced`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.RustHeap (LayoutOk arrayAt vecBuf)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPC_617 blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AtRetPlaced InMainPlaced LsCodeInv argsBuf mPcPlaced_eq mProgPlaced
   mProgPlaced_eq mainFrameSize mainOom mainSaved main_call_rocl sepWPp_seq_codeOk
   sepWPp_with_stk_le_two_pow_64 sliceRefAt stackAt_split_ge)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.FreeArgsPlacedBudget

open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget RustLayoutOk rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
  (ExitKPlaced MainCalleesBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlacedBudget
  (main_dealloc_fs_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget
  (ExitKPoolPlaced exitKPoolPlaced_of_exitKPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] ProofLib.bv_sub_add_lit
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem sepWPp_weaken_pre_p {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P ⊢ P') (h : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  exact h R (Satisfies.mono (sepConj_mono_left hP) hm) hL

private theorem shl4_toNat_p {cap : BitVec 64} (hlt : cap.toNat * 16 < 2 ^ 63) :
    (cap <<< 4).toNat = cap.toNat * 16 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt (by omega)

private theorem rustLayoutOk_mul16_8_p {cap : BitVec 64} (hcap : cap ≠ 0)
    (hlt : cap.toNat * 16 < 2 ^ 63) :
    RustLayoutOk (cap.toNat * 16) 8 := by
  have hpos : 0 < cap.toNat := Nat.pos_of_ne_zero (fun h0 => hcap (BitVec.eq_of_toNat_eq h0))
  have hlay : LayoutOk (cap.toNat * 16) 8 := ⟨by omega, ⟨3, rfl⟩, by omega⟩
  exact ⟨hlay, by decide⟩

private theorem sliceRefAt_entails_memRegion_p (a p : BitVec 64) (len : Nat) :
    sliceRefAt a p len ⊢ memRegion a 16 := by
  unfold sliceRefAt
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)) ?_
  exact Entails.of_eq (ProofLib.memRegion_split a 8 8 (by decide)).symm

private theorem sliceArray_entails_memRegion_p
    (buf : BitVec 64) (ps : List (BitVec 64 × List (BitVec 8)))
    (hlt : ps.length * 16 < 2 ^ 64) :
    arrayAt (fun pb a => sliceRefAt a pb.1 pb.2.length) 16 buf ps ⊢
      memRegion buf (ps.length * 16) := by
  induction ps generalizing buf with
  | nil =>
    simp only [arrayAt, List.length, Nat.zero_mul, ProofLib.memRegion_zero]
    exact Entails.refl emp
  | cons pb ps ih =>
    dsimp only [arrayAt]
    have hlt' : ps.length * 16 < 2 ^ 64 := by
      simp only [List.length_cons] at hlt; omega
    refine Entails.trans
      (sepConj_mono (sliceRefAt_entails_memRegion_p buf pb.1 pb.2.length) (ih (buf + 16#64) hlt')) ?_
    have heq : 16 + ps.length * 16 = (pb :: ps).length * 16 := by
      simp only [List.length_cons]; omega
    rw [← heq]
    exact Entails.of_eq (ProofLib.memRegion_split buf 16 (ps.length * 16) (by omega)).symm

private theorem argsBuf_entails_dealloc_p {M : AllocCostModel} (A : RustCliAllocBudget M)
    {cap buf : BitVec 64} (ps : List (BitVec 64 × List (BitVec 8))) (hcap : cap ≠ 0) :
    argsBuf A.repAlloc cap buf ps ⊢
      ⌜cap.toNat * 16 < 2 ^ 63⌝ ∗ A.live buf (cap.toNat * 16) 8 ∗ memRegion buf (cap.toNat * 16) := by
  unfold argsBuf vecBuf
  simp only [hcap, ↓reduceIte, A.repAlloc_live_norm]
  apply Entails.pure_left
  rintro ⟨hlen, hlt, _⟩
  apply Entails.pure_right hlt
  have hps_lt : ps.length * 16 < 2 ^ 64 := by omega
  have hmerge :
      memRegion buf (ps.length * 16) ∗
        memRegion (buf + BitVec.ofNat 64 (ps.length * 16)) ((cap.toNat - ps.length) * 16) =
      memRegion buf (cap.toNat * 16) := by
    have hsum : ps.length * 16 + (cap.toNat - ps.length) * 16 = cap.toNat * 16 := by
      have : ps.length + (cap.toNat - ps.length) = cap.toNat := Nat.add_sub_of_le hlen
      calc
        ps.length * 16 + (cap.toNat - ps.length) * 16
          = (ps.length + (cap.toNat - ps.length)) * 16 := (Nat.add_mul _ _ _).symm
        _ = cap.toNat * 16 := by rw [this]
    rw [← hsum]
    exact (ProofLib.memRegion_split buf (ps.length * 16) ((cap.toNat - ps.length) * 16) (by omega)).symm
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left (sliceArray_entails_memRegion_p buf ps hps_lt))) ?_
  rw [hmerge]
  exact Entails.refl _

private theorem argsBuf_zero_entails_emp_p {M : AllocCostModel} (A : RustCliAllocBudget M)
    (buf : BitVec 64) (ps : List (BitVec 64 × List (BitVec 8))) :
    argsBuf A.repAlloc 0 buf ps ⊢ emp := by
  unfold argsBuf vecBuf
  simp only [↓reduceIte]
  exact Entails.pure_left fun _ => Entails.refl emp

private theorem finish_dealloc_pool_call_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {s0 s sm : State} {stk code : Nat} {cap buf : BitVec 64}
    {G : Nat → State → Prop} {Q Qp : State → SepProp → Prop} {F0 : SepProp}
    (hdealloc : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustDeallocSymCli)
      (withLsRoCl lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack).keepsFs))
    (hext_le : extHookStack ≤ stk - mainFrameSize)
    (hstk64 : stk ≤ 2 ^ 64)
    (hs : InMainPlaced CodeOk s0 s 0xb70)
    (hlay : RustLayoutOk (cap.toNat * 16) 8)
    (hG : ∀ s', s'.trace = s.trace → s'.fs = s.fs → G code s')
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk G Q Qp)
    (hinv_da : CodeOk sm.mem)
    (hpc_m : sm.pc = lsρ lsRustDeallocSymCli)
    (hrun_m : sm.status = .Running)
    (hsp_m : sm.sp = s.sp)
    (hsp_al_m : sm.spAligned = true)
    (hlr_m : sm.readReg64 .lr = (blkPl_617).base + 2944#64)
    (hx0_m : sm.readReg64 .x0 = buf)
    (hx1_m : (sm.readReg64 .x1).toNat = cap.toNat * 16)
    (hx2_m : (sm.readReg64 .x2).toNat = 8)
    (hw26_m : (sm.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code)
    (hfp_m : sm.readReg64 .fp = s.readReg64 .fp)
    (hv_m : calleeSavedVRegs sm = calleeSavedVRegs s)
    (htr_m : sm.trace = s.trace)
    (hfs_m : sm.fs = s.fs)
    (hpool_m : A.pool lim st sm = A.pool lim st s)
    (hF0 : F0 =
      A.live buf (cap.toNat * 16) 8 ∗
        memRegion buf (cap.toNat * 16) ∗
          mainSaved s0 ∗
            memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
              (memRegion
                  (s0.sp - BitVec.ofNat 64 mainFrameSize - BitVec.ofNat 64 (stk - mainFrameSize))
                  (stk - mainFrameSize - extHookStack) ∗
                stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) extHookStack) ∗
                A.pool lim st s ∗ anyHeap) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H)
      (s0.readReg64 .lr) sm F0 Q Qp (mainOom s0) := by
  subst hF0
  have hsp_split := stackAt_split_ge (s0.sp - BitVec.ofNat 64 mainFrameSize) hext_le (by omega)
  let F : SepProp :=
    mainSaved s0 ∗ memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
      memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize - BitVec.ofNat 64 (stk - mainFrameSize))
        (stk - mainFrameSize - extHookStack) ∗
      anyHeap
  have hsp0_m : sm.sp = s0.sp - BitVec.ofNat 64 mainFrameSize := hsp_m.trans hs.sp
  refine main_call_rocl (buf, cap.toNat * 16, 8, st) hdealloc hinv_da hpc_m hrun_m hsp_al_m hlr_m
    (F := F) ?_ (hnext := ?_)
  · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack, F]
    rw [hpool_m]
    simp only [hsp0_m, sepConj_assoc]
    have hpure : sm.readReg64 .x0 = buf ∧ (sm.readReg64 .x1).toNat = cap.toNat * 16 ∧
        (sm.readReg64 .x2).toNat = 8 ∧ RustLayoutOk (cap.toNat * 16) 8 ∧
        LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (sm.readReg64 .lr) :=
      ⟨hx0_m, hx1_m, hx2_m, hlay, by
        rw [hlr_m]
        exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_blockPlacement_base_add
          617 2944#64 (by decide) (by decide)⟩
    refine Entails.pure_right hpure ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf hinv_f hpcm hrunm hspm hcsm
    dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun hfs_f => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun htr_f => ?_
    have hsp_f : sf.sp = s.sp := hspm.trans hsp_m
    have hfp_f : sf.readReg64 .fp = s.readReg64 .fp :=
      hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hfp_m
    have hv_f : calleeSavedVRegs sf = calleeSavedVRegs s :=
      hcsm.2.2.2.2.2.2.2.2.2.2.2.trans hv_m
    have hw26_f : (sf.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code := by
      rw [hcsm.2.2.2.2.2.2.2.1]; exact hw26_m
    have hAtRet : AtRetPlaced CodeOk s0 sf code :=
      ⟨InMainPlaced.mk_step hs hpcm hrunm hsp_f hfp_f hinv_f hv_f, hw26_f⟩
    refine sepWPp_weaken_pre_p ?_
      (hexit sf (M.stepEvents (rustDeallocEvents (cap.toNat * 16) 8) st) code hAtRet
        (hG sf (htr_f.trans htr_m) (hfs_f.trans hfs_m)))
    unfold CryptoVerification.SignalSession.Cli.MainHops.retMem
    rw [RustCliAllocBudget.atState_pool]
    dsimp only [F]
    rw [hsp0_m, hsp_split]
    exact Entails.of_eq (by sep_ac_rfl)

private theorem free_args_at_b70_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {s0 s : State}
    {stk hookStack resStack code : Nat} {cap buf : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {G : Nat → State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (_hstk0 : mainFrameSize ≤ stk)
    (hext_le : extHookStack ≤ stk - mainFrameSize)
    (hstk64 : stk ≤ 2 ^ 64)
    (hs : InMainPlaced CodeOk s0 s 0xb70)
    (hcap : cap ≠ 0)
    (hcode : (s.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code)
    (hx24 : s.readReg64 (.gpr 24#5) = cap)
    (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hG : ∀ s', s'.trace = s.trace → s'.fs = s.fs → G code s')
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk G Q Qp) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (argsBuf A.repAlloc cap buf ps ∗ mainSaved s0 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ anyHeap)
      Q Qp (mainOom s0) := by
  have hdealloc := main_dealloc_fs_placed_ok hc.allocFs
  clear hc
  refine sepWPp_weaken_pre_p (sepConj_mono_left (argsBuf_entails_dealloc_p A ps hcap)) ?_
  rw [sepConj_assoc, sepConj_assoc]
  apply SepWPp.pure_left
  intro hlt
  have hshl : (cap <<< 4).toNat = cap.toNat * 16 := shl4_toNat_p hlt
  have hlay : RustLayoutOk (cap.toNat * 16) 8 := rustLayoutOk_mul16_8_p hcap hlt
  have hsp_split := stackAt_split_ge (s0.sp - BitVec.ofNat 64 mainFrameSize) hext_le (by omega)
  rw [hsp_split]
  have hpc : s.pc = (blkPl_617).base + 2928#64 := hs.pc
  have hrun : s.status = .Running := hs.run
  have hsp_al : s.spAligned = true := hs.spAligned_state
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsρ lsRustDeallocSymCli) hs.inv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  intro hinv_da
  exact finish_dealloc_pool_call_placed hdealloc hext_le hstk64 hs hlay hG hexit hinv_da
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, hrun])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm]; exact hsp_al)
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm, hshl])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm, hcode])
    (by simp only [arm64_norm])
    (by simp only [calleeSavedVRegs, arm64_norm])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    rfl

/-- Frees `args`'s buffer (`cap = x24`, `buf = x19`) at `M+0xb6c` (or `M+0xb70` when `cap ≠ 0`)
under `RustCliAllocBudget M` and hands `retMem (A.atState lim st' sf) s0 stk` to `ExitKPoolPlaced`. -/
theorem free_args_pool_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {s0 s : State} {stk hookStack resStack code : Nat} {cap buf : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {G : Nat → State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max extHookStack hookStack ≤ stk)
    (hs : InMainPlaced CodeOk s0 s 0xb6c ∨ (InMainPlaced CodeOk s0 s 0xb70 ∧ cap ≠ 0))
    (hcode : (s.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code)
    (hx24 : s.readReg64 (.gpr 24#5) = cap) (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hG : ∀ s', s'.trace = s.trace → s'.fs = s.fs → G code s')
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk G Q Qp) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (argsBuf A.repAlloc cap buf ps ∗ mainSaved s0 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ anyHeap)
      Q Qp (mainOom s0) := by
  have hstk0 : mainFrameSize ≤ stk := by omega
  have hext_le : extHookStack ≤ stk - mainFrameSize := by omega
  refine sepWPp_with_stk_le_two_pow_64 hstk0
    (F := argsBuf A.repAlloc cap buf ps ∗
      memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
      A.pool lim st s ∗ anyHeap)
    (Entails.of_eq (by sep_ac_rfl))
    fun hstk64 => ?_
  rcases hs with hs10 | ⟨hs14, hcap⟩
  · by_cases hcap : cap = 0
    · subst hcap
      refine sepWPp_weaken_pre_p (sepConj_mono_left (argsBuf_zero_entails_emp_p A buf ps)) ?_
      rw [emp_sepConj]
      have hpc : s.pc = (blkPl_617).base + 2924#64 := hs10.pc
      have hrun : s.status = .Running := hs10.run
      have _hsp_al : s.spAligned = true := hs10.spAligned_state
      rw [mProgPlaced_eq]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 2944#64) hs10.inv
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
      intro hinv_ret
      refine SepWPp.congr_pre ?_
        (hexit _ st code
          ⟨InMainPlaced.mk_step hs10
            (by simp only [mPcPlaced_eq, arm64_norm, *])
            (by simp only [arm64_norm, hrun])
            (by simp only [arm64_norm])
            (by simp only [arm64_norm])
            hinv_ret
            (by simp only [calleeSavedVRegs, arm64_norm]),
           by simpa only [arm64_norm] using hcode⟩
          (hG _ (by simp only [arm64_norm]) (by simp only [arm64_norm])))
      unfold CryptoVerification.SignalSession.Cli.MainHops.retMem
      rw [RustCliAllocBudget.atState_pool]
      simp only [arm64_norm]
    · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      have hpc : s.pc = (blkPl_617).base + 2924#64 := hs10.pc
      have hrun : s.status = .Running := hs10.run
      have _hsp_al : s.spAligned = true := hs10.spAligned_state
      rw [mProgPlaced_eq]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 2928#64) hs10.inv
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
      intro hinv_14
      refine SepWPp.congr_pre ?_
        (free_args_at_b70_pool_placed (st := st) (ps := ps) hc hstk0 hext_le hstk64
          (InMainPlaced.mk_step hs10
            (by simp only [mPcPlaced_eq, arm64_norm, *])
            (by simp only [arm64_norm, hrun])
            (by simp only [arm64_norm])
            (by simp only [arm64_norm])
            hinv_14
            (by simp only [calleeSavedVRegs, arm64_norm]))
          hcap
          (by simpa only [arm64_norm] using hcode)
          (by simpa only [arm64_norm] using hx24)
          (by simpa only [arm64_norm] using hx19)
          (fun s' htr' hfs' =>
            hG s' (htr'.trans (by simp only [arm64_norm])) (hfs'.trans (by simp only [arm64_norm])))
          hexit)
      simp only [arm64_norm]
  · exact free_args_at_b70_pool_placed hc hstk0 hext_le hstk64 hs14 hcap hcode hx24 hx19 hG hexit

/-- Frees `args`'s buffer (`cap = x24`, `buf = x19`) at `M+0xb6c` (or `M+0xb70` when `cap ≠ 0`)
under `RustCliAllocBudget M` and falls through to `M+0xb80` (`ExitKPlaced`). -/
theorem free_args_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {s0 s : State} {stk hookStack resStack code : Nat} {cap buf : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {G : Nat → State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max extHookStack hookStack ≤ stk)
    (hs : InMainPlaced CodeOk s0 s 0xb6c ∨ (InMainPlaced CodeOk s0 s 0xb70 ∧ cap ≠ 0))
    (hcode : (s.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code)
    (hx24 : s.readReg64 (.gpr 24#5) = cap) (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hG : ∀ s', s'.trace = s.trace → s'.fs = s.fs → G code s')
    (hexit : ExitKPlaced CodeOk H A s0 stk G Q Qp) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (argsBuf A.repAlloc cap buf ps ∗ mainSaved s0 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ anyHeap)
      Q Qp (mainOom s0) :=
  free_args_pool_placed_proof hc hstk hs hcode hx24 hx19 hG
    (exitKPoolPlaced_of_exitKPlaced hexit)

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.FreeArgsPlacedBudget
