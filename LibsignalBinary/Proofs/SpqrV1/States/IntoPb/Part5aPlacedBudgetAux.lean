/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`) — Part 5a Placed Aux: Arm 8 Step Lemmas

Relocatable `[LibsignalPlacement]` step lemmas (`+60 -> +1760 -> +2252 -> +2324 -> +2340 -> +1544`)
on Block `334` for Arm 8 (`States.ekReceivedCt1Sampled`, tag `10`), threading `RustCliAllocBudget M`,
`BudgetLimits`, `FitsEnv`/`FitsEvents`, `VmPreserved`, and `AllocCallPreserved`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aPlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement libsignalSessionCode lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1 (PolyEncoder)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Drop
  (none2Cap_add_two_beq_zero noneCap_add_two_beq_zero vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly
  (polyEncoderAt polyEncoderSize protoPolynomialEncoderSize)
open CryptoVerification.SpqrV1.Poly.DecoderPb (spqrRustDeallocSym)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb
  (TraceCalleeSaved bv_add_add_lit' bv_sub_sub_lit'
   ekReceivedScratchCells epilogueStagingCells
   ofNat_beq_zero_false' ofNat_lt_2pow63_and_highBit_zero
   ofNat_lt_2pow63_lsr63_zero ofNat_lt_2pow63_msb_zero ofNat_ne_zero_true
   protoPolynomialEncoderHeap
   sp_sub_1520_add_1424 sp_sub_480_add_200
   sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
   sp_sub_96_sub_1424 sp_sub_96_sub_160 sp_sub_96_sub_168 sp_sub_96_sub_176
   sp_sub_96_sub_192 sp_sub_96_sub_208
   statesIntoPbJumpTableBytes statesIntoPbJumpTablePlacedAt
   vecU8CloneTail vecU8CloneTail_entails_dealloc vecU8Heap vecU8Heap_nil_intro
   vecU8Heap_of_exact_alloc)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
   RustCliAllocBudget RustLayoutOk VmPreserved rustAllocEvents
   rustCliAllocNoOomSpec rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget
  (EncoderIntoPbAllocEnv EncoderIntoPbEnv encoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1PlacedBudget
  (call_encoderIntoPb_expose_wp_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5PlacedBudget
  (StatesIntoPbAllocPlacedBudget allocNoOom_ok_placed dealloc_ok_placed
   framelessMemcpy_ok_placed noAllocShim_ok_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget
  (ct1CloneEvents ct1DeallocEvents)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (framelessMemcpyBudgetSpec noAllocShimBudgetSpec)

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_1424 sp_sub_96_sub_160 sp_sub_1520_add_1424
  sp_sub_96_sub_208 sp_sub_96_sub_192 sp_sub_96_sub_176 sp_sub_96_sub_168 sp_sub_480_add_200
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

private theorem align_pre {prog : Program} {target : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (heq : P = P') (h : SepWP prog target s P' post) :
    SepWP prog target s P post :=
  heq ▸ h

private theorem vmPreserved_prepend {s s1 s2 : State}
    (h2 : VmPreserved s1 s2) (h1 : VmPreserved s s1) :
    VmPreserved s s2 :=
  h1.trans h2

private theorem allocCallPreserved_trans {s0 s1 s2 : State}
    (h1 : AllocCallPreserved s0 s1) (h2 : AllocCallPreserved s1 s2) :
    AllocCallPreserved s0 s2 := by
  rcases h1 with ⟨hfs1, htr1, hsig1, htp1, hbs1, hor1, hsym1⟩
  rcases h2 with ⟨hfs2, htr2, hsig2, htp2, hbs2, hor2, hsym2⟩
  exact ⟨hfs2.trans hfs1, htr2.trans htr1, hsig2.trans hsig1,
    htp2.trans htp1, hbs2.trans hbs1, hor2.trans hor1, hsym2.trans hsym1⟩

private theorem seq_vm_step {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre
      (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

/-! ## Relocatable Step Lemmas for Arm 8 (`+60 -> +1760 -> +2252 -> +2324 -> +2340 -> +1544`) -/

/-- Step 1b (`+60 -> +1760` in Block `334`): jump via index `8` (`tag = 10#64` -> `+1644`),
    load `auth`, `cap_ct1`, `ptr_ct1`, `len_ct1`, and `epoch` from `stA + 408..528`,
    stage `auth` into `s0.sp - 1360..1312` (`t0..t5`), and take `tbz x21, #0x3f, +1760`,
    preserving `VmPreserved` and `AllocCallPreserved`. -/
theorem ekReceivedCt1Sampled_step_60_to_1760_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (out stA : BitVec 64)
    (a0 a1 a2 a3 a4 a5 cap_ct1 ptr_ct1 epoch : BitVec 64) (len_ct1 : Nat)
    (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 : BitVec 64)
    (u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : len_ct1 < 2 ^ 63)
    (hpc : s.pc = (blkPl_334).base + 60#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 256#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx20 : s.readReg64 .x20 = stA)
    (hx19 : s.readReg64 .x19 = out)
    (hx8 : s.readReg64 .x8 = 10#64)
    (htrace : TraceCalleeSaved s s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 1760#64) s
      (statesIntoPbJumpTablePlacedAt ∗
       ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
       ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
       ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 len_ct1) ∗
       ((stA + 528#64) ↦₆₄ epoch) ∗
       ekReceivedScratchCells s0.sp
         t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
         u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 ∗
       Rest)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢
          statesIntoPbJumpTablePlacedAt ∗
          ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
          ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
          ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
          ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 len_ct1) ∗
          ((stA + 528#64) ↦₆₄ epoch) ∗
          ekReceivedScratchCells s0.sp
            a0 a1 a2 a3 a4 a5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
            u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 ∗
          Rest) ∧
        AllocCallPreserved s sm ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = stA ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 len_ct1 ∧
        sm.readReg64 .x23 = cap_ct1 ∧
        sm.readReg64 .x24 = ptr_ct1 ∧
        sm.readReg64 .x26 = s0.sp - 480#64 ∧
        sm.readReg64 .x27 = s0.sp - 1360#64 ∧
        sm.readReg64 .x28 = epoch ∧
        TraceCalleeSaved sm s0) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hmsb := ofNat_lt_2pow63_msb_zero hlen
  have hand := ofNat_lt_2pow63_and_highBit_zero hlen
  have hlsr := ofNat_lt_2pow63_lsr63_zero hlen
  dsimp only [ekReceivedScratchCells, BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine seq_vm_step
    (mid := (blkPl_334).base + 1644#64)
    (P_mid :=
      statesIntoPbJumpTablePlacedAt ∗
      ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
      ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
      ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
      ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 len_ct1) ∗
      ((stA + 528#64) ↦₆₄ epoch) ∗
      ekReceivedScratchCells s0.sp
        t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
        u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 ∗
      Rest)
    (Q := fun sc =>
      AllocCallPreserved s sc ∧
      sc.sp = s0.sp - 1520#64 ∧
      sc.readReg64 .x29 = s0.sp - 96#64 ∧
      sc.readReg64 .x28 = s0.sp - 256#64 ∧
      sc.readReg64 .x27 = s0.sp - 1360#64 ∧
      sc.readReg64 .x26 = s0.sp - 480#64 ∧
      sc.readReg64 .x20 = stA ∧
      sc.readReg64 .x19 = out ∧
      TraceCalleeSaved sc s0)
    ?_ ?_
  · dsimp only [statesIntoPbJumpTablePlacedAt, statesIntoPbJumpTableBytes,
      ekReceivedScratchCells, BitVec.ofNat_eq_ofNat]
    wp_steps
    refine align_pre (by sep_ac_rfl) ?_
    wp_done
  · intro sc hpcc hrunc hvmc ⟨hacp_sc, hspc, hx29c, hx28c, hx27c, hx26c, hx20c, hx19c, htrc, hvregsc⟩
    dsimp only [ekReceivedScratchCells, BitVec.ofNat_eq_ofNat] at hpcc ⊢
    refine SepWP.mono
      (post := fun sm Pm =>
        VmPreserved sc sm ∧
        (Pm ⊢
          statesIntoPbJumpTablePlacedAt ∗
          ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
          ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
          ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
          ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 len_ct1) ∗
          ((stA + 528#64) ↦₆₄ epoch) ∗
          ekReceivedScratchCells s0.sp
            a0 a1 a2 a3 a4 a5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
            u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 ∗
          Rest) ∧
        AllocCallPreserved sc sm ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = stA ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 len_ct1 ∧
        sm.readReg64 .x23 = cap_ct1 ∧
        sm.readReg64 .x24 = ptr_ct1 ∧
        sm.readReg64 .x26 = s0.sp - 480#64 ∧
        sm.readReg64 .x27 = s0.sp - 1360#64 ∧
        sm.readReg64 .x28 = epoch ∧
        TraceCalleeSaved sm s0)
      ?_
      (fun sm _Pm _ _ ⟨hvm_m, hPm, hacp_m, hrest⟩ =>
        ⟨hvmc.trans hvm_m, hPm, allocCallPreserved_trans hacp_sc hacp_m, hrest⟩)
    dsimp only [ekReceivedScratchCells, BitVec.ofNat_eq_ofNat]
    by_vm_steps (wp_steps; refine align_pre (by sep_ac_rfl) ?_; wp_done)

/-- Step 2 (`+1760 -> +2252` in Block `334`, direct `SepWP` form under `FitsEvents`):
    clones `ct1 : List (BitVec 8)` into `x22 = ptr_new` (with `x21 = BitVec.ofNat 64 ct1.length`)
    without OOM or panic, advancing `st` by `ct1CloneEvents ct1`. -/
theorem ekReceivedCt1Sampled_step_1760_to_2252_wp_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (s0 s : State) (st : M.σ) (out stA cap_ct1 ptr_ct1 epoch : BitVec 64)
    (ct1 : List (BitVec 8))
    (Frame : SepProp)
    (hfits : FitsEvents M lim st (ct1CloneEvents ct1))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : ct1.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_334).base + 1760#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 ct1.length)
    (hx23 : s.readReg64 .x23 = cap_ct1)
    (hx24 : s.readReg64 .x24 = ptr_ct1)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx28 : s.readReg64 .x28 = epoch)
    (htrace : TraceCalleeSaved s s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 2252#64) s
      ((ptr_ct1 ↦ₛ ct1) ∗
       vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 ct1 ∗
       A.pool lim st s ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ ptr_new : BitVec 64,
          (Pm ⊢ vecU8Heap A.repAlloc (BitVec.ofNat 64 ct1.length) ptr_new
              (BitVec.ofNat 64 ct1.length) ct1 ∗
            vecCapPtrDealloc A.repAlloc cap_ct1 ptr_ct1 ∗
            A.pool lim (M.stepEvents (ct1CloneEvents ct1) st) sm ∗
            stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame) ∧
          sm.sp = s0.sp - 1520#64 ∧
          sm.readReg64 .x29 = s0.sp - 96#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = stA ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 ct1.length ∧
          sm.readReg64 .x22 = ptr_new ∧
          sm.readReg64 .x23 = cap_ct1 ∧
          sm.readReg64 .x24 = ptr_ct1 ∧
          sm.readReg64 .x26 = s0.sp - 480#64 ∧
          sm.readReg64 .x27 = s0.sp - 1360#64 ∧
          sm.readReg64 .x28 = epoch ∧
          TraceCalleeSaved sm s0) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  by_cases hlen_zero : ct1.length = 0
  · have hnil_eq : ct1 = [] := List.eq_nil_of_length_eq_zero hlen_zero
    subst hnil_eq
    simp only [ct1CloneEvents, List.length_nil, ↓reduceIte, M.stepEvents_nil,
      BitVec.ofNat_eq_ofNat] at hx21 hlen ⊢
    refine SepWP.mono
      (post := fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ vecU8Heap A.repAlloc 0#64 1#64 0#64 [] ∗
          vecCapPtrDealloc A.repAlloc cap_ct1 ptr_ct1 ∗
          A.pool lim st s ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame) ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = stA ∧
        sm.readReg64 .x21 = 0#64 ∧
        sm.readReg64 .x22 = 1#64 ∧
        sm.readReg64 .x23 = cap_ct1 ∧
        sm.readReg64 .x24 = ptr_ct1 ∧
        sm.readReg64 .x26 = s0.sp - 480#64 ∧
        sm.readReg64 .x27 = s0.sp - 1360#64 ∧
        sm.readReg64 .x28 = epoch ∧
        TraceCalleeSaved sm s0)
      ?_
      (fun sm _Pm _ _ ⟨hvm, hPm, hspm, hx29m, hx19m, hx20m, hx21m,
          hx22m, hx23m, hx24m, hx26m, hx27m, hx28m, htrm⟩ => by
        refine ⟨1#64, ?_, hspm, hx29m, hx19m, hx20m, hx21m,
          hx22m, hx23m, hx24m, hx26m, hx27m, hx28m, htrm⟩
        rw [A.pool_of_vmPreserved hvm]
        exact hPm)
    by_vm_steps (
      wp_steps
      have hdealloc := vecU8CloneTail_entails_dealloc A.repAlloc cap_ct1 ptr_ct1 []
      have hnil := vecU8Heap_nil_intro A.repAlloc
        (vecCapPtrDealloc A.repAlloc cap_ct1 ptr_ct1 ∗
         A.pool lim st s ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame)
      simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hnil
      have hent :
          (ptr_ct1 ↦ₛ []) ∗ vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 [] ∗
          A.pool lim st s ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame ⊢
          vecU8Heap A.repAlloc 0#64 1#64 0#64 [] ∗
          vecCapPtrDealloc A.repAlloc cap_ct1 ptr_ct1 ∗
          A.pool lim st s ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame := by
        rw [show (ptr_ct1 ↦ₛ []) ∗ vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 [] ∗
            A.pool lim st s ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame =
            ((ptr_ct1 ↦ₛ []) ∗ vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 []) ∗
            (A.pool lim st s ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame) by sep_ac_rfl]
        exact Entails.trans (sepConj_mono_left hdealloc) hnil
      exact SepWP.weaken_pre hent (by wp_done))
  · have hpos : 0 < ct1.length := Nat.pos_of_ne_zero hlen_zero
    have hfits_alloc : FitsEvents M lim st (rustAllocEvents ct1.length 1) := by
      simpa only [ct1CloneEvents, hlen_zero, ↓reduceIte] using hfits
    simp only [ct1CloneEvents, hlen_zero, ↓reduceIte]
    have hbeq0 : (BitVec.ofNat 64 ct1.length == 0#64) = false :=
      ofNat_beq_zero_false' hpos (by omega)
    have hne0 : (BitVec.ofNat 64 ct1.length != 0#64) = true :=
      ofNat_ne_zero_true hpos (by omega)
    have htoNat_len : (BitVec.ofNat 64 ct1.length).toNat = ct1.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlay : RustLayoutOk ct1.length 1 := ⟨⟨hpos, ⟨0, rfl⟩, by omega⟩, by decide⟩
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
    have hsum1 : ct1.length + 1 ≤ 2 ^ 63 := by omega
    have hshim := noAllocShim_ok_placed hA
    have halloc := allocNoOom_ok_placed hA
    have hmemcpy := framelessMemcpy_ok_placed hA
    simp only [noAllocShimBudgetSpec] at hshim
    simp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte] at halloc
    simp only [framelessMemcpyBudgetSpec] at hmemcpy
    dsimp only [spqrRustNoAllocShimSym, spqrRustAllocSym, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hmemcpy ⊢
    wp_steps
    wp_call hshim ()
    have hvm_sf : VmPreserved s sf :=
      vmPreserved_prepend ‹VmPreserved _ sf› (by simp only [arm64_norm])
    refine SepWP.transport_budgetPool hvm_sf (hnext := ?_)
    wp_steps
    refine SepWP.transport_budgetPool (s1 := sf) (by simp only [arm64_norm]) (hnext := ?_)
    rw [← hsp, ← ‹sf.sp = s.sp›]
    wp_call halloc (ct1.length, 1, st)
    have htr_1 : sf_1.trace = s0.trace :=
      ‹AllocCallPreserved _ sf_1›.2.1.trans (‹sf.trace = _›.trans htrace)
    have hne_null : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
    have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hne_null
    have hoom_bne : (sf_1.readReg64 (Reg.gpr 0#5) != 0#64) = true :=
      bne_iff_ne.mpr hne_null
    let ptr_c := sf_1.readReg64 (Reg.gpr 0#5)
    wp_steps
    wp_call hmemcpy (ptr_c, ptr_ct1, ct1)
    have hvm_12 : VmPreserved sf_1 sf_2 :=
      vmPreserved_prepend ‹VmPreserved _ sf_2› (by simp only [arm64_norm])
    refine SepWP.transport_budgetPool hvm_12 (hnext := ?_)
    wp_steps
    have hbuf : (ptr_c ↦ₛ ct1) ∗ A.live ptr_c ct1.length 1 ⊢
        vecU8Heap A.repAlloc (BitVec.ofNat 64 ct1.length) ptr_c
          (BitVec.ofNat 64 ct1.length) ct1 := by
      rw [← A.repAlloc_live]
      exact vecU8Heap_of_exact_alloc A.repAlloc ptr_c ct1 hpos hlen hne_null
    have hdealloc := vecU8CloneTail_entails_dealloc A.repAlloc cap_ct1 ptr_ct1 ct1
    have hent :
        A.pool lim (M.stepEvents (rustAllocEvents ct1.length 1) st) sf_2 ∗
        (ptr_c ↦ₛ ct1) ∗ (ptr_ct1 ↦ₛ ct1) ∗
        stackAt sf.sp allocHookStack ∗
        A.live ptr_c ct1.length 1 ∗
        vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 ct1 ∗ Frame ⊢
        vecU8Heap A.repAlloc (BitVec.ofNat 64 ct1.length) ptr_c
          (BitVec.ofNat 64 ct1.length) ct1 ∗
        vecCapPtrDealloc A.repAlloc cap_ct1 ptr_ct1 ∗
        A.pool lim (M.stepEvents (rustAllocEvents ct1.length 1) st) sf_2 ∗
        stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame := by
      rw [‹sf.sp = s.sp›, hsp]
      refine Entails.trans (Entails.of_eq (show _ =
        ((ptr_c ↦ₛ ct1) ∗ A.live ptr_c ct1.length 1) ∗
        ((ptr_ct1 ↦ₛ ct1) ∗ vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 ct1) ∗
        (A.pool lim (M.stepEvents (rustAllocEvents ct1.length 1) st) sf_2 ∗
         stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
      exact sepConj_mono hbuf (sepConj_mono hdealloc (Entails.refl _))
    refine SepWP.weaken_pre hent ?_
    refine SepWP.mono
      (post := fun sm Pm =>
        (Pm ⊢ vecU8Heap A.repAlloc (BitVec.ofNat 64 ct1.length) ptr_c
            (BitVec.ofNat 64 ct1.length) ct1 ∗
          vecCapPtrDealloc A.repAlloc cap_ct1 ptr_ct1 ∗
          A.pool lim (M.stepEvents (rustAllocEvents ct1.length 1) st) sm ∗
          stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame) ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = stA ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 ct1.length ∧
        sm.readReg64 .x22 = ptr_c ∧
        sm.readReg64 .x23 = cap_ct1 ∧
        sm.readReg64 .x24 = ptr_ct1 ∧
        sm.readReg64 .x26 = s0.sp - 480#64 ∧
        sm.readReg64 .x27 = s0.sp - 1360#64 ∧
        sm.readReg64 .x28 = epoch ∧
        TraceCalleeSaved sm s0)
      (by wp_done)
      (fun _ _ _ _ h => ⟨ptr_c, by rwa [‹sf.sp = s.sp›, hsp]⟩)

/-- Step 2 (`+1760 -> +2252` in Block `334`, CPS `SepWPp` form, parametric in `{Q Qp}`). -/
theorem ekReceivedCt1Sampled_step_1760_to_2252_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {Q Qp : State → SepProp → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (s0 s : State) (st : M.σ) (out stA cap_ct1 ptr_ct1 epoch : BitVec 64)
    (ct1 : List (BitVec 8))
    (Frame : SepProp)
    (hfits : FitsEvents M lim st (ct1CloneEvents ct1))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : ct1.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_334).base + 1760#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 ct1.length)
    (hx23 : s.readReg64 .x23 = cap_ct1)
    (hx24 : s.readReg64 .x24 = ptr_ct1)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx28 : s.readReg64 .x28 = epoch)
    (htrace : TraceCalleeSaved s s0)
    (hnext : ∀ (sm : State) (ptr_new : BitVec 64),
      sm.pc = (blkPl_334).base + 2252#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 1520#64 →
      sm.readReg64 .x29 = s0.sp - 96#64 →
      sm.readReg64 .x19 = out →
      sm.readReg64 .x20 = stA →
      sm.readReg64 .x21 = BitVec.ofNat 64 ct1.length →
      sm.readReg64 .x22 = ptr_new →
      sm.readReg64 .x23 = cap_ct1 →
      sm.readReg64 .x24 = ptr_ct1 →
      sm.readReg64 .x26 = s0.sp - 480#64 →
      sm.readReg64 .x27 = s0.sp - 1360#64 →
      sm.readReg64 .x28 = epoch →
      TraceCalleeSaved sm s0 →
      SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sm
        (vecU8Heap A.repAlloc (BitVec.ofNat 64 ct1.length) ptr_new
            (BitVec.ofNat 64 ct1.length) ct1 ∗
         vecCapPtrDealloc A.repAlloc cap_ct1 ptr_ct1 ∗
         A.pool lim (M.stepEvents (ct1CloneEvents ct1) st) sm ∗
         stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      ((ptr_ct1 ↦ₛ ct1) ∗
       vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 ct1 ∗
       A.pool lim st s ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame)
      Q Qp := by
  have hwp := ekReceivedCt1Sampled_step_1760_to_2252_wp_placed hA s0 s st out stA cap_ct1 ptr_ct1 epoch
    ct1 Frame hfits hsp0_align hlen hpc hrun hsp hx29 hx19 hx20 hx21 hx23 hx24 hx26 hx27 hx28 htrace
  refine SepWPp.of_sepWP (mid := (blkPl_334).base + 2252#64) ?_
  refine SepWP.mono hwp fun sm Pm hpcm hrunm
      ⟨ptr_new, hPm, hspm, hx29m, hx19m, hx20m, hx21m, hx22m,
        hx23m, hx24m, hx26m, hx27m, hx28m, htrm⟩ => ?_
  exact SepWPp.weaken_pre hPm
    (hnext sm ptr_new hpcm hrunm hspm hx29m hx19m hx20m hx21m hx22m
      hx23m hx24m hx26m hx27m hx28m htrm)

/-- Step 3 (`+2252 -> +2324` in Block `334`): move `auth` from `s0.sp - 1360..1312` (`t0..t5`) to
    `s0.sp - 256..208` (`v0..v5`), load `es` and `ek` from `stA + 456..496` into
    `s0.sp - 480..432` (`u0..u5`), and deallocate `(cap_ct1, ptr_ct1)` via
    `cbz x23, +2324; bl __rust_dealloc`, advancing `st` by `ct1DeallocEvents cap_ct1`. -/
theorem ekReceivedCt1Sampled_step_2252_to_2324_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (s0 s : State) (st : M.σ) (out stA cap_ct1 ptr_ct1 ptr_new len_ct1 epoch : BitVec 64)
    (a0 a1 a2 a3 a4 a5 es0 es1 es2 ek0 ek1 ek2 : BitVec 64)
    (t6 t7 t8 t8' t9 t10 t11 t12 t13 t14 : BitVec 64)
    (u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_334).base + 2252#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = len_ct1)
    (hx22 : s.readReg64 .x22 = ptr_new)
    (hx23 : s.readReg64 .x23 = cap_ct1)
    (hx24 : s.readReg64 .x24 = ptr_ct1)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx28 : s.readReg64 .x28 = epoch)
    (htrace : TraceCalleeSaved s s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 2324#64) s
      (((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
       ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
       ekReceivedScratchCells s0.sp
         a0 a1 a2 a3 a4 a5 t6 t7 t8 t8' t9 t10 t11 t12 t13 t14
         u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 ∗
       vecCapPtrDealloc A.repAlloc cap_ct1 ptr_ct1 ∗
       A.pool lim st s ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
          ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
          ekReceivedScratchCells s0.sp
            a0 a1 a2 a3 a4 a5 t6 t7 t8 t8' t9 t10 t11 t12 t13 t14
            es0 es1 es2 ek0 ek1 ek2 a0 a1 a2 a3 a4 a5 ∗
          A.pool lim (M.stepEvents (ct1DeallocEvents cap_ct1) st) sm ∗
          stackAt (s0.sp - 1520#64) allocHookStack ∗ Rest) ∧
        AllocCallPreserved s sm ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = stA ∧
        sm.readReg64 .x21 = len_ct1 ∧
        sm.readReg64 .x22 = ptr_new ∧
        sm.readReg64 .x27 = s0.sp - 1360#64 ∧
        sm.readReg64 .x28 = epoch ∧
        TraceCalleeSaved sm s0) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hdealloc := dealloc_ok_placed hA
  simp only [rustCliDeallocBudgetSpec] at hdealloc
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  by_cases hc : (cap_ct1 == 0#64) = true
  · have hc_bne : (cap_ct1 != 0#64) = false := by
      rcases eq_or_ne cap_ct1 0#64 with rfl | hne
      · rfl
      · exact False.elim (hne (beq_iff_eq.mp hc))
    simp only [ct1DeallocEvents, vecCapPtrDealloc, hc, ↓reduceIte, M.stepEvents_nil,
      sepConj_emp, emp_sepConj]
    refine SepWP.mono
      (post := fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢
          ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
          ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
          ekReceivedScratchCells s0.sp
            a0 a1 a2 a3 a4 a5 t6 t7 t8 t8' t9 t10 t11 t12 t13 t14
            es0 es1 es2 ek0 ek1 ek2 a0 a1 a2 a3 a4 a5 ∗
          A.pool lim st s ∗
          stackAt (s0.sp - 1520#64) allocHookStack ∗ Rest) ∧
        AllocCallPreserved s sm ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = stA ∧
        sm.readReg64 .x21 = len_ct1 ∧
        sm.readReg64 .x22 = ptr_new ∧
        sm.readReg64 .x27 = s0.sp - 1360#64 ∧
        sm.readReg64 .x28 = epoch ∧
        TraceCalleeSaved sm s0)
      ?_
      (fun sm _Pm _ _ ⟨hvm, hPm, hacp, hrest⟩ => by
        refine ⟨?_, hacp, hrest⟩
        rw [A.pool_of_vmPreserved hvm]
        exact hPm)
    dsimp only [ekReceivedScratchCells, BitVec.ofNat_eq_ofNat] at hpc ⊢
    by_vm_steps (
      wp_steps
      refine align_pre (by sep_ac_rfl) ?_
      wp_done)
  · have hc_beq : (cap_ct1 == 0#64) = false := Bool.eq_false_iff.mpr hc
    have hc_bne : (cap_ct1 != 0#64) = true := by
      rw [bne_iff_ne]; intro h; exact hc (beq_iff_eq.mpr h)
    simp only [ct1DeallocEvents, vecCapPtrDealloc, hc, Bool.false_eq_true, ↓reduceIte,
      A.repAlloc_live]
    refine seq_vm_step
      (mid := lsρ spqrRustDeallocSym)
      (P_mid :=
        ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
        ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
        ekReceivedScratchCells s0.sp
          a0 a1 a2 a3 a4 a5 t6 t7 t8 t8' t9 t10 t11 t12 t13 t14
          es0 es1 es2 ek0 ek1 ek2 a0 a1 a2 a3 a4 a5 ∗
        (A.live ptr_ct1 cap_ct1.toNat 1 ∗ memRegion ptr_ct1 cap_ct1.toNat) ∗
        A.pool lim st s ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Rest)
      (Q := fun sc =>
        AllocCallPreserved s sc ∧
        sc.sp = s0.sp - 1520#64 ∧
        sc.readReg64 .x30 = (blkPl_334).base + 2324#64 ∧
        sc.readReg64 .x0 = ptr_ct1 ∧
        sc.readReg64 .x1 = cap_ct1 ∧
        sc.readReg64 .x2 = 1#64 ∧
        sc.readReg64 .x29 = s0.sp - 96#64 ∧
        sc.readReg64 .x19 = out ∧
        sc.readReg64 .x20 = stA ∧
        sc.readReg64 .x21 = len_ct1 ∧
        sc.readReg64 .x22 = ptr_new ∧
        sc.readReg64 .x27 = s0.sp - 1360#64 ∧
        sc.readReg64 .x28 = epoch ∧
        TraceCalleeSaved sc s0)
      ?_ ?_
    · dsimp only [spqrRustDeallocSym, ekReceivedScratchCells, BitVec.ofNat_eq_ofNat] at hpc ⊢
      by_vm_steps (
        wp_steps
        refine align_pre (by sep_ac_rfl) ?_
        wp_done)
    · intro sc hpcc hrunc hvmc ⟨hacp_sc, hspc, hx30c, hx0c, hx1c, hx2c,
        hx29c, hx19c, hx20c, hx21c, hx22c, hx27c, hx28c, htrc, hvregsc⟩
      rw [← A.pool_of_vmPreserved hvmc, ← hspc]
      dsimp only [spqrRustDeallocSym, BitVec.ofNat_eq_ofNat] at hpcc hx30c hdealloc ⊢
      wp_call hdealloc (ptr_ct1, cap_ct1.toNat, 1, st)
      have hacp_cf : AllocCallPreserved sc sf := by assumption
      rcases allocCallPreserved_trans hacp_sc hacp_cf with
        ⟨hfs_sf, htr_s_sf, hsig_sf, htp_sf, hbrk_sf, hor_sf, hsym_sf⟩
      have htr_sf : sf.trace = s0.trace := hacp_cf.2.1.trans htrc
      rw [hspc]
      refine align_pre (by sep_ac_rfl) ?_
      wp_done

/-- Step 4 (`+2324 -> +2340` in Block `334`, direct `SepWP` form):
    calls `<PolyEncoder>::into_pb(s0.sp - 1232, stA + 8)` (`lsmpl.base 375`) under
    `FitsEnv M lim st (EncoderIntoPbAllocEnv enc)`. -/
theorem ekReceivedCt1Sampled_step_2324_to_2340_wp_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (henc : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (s0 s : State) (st : M.σ) (out stA ptr_new len_ct1 epoch : BitVec 64)
    (enc : PolyEncoder)
    (Frame : SepProp)
    (hfits : FitsEnv M lim st (EncoderIntoPbAllocEnv enc))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_334).base + 2324#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = len_ct1)
    (hx22 : s.readReg64 .x22 = ptr_new)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx28 : s.readReg64 .x28 = epoch)
    (htrace : TraceCalleeSaved s s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 2340#64) s
      (memRegion (s0.sp - 1232#64) 56 ∗
       polyEncoderAt A.repAlloc (stA + 8#64) enc ∗
       A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
      (fun sm Pm =>
        ∃ (evs : List AllocEvent) (e0 e1 e2 e3 e4 e5 e6 : BitVec 64),
          EncoderIntoPbEnv enc evs ∧
          AllocCallPreserved s sm ∧
          (Pm ⊢
            (((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
             ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
             ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
             ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
            protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 enc.intoPb ∗
            memRegion (stA + 8#64) polyEncoderSize ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame) ∧
          sm.sp = s0.sp - 1520#64 ∧
          sm.readReg64 .x29 = s0.sp - 96#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = stA ∧
          sm.readReg64 .x21 = len_ct1 ∧
          sm.readReg64 .x22 = ptr_new ∧
          sm.readReg64 .x27 = s0.sp - 1360#64 ∧
          sm.readReg64 .x28 = epoch ∧
          TraceCalleeSaved sm s0) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  refine seq_vm_step
    (mid := lsmpl.base 375)
    (P_mid :=
      memRegion (s0.sp - 1232#64) 56 ∗
      polyEncoderAt A.repAlloc (stA + 8#64) enc ∗
      A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
    (Q := fun sc =>
      AllocCallPreserved s sc ∧
      sc.sp = s0.sp - 1520#64 ∧
      sc.readReg64 .x29 = s0.sp - 96#64 ∧
      sc.readReg64 .x19 = out ∧
      sc.readReg64 .x20 = stA ∧
      sc.readReg64 .x21 = len_ct1 ∧
      sc.readReg64 .x22 = ptr_new ∧
      sc.readReg64 .x27 = s0.sp - 1360#64 ∧
      sc.readReg64 .x28 = epoch ∧
      sc.readReg64 .x0 = s0.sp - 1232#64 ∧
      sc.readReg64 .x1 = stA + 8#64 ∧
      sc.readReg64 .x30 = (blkPl_334).base + 2340#64 ∧
      TraceCalleeSaved sc s0)
    ?_ ?_
  · by_vm_steps (
      wp_steps
      wp_done)
  · intro sc hpcc hrunc hvmc ⟨hacp_sc, hspc, hx29c, hx19c, hx20c, hx21c, hx22c,
      hx27c, hx28c, hx0c, hx1c, hx30c, htrc⟩
    rw [← A.pool_of_vmPreserved hvmc]
    exact call_encoderIntoPb_expose_wp_placed henc st (s0.sp - 1232#64) (stA + 8#64) enc
      hpcc hrunc hspc hfsp_align hx30c htrc hx0c hx1c hfits
      (by sep_ac_rfl)
      (fun sm evs e0 e1 e2 e3 e4 e5 e6 hpcm hrunm hspm hcc hacp_cm htrm henv =>
        SepWP.done hpcm hrunm
          ⟨evs, e0, e1, e2, e3, e4, e5, e6, henv, allocCallPreserved_trans hacp_sc hacp_cm,
            Entails.of_eq (by sep_ac_rfl),
            hspm,
            hcc.2.2.2.2.2.2.2.2.2.2.1.trans hx29c,
            hcc.1.trans hx19c,
            hcc.2.1.trans hx20c,
            hcc.2.2.1.trans hx21c,
            hcc.2.2.2.1.trans hx22c,
            hcc.2.2.2.2.2.2.2.2.1.trans hx27c,
            hcc.2.2.2.2.2.2.2.2.2.1.trans hx28c,
            htrm⟩)

/-- Step 4 (`+2324 -> +2340` in Block `334`, CPS `SepWPp` form, parametric in `{Q Qp}`). -/
theorem ekReceivedCt1Sampled_step_2324_to_2340_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {Q Qp : State → SepProp → Prop}
    (henc : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (s0 s : State) (st : M.σ) (out stA ptr_new len_ct1 epoch : BitVec 64)
    (enc : PolyEncoder)
    (Frame : SepProp)
    (hfits : FitsEnv M lim st (EncoderIntoPbAllocEnv enc))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_334).base + 2324#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = len_ct1)
    (hx22 : s.readReg64 .x22 = ptr_new)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx28 : s.readReg64 .x28 = epoch)
    (htrace : TraceCalleeSaved s s0)
    (hnext : ∀ (sm : State) (evs : List AllocEvent) (e0 e1 e2 e3 e4 e5 e6 : BitVec 64),
      EncoderIntoPbEnv enc evs →
      AllocCallPreserved s sm →
      sm.pc = (blkPl_334).base + 2340#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 1520#64 →
      sm.readReg64 .x29 = s0.sp - 96#64 →
      sm.readReg64 .x19 = out →
      sm.readReg64 .x20 = stA →
      sm.readReg64 .x21 = len_ct1 →
      sm.readReg64 .x22 = ptr_new →
      sm.readReg64 .x27 = s0.sp - 1360#64 →
      sm.readReg64 .x28 = epoch →
      TraceCalleeSaved sm s0 →
      SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sm
        ((((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
          ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
          ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
          ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
         protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 enc.intoPb ∗
         memRegion (stA + 8#64) polyEncoderSize ∗
         A.pool lim (M.stepEvents evs st) sm ∗
         stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (memRegion (s0.sp - 1232#64) 56 ∗
       polyEncoderAt A.repAlloc (stA + 8#64) enc ∗
       A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
      Q Qp := by
  have hwp := ekReceivedCt1Sampled_step_2324_to_2340_wp_placed henc s0 s st out stA ptr_new len_ct1 epoch
    enc Frame hfits hsp0_align hpc hrun hsp hx29 hx19 hx20 hx21 hx22 hx27 hx28 htrace
  refine SepWPp.of_sepWP (mid := (blkPl_334).base + 2340#64) ?_
  refine SepWP.mono hwp fun sm Pm hpcm hrunm
      ⟨evs, e0, e1, e2, e3, e4, e5, e6, henv, hacp, hPm, hspm, hx29m, hx19m, hx20m,
        hx21m, hx22m, hx27m, hx28m, htrm⟩ => ?_
  exact SepWPp.weaken_pre hPm
    (hnext sm evs e0 e1 e2 e3 e4 e5 e6 henv hacp hpcm hrunm hspm hx29m hx19m hx20m
      hx21m hx22m hx27m hx28m htrm)

/-- Step 5 (`+2340 -> +1544` in Block `334`): pack `es`, `ek`, `ct1`, `auth`, `epoch`, and
    `sending_ct1.intoPb` into `epilogueStagingCells` (with `x22 = 0x8000000000000008#64` and
    `x21 = len_ct1`) and branch to `+1544`, preserving `VmPreserved` and `AllocCallPreserved`. -/
theorem ekReceivedCt1Sampled_step_2340_to_1544_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (out stA ptr_new len_ct1 epoch : BitVec 64)
    (a0 a1 a2 a3 a4 a5 es0 es1 es2 ek0 ek1 ek2 : BitVec 64)
    (e0 e1 e2 e3 e4 e5 e6 : BitVec 64)
    (t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 : BitVec 64)
    (w8 w16 w24 w32 w40 w48
     w64 w72 w80 w88 w96 w104 w112 w120
     w128 w136 w144 w152 w160 w168 w176 w184
     w192 w200 w208 w216 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_334).base + 2340#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = len_ct1)
    (hx22 : s.readReg64 .x22 = ptr_new)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx28 : s.readReg64 .x28 = epoch)
    (htrace : TraceCalleeSaved s s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 1544#64) s
      (ekReceivedScratchCells s0.sp
         a0 a1 a2 a3 a4 a5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
         es0 es1 es2 ek0 ek1 ek2 a0 a1 a2 a3 a4 a5 ∗
       (((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
        ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
        ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
        ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
       epilogueStagingCells s0.sp
         w8 w16 w24 w32 w40 w48
         w64 w72 w80 w88 w96 w104 w112 w120
         w128 w136 w144 w152 w160 w168 w176 w184
         w192 w200 w208 w216 ∗
       Rest)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢
          ekReceivedScratchCells s0.sp
            es0 es1 es2 ek0 ek1 ek2 t6 ptr_new len_ct1 a0 a1 a2 a3 a4 a5 epoch
            es0 es1 es2 ek0 ek1 ek2 a0 a1 a2 a3 a4 a5 ∗
          (((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
           ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
           ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
           ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
          epilogueStagingCells s0.sp
            es0 es1 es2 ek0 ek1 ek2
            ptr_new len_ct1 a0 a1 a2 a3 a4 a5
            epoch e0 e1 e2 e3 e4 e5 e6
            w192 w200 w208 w216 ∗
          Rest) ∧
        AllocCallPreserved s sm ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = len_ct1 ∧
        sm.readReg64 .x22 = 0x8000000000000008#64 ∧
        TraceCalleeSaved sm s0) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  dsimp only [ekReceivedScratchCells, epilogueStagingCells, BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps (
    wp_steps
    refine align_pre (by sep_ac_rfl) ?_
    wp_done)

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aPlacedBudgetAux
