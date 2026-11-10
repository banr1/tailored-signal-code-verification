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
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`) — Part 5b Placed: Arm 9 (`States.ct1Acknowledged`) Step Lemmas

Relocatable `[LibsignalPlacement]` step lemmas on Block `334` for Arm 9 (`States.ct1Acknowledged`,
tag `11`), threading `RustCliAllocBudget M`, `BudgetLimits`, `FitsEvents`, `FreeOnlyEvs`,
`VmPreserved`, and `AllocCallPreserved`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement libsignalSessionCode lsmpl lsρ)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Drop
  (none2Cap_add_two_beq_zero noneCap_add_two_beq_zero vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly.DecoderPb (spqrRustDeallocSym)
open CryptoVerification.SpqrV1.States.IntoPb
  (TraceCalleeSaved bv_add_add_lit' bv_sub_sub_lit'
   ct1AcknowledgedScratchCells epilogueStagingCells
   ofNat_beq_zero_false' ofNat_lt_2pow63_and_highBit_zero
   ofNat_lt_2pow63_lsr63_zero ofNat_lt_2pow63_msb_zero ofNat_ne_zero_true
   statesIntoPbJumpTableBytes statesIntoPbJumpTablePlacedAt
   vecU8CloneTail vecU8CloneTail_entails_dealloc vecU8Heap vecU8Heap_nil_intro
   vecU8Heap_of_exact_alloc)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEvents
   FreeOnlyEvs RustCliAllocBudget RustLayoutOk VmPreserved rustAllocEvents
   rustCliAllocNoOomSpec rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5PlacedBudget
  (StatesIntoPbAllocPlacedBudget allocNoOom_ok_placed dealloc_ok_placed
   framelessMemcpy_ok_placed noAllocShim_ok_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget
  (ct1CloneEvents ct1DeallocEvents freeOnlyEvs_ct1DeallocEvents)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (framelessMemcpyBudgetSpec noAllocShimBudgetSpec)

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## 1. Re-Exports from `Part5bBudget` and `Part5PlacedBudget` -/

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget
  (ct1CloneEvents ct1DeallocEvents freeOnlyEvs_ct1DeallocEvents
   words4 words4_polyDecoderAt unchunkedCt1Sent_expose_clone
   chunkedCt1Acknowledged_expose stA_ct1Acknowledged_entails_928
   memRegion_ct1Acknowledged_scratch_split
   ct1AcknowledgedScratchCells_entails_memRegions
   outWords28_entails_ct1Acknowledged)

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

/-! ## 2. Relocatable Step Lemmas for Arm 9 (`States.ct1Acknowledged`, Block `334`) -/

/-- Step 1b (`+60 -> +372` in Block `334`): jump-table dispatch for tag `11#64` (index `9` -> `+360`)
    and setup for `memcpy(s0.sp - 1360, stA + 8, 528)` at `+372` (`lsρ "memcpy"`), preserving
    `VmPreserved` and `AllocCallPreserved`. -/
theorem ct1Acknowledged_step_60_to_372_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (out stA : BitVec 64)
    (Rest : SepProp)
    (hpc : s.pc = (blkPl_334).base + 60#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 256#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx20 : s.readReg64 .x20 = stA)
    (hx19 : s.readReg64 .x19 = out)
    (hx8 : s.readReg64 .x8 = 11#64)
    (htrace : TraceCalleeSaved s s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") s
      (statesIntoPbJumpTablePlacedAt ∗ Rest)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ statesIntoPbJumpTablePlacedAt ∗ Rest) ∧
        AllocCallPreserved s sm ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x30 = (blkPl_334).base + 376#64 ∧
        sm.readReg64 .x0 = s0.sp - 1360#64 ∧
        sm.readReg64 .x1 = stA + 8#64 ∧
        (sm.readReg64 .x2).toNat = 528 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x28 = s0.sp - 256#64 ∧
        sm.readReg64 .x26 = s0.sp - 480#64 ∧
        sm.readReg64 .x20 = stA ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  rcases htrace with ⟨htrace, hvregs⟩
  dsimp only [statesIntoPbJumpTablePlacedAt, statesIntoPbJumpTableBytes, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  wp_done

/-- Step 2 (`+376 -> +424` in Block `334`): load `cap_ct1`, `ptr_ct1`, `len_ct1`, `epoch` from
    `s0.sp - 1264..1240`, copy `a0..a5` from `stA + 8..48` to `s0.sp - 480..440` (`u0..u5`), and
    take fallthrough of `tbnz x21, #0x3f, +1696`, preserving `VmPreserved` and
    `AllocCallPreserved`. -/
theorem ct1Acknowledged_step_376_to_424_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (out stA : BitVec 64)
    (a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2 cap_ct1 ptr_ct1 epoch : BitVec 64)
    (len_ct1 : Nat)
    (u0 u1 u2 u3 u4 u5 : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 : BitVec 64)
    (w0 w1 w2 w3 w4 w5 : BitVec 64)
    (y0 y1 y2 y3 y4 y5 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : len_ct1 < 2 ^ 63)
    (hpc : s.pc = (blkPl_334).base + 376#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 256#64)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx20 : s.readReg64 .x20 = stA)
    (hx19 : s.readReg64 .x19 = out)
    (htrace : TraceCalleeSaved s s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 424#64) s
      ((((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
        ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
        ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
       (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
        ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 len_ct1) ∗
        ((s0.sp - 1240#64) ↦₆₄ epoch)) ∗
       ct1AcknowledgedScratchCells s0.sp
         u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 v6 v7 v8
         w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
       Rest)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢
          (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
           ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
           ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
           ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
          (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
           ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 len_ct1) ∗
           ((s0.sp - 1240#64) ↦₆₄ epoch)) ∗
          ct1AcknowledgedScratchCells s0.sp
            a0 a1 a2 a3 a4 a5 v0 v1 v2 v3 v4 v5 v6 v7 v8
            w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
          Rest) ∧
        AllocCallPreserved s sm ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x28 = s0.sp - 256#64 ∧
        sm.readReg64 .x27 = epoch ∧
        sm.readReg64 .x26 = s0.sp - 480#64 ∧
        sm.readReg64 .x24 = ptr_ct1 ∧
        sm.readReg64 .x23 = cap_ct1 ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 len_ct1 ∧
        sm.readReg64 .x20 = stA ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hmsb := ofNat_lt_2pow63_msb_zero hlen
  have hand := ofNat_lt_2pow63_and_highBit_zero hlen
  have hlsr := ofNat_lt_2pow63_lsr63_zero hlen
  dsimp only [ct1AcknowledgedScratchCells, BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps (
    wp_steps
    refine align_pre (by sep_ac_rfl) ?_
    wp_done)

/-- Step 3 (`+424 -> +1812` in Block `334`, direct `SepWP` form under `FitsEvents`):
    clones `ct1 : List (BitVec 8)` without OOM or panic, advancing `st` by `ct1CloneEvents ct1`. -/
theorem ct1Acknowledged_step_424_to_1812_wp_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (s0 s : State) (st : M.σ) (out stA cap_ct1 ptr_ct1 epoch : BitVec 64)
    (ct1 : List (BitVec 8))
    (Frame : SepProp)
    (hfits : FitsEvents M lim st (ct1CloneEvents ct1))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : ct1.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_334).base + 424#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 256#64)
    (hx27 : s.readReg64 .x27 = epoch)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx24 : s.readReg64 .x24 = ptr_ct1)
    (hx23 : s.readReg64 .x23 = cap_ct1)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 ct1.length)
    (hx20 : s.readReg64 .x20 = stA)
    (hx19 : s.readReg64 .x19 = out)
    (htrace : TraceCalleeSaved s s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 1812#64) s
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
          sm.readReg64 .x28 = s0.sp - 256#64 ∧
          sm.readReg64 .x27 = epoch ∧
          sm.readReg64 .x26 = s0.sp - 480#64 ∧
          sm.readReg64 .x24 = ptr_ct1 ∧
          sm.readReg64 .x23 = cap_ct1 ∧
          sm.readReg64 .x22 = ptr_new ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 ct1.length ∧
          sm.readReg64 .x20 = stA ∧
          sm.readReg64 .x19 = out ∧
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
        sm.readReg64 .x28 = s0.sp - 256#64 ∧
        sm.readReg64 .x27 = epoch ∧
        sm.readReg64 .x26 = s0.sp - 480#64 ∧
        sm.readReg64 .x24 = ptr_ct1 ∧
        sm.readReg64 .x23 = cap_ct1 ∧
        sm.readReg64 .x22 = 1#64 ∧
        sm.readReg64 .x21 = 0#64 ∧
        sm.readReg64 .x20 = stA ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0)
      ?_
      (fun sm _Pm _ _ ⟨hvm, hPm, hspm, hx29m, hx28m, hx27m, hx26m,
          hx24m, hx23m, hx22m, hx21m, hx20m, hx19m, htrm⟩ => by
        refine ⟨1#64, ?_, hspm, hx29m, hx28m, hx27m, hx26m,
          hx24m, hx23m, hx22m, hx21m, hx20m, hx19m, htrm⟩
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
        sm.readReg64 .x28 = s0.sp - 256#64 ∧
        sm.readReg64 .x27 = epoch ∧
        sm.readReg64 .x26 = s0.sp - 480#64 ∧
        sm.readReg64 .x24 = ptr_ct1 ∧
        sm.readReg64 .x23 = cap_ct1 ∧
        sm.readReg64 .x22 = ptr_c ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 ct1.length ∧
        sm.readReg64 .x20 = stA ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0)
      (by wp_done)
      (fun _ _ _ _ h => ⟨ptr_c, by rwa [‹sf.sp = s.sp›, hsp]⟩)

/-- Step 3 (`+424 -> +1812` in Block `334`, CPS `SepWPp` form, parametric in `{Q Qp}`):
    clones `s.uc.ct1` under `FitsEvents M lim st (ct1CloneEvents ct1)`. -/
theorem ct1Acknowledged_step_424_to_1812_placed [LibsignalPlacement]
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
    (hpc : s.pc = (blkPl_334).base + 424#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 256#64)
    (hx27 : s.readReg64 .x27 = epoch)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx24 : s.readReg64 .x24 = ptr_ct1)
    (hx23 : s.readReg64 .x23 = cap_ct1)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 ct1.length)
    (hx20 : s.readReg64 .x20 = stA)
    (hx19 : s.readReg64 .x19 = out)
    (htrace : TraceCalleeSaved s s0)
    (hnext : ∀ (sm : State) (ptr_new : BitVec 64),
      sm.pc = (blkPl_334).base + 1812#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 1520#64 →
      sm.readReg64 .x29 = s0.sp - 96#64 →
      sm.readReg64 .x28 = s0.sp - 256#64 →
      sm.readReg64 .x27 = epoch →
      sm.readReg64 .x26 = s0.sp - 480#64 →
      sm.readReg64 .x24 = ptr_ct1 →
      sm.readReg64 .x23 = cap_ct1 →
      sm.readReg64 .x22 = ptr_new →
      sm.readReg64 .x21 = BitVec.ofNat 64 ct1.length →
      sm.readReg64 .x20 = stA →
      sm.readReg64 .x19 = out →
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
  have hwp := ct1Acknowledged_step_424_to_1812_wp_placed hA s0 s st out stA cap_ct1 ptr_ct1 epoch
    ct1 Frame hfits hsp0_align hlen hpc hrun hsp hx29 hx28 hx27 hx26 hx24 hx23 hx21 hx20 hx19 htrace
  refine SepWPp.of_sepWP (mid := (blkPl_334).base + 1812#64) ?_
  refine SepWP.mono hwp fun sm Pm hpcm hrunm
      ⟨ptr_new, hPm, hspm, hx29m, hx28m, hx27m, hx26m,
        hx24m, hx23m, hx22m, hx21m, hx20m, hx19m, htrm⟩ => ?_
  exact SepWPp.weaken_pre hPm
    (hnext sm ptr_new hpcm hrunm hspm hx29m hx28m hx27m hx26m
      hx24m hx23m hx22m hx21m hx20m hx19m htrm)

/-- Step 4 (`+1812 -> +1900` in Block `334`): move `a0..a5` from `s0.sp - 480..440` (`u0..u5`) to
    `s0.sp - 160..120` (`y0..y5`), copy `hdr0..hdr2, es0..es2` from `stA + 56..96` to
    `s0.sp - 256..216` (`w0..w5`), deallocate `(cap_ct1, ptr_ct1)` via `__rust_dealloc`
    (advancing `st` by `ct1DeallocEvents cap_ct1` with `FreeOnlyEvs`), and set up
    `<PolyDecoder>::into_pb(s0.sp - 352, s0.sp - 1232)` at `+1900` (`lsmpl.base 377`). -/
theorem ct1Acknowledged_step_1812_to_1900_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (s0 s : State) (st : M.σ) (out stA cap_ct1 ptr_ct1 ptr_new len_ct1 epoch : BitVec 64)
    (a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2 : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 : BitVec 64)
    (w0 w1 w2 w3 w4 w5 : BitVec 64)
    (y0 y1 y2 y3 y4 y5 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_334).base + 1812#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 256#64)
    (hx27 : s.readReg64 .x27 = epoch)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx24 : s.readReg64 .x24 = ptr_ct1)
    (hx23 : s.readReg64 .x23 = cap_ct1)
    (hx22 : s.readReg64 .x22 = ptr_new)
    (hx21 : s.readReg64 .x21 = len_ct1)
    (hx20 : s.readReg64 .x20 = stA)
    (hx19 : s.readReg64 .x19 = out)
    (htrace : TraceCalleeSaved s s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) s
      ((((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
        ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
        ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
       ct1AcknowledgedScratchCells s0.sp
         a0 a1 a2 a3 a4 a5 v0 v1 v2 v3 v4 v5 v6 v7 v8
         w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
       vecCapPtrDealloc A.repAlloc cap_ct1 ptr_ct1 ∗
       A.pool lim st s ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
           ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
           ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
           ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
          ct1AcknowledgedScratchCells s0.sp
            a0 a1 a2 a3 a4 a5 v0 v1 v2 v3 v4 v5 v6 v7 v8
            hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
          A.pool lim (M.stepEvents (ct1DeallocEvents cap_ct1) st) sm ∗
          stackAt (s0.sp - 1520#64) allocHookStack ∗ Rest) ∧
        AllocCallPreserved s sm ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x30 = (blkPl_334).base + 1904#64 ∧
        sm.readReg64 .x0 = s0.sp - 352#64 ∧
        sm.readReg64 .x1 = s0.sp - 1232#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x27 = epoch ∧
        sm.readReg64 .x26 = s0.sp - 480#64 ∧
        sm.readReg64 .x22 = ptr_new ∧
        sm.readReg64 .x21 = len_ct1 ∧
        sm.readReg64 .x19 = out ∧
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
          (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
           ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
           ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
           ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
          ct1AcknowledgedScratchCells s0.sp
            a0 a1 a2 a3 a4 a5 v0 v1 v2 v3 v4 v5 v6 v7 v8
            hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
          A.pool lim st s ∗
          stackAt (s0.sp - 1520#64) allocHookStack ∗ Rest) ∧
        AllocCallPreserved s sm ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x30 = (blkPl_334).base + 1904#64 ∧
        sm.readReg64 .x0 = s0.sp - 352#64 ∧
        sm.readReg64 .x1 = s0.sp - 1232#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x27 = epoch ∧
        sm.readReg64 .x26 = s0.sp - 480#64 ∧
        sm.readReg64 .x22 = ptr_new ∧
        sm.readReg64 .x21 = len_ct1 ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0)
      ?_
      (fun sm _Pm _ _ ⟨hvm, hPm, hacp, hrest⟩ => by
        refine ⟨?_, hacp, hrest⟩
        rw [A.pool_of_vmPreserved hvm]
        exact hPm)
    dsimp only [ct1AcknowledgedScratchCells, BitVec.ofNat_eq_ofNat] at hpc ⊢
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
        (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
         ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
         ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
         ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
        ct1AcknowledgedScratchCells s0.sp
          a0 a1 a2 a3 a4 a5 v0 v1 v2 v3 v4 v5 v6 v7 v8
          hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
        (A.live ptr_ct1 cap_ct1.toNat 1 ∗ memRegion ptr_ct1 cap_ct1.toNat) ∗
        A.pool lim st s ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Rest)
      (Q := fun sc =>
        AllocCallPreserved s sc ∧
        sc.sp = s0.sp - 1520#64 ∧
        sc.readReg64 .x30 = (blkPl_334).base + 1884#64 ∧
        sc.readReg64 .x0 = ptr_ct1 ∧
        sc.readReg64 .x1 = cap_ct1 ∧
        sc.readReg64 .x2 = 1#64 ∧
        sc.readReg64 .x29 = s0.sp - 96#64 ∧
        sc.readReg64 .x27 = epoch ∧
        sc.readReg64 .x26 = s0.sp - 480#64 ∧
        sc.readReg64 .x22 = ptr_new ∧
        sc.readReg64 .x21 = len_ct1 ∧
        sc.readReg64 .x19 = out ∧
        TraceCalleeSaved sc s0)
      ?_ ?_
    · dsimp only [spqrRustDeallocSym, ct1AcknowledgedScratchCells, BitVec.ofNat_eq_ofNat] at hpc ⊢
      by_vm_steps (
        wp_steps
        refine align_pre (by sep_ac_rfl) ?_
        wp_done)
    · intro sc hpcc hrunc hvmc ⟨hacp_sc, hspc, hx30c, hx0c, hx1c, hx2c,
        hx29c, hx27c, hx26c, hx22c, hx21c, hx19c, htrc, hvregsc⟩
      rw [← A.pool_of_vmPreserved hvmc, ← hspc]
      dsimp only [spqrRustDeallocSym, BitVec.ofNat_eq_ofNat] at hpcc hx30c hdealloc ⊢
      wp_call hdealloc (ptr_ct1, cap_ct1.toNat, 1, st)
      have hacp_cf : AllocCallPreserved sc sf := by assumption
      have hacp_sf : AllocCallPreserved s sf := allocCallPreserved_trans hacp_sc hacp_cf
      have htr_sf : sf.trace = s0.trace := hacp_cf.2.1.trans htrc
      rw [hspc]
      refine SepWP.mono
        (post := fun sm Pm =>
          VmPreserved sf sm ∧
          (Pm ⊢
            (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
             ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
             ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
             ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
            ct1AcknowledgedScratchCells s0.sp
              a0 a1 a2 a3 a4 a5 v0 v1 v2 v3 v4 v5 v6 v7 v8
              hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
            A.pool lim (M.stepEvents (rustDeallocEvents cap_ct1.toNat 1) st) sf ∗
            stackAt (s0.sp - 1520#64) allocHookStack ∗ Rest) ∧
          AllocCallPreserved sf sm ∧
          sm.sp = s0.sp - 1520#64 ∧
          sm.readReg64 .x30 = (blkPl_334).base + 1904#64 ∧
          sm.readReg64 .x0 = s0.sp - 352#64 ∧
          sm.readReg64 .x1 = s0.sp - 1232#64 ∧
          sm.readReg64 .x29 = s0.sp - 96#64 ∧
          sm.readReg64 .x27 = epoch ∧
          sm.readReg64 .x26 = s0.sp - 480#64 ∧
          sm.readReg64 .x22 = ptr_new ∧
          sm.readReg64 .x21 = len_ct1 ∧
          sm.readReg64 .x19 = out ∧
          TraceCalleeSaved sm s0)
        ?_
        (fun sm _Pm _ _ ⟨hvm_m, hPm, hacp_m, hrest⟩ => by
          refine ⟨?_, allocCallPreserved_trans hacp_sf hacp_m, hrest⟩
          rw [A.pool_of_vmPreserved hvm_m]
          exact hPm)
      dsimp only [ct1AcknowledgedScratchCells, BitVec.ofNat_eq_ofNat]
      by_vm_steps (
        wp_steps
        refine align_pre (by sep_ac_rfl) ?_
        wp_done)

/-- Step 5 (`+1904 -> +1544` in Block `334`): pack `hdr`, `es`, `ct1`, `auth`, `epoch`, and
    `receiving_ek.intoPb` into `epilogueStagingCells` and branch to `+1544`, preserving
    `VmPreserved` and `AllocCallPreserved`. -/
theorem ct1Acknowledged_step_1904_to_1544_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (out ptr_new len_ct1 epoch : BitVec 64)
    (a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2 : BitVec 64)
    (d0 d1 d2 d3 d4 : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 : BitVec 64)
    (w8 w16 w24 w32 w40 w48
     w64 w72 w80 w88 w96 w104 w112 w120
     w128 w136 w144 w152 w160 w168 w176 w184
     w192 w200 w208 w216 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_334).base + 1904#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx27 : s.readReg64 .x27 = epoch)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx22 : s.readReg64 .x22 = ptr_new)
    (hx21 : s.readReg64 .x21 = len_ct1)
    (hx19 : s.readReg64 .x19 = out)
    (htrace : TraceCalleeSaved s s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 1544#64) s
      (ct1AcknowledgedScratchCells s0.sp
         a0 a1 a2 a3 a4 a5 v0 v1 v2 v3 v4 v5 v6 v7 v8
         hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
       (((s0.sp - 352#64) ↦₆₄ d0) ∗ ((s0.sp - 344#64) ↦₆₄ d1) ∗
        ((s0.sp - 336#64) ↦₆₄ d2) ∗ ((s0.sp - 328#64) ↦₆₄ d3) ∗
        ((s0.sp - 320#64) ↦₆₄ d4)) ∗
       epilogueStagingCells s0.sp
         w8 w16 w24 w32 w40 w48
         w64 w72 w80 w88 w96 w104 w112 w120
         w128 w136 w144 w152 w160 w168 w176 w184
         w192 w200 w208 w216 ∗
       Rest)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢
          ct1AcknowledgedScratchCells s0.sp
            hdr0 hdr1 hdr2 es0 es1 es2
            ptr_new len_ct1 a0 a1 a2 a3 a4 a5 epoch
            hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
          (((s0.sp - 352#64) ↦₆₄ d0) ∗ ((s0.sp - 344#64) ↦₆₄ d1) ∗
           ((s0.sp - 336#64) ↦₆₄ d2) ∗ ((s0.sp - 328#64) ↦₆₄ d3) ∗
           ((s0.sp - 320#64) ↦₆₄ d4)) ∗
          epilogueStagingCells s0.sp
            hdr0 hdr1 hdr2 es0 es1 es2
            ptr_new len_ct1 a0 a1 a2 a3 a4 a5
            epoch d0 d1 d2 d3 d4 w176 w184
            w192 w200 w208 w216 ∗
          Rest) ∧
        AllocCallPreserved s sm ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = len_ct1 ∧
        sm.readReg64 .x22 = 0x8000000000000009#64 ∧
        TraceCalleeSaved sm s0) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  dsimp only [ct1AcknowledgedScratchCells, epilogueStagingCells, BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps (
    wp_steps
    refine align_pre (by sep_ac_rfl) ?_
    wp_done)

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bPlacedBudget
