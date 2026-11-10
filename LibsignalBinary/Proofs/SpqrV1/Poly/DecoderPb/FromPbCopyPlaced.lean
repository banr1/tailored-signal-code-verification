/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbExit
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbCopy
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbExitPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyDecoder>::from_pb`: Relocatable Success Copy and Deallocation

Relocatable `[LibsignalPlacement]` proof of the `SortedSet<Pt>` header `memcpy`, unrolled 16-slot
`Vec<u8>` deallocation (`+904..+1236`), and success exit (`+876 → s0.lr`) on Block `376`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.DecoderPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Alloc
  (spqrRustAllocSym spqrRustReallocSym spqrRustNoAllocShimSym
   spqrHandleErrorSym spqrMemcpySym spqrMemmoveSym)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  truncate8_truncate32_zeroExtend64 fromPb_bv384_toNat
attribute [local simp] truncate8_truncate32_zeroExtend64 fromPb_bv384_toNat

local macro "dealloc_u8_slot_step " ptsPtr:term:max off0:term:max off8:term:max off16:term:max off24:term:max k:term:max k24:term:max c:term:max hsp:ident : tactic =>
  `(tactic| (
    refine SepWP.dealloc_u8_list_cons_step $ptsPtr $off0 $off8 $off16 $off24 $k $k24
      rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) $c _ _ ?_
    intro cap ptr; dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp]
    · wp_steps; wp_done
    · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [$hsp:ident]; ac_rfl) ?_; wp_done))

theorem fromPb_success_dealloc_first8_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A))
    (s0 : State) (fsp out pbA ptsPtr d384 ptsNeeded64 : BitVec 64)
    (b392 isComplete8 : BitVec 8)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (c0 c1 c2 c3 c4 c5 c6 c7 : List (BitVec 8)) (rest : List (List (BitVec 8)))
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 904#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = ptsNeeded64)
    (hx20 : s.readReg64 .x20 = isComplete8.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = ptsPtr)
    (hx22 : s.readReg64 .x22 = out)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      ((blkPl_376).base + 1076#64)
      s
      (arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr
        (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
        (((out + 384#64) ↦₆₄ d384) ∗ ((out + 392#64) ↦₈ b392) ∗
          ((fsp + 16#64) ↦₆₄ pbA) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame))
      (fun sm Pm =>
        (Pm ⊢ arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 192#64) rest ∗
          (memRegion ptsPtr 192 ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
            ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame))) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) := by
  simp only [rustDeallocSpec, spqrRustDeallocSym] at hdealloc
  dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, BitVec.ofNat_eq_ofNat] at hdealloc hpc hx19 hx20 hx21 hx22 ⊢
  refine DropGlueFacts.seq_clean (mid := (blkPl_376).base + 932#64) (P_mid :=
    arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 24#64)
      (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
      (memRegion ptsPtr 24 ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
        ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
  · have hpre0 :
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr
          (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
          (((out + 384#64) ↦₆₄ d384) ∗ ((out + 392#64) ↦₈ b392) ∗
            ((fsp + 16#64) ↦₆₄ pbA) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) =
        vecU8 A ptsPtr c0 ∗
          (arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 24#64)
            (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
            (((out + 384#64) ↦₆₄ d384) ∗ ((out + 392#64) ↦₈ b392) ∗
              ((fsp + 16#64) ↦₆₄ pbA) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)) := by
      show (vecU8 A ptsPtr c0 ∗ _) ∗ _ = _
      ac_rfl
    rw [hpre0]
    refine SepWP.weaken_pre (vecU8_frame_entails A ptsPtr c0 _) ?_
    apply ProofLib.SepWP.exists_left; intro cap
    apply ProofLib.SepWP.exists_left; intro ptr
    dsimp only [vecCapPtrDealloc]
    have hpost0 :
        ((ptsPtr ↦₆₄ cap) ∗ ((ptsPtr + 8#64) ↦₆₄ ptr) ∗ memRegion (ptsPtr + 16#64) 8) ∗
          (arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 24#64)
            (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
            (((out + 384#64) ↦₆₄ ptsNeeded64) ∗ ((out + 392#64) ↦₈ isComplete8) ∗
              ((fsp + 16#64) ↦₆₄ pbA) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)) ⊢
        arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 24#64)
          (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
          (memRegion ptsPtr 24 ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
            ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)) := by
      refine Entails.trans (slot0_entails_memRegion_24 ptsPtr cap ptr _) ?_
      exact Entails.of_eq (by ac_rfl)
    refine SepWP.strengthen_entails_const hpost0 ?_
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp]
    · wp_steps; wp_done
    · wp_steps; wp_apply
      refine DropGlueFacts.align_pre (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨hsp_1, hx21_1, hvregs_1, htrace_1⟩
    refine DropGlueFacts.seq_clean (mid := (blkPl_376).base + 952#64) (P_mid :=
      arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 48#64)
        (c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
        (memRegion ptsPtr 48 ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
          ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · dealloc_u8_slot_step ptsPtr 24#64 32#64 40#64 48#64 24 48 c1 hsp_1
    · intro s2 hpc2 hrun2 ⟨hsp_2, hx21_2, hvregs_2, htrace_2⟩
      refine DropGlueFacts.seq_clean (mid := (blkPl_376).base + 976#64) (P_mid :=
        arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 72#64)
          (c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
          (memRegion ptsPtr 72 ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
            ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
        (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
          sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
      · dealloc_u8_slot_step ptsPtr 48#64 56#64 64#64 72#64 48 72 c2 hsp_2
      · intro s3 hpc3 hrun3 ⟨hsp_3, hx19_3, hx21_3, hvregs_3, htrace_3⟩
        refine DropGlueFacts.seq_clean (mid := (blkPl_376).base + 996#64) (P_mid :=
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 96#64)
            (c4 :: c5 :: c6 :: c7 :: rest) ∗
            (memRegion ptsPtr 96 ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
               ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
          (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
            sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
        · dealloc_u8_slot_step ptsPtr 72#64 80#64 88#64 96#64 72 96 c3 hsp_3
        · intro s4 hpc4 hrun4 ⟨hsp_4, hx19_4, hx21_4, hvregs_4, htrace_4⟩
          refine DropGlueFacts.seq_clean (mid := (blkPl_376).base + 1016#64) (P_mid :=
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 120#64)
              (c5 :: c6 :: c7 :: rest) ∗
              (memRegion ptsPtr 120 ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
                ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
            (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
              sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
          · dealloc_u8_slot_step ptsPtr 96#64 104#64 112#64 120#64 96 120 c4 hsp_4
          · intro s5 hpc5 hrun5 ⟨hsp_5, hx19_5, hx21_5, hvregs_5, htrace_5⟩
            refine DropGlueFacts.seq_clean (mid := (blkPl_376).base + 1036#64) (P_mid :=
              arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 144#64)
                (c6 :: c7 :: rest) ∗
                (memRegion ptsPtr 144 ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
                  ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
                  A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
              (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
                sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
            · dealloc_u8_slot_step ptsPtr 120#64 128#64 136#64 144#64 120 144 c5 hsp_5
            · intro s6 hpc6 hrun6 ⟨hsp_6, hx19_6, hx21_6, hvregs_6, htrace_6⟩
              refine DropGlueFacts.seq_clean (mid := (blkPl_376).base + 1056#64) (P_mid :=
                arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 168#64)
                  (c7 :: rest) ∗
                  (memRegion ptsPtr 168 ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
                    ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
                    A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
                (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
                  sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
              · dealloc_u8_slot_step ptsPtr 144#64 152#64 160#64 168#64 144 168 c6 hsp_6
              · intro s7 hpc7 hrun7 ⟨hsp_7, hx19_7, hx21_7, hvregs_7, htrace_7⟩
                dealloc_u8_slot_step ptsPtr 168#64 176#64 184#64 192#64 168 192 c7 hsp_7

theorem fromPb_success_dealloc_last8_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A))
    (s0 : State) (fsp pbA ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (c8 c9 c10 c11 c12 c13 c14 c15 : List (BitVec 8))
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 1076#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = pbA)
    (hx21 : s.readReg64 .x21 = ptsPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      ((blkPl_376).base + 1236#64)
      s
      (arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 192#64)
        (c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: []) ∗
        (memRegion ptsPtr 192 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
      (fun sm Pm =>
        (Pm ⊢ memRegion ptsPtr 384 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) := by
  simp only [rustDeallocSpec, spqrRustDeallocSym] at hdealloc
  dsimp only [Reg.x19, Reg.x21, BitVec.ofNat_eq_ofNat] at hdealloc hpc hx19 hx21 ⊢
  refine DropGlueFacts.seq_clean (mid := (blkPl_376).base + 1096#64) (P_mid :=
    arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 216#64)
      (c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: []) ∗
      (memRegion ptsPtr 216 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
      sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
  · dealloc_u8_slot_step ptsPtr 192#64 200#64 208#64 216#64 192 216 c8 hsp
  · intro s1 hpc1 hrun1 ⟨hsp_1, hx19_1, hx21_1, hvregs_1, htrace_1⟩
    refine DropGlueFacts.seq_clean (mid := (blkPl_376).base + 1116#64) (P_mid :=
      arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 240#64)
        (c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: []) ∗
        (memRegion ptsPtr 240 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
        sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · dealloc_u8_slot_step ptsPtr 216#64 224#64 232#64 240#64 216 240 c9 hsp_1
    · intro s2 hpc2 hrun2 ⟨hsp_2, hx19_2, hx21_2, hvregs_2, htrace_2⟩
      refine DropGlueFacts.seq_clean (mid := (blkPl_376).base + 1136#64) (P_mid :=
        arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 264#64)
          (c11 :: c12 :: c13 :: c14 :: c15 :: []) ∗
          (memRegion ptsPtr 264 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
        (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
          sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
      · dealloc_u8_slot_step ptsPtr 240#64 248#64 256#64 264#64 240 264 c10 hsp_2
      · intro s3 hpc3 hrun3 ⟨hsp_3, hx19_3, hx21_3, hvregs_3, htrace_3⟩
        refine DropGlueFacts.seq_clean (mid := (blkPl_376).base + 1156#64) (P_mid :=
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 288#64)
            (c12 :: c13 :: c14 :: c15 :: []) ∗
            (memRegion ptsPtr 288 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
          (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
            sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
        · dealloc_u8_slot_step ptsPtr 264#64 272#64 280#64 288#64 264 288 c11 hsp_3
        · intro s4 hpc4 hrun4 ⟨hsp_4, hx19_4, hx21_4, hvregs_4, htrace_4⟩
          refine DropGlueFacts.seq_clean (mid := (blkPl_376).base + 1176#64) (P_mid :=
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 312#64)
              (c13 :: c14 :: c15 :: []) ∗
              (memRegion ptsPtr 312 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
            (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
              sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
          · dealloc_u8_slot_step ptsPtr 288#64 296#64 304#64 312#64 288 312 c12 hsp_4
          · intro s5 hpc5 hrun5 ⟨hsp_5, hx19_5, hx21_5, hvregs_5, htrace_5⟩
            refine DropGlueFacts.seq_clean (mid := (blkPl_376).base + 1196#64) (P_mid :=
              arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 336#64)
                (c14 :: c15 :: []) ∗
                (memRegion ptsPtr 336 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
              (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
                sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
            · dealloc_u8_slot_step ptsPtr 312#64 320#64 328#64 336#64 312 336 c13 hsp_5
            · intro s6 hpc6 hrun6 ⟨hsp_6, hx19_6, hx21_6, hvregs_6, htrace_6⟩
              refine DropGlueFacts.seq_clean (mid := (blkPl_376).base + 1216#64) (P_mid :=
                arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 360#64)
                   (c15 :: []) ∗
                  (memRegion ptsPtr 360 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
                (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
                  sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
              · dealloc_u8_slot_step ptsPtr 336#64 344#64 352#64 360#64 336 360 c14 hsp_6
              · intro s7 hpc7 hrun7 ⟨hsp_7, hx19_7, hx21_7, hvregs_7, htrace_7⟩
                have hpost_nil :
                    arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 384#64) [] ∗
                      (memRegion ptsPtr 384 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)) ⊢
                    memRegion ptsPtr 384 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame) := by
                  simp only [arrayAt_nil, emp_sepConj]; exact Entails.refl _
                refine SepWP.strengthen_entails_const hpost_nil ?_
                dealloc_u8_slot_step ptsPtr 360#64 368#64 376#64 384#64 360 384 c15 hsp_7

theorem fromPb_success_exit_876_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpySpec)
    (s0 : State) (fsp out pbA cap_pts ptsPtr w416 w424 w432 : BitVec 64)
    (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (pb : ProtoPolynomialDecoder) (hbss_len : pb.pts.length = 16)
    (outPts : List SortedSetPt) (hout_len : outPts.length = 16)
    (hle : pb.pts.length ≤ cap_pts.toNat)
    (hcap_bound : cap_pts.toNat * 24 < 2 ^ 63)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 876#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = ptsPtr) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (sortedSetPtListOf A (fsp + 32#64) outPts ∗
        memRegion out 400 ∗ memRegion fsp 8 ∗
        ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
        ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
        memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
        ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
        ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        memRegion (fsp - 4128#64) 32 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sf P' =>
        (P' ⊢ resultPolyDecoderFromPbAt A out
            (.ok { ptsNeeded := pb.ptsNeeded.toNat, isComplete := pb.isComplete, pts := outPts }) ∗
          memRegion pbA 40 ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  simp only [sessionMemcpySpec, spqrMemcpySym] at hmemcpy
  rw [sortedSetPtListOf_eq_vecPtListOf]
  have hvecs_len : (outPts.map SortedSetPt.vec).length = 16 := by simp [hout_len]
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecPtListOf_entails_headers_heaps A (outPts.map SortedSetPt.vec) (fsp + 32#64))) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro pins
  rw [sepConj_assoc, sepConj_assoc]
  apply SepWP.pure_elim; intro hpins_len
  have hbs_len : (vecHeadersBytesOf pins (outPts.map SortedSetPt.vec)).length = 384 := by
    rw [length_vecHeadersBytesOf pins _ hpins_len, hvecs_len]
  conv => arg 4; rw [memRegion_400_split_ok out]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro b392
  apply ProofLib.SepWP.exists_left; intro d384
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, hpts_eq⟩ :=
    list_length_16_elim hbss_len
  refine DropGlueFacts.seq_clean
    (mid := (blkPl_376).base + 904#64)
    (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
      (((out + 384#64) ↦₆₄ d384) ∗ ((out + 392#64) ↦₈ b392) ∗
        ((fsp + 16#64) ↦₆₄ pbA) ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (sortedSetPtListOf A out outPts ∗
          memRegion (out + 393#64) 7 ∗
          memRegion fsp 8 ∗ ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          memRegion (fsp + 32#64) 384 ∗
          ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
          memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          memRegion (pbA + 24#64) 16 ∗
          (if cap_pts = 0 then emp
            else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
          memRegion (fsp - 4128#64) 32 ∗ Frame)))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = BitVec.ofNat 64 pb.ptsNeeded.toNat ∧
      sm.readReg64 .x20 = (boolByte pb.isComplete).zeroExtend 64 ∧
      sm.readReg64 .x21 = ptsPtr ∧
      sm.readReg64 .x22 = out ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
  · dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, BitVec.ofNat_eq_ofNat] at hmemcpy hpc hx21 ⊢
    wp_steps
    rw [← hbs_len]
    wp_call hmemcpy (out, fsp + 32#64, vecHeadersBytesOf pins (outPts.map SortedSetPt.vec))
    apply SepWP.done hpc_sf hrun_sf
    have hsp_sf' : sf.sp = fsp := hsp_sf.trans (by simp [wp_norm, arm64_norm, hsp])
    refine ⟨?_, ?_⟩
    · rw [← hsp_sf, hsp_sf', hbs_len, sortedSetPtListOf_eq_vecPtListOf]
      have hdst : (out ↦ₛ vecHeadersBytesOf pins (outPts.map SortedSetPt.vec)) ∗
          vecPtHeapList A pins (outPts.map SortedSetPt.vec) ⊢
          vecPtListOf A out (outPts.map SortedSetPt.vec) :=
        headers_heaps_entails_vecPtListOf A pins (outPts.map SortedSetPt.vec) out hpins_len
      have hsrc : ((fsp + 32#64) ↦ₛ vecHeadersBytesOf pins (outPts.map SortedSetPt.vec)) ⊢
          memRegion (fsp + 32#64) 384 := by
        rw [← hbs_len]
        exact ProofLib.pointsToBytes_entails_memRegion (fsp + 32#64) _
      have hpb16 := pbA_tail_entails_memRegion_16 pbA pb.ptsNeeded pb.polys (boolByte pb.isComplete)
      refine Entails.trans (replace_sub_entails hdst
        (((fsp + 32#64) ↦ₛ vecHeadersBytesOf pins (outPts.map SortedSetPt.vec)) ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
          ((out + 384#64) ↦₆₄ d384) ∗ ((out + 392#64) ↦₈ b392) ∗
          memRegion (out + 393#64) 7 ∗ memRegion fsp 8 ∗
          ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
          memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
          ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
          (if cap_pts = 0 then emp
            else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
          memRegion (fsp - 4128#64) 32 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (by ac_rfl) (by ac_rfl)) ?_
      refine Entails.trans (replace_sub_entails hsrc
        (vecPtListOf A out (outPts.map SortedSetPt.vec) ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
          ((out + 384#64) ↦₆₄ d384) ∗ ((out + 392#64) ↦₈ b392) ∗
          memRegion (out + 393#64) 7 ∗ memRegion fsp 8 ∗
          ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
          memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
          ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
          (if cap_pts = 0 then emp
            else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
          memRegion (fsp - 4128#64) 32 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (by ac_rfl) (by ac_rfl)) ?_
      exact replace_sub_entails hpb16
        (vecPtListOf A out (outPts.map SortedSetPt.vec) ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
          ((out + 384#64) ↦₆₄ d384) ∗ ((out + 392#64) ↦₈ b392) ∗
          memRegion (out + 393#64) 7 ∗ memRegion fsp 8 ∗
          ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          memRegion (fsp + 32#64) 384 ∗
          ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
          memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          (if cap_pts = 0 then emp
            else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
          memRegion (fsp - 4128#64) 32 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (by ac_rfl) (by ac_rfl)
    · rw [← u32_zeroExtend64_eq_ofNat_toNat pb.ptsNeeded]
      simp [wp_norm, arm64_norm, *]
  · intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hvregs1, htr1⟩
    have harr_eq : arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts =
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr
          [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15] := by
      rw [hpts_eq]
    conv => arg 4; rw [harr_eq]
    refine DropGlueFacts.seq_clean
      (fromPb_success_dealloc_first8_placed hdealloc s0 fsp out pbA ptsPtr d384
        (BitVec.ofNat 64 pb.ptsNeeded.toNat) b392 (boolByte pb.isComplete) hfsp_align
        c0 c1 c2 c3 c4 c5 c6 c7 [c8, c9, c10, c11, c12, c13, c14, c15] s1 _
        hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 hx22_1 hvregs1 htr1) ?_
    intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx21_2, hvregs2, htr2⟩
    refine align_pre_wp
      (DropGlueFacts.seq_clean
        (fromPb_success_dealloc_last8_placed hdealloc s0 fsp pbA ptsPtr hfsp_align
          c8 c9 c10 c11 c12 c13 c14 c15 s2
          (((out + 384#64) ↦₆₄ BitVec.ofNat 64 pb.ptsNeeded.toNat) ∗
            ((out + 392#64) ↦₈ boolByte pb.isComplete) ∗
            ((fsp + 16#64) ↦₆₄ pbA) ∗
            (sortedSetPtListOf A out outPts ∗
              memRegion (out + 393#64) 7 ∗
              memRegion fsp 8 ∗ ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
              memRegion (fsp + 32#64) 384 ∗
              ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
              memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
              (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
              memRegion (pbA + 24#64) 16 ∗
              (if cap_pts = 0 then emp
                else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
                  memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
              memRegion (fsp - 4128#64) 32 ∗ Frame))
          hpc2 hrun2 hsp2 hx19_2 hx21_2 hvregs2 htr2) ?_)
      (by ac_rfl)
    intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx21_3, hvregs3, htr3⟩
    have hrejoin_pb := pbA_rejoin_40 pbA cap_pts ptsPtr 16#64
    have hrejoin_buf := DropGlueFacts.memRegion_rejoin_vecBuf A 24 8 cap_pts ptsPtr pb.pts.length hle hcap_bound
    have hfsp448 := fsp_rejoin_448 fsp out pbA ptsPtr w416 w424 w432
    have hok_out :
        sortedSetPtListOf A out outPts ∗
          ((out + 384#64) ↦₆₄ BitVec.ofNat 64 pb.ptsNeeded.toNat) ∗
          ((out + 392#64) ↦₈ boolByte pb.isComplete) ∗
          memRegion (out + 393#64) 7 ⊢
        resultPolyDecoderFromPbAt A out
          (.ok { ptsNeeded := pb.ptsNeeded.toNat, isComplete := pb.isComplete, pts := outPts }) := by
      unfold resultPolyDecoderFromPbAt polyDecoderAt
      dsimp only [polyDecoderPtsNeededOff, polyDecoderIsCompleteOff, polyDecoderPadOff, polyDecoderPadSize]
      have hpure : outPts.length = NUM_POLYS ∧ pb.ptsNeeded.toNat < 2 ^ 64 :=
        ⟨by simp [hout_len, NUM_POLYS, CHUNK_SIZE], by omega⟩
      exact Entails.pure_right hpure (Entails.of_eq (by ac_rfl))
    have hpre_1236 :
        memRegion ptsPtr 384 ∗
          (A.pool ∗ stackAt fsp allocHookStack ∗
            (((out + 384#64) ↦₆₄ BitVec.ofNat 64 pb.ptsNeeded.toNat) ∗
              ((out + 392#64) ↦₈ boolByte pb.isComplete) ∗
              ((fsp + 16#64) ↦₆₄ pbA) ∗
              (sortedSetPtListOf A out outPts ∗
                memRegion (out + 393#64) 7 ∗
                memRegion fsp 8 ∗ ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
                memRegion (fsp + 32#64) 384 ∗
                ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
                memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
                (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
                memRegion (pbA + 24#64) 16 ∗
                (if cap_pts = 0 then emp
                  else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
                    memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
                memRegion (fsp - 4128#64) 32 ∗ Frame))) ⊢
        (pbA ↦₆₄ cap_pts) ∗ vecVecU8BufDealloc A cap_pts ptsPtr ∗
          savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
          A.pool ∗ stackAt fsp dropGluePoly16Stack ∗
          (resultPolyDecoderFromPbAt A out
              (.ok { ptsNeeded := pb.ptsNeeded.toNat, isComplete := pb.isComplete, pts := outPts }) ∗
            ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
            memRegion (pbA + 24#64) 16 ∗ Frame) := by
      have h384 : memRegion ptsPtr 384 = memRegion ptsPtr (pb.pts.length * 24) := by rw [hbss_len]
      rw [h384, fromPb_stackAt_dropGluePoly16_split_bottom fsp]
      unfold vecVecU8BufDealloc
      refine Entails.trans (replace_sub_entails hrejoin_buf
        (A.pool ∗ stackAt fsp allocHookStack ∗ memRegion (fsp - 4128#64) 32 ∗
          ((out + 384#64) ↦₆₄ BitVec.ofNat 64 pb.ptsNeeded.toNat) ∗
          ((out + 392#64) ↦₈ boolByte pb.isComplete) ∗
          sortedSetPtListOf A out outPts ∗
          memRegion (out + 393#64) 7 ∗
          memRegion fsp 8 ∗ ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          memRegion (fsp + 32#64) 384 ∗
          ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
          memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          memRegion (pbA + 24#64) 16 ∗ Frame) (by ac_rfl) (by ac_rfl)) ?_
      refine Entails.trans (replace_sub_entails hfsp448
        ((if (cap_pts == 0#64) = true then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗ memRegion ptsPtr (cap_pts.toNat * 24)) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ memRegion (fsp - 4128#64) 32 ∗
          ((out + 384#64) ↦₆₄ BitVec.ofNat 64 pb.ptsNeeded.toNat) ∗
          ((out + 392#64) ↦₈ boolByte pb.isComplete) ∗
          sortedSetPtListOf A out outPts ∗
          memRegion (out + 393#64) 7 ∗
          savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          memRegion (pbA + 24#64) 16 ∗ Frame) (by ac_rfl) (by ac_rfl)) ?_
      exact replace_sub_entails hok_out
        ((pbA ↦₆₄ cap_pts) ∗
          (if (cap_pts == 0#64) = true then emp
            else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗ memRegion ptsPtr (cap_pts.toNat * 24)) ∗
          savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
          A.pool ∗ memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack ∗
          ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          memRegion (pbA + 24#64) 16 ∗ Frame) (by ac_rfl) (by ac_rfl)
    have hpost_final :
        (pbA ↦₆₄ cap_pts) ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗
          (resultPolyDecoderFromPbAt A out
              (.ok { ptsNeeded := pb.ptsNeeded.toNat, isComplete := pb.isComplete, pts := outPts }) ∗
            ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
            memRegion (pbA + 24#64) 16 ∗ Frame) ⊢
        resultPolyDecoderFromPbAt A out
            (.ok { ptsNeeded := pb.ptsNeeded.toNat, isComplete := pb.isComplete, pts := outPts }) ∗
          memRegion pbA 40 ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame :=
      replace_sub_entails hrejoin_pb
        (resultPolyDecoderFromPbAt A out
            (.ok { ptsNeeded := pb.ptsNeeded.toNat, isComplete := pb.isComplete, pts := outPts }) ∗
          A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame) (by ac_rfl) (by ac_rfl)
    exact SepWP.weaken_pre hpre_1236
      (SepWP.strengthen_entails_const hpost_final
        (fromPb_tail_1236_placed_sepWP hdealloc s0 fsp pbA ptsPtr cap_pts hfsp hsp0_align hfsp_align hcap_bound
          s3 _ hpc3 hrun3 hsp3 hx19_3 hx21_3 hvregs3 htr3))

end CryptoVerification.SpqrV1.Poly.DecoderPb
