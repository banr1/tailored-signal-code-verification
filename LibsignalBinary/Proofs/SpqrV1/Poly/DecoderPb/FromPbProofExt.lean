/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbProof
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbCopy
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDecodes
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbOuterExt
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# 4K-Stack Top-Level Proof for `<PolyDecoder>::from_pb`

Lifts the success deallocation exit (`+876 → s0.lr`), `fromPbDec_ok_ext`, `decoder_from_pb_ok_ext`,
and `fromPbDec_ok_x` to `AllocContracts4K`.
-/

namespace CryptoVerification.SpqrV1.Poly.DecoderPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc (AllocContracts4K)
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L37a

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  truncate8_truncate32_zeroExtend64 fromPb_bv384_toNat bv_add_lit_add_lit
attribute [local arm64_norm, local wp_norm]
  fsp_448_add_8 fsp_448_add_16 fsp_448_add_24 fsp_448_add_32
  fsp_448_add_40 fsp_448_add_48 fsp_448_add_56 fsp_448_add_64
  fsp_448_add_72 fsp_448_add_80 fsp_448_add_88 fsp_448_add_96
  fsp_456_add_8 fsp_464_add_8 fsp_472_add_8 fsp_480_add_8
  fsp_488_add_8 fsp_496_add_8 fsp_504_add_8 fsp_512_add_8
  fsp_520_add_8 fsp_528_add_8

/-! ## Unrolled 16-Slot `Vec<u8>` Deallocation (`+904 -> +1236`) and Success Exit (`+876 -> s0.lr`) -/

local macro "dealloc_u8_slot_step " ptsPtr:term:max off0:term:max off8:term:max off16:term:max off24:term:max k:term:max k24:term:max c:term:max hsp:ident : tactic =>
  `(tactic| (
    refine SepWP.dealloc_u8_list_cons_step $ptsPtr $off0 $off8 $off16 $off24 $k $k24
      rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) $c _ _ ?_
    intro cap ptr; dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp]
    · wp_steps; wp_done
    · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [$hsp:ident]; ac_rfl) ?_; wp_done))

theorem fromPb_success_dealloc_first8_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    (s0 : State) (fsp out pbA ptsPtr d384 ptsNeeded64 : BitVec 64)
    (b392 isComplete8 : BitVec 8)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (c0 c1 c2 c3 c4 c5 c6 c7 : List (BitVec 8)) (rest : List (List (BitVec 8)))
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 904#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = ptsNeeded64)
    (hx20 : s.readReg64 .x20 = isComplete8.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = ptsPtr)
    (hx22 : s.readReg64 .x22 = out)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 1076#64)
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
  have hdealloc := hA.dealloc_ok_at fromPbDecName
    (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<spqr::encoding::polynomial::PolyDecoder>::from_pb"))
    (by rw [decoderFromPb_fnOff]; simp only [arm64_norm])
  simp only [rustDeallocSpec] at hdealloc
  from_pb_fetches_range b (Rust.withPanics ext) 904 172
  dsimp only [tripleRatchetProgAtExt, fromPbDecName,
    Reg.x19, Reg.x20, Reg.x21, Reg.x22, BitVec.ofNat_eq_ofNat] at hdealloc hpc hx19 hx20 hx21 hx22 ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
  examples_hide_fetches
  refine DropGlueFacts.seq_clean (mid := entry + 932#64) (P_mid :=
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
    refine DropGlueFacts.seq_clean (mid := entry + 952#64) (P_mid :=
      arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 48#64)
        (c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
        (memRegion ptsPtr 48 ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
          ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · dealloc_u8_slot_step ptsPtr 24#64 32#64 40#64 48#64 24 48 c1 hsp_1
    · intro s2 hpc2 hrun2 ⟨hsp_2, hx21_2, hvregs_2, htrace_2⟩
      refine DropGlueFacts.seq_clean (mid := entry + 976#64) (P_mid :=
        arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 72#64)
          (c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
          (memRegion ptsPtr 72 ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
            ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
        (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
          sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
      · dealloc_u8_slot_step ptsPtr 48#64 56#64 64#64 72#64 48 72 c2 hsp_2
      · intro s3 hpc3 hrun3 ⟨hsp_3, hx19_3, hx21_3, hvregs_3, htrace_3⟩
        refine DropGlueFacts.seq_clean (mid := entry + 996#64) (P_mid :=
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 96#64)
            (c4 :: c5 :: c6 :: c7 :: rest) ∗
            (memRegion ptsPtr 96 ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
              ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
          (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
            sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
        · dealloc_u8_slot_step ptsPtr 72#64 80#64 88#64 96#64 72 96 c3 hsp_3
        · intro s4 hpc4 hrun4 ⟨hsp_4, hx19_4, hx21_4, hvregs_4, htrace_4⟩
          refine DropGlueFacts.seq_clean (mid := entry + 1016#64) (P_mid :=
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 120#64)
              (c5 :: c6 :: c7 :: rest) ∗
              (memRegion ptsPtr 120 ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
                ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
            (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
              sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
          · dealloc_u8_slot_step ptsPtr 96#64 104#64 112#64 120#64 96 120 c4 hsp_4
          · intro s5 hpc5 hrun5 ⟨hsp_5, hx19_5, hx21_5, hvregs_5, htrace_5⟩
            refine DropGlueFacts.seq_clean (mid := entry + 1036#64) (P_mid :=
              arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 144#64)
                (c6 :: c7 :: rest) ∗
                (memRegion ptsPtr 144 ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
                  ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
                  A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
              (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
                sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
            · dealloc_u8_slot_step ptsPtr 120#64 128#64 136#64 144#64 120 144 c5 hsp_5
            · intro s6 hpc6 hrun6 ⟨hsp_6, hx19_6, hx21_6, hvregs_6, htrace_6⟩
              refine DropGlueFacts.seq_clean (mid := entry + 1056#64) (P_mid :=
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

theorem fromPb_success_dealloc_last8_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    (s0 : State) (fsp pbA ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (c8 c9 c10 c11 c12 c13 c14 c15 : List (BitVec 8))
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 1076#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = pbA)
    (hx21 : s.readReg64 .x21 = ptsPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 1236#64)
      s
      (arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 192#64)
        (c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: []) ∗
        (memRegion ptsPtr 192 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
      (fun sm Pm =>
        (Pm ⊢ memRegion ptsPtr 384 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) := by
  have hdealloc := hA.dealloc_ok_at fromPbDecName
    (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<spqr::encoding::polynomial::PolyDecoder>::from_pb"))
    (by rw [decoderFromPb_fnOff]; simp only [arm64_norm])
  simp only [rustDeallocSpec] at hdealloc
  from_pb_fetches_range b (Rust.withPanics ext) 1076 160
  dsimp only [tripleRatchetProgAtExt, fromPbDecName,
    Reg.x19, Reg.x21, BitVec.ofNat_eq_ofNat] at hdealloc hpc hx19 hx21 ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
  examples_hide_fetches
  refine DropGlueFacts.seq_clean (mid := entry + 1096#64) (P_mid :=
    arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 216#64)
      (c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: []) ∗
      (memRegion ptsPtr 216 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
      sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
  · dealloc_u8_slot_step ptsPtr 192#64 200#64 208#64 216#64 192 216 c8 hsp
  · intro s1 hpc1 hrun1 ⟨hsp_1, hx19_1, hx21_1, hvregs_1, htrace_1⟩
    refine DropGlueFacts.seq_clean (mid := entry + 1116#64) (P_mid :=
      arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 240#64)
        (c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: []) ∗
        (memRegion ptsPtr 240 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
        sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · dealloc_u8_slot_step ptsPtr 216#64 224#64 232#64 240#64 216 240 c9 hsp_1
    · intro s2 hpc2 hrun2 ⟨hsp_2, hx19_2, hx21_2, hvregs_2, htrace_2⟩
      refine DropGlueFacts.seq_clean (mid := entry + 1136#64) (P_mid :=
        arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 264#64)
          (c11 :: c12 :: c13 :: c14 :: c15 :: []) ∗
          (memRegion ptsPtr 264 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
        (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
          sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
      · dealloc_u8_slot_step ptsPtr 240#64 248#64 256#64 264#64 240 264 c10 hsp_2
      · intro s3 hpc3 hrun3 ⟨hsp_3, hx19_3, hx21_3, hvregs_3, htrace_3⟩
        refine DropGlueFacts.seq_clean (mid := entry + 1156#64) (P_mid :=
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 288#64)
            (c12 :: c13 :: c14 :: c15 :: []) ∗
            (memRegion ptsPtr 288 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
          (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
            sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
        · dealloc_u8_slot_step ptsPtr 264#64 272#64 280#64 288#64 264 288 c11 hsp_3
        · intro s4 hpc4 hrun4 ⟨hsp_4, hx19_4, hx21_4, hvregs_4, htrace_4⟩
          refine DropGlueFacts.seq_clean (mid := entry + 1176#64) (P_mid :=
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 312#64)
              (c13 :: c14 :: c15 :: []) ∗
              (memRegion ptsPtr 312 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
            (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
              sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
          · dealloc_u8_slot_step ptsPtr 288#64 296#64 304#64 312#64 288 312 c12 hsp_4
          · intro s5 hpc5 hrun5 ⟨hsp_5, hx19_5, hx21_5, hvregs_5, htrace_5⟩
            refine DropGlueFacts.seq_clean (mid := entry + 1196#64) (P_mid :=
              arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 336#64)
                (c14 :: c15 :: []) ∗
                (memRegion ptsPtr 336 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
              (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
                sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
            · dealloc_u8_slot_step ptsPtr 312#64 320#64 328#64 336#64 312 336 c13 hsp_5
            · intro s6 hpc6 hrun6 ⟨hsp_6, hx19_6, hx21_6, hvregs_6, htrace_6⟩
              refine DropGlueFacts.seq_clean (mid := entry + 1216#64) (P_mid :=
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

theorem fromPb_success_exit_876_sepWP_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    (s0 : State) (fsp out pbA cap_pts ptsPtr w416 w424 w432 : BitVec 64)
    (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (pb : ProtoPolynomialDecoder) (hbss_len : pb.pts.length = 16)
    (outPts : List SortedSetPt) (hout_len : outPts.length = 16)
    (hle : pb.pts.length ≤ cap_pts.toNat)
    (hcap_bound : cap_pts.toNat * 24 < 2 ^ 63)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 876#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = ptsPtr) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
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
  have hmemcpy := hA.session_memcpy_ok_at fromPbDecName
    (num% (ls_off% "memcpy" - ls_off% "<spqr::encoding::polynomial::PolyDecoder>::from_pb"))
    allocHookStack (by decide) (by decide)
    (by rw [decoderFromPb_fnOff]; simp only [arm64_norm])
  simp only [sessionMemcpySpec] at hmemcpy
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
    (mid := (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 904#64)
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
  · from_pb_fetches_range b (Rust.withPanics ext) 876 28
    dsimp only [tripleRatchetProgAtExt, fromPbDecName,
      Reg.x19, Reg.x20, Reg.x21, Reg.x22, BitVec.ofNat_eq_ofNat] at hmemcpy hpc hx21 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
    examples_hide_fetches
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
      (fromPb_success_dealloc_first8_4k hA s0 fsp out pbA ptsPtr d384
        (BitVec.ofNat 64 pb.ptsNeeded.toNat) b392 (boolByte pb.isComplete) hfsp_align
        c0 c1 c2 c3 c4 c5 c6 c7 [c8, c9, c10, c11, c12, c13, c14, c15] s1 _
        hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 hx22_1 hvregs1 htr1) ?_
    intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx21_2, hvregs2, htr2⟩
    refine align_pre_wp
      (DropGlueFacts.seq_clean
        (fromPb_success_dealloc_last8_4k hA s0 fsp pbA ptsPtr hfsp_align
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
        (fromPb_tail_1236_sepWP_dealloc hA.dealloc s0 fsp pbA ptsPtr cap_pts hfsp hsp0_align hfsp_align hcap_bound
          s3 _ hpc3 hrun3 hsp3 hx19_3 hx21_3 hvregs3 htr3))

/-! ## Top-Level 4-KiB Proofs (`fromPbDec_ok_ext_4k`, `decoder_from_pb_ok_ext_4k`, `fromPbDec_ok_x_4k`) -/

theorem fromPbDec_ok_core_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr fromPbDecName)
      (fromPbDecSpecWithStack A fromPbCoreStack) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨out, pbA, pb⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [fromPbDecSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  refine ⟨stackAt s0.sp fromPbCoreStack ∗
      (memRegion out polyDecoderSize ∗ protoPolynomialDecoderAt A pbA pb ∗ A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  dsimp only [fromPbDecSpecWithStack]
  have hpro := fromPb_save_regs_sepWP (b := b) (ext := ext) s0 out pbA hsp0_align
    (memRegion out polyDecoderSize ∗ protoPolynomialDecoderAt A pbA pb ∗ A.pool)
    hpc0 hrun0 hx0 hx1
  refine SepWPp.seq_clean hpro ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx29_1, hvregs1, htr1⟩
  let fsp := s0.sp - 544#64
  have hfsp : HiddenEq fsp (s0.sp - 544#64) := ⟨rfl⟩
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 544#64 hsp0_align
  refine SepWPp.weaken_pre
    (Entails.trans (Entails.of_eq (by ac_rfl))
      (protoPolynomialDecoderAt_expose A pbA pb
        (savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗
          memRegion out polyDecoderSize ∗ A.pool))) ?_
  apply SepWPp.exists_elim; intro cap_pts
  apply SepWPp.exists_elim; intro ptsPtr
  apply SepWPp.pure_elim; rintro ⟨hle, hcap_bound, hlen_bound, _⟩
  by_cases hlen16 : pb.pts.length = 16
  · have hhdr := fromPb_header_ok_sepWP (b := b) (ext := ext) s1 fsp out pbA
      ((pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
        ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗
        memRegion out polyDecoderSize ∗ A.pool)
      hpc1 hrun1 hsp1 hx0_1 hx1_1 hx29_1
    refine SepWPp.weaken_pre (by rw [hlen16]; exact Entails.of_eq (by ac_rfl))
      (SepWPp.seq_clean hhdr ?_)
    intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx20_2, hx24_2, hx29_2, hvregs2, htr2⟩
    conv => arg 4; rw [memRegion_448_split fsp, fromPb_stackAt_dropGluePoly16_split_bottom fsp]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPp.exists_elim; intro v432
    apply SepWPp.exists_elim; intro v424
    apply SepWPp.exists_elim; intro v416
    apply SepWPp.exists_elim; intro v24
    apply SepWPp.exists_elim; intro v16
    apply SepWPp.exists_elim; intro v8
    have hinit := fromPb_init_empty_headers_sepWP (b := b) (ext := ext)
      s2 fsp out pbA ptsPtr v8 v16 v24 hfsp_align
      (memRegion fsp 8 ∗
        ((fsp + 416#64) ↦₆₄ v416) ∗ ((fsp + 424#64) ↦₆₄ v424) ∗ ((fsp + 432#64) ↦₆₄ v432) ∗
        memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
        ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
        ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack ∗
        memRegion out polyDecoderSize ∗ A.pool)
      hpc2 hrun2 hsp2 hx0_2 hx20_2 hx24_2 hx29_2
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWPp.seq_clean hinit ?_)
    intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx21_3, hx24_3, hx25_3, hx29_3, hvregs3, htr3⟩
    have hpts_ne : pb.pts ≠ [] := by intro h; simp [h] at hlen16
    refine SepWPp.weaken_pre
      (by
        dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat]
        rw [BitVec.add_zero, BitVec.add_zero, hlen16]
        exact Entails.of_eq (by ac_rfl))
      (fromPb_outer_loop_wpp_4k hA s0 fsp ptsPtr hfsp_align pb.pts hpts_ne 0
        (by omega) v416 v424 v432 s3
        (((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
          memRegion fsp 8 ∗ memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
          ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
          (if cap_pts = 0 then emp
            else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
          memRegion (fsp - 4128#64) 32 ∗ memRegion out polyDecoderSize)
        hpc3 hrun3 hsp3 hx19_3 hx21_3 hx24_3 hx25_3 hx29_3
        (by rw [htr3, htr2, htr1]) (by rw [hvregs3, hvregs2, hvregs1])
        (fun sm w416 w424 w432 hall hpcm hrunm hspm hx21m _ _ htrm hvregsm => ?_)
        (fun sm sets_err w416 w424 w432 hex hsets_len hpcm hrunm hspm hx21m hx24m hx29m htrm hvregsm => ?_))
    · rw [fromPbDecResult_eq_ok_of_all_mod4 pb hlen16 hall]
      have hout_len : (pb.pts.map fun bs => pushChunks4Total bs { vec := [] }).length = 16 := by
        simp [hlen16]
      have hok := fromPb_success_exit_876_sepWP_4k hA s0 fsp out pbA cap_pts ptsPtr w416 w424 w432
        hfsp hsp0_align hfsp_align pb hlen16
        (pb.pts.map fun bs => pushChunks4Total bs { vec := [] }) hout_len hle hcap_bound
        sm emp hpcm hrunm hspm hx21m hvregsm htrm
      refine SepWPp.weaken_pre ?_
        (sepWPp_of_exit_core s0 sm out pbA _ _ R hok)
      dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, polyDecoderSize]
      rw [BitVec.add_zero, BitVec.add_zero]
      exact Entails.of_eq (by ac_rfl)
    · rw [fromPbDecResult_eq_err_of_exists_mod4 pb hlen16 hex]
      have hsets_len16 : sets_err.length = 16 := hsets_len.trans hlen16
      have herr := fromPb_error_exit_740_sepWP_dealloc hA.dealloc s0 fsp out pbA cap_pts ptsPtr w416 w424 w432
        hfsp hsp0_align hfsp_align sets_err hsets_len16 pb.pts hlen16 hle hcap_bound
        sm emp hpcm hrunm hspm hx21m hx24m hx29m hvregsm htrm
      refine SepWPp.weaken_pre ?_
        (sepWPp_of_exit_core s0 sm out pbA (.error .serializationInvalid) _ R herr)
      dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, polyDecoderSize]
      rw [BitVec.add_zero, BitVec.add_zero]
      have hpb16 := pbA_tail_entails_memRegion_16 pbA pb.ptsNeeded pb.polys (boolByte pb.isComplete)
      exact replace_sub_entails hpb16
        (memRegion out 400 ∗ memRegion fsp 8 ∗
          ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          sortedSetPtListOf A (fsp + 32#64) sets_err ∗
          ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
          memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
          (if cap_pts = 0 then emp
            else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
          memRegion (fsp - 4128#64) 32 ∗ A.pool ∗ stackAt fsp allocHookStack)
        (by ac_rfl) (by ac_rfl)
  · rw [fromPbDecResult_eq_err_of_len_ne_16 pb hlen16]
    have hnPts : pb.pts.length < 2 ^ 64 := by omega
    have hhdr := fromPb_header_err_sepWP (b := b) (ext := ext) s1 fsp out pbA
      pb.pts.length hnPts hlen16
      ((pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
        ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗
        memRegion out polyDecoderSize ∗ A.pool)
      hpc1 hrun1 hsp1 hx0_1 hx1_1 hx29_1
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWPp.seq_clean hhdr ?_)
    intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx20_2, hx24_2, _, hvregs2, htr2⟩
    have herr := fromPb_error_exit_712_sepWP_dealloc hA.dealloc s0 fsp out pbA cap_pts ptsPtr
      hfsp hsp0_align hfsp_align pb.pts hle hcap_bound hlen_bound
      s2 emp hpc2 hrun2 hsp2 hx0_2 hx20_2 hx24_2 (by rw [hvregs2, hvregs1]) (by rw [htr2, htr1])
    refine SepWPp.weaken_pre ?_
      (sepWPp_of_exit_core s0 s2 out pbA (.error .serializationInvalid) _ R herr)
    dsimp only [polyDecoderSize]
    have hpb16 := pbA_tail_entails_memRegion_16 pbA pb.ptsNeeded pb.polys (boolByte pb.isComplete)
    exact replace_sub_entails hpb16
      (memRegion out 400 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack)
      (by ac_rfl) (by ac_rfl)

theorem fromPbDec_ok_ext_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    FromPbDecOkExt b A ext :=
  fromPbDecSpecWithStack_mono (by decide) (by decide) (fromPbDec_ok_core_4k hA)

theorem fromPbDec_ok_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    FromPbDecOkExt b A ext :=
  fromPbDec_ok_ext_4k hA

/-- `<spqr::encoding::polynomial::PolyDecoder>::from_pb` at the `1056 + allocHookStack`
stack budget (`States.FromPb.decoderFromPbStack`) from `AllocContracts4K`. -/
theorem fromPbDec_ok_stack1056_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr fromPbDecName)
      (fromPbDecSpecWithStack A (1056 + allocHookStack)) :=
  fromPbDecSpecWithStack_mono (by decide) (by decide) (fromPbDec_ok_core_4k hA)

theorem decoder_from_pb_ok_ext_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    States.FromPb.DecoderFromPbOkExt b A ext :=
  decoderFromPbSpec_of_fromPbDecSpecWithStack (fromPbDec_ok_stack1056_4k hA)

theorem decoderFromPb_ok_ext_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    States.FromPb.DecoderFromPbOkExt b A ext :=
  decoder_from_pb_ok_ext_4k hA

theorem fromPbDec_ok_x_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext) :
    FromPbDecOkX img A ext :=
  subroutine_ok_inImage_of_subroutine_ok img
    (fromPbDecSpecWithStack_mono (by decide) (by decide) (fromPbDec_ok_core_4k hA))

theorem decoder_from_pb_ok_x_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext) :
    FromPbDecOkX img A ext :=
  fromPbDec_ok_x_4k hA

end CryptoVerification.SpqrV1.Poly.DecoderPb
