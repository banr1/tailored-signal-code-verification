/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `send_ct2_encoder`: Relocatable Continuation Proofs (Block `382`)

Relocatable `[LibsignalPlacement]` continuations (`send_ct2_encoder_finish_placed_budget`,
`send_ct2_encoder_mac_placed_budget`) and single-envelope Block `382` contracts
`send_ct2_encoder_placed_{cl_ext,ok_x}{,_ofEnv}`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux2

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement blkLib_eq_382 blkPC_382 blkPl_382
  lsProg_382 ls_subroutine_ok_of_block lsmpl lsρ
  subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.LibsignalSpqrV1 (Bytes PolyEncoder spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (send_ct2_encoder)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.SpqrV1.Alloc (
  spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
  spqr_hook_ok_of_mem
)
open CryptoVerification.SpqrV1.Drop (vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly (polyEncoderAt)
open CryptoVerification.SpqrV1.Poly.EncodeBytes (encodeBytesResult encodeBytesStackX)
open CryptoVerification.SpqrV1.States.Leaves (
  Relocatable SendCt2EncoderGhost bv_sub_sub encodeBytesResult_of_expectEncodeBytes_ok
  fold_sendCt2SavedCells of_sepWP_lscl polyEncoderAt_split_tag
  sendCt2EncoderStack sendCt2SavedCells slice_and_tail_entails_vecCapPtrDealloc
  sp_sub_496_add_8 sp_sub_504_add_16 sp_sub_504_add_8
  sp_sub_512_add_16 sp_sub_512_add_24 sp_sub_512_add_32 sp_sub_512_add_432 sp_sub_512_add_8
  sp_sub_80_add_16 sp_sub_80_add_24 sp_sub_80_add_32 sp_sub_80_add_40 sp_sub_80_add_48
  sp_sub_80_add_56 sp_sub_80_add_64 sp_sub_80_add_72 sp_sub_80_add_80 sp_sub_80_sub_432
  stackAt_512_recompose stackAt_encodeBytesX_from_allocHook stackAt_encodeBytesX_from_doReserve
  stackAt_encodeBytesX_to_allocHook stackAt_encodeBytesX_to_doReserve
  stackAt_sendCt2Encoder_from_allocHook stackAt_sendCt2Encoder_split
  stackAt_sendCt2Encoder_to_allocHook subroutine_ok_withLsCodeLoaded_of_left vecU8Tail
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
  rustAllocEvents rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
  rustDeallocEvents subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget (
  doReserveRawSpec do_reserve_7_raw_placed_ok
)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget (
  encodeBytesAllocEvents encodeBytesSpec encodeBytesSpecX
)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.ProofBudget (encode_bytes_placed_ok_ext)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget (
  SendCt2EncoderEnv SendCt2EncoderPlacedOkX sendCt2EncoderSpecOfEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux (
  SendCt2EncoderExactEnv call_doReserve7Raw_cl_budget call_encodeBytesX_cl_budget
  call_memcpy_bytes_budget call_memcpy_relocate_cs_budget call_noAllocShim_budget
  call_rustAllocNoOom_budget call_rustDealloc_budget doReserveEvents_eq_sendCt2MacEvs
  encodeBytesSpecX_cl_of_encodeBytesSpec_cl fitsEvents_sendCt2EncoderEvents_split
  hookSat_sessionMemcpyBudget_of_region hookSat_sessionShimBudget_of_noAllocShim
  sendCt2Cap1 sendCt2Cap2 sendCt2EncoderEvents sendCt2EncoderEvents_in_sendCt2EncoderEnv
  sendCt2FreeEvs sendCt2InitEvs sendCt2MacEvs stepEvents_sendCt2EncoderEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [-arm64_norm]
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_sub_496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_add_neg496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.esp_add_496_sub_496
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  sp_sub_80_sub_432 sp_sub_512_add_432
  sp_sub_512_add_8 sp_sub_512_add_16 sp_sub_512_add_24 sp_sub_512_add_32
  sp_sub_504_add_8 sp_sub_504_add_16 sp_sub_496_add_8
  sp_sub_80_add_16 sp_sub_80_add_24 sp_sub_80_add_32
  sp_sub_80_add_40 sp_sub_80_add_48 sp_sub_80_add_56 sp_sub_80_add_64
  sp_sub_80_add_72 sp_sub_80_add_80

@[local arm64_norm, local wp_norm] private theorem sp_sub_80_add_8_loc (sp : BitVec 64) :
    (sp - 80#64) + 8#64 = sp - 72#64 := by bv_omega

/-! ## 1. Exit Postcondition Closer & Encoder Continuation (`+100`) -/

theorem finish_post_close
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {s0 sf : State} {P R : SepProp}
    (x : SendCt2EncoderGhost) (st0 st_f : M.σ)
    (Env : SendCt2EncoderGhost → List AllocEvent → Prop)
    (hEnv : Env x (sendCt2EncoderEvents x.ct2 x.mac))
    (hst : st_f = M.stepEvents (sendCt2EncoderEvents x.ct2 x.mac) st0)
    (hpc : sf.pc = s0.readReg64 Reg.lr)
    (hrun : sf.status = .Running)
    (hsp : sf.sp = s0.sp)
    (hcs : CalleeSavedPreserved s0 sf)
    (htr : sf.trace = s0.trace)
    (hP : P =
      polyEncoderAt A.repAlloc x.outA x.outEnc ∗
      (x.ct2Ptr ↦ₛ x.ct2) ∗
      (x.macPtr ↦ₛ x.mac) ∗
      A.pool lim st_f sf ∗
      stackAt s0.sp sendCt2EncoderStack) :
    SepWP prog (s0.readReg64 Reg.lr) sf P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (∃∗ evs : List AllocEvent,
              ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
              polyEncoderAt A.repAlloc x.outA x.outEnc ∗
              (x.ct2Ptr ↦ₛ x.ct2) ∗
              (x.macPtr ↦ₛ x.mac) ∗
              A.pool lim (M.stepEvents evs st0) sf ∗
              stackAt s0.sp sendCt2EncoderStack) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  refine SepWP.done hpc hrun ⟨?_, hsp, hcs⟩
  intro hm
  rw [hP, hst] at hm
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨sendCt2EncoderEvents x.ct2 x.mac, ?_⟩
  simp only [sepConj_assoc] at hm ⊢
  rw [satisfies_pure_sepConj]
  exact ⟨⟨htr, hEnv⟩, hm⟩

theorem send_ct2_encoder_finish_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (henc_call : subroutine_ok ((blkPC_382).rebase (blkPl_382).base (Rust.withPanics ext))
      (lsmpl.base 417) (withLsCodeLoaded lsmpl (encodeBytesSpecX A lim)))
    (hmemcpy : subroutine_ok ((blkPC_382).rebase (blkPl_382).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (hdealloc : subroutine_ok ((blkPC_382).rebase (blkPl_382).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (outEnc : PolyEncoder)
    (cap ptr w24 d56 : BitVec 64) (st0 st2 : M.σ)
    (Env : SendCt2EncoderGhost → List AllocEvent → Prop)
    (hEnv : Env ⟨outA, ct2Ptr, ct2, macPtr, mac, outEnc⟩ (sendCt2EncoderEvents ct2 mac))
    (henc_res : encodeBytesResult (ct2 ++ mac) = .ok outEnc)
    (hlen_le : (ct2 ++ mac).length ≤ 1048576)
    (hcap_le : (ct2 ++ mac).length ≤ cap.toNat)
    (hcap_lt : cap.toNat < 2 ^ 63)
    (hfit_enc : FitsEvents M lim st2 (encodeBytesAllocEvents (ct2.length + mac.length)))
    (hst_eq :
      M.stepEvents (sendCt2FreeEvs cap.toNat)
        (M.stepEvents (encodeBytesAllocEvents (ct2.length + mac.length)) st2) =
      M.stepEvents (sendCt2EncoderEvents ct2 mac) st0)
    {s0 s : State} {P R : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : ((s0.sp - 512#64) &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_382).base + 100#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 512#64)
    (hx19 : s.readReg64 .x19 = outA)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 mac.length)
    (hx21 : s.readReg64 .x21 = ptr)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 ct2.length)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (
      memRegion outA 400 ∗
       (ct2Ptr ↦ₛ ct2) ∗
       (macPtr ↦ₛ mac) ∗
       (ptr ↦ₛ (ct2 ++ mac)) ∗
       vecU8Tail A.repAlloc cap ptr (ct2 ++ mac) ∗
       ((s0.sp - 504#64) ↦₆₄ cap) ∗
       ((s0.sp - 496#64) ↦₆₄ ptr) ∗
       ((s0.sp - 488#64) ↦₆₄ w24) ∗
       memRegion (s0.sp - 512#64) 8 ∗
       memRegion (s0.sp - 480#64) 400 ∗
       sendCt2SavedCells s0 d56 ∗
       A.pool lim st2 s ∗
       stackAt (s0.sp - 512#64) encodeBytesStackX) ∗ emp)
    (hlr_ls : LsRetAddr624 (s0.readReg64 Reg.lr) := by
      first | assumption | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWPp ((blkPC_382).rebase (blkPl_382).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (∃∗ evs : List AllocEvent,
              ⌜sf.trace = s0.trace ∧ Env ⟨outA, ct2Ptr, ct2, macPtr, mac, outEnc⟩ evs⌝ ∗
              polyEncoderAt A.repAlloc outA outEnc ∗
              (ct2Ptr ↦ₛ ct2) ∗
              (macPtr ↦ₛ mac) ∗
              A.pool lim (M.stepEvents evs st0) sf ∗
              stackAt s0.sp sendCt2EncoderStack) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R)) := by
  rw [hP, sepConj_emp]
  have hadd_len :
      BitVec.ofNat 64 ct2.length + BitVec.ofNat 64 mac.length =
        BitVec.ofNat 64 (ct2 ++ mac).length := by
    rw [List.length_append, BitVec.ofNat_add]
  have hlen_lt64 : (ct2 ++ mac).length < 2 ^ 64 := by omega
  have hfit_enc' : FitsEvents M lim st2 (encodeBytesAllocEvents (ct2 ++ mac).length) := by
    rwa [List.length_append]
  apply of_sepWP_lscl hcl (mid := lsmpl.base 417)
  wp_steps_sync_pool (lsmpl.base 417)
  refine call_encodeBytesX_cl_budget henc_call
    (s0.sp - 480#64) ptr (ct2 ++ mac) outEnc st2 henc_res hlen_lt64 hfit_enc'
    (ret_pc := (blkPl_382).base + 120#64) (sp_call := s0.sp - 512#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htrace])
    (by simp only [Reg.x8, arm64_norm, hsp])
    (by simp only [Reg.x0, arm64_norm, hx21])
    (by simp only [Reg.x1, arm64_norm, hx22, hx20, hadd_len])
    (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx19, hx20, hx21, hx22, hx25, hx26, hx27, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  let st3 := M.stepEvents (encodeBytesAllocEvents (ct2 ++ mac).length) st2
  have hst3_eq : st3 = M.stepEvents (encodeBytesAllocEvents (ct2.length + mac.length)) st2 := by
    dsimp [st3]; rw [List.length_append]
  have hafter_memcpy :
      ∀ (sf2 : State),
        sf2.pc = (blkPl_382).base + 148#64 →
        sf2.status = .Running →
        sf2.sp = s0.sp - 512#64 →
        CalleeSavedPreserved sf1 sf2 →
        sf2.trace = s0.trace →
        SepWP ((blkPC_382).rebase (blkPl_382).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sf2
          ((polyEncoderAt A.repAlloc outA outEnc ∗
            memRegion (s0.sp - 480#64) 400 ∗
            A.pool lim st3 sf2) ∗
           ((ptr ↦ₛ (ct2 ++ mac)) ∗
            stackAt (s0.sp - 512#64) encodeBytesStackX ∗
            ((ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
             vecU8Tail A.repAlloc cap ptr (ct2 ++ mac) ∗
             ((s0.sp - 504#64) ↦₆₄ cap) ∗
             ((s0.sp - 496#64) ↦₆₄ ptr) ∗
             ((s0.sp - 488#64) ↦₆₄ BitVec.ofNat 64 (ct2 ++ mac).length) ∗
             memRegion (s0.sp - 512#64) 8 ∗
             sendCt2SavedCells s0 d56)))
          (fun sf P_f =>
            (sf.mem ⊨ P_f ∗ R →
              sf.mem ⊨
                (∃∗ evs : List AllocEvent,
                  ⌜sf.trace = s0.trace ∧ Env ⟨outA, ct2Ptr, ct2, macPtr, mac, outEnc⟩ evs⌝ ∗
                  polyEncoderAt A.repAlloc outA outEnc ∗
                  (ct2Ptr ↦ₛ ct2) ∗
                  (macPtr ↦ₛ mac) ∗
                  A.pool lim (M.stepEvents evs st0) sf ∗
                  stackAt s0.sp sendCt2EncoderStack) ∗ R) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
    intro sf2 hpc2 hrun2 hsp2 hcs2 htr2
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
    simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx25_1, hx26_1, hx27_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
    refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A.repAlloc cap ptr (ct2 ++ mac) hcap_le hcap_lt)
      (by sep_focus) ?_
    dsimp only [vecCapPtrDealloc, sendCt2SavedCells, RustCliAllocBudget.repAlloc]
    by_cases hcap0 : (cap == 0#64) = true <;>
      simp only [hcap0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · have hcap_eq0 : cap = 0#64 := eq_of_beq hcap0
      subst hcap_eq0
      wp_steps_sync_pool (s0.readReg64 Reg.lr)
      refine SepWP.fold (stackAt_512_recompose s0 0#64 ptr (BitVec.ofNat 64 (ct2 ++ mac).length) d56)
        (by dsimp only [sendCt2SavedCells]; sep_focus) ?_
      have hst_f : st3 = M.stepEvents (sendCt2EncoderEvents ct2 mac) st0 := by
        rw [← hst_eq, ← hst3_eq]; rfl
      refine finish_post_close ⟨outA, ct2Ptr, ct2, macPtr, mac, outEnc⟩ st0 st3 Env hEnv hst_f
        (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [State.sp, arm64_norm, hsp2, *])
        ⟨by simp only [Reg.x19, arm64_norm, *],
         by simp only [Reg.x20, arm64_norm, *],
         by simp only [Reg.x21, arm64_norm, *],
         by simp only [Reg.x22, arm64_norm, *],
         by simp only [Reg.x23, arm64_norm, *],
         by simp only [Reg.x24, arm64_norm, *],
         by simp only [Reg.x25, arm64_norm, *],
         by simp only [Reg.x26, arm64_norm, *],
         by simp only [Reg.x27, arm64_norm, *],
         by simp only [Reg.x28, arm64_norm, *],
         by simp only [Reg.fp, arm64_norm, *],
         by simp only [arm64_norm, hvregs_2, *]⟩
        (by simp only [arm64_norm, htr2, *])
        (by ac_rfl)
    · have hcap_ne0 : cap ≠ 0#64 := ne_of_beq_false (Bool.eq_false_iff.mpr hcap0)
      have hcap_pos : 0 < cap.toNat := Nat.pos_of_ne_zero fun h0 =>
        hcap_ne0 (BitVec.eq_of_toNat_eq (by simpa using h0))
      have hcap_ne0_nat : cap.toNat ≠ 0 := Nat.ne_of_gt hcap_pos
      wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      refine SepWP.fold (stackAt_512_recompose s0 cap ptr (BitVec.ofNat 64 (ct2 ++ mac).length) d56)
        (by dsimp only [sendCt2SavedCells]; sep_focus) ?_
      refine SepWP.fold (stackAt_sendCt2Encoder_to_allocHook s0.sp) (by sep_focus) ?_
      refine call_rustDealloc_budget hdealloc ptr cap.toNat 1 st3
        (s0 := s0) (ret_pc := s0.readReg64 Reg.lr) (sp_call := s0.sp)
        (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [State.sp, arm64_norm, hsp2, *]) hsp0_align
        (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, htr2, *])
        (by simp only [Reg.x0, arm64_norm, *])
        (by simp only [Reg.x1, arm64_norm, *])
        (by simp only [Reg.x2, arm64_norm, *])
        (by sep_focus)
        (fun sf3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_)
      rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
      simp only [arm64_norm, *] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3
      refine SepWP.fold (stackAt_sendCt2Encoder_from_allocHook s0.sp) (by sep_focus) ?_
      have hst_f :
          M.stepEvents (rustDeallocEvents cap.toNat 1) st3 =
            M.stepEvents (sendCt2EncoderEvents ct2 mac) st0 := by
        rw [← hst_eq, ← hst3_eq]
        unfold sendCt2FreeEvs
        simp only [hcap_ne0_nat, ↓reduceIte]
      refine finish_post_close ⟨outA, ct2Ptr, ct2, macPtr, mac, outEnc⟩ st0
        (M.stepEvents (rustDeallocEvents cap.toNat 1) st3) Env hEnv hst_f
        hpc3 hrun3 hsp3
        ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
        htr3 (by ac_rfl)
  obtain ⟨tag, htag01, encRest, henc_split⟩ := polyEncoderAt_split_tag A.repAlloc (s0.sp - 480#64) outEnc
  rcases htag01 with rfl | rfl
  · wp_conv_pre => rw [henc_split]
    wp_steps_sync_pool (lsρ "memcpy")
    refine SepWP.fold (Entails.of_eq henc_split.symm) (by sep_focus) ?_
    exact call_memcpy_relocate_cs_budget hmemcpy (s0 := s0)
      (Relocatable.of_polyEncoderAt A.repAlloc outEnc) outA (s0.sp - 480#64) st3
      (ret_pc := (blkPl_382).base + 148#64) (sp_call := s0.sp - 512#64)
      (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
      (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
      (by simp only [Reg.x0, arm64_norm, hx19_1])
      (by simp only [Reg.x1, arm64_norm, hsp1])
      (by simp only [Reg.x2, arm64_norm])
      (by sep_focus)
      hafter_memcpy
  · wp_conv_pre => rw [henc_split]
    wp_steps_sync_pool (lsρ "memcpy")
    refine SepWP.fold (Entails.of_eq henc_split.symm) (by sep_focus) ?_
    exact call_memcpy_relocate_cs_budget hmemcpy (s0 := s0)
      (Relocatable.of_polyEncoderAt A.repAlloc outEnc) outA (s0.sp - 480#64) st3
      (ret_pc := (blkPl_382).base + 148#64) (sp_call := s0.sp - 512#64)
      (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
      (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
      (by simp only [Reg.x0, arm64_norm, hx19_1])
      (by simp only [Reg.x1, arm64_norm, hsp1])
      (by simp only [Reg.x2, arm64_norm])
      (by sep_focus)
      hafter_memcpy

/-! ## 2. MAC Reserve Continuation (`+208`) & Top-Level Block-`382` Contracts -/

theorem send_ct2_encoder_mac_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdr7 : subroutine_ok ((blkPC_382).rebase (blkPl_382).base (Rust.withPanics ext))
      (lsmpl.base 320) (withLsCodeLoaded lsmpl (doReserveRawSpec M A lim)))
    (henc_call : subroutine_ok ((blkPC_382).rebase (blkPl_382).base (Rust.withPanics ext))
      (lsmpl.base 417) (withLsCodeLoaded lsmpl (encodeBytesSpecX A lim)))
    (hmemcpy : subroutine_ok ((blkPC_382).rebase (blkPl_382).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (hdealloc : subroutine_ok ((blkPC_382).rebase (blkPl_382).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (outEnc : PolyEncoder)
    (cap ptr d56 : BitVec 64) (st0 st1 : M.σ)
    (Env : SendCt2EncoderGhost → List AllocEvent → Prop)
    (hEnv : Env ⟨outA, ct2Ptr, ct2, macPtr, mac, outEnc⟩ (sendCt2EncoderEvents ct2 mac))
    (henc_res : encodeBytesResult (ct2 ++ mac) = .ok outEnc)
    (hlen_le : (ct2 ++ mac).length ≤ 1048576)
    (hmac_ne : mac ≠ [])
    (hcap_eq : cap.toNat = ct2.length)
    (hptr_ne : ptr ≠ 0#64)
    (hfit_mac : FitsEvents M lim st1 (sendCt2MacEvs ct2 mac))
    (hfit_enc : FitsEvents M lim (M.stepEvents (sendCt2MacEvs ct2 mac) st1)
      (encodeBytesAllocEvents (ct2.length + mac.length)))
    (hst_eq :
      M.stepEvents (sendCt2FreeEvs (reserveCap cap.toNat ct2.length mac.length))
        (M.stepEvents (encodeBytesAllocEvents (ct2.length + mac.length))
          (M.stepEvents (sendCt2MacEvs ct2 mac) st1)) =
      M.stepEvents (sendCt2EncoderEvents ct2 mac) st0)
    {s0 s : State} {P R : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : ((s0.sp - 512#64) &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_382).base + 208#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 512#64)
    (hx19 : s.readReg64 .x19 = outA)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 mac.length)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 ct2.length)
    (hx23 : s.readReg64 .x23 = macPtr)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (
      memRegion outA 400 ∗
       (ct2Ptr ↦ₛ ct2) ∗
       (macPtr ↦ₛ mac) ∗
       (ptr ↦ₛ ct2) ∗
       vecU8Tail A.repAlloc cap ptr ct2 ∗
       ((s0.sp - 504#64) ↦₆₄ cap) ∗
       ((s0.sp - 496#64) ↦₆₄ ptr) ∗
       ((s0.sp - 488#64) ↦₆₄ BitVec.ofNat 64 ct2.length) ∗
       memRegion (s0.sp - 512#64) 8 ∗
       memRegion (s0.sp - 480#64) 400 ∗
       sendCt2SavedCells s0 d56 ∗
       A.pool lim st1 s ∗
       stackAt (s0.sp - 512#64) encodeBytesStackX) ∗ emp)
    (hlr_ls : LsRetAddr624 (s0.readReg64 Reg.lr) := by
      first | assumption | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWPp ((blkPC_382).rebase (blkPl_382).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (∃∗ evs : List AllocEvent,
              ⌜sf.trace = s0.trace ∧ Env ⟨outA, ct2Ptr, ct2, macPtr, mac, outEnc⟩ evs⌝ ∗
              polyEncoderAt A.repAlloc outA outEnc ∗
              (ct2Ptr ↦ₛ ct2) ∗
              (macPtr ↦ₛ mac) ∗
              A.pool lim (M.stepEvents evs st0) sf ∗
              stackAt s0.sp sendCt2EncoderStack) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R)) := by
  rw [hP, sepConj_emp]
  have hlen_app : (ct2 ++ mac).length = ct2.length + mac.length := List.length_append
  have hct2_lt : ct2.length < 2 ^ 64 := by omega
  have hmac_lt : mac.length < 2 ^ 64 := by omega
  have hct2_toNat : (BitVec.ofNat 64 ct2.length).toNat = ct2.length := Nat.mod_eq_of_lt hct2_lt
  have hmac_toNat : (BitVec.ofNat 64 mac.length).toNat = mac.length := Nat.mod_eq_of_lt hmac_lt
  have h0_imp : cap = 0#64 → ct2 = [] := fun hc0 => by
    subst hc0; exact List.eq_nil_of_length_eq_zero hcap_eq.symm
  let newCap := reserveCap cap.toNat ct2.length mac.length
  have hnew_bound : newCap + 1 ≤ 2 ^ 63 := by dsimp [newCap, reserveCap]; omega
  have hnew_ge : ct2.length + mac.length ≤ newCap := by dsimp [newCap, reserveCap]; omega
  have hnew_pos : 0 < newCap := by dsimp [newCap, reserveCap]; omega
  have hnew_lt63 : newCap < 2 ^ 63 := by omega
  have hnew_toNat : (BitVec.ofNat 64 newCap).toNat = newCap := Nat.mod_eq_of_lt (by omega)
  have hnew_ne0 : BitVec.ofNat 64 newCap ≠ 0#64 := by
    intro h0; have := congrArg BitVec.toNat h0; rw [hnew_toNat] at this
    change newCap = 0 at this; omega
  have hdo_evs : doReserveEvents ⟨s0.sp - 504#64, cap, ptr, ct2, mac.length⟩ = sendCt2MacEvs ct2 mac :=
    doReserveEvents_eq_sendCt2MacEvs (s0.sp - 504#64) cap ptr ct2 mac hmac_ne hcap_eq
  have hfit_do : FitsEvents M lim st1 (doReserveEvents ⟨s0.sp - 504#64, cap, ptr, ct2, mac.length⟩) := by
    rwa [hdo_evs]
  apply of_sepWP_lscl hcl (mid := lsmpl.base 320)
  wp_steps_sync_pool (lsmpl.base 320)
  refine SepWP.fold (stackAt_encodeBytesX_to_doReserve (s0.sp - 512#64)) (by sep_focus) ?_
  refine call_doReserve7Raw_cl_budget hdr7
    (s0.sp - 504#64) cap ptr ct2 mac.length st1
    (by omega) hptr_ne h0_imp hnew_bound hfit_do
    (ret_pc := (blkPl_382).base + 232#64) (next_pc := (blkPl_382).base + 100#64)
    (sp_call := s0.sp - 512#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htrace])
    (by simp only [Reg.x0, arm64_norm, hsp])
    (by simp only [Reg.x1, arm64_norm, hx22, hct2_toNat])
    (by simp only [Reg.x2, arm64_norm, hx20, hmac_toNat])
    (by simp only [Reg.x3, arm64_norm])
    (by simp only [Reg.x4, arm64_norm])
    (by sep_focus)
    (fun sf1 p' hpc1 hrun1 hsp1 hcs1 htr1 hp'_ne => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx19, hx20, hx22, hx23, hx25, hx26, hx27, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  wp_conv_pre => rw [hdo_evs]
  refine SepWP.fold (stackAt_encodeBytesX_from_doReserve (s0.sp - 512#64)) (by sep_focus) ?_
  have hmem_split :
      memRegion (p' + BitVec.ofNat 64 ct2.length) (newCap - ct2.length) ⊢
      memRegion (p' + BitVec.ofNat 64 ct2.length) mac.length ∗
      memRegion (p' + BitVec.ofNat 64 (ct2 ++ mac).length) (newCap - (ct2 ++ mac).length) := by
    rw [ProofLib.memRegion_split'
      (b := p' + BitVec.ofNat 64 ct2.length)
      (n := mac.length)
      (k := newCap - (ct2 ++ mac).length)
      (b' := p' + BitVec.ofNat 64 (ct2 ++ mac).length)
      (by omega)
      (by rw [List.length_append, BitVec.ofNat_add, BitVec.add_assoc])
      (by omega)]
    exact Entails.refl _
  refine SepWP.fold hmem_split (by sep_focus) ?_
  wp_steps_sync_pool (lsρ "memcpy")
  refine call_memcpy_bytes_budget hmemcpy
    (p' + BitVec.ofNat 64 ct2.length) macPtr mac
    (M.stepEvents (sendCt2MacEvs ct2 mac) st1)
    (s0 := s0) (ret_pc := _) (target_pc := (blkPl_382).base + 100#64)
    (sp_call := s0.sp - 512#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp1, *]) hfsp_align
    rfl (by simp only [arm64_norm, htr1, *])
    (by simp only [Reg.x0, arm64_norm, *])
    (by simp only [Reg.x1, arm64_norm, hx23_1, *])
    (by simp only [Reg.x2, arm64_norm, hx20_1, hmac_toNat, *])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
  simp only [Reg.lr, arm64_norm] at hpc2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx20_1, hx22_1, hx23_1, hx25_1, hx26_1, hx27_1, hvregs_1, *] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  wp_steps_sync_pool ((blkPl_382).base + 100#64)
  have hjoin_mac :
      A.live p' newCap 1 ∗
        (p' ↦ₛ ct2) ∗
        ((p' + BitVec.ofNat 64 ct2.length) ↦ₛ mac) ∗
        memRegion (p' + BitVec.ofNat 64 (ct2 ++ mac).length) (newCap - (ct2 ++ mac).length) ⊢
      (p' ↦ₛ (ct2 ++ mac)) ∗ vecU8Tail A.repAlloc (BitVec.ofNat 64 newCap) p' (ct2 ++ mac) := by
    have hcb : (BitVec.ofNat 64 newCap == 0#64) = false := beq_false_of_ne hnew_ne0
    unfold vecU8Tail
    dsimp only [RustCliAllocBudget.repAlloc]
    simp only [hcb, Bool.false_eq_true, ↓reduceIte, hnew_toNat, pointsToBytes_append]
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.fold hjoin_mac (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  intro hcl2
  exact send_ct2_encoder_finish_placed_budget henc_call hmemcpy hdealloc
    outA ct2Ptr macPtr ct2 mac outEnc
    (BitVec.ofNat 64 newCap) p' (BitVec.ofNat 64 ct2.length) d56
    st0 (M.stepEvents (sendCt2MacEvs ct2 mac) st1) Env hEnv
    henc_res hlen_le (by rw [hnew_toNat]; omega) (by rw [hnew_toNat]; omega)
    hfit_enc (by rw [hnew_toNat]; exact hst_eq)
    hcl2 hsp0_align hfsp_align
    (by wp_norm_goal)
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, hsp2, *])
    (by simp only [Reg.x19, arm64_norm, hx19_2, *])
    (by simp only [Reg.x20, arm64_norm, hx20_2, *])
    (by simp only [Reg.x21, arm64_norm, hx21_2, *])
    (by simp only [Reg.x22, arm64_norm, hx22_2, *])
    (by simp only [Reg.x25, arm64_norm, hx25_2, *])
    (by simp only [Reg.x26, arm64_norm, hx26_2, *])
    (by simp only [Reg.x27, arm64_norm, hx27_2, *])
    (by simp only [arm64_norm, htr2, *])
    (by simp only [arm64_norm, hvregs_2, *])
    (by sep_focus)
    hlr_ls

/-- Envelope-parametric relocatable `spqr::v1::chunked::send_ct::send_ct2_encoder` (Block `382`,
    85 instructions) given `withLsCodeLoaded` contracts for `do_reserve_7` (Block `320`) and
    `encode_bytes` (Block `417`). -/
theorem send_ct2_encoder_placed_cl_ext_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {Env : SendCt2EncoderGhost → List AllocEvent → Prop}
    (hEnv : ∀ x, (x.ct2 ++ x.mac).length ≤ 1048576 → Env x (sendCt2EncoderEvents x.ct2 x.mac))
    (hdr7 : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsmpl.base 320) (withLsCodeLoaded lsmpl (doReserveRawSpec M A lim)))
    (henc : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsmpl.base 417) (withLsCodeLoaded lsmpl (encodeBytesSpec A lim)))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc_sat : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_382 (Rust.withPanics ext)) (blkPl_382).base
      (withLsCodeLoaded lsmpl (sendCt2EncoderSpecOfEnv M A lim Env)) := by
  have hshim : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) noAllocShimSpec :=
    spqr_hook_ok_of_mem (sym := spqrRustNoAllocShimSym) hshim_sat
  have halloc : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false) :=
    spqr_hook_ok_of_mem (sym := spqrRustAllocSym) halloc_sat
  have halloc_nooom := subroutine_ok_allocNoOom_of_budget halloc
  have hdealloc : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim) :=
    spqr_hook_ok_of_mem (sym := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") hdealloc_sat
  have hmemcpy : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec :=
    spqr_hook_ok_of_mem (sym := "memcpy") hmemcpy_sat
  have henc_call : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsmpl.base 417) (withLsCodeLoaded lsmpl (encodeBytesSpecX A lim)) :=
    encodeBytesSpecX_cl_of_encodeBytesSpec_cl henc
  apply subroutine_ok_withLsCodeLoaded_of_left
  simp only [lsProg_382] at hdr7 henc_call hshim halloc halloc_nooom hdealloc hmemcpy ⊢
  unfold sendCt2EncoderSpecOfEnv
  conv => arg 3; arg 1; ext x s; simp only [stackAt_sendCt2Encoder_split]
  cells_unfold
  wpp_init x s0
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  rcases x with ⟨⟨outA, ct2Ptr, ct2, macPtr, mac, outEnc⟩, st0⟩
  dsimp only [BitVec.ofNat_eq_ofNat] at *
  obtain ⟨henc_res, hlen_le⟩ := encodeBytesResult_of_expectEncodeBytes_ok
    ‹send_ct2_encoder spqrPolyApi ct2 mac = .ok outEnc›
  have hEnv_x : Env ⟨outA, ct2Ptr, ct2, macPtr, mac, outEnc⟩ (sendCt2EncoderEvents ct2 mac) :=
    hEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, outEnc⟩ hlen_le
  have hFit : FitsEnv M lim st0 (Env ⟨outA, ct2Ptr, ct2, macPtr, mac, outEnc⟩) := by assumption
  have hfit_all : FitsEvents M lim st0 (sendCt2EncoderEvents ct2 mac) := hFit _ hEnv_x
  obtain ⟨hfit_init, hfit_mac, hfit_enc, _⟩ := fitsEvents_sendCt2EncoderEvents_split hfit_all
  have hst_all := (stepEvents_sendCt2EncoderEvents M ct2 mac st0).symm
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := ‹(s0.sp &&& 15#64 == 0#64) = true›
  have hfsp_align : ((s0.sp - 512#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 512#64 hsp0_align (by decide)
  have hlen_app : (ct2 ++ mac).length = ct2.length + mac.length := List.length_append
  by_cases hct2_nil : ct2 = []
  · subst hct2_nil
    have hct2_z : (BitVec.ofNat 64 ([] : Bytes).length == 0#64) = true := rfl
    have henc_nil :
        emp ⊢ ((1#64 : BitVec 64) ↦ₛ ([] : Bytes)) ∗ vecU8Tail A.repAlloc 0#64 1#64 [] := by
      unfold vecU8Tail
      simp [pointsToBytes_nil]
      exact Entails.refl emp
    by_cases hmac_nil : mac = []
    · subst hmac_nil
      have hmac_z : (BitVec.ofNat 64 ([] : Bytes).length == 0#64) = true := rfl
      apply of_sepWP_lscl hcl0 (mid := (blkPl_382).base + 100#64)
      wp_steps_sync_pool ((blkPl_382).base + 100#64)
      refine SepWP.fold (Entails.trans (Entails.of_eq (emp_sepConj _).symm)
        (sepConj_mono_left henc_nil)) (sepConj_emp _).symm ?_
      rw [sepConj_emp]
      refine SepWP.fold (fold_sendCt2SavedCells s0 _) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcl1
      exact send_ct2_encoder_finish_placed_budget henc_call hmemcpy hdealloc
        outA ct2Ptr macPtr [] [] outEnc
        0#64 1#64 0#64 _ st0 st0 Env hEnv_x
        henc_res hlen_le (by decide) (by decide)
        (by simpa [sendCt2InitEvs, sendCt2MacEvs] using hfit_enc)
        (by simpa [sendCt2InitEvs, sendCt2MacEvs, sendCt2Cap2, sendCt2Cap1] using hst_all)
        hcl1 hsp0_align hfsp_align
        (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [State.sp, arm64_norm, *])
        (by simp only [Reg.x19, arm64_norm, *])
        (by simp only [Reg.x20, arm64_norm, *])
        (by simp only [Reg.x21, arm64_norm, *])
        (by simp only [Reg.x22, arm64_norm, *])
        (by simp only [Reg.x25, arm64_norm, *])
        (by simp only [Reg.x26, arm64_norm, *])
        (by simp only [Reg.x27, arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [List.append_nil]; sep_focus)
        (by dsimp only [Reg.lr, Reg.x30] at *; assumption)
    · have hmac_pos : 0 < mac.length := List.length_pos_iff.mpr hmac_nil
      have hmac_ne0 : BitVec.ofNat 64 mac.length ≠ 0#64 := by
        intro h0; have := congrArg BitVec.toNat h0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        change mac.length = 0 at this; omega
      have hmac_z : (BitVec.ofNat 64 mac.length == 0#64) = false := beq_false_of_ne hmac_ne0
      apply of_sepWP_lscl hcl0 (mid := (blkPl_382).base + 208#64)
      wp_steps_sync_pool ((blkPl_382).base + 208#64)
      refine SepWP.fold (Entails.trans (Entails.of_eq (emp_sepConj _).symm)
        (sepConj_mono_left henc_nil)) (sepConj_emp _).symm ?_
      rw [sepConj_emp]
      refine SepWP.fold (fold_sendCt2SavedCells s0 _) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcl1
      exact send_ct2_encoder_mac_placed_budget hdr7 henc_call hmemcpy hdealloc
        outA ct2Ptr macPtr [] mac outEnc
        0#64 1#64 _ st0 st0 Env hEnv_x
        henc_res hlen_le hmac_nil rfl (by decide)
        (by simpa [sendCt2InitEvs] using hfit_mac)
        (by simpa [sendCt2InitEvs] using hfit_enc)
        (by simpa [sendCt2InitEvs, sendCt2Cap2, sendCt2Cap1, hmac_nil] using hst_all)
        hcl1 hsp0_align hfsp_align
        (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [State.sp, arm64_norm, *])
        (by simp only [Reg.x19, arm64_norm, *])
        (by simp only [Reg.x20, arm64_norm, *])
        (by simp only [Reg.x22, arm64_norm, *])
        (by simp only [Reg.x23, arm64_norm, *])
        (by simp only [Reg.x25, arm64_norm, *])
        (by simp only [Reg.x26, arm64_norm, *])
        (by simp only [Reg.x27, arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by sep_focus)
        (by dsimp only [Reg.lr, Reg.x30] at *; assumption)
  · have hct2_pos : 0 < ct2.length := List.length_pos_iff.mpr hct2_nil
    have hct2_toNat : (BitVec.ofNat 64 ct2.length).toNat = ct2.length := Nat.mod_eq_of_lt (by omega)
    have hct2_ne0 : BitVec.ofNat 64 ct2.length ≠ 0#64 := by
      intro h0; have := congrArg BitVec.toNat h0; rw [hct2_toNat] at this
      change ct2.length = 0 at this; omega
    have hct2_z : (BitVec.ofNat 64 ct2.length == 0#64) = false := beq_false_of_ne hct2_ne0
    have hrlay_ct2 : RustLayoutOk ct2.length 1 := ⟨⟨hct2_pos, ⟨0, rfl⟩, by omega⟩, by decide⟩
    have hinit_eq : sendCt2InitEvs ct2 = rustAllocEvents ct2.length 1 := by
      simp [sendCt2InitEvs, hct2_nil]
    have hfit_init' : FitsEvents M lim st0 (rustAllocEvents ct2.length 1) := by
      rwa [← hinit_eq]
    apply of_sepWP_lscl hcl0 (mid := (blkPl_382).base + 68#64)
    wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
    refine call_noAllocShim_budget hshim st0
      (s0 := s0) (ret_pc := _) (target_pc := (blkPl_382).base + 68#64)
      (sp_call := s0.sp - 512#64)
      (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [State.sp, arm64_norm, *]) hfsp_align
      rfl (by simp only [arm64_norm, *])
      (by sep_focus)
      (fun sf0 hpc0 hrun0 hsp0 hcs0 htr0 => ?_)
    simp only [Reg.lr, arm64_norm] at hpc0
    rcases hcs0 with ⟨hx19_0, hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hfp_0, hvregs_0⟩
    simp only [arm64_norm, *] at hx19_0 hx20_0 hx21_0 hx22_0 hx23_0 hx24_0 hx25_0 hx26_0 hx27_0 hx28_0 hfp_0 hvregs_0
    wp_steps_sync_pool (lsρ spqrRustAllocSym)
    refine SepWP.fold (stackAt_encodeBytesX_to_allocHook (s0.sp - 512#64)) (by sep_focus) ?_
    refine call_rustAllocNoOom_budget halloc_nooom ct2.length 1 st0 hrlay_ct2 hfit_init'
      (s0 := s0) (ret_pc := (blkPl_382).base + 68#64) (target_pc := (blkPl_382).base + 68#64)
      (sp_call := s0.sp - 512#64)
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *]) hfsp_align
      (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [Reg.x0, arm64_norm, hct2_toNat, *])
      (by simp only [Reg.x1, arm64_norm, *])
      (by sep_focus)
      (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 hoom => ?_)
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
    simp only [arm64_norm, *] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
    wp_conv_pre => rw [← hinit_eq]
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    intro hcl1
    dsimp only [Reg.x0] at hoom
    have hoom_false : (sf1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hoom
    have hjoin_ct2 :
        A.live (sf1.readReg64 (Reg.gpr 0#5)) ct2.length 1 ∗
          (sf1.readReg64 (Reg.gpr 0#5) ↦ₛ ct2) ⊢
        (sf1.readReg64 (Reg.gpr 0#5) ↦ₛ ct2) ∗
          vecU8Tail A.repAlloc (BitVec.ofNat 64 ct2.length) (sf1.readReg64 (Reg.gpr 0#5)) ct2 := by
      unfold vecU8Tail
      dsimp only [RustCliAllocBudget.repAlloc]
      simp only [hct2_z, Bool.false_eq_true, ↓reduceIte, hct2_toNat, Nat.sub_self,
        ProofLib.memRegion_zero, sepConj_emp]
      exact Entails.of_eq (sepConj_comm _ _)
    let st1 := M.stepEvents (sendCt2InitEvs ct2) st0
    by_cases hmac_nil : mac = []
    · have hmac_z : (BitVec.ofNat 64 mac.length == 0#64) = true := by subst hmac_nil; rfl
      apply of_sepWP_lscl hcl1 (mid := (blkPl_382).base + 100#64)
      refine SepWP.fold (stackAt_encodeBytesX_from_allocHook (s0.sp - 512#64)) (by sep_focus) ?_
      wp_steps_sync_pool (lsρ "memcpy")
      refine call_memcpy_bytes_budget hmemcpy
        (sf1.readReg64 (Reg.gpr 0#5)) ct2Ptr ct2 st1
        (s0 := s0) (ret_pc := _) (target_pc := (blkPl_382).base + 100#64)
        (sp_call := s0.sp - 512#64)
        (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [State.sp, arm64_norm, *]) hfsp_align
        rfl (by simp only [arm64_norm, *])
        (by simp only [Reg.x0, arm64_norm, *])
        (by simp only [Reg.x1, arm64_norm, *])
        (by simp only [Reg.x2, arm64_norm, hct2_toNat, *])
        (by sep_focus)
        (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
      simp only [Reg.lr, arm64_norm] at hpc2
      rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
      simp only [arm64_norm, *] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
      wp_steps_sync_pool ((blkPl_382).base + 100#64)
      subst hmac_nil
      refine SepWP.fold hjoin_ct2 (by sep_focus) ?_
      refine SepWP.fold (fold_sendCt2SavedCells s0 _) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      intro hcl2
      exact send_ct2_encoder_finish_placed_budget henc_call hmemcpy hdealloc
        outA ct2Ptr macPtr ct2 [] outEnc
        (BitVec.ofNat 64 ct2.length) (sf1.readReg64 (Reg.gpr 0#5)) (BitVec.ofNat 64 ct2.length) _
        st0 st1 Env hEnv_x
        henc_res hlen_le (by rw [List.append_nil, hct2_toNat]) (by rw [hct2_toNat]; omega)
        (by simpa [sendCt2MacEvs] using hfit_enc)
        (by simpa [sendCt2MacEvs, sendCt2Cap2, sendCt2Cap1, hct2_nil, hct2_toNat] using hst_all)
        hcl2 hsp0_align hfsp_align
        (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.sp, arm64_norm, *])
        (by simp only [Reg.x19, arm64_norm, *])
        (by simp only [Reg.x20, arm64_norm, *])
        (by simp only [Reg.x21, arm64_norm, *])
        (by simp only [Reg.x22, arm64_norm, *])
        (by simp only [Reg.x25, arm64_norm, *])
        (by simp only [Reg.x26, arm64_norm, *])
        (by simp only [Reg.x27, arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [List.append_nil]; sep_focus)
        (by dsimp only [Reg.lr, Reg.x30] at *; assumption)
    · have hmac_pos : 0 < mac.length := List.length_pos_iff.mpr hmac_nil
      have hmac_ne0 : BitVec.ofNat 64 mac.length ≠ 0#64 := by
        intro h0; have := congrArg BitVec.toNat h0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        change mac.length = 0 at this; omega
      have hmac_z : (BitVec.ofNat 64 mac.length == 0#64) = false := beq_false_of_ne hmac_ne0
      apply of_sepWP_lscl hcl1 (mid := (blkPl_382).base + 208#64)
      refine SepWP.fold (stackAt_encodeBytesX_from_allocHook (s0.sp - 512#64)) (by sep_focus) ?_
      wp_steps_sync_pool (lsρ "memcpy")
      refine call_memcpy_bytes_budget hmemcpy
        (sf1.readReg64 (Reg.gpr 0#5)) ct2Ptr ct2 st1
        (s0 := s0) (ret_pc := _) (target_pc := (blkPl_382).base + 208#64)
        (sp_call := s0.sp - 512#64)
        (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [State.sp, arm64_norm, *]) hfsp_align
        rfl (by simp only [arm64_norm, *])
        (by simp only [Reg.x0, arm64_norm, *])
        (by simp only [Reg.x1, arm64_norm, *])
        (by simp only [Reg.x2, arm64_norm, hct2_toNat, *])
        (by sep_focus)
        (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
      simp only [Reg.lr, arm64_norm] at hpc2
      rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
      simp only [arm64_norm, *] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
      wp_steps_sync_pool ((blkPl_382).base + 208#64)
      refine SepWP.fold hjoin_ct2 (by sep_focus) ?_
      refine SepWP.fold (fold_sendCt2SavedCells s0 _) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      intro hcl2
      exact send_ct2_encoder_mac_placed_budget hdr7 henc_call hmemcpy hdealloc
        outA ct2Ptr macPtr ct2 mac outEnc
        (BitVec.ofNat 64 ct2.length) (sf1.readReg64 (Reg.gpr 0#5)) _
        st0 st1 Env hEnv_x
        henc_res hlen_le hmac_nil hct2_toNat hoom
        hfit_mac hfit_enc
        (by simpa [sendCt2Cap2, sendCt2Cap1, hmac_nil, hct2_nil, hct2_toNat] using hst_all)
        hcl2 hsp0_align hfsp_align
        (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.sp, arm64_norm, *])
        (by simp only [Reg.x19, arm64_norm, *])
        (by simp only [Reg.x20, arm64_norm, *])
        (by simp only [Reg.x22, arm64_norm, *])
        (by simp only [Reg.x23, arm64_norm, *])
        (by simp only [Reg.x25, arm64_norm, *])
        (by simp only [Reg.x26, arm64_norm, *])
        (by simp only [Reg.x27, arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by sep_focus)
        (by dsimp only [Reg.lr, Reg.x30] at *; assumption)

theorem send_ct2_encoder_placed_cl_ext_exact [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdr7 : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsmpl.base 320) (withLsCodeLoaded lsmpl (doReserveRawSpec M A lim)))
    (henc : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsmpl.base 417) (withLsCodeLoaded lsmpl (encodeBytesSpec A lim)))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc_sat : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_382 (Rust.withPanics ext)) (blkPl_382).base
      (withLsCodeLoaded lsmpl (sendCt2EncoderSpecOfEnv M A lim SendCt2EncoderExactEnv)) :=
  send_ct2_encoder_placed_cl_ext_ofEnv (fun _ _ => rfl) hdr7 henc hshim_sat halloc_sat hdealloc_sat hmemcpy_sat

/-- Relocatable `spqr::v1::chunked::send_ct::send_ct2_encoder` (Block `382`, 85 instructions)
    given `withLsCodeLoaded` contracts for `do_reserve_7` (Block `320`) and `encode_bytes` (Block `417`). -/
theorem send_ct2_encoder_placed_cl_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdr7 : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsmpl.base 320) (withLsCodeLoaded lsmpl (doReserveRawSpec M A lim)))
    (henc : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsmpl.base 417) (withLsCodeLoaded lsmpl (encodeBytesSpec A lim)))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc_sat : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec) :
    SendCt2EncoderPlacedOkX M A lim ext :=
  send_ct2_encoder_placed_cl_ext_ofEnv sendCt2EncoderEvents_in_sendCt2EncoderEnv
    hdr7 henc hshim_sat halloc_sat hdealloc_sat hmemcpy_sat

/-- Envelope-parametric closed `[LibsignalPlacement]` contract for
    `spqr::v1::chunked::send_ct::send_ct2_encoder` (Block `382`), discharging both
    `do_reserve_and_handle [local#7]` (Block `320`) and `<PolyEncoder as Encoder>::encode_bytes`
    (Block `417`) from `HookSat` hypotheses. -/
theorem send_ct2_encoder_placed_ok_x_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {Env : SendCt2EncoderGhost → List AllocEvent → Prop}
    (hEnv : ∀ x, (x.ct2 ++ x.mac).length ≤ 1048576 → Env x (sendCt2EncoderEvents x.ct2 x.mac))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_382 (Rust.withPanics ext)) (blkPl_382).base
      (withLsCodeLoaded lsmpl (sendCt2EncoderSpecOfEnv M A lim Env)) :=
  send_ct2_encoder_placed_cl_ext_ofEnv hEnv
    (ls_subroutine_ok_of_block (i := 382) (j := 320)
      (do_reserve_7_raw_placed_ok h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (i := 382) (j := 417)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (encode_bytes_placed_ok_ext
          (hookSat_sessionShimBudget_of_noAllocShim hshim)
          halloc
          (hookSat_sessionMemcpyBudget_of_region hmemcpy))))
    hshim halloc hdealloc hmemcpy

/-- Closed `[LibsignalPlacement]` contract for `spqr::v1::chunked::send_ct::send_ct2_encoder`
    (Block `382`), discharging both `do_reserve_and_handle [local#7]` (Block `320`) and
    `<PolyEncoder as Encoder>::encode_bytes` (Block `417`) from `HookSat` hypotheses. -/
theorem send_ct2_encoder_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec) :
    SendCt2EncoderPlacedOkX M A lim ext :=
  send_ct2_encoder_placed_ok_x_ofEnv sendCt2EncoderEvents_in_sendCt2EncoderEnv
    h_panic hshim halloc hrealloc hdealloc hmemcpy

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux2
