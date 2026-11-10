/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Disproof.Basic
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.FinishGrowFs
public import LibsignalBinary.Proofs.SignalSession.Cli.Specs
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.FinishGrow
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# `do_reserve_and_handle [local#11]` Contracts and Unbounded-Capacity Counterexample

Verifies `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle [local#11]`:
- `reserve11_raw_ok` and `reserve11_raw_fs_ok`: general `(stride, align)` contract `doReserveStrideRawSpecX`
  and its `.keepsFs` strengthening via `finish_grow [local#12]`.
- `reserve1_ok`, `cliDoReserve_ok`, `reserve16Cap_ok` (`16 * cap < 2 ^ 62`), `reserve16Eq_ok`
  (`cap = len`), and `reserve16_ok`.
- `not_subroutine_ok_reserve16Spec`: binary counterexample refuting `reserve16SpecR2` (which omits
  `16 * cap < 2 ^ 62`) at `cap = 2 ^ 58, bs = []`, where `finish_grow` panics on capacity overflow
  without invoking the allocator.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace Reserve11Norm

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

theorem repack_stack_bound (C0 C1 C2 Buf Pool Stack R : SepProp) :
    C0 ∗ C1 ∗ C2 ∗ Buf ∗ Pool ∗ Stack ∗ R =
      Stack ∗ (C0 ∗ (C1 ∗ C2 ∗ Buf ∗ Pool ∗ R)) := by ac_rfl

theorem repack_raw_pre (C0 C1 C2 Buf Pool Extra SubStack R : SepProp) :
    C0 ∗ C1 ∗ C2 ∗ Buf ∗ Pool ∗ (Extra ∗ SubStack) ∗ R =
      C0 ∗ C1 ∗ Buf ∗ Pool ∗ SubStack ∗ (C2 ∗ Extra ∗ R) := by ac_rfl

theorem repack_raw_post (C0' C1' C2 Live' Bs' Tail' Pool Extra SubStack R : SepProp) :
    (C0' ∗ C1' ∗ Live' ∗ Bs' ∗ Tail') ∗ (Pool ∗ SubStack) ∗ (C2 ∗ Extra ∗ R) =
      (C0' ∗ C1' ∗ C2 ∗ Live' ∗ Bs' ∗ Tail') ∗ (Pool ∗ Extra ∗ SubStack) ∗ R := by ac_rfl

theorem repack_anyHeap (F1 F2 R : SepProp) :
    anyHeap ∗ (F1 ∗ F2 ∗ R) = (anyHeap ∗ F1 ∗ F2) ∗ R := by ac_rfl

end Reserve11Norm

open Reserve11Norm

attribute [local wp_norm]
  State.fs_writeReg64 State.fs_writeReg32 State.fs_writeVReg128
  State.fs_advancePC State.fs_setPC State.fs_setPState
  State.fs_setMem State.fs_setStatus State.fs_appendTrace

/-! ## 1. Decodes & arithmetic helpers for `do_reserve_and_handle [local#11]` -/

gen_decodes CryptoVerification.libsignalSessionCode_tree cliReserve11Bin
  [(ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]") →
   (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]" + 136)]

private theorem adds_cs_eq_false {x2 x1 : BitVec 64}
    (h : x2.toNat + x1.toNat < 2 ^ 64) :
    (x2 + x1).ult x2 = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, BitVec.toNat_add, Nat.mod_eq_of_lt h]
  omega

private theorem reserve_new_cap_stride_eq {stride cap x1 x2 : BitVec 64} {len additional : Nat}
    (hx1 : x1.toNat = len) (hx2 : x2.toNat = additional)
    (h : SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional < 2 ^ 63) :
    (if (if (stride == 1#64) = true then 8#64 else 4#64).ult
          (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1) = true then
      if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1
     else if (stride == 1#64) = true then 8#64 else 4#64) =
      BitVec.ofNat 64 (SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional) := by
  have hmin_ge : 4 ≤ SpqrV1.Alloc.reserveMinCap stride.toNat := by
    unfold SpqrV1.Alloc.reserveMinCap; split <;> omega
  have hmax : max (max (len + additional) (2 * cap.toNat)) (SpqrV1.Alloc.reserveMinCap stride.toNat) < 2 ^ 63 := h
  have hadd : (x2 + x1).toNat = len + additional := by
    rw [BitVec.toNat_add, hx2, hx1, Nat.mod_eq_of_lt (by omega)]
    omega
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hm0 : (if (stride == 1#64) = true then 8#64 else 4#64).toNat =
      SpqrV1.Alloc.reserveMinCap stride.toNat := by
    by_cases hs : (stride == 1#64) = true
    · have hs' : stride = 1#64 := beq_iff_eq.mp hs
      subst hs'
      rfl
    · have hs' : stride.toNat ≠ 1 := by
        intro h1
        apply hs
        exact beq_iff_eq.mpr (BitVec.eq_of_toNat_eq h1)
      simp only [hs, Bool.false_eq_true, ite_false, SpqrV1.Alloc.reserveMinCap, hs']
      rfl
  have hm1 : (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1).toNat =
      max (len + additional) (2 * cap.toNat) := by
    by_cases hc : (cap <<< 1).ult (x2 + x1) = true
    · simp only [hc, ite_true, hadd]
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh, hadd] at hc
      omega
    · simp only [hc, Bool.false_eq_true, ite_false, hsh]
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh, hadd] at hc
      omega
  apply BitVec.eq_of_toNat_eq
  dsimp only [SpqrV1.Alloc.reserveCapStride]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  generalize (if (stride == 1#64) = true then 8#64 else 4#64) = m0 at hm0 ⊢
  generalize (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1) = m1 at hm1 ⊢
  by_cases hc2 : m0.ult m1 = true
  · simp only [hc2, ite_true, hm1]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm0, hm1] at hc2
    omega
  · simp only [hc2, Bool.false_eq_true, ite_false, hm0]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm0, hm1] at hc2
    omega

/-! ## 2. General `(stride, align)` raw contract (`reserve11_raw_ok`) -/

/-- General raw `(stride, align)` contract of `do_reserve_and_handle [local#11]` (`reserve11Name`)
at stack budget `doReserveStackX`. -/
def doReserveStrideRawSpecX (A : RustAlloc) : Spec SpqrV1.Alloc.DoReserveStrideCall where
  pre := fun x s =>
    let newCap := SpqrV1.Alloc.reserveCapStride x.stride.toNat x.cap.toNat x.len x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.len ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = x.align ∧
      s.readReg64 .x4 = x.stride ∧
      x.len ≤ x.cap.toNat ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
      x.ptr ≠ 0#64 ∧ 0 < x.stride.toNat ∧ LayoutOk (newCap * x.stride.toNat) x.align.toNat⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    (if x.cap = 0#64 then emp
     else A.live x.ptr (x.cap.toNat * x.stride.toNat) x.align.toNat ∗ (x.ptr ↦ₛ x.bs) ∗
       memRegion (x.ptr + BitVec.ofNat 64 x.bs.length)
         (x.cap.toNat * x.stride.toNat - x.bs.length)) ∗
    A.pool ∗ stackAt s.sp doReserveStackX
  post := fun x s0 sf =>
    let newCap := SpqrV1.Alloc.reserveCapStride x.stride.toNat x.cap.toNat x.len x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % x.align.toNat = 0⌝ ∗
      (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' (newCap * x.stride.toNat) x.align.toNat ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length)
        (newCap * x.stride.toNat - x.bs.length)) ∗
    A.pool ∗ stackAt s0.sp doReserveStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `do_reserve_and_handle [local#11]` satisfies `(doReserveStrideRawSpecX A).inImage img`
for arbitrary `(stride, align)` on `mProg img ext` under `AllocContractsX img A ext`. -/
theorem reserve11_raw_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr reserve11Name)
      ((doReserveStrideRawSpecX A).inImage img) := by
  unfold Spec.inImage mProg
  simp only [doReserveStrideRawSpecX, GrowOne.Helpers.stackAt_cliGrowOne, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff reserve11Name =
      num% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]") :=
    cliDoReserve_fnOff
  have hpanic := panic_at_handle_error_norm_ext (b := img.base) (ext := ext)
    (name := reserve11Name)
    (k := num% (ls_rel%
      "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
      "alloc::raw_vec::handle_error"))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg := FinishGrow.cliFinishGrow_ok_x hA
  have hfg0 := GrowOne.Helpers.finish_grow_zero_cells_ok_x hfg
  have hfg1 := GrowOne.Helpers.finish_grow_ne_cells_ok_x hfg
  rw [Program.fnAddr_rel (name := reserve11Name)
    hfn cliFinishGrow_fnOff
    (k := num% (ls_rel%
      "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
      "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]"))
    (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode cliReserve11Bin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]")) 140
  dsimp only [tripleRatchetProgAtExt] at hpanic hfg0 hfg1 ⊢
  clear hfn hA hfg
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr reserve11Name = fnBase
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs, len, additional, align, stride⟩ := x
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hx1_eq : (s0.readReg64 .x1).toNat = len := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hlen_le_cap : len ≤ cap.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hptr_ne : ptr ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hsz_pos : 0 < SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat := h.1
  have hpow : ∃ k, align.toNat = 2 ^ k := h.2.1
  have hbound :
      SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat + align.toNat ≤ 2 ^ 63 :=
    h.2.2
  have halign_pos : 1 ≤ align.toNat := by
    rcases hpow with ⟨k, hk⟩; rw [hk]; exact Nat.one_le_two_pow
  have hmin_ge : 4 ≤ SpqrV1.Alloc.reserveMinCap stride.toNat := by
    unfold SpqrV1.Alloc.reserveMinCap; split <;> omega
  have hnew_lt63 : SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional < 2 ^ 63 := by
    have : SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * 1 ≤
        SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat :=
      Nat.mul_le_mul_left _ hstr_pos
    omega
  have hmax : max (max (len + additional) (2 * cap.toNat)) (SpqrV1.Alloc.reserveMinCap stride.toNat) < 2 ^ 63 :=
    hnew_lt63
  have hcs := adds_cs_eq_false (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_stride_eq (stride := stride) (cap := cap) hx1_eq hx2_eq hnew_lt63
  let new := BitVec.ofNat 64 (SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional)
  have hnew_toNat : new.toNat = SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by
    rw [hnew_toNat]; dsimp [SpqrV1.Alloc.reserveCapStride]; omega
  have hnew_pos : 0 < new.toNat := by
    rw [hnew_toNat]; dsimp [SpqrV1.Alloc.reserveCapStride]; omega
  have hnew_lay : LayoutOk (new.toNat * stride.toNat) align.toNat := by
    rw [hnew_toNat]; exact h
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * stride.toNat = 0 := Nat.zero_mul stride.toNat
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hnew_eq0 :
        (if (if (stride == 1#64) = true then 8#64 else 4#64).ult
              (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
                s0.readReg64 .x2 + s0.readReg64 .x1
               else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1
           else 0#64
         else if (stride == 1#64) = true then 8#64 else 4#64) = new := hnew_eq
    have hmul_eq : SpqrV1.Alloc.reserveCapStride stride.toNat 0 len additional * stride.toNat =
        new.toNat * stride.toNat := by
      rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.zero_mod, hmul_eq]
    apply SepWPp.of_sepWP (mid := fnBase + bv% (88))
    apply SepWP.seq_inImage
      (mid := fnBase + bv% (ls_rel%
        "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
        "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]"))
      hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    rintro ⟨hF1, hsym1⟩
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, align, stride, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := fnBase + bv% (ls_rel%
          "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
          "alloc::raw_vec::handle_error"))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
  · simp only [hcap0, ite_false, sepConj_assoc]
    have hsub_eq :
        SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat - bs.length =
          new.toNat * stride.toNat - bs.length := by rw [hnew_toNat]
    have hmul_eq :
        SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat =
          new.toNat * stride.toNat := by rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply SepWPp.of_sepWP (mid := fnBase + bv% (88))
    apply SepWP.seq_inImage
      (mid := fnBase + bv% (ls_rel%
        "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
        "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]"))
      hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    rintro ⟨hF1, hsym1⟩
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, align, stride, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := fnBase + bv% (ls_rel%
          "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
          "alloc::raw_vec::handle_error"))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

/-- `do_reserve_and_handle [local#11]` satisfies `(doReserveStrideRawSpecX A).keepsFs.inImage img`
for arbitrary `(stride, align)` on `mProg img ext` under `AllocContractsFs img A ext`. -/
theorem reserve11_raw_fs_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hFs : AllocContractsFs img A ext) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr reserve11Name)
      ((doReserveStrideRawSpecX A).keepsFs.inImage img) := by
  unfold Spec.inImage mProg
  simp only [Spec.keepsFs, doReserveStrideRawSpecX, GrowOne.Helpers.stackAt_cliGrowOne,
    sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff reserve11Name =
      num% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]") :=
    cliDoReserve_fnOff
  have hpanic := panic_at_handle_error_norm_ext (b := img.base) (ext := ext)
    (name := reserve11Name)
    (k := num% (ls_rel%
      "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
      "alloc::raw_vec::handle_error"))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg := cliFinishGrow_okFs hFs
  have hfg0 := finish_grow_zero_cells_fs_ok_x hfg
  have hfg1 := finish_grow_ne_cells_fs_ok_x hfg
  rw [Program.fnAddr_rel (name := reserve11Name)
    hfn cliFinishGrow_fnOff
    (k := num% (ls_rel%
      "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
      "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]"))
    (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode cliReserve11Bin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]")) 140
  dsimp only [tripleRatchetProgAtExt] at hpanic hfg0 hfg1 ⊢
  clear hfn hFs hfg
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr reserve11Name = fnBase
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs, len, additional, align, stride⟩ := x
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hx1_eq : (s0.readReg64 .x1).toNat = len := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hlen_le_cap : len ≤ cap.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hptr_ne : ptr ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hsz_pos : 0 < SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat := h.1
  have hpow : ∃ k, align.toNat = 2 ^ k := h.2.1
  have hbound :
      SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat + align.toNat ≤ 2 ^ 63 :=
    h.2.2
  have halign_pos : 1 ≤ align.toNat := by
    rcases hpow with ⟨k, hk⟩; rw [hk]; exact Nat.one_le_two_pow
  have hmin_ge : 4 ≤ SpqrV1.Alloc.reserveMinCap stride.toNat := by
    unfold SpqrV1.Alloc.reserveMinCap; split <;> omega
  have hnew_lt63 : SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional < 2 ^ 63 := by
    have : SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * 1 ≤
        SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat :=
      Nat.mul_le_mul_left _ hstr_pos
    omega
  have hmax : max (max (len + additional) (2 * cap.toNat)) (SpqrV1.Alloc.reserveMinCap stride.toNat) < 2 ^ 63 :=
    hnew_lt63
  have hcs := adds_cs_eq_false (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_stride_eq (stride := stride) (cap := cap) hx1_eq hx2_eq hnew_lt63
  let new := BitVec.ofNat 64 (SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional)
  have hnew_toNat : new.toNat = SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by
    rw [hnew_toNat]; dsimp [SpqrV1.Alloc.reserveCapStride]; omega
  have hnew_pos : 0 < new.toNat := by
    rw [hnew_toNat]; dsimp [SpqrV1.Alloc.reserveCapStride]; omega
  have hnew_lay : LayoutOk (new.toNat * stride.toNat) align.toNat := by
    rw [hnew_toNat]; exact h
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * stride.toNat = 0 := Nat.zero_mul stride.toNat
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hnew_eq0 :
        (if (if (stride == 1#64) = true then 8#64 else 4#64).ult
              (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
                s0.readReg64 .x2 + s0.readReg64 .x1
               else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1
           else 0#64
         else if (stride == 1#64) = true then 8#64 else 4#64) = new := hnew_eq
    have hmul_eq : SpqrV1.Alloc.reserveCapStride stride.toNat 0 len additional * stride.toNat =
        new.toNat * stride.toNat := by
      rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.zero_mod, hmul_eq]
    apply SepWPp.of_sepWP (mid := fnBase + bv% (88))
    apply SepWP.seq_inImage
      (mid := fnBase + bv% (ls_rel%
        "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
        "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]"))
      hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    rintro ⟨hF1, hsym1⟩
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, align, stride, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := fnBase + bv% (ls_rel%
          "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
          "alloc::raw_vec::handle_error"))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
  · simp only [hcap0, ite_false, sepConj_assoc]
    have hsub_eq :
        SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat - bs.length =
          new.toNat * stride.toNat - bs.length := by rw [hnew_toNat]
    have hmul_eq :
        SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat =
          new.toNat * stride.toNat := by rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply SepWPp.of_sepWP (mid := fnBase + bv% (88))
    apply SepWP.seq_inImage
      (mid := fnBase + bv% (ls_rel%
        "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
        "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]"))
      hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    rintro ⟨hF1, hsym1⟩
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, align, stride, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := fnBase + bv% (ls_rel%
          "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
          "alloc::raw_vec::handle_error"))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

/-! ## 3. `reserve1_keepsFs_ok` (`MainCallees.reserve1`), `reserve1_ok`, and `cliDoReserve_ok` -/

private theorem vecU8At_eq (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, BitVec.ofNat_eq_ofNat]
  ac_rfl

/-- Pure spec refinement from `doReserveStrideRawSpecX` (`stride = 1, align = 1`, stack budget
`doReserveStackX`) to `SpqrV1.Varint.doReserveSpecOf resStack A` for any `resStack ≥ doReserveStackX`
(deriving `resStack ≤ 2 ^ 64` from `s0.mem`). Lifts simultaneously to both `subroutine_ok` and
`Spec.keepsFs`. -/
theorem doReserveStrideRaw_refines_doReserveSpecOf {img : Obj.Image} {A : RustAlloc}
    {resStack : Nat} (hstk : doReserveStackX ≤ resStack) :
    SpecRefines
      ((doReserveStrideRawSpecX A).inImage img)
      ((CryptoVerification.SpqrV1.Varint.doReserveSpecOf resStack A).inImage img) := by
  intro x R s0 hpre
  simp only [Spec.inImage, SpqrV1.Varint.doReserveSpecOf, vecU8At_eq,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, ⟨hlen, hcap63, hptr⟩, hmem⟩
  have hhi : resStack ≤ 2 ^ 64 := by
    have hm := hmem
    rw [stackAt, repack_stack_bound] at hm
    exact GrowOne.Helpers.memRegion_bound_of_pointsTo64 hm
  have hlo : 64 + finishGrowStackX ≤ resStack := by
    have : 64 + finishGrowStackX = doReserveStackX := by decide
    omega
  have hsplit : stackAt s0.sp resStack =
      memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - doReserveStackX) ∗
        stackAt s0.sp doReserveStackX :=
    GrowOne.Helpers.stackAt_split_stk s0.sp hlo hhi
  rw [hsplit, repack_raw_pre] at hmem
  let xs : SpqrV1.Alloc.DoReserveStrideCall :=
    ⟨x.v, x.cap, x.ptr, x.bs, x.bs.length, x.additional, 1#64, 1#64⟩
  have hlay : LayoutOk (reserveCap x.cap.toNat x.bs.length x.additional) 1 :=
    ⟨by dsimp [reserveCap]; omega, ⟨0, rfl⟩, by omega⟩
  let F : SepProp :=
    ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
      memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - doReserveStackX) ∗ R
  have hpre' : s0.mem ⊨ ((doReserveStrideRawSpecX A).inImage img).pre xs s0 ∗ F := by
    simp only [Spec.inImage, doReserveStrideRawSpecX, xs, BitVec.toNat_ofNat, Nat.one_mod,
      SpqrV1.Alloc.reserveCapStride_one, Nat.mul_one, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hlen, hlen, hptr, by decide, hlay⟩, hmem⟩
  refine ⟨xs, F, hpre', ?_, ?_, ?_, ?_⟩
  · intro sf hq
    simp only [Spec.inImage, doReserveStrideRawSpecX, SpqrV1.Varint.doReserveSpecOf, vecU8At_eq,
      xs, BitVec.toNat_ofNat, Nat.one_mod, SpqrV1.Alloc.reserveCapStride_one, Nat.mul_one,
      Nat.mod_one, and_true] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htrace, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨p', hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hp', hpost_mem⟩
    have hlt : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 64 := by
      dsimp [reserveCap] at hbound ⊢; omega
    have hlen_le : x.bs.length ≤ reserveCap x.cap.toNat x.bs.length x.additional := by
      dsimp [reserveCap]; omega
    have hcap63' : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 63 := by omega
    have hcap_ne : BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional) ≠ 0#64 := by
      intro heq
      have ht := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
      change reserveCap x.cap.toNat x.bs.length x.additional = 0 at ht
      dsimp [reserveCap] at ht; omega
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨p', ?_⟩
    simp only [hcap_ne, ite_false, Nat.mod_eq_of_lt hlt, hsplit]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hlen_le, hcap63', hp'⟩, ?_⟩
    rw [← repack_raw_post]
    dsimp only [F] at hpost_mem
    exact hpost_mem
  · intro sf hq
    dsimp only [Spec.inImage, doReserveStrideRawSpecX, SpqrV1.Varint.doReserveSpecOf,
      doReserveSpec, F] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    refine ⟨hq.1, ?_⟩
    rw [repack_anyHeap] at hq
    exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hq.2
  · intro _ _ hq
    exact (allowPanic_not_exited hq).elim
  · intro _ hq
    exact (allowPanic_not_exited hq).elim

/-- `do_reserve_and_handle [local#11]` satisfies
`(SpqrV1.Varint.doReserveSpecOf resStack A).keepsFs.inImage img` for any
`resStack ≥ doReserveStackX` (`resStack ≤ 2 ^ 64` is derived from `s0.mem`). -/
theorem reserve1_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack : Nat}
    (hCF : AllocContractsFs img A ext)
    (hres : doReserveStackX ≤ resStack) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr reserve11Name)
      ((CryptoVerification.SpqrV1.Varint.doReserveSpecOf resStack A).keepsFs.inImage img) :=
  (doReserveStrideRaw_refines_doReserveSpecOf hres).apply_keepsFs_inImage (reserve11_raw_fs_ok hCF)

/-- `do_reserve_and_handle [local#11]` contract matching the `hRes` premise of `Cli.Path`,
`Cli.Decimal`, and `Cli.AddressText`. -/
theorem cliDoReserve_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack : Nat}
    (hA : AllocContractsX img A ext)
    (hstk : doReserveStackX ≤ resStack) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDoReserveName)
      ((SpqrV1.Varint.doReserveSpecOf resStack A).inImage img) :=
  (doReserveStrideRaw_refines_doReserveSpecOf hstk).apply_ok (reserve11_raw_ok hA)

/-! ## 4. `reserve16_ok` (`MainCallees.reserve16`) and sharp `.pre`-amended twins (`reserve16Cap_ok` / `reserve16Eq_ok`) -/

private theorem vec16At_eq (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vec16At A v cap ptr bs =
      ⌜bs.length % 16 = 0 ∧ bs.length ≤ 16 * cap.toNat ∧ 16 * cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs.length / 16)) ∗
      (if cap = 0#64 then emp
       else A.live ptr (16 * cap.toNat) 8 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (16 * cap.toNat - bs.length)) := by
  simp only [vec16At, vecHeader, BitVec.ofNat_eq_ofNat]
  ac_rfl

/-- Capacity-bounded `reserve16Spec` requiring `16 * x.cap.toNat < 2 ^ 62` so
`newCap = max (max (len + 1) (2 * cap)) 4` satisfies `LayoutOk (newCap * 16) 8`. -/
def reserve16CapSpec (A : RustAlloc) (resStack : Nat) : Spec Reserve16Call where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.v ∧ s0.readReg64 .x1 = BitVec.ofNat 64 (x.bs.length / 16) ∧
      s0.readReg64 .x2 = 1#64 ∧ s0.readReg64 .x3 = 8#64 ∧ s0.readReg64 .x4 = 16#64 ∧
      16 * (x.bs.length / 16 + 1) < 2 ^ 62 ∧ 16 * x.cap.toNat < 2 ^ 62⌝ ∗
      vec16At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s0.sp resStack
  post := (reserve16Spec A resStack).post
  onPanic := (reserve16Spec A resStack).onPanic

/-- Equality-guarded `reserve16Spec` for `Vec::push` growth (`x.cap = BitVec.ofNat 64 (x.bs.length / 16)`),
preserving `sf.trace = s0.trace ∧ sf.fs = s0.fs` and `allocFailedIn s0 sf` on panic. -/
def reserve16EqSpec (A : RustAlloc) (resStack : Nat) : Spec Reserve16Call where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.v ∧ s0.readReg64 .x1 = BitVec.ofNat 64 (x.bs.length / 16) ∧
      s0.readReg64 .x2 = 1#64 ∧ s0.readReg64 .x3 = 8#64 ∧ s0.readReg64 .x4 = 16#64 ∧
      16 * (x.bs.length / 16 + 1) < 2 ^ 62 ∧
      x.cap = BitVec.ofNat 64 (x.bs.length / 16)⌝ ∗
      vec16At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s0.sp resStack
  post := (reserve16Spec A resStack).post
  onPanic := (reserve16Spec A resStack).onPanic

/-- `do_reserve_and_handle [local#11]` meets `(reserve16CapSpec A resStack).inImage img` (including
`sf.fs = s0.fs` in `.post`) for any `resStack ≥ doReserveStackX` and arbitrary `RustAlloc`. -/
theorem reserve16Cap_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack : Nat}
    (hCF : AllocContractsFs img A ext)
    (hres : doReserveStackX ≤ resStack) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr reserve11Name)
      ((reserve16CapSpec A resStack).inImage img) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  simp only [Spec.inImage, reserve16CapSpec, vec16At_eq,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hlen62, hcap62⟩,
    ⟨hmod16, hbs_le, hcap63, hptr⟩, hmem⟩
  have hhi : resStack ≤ 2 ^ 64 := by
    have hm := hmem
    rw [stackAt, repack_stack_bound] at hm
    exact GrowOne.Helpers.memRegion_bound_of_pointsTo64 hm
  have hlo : 64 + finishGrowStackX ≤ resStack := by
    have : 64 + finishGrowStackX = doReserveStackX := by decide
    omega
  have hsplit : stackAt s0.sp resStack =
      memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - doReserveStackX) ∗
        stackAt s0.sp doReserveStackX :=
    GrowOne.Helpers.stackAt_split_stk s0.sp hlo hhi
  rw [hsplit, repack_raw_pre] at hmem
  let len := x.bs.length / 16
  let newCap := SpqrV1.Alloc.reserveCapStride 16 x.cap.toNat len 1
  have hx1_nat : (s0.readReg64 .x1).toNat = len := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp [len]; omega)]
  have hx2_nat : (s0.readReg64 .x2).toNat = 1 := by rw [hx2]; rfl
  have hlen_le_cap : len ≤ x.cap.toNat := by dsimp [len]; omega
  have hnew_mul : newCap * 16 + 8 ≤ 2 ^ 63 := by
    dsimp [newCap, SpqrV1.Alloc.reserveCapStride, SpqrV1.Alloc.reserveMinCap, len]
    omega
  have hlay : LayoutOk (newCap * 16) 8 :=
    ⟨by dsimp [newCap, SpqrV1.Alloc.reserveCapStride, SpqrV1.Alloc.reserveMinCap]; omega,
     ⟨3, rfl⟩, hnew_mul⟩
  let xs : SpqrV1.Alloc.DoReserveStrideCall :=
    ⟨x.v, x.cap, x.ptr, x.bs, len, 1, 8#64, 16#64⟩
  let F : SepProp :=
    ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 len) ∗
      memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - doReserveStackX) ∗ R
  have hcap_comm : x.cap.toNat * 16 = 16 * x.cap.toNat := Nat.mul_comm _ _
  have hpre' : s0.mem ⊨ ((doReserveStrideRawSpecX A).keepsFs.inImage img).pre xs s0 ∗ F := by
    simp only [Spec.inImage, Spec.keepsFs, doReserveStrideRawSpecX, xs,
      show (8#64 : BitVec 64).toNat = 8 from rfl,
      show (16#64 : BitVec 64).toNat = 16 from rfl,
      hcap_comm, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1_nat, hx2_nat, hx3, hx4, hlen_le_cap, hbs_le, hptr, by decide, hlay⟩, hmem⟩
  refine subroutine_ok.mono_outcome (reserve11_raw_fs_ok hCF) xs F s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.inImage, Spec.keepsFs, doReserveStrideRawSpecX, reserve16CapSpec,
      reserve16Spec, vec16At_eq, xs, show (8#64 : BitVec 64).toNat = 8 from rfl,
      show (16#64 : BitVec 64).toNat = 16 from rfl] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hfs, hq⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htrace, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨p', hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hp'_ne, _⟩, hpost_mem⟩
    have hnew_lt64 : newCap < 2 ^ 64 := by omega
    have htoNat : (BitVec.ofNat 64 newCap).toNat = newCap := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnew_lt64]
    have hgrow : len + 1 ≤ newCap := by
      dsimp [newCap, SpqrV1.Alloc.reserveCapStride]; omega
    have hbs_le' : x.bs.length ≤ 16 * newCap := by dsimp [len] at hgrow; omega
    have hcap63' : 16 * newCap < 2 ^ 63 := by omega
    have hcap_ne : BitVec.ofNat 64 newCap ≠ 0#64 := by
      intro heq
      have ht := congrArg BitVec.toNat heq
      rw [htoNat] at ht
      change newCap = 0 at ht
      omega
    have hnew_comm : newCap * 16 = 16 * newCap := Nat.mul_comm _ _
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htrace, hfs⟩, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨BitVec.ofNat 64 newCap, p', ?_⟩
    simp only [hcap_ne, ite_false, htoNat, hsplit]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hgrow, ?_⟩
    rw [satisfies_pure_sepConj]
    refine ⟨⟨hmod16, hbs_le', hcap63', hp'_ne⟩, ?_⟩
    rw [hnew_comm] at hpost_mem
    rw [← repack_raw_post]
    dsimp only [F] at hpost_mem
    exact hpost_mem
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, Spec.keepsFs, doReserveStrideRawSpecX, reserve16CapSpec,
      reserve16Spec, F] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    refine ⟨hq.1.1, ?_⟩
    rw [repack_anyHeap] at hq
    exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hq.2
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hq).elim

/-- `do_reserve_and_handle [local#11]` meets `(reserve16EqSpec A resStack).inImage img` (the exact
`cap == len` call-site contract in `main_m2`, including `sf.fs = s0.fs` in `.post`) for arbitrary
`RustAlloc`. -/
theorem reserve16Eq_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack : Nat}
    (hCF : AllocContractsFs img A ext)
    (hres : doReserveStackX ≤ resStack) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr reserve11Name)
      ((reserve16EqSpec A resStack).inImage img) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  simp only [Spec.inImage, reserve16EqSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hlen62, hcap_eq⟩, hmem⟩
  have hcap62 : 16 * x.cap.toNat < 2 ^ 62 := by
    rw [hcap_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hpre' : s0.mem ⊨ ((reserve16CapSpec A resStack).inImage img).pre x s0 ∗ R := by
    simp only [Spec.inImage, reserve16CapSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hlen62, hcap62⟩, hmem⟩
  exact subroutine_ok.mono_outcome (reserve16Cap_ok hCF hres) x R s0 hpc hrun hpre' hsp
    (fun _ hout => hout)

private theorem pull_live_bound (C0 C1 C2 Live Rest : SepProp) :
    C0 ∗ C1 ∗ C2 ∗ Live ∗ Rest = Live ∗ (C0 ∗ C1 ∗ C2 ∗ Rest) := by ac_rfl

/-- Discharges `MainCallees.reserve16` for any allocator model `A` whose `A.live` token enforces
`sz < 2 ^ 62` (e.g., arenas `< 2 ^ 62`). For token-free `A`, see `reserve16Cap_ok`,
`reserve16Eq_ok`, and `not_subroutine_ok_reserve16Spec`. -/
theorem reserve16_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack : Nat}
    (hCF : AllocContractsFs img A ext)
    (hres : doReserveStackX ≤ resStack)
    (_hlive : ∀ m p sz al F, (m ⊨ A.live p sz al ∗ F) → sz < 2 ^ 62) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr reserve11Name)
      ((reserve16Spec A resStack).inImage img) :=
  reserve16Cap_ok hCF hres

/-! ## 5. Counterexample Refuting Unbounded-Capacity `reserve16SpecR2`

At `x.cap = 2 ^ 58` and `x.bs = []`, `vec16At` (`16 * cap < 2 ^ 63`) and `reserve16SpecR2.pre`
hold, yet `do_reserve_and_handle [local#11]` computes `newCap = 2 ^ 59` so `finish_grow [local#12]`
panics on `isize::MAX` overflow with `sf.trace = s0.trace` (`¬ allocFailedIn s0 sf`). -/

/-- Unbounded-capacity variant of `reserve16Spec` omitting `16 * x.cap.toNat < 2 ^ 62`,
refuted by `not_subroutine_ok_reserve16Spec` below. -/
def reserve16SpecR2 (A : RustAlloc) (resStack : Nat) : Spec Reserve16Call where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.v ∧ s0.readReg64 .x1 = BitVec.ofNat 64 (x.bs.length / 16) ∧
      s0.readReg64 .x2 = 1#64 ∧ s0.readReg64 .x3 = 8#64 ∧ s0.readReg64 .x4 = 16#64 ∧
      16 * (x.bs.length / 16 + 1) < 2 ^ 62⌝ ∗
      vec16At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s0.sp resStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
      (∃∗ cap' : BitVec 64, ∃∗ p' : BitVec 64,
        ⌜x.bs.length / 16 + 1 ≤ cap'.toNat⌝ ∗ vec16At A x.v cap' p' x.bs) ∗
      A.pool ∗ stackAt s0.sp resStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf⌝ ∗ anyHeap

/-- Pure side conditions of `reserve16SpecR2.pre` and `vec16At` hold simultaneously at
`cap = BitVec.ofNat 64 (2 ^ 58)`, `bs = []` (`16 * cap.toNat = 2 ^ 62 < 2 ^ 63`). -/
theorem reserve16_overflow_call_valid :
    let cap : BitVec 64 := BitVec.ofNat 64 (2 ^ 58)
    let bs : List (BitVec 8) := []
    16 * (bs.length / 16 + 1) < 2 ^ 62 ∧
      bs.length % 16 = 0 ∧ bs.length ≤ 16 * cap.toNat ∧ 16 * cap.toNat < 2 ^ 63 := by
  decide

private def finishGrowOverflowSpec :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (out, cap, ptr, v1, v2) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = BitVec.ofNat 64 (2 ^ 59) ∧
      s.readReg64 .x4 = 8#64 ∧ s.readReg64 .x5 = 16#64⌝ ∗
    (out ↦₆₄ v1) ∗ ((out + 8#64) ↦₆₄ v2) ∗ stackAt s.sp finishGrowStackX
  post := fun (out, _, _, _, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (out ↦₆₄ 1#64) ∗ ((out + 8#64) ↦₆₄ 0#64) ∗ stackAt s0.sp finishGrowStackX

private theorem stackAt_finishGrowX (sp : BitVec 64) :
    stackAt sp finishGrowStackX =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp 16384 6 (by decide)

private theorem finish_grow_overflow_ok {img : Obj.Image}
    {ext : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliFinishGrowName)
      (finishGrowOverflowSpec.inImage img) := by
  unfold Spec.inImage finishGrowOverflowSpec
  simp only [stackAt_finishGrowX]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff cliFinishGrowName =
      num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]") :=
    (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]")
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.SignalSession.Cli.FinishGrow.libsignalSessionBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]")) 180
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, cap, ptr, v1, v2⟩ := x
  dsimp only at *
  wp_steps
  wp_done

/-- Concrete overflow-panic specification on `(reserve16SpecR2 A resStack).inImage img` at
`x.cap = BitVec.ofNat 64 (2 ^ 58)`, `x.bs = []`: `[local#11]` never returns and panics with
`sf.trace = s0.trace` (`¬ allocFailedIn s0 sf`), independent of `AllocContractsX`. -/
def reserve16SilentPanicSpec (A : RustAlloc) (resStack : Nat) (img : Obj.Image) :
    Spec Reserve16Call where
  pre := fun x s0 =>
    ⌜x.cap = BitVec.ofNat 64 (2 ^ 58) ∧ x.bs = []⌝ ∗
      ((reserve16SpecR2 A resStack).inImage img).pre x s0
  post := fun _ _ _ => ⌜False⌝
  onPanic := fun _ s0 sf => ⌜sf.trace = s0.trace ∧ ¬ allocFailedIn s0 sf⌝ ∗ anyHeap

private theorem reserve16_silent_panic_raw_ok {img : Obj.Image}
    {ext : String → Option (State → State)} :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr reserve11Name)
      ({ pre := fun (v, ptr) s =>
           ⌜s.readReg64 .x0 = v ∧ s.readReg64 .x1 = 0#64 ∧
             s.readReg64 .x2 = 1#64 ∧ s.readReg64 .x3 = 8#64 ∧ s.readReg64 .x4 = 16#64⌝ ∗
           (v ↦₆₄ BitVec.ofNat 64 (2 ^ 58)) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
           stackAt s.sp doReserveStackX
         post := fun _ _ _ => ⌜False⌝
         onPanic := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ ∗ anyHeap
         : Spec (BitVec 64 × BitVec 64) }.inImage img) := by
  unfold Spec.inImage mProg
  simp only [GrowOne.Helpers.stackAt_cliGrowOne, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff reserve11Name =
      num% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]") :=
    cliDoReserve_fnOff
  have hpanic := panic_at_handle_error_norm_ext (b := img.base) (ext := ext)
    (name := reserve11Name)
    (k := num% (ls_rel%
      "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
      "alloc::raw_vec::handle_error"))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg := finish_grow_overflow_ok (img := img) (ext := ext)
  rw [Program.fnAddr_rel (name := reserve11Name)
    hfn cliFinishGrow_fnOff
    (k := num% (ls_rel%
      "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
      "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]"))
    (by decide)] at hfg
  code_fetches CryptoVerification.libsignalSessionCode cliReserve11Bin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]")) 140
  dsimp only [tripleRatchetProgAtExt] at hpanic hfg ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr reserve11Name = fnBase
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, ptr⟩ := x
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  apply SepWPp.of_sepWP (mid := fnBase + bv% (88))
  apply SepWP.seq_inImage
    (mid := fnBase + bv% (ls_rel%
      "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
      "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]"))
    hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  rintro ⟨hF1, hsym1⟩
  wp_call hfg (s0.sp - 56#64, BitVec.ofNat 64 (2 ^ 58), ptr, v_stk_1, v_stk_2)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  apply SepWPp.of_sepWP
    (mid := fnBase + bv% (ls_rel%
      "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
      "alloc::raw_vec::handle_error"))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨by simp only [Rust.panicked, wp_norm, arm64_norm, *],
    Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm⟩

/-- Under `((reserve16SpecR2 A resStack).inImage img).pre x s0` with `x.cap = BitVec.ofNat 64 (2 ^ 58)`
and `x.bs = []`, `do_reserve_and_handle [local#11]` panics silently (`sf.trace = s0.trace`,
`¬ allocFailedIn s0 sf`). -/
theorem reserve16Spec_silent_panic_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack : Nat}
    (hstk : doReserveStackX ≤ resStack) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr reserve11Name)
      (reserve16SilentPanicSpec A resStack img) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  rcases x with ⟨v, cap, ptr, bs⟩
  simp only [reserve16SilentPanicSpec, Spec.inImage, reserve16SpecR2, vec16At_eq,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨rfl, rfl⟩, hinv, ⟨hx0, hx1, hx2, hx3, hx4, _⟩, ⟨_, _, _, _⟩, hmem⟩
  have hhi : resStack ≤ 2 ^ 64 := by
    have hm := hmem
    rw [stackAt, repack_stack_bound] at hm
    exact GrowOne.Helpers.memRegion_bound_of_pointsTo64 hm
  have hlo : 64 + finishGrowStackX ≤ resStack := by
    have : 64 + finishGrowStackX = doReserveStackX := by decide
    omega
  have hsplit : stackAt s0.sp resStack =
      memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - doReserveStackX) ∗
        stackAt s0.sp doReserveStackX :=
    GrowOne.Helpers.stackAt_split_stk s0.sp hlo hhi
  rw [hsplit] at hmem
  let F : SepProp :=
    ((v + 16#64) ↦₆₄ 0#64) ∗
      (if BitVec.ofNat 64 (2 ^ 58) = 0#64 then emp
       else A.live ptr (16 * (BitVec.ofNat 64 (2 ^ 58)).toNat) 8 ∗ (ptr ↦ₛ []) ∗
         memRegion (ptr + 0#64) (16 * (BitVec.ofNat 64 (2 ^ 58)).toNat - 0)) ∗
      A.pool ∗ memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - doReserveStackX) ∗ R
  have hrepack :
      ∀ (C0 C1 C2 Buf Pool Extra SubStack : SepProp),
        C0 ∗ C1 ∗ C2 ∗ Buf ∗ Pool ∗ (Extra ∗ SubStack) ∗ R =
          C0 ∗ C1 ∗ SubStack ∗ (C2 ∗ Buf ∗ Pool ∗ Extra ∗ R) := fun _ _ _ _ _ _ _ => by ac_rfl
  rw [List.length_nil] at hx1 hmem
  change s0.readReg64 .x1 = 0#64 at hx1
  change s0.mem ⊨ (v ↦₆₄ BitVec.ofNat 64 (2 ^ 58)) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
    (if BitVec.ofNat 64 (2 ^ 58) = 0#64 then emp
     else A.live ptr (16 * (BitVec.ofNat 64 (2 ^ 58)).toNat) 8 ∗ (ptr ↦ₛ []) ∗
       memRegion (ptr + 0#64) (16 * (BitVec.ofNat 64 (2 ^ 58)).toNat - 0)) ∗
    A.pool ∗ (memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - doReserveStackX) ∗
      stackAt s0.sp doReserveStackX) ∗ R at hmem
  rw [hrepack] at hmem
  have hpre' : s0.mem ⊨
      ({ pre := fun (v, ptr) s =>
           ⌜s.readReg64 .x0 = v ∧ s.readReg64 .x1 = 0#64 ∧
             s.readReg64 .x2 = 1#64 ∧ s.readReg64 .x3 = 8#64 ∧ s.readReg64 .x4 = 16#64⌝ ∗
           (v ↦₆₄ BitVec.ofNat 64 (2 ^ 58)) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
           stackAt s.sp doReserveStackX
         post := fun _ _ _ => ⌜False⌝
         onPanic := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ ∗ anyHeap
         : Spec (BitVec 64 × BitVec 64) }.inImage img).pre (v, ptr) s0 ∗ F := by
    simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4⟩, hmem⟩
  refine subroutine_ok.mono_outcome (reserve16_silent_panic_raw_ok (img := img) (ext := ext))
    (v, ptr) F s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨_, _, hq⟩ | ⟨hpan, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · dsimp only [Spec.inImage] at hq
    rw [satisfies_pure_sepConj] at hq
    exact hq.1.elim
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, reserve16SilentPanicSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    have hnot : ¬ allocFailedIn s0 sf := by
      simp [allocFailedIn, hq.1]
    have hany : ∀ (C2 Buf Pool Extra : SepProp),
        anyHeap ∗ (C2 ∗ Buf ∗ Pool ∗ Extra ∗ R) =
          (anyHeap ∗ C2 ∗ Buf ∗ Pool ∗ Extra) ∗ R := fun _ _ _ _ => by ac_rfl
    dsimp only [F] at hq
    rw [hany] at hq
    exact ⟨⟨hq.1, hnot⟩, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hq.2⟩
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hq).elim

/-- Refutation of `reserve16SpecR2` on `do_reserve_and_handle [local#11]`: at
`x.cap = BitVec.ofNat 64 (2 ^ 58)` and `x.bs = []` (with `doReserveStackX ≤ resStack` and
`HaltsAtReturn (mProg img ext) s0`), `[local#11]` panics on capacity overflow inside
`finish_grow [local#12]` without emitting `allocFailedEvent`. -/
theorem not_subroutine_ok_reserve16Spec
    {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack : Nat}
    (hstk : doReserveStackX ≤ resStack)
    (x : Reserve16Call) (s0 : State)
    (hcap : x.cap = BitVec.ofNat 64 (2 ^ 58))
    (hbs : x.bs = [])
    (hentry : AapcsEntry s0 ((mProg img ext).fnAddr reserve11Name))
    (hcode : (mProg img ext).CodeLoaded s0.mem)
    (hpre : s0.mem ⊨ ((reserve16SpecR2 A resStack).inImage img).pre x s0)
    (hlr : ProofLib.Disproof.HaltsAtReturn (mProg img ext) s0) :
    ¬ subroutine_ok (mProg img ext) ((mProg img ext).fnAddr reserve11Name)
        ((reserve16SpecR2 A resStack).inImage img) := by
  have hpre_sil : s0.mem ⊨ (reserve16SilentPanicSpec A resStack img).pre x s0 ∗ emp := by
    simp only [reserve16SilentPanicSpec, sepConj_emp, satisfies_pure_sepConj]
    exact ⟨⟨hcap, hbs⟩, hpre⟩
  have hwp : SepWPp (mProg img ext) (s0.readReg64 Reg.lr) s0
      ((reserve16SilentPanicSpec A resStack img).pre x s0)
      (fun _ _ => False)
      (fun sf _ => ¬ (sf.mem ⊨ ((reserve16SpecR2 A resStack).inImage img).onPanic x s0 sf ∗ emp)) := by
    refine SepWPp.call_wpp (reserve16Spec_silent_panic_ok (A := A) hstk) (x := x) (F := emp)
      hentry.1 hentry.2.1 hentry.2.2 rfl
      (fun R hm => by rwa [emp_sepConj])
      (fun _ _ _ _ hq => allowPanic_not_exited hq)
      (fun sf _ ⟨R', hq⟩ hon => ?_)
      (fun sf hpcm hrunm _ _ => ?_)
      (fun _ _ _ hq => (allowPanic_not_exited hq).elim)
    · simp only [reserve16SilentPanicSpec, sepConj_assoc, satisfies_pure_sepConj] at hq
      simp only [Spec.inImage, reserve16SpecR2, sepConj_emp, satisfies_pure_sepConj] at hon
      exact hq.1.2 hon.1
    · intro R hm _
      simp only [reserve16SilentPanicSpec, sepConj_emp, satisfies_pure_sepConj] at hm
      exact hm.1.elim
  rcases hwp emp hpre_sil hcode with
      ⟨sf, hsteps, ⟨_, _, _, _, hf⟩ | ⟨hpan, _, _, hpost_false⟩ | ⟨_, hmo⟩⟩
  · exact hf.elim
  · exact ProofLib.Disproof.not_subroutine_ok_of_panic_post_false
      x emp hentry hcode (by simpa only [sepConj_emp] using hpre) hsteps hpan hpost_false hlr
  · exact (not_satisfies_false_sepConj hmo).elim

end CryptoVerification.SignalSession.Cli.MainHops
