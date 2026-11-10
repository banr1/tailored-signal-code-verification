/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.Prost
import ProofLib.SepLogic.WPp

/-!
# `prost::encoding::varint::decode_varint` Proof for `CliC`

Proves `decodeVarint2Spec` and `(decodeVarint2SpecX A).inImage img` for `CliC`
`prost::encoding::varint::decode_varint::<&mut &[u8]>` in the CLI image.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Varint

open Arm64 ProofLib CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Prost


set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

abbrev _root_.CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2Name : String :=
  "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]"

theorem _root_.CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2_fnOff :
    libsignalSessionCode.fnOff CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2Name = (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]") :=
  (ls_lemma% fnOff "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]")

gen_decodes libsignalSessionCode_tree decodeVarint2CliC [(ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]" + 0) → (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]" + 576)]

theorem _root_.CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2_add_from_eq_fnAddr (b : BitVec 64) (H : String → Option (State → State)) :
    (libsignalSessionCode.rebase b H).fnAddr CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2Name + bv% ((2^64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]") % 2^64) =
      (libsignalSessionCode.rebase b H).fnAddr decodeErrorFromName := by
  have h1 := (ls_lemma% fnOff "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]")
  have h2 := libsignalSessionCode_fnOff_0x459a8
  change (b + BitVec.ofNat 64 (libsignalSessionCode.fnOff CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2Name)) + bv% ((2^64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]") % 2^64) =
    b + BitVec.ofNat 64 (libsignalSessionCode.fnOff decodeErrorFromName)
  rw [h1, h2]
  bv_omega

/-- The `decode_varint_slow` call target as a wrapping offset from this copy: in the CLI image
`decode_varint_slow` may lie below the copy, so the Nat offset `k` of `decodeVarintSlow_ok_at*` is
taken from the callee's own entry (`k = 0`). -/
theorem _root_.CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2_add_slow_eq_fnAddr (b : BitVec 64) (H : String → Option (State → State)) :
    (libsignalSessionCode.rebase b H).fnAddr CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2Name + bv% ((2^64 + ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]")) % 2^64) =
      (libsignalSessionCode.rebase b H).fnAddr varintSlowName + BitVec.ofNat 64 0 := by
  have h1 := (ls_lemma% fnOff "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]")
  have h2 := (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>")
  change (b + BitVec.ofNat 64 (libsignalSessionCode.fnOff CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2Name)) + bv% ((2^64 + ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]")) % 2^64) =
    (b + BitVec.ofNat 64 (libsignalSessionCode.fnOff varintSlowName)) + BitVec.ofNat 64 0
  rw [h1, h2]
  bv_omega

set_option maxHeartbeats 8000000 in
theorem _root_.CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2_ok_of_contracts {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2Name + bv% ((2^64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]") % 2^64))
      (decodeErrorFromSpec A))
    (hSlowCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2Name + bv% ((2^64 + ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]")) % 2^64))
      (Prost.decodeVarintSlowSpec A)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2Name)
      (decodeVarint2Spec A) := by
  unfold decodeVarint2Spec
  simp only [sliceCursorAt, stackAt_decodeVarint2, sepExists_sepConj_left, sepExists_sepConj_right]
  have hfn := (ls_lemma% fnOff "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]")
  code_fetches CryptoVerification.libsignalSessionCode decodeVarint2CliC b H hfn (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]") 580
  clear hfn
  dsimp only [CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2Name] at hFromCall hSlowCall ⊢
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr
    "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]" = entry
  generalize_entry (libsignalSessionCode.rebase b H) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨bufRef, slot, ptr, bs⟩ := x
  dsimp only at *
  cases bs with
  | nil =>
    have hd_nil : decodeVarint ([] : List (BitVec 8)) = none := rfl
    rw [hd_nil]
    dsimp only
    apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]") % 2^64))
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 [].length)) (by sep_focus)
    conv => arg 4; rw [stackAt_slow_eq_errorHook (s0.sp - 64#64)]
    wp_reach
    refine SepWPp.call_frame (x := (s0.sp - 64#64, 0x8000000000000001#64))
      (ret_pc := entry + 460#64) hFromCall
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]; rfl)
      (⟨rfl, by decide⟩ : s0.sp - 64#64 = s0.sp - 64#64 ∧ KindNoHeap 0x8000000000000001#64)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved, arm64_norm] at hcsm
    rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
    apply SepWPp.of_sepWP_ret
    conv => arg 4; simp only [memRegion_48_split, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
    apply SepWP.exists_elim; intro v_err
    apply SepWP.fold (stackAt_errorHook_entails_slow s0.sp) (by sep_focus)
    wp_steps
    wp_done
  | cons b0 bs1 =>
    have hcbz := cbz_len_cons_false h
    by_cases hb0 : b0 ≤ 0x7f#8
    · have hbit0 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_le hb0
      rw [decodeVarint_1 bs1 hb0]
      dsimp only
      rw [sliceCursorAfter_of_eq (k := 1) rfl]
      apply SepWPp.of_sepWP_ret
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps
      conv => arg 4; rw [← pointsToBytes_cons]
      wp_done
    · have hbit0 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_gt hb0
      apply SepWPp.of_sepWP (mid := entry + 64#64)
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps
      wp_reach
      by_cases hpre : VarintSlicePre (b0 :: bs1)
      · obtain ⟨b1, bs2, rfl⟩ := exists_cons_of_all_gt (pre := [b0]) hpre (by simp)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, hb0, not_false_eq_true])
        suffices hjoin : SepWPp prog (s0.readReg64 Reg.lr)
            ((((((((s0.writeReg64 Reg.sp (s0.sp - 64#64)).writeReg64 (Reg.gpr 29#5) (s0.sp - 16#64)).writeReg64
                (Reg.gpr 8#5) slot).writeReg64 (Reg.gpr 9#5)
                (BitVec.ofNat 64 (b0 :: b1 :: bs2).length)).writeReg64 (Reg.gpr 10#5) ptr).writeReg64
                (Reg.gpr 1#5) (BitVec.signExtend 64 b0)).writeReg64
                (Reg.gpr 11#5) (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 b1)))).setPState
                (subsPState64 (BitVec.ofNat 64 (b0 :: b1 :: bs2).length) 10#64)
              |>.setPC (entry + 88#64) |>.setMem m)
            (bufRef ↦₆₄ slot ∗ slot ↦₆₄ ptr ∗
              (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (b0 :: b1 :: bs2).length ∗
              (ptr ↦₈ b0 ∗ ((ptr + 1#64) ↦₈ b1 ∗ (ptr + 1#64 + 1#64) ↦ₛ bs2)) ∗ A.pool ∗
              stackAt (s0.sp - 64#64) decodeVarintSlowStack ∗ memRegion (s0.sp - 56#64) 40 ∗
              (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗
              (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
              (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5))
            (fun sf P_f =>
              (sf.mem ⊨ P_f ∗ R →
                  sf.mem ⊨
                    (∃∗ x, ∃∗ x_1, ∃∗ x_2,
                      (match decodeVarint (b0 :: b1 :: bs2) with
                        | some (v, _) => ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝
                        | none => ⌜sf.readReg64 .x0 = 1#64⌝) ∗
                        ⌜sf.trace = s0.trace⌝ ∗ bufRef ↦₆₄ slot ∗ A.pool ∗
                        (stackAt (s0.sp - 64#64) decodeVarintSlowStack ∗
                          memRegion (s0.sp - 56#64) 40 ∗
                          (s0.sp - 64#64) ↦₆₄ x_2 ∗ (s0.sp - 16#64) ↦₆₄ x_1 ∗
                          (s0.sp - 8#64) ↦₆₄ x) ∗
                        match decodeVarint (b0 :: b1 :: bs2) with
                        | some (_, rest) =>
                          sliceCursorAfter slot ptr (b0 :: b1 :: bs2) rest
                        | none =>
                          ⌜sf.readReg64 .x1 ≠ 0#64⌝ ∗
                            decodeErrorAtStackLen A (sf.readReg64 .x1) 0 ∗
                            memRegion slot 16 ∗ ptr ↦ₛ (b0 :: b1 :: bs2)) ∗ R) ∧
                sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
            (fun sf P_f => sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R) by
          by_cases h11 : 11 ≤ (b0 :: b1 :: bs2).length
          · have hhi := ult_10_of_ge_11 h11 h
            apply SepWPp.of_sepWP (mid := entry + 88#64)
            conv => arg 4; rw [pointsToBytes_cons]
            wp_steps
            wp_reach
            exact hjoin
          · rcases hpre with h11' | ⟨hne, hlast⟩
            · exact (h11 h11').elim
            · have hhi := ult_10_of_lt_11 h11 h
              have hbit_last := VarintSliceBits.getLsbD_7_beq_of_le hlast
              apply SepWPp.of_sepWP (mid := entry + 84#64)
              conv => arg 4; rw [← pointsToBytes_cons, pointsToBytes_split_last ptr (b0 :: b1 :: bs2) hne h]
              wp_steps
              conv => arg 4; rw [← pointsToBytes_split_last ptr (b0 :: b1 :: bs2) hne h, pointsToBytes_cons, pointsToBytes_cons]
              wp_reach
              apply SepWPp.of_sepWP (mid := entry + 88#64)
              wp_steps
              wp_reach
              exact hjoin
        by_cases hnone : decodeVarint (b0 :: b1 :: bs2) = none
        · obtain ⟨b0', b1', b2, b3, b4, b5, b6, b7, b8, b9, rest, heq,
            hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9⟩ := decodeVarint_eq_none_of_pre hpre hnone
          cases heq
          rw [hnone]; dsimp only
          have hbit1 := VarintSliceBits.getLsbD_7_beq_of_gt hb1
          have hbit2 := VarintSliceBits.getLsbD_7_beq_of_gt hb2
          have hbit3 := VarintSliceBits.getLsbD_7_beq_of_gt hb3
          have hbit4 := VarintSliceBits.getLsbD_7_beq_of_gt hb4
          have hbit5 := VarintSliceBits.getLsbD_7_beq_of_gt hb5
          have hbit6 := VarintSliceBits.getLsbD_7_beq_of_gt hb6
          have hbit7 := VarintSliceBits.getLsbD_7_beq_of_gt hb7
          have hbit8 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_gt hb8
          have hovf2 := ovf_byte2 hb0 hb1
          have hovf3 := ovf_byte3 hb0 hb1 hb2
          have hovf4 := VarintSliceBits.ovf_byte4_zext hb0 hb1 hb2 hb3
          have hovf6 := ovf_byte6 hb4 hb5
          have hovf7 := ovf_byte7 hb4 hb5 hb6
          have hovf8 := VarintSliceBits.ovf_byte8_zext hb4 hb5 hb6 hb7
          have hb9_ult := byte9_ult1_of_ge hb9
          have hb9_ule := byte9_ule_of_ge hb9
          apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]") % 2^64))
          conv => arg 4; simp only [pointsToBytes_cons]
          wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: rest).length)) (by sep_focus)
          conv => arg 4; rw [stackAt_slow_eq_errorHook (s0.sp - 64#64)]
          wp_reach
          refine SepWPp.call_frame (x := (s0.sp - 64#64, 0x8000000000000001#64))
            (ret_pc := entry + 460#64) hFromCall
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
            (by simp only [arm64_norm])
            (by simp only [arm64_norm]; rfl)
            (⟨rfl, by decide⟩ : s0.sp - 64#64 = s0.sp - 64#64 ∧ KindNoHeap 0x8000000000000001#64)
            (by sep_focus)
            (fun _ _ _ _ hex => allowPanic_not_exited hex)
            (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
          intro sm hpcm hrunm hspm hcsm
          simp only [CalleeSavedPreserved, arm64_norm] at hcsm
          rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
          apply SepWPp.of_sepWP_ret
          conv => arg 4; simp only [memRegion_48_split, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
          apply SepWP.exists_elim; intro v_err
          apply SepWP.fold (stackAt_errorHook_entails_slow s0.sp) (by sep_focus)
          wp_steps
          apply SepWP.done
          · simp only [arm64_norm]
          · simp only [arm64_norm, hrunm]
          · refine ⟨?_, by simp only [arm64_norm], ?_⟩
            · intro hm_final
              simp only [pointsToBytes_cons, sepExists_sepConj_left, arm64_norm] at hm_final ⊢
              rcases hm_final with ⟨⟨hx0_ne, htr⟩, hm_final⟩
              refine ⟨s0.readReg64 (Reg.gpr 30#5), s0.readReg64 (Reg.gpr 29#5), v_err, ⟨htr, hx0_ne⟩, ?_⟩
              arm64_sep_close
            · simp only [CalleeSavedPreserved, arm64_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
        · apply SepWPp.of_sepWP_ret
          wp_steps 4
          by_cases hb1 : b1 ≤ 0x7f#8
          · have hbit1 := VarintSliceBits.getLsbD_7_beq_of_le hb1
            rw [decodeVarint_2 bs2 hb0 hb1]
            dsimp only
            rw [sliceCursorAfter_of_eq (k := 2) rfl]
            wp_steps
            conv => arg 4; simp only [← pointsToBytes_cons]
            wp_done
          · have hbit1 := VarintSliceBits.getLsbD_7_beq_of_gt hb1
            have hovf2 := ovf_byte2 hb0 hb1
            obtain ⟨b2, bs3, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1]) hpre (by simp)
              (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                hb0, hb1, not_false_eq_true, and_self])
            conv => arg 4; rw [pointsToBytes_cons]
            wp_steps 7
            by_cases hb2 : b2 ≤ 0x7f#8
            · have hbit2 := VarintSliceBits.getLsbD_7_beq_of_le hb2
              rw [decodeVarint_3 bs3 hb0 hb1 hb2]
              dsimp only
              rw [sliceCursorAfter_of_eq (k := 3) rfl]
              wp_steps
              conv => arg 4; simp only [← pointsToBytes_cons]
              wp_done
            · have hbit2 := VarintSliceBits.getLsbD_7_beq_of_gt hb2
              have hovf3 := ovf_byte3 hb0 hb1 hb2
              obtain ⟨b3, bs4, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2]) hpre (by simp)
                (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                  hb0, hb1, hb2, not_false_eq_true, and_self])
              conv => arg 4; rw [pointsToBytes_cons]
              wp_steps 7
              by_cases hb3 : b3 ≤ 0x7f#8
              · have hbit3 := VarintSliceBits.getLsbD_7_beq_of_le hb3
                rw [decodeVarint_4 bs4 hb0 hb1 hb2 hb3]
                dsimp only
                rw [sliceCursorAfter_of_eq (k := 4) rfl]
                wp_steps
                conv => arg 4; simp only [← pointsToBytes_cons]
                wp_done
              · have hbit3 := VarintSliceBits.getLsbD_7_beq_of_gt hb3
                have hovf4 := VarintSliceBits.ovf_byte4_zext hb0 hb1 hb2 hb3
                obtain ⟨b4, bs5, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3]) hpre (by simp)
                  (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                    hb0, hb1, hb2, hb3, not_false_eq_true, and_self])
                conv => arg 4; rw [pointsToBytes_cons]
                wp_steps 7
                by_cases hb4 : b4 ≤ 0x7f#8
                · have hbit4 := VarintSliceBits.getLsbD_7_beq_of_le hb4
                  rw [decodeVarint_5 bs5 hb0 hb1 hb2 hb3 hb4]
                  dsimp only
                  rw [sliceCursorAfter_of_eq (k := 5) rfl]
                  wp_steps
                  conv => arg 4; simp only [← pointsToBytes_cons]
                  wp_done
                · have hbit4 := VarintSliceBits.getLsbD_7_beq_of_gt hb4
                  obtain ⟨b5, bs6, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4]) hpre (by simp)
                    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                      hb0, hb1, hb2, hb3, hb4, not_false_eq_true, and_self])
                  conv => arg 4; rw [pointsToBytes_cons]
                  wp_steps 5
                  by_cases hb5 : b5 ≤ 0x7f#8
                  · have hbit5 := VarintSliceBits.getLsbD_7_beq_of_le hb5
                    rw [decodeVarint_6 bs6 hb0 hb1 hb2 hb3 hb4 hb5]
                    dsimp only
                    rw [sliceCursorAfter_of_eq (k := 6) rfl]
                    wp_steps
                    conv => arg 4; simp only [← pointsToBytes_cons]
                    wp_done
                  · have hbit5 := VarintSliceBits.getLsbD_7_beq_of_gt hb5
                    have hovf6 := ovf_byte6 hb4 hb5
                    obtain ⟨b6, bs7, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4, b5]) hpre
                      (by simp) (by simp only [List.mem_cons, List.not_mem_nil, or_false,
                        forall_eq_or_imp, forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, not_false_eq_true,
                        and_self])
                    conv => arg 4; rw [pointsToBytes_cons]
                    wp_steps 7
                    by_cases hb6 : b6 ≤ 0x7f#8
                    · have hbit6 := VarintSliceBits.getLsbD_7_beq_of_le hb6
                      rw [decodeVarint_7 bs7 hb0 hb1 hb2 hb3 hb4 hb5 hb6]
                      dsimp only
                      rw [sliceCursorAfter_of_eq (k := 7) rfl]
                      wp_steps
                      conv => arg 4; simp only [← pointsToBytes_cons]
                      wp_done
                    · have hbit6 := VarintSliceBits.getLsbD_7_beq_of_gt hb6
                      have hovf7 := ovf_byte7 hb4 hb5 hb6
                      obtain ⟨b7, bs8, rfl⟩ := exists_cons_of_all_gt
                        (pre := [b0, b1, b2, b3, b4, b5, b6]) hpre (by simp)
                        (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                          forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, not_false_eq_true, and_self])
                      conv => arg 4; rw [pointsToBytes_cons]
                      wp_steps 7
                      by_cases hb7 : b7 ≤ 0x7f#8
                      · have hbit7 := VarintSliceBits.getLsbD_7_beq_of_le hb7
                        rw [decodeVarint_8 bs8 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7]
                        dsimp only
                        rw [sliceCursorAfter_of_eq (k := 8) rfl]
                        wp_steps
                        conv => arg 4; simp only [← pointsToBytes_cons]
                        wp_done
                      · have hbit7 := VarintSliceBits.getLsbD_7_beq_of_gt hb7
                        have hovf8 := VarintSliceBits.ovf_byte8_zext hb4 hb5 hb6 hb7
                        obtain ⟨b8, bs9, rfl⟩ := exists_cons_of_all_gt
                          (pre := [b0, b1, b2, b3, b4, b5, b6, b7]) hpre (by simp)
                          (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                            forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, not_false_eq_true,
                            and_self])
                        conv => arg 4; rw [pointsToBytes_cons]
                        wp_steps 7
                        by_cases hb8 : b8 ≤ 0x7f#8
                        · have hbit8 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_le hb8
                          rw [decodeVarint_9 bs9 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8]
                          dsimp only
                          rw [sliceCursorAfter_of_eq (k := 9) rfl]
                          wp_steps
                          conv => arg 4; simp only [← pointsToBytes_cons]
                          wp_done
                        · have hbit8 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_gt hb8
                          obtain ⟨b9, bs10, rfl⟩ := exists_cons_of_all_gt
                            (pre := [b0, b1, b2, b3, b4, b5, b6, b7, b8]) hpre (by simp)
                            (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                              forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, not_false_eq_true,
                              and_self])
                          have hb9 : ¬ 2#8 ≤ b9 := by
                            intro hge
                            apply hnone
                            rw [decodeVarint]; iterate 10 rw [decodeVarintAux]
                            by_cases hb9_le : b9 ≤ 0x7f#8 <;>
                              simp [toNat_le_0x7f_iff, two_le_toNat_iff, hb0, hb1, hb2, hb3, hb4, hb5,
                                hb6, hb7, hb8, hb9_le, hge]
                          have hb9_ult := byte9_ult1_of_lt hb9
                          have hb9_ule := byte9_ule_of_lt hb9
                          have hovf10 := ovf_byte10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
                          conv => arg 4; rw [pointsToBytes_cons]
                          rw [decodeVarint_10 bs10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9]
                          dsimp only
                          rw [sliceCursorAfter_of_eq (k := 10) rfl]
                          wp_steps
                          conv => arg 4; simp only [← pointsToBytes_cons]
                          wp_done
      · have h11 : ¬ 11 ≤ (b0 :: bs1).length := fun h => hpre (Or.inl h)
        have hne : b0 :: bs1 ≠ [] := List.cons_ne_nil b0 bs1
        have hlast : ¬ (b0 :: bs1).getLast hne ≤ 0x7f#8 := fun h => hpre (Or.inr ⟨hne, h⟩)
        have hhi := ult_10_of_lt_11 h11 h
        have hbit_last := VarintSliceBits.getLsbD_7_beq_of_gt hlast
        apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]")) % 2^64))
        conv => arg 4; rw [← pointsToBytes_cons, pointsToBytes_split_last ptr (b0 :: bs1) hne h]
        wp_steps
        conv => arg 4; rw [← pointsToBytes_split_last ptr (b0 :: bs1) hne h]
        wp_reach
        refine SepWPp.call_frame (x := ⟨bufRef, slot, ptr, b0 :: bs1⟩)
          (ret_pc := entry + 484#64) hSlowCall
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
          (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
          (by simp only [arm64_norm])
          (by simp only [arm64_norm]; rfl)
          (⟨by simp only [arm64_norm, h_1], h⟩ : _ ∧ (b0 :: bs1).length < 2 ^ 63)
          (by simp only [sliceCursorAt]; sep_focus)
          (fun _ _ _ _ hex => allowPanic_not_exited hex)
          (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
        intro sm hpcm hrunm hspm hcsm
        simp only [CalleeSavedPreserved, arm64_norm] at hcsm
        rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
        apply SepWPp.of_sepWP_ret
        cases hd : decodeVarint (b0 :: bs1) with
        | none =>
          dsimp only
          conv => arg 4; simp only [hd, sepConj_assoc, arm64_norm]
          apply SepWP.pure_elim; intro hsm0
          wp_steps
          wp_done
        | some p =>
          rcases p with ⟨v, rest⟩
          dsimp only
          conv => arg 4; simp only [hd, sepConj_assoc, arm64_norm]
          apply SepWP.pure_elim; rintro ⟨hsm0, hsm1⟩
          wp_steps
          wp_done

def _root_.CryptoVerification.CliC.SpqrV1.Varint.DecodeVarint2OkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2Name)
    (decodeVarint2Spec A)

def _root_.CryptoVerification.CliC.SpqrV1.Varint.DecodeVarint2Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2Name)
    (decodeVarint2Spec A)

def _root_.CryptoVerification.CliC.SpqrV1.Varint.DecodeVarint2OkExtX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2Name)
    ((decodeVarint2SpecX A).inImage img)

theorem _root_.CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2_ok_ext {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hC : Stage2Contracts b C A ctl uuidTryParse S ext) :
    CryptoVerification.CliC.SpqrV1.Varint.DecodeVarint2OkExt b A ext := by
  refine CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2_ok_of_contracts ?_ ?_
  · rw [CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2_add_from_eq_fnAddr]
    exact hC.decode_error_from
  · rw [CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2_add_slow_eq_fnAddr]
    exact decodeVarintSlow_ok_at_ext hC (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>")
      (k := 0) (by simp only [Nat.add_zero])

theorem _root_.CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hFrom : AllocHooks A abs) :
    CryptoVerification.CliC.SpqrV1.Varint.DecodeVarint2Ok b C A ctl abs := by
  refine CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2_ok_of_contracts ?_ ?_
  · rw [CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2_add_from_eq_fnAddr]
    exact LibsignalTripleRatchet.decodeErrorFrom_ok b C A ctl abs hFrom
  · rw [CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2_add_slow_eq_fnAddr]
    exact decodeVarintSlow_ok_at (b := b) (C := C) (ctl := ctl)
      hFrom (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>")
      (k := 0) (by simp only [Nat.add_zero])

set_option maxHeartbeats 8000000 in
theorem _root_.CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2_ok_of_contracts_x {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall0 : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2Name + bv% ((2^64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]") % 2^64))
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    (hSlowCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2Name + bv% ((2^64 + ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]")) % 2^64))
      ((decodeVarintSlowSpecX A).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2Name)
      ((decodeVarint2SpecX A).inImage img) := by
  have hFromCall :=
    decodeErrorFromSpecWithStack_inImage_mono (s2 := decodeErrorHookStackX) hFromCall0
  unfold decodeVarint2SpecX
  simp only [sliceCursorAt, stackAt_decodeVarint2X, sepExists_sepConj_left, sepExists_sepConj_right]
  have hfn := (ls_lemma% fnOff "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]")
  code_fetches CryptoVerification.libsignalSessionCode decodeVarint2CliC img.base H hfn (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]") 580
  clear hfn hFromCall0
  dsimp only [CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2Name] at hFromCall hSlowCall ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr
    "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]" = entry
  generalize_entry (libsignalSessionCode.rebase img.base H) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init_inImage x s0 hfl0 hsym0
  obtain ⟨bufRef, slot, ptr, bs⟩ := x
  dsimp only at *
  cases bs with
  | nil =>
    have hd_nil : decodeVarint ([] : List (BitVec 8)) = none := rfl
    rw [hd_nil]
    dsimp only
    apply Prost.SepWPp.of_sepWP_inv (mid := entry + bv% ((2^64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]") % 2^64)) hfl0 hsym0
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 [].length)) (by sep_focus)
    conv => arg 4; rw [stackAt_slowX_eq_errorHookX (s0.sp - 64#64)]
    wp_reach
    intro hfl1 hsym1
    refine Prost.SepWPp.call_frame_inv (x := (s0.sp - 64#64, 0x8000000000000001#64))
      (ret_pc := entry + 460#64) hFromCall hfl1 hsym1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]; rfl)
      (⟨rfl, by decide⟩ : s0.sp - 64#64 = s0.sp - 64#64 ∧ KindNoHeap 0x8000000000000001#64)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm _ _
    simp only [CalleeSavedPreserved, arm64_norm] at hcsm
    rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
    apply SepWPp.of_sepWP_ret
    conv => arg 4; simp only [memRegion_48_split, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
    apply SepWP.exists_elim; intro v_err
    apply SepWP.fold (stackAt_errorHookX_entails_slowX s0.sp) (by sep_focus)
    wp_steps
    wp_done
  | cons b0 bs1 =>
    have hcbz := cbz_len_cons_false h
    by_cases hb0 : b0 ≤ 0x7f#8
    · have hbit0 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_le hb0
      rw [decodeVarint_1 bs1 hb0]
      dsimp only
      rw [sliceCursorAfter_of_eq (k := 1) rfl]
      apply SepWPp.of_sepWP_ret
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps
      conv => arg 4; rw [← pointsToBytes_cons]
      wp_done
    · have hbit0 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_gt hb0
      apply Prost.SepWPp.of_sepWP_inv (mid := entry + 64#64) hfl0 hsym0
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps
      wp_reach
      intro hfl1 hsym1
      by_cases hpre : VarintSlicePre (b0 :: bs1)
      · obtain ⟨b1, bs2, rfl⟩ := exists_cons_of_all_gt (pre := [b0]) hpre (by simp)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, hb0, not_false_eq_true])
        suffices hjoin :
            _ → _ →
            SepWPp prog (s0.readReg64 Reg.lr)
            ((((((((s0.writeReg64 Reg.sp (s0.sp - 64#64)).writeReg64 (Reg.gpr 29#5) (s0.sp - 16#64)).writeReg64
                (Reg.gpr 8#5) slot).writeReg64 (Reg.gpr 9#5)
                (BitVec.ofNat 64 (b0 :: b1 :: bs2).length)).writeReg64 (Reg.gpr 10#5) ptr).writeReg64
                (Reg.gpr 1#5) (BitVec.signExtend 64 b0)).writeReg64
                (Reg.gpr 11#5) (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 b1)))).setPState
                (subsPState64 (BitVec.ofNat 64 (b0 :: b1 :: bs2).length) 10#64)
              |>.setPC (entry + 88#64) |>.setMem m)
            (bufRef ↦₆₄ slot ∗ slot ↦₆₄ ptr ∗
              (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (b0 :: b1 :: bs2).length ∗
              (ptr ↦₈ b0 ∗ ((ptr + 1#64) ↦₈ b1 ∗ (ptr + 1#64 + 1#64) ↦ₛ bs2)) ∗ A.pool ∗
              stackAt (s0.sp - 64#64) decodeVarintSlowStackX ∗ memRegion (s0.sp - 56#64) 40 ∗
              (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗
              (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
              (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5))
            (fun sf P_f =>
              (sf.mem ⊨ P_f ∗ R →
                  sf.mem ⊨
                    (∃∗ x, ∃∗ x_1, ∃∗ x_2,
                      (match decodeVarint (b0 :: b1 :: bs2) with
                        | some (v, _) => ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝
                        | none => ⌜sf.readReg64 .x0 = 1#64⌝) ∗
                        ⌜sf.trace = s0.trace⌝ ∗ bufRef ↦₆₄ slot ∗ A.pool ∗
                        (stackAt (s0.sp - 64#64) decodeVarintSlowStackX ∗
                          memRegion (s0.sp - 56#64) 40 ∗
                          (s0.sp - 64#64) ↦₆₄ x_2 ∗ (s0.sp - 16#64) ↦₆₄ x_1 ∗
                          (s0.sp - 8#64) ↦₆₄ x) ∗
                        match decodeVarint (b0 :: b1 :: bs2) with
                        | some (_, rest) =>
                          sliceCursorAfter slot ptr (b0 :: b1 :: bs2) rest
                        | none =>
                          ⌜sf.readReg64 .x1 ≠ 0#64⌝ ∗
                            decodeErrorAtStackLen A (sf.readReg64 .x1) 0 ∗
                            memRegion slot 16 ∗ ptr ↦ₛ (b0 :: b1 :: bs2)) ∗ R) ∧
                sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
            (fun sf P_f => sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R) by
          by_cases h11 : 11 ≤ (b0 :: b1 :: bs2).length
          · have hhi := ult_10_of_ge_11 h11 h
            apply Prost.SepWPp.of_sepWP_inv (mid := entry + 88#64) hfl1 hsym1
            conv => arg 4; rw [pointsToBytes_cons]
            wp_steps
            wp_reach
            exact hjoin
          · rcases hpre with h11' | ⟨hne, hlast⟩
            · exact (h11 h11').elim
            · have hhi := ult_10_of_lt_11 h11 h
              have hbit_last := VarintSliceBits.getLsbD_7_beq_of_le hlast
              apply Prost.SepWPp.of_sepWP_inv (mid := entry + 84#64) hfl1 hsym1
              conv => arg 4; rw [← pointsToBytes_cons, pointsToBytes_split_last ptr (b0 :: b1 :: bs2) hne h]
              wp_steps
              conv => arg 4; rw [← pointsToBytes_split_last ptr (b0 :: b1 :: bs2) hne h, pointsToBytes_cons, pointsToBytes_cons]
              wp_reach
              intro hfl2 hsym2
              apply Prost.SepWPp.of_sepWP_inv (mid := entry + 88#64) hfl2 hsym2
              wp_steps
              wp_reach
              exact hjoin
        intro hfl2 hsym2
        by_cases hnone : decodeVarint (b0 :: b1 :: bs2) = none
        · obtain ⟨b0', b1', b2, b3, b4, b5, b6, b7, b8, b9, rest, heq,
            hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9⟩ := decodeVarint_eq_none_of_pre hpre hnone
          cases heq
          rw [hnone]; dsimp only
          have hbit1 := VarintSliceBits.getLsbD_7_beq_of_gt hb1
          have hbit2 := VarintSliceBits.getLsbD_7_beq_of_gt hb2
          have hbit3 := VarintSliceBits.getLsbD_7_beq_of_gt hb3
          have hbit4 := VarintSliceBits.getLsbD_7_beq_of_gt hb4
          have hbit5 := VarintSliceBits.getLsbD_7_beq_of_gt hb5
          have hbit6 := VarintSliceBits.getLsbD_7_beq_of_gt hb6
          have hbit7 := VarintSliceBits.getLsbD_7_beq_of_gt hb7
          have hbit8 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_gt hb8
          have hovf2 := ovf_byte2 hb0 hb1
          have hovf3 := ovf_byte3 hb0 hb1 hb2
          have hovf4 := VarintSliceBits.ovf_byte4_zext hb0 hb1 hb2 hb3
          have hovf6 := ovf_byte6 hb4 hb5
          have hovf7 := ovf_byte7 hb4 hb5 hb6
          have hovf8 := VarintSliceBits.ovf_byte8_zext hb4 hb5 hb6 hb7
          have hb9_ult := byte9_ult1_of_ge hb9
          have hb9_ule := byte9_ule_of_ge hb9
          apply Prost.SepWPp.of_sepWP_inv (mid := entry + bv% ((2^64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]") % 2^64)) hfl2 hsym2
          conv => arg 4; simp only [pointsToBytes_cons]
          wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: rest).length)) (by sep_focus)
          conv => arg 4; rw [stackAt_slowX_eq_errorHookX (s0.sp - 64#64)]
          wp_reach
          intro hfl3 hsym3
          refine Prost.SepWPp.call_frame_inv (x := (s0.sp - 64#64, 0x8000000000000001#64))
            (ret_pc := entry + 460#64) hFromCall hfl3 hsym3
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
            (by simp only [arm64_norm])
            (by simp only [arm64_norm]; rfl)
            (⟨rfl, by decide⟩ : s0.sp - 64#64 = s0.sp - 64#64 ∧ KindNoHeap 0x8000000000000001#64)
            (by sep_focus)
            (fun _ _ _ _ hex => allowPanic_not_exited hex)
            (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
          intro sm hpcm hrunm hspm hcsm _ _
          simp only [CalleeSavedPreserved, arm64_norm] at hcsm
          rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
          apply SepWPp.of_sepWP_ret
          conv => arg 4; simp only [memRegion_48_split, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
          apply SepWP.exists_elim; intro v_err
          apply SepWP.fold (stackAt_errorHookX_entails_slowX s0.sp) (by sep_focus)
          wp_steps
          apply SepWP.done
          · simp only [arm64_norm]
          · simp only [arm64_norm, hrunm]
          · refine ⟨?_, by simp only [arm64_norm], ?_⟩
            · intro hm_final
              simp only [pointsToBytes_cons, sepExists_sepConj_left, arm64_norm] at hm_final ⊢
              rcases hm_final with ⟨⟨hx0_ne, htr⟩, hm_final⟩
              refine ⟨s0.readReg64 (Reg.gpr 30#5), s0.readReg64 (Reg.gpr 29#5), v_err, ⟨htr, hx0_ne⟩, ?_⟩
              arm64_sep_close
            · simp only [CalleeSavedPreserved, arm64_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
        · apply SepWPp.of_sepWP_ret
          wp_steps 4
          by_cases hb1 : b1 ≤ 0x7f#8
          · have hbit1 := VarintSliceBits.getLsbD_7_beq_of_le hb1
            rw [decodeVarint_2 bs2 hb0 hb1]
            dsimp only
            rw [sliceCursorAfter_of_eq (k := 2) rfl]
            wp_steps
            conv => arg 4; simp only [← pointsToBytes_cons]
            wp_done
          · have hbit1 := VarintSliceBits.getLsbD_7_beq_of_gt hb1
            have hovf2 := ovf_byte2 hb0 hb1
            obtain ⟨b2, bs3, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1]) hpre (by simp)
              (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                hb0, hb1, not_false_eq_true, and_self])
            conv => arg 4; rw [pointsToBytes_cons]
            wp_steps 7
            by_cases hb2 : b2 ≤ 0x7f#8
            · have hbit2 := VarintSliceBits.getLsbD_7_beq_of_le hb2
              rw [decodeVarint_3 bs3 hb0 hb1 hb2]
              dsimp only
              rw [sliceCursorAfter_of_eq (k := 3) rfl]
              wp_steps
              conv => arg 4; simp only [← pointsToBytes_cons]
              wp_done
            · have hbit2 := VarintSliceBits.getLsbD_7_beq_of_gt hb2
              have hovf3 := ovf_byte3 hb0 hb1 hb2
              obtain ⟨b3, bs4, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2]) hpre (by simp)
                (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                  hb0, hb1, hb2, not_false_eq_true, and_self])
              conv => arg 4; rw [pointsToBytes_cons]
              wp_steps 7
              by_cases hb3 : b3 ≤ 0x7f#8
              · have hbit3 := VarintSliceBits.getLsbD_7_beq_of_le hb3
                rw [decodeVarint_4 bs4 hb0 hb1 hb2 hb3]
                dsimp only
                rw [sliceCursorAfter_of_eq (k := 4) rfl]
                wp_steps
                conv => arg 4; simp only [← pointsToBytes_cons]
                wp_done
              · have hbit3 := VarintSliceBits.getLsbD_7_beq_of_gt hb3
                have hovf4 := VarintSliceBits.ovf_byte4_zext hb0 hb1 hb2 hb3
                obtain ⟨b4, bs5, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3]) hpre (by simp)
                  (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                    hb0, hb1, hb2, hb3, not_false_eq_true, and_self])
                conv => arg 4; rw [pointsToBytes_cons]
                wp_steps 7
                by_cases hb4 : b4 ≤ 0x7f#8
                · have hbit4 := VarintSliceBits.getLsbD_7_beq_of_le hb4
                  rw [decodeVarint_5 bs5 hb0 hb1 hb2 hb3 hb4]
                  dsimp only
                  rw [sliceCursorAfter_of_eq (k := 5) rfl]
                  wp_steps
                  conv => arg 4; simp only [← pointsToBytes_cons]
                  wp_done
                · have hbit4 := VarintSliceBits.getLsbD_7_beq_of_gt hb4
                  obtain ⟨b5, bs6, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4]) hpre (by simp)
                    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                      hb0, hb1, hb2, hb3, hb4, not_false_eq_true, and_self])
                  conv => arg 4; rw [pointsToBytes_cons]
                  wp_steps 5
                  by_cases hb5 : b5 ≤ 0x7f#8
                  · have hbit5 := VarintSliceBits.getLsbD_7_beq_of_le hb5
                    rw [decodeVarint_6 bs6 hb0 hb1 hb2 hb3 hb4 hb5]
                    dsimp only
                    rw [sliceCursorAfter_of_eq (k := 6) rfl]
                    wp_steps
                    conv => arg 4; simp only [← pointsToBytes_cons]
                    wp_done
                  · have hbit5 := VarintSliceBits.getLsbD_7_beq_of_gt hb5
                    have hovf6 := ovf_byte6 hb4 hb5
                    obtain ⟨b6, bs7, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4, b5]) hpre
                      (by simp) (by simp only [List.mem_cons, List.not_mem_nil, or_false,
                        forall_eq_or_imp, forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, not_false_eq_true,
                        and_self])
                    conv => arg 4; rw [pointsToBytes_cons]
                    wp_steps 7
                    by_cases hb6 : b6 ≤ 0x7f#8
                    · have hbit6 := VarintSliceBits.getLsbD_7_beq_of_le hb6
                      rw [decodeVarint_7 bs7 hb0 hb1 hb2 hb3 hb4 hb5 hb6]
                      dsimp only
                      rw [sliceCursorAfter_of_eq (k := 7) rfl]
                      wp_steps
                      conv => arg 4; simp only [← pointsToBytes_cons]
                      wp_done
                    · have hbit6 := VarintSliceBits.getLsbD_7_beq_of_gt hb6
                      have hovf7 := ovf_byte7 hb4 hb5 hb6
                      obtain ⟨b7, bs8, rfl⟩ := exists_cons_of_all_gt
                        (pre := [b0, b1, b2, b3, b4, b5, b6]) hpre (by simp)
                        (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                          forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, not_false_eq_true, and_self])
                      conv => arg 4; rw [pointsToBytes_cons]
                      wp_steps 7
                      by_cases hb7 : b7 ≤ 0x7f#8
                      · have hbit7 := VarintSliceBits.getLsbD_7_beq_of_le hb7
                        rw [decodeVarint_8 bs8 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7]
                        dsimp only
                        rw [sliceCursorAfter_of_eq (k := 8) rfl]
                        wp_steps
                        conv => arg 4; simp only [← pointsToBytes_cons]
                        wp_done
                      · have hbit7 := VarintSliceBits.getLsbD_7_beq_of_gt hb7
                        have hovf8 := VarintSliceBits.ovf_byte8_zext hb4 hb5 hb6 hb7
                        obtain ⟨b8, bs9, rfl⟩ := exists_cons_of_all_gt
                          (pre := [b0, b1, b2, b3, b4, b5, b6, b7]) hpre (by simp)
                          (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                            forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, not_false_eq_true,
                            and_self])
                        conv => arg 4; rw [pointsToBytes_cons]
                        wp_steps 7
                        by_cases hb8 : b8 ≤ 0x7f#8
                        · have hbit8 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_le hb8
                          rw [decodeVarint_9 bs9 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8]
                          dsimp only
                          rw [sliceCursorAfter_of_eq (k := 9) rfl]
                          wp_steps
                          conv => arg 4; simp only [← pointsToBytes_cons]
                          wp_done
                        · have hbit8 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_gt hb8
                          obtain ⟨b9, bs10, rfl⟩ := exists_cons_of_all_gt
                            (pre := [b0, b1, b2, b3, b4, b5, b6, b7, b8]) hpre (by simp)
                            (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                              forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, not_false_eq_true,
                              and_self])
                          have hb9 : ¬ 2#8 ≤ b9 := by
                            intro hge
                            apply hnone
                            rw [decodeVarint]; iterate 10 rw [decodeVarintAux]
                            by_cases hb9_le : b9 ≤ 0x7f#8 <;>
                              simp [toNat_le_0x7f_iff, two_le_toNat_iff, hb0, hb1, hb2, hb3, hb4, hb5,
                                hb6, hb7, hb8, hb9_le, hge]
                          have hb9_ult := byte9_ult1_of_lt hb9
                          have hb9_ule := byte9_ule_of_lt hb9
                          have hovf10 := ovf_byte10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
                          conv => arg 4; rw [pointsToBytes_cons]
                          rw [decodeVarint_10 bs10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9]
                          dsimp only
                          rw [sliceCursorAfter_of_eq (k := 10) rfl]
                          wp_steps
                          conv => arg 4; simp only [← pointsToBytes_cons]
                          wp_done
      · have h11 : ¬ 11 ≤ (b0 :: bs1).length := fun h => hpre (Or.inl h)
        have hne : b0 :: bs1 ≠ [] := List.cons_ne_nil b0 bs1
        have hlast : ¬ (b0 :: bs1).getLast hne ≤ 0x7f#8 := fun h => hpre (Or.inr ⟨hne, h⟩)
        have hhi := ult_10_of_lt_11 h11 h
        have hbit_last := VarintSliceBits.getLsbD_7_beq_of_gt hlast
        apply Prost.SepWPp.of_sepWP_inv (mid := entry + bv% ((2^64 + ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]")) % 2^64)) hfl1 hsym1
        conv => arg 4; rw [← pointsToBytes_cons, pointsToBytes_split_last ptr (b0 :: bs1) hne h]
        wp_steps
        conv => arg 4; rw [← pointsToBytes_split_last ptr (b0 :: bs1) hne h]
        wp_reach
        intro hfl2 hsym2
        refine Prost.SepWPp.call_frame_inv (x := ⟨bufRef, slot, ptr, b0 :: bs1⟩)
          (ret_pc := entry + 484#64) hSlowCall hfl2 hsym2
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
          (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
          (by simp only [arm64_norm])
          (by simp only [arm64_norm]; rfl)
          (⟨by simp only [arm64_norm, h_1], h⟩ : _ ∧ (b0 :: bs1).length < 2 ^ 63)
          (by simp only [sliceCursorAt]; sep_focus)
          (fun _ _ _ _ hex => allowPanic_not_exited hex)
          (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
        intro sm hpcm hrunm hspm hcsm _ _
        simp only [CalleeSavedPreserved, arm64_norm] at hcsm
        rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
        apply SepWPp.of_sepWP_ret
        cases hd : decodeVarint (b0 :: bs1) with
        | none =>
          dsimp only
          conv => arg 4; simp only [hd, sepConj_assoc, arm64_norm]
          apply SepWP.pure_elim; intro hsm0
          wp_steps
          wp_done
        | some p =>
          rcases p with ⟨v, rest⟩
          dsimp only
          conv => arg 4; simp only [hd, sepConj_assoc, arm64_norm]
          apply SepWP.pure_elim; rintro ⟨hsm0, hsm1⟩
          wp_steps
          wp_done

theorem _root_.CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2_ok_ext_x {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsX img C A encFn decFn ext) :
    CryptoVerification.CliC.SpqrV1.Varint.DecodeVarint2OkExtX img A ext := by
  refine CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2_ok_of_contracts_x ?_ ?_
  · rw [CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2_add_from_eq_fnAddr]
    exact hC.decode_error_from
  · rw [CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2_add_slow_eq_fnAddr]
    exact decodeVarintSlowX_ok_at_ext hC (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>")
      (k := 0) (by simp only [Nat.add_zero])

end CryptoVerification.SpqrV1.Varint
