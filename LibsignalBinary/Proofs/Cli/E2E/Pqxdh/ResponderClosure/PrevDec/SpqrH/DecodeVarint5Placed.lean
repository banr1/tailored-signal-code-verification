/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymA
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeErrorFromX
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp

/-!
# Placed Handshake `decode_varint [local#4]` Verification

Verifies `[LibsignalPlacement]` `prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]`
(Block `515`) against `decodeVarint2SpecX` from `AllocContractsPlaced`, with cross-block lifting to
`lsProg_518`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.VarintBridge
open CryptoVerification.CodeLayout
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.CliHandshake.Placed
open Proofs.libsignal.Stage1X

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Relocatable `[LibsignalPlacement]` contract for
`prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]`
(Block `515`, `(blkPl_515).base = lsmpl.base 515`) on `lsProg_518 ext`. -/
def DecodeVarint5PlacedOkExtX [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 515)
    (withLsCl lsmpl (decodeVarint2SpecX A))

/-! ## Split join helpers at `(blkPl_515).base + 88#64` -/

private abbrev dv5PlJoinState (s0 : State) (slot ptr : BitVec 64)
    (b0 b1 : BitVec 8) (bs2 : List (BitVec 8)) (entry : BitVec 64) (m : Memory) : State :=
  ((((((((s0.writeReg64 Reg.sp (s0.sp - 64#64)).writeReg64 (Reg.gpr 29#5) (s0.sp - 16#64)).writeReg64
      (Reg.gpr 8#5) slot).writeReg64 (Reg.gpr 9#5)
      (BitVec.ofNat 64 (b0 :: b1 :: bs2).length)).writeReg64 (Reg.gpr 10#5) ptr).writeReg64
      (Reg.gpr 1#5) (BitVec.signExtend 64 b0)).writeReg64
      (Reg.gpr 11#5) (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 b1)))).setPState
      (subsPState64 (BitVec.ofNat 64 (b0 :: b1 :: bs2).length) 10#64)
    |>.setPC (entry + 88#64) |>.setMem m)

private abbrev dv5PlJoinPre (A : RustAlloc) (s0 : State) (bufRef slot ptr v_stk_2 : BitVec 64)
    (b0 b1 : BitVec 8) (bs2 : List (BitVec 8)) : SepProp :=
  bufRef ↦₆₄ slot ∗ slot ↦₆₄ ptr ∗
    (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (b0 :: b1 :: bs2).length ∗
    (ptr ↦₈ b0 ∗ ((ptr + 1#64) ↦₈ b1 ∗ (ptr + 1#64 + 1#64) ↦ₛ bs2)) ∗ A.pool ∗
    stackAt (s0.sp - 64#64) decodeVarintSlowStackX ∗ memRegion (s0.sp - 56#64) 40 ∗
    (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗
    (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
    (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)

private abbrev dv5PlJoinPost (A : RustAlloc) (s0 : State) (bufRef slot ptr : BitVec 64)
    (b0 b1 : BitVec 8) (bs2 : List (BitVec 8)) (R : SepProp) :
    State → SepProp → Prop := fun sf P_f =>
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
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

private abbrev dv5PlJoinPanic (s0 : State) (R : SepProp) :
    State → SepProp → Prop := fun sf P_f =>
  sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R

set_option maxHeartbeats 1600000 in
private theorem decodeVarint5_placed_join_none_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hFromCall : subroutine_ok (lsProg_515 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpecWithStack A decodeErrorHookStackX)))
    (s0 : State) (hrun : s0.status = .Running) (hsp_align : s0.spAligned)
    (bufRef slot ptr v_stk_2 : BitVec 64) (m : Memory) (R : SepProp)
    (b0 b1 : BitVec 8) (bs2 : List (BitVec 8))
    (hpre : VarintSlicePre (b0 :: b1 :: bs2))
    (hnone : decodeVarint (b0 :: b1 :: bs2) = none)
    (hcl_join : LibsignalCodeLoaded lsmpl m) :
    SepWPp (lsProg_515 H) (s0.readReg64 Reg.lr)
      (dv5PlJoinState s0 slot ptr b0 b1 bs2 (blkPl_515).base m)
      (dv5PlJoinPre A s0 bufRef slot ptr v_stk_2 b0 b1 bs2)
      (dv5PlJoinPost A s0 bufRef slot ptr b0 b1 bs2 R)
      (dv5PlJoinPanic s0 R) := by
  unfold dv5PlJoinPost dv5PlJoinPanic
  dsimp only [dv5PlJoinState, dv5PlJoinPre]
  obtain ⟨b0', b1', b2, b3, b4, b5, b6, b7, b8, b9, rest, heq,
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
  apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl_join
  conv => arg 4; simp only [pointsToBytes_cons]
  wp_steps
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr
    (BitVec.ofNat 64 (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: rest).length)) (by sep_focus)
  conv => arg 4; rw [stackAt_slowX_eq_errorHookX (s0.sp - 64#64)]
  wp_reach
  intro hcl_err
  refine SepWPp.call_frame_lscl (spec := decodeErrorFromSpecWithStack A decodeErrorHookStackX)
    (x := (s0.sp - 64#64, 0x8000000000000001#64))
    (ret_pc := (blkPl_515).base + 460#64) hFromCall hcl_err
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [decodeErrorFromSpecWithStack, arm64_norm]; rfl)
    (⟨rfl, by decide⟩ : s0.sp - 64#64 = s0.sp - 64#64 ∧ KindNoHeap 0x8000000000000001#64)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm _hcl_post
  simp only [CalleeSavedPreserved, arm64_norm] at hcsm
  rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
  apply SepWPp.of_sepWP_ret
  conv => arg 4; simp only [decodeErrorFromSpecWithStack, memRegion_48_split, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
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

set_option maxHeartbeats 800000 in
private theorem decodeVarint5_placed_join_2_to_5_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (s0 : State) (hrun : s0.status = .Running) (hsp_align : s0.spAligned)
    (bufRef slot ptr v_stk_2 : BitVec 64) (m : Memory) (R : SepProp)
    (b0 b1 : BitVec 8) (bs2 : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8)
    (hpre : VarintSlicePre (b0 :: b1 :: bs2))
    (h25 : b1 ≤ 0x7f#8 ∨ ∃ b2 bs3, bs2 = b2 :: bs3 ∧
      (b2 ≤ 0x7f#8 ∨ ∃ b3 bs4, bs3 = b3 :: bs4 ∧
        (b3 ≤ 0x7f#8 ∨ ∃ b4 bs5, bs4 = b4 :: bs5 ∧ b4 ≤ 0x7f#8))) :
    SepWPp (lsProg_515 H) (s0.readReg64 Reg.lr)
      (dv5PlJoinState s0 slot ptr b0 b1 bs2 (blkPl_515).base m)
      (dv5PlJoinPre A s0 bufRef slot ptr v_stk_2 b0 b1 bs2)
      (dv5PlJoinPost A s0 bufRef slot ptr b0 b1 bs2 R)
      (dv5PlJoinPanic s0 R) := by
  unfold dv5PlJoinPost dv5PlJoinPanic
  dsimp only [dv5PlJoinState, dv5PlJoinPre]
  apply SepWPp.of_sepWP_ret
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
        · exfalso
          rcases h25 with h1 | ⟨b2', bs3', hcons2, h2 | ⟨b3', bs4', hcons3, h3 | ⟨b4', bs5', hcons4, h4⟩⟩⟩
          · exact hb1 h1
          · cases hcons2; exact hb2 h2
          · cases hcons2; cases hcons3; exact hb3 h3
          · cases hcons2; cases hcons3; cases hcons4; exact hb4 h4

set_option maxHeartbeats 800000 in
private theorem decodeVarint5_placed_join_6_to_10_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (s0 : State) (hrun : s0.status = .Running) (hsp_align : s0.spAligned)
    (bufRef slot ptr v_stk_2 : BitVec 64) (m : Memory) (R : SepProp)
    (b0 b1 b2 b3 b4 : BitVec 8) (bs5 : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8)
    (hpre : VarintSlicePre (b0 :: b1 :: b2 :: b3 :: b4 :: bs5))
    (hnone : ¬ decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: bs5) = none) :
    SepWPp (lsProg_515 H) (s0.readReg64 Reg.lr)
      (dv5PlJoinState s0 slot ptr b0 b1 (b2 :: b3 :: b4 :: bs5) (blkPl_515).base m)
      (dv5PlJoinPre A s0 bufRef slot ptr v_stk_2 b0 b1 (b2 :: b3 :: b4 :: bs5))
      (dv5PlJoinPost A s0 bufRef slot ptr b0 b1 (b2 :: b3 :: b4 :: bs5) R)
      (dv5PlJoinPanic s0 R) := by
  unfold dv5PlJoinPost dv5PlJoinPanic
  dsimp only [dv5PlJoinState, dv5PlJoinPre]
  apply SepWPp.of_sepWP_ret
  have hbit1 := VarintSliceBits.getLsbD_7_beq_of_gt hb1
  have hovf2 := ovf_byte2 hb0 hb1
  have hbit2 := VarintSliceBits.getLsbD_7_beq_of_gt hb2
  have hovf3 := ovf_byte3 hb0 hb1 hb2
  have hbit3 := VarintSliceBits.getLsbD_7_beq_of_gt hb3
  have hovf4 := VarintSliceBits.ovf_byte4_zext hb0 hb1 hb2 hb3
  have hbit4 := VarintSliceBits.getLsbD_7_beq_of_gt hb4
  obtain ⟨b5, bs6, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4]) hpre (by simp)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      hb0, hb1, hb2, hb3, hb4, not_false_eq_true, and_self])
  wp_steps 4
  conv => arg 4; rw [pointsToBytes_cons]
  wp_steps 7
  conv => arg 4; rw [pointsToBytes_cons]
  wp_steps 7
  conv => arg 4; rw [pointsToBytes_cons]
  wp_steps 7
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

/-! ## Top-level verification of `decode_varint::<&mut &[u8]> [local#4]` (Block `515`) -/

set_option maxHeartbeats 800000 in
theorem decodeVarint5_placed_ok_of_contracts_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H) (blkPl_261).base
      (withLsCodeLoaded lsmpl (decodeErrorFromSpecWithStack A decodeErrorHookStackX)))
    (hSlow : subroutine_ok ((blkPC_293).rebase (blkPl_293).base H) (blkPl_293).base
      (withLsCodeLoaded lsmpl (Prost.decodeVarintSlowSpecX A))) :
    subroutine_ok (lsProg_515 H) (blkPl_515).base
      (withLsCodeLoaded lsmpl (decodeVarint2SpecX A)) := by
  have hFromCall : subroutine_ok (lsProg_515 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpecWithStack A decodeErrorHookStackX)) :=
    ls_subroutine_ok_cl_of_block (callerProg := lsProg_515 H) hFrom
  have hSlowCall : subroutine_ok (lsProg_515 H) (lsmpl.base 293)
      (withLsCl lsmpl (Prost.decodeVarintSlowSpecX A)) :=
    ls_subroutine_ok_cl_of_block (callerProg := lsProg_515 H) hSlow
  clear hFrom hSlow
  have hjoin_dispatch : ∀ (s0 : State) (_hrun : s0.status = .Running) (_hsp_align : s0.spAligned)
      (bufRef slot ptr v_stk_2 : BitVec 64) (m : Memory) (R : SepProp)
      (b0 b1 : BitVec 8) (bs2 : List (BitVec 8)),
      ¬ b0 ≤ 0x7f#8 →
      VarintSlicePre (b0 :: b1 :: bs2) →
      LibsignalCodeLoaded lsmpl m →
      SepWPp (lsProg_515 H) (s0.readReg64 Reg.lr)
        (dv5PlJoinState s0 slot ptr b0 b1 bs2 (blkPl_515).base m)
        (dv5PlJoinPre A s0 bufRef slot ptr v_stk_2 b0 b1 bs2)
        (dv5PlJoinPost A s0 bufRef slot ptr b0 b1 bs2 R)
        (dv5PlJoinPanic s0 R) := by
    intro s0 hrun hsp_align bufRef slot ptr v_stk_2 m R b0 b1 bs2 hb0 hpre hcl_join
    by_cases hnone : decodeVarint (b0 :: b1 :: bs2) = none
    · exact decodeVarint5_placed_join_none_x hFromCall s0 hrun hsp_align bufRef slot ptr v_stk_2 m R
        b0 b1 bs2 hpre hnone hcl_join
    · by_cases h25 : b1 ≤ 0x7f#8 ∨ ∃ b2 bs3, bs2 = b2 :: bs3 ∧
          (b2 ≤ 0x7f#8 ∨ ∃ b3 bs4, bs3 = b3 :: bs4 ∧
            (b3 ≤ 0x7f#8 ∨ ∃ b4 bs5, bs4 = b4 :: bs5 ∧ b4 ≤ 0x7f#8))
      · exact decodeVarint5_placed_join_2_to_5_x s0 hrun hsp_align bufRef slot ptr v_stk_2 m R
          b0 b1 bs2 hb0 hpre h25
      · have hb1 : ¬ b1 ≤ 0x7f#8 := fun h => h25 (Or.inl h)
        obtain ⟨b2, bs3, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1]) hpre (by simp)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
            hb0, hb1, not_false_eq_true, and_self])
        have hb2 : ¬ b2 ≤ 0x7f#8 := fun h => h25 (Or.inr ⟨b2, bs3, rfl, Or.inl h⟩)
        obtain ⟨b3, bs4, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2]) hpre (by simp)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
            hb0, hb1, hb2, not_false_eq_true, and_self])
        have hb3 : ¬ b3 ≤ 0x7f#8 :=
          fun h => h25 (Or.inr ⟨b2, b3 :: bs4, rfl, Or.inr ⟨b3, bs4, rfl, Or.inl h⟩⟩)
        obtain ⟨b4, bs5, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3]) hpre (by simp)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
            hb0, hb1, hb2, hb3, not_false_eq_true, and_self])
        have hb4 : ¬ b4 ≤ 0x7f#8 := fun h =>
          h25 (Or.inr ⟨b2, b3 :: b4 :: bs5, rfl, Or.inr ⟨b3, b4 :: bs5, rfl, Or.inr ⟨b4, bs5, rfl, h⟩⟩⟩)
        exact decodeVarint5_placed_join_6_to_10_x s0 hrun hsp_align bufRef slot ptr v_stk_2 m R
          b0 b1 b2 b3 b4 bs5 hb0 hb1 hb2 hb3 hb4 hpre hnone
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold decodeVarint2SpecX
    simp only [sliceCursorAt, stackAt_decodeVarint2X, sepExists_sepConj_left, sepExists_sepConj_right]
  dsimp only [dv5PlJoinState, dv5PlJoinPre, dv5PlJoinPost, dv5PlJoinPanic] at hjoin_dispatch
  wpp_init x s0
  obtain ⟨bufRef, slot, ptr, bs⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hlen_lt : bs.length < 2 ^ 63 := by assumption
  have hx0_slot : s0.readReg64 (Reg.gpr 0#5) = bufRef := by assumption
  cases bs with
  | nil =>
    have hd_nil : decodeVarint ([] : List (BitVec 8)) = none := rfl
    rw [hd_nil]
    dsimp only
    apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl0
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 [].length)) (by sep_focus)
    conv => arg 4; rw [stackAt_slowX_eq_errorHookX (s0.sp - 64#64)]
    wp_reach
    intro hcl1
    refine SepWPp.call_frame_lscl (spec := decodeErrorFromSpecWithStack A decodeErrorHookStackX)
      (x := (s0.sp - 64#64, 0x8000000000000001#64))
      (ret_pc := (blkPl_515).base + 460#64) hFromCall hcl1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [decodeErrorFromSpecWithStack, arm64_norm]; rfl)
      (⟨rfl, by decide⟩ : s0.sp - 64#64 = s0.sp - 64#64 ∧ KindNoHeap 0x8000000000000001#64)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm _hcl2
    simp only [CalleeSavedPreserved, arm64_norm] at hcsm
    rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
    apply SepWPp.of_sepWP_ret
    conv => arg 4; simp only [decodeErrorFromSpecWithStack, memRegion_48_split, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
    apply SepWP.exists_elim; intro v_err
    apply SepWP.fold (stackAt_errorHookX_entails_slowX s0.sp) (by sep_focus)
    wp_steps
    wp_done
  | cons b0 bs1 =>
    have hcbz := cbz_len_cons_false hlen_lt
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
      apply SepWPp.of_sepWP_lscl (mid := (blkPl_515).base + 64#64) hcl0
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps
      wp_reach
      intro hcl1
      by_cases hpre : VarintSlicePre (b0 :: bs1)
      · obtain ⟨b1, bs2, rfl⟩ := exists_cons_of_all_gt (pre := [b0]) hpre (by simp)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, hb0, not_false_eq_true])
        by_cases h11 : 11 ≤ (b0 :: b1 :: bs2).length
        · have hhi := ult_10_of_ge_11 h11 hlen_lt
          apply SepWPp.of_sepWP_lscl (mid := (blkPl_515).base + 88#64) hcl1
          conv => arg 4; rw [pointsToBytes_cons]
          wp_steps
          wp_reach
          intro hcl2
          conv => arg 4; simp only [arm64_norm]
          exact hjoin_dispatch s0 hrun hsp_align bufRef slot ptr v_stk_2 _ R b0 b1 bs2 hb0 hpre
            (by simpa only [arm64_norm] using hcl2)
        · have hpre_cases := hpre
          rcases hpre_cases with h11' | ⟨hne, hlast⟩
          · exact (h11 h11').elim
          · have hhi := ult_10_of_lt_11 h11 hlen_lt
            have hbit_last := VarintSliceBits.getLsbD_7_beq_of_le hlast
            apply SepWPp.of_sepWP_lscl (mid := (blkPl_515).base + 84#64) hcl1
            conv => arg 4; rw [← pointsToBytes_cons, pointsToBytes_split_last ptr (b0 :: b1 :: bs2) hne hlen_lt]
            wp_steps
            conv => arg 4; rw [← pointsToBytes_split_last ptr (b0 :: b1 :: bs2) hne hlen_lt, pointsToBytes_cons, pointsToBytes_cons]
            wp_reach
            intro hcl2
            apply SepWPp.of_sepWP_lscl (mid := (blkPl_515).base + 88#64) hcl2
            wp_steps
            wp_reach
            intro hcl3
            conv => arg 4; simp only [arm64_norm]
            exact hjoin_dispatch s0 hrun hsp_align bufRef slot ptr v_stk_2 _ R b0 b1 bs2 hb0 hpre
              (by simpa only [arm64_norm] using hcl3)
      · have h11 : ¬ 11 ≤ (b0 :: bs1).length := fun h => hpre (Or.inl h)
        have hne : b0 :: bs1 ≠ [] := List.cons_ne_nil b0 bs1
        have hlast : ¬ (b0 :: bs1).getLast hne ≤ 0x7f#8 := fun h => hpre (Or.inr ⟨hne, h⟩)
        have hhi := ult_10_of_lt_11 h11 hlen_lt
        have hbit_last := VarintSliceBits.getLsbD_7_beq_of_gt hlast
        apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 293) hcl1
        conv => arg 4; rw [← pointsToBytes_cons, pointsToBytes_split_last ptr (b0 :: bs1) hne hlen_lt]
        wp_steps
        conv => arg 4; rw [← pointsToBytes_split_last ptr (b0 :: bs1) hne hlen_lt]
        wp_reach
        intro hcl_slow
        refine SepWPp.call_frame_lscl (spec := Prost.decodeVarintSlowSpecX A)
          (x := ⟨bufRef, slot, ptr, b0 :: bs1⟩)
          (ret_pc := (blkPl_515).base + 484#64) hSlowCall hcl_slow
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
          (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
          (by simp only [arm64_norm])
          (by simp only [Prost.decodeVarintSlowSpecX, decodeVarintSlowSpecGen, arm64_norm]; rfl)
          (⟨by simp only [arm64_norm, hx0_slot], hlen_lt⟩ : _ ∧ (b0 :: bs1).length < 2 ^ 63)
          (by simp only [sliceCursorAt]; sep_focus)
          (fun _ _ _ _ hex => allowPanic_not_exited hex)
          (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
        intro sm hpcm hrunm hspm hcsm _hcl_post
        simp only [CalleeSavedPreserved, arm64_norm] at hcsm
        rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
        apply SepWPp.of_sepWP_ret
        cases hd : decodeVarint (b0 :: bs1) with
        | none =>
          dsimp only
          conv => arg 4; simp only [Prost.decodeVarintSlowSpecX, decodeVarintSlowSpecGen, hd, sepConj_assoc, arm64_norm]
          apply SepWP.pure_elim; intro hsm0
          wp_steps
          wp_done
        | some p =>
          rcases p with ⟨v, rest⟩
          dsimp only
          conv => arg 4; simp only [Prost.decodeVarintSlowSpecX, decodeVarintSlowSpecGen, hd, sepConj_assoc, arm64_norm]
          apply SepWP.pure_elim; rintro ⟨hsm0, hsm1⟩
          wp_steps
          wp_done

/-- `withLsCodeLoaded pl (decodeErrorFromSpecWithStack A s1)` entails the same spec at any
larger budget `s2 ≤ 2^64`. -/
theorem decodeErrorFromSpecWithStack_lscl_le {pl : Obj.MultiPlacement} {P : Program}
    {addr : BitVec 64} {A : RustAlloc} {s1 s2 : Nat}
    (h : subroutine_ok P addr (withLsCodeLoaded pl (decodeErrorFromSpecWithStack A s1)))
    (hle : s1 ≤ s2 := by decide) (hmax : s2 ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (withLsCodeLoaded pl (decodeErrorFromSpecWithStack A s2)) := by
  refine subroutine_ok_map_panic h fun ⟨k, w⟩ R s0 hpre => ?_
  have hsplit : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h1 := stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  refine ⟨(k, w), memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R, ?_, ?_,
    fun sf hp => Satisfies.mono (by
      dsimp only [withLsCodeLoaded, decodeErrorFromSpecWithStack]
      rw [sepConj_assoc _ anyHeap _, ← sepConj_assoc anyHeap _ R, sepConj_assoc _ anyHeap R]
      exact sepConj_mono_right (sepConj_mono_left (entails_anyHeap _))) hp⟩
  · dsimp only [withLsCodeLoaded, decodeErrorFromSpecWithStack] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  · intro sf hpost
    dsimp only [withLsCodeLoaded, decodeErrorFromSpecWithStack] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢

theorem dv5_decodeErrorFrom_placed_of_alloc [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hAlloc : Proofs.libsignal.Stage1X.AllocContractsPlaced A H) :
    subroutine_ok ((blkPC_261).rebase (blkPl_261).base H) (blkPl_261).base
      (withLsCodeLoaded lsmpl (decodeErrorFromSpecWithStack A decodeErrorHookStackX)) :=
  decodeErrorFromSpecWithStack_lscl_le
    (s1 := CryptoVerification.LibsignalTripleRatchet.Prost.X.decodeErrorHookStackW)
    (s2 := decodeErrorHookStackX)
    (CryptoVerification.LibsignalTripleRatchet.Prost.X.decodeErrorFrom_placed_okW hAlloc)

theorem dv5_decodeVarintSlow_placed_of_alloc [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hAlloc : Proofs.libsignal.Stage1X.AllocContractsPlaced A H) :
    subroutine_ok ((blkPC_293).rebase (blkPl_293).base H) (blkPl_293).base
      (withLsCodeLoaded lsmpl (Prost.decodeVarintSlowSpecX A)) :=
  decodeVarintSlowGen_lscl_ok_of_session2
    (decode_varint_slow_placed_ok_with_stack
      (errStack := decodeErrorHookStackX) (by decide)
      (ls_subroutine_ok_cl_of_block
        (callerProg := (blkPC_293).rebase (blkPl_293).base H)
        (dv5_decodeErrorFrom_placed_of_alloc hAlloc)))

/-- `decodeVarint2SpecX` on Block `515` (`lsProg_515 H`) discharged from `AllocContractsPlaced`. -/
theorem decodeVarint5_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hAlloc : Proofs.libsignal.Stage1X.AllocContractsPlaced A H) :
    subroutine_ok (lsProg_515 H) (blkPl_515).base
      (withLsCodeLoaded lsmpl (decodeVarint2SpecX A)) :=
  decodeVarint5_placed_ok_of_contracts_x
    (dv5_decodeErrorFrom_placed_of_alloc hAlloc)
    (dv5_decodeVarintSlow_placed_of_alloc hAlloc)

theorem decodeVarint5_placed_ok_cl [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i H]
    (hAlloc : Proofs.libsignal.Stage1X.AllocContractsPlaced A H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 515)
      (withLsCl lsmpl (decodeVarint2SpecX A)) :=
  ls_subroutine_ok_cl_of_block (callerProg := callerProg) (decodeVarint5_placed_ok hAlloc) hi

theorem decodeVarint5_placed_ok_ext_x [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hAlloc : Proofs.libsignal.Stage1X.AllocContractsPlaced A ext) :
    DecodeVarint5PlacedOkExtX A ext :=
  decodeVarint5_placed_ok_cl (callerProg := lsProg_518 ext) hAlloc

alias bm6_decodeVarint5_placed_of_alloc := decodeVarint5_placed_ok

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

export SpqrH (
  DecodeVarint5PlacedOkExtX
  decodeErrorFromSpecWithStack_lscl_le
  dv5_decodeErrorFrom_placed_of_alloc
  dv5_decodeVarintSlow_placed_of_alloc
  decodeVarint5_placed_ok_of_contracts_x
  decodeVarint5_placed_ok
  decodeVarint5_placed_ok_cl
  decodeVarint5_placed_ok_ext_x
  bm6_decodeVarint5_placed_of_alloc
)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
