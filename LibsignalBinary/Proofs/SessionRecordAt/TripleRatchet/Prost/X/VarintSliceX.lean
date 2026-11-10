/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Wire.X.CalleesW
public import LibsignalBinary.Proofs.CodeLayout
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Wire.X.TryFromDefsX
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSlice
import ProofLib.SepLogic.WPp

/-!
# `prost::encoding::varint::decode_varint_slice`

Verifies `prost::encoding::varint::decode_varint_slice` (`0x23008`, block `76`) on
`contractProg img.base ext` and under `[LibsignalPlacement]` from `DecodeError::from`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet.Prost.X
open CryptoVerification.LibsignalTripleRatchet.Prost

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.WireX
open Proofs.libsignal.Stage1X

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_VarintSliceX : True := trivial

/-! ## Memory and stack layout lemmas -/

theorem stackAt_decodeVarintSliceX (sp : BitVec 64) :
    stackAt sp decodeVarintSliceStackW =
      stackAt (sp - 80#64) decodeErrorHookStackW ∗
        memRegion (sp - 80#64) 8 ∗
        memRegion (sp - 56#64) 40 ∗
        (∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
          ((sp - 72#64) ↦₆₄ v9) ∗ ((sp - 64#64) ↦₆₄ v8) ∗
          ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v1)) := by
  have h0 := stackAt_split_cells sp decodeErrorHookStackW 10 (by decide)
  rw [← memRegion_cells (sp - BitVec.ofNat 64 (8 * 10)) 10 (by decide)] at h0
  change stackAt sp decodeVarintSliceStackW =
    stackAt (sp - 80#64) decodeErrorHookStackW ∗ memRegion (sp - 80#64) 80 at h0
  have s1 := memRegion_split (sp - 80#64) 8 72 (by decide)
  rw [bv_sub_add_lit sp 80 8] at s1
  have s2 := memRegion_split (sp - 72#64) 8 64 (by decide)
  rw [bv_sub_add_lit sp 72 8] at s2
  have s3 := memRegion_split (sp - 64#64) 8 56 (by decide)
  rw [bv_sub_add_lit sp 64 8] at s3
  have s4 := memRegion_split (sp - 56#64) 40 16 (by decide)
  rw [bv_sub_add_lit sp 56 40] at s4
  have s5 := memRegion_split (sp - 16#64) 8 8 (by decide)
  rw [bv_sub_add_lit sp 16 8] at s5
  rw [h0, s1, s2, s3, s4, s5,
    memRegion_eight (sp - 72#64), memRegion_eight (sp - 64#64),
    memRegion_eight (sp - 16#64), memRegion_eight (sp - 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  ac_rfl

theorem pointsToBytes_split_lastW (ptr : BitVec 64) (bs : List (BitVec 8))
    (hne : bs ≠ []) :
    (ptr ↦ₛ bs) =
      (ptr ↦ₛ bs.dropLast) ∗
      ((ptr + BitVec.ofNat 64 bs.length - 1#64) ↦₈ bs.getLast hne) :=
  ProofLib.pointsToBytes_split_last ptr bs hne

theorem ule_11_of_geW {n : Nat} (h11 : 11 ≤ n) (_hlt : n < 2 ^ 63) :
    (11#64).ule (BitVec.ofNat 64 n) = true := by
  rw [BitVec.ule_iff_le, BitVec.le_def, BitVec.toNat_ofNat]
  change 11 ≤ n % 2 ^ 64
  omega

theorem ule_11_of_ltW {n : Nat} (h11 : ¬ 11 ≤ n) (_hlt : n < 2 ^ 63) :
    (11#64).ule (BitVec.ofNat 64 n) = false := by
  rw [Bool.eq_false_iff, ne_eq, BitVec.ule_iff_le, BitVec.le_def, BitVec.toNat_ofNat]
  change ¬ 11 ≤ n % 2 ^ 64
  omega

open Lean Elab Tactic Meta in
local elab "wp_ret8_bv_bits " retStx:term:max ppSpace targetVal:term : tactic => do
  let g ← getMainGoal
  g.withContext do
    let addr ← elabTerm (← `($retStx + 8#64)) none
    let rhs ← elabTerm targetVal none
    let ty ← instantiateMVars (← g.getType)
    let pExpr := ty.getArg! 3
    let some sub := pExpr.find? fun e =>
        e.isAppOfArity ``Arm64.pointsTo64 2 && e.getArg! 0 == addr
      | throwError "wp_ret8_bv_bits: no (ret + 8#64) ↦₆₄ _ found in spatial context"
    let rhsCell ← mkAppM ``Arm64.pointsTo64 #[addr, rhs]
    let cellEqTy ← mkEq sub rhsCell
    let prfMVar ← mkFreshExprMVar cellEqTy
    let gs ← getGoals
    let mut toClear : Array FVarId := #[]
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail then
        let u := decl.userName
        if u != `b0 && u != `b1 && u != `b2 && u != `b3 && u != `b4 &&
           u != `b5 && u != `b6 && u != `b7 && u != `b8 && u != `b9 &&
           u != `hb0 && u != `hb1 && u != `hb2 && u != `hb3 && u != `hb4 &&
           u != `hb5 && u != `hb6 && u != `hb7 && u != `hb8 && u != `hb9 &&
           u != `ret then
          toClear := toClear.push decl.fvarId
    let mId ← prfMVar.mvarId!.tryClearMany toClear
    setGoals [mId]
    let hb0 := mkIdent `hb0
    let hb1 := mkIdent `hb1
    let hb2 := mkIdent `hb2
    let hb3 := mkIdent `hb3
    let hb4 := mkIdent `hb4
    let hb5 := mkIdent `hb5
    let hb6 := mkIdent `hb6
    let hb7 := mkIdent `hb7
    let hb8 := mkIdent `hb8
    evalTactic (← `(tactic| (
      apply pointsTo64_congr_val
      first
      | (rw [hw_part01_eq $hb0:ident $hb1:ident $hb2:ident $hb3:ident
               $hb4:ident $hb5:ident $hb6:ident $hb7:ident]
         clear $hb0:ident $hb1:ident $hb2:ident $hb3:ident
               $hb4:ident $hb5:ident $hb6:ident $hb7:ident
         try (rw [vAcc10]; refine congrArg₂ (· ||| ·) ?_ (by clear $hb8:ident; bv_bits))
         rw [vAcc9_eq]
         bv_bits)
      | (rw [hw_part0_eq $hb0:ident $hb1:ident $hb2:ident $hb3:ident]
         clear $hb0:ident $hb1:ident $hb2:ident $hb3:ident
         simp only [vAcc8_eq, vAcc7_eq, vAcc6_eq, vAcc5_eq, part1_4, part1_3, part1_2]
         bv_bits)
      | (simp only [vAcc4_eq, vAcc3_eq, vAcc2_eq, vAcc1_eq, part0_4, part0_3, part0_2]
         bv_bits))))
    setGoals gs
    let g' ← g.assert `hret8_val cellEqTy (← instantiateMVars prfMVar)
    let (_, g'') ← g'.intro1P
    replaceMainGoal [g'']
    let hId := mkIdent `hret8_val
    evalTactic (← `(tactic| (rw [$hId:ident]; clear $hId:ident)))

macro "wp_reach" : tactic =>
  `(tactic| apply SepWP.done (by try simp only [arm64_norm]; rfl) (by try simp only [arm64_norm, *]; try assumption; rfl))

/-! ## Main proof -/

theorem decodeErrorFrom_ok_at_varintSliceX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hFrom : DecodeErrorFromOkW img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr decodeVarintSliceName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::varint::decode_varint_slice"))
      ((decodeErrorFromSpecX A).inImage img) := by
  have heq : (contractProg img.base ext).fnAddr decodeVarintSliceName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::varint::decode_varint_slice") =
      (contractProg img.base ext).fnAddr decodeErrorFromName := by
    simp only [contractProg, Program.fnAddr_rebase, decodeVarintSliceName, decodeErrorFromName,
      (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slice"), (ls_lemma% fnOff "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")]
    bv_lin
  rw [heq]
  exact hFrom

theorem decodeVarintSlice_okW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hFrom : DecodeErrorFromOkW img A ext) :
    DecodeVarintSliceOkW img A ext := by
  unfold DecodeVarintSliceOkW Spec.inImage decodeVarintSliceSpecW
  simp only [memRegion_24_cells, stackAt_decodeVarintSliceX, sepExists_sepConj_left,
    sepExists_sepConj_right]
  have hfn := (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slice")
  have hFromCall := decodeErrorFrom_ok_at_varintSliceX hFrom
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "prost::encoding::varint::decode_varint_slice")) 704
  clear hfn hFrom
  dsimp only [contractProg] at hFromCall ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr decodeVarintSliceName = entry
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  have hinv0 : CryptoVerification.LibsignalTripleRatchet.ImgCallInv img s0 := ⟨h_2, h_1⟩
  obtain ⟨ret, ptr, bs⟩ := x
  dsimp only at *
  have hx2 : s0.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := eq_ofNat_of_toNat_eq h_5
  obtain ⟨b0, bs1, rfl⟩ := exists_cons_of_all_gt (pre := []) h (by simp) (by rintro _ ⟨⟩)
  apply _root_.ProofLib.SepWPp.of_sepWP_inImage (mid := entry + bv% (16)) hinv0
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  intro hinv16
  suffices hjoin : ∀ (hinv36 : CryptoVerification.LibsignalTripleRatchet.ImgCallInv img (((((s0.writeReg64 Reg.sp (s0.sp - 80#64)).writeReg64 (Reg.gpr 29#5) (s0.sp - 16#64)).writeReg64
          (Reg.gpr 8#5) (BitVec.signExtend 64 b0)).setPState
        (subsPState64 (BitVec.ofNat 64 (b0 :: bs1).length) 11#64)).setPC (entry + bv% (36)) |>.setMem m)),
      SepWPp prog (s0.readReg64 Reg.lr)
      (((((s0.writeReg64 Reg.sp (s0.sp - 80#64)).writeReg64 (Reg.gpr 29#5) (s0.sp - 16#64)).writeReg64
          (Reg.gpr 8#5) (BitVec.signExtend 64 b0)).setPState
        (subsPState64 (BitVec.ofNat 64 (b0 :: bs1).length) 11#64)).setPC (entry + bv% (36)) |>.setMem m)
      (ret ↦₆₄ v_stk_6 ∗ (ret + 8#64) ↦₆₄ v_stk_5 ∗ (ret + 16#64) ↦₆₄ v_stk_4 ∗
        (ptr ↦₈ b0 ∗ (ptr + 1#64) ↦ₛ bs1) ∗ A.pool ∗
        stackAt (s0.sp - 80#64) decodeErrorHookStackW ∗ memRegion (s0.sp - 80#64) 8 ∗
        memRegion (s0.sp - 56#64) 40 ∗ (s0.sp - 72#64) ↦₆₄ v_stk_3 ∗
        (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗ (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
        (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5))
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨
              (∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3,
                ⌜sf.trace = s0.trace⌝ ∗
                  varintSliceResultAt A ret (b0 :: bs1) (decodeVarint (b0 :: bs1)) ∗
                  ptr ↦ₛ (b0 :: bs1) ∗ A.pool ∗
                  stackAt (s0.sp - 80#64) decodeErrorHookStackW ∗ memRegion (s0.sp - 80#64) 8 ∗
                  memRegion (s0.sp - 56#64) 40 ∗ (s0.sp - 72#64) ↦₆₄ x_3 ∗
                  (s0.sp - 64#64) ↦₆₄ x_2 ∗ (s0.sp - 16#64) ↦₆₄ x_1 ∗ (s0.sp - 8#64) ↦₆₄ x) ∗ R) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R) by
    by_cases h11 : 11 ≤ (b0 :: bs1).length
    · have hule11 := ule_11_of_geW h11 h_6
      apply _root_.ProofLib.SepWPp.of_sepWP_inImage (mid := entry + bv% (36)) hinv16
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun)
      intro hinv36
      exact hjoin hinv36
    · rcases h with h11' | ⟨hne, hlast⟩
      · exact (h11 h11').elim
      · have hule11 := ule_11_of_ltW h11 h_6
        have hbit_last := VarintSliceBits.getLsbD_7_beq_of_le hlast
        apply _root_.ProofLib.SepWPp.of_sepWP_inImage (mid := entry + bv% (32)) hinv16
        conv => arg 4; rw [pointsToBytes_split_lastW ptr (b0 :: bs1) hne]
        wp_steps
        conv => arg 4; rw [← pointsToBytes_split_lastW ptr (b0 :: bs1) hne, pointsToBytes_cons]
        apply SepWP.done (by rfl) (by exact hrun)
        intro hinv32
        apply _root_.ProofLib.SepWPp.of_sepWP_inImage (mid := entry + bv% (36)) hinv32
        wp_steps
        apply SepWP.done (by rfl) (by exact hrun)
        intro hinv36
        exact hjoin hinv36
  intro hinv36
  by_cases hnone : decodeVarint (b0 :: bs1) = none
  · obtain ⟨b0', b1, b2, b3, b4, b5, b6, b7, b8, b9, rest, heq,
      hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9⟩ := decodeVarint_eq_none_of_pre h hnone
    cases heq
    simp only [hnone, varintSliceResultAt]
    have hbit0 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_gt hb0
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
    have hb9_ule := byte9_ule_of_ge hb9
    apply _root_.ProofLib.SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::varint::decode_varint_slice")) hinv36
    conv => arg 4; simp only [pointsToBytes_cons]
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    intro hinv_call
    refine SepWPp.call_frame (x := (s0.sp - 64#64, 0x8000000000000001#64))
      (ret_pc := entry + bv% (592)) hFromCall
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by dsimp only; simp only [pure_sepConj_pure_assoc, arm64_norm]; rfl)
      (⟨hinv_call, rfl, by decide⟩ :
        (img.FrozenLoaded _ ∧ _ = img.symtab) ∧ (_ = s0.sp - 64#64 ∧ KindNoHeap 0x8000000000000001#64))
      (by sep_frame)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved, arm64_norm] at hcsm
    apply SepWPp.of_sepWP_ret
    conv => arg 4; simp only [memRegion_48_split, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
    apply SepWP.exists_elim; intro v_err
    wp_steps
    apply SepWP.fold (pointsTo64_entails_memRegion8 (ret + 16#64) _) (by sep_frame)
    apply SepWP.done
    · simp only [arm64_norm]
    · simp only [arm64_norm, hrunm]
    · rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
      refine ⟨?_, by simp only [arm64_norm], ?_⟩
      · intro hm_final
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm] at hm_final ⊢
        rcases hm_final with ⟨⟨hx0_ne, htr⟩, hm_final⟩
        refine ⟨s0.readReg64 (Reg.gpr 30#5), s0.readReg64 (Reg.gpr 29#5), v_err, ret, sm.readReg64 (Reg.gpr 0#5), ⟨htr, hx0_ne⟩, ?_⟩
        arm64_sep_close
      · simp only [CalleeSavedPreserved, arm64_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
  · apply SepWPp.of_sepWP_ret
    by_cases hb0 : b0 ≤ 0x7f#8
    · have hbit0 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_le hb0
      rw [varintSliceResultAt_1 A ret b0 bs1 hb0]
      wp_steps
      wp_ret8_bv_bits ret (vAcc1 b0)
      conv => arg 4; simp only [← pointsToBytes_cons]
      wp_done
    · have hbit0 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_gt hb0
      obtain ⟨b1, bs2, rfl⟩ := exists_cons_of_all_gt (pre := [b0]) h (by simp)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, hb0, not_false_eq_true])
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps 7
      by_cases hb1 : b1 ≤ 0x7f#8
      · have hbit1 := VarintSliceBits.getLsbD_7_beq_of_le hb1
        rw [varintSliceResultAt_2 A ret b0 b1 bs2 hb0 hb1]
        wp_steps
        wp_ret8_bv_bits ret (vAcc2 b0 b1)
        conv => arg 4; simp only [← pointsToBytes_cons]
        wp_done
      · have hbit1 := VarintSliceBits.getLsbD_7_beq_of_gt hb1
        have hovf2 := ovf_byte2 hb0 hb1
        obtain ⟨b2, bs3, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1]) h (by simp)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
            hb0, hb1, not_false_eq_true, and_self])
        conv => arg 4; rw [pointsToBytes_cons]
        wp_steps 7
        by_cases hb2 : b2 ≤ 0x7f#8
        · have hbit2 := VarintSliceBits.getLsbD_7_beq_of_le hb2
          rw [varintSliceResultAt_3 A ret b0 b1 b2 bs3 hb0 hb1 hb2]
          wp_steps
          wp_ret8_bv_bits ret (vAcc3 b0 b1 b2)
          conv => arg 4; simp only [← pointsToBytes_cons]
          wp_done
        · have hbit2 := VarintSliceBits.getLsbD_7_beq_of_gt hb2
          have hovf3 := ovf_byte3 hb0 hb1 hb2
          obtain ⟨b3, bs4, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2]) h (by simp)
            (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
              hb0, hb1, hb2, not_false_eq_true, and_self])
          conv => arg 4; rw [pointsToBytes_cons]
          wp_steps 7
          by_cases hb3 : b3 ≤ 0x7f#8
          · have hbit3 := VarintSliceBits.getLsbD_7_beq_of_le hb3
            rw [varintSliceResultAt_4 A ret b0 b1 b2 b3 bs4 hb0 hb1 hb2 hb3]
            wp_steps
            wp_ret8_bv_bits ret (vAcc4 b0 b1 b2 b3)
            conv => arg 4; simp only [← pointsToBytes_cons]
            wp_done
          · have hbit3 := VarintSliceBits.getLsbD_7_beq_of_gt hb3
            have hovf4 := VarintSliceBits.ovf_byte4_zext hb0 hb1 hb2 hb3
            obtain ⟨b4, bs5, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3]) h (by simp)
              (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                hb0, hb1, hb2, hb3, not_false_eq_true, and_self])
            conv => arg 4; rw [pointsToBytes_cons]
            wp_steps 7
            by_cases hb4 : b4 ≤ 0x7f#8
            · have hbit4 := VarintSliceBits.getLsbD_7_beq_of_le hb4
              rw [varintSliceResultAt_5 A ret b0 b1 b2 b3 b4 bs5 hb0 hb1 hb2 hb3 hb4]
              wp_steps
              wp_ret8_bv_bits ret (vAcc5 b0 b1 b2 b3 b4)
              conv => arg 4; simp only [← pointsToBytes_cons]
              wp_done
            · have hbit4 := VarintSliceBits.getLsbD_7_beq_of_gt hb4
              obtain ⟨b5, bs6, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4]) h
                (by simp) (by simp only [List.mem_cons, List.not_mem_nil, or_false,
                  forall_eq_or_imp, forall_eq, hb0, hb1, hb2, hb3, hb4, not_false_eq_true,
                  and_self])
              conv => arg 4; rw [pointsToBytes_cons]
              wp_steps 7
              by_cases hb5 : b5 ≤ 0x7f#8
              · have hbit5 := VarintSliceBits.getLsbD_7_beq_of_le hb5
                rw [varintSliceResultAt_6 A ret b0 b1 b2 b3 b4 b5 bs6 hb0 hb1 hb2 hb3 hb4 hb5]
                wp_steps
                wp_ret8_bv_bits ret (vAcc6 b0 b1 b2 b3 b4 b5)
                conv => arg 4; simp only [← pointsToBytes_cons]
                wp_done
              · have hbit5 := VarintSliceBits.getLsbD_7_beq_of_gt hb5
                have hovf6 := ovf_byte6 hb4 hb5
                obtain ⟨b6, bs7, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4, b5])
                  h (by simp) (by simp only [List.mem_cons, List.not_mem_nil, or_false,
                    forall_eq_or_imp, forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, not_false_eq_true,
                    and_self])
                conv => arg 4; rw [pointsToBytes_cons]
                wp_steps 7
                by_cases hb6 : b6 ≤ 0x7f#8
                · have hbit6 := VarintSliceBits.getLsbD_7_beq_of_le hb6
                  rw [varintSliceResultAt_7 A ret b0 b1 b2 b3 b4 b5 b6 bs7 hb0 hb1 hb2 hb3 hb4 hb5 hb6]
                  wp_steps
                  wp_ret8_bv_bits ret (vAcc7 b0 b1 b2 b3 b4 b5 b6)
                  conv => arg 4; simp only [← pointsToBytes_cons]
                  wp_done
                · have hbit6 := VarintSliceBits.getLsbD_7_beq_of_gt hb6
                  have hovf7 := ovf_byte7 hb4 hb5 hb6
                  obtain ⟨b7, bs8, rfl⟩ := exists_cons_of_all_gt
                    (pre := [b0, b1, b2, b3, b4, b5, b6]) h (by simp)
                    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                      forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, not_false_eq_true, and_self])
                  conv => arg 4; rw [pointsToBytes_cons]
                  wp_steps 7
                  by_cases hb7 : b7 ≤ 0x7f#8
                  · have hbit7 := VarintSliceBits.getLsbD_7_beq_of_le hb7
                    rw [varintSliceResultAt_8 A ret b0 b1 b2 b3 b4 b5 b6 b7 bs8
                      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7]
                    wp_steps
                    wp_ret8_bv_bits ret (vAcc8 b0 b1 b2 b3 b4 b5 b6 b7)
                    conv => arg 4; simp only [← pointsToBytes_cons]
                    wp_done
                  · have hbit7 := VarintSliceBits.getLsbD_7_beq_of_gt hb7
                    have hovf8 := VarintSliceBits.ovf_byte8_zext hb4 hb5 hb6 hb7
                    obtain ⟨b8, bs9, rfl⟩ := exists_cons_of_all_gt
                      (pre := [b0, b1, b2, b3, b4, b5, b6, b7]) h (by simp)
                      (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                        forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, not_false_eq_true,
                        and_self])
                    conv => arg 4; rw [pointsToBytes_cons]
                    wp_steps 7
                    by_cases hb8 : b8 ≤ 0x7f#8
                    · have hbit8 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_le hb8
                      rw [varintSliceResultAt_9 A ret b0 b1 b2 b3 b4 b5 b6 b7 b8 bs9
                        hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8]
                      wp_steps
                      wp_ret8_bv_bits ret (vAcc9 b0 b1 b2 b3 b4 b5 b6 b7 b8)
                      conv => arg 4; simp only [← pointsToBytes_cons]
                      wp_done
                    · have hbit8 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_gt hb8
                      obtain ⟨b9, bs10, rfl⟩ := exists_cons_of_all_gt
                        (pre := [b0, b1, b2, b3, b4, b5, b6, b7, b8]) h (by simp)
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
                      have hb9_ule := byte9_ule_of_lt hb9
                      have hovf10 := ovf_byte10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
                      conv => arg 4; rw [pointsToBytes_cons]
                      rw [varintSliceResultAt_10 A ret b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 bs10
                        hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9]
                      wp_steps
                      wp_ret8_bv_bits ret (vAcc10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)
                      conv => arg 4; simp only [← pointsToBytes_cons]
                      wp_done

/-! ## Relocatable `[LibsignalPlacement]` Proofs (Block `76`) -/

section Placed

open CryptoVerification

set_option maxHeartbeats 8000000 in
/-- Relocatable `prost::encoding::varint::decode_varint_slice` (Block `76`) meets
`DecodeVarintSlicePlacedOkW A H` given `DecodeErrorFromPlacedOkW A H`. -/
theorem decodeVarintSlice_placed_okW [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hFrom : DecodeErrorFromPlacedOkW A H) :
    DecodeVarintSlicePlacedOkW A H := by
  have hFromCall : subroutine_ok ((blkPC_76).rebase (blkPl_76).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpecWithStack A decodeErrorHookStackW)) :=
    WireX.decodeErrorFrom_placed_ok_cl (callerProg := (blkPC_76).rebase (blkPl_76).base H) hFrom
  clear hFrom
  unfold DecodeVarintSlicePlacedOkW withLsCodeLoaded
  conv =>
    arg 3
    unfold decodeVarintSliceSpecW
    simp only [memRegion_24_cells, stackAt_decodeVarintSliceX, sepExists_sepConj_left,
      sepExists_sepConj_right]
  wpp_init x s0
  obtain ⟨ret, ptr, bs⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have h : VarintSlicePre bs := by assumption
  have h_4 : bs.length < 2 ^ 63 := by assumption
  have hx2 : s0.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := by
    apply eq_ofNat_of_toNat_eq; assumption
  obtain ⟨b0, bs1, rfl⟩ := exists_cons_of_all_gt (pre := []) h (by simp) (by rintro _ ⟨⟩)
  apply SepWPp.of_sepWP_lscl (mid := (blkPl_76).base + bv% (16)) hcl0
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  suffices hjoin :
      LibsignalCodeLoaded lsmpl m →
      SepWPp ((blkPC_76).rebase (blkPl_76).base H) (s0.readReg64 Reg.lr)
      (((((s0.writeReg64 Reg.sp (s0.sp - 80#64)).writeReg64 (Reg.gpr 29#5) (s0.sp - 16#64)).writeReg64
          (Reg.gpr 8#5) (BitVec.signExtend 64 b0)).setPState
        (subsPState64 (BitVec.ofNat 64 (b0 :: bs1).length) 11#64)).setPC ((blkPl_76).base + bv% (36)) |>.setMem m)
      (ret ↦₆₄ v_stk_6 ∗ (ret + 8#64) ↦₆₄ v_stk_5 ∗ (ret + 16#64) ↦₆₄ v_stk_4 ∗
        (ptr ↦₈ b0 ∗ (ptr + 1#64) ↦ₛ bs1) ∗ A.pool ∗
        stackAt (s0.sp - 80#64) decodeErrorHookStackW ∗ memRegion (s0.sp - 80#64) 8 ∗
        memRegion (s0.sp - 56#64) 40 ∗ (s0.sp - 72#64) ↦₆₄ v_stk_3 ∗
        (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗ (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
        (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5))
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨
              (∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3,
                ⌜sf.trace = s0.trace⌝ ∗
                  varintSliceResultAt A ret (b0 :: bs1) (decodeVarint (b0 :: bs1)) ∗
                  ptr ↦ₛ (b0 :: bs1) ∗ A.pool ∗
                  stackAt (s0.sp - 80#64) decodeErrorHookStackW ∗ memRegion (s0.sp - 80#64) 8 ∗
                  memRegion (s0.sp - 56#64) 40 ∗ (s0.sp - 72#64) ↦₆₄ x_3 ∗
                  (s0.sp - 64#64) ↦₆₄ x_2 ∗ (s0.sp - 16#64) ↦₆₄ x_1 ∗ (s0.sp - 8#64) ↦₆₄ x) ∗ R) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R) by
    by_cases h11 : 11 ≤ (b0 :: bs1).length
    · have hule11 := ule_11_of_geW h11 h_4
      apply SepWPp.of_sepWP_lscl (mid := (blkPl_76).base + bv% (36)) hcl1
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      exact hjoin
    · rcases h with h11' | ⟨hne, hlast⟩
      · exact (h11 h11').elim
      · have hule11 := ule_11_of_ltW h11 h_4
        have hbit_last := VarintSliceBits.getLsbD_7_beq_of_le hlast
        apply SepWPp.of_sepWP_lscl (mid := (blkPl_76).base + bv% (32)) hcl1
        conv => arg 4; rw [pointsToBytes_split_lastW ptr (b0 :: bs1) hne]
        wp_steps
        conv => arg 4; rw [← pointsToBytes_split_lastW ptr (b0 :: bs1) hne, pointsToBytes_cons]
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hcl2
        apply SepWPp.of_sepWP_lscl (mid := (blkPl_76).base + bv% (36)) hcl2
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        exact hjoin
  intro hcl_join
  by_cases hnone : decodeVarint (b0 :: bs1) = none
  · obtain ⟨b0', b1, b2, b3, b4, b5, b6, b7, b8, b9, rest, heq,
      hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9⟩ := decodeVarint_eq_none_of_pre h hnone
    cases heq
    simp only [hnone, varintSliceResultAt]
    have hbit0 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_gt hb0
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
    have hb9_ule := byte9_ule_of_ge hb9
    apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl_join
    conv => arg 4; simp only [pointsToBytes_cons]
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcl_call
    refine SepWPp.call_frame_lscl (spec := decodeErrorFromSpecWithStack A decodeErrorHookStackW)
      (x := (s0.sp - 64#64, 0x8000000000000001#64))
      (ret_pc := (blkPl_76).base + bv% (592)) hFromCall hcl_call
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [decodeErrorFromSpecWithStack, arm64_norm]; rfl)
      (⟨rfl, by decide⟩ : s0.sp - 64#64 = s0.sp - 64#64 ∧ KindNoHeap 0x8000000000000001#64)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm _
    simp only [CalleeSavedPreserved, arm64_norm] at hcsm
    apply SepWPp.of_sepWP_ret
    conv => arg 4; simp only [decodeErrorFromSpecWithStack, memRegion_48_split, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
    apply SepWP.exists_elim; intro v_err
    wp_steps
    apply SepWP.fold (pointsTo64_entails_memRegion8 (ret + 16#64) _) (by sep_focus)
    apply SepWP.done
    · simp only [arm64_norm]
    · simp only [arm64_norm, hrunm]
    · rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
      refine ⟨?_, by simp only [arm64_norm], ?_⟩
      · intro hm_final
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm] at hm_final ⊢
        rcases hm_final with ⟨⟨hx0_ne, htr⟩, hm_final⟩
        refine ⟨s0.readReg64 (Reg.gpr 30#5), s0.readReg64 (Reg.gpr 29#5), v_err, ret, sm.readReg64 (Reg.gpr 0#5), ⟨htr, hx0_ne⟩, ?_⟩
        arm64_sep_close
      · simp only [CalleeSavedPreserved, arm64_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
  · apply SepWPp.of_sepWP_ret
    by_cases hb0 : b0 ≤ 0x7f#8
    · have hbit0 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_le hb0
      rw [varintSliceResultAt_1 A ret b0 bs1 hb0]
      wp_steps
      wp_ret8_bv_bits ret (vAcc1 b0)
      conv => arg 4; simp only [← pointsToBytes_cons]
      wp_done
    · have hbit0 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_gt hb0
      obtain ⟨b1, bs2, rfl⟩ := exists_cons_of_all_gt (pre := [b0]) h (by simp)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, hb0, not_false_eq_true])
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps 7
      by_cases hb1 : b1 ≤ 0x7f#8
      · have hbit1 := VarintSliceBits.getLsbD_7_beq_of_le hb1
        rw [varintSliceResultAt_2 A ret b0 b1 bs2 hb0 hb1]
        wp_steps
        wp_ret8_bv_bits ret (vAcc2 b0 b1)
        conv => arg 4; simp only [← pointsToBytes_cons]
        wp_done
      · have hbit1 := VarintSliceBits.getLsbD_7_beq_of_gt hb1
        have hovf2 := ovf_byte2 hb0 hb1
        obtain ⟨b2, bs3, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1]) h (by simp)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
            hb0, hb1, not_false_eq_true, and_self])
        conv => arg 4; rw [pointsToBytes_cons]
        wp_steps 7
        by_cases hb2 : b2 ≤ 0x7f#8
        · have hbit2 := VarintSliceBits.getLsbD_7_beq_of_le hb2
          rw [varintSliceResultAt_3 A ret b0 b1 b2 bs3 hb0 hb1 hb2]
          wp_steps
          wp_ret8_bv_bits ret (vAcc3 b0 b1 b2)
          conv => arg 4; simp only [← pointsToBytes_cons]
          wp_done
        · have hbit2 := VarintSliceBits.getLsbD_7_beq_of_gt hb2
          have hovf3 := ovf_byte3 hb0 hb1 hb2
          obtain ⟨b3, bs4, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2]) h (by simp)
            (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
              hb0, hb1, hb2, not_false_eq_true, and_self])
          conv => arg 4; rw [pointsToBytes_cons]
          wp_steps 7
          by_cases hb3 : b3 ≤ 0x7f#8
          · have hbit3 := VarintSliceBits.getLsbD_7_beq_of_le hb3
            rw [varintSliceResultAt_4 A ret b0 b1 b2 b3 bs4 hb0 hb1 hb2 hb3]
            wp_steps
            wp_ret8_bv_bits ret (vAcc4 b0 b1 b2 b3)
            conv => arg 4; simp only [← pointsToBytes_cons]
            wp_done
          · have hbit3 := VarintSliceBits.getLsbD_7_beq_of_gt hb3
            have hovf4 := VarintSliceBits.ovf_byte4_zext hb0 hb1 hb2 hb3
            obtain ⟨b4, bs5, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3]) h (by simp)
              (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                hb0, hb1, hb2, hb3, not_false_eq_true, and_self])
            conv => arg 4; rw [pointsToBytes_cons]
            wp_steps 7
            by_cases hb4 : b4 ≤ 0x7f#8
            · have hbit4 := VarintSliceBits.getLsbD_7_beq_of_le hb4
              rw [varintSliceResultAt_5 A ret b0 b1 b2 b3 b4 bs5 hb0 hb1 hb2 hb3 hb4]
              wp_steps
              wp_ret8_bv_bits ret (vAcc5 b0 b1 b2 b3 b4)
              conv => arg 4; simp only [← pointsToBytes_cons]
              wp_done
            · have hbit4 := VarintSliceBits.getLsbD_7_beq_of_gt hb4
              obtain ⟨b5, bs6, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4]) h (by simp)
                (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                  hb0, hb1, hb2, hb3, hb4, not_false_eq_true, and_self])
              conv => arg 4; rw [pointsToBytes_cons]
              wp_steps 5
              by_cases hb5 : b5 ≤ 0x7f#8
              · have hbit5 := VarintSliceBits.getLsbD_7_beq_of_le hb5
                rw [varintSliceResultAt_6 A ret b0 b1 b2 b3 b4 b5 bs6 hb0 hb1 hb2 hb3 hb4 hb5]
                wp_steps
                wp_ret8_bv_bits ret (vAcc6 b0 b1 b2 b3 b4 b5)
                conv => arg 4; simp only [← pointsToBytes_cons]
                wp_done
              · have hbit5 := VarintSliceBits.getLsbD_7_beq_of_gt hb5
                have hovf6 := ovf_byte6 hb4 hb5
                obtain ⟨b6, bs7, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4, b5]) h
                  (by simp) (by simp only [List.mem_cons, List.not_mem_nil, or_false,
                    forall_eq_or_imp, forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, not_false_eq_true,
                    and_self])
                conv => arg 4; rw [pointsToBytes_cons]
                wp_steps 7
                by_cases hb6 : b6 ≤ 0x7f#8
                · have hbit6 := VarintSliceBits.getLsbD_7_beq_of_le hb6
                  rw [varintSliceResultAt_7 A ret b0 b1 b2 b3 b4 b5 b6 bs7 hb0 hb1 hb2 hb3 hb4 hb5 hb6]
                  wp_steps
                  wp_ret8_bv_bits ret (vAcc7 b0 b1 b2 b3 b4 b5 b6)
                  conv => arg 4; simp only [← pointsToBytes_cons]
                  wp_done
                · have hbit6 := VarintSliceBits.getLsbD_7_beq_of_gt hb6
                  have hovf7 := ovf_byte7 hb4 hb5 hb6
                  obtain ⟨b7, bs8, rfl⟩ := exists_cons_of_all_gt
                    (pre := [b0, b1, b2, b3, b4, b5, b6]) h (by simp)
                    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                      forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, not_false_eq_true, and_self])
                  conv => arg 4; rw [pointsToBytes_cons]
                  wp_steps 7
                  by_cases hb7 : b7 ≤ 0x7f#8
                  · have hbit7 := VarintSliceBits.getLsbD_7_beq_of_le hb7
                    rw [varintSliceResultAt_8 A ret b0 b1 b2 b3 b4 b5 b6 b7 bs8
                      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7]
                    wp_steps
                    wp_ret8_bv_bits ret (vAcc8 b0 b1 b2 b3 b4 b5 b6 b7)
                    conv => arg 4; simp only [← pointsToBytes_cons]
                    wp_done
                  · have hbit7 := VarintSliceBits.getLsbD_7_beq_of_gt hb7
                    have hovf8 := VarintSliceBits.ovf_byte8_zext hb4 hb5 hb6 hb7
                    obtain ⟨b8, bs9, rfl⟩ := exists_cons_of_all_gt
                      (pre := [b0, b1, b2, b3, b4, b5, b6, b7]) h (by simp)
                      (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                        forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, not_false_eq_true,
                        and_self])
                    conv => arg 4; rw [pointsToBytes_cons]
                    wp_steps 7
                    by_cases hb8 : b8 ≤ 0x7f#8
                    · have hbit8 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_le hb8
                      rw [varintSliceResultAt_9 A ret b0 b1 b2 b3 b4 b5 b6 b7 b8 bs9
                        hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8]
                      wp_steps
                      wp_ret8_bv_bits ret (vAcc9 b0 b1 b2 b3 b4 b5 b6 b7 b8)
                      conv => arg 4; simp only [← pointsToBytes_cons]
                      wp_done
                    · have hbit8 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_gt hb8
                      obtain ⟨b9, bs10, rfl⟩ := exists_cons_of_all_gt
                        (pre := [b0, b1, b2, b3, b4, b5, b6, b7, b8]) h (by simp)
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
                      have hb9_ule := byte9_ule_of_lt hb9
                      have hovf10 := ovf_byte10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
                      conv => arg 4; rw [pointsToBytes_cons]
                      rw [varintSliceResultAt_10 A ret b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 bs10
                        hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9]
                      wp_steps
                      wp_ret8_bv_bits ret (vAcc10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)
                      conv => arg 4; simp only [← pointsToBytes_cons]
                      wp_done

end Placed

end CryptoVerification.LibsignalTripleRatchet.Prost.X
