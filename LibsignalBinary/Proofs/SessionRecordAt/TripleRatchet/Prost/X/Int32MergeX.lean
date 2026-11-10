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
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Wire.X.TryFromDefsX
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32Merge
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.Prost.WireTypeBv -- shake: keep

/-!
# `prost::encoding::int32::merge`

Verifies `prost::encoding::int32::merge::<&mut &[u8]>` (`0x2bc4`, block `8`) on
`contractProg img.base ext` and under `[LibsignalPlacement]` from `DecodeError::from`,
`decode_varint_slow`, and `decode_varint_slice`.
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
open CryptoVerification.LibsignalTripleRatchet.VarintBridge
open Proofs.libsignal.Stage1X

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_Int32MergeX : True := trivial

/-! ## Stack layout lemmas -/

theorem stackAt_int32MergeX (sp : BitVec 64) :
    stackAt sp int32MergeStackW =
      stackAt (sp - 80#64) decodeVarintSliceStackW ∗
        memRegion (sp - 80#64) 48 ∗
        (∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64,
          ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v3) ∗
          ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v1)) := by
  have h0 := stackAt_split_cells sp decodeVarintSliceStackW 10 (by decide)
  rw [← memRegion_cells (sp - BitVec.ofNat 64 (8 * 10)) 10 (by decide)] at h0
  change stackAt sp int32MergeStackW =
    stackAt (sp - 80#64) decodeVarintSliceStackW ∗ memRegion (sp - 80#64) 80 at h0
  have s1 := memRegion_split (sp - 80#64) 48 32 (by decide)
  rw [bv_sub_add_lit sp 80 48] at s1
  have s2 := memRegion_split (sp - 32#64) 8 24 (by decide)
  rw [bv_sub_add_lit sp 32 8] at s2
  have s3 := memRegion_split (sp - 24#64) 8 16 (by decide)
  rw [bv_sub_add_lit sp 24 8] at s3
  have s4 := memRegion_split (sp - 16#64) 8 8 (by decide)
  rw [bv_sub_add_lit sp 16 8] at s4
  rw [h0, s1, s2, s3, s4,
    memRegion_eight (sp - 32#64), memRegion_eight (sp - 24#64),
    memRegion_eight (sp - 16#64), memRegion_eight (sp - 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem stackAt_slice_eq_errorHookX (sp : BitVec 64) :
    stackAt sp decodeVarintSliceStackW =
      memRegion (sp - BitVec.ofNat 64 decodeVarintSliceStackW) 80 ∗
        stackAt sp decodeErrorHookStackW :=
  ProofLib.stackAt_split_bottom sp decodeErrorHookStackW 80 (by decide)

theorem stackAt_errorHook_entails_sliceX (sp : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 int32MergeStackW) 80 ∗ stackAt (sp - 80#64) decodeErrorHookStackW ⊢
      stackAt (sp - 80#64) decodeVarintSliceStackW := by
  have h := stackAt_slice_eq_errorHookX (sp - 80#64)
  have hsub : sp - 80#64 - BitVec.ofNat 64 decodeVarintSliceStackW = sp - BitVec.ofNat 64 int32MergeStackW := by
    change sp - 80#64 - BitVec.ofNat 64 decodeVarintSliceStackW = sp - BitVec.ofNat 64 (80 + decodeVarintSliceStackW)
    bv_lin
  rw [hsub] at h
  exact Entails.of_eq h.symm

theorem stackAt_slice_eq_slowX (sp : BitVec 64) :
    stackAt sp decodeVarintSliceStackW =
      memRegion (sp - BitVec.ofNat 64 decodeVarintSliceStackW) 16 ∗
        stackAt sp varintSlowStackX :=
  ProofLib.stackAt_split_bottom sp varintSlowStackX 16 (by decide)

theorem stackAt_slow_entails_sliceX (sp : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 int32MergeStackW) 16 ∗ stackAt (sp - 80#64) varintSlowStackX ⊢
      stackAt (sp - 80#64) decodeVarintSliceStackW := by
  have h := stackAt_slice_eq_slowX (sp - 80#64)
  have hsub : sp - 80#64 - BitVec.ofNat 64 decodeVarintSliceStackW = sp - BitVec.ofNat 64 int32MergeStackW := by
    change sp - 80#64 - BitVec.ofNat 64 decodeVarintSliceStackW = sp - BitVec.ofNat 64 (80 + decodeVarintSliceStackW)
    bv_lin
  rw [hsub] at h
  exact Entails.of_eq h.symm

/-! ## Arithmetic and list bounds for W (< 2^63) -/

private theorem cbz_len_cons_falseW {b0 : BitVec 8} {bs1 : List (BitVec 8)}
    (hlen : (b0 :: bs1).length < 2 ^ 63) :
    (BitVec.ofNat 64 (b0 :: bs1).length == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
  simp at h1

private theorem ult_10_of_ge_11W {n : Nat} (h11 : 11 ≤ n) (hlt : n < 2 ^ 63) :
    (10#64).ult (BitVec.ofNat 64 n) = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    decide_eq_true_eq]
  omega

private theorem ult_10_of_lt_11W {n : Nat} (h11 : ¬ 11 ≤ n) (_hlt : n < 2 ^ 63) :
    (10#64).ult (BitVec.ofNat 64 n) = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    decide_eq_false_iff_not]
  omega

private theorem len_ult_consumed_falseW {bs rest : List (BitVec 8)} (_hlt : bs.length < 2 ^ 63) :
    (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 (bs.length - rest.length)) = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : bs.length < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : bs.length - rest.length < 2 ^ 64),
    decide_eq_false_iff_not]
  omega

/-! ## Callee helpers -/

theorem decodeErrorFrom_ok_at_int32MergeX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hFrom : DecodeErrorFromOkW img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr int32MergeName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>"))
      ((decodeErrorFromSpecX A).inImage img) := by
  have heq : (contractProg img.base ext).fnAddr int32MergeName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") =
      (contractProg img.base ext).fnAddr decodeErrorFromName := by
    simp only [contractProg, Program.fnAddr_rebase, int32MergeName, decodeErrorFromName,
      (ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>"), (ls_lemma% fnOff "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")]
    bv_lin
  rw [heq]
  exact hFrom

theorem decodeVarintSlow_ok_at_int32MergeX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hSlow : DecodeVarintSlowOkW img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr int32MergeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>"))
      ((WireX.decodeVarintSlowSpecX A).inImage img) := by
  have heq : (contractProg img.base ext).fnAddr int32MergeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") =
      (contractProg img.base ext).fnAddr varintSlowName := by
    simp only [contractProg, Program.fnAddr_rebase, int32MergeName, varintSlowName,
      (ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>"), (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>")]
    bv_lin
  rw [heq]
  exact hSlow

theorem decodeVarintSlice_ok_at_int32MergeX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hSlice : DecodeVarintSliceOkW img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr int32MergeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>"))
      ((decodeVarintSliceSpecW A).inImage img) := by
  have heq : (contractProg img.base ext).fnAddr int32MergeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") =
      (contractProg img.base ext).fnAddr decodeVarintSliceName := by
    simp only [contractProg, Program.fnAddr_rebase, int32MergeName, decodeVarintSliceName,
      (ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>"), (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slice")]
    bv_lin
  rw [heq]
  exact hSlice

theorem int32Merge_okW {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hFrom : DecodeErrorFromOkW img A ext)
    (hSlow : DecodeVarintSlowOkW img A ext)
    (hSlice : DecodeVarintSliceOkW img A ext) :
    Int32MergeOkW img A ext := by
  unfold Int32MergeOkW Spec.inImage int32MergeSpecW
  simp only [sliceCursorAt, stackAt_int32MergeX, sepExists_sepConj_left, sepExists_sepConj_right]
  have hfn := (ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>")
  have hFromCall := decodeErrorFrom_ok_at_int32MergeX hFrom
  have hSlowCall := decodeVarintSlow_ok_at_int32MergeX hSlow
  have hSliceCall := decodeVarintSlice_ok_at_int32MergeX hSlice
  code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base (Rust.withPanics ext) hfn (num% (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>")) 300
  clear hfn hFrom hSlow hSlice
  dsimp only [contractProg] at hFromCall hSlowCall hSliceCall ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr int32MergeName = entry
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  have hinv0 : CryptoVerification.LibsignalTripleRatchet.ImgCallInv img s0 := ⟨h_2, h_1⟩
  rcases x with ⟨wt, valPtr, bufRef, slot, ptr, bs⟩
  dsimp only at *
  by_cases hwt : wt = .varint
  · subst hwt
    have hwt_br := wt_beq_zero_of_varint h_3
    cases bs with
    | nil =>
      simp only [mergeUint32, decodeVarint, decodeVarintAux, ne_eq, not_true_eq_false, ite_false]
      apply _root_.ProofLib.SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>")) hinv0
      conv => arg 4; rw [memRegion_48_split (s0.sp - 80#64), bv_sub_add_lit s0.sp 80 8]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro v_err0
      wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr 0#64) (by sep_frame)
      conv => arg 4; rw [stackAt_slice_eq_errorHookX (s0.sp - 80#64)]
      apply SepWP.done (by rfl) (by exact hrun)
      intro hinv_call
      refine SepWPp.call_frame (x := (s0.sp - 80#64, 0x8000000000000001#64))
        (ret_pc := entry + bv% (52)) hFromCall
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
        (by simp only [arm64_norm])
        (by dsimp only; simp only [pure_sepConj_pure_assoc, arm64_norm]; rfl)
        (⟨hinv_call, rfl, by decide⟩ :
          (img.FrozenLoaded _ ∧ _ = img.symtab) ∧ (_ = s0.sp - 80#64 ∧ KindNoHeap 0x8000000000000001#64))
        (by sep_frame)
        (fun _ _ _ _ hex => allowPanic_not_exited hex)
        (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
      intro sm hpcm hrunm hspm hcsm
      have hvregs := hcsm.2.2.2.2.2.2.2.2.2.2.2
      simp only [arm64_norm] at hvregs
      apply SepWPp.of_sepWP_ret
      simp only [arm64_norm]
      apply SepWP.fold (stackAt_errorHook_entails_sliceX s0.sp) (by sep_frame)
      wp_steps
      wp_done
    | cons b0 bs1 =>
      have hcbz := cbz_len_cons_falseW h
      by_cases hb0 : b0 ≤ 0x7f#8
      · have hbit0 := signExtend64_getLsbD_63_of_le hb0
        rw [mergeUint32_varint_1 bs1 hb0]
        apply SepWPp.of_sepWP_ret
        conv => arg 4; rw [pointsToBytes_cons, memRegion_four valPtr]
        simp only [sepExists_sepConj_left]
        apply SepWP.exists_elim; intro v_val
        wp_steps
        conv => arg 4; rw [len_cons_sub_one b0 bs1, ← pointsToBytes_cons]
        simp only [sliceCursorAfter, List.length_cons, Nat.add_sub_cancel_left]
        wp_done
      · have hbit0 := signExtend64_getLsbD_63_of_gt hb0
        have hlen_toNat : (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        apply _root_.ProofLib.SepWPp.of_sepWP_inImage (mid := entry + bv% (144)) hinv0
        conv => arg 4; rw [pointsToBytes_cons]
        wp_steps
        apply SepWP.done (by rfl) (by exact hrun)
        intro hinv144
        by_cases h11 : 11 ≤ (b0 :: bs1).length
        · have hhi := ult_10_of_ge_11W h11 h
          have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inl h11
          apply _root_.ProofLib.SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>")) hinv144
          conv => arg 4; rw [memRegion_48_slice s0.sp]
          wp_steps
          apply SepWP.done (by rfl) (by exact hrun)
          intro hinv_call
          refine SepWPp.call_frame (x := ⟨s0.sp - 80#64, ptr, b0 :: bs1⟩)
            (ret_pc := entry + bv% (176)) hSliceCall
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
            (by simp only [arm64_norm])
            (by dsimp only; simp only [pure_sepConj_pure_assoc, arm64_norm]; rfl)
            (⟨hinv_call, rfl, rfl, hlen_toNat, h, hpre_slice⟩ :
              (img.FrozenLoaded _ ∧ _ = img.symtab) ∧
                (s0.sp - 80#64 = s0.sp - 80#64 ∧ ptr = ptr ∧
                  (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length ∧
                  (b0 :: bs1).length < 2 ^ 63 ∧ VarintSlicePre (b0 :: bs1)))
            (by sep_frame)
            (fun _ _ _ _ hex => allowPanic_not_exited hex)
            (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
          intro sm hpcm hrunm hspm hcsm
          simp only [CalleeSavedPreserved] at hcsm
          obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
          simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
          apply SepWPp.of_sepWP_ret
          cases hd : decodeVarint (b0 :: bs1) with
          | none =>
            simp only [mergeUint32, hd, ne_eq, not_true_eq_false, ite_false, varintSliceResultAt,
              sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
            apply SepWP.exists_elim; intro e_err
            wp_steps
            apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 (b0 :: bs1).length)) (by sep_frame)
            apply SepWP.fold (sliceErr_entails_memRegion48 s0.sp 1#64 e_err) (by sep_frame)
            wp_done
          | some p =>
            rcases p with ⟨v, rest⟩
            have hcc := len_ult_consumed_falseW (rest := rest) h
            have hsub_len := bv_len_sub_consumed hd
            simp only [mergeUint32, hd, ne_eq, not_true_eq_false, ite_false, varintSliceResultAt,
              sliceCursorAfter, arm64_norm]
            conv => arg 4; rw [memRegion_four valPtr]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right]
            apply SepWP.exists_elim; intro v_val
            wp_steps
            apply SepWP.fold (sliceOk_entails_memRegion48 s0.sp 0#64 v (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_frame)
            wp_done
        · have hhi := ult_10_of_lt_11W h11 h
          have hne_cons : b0 :: bs1 ≠ [] := List.cons_ne_nil b0 bs1
          apply _root_.ProofLib.SepWPp.of_sepWP_inImage (mid := entry + bv% (156)) hinv144
          conv => arg 4; rw [← pointsToBytes_cons, ProofLib.pointsToBytes_split_last ptr (b0 :: bs1) hne_cons]
          wp_steps
          conv => arg 4; rw [← ProofLib.pointsToBytes_split_last ptr (b0 :: bs1) hne_cons]
          apply SepWP.done (by rfl) (by exact hrun)
          intro hinv156
          by_cases hlast : ((b0 :: bs1).getLast hne_cons).toNat ≤ 0x7F
          · have hbit_last := getLsbD_7_of_le hlast
            have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inr ⟨hne_cons, hlast⟩
            apply _root_.ProofLib.SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>")) hinv156
            conv => arg 4; rw [pointsToBytes_cons, memRegion_48_slice s0.sp]
            wp_steps
            apply SepWP.done (by rfl) (by exact hrun)
            intro hinv_call
            refine SepWPp.call_frame (x := ⟨s0.sp - 80#64, ptr, b0 :: bs1⟩)
              (ret_pc := entry + bv% (176)) hSliceCall
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
              (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
              (by simp only [arm64_norm])
              (by dsimp only; simp only [pure_sepConj_pure_assoc, arm64_norm]; rfl)
              (⟨hinv_call, rfl, rfl, hlen_toNat, h, hpre_slice⟩ :
                (img.FrozenLoaded _ ∧ _ = img.symtab) ∧
                  (s0.sp - 80#64 = s0.sp - 80#64 ∧ ptr = ptr ∧
                    (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length ∧
                    (b0 :: bs1).length < 2 ^ 63 ∧ VarintSlicePre (b0 :: bs1)))
              (by sep_frame)
              (fun _ _ _ _ hex => allowPanic_not_exited hex)
              (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
            intro sm hpcm hrunm hspm hcsm
            simp only [CalleeSavedPreserved] at hcsm
            obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
            simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
            apply SepWPp.of_sepWP_ret
            cases hd : decodeVarint (b0 :: bs1) with
            | none =>
              simp only [mergeUint32, hd, ne_eq, not_true_eq_false, ite_false, varintSliceResultAt,
                sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
              apply SepWP.exists_elim; intro e_err
              wp_steps
              apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 (b0 :: bs1).length)) (by sep_frame)
              apply SepWP.fold (sliceErr_entails_memRegion48 s0.sp 1#64 e_err) (by sep_frame)
              wp_done
            | some p =>
              rcases p with ⟨v, rest⟩
              have hcc := len_ult_consumed_falseW (rest := rest) h
              have hsub_len := bv_len_sub_consumed hd
              simp only [mergeUint32, hd, ne_eq, not_true_eq_false, ite_false, varintSliceResultAt,
                sliceCursorAfter, arm64_norm]
              conv => arg 4; rw [memRegion_four valPtr]
              simp only [sepExists_sepConj_left, sepExists_sepConj_right]
              apply SepWP.exists_elim; intro v_val
              wp_steps
              apply SepWP.fold (sliceOk_entails_memRegion48 s0.sp 0#64 v (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_frame)
              wp_done
          · have hbit_last := getLsbD_7_of_gt hlast
            apply _root_.ProofLib.SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>")) hinv156
            wp_steps
            conv => arg 4; rw [pointsToBytes_cons, stackAt_slice_eq_slowX (s0.sp - 80#64)]
            apply SepWP.done (by rfl) (by exact hrun)
            intro hinv_call
            refine SepWPp.call_frame (x := (bufRef, slot, ptr, b0 :: bs1))
              (ret_pc := entry + bv% (268)) hSlowCall
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
              (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
              (by simp only [arm64_norm])
              (by dsimp only; simp only [pure_sepConj_pure_assoc, arm64_norm]; rfl)
              (⟨hinv_call, rfl, by omega⟩ :
                (img.FrozenLoaded _ ∧ _ = img.symtab) ∧ (bufRef = bufRef ∧ (b0 :: bs1).length < 2 ^ 64))
              (by sep_frame)
              (fun _ _ _ _ hex => allowPanic_not_exited hex)
              (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
            intro sm hpcm hrunm hspm hcsm
            simp only [CalleeSavedPreserved] at hcsm
            obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
            simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
            apply SepWPp.of_sepWP_ret
            dsimp only [WireX.decodeVarintSlowSpecX]
            rw [decodeVarint_eq_varintSlow]
            cases hd : decodeVarint (b0 :: bs1) with
            | none =>
              simp only [hd, Option.map_none, mergeUint32, ne_eq, not_true_eq_false, ite_false,
                sepConj_assoc, arm64_norm]
              apply SepWP.pure_elim; rintro ⟨hsm0, hsm1⟩
              apply SepWP.fold (stackAt_slow_entails_sliceX s0.sp) (by sep_frame)
              wp_steps
              apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot _ _) (by sep_frame)
              wp_done
            | some p =>
              rcases p with ⟨v, rest⟩
              obtain ⟨k, _, hkl, hrest_eq⟩ := decodeVarintAux_suffix (b0 :: bs1) 0 0#64 v rest hd
              have hlen_sub : (b0 :: bs1).length - ((b0 :: bs1).length - rest.length) = rest.length := by
                rw [hrest_eq, List.length_drop]; omega
              simp only [hd, Option.map_some, hlen_sub, mergeUint32, ne_eq, not_true_eq_false, ite_false,
                sepConj_assoc, arm64_norm, sliceCursorAfter]
              apply SepWP.pure_elim; rintro ⟨hsm0, hsm1⟩
              apply SepWP.fold (stackAt_slow_entails_sliceX s0.sp) (by sep_frame)
              conv => arg 4; rw [memRegion_four valPtr]
              simp only [sepExists_sepConj_left, sepExists_sepConj_right]
              apply SepWP.exists_elim; intro v_val
              wp_steps
              wp_done
  · have hwt_br := wt_beq_zero_of_ne_varint h_3 hwt
    rw [mergeUint32_ne_varint bs hwt]
    apply _root_.ProofLib.SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>")) hinv0
    conv => arg 4; rw [memRegion_48_wtErr s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro b_err1
    apply SepWP.exists_elim; intro b_err0
    apply SepWP.exists_elim; intro v_err0
    wp_steps
    apply SepWP.fold (wtErr_entails_memRegion40 s0.sp _ _) (by sep_frame)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_frame)
    conv => arg 4; rw [stackAt_slice_eq_errorHookX (s0.sp - 80#64)]
    apply SepWP.done (by rfl) (by exact hrun)
    intro hinv_call
    refine SepWPp.call_frame (x := (s0.sp - 80#64, 0x8000000000000006#64))
      (ret_pc := entry + bv% (52)) hFromCall
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by dsimp only; simp only [pure_sepConj_pure_assoc, arm64_norm]; rfl)
      (⟨hinv_call, rfl, by decide⟩ :
        (img.FrozenLoaded _ ∧ _ = img.symtab) ∧ (_ = s0.sp - 80#64 ∧ KindNoHeap 0x8000000000000006#64))
      (by sep_frame)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm
    have hvregs := hcsm.2.2.2.2.2.2.2.2.2.2.2
    simp only [arm64_norm] at hvregs
    apply SepWPp.of_sepWP_ret
    simp only [arm64_norm]
    apply SepWP.fold (stackAt_errorHook_entails_sliceX s0.sp) (by sep_frame)
    wp_steps
    wp_done

/-! ## Relocatable `[LibsignalPlacement]` Proofs (Block `8`) -/

section Placed

open CryptoVerification

/-- Relocatable `prost::encoding::int32::merge::<&mut &[u8]>` (Block `8`) meets
`Int32MergePlacedOkW A H` given placed contracts for `DecodeError::from`,
`decode_varint_slow`, and `decode_varint_slice`. -/
theorem int32Merge_placed_okW [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hFrom : DecodeErrorFromPlacedOkW A H)
    (hSlow : DecodeVarintSlowPlacedOkW A H)
    (hSlice : DecodeVarintSlicePlacedOkW A H) :
    Int32MergePlacedOkW A H :=
  CryptoVerification.LibsignalTripleRatchet.Prost.int32_merge_placed_ok_gen
    (errStack := decodeErrorHookStackW) (by decide)
    (WireX.decodeErrorFrom_placed_ok_cl (callerProg := (blkPC_8).rebase (blkPl_8).base H) hFrom)
    (ls_subroutine_ok_cl_of_callee (callerProg := (blkPC_8).rebase (blkPl_8).base H)
      (CryptoVerification.LibsignalTripleRatchet.Prost.decodeVarintSlowGen_lscl_ok_of_session2 hSlow))
    (ls_subroutine_ok_cl_of_callee (callerProg := (blkPC_8).rebase (blkPl_8).base H) hSlice)

end Placed

end CryptoVerification.LibsignalTripleRatchet.Prost.X
