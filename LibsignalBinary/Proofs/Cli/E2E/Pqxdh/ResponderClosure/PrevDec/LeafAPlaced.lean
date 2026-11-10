/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafA
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmas
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp

/-!
# Relocatable `prost::encoding::skip_field::<&mut &[u8]> [local#5]` (Cases 1–6)

Relocatable (`[LibsignalPlacement]`) verification of the six non-group dispatch branches of
`prost::encoding::skip_field::<&mut &[u8]> [local#5]` on Block `510`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.VarintBridge
open CryptoVerification.CodeLayout
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.CliHandshake.Placed

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
private theorem bv64_sub_zero_pl (x : BitVec 64) : x - 0#64 = x := BitVec.sub_zero x

@[local simp, local arm64_norm]
private theorem bv64_add_zero_pl (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

/-- Case-restricted relocatable `[LibsignalPlacement]` contract for
`prost::encoding::skip_field::<&mut &[u8]> [local#5]` (Block `510`, `lsmpl.base 510`) at recursion
budget `depth` under predicate `P`. -/
def SkipField6AtPlacedOk [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) (depth : Nat) (P : SkipFieldGhost → Prop) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 510)
    (withLsCl lsmpl (skipField3SpecAt A depth P))

/-! ## Case 1: `depth = 0` (`RecursionLimitReached`) -/

theorem skipField6_depth_zero_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hFromCall : subroutine_ok (lsProg_507 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpecWithStack A decodeErrorHookStackX))) :
    subroutine_ok (lsProg_507 H) (blkPl_507).base
      (withLsCodeLoaded lsmpl (skipField3SpecAt A 0 (fun _ => True))) := by
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold skipField3SpecAt
    simp only [sliceCursorAt, stackAt_skipField3 _ 0 (by decide),
      sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hd_zero : BitVec.setWidth 32 (s0.readReg64 (Reg.gpr 3#5)) = 0#32 := by assumption
  have hcbz := cbz_depth_zero hd_zero
  rw [skipField_depth_zero]
  apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl0
  conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v_err0
  wp_steps
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
  conv => arg 4; rw [skipBelow3_err s0.sp 0 (by decide)]
  wp_reach
  intro hcl1
  refine SepWPp.call_frame_lscl (spec := decodeErrorFromSpecWithStack A decodeErrorHookStackX)
    (x := (s0.sp - 96#64, 0x8000000000000002#64))
    (ret_pc := (blkPl_507).base + 204#64) hFromCall hcl1
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [decodeErrorFromSpecWithStack, arm64_norm]; rfl)
    (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000002#64)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm _hcl2
  simp only [CalleeSavedPreserved, arm64_norm] at hcsm
  rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
  apply SepWPp.of_sepWP_ret
  dsimp only [decodeErrorFromSpecWithStack]
  simp only [arm64_norm]
  apply SepWP.fold (skipBelow3_err_entails s0.sp 0 (by decide)) (by sep_focus)
  wp_steps
  wp_done

/-! ## Case 2: `depth = d + 1`, `wt = .endGroup` (`UnexpectedEndGroupTag`) -/

theorem skipField6_endGroup_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hFromCall : subroutine_ok (lsProg_507 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpecWithStack A decodeErrorHookStackX)))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (lsProg_507 H) (blkPl_507).base
      (withLsCodeLoaded lsmpl (skipField3SpecAt A (d + 1) (fun x => x.wt = .endGroup))) := by
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold skipField3SpecAt
    simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
      sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hwt_eq : wt = .endGroup := by assumption
  subst hwt_eq
  have hx0_wt : BitVec.setWidth 8 (s0.readReg64 (Reg.gpr 0#5)) = BitVec.ofNat 8 WireType.endGroup.toNat := by assumption
  have hx3_d : BitVec.setWidth 32 (s0.readReg64 (Reg.gpr 3#5)) = BitVec.ofNat 32 (d + 1) := by assumption
  have hcbz := cbz_depth_succ hx3_d hdepth
  have hw0 := w0_and_255_eq hx0_wt
  dsimp [WireType.toNat] at hw0
  rw [skipField_succ_endGroup]
  apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl0
  conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v_err0
  wp_steps
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
  conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth]
  wp_reach
  intro hcl1
  refine SepWPp.call_frame_lscl (spec := decodeErrorFromSpecWithStack A decodeErrorHookStackX)
    (x := (s0.sp - 96#64, 0x8000000000000009#64))
    (ret_pc := (blkPl_507).base + 204#64) hFromCall hcl1
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [decodeErrorFromSpecWithStack, arm64_norm]; rfl)
    (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000009#64)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm _hcl2
  simp only [CalleeSavedPreserved, arm64_norm] at hcsm
  rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
  apply SepWPp.of_sepWP_ret
  dsimp only [decodeErrorFromSpecWithStack]
  simp only [arm64_norm]
  apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
  wp_steps
  wp_done

/-! ## Case 3: `depth = d + 1`, `wt = .sixtyFourBit` (`skipBytes 8`) -/

theorem skipField6_sixtyFourBit_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hFromCall : subroutine_ok (lsProg_507 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpecWithStack A decodeErrorHookStackX)))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (lsProg_507 H) (blkPl_507).base
      (withLsCodeLoaded lsmpl (skipField3SpecAt A (d + 1) (fun x => x.wt = .sixtyFourBit))) := by
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold skipField3SpecAt
    simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
      sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hlen_lt : bs.length < 2 ^ 63 := by assumption
  have hwt_eq : wt = .sixtyFourBit := by assumption
  subst hwt_eq
  have hx0_wt : BitVec.setWidth 8 (s0.readReg64 (Reg.gpr 0#5)) = BitVec.ofNat 8 WireType.sixtyFourBit.toNat := by assumption
  have hx3_d : BitVec.setWidth 32 (s0.readReg64 (Reg.gpr 3#5)) = BitVec.ofNat 32 (d + 1) := by assumption
  have hcbz := cbz_depth_succ hx3_d hdepth
  have hw0 := w0_and_255_eq hx0_wt
  dsimp [WireType.toNat] at hw0
  rw [skipField_succ_sixtyFourBit]
  by_cases hlt : bs.length < 8
  · have hule := ule_len_of_lt (n := 8#64) hlt hlen_lt
    simp only [skipBytes, hlt, ↓reduceIte]
    apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl0
    conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro v_err0
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
    conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth]
    wp_reach
    intro hcl1
    refine SepWPp.call_frame_lscl (spec := decodeErrorFromSpecWithStack A decodeErrorHookStackX)
      (x := (s0.sp - 96#64, 0x8000000000000007#64))
      (ret_pc := (blkPl_507).base + 204#64) hFromCall hcl1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [decodeErrorFromSpecWithStack, arm64_norm]; rfl)
      (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm _hcl2
    simp only [CalleeSavedPreserved, arm64_norm] at hcsm
    rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
    apply SepWPp.of_sepWP_ret
    dsimp only [decodeErrorFromSpecWithStack]
    simp only [arm64_norm]
    apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps
    wp_done
  · have hule := ule_len_of_ge (n := 8#64) hlt hlen_lt
    have hsub := bv_len_sub_skip (n := 8#64) hlt
    have hadd := bv_ptr_add_skip_top (ptr := ptr) (n := 8#64) hlt
    simp only [skipBytes, hlt, ↓reduceIte, sliceCursorAfter]
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

/-! ## Case 4: `depth = d + 1`, `wt = .thirtyTwoBit` (`skipBytes 4`) -/

theorem skipField6_thirtyTwoBit_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hFromCall : subroutine_ok (lsProg_507 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpecWithStack A decodeErrorHookStackX)))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (lsProg_507 H) (blkPl_507).base
      (withLsCodeLoaded lsmpl (skipField3SpecAt A (d + 1) (fun x => x.wt = .thirtyTwoBit))) := by
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold skipField3SpecAt
    simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
      sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hlen_lt : bs.length < 2 ^ 63 := by assumption
  have hwt_eq : wt = .thirtyTwoBit := by assumption
  subst hwt_eq
  have hx0_wt : BitVec.setWidth 8 (s0.readReg64 (Reg.gpr 0#5)) = BitVec.ofNat 8 WireType.thirtyTwoBit.toNat := by assumption
  have hx3_d : BitVec.setWidth 32 (s0.readReg64 (Reg.gpr 3#5)) = BitVec.ofNat 32 (d + 1) := by assumption
  have hcbz := cbz_depth_succ hx3_d hdepth
  have hw0 := w0_and_255_eq hx0_wt
  dsimp [WireType.toNat] at hw0
  rw [skipField_succ_thirtyTwoBit]
  by_cases hlt : bs.length < 4
  · have hule := ule_len_of_lt (n := 4#64) hlt hlen_lt
    simp only [skipBytes, hlt, ↓reduceIte]
    apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl0
    conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro v_err0
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
    conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth]
    wp_reach
    intro hcl1
    refine SepWPp.call_frame_lscl (spec := decodeErrorFromSpecWithStack A decodeErrorHookStackX)
      (x := (s0.sp - 96#64, 0x8000000000000007#64))
      (ret_pc := (blkPl_507).base + 204#64) hFromCall hcl1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [decodeErrorFromSpecWithStack, arm64_norm]; rfl)
      (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm _hcl2
    simp only [CalleeSavedPreserved, arm64_norm] at hcsm
    rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
    apply SepWPp.of_sepWP_ret
    dsimp only [decodeErrorFromSpecWithStack]
    simp only [arm64_norm]
    apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps
    wp_done
  · have hule := ule_len_of_ge (n := 4#64) hlt hlen_lt
    have hsub := bv_len_sub_skip (n := 4#64) hlt
    have hadd := bv_ptr_add_skip_top (ptr := ptr) (n := 4#64) hlt
    simp only [skipBytes, hlt, ↓reduceIte, sliceCursorAfter]
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

/-! ## Case 5: `depth = d + 1`, `wt = .varint` -/

theorem skipField6_varint_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hVarintCall : subroutine_ok (lsProg_507 H) (lsmpl.base 515)
      (withLsCl lsmpl (decodeVarint2SpecX A)))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (lsProg_507 H) (blkPl_507).base
      (withLsCodeLoaded lsmpl (skipField3SpecAt A (d + 1) (fun x => x.wt = .varint))) := by
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold skipField3SpecAt
    simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
      sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hlen_lt : bs.length < 2 ^ 63 := by assumption
  have hwt_eq : wt = .varint := by assumption
  subst hwt_eq
  have hx0_wt : BitVec.setWidth 8 (s0.readReg64 (Reg.gpr 0#5)) = BitVec.ofNat 8 WireType.varint.toNat := by assumption
  have hx3_d : BitVec.setWidth 32 (s0.readReg64 (Reg.gpr 3#5)) = BitVec.ofNat 32 (d + 1) := by assumption
  have hcbz := cbz_depth_succ hx3_d hdepth
  have hw0 := w0_and_255_eq hx0_wt
  dsimp [WireType.toNat] at hw0
  rw [skipField_succ_varint]
  apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 515) hcl0
  conv => arg 4; rw [skipBelow3_leaf s0.sp (d + 1) hdepth]
  wp_steps
  wp_reach
  intro hcl1
  refine SepWPp.call_frame_lscl (spec := decodeVarint2SpecX A)
    (x := ⟨bufRef, slot, ptr, bs⟩)
    (ret_pc := (blkPl_507).base + 112#64) hVarintCall hcl1
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [decodeVarint2SpecX, arm64_norm]; rfl)
    (⟨rfl, hlen_lt⟩ : bufRef = bufRef ∧ bs.length < 2 ^ 63)
    (by simp only [sliceCursorAt]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm _hcl2
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
  apply SepWPp.of_sepWP_ret
  dsimp only [decodeVarint2SpecX]
  cases hd : decodeVarint bs with
  | none =>
    simp only [Option.map, sepConj_assoc, arm64_norm]
    apply SepWP.pure_elim; intro hsm0
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps
    wp_done
  | some p =>
    rcases p with ⟨v, rest⟩
    simp only [Option.map, sliceCursorAfter, sepConj_assoc, arm64_norm]
    apply SepWP.pure_elim; rintro ⟨hsm0, hsm1⟩
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps
    wp_done

/-! ## Case 6: `depth = d + 1`, `wt = .lengthDelimited` -/

theorem skipField6_lengthDelimited_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hFromCall : subroutine_ok (lsProg_507 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpecWithStack A decodeErrorHookStackX)))
    (hVarintCall : subroutine_ok (lsProg_507 H) (lsmpl.base 515)
      (withLsCl lsmpl (decodeVarint2SpecX A)))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (lsProg_507 H) (blkPl_507).base
      (withLsCodeLoaded lsmpl (skipField3SpecAt A (d + 1) (fun x => x.wt = .lengthDelimited))) := by
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold skipField3SpecAt
    simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
      sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hlen_lt : bs.length < 2 ^ 63 := by assumption
  have hwt_eq : wt = .lengthDelimited := by assumption
  subst hwt_eq
  have hx0_wt : BitVec.setWidth 8 (s0.readReg64 (Reg.gpr 0#5)) = BitVec.ofNat 8 WireType.lengthDelimited.toNat := by assumption
  have hx3_d : BitVec.setWidth 32 (s0.readReg64 (Reg.gpr 3#5)) = BitVec.ofNat 32 (d + 1) := by assumption
  have hcbz := cbz_depth_succ hx3_d hdepth
  have hw0 := w0_and_255_eq hx0_wt
  dsimp [WireType.toNat] at hw0
  rw [skipField_succ_lengthDelimited]
  apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 515) hcl0
  conv => arg 4; rw [skipBelow3_leaf s0.sp (d + 1) hdepth]
  wp_steps
  wp_reach
  intro hcl1
  refine SepWPp.call_frame_lscl (spec := decodeVarint2SpecX A)
    (x := ⟨bufRef, slot, ptr, bs⟩)
    (ret_pc := (blkPl_507).base + 160#64) hVarintCall hcl1
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [decodeVarint2SpecX, arm64_norm]; rfl)
    (⟨rfl, hlen_lt⟩ : bufRef = bufRef ∧ bs.length < 2 ^ 63)
    (by simp only [sliceCursorAt]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hcl2
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
  dsimp only [decodeVarint2SpecX]
  cases hd : decodeVarint bs with
  | none =>
    apply SepWPp.of_sepWP_ret
    simp only [sepConj_assoc, arm64_norm]
    apply SepWP.pure_elim; intro hsm0
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps
    wp_done
  | some p =>
    rcases p with ⟨len, rest⟩
    have hrest_le : rest.length ≤ bs.length := Nat.le_of_lt (decodeVarint_length hd)
    have hrest_lt : rest.length < 2 ^ 63 := by omega
    by_cases hlt : rest.length < len.toNat
    · have hule := ule_len_of_lt hlt hrest_lt
      simp only [skipBytes, hlt, ↓reduceIte, sliceCursorAfter, sepConj_assoc, arm64_norm]
      apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl2
      apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
      conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro v_err0
      wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
      conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth, ← hspm]
      wp_reach
      intro hcl3
      refine SepWPp.call_frame_lscl (spec := decodeErrorFromSpecWithStack A decodeErrorHookStackX)
        (x := (s0.sp - 96#64, 0x8000000000000007#64))
        (ret_pc := (blkPl_507).base + 204#64) hFromCall hcl3
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
        (by simp only [arm64_norm])
        (by simp only [decodeErrorFromSpecWithStack, arm64_norm]; rfl)
        (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64)
        (by sep_focus)
        (fun _ _ _ _ hex => allowPanic_not_exited hex)
        (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm]) hpan) ?_
      intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _hcl4
      simp only [CalleeSavedPreserved] at hcsm2
      obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩ := hcsm2
      simp (config := { decide := true }) only [arm64_norm, hspm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs] at hpcm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
      apply SepWPp.of_sepWP_ret
      dsimp only [decodeErrorFromSpecWithStack]
      simp only [arm64_norm, htrm, hspm]
      apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
      wp_steps
      wp_done
    · have hule := ule_len_of_ge hlt hrest_lt
      have hsub := bv_len_sub_skip hlt
      have hadd := bv_ptr_add_skip (ptr := ptr) hrest_le hlt
      simp only [skipBytes, hlt, ↓reduceIte, sliceCursorAfter, sepConj_assoc, arm64_norm]
      apply SepWPp.of_sepWP_ret
      apply SepWP.pure_elim; rintro ⟨hsm0, hsm1⟩
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
      wp_steps
      wp_done

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
