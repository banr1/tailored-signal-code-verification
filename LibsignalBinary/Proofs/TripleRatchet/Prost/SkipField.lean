/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmas
public import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.BranchesX
public import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.StartGroupX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Prost

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero


theorem skipField_at_depth_ok_x {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipFieldName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    (hSlowCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipFieldName + bv% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
      ((decodeVarintSlowSpecX A).inImage img))
    (hSliceCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipFieldName + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
      ((decodeVarintSliceSpecX A).inImage img))
    (depth : Nat) (hdepth : depth < 2 ^ 32) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipFieldName)
      ((skipFieldSpecAtX A depth (fun _ => True)).inImage img) := by
  induction depth with
  | zero => exact skipField_depth_zero_ok_x hFromCall
  | succ d ih =>
    have hrec := ih (by omega)
    have hAll :=
      subroutine_ok_skipFieldX_or (skipField_varint_ok_x hFromCall hSlowCall hSliceCall d hdepth)
        (subroutine_ok_skipFieldX_or (skipField_sixtyFourBit_ok_x hFromCall d hdepth)
          (subroutine_ok_skipFieldX_or (skipField_lengthDelimited_ok_x hFromCall hSlowCall hSliceCall d hdepth)
            (subroutine_ok_skipFieldX_or (skipField_startGroup_ok_x hFromCall hSlowCall hSliceCall d hdepth hrec)
              (subroutine_ok_skipFieldX_or (skipField_endGroup_ok_x hFromCall d hdepth)
                (skipField_thirtyTwoBit_ok_x hFromCall d hdepth)))))
    refine subroutine_ok_skipFieldX_imp (fun x _ => ?_) hAll
    cases x.wt <;> simp

theorem skipField_at_depth_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromSpecWithStack A decodeErrorHookStackX)))
    (hSlowCall : subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (lsmpl.base 293)
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpecX A)))
    (hSliceCall : subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (lsmpl.base 76)
      (withLsCodeLoaded lsmpl (decodeVarintSliceSpecX A)))
    (depth : Nat) (hdepth : depth < 2 ^ 32) :
    subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (blkPl_1).base
      (withLsCodeLoaded lsmpl (skipFieldSpecAtX A depth (fun _ => True))) := by
  induction depth with
  | zero => exact skipField_depth_zero_placed_ok_x hFromCall
  | succ d ih =>
    have hrec := ih (by omega)
    have hAll :=
      subroutine_ok_skipFieldX_or_lscl (skipField_varint_placed_ok_x hFromCall hSlowCall hSliceCall d hdepth)
        (subroutine_ok_skipFieldX_or_lscl (skipField_sixtyFourBit_placed_ok_x hFromCall d hdepth)
          (subroutine_ok_skipFieldX_or_lscl (skipField_lengthDelimited_placed_ok_x hFromCall hSlowCall hSliceCall d hdepth)
            (subroutine_ok_skipFieldX_or_lscl (skipField_startGroup_placed_ok_x hFromCall hSlowCall hSliceCall d hdepth hrec)
              (subroutine_ok_skipFieldX_or_lscl (skipField_endGroup_placed_ok_x hFromCall d hdepth)
                (skipField_thirtyTwoBit_placed_ok_x hFromCall d hdepth)))))
    refine subroutine_ok_skipFieldX_imp_lscl (fun x _ => ?_) hAll
    cases x.wt <;> simp

namespace SkipFieldCalls

theorem skipFieldSpecAtX_reaches_outcome_eq (prog : Program) (img : Obj.Image) (A : RustAlloc)
    (P : SkipFieldGhost → Prop) (x : SkipFieldGhost) (R : SepProp) (s0 : State) :
    reaches_outcome prog ((skipFieldSpecAtX A x.depth P).inImage img) x R s0 s0 =
      reaches_outcome prog ((skipFieldSpecX A).inImage img) x R s0 s0 := by
  have hpost : ((skipFieldSpecAtX A x.depth P).inImage img).post x = ((skipFieldSpecX A).inImage img).post x := by
    funext s0' sf'
    dsimp only [Spec.inImage, skipFieldSpecAtX, skipFieldSpecX]
    cases skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs <;> rfl
  have hpan : ((skipFieldSpecAtX A x.depth P).inImage img).onPanic x = ((skipFieldSpecX A).inImage img).onPanic x := rfl
  have hexit : ((skipFieldSpecAtX A x.depth P).inImage img).onExit x = ((skipFieldSpecX A).inImage img).onExit x := rfl
  have hoom : ((skipFieldSpecAtX A x.depth P).inImage img).onOom x = ((skipFieldSpecX A).inImage img).onOom x := rfl
  have hout : ∀ sf,
      SubroutineOutcome ((skipFieldSpecAtX A x.depth P).inImage img) x R s0 sf =
      SubroutineOutcome ((skipFieldSpecX A).inImage img) x R s0 sf := by
    intro sf; dsimp only [SubroutineOutcome]; rw [hpost, hpan, hexit, hoom]
  exact propext ⟨fun h => h.mono_outcome (fun sf hs => hout sf ▸ hs),
    fun h => h.mono_outcome (fun sf hs => (hout sf).symm ▸ hs)⟩

theorem subroutine_ok_skipFieldSpecX_of_at_depth {prog : Program} {entry : BitVec 64} {img : Obj.Image} {A : RustAlloc}
    (h : ∀ depth, depth < 2 ^ 32 → subroutine_ok prog entry ((skipFieldSpecAtX A depth (fun _ => True)).inImage img)) :
    subroutine_ok prog entry ((skipFieldSpecX A).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpre' := hpre
  simp only [Spec.inImage, skipFieldSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  have hdepth : x.depth < 2 ^ 32 := hpre'.2.1.2.2.2.2.2.1
  rw [← skipFieldSpecAtX_reaches_outcome_eq prog img A (fun _ => True) x R s0]
  refine (h x.depth hdepth).to_outcome x R s0 hpc hrun ?_ hsp
  simp only [Spec.inImage, skipFieldSpecAtX, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpre'.1, ⟨trivial, trivial, hpre'.2.1⟩, hpre'.2.2⟩

theorem skipFieldSpecAtX_reaches_outcome_eq_lscl [LibsignalPlacement] (prog : Program) (A : RustAlloc)
    (P : SkipFieldGhost → Prop) (x : SkipFieldGhost) (R : SepProp) (s0 : State) :
    reaches_outcome prog (withLsCodeLoaded lsmpl (skipFieldSpecAtX A x.depth P)) x R s0 s0 =
      reaches_outcome prog (withLsCodeLoaded lsmpl (skipFieldSpecX A)) x R s0 s0 := by
  have hpost : (withLsCodeLoaded lsmpl (skipFieldSpecAtX A x.depth P)).post x = (withLsCodeLoaded lsmpl (skipFieldSpecX A)).post x := by
    funext s0' sf'
    dsimp only [withLsCodeLoaded, skipFieldSpecAtX, skipFieldSpecX]
    cases skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs <;> rfl
  have hpan : (withLsCodeLoaded lsmpl (skipFieldSpecAtX A x.depth P)).onPanic x = (withLsCodeLoaded lsmpl (skipFieldSpecX A)).onPanic x := rfl
  have hexit : (withLsCodeLoaded lsmpl (skipFieldSpecAtX A x.depth P)).onExit x = (withLsCodeLoaded lsmpl (skipFieldSpecX A)).onExit x := rfl
  have hoom : (withLsCodeLoaded lsmpl (skipFieldSpecAtX A x.depth P)).onOom x = (withLsCodeLoaded lsmpl (skipFieldSpecX A)).onOom x := rfl
  have hout : ∀ sf,
      SubroutineOutcome (withLsCodeLoaded lsmpl (skipFieldSpecAtX A x.depth P)) x R s0 sf =
      SubroutineOutcome (withLsCodeLoaded lsmpl (skipFieldSpecX A)) x R s0 sf := by
    intro sf; dsimp only [SubroutineOutcome]; rw [hpost, hpan, hexit, hoom]
  exact propext ⟨fun h => h.mono_outcome (fun sf hs => hout sf ▸ hs),
    fun h => h.mono_outcome (fun sf hs => (hout sf).symm ▸ hs)⟩

theorem subroutine_ok_skipFieldSpecX_of_at_depth_lscl [LibsignalPlacement] {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (h : ∀ depth, depth < 2 ^ 32 → subroutine_ok prog entry (withLsCodeLoaded lsmpl (skipFieldSpecAtX A depth (fun _ => True)))) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl (skipFieldSpecX A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpre' := hpre
  simp only [skipFieldSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  have hdepth : x.depth < 2 ^ 32 := hpre'.1.2.2.2.2.2.1
  rw [← skipFieldSpecAtX_reaches_outcome_eq_lscl prog A (fun _ => True) x R s0]
  refine (h x.depth hdepth).to_outcome x R s0 hpc hrun ?_ hsp
  simp only [skipFieldSpecAtX, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨trivial, trivial, hpre'.1⟩, hpre'.2⟩

end SkipFieldCalls

theorem skipField_ok_of_contracts_x {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipFieldName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    (hSlowCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipFieldName + bv% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
      ((decodeVarintSlowSpecX A).inImage img))
    (hSlice : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr decodeVarintSliceName)
      ((decodeVarintSliceSpecX A).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipFieldName)
      ((skipFieldSpecX A).inImage img) := by
  have hSliceCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipFieldName + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
      ((decodeVarintSliceSpecX A).inImage img) := by
    rw [fnAddr_rebase_offset (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#1]") (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slice") (by decide)]
    exact hSlice
  exact SkipFieldCalls.subroutine_ok_skipFieldSpecX_of_at_depth
    (skipField_at_depth_ok_x hFromCall hSlowCall hSliceCall)

theorem skipField_ok_ext_x {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsX img C A encFn decFn ext) :
    SkipFieldOkExtX img A ext :=
  skipField_ok_of_contracts_x
    (decodeErrorFromSpecWithStack_inImage_mono (s2 := decodeErrorHookStackX)
      (hC.decode_error_from_ok_at skipFieldName (num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
        (by fnoff_eq)))
    (decodeVarintSlowX_ok_at_ext hC (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#1]") (k := num% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]")) (by decide))
    (decodeVarintSlice_ok_ext_x hC)

theorem skipField_placed_ok_of_contracts_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromSpecWithStack A decodeErrorHookStackX))
    (hSlow : subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (blkPl_293).base
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpecX A)))
    (hSlice : subroutine_ok ((blkPC_76).rebase (blkPl_76).base H)
      (blkPl_76).base
      (withLsCodeLoaded lsmpl (decodeVarintSliceSpecX A))) :
    subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (blkPl_1).base
      (withLsCodeLoaded lsmpl (skipFieldSpecX A)) :=
  SkipFieldCalls.subroutine_ok_skipFieldSpecX_of_at_depth_lscl
    (skipField_at_depth_placed_ok_x
      (ls_subroutine_ok_of_block (callerProg := (blkPC_1).rebase (blkPl_1).base H)
        (subroutine_ok_withLsCodeLoaded_of_plain hFrom))
      (ls_subroutine_ok_of_block (callerProg := (blkPC_1).rebase (blkPl_1).base H) hSlow)
      (ls_subroutine_ok_of_block (callerProg := (blkPC_1).rebase (blkPl_1).base H) hSlice))

theorem skipField_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (blkPl_1).base
      (withLsCodeLoaded lsmpl (skipFieldSpecX A)) :=
  skipField_placed_ok_of_contracts_x
    (decode_error_from_placed_ok_x hshim halloc hpanic)
    (decode_varint_slow_placed_ok_x hshim halloc hpanic)
    (decode_varint_slice_placed_ok_x hshim halloc hpanic)

end CryptoVerification.LibsignalTripleRatchet.Prost

