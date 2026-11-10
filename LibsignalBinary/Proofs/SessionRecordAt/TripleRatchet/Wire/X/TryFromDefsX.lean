/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Wire.X.CalleesW
public import LibsignalBinary.Proofs.CodeLayout
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX
import ProofLib.SepLogic.WPFrozen

/-!
# Callee Wrappers for `SignalMessage::try_from`

Page-aligned ADRP helper, `handle_alloc_error` panic-stub lookup, and caller-relative callee
transfer lemmas for `SignalMessage::try_from` on `contractProg img.base ext` and under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet.WireX

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.X
open CryptoVerification.LibsignalTripleRatchet.Getters

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

theorem L1_TryFromDefsX : True := trivial

/-! ## Page-aligned ADRP helper for `try_from` (second page) -/

theorem fnAddr_tryFrom_adrpX {b : BitVec 64} {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) {k : BitVec 64}
    (hk : (bv% (ls_off% "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from") + k) &&& 0xfffffffffffff000#64 = bv% (page% (ls_off% "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from")) := by rfl) :
    (((contractProg b ext).fnAddr tryFromName + k) &&&
      0xfffffffffffff000#64) = b + bv% (page% (ls_off% "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from")) := by
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from"), BitVec.add_assoc,
    adrp_page_of_aligned hb, hk]

/-! ## Panic-stub lookup -/

/-- The `alloc::alloc::handle_alloc_error` stub panics on `contractProg b ext`. -/
theorem panic_at_handle_alloc_errorX {b : BitVec 64} {ext : String → Option (State → State)}
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "alloc::alloc::handle_alloc_error" := by fnoff_eq) :
    (contractProg b ext).externAt? ((contractProg b ext).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_panicSymbol (hname := "alloc::alloc::handle_alloc_error") rfl hk
    (by fnoff_eq)
    (by fnoff_eq) (by simp [Rust.isPanicSymbol])

/-! ## Caller-relative callee obligations -/

theorem decodeErrorFrom_ok_atX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : DecodeErrorFromOkW img A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff decodeErrorFromName := by fnoff_eq) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((decodeErrorFromSpecX A).inImage img) := by
  rw [← Program.fnAddr_rel rfl rfl hk]; exact h

theorem decodeErrorPush_ok_atX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : DecodeErrorPushOkW img A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff decodeErrorPushName := by fnoff_eq) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((decodeErrorPushSpecX A).inImage img) := by
  rw [← Program.fnAddr_rel rfl rfl hk]; exact h

theorem decodeVarintSlow_ok_atX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : DecodeVarintSlowOkW img A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff varintSlowName := by fnoff_eq) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((decodeVarintSlowSpecX A).inImage img) := by
  rw [← Program.fnAddr_rel rfl rfl hk]; exact h

theorem decodeVarintSlice_ok_atX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : DecodeVarintSliceOkW img A ext)
    {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "prost::encoding::varint::decode_varint_slice")) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((decodeVarintSliceSpecW A).inImage img) := by
  rw [← Program.fnAddr_rel hfn (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slice") hk]; exact h

theorem int32Merge_ok_atX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : Int32MergeOkW img A ext)
    {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>")) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((int32MergeSpecW A).inImage img) := by
  rw [← Program.fnAddr_rel hfn (ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>") hk]; exact h

theorem skipField_ok_atX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : SkipFieldOkW img A ext)
    {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]")) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((skipFieldSpecW A).inImage img) := by
  rw [← Program.fnAddr_rel hfn (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#1]") hk]; exact h

theorem dropDecodeError_ok_atX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : DropDecodeErrorOkW img A ext)
    {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]")) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((dropDecodeErrorSpecW A).inImage img) := by
  rw [← Program.fnAddr_rel hfn (ls_lemma% fnOff "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]") hk]; exact h

theorem bytesMerge_ok_atX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : BytesMergeOkW img A ext)
    {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (bytesMergeSpecW A img) := by
  rw [← Program.fnAddr_rel hfn (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") hk]; exact h

theorem dropSpe_ok_atX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : DropSpeOkW img A ext)
    {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]")) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((dropSpeSpecX A).inImage img) := by
  rw [← Program.fnAddr_rel hfn (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]") hk]; exact h

theorem intoBoxedSlice_ok_atX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : IntoBoxedSliceOkW img A ext)
    {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice")) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((intoBoxedSliceSpecX A).inImage img) := by
  rw [← Program.fnAddr_rel hfn (ls_lemma% fnOff "<alloc::vec::Vec<u8>>::into_boxed_slice") hk]; exact h

theorem tryCloneFromRef_ok_atX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : TryCloneFromRefOkW img A ext)
    {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((tryCloneFromRefSpecX A).inImage img) := by
  rw [← Program.fnAddr_rel hfn (ls_lemma% fnOff "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in") hk]; exact h

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/

section Placed

open CryptoVerification

set_option maxRecDepth 2000000

/-- Wrap `spec` with `⌜LibsignalCodeRoLoaded pl ·.mem⌝` in both precondition and postcondition
(definitionally equal to `StoreKit.withLsRoCl`). -/
abbrev withLsRoClW {α : Type} (pl : Obj.MultiPlacement) (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s0 => spec.pre x s0 ∗ ⌜CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded pl s0.mem⌝
    post := fun x s0 sf => ⌜CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded pl sf.mem⌝ ∗ spec.post x s0 sf }

/-- Mangled extern symbol for `alloc::alloc::handle_alloc_error`. -/
abbrev lsHandleAllocErrorSymW : String :=
  "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error"

/-- Transfer `subroutine_ok calleeProg entry (withLsCodeRoLoaded lsmpl spec)` from block `j` to any
caller block `i`'s `callerProg` (preserving `withLsCodeRoLoaded`), without requiring `i < 619`. -/
theorem ls_subroutine_ok_cro_of_callee [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl spec))
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hfr0, _⟩ := CryptoVerification.LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  have hQL : calleeProg.CodeLoaded s0.mem :=
    hcallee_prog.eq_blockProgram ▸ hfr0.1 j (Nat.lt_of_lt_of_le hj (by decide)) hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

/-- Transfer `subroutine_ok calleeProg entry (withLsCodeRoLoaded lsmpl spec)` from block `j` to any
caller block `i`'s `callerProg` in `withLsRoClW` form, without requiring `i < 619`. -/
theorem ls_subroutine_ok_rocl_of_callee [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl spec))
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsRoClW lsmpl spec) := by
  have h0 := ls_subroutine_ok_cro_of_callee (callerProg := callerProg) hcallee hj hj_unmut
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  have ⟨hcrl0, _⟩ := CryptoVerification.LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  obtain ⟨sf, hsteps, hout, -⟩ := h0.no_fault_before_outcome x R s0 hpc hrun hpre hsp hL
  have hcrlf := hcrl0.of_keepsFrozen hsteps.keepsFrozen
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsRoClW]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcrlf, hpost⟩
  · exact Or.inr hrest

/-- Resolve `handle_alloc_error` panic stub on any caller block program `callerProg`. -/
theorem panic_at_handle_alloc_error_placed [LibsignalPlacement]
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hpan : H lsHandleAllocErrorSymW = some Rust.panicked) :
    callerProg.externAt? (lsρ lsHandleAllocErrorSymW) = some Rust.panicked :=
  (ls_externAt?_of_caller (sym := lsHandleAllocErrorSymW)).trans hpan

theorem decodeErrorFrom_placed_ok_cl [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h : DecodeErrorFromPlacedOkW A H) :
    subroutine_ok callerProg (lsmpl.base 261) (withLsCl lsmpl (decodeErrorFromSpecX A)) :=
  ls_subroutine_ok_cl_of_callee h

theorem decodeErrorPush_placed_ok_cl [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h : DecodeErrorPushPlacedOkW A H) :
    subroutine_ok callerProg (lsmpl.base 257) (withLsCl lsmpl (decodeErrorPushSpecX A)) :=
  ls_subroutine_ok_cl_of_callee h

theorem decodeVarintSlow_placed_ok_cl [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h : DecodeVarintSlowPlacedOkW A H) :
    subroutine_ok callerProg (lsmpl.base 293) (withLsCl lsmpl (decodeVarintSlowSpecX A)) :=
  ls_subroutine_ok_cl_of_callee h

theorem decodeVarintSlice_placed_ok_cl [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h : DecodeVarintSlicePlacedOkW A H) :
    subroutine_ok callerProg (lsmpl.base 76) (withLsCl lsmpl (decodeVarintSliceSpecW A)) :=
  ls_subroutine_ok_cl_of_callee h

theorem int32Merge_placed_ok_cl [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h : Int32MergePlacedOkW A H) :
    subroutine_ok callerProg (lsmpl.base 8) (withLsCl lsmpl (int32MergeSpecW A)) :=
  ls_subroutine_ok_cl_of_callee h

theorem skipField_placed_ok_cl [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h : SkipFieldPlacedOkW A H) :
    subroutine_ok callerProg (lsmpl.base 1) (withLsCl lsmpl (skipFieldSpecW A)) :=
  ls_subroutine_ok_cl_of_callee h

theorem dropDecodeError_placed_ok_cl [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h : DropDecodeErrorPlacedOkW A H) :
    subroutine_ok callerProg (lsmpl.base 4) (withLsCl lsmpl (dropDecodeErrorSpecW A)) :=
  ls_subroutine_ok_cl_of_callee h

theorem bytesMerge_placed_ok_cro [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h : BytesMergePlacedOkW A H) :
    subroutine_ok callerProg (lsmpl.base 7) (bytesMergePlacedSpecW A) :=
  ls_subroutine_ok_cro_of_callee h

theorem bytesMerge_placed_ok_rocl [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h : BytesMergePlacedOkW A H) :
    subroutine_ok callerProg (lsmpl.base 7) (withLsRoClW lsmpl (bytesMergeRawSpecW A)) :=
  ls_subroutine_ok_rocl_of_callee h

theorem dropSpe_placed_ok_cl [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h : DropSpePlacedOkW A H) :
    subroutine_ok callerProg (lsmpl.base 5) (withLsCl lsmpl (dropSpeSpecX A)) :=
  ls_subroutine_ok_cl_of_callee h

theorem intoBoxedSlice_placed_ok_cl [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h : IntoBoxedSlicePlacedOkW A H) :
    subroutine_ok callerProg (lsmpl.base 56) (withLsCl lsmpl (intoBoxedSliceSpecX A)) :=
  ls_subroutine_ok_cl_of_callee h

theorem tryCloneFromRef_placed_ok_cl [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h : TryCloneFromRefPlacedOkW A H) :
    subroutine_ok callerProg (lsmpl.base 23) (withLsCl lsmpl (tryCloneFromRefSpecX A)) :=
  ls_subroutine_ok_cl_of_callee h

end Placed

end CryptoVerification.LibsignalTripleRatchet.WireX
