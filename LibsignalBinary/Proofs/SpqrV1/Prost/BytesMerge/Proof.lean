/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Defs
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.BytesMergeCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Phase23Placed
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp

/-!
# `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]> [local#3]`: Verification

Top-level fixed-base (`0x4d13c`) and relocatable (`[LibsignalPlacement]`, Block `290`) verification
of `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]` against both
`LibsignalProtoCodec.mergeBytes` and `LibsignalSpqrV1.Proto.mergeBytes`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.BytesMerge

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Varint hiding decodeVarint2Name decodeVarint2_fnOff
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bytesMerge3_fnOff decodeVarint2_fnOff doReserve7_fnOff

/-! ## 1. `bytes::merge [local#3]` (`0x4d13c`) Specs -/

/-- Stack budget for `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]> [local#3]` (`0x4d13c`):
own frame `0xe0` (`224`) bytes plus `decodeVarint2Stack` (`8320` B) = `8544` B (`48 + bytesMergeStack`). -/
abbrev bytesMerge3Stack : Nat := 0xe0 + decodeVarint2Stack

/-- Raw contract of `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]`
(image offset `0x4d13c`, 228 instructions). -/
def bytesMerge3RawSpec (A : RustAlloc) : Spec BytesMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      BytesMergeCapOk x.valCap x.bs.length⌝ ∗
      vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp bytesMerge3Stack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗ stackAt s0.sp bytesMerge3Stack ∗
      match mergeBytes x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
            ⌜BytesMergeCapOk cap' rest.length⌝ ∗ vecU8At A x.valPtr cap' ptr' v) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Contract of `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]`
(`0x4d13c`) in a loaded image `img`. -/
def bytesMerge3Spec (A : RustAlloc) (img : Obj.Image) : Spec BytesMergeGhost :=
  (bytesMerge3RawSpec A).inImage img

/-- `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]` (`0x4d13c`)
meets `bytesMerge3Spec A img` on `tripleRatchetProgAtExt img.base ext`. -/
def BytesMerge3OkExt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name)
    (bytesMerge3Spec A img)

/-! ## 2. Stack Layout & `MergePost3` / `MergePanic3` Lifting Lemmas -/

theorem stackAt_varint2_to_slice (sp0 : BitVec 64) :
    stackAt (sp0 - 224#64) decodeVarint2Stack =
      memRegion (sp0 - 8544#64) 48 ∗ stackAt (sp0 - 224#64) decodeVarintSliceStack := by
  have h : sp0 - 224#64 - 8320#64 = sp0 - 8544#64 := by bv_omega
  rw [← h]
  exact stackAt_split_sub (sp0 - 224#64) 48 decodeVarintSliceStack (by decide)

theorem stackAt_bytesMerge3_eq (sp0 : BitVec 64) :
    stackAt sp0 bytesMerge3Stack =
      memRegion (sp0 - 8544#64) 48 ∗ stackAt sp0 bytesMergeStack := by
  exact stackAt_split_sub sp0 48 bytesMergeStack (by decide)

theorem stackAt_bytesMerge3_entry (sp0 : BitVec 64) :
    stackAt sp0 bytesMerge3Stack =
      stackAt (sp0 - 224#64) decodeVarint2Stack ∗
      memRegion (sp0 - 224#64) 8 ∗
      memRegion (sp0 - 216#64) 48 ∗
      memRegion (sp0 - 168#64) 104 ∗
      cells (sp0 - 64#64) 8 := by
  rw [stackAt_bytesMerge3_eq sp0, stackAt_bytesMerge_entry sp0, stackAt_varint2_to_slice sp0]
  ac_rfl

abbrev MergePost3 (A : RustAlloc) (x : BytesMergeGhost) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMerge3RawSpec A).post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev MergePanic3 (A : RustAlloc) (x : BytesMergeGhost) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMerge3RawSpec A).onPanic x s0 sf ∗ R)

theorem SepWPp.to_subroutineOutcome3 {prog : Program} {A : RustAlloc} {img : Obj.Image}
    {x : BytesMergeGhost} {s0 : State} {P R : SepProp}
    (_hsp_align : s0.spAligned = true)
    (hm : s0.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s0.mem)
    (h : SepWPp prog (s0.readReg64 .lr) s0 P (MergePost3 A x s0 R) (MergePanic3 A x s0 R)) :
    ∃ sf, Steps prog s0 sf ∧
      SubroutineOutcome (bytesMerge3Spec A img) x R s0 sf := by
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hfalse⟩⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpc, hsp, hrun⟩, ⟨hsp, hcs⟩, hpost hmf⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hpanic hmf⟩)⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

theorem SepWPp.lift_merge3 {prog : Program} {A : RustAlloc}
    {x : BytesMergeGhost} {s0 s : State} {P R : SepProp}
    (h : SepWPp prog (s0.readReg64 .lr) s P
      (MergePost A x s0 (memRegion (s0.sp - 8544#64) 48 ∗ R))
      (MergePanic A x s0 (memRegion (s0.sp - 8544#64) 48 ∗ R))) :
    SepWPp prog (s0.readReg64 .lr) s (memRegion (s0.sp - 8544#64) 48 ∗ P)
      (MergePost3 A x s0 R) (MergePanic3 A x s0 R) := by
  intro F hm hL
  have hm' : s.mem ⊨ P ∗ (memRegion (s0.sp - 8544#64) 48 ∗ F) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hfalse⟩⟩ :=
    h (memRegion (s0.sp - 8544#64) 48 ∗ F) hm' hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc, hrun, memRegion (s0.sp - 8544#64) 48 ∗ P_f,
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hmf, ?_, hsp, hcs⟩⟩
    intro hmr
    have hmr' : sf.mem ⊨ P_f ∗ (memRegion (s0.sp - 8544#64) 48 ∗ R) :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hmr
    have hp := hpost hmr'
    dsimp only [bytesMergeRawSpec, bytesMerge3RawSpec] at hp ⊢
    rw [stackAt_bytesMerge3_eq s0.sp]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hp
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, memRegion (s0.sp - 8544#64) 48 ∗ P_f,
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hmf, ?_⟩)⟩
    intro hmr
    have hmr' : sf.mem ⊨ P_f ∗ (memRegion (s0.sp - 8544#64) 48 ∗ R) :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hmr
    have hp := hpanic hmr'
    dsimp only [bytesMergeRawSpec, bytesMerge3RawSpec] at hp ⊢
    rw [← sepConj_assoc] at hp
    exact allowPanic_frame id hp
  · exact False.elim (not_satisfies_false_sepConj hfalse)

/-! ## 3. Phase 1 (`+0x000..+0x074`) and `bytes_merge_3_ok_ext` -/

/-- Generalized verification of `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]`
(`0x4d13c`) on any `libsignalSessionCode.rebase img.base H`. -/
theorem bytes_merge_3_ok_of_contracts {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hdef : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" + 0x10000000000000000 - 0x47d44))
      (decodeErrorFromSpec A))
    (hmc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + bv% (ls_off% "memcpy" - 0x47d44))
      framelessMemcpySpec)
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x47d44))
      noAllocShimSpec)
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + bv% (ls_off% "__rustc::__rust_alloc" - 0x47d44))
      (rustAllocSpec A))
    (hpanic : (libsignalSessionCode.rebase img.base H).externAt?
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x47d44)) =
      some Rust.panicked)
    (hDecodeVarint2 : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr decodeVarint2Name)
      ((decodeVarint2Spec A).inImage img))
    (hBytesFromVec : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img))
    (hReserve7 : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr doReserve7Name)
      (doReserveSpec A))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (libsignalSessionCode.rebase img.base H)
        (bytesDropFnAddr img.base tmpPtr v.length)
        ((bytesVtableDropSpec A tmpPtr v v.length).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name)
      (bytesMerge3Spec A img) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp_align hL => ?_
  rw [bytesMerge3Spec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hfl, hsym⟩, hpre⟩ := hpre
  rw [bytesMerge3RawSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hw0, hx1, hx2, hbs_len, hcapOk⟩, hm⟩ := hpre
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hcall_dv2 : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + 912#64)
      ((decodeVarint2Spec A).inImage img) := by
    rw [fnAddr_offset_eq_H (name := bytesMerge3Name) (callee := decodeVarint2Name) (k := 912#64)]
    exact hDecodeVarint2
  let R48 : SepProp := memRegion (s0.sp - 8544#64) 48 ∗ R
  have herr_exit := fun {s : State} (hmerge : mergeBytes x.wt x.bs = none) =>
    @epilogue3_err_0x07c img A H x s0 s R48 hmerge
  have hde_exit := fun (w : BitVec 64) (hw : KindNoHeap w) {s : State}
      (hmerge : mergeBytes x.wt x.bs = none) =>
    @epilogue3_decodeErrorFrom_0x074 img A H hdef x s0 s R48 w hw hmerge
  have h094_exit := fun (len : BitVec 64) (rest0 : List (BitVec 8)) {s : State}
      (hwt : x.wt = .lengthDelimited)
      (hvar : decodeVarint x.bs = some (len, rest0))
      (hle : len.toNat ≤ rest0.length) =>
    @phase2_from_0x094 img A H himg hmc hshim halloc hpanic hBytesFromVec hReserve7
      hVtableSlot hVtableDrop x s0 s R48 len rest0 hwt hvar hle hbs_len hcapOk
  clear hDecodeVarint2 hBytesFromVec hReserve7 hVtableDrop
  refine Exists.elim (SepWPp.to_subroutineOutcome3 (img := img) hsp_align hm hL ?_)
    fun _ ⟨hsteps, hout⟩ => reaches_outcome_steps hsteps (reaches_outcome.of_outcome hout)
  rw [stackAt_bytesMerge3_entry s0.sp]
  refine SepWPp.weaken_pre (P' := cells (s0.sp - 64#64) 8 ∗
    (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗
      stackAt (s0.sp - 224#64) decodeVarint2Stack ∗
      memRegion (s0.sp - 224#64) 8 ∗
      memRegion (s0.sp - 216#64) 48 ∗
      memRegion (s0.sp - 168#64) 104))
    (Entails.of_eq (by ac_rfl)) ?_
  refine SepWPp.unfold_cells_64 fun c0 c1 c2 c3 c4 c5 c6 c7 => ?_
  merge3_fetches_H img.base H bytesMerge3_fnOff 0 116
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name = entry
  examples_hide_fetches
  by_cases hwt : x.wt = .lengthDelimited
  · have hw0_br :
        (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      change (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x0)) &&& 255#64) != 2#32) = false
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, hw0, hwt]
      decide
    apply SepWPp.bm_of_sepWP_inv hfl hsym (mid := entry + 912#64)
    wp_steps
    apply SepWP.fold (show
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢
        savedRegsStack s0.sp s0 from Entails.refl _) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hfl1 hsym1
    refine SepWPp.bm_call_frame_inv
      (x := ({ bufRef := x.bufRef, slot := x.slot, ptr := x.ptr, bs := x.bs } : DecodeVarintSlowGhost))
      (T := (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarint2Stack)
      hcall_dv2 hfl1 hsym1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp_align]) rfl
      (by simp (config := { decide := true }) only [decodeVarint2Spec, arm64_norm])
      hbs_len
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sf _ hm => by
        simp only [bytesMerge3RawSpec, Spec.inImage, decodeVarint2Spec,
          State.trace_setPC, State.trace_writeReg64, allocFailedIn] at hm ⊢
        exact allowPanic_frame id hm) ?_
    intro sf_dv hpcf hrunf hspf hcsf hflf hsymf
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f, hvregsf⟩ := hcsf
    simp (config := { decide := true }) only [arm64_norm, hx1, hx2] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f hvregsf
    simp (config := { decide := true }) only [decodeVarint2Spec, wp_norm, arm64_norm]
    rw [stackAt_varint2_to_slice s0.sp]
    rcases hvar : decodeVarint x.bs with _ | ⟨len, rest0⟩
    · dsimp only
      have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_of_decodeVarint_none hvar
      refine SepWPp.weaken_pre (P' :=
        ⌜sf_dv.readReg64 .x0 = 1#64⌝ ∗ ⌜sf_dv.trace = s0.trace⌝ ∗ ⌜sf_dv.readReg64 .x1 ≠ 0#64⌝ ∗
          (memRegion (s0.sp - 8544#64) 48 ∗
            decodeErrorAtStackLen A (sf_dv.readReg64 .x1) 0 ∗
            vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
            (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
            stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
            memRegion (s0.sp - 224#64) 8 ∗
            memRegion (s0.sp - 216#64) 48 ∗
            memRegion (s0.sp - 168#64) 104 ∗
            savedRegsStack s0.sp s0))
        (Entails.of_eq (by
          dsimp only [savedRegsStack, Reg.x0, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x29, Reg.x30]
          ac_rfl)) ?_
      refine SepWPp.pure_elim fun hx0_sf => ?_
      refine SepWPp.pure_elim fun htr => ?_
      refine SepWPp.pure_elim fun hx1_sf => ?_
      apply SepWPp.bm_of_sepWP_inv hflf hsymf (mid := entry + 124#64)
      wp_steps
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      intro hfl2 hsym2
      exact SepWPp.lift_merge3 (herr_exit hmerge
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm]; exact hx1_sf)
        (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, and_self]))
    · dsimp only
      obtain ⟨pfx, hpfx⟩ := bm_decodeVarint_suffix hvar
      have hrest0_len : rest0.length ≤ x.bs.length := by rw [hpfx, List.length_append]; omega
      have hrest0_toNat : (BitVec.ofNat 64 rest0.length).toNat = rest0.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine SepWPp.weaken_pre (P' :=
        ⌜sf_dv.readReg64 .x0 = 0#64 ∧ sf_dv.readReg64 .x1 = len⌝ ∗ ⌜sf_dv.trace = s0.trace⌝ ∗
          (memRegion (s0.sp - 8544#64) 48 ∗
            vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
            (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
            stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
            memRegion (s0.sp - 224#64) 8 ∗
            memRegion (s0.sp - 216#64) 48 ∗
            memRegion (s0.sp - 168#64) 104 ∗
            savedRegsStack s0.sp s0))
        (Entails.of_eq (by
          dsimp only [savedRegsStack, Reg.x0, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x29, Reg.x30]
          ac_rfl)) ?_

      refine SepWPp.pure_elim fun ⟨hx0_sf, hx1_sf⟩ => ?_
      refine SepWPp.pure_elim fun htr => ?_
      dsimp only [sliceCursorAfter]
      apply SepWPp.bm_of_sepWP_inv hflf hsymf
        (mid := if len.ule (BitVec.ofNat 64 rest0.length) = true then entry + 148#64 else entry + 80#64)
      wp_steps
      apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length))) ∗
          ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗ (x.ptr ↦ₛ x.bs) ⊢
          sliceCursorAfter x.slot x.ptr x.bs rest0 from Entails.refl _) (by sep_focus)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      intro hfl2 hsym2
      by_cases hule : len.ule (BitVec.ofNat 64 rest0.length) = false
      · simp only [hule, Bool.false_eq_true, ↓reduceIte] at hfl2 hsym2 ⊢
        have hlt : rest0.length < len.toNat := by simp [BitVec.ule, hrest0_toNat] at hule; omega
        have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_lengthDelimited_underflow hwt hvar hlt
        refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 216#64) 48 ∗
          (memRegion (s0.sp - 8544#64) 48 ∗
            vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
            (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
            stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
            memRegion (s0.sp - 224#64) 8 ∗
            memRegion (s0.sp - 168#64) 104 ∗
            savedRegsStack s0.sp s0))
          (Entails.of_eq (by ac_rfl)) ?_
        refine SepWPp.unfold_memRegion_216 fun w216 => ?_
        apply SepWPp.bm_of_sepWP_inv hfl2 hsym2 (mid := entry + 116#64)
        wp_steps
        apply SepWP.fold (sliceCursorAfter_to_err x.slot x.ptr x.bs rest0) (by sep_focus)
        apply SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
        intro hfl3 hsym3
        refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3 (hde_exit 0x8000000000000007#64 (by simp [KindNoHeap]) hmerge
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
          hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, and_self])))
        exact Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm]; ac_rfl)
      · have hule_eq : len.ule (BitVec.ofNat 64 rest0.length) = true :=
          Bool.eq_true_of_not_eq_false hule
        simp only [hule_eq, ↓reduceIte] at hfl2 hsym2 ⊢
        have hle : len.toNat ≤ rest0.length := by simpa [BitVec.ule, hrest0_toNat] using hule_eq
        refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3 (h094_exit len rest0 hwt hvar hle
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule_eq])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
          hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, and_self])
          hfl2 hsym2
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1_sf])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29f])))
        exact Entails.of_eq (by ac_rfl)
  · have hw0_br :
        (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      change (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x0)) &&& 255#64) != 2#32) = true
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, hw0]
      cases hxwt : x.wt <;> simp_all [WireType.toNat]
    have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_ne_lengthDelimited hwt
    dsimp only [sliceCursorAt]
    rw [stackAt_varint2_to_slice s0.sp]
    refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 216#64) 48 ∗
      (memRegion (s0.sp - 8544#64) 48 ∗
        ((s0.sp - 64#64) ↦₆₄ c0) ∗ ((s0.sp - 56#64) ↦₆₄ c1) ∗
        ((s0.sp - 48#64) ↦₆₄ c2) ∗ ((s0.sp - 40#64) ↦₆₄ c3) ∗
        ((s0.sp - 32#64) ↦₆₄ c4) ∗ ((s0.sp - 24#64) ↦₆₄ c5) ∗
        ((s0.sp - 16#64) ↦₆₄ c6) ∗ ((s0.sp - 8#64) ↦₆₄ c7) ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗
        ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
        (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104)) (Entails.of_eq (by ac_rfl)) ?_
    refine SepWPp.unfold_memRegion_216_invalidWireType fun w0_216 b0_216 b1_216 => ?_
    apply SepWPp.bm_of_sepWP_inv hfl hsym (mid := entry + 116#64)
    wp_steps
    apply SepWP.fold (fold_memRegion_40_bytes (s0.sp - 216#64)
      (BitVec.ofNat 8 x.wt.toNat) 2#8) (by sep_focus)
    apply SepWP.fold (fold_slot_16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (show
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢
        savedRegsStack s0.sp s0 from Entails.refl _) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br, hw0, mask_ff_32_of_setWidth8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hfl1 hsym1
    refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3 (hde_exit 0x8000000000000006#64 (by simp [KindNoHeap]) hmerge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br, hw0, mask_ff_32_of_setWidth8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, and_self])))
    exact Entails.of_eq (by dsimp only [savedRegsStack]; simp (config := { decide := true }) only [arm64_norm]; ac_rfl)

/-- `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]` (`0x4d13c`) meets `bytesMerge3Spec A img` on `tripleRatchetProgAtExt img.base ext`. -/
theorem bytes_merge_3_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hAlloc : AllocContracts img.base A ext)
    (hDecodeErrorFrom : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName) (decodeErrorFromSpec A))
    (hDecodeVarint2 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeVarint2Name)
      ((decodeVarint2Spec A).inImage img))
    (hBytesFromVec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img))
    (hReserve7 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve7Name) (doReserveSpec A))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        (bytesDropFnAddr img.base tmpPtr v.length)
        ((bytesVtableDropSpec A tmpPtr v v.length).inImage img)) :
    BytesMerge3OkExt img A ext := by
  have hdef : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" + 0x10000000000000000 - 0x47d44))
      (decodeErrorFromSpec A) := by
    rw [fnAddr_offset_eq_H (name := bytesMerge3Name) (callee := decodeErrorFromName)]
    exact hDecodeErrorFrom
  exact bytes_merge_3_ok_of_contracts himg hdef
    (hAlloc.session_memcpy_region_ok_at bytesMerge3Name (num% (ls_off% "memcpy" - 0x47d44)))
    (hAlloc.shim_ok_at bytesMerge3Name (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x47d44)))
    (hAlloc.alloc_ok_at bytesMerge3Name (num% (ls_off% "__rustc::__rust_alloc" - 0x47d44)))
    (panic_at_handle_error_ext img.base ext bytesMerge3Name (num% (ls_off% "alloc::raw_vec::handle_error" - 0x47d44)))
    hDecodeVarint2 hBytesFromVec hReserve7 hVtableSlot hVtableDrop

/-! ## 4. Equivalence with `LibsignalSpqrV1.Proto.mergeBytes` (`Proto.lean`) -/

/-- Bijection from `LibsignalSpqrV1.Proto.WireType` to `LibsignalProtoCodec.WireType`. -/
def protoWireTypeToCodec : LibsignalSpqrV1.Proto.WireType → WireType
  | .varint => .varint
  | .SixtyFourBit => .sixtyFourBit
  | .lengthDelimited => .lengthDelimited
  | .startGroup => .startGroup
  | .endGroup => .endGroup
  | .ThirtyTwoBit => .thirtyTwoBit

@[simp]
theorem protoWireTypeToCodec_toNat (wt : LibsignalSpqrV1.Proto.WireType) :
    BitVec.ofNat 8 (protoWireTypeToCodec wt).toNat = wt.toU32.setWidth 8 := by
  cases wt <;> rfl

theorem proto_takeExact_toOption (n : Nat) (bs : List (BitVec 8)) :
    (LibsignalSpqrV1.Proto.takeExact n bs).toOption =
      if bs.length < n then none else some (bs.take n, bs.drop n) := by
  induction n generalizing bs with
  | zero =>
    simp [LibsignalSpqrV1.Proto.takeExact, Except.toOption]
  | succ n ih =>
    cases bs with
    | nil =>
      simp [LibsignalSpqrV1.Proto.takeExact, Except.toOption]
    | cons b rest =>
      have hbind : (LibsignalSpqrV1.Proto.takeExact (n + 1) (b :: rest)).toOption =
          ((LibsignalSpqrV1.Proto.takeExact n rest).toOption).map (fun p => (b :: p.1, p.2)) := by
        simp only [LibsignalSpqrV1.Proto.takeExact]
        rcases LibsignalSpqrV1.Proto.takeExact n rest with _ | ⟨hd, tl⟩ <;> rfl
      rw [hbind, ih]
      by_cases hlt : rest.length < n
      · have hlt' : (b :: rest).length < n + 1 := by simp; omega
        simp [hlt, hlt']
      · have hlt' : ¬ (b :: rest).length < n + 1 := by simp; omega
        simp [hlt, hlt']

private theorem bitvec8_lt_0x80_iff (b : BitVec 8) :
    (b < 0x80#8) ↔ b.toNat ≤ 0x7F := by
  revert b; apply BytesMergeFacts.bitvec8_forall; decide

private theorem bitvec8_ge_0x02_iff (b : BitVec 8) :
    (b ≥ 0x02#8) ↔ 0x02 ≤ b.toNat := by
  revert b; apply BytesMergeFacts.bitvec8_forall; decide

theorem proto_decodeVarintAux_toOption (fuel idx : Nat) (acc : BitVec 64) (bs : List (BitVec 8))
    (hfuel : fuel + idx = 10) (hidx : idx < 10) :
    (LibsignalSpqrV1.Proto.decodeVarintAux fuel idx acc bs).toOption = decodeVarintAux idx acc bs := by
  induction fuel generalizing idx acc bs with
  | zero => omega
  | succ fuel ih =>
    cases bs with
    | nil =>
      simp [LibsignalSpqrV1.Proto.decodeVarintAux, decodeVarintAux, Except.toOption]
    | cons b rest =>
      have hshift : ((b &&& 0x7f#8).zeroExtend 64 <<< (idx * 7)) =
          ((b &&& 0x7F).zeroExtend 64 <<< (7 * idx)) := by
        rw [Nat.mul_comm]
        rfl
      by_cases h9 : idx = 9
      · subst h9
        have hfuel0 : fuel = 0 := by omega
        subst hfuel0
        simp only [LibsignalSpqrV1.Proto.decodeVarintAux, decodeVarintAux, beq_self_eq_true, ↓reduceIte, true_and]
        by_cases hb2 : 0x02 ≤ b.toNat
        · have hb2' : b ≥ 0x02#8 := (bitvec8_ge_0x02_iff b).mpr hb2
          simp [hb2, hb2', Except.toOption]
        · have hb2' : ¬ (b ≥ 0x02#8) := fun h => hb2 ((bitvec8_ge_0x02_iff b).mp h)
          have hb_lt : b.toNat ≤ 0x7F := by
            change ¬ (2 ≤ b.toNat) at hb2
            omega
          simp [hb2, hb2', hb_lt, Except.toOption]
      · have h9_beq : (idx == 9) = false := beq_false_of_ne h9
        simp only [LibsignalSpqrV1.Proto.decodeVarintAux, decodeVarintAux, h9_beq, Bool.false_eq_true, ↓reduceIte, h9, false_and, hshift]
        by_cases hlt : b.toNat ≤ 0x7F
        · have hlt' : b < 0x80#8 := (bitvec8_lt_0x80_iff b).mpr hlt
          simp [hlt, hlt', Except.toOption]
        · have hlt' : ¬ (b < 0x80#8) := fun h => hlt ((bitvec8_lt_0x80_iff b).mp h)
          simp only [hlt, hlt', ↓reduceIte]
          exact ih (idx + 1) (acc ||| ((b &&& 0x7F).zeroExtend 64 <<< (7 * idx))) rest (by omega) (by omega)

@[simp]
theorem proto_decodeVarint_toOption (bs : List (BitVec 8)) :
    (LibsignalSpqrV1.Proto.decodeVarint bs).toOption = decodeVarint bs :=
  proto_decodeVarintAux_toOption 10 0 0#64 bs rfl (by decide)

@[simp]
theorem proto_mergeBytes_toOption (wt : LibsignalSpqrV1.Proto.WireType) (bs : List (BitVec 8)) :
    (LibsignalSpqrV1.Proto.mergeBytes wt bs).toOption = mergeBytes (protoWireTypeToCodec wt) bs := by
  cases wt <;> simp only [LibsignalSpqrV1.Proto.mergeBytes, LibsignalSpqrV1.Proto.checkWireType, protoWireTypeToCodec, mergeBytes]
  case lengthDelimited =>
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
    rcases hdv : LibsignalSpqrV1.Proto.decodeVarint bs with err | ⟨len, rest⟩
    · have hdv' : decodeVarint bs = none := by
        rw [← proto_decodeVarint_toOption bs, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
    · have hdv' : decodeVarint bs = some (len, rest) := by
        rw [← proto_decodeVarint_toOption bs, hdv]; rfl
      simp only [hdv', Bind.bind, Except.bind, proto_takeExact_toOption]
  all_goals rfl

/-- Ghost input for `bytesMerge3ProtoRawSpec`, parameterized directly by `LibsignalSpqrV1.Proto.WireType`. -/
structure BytesMergeProtoGhost where
  wt : LibsignalSpqrV1.Proto.WireType
  valPtr : BitVec 64
  valCap : BitVec 64
  valBuf : BitVec 64
  valBs : List (BitVec 8)
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

def BytesMergeProtoGhost.toCodec (x : BytesMergeProtoGhost) : BytesMergeGhost :=
  { wt := protoWireTypeToCodec x.wt
    valPtr := x.valPtr
    valCap := x.valCap
    valBuf := x.valBuf
    valBs := x.valBs
    bufRef := x.bufRef
    slot := x.slot
    ptr := x.ptr
    bs := x.bs }

/-- Raw contract of `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]`
(`0x4d13c`) stated directly in terms of `LibsignalSpqrV1.Proto.mergeBytes`. -/
def bytesMerge3ProtoRawSpec (A : RustAlloc) : Spec BytesMergeProtoGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = x.wt.toU32.setWidth 8 ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      BytesMergeCapOk x.valCap x.bs.length⌝ ∗
      vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp bytesMerge3Stack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗ stackAt s0.sp bytesMerge3Stack ∗
      match (LibsignalSpqrV1.Proto.mergeBytes x.wt x.bs).toOption with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
            ⌜BytesMergeCapOk cap' rest.length⌝ ∗ vecU8At A x.valPtr cap' ptr' v) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Contract of `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]`
(`0x4d13c`) in a loaded image `img` against `LibsignalSpqrV1.Proto.mergeBytes`. -/
def bytesMerge3ProtoSpec (A : RustAlloc) (img : Obj.Image) : Spec BytesMergeProtoGhost :=
  (bytesMerge3ProtoRawSpec A).inImage img

/-- `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]` (`0x4d13c`)
meets `bytesMerge3ProtoSpec A img` on `tripleRatchetProgAtExt img.base ext`. -/
def BytesMerge3ProtoOkExt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name)
    (bytesMerge3ProtoSpec A img)

/-- `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]` (`0x4d13c`) meets `bytesMerge3ProtoSpec A img` on `tripleRatchetProgAtExt img.base ext`. -/
theorem bytes_merge_3_proto_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hAlloc : AllocContracts img.base A ext)
    (hDecodeErrorFrom : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName) (decodeErrorFromSpec A))
    (hDecodeVarint2 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeVarint2Name)
      ((decodeVarint2Spec A).inImage img))
    (hBytesFromVec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img))
    (hReserve7 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve7Name) (doReserveSpec A))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        (bytesDropFnAddr img.base tmpPtr v.length)
        ((bytesVtableDropSpec A tmpPtr v v.length).inImage img)) :
    BytesMerge3ProtoOkExt img A ext := by
  have hok := bytes_merge_3_ok_ext himg hAlloc hDecodeErrorFrom hDecodeVarint2
    hBytesFromVec hReserve7 hVtableSlot hVtableDrop
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (bytesMerge3Spec A img).pre x.toCodec s0 ∗ R := by
    simpa only [bytesMerge3ProtoSpec, bytesMerge3Spec, Spec.inImage,
      bytesMerge3ProtoRawSpec, bytesMerge3RawSpec, BytesMergeProtoGhost.toCodec,
      protoWireTypeToCodec_toNat] using hpre
  refine subroutine_ok.mono_outcome hok x.toCodec R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [bytesMerge3ProtoSpec, bytesMerge3Spec, Spec.inImage,
      bytesMerge3ProtoRawSpec, bytesMerge3RawSpec, BytesMergeProtoGhost.toCodec] at hpost ⊢
    rw [proto_mergeBytes_toOption]
    exact hpost
  · exact Or.inr hfail

/-! ## 5. Relocatable `[LibsignalPlacement]` Verification of `bytes::merge [local#3]` (Block `290`) -/

theorem SepWPp.to_subroutineOutcome3_placed [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {x : BytesMergeGhost} {s0 : State} {P R : SepProp}
    (_hsp_align : s0.spAligned = true)
    (hm : s0.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s0.mem)
    (h : SepWPp prog (s0.readReg64 .lr) s0 P (MergePost3 A x s0 R) (MergePanic3 A x s0 R)) :
    ∃ sf, Steps prog s0 sf ∧
      SubroutineOutcome (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)) x R s0 sf := by
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hfalse⟩⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpc, hsp, hrun⟩, ⟨hsp, hcs⟩, hpost hmf⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hpanic hmf⟩)⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

/-- Relocatable `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]`
(Block `290`) meets `withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)` under `[LibsignalPlacement]`. -/
theorem bytes_merge_3_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdef : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpec A)))
    (hmc : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      ((blkPl_290).ρ "memcpy")
      framelessMemcpySpec)
    (hshim : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      ((blkPl_290).ρ lsRustNoAllocShimSym)
      noAllocShimSpec)
    (halloc : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      ((blkPl_290).ρ lsRustAllocSym)
      (withLsCl lsmpl (rustAllocSpec A)))
    (hpanic : ((blkPC_290).rebase (blkPl_290).base H).externAt?
      ((blkPl_290).ρ lsHandleErrorSym) =
      some Rust.panicked)
    (hDecodeVarint2 : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (lsmpl.base 291)
      (withLsCl lsmpl (decodeVarint2Spec A)))
    (hBytesFromVec : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A)))
    (hReserve7 : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (lsmpl.base 320)
      (withLsCl lsmpl (doReserveSpec A)))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpec A tmpPtr v v.length))) :
    subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (blkPl_290).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp_align hL => ?_
  obtain ⟨⟨hcl, hro⟩, hpre⟩ := extract_withLsCodeRoLoaded hpre
  rw [bytesMerge3RawSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hw0, hx1, hx2, hbs_len, hcapOk⟩, hm⟩ := hpre
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  let R48 : SepProp := memRegion (s0.sp - 8544#64) 48 ∗ R
  have herr_exit := fun {s : State} (hmerge : mergeBytes x.wt x.bs = none) =>
    @epilogue3_err_0x07c_placed _ A H x s0 s R48 hmerge
  have hde_exit := fun (w : BitVec 64) (hw : KindNoHeap w) {s : State}
      (hmerge : mergeBytes x.wt x.bs = none) =>
    @epilogue3_decodeErrorFrom_0x074_placed _ A H hdef x s0 s R48 w hw hmerge
  have h094_exit := fun (len : BitVec 64) (rest0 : List (BitVec 8)) {s : State}
      (hwt : x.wt = .lengthDelimited)
      (hvar : decodeVarint x.bs = some (len, rest0))
      (hle : len.toNat ≤ rest0.length) =>
    @phase2_from_0x094_placed _ A H hmc hshim halloc hpanic hBytesFromVec hReserve7
      hVtableDrop x s0 s R48 len rest0 hwt hvar hle hbs_len hcapOk
  clear hBytesFromVec hReserve7 hVtableDrop
  refine Exists.elim (SepWPp.to_subroutineOutcome3_placed hsp_align hm hL ?_)
    fun _ ⟨hsteps, hout⟩ => reaches_outcome_steps hsteps (reaches_outcome.of_outcome hout)
  rw [stackAt_bytesMerge3_entry s0.sp]
  refine SepWPp.weaken_pre (P' := cells (s0.sp - 64#64) 8 ∗
    (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗
      stackAt (s0.sp - 224#64) decodeVarint2Stack ∗
      memRegion (s0.sp - 224#64) 8 ∗
      memRegion (s0.sp - 216#64) 48 ∗
      memRegion (s0.sp - 168#64) 104))
    (Entails.of_eq (by ac_rfl)) ?_
  refine SepWPp.unfold_cells_64 fun c0 c1 c2 c3 c4 c5 c6 c7 => ?_
  by_cases hwt : x.wt = .lengthDelimited
  · have hw0_br :
        (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      change (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x0)) &&& 255#64) != 2#32) = false
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, hw0, hwt]
      decide
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := lsmpl.base 291)
    wp_steps
    apply SepWP.fold (show
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢
        savedRegsStack s0.sp s0 from Entails.refl _) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl1 hro1
    refine SepWPp.bm_call_frame_lscl
      (x := ({ bufRef := x.bufRef, slot := x.slot, ptr := x.ptr, bs := x.bs } : DecodeVarintSlowGhost))
      (T := (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarint2Stack)
      hDecodeVarint2 hcl1 hro1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp_align]) rfl
      (by simp (config := { decide := true }) only [decodeVarint2Spec, arm64_norm])
      hbs_len
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sf _ hm => by
        simp only [bytesMerge3RawSpec, withLsCl, decodeVarint2Spec,
          State.trace_setPC, State.trace_writeReg64, allocFailedIn] at hm ⊢
        exact allowPanic_frame id hm) ?_
    intro sf_dv hpcf hrunf hspf hcsf hclf hrof
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f, hvregsf⟩ := hcsf
    simp (config := { decide := true }) only [arm64_norm, hx1, hx2] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f hvregsf
    simp (config := { decide := true }) only [decodeVarint2Spec, wp_norm, arm64_norm]
    rw [stackAt_varint2_to_slice s0.sp]
    rcases hvar : decodeVarint x.bs with _ | ⟨len, rest0⟩
    · dsimp only
      have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_of_decodeVarint_none hvar
      refine SepWPp.weaken_pre (P' :=
        ⌜sf_dv.readReg64 .x0 = 1#64⌝ ∗ ⌜sf_dv.trace = s0.trace⌝ ∗ ⌜sf_dv.readReg64 .x1 ≠ 0#64⌝ ∗
          (memRegion (s0.sp - 8544#64) 48 ∗
            decodeErrorAtStackLen A (sf_dv.readReg64 .x1) 0 ∗
            vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
            (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
            stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
            memRegion (s0.sp - 224#64) 8 ∗
            memRegion (s0.sp - 216#64) 48 ∗
            memRegion (s0.sp - 168#64) 104 ∗
            savedRegsStack s0.sp s0))
        (Entails.of_eq (by
          dsimp only [savedRegsStack, Reg.x0, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x29, Reg.x30]
          ac_rfl)) ?_
      refine SepWPp.pure_elim fun hx0_sf => ?_
      refine SepWPp.pure_elim fun htr => ?_
      refine SepWPp.pure_elim fun hx1_sf => ?_
      apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_290).base + 124#64)
      wp_steps
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      intro hcl2 hro2
      exact SepWPp.lift_merge3 (herr_exit hmerge
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm]; exact hx1_sf)
        (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, and_self]))
    · dsimp only
      obtain ⟨pfx, hpfx⟩ := bm_decodeVarint_suffix hvar
      have hrest0_len : rest0.length ≤ x.bs.length := by rw [hpfx, List.length_append]; omega
      have hrest0_toNat : (BitVec.ofNat 64 rest0.length).toNat = rest0.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine SepWPp.weaken_pre (P' :=
        ⌜sf_dv.readReg64 .x0 = 0#64 ∧ sf_dv.readReg64 .x1 = len⌝ ∗ ⌜sf_dv.trace = s0.trace⌝ ∗
          (memRegion (s0.sp - 8544#64) 48 ∗
            vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
            (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
            stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
            memRegion (s0.sp - 224#64) 8 ∗
            memRegion (s0.sp - 216#64) 48 ∗
            memRegion (s0.sp - 168#64) 104 ∗
            savedRegsStack s0.sp s0))
        (Entails.of_eq (by
          dsimp only [savedRegsStack, Reg.x0, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x29, Reg.x30]
          ac_rfl)) ?_
      refine SepWPp.pure_elim fun ⟨hx0_sf, hx1_sf⟩ => ?_
      refine SepWPp.pure_elim fun htr => ?_
      dsimp only [sliceCursorAfter]
      apply SepWPp.bm_of_sepWP_lscl hclf hrof
        (mid := if len.ule (BitVec.ofNat 64 rest0.length) = true then (blkPl_290).base + 148#64 else (blkPl_290).base + 80#64)
      wp_steps
      apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length))) ∗
          ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗ (x.ptr ↦ₛ x.bs) ⊢
          sliceCursorAfter x.slot x.ptr x.bs rest0 from Entails.refl _) (by sep_focus)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      intro hcl2 hro2
      by_cases hule : len.ule (BitVec.ofNat 64 rest0.length) = false
      · simp only [hule, Bool.false_eq_true, ↓reduceIte] at hcl2 hro2 ⊢
        have hlt : rest0.length < len.toNat := by simp [BitVec.ule, hrest0_toNat] at hule; omega
        have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_lengthDelimited_underflow hwt hvar hlt
        refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 216#64) 48 ∗
          (memRegion (s0.sp - 8544#64) 48 ∗
            vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
            (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
            stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
            memRegion (s0.sp - 224#64) 8 ∗
            memRegion (s0.sp - 168#64) 104 ∗
            savedRegsStack s0.sp s0))
          (Entails.of_eq (by ac_rfl)) ?_
        refine SepWPp.unfold_memRegion_216 fun w216 => ?_
        apply SepWPp.bm_of_sepWP_lscl hcl2 hro2 (mid := (blkPl_290).base + 116#64)
        wp_steps
        apply SepWP.fold (sliceCursorAfter_to_err x.slot x.ptr x.bs rest0) (by sep_focus)
        apply SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
        intro hcl3 hro3
        refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3 (hde_exit 0x8000000000000007#64 (by simp [KindNoHeap]) hmerge
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
          hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, and_self])
          hcl3 hro3))
        exact Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm]; ac_rfl)
      · have hule_eq : len.ule (BitVec.ofNat 64 rest0.length) = true :=
          Bool.eq_true_of_not_eq_false hule
        simp only [hule_eq, ↓reduceIte] at hcl2 hro2 ⊢
        have hle : len.toNat ≤ rest0.length := by simpa [BitVec.ule, hrest0_toNat] using hule_eq
        refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3 (h094_exit len rest0 hwt hvar hle
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule_eq])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
          hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, and_self])
          hcl2 hro2
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1_sf])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29f])))
        exact Entails.of_eq (by ac_rfl)
  · have hw0_br :
        (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      change (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x0)) &&& 255#64) != 2#32) = true
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, hw0]
      cases hxwt : x.wt <;> simp_all [WireType.toNat]
    have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_ne_lengthDelimited hwt
    dsimp only [sliceCursorAt]
    rw [stackAt_varint2_to_slice s0.sp]
    refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 216#64) 48 ∗
      (memRegion (s0.sp - 8544#64) 48 ∗
        ((s0.sp - 64#64) ↦₆₄ c0) ∗ ((s0.sp - 56#64) ↦₆₄ c1) ∗
        ((s0.sp - 48#64) ↦₆₄ c2) ∗ ((s0.sp - 40#64) ↦₆₄ c3) ∗
        ((s0.sp - 32#64) ↦₆₄ c4) ∗ ((s0.sp - 24#64) ↦₆₄ c5) ∗
        ((s0.sp - 16#64) ↦₆₄ c6) ∗ ((s0.sp - 8#64) ↦₆₄ c7) ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗
        ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
        (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104)) (Entails.of_eq (by ac_rfl)) ?_
    refine SepWPp.unfold_memRegion_216_invalidWireType fun w0_216 b0_216 b1_216 => ?_
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_290).base + 116#64)
    wp_steps
    apply SepWP.fold (fold_memRegion_40_bytes (s0.sp - 216#64)
      (BitVec.ofNat 8 x.wt.toNat) 2#8) (by sep_focus)
    apply SepWP.fold (fold_slot_16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (show
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢
        savedRegsStack s0.sp s0 from Entails.refl _) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br, hw0, mask_ff_32_of_setWidth8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl1 hro1
    refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3 (hde_exit 0x8000000000000006#64 (by simp [KindNoHeap]) hmerge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br, hw0, mask_ff_32_of_setWidth8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, and_self])
      hcl1 hro1))
    exact Entails.of_eq (by dsimp only [savedRegsStack]; simp (config := { decide := true }) only [arm64_norm]; ac_rfl)

theorem bytes_merge_3_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : H lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked)
    (hErr341 : subroutine_ok ((blkPC_291).rebase (blkPl_291).base H)
      (lsmpl.base 261) (decodeErrorFromSpec A))
    (hSlow : subroutine_ok ((blkPC_291).rebase (blkPl_291).base H)
      (lsmpl.base 293) (Prost.decodeVarintSlowSpec A)) :
    subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (blkPl_290).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)) :=
  bytes_merge_3_placed_ok_of_contracts
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_290).rebase (blkPl_290).base H)
      (decode_error_from_placed_ok hshim halloc hpanic_alloc))
    (ls_hook_ok_of_mem hmc)
    (ls_hook_ok_of_mem hshim)
    (subroutine_ok_withLsCl_of_plain (ls_hook_ok_of_mem halloc))
    ((ls_externAt?_of_mem (H := H) (sym := lsHandleErrorSym)).trans hpanic_raw)
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_290).rebase (blkPl_290).base H) (j := 291)
      (decodeVarint2_placed_ok_of_contracts hErr341 hSlow))
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_290).rebase (blkPl_290).base H)
      (bytesFromVec_placed_ok H))
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_290).rebase (blkPl_290).base H)
      (do_reserve_7_placed_ok hpanic_raw hshim halloc hrealloc))
    (fun tmpPtr v =>
      subroutine_ok_withLsCl_of_withLsCodeLoaded
        (bytesVtableDrop_placed_ok hdealloc (by decide) tmpPtr v v.length))

theorem bytes_merge_3_proto_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdef : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpec A)))
    (hmc : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      ((blkPl_290).ρ "memcpy")
      framelessMemcpySpec)
    (hshim : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      ((blkPl_290).ρ lsRustNoAllocShimSym)
      noAllocShimSpec)
    (halloc : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      ((blkPl_290).ρ lsRustAllocSym)
      (withLsCl lsmpl (rustAllocSpec A)))
    (hpanic : ((blkPC_290).rebase (blkPl_290).base H).externAt?
      ((blkPl_290).ρ lsHandleErrorSym) =
      some Rust.panicked)
    (hDecodeVarint2 : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (lsmpl.base 291)
      (withLsCl lsmpl (decodeVarint2Spec A)))
    (hBytesFromVec : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A)))
    (hReserve7 : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (lsmpl.base 320)
      (withLsCl lsmpl (doReserveSpec A)))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpec A tmpPtr v v.length))) :
    subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (blkPl_290).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3ProtoRawSpec A)) := by
  have hok := bytes_merge_3_placed_ok_of_contracts hdef hmc hshim halloc hpanic hDecodeVarint2
    hBytesFromVec hReserve7 hVtableDrop
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)).pre x.toCodec s0 ∗ R := by
    simpa only [withLsCodeRoLoaded, bytesMerge3ProtoRawSpec, bytesMerge3RawSpec,
      BytesMergeProtoGhost.toCodec, protoWireTypeToCodec_toNat] using hpre
  refine subroutine_ok.mono_outcome hok x.toCodec R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, bytesMerge3ProtoRawSpec, bytesMerge3RawSpec,
      BytesMergeProtoGhost.toCodec] at hpost ⊢
    rw [proto_mergeBytes_toOption]
    exact hpost
  · exact Or.inr hfail

theorem bytes_merge_3_proto_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : H lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked)
    (hErr341 : subroutine_ok ((blkPC_291).rebase (blkPl_291).base H)
      (lsmpl.base 261) (decodeErrorFromSpec A))
    (hSlow : subroutine_ok ((blkPC_291).rebase (blkPl_291).base H)
      (lsmpl.base 293) (Prost.decodeVarintSlowSpec A)) :
    subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (blkPl_290).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3ProtoRawSpec A)) := by
  have hok := bytes_merge_3_placed_ok hshim halloc hrealloc hdealloc hmc hpanic_alloc hpanic_raw hErr341 hSlow
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)).pre x.toCodec s0 ∗ R := by
    simpa only [withLsCodeRoLoaded, bytesMerge3ProtoRawSpec, bytesMerge3RawSpec,
      BytesMergeProtoGhost.toCodec, protoWireTypeToCodec_toNat] using hpre
  refine subroutine_ok.mono_outcome hok x.toCodec R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, bytesMerge3ProtoRawSpec, bytesMerge3RawSpec,
      BytesMergeProtoGhost.toCodec] at hpost ⊢
    rw [proto_mergeBytes_toOption]
    exact hpost
  · exact Or.inr hfail

end CryptoVerification.SpqrV1.Prost.BytesMerge





