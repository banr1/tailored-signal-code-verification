/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.BytesMerge7Phase23
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeErrorFromX
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.VarintDrop7
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp

/-!
# X-Form Crate-10 `bytes::merge [local#7]` Verification

Proves error epilogues (`+0x074`, `+0x07c`), Phase 1 (`+0x000..+0x074`), and top-level X-form
contracts `bytesMerge7_ok_of_alloc_x` (`bytesMerge3Spec A img`) and
`bytesMerge7_proto_ok_of_alloc_x` (`bytesMerge3ProtoSpec A img`) on
`tripleRatchetProgAtExt img.base ext` under `AllocContractsX img A ext`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.BytesMerge7

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open scoped CryptoVerification.CodeLayout
open CryptoVerification (libsignalSessionCode libsignalSessionImage)
open CryptoVerification.RustHeap (RustAlloc vecU8At allocFailedIn)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (AllocContractsX tripleRatchetProgAtExt extHookStack rustAllocSpecWithStack
   sessionShimSpec sessionMemcpyRegionSpec withStack
   panic_at_handle_error_ext doReserveSpecX decodeErrorFromSpecWithStack_inImage_le
   bytesFromVecName bytesFromVecSpec bytesFromVecOk_ext
   bytesDropFnAddr bytesVtableDropSpecX BytesVtableSlotLoadedStmt
   bytesVtableSlotLoaded bytesVtableDrop_base_ok_ext_x
   decodeErrorFromName decodeErrorFromSpecWithStack decodeErrorAtStackLen KindNoHeap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeGhost BytesMergeCapOk bytesMergeRawSpecX MergePostX MergePanicX
   savedRegsStack bm_HighCalleeSaved spAligned_sub_224
   decodeVarintSliceStackX decodeErrorHookStackX
   sliceCursorAt sliceCursorAfter
   DecodeVarintSlowGhost
   fold_stackAt_bytesMergeX stackAt_sliceX_to_decodeErrorX
   session2ShimSpecBMX session2MemcpySpecBMX
   bm_decodeVarint_suffix mergeBytes_of_decodeVarint_none
   mergeBytes_lengthDelimited_underflow mergeBytes_ne_lengthDelimited
   sliceCursorAfter_to_err fold_memRegion_40_bytes fold_slot_16
   mask_ff_32_of_setWidth8)
open CryptoVerification.SpqrV1.Varint (decodeVarint2StackX decodeVarint2SpecX)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
  (bytesMerge3RawSpec bytesMerge3Spec bytesMerge3ProtoRawSpec bytesMerge3ProtoSpec
   BytesMergeProtoGhost protoWireTypeToCodec_toNat proto_mergeBytes_toOption
   stackAt_bytesMerge3_entry stackAt_varint2_to_slice)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH
  (c3_stage1Alloc_of_allocContractsX)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.DoReserve11
  (doReserve11Name do_reserve_11_ok_ext_xa)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.VarintDrop7
  (decodeVarint6_ok_of_alloc_x)
open scoped LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.BytesMerge7Phase23
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.BytesMerge7Phase23
  (bytesMerge7Name decodeVarint6Name bytesMerge7Off decodeVarint6Off doReserve11Off
   bytesMerge7_fnOff decodeVarint6_fnOff doReserve11_fnOff
   bm7DecodeErrorFromRelOff bm7MemcpyRelOff bm7MemcpyRelNat
   bm7ShimRelOff bm7ShimRelNat bm7AllocRelOff bm7AllocRelNat
   bm7HandleErrorRelOff bm7HandleErrorRelNat bm7BytesFromVecRelOff
   bm7DoReserve11RelOff bm7DecodeVarint6RelOff
   bm7_add_decodeErrorFrom_eq_fnAddr bm7_add_decodeVarint6_eq_fnAddr
   bm7Off050 bm7Off074 bm7Off07c bm7Off094 phase2_7_from_0x094)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bytesMerge7_fnOff decodeVarint6_fnOff doReserve11_fnOff
  bytesMerge7Off decodeVarint6Off doReserve11Off
  bm7DoReserve11RelOff bm7DecodeVarint6RelOff
  bm7DecodeErrorFromRelOff bm7MemcpyRelOff bm7MemcpyRelNat bm7ShimRelOff bm7ShimRelNat
  bm7AllocRelOff bm7AllocRelNat bm7HandleErrorRelOff bm7HandleErrorRelNat bm7BytesFromVecRelOff
  bm7Off050 bm7Off074 bm7Off07c bm7Off094

/-! ## 1. Error Epilogue Lemmas (`+0x074`, `+0x07c`) -/

theorem epilogue7_err_0x07c {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    (hmerge : mergeBytes x.wt x.bs = none)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMerge7Name + bm7Off07c)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 ≠ 0#64)
    (hhigh : bm_HighCalleeSaved s0 s) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (decodeErrorAtStackLen A (s.readReg64 .x0) 0 ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostX A x s0 R) (MergePanicX A x s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  obtain ⟨h25, h26, h27, h28, hvregs⟩ := hhigh
  merge7_fetches_H img.base H bytesMerge7_fnOff 124 24
  dsimp only [savedRegsStack] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMerge7Name = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.fold (fold_stackAt_bytesMergeX s0.sp
    (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x24) (s0.readReg64 .x23)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  refine ⟨?_, by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp],
    by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, h25, h26, h27, h28, hvregs, and_self]⟩
  intro hmf
  dsimp only [Reg.x0] at hx0 hmf ⊢
  simp (config := { decide := true }) only [bytesMergeRawSpecX, hmerge, State.readReg64_setPC,
    State.readReg64_writeReg64, State.trace_setPC, State.trace_writeReg64, Reg.x0, hx0, htrace,
    ↓reduceIte, ne_eq, not_false_eq_true, pure_true, emp_sepConj]
  convert hmf using 2
  sep_frame

theorem epilogue7_decodeErrorFrom_0x074 {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdef : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge7Name + bm7DecodeErrorFromRelOff)
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp} {w : BitVec 64}
    (hw : KindNoHeap w)
    (hmerge : mergeBytes x.wt x.bs = none)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMerge7Name + bm7Off074)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hfl : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (((s0.sp - 216#64) ↦₆₄ w) ∗ memRegion (s0.sp - 216#64 + 8#64) 40 ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostX A x s0 R) (MergePanicX A x s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  merge7_fetches_H img.base H bytesMerge7_fnOff 116 32
  dsimp only [savedRegsStack] at hpc hdef ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMerge7Name = entry
  examples_hide_fetches
  apply CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.bm_of_sepWP_inv hfl hsym (mid := entry + bm7DecodeErrorFromRelOff)
  wp_steps
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hfl_call hsym_call
  refine CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.bm_call_frame_inv (x := (s0.sp - 216#64, w))
    (T := ((s0.sp - 216#64) ↦₆₄ w) ∗ memRegion (s0.sp - 216#64 + 8#64) 40 ∗
      A.pool ∗ stackAt (s0.sp - 224#64) decodeErrorHookStackX)
    hdef hfl_call hsym_call
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [decodeErrorFromSpecWithStack, arm64_norm, hsp]; rfl)
    (by simp (config := { decide := true }) only [KindNoHeap, wp_norm, arm64_norm, hsp, hw, and_self])
    (by rw [stackAt_sliceX_to_decodeErrorX]; sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf _ hm => by
      simp only [bytesMergeRawSpecX, decodeErrorFromSpecWithStack,
        State.trace_setPC, State.trace_writeReg64, allocFailedIn, htrace] at hm ⊢
      exact allowPanic_frame id hm) ?_
  intro sf_de hpcf hrunf hspf hcsf _ _
  have hhigh' : bm_HighCalleeSaved s0 sf_de := hhigh.of_calleeSaved hcsf
  obtain ⟨h25, h26, h27, h28, hvregs⟩ := hhigh'
  simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf
  simp (config := { decide := true }) only [decodeErrorFromSpecWithStack, arm64_norm, hsp, htrace]
  refine SepWPp.pure_elim fun ⟨hx0, htr⟩ => ?_
  apply SepWPp.fold (T' := stackAt (s0.sp - 224#64) decodeVarintSliceStackX)
    (by rw [stackAt_sliceX_to_decodeErrorX]; exact Entails.refl _) (by sep_focus)
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.fold (fold_stackAt_bytesMergeX s0.sp
    (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x24) (s0.readReg64 .x23)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
  refine ⟨?_, by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf],
    by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, h25, h26, h27, h28, hvregs, and_self]⟩
  intro hmf
  simp (config := { decide := true }) only [bytesMergeRawSpecX, hmerge, State.readReg64_setPC,
    State.readReg64_writeReg64, State.trace_setPC, State.trace_writeReg64, Reg.x0, hx0, htr,
    ↓reduceIte, ne_eq, not_false_eq_true, pure_true, emp_sepConj]
  convert hmf using 2
  sep_frame

/-! ## 2. Phase 1 (`+0x000..+0x074`) and `bytesMerge7_ok_of_alloc_x` -/

set_option maxHeartbeats 500000 in
/-- Generalized verification of `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]`
on any `libsignalSessionCode.rebase img.base H`. -/
theorem bytesMerge7_ok_of_contracts {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hdef : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge7Name + bm7DecodeErrorFromRelOff)
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    (hmc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge7Name + bm7MemcpyRelOff)
      (session2MemcpySpecBMX.inImage img))
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge7Name + bm7ShimRelOff)
      (session2ShimSpecBMX.inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge7Name + bm7AllocRelOff)
      ((rustAllocSpecWithStack A extHookStack).inImage img))
    (hpanic : (libsignalSessionCode.rebase img.base H).externAt?
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge7Name + bm7HandleErrorRelOff) =
      some Rust.panicked)
    (hDecodeVarint6 : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr decodeVarint6Name)
      ((decodeVarint2SpecX A).inImage img))
    (hBytesFromVec : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img))
    (hReserve11 : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr doReserve11Name)
      ((doReserveSpecX A).inImage img))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (libsignalSessionCode.rebase img.base H)
        (bytesDropFnAddr img.base tmpPtr v.length)
        ((bytesVtableDropSpecX A tmpPtr v v.length).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge7Name)
      (bytesMerge3Spec A img) := by
  refine ProofLib.subroutine_ok_of_sepWPp fun x R s0 hpc hrun hpre hsp_align => ?_
  rw [bytesMerge3Spec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hfl, hsym⟩, hpre⟩ := hpre
  rw [bytesMerge3RawSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hw0, hx1, hx2, hbs_len, hcapOk⟩, hm⟩ := hpre
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hcall_dv6 : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge7Name + bm7DecodeVarint6RelOff)
      ((decodeVarint2SpecX A).inImage img) := by
    rw [bm7_add_decodeVarint6_eq_fnAddr]
    exact hDecodeVarint6
  have herr_exit := fun {s : State} (hmerge : mergeBytes x.wt x.bs = none) =>
    @epilogue7_err_0x07c img A H x s0 s (memRegion (s0.sp - 33120#64) 48 ∗ R) hmerge
  have hde_exit := fun (w : BitVec 64) (hw : KindNoHeap w) {s : State}
      (hmerge : mergeBytes x.wt x.bs = none) =>
    @epilogue7_decodeErrorFrom_0x074 img A H hdef x s0 s (memRegion (s0.sp - 33120#64) 48 ∗ R) w hw hmerge
  have h094_exit := fun (len : BitVec 64) (rest0 : List (BitVec 8)) {s : State}
      (hwt : x.wt = .lengthDelimited)
      (hvar : decodeVarint x.bs = some (len, rest0))
      (hle : len.toNat ≤ rest0.length) =>
    @phase2_7_from_0x094 img A H himg hmc hshim halloc hpanic hBytesFromVec hReserve11
      hVtableSlot hVtableDrop x s0 s (memRegion (s0.sp - 33120#64) 48 ∗ R) len rest0 hwt hvar hle hbs_len hcapOk
  clear hDecodeVarint6 hBytesFromVec hReserve11 hVtableDrop
  refine ⟨_, R, hm, ?_⟩
  change SepWPp _ (s0.readReg64 .lr) s0 _
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergePost3 A x s0 R)
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergePanic3 A x s0 R)
  rw [stackAt_bytesMerge3_entry s0.sp]
  refine SepWPp.weaken_pre (P' := cells (s0.sp - 64#64) 8 ∗
    (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗
      stackAt (s0.sp - 224#64) decodeVarint2StackX ∗
      memRegion (s0.sp - 224#64) 8 ∗
      memRegion (s0.sp - 216#64) 48 ∗
      memRegion (s0.sp - 168#64) 104))
    (by sep_frame) ?_
  refine CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.unfold_cells_64 fun c0 c1 c2 c3 c4 c5 c6 c7 => ?_
  merge7_fetches_H img.base H bytesMerge7_fnOff 0 116
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMerge7Name = entry
  examples_hide_fetches
  by_cases hwt : x.wt = .lengthDelimited
  · have hw0_br :
        (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      change (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x0)) &&& 255#64) != 2#32) = false
      rw [CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, hw0, hwt]
      decide
    apply CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.bm_of_sepWP_inv hfl hsym (mid := entry + bm7DecodeVarint6RelOff)
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
    refine CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.bm_call_frame_inv
      (x := ({ bufRef := x.bufRef, slot := x.slot, ptr := x.ptr, bs := x.bs } : DecodeVarintSlowGhost))
      (T := (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarint2StackX)
      hcall_dv6 hfl1 hsym1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp_align]) rfl
      (by simp (config := { decide := true }) only [decodeVarint2SpecX, arm64_norm])
      hbs_len
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sf _ hm => by
        simp only [bytesMerge3RawSpec, Spec.inImage, decodeVarint2SpecX,
          State.trace_setPC, State.trace_writeReg64, allocFailedIn] at hm ⊢
        exact allowPanic_frame id hm) ?_
    intro sf_dv hpcf hrunf hspf hcsf hflf hsymf
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f, hvregsf⟩ := hcsf
    simp (config := { decide := true }) only [arm64_norm, hx1, hx2] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f hvregsf
    simp (config := { decide := true }) only [decodeVarint2SpecX, wp_norm, arm64_norm]
    rw [stackAt_varint2_to_slice s0.sp]
    rcases hvar : decodeVarint x.bs with _ | ⟨len, rest0⟩
    · dsimp only
      have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_of_decodeVarint_none hvar
      refine SepWPp.weaken_pre (P' :=
        ⌜sf_dv.readReg64 .x0 = 1#64⌝ ∗ ⌜sf_dv.trace = s0.trace⌝ ∗ ⌜sf_dv.readReg64 .x1 ≠ 0#64⌝ ∗
          (memRegion (s0.sp - 33120#64) 48 ∗
            decodeErrorAtStackLen A (sf_dv.readReg64 .x1) 0 ∗
            vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
            (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
            stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
            memRegion (s0.sp - 224#64) 8 ∗
            memRegion (s0.sp - 216#64) 48 ∗
            memRegion (s0.sp - 168#64) 104 ∗
            savedRegsStack s0.sp s0))
        (Entails.of_eq (by
          dsimp only [savedRegsStack, Reg.x0, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x29, Reg.x30]
          sep_ac_rfl)) ?_
      refine SepWPp.pure_elim fun hx0_sf => ?_
      refine SepWPp.pure_elim fun htr => ?_
      refine SepWPp.pure_elim fun hx1_sf => ?_
      apply CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.bm_of_sepWP_inv hflf hsymf (mid := entry + bm7Off07c)
      wp_steps
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      intro hfl2 hsym2
      exact CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SepWPp.lift_merge3 (herr_exit hmerge
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
          (memRegion (s0.sp - 33120#64) 48 ∗
            vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
            (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
            stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
            memRegion (s0.sp - 224#64) 8 ∗
            memRegion (s0.sp - 216#64) 48 ∗
            memRegion (s0.sp - 168#64) 104 ∗
            savedRegsStack s0.sp s0))
        (Entails.of_eq (by
          dsimp only [savedRegsStack, Reg.x0, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x29, Reg.x30]
          sep_ac_rfl)) ?_
      refine SepWPp.pure_elim fun ⟨hx0_sf, hx1_sf⟩ => ?_
      refine SepWPp.pure_elim fun htr => ?_
      dsimp only [sliceCursorAfter]
      apply CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.bm_of_sepWP_inv hflf hsymf
        (mid := if len.ule (BitVec.ofNat 64 rest0.length) = true then entry + bm7Off094 else entry + bm7Off050)
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
          (memRegion (s0.sp - 33120#64) 48 ∗
            vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
            (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
            stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
            memRegion (s0.sp - 224#64) 8 ∗
            memRegion (s0.sp - 168#64) 104 ∗
            savedRegsStack s0.sp s0))
          (by sep_frame) ?_
        refine CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.unfold_memRegion_216 fun w216 => ?_
        apply CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.bm_of_sepWP_inv hfl2 hsym2 (mid := entry + bm7Off074)
        wp_steps
        apply SepWP.fold (sliceCursorAfter_to_err x.slot x.ptr x.bs rest0) (by sep_focus)
        apply SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
        intro hfl3 hsym3
        refine SepWPp.weaken_pre ?_ (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SepWPp.lift_merge3 (hde_exit 0x8000000000000007#64 (by simp [KindNoHeap]) hmerge
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
          hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, and_self])
          hfl3 hsym3))
        simp (config := { decide := true }) only [arm64_norm]
        sep_frame
      · have hule_eq : len.ule (BitVec.ofNat 64 rest0.length) = true :=
          Bool.eq_true_of_not_eq_false hule
        simp only [hule_eq, ↓reduceIte] at hfl2 hsym2 ⊢
        have hle : len.toNat ≤ rest0.length := by simpa [BitVec.ule, hrest0_toNat] using hule_eq
        refine SepWPp.weaken_pre ?_ (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SepWPp.lift_merge3 (h094_exit len rest0 hwt hvar hle
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
        sep_frame
  · have hw0_br :
        (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      change (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x0)) &&& 255#64) != 2#32) = true
      rw [CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, hw0]
      cases hxwt : x.wt <;> simp_all [WireType.toNat]
    have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_ne_lengthDelimited hwt
    dsimp only [sliceCursorAt]
    rw [stackAt_varint2_to_slice s0.sp]
    refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 216#64) 48 ∗
      (memRegion (s0.sp - 33120#64) 48 ∗
        ((s0.sp - 64#64) ↦₆₄ c0) ∗ ((s0.sp - 56#64) ↦₆₄ c1) ∗
        ((s0.sp - 48#64) ↦₆₄ c2) ∗ ((s0.sp - 40#64) ↦₆₄ c3) ∗
        ((s0.sp - 32#64) ↦₆₄ c4) ∗ ((s0.sp - 24#64) ↦₆₄ c5) ∗
        ((s0.sp - 16#64) ↦₆₄ c6) ∗ ((s0.sp - 8#64) ↦₆₄ c7) ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗
        ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
        (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104)) (by sep_frame) ?_
    refine CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.unfold_memRegion_216_invalidWireType fun w0_216 b0_216 b1_216 => ?_
    apply CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.bm_of_sepWP_inv hfl hsym (mid := entry + bm7Off074)
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
    refine SepWPp.weaken_pre ?_ (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SepWPp.lift_merge3 (hde_exit 0x8000000000000006#64 (by simp [KindNoHeap]) hmerge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br, hw0, mask_ff_32_of_setWidth8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, and_self])
      hfl1 hsym1))
    dsimp only [savedRegsStack]
    simp (config := { decide := true }) only [arm64_norm]
    sep_frame

private theorem bm7_shim_ok_at_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge7Name + bm7ShimRelOff)
      (session2ShimSpecBMX.inImage img) := by
  have h := hA.shim_ok_at bytesMerge7Name bm7ShimRelNat decodeVarintSliceStackX (by decide) (by decide)
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ ((withStack sessionShimSpec decodeVarintSliceStackX).inImage img).pre x s0 ∗ R := by
    dsimp only [Spec.inImage, withStack, sessionShimSpec, session2ShimSpecBMX] at hpre ⊢
    simpa only [pure_true, emp_sepConj, sepConj_assoc] using hpre
  refine h.mono_outcome x R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hfail
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · exact Or.inr hfail

private theorem bm7_memcpy_ok_at_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge7Name + bm7MemcpyRelOff)
      (session2MemcpySpecBMX.inImage img) := by
  have h := hA.session_memcpy_region_ok_at bytesMerge7Name bm7MemcpyRelNat decodeVarintSliceStackX (by decide) (by decide)
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ ((withStack sessionMemcpyRegionSpec decodeVarintSliceStackX).inImage img).pre x s0 ∗ R := by
    dsimp only [Spec.inImage, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, session2MemcpySpecBMX] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  refine h.mono_outcome x R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, session2MemcpySpecBMX] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr hfail

private theorem bm7_decodeErrorFrom_of_alloc {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hAlloc : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName)
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img) :=
  decodeErrorFromSpecWithStack_inImage_le
    (s1 := CryptoVerification.LibsignalTripleRatchet.Prost.X.decodeErrorHookStackW)
    (s2 := decodeErrorHookStackX)
    (CryptoVerification.LibsignalTripleRatchet.Prost.X.decodeErrorFrom_okW
      (c3_stage1Alloc_of_allocContractsX hAlloc))

/-- Top-level X-form `bytes::merge [local#7]` (`bytesMerge3Spec A img`) closed from
`Obj.Loads libsignalSessionImage img` and `AllocContractsX img A ext`. -/
theorem bytesMerge7_ok_of_alloc_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hAlloc : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge7Name)
      (bytesMerge3Spec A img) := by
  have hdef : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge7Name + bm7DecodeErrorFromRelOff)
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img) := by
    rw [bm7_add_decodeErrorFrom_eq_fnAddr]
    exact bm7_decodeErrorFrom_of_alloc hAlloc
  exact bytesMerge7_ok_of_contracts himg hdef
    (bm7_memcpy_ok_at_ext_x hAlloc)
    (bm7_shim_ok_at_ext_x hAlloc)
    (hAlloc.alloc_ok_at bytesMerge7Name bm7AllocRelNat)
    (panic_at_handle_error_ext img.base ext bytesMerge7Name bm7HandleErrorRelNat)
    (decodeVarint6_ok_of_alloc_x hAlloc)
    (bytesFromVecOk_ext himg rfl)
    (do_reserve_11_ok_ext_xa hAlloc)
    bytesVtableSlotLoaded
    (fun tmpPtr v => bytesVtableDrop_base_ok_ext_x hAlloc tmpPtr v v.length)

/-- Top-level X-form `bytes::merge [local#7]` (`bytesMerge3ProtoSpec A img` / `Proto.mergeBytes` form)
closed from `Obj.Loads libsignalSessionImage img` and `AllocContractsX img A ext`. -/
theorem bytesMerge7_proto_ok_of_alloc_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hAlloc : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge7Name)
      (bytesMerge3ProtoSpec A img) := by
  have hok := bytesMerge7_ok_of_alloc_x himg hAlloc
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (bytesMerge3Spec A img).pre x.toCodec s0 ∗ R := by
    simpa only [bytesMerge3ProtoSpec, bytesMerge3Spec, Spec.inImage,
      bytesMerge3ProtoRawSpec, bytesMerge3RawSpec,
      BytesMergeProtoGhost.toCodec, protoWireTypeToCodec_toNat] using hpre
  refine hok.mono_outcome x.toCodec R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [bytesMerge3ProtoSpec, bytesMerge3Spec, Spec.inImage,
      bytesMerge3ProtoRawSpec, bytesMerge3RawSpec,
      BytesMergeProtoGhost.toCodec] at hpost ⊢
    rw [proto_mergeBytes_toOption]
    exact hpost
  · exact Or.inr hfail

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.BytesMerge7
