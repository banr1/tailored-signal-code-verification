/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Phase23
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Phase 2, Phase 3, and Epilogue Lemmas for `CliC` `bytes::merge`

Proves `[LibsignalPlacement]` error/drop epilogues, Phase 3, and Phase 2 for `CliC`
`prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]> [local#6]` (Block `558`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Prost.BytesMerge

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.VarintBridge
open CryptoVerification.RecordCodecs.Placed

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local simp]
  bytesMutDataWord_zero bytesMutDataWord_bit0 bytesMutDataWord_getLsbD_zero
  bytesMutDataWord_getElem_zero bytesMutDataWord_lsr5 bitvec_ult_zero
  bitvec_ult_33bits_of_lt32 bitvec_msb_false_of_lt32 bitvec_getLsbD_63_of_lt32
  Prost.bitvec_ult_self bitvec_sub_self_64 bitvec_if_zero_ult_self

/-! ## Error and Drop Epilogue Lemmas (`+0x074`, `+0x07c`, `+0x254`) -/

theorem _root_.CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.epilogue3_err_0x07c_placed
    [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    (hmerge : mergeBytes x.wt x.bs = none)
    (hpc : s.pc = (blkPl_558).base + 124#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 ≠ 0#64)
    (hhigh : bm_HighCalleeSaved s0 s) :
    SepWPp (lsProg_558 H) (s0.readReg64 .lr) s
      (decodeErrorAtStackLen A (s.readReg64 .x0) 0 ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePost A x s0 R) (MergePanic A x s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  obtain ⟨h25, h26, h27, h28, hvregs⟩ := hhigh
  dsimp only [savedRegsStack] at hpc ⊢
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.fold (fold_stackAt_bytesMerge s0.sp
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
  simp (config := { decide := true }) only [bytesMergeRawSpec, hmerge, State.readReg64_setPC,
    State.readReg64_writeReg64, State.trace_setPC, State.trace_writeReg64, Reg.x0, hx0, htrace,
    ↓reduceIte, ne_eq, not_false_eq_true, pure_true, emp_sepConj]
  convert hmf using 2
  ac_rfl

theorem _root_.CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.epilogue3_decodeErrorFrom_0x074_placed
    [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hdef : subroutine_ok (lsProg_558 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpec A)))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp} {w : BitVec 64}
    (hw : KindNoHeap w)
    (hmerge : mergeBytes x.wt x.bs = none)
    (hpc : s.pc = (blkPl_558).base + 116#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    SepWPp (lsProg_558 H) (s0.readReg64 .lr) s
      (((s0.sp - 216#64) ↦₆₄ w) ∗ memRegion (s0.sp - 216#64 + 8#64) 40 ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePost A x s0 R) (MergePanic A x s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  dsimp only [savedRegsStack] at hpc hdef ⊢
  apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := lsmpl.base 261)
  wp_steps
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl1 hro1
  refine SepWPp.bm_call_frame_lscl (spec := decodeErrorFromSpec A) (x := (s0.sp - 216#64, w))
    (T := ((s0.sp - 216#64) ↦₆₄ w) ∗ memRegion (s0.sp - 216#64 + 8#64) 40 ∗
      A.pool ∗ stackAt (s0.sp - 224#64) decodeErrorHookStack)
    hdef hcl1 hro1
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [decodeErrorFromSpec, arm64_norm, hsp]; rfl)
    (by simp (config := { decide := true }) only [KindNoHeap, wp_norm, arm64_norm, hsp, hw, and_self])
    (by rw [stackAt_slice_to_decodeError]; sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf _ hm => by
      simp only [bytesMergeRawSpec, decodeErrorFromSpec,
        State.trace_setPC, State.trace_writeReg64, allocFailedIn, htrace] at hm ⊢
      exact allowPanic_frame id hm) ?_
  intro sf_de hpcf hrunf hspf hcsf _hclf _hrof
  have hhigh' : bm_HighCalleeSaved s0 sf_de := hhigh.of_calleeSaved hcsf
  obtain ⟨h25, h26, h27, h28, hvregs⟩ := hhigh'
  simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf
  simp (config := { decide := true }) only [decodeErrorFromSpec, arm64_norm, hsp, htrace]
  refine SepWPp.pure_elim fun ⟨hx0, htr⟩ => ?_
  apply SepWPp.fold (T' := stackAt (s0.sp - 224#64) decodeVarintSliceStack)
    (by rw [stackAt_slice_to_decodeError]; exact Entails.refl _) (by sep_focus)
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.fold (fold_stackAt_bytesMerge s0.sp
    (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x24) (s0.readReg64 .x23)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
  refine ⟨?_, by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf],
    by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, h25, h26, h27, h28, hvregs, and_self]⟩
  intro hmf
  simp (config := { decide := true }) only [bytesMergeRawSpec, hmerge, State.readReg64_setPC,
    State.readReg64_writeReg64, State.trace_setPC, State.trace_writeReg64, Reg.x0, hx0, htr,
    ↓reduceIte, ne_eq, not_false_eq_true, pure_true, emp_sepConj]
  convert hmf using 2
  ac_rfl

theorem _root_.CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.epilogue3_vtableDrop_0x254_placed
    [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr cap' ptr' : BitVec 64}
    (hVtableDrop : subroutine_ok (lsProg_558 H)
      (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpec A tmpPtr v v.length)))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hcapOk : BytesMergeCapOk cap' rest.length)
    (hpc : s.pc = (blkPl_558).base + 596#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx21 : s.readReg64 .x21 = bytesPtr tmpPtr v.length + BitVec.ofNat 64 v.length)
    (hx22 : s.readReg64 .x22 = bytesData tmpPtr v.length)
    (hx24 : s.readReg64 .x24 = bytesPlacedVtable tmpPtr v.length) :
    SepWPp (lsProg_558 H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr cap' ptr' v ∗
        bytesBoxU8Buf A tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePost A x s0 R) (MergePanic A x s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  dsimp only [savedRegsStack] at hpc hVtableDrop ⊢
  apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := bytesPlacedDropFnAddr tmpPtr v.length)
  apply SepWP.with_vtableSlot_placed tmpPtr v.length hro
  wp_steps
  apply SepWP.drop_left
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl_call hro_call
  refine SepWPp.bm_call_frame_lscl (spec := bytesVtableDropSpec A tmpPtr v v.length) (x := ())
    (T := bytesBoxU8Buf A tmpPtr v ∗ A.pool ∗ stackAt (s0.sp - 224#64) bytesVtableDropStack)
    hVtableDrop hcl_call hro_call
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [bytesVtableDropSpec, arm64_norm, hsp]; rfl)
    (by simp only [Nat.le_refl, Nat.sub_self, BitVec.ofNat_eq_ofNat, and_self])
    (by rw [stackAt_slice_to_vtableDrop]; sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (by intro _ _ hm; dsimp only [bytesVtableDropSpec] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
  intro sf_dr hpcf hrunf hspf hcsf _hclf _hrof
  have hhigh' : bm_HighCalleeSaved s0 sf_dr := hhigh.of_calleeSaved hcsf
  obtain ⟨h25, h26, h27, h28, hvregs⟩ := hhigh'
  simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf
  simp (config := { decide := true }) only [bytesVtableDropSpec, arm64_norm, hsp, htrace]
  refine SepWPp.pure_elim fun htr => ?_
  apply SepWPp.fold (T' := stackAt (s0.sp - 224#64) decodeVarintSliceStack)
    (by rw [stackAt_slice_to_vtableDrop]; exact Entails.refl _) (by sep_focus)
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.fold (fold_stackAt_bytesMerge s0.sp
    (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x24) (s0.readReg64 .x23)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by sep_focus)
  apply SepWP.fold (vecU8At_entails_exists A x.valPtr cap' ptr' v hcapOk)
    (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
  refine ⟨?_, by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf],
    by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, h25, h26, h27, h28, hvregs, and_self]⟩
  intro hmf
  simp (config := { decide := true }) only [bytesMergeRawSpec, hmerge, State.readReg64_setPC,
    State.readReg64_writeReg64, State.trace_setPC, State.trace_writeReg64, Reg.x0, htr, ↓reduceIte,
    pure_true, emp_sepConj]
  convert hmf using 2
  ac_rfl

/-! ## Phase 3 (`+0x210..+0x250`, `+0x29c..+0x2cc`) -/

theorem _root_.CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.phase3_from_0x230_placed
    [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hmc : subroutine_ok (lsProg_558 H) ((blkPl_558).ρ lsMemcpySym)
      (withLsCl lsmpl framelessMemcpySpec))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr cap' ptr' : BitVec 64}
    (hVtableDrop : subroutine_ok (lsProg_558 H)
      (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpec A tmpPtr v v.length)))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hcapOk : BytesMergeCapOk cap' rest.length)
    (hcap' : v.length ≤ cap'.toNat)
    (hv_len : v.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_558).base + 560#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 v.length)
    (hx21 : s.readReg64 .x21 = bytesPtr tmpPtr v.length)
    (hx22 : s.readReg64 .x22 = bytesData tmpPtr v.length)
    (hx23 : s.readReg64 .x23 = 0#64)
    (hx24 : s.readReg64 .x24 = bytesPlacedVtable tmpPtr v.length) :
    SepWPp (lsProg_558 H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr cap' ptr' [] ∗
        bytesBoxU8Buf A tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePost A x s0 R) (MergePanic A x s0 R) := by
  rcases v with _ | ⟨b0, v'⟩
  · have hep := fun {s : State} =>
      @CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.epilogue3_vtableDrop_0x254_placed _ A H
        x s0 s R [] rest tmpPtr cap' ptr' hVtableDrop hmerge hcapOk
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_558).base + 596#64)
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl1 hro1
    exact hep
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
      hhigh hcl1 hro1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx21])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx24])
  · set v := b0 :: v'
    have hep := fun {s : State} =>
      @CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.epilogue3_vtableDrop_0x254_placed _ A H
        x s0 s R v rest tmpPtr cap' ptr' hVtableDrop hmerge hcapOk
    have hpos : 0 < v.length := List.length_pos_of_ne_nil (List.cons_ne_nil b0 v')
    have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlen_ne : (BitVec.ofNat 64 v.length == 0#64) = false := by
      apply beq_false_of_ne
      intro h
      have h2 := congrArg BitVec.toNat h
      rw [hlen_toNat] at h2
      exact absurd h2 (by dsimp [v]; omega)
    have hbytesPtr : bytesPtr tmpPtr v.length = tmpPtr := by
      unfold bytesPtr
      have : v.length ≠ 0 := by omega
      simp [this]
    rw [vecU8At_nil_eq A x.valPtr cap' ptr' v hpos hcap', sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, hcap_lt, hptr'⟩ => ?_
    rw [bytesBoxU8Buf_nonempty A tmpPtr v hpos]
    refine SepWPp.weaken_pre (P' := ⌜tmpPtr ≠ 0#64 ∧ v.length < 2 ^ 63⌝ ∗
      ((x.valPtr ↦₆₄ cap') ∗ ((x.valPtr + 8#64) ↦₆₄ ptr') ∗ ((x.valPtr + 16#64) ↦₆₄ 0#64) ∗
        A.live ptr' cap'.toNat 1 ∗ memRegion ptr' v.length ∗
        memRegion (ptr' + BitVec.ofNat 64 v.length) (cap'.toNat - v.length) ∗
        A.live tmpPtr v.length 1 ∗ (tmpPtr ↦ₛ v) ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)) (Entails.of_eq (by ac_rfl)) ?_
    refine SepWPp.pure_elim fun ⟨htmp_ne, hv_lt63⟩ => ?_
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_558).ρ lsMemcpySym)
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hlen_ne])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl1 hro1
    refine SepWPp.bm_call_frame_lscl (spec := framelessMemcpySpec) (x := (ptr', tmpPtr, v))
      (T := memRegion ptr' v.length ∗ (tmpPtr ↦ₛ v))
      hmc hcl1 hro1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hlen_ne])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
      rfl
      (by simp (config := { decide := true }) only [arm64_norm, hlen_toNat, hv_lt63, and_self])
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (by intro _ _ hm; dsimp only [framelessMemcpySpec] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
    intro sf_mc hpcf hrunf hspf hcsf hclf hrof
    have hhigh' : bm_HighCalleeSaved s0 sf_mc := hhigh.of_calleeSaved hcsf
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, _, _, _, _, h29f, hvregsf⟩ := hcsf
    simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf h19f h20f h21f h22f h23f h24f h29f hvregsf
    simp (config := { decide := true }) only [framelessMemcpySpec, arm64_norm, htrace]
    refine SepWPp.pure_elim fun ⟨_, htr⟩ => ?_
    apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_558).base + 596#64)
    wp_steps
    apply SepWP.fold (fold_bytesBoxU8Buf_nonempty A tmpPtr v hpos htmp_ne hv_lt63)
      (by sep_focus)
    apply SepWP.fold (fold_vecU8At_copied A x.valPtr cap' ptr' v hpos hcap' hcap_lt hptr')
      (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hcl2 hro2
    exact hep
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by obtain ⟨h25, h26, h27, h28, hvregs⟩ := hhigh'; simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25, h26, h27, h28, hvregs, and_self])
      hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f, hx21, h20f, hx20, hbytesPtr])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h22f, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24f, hx24])

private theorem mergePanic_of_allocFailed_placed {A : RustAlloc} {x : BytesMergeGhost}
    {s0 s_call sf : State} {F R : SepProp} (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (bytesMergeRawSpec A).onPanic x s0 sf ∗ R := by
  dsimp only [bytesMergeRawSpec, allocFailedIn] at hm ⊢
  rw [htr] at hm
  exact allowPanic_frame id hm

private theorem decodeVarintAux_length_lt_placed (i : Nat) (acc : BitVec 64)
    (bs rest0 : List (BitVec 8)) (len : BitVec 64)
    (h : decodeVarintAux i acc bs = some (len, rest0)) :
    rest0.length < bs.length := by
  induction bs generalizing i acc with
  | nil => simp [decodeVarintAux] at h
  | cons b bs' ih =>
    unfold decodeVarintAux at h
    dsimp only at h
    split at h
    · split at h
      · contradiction
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        simp
    · split at h
      · contradiction
      · have hlt := ih _ _ h
        simp; omega

private theorem mergeBytes_length_sum_placed {wt : WireType} {bs v rest : List (BitVec 8)}
    (h : mergeBytes wt bs = some (v, rest)) :
    1 + v.length + rest.length ≤ bs.length := by
  cases wt <;> try simp [mergeBytes] at h
  cases hvar : decodeVarint bs with
  | none => simp [hvar] at h
  | some p =>
    rcases p with ⟨len, rest0⟩
    rw [hvar] at h
    dsimp only at h
    split at h
    · contradiction
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have h1 : rest0.length < bs.length := decodeVarintAux_length_lt_placed 0 0 bs rest0 len hvar
      have h2 : (rest0.take len.toNat).length + (rest0.drop len.toNat).length = rest0.length := by
        rw [← List.length_append, List.take_append_drop]
      omega

theorem _root_.CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.phase3_from_0x210_placed
    [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hmc : subroutine_ok (lsProg_558 H) ((blkPl_558).ρ lsMemcpySym)
      (withLsCl lsmpl framelessMemcpySpec))
    (hReserve : subroutine_ok (lsProg_558 H) (lsmpl.base 561)
      (withLsCl lsmpl (doReserveSpec A)))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr : BitVec 64}
    (hVtableDrop : subroutine_ok (lsProg_558 H)
      (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpec A tmpPtr v v.length)))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hv_len : v.length < 2 ^ 63)
    (hbs_len : x.bs.length < 2 ^ 63)
    (hcapOk : BytesMergeCapOk x.valCap x.bs.length)
    (hpc : s.pc = (blkPl_558).base + 528#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 v.length)
    (hx21 : s.readReg64 .x21 = bytesPtr tmpPtr v.length)
    (hx22 : s.readReg64 .x22 = bytesData tmpPtr v.length)
    (hx24 : s.readReg64 .x24 = bytesPlacedVtable tmpPtr v.length) :
    SepWPp (lsProg_558 H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        bytesBoxU8Buf A tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePost A x s0 R) (MergePanic A x s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hsum : 1 + v.length + rest.length ≤ x.bs.length := mergeBytes_length_sum_placed hmerge
  have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hp3 := fun (cap' ptr' : BitVec 64) {s : State}
      (hcapOk' : BytesMergeCapOk cap' rest.length) (hcap' : v.length ≤ cap'.toNat) =>
    @CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.phase3_from_0x230_placed _ A H hmc
      x s0 s R v rest tmpPtr cap' ptr' hVtableDrop hmerge hcapOk' hcap' hv_len
  rw [bm_vecU8At_eq_header_sep_buf A x.valPtr x.valCap x.valBuf x.valBs]
  dsimp only [vecHeader] at hpc hReserve hp3 ⊢
  apply SepWPp.bm_of_sepWP_lscl hcl hro
    (mid := if x.valCap.ult (BitVec.ofNat 64 v.length) = true then (blkPl_558).base + 668#64 else (blkPl_558).base + 544#64)
  wp_steps
  apply SepWP.fold (fold_vecU8At_clear A x.valPtr x.valCap x.valBuf x.valBs) (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl1 hro1
  by_cases hult : x.valCap.ult (BitVec.ofNat 64 v.length) = true
  · simp only [hult, ↓reduceIte] at hcl1 hro1 ⊢
    have hcap_lt : x.valCap.toNat < v.length := by
      simpa [BitVec.ult, hlen_toNat] using hult
    have hnewCap_bound : reserveCap x.valCap.toNat ([] : List (BitVec 8)).length v.length ≤ 9223372036854775807 :=
      bytesMergeCapOk_reserveCap_bound hcapOk hcap_lt hsum hbs_len
    have hcapOk' : BytesMergeCapOk (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) rest.length :=
      bytesMergeCapOk_after_reserve hcapOk hcap_lt hsum hbs_len
    have hnewCap_ge : v.length ≤ (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)).toNat := by
      dsimp [reserveCap] at hnewCap_bound ⊢
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hnewCap_ule :
        (BitVec.ofNat 64 v.length).ule (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) = true := by
      simp only [BitVec.ule, hlen_toNat, decide_eq_true_eq]
      exact hnewCap_ge
    apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := lsmpl.base 561)
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl2 hro2
    rw [stackAt_slice_to_doReserve s0.sp]
    refine SepWPp.bm_call_frame_lscl (spec := doReserveSpec A)
      (x := { v := x.valPtr, cap := x.valCap, ptr := x.valBuf, bs := [], additional := v.length })
      (T := vecU8At A x.valPtr x.valCap x.valBuf [] ∗ A.pool ∗ stackAt (s0.sp - 224#64) doReserveStack)
      hReserve hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
      (by simp (config := { decide := true }) only [doReserveSpec, arm64_norm, hsp, hx19, hx20]; rfl)
      (by exact ⟨hlen_toNat, hnewCap_bound⟩)
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (by intro _ _ hm; exact mergePanic_of_allocFailed_placed (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace]) hm) ?_
    intro sf_res hpcf hrunf hspf hcsf hclf hrof
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f, hvregsf⟩ := hcsf
    obtain ⟨h25_0, h26_0, h27_0, h28_0, hvregs_0⟩ := hhigh
    simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f hvregsf
    dsimp only [doReserveSpec, List.length_nil]
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun htr => ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun ptr' => ?_
    rw [bm_vecU8At_eq_header_sep_buf A x.valPtr (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' []]
    dsimp only [vecHeader, List.length_nil]
    apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_558).base + 560#64)
    wp_steps
    apply SepWP.fold
      (fold_vecU8At_clear A x.valPtr (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' [])
      (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hx20, hnewCap_ule])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hcl3 hro3
    refine SepWPp.weaken_pre (P' :=
      vecU8At A x.valPtr (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' [] ∗
        bytesBoxU8Buf A tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, hsp]; rw [stackAt_slice_to_doReserve s0.sp]; ac_rfl)) ?_
    exact hp3 (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' hcapOk' hnewCap_ge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hx20, hnewCap_ule])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr, htrace])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, h25_0, h26_0, h27_0, h28_0, hvregs_0, and_self])
      hcl3 hro3
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f, hx19])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h20f, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f, hx21])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h22f, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h23f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24f, hx24])
  · have hult_eq : x.valCap.ult (BitVec.ofNat 64 v.length) = false :=
      Bool.eq_false_iff.mpr hult
    simp only [hult_eq, Bool.false_eq_true, ↓reduceIte] at hcl1 hro1 ⊢
    have hcap_ge : v.length ≤ x.valCap.toNat := by
      simp [BitVec.ult, hlen_toNat] at hult_eq
      exact hult_eq
    have hcapOk' : BytesMergeCapOk x.valCap rest.length :=
      bytesMergeCapOk_mono hcapOk (by omega)
    apply SepWPp.bm_of_sepWP_lscl hcl1 hro1
      (mid := (blkPl_558).base + 560#64)
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult_eq])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl2 hro2
    exact hp3 x.valCap x.valBuf hcapOk' hcap_ge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult_eq])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
      (by obtain ⟨h25, h26, h27, h28, hvregs⟩ := hhigh; simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25, h26, h27, h28, hvregs, and_self])
      hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx21])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx24])

/-! ## Phase 2 (`+0x094..+0x20c`): `BytesMut::with_capacity`, `memcpy`, `Bytes::from_vec` -/

theorem _root_.CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.phase2_from_0x1b8_placed
    [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hmc : subroutine_ok (lsProg_558 H) ((blkPl_558).ρ lsMemcpySym)
      (withLsCl lsmpl framelessMemcpySpec))
    (hBytesFromVec : subroutine_ok (lsProg_558 H) (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A)))
    (hReserve : subroutine_ok (lsProg_558 H) (lsmpl.base 561)
      (withLsCl lsmpl (doReserveSpec A)))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 : BitVec 64}
    (hVtableDrop : subroutine_ok (lsProg_558 H)
      (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpec A tmpPtr v v.length)))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hv_len : v.length < 2 ^ 63)
    (hbs_len : x.bs.length < 2 ^ 63)
    (hcapOk : BytesMergeCapOk x.valCap x.bs.length)
    (hpc : s.pc = (blkPl_558).base + 440#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 v.length)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 v.length)
    (hx21 : s.readReg64 .x21 = tmpPtr)
    (hx22 : s.readReg64 .x22 = bytesMutDataWord (BitVec.ofNat 64 v.length))
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp (lsProg_558 H) (s0.readReg64 .lr) s
      (((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗
        ((s0.sp - 152#64) ↦₆₄ w2) ∗ ((s0.sp - 144#64) ↦₆₄ w3) ∗
        ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
        ((s0.sp - 120#64) ↦₆₄ w6) ∗
        memRegion (s0.sp - 112#64) 32 ∗
        ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
        bm_vecU8Buf A (BitVec.ofNat 64 v.length) tmpPtr v ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        savedRegsStack s0.sp s0)
      (MergePost A x s0 R) (MergePanic A x s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hp3 := fun {s : State} =>
    @CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.phase3_from_0x210_placed _ A H hmc hReserve
      x s0 s R v rest tmpPtr hVtableDrop hmerge hv_len hbs_len hcapOk
  clear hReserve
  apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := lsmpl.base 250)
  wp_steps
  apply SepWP.fold (fold_vecU8At_sp136 A s0.sp (BitVec.ofNat 64 v.length) tmpPtr v) (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx21, hx22, hx29, hsp,
      bytesMutDataWord_getElem_zero, bytesMutDataWord_lsr5, bitvec_ult_zero])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl1 hro1
  rw [stackAt_slice_to_bytesFromVec s0.sp]
  refine SepWPp.bm_call_frame_lscl (spec := bytesFromVecPlacedSpec A)
    (x := (s0.sp - 136#64, s0.sp - 112#64, BitVec.ofNat 64 v.length, tmpPtr, v))
    (T := vecU8At A (s0.sp - 136#64) (BitVec.ofNat 64 v.length) tmpPtr v ∗
      memRegion (s0.sp - 112#64) 32 ∗
      stackAt (s0.sp - 224#64) bytesFromVecStack)
    hBytesFromVec hcl1 hro1
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx21, hx22, hx29, hsp,
      bytesMutDataWord_getElem_zero, bytesMutDataWord_lsr5, bitvec_ult_zero])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [bytesFromVecPlacedSpec, arm64_norm, hsp, hx29])
    hlen_toNat
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (by intro _ _ hm; dsimp only [bytesFromVecPlacedSpec] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
  intro sf_bfv hpcf hrunf hspf hcsf hclf hrof
  obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f, hvregsf⟩ := hcsf
  obtain ⟨h25_0, h26_0, h27_0, h28_0, hvregs_0⟩ := hhigh
  simp (config := { decide := true }) only [arm64_norm, hsp, hx0, hx19, hx20, hx21, hx22, hx29,
    bytesMutDataWord_getElem_zero, bytesMutDataWord_lsr5, bitvec_ult_zero] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f hvregsf
  dsimp only [bytesFromVecPlacedSpec]
  rw [sepConj_assoc, sepConj_assoc]
  refine SepWPp.pure_elim fun htr => ?_
  rw [unfold_vecHeader_sp136, unfold_bytesPlacedAt_sp112]
  apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_558).base + 528#64)
  wp_steps
  apply SepWP.fold (memRegion_104_fold s0.sp w0 w1 w2 w3
    (BitVec.ofNat 64 v.length) tmpPtr (BitVec.ofNat 64 v.length)
    (bytesPlacedVtable tmpPtr v.length) (bytesPtr tmpPtr v.length)
    (BitVec.ofNat 64 v.length) (bytesData tmpPtr v.length) 0#64) (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
  intro hcl2 hro2
  refine SepWPp.weaken_pre (P' :=
    vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
      bytesBoxU8Buf A tmpPtr v ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
      stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
      memRegion (s0.sp - 224#64) 8 ∗
      memRegion (s0.sp - 216#64) 48 ∗
      memRegion (s0.sp - 168#64) 104 ∗
      savedRegsStack s0.sp s0)
    (Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, hsp]; rw [stackAt_slice_to_bytesFromVec s0.sp]; ac_rfl)) ?_
  exact hp3
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
    hsp_align
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr, htrace])
    (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, h25_0, h26_0, h27_0, h28_0, hvregs_0, and_self])
    hcl2 hro2
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])

theorem _root_.CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.phase2_from_0x0e4_nonempty_placed
    [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hmc : subroutine_ok (lsProg_558 H) ((blkPl_558).ρ lsMemcpySym)
      (withLsCl lsmpl framelessMemcpySpec))
    (hBytesFromVec : subroutine_ok (lsProg_558 H) (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A)))
    (hReserve : subroutine_ok (lsProg_558 H) (lsmpl.base 561)
      (withLsCl lsmpl (doReserveSpec A)))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {pfx rest0 : List (BitVec 8)} {b0 : BitVec 8} {v' : List (BitVec 8)}
    {tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 : BitVec 64}
    (hVtableDrop : subroutine_ok (lsProg_558 H)
      (bytesPlacedDropFnAddr tmpPtr (b0 :: v').length)
      (withLsCl lsmpl (bytesVtableDropSpec A tmpPtr (b0 :: v') (b0 :: v').length)))
    (hvar : decodeVarint x.bs = some (BitVec.ofNat 64 (b0 :: v').length, rest0))
    (hpfx : x.bs = pfx ++ rest0)
    (hle : (b0 :: v').length ≤ rest0.length)
    (hv_take : rest0.take (b0 :: v').length = b0 :: v')
    (hwt : x.wt = .lengthDelimited)
    (hbs_len : x.bs.length < 2 ^ 63)
    (hcapOk : BytesMergeCapOk x.valCap x.bs.length)
    (htmp_ne : tmpPtr ≠ 0#64)
    (hpc : s.pc = (blkPl_558).base + 228#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 (b0 :: v').length)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 rest0.length)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx21 : s.readReg64 .x21 = tmpPtr)
    (hx24 : s.readReg64 .x24 = x.slot)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp (lsProg_558 H) (s0.readReg64 .lr) s
      (((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗
        ((s0.sp - 152#64) ↦₆₄ w2) ∗ ((s0.sp - 144#64) ↦₆₄ w3) ∗
        ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
        ((s0.sp - 120#64) ↦₆₄ w6) ∗
        memRegion (s0.sp - 112#64) 32 ∗
        ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
        A.live tmpPtr (b0 :: v').length 1 ∗ memRegion tmpPtr (b0 :: v').length ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        savedRegsStack s0.sp s0)
      (MergePost A x s0 R) (MergePanic A x s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  set v := b0 :: v'
  have hpos : 0 < v.length := List.length_pos_of_ne_nil (List.cons_ne_nil b0 v')
  have hrest0_len : rest0.length ≤ x.bs.length := by rw [hpfx, List.length_append]; omega
  have hv_len : v.length < 2 ^ 63 := by omega
  have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrest0_toNat : (BitVec.ofNat 64 rest0.length).toNat = rest0.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmin_v : (if (BitVec.ofNat 64 v.length).ult (BitVec.ofNat 64 rest0.length) = true
      then BitVec.ofNat 64 v.length else BitVec.ofNat 64 rest0.length) = BitVec.ofNat 64 v.length := by
    by_cases hlt : v.length < rest0.length
    · have hult : (BitVec.ofNat 64 v.length).ult (BitVec.ofNat 64 rest0.length) = true := by
        simp [BitVec.ult, hlen_toNat, hrest0_toNat, hlt]
      simp [hult]
    · have heq : rest0.length = v.length := by omega
      simp [heq]
  have hrest0_ult_v : (BitVec.ofNat 64 rest0.length).ult (BitVec.ofNat 64 v.length) = false := by
    simp [BitVec.ult, hlen_toNat, hrest0_toNat, hle]
  have hlen_ne : (BitVec.ofNat 64 v.length == 0#64) = false := by
    apply beq_false_of_ne
    intro h
    have h2 := congrArg BitVec.toNat h
    rw [hlen_toNat] at h2
    exact absurd h2 (by dsimp [v]; omega)
  have hmerge : mergeBytes x.wt x.bs = some (v, rest0.drop v.length) := by
    have hm := mergeBytes_lengthDelimited_ok hwt hvar (by rw [hlen_toNat]; exact hle)
    rwa [hlen_toNat, hv_take] at hm
  have hp2 := fun {s : State} =>
    @CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.phase2_from_0x1b8_placed _ A H hmc hBytesFromVec hReserve
      x s0 s R v (rest0.drop v.length) tmpPtr tmpPtr (BitVec.ofNat 64 v.length) (BitVec.ofNat 64 v.length)
      (1#64 ||| (if (64#64 - BitVec.ofNat 64 (countLeadingZeros (BitVec.ofNat 64 v.length >>> 10))).ult 7#64 = true
        then 64#64 - BitVec.ofNat 64 (countLeadingZeros (BitVec.ofNat 64 v.length >>> 10)) else 7#64) <<< 2)
      w4 w5 w6 w80 hVtableDrop hmerge hv_len hbs_len hcapOk
  clear hBytesFromVec hReserve
  rw [sliceCursorAfter_split_copy x.slot x.ptr x.bs pfx rest0 v.length hpfx hle]
  rw [hv_take]
  have hadv := sliceCursorAfter_advance_fold x.slot x.ptr x.bs pfx rest0 v.length hpfx hle hbs_len
  dsimp only at hadv
  rw [hv_take] at hadv
  clear hpfx
  apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_558).ρ lsMemcpySym)
  wp_steps
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx21, hx24, hx29, hsp,
      hv_len, hmin_v, hrest0_ult_v, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
      bitvec_getLsbD_63_of_lt32, Prost.bitvec_ult_self, bitvec_sub_self_64, bitvec_if_zero_ult_self])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl1 hro1
  refine SepWPp.bm_call_frame_lscl (spec := framelessMemcpySpec)
    (x := (tmpPtr, x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length), v))
    (T := memRegion tmpPtr v.length ∗ ((x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)) ↦ₛ v))
    hmc hcl1 hro1
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx21, hx24, hx29, hsp,
      hv_len, hmin_v, hrest0_ult_v, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
      bitvec_getLsbD_63_of_lt32, Prost.bitvec_ult_self, bitvec_sub_self_64, bitvec_if_zero_ult_self])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    rfl
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx0, hx8, hx21, hx24, hx29, hsp,
      hv_len, hmin_v, hrest0_ult_v, hlen_ne, hlen_toNat, and_self])
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (by intro _ _ hm; dsimp only [framelessMemcpySpec] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
  intro sf_mc hpcf hrunf hspf hcsf hclf hrof
  obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f, hvregsf⟩ := hcsf
  obtain ⟨h25_0, h26_0, h27_0, h28_0, hvregs_0⟩ := hhigh
  simp (config := { decide := true }) only [arm64_norm, hsp, hx0, hx8, hx19, hx21, hx24, hx29, hmin_v] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f hvregsf
  simp (config := { decide := true }) only [framelessMemcpySpec, arm64_norm, htrace]
  refine SepWPp.pure_elim fun ⟨_, htr⟩ => ?_
  apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_558).base + 440#64)
  wp_steps
  apply SepWP.fold (fold_vecU8Buf_nonempty A tmpPtr v hpos hv_len htmp_ne) (by sep_focus)
  apply SepWP.fold hadv (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
  intro hcl2 hro2
  refine SepWPp.weaken_pre ?_
    (hp2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, h25_0, h26_0, h27_0, h28_0, hvregs_0, and_self])
      hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h20f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h20f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f])
      (by simp (config := { decide := true }) only [bytesMutDataWord, wp_norm, arm64_norm, h22f, ProofLib.ofNat_countLeadingZeros64])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29f]))
  exact Entails.of_eq (by simp only [ProofLib.ofNat_countLeadingZeros64]; ac_rfl)

theorem _root_.CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.phase2_from_0x094_placed
    [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hmc : subroutine_ok (lsProg_558 H) ((blkPl_558).ρ lsMemcpySym)
      (withLsCl lsmpl framelessMemcpySpec))
    (hshim : subroutine_ok (lsProg_558 H) ((blkPl_558).ρ lsRustNoAllocShimSym)
      (withLsCl lsmpl noAllocShimSpec))
    (halloc : subroutine_ok (lsProg_558 H) ((blkPl_558).ρ lsRustAllocSym)
      (withLsCl lsmpl (rustAllocSpec A)))
    (hpanic : (lsProg_558 H).externAt? ((blkPl_558).ρ lsHandleErrorSym) = some Rust.panicked)
    (hBytesFromVec : subroutine_ok (lsProg_558 H) (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A)))
    (hReserve : subroutine_ok (lsProg_558 H) (lsmpl.base 561)
      (withLsCl lsmpl (doReserveSpec A)))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (lsProg_558 H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpec A tmpPtr v v.length)))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {len : BitVec 64} {rest0 : List (BitVec 8)}
    (hwt : x.wt = .lengthDelimited)
    (hvar : decodeVarint x.bs = some (len, rest0))
    (hle : len.toNat ≤ rest0.length)
    (hbs_len : x.bs.length < 2 ^ 63)
    (hcapOk : BytesMergeCapOk x.valCap x.bs.length)
    (hpc : s.pc = (blkPl_558).base + 148#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = len)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 rest0.length)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx24 : s.readReg64 .x24 = x.slot)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp (lsProg_558 H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePost A x s0 R) (MergePanic A x s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  obtain ⟨pfx, hpfx⟩ := bm_decodeVarint_suffix hvar
  have hrest0_len : rest0.length ≤ x.bs.length := by rw [hpfx, List.length_append]; omega
  have hrest0_toNat : (BitVec.ofNat 64 rest0.length).toNat = rest0.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1b8_exit := fun (w4 w5 w6 w80 : BitVec 64) {s : State}
      (hmerge : mergeBytes x.wt x.bs = some ([], rest0)) =>
    @CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.phase2_from_0x1b8_placed _ A H hmc hBytesFromVec hReserve
      x s0 s R [] rest0 1#64 1#64 0#64 0#64 1#64 w4 w5 w6 w80 (hVtableDrop 1#64 []) hmerge (by decide) hbs_len hcapOk
  have h0e4_exit := fun (b0 : BitVec 8) (v' : List (BitVec 8)) (tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 : BitVec 64)
      {s : State}
      (hvar' : decodeVarint x.bs = some (BitVec.ofNat 64 (b0 :: v').length, rest0))
      (hle' : (b0 :: v').length ≤ rest0.length)
      (hv_take' : rest0.take (b0 :: v').length = b0 :: v')
      (htmp_ne : tmpPtr ≠ 0#64) =>
    @CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.phase2_from_0x0e4_nonempty_placed _ A H hmc hBytesFromVec hReserve
      x s0 s R pfx rest0 b0 v' tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 (hVtableDrop tmpPtr (b0 :: v'))
      hvar' hpfx hle' hv_take' hwt hbs_len hcapOk htmp_ne
  clear hBytesFromVec hReserve hVtableDrop
  refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 168#64) 104 ∗
    (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
      stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
      memRegion (s0.sp - 224#64) 8 ∗
      memRegion (s0.sp - 216#64) 48 ∗
      savedRegsStack s0.sp s0)) (Entails.of_eq (by ac_rfl)) ?_
  refine SepWPp.unfold_memRegion_168 fun w0 w1 w2 w3 w4 w5 w6 w80 => ?_
  rcases hv : rest0.take len.toNat with _ | ⟨b0, v'⟩
  · have hlen0 : len = 0#64 := by
      have hv_len0 : (rest0.take len.toNat).length = 0 := by rw [hv]; rfl
      rw [List.length_take_of_le hle] at hv_len0
      exact BitVec.eq_of_toNat_eq hv_len0
    have hmerge : mergeBytes x.wt x.bs = some ([], rest0) := by
      have hv_len0 : len.toNat = 0 := by rw [hlen0]; rfl
      have hdrop0 : rest0.drop len.toNat = rest0 := by rw [hv_len0]; rfl
      have hm := mergeBytes_lengthDelimited_ok hwt hvar hle
      rwa [hv, hdrop0] at hm
    clear hv
    have hmin0 : (if (0#64).ult (BitVec.ofNat 64 rest0.length) = true then 0#64 else BitVec.ofNat 64 rest0.length) = 0#64 :=
      bitvec_if_zero_ult_self (BitVec.ofNat 64 rest0.length)
    rw [← emp_sepConj (((s0.sp - 168#64) ↦₆₄ w0) ∗ _)]
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_558).base + 440#64)
    wp_steps
    apply SepWP.fold (vecU8Buf_nil_one A) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx29, hsp, hlen0, hmin0, bitvec_ult_zero, Prost.bitvec_ult_self, bitvec_sub_self_64])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl2 hro2
    refine SepWPp.weaken_pre ?_ (h1b8_exit w4 w5 w6 w80 hmerge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx29, hsp, hlen0, hmin0, bitvec_ult_zero, Prost.bitvec_ult_self, bitvec_sub_self_64])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
      (by obtain ⟨h25, h26, h27, h28, hvregs⟩ := hhigh; simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25, h26, h27, h28, hvregs, and_self])
      hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx0, hlen0, hmin0, bitvec_ult_zero, Prost.bitvec_ult_self, bitvec_sub_self_64])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx0, hlen0, hmin0, bitvec_ult_zero, Prost.bitvec_ult_self, bitvec_sub_self_64])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, bytesMutDataWord_zero])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx29]))
    exact Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, hsp]; ac_rfl)
  · set v := b0 :: v'
    have hlen_v : len = BitVec.ofNat 64 v.length := by
      have hv_len_eq : v.length = len.toNat := by rw [← hv, List.length_take_of_le hle]
      rw [hv_len_eq, BitVec.ofNat_toNat]; rfl
    have hle' : v.length ≤ rest0.length := by
      have hv_len_eq : v.length = len.toNat := by rw [← hv, List.length_take_of_le hle]
      omega
    have hv_take' : rest0.take v.length = v := by
      have hv_len_eq : v.length = len.toNat := by rw [← hv, List.length_take_of_le hle]
      rw [hv_len_eq]; exact hv
    clear hv
    have hpos : 0 < v.length := List.length_pos_of_ne_nil (List.cons_ne_nil b0 v')
    have hv_len : v.length < 2 ^ 63 := by omega
    have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hmin_v : (if (BitVec.ofNat 64 v.length).ult (BitVec.ofNat 64 rest0.length) = true
        then BitVec.ofNat 64 v.length else BitVec.ofNat 64 rest0.length) = BitVec.ofNat 64 v.length := by
      by_cases hlt : v.length < rest0.length
      · have hult : (BitVec.ofNat 64 v.length).ult (BitVec.ofNat 64 rest0.length) = true := by
          simp [BitVec.ult, hlen_toNat, hrest0_toNat, hlt]
        simp [hult]
      · have heq : rest0.length = v.length := by omega
        simp [heq]
    have hmsb : (BitVec.ofNat 64 v.length).getLsbD 63 = false :=
      bitvec_getLsbD_63_of_lt32 hv_len
    have hlen_ne : (BitVec.ofNat 64 v.length == 0#64) = false := by
      apply beq_false_of_ne
      intro h
      have h2 := congrArg BitVec.toNat h
      rw [hlen_toNat] at h2
      exact absurd h2 (by simp)
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_558).ρ lsRustNoAllocShimSym)
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx29, hsp,
        hlen_v, hmin_v, hv_len, hmsb, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
        bitvec_getLsbD_63_of_lt32])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl2 hro2
    refine SepWPp.bm_call_frame_lscl (spec := noAllocShimSpec) (x := ()) (T := emp)
      hshim hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx29, hsp,
        hlen_v, hmin_v, hv_len, hmsb, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
        bitvec_getLsbD_63_of_lt32])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
      (by simp [noAllocShimSpec]) trivial (by rw [emp_sepConj])
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (by intro _ _ hm; dsimp only [noAllocShimSpec] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
    intro sf_sh hpcf_sh hrunf_sh hspf_sh hcsf_sh hclf_sh hrof_sh
    obtain ⟨h19_sh, h20_sh, h21_sh, h22_sh, h23_sh, h24_sh, h25_sh, h26_sh, h27_sh, h28_sh, h29_sh, hvregs_sh⟩ := hcsf_sh
    simp (config := { decide := true }) only [arm64_norm, hsp, hx0, hx8, hx19, hx24, hx29, hlen_v, hmin_v] at hpcf_sh hspf_sh h19_sh h20_sh h21_sh h22_sh h23_sh h24_sh h25_sh h26_sh h27_sh h28_sh h29_sh hvregs_sh
    dsimp only [noAllocShimSpec]
    refine SepWPp.pure_elim fun htr_sh => ?_
    apply SepWPp.bm_of_sepWP_lscl hclf_sh hrof_sh (mid := (blkPl_558).ρ lsRustAllocSym)
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_sh])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_sh])
    intro hcl3 hro3
    rw [stackAt_slice_to_alloc s0.sp]
    refine SepWPp.bm_call_frame_lscl (spec := rustAllocSpec A) (x := (v.length, 1))
      (T := A.pool ∗ stackAt (s0.sp - 224#64) allocHookStack)
      halloc hcl3 hro3
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_sh])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_sh])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hspf_sh, hsp_align]) rfl
      (by simp (config := { decide := true }) only [rustAllocSpec, arm64_norm, hspf_sh, h21_sh]; rfl)
      (by refine ⟨hlen_toNat, hpos, ⟨0, rfl⟩, by simp only [v, List.length_cons] at hv_len ⊢; omega⟩)
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (by intro _ _ hm; dsimp only [rustAllocSpec] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
    intro sf_al hpcf_al hrunf_al hspf_al hcsf_al hclf_al hrof_al
    obtain ⟨h19_al, h20_al, h21_al, h22_al, h23_al, h24_al, h25_al, h26_al, h27_al, h28_al, h29_al, hvregs_al⟩ := hcsf_al
    simp (config := { decide := true }) only [arm64_norm, hspf_sh, h19_sh, h21_sh, h24_sh, h29_sh] at hpcf_al hspf_al h19_al h20_al h21_al h22_al h23_al h24_al h25_al h26_al h27_al h28_al h29_al hvregs_al
    simp (config := { decide := true }) only [rustAllocSpec, arm64_norm, htr_sh, htrace]
    by_cases h0 : sf_al.readReg64 .x0 = 0
    · simp only [h0, ↓reduceIte]
      refine SepWPp.weaken_pre (P' :=
        ⌜sf_al.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          (A.pool ∗ stackAt (s0.sp - 224#64) allocHookStack ∗
            ((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗
            ((s0.sp - 152#64) ↦₆₄ w2) ∗ ((s0.sp - 144#64) ↦₆₄ w3) ∗
            ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
            ((s0.sp - 120#64) ↦₆₄ w6) ∗
            memRegion (s0.sp - 112#64) 32 ∗
            ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
            vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
            (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗
            memRegion (s0.sp - 8496#64) 4176 ∗
            memRegion (s0.sp - 224#64) 8 ∗
            memRegion (s0.sp - 216#64) 48 ∗
            savedRegsStack s0.sp s0))
        (Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, hspf_sh])) ?_
      refine SepWPp.pure_elim fun htr_al => ?_
      have h0_64 : sf_al.readReg64 .x0 = 0#64 := h0
      apply SepWPp.of_sepWP (mid := (blkPl_558).ρ lsHandleErrorSym)
      wp_steps
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_al, h0_64])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_al])
      refine SepWPp.panic
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_al])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_al, h0_64]; exact hpanic)
        fun hm => ?_
      dsimp only [bytesMergeRawSpec]
      exact allowPanic_panicked (allocFailedIn_of_eq (by simp (config := { decide := true }) only [Rust.panicked, wp_norm, arm64_norm, htr_al])) hm
    · have h0_64 : sf_al.readReg64 .x0 ≠ 0#64 := h0
      have h0_beq : (sf_al.readReg64 .x0 == 0#64) = false := beq_false_of_ne h0_64
      simp only [h0, ↓reduceIte]
      refine SepWPp.weaken_pre (P' :=
        ⌜(sf_al.readReg64 .x0).toNat % 1 = 0 ∧ sf_al.trace = s0.trace⌝ ∗
          (((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗
            ((s0.sp - 152#64) ↦₆₄ w2) ∗ ((s0.sp - 144#64) ↦₆₄ w3) ∗
            ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
            ((s0.sp - 120#64) ↦₆₄ w6) ∗
            memRegion (s0.sp - 112#64) 32 ∗
            ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
            A.live (sf_al.readReg64 .x0) (b0 :: v').length 1 ∗ memRegion (sf_al.readReg64 .x0) (b0 :: v').length ∗
            vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
            (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
            stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
            memRegion (s0.sp - 224#64) 8 ∗
            memRegion (s0.sp - 216#64) 48 ∗
            savedRegsStack s0.sp s0))
        (Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, hspf_sh]; rw [stackAt_slice_to_alloc s0.sp]; ac_rfl)) ?_
      refine SepWPp.pure_elim fun ⟨_, htr_al⟩ => ?_
      dsimp only [sliceCursorAfter]
      apply SepWPp.bm_of_sepWP_lscl hclf_al hrof_al (mid := (blkPl_558).base + 228#64)
      wp_steps
      apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length))) ∗
          ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗ (x.ptr ↦ₛ x.bs) ⊢
          sliceCursorAfter x.slot x.ptr x.bs rest0 from Entails.refl _) (by sep_focus)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_al, h0_beq])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_al])
      intro hcl4 hro4
      have hvar' : decodeVarint x.bs = some (BitVec.ofNat 64 (b0 :: v').length, rest0) := by rwa [← hlen_v]
      obtain ⟨h25_0, h26_0, h27_0, h28_0, hvregs_0⟩ := hhigh
      refine SepWPp.weaken_pre ?_ (h0e4_exit b0 v' (sf_al.readReg64 .x0) w0 w1 w2 w3 w4 w5 w6 w80
        hvar' hle' hv_take' h0_64
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_al, h0_beq])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_al])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf_al])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr_al])
        (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25_al, h26_al, h27_al, h28_al, hvregs_al, h25_sh, h26_sh, h27_sh, h28_sh, hvregs_sh, h25_0, h26_0, h27_0, h28_0, hvregs_0, and_self])
        hcl4 hro4
        (by dsimp only [v]; simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24_al])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19_al])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24_al])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29_al]))
      exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Prost.BytesMerge
