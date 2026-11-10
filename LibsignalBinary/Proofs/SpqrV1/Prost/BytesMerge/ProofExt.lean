/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Proof
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve -- shake: keep

@[expose] public section

set_option autoImplicit false

/-!
# `prost::encoding::bytes::merge [local#3]`: `AllocContracts4K` Verification

Lifts `bytes_merge_3_ok_ext` and `bytes_merge_3_proto_ok_ext` to 4 KB stack-bounded
`AllocContracts4K` (`allocHookStack = 4096` B).
-/

namespace CryptoVerification.SpqrV1.Prost.BytesMerge

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
open CryptoVerification.LibsignalTripleRatchet.VarintBridge
open CryptoVerification.SpqrV1.Alloc hiding doReserve7Name
open CryptoVerification.SpqrV1.Varint hiding decodeVarint2Name decodeVarint2_fnOff
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bytesMerge3_fnOff decodeVarint2_fnOff doReserve7_fnOff
attribute [local simp]
  bytesMutDataWord_zero bytesMutDataWord_bit0 bytesMutDataWord_getLsbD_zero
  bytesMutDataWord_getElem_zero bytesMutDataWord_lsr5 bitvec_ult_zero
  bitvec_ult_33bits_of_lt32 bitvec_msb_false_of_lt32 bitvec_getLsbD_63_of_lt32
  Prost.bitvec_ult_self bitvec_sub_self_64 bitvec_if_zero_ult_self

private theorem dealloc_opt_of_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff deallocName) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv none (rustDeallocExternSpecWithStack A allocHookStack)) :=
  subroutine_ok_to_optNone
    (rustDeallocExternWithStack_of_rustDealloc (hookStack := allocHookStack)
      (hA.dealloc_ok_at name k hk))

/-- Unified vtable `drop` dispatch meets `bytesVtableDropSpec` on `tripleRatchetProgAtExt b ext`
under `AllocContracts4K b A ext`. -/
theorem bytesVtableDrop_base_ok_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      (bytesDropFnAddr b ptr bs.length)
      (bytesVtableDropSpec A ptr bs off) :=
  subroutine_ok_of_optNone
    (bytesVtableDrop_base_ok_of_drops_opt
      (promotableEvenDrop_base_ok_of_dealloc_opt (by decide)
        (dealloc_opt_of_4k hA (by fnoff_eq)))
      (promotableOddDrop_base_ok_of_dealloc_opt (by decide)
        (dealloc_opt_of_4k hA (by fnoff_eq)))
      ptr bs off)

/-- Right-associated `4096`-byte stack variant of `framelessMemcpySpec` for `SepWPp.call_frame_keep`. -/
def framelessMemcpySpec4K : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s0.sp allocHookStack)
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp allocHookStack)

theorem framelessMemcpy4K_of_sessionMemcpyRegion {prog : Program} {addr : BitVec 64}
    (h : subroutine_ok prog addr (withStack sessionMemcpyRegionSpec allocHookStack)) :
    subroutine_ok prog addr framelessMemcpySpec4K := by
  refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack sessionMemcpyRegionSpec allocHookStack).pre (dst, src, bs) s0 ∗ R := by
    dsimp only [framelessMemcpySpec4K, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  refine (h.to_outcome (dst, src, bs) R s0 hpc hrun hpre' hal).mono_outcome ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [framelessMemcpySpec4K, withStack, sessionMemcpyRegionSpec] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr hfail

private theorem mergePanic_of_allocFailed_4k {A : RustAlloc} {x : BytesMergeGhost}
    {s0 s_call sf : State} {F R : SepProp} (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (bytesMergeRawSpec A).onPanic x s0 sf ∗ R := by
  dsimp only [bytesMergeRawSpec, allocFailedIn] at hm ⊢; rw [htr] at hm; exact allowPanic_frame id hm

private theorem decodeVarintAux_length_lt_4k (i : Nat) (acc : BitVec 64) (bs rest0 : List (BitVec 8))
    (len : BitVec 64) (h : decodeVarintAux i acc bs = some (len, rest0)) :
    rest0.length < bs.length := by
  induction bs generalizing i acc with
  | nil => simp [decodeVarintAux] at h
  | cons b bs' ih =>
    unfold decodeVarintAux at h; dsimp only at h
    split at h
    · split at h
      · contradiction
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; simp
    · split at h
      · contradiction
      · have hlt := ih _ _ h; simp; omega

private theorem mergeBytes_length_sum_4k {wt : WireType} {bs v rest : List (BitVec 8)}
    (h : mergeBytes wt bs = some (v, rest)) :
    1 + v.length + rest.length ≤ bs.length := by
  cases wt <;> try simp [mergeBytes] at h
  cases hvar : decodeVarint bs with
  | none => simp [hvar] at h
  | some p =>
    rcases p with ⟨len, rest0⟩; rw [hvar] at h; dsimp only at h
    split at h
    · contradiction
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      have h1 := decodeVarintAux_length_lt_4k 0 0 bs rest0 len hvar
      have h2 : (rest0.take len.toNat).length + (rest0.drop len.toNat).length = rest0.length := by
        rw [← List.length_append, List.take_append_drop]
      omega

theorem phase3_from_0x230_4k {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hmc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + bv% (ls_off% "memcpy" - 0x47d44))
      framelessMemcpySpec4K)
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr cap' ptr' : BitVec 64}
    (hVtableDrop : subroutine_ok (libsignalSessionCode.rebase img.base H)
      (bytesDropFnAddr img.base tmpPtr v.length)
      ((bytesVtableDropSpec A tmpPtr v v.length).inImage img))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hcapOk : BytesMergeCapOk cap' rest.length)
    (hcap' : v.length ≤ cap'.toNat)
    (hv_len : v.length < 2 ^ 63)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + 560#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hfl : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 v.length)
    (hx21 : s.readReg64 .x21 = bytesPtr tmpPtr v.length)
    (hx22 : s.readReg64 .x22 = bytesData tmpPtr v.length)
    (hx23 : s.readReg64 .x23 = 0#64)
    (hx24 : s.readReg64 .x24 = bytesVtable img.base tmpPtr v.length) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
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
      @epilogue3_vtableDrop_0x254 img A H himg hVtableSlot x s0 s R [] rest tmpPtr cap' ptr' hVtableDrop hmerge hcapOk
    merge3_fetches_H img.base H bytesMerge3_fnOff 560 4
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name = entry
    examples_hide_fetches
    apply SepWPp.bm_of_sepWP_inv hfl hsym (mid := entry + 596#64)
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hfl1 hsym1
    exact hep
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
      hhigh hfl1 hsym1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx21])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx24])
  · set v := b0 :: v'
    have hep := fun {s : State} =>
      @epilogue3_vtableDrop_0x254 img A H himg hVtableSlot x s0 s R v rest tmpPtr cap' ptr' hVtableDrop hmerge hcapOk
    have hpos : 0 < v.length := List.length_pos_of_ne_nil (List.cons_ne_nil b0 v')
    have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlen_ne : (BitVec.ofNat 64 v.length == 0#64) = false := by
      apply beq_false_of_ne; intro h
      have h2 := congrArg BitVec.toNat h; rw [hlen_toNat] at h2; exact absurd h2 (by dsimp [v]; omega)
    have hbytesPtr : bytesPtr tmpPtr v.length = tmpPtr := by
      unfold bytesPtr; have : v.length ≠ 0 := by omega
      simp [this]
    rw [vecU8At_nil_eq A x.valPtr cap' ptr' v hpos hcap', sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, hcap_lt, hptr'⟩ => ?_
    rw [bytesBoxU8Buf_nonempty A tmpPtr v hpos]
    refine SepWPp.weaken_pre (P' := ⌜tmpPtr ≠ 0#64 ∧ v.length < 2 ^ 63⌝ ∗
      ((x.valPtr ↦₆₄ cap') ∗ ((x.valPtr + 8#64) ↦₆₄ ptr') ∗ ((x.valPtr + 16#64) ↦₆₄ 0#64) ∗
        A.live ptr' cap'.toNat 1 ∗ memRegion ptr' v.length ∗
        memRegion (ptr' + BitVec.ofNat 64 v.length) (cap'.toNat - v.length) ∗
        A.live tmpPtr v.length 1 ∗ (tmpPtr ↦ₛ v) ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗ stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗ memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗ savedRegsStack s0.sp s0)) (Entails.of_eq (by ac_rfl)) ?_
    refine SepWPp.pure_elim fun ⟨htmp_ne, hv_lt63⟩ => ?_
    merge3_fetches_H img.base H bytesMerge3_fnOff 560 36
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name = entry
    examples_hide_fetches
    apply SepWPp.bm_of_sepWP_inv hfl hsym (mid := entry + bv% (ls_off% "memcpy" - 0x47d44))
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hlen_ne])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hfl1 hsym1
    rw [stackAt_slice_to_alloc s0.sp]
    refine SepWPp.call_frame_keep (x := (ptr', tmpPtr, v))
      (T := memRegion ptr' v.length ∗ (tmpPtr ↦ₛ v) ∗ stackAt (s0.sp - 224#64) allocHookStack)
      hmc hfl1 hsym1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hlen_ne])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
      (by simp (config := { decide := true }) only [framelessMemcpySpec4K, arm64_norm, hsp]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm, hlen_toNat, hv_lt63, and_self])
      (by sep_focus) (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (by intro _ _ hm; dsimp only [framelessMemcpySpec4K] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
    intro sf_mc hpcf hrunf hspf hcsf hflf hsymf
    have hhigh' : bm_HighCalleeSaved s0 sf_mc := hhigh.of_calleeSaved hcsf
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, _, _, _, _, h29f, hvregsf⟩ := hcsf
    simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf h19f h20f h21f h22f h23f h24f h29f hvregsf
    simp (config := { decide := true }) only [framelessMemcpySpec4K, arm64_norm, hsp, htrace]
    refine SepWPp.pure_elim fun ⟨_, htr⟩ => ?_
    apply SepWPp.bm_of_sepWP_inv hflf hsymf (mid := entry + 596#64)
    wp_steps
    apply SepWP.fold (fold_bytesBoxU8Buf_nonempty A tmpPtr v hpos htmp_ne hv_lt63) (by sep_focus)
    apply SepWP.fold (fold_vecU8At_copied A x.valPtr cap' ptr' v hpos hcap' hcap_lt hptr') (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hfl2 hsym2
    refine SepWPp.weaken_pre (P' :=
      vecU8At A x.valPtr cap' ptr' v ∗ bytesBoxU8Buf A tmpPtr v ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗ stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗ memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗ savedRegsStack s0.sp s0)
      (Entails.of_eq (by rw [stackAt_slice_to_alloc s0.sp]; ac_rfl)) ?_
    exact hep
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf]) hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by obtain ⟨h25, h26, h27, h28, hvregs⟩ := hhigh'; simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25, h26, h27, h28, hvregs, and_self])
      hfl2 hsym2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f, hx21, h20f, hx20, hbytesPtr])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h22f, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24f, hx24])

theorem phase3_from_0x210_4k {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hmc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + bv% (ls_off% "memcpy" - 0x47d44))
      framelessMemcpySpec4K)
    (hReserve : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr doReserve7Name) (doReserveSpec A))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp} {v rest : List (BitVec 8)} {tmpPtr : BitVec 64}
    (hVtableDrop : subroutine_ok (libsignalSessionCode.rebase img.base H)
      (bytesDropFnAddr img.base tmpPtr v.length) ((bytesVtableDropSpec A tmpPtr v v.length).inImage img))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hv_len : v.length < 2 ^ 63) (hbs_len : x.bs.length < 2 ^ 63)
    (hcapOk : BytesMergeCapOk x.valCap x.bs.length)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + 528#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 224#64) (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace) (hhigh : bm_HighCalleeSaved s0 s)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hx19 : s.readReg64 .x19 = x.valPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 v.length)
    (hx21 : s.readReg64 .x21 = bytesPtr tmpPtr v.length)
    (hx22 : s.readReg64 .x22 = bytesData tmpPtr v.length)
    (hx24 : s.readReg64 .x24 = bytesVtable img.base tmpPtr v.length) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗ bytesBoxU8Buf A tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗ memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗ memRegion (s0.sp - 168#64) 104 ∗ savedRegsStack s0.sp s0)
      (MergePost A x s0 R) (MergePanic A x s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hsum : 1 + v.length + rest.length ≤ x.bs.length := mergeBytes_length_sum_4k hmerge
  have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hReserve' : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + 24420#64)
      (doReserveSpec A) := by
    rw [fnAddr_offset_eq_H (name := bytesMerge3Name) (callee := doReserve7Name) (k := 24420#64)]
    exact hReserve
  clear hReserve
  have hp3 := fun (cap' ptr' : BitVec 64) {s : State}
      (hcapOk' : BytesMergeCapOk cap' rest.length) (hcap' : v.length ≤ cap'.toNat) =>
    @phase3_from_0x230_4k img A H himg hmc hVtableSlot x s0 s R v rest tmpPtr cap' ptr'
      hVtableDrop hmerge hcapOk' hcap' hv_len
  rw [bm_vecU8At_eq_header_sep_buf A x.valPtr x.valCap x.valBuf x.valBs]
  merge3_fetches_H img.base H bytesMerge3_fnOff 528 32
  merge3_fetches_H img.base H bytesMerge3_fnOff 668 52
  dsimp only [vecHeader] at hpc hReserve' hp3 ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name = entry
  examples_hide_fetches
  apply SepWPp.bm_of_sepWP_inv hfl hsym
    (mid := if x.valCap.ult (BitVec.ofNat 64 v.length) = true then entry + 668#64 else entry + 544#64)
  wp_steps
  apply SepWP.fold (fold_vecU8At_clear A x.valPtr x.valCap x.valBuf x.valBs) (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hfl1 hsym1
  by_cases hult : x.valCap.ult (BitVec.ofNat 64 v.length) = true
  · simp only [hult, ↓reduceIte] at hfl1 hsym1 ⊢
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
    apply SepWPp.bm_of_sepWP_inv hfl1 hsym1 (mid := entry + 24420#64)
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hfl2 hsym2
    rw [stackAt_slice_to_doReserve s0.sp]
    refine SepWPp.call_frame_keep
      (x := { v := x.valPtr, cap := x.valCap, ptr := x.valBuf, bs := [], additional := v.length })
      (T := vecU8At A x.valPtr x.valCap x.valBuf [] ∗ A.pool ∗ stackAt (s0.sp - 224#64) doReserveStack)
      hReserve' hfl2 hsym2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
      (by simp (config := { decide := true }) only [doReserveSpec, arm64_norm, hsp, hx19, hx20]; rfl)
      (by exact ⟨hlen_toNat, hnewCap_bound⟩)
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (by intro _ _ hm; exact mergePanic_of_allocFailed_4k (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace]) hm) ?_
    intro sf_res hpcf hrunf hspf hcsf hflf hsymf
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
    apply SepWPp.bm_of_sepWP_inv hflf hsymf (mid := entry + 560#64)
    wp_steps
    apply SepWP.fold
      (fold_vecU8At_clear A x.valPtr (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' [])
      (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hx20, hnewCap_ule])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hfl3 hsym3
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
      hfl3 hsym3
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f, hx19])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h20f, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f, hx21])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h22f, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h23f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24f, hx24])
  · have hult_eq : x.valCap.ult (BitVec.ofNat 64 v.length) = false :=
      Bool.eq_false_iff.mpr hult
    simp only [hult_eq, Bool.false_eq_true, ↓reduceIte] at hfl1 hsym1 ⊢
    have hcap_ge : v.length ≤ x.valCap.toNat := by
      simp [BitVec.ult, hlen_toNat] at hult_eq
      exact hult_eq
    have hcapOk' : BytesMergeCapOk x.valCap rest.length :=
      bytesMergeCapOk_mono hcapOk (by omega)
    apply SepWPp.bm_of_sepWP_inv hfl1 hsym1
      (mid := if x.valCap.ult (BitVec.ofNat 64 v.length) = true then entry + 712#64 else entry + 560#64)
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult_eq])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hfl2 hsym2
    exact hp3 x.valCap x.valBuf hcapOk' hcap_ge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult_eq])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
      (by obtain ⟨h25, h26, h27, h28, hvregs⟩ := hhigh; simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25, h26, h27, h28, hvregs, and_self])
      hfl2 hsym2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx21])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx24])

theorem phase2_from_0x1b8_4k {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hmc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + bv% (ls_off% "memcpy" - 0x47d44))
      framelessMemcpySpec4K)
    (hBytesFromVec : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img))
    (hReserve : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr doReserve7Name) (doReserveSpec A))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 : BitVec 64}
    (hVtableDrop : subroutine_ok (libsignalSessionCode.rebase img.base H)
      (bytesDropFnAddr img.base tmpPtr v.length) ((bytesVtableDropSpec A tmpPtr v v.length).inImage img))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hv_len : v.length < 2 ^ 63) (hbs_len : x.bs.length < 2 ^ 63)
    (hcapOk : BytesMergeCapOk x.valCap x.bs.length)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + 440#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 224#64) (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace) (hhigh : bm_HighCalleeSaved s0 s)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 v.length) (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 v.length) (hx21 : s.readReg64 .x21 = tmpPtr)
    (hx22 : s.readReg64 .x22 = bytesMutDataWord (BitVec.ofNat 64 v.length))
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗ ((s0.sp - 152#64) ↦₆₄ w2) ∗
        ((s0.sp - 144#64) ↦₆₄ w3) ∗ ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
        ((s0.sp - 120#64) ↦₆₄ w6) ∗ memRegion (s0.sp - 112#64) 32 ∗
        ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
        bm_vecU8Buf A (BitVec.ofNat 64 v.length) tmpPtr v ∗ vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗ memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗ savedRegsStack s0.sp s0)
      (MergePost A x s0 R) (MergePanic A x s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hBytesFromVec' : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + bv% (ls_off% "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from" + 0x10000000000000000 - 0x47d44))
      ((bytesFromVecSpec A img.base).inImage img) := by
    rw [fnAddr_offset_eq_H (name := bytesMerge3Name) (callee := bytesFromVecName) (k := bv% (ls_off% "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from" + 0x10000000000000000 - 0x47d44)) (hk := by simp only [arm64_norm, bytesMerge3Name, bytesFromVecName])]
    exact hBytesFromVec
  have hp3 := fun {s : State} =>
    @phase3_from_0x210_4k img A H himg hmc hReserve hVtableSlot x s0 s R v rest tmpPtr
      hVtableDrop hmerge hv_len hbs_len hcapOk
  clear hBytesFromVec hReserve
  merge3_fetches_H img.base H bytesMerge3_fnOff 440 88
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name = entry
  examples_hide_fetches
  apply SepWPp.bm_of_sepWP_inv hfl hsym (mid := entry + bv% (ls_off% "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from" + 0x10000000000000000 - 0x47d44))
  wp_steps
  apply SepWP.fold (fold_vecU8At_sp136 A s0.sp (BitVec.ofNat 64 v.length) tmpPtr v) (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx21, hx22, hx29, hsp,
      bytesMutDataWord_getElem_zero, bytesMutDataWord_lsr5, bitvec_ult_zero])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hfl1 hsym1
  rw [stackAt_slice_to_bytesFromVec s0.sp]
  refine SepWPp.bm_call_frame_inv
    (x := (s0.sp - 136#64, s0.sp - 112#64, BitVec.ofNat 64 v.length, tmpPtr, v))
    (T := vecU8At A (s0.sp - 136#64) (BitVec.ofNat 64 v.length) tmpPtr v ∗
      memRegion (s0.sp - 112#64) 32 ∗
      stackAt (s0.sp - 224#64) bytesFromVecStack)
    hBytesFromVec' hfl1 hsym1
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx21, hx22, hx29, hsp,
      bytesMutDataWord_getElem_zero, bytesMutDataWord_lsr5, bitvec_ult_zero])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [bytesFromVecSpec, arm64_norm, hsp, hx29])
    hlen_toNat
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (by intro _ _ hm; dsimp only [bytesFromVecSpec] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
  intro sf_bfv hpcf hrunf hspf hcsf hflf hsymf
  obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f, hvregsf⟩ := hcsf
  obtain ⟨h25_0, h26_0, h27_0, h28_0, hvregs_0⟩ := hhigh
  simp (config := { decide := true }) only [arm64_norm, hsp, hx0, hx19, hx20, hx21, hx22, hx29,
    bytesMutDataWord_getElem_zero, bytesMutDataWord_lsr5, bitvec_ult_zero] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f hvregsf
  dsimp only [bytesFromVecSpec]
  rw [sepConj_assoc, sepConj_assoc]
  refine SepWPp.pure_elim fun htr => ?_
  rw [unfold_vecHeader_sp136, unfold_bytesAt_sp112]
  apply SepWPp.bm_of_sepWP_inv hflf hsymf (mid := entry + 528#64)
  wp_steps
  apply SepWP.fold (memRegion_104_fold s0.sp w0 w1 w2 w3
    (BitVec.ofNat 64 v.length) tmpPtr (BitVec.ofNat 64 v.length)
    (bytesVtable img.base tmpPtr v.length) (bytesPtr tmpPtr v.length)
    (BitVec.ofNat 64 v.length) (bytesData tmpPtr v.length) 0#64) (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
  intro hfl2 hsym2
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
    hfl2 hsym2
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])

theorem phase2_from_0x0e4_nonempty_4k {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hmc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + bv% (ls_off% "memcpy" - 0x47d44))
      framelessMemcpySpec4K)
    (hBytesFromVec : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img))
    (hReserve : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr doReserve7Name) (doReserveSpec A))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {pfx rest0 : List (BitVec 8)} {b0 : BitVec 8} {v' : List (BitVec 8)}
    {tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 : BitVec 64}
    (hVtableDrop : subroutine_ok (libsignalSessionCode.rebase img.base H)
      (bytesDropFnAddr img.base tmpPtr (b0 :: v').length)
      ((bytesVtableDropSpec A tmpPtr (b0 :: v') (b0 :: v').length).inImage img))
    (hvar : decodeVarint x.bs = some (BitVec.ofNat 64 (b0 :: v').length, rest0))
    (hpfx : x.bs = pfx ++ rest0) (hle : (b0 :: v').length ≤ rest0.length)
    (hv_take : rest0.take (b0 :: v').length = b0 :: v') (hwt : x.wt = .lengthDelimited)
    (hbs_len : x.bs.length < 2 ^ 63) (hcapOk : BytesMergeCapOk x.valCap x.bs.length)
    (htmp_ne : tmpPtr ≠ 0#64)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 224#64) (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace) (hhigh : bm_HighCalleeSaved s0 s)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 (b0 :: v').length)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 rest0.length)
    (hx19 : s.readReg64 .x19 = x.valPtr) (hx21 : s.readReg64 .x21 = tmpPtr)
    (hx24 : s.readReg64 .x24 = x.slot) (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗ ((s0.sp - 152#64) ↦₆₄ w2) ∗
        ((s0.sp - 144#64) ↦₆₄ w3) ∗ ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
        ((s0.sp - 120#64) ↦₆₄ w6) ∗ memRegion (s0.sp - 112#64) 32 ∗
        ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
        A.live tmpPtr (b0 :: v').length 1 ∗ memRegion tmpPtr (b0 :: v').length ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗ memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗ savedRegsStack s0.sp s0)
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
    @phase2_from_0x1b8_4k img A H himg hmc hBytesFromVec hReserve hVtableSlot x s0 s R
      v (rest0.drop v.length) tmpPtr tmpPtr (BitVec.ofNat 64 v.length) (BitVec.ofNat 64 v.length)
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
  merge3_fetches_H img.base H bytesMerge3_fnOff 228 212
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name = entry
  examples_hide_fetches
  apply SepWPp.bm_of_sepWP_inv hfl hsym (mid := entry + bv% (ls_off% "memcpy" - 0x47d44))
  wp_steps
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx21, hx24, hx29, hsp,
      hv_len, hmin_v, hrest0_ult_v, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
      bitvec_getLsbD_63_of_lt32, Prost.bitvec_ult_self, bitvec_sub_self_64, bitvec_if_zero_ult_self])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hfl1 hsym1
  rw [stackAt_slice_to_alloc s0.sp]
  refine SepWPp.call_frame_keep
    (x := (tmpPtr, x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length), v))
    (T := memRegion tmpPtr v.length ∗ ((x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)) ↦ₛ v) ∗
      stackAt (s0.sp - 224#64) allocHookStack)
    hmc hfl1 hsym1
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx21, hx24, hx29, hsp,
      hv_len, hmin_v, hrest0_ult_v, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
      bitvec_getLsbD_63_of_lt32, Prost.bitvec_ult_self, bitvec_sub_self_64, bitvec_if_zero_ult_self])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [framelessMemcpySpec4K, arm64_norm, hsp]; rfl)
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx0, hx8, hx21, hx24, hx29, hsp,
      hv_len, hmin_v, hrest0_ult_v, hlen_ne, hlen_toNat, and_self])
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (by intro _ _ hm; dsimp only [framelessMemcpySpec4K] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
  intro sf_mc hpcf hrunf hspf hcsf hflf hsymf
  obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f, hvregsf⟩ := hcsf
  obtain ⟨h25_0, h26_0, h27_0, h28_0, hvregs_0⟩ := hhigh
  simp (config := { decide := true }) only [arm64_norm, hsp, hx0, hx8, hx19, hx21, hx24, hx29, hmin_v] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f hvregsf
  simp (config := { decide := true }) only [framelessMemcpySpec4K, arm64_norm, hsp, htrace]
  refine SepWPp.pure_elim fun ⟨_, htr⟩ => ?_
  apply SepWPp.bm_of_sepWP_inv hflf hsymf (mid := entry + 440#64)
  wp_steps
  apply SepWP.fold (fold_vecU8Buf_nonempty A tmpPtr v hpos hv_len htmp_ne) (by sep_focus)
  apply SepWP.fold hadv (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
  intro hfl2 hsym2
  refine SepWPp.weaken_pre ?_ (hp2
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf]) hsp_align
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
    (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, h25_0, h26_0, h27_0, h28_0, hvregs_0, and_self])
    hfl2 hsym2
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h20f]) (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h20f]) (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f])
    (by simp (config := { decide := true }) only [bytesMutDataWord, wp_norm, arm64_norm, h22f, ProofLib.ofNat_countLeadingZeros64])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29f]))
  exact Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, hsp, ProofLib.ofNat_countLeadingZeros64]; rw [stackAt_slice_to_alloc s0.sp]; ac_rfl)

theorem phase2_from_0x094_4k {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hmc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + bv% (ls_off% "memcpy" - 0x47d44)) framelessMemcpySpec4K)
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x47d44)) noAllocShimSpec)
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + bv% (ls_off% "__rustc::__rust_alloc" - 0x47d44)) (rustAllocSpec A))
    (hpanic : (libsignalSessionCode.rebase img.base H).externAt?
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x47d44)) = some Rust.panicked)
    (hBytesFromVec : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesFromVecName) ((bytesFromVecSpec A img.base).inImage img))
    (hReserve : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr doReserve7Name) (doReserveSpec A))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (libsignalSessionCode.rebase img.base H) (bytesDropFnAddr img.base tmpPtr v.length)
        ((bytesVtableDropSpec A tmpPtr v v.length).inImage img))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp} {len : BitVec 64} {rest0 : List (BitVec 8)}
    (hwt : x.wt = .lengthDelimited) (hvar : decodeVarint x.bs = some (len, rest0))
    (hle : len.toNat ≤ rest0.length) (hbs_len : x.bs.length < 2 ^ 63) (hcapOk : BytesMergeCapOk x.valCap x.bs.length)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + 148#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 224#64) (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace) (hhigh : bm_HighCalleeSaved s0 s) (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hx0 : s.readReg64 .x0 = len) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 rest0.length)
    (hx19 : s.readReg64 .x19 = x.valPtr) (hx24 : s.readReg64 .x24 = x.slot) (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗ memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗ memRegion (s0.sp - 168#64) 104 ∗ savedRegsStack s0.sp s0)
      (MergePost A x s0 R) (MergePanic A x s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  obtain ⟨pfx, hpfx⟩ := bm_decodeVarint_suffix hvar
  have hrest0_len : rest0.length ≤ x.bs.length := by rw [hpfx, List.length_append]; omega
  have hrest0_toNat : (BitVec.ofNat 64 rest0.length).toNat = rest0.length := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1b8_exit := fun (w4 w5 w6 w80 : BitVec 64) {s : State} (hmerge : mergeBytes x.wt x.bs = some ([], rest0)) =>
    @phase2_from_0x1b8_4k img A H himg hmc hBytesFromVec hReserve hVtableSlot x s0 s R
      [] rest0 1#64 1#64 0#64 0#64 1#64 w4 w5 w6 w80 (hVtableDrop 1#64 []) hmerge (by decide) hbs_len hcapOk
  have h0e4_exit := fun (b0 : BitVec 8) (v' : List (BitVec 8)) (tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 : BitVec 64) {s : State}
      (hvar' : decodeVarint x.bs = some (BitVec.ofNat 64 (b0 :: v').length, rest0))
      (hle' : (b0 :: v').length ≤ rest0.length) (hv_take' : rest0.take (b0 :: v').length = b0 :: v') (htmp_ne : tmpPtr ≠ 0#64) =>
    @phase2_from_0x0e4_nonempty_4k img A H himg hmc hBytesFromVec hReserve hVtableSlot x s0 s R
      pfx rest0 b0 v' tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 (hVtableDrop tmpPtr (b0 :: v'))
      hvar' hpfx hle' hv_take' hwt hbs_len hcapOk htmp_ne
  clear hBytesFromVec hReserve hVtableDrop
  merge3_fetches_H img.base H bytesMerge3_fnOff 148 140
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name = entry
  examples_hide_fetches
  refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 168#64) 104 ∗
    (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
      stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗ memRegion (s0.sp - 224#64) 8 ∗
      memRegion (s0.sp - 216#64) 48 ∗ savedRegsStack s0.sp s0)) (Entails.of_eq (by ac_rfl)) ?_
  refine SepWPp.unfold_memRegion_168 fun w0 w1 w2 w3 w4 w5 w6 w80 => ?_
  rcases hv : rest0.take len.toNat with _ | ⟨b0, v'⟩
  · have hlen0 : len = 0#64 := by
      have hv_len0 : (rest0.take len.toNat).length = 0 := by rw [hv]; rfl
      rw [List.length_take_of_le hle] at hv_len0; exact BitVec.eq_of_toNat_eq hv_len0
    have hmerge : mergeBytes x.wt x.bs = some ([], rest0) := by
      have hv_len0 : len.toNat = 0 := by rw [hlen0]; rfl
      have hdrop0 : rest0.drop len.toNat = rest0 := by rw [hv_len0]; rfl
      have hm := mergeBytes_lengthDelimited_ok hwt hvar hle; rwa [hv, hdrop0] at hm
    clear hv
    have hmin0 : (if (0#64).ult (BitVec.ofNat 64 rest0.length) = true then 0#64 else BitVec.ofNat 64 rest0.length) = 0#64 :=
      bitvec_if_zero_ult_self (BitVec.ofNat 64 rest0.length)
    rw [← emp_sepConj (((s0.sp - 168#64) ↦₆₄ w0) ∗ _)]
    apply SepWPp.bm_of_sepWP_inv hfl hsym (mid := entry + 440#64)
    wp_steps
    apply SepWP.fold (vecU8Buf_nil_one A) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx29, hsp, hlen0, hmin0, bitvec_ult_zero, Prost.bitvec_ult_self, bitvec_sub_self_64])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hfl2 hsym2
    refine SepWPp.weaken_pre ?_ (h1b8_exit w4 w5 w6 w80 hmerge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx29, hsp, hlen0, hmin0, bitvec_ult_zero, Prost.bitvec_ult_self, bitvec_sub_self_64])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp]) hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
      (by obtain ⟨h25, h26, h27, h28, hvregs⟩ := hhigh; simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25, h26, h27, h28, hvregs, and_self])
      hfl2 hsym2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx0, hlen0, hmin0, bitvec_ult_zero, Prost.bitvec_ult_self, bitvec_sub_self_64])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx0, hlen0, hmin0, bitvec_ult_zero, Prost.bitvec_ult_self, bitvec_sub_self_64])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, bytesMutDataWord_zero])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx29]))
    exact Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, hsp]; ac_rfl)
  · set v := b0 :: v'
    have hv_len_eq : v.length = len.toNat := by rw [← hv, List.length_take_of_le hle]
    have hlen_v : len = BitVec.ofNat 64 v.length := by rw [hv_len_eq, BitVec.ofNat_toNat]; rfl
    have hle' : v.length ≤ rest0.length := by omega
    have hv_take' : rest0.take v.length = v := by rw [hv_len_eq]; exact hv
    clear hv hv_len_eq
    have hpos : 0 < v.length := List.length_pos_of_ne_nil (List.cons_ne_nil b0 v')
    have hv_len : v.length < 2 ^ 63 := by omega
    have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hmin_v : (if (BitVec.ofNat 64 v.length).ult (BitVec.ofNat 64 rest0.length) = true
        then BitVec.ofNat 64 v.length else BitVec.ofNat 64 rest0.length) = BitVec.ofNat 64 v.length := by
      by_cases hlt : v.length < rest0.length
      · have hult : (BitVec.ofNat 64 v.length).ult (BitVec.ofNat 64 rest0.length) = true := by simp [BitVec.ult, hlen_toNat, hrest0_toNat, hlt]
        simp [hult]
      · have heq : rest0.length = v.length := by omega
        simp [heq]
    have hmsb : (BitVec.ofNat 64 v.length).getLsbD 63 = false := bitvec_getLsbD_63_of_lt32 hv_len
    have hlen_ne : (BitVec.ofNat 64 v.length == 0#64) = false := by
      apply beq_false_of_ne; intro h; have h2 := congrArg BitVec.toNat h; rw [hlen_toNat] at h2; exact absurd h2 (by simp)
    apply SepWPp.bm_of_sepWP_inv hfl hsym (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x47d44))
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx29, hsp, hlen_v, hmin_v, hv_len, hmsb, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32, bitvec_getLsbD_63_of_lt32])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hfl2 hsym2
    refine SepWPp.call_frame_keep (x := ()) (T := emp) hshim hfl2 hsym2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx29, hsp, hlen_v, hmin_v, hv_len, hmsb, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32, bitvec_getLsbD_63_of_lt32])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
      (by simp [noAllocShimSpec]) trivial (by rw [emp_sepConj])
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (by intro _ _ hm; dsimp only [noAllocShimSpec] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
    intro sf_sh hpcf_sh hrunf_sh hspf_sh hcsf_sh hflf_sh hsymf_sh
    obtain ⟨h19_sh, h20_sh, h21_sh, h22_sh, h23_sh, h24_sh, h25_sh, h26_sh, h27_sh, h28_sh, h29_sh, hvregs_sh⟩ := hcsf_sh
    simp (config := { decide := true }) only [arm64_norm, hsp, hx0, hx8, hx19, hx24, hx29, hlen_v, hmin_v] at hpcf_sh hspf_sh h19_sh h20_sh h21_sh h22_sh h23_sh h24_sh h25_sh h26_sh h27_sh h28_sh h29_sh hvregs_sh
    dsimp only [noAllocShimSpec]
    refine SepWPp.pure_elim fun htr_sh => ?_
    apply SepWPp.bm_of_sepWP_inv hflf_sh hsymf_sh (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - 0x47d44))
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_sh])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_sh])
    intro hfl3 hsym3
    rw [stackAt_slice_to_alloc s0.sp]
    refine SepWPp.call_frame_keep (x := (v.length, 1)) (T := A.pool ∗ stackAt (s0.sp - 224#64) allocHookStack)
      halloc hfl3 hsym3
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_sh])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_sh])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hspf_sh, hsp_align]) rfl
      (by simp (config := { decide := true }) only [rustAllocSpec, arm64_norm, hspf_sh, h21_sh]; rfl)
      (by refine ⟨hlen_toNat, hpos, ⟨0, rfl⟩, by simp only [v, List.length_cons] at hv_len ⊢; omega⟩)
      (by sep_focus) (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (by intro _ _ hm; dsimp only [rustAllocSpec] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
    intro sf_al hpcf_al hrunf_al hspf_al hcsf_al hflf_al hsymf_al
    obtain ⟨h19_al, h20_al, h21_al, h22_al, h23_al, h24_al, h25_al, h26_al, h27_al, h28_al, h29_al, hvregs_al⟩ := hcsf_al
    simp (config := { decide := true }) only [arm64_norm, hspf_sh, h19_sh, h21_sh, h24_sh, h29_sh] at hpcf_al hspf_al h19_al h20_al h21_al h22_al h23_al h24_al h25_al h26_al h27_al h28_al h29_al hvregs_al
    simp (config := { decide := true }) only [rustAllocSpec, arm64_norm, htr_sh, htrace]
    by_cases h0 : sf_al.readReg64 .x0 = 0
    · simp only [h0, ↓reduceIte]
      refine SepWPp.weaken_pre (P' := ⌜sf_al.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
        (A.pool ∗ stackAt (s0.sp - 224#64) allocHookStack ∗
          ((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗ ((s0.sp - 152#64) ↦₆₄ w2) ∗
          ((s0.sp - 144#64) ↦₆₄ w3) ∗ ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
          ((s0.sp - 120#64) ↦₆₄ w6) ∗ memRegion (s0.sp - 112#64) 32 ∗ ((s0.sp - 80#64) ↦₆₄ w80) ∗
          memRegion (s0.sp - 72#64) 8 ∗ vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ memRegion (s0.sp - 8496#64) 4176 ∗
          memRegion (s0.sp - 224#64) 8 ∗ memRegion (s0.sp - 216#64) 48 ∗ savedRegsStack s0.sp s0))
        (Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, hspf_sh])) ?_
      refine SepWPp.pure_elim fun htr_al => ?_
      have h0_64 : sf_al.readReg64 .x0 = 0#64 := h0
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x47d44))
      wp_steps
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_al, h0_64])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_al])
      refine SepWPp.panic
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_al])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_al, h0_64, hpanic]) fun hm => ?_
      dsimp only [bytesMergeRawSpec]
      exact allowPanic_panicked (allocFailedIn_of_eq (by simp (config := { decide := true }) only [Rust.panicked, wp_norm, arm64_norm, htr_al])) hm
    · have h0_64 : sf_al.readReg64 .x0 ≠ 0#64 := h0
      have h0_beq : (sf_al.readReg64 .x0 == 0#64) = false := beq_false_of_ne h0_64
      simp only [h0, ↓reduceIte]
      refine SepWPp.weaken_pre (P' := ⌜(sf_al.readReg64 .x0).toNat % 1 = 0 ∧ sf_al.trace = s0.trace⌝ ∗
        (((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗ ((s0.sp - 152#64) ↦₆₄ w2) ∗
          ((s0.sp - 144#64) ↦₆₄ w3) ∗ ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
          ((s0.sp - 120#64) ↦₆₄ w6) ∗ memRegion (s0.sp - 112#64) 32 ∗ ((s0.sp - 80#64) ↦₆₄ w80) ∗
          memRegion (s0.sp - 72#64) 8 ∗ A.live (sf_al.readReg64 .x0) (b0 :: v').length 1 ∗
          memRegion (sf_al.readReg64 .x0) (b0 :: v').length ∗ vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
          stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗ memRegion (s0.sp - 224#64) 8 ∗
          memRegion (s0.sp - 216#64) 48 ∗ savedRegsStack s0.sp s0))
        (Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, hspf_sh]; rw [stackAt_slice_to_alloc s0.sp]; ac_rfl)) ?_
      refine SepWPp.pure_elim fun ⟨_, htr_al⟩ => ?_
      dsimp only [sliceCursorAfter]
      apply SepWPp.bm_of_sepWP_inv hflf_al hsymf_al (mid := entry + 228#64)
      wp_steps
      apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length))) ∗
          ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗ (x.ptr ↦ₛ x.bs) ⊢
          sliceCursorAfter x.slot x.ptr x.bs rest0 from Entails.refl _) (by sep_focus)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_al, h0_beq])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_al])
      intro hfl4 hsym4
      have hvar' : decodeVarint x.bs = some (BitVec.ofNat 64 (b0 :: v').length, rest0) := by rwa [← hlen_v]
      obtain ⟨h25_0, h26_0, h27_0, h28_0, hvregs_0⟩ := hhigh
      refine SepWPp.weaken_pre ?_ (h0e4_exit b0 v' (sf_al.readReg64 .x0) w0 w1 w2 w3 w4 w5 w6 w80
        hvar' hle' hv_take' h0_64
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_al, h0_beq])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_al])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf_al]) hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr_al])
        (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25_al, h26_al, h27_al, h28_al, hvregs_al, h25_sh, h26_sh, h27_sh, h28_sh, hvregs_sh, h25_0, h26_0, h27_0, h28_0, hvregs_0, and_self])
        hfl4 hsym4
        (by dsimp only [v]; simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24_al])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19_al])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24_al])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29_al]))
      exact Entails.of_eq (by ac_rfl)

/-- 4K-stack generalized verification of `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]`
(`0x47c60`) on any `libsignalSessionCode.rebase img.base H`. -/
theorem bytes_merge_3_ok_of_contracts_4k {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hdef : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" + 0x10000000000000000 - 0x47d44))
      (decodeErrorFromSpec A))
    (hmc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + bv% (ls_off% "memcpy" - 0x47d44)) framelessMemcpySpec4K)
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x47d44)) noAllocShimSpec)
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + bv% (ls_off% "__rustc::__rust_alloc" - 0x47d44)) (rustAllocSpec A))
    (hpanic : (libsignalSessionCode.rebase img.base H).externAt?
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x47d44)) = some Rust.panicked)
    (hDecodeVarint2 : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr decodeVarint2Name) ((decodeVarint2Spec A).inImage img))
    (hBytesFromVec : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesFromVecName) ((bytesFromVecSpec A img.base).inImage img))
    (hReserve7 : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr doReserve7Name) (doReserveSpec A))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (libsignalSessionCode.rebase img.base H) (bytesDropFnAddr img.base tmpPtr v.length)
        ((bytesVtableDropSpec A tmpPtr v v.length).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name) (bytesMerge3Spec A img) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp_align
  rw [bytesMerge3Spec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hfl, hsym⟩, hpre⟩ := hpre
  rw [bytesMerge3RawSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hw0, hx1, hx2, hbs_len, hcapOk⟩, hm⟩ := hpre
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hcall_dv2 : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name + 912#64) ((decodeVarint2Spec A).inImage img) := by
    rw [fnAddr_offset_eq_H (name := bytesMerge3Name) (callee := decodeVarint2Name) (k := 912#64)]; exact hDecodeVarint2
  let R48 : SepProp := memRegion (s0.sp - 8544#64) 48 ∗ R
  have herr_exit := fun {s : State} (hmerge : mergeBytes x.wt x.bs = none) => @epilogue3_err_0x07c img A H x s0 s R48 hmerge
  have hde_exit := fun (w : BitVec 64) (hw : KindNoHeap w) {s : State} (hmerge : mergeBytes x.wt x.bs = none) =>
    @epilogue3_decodeErrorFrom_0x074 img A H hdef x s0 s R48 w hw hmerge
  have h094_exit := fun (len : BitVec 64) (rest0 : List (BitVec 8)) {s : State}
      (hwt : x.wt = .lengthDelimited) (hvar : decodeVarint x.bs = some (len, rest0)) (hle : len.toNat ≤ rest0.length) =>
    @phase2_from_0x094_4k img A H himg hmc hshim halloc hpanic hBytesFromVec hReserve7
      hVtableSlot hVtableDrop x s0 s R48 len rest0 hwt hvar hle hbs_len hcapOk
  clear hDecodeVarint2 hBytesFromVec hReserve7 hVtableDrop
  refine ⟨_, R, hm, ?_⟩
  change SepWPp _ (s0.readReg64 .lr) s0 _ (MergePost3 A x s0 R) (MergePanic3 A x s0 R)
  rw [stackAt_bytesMerge3_entry s0.sp]
  refine SepWPp.weaken_pre (P' := cells (s0.sp - 64#64) 8 ∗
    (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗
      stackAt (s0.sp - 224#64) decodeVarint2Stack ∗ memRegion (s0.sp - 224#64) 8 ∗
      memRegion (s0.sp - 216#64) 48 ∗ memRegion (s0.sp - 168#64) 104)) (Entails.of_eq (by ac_rfl)) ?_
  refine SepWPp.unfold_cells_64 fun c0 c1 c2 c3 c4 c5 c6 c7 => ?_
  merge3_fetches_H img.base H bytesMerge3_fnOff 0 116
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMerge3Name = entry
  examples_hide_fetches
  by_cases hwt : x.wt = .lengthDelimited
  · have hw0_br : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      change (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x0)) &&& 255#64) != 2#32) = false
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, hw0, hwt]; decide
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
      (T := (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗ stackAt (s0.sp - 224#64) decodeVarint2Stack)
      hcall_dv2 hfl1 hsym1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp_align]) rfl
      (by simp (config := { decide := true }) only [decodeVarint2Spec, arm64_norm]) hbs_len (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sf _ hm => by
        simp only [bytesMerge3RawSpec, Spec.inImage, decodeVarint2Spec, State.trace_setPC, State.trace_writeReg64, allocFailedIn] at hm ⊢
        exact allowPanic_frame id hm) ?_
    intro sf_dv hpcf hrunf hspf hcsf hflf hsymf
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f, hvregsf⟩ := hcsf
    simp (config := { decide := true }) only [arm64_norm, hx1, hx2] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f hvregsf
    simp (config := { decide := true }) only [decodeVarint2Spec, wp_norm, arm64_norm]
    rw [stackAt_varint2_to_slice s0.sp]
    rcases hvar : decodeVarint x.bs with _ | ⟨len, rest0⟩
    · dsimp only
      have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_of_decodeVarint_none hvar
      refine SepWPp.weaken_pre (P' := ⌜sf_dv.readReg64 .x0 = 1#64⌝ ∗ ⌜sf_dv.trace = s0.trace⌝ ∗ ⌜sf_dv.readReg64 .x1 ≠ 0#64⌝ ∗
        (memRegion (s0.sp - 8544#64) 48 ∗ decodeErrorAtStackLen A (sf_dv.readReg64 .x1) 0 ∗
          vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗ (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
          stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗ memRegion (s0.sp - 224#64) 8 ∗
          memRegion (s0.sp - 216#64) 48 ∗ memRegion (s0.sp - 168#64) 104 ∗ savedRegsStack s0.sp s0))
        (Entails.of_eq (by dsimp only [savedRegsStack, Reg.x0, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x29, Reg.x30]; ac_rfl)) ?_
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
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf]) hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm]; exact hx1_sf)
        (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, and_self]))
    · dsimp only
      obtain ⟨pfx, hpfx⟩ := bm_decodeVarint_suffix hvar
      have hrest0_len : rest0.length ≤ x.bs.length := by rw [hpfx, List.length_append]; omega
      have hrest0_toNat : (BitVec.ofNat 64 rest0.length).toNat = rest0.length := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine SepWPp.weaken_pre (P' := ⌜sf_dv.readReg64 .x0 = 0#64 ∧ sf_dv.readReg64 .x1 = len⌝ ∗ ⌜sf_dv.trace = s0.trace⌝ ∗
        (memRegion (s0.sp - 8544#64) 48 ∗ vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
          stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗ memRegion (s0.sp - 224#64) 8 ∗
          memRegion (s0.sp - 216#64) 48 ∗ memRegion (s0.sp - 168#64) 104 ∗ savedRegsStack s0.sp s0))
        (Entails.of_eq (by dsimp only [savedRegsStack, Reg.x0, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x29, Reg.x30]; ac_rfl)) ?_
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
          (memRegion (s0.sp - 8544#64) 48 ∗ vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
            (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
            stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗ memRegion (s0.sp - 224#64) 8 ∗
            memRegion (s0.sp - 168#64) 104 ∗ savedRegsStack s0.sp s0)) (Entails.of_eq (by ac_rfl)) ?_
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
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf]) hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, and_self])))
        exact Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm]; ac_rfl)
      · have hule_eq : len.ule (BitVec.ofNat 64 rest0.length) = true := Bool.eq_true_of_not_eq_false hule
        simp only [hule_eq, ↓reduceIte] at hfl2 hsym2 ⊢
        have hle : len.toNat ≤ rest0.length := by simpa [BitVec.ule, hrest0_toNat] using hule_eq
        refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3 (h094_exit len rest0 hwt hvar hle
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule_eq])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf]) hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, and_self])
          hfl2 hsym2
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1_sf])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29f])))
        exact Entails.of_eq (by ac_rfl)
  · have hw0_br : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      change (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x0)) &&& 255#64) != 2#32) = true
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, hw0]; cases hxwt : x.wt <;> simp_all [WireType.toNat]
    have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_ne_lengthDelimited hwt
    dsimp only [sliceCursorAt]; rw [stackAt_varint2_to_slice s0.sp]
    refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 216#64) 48 ∗
      (memRegion (s0.sp - 8544#64) 48 ∗ ((s0.sp - 64#64) ↦₆₄ c0) ∗ ((s0.sp - 56#64) ↦₆₄ c1) ∗
        ((s0.sp - 48#64) ↦₆₄ c2) ∗ ((s0.sp - 40#64) ↦₆₄ c3) ∗ ((s0.sp - 32#64) ↦₆₄ c4) ∗
        ((s0.sp - 24#64) ↦₆₄ c5) ∗ ((s0.sp - 16#64) ↦₆₄ c6) ∗ ((s0.sp - 8#64) ↦₆₄ c7) ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗ (x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗
        ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗ memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104)) (Entails.of_eq (by ac_rfl)) ?_
    refine SepWPp.unfold_memRegion_216_invalidWireType fun w0_216 b0_216 b1_216 => ?_
    apply SepWPp.bm_of_sepWP_inv hfl hsym (mid := entry + 116#64)
    wp_steps
    apply SepWP.fold (fold_memRegion_40_bytes (s0.sp - 216#64) (BitVec.ofNat 8 x.wt.toNat) 2#8) (by sep_focus)
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

/-- `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]` meets `bytesMerge3Spec A img` on `tripleRatchetProgAtExt img.base ext` under `AllocContracts4K img.base A ext`. -/
theorem bytes_merge_3_ok_ext_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hAlloc : AllocContracts4K img.base A ext)
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
  exact bytes_merge_3_ok_of_contracts_4k himg hdef
    (framelessMemcpy4K_of_sessionMemcpyRegion
      (hAlloc.session_memcpy_region_ok_at bytesMerge3Name (num% (ls_off% "memcpy" - 0x47d44))))
    (hAlloc.shim_ok_at bytesMerge3Name (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x47d44)))
    (hAlloc.alloc_ok_at bytesMerge3Name (num% (ls_off% "__rustc::__rust_alloc" - 0x47d44)))
    (panic_at_handle_error_ext img.base ext bytesMerge3Name (num% (ls_off% "alloc::raw_vec::handle_error" - 0x47d44)))
    hDecodeVarint2 hBytesFromVec hReserve7 hVtableSlot hVtableDrop

/-- `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]` meets `bytesMerge3ProtoSpec A img` on `tripleRatchetProgAtExt img.base ext` under `AllocContracts4K img.base A ext`. -/
theorem bytes_merge_3_proto_ok_ext_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hAlloc : AllocContracts4K img.base A ext)
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
  have hok := bytes_merge_3_ok_ext_4k himg hAlloc hDecodeErrorFrom hDecodeVarint2
    hBytesFromVec hReserve7 hVtableSlot hVtableDrop
  unfold BytesMerge3ProtoOkExt
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (bytesMerge3Spec A img).pre x.toCodec s0 ∗ R := by
    simpa only [bytesMerge3ProtoSpec, bytesMerge3Spec, Spec.inImage,
      bytesMerge3ProtoRawSpec, bytesMerge3RawSpec, BytesMergeProtoGhost.toCodec,
      protoWireTypeToCodec_toNat] using hpre
  refine (hok.to_outcome x.toCodec R s0 hpc hrun hpre' hal).mono_outcome ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [bytesMerge3ProtoSpec, bytesMerge3Spec, Spec.inImage,
      bytesMerge3ProtoRawSpec, bytesMerge3RawSpec, BytesMergeProtoGhost.toCodec] at hpost ⊢
    rw [proto_mergeBytes_toOption]
    exact hpost
  · exact Or.inr hfail

end CryptoVerification.SpqrV1.Prost.BytesMerge
