/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsX
public import LibsignalBinary.Proofs.E2E.Bin.SpecsCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.Canon

@[expose] public section

set_option autoImplicit false

/-!
# Bridge from `serializeSpecX` to `recordSerializeSpec`

Connects the internal `SessionRecord::serialize` body contract (`serializeSpecX A`) for an arbitrary
`A : RustAlloc` to `serializeCanonSpecX A` and `Bin.recordSerializeSpec A` on `SP2Ext` and under
relocatable `[LibsignalPlacement]` (Block `52`), framing the remaining stack slack and 16-byte
result-buffer tail under `CanonRecord`.
-/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Bin

theorem L1_RecordSerializeExt : True := trivial

theorem canonRecord_to_serializationCanonX {g : CryptoVerification.E2E.Bin.RecordGhost}
    {r : CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8))}
    (h : CryptoVerification.E2E.Bin.CanonRecord g r) :
    CryptoVerification.E2E.Record.Serialization.CanonRecord g r := by
  rcases g with ⟨_, _, _ | G⟩ <;> rcases r with ⟨_ | s⟩
  · exact True.intro
  · contradiction
  · contradiction
  · exact h.toCanonSession

private theorem stackAt_sub_split (sp : BitVec 64) (k m : Nat) (hkm : k ≤ m)
    (hm : m ≤ 2 ^ 64) :
    stackAt sp m =
      memRegion (sp - BitVec.ofNat 64 m) (m - k) ∗ stackAt sp k := by
  unfold stackAt
  have hsplit := memRegion_split' (b := sp - BitVec.ofNat 64 m) (b' := sp - BitVec.ofNat 64 k)
    (N := m) (n := m - k) (k := k) (by omega)
    (by
      have h1 : BitVec.ofNat 64 m = BitVec.ofNat 64 (m - k) + BitVec.ofNat 64 k := by
        rw [← BitVec.ofNat_add, Nat.sub_add_cancel hkm]
      rw [h1]
      bv_lin)
    (by omega)
  exact hsplit

private theorem stackAt_recordSerialize_split (sp : BitVec 64) :
    stackAt sp CryptoVerification.E2E.Bin.recordSerializeStack =
      memRegion (sp - BitVec.ofNat 64 CryptoVerification.E2E.Bin.recordSerializeStack)
        (CryptoVerification.E2E.Bin.recordSerializeStack - serializeStackX) ∗
      stackAt sp serializeStackX :=
  stackAt_sub_split sp serializeStackX CryptoVerification.E2E.Bin.recordSerializeStack
    serializeStackX_le_recordSerializeStack (by decide)

private theorem memRegion_48_split_32_16 (out : BitVec 64) :
    memRegion out 48 = memRegion out 32 ∗ memRegion (out + 32#64) 16 :=
  memRegion_split out 32 16 (by decide)

/-- Lifts `serializeSpecX A` to `serializeCanonSpecX A` under `CanonRecord`. -/
theorem serializeCanonX_of_serializeX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr CryptoVerification.E2E.Record.Serialization.serializeName)
      ((serializeSpecX A).inImage img)) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr CryptoVerification.E2E.Record.Serialization.serializeName)
      ((serializeCanonSpecX A).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hp hsp_align => ?_
  have hp' := hp
  simp only [Spec.inImage, serializeCanonSpecX] at hp'
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp'
  obtain ⟨⟨hF, hsym⟩, hp'⟩ := hp'
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp'
  obtain ⟨⟨h0, h8, hcanon, hlen⟩, hrest⟩ := hp'
  have henc := encRecordMem_eq_of_canon x.g x.r hcanon
  have hpre : s0.mem ⊨ ((serializeSpecX A).inImage img).pre x s0 ∗ R := by
    simp only [Spec.inImage, serializeSpecX]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hF, hsym⟩, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨h0, h8, henc ▸ hlen⟩, hrest⟩
  refine h.mono_outcome x R s0 hpc hrun hpre hsp_align fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, serializeSpecX] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq_mem⟩
    dsimp only [Spec.inImage, serializeCanonSpecX]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    simpa only [henc] using hq_mem
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, serializeSpecX, serializeCanonSpecX] at hq ⊢
    exact hq
  · refine Or.inr (Or.inr (Or.inl ⟨code, hex, ?_⟩))
    dsimp only [Spec.inImage, serializeSpecX, serializeCanonSpecX] at hq ⊢
    exact hq
  · refine Or.inr (Or.inr (Or.inr ⟨hoom, ?_⟩))
    dsimp only [Spec.inImage, serializeSpecX, serializeCanonSpecX] at hq ⊢
    exact hq

/-- Lifts `serializeSpecX A` to `(Bin.recordSerializeSpec A).inImage img` on `SP2Ext`. -/
theorem recordSerialize_ok_ext_of_serializeX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr CryptoVerification.E2E.Record.Serialization.serializeName)
      ((serializeSpecX A).inImage img)) :
    subroutine_ok (CryptoVerification.LibsignalTripleRatchet.contractProg img.base ext)
      (img.base + CryptoVerification.E2E.Bin.serializeOff)
      ((CryptoVerification.E2E.Bin.recordSerializeSpec A).inImage img) := by
  have hser := serializeCanonX_of_serializeX h
  have hAddr :
      (SP2Ext img.base ext).fnAddr CryptoVerification.E2E.Record.Serialization.serializeName =
        img.base + CryptoVerification.E2E.Bin.serializeOff := by
    change (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
        CryptoVerification.E2E.Bin.recordSerializeName =
      img.base + CryptoVerification.E2E.Bin.serializeOff
    rw [Program.fnAddr_rebase, CryptoVerification.E2E.Bin.serialize_fnOff]
  rw [SP2Ext_eq_contractProg, hAddr] at hser
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' := hpre
  dsimp only [Spec.inImage, recordSerializeSpec] at hpre'
  rw [memRegion_48_split_32_16 x.out, stackAt_recordSerialize_split s0.sp,
      sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hF, hsym⟩, hpre'⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx8, hcanon, hlen⟩, hmem⟩
  have hcanon_serialize : CryptoVerification.E2E.Record.Serialization.CanonRecord x.g x.r :=
    canonRecord_to_serializationCanonX hcanon
  let x_serialize : CryptoVerification.E2E.Record.Serialization.SerializeGhost := ⟨x.self, x.out, x.g, x.r⟩
  let R_serialize : SepProp :=
    (memRegion (x.out + 32#64) 16 ∗
     memRegion (s0.sp - BitVec.ofNat 64 CryptoVerification.E2E.Bin.recordSerializeStack)
       (CryptoVerification.E2E.Bin.recordSerializeStack - serializeStackX) ∗ R)
  have hpre_serialize : s0.mem ⊨ ((serializeCanonSpecX A).inImage img).pre x_serialize s0 ∗ R_serialize := by
    dsimp only [Spec.inImage, serializeCanonSpecX, x_serialize, R_serialize]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hF, hsym⟩, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hcanon_serialize, hlen⟩, ?_⟩
    convert hmem using 1; ac_rfl
  refine hser.mono_outcome x_serialize R_serialize s0 hpc hrun hpre_serialize hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, serializeCanonSpecX, x_serialize, R_serialize] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq_mem⟩
    dsimp only [Spec.inImage, recordSerializeSpec]
    rw [stackAt_recordSerialize_split s0.sp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    convert hq_mem using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, serializeCanonSpecX, CryptoVerification.E2E.Record.Serialization.allocPanic,
      recordSerializeSpec, R_serialize] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hfail, hq_mem⟩
    refine ⟨hfail, ?_⟩
    have hany : (anyHeap ∗ memRegion (x.out + 32#64) 16 ∗
        memRegion (s0.sp - BitVec.ofNat 64 CryptoVerification.E2E.Bin.recordSerializeStack)
          (CryptoVerification.E2E.Bin.recordSerializeStack - serializeStackX)) ∗ R ⊢ anyHeap ∗ R :=
      sepConj_mono_left (entails_anyHeap _)
    refine Satisfies.mono hany ?_
    convert hq_mem using 1; ac_rfl
  · dsimp only [Spec.inImage, serializeCanonSpecX] at hq
    rw [satisfies_pure_sepConj] at hq
    exact hq.1.elim
  · dsimp only [Spec.inImage, serializeCanonSpecX] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem serializeCanonX_trProgExt_of_serializeX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr CryptoVerification.E2E.Record.Serialization.serializeName)
      ((serializeSpecX A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.E2E.Record.Serialization.serializeName)
      ((serializeCanonSpecX A).inImage img) :=
  serializeCanonX_of_serializeX h

theorem recordSerialize_trProgExt_of_serializeX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr CryptoVerification.E2E.Record.Serialization.serializeName)
      ((serializeSpecX A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (img.base + CryptoVerification.E2E.Bin.serializeOff)
      ((CryptoVerification.E2E.Bin.recordSerializeSpec A).inImage img) :=
  recordSerialize_ok_ext_of_serializeX h

theorem recordSerialize_fnAddr_trProgExt_of_serializeX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr CryptoVerification.E2E.Record.Serialization.serializeName)
      ((serializeSpecX A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.E2E.Bin.recordSerializeName)
      ((CryptoVerification.E2E.Bin.recordSerializeSpec A).inImage img) := by
  have hAddr :
      (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.E2E.Bin.recordSerializeName =
        img.base + CryptoVerification.E2E.Bin.serializeOff := by
    change (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
        CryptoVerification.E2E.Bin.recordSerializeName =
      img.base + CryptoVerification.E2E.Bin.serializeOff
    rw [Program.fnAddr_rebase, CryptoVerification.E2E.Bin.serialize_fnOff]
  rw [hAddr]
  exact recordSerialize_ok_ext_of_serializeX h

/-! ## Relocatable `[LibsignalPlacement]` bridge (Block `52`) -/

section Placed

open Arm64.Obj CryptoVerification.E2E.Record.Placed

theorem L1_RecordSerializeExt_Placed : True := trivial

private theorem pack_withLsCodeLoaded_rse {pl : MultiPlacement} {α : Type} {S : Spec α}
    {x : α} {s0 : State} {R : SepProp}
    (hcl : LibsignalCodeLoaded pl s0.mem)
    (hp : s0.mem ⊨ S.pre x s0 ∗ R) :
    s0.mem ⊨ (withLsCodeLoaded pl S).pre x s0 ∗ R := by
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm _ ⌜LibsignalCodeLoaded pl s0.mem⌝, satisfies_pure_sepConj]
  exact ⟨hcl, hp⟩

/-- Relocatable `withLsCodeLoaded` bridge from `serializeSpecX A` to `serializeCanonSpecX A`. -/
theorem serializeCanonX_of_serialize_placedX {pl : MultiPlacement} {A : RustAlloc}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl (serializeSpecX A))) :
    subroutine_ok prog entry (withLsCodeLoaded pl (serializeCanonSpecX A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hp hsp_align => ?_
  obtain ⟨hcl, hp'⟩ := extract_withLsCodeLoaded hp
  simp only [serializeCanonSpecX] at hp'
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp'
  obtain ⟨⟨h0, h8, hcanon, hlen⟩, hrest⟩ := hp'
  have henc := encRecordMem_eq_of_canon x.g x.r hcanon
  have hpre : s0.mem ⊨ (withLsCodeLoaded pl (serializeSpecX A)).pre x s0 ∗ R := by
    refine pack_withLsCodeLoaded_rse hcl ?_
    simp only [serializeSpecX]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨h0, h8, henc ▸ hlen⟩, hrest⟩
  refine h.mono_outcome x R s0 hpc hrun hpre hsp_align fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, serializeSpecX] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq_mem⟩
    dsimp only [withLsCodeLoaded, serializeCanonSpecX]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    simpa only [henc] using hq_mem
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

/-- Relocatable `withLsCodeLoaded` bridge from `serializeSpecX A` to `Bin.recordSerializeSpec A`. -/
theorem recordSerialize_placed_ok_ext_of_serializeX {pl : MultiPlacement} {A : RustAlloc}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl (serializeSpecX A))) :
    subroutine_ok prog entry
      (withLsCodeLoaded pl (CryptoVerification.E2E.Bin.recordSerializeSpec A)) := by
  have hser := serializeCanonX_of_serialize_placedX h
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  obtain ⟨hcl, hpre'⟩ := extract_withLsCodeLoaded hpre
  dsimp only [recordSerializeSpec] at hpre'
  rw [memRegion_48_split_32_16 x.out, stackAt_recordSerialize_split s0.sp,
      sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx8, hcanon, hlen⟩, hmem⟩
  have hcanon_serialize : CryptoVerification.E2E.Record.Serialization.CanonRecord x.g x.r :=
    canonRecord_to_serializationCanonX hcanon
  let x_serialize : CryptoVerification.E2E.Record.Serialization.SerializeGhost := ⟨x.self, x.out, x.g, x.r⟩
  let R_serialize : SepProp :=
    (memRegion (x.out + 32#64) 16 ∗
     memRegion (s0.sp - BitVec.ofNat 64 CryptoVerification.E2E.Bin.recordSerializeStack)
       (CryptoVerification.E2E.Bin.recordSerializeStack - serializeStackX) ∗ R)
  have hpre_serialize : s0.mem ⊨ (withLsCodeLoaded pl (serializeCanonSpecX A)).pre x_serialize s0 ∗ R_serialize := by
    refine pack_withLsCodeLoaded_rse hcl ?_
    dsimp only [serializeCanonSpecX, x_serialize, R_serialize]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hcanon_serialize, hlen⟩, ?_⟩
    convert hmem using 1; ac_rfl
  refine hser.mono_outcome x_serialize R_serialize s0 hpc hrun hpre_serialize hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, serializeCanonSpecX, x_serialize, R_serialize] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq_mem⟩
    dsimp only [withLsCodeLoaded, recordSerializeSpec]
    rw [stackAt_recordSerialize_split s0.sp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    convert hq_mem using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withLsCodeLoaded, serializeCanonSpecX, CryptoVerification.E2E.Record.Serialization.allocPanic,
      recordSerializeSpec, R_serialize] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hfail, hq_mem⟩
    refine ⟨hfail, ?_⟩
    have hany : (anyHeap ∗ memRegion (x.out + 32#64) 16 ∗
        memRegion (s0.sp - BitVec.ofNat 64 CryptoVerification.E2E.Bin.recordSerializeStack)
          (CryptoVerification.E2E.Bin.recordSerializeStack - serializeStackX)) ∗ R ⊢ anyHeap ∗ R :=
      sepConj_mono_left (entails_anyHeap _)
    refine Satisfies.mono hany ?_
    convert hq_mem using 1; ac_rfl
  · dsimp only [withLsCodeLoaded, serializeCanonSpecX] at hq
    rw [satisfies_pure_sepConj] at hq
    exact hq.1.elim
  · dsimp only [withLsCodeLoaded, serializeCanonSpecX] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem recordSerialize_placed_cl_of_serializeX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h : subroutine_ok (lsProg_52 H) (blkPl_52).base (withLsCodeLoaded lsmpl (serializeSpecX A))) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (CryptoVerification.E2E.Bin.recordSerializeSpec A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (recordSerialize_placed_ok_ext_of_serializeX h)

end Placed

end Proofs.libsignal.Hooks2
