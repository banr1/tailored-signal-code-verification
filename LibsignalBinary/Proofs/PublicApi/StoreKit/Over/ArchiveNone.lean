/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchivePendPlaced
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Fetch
import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.HeapDefs
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyNoneX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodySomeX
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# Tail and Top-Level Proofs of `archive_current_state_inner`

Proves the post-`encode_raw` tails (`prevCap = 0#64` via `RawVec<Vec<u8>>::grow_one` and
`prevCap ≠ 0#64` via in-place slot-`0` write) and assembles `archive_over_okX` and
`archive_over_gen_ok` across arbitrary `pending_pre_key` and `pending_kyber_pre_key` states, along
with relocatable `[LibsignalPlacement]` counterparts on Block `51`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.CodeLayout CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX
open CryptoVerification.LibsignalSpqrV1 (growOneVecU8Spec)
open Proofs.libsignal.Hooks2

set_option maxRecDepth 2000000
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Stack and Buffer Packing Helpers -/

theorem prev1_of_partsX (A : RustAlloc) (q : BitVec 64) (enc : List (BitVec 8)) (hq : q ≠ 0#64) :
    (A.live q 96 8 ∗ vecU8 A q enc ∗ memRegion (q + 24#64) 72) ⊢ Prev1 A q enc := by
  rw [prev1_eq]
  exact Entails.pure_right ⟨by decide, by decide, hq⟩ (Entails.refl _)

theorem hdrP_of_cellsX (r cap ptr len : BitVec 64) :
    ((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ ptr) ∗ ((r + 16#64) ↦₆₄ len)) ⊢ HdrP r cap ptr len :=
  Entails.of_eq (hdrP_eq r cap ptr len).symm

theorem hdrP_prev1_of_raw_cellsX (A : RustAlloc) (recPtr q cap ptr : BitVec 64)
    (enc : List (BitVec 8)) (hq : q ≠ 0) :
    ((recPtr ↦₆₄ 4#64) ∗ ((recPtr + 8#64) ↦₆₄ q) ∗ ((recPtr + 16#64) ↦₆₄ 1#64) ∗
      A.live q 96 8 ∗
      (q ↦₆₄ cap) ∗ ((q + 8#64) ↦₆₄ ptr) ∗ ((q + 16#64) ↦₆₄ BitVec.ofNat 64 enc.length) ∗
      RustHeap.vecU8Buf A cap ptr enc ∗ memRegion (q + 24#64) 72) ⊢
      HdrP recPtr 4#64 q 1#64 ∗ Prev1 A q enc := by
  have hhdr := hdrP_of_cellsX recPtr 4#64 q 1#64
  have hvec := vecU8_from_cellsX A q cap ptr enc
  have hprev := prev1_of_partsX A q enc hq
  have hgroup :
      ((recPtr ↦₆₄ 4#64) ∗ ((recPtr + 8#64) ↦₆₄ q) ∗ ((recPtr + 16#64) ↦₆₄ 1#64) ∗
        A.live q 96 8 ∗
        (q ↦₆₄ cap) ∗ ((q + 8#64) ↦₆₄ ptr) ∗ ((q + 16#64) ↦₆₄ BitVec.ofNat 64 enc.length) ∗
        RustHeap.vecU8Buf A cap ptr enc ∗ memRegion (q + 24#64) 72) =
      ((recPtr ↦₆₄ 4#64) ∗ ((recPtr + 8#64) ↦₆₄ q) ∗ ((recPtr + 16#64) ↦₆₄ 1#64)) ∗
        (A.live q 96 8 ∗
          ((q ↦₆₄ cap) ∗ ((q + 8#64) ↦₆₄ ptr) ∗ ((q + 16#64) ↦₆₄ BitVec.ofNat 64 enc.length) ∗
            RustHeap.vecU8Buf A cap ptr enc) ∗
          memRegion (q + 24#64) 72) := by
    ac_rfl
  rw [hgroup]
  exact sepConj_mono hhdr
    (Entails.trans (sepConj_mono_right (sepConj_mono_left hvec)) hprev)

theorem memRegion_prev96_cellsX (q : BitVec 64) :
    memRegion q 96 =
      (∃∗ a : BitVec 64, q ↦₆₄ a) ∗ (∃∗ b : BitVec 64, (q + 8#64) ↦₆₄ b) ∗
        (∃∗ c : BitVec 64, (q + 16#64) ↦₆₄ c) ∗ memRegion (q + 24#64) 72 := by
  rw [show (96 : Nat) = 8 + (8 + (8 + 72)) by rfl, memRegion_split q 8 _ (by decide),
    memRegion_split _ 8 _ (by decide), memRegion_split _ 8 72 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  have e1 : q + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = q + 16#64 := by
    rw [BitVec.add_assoc]; rfl
  have e2 : q + 16#64 + BitVec.ofNat 64 8 = q + 24#64 := by
    rw [BitVec.add_assoc]; rfl
  rw [e1, e2]

theorem stackAt_archive_unpackX (sp : BitVec 64) :
    stackAt sp archiveStackX =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
       ∃∗ v112 : BitVec 128, ∃∗ v456 : BitVec 64, ∃∗ v464 : BitVec 64,
        stackAt (sp - 464#64) serializeSubStackX ∗
        ((sp - 464#64) ↦₆₄ v464) ∗ ((sp - 456#64) ↦₆₄ v456) ∗
        memRegion (sp - 448#64) 336 ∗ ((sp - 112#64) ↦₁₂₈ v112) ∗
        ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗
        ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
        ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗
        ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
        ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗
        ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) := by
  rw [stackAt_archive_preX sp, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_sixteen]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem stackAt_archive_pack_344X
    (sp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v464 lo112 hi112 : BitVec 64) :
    (stackAt (sp - 464#64) serializeSubStackX ∗
      ((sp - 464#64) ↦₆₄ v464) ∗
      memRegion (sp - 456#64) 344 ∗
      ((sp - 112#64) ↦₆₄ lo112) ∗ ((sp - 104#64) ↦₆₄ hi112) ∗
      ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗
      ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
      ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗
      ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
      ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗
      ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) ⊢
      stackAt sp archiveStackX := by
  rw [stackAt_archive_preX sp]
  refine Entails.sepExists_right c0 (Entails.sepExists_right c1 (Entails.sepExists_right c2
    (Entails.sepExists_right c3 (Entails.sepExists_right c4 (Entails.sepExists_right c5
    (Entails.sepExists_right c6 (Entails.sepExists_right c7 (Entails.sepExists_right c8
    (Entails.sepExists_right c9 (Entails.sepExists_right c10 (Entails.sepExists_right c11 ?_)))))))))))
  have h344 : memRegion (sp - 456#64) 344 =
      memRegion (sp - 456#64) 8 ∗ memRegion (sp - 448#64) 336 := by
    rw [show (344 : Nat) = 8 + 336 by rfl, memRegion_split _ 8 336 (by decide),
      bv_sub_add_lit sp 456 8]
  have h464 : ((sp - 464#64) ↦₆₄ v464) ⊢ memRegion (sp - 464#64) 8 :=
    pointsTo64_entails_memRegion _ _
  have h112 : (((sp - 112#64) ↦₆₄ lo112) ∗ ((sp - 104#64) ↦₆₄ hi112)) ⊢
      memRegion (sp - 112#64) 16 := by
    refine Entails.trans (cell112_packX sp lo112 hi112) ?_
    rw [ProofLib.memRegion_sixteen]
    exact Entails.sepExists_right _ (Entails.refl _)
  rw [h344]
  have hgroup :
      stackAt (sp - 464#64) serializeSubStackX ∗
        ((sp - 464#64) ↦₆₄ v464) ∗
        (memRegion (sp - 456#64) 8 ∗ memRegion (sp - 448#64) 336) ∗
        ((sp - 112#64) ↦₆₄ lo112) ∗ ((sp - 104#64) ↦₆₄ hi112) ∗
        ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗
        ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
        ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗
        ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
        ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗
        ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11) =
      ((sp - 464#64) ↦₆₄ v464) ∗
        (((sp - 112#64) ↦₆₄ lo112) ∗ ((sp - 104#64) ↦₆₄ hi112)) ∗
        (stackAt (sp - 464#64) serializeSubStackX ∗
          memRegion (sp - 456#64) 8 ∗ memRegion (sp - 448#64) 336 ∗
          ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗
          ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
          ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗
          ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
          ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗
          ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) := by
    ac_rfl
  rw [hgroup]
  refine Entails.trans (sepConj_mono h464 (sepConj_mono_left h112)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem hdrP_prev1_entails_gen (A : RustAlloc) (recPtr q : BitVec 64) (enc : List (BitVec 8)) :
    (HdrP recPtr 4#64 q 1#64 ∗ Prev1 A q enc) ⊢
      ∃∗ prevCap' : BitVec 64, ∃∗ prevPtr' : BitVec 64,
        ⌜prevCap' ≠ 0#64⌝ ∗ prevVecAt A recPtr prevCap' prevPtr' [enc] := by
  rw [hdrP_prev1_eq A recPtr q enc]
  exact Entails.sepExists_right 4#64
    (Entails.sepExists_right q (Entails.pure_right (by decide) (Entails.refl _)))

/-! ## Zero-Capacity Tail (`prevCap = 0#64`) -/

set_option maxHeartbeats 800000 in
theorem archive_tail_zero_cap_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext)
    (hDrop : DropSessionStructureLocal1OkX img A ext)
    (recPtr prevPtr : BitVec 64)
    (hprev_ne : prevPtr ≠ 0#64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (bs336 : List (BitVec 8)) (hbs336 : bs336.length = 336)
    (capEnc ptrEnc c0 v464 : BitVec 64) (v112 : BitVec 128)
    (R : SepProp) (s0 s3 : State)
    (hsp_align : s0.spAligned = true)
    (hpc3 : s3.pc = (SP2Ext img.base ext).fnAddr archiveCurrentStateInnerName + (archiveEncodeRawCutOff + 4#64))
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 464#64)
    (htr3 : s3.trace = s0.trace)
    (hx19 : s3.readReg64 .x19 = recPtr)
    (_hx20 : s3.readReg64 .x20 = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length)
    (hx21 : s3.readReg64 .x21 = s0.sp - 112#64)
    (hx23 : s3.readReg64 .x23 = 0#64)
    (hx24 : s3.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s3.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s3.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s3.readReg64 .x27 = s0.readReg64 .x27)
    (_hx28 : s3.readReg64 .x28 = s0.readReg64 .x28)
    (hx29 : s3.readReg64 .x29 = s0.sp - 64#64)
    (hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 .lr) s3
      (archiveMidRawPre A s0 recPtr 0#64 prevPtr G sess bs336 capEnc ptrEnc c0 v464 v112 emp)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (archiveOverSpecX A).post ⟨recPtr, prevPtr, G, sess⟩ s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (archiveQp s0 R) := by
  have hfn : libsignalSessionCode.fnOff archiveCurrentStateInnerName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner") :=
    libsignalSessionCode_fnOff_archive
  have hgrow := growOne_arch_okX (img := img) hA
  have hdrop := dropLocal1_arch_okX hDrop
  code_fetches_from CryptoVerification.libsignalSessionCode
    archiveBin img.base (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
    0x110 0x38
  code_fetches_from CryptoVerification.libsignalSessionCode
    archiveBin img.base (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
    0x15c 0x40
  revert hpc3
  have hpc_anchor :
      ({ s0 with pc := (SP2Ext img.base ext).fnAddr archiveCurrentStateInnerName } : State).pc =
        (SP2Ext img.base ext).fnAddr archiveCurrentStateInnerName := rfl
  examples_generalize_entry
  clear hpc_anchor
  intro hpc3
  simp only [archiveEncodeRawCutOff, arm64_norm] at hpc3
  examples_hide_fetches
  unfold archiveMidRawPre
  conv => arg 5; simp only [sepConj_emp]
  apply SepWPpIn.of_sepWP
    (mid := entry +
      bv% (ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one" -
        ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
  rw [vecU8At_unpack_88X]
  refine SepWP.fold (cell112_splitX s0.sp _) (by sep_focus) ?_
  apply sepWP_exists_left_sepX; intro lo112
  conv => arg 4; simp only [sepExists_sepConj_left]
  apply SepWP.exists_left; intro hi112
  conv => arg 4; simp only [sepConj_assoc]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  have hprev_ne0 : prevPtr ≠ 0 := hprev_ne
  wppin_callc hgrow ((growOneSubSpecX A).inImage img) ⟨recPtr, 0#64, prevPtr, []⟩
  apply SepWPpIn.of_sepWP
    (mid := entry +
      bv% (2 ^ 64 +
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") -
        (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner")))
  rw [memRegion_prev96_cellsX, newCapVecU8_zeroX]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro sc0
  apply SepWP.exists_left; intro sc8
  apply SepWP.exists_left; intro sc16
  wp_steps
  refine SepWP.fold
    (sessionAt_entails_sessionStateAt A (s0.sp - 456#64) (clearPendingGhost G) (clearPending sess))
    (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  wppin_callc hdrop ((dropLocal1SubSpecX A).inImage img)
    ⟨s0.sp - 456#64, clearPendingGhost G, (clearPending sess).state⟩
  apply SepWPpIn.of_sepWP_ret
  wp_steps
  refine SepWP.fold
    (hdrP_prev1_of_raw_cellsX A recPtr _ _ _
      (encSessionMem (clearPendingGhost G) (clearPending sess)) (by assumption))
    (by sep_focus) ?_
  have h32 : ((recPtr + 32#64) ↦ₛ bs336) ⊢ memRegion (recPtr + 0x20#64) 336 := by
    rw [← hbs336]; exact pointsToBytes_entails_memRegion _ _
  refine SepWP.fold h32 (by sep_focus) ?_
  refine SepWP.fold
    (stackAt_archive_pack_344X s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (by sep_focus) ?_
  wp_done

/-! ## Nonzero-Capacity Tail (`prevCap ≠ 0#64`) -/

set_option maxHeartbeats 800000 in
theorem archive_tail_nonzero_cap_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hDrop : DropSessionStructureLocal1OkX img A ext)
    (recPtr prevCap prevPtr : BitVec 64)
    (hcap : prevCap ≠ 0#64)
    (hbound : prevCap.toNat * 24 < 2 ^ 63)
    (hprev_ne : prevPtr ≠ 0#64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (bs336 : List (BitVec 8)) (hbs336 : bs336.length = 336)
    (capEnc ptrEnc c0 v464 : BitVec 64) (v112 : BitVec 128)
    (R : SepProp) (s0 s3 : State)
    (hsp_align : s0.spAligned = true)
    (hpc3 : s3.pc = (SP2Ext img.base ext).fnAddr archiveCurrentStateInnerName + (archiveEncodeRawCutOff + 4#64))
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 464#64)
    (htr3 : s3.trace = s0.trace)
    (hx19 : s3.readReg64 .x19 = recPtr)
    (_hx20 : s3.readReg64 .x20 = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length)
    (hx21 : s3.readReg64 .x21 = s0.sp - 112#64)
    (hx23 : s3.readReg64 .x23 = 0#64)
    (hx24 : s3.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s3.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s3.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s3.readReg64 .x27 = s0.readReg64 .x27)
    (_hx28 : s3.readReg64 .x28 = s0.readReg64 .x28)
    (hx29 : s3.readReg64 .x29 = s0.sp - 64#64)
    (hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 .lr) s3
      (archiveMidRawPre A s0 recPtr prevCap prevPtr G sess bs336 capEnc ptrEnc c0 v464 v112
        (A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (archiveOverGenSpec A).post ⟨recPtr, prevCap, prevPtr, G, sess⟩ s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (archiveQp s0 R) := by
  have hfn : libsignalSessionCode.fnOff archiveCurrentStateInnerName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner") :=
    libsignalSessionCode_fnOff_archive
  have hdrop := dropLocal1_arch_okX hDrop
  code_fetches_from CryptoVerification.libsignalSessionCode
    archiveBin img.base (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
    0x110 0x38
  code_fetches_from CryptoVerification.libsignalSessionCode
    archiveBin img.base (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
    0x15c 0x40
  revert hpc3
  have hpc_anchor :
      ({ s0 with pc := (SP2Ext img.base ext).fnAddr archiveCurrentStateInnerName } : State).pc =
        (SP2Ext img.base ext).fnAddr archiveCurrentStateInnerName := rfl
  examples_generalize_entry
  clear hpc_anchor
  intro hpc3
  simp only [archiveEncodeRawCutOff, arm64_norm] at hpc3
  examples_hide_fetches
  unfold archiveMidRawPre
  have hcap_beq1 : (prevCap == 0#64) = false := beq_false_of_ne hcap
  have hcap_beq2 : (0#64 == prevCap) = false := beq_false_of_ne (Ne.symm hcap)
  have hcap_bne1 : (prevCap != 0#64) = true := bne_iff_ne.mpr hcap
  have hcap_bne2 : (0#64 != prevCap) = true := bne_iff_ne.mpr (Ne.symm hcap)
  apply SepWPpIn.of_sepWP
    (mid := entry +
      bv% (2 ^ 64 +
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") -
        (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner")))
  rw [vecU8At_unpack_88X, memRegion_prev_slot0_cells prevPtr prevCap hcap hbound]
  refine SepWP.fold (cell112_splitX s0.sp _) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro lo112
  apply SepWP.exists_left; intro hi112
  apply SepWP.exists_left; intro sc2
  apply SepWP.exists_left; intro sc1
  apply SepWP.exists_left; intro sc0
  wp_steps
  refine SepWP.fold
    (sessionAt_entails_sessionStateAt A (s0.sp - 456#64) (clearPendingGhost G) (clearPending sess))
    (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  wppin_callc hdrop ((dropLocal1SubSpecX A).inImage img)
    ⟨s0.sp - 456#64, clearPendingGhost G, (clearPending sess).state⟩
  apply SepWPpIn.of_sepWP_ret
  wp_steps
  refine SepWP.fold
    (vecU8_from_cellsX A prevPtr _ _ (encSessionMem (clearPendingGhost G) (clearPending sess)))
    (by sep_focus) ?_
  refine SepWP.fold
    (prevVecAt_one_of_parts A recPtr prevCap prevPtr
      (encSessionMem (clearPendingGhost G) (clearPending sess)) hcap hbound hprev_ne)
    (by sep_focus) ?_
  have h32 : ((recPtr + 32#64) ↦ₛ bs336) ⊢ memRegion (recPtr + 0x20#64) 336 := by
    rw [← hbs336]; exact pointsToBytes_entails_memRegion _ _
  refine SepWP.fold h32 (by sep_focus) ?_
  refine SepWP.fold
    (stackAt_archive_pack_344X s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (by sep_focus) ?_
  wp_done

/-! ## Top-Level `ArchiveOverOkX` and `ArchiveOverGenOk` -/

private structure TailDeps (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  alloc : Proofs.libsignal.Stage1X.AllocContractsX img A ext
  drop : DropSessionStructureLocal1OkX img A ext

private theorem sepWPpIn_mono_post {img : Obj.Image} {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q1 Q2 Qp : State → SepProp → Prop}
    (hQ : ∀ sf P_f, Q1 sf P_f → Q2 sf P_f)
    (h : SepWPpIn img prog ret s P Q1 Qp) :
    SepWPpIn img prog ret s P Q2 Qp := by
  intro hF hsym R hm hL
  obtain ⟨sf, hsteps, hout⟩ := h hF hsym R hm hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hret, hrun, Pm, hpm, hq⟩ | hrest
  · exact Or.inl ⟨hret, hrun, Pm, hpm, hQ sf Pm hq⟩
  · exact Or.inr hrest

set_option maxHeartbeats 800000 in
theorem archive_over_okX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext)
    (hRaw : EncodeRawOkX img A ext)
    (hDrop : DropSessionStructureLocal1OkX img A ext) :
    ArchiveOverOkX img A ext := by
  have hDeps : TailDeps img A ext := ⟨hC.alloc, hDrop⟩
  clear hDrop
  unfold ArchiveOverOkX archiveOverSpecX
  show subroutine_ok (SP2Ext img.base ext) _ _
  wppin_init x s0
  obtain ⟨recPtr, prevPtr, G, sess⟩ := x
  dsimp only at *
  have hx0 : s0.readReg64 .x0 = recPtr := by assumption
  have hprev_ne : prevPtr ≠ 0#64 := by assumption
  have hlen_enc : (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 2 ^ 32 := by
    assumption
  conv => arg 5; rw [hdrP_eq, stackAt_archive_unpackX s0.sp]
  conv => arg 5; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPpIn.exists_elim fun c0 => SepWPpIn.exists_elim fun c1 =>
    SepWPpIn.exists_elim fun c2 => SepWPpIn.exists_elim fun c3 =>
    SepWPpIn.exists_elim fun c4 => SepWPpIn.exists_elim fun c5 =>
    SepWPpIn.exists_elim fun c6 => SepWPpIn.exists_elim fun c7 =>
    SepWPpIn.exists_elim fun c8 => SepWPpIn.exists_elim fun c9 =>
    SepWPpIn.exists_elim fun c10 => SepWPpIn.exists_elim fun c11 =>
    SepWPpIn.exists_elim fun v112 => SepWPpIn.exists_elim fun v456 =>
    SepWPpIn.exists_elim fun v464 => ?_
  refine SepWPpIn.weaken_pre
    (P' := (recPtr ↦₆₄ 0#64) ∗ ((recPtr + 8#64) ↦₆₄ prevPtr) ∗ ((recPtr + 16#64) ↦₆₄ 0#64) ∗
      sessionStateReprAt A (recPtr + 0x18#64) G sess ∗ A.pool ∗
      stackAt (s0.sp - 464#64) serializeSubStackX ∗
      ((s0.sp - 464#64) ↦₆₄ v464) ∗ ((s0.sp - 456#64) ↦₆₄ v456) ∗
      memRegion (s0.sp - 448#64) 336 ∗ ((s0.sp - 112#64) ↦₁₂₈ v112) ∗
      ((s0.sp - 96#64) ↦₆₄ c0) ∗ ((s0.sp - 88#64) ↦₆₄ c1) ∗
      ((s0.sp - 80#64) ↦₆₄ c2) ∗ ((s0.sp - 72#64) ↦₆₄ c3) ∗
      ((s0.sp - 64#64) ↦₆₄ c4) ∗ ((s0.sp - 56#64) ↦₆₄ c5) ∗
      ((s0.sp - 48#64) ↦₆₄ c6) ∗ ((s0.sp - 40#64) ↦₆₄ c7) ∗
      ((s0.sp - 32#64) ↦₆₄ c8) ∗ ((s0.sp - 24#64) ↦₆₄ c9) ∗
      ((s0.sp - 16#64) ↦₆₄ c10) ∗ ((s0.sp - 8#64) ↦₆₄ c11) ∗ emp)
    (Entails.of_eq (by simp only [sepConj_emp])) ?_
  exact archive_head_to_raw_cps hC hRaw recPtr 0#64 prevPtr G sess emp _ s0 _
    (by assumption) (by assumption) (by assumption) hx0 hlen_enc
    c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v464 v456 v112
    fun s3 bs336 capEnc ptrEnc hbs336 hpc3 hrun3 hsp3 htr3 hx19 hx20 hx21 hx23
      hx24 hx25 hx26 hx27 hx28 hx29 hvregs3 =>
      archive_tail_zero_cap_wp hDeps.alloc hDeps.drop recPtr prevPtr hprev_ne G sess bs336 hbs336
        capEnc ptrEnc c0 v464 v112 _ s0 s3 (by assumption)
        hpc3 hrun3 hsp3 htr3 hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs3

set_option maxHeartbeats 800000 in
theorem archive_over_gen_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext)
    (hRaw : EncodeRawOkX img A ext)
    (hDrop : DropSessionStructureLocal1OkX img A ext) :
    ArchiveOverGenOk img A ext := by
  have hDeps : TailDeps img A ext := ⟨hC.alloc, hDrop⟩
  clear hDrop
  unfold ArchiveOverGenOk archiveOverGenSpec
  simp only [prevVecAt_nil_eq]
  show subroutine_ok (SP2Ext img.base ext) _ _
  wppin_init x s0
  obtain ⟨recPtr, prevCap, prevPtr, G, sess⟩ := x
  dsimp only at *
  have hx0 : s0.readReg64 .x0 = recPtr := by assumption
  have hlen_enc : (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 2 ^ 32 := by
    assumption
  conv => arg 5; rw [stackAt_archive_unpackX s0.sp]
  by_cases hcap : prevCap = 0#64
  · subst hcap
    conv => arg 5; rw [prevVecAt_zero_nil_eq, hdrP_eq]
    conv => arg 5; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpIn.exists_elim fun c0 => SepWPpIn.exists_elim fun c1 =>
      SepWPpIn.exists_elim fun c2 => SepWPpIn.exists_elim fun c3 =>
      SepWPpIn.exists_elim fun c4 => SepWPpIn.exists_elim fun c5 =>
      SepWPpIn.exists_elim fun c6 => SepWPpIn.exists_elim fun c7 =>
      SepWPpIn.exists_elim fun c8 => SepWPpIn.exists_elim fun c9 =>
      SepWPpIn.exists_elim fun c10 => SepWPpIn.exists_elim fun c11 =>
      SepWPpIn.exists_elim fun v112 => SepWPpIn.exists_elim fun v456 =>
      SepWPpIn.exists_elim fun v464 => ?_
    refine SepWPpIn.weaken_pre
      (P' := ⌜prevPtr ≠ 0#64⌝ ∗
        ((recPtr ↦₆₄ 0#64) ∗ ((recPtr + 8#64) ↦₆₄ prevPtr) ∗ ((recPtr + 16#64) ↦₆₄ 0#64) ∗
          sessionStateReprAt A (recPtr + 0x18#64) G sess ∗ A.pool ∗
          stackAt (s0.sp - 464#64) serializeSubStackX ∗
          ((s0.sp - 464#64) ↦₆₄ v464) ∗ ((s0.sp - 456#64) ↦₆₄ v456) ∗
          memRegion (s0.sp - 448#64) 336 ∗ ((s0.sp - 112#64) ↦₁₂₈ v112) ∗
          ((s0.sp - 96#64) ↦₆₄ c0) ∗ ((s0.sp - 88#64) ↦₆₄ c1) ∗
          ((s0.sp - 80#64) ↦₆₄ c2) ∗ ((s0.sp - 72#64) ↦₆₄ c3) ∗
          ((s0.sp - 64#64) ↦₆₄ c4) ∗ ((s0.sp - 56#64) ↦₆₄ c5) ∗
          ((s0.sp - 48#64) ↦₆₄ c6) ∗ ((s0.sp - 40#64) ↦₆₄ c7) ∗
          ((s0.sp - 32#64) ↦₆₄ c8) ∗ ((s0.sp - 24#64) ↦₆₄ c9) ∗
          ((s0.sp - 16#64) ↦₆₄ c10) ∗ ((s0.sp - 8#64) ↦₆₄ c11) ∗ emp))
      (Entails.of_eq (by simp only [sepConj_emp]; ac_rfl)) ?_
    refine SepWPpIn.pure_elim fun hprev_ne => ?_
    refine sepWPpIn_mono_post ?_
      (archive_head_to_raw_cps hC hRaw recPtr 0#64 prevPtr G sess emp _ s0 _
        (by assumption) (by assumption) (by assumption) hx0 hlen_enc
        c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v464 v456 v112
        fun s3 bs336 capEnc ptrEnc hbs336 hpc3 hrun3 hsp3 htr3 hx19 hx20 hx21 hx23
          hx24 hx25 hx26 hx27 hx28 hx29 hvregs3 =>
          archive_tail_zero_cap_wp hDeps.alloc hDeps.drop recPtr prevPtr hprev_ne G sess bs336 hbs336
            capEnc ptrEnc c0 v464 v112 _ s0 s3 (by assumption)
            hpc3 hrun3 hsp3 htr3 hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs3)
    intro sf P_f ⟨hm_post, hsp_sf, hcs_sf⟩
    refine ⟨fun hm => Satisfies.mono (sepConj_mono_left ?_) (hm_post hm), hsp_sf, hcs_sf⟩
    unfold archiveOverSpecX
    dsimp only
    refine sepConj_mono_right (sepConj_mono_left ?_)
    exact Entails.sepExists_elim fun q => hdrP_prev1_entails_gen A recPtr q _
  · conv => arg 5; rw [prevVecAt_ne_zero_nil_eq A recPtr prevCap prevPtr hcap, hdrP_eq]
    conv => arg 5; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpIn.exists_elim fun c0 => SepWPpIn.exists_elim fun c1 =>
      SepWPpIn.exists_elim fun c2 => SepWPpIn.exists_elim fun c3 =>
      SepWPpIn.exists_elim fun c4 => SepWPpIn.exists_elim fun c5 =>
      SepWPpIn.exists_elim fun c6 => SepWPpIn.exists_elim fun c7 =>
      SepWPpIn.exists_elim fun c8 => SepWPpIn.exists_elim fun c9 =>
      SepWPpIn.exists_elim fun c10 => SepWPpIn.exists_elim fun c11 =>
      SepWPpIn.exists_elim fun v112 => SepWPpIn.exists_elim fun v456 =>
      SepWPpIn.exists_elim fun v464 => ?_
    refine SepWPpIn.weaken_pre
      (P' := ⌜prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
        ((recPtr ↦₆₄ prevCap) ∗ ((recPtr + 8#64) ↦₆₄ prevPtr) ∗ ((recPtr + 16#64) ↦₆₄ 0#64) ∗
          sessionStateReprAt A (recPtr + 0x18#64) G sess ∗ A.pool ∗
          stackAt (s0.sp - 464#64) serializeSubStackX ∗
          ((s0.sp - 464#64) ↦₆₄ v464) ∗ ((s0.sp - 456#64) ↦₆₄ v456) ∗
          memRegion (s0.sp - 448#64) 336 ∗ ((s0.sp - 112#64) ↦₁₂₈ v112) ∗
          ((s0.sp - 96#64) ↦₆₄ c0) ∗ ((s0.sp - 88#64) ↦₆₄ c1) ∗
          ((s0.sp - 80#64) ↦₆₄ c2) ∗ ((s0.sp - 72#64) ↦₆₄ c3) ∗
          ((s0.sp - 64#64) ↦₆₄ c4) ∗ ((s0.sp - 56#64) ↦₆₄ c5) ∗
          ((s0.sp - 48#64) ↦₆₄ c6) ∗ ((s0.sp - 40#64) ↦₆₄ c7) ∗
          ((s0.sp - 32#64) ↦₆₄ c8) ∗ ((s0.sp - 24#64) ↦₆₄ c9) ∗
          ((s0.sp - 16#64) ↦₆₄ c10) ∗ ((s0.sp - 8#64) ↦₆₄ c11) ∗
          (A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24))))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWPpIn.pure_elim fun ⟨hbound, hprev_ne⟩ => ?_
    exact archive_head_to_raw_cps hC hRaw recPtr prevCap prevPtr G sess
      (A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) _ s0 _
      (by assumption) (by assumption) (by assumption) hx0 hlen_enc
      c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v464 v456 v112
      fun s3 bs336 capEnc ptrEnc hbs336 hpc3 hrun3 hsp3 htr3 hx19 hx20 hx21 hx23
        hx24 hx25 hx26 hx27 hx28 hx29 hvregs3 =>
        archive_tail_nonzero_cap_wp hDeps.drop recPtr prevCap prevPtr hcap hbound hprev_ne
          G sess bs336 hbs336 capEnc ptrEnc c0 v464 v112 _ s0 s3 (by assumption)
          hpc3 hrun3 hsp3 htr3 hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs3

/-! ## Relocatable `[LibsignalPlacement]` Proofs (Block `51`) -/

section Placed

open Arm64.Obj CryptoVerification.E2E.Record.Placed

attribute [local irreducible] Program.fetch Program.externAt?

theorem L1_ArchiveNone_Placed : True := trivial

set_option maxHeartbeats 800000 in
/-- Relocatable `prevCap = 0#64` tail (`grow_one` to capacity `4#64`) on `lsProg_51 H`. -/
theorem archive_tail_zero_cap_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8Spec A)))
    (hDrop : DropSessionStructureLocal1PlacedOkX A H)
    (recPtr prevPtr : BitVec 64)
    (hprev_ne : prevPtr ≠ 0#64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (bs336 : List (BitVec 8)) (hbs336 : bs336.length = 336)
    (capEnc ptrEnc c0 v464 : BitVec 64) (v112 : BitVec 128)
    (R : SepProp) (s0 s3 : State)
    (hsp_align : s0.spAligned = true)
    (hpc3 : s3.pc = (blkPl_51).base + (archiveEncodeRawCutOff + 4#64))
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 464#64)
    (htr3 : s3.trace = s0.trace)
    (hx19 : s3.readReg64 .x19 = recPtr)
    (_hx20 : s3.readReg64 .x20 = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length)
    (hx21 : s3.readReg64 .x21 = s0.sp - 112#64)
    (hx23 : s3.readReg64 .x23 = 0#64)
    (hx24 : s3.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s3.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s3.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s3.readReg64 .x27 = s0.readReg64 .x27)
    (_hx28 : s3.readReg64 .x28 = s0.readReg64 .x28)
    (hx29 : s3.readReg64 .x29 = s0.sp - 64#64)
    (hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0) :
    SepWPpLsCl lsmpl (lsProg_51 H) (s0.readReg64 .lr) s3
      (archiveMidRawPre A s0 recPtr 0#64 prevPtr G sess bs336 capEnc ptrEnc c0 v464 v112 emp)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (archiveOverSpecX A).post ⟨recPtr, prevPtr, G, sess⟩ s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (archiveQp s0 R) := by
  have hgrow := growOne_arch_placed_okX (callerProg := lsProg_51 H) hGrow
  have hdrop : subroutine_ok (lsProg_51 H) (lsmpl.base 6)
      (withLsCodeLoaded lsmpl (dropLocal1SubSpecX A)) :=
    dropLocal1_placed_sub_okX (callerProg := lsProg_51 H) hDrop
  simp only [archiveEncodeRawCutOff, arm64_norm] at hpc3
  unfold archiveMidRawPre
  conv => arg 5; simp only [sepConj_emp]
  apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 621)
  rw [vecU8At_unpack_88X]
  refine SepWP.fold (cell112_splitX s0.sp _) (by sep_focus) ?_
  apply sepWP_exists_left_sepX; intro lo112
  conv => arg 4; simp only [sepExists_sepConj_left]
  apply SepWP.exists_left; intro hi112
  conv => arg 4; simp only [sepConj_assoc]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  have hprev_ne0 : prevPtr ≠ 0 := hprev_ne
  wpplscl_callc hgrow (withLsCodeLoaded lsmpl (growOneSubSpecX A)) ⟨recPtr, 0#64, prevPtr, []⟩
  apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 6)
  rw [memRegion_prev96_cellsX, newCapVecU8_zeroX]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro sc0
  apply SepWP.exists_left; intro sc8
  apply SepWP.exists_left; intro sc16
  wp_steps
  refine SepWP.fold
    (sessionAt_entails_sessionStateAt A (s0.sp - 456#64) (clearPendingGhost G) (clearPending sess))
    (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  wpplscl_callc hdrop (withLsCodeLoaded lsmpl (dropLocal1SubSpecX A))
    ⟨s0.sp - 456#64, clearPendingGhost G, (clearPending sess).state⟩
  apply SepWPpLsCl.of_sepWP_ret
  wp_steps
  refine SepWP.fold
    (hdrP_prev1_of_raw_cellsX A recPtr _ _ _
      (encSessionMem (clearPendingGhost G) (clearPending sess)) (by assumption))
    (by sep_focus) ?_
  have h32 : ((recPtr + 32#64) ↦ₛ bs336) ⊢ memRegion (recPtr + 0x20#64) 336 := by
    rw [← hbs336]; exact pointsToBytes_entails_memRegion _ _
  refine SepWP.fold h32 (by sep_focus) ?_
  refine SepWP.fold
    (stackAt_archive_pack_344X s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (by sep_focus) ?_
  wp_done

set_option maxHeartbeats 800000 in
/-- Relocatable `prevCap ≠ 0#64` tail (in-place store into pre-allocated buffer) on `lsProg_51 H`. -/
theorem archive_tail_nonzero_cap_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hDrop : DropSessionStructureLocal1PlacedOkX A H)
    (recPtr prevCap prevPtr : BitVec 64)
    (hcap : prevCap ≠ 0#64)
    (hbound : prevCap.toNat * 24 < 2 ^ 63)
    (hprev_ne : prevPtr ≠ 0#64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (bs336 : List (BitVec 8)) (hbs336 : bs336.length = 336)
    (capEnc ptrEnc c0 v464 : BitVec 64) (v112 : BitVec 128)
    (R : SepProp) (s0 s3 : State)
    (hsp_align : s0.spAligned = true)
    (hpc3 : s3.pc = (blkPl_51).base + (archiveEncodeRawCutOff + 4#64))
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 464#64)
    (htr3 : s3.trace = s0.trace)
    (hx19 : s3.readReg64 .x19 = recPtr)
    (_hx20 : s3.readReg64 .x20 = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length)
    (hx21 : s3.readReg64 .x21 = s0.sp - 112#64)
    (hx23 : s3.readReg64 .x23 = 0#64)
    (hx24 : s3.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s3.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s3.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s3.readReg64 .x27 = s0.readReg64 .x27)
    (_hx28 : s3.readReg64 .x28 = s0.readReg64 .x28)
    (hx29 : s3.readReg64 .x29 = s0.sp - 64#64)
    (hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0) :
    SepWPpLsCl lsmpl (lsProg_51 H) (s0.readReg64 .lr) s3
      (archiveMidRawPre A s0 recPtr prevCap prevPtr G sess bs336 capEnc ptrEnc c0 v464 v112
        (A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (archiveOverGenSpec A).post ⟨recPtr, prevCap, prevPtr, G, sess⟩ s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (archiveQp s0 R) := by
  have hdrop : subroutine_ok (lsProg_51 H) (lsmpl.base 6)
      (withLsCodeLoaded lsmpl (dropLocal1SubSpecX A)) :=
    dropLocal1_placed_sub_okX (callerProg := lsProg_51 H) hDrop
  simp only [archiveEncodeRawCutOff, arm64_norm] at hpc3
  unfold archiveMidRawPre
  have hcap_beq1 : (prevCap == 0#64) = false := beq_false_of_ne hcap
  have hcap_beq2 : (0#64 == prevCap) = false := beq_false_of_ne (Ne.symm hcap)
  have hcap_bne1 : (prevCap != 0#64) = true := bne_iff_ne.mpr hcap
  have hcap_bne2 : (0#64 != prevCap) = true := bne_iff_ne.mpr (Ne.symm hcap)
  apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 6)
  rw [vecU8At_unpack_88X, memRegion_prev_slot0_cells prevPtr prevCap hcap hbound]
  refine SepWP.fold (cell112_splitX s0.sp _) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro lo112
  apply SepWP.exists_left; intro hi112
  apply SepWP.exists_left; intro sc2
  apply SepWP.exists_left; intro sc1
  apply SepWP.exists_left; intro sc0
  wp_steps
  refine SepWP.fold
    (sessionAt_entails_sessionStateAt A (s0.sp - 456#64) (clearPendingGhost G) (clearPending sess))
    (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  wpplscl_callc hdrop (withLsCodeLoaded lsmpl (dropLocal1SubSpecX A))
    ⟨s0.sp - 456#64, clearPendingGhost G, (clearPending sess).state⟩
  apply SepWPpLsCl.of_sepWP_ret
  wp_steps
  refine SepWP.fold
    (vecU8_from_cellsX A prevPtr _ _ (encSessionMem (clearPendingGhost G) (clearPending sess)))
    (by sep_focus) ?_
  refine SepWP.fold
    (prevVecAt_one_of_parts A recPtr prevCap prevPtr
      (encSessionMem (clearPendingGhost G) (clearPending sess)) hcap hbound hprev_ne)
    (by sep_focus) ?_
  have h32 : ((recPtr + 32#64) ↦ₛ bs336) ⊢ memRegion (recPtr + 0x20#64) 336 := by
    rw [← hbs336]; exact pointsToBytes_entails_memRegion _ _
  refine SepWP.fold h32 (by sep_focus) ?_
  refine SepWP.fold
    (stackAt_archive_pack_344X s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (by sep_focus) ?_
  wp_done

private structure TailDepsPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop where
  grow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
    (withLsCl lsmpl (growOneVecU8Spec A))
  drop : DropSessionStructureLocal1PlacedOkX A H

private theorem sepWPpLsCl_mono_post {pl : MultiPlacement} {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q1 Q2 Qp : State → SepProp → Prop}
    (hQ : ∀ sf P_f, Q1 sf P_f → Q2 sf P_f)
    (h : SepWPpLsCl pl prog ret s P Q1 Qp) :
    SepWPpLsCl pl prog ret s P Q2 Qp := by
  intro hcl R hm hL
  obtain ⟨sf, hsteps, hout⟩ := h hcl R hm hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hret, hrun, Pm, hpm, hq⟩ | hrest
  · exact Or.inl ⟨hret, hrun, Pm, hpm, hQ sf Pm hq⟩
  · exact Or.inr hrest

set_option maxHeartbeats 800000 in
/-- Relocatable `ArchiveOverPlacedOkX` (Block `51`) from `SerContractsXPlaced`, a Block `51`→`621`
`grow_one` contract, `EncodeRawPlacedOkX`, and `DropSessionStructureLocal1PlacedOkX`. -/
theorem archive_over_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8Spec A)))
    (hRaw : EncodeRawPlacedOkX A H)
    (hDrop : DropSessionStructureLocal1PlacedOkX A H) :
    ArchiveOverPlacedOkX A H := by
  have hDeps : TailDepsPlaced A H := ⟨hGrow, hDrop⟩
  clear hGrow hDrop
  unfold ArchiveOverPlacedOkX archiveOverSpecX
  show subroutine_ok (lsProg_51 H) _ _
  wpplscl_init x s0
  obtain ⟨recPtr, prevPtr, G, sess⟩ := x
  dsimp only at *
  have hx0 : s0.readReg64 .x0 = recPtr := by assumption
  have hprev_ne : prevPtr ≠ 0#64 := by assumption
  have hlen_enc : (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 2 ^ 32 := by
    assumption
  conv => arg 5; rw [hdrP_eq, stackAt_archive_unpackX s0.sp]
  conv => arg 5; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPpLsCl.exists_elim fun c0 => SepWPpLsCl.exists_elim fun c1 =>
    SepWPpLsCl.exists_elim fun c2 => SepWPpLsCl.exists_elim fun c3 =>
    SepWPpLsCl.exists_elim fun c4 => SepWPpLsCl.exists_elim fun c5 =>
    SepWPpLsCl.exists_elim fun c6 => SepWPpLsCl.exists_elim fun c7 =>
    SepWPpLsCl.exists_elim fun c8 => SepWPpLsCl.exists_elim fun c9 =>
    SepWPpLsCl.exists_elim fun c10 => SepWPpLsCl.exists_elim fun c11 =>
    SepWPpLsCl.exists_elim fun v112 => SepWPpLsCl.exists_elim fun v456 =>
    SepWPpLsCl.exists_elim fun v464 => ?_
  refine SepWPpLsCl.weaken_pre
    (P' := (recPtr ↦₆₄ 0#64) ∗ ((recPtr + 8#64) ↦₆₄ prevPtr) ∗ ((recPtr + 16#64) ↦₆₄ 0#64) ∗
      sessionStateReprAt A (recPtr + 0x18#64) G sess ∗ A.pool ∗
      stackAt (s0.sp - 464#64) serializeSubStackX ∗
      ((s0.sp - 464#64) ↦₆₄ v464) ∗ ((s0.sp - 456#64) ↦₆₄ v456) ∗
      memRegion (s0.sp - 448#64) 336 ∗ ((s0.sp - 112#64) ↦₁₂₈ v112) ∗
      ((s0.sp - 96#64) ↦₆₄ c0) ∗ ((s0.sp - 88#64) ↦₆₄ c1) ∗
      ((s0.sp - 80#64) ↦₆₄ c2) ∗ ((s0.sp - 72#64) ↦₆₄ c3) ∗
      ((s0.sp - 64#64) ↦₆₄ c4) ∗ ((s0.sp - 56#64) ↦₆₄ c5) ∗
      ((s0.sp - 48#64) ↦₆₄ c6) ∗ ((s0.sp - 40#64) ↦₆₄ c7) ∗
      ((s0.sp - 32#64) ↦₆₄ c8) ∗ ((s0.sp - 24#64) ↦₆₄ c9) ∗
      ((s0.sp - 16#64) ↦₆₄ c10) ∗ ((s0.sp - 8#64) ↦₆₄ c11) ∗ emp)
    (Entails.of_eq (by simp only [sepConj_emp])) ?_
  exact archive_head_to_raw_placed_cps hC hRaw recPtr 0#64 prevPtr G sess emp _ s0 _
    (by assumption) (by assumption) (by assumption) hx0 hlen_enc
    c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v464 v456 v112
    fun s3 bs336 capEnc ptrEnc hbs336 hpc3 hrun3 hsp3 htr3 hx19 hx20 hx21 hx23
      hx24 hx25 hx26 hx27 hx28 hx29 hvregs3 =>
      archive_tail_zero_cap_placed_wp hDeps.grow hDeps.drop recPtr prevPtr hprev_ne G sess bs336 hbs336
        capEnc ptrEnc c0 v464 v112 _ s0 s3 (by assumption)
        hpc3 hrun3 hsp3 htr3 hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs3

/-- Caller-block-polymorphic `withLsCl` form of `archive_over_placed_ok_of_contracts`. -/
theorem archive_over_placed_cl_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced A H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8Spec A)))
    (hRaw : EncodeRawPlacedOkX A H)
    (hDrop : DropSessionStructureLocal1PlacedOkX A H) :
    subroutine_ok callerProg (lsmpl.base 51) (withLsCl lsmpl (archiveOverSpecX A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (archive_over_placed_ok_of_contracts hC hGrow hRaw hDrop)

set_option maxHeartbeats 800000 in
/-- Relocatable `ArchiveOverGenPlacedOk` (Block `51`) from `SerContractsXPlaced`, a Block `51`→`621`
`grow_one` contract, `EncodeRawPlacedOkX`, and `DropSessionStructureLocal1PlacedOkX`. -/
theorem archive_over_gen_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8Spec A)))
    (hRaw : EncodeRawPlacedOkX A H)
    (hDrop : DropSessionStructureLocal1PlacedOkX A H) :
    ArchiveOverGenPlacedOk A H := by
  have hDeps : TailDepsPlaced A H := ⟨hGrow, hDrop⟩
  clear hGrow hDrop
  unfold ArchiveOverGenPlacedOk archiveOverGenSpec
  simp only [prevVecAt_nil_eq]
  show subroutine_ok (lsProg_51 H) _ _
  wpplscl_init x s0
  obtain ⟨recPtr, prevCap, prevPtr, G, sess⟩ := x
  dsimp only at *
  have hx0 : s0.readReg64 .x0 = recPtr := by assumption
  have hlen_enc : (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 2 ^ 32 := by
    assumption
  conv => arg 5; rw [stackAt_archive_unpackX s0.sp]
  by_cases hcap : prevCap = 0#64
  · subst hcap
    conv => arg 5; rw [prevVecAt_zero_nil_eq, hdrP_eq]
    conv => arg 5; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpLsCl.exists_elim fun c0 => SepWPpLsCl.exists_elim fun c1 =>
      SepWPpLsCl.exists_elim fun c2 => SepWPpLsCl.exists_elim fun c3 =>
      SepWPpLsCl.exists_elim fun c4 => SepWPpLsCl.exists_elim fun c5 =>
      SepWPpLsCl.exists_elim fun c6 => SepWPpLsCl.exists_elim fun c7 =>
      SepWPpLsCl.exists_elim fun c8 => SepWPpLsCl.exists_elim fun c9 =>
      SepWPpLsCl.exists_elim fun c10 => SepWPpLsCl.exists_elim fun c11 =>
      SepWPpLsCl.exists_elim fun v112 => SepWPpLsCl.exists_elim fun v456 =>
      SepWPpLsCl.exists_elim fun v464 => ?_
    refine SepWPpLsCl.weaken_pre
      (P' := ⌜prevPtr ≠ 0#64⌝ ∗
        ((recPtr ↦₆₄ 0#64) ∗ ((recPtr + 8#64) ↦₆₄ prevPtr) ∗ ((recPtr + 16#64) ↦₆₄ 0#64) ∗
          sessionStateReprAt A (recPtr + 0x18#64) G sess ∗ A.pool ∗
          stackAt (s0.sp - 464#64) serializeSubStackX ∗
          ((s0.sp - 464#64) ↦₆₄ v464) ∗ ((s0.sp - 456#64) ↦₆₄ v456) ∗
          memRegion (s0.sp - 448#64) 336 ∗ ((s0.sp - 112#64) ↦₁₂₈ v112) ∗
          ((s0.sp - 96#64) ↦₆₄ c0) ∗ ((s0.sp - 88#64) ↦₆₄ c1) ∗
          ((s0.sp - 80#64) ↦₆₄ c2) ∗ ((s0.sp - 72#64) ↦₆₄ c3) ∗
          ((s0.sp - 64#64) ↦₆₄ c4) ∗ ((s0.sp - 56#64) ↦₆₄ c5) ∗
          ((s0.sp - 48#64) ↦₆₄ c6) ∗ ((s0.sp - 40#64) ↦₆₄ c7) ∗
          ((s0.sp - 32#64) ↦₆₄ c8) ∗ ((s0.sp - 24#64) ↦₆₄ c9) ∗
          ((s0.sp - 16#64) ↦₆₄ c10) ∗ ((s0.sp - 8#64) ↦₆₄ c11) ∗ emp))
      (Entails.of_eq (by simp only [sepConj_emp]; ac_rfl)) ?_
    refine SepWPpLsCl.pure_elim fun hprev_ne => ?_
    refine sepWPpLsCl_mono_post ?_
      (archive_head_to_raw_placed_cps hC hRaw recPtr 0#64 prevPtr G sess emp _ s0 _
        (by assumption) (by assumption) (by assumption) hx0 hlen_enc
        c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v464 v456 v112
        fun s3 bs336 capEnc ptrEnc hbs336 hpc3 hrun3 hsp3 htr3 hx19 hx20 hx21 hx23
          hx24 hx25 hx26 hx27 hx28 hx29 hvregs3 =>
          archive_tail_zero_cap_placed_wp hDeps.grow hDeps.drop recPtr prevPtr hprev_ne G sess bs336 hbs336
            capEnc ptrEnc c0 v464 v112 _ s0 s3 (by assumption)
            hpc3 hrun3 hsp3 htr3 hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs3)
    intro sf P_f ⟨hm_post, hsp_sf, hcs_sf⟩
    refine ⟨fun hm => Satisfies.mono (sepConj_mono_left ?_) (hm_post hm), hsp_sf, hcs_sf⟩
    unfold archiveOverSpecX
    dsimp only
    refine sepConj_mono_right (sepConj_mono_left ?_)
    exact Entails.sepExists_elim fun q => hdrP_prev1_entails_gen A recPtr q _
  · conv => arg 5; rw [prevVecAt_ne_zero_nil_eq A recPtr prevCap prevPtr hcap, hdrP_eq]
    conv => arg 5; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpLsCl.exists_elim fun c0 => SepWPpLsCl.exists_elim fun c1 =>
      SepWPpLsCl.exists_elim fun c2 => SepWPpLsCl.exists_elim fun c3 =>
      SepWPpLsCl.exists_elim fun c4 => SepWPpLsCl.exists_elim fun c5 =>
      SepWPpLsCl.exists_elim fun c6 => SepWPpLsCl.exists_elim fun c7 =>
      SepWPpLsCl.exists_elim fun c8 => SepWPpLsCl.exists_elim fun c9 =>
      SepWPpLsCl.exists_elim fun c10 => SepWPpLsCl.exists_elim fun c11 =>
      SepWPpLsCl.exists_elim fun v112 => SepWPpLsCl.exists_elim fun v456 =>
      SepWPpLsCl.exists_elim fun v464 => ?_
    refine SepWPpLsCl.weaken_pre
      (P' := ⌜prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
        ((recPtr ↦₆₄ prevCap) ∗ ((recPtr + 8#64) ↦₆₄ prevPtr) ∗ ((recPtr + 16#64) ↦₆₄ 0#64) ∗
          sessionStateReprAt A (recPtr + 0x18#64) G sess ∗ A.pool ∗
          stackAt (s0.sp - 464#64) serializeSubStackX ∗
          ((s0.sp - 464#64) ↦₆₄ v464) ∗ ((s0.sp - 456#64) ↦₆₄ v456) ∗
          memRegion (s0.sp - 448#64) 336 ∗ ((s0.sp - 112#64) ↦₁₂₈ v112) ∗
          ((s0.sp - 96#64) ↦₆₄ c0) ∗ ((s0.sp - 88#64) ↦₆₄ c1) ∗
          ((s0.sp - 80#64) ↦₆₄ c2) ∗ ((s0.sp - 72#64) ↦₆₄ c3) ∗
          ((s0.sp - 64#64) ↦₆₄ c4) ∗ ((s0.sp - 56#64) ↦₆₄ c5) ∗
          ((s0.sp - 48#64) ↦₆₄ c6) ∗ ((s0.sp - 40#64) ↦₆₄ c7) ∗
          ((s0.sp - 32#64) ↦₆₄ c8) ∗ ((s0.sp - 24#64) ↦₆₄ c9) ∗
          ((s0.sp - 16#64) ↦₆₄ c10) ∗ ((s0.sp - 8#64) ↦₆₄ c11) ∗
          (A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24))))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWPpLsCl.pure_elim fun ⟨hbound, hprev_ne⟩ => ?_
    exact archive_head_to_raw_placed_cps hC hRaw recPtr prevCap prevPtr G sess
      (A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) _ s0 _
      (by assumption) (by assumption) (by assumption) hx0 hlen_enc
      c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v464 v456 v112
      fun s3 bs336 capEnc ptrEnc hbs336 hpc3 hrun3 hsp3 htr3 hx19 hx20 hx21 hx23
        hx24 hx25 hx26 hx27 hx28 hx29 hvregs3 =>
        archive_tail_nonzero_cap_placed_wp hDeps.drop recPtr prevCap prevPtr hcap hbound hprev_ne
          G sess bs336 hbs336 capEnc ptrEnc c0 v464 v112 _ s0 s3 (by assumption)
          hpc3 hrun3 hsp3 htr3 hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs3

/-- Caller-block-polymorphic `withLsCl` form of `archive_over_gen_placed_ok_of_contracts`. -/
theorem archive_over_gen_placed_cl_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced A H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8Spec A)))
    (hRaw : EncodeRawPlacedOkX A H)
    (hDrop : DropSessionStructureLocal1PlacedOkX A H) :
    subroutine_ok callerProg (lsmpl.base 51) (withLsCl lsmpl (archiveOverGenSpec A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (archive_over_gen_placed_ok_of_contracts hC hGrow hRaw hDrop)

end Placed

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
