/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Base
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Steps
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMerge -- shake: keep

/-!
# Seed `SessionStructure::merge_field` on `receiver_chains` (Tag `7`)

Proves `mergeFieldSeed7_ok` and `mergeFieldSeed7_placed_ok` for
`<SessionStructure as prost::Message>::merge_field::<&mut &[u8]>` (`0x581c`, block `15`) restricted
to tag `7` (`receiver_chains` at `SS + 0x48`), decoding into a 104-byte stack `Chain::default()`
slot via `message::merge<Chain>` and pushing onto `Vec<Chain>` via `RawVec<Chain>::grow_one`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeSeed

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr sessionImg0
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg

attribute [local irreducible] prostSSRest_receiverChains prostChainAt prostSSAt mfFramePad_receiverChains
  Prost.sliceCursorAt Prost.sliceCursorAfter

theorem adrp_0x4601c_40_eq_receiverChains {entry : BitVec 64}
    (he : entry = sessionImg0.base + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) :
    (entry + bv% (40) &&& bv% (2 ^ 64 - 4096)) = sessionImg0.base + 20480#64 := by
  subst he
  have hadd : sessionImg0.base + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") + 40#64 = sessionImg0.base + 22596#64 := by
    rw [BitVec.add_assoc]; rfl
  rw [hadd, adrp_page_of_aligned sessionImg0_base_aligned_receiverChains]
  rfl

theorem zext64_trunc32_and_255_eq_of_trunc8_receiverChains {w : BitVec 64} {b : BitVec 8}
    (h : w.truncate 8 = b) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 w) &&& 255#64 = b.zeroExtend 64 := by
  subst h
  bv_bits

theorem recv_payload_append_eq_receiverChains {fld : SeedField} {c : ChainV} (hfld : fld = .recv c)
    (tail : List (BitVec 8)) :
    [BitVec.ofNat 8 c.enc.length] ++ c.enc ++ tail = fld.payload ++ tail := by
  subst hfld
  rfl

theorem chainMerge_pre_eq_receiverChains (x : MergeFieldGhost) (c : ChainV) (s0_sp_232 sp : BitVec 64)
    (s : State) (hfld : x.fld = .recv c) (hsp : s.sp = sp) :
    chainMergeSeedSpec.pre ⟨s0_sp_232, c, x.bufRef, x.slot, x.ptr, x.tail, x.f⟩ s =
      ⌜(s.readReg64 .x0).setWidth 8 = 2#8 ∧ s.readReg64 .x1 = s0_sp_232 ∧
        s.readReg64 .x2 = x.bufRef ∧ (s.readReg64 .x3).setWidth 32 = 99#32 ∧
        SeedOk x.f ∧
        (SeedField.sender c ∈ seedFields x.f ∨ SeedField.recv c ∈ seedFields x.f) ∧
        (x.fld.payload ++ x.tail).length < 2 ^ 32 ∧
        sessionImg0.FrozenLoaded s ∧ s.symtab = sessionImg0.symtab⌝ ∗
      (prostChainAt A0 s0_sp_232 ⟨[], [], none⟩ ∗ (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗
        stackAt sp chainMergeStack) := by
  unfold chainMergeSeedSpec
  dsimp only
  rw [recv_payload_append_eq_receiverChains hfld x.tail, hsp]

theorem chainMerge_post_eq_receiverChains (x : MergeFieldGhost) (c : ChainV) (s0_sp_232 sp : BitVec 64)
    (s_pre sf : State) (hfld : x.fld = .recv c) (hsp : s_pre.sp = sp) :
    chainMergeSeedSpec.post ⟨s0_sp_232, c, x.bufRef, x.slot, x.ptr, x.tail, x.f⟩ s_pre sf ⊢
      ⌜sf.trace = s_pre.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      prostChainAt A0 s0_sp_232 c ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt sp chainMergeStack := by
  unfold chainMergeSeedSpec
  dsimp only
  rw [recv_payload_append_eq_receiverChains hfld x.tail, hsp]
  exact Entails.refl _

theorem prostChainAt_default_of_cells_lit_receiverChains (sp0 : BitVec 64) :
    ((sp0 - 232#64) ↦₆₄ 0#64) ∗
    ((sp0 - 224#64) ↦₆₄ 1#64) ∗
    ((sp0 - 216#64) ↦₆₄ 0#64) ∗
    ((sp0 - 208#64) ↦₆₄ 0#64) ∗
    ((sp0 - 200#64) ↦₆₄ 1#64) ∗
    ((sp0 - 192#64) ↦₆₄ 0#64) ∗
    ((sp0 - 184#64) ↦₆₄ 0#64) ∗
    ((sp0 - 176#64) ↦₆₄ 8#64) ∗
    ((sp0 - 168#64) ↦₆₄ 0#64) ∗
    ((sp0 - 160#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
    memRegion (sp0 - 152#64) 24 ⊢
    prostChainAt A0 (sp0 - 232#64) ⟨[], [], none⟩ := by
  simpa only [noneCap, sepConj_assoc] using prostChainAt_default_of_cells_receiverChains A0 sp0

theorem mfSavedRegs_intro_receiverChains (sp0 : BitVec 64) (s0 : State) (w56 : BitVec 64) :
    ((sp0 - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((sp0 - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((sp0 - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
    ((sp0 - 56#64) ↦₆₄ w56) ∗
    ((sp0 - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
    ((sp0 - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
    ((sp0 - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((sp0 - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((sp0 - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((sp0 - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
    mfSavedRegs_receiverChains sp0 s0 w56 :=
  Entails.refl _

attribute [local irreducible] mfSavedRegs_receiverChains

/-- `SessionStructure::merge_field` (`0x581c`) satisfies `mergeFieldSeedSpec` on seed's tag-`7`
`receiver_chains` field, decoding `Chain` into `sp + 8` via `message::merge<Chain>` and pushing
onto `SS + 0x48` via `RawVec<Chain>::grow_one`. -/
theorem mergeFieldSeed7_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) (hCh : ChainMergeSeedOk C ctl abs) :
    MergeFieldSeedOk C ctl (fun fl => ∃ c, fl = .recv c) abs := by
  apply subroutine_ok_of_sepWPp
  intro x Fr s0 hpc hrun hpre hsp
  refine ⟨_, Fr, hpre, ?_⟩
  conv => arg 4; dsimp only [mergeFieldSeedSpec]; simp only [sepConj_assoc]
  apply SepWPp.pure_left
  rintro ⟨hx0, hx1, hx2, hx3, hx4, ⟨c, hfld⟩, hSeedOk, hMemFields, -, -, hrecv_imp, hlen, hF, hsym⟩
  have hrecv : x.v.recv = [] := hrecv_imp (by rw [hfld])
  have hMemRecv : SeedField.recv c ∈ seedFields x.f := hfld ▸ hMemFields
  rw [hfld] at hx1 hx2
  dsimp only [SeedField.tag, SeedField.wt, CryptoVerification.LibsignalProtoCodec.WireType.toNat,
    BitVec.ofNat_eq_ofNat] at hx1 hx2
  have hx2' : BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x2)) &&& 255#64 = 2#64 :=
    zext64_trunc32_and_255_eq_of_trunc8_receiverChains hx2
  have hsp0 : s0.sp &&& 15#64 = 0#64 := eq_of_beq hsp
  have hsp240 : (s0.sp - 240#64) &&& 15#64 = 0#64 := sp_sub_240_aligned_receiverChains hsp0
  have hsp240_beq : ((s0.sp - 240#64) &&& 15#64 == 0#64) = true := beq_iff_eq.mpr hsp240
  have he : (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr mergeFieldName =
      sessionImg0.base + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") :=
    mergeField_fnAddr_eq_base_add_receiverChains C ctl
  have hCh' : subroutine_ok (tripleRatchetProgAt sessionImg0.base C ctl abs)
      ((tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr mergeFieldName + bv% (2 ^ 64 + (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")))
      chainMergeSeedSpec := by
    rw [chainMerge_fnAddr_eq_receiverChains]
    exact hCh
  have h2bc := @step_receiverChains_from_0x2bc_to_ret_receiverChains C ctl abs hC.2.2.2
    (fun fl => ∃ c, fl = .recv c) x c s0
  mf7_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0 60
  mf7_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 628 696
  rw [stackAt_mergeFieldStack_split_receiverChains s0.sp,
    memRegion80_chainInit_eq_cells10_receiverChains s0.sp,
    memRegion80_eq_cells10_receiverChains s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro c0
  apply SepWPp.exists_elim; intro c1
  apply SepWPp.exists_elim; intro c2
  apply SepWPp.exists_elim; intro c3
  apply SepWPp.exists_elim; intro c4
  apply SepWPp.exists_elim; intro c5
  apply SepWPp.exists_elim; intro c6
  apply SepWPp.exists_elim; intro c7
  apply SepWPp.exists_elim; intro c8
  apply SepWPp.exists_elim; intro c9
  apply SepWPp.exists_elim; intro w80
  apply SepWPp.exists_elim; intro w72
  apply SepWPp.exists_elim; intro w64
  apply SepWPp.exists_elim; intro w56
  apply SepWPp.exists_elim; intro w48
  apply SepWPp.exists_elim; intro w40
  apply SepWPp.exists_elim; intro w32
  apply SepWPp.exists_elim; intro w24
  apply SepWPp.exists_elim; intro w16
  apply SepWPp.exists_elim; intro w8
  dsimp only [tripleRatchetProgAt, mergeFieldName] at he hCh' h2bc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" = entry
  have hadrp : (entry + bv% (40) &&& bv% (2 ^ 64 - 4096)) = sessionImg0.base + 20480#64 :=
    adrp_0x4601c_40_eq_receiverChains he
  clear he
  examples_hide_fetches
  apply of_sepWP_inImage_receiverChains (entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>"))) hF hsym
  apply sepWP_intro_rodata_tag7_receiverChains hF
  wp_steps
  apply sepWP_drop_left_receiverChains
  apply SepWP.fold (prostChainAt_default_of_cells_lit_receiverChains s0.sp) (by sep_focus)
  apply SepWP.fold (mfSavedRegs_intro_receiverChains s0.sp s0 c3) (by sep_focus)
  apply SepWP.fold (Entails.of_eq (stackAt_sub_to_chainMerge_receiverChains (s0.sp - 240#64))) (by sep_focus)
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) ?_
  intro hF1 hsym1
  refine call_frame_inImage_receiverChains (ret_pc := entry + bv% (700)) hF1 hsym1 hCh'
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
    (by simp only [arm64_norm])
    (chainMerge_pre_eq_receiverChains x c (s0.sp - 232#64) (s0.sp - 240#64) _ hfld (by simp only [arm64_norm]))
    ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm], hSeedOk, Or.inr hMemRecv, hlen, hF1, hsym1⟩
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans_receiverChains (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hF2 hsym2
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx25m, hx26m, hx27m, hx28m, hfpm, hvregsm⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19m hx20m hx21m hx22m hx23m hx24m hx25m hx26m hx27m hx28m hfpm hvregsm
  have hsp_align_m : sm.spAligned = true := by
    simp only [State.spAligned, hspm]
    exact hsp240_beq
  refine SepWPp.fold
    (chainMerge_post_eq_receiverChains x c (s0.sp - 232#64) (s0.sp - 240#64) _ sm hfld ?_) rfl ?_
  · simp only [arm64_norm]
  simp only [sepConj_assoc]
  apply SepWPp.pure_left; rintro ⟨htr_m, hx0_m⟩
  have htr_m' : sm.trace = s0.trace := by simpa only [arm64_norm] using htr_m
  refine SepWPp.weaken_pre ?_
    (h2bc sm Fr c3 hrecv hfld hF2 hsym2 hpcm hrunm hspm hsp_align_m htr_m' hvregsm hx0_m hx20m hx26m hx27m hx28m)
  have hsub16384 : (s0.sp - 240#64) - 16144#64 = s0.sp - 16384#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  exact Entails.of_eq (by rw [hsub16384]; ac_rfl)

/-! ## Relocatable `[LibsignalPlacement]` Proof (`lsProg_15 H`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem chainMerge_placed_pre_eq_receiverChains [LibsignalPlacement]
    (x : MergeFieldGhost) (c : ChainV) (s0_sp_232 sp : BitVec 64)
    (s : State) (hfld : x.fld = .recv c) (hsp : s.sp = sp) :
    chainMergeSeedPlacedSpec.pre ⟨s0_sp_232, c, x.bufRef, x.slot, x.ptr, x.tail, x.f⟩ s =
      ⌜LibsignalCodeRoLoaded lsmpl s.mem ∧
        ((s.readReg64 .x0).setWidth 8 = 2#8 ∧ s.readReg64 .x1 = s0_sp_232 ∧
          s.readReg64 .x2 = x.bufRef ∧ (s.readReg64 .x3).setWidth 32 = 99#32 ∧
          SeedOk x.f ∧
          (SeedField.sender c ∈ seedFields x.f ∨ SeedField.recv c ∈ seedFields x.f) ∧
          (x.fld.payload ++ x.tail).length < 2 ^ 32)⌝ ∗
      (prostChainAt A0 s0_sp_232 ⟨[], [], none⟩ ∗ (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗
        stackAt sp chainMergeStack) := by
  unfold chainMergeSeedPlacedSpec LibsignalTripleRatchet.withLsCodeRoLoaded chainMergeSeedRawSpec
  dsimp only
  rw [sepConj_comm, recv_payload_append_eq_receiverChains hfld x.tail, hsp,
    pure_sepConj_pure_assoc]

theorem chainMerge_placed_post_eq_receiverChains [LibsignalPlacement]
    (x : MergeFieldGhost) (c : ChainV) (s0_sp_232 sp : BitVec 64)
    (s_pre sf : State) (hfld : x.fld = .recv c) (hsp : s_pre.sp = sp) :
    chainMergeSeedPlacedSpec.post ⟨s0_sp_232, c, x.bufRef, x.slot, x.ptr, x.tail, x.f⟩ s_pre sf ⊢
      ⌜sf.trace = s_pre.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      prostChainAt A0 s0_sp_232 c ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt sp chainMergeStack := by
  unfold chainMergeSeedPlacedSpec LibsignalTripleRatchet.withLsCodeRoLoaded chainMergeSeedRawSpec
  dsimp only
  rw [recv_payload_append_eq_receiverChains hfld x.tail, hsp]
  exact Entails.refl _

/-- Relocatable `[LibsignalPlacement]` proof of `SessionStructure::merge_field` (block `15`,
`lsProg_15 H`) on seed's tag-7 field (`receiver_chains`). -/
theorem mergeFieldSeed7_placed_ok [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hC : DeserializeCalleesPlaced H) (hCh : ChainMergeSeedPlacedOk H) :
    MergeFieldSeedPlacedOk (fun fl => ∃ c, fl = .recv c) H := by
  apply subroutine_ok_of_sepWPp
  intro x Fr s0 hpc hrun hpre hsp
  have ⟨hcrl0, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  refine ⟨_, Fr, hpre_raw, ?_⟩
  conv =>
    arg 4
    dsimp only [mergeFieldSeedRawSpec]
    simp only [sepConj_assoc]
  apply SepWPp.pure_left
  rintro ⟨hx0, hx1, hx2, hx3, hx4, ⟨c, hfld⟩, hSeedOk, hMemFields, -, -, hrecv_imp, hlen⟩
  have hrecv : x.v.recv = [] := hrecv_imp (by rw [hfld])
  have hMemRecv : SeedField.recv c ∈ seedFields x.f := hfld ▸ hMemFields
  rw [hfld] at hx1 hx2
  dsimp only [SeedField.tag, SeedField.wt, CryptoVerification.LibsignalProtoCodec.WireType.toNat,
    BitVec.ofNat_eq_ofNat] at hx1 hx2
  have hx2' : BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x2)) &&& 255#64 = 2#64 :=
    zext64_trunc32_and_255_eq_of_trunc8_receiverChains hx2
  have hsp0 : s0.sp &&& 15#64 = 0#64 := eq_of_beq hsp
  have hsp240 : (s0.sp - 240#64) &&& 15#64 = 0#64 := sp_sub_240_aligned_receiverChains hsp0
  have hsp240_beq : ((s0.sp - 240#64) &&& 15#64 == 0#64) = true := beq_iff_eq.mpr hsp240
  have hCh' := chainMerge_placed_ok_sub_receiverChains hCh
  have h2bc := @step_receiverChains_from_0x2bc_to_ret_placed_receiverChains _ H hC.2.2.2
    (fun fl => ∃ c, fl = .recv c) x c s0
  rw [stackAt_mergeFieldStack_split_receiverChains s0.sp,
    memRegion80_chainInit_eq_cells10_receiverChains s0.sp,
    memRegion80_eq_cells10_receiverChains s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro c0
  apply SepWPp.exists_elim; intro c1
  apply SepWPp.exists_elim; intro c2
  apply SepWPp.exists_elim; intro c3
  apply SepWPp.exists_elim; intro c4
  apply SepWPp.exists_elim; intro c5
  apply SepWPp.exists_elim; intro c6
  apply SepWPp.exists_elim; intro c7
  apply SepWPp.exists_elim; intro c8
  apply SepWPp.exists_elim; intro c9
  apply SepWPp.exists_elim; intro w80
  apply SepWPp.exists_elim; intro w72
  apply SepWPp.exists_elim; intro w64
  apply SepWPp.exists_elim; intro w56
  apply SepWPp.exists_elim; intro w48
  apply SepWPp.exists_elim; intro w40
  apply SepWPp.exists_elim; intro w32
  apply SepWPp.exists_elim; intro w24
  apply SepWPp.exists_elim; intro w16
  apply SepWPp.exists_elim; intro w8
  apply LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 11) hcrl0
  apply sepWP_intro_rodata_tag7_placed_receiverChains hcrl0
  wp_steps
  apply sepWP_drop_left_receiverChains
  apply SepWP.fold (prostChainAt_default_of_cells_lit_receiverChains s0.sp) (by sep_frame)
  apply SepWP.fold (mfSavedRegs_intro_receiverChains s0.sp s0 c3) (by sep_frame)
  apply SepWP.fold (Entails.of_eq (stackAt_sub_to_chainMerge_receiverChains (s0.sp - 240#64))) (by sep_frame)
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) ?_
  intro hcrl1
  refine call_frame_lscro_receiverChains (ret_pc := (blkPl_15).base + 700#64) hcrl1 hCh'
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
    (by simp only [arm64_norm])
    (chainMerge_placed_pre_eq_receiverChains x c (s0.sp - 232#64) (s0.sp - 240#64) _ hfld (by simp only [arm64_norm]))
    ⟨hcrl1, by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm], hSeedOk, Or.inr hMemRecv, hlen⟩
    (by sep_frame)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans_receiverChains (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hcrl2
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx25m, hx26m, hx27m, hx28m, hfpm, hvregsm⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19m hx20m hx21m hx22m hx23m hx24m hx25m hx26m hx27m hx28m hfpm hvregsm
  have hsp_align_m : sm.spAligned = true := by
    simp only [State.spAligned, hspm]
    exact hsp240_beq
  refine SepWPp.fold
    (chainMerge_placed_post_eq_receiverChains x c (s0.sp - 232#64) (s0.sp - 240#64) _ sm hfld ?_) rfl ?_
  · simp only [arm64_norm]
  simp only [sepConj_assoc]
  apply SepWPp.pure_left; rintro ⟨htr_m, hx0_m⟩
  have htr_m' : sm.trace = s0.trace := by simpa only [arm64_norm] using htr_m
  refine SepWPp.weaken_pre ?_
    (h2bc sm Fr c3 hrecv hfld hcrl2 hpcm hrunm hspm hsp_align_m htr_m' hvregsm hx0_m hx20m hx26m hx27m hx28m)
  have hsub16384 : (s0.sp - 240#64) - 16144#64 = s0.sp - 16384#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  exact Entails.of_eq (by rw [hsub16384]; ac_rfl)

end Placed

end CryptoVerification.E2E.Record.DeserializeSeed
