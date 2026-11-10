/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.DeserLoopIterG
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Fields
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
/-!
# `SessionRecord::deserialize` Single-Field Loop Iteration (`+0x254` → `+0x254`)

Verifies one iteration of the `SessionRecord::deserialize` protobuf field-dispatch loop
(`+0x254` → `SessionStructure::merge_field` → `+0x254`) on `SP2Ext` and under relocatable
`[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.DeserLoopIterG

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (CanonRecord CanonSession)
open CryptoVerification.E2E.Record.DeserializeSeed.LoopIterStateSimp
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  keyByte_signExtend_lsb63_loopIterG
  keyByte_signExtend_lsr32_loopIterG
  keyByte_signExtend_and7_ule6_loopIterG
  keyByte_signExtend_tag_w1_loopIterG
  tag_zeroExtend_ofNat32_loopIterG
  tag_ofNat64_beq0_loopIterG
  tag_ofNat64_setWidth32_loopIterG ofNat_succ_sub_one_loopIter

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPC_pre_loopIterG (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_setPC_pre_loopIterG (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPC_pre_loopIterG (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_setPC_pre_loopIterG (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPC_pre_loopIterG (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_setPC_pre_loopIterG (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPC_pre_loopIterG (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_setPC_pre_loopIterG (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

/-! ## Spatial cursor and length helpers -/

theorem fnAddr_mergeField_eq_deser_at (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)} :
    (tripleRatchetProgAt img.base C ctl abs).fnAddr recDeserializeName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) =
      (tripleRatchetProgAt img.base C ctl abs).fnAddr mergeFieldName := by
  dsimp only [tripleRatchetProgAt]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize"), (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")]
  bv_omega

theorem step_254_to_2e8_loopIterG_at (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (L curPtr : BitVec 64) (fl : GenField) (n : Nat) (s : State)
    {post : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr recDeserializeName + 596#64)
    (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = L + 0x710#64)
    (hx20 : s.readReg64 .x20 = 0#64)
    (hx23 : s.readReg64 .x23 = L + 0x408#64)
    (hn : n < 2 ^ 20)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr recDeserializeName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) →
      sm.status = .Running →
      sm.sp = s.sp →
      (sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) →
      sm.readReg64 .lr = (tripleRatchetProgAt img.base C ctl abs).fnAddr recDeserializeName + 748#64 →
      sm.readReg64 .x0 = L + 0x420#64 →
      (sm.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 fl.tag →
      (sm.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 fl.wt.toNat →
      sm.readReg64 .x3 = L + 0x6e8#64 →
      (sm.readReg64 .x4).setWidth 32 = 99#32 →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = 0#64 →
      sm.readReg64 .x23 = L + 0x408#64 →
      sm.readReg64 .x29 = L + 0x710#64 →
      post sm (stepPost_loopIter L curPtr (keyByte_loopIterG fl) n)) :
    SepWP (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr recDeserializeName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize"))) s
      (stepPre_loopIter L curPtr (keyByte_loopIterG fl) n) post := by
  have hule := ule_zero_ofNat_succ_loopIterG hn
  let H := Rust.withPanics (selExt img.base C ctl abs)
  diter_fetches img.base H
  dsimp only [tripleRatchetProgAt] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr recDeserializeName = entry
  examples_hide_fetches
  unfold stepPre_loopIter
  iterate 22 wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  exact hnext _
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]; cases fl <;> simp [keyByte_loopIterG, GenField.tag, GenField.wt, WireType.toNat])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])

theorem step_2ec_loopIter_at (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (s2 : State) {P : SepProp} {post : State → SepProp → Prop}
    (hpc2 : s2.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr recDeserializeName + 748#64)
    (hrun2 : s2.status = .Running)
    (hx0_2 : s2.readReg64 .x0 = 0#64)
    (hnext : ∀ sf : State,
      sf.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr recDeserializeName + 596#64 →
      sf.status = .Running →
      sf.sp = s2.sp →
      (sf.trace = s2.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s2) →
      sf.readReg64 .x19 = s2.readReg64 .x19 →
      sf.readReg64 .x20 = s2.readReg64 .x20 →
      sf.readReg64 .x23 = s2.readReg64 .x23 →
      sf.readReg64 .x29 = s2.readReg64 .x29 →
      post sf P) :
    SepWP (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr recDeserializeName + 596#64) s2 P post := by
  let H := Rust.withPanics (selExt img.base C ctl abs)
  diter_fetches img.base H
  dsimp only [tripleRatchetProgAt] at hpc2 hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr recDeserializeName = entry
  examples_hide_fetches
  wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  exact hnext _
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])

theorem deserLoopIterG_ok_at (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hMF : MergeFieldGenOkAt img C ctl (fun _ => True) abs) (x : DeserializeGenGhost) (R : SepProp)
    (s0 : State) (k : Nat) (s : State) (hr : DeserializeScope x.r) (hk : k < (recFields x.r).length)
    (hs : DeserLoopGAt img C ctl x R s0 k s abs) :
    DeserStepGAt img C ctl x R s0 s (fun s' => DeserLoopGAt img C ctl x R s0 (k + 1) s' abs) abs := by
  obtain ⟨hpc, hrun, htr, hsym, hF, hsp, hal, hx29, hx19, hx20, hx23, hmem⟩ := hs
  let L := deserSpL s0.sp
  let fl := (recFields x.r)[k]
  let rest := ((recFields x.r).drop (k + 1)).flatMap GenField.enc
  let payRest := fl.payload ++ rest
  let curPtr := curPtr_loopIterG x.p x.r k
  have hpc_entry : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr recDeserializeName + 596#64 := hpc
  have hn_lt : payRest.length < 2 ^ 20 := payload_rest_length_lt_loopIterG hr hk
  set F_loop : SepProp :=
    (x.p ↦ₛ preBytes_loopIterG x.r k) ∗
      prostSSGAt A0 (L + 0x420#64) (ssgAfter x.r k) ∗
      ((curPtr + 1#64) ↦ₛ payRest) ∗
      deserFixed_loopIter L ∗ deserOutRegion_loopIter x.out ∗
      deserCalleeUnused_loopIter L ∗ stackAt L mergeFieldStack ∗
      deserSaved s0 ∗ R
  have hmem1 : s.mem ⊨ stepPre_loopIter L curPtr (keyByte_loopIterG fl) payRest.length ∗ F_loop := by
    change s.mem ⊨ deserLocalsG L x.p (encodeRecord x.r) (((recFields x.r).drop k).flatMap GenField.enc)
        (ssgAfter x.r k) ∗
      memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R at hmem
    rw [deserLocalsG_decomp_loopIterG, deserOutRegion_eq_loopIter,
      sliceCursorAfter_split_key_loopIterG L x.p hr hk,
      stackAt_deserCallee_split_loopIter L, sep_perm1_loopIter] at hmem
    exact hmem
  intro hL
  obtain ⟨sm, hsteps1, ⟨-, -, Pm, hmm, hpcm, hrunm, hspm, htrm, hlrm,
      hx0m, hx1m, hx2m, hx3m, hx4m, hx19m, hx20m, hx23m, hx29m, hPm⟩ | ⟨_, _hoom⟩⟩ :=
    (step_254_to_2e8_loopIterG_at img C ctl L curPtr fl payRest.length s
      (post := fun sm Pm =>
        sm.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr recDeserializeName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) ∧
        sm.status = .Running ∧
        sm.sp = s.sp ∧
        (sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        sm.readReg64 .lr = (tripleRatchetProgAt img.base C ctl abs).fnAddr recDeserializeName + 748#64 ∧
        sm.readReg64 .x0 = L + 0x420#64 ∧
        (sm.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 fl.tag ∧
        (sm.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 fl.wt.toNat ∧
        sm.readReg64 .x3 = L + 0x6e8#64 ∧
        (sm.readReg64 .x4).setWidth 32 = 99#32 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = 0#64 ∧
        sm.readReg64 .x23 = L + 0x408#64 ∧
        sm.readReg64 .x29 = L + 0x710#64 ∧
        Pm = stepPost_loopIter L curPtr (keyByte_loopIterG fl) payRest.length)
      hpc_entry hrun hx29 hx20 hx23 hn_lt
      (fun _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 =>
        ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, rfl⟩)).elim hmem1 hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  subst hPm
  have hFm : img.FrozenLoaded sm := hsteps1.frozenLoaded hF
  have hsymm : sm.symtab = img.symtab := hsteps1.symtab_eq.trans hsym
  have hLm : (tripleRatchetProgAt img.base C ctl abs).CodeLoaded sm.mem := hsteps1.codeLoaded hL
  have hspm_L : sm.sp = L := hspm.trans hsp
  have hal_m : sm.spAligned = true := by
    simp only [State.spAligned] at hal ⊢
    rwa [hspm]
  have hcall : subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr recDeserializeName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")))
      (mergeFieldGenSpecAt img (fun _ => True)) := by
    rw [fnAddr_mergeField_eq_deser_at]
    exact hMF
  let g : MergeFieldGenGhost :=
    ⟨L + 0x420#64, ssgAfter x.r k, fl, L + 0x6e8#64, L + 0x3f8#64, curPtr + 1#64, rest⟩
  set F_mf : SepProp :=
    (curPtr ↦₈ keyByte_loopIterG fl) ∗
      (x.p ↦ₛ preBytes_loopIterG x.r k) ∗
      deserFixed_loopIter L ∗ deserOutRegion_loopIter x.out ∗
      deserCalleeUnused_loopIter L ∗ deserSaved s0
  have hok : fl.Ok := recFields_ok x.r hr fl (List.getElem_mem hk)
  have hfresh : fl.Fresh (ssgAfter x.r k) := recFields_fresh x.r hr k hk
  have hpay_lt32 : (fl.payload ++ rest).length < 2 ^ 32 :=
    Nat.lt_trans hn_lt (by decide)
  have hpre_mf : sm.mem ⊨ (mergeFieldGenSpecAt img (fun _ => True)).pre g sm ∗ (F_mf ∗ R) := by
    dsimp only [mergeFieldGenSpecAt, g]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0m, hx1m, hx2m, hx3m, hx4m, trivial, hok, hfresh, hpay_lt32, hFm, hsymm⟩, ?_⟩
    rw [hspm_L]
    unfold Prost.sliceCursorAt
    have ha : L + 0x3f8#64 + 8#64 = L + 0x400#64 := by bv_omega
    rw [ha]
    dsimp only [stepPost_loopIter, F_loop] at hmm
    dsimp only [F_mf]
    rw [← sep_perm2_loopIter]
    exact hmm
  obtain ⟨s2, hsteps2, hout, -⟩ :=
    hcall.no_fault_before_outcome g (F_mf ∗ R) sm hpcm hrunm hpre_mf hal_m hLm
  rcases hout with ⟨⟨hpc2, _, hrun2⟩, ⟨hsp2, hcs2⟩, hpost2⟩ | ⟨hpan2, hpost2⟩ | ⟨code, _, hpost2⟩ | ⟨_hoom_st, _hoom_post⟩
  rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
  · rw [hlrm] at hpc2
    dsimp only [mergeFieldGenSpecAt, g] at hpost2
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost2
    obtain ⟨⟨htr2, hx0_2⟩, hmem2⟩ := hpost2
    have hL2 : (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s2.mem := hsteps2.codeLoaded hLm
    obtain ⟨sf, hsteps3, ⟨-, -, P_f, hmf, hpcf, hrunf, hspf, htrf,
        hx19f, hx20f, hx23f, hx29f, hPf⟩ | ⟨_, _hoom⟩⟩ :=
      (step_2ec_loopIter_at img C ctl s2
        (P := prostSSGAt A0 (L + 0x420#64) ((ssgAfter x.r k).apply fl) ∗
          ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
          Prost.sliceCursorAfter (L + 0x3f8#64) (curPtr + 1#64) payRest rest ∗
          stackAt sm.sp mergeFieldStack)
        (post := fun sf P_f =>
          sf.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr recDeserializeName + 596#64 ∧
          sf.status = .Running ∧
          sf.sp = s2.sp ∧
          (sf.trace = s2.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s2) ∧
          sf.readReg64 .x19 = s2.readReg64 .x19 ∧
          sf.readReg64 .x20 = s2.readReg64 .x20 ∧
          sf.readReg64 .x23 = s2.readReg64 .x23 ∧
          sf.readReg64 .x29 = s2.readReg64 .x29 ∧
          P_f = (prostSSGAt A0 (L + 0x420#64) ((ssgAfter x.r k).apply fl) ∗
            ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
            Prost.sliceCursorAfter (L + 0x3f8#64) (curPtr + 1#64) payRest rest ∗
            stackAt sm.sp mergeFieldStack))
        hpc2 hrun2 hx0_2
        (fun _ h1 h2 h3 h4 h5 h6 h7 h8 => ⟨h1, h2, h3, h4, h5, h6, h7, h8, rfl⟩)).elim hmem2 hL2
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    subst hPf
    have hsteps_all : Steps (tripleRatchetProgAt img.base C ctl abs) s sf := (hsteps1.trans hsteps2).trans hsteps3
    have hsp_sf : sf.sp = L := hspf.trans (hsp2.trans hspm_L)
    have hsp_s : sf.sp = s.sp := hsp_sf.trans hsp.symm
    have hal_sf : sf.spAligned = true := by
      simp only [State.spAligned] at hal ⊢
      rwa [hsp_s]
    refine ⟨sf, hsteps_all, Or.inl ?_⟩
    refine ⟨hpcf, hrunf,
      htrf.1.trans (htr2.trans (htrm.1.trans htr)),
      hsteps_all.symtab_eq.trans hsym, hsteps_all.frozenLoaded hF,
      hsp_sf, hal_sf,
      by reg_chain,
      by reg_chain,
      by reg_chain,
      by reg_chain, ?_⟩
    · change sf.mem ⊨ deserLocalsG L x.p (encodeRecord x.r)
          (((recFields x.r).drop (k + 1)).flatMap GenField.enc) (ssgAfter x.r (k + 1)) ∗
        memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R
      rw [deserLocalsG_decomp_loopIterG, deserOutRegion_eq_loopIter,
        ssgAfter_succ_loopIterG hk, ← sliceCursorAfter_unsplit_key_loopIterG L x.p hr hk,
        stackAt_deserCallee_split_loopIter L, ← sep_perm3_loopIter]
      rw [hspm_L] at hmf
      exact hmf
  · have hsteps_all : Steps (tripleRatchetProgAt img.base C ctl abs) s s2 := hsteps1.trans hsteps2
    refine ⟨s2, hsteps_all, Or.inr ⟨hpan2, ?_⟩⟩
    dsimp only [mergeFieldGenSpecAt, deserializeGenSpecAt, Serialization.allocPanic] at hpost2 ⊢
    rw [← sepConj_assoc] at hpost2
    refine allowPanic_frame (fun ⟨ha, hp⟩ => ?_) hpost2
    rw [allocFailedIn, htrm.1, htr] at ha
    rw [htrm.1, htr] at hp
    exact ⟨ha, hp⟩
  · exact (not_satisfies_false_sepConj hpost2).elim

theorem fnAddr_mergeField_eq_deser_at_ext (img : Obj.Image)
    (ext : String → Option (State → State)) :
    (SP2Ext img.base ext).fnAddr recDeserializeName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) =
      (SP2Ext img.base ext).fnAddr mergeFieldName := by
  dsimp only [SP2Ext, contractProg]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize"), (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")]
  bv_omega

theorem step_254_to_2e8_loopIterG_at_ext (img : Obj.Image)
    (ext : String → Option (State → State))
    (L curPtr : BitVec 64) (fl : GenField) (n : Nat) (s : State)
    {post : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 596#64)
    (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = L + 0x710#64)
    (hx20 : s.readReg64 .x20 = 0#64)
    (hx23 : s.readReg64 .x23 = L + 0x408#64)
    (hn : n < 2 ^ 20)
    (hnext : ∀ sm : State,
      sm.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) →
      sm.status = .Running →
      sm.sp = s.sp →
      (sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) →
      sm.readReg64 .lr = (SP2Ext img.base ext).fnAddr recDeserializeName + 748#64 →
      sm.readReg64 .x0 = L + 0x420#64 →
      (sm.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 fl.tag →
      (sm.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 fl.wt.toNat →
      sm.readReg64 .x3 = L + 0x6e8#64 →
      (sm.readReg64 .x4).setWidth 32 = 99#32 →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = 0#64 →
      sm.readReg64 .x23 = L + 0x408#64 →
      sm.readReg64 .x29 = L + 0x710#64 →
      post sm (stepPost_loopIter L curPtr (keyByte_loopIterG fl) n)) :
    SepWP (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize"))) s
      (stepPre_loopIter L curPtr (keyByte_loopIterG fl) n) post := by
  have hule := ule_zero_ofNat_succ_loopIterG hn
  let H := Rust.withPanics ext
  diter_fetches img.base H
  dsimp only [SP2Ext, contractProg] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr recDeserializeName = entry
  examples_hide_fetches
  unfold stepPre_loopIter
  iterate 22 wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  exact hnext _
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]; cases fl <;> simp [keyByte_loopIterG, GenField.tag, GenField.wt, WireType.toNat])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])

theorem step_2ec_loopIter_at_ext (img : Obj.Image)
    (ext : String → Option (State → State))
    (s2 : State) {P : SepProp} {post : State → SepProp → Prop}
    (hpc2 : s2.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 748#64)
    (hrun2 : s2.status = .Running)
    (hx0_2 : s2.readReg64 .x0 = 0#64)
    (hnext : ∀ sf : State,
      sf.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 596#64 →
      sf.status = .Running →
      sf.sp = s2.sp →
      (sf.trace = s2.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s2) →
      sf.readReg64 .x19 = s2.readReg64 .x19 →
      sf.readReg64 .x20 = s2.readReg64 .x20 →
      sf.readReg64 .x23 = s2.readReg64 .x23 →
      sf.readReg64 .x29 = s2.readReg64 .x29 →
      post sf P) :
    SepWP (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName + 596#64) s2 P post := by
  let H := Rust.withPanics ext
  diter_fetches img.base H
  dsimp only [SP2Ext, contractProg] at hpc2 hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr recDeserializeName = entry
  examples_hide_fetches
  wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  exact hnext _
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])

@[irreducible] def deserCalleeUnused_loopIterW (L : BitVec 64) : SepProp :=
  memRegion (L - 63632#64) 30864

theorem stackAt_deserCallee_split_loopIterW (L : BitVec 64) :
    stackAt L deserCalleeStack =
      deserCalleeUnused_loopIterW L ∗ stackAt L mergeFieldStackX := by
  unfold stackAt deserCalleeUnused_loopIterW deserCalleeStack recDeserializeStack
    mergeFieldStackX mergeFieldStack
  have hsplit := memRegion_split (L - 63632#64) 30864 32768 (by decide)
  have ha : L - 63632#64 + 30864#64 = L - 32768#64 := by bv_omega
  rw [show (65536 - 0x770 : Nat) = 30864 + (0x4000 + 16384) by rfl,
    show BitVec.ofNat 64 (30864 + (0x4000 + 16384)) = 63632#64 by rfl,
    show BitVec.ofNat 64 (0x4000 + 16384) = 32768#64 by rfl, hsplit, ha]

theorem deserLoopIterG_ok_atW (img : Obj.Image)
    (ext : String → Option (State → State))
    (hMF : MergeFieldGenOkAtW img ext (fun _ => True)) (x : DeserializeGenGhost) (R : SepProp)
    (s0 : State) (k : Nat) (s : State) (hr : DeserializeScope x.r) (hk : k < (recFields x.r).length)
    (hs : DeserLoopGAtW img ext x R s0 k s) :
    DeserStepGAtW img ext x R s0 s (fun s' => DeserLoopGAtW img ext x R s0 (k + 1) s') := by
  obtain ⟨hpc, hrun, htr, hsym, hF, hsp, hal, hx29, hx19, hx20, hx23, hmem⟩ := hs
  let L := deserSpL s0.sp
  let fl := (recFields x.r)[k]
  let rest := ((recFields x.r).drop (k + 1)).flatMap GenField.enc
  let payRest := fl.payload ++ rest
  let curPtr := curPtr_loopIterG x.p x.r k
  have hpc_entry : s.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 596#64 := hpc
  have hn_lt : payRest.length < 2 ^ 20 := payload_rest_length_lt_loopIterG hr hk
  set F_loop : SepProp :=
    (x.p ↦ₛ preBytes_loopIterG x.r k) ∗
      prostSSGAt A0 (L + 0x420#64) (ssgAfter x.r k) ∗
      ((curPtr + 1#64) ↦ₛ payRest) ∗
      deserFixed_loopIter L ∗ deserOutRegion_loopIter x.out ∗
      deserCalleeUnused_loopIterW L ∗ stackAt L mergeFieldStackX ∗
      deserSaved s0 ∗ R
  have hmem1 : s.mem ⊨ stepPre_loopIter L curPtr (keyByte_loopIterG fl) payRest.length ∗ F_loop := by
    change s.mem ⊨ deserLocalsG L x.p (encodeRecord x.r) (((recFields x.r).drop k).flatMap GenField.enc)
        (ssgAfter x.r k) ∗
      memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R at hmem
    rw [deserLocalsG_decomp_loopIterG, deserOutRegion_eq_loopIter,
      sliceCursorAfter_split_key_loopIterG L x.p hr hk,
      stackAt_deserCallee_split_loopIterW L, sep_perm1_loopIter] at hmem
    exact hmem
  intro hL
  obtain ⟨sm, hsteps1, ⟨-, -, Pm, hmm, hpcm, hrunm, hspm, htrm, hlrm,
      hx0m, hx1m, hx2m, hx3m, hx4m, hx19m, hx20m, hx23m, hx29m, hPm⟩ | ⟨_, _hoom⟩⟩ :=
    (step_254_to_2e8_loopIterG_at_ext img ext L curPtr fl payRest.length s
      (post := fun sm Pm =>
        sm.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) ∧
        sm.status = .Running ∧
        sm.sp = s.sp ∧
        (sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        sm.readReg64 .lr = (SP2Ext img.base ext).fnAddr recDeserializeName + 748#64 ∧
        sm.readReg64 .x0 = L + 0x420#64 ∧
        (sm.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 fl.tag ∧
        (sm.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 fl.wt.toNat ∧
        sm.readReg64 .x3 = L + 0x6e8#64 ∧
        (sm.readReg64 .x4).setWidth 32 = 99#32 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = 0#64 ∧
        sm.readReg64 .x23 = L + 0x408#64 ∧
        sm.readReg64 .x29 = L + 0x710#64 ∧
        Pm = stepPost_loopIter L curPtr (keyByte_loopIterG fl) payRest.length)
      hpc_entry hrun hx29 hx20 hx23 hn_lt
      (fun _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 =>
        ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, rfl⟩)).elim hmem1 hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  subst hPm
  have hFm : img.FrozenLoaded sm := hsteps1.frozenLoaded hF
  have hsymm : sm.symtab = img.symtab := hsteps1.symtab_eq.trans hsym
  have hLm : (SP2Ext img.base ext).CodeLoaded sm.mem := hsteps1.codeLoaded hL
  have hspm_L : sm.sp = L := hspm.trans hsp
  have hal_m : sm.spAligned = true := by
    simp only [State.spAligned] at hal ⊢
    rwa [hspm]
  have hcall : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")))
      (mergeFieldGenSpecAtW img (fun _ => True)) := by
    rw [fnAddr_mergeField_eq_deser_at_ext]
    exact hMF
  let g : MergeFieldGenGhost :=
    ⟨L + 0x420#64, ssgAfter x.r k, fl, L + 0x6e8#64, L + 0x3f8#64, curPtr + 1#64, rest⟩
  set F_mf : SepProp :=
    (curPtr ↦₈ keyByte_loopIterG fl) ∗
      (x.p ↦ₛ preBytes_loopIterG x.r k) ∗
      deserFixed_loopIter L ∗ deserOutRegion_loopIter x.out ∗
      deserCalleeUnused_loopIterW L ∗ deserSaved s0
  have hok : fl.Ok := recFields_ok x.r hr fl (List.getElem_mem hk)
  have hfresh : fl.Fresh (ssgAfter x.r k) := recFields_fresh x.r hr k hk
  have hpay_lt62 : (fl.payload ++ rest).length < 2 ^ 62 :=
    Nat.lt_trans hn_lt (by decide)
  have hpre_mf : sm.mem ⊨ (mergeFieldGenSpecAtW img (fun _ => True)).pre g sm ∗ (F_mf ∗ R) := by
    dsimp only [mergeFieldGenSpecAtW, g]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0m, hx1m, hx2m, hx3m, hx4m, trivial, hok, hfresh, hpay_lt62, hFm, hsymm⟩, ?_⟩
    rw [hspm_L]
    unfold Prost.sliceCursorAt
    have ha : L + 0x3f8#64 + 8#64 = L + 0x400#64 := by bv_omega
    rw [ha]
    dsimp only [stepPost_loopIter, F_loop] at hmm
    dsimp only [F_mf]
    rw [← sep_perm2_loopIter]
    exact hmm
  obtain ⟨s2, hsteps2, hout, -⟩ :=
    hcall.no_fault_before_outcome g (F_mf ∗ R) sm hpcm hrunm hpre_mf hal_m hLm
  rcases hout with ⟨⟨hpc2, _, hrun2⟩, ⟨hsp2, hcs2⟩, hpost2⟩ | ⟨hpan2, hpost2⟩ | ⟨code, _, hpost2⟩ | ⟨_hoom_st, _hoom_post⟩
  rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
  · rw [hlrm] at hpc2
    dsimp only [mergeFieldGenSpecAtW, g] at hpost2
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost2
    obtain ⟨⟨htr2, hx0_2⟩, hmem2⟩ := hpost2
    have hL2 : (SP2Ext img.base ext).CodeLoaded s2.mem := hsteps2.codeLoaded hLm
    obtain ⟨sf, hsteps3, ⟨-, -, P_f, hmf, hpcf, hrunf, hspf, htrf,
        hx19f, hx20f, hx23f, hx29f, hPf⟩ | ⟨_, _hoom⟩⟩ :=
      (step_2ec_loopIter_at_ext img ext s2
        (P := prostSSGAt A0 (L + 0x420#64) ((ssgAfter x.r k).apply fl) ∗
          ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
          Prost.sliceCursorAfter (L + 0x3f8#64) (curPtr + 1#64) payRest rest ∗
          stackAt sm.sp mergeFieldStackX)
        (post := fun sf P_f =>
          sf.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 596#64 ∧
          sf.status = .Running ∧
          sf.sp = s2.sp ∧
          (sf.trace = s2.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s2) ∧
          sf.readReg64 .x19 = s2.readReg64 .x19 ∧
          sf.readReg64 .x20 = s2.readReg64 .x20 ∧
          sf.readReg64 .x23 = s2.readReg64 .x23 ∧
          sf.readReg64 .x29 = s2.readReg64 .x29 ∧
          P_f = (prostSSGAt A0 (L + 0x420#64) ((ssgAfter x.r k).apply fl) ∗
            ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
            Prost.sliceCursorAfter (L + 0x3f8#64) (curPtr + 1#64) payRest rest ∗
            stackAt sm.sp mergeFieldStackX))
        hpc2 hrun2 hx0_2
        (fun _ h1 h2 h3 h4 h5 h6 h7 h8 => ⟨h1, h2, h3, h4, h5, h6, h7, h8, rfl⟩)).elim hmem2 hL2
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    subst hPf
    have hsteps_all : Steps (SP2Ext img.base ext) s sf := (hsteps1.trans hsteps2).trans hsteps3
    have hsp_sf : sf.sp = L := hspf.trans (hsp2.trans hspm_L)
    have hsp_s : sf.sp = s.sp := hsp_sf.trans hsp.symm
    have hal_sf : sf.spAligned = true := by
      simp only [State.spAligned] at hal ⊢
      rwa [hsp_s]
    refine ⟨sf, hsteps_all, Or.inl ?_⟩
    refine ⟨hpcf, hrunf,
      ⟨htrf.1.trans (htr2.trans (htrm.1.trans htr.1)),
       htrf.2.trans (hcs2.2.2.2.2.2.2.2.2.2.2.2.trans (htrm.2.trans htr.2))⟩,
      hsteps_all.symtab_eq.trans hsym, hsteps_all.frozenLoaded hF,
      hsp_sf, hal_sf,
      by reg_chain,
      by reg_chain,
      by reg_chain,
      by reg_chain, ?_⟩
    · change sf.mem ⊨ deserLocalsG L x.p (encodeRecord x.r)
          (((recFields x.r).drop (k + 1)).flatMap GenField.enc) (ssgAfter x.r (k + 1)) ∗
        memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R
      rw [deserLocalsG_decomp_loopIterG, deserOutRegion_eq_loopIter,
        ssgAfter_succ_loopIterG hk, ← sliceCursorAfter_unsplit_key_loopIterG L x.p hr hk,
        stackAt_deserCallee_split_loopIterW L, ← sep_perm3_loopIter]
      rw [hspm_L] at hmf
      exact hmf
  · have hsteps_all : Steps (SP2Ext img.base ext) s s2 := hsteps1.trans hsteps2
    refine ⟨s2, hsteps_all, Or.inr ⟨hpan2, ?_⟩⟩
    dsimp only [mergeFieldGenSpecAtW, deserializeGenSpecAt, Serialization.allocPanic] at hpost2 ⊢
    rw [← sepConj_assoc] at hpost2
    refine allowPanic_frame (fun ⟨ha, hp⟩ => ?_) hpost2
    rw [allocFailedIn, htrm.1, htr.1] at ha
    rw [htrm.1, htr.1] at hp
    exact ⟨ha, hp⟩
  · exact (not_satisfies_false_sepConj hpost2).elim

private theorem deserLocalsGA_decomp_loopIterG (A : RustAlloc) (L p : BitVec 64)
    (bs rest : List (BitVec 8)) (v : SSG) :
    deserLocalsGA A L p bs rest v =
      Prost.sliceCursorAfter (L + 0x3f8#64) p bs rest ∗
      prostSSGAt A (L + 0x420#64) v ∗
      ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
      deserFixed_loopIter L := by
  unfold deserLocalsGA deserFixed_loopIter
  generalize memRegion L 0x3f8 = m1
  generalize memRegion (L + 0x578#64) 0x170 = m2
  generalize memRegion (L + 0x6f0#64) 0x20 = m3
  ac_rfl

private theorem pool_stackAt_deserCallee_split_loopIterWA (A : RustAlloc) (L : BitVec 64)
    (rest : SepProp) :
    A.pool ∗ stackAt L deserCalleeStack ∗ rest =
      (deserCalleeUnused_loopIterW L ∗ (A.pool ∗ stackAt L mergeFieldStackX)) ∗ rest := by
  rw [stackAt_deserCallee_split_loopIterW L]
  ac_rfl

theorem deserLoopIterG_ok_atWA (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hMF : MergeFieldGenOkAtWA img A ext (fun _ => True)) (x : DeserializeGenGhost) (R : SepProp)
    (s0 : State) (k : Nat) (s : State) (hr : DeserializeScope x.r) (hk : k < (recFields x.r).length)
    (hs : DeserLoopGAtWA img A ext x R s0 k s) :
    DeserStepGAtWA img A ext x R s0 s (DeserLoopGAtWA img A ext x R s0 (k + 1)) := by
  obtain ⟨hpc, hrun, htr, hsym, hF, hsp, hal, hx29, hx19, hx20, hx23, hmem⟩ := hs
  let L := deserSpL s0.sp
  let fl := (recFields x.r)[k]
  let rest := ((recFields x.r).drop (k + 1)).flatMap GenField.enc
  let payRest := fl.payload ++ rest
  let curPtr := curPtr_loopIterG x.p x.r k
  have hpc_entry : s.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 596#64 := hpc
  have hn_lt : payRest.length < 2 ^ 20 := payload_rest_length_lt_loopIterG hr hk
  set F_loop : SepProp :=
    (x.p ↦ₛ preBytes_loopIterG x.r k) ∗
      prostSSGAt A (L + 0x420#64) (ssgAfter x.r k) ∗
      ((curPtr + 1#64) ↦ₛ payRest) ∗
      deserFixed_loopIter L ∗ deserOutRegion_loopIter x.out ∗
      deserCalleeUnused_loopIterW L ∗ (A.pool ∗ stackAt L mergeFieldStackX) ∗
      deserSaved s0 ∗ R
  have hmem1 : s.mem ⊨ stepPre_loopIter L curPtr (keyByte_loopIterG fl) payRest.length ∗ F_loop := by
    change s.mem ⊨ deserLocalsGA A L x.p (encodeRecord x.r) (((recFields x.r).drop k).flatMap GenField.enc)
        (ssgAfter x.r k) ∗
      memRegion x.out 368 ∗ A.pool ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R at hmem
    rw [deserLocalsGA_decomp_loopIterG, deserOutRegion_eq_loopIter,
      sliceCursorAfter_split_key_loopIterG L x.p hr hk,
      pool_stackAt_deserCallee_split_loopIterWA A L, sep_perm1_loopIter] at hmem
    exact hmem
  intro hL
  obtain ⟨sm, hsteps1, ⟨-, -, Pm, hmm, hpcm, hrunm, hspm, htrm, hlrm,
      hx0m, hx1m, hx2m, hx3m, hx4m, hx19m, hx20m, hx23m, hx29m, hPm⟩ | ⟨_, _hoom⟩⟩ :=
    (step_254_to_2e8_loopIterG_at_ext img ext L curPtr fl payRest.length s
      (post := fun sm Pm =>
        sm.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) ∧
        sm.status = .Running ∧
        sm.sp = s.sp ∧
        (sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        sm.readReg64 .lr = (SP2Ext img.base ext).fnAddr recDeserializeName + 748#64 ∧
        sm.readReg64 .x0 = L + 0x420#64 ∧
        (sm.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 fl.tag ∧
        (sm.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 fl.wt.toNat ∧
        sm.readReg64 .x3 = L + 0x6e8#64 ∧
        (sm.readReg64 .x4).setWidth 32 = 99#32 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = 0#64 ∧
        sm.readReg64 .x23 = L + 0x408#64 ∧
        sm.readReg64 .x29 = L + 0x710#64 ∧
        Pm = stepPost_loopIter L curPtr (keyByte_loopIterG fl) payRest.length)
      hpc_entry hrun hx29 hx20 hx23 hn_lt
      (fun _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 =>
        ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, rfl⟩)).elim hmem1 hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  subst hPm
  have hFm : img.FrozenLoaded sm := hsteps1.frozenLoaded hF
  have hsymm : sm.symtab = img.symtab := hsteps1.symtab_eq.trans hsym
  have hLm : (SP2Ext img.base ext).CodeLoaded sm.mem := hsteps1.codeLoaded hL
  have hspm_L : sm.sp = L := hspm.trans hsp
  have hal_m : sm.spAligned = true := by
    simp only [State.spAligned] at hal ⊢
    rwa [hspm]
  have hcall : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")))
      (mergeFieldGenSpecAtWA A img (fun _ => True)) := by
    rw [fnAddr_mergeField_eq_deser_at_ext]
    exact hMF
  let g : MergeFieldGenGhost :=
    ⟨L + 0x420#64, ssgAfter x.r k, fl, L + 0x6e8#64, L + 0x3f8#64, curPtr + 1#64, rest⟩
  set F_mf : SepProp :=
    (curPtr ↦₈ keyByte_loopIterG fl) ∗
      (x.p ↦ₛ preBytes_loopIterG x.r k) ∗
      deserFixed_loopIter L ∗ deserOutRegion_loopIter x.out ∗
      deserCalleeUnused_loopIterW L ∗ deserSaved s0
  have hok : fl.Ok := recFields_ok x.r hr fl (List.getElem_mem hk)
  have hfresh : fl.Fresh (ssgAfter x.r k) := recFields_fresh x.r hr k hk
  have hpay_lt62 : (fl.payload ++ rest).length < 2 ^ 62 :=
    Nat.lt_trans hn_lt (by decide)
  have hpre_mf : sm.mem ⊨ (mergeFieldGenSpecAtWA A img (fun _ => True)).pre g sm ∗ (F_mf ∗ R) := by
    dsimp only [mergeFieldGenSpecAtWA, g]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0m, hx1m, hx2m, hx3m, hx4m, trivial, hok, hfresh, hpay_lt62, hFm, hsymm⟩, ?_⟩
    rw [hspm_L]
    unfold Prost.sliceCursorAt
    have ha : L + 0x3f8#64 + 8#64 = L + 0x400#64 := by bv_omega
    rw [ha]
    dsimp only [stepPost_loopIter, F_loop] at hmm
    dsimp only [F_mf]
    rw [← sep_perm2_loopIter]
    exact hmm
  obtain ⟨s2, hsteps2, hout, -⟩ :=
    hcall.no_fault_before_outcome g (F_mf ∗ R) sm hpcm hrunm hpre_mf hal_m hLm
  rcases hout with ⟨⟨hpc2, _, hrun2⟩, ⟨hsp2, hcs2⟩, hpost2⟩ | ⟨hpan2, hpost2⟩ | ⟨code, _, hpost2⟩ | ⟨_hoom_st, _hoom_post⟩
  rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
  · rw [hlrm] at hpc2
    dsimp only [mergeFieldGenSpecAtWA, g] at hpost2
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost2
    obtain ⟨⟨htr2, hx0_2⟩, hmem2⟩ := hpost2
    have hL2 : (SP2Ext img.base ext).CodeLoaded s2.mem := hsteps2.codeLoaded hLm
    obtain ⟨sf, hsteps3, ⟨-, -, P_f, hmf, hpcf, hrunf, hspf, htrf,
        hx19f, hx20f, hx23f, hx29f, hPf⟩ | ⟨_, _hoom⟩⟩ :=
      (step_2ec_loopIter_at_ext img ext s2
        (P := prostSSGAt A (L + 0x420#64) ((ssgAfter x.r k).apply fl) ∗
          ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
          Prost.sliceCursorAfter (L + 0x3f8#64) (curPtr + 1#64) payRest rest ∗
          (A.pool ∗ stackAt sm.sp mergeFieldStackX))
        (post := fun sf P_f =>
          sf.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 596#64 ∧
          sf.status = .Running ∧
          sf.sp = s2.sp ∧
          (sf.trace = s2.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s2) ∧
          sf.readReg64 .x19 = s2.readReg64 .x19 ∧
          sf.readReg64 .x20 = s2.readReg64 .x20 ∧
          sf.readReg64 .x23 = s2.readReg64 .x23 ∧
          sf.readReg64 .x29 = s2.readReg64 .x29 ∧
          P_f = (prostSSGAt A (L + 0x420#64) ((ssgAfter x.r k).apply fl) ∗
            ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
            Prost.sliceCursorAfter (L + 0x3f8#64) (curPtr + 1#64) payRest rest ∗
            (A.pool ∗ stackAt sm.sp mergeFieldStackX)))
        hpc2 hrun2 hx0_2
        (fun _ h1 h2 h3 h4 h5 h6 h7 h8 => ⟨h1, h2, h3, h4, h5, h6, h7, h8, rfl⟩)).elim hmem2 hL2
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    subst hPf
    have hsteps_all : Steps (SP2Ext img.base ext) s sf := (hsteps1.trans hsteps2).trans hsteps3
    have hsp_sf : sf.sp = L := hspf.trans (hsp2.trans hspm_L)
    have hsp_s : sf.sp = s.sp := hsp_sf.trans hsp.symm
    have hal_sf : sf.spAligned = true := by
      simp only [State.spAligned] at hal ⊢
      rwa [hsp_s]
    refine ⟨sf, hsteps_all, Or.inl ?_⟩
    refine ⟨hpcf, hrunf,
      ⟨htrf.1.trans (htr2.trans (htrm.1.trans htr.1)),
       htrf.2.trans (hcs2.2.2.2.2.2.2.2.2.2.2.2.trans (htrm.2.trans htr.2))⟩,
      hsteps_all.symtab_eq.trans hsym, hsteps_all.frozenLoaded hF,
      hsp_sf, hal_sf,
      by reg_chain,
      by reg_chain,
      by reg_chain,
      by reg_chain, ?_⟩
    · change sf.mem ⊨ deserLocalsGA A L x.p (encodeRecord x.r)
          (((recFields x.r).drop (k + 1)).flatMap GenField.enc) (ssgAfter x.r (k + 1)) ∗
        memRegion x.out 368 ∗ A.pool ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R
      rw [deserLocalsGA_decomp_loopIterG, deserOutRegion_eq_loopIter,
        ssgAfter_succ_loopIterG hk, ← sliceCursorAfter_unsplit_key_loopIterG L x.p hr hk,
        pool_stackAt_deserCallee_split_loopIterWA A L, ← sep_perm3_loopIter]
      rw [hspm_L] at hmf
      exact hmf
  · have hsteps_all : Steps (SP2Ext img.base ext) s s2 := hsteps1.trans hsteps2
    refine ⟨s2, hsteps_all, Or.inr ⟨hpan2, ?_⟩⟩
    dsimp only [mergeFieldGenSpecAtWA, deserializeGenSpecAtA, Serialization.allocPanic] at hpost2 ⊢
    rw [← sepConj_assoc] at hpost2
    refine allowPanic_frame (fun ⟨ha, hp⟩ => ?_) hpost2
    rw [allocFailedIn, htrm.1, htr.1] at ha
    rw [htrm.1, htr.1] at hp
    exact ⟨ha, hp⟩
  · exact (not_satisfies_false_sepConj hpost2).elim

/-! ## Relocatable `[LibsignalPlacement]` loop iteration -/

section Placed

open Arm64.Obj CryptoVerification.E2E.Record.Placed

theorem L1_DeserLoopIterGExt_Placed : True := trivial

theorem ule_zero_ofNat_succ_placed_loopIterG {n : Nat} (hn : n < 2 ^ 62) :
    (BitVec.ofNat 64 (n + 1)).ule 0#64 = false := by
  rw [BitVec.ule_eq_decide, decide_eq_false_iff_not, BitVec.toNat_ofNat, BitVec.toNat_zero,
    Nat.mod_eq_of_lt (by omega : n + 1 < 2 ^ 64)]
  omega

private def kbNormOk (i : Fin 128) : Bool :=
  let kb : BitVec 8 := BitVec.ofNat 8 i.val
  let t : Nat := i.val / 8
  let w : Nat := i.val % 8
  !(decide (0 < t) && decide (w < 6)) ||
    (((BitVec.signExtend 64 kb).getLsbD 63 == false) &&
     ((BitVec.signExtend 64 kb) >>> 32 == 0#64) &&
     ((6#64).ule (BitVec.signExtend 64 kb &&& 7#64) == false) &&
     (BitVec.zeroExtend 64
        (BitVec.truncate 32
          (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 kb)) >>> 3)) ==
        BitVec.ofNat 64 t) &&
     (BitVec.zeroExtend 64 (BitVec.ofNat 32 t) == BitVec.ofNat 64 t) &&
     ((BitVec.ofNat 64 t == 0#64) == false) &&
     ((BitVec.ofNat 64 t).setWidth 32 == BitVec.ofNat 32 t) &&
     ((BitVec.signExtend 64 kb &&& 7#64).setWidth 8 == BitVec.ofNat 8 w) &&
     ((kb &&& 7#8) == BitVec.ofNat 8 w))

private theorem kbNormOk_all : (List.finRange 128).all kbNormOk = true := by decide

private theorem kb_norm_props {kb : BitVec 8}
    (hkb : kb.toNat < 128) (htag : 0 < kb.toNat / 8) (hwt : kb.toNat % 8 < 6) :
    (BitVec.signExtend 64 kb).getLsbD 63 = false ∧
    (BitVec.signExtend 64 kb) >>> 32 = 0#64 ∧
    (6#64).ule (BitVec.signExtend 64 kb &&& 7#64) = false ∧
    BitVec.zeroExtend 64
      (BitVec.truncate 32
        (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 kb)) >>> 3)) =
      BitVec.ofNat 64 (kb.toNat / 8) ∧
    BitVec.zeroExtend 64 (BitVec.ofNat 32 (kb.toNat / 8)) = BitVec.ofNat 64 (kb.toNat / 8) ∧
    (BitVec.ofNat 64 (kb.toNat / 8) == 0#64) = false ∧
    (BitVec.ofNat 64 (kb.toNat / 8)).setWidth 32 = BitVec.ofNat 32 (kb.toNat / 8) ∧
    (BitVec.signExtend 64 kb &&& 7#64).setWidth 8 = BitVec.ofNat 8 (kb.toNat % 8) ∧
    (kb &&& 7#8) = BitVec.ofNat 8 (kb.toNat % 8) := by
  have hi := List.all_eq_true.mp kbNormOk_all ⟨kb.toNat, hkb⟩ (List.mem_finRange _)
  have hkb_eq : BitVec.ofNat 8 kb.toNat = kb := by apply BitVec.eq_of_toNat_eq; simp
  dsimp only [kbNormOk] at hi
  rw [hkb_eq] at hi
  simp only [htag, hwt, decide_true, Bool.and_self, Bool.not_true, Bool.false_or,
    Bool.and_eq_true, beq_iff_eq] at hi
  rcases hi with ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- Relocatable `SessionRecord::deserialize` inner-loop key-byte decode and call setup
(`+0x254` → `BL merge_field` at `lsmpl.base 15`) on `lsProg_46 H` for a single-byte protobuf key
`kb : BitVec 8` (`kb.toNat < 128`, `0 < kb.toNat / 8`, `kb.toNat % 8 < 6`) and remaining byte count
`n < 2 ^ 62`. -/
theorem step_254_to_2e8_placed_loopIter_kb [LibsignalPlacement]
    {H : LibsignalHooks}
    (L curPtr : BitVec 64) (kb : BitVec 8) (n : Nat) (s : State)
    {post : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_46).base + 596#64)
    (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = L + 0x710#64)
    (hx20 : s.readReg64 .x20 = 0#64)
    (hx23 : s.readReg64 .x23 = L + 0x408#64)
    (hkb : kb.toNat < 128)
    (htag : 0 < kb.toNat / 8)
    (hwt : kb.toNat % 8 < 6)
    (hn : n < 2 ^ 62)
    (hnext : ∀ sm : State,
      sm.pc = lsmpl.base 15 →
      sm.status = .Running →
      sm.sp = s.sp →
      (sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) →
      sm.readReg64 .lr = (blkPl_46).base + 748#64 →
      sm.readReg64 .x0 = L + 0x420#64 →
      (sm.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 (kb.toNat / 8) →
      (sm.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 (kb.toNat % 8) →
      sm.readReg64 .x3 = L + 0x6e8#64 →
      (sm.readReg64 .x4).setWidth 32 = 99#32 →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = 0#64 →
      sm.readReg64 .x23 = L + 0x408#64 →
      sm.readReg64 .x29 = L + 0x710#64 →
      post sm (stepPost_loopIter L curPtr kb n)) :
    SepWP (lsProg_46 H) (lsmpl.base 15) s
      (stepPre_loopIter L curPtr kb n) post := by
  have hule := ule_zero_ofNat_succ_placed_loopIterG hn
  obtain ⟨hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8, hk9⟩ := kb_norm_props hkb htag hwt
  unfold stepPre_loopIter
  iterate 22 wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  exact hnext _
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])

private theorem keyByte_loopIterG_bounds (fl : GenField) :
    (keyByte_loopIterG fl).toNat < 128 ∧
    0 < (keyByte_loopIterG fl).toNat / 8 ∧
    (keyByte_loopIterG fl).toNat % 8 < 6 ∧
    (keyByte_loopIterG fl).toNat / 8 = fl.tag ∧
    (keyByte_loopIterG fl).toNat % 8 = fl.wt.toNat := by
  cases fl <;> simp [keyByte_loopIterG, GenField.tag, GenField.wt, WireType.toNat]

/-- Relocatable `SessionRecord::deserialize` single-field loop iteration (`+0x254` → `+0x254`) on
`lsProg_46 H`. -/
theorem deserLoopIterG_placed_okW [LibsignalPlacement]
    (H : LibsignalHooks)
    (hMF : MergeFieldGenPlacedOkW H (fun _ => True)) (x : DeserializeGenGhost) (R : SepProp)
    (s0 : State) (k : Nat) (s : State) (hr : DeserializeScope x.r) (hk : k < (recFields x.r).length)
    (hs : DeserLoopGPlacedW x R s0 k s) :
    DeserStepGPlacedW H x R s0 s (fun s' => DeserLoopGPlacedW x R s0 (k + 1) s') := by
  obtain ⟨hpc, hrun, htr, hcrl, hsp, hal, hx29, hx19, hx20, hx23, hmem⟩ := hs
  let L := deserSpL s0.sp
  let fl := (recFields x.r)[k]
  let rest := ((recFields x.r).drop (k + 1)).flatMap GenField.enc
  let payRest := fl.payload ++ rest
  let curPtr := curPtr_loopIterG x.p x.r k
  have hpc_entry : s.pc = (blkPl_46).base + 596#64 := hpc
  have hn_lt20 : payRest.length < 2 ^ 20 := payload_rest_length_lt_loopIterG hr hk
  have hn_lt62 : payRest.length < 2 ^ 62 := Nat.lt_trans hn_lt20 (by decide)
  obtain ⟨hkb_lt, htag_pos, hwt_lt, hkb_tag, hkb_wt⟩ := keyByte_loopIterG_bounds fl
  set F_loop : SepProp :=
    (x.p ↦ₛ preBytes_loopIterG x.r k) ∗
      prostSSGAt A0 (L + 0x420#64) (ssgAfter x.r k) ∗
      ((curPtr + 1#64) ↦ₛ payRest) ∗
      deserFixed_loopIter L ∗ deserOutRegion_loopIter x.out ∗
      deserCalleeUnused_loopIterW L ∗ stackAt L mergeFieldStackX ∗
      deserSaved s0 ∗ R
  have hmem1 : s.mem ⊨ stepPre_loopIter L curPtr (keyByte_loopIterG fl) payRest.length ∗ F_loop := by
    change s.mem ⊨ deserLocalsG L x.p (encodeRecord x.r) (((recFields x.r).drop k).flatMap GenField.enc)
        (ssgAfter x.r k) ∗
      memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R at hmem
    rw [deserLocalsG_decomp_loopIterG, deserOutRegion_eq_loopIter,
      sliceCursorAfter_split_key_loopIterG L x.p hr hk,
      stackAt_deserCallee_split_loopIterW L, sep_perm1_loopIter] at hmem
    exact hmem
  intro hL
  obtain ⟨sm, hsteps1, ⟨-, -, Pm, hmm, hpcm, hrunm, hspm, htrm, hlrm,
      hx0m, hx1m, hx2m, hx3m, hx4m, hx19m, hx20m, hx23m, hx29m, hPm⟩ | ⟨_, _hoom⟩⟩ :=
    (step_254_to_2e8_placed_loopIter_kb L curPtr (keyByte_loopIterG fl) payRest.length s
      (post := fun sm Pm =>
        sm.pc = lsmpl.base 15 ∧
        sm.status = .Running ∧
        sm.sp = s.sp ∧
        (sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        sm.readReg64 .lr = (blkPl_46).base + 748#64 ∧
        sm.readReg64 .x0 = L + 0x420#64 ∧
        (sm.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 ((keyByte_loopIterG fl).toNat / 8) ∧
        (sm.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 ((keyByte_loopIterG fl).toNat % 8) ∧
        sm.readReg64 .x3 = L + 0x6e8#64 ∧
        (sm.readReg64 .x4).setWidth 32 = 99#32 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = 0#64 ∧
        sm.readReg64 .x23 = L + 0x408#64 ∧
        sm.readReg64 .x29 = L + 0x710#64 ∧
        Pm = stepPost_loopIter L curPtr (keyByte_loopIterG fl) payRest.length)
      hpc_entry hrun hx29 hx20 hx23 hkb_lt htag_pos hwt_lt hn_lt62
      (fun _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 =>
        ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, rfl⟩)).elim hmem1 hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  subst hPm
  rw [hkb_tag] at hx1m
  rw [hkb_wt] at hx2m
  have hcrl_m : LibsignalCodeRoLoaded lsmpl sm.mem := hcrl.of_keepsFrozen hsteps1.keepsFrozen
  have hLm : (lsProg_46 H).CodeLoaded sm.mem := hsteps1.codeLoaded hL
  have hspm_L : sm.sp = L := hspm.trans hsp
  have hal_m : sm.spAligned = true := by
    simp only [State.spAligned] at hal ⊢
    rwa [hspm]
  have hcall : subroutine_ok (lsProg_46 H) (lsmpl.base 15)
      (mergeFieldGenPlacedSpecW (fun _ => True)) :=
    ls_call_ro_of_block (callerProg := lsProg_46 H) hMF
  let g : MergeFieldGenGhost :=
    ⟨L + 0x420#64, ssgAfter x.r k, fl, L + 0x6e8#64, L + 0x3f8#64, curPtr + 1#64, rest⟩
  set F_mf : SepProp :=
    (curPtr ↦₈ keyByte_loopIterG fl) ∗
      (x.p ↦ₛ preBytes_loopIterG x.r k) ∗
      deserFixed_loopIter L ∗ deserOutRegion_loopIter x.out ∗
      deserCalleeUnused_loopIterW L ∗ deserSaved s0
  have hok : fl.Ok := recFields_ok x.r hr fl (List.getElem_mem hk)
  have hfresh : fl.Fresh (ssgAfter x.r k) := recFields_fresh x.r hr k hk
  have hpre_mf : sm.mem ⊨ (mergeFieldGenPlacedSpecW (fun _ => True)).pre g sm ∗ (F_mf ∗ R) := by
    dsimp only [mergeFieldGenPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl_m, ?_⟩
    dsimp only [mergeFieldGenRawSpecW, g]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0m, hx1m, hx2m, hx3m, hx4m, trivial, hok, hfresh, hn_lt62⟩, ?_⟩
    rw [hspm_L]
    unfold Prost.sliceCursorAt
    have ha : L + 0x3f8#64 + 8#64 = L + 0x400#64 := by bv_omega
    rw [ha]
    dsimp only [stepPost_loopIter, F_loop] at hmm
    dsimp only [F_mf]
    rw [← sep_perm2_loopIter]
    exact hmm
  obtain ⟨s2, hsteps2, hout, -⟩ :=
    hcall.no_fault_before_outcome g (F_mf ∗ R) sm hpcm hrunm hpre_mf hal_m hLm
  rcases hout with ⟨⟨hpc2, _, hrun2⟩, ⟨hsp2, hcs2⟩, hpost2⟩ | ⟨hpan2, hpost2⟩ | ⟨code, _, hpost2⟩ | ⟨_, _hoom_post⟩
  rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
  · rw [hlrm] at hpc2
    dsimp only [mergeFieldGenPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded,
      mergeFieldGenRawSpecW, g] at hpost2
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost2
    obtain ⟨⟨htr2, hx0_2⟩, hmem2⟩ := hpost2
    have hL2 : (lsProg_46 H).CodeLoaded s2.mem := hsteps2.codeLoaded hLm
    obtain ⟨sf, hsteps3, ⟨-, -, P_f, hmf, hpcf, hrunf, hspf, htrf,
        hx19f, hx20f, hx23f, hx29f, hPf⟩ | ⟨_, _hoom⟩⟩ :=
      (step_2ec_placed_loopIter s2
        (P := prostSSGAt A0 (L + 0x420#64) ((ssgAfter x.r k).apply fl) ∗
          ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
          Prost.sliceCursorAfter (L + 0x3f8#64) (curPtr + 1#64) payRest rest ∗
          stackAt sm.sp mergeFieldStackX)
        (post := fun sf P_f =>
          sf.pc = (blkPl_46).base + 596#64 ∧
          sf.status = .Running ∧
          sf.sp = s2.sp ∧
          (sf.trace = s2.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s2) ∧
          sf.readReg64 .x19 = s2.readReg64 .x19 ∧
          sf.readReg64 .x20 = s2.readReg64 .x20 ∧
          sf.readReg64 .x23 = s2.readReg64 .x23 ∧
          sf.readReg64 .x29 = s2.readReg64 .x29 ∧
          P_f = (prostSSGAt A0 (L + 0x420#64) ((ssgAfter x.r k).apply fl) ∗
            ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
            Prost.sliceCursorAfter (L + 0x3f8#64) (curPtr + 1#64) payRest rest ∗
            stackAt sm.sp mergeFieldStackX))
        hpc2 hrun2 hx0_2
        (fun _ h1 h2 h3 h4 h5 h6 h7 h8 => ⟨h1, h2, h3, h4, h5, h6, h7, h8, rfl⟩)).elim hmem2 hL2
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    subst hPf
    have hsteps_all : Steps (lsProg_46 H) s sf := (hsteps1.trans hsteps2).trans hsteps3
    have hsp_sf : sf.sp = L := hspf.trans (hsp2.trans hspm_L)
    have hsp_s : sf.sp = s.sp := hsp_sf.trans hsp.symm
    have hal_sf : sf.spAligned = true := by
      simp only [State.spAligned] at hal ⊢
      rwa [hsp_s]
    refine ⟨sf, hsteps_all, Or.inl ?_⟩
    refine ⟨hpcf, hrunf,
      ⟨htrf.1.trans (htr2.trans (htrm.1.trans htr.1)),
       htrf.2.trans (hcs2.2.2.2.2.2.2.2.2.2.2.2.trans (htrm.2.trans htr.2))⟩,
      hcrl.of_keepsFrozen hsteps_all.keepsFrozen,
      hsp_sf, hal_sf,
      by reg_chain, by reg_chain, by reg_chain, by reg_chain, ?_⟩
    · change sf.mem ⊨ deserLocalsG L x.p (encodeRecord x.r)
          (((recFields x.r).drop (k + 1)).flatMap GenField.enc) (ssgAfter x.r (k + 1)) ∗
        memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R
      rw [deserLocalsG_decomp_loopIterG, deserOutRegion_eq_loopIter,
        ssgAfter_succ_loopIterG hk, ← sliceCursorAfter_unsplit_key_loopIterG L x.p hr hk,
        stackAt_deserCallee_split_loopIterW L, ← sep_perm3_loopIter]
      rw [hspm_L] at hmf
      exact hmf
  · have hsteps_all : Steps (lsProg_46 H) s s2 := hsteps1.trans hsteps2
    refine ⟨s2, hsteps_all, Or.inr ⟨hpan2, ?_⟩⟩
    dsimp only [mergeFieldGenPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded,
      mergeFieldGenRawSpecW, deserializeGenPlacedSpec, deserializeGenRawSpec,
      Serialization.allocPanic] at hpost2 ⊢
    rw [← sepConj_assoc] at hpost2
    refine allowPanic_frame (fun ⟨ha, hp⟩ => ?_) hpost2
    rw [allocFailedIn, htrm.1, htr.1] at ha
    rw [htrm.1, htr.1] at hp
    exact ⟨ha, hp⟩
  · exact (not_satisfies_false_sepConj hpost2).elim

end Placed

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.DeserLoopIterG
