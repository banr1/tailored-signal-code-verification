/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChains
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Steps
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

@[expose] public section

set_option autoImplicit false

/-!
# `SessionStructure::merge_field` Tag 7 (`receiver_chains`)

Verifies `SessionStructure::merge_field` (`0x5ca4`, Block `15`) on protobuf tag 7
(`receiver_chains`) on `SP2Ext` and under relocatable `[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal Proofs.libsignal.Hooks2

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local irreducible] prostSSRest_receiverChains prostChainAt prostSSAt mfFramePad_receiverChains
  Prost.sliceCursorAt Prost.sliceCursorAfter

theorem mergeField_fnAddr_eq_base_add_receiverChains_ext (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (SP2Ext b ext).fnAddr mergeFieldName = b + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") := by
  have h1 := (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")
  simp only [SP2Ext, contractProg, Program.fnAddr_rebase, mergeFieldName, h1]

theorem adrp_0x4601c_40_eq_receiverChains_ext {base entry : BitVec 64}
    (halign : base &&& 0xfff#64 = 0#64)
    (he : entry = base + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) :
    (entry + bv% (40) &&& bv% (2 ^ 64 - 4096)) = base + bv% (page% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 40)) := by
  subst he
  bv_arith

theorem chainMerge_fnAddr_eq_receiverChains_ext (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (SP2Ext b ext).fnAddr mergeFieldName + bv% (2 ^ 64 + (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) =
      (SP2Ext b ext).fnAddr chainMergeName := by
  have h1 := (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")
  have h2 := (ls_lemma% fnOff "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")
  simp only [SP2Ext, contractProg, Program.fnAddr_rebase, mergeFieldName, chainMergeName, h1, h2]
  rw [BitVec.add_assoc]
  rfl

theorem growOneChain_fnAddr_eq_receiverChains_ext (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (SP2Ext b ext).fnAddr mergeFieldName + bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") =
      (SP2Ext b ext).fnAddr growOneChainNameX := by
  have h1 := (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")
  have h2 := (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")
  simp only [SP2Ext, contractProg, Program.fnAddr_rebase, mergeFieldName, growOneChainNameX, h1, h2]
  rw [BitVec.add_assoc]
  rfl

theorem sepWP_intro_rodata_tag7_receiverChains_ext {img : Obj.Image}
    (hLoads : Obj.Loads libsignalSessionImage img)
    {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (hF : img.FrozenLoaded s)
    (h : SepWP prog target_pc s (((img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 6)) ↦₈ᵣ 0x8d#8) ∗ P) post) :
    SepWP prog target_pc s P post := by
  have hro : img.RoDataLoaded s.mem := (Obj.Image.frozenLoaded_iff.mp hF).2.1
  unfold SepWP at h ⊢
  intro R hm
  have hR := h R
  rw [sepConj_assoc] at hR
  exact hR (rodata_mfJumpTable_tag7_intro_receiverChains hLoads hro hm)

theorem of_sepWP_inImage_receiverChains_ext {img : Obj.Image} {prog : Program} (mid : BitVec 64) {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog mid s P (fun sm Pm =>
      img.FrozenLoaded sm → sm.symtab = img.symtab →
        SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, _hoom⟩⟩ := h.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ :=
    hnext (hsteps.frozenLoaded hF) (hsteps.symtab_eq.trans hsym) R hmm (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

theorem call_frame_inImage_receiverChains_ext {α : Type} {img : Obj.Image} {prog : Program} {entry ret_pc ret : BitVec 64}
    {spec : Spec α} {x : α} {φ : Prop} {P T F : SepProp} {s : State}
    {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp :=
  ProofLib.SepWPp.call_frame_frozen hcall hF hsym hpc hrun hsp hlr hspec hφ hP hexit hpanic hnext
    (fun sf _ _ hpost => by rw [hoom sf] at hpost; exact (not_satisfies_false_sepConj hpost).elim)

private theorem stackAt_sub_to_chainMerge_receiverChains_extW (sp : BitVec 64) :
    stackAt sp mergeFieldSubStackX =
      memRegion (sp - 32528#64) 3856 ∗ stackAt sp chainMergeStackX := by
  change memRegion (sp - 32528#64) 32528 =
    memRegion (sp - 32528#64) 3856 ∗ memRegion (sp - 28672#64) 28672
  have h3 : (sp - 32528#64) + 3856#64 = sp - 28672#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have hsplit := memRegion_split (sp - 32528#64) 3856 28672 (by decide)
  rw [show (3856 : Nat) + 28672 = 32528 by decide,
      show BitVec.ofNat 64 3856 = 3856#64 from rfl, h3] at hsplit
  exact hsplit

private theorem stackAt_sub_to_growOne_receiverChains_extW (sp : BitVec 64) :
    stackAt sp mergeFieldSubStackX =
      memRegion (sp - 32528#64) 15632 ∗ stackAt sp Stage1X.growOneChainStackX := by
  change memRegion (sp - 32528#64) 32528 =
    memRegion (sp - 32528#64) 15632 ∗ memRegion (sp - 16896#64) 16896
  have h3 : (sp - 32528#64) + 15632#64 = sp - 16896#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have hsplit := memRegion_split (sp - 32528#64) 15632 16896 (by decide)
  rw [show (15632 : Nat) + 16896 = 32528 by decide,
      show BitVec.ofNat 64 15632 = 15632#64 from rfl, h3] at hsplit
  exact hsplit

private theorem stackAt_mergeFieldStack_split_receiverChains_extW (sp0 : BitVec 64) :
    stackAt sp0 mergeFieldStackX =
      stackAt (sp0 - 240#64) mergeFieldSubStackX ∗
      mfFramePad_receiverChains sp0 ∗
      memRegion (sp0 - 232#64) 80 ∗
      memRegion (sp0 - 152#64) 24 ∗
      memRegion (sp0 - 80#64) 80 := by
  unfold mfFramePad_receiverChains
  change memRegion (sp0 - 32768#64) 32768 =
    memRegion (sp0 - 240#64 - 32528#64) 32528 ∗
    (memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 128#64) 48) ∗
    memRegion (sp0 - 232#64) 80 ∗
    memRegion (sp0 - 152#64) 24 ∗
    memRegion (sp0 - 80#64) 80
  have e_base : sp0 - 240#64 - 32528#64 = sp0 - 32768#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have s1 := memRegion_split (sp0 - 32768#64) 32528 240 (by decide)
  have e1 : (sp0 - 32768#64) + BitVec.ofNat 64 32528 = sp0 - 240#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (32528 : Nat) + 240 = 32768 by decide, e1] at s1
  have s2 := memRegion_split (sp0 - 240#64) 8 232 (by decide)
  have e2 : (sp0 - 240#64) + BitVec.ofNat 64 8 = sp0 - 232#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (8 : Nat) + 232 = 240 by decide, e2] at s2
  have s3 := memRegion_split (sp0 - 232#64) 80 152 (by decide)
  have e3 : (sp0 - 232#64) + BitVec.ofNat 64 80 = sp0 - 152#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (80 : Nat) + 152 = 232 by decide, e3] at s3
  have s4 := memRegion_split (sp0 - 152#64) 24 128 (by decide)
  have e4 : (sp0 - 152#64) + BitVec.ofNat 64 24 = sp0 - 128#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (24 : Nat) + 128 = 152 by decide, e4] at s4
  have s5 := memRegion_split (sp0 - 128#64) 48 80 (by decide)
  have e5 : (sp0 - 128#64) + BitVec.ofNat 64 48 = sp0 - 80#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (48 : Nat) + 80 = 128 by decide, e5] at s5
  rw [e_base, s1, s2, s3, s4, s5]
  ac_rfl

private theorem stackAt_mergeFieldStack_join_receiverChains_extW (sp0 : BitVec 64) :
    stackAt (sp0 - 240#64) mergeFieldSubStackX ∗
      mfFramePad_receiverChains sp0 ∗
      memRegion (sp0 - 232#64) 104 ∗
      memRegion (sp0 - 80#64) 80 =
    stackAt sp0 mergeFieldStackX := by
  have s := memRegion_split (sp0 - 232#64) 80 24 (by decide)
  have e : (sp0 - 232#64) + BitVec.ofNat 64 80 = sp0 - 152#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (80 : Nat) + 24 = 104 by decide, e] at s
  rw [s, stackAt_mergeFieldStack_split_receiverChains_extW sp0]
  ac_rfl

private theorem stackAt_receiverChains_epilogue_fold_receiverChains_extW
    (sp0 : BitVec 64) (s0 : State) (w56 : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    (stackAt (sp0 - 240#64) mergeFieldSubStackX ∗
      mfFramePad_receiverChains sp0 ∗
      RawByteMove.chunks104_6QWAt (sp0 - 232#64) q0 q1 q2 q3 q4 q5 w6 ∗
      mfSavedRegs_receiverChains sp0 s0 w56) ⊢
    stackAt sp0 mergeFieldStackX := by
  rw [← stackAt_mergeFieldStack_join_receiverChains_extW sp0]
  have h1 := chunks104_6QWAt_entails_memRegion104_receiverChains (sp0 - 232#64) q0 q1 q2 q3 q4 q5 w6
  have h2 : mfSavedRegs_receiverChains sp0 s0 w56 ⊢ memRegion (sp0 - 80#64) 80 :=
    cells10_entails_memRegion80_receiverChains sp0
      (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x25) w56
      (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
      (s0.readReg64 .x20) (s0.readReg64 .x19)
  exact sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono h1 h2))

private theorem prostChainGAt_default_of_cells_litA (A : RustAlloc) (sp0 : BitVec 64) :
    ((sp0 - 232#64) ↦₆₄ 0#64) ∗ ((sp0 - 224#64) ↦₆₄ 1#64) ∗ ((sp0 - 216#64) ↦₆₄ 0#64) ∗
    ((sp0 - 208#64) ↦₆₄ 0#64) ∗ ((sp0 - 200#64) ↦₆₄ 1#64) ∗ ((sp0 - 192#64) ↦₆₄ 0#64) ∗
    ((sp0 - 184#64) ↦₆₄ 0#64) ∗ ((sp0 - 176#64) ↦₆₄ 8#64) ∗ ((sp0 - 168#64) ↦₆₄ 0#64) ∗
    ((sp0 - 160#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ memRegion (sp0 - 152#64) 24 ⊢
    prostChainGAt A (sp0 - 232#64) ChainG.empty := by
  simpa only [noneCap, sepConj_assoc] using prostChainGAt_default_of_cells A sp0

private theorem vecAt_recv_openA (A : RustAlloc) (ss : BitVec 64) (cs : List ChainG) :
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) cs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cs.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗
        ((ss + 0x58#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
        (if cap = 0#64 then emp
         else A.live ptr (cap.toNat * 104) 8 ∗ arrayAt (fun c a => prostChainGAt A a c) 104 ptr cs ∗
           memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) := by
  unfold vecOf vecAt vecHeader vecBuf
  apply Entails.sepExists_elim; intro cap; apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have e50 : ss + 0x48#64 + 8#64 = ss + 0x50#64 := by rw [BitVec.add_assoc]; rfl
  have e58 : ss + 0x48#64 + 16#64 = ss + 0x58#64 := by rw [BitVec.add_assoc]; rfl
  have h0 : (0 : BitVec 64) = 0#64 := rfl
  rw [e50, e58, h0]
  by_cases hcap : cap = 0#64 <;> simp only [hcap, ↓reduceIte] <;> exact Entails.of_eq (by ac_rfl)

private theorem vecBuf_recv_full_openA (A : RustAlloc) (cap ptr : BitVec 64) (cs : List ChainG)
    (hfull : cs.length = cap.toNat) :
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 104) 8 ∗ arrayAt (fun c a => prostChainGAt A a c) 104 ptr cs ∗
       memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = cap.toNat * 104 ∧
          ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ arrayAt (fun c b' => prostChainGAt A b' c) 104 b cs⌝ ∗
        (if cap = 0#64 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗ H := by
  by_cases hcap0 : cap = 0#64
  · subst hcap0; have hcs : cs = [] := List.eq_nil_of_length_eq_zero (by simpa using hfull)
    subst hcs; simp only [↓reduceIte, BitVec.toNat_ofNat]
    refine Entails.sepExists_right [] (Entails.sepExists_right emp ?_); rw [emp_sepConj]
    refine Entails.pure_right ⟨rfl, fun b => ?_⟩ (Entails.refl _); rw [pointsToBytes_nil, sepConj_emp]; exact Entails.refl _
  · simp only [hcap0, ↓reduceIte]
    have hrem : (cap.toNat - cs.length) * 104 = 0 := by omega
    rw [hrem, ProofLib.memRegion_zero, sepConj_emp]
    refine Entails.trans (sepConj_mono_right (arrayAt_prostChainGAt_move_bytes A cs ptr)) ?_
    rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro bs
    rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro H
    rw [← sepConj_assoc, sepConj_comm (A.live _ _ _), sepConj_assoc]
    apply Entails.pure_left; rintro ⟨hbs_len, hmov⟩
    have hbs_cap : bs.length = cap.toNat * 104 := by rw [hbs_len, hfull]
    refine Entails.sepExists_right bs (Entails.sepExists_right H ?_)
    rw [← hbs_cap]; exact Entails.pure_right ⟨rfl, hmov⟩ (Entails.of_eq (by ac_rfl))

private theorem vecBuf_recv_not_full_openA (A : RustAlloc) (cap ptr : BitVec 64) (cs : List ChainG)
    (hlt : cs.length < cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) :
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 104) 8 ∗ arrayAt (fun c a => prostChainGAt A a c) 104 ptr cs ∗
       memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) =
      (A.live ptr (cap.toNat * 104) 8 ∗ arrayAt (fun c b => prostChainGAt A b c) 104 ptr cs ∗
        memRegion (ptr + BitVec.ofNat 64 cs.length * 104#64) 104 ∗
        memRegion (ptr + BitVec.ofNat 64 ((cs.length + 1) * 104)) ((cap.toNat - (cs.length + 1)) * 104)) := by
  have hcap0 : cap ≠ 0#64 := by intro h0; subst h0; simp at hlt
  simp only [hcap0, ↓reduceIte]
  have hrem : (cap.toNat - cs.length) * 104 = 104 + (cap.toNat - (cs.length + 1)) * 104 := by
    have : cap.toNat - cs.length = 1 + (cap.toNat - (cs.length + 1)) := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have hmul : BitVec.ofNat 64 (cs.length * 104) = BitVec.ofNat 64 cs.length * 104#64 := BitVec.ofNat_mul _ _
  have hoff : ptr + BitVec.ofNat 64 (cs.length * 104) + BitVec.ofNat 64 104 = ptr + BitVec.ofNat 64 ((cs.length + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  rw [hrem, memRegion_split (ptr + BitVec.ofNat 64 (cs.length * 104)) 104 _ (by omega), hoff, hmul]

private theorem vecAt_recv_push_foldA (A : RustAlloc) (ss cap ptr : BitVec 64) (cs : List ChainG) (c : ChainG)
    (hlt : cs.length < cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    ((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗
      ((ss + 0x58#64) ↦₆₄ (BitVec.ofNat 64 cs.length + 1#64)) ∗
      A.live ptr (cap.toNat * 104) 8 ∗
      arrayAt (fun c' a => prostChainGAt A a c') 104 ptr cs ∗
      prostChainGAt A (ptr + BitVec.ofNat 64 cs.length * 104#64) c ∗
      memRegion (ptr + BitVec.ofNat 64 ((cs.length + 1) * 104)) ((cap.toNat - (cs.length + 1)) * 104) ⊢
    vecOf A 104 8 (fun c' a => prostChainGAt A a c') (ss + 0x48#64) (cs ++ [c]) := by
  have hne0 : cap ≠ 0 := by intro h0; subst h0; simp at hlt
  unfold vecOf vecAt vecHeader vecBuf
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have e50 : ss + 0x48#64 + 8#64 = ss + 0x50#64 := by rw [BitVec.add_assoc]; rfl
  have e58 : ss + 0x48#64 + 16#64 = ss + 0x58#64 := by rw [BitVec.add_assoc]; rfl
  have hlen_app : (cs ++ [c]).length = cs.length + 1 := by simp
  have hlen_bv : BitVec.ofNat 64 (cs.length + 1) = BitVec.ofNat 64 cs.length + 1#64 := BitVec.ofNat_add _ _
  have hmul : BitVec.ofNat 64 (cs.length * 104) = BitVec.ofNat 64 cs.length * 104#64 := BitVec.ofNat_mul _ _
  have h0 : (ptr ≠ (0 : BitVec 64)) = (ptr ≠ 0#64) := rfl
  rw [e50, e58, hlen_app, hlen_bv, arrayAt_concat, hmul, h0]; simp only [hne0, ↓reduceIte]
  rw [show (((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗ ((ss + 0x58#64) ↦₆₄ (BitVec.ofNat 64 cs.length + 1#64))) ∗
        (⌜cs.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          A.live ptr (cap.toNat * 104) 8 ∗
          (arrayAt (fun c' a => prostChainGAt A a c') 104 ptr cs ∗ prostChainGAt A (ptr + BitVec.ofNat 64 cs.length * 104#64) c) ∗
          memRegion (ptr + BitVec.ofNat 64 ((cs.length + 1) * 104)) ((cap.toNat - (cs.length + 1)) * 104)) =
      ⌜cs.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗ ((ss + 0x58#64) ↦₆₄ (BitVec.ofNat 64 cs.length + 1#64)) ∗
          A.live ptr (cap.toNat * 104) 8 ∗ arrayAt (fun c' a => prostChainGAt A a c') 104 ptr cs ∗
          prostChainGAt A (ptr + BitVec.ofNat 64 cs.length * 104#64) c ∗
          memRegion (ptr + BitVec.ofNat 64 ((cs.length + 1) * 104)) ((cap.toNat - (cs.length + 1)) * 104)) by ac_rfl]
  exact Entails.pure_right ⟨by omega, hcap_lt, hptr⟩ (Entails.refl _)

private theorem prostSSGAt_fold_apply_recvA (A : RustAlloc) (ss cap ptr : BitVec 64) (v : SSG) (c : ChainG)
    (hlt : v.recv.length < cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    (((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗
      ((ss + 0x58#64) ↦₆₄ (BitVec.ofNat 64 v.recv.length + 1#64)) ∗
      A.live ptr (cap.toNat * 104) 8 ∗
      arrayAt (fun c' a => prostChainGAt A a c') 104 ptr v.recv ∗
      prostChainGAt A (ptr + BitVec.ofNat 64 v.recv.length * 104#64) c ∗
      memRegion (ptr + BitVec.ofNat 64 ((v.recv.length + 1) * 104)) ((cap.toNat - (v.recv.length + 1)) * 104) ∗
      prostSSGRest A ss v) ⊢
    prostSSGAt A ss (v.apply (.recv c)) := by
  rw [prostSSGAt_eq_recv_sep_rest A ss (v.apply (.recv c)), prostSSGRest_apply_recv A ss v c]
  dsimp only [SSG.apply]
  refine Entails.trans (Entails.of_eq (show _ = (((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗
      ((ss + 0x58#64) ↦₆₄ (BitVec.ofNat 64 v.recv.length + 1#64)) ∗ A.live ptr (cap.toNat * 104) 8 ∗
      arrayAt (fun c' a => prostChainGAt A a c') 104 ptr v.recv ∗
      prostChainGAt A (ptr + BitVec.ofNat 64 v.recv.length * 104#64) c ∗
      memRegion (ptr + BitVec.ofNat 64 ((v.recv.length + 1) * 104)) ((cap.toNat - (v.recv.length + 1)) * 104)) ∗
      prostSSGRest A ss v by ac_rfl)) ?_
  exact sepConj_mono_left (vecAt_recv_push_foldA A ss cap ptr v.recv c hlt hcap_lt hptr)

private theorem growOne_inImage_pre_eq_extWA_rc (img : Obj.Image) (A : RustAlloc) (ss cap ptr sp : BitVec 64)
    (bs : List (BitVec 8)) (s : State) (hsp : s.sp = sp) :
    ((Stage1X.growOneChainSpecX A).inImage img).pre (ss + 0x48#64, cap, ptr, bs) s =
    ⌜(bs.length = cap.toNat * 104 ∧ s.readReg64 .x0 = ss + 0x48#64 ∧
        ptr ≠ 0#64 ∧ 8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63) ∧
      img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
    (((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗
      (if cap = 0#64 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
      A.pool ∗ stackAt sp Stage1X.growOneChainStackX) := by
  have h1 := growOne_inImage_pre_eq_extWA img A (ss + 0x48#64) cap ptr sp bs s hsp
  rwa [show ss + 0x48#64 + 8#64 = ss + 0x50#64 by rw [BitVec.add_assoc]; rfl] at h1

private theorem growOne_post_elim_sp_extWA_rc (img : Obj.Image) (A : RustAlloc) (ss cap ptr sp : BitVec 64)
    (cs : List ChainG) (bs : List (BitVec 8)) (s_pre sf : State)
    (hsp : s_pre.sp = sp) (hfull : cs.length = cap.toNat) (hlt5 : cs.length < maxReceiverChains)
    (hbs : bs.length = cap.toNat * 104) :
    ((Stage1X.growOneChainSpecX A).inImage img).post (ss + 0x48#64, cap, ptr, bs) s_pre sf ⊢
      ⌜sf.trace = s_pre.trace⌝ ∗
      ∃∗ cap' : BitVec 64, ∃∗ p' : BitVec 64,
        ⌜cs.length < cap'.toNat ∧ cap'.toNat * 104 < 2 ^ 63 ∧ p' ≠ 0#64⌝ ∗
        ((ss + 0x48#64) ↦₆₄ cap') ∗ ((ss + 0x50#64) ↦₆₄ p') ∗
        A.live p' (cap'.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 cs.length * 104#64) 104 ∗
        memRegion (p' + BitVec.ofNat 64 ((cs.length + 1) * 104)) ((cap'.toNat - (cs.length + 1)) * 104) ∗
        A.pool ∗ stackAt sp Stage1X.growOneChainStackX := by
  have h1 := growOne_post_elim_sp_extWA img A (ss + 0x48#64) cap ptr sp bs cs.length s_pre sf
    hsp hfull (hbs.trans (by rw [hfull])) (by unfold maxReceiverChains at *; omega)
  have e50 : ss + 0x48#64 + 8#64 = ss + 0x50#64 := by rw [BitVec.add_assoc]; rfl
  have emul : BitVec.ofNat 64 (cs.length * 104) = BitVec.ofNat 64 cs.length * 104#64 := BitVec.ofNat_mul _ _
  rw [e50, emul] at h1; refine Entails.trans h1 ?_
  apply Entails.pure_left; intro htr; refine Entails.pure_right htr ?_
  apply Entails.sepExists_elim; intro cap'; refine Entails.sepExists_right cap' ?_
  apply Entails.sepExists_elim; intro p'; refine Entails.sepExists_right p' ?_
  apply Entails.pure_left; rintro ⟨hle, hlt63, hp'⟩
  refine Entails.pure_right ⟨by omega, hlt63, hp'⟩ (Entails.refl _)

private theorem chainMergeGen_pre_eq_extWA (img : Obj.Image) (A : RustAlloc) (x : MergeFieldGenGhost)
    (c : ChainG) (s0_sp_232 sp : BitVec 64) (s : State) (hfld : x.fld = .recv c) (hsp : s.sp = sp) :
    (chainMergeGenSpecAtWA A img).pre ⟨s0_sp_232, c, x.bufRef, x.slot, x.ptr, x.tail⟩ s =
      ⌜(s.readReg64 .x0).setWidth 8 = 2#8 ∧ s.readReg64 .x1 = s0_sp_232 ∧
        s.readReg64 .x2 = x.bufRef ∧ (s.readReg64 .x3).setWidth 32 = 99#32 ∧
        c.Ok ∧ (x.fld.payload ++ x.tail).length < 2 ^ 62 ∧
        img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      (prostChainGAt A s0_sp_232 ChainG.empty ∗ (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗
        A.pool ∗ stackAt sp chainMergeStackX) := by
  unfold chainMergeGenSpecAtWA; dsimp only; rw [recv_payload_append_eq hfld x.tail, hsp]

private theorem chainMergeGen_post_eq_extWA (img : Obj.Image) (A : RustAlloc) (x : MergeFieldGenGhost)
    (c : ChainG) (s0_sp_232 sp : BitVec 64) (s_pre sf : State) (hfld : x.fld = .recv c) (hsp : s_pre.sp = sp) :
    (chainMergeGenSpecAtWA A img).post ⟨s0_sp_232, c, x.bufRef, x.slot, x.ptr, x.tail⟩ s_pre sf ⊢
      ⌜sf.trace = s_pre.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      prostChainGAt A s0_sp_232 c ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      A.pool ∗ stackAt sp chainMergeStackX := by
  unfold chainMergeGenSpecAtWA; dsimp only; rw [recv_payload_append_eq hfld x.tail, hsp]; exact Entails.refl _

/-- Step from `+0x45c` (`entry + 1116#64`) through the 104-byte `Chain` move and epilogue
(`+0x758..+0x770`) to `ret` under X-stack `mergeFieldSubStackX` / `mergeFieldStackX` (`A : RustAlloc`). -/
private theorem step_receiverChains_from_0x45c_to_ret_extWA
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (P : GenField → Prop) (x : MergeFieldGenGhost) (c : ChainG)
    (s0 s : State) (Fr : SepProp) (w56 cap' ptr' : BitVec 64)
    (hfld : x.fld = .recv c)
    (hlt : x.v.recv.length < cap'.toNat) (hcap_lt : cap'.toNat * 104 < 2 ^ 63) (hptr : ptr' ≠ 0#64)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr mergeFieldName + 1116#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 240#64)
    (hsp_align : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = x.ss)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.v.recv.length)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (SP2Ext img.base ext) (s0.readReg64 Reg.lr) s
      (((x.ss + 0x48#64) ↦₆₄ cap') ∗ ((x.ss + 0x50#64) ↦₆₄ ptr') ∗
        ((x.ss + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.v.recv.length) ∗
        A.live ptr' (cap'.toNat * 104) 8 ∗
        arrayAt (fun c' a => prostChainGAt A a c') 104 ptr' x.v.recv ∗
        memRegion (ptr' + BitVec.ofNat 64 x.v.recv.length * 104#64) 104 ∗
        memRegion (ptr' + BitVec.ofNat 64 ((x.v.recv.length + 1) * 104))
          ((cap'.toNat - (x.v.recv.length + 1)) * 104) ∗
        prostSSGRest A x.ss x.v ∗
        prostChainGAt A (s0.sp - 232#64) c ∗
        mfSavedRegs_receiverChains s0.sp s0 w56 ∗ mfFramePad_receiverChains s0.sp ∗
        A.pool ∗ stackAt (s0.sp - 240#64) mergeFieldSubStackX ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (mergeFieldGenSpecAtWA A img P).post x s0 sf ∗ Fr)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  mf7_fetches_range img.base (Rust.withPanics ext) 1116 1196
  mf7_fetches_range img.base (Rust.withPanics ext) 1880 1904
  dsimp only [SP2Ext, contractProg, mergeFieldName] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" = entry
  examples_hide_fetches
  apply SepWP.fold (prostChainGAt_move_chunks104 A (s0.sp - 232#64) c) (by sep_frame)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro q0; apply SepWP.exists_elim; intro q1
  apply SepWP.exists_elim; intro q2; apply SepWP.exists_elim; intro q3
  apply SepWP.exists_elim; intro q4; apply SepWP.exists_elim; intro q5
  apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro H
  apply SepWP.pure_elim; intro hmov
  set dst : BitVec 64 := ptr' + BitVec.ofNat 64 x.v.recv.length * 104#64
  apply SepWP.fold (Entails.of_eq (memRegion104_eq_exists_chunks104_6QWAt_receiverChains dst)) (by sep_frame)
  simp only [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d5
  apply SepWP.exists_elim; intro dw6
  conv => arg 4; rw [chunks104_6QWAt_stack_eq_receiverChains s0.sp q0 q1 q2 q3 q4 q5 w6,
    chunks104_6QWAt_dst_eq_receiverChains dst d0 d1 d2 d3 d4 d5 dw6, mfSavedRegs_receiverChains]
  wp_steps
  conv => arg 4; rw [← chunks104_6QWAt_dst_eq_receiverChains dst q0 q1 q2 q3 q4 q5 w6,
    ← chunks104_6QWAt_stack_eq_receiverChains s0.sp q0 q1 q2 q3 q4 q5 w6,
    ← mfSavedRegs_receiverChains]
  apply SepWP.fold (hmov dst) (by sep_frame)
  apply SepWP.fold (prostSSGAt_fold_apply_recvA A x.ss cap' ptr' x.v c hlt hcap_lt hptr) (by sep_frame)
  apply SepWP.fold (stackAt_receiverChains_epilogue_fold_receiverChains_extW s0.sp s0 w56 q0 q1 q2 q3 q4 q5 w6) (by sep_frame)
  simp only [mergeFieldGenSpecAtWA, hfld]
  wp_done

/-- Step from `+0x2bc` (`entry + 700#64`, return of `message::merge<Chain>`) to `ret`,
handling both `x.v.recv.length = cap.toNat` (`grow_one` at `+0x9ac`) and `x.v.recv.length < cap.toNat` (`A : RustAlloc`). -/
private theorem step_receiverChains_from_0x2bc_to_ret_extWA
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hG : Stage1X.GrowOneChainOkX img A ext)
    (P : GenField → Prop) (x : MergeFieldGenGhost) (c : ChainG)
    (s0 s : State) (Fr : SepProp) (w56 : BitVec 64)
    (hfresh : x.v.recv.length < maxReceiverChains)
    (hfld : x.fld = .recv c)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr mergeFieldName + 700#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 240#64)
    (hsp_align : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx20 : s.readReg64 .x20 = x.ss)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (SP2Ext img.base ext) (s0.readReg64 Reg.lr) s
      (prostChainGAt A (s0.sp - 232#64) c ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
        A.pool ∗ stackAt (s0.sp - 240#64) chainMergeStackX ∗
        memRegion ((s0.sp - 240#64) - 32528#64) 3856 ∗
        mfSavedRegs_receiverChains s0.sp s0 w56 ∗
        mfFramePad_receiverChains s0.sp ∗
        prostSSGAt A x.ss x.v)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (mergeFieldGenSpecAtWA A img P).post x s0 sf ∗ Fr)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (mergeFieldGenSpecAtWA A img P).onPanic x s0 sf ∗ Fr)) := by
  have hG' : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr mergeFieldName + bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>"))
      ((Stage1X.growOneChainSpecX A).inImage img) := by
    rw [growOneChain_fnAddr_eq_receiverChains_ext]; exact hG
  have h45c := @step_receiverChains_from_0x45c_to_ret_extWA img A ext P x c s0
  mf7_fetches_range img.base (Rust.withPanics ext) 700 700
  mf7_fetches_range img.base (Rust.withPanics ext) 1096 1112
  mf7_fetches_range img.base (Rust.withPanics ext) 2472 2484
  dsimp only [SP2Ext, contractProg, mergeFieldName] at hG' h45c hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" = entry
  examples_hide_fetches
  apply SepWPp.fold (Entails.of_eq (stackAt_sub_to_chainMerge_receiverChains_extW (s0.sp - 240#64)).symm) (by sep_frame)
  rw [prostSSGAt_eq_recv_sep_rest A x.ss x.v]
  apply SepWPp.fold (vecAt_recv_openA A x.ss x.v.recv) (by sep_frame)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap; apply SepWPp.exists_elim; intro ptr
  apply SepWPp.pure_left; rintro ⟨hlen_le, hcap_lt, hptr⟩
  by_cases hfull : x.v.recv.length = cap.toNat
  · apply SepWPp.fold (vecBuf_recv_full_openA A cap ptr x.v.recv hfull) (by sep_frame)
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.exists_elim; intro bs; apply SepWPp.exists_elim; intro H
    apply SepWPp.pure_left; rintro ⟨hbs_len, hmov⟩
    have hlen_cap : BitVec.ofNat 64 x.v.recv.length = cap := ofNat_length_eq_cap_of_eq hfull
    have hmax_lt : 8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63 := by have h5 : maxReceiverChains = 5 := rfl; omega
    rw [hlen_cap, stackAt_sub_to_growOne_receiverChains_extW (s0.sp - 240#64)]
    apply of_sepWP_inImage_receiverChains_ext (entry + bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) hF hsym
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) ?_
    intro hF1 hsym1
    refine SepWPp.call_frame (x := (x.ss + 0x48#64, cap, ptr, bs))
      (ret_pc := entry + bv% (2480)) hG'
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm] at hsp_align ⊢; exact hsp_align)
      (by simp only [arm64_norm])
      (growOne_inImage_pre_eq_extWA_rc img A x.ss cap ptr (s0.sp - 240#64) bs _ (by simp only [arm64_norm, hsp]))
      ⟨⟨hbs_len, by simp only [arm64_norm], hptr, hmax_lt⟩, hF1, hsym1⟩
      (by sep_frame)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans_receiverChains (by simp only [arm64_norm, htr])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx25m, hx26m, hx27m, hx28m, hfpm, hvregsm⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hx20, hx26, hx27, hx28, hsp, hvregs] at hpcm hspm hx19m hx20m hx21m hx22m hx23m hx24m hx25m hx26m hx27m hx28m hfpm hvregsm
    have hsp_align_m : sm.spAligned = true := by simp only [State.spAligned] at hsp_align ⊢; rw [hspm, ← hsp]; exact hsp_align
    refine SepWPp.fold
      (growOne_post_elim_sp_extWA_rc img A x.ss cap ptr (s0.sp - 240#64) x.v.recv bs _ sm ?_ hfull hfresh hbs_len) rfl ?_
    · simp only [arm64_norm, hsp]
    simp only [sepConj_assoc]
    apply SepWPp.pure_left; intro htr_m
    have htr_m' : sm.trace = s0.trace := by simpa only [arm64_norm, htr] using htr_m
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.exists_elim; intro cap'; apply SepWPp.exists_elim; intro p'
    apply SepWPp.pure_left; rintro ⟨hlt_cap', hcap_lt', hp'⟩
    apply SepWPp.fold (hmov p') (by sep_frame)
    apply SepWPp.fold (Entails.of_eq (stackAt_sub_to_growOne_receiverChains_extW (s0.sp - 240#64)).symm) (by sep_frame)
    rw [← hlen_cap] at hx19m ⊢
    apply SepWPp.of_sepWP (mid := entry + bv% (1116))
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) ?_
    apply SepWPp.of_sepWP_ret
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (h45c _ Fr w56 cap' p' hfld hlt_cap' hcap_lt' hp'
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [State.spAligned, arm64_norm] at hsp_align_m ⊢; exact hsp_align_m)
        (by simp only [arm64_norm, htr_m']) (by simp only [arm64_norm]) (by simp only [arm64_norm, hx19m])
        (by simp only [arm64_norm, hx26m]) (by simp only [arm64_norm, hx27m]) (by simp only [arm64_norm, hx28m])
        (by simp only [arm64_norm, hvregsm]))
  · have hlt : x.v.recv.length < cap.toNat := by omega
    have hbeq : (BitVec.ofNat 64 x.v.recv.length == cap) = false := beq_ofNat_len_cap_false hlt
    rw [vecBuf_recv_not_full_openA A cap ptr x.v.recv hlt hcap_lt]
    apply SepWPp.of_sepWP (mid := entry + bv% (1116))
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) ?_
    apply SepWPp.of_sepWP_ret
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (h45c _ Fr w56 cap ptr hfld hlt hcap_lt hptr
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
        (by simp only [State.spAligned, arm64_norm] at hsp_align ⊢; exact hsp_align)
        (by simp only [arm64_norm, htr]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, hx26]) (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
        (by simp only [arm64_norm, hvregs]))

theorem mergeFieldGenReceiverChains_ok_extWA (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hC : DeserializeCalleesAtWA img A ext)
    (hCh : ChainMergeGenOkAtWA img A ext) :
    MergeFieldGenOkAtWA img A ext (fun fl => fl.tag = 7) := by
  unfold MergeFieldGenOkAtWA OkAtX
  apply subroutine_ok_of_sepWPp
  intro x Fr s0 hpc hrun hpre hsp
  refine ⟨_, Fr, hpre, ?_⟩
  conv => arg 4; dsimp only [mergeFieldGenSpecAtWA]
  apply SepWPp.pure_left
  rintro ⟨hx0, hx1, hx2, hx3, hx4, htag, hOk, hFresh, hlen, hF, hsym⟩
  obtain ⟨c, hfld⟩ := eq_recv_of_tag_eq_7 htag
  have hcOk : c.Ok := by rw [hfld] at hOk; exact hOk.1
  have hfresh : x.v.recv.length < maxReceiverChains := by rw [hfld] at hFresh; exact hFresh
  rw [hfld] at hx1 hx2
  dsimp only [GenField.tag, GenField.wt, CryptoVerification.LibsignalProtoCodec.WireType.toNat,
    BitVec.ofNat_eq_ofNat] at hx1 hx2
  have hx2' : BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x2)) &&& 255#64 = 2#64 :=
    zext64_trunc32_and_255_eq_of_trunc8_receiverChains hx2
  have hsp0 : s0.sp &&& 15#64 = 0#64 := eq_of_beq hsp
  have hsp240 : (s0.sp - 240#64) &&& 15#64 = 0#64 := sp_sub_240_aligned_receiverChains hsp0
  have hsp240_beq : ((s0.sp - 240#64) &&& 15#64 == 0#64) = true := beq_iff_eq.mpr hsp240
  have halign : img.base &&& 0xfff#64 = 0#64 := base_aligned_of_loads hLoads
  have he : (SP2Ext img.base ext).fnAddr mergeFieldName = img.base + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") :=
    mergeField_fnAddr_eq_base_add_receiverChains_ext img.base ext
  have hCh' : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr mergeFieldName + bv% (2 ^ 64 + (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")))
      (chainMergeGenSpecAtWA A img) := by
    rw [chainMerge_fnAddr_eq_receiverChains_ext]; exact hCh
  have h2bc := @step_receiverChains_from_0x2bc_to_ret_extWA img A ext hC.2.2.2
    (fun fl => fl.tag = 7) x c s0
  mf7_fetches_range img.base (Rust.withPanics ext) 0 60
  mf7_fetches_range img.base (Rust.withPanics ext) 628 696
  rw [stackAt_mergeFieldStack_split_receiverChains_extW s0.sp,
    memRegion80_chainInit_eq_cells10_receiverChains s0.sp,
    memRegion80_eq_cells10_receiverChains s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro c0; apply SepWPp.exists_elim; intro c1
  apply SepWPp.exists_elim; intro c2; apply SepWPp.exists_elim; intro c3
  apply SepWPp.exists_elim; intro c4; apply SepWPp.exists_elim; intro c5
  apply SepWPp.exists_elim; intro c6; apply SepWPp.exists_elim; intro c7
  apply SepWPp.exists_elim; intro c8; apply SepWPp.exists_elim; intro c9
  apply SepWPp.exists_elim; intro w80; apply SepWPp.exists_elim; intro w72
  apply SepWPp.exists_elim; intro w64; apply SepWPp.exists_elim; intro w56
  apply SepWPp.exists_elim; intro w48; apply SepWPp.exists_elim; intro w40
  apply SepWPp.exists_elim; intro w32; apply SepWPp.exists_elim; intro w24
  apply SepWPp.exists_elim; intro w16; apply SepWPp.exists_elim; intro w8
  dsimp only [SP2Ext, contractProg, mergeFieldName] at he hCh' h2bc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" = entry
  have hadrp : (entry + bv% (40) &&& bv% (2 ^ 64 - 4096)) = img.base + bv% (page% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 40)) :=
    adrp_0x4601c_40_eq_receiverChains_ext halign he
  clear he
  examples_hide_fetches
  apply of_sepWP_inImage_receiverChains_ext (entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>"))) hF hsym
  apply sepWP_intro_rodata_tag7_receiverChains_ext hLoads hF
  wp_steps
  apply sepWP_drop_left_receiverChains
  apply SepWP.fold (prostChainGAt_default_of_cells_litA A s0.sp) (by sep_frame)
  apply SepWP.fold (mfSavedRegs_intro_receiverChains s0.sp s0 c3) (by sep_frame)
  apply SepWP.fold (Entails.of_eq (stackAt_sub_to_chainMerge_receiverChains_extW (s0.sp - 240#64))) (by sep_frame)
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) ?_
  intro hF1 hsym1
  refine call_frame_inImage_receiverChains_ext (ret_pc := entry + bv% (700)) hF1 hsym1 hCh'
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
    (by simp only [arm64_norm])
    (chainMergeGen_pre_eq_extWA img A x c (s0.sp - 232#64) (s0.sp - 240#64) _ hfld (by simp only [arm64_norm]))
    ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm], hcOk, hlen, hF1, hsym1⟩
    (by sep_frame)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans_receiverChains (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hF2 hsym2
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx25m, hx26m, hx27m, hx28m, hfpm, hvregsm⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19m hx20m hx21m hx22m hx23m hx24m hx25m hx26m hx27m hx28m hfpm hvregsm
  have hsp_align_m : sm.spAligned = true := by simp only [State.spAligned, hspm]; exact hsp240_beq
  refine SepWPp.fold
    (chainMergeGen_post_eq_extWA img A x c (s0.sp - 232#64) (s0.sp - 240#64) _ sm hfld (by simp only [arm64_norm])) rfl ?_
  simp only [sepConj_assoc]
  apply SepWPp.pure_left; rintro ⟨htr_m, hx0_m⟩
  have htr_m' : sm.trace = s0.trace := by simpa only [arm64_norm] using htr_m
  refine SepWPp.weaken_pre ?_
    (h2bc sm Fr c3 hfresh hfld hF2 hsym2 hpcm hrunm hspm hsp_align_m htr_m' hx0_m hx20m hx26m hx27m hx28m hvregsm)
  have hsub32768 : (s0.sp - 240#64) - 32528#64 = s0.sp - 32768#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  exact Entails.of_eq (by rw [hsub32768]; ac_rfl)

theorem mergeFieldGenReceiverChains_ok_extW (img : Obj.Image)
    (ext : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hC : DeserializeCalleesAtW img ext)
    (hCh : ChainMergeGenOkAtW img ext) :
    MergeFieldGenOkAtW img ext (fun fl => fl.tag = 7) := by
  have hp : A0.pool = emp := rfl
  have hspec : mergeFieldGenSpecAtWA A0 img (fun fl => fl.tag = 7) = mergeFieldGenSpecAtW img (fun fl => fl.tag = 7) := by
    unfold mergeFieldGenSpecAtWA mergeFieldGenSpecAtW; simp only [hp, emp_sepConj]
  have hcspec : chainMergeGenSpecAtWA A0 img = chainMergeGenSpecAtW img := by
    unfold chainMergeGenSpecAtWA chainMergeGenSpecAtW; simp only [hp, emp_sepConj]
  unfold MergeFieldGenOkAtW; rw [← hspec]
  exact mergeFieldGenReceiverChains_ok_extWA img A0 ext hLoads hC (by unfold ChainMergeGenOkAtWA; rwa [hcspec])

/-! ## Relocatable `[LibsignalPlacement]` proof for tag 7 (`receiver_chains`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem L1_MergeFieldGenReceiverChainsExt_Placed : True := trivial

private theorem sepWP_intro_rodata_tag7_placed_receiverChains_ext [LibsignalPlacement]
    {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog target_pc s (((lsmpl.ρ mergeFieldRodataSym + 6#64) ↦₈ᵣ 0x8d#8) ∗ P) post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  have hR := h R
  rw [sepConj_assoc] at hR
  exact hR (lsro8_intro hcrl.2 (by lsro_addr) (by decide +kernel) hm)

private theorem call_frame_lscro_receiverChains_ext {α : Type} {prog : Program} {pl : MultiPlacement}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {P T F : SepProp} {s : State} {Q Qp : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded pl s.mem)
    (hcall : subroutine_ok prog entry (LibsignalTripleRatchet.withLsCodeRoLoaded pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalCodeRoLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hpre_in : s.mem ⊨ (LibsignalTripleRatchet.withLsCodeRoLoaded pl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hpre_in hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hcrl.of_keepsFrozen hsteps.keepsFrozen) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, hpanic sm hpan⟩)⟩
  · exact (hexit sm code _ hex hpost).elim
  · dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded] at hpost
    rw [hoom sm] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

private theorem growOne_placed_pre_eq_extW_rc (ss cap ptr sp : BitVec 64)
    (bs : List (BitVec 8)) (s : State) (hsp : s.sp = sp) :
    (Stage1X.growOneChainSpecX A0).pre (ss + 0x48#64, cap, ptr, bs) s =
      ⌜bs.length = cap.toNat * 104 ∧ s.readReg64 .x0 = ss + 0x48#64 ∧ ptr ≠ 0#64 ∧
        8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63⌝ ∗
      (((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗
        (if cap = 0#64 then emp else A0.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
        stackAt sp Stage1X.growOneChainStackX) := by
  unfold Stage1X.growOneChainSpecX Stage1X.growOne104SpecX
  dsimp only
  have e50 : ss + 0x48#64 + 8#64 = ss + 0x50#64 := by rw [BitVec.add_assoc]; rfl
  have hpool : A0.pool = emp := rfl
  have h0 : (0 : BitVec 64) = 0#64 := rfl
  have hpure :
      (s.readReg64 .x0 = ss + 0x48#64 ∧ bs.length = cap.toNat * 104 ∧ ptr ≠ 0 ∧
        max (2 * cap.toNat) 4 * 104 + 8 ≤ 2 ^ 63) =
      (bs.length = cap.toNat * 104 ∧ s.readReg64 .x0 = ss + 0x48#64 ∧ ptr ≠ 0#64 ∧
        8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63) :=
    propext ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h2, h1, h3, by omega⟩,
             fun ⟨h1, h2, h3, h4⟩ => ⟨h2, h1, h3, by omega⟩⟩
  rw [hpure, e50, hpool, hsp, h0]
  change _ = _ ∗ (_ ∗ _ ∗ _ ∗ stackAt sp (464 + Stage1X.finishGrowStackX))
  simp only [emp_sepConj, ← sepConj_assoc]

private theorem growOne_placed_post_elim_sp_extW_rc (ss cap ptr sp : BitVec 64)
    (recv : List ChainG) (bs : List (BitVec 8)) (s_pre sf : State)
    (hsp : s_pre.sp = sp) (hfull : recv.length = cap.toNat)
    (hfresh : recv.length < maxReceiverChains) (hbs : bs.length = recv.length * 104) :
    (Stage1X.growOneChainSpecX A0).post (ss + 0x48#64, cap, ptr, bs) s_pre sf ⊢
      ⌜sf.trace = s_pre.trace⌝ ∗ ∃∗ cap' : BitVec 64, ∃∗ p' : BitVec 64,
        ⌜recv.length < cap'.toNat ∧ cap'.toNat * 104 < 2 ^ 63 ∧ p' ≠ 0#64⌝ ∗
        ((ss + 0x48#64) ↦₆₄ cap') ∗ ((ss + 0x50#64) ↦₆₄ p') ∗ (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 recv.length * 104#64) 104 ∗
        memRegion (p' + BitVec.ofNat 64 ((recv.length + 1) * 104))
          ((cap'.toNat - (recv.length + 1)) * 104) ∗
        stackAt sp Stage1X.growOneChainStackX := by
  have h5 : maxReceiverChains = 5 := rfl
  have h := growOne_placed_post_elim_sp_extW (ss + 0x48#64) cap ptr sp bs recv.length
    s_pre sf hsp hfull hbs (by omega)
  have h50 : ss + 0x48#64 + 8#64 = ss + 0x50#64 := by bv_omega
  have hmul : BitVec.ofNat 64 (recv.length * 104) = BitVec.ofNat 64 recv.length * 104#64 := by
    rw [BitVec.ofNat_mul]
  rw [h50, hmul] at h
  exact h

private theorem chainMergeGen_placed_pre_eq_extW (x : MergeFieldGenGhost) (c : ChainG)
    (s0_sp_232 sp : BitVec 64) (s : State) (hfld : x.fld = .recv c) (hsp : s.sp = sp) :
    chainMergeGenRawSpecW.pre ⟨s0_sp_232, c, x.bufRef, x.slot, x.ptr, x.tail⟩ s =
      ⌜(s.readReg64 .x0).setWidth 8 = 2#8 ∧ s.readReg64 .x1 = s0_sp_232 ∧
        s.readReg64 .x2 = x.bufRef ∧ (s.readReg64 .x3).setWidth 32 = 99#32 ∧
        c.Ok ∧ (x.fld.payload ++ x.tail).length < 2 ^ 62⌝ ∗
      (prostChainGAt A0 s0_sp_232 ChainG.empty ∗ (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗
        stackAt sp chainMergeStackX) := by
  unfold chainMergeGenRawSpecW
  dsimp only
  rw [recv_payload_append_eq hfld x.tail, hsp]

private theorem chainMergeGen_placed_post_eq_extW (x : MergeFieldGenGhost) (c : ChainG)
    (s0_sp_232 sp : BitVec 64) (s_pre sf : State) (hfld : x.fld = .recv c) (hsp : s_pre.sp = sp) :
    chainMergeGenRawSpecW.post ⟨s0_sp_232, c, x.bufRef, x.slot, x.ptr, x.tail⟩ s_pre sf ⊢
      ⌜sf.trace = s_pre.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      prostChainGAt A0 s0_sp_232 c ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt sp chainMergeStackX := by
  unfold chainMergeGenRawSpecW
  dsimp only
  rw [recv_payload_append_eq hfld x.tail, hsp]
  exact Entails.refl _

private theorem step_receiverChains_from_0x45c_to_ret_placed_extW [LibsignalPlacement]
    {H : LibsignalHooks}
    (P : GenField → Prop) (x : MergeFieldGenGhost) (c : ChainG)
    (s0 s : State) (Fr : SepProp) (w56 cap' ptr' : BitVec 64)
    (hfld : x.fld = .recv c)
    (hlt : x.v.recv.length < cap'.toNat) (hcap_lt : cap'.toNat * 104 < 2 ^ 63) (hptr : ptr' ≠ 0#64)
    (hpc : s.pc = (blkPl_15).base + 1116#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 240#64)
    (hsp_align : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = x.ss)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.v.recv.length)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (lsProg_15 H) (s0.readReg64 Reg.lr) s
      (((x.ss + 0x48#64) ↦₆₄ cap') ∗ ((x.ss + 0x50#64) ↦₆₄ ptr') ∗
        ((x.ss + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.v.recv.length) ∗
        arrayAt (fun c' a => prostChainGAt A0 a c') 104 ptr' x.v.recv ∗
        memRegion (ptr' + BitVec.ofNat 64 x.v.recv.length * 104#64) 104 ∗
        memRegion (ptr' + BitVec.ofNat 64 ((x.v.recv.length + 1) * 104))
          ((cap'.toNat - (x.v.recv.length + 1)) * 104) ∗
        prostSSGRest A0 x.ss x.v ∗
        prostChainGAt A0 (s0.sp - 232#64) c ∗
        mfSavedRegs_receiverChains s0.sp s0 w56 ∗ mfFramePad_receiverChains s0.sp ∗
        stackAt (s0.sp - 240#64) mergeFieldSubStackX ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (mergeFieldGenPlacedSpecW P).post x s0 sf ∗ Fr)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  apply SepWP.fold (prostChainGAt_move_chunks104 A0 (s0.sp - 232#64) c) (by sep_frame)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro q0
  apply SepWP.exists_elim; intro q1
  apply SepWP.exists_elim; intro q2
  apply SepWP.exists_elim; intro q3
  apply SepWP.exists_elim; intro q4
  apply SepWP.exists_elim; intro q5
  apply SepWP.exists_elim; intro w6
  apply SepWP.exists_elim; intro H_mov
  apply SepWP.pure_elim; intro hmov
  set dst : BitVec 64 := ptr' + BitVec.ofNat 64 x.v.recv.length * 104#64
  apply SepWP.fold (Entails.of_eq (memRegion104_eq_exists_chunks104_6QWAt_receiverChains dst)) (by sep_frame)
  simp only [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro d0
  apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d2
  apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d4
  apply SepWP.exists_elim; intro d5
  apply SepWP.exists_elim; intro dw6
  conv => arg 4; rw [chunks104_6QWAt_stack_eq_receiverChains s0.sp q0 q1 q2 q3 q4 q5 w6,
    chunks104_6QWAt_dst_eq_receiverChains dst d0 d1 d2 d3 d4 d5 dw6, mfSavedRegs_receiverChains]
  wp_steps
  conv => arg 4; rw [← chunks104_6QWAt_dst_eq_receiverChains dst q0 q1 q2 q3 q4 q5 w6,
    ← chunks104_6QWAt_stack_eq_receiverChains s0.sp q0 q1 q2 q3 q4 q5 w6,
    ← mfSavedRegs_receiverChains]
  apply SepWP.fold (hmov dst) (by sep_frame)
  apply SepWP.fold (prostSSGAt_fold_apply_recv x.ss cap' ptr' x.v c hlt hcap_lt hptr) (by sep_frame)
  apply SepWP.fold (stackAt_receiverChains_epilogue_fold_receiverChains_extW s0.sp s0 w56 q0 q1 q2 q3 q4 q5 w6) (by sep_frame)
  simp only [mergeFieldGenRawSpecW, hfld]
  wp_done

private theorem step_receiverChains_from_0x2bc_to_ret_placed_extW [LibsignalPlacement]
    {H : LibsignalHooks}
    (hG : Stage1X.GrowOneChainPlacedOkX A0 H)
    (P : GenField → Prop) (x : MergeFieldGenGhost) (c : ChainG)
    (s0 s : State) (Fr : SepProp) (w56 : BitVec 64)
    (hfresh : x.v.recv.length < maxReceiverChains)
    (hfld : x.fld = .recv c)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_15).base + 700#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 240#64)
    (hsp_align : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx20 : s.readReg64 .x20 = x.ss)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_15 H) (s0.readReg64 Reg.lr) s
      (prostChainGAt A0 (s0.sp - 232#64) c ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
        stackAt (s0.sp - 240#64) chainMergeStackX ∗
        memRegion ((s0.sp - 240#64) - 32528#64) 3856 ∗
        mfSavedRegs_receiverChains s0.sp s0 w56 ∗
        mfFramePad_receiverChains s0.sp ∗
        prostSSGAt A0 x.ss x.v)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (mergeFieldGenPlacedSpecW P).post x s0 sf ∗ Fr)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (mergeFieldGenPlacedSpecW P).onPanic x s0 sf ∗ Fr)) := by
  have hG' : subroutine_ok (lsProg_15 H) (lsmpl.base 43)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (Stage1X.growOneChainSpecX A0)) :=
    ls_call_ro_of_cl (callerProg := lsProg_15 H) hG
  have h45c := @step_receiverChains_from_0x45c_to_ret_placed_extW _ H P x c s0
  apply SepWPp.fold (Entails.of_eq (stackAt_sub_to_chainMerge_receiverChains_extW (s0.sp - 240#64)).symm) (by sep_frame)
  rw [prostSSGAt_eq_recv_sep_rest A0 x.ss x.v]
  apply SepWPp.fold (vecAt_recv_open x.ss x.v.recv) (by sep_frame)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap
  apply SepWPp.exists_elim; intro ptr
  apply SepWPp.pure_left; rintro ⟨hlen_le, hcap_lt, hptr⟩
  by_cases hfull : x.v.recv.length = cap.toNat
  · apply SepWPp.fold (vecBuf_recv_full_open cap ptr x.v.recv hfull) (by sep_frame)
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.exists_elim; intro bs
    apply SepWPp.exists_elim; intro H_mov
    apply SepWPp.pure_left; rintro ⟨hbs_len, hmov⟩
    have hlen_cap : BitVec.ofNat 64 x.v.recv.length = cap := ofNat_length_eq_cap_of_eq hfull
    have hmax_lt : 8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63 := by
      have h5 : maxReceiverChains = 5 := rfl
      omega
    rw [hlen_cap, stackAt_sub_to_growOne_receiverChains_extW (s0.sp - 240#64)]
    apply LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 43) hcrl
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) ?_
    intro hcrl1
    refine call_frame_lscro_receiverChains_ext (x := (x.ss + 0x48#64, cap, ptr, bs))
      (ret_pc := (blkPl_15).base + 2480#64) hcrl1 hG'
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm] at hsp_align ⊢; exact hsp_align)
      (by simp only [arm64_norm])
      (growOne_placed_pre_eq_extW_rc x.ss cap ptr (s0.sp - 240#64) bs _ (by simp only [arm64_norm, hsp]))
      ⟨hfull ▸ hbs_len, by simp only [arm64_norm], hptr, hmax_lt⟩
      (by sep_frame)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans_receiverChains (by simp only [arm64_norm, htr])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm _hcrl2
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx25m, hx26m, hx27m, hx28m, hfpm, hvregsm⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hx20, hx26, hx27, hx28, hsp, hvregs] at hpcm hspm hx19m hx20m hx21m hx22m hx23m hx24m hx25m hx26m hx27m hx28m hfpm hvregsm
    have hsp_align_m : sm.spAligned = true := by
      simp only [State.spAligned] at hsp_align ⊢
      rw [hspm, ← hsp]
      exact hsp_align
    refine SepWPp.fold
      (growOne_placed_post_elim_sp_extW_rc x.ss cap ptr (s0.sp - 240#64) x.v.recv bs _ sm ?_ hfull hfresh (hfull.symm ▸ hbs_len)) rfl ?_
    · simp only [arm64_norm, hsp]
    simp only [sepConj_assoc]
    apply SepWPp.pure_left; intro htr_m
    have htr_m' : sm.trace = s0.trace := by simpa only [arm64_norm, htr] using htr_m
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.exists_elim; intro cap'
    apply SepWPp.exists_elim; intro p'
    apply SepWPp.pure_left; rintro ⟨hlt_cap', hcap_lt', hp'⟩
    apply SepWPp.fold (hmov p') (by sep_frame)
    apply SepWPp.fold (Entails.of_eq (stackAt_sub_to_growOne_receiverChains_extW (s0.sp - 240#64)).symm) (by sep_frame)
    rw [← hlen_cap] at hx19m ⊢
    apply SepWPp.of_sepWP (mid := (blkPl_15).base + 1116#64)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) ?_
    apply SepWPp.of_sepWP_ret
    refine SepWP.weaken_pre ?_
      (h45c _ Fr w56 cap' p' hfld hlt_cap' hcap_lt' hp' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · exact Entails.of_eq (by ac_rfl)
    · simp only [arm64_norm]
    · simp only [arm64_norm, hrunm]
    · simp only [arm64_norm, hspm]
    · simp only [State.spAligned, arm64_norm] at hsp_align_m ⊢; exact hsp_align_m
    · simp only [arm64_norm, htr_m']
    · simp only [arm64_norm]
    · simp only [arm64_norm, hx19m]
    · simp only [arm64_norm, hx26m]
    · simp only [arm64_norm, hx27m]
    · simp only [arm64_norm, hx28m]
    · simp only [arm64_norm, hvregsm]
  · have hlt : x.v.recv.length < cap.toNat := by omega
    have hbeq : (BitVec.ofNat 64 x.v.recv.length == cap) = false := beq_ofNat_len_cap_false hlt
    rw [vecBuf_recv_not_full_open cap ptr x.v.recv hlt hcap_lt]
    apply SepWPp.of_sepWP (mid := (blkPl_15).base + 1116#64)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm])
      (by simp only [arm64_norm, hrun]) ?_
    apply SepWPp.of_sepWP_ret
    refine SepWP.weaken_pre ?_
      (h45c _ Fr w56 cap ptr hfld hlt hcap_lt hptr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · exact Entails.of_eq (by ac_rfl)
    · simp only [arm64_norm]
    · simp only [arm64_norm, hrun]
    · simp only [arm64_norm, hsp]
    · simp only [State.spAligned, arm64_norm] at hsp_align ⊢; exact hsp_align
    · simp only [arm64_norm, htr]
    · simp only [arm64_norm]
    · simp only [arm64_norm]
    · simp only [arm64_norm, hx26]
    · simp only [arm64_norm, hx27]
    · simp only [arm64_norm, hx28]
    · simp only [arm64_norm, hvregs]

/-- Relocatable `SessionStructure::merge_field` (Block `15`, `lsProg_15 H`) on tag 7
(`receiver_chains`) at `mergeFieldStackX`. -/
theorem mergeFieldGenReceiverChains_placed_okW [LibsignalPlacement]
    (H : LibsignalHooks)
    (hC : DeserializeCalleesPlacedW H)
    (hCh : ChainMergeGenPlacedOkW H) :
    MergeFieldGenPlacedOkW H (fun fl => fl.tag = 7) := by
  unfold MergeFieldGenPlacedOkW
  apply subroutine_ok_of_sepWPp
  intro x Fr s0 hpc hrun hpre hsp
  have ⟨hcrl0, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  refine ⟨_, Fr, hpre_raw, ?_⟩
  conv => arg 4; dsimp only [mergeFieldGenRawSpecW]
  apply SepWPp.pure_left
  rintro ⟨hx0, hx1, hx2, hx3, hx4, htag, hOk, hFresh, hlen⟩
  obtain ⟨c, hfld⟩ := eq_recv_of_tag_eq_7 htag
  have hcOk : c.Ok := by rw [hfld] at hOk; exact hOk.1
  have hfresh : x.v.recv.length < maxReceiverChains := by rw [hfld] at hFresh; exact hFresh
  rw [hfld] at hx1 hx2
  dsimp only [GenField.tag, GenField.wt, CryptoVerification.LibsignalProtoCodec.WireType.toNat,
    BitVec.ofNat_eq_ofNat] at hx1 hx2
  have hx2' : BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x2)) &&& 255#64 = 2#64 :=
    zext64_trunc32_and_255_eq_of_trunc8_receiverChains hx2
  have hsp0 : s0.sp &&& 15#64 = 0#64 := eq_of_beq hsp
  have hsp240 : (s0.sp - 240#64) &&& 15#64 = 0#64 := sp_sub_240_aligned_receiverChains hsp0
  have hsp240_beq : ((s0.sp - 240#64) &&& 15#64 == 0#64) = true := beq_iff_eq.mpr hsp240
  have hCh' : subroutine_ok (lsProg_15 H) (lsmpl.base 11) chainMergeGenPlacedSpecW :=
    ls_call_ro_of_block (callerProg := lsProg_15 H) hCh
  have h2bc := @step_receiverChains_from_0x2bc_to_ret_placed_extW _ H hC.2.2.2
    (fun fl => fl.tag = 7) x c s0
  rw [stackAt_mergeFieldStack_split_receiverChains_extW s0.sp,
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
  apply sepWP_intro_rodata_tag7_placed_receiverChains_ext hcrl0
  wp_steps
  apply sepWP_drop_left_receiverChains
  apply SepWP.fold (prostChainGAt_default_of_cells_lit s0.sp) (by sep_frame)
  apply SepWP.fold (mfSavedRegs_intro_receiverChains s0.sp s0 c3) (by sep_frame)
  apply SepWP.fold (Entails.of_eq (stackAt_sub_to_chainMerge_receiverChains_extW (s0.sp - 240#64))) (by sep_frame)
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) ?_
  intro hcrl1
  refine call_frame_lscro_receiverChains_ext (ret_pc := (blkPl_15).base + 700#64) hcrl1 hCh'
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
    (by simp only [arm64_norm])
    (chainMergeGen_placed_pre_eq_extW x c (s0.sp - 232#64) (s0.sp - 240#64) _ hfld (by simp only [arm64_norm]))
    ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm], hcOk, hlen⟩
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
    (chainMergeGen_placed_post_eq_extW x c (s0.sp - 232#64) (s0.sp - 240#64) _ sm hfld ?_) rfl ?_
  · simp only [arm64_norm]
  simp only [sepConj_assoc]
  apply SepWPp.pure_left; rintro ⟨htr_m, hx0_m⟩
  have htr_m' : sm.trace = s0.trace := by simpa only [arm64_norm] using htr_m
  refine SepWPp.weaken_pre ?_
    (h2bc sm Fr c3 hfresh hfld hcrl2 hpcm hrunm hspm hsp_align_m htr_m' hx0_m hx20m hx26m hx27m hx28m hvregsm)
  have hsub32768 : (s0.sp - 240#64) - 32528#64 = s0.sp - 32768#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  exact Entails.of_eq (by rw [hsub32768]; ac_rfl)

end Placed

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains

