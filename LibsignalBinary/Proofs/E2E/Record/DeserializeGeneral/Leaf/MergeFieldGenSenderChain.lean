/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeSenderChainAux.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Tag-6 Leaf (`mergeFieldGenSenderChain_ok`) for `SessionStructure::merge_field`

Proves `mergeFieldGenSenderChain_ok` for `sender_chain` (tag `6`), writing `Chain::default()` at
`ss + 0x90` when `sender = none` and invoking `message::merge<Chain>`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenSenderChain

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (allocPanic)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

private theorem mergeField_fnAddr_eq_mf6g (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr mergeFieldName = b + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") := by
  have h1 := (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, mergeFieldName, h1]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
  sessionImg0 libsignalSessionCode
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg

@[local arm64_norm, local wp_norm]
private theorem calleeSavedVRegs_setPC_pre_mf6g (s : State) (v : BitVec 64) :
    calleeSavedVRegs (s.setPC v) = calleeSavedVRegs s := rfl

@[local arm64_norm, local wp_norm]
private theorem calleeSavedVRegs_setMem_setPC_pre_mf6g (s : State) (v : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC v).setMem m) = calleeSavedVRegs s := rfl

@[local arm64_norm]
private theorem bv_add_neg240_mf6g (sp0 : BitVec 64) :
    sp0 + bv% (2 ^ 64 - 240) = sp0 - 240#64 := by
  simp only [BitVec.sub_eq_add_neg]
  rfl

-- Pre-indexed load (`ldr x8, [x1, #0x90]!` at +0x10c) applies `setPC` before reading/writing
-- registers; commute register/SP reads past `setPC` and `setMem`.
@[local arm64_norm, local wp_norm]
private theorem sp_setPC_pre_mf6g (s : State) (v : BitVec 64) : (s.setPC v).sp = s.sp := rfl

@[local arm64_norm, local wp_norm]
private theorem sp_setMem_setPC_pre_mf6g (s : State) (v : BitVec 64) (m : Memory) :
    ((s.setPC v).setMem m).sp = s.sp := rfl

@[local arm64_norm, local wp_norm]
private theorem readReg64_setPC_pre_mf6g (s : State) (v : BitVec 64) (r : Reg) :
    (s.setPC v).readReg64 r = s.readReg64 r := rfl

@[local arm64_norm, local wp_norm]
private theorem readReg64_setMem_setPC_pre_mf6g (s : State) (v : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC v).setMem m).readReg64 r = s.readReg64 r := rfl

@[local arm64_norm, local wp_norm]
private theorem readReg32_setPC_pre_mf6g (s : State) (v : BitVec 64) (r : Reg) :
    (s.setPC v).readReg32 r = s.readReg32 r := rfl

@[local arm64_norm, local wp_norm]
private theorem readReg32_setMem_setPC_pre_mf6g (s : State) (v : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC v).setMem m).readReg32 r = s.readReg32 r := rfl

@[local arm64_norm, local wp_norm]
private theorem readReg_setPC_pre_mf6g (s : State) (v : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC v).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm, local wp_norm]
private theorem readReg_setMem_setPC_pre_mf6g (s : State) (v : BitVec 64) (m : Memory)
    (w : RegWidth) (r : Reg) :
    ((s.setPC v).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

private theorem sepWPp_of_sepWP_frozen_mf6g {prog : Program} {img : Obj.Image} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog mid s P (fun sm Pm =>
      img.FrozenLoaded sm → sm.symtab = img.symtab → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP_frozen hF hsym h

private theorem sepWPp_mono_pre_mf6g {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P ⊢ P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  exact h R (Satisfies.mono (sepConj_mono_left hent) hm) hL

private theorem sepWPp_drop_left_mf6g {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P2 Q Qp) :
    SepWPp prog ret s (P1 ∗ P2) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  exact h _ (Satisfies.of_sep_right hm) hL

private theorem setWidth8_setWidth64_setWidth32_mf6g (v : BitVec 64) :
    (((v.setWidth 32).setWidth 64).setWidth 8) = v.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  omega

private theorem genField_eq_sender_of_tag_eq_6 {fl : GenField} (h : fl.tag = 6) :
    ∃ c : ChainG, fl = .sender c := by
  cases fl <;> simp [GenField.tag] at h
  rename_i c
  exact ⟨c, rfl⟩

/-- All fields of `prostSSGAt A ss v` except `sender` at `ss + 0x90`. -/
def prostSSGRest (A : RustAlloc) (ss : BitVec 64) (v : SSG) : SepProp :=
  vecU8 A ss v.lik ∗ vecU8 A (ss + 0x18#64) v.rik ∗ vecU8 A (ss + 0x30#64) v.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.recv ∗
    vecU8 A (ss + 0x60#64) [] ∗ vecU8 A (ss + 0x78#64) [] ∗
    (match v.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗ ((ss + 0x110#64) ↦₃₂ 0#32) ∗
         memRegion (ss + 0x114#64) 4 ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗
         ((ss + 0x120#64) ↦₃₂ 0#32) ∗ memRegion (ss + 0x124#64) 4) ∗
    ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24 ∗
    ((ss + 0x148#64) ↦₃₂ v.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.prevCounter) ∗
    ((ss + 0x150#64) ↦₆₄ 0#64)

theorem prostSSGAt_sender_none_eq (A : RustAlloc) (ss : BitVec 64) (v : SSG)
    (hnone : v.sender = none) :
    prostSSGAt A ss v =
      ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96 ∗ prostSSGRest A ss v := by
  unfold prostSSGAt prostSSGRest
  rw [hnone]
  dsimp only
  ac_rfl

theorem prostSSGAt_sender_some_eq (A : RustAlloc) (ss : BitVec 64) (v : SSG) (c : ChainG) :
    prostSSGAt A ss (v.apply (.sender c)) =
      prostChainGAt A (ss + 0x90#64) c ∗ prostSSGRest A ss v := by
  rcases v with ⟨ver, lik, rik, root, prevCounter, recv, sender, pending⟩
  unfold prostSSGAt prostSSGRest SSG.apply
  dsimp only
  ac_rfl

theorem empty_vecOf_msgKey_entails (A : RustAlloc) (v a8 a16 : BitVec 64)
    (h8 : v + 8#64 = a8) (h16 : v + 16#64 = a16) :
    (v ↦₆₄ 0#64) ∗ (a8 ↦₆₄ 8#64) ∗ (a16 ↦₆₄ 0#64) ⊢
      vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) v [] := by
  unfold vecOf
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 8#64 ?_)
  unfold vecAt vecHeader vecBuf
  subst h8 h16
  have hp : (⌜([] : List MessageKeyGenerator).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0⌝ : SepProp) = emp := by
    simp
  rw [hp]
  simp only [emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

theorem default_cells_entail_prostChainGAt (A : RustAlloc) (ss : BitVec 64) :
    ((ss + 144#64) ↦₆₄ 0#64) ∗ ((ss + 152#64) ↦₆₄ 1#64) ∗ ((ss + 160#64) ↦₆₄ 0#64) ∗
    ((ss + 168#64) ↦₆₄ 0#64) ∗ ((ss + 176#64) ↦₆₄ 1#64) ∗ ((ss + 184#64) ↦₆₄ 0#64) ∗
    ((ss + 192#64) ↦₆₄ 0#64) ∗ ((ss + 200#64) ↦₆₄ 8#64) ∗ ((ss + 208#64) ↦₆₄ 0#64) ∗
    ((ss + 216#64) ↦₆₄ noneCap) ∗ memRegion (ss + 224#64) 24 ⊢
      prostChainGAt A (ss + 0x90#64) ChainG.empty := by
  unfold prostChainGAt ChainG.empty
  dsimp only
  have hv1 := empty_vecU8_entails_senderChain A (ss + 144#64) (ss + 152#64) (ss + 160#64)
    (by rw [BitVec.add_assoc]; rfl) (by rw [BitVec.add_assoc]; rfl)
  have hv2 := empty_vecU8_entails_senderChain A (ss + 144#64 + 0x18#64) (ss + 176#64) (ss + 184#64)
    (by simp only [BitVec.add_assoc]; rfl) (by simp only [BitVec.add_assoc]; rfl)
  have hv3 := empty_vecOf_msgKey_entails A (ss + 144#64 + 0x30#64) (ss + 200#64) (ss + 208#64)
    (by simp only [BitVec.add_assoc]; rfl) (by simp only [BitVec.add_assoc]; rfl)
  have ha2 : ss + 144#64 + 0x18#64 = ss + 168#64 := by rw [BitVec.add_assoc]; rfl
  have ha3 : ss + 144#64 + 0x30#64 = ss + 192#64 := by rw [BitVec.add_assoc]; rfl
  have ha4 : ss + 0x90#64 + 0x48#64 = ss + 216#64 := by rw [BitVec.add_assoc]; rfl
  have ha5 : ss + 0x90#64 + 0x50#64 = ss + 224#64 := by rw [BitVec.add_assoc]; rfl
  rw [ha2] at hv2
  rw [ha3] at hv3
  rw [ha2, ha3, ha4, ha5]
  refine Entails.trans ?_
    (sepConj_mono hv1 (sepConj_mono hv2 (sepConj_mono hv3 (Entails.refl _))))
  exact Entails.of_eq (by ac_rfl)

/-- Step `+0x000..+0x03c` (prologue + jump table dispatch for tag 6) and `+0x108..+0x144`
(`sender_chain` niche check, `Chain::default()` stores, and `bl 0x3974` to `message::merge<Chain>`). -/
private theorem step_mf6g_to_call_core (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (ss bufRef sp0 w80 w72 w64 w56 w48 w40 w32 w24 w16 w8 : BitVec 64)
    (u1 u2 u3 u4 u5 u6 u7 u8 u9 : BitVec 64)
    {s : State} {P F : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr mergeFieldName)
    (hadp : (((tripleRatchetProgAt b C ctl abs).fnAddr mergeFieldName + 40#64) &&&
      bv% (2 ^ 64 - 4096)) = b + 20480#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0)
    (halign : sp0 &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = ss)
    (hx1 : (s.readReg64 .x1).setWidth 32 = 6#32)
    (hx2 : (s.readReg64 .x2).setWidth 8 = 2#8)
    (hx3 : s.readReg64 .x3 = bufRef)
    (hx4 : (s.readReg64 .x4).setWidth 32 = 99#32)
    (hP : P = ((b + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 5)) ↦₈ᵣ 0x32#8) ∗
      (((ss + 0x90#64) ↦₆₄ noneCap) ∗
       ((ss + 152#64) ↦₆₄ u1) ∗ ((ss + 160#64) ↦₆₄ u2) ∗
       ((ss + 168#64) ↦₆₄ u3) ∗ ((ss + 176#64) ↦₆₄ u4) ∗
       ((ss + 184#64) ↦₆₄ u5) ∗ ((ss + 192#64) ↦₆₄ u6) ∗
       ((ss + 200#64) ↦₆₄ u7) ∗ ((ss + 208#64) ↦₆₄ u8) ∗
       ((ss + 216#64) ↦₆₄ u9) ∗ memRegion (ss + 224#64) 24) ∗
      (((sp0 - 80#64) ↦₆₄ w80) ∗ ((sp0 - 72#64) ↦₆₄ w72) ∗
       ((sp0 - 64#64) ↦₆₄ w64) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
       ((sp0 - 48#64) ↦₆₄ w48) ∗ ((sp0 - 40#64) ↦₆₄ w40) ∗
       ((sp0 - 32#64) ↦₆₄ w32) ∗ ((sp0 - 24#64) ↦₆₄ w24) ∗
       ((sp0 - 16#64) ↦₆₄ w16) ∗ ((sp0 - 8#64) ↦₆₄ w8)) ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = (tripleRatchetProgAt b C ctl abs).fnAddr mergeFieldName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) →
      s1.status = .Running →
      s1.sp = sp0 - 240#64 →
      s1.trace = s.trace →
      s1.readReg64 .lr = (tripleRatchetProgAt b C ctl abs).fnAddr mergeFieldName + 328#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 →
      s1.readReg64 .x1 = ss + 0x90#64 →
      s1.readReg64 .x2 = bufRef →
      (s1.readReg64 .x3).setWidth 32 = 99#32 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      post s1 (((b + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 5)) ↦₈ᵣ 0x32#8) ∗
        prostChainGAt A0 (ss + 0x90#64) ChainG.empty ∗ savedRegs_senderChain sp0 w56 s ∗ F)) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr mergeFieldName + bv% (2 ^ 64 + (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")))
      s P post := by
  mf6_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0 60
  mf6_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 264 324
  dsimp only [tripleRatchetProgAt] at hpc hadp hnext ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr mergeFieldName = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))) = prog
    reverting [Program.fetch, Program.externAt?]
  examples_hide_fetches
  subst hP
  have hx1' : s.readReg32 (Reg.gpr 1#5) = 6#32 := hx1
  have hx4' : s.readReg32 (Reg.gpr 4#5) = 99#32 := hx4
  have hnoneCap : noneCap = 0xffffffffffffffff#64 := rfl
  rw [hnoneCap]
  wp_steps
  apply SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (default_cells_entail_prostChainGAt A0 ss)))
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  refine hnext _ (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    ?_ (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
  have h0 : (((s.readReg64 (Reg.gpr 2#5)).setWidth 32).setWidth 64).setWidth 8 = 2#8 := by
    rw [setWidth8_setWidth64_setWidth32_mf6g]
    exact hx2
  simpa only [wp_norm, arm64_norm] using h0

private theorem step_mf6g_to_call (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (ss bufRef sp0 : BitVec 64)
    {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr mergeFieldName)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : sessionImg0.FrozenLoaded s)
    (hsym : s.symtab = sessionImg0.symtab)
    (hx0 : s.readReg64 .x0 = ss)
    (hx1 : (s.readReg64 .x1).setWidth 32 = 6#32)
    (hx2 : (s.readReg64 .x2).setWidth 8 = 2#8)
    (hx3 : s.readReg64 .x3 = bufRef)
    (hx4 : (s.readReg64 .x4).setWidth 32 = 99#32)
    (hP : P = ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96 ∗
      F ∗ stackAt sp0 mergeFieldStack)
    (hnext : ∀ (s1 : State) (w56 : BitVec 64),
      s1.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr mergeFieldName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) →
      s1.status = .Running →
      s1.sp = sp0 - 240#64 →
      s1.trace = s.trace →
      s1.readReg64 .lr = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr mergeFieldName + 328#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 →
      s1.readReg64 .x1 = ss + 0x90#64 →
      s1.readReg64 .x2 = bufRef →
      (s1.readReg64 .x3).setWidth 32 = 99#32 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      sessionImg0.FrozenLoaded s1 →
      s1.symtab = sessionImg0.symtab →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) (s.readReg64 .lr) s1
        (prostChainGAt A0 (ss + 0x90#64) ChainG.empty ∗
         stackAt (sp0 - 80#64) 16304 ∗ savedRegs_senderChain sp0 w56 s ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) (s.readReg64 .lr) s P Q Qp := by
  subst hP
  rw [stackAt_mergeFieldStack_split_senderChain sp0, memRegion96_sender_split_senderChain ss]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun w80 => SepWPp.exists_elim fun w72 =>
    SepWPp.exists_elim fun w64 => SepWPp.exists_elim fun w56 =>
    SepWPp.exists_elim fun w48 => SepWPp.exists_elim fun w40 =>
    SepWPp.exists_elim fun w32 => SepWPp.exists_elim fun w24 =>
    SepWPp.exists_elim fun w16 => SepWPp.exists_elim fun w8 =>
    SepWPp.exists_elim fun u9 => SepWPp.exists_elim fun u8 =>
    SepWPp.exists_elim fun u7 => SepWPp.exists_elim fun u6 =>
    SepWPp.exists_elim fun u5 => SepWPp.exists_elim fun u4 =>
    SepWPp.exists_elim fun u3 => SepWPp.exists_elim fun u2 =>
    SepWPp.exists_elim fun u1 => ?_
  apply sepWPp_intro_rodata_byte5_senderChain loads_sessionImg0 hF.roData
  apply sepWPp_of_sepWP_frozen_mf6g hF hsym
  have hb0 := ProofLib.ObjectLoad.base_aligned_of_loads loads_sessionImg0
  refine step_mf6g_to_call_core sessionImg0.base C ctl ss bufRef sp0
    w80 w72 w64 w56 w48 w40 w32 w24 w16 w8 u1 u2 u3 u4 u5 u6 u7 u8 u9
    (F := stackAt (sp0 - 80#64) 16304 ∗ F)
    hpc
    (adrp_0x46000_eq_senderChain hb0
      (mergeField_fnAddr_eq_mf6g sessionImg0.base C ctl abs))
    hrun hsp halign hx0 hx1 hx2 hx3 hx4 (by ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hlr1 hx0_1 hx1_1 hx2_1 hx3_1 hx26_1 hx27_1 hx28_1 hvregs1 hF1 hsym1
  apply sepWPp_drop_left_mf6g
  refine sepWPp_mono_pre_mf6g (Entails.of_eq (by ac_rfl))
    (hnext s1 w56 hpc1 hrun1 hsp1 htr1 hlr1 hx0_1 hx1_1 hx2_1 hx3_1 hx26_1 hx27_1 hx28_1 hvregs1 hF1 hsym1)

/-- Step `+0x148` (`cbz x0, +0x758`) and `+0x758..+0x770` (epilogue `ret`). -/
private theorem step_mf6g_epilogue (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (c : ChainG) (w56 : BitVec 64)
    {P_fld : GenField → Prop} {x : MergeFieldGenGhost} {R : SepProp}
    {s0 s : State} {P : SepProp}
    (hfl : x.fld = .sender c)
    (hpc : s.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr mergeFieldName + 328#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 240#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hP : P = prostChainGAt A0 (x.ss + 0x90#64) c ∗ prostSSGRest A0 x.ss x.v ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt (s0.sp - 80#64) 16304 ∗ savedRegs_senderChain s0.sp w56 s0) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (mergeFieldGenSpec P_fld).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (mergeFieldGenSpec P_fld).onPanic x s0 sf ∗ R)) := by
  mf6_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 328 328
  mf6_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1880 1904
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr mergeFieldName = entry
  generalize_entry (libsignalSessionCode.rebase sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))) = prog
    reverting [Program.fetch, Program.externAt?]
  examples_hide_fetches
  subst hP
  unfold savedRegs_senderChain
  have hsp_align240 := sp_sub_240_aligned_senderChain halign
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have hx26' : s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := hx28
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine ⟨?_, by simp only [arm64_norm, *],
    ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩⟩
  intro hm
  simp only [mergeFieldGenSpec, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩, ?_⟩
  rw [hfl, prostSSGAt_sender_some_eq A0 x.ss x.v c, stackAt_mergeFieldStack_split_senderChain s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
    s0.readReg64 (Reg.gpr 25#5), w56,
    s0.readReg64 (Reg.gpr 24#5), s0.readReg64 (Reg.gpr 23#5),
    s0.readReg64 (Reg.gpr 22#5), s0.readReg64 (Reg.gpr 21#5),
    s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5), ?_⟩
  rw [← hfl]
  convert hm using 1
  ac_rfl

theorem mergeFieldGenSenderChain_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) (hCh : ChainMergeGenOk C ctl abs) :
    MergeFieldGenOk C ctl (fun fl => fl.tag = 6) abs := by
  let _ := hC
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre halign_bool
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using halign_bool
  refine ⟨(mergeFieldGenSpec (fun fl => fl.tag = 6)).pre x s0, R, hpre, ?_⟩
  conv =>
    arg 4
    simp only [mergeFieldGenSpec, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, hx4, htag6, hok, hfresh, hlen, hF, hsym⟩ => ?_
  obtain ⟨c, hfl⟩ := genField_eq_sender_of_tag_eq_6 htag6
  have hv_none : x.v.sender = none := by
    simpa [hfl, GenField.Fresh] using hfresh
  have hc_ok : c.Ok := by
    rw [hfl, GenField.Ok] at hok
    exact hok.1
  have htag : BitVec.ofNat 32 x.fld.tag = 6#32 := by rw [hfl]; rfl
  have hwt : BitVec.ofNat 8 x.fld.wt.toNat = 2#8 := by rw [hfl]; rfl
  rw [htag] at hx1
  rw [hwt] at hx2
  rw [prostSSGAt_sender_none_eq A0 x.ss x.v hv_none]
  refine step_mf6g_to_call C ctl x.ss x.bufRef s0.sp
    (F := prostSSGRest A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail))
    hpc hrun rfl halign hF hsym hx0 hx1 hx2 hx3 hx4 (by ac_rfl) ?_
  intro s1 w56 hpc1 hrun1 hsp1 htr1 hlr1 hx0_1 hx1_1 hx2_1 hx3_1 hx26_1 hx27_1 hx28_1 hvregs1 hF1 hsym1
  rw [chainMerge_fnAddr_eq_senderChain] at hpc1
  have hsp1_aligned : s1.spAligned = true := by
    simp only [State.spAligned, hsp1, beq_iff_eq]
    exact sp_sub_240_aligned_senderChain halign
  have hpay : x.fld.payload ++ x.tail = c.payload ++ x.tail := by
    rw [hfl, GenField.payload]
  refine SepWPp.call
    (x := ChainMergeGenGhost.mk (x.ss + 0x90#64) c x.bufRef x.slot x.ptr x.tail)
    (F := prostSSGRest A0 x.ss x.v ∗
      memRegion (s0.sp - 16384#64) 3856 ∗
      memRegion (s0.sp - 240#64) 160 ∗
      savedRegs_senderChain s0.sp w56 s0)
    hCh hpc1 hrun1 hsp1_aligned hlr1 ?_ ?_ ?_ ?_
      (fun sf R' _ hoom => by simp only [chainMergeGenSpec, sepConj_assoc] at hoom; exact (not_satisfies_false_sepConj hoom).elim)
  · intro R' hm
    rw [stackAt_16304_to_chainMerge_senderChain s0.sp, hpay] at hm
    simp only [chainMergeGenSpec, hsp1, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_1, hx1_1, hx2_1, hx3_1, hc_ok, hpay ▸ hlen, hF1, hsym1⟩, ?_⟩
    convert hm using 1
    ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [chainMergeGenSpec, allocPanic, allocFailedIn, htr1] at hm ⊢
    exact allowPanic_frame id hm
  · intro s2 hpc2 hrun2 hsp2 hcs2
    rw [hsp1] at hsp2
    conv =>
      arg 4
      simp only [chainMergeGenSpec, hsp1, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨htr2, hx0_2⟩ => ?_
    refine step_mf6g_epilogue C ctl c w56 hfl hpc2 hrun2 hsp2 halign
      (by reg_chain) (hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1) hx0_2 (by reg_chain) (by reg_chain) (by reg_chain) ?_
    rw [stackAt_16304_to_chainMerge_senderChain s0.sp, hpay]
    ac_rfl

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenSenderChain
