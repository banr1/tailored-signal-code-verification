/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.StepsFront
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Defs
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.Pure
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenAux.Pure
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.Decode
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.StepsChains
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<SessionStructure as prost::Message>::encoded_len`: Prologue and Tags 1–7 (`+0x000..+0x1bc`)

Verifies the prologue, protobuf tags 1–5 (`+0x000..+0x110`), tag 6 (`sender_chain`, `272..352`), and
tag 7 (`receiver_chains`, `352..444`) of `SessionStructure::encoded_len` (`0x25fd0`) on `SP2Ext`.
-/

namespace CryptoVerification.E2E.Record.Serialization.SessionLenAux

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Serialization
open Proofs.libsignal.Hooks2

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm]
  bv_sub_add_lit BitVec.toNat_zero
  sessHwVarintLen_eq_encodeVarint_length
  sessHwVarintLen_bvShift_eq_encodeVarint_length
  Prost.ofNat_countLeadingZeros_64
  Prost.ofNat_countLeadingZeros_32
  Prost.truncate32_ofNat64
  sess_truncate32_zext64_lsr6
  sessHwVarintLen_w32_eq_encodeVarint_length
  sessHwVarintLen_w32_natShift_eq_encodeVarint_length
  Prost.noneCap_add_one_beq_zero
  Prost.noneCap_add_one_bne_zero
  Prost.optU32Tag_beq_one
  Prost.optU32Tag_bne_one
  Prost.zext64_optU32Tag_truncate32
  sess_ule_zero_64
  sess_ult_zero_64

@[local simp, local arm64_norm]
theorem add_neg64_eq_sub64' (x : BitVec 64) :
    x + bv% (2 ^ 64 - 64) = x - 64#64 := by
  bv_omega

theorem fnAddr_chainLen_eq_ext (b : BitVec 64) (ext : String → Option (State → State)) :
    (SP2Ext b ext).fnAddr chainLenName =
      (SP2Ext b ext).fnAddr sessionLenName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encoded_len") := by
  simp only [SP2Ext, contractProg, Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len"),
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encoded_len")]
  bv_omega

/-- Invoke `hchain : subroutine_ok (SP2Ext b ext) ((SP2Ext b ext).fnAddr chainLenName) (chainLenSpec A)`
at a `bl` target state on `protoChainAt`. -/
theorem call_protoChainLen_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hchain : subroutine_ok (SP2Ext b ext) ((SP2Ext b ext).fnAddr chainLenName) (chainLenSpec A))
    (a ret_pc : BitVec 64) (gc : ChainGhost × ReceiverChain)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext b ext).fnAddr sessionLenName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encoded_len"))
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = a)
    (hfit : (encChainMem gc).length < 2 ^ 32)
    (hP : P = (protoChainAt A gc a ∗ stackAt s.sp chainLenStack) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (encChainMem gc).length →
      CalleeSavedPreserved s sf →
      SepWPp (SP2Ext b ext) ret sf P Q Qp) :
    SepWPp (SP2Ext b ext) ret s P Q Qp := by
  intro R hm hL
  have hpc' : s.pc = (SP2Ext b ext).fnAddr chainLenName := by
    rw [fnAddr_chainLen_eq_ext, hpc]
  have hpre : s.mem ⊨ (chainLenSpec A).pre ⟨a, gc⟩ s ∗ (F ∗ R) := by
    dsimp only [chainLenSpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hfit⟩, ?_⟩
    rw [← sepConj_assoc, ← sepConj_assoc, ← hP]
    exact hm
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hchain.no_fault_before_outcome ⟨a, gc⟩ (F ∗ R) s hpc' hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
  · dsimp only [chainLenSpec] at hpost
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0_m, htr_m⟩, hpost⟩
    rw [← sepConj_assoc, ← sepConj_assoc, ← hP] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm htr_m hx0_m hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [chainLenSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [chainLenSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

/-- Invoke `hchain : subroutine_ok (SP2Ext b ext) ((SP2Ext b ext).fnAddr chainLenName) (chainLenSpec A)`
at a `bl` target state on `chainAt`. -/
theorem call_chainLen_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hchain : subroutine_ok (SP2Ext b ext) ((SP2Ext b ext).fnAddr chainLenName) (chainLenSpec A))
    (a ret_pc : BitVec 64) (gc : ChainGhost × ReceiverChain)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext b ext).fnAddr sessionLenName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encoded_len"))
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = a)
    (hfit : (encChainMem gc).length < 2 ^ 32)
    (hP : P = (chainAt A gc a ∗ stackAt s.sp chainLenStack) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (encChainMem gc).length →
      CalleeSavedPreserved s sf →
      SepWPp (SP2Ext b ext) ret sf P Q Qp) :
    SepWPp (SP2Ext b ext) ret s P Q Qp := by
  have hP' : P = (protoChainAt A gc a ∗ stackAt s.sp chainLenStack) ∗
      (⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗ F) := by
    rw [hP, chainAt_eq_protoChainAt A gc a]; ac_rfl
  exact call_protoChainLen_ext b A ext hchain a ret_pc gc
    hpc hrun hsp hlr hx0 hfit hP' hnext

theorem step_sessLen_f1_ext (b : BitVec 64) (ext : String → Option (State → State))
    (ss sp v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64)
    (G : SessionGhost) (m : Session (List (BitVec 8)))
    (hloc_fit : (bytesField 2 G.localIk.bytes).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext b ext).fnAddr sessionLenName)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = ss)
    (hP : P = (tags1to5Cells ss G m ∗ frameCells sp v64 v56 v48 v40 v32 v24 v16 v8) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if G.localIk.bytes = [] then
        (SP2Ext b ext).fnAddr sessionLenName + 248#64
      else
        (SP2Ext b ext).fnAddr sessionLenName + 68#64) →
      sm.status = .Running →
      sm.sp = sp - 64#64 →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64 (uint32Field 1 m.state.sessionVersion).length →
      sm.readReg64 .x9 = BitVec.ofNat 64 G.localIk.bytes.length →
      SessLenCalleeSaved s sm →
      SepWPp (SP2Ext b ext) ret sm
        ((tags1to5Cells ss G m ∗
          frameCells sp (s.readReg64 .fp) (s.readReg64 .lr)
            (s.readReg64 .x24) (s.readReg64 .x23)
            (s.readReg64 .x22) (s.readReg64 .x21)
            (s.readReg64 .x20) (s.readReg64 .x19)) ∗ F) Q Qp) :
    SepWPp (SP2Ext b ext) ret s P Q Qp := by
  sesslen_fetches b (Rust.withPanics ext) 0 68
  sesslen_fetches b (Rust.withPanics ext) 236 248
  generalize_entry (SP2Ext b ext).fnAddr sessionLenName = entry
  examples_hide_fetches
  have hloc_beq := ofNat64_length_beq_zero_of_bytesField_lt hloc_fit
  have hloc_bne := ofNat64_length_bne_zero_of_bytesField_lt hloc_fit
  subst hP
  have hT : tags1to5Cells ss G m =
      ((ss + 16#64) ↦₆₄ BitVec.ofNat 64 G.localIk.bytes.length) ∗
      ((ss + 40#64) ↦₆₄ BitVec.ofNat 64 G.remoteIk.bytes.length) ∗
      ((ss + 64#64) ↦₆₄ 32#64) ∗
      ((ss + 328#64) ↦₃₂ m.state.sessionVersion) ∗
      ((ss + 332#64) ↦₃₂ m.state.previousCounter) := rfl
  have hFr0 : frameCells sp v64 v56 v48 v40 v32 v24 v16 v8 =
      ((sp - 64#64) ↦₆₄ v64) ∗ ((sp - 56#64) ↦₆₄ v56) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) := rfl
  have hFr1 : frameCells sp (s.readReg64 .fp) (s.readReg64 .lr)
        (s.readReg64 .x24) (s.readReg64 .x23)
        (s.readReg64 .x22) (s.readReg64 .x21)
        (s.readReg64 .x20) (s.readReg64 .x19) =
      ((sp - 64#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 56#64) ↦₆₄ s.readReg64 .lr) ∗
      ((sp - 48#64) ↦₆₄ s.readReg64 .x24) ∗ ((sp - 40#64) ↦₆₄ s.readReg64 .x23) ∗
      ((sp - 32#64) ↦₆₄ s.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .x21) ∗
      ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19) := rfl
  rw [hT, hFr0]
  by_cases hver : m.state.sessionVersion = 0#32
  · have hver_beq : (m.state.sessionVersion == 0#32) = true := beq_iff_eq.mpr hver
    apply SepWPp.of_sepWP (mid := if G.localIk.bytes = [] then entry + bv% (248) else entry + bv% (68))
    wp_steps
    apply SepWP.done (by cases G.localIk.bytes <;> simp_all) (by simp_all)
    rw [← hT, ← hFr1]
    exact hnext _ (by cases G.localIk.bytes <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [uint32Field]) (by simp_all)
      (by simp_all [SessLenCalleeSaved])
  · have hver_beq : (m.state.sessionVersion == 0#32) = false := beq_eq_false_iff_ne.mpr hver
    have henc := bv_uint32Field_nonzero_length (t := 1) hver rfl
    apply SepWPp.of_sepWP (mid := if G.localIk.bytes = [] then entry + bv% (248) else entry + bv% (68))
    wp_steps
    apply SepWP.done (by cases G.localIk.bytes <;> simp_all) (by simp_all)
    rw [← hT, ← hFr1]
    exact hnext _ (by cases G.localIk.bytes <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_f2_ext (b : BitVec 64) (ext : String → Option (State → State))
    (ss : BitVec 64) (G : SessionGhost) (m : Session (List (BitVec 8))) (s1 : Nat)
    (hrem_fit : (bytesField 3 G.remoteIk.bytes).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if G.localIk.bytes = [] then
      (SP2Ext b ext).fnAddr sessionLenName + 248#64
    else
      (SP2Ext b ext).fnAddr sessionLenName + 68#64))
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 G.localIk.bytes.length)
    (hP : P = tags1to5Cells ss G m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if G.remoteIk.bytes = [] then
        (SP2Ext b ext).fnAddr sessionLenName + 144#64
      else
        (SP2Ext b ext).fnAddr sessionLenName + 108#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1 + (bytesField 2 G.localIk.bytes).length) →
      sm.readReg64 .x9 = BitVec.ofNat 64 G.remoteIk.bytes.length →
      SessLenCalleeSaved s sm →
      SepWPp (SP2Ext b ext) ret sm P Q Qp) :
    SepWPp (SP2Ext b ext) ret s P Q Qp := by
  sesslen_fetches b (Rust.withPanics ext) 68 108
  sesslen_fetches b (Rust.withPanics ext) 136 144
  sesslen_fetches b (Rust.withPanics ext) 248 264
  generalize_entry (SP2Ext b ext).fnAddr sessionLenName = entry
  examples_hide_fetches
  have hrem_beq := ofNat64_length_beq_zero_of_bytesField_lt hrem_fit
  have hrem_bne := ofNat64_length_bne_zero_of_bytesField_lt hrem_fit
  subst hP
  have hT : tags1to5Cells ss G m =
      ((ss + 16#64) ↦₆₄ BitVec.ofNat 64 G.localIk.bytes.length) ∗
      ((ss + 40#64) ↦₆₄ BitVec.ofNat 64 G.remoteIk.bytes.length) ∗
      ((ss + 64#64) ↦₆₄ 32#64) ∗
      ((ss + 328#64) ↦₃₂ m.state.sessionVersion) ∗
      ((ss + 332#64) ↦₃₂ m.state.previousCounter) := rfl
  rw [hT]
  by_cases hloc : G.localIk.bytes = []
  · simp only [hloc, ↓reduceIte] at hpc
    by_cases hrem : G.remoteIk.bytes = []
    · have hrem_b : (G.remoteIk.bytes == []) = true := beq_iff_eq.mpr hrem
      have hrem_bn : (G.remoteIk.bytes != []) = false := bne_eq_false_iff_eq.mpr hrem
      apply SepWPp.of_sepWP (mid := entry + bv% (144))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hT]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [bytesField]) (by simp_all)
        (by simp_all [SessLenCalleeSaved])
    · have hrem_b : (G.remoteIk.bytes == []) = false := beq_eq_false_iff_ne.mpr hrem
      have hrem_bn : (G.remoteIk.bytes != []) = true := bne_iff_ne.mpr hrem
      apply SepWPp.of_sepWP (mid := entry + bv% (108))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hT]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [bytesField]) (by simp_all)
        (by simp_all [SessLenCalleeSaved])
  · simp only [hloc, ↓reduceIte] at hpc
    have henc := bv_bytesField_nonempty_length (t := 2) hloc rfl
    have hadd := bv_add_ofNat_comm s1 (bytesField 2 G.localIk.bytes).length
    by_cases hrem : G.remoteIk.bytes = []
    · have hrem_b : (G.remoteIk.bytes == []) = true := beq_iff_eq.mpr hrem
      have hrem_bn : (G.remoteIk.bytes != []) = false := bne_eq_false_iff_eq.mpr hrem
      apply SepWPp.of_sepWP (mid := entry + bv% (144))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hT]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all [SessLenCalleeSaved])
    · have hrem_b : (G.remoteIk.bytes == []) = false := beq_eq_false_iff_ne.mpr hrem
      have hrem_bn : (G.remoteIk.bytes != []) = true := bne_iff_ne.mpr hrem
      apply SepWPp.of_sepWP (mid := entry + bv% (108))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hT]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_f3_ext (b : BitVec 64) (ext : String → Option (State → State))
    (ss : BitVec 64) (G : SessionGhost) (m : Session (List (BitVec 8))) (s12 : Nat)
    (hfit : s12 + (bytesField 3 G.remoteIk.bytes).length +
      (bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if G.remoteIk.bytes = [] then
      (SP2Ext b ext).fnAddr sessionLenName + 144#64
    else
      (SP2Ext b ext).fnAddr sessionLenName + 108#64))
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s12)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 G.remoteIk.bytes.length)
    (hP : P = tags1to5Cells ss G m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (SP2Ext b ext).fnAddr sessionLenName + 188#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64
        (s12 + (bytesField 3 G.remoteIk.bytes).length +
         (bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)).length) →
      SessLenCalleeSaved s sm →
      SepWPp (SP2Ext b ext) ret sm P Q Qp) :
    SepWPp (SP2Ext b ext) ret s P Q Qp := by
  sesslen_fetches b (Rust.withPanics ext) 108 188
  generalize_entry (SP2Ext b ext).fnAddr sessionLenName = entry
  examples_hide_fetches
  have hroot := bytesField_rootKey_length m.state.rootKey
  have hfit3 : s12 + (bytesField 3 G.remoteIk.bytes).length < 2 ^ 64 := by omega
  have hcc4 := ult_ofNat_add_of_lt (a := s12 + (bytesField 3 G.remoteIk.bytes).length) (b := 34)
    (by omega)
  have hadd4 := bv_add_ofNat_comm (s12 + (bytesField 3 G.remoteIk.bytes).length) 34
  subst hP
  have hT : tags1to5Cells ss G m =
      ((ss + 16#64) ↦₆₄ BitVec.ofNat 64 G.localIk.bytes.length) ∗
      ((ss + 40#64) ↦₆₄ BitVec.ofNat 64 G.remoteIk.bytes.length) ∗
      ((ss + 64#64) ↦₆₄ 32#64) ∗
      ((ss + 328#64) ↦₃₂ m.state.sessionVersion) ∗
      ((ss + 332#64) ↦₃₂ m.state.previousCounter) := rfl
  rw [hT]
  by_cases hrem : G.remoteIk.bytes = []
  · simp only [hrem, ↓reduceIte, bytesField, List.length_nil, Nat.add_zero] at hpc hcc4 hadd4
    apply SepWPp.of_sepWP (mid := entry + bv% (188))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hT]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [bytesField]) (by simp_all [SessLenCalleeSaved])
  · simp only [hrem, ↓reduceIte] at hpc
    have henc3 := bv_bytesField_nonempty_length (t := 3) hrem rfl
    have hcc3 := ult_ofNat_add_of_lt hfit3
    have hadd3 := bv_add_ofNat_comm s12 (bytesField 3 G.remoteIk.bytes).length
    apply SepWPp.of_sepWP (mid := entry + bv% (188))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hT]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_f4_ext (b : BitVec 64) (ext : String → Option (State → State))
    (ss : BitVec 64) (G : SessionGhost) (m : Session (List (BitVec 8))) (s1234 : Nat)
    (hfit : s1234 + (uint32Field 5 m.state.previousCounter).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext b ext).fnAddr sessionLenName + 188#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1234)
    (hP : P = tags1to5Cells ss G m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (SP2Ext b ext).fnAddr sessionLenName + 272#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x20 = BitVec.ofNat 64 (s1234 + (uint32Field 5 m.state.previousCounter).length) →
      SessLenCalleeSaved s sm →
      SepWPp (SP2Ext b ext) ret sm P Q Qp) :
    SepWPp (SP2Ext b ext) ret s P Q Qp := by
  sesslen_fetches b (Rust.withPanics ext) 188 232
  sesslen_fetches b (Rust.withPanics ext) 264 272
  generalize_entry (SP2Ext b ext).fnAddr sessionLenName = entry
  examples_hide_fetches
  subst hP
  have hT : tags1to5Cells ss G m =
      ((ss + 16#64) ↦₆₄ BitVec.ofNat 64 G.localIk.bytes.length) ∗
      ((ss + 40#64) ↦₆₄ BitVec.ofNat 64 G.remoteIk.bytes.length) ∗
      ((ss + 64#64) ↦₆₄ 32#64) ∗
      ((ss + 328#64) ↦₃₂ m.state.sessionVersion) ∗
      ((ss + 332#64) ↦₃₂ m.state.previousCounter) := rfl
  rw [hT]
  by_cases hprev : m.state.previousCounter = 0#32
  · have hprev_beq : (m.state.previousCounter == 0#32) = true := beq_iff_eq.mpr hprev
    apply SepWPp.of_sepWP (mid := entry + bv% (272))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hT]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [uint32Field]) (by simp_all [SessLenCalleeSaved])
  · have hprev_beq : (m.state.previousCounter == 0#32) = false := beq_eq_false_iff_ne.mpr hprev
    have henc := bv_uint32Field_nonzero_length (t := 5) hprev rfl
    have hcc := ule_ofNat_add_of_lt hfit
    have hcc_ult := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s1234 (uint32Field 5 m.state.previousCounter).length
    apply SepWPp.of_sepWP (mid := entry + bv% (272))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hT]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])

/-! ## Tag 6 (`sender_chain` @ `ss + 144`, `272..352`) -/

theorem step_sessLen_sender_pre_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (ss : BitVec 64) (g : SenderChainGhost) (sc : SenderChain)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext b ext).fnAddr sessionLenName + 272#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hP : P = protoChainAt A (senderGhostAsChain g, senderAsChain sc) (ss + 144#64) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (SP2Ext b ext).fnAddr sessionLenName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encoded_len") →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = ss + 144#64 →
      sm.readReg64 .lr = (SP2Ext b ext).fnAddr sessionLenName + 292#64 →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      SessLenCalleeSaved s sm →
      SepWPp (SP2Ext b ext) ret sm P Q Qp) :
    SepWPp (SP2Ext b ext) ret s P Q Qp := by
  intro R hm hL
  have hm_cap : s.mem ⊨ protoChainAt A (senderGhostAsChain g, senderAsChain sc) (ss + 144#64) ∗ (F ∗ R) := by
    rw [← sepConj_assoc, ← hP]; exact hm
  have hcap_lt : (senderGhostAsChain g).srk.cap.toNat < 2 ^ 63 := chainAt_srk_cap_lt hm_cap
  have hcap_beq : (g.srk.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hcap_lt
  clear hm_cap
  revert R hm hL
  change SepWPp (SP2Ext b ext) ret s P Q Qp
  sesslen_fetches b (Rust.withPanics ext) 272 292
  generalize_entry (SP2Ext b ext).fnAddr sessionLenName = entry
  examples_hide_fetches
  subst hP
  have hexp := chainAt_expose_cap A (senderGhostAsChain g, senderAsChain sc) (ss + 144#64)
  conv at hexp => rhs; dsimp only [senderGhostAsChain]
  rw [hexp]
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encoded_len"))
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  rw [← hexp]
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_sender_post_ext (b : BitVec 64)
    (ext : String → Option (State → State))
    (ss : BitVec 64) (gc : ChainGhost × ReceiverChain) (s1_5 : Nat)
    (hfit_sum : s1_5 + (lenField 6 (encChainMem gc)).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext b ext).fnAddr sessionLenName + 292#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 (encChainMem gc).length)
    (hx19 : s.readReg64 .x19 = ss)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 s1_5)
    (hnext : ∀ sm : State,
      sm.pc = (SP2Ext b ext).fnAddr sessionLenName + 352#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x21 = BitVec.ofNat 64 (s1_5 + (lenField 6 (encChainMem gc)).length) →
      SessLenCalleeSaved s sm →
      SepWPp (SP2Ext b ext) ret sm P Q Qp) :
    SepWPp (SP2Ext b ext) ret s P Q Qp := by
  sesslen_fetches b (Rust.withPanics ext) 292 340
  generalize_entry (SP2Ext b ext).fnAddr sessionLenName = entry
  examples_hide_fetches
  have hfit_v : (encChainMem gc).length +
      (encodeVarint (BitVec.ofNat 64 (encChainMem gc).length)).length + 1 < 2 ^ 64 := by
    have := lenField_length (t := 6) (encChainMem gc) rfl; omega
  have henc := bv_lenField_length (t := 6) (bs := encChainMem gc) rfl
  have hls := ule_lenField_varint_false hfit_v
  have hult := ult_varint_lenField hfit_v
  rw [show (encChainMem gc).length +
      (encodeVarint (BitVec.ofNat 64 (encChainMem gc).length)).length + 1 =
      (lenField 6 (encChainMem gc)).length by
    rw [lenField_length (t := 6) (encChainMem gc) rfl]; omega] at hls hult
  have hcc := ule_ofNat_add_of_lt hfit_sum
  have hcc_ult := ult_ofNat_add_of_lt hfit_sum
  have hadd := bv_add_ofNat_comm s1_5 (lenField 6 (encChainMem gc)).length
  apply SepWPp.of_sepWP (mid := entry + bv% (352))
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_f5_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hchain : subroutine_ok (SP2Ext b ext) ((SP2Ext b ext).fnAddr chainLenName) (chainLenSpec A))
    (ss : BitVec 64) (G : SessionGhost) (m : Session (List (BitVec 8))) (s1_5 : Nat)
    (hfit_sender : (encSenderFieldMem G.sender m.state.senderChain).length < 2 ^ 32)
    (hfit_sum : s1_5 + (encSenderFieldMem G.sender m.state.senderChain).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext b ext).fnAddr sessionLenName + 272#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = ss)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 s1_5)
    (hP : P = (optSenderChainAt A (ss + 144#64) G.sender m.state.senderChain ∗
      stackAt s.sp chainLenStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (SP2Ext b ext).fnAddr sessionLenName + 352#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x21 = BitVec.ofNat 64
        (s1_5 + (encSenderFieldMem G.sender m.state.senderChain).length) →
      SessLenCalleeSaved s sm →
      SepWPp (SP2Ext b ext) ret sm P Q Qp) :
    SepWPp (SP2Ext b ext) ret s P Q Qp := by
  cases hgs : G.sender with
  | none =>
    cases hsc : m.state.senderChain with
    | none =>
      sesslen_fetches b (Rust.withPanics ext) 272 288
      sesslen_fetches b (Rust.withPanics ext) 344 352
      generalize_entry (SP2Ext b ext).fnAddr sessionLenName = entry
      examples_hide_fetches
      have hP0 : P = (((ss + 144#64) ↦₆₄ noneCap ∗ memRegion (ss + 144#64 + 8#64) 96) ∗
          stackAt s.sp chainLenStack) ∗ F := by
        rw [hP, hgs, hsc]; rfl
      rw [hP0]
      apply SepWPp.of_sepWP (mid := entry + bv% (352))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP0]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all [encSenderFieldMem]) (by simp_all [SessLenCalleeSaved])
    | some sc =>
      intro R hm _
      rw [hP, hgs, hsc] at hm
      dsimp only [optSenderChainAt] at hm
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
      exact hm.1.elim
  | some g =>
    cases hsc : m.state.senderChain with
    | none =>
      intro R hm _
      rw [hP, hgs, hsc] at hm
      dsimp only [optSenderChainAt] at hm
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
      exact hm.1.elim
    | some sc =>
      have hopt_eq := optSenderChainAt_some_eq_sessLen A (ss + 144#64) g sc
      have hP' : P = protoChainAt A (senderGhostAsChain g, senderAsChain sc) (ss + 144#64) ∗
          (⌜g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
            Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
            g.srk.bytes.length = 33⌝ ∗
           stackAt s.sp chainLenStack ∗ F) := by
        rw [hP, hgs, hsc, hopt_eq]; ac_rfl
      simp only [hgs, hsc, encSenderFieldMem] at hfit_sender hfit_sum
      have hfit_chain : (encChainMem (senderGhostAsChain g, senderAsChain sc)).length < 2 ^ 32 := by
        have hle : (encChainMem (senderGhostAsChain g, senderAsChain sc)).length ≤
            (lenField 6 (encChainMem (senderGhostAsChain g, senderAsChain sc))).length := by
          rw [lenField_length (encChainMem (senderGhostAsChain g, senderAsChain sc)) rfl]; omega
        omega
      refine step_sessLen_sender_pre_ext b A ext ss g sc hpc hrun hx19 hP' ?_
      intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hlr1 hx19_1 hx20_1 hcs1
      have hsp1_align : s1.spAligned = true := by
        simpa only [State.spAligned, hsp1] using hsp
      have hP1 : P = (protoChainAt A (senderGhostAsChain g, senderAsChain sc) (ss + 144#64) ∗
          stackAt s1.sp chainLenStack) ∗
          (⌜g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
            Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
            g.srk.bytes.length = 33⌝ ∗ F) := by
        rw [hsp1, hP']; ac_rfl
      refine call_protoChainLen_ext b A ext hchain (ss + 144#64)
        ((SP2Ext b ext).fnAddr sessionLenName + 292#64)
        (senderGhostAsChain g, senderAsChain sc)
        hpc1 hrun1 hsp1_align hlr1 hx0_1 hfit_chain hP1 ?_
      intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hcs2
      have hx19_2 : s2.readReg64 .x19 = ss := hcs2.1.trans hx19_1
      have hx20_2 : s2.readReg64 .x20 = BitVec.ofNat 64 s1_5 :=
        (hcs2.2.1.trans hx20_1).trans hx20
      refine step_sessLen_sender_post_ext b ext ss
        (senderGhostAsChain g, senderAsChain sc) s1_5
        hfit_sum hpc2 hrun2 hx0_2 hx19_2 hx20_2 ?_
      intro s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx21_3 hcs3
      refine hnext s3 hpc3 hrun3 (hsp3.trans (hsp2.trans hsp1)) (htr3.trans (htr2.trans htr1))
        hx19_3 ?_ (hcs1.trans ((SessLenCalleeSaved.of_calleeSavedPreserved hcs2).trans hcs3))
      simpa only [hgs, hsc, encSenderFieldMem] using hx21_3

/-! ## Tag 7 (`receiver_chains` @ `ss + 72`, `352..444` and `512..520`) -/

theorem step_sessLen_loop_pre_ext (b : BitVec 64)
    (ext : String → Option (State → State))
    (ptr : BitVec 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext b ext).fnAddr sessionLenName + 372#64)
    (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = ptr)
    (hnext : ∀ sm : State,
      sm.pc = (SP2Ext b ext).fnAddr sessionLenName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encoded_len") →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = ptr →
      sm.readReg64 .lr = (SP2Ext b ext).fnAddr sessionLenName + 380#64 →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = ptr →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x24 = s.readReg64 .x24 →
      SessLenCalleeSaved s sm →
      SepWPp (SP2Ext b ext) ret sm P Q Qp) :
    SepWPp (SP2Ext b ext) ret s P Q Qp := by
  sesslen_fetches b (Rust.withPanics ext) 372 380
  generalize_entry (SP2Ext b ext).fnAddr sessionLenName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encoded_len"))
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_loop_post_ext (b : BitVec 64)
    (ext : String → Option (State → State))
    (ptr : BitVec 64) (gc : ChainGhost × ReceiverChain) (acc n_rem : Nat)
    (hfit_acc : acc + chainNoKeyLen gc < 2 ^ 64)
    (hn_rem : n_rem + 1 < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext b ext).fnAddr sessionLenName + 380#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 (encChainMem gc).length)
    (hx20 : s.readReg64 .x20 = ptr)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 acc)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (n_rem + 1))
    (hnext : ∀ sm : State,
      sm.pc = (if n_rem = 0 then
        (SP2Ext b ext).fnAddr sessionLenName + 428#64
      else
        (SP2Ext b ext).fnAddr sessionLenName + 372#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = ptr + 104#64 →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = BitVec.ofNat 64 (acc + chainNoKeyLen gc) →
      sm.readReg64 .x24 = BitVec.ofNat 64 n_rem →
      SessLenCalleeSaved s sm →
      SepWPp (SP2Ext b ext) ret sm P Q Qp) :
    SepWPp (SP2Ext b ext) ret s P Q Qp := by
  sesslen_fetches b (Rust.withPanics ext) 380 428
  generalize_entry (SP2Ext b ext).fnAddr sessionLenName = entry
  examples_hide_fetches
  have hfit_c : (encChainMem gc).length +
      (encodeVarint (BitVec.ofNat 64 (encChainMem gc).length)).length < 2 ^ 64 := by
    have : chainNoKeyLen gc = (encChainMem gc).length +
        (encodeVarint (BitVec.ofNat 64 (encChainMem gc).length)).length := rfl
    omega
  have hadd_c : BitVec.ofNat 64 (encChainMem gc).length +
      BitVec.ofNat 64 (encodeVarint (BitVec.ofNat 64 (encChainMem gc).length)).length =
      BitVec.ofNat 64 (chainNoKeyLen gc) := by
    rw [← BitVec.ofNat_add]; rfl
  have hcc_c : BitVec.ult (BitVec.ofNat 64 (chainNoKeyLen gc))
      (BitVec.ofNat 64 (encChainMem gc).length) = false := by
    have h := ult_ofNat_add_of_lt (a := (encodeVarint (BitVec.ofNat 64 (encChainMem gc).length)).length)
      (b := (encChainMem gc).length) (by omega)
    rwa [Nat.add_comm] at h
  have hadd_acc := bv_add_ofNat_comm acc (chainNoKeyLen gc)
  have hcc_acc := ult_ofNat_add_of_lt hfit_acc
  have hsub1 := bv_sub_one_ofNat_succ n_rem
  have hadd_neg1 := bv_add_neg1_ofNat_succ n_rem
  have hrem_beq1 := ofNat64_succ_beq_one_of_lt hn_rem
  have hrem_beq := ofNat64_beq_zero_of_lt (n := n_rem) (by omega)
  have hrem_bne := ofNat64_bne_zero_of_lt (n := n_rem) (by omega)
  apply SepWPp.of_sepWP (mid := if n_rem = 0 then entry + bv% (428) else entry + bv% (372))
  wp_steps
  apply SepWP.done (by cases n_rem <;> simp_all) (by simp_all)
  exact hnext _ (by cases n_rem <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_chains_loop_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hchain : subroutine_ok (SP2Ext b ext) ((SP2Ext b ext).fnAddr chainLenName) (chainLenSpec A))
    : ∀ (rest : List (ChainGhost × ReceiverChain)) (gc : ChainGhost × ReceiverChain)
        (ptr : BitVec 64) (acc : Nat)
        {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop},
      acc + chainsNoKeySum (gc :: rest) < 2 ^ 32 →
      rest.length + 1 < 2 ^ 64 →
      s.pc = (SP2Ext b ext).fnAddr sessionLenName + 372#64 →
      s.status = .Running →
      s.spAligned = true →
      s.readReg64 .x20 = ptr →
      s.readReg64 .x23 = BitVec.ofNat 64 acc →
      s.readReg64 .x24 = BitVec.ofNat 64 (rest.length + 1) →
      P = (arrayAt (chainAt A) 104 ptr (gc :: rest) ∗ stackAt s.sp chainLenStack) ∗ F →
      (∀ sm : State,
        sm.pc = (SP2Ext b ext).fnAddr sessionLenName + 428#64 →
        sm.status = .Running →
        sm.sp = s.sp →
        sm.trace = s.trace →
        sm.readReg64 .x19 = s.readReg64 .x19 →
        sm.readReg64 .x21 = s.readReg64 .x21 →
        sm.readReg64 .x22 = s.readReg64 .x22 →
        sm.readReg64 .x23 = BitVec.ofNat 64 (acc + chainsNoKeySum (gc :: rest)) →
        SessLenCalleeSaved s sm →
        SepWPp (SP2Ext b ext) ret sm P Q Qp) →
      SepWPp (SP2Ext b ext) ret s P Q Qp
  | [], gc, ptr, acc, ret, s, P, F, Q, Qp,
      hfit, hlen, hpc, hrun, hsp, hx20, hx23, hx24, hP, hnext => by
    simp only [chainsNoKeySum, Nat.add_zero] at hfit
    have hfit_c : (encChainMem gc).length < 2 ^ 32 := by
      have : (encChainMem gc).length ≤ chainNoKeyLen gc := by unfold chainNoKeyLen; omega
      omega
    refine step_sessLen_loop_pre_ext b ext ptr hpc hrun hx20 ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hlr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hcs1
    have hsp1_align : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp
    have hP1 : P = (chainAt A gc ptr ∗ stackAt s1.sp chainLenStack) ∗
        (arrayAt (chainAt A) 104 (ptr + 104#64) [] ∗ F) := by
      rw [hsp1, hP]; dsimp only [arrayAt]; ac_rfl
    refine call_chainLen_ext b A ext hchain ptr
      ((SP2Ext b ext).fnAddr sessionLenName + 380#64) gc
      hpc1 hrun1 hsp1_align hlr1 hx0_1 hfit_c hP1 ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hcs2
    have hx19_2 : s2.readReg64 .x19 = s.readReg64 .x19 := hcs2.1.trans hx19_1
    have hx20_2 : s2.readReg64 .x20 = ptr := hcs2.2.1.trans hx20_1
    have hx21_2 : s2.readReg64 .x21 = s.readReg64 .x21 := hcs2.2.2.1.trans hx21_1
    have hx22_2 : s2.readReg64 .x22 = s.readReg64 .x22 := hcs2.2.2.2.1.trans hx22_1
    have hx23_2 : s2.readReg64 .x23 = BitVec.ofNat 64 acc := (hcs2.2.2.2.2.1.trans hx23_1).trans hx23
    have hx24_2 : s2.readReg64 .x24 = BitVec.ofNat 64 (0 + 1) :=
      (hcs2.2.2.2.2.2.1.trans hx24_1).trans hx24
    refine step_sessLen_loop_post_ext b ext ptr gc acc 0 (by omega) hlen
      hpc2 hrun2 hx0_2 hx20_2 hx23_2 hx24_2 ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hcs3
    simp only [↓reduceIte] at hpc3
    refine hnext s3 hpc3 hrun3 (hsp3.trans (hsp2.trans hsp1)) (htr3.trans (htr2.trans htr1))
      (hx19_3.trans hx19_2) (hx21_3.trans hx21_2) (hx22_3.trans hx22_2) ?_
      (hcs1.trans ((SessLenCalleeSaved.of_calleeSavedPreserved hcs2).trans hcs3))
    simpa only [chainsNoKeySum, Nat.add_zero] using hx23_3
  | gc' :: rest', gc, ptr, acc, ret, s, P, F, Q, Qp,
      hfit, hlen, hpc, hrun, hsp, hx20, hx23, hx24, hP, hnext => by
    simp only [chainsNoKeySum] at hfit
    have hfit_c : (encChainMem gc).length < 2 ^ 32 := by
      have : (encChainMem gc).length ≤ chainNoKeyLen gc := by unfold chainNoKeyLen; omega
      omega
    refine step_sessLen_loop_pre_ext b ext ptr hpc hrun hx20 ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hlr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hcs1
    have hsp1_align : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp
    have hP1 : P = (chainAt A gc ptr ∗ stackAt s1.sp chainLenStack) ∗
        (arrayAt (chainAt A) 104 (ptr + 104#64) (gc' :: rest') ∗ F) := by
      rw [hsp1, hP]; dsimp only [arrayAt]; ac_rfl
    refine call_chainLen_ext b A ext hchain ptr
      ((SP2Ext b ext).fnAddr sessionLenName + 380#64) gc
      hpc1 hrun1 hsp1_align hlr1 hx0_1 hfit_c hP1 ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hcs2
    have hx19_2 : s2.readReg64 .x19 = s.readReg64 .x19 := hcs2.1.trans hx19_1
    have hx20_2 : s2.readReg64 .x20 = ptr := hcs2.2.1.trans hx20_1
    have hx21_2 : s2.readReg64 .x21 = s.readReg64 .x21 := hcs2.2.2.1.trans hx21_1
    have hx22_2 : s2.readReg64 .x22 = s.readReg64 .x22 := hcs2.2.2.2.1.trans hx22_1
    have hx23_2 : s2.readReg64 .x23 = BitVec.ofNat 64 acc := (hcs2.2.2.2.2.1.trans hx23_1).trans hx23
    have hx24_2 : s2.readReg64 .x24 = BitVec.ofNat 64 ((gc' :: rest').length + 1) :=
      (hcs2.2.2.2.2.2.1.trans hx24_1).trans hx24
    refine step_sessLen_loop_post_ext b ext ptr gc acc (gc' :: rest').length (by omega) hlen
      hpc2 hrun2 hx0_2 hx20_2 hx23_2 hx24_2 ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hcs3
    simp only [List.length_cons, Nat.succ_ne_zero, ↓reduceIte] at hpc3 hx24_3
    have hsp3_eq : s3.sp = s.sp := hsp3.trans (hsp2.trans hsp1)
    have hsp3_align : s3.spAligned = true := by simpa only [State.spAligned, hsp3_eq] using hsp
    have hP3 : P = (arrayAt (chainAt A) 104 (ptr + 104#64) (gc' :: rest') ∗ stackAt s3.sp chainLenStack) ∗
        (chainAt A gc ptr ∗ F) := by
      rw [hsp3_eq, hP]; dsimp only [arrayAt]; ac_rfl
    have hfit' : (acc + chainNoKeyLen gc) + chainsNoKeySum (gc' :: rest') < 2 ^ 32 := by
      simp only [chainsNoKeySum]; omega
    refine step_sessLen_chains_loop_ext b A ext hchain rest' gc' (ptr + 104#64)
      (acc + chainNoKeyLen gc) hfit' (by simp only [List.length_cons] at hlen; omega)
      hpc3 hrun3 hsp3_align hx20_3 hx23_3 hx24_3 hP3 ?_
    intro s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx21_4 hx22_4 hx23_4 hcs4
    refine hnext s4 hpc4 hrun4 (hsp4.trans hsp3_eq) (htr4.trans (htr3.trans (htr2.trans htr1)))
      (hx19_4.trans (hx19_3.trans hx19_2))
      (hx21_4.trans (hx21_3.trans hx21_2))
      (hx22_4.trans (hx22_3.trans hx22_2)) ?_
      (hcs1.trans ((SessLenCalleeSaved.of_calleeSavedPreserved hcs2).trans (hcs3.trans hcs4)))
    simpa only [chainsNoKeySum, Nat.add_assoc] using hx23_4

theorem step_sessLen_chains_enter_ext (b : BitVec 64)
    (ext : String → Option (State → State))
    (ss ptr : BitVec 64) (n : Nat)
    (hn_pos : n ≠ 0) (hn_lt : n < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext b ext).fnAddr sessionLenName + 352#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hP : P = (((ss + 80#64) ↦₆₄ ptr) ∗ ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 n)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (SP2Ext b ext).fnAddr sessionLenName + 372#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x20 = ptr →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = BitVec.ofNat 64 n →
      sm.readReg64 .x23 = 0#64 →
      sm.readReg64 .x24 = BitVec.ofNat 64 n →
      SessLenCalleeSaved s sm →
      SepWPp (SP2Ext b ext) ret sm P Q Qp) :
    SepWPp (SP2Ext b ext) ret s P Q Qp := by
  sesslen_fetches b (Rust.withPanics ext) 352 372
  generalize_entry (SP2Ext b ext).fnAddr sessionLenName = entry
  examples_hide_fetches
  have hn_beq : (BitVec.ofNat 64 n == 0#64) = false := by
    rw [ofNat64_beq_zero_of_lt hn_lt]
    exact beq_eq_false_iff_ne.mpr hn_pos
  subst hP
  apply SepWPp.of_sepWP (mid := entry + bv% (372))
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_chains_exit_ext (b : BitVec 64)
    (ext : String → Option (State → State))
    (cs : List (ChainGhost × ReceiverChain)) (s1_6 : Nat)
    (hfit : s1_6 + chainsTotalLen cs < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext b ext).fnAddr sessionLenName + 428#64)
    (hrun : s.status = .Running)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 s1_6)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 cs.length)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (chainsNoKeySum cs))
    (hnext : ∀ sm : State,
      sm.pc = (SP2Ext b ext).fnAddr sessionLenName + 444#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1_6 + chainsTotalLen cs) →
      SessLenCalleeSaved s sm →
      SepWPp (SP2Ext b ext) ret sm P Q Qp) :
    SepWPp (SP2Ext b ext) ret s P Q Qp := by
  sesslen_fetches b (Rust.withPanics ext) 428 444
  generalize_entry (SP2Ext b ext).fnAddr sessionLenName = entry
  examples_hide_fetches
  have hsum_eq := chainsNoKeySum_add_length cs
  have hfit1 : chainsNoKeySum cs + cs.length < 2 ^ 64 := by omega
  have hadd1 : BitVec.ofNat 64 (chainsNoKeySum cs) + BitVec.ofNat 64 cs.length =
      BitVec.ofNat 64 (chainsTotalLen cs) := by
    rw [← BitVec.ofNat_add, hsum_eq]
  have hcc1 : BitVec.ult (BitVec.ofNat 64 (chainsTotalLen cs))
      (BitVec.ofNat 64 (chainsNoKeySum cs)) = false := by
    have h := ult_ofNat_add_of_lt (a := cs.length) (b := chainsNoKeySum cs) (by omega)
    rwa [Nat.add_comm, hsum_eq] at h
  have hadd2 := bv_add_ofNat_comm s1_6 (chainsTotalLen cs)
  have hcc2 : BitVec.ult (BitVec.ofNat 64 (s1_6 + chainsTotalLen cs))
      (BitVec.ofNat 64 (chainsTotalLen cs)) = false :=
    ult_ofNat_add_of_lt hfit
  apply SepWPp.of_sepWP (mid := entry + bv% (444))
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_f6_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hchain : subroutine_ok (SP2Ext b ext) ((SP2Ext b ext).fnAddr chainLenName) (chainLenSpec A))
    (ss : BitVec 64) (G : SessionGhost) (m : Session (List (BitVec 8))) (s1_6 : Nat)
    (hfit : s1_6 + chainsTotalLen (G.chains.zip m.state.receiverChains) < 2 ^ 32)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext b ext).fnAddr sessionLenName + 352#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = ss)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 s1_6)
    (hP : P = (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
      ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip m.state.receiverChains).length) ∗
      vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip m.state.receiverChains) ∗
      stackAt s.sp chainLenStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (SP2Ext b ext).fnAddr sessionLenName + 444#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64
        (s1_6 + chainsTotalLen (G.chains.zip m.state.receiverChains)) →
      SessLenCalleeSaved s sm →
      SepWPp (SP2Ext b ext) ret sm P Q Qp) :
    SepWPp (SP2Ext b ext) ret s P Q Qp := by
  intro R hm hL
  have hm_pure : s.mem ⊨
      ⌜(G.chains.zip m.state.receiverChains).length ≤ G.chainsCap.toNat ∧
        G.chainsCap.toNat * 104 < 2 ^ 63 ∧ G.chainsPtr ≠ 0⌝ ∗
      ((if G.chainsCap = 0 then emp
        else A.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
          arrayAt (chainAt A) 104 G.chainsPtr (G.chains.zip m.state.receiverChains) ∗
          memRegion (G.chainsPtr + BitVec.ofNat 64 ((G.chains.zip m.state.receiverChains).length * 104))
            ((G.chainsCap.toNat - (G.chains.zip m.state.receiverChains).length) * 104)) ∗
       ((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
       ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip m.state.receiverChains).length) ∗
       stackAt s.sp chainLenStack ∗ F ∗ R) := by
    rw [hP] at hm
    dsimp only [vecBuf] at hm
    convert hm using 1; ac_rfl
  rw [satisfies_pure_sepConj] at hm_pure
  rcases hm_pure.1 with ⟨hlen_le, hcap_lt, _⟩
  clear hm_pure
  revert R hm hL
  change SepWPp (SP2Ext b ext) ret s P Q Qp
  cases hcs : G.chains.zip m.state.receiverChains with
  | nil =>
    sesslen_fetches b (Rust.withPanics ext) 352 360
    sesslen_fetches b (Rust.withPanics ext) 436 444
    sesslen_fetches b (Rust.withPanics ext) 512 520
    generalize_entry (SP2Ext b ext).fnAddr sessionLenName = entry
    examples_hide_fetches
    subst hP
    have hlen0 : (G.chains.zip m.state.receiverChains).length = 0 := by rw [hcs]; rfl
    have htot0 : chainsTotalLen (G.chains.zip m.state.receiverChains) = 0 := by rw [hcs]; rfl
    have hP0 : (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
        ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip m.state.receiverChains).length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip m.state.receiverChains) ∗
        stackAt s.sp chainLenStack) ∗ F =
        ((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
        ((ss + 88#64) ↦₆₄ 0#64) ∗
        (vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip m.state.receiverChains) ∗
         stackAt s.sp chainLenStack ∗ F) := by
      simp only [hlen0, sepConj_assoc]
    rw [hP0]
    apply SepWPp.of_sepWP (mid := entry + bv% (444))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP0]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])
  | cons gc rest =>
    rw [hcs] at hlen_le
    have hcap_ne : G.chainsCap ≠ 0 := by
      intro h0
      have hcap0 : G.chainsCap.toNat = 0 := by simp [h0]
      simp only [List.length_cons, hcap0] at hlen_le
      omega
    have hV : P = (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
        ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (gc :: rest).length)) ∗
        ((⌜(gc :: rest).length ≤ G.chainsCap.toNat ∧
            G.chainsCap.toNat * 104 < 2 ^ 63 ∧ G.chainsPtr ≠ 0⌝ ∗
          A.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
          arrayAt (chainAt A) 104 G.chainsPtr (gc :: rest) ∗
          memRegion (G.chainsPtr + BitVec.ofNat 64 ((gc :: rest).length * 104))
            ((G.chainsCap.toNat - (gc :: rest).length) * 104)) ∗
          stackAt s.sp chainLenStack ∗ F) := by
      rw [hP, hcs]
      dsimp only [vecBuf]
      simp only [hcap_ne, ↓reduceIte]
      ac_rfl
    refine step_sessLen_chains_enter_ext b ext ss G.chainsPtr
      (gc :: rest).length (by simp) (by omega) hpc hrun hx19 hV ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hcs1
    have hsp1_align : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp
    have hP1 : P = (arrayAt (chainAt A) 104 G.chainsPtr (gc :: rest) ∗ stackAt s1.sp chainLenStack) ∗
        (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
         ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (gc :: rest).length) ∗
         ⌜(gc :: rest).length ≤ G.chainsCap.toNat ∧
           G.chainsCap.toNat * 104 < 2 ^ 63 ∧ G.chainsPtr ≠ 0⌝ ∗
         A.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
         memRegion (G.chainsPtr + BitVec.ofNat 64 ((gc :: rest).length * 104))
           ((G.chainsCap.toNat - (gc :: rest).length) * 104) ∗ F) := by
      rw [hsp1, hV]; ac_rfl
    have hfit_loop : 0 + chainsNoKeySum (gc :: rest) < 2 ^ 32 := by
      rw [hcs] at hfit
      have := chainsNoKeySum_add_length (gc :: rest)
      omega
    refine step_sessLen_chains_loop_ext b A ext hchain rest gc G.chainsPtr 0
      hfit_loop (by simp only [List.length_cons] at hlen_le; omega)
      hpc1 hrun1 hsp1_align hx20_1 hx23_1 hx24_1 hP1 ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx21_2 hx22_2 hx23_2 hcs2
    simp only [Nat.zero_add] at hx23_2
    have hx21_2' : s2.readReg64 .x21 = BitVec.ofNat 64 s1_6 :=
      (hx21_2.trans hx21_1).trans hx21
    have hx22_2' : s2.readReg64 .x22 = BitVec.ofNat 64 (gc :: rest).length :=
      hx22_2.trans hx22_1
    have hfit_exit : s1_6 + chainsTotalLen (gc :: rest) < 2 ^ 64 := by
      rw [hcs] at hfit; omega
    refine step_sessLen_chains_exit_ext b ext (gc :: rest) s1_6 hfit_exit
      hpc2 hrun2 hx21_2' hx22_2' hx23_2 ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx8_3 hcs3
    refine hnext s3 hpc3 hrun3 (hsp3.trans (hsp2.trans hsp1)) (htr3.trans (htr2.trans htr1))
      ((hx19_3.trans hx19_2).trans hx19_1) ?_
      (hcs1.trans (hcs2.trans hcs3))
    simpa only [hcs] using hx8_3

/-! ## Relocatable `[LibsignalPlacement]` front steps (Block `86`)

Relocatable front step lemmas (`step_sessLen_f1_placed`..`step_sessLen_f4_placed`) are re-exported
from `SessionLenAux.StepsFront` and `SessionLenAux.StepsChains`. -/

section Placed

abbrev call_protoChainLen_placed_ext := @call_protoChainLen_placed
abbrev call_chainLen_placed_ext := @call_chainLen_placed
abbrev step_sessLen_f1_placed_ext := @step_sessLen_f1_placed
abbrev step_sessLen_f2_placed_ext := @step_sessLen_f2_placed
abbrev step_sessLen_f3_placed_ext := @step_sessLen_f3_placed
abbrev step_sessLen_f4_placed_ext := @step_sessLen_f4_placed

end Placed

end CryptoVerification.E2E.Record.Serialization.SessionLenAux
