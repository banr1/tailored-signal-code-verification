/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart1
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.Fetch
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.KyberPart1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.ChainCloneEpilogue -- shake: keep

@[expose] public section

set_option autoImplicit false

/-!
# `SessionStructure::clone`: `alice_base_key` and `pq_ratchet_state`

Completes `alice_base_key` (Field 8) and `pq_ratchet_state` (Field 9, `+0x390 / +0x30c → +0x39c`).
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.ChainCloneLocal1 hiding
  allocFailedIn_of_eq srk_length_pos ofNat_ne_zero_of_pos beq_ofNat_zero_eq_false sepWPp_pure_mid
  vecU8At_eq_of_nil vecU8At_eq_of_pos vecGhostAt_eq_of_nil vecGhostAt_eq_of_pos vecU8Buf_nil_eq vecU8Buf_pos_eq
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.E2E.Record.Serialization
open ProofLib.ProgramReflection
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem sepWPpX_pure_2nd {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {A B : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPpX img prog ret s (A ∗ B) Q Qp) :
    SepWPpX img prog ret s (A ∗ ⌜φ⌝ ∗ B) Q Qp :=
  SepWPpX.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWPpX.pure_elim h)

private theorem sepWPpX_pure_3rd {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPpX img prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPpX img prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp :=
  SepWPpX.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWPpX.pure_elim h)

theorem sc_aliceBaseKey {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v30 : BitVec 64} {v3c w288 w28c : BitVec 32} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x260#64 ∨
           s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x374#64 ∨
           s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x2d0#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (alice' : VecGhost),
      s1.pc = (if x.G.alice.bytes = [] then
                 (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x390#64
               else
                 (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x30c#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      (s1.readReg64 .x20).truncate 32 = w288 →
      s1.readReg64 .x21 = alice'.cap →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      alice'.bytes = x.G.alice.bytes →
      alice'.cap = BitVec.ofNat 64 x.G.alice.bytes.length →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          vecGhostAt A x.G.alice (x.src + 0x60#64) ∗
          vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗
          ((x.src + 0x150#64) ↦₃₂ w288) ∗
          ((x.src + 0x154#64) ↦₃₂ w28c) ∗
          ((s.sp + 0x30#64) ↦₆₄ alice'.ptr) ∗
          ((s.sp + 0x3c#64) ↦₃₂ w28c) ∗
          stackAt s.sp extHookStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        vecGhostAt A x.G.alice (x.src + 0x60#64) ∗
        ((x.src + 0x150#64) ↦₃₂ w288) ∗
        ((x.src + 0x154#64) ↦₃₂ w28c) ∗
        ((s.sp + 0x30#64) ↦₆₄ v30) ∗
        ((s.sp + 0x3c#64) ↦₃₂ v3c) ∗
        stackAt s.sp extHookStack ∗ F)
      Q (scPanicPost A x R s0) := by
  have hfn := fnOff_sessionClone
  have h68 : x.src + 0x60#64 + 8#64 = x.src + 0x68#64 := by bv_arith
  have h70 : x.src + 0x60#64 + 16#64 = x.src + 0x70#64 := by bv_arith
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x260 24
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x2d0 20
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x374 28
  clear hfn
  rcases eq_nil_or_length_pos x.G.alice.bytes with halice | halice
  · simp only [halice, ↓reduceIte] at hnext
    rw [vecGhostAt_eq_of_nil A x.G.alice (x.src + 0x60#64) halice, h68, h70]
    simp only [sepConj_assoc]
    refine sepWPpX_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
    have h_pure_emp :
        (⌜x.G.alice.cap.toNat < 2 ^ 63 ∧ x.G.alice.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hcap_lt, hptr⟩
    unfold tripleRatchetProgAtExt at *
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    rcases hpc with hpc | hpc | hpc
    · apply SepWPpX.of_sepWP (mid := entry + bv% (912))
      wp_steps
      refine SepWP.done (by sc_close3) (by sc_close3) ?_
      refine SepWPpX.weaken_pre ?_
        (hnext _ ⟨0#64, 1#64, []⟩ (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
          (by simp [halice]) (by simp [halice]))
      rw [vecGhostAt_eq_of_nil A x.G.alice (x.src + 0x60#64) halice, h68, h70,
          vecU8Buf_nil_eq A, h_pure_emp]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
    · apply SepWPpX.of_sepWP (mid := entry + bv% (912))
      wp_steps
      refine SepWP.done (by sc_close3) (by sc_close3) ?_
      refine SepWPpX.weaken_pre ?_
        (hnext _ ⟨0#64, 1#64, []⟩ (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
          (by simp [halice]) (by simp [halice]))
      rw [vecGhostAt_eq_of_nil A x.G.alice (x.src + 0x60#64) halice, h68, h70,
          vecU8Buf_nil_eq A, h_pure_emp]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
    · apply SepWPpX.of_sepWP (mid := entry + bv% (912))
      wp_steps
      refine SepWP.done (by sc_close3) (by sc_close3) ?_
      refine SepWPpX.weaken_pre ?_
        (hnext _ ⟨0#64, 1#64, []⟩ (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
          (by simp [halice]) (by simp [halice]))
      rw [vecGhostAt_eq_of_nil A x.G.alice (x.src + 0x60#64) halice, h68, h70,
          vecU8Buf_nil_eq A, h_pure_emp]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
  · have halice_ne_nil : x.G.alice.bytes ≠ [] := List.ne_nil_of_length_pos halice
    simp only [halice_ne_nil, ↓reduceIte] at hnext
    rw [vecGhostAt_eq_of_pos A x.G.alice (x.src + 0x60#64) halice, h68, h70]
    simp only [sepConj_assoc]
    refine sepWPpX_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have halice_ne : BitVec.ofNat 64 x.G.alice.bytes.length ≠ 0#64 :=
      ofNat_ne_zero_of_pos halice (by omega)
    have halice_beq : (BitVec.ofNat 64 x.G.alice.bytes.length == 0#64) = false :=
      beq_ofNat_zero_eq_false halice (by omega)
    have hsub := @sc_aliceBaseKey_2e4_pos img A ext hA x R s0
    unfold tripleRatchetProgAtExt at *
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    suffices h_at_2e4 : ∀ s_2e4 : State,
        s_2e4.pc = entry + bv% (740) →
        s_2e4.status = .Running →
        s_2e4.sp = s.sp →
        s_2e4.spAligned = true →
        s_2e4.readReg64 .x19 = s.readReg64 .x19 →
        (s_2e4.readReg64 .x20).truncate 32 = w288 →
        s_2e4.readReg64 .x21 = BitVec.ofNat 64 x.G.alice.bytes.length →
        s_2e4.readReg64 .x23 = s.readReg64 .x23 →
        s_2e4.readReg64 .x24 = s.readReg64 .x24 →
        s_2e4.readReg64 .x25 = x.src →
        s_2e4.readReg64 .x26 = s.readReg64 .x26 →
        s_2e4.readReg64 .x27 = s.readReg64 .x27 →
        s_2e4.readReg64 .x28 = s.readReg64 .x28 →
        s_2e4.readReg64 .x29 = s.readReg64 .x29 →
        s_2e4.trace = s0.trace →
        calleeSavedVRegs s_2e4 = calleeSavedVRegs s0 →
        SepWPpX img prog ret s_2e4
          (A.pool ∗
            ((x.src + 0x60#64) ↦₆₄ x.G.alice.cap) ∗
            ((x.src + 0x68#64) ↦₆₄ x.G.alice.ptr) ∗
            ((x.src + 0x70#64) ↦₆₄ BitVec.ofNat 64 x.G.alice.bytes.length) ∗
            (x.G.alice.ptr ↦ₛ x.G.alice.bytes) ∗
            A.live x.G.alice.ptr x.G.alice.cap.toNat 1 ∗
            memRegion (x.G.alice.ptr + BitVec.ofNat 64 x.G.alice.bytes.length)
              (x.G.alice.cap.toNat - x.G.alice.bytes.length) ∗
            ((x.src + 0x150#64) ↦₃₂ w288) ∗
            ((x.src + 0x154#64) ↦₃₂ w28c) ∗
            ((s_2e4.sp + 0x30#64) ↦₆₄ v30) ∗
            ((s_2e4.sp + 0x3c#64) ↦₃₂ w28c) ∗
            stackAt s_2e4.sp extHookStack ∗ F)
          Q (scPanicPost A x R s0) by
      clear hsub
      rcases hpc with hpc | hpc | hpc
      · apply SepWPpX.of_sepWP (mid := entry + bv% (740))
        wp_steps
        refine SepWP.done (by sc_close3) (by sc_close3) ?_
        exact h_at_2e4 _ (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
      · apply SepWPpX.of_sepWP (mid := entry + bv% (740))
        wp_steps
        refine SepWP.done (by sc_close3) (by sc_close3) ?_
        exact h_at_2e4 _ (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
      · apply SepWPpX.of_sepWP (mid := entry + bv% (740))
        wp_steps
        refine SepWP.done (by sc_close3) (by sc_close3) ?_
        exact h_at_2e4 _ (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
    intro s_2e4 hpc2e4 hrun2e4 hsp2e4 hspA2e4 hx19_2e4 hx20_2e4 hx21_2e4 hx23_2e4 hx24_2e4 hx25_2e4 hx26_2e4 hx27_2e4 hx28_2e4 hx29_2e4 htr2e4 hvregs2e4
    refine SepWPpX.weaken_pre
      (P' := A.pool ∗
              ((x.src + 0x60#64) ↦₆₄ x.G.alice.cap) ∗
              ((x.src + 0x68#64) ↦₆₄ x.G.alice.ptr) ∗
              ((x.src + 0x70#64) ↦₆₄ BitVec.ofNat 64 x.G.alice.bytes.length) ∗
              (x.G.alice.ptr ↦ₛ x.G.alice.bytes) ∗
              A.live x.G.alice.ptr x.G.alice.cap.toNat 1 ∗
              memRegion (x.G.alice.ptr + BitVec.ofNat 64 x.G.alice.bytes.length)
                (x.G.alice.cap.toNat - x.G.alice.bytes.length) ∗
              ((s_2e4.sp + 0x30#64) ↦₆₄ v30) ∗
              stackAt s_2e4.sp extHookStack ∗
              (((x.src + 0x150#64) ↦₃₂ w288) ∗
                ((x.src + 0x154#64) ↦₃₂ w28c) ∗
                ((s_2e4.sp + 0x3c#64) ↦₃₂ w28c) ∗ F))
      (Entails.of_eq (by ac_rfl)) ?_
    refine hsub halice hlen_le hcap_lt hptr hpc2e4 hrun2e4 hspA2e4 hx21_2e4 hx25_2e4 htr2e4 hvregs2e4
      fun s1 alice' hpc1 hrun1 hsp1 hspA1 hx19_1 hx20_1 hx21_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 htr1 hvregs1 hbytes' hcap' => ?_
    rw [hsp2e4]
    refine SepWPpX.weaken_pre ?_
      (hnext s1 alice' hpc1 hrun1 (hsp1.trans hsp2e4) hspA1
        (hx19_1.trans hx19_2e4) (by rw [hx20_1]; exact hx20_2e4) hx21_1
        (hx23_1.trans hx23_2e4) (hx24_1.trans hx24_2e4) hx25_1
        (hx26_1.trans hx26_2e4) (hx27_1.trans hx27_2e4) (hx28_1.trans hx28_2e4)
        (hx29_1.trans hx29_2e4) htr1 hvregs1 hbytes' hcap')
    exact Entails.of_eq (by ac_rfl)

/-! ## 3. Field 9: `pq_ratchet_state` (`+0x390 / +0x30c → +0x39c`) -/

theorem sc_pqRatchet_314_pos {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v0c : BitVec 32} {F : SepProp}
    (hpq : 0 < x.s.state.pqRatchetState.length)
    (hlen_le : x.s.state.pqRatchetState.length ≤ x.G.pq.cap.toNat)
    (hcap_lt : x.G.pq.cap.toNat < 2 ^ 63)
    (hptr : x.G.pq.ptr ≠ 0)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x314#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 x.s.state.pqRatchetState.length)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pqCap' pqPtr' : BitVec 64) (v0c' : BitVec 32),
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x39c#64 →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      (s1.readReg64 .x20).truncate 32 = (s.readReg64 .x20).truncate 32 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = pqCap' →
      (s1.readReg64 .x23).truncate 32 = (s.readReg64 .x23).truncate 32 →
      (s1.readReg64 .x24).truncate 32 = (s.readReg64 .x24).truncate 32 →
      s1.readReg64 .x25 = pqPtr' →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      pqCap' = BitVec.ofNat 64 x.s.state.pqRatchetState.length →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          vecU8At A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
          vecU8Buf A pqCap' pqPtr' x.s.state.pqRatchetState ∗
          ((s.sp + 0x0c#64) ↦₃₂ v0c') ∗
          stackAt s.sp extHookStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        ((x.src + 0x78#64) ↦₆₄ x.G.pq.cap) ∗
        ((x.src + 0x80#64) ↦₆₄ x.G.pq.ptr) ∗
        ((x.src + 0x88#64) ↦₆₄ BitVec.ofNat 64 x.s.state.pqRatchetState.length) ∗
        (x.G.pq.ptr ↦ₛ x.s.state.pqRatchetState) ∗
        A.live x.G.pq.ptr x.G.pq.cap.toNat 1 ∗
        memRegion (x.G.pq.ptr + BitVec.ofNat 64 x.s.state.pqRatchetState.length)
          (x.G.pq.cap.toNat - x.s.state.pqRatchetState.length) ∗
        ((s.sp + 0x0c#64) ↦₃₂ v0c) ∗
        stackAt s.sp extHookStack ∗ F)
      Q (scPanicPost A x R s0) := by
  have hfn := fnOff_sessionClone
  have hshim := sc_shim_ok_at hA (ext := ext)
  have halloc := sc_alloc_ok_at (A := A) (img := img) (ext := ext) hA
  have hmemcpy := sc_memcpy_ok_at hA (ext := ext)
  dsimp only [scShimSpec] at hshim
  dsimp only [rustAllocSpecWithStack, withStack, rustAllocSpec] at halloc
  dsimp only [scMemcpySpec] at hmemcpy
  have hpanic := sc_panic_0x4a4 (img := img) (A := A) (ext := ext) (ret := ret) (Q := Q) x s0
  have h80 : x.src + 0x78#64 + 8#64 = x.src + 0x80#64 := by bv_arith
  have h88 : x.src + 0x78#64 + 16#64 = x.src + 0x88#64 := by bv_arith
  have hpq_lt : x.s.state.pqRatchetState.length < 2 ^ 63 := by omega
  have hpq_le63 : x.s.state.pqRatchetState.length + 1 ≤ 2 ^ 63 := by omega
  have hpq_le64 : x.s.state.pqRatchetState.length ≤ 2 ^ 64 := by omega
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk x.s.state.pqRatchetState.length 1 := ⟨hpq, hpow2, hpq_le63⟩
  have htoNat : (BitVec.ofNat 64 x.s.state.pqRatchetState.length).toNat = x.s.state.pqRatchetState.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x314 84
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  wpx_of_sepWP (mid := entry + bv% (828))
  wpx_steps
  wpx_call hshim ()
  clear hshim
  wpx_steps
  wpx_call halloc (x.s.state.pqRatchetState.length, 1)
  clear halloc
  wpx_clear_invs
  refine SepWP.done (by sc_close3) (by sc_close3) ?_
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · clear hmemcpy hnext
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPpX_pure_3rd fun htrace => ?_
    apply SepWPpX.of_sepWP (mid := entry + bv% (1188))
    wp_steps
    refine SepWP.done (by sc_close3) (by sc_close3) ?_
    exact hpanic _ _ R (by sc_close3) (by sc_close3) (by sc_close3)
  · clear hpanic
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPpX_pure_3rd fun ⟨hmod, htrace⟩ => ?_
    wpx_of_sepWP (mid := entry + bv% (924))
    wpx_steps
    wpx_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.pq.ptr, x.s.state.pqRatchetState)
    clear hmemcpy
    wpx_steps
    wpx_clear_invs
    refine SepWP.done (by sc_close3) (by sc_close3) ?_
    have hsp_eq : sf.sp = s.sp := by sc_close3
    have hsf1_sp : sf_1.sp = s.sp := by sc_close3
    refine SepWPpX.weaken_pre ?_
      (hnext _ (BitVec.ofNat 64 x.s.state.pqRatchetState.length) (sf_1.readReg64 (Reg.gpr 0#5))
        ((s.readReg64 .x20).truncate 32)
        (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
        (by sc_close3) (by sc_close3) (by sc_close3)
        (by sc_close3) (by sc_close3) (by sc_close3)
        (by sc_close3) (by sc_close3) (by sc_close3)
        (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3) rfl)
    rw [vecU8At_eq_of_pos A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState hpq,
        h80, h88,
        vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) x.s.state.pqRatchetState hpq hpq_lt hoom64]
    have h_pure_emp :
        (⌜x.s.state.pqRatchetState.length ≤ x.G.pq.cap.toNat ∧
            x.G.pq.cap.toNat < 2 ^ 63 ∧ x.G.pq.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
    rw [h_pure_emp]
    dsimp only [Reg.x20]
    simp only [sepConj_assoc, hsp_eq, hsf1_sp, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)

/-- Field 9 (`+0x390 / +0x30c → +0x39c`): clones `pq_ratchet_state`
into `x22 = pqCap'` and `x25 = pqPtr'`. -/
theorem sc_pqRatchet {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v0c : BitVec 32} {F : SepProp}
    (hpc : s.pc = (if x.G.alice.bytes = [] then
                     (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x390#64
                   else
                     (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x30c#64))
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pqCap' pqPtr' : BitVec 64) (v0c' : BitVec 32),
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x39c#64 →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      (s1.readReg64 .x20).truncate 32 = (s.readReg64 .x20).truncate 32 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = pqCap' →
      (s1.readReg64 .x23).truncate 32 = (s.readReg64 .x23).truncate 32 →
      (s1.readReg64 .x24).truncate 32 = (s.readReg64 .x24).truncate 32 →
      s1.readReg64 .x25 = pqPtr' →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      pqCap' = BitVec.ofNat 64 x.s.state.pqRatchetState.length →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          vecU8At A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
          vecU8Buf A pqCap' pqPtr' x.s.state.pqRatchetState ∗
          ((s.sp + 0x0c#64) ↦₃₂ v0c') ∗
          stackAt s.sp extHookStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        vecU8At A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
        ((s.sp + 0x0c#64) ↦₃₂ v0c) ∗
        stackAt s.sp extHookStack ∗ F)
      Q (scPanicPost A x R s0) := by
  have hfn := fnOff_sessionClone
  have h80 : x.src + 0x78#64 + 8#64 = x.src + 0x80#64 := by bv_arith
  have h88 : x.src + 0x78#64 + 16#64 = x.src + 0x88#64 := by bv_arith
  have hpcs : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x390#64 ∨
              s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x30c#64 := by
    by_cases h : x.G.alice.bytes = [] <;> simp only [h, ↓reduceIte] at hpc <;> [exact Or.inl hpc; exact Or.inr hpc]
  clear hpc
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x30c 8
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x390 12
  clear hfn
  rcases eq_nil_or_length_pos x.s.state.pqRatchetState with hpq | hpq
  · rw [hpq, vecU8At_eq_of_nil A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr, h80, h88]
    simp only [sepConj_assoc]
    refine sepWPpX_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
    have h_pure_emp :
        (⌜x.G.pq.cap.toNat < 2 ^ 63 ∧ x.G.pq.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hcap_lt, hptr⟩
    unfold tripleRatchetProgAtExt at *
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    rcases hpcs with hpc | hpc
    · apply SepWPpX.of_sepWP (mid := entry + bv% (924))
      wp_steps
      refine SepWP.done (by sc_close3) (by sc_close3) ?_
      refine SepWPpX.weaken_pre ?_
        (hnext _ 0#64 1#64 v0c (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by simp [hpq]))
      rw [hpq, vecU8At_eq_of_nil A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr, h80, h88,
          vecU8Buf_nil_eq A, h_pure_emp]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
    · apply SepWPpX.of_sepWP (mid := entry + bv% (924))
      wp_steps
      refine SepWP.done (by sc_close3) (by sc_close3) ?_
      refine SepWPpX.weaken_pre ?_
        (hnext _ 0#64 1#64 v0c (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by simp [hpq]))
      rw [hpq, vecU8At_eq_of_nil A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr, h80, h88,
          vecU8Buf_nil_eq A, h_pure_emp]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
  · rw [vecU8At_eq_of_pos A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState hpq,
        h80, h88]
    simp only [sepConj_assoc]
    refine sepWPpX_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hpq_ne : BitVec.ofNat 64 x.s.state.pqRatchetState.length ≠ 0#64 :=
      ofNat_ne_zero_of_pos hpq (by omega)
    have hpq_beq : (BitVec.ofNat 64 x.s.state.pqRatchetState.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hpq (by omega)
    have hsub := @sc_pqRatchet_314_pos img A ext hA x R s0
    unfold tripleRatchetProgAtExt at *
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    suffices h_at_314 : ∀ s_314 : State,
        s_314.pc = entry + bv% (788) →
        s_314.status = .Running →
        s_314.sp = s.sp →
        s_314.spAligned = true →
        s_314.readReg64 .x19 = s.readReg64 .x19 →
        (s_314.readReg64 .x20).truncate 32 = (s.readReg64 .x20).truncate 32 →
        s_314.readReg64 .x21 = s.readReg64 .x21 →
        s_314.readReg64 .x22 = BitVec.ofNat 64 x.s.state.pqRatchetState.length →
        (s_314.readReg64 .x23).truncate 32 = (s.readReg64 .x23).truncate 32 →
        (s_314.readReg64 .x24).truncate 32 = (s.readReg64 .x24).truncate 32 →
        s_314.readReg64 .x25 = x.src →
        s_314.readReg64 .x26 = s.readReg64 .x26 →
        s_314.readReg64 .x27 = s.readReg64 .x27 →
        s_314.readReg64 .x28 = s.readReg64 .x28 →
        s_314.readReg64 .x29 = s.readReg64 .x29 →
        s_314.trace = s0.trace →
        calleeSavedVRegs s_314 = calleeSavedVRegs s0 →
        SepWPpX img prog ret s_314
          (A.pool ∗
            ((x.src + 0x78#64) ↦₆₄ x.G.pq.cap) ∗
            ((x.src + 0x80#64) ↦₆₄ x.G.pq.ptr) ∗
            ((x.src + 0x88#64) ↦₆₄ BitVec.ofNat 64 x.s.state.pqRatchetState.length) ∗
            (x.G.pq.ptr ↦ₛ x.s.state.pqRatchetState) ∗
            A.live x.G.pq.ptr x.G.pq.cap.toNat 1 ∗
            memRegion (x.G.pq.ptr + BitVec.ofNat 64 x.s.state.pqRatchetState.length)
              (x.G.pq.cap.toNat - x.s.state.pqRatchetState.length) ∗
            ((s_314.sp + 0x0c#64) ↦₃₂ v0c) ∗
            stackAt s_314.sp extHookStack ∗ F)
          Q (scPanicPost A x R s0) by
      clear hsub
      rcases hpcs with hpc | hpc
      · apply SepWPpX.of_sepWP (mid := entry + bv% (788))
        wp_steps
        refine SepWP.done (by sc_close3) (by sc_close3) ?_
        exact h_at_314 _ (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
      · apply SepWPpX.of_sepWP (mid := entry + bv% (788))
        wp_steps
        refine SepWP.done (by sc_close3) (by sc_close3) ?_
        exact h_at_314 _ (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
    intro s_314 hpc314 hrun314 hsp314 hspA314 hx19_314 hx20_314 hx21_314 hx22_314 hx23_314 hx24_314 hx25_314 hx26_314 hx27_314 hx28_314 hx29_314 htr314 hvregs314
    refine hsub hpq hlen_le hcap_lt hptr hpc314 hrun314 hspA314 hx22_314 hx25_314 htr314 hvregs314
      fun s1 pqCap' pqPtr' v0c' hpc1 hrun1 hsp1 hspA1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 htr1 hvregs1 hcap' => ?_
    rw [hsp314]
    exact hnext s1 pqCap' pqPtr' v0c' hpc1 hrun1 (hsp1.trans hsp314) hspA1
      (hx19_1.trans hx19_314) (hx20_1.trans hx20_314) (hx21_1.trans hx21_314) hx22_1
      (hx23_1.trans hx23_314) (hx24_1.trans hx24_314) hx25_1
      (hx26_1.trans hx26_314) (hx27_1.trans hx27_314) (hx28_1.trans hx28_314)
      (hx29_1.trans hx29_314) htr1 hvregs1 hcap'

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
