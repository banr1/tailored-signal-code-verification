/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommon
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiation
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::decode_state`: `ChainPB` Field Merge Handlers (Tags 1, 2, 4, 5, 6 & `skip_field`)

**Checked by Lean.** Verifies the per-field handlers inside the inlined `ChainPB::merge` loop:
tag 1 (`direction`), tag 2 (`current_epoch`), tag 4 (`next_root`), tag 5 (`send_epoch`),
tag 6 (`params`), and unknown-tag `skip_field(depth=99)` (`0x5378c..0x53940`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
  CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalTripleRatchet.Prost
  CryptoVerification.SpqrV1.Varint CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.ProtoRepr
  CryptoVerification.SpqrV1.Prost.BytesMerge CryptoVerification.SpqrV1.Prost.MessageMerge
  CryptoVerification.SpqrV1.Drop CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## Layout Unfolding Helpers for `Some ch` at `s0.sp - 1040#64` -/

theorem protoPqRatchetStateCapOkAt_some_ch_eq (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (sp : BitVec 64) (remLen : Nat) (optVn : Option VersionNegotiationPB)
    (ch : ChainPB) (inner : Option PqRatchetState.Inner) :
    protoPqRatchetStateCapOkAt H_inner A (sp - 1040#64) remLen ⟨optVn, some ch, inner⟩ =
      optVersionNegotiationPBCapOkAt A (sp - 1040#64) remLen optVn ∗
        (⌜ch.links.length + remLen ≤ 2 ^ 54⌝ ∗
          chainLinksVecAt A (sp - 992#64) ch.links ∗
          vecU8CapOkAt A (sp - 968#64) remLen ch.nextRoot ∗
          ((sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
          ((sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
          optChainParamsPBAt (sp - 928#64) ch.params ∗
          ((sp - 916#64) ↦₃₂ ch.direction)) ∗
        optProtoPqRatchetInnerCapOkAt H_inner A (sp - 912#64) remLen inner := by
  unfold protoPqRatchetStateCapOkAt optChainPBCapOkAt chainPBCapOkAt
  dsimp only
  have ha1 : sp - 1040#64 + 48#64 = sp - 992#64 := by bv_omega
  have ha2 : sp - 1040#64 + 128#64 = sp - 912#64 := by bv_omega
  have hc1 : sp - 992#64 + 0x18#64 = sp - 968#64 := by bv_omega
  have hc2 : sp - 992#64 + 0x30#64 = sp - 944#64 := by bv_omega
  have hc3 : sp - 992#64 + 0x38#64 = sp - 936#64 := by bv_omega
  have hc4 : sp - 992#64 + 0x40#64 = sp - 928#64 := by bv_omega
  have hc5 : sp - 992#64 + 0x4c#64 = sp - 916#64 := by bv_omega
  rw [ha1, ha2, hc1, hc2, hc3, hc4, hc5]

theorem protoPqRatchetStateAt_some_ch_eq (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (sp : BitVec 64) (optVn : Option VersionNegotiationPB)
    (ch : ChainPB) (inner : Option PqRatchetState.Inner) :
    protoPqRatchetStateAt H_inner A (sp - 1040#64) ⟨optVn, some ch, inner⟩ =
      optVersionNegotiationPBAt A (sp - 1040#64) optVn ∗
        (chainLinksVecAt A (sp - 992#64) ch.links ∗
          rustBytesVecAt A (sp - 968#64) ch.nextRoot ∗
          ((sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
          ((sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
          optChainParamsPBAt (sp - 928#64) ch.params ∗
          ((sp - 916#64) ↦₃₂ ch.direction)) ∗
        optProtoPqRatchetInnerAt H_inner A (sp - 912#64) inner := by
  unfold protoPqRatchetStateAt optChainPBAt chainPBAt
  dsimp only
  have ha1 : sp - 1040#64 + 48#64 = sp - 992#64 := by bv_omega
  have ha2 : sp - 1040#64 + 128#64 = sp - 912#64 := by bv_omega
  have hc1 : sp - 992#64 + 0x18#64 = sp - 968#64 := by bv_omega
  have hc2 : sp - 992#64 + 0x30#64 = sp - 944#64 := by bv_omega
  have hc3 : sp - 992#64 + 0x38#64 = sp - 936#64 := by bv_omega
  have hc4 : sp - 992#64 + 0x40#64 = sp - 928#64 := by bv_omega
  have hc5 : sp - 992#64 + 0x4c#64 = sp - 916#64 := by bv_omega
  rw [ha1, ha2, hc1, hc2, hc3, hc4, hc5]

theorem optChainParamsPBAt_some_ch_eq (sp : BitVec 64) (cp : ChainParamsPB) :
    optChainParamsPBAt (sp - 928#64) (some cp) =
      ((sp - 928#64) ↦₃₂ 1#32) ∗ chainParamsPBAt (sp - 924#64) cp := by
  unfold optChainParamsPBAt
  dsimp only
  have ha : sp - 928#64 + 4#64 = sp - 924#64 := by bv_omega
  rw [ha]

theorem chainLinks_bound_mono {len rem1 rem2 : Nat} (hle : rem2 ≤ rem1) (Q : SepProp) :
    (⌜len + rem1 ≤ 2 ^ 54⌝ : SepProp) ∗ Q ⊢ ⌜len + rem2 ≤ 2 ^ 54⌝ ∗ Q := by
  apply Entails.pure_left; intro h
  exact Entails.pure_right (by omega) (Entails.refl _)

theorem chainLinks_bound_drop (len rem : Nat) (Q : SepProp) :
    (⌜len + rem ≤ 2 ^ 54⌝ : SepProp) ∗ Q ⊢ Q := by
  apply Entails.pure_left; intro _
  exact Entails.refl _

/-! ## `ChainPB` Field Merge Handlers -/

/-- Tag 1 (`direction: i32`) in `ChainPB` at `0x537b4..0x537d0`, `0x53844..0x5384c`
(`+792..+820`, `+936..+944`). -/
theorem decodeState_chain_tag1_537b4 {H_inner : V1InnerHeapPred} {img : Obj.Image} {b v27 : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_ne : iwt ≠ .varint → spqrDecodeState x.st.bytes = .error .stateDecode)
    (herr_of_none : iwt = .varint → decodeVarint rest1 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 792#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length ⟨optVn, some ch, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommon b A x s0)
    (hloop : ∀ (v : BitVec 64) (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      iwt = .varint →
      decodeVarint rest1 = some (v, rest2) →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 508#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length
          ⟨optVn, some { ch with direction := v.truncate 32 }, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 →
      SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPost H_inner b A x s0 R)) :
    SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  by_cases hwt : iwt = .varint
  · subst hwt
    have hdv_call := hc.decodeVarint2_at
    subst hP
    rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf,
      protoPqRatchetStateCapOkAt_some_ch_eq]
    dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateLoopCommon, WireType.toNat] at hpc hdv_call hx0 ⊢
    have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
    have hentry : decodeStateEntry b ext =
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
    decodeState_fetches b (Rust.withPanics ext) 792 28
    decodeState_fetches b (Rust.withPanics ext) 936 12
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::decode_state" = entry
    examples_hide_fetches
    apply SepWPpI.of_sepWP (mid := entry + (0x480d4#64 - 0x4e0a4#64))
    wp_steps 3
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
    refine SepWPpI.call_decodeVarint2 hdv_call
      (s0.sp - 336#64) (s0.sp - 1056#64)
      (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1
      (ret_pc := entry + 804#64)
      (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
      (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
      (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
      (hx0 := by simp only [arm64_norm, hx29, hx29_f0])
      (hlen := by omega)
      (hP := by sep_focus) ?_ ?_
    · intro s1 v rest2 hdv hlt2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_v
      have hle2 : rest2.length ≤ rest1.length := Nat.le_of_lt hlt2
      rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
      simp only [arm64_norm, wp_norm] at hx0_0 hx1_v hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      have hsp1_a : s1.spAligned = true := by rw [State.spAligned, hsp1]; exact sp_sub_1392_aligned s0 hs0A
      apply SepWPpI.of_sepWP (mid := entry + 508#64)
      wp_steps 5
      refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
        hrest1_le hrest1_suf hle2) (by sep_focus) ?_
      refine SepWP.fold (optVersionNegotiationPBCapOkAt_mono (A := A) (a := s0.sp - 1040#64)
        (rem1 := rest1.length) (rem2 := rest2.length) (opt := optVn) hle2)
        (by sep_focus) ?_
      refine SepWP.fold (chainLinks_bound_mono (len := ch.links.length) hle2
        (chainLinksVecAt A (s0.sp - 992#64) ch.links)) (by sep_focus) ?_
      refine SepWP.fold (vecU8CapOkAt_mono (A := A) (v := s0.sp - 968#64)
        (rem1 := rest1.length) (rem2 := rest2.length) (bs := ch.nextRoot) hle2)
        (by sep_focus) ?_
      refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_mono (H_inner := H_inner) (A := A)
        (a := s0.sp - 912#64) (rem1 := rest1.length) (rem2 := rest2.length) (opt := inner) hle2)
        (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
      exact hloop v rest2 _ _ rfl hdv hle2 hsuf2
        (by simp only [arm64_norm])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
        (by simp only [arm64_norm, htr1])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by rw [protoPqRatchetStateCapOkAt_some_ch_eq]; dsimp only [decodeStateLoopCommon, BitVec.truncate]; ac_rfl)
    · intro s1 hdv hpc1 hrun1 hsp1 htr1 hcs1 hx0_1 hx1_ne
      rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
      simp only [arm64_norm, wp_norm] at hx0_1 hx1_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      apply SepWPpI.of_sepWP (mid := entry + 2684#64)
      wp_steps 3
      wp_if hcbnz
      · refine SepWP.fold (errFrame_parts_fold A x s0 hrest1_le hrest1_suf) (by sep_focus) ?_
        refine SepWP.fold (optVersionNegotiationPBCapOkAt_entails_optVersionNegotiationPBAt A
          (s0.sp - 1040#64) rest1.length optVn) (by sep_focus) ?_
        refine SepWP.fold (chainLinks_bound_drop ch.links.length rest1.length
          (chainLinksVecAt A (s0.sp - 992#64) ch.links)) (by sep_focus) ?_
        refine SepWP.fold (vecU8CapOkAt_entails_rustBytesVecAt A (s0.sp - 968#64) rest1.length ch.nextRoot)
          (by sep_focus) ?_
        refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_entails_optProtoPqRatchetInnerAt H_inner A
          (s0.sp - 912#64) rest1.length inner) (by sep_focus) ?_
        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
        exact SepWPpI.of_sepWPp (decodeState_err_push_53f18 hc x ⟨optVn, some ch, inner⟩ w0 0 s0 _ _ R post hpost
          (herr_of_none rfl hdv) (by decide)
          (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
          (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
          (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
          (by unfold decodeStateErrFrame; rw [protoPqRatchetStateAt_some_ch_eq]; simp only [arm64_norm]; ac_rfl))
      · exact absurd hcbnz hx1_ne
  · subst hP
    dsimp only [tripleRatchetProgAtExt, decodeStateName] at hpc ⊢
    have hentry : decodeStateEntry b ext =
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
    decodeState_fetches b (Rust.withPanics ext) 792 4
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::decode_state" = entry
    examples_hide_fetches
    apply SepWPpI.of_sepWP (mid := entry + 2660#64)
    wp_steps 1
    wp_if hcbnz
    · refine SepWP.fold
        (loopCommon_cursor_to_errFrame H_inner b A x rest1 rest1.length ⟨optVn, some ch, inner⟩ s0)
        (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      exact SepWPpI.of_sepWPp (decodeState_err_53f00 hc x ⟨optVn, some ch, inner⟩ w0 s0 _ _ R post hpost (herr_of_ne hwt)
        (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
        (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx21]) (by ac_rfl))
    · exact absurd hcbnz (wireType_ofNat64_ne_zero_of_ne_varint hwt)

/-- Tag 2 (`current_epoch: u64`) in `ChainPB` at `0x53804..0x53820`, `0x5392c..0x53934`
(`+872..+900`, `+1168..+1176`). -/
theorem decodeState_chain_tag2_53804 {H_inner : V1InnerHeapPred} {img : Obj.Image} {b v27 : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_ne : iwt ≠ .varint → spqrDecodeState x.st.bytes = .error .stateDecode)
    (herr_of_none : iwt = .varint → decodeVarint rest1 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 872#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length ⟨optVn, some ch, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommon b A x s0)
    (hloop : ∀ (v : BitVec 64) (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      iwt = .varint →
      decodeVarint rest1 = some (v, rest2) →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 508#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length
          ⟨optVn, some { ch with currentEpoch := v }, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 →
      SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPost H_inner b A x s0 R)) :
    SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  by_cases hwt : iwt = .varint
  · subst hwt
    have hdv_call := hc.decodeVarint2_at
    subst hP
    rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf,
      protoPqRatchetStateCapOkAt_some_ch_eq]
    dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateLoopCommon, WireType.toNat] at hpc hdv_call hx0 ⊢
    have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
    have hentry : decodeStateEntry b ext =
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
    decodeState_fetches b (Rust.withPanics ext) 872 28
    decodeState_fetches b (Rust.withPanics ext) 1168 12
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::decode_state" = entry
    examples_hide_fetches
    apply SepWPpI.of_sepWP (mid := entry + (0x480d4#64 - 0x4e0a4#64))
    wp_steps 3
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
    refine SepWPpI.call_decodeVarint2 hdv_call
      (s0.sp - 336#64) (s0.sp - 1056#64)
      (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1
      (ret_pc := entry + 884#64)
      (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
      (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
      (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
      (hx0 := by simp only [arm64_norm, hx29, hx29_f0])
      (hlen := by omega)
      (hP := by sep_focus) ?_ ?_
    · intro s1 v rest2 hdv hlt2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_v
      have hle2 : rest2.length ≤ rest1.length := Nat.le_of_lt hlt2
      rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
      simp only [arm64_norm, wp_norm] at hx0_0 hx1_v hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      have hsp1_a : s1.spAligned = true := by rw [State.spAligned, hsp1]; exact sp_sub_1392_aligned s0 hs0A
      apply SepWPpI.of_sepWP (mid := entry + 508#64)
      wp_steps 5
      refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
        hrest1_le hrest1_suf hle2) (by sep_focus) ?_
      refine SepWP.fold (optVersionNegotiationPBCapOkAt_mono (A := A) (a := s0.sp - 1040#64)
        (rem1 := rest1.length) (rem2 := rest2.length) (opt := optVn) hle2)
        (by sep_focus) ?_
      refine SepWP.fold (chainLinks_bound_mono (len := ch.links.length) hle2
        (chainLinksVecAt A (s0.sp - 992#64) ch.links)) (by sep_focus) ?_
      refine SepWP.fold (vecU8CapOkAt_mono (A := A) (v := s0.sp - 968#64)
        (rem1 := rest1.length) (rem2 := rest2.length) (bs := ch.nextRoot) hle2)
        (by sep_focus) ?_
      refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_mono (H_inner := H_inner) (A := A)
        (a := s0.sp - 912#64) (rem1 := rest1.length) (rem2 := rest2.length) (opt := inner) hle2)
        (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
      exact hloop v rest2 _ _ rfl hdv hle2 hsuf2
        (by simp only [arm64_norm])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
        (by simp only [arm64_norm, htr1])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by rw [protoPqRatchetStateCapOkAt_some_ch_eq]; dsimp only [decodeStateLoopCommon]; ac_rfl)
    · intro s1 hdv hpc1 hrun1 hsp1 htr1 hcs1 hx0_1 hx1_ne
      rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
      simp only [arm64_norm, wp_norm] at hx0_1 hx1_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      apply SepWPpI.of_sepWP (mid := entry + 2764#64)
      wp_steps 3
      wp_if hcbnz
      · refine SepWP.fold (errFrame_parts_fold A x s0 hrest1_le hrest1_suf) (by sep_focus) ?_
        refine SepWP.fold (optVersionNegotiationPBCapOkAt_entails_optVersionNegotiationPBAt A
          (s0.sp - 1040#64) rest1.length optVn) (by sep_focus) ?_
        refine SepWP.fold (chainLinks_bound_drop ch.links.length rest1.length
          (chainLinksVecAt A (s0.sp - 992#64) ch.links)) (by sep_focus) ?_
        refine SepWP.fold (vecU8CapOkAt_entails_rustBytesVecAt A (s0.sp - 968#64) rest1.length ch.nextRoot)
          (by sep_focus) ?_
        refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_entails_optProtoPqRatchetInnerAt H_inner A
          (s0.sp - 912#64) rest1.length inner) (by sep_focus) ?_
        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
        exact SepWPpI.of_sepWPp (decodeState_err_push_53f68 hc x ⟨optVn, some ch, inner⟩ w0 0 s0 _ _ R post hpost
          (herr_of_none rfl hdv) (by decide)
          (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
          (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
          (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
          (by unfold decodeStateErrFrame; rw [protoPqRatchetStateAt_some_ch_eq]; simp only [arm64_norm]; ac_rfl))
      · exact absurd hcbnz hx1_ne
  · subst hP
    dsimp only [tripleRatchetProgAtExt, decodeStateName] at hpc ⊢
    have hentry : decodeStateEntry b ext =
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
    decodeState_fetches b (Rust.withPanics ext) 872 4
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::decode_state" = entry
    examples_hide_fetches
    apply SepWPpI.of_sepWP (mid := entry + 2740#64)
    wp_steps 1
    wp_if hcbnz
    · refine SepWP.fold
        (loopCommon_cursor_to_errFrame H_inner b A x rest1 rest1.length ⟨optVn, some ch, inner⟩ s0)
        (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      exact SepWPpI.of_sepWPp (decodeState_err_53f50 hc x ⟨optVn, some ch, inner⟩ w0 s0 _ _ R post hpost (herr_of_ne hwt)
        (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
        (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx21]) (by ac_rfl))
    · exact absurd hcbnz (wireType_ofNat64_ne_zero_of_ne_varint hwt)

/-- Tag 4 (`next_root: Vec<u8>`) in `ChainPB` at `0x537d4..0x537e8` (`+824..+844`). -/
theorem decodeState_chain_tag4_537d4 {H_inner : V1InnerHeapPred} {img : Obj.Image} {b v27 : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsX4K H_inner img b A ext)
    (x : DecodeStateGhost) (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none : (Proto.mergeBytes (codecWireTypeToProto iwt) rest1).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 824#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length ⟨optVn, some ch, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommon b A x s0)
    (hloop : ∀ (bs' rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      (Proto.mergeBytes (codecWireTypeToProto iwt) rest1).toOption = some (bs', rest2) →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 508#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length
          ⟨optVn, some { ch with nextRoot := bs' }, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 →
      SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPost H_inner b A x s0 R)) :
    SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hbm := hc.bytesMerge3_at
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf,
    protoPqRatchetStateCapOkAt_some_ch_eq]
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateLoopCommon] at hpc hbm ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 824 24
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPpI.of_sepWP (mid := entry + (0x47d44#64 - 0x4e0a4#64))
  wp_steps 3
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  have hx22_48 : s0.sp - 1040#64 + 72#64 = s0.sp - 968#64 := by bv_omega
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine SepWPpI.call_bytesMerge3 hbm iwt (s0.sp - 968#64) ch.nextRoot
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1
    (ret_pc := entry + 836#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx0])
    (hx1 := by simp only [arm64_norm, hx22, hx22_48])
    (hx2 := by simp only [arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hP := by sep_focus) ?_ ?_
  · intro s1 bs' rest2 hmb hle2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpI.of_sepWP (mid := entry + 508#64)
    wp_steps 3
    refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
      hrest1_le hrest1_suf hle2) (by sep_focus) ?_
    refine SepWP.fold (optVersionNegotiationPBCapOkAt_mono (A := A) (a := s0.sp - 1040#64)
      (rem1 := rest1.length) (rem2 := rest2.length) (opt := optVn) hle2)
      (by sep_focus) ?_
    refine SepWP.fold (chainLinks_bound_mono (len := ch.links.length) hle2
      (chainLinksVecAt A (s0.sp - 992#64) ch.links)) (by sep_focus) ?_
    refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_mono (H_inner := H_inner) (A := A)
      (a := s0.sp - 912#64) (rem1 := rest1.length) (rem2 := rest2.length) (opt := inner) hle2)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    exact hloop bs' rest2 _ _ hmb hle2 hsuf2
      (by simp only [arm64_norm])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
      (by simp only [arm64_norm, htr1])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by rw [protoPqRatchetStateCapOkAt_some_ch_eq]; dsimp only [decodeStateLoopCommon]; ac_rfl)
  · intro s1 hmb hpc1 hrun1 hsp1 htr1 hcs1 hx0_ne
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpI.of_sepWP (mid := entry + 2800#64)
    wp_steps 1
    wp_if hcbnz
    · refine SepWP.fold (errFrame_parts_fold A x s0 hrest1_le hrest1_suf) (by sep_focus) ?_
      refine SepWP.fold (optVersionNegotiationPBCapOkAt_entails_optVersionNegotiationPBAt A
        (s0.sp - 1040#64) rest1.length optVn) (by sep_focus) ?_
      refine SepWP.fold (chainLinks_bound_drop ch.links.length rest1.length
        (chainLinksVecAt A (s0.sp - 992#64) ch.links)) (by sep_focus) ?_
      refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_entails_optProtoPqRatchetInnerAt H_inner A
        (s0.sp - 912#64) rest1.length inner) (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
      exact SepWPpI.of_sepWPp (decodeState_err_push_53f8c hc.toDecodeStateCalleeContracts4K x
        ⟨optVn, some ch, inner⟩ w0 0 s0 _ _ R post hpost
        (herr_of_none hmb) (by decide)
        (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
        (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
        (by unfold decodeStateErrFrame; rw [protoPqRatchetStateAt_some_ch_eq]; simp only [arm64_norm]; ac_rfl))
    · exact absurd hcbnz hx0_ne

/-- Tag 5 (`send_epoch: u64`) in `ChainPB` at `0x53824..0x53840`, `0x53938..0x53940`
(`+904..+932`, `+1180..+1188`). -/
theorem decodeState_chain_tag5_53824 {H_inner : V1InnerHeapPred} {img : Obj.Image} {b v27 : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_ne : iwt ≠ .varint → spqrDecodeState x.st.bytes = .error .stateDecode)
    (herr_of_none : iwt = .varint → decodeVarint rest1 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 904#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length ⟨optVn, some ch, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommon b A x s0)
    (hloop : ∀ (v : BitVec 64) (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      iwt = .varint →
      decodeVarint rest1 = some (v, rest2) →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 508#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length
          ⟨optVn, some { ch with sendEpoch := v }, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 →
      SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPost H_inner b A x s0 R)) :
    SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  by_cases hwt : iwt = .varint
  · subst hwt
    have hdv_call := hc.decodeVarint2_at
    subst hP
    rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf,
      protoPqRatchetStateCapOkAt_some_ch_eq]
    dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateLoopCommon, WireType.toNat] at hpc hdv_call hx0 ⊢
    have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
    have hentry : decodeStateEntry b ext =
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
    decodeState_fetches b (Rust.withPanics ext) 904 28
    decodeState_fetches b (Rust.withPanics ext) 1180 12
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::decode_state" = entry
    examples_hide_fetches
    apply SepWPpI.of_sepWP (mid := entry + (0x480d4#64 - 0x4e0a4#64))
    wp_steps 3
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
    refine SepWPpI.call_decodeVarint2 hdv_call
      (s0.sp - 336#64) (s0.sp - 1056#64)
      (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1
      (ret_pc := entry + 916#64)
      (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
      (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
      (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
      (hx0 := by simp only [arm64_norm, hx29, hx29_f0])
      (hlen := by omega)
      (hP := by sep_focus) ?_ ?_
    · intro s1 v rest2 hdv hlt2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_v
      have hle2 : rest2.length ≤ rest1.length := Nat.le_of_lt hlt2
      rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
      simp only [arm64_norm, wp_norm] at hx0_0 hx1_v hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      have hsp1_a : s1.spAligned = true := by rw [State.spAligned, hsp1]; exact sp_sub_1392_aligned s0 hs0A
      apply SepWPpI.of_sepWP (mid := entry + 508#64)
      wp_steps 5
      refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
        hrest1_le hrest1_suf hle2) (by sep_focus) ?_
      refine SepWP.fold (optVersionNegotiationPBCapOkAt_mono (A := A) (a := s0.sp - 1040#64)
        (rem1 := rest1.length) (rem2 := rest2.length) (opt := optVn) hle2)
        (by sep_focus) ?_
      refine SepWP.fold (chainLinks_bound_mono (len := ch.links.length) hle2
        (chainLinksVecAt A (s0.sp - 992#64) ch.links)) (by sep_focus) ?_
      refine SepWP.fold (vecU8CapOkAt_mono (A := A) (v := s0.sp - 968#64)
        (rem1 := rest1.length) (rem2 := rest2.length) (bs := ch.nextRoot) hle2)
        (by sep_focus) ?_
      refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_mono (H_inner := H_inner) (A := A)
        (a := s0.sp - 912#64) (rem1 := rest1.length) (rem2 := rest2.length) (opt := inner) hle2)
        (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
      exact hloop v rest2 _ _ rfl hdv hle2 hsuf2
        (by simp only [arm64_norm])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
        (by simp only [arm64_norm, htr1])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by rw [protoPqRatchetStateCapOkAt_some_ch_eq]; dsimp only [decodeStateLoopCommon]; ac_rfl)
    · intro s1 hdv hpc1 hrun1 hsp1 htr1 hcs1 hx0_1 hx1_ne
      rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
      simp only [arm64_norm, wp_norm] at hx0_1 hx1_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      apply SepWPpI.of_sepWP (mid := entry + 2624#64)
      wp_steps 3
      wp_if hcbnz
      · refine SepWP.fold (errFrame_parts_fold A x s0 hrest1_le hrest1_suf) (by sep_focus) ?_
        refine SepWP.fold (optVersionNegotiationPBCapOkAt_entails_optVersionNegotiationPBAt A
          (s0.sp - 1040#64) rest1.length optVn) (by sep_focus) ?_
        refine SepWP.fold (chainLinks_bound_drop ch.links.length rest1.length
          (chainLinksVecAt A (s0.sp - 992#64) ch.links)) (by sep_focus) ?_
        refine SepWP.fold (vecU8CapOkAt_entails_rustBytesVecAt A (s0.sp - 968#64) rest1.length ch.nextRoot)
          (by sep_focus) ?_
        refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_entails_optProtoPqRatchetInnerAt H_inner A
          (s0.sp - 912#64) rest1.length inner) (by sep_focus) ?_
        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
        exact SepWPpI.of_sepWPp (decodeState_err_push_53edc hc x ⟨optVn, some ch, inner⟩ w0 0 s0 _ _ R post hpost
          (herr_of_none rfl hdv) (by decide)
          (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
          (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
          (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
          (by unfold decodeStateErrFrame; rw [protoPqRatchetStateAt_some_ch_eq]; simp only [arm64_norm]; ac_rfl))
      · exact absurd hcbnz hx1_ne
  · subst hP
    dsimp only [tripleRatchetProgAtExt, decodeStateName] at hpc ⊢
    have hentry : decodeStateEntry b ext =
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
    decodeState_fetches b (Rust.withPanics ext) 904 4
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::decode_state" = entry
    examples_hide_fetches
    apply SepWPpI.of_sepWP (mid := entry + 2600#64)
    wp_steps 1
    wp_if hcbnz
    · refine SepWP.fold
        (loopCommon_cursor_to_errFrame H_inner b A x rest1 rest1.length ⟨optVn, some ch, inner⟩ s0)
        (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      exact SepWPpI.of_sepWPp (decodeState_err_53ec4 hc x ⟨optVn, some ch, inner⟩ w0 s0 _ _ R post hpost (herr_of_ne hwt)
        (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
        (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx21]) (by ac_rfl))
    · exact absurd hcbnz (wireType_ofNat64_ne_zero_of_ne_varint hwt)

theorem decodeState_chain_tag6_call_5379c {H_inner : V1InnerHeapPred} {img : Obj.Image} {b v27 : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (cp : ChainParamsPB)
    (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (Proto.mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt) cp rest1 99).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 768#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length
        ⟨optVn, some { ch with params := some cp }, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommon b A x s0)
    (hloop : ∀ (cp' : ChainParamsPB) (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      (Proto.mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt) cp rest1 99).toOption =
        some (cp', rest2) →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 508#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length
          ⟨optVn, some { ch with params := some cp' }, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 →
      SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPost H_inner b A x s0 R)) :
    SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hcp_call := hc.chainParamsMerge_at
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf,
    protoPqRatchetStateCapOkAt_some_ch_eq, optChainParamsPBAt_some_ch_eq]
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateLoopCommon] at hpc hcp_call ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 768 24
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPpI.of_sepWP (mid := entry + (0x48900#64 - 0x4e0a4#64))
  wp_steps 3
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  have hx22_74 : s0.sp - 1040#64 + 116#64 = s0.sp - 924#64 := by bv_omega
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine SepWPpI.call_chainParamsMerge hcp_call iwt (s0.sp - 924#64) cp
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1
    (ret_pc := entry + 780#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx0])
    (hx1 := by simp only [arm64_norm, hx22, hx22_74])
    (hx2 := by simp only [arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hP := by sep_focus) ?_ ?_
  · intro s1 cp' rest2 hcp hle2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpI.of_sepWP (mid := entry + 508#64)
    wp_steps 3
    refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
      hrest1_le hrest1_suf hle2) (by sep_focus) ?_
    refine SepWP.fold (optVersionNegotiationPBCapOkAt_mono (A := A) (a := s0.sp - 1040#64)
      (rem1 := rest1.length) (rem2 := rest2.length) (opt := optVn) hle2)
      (by sep_focus) ?_
    refine SepWP.fold (chainLinks_bound_mono (len := ch.links.length) hle2
      (chainLinksVecAt A (s0.sp - 992#64) ch.links)) (by sep_focus) ?_
    refine SepWP.fold (vecU8CapOkAt_mono (A := A) (v := s0.sp - 968#64)
      (rem1 := rest1.length) (rem2 := rest2.length) (bs := ch.nextRoot) hle2)
      (by sep_focus) ?_
    refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_mono (H_inner := H_inner) (A := A)
      (a := s0.sp - 912#64) (rem1 := rest1.length) (rem2 := rest2.length) (opt := inner) hle2)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    exact hloop cp' rest2 _ _ hcp hle2 hsuf2
      (by simp only [arm64_norm])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
      (by simp only [arm64_norm, htr1])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by rw [protoPqRatchetStateCapOkAt_some_ch_eq, optChainParamsPBAt_some_ch_eq]; dsimp only [decodeStateLoopCommon]; ac_rfl)
  · intro s1 n cp' hcp hpc1 hrun1 hsp1 htr1 hcs1 hx0_ne hn_le
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpI.of_sepWP (mid := entry + 2836#64)
    wp_steps 1
    wp_if hcbnz
    · refine SepWP.fold (errFrame_parts_fold A x s0 hrest1_le hrest1_suf) (by sep_focus) ?_
      refine SepWP.fold (optVersionNegotiationPBCapOkAt_entails_optVersionNegotiationPBAt A
        (s0.sp - 1040#64) rest1.length optVn) (by sep_focus) ?_
      refine SepWP.fold (chainLinks_bound_drop ch.links.length rest1.length
        (chainLinksVecAt A (s0.sp - 992#64) ch.links)) (by sep_focus) ?_
      refine SepWP.fold (vecU8CapOkAt_entails_rustBytesVecAt A (s0.sp - 968#64) rest1.length ch.nextRoot)
        (by sep_focus) ?_
      refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_entails_optProtoPqRatchetInnerAt H_inner A
        (s0.sp - 912#64) rest1.length inner) (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
      exact SepWPpI.of_sepWPp (decodeState_err_push_53fb0 hc x ⟨optVn, some { ch with params := some cp' }, inner⟩
        w0 n s0 _ _ R post hpost (herr_of_none hcp) (by omega)
        (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
        (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
        (by unfold decodeStateErrFrame; rw [protoPqRatchetStateAt_some_ch_eq, optChainParamsPBAt_some_ch_eq]; simp only [arm64_norm]; ac_rfl))
    · exact absurd hcbnz hx0_ne

/-- Tag 6 (`params: Option<ChainParamsPB>`) in `ChainPB` at `0x5378c..0x537b0` (`+752..+788`). -/
theorem decodeState_chain_tag6_5378c {H_inner : V1InnerHeapPred} {img : Obj.Image} {b v27 : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (Proto.mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt)
        (ch.params.getD default) rest1 99).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 752#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length ⟨optVn, some ch, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommon b A x s0)
    (hloop : ∀ (cp' : ChainParamsPB) (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      (Proto.mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt)
        (ch.params.getD default) rest1 99).toOption = some (cp', rest2) →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 508#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length
          ⟨optVn, some { ch with params := some cp' }, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 →
      SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPost H_inner b A x s0 R)) :
    SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  rcases ch with ⟨dir, curEp, links, nextRoot, sendEp, _ | cp⟩
  · rw [protoPqRatchetStateCapOkAt_some_ch_eq]
    dsimp only [Option.getD] at herr_of_none hloop ⊢
    have hnone_eq : optChainParamsPBAt (s0.sp - 928#64) none =
        ((s0.sp - 928#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 928#64 + 4#64) 8 := rfl
    rw [hnone_eq]
    dsimp only [tripleRatchetProgAtExt, decodeStateName] at hpc ⊢
    have hentry : decodeStateEntry b ext =
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
    decodeState_fetches b (Rust.withPanics ext) 752 16
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::decode_state" = entry
    examples_hide_fetches
    apply SepWPpI.of_sepWP (mid := entry + 768#64)
    wp_steps 2
    refine SepWP.fold (optChainParamsPBAt_none_to_init (s0.sp - 928#64)) (by sep_focus) ?_
    wp_pull_exists
    wp_steps 2
    have hinit : ((s0.sp - 928#64) ↦₆₄ 1#64) ∗ ((s0.sp - 920#64) ↦₃₂ 0#32) ⊢
        optChainParamsPBAt (s0.sp - 928#64) (some default) := by
      have h1 := optChainParamsPBAt_some_default_init (s0.sp - 928#64)
      have ha8 : s0.sp - 928#64 + 8#64 = s0.sp - 920#64 := by bv_omega
      rw [ha8] at h1
      exact h1
    refine SepWP.fold hinit (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    rw [← hentry, ← decodeStateEntry_eq] at hloop
    exact decodeState_chain_tag6_call_5379c (v27 := v27) hc x w0 optVn
      ⟨dir, curEp, links, nextRoot, sendEp, none⟩ default inner rest1 limit iwt
      hrest1_le hrest1_suf hlen_bound herr_of_none s0 _ _ R post hpost hs0A
      (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
      (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
      (by simp only [arm64_norm, hx29])
      (by rw [protoPqRatchetStateCapOkAt_some_ch_eq]; ac_rfl) hloop
  · rw [protoPqRatchetStateCapOkAt_some_ch_eq, optChainParamsPBAt_some_ch_eq]
    dsimp only [Option.getD] at herr_of_none hloop ⊢
    dsimp only [tripleRatchetProgAtExt, decodeStateName] at hpc ⊢
    have hentry : decodeStateEntry b ext =
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
    decodeState_fetches b (Rust.withPanics ext) 752 8
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::decode_state" = entry
    examples_hide_fetches
    apply SepWPpI.of_sepWP (mid := entry + 768#64)
    wp_steps 2
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    rw [← hentry, ← decodeStateEntry_eq] at hloop
    exact decodeState_chain_tag6_call_5379c (v27 := v27) hc x w0 optVn
      ⟨dir, curEp, links, nextRoot, sendEp, some cp⟩ cp inner rest1 limit iwt
      hrest1_le hrest1_suf hlen_bound herr_of_none s0 _ _ R post hpost hs0A
      (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
      (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
      (by simp only [arm64_norm, hx29])
      (by rw [protoPqRatchetStateCapOkAt_some_ch_eq, optChainParamsPBAt_some_ch_eq]) hloop

/-- Unknown tag (`skip_field`) in `ChainPB` at `0x537ec..0x53800` (`+848..+868`). -/
theorem decodeState_chain_skip_537ec {H_inner : V1InnerHeapPred} {img : Obj.Image} {b v27 : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit tag : Nat) (iwt : WireType)
    (htag : 1 ≤ tag ∧ tag < 2 ^ 32)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none : skipField (2 * rest1.length + 2) 99 tag iwt rest1 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 848#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : BitVec.setWidth 8 (s.readReg64 .x0) = BitVec.ofNat 8 iwt.toNat)
    (hx1 : BitVec.setWidth 32 (s.readReg64 .x1) = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length ⟨optVn, some ch, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommon b A x s0)
    (hloop : ∀ (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      skipField (2 * rest1.length + 2) 99 tag iwt rest1 = some rest2 →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 508#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length ⟨optVn, some ch, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 →
      SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPost H_inner b A x s0 R)) :
    SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hsf_call := hc.skipField3_at
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf]
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateLoopCommon] at hpc hsf_call ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 848 24
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPpI.of_sepWP (mid := entry + (0x4677c#64 - 0x4e0a4#64))
  wp_steps 3
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine SepWPpI.call_skipField3 hsf_call iwt tag 99
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1
    (ret_pc := entry + 860#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx0]) (hx1 := by simp only [arm64_norm, hx1])
    (htag := htag.2) (hx2 := by simp only [arm64_norm, hx29, hx29_f0])
    (hx3 := by simp only [arm64_norm]) (hdepth := by decide) (hlen := by omega)
    (hP := by sep_focus) ?_ ?_
  · intro s1 rest2 hsf hle2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpI.of_sepWP (mid := entry + 508#64)
    wp_steps 2
    refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
      hrest1_le hrest1_suf hle2) (by sep_focus) ?_
    refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A)
      (a := s0.sp - 1040#64) (rem1 := rest1.length) (rem2 := rest2.length)
      (st := ⟨optVn, some ch, inner⟩) hle2) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    exact hloop rest2 _ _ hsf hle2 hsuf2
      (by simp only [arm64_norm])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
      (by simp only [arm64_norm, htr1])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by dsimp only [decodeStateLoopCommon]; ac_rfl)
  · intro s1 hsf hpc1 hrun1 hsp1 htr1 hcs1 hx0_ne
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpI.of_sepWP (mid := entry + 2112#64)
    wp_steps 2
    wp_if hcbz
    · exact absurd hcbz hx0_ne
    · wp_steps 1
      refine SepWP.fold (errFrame_parts_fold A x s0 hrest1_le hrest1_suf) (by sep_focus) ?_
      refine SepWP.fold (protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt H_inner A
        (s0.sp - 1040#64) rest1.length ⟨optVn, some ch, inner⟩) (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
      exact SepWPpI.of_sepWPp (decodeState_err_push_53cdc hc x ⟨optVn, some ch, inner⟩ w0 0 s0 _ _ R post hpost
        (herr_of_none hsf) (by decide)
        (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
        (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
        (by simp only [decodeStateErrFrame, arm64_norm]; ac_rfl))

end CryptoVerification.SpqrV1.Top.DecodeState
