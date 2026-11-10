/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateReloc
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergePart2CodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Shared Tag Entry/Latch Infrastructure and Tag Arm 1 (`KeysUnsampled`) for `V1State::merge`

Defines `InnerStateDiscrFull`, the shared tag entry/continuation bundles (`V1StateTagEntryHyp`,
`V1StateTagCont`), and shared latch tails (`+2680`, `+2692`), and verifies tag arm 1
(`KeysUnsampled`, entry `+300`) to `entry + 2700#64` (`0x4f274`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageMerge

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen hiding vecU8Buf vecU8At_eq_header_sep_buf
open CryptoVerification.SpqrV1.Auth hiding bv64_sub_zero bv64_add_zero
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout
open ChunkedMerge

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
  v1StateMergeJumpTableExpanded optProtoInnerStateJumpTableAt v1StateSavedRegsAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero v1StateMerge_fnOff

/-- Strengthened discriminant relation including `d.toNat < 2 ^ 63` for `Ct1Sampled` with `uc = some _`. -/
def InnerStateDiscrFull (bsLen : Nat) : Option V1State.InnerState → BitVec 64 → Prop
  | none, d => d = none2Cap
  | some (.keysUnsampled _), d => d = 0x8000000000000000#64
  | some (.keysSampled _), d => d = 0x8000000000000001#64
  | some (.headerSent _), d => d = 0x8000000000000002#64
  | some (.ct1Received _), d => d = 0x8000000000000003#64
  | some (.ekSentCt1Received _), d => d = 0x8000000000000004#64
  | some (.noHeaderReceived _), d => d = 0x8000000000000005#64
  | some (.headerReceived _), d => d = 0x8000000000000006#64
  | some (.ct1Sampled s), d =>
      match s.uc with
      | none => d = noneCap
      | some _ => d.toNat < 2 ^ 63 ∧ BytesMergeCapOk d bsLen
  | some (.ekReceivedCt1Sampled _), d => d = 0x8000000000000008#64
  | some (.ct1Acknowledged _), d => d = 0x8000000000000009#64
  | some (.ct2Sampled _), d => d = 0x800000000000000a#64

theorem innerStateDiscrFull_imp_discr {bsLen : Nat} {is : Option V1State.InnerState} {d : BitVec 64}
    (h : InnerStateDiscrFull bsLen is d) : InnerStateDiscr bsLen is d := by
  rcases is with _ | st
  · exact h
  · cases st with
    | ct1Sampled s =>
      rcases s with ⟨_ | u, _, _⟩
      · exact h
      · exact h.2
    | _ => exact h

theorem optProtoInnerStateCapAt_entails_discrFull (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (is : Option V1State.InnerState) :
    optProtoInnerStateCapAt A a bsLen is ⊢
      ∃∗ d : BitVec 64, ⌜InnerStateDiscrFull bsLen is d⌝ ∗ (a ↦₆₄ d) ∗ optProtoInnerStateCapTailAt A a bsLen is d := by
  refine Entails.trans (optProtoInnerStateCapAt_entails_discr A a bsLen is) ?_
  refine ProofLib.Entails.sepExists_elim fun d => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro d)
  refine Entails.pure_left fun hd => ?_
  rcases is with _ | st
  · exact Entails.pure_right hd (Entails.refl _)
  · cases st with
    | ct1Sampled s =>
      rcases s with ⟨_ | u, sendingCt1, receivingEk⟩
      · exact Entails.pure_right hd (Entails.refl _)
      · dsimp only [optProtoInnerStateCapTailAt]
        conv_lhs => rw [← sepConj_assoc, sepExists_sepConj_right, sepExists_sepConj_left]
        refine ProofLib.Entails.sepExists_elim fun ptr => ?_
        have hlt : EncodedLen.vecU8Buf A d ptr u.hdr ⊢ ⌜d.toNat < 2 ^ 63⌝ ∗ EncodedLen.vecU8Buf A d ptr u.hdr :=
          vecU8Buf_entails_cap_lt A d ptr u.hdr
        refine Entails.trans (Entails.of_eq (by ac_rfl :
          ((a ↦₆₄ d) ∗ (((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗
            EncodedLen.vecU8Buf A d ptr u.hdr)) ∗
            ((∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A (a + 0x18#64) cap ptr u.es) ∗
            (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A (a + 0x30#64) cap ptr u.ct1) ∗
            optAuthenticatorPBCapAt A (a + 0x48#64) bsLen u.auth ∗
            ((a + 0x78#64) ↦₆₄ u.epoch) ∗
            optPolynomialEncoderPBAt A (a + 128#64) sendingCt1 ∗
            optPolynomialDecoderPBAt A (a + 184#64) receivingEk) =
          EncodedLen.vecU8Buf A d ptr u.hdr ∗
            ((a ↦₆₄ d) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗
            (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A (a + 0x18#64) cap ptr u.es) ∗
            (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A (a + 0x30#64) cap ptr u.ct1) ∗
            optAuthenticatorPBCapAt A (a + 0x48#64) bsLen u.auth ∗
            ((a + 0x78#64) ↦₆₄ u.epoch) ∗
            optPolynomialEncoderPBAt A (a + 128#64) sendingCt1 ∗
            optPolynomialDecoderPBAt A (a + 184#64) receivingEk))) ?_
        refine Entails.trans (sepConj_mono_left hlt) ?_
        rw [sepConj_assoc]
        refine Entails.pure_left fun hcap_lt => ?_
        refine Entails.pure_right ⟨hcap_lt, hd⟩ ?_
        refine Entails.trans (Entails.of_eq (by ac_rfl :
          EncodedLen.vecU8Buf A d ptr u.hdr ∗
            ((a ↦₆₄ d) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗
            (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A (a + 0x18#64) cap ptr u.es) ∗
            (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A (a + 0x30#64) cap ptr u.ct1) ∗
            optAuthenticatorPBCapAt A (a + 0x48#64) bsLen u.auth ∗
            ((a + 0x78#64) ↦₆₄ u.epoch) ∗
            optPolynomialEncoderPBAt A (a + 128#64) sendingCt1 ∗
            optPolynomialDecoderPBAt A (a + 184#64) receivingEk) =
          (((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗ EncodedLen.vecU8Buf A d ptr u.hdr) ∗
            ((a ↦₆₄ d) ∗
            (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A (a + 0x18#64) cap ptr u.es) ∗
            (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A (a + 0x30#64) cap ptr u.ct1) ∗
            optAuthenticatorPBCapAt A (a + 0x48#64) bsLen u.auth ∗
            ((a + 0x78#64) ↦₆₄ u.epoch) ∗
            optPolynomialEncoderPBAt A (a + 128#64) sendingCt1 ∗
            optPolynomialDecoderPBAt A (a + 184#64) receivingEk))) ?_
        refine Entails.trans (sepConj_mono_left (Entails.sepExists_intro
          (P := fun ptr => ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗ EncodedLen.vecU8Buf A d ptr u.hdr) ptr)) ?_
        exact Entails.of_eq (by ac_rfl)
    | _ => exact Entails.pure_right hd (Entails.refl _)

theorem discrFull_none_add2 {bsLen : Nat} {d : BitVec 64}
    (h : InnerStateDiscrFull bsLen none d) :
    (d + 2#64 == 0#64) = true ∧ (d + 2#64 != 0#64) = false := by
  change d = none2Cap at h; subst h; decide

theorem cap_lt_add2_beq_zero_false {d : BitVec 64} (h : d.toNat < 2 ^ 63) :
    (d + 2#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; intro heq
  have h1 : (d + 2#64).toNat = 0 := by rw [heq]; rfl
  rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl] at h1; omega

theorem cap_lt_add2_bne_zero_true {d : BitVec 64} (h : d.toNat < 2 ^ 63) :
    (d + 2#64 != 0#64) = true := by
  rw [bne_iff_ne]; intro heq
  have h1 : (d + 2#64).toNat = 0 := by rw [heq]; rfl
  rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl] at h1; omega

theorem discrFull_some_add2 {bsLen : Nat} {st : V1State.InnerState} {d : BitVec 64}
    (h : InnerStateDiscrFull bsLen (some st) d) :
    (d + 2#64 == 0#64) = false ∧ (d + 2#64 != 0#64) = true := by
  cases st with
  | ct1Sampled s =>
    rcases s with ⟨_ | u, _, _⟩
    · change d = noneCap at h; subst h; decide
    · exact ⟨cap_lt_add2_beq_zero_false h.1, cap_lt_add2_bne_zero_true h.1⟩
  | _ => subst h; decide

theorem discrFull_ct1Sampled_sub_ne {bsLen : Nat} {s : V1State.Chunked.Ct1Sampled}
    {d c : BitVec 64} (h : InnerStateDiscrFull bsLen (some (.ct1Sampled s)) d)
    (hc1 : 2 ^ 63 ≤ c.toNat) (hc2 : c ≠ noneCap) :
    (d - c == 0#64) = false ∧ (d - c != 0#64) = true := by
  have hne : d - c ≠ 0#64 := by
    intro heq
    have hdc : d = c := by rw [← BitVec.add_zero c, ← heq]; bv_lin
    subst hdc
    rcases s with ⟨_ | u, _, _⟩
    · exact hc2 h
    · have := h.1; omega
  exact ⟨beq_eq_false_iff_ne.mpr hne, bne_iff_ne.mpr hne⟩

/-- Bundled entry hypotheses for any tag arm `1..11` after `BR X10` (`+296`). -/
structure V1StateTagEntryHyp (img : Obj.Image) (b : BitVec 64)
    (H : String → Option (State → State)) (s0 : State) (x : V1StateMergeGhost)
    (m : V1State) (rest : List (BitVec 8)) (iwt : WireType) (limit : Nat) (s : State) : Prop where
  hsp_align : (s0.sp &&& 15#64 == 0#64) = true
  hb_align : b &&& 0xfff#64 = 0#64
  hrest_le : rest.length ≤ x.bs.length
  hrest_lt : rest.length < 2 ^ 63
  hrest_suf : IsDropSuffix x.bs rest
  hpoly : OptInnerStatePolyBound rest.length m.innerState
  hrun : s.status = .Running
  hsp : s.sp = s0.sp - 816#64
  htr : s.v1TraceEq s0
  hx0 : (s.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 iwt.toNat
  hx9 : InnerStateDiscrFull rest.length m.innerState (s.readReg64 (Reg.gpr 9#5))
  hregs : V1StateLoopRegs b s0 x limit s
  hinv : ImgCallInv img s

/-- Bundled continuation at `entry + 2700#64` (`0x4f274`) for tag `k` (`1..11`). -/
structure V1StateTagCont (img : Obj.Image) (b : BitVec 64) (A : RustAlloc)
    (H : String → Option (State → State)) (s0 : State) (x : V1StateMergeGhost) (R : SepProp)
    (k : Nat) (m : V1State) (rest : List (BitVec 8)) (iwt : WireType) (limit : Nat) : Prop where
  onErr :
    (V1State.mergeField m (BitVec.ofNat 32 k) (codecWireTypeToProto iwt) rest 99).toOption = none →
    ∀ (s' : State) (err : BitVec 64) (n_err : Nat),
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64 →
      s'.status = .Running → s'.sp = s0.sp - 816#64 → s'.v1TraceEq s0 →
      s'.readReg64 (Reg.gpr 21#5) = err → err ≠ 0#64 → n_err ≤ 3 →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (decodeErrorAtStackLen A err n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
          memRegion (s0.sp - 816#64) 720 ∗
          v1StateErrFrame A b s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
        (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0)
  onOk :
    ∀ (m' : V1State) (rest' : List (BitVec 8)) (s' : State),
      (V1State.mergeField m (BitVec.ofNat 32 k) (codecWireTypeToProto iwt) rest 99).toOption = some (m', rest') →
      OptInnerStatePolyBound rest'.length m'.innerState →
      rest'.length ≤ rest.length →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64 →
      s'.status = .Running → s'.sp = s0.sp - 816#64 → s'.v1TraceEq s0 →
      s'.readReg64 (Reg.gpr 21#5) = 0#64 →
      V1StateLoopRegs b s0 x limit s' →
      ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m' x.bs rest')
        (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0)

/-- Shared tail `entry + 2692#64 -> entry + 2700#64` (`0x4f26c..0x4f274`):
restores `X22 = 0x8000000000000000#64` and `X23 = 0xffffffffffffffff#64`. -/
theorem v1State_tail_2692 {b : BitVec 64} {H : String → Option (State → State)}
    {s0 s : State} {P : SepProp} {post panic : State → SepProp → Prop}
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2692#64)
    (hrun : s.status = .Running)
    (hcont : ∀ s' : State,
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64 →
      s'.status = .Running → s'.sp = s.sp → s'.v1TraceEq s →
      s'.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) →
      s'.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) →
      s'.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) →
      s'.readReg64 (Reg.gpr 22#5) = 0x8000000000000000#64 →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) →
      s'.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) →
      s'.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) →
      s'.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) →
      s'.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) →
      s'.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5) →
      (∀ img, ImgCallInv img s → ImgCallInv img s') →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s' P post panic) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s P post panic := by
  v1StateMerge_fetches b H 2692 8
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2700#64)
  wp_steps; wp_reach
  exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (fun _ hinv => ⟨by simpa only [Obj.Image.FrozenLoaded, arm64_norm] using hinv.1,
      by simpa only [arm64_norm] using hinv.2⟩)

/-- Shared tail `entry + 2680#64 -> entry + 2700#64` (`0x4f260..0x4f274`):
restores `X24 = X27`, `X25 = SP + 240`, `X27 = -2`, `X22 = 2^63`, `X23 = -1`. -/
theorem v1State_tail_2680 {b : BitVec 64} {H : String → Option (State → State)}
    {s0 s : State} {P : SepProp} {post panic : State → SepProp → Prop}
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2680#64)
    (hrun : s.status = .Running)
    (hcont : ∀ s' : State,
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64 →
      s'.status = .Running → s'.sp = s.sp → s'.v1TraceEq s →
      s'.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) →
      s'.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) →
      s'.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) →
      s'.readReg64 (Reg.gpr 22#5) = 0x8000000000000000#64 →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 27#5) →
      s'.readReg64 (Reg.gpr 25#5) = s.sp + 240#64 →
      s'.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) →
      s'.readReg64 (Reg.gpr 27#5) = 0xfffffffffffffffe#64 →
      s'.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) →
      s'.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5) →
      (∀ img, ImgCallInv img s → ImgCallInv img s') →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s' P post panic) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s P post panic := by
  v1StateMerge_fetches b H 2680 20
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2700#64)
  wp_steps; wp_reach
  exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (fun _ hinv => ⟨by simpa only [Obj.Image.FrozenLoaded, arm64_norm] using hinv.1,
      by simpa only [arm64_norm] using hinv.2⟩)

/-! ## 1. Tag 1 (`KeysUnsampled`, `+300..+332`, `+1472..+1564`, `+2632..+2700`) -/

theorem v1State_tag1_inplace {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hKuCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x206c#64)
      ((chunkedKeysUnsampledMergeSpec A).inImage img))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {ku : V1State.Chunked.KeysUnsampled}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_is : m.innerState = some (.keysUnsampled ku))
    (hentry : V1StateTagEntryHyp img b H s0 x m rest iwt limit s)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 300#64)
    (hcont : V1StateTagCont img b A H s0 x R 1 m rest iwt limit) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, hb_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  obtain ⟨honErr, honOk⟩ := hcont
  rw [hm_is] at hx9
  change s.readReg64 (Reg.gpr 9#5) = 0x8000000000000000#64 at hx9
  have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := by rw [hx9]; decide
  have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000000#64) = false := by rw [hx9]; decide
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  v1StateMerge_fetches b H 300 36
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_img (mid := entry + 0x206c#64) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPre, hm_is, optProtoInnerStateCapAt, protoInnerStateCapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  simp only [sepConj_assoc]
  wp_steps; wp_reach; intro hinv_c
  refine SepWPp.call_frame_inImage (hinv := hinv_c)
    (x := ⟨iwt, x.msgPtr + 8#64, ku, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 328#64) hKuCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [chunkedKeysUnsampledMergeSpec]; simp only [arm64_norm, hsp, hx0, hx20, hx19]; rfl)
    (⟨rfl, rfl, rfl, hrest_lt⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        x.msgPtr + 8#64 = x.msgPtr + 8#64 ∧ x.bufRef = x.bufRef ∧ rest.length < 2 ^ 63)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedKeysUnsampledMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hm_field := v1State_mergeField_tag1 m iwt rest 99
  rw [hm_is] at hm_field; dsimp only at hm_field
  cases hku_res : (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto iwt) ku rest 99).toOption with
  | none =>
    rw [hku_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := entry + 2700#64)
    conv =>
      arg 4
      simp only [chunkedKeysUnsampledMergeSpec, hku_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro ku'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hfold_is : (x.msgPtr ↦₆₄ 0x8000000000000000#64) ∗
        chunkedKeysUnsampledPBAt A (x.msgPtr + 8#64) ku' ∗ memRegion (x.msgPtr + 64#64) 160 ⊢
        ∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is' := by
      rw [chunkedKeysUnsampledPBAt_eq_proto]
      exact optProtoInnerStateAt_entails_exists A x.msgPtr (some (.keysUnsampled ku'))
    apply SepWP.fold hfold_is (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFrame A b s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFrame]; ac_rfl))
    exact honErr hm_field _ (sm.readReg64 (Reg.gpr 0#5)) n_err
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm0 hn_err
  | some p =>
    rcases p with ⟨ku', rest'⟩
    rw [hku_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hku_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.keysUnsampled ku')) := by
      have h56 := optInnerStatePolyBound_lt_2_56 hpoly
      unfold OptInnerStatePolyBound InnerStatePolyBound; omega
    refine SepWPp.of_sepWP_img (mid := entry + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedKeysUnsampledMergeSpec, hku_res,
        sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.keysUnsampled ku') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPre, optProtoInnerStateCapAt, protoInnerStateCapAt]; ac_rfl))
    exact honOk { m with innerState := some (.keysUnsampled ku') } rest' _ hm_field hpoly' hrest'_le
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hsm0])
      ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m],
       by simp only [arm64_norm, hx22_m], by simp only [arm64_norm, hx23_m],
       by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hfp_m]⟩ hinv_n

theorem memRegion_split_tag1_temp (sp : BitVec 64) :
    memRegion (sp - 816#64) 720 =
      memRegion (sp - 816#64) 8 ∗
      (∃∗ w_sp8 : BitVec 64, ((sp - 808#64) ↦₆₄ w_sp8)) ∗
      memRegion (sp - 800#64) 224 ∗
      (∃∗ w_sp240 : BitVec 64, ((sp - 576#64) ↦₆₄ w_sp240)) ∗
      memRegion (sp - 568#64) 48 ∗
      memRegion (sp - 520#64) 424 := by
  have s1 := memRegion_split' (b := sp - 816#64) (b' := sp - 808#64) (n := 8) (k := 712) (N := 720) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := sp - 808#64) (b' := sp - 800#64) (n := 8) (k := 704) (N := 712) rfl (by bv_lin) (by decide)
  have s3 := memRegion_split' (b := sp - 800#64) (b' := sp - 576#64) (n := 224) (k := 480) (N := 704) rfl (by bv_lin) (by decide)
  have s4 := memRegion_split' (b := sp - 576#64) (b' := sp - 568#64) (n := 8) (k := 472) (N := 480) rfl (by bv_lin) (by decide)
  have s5 := memRegion_split' (b := sp - 568#64) (b' := sp - 520#64) (n := 48) (k := 424) (N := 472) rfl (by bv_lin) (by decide)
  rw [s1, s2, s3, s4, s5, ProofLib.memRegion_eight (sp - 808#64), ProofLib.memRegion_eight (sp - 576#64)]

theorem memRegion_fold_tag1_temp (sp : BitVec 64)
    (w_sp8 w0 w1 w2 w3 w4 w5 w6 : BitVec 64) :
    memRegion (sp - 816#64) 8 ∗ ((sp - 808#64) ↦₆₄ w_sp8) ∗ memRegion (sp - 800#64) 224 ∗
      words7At (sp - 576#64) w0 w1 w2 w3 w4 w5 w6 ∗ memRegion (sp - 520#64) 424 ⊢
      memRegion (sp - 816#64) 720 := by
  have h56 : words7At (sp - 576#64) w0 w1 w2 w3 w4 w5 w6 ⊢
      (∃∗ v : BitVec 64, ((sp - 576#64) ↦₆₄ v)) ∗ memRegion (sp - 568#64) 48 := by
    have h48 : (sp - 576#64) + 8#64 = sp - 568#64 := by bv_lin
    have h16 : (sp - 576#64) + 16#64 = sp - 560#64 := by bv_lin
    have h24 : (sp - 576#64) + 24#64 = sp - 552#64 := by bv_lin
    have h32 : (sp - 576#64) + 32#64 = sp - 544#64 := by bv_lin
    have h40 : (sp - 576#64) + 40#64 = sp - 536#64 := by bv_lin
    have h48' : (sp - 576#64) + 48#64 = sp - 528#64 := by bv_lin
    rw [ ← h48, memRegion_48_eq_words6 (sp - 576#64)]; dsimp only [words7At]
    refine sepConj_mono (Entails.sepExists_intro w0) ?_
    refine Entails.trans ?_ (Entails.sepExists_intro w6); refine Entails.trans ?_ (Entails.sepExists_intro w5)
    refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w3)
    refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w1)
    exact Entails.refl _
  rw [memRegion_split_tag1_temp sp]
  refine Entails.trans (Entails.of_eq (by ac_rfl :
    memRegion (sp - 816#64) 8 ∗ ((sp - 808#64) ↦₆₄ w_sp8) ∗ memRegion (sp - 800#64) 224 ∗
      words7At (sp - 576#64) w0 w1 w2 w3 w4 w5 w6 ∗ memRegion (sp - 520#64) 424 =
    memRegion (sp - 816#64) 8 ∗ ((sp - 808#64) ↦₆₄ w_sp8) ∗ memRegion (sp - 800#64) 224 ∗
      (words7At (sp - 576#64) w0 w1 w2 w3 w4 w5 w6) ∗ memRegion (sp - 520#64) 424)) ?_
  refine sepConj_mono_right (sepConj_mono (Entails.sepExists_intro w_sp8) (sepConj_mono_right ?_))
  rw [← sepConj_assoc]
  exact sepConj_mono_left h56

theorem memRegion_224_split_tag1_ok (a : BitVec 64) :
    memRegion a 224 =
      ∃∗ vd : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v4 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v0 : BitVec 64,
        (a ↦₆₄ vd) ∗ words7At (a + 8#64) v0 v1 v2 v3 v4 v5 v6 ∗ memRegion (a + 64#64) 160 := by
  have s1 := memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 216) (N := 224) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := a + 8#64) (b' := a + 64#64) (n := 56) (k := 160) (N := 216) rfl (by bv_lin) (by decide)
  rw [s1, s2, ProofLib.memRegion_eight a, sepExists_sepConj_left, memRegion_56_eq_words7 (a + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem vecU8CapHeap_entails_dealloc (A : RustAlloc) (bsLen : Nat) (v : List (BitVec 8))
    (w0 w1 w2 : BitVec 64) :
    vecU8CapHeap A bsLen v w0 w1 w2 ⊢ ⌜w0.toNat < 2 ^ 63⌝ ∗ vecCapPtrDealloc A w0 w1 := by
  dsimp only [vecU8CapHeap, EncodedLen.vecU8Buf, vecCapPtrDealloc]
  refine Entails.pure_left fun _ => Entails.pure_left fun ⟨hle, hcap_lt, _⟩ => ?_
  have hbeq : ((w0 == 0#64) = true) ↔ w0 = 0 := beq_iff_eq
  simp only [hbeq]
  refine Entails.pure_right hcap_lt ?_
  by_cases h0 : w0 = 0
  · simp [h0]; exact Entails.refl _
  · simp only [h0, ↓reduceIte]
    have hsplit : w0.toNat = v.length + (w0.toNat - v.length) := by omega
    have hbound : v.length + (w0.toNat - v.length) ≤ 2 ^ 64 := by omega
    conv_rhs => arg 2; rw [hsplit, ProofLib.memRegion_split w1 v.length (w0.toNat - v.length) hbound]
    exact sepConj_mono_right (sepConj_mono_left (pointsToBytes_entails_memRegion w1 v))

theorem cap_lt_add2_ult_two_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    BitVec.ult (cap + 2#64) 2#64 = false := by
  rw [BitVec.ult, decide_eq_false_iff_not]
  have hadd : (cap + 2#64).toNat = cap.toNat + 2 := by
    rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
  rw [hadd, show (2#64 : BitVec 64).toNat = 2 from rfl]; omega

theorem cap_lt_add2_cc_two_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    ConditionHolds .CC (subsPState64 (cap + 2#64) 2#64) = false := by
  rw [conditionHolds_cc_subsPState64, cap_lt_add2_ult_two_false h]

private theorem v1State_tag1_dealloc_x24 {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x493f0))
      (rustDeallocSpec A))
    {s : State} {fsp w0 w1 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1524#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = w0) (hx25 : s.readReg64 (Reg.gpr 25#5) = w1) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1544#64) s
      (vecCapPtrDealloc A w0 w1 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5)) := by
  simp only [rustDeallocSpec] at hDealloc
  v1StateMerge_fetches b H 1524 20
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  dsimp only [vecCapPtrDealloc]
  by_cases hw0 : (w0 == 0#64) = true <;>
    simp only [hw0, ↓reduceIte, Bool.false_eq_true, sepConj_emp, emp_sepConj]
  · have hbr : (s.readReg64 (Reg.gpr 24#5) == 0#64) = true := by rw [hx24]; exact hw0
    wp_steps; wp_done
  · have hbr : (s.readReg64 (Reg.gpr 24#5) == 0#64) = false := by
      rw [hx24]; exact Bool.eq_false_iff.mpr hw0
    wp_steps; wp_apply
    exact align_pre (by rw [hsp]) (by wp_done)

private theorem v1State_tag1_dealloc_x22 {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x493f0))
      (rustDeallocSpec A))
    {s : State} {fsp w3 w4 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1544#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = w3) (hx23 : s.readReg64 (Reg.gpr 23#5) = w4) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2680#64) s
      (vecCapPtrDealloc A w3 w4 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [rustDeallocSpec] at hDealloc
  v1StateMerge_fetches b H 1544 24
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  dsimp only [vecCapPtrDealloc]
  by_cases hw3 : (w3 == 0#64) = true <;>
    simp only [hw3, ↓reduceIte, Bool.false_eq_true, sepConj_emp, emp_sepConj]
  · have hbr : (s.readReg64 (Reg.gpr 22#5) == 0#64) = true := by rw [hx22]; exact hw3
    wp_steps; wp_done
  · have hbr : (s.readReg64 (Reg.gpr 22#5) == 0#64) = false := by
      rw [hx22]; exact Bool.eq_false_iff.mpr hw3
    wp_steps; wp_apply; wp_steps
    exact align_pre (by rw [hsp]) (by wp_done)

private theorem v1State_tag1_ok_copy_2632 {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropInner : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffd8ec#64)
      (dropOptProtoInnerStateSpec A b))
    {s : State} {fsp mPtr w_sp8 w0 w1 w2 w3 w4 w5 w6 : BitVec 64}
    {is : Option V1State.InnerState} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true) (hb_align : b &&& 4095#64 = 0#64)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2632#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = w3) (hx23 : s.readReg64 (Reg.gpr 23#5) = w4)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = w0) (hx25 : s.readReg64 (Reg.gpr 25#5) = w1) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2680#64) s
      (optProtoInnerStateAt A mPtr is ∗ A.pool ∗ optProtoInnerStateJumpTableAt b ∗
        stackAt fsp dropStack96 ∗ words7At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗
        ((fsp + 8#64) ↦₆₄ w_sp8) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words7At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗ ((fsp + 8#64) ↦₆₄ w2) ∗
          (mPtr ↦₆₄ 0x8000000000000000#64) ∗ words7At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 ∗
          memRegion (mPtr + 64#64) 160 ∗ A.pool ∗ optProtoInnerStateJumpTableAt b ∗
          stackAt fsp dropStack96 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  simp only [dropOptProtoInnerStateSpec] at hDropInner
  v1StateMerge_fetches b H 2632 48
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  dsimp only [words7At]
  wp_steps; wp_apply
  dsimp only [optProtoInnerStateSize]
  rw [memRegion_224_split_tag1_ok mPtr]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro vd
  apply SepWP.exists_elim; intro v6
  apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4
  apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v2
  apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0
  dsimp only [words7At]
  wp_steps; wp_done

theorem tag1_err_heap_dealloc (A : RustAlloc) (ku : V1State.Chunked.KeysUnsampled)
    (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) :
    optUnchunked2CapHeap A 0 (ku.uc.map fun u => (u.epoch, u.auth)) w0 w1 w2 w3 w4 w5 w6 ⊢
      if ConditionHolds .CC (subsPState64 (w0 + 2#64) 2#64) then emp
      else vecCapPtrDealloc A w0 w1 ∗ vecCapPtrDealloc A w3 w4 := by
  rcases ku with ⟨_ | ⟨epoch, auth⟩⟩
  · dsimp only [Option.map, optUnchunked2CapHeap]
    rw [← sepConj_emp ⌜w0 = noneCap2⌝]
    refine Entails.pure_left fun hw0 => ?_; subst hw0
    have hcc : ConditionHolds .CC (subsPState64 (noneCap2 + 2#64) 2#64) = true := by
      rw [conditionHolds_cc_subsPState64]; unfold noneCap2; decide
    simp only [hcc, ↓reduceIte]; exact Entails.refl _
  · rcases auth with _ | auth
    · dsimp only [Option.map, optUnchunked2CapHeap, unchunked2CapHeap, optAuthCapHeap]
      refine Entails.pure_left fun hw0 => ?_; subst hw0
      rw [← sepConj_emp ⌜w6 = epoch⌝]
      refine Entails.pure_left fun _ => ?_
      have hcc : ConditionHolds .CC (subsPState64 (noneCap + 2#64) 2#64) = true := by
        rw [conditionHolds_cc_subsPState64]; unfold noneCap; decide
      simp only [hcc, ↓reduceIte]; exact Entails.refl _
    · dsimp only [Option.map, optUnchunked2CapHeap, unchunked2CapHeap, optAuthCapHeap]
      refine Entails.trans (sepConj_mono_left (sepConj_mono
        (vecU8CapHeap_entails_dealloc A 0 auth.rootKey w0 w1 w2)
        (vecU8CapHeap_entails_dealloc A 0 auth.macKey w3 w4 w5))) ?_
      refine Entails.trans (Entails.of_eq (by ac_rfl :
        ((⌜w0.toNat < 2 ^ 63⌝ ∗ vecCapPtrDealloc A w0 w1) ∗
          (⌜w3.toNat < 2 ^ 63⌝ ∗ vecCapPtrDealloc A w3 w4)) ∗ ⌜w6 = epoch⌝ =
        ⌜w0.toNat < 2 ^ 63⌝ ∗ ⌜w3.toNat < 2 ^ 63⌝ ∗ ⌜w6 = epoch⌝ ∗
          (vecCapPtrDealloc A w0 w1 ∗ vecCapPtrDealloc A w3 w4))) ?_
      refine Entails.pure_left fun hw0 => Entails.pure_left fun _ => Entails.pure_left fun _ => ?_
      rw [cap_lt_add2_cc_two_false hw0]; simp only [Bool.false_eq_true, ↓reduceIte]
      exact Entails.refl _

theorem chunkedKeysUnsampledPBAt_entails_err_dealloc (A : RustAlloc) (a : BitVec 64)
    (ku : V1State.Chunked.KeysUnsampled) :
    chunkedKeysUnsampledPBAt A a ku ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
        words7At a w0 w1 w2 w3 w4 w5 w6 ∗
        (if ConditionHolds .CC (subsPState64 (w0 + 2#64) 2#64) then emp
         else vecCapPtrDealloc A w0 w1 ∗ vecCapPtrDealloc A w3 w4) := by
  dsimp only [chunkedKeysUnsampledPBAt]
  refine Entails.trans (optKeysUnsampledPBAt_entails_cap_zero A a ku.uc) ?_
  rw [optKeysUnsampledPBCapAt_eq_optUnchunked2]
  refine Entails.trans (optUnchunked2CapAt_extract_words A a 0 (ku.uc.map fun u => (u.epoch, u.auth))) ?_
  refine ProofLib.Entails.sepExists_elim fun w0 => ProofLib.Entails.sepExists_elim fun w1 =>
    ProofLib.Entails.sepExists_elim fun w2 => ProofLib.Entails.sepExists_elim fun w3 =>
    ProofLib.Entails.sepExists_elim fun w4 => ProofLib.Entails.sepExists_elim fun w5 =>
    ProofLib.Entails.sepExists_elim fun w6 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro w0); refine Entails.trans ?_ (Entails.sepExists_intro w1)
  refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w3)
  refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w5)
  refine Entails.trans ?_ (Entails.sepExists_intro w6)
  exact sepConj_mono_right (tag1_err_heap_dealloc A ku w0 w1 w2 w3 w4 w5 w6)

private theorem v1State_tag1_err_1512 {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x493f0))
      (rustDeallocSpec A))
    {s : State} {fsp w0 w1 w3 w4 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1512#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = w3) (hx23 : s.readReg64 (Reg.gpr 23#5) = w4)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = w0) (hx25 : s.readReg64 (Reg.gpr 25#5) = w1) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2680#64) s
      ((if ConditionHolds .CC (subsPState64 (w0 + 2#64) 2#64) then emp
        else vecCapPtrDealloc A w0 w1 ∗ vecCapPtrDealloc A w3 w4) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  by_cases hcc : ConditionHolds .CC (subsPState64 (w0 + 2#64) 2#64) = true <;>
    simp only [hcc, ↓reduceIte, Bool.false_eq_true, sepConj_emp, emp_sepConj]
  · v1StateMerge_fetches b H 1512 12
    generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
    examples_hide_fetches
    have hbr : ConditionHolds .CC (subsPState64 (s.readReg64 (Reg.gpr 24#5) + 2#64) 2#64) = true := by
      rw [hx24]; exact hcc
    wp_steps; wp_done
  · have hstep1 : SepWP (libsignalSessionCode.rebase b H)
        ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1524#64) s
        ((vecCapPtrDealloc A w0 w1 ∗ vecCapPtrDealloc A w3 w4) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun s1 P1 =>
          (P1 ⊢ vecCapPtrDealloc A w0 w1 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ (vecCapPtrDealloc A w3 w4 ∗ Frame)) ∧
          s1.sp = s.sp ∧ s1.v1TraceEq s ∧
          s1.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
          s1.readReg64 (Reg.gpr 22#5) = w3 ∧ s1.readReg64 (Reg.gpr 23#5) = w4 ∧
          s1.readReg64 (Reg.gpr 24#5) = w0 ∧ s1.readReg64 (Reg.gpr 25#5) = w1) := by
      v1StateMerge_fetches b H 1512 12
      generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
      examples_hide_fetches
      have hbr : ConditionHolds .CC (subsPState64 (s.readReg64 (Reg.gpr 24#5) + 2#64) 2#64) = false := by
        rw [hx24]; exact Bool.eq_false_iff.mpr hcc
      wp_steps; wp_done
    refine SepWP.seq hstep1 ?_
    rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1⟩
    refine SepWP.weaken_pre hP1 ?_
    refine SepWP.seq (v1State_tag1_dealloc_x24 hDealloc hsp_align hpc1 hrun1 (hsp1.trans hsp) hx24_1 hx25_1) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx21_2, hx22_2, hx23_2⟩
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl :
      A.pool ∗ stackAt fsp allocHookStack ∗ (vecCapPtrDealloc A w3 w4 ∗ Frame) =
      vecCapPtrDealloc A w3 w4 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame))) ?_
    refine SepWP.mono (v1State_tag1_dealloc_x22 hDealloc hsp_align hpc2 hrun2 (hsp2.trans (hsp1.trans hsp))
      (hx22_2.trans hx22_1) (hx23_2.trans hx23_1)) ?_
    rintro s3 P3 _ _ ⟨hP3, hsp3, htr3, hx21_3⟩
    exact ⟨hP3, hsp3.trans (hsp2.trans hsp1), htr3.trans (htr2.trans htr1), hx21_3.trans (hx21_2.trans hx21_1)⟩

private theorem v1State_tag1_load_ok_1496 {b : BitVec 64} {H : String → Option (State → State)}
    {s : State} {fsp w0 w1 w2 w3 w4 w5 w6 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1496#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2632#64) s
      (words7At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words7At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        sm.readReg64 (Reg.gpr 21#5) = 0#64 ∧
        sm.readReg64 (Reg.gpr 22#5) = w3 ∧ sm.readReg64 (Reg.gpr 23#5) = w4 ∧
        sm.readReg64 (Reg.gpr 24#5) = w0 ∧ sm.readReg64 (Reg.gpr 25#5) = w1 ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  v1StateMerge_fetches b H 1496 16
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  dsimp only [words7At]
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = true := by rw [hx0]; rfl
  wp_steps; wp_done

private theorem v1State_tag1_load_err_1496 {b : BitVec 64} {H : String → Option (State → State)}
    {s : State} {fsp w0 w1 w2 w3 w4 w5 w6 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1496#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) ≠ 0#64) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1512#64) s
      (words7At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words7At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 0#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = w3 ∧ sm.readReg64 (Reg.gpr 23#5) = w4 ∧
        sm.readReg64 (Reg.gpr 24#5) = w0 ∧ sm.readReg64 (Reg.gpr 25#5) = w1) := by
  v1StateMerge_fetches b H 1496 16
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  dsimp only [words7At]
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0
  wp_steps; wp_done

theorem tag1_reconstruct_innerState (A : RustAlloc) (mPtr : BitVec 64) (bsLen : Nat)
    (ku : V1State.Chunked.KeysUnsampled) (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) :
    (mPtr ↦₆₄ 0x8000000000000000#64) ∗ words7At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 ∗
      optUnchunked2CapHeap A bsLen (ku.uc.map fun u => (u.epoch, u.auth)) w0 w1 w2 w3 w4 w5 w6 ∗
      memRegion (mPtr + 64#64) 160 ⊢
      optProtoInnerStateCapAt A mPtr bsLen (some (.keysUnsampled ku)) := by
  dsimp only [optProtoInnerStateCapAt, protoInnerStateCapAt, chunkedKeysUnsampledPBCapAt]
  rw [optKeysUnsampledPBCapAt_eq_optUnchunked2]
  refine Entails.trans (Entails.of_eq (by ac_rfl :
    (mPtr ↦₆₄ 0x8000000000000000#64) ∗ words7At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 ∗
      optUnchunked2CapHeap A bsLen (ku.uc.map fun u => (u.epoch, u.auth)) w0 w1 w2 w3 w4 w5 w6 ∗
      memRegion (mPtr + 64#64) 160 =
    (mPtr ↦₆₄ 0x8000000000000000#64) ∗
      (words7At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 ∗
        optUnchunked2CapHeap A bsLen (ku.uc.map fun u => (u.epoch, u.auth)) w0 w1 w2 w3 w4 w5 w6) ∗
      memRegion (mPtr + 64#64) 160)) ?_
  exact sepConj_mono_right (sepConj_mono_left
    (optUnchunked2CapAt_of_words A (mPtr + 8#64) bsLen (ku.uc.map fun u => (u.epoch, u.auth)) w0 w1 w2 w3 w4 w5 w6))

private theorem v1State_tag1_setup_1472 {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    {s : State} {fsp w_sp240 : BitVec 64} {restLen : Nat} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1472#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x206c#64) s
      (((fsp + 240#64) ↦₆₄ w_sp240) ∗ memRegion (fsp + 248#64) 48 ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢ chunkedKeysUnsampledPBCapAt A (fsp + 240#64) restLen default ∗ Frame) ∧
        s1.sp = s.sp ∧ s1.v1TraceEq s ∧
        s1.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) ∧
        s1.readReg64 (Reg.gpr 1#5) = fsp + 240#64 ∧
        s1.readReg64 (Reg.gpr 2#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 Reg.lr = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1496#64 ∧
        s1.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        s1.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        s1.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        s1.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s1.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s1.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        s1.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s1.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        s1.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hdef_ku : ((fsp + 240#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ memRegion (fsp + 248#64) 48 ⊢
      chunkedKeysUnsampledPBCapAt A (fsp + 240#64) restLen default := by
    dsimp only [chunkedKeysUnsampledPBCapAt, default, Inhabited.default, optKeysUnsampledPBCapAt, noneCap2]
    have h8 : (fsp + 240#64) + 8#64 = fsp + 248#64 := by bv_lin
    rw [h8]; exact Entails.refl _
  v1StateMerge_fetches b H 1472 24
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  wp_steps
  apply SepWP.fold hdef_ku (by sep_focus)
  wp_done

theorem v1State_tag1_at_1472 {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hKuCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x206c#64)
      ((chunkedKeysUnsampledMergeSpec A).inImage img))
    (hDropInner : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffd8ec#64)
      (dropOptProtoInnerStateSpec A b))
    (hDealloc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x493f0))
      (rustDeallocSpec A))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_not : ∀ ku, m.innerState ≠ some (.keysUnsampled ku))
    (hentry : V1StateTagEntryHyp img b H s0 x m rest iwt limit s)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1472#64)
    (hcont : V1StateTagCont img b A H s0 x R 1 m rest iwt limit) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, hb_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, _hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfsp_align : ((s0.sp - 816#64) &&& 15#64 == 0#64) = true := by
    simpa only [arm64_norm] using hsp_align
  have hfsp240 : (s0.sp - 816#64) + 240#64 = s0.sp - 576#64 := by bv_lin
  have hfsp248 : (s0.sp - 816#64) + 248#64 = s0.sp - 568#64 := by bv_lin
  have hfsp8 : (s0.sp - 816#64) + 8#64 = s0.sp - 808#64 := by bv_lin
  refine SepWPp.of_sepWP_img (mid := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x206c#64) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPre, memRegion_split_tag1_temp s0.sp, sliceCursorAfter_eq_split hrest_le hrest_suf]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp240
  apply SepWP.exists_elim; intro w_sp8
  rw [← hfsp240, ← hfsp248]
  refine SepWP.weaken_pre (P' := (((s0.sp - 816#64) + 240#64) ↦₆₄ w_sp240) ∗
    memRegion ((s0.sp - 816#64) + 248#64) 48 ∗
    (stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 8 ∗
      ((s0.sp - 808#64) ↦₆₄ w_sp8) ∗ memRegion (s0.sp - 800#64) 224 ∗
      memRegion (s0.sp - 520#64) 424 ∗ v1StateJumpTablesAt b ∗
      optProtoInnerStateCapAt A x.msgPtr rest.length m.innerState ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest ∗
      (x.ptr ↦ₛ x.bs.take (x.bs.length - rest.length)) ∗ A.pool ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [restPtr]; ac_rfl)) ?_
  refine SepWP.mono (v1State_tag1_setup_1472 (A := A) (restLen := rest.length) hfsp_align hpc hrun hsp) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩ hinv_c
  rw [hfsp240] at hP1 hx1_1
  rw [hsp] at hsp1; rw [hx19] at hx2_1 hx19_1; rw [hx20] at hx20_1
  rw [hx22] at hx22_1; rw [hx23] at hx23_1; rw [hx24] at hx24_1 hx27_1; rw [hx25] at hx25_1
  rw [hx26] at hx26_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1
  have hx0_1' : (s1.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 iwt.toNat := by
    rw [hx0_1, hx0]
  apply SepWPp.weaken_pre hP1
  refine SepWPp.call_frame_inImage (hinv := hinv_c)
    (x := ⟨iwt, s0.sp - 576#64, default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1496#64) hKuCall
    hpc1 hrun1
    (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    (by dsimp only [chunkedKeysUnsampledMergeSpec]; simp only [hx0_1', hx1_1, hx2_1, hsp1]; rfl)
    (⟨rfl, rfl, rfl, hrest_lt⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        s0.sp - 576#64 = s0.sp - 576#64 ∧ x.bufRef = x.bufRef ∧ rest.length < 2 ^ 63)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedKeysUnsampledMergeSpec] at hpan; exact allowPanic_frame' (htr1.trans htr) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  have hm_field : (V1State.mergeField m (BitVec.ofNat 32 1) (codecWireTypeToProto iwt) rest 99).toOption =
      (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto iwt) default rest 99).toOption.map
        (fun (v', rest') => ({ m with innerState := some (.keysUnsampled v') }, rest')) := by
    rw [v1State_mergeField_tag1]
    rcases h : m.innerState with _ | st
    · rfl
    · cases st with
      | keysUnsampled ku => exact absurd h (hm_not ku)
      | _ => rfl
  cases hku_res : (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto iwt) default rest 99).toOption with
  | none =>
    rw [hku_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2680#64)
    conv =>
      arg 4
      simp only [chunkedKeysUnsampledMergeSpec, hku_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro ku'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (chunkedKeysUnsampledPBAt_entails_err_dealloc A (s0.sp - 576#64) ku') (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState)
      (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
    rw [v1StateBelow_allocHook (s0.sp - 816#64), ← hfsp240]
    let Frame_err : SepProp :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
        v1StateBelowRest (s0.sp - 816#64) allocHookStack ∗
        memRegion (s0.sp - 816#64) 8 ∗ ((s0.sp - 808#64) ↦₆₄ w_sp8) ∗
        memRegion (s0.sp - 800#64) 224 ∗ memRegion (s0.sp - 520#64) 424 ∗
        v1StateJumpTablesAt b ∗
        (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
        (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      words7At ((s0.sp - 816#64) + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗
        ((if ConditionHolds .CC (subsPState64 (w0 + 2#64) 2#64) then emp
          else vecCapPtrDealloc A w0 w1 ∗ vecCapPtrDealloc A w3 w4) ∗
          A.pool ∗ stackAt (s0.sp - 816#64) allocHookStack ∗ Frame_err))
      (Entails.of_eq (by dsimp only [Frame_err]; ac_rfl)) ?_
    refine SepWP.seq (v1State_tag1_load_err_1496 hfsp_align hpcm hrunm hspm hsm0) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2⟩
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl :
      words7At ((s0.sp - 816#64) + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗
        ((if ConditionHolds .CC (subsPState64 (w0 + 2#64) 2#64) then emp
          else vecCapPtrDealloc A w0 w1 ∗ vecCapPtrDealloc A w3 w4) ∗
          A.pool ∗ stackAt (s0.sp - 816#64) allocHookStack ∗ Frame_err) =
      (if ConditionHolds .CC (subsPState64 (w0 + 2#64) 2#64) then emp
       else vecCapPtrDealloc A w0 w1 ∗ vecCapPtrDealloc A w3 w4) ∗
        A.pool ∗ stackAt (s0.sp - 816#64) allocHookStack ∗
        (words7At ((s0.sp - 816#64) + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗ Frame_err)))) ?_
    refine SepWP.seq (v1State_tag1_err_1512 hDealloc hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx22_2 hx23_2 hx24_2 hx25_2) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx21_3⟩
    apply SepWP.weaken_pre hP3
    rw [hfsp240]; dsimp only [Frame_err]
    apply SepWP.fold (v1StateBelow_allocHook_entails (s0.sp - 816#64)) (by sep_focus)
    apply SepWP.fold (memRegion_fold_tag1_temp s0.sp w_sp8 w0 w1 w2 w3 w4 w5 w6) (by sep_focus)
    refine SepWP.done hpc3 hrun3 ?_
    refine v1State_tail_2680 hpc3 hrun3 ?_
    intro s4 hpc4 hrun4 hsp4 htr4 _ _ hx21_4 _ _ _ _ _ _ _ _ _
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFrame A b s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFrame]; ac_rfl))
    exact hcont.onErr hm_field s4 (sm.readReg64 (Reg.gpr 0#5)) n_err hpc4 hrun4
      (hsp4.trans (hsp3.trans (hsp2.trans hspm)))
      (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr)))))
      (hx21_4.trans (hx21_3.trans hx21_2)) hsm0 hn_err
  | some p =>
    rcases p with ⟨ku', rest'⟩
    rw [hku_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hku_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.keysUnsampled ku')) := by
      have h56 := optInnerStatePolyBound_lt_2_56 hpoly
      unfold OptInnerStatePolyBound InnerStatePolyBound; omega
    refine SepWPp.of_sepWP_img (mid := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2680#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedKeysUnsampledMergeSpec, hku_res, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState) (by sep_focus)
    have hku_words : chunkedKeysUnsampledPBCapAt A (s0.sp - 576#64) rest'.length ku' ⊢
        ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
          words7At (s0.sp - 576#64) w0 w1 w2 w3 w4 w5 w6 ∗
          optUnchunked2CapHeap A rest'.length (ku'.uc.map fun u => (u.epoch, u.auth)) w0 w1 w2 w3 w4 w5 w6 := by
      dsimp only [chunkedKeysUnsampledPBCapAt]
      rw [optKeysUnsampledPBCapAt_eq_optUnchunked2]
      exact optUnchunked2CapAt_extract_words A (s0.sp - 576#64) rest'.length (ku'.uc.map fun u => (u.epoch, u.auth))
    apply SepWP.fold hku_words (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6
    rw [v1StateBelow_dropStack96 (s0.sp - 816#64), ← hfsp240, ← hfsp8]
    dsimp only [v1StateJumpTablesAt]
    let Frame_ok : SepProp :=
      optUnchunked2CapHeap A rest'.length (ku'.uc.map fun u => (u.epoch, u.auth)) w0 w1 w2 w3 w4 w5 w6 ∗
        v1StateBelowRest (s0.sp - 816#64) dropStack96 ∗
        memRegion (s0.sp - 816#64) 8 ∗ memRegion (s0.sp - 800#64) 224 ∗
        memRegion (s0.sp - 520#64) 424 ∗ v1StateMergeJumpTableExpanded b ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
        v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      words7At ((s0.sp - 816#64) + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗
        (optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗
          optProtoInnerStateJumpTableAt b ∗ stackAt (s0.sp - 816#64) dropStack96 ∗
          (((s0.sp - 816#64) + 8#64) ↦₆₄ w_sp8) ∗ Frame_ok))
      (Entails.of_eq (by dsimp only [Frame_ok]; ac_rfl)) ?_
    refine SepWP.seq (v1State_tag1_load_ok_1496 hfsp_align hpcm hrunm hspm hsm0) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl :
      words7At ((s0.sp - 816#64) + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗
        (optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗
          optProtoInnerStateJumpTableAt b ∗ stackAt (s0.sp - 816#64) dropStack96 ∗
          (((s0.sp - 816#64) + 8#64) ↦₆₄ w_sp8) ∗ Frame_ok) =
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗
        optProtoInnerStateJumpTableAt b ∗ stackAt (s0.sp - 816#64) dropStack96 ∗
        words7At ((s0.sp - 816#64) + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗
        (((s0.sp - 816#64) + 8#64) ↦₆₄ w_sp8) ∗ Frame_ok))) ?_
    refine SepWP.seq (v1State_tag1_ok_copy_2632 hDropInner hfsp_align hb_align hpc2 hrun2
      (hsp2.trans hspm) (hx20_2.trans hx20_m) hx22_2 hx23_2 hx24_2 hx25_2) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx19_3, hx20_3, hx21_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
    apply SepWP.weaken_pre hP3
    rw [hfsp240, hfsp8]; dsimp only [Frame_ok]
    apply SepWP.fold (v1StateBelow_dropStack96_entails (s0.sp - 816#64)) (by sep_focus)
    apply SepWP.fold (memRegion_fold_tag1_temp s0.sp w2 w0 w1 w2 w3 w4 w5 w6) (by sep_focus)
    apply SepWP.fold (tag1_reconstruct_innerState A x.msgPtr rest'.length ku' w0 w1 w2 w3 w4 w5 w6) (by sep_focus)
    refine SepWP.done hpc3 hrun3 (fun hinv3 => ?_)
    refine v1State_tail_2680 hpc3 hrun3 ?_
    intro s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hinv4
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.keysUnsampled ku') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPre, v1StateJumpTablesAt]; ac_rfl))
    have hsp4' : s4.sp = s0.sp - 816#64 := hsp4.trans (hsp3.trans (hsp2.trans hspm))
    exact hcont.onOk { m with innerState := some (.keysUnsampled ku') } rest' s4 hm_field hpoly' hrest'_le
      hpc4 hrun4 hsp4'
      (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr)))))
      (hx21_4.trans (hx21_3.trans hx21_2))
      ⟨hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_m)),
       hx20_4.trans (hx20_3.trans (hx20_2.trans hx20_m)),
       hx22_4, hx23_4,
       hx24_4.trans (hx27_3.trans (hx27_2.trans hx27_m)),
       by rw [hx25_4, hsp3.trans (hsp2.trans hspm), hfsp240],
       hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_m)),
       hx27_4,
       hx28_4.trans (hx28_3.trans (hx28_2.trans hx28_m)),
       hx29_4.trans (hx29_3.trans (hx29_2.trans hfp_m))⟩
      (hinv4 _ hinv3)

theorem discrFull_other_tag1 {bsLen : Nat} {is : V1State.InnerState} {d : BitVec 64}
    (hne : ∀ v, is ≠ .keysUnsampled v) (hd : InnerStateDiscrFull bsLen (some is) d) :
    (d != 0x8000000000000000#64) = true := by
  cases is with
  | keysUnsampled v => exact absurd rfl (hne v)
  | ct1Sampled s =>
    rcases s with ⟨_ | u, _, _⟩
    · change d = noneCap at hd; subst hd; decide
    · rw [bne_iff_ne]; intro heq; subst heq; exact absurd hd.1 (by decide)
  | _ => subst hd; decide

private theorem v1State_tag1_branch_1472 {img : Obj.Image} {b : BitVec 64}
    {H : String → Option (State → State)}
    {s0 s : State} {x : V1StateMergeGhost} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {P : SepProp} {post panic : State → SepProp → Prop}
    (hm_not : ∀ ku, m.innerState ≠ some (.keysUnsampled ku))
    (hentry : V1StateTagEntryHyp img b H s0 x m rest iwt limit s)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 300#64)
    (hcont : ∀ s' : State,
      V1StateTagEntryHyp img b H s0 x m rest iwt limit s' →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1472#64 →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s' P post panic) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s P post panic := by
  obtain ⟨hsp_align, hb_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  v1StateMerge_fetches b H 300 16
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_img (mid := entry + 1472#64) hinv ?_
  cases hm_is : m.innerState with
  | none =>
    have hx9_n : InnerStateDiscrFull rest.length none (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = true := (discrFull_none_add2 hx9_n).1
    wp_steps; wp_reach; intro hinv'
    exact hcont _
      ⟨hsp_align, hb_align, hrest_le, hrest_lt, hrest_suf, hpoly,
        by simp only [arm64_norm, hrun], by simp only [arm64_norm, hsp],
        by simp only [arm64_norm, htr], by simp only [arm64_norm]; exact hx0,
        by simp only [arm64_norm]; exact hx9,
        ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
         by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx23],
         by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
         by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
         by simp only [arm64_norm, hx28], by simp only [arm64_norm, hx29]⟩, hinv'⟩
      (by simp only [arm64_norm])
  | some is =>
    have hne : ∀ ku, is ≠ .keysUnsampled ku := fun ku h => hm_not ku (by rw [hm_is, h])
    have hx9_s : InnerStateDiscrFull rest.length (some is) (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := (discrFull_some_add2 hx9_s).1
    have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000000#64) = true :=
      discrFull_other_tag1 hne hx9_s
    wp_steps; wp_reach; intro hinv'
    exact hcont _
      ⟨hsp_align, hb_align, hrest_le, hrest_lt, hrest_suf, hpoly,
        by simp only [arm64_norm, hrun], by simp only [arm64_norm, hsp],
        by simp only [arm64_norm, htr], by simp only [arm64_norm]; exact hx0,
        by simp only [arm64_norm]; exact hx9,
        ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
         by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx23],
         by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
         by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
         by simp only [arm64_norm, hx28], by simp only [arm64_norm, hx29]⟩, hinv'⟩
      (by simp only [arm64_norm])

theorem v1State_tag1_step {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hKuCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x206c#64)
      ((chunkedKeysUnsampledMergeSpec A).inImage img))
    (hDropInner : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffd8ec#64)
      (dropOptProtoInnerStateSpec A b))
    (hDealloc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x493f0))
      (rustDeallocSpec A))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hentry : V1StateTagEntryHyp img b H s0 x m rest iwt limit s)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 300#64)
    (hcont : V1StateTagCont img b A H s0 x R 1 m rest iwt limit) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  by_cases hex : ∃ ku, m.innerState = some (.keysUnsampled ku)
  · rcases hex with ⟨ku, hm_is⟩
    exact v1State_tag1_inplace hKuCall hm_is hentry hpc hcont
  · have hm_not : ∀ ku, m.innerState ≠ some (.keysUnsampled ku) := fun ku h => hex ⟨ku, h⟩
    refine v1State_tag1_branch_1472 hm_not hentry hpc fun s' hentry' hpc' => ?_
    exact v1State_tag1_at_1472 hKuCall hDropInner hDealloc hm_not hentry' hpc' hcont

section Placed

open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

attribute [local irreducible] v1StateMergeJumpTablePlacedExpanded optProtoInnerStateJumpTablePlacedAt

/-- Bundled entry hypotheses for any tag arm `1..11` after `BR X10` (`+296`) under `[LibsignalPlacement]`. -/
structure V1StateTagEntryHypPlaced [LibsignalPlacement]
    (H : String → Option (State → State)) (s0 : State) (x : V1StateMergeGhost)
    (m : V1State) (rest : List (BitVec 8)) (iwt : WireType) (limit : Nat) (s : State) : Prop where
  hsp_align : (s0.sp &&& 15#64 == 0#64) = true
  hrest_le : rest.length ≤ x.bs.length
  hrest_lt : rest.length < 2 ^ 63
  hrest_suf : IsDropSuffix x.bs rest
  hpoly : OptInnerStatePolyBound rest.length m.innerState
  hrun : s.status = .Running
  hsp : s.sp = s0.sp - 816#64
  htr : s.v1TraceEq s0
  hx0 : (s.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 iwt.toNat
  hx9 : InnerStateDiscrFull rest.length m.innerState (s.readReg64 (Reg.gpr 9#5))
  hregs : V1StateLoopRegsPlaced s0 x limit s
  hinv : LibsignalCodeRoLoaded lsmpl s.mem

/-- Bundled continuation at `entry + 2700#64` (`0x4f274`) for tag `k` (`1..11`) under `[LibsignalPlacement]`. -/
structure V1StateTagContPlaced [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) (s0 : State) (x : V1StateMergeGhost) (R : SepProp)
    (k : Nat) (m : V1State) (rest : List (BitVec 8)) (iwt : WireType) (limit : Nat) : Prop where
  onErr :
    (V1State.mergeField m (BitVec.ofNat 32 k) (codecWireTypeToProto iwt) rest 99).toOption = none →
    ∀ (s' : State) (err : BitVec 64) (n_err : Nat),
      s'.pc = (blkPl_298).base + 2700#64 →
      s'.status = .Running → s'.sp = s0.sp - 816#64 → s'.v1TraceEq s0 →
      s'.readReg64 (Reg.gpr 21#5) = err → err ≠ 0#64 → n_err ≤ 3 →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s'
        (decodeErrorAtStackLen A err n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
          memRegion (s0.sp - 816#64) 720 ∗
          v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
        (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0)
  onOk :
    ∀ (m' : V1State) (rest' : List (BitVec 8)) (s' : State),
      (V1State.mergeField m (BitVec.ofNat 32 k) (codecWireTypeToProto iwt) rest 99).toOption = some (m', rest') →
      OptInnerStatePolyBound rest'.length m'.innerState →
      rest'.length ≤ rest.length →
      s'.pc = (blkPl_298).base + 2700#64 →
      s'.status = .Running → s'.sp = s0.sp - 816#64 → s'.v1TraceEq s0 →
      s'.readReg64 (Reg.gpr 21#5) = 0#64 →
      V1StateLoopRegsPlaced s0 x limit s' →
      LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s'
        (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m' x.bs rest')
        (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0)

theorem v1State_tail_2692_placed [LibsignalPlacement] {H : String → Option (State → State)}
    {s0 s : State} {P : SepProp} {post panic : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_298).base + 2692#64)
    (hrun : s.status = .Running)
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_298).base + 2700#64 →
      s'.status = .Running → s'.sp = s.sp → s'.v1TraceEq s →
      s'.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) →
      s'.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) →
      s'.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) →
      s'.readReg64 (Reg.gpr 22#5) = 0x8000000000000000#64 →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) →
      s'.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) →
      s'.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) →
      s'.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) →
      s'.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) →
      s'.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5) →
      (∀ mpl, LibsignalCodeRoLoaded mpl s.mem → LibsignalCodeRoLoaded mpl s'.mem) →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s' P post panic) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s P post panic := by
  apply SepWPp.of_sepWP (mid := (blkPl_298).base + 2700#64)
  wp_steps; wp_reach
  exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (fun _ hinv => by simpa only [arm64_norm] using hinv)

theorem v1State_tail_2680_placed [LibsignalPlacement] {H : String → Option (State → State)}
    {s0 s : State} {P : SepProp} {post panic : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_298).base + 2680#64)
    (hrun : s.status = .Running)
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_298).base + 2700#64 →
      s'.status = .Running → s'.sp = s.sp → s'.v1TraceEq s →
      s'.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) →
      s'.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) →
      s'.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) →
      s'.readReg64 (Reg.gpr 22#5) = 0x8000000000000000#64 →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 27#5) →
      s'.readReg64 (Reg.gpr 25#5) = s.sp + 240#64 →
      s'.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) →
      s'.readReg64 (Reg.gpr 27#5) = 0xfffffffffffffffe#64 →
      s'.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) →
      s'.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5) →
      (∀ mpl, LibsignalCodeRoLoaded mpl s.mem → LibsignalCodeRoLoaded mpl s'.mem) →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s' P post panic) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s P post panic := by
  apply SepWPp.of_sepWP (mid := (blkPl_298).base + 2700#64)
  wp_steps; wp_reach
  exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (fun _ hinv => by simpa only [arm64_norm] using hinv)

theorem v1State_tag1_inplace_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hKuCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 305)
      (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A)))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {ku : V1State.Chunked.KeysUnsampled}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_is : m.innerState = some (.keysUnsampled ku))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 300#64)
    (hcont : V1StateTagContPlaced A H s0 x R 1 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  obtain ⟨honErr, honOk⟩ := hcont
  rw [hm_is] at hx9
  change s.readReg64 (Reg.gpr 9#5) = 0x8000000000000000#64 at hx9
  have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := by rw [hx9]; decide
  have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000000#64) = false := by rw [hx9]; decide
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 305) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, hm_is, optProtoInnerStateCapAt, protoInnerStateCapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  simp only [sepConj_assoc]
  wp_steps; wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := ⟨iwt, x.msgPtr + 8#64, ku, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_298).base + 328#64) hKuCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [chunkedKeysUnsampledMergeSpec]; simp only [arm64_norm, hsp, hx0, hx20, hx19]; rfl)
    (⟨rfl, rfl, rfl, hrest_lt⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        x.msgPtr + 8#64 = x.msgPtr + 8#64 ∧ x.bufRef = x.bufRef ∧ rest.length < 2 ^ 63)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedKeysUnsampledMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hm_field := v1State_mergeField_tag1 m iwt rest 99
  rw [hm_is] at hm_field; dsimp only at hm_field
  cases hku_res : (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto iwt) ku rest 99).toOption with
  | none =>
    rw [hku_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 2700#64)
    conv =>
      arg 4
      simp only [chunkedKeysUnsampledMergeSpec, hku_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro ku'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hfold_is : (x.msgPtr ↦₆₄ 0x8000000000000000#64) ∗
        chunkedKeysUnsampledPBAt A (x.msgPtr + 8#64) ku' ∗ memRegion (x.msgPtr + 64#64) 160 ⊢
        ∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is' := by
      rw [chunkedKeysUnsampledPBAt_eq_proto]
      exact optProtoInnerStateAt_entails_exists A x.msgPtr (some (.keysUnsampled ku'))
    apply SepWP.fold hfold_is (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFramePlaced]; ac_rfl))
    exact honErr hm_field _ (sm.readReg64 (Reg.gpr 0#5)) n_err
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm0 hn_err
  | some p =>
    rcases p with ⟨ku', rest'⟩
    rw [hku_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hku_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.keysUnsampled ku')) := by
      have h56 := optInnerStatePolyBound_lt_2_56 hpoly
      unfold OptInnerStatePolyBound InnerStatePolyBound; omega
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedKeysUnsampledMergeSpec, hku_res,
        sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.keysUnsampled ku') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, optProtoInnerStateCapAt, protoInnerStateCapAt]; ac_rfl))
    exact honOk { m with innerState := some (.keysUnsampled ku') } rest' _ hm_field hpoly' hrest'_le
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hsm0])
      ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m],
       by simp only [arm64_norm, hx22_m], by simp only [arm64_norm, hx23_m],
       by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hfp_m]⟩ hinv_n

private theorem v1State_tag1_dealloc_x24_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    {s : State} {fsp w0 w1 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1524#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = w0) (hx25 : s.readReg64 (Reg.gpr 25#5) = w1) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1544#64) s
      (vecCapPtrDealloc A w0 w1 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5)) := by
  simp only [rustDeallocSpec] at hDealloc
  dsimp only [vecCapPtrDealloc]
  by_cases hw0 : (w0 == 0#64) = true <;>
    simp only [hw0, ↓reduceIte, Bool.false_eq_true, sepConj_emp, emp_sepConj]
  · have hbr : (s.readReg64 (Reg.gpr 24#5) == 0#64) = true := by rw [hx24]; exact hw0
    wp_steps; wp_done
  · have hbr : (s.readReg64 (Reg.gpr 24#5) == 0#64) = false := by
      rw [hx24]; exact Bool.eq_false_iff.mpr hw0
    wp_steps; wp_apply
    exact align_pre (by rw [hsp]) (by wp_done)

private theorem v1State_tag1_dealloc_x22_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    {s : State} {fsp w3 w4 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1544#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = w3) (hx23 : s.readReg64 (Reg.gpr 23#5) = w4) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2680#64) s
      (vecCapPtrDealloc A w3 w4 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [rustDeallocSpec] at hDealloc
  dsimp only [vecCapPtrDealloc]
  by_cases hw3 : (w3 == 0#64) = true <;>
    simp only [hw3, ↓reduceIte, Bool.false_eq_true, sepConj_emp, emp_sepConj]
  · have hbr : (s.readReg64 (Reg.gpr 22#5) == 0#64) = true := by rw [hx22]; exact hw3
    wp_steps; wp_done
  · have hbr : (s.readReg64 (Reg.gpr 22#5) == 0#64) = false := by
      rw [hx22]; exact Bool.eq_false_iff.mpr hw3
    wp_steps; wp_apply; wp_steps
    exact align_pre (by rw [hsp]) (by wp_done)

private theorem v1State_tag1_ok_copy_2632_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (dropOptProtoInnerStatePlacedSpec A))
    {s : State} {fsp mPtr w_sp8 w0 w1 w2 w3 w4 w5 w6 : BitVec 64}
    {is : Option V1State.InnerState} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2632#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = w3) (hx23 : s.readReg64 (Reg.gpr 23#5) = w4)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = w0) (hx25 : s.readReg64 (Reg.gpr 25#5) = w1) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2680#64) s
      (optProtoInnerStateAt A mPtr is ∗ A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗
        stackAt fsp dropStack96 ∗ words7At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗
        ((fsp + 8#64) ↦₆₄ w_sp8) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words7At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗ ((fsp + 8#64) ↦₆₄ w2) ∗
          (mPtr ↦₆₄ 0x8000000000000000#64) ∗ words7At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 ∗
          memRegion (mPtr + 64#64) 160 ∗ A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗
          stackAt fsp dropStack96 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  simp only [dropOptProtoInnerStatePlacedSpec] at hDropInner
  dsimp only [words7At]
  wp_steps; wp_apply
  dsimp only [optProtoInnerStateSize]
  rw [memRegion_224_split_tag1_ok mPtr]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro vd
  apply SepWP.exists_elim; intro v6
  apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4
  apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v2
  apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0
  dsimp only [words7At]
  wp_steps; wp_done

private theorem v1State_tag1_err_1512_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    {s : State} {fsp w0 w1 w3 w4 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1512#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = w3) (hx23 : s.readReg64 (Reg.gpr 23#5) = w4)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = w0) (hx25 : s.readReg64 (Reg.gpr 25#5) = w1) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2680#64) s
      ((if ConditionHolds .CC (subsPState64 (w0 + 2#64) 2#64) then emp
        else vecCapPtrDealloc A w0 w1 ∗ vecCapPtrDealloc A w3 w4) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  by_cases hcc : ConditionHolds .CC (subsPState64 (w0 + 2#64) 2#64) = true <;>
    simp only [hcc, ↓reduceIte, Bool.false_eq_true, sepConj_emp, emp_sepConj]
  · have hbr : ConditionHolds .CC (subsPState64 (s.readReg64 (Reg.gpr 24#5) + 2#64) 2#64) = true := by
      rw [hx24]; exact hcc
    wp_steps; wp_done
  · have hstep1 : SepWP ((blkPC_298).rebase (blkPl_298).base H)
        ((blkPl_298).base + 1524#64) s
        ((vecCapPtrDealloc A w0 w1 ∗ vecCapPtrDealloc A w3 w4) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun s1 P1 =>
          (P1 ⊢ vecCapPtrDealloc A w0 w1 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ (vecCapPtrDealloc A w3 w4 ∗ Frame)) ∧
          s1.sp = s.sp ∧ s1.v1TraceEq s ∧
          s1.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
          s1.readReg64 (Reg.gpr 22#5) = w3 ∧ s1.readReg64 (Reg.gpr 23#5) = w4 ∧
          s1.readReg64 (Reg.gpr 24#5) = w0 ∧ s1.readReg64 (Reg.gpr 25#5) = w1) := by
      have hbr : ConditionHolds .CC (subsPState64 (s.readReg64 (Reg.gpr 24#5) + 2#64) 2#64) = false := by
        rw [hx24]; exact Bool.eq_false_iff.mpr hcc
      wp_steps; wp_done
    refine SepWP.seq hstep1 ?_
    rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1⟩
    refine SepWP.weaken_pre hP1 ?_
    refine SepWP.seq (v1State_tag1_dealloc_x24_placed hDealloc hsp_align hpc1 hrun1 (hsp1.trans hsp) hx24_1 hx25_1) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx21_2, hx22_2, hx23_2⟩
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl :
      A.pool ∗ stackAt fsp allocHookStack ∗ (vecCapPtrDealloc A w3 w4 ∗ Frame) =
      vecCapPtrDealloc A w3 w4 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame))) ?_
    refine SepWP.mono (v1State_tag1_dealloc_x22_placed hDealloc hsp_align hpc2 hrun2 (hsp2.trans (hsp1.trans hsp))
      (hx22_2.trans hx22_1) (hx23_2.trans hx23_1)) ?_
    rintro s3 P3 _ _ ⟨hP3, hsp3, htr3, hx21_3⟩
    exact ⟨hP3, hsp3.trans (hsp2.trans hsp1), htr3.trans (htr2.trans htr1), hx21_3.trans (hx21_2.trans hx21_1)⟩

private theorem v1State_tag1_load_ok_1496_placed [LibsignalPlacement] {H : String → Option (State → State)}
    {s : State} {fsp w0 w1 w2 w3 w4 w5 w6 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1496#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2632#64) s
      (words7At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words7At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        sm.readReg64 (Reg.gpr 21#5) = 0#64 ∧
        sm.readReg64 (Reg.gpr 22#5) = w3 ∧ sm.readReg64 (Reg.gpr 23#5) = w4 ∧
        sm.readReg64 (Reg.gpr 24#5) = w0 ∧ sm.readReg64 (Reg.gpr 25#5) = w1 ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  dsimp only [words7At]
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = true := by rw [hx0]; rfl
  wp_steps; wp_done

private theorem v1State_tag1_load_err_1496_placed [LibsignalPlacement] {H : String → Option (State → State)}
    {s : State} {fsp w0 w1 w2 w3 w4 w5 w6 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1496#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) ≠ 0#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1512#64) s
      (words7At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words7At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 0#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = w3 ∧ sm.readReg64 (Reg.gpr 23#5) = w4 ∧
        sm.readReg64 (Reg.gpr 24#5) = w0 ∧ sm.readReg64 (Reg.gpr 25#5) = w1) := by
  dsimp only [words7At]
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0
  wp_steps; wp_done

private theorem v1State_tag1_setup_1472_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {s : State} {fsp w_sp240 : BitVec 64} {restLen : Nat} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1472#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 305) s
      (((fsp + 240#64) ↦₆₄ w_sp240) ∗ memRegion (fsp + 248#64) 48 ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢ chunkedKeysUnsampledPBCapAt A (fsp + 240#64) restLen default ∗ Frame) ∧
        s1.sp = s.sp ∧ s1.v1TraceEq s ∧
        s1.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) ∧
        s1.readReg64 (Reg.gpr 1#5) = fsp + 240#64 ∧
        s1.readReg64 (Reg.gpr 2#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 Reg.lr = (blkPl_298).base + 1496#64 ∧
        s1.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        s1.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        s1.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        s1.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s1.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s1.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        s1.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s1.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        s1.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hdef_ku : ((fsp + 240#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ memRegion (fsp + 248#64) 48 ⊢
      chunkedKeysUnsampledPBCapAt A (fsp + 240#64) restLen default := by
    dsimp only [chunkedKeysUnsampledPBCapAt, default, Inhabited.default, optKeysUnsampledPBCapAt, noneCap2]
    have h8 : (fsp + 240#64) + 8#64 = fsp + 248#64 := by bv_lin
    rw [h8]; exact Entails.refl _
  wp_steps
  apply SepWP.fold hdef_ku (by sep_focus)
  wp_done

theorem v1State_tag1_at_1472_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hKuCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 305)
      (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A)))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (dropOptProtoInnerStatePlacedSpec A))
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_not : ∀ ku, m.innerState ≠ some (.keysUnsampled ku))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 1472#64)
    (hcont : V1StateTagContPlaced A H s0 x R 1 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, _hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfsp_align : ((s0.sp - 816#64) &&& 15#64 == 0#64) = true := by
    simpa only [arm64_norm] using hsp_align
  have hfsp240 : (s0.sp - 816#64) + 240#64 = s0.sp - 576#64 := by bv_lin
  have hfsp248 : (s0.sp - 816#64) + 248#64 = s0.sp - 568#64 := by bv_lin
  have hfsp8 : (s0.sp - 816#64) + 8#64 = s0.sp - 808#64 := by bv_lin
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 305) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, memRegion_split_tag1_temp s0.sp, sliceCursorAfter_eq_split hrest_le hrest_suf]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp240
  apply SepWP.exists_elim; intro w_sp8
  rw [← hfsp240, ← hfsp248]
  refine SepWP.weaken_pre (P' := (((s0.sp - 816#64) + 240#64) ↦₆₄ w_sp240) ∗
    memRegion ((s0.sp - 816#64) + 248#64) 48 ∗
    (stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 8 ∗
      ((s0.sp - 808#64) ↦₆₄ w_sp8) ∗ memRegion (s0.sp - 800#64) 224 ∗
      memRegion (s0.sp - 520#64) 424 ∗ v1StateJumpTablesPlacedAt ∗
      optProtoInnerStateCapAt A x.msgPtr rest.length m.innerState ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest ∗
      (x.ptr ↦ₛ x.bs.take (x.bs.length - rest.length)) ∗ A.pool ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [restPtr]; ac_rfl)) ?_
  refine SepWP.mono (v1State_tag1_setup_1472_placed (A := A) (restLen := rest.length) hfsp_align hpc hrun hsp) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩ hinv_c
  rw [hfsp240] at hP1 hx1_1
  rw [hsp] at hsp1; rw [hx19] at hx2_1 hx19_1; rw [hx20] at hx20_1
  rw [hx22] at hx22_1; rw [hx23] at hx23_1; rw [hx24] at hx24_1 hx27_1; rw [hx25] at hx25_1
  rw [hx26] at hx26_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1
  have hx0_1' : (s1.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 iwt.toNat := by
    rw [hx0_1, hx0]
  apply SepWPp.weaken_pre hP1
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := ⟨iwt, s0.sp - 576#64, default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_298).base + 1496#64) hKuCall
    hpc1 hrun1
    (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    (by dsimp only [chunkedKeysUnsampledMergeSpec]; simp only [hx0_1', hx1_1, hx2_1, hsp1]; rfl)
    (⟨rfl, rfl, rfl, hrest_lt⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        s0.sp - 576#64 = s0.sp - 576#64 ∧ x.bufRef = x.bufRef ∧ rest.length < 2 ^ 63)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedKeysUnsampledMergeSpec] at hpan; exact allowPanic_frame' (htr1.trans htr) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  have hm_field : (V1State.mergeField m (BitVec.ofNat 32 1) (codecWireTypeToProto iwt) rest 99).toOption =
      (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto iwt) default rest 99).toOption.map
        (fun (v', rest') => ({ m with innerState := some (.keysUnsampled v') }, rest')) := by
    rw [v1State_mergeField_tag1]
    rcases h : m.innerState with _ | st
    · rfl
    · cases st with
      | keysUnsampled ku => exact absurd h (hm_not ku)
      | _ => rfl
  cases hku_res : (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto iwt) default rest 99).toOption with
  | none =>
    rw [hku_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 2680#64)
    conv =>
      arg 4
      simp only [chunkedKeysUnsampledMergeSpec, hku_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro ku'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (chunkedKeysUnsampledPBAt_entails_err_dealloc A (s0.sp - 576#64) ku') (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState)
      (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
    rw [v1StateBelow_allocHook (s0.sp - 816#64), ← hfsp240]
    let Frame_err : SepProp :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
        v1StateBelowRest (s0.sp - 816#64) allocHookStack ∗
        memRegion (s0.sp - 816#64) 8 ∗ ((s0.sp - 808#64) ↦₆₄ w_sp8) ∗
        memRegion (s0.sp - 800#64) 224 ∗ memRegion (s0.sp - 520#64) 424 ∗
        v1StateJumpTablesPlacedAt ∗
        (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
        (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      words7At ((s0.sp - 816#64) + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗
        ((if ConditionHolds .CC (subsPState64 (w0 + 2#64) 2#64) then emp
          else vecCapPtrDealloc A w0 w1 ∗ vecCapPtrDealloc A w3 w4) ∗
          A.pool ∗ stackAt (s0.sp - 816#64) allocHookStack ∗ Frame_err))
      (Entails.of_eq (by dsimp only [Frame_err]; ac_rfl)) ?_
    refine SepWP.seq (v1State_tag1_load_err_1496_placed hfsp_align hpcm hrunm hspm hsm0) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2⟩
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl :
      words7At ((s0.sp - 816#64) + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗
        ((if ConditionHolds .CC (subsPState64 (w0 + 2#64) 2#64) then emp
          else vecCapPtrDealloc A w0 w1 ∗ vecCapPtrDealloc A w3 w4) ∗
          A.pool ∗ stackAt (s0.sp - 816#64) allocHookStack ∗ Frame_err) =
      (if ConditionHolds .CC (subsPState64 (w0 + 2#64) 2#64) then emp
       else vecCapPtrDealloc A w0 w1 ∗ vecCapPtrDealloc A w3 w4) ∗
        A.pool ∗ stackAt (s0.sp - 816#64) allocHookStack ∗
        (words7At ((s0.sp - 816#64) + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗ Frame_err)))) ?_
    refine SepWP.seq (v1State_tag1_err_1512_placed hDealloc hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx22_2 hx23_2 hx24_2 hx25_2) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx21_3⟩
    apply SepWP.weaken_pre hP3
    rw [hfsp240]; dsimp only [Frame_err]
    apply SepWP.fold (v1StateBelow_allocHook_entails (s0.sp - 816#64)) (by sep_focus)
    apply SepWP.fold (memRegion_fold_tag1_temp s0.sp w_sp8 w0 w1 w2 w3 w4 w5 w6) (by sep_focus)
    refine SepWP.done hpc3 hrun3 ?_
    refine v1State_tail_2680_placed hpc3 hrun3 ?_
    intro s4 hpc4 hrun4 hsp4 htr4 _ _ hx21_4 _ _ _ _ _ _ _ _ _
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFramePlaced]; ac_rfl))
    exact hcont.onErr hm_field s4 (sm.readReg64 (Reg.gpr 0#5)) n_err hpc4 hrun4
      (hsp4.trans (hsp3.trans (hsp2.trans hspm)))
      (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr)))))
      (hx21_4.trans (hx21_3.trans hx21_2)) hsm0 hn_err
  | some p =>
    rcases p with ⟨ku', rest'⟩
    rw [hku_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hku_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.keysUnsampled ku')) := by
      have h56 := optInnerStatePolyBound_lt_2_56 hpoly
      unfold OptInnerStatePolyBound InnerStatePolyBound; omega
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2680#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedKeysUnsampledMergeSpec, hku_res, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState) (by sep_focus)
    have hku_words : chunkedKeysUnsampledPBCapAt A (s0.sp - 576#64) rest'.length ku' ⊢
        ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
          words7At (s0.sp - 576#64) w0 w1 w2 w3 w4 w5 w6 ∗
          optUnchunked2CapHeap A rest'.length (ku'.uc.map fun u => (u.epoch, u.auth)) w0 w1 w2 w3 w4 w5 w6 := by
      dsimp only [chunkedKeysUnsampledPBCapAt]
      rw [optKeysUnsampledPBCapAt_eq_optUnchunked2]
      exact optUnchunked2CapAt_extract_words A (s0.sp - 576#64) rest'.length (ku'.uc.map fun u => (u.epoch, u.auth))
    apply SepWP.fold hku_words (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6
    rw [v1StateBelow_dropStack96 (s0.sp - 816#64), ← hfsp240, ← hfsp8]
    dsimp only [v1StateJumpTablesPlacedAt]
    let Frame_ok : SepProp :=
      optUnchunked2CapHeap A rest'.length (ku'.uc.map fun u => (u.epoch, u.auth)) w0 w1 w2 w3 w4 w5 w6 ∗
        v1StateBelowRest (s0.sp - 816#64) dropStack96 ∗
        memRegion (s0.sp - 816#64) 8 ∗ memRegion (s0.sp - 800#64) 224 ∗
        memRegion (s0.sp - 520#64) 424 ∗ v1StateMergeJumpTablePlacedExpanded ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
        v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      words7At ((s0.sp - 816#64) + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗
        (optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗
          optProtoInnerStateJumpTablePlacedAt ∗ stackAt (s0.sp - 816#64) dropStack96 ∗
          (((s0.sp - 816#64) + 8#64) ↦₆₄ w_sp8) ∗ Frame_ok))
      (Entails.of_eq (by dsimp only [Frame_ok]; ac_rfl)) ?_
    refine SepWP.seq (v1State_tag1_load_ok_1496_placed hfsp_align hpcm hrunm hspm hsm0) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl :
      words7At ((s0.sp - 816#64) + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗
        (optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗
          optProtoInnerStateJumpTablePlacedAt ∗ stackAt (s0.sp - 816#64) dropStack96 ∗
          (((s0.sp - 816#64) + 8#64) ↦₆₄ w_sp8) ∗ Frame_ok) =
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗
        optProtoInnerStateJumpTablePlacedAt ∗ stackAt (s0.sp - 816#64) dropStack96 ∗
        words7At ((s0.sp - 816#64) + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗
        (((s0.sp - 816#64) + 8#64) ↦₆₄ w_sp8) ∗ Frame_ok))) ?_
    refine SepWP.seq (v1State_tag1_ok_copy_2632_placed hDropInner hfsp_align hpc2 hrun2
      (hsp2.trans hspm) (hx20_2.trans hx20_m) hx22_2 hx23_2 hx24_2 hx25_2) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx19_3, hx20_3, hx21_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
    apply SepWP.weaken_pre hP3
    rw [hfsp240, hfsp8]; dsimp only [Frame_ok]
    apply SepWP.fold (v1StateBelow_dropStack96_entails (s0.sp - 816#64)) (by sep_focus)
    apply SepWP.fold (memRegion_fold_tag1_temp s0.sp w2 w0 w1 w2 w3 w4 w5 w6) (by sep_focus)
    apply SepWP.fold (tag1_reconstruct_innerState A x.msgPtr rest'.length ku' w0 w1 w2 w3 w4 w5 w6) (by sep_focus)
    refine SepWP.done hpc3 hrun3 (fun hinv3 => ?_)
    refine v1State_tail_2680_placed hpc3 hrun3 ?_
    intro s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hinv4
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.keysUnsampled ku') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt]; ac_rfl))
    have hsp4' : s4.sp = s0.sp - 816#64 := hsp4.trans (hsp3.trans (hsp2.trans hspm))
    exact hcont.onOk { m with innerState := some (.keysUnsampled ku') } rest' s4 hm_field hpoly' hrest'_le
      hpc4 hrun4 hsp4'
      (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr)))))
      (hx21_4.trans (hx21_3.trans hx21_2))
      ⟨hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_m)),
       hx20_4.trans (hx20_3.trans (hx20_2.trans hx20_m)),
       hx22_4, hx23_4,
       hx24_4.trans (hx27_3.trans (hx27_2.trans hx27_m)),
       by rw [hx25_4, hsp3.trans (hsp2.trans hspm), hfsp240],
       hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_m)),
       hx27_4,
       hx28_4.trans (hx28_3.trans (hx28_2.trans hx28_m)),
       hx29_4.trans (hx29_3.trans (hx29_2.trans hfp_m))⟩
      (hinv4 _ hinv3)

private theorem v1State_tag1_branch_1472_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s0 s : State} {x : V1StateMergeGhost} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {P : SepProp} {post panic : State → SepProp → Prop}
    (hm_not : ∀ ku, m.innerState ≠ some (.keysUnsampled ku))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 300#64)
    (hcont : ∀ s' : State,
      V1StateTagEntryHypPlaced H s0 x m rest iwt limit s' →
      s'.pc = (blkPl_298).base + 1472#64 →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s' P post panic) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s P post panic := by
  obtain ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 1472#64) hinv ?_
  cases hm_is : m.innerState with
  | none =>
    have hx9_n : InnerStateDiscrFull rest.length none (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = true := (discrFull_none_add2 hx9_n).1
    wp_steps; wp_reach; intro hinv'
    exact hcont _
      ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
        by simp only [arm64_norm, hrun], by simp only [arm64_norm, hsp],
        by simp only [arm64_norm, htr], by simp only [arm64_norm]; exact hx0,
        by simp only [arm64_norm]; exact hx9,
        ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
         by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx23],
         by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
         by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
         by simp only [arm64_norm, hx28], by simp only [arm64_norm, hx29]⟩, hinv'⟩
      (by simp only [arm64_norm])
  | some is =>
    have hne : ∀ ku, is ≠ .keysUnsampled ku := fun ku h => hm_not ku (by rw [hm_is, h])
    have hx9_s : InnerStateDiscrFull rest.length (some is) (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := (discrFull_some_add2 hx9_s).1
    have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000000#64) = true :=
      discrFull_other_tag1 hne hx9_s
    wp_steps; wp_reach; intro hinv'
    exact hcont _
      ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
        by simp only [arm64_norm, hrun], by simp only [arm64_norm, hsp],
        by simp only [arm64_norm, htr], by simp only [arm64_norm]; exact hx0,
        by simp only [arm64_norm]; exact hx9,
        ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
         by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx23],
         by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
         by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
         by simp only [arm64_norm, hx28], by simp only [arm64_norm, hx29]⟩, hinv'⟩
      (by simp only [arm64_norm])

theorem v1State_tag1_step_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hKuCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 305)
      (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A)))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (dropOptProtoInnerStatePlacedSpec A))
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 300#64)
    (hcont : V1StateTagContPlaced A H s0 x R 1 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  by_cases hex : ∃ ku, m.innerState = some (.keysUnsampled ku)
  · rcases hex with ⟨ku, hm_is⟩
    exact v1State_tag1_inplace_placed hKuCall hm_is hentry hpc hcont
  · have hm_not : ∀ ku, m.innerState ≠ some (.keysUnsampled ku) := fun ku h => hex ⟨ku, h⟩
    refine v1State_tag1_branch_1472_placed hm_not hentry hpc fun s' hentry' hpc' => ?_
    exact v1State_tag1_at_1472_placed hKuCall hDropInner hDealloc hm_not hentry' hpc' hcont

end Placed

end CryptoVerification.SpqrV1.Prost.MessageMerge

