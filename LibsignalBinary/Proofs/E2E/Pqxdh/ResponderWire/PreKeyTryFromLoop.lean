/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBase
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFrom
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.Fetch
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
import ProofLib.SepLogic.WPp

@[expose] public section
namespace CryptoVerification.E2E.Pqxdh.ResponderWire
open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
set_option maxRecDepth 200000
set_option maxHeartbeats 800000
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit' bv_sub_sub_lit
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512
abbrev SepWPp := Wire.SepWPp
abbrev SepWP.done := @Wire.SepWP.done
abbrev SepWPp.of_sepWP := @Wire.SepWPp.of_sepWP
abbrev SepWPp.of_sepWP_frozen := @Wire.SepWPp.of_sepWP_frozen
abbrev SepWPp.of_sepWP_end := @Wire.SepWPp.of_sepWP_end
abbrev SepWPp.panic := @Wire.SepWPp.panic
abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
abbrev SepWPp.bind := @Wire.SepWPp.bind
abbrev SepWPp.bind_entails := @Wire.SepWPp.bind_entails
abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
/-! ## Loop Register Invariant and Callee-Saved Area (`sp' + 512..608`) -/
structure PreKeyLoopRegs (sp' : BitVec 64) (x : PreKeyTryFromArgs) (s : State) : Prop where
  sp  : s.sp = sp'
  x29 : s.readReg64 .x29 = sp' + 512#64
  x28 : s.readReg64 .x28 = sp' + 296#64
  x27 : s.readReg64 .x27 = 0x8000000000000002#64
  x26 : s.readReg64 .x26 = sp' + 304#64
  x25 : s.readReg64 .x25 = 1#64
  x23 : s.readReg64 .x23 = sp' + 312#64
  x22 : s.readReg64 .x22 = 0x44#64
  x21 : s.readReg64 .x21 = x.ptr
  x20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length
  x19 : s.readReg64 .x19 = x.sret
theorem PreKeyLoopRegs.of_calleeSaved {sp' : BitVec 64} {x : PreKeyTryFromArgs} {s1 s2 : State}
    (h1 : PreKeyLoopRegs sp' x s1) (hsp : s2.sp = s1.sp) (hcs : CalleeSavedPreserved s1 s2) :
    PreKeyLoopRegs sp' x s2 := by
  rcases hcs with ⟨h19, h20, h21, h22, h23, _, h25, h26, h27, h28, h29, _⟩
  exact ⟨hsp.trans h1.sp, h29.trans h1.x29, h28.trans h1.x28, h27.trans h1.x27,
    h26.trans h1.x26, h25.trans h1.x25, h23.trans h1.x23, h22.trans h1.x22,
    h21.trans h1.x21, h20.trans h1.x20, h19.trans h1.x19⟩
def preKeyCalleeSavedAt (sp' : BitVec 64) (s0 : State) : SepProp :=
  ((sp' + 512#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp' + 520#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp' + 528#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp' + 536#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp' + 544#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp' + 552#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp' + 560#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp' + 568#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp' + 576#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp' + 584#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp' + 592#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp' + 600#64) ↦₆₄ s0.readReg64 .x19)
theorem preKeyCalleeSavedAt_eq_calleeSavedAt (sp' : BitVec 64) (s0 : State) :
    preKeyCalleeSavedAt sp' s0 = calleeSavedAt (sp' + 160#64) s0 := by
  unfold preKeyCalleeSavedAt calleeSavedAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
theorem preKeyCalleeSavedAt_entails_memRegion96 (sp' : BitVec 64) (s0 : State) :
    preKeyCalleeSavedAt sp' s0 ⊢ memRegion (sp' + 512#64) 96 := by
  have h := calleeSavedAt_entails_memRegion96 (sp' + 160#64) s0
  have ha : sp' + 160#64 + 352#64 = sp' + 512#64 := by bv_omega
  rw [ha, ← preKeyCalleeSavedAt_eq_calleeSavedAt] at h
  exact h
theorem memRegion96_split_preKeyCalleeSaved (sp' : BitVec 64) :
    memRegion (sp' + 512#64) 96 ⊢
      ∃∗ w19 : BitVec 64, ∃∗ w20 : BitVec 64, ∃∗ w21 : BitVec 64, ∃∗ w22 : BitVec 64,
      ∃∗ w23 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w25 : BitVec 64, ∃∗ w26 : BitVec 64,
      ∃∗ w27 : BitVec 64, ∃∗ w28 : BitVec 64, ∃∗ w30 : BitVec 64, ∃∗ w29 : BitVec 64,
        ((sp' + 512#64) ↦₆₄ w29) ∗ ((sp' + 520#64) ↦₆₄ w30) ∗ ((sp' + 528#64) ↦₆₄ w28) ∗ ((sp' +
        536#64) ↦₆₄ w27) ∗
        ((sp' + 544#64) ↦₆₄ w26) ∗ ((sp' + 552#64) ↦₆₄ w25) ∗ ((sp' + 560#64) ↦₆₄ w24) ∗ ((sp' +
        568#64) ↦₆₄ w23) ∗
        ((sp' + 576#64) ↦₆₄ w22) ∗ ((sp' + 584#64) ↦₆₄ w21) ∗ ((sp' + 592#64) ↦₆₄ w20) ∗ ((sp' +
        600#64) ↦₆₄ w19) := by
  have h := memRegion96_cells (sp' + 160#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  exact h
theorem stackAt_preKeyTryFrom_split (sp : BitVec 64) :
    stackAt sp preKeyTryFromStack =
      stackAt (sp - 608#64) preKeyTryFromSubStack ∗ memRegion (sp - 608#64) 296 ∗ memRegion (sp -
        608#64 + 296#64) 152 ∗
      memRegion (sp - 608#64 + 448#64) 64 ∗ memRegion (sp - 608#64 + 512#64) 96 := by
  have h1 := stackAt_sub_split sp 608 preKeyTryFromStack (by decide) (by decide)
  have h2 : memRegion (sp - BitVec.ofNat 64 preKeyTryFromStack) (preKeyTryFromStack - 608) =
      stackAt (sp - 608#64) preKeyTryFromSubStack := by
    unfold stackAt
    have ha : sp - BitVec.ofNat 64 preKeyTryFromStack =
        sp - 608#64 - BitVec.ofNat 64 preKeyTryFromSubStack := by
      change sp - 66144#64 = sp - 608#64 - 65536#64
      bv_omega
    rw [ha]; rfl
  have h3 : stackAt sp 608 =
      memRegion (sp - 608#64) 296 ∗ memRegion (sp - 608#64 + 296#64) 152 ∗ memRegion (sp - 608#64 +
        448#64) 64 ∗
      memRegion (sp - 608#64 + 512#64) 96 := by
    unfold stackAt
    rw [show (608 : Nat) = 296 + (152 + (64 + 96)) by decide,
      memRegion_split (sp - 608#64) 296 312 (by decide),
      memRegion_split (sp - 608#64 + 296#64) 152 160 (by decide),
      memRegion_split (sp - 608#64 + 296#64 + 152#64) 64 96 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [h1, h2, h3]
theorem spAligned_sub608 {s : State} (h : s.spAligned = true) :
    ((s.sp - 608#64) &&& 15#64 == 0#64) = true := by
  rw [State.spAligned, beq_iff_eq] at h
  have h15 : (15#64 : BitVec 64).toNat = 2 ^ 4 - 1 := rfl
  have h608 : (608#64 : BitVec 64).toNat = 608 := rfl
  have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
  have hmod : s.sp.toNat % 16 = 0 := by
    have ha := congrArg BitVec.toNat h
    rw [BitVec.toNat_and, h15, h0, Nat.and_two_pow_sub_one_eq_mod] at ha
    exact ha
  rw [beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, h15, h0, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_sub, h608]
  omega
/-! ## Round-Trip and Cursor Helpers for Fields 1..8 -/
def cur0 (x : PreKeyTryFromArgs) : BitVec 64 := x.ptr + 1#64
def cur1 (x : PreKeyTryFromArgs) : BitVec 64 := cur0 x + BitVec.ofNat 64 (psmField1 x).length
def cur2 (x : PreKeyTryFromArgs) : BitVec 64 := cur1 x + BitVec.ofNat 64 (psmField2 x).length
def cur3 (x : PreKeyTryFromArgs) : BitVec 64 := cur2 x + BitVec.ofNat 64 (psmField3 x).length
def cur4 (x : PreKeyTryFromArgs) : BitVec 64 := cur3 x + BitVec.ofNat 64 (psmField4 x).length
def cur5 (x : PreKeyTryFromArgs) : BitVec 64 := cur4 x + BitVec.ofNat 64 (psmField5 x).length
def cur6 (x : PreKeyTryFromArgs) : BitVec 64 := cur5 x + BitVec.ofNat 64 (psmField6 x).length
def cur7 (x : PreKeyTryFromArgs) : BitVec 64 := cur6 x + BitVec.ofNat 64 (psmField7 x).length
def cur8 (x : PreKeyTryFromArgs) : BitVec 64 := cur7 x + BitVec.ofNat 64 (psmField8 x).length
theorem bytes_eq_cons_psmRem0 (x : PreKeyTryFromArgs) : x.bytes = 0x44#8 :: psmRem0 x := by
  have hvb : versionByte 4#8 = 0x44#8 := by decide
  rw [PreKeyTryFromArgs.bytes, hvb, protoBytes_eq_psmRem0]
theorem pointsToBytes_psm_reassemble (x : PreKeyTryFromArgs) :
    (x.ptr ↦₈ 0x44#8) ∗ (cur0 x ↦ₛ psmField1 x) ∗ (cur1 x ↦ₛ psmField2 x) ∗
      (cur2 x ↦ₛ psmField3 x) ∗ (cur3 x ↦ₛ psmField4 x) ∗
    (cur4 x ↦ₛ psmField5 x) ∗ (cur5 x ↦ₛ psmField6 x) ∗ (cur6 x ↦ₛ psmField7 x) ∗
      (cur7 x ↦ₛ psmField8 x) = (x.ptr ↦ₛ x.bytes) := by
  rw [bytes_eq_cons_psmRem0 x, pointsToBytes_cons, psmRem0, pointsToBytes_append, ← cur0, ← cur1,
    psmRem1, pointsToBytes_append, ← cur2, psmRem2, pointsToBytes_append, ← cur3,
    psmRem3, pointsToBytes_append, ← cur4, psmRem4, pointsToBytes_append, ← cur5,
    psmRem5, pointsToBytes_append, ← cur6, psmRem6, pointsToBytes_append, ← cur7,
    psmRem7, psmRem8, List.append_nil]
theorem psmRem7_ne_nil (x : PreKeyTryFromArgs) : psmRem7 x ≠ [] := by
  rw [psmRem7, psmField8_eq]; simp
theorem psmRem6_ne_nil (x : PreKeyTryFromArgs) : psmRem6 x ≠ [] := by
  rw [psmRem6, psmField7_eq]; simp
theorem psmRem5_ne_nil (x : PreKeyTryFromArgs) : psmRem5 x ≠ [] := by
  rw [psmRem5, psmField6_eq]; simp
theorem psmRem4_ne_nil (x : PreKeyTryFromArgs) : psmRem4 x ≠ [] := by
  rw [psmRem4, psmField5_eq]; simp
theorem psmRem3_ne_nil (x : PreKeyTryFromArgs) : psmRem3 x ≠ [] := by
  have h4 := psmRem4_ne_nil x
  unfold psmRem3; intro h; exact h4 (List.append_eq_nil_iff.mp h).2
theorem psmRem2_ne_nil (x : PreKeyTryFromArgs) : psmRem2 x ≠ [] := by
  rw [psmRem2, psmField3_eq]; simp
theorem psmRem1_ne_nil (x : PreKeyTryFromArgs) : psmRem1 x ≠ [] := by
  rw [psmRem1, psmField2_eq]; simp
theorem psmRem0_ne_nil (x : PreKeyTryFromArgs) : psmRem0 x ≠ [] := by
  have h1 := psmRem1_ne_nil x
  unfold psmRem0; intro h; exact h1 (List.append_eq_nil_iff.mp h).2
theorem ofNat64_length_ne_zero {bs : List (BitVec 8)} (hne : bs ≠ []) (hlt : bs.length < 2 ^ 32) :
    BitVec.ofNat 64 bs.length ≠ 0#64 := by
  have hpos : 0 < bs.length := List.length_pos_of_ne_nil hne
  intro h
  have hto := congrArg BitVec.toNat h
  have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
  rw [BitVec.toNat_ofNat, h0, Nat.mod_eq_of_lt (by omega)] at hto
  omega
theorem ofNat64_cons_sub_one (b0 : BitVec 8) (rest : List (BitVec 8)) :
    BitVec.ofNat 64 (b0 :: rest).length - 1#64 = BitVec.ofNat 64 rest.length := by
  simp only [List.length_cons, BitVec.ofNat_add]
  bv_omega
theorem merge_field1_some (x : PreKeyTryFromArgs) (v : BitVec 32) :
    mergeUint32 .varint (encodeVarint (v.zeroExtend 64) ++ psmRem1 x) = some (v, psmRem1 x) :=
  mergeUint32_encode v (psmRem1 x)
theorem merge_field2 (x : PreKeyTryFromArgs) :
    mergeBytes .lengthDelimited ((encodeVarint 33#64 ++ x.bkBytes) ++ psmRem2 x) =
      some (x.bkBytes, psmRem2 x) := by
  rw [List.append_assoc]
  simpa [PreKeyTryFromArgs.bkBytes_length] using
    mergeBytes_encode x.bkBytes (psmRem2 x) (by simp)
theorem merge_field3 (x : PreKeyTryFromArgs) :
    mergeBytes .lengthDelimited ((encodeVarint 33#64 ++ x.ikBytes) ++ psmRem3 x) =
      some (x.ikBytes, psmRem3 x) := by
  rw [List.append_assoc]
  simpa [PreKeyTryFromArgs.ikBytes_length] using
    mergeBytes_encode x.ikBytes (psmRem3 x) (by simp)
theorem merge_field4 (x : PreKeyTryFromArgs) (hlen : x.inner.length < 2 ^ 64) :
    mergeBytes .lengthDelimited
      ((encodeVarint (BitVec.ofNat 64 x.inner.length) ++ x.inner) ++ psmRem4 x) =
      some (x.inner, psmRem4 x) := by
  rw [List.append_assoc]
  exact mergeBytes_encode x.inner (psmRem4 x) hlen
theorem merge_field5 (x : PreKeyTryFromArgs) :
    mergeUint32 .varint (encodeVarint (x.regId.zeroExtend 64) ++ psmRem5 x) =
      some (x.regId, psmRem5 x) :=
  mergeUint32_encode x.regId (psmRem5 x)
theorem merge_field6 (x : PreKeyTryFromArgs) :
    mergeUint32 .varint (encodeVarint (x.spkId.zeroExtend 64) ++ psmRem6 x) =
      some (x.spkId, psmRem6 x) :=
  mergeUint32_encode x.spkId (psmRem6 x)
theorem merge_field7 (x : PreKeyTryFromArgs) :
    mergeUint32 .varint (encodeVarint (x.kpkId.zeroExtend 64) ++ psmRem7 x) =
      some (x.kpkId, psmRem7 x) :=
  mergeUint32_encode x.kpkId (psmRem7 x)
theorem merge_field8 (x : PreKeyTryFromArgs) :
    mergeBytes .lengthDelimited ((encodeVarint 1569#64 ++ x.kyberBytes) ++ psmRem8 x) =
      some (x.kyberBytes, psmRem8 x) := by
  rw [List.append_assoc]
  simpa [PreKeyTryFromArgs.kyberBytes_length] using
    mergeBytes_encode x.kyberBytes (psmRem8 x) (by simp)
/-! ## Prologue (`0x29b30 .. 0x29c00` → `0x29c24`) -/
theorem memRegion152_init_cells (sp' : BitVec 64) :
    memRegion (sp' + 296#64) 152 ⊢
      ∃∗ w440 : BitVec 64, ∃∗ w432 : BitVec 32, ∃∗ w424 : BitVec 32,
      ∃∗ w416 : BitVec 32, ∃∗ w408 : BitVec 32, ∃∗ w384 : BitVec 64, ∃∗ w360 : BitVec 64,
      ∃∗ w336 : BitVec 64, ∃∗ w312 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c0 : BitVec 64,
        ((sp' + 296#64) ↦₆₄ c0) ∗ ((sp' + 304#64) ↦₆₄ c1) ∗ ((sp' + 312#64) ↦₆₄ w312) ∗
        memRegion (sp' + 320#64) 16 ∗
        ((sp' + 336#64) ↦₆₄ w336) ∗ memRegion (sp' + 344#64) 16 ∗ ((sp' + 360#64) ↦₆₄ w360) ∗
        memRegion (sp' + 368#64) 16 ∗
        ((sp' + 384#64) ↦₆₄ w384) ∗ memRegion (sp' + 392#64) 16 ∗ ((sp' + 408#64) ↦₃₂ w408) ∗
        memRegion (sp' + 412#64) 4 ∗
        ((sp' + 416#64) ↦₃₂ w416) ∗ memRegion (sp' + 420#64) 4 ∗ ((sp' + 424#64) ↦₃₂ w424) ∗
        memRegion (sp' + 428#64) 4 ∗
        ((sp' + 432#64) ↦₃₂ w432) ∗ memRegion (sp' + 436#64) 4 ∗ ((sp' + 440#64) ↦₆₄ w440) := by
  have h112 := memRegion112_emptyMsg_cells (sp' + 136#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h112
  rw [show (152 : Nat) = 16 + (112 + (8 + (8 + 8))) by decide,
    memRegion_split (sp' + 296#64) 16 136 (by decide),
    memRegion_split (sp' + 296#64 + 16#64) 112 24 (by decide),
    memRegion_split (sp' + 296#64 + 16#64 + 112#64) 8 16 (by decide),
    memRegion_split (sp' + 296#64 + 16#64 + 112#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans
    (sepConj_mono (memRegion16_split8_8' (sp' + 296#64)) (sepConj_mono h112
        (sepConj_mono (memRegion8_split4_4 (sp' + 424#64))
          (sepConj_mono (memRegion8_split4_4 (sp' + 432#64))
            (by rw [ProofLib.memRegion_eight (sp' + 440#64)]; exact Entails.refl _))))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.refl _
theorem cond_eq_subs1_false {n : Nat} (hge2 : 2 ≤ n) (hlt : n < 2 ^ 32) :
    ConditionHolds .EQ (subsPState64 (BitVec.ofNat 64 n) 1#64) = false := by
  have hgt : 1#64 < BitVec.ofNat 64 n := by
    rw [BitVec.lt_def]
    have h1 : (BitVec.ofNat 64 n).toNat = n := Nat.mod_eq_of_lt (by omega)
    have h2 : (1#64 : BitVec 64).toNat = 1 := rfl
    omega
  unfold ConditionHolds subsPState64 AddWithCarry64
  simp only [↓reduceIte, beq_eq_false_iff_ne]
  have hnot : (~~~(1#64) : BitVec 64) = 18446744073709551614#64 := rfl
  rw [hnot]
  bv_omega
theorem prologue_to_c24_wp {img : Obj.Image} {C : Crypto}
    (ctl : BitVec 64) {abs : String → Option (State → State)} {x : PreKeyTryFromArgs} {s0 : State}
    (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hF : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab) (hx0 : s0.readReg64 .x0 = x.ptr)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length) (hx8 : s0.readReg64 .x8 = x.sret) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 0xf4#64) s0
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion (s0.sp - 608#64 + 296#64) 152 ∗ memRegion (s0.sp - 608#64 +
        512#64) 96)
      (fun s1 P1 =>
        PreKeyLoopRegs (s0.sp - 608#64) x s1 ∧ s1.spAligned = true ∧ img.FrozenLoaded s1 ∧
        s1.symtab = img.symtab ∧
        s1.trace = s0.trace ∧ s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem0 x).length ∧
        (P1 ⊢ (x.ptr ↦₈ 0x44#8) ∗
          sliceCursorAt (s0.sp - 608#64 + 296#64) (cur0 x) (psmRem0 x) ∗ ((s0.sp - 608#64 +
          440#64) ↦₆₄ (s0.sp - 608#64 + 296#64)) ∗
          ((s0.sp - 608#64 + 312#64) ↦₆₄ noneCap) ∗ memRegion (s0.sp - 608#64 + 320#64) 16 ∗
          ((s0.sp - 608#64 + 336#64) ↦₆₄ noneCap) ∗ memRegion (s0.sp - 608#64 + 344#64) 16 ∗
          ((s0.sp - 608#64 + 360#64) ↦₆₄ noneCap) ∗ memRegion (s0.sp - 608#64 + 368#64) 16 ∗
          ((s0.sp - 608#64 + 384#64) ↦₆₄ noneCap) ∗ memRegion (s0.sp - 608#64 + 392#64) 16 ∗
          ((s0.sp - 608#64 + 408#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 608#64 + 412#64) 4 ∗
          ((s0.sp - 608#64 + 416#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 608#64 + 420#64) 4 ∗
          ((s0.sp - 608#64 + 424#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 608#64 + 428#64) 4 ∗
          ((s0.sp - 608#64 + 432#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 608#64 + 436#64) 4 ∗
          preKeyCalleeSavedAt (s0.sp - 608#64) s0))
      (tryFromQp s0) := by
  have hb := bytes_eq_cons_psmRem0 x
  have hge2 : 2 ≤ x.bytes.length := by
    have hrem0 := List.length_pos_of_ne_nil (psmRem0_ne_nil x)
    rw [hb, List.length_cons]; omega
  have hlen_ne : BitVec.ofNat 64 x.bytes.length ≠ 0#64 :=
    ofNat64_length_ne_zero (by rw [hb]; simp) hlt
  have hlen_beq : (BitVec.ofNat 64 x.bytes.length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hlen_ne
  have hcond_eq := cond_eq_subs1_false hge2 hlt
  have hsub1 : BitVec.ofNat 64 x.bytes.length - 1#64 = BitVec.ofNat 64 (psmRem0 x).length := by
    rw [hb, ofNat64_cons_sub_one]
  have hbytes : (x.ptr ↦ₛ x.bytes) = (x.ptr ↦₈ 0x44#8) ∗ ((x.ptr + 1#64) ↦ₛ psmRem0 x) := by
    rw [hb, pointsToBytes_cons]
  clear hb
  rw [hbytes]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono (memRegion152_init_cells (s0.sp - 608#64))
        (memRegion96_split_preKeyCalleeSaved (s0.sp - 608#64)))) ?_
  simp only [bv_sub_add_lit', BitVec.reduceSub,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun w19 => SepWPp.exists_pre fun w20 =>
    SepWPp.exists_pre fun w21 => SepWPp.exists_pre fun w22 =>
    SepWPp.exists_pre fun w23 => SepWPp.exists_pre fun w24 =>
    SepWPp.exists_pre fun w25 => SepWPp.exists_pre fun w26 =>
    SepWPp.exists_pre fun w27 => SepWPp.exists_pre fun w28 =>
    SepWPp.exists_pre fun w30 => SepWPp.exists_pre fun w29 =>
    SepWPp.exists_pre fun w440 =>
    SepWPp.exists_pre fun w432 => SepWPp.exists_pre fun w424 =>
    SepWPp.exists_pre fun w416 => SepWPp.exists_pre fun w408 =>
    SepWPp.exists_pre fun w384 => SepWPp.exists_pre fun w360 =>
    SepWPp.exists_pre fun w336 => SepWPp.exists_pre fun w312 =>
    SepWPp.exists_pre fun c1 => SepWPp.exists_pre fun c0 => ?_
  have hfn : libsignalSessionCode.fnOff preKeyTryFromName = 0x29c14 :=
    libsignalSessionCode_fnOff_0x29c14
  responder_wire_fetches_from img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x29c14 0 212
  clear hfn
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base _)
    ((libsignalSessionCode.rebase img.base _).fnAddr preKeyTryFromName + 244#64) _ _ _ _
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine ⟨⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩, ?_, hF1, hsym1,
    by simp [arm64_norm],
    by simp [arm64_norm], ?_⟩
  · rw [State.spAligned]
    simpa [arm64_norm] using spAligned_sub608 hsp
  · unfold sliceCursorAt preKeyCalleeSavedAt cur0 noneCap
    simp only [arm64_norm]
    apply entails_of_eq; ac_rfl
/-! ## Field Decode Iterations 1..8 (`0x29c24 .. 0x29e34` → `0x29f90`) -/
theorem bv_add_sub_lit (x a b : BitVec 64) : x + a - b = x + (a - b) := by bv_omega
theorem SepWPp.call_tryFrom {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {s0 s : Arm64.State} {P T F : SepProp} {φ : Prop}
    {Q : Arm64.State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry spec) (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F := by sep_focus)
    (hnext : ∀ sf : Arm64.State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      sf.spAligned = true → img.FrozenLoaded sf → sf.symtab = img.symtab →
      CalleeSavedPreserved s sf → SepWPp prog ret sf (spec.post x s sf ∗ F) Q (tryFromQp s0))
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) :=
      by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q (tryFromQp s0) := by
  refine ProofLib.SepWPp.call_wpp_frozen hcall hF hsym hpc hrun hsp hlr
    (x := x) (F := F)
    (fun R' hm => by
      rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]; exact ⟨hφ, hm⟩)
    (fun sm code _ _ hpost => by
      rw [hexit sm code] at hpost; exact allowPanic_not_exited hpost)
    (fun sm _ _ => by
      rw [hpan sm]; exact tryFromQp_of_call htr)
    (fun sm hpcm hrunm hspm hcsm hFm hsymm R' hpost hLm => ?_)
    (fun sm _ _ hoom => by
      rw [hoom_eq sm] at hoom; exact (not_satisfies_false_sepConj hoom).elim)
  have hspm_align : sm.spAligned = true := by
    rw [Arm64.State.spAligned, hspm, ← Arm64.State.spAligned]; exact hsp
  obtain ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hqf, hvf⟩ | hpanf⟩ :=
    hnext sm hpcm hrunm hspm hspm_align hFm hsymm hcsm R' hpost hLm
  · exact ⟨sf, hsteps',
      Or.inl ⟨hpcf, hrunf, Pf, hmf, hqf, hvf.trans hcsm.2.2.2.2.2.2.2.2.2.2.2⟩⟩
  · exact ⟨sf, hsteps', Or.inr hpanf⟩
attribute [local arm64_norm, local wp_norm] bv_add_sub_lit
/-- Field 1 step. -/
theorem step_field1_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    (hint32 : Int32MergeOk img.base C A ctl abs)
    {x : PreKeyTryFromArgs} {s0 s : State} {sp' : BitVec 64} (hlt0 : (psmRem0 x).length < 2 ^ 32)
    (hlt1 : (psmRem1 x).length < 2 ^ 32)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 0xf4#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' x s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (psmRem0 x).length) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 0xf4#64) s
      (sliceCursorAt (sp' + 296#64) (cur0 x) (psmRem0 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 416#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 420#64) 4 ∗ A.pool ∗
        stackAt sp' int32MergeStack)
      (fun s1 P1 =>
        PreKeyLoopRegs sp' x s1 ∧ s1.spAligned = true ∧ img.FrozenLoaded s1 ∧ s1.symtab =
        img.symtab ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem1 x).length ∧ ∃ opkVal : BitVec 32, (∀ v,
        x.opkId = some v → opkVal = v) ∧
          (P1 ⊢ (cur0 x ↦ₛ psmField1 x) ∗ sliceCursorAt (sp' + 296#64) (cur1 x) (psmRem1 x) ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
            ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗ A.pool ∗
            stackAt sp' int32MergeStack))
      (tryFromQp s0) := by
  cases hopk : x.opkId with
  | none =>
    have hf1 : psmField1 x = [] := by simp [psmField1, hopk, Prost.uint32Field]
    have hrem0 : psmRem0 x = psmRem1 x := by simp [psmRem0, hf1]
    have hcur1 : cur1 x = cur0 x := by simp [cur1, hf1]
    rw [memRegion_four (sp' + 420#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_pre fun w420 => ?_
    refine SepWPp.of_sepWP_end hF hsym ?_
    refine SepWP.done hpc hrun ?_
    intro hF1 hsym1
    refine ⟨hregs, hsp, hF1, hsym1, htr, by rw [← hrem0]; exact hx2,
      w420, fun _ h => by simp at h, ?_⟩
    simp only [opkTag, hopk, hf1, hcur1, hrem0, pointsToBytes_nil, emp_sepConj]
    apply entails_of_eq; ac_rfl
  | some v =>
    have hf1 := psmField1_some x v hopk
    let body := encodeVarint (v.zeroExtend 64)
    have hrem0 : psmRem0 x = 0x08#8 :: (body ++ psmRem1 x) := by rw [psmRem0, hf1, List.cons_append]
    have hlt_body : (body ++ psmRem1 x).length < 2 ^ 32 := by
      rw [hrem0, List.length_cons] at hlt0; omega
    have hsub1 : BitVec.ofNat 64 (psmRem0 x).length - 1#64 =
        BitVec.ofNat 64 (body ++ psmRem1 x).length := by
      rw [hrem0, ofNat64_cons_sub_one]
    have hrem1_ne : BitVec.ofNat 64 (psmRem1 x).length ≠ 0#64 :=
      ofNat64_length_ne_zero (psmRem1_ne_nil x) hlt1
    have hrem1_beq : (BitVec.ofNat 64 (psmRem1 x).length == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hrem1_ne
    have hcall := int32Merge_ok_at_prekey hint32
    have hfn : libsignalSessionCode.fnOff preKeyTryFromName = 0x29c14 :=
      libsignalSessionCode_fnOff_0x29c14
    let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
    responder_wire_fetches_from img.base H hfn 0x29c14 244 24
    responder_wire_fetches_from img.base H hfn 0x29c14 332 60
    responder_wire_fetches_from img.base H hfn 0x29c14 608 28
    responder_wire_fetches_from img.base H hfn 0x29c14 228 16; clear hfn
    dsimp only [tripleRatchetProgAt] at hcall hpc ⊢
    change SepWPp (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 244#64) _ _ _ _
    change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 244#64 at hpc
    change subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName +
        18446744073709391792#64) _ at hcall
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    have hsp_eq := hregs.sp
    have h29 := hregs.x29
    have h28 := hregs.x28
    have h26 := hregs.x26
    have h25 := hregs.x25
    have h23 := hregs.x23
    have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (psmRem0 x).length := hx2
    have hpts : (cur0 x ↦ₛ psmRem0 x) =
        (cur0 x ↦₈ 0x08#8) ∗ ((cur0 x + 1#64) ↦ₛ (body ++ psmRem1 x)) := by
      rw [hrem0, pointsToBytes_cons]
    clear hrem0
    unfold sliceCursorAt
    rw [hpts]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 616#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    have hent1 := pointsTo32_memRegion4_entails_exists_pointsTo64 (sp' + 416#64) 0#32
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hent1
    refine SepWPp.mono_pre
      (P' := (∃∗ w : BitVec 64, (sp' + 416#64) ↦₆₄ w) ∗ ((cur0 x ↦₈ 0x08#8) ∗ ((cur0 x +
        1#64) ↦ₛ (body ++ psmRem1 x)) ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 296#64) ↦₆₄ (cur0 x + 1#64)) ∗
          ((sp' + 304#64) ↦₆₄ BitVec.ofNat 64 (body ++ psmRem1 x).length) ∗ A.pool ∗
          stackAt sp' int32MergeStack))
      (by
        refine Entails.trans ?_ (sepConj_mono_left hent1)
        apply entails_of_eq; ac_rfl) ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_pre fun w416 => ?_
    refine SepWPp.of_sepWP_frozen hF1 hsym1 (mid := entry + 18446744073709391792#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF2 hsym2
    have hent2 := pointsTo64_one_entails_pointsTo32_memRegion4 (sp' + 416#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hent2
    refine SepWPp.mono_pre
      (P' := (((sp' + 416#64) ↦₃₂ 1#32) ∗ memRegion (sp' + 420#64) 4) ∗ ((cur0 x ↦₈ 0x08#8) ∗
        sliceCursorAt (sp' + 296#64) (cur0 x + 1#64) (body ++ psmRem1 x) ∗ ((sp' +
        440#64) ↦₆₄ (sp' + 296#64)) ∗ A.pool ∗ stackAt sp' int32MergeStack))
      (by
        unfold sliceCursorAt
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        refine Entails.trans ?_ (sepConj_mono_left hent2)
        apply entails_of_eq; ac_rfl) ?_
    simp only [sepConj_assoc]
    refine SepWPp.call_tryFrom
      ⟨.varint, sp' + 420#64, sp' + 440#64, sp' + 296#64, cur0 x + 1#64, body ++ psmRem1 x⟩
      hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF2 hsym2
      (ret_pc := entry + 632#64) (by simp [arm64_norm])
      (by simpa [arm64_norm] using htr)
      (T := memRegion (sp' + 420#64) 4 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        sliceCursorAt (sp' + 296#64) (cur0 x + 1#64) (body ++ psmRem1 x) ∗ A.pool ∗
        stackAt sp' int32MergeStack)
      (φ := (0#64 : BitVec 64).setWidth 8 = BitVec.ofNat 8 WireType.varint.toNat ∧ sp' + 312#64 +
        108#64 = sp' + 420#64 ∧
        sp' + 512#64 - 72#64 = sp' + 440#64 ∧ (body ++ psmRem1 x).length < 9223372036854775808)
      (by dsimp only [int32MergeSpec]; simp only [hsp_eq, arm64_norm])
      ⟨rfl, by bv_omega, by bv_omega, by omega⟩
      (by sep_focus)
      ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF3 hsym3 hcs2
    have hregs2 : PreKeyLoopRegs sp' x s2 := PreKeyLoopRegs.of_calleeSaved
        ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
         by simpa [arm64_norm] using h28, by simpa [arm64_norm] using hregs.x27,
         by simpa [arm64_norm] using h26, by simpa [arm64_norm] using h25,
         by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19⟩
        hsp2 hcs2
    have h29_2 := hregs2.x29
    dsimp only [int32MergeSpec]
    rw [merge_field1_some x v]
    dsimp only
    rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hx0_2 => ?_
    have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    have hpost_cur :
        (cur0 x ↦₈ 0x08#8) ∗ sliceCursorAfter (sp' + 296#64) (cur0 x + 1#64) (body ++
        psmRem1 x) (psmRem1 x) = (cur0 x ↦ₛ psmField1 x) ∗ (((sp' + 296#64) ↦₆₄ cur1 x) ∗ (((sp' +
        304#64) ↦₆₄ BitVec.ofNat 64 (psmRem1 x).length) ∗ (cur1 x ↦ₛ psmRem1 x))) := by
      rw [cons_sliceCursorAfter_split, ← hf1]
      unfold sliceCursorAt
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rfl
    refine SepWPp.mono_pre
      (P' := ((cur0 x ↦₈ 0x08#8) ∗ sliceCursorAfter (sp' + 296#64) (cur0 x + 1#64) (body ++
        psmRem1 x) (psmRem1 x)) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 416#64) ↦₃₂ 1#32) ∗ ((sp' + 420#64) ↦₃₂ v) ∗
        A.pool ∗ stackAt sp' int32MergeStack)
      (by
        simp only [hsp_eq, arm64_norm]
        apply entails_of_eq; ac_rfl) ?_
    rw [hpost_cur]
    simp only [sepConj_assoc]
    refine SepWPp.of_sepWP_end hF3 hsym3 ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    intro hF4 hsym4
    refine ⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
      by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x27,
      by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x25,
      by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
      by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
      by simpa [arm64_norm] using hregs2.x19⟩,
      by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
      hF4, hsym4, by simpa [arm64_norm] using htr2.trans htr,
      by simp [arm64_norm], v, fun v' hv' => Option.some.inj hv', ?_⟩
    simp only [opkTag, hopk]
    apply entails_of_eq; ac_rfl
/-- Field 2 step. -/ theorem step_field2_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hbytes : BytesMergeOk img C A ctl abs) {x : PreKeyTryFromArgs} {s0 s : State} {sp' : BitVec 64}
    (hlt1 : (psmRem1 x).length < 2 ^ 32) (hlt2 : (psmRem2 x).length < 2 ^ 32)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 0xf4#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' x s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (psmRem1 x).length) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 0xf4#64) s
      (sliceCursorAt (sp' + 296#64) (cur1 x) (psmRem1 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 336#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 344#64) 16 ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
      (fun s1 P1 =>
        PreKeyLoopRegs sp' x s1 ∧ s1.spAligned = true ∧ img.FrozenLoaded s1 ∧ s1.symtab =
        img.symtab ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem2 x).length ∧ ∃ cap' ptr' : BitVec 64,
          P1 ⊢ (cur1 x ↦ₛ psmField2 x) ∗ sliceCursorAt (sp' + 296#64) (cur2 x) (psmRem2 x) ∗ ((sp' +
          440#64) ↦₆₄ (sp' + 296#64)) ∗
            vecU8At A (sp' + 336#64) cap' ptr' x.bkBytes ∗ A.pool ∗ stackAt sp' bytesMergeStack)
      (tryFromQp s0) := by
  have hf2 := psmField2_eq x
  let body := encodeVarint 33#64 ++ x.bkBytes
  have hrem1 : psmRem1 x = 0x12#8 :: (body ++ psmRem2 x) := by rw [psmRem1, hf2, List.cons_append]
  have hlt_body : (body ++ psmRem2 x).length < 2 ^ 32 := by
    have hlen : (psmRem1 x).length = (body ++ psmRem2 x).length + 1 := by
      rw [hrem1, List.length_cons]
    omega
  have hsub1 : BitVec.ofNat 64 (psmRem1 x).length - 1#64 =
      BitVec.ofNat 64 (body ++ psmRem2 x).length := by
    rw [hrem1, ofNat64_cons_sub_one]
  have hrem2_ne : BitVec.ofNat 64 (psmRem2 x).length ≠ 0#64 :=
    ofNat64_length_ne_zero (psmRem2_ne_nil x) hlt2
  have hrem2_beq : (BitVec.ofNat 64 (psmRem2 x).length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hrem2_ne
  have hcall := bytesMerge_ok_at_prekey hbytes
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have hfn := libsignalSessionCode_fnOff_0x29c14
  responder_wire_fetches_from img.base H hfn 0x29c14 244 24
  responder_wire_fetches_from img.base H hfn 0x29c14 332 108
  responder_wire_fetches_from img.base H hfn 0x29c14 228 16
  clear hfn
  dsimp only [tripleRatchetProgAt] at hcall hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 244#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 244#64 at hpc
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 18446744073709390708#64) _
      at hcall
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hsp_eq := hregs.sp
  have h29 := hregs.x29
  have h28 := hregs.x28
  have h26 := hregs.x26
  have h25 := hregs.x25
  have h23 := hregs.x23
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (psmRem1 x).length := hx2
  have hpts : (cur1 x ↦ₛ psmRem1 x) =
      (cur1 x ↦₈ 0x12#8) ∗ ((cur1 x + 1#64) ↦ₛ (body ++ psmRem2 x)) := by
    rw [hrem1, pointsToBytes_cons]
  clear hrem1
  have hmr16 := memRegion16_split8_8' (sp' + 344#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmr16
  refine SepWPp.mono_pre
    (P' := (∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        ((sp' + 344#64) ↦₆₄ w0) ∗ ((sp' + 352#64) ↦₆₄ w1)) ∗ (sliceCursorAt (sp' +
        296#64) (cur1 x) (psmRem1 x) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 336#64) ↦₆₄ noneCap) ∗ A.pool ∗
        stackAt sp' bytesMergeStack))
    (by
      refine Entails.trans ?_ (sepConj_mono_left hmr16)
      apply entails_of_eq; ac_rfl) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w2 => ?_
  unfold sliceCursorAt
  rw [hpts]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 18446744073709390708#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.mono_pre
    (P' := (cur1 x ↦₈ 0x12#8) ∗ vecU8At A (sp' + 336#64) 0#64 1#64 [] ∗ ((sp' + 440#64) ↦₆₄ (sp' +
      296#64)) ∗ sliceCursorAt (sp' + 296#64) (cur1 x + 1#64) (body ++ psmRem2 x) ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
    (by
      rw [← pointsTo64_emptyVec_eq_vecU8At A sp' 336#64 344#64 352#64]
      unfold sliceCursorAt
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.call_tryFrom
    ⟨.lengthDelimited, sp' + 336#64, 0#64, 1#64, [], sp' + 440#64, sp' + 296#64,
      cur1 x + 1#64, body ++ psmRem2 x⟩
    hcall (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + 432#64) (by simp [arm64_norm]) (by simpa [arm64_norm] using htr)
    (T := vecU8At A (sp' + 336#64) 0#64 1#64 [] ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) (cur1 x + 1#64) (body ++ psmRem2 x) ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
    (φ := (2#64 : BitVec 64).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat ∧ sp' +
      312#64 + 24#64 = sp' + 336#64 ∧
      sp' + 512#64 - 72#64 = sp' + 440#64 ∧ (body ++ psmRem2 x).length < 9223372036854775808 ∧
      BytesMergeCapOk 0#64 (body ++ psmRem2 x).length)
    (by
      dsimp only [bytesMergeSpec, Spec.inImage]
      rw [pure_true_emp (And.intro hF1 hsym1), emp_sepConj]
      simp only [bytesMergeRawSpec, hsp_eq, arm64_norm])
    ⟨rfl, by bv_omega, by bv_omega, by omega, bytesMergeCapOk_of_len_lt32 hlt_body⟩ (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  have hregs2 : PreKeyLoopRegs sp' x s2 := PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using h28, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using h26, by simpa [arm64_norm] using h25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      hsp2 hcs2
  have h29_2 := hregs2.x29
  dsimp only [bytesMergeSpec, Spec.inImage, bytesMergeRawSpec]; rw [merge_field2 x]
  dsimp only; rw [sepConj_assoc]; refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre fun hx0_2 => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
  refine SepWPp.exists_pre fun cap' => SepWPp.exists_pre fun ptr' => SepWPp.pure_pre fun _ => ?_
  have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hpost_cur :
      (cur1 x ↦₈ 0x12#8) ∗ sliceCursorAfter (sp' + 296#64) (cur1 x + 1#64) (body ++
        psmRem2 x) (psmRem2 x) =
      (cur1 x ↦ₛ psmField2 x) ∗ (((sp' + 296#64) ↦₆₄ cur2 x) ∗ (((sp' +
        304#64) ↦₆₄ BitVec.ofNat 64 (psmRem2 x).length) ∗ (cur2 x ↦ₛ psmRem2 x))) := by
    rw [cons_sliceCursorAfter_split, ← hf2]
    unfold sliceCursorAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rfl
  refine SepWPp.mono_pre
    (P' := ((cur1 x ↦₈ 0x12#8) ∗ sliceCursorAfter (sp' + 296#64) (cur1 x + 1#64) (body ++
      psmRem2 x) (psmRem2 x)) ∗
      ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ vecU8At A (sp' + 336#64) cap' ptr' x.bkBytes ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
    (by
      simp only [hsp_eq, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  rw [hpost_cur]; simp only [sepConj_assoc]; refine SepWPp.of_sepWP_end hF2 hsym2 ?_; wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hF3 hsym3
  refine ⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x27,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x25,
    by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
    by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
    by simpa [arm64_norm] using hregs2.x19⟩,
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hF3, hsym3, by simpa [arm64_norm] using htr2.trans htr,
    by simp [arm64_norm], cap', ptr', ?_⟩
  apply entails_of_eq; ac_rfl
/-- Field 3 step. -/ theorem step_field3_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hbytes : BytesMergeOk img C A ctl abs) {x : PreKeyTryFromArgs} {s0 s : State} {sp' : BitVec 64}
    (hlt2 : (psmRem2 x).length < 2 ^ 32) (hlt3 : (psmRem3 x).length < 2 ^ 32)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 0xf4#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' x s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (psmRem2 x).length) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 0xf4#64) s
      (sliceCursorAt (sp' + 296#64) (cur2 x) (psmRem2 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
      (fun s1 P1 =>
        PreKeyLoopRegs sp' x s1 ∧ s1.spAligned = true ∧ img.FrozenLoaded s1 ∧ s1.symtab =
        img.symtab ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem3 x).length ∧ ∃ cap' ptr' : BitVec 64,
          P1 ⊢ (cur2 x ↦ₛ psmField3 x) ∗ sliceCursorAt (sp' + 296#64) (cur3 x) (psmRem3 x) ∗ ((sp' +
          440#64) ↦₆₄ (sp' + 296#64)) ∗
            vecU8At A (sp' + 360#64) cap' ptr' x.ikBytes ∗ A.pool ∗ stackAt sp' bytesMergeStack)
      (tryFromQp s0) := by
  have hf3 := psmField3_eq x
  let body := encodeVarint 33#64 ++ x.ikBytes
  have hrem2 : psmRem2 x = 0x1a#8 :: (body ++ psmRem3 x) := by rw [psmRem2, hf3, List.cons_append]
  have hlt_body : (body ++ psmRem3 x).length < 2 ^ 32 := by
    have hlen : (psmRem2 x).length = (body ++ psmRem3 x).length + 1 := by
      rw [hrem2, List.length_cons]
    omega
  have hsub1 : BitVec.ofNat 64 (psmRem2 x).length - 1#64 =
      BitVec.ofNat 64 (body ++ psmRem3 x).length := by
    rw [hrem2, ofNat64_cons_sub_one]
  have hrem3_ne : BitVec.ofNat 64 (psmRem3 x).length ≠ 0#64 :=
    ofNat64_length_ne_zero (psmRem3_ne_nil x) hlt3
  have hrem3_beq : (BitVec.ofNat 64 (psmRem3 x).length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hrem3_ne
  have hcall := bytesMerge_ok_at_prekey hbytes
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have hfn := libsignalSessionCode_fnOff_0x29c14
  responder_wire_fetches_from img.base H hfn 0x29c14 244 24
  responder_wire_fetches_from img.base H hfn 0x29c14 332 52
  responder_wire_fetches_from img.base H hfn 0x29c14 496 8
  responder_wire_fetches_from img.base H hfn 0x29c14 672 36
  responder_wire_fetches_from img.base H hfn 0x29c14 228 16
  clear hfn
  dsimp only [tripleRatchetProgAt] at hcall hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 244#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 244#64 at hpc
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 18446744073709390708#64) _
      at hcall
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hsp_eq := hregs.sp
  have h29 := hregs.x29
  have h28 := hregs.x28
  have h26 := hregs.x26
  have h25 := hregs.x25
  have h23 := hregs.x23
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (psmRem2 x).length := hx2
  have hpts : (cur2 x ↦ₛ psmRem2 x) =
      (cur2 x ↦₈ 0x1a#8) ∗ ((cur2 x + 1#64) ↦ₛ (body ++ psmRem3 x)) := by
    rw [hrem2, pointsToBytes_cons]
  clear hrem2
  have hmr16 := memRegion16_split8_8' (sp' + 368#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmr16
  refine SepWPp.mono_pre
    (P' := (∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        ((sp' + 368#64) ↦₆₄ w0) ∗ ((sp' + 376#64) ↦₆₄ w1)) ∗ (sliceCursorAt (sp' +
        296#64) (cur2 x) (psmRem2 x) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 360#64) ↦₆₄ noneCap) ∗ A.pool ∗
        stackAt sp' bytesMergeStack))
    (by
      refine Entails.trans ?_ (sepConj_mono_left hmr16)
      apply entails_of_eq; ac_rfl) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w2 => ?_
  unfold sliceCursorAt
  rw [hpts]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 18446744073709390708#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.mono_pre
    (P' := (cur2 x ↦₈ 0x1a#8) ∗ vecU8At A (sp' + 360#64) 0#64 1#64 [] ∗ ((sp' + 440#64) ↦₆₄ (sp' +
      296#64)) ∗ sliceCursorAt (sp' + 296#64) (cur2 x + 1#64) (body ++ psmRem3 x) ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
    (by
      rw [← pointsTo64_emptyVec_eq_vecU8At A sp' 360#64 368#64 376#64]
      unfold sliceCursorAt
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.call_tryFrom
    ⟨.lengthDelimited, sp' + 360#64, 0#64, 1#64, [], sp' + 440#64, sp' + 296#64,
      cur2 x + 1#64, body ++ psmRem3 x⟩
    hcall (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + 704#64) (by simp [arm64_norm]) (by simpa [arm64_norm] using htr)
    (T := vecU8At A (sp' + 360#64) 0#64 1#64 [] ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) (cur2 x + 1#64) (body ++ psmRem3 x) ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
    (φ := (2#64 : BitVec 64).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat ∧ sp' +
      312#64 + 48#64 = sp' + 360#64 ∧
      sp' + 512#64 - 72#64 = sp' + 440#64 ∧ (body ++ psmRem3 x).length < 9223372036854775808 ∧
      BytesMergeCapOk 0#64 (body ++ psmRem3 x).length)
    (by
      dsimp only [bytesMergeSpec, Spec.inImage]
      rw [pure_true_emp (And.intro hF1 hsym1), emp_sepConj]
      simp only [bytesMergeRawSpec, hsp_eq, arm64_norm])
    ⟨rfl, by bv_omega, by bv_omega, by omega, bytesMergeCapOk_of_len_lt32 hlt_body⟩ (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  have hregs2 : PreKeyLoopRegs sp' x s2 := PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using h28, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using h26, by simpa [arm64_norm] using h25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      hsp2 hcs2
  have h29_2 := hregs2.x29
  dsimp only [bytesMergeSpec, Spec.inImage, bytesMergeRawSpec]; rw [merge_field3 x]
  dsimp only; rw [sepConj_assoc]; refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre fun hx0_2 => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
  refine SepWPp.exists_pre fun cap' => SepWPp.exists_pre fun ptr' => SepWPp.pure_pre fun _ => ?_
  have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hpost_cur :
      (cur2 x ↦₈ 0x1a#8) ∗ sliceCursorAfter (sp' + 296#64) (cur2 x + 1#64) (body ++
        psmRem3 x) (psmRem3 x) =
      (cur2 x ↦ₛ psmField3 x) ∗ (((sp' + 296#64) ↦₆₄ cur3 x) ∗ (((sp' +
        304#64) ↦₆₄ BitVec.ofNat 64 (psmRem3 x).length) ∗ (cur3 x ↦ₛ psmRem3 x))) := by
    rw [cons_sliceCursorAfter_split, ← hf3]
    unfold sliceCursorAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rfl
  refine SepWPp.mono_pre
    (P' := ((cur2 x ↦₈ 0x1a#8) ∗ sliceCursorAfter (sp' + 296#64) (cur2 x + 1#64) (body ++
      psmRem3 x) (psmRem3 x)) ∗
      ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ vecU8At A (sp' + 360#64) cap' ptr' x.ikBytes ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
    (by
      simp only [hsp_eq, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  rw [hpost_cur]; simp only [sepConj_assoc]; refine SepWPp.of_sepWP_end hF2 hsym2 ?_; wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hF3 hsym3
  refine ⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x27,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x25,
    by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
    by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
    by simpa [arm64_norm] using hregs2.x19⟩,
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hF3, hsym3, by simpa [arm64_norm] using htr2.trans htr,
    by simp [arm64_norm], cap', ptr', ?_⟩
  apply entails_of_eq; ac_rfl
/-- Field 4 step. -/ theorem step_field4_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hbytes : BytesMergeOk img C A ctl abs) {x : PreKeyTryFromArgs} {s0 s : State} {sp' : BitVec 64}
    (hlt_inner : x.inner.length < 2 ^ 32) (hlt3 : (psmRem3 x).length < 2 ^ 32)
    (hlt4 : (psmRem4 x).length < 2 ^ 32)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 0xf4#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' x s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (psmRem3 x).length) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 0xf4#64) s
      (sliceCursorAt (sp' + 296#64) (cur3 x) (psmRem3 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
      (fun s1 P1 =>
        PreKeyLoopRegs sp' x s1 ∧ s1.spAligned = true ∧ img.FrozenLoaded s1 ∧ s1.symtab =
        img.symtab ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem4 x).length ∧ ∃ cap' ptr' : BitVec 64,
          P1 ⊢ (cur3 x ↦ₛ psmField4 x) ∗ sliceCursorAt (sp' + 296#64) (cur4 x) (psmRem4 x) ∗ ((sp' +
          440#64) ↦₆₄ (sp' + 296#64)) ∗
            vecU8At A (sp' + 384#64) cap' ptr' x.inner ∗ A.pool ∗ stackAt sp' bytesMergeStack)
      (tryFromQp s0) := by
  have hlt_inner64 : x.inner.length < 2 ^ 64 := by omega
  have hf4 := psmField4_eq x hlt_inner64
  let body := encodeVarint (BitVec.ofNat 64 x.inner.length) ++ x.inner
  have hrem3 : psmRem3 x = 0x22#8 :: (body ++ psmRem4 x) := by rw [psmRem3, hf4, List.cons_append]
  have hlt_body : (body ++ psmRem4 x).length < 2 ^ 32 := by
    have hlen : (psmRem3 x).length = (body ++ psmRem4 x).length + 1 := by
      rw [hrem3, List.length_cons]
    omega
  have hsub1 : BitVec.ofNat 64 (psmRem3 x).length - 1#64 =
      BitVec.ofNat 64 (body ++ psmRem4 x).length := by
    rw [hrem3, ofNat64_cons_sub_one]
  have hrem4_ne : BitVec.ofNat 64 (psmRem4 x).length ≠ 0#64 :=
    ofNat64_length_ne_zero (psmRem4_ne_nil x) hlt4
  have hrem4_beq : (BitVec.ofNat 64 (psmRem4 x).length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hrem4_ne
  have hcall := bytesMerge_ok_at_prekey hbytes
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have hfn := libsignalSessionCode_fnOff_0x29c14
  responder_wire_fetches_from img.base H hfn 0x29c14 244 24
  responder_wire_fetches_from img.base H hfn 0x29c14 332 52
  responder_wire_fetches_from img.base H hfn 0x29c14 496 52
  responder_wire_fetches_from img.base H hfn 0x29c14 228 16
  clear hfn
  dsimp only [tripleRatchetProgAt] at hcall hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 244#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 244#64 at hpc
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 18446744073709390708#64) _
      at hcall
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hsp_eq := hregs.sp
  have h29 := hregs.x29
  have h28 := hregs.x28
  have h26 := hregs.x26
  have h25 := hregs.x25
  have h23 := hregs.x23
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (psmRem3 x).length := hx2
  have hpts : (cur3 x ↦ₛ psmRem3 x) =
      (cur3 x ↦₈ 0x22#8) ∗ ((cur3 x + 1#64) ↦ₛ (body ++ psmRem4 x)) := by
    rw [hrem3, pointsToBytes_cons]
  clear hrem3
  have hmr16 := memRegion16_split8_8' (sp' + 392#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmr16
  refine SepWPp.mono_pre
    (P' := (∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        ((sp' + 392#64) ↦₆₄ w0) ∗ ((sp' + 400#64) ↦₆₄ w1)) ∗ (sliceCursorAt (sp' +
        296#64) (cur3 x) (psmRem3 x) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 384#64) ↦₆₄ noneCap) ∗ A.pool ∗
        stackAt sp' bytesMergeStack))
    (by
      refine Entails.trans ?_ (sepConj_mono_left hmr16)
      apply entails_of_eq; ac_rfl) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w2 => ?_
  unfold sliceCursorAt
  rw [hpts]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 18446744073709390708#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.mono_pre
    (P' := (cur3 x ↦₈ 0x22#8) ∗ vecU8At A (sp' + 384#64) 0#64 1#64 [] ∗ ((sp' + 440#64) ↦₆₄ (sp' +
      296#64)) ∗ sliceCursorAt (sp' + 296#64) (cur3 x + 1#64) (body ++ psmRem4 x) ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
    (by
      rw [← pointsTo64_emptyVec_eq_vecU8At A sp' 384#64 392#64 400#64]
      unfold sliceCursorAt
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.call_tryFrom
    ⟨.lengthDelimited, sp' + 384#64, 0#64, 1#64, [], sp' + 440#64, sp' + 296#64,
      cur3 x + 1#64, body ++ psmRem4 x⟩
    hcall (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + 544#64) (by simp [arm64_norm]) (by simpa [arm64_norm] using htr)
    (T := vecU8At A (sp' + 384#64) 0#64 1#64 [] ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) (cur3 x + 1#64) (body ++ psmRem4 x) ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
    (φ := (2#64 : BitVec 64).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat ∧ sp' +
      312#64 + 72#64 = sp' + 384#64 ∧
      sp' + 512#64 - 72#64 = sp' + 440#64 ∧ (body ++ psmRem4 x).length < 9223372036854775808 ∧
      BytesMergeCapOk 0#64 (body ++ psmRem4 x).length)
    (by
      dsimp only [bytesMergeSpec, Spec.inImage]
      rw [pure_true_emp (And.intro hF1 hsym1), emp_sepConj]
      simp only [bytesMergeRawSpec, hsp_eq, arm64_norm])
    ⟨rfl, by bv_omega, by bv_omega, by omega, bytesMergeCapOk_of_len_lt32 hlt_body⟩ (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  have hregs2 : PreKeyLoopRegs sp' x s2 := PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using h28, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using h26, by simpa [arm64_norm] using h25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      hsp2 hcs2
  have h29_2 := hregs2.x29
  dsimp only [bytesMergeSpec, Spec.inImage, bytesMergeRawSpec]; rw [merge_field4 x hlt_inner64]
  dsimp only; rw [sepConj_assoc]; refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre fun hx0_2 => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
  refine SepWPp.exists_pre fun cap' => SepWPp.exists_pre fun ptr' => SepWPp.pure_pre fun _ => ?_
  have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hpost_cur :
      (cur3 x ↦₈ 0x22#8) ∗ sliceCursorAfter (sp' + 296#64) (cur3 x + 1#64) (body ++
        psmRem4 x) (psmRem4 x) =
      (cur3 x ↦ₛ psmField4 x) ∗ (((sp' + 296#64) ↦₆₄ cur4 x) ∗ (((sp' +
        304#64) ↦₆₄ BitVec.ofNat 64 (psmRem4 x).length) ∗ (cur4 x ↦ₛ psmRem4 x))) := by
    rw [cons_sliceCursorAfter_split, ← hf4]
    unfold sliceCursorAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rfl
  refine SepWPp.mono_pre
    (P' := ((cur3 x ↦₈ 0x22#8) ∗ sliceCursorAfter (sp' + 296#64) (cur3 x + 1#64) (body ++
      psmRem4 x) (psmRem4 x)) ∗
      ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ vecU8At A (sp' + 384#64) cap' ptr' x.inner ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
    (by
      simp only [hsp_eq, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  rw [hpost_cur]; simp only [sepConj_assoc]; refine SepWPp.of_sepWP_end hF2 hsym2 ?_; wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hF3 hsym3
  refine ⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x27,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x25,
    by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
    by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
    by simpa [arm64_norm] using hregs2.x19⟩,
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hF3, hsym3, by simpa [arm64_norm] using htr2.trans htr,
    by simp [arm64_norm], cap', ptr', ?_⟩
  apply entails_of_eq; ac_rfl
/-- Field 5 (`u32`) step. -/ theorem step_field5_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hint32 : Int32MergeOk img.base C A ctl abs)
    {x : PreKeyTryFromArgs} {s0 s : State} {sp' : BitVec 64} (hlt4 : (psmRem4 x).length < 2 ^ 32)
    (hlt5 : (psmRem5 x).length < 2 ^ 32)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 0xf4#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' x s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (psmRem4 x).length) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 0xf4#64) s
      (sliceCursorAt (sp' + 296#64) (cur4 x) (psmRem4 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗ A.pool ∗
        stackAt sp' int32MergeStack)
      (fun s1 P1 =>
        PreKeyLoopRegs sp' x s1 ∧ s1.spAligned = true ∧ img.FrozenLoaded s1 ∧ s1.symtab =
        img.symtab ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem5 x).length ∧ (P1 ⊢ (cur4 x ↦ₛ psmField5 x) ∗
          sliceCursorAt (sp' + 296#64) (cur5 x) (psmRem5 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗ A.pool ∗
          stackAt sp' int32MergeStack))
      (tryFromQp s0) := by
  have hf5 := psmField5_eq x
  let body := encodeVarint (x.regId.zeroExtend 64)
  have hrem4 : psmRem4 x = 0x28#8 :: (body ++ psmRem5 x) := by rw [psmRem4, hf5, List.cons_append]
  have hlt_body : (body ++ psmRem5 x).length < 2 ^ 32 := by
    have hlen : (psmRem4 x).length = (body ++ psmRem5 x).length + 1 := by
      rw [hrem4, List.length_cons]
    omega
  have hsub1 : BitVec.ofNat 64 (psmRem4 x).length - 1#64 =
      BitVec.ofNat 64 (body ++ psmRem5 x).length := by
    rw [hrem4, ofNat64_cons_sub_one]
  have hrem5_ne : BitVec.ofNat 64 (psmRem5 x).length ≠ 0#64 :=
    ofNat64_length_ne_zero (psmRem5_ne_nil x) hlt5
  have hrem5_beq : (BitVec.ofNat 64 (psmRem5 x).length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hrem5_ne
  have hcall := int32Merge_ok_at_prekey hint32
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have hfn := libsignalSessionCode_fnOff_0x29c14
  responder_wire_fetches_from img.base H hfn 0x29c14 244 24
  responder_wire_fetches_from img.base H hfn 0x29c14 332 44
  responder_wire_fetches_from img.base H hfn 0x29c14 440 16
  responder_wire_fetches_from img.base H hfn 0x29c14 640 28
  responder_wire_fetches_from img.base H hfn 0x29c14 228 16
  clear hfn
  dsimp only [tripleRatchetProgAt] at hcall hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 244#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 244#64 at hpc
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 18446744073709391792#64) _
      at hcall
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hsp_eq := hregs.sp
  have h29 := hregs.x29
  have h28 := hregs.x28
  have h26 := hregs.x26
  have h25 := hregs.x25
  have h23 := hregs.x23
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (psmRem4 x).length := hx2
  have hpts : (cur4 x ↦ₛ psmRem4 x) =
      (cur4 x ↦₈ 0x28#8) ∗ ((cur4 x + 1#64) ↦ₛ (body ++ psmRem5 x)) := by
    rw [hrem4, pointsToBytes_cons]
  clear hrem4
  unfold sliceCursorAt
  rw [hpts]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 648#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  have hent1 := pointsTo32_memRegion4_entails_exists_pointsTo64 (sp' + 408#64) 0#32
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hent1
  refine SepWPp.mono_pre
    (P' := (∃∗ w : BitVec 64, (sp' + 408#64) ↦₆₄ w) ∗ ((cur4 x ↦₈ 0x28#8) ∗ ((cur4 x +
      1#64) ↦ₛ (body ++ psmRem5 x)) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 296#64) ↦₆₄ (cur4 x + 1#64)) ∗
        ((sp' + 304#64) ↦₆₄ BitVec.ofNat 64 (body ++ psmRem5 x).length) ∗ A.pool ∗
        stackAt sp' int32MergeStack))
    (by
      refine Entails.trans ?_ (sepConj_mono_left hent1)
      apply entails_of_eq; ac_rfl) ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_pre fun w408 => ?_
  refine SepWPp.of_sepWP_frozen hF1 hsym1 (mid := entry + 18446744073709391792#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF2 hsym2
  have hent2 := pointsTo64_one_entails_pointsTo32_memRegion4 (sp' + 408#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hent2
  refine SepWPp.mono_pre
    (P' := (((sp' + 408#64) ↦₃₂ 1#32) ∗ memRegion (sp' + 412#64) 4) ∗ ((cur4 x ↦₈ 0x28#8) ∗
      sliceCursorAt (sp' + 296#64) (cur4 x + 1#64) (body ++ psmRem5 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' +
        296#64)) ∗
      A.pool ∗ stackAt sp' int32MergeStack))
    (by
      unfold sliceCursorAt
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      refine Entails.trans ?_ (sepConj_mono_left hent2)
      apply entails_of_eq; ac_rfl) ?_
  simp only [sepConj_assoc]
  refine SepWPp.call_tryFrom
    ⟨.varint, sp' + 412#64, sp' + 440#64, sp' + 296#64, cur4 x + 1#64, body ++ psmRem5 x⟩
    hcall (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF2 hsym2
    (ret_pc := entry + 664#64) (by simp [arm64_norm]) (by simpa [arm64_norm] using htr)
    (T := memRegion (sp' + 412#64) 4 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) (cur4 x + 1#64) (body ++ psmRem5 x) ∗ A.pool ∗
        stackAt sp' int32MergeStack)
    (φ := (0#64 : BitVec 64).setWidth 8 = BitVec.ofNat 8 WireType.varint.toNat ∧ sp' + 312#64 +
      100#64 = sp' + 412#64 ∧
      sp' + 512#64 - 72#64 = sp' + 440#64 ∧ (body ++ psmRem5 x).length < 9223372036854775808)
    (by dsimp only [int32MergeSpec]; simp only [hsp_eq, arm64_norm])
    ⟨rfl, by bv_omega, by bv_omega, by omega⟩ (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF3 hsym3 hcs2
  have hregs2 : PreKeyLoopRegs sp' x s2 := PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using h28, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using h26, by simpa [arm64_norm] using h25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      hsp2 hcs2
  have h29_2 := hregs2.x29
  dsimp only [int32MergeSpec]
  rw [merge_field5 x]
  dsimp only; rw [sepConj_assoc]; refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre fun hx0_2 => ?_
  have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hpost_cur :
      (cur4 x ↦₈ 0x28#8) ∗ sliceCursorAfter (sp' + 296#64) (cur4 x + 1#64) (body ++
        psmRem5 x) (psmRem5 x) =
      (cur4 x ↦ₛ psmField5 x) ∗ (((sp' + 296#64) ↦₆₄ cur5 x) ∗ (((sp' +
        304#64) ↦₆₄ BitVec.ofNat 64 (psmRem5 x).length) ∗ (cur5 x ↦ₛ psmRem5 x))) := by
    rw [cons_sliceCursorAfter_split, ← hf5]
    unfold sliceCursorAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rfl
  refine SepWPp.mono_pre
    (P' := ((cur4 x ↦₈ 0x28#8) ∗ sliceCursorAfter (sp' + 296#64) (cur4 x + 1#64) (body ++
      psmRem5 x) (psmRem5 x)) ∗
      ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' +
        412#64) ↦₃₂ x.regId) ∗
      A.pool ∗ stackAt sp' int32MergeStack)
    (by
      simp only [hsp_eq, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  rw [hpost_cur]
  simp only [sepConj_assoc]
  refine SepWPp.of_sepWP_end hF3 hsym3 ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hF4 hsym4
  refine ⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x27,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x25,
    by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
    by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
    by simpa [arm64_norm] using hregs2.x19⟩,
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hF4, hsym4, by simpa [arm64_norm] using htr2.trans htr,
    by simp [arm64_norm], ?_⟩
  apply entails_of_eq; ac_rfl
/-- Field 6 (`u32`) step. -/ theorem step_field6_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hint32 : Int32MergeOk img.base C A ctl abs)
    {x : PreKeyTryFromArgs} {s0 s : State} {sp' : BitVec 64} (hlt5 : (psmRem5 x).length < 2 ^ 32)
    (hlt6 : (psmRem6 x).length < 2 ^ 32)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 0xf4#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' x s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (psmRem5 x).length) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 0xf4#64) s
      (sliceCursorAt (sp' + 296#64) (cur5 x) (psmRem5 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗ A.pool ∗
        stackAt sp' int32MergeStack)
      (fun s1 P1 =>
        PreKeyLoopRegs sp' x s1 ∧ s1.spAligned = true ∧ img.FrozenLoaded s1 ∧ s1.symtab =
        img.symtab ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem6 x).length ∧ (P1 ⊢ (cur5 x ↦ₛ psmField6 x) ∗
          sliceCursorAt (sp' + 296#64) (cur6 x) (psmRem6 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗ A.pool ∗
          stackAt sp' int32MergeStack))
      (tryFromQp s0) := by
  have hf6 := psmField6_eq x
  let body := encodeVarint (x.spkId.zeroExtend 64)
  have hrem5 : psmRem5 x = 0x30#8 :: (body ++ psmRem6 x) := by
    rw [psmRem5, hf6, List.cons_append]
  have hlt_body : (body ++ psmRem6 x).length < 2 ^ 32 := by
    have hlen : (psmRem5 x).length = (body ++ psmRem6 x).length + 1 := by
      rw [hrem5, List.length_cons]
    omega
  have hsub1 : BitVec.ofNat 64 (psmRem5 x).length - 1#64 =
      BitVec.ofNat 64 (body ++ psmRem6 x).length := by
    rw [hrem5, ofNat64_cons_sub_one]
  have hrem6_ne : BitVec.ofNat 64 (psmRem6 x).length ≠ 0#64 :=
    ofNat64_length_ne_zero (psmRem6_ne_nil x) hlt6
  have hrem6_beq : (BitVec.ofNat 64 (psmRem6 x).length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hrem6_ne
  have hcall := int32Merge_ok_at_prekey hint32
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have hfn := libsignalSessionCode_fnOff_0x29c14
  responder_wire_fetches_from img.base H hfn 0x29c14 244 24
  responder_wire_fetches_from img.base H hfn 0x29c14 332 44
  responder_wire_fetches_from img.base H hfn 0x29c14 440 52
  responder_wire_fetches_from img.base H hfn 0x29c14 228 16
  clear hfn
  dsimp only [tripleRatchetProgAt] at hcall hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 244#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 244#64 at hpc
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 18446744073709391792#64) _
      at hcall
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hsp_eq := hregs.sp
  have h29 := hregs.x29
  have h28 := hregs.x28
  have h26 := hregs.x26
  have h25 := hregs.x25
  have h23 := hregs.x23
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (psmRem5 x).length := hx2
  have hpts : (cur5 x ↦ₛ psmRem5 x) =
      (cur5 x ↦₈ 0x30#8) ∗ ((cur5 x + 1#64) ↦ₛ (body ++ psmRem6 x)) := by
    rw [hrem5, pointsToBytes_cons]
  clear hrem5
  unfold sliceCursorAt
  rw [hpts]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 472#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  have hent1 := pointsTo32_memRegion4_entails_exists_pointsTo64 (sp' + 424#64) 0#32
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hent1
  refine SepWPp.mono_pre
    (P' := (∃∗ w : BitVec 64, (sp' + 424#64) ↦₆₄ w) ∗ ((cur5 x ↦₈ 0x30#8) ∗ ((cur5 x +
      1#64) ↦ₛ (body ++ psmRem6 x)) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 296#64) ↦₆₄ (cur5 x + 1#64)) ∗
        ((sp' + 304#64) ↦₆₄ BitVec.ofNat 64 (body ++ psmRem6 x).length) ∗ A.pool ∗
        stackAt sp' int32MergeStack))
    (by
      refine Entails.trans ?_ (sepConj_mono_left hent1)
      apply entails_of_eq; ac_rfl) ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_pre fun w424 => ?_
  refine SepWPp.of_sepWP_frozen hF1 hsym1 (mid := entry + 18446744073709391792#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF2 hsym2
  have hent2 := pointsTo64_one_entails_pointsTo32_memRegion4 (sp' + 424#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hent2
  refine SepWPp.mono_pre
    (P' := (((sp' + 424#64) ↦₃₂ 1#32) ∗ memRegion (sp' + 428#64) 4) ∗ ((cur5 x ↦₈ 0x30#8) ∗
      sliceCursorAt (sp' + 296#64) (cur5 x + 1#64) (body ++ psmRem6 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' +
        296#64)) ∗
      A.pool ∗ stackAt sp' int32MergeStack))
    (by
      unfold sliceCursorAt
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      refine Entails.trans ?_ (sepConj_mono_left hent2)
      apply entails_of_eq; ac_rfl) ?_
  simp only [sepConj_assoc]
  refine SepWPp.call_tryFrom
    ⟨.varint, sp' + 428#64, sp' + 440#64, sp' + 296#64, cur5 x + 1#64, body ++ psmRem6 x⟩
    hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF2 hsym2
    (ret_pc := entry + 488#64) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := memRegion (sp' + 428#64) 4 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) (cur5 x + 1#64) (body ++ psmRem6 x) ∗ A.pool ∗
        stackAt sp' int32MergeStack)
    (φ := (0#64 : BitVec 64).setWidth 8 = BitVec.ofNat 8 WireType.varint.toNat ∧ sp' + 312#64 +
      116#64 = sp' + 428#64 ∧
      sp' + 512#64 - 72#64 = sp' + 440#64 ∧ (body ++ psmRem6 x).length < 9223372036854775808)
    (by dsimp only [int32MergeSpec]; simp only [hsp_eq, arm64_norm])
    ⟨rfl, by bv_omega, by bv_omega, by omega⟩
    (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF3 hsym3 hcs2
  have hregs2 : PreKeyLoopRegs sp' x s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using h28, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using h26, by simpa [arm64_norm] using h25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      hsp2 hcs2
  have h29_2 := hregs2.x29
  dsimp only [int32MergeSpec]
  rw [merge_field6 x]
  dsimp only; rw [sepConj_assoc]; refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre fun hx0_2 => ?_
  have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hpost_cur :
      (cur5 x ↦₈ 0x30#8) ∗ sliceCursorAfter (sp' + 296#64) (cur5 x + 1#64) (body ++
        psmRem6 x) (psmRem6 x) =
      (cur5 x ↦ₛ psmField6 x) ∗ (((sp' + 296#64) ↦₆₄ cur6 x) ∗ (((sp' +
        304#64) ↦₆₄ BitVec.ofNat 64 (psmRem6 x).length) ∗
        (cur6 x ↦ₛ psmRem6 x))) := by
    rw [cons_sliceCursorAfter_split, ← hf6]
    unfold sliceCursorAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rfl
  refine SepWPp.mono_pre
    (P' := ((cur5 x ↦₈ 0x30#8) ∗ sliceCursorAfter (sp' + 296#64) (cur5 x + 1#64) (body ++
      psmRem6 x) (psmRem6 x)) ∗
      ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' +
        428#64) ↦₃₂ x.spkId) ∗
      A.pool ∗ stackAt sp' int32MergeStack)
    (by
      simp only [hsp_eq, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  rw [hpost_cur]
  simp only [sepConj_assoc]
  refine SepWPp.of_sepWP_end hF3 hsym3 ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hF4 hsym4
  refine ⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x27,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x25,
    by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
    by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
    by simpa [arm64_norm] using hregs2.x19⟩,
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hF4, hsym4, by simpa [arm64_norm] using htr2.trans htr,
    by simp [arm64_norm], ?_⟩
  apply entails_of_eq; ac_rfl
/-- Field 7 (`u32`) step. -/ theorem step_field7_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hint32 : Int32MergeOk img.base C A ctl abs)
    {x : PreKeyTryFromArgs} {s0 s : State} {sp' : BitVec 64}
    (hlt6 : (psmRem6 x).length < 2 ^ 32)
    (hlt7 : (psmRem7 x).length < 2 ^ 32)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 0xf4#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' x s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (psmRem6 x).length) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 0xf4#64) s
      (sliceCursorAt (sp' + 296#64) (cur6 x) (psmRem6 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗ A.pool ∗
        stackAt sp' int32MergeStack)
      (fun s1 P1 =>
        PreKeyLoopRegs sp' x s1 ∧ s1.spAligned = true ∧ img.FrozenLoaded s1 ∧ s1.symtab =
        img.symtab ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem7 x).length ∧ (P1 ⊢ (cur6 x ↦ₛ psmField7 x) ∗
          sliceCursorAt (sp' + 296#64) (cur7 x) (psmRem7 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          ((sp' + 432#64) ↦₃₂ 1#32) ∗ ((sp' + 436#64) ↦₃₂ x.kpkId) ∗ A.pool ∗
          stackAt sp' int32MergeStack))
      (tryFromQp s0) := by
  have hf7 := psmField7_eq x
  let body := encodeVarint (x.kpkId.zeroExtend 64)
  have hrem6 : psmRem6 x = 0x38#8 :: (body ++ psmRem7 x) := by
    rw [psmRem6, hf7, List.cons_append]
  have hlt_body : (body ++ psmRem7 x).length < 2 ^ 32 := by
    have hlen : (psmRem6 x).length = (body ++ psmRem7 x).length + 1 := by
      rw [hrem6, List.length_cons]
    omega
  have hsub1 : BitVec.ofNat 64 (psmRem6 x).length - 1#64 =
      BitVec.ofNat 64 (body ++ psmRem7 x).length := by
    rw [hrem6, ofNat64_cons_sub_one]
  have hrem7_ne : BitVec.ofNat 64 (psmRem7 x).length ≠ 0#64 :=
    ofNat64_length_ne_zero (psmRem7_ne_nil x) hlt7
  have hrem7_beq : (BitVec.ofNat 64 (psmRem7 x).length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hrem7_ne
  have hcall := int32Merge_ok_at_prekey hint32
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have hfn := libsignalSessionCode_fnOff_0x29c14
  responder_wire_fetches_from img.base H hfn 0x29c14 244 24
  responder_wire_fetches_from img.base H hfn 0x29c14 332 44
  responder_wire_fetches_from img.base H hfn 0x29c14 440 8
  responder_wire_fetches_from img.base H hfn 0x29c14 552 8
  responder_wire_fetches_from img.base H hfn 0x29c14 712 16
  responder_wire_fetches_from img.base H hfn 0x29c14 212 32
  clear hfn
  dsimp only [tripleRatchetProgAt] at hcall hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 244#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 244#64 at hpc
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 18446744073709391792#64) _
      at hcall
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hsp_eq := hregs.sp
  have h29 := hregs.x29
  have h28 := hregs.x28
  have h26 := hregs.x26
  have h25 := hregs.x25
  have h23 := hregs.x23
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (psmRem6 x).length := hx2
  have hpts : (cur6 x ↦ₛ psmRem6 x) =
      (cur6 x ↦₈ 0x38#8) ∗ ((cur6 x + 1#64) ↦ₛ (body ++ psmRem7 x)) := by
    rw [hrem6, pointsToBytes_cons]
  clear hrem6
  unfold sliceCursorAt
  rw [hpts]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 720#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  have hent1 := pointsTo32_memRegion4_entails_exists_pointsTo64 (sp' + 432#64) 0#32
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hent1
  refine SepWPp.mono_pre
    (P' := (∃∗ w : BitVec 64, (sp' + 432#64) ↦₆₄ w) ∗ ((cur6 x ↦₈ 0x38#8) ∗ ((cur6 x +
      1#64) ↦ₛ (body ++ psmRem7 x)) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 296#64) ↦₆₄ (cur6 x + 1#64)) ∗
        ((sp' + 304#64) ↦₆₄ BitVec.ofNat 64 (body ++ psmRem7 x).length) ∗ A.pool ∗
        stackAt sp' int32MergeStack))
    (by
      refine Entails.trans ?_ (sepConj_mono_left hent1)
      apply entails_of_eq; ac_rfl) ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_pre fun w432 => ?_
  refine SepWPp.of_sepWP_frozen hF1 hsym1 (mid := entry + 18446744073709391792#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF2 hsym2
  have hent2 := pointsTo64_one_entails_pointsTo32_memRegion4 (sp' + 432#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hent2
  refine SepWPp.mono_pre
    (P' := (((sp' + 432#64) ↦₃₂ 1#32) ∗ memRegion (sp' + 436#64) 4) ∗ ((cur6 x ↦₈ 0x38#8) ∗
      sliceCursorAt (sp' + 296#64) (cur6 x + 1#64) (body ++ psmRem7 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' +
        296#64)) ∗
      A.pool ∗ stackAt sp' int32MergeStack))
    (by
      unfold sliceCursorAt
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      refine Entails.trans ?_ (sepConj_mono_left hent2)
      apply entails_of_eq; ac_rfl) ?_
  simp only [sepConj_assoc]
  refine SepWPp.call_tryFrom
    ⟨.varint, sp' + 436#64, sp' + 440#64, sp' + 296#64, cur6 x + 1#64, body ++ psmRem7 x⟩
    hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF2 hsym2
    (ret_pc := entry + 224#64) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := memRegion (sp' + 436#64) 4 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) (cur6 x + 1#64) (body ++ psmRem7 x) ∗ A.pool ∗
        stackAt sp' int32MergeStack)
    (φ := (0#64 : BitVec 64).setWidth 8 = BitVec.ofNat 8 WireType.varint.toNat ∧ sp' + 312#64 +
      124#64 = sp' + 436#64 ∧
      sp' + 512#64 - 72#64 = sp' + 440#64 ∧ (body ++ psmRem7 x).length < 9223372036854775808)
    (by dsimp only [int32MergeSpec]; simp only [hsp_eq, arm64_norm])
    ⟨rfl, by bv_omega, by bv_omega, by omega⟩
    (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF3 hsym3 hcs2
  have hregs2 : PreKeyLoopRegs sp' x s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using h28, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using h26, by simpa [arm64_norm] using h25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      hsp2 hcs2
  have h29_2 := hregs2.x29
  dsimp only [int32MergeSpec]
  rw [merge_field7 x]
  dsimp only; rw [sepConj_assoc]; refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre fun hx0_2 => ?_
  have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hpost_cur :
      (cur6 x ↦₈ 0x38#8) ∗ sliceCursorAfter (sp' + 296#64) (cur6 x + 1#64) (body ++
        psmRem7 x) (psmRem7 x) =
      (cur6 x ↦ₛ psmField7 x) ∗ (((sp' + 296#64) ↦₆₄ cur7 x) ∗ (((sp' +
        304#64) ↦₆₄ BitVec.ofNat 64 (psmRem7 x).length) ∗
        (cur7 x ↦ₛ psmRem7 x))) := by
    rw [cons_sliceCursorAfter_split, ← hf7]
    unfold sliceCursorAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rfl
  refine SepWPp.mono_pre
    (P' := ((cur6 x ↦₈ 0x38#8) ∗ sliceCursorAfter (sp' + 296#64) (cur6 x + 1#64) (body ++
      psmRem7 x) (psmRem7 x)) ∗
      ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 432#64) ↦₃₂ 1#32) ∗ ((sp' +
        436#64) ↦₃₂ x.kpkId) ∗
      A.pool ∗ stackAt sp' int32MergeStack)
    (by
      simp only [hsp_eq, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  rw [hpost_cur]
  simp only [sepConj_assoc]
  refine SepWPp.of_sepWP_end hF3 hsym3 ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hF4 hsym4
  refine ⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x27,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x25,
    by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
    by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
    by simpa [arm64_norm] using hregs2.x19⟩,
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hF4, hsym4, by simpa [arm64_norm] using htr2.trans htr,
    by simp [arm64_norm], ?_⟩
  apply entails_of_eq; ac_rfl
/-- Field 8 and loop-exit step (`+0xf4 → +0x460`). -/
theorem step_field8_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hbytes : BytesMergeOk img C A ctl abs)
    {x : PreKeyTryFromArgs} {s0 s : State} {sp' : BitVec 64}
    (hlt7 : (psmRem7 x).length < 2 ^ 32)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 0xf4#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' x s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (psmRem7 x).length) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) (cur7 x) (psmRem7 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
      (fun s1 P1 =>
        PreKeyLoopRegs sp' x s1 ∧ s1.spAligned = true ∧ img.FrozenLoaded s1 ∧ s1.symtab =
        img.symtab ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x24 = 0#64 ∧ ∃ cap' ptr' : BitVec 64,
          P1 ⊢ (cur7 x ↦ₛ psmField8 x) ∗ sliceCursorAt (sp' + 296#64) (cur8 x) (psmRem8 x) ∗ ((sp' +
          440#64) ↦₆₄ (sp' + 296#64)) ∗
            vecU8At A (sp' + 312#64) cap' ptr' x.kyberBytes ∗ A.pool ∗ stackAt sp' bytesMergeStack)
      (tryFromQp s0) := by
  have hf8 := psmField8_eq x
  let body := encodeVarint 1569#64 ++ x.kyberBytes
  have hrem7 : psmRem7 x = 0x42#8 :: (body ++ psmRem8 x) := by
    rw [psmRem7, hf8, List.cons_append]
  have hlt_body : (body ++ psmRem8 x).length < 2 ^ 32 := by
    have hlen : (psmRem7 x).length = (body ++ psmRem8 x).length + 1 := by
      rw [hrem7, List.length_cons]
    omega
  have hsub1 : BitVec.ofNat 64 (psmRem7 x).length - 1#64 =
      BitVec.ofNat 64 (body ++ psmRem8 x).length := by
    rw [hrem7, ofNat64_cons_sub_one]
  have hrem8_len : BitVec.ofNat 64 (psmRem8 x).length = 0#64 := rfl
  have hcall := bytesMerge_ok_at_prekey hbytes
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have hfn := libsignalSessionCode_fnOff_0x29c14
  responder_wire_fetches_from img.base H hfn 0x29c14 244 24
  responder_wire_fetches_from img.base H hfn 0x29c14 332 44
  responder_wire_fetches_from img.base H hfn 0x29c14 440 8
  responder_wire_fetches_from img.base H hfn 0x29c14 552 52
  responder_wire_fetches_from img.base H hfn 0x29c14 228 16
  responder_wire_fetches_from img.base H hfn 0x29c14 768 8
  clear hfn
  dsimp only [tripleRatchetProgAt] at hcall hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 244#64 at hpc
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 18446744073709390708#64) _
      at hcall
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hsp_eq := hregs.sp
  have h29 := hregs.x29
  have h28 := hregs.x28
  have h26 := hregs.x26
  have h25 := hregs.x25
  have h23 := hregs.x23
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (psmRem7 x).length := hx2
  have hpts : (cur7 x ↦ₛ psmRem7 x) =
      (cur7 x ↦₈ 0x42#8) ∗ ((cur7 x + 1#64) ↦ₛ (body ++ psmRem8 x)) := by
    rw [hrem7, pointsToBytes_cons]
  clear hrem7
  have hmr16 := memRegion16_split8_8' (sp' + 320#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmr16
  refine SepWPp.mono_pre
    (P' := (∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        ((sp' + 320#64) ↦₆₄ w0) ∗ ((sp' + 328#64) ↦₆₄ w1)) ∗ (sliceCursorAt (sp' +
        296#64) (cur7 x) (psmRem7 x) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 312#64) ↦₆₄ noneCap) ∗ A.pool ∗
        stackAt sp' bytesMergeStack))
    (by
      refine Entails.trans ?_ (sepConj_mono_left hmr16)
      apply entails_of_eq; ac_rfl) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w2 => ?_
  unfold sliceCursorAt
  rw [hpts]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 18446744073709390708#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.mono_pre
    (P' := (cur7 x ↦₈ 0x42#8) ∗ vecU8At A (sp' + 312#64) 0#64 1#64 [] ∗ ((sp' + 440#64) ↦₆₄ (sp' +
      296#64)) ∗
      sliceCursorAt (sp' + 296#64) (cur7 x + 1#64) (body ++ psmRem8 x) ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
    (by
      rw [← pointsTo64_emptyVec_eq_vecU8At A sp' 312#64 320#64 328#64]
      unfold sliceCursorAt
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.call_tryFrom
    ⟨.lengthDelimited, sp' + 312#64, 0#64, 1#64, [], sp' + 440#64, sp' + 296#64,
      cur7 x + 1#64, body ++ psmRem8 x⟩
    hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + 600#64) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := vecU8At A (sp' + 312#64) 0#64 1#64 [] ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) (cur7 x + 1#64) (body ++ psmRem8 x) ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
    (φ := (2#64 : BitVec 64).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat ∧ sp' +
      512#64 - 200#64 = sp' + 312#64 ∧
      sp' + 512#64 - 72#64 = sp' + 440#64 ∧ (body ++ psmRem8 x).length < 9223372036854775808 ∧
      BytesMergeCapOk 0#64 (body ++ psmRem8 x).length)
    (by
      dsimp only [bytesMergeSpec, Spec.inImage]
      rw [pure_true_emp (And.intro hF1 hsym1), emp_sepConj]
      simp only [bytesMergeRawSpec, hsp_eq, arm64_norm])
    ⟨rfl, by bv_omega, by bv_omega, by omega, bytesMergeCapOk_of_len_lt32 hlt_body⟩
    (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  have hregs2 : PreKeyLoopRegs sp' x s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using h28, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using h26, by simpa [arm64_norm] using h25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      hsp2 hcs2
  have h29_2 := hregs2.x29
  dsimp only [bytesMergeSpec, Spec.inImage, bytesMergeRawSpec]; rw [merge_field8 x]
  dsimp only; rw [sepConj_assoc]; refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre fun hx0_2 => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
  refine SepWPp.exists_pre fun cap' => SepWPp.exists_pre fun ptr' => SepWPp.pure_pre fun _ => ?_
  have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hpost_cur :
      (cur7 x ↦₈ 0x42#8) ∗ sliceCursorAfter (sp' + 296#64) (cur7 x + 1#64) (body ++
        psmRem8 x) (psmRem8 x) =
      (cur7 x ↦ₛ psmField8 x) ∗ (((sp' + 296#64) ↦₆₄ cur8 x) ∗ (((sp' + 304#64) ↦₆₄ 0#64) ∗
        (cur8 x ↦ₛ psmRem8 x))) := by
    rw [cons_sliceCursorAfter_split, ← hf8]
    unfold sliceCursorAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rfl
  refine SepWPp.mono_pre
    (P' := ((cur7 x ↦₈ 0x42#8) ∗ sliceCursorAfter (sp' + 296#64) (cur7 x + 1#64) (body ++
      psmRem8 x) (psmRem8 x)) ∗
      ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ vecU8At A (sp' + 312#64) cap' ptr' x.kyberBytes ∗
        A.pool ∗ stackAt sp' bytesMergeStack)
    (by
      simp only [hsp_eq, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  rw [hpost_cur]; simp only [sepConj_assoc]; refine SepWPp.of_sepWP_end hF2 hsym2 ?_; wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hF3 hsym3
  refine ⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x27,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x25,
    by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
    by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
    by simpa [arm64_norm] using hregs2.x19⟩,
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hF3, hsym3, by simpa [arm64_norm] using htr2.trans htr,
    by simp [arm64_norm],
    cap', ptr', ?_⟩
  apply entails_of_eq; ac_rfl
/-! ## Entry-to-Post-Loop Composition (`0x29b30 → 0x29f90`) -/
theorem stackAt_bytesMerge_split_int32 (sp' : BitVec 64) :
    stackAt sp' bytesMergeStack =
      memRegion (sp' - BitVec.ofNat 64 bytesMergeStack) (bytesMergeStack - int32MergeStack) ∗
        stackAt sp' int32MergeStack :=
  stackAt_sub_split sp' int32MergeStack bytesMergeStack (by decide) (by decide)
set_option maxHeartbeats 1600000 in
theorem preKey_entry_to_f90_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hint32 : Int32MergeOk img.base C A ctl abs)
    (hbytes : BytesMergeOk img C A ctl abs)
    {x : PreKeyTryFromArgs} {s0 : State} {sp' : BitVec 64}
    (hsp' : sp' = s0.sp - 608#64)
    (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hF : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab)
    (hx0 : s0.readReg64 .x0 = x.ptr)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.sret) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 0x460#64) s0
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion (sp' + 296#64) 152 ∗ memRegion (sp' + 512#64) 96 ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
      (fun sf Pf =>
        PreKeyLoopRegs sp' x sf ∧ sf.spAligned = true ∧ img.FrozenLoaded sf ∧ sf.symtab =
        img.symtab ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x24 = 0#64 ∧
        ∃ (opkVal : BitVec 32) (kyberCap kyberPtr bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec
        64),
          (∀ v, x.opkId = some v → opkVal = v) ∧ (Pf ⊢ (x.ptr ↦ₛ x.bytes) ∗ ((sp' +
          296#64) ↦₆₄ cur8 x) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
            vecU8At A (sp' + 312#64) kyberCap kyberPtr x.kyberBytes ∗ vecU8At A (sp' +
            336#64) bkCap bkPtr x.bkBytes ∗
            vecU8At A (sp' + 360#64) ikCap ikPtr x.ikBytes ∗ vecU8At A (sp' +
            384#64) msgCap msgPtr x.inner ∗
            ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗ ((sp' +
            416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
            ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗ ((sp' + 432#64) ↦₃₂ 1#32) ∗
            ((sp' + 436#64) ↦₃₂ x.kpkId) ∗
            ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ preKeyCalleeSavedAt sp' s0 ∗ A.pool ∗
            stackAt sp' bytesMergeStack))
      (tryFromQp s0) := by
  rcases psmRem_lengths_lt x hlt with ⟨_, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt_in⟩
  refine SepWPp.mono_pre
    (P' := ((x.ptr ↦ₛ x.bytes) ∗ memRegion (sp' + 296#64) 152 ∗ memRegion (sp' + 512#64) 96) ∗
      (A.pool ∗ stackAt sp' bytesMergeStack))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (hsp' ▸ prologue_to_c24_wp ctl hlt hpc hrun hsp hF hsym hx0 hx1 hx8) ?_
  intro s1 P1 hpc1 hrun1 ⟨hregs1, hsp1, hF1, hsym1, htr1, hx2_1, hent1⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent1) ?_
  clear hent1
  refine SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur0 x) (psmRem0 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' +
      296#64)) ∗
        ((sp' + 416#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 420#64) 4 ∗ A.pool ∗
        stackAt sp' int32MergeStack) ∗ ((x.ptr ↦₈ 0x44#8) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗ ((sp' + 336#64) ↦₆₄ noneCap) ∗
        memRegion (sp' + 344#64) 16 ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗ ((sp' + 384#64) ↦₆₄ noneCap) ∗
        memRegion (sp' + 392#64) 16 ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗ ((sp' + 424#64) ↦₃₂ 0#32) ∗
        memRegion (sp' + 428#64) 4 ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗
        preKeyCalleeSavedAt sp' s0 ∗ memRegion (sp' -
        BitVec.ofNat 64 bytesMergeStack) (bytesMergeStack - int32MergeStack)))
    (by apply entails_of_eq; rw [stackAt_bytesMerge_split_int32 sp']; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (step_field1_wp ctl hint32 hlt0 hlt1 hpc1 hrun1 hregs1 hsp1 hF1 hsym1 htr1 hx2_1) ?_
  intro s2 P2 hpc2 hrun2 ⟨hregs2, hsp2, hF2, hsym2, htr2, hx2_2, opkVal, hopkVal, hent2⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent2) ?_
  clear hent2
  refine SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur1 x) (psmRem1 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' +
      296#64)) ∗
        ((sp' + 336#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 344#64) 16 ∗ A.pool ∗
        stackAt sp' bytesMergeStack) ∗
      ((x.ptr ↦₈ 0x44#8) ∗ (cur0 x ↦ₛ psmField1 x) ∗ ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' +
        320#64) 16 ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗ ((sp' + 384#64) ↦₆₄ noneCap) ∗
        memRegion (sp' + 392#64) 16 ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗ ((sp' + 416#64) ↦₃₂ opkTag x) ∗
        ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗ ((sp' + 432#64) ↦₃₂ 0#32) ∗
        memRegion (sp' + 436#64) 4 ∗
        preKeyCalleeSavedAt sp' s0))
    (by apply entails_of_eq; rw [stackAt_bytesMerge_split_int32 sp']; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (step_field2_wp hbytes hlt1 hlt2 hpc2 hrun2 hregs2 hsp2 hF2 hsym2 htr2 hx2_2) ?_
  intro s3 P3 hpc3 hrun3 ⟨hregs3, hsp3, hF3, hsym3, htr3, hx2_3, bkCap, bkPtr, hent3⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent3) ?_
  clear hent3
  refine SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur2 x) (psmRem2 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' +
      296#64)) ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗ A.pool ∗
        stackAt sp' bytesMergeStack) ∗
      ((x.ptr ↦₈ 0x44#8) ∗ (cur0 x ↦ₛ psmField1 x) ∗ (cur1 x ↦ₛ psmField2 x) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗ vecU8At A (sp' +
        336#64) bkCap bkPtr x.bkBytes ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗ ((sp' + 408#64) ↦₃₂ 0#32) ∗
        memRegion (sp' + 412#64) 4 ∗
        ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗ ((sp' + 424#64) ↦₃₂ 0#32) ∗
        memRegion (sp' + 428#64) 4 ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗ preKeyCalleeSavedAt sp' s0))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (step_field3_wp hbytes hlt2 hlt3 hpc3 hrun3 hregs3 hsp3 hF3 hsym3 htr3 hx2_3) ?_
  intro s4 P4 hpc4 hrun4 ⟨hregs4, hsp4, hF4, hsym4, htr4, hx2_4, ikCap, ikPtr, hent4⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent4) ?_
  clear hent4
  refine SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur3 x) (psmRem3 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' +
      296#64)) ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗ A.pool ∗
        stackAt sp' bytesMergeStack) ∗
      ((x.ptr ↦₈ 0x44#8) ∗ (cur0 x ↦ₛ psmField1 x) ∗ (cur1 x ↦ₛ psmField2 x) ∗
        (cur2 x ↦ₛ psmField3 x) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗ vecU8At A (sp' +
        336#64) bkCap bkPtr x.bkBytes ∗
        vecU8At A (sp' + 360#64) ikCap ikPtr x.ikBytes ∗ ((sp' + 408#64) ↦₃₂ 0#32) ∗
        memRegion (sp' + 412#64) 4 ∗
        ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗ ((sp' + 424#64) ↦₃₂ 0#32) ∗
        memRegion (sp' + 428#64) 4 ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗ preKeyCalleeSavedAt sp' s0))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (step_field4_wp hbytes hlt_in hlt3 hlt4 hpc4 hrun4 hregs4 hsp4 hF4 hsym4 htr4 hx2_4) ?_
  intro s5 P5 hpc5 hrun5 ⟨hregs5, hsp5, hF5, hsym5, htr5, hx2_5, msgCap, msgPtr, hent5⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent5) ?_
  clear hent5
  refine SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur4 x) (psmRem4 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' +
      296#64)) ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗ A.pool ∗
        stackAt sp' int32MergeStack) ∗
      ((x.ptr ↦₈ 0x44#8) ∗ (cur0 x ↦ₛ psmField1 x) ∗ (cur1 x ↦ₛ psmField2 x) ∗
        (cur2 x ↦ₛ psmField3 x) ∗ (cur3 x ↦ₛ psmField4 x) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗ vecU8At A (sp' +
        336#64) bkCap bkPtr x.bkBytes ∗
        vecU8At A (sp' + 360#64) ikCap ikPtr x.ikBytes ∗ vecU8At A (sp' +
        384#64) msgCap msgPtr x.inner ∗
        ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗ ((sp' + 424#64) ↦₃₂ 0#32) ∗
        memRegion (sp' + 428#64) 4 ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗
        preKeyCalleeSavedAt sp' s0 ∗ memRegion (sp' -
        BitVec.ofNat 64 bytesMergeStack) (bytesMergeStack - int32MergeStack)))
    (by apply entails_of_eq; rw [stackAt_bytesMerge_split_int32 sp']; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (step_field5_wp hint32 hlt4 hlt5 hpc5 hrun5 hregs5 hsp5 hF5 hsym5 htr5 hx2_5) ?_
  intro s6 P6 hpc6 hrun6 ⟨hregs6, hsp6, hF6, hsym6, htr6, hx2_6, hent6⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent6) ?_
  clear hent6
  refine SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur5 x) (psmRem5 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' +
      296#64)) ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗ A.pool ∗
        stackAt sp' int32MergeStack) ∗
      ((x.ptr ↦₈ 0x44#8) ∗ (cur0 x ↦ₛ psmField1 x) ∗ (cur1 x ↦ₛ psmField2 x) ∗
        (cur2 x ↦ₛ psmField3 x) ∗ (cur3 x ↦ₛ psmField4 x) ∗ (cur4 x ↦ₛ psmField5 x) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗ vecU8At A (sp' +
        336#64) bkCap bkPtr x.bkBytes ∗
        vecU8At A (sp' + 360#64) ikCap ikPtr x.ikBytes ∗ vecU8At A (sp' +
        384#64) msgCap msgPtr x.inner ∗
        ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗ ((sp' + 416#64) ↦₃₂ opkTag x) ∗
        ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗
        preKeyCalleeSavedAt sp' s0 ∗ memRegion (sp' -
        BitVec.ofNat 64 bytesMergeStack) (bytesMergeStack - int32MergeStack)))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (step_field6_wp hint32 hlt5 hlt6 hpc6 hrun6 hregs6 hsp6 hF6 hsym6 htr6 hx2_6) ?_
  intro s7 P7 hpc7 hrun7 ⟨hregs7, hsp7, hF7, hsym7, htr7, hx2_7, hent7⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent7) ?_
  clear hent7
  refine SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur6 x) (psmRem6 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' +
      296#64)) ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗ A.pool ∗
        stackAt sp' int32MergeStack) ∗
      ((x.ptr ↦₈ 0x44#8) ∗ (cur0 x ↦ₛ psmField1 x) ∗ (cur1 x ↦ₛ psmField2 x) ∗
        (cur2 x ↦ₛ psmField3 x) ∗ (cur3 x ↦ₛ psmField4 x) ∗ (cur4 x ↦ₛ psmField5 x) ∗
        (cur5 x ↦ₛ psmField6 x) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗ vecU8At A (sp' +
        336#64) bkCap bkPtr x.bkBytes ∗
        vecU8At A (sp' + 360#64) ikCap ikPtr x.ikBytes ∗ vecU8At A (sp' +
        384#64) msgCap msgPtr x.inner ∗
        ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗ ((sp' + 416#64) ↦₃₂ opkTag x) ∗
        ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗
        preKeyCalleeSavedAt sp' s0 ∗ memRegion (sp' -
        BitVec.ofNat 64 bytesMergeStack) (bytesMergeStack - int32MergeStack)))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (step_field7_wp hint32 hlt6 hlt7 hpc7 hrun7 hregs7 hsp7 hF7 hsym7 htr7 hx2_7) ?_
  intro s8 P8 hpc8 hrun8 ⟨hregs8, hsp8, hF8, hsym8, htr8, hx2_8, hent8⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent8) ?_
  clear hent8
  refine SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur7 x) (psmRem7 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' +
      296#64)) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗ A.pool ∗
        stackAt sp' bytesMergeStack) ∗
      ((x.ptr ↦₈ 0x44#8) ∗ (cur0 x ↦ₛ psmField1 x) ∗ (cur1 x ↦ₛ psmField2 x) ∗
        (cur2 x ↦ₛ psmField3 x) ∗ (cur3 x ↦ₛ psmField4 x) ∗ (cur4 x ↦ₛ psmField5 x) ∗
        (cur5 x ↦ₛ psmField6 x) ∗ (cur6 x ↦ₛ psmField7 x) ∗ vecU8At A (sp' +
        336#64) bkCap bkPtr x.bkBytes ∗
        vecU8At A (sp' + 360#64) ikCap ikPtr x.ikBytes ∗ vecU8At A (sp' +
        384#64) msgCap msgPtr x.inner ∗
        ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗ ((sp' + 416#64) ↦₃₂ opkTag x) ∗
        ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗ ((sp' + 432#64) ↦₃₂ 1#32) ∗
        ((sp' + 436#64) ↦₃₂ x.kpkId) ∗
        preKeyCalleeSavedAt sp' s0))
    (by apply entails_of_eq; rw [stackAt_bytesMerge_split_int32 sp']; ac_rfl) ?_
  refine SepWPp.frame_tryFrom
    (step_field8_wp hbytes hlt7 hpc8 hrun8 hregs8 hsp8 hF8 hsym8 htr8 hx2_8)
    fun sf Pf ⟨hregsf, hspf, hFf, hsymf, htrf, hx24f, kyberCap, kyberPtr, hentf⟩ =>
      ⟨hregsf, hspf, hFf, hsymf, htrf, hx24f,
        opkVal, kyberCap, kyberPtr, bkCap, bkPtr, ikCap, ikPtr, msgCap, msgPtr, hopkVal, ?_⟩
  refine Entails.trans (sepConj_mono_left hentf) ?_
  have hcur8 : sliceCursorAt (sp' + 296#64) (cur8 x) (psmRem8 x) =
      ((sp' + 296#64) ↦₆₄ cur8 x) ∗ ((sp' + 304#64) ↦₆₄ 0#64) := by
    unfold sliceCursorAt psmRem8
    simp only [List.length_nil, pointsToBytes_nil,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
  rw [hcur8, ← pointsToBytes_psm_reassemble x]
  apply entails_of_eq; ac_rfl

/-! ## Relocatable `[LibsignalPlacement]` Entry-to-Post-Loop (Block `111`) -/

theorem SepWPp.of_sepWP_lscl [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s : Arm64.State} {P : SepProp} {Q Qp : Arm64.State → SepProp → Prop}
    {mid : BitVec 64}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : ProofLib.SepWP prog mid s P (fun sm Pm =>
      VRegsAt s sm ∧
      (LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp prog ret sm Pm Q Qp))) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hv, hnext⟩ | hoom⟩
  · have hcl_m := hcl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', ⟨hpc, hrun, Pf, hmf, hq, hvf⟩ | hpan⟩ :=
      hnext hcl_m R hmm (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpc, hrun, Pf, hmf, hq, hvf.trans hv.eq⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr hpan⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem SepWPp.of_sepWP_end_lscl [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s0 s : Arm64.State} {P : SepProp} {Q : Arm64.State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : ProofLib.SepWP prog ret s P (fun sf Pf =>
      VRegsAt s sf ∧
      (LibsignalCodeLoaded lsmpl sf.mem → Q sf Pf))) :
    SepWPp prog ret s P Q (tryFromQp s0) := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hv, hq⟩ | ⟨_, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf,
      hq (hcl.of_keepsFrozen hsteps.keepsFrozen), hv.eq⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem SepWPp.call_tryFrom_lscl [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {s0 s : Arm64.State} {P T F : SepProp} {φ : Prop}
    {Q : Arm64.State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F := by sep_focus)
    (hnext : ∀ sf : Arm64.State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      sf.spAligned = true → LibsignalCodeLoaded lsmpl sf.mem →
      CalleeSavedPreserved s sf → SepWPp prog ret sf (spec.post x s sf ∗ F) Q (tryFromQp s0))
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) :=
      by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q (tryFromQp s0) := by
  intro R' hm hL
  have hpre : s.mem ⊨ (withLsCodeLoaded lsmpl spec).pre x s ∗ (F ∗ R') := by
    dsimp only [withLsCodeLoaded]
    rw [hspec]
    have hcomm : ((⌜φ⌝ ∗ T) ∗ ⌜LibsignalCodeLoaded lsmpl s.mem⌝) ∗ (F ∗ R') =
        ⌜φ⌝ ∗ (⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗ ((T ∗ F) ∗ R')) := by ac_rfl
    rw [hcomm, satisfies_pure_sepConj]
    refine ⟨hφ, ?_⟩
    rw [satisfies_pure_sepConj, ← hP]
    exact ⟨hcl, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hoom⟩
  · dsimp only [withLsCodeLoaded] at hpost
    rw [← sepConj_assoc] at hpost; rw [hlr] at hpcm
    have hspm_align : sm.spAligned = true := by
      rw [Arm64.State.spAligned, hspm, ← Arm64.State.spAligned]; exact hsp
    have hclm := hcl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hqf, hvf⟩ | hpanf⟩ :=
      hnext sm hpcm hrunm hspm hspm_align hclm hcsm R' hpost (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps',
        Or.inl ⟨hpcf, hrunf, Pf, hmf, hqf, hvf.trans hcsm.2.2.2.2.2.2.2.2.2.2.2⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr hpanf⟩
  · dsimp only [withLsCodeLoaded] at hpost
    rw [← sepConj_assoc, hpan sm] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost, tryFromQp_of_call htr⟩)⟩
  · dsimp only [withLsCodeLoaded] at hpost
    rw [hexit sm code] at hpost; exact (allowPanic_not_exited hpost).elim
  · dsimp only [withLsCodeLoaded] at hoom
    rw [hoom_eq sm] at hoom; exact (not_satisfies_false_sepConj hoom).elim

theorem prologue_to_c24_placed_wp [LibsignalPlacement] {H : LibsignalHooks}
    {x : PreKeyTryFromArgs} {s0 : State}
    (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (blkPl_111).base)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (hx0 : s0.readReg64 .x0 = x.ptr)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length) (hx8 : s0.readReg64 .x8 = x.sret) :
    SepWPp ((blkPC_111).rebase (blkPl_111).base H)
      ((blkPl_111).base + 0xf4#64) s0
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion (s0.sp - 608#64 + 296#64) 152 ∗ memRegion (s0.sp - 608#64 +
        512#64) 96)
      (fun s1 P1 =>
        PreKeyLoopRegs (s0.sp - 608#64) x s1 ∧ s1.spAligned = true ∧
        LibsignalCodeLoaded lsmpl s1.mem ∧
        s1.trace = s0.trace ∧ s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem0 x).length ∧
        (P1 ⊢ (x.ptr ↦₈ 0x44#8) ∗
          sliceCursorAt (s0.sp - 608#64 + 296#64) (cur0 x) (psmRem0 x) ∗ ((s0.sp - 608#64 +
          440#64) ↦₆₄ (s0.sp - 608#64 + 296#64)) ∗
          ((s0.sp - 608#64 + 312#64) ↦₆₄ noneCap) ∗ memRegion (s0.sp - 608#64 + 320#64) 16 ∗
          ((s0.sp - 608#64 + 336#64) ↦₆₄ noneCap) ∗ memRegion (s0.sp - 608#64 + 344#64) 16 ∗
          ((s0.sp - 608#64 + 360#64) ↦₆₄ noneCap) ∗ memRegion (s0.sp - 608#64 + 368#64) 16 ∗
          ((s0.sp - 608#64 + 384#64) ↦₆₄ noneCap) ∗ memRegion (s0.sp - 608#64 + 392#64) 16 ∗
          ((s0.sp - 608#64 + 408#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 608#64 + 412#64) 4 ∗
          ((s0.sp - 608#64 + 416#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 608#64 + 420#64) 4 ∗
          ((s0.sp - 608#64 + 424#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 608#64 + 428#64) 4 ∗
          ((s0.sp - 608#64 + 432#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 608#64 + 436#64) 4 ∗
          preKeyCalleeSavedAt (s0.sp - 608#64) s0))
      (tryFromQp s0) := by
  have hb := bytes_eq_cons_psmRem0 x
  have hge2 : 2 ≤ x.bytes.length := by
    have hrem0 := List.length_pos_of_ne_nil (psmRem0_ne_nil x)
    rw [hb, List.length_cons]; omega
  have hlen_ne : BitVec.ofNat 64 x.bytes.length ≠ 0#64 :=
    ofNat64_length_ne_zero (by rw [hb]; simp) hlt
  have hlen_beq : (BitVec.ofNat 64 x.bytes.length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hlen_ne
  have hcond_eq := cond_eq_subs1_false hge2 hlt
  have hsub1 : BitVec.ofNat 64 x.bytes.length - 1#64 = BitVec.ofNat 64 (psmRem0 x).length := by
    rw [hb, ofNat64_cons_sub_one]
  have hbytes : (x.ptr ↦ₛ x.bytes) = (x.ptr ↦₈ 0x44#8) ∗ ((x.ptr + 1#64) ↦ₛ psmRem0 x) := by
    rw [hb, pointsToBytes_cons]
  clear hb
  rw [hbytes]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono (memRegion152_init_cells (s0.sp - 608#64))
        (memRegion96_split_preKeyCalleeSaved (s0.sp - 608#64)))) ?_
  simp only [bv_sub_add_lit', BitVec.reduceSub,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun w19 => SepWPp.exists_pre fun w20 =>
    SepWPp.exists_pre fun w21 => SepWPp.exists_pre fun w22 =>
    SepWPp.exists_pre fun w23 => SepWPp.exists_pre fun w24 =>
    SepWPp.exists_pre fun w25 => SepWPp.exists_pre fun w26 =>
    SepWPp.exists_pre fun w27 => SepWPp.exists_pre fun w28 =>
    SepWPp.exists_pre fun w30 => SepWPp.exists_pre fun w29 =>
    SepWPp.exists_pre fun w440 =>
    SepWPp.exists_pre fun w432 => SepWPp.exists_pre fun w424 =>
    SepWPp.exists_pre fun w416 => SepWPp.exists_pre fun w408 =>
    SepWPp.exists_pre fun w384 => SepWPp.exists_pre fun w360 =>
    SepWPp.exists_pre fun w336 => SepWPp.exists_pre fun w312 =>
    SepWPp.exists_pre fun c1 => SepWPp.exists_pre fun c0 => ?_
  refine SepWPp.of_sepWP_end_lscl hcl ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  refine ⟨⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩, ?_, hcl1,
    by simp [arm64_norm],
    by simp [arm64_norm], ?_⟩
  · rw [State.spAligned]
    simpa [arm64_norm] using spAligned_sub608 hsp
  · unfold sliceCursorAt preKeyCalleeSavedAt cur0 noneCap
    simp only [arm64_norm]
    apply entails_of_eq; ac_rfl

theorem step_field1_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hint32 : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H)
      (lsmpl.base 8) (withLsCodeLoaded lsmpl (int32MergeSpec A)))
    {x : PreKeyTryFromArgs} {s0 s : State} {sp' : BitVec 64} (hlt0 : (psmRem0 x).length < 2 ^ 32)
    (hlt1 : (psmRem1 x).length < 2 ^ 32)
    (hpc : s.pc = (blkPl_111).base + 0xf4#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' x s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (psmRem0 x).length) :
    SepWPp ((blkPC_111).rebase (blkPl_111).base H)
      ((blkPl_111).base + 0xf4#64) s
      (sliceCursorAt (sp' + 296#64) (cur0 x) (psmRem0 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 416#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 420#64) 4 ∗ A.pool ∗
        stackAt sp' int32MergeStack)
      (fun s1 P1 =>
        PreKeyLoopRegs sp' x s1 ∧ s1.spAligned = true ∧ LibsignalCodeLoaded lsmpl s1.mem ∧
        s1.trace = s0.trace ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem1 x).length ∧ ∃ opkVal : BitVec 32, (∀ v,
        x.opkId = some v → opkVal = v) ∧
          (P1 ⊢ (cur0 x ↦ₛ psmField1 x) ∗ sliceCursorAt (sp' + 296#64) (cur1 x) (psmRem1 x) ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
            ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗ A.pool ∗
            stackAt sp' int32MergeStack))
      (tryFromQp s0) := by
  cases hopk : x.opkId with
  | none =>
    have hf1 : psmField1 x = [] := by simp [psmField1, hopk, Prost.uint32Field]
    have hrem0 : psmRem0 x = psmRem1 x := by simp [psmRem0, hf1]
    have hcur1 : cur1 x = cur0 x := by simp [cur1, hf1]
    rw [memRegion_four (sp' + 420#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_pre fun w420 => ?_
    refine SepWPp.of_sepWP_end_lscl hcl ?_
    refine SepWP.done hpc hrun ?_
    intro hcl1
    refine ⟨hregs, hsp, hcl1, htr, by rw [← hrem0]; exact hx2,
      w420, fun _ h => by simp at h, ?_⟩
    simp only [opkTag, hopk, hf1, hcur1, hrem0, pointsToBytes_nil, emp_sepConj]
    apply entails_of_eq; ac_rfl
  | some v =>
    have hf1 := psmField1_some x v hopk
    let body := encodeVarint (v.zeroExtend 64)
    have hrem0 : psmRem0 x = 0x08#8 :: (body ++ psmRem1 x) := by rw [psmRem0, hf1, List.cons_append]
    have hlt_body : (body ++ psmRem1 x).length < 2 ^ 32 := by
      rw [hrem0, List.length_cons] at hlt0; omega
    have hsub1 : BitVec.ofNat 64 (psmRem0 x).length - 1#64 =
        BitVec.ofNat 64 (body ++ psmRem1 x).length := by
      rw [hrem0, ofNat64_cons_sub_one]
    have hrem1_ne : BitVec.ofNat 64 (psmRem1 x).length ≠ 0#64 :=
      ofNat64_length_ne_zero (psmRem1_ne_nil x) hlt1
    have hrem1_beq : (BitVec.ofNat 64 (psmRem1 x).length == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hrem1_ne
    have hsp_eq := hregs.sp
    have h29 := hregs.x29
    have h28 := hregs.x28
    have h26 := hregs.x26
    have h25 := hregs.x25
    have h23 := hregs.x23
    have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (psmRem0 x).length := hx2
    have hpts : (cur0 x ↦ₛ psmRem0 x) =
        (cur0 x ↦₈ 0x08#8) ∗ ((cur0 x + 1#64) ↦ₛ (body ++ psmRem1 x)) := by
      rw [hrem0, pointsToBytes_cons]
    clear hrem0
    unfold sliceCursorAt
    rw [hpts]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine SepWPp.of_sepWP_lscl hcl (mid := (blkPl_111).base + 616#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcl1
    have hent1 := pointsTo32_memRegion4_entails_exists_pointsTo64 (sp' + 416#64) 0#32
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hent1
    refine SepWPp.mono_pre
      (P' := (∃∗ w : BitVec 64, (sp' + 416#64) ↦₆₄ w) ∗ ((cur0 x ↦₈ 0x08#8) ∗ ((cur0 x +
        1#64) ↦ₛ (body ++ psmRem1 x)) ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 296#64) ↦₆₄ (cur0 x + 1#64)) ∗
          ((sp' + 304#64) ↦₆₄ BitVec.ofNat 64 (body ++ psmRem1 x).length) ∗ A.pool ∗
          stackAt sp' int32MergeStack))
      (by
        refine Entails.trans ?_ (sepConj_mono_left hent1)
        apply entails_of_eq; ac_rfl) ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_pre fun w416 => ?_
    refine SepWPp.of_sepWP_lscl hcl1 (mid := lsmpl.base 8) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcl2
    have hent2 := pointsTo64_one_entails_pointsTo32_memRegion4 (sp' + 416#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hent2
    refine SepWPp.mono_pre
      (P' := (((sp' + 416#64) ↦₃₂ 1#32) ∗ memRegion (sp' + 420#64) 4) ∗ ((cur0 x ↦₈ 0x08#8) ∗
        sliceCursorAt (sp' + 296#64) (cur0 x + 1#64) (body ++ psmRem1 x) ∗ ((sp' +
        440#64) ↦₆₄ (sp' + 296#64)) ∗ A.pool ∗ stackAt sp' int32MergeStack))
      (by
        unfold sliceCursorAt
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        refine Entails.trans ?_ (sepConj_mono_left hent2)
        apply entails_of_eq; ac_rfl) ?_
    simp only [sepConj_assoc]
    refine SepWPp.call_tryFrom_lscl
      ⟨.varint, sp' + 420#64, sp' + 440#64, sp' + 296#64, cur0 x + 1#64, body ++ psmRem1 x⟩
      hint32
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl2
      (ret_pc := (blkPl_111).base + 632#64) (by simp [arm64_norm])
      (by simpa [arm64_norm] using htr)
      (T := memRegion (sp' + 420#64) 4 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        sliceCursorAt (sp' + 296#64) (cur0 x + 1#64) (body ++ psmRem1 x) ∗ A.pool ∗
        stackAt sp' int32MergeStack)
      (φ := (0#64 : BitVec 64).setWidth 8 = BitVec.ofNat 8 WireType.varint.toNat ∧ sp' + 312#64 +
        108#64 = sp' + 420#64 ∧
        sp' + 512#64 - 72#64 = sp' + 440#64 ∧ (body ++ psmRem1 x).length < 9223372036854775808)
      (by dsimp only [int32MergeSpec]; simp only [hsp_eq, arm64_norm])
      ⟨rfl, by bv_omega, by bv_omega, by omega⟩
      (by sep_focus)
      ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
    have hregs2 : PreKeyLoopRegs sp' x s2 := PreKeyLoopRegs.of_calleeSaved
        ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
         by simpa [arm64_norm] using h28, by simpa [arm64_norm] using hregs.x27,
         by simpa [arm64_norm] using h26, by simpa [arm64_norm] using h25,
         by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19⟩
        hsp2 hcs2
    have h29_2 := hregs2.x29
    dsimp only [int32MergeSpec]
    rw [merge_field1_some x v]
    dsimp only
    rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hx0_2 => ?_
    have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    have hpost_cur :
        (cur0 x ↦₈ 0x08#8) ∗ sliceCursorAfter (sp' + 296#64) (cur0 x + 1#64) (body ++
        psmRem1 x) (psmRem1 x) = (cur0 x ↦ₛ psmField1 x) ∗ (((sp' + 296#64) ↦₆₄ cur1 x) ∗ (((sp' +
        304#64) ↦₆₄ BitVec.ofNat 64 (psmRem1 x).length) ∗ (cur1 x ↦ₛ psmRem1 x))) := by
      rw [cons_sliceCursorAfter_split, ← hf1]
      unfold sliceCursorAt
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rfl
    refine SepWPp.mono_pre
      (P' := ((cur0 x ↦₈ 0x08#8) ∗ sliceCursorAfter (sp' + 296#64) (cur0 x + 1#64) (body ++
        psmRem1 x) (psmRem1 x)) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 416#64) ↦₃₂ 1#32) ∗ ((sp' + 420#64) ↦₃₂ v) ∗
        A.pool ∗ stackAt sp' int32MergeStack)
      (by
        simp only [hsp_eq, arm64_norm]
        apply entails_of_eq; ac_rfl) ?_
    rw [hpost_cur]
    simp only [sepConj_assoc]
    refine SepWPp.of_sepWP_end_lscl hcl3 ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    intro hcl4
    refine ⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
      by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x27,
      by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x25,
      by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
      by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
      by simpa [arm64_norm] using hregs2.x19⟩,
      by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
      hcl4, by simpa [arm64_norm] using htr2.trans htr,
      by simp [arm64_norm], v, fun v' hv' => Option.some.inj hv', ?_⟩
    simp only [opkTag, hopk]
    apply entails_of_eq; ac_rfl

theorem step_field2_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hbytes : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H)
      (lsmpl.base 7) (withLsCodeLoaded lsmpl (bytesMergeRawSpec A)))
    {x : PreKeyTryFromArgs} {s0 s : State} {sp' : BitVec 64}
    (hlt1 : (psmRem1 x).length < 2 ^ 32) (hlt2 : (psmRem2 x).length < 2 ^ 32)
    (hpc : s.pc = (blkPl_111).base + 0xf4#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' x s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (psmRem1 x).length) :
    SepWPp ((blkPC_111).rebase (blkPl_111).base H)
      ((blkPl_111).base + 0xf4#64) s
      (sliceCursorAt (sp' + 296#64) (cur1 x) (psmRem1 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 336#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 344#64) 16 ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
      (fun s1 P1 =>
        PreKeyLoopRegs sp' x s1 ∧ s1.spAligned = true ∧ LibsignalCodeLoaded lsmpl s1.mem ∧
        s1.trace = s0.trace ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem2 x).length ∧ ∃ cap' ptr' : BitVec 64,
          P1 ⊢ (cur1 x ↦ₛ psmField2 x) ∗ sliceCursorAt (sp' + 296#64) (cur2 x) (psmRem2 x) ∗ ((sp' +
          440#64) ↦₆₄ (sp' + 296#64)) ∗
            vecU8At A (sp' + 336#64) cap' ptr' x.bkBytes ∗ A.pool ∗ stackAt sp' bytesMergeStack)
      (tryFromQp s0) := by
  have hf2 := psmField2_eq x
  let body := encodeVarint 33#64 ++ x.bkBytes
  have hrem1 : psmRem1 x = 0x12#8 :: (body ++ psmRem2 x) := by rw [psmRem1, hf2, List.cons_append]
  have hlt_body : (body ++ psmRem2 x).length < 2 ^ 32 := by
    have hlen : (psmRem1 x).length = (body ++ psmRem2 x).length + 1 := by
      rw [hrem1, List.length_cons]
    omega
  have hsub1 : BitVec.ofNat 64 (psmRem1 x).length - 1#64 =
      BitVec.ofNat 64 (body ++ psmRem2 x).length := by
    rw [hrem1, ofNat64_cons_sub_one]
  have hrem2_ne : BitVec.ofNat 64 (psmRem2 x).length ≠ 0#64 :=
    ofNat64_length_ne_zero (psmRem2_ne_nil x) hlt2
  have hrem2_beq : (BitVec.ofNat 64 (psmRem2 x).length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hrem2_ne
  have hsp_eq := hregs.sp
  have h29 := hregs.x29
  have h28 := hregs.x28
  have h26 := hregs.x26
  have h25 := hregs.x25
  have h23 := hregs.x23
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (psmRem1 x).length := hx2
  have hpts : (cur1 x ↦ₛ psmRem1 x) =
      (cur1 x ↦₈ 0x12#8) ∗ ((cur1 x + 1#64) ↦ₛ (body ++ psmRem2 x)) := by
    rw [hrem1, pointsToBytes_cons]
  clear hrem1
  have hmr16 := memRegion16_split8_8' (sp' + 344#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmr16
  refine SepWPp.mono_pre
    (P' := (∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        ((sp' + 344#64) ↦₆₄ w0) ∗ ((sp' + 352#64) ↦₆₄ w1)) ∗ (sliceCursorAt (sp' +
        296#64) (cur1 x) (psmRem1 x) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 336#64) ↦₆₄ noneCap) ∗ A.pool ∗
        stackAt sp' bytesMergeStack))
    (by
      refine Entails.trans ?_ (sepConj_mono_left hmr16)
      apply entails_of_eq; ac_rfl) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w2 => ?_
  unfold sliceCursorAt
  rw [hpts]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_lscl hcl (mid := lsmpl.base 7) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  refine SepWPp.mono_pre
    (P' := (cur1 x ↦₈ 0x12#8) ∗ vecU8At A (sp' + 336#64) 0#64 1#64 [] ∗ ((sp' + 440#64) ↦₆₄ (sp' +
      296#64)) ∗ sliceCursorAt (sp' + 296#64) (cur1 x + 1#64) (body ++ psmRem2 x) ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
    (by
      rw [← pointsTo64_emptyVec_eq_vecU8At A sp' 336#64 344#64 352#64]
      unfold sliceCursorAt
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.call_tryFrom_lscl
    ⟨.lengthDelimited, sp' + 336#64, 0#64, 1#64, [], sp' + 440#64, sp' + 296#64,
      cur1 x + 1#64, body ++ psmRem2 x⟩
    hbytes (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_111).base + 432#64) (by simp [arm64_norm]) (by simpa [arm64_norm] using htr)
    (T := vecU8At A (sp' + 336#64) 0#64 1#64 [] ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) (cur1 x + 1#64) (body ++ psmRem2 x) ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
    (φ := (2#64 : BitVec 64).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat ∧ sp' +
      312#64 + 24#64 = sp' + 336#64 ∧
      sp' + 512#64 - 72#64 = sp' + 440#64 ∧ (body ++ psmRem2 x).length < 9223372036854775808 ∧
      BytesMergeCapOk 0#64 (body ++ psmRem2 x).length)
    (by simp only [bytesMergeRawSpec, hsp_eq, arm64_norm])
    ⟨rfl, by bv_omega, by bv_omega, by omega, bytesMergeCapOk_of_len_lt32 hlt_body⟩ (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  have hregs2 : PreKeyLoopRegs sp' x s2 := PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using h28, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using h26, by simpa [arm64_norm] using h25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      hsp2 hcs2
  have h29_2 := hregs2.x29
  dsimp only [bytesMergeRawSpec]; rw [merge_field2 x]
  dsimp only; rw [sepConj_assoc]; refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre fun hx0_2 => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
  refine SepWPp.exists_pre fun cap' => SepWPp.exists_pre fun ptr' => SepWPp.pure_pre fun _ => ?_
  have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hpost_cur :
      (cur1 x ↦₈ 0x12#8) ∗ sliceCursorAfter (sp' + 296#64) (cur1 x + 1#64) (body ++
        psmRem2 x) (psmRem2 x) =
      (cur1 x ↦ₛ psmField2 x) ∗ (((sp' + 296#64) ↦₆₄ cur2 x) ∗ (((sp' +
        304#64) ↦₆₄ BitVec.ofNat 64 (psmRem2 x).length) ∗ (cur2 x ↦ₛ psmRem2 x))) := by
    rw [cons_sliceCursorAfter_split, ← hf2]
    unfold sliceCursorAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rfl
  refine SepWPp.mono_pre
    (P' := ((cur1 x ↦₈ 0x12#8) ∗ sliceCursorAfter (sp' + 296#64) (cur1 x + 1#64) (body ++
      psmRem2 x) (psmRem2 x)) ∗
      ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ vecU8At A (sp' + 336#64) cap' ptr' x.bkBytes ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
    (by
      simp only [hsp_eq, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  rw [hpost_cur]; simp only [sepConj_assoc]; refine SepWPp.of_sepWP_end_lscl hcl2 ?_; wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hcl3
  refine ⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x27,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x25,
    by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
    by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
    by simpa [arm64_norm] using hregs2.x19⟩,
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hcl3, by simpa [arm64_norm] using htr2.trans htr,
    by simp [arm64_norm], cap', ptr', ?_⟩
  apply entails_of_eq; ac_rfl

theorem step_field3_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hbytes : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H)
      (lsmpl.base 7) (withLsCodeLoaded lsmpl (bytesMergeRawSpec A)))
    {x : PreKeyTryFromArgs} {s0 s : State} {sp' : BitVec 64}
    (hlt2 : (psmRem2 x).length < 2 ^ 32) (hlt3 : (psmRem3 x).length < 2 ^ 32)
    (hpc : s.pc = (blkPl_111).base + 0xf4#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' x s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (psmRem2 x).length) :
    SepWPp ((blkPC_111).rebase (blkPl_111).base H)
      ((blkPl_111).base + 0xf4#64) s
      (sliceCursorAt (sp' + 296#64) (cur2 x) (psmRem2 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
      (fun s1 P1 =>
        PreKeyLoopRegs sp' x s1 ∧ s1.spAligned = true ∧ LibsignalCodeLoaded lsmpl s1.mem ∧
        s1.trace = s0.trace ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem3 x).length ∧ ∃ cap' ptr' : BitVec 64,
          P1 ⊢ (cur2 x ↦ₛ psmField3 x) ∗ sliceCursorAt (sp' + 296#64) (cur3 x) (psmRem3 x) ∗ ((sp' +
          440#64) ↦₆₄ (sp' + 296#64)) ∗
            vecU8At A (sp' + 360#64) cap' ptr' x.ikBytes ∗ A.pool ∗ stackAt sp' bytesMergeStack)
      (tryFromQp s0) := by
  have hf3 := psmField3_eq x
  let body := encodeVarint 33#64 ++ x.ikBytes
  have hrem2 : psmRem2 x = 0x1a#8 :: (body ++ psmRem3 x) := by rw [psmRem2, hf3, List.cons_append]
  have hlt_body : (body ++ psmRem3 x).length < 2 ^ 32 := by
    have hlen : (psmRem2 x).length = (body ++ psmRem3 x).length + 1 := by
      rw [hrem2, List.length_cons]
    omega
  have hsub1 : BitVec.ofNat 64 (psmRem2 x).length - 1#64 =
      BitVec.ofNat 64 (body ++ psmRem3 x).length := by
    rw [hrem2, ofNat64_cons_sub_one]
  have hrem3_ne : BitVec.ofNat 64 (psmRem3 x).length ≠ 0#64 :=
    ofNat64_length_ne_zero (psmRem3_ne_nil x) hlt3
  have hrem3_beq : (BitVec.ofNat 64 (psmRem3 x).length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hrem3_ne
  have hsp_eq := hregs.sp
  have h29 := hregs.x29
  have h28 := hregs.x28
  have h26 := hregs.x26
  have h25 := hregs.x25
  have h23 := hregs.x23
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (psmRem2 x).length := hx2
  have hpts : (cur2 x ↦ₛ psmRem2 x) =
      (cur2 x ↦₈ 0x1a#8) ∗ ((cur2 x + 1#64) ↦ₛ (body ++ psmRem3 x)) := by
    rw [hrem2, pointsToBytes_cons]
  clear hrem2
  have hmr16 := memRegion16_split8_8' (sp' + 368#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmr16
  refine SepWPp.mono_pre
    (P' := (∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        ((sp' + 368#64) ↦₆₄ w0) ∗ ((sp' + 376#64) ↦₆₄ w1)) ∗ (sliceCursorAt (sp' +
        296#64) (cur2 x) (psmRem2 x) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 360#64) ↦₆₄ noneCap) ∗ A.pool ∗
        stackAt sp' bytesMergeStack))
    (by
      refine Entails.trans ?_ (sepConj_mono_left hmr16)
      apply entails_of_eq; ac_rfl) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w2 => ?_
  unfold sliceCursorAt
  rw [hpts]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_lscl hcl (mid := lsmpl.base 7) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  refine SepWPp.mono_pre
    (P' := (cur2 x ↦₈ 0x1a#8) ∗ vecU8At A (sp' + 360#64) 0#64 1#64 [] ∗ ((sp' + 440#64) ↦₆₄ (sp' +
      296#64)) ∗ sliceCursorAt (sp' + 296#64) (cur2 x + 1#64) (body ++ psmRem3 x) ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
    (by
      rw [← pointsTo64_emptyVec_eq_vecU8At A sp' 360#64 368#64 376#64]
      unfold sliceCursorAt
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.call_tryFrom_lscl
    ⟨.lengthDelimited, sp' + 360#64, 0#64, 1#64, [], sp' + 440#64, sp' + 296#64,
      cur2 x + 1#64, body ++ psmRem3 x⟩
    hbytes (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_111).base + 704#64) (by simp [arm64_norm]) (by simpa [arm64_norm] using htr)
    (T := vecU8At A (sp' + 360#64) 0#64 1#64 [] ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) (cur2 x + 1#64) (body ++ psmRem3 x) ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
    (φ := (2#64 : BitVec 64).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat ∧ sp' +
      312#64 + 48#64 = sp' + 360#64 ∧
      sp' + 512#64 - 72#64 = sp' + 440#64 ∧ (body ++ psmRem3 x).length < 9223372036854775808 ∧
      BytesMergeCapOk 0#64 (body ++ psmRem3 x).length)
    (by simp only [bytesMergeRawSpec, hsp_eq, arm64_norm])
    ⟨rfl, by bv_omega, by bv_omega, by omega, bytesMergeCapOk_of_len_lt32 hlt_body⟩ (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  have hregs2 : PreKeyLoopRegs sp' x s2 := PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using h28, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using h26, by simpa [arm64_norm] using h25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      hsp2 hcs2
  have h29_2 := hregs2.x29
  dsimp only [bytesMergeRawSpec]; rw [merge_field3 x]
  dsimp only; rw [sepConj_assoc]; refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre fun hx0_2 => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
  refine SepWPp.exists_pre fun cap' => SepWPp.exists_pre fun ptr' => SepWPp.pure_pre fun _ => ?_
  have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hpost_cur :
      (cur2 x ↦₈ 0x1a#8) ∗ sliceCursorAfter (sp' + 296#64) (cur2 x + 1#64) (body ++
        psmRem3 x) (psmRem3 x) =
      (cur2 x ↦ₛ psmField3 x) ∗ (((sp' + 296#64) ↦₆₄ cur3 x) ∗ (((sp' +
        304#64) ↦₆₄ BitVec.ofNat 64 (psmRem3 x).length) ∗ (cur3 x ↦ₛ psmRem3 x))) := by
    rw [cons_sliceCursorAfter_split, ← hf3]
    unfold sliceCursorAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rfl
  refine SepWPp.mono_pre
    (P' := ((cur2 x ↦₈ 0x1a#8) ∗ sliceCursorAfter (sp' + 296#64) (cur2 x + 1#64) (body ++
      psmRem3 x) (psmRem3 x)) ∗
      ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ vecU8At A (sp' + 360#64) cap' ptr' x.ikBytes ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
    (by
      simp only [hsp_eq, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  rw [hpost_cur]; simp only [sepConj_assoc]; refine SepWPp.of_sepWP_end_lscl hcl2 ?_; wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hcl3
  refine ⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x27,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x25,
    by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
    by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
    by simpa [arm64_norm] using hregs2.x19⟩,
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hcl3, by simpa [arm64_norm] using htr2.trans htr,
    by simp [arm64_norm], cap', ptr', ?_⟩
  apply entails_of_eq; ac_rfl

theorem step_field4_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hbytes : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H)
      (lsmpl.base 7) (withLsCodeLoaded lsmpl (bytesMergeRawSpec A)))
    {x : PreKeyTryFromArgs} {s0 s : State} {sp' : BitVec 64}
    (hlt_inner : x.inner.length < 2 ^ 32) (hlt3 : (psmRem3 x).length < 2 ^ 32)
    (hlt4 : (psmRem4 x).length < 2 ^ 32)
    (hpc : s.pc = (blkPl_111).base + 0xf4#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' x s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (psmRem3 x).length) :
    SepWPp ((blkPC_111).rebase (blkPl_111).base H)
      ((blkPl_111).base + 0xf4#64) s
      (sliceCursorAt (sp' + 296#64) (cur3 x) (psmRem3 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
      (fun s1 P1 =>
        PreKeyLoopRegs sp' x s1 ∧ s1.spAligned = true ∧ LibsignalCodeLoaded lsmpl s1.mem ∧
        s1.trace = s0.trace ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem4 x).length ∧ ∃ cap' ptr' : BitVec 64,
          P1 ⊢ (cur3 x ↦ₛ psmField4 x) ∗ sliceCursorAt (sp' + 296#64) (cur4 x) (psmRem4 x) ∗ ((sp' +
          440#64) ↦₆₄ (sp' + 296#64)) ∗
            vecU8At A (sp' + 384#64) cap' ptr' x.inner ∗ A.pool ∗ stackAt sp' bytesMergeStack)
      (tryFromQp s0) := by
  have hlt_inner64 : x.inner.length < 2 ^ 64 := by omega
  have hf4 := psmField4_eq x hlt_inner64
  let body := encodeVarint (BitVec.ofNat 64 x.inner.length) ++ x.inner
  have hrem3 : psmRem3 x = 0x22#8 :: (body ++ psmRem4 x) := by rw [psmRem3, hf4, List.cons_append]
  have hlt_body : (body ++ psmRem4 x).length < 2 ^ 32 := by
    have hlen : (psmRem3 x).length = (body ++ psmRem4 x).length + 1 := by
      rw [hrem3, List.length_cons]
    omega
  have hsub1 : BitVec.ofNat 64 (psmRem3 x).length - 1#64 =
      BitVec.ofNat 64 (body ++ psmRem4 x).length := by
    rw [hrem3, ofNat64_cons_sub_one]
  have hrem4_ne : BitVec.ofNat 64 (psmRem4 x).length ≠ 0#64 :=
    ofNat64_length_ne_zero (psmRem4_ne_nil x) hlt4
  have hrem4_beq : (BitVec.ofNat 64 (psmRem4 x).length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hrem4_ne
  have hsp_eq := hregs.sp
  have h29 := hregs.x29
  have h28 := hregs.x28
  have h26 := hregs.x26
  have h25 := hregs.x25
  have h23 := hregs.x23
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (psmRem3 x).length := hx2
  have hpts : (cur3 x ↦ₛ psmRem3 x) =
      (cur3 x ↦₈ 0x22#8) ∗ ((cur3 x + 1#64) ↦ₛ (body ++ psmRem4 x)) := by
    rw [hrem3, pointsToBytes_cons]
  clear hrem3
  have hmr16 := memRegion16_split8_8' (sp' + 392#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmr16
  refine SepWPp.mono_pre
    (P' := (∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        ((sp' + 392#64) ↦₆₄ w0) ∗ ((sp' + 400#64) ↦₆₄ w1)) ∗ (sliceCursorAt (sp' +
        296#64) (cur3 x) (psmRem3 x) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 384#64) ↦₆₄ noneCap) ∗ A.pool ∗
        stackAt sp' bytesMergeStack))
    (by
      refine Entails.trans ?_ (sepConj_mono_left hmr16)
      apply entails_of_eq; ac_rfl) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w2 => ?_
  unfold sliceCursorAt
  rw [hpts]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_lscl hcl (mid := lsmpl.base 7) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  refine SepWPp.mono_pre
    (P' := (cur3 x ↦₈ 0x22#8) ∗ vecU8At A (sp' + 384#64) 0#64 1#64 [] ∗ ((sp' + 440#64) ↦₆₄ (sp' +
      296#64)) ∗ sliceCursorAt (sp' + 296#64) (cur3 x + 1#64) (body ++ psmRem4 x) ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
    (by
      rw [← pointsTo64_emptyVec_eq_vecU8At A sp' 384#64 392#64 400#64]
      unfold sliceCursorAt
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.call_tryFrom_lscl
    ⟨.lengthDelimited, sp' + 384#64, 0#64, 1#64, [], sp' + 440#64, sp' + 296#64,
      cur3 x + 1#64, body ++ psmRem4 x⟩
    hbytes (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_111).base + 544#64) (by simp [arm64_norm]) (by simpa [arm64_norm] using htr)
    (T := vecU8At A (sp' + 384#64) 0#64 1#64 [] ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) (cur3 x + 1#64) (body ++ psmRem4 x) ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
    (φ := (2#64 : BitVec 64).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat ∧ sp' +
      312#64 + 72#64 = sp' + 384#64 ∧
      sp' + 512#64 - 72#64 = sp' + 440#64 ∧ (body ++ psmRem4 x).length < 9223372036854775808 ∧
      BytesMergeCapOk 0#64 (body ++ psmRem4 x).length)
    (by simp only [bytesMergeRawSpec, hsp_eq, arm64_norm])
    ⟨rfl, by bv_omega, by bv_omega, by omega, bytesMergeCapOk_of_len_lt32 hlt_body⟩ (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  have hregs2 : PreKeyLoopRegs sp' x s2 := PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using h28, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using h26, by simpa [arm64_norm] using h25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      hsp2 hcs2
  have h29_2 := hregs2.x29
  dsimp only [bytesMergeRawSpec]; rw [merge_field4 x hlt_inner64]
  dsimp only; rw [sepConj_assoc]; refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre fun hx0_2 => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
  refine SepWPp.exists_pre fun cap' => SepWPp.exists_pre fun ptr' => SepWPp.pure_pre fun _ => ?_
  have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hpost_cur :
      (cur3 x ↦₈ 0x22#8) ∗ sliceCursorAfter (sp' + 296#64) (cur3 x + 1#64) (body ++
        psmRem4 x) (psmRem4 x) =
      (cur3 x ↦ₛ psmField4 x) ∗ (((sp' + 296#64) ↦₆₄ cur4 x) ∗ (((sp' +
        304#64) ↦₆₄ BitVec.ofNat 64 (psmRem4 x).length) ∗ (cur4 x ↦ₛ psmRem4 x))) := by
    rw [cons_sliceCursorAfter_split, ← hf4]
    unfold sliceCursorAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rfl
  refine SepWPp.mono_pre
    (P' := ((cur3 x ↦₈ 0x22#8) ∗ sliceCursorAfter (sp' + 296#64) (cur3 x + 1#64) (body ++
      psmRem4 x) (psmRem4 x)) ∗
      ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ vecU8At A (sp' + 384#64) cap' ptr' x.inner ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
    (by
      simp only [hsp_eq, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  rw [hpost_cur]; simp only [sepConj_assoc]; refine SepWPp.of_sepWP_end_lscl hcl2 ?_; wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hcl3
  refine ⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x27,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x25,
    by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
    by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
    by simpa [arm64_norm] using hregs2.x19⟩,
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hcl3, by simpa [arm64_norm] using htr2.trans htr,
    by simp [arm64_norm], cap', ptr', ?_⟩
  apply entails_of_eq; ac_rfl

theorem step_field5_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hint32 : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H)
      (lsmpl.base 8) (withLsCodeLoaded lsmpl (int32MergeSpec A)))
    {x : PreKeyTryFromArgs} {s0 s : State} {sp' : BitVec 64} (hlt4 : (psmRem4 x).length < 2 ^ 32)
    (hlt5 : (psmRem5 x).length < 2 ^ 32)
    (hpc : s.pc = (blkPl_111).base + 0xf4#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' x s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (psmRem4 x).length) :
    SepWPp ((blkPC_111).rebase (blkPl_111).base H)
      ((blkPl_111).base + 0xf4#64) s
      (sliceCursorAt (sp' + 296#64) (cur4 x) (psmRem4 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗ A.pool ∗
        stackAt sp' int32MergeStack)
      (fun s1 P1 =>
        PreKeyLoopRegs sp' x s1 ∧ s1.spAligned = true ∧ LibsignalCodeLoaded lsmpl s1.mem ∧
        s1.trace = s0.trace ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem5 x).length ∧ (P1 ⊢ (cur4 x ↦ₛ psmField5 x) ∗
          sliceCursorAt (sp' + 296#64) (cur5 x) (psmRem5 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗ A.pool ∗
          stackAt sp' int32MergeStack))
      (tryFromQp s0) := by
  have hf5 := psmField5_eq x
  let body := encodeVarint (x.regId.zeroExtend 64)
  have hrem4 : psmRem4 x = 0x28#8 :: (body ++ psmRem5 x) := by rw [psmRem4, hf5, List.cons_append]
  have hlt_body : (body ++ psmRem5 x).length < 2 ^ 32 := by
    have hlen : (psmRem4 x).length = (body ++ psmRem5 x).length + 1 := by
      rw [hrem4, List.length_cons]
    omega
  have hsub1 : BitVec.ofNat 64 (psmRem4 x).length - 1#64 =
      BitVec.ofNat 64 (body ++ psmRem5 x).length := by
    rw [hrem4, ofNat64_cons_sub_one]
  have hrem5_ne : BitVec.ofNat 64 (psmRem5 x).length ≠ 0#64 :=
    ofNat64_length_ne_zero (psmRem5_ne_nil x) hlt5
  have hrem5_beq : (BitVec.ofNat 64 (psmRem5 x).length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hrem5_ne
  have hsp_eq := hregs.sp
  have h29 := hregs.x29
  have h28 := hregs.x28
  have h26 := hregs.x26
  have h25 := hregs.x25
  have h23 := hregs.x23
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (psmRem4 x).length := hx2
  have hpts : (cur4 x ↦ₛ psmRem4 x) =
      (cur4 x ↦₈ 0x28#8) ∗ ((cur4 x + 1#64) ↦ₛ (body ++ psmRem5 x)) := by
    rw [hrem4, pointsToBytes_cons]
  clear hrem4
  unfold sliceCursorAt
  rw [hpts]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_lscl hcl (mid := (blkPl_111).base + 648#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  have hent1 := pointsTo32_memRegion4_entails_exists_pointsTo64 (sp' + 408#64) 0#32
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hent1
  refine SepWPp.mono_pre
    (P' := (∃∗ w : BitVec 64, (sp' + 408#64) ↦₆₄ w) ∗ ((cur4 x ↦₈ 0x28#8) ∗ ((cur4 x +
      1#64) ↦ₛ (body ++ psmRem5 x)) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 296#64) ↦₆₄ (cur4 x + 1#64)) ∗
        ((sp' + 304#64) ↦₆₄ BitVec.ofNat 64 (body ++ psmRem5 x).length) ∗ A.pool ∗
        stackAt sp' int32MergeStack))
    (by
      refine Entails.trans ?_ (sepConj_mono_left hent1)
      apply entails_of_eq; ac_rfl) ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_pre fun w408 => ?_
  refine SepWPp.of_sepWP_lscl hcl1 (mid := lsmpl.base 8) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl2
  have hent2 := pointsTo64_one_entails_pointsTo32_memRegion4 (sp' + 408#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hent2
  refine SepWPp.mono_pre
    (P' := (((sp' + 408#64) ↦₃₂ 1#32) ∗ memRegion (sp' + 412#64) 4) ∗ ((cur4 x ↦₈ 0x28#8) ∗
      sliceCursorAt (sp' + 296#64) (cur4 x + 1#64) (body ++ psmRem5 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' +
        296#64)) ∗
      A.pool ∗ stackAt sp' int32MergeStack))
    (by
      unfold sliceCursorAt
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      refine Entails.trans ?_ (sepConj_mono_left hent2)
      apply entails_of_eq; ac_rfl) ?_
  simp only [sepConj_assoc]
  refine SepWPp.call_tryFrom_lscl
    ⟨.varint, sp' + 412#64, sp' + 440#64, sp' + 296#64, cur4 x + 1#64, body ++ psmRem5 x⟩
    hint32 (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl2
    (ret_pc := (blkPl_111).base + 664#64) (by simp [arm64_norm]) (by simpa [arm64_norm] using htr)
    (T := memRegion (sp' + 412#64) 4 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) (cur4 x + 1#64) (body ++ psmRem5 x) ∗ A.pool ∗
        stackAt sp' int32MergeStack)
    (φ := (0#64 : BitVec 64).setWidth 8 = BitVec.ofNat 8 WireType.varint.toNat ∧ sp' + 312#64 +
      100#64 = sp' + 412#64 ∧
      sp' + 512#64 - 72#64 = sp' + 440#64 ∧ (body ++ psmRem5 x).length < 9223372036854775808)
    (by dsimp only [int32MergeSpec]; simp only [hsp_eq, arm64_norm])
    ⟨rfl, by bv_omega, by bv_omega, by omega⟩ (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
  have hregs2 : PreKeyLoopRegs sp' x s2 := PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using h28, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using h26, by simpa [arm64_norm] using h25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      hsp2 hcs2
  have h29_2 := hregs2.x29
  dsimp only [int32MergeSpec]
  rw [merge_field5 x]
  dsimp only; rw [sepConj_assoc]; refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre fun hx0_2 => ?_
  have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hpost_cur :
      (cur4 x ↦₈ 0x28#8) ∗ sliceCursorAfter (sp' + 296#64) (cur4 x + 1#64) (body ++
        psmRem5 x) (psmRem5 x) =
      (cur4 x ↦ₛ psmField5 x) ∗ (((sp' + 296#64) ↦₆₄ cur5 x) ∗ (((sp' +
        304#64) ↦₆₄ BitVec.ofNat 64 (psmRem5 x).length) ∗ (cur5 x ↦ₛ psmRem5 x))) := by
    rw [cons_sliceCursorAfter_split, ← hf5]
    unfold sliceCursorAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rfl
  refine SepWPp.mono_pre
    (P' := ((cur4 x ↦₈ 0x28#8) ∗ sliceCursorAfter (sp' + 296#64) (cur4 x + 1#64) (body ++
      psmRem5 x) (psmRem5 x)) ∗
      ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' +
        412#64) ↦₃₂ x.regId) ∗
      A.pool ∗ stackAt sp' int32MergeStack)
    (by
      simp only [hsp_eq, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  rw [hpost_cur]
  simp only [sepConj_assoc]
  refine SepWPp.of_sepWP_end_lscl hcl3 ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hcl4
  refine ⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x27,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x25,
    by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
    by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
    by simpa [arm64_norm] using hregs2.x19⟩,
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hcl4, by simpa [arm64_norm] using htr2.trans htr,
    by simp [arm64_norm], ?_⟩
  apply entails_of_eq; ac_rfl

theorem step_field6_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hint32 : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H)
      (lsmpl.base 8) (withLsCodeLoaded lsmpl (int32MergeSpec A)))
    {x : PreKeyTryFromArgs} {s0 s : State} {sp' : BitVec 64} (hlt5 : (psmRem5 x).length < 2 ^ 32)
    (hlt6 : (psmRem6 x).length < 2 ^ 32)
    (hpc : s.pc = (blkPl_111).base + 0xf4#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' x s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (psmRem5 x).length) :
    SepWPp ((blkPC_111).rebase (blkPl_111).base H)
      ((blkPl_111).base + 0xf4#64) s
      (sliceCursorAt (sp' + 296#64) (cur5 x) (psmRem5 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗ A.pool ∗
        stackAt sp' int32MergeStack)
      (fun s1 P1 =>
        PreKeyLoopRegs sp' x s1 ∧ s1.spAligned = true ∧ LibsignalCodeLoaded lsmpl s1.mem ∧
        s1.trace = s0.trace ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem6 x).length ∧ (P1 ⊢ (cur5 x ↦ₛ psmField6 x) ∗
          sliceCursorAt (sp' + 296#64) (cur6 x) (psmRem6 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗ A.pool ∗
          stackAt sp' int32MergeStack))
      (tryFromQp s0) := by
  have hf6 := psmField6_eq x
  let body := encodeVarint (x.spkId.zeroExtend 64)
  have hrem5 : psmRem5 x = 0x30#8 :: (body ++ psmRem6 x) := by
    rw [psmRem5, hf6, List.cons_append]
  have hlt_body : (body ++ psmRem6 x).length < 2 ^ 32 := by
    have hlen : (psmRem5 x).length = (body ++ psmRem6 x).length + 1 := by
      rw [hrem5, List.length_cons]
    omega
  have hsub1 : BitVec.ofNat 64 (psmRem5 x).length - 1#64 =
      BitVec.ofNat 64 (body ++ psmRem6 x).length := by
    rw [hrem5, ofNat64_cons_sub_one]
  have hrem6_ne : BitVec.ofNat 64 (psmRem6 x).length ≠ 0#64 :=
    ofNat64_length_ne_zero (psmRem6_ne_nil x) hlt6
  have hrem6_beq : (BitVec.ofNat 64 (psmRem6 x).length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hrem6_ne
  have hsp_eq := hregs.sp
  have h29 := hregs.x29
  have h28 := hregs.x28
  have h26 := hregs.x26
  have h25 := hregs.x25
  have h23 := hregs.x23
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (psmRem5 x).length := hx2
  have hpts : (cur5 x ↦ₛ psmRem5 x) =
      (cur5 x ↦₈ 0x30#8) ∗ ((cur5 x + 1#64) ↦ₛ (body ++ psmRem6 x)) := by
    rw [hrem5, pointsToBytes_cons]
  clear hrem5
  unfold sliceCursorAt
  rw [hpts]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_lscl hcl (mid := (blkPl_111).base + 472#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  have hent1 := pointsTo32_memRegion4_entails_exists_pointsTo64 (sp' + 424#64) 0#32
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hent1
  refine SepWPp.mono_pre
    (P' := (∃∗ w : BitVec 64, (sp' + 424#64) ↦₆₄ w) ∗ ((cur5 x ↦₈ 0x30#8) ∗ ((cur5 x +
      1#64) ↦ₛ (body ++ psmRem6 x)) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 296#64) ↦₆₄ (cur5 x + 1#64)) ∗
        ((sp' + 304#64) ↦₆₄ BitVec.ofNat 64 (body ++ psmRem6 x).length) ∗ A.pool ∗
        stackAt sp' int32MergeStack))
    (by
      refine Entails.trans ?_ (sepConj_mono_left hent1)
      apply entails_of_eq; ac_rfl) ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_pre fun w424 => ?_
  refine SepWPp.of_sepWP_lscl hcl1 (mid := lsmpl.base 8) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl2
  have hent2 := pointsTo64_one_entails_pointsTo32_memRegion4 (sp' + 424#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hent2
  refine SepWPp.mono_pre
    (P' := (((sp' + 424#64) ↦₃₂ 1#32) ∗ memRegion (sp' + 428#64) 4) ∗ ((cur5 x ↦₈ 0x30#8) ∗
      sliceCursorAt (sp' + 296#64) (cur5 x + 1#64) (body ++ psmRem6 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' +
        296#64)) ∗
      A.pool ∗ stackAt sp' int32MergeStack))
    (by
      unfold sliceCursorAt
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      refine Entails.trans ?_ (sepConj_mono_left hent2)
      apply entails_of_eq; ac_rfl) ?_
  simp only [sepConj_assoc]
  refine SepWPp.call_tryFrom_lscl
    ⟨.varint, sp' + 428#64, sp' + 440#64, sp' + 296#64, cur5 x + 1#64, body ++ psmRem6 x⟩
    hint32
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl2
    (ret_pc := (blkPl_111).base + 488#64) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := memRegion (sp' + 428#64) 4 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) (cur5 x + 1#64) (body ++ psmRem6 x) ∗ A.pool ∗
        stackAt sp' int32MergeStack)
    (φ := (0#64 : BitVec 64).setWidth 8 = BitVec.ofNat 8 WireType.varint.toNat ∧ sp' + 312#64 +
      116#64 = sp' + 428#64 ∧
      sp' + 512#64 - 72#64 = sp' + 440#64 ∧ (body ++ psmRem6 x).length < 9223372036854775808)
    (by dsimp only [int32MergeSpec]; simp only [hsp_eq, arm64_norm])
    ⟨rfl, by bv_omega, by bv_omega, by omega⟩
    (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
  have hregs2 : PreKeyLoopRegs sp' x s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using h28, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using h26, by simpa [arm64_norm] using h25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      hsp2 hcs2
  have h29_2 := hregs2.x29
  dsimp only [int32MergeSpec]
  rw [merge_field6 x]
  dsimp only; rw [sepConj_assoc]; refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre fun hx0_2 => ?_
  have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hpost_cur :
      (cur5 x ↦₈ 0x30#8) ∗ sliceCursorAfter (sp' + 296#64) (cur5 x + 1#64) (body ++
        psmRem6 x) (psmRem6 x) =
      (cur5 x ↦ₛ psmField6 x) ∗ (((sp' + 296#64) ↦₆₄ cur6 x) ∗ (((sp' +
        304#64) ↦₆₄ BitVec.ofNat 64 (psmRem6 x).length) ∗
        (cur6 x ↦ₛ psmRem6 x))) := by
    rw [cons_sliceCursorAfter_split, ← hf6]
    unfold sliceCursorAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rfl
  refine SepWPp.mono_pre
    (P' := ((cur5 x ↦₈ 0x30#8) ∗ sliceCursorAfter (sp' + 296#64) (cur5 x + 1#64) (body ++
      psmRem6 x) (psmRem6 x)) ∗
      ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' +
        428#64) ↦₃₂ x.spkId) ∗
      A.pool ∗ stackAt sp' int32MergeStack)
    (by
      simp only [hsp_eq, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  rw [hpost_cur]
  simp only [sepConj_assoc]
  refine SepWPp.of_sepWP_end_lscl hcl3 ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hcl4
  refine ⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x27,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x25,
    by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
    by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
    by simpa [arm64_norm] using hregs2.x19⟩,
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hcl4, by simpa [arm64_norm] using htr2.trans htr,
    by simp [arm64_norm], ?_⟩
  apply entails_of_eq; ac_rfl

theorem step_field7_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hint32 : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H)
      (lsmpl.base 8) (withLsCodeLoaded lsmpl (int32MergeSpec A)))
    {x : PreKeyTryFromArgs} {s0 s : State} {sp' : BitVec 64}
    (hlt6 : (psmRem6 x).length < 2 ^ 32)
    (hlt7 : (psmRem7 x).length < 2 ^ 32)
    (hpc : s.pc = (blkPl_111).base + 0xf4#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' x s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (psmRem6 x).length) :
    SepWPp ((blkPC_111).rebase (blkPl_111).base H)
      ((blkPl_111).base + 0xf4#64) s
      (sliceCursorAt (sp' + 296#64) (cur6 x) (psmRem6 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗ A.pool ∗
        stackAt sp' int32MergeStack)
      (fun s1 P1 =>
        PreKeyLoopRegs sp' x s1 ∧ s1.spAligned = true ∧ LibsignalCodeLoaded lsmpl s1.mem ∧
        s1.trace = s0.trace ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem7 x).length ∧ (P1 ⊢ (cur6 x ↦ₛ psmField7 x) ∗
          sliceCursorAt (sp' + 296#64) (cur7 x) (psmRem7 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          ((sp' + 432#64) ↦₃₂ 1#32) ∗ ((sp' + 436#64) ↦₃₂ x.kpkId) ∗ A.pool ∗
          stackAt sp' int32MergeStack))
      (tryFromQp s0) := by
  have hf7 := psmField7_eq x
  let body := encodeVarint (x.kpkId.zeroExtend 64)
  have hrem6 : psmRem6 x = 0x38#8 :: (body ++ psmRem7 x) := by
    rw [psmRem6, hf7, List.cons_append]
  have hlt_body : (body ++ psmRem7 x).length < 2 ^ 32 := by
    have hlen : (psmRem6 x).length = (body ++ psmRem7 x).length + 1 := by
      rw [hrem6, List.length_cons]
    omega
  have hsub1 : BitVec.ofNat 64 (psmRem6 x).length - 1#64 =
      BitVec.ofNat 64 (body ++ psmRem7 x).length := by
    rw [hrem6, ofNat64_cons_sub_one]
  have hrem7_ne : BitVec.ofNat 64 (psmRem7 x).length ≠ 0#64 :=
    ofNat64_length_ne_zero (psmRem7_ne_nil x) hlt7
  have hrem7_beq : (BitVec.ofNat 64 (psmRem7 x).length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hrem7_ne
  have hsp_eq := hregs.sp
  have h29 := hregs.x29
  have h28 := hregs.x28
  have h26 := hregs.x26
  have h25 := hregs.x25
  have h23 := hregs.x23
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (psmRem6 x).length := hx2
  have hpts : (cur6 x ↦ₛ psmRem6 x) =
      (cur6 x ↦₈ 0x38#8) ∗ ((cur6 x + 1#64) ↦ₛ (body ++ psmRem7 x)) := by
    rw [hrem6, pointsToBytes_cons]
  clear hrem6
  unfold sliceCursorAt
  rw [hpts]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_lscl hcl (mid := (blkPl_111).base + 720#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  have hent1 := pointsTo32_memRegion4_entails_exists_pointsTo64 (sp' + 432#64) 0#32
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hent1
  refine SepWPp.mono_pre
    (P' := (∃∗ w : BitVec 64, (sp' + 432#64) ↦₆₄ w) ∗ ((cur6 x ↦₈ 0x38#8) ∗ ((cur6 x +
      1#64) ↦ₛ (body ++ psmRem7 x)) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 296#64) ↦₆₄ (cur6 x + 1#64)) ∗
        ((sp' + 304#64) ↦₆₄ BitVec.ofNat 64 (body ++ psmRem7 x).length) ∗ A.pool ∗
        stackAt sp' int32MergeStack))
    (by
      refine Entails.trans ?_ (sepConj_mono_left hent1)
      apply entails_of_eq; ac_rfl) ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_pre fun w432 => ?_
  refine SepWPp.of_sepWP_lscl hcl1 (mid := lsmpl.base 8) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl2
  have hent2 := pointsTo64_one_entails_pointsTo32_memRegion4 (sp' + 432#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hent2
  refine SepWPp.mono_pre
    (P' := (((sp' + 432#64) ↦₃₂ 1#32) ∗ memRegion (sp' + 436#64) 4) ∗ ((cur6 x ↦₈ 0x38#8) ∗
      sliceCursorAt (sp' + 296#64) (cur6 x + 1#64) (body ++ psmRem7 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' +
        296#64)) ∗
      A.pool ∗ stackAt sp' int32MergeStack))
    (by
      unfold sliceCursorAt
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      refine Entails.trans ?_ (sepConj_mono_left hent2)
      apply entails_of_eq; ac_rfl) ?_
  simp only [sepConj_assoc]
  refine SepWPp.call_tryFrom_lscl
    ⟨.varint, sp' + 436#64, sp' + 440#64, sp' + 296#64, cur6 x + 1#64, body ++ psmRem7 x⟩
    hint32
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl2
    (ret_pc := (blkPl_111).base + 224#64) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := memRegion (sp' + 436#64) 4 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) (cur6 x + 1#64) (body ++ psmRem7 x) ∗ A.pool ∗
        stackAt sp' int32MergeStack)
    (φ := (0#64 : BitVec 64).setWidth 8 = BitVec.ofNat 8 WireType.varint.toNat ∧ sp' + 312#64 +
      124#64 = sp' + 436#64 ∧
      sp' + 512#64 - 72#64 = sp' + 440#64 ∧ (body ++ psmRem7 x).length < 9223372036854775808)
    (by dsimp only [int32MergeSpec]; simp only [hsp_eq, arm64_norm])
    ⟨rfl, by bv_omega, by bv_omega, by omega⟩
    (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
  have hregs2 : PreKeyLoopRegs sp' x s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using h28, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using h26, by simpa [arm64_norm] using h25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      hsp2 hcs2
  have h29_2 := hregs2.x29
  dsimp only [int32MergeSpec]
  rw [merge_field7 x]
  dsimp only; rw [sepConj_assoc]; refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre fun hx0_2 => ?_
  have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hpost_cur :
      (cur6 x ↦₈ 0x38#8) ∗ sliceCursorAfter (sp' + 296#64) (cur6 x + 1#64) (body ++
        psmRem7 x) (psmRem7 x) =
      (cur6 x ↦ₛ psmField7 x) ∗ (((sp' + 296#64) ↦₆₄ cur7 x) ∗ (((sp' +
        304#64) ↦₆₄ BitVec.ofNat 64 (psmRem7 x).length) ∗
        (cur7 x ↦ₛ psmRem7 x))) := by
    rw [cons_sliceCursorAfter_split, ← hf7]
    unfold sliceCursorAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rfl
  refine SepWPp.mono_pre
    (P' := ((cur6 x ↦₈ 0x38#8) ∗ sliceCursorAfter (sp' + 296#64) (cur6 x + 1#64) (body ++
      psmRem7 x) (psmRem7 x)) ∗
      ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 432#64) ↦₃₂ 1#32) ∗ ((sp' +
        436#64) ↦₃₂ x.kpkId) ∗
      A.pool ∗ stackAt sp' int32MergeStack)
    (by
      simp only [hsp_eq, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  rw [hpost_cur]
  simp only [sepConj_assoc]
  refine SepWPp.of_sepWP_end_lscl hcl3 ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hcl4
  refine ⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x27,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x25,
    by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
    by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
    by simpa [arm64_norm] using hregs2.x19⟩,
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hcl4, by simpa [arm64_norm] using htr2.trans htr,
    by simp [arm64_norm], ?_⟩
  apply entails_of_eq; ac_rfl

theorem step_field8_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hbytes : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H)
      (lsmpl.base 7) (withLsCodeLoaded lsmpl (bytesMergeRawSpec A)))
    {x : PreKeyTryFromArgs} {s0 s : State} {sp' : BitVec 64}
    (hlt7 : (psmRem7 x).length < 2 ^ 32)
    (hpc : s.pc = (blkPl_111).base + 0xf4#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' x s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (psmRem7 x).length) :
    SepWPp ((blkPC_111).rebase (blkPl_111).base H)
      ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) (cur7 x) (psmRem7 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
      (fun s1 P1 =>
        PreKeyLoopRegs sp' x s1 ∧ s1.spAligned = true ∧ LibsignalCodeLoaded lsmpl s1.mem ∧
        s1.trace = s0.trace ∧
        s1.readReg64 .x24 = 0#64 ∧ ∃ cap' ptr' : BitVec 64,
          P1 ⊢ (cur7 x ↦ₛ psmField8 x) ∗ sliceCursorAt (sp' + 296#64) (cur8 x) (psmRem8 x) ∗ ((sp' +
          440#64) ↦₆₄ (sp' + 296#64)) ∗
            vecU8At A (sp' + 312#64) cap' ptr' x.kyberBytes ∗ A.pool ∗ stackAt sp' bytesMergeStack)
      (tryFromQp s0) := by
  have hf8 := psmField8_eq x
  let body := encodeVarint 1569#64 ++ x.kyberBytes
  have hrem7 : psmRem7 x = 0x42#8 :: (body ++ psmRem8 x) := by
    rw [psmRem7, hf8, List.cons_append]
  have hlt_body : (body ++ psmRem8 x).length < 2 ^ 32 := by
    have hlen : (psmRem7 x).length = (body ++ psmRem8 x).length + 1 := by
      rw [hrem7, List.length_cons]
    omega
  have hsub1 : BitVec.ofNat 64 (psmRem7 x).length - 1#64 =
      BitVec.ofNat 64 (body ++ psmRem8 x).length := by
    rw [hrem7, ofNat64_cons_sub_one]
  have hrem8_len : BitVec.ofNat 64 (psmRem8 x).length = 0#64 := rfl
  have hsp_eq := hregs.sp
  have h29 := hregs.x29
  have h28 := hregs.x28
  have h26 := hregs.x26
  have h25 := hregs.x25
  have h23 := hregs.x23
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (psmRem7 x).length := hx2
  have hpts : (cur7 x ↦ₛ psmRem7 x) =
      (cur7 x ↦₈ 0x42#8) ∗ ((cur7 x + 1#64) ↦ₛ (body ++ psmRem8 x)) := by
    rw [hrem7, pointsToBytes_cons]
  clear hrem7
  have hmr16 := memRegion16_split8_8' (sp' + 320#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmr16
  refine SepWPp.mono_pre
    (P' := (∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        ((sp' + 320#64) ↦₆₄ w0) ∗ ((sp' + 328#64) ↦₆₄ w1)) ∗ (sliceCursorAt (sp' +
        296#64) (cur7 x) (psmRem7 x) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 312#64) ↦₆₄ noneCap) ∗ A.pool ∗
        stackAt sp' bytesMergeStack))
    (by
      refine Entails.trans ?_ (sepConj_mono_left hmr16)
      apply entails_of_eq; ac_rfl) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w2 => ?_
  unfold sliceCursorAt
  rw [hpts]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_lscl hcl (mid := lsmpl.base 7) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  refine SepWPp.mono_pre
    (P' := (cur7 x ↦₈ 0x42#8) ∗ vecU8At A (sp' + 312#64) 0#64 1#64 [] ∗ ((sp' + 440#64) ↦₆₄ (sp' +
      296#64)) ∗
      sliceCursorAt (sp' + 296#64) (cur7 x + 1#64) (body ++ psmRem8 x) ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
    (by
      rw [← pointsTo64_emptyVec_eq_vecU8At A sp' 312#64 320#64 328#64]
      unfold sliceCursorAt
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.call_tryFrom_lscl
    ⟨.lengthDelimited, sp' + 312#64, 0#64, 1#64, [], sp' + 440#64, sp' + 296#64,
      cur7 x + 1#64, body ++ psmRem8 x⟩
    hbytes
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_111).base + 600#64) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := vecU8At A (sp' + 312#64) 0#64 1#64 [] ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) (cur7 x + 1#64) (body ++ psmRem8 x) ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
    (φ := (2#64 : BitVec 64).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat ∧ sp' +
      512#64 - 200#64 = sp' + 312#64 ∧
      sp' + 512#64 - 72#64 = sp' + 440#64 ∧ (body ++ psmRem8 x).length < 9223372036854775808 ∧
      BytesMergeCapOk 0#64 (body ++ psmRem8 x).length)
    (by simp only [bytesMergeRawSpec, hsp_eq, arm64_norm])
    ⟨rfl, by bv_omega, by bv_omega, by omega, bytesMergeCapOk_of_len_lt32 hlt_body⟩
    (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  have hregs2 : PreKeyLoopRegs sp' x s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using h28, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using h26, by simpa [arm64_norm] using h25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      hsp2 hcs2
  have h29_2 := hregs2.x29
  dsimp only [bytesMergeRawSpec]; rw [merge_field8 x]
  dsimp only; rw [sepConj_assoc]; refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre fun hx0_2 => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
  refine SepWPp.exists_pre fun cap' => SepWPp.exists_pre fun ptr' => SepWPp.pure_pre fun _ => ?_
  have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hpost_cur :
      (cur7 x ↦₈ 0x42#8) ∗ sliceCursorAfter (sp' + 296#64) (cur7 x + 1#64) (body ++
        psmRem8 x) (psmRem8 x) =
      (cur7 x ↦ₛ psmField8 x) ∗ (((sp' + 296#64) ↦₆₄ cur8 x) ∗ (((sp' + 304#64) ↦₆₄ 0#64) ∗
        (cur8 x ↦ₛ psmRem8 x))) := by
    rw [cons_sliceCursorAfter_split, ← hf8]
    unfold sliceCursorAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rfl
  refine SepWPp.mono_pre
    (P' := ((cur7 x ↦₈ 0x42#8) ∗ sliceCursorAfter (sp' + 296#64) (cur7 x + 1#64) (body ++
      psmRem8 x) (psmRem8 x)) ∗
      ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ vecU8At A (sp' + 312#64) cap' ptr' x.kyberBytes ∗
        A.pool ∗ stackAt sp' bytesMergeStack)
    (by
      simp only [hsp_eq, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  rw [hpost_cur]; simp only [sepConj_assoc]; refine SepWPp.of_sepWP_end_lscl hcl2 ?_; wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hcl3
  refine ⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x27,
    by simp [arm64_norm], by simpa [arm64_norm] using hregs2.x25,
    by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
    by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
    by simpa [arm64_norm] using hregs2.x19⟩,
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hcl3, by simpa [arm64_norm] using htr2.trans htr,
    by simp [arm64_norm],
    cap', ptr', ?_⟩
  apply entails_of_eq; ac_rfl

set_option maxHeartbeats 1600000 in
theorem preKey_entry_to_f90_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hint32 : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H)
      (lsmpl.base 8) (withLsCodeLoaded lsmpl (int32MergeSpec A)))
    (hbytes : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H)
      (lsmpl.base 7) (withLsCodeLoaded lsmpl (bytesMergeRawSpec A)))
    {x : PreKeyTryFromArgs} {s0 : State} {sp' : BitVec 64}
    (hsp' : sp' = s0.sp - 608#64)
    (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (blkPl_111).base)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = x.ptr)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.sret) :
    SepWPp ((blkPC_111).rebase (blkPl_111).base H)
      ((blkPl_111).base + 0x460#64) s0
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion (sp' + 296#64) 152 ∗ memRegion (sp' + 512#64) 96 ∗ A.pool ∗
        stackAt sp' bytesMergeStack)
      (fun sf Pf =>
        PreKeyLoopRegs sp' x sf ∧ sf.spAligned = true ∧ LibsignalCodeLoaded lsmpl sf.mem ∧
        sf.trace = s0.trace ∧
        sf.readReg64 .x24 = 0#64 ∧
        ∃ (opkVal : BitVec 32) (kyberCap kyberPtr bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec
        64),
          (∀ v, x.opkId = some v → opkVal = v) ∧ (Pf ⊢ (x.ptr ↦ₛ x.bytes) ∗ ((sp' +
          296#64) ↦₆₄ cur8 x) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
            vecU8At A (sp' + 312#64) kyberCap kyberPtr x.kyberBytes ∗ vecU8At A (sp' +
            336#64) bkCap bkPtr x.bkBytes ∗
            vecU8At A (sp' + 360#64) ikCap ikPtr x.ikBytes ∗ vecU8At A (sp' +
            384#64) msgCap msgPtr x.inner ∗
            ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗ ((sp' +
            416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
            ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗ ((sp' + 432#64) ↦₃₂ 1#32) ∗
            ((sp' + 436#64) ↦₃₂ x.kpkId) ∗
            ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ preKeyCalleeSavedAt sp' s0 ∗ A.pool ∗
            stackAt sp' bytesMergeStack))
      (tryFromQp s0) := by
  rcases psmRem_lengths_lt x hlt with ⟨_, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt_in⟩
  refine SepWPp.mono_pre
    (P' := ((x.ptr ↦ₛ x.bytes) ∗ memRegion (sp' + 296#64) 152 ∗ memRegion (sp' + 512#64) 96) ∗
      (A.pool ∗ stackAt sp' bytesMergeStack))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (hsp' ▸ prologue_to_c24_placed_wp hlt hpc hrun hsp hcl hx0 hx1 hx8) ?_
  intro s1 P1 hpc1 hrun1 ⟨hregs1, hsp1, hcl1, htr1, hx2_1, hent1⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent1) ?_
  clear hent1
  refine SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur0 x) (psmRem0 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' +
      296#64)) ∗
        ((sp' + 416#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 420#64) 4 ∗ A.pool ∗
        stackAt sp' int32MergeStack) ∗ ((x.ptr ↦₈ 0x44#8) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗ ((sp' + 336#64) ↦₆₄ noneCap) ∗
        memRegion (sp' + 344#64) 16 ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗ ((sp' + 384#64) ↦₆₄ noneCap) ∗
        memRegion (sp' + 392#64) 16 ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗ ((sp' + 424#64) ↦₃₂ 0#32) ∗
        memRegion (sp' + 428#64) 4 ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗
        preKeyCalleeSavedAt sp' s0 ∗ memRegion (sp' -
        BitVec.ofNat 64 bytesMergeStack) (bytesMergeStack - int32MergeStack)))
    (by apply entails_of_eq; rw [stackAt_bytesMerge_split_int32 sp']; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (step_field1_placed_wp hint32 hlt0 hlt1 hpc1 hrun1 hregs1 hsp1 hcl1 htr1 hx2_1) ?_
  intro s2 P2 hpc2 hrun2 ⟨hregs2, hsp2, hcl2, htr2, hx2_2, opkVal, hopkVal, hent2⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent2) ?_
  clear hent2
  refine SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur1 x) (psmRem1 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' +
      296#64)) ∗
        ((sp' + 336#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 344#64) 16 ∗ A.pool ∗
        stackAt sp' bytesMergeStack) ∗
      ((x.ptr ↦₈ 0x44#8) ∗ (cur0 x ↦ₛ psmField1 x) ∗ ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' +
        320#64) 16 ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗ ((sp' + 384#64) ↦₆₄ noneCap) ∗
        memRegion (sp' + 392#64) 16 ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗ ((sp' + 416#64) ↦₃₂ opkTag x) ∗
        ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗ ((sp' + 432#64) ↦₃₂ 0#32) ∗
        memRegion (sp' + 436#64) 4 ∗
        preKeyCalleeSavedAt sp' s0))
    (by apply entails_of_eq; rw [stackAt_bytesMerge_split_int32 sp']; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (step_field2_placed_wp hbytes hlt1 hlt2 hpc2 hrun2 hregs2 hsp2 hcl2 htr2 hx2_2) ?_
  intro s3 P3 hpc3 hrun3 ⟨hregs3, hsp3, hcl3, htr3, hx2_3, bkCap, bkPtr, hent3⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent3) ?_
  clear hent3
  refine SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur2 x) (psmRem2 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' +
      296#64)) ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗ A.pool ∗
        stackAt sp' bytesMergeStack) ∗
      ((x.ptr ↦₈ 0x44#8) ∗ (cur0 x ↦ₛ psmField1 x) ∗ (cur1 x ↦ₛ psmField2 x) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗ vecU8At A (sp' +
        336#64) bkCap bkPtr x.bkBytes ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗ ((sp' + 408#64) ↦₃₂ 0#32) ∗
        memRegion (sp' + 412#64) 4 ∗
        ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗ ((sp' + 424#64) ↦₃₂ 0#32) ∗
        memRegion (sp' + 428#64) 4 ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗ preKeyCalleeSavedAt sp' s0))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (step_field3_placed_wp hbytes hlt2 hlt3 hpc3 hrun3 hregs3 hsp3 hcl3 htr3 hx2_3) ?_
  intro s4 P4 hpc4 hrun4 ⟨hregs4, hsp4, hcl4, htr4, hx2_4, ikCap, ikPtr, hent4⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent4) ?_
  clear hent4
  refine SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur3 x) (psmRem3 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' +
      296#64)) ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗ A.pool ∗
        stackAt sp' bytesMergeStack) ∗
      ((x.ptr ↦₈ 0x44#8) ∗ (cur0 x ↦ₛ psmField1 x) ∗ (cur1 x ↦ₛ psmField2 x) ∗
        (cur2 x ↦ₛ psmField3 x) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗ vecU8At A (sp' +
        336#64) bkCap bkPtr x.bkBytes ∗
        vecU8At A (sp' + 360#64) ikCap ikPtr x.ikBytes ∗ ((sp' + 408#64) ↦₃₂ 0#32) ∗
        memRegion (sp' + 412#64) 4 ∗
        ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗ ((sp' + 424#64) ↦₃₂ 0#32) ∗
        memRegion (sp' + 428#64) 4 ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗ preKeyCalleeSavedAt sp' s0))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (step_field4_placed_wp hbytes hlt_in hlt3 hlt4 hpc4 hrun4 hregs4 hsp4 hcl4 htr4 hx2_4) ?_
  intro s5 P5 hpc5 hrun5 ⟨hregs5, hsp5, hcl5, htr5, hx2_5, msgCap, msgPtr, hent5⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent5) ?_
  clear hent5
  refine SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur4 x) (psmRem4 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' +
      296#64)) ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗ A.pool ∗
        stackAt sp' int32MergeStack) ∗
      ((x.ptr ↦₈ 0x44#8) ∗ (cur0 x ↦ₛ psmField1 x) ∗ (cur1 x ↦ₛ psmField2 x) ∗
        (cur2 x ↦ₛ psmField3 x) ∗ (cur3 x ↦ₛ psmField4 x) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗ vecU8At A (sp' +
        336#64) bkCap bkPtr x.bkBytes ∗
        vecU8At A (sp' + 360#64) ikCap ikPtr x.ikBytes ∗ vecU8At A (sp' +
        384#64) msgCap msgPtr x.inner ∗
        ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗ ((sp' + 424#64) ↦₃₂ 0#32) ∗
        memRegion (sp' + 428#64) 4 ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗
        preKeyCalleeSavedAt sp' s0 ∗ memRegion (sp' -
        BitVec.ofNat 64 bytesMergeStack) (bytesMergeStack - int32MergeStack)))
    (by apply entails_of_eq; rw [stackAt_bytesMerge_split_int32 sp']; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (step_field5_placed_wp hint32 hlt4 hlt5 hpc5 hrun5 hregs5 hsp5 hcl5 htr5 hx2_5) ?_
  intro s6 P6 hpc6 hrun6 ⟨hregs6, hsp6, hcl6, htr6, hx2_6, hent6⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent6) ?_
  clear hent6
  refine SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur5 x) (psmRem5 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' +
      296#64)) ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗ A.pool ∗
        stackAt sp' int32MergeStack) ∗
      ((x.ptr ↦₈ 0x44#8) ∗ (cur0 x ↦ₛ psmField1 x) ∗ (cur1 x ↦ₛ psmField2 x) ∗
        (cur2 x ↦ₛ psmField3 x) ∗ (cur3 x ↦ₛ psmField4 x) ∗ (cur4 x ↦ₛ psmField5 x) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗ vecU8At A (sp' +
        336#64) bkCap bkPtr x.bkBytes ∗
        vecU8At A (sp' + 360#64) ikCap ikPtr x.ikBytes ∗ vecU8At A (sp' +
        384#64) msgCap msgPtr x.inner ∗
        ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗ ((sp' + 416#64) ↦₃₂ opkTag x) ∗
        ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗
        preKeyCalleeSavedAt sp' s0 ∗ memRegion (sp' -
        BitVec.ofNat 64 bytesMergeStack) (bytesMergeStack - int32MergeStack)))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (step_field6_placed_wp hint32 hlt5 hlt6 hpc6 hrun6 hregs6 hsp6 hcl6 htr6 hx2_6) ?_
  intro s7 P7 hpc7 hrun7 ⟨hregs7, hsp7, hcl7, htr7, hx2_7, hent7⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent7) ?_
  clear hent7
  refine SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur6 x) (psmRem6 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' +
      296#64)) ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗ A.pool ∗
        stackAt sp' int32MergeStack) ∗
      ((x.ptr ↦₈ 0x44#8) ∗ (cur0 x ↦ₛ psmField1 x) ∗ (cur1 x ↦ₛ psmField2 x) ∗
        (cur2 x ↦ₛ psmField3 x) ∗ (cur3 x ↦ₛ psmField4 x) ∗ (cur4 x ↦ₛ psmField5 x) ∗
        (cur5 x ↦ₛ psmField6 x) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗ vecU8At A (sp' +
        336#64) bkCap bkPtr x.bkBytes ∗
        vecU8At A (sp' + 360#64) ikCap ikPtr x.ikBytes ∗ vecU8At A (sp' +
        384#64) msgCap msgPtr x.inner ∗
        ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗ ((sp' + 416#64) ↦₃₂ opkTag x) ∗
        ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗
        preKeyCalleeSavedAt sp' s0 ∗ memRegion (sp' -
        BitVec.ofNat 64 bytesMergeStack) (bytesMergeStack - int32MergeStack)))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (step_field7_placed_wp hint32 hlt6 hlt7 hpc7 hrun7 hregs7 hsp7 hcl7 htr7 hx2_7) ?_
  intro s8 P8 hpc8 hrun8 ⟨hregs8, hsp8, hcl8, htr8, hx2_8, hent8⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent8) ?_
  clear hent8
  refine SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur7 x) (psmRem7 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' +
      296#64)) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗ A.pool ∗
        stackAt sp' bytesMergeStack) ∗
      ((x.ptr ↦₈ 0x44#8) ∗ (cur0 x ↦ₛ psmField1 x) ∗ (cur1 x ↦ₛ psmField2 x) ∗
        (cur2 x ↦ₛ psmField3 x) ∗ (cur3 x ↦ₛ psmField4 x) ∗ (cur4 x ↦ₛ psmField5 x) ∗
        (cur5 x ↦ₛ psmField6 x) ∗ (cur6 x ↦ₛ psmField7 x) ∗ vecU8At A (sp' +
        336#64) bkCap bkPtr x.bkBytes ∗
        vecU8At A (sp' + 360#64) ikCap ikPtr x.ikBytes ∗ vecU8At A (sp' +
        384#64) msgCap msgPtr x.inner ∗
        ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗ ((sp' + 416#64) ↦₃₂ opkTag x) ∗
        ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗ ((sp' + 432#64) ↦₃₂ 1#32) ∗
        ((sp' + 436#64) ↦₃₂ x.kpkId) ∗
        preKeyCalleeSavedAt sp' s0))
    (by apply entails_of_eq; rw [stackAt_bytesMerge_split_int32 sp']; ac_rfl) ?_
  refine SepWPp.frame_tryFrom
    (step_field8_placed_wp hbytes hlt7 hpc8 hrun8 hregs8 hsp8 hcl8 htr8 hx2_8)
    fun sf Pf ⟨hregsf, hspf, hclf, htrf, hx24f, kyberCap, kyberPtr, hentf⟩ =>
      ⟨hregsf, hspf, hclf, htrf, hx24f,
        opkVal, kyberCap, kyberPtr, bkCap, bkPtr, ikCap, ikPtr, msgCap, msgPtr, hopkVal, ?_⟩
  refine Entails.trans (sepConj_mono_left hentf) ?_
  have hcur8 : sliceCursorAt (sp' + 296#64) (cur8 x) (psmRem8 x) =
      ((sp' + 296#64) ↦₆₄ cur8 x) ∗ ((sp' + 304#64) ↦₆₄ 0#64) := by
    unfold sliceCursorAt psmRem8
    simp only [List.length_nil, pointsToBytes_nil,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
  rw [hcur8, ← pointsToBytes_psm_reassemble x]
  apply entails_of_eq; ac_rfl

end CryptoVerification.E2E.Pqxdh.ResponderWire
