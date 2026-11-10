/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.L1GX.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.MF14Aux.Decodes
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.MF14Aux.Helpers
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32Merge
import ProofLib.SepLogic.WPp

/-!
# `SessionStructure::merge_field` on tag 14 (`pending_kyber_pre_key`)

Proves `mergeFieldX14_ok` (`0x581c`) on `GenFieldX.kyber i ct` (arbitrary `u32` `pre_key_id`
and 1569-byte ciphertext) starting from `pending_kyber_pre_key = None`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.L1GX.Leaf.MergeFieldX14

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.L1GX CryptoVerification.E2E.Record.L1GX.Leaf.MF14Aux
open CryptoVerification.E2E.Record.Serialization (OkAt allocPanic)

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

attribute [local irreducible] Program.fetch Program.externAt? sessionImg0
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  kyberB0_signExtend_getLsbD_63 kyberB0_signExtend_getLsbD_63_beq
attribute [local wp_norm] kyberB0_signExtend_getLsbD_63 kyberB0_signExtend_getLsbD_63_beq

private theorem wt_and_ff_eq_mf14 (r2 : BitVec 64) (hx2 : r2.setWidth 8 = 2#8) :
    r2.truncate 32 &&& 255#32 = 2#32 := by
  apply BitVec.eq_of_toNat_eq
  have h := congrArg BitVec.toNat hx2
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_and, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat] at h ⊢
  change (r2.toNat % 4294967296 &&& (2 ^ 8 - 1)) = 2
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

private theorem wt_and_ff_64_eq_mf14 (r2 : BitVec 64) (hx2 : r2.setWidth 8 = 2#8) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 r2) &&& 255#64) = 2#32 := by
  apply BitVec.eq_of_toNat_eq
  have h := congrArg BitVec.toNat hx2
  simp only [BitVec.truncate_eq_setWidth,
    BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat] at h ⊢
  change (((r2.toNat % 4294967296) % 18446744073709551616 &&& (2 ^ 8 - 1)) % 4294967296) = 2
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

private theorem post_of_decode_mf14 {ct : List (BitVec 8)} (hct : ct.length = 1569)
    (tail : List (BitVec 8)) (ptr sp0 : BitVec 64) (sm sf : State)
    (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.decodeVarintSliceSpec A0).post
        ⟨sp0 - 232#64, ptr, 164#8 :: 12#8 :: 18#8 :: innerBytes ct tail⟩ sm sf ∗ Fr =
      ⌜sf.trace = sm.trace⌝ ∗ ((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
        ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 1572) ∗ ((sp0 - 216#64) ↦₆₄ 2#64) ∗
        (ptr ↦₈ 164#8) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 18#8) ∗
        ((ptr + 3#64) ↦ₛ innerBytes ct tail) ∗
        stackAt (sp0 - 240#64) Prost.decodeVarintSliceStack ∗ Fr := by
  dsimp only [Prost.decodeVarintSliceSpec]
  rw [decode_kyber_result_mf14 hct, hsp, bytes_kyber_split_mf14, pointsTo64_zero_split32_mf14,
    show sp0 - 232#64 + 8#64 = sp0 - 224#64 by bv_omega,
    show sp0 - 232#64 + 16#64 = sp0 - 216#64 by bv_omega,
    show A0.pool = emp from rfl, emp_sepConj]
  simp only [sepConj_assoc]

private theorem post_of_bytesMerge_mf14 (ss bufRef slot ptr sp0 : BitVec 64)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8))
    (sm sf : State) (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.bytesMergeRawSpec A0).post
        ⟨.lengthDelimited, ss + 296#64, 0#64, 1#64, [], bufRef, slot, ptr + 3#64,
          innerBytes ct tail⟩ sm sf ∗
      (memRegion (sp0 - 240#64 - 16144#64) 7648 ∗ Fr) =
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜sf.trace = sm.trace⌝ ∗ ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        ⌜Prost.BytesMergeCapOk cap' tail.length⌝ ∗
        vecU8At A0 (ss + 296#64) cap' ptr' ct ∗ (bufRef ↦₆₄ slot) ∗
        (slot ↦₆₄ (ptr + 1574#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
        ((ptr + 3#64) ↦ₛ innerBytes ct tail) ∗
        stackAt (sp0 - 240#64) mergeFieldSubStack_mf14 ∗ Fr) := by
  have hpool : A0.pool = emp := rfl
  dsimp only [Prost.bytesMergeRawSpec]
  rw [mergeBytes_inner hct tail]
  dsimp only
  rw [hsp, sliceCursorAfter_inner_unfold_mf14 slot ptr hct tail,
      stackAt_sub_to_bytesMerge_mf14 (sp0 - 240#64), hpool, emp_sepConj]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine congrArg sepExists (funext fun cap' => congrArg sepExists (funext fun ptr' => ?_))
  ac_rfl

private theorem final_post_entails_mf14 (ss cap' ptr' : BitVec 64) (v : SSGX)
    (bufRef slot ptr : BitVec 64) {ct : List (BitVec 8)} (hct : ct.length = 1569)
    (tail : List (BitVec 8))
    (sp0 r29 r30 r25 w56 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    (vecU8At A0 (ss + 296#64) cap' ptr' ct ∗ (bufRef ↦₆₄ slot) ∗
      (slot ↦₆₄ (ptr + 1574#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      ((ptr + 3#64) ↦ₛ innerBytes ct tail) ∗
      stackAt (sp0 - 240#64) mergeFieldSubStack_mf14 ∗
      ((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
      ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 1572) ∗ ((sp0 - 216#64) ↦₆₄ 2#64) ∗
      (ptr ↦₈ 164#8) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 18#8) ∗
      ((ss + 320#64) ↦₃₂ 0#32) ∗ memRegion (ss + 324#64) 4 ∗ restX14 A0 ss v ∗
      ((sp0 - 80#64) ↦₆₄ r29) ∗ ((sp0 - 72#64) ↦₆₄ r30) ∗
      ((sp0 - 64#64) ↦₆₄ r25) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ r24) ∗ ((sp0 - 40#64) ↦₆₄ r23) ∗
      ((sp0 - 32#64) ↦₆₄ r22) ∗ ((sp0 - 24#64) ↦₆₄ r21) ∗
      ((sp0 - 16#64) ↦₆₄ r20) ∗ ((sp0 - 8#64) ↦₆₄ r19) ∗
      memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 208#64) 128) ⊢
    prostSSGXAt A0 ss (v.apply (GenFieldX.kyber 0#32 ct)) ∗
      (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAfter slot ptr ((GenFieldX.kyber 0#32 ct).payload ++ tail) tail ∗
      stackAt sp0 mergeFieldStack := by
  rw [← sliceCursorAfter_kyber_fold_mf14 slot ptr hct tail]
  refine Entails.trans (Q :=
    (vecU8At A0 (ss + 296#64) cap' ptr' ct ∗ ((ss + 320#64) ↦₃₂ 0#32) ∗
      memRegion (ss + 324#64) 4 ∗ restX14 A0 ss v) ∗
    (bufRef ↦₆₄ slot) ∗
    ((slot ↦₆₄ (ptr + 1574#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ 164#8) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 18#8) ∗
      ((ptr + 3#64) ↦ₛ innerBytes ct tail)) ∗
    ((((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
      ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 1572) ∗ ((sp0 - 216#64) ↦₆₄ 2#64)) ∗
      (((sp0 - 80#64) ↦₆₄ r29) ∗ ((sp0 - 72#64) ↦₆₄ r30) ∗
      ((sp0 - 64#64) ↦₆₄ r25) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ r24) ∗ ((sp0 - 40#64) ↦₆₄ r23) ∗
      ((sp0 - 32#64) ↦₆₄ r22) ∗ ((sp0 - 24#64) ↦₆₄ r21) ∗
      ((sp0 - 16#64) ↦₆₄ r20) ∗ ((sp0 - 8#64) ↦₆₄ r19) ∗
      memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 208#64) 128 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStack_mf14)))
    (Entails.of_eq (by ac_rfl)) ?_
  refine sepConj_mono (prostSSGXAt_kyber_some_fold A0 ss cap' ptr' v 0#32 ct) ?_
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine Entails.trans (sepConj_mono (cells24_entails_memRegion24_mf14 sp0 _ _)
    (Entails.refl _)) ?_
  refine Entails.trans ?_ (stackAt_mergeField_fold_mf14 sp0 r29 r30 r25 w56 r24 r23 r22 r21 r20 r19)
  rw [← memRegion160_fold_mf14]
  exact Entails.of_eq (by ac_rfl)

/-! ## Postcondition assembly for `i ≠ 0#32` -/

private theorem post_of_decode_ne_mf14 (i : BitVec 32) {ct : List (BitVec 8)} (hct : ct.length =
    1569)
    (tail : List (BitVec 8)) (ptr sp0 : BitVec 64) (sm sf : State)
    (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.decodeVarintSliceSpec A0).post
        ⟨sp0 - 232#64, ptr, kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail⟩ sm sf ∗ Fr =
      ⌜sf.trace = sm.trace⌝ ∗ ((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
        ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
        ((sp0 - 216#64) ↦₆₄ 2#64) ∗
        (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
        ((ptr + 3#64) ↦ₛ kyberIdBytes i ct tail) ∗
        stackAt (sp0 - 240#64) Prost.decodeVarintSliceStack ∗ Fr := by
  dsimp only [Prost.decodeVarintSliceSpec]
  rw [decode_kyber_ne_result_mf14 i hct, hsp, bytes_kyber_ne_split_mf14,
      pointsTo64_zero_split32_mf14,
    show sp0 - 232#64 + 8#64 = sp0 - 224#64 by bv_omega,
    show sp0 - 232#64 + 16#64 = sp0 - 216#64 by bv_omega,
    show A0.pool = emp from rfl, emp_sepConj]
  simp only [sepConj_assoc]

private theorem pre_to_int32Merge_ne_mf14 (ss bufRef slot ptr sp0 : BitVec 64) (i : BitVec 32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8)) (Fr : SepProp) :
    ((ss + 320#64) ↦₃₂ 0#32) ∗ (bufRef ↦₆₄ slot) ∗
      (slot ↦₆₄ (ptr + 3#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1572 + (encodeVarint (i.setWidth 64)).length +
        tail.length)) ∗
      ((ptr + 3#64) ↦ₛ kyberIdBytes i ct tail) ∗
      memRegion (sp0 - 240#64 - 16144#64) 7872 ∗
      stackAt (sp0 - 240#64) Prost.decodeVarintSliceStack ∗ Fr ⊢
    (memRegion (ss + 320#64) 4 ∗ (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAt slot (ptr + 3#64) (kyberIdBytes i ct tail) ∗ A0.pool ∗
      stackAt (sp0 - 240#64) Prost.int32MergeStack) ∗
    (memRegion (sp0 - 240#64 - 16144#64) 7792 ∗ Fr) := by
  have hpool : A0.pool = emp := rfl
  rw [← sliceCursorAt_kyberId_fold_mf14 slot ptr i hct tail, hpool, emp_sepConj]
  refine Entails.trans (sepConj_mono_left (Prost.pointsTo32_entails_memRegion4 (ss +
      320#64) 0#32)) ?_
  apply Entails.of_eq
  rw [← sepConj_assoc (memRegion (sp0 - 240#64 - 16144#64) 7872),
      decode_to_int32Merge_stack_mf14 (sp0 - 240#64)]
  ac_rfl

private theorem call_alloc_entails_mf14 {α β : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s s0 : State} {P R : SepProp} {Q : State → SepProp → Prop} {y : β}
    (hcall : subroutine_ok prog entry spec)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P ⊢ T ∗ F)
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝)
    (hpan : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap))
    (htr : s.trace = s0.trace)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ allocPanic y s0 sf ∗ R)))
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ allocPanic y s0 sf ∗ R)) := by
  intro R' hm hL
  exact call_alloc_mf14 hcall hfl hsym hpc hrun hsp hlr hspec hφ rfl hexit hpan htr hnext hoom R'
    (Satisfies.mono (sepConj_mono_left hP) hm) hL

private theorem post_of_int32Merge_ne_mf14 (ss bufRef slot ptr sp0 : BitVec 64) (i : BitVec 32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8))
    (sm sf : State) (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.int32MergeSpec A0).post
        ⟨.varint, ss + 320#64, bufRef, slot, ptr + 3#64, kyberIdBytes i ct tail⟩ sm sf ∗ Fr =
      ⌜sf.trace = sm.trace⌝ ∗ ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        ((ss + 320#64) ↦₃₂ i) ∗ (bufRef ↦₆₄ slot) ∗
        (slot ↦₆₄ kyberPtr2 ptr i) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1572 + tail.length)) ∗
        ((ptr + 3#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
        (kyberPtr2 ptr i ↦₈ 18#8) ∗
        ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail) ∗
        stackAt (sp0 - 240#64) Prost.int32MergeStack ∗ Fr := by
  have hpool : A0.pool = emp := rfl
  dsimp only [Prost.int32MergeSpec]
  rw [mergeUint32_kyberIdBytes i tail]
  dsimp only
  rw [hsp, sliceCursorAfter_kyberId_unfold_mf14 slot ptr i hct tail, hpool, emp_sepConj]
  simp only [sepConj_assoc]
  ac_rfl

private theorem post_of_bytesMerge_ne_mf14 (ss bufRef slot ptr sp0 : BitVec 64) (i : BitVec 32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8))
    (sm sf : State) (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.bytesMergeRawSpec A0).post
        ⟨.lengthDelimited, ss + 296#64, 0#64, 1#64, [], bufRef, slot, kyberPtr2 ptr i + 1#64,
          innerBytes ct tail⟩ sm sf ∗
      (memRegion (sp0 - 240#64 - 16144#64) 7648 ∗ Fr) =
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜sf.trace = sm.trace⌝ ∗ ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        ⌜Prost.BytesMergeCapOk cap' tail.length⌝ ∗
        vecU8At A0 (ss + 296#64) cap' ptr' ct ∗ (bufRef ↦₆₄ slot) ∗
        (slot ↦₆₄ (kyberPtr2 ptr i + 1572#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
        ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail) ∗
        stackAt (sp0 - 240#64) mergeFieldSubStack_mf14 ∗ Fr) := by
  have hpool : A0.pool = emp := rfl
  dsimp only [Prost.bytesMergeRawSpec]
  rw [mergeBytes_inner hct tail]
  dsimp only
  rw [hsp, sliceCursorAfter_inner_ne_unfold_mf14 slot ptr i hct tail,
      stackAt_sub_to_bytesMerge_mf14 (sp0 - 240#64), hpool, emp_sepConj]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine congrArg sepExists (funext fun cap' => congrArg sepExists (funext fun ptr' => ?_))
  ac_rfl

private theorem final_post_entails_ne_mf14 (ss cap' ptr' : BitVec 64) (v : SSGX)
    (bufRef slot ptr : BitVec 64) {i : BitVec 32} (hi : i ≠ 0#32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8))
    (sp0 r29 r30 r25 w56 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    (vecU8At A0 (ss + 296#64) cap' ptr' ct ∗ (bufRef ↦₆₄ slot) ∗
      (slot ↦₆₄ (kyberPtr2 ptr i + 1572#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail) ∗
      stackAt (sp0 - 240#64) mergeFieldSubStack_mf14 ∗
      ((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
      ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
      ((sp0 - 216#64) ↦₆₄ 2#64) ∗
      (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
      ((ptr + 3#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
      (kyberPtr2 ptr i ↦₈ 18#8) ∗
      ((ss + 320#64) ↦₃₂ i) ∗ memRegion (ss + 324#64) 4 ∗ restX14 A0 ss v ∗
      ((sp0 - 80#64) ↦₆₄ r29) ∗ ((sp0 - 72#64) ↦₆₄ r30) ∗
      ((sp0 - 64#64) ↦₆₄ r25) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ r24) ∗ ((sp0 - 40#64) ↦₆₄ r23) ∗
      ((sp0 - 32#64) ↦₆₄ r22) ∗ ((sp0 - 24#64) ↦₆₄ r21) ∗
      ((sp0 - 16#64) ↦₆₄ r20) ∗ ((sp0 - 8#64) ↦₆₄ r19) ∗
      memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 208#64) 128) ⊢
    prostSSGXAt A0 ss (v.apply (GenFieldX.kyber i ct)) ∗
      (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAfter slot ptr ((GenFieldX.kyber i ct).payload ++ tail) tail ∗
      stackAt sp0 mergeFieldStack := by
  rw [← sliceCursorAfter_kyber_ne_fold_mf14 slot ptr hi hct tail]
  refine Entails.trans (Q :=
    (vecU8At A0 (ss + 296#64) cap' ptr' ct ∗ ((ss + 320#64) ↦₃₂ i) ∗
      memRegion (ss + 324#64) 4 ∗ restX14 A0 ss v) ∗
    (bufRef ↦₆₄ slot) ∗
    ((slot ↦₆₄ (kyberPtr2 ptr i + 1572#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
      ((ptr + 3#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
      (kyberPtr2 ptr i ↦₈ 18#8) ∗
      ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail)) ∗
    ((((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
      ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
      ((sp0 - 216#64) ↦₆₄ 2#64)) ∗
      (((sp0 - 80#64) ↦₆₄ r29) ∗ ((sp0 - 72#64) ↦₆₄ r30) ∗
      ((sp0 - 64#64) ↦₆₄ r25) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ r24) ∗ ((sp0 - 40#64) ↦₆₄ r23) ∗
      ((sp0 - 32#64) ↦₆₄ r22) ∗ ((sp0 - 24#64) ↦₆₄ r21) ∗
      ((sp0 - 16#64) ↦₆₄ r20) ∗ ((sp0 - 8#64) ↦₆₄ r19) ∗
      memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 208#64) 128 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStack_mf14)))
    (Entails.of_eq (by ac_rfl)) ?_
  refine sepConj_mono (prostSSGXAt_kyber_some_fold A0 ss cap' ptr' v i ct) ?_
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine Entails.trans (sepConj_mono (cells24_entails_memRegion24_mf14 sp0 _ _)
    (Entails.refl _)) ?_
  refine Entails.trans ?_ (stackAt_mergeField_fold_mf14 sp0 r29 r30 r25 w56 r24 r23 r22 r21 r20 r19)
  rw [← memRegion160_fold_mf14]
  exact Entails.of_eq (by ac_rfl)

private theorem sat_pure_true_mf14 {m : Memory} {φ : Prop} {X R : SepProp} (hφ : φ)
    (h : m ⊨ (X ∗ emp) ∗ R) : m ⊨ (⌜φ⌝ ∗ X) ∗ R := by
  rw [sepConj_emp] at h
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hφ, h⟩

/-- `SessionStructure::merge_field` contract for tag 14 (`pending_kyber_pre_key`, wire type 2, 1569-byte ciphertext). -/
theorem mergeFieldX14_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) :
    MergeFieldXOk C ctl (fun fl => fl.tag = 14) abs := by
  dsimp only [MergeFieldXOk, OkAt]
  apply subroutine_ok_of_sepWPp
  intro ⟨ss, v, fld, bufRef, slot, ptr, tail⟩ R s0 hpc hrun hpre hsp_align
  refine ⟨(mergeFieldXSpec (fun fl => fl.tag = 14)).pre
    ⟨ss, v, fld, bufRef, slot, ptr, tail⟩ s0, R, hpre, ?_⟩
  clear hpre
  dsimp only [mergeFieldXSpec]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, hx4, htag, hOk, hFresh, hlen, hF0, hsym0⟩ => ?_
  obtain ⟨i, ct, rfl⟩ := (genFieldX_tag_eq_14_iff fld).mp htag
  have hct : ct.length = 1569 := hOk
  have hk : v.ext.kyber = none := hFresh
  dsimp only [GenFieldX.tag, GenFieldX.wt, WireType.toNat] at hx1 hx2
  have hx1_tr : BitVec.truncate 32 (s0.readReg64 .x1) = 14#32 := hx1
  have hx4_tr : BitVec.truncate 32 (s0.readReg64 .x4) = 99#32 := hx4
  rw [State.spAligned] at hsp_align
  have hb : sessionImg0.base &&& 4095#64 = 0#64 :=
    base_aligned_of_loads E2E.Record.loads_sessionImg0
  have hcallD := decodeVarintSlice_ok_sub_mf14 hC.1
  have hcallI := int32Merge_ok_sub_mf14 hC.2.1
  have hcallB := bytesMerge_ok_sub_mf14 hC.2.2.1
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
    (b := sessionImg0.base) (H := H)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x581c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 4)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5820
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 8)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5824
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 12)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5828
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 16)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x582c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 20)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5830
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 24)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5834
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 28)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5838
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 32)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x583c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 36)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5840
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 40)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5844
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 44)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5848
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 48)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x584c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 52)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5850
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 56)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5854
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 60)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5858
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 368)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x598c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 372)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5990
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 376)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5994
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 380)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5998
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 384)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x599c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 388)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x59a0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 392)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x59a4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 396)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x59a8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 400)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x59ac
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 404)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x59b0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 408)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x59b4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 412)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x59b8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 416)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x59bc
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 420)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x59c0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 424)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x59c4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 428)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x59c8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1208)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5cd4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1212)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5cd8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1216)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5cdc
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1220)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5ce0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1224)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5ce4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1228)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5ce8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1232)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5cec
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1236)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5cf0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1240)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5cf4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1244)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5cf8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1248)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5cfc
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1252)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5d00
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1320)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5d44
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1324)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5d48
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1328)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5d4c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1332)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5d50
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1336)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5d54
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1340)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5d58
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1344)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5d5c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1348)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5d60
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1352)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5d64
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1356)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5d68
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1360)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5d6c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1364)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5d70
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1368)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5d74
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1372)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5d78
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1376)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5d7c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1380)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5d80
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1384)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5d84
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1388)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5d88
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1392)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5d8c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1396)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5d90
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1400)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5d94
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1404)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5d98
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1408)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5d9c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1412)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5da0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1416)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5da4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1420)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5da8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1424)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5dac
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1428)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5db0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1432)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5db4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1436)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5db8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1440)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5dbc
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1444)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5dc0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1448)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5dc4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1452)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5dc8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1456)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5dcc
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1460)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5dd0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1464)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5dd4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1468)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5dd8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1472)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5ddc
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1476)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5de0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1480)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5de4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1484)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5de8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1488)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5dec
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1492)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5df0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1496)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5df4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1500)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5df8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1504)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5dfc
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1508)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e00
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1512)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e04
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1516)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e08
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1520)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e0c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1524)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e10
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1528)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e14
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1532)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e18
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1536)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e1c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1540)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e20
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1544)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e24
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1548)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e28
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1552)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e2c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1556)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e30
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1560)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e34
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1564)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e38
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1568)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e3c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1572)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e40
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1576)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e44
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1580)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e48
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1584)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e4c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1588)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e50
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1592)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e54
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1596)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e58
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1600)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e5c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1604)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e60
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1608)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e64
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1612)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e68
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1616)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e6c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1620)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e70
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1624)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e74
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1628)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e78
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1632)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e7c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1636)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e80
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1640)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e84
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1644)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e88
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1648)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e8c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1652)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e90
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1656)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e94
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1660)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e98
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1664)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5e9c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1668)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5ea0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1672)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5ea4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1676)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5ea8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1680)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5eac
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1684)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5eb0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1688)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5eb4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1692)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5eb8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1696)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5ebc
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1700)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5ec0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1704)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5ec4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1708)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5ec8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1712)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5ecc
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1716)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5ed0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1720)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5ed4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1724)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5ed8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1880)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5f74
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1884)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5f78
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1888)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5f7c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1892)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5f80
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1896)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5f84
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1900)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5f88
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1904)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x5f8c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2328)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x6134
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2332)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x6138
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2336)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x613c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2340)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x6140
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2344)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x6144
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2348)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x6148
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2352)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x614c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 2356)
    mergeField_fnOff_mf14 (by decide) mf14_decode_0x6150
  dsimp only [tripleRatchetProgAt] at hpc hcallD hcallI hcallB ⊢
  have hx2_tr : (s0.readReg64 (Reg.gpr 2#5)).truncate 32 &&& 255#32 = 2#32 :=
    wt_and_ff_eq_mf14 (s0.readReg64 .x2) hx2
  have hx2_64 : BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr
      2#5))) &&& 255#64) = 2#32 :=
    wt_and_ff_64_eq_mf14 (s0.readReg64 .x2) hx2
  have hadrp :
      (((libsignalSessionCode.rebase sessionImg0.base
        (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr mergeFieldName + 40#64) &&&
        18446744073709547520#64) + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" - 0x5000) = sessionImg0.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d") := by
    rw [Program.fnAddr_rebase, CryptoVerification.libsignalSessionCode_fnOff_0x581c]
    exact adrp_rodata_mf14 sessionImg0.base hb
  have hfetch_0x34 := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := Rust.withPanics (tripleRatchetExterns C ctl abs))
    (k := 52) mergeField_fnOff_mf14 (by decide)
    mf14_decode_0x5850
  generalize_entry (libsignalSessionCode.rebase sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr mergeFieldName = entry
  examples_hide_fetches
  by_cases hi : i = 0#32
  · subst hi
    rw [kyber_payload_tail_length hct] at hlen
    have hL_ne0 : (BitVec.ofNat 64 (1574 + tail.length) == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro heq
      have h1 := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at h1; omega
    have hL_ule10 : BitVec.ule (BitVec.ofNat 64 (1574 + tail.length)) 10#64 = false := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hL_ult10 : BitVec.ult 10#64 (BitVec.ofNat 64 (1574 + tail.length)) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    conv =>
      arg 4
      rw [prostSSGXAt_kyber_none_unfold A0 ss v hk,
          sliceCursorAt_kyber_unfold_mf14 slot ptr hct tail,
          bytes_kyber_split_mf14,
          stackAt_mergeField_unfold_mf14 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun w130 => SepWPp.exists_elim fun w138 =>
      SepWPp.exists_elim fun w140 => SepWPp.exists_elim fun v80 =>
      SepWPp.exists_elim fun v72 => SepWPp.exists_elim fun v64 =>
      SepWPp.exists_elim fun v56 => SepWPp.exists_elim fun v48 =>
      SepWPp.exists_elim fun v40 => SepWPp.exists_elim fun v32 =>
      SepWPp.exists_elim fun v24 => SepWPp.exists_elim fun v16 =>
      SepWPp.exists_elim fun v8 => ?_
    apply of_sepWP_frozen_mf14 hF0 hsym0 (mid := entry + 52#64)
    iterate 13 wp_step
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    intro hF1 hsym1
    obtain ⟨hread14, hcan14⟩ := rodata_jump_tag14_mf14 hF1
    apply of_sepWP_frozen_mf14 hF1 hsym1 (mid := entry + 118436#64)
    refine step_ldr8_ro_mf14 (pc := entry + 52#64) (pc' := entry + 56#64)
      (r := Reg.gpr 11#5) (v64 := 76#64)
      rfl (by simp only [wp_norm, arm64_norm, hrun]) hfetch_0x34 rfl
      (ea := sessionImg0.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 13)) (wb := none)
      (by simp only [evalAddrMode, wp_norm, arm64_norm])
      hread14 hcan14 (by simp only [applyWriteback, wp_norm, arm64_norm]) ?_
    iterate 25 wp_step
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    intro hF2 hsym2
    refine call_alloc_mf14 (s0 := s0) (R := R)
      (x := (⟨s0.sp - 232#64, ptr, 164#8 :: 12#8 :: 18#8 :: innerBytes ct tail⟩ :
        Prost.DecodeVarintSliceGhost))
      (T := memRegion (s0.sp - 232#64) 24 ∗
        (ptr ↦ₛ (164#8 :: 12#8 :: 18#8 :: innerBytes ct tail)) ∗ A0.pool ∗
        stackAt (s0.sp - 240#64) Prost.decodeVarintSliceStack)
      (F := memRegion (s0.sp - 240#64 - 16144#64) 7872 ∗
        ((ss + 296#64) ↦₆₄ 0#64) ∗ ((ss + 304#64) ↦₆₄ 1#64) ∗ ((ss + 312#64) ↦₆₄ 0#64) ∗
        ((ss + 320#64) ↦₃₂ 0#32) ∗ memRegion (ss + 324#64) 4 ∗ restX14 A0 ss v ∗
        (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1574 + tail.length)) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ v80) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        memRegion (s0.sp - 240#64) 8 ∗ memRegion (s0.sp - 208#64) 128)
      hcallD hF2 hsym2
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned]; simpa only [wp_norm, arm64_norm] using hsp_align)
      rfl
      (by simp only [Prost.decodeVarintSliceSpec, wp_norm, arm64_norm]; rfl)
      ?_
      (by rw [bytes_kyber_split_mf14, show A0.pool = emp from rfl, emp_sepConj]; ac_rfl)
      (fun _ _ => rfl) (fun _ => rfl)
      (by simp only [wp_norm, arm64_norm])
      ?_
    · refine ⟨?_, ?_, Or.inl ?_⟩ <;>
        simp only [List.length_cons, innerBytes_length hct, BitVec.toNat_ofNat] <;> omega
    intro sf hpcf hrunf hspf hcsf hF3 hsym3
    simp only [wp_norm, arm64_norm] at hpcf
    have hsp_sf : sf.sp = s0.sp - 240#64 := by
      simpa only [wp_norm, arm64_norm] using hspf
    have hx19_sf : sf.readReg64 (Reg.gpr 19#5) = slot := by
      simpa only [wp_norm, arm64_norm] using hcsf.1
    have hx20_sf : sf.readReg64 (Reg.gpr 20#5) = 99#64 := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.1
    have hx21_sf : sf.readReg64 (Reg.gpr 21#5) = ss := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.1
    have hx22_sf : sf.readReg64 (Reg.gpr 22#5) = bufRef := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.1
    rw [post_of_decode_mf14 hct tail ptr s0.sp _ sf (by simp only [wp_norm, arm64_norm])]
    refine SepWPp.pure_elim fun htr_sf => ?_
    have hc_ult2 : BitVec.ult (BitVec.ofNat 64 (1574 + tail.length)) 2#64 = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_sub2 : BitVec.ofNat 64 (1574 + tail.length) - 2#64 =
        BitVec.ofNat 64 (1572 + tail.length) := len_sub_mf14 (by omega) (by omega)
    have hc_ult1572 : BitVec.ult (BitVec.ofNat 64 (1572 + tail.length)) 1572#64 = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_sub1572 : BitVec.ofNat 64 (1572 + tail.length) - 1572#64 =
        BitVec.ofNat 64 tail.length := by
      have := len_sub_mf14 (a := 1572) (b := 1572) (n := tail.length) (by omega) (by omega)
      simpa using this
    have hc_ule1572 : BitVec.ule 1572#64 (BitVec.ofNat 64 (1572 + tail.length)) = true := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hc_ule_n2 : BitVec.ule (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 (1572 + tail.length)) = true := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hc_ult_n : BitVec.ult (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 (1572 + tail.length)) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hc_ult_n2 : BitVec.ult (BitVec.ofNat 64 (1572 + tail.length))
        (BitVec.ofNat 64 tail.length) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_ule_n : BitVec.ule (BitVec.ofNat 64 (1572 + tail.length))
        (BitVec.ofNat 64 tail.length) = false := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_eq_n : (BitVec.ofNat 64 (1572 + tail.length) == BitVec.ofNat 64 tail.length) =
      false := by
      rw [beq_eq_false_iff_ne]; intro heq
      have h1 := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at h1; omega
    have hc_sub1 : BitVec.ofNat 64 (1572 + tail.length) - 1#64 =
        BitVec.ofNat 64 (1571 + tail.length) := len_sub_mf14 (by omega) (by omega)
    apply of_sepWP_frozen_mf14 hF3 hsym3 (mid := entry + 18446744073709539180#64)
    have htr_sf' : sf.trace = s0.trace := by
      simpa only [wp_norm, arm64_norm] using htr_sf
    have hx26_sf : sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.1
    have hx27_sf : sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.1
    have hx28_sf : sf.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.1
    have hcsv_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.2.2
    iterate 47 wp_step
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm,
      hrunf])
    intro hF4 hsym4
    refine call_alloc_mf14 (s0 := s0) (R := R)
      (x := (⟨.lengthDelimited, ss + 296#64, 0#64, 1#64, [], bufRef, slot, ptr + 3#64,
        innerBytes ct tail⟩ : Prost.BytesMergeGhost))
      (T := vecU8At A0 (ss + 296#64) 0#64 1#64 [] ∗ (bufRef ↦₆₄ slot) ∗
        Prost.sliceCursorAt slot (ptr + 3#64) (innerBytes ct tail) ∗ A0.pool ∗
        stackAt (s0.sp - 240#64) Prost.bytesMergeStack)
      (F := memRegion (s0.sp - 240#64 - 16144#64) 7648 ∗
        ((s0.sp - 232#64) ↦₃₂ 0#32) ∗ ((s0.sp - 228#64) ↦₃₂ 0#32) ∗
        ((s0.sp - 224#64) ↦₆₄ BitVec.ofNat 64 1572) ∗ ((s0.sp - 216#64) ↦₆₄ 2#64) ∗
        (ptr ↦₈ 164#8) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 18#8) ∗
        ((ss + 320#64) ↦₃₂ 0#32) ∗ memRegion (ss + 324#64) 4 ∗ restX14 A0 ss v ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ v80) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        memRegion (s0.sp - 240#64) 8 ∗ memRegion (s0.sp - 208#64) 128)
      hcallB hF4 hsym4
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrunf])
      (by rw [State.spAligned]; simpa only [wp_norm, arm64_norm, hsp_sf] using hsp_align)
      rfl
      (by
        dsimp only [Prost.bytesMergeSpec, Spec.inImage, Prost.bytesMergeRawSpec]
        rw [pure_sepConj_pure_assoc]
        congr 1
        simp only [wp_norm, arm64_norm, hsp_sf])
      (by exact ⟨⟨hF4, hsym4⟩, by simp only [wp_norm, arm64_norm, WireType.toNat],
        by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
        by simp only [innerBytes_length hct]; omega, Prost.bytesMergeCapOk_zero⟩)
      (by
        rw [← emptyVec_kyber_eq_vecU8At, ← sliceCursorAt_inner_fold_mf14 slot ptr hct tail,
          show A0.pool = emp from rfl, emp_sepConj,
          ← sepConj_assoc (stackAt _ _), sepConj_comm (stackAt _ _),
          decode_to_bytesMerge_stack_mf14]
        ac_rfl)
      (fun _ _ => rfl) (fun _ => rfl)
      (by simp only [wp_norm, arm64_norm, htr_sf'])
      ?_
    intro sf2 hpcf2 hrunf2 hspf2 hcsf2 _ _
    simp only [wp_norm, arm64_norm] at hpcf2
    have hsp_sf2 : sf2.sp = s0.sp - 240#64 := by
      simpa only [wp_norm, arm64_norm, hsp_sf] using hspf2
    dsimp only [Prost.bytesMergeSpec, Spec.inImage]
    rw [post_of_bytesMerge_mf14 ss bufRef slot ptr s0.sp hct tail _ sf2
      (by simp only [wp_norm, arm64_norm, hsp_sf])]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' =>
      SepWPp.pure_elim fun htr_sf2 => SepWPp.pure_elim fun hx0_sf2 =>
      SepWPp.pure_elim fun _hcapOk => ?_
    have htr_sf2' : sf2.trace = s0.trace := by
      simpa only [wp_norm, arm64_norm, htr_sf'] using htr_sf2
    have hx0_sf2' : sf2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_sf2
    have hx26_sf2 : sf2.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
      simpa only [wp_norm, arm64_norm, hx26_sf] using hcsf2.2.2.2.2.2.2.2.1
    have hx27_sf2 : sf2.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
      simpa only [wp_norm, arm64_norm, hx27_sf] using hcsf2.2.2.2.2.2.2.2.2.1
    have hx28_sf2 : sf2.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
      simpa only [wp_norm, arm64_norm, hx28_sf] using hcsf2.2.2.2.2.2.2.2.2.2.1
    have hcsv_sf2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0 := by
      simpa only [wp_norm, arm64_norm, hcsv_sf] using hcsf2.2.2.2.2.2.2.2.2.2.2.2
    have hx21_sf2 : sf2.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
      simpa only [wp_norm, arm64_norm] using hcsf2.2.2.1
    have hx22_sf2 : sf2.readReg64 (Reg.gpr 22#5) = bufRef := by
      simpa only [wp_norm, arm64_norm] using hcsf2.2.2.2.1
    have htail_ult_self : BitVec.ult (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 tail.length) = false := by
      simp [BitVec.ult]
    have htail_ule_self : BitVec.ule (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 tail.length) = true := by
      simp [BitVec.ule]
    apply SepWPp.of_sepWP_ret
    iterate 19 wp_step
    apply SepWP.fold (final_post_entails_mf14 ss cap' ptr' v bufRef slot ptr hct tail s0.sp
      (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 25#5)) v80
      (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
      (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
      (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
      (sepConj_emp _).symm
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm,
      hrunf2])
    refine ⟨fun hmf => sat_pure_true_mf14 ⟨?_, ?_⟩ hmf,
      by simp only [wp_norm, arm64_norm],
      by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, hx26_sf2, hx27_sf2, hx28_sf2,
        hcsv_sf2, and_self]⟩
    · simp only [wp_norm, arm64_norm, htr_sf2']
    · simp only [wp_norm, arm64_norm]
  · -- Non-zero `pre_key_id` (`i ≠ 0#32`)
    have hm_bounds := encodeVarint_length_bounds_mf14 (i.setWidth 64)
    rw [kyber_ne_payload_tail_length hi hct] at hlen
    have hL_ne0 : (BitVec.ofNat 64 (1575 + (encodeVarint (i.setWidth 64)).length +
      tail.length) == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro heq
      have h1 := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at h1; omega
    have hL_ule10 : BitVec.ule (BitVec.ofNat 64 (1575 + (encodeVarint (i.setWidth 64)).length +
      tail.length)) 10#64 = false := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hL_ult10 : BitVec.ult 10#64 (BitVec.ofNat 64 (1575 +
      (encodeVarint (i.setWidth 64)).length + tail.length)) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    conv =>
      arg 4
      rw [prostSSGXAt_kyber_none_unfold A0 ss v hk,
          sliceCursorAt_kyber_ne_unfold_mf14 slot ptr hi hct tail,
          bytes_kyber_ne_split_mf14,
          stackAt_mergeField_unfold_mf14 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun w130 => SepWPp.exists_elim fun w138 =>
      SepWPp.exists_elim fun w140 => SepWPp.exists_elim fun v80 =>
      SepWPp.exists_elim fun v72 => SepWPp.exists_elim fun v64 =>
      SepWPp.exists_elim fun v56 => SepWPp.exists_elim fun v48 =>
      SepWPp.exists_elim fun v40 => SepWPp.exists_elim fun v32 =>
      SepWPp.exists_elim fun v24 => SepWPp.exists_elim fun v16 =>
      SepWPp.exists_elim fun v8 => ?_
    apply of_sepWP_frozen_mf14 hF0 hsym0 (mid := entry + 52#64)
    iterate 13 wp_step
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    intro hF1 hsym1
    obtain ⟨hread14, hcan14⟩ := rodata_jump_tag14_mf14 hF1
    apply of_sepWP_frozen_mf14 hF1 hsym1 (mid := entry + 118436#64)
    refine step_ldr8_ro_mf14 (pc := entry + 52#64) (pc' := entry + 56#64)
      (r := Reg.gpr 11#5) (v64 := 76#64)
      rfl (by simp only [wp_norm, arm64_norm, hrun]) hfetch_0x34 rfl
      (ea := sessionImg0.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 13)) (wb := none)
      (by simp only [evalAddrMode, wp_norm, arm64_norm])
      hread14 hcan14 (by simp only [applyWriteback, wp_norm, arm64_norm]) ?_
    iterate 25 wp_step
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    intro hF2 hsym2
    refine call_alloc_mf14 (s0 := s0) (R := R)
      (x := (⟨s0.sp - 232#64, ptr, kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail⟩ :
        Prost.DecodeVarintSliceGhost))
      (T := memRegion (s0.sp - 232#64) 24 ∗
        (ptr ↦ₛ (kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail)) ∗ A0.pool ∗
        stackAt (s0.sp - 240#64) Prost.decodeVarintSliceStack)
      (F := memRegion (s0.sp - 240#64 - 16144#64) 7872 ∗
        ((ss + 296#64) ↦₆₄ 0#64) ∗ ((ss + 304#64) ↦₆₄ 1#64) ∗ ((ss + 312#64) ↦₆₄ 0#64) ∗
        ((ss + 320#64) ↦₃₂ 0#32) ∗ memRegion (ss + 324#64) 4 ∗ restX14 A0 ss v ∗
        (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1575 + (encodeVarint (i.setWidth 64)).length +
          tail.length)) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ v80) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        memRegion (s0.sp - 240#64) 8 ∗ memRegion (s0.sp - 208#64) 128)
      hcallD hF2 hsym2
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned]; simpa only [wp_norm, arm64_norm] using hsp_align)
      rfl
      (by simp only [Prost.decodeVarintSliceSpec, wp_norm, arm64_norm]; rfl)
      ?_
      (by rw [bytes_kyber_ne_split_mf14, show A0.pool = emp from rfl, emp_sepConj]; ac_rfl)
      (fun _ _ => rfl) (fun _ => rfl)
      (by simp only [wp_norm, arm64_norm])
      ?_
    · refine ⟨?_, ?_, Or.inl ?_⟩ <;>
        simp only [List.length_cons, kyberIdBytes_length i hct, BitVec.toNat_ofNat] <;> omega
    intro sf hpcf hrunf hspf hcsf hF3 hsym3
    simp only [wp_norm, arm64_norm] at hpcf
    have hsp_sf : sf.sp = s0.sp - 240#64 := by
      simpa only [wp_norm, arm64_norm] using hspf
    have hx19_sf : sf.readReg64 (Reg.gpr 19#5) = slot := by
      simpa only [wp_norm, arm64_norm] using hcsf.1
    have hx20_sf : sf.readReg64 (Reg.gpr 20#5) = 99#64 := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.1
    have hx21_sf : sf.readReg64 (Reg.gpr 21#5) = ss := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.1
    have hx22_sf : sf.readReg64 (Reg.gpr 22#5) = bufRef := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.1
    rw [post_of_decode_ne_mf14 i hct tail ptr s0.sp _ sf (by simp only [wp_norm, arm64_norm])]
    refine SepWPp.pure_elim fun htr_sf => ?_
    have hc_ult2' : BitVec.ult (BitVec.ofNat 64 (1575 + (encodeVarint (i.setWidth 64)).length +
      tail.length)) 2#64 = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_sub2' : BitVec.ofNat 64 (1575 + (encodeVarint (i.setWidth 64)).length +
      tail.length) - 2#64 =
        BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length + tail.length) := by
      have hsub := len_sub_mf14 (a := 1575 + (encodeVarint (i.setWidth 64)).length) (b :=
        2) (n := tail.length) (by omega) (by omega)
      have heq : 1575 + (encodeVarint (i.setWidth 64)).length - 2 + tail.length =
          1573 + (encodeVarint (i.setWidth 64)).length + tail.length := by omega
      rwa [heq] at hsub
    have hc_ult_body : BitVec.ult (BitVec.ofNat 64 (1573 +
      (encodeVarint (i.setWidth 64)).length + tail.length))
        (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_sub_body : BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length +
      tail.length) -
        BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length) =
        BitVec.ofNat 64 tail.length := by
      have := len_sub_mf14 (a := 1573 + (encodeVarint (i.setWidth 64)).length)
        (b := 1573 + (encodeVarint (i.setWidth 64)).length) (n := tail.length) (by omega) (by omega)
      simpa using this
    have hc_ule_body : BitVec.ule (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length))
        (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length + tail.length)) = true := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hc_ule_n2' : BitVec.ule (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length + tail.length)) = true := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hc_ult_n' : BitVec.ult (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length + tail.length)) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hc_ult_n2' : BitVec.ult (BitVec.ofNat 64 (1573 +
      (encodeVarint (i.setWidth 64)).length + tail.length))
        (BitVec.ofNat 64 tail.length) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_ule_n' : BitVec.ule (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length +
      tail.length))
        (BitVec.ofNat 64 tail.length) = false := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_eq_n' : (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length + tail.length) ==
        BitVec.ofNat 64 tail.length) = false := by
      rw [beq_eq_false_iff_ne]; intro heq
      have h1 := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at h1; omega
    have hc_sub1' : BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length +
      tail.length) - 1#64 =
        BitVec.ofNat 64 (1572 + (encodeVarint (i.setWidth 64)).length + tail.length) := by
      have hsub := len_sub_mf14 (a := 1573 + (encodeVarint (i.setWidth 64)).length) (b :=
        1) (n := tail.length) (by omega) (by omega)
      have heq : 1573 + (encodeVarint (i.setWidth 64)).length - 1 + tail.length =
          1572 + (encodeVarint (i.setWidth 64)).length + tail.length := by omega
      rwa [heq] at hsub
    apply of_sepWP_frozen_mf14 hF3 hsym3 (mid := entry + 18446744073709540264#64)
    have htr_sf' : sf.trace = s0.trace := by
      simpa only [wp_norm, arm64_norm] using htr_sf
    have hx26_sf : sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.1
    have hx27_sf : sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.1
    have hx28_sf : sf.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.1
    have hcsv_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.2.2
    iterate 45 wp_step
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm,
      hrunf])
    intro hF4 hsym4
    refine call_alloc_entails_mf14 (s0 := s0) (R := R)
      (x := (⟨.varint, ss + 320#64, bufRef, slot, ptr + 3#64, kyberIdBytes i ct tail⟩ :
        Prost.Int32MergeGhost))
      (T := memRegion (ss + 320#64) 4 ∗ (bufRef ↦₆₄ slot) ∗
        Prost.sliceCursorAt slot (ptr + 3#64) (kyberIdBytes i ct tail) ∗ A0.pool ∗
        stackAt (s0.sp - 240#64) Prost.int32MergeStack)
      (F := memRegion (s0.sp - 240#64 - 16144#64) 7792 ∗
        ((s0.sp - 232#64) ↦₃₂ 0#32) ∗ ((s0.sp - 228#64) ↦₃₂ 0#32) ∗
        ((s0.sp - 224#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
        ((s0.sp - 216#64) ↦₆₄ 2#64) ∗
        (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
        ((ss + 296#64) ↦₆₄ 0#64) ∗ ((ss + 304#64) ↦₆₄ 1#64) ∗ ((ss + 312#64) ↦₆₄ 0#64) ∗
        memRegion (ss + 324#64) 4 ∗ restX14 A0 ss v ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ v80) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        memRegion (s0.sp - 240#64) 8 ∗ memRegion (s0.sp - 208#64) 128)
      hcallI hF4 hsym4
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrunf])
      (by rw [State.spAligned]; simpa only [wp_norm, arm64_norm, hsp_sf] using hsp_align)
      rfl
      (by simp only [Prost.int32MergeSpec, wp_norm, arm64_norm, hsp_sf]; rfl)
      (by rw [kyberIdBytes_length i hct]; omega)
      (by
        refine Entails.trans ?_ (pre_to_int32Merge_ne_mf14 ss bufRef slot ptr s0.sp i hct tail _)
        exact Entails.of_eq (by ac_rfl))
      (fun _ _ => rfl) (fun _ => rfl)
      (by simp only [wp_norm, arm64_norm, htr_sf'])
      ?_
    intro sfI hpcfI hrunfI hspfI hcsfI hF5 hsym5
    simp only [wp_norm, arm64_norm] at hpcfI
    have hsp_sfI : sfI.sp = s0.sp - 240#64 := by
      simpa only [wp_norm, arm64_norm, hsp_sf] using hspfI
    rw [post_of_int32Merge_ne_mf14 ss bufRef slot ptr s0.sp i hct tail _ sfI
      (by simp only [wp_norm, arm64_norm, hsp_sf])]
    refine SepWPp.pure_elim fun htr_sfI => SepWPp.pure_elim fun hx0_sfI => ?_
    have htr_sfI' : sfI.trace = s0.trace := by
      simpa only [wp_norm, arm64_norm, htr_sf'] using htr_sfI
    have hx0_sfI' : sfI.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_sfI
    have hx19_sfI : sfI.readReg64 (Reg.gpr 19#5) = 98#64 := by
      simpa only [wp_norm, arm64_norm] using hcsfI.1
    have hx20_sfI : sfI.readReg64 (Reg.gpr 20#5) = ss := by
      simpa only [wp_norm, arm64_norm] using hcsfI.2.1
    have hx21_sfI : sfI.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
      simpa only [wp_norm, arm64_norm] using hcsfI.2.2.1
    have hx22_sfI : sfI.readReg64 (Reg.gpr 22#5) = bufRef := by
      simpa only [wp_norm, arm64_norm] using hcsfI.2.2.2.1
    have hx26_sfI : sfI.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
      simpa only [wp_norm, arm64_norm, hx26_sf] using hcsfI.2.2.2.2.2.2.2.1
    have hx27_sfI : sfI.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
      simpa only [wp_norm, arm64_norm, hx27_sf] using hcsfI.2.2.2.2.2.2.2.2.1
    have hx28_sfI : sfI.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
      simpa only [wp_norm, arm64_norm, hx28_sf] using hcsfI.2.2.2.2.2.2.2.2.2.1
    have hcsv_sfI : calleeSavedVRegs sfI = calleeSavedVRegs s0 := by
      simpa only [wp_norm, arm64_norm, hcsv_sf] using hcsfI.2.2.2.2.2.2.2.2.2.2.2
    have hc_ule_n2 : BitVec.ule (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 (1572 + tail.length)) = true := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hc_ult_n : BitVec.ult (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 (1572 + tail.length)) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hc_ult_n2 : BitVec.ult (BitVec.ofNat 64 (1572 + tail.length))
        (BitVec.ofNat 64 tail.length) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_ule_n : BitVec.ule (BitVec.ofNat 64 (1572 + tail.length))
        (BitVec.ofNat 64 tail.length) = false := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_eq_n : (BitVec.ofNat 64 (1572 + tail.length) == BitVec.ofNat 64 tail.length) =
      false := by
      rw [beq_eq_false_iff_ne]; intro heq
      have h1 := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at h1; omega
    have hc_sub1 : BitVec.ofNat 64 (1572 + tail.length) - 1#64 =
        BitVec.ofNat 64 (1571 + tail.length) := len_sub_mf14 (by omega) (by omega)
    apply of_sepWP_frozen_mf14 hF5 hsym5 (mid := entry + 18446744073709539180#64)
    iterate 33 wp_step
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm,
      hrunfI])
    intro hF6 hsym6
    refine call_alloc_mf14 (s0 := s0) (R := R)
      (x := (⟨.lengthDelimited, ss + 296#64, 0#64, 1#64, [], bufRef, slot, kyberPtr2 ptr i + 1#64,
        innerBytes ct tail⟩ : Prost.BytesMergeGhost))
      (T := vecU8At A0 (ss + 296#64) 0#64 1#64 [] ∗ (bufRef ↦₆₄ slot) ∗
        Prost.sliceCursorAt slot (kyberPtr2 ptr i + 1#64) (innerBytes ct tail) ∗ A0.pool ∗
        stackAt (s0.sp - 240#64) Prost.bytesMergeStack)
      (F := memRegion (s0.sp - 240#64 - 16144#64) 7648 ∗
        ((s0.sp - 232#64) ↦₃₂ 0#32) ∗ ((s0.sp - 228#64) ↦₃₂ 0#32) ∗
        ((s0.sp - 224#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
        ((s0.sp - 216#64) ↦₆₄ 2#64) ∗
        (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
        ((ptr + 3#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
        (kyberPtr2 ptr i ↦₈ 18#8) ∗
        ((ss + 320#64) ↦₃₂ i) ∗ memRegion (ss + 324#64) 4 ∗ restX14 A0 ss v ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ v80) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        memRegion (s0.sp - 240#64) 8 ∗ memRegion (s0.sp - 208#64) 128)
      hcallB hF6 hsym6
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrunfI])
      (by rw [State.spAligned]; simpa only [wp_norm, arm64_norm, hsp_sfI] using hsp_align)
      rfl
      (by
        dsimp only [Prost.bytesMergeSpec, Spec.inImage, Prost.bytesMergeRawSpec]
        rw [pure_sepConj_pure_assoc]
        congr 1
        simp only [wp_norm, arm64_norm, hsp_sfI])
      (by exact ⟨⟨hF6, hsym6⟩, by simp only [wp_norm, arm64_norm, WireType.toNat],
        by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
        by simp only [innerBytes_length hct]; omega, Prost.bytesMergeCapOk_zero⟩)
      (by
        rw [← emptyVec_kyber_eq_vecU8At, ← sliceCursorAt_inner_ne_fold_mf14 slot ptr i hct tail,
          show A0.pool = emp from rfl, emp_sepConj,
          ← sepConj_assoc (stackAt _ _), sepConj_comm (stackAt _ _),
          int32Merge_to_bytesMerge_stack_mf14]
        ac_rfl)
      (fun _ _ => rfl) (fun _ => rfl)
      (by simp only [wp_norm, arm64_norm, htr_sfI'])
      ?_
    intro sf2 hpcf2 hrunf2 hspf2 hcsf2 _ _
    simp only [wp_norm, arm64_norm] at hpcf2
    have hsp_sf2 : sf2.sp = s0.sp - 240#64 := by
      simpa only [wp_norm, arm64_norm, hsp_sfI] using hspf2
    dsimp only [Prost.bytesMergeSpec, Spec.inImage]
    rw [post_of_bytesMerge_ne_mf14 ss bufRef slot ptr s0.sp i hct tail _ sf2
      (by simp only [wp_norm, arm64_norm, hsp_sfI])]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' =>
      SepWPp.pure_elim fun htr_sf2 => SepWPp.pure_elim fun hx0_sf2 =>
      SepWPp.pure_elim fun _hcapOk => ?_
    have htr_sf2' : sf2.trace = s0.trace := by
      simpa only [wp_norm, arm64_norm, htr_sfI'] using htr_sf2
    have hx0_sf2' : sf2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_sf2
    have hx26_sf2 : sf2.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
      simpa only [wp_norm, arm64_norm, hx26_sfI] using hcsf2.2.2.2.2.2.2.2.1
    have hx27_sf2 : sf2.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
      simpa only [wp_norm, arm64_norm, hx27_sfI] using hcsf2.2.2.2.2.2.2.2.2.1
    have hx28_sf2 : sf2.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
      simpa only [wp_norm, arm64_norm, hx28_sfI] using hcsf2.2.2.2.2.2.2.2.2.2.1
    have hcsv_sf2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0 := by
      simpa only [wp_norm, arm64_norm, hcsv_sfI] using hcsf2.2.2.2.2.2.2.2.2.2.2.2
    have hx21_sf2 : sf2.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
      simpa only [wp_norm, arm64_norm, hx21_sfI] using hcsf2.2.2.1
    have hx22_sf2 : sf2.readReg64 (Reg.gpr 22#5) = bufRef := by
      simpa only [wp_norm, arm64_norm, hx22_sfI] using hcsf2.2.2.2.1
    have htail_ult_self : BitVec.ult (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 tail.length) = false := by
      simp [BitVec.ult]
    have htail_ule_self : BitVec.ule (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 tail.length) = true := by
      simp [BitVec.ule]
    apply SepWPp.of_sepWP_ret
    iterate 19 wp_step
    apply SepWP.fold (final_post_entails_ne_mf14 ss cap' ptr' v bufRef slot ptr hi hct tail s0.sp
      (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 25#5)) v80
      (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
      (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
      (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
      (sepConj_emp _).symm
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm,
      hrunf2])
    refine ⟨fun hmf => sat_pure_true_mf14 ⟨?_, ?_⟩ hmf,
      by simp only [wp_norm, arm64_norm],
      by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, hx26_sf2, hx27_sf2, hx28_sf2,
        hcsv_sf2, and_self]⟩
    · simp only [wp_norm, arm64_norm, htr_sf2']
    · simp only [wp_norm, arm64_norm]

end CryptoVerification.E2E.Record.L1GX.Leaf.MergeFieldX14
