/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.Specs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.VarintBridge -- shake: keep

/-!
# Binary Verification of `spqr::decode_state` (`0x5349c`) — Stack Frame & Error Exits

**Checked by Lean.**

Defines callee-saved register save-slot layouts and stack-frame splits, proves the shared
epilogue (`0x53e60..0x53e7c`) and `DecodeError` drop/unwind tail (`0x53df4..0x53e5c`), and
establishes panic-aware `DecodeError::push` and `DecodeError::from` error-exit paths.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost CryptoVerification.LibsignalTripleRatchet.VarintBridge
open CryptoVerification.SpqrV1.Varint CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.BytesMerge CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Drop CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Callee-Saved Register Slots & Stack Frame Splits -/

/-- Callee-saved register save slots `[sp0 - 96, sp0)` (`0x60` bytes) for `spqr::decode_state`. -/
def decodeStateSavedAt (sp0 s29 s30 s28 s27 s26 s25 s24 s23 s22 s21 s20 s19 : BitVec 64) : SepProp :=
  ((sp0 - 96#64) ↦₆₄ s29) ∗ ((sp0 - 88#64) ↦₆₄ s30) ∗
    ((sp0 - 80#64) ↦₆₄ s28) ∗ ((sp0 - 72#64) ↦₆₄ s27) ∗
    ((sp0 - 64#64) ↦₆₄ s26) ∗ ((sp0 - 56#64) ↦₆₄ s25) ∗
    ((sp0 - 48#64) ↦₆₄ s24) ∗ ((sp0 - 40#64) ↦₆₄ s23) ∗
    ((sp0 - 32#64) ↦₆₄ s22) ∗ ((sp0 - 24#64) ↦₆₄ s21) ∗
    ((sp0 - 16#64) ↦₆₄ s20) ∗ ((sp0 - 8#64) ↦₆₄ s19)

theorem stackAt_decodeState_entry_split (sp0 : BitVec 64) :
    stackAt sp0 decodeStateStackX =
      stackAt (sp0 - 1392#64) v1StateMergeStack ∗
      memRegion (sp0 - 1384#64) 1288 ∗
      (∃∗ s19 : BitVec 64, ∃∗ s20 : BitVec 64, ∃∗ s21 : BitVec 64, ∃∗ s22 : BitVec 64,
       ∃∗ s23 : BitVec 64, ∃∗ s24 : BitVec 64, ∃∗ s25 : BitVec 64, ∃∗ s26 : BitVec 64,
       ∃∗ s27 : BitVec 64, ∃∗ s28 : BitVec 64, ∃∗ s30 : BitVec 64, ∃∗ s29 : BitVec 64,
       ∃∗ w0 : BitVec 64,
        ((sp0 - 1392#64) ↦₆₄ w0) ∗
        decodeStateSavedAt sp0 s29 s30 s28 s27 s26 s25 s24 s23 s22 s21 s20 s19) := by
  have h1 : stackAt sp0 decodeStateStackX =
      stackAt (sp0 - 1392#64) v1StateMergeStack ∗ memRegion (sp0 - 1392#64) 1392 := by
    unfold stackAt decodeStateStackX
    have h100 : BitVec.ofNat 64 (0x570 + v1StateMergeStack) =
        1392#64 + BitVec.ofNat 64 v1StateMergeStack := by decide
    have hbase : sp0 - 1392#64 =
        sp0 - BitVec.ofNat 64 (0x570 + v1StateMergeStack) + BitVec.ofNat 64 v1StateMergeStack := by
      rw [h100]; bv_omega
    have hsub : sp0 - 1392#64 - BitVec.ofNat 64 v1StateMergeStack =
        sp0 - BitVec.ofNat 64 (0x570 + v1StateMergeStack) := by
      rw [h100]; bv_omega
    rw [hsub]
    exact ProofLib.memRegion_split' (b := sp0 - BitVec.ofNat 64 (0x570 + v1StateMergeStack))
      (n := v1StateMergeStack) (k := 1392) (b' := sp0 - 1392#64) (by decide) hbase (by decide)
  rw [h1]
  rw [ProofLib.memRegion_split' (b := sp0 - 1392#64) (n := 8) (k := 1384)
      (b' := sp0 - 1384#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 1384#64) (n := 1288) (k := 96)
      (b' := sp0 - 96#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 96#64) (n := 8) (k := 88)
      (b' := sp0 - 88#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 88#64) (n := 8) (k := 80)
      (b' := sp0 - 80#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 80#64) (n := 8) (k := 72)
      (b' := sp0 - 72#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 72#64) (n := 8) (k := 64)
      (b' := sp0 - 64#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 64#64) (n := 8) (k := 56)
      (b' := sp0 - 56#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 56#64) (n := 8) (k := 48)
      (b' := sp0 - 48#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 48#64) (n := 8) (k := 40)
      (b' := sp0 - 40#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 40#64) (n := 8) (k := 32)
      (b' := sp0 - 32#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 32#64) (n := 8) (k := 24)
      (b' := sp0 - 24#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 24#64) (n := 8) (k := 16)
      (b' := sp0 - 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 16#64) (n := 8) (k := 8)
      (b' := sp0 - 8#64) rfl (by bv_omega) (by decide)]
  rw [ProofLib.memRegion_eight (sp0 - 1392#64), ProofLib.memRegion_eight (sp0 - 96#64),
    ProofLib.memRegion_eight (sp0 - 88#64), ProofLib.memRegion_eight (sp0 - 80#64),
    ProofLib.memRegion_eight (sp0 - 72#64), ProofLib.memRegion_eight (sp0 - 64#64),
    ProofLib.memRegion_eight (sp0 - 56#64), ProofLib.memRegion_eight (sp0 - 48#64),
    ProofLib.memRegion_eight (sp0 - 40#64), ProofLib.memRegion_eight (sp0 - 32#64),
    ProofLib.memRegion_eight (sp0 - 24#64), ProofLib.memRegion_eight (sp0 - 16#64),
    ProofLib.memRegion_eight (sp0 - 8#64)]
  unfold decodeStateSavedAt
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; ac_rfl

theorem decodeState_stack_restore_1296 (sp0 s29 s30 s28 s27 s26 s25 s24 s23 s22 s21 s20 s19 : BitVec 64) :
    stackAt (sp0 - 1392#64) v1StateMergeStack ∗
      memRegion (sp0 - 1392#64) 1296 ∗
      decodeStateSavedAt sp0 s29 s30 s28 s27 s26 s25 s24 s23 s22 s21 s20 s19 ⊢
      stackAt sp0 decodeStateStackX := by
  rw [ProofLib.memRegion_split' (b := sp0 - 1392#64) (n := 8) (k := 1288)
      (b' := sp0 - 1384#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight (sp0 - 1392#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w0
  rw [stackAt_decodeState_entry_split sp0]
  refine sepConj_mono_right ?_
  have hassoc :
      (sp0 - 1392#64) ↦₆₄ w0 ∗ memRegion (sp0 - 1384#64) 1288 ∗
        decodeStateSavedAt sp0 s29 s30 s28 s27 s26 s25 s24 s23 s22 s21 s20 s19 =
      memRegion (sp0 - 1384#64) 1288 ∗
        ((sp0 - 1392#64) ↦₆₄ w0 ∗
          decodeStateSavedAt sp0 s29 s30 s28 s27 s26 s25 s24 s23 s22 s21 s20 s19) := by ac_rfl
  rw [hassoc]
  refine sepConj_mono_right ?_
  exact Entails.sepExists_right s19 (Entails.sepExists_right s20 (Entails.sepExists_right s21
    (Entails.sepExists_right s22 (Entails.sepExists_right s23 (Entails.sepExists_right s24
    (Entails.sepExists_right s25 (Entails.sepExists_right s26 (Entails.sepExists_right s27
    (Entails.sepExists_right s28 (Entails.sepExists_right s30 (Entails.sepExists_right s29
    (Entails.sepExists_right w0 (Entails.refl _)))))))))))))

/-- Split `stackAt sp v1StateMergeStack` for a callee requiring stack budget `M ≤ v1StateMergeStack`. -/
theorem stackAt_to_callee (sp : BitVec 64) (M : Nat) (hM : M ≤ v1StateMergeStack) :
    stackAt sp v1StateMergeStack ⊢
      memRegion (sp - BitVec.ofNat 64 v1StateMergeStack) (v1StateMergeStack - M) ∗ stackAt sp M := by
  have h100 : v1StateMergeStack < 2 ^ 64 := by decide
  have heq := ProofLib.stackAt_split_bottom sp M (v1StateMergeStack - M) (by omega)
  have hadd : M + (v1StateMergeStack - M) = v1StateMergeStack := by omega
  rw [hadd] at heq; exact Entails.of_eq heq

/-- Restore `stackAt sp v1StateMergeStack` after a callee requiring stack budget `M ≤ v1StateMergeStack`. -/
theorem stackAt_of_callee (sp : BitVec 64) (M : Nat) (hM : M ≤ v1StateMergeStack) :
    memRegion (sp - BitVec.ofNat 64 v1StateMergeStack) (v1StateMergeStack - M) ∗ stackAt sp M ⊢
      stackAt sp v1StateMergeStack := by
  have h100 : v1StateMergeStack < 2 ^ 64 := by decide
  have heq := ProofLib.stackAt_split_bottom sp M (v1StateMergeStack - M) (by omega)
  have hadd : M + (v1StateMergeStack - M) = v1StateMergeStack := by omega
  rw [hadd] at heq; exact Entails.of_eq heq.symm

/-- On the non-empty input path, fold `(sp ↦₆₄ w0)` with `memRegion (sp + 8#64) 1288` and split
    into the disjoint stack frame regions of `spqr::decode_state`:
    - `memRegion sp 336` (`[sp, sp + 0x150)`)
    - `(sp + 0x150#64) ↦₆₄ cPtr ∗ (sp + 0x158#64) ↦₆₄ cLen` (`16`B cursor)
    - `(sp + 0x160#64) ↦₆₄ vn0 ∗ memRegion (sp + 0x168#64) 40` (`48`B `VersionNegotiationPB`)
    - `(sp + 0x190#64) ↦₆₄ ch0 ∗ memRegion (sp + 0x198#64) 72` (`80`B `ChainPB`)
    - `(sp + 0x1e0#64) ↦₆₄ in0 ∗ memRegion (sp + 0x1e8#64) 216` (`224`B `Inner`)
    - `memRegion (sp + 0x2c0#64) 352` (`352`B scratch)
    - `(sp + 0x420#64) ↦₆₄ bRef` (`8`B `bufRef` at `x29 - 0xf0`)
    - `memRegion (sp + 0x428#64) 224` (`224`B scratch at `x29 - 0xe8`)
    - `memRegion (sp + 0x508#64) 8` (`8`B padding before `x29`). -/
theorem decodeState_nonempty_frame_split (sp w0 : BitVec 64) :
    (sp ↦₆₄ w0) ∗ memRegion (sp + 8#64) 1288 ⊢
      memRegion sp 336 ∗
      memRegion (sp + 0x168#64) 40 ∗
      memRegion (sp + 0x198#64) 72 ∗
      memRegion (sp + 0x1e8#64) 216 ∗
      memRegion (sp + 0x2c0#64) 352 ∗
      memRegion (sp + 0x428#64) 224 ∗
      memRegion (sp + 0x508#64) 8 ∗
      (∃∗ bRef : BitVec 64, ∃∗ in0 : BitVec 64, ∃∗ ch0 : BitVec 64,
       ∃∗ vn0 : BitVec 64, ∃∗ cLen : BitVec 64, ∃∗ cPtr : BitVec 64,
        ((sp + 0x150#64) ↦₆₄ cPtr) ∗ ((sp + 0x158#64) ↦₆₄ cLen) ∗
        ((sp + 0x160#64) ↦₆₄ vn0) ∗ ((sp + 0x190#64) ↦₆₄ ch0) ∗
        ((sp + 0x1e0#64) ↦₆₄ in0) ∗ ((sp + 0x420#64) ↦₆₄ bRef)) := by
  have h1296 : (sp ↦₆₄ w0) ∗ memRegion (sp + 8#64) 1288 ⊢ memRegion sp 1296 := by
    rw [ProofLib.memRegion_split' (b := sp) (n := 8) (k := 1288)
        (b' := sp + 8#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion sp w0)
  refine Entails.trans h1296 ?_
  rw [ProofLib.memRegion_split' (b := sp) (n := 336) (k := 960)
      (b' := sp + 0x150#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x150#64) (n := 8) (k := 952)
      (b' := sp + 0x158#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x158#64) (n := 8) (k := 944)
      (b' := sp + 0x160#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x160#64) (n := 8) (k := 936)
      (b' := sp + 0x168#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x168#64) (n := 40) (k := 896)
      (b' := sp + 0x190#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x190#64) (n := 8) (k := 888)
      (b' := sp + 0x198#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x198#64) (n := 72) (k := 816)
      (b' := sp + 0x1e0#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x1e0#64) (n := 8) (k := 808)
      (b' := sp + 0x1e8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x1e8#64) (n := 216) (k := 592)
      (b' := sp + 0x2c0#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x2c0#64) (n := 352) (k := 240)
      (b' := sp + 0x420#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x420#64) (n := 8) (k := 232)
      (b' := sp + 0x428#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x428#64) (n := 224) (k := 8)
      (b' := sp + 0x508#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight (sp + 0x150#64),
    ProofLib.memRegion_eight (sp + 0x158#64),
    ProofLib.memRegion_eight (sp + 0x160#64),
    ProofLib.memRegion_eight (sp + 0x190#64),
    ProofLib.memRegion_eight (sp + 0x1e0#64),
    ProofLib.memRegion_eight (sp + 0x420#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

/-- Fold the 7 stack frame regions (`336 + 16 + 352 + 352 + 8 + 224 + 8 = 1296` bytes)
    back into `memRegion sp 1296` before the epilogue `0x53e60`. -/
theorem decodeState_frame_fold (sp bRef : BitVec 64) :
    memRegion sp 336 ∗
      memRegion (sp + 0x150#64) 16 ∗
      memRegion (sp + 0x160#64) 352 ∗
      memRegion (sp + 0x2c0#64) 352 ∗
      ((sp + 0x420#64) ↦₆₄ bRef) ∗
      memRegion (sp + 0x428#64) 224 ∗
      memRegion (sp + 0x508#64) 8 ⊢
      memRegion sp 1296 := by
  have hb : ((sp + 0x420#64) ↦₆₄ bRef) ⊢ memRegion (sp + 0x420#64) 8 :=
    ProofLib.pointsTo64_entails_memRegion (sp + 0x420#64) bRef
  rw [ProofLib.memRegion_split' (b := sp) (n := 336) (k := 960)
      (b' := sp + 0x150#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x150#64) (n := 16) (k := 944)
      (b' := sp + 0x160#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x160#64) (n := 352) (k := 592)
      (b' := sp + 0x2c0#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x2c0#64) (n := 352) (k := 240)
      (b' := sp + 0x420#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x420#64) (n := 8) (k := 232)
      (b' := sp + 0x428#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x428#64) (n := 224) (k := 8)
      (b' := sp + 0x508#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left hb))))

/-! ## 2. Output Buffer Error Split & Callee Address Helpers -/

theorem memRegion_352_err_split (outPtr : BitVec 64) :
    memRegion outPtr 352 ⊢
      memRegion (outPtr + 9#64) 343 ∗
      (∃∗ b8 : BitVec 8, ∃∗ w0 : BitVec 64,
        (outPtr ↦₆₄ w0) ∗ ((outPtr + 8#64) ↦₈ b8)) := by
  rw [ProofLib.memRegion_split' (b := outPtr) (n := 8) (k := 344)
      (b' := outPtr + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := outPtr + 8#64) (n := 1) (k := 343)
      (b' := outPtr + 9#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight outPtr,
    ProofLib.memRegion_one (outPtr + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

theorem fold_decodeStateResultAt_err (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (outPtr : BitVec 64) {res : Except Error PqRatchetState}
    (hres : res = .error .stateDecode) :
    (outPtr ↦₆₄ 18446744073709551614#64) ∗ ((outPtr + 8#64) ↦₈ 0#8) ∗ memRegion (outPtr + 9#64) 343 ⊢
      decodeStateResultAt H_inner A outPtr res := by
  subst hres
  exact Entails.refl _

theorem DecodeStateCalleeContracts4K.dealloc_at {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decodeStateName +
        (bv% (ls_off% "__rustc::__rust_dealloc") - bv% (ls_off% "spqr::decode_state")))
      (rustDeallocSpec A) := by
  refine sub_ok_of_addr_eq ?_ hc.alloc.dealloc
  have hfn : libsignalSessionCode.fnOff "__rustc::__rust_dealloc" =
      num% (ls_off% "__rustc::__rust_dealloc") :=
    ls_stub% "__rustc::__rust_dealloc"
  change libsignalSessionCode.fnOff LibsignalTripleRatchet.deallocName =
    num% (ls_off% "__rustc::__rust_dealloc") at hfn
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, decodeState_fnOff, hfn]
  bv_omega

theorem DecodeStateCalleeContracts4K.memcpy_at {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext) (hookStack : Nat)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decodeStateName +
        (bv% (ls_off% "memcpy") - bv% (ls_off% "spqr::decode_state")))
      (libcMemcpySpec hookStack) := by
  refine sub_ok_of_addr_eq ?_ (hc.alloc.memcpy hookStack hstack hmax)
  have hfn : libsignalSessionCode.fnOff "memcpy" = num% (ls_off% "memcpy") :=
    ls_stub% "memcpy"
  change libsignalSessionCode.fnOff LibsignalTripleRatchet.memcpyName =
    num% (ls_off% "memcpy") at hfn
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, decodeState_fnOff, hfn]
  bv_omega

theorem DecodeStateCalleeContracts4K.decodeErrorFrom_at {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decodeStateName +
        (bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") -
          bv% (ls_off% "spqr::decode_state")))
      (decodeErrorFromSpec A) := by
  refine sub_ok_of_addr_eq ?_ hc.decodeErrorFrom
  have hfn : libsignalSessionCode.fnOff decodeErrorFromName =
      num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") :=
    ls_lemma% fnOff "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from"
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, decodeState_fnOff, hfn]
  bv_omega

theorem DecodeStateCalleeContracts4K.decodeErrorPush_at {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decodeStateName +
        (bv% (ls_off% "<prost::error::DecodeError>::push") - bv% (ls_off% "spqr::decode_state")))
      (decodeErrorPushSpec A) := by
  refine sub_ok_of_addr_eq ?_ hc.decodeErrorPush
  have hfn : libsignalSessionCode.fnOff decodeErrorPushName =
      num% (ls_off% "<prost::error::DecodeError>::push") :=
    ls_lemma% fnOff "<prost::error::DecodeError>::push"
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, decodeState_fnOff, hfn]
  bv_omega

theorem DecodeStateCalleeContracts4K.dropProtoPqRatchetState_at {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decodeStateName +
        (bv% (ls_off% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>") -
          bv% (ls_off% "spqr::decode_state")))
      (dropProtoPqRatchetStateSpec H_inner A b) := by
  refine sub_ok_of_addr_eq ?_ hc.dropProtoPqRatchetState
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, decodeState_fnOff, dropProtoPqRatchetState_fnOff]
  bv_omega

theorem DecodeStateCalleeContracts4K.dropOptProtoInnerState_at {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decodeStateName +
        (bv% (ls_off% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>") -
          bv% (ls_off% "spqr::decode_state")))
      (dropOptProtoInnerStateSpec H_inner A b) := by
  refine sub_ok_of_addr_eq ?_ hc.dropOptProtoInnerState
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, decodeState_fnOff, dropOptProtoInnerState_fnOff]
  bv_omega

theorem DecodeStateCalleeContracts4K.decodeVarint2_at {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decodeStateName +
        (bv% (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#2]") -
          bv% (ls_off% "spqr::decode_state")))
      (Varint.decodeVarint2Spec A) := by
  refine sub_ok_of_addr_eq ?_ hc.decodeVarint2
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, decodeState_fnOff, Varint.decodeVarint2_fnOff]
  bv_omega

theorem DecodeStateCalleeContracts4K.skipField3_at {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decodeStateName +
        (bv% (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#3]") -
          bv% (ls_off% "spqr::decode_state")))
      (skipField3Spec A) := by
  refine sub_ok_of_addr_eq ?_ hc.skipField3
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, decodeState_fnOff, skipField3_fnOff]
  bv_omega

theorem DecodeStateCalleeContractsX4K.bytesMerge3_at {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsX4K H_inner img b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decodeStateName +
        (bv% (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]") -
          bv% (ls_off% "spqr::decode_state")))
      ((bytesMerge3RawSpec A).inImage img) := by
  refine sub_ok_of_addr_eq ?_ hc.bytesMerge3
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, decodeState_fnOff, bytesMerge3_fnOff]
  bv_omega

theorem DecodeStateCalleeContracts4K.chainParamsMerge_at {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decodeStateName +
        (bv% (ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::ChainParams, &mut &[u8]>") -
          bv% (ls_off% "spqr::decode_state")))
      (chainParamsMergeSpec A) := by
  refine sub_ok_of_addr_eq ?_ hc.chainParamsMerge
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, decodeState_fnOff, chainParamsMerge_fnOff]
  bv_omega

theorem DecodeStateCalleeContractsX4K.epochDirectionMerge_at {H_inner : V1InnerHeapPred}
    {img : Obj.Image} {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsX4K H_inner img b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decodeStateName +
        (bv% (ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, &mut &[u8]>") -
          bv% (ls_off% "spqr::decode_state")))
      ((epochDirectionMergeSpec A).inImage img) := by
  refine sub_ok_of_addr_eq ?_ hc.epochDirectionMerge
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, decodeState_fnOff, epochDirectionMerge_fnOff]
  bv_omega

theorem DecodeStateCalleeContractsX4K.v1StateMerge_at {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsX4K H_inner img b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decodeStateName +
        (bv% (ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::V1State, &mut &[u8]>") -
          bv% (ls_off% "spqr::decode_state")))
      ((Prost.MessageMerge.v1StateMergeSpec A b).inImage img) := by
  refine sub_ok_of_addr_eq ?_ hc.v1StateMerge
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, decodeState_fnOff, v1StateMerge_fnOff]
  bv_omega

theorem DecodeStateCalleeContracts4K.growOneChainEpoch_at {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decodeStateName +
        (bv% (ls_off% "<alloc::raw_vec::RawVec<spqr::chain::ChainEpoch>>::grow_one") -
          bv% (ls_off% "spqr::decode_state")))
      (growOneStrideFullSpec A 112 8) := by
  refine sub_ok_of_addr_eq ?_ hc.growOneChainEpoch
  have hfn : libsignalSessionCode.fnOff growOneChainEpochName =
      num% (ls_off% "<alloc::raw_vec::RawVec<spqr::chain::ChainEpoch>>::grow_one") :=
    ls_lemma% fnOff "<alloc::raw_vec::RawVec<spqr::chain::ChainEpoch>>::grow_one"
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, decodeState_fnOff, hfn]
  bv_omega

theorem DecodeStateCalleeContracts4K.session_memcpy_at {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext) (hookStack : Nat)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decodeStateName +
        (bv% (ls_off% "memcpy") - bv% (ls_off% "spqr::decode_state")))
      (sessionMemcpySpec hookStack) := by
  refine sub_ok_of_addr_eq ?_ (hc.alloc.session_memcpy hookStack hstack hmax)
  have hfn : libsignalSessionCode.fnOff "memcpy" = num% (ls_off% "memcpy") :=
    ls_stub% "memcpy"
  change libsignalSessionCode.fnOff LibsignalTripleRatchet.memcpyName =
    num% (ls_off% "memcpy") at hfn
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, decodeState_fnOff, hfn]
  bv_omega

noncomputable def decodeStateEntry (b : BitVec 64) (ext : String → Option (State → State)) : BitVec 64 :=
  (tripleRatchetProgAtExt b ext).fnAddr decodeStateName

theorem decodeStateEntry_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr decodeStateName = decodeStateEntry b ext := rfl

abbrev decodeStatePost (H_inner : V1InnerHeapPred) (b : BitVec 64) (A : RustAlloc)
    (x : DecodeStateGhost) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decodeStateSpecX H_inner b A).post x s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev decodeStatePanicPost (H_inner : V1InnerHeapPred) (b : BitVec 64) (A : RustAlloc)
    (x : DecodeStateGhost) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decodeStateSpecX H_inner b A).onPanic x s0 sf ∗ R)

@[simp, arm64_norm]
abbrev TraceVRegs (s s0 : State) : Prop :=
  s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0

theorem TraceVRegs.step {s0 s sm : State} (htr : TraceVRegs s s0)
    (htrm : sm.trace = s.trace) (hcsm : CalleeSavedPreserved s sm) :
    TraceVRegs sm s0 :=
  ⟨htrm.trans htr.1, hcsm.2.2.2.2.2.2.2.2.2.2.2.trans htr.2⟩

theorem allocFailedIn_trans {s0 sm sf : State} (htr : TraceVRegs sm s0)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  simpa only [allocFailedIn, htr.1] using h

theorem sp_sub_1392_aligned (s0 : State) (h : s0.spAligned = true) :
    ((s0.sp - 1392#64) &&& 15#64 == 0#64) = true := by

  simp only [State.spAligned, beq_iff_eq] at h ⊢
  generalize s0.sp = sp at h ⊢
  revert sp h; bv_kernel

/-! ## 3. Shared Epilogue `0x53e60..0x53e7c` and Error Tail `0x53df4..0x53e5c` -/

/-- Shared epilogue `0x53e60..0x53e7c` (`+2500..+2528`, 8 instructions):
    restores `sp := sp + 0x510`, pops `x20, x19, ..., x29, x30`, `sp := sp + 0x60`, and returns. -/
theorem decodeState_epilogue_53e60 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (x : DecodeStateGhost) (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decodeStateSpecX H_inner b A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2500#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hP : P =
      v1StateJumpTablesAt b ∗
      x.st.at A ∗
      decodeStateResultAt H_inner A x.outPtr (spqrDecodeState x.st.bytes) ∗
      A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 1296 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post := by
  rcases htr with ⟨htr, hvregs⟩
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP hpost
  dsimp only [tripleRatchetProgAtExt, decodeStateName] at hpc ⊢
  decodeState_fetches b (Rust.withPanics ext) 2500 32
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  unfold decodeStateSavedAt
  wp_steps
  dsimp only [decodeStateSpecX]
  refine SepWP.fold (decodeState_stack_restore_1296 s0.sp
    (s0.readReg64 .x29) (s0.readReg64 .x30)
    (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
    (s0.readReg64 .x20) (s0.readReg64 .x19)) (by
    unfold decodeStateSavedAt
    sep_focus) ?_
  wp_done

theorem decodeErrorWith_unfold (A : RustAlloc) (e : BitVec 64) (n : Nat) :
    decodeErrorAtStackLen A e n ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ w : BitVec 64,
        ⌜n ≤ cap.toNat ∧ cap.toNat * 32 < 2 ^ 63 ∧ ptr ≠ 0 ∧ KindNoHeap w⌝ ∗
        A.live e 72 8 ∗
        (e ↦₆₄ cap) ∗ ((e + 8#64) ↦₆₄ ptr) ∗ ((e + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
        ((e + 24#64) ↦₆₄ w) ∗ memRegion (e + 32#64) 40 ∗
        (if cap = 0 then emp else A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)) := by
  simp only [decodeErrorAtStackLen, vecOf, vecAt, vecHeader, vecBuf, List.length_replicate,
    sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.sepExists_right w ?_))
  have hreord :
      A.live e 72 8 ∗
        ((e ↦₆₄ cap ∗ (e + 8#64) ↦₆₄ ptr ∗ (e + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
          ⌜n ≤ cap.toNat ∧ cap.toNat * 32 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          if cap = 0 then emp
          else A.live ptr (cap.toNat * 32) 8 ∗
            arrayAt stackEntryAt 32 ptr (List.replicate n ()) ∗
            memRegion (ptr + BitVec.ofNat 64 (n * 32)) ((cap.toNat - n) * 32)) ∗
        (⌜KindNoHeap w⌝ ∗ (e + 24#64) ↦₆₄ w) ∗ memRegion (e + 32#64) 40 =
      ⌜n ≤ cap.toNat ∧ cap.toNat * 32 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ ⌜KindNoHeap w⌝ ∗
        A.live e 72 8 ∗ e ↦₆₄ cap ∗ (e + 8#64) ↦₆₄ ptr ∗ (e + 16#64) ↦₆₄ BitVec.ofNat 64 n ∗
        (e + 24#64) ↦₆₄ w ∗ memRegion (e + 32#64) 40 ∗
        (if cap = 0 then emp
          else A.live ptr (cap.toNat * 32) 8 ∗
            arrayAt stackEntryAt 32 ptr (List.replicate n ()) ∗
            memRegion (ptr + BitVec.ofNat 64 (n * 32)) ((cap.toNat - n) * 32)) := by ac_rfl
  refine Entails.trans (Entails.of_eq hreord) ?_
  apply Entails.pure_left; rintro ⟨hn, hcap, hptr⟩
  apply Entails.pure_left; intro hw
  apply Entails.pure_right ⟨hn, hcap, hptr, hw⟩
  by_cases hc : cap = 0
  · simp only [hc, ↓reduceIte]
    exact Entails.refl _
  · simp only [hc, ↓reduceIte, stackVec_buf_memRegion hn hcap]
    exact Entails.refl _

set_option maxHeartbeats 800000 in
/-- Inlined `drop_glue::<DecodeError>` + `Err(Error::StateDecode)` write + epilogue
    (`0x53e0c..0x53e7c`, `+2416..+2528`, 29 instructions). -/
theorem decodeState_err_drop_53e0c {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (n : Nat) (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decodeStateSpecX H_inner b A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2416#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P =
      decodeErrorAtStackLen A (s.readReg64 .x20) n ∗
      v1StateJumpTablesAt b ∗
      x.st.at A ∗
      memRegion x.outPtr 352 ∗
      A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 1296 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post := by
  rcases htr with ⟨htr, hvregs⟩
  have hdealloc := hc.dealloc_at
  simp only [rustDeallocSpec] at hdealloc
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP hpost
  dsimp only [tripleRatchetProgAtExt, decodeStateName] at hpc hdealloc ⊢
  decodeState_fetches b (Rust.withPanics ext) 2416 116
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  refine SepWP.weaken_pre (sepConj_mono_left (decodeErrorWith_unfold A (s.readReg64 .x20) n)) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro cap
  apply ProofLib.SepWP.exists_left; intro ptr
  apply ProofLib.SepWP.exists_left; intro w
  wp_focus_pure; rintro ⟨hn_cap, hcap_lt, hptr, hw⟩
  have hbr := kindNoHeap_branch_false hw
  refine SepWP.fold (memRegion_352_err_split x.outPtr) (by sep_focus) ?_
  wp_pull_exists
  refine SepWP.fold (stackAt_to_callee (s0.sp - 1392#64) allocHookStack (by decide)) (by sep_focus) ?_
  unfold decodeStateSavedAt
  by_cases hcap0 : cap = 0
  · have hcap_beq : (cap == 0#64) = true := beq_iff_eq.mpr hcap0
    have hite : (if cap = 0 then emp else A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)) = emp := by
      simp [hcap0]
    rw [hite, emp_sepConj]
    wp_steps
    refine SepWP.fold (box72_entails_memRegion (s.readReg64 .x20) cap ptr (BitVec.ofNat 64 n) w)
      (by sep_focus) ?_
    wp_apply
    wp_conv_pre => simp only [*]
    refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide)) (by sep_focus) ?_
    wp_steps
    try dsimp only [decodeStateSpecX]
    refine SepWP.fold (fold_decodeStateResultAt_err H_inner A x.outPtr herr) (by sep_focus) ?_
    refine SepWP.fold (decodeState_stack_restore_1296 s0.sp
      (s0.readReg64 .x29) (s0.readReg64 .x30)
      (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
      (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
      (s0.readReg64 .x20) (s0.readReg64 .x19)) (by
      unfold decodeStateSavedAt
      sep_focus) ?_
    wp_done
  · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap0
    have hshl : (cap <<< 5).toNat = cap.toNat * 32 := shl5_toNat hcap_lt
    have hite : (if cap = 0 then emp else A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)) =
        (A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)) :=
      ite_eq_right_iff.mpr fun h => absurd h hcap0
    rw [hite]
    wp_steps
    wp_apply
    wp_conv_pre => simp only [*]
    wp_steps
    refine SepWP.fold (box72_entails_memRegion (s.readReg64 .x20) cap ptr (BitVec.ofNat 64 n) w)
      (by sep_focus) ?_
    wp_apply
    wp_conv_pre => simp only [*]
    refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide)) (by sep_focus) ?_
    wp_steps
    try dsimp only [decodeStateSpecX]
    refine SepWP.fold (fold_decodeStateResultAt_err H_inner A x.outPtr herr) (by sep_focus) ?_
    refine SepWP.fold (decodeState_stack_restore_1296 s0.sp
      (s0.readReg64 .x29) (s0.readReg64 .x30)
      (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
      (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
      (s0.readReg64 .x20) (s0.readReg64 .x19)) (by
      unfold decodeStateSavedAt
      sep_focus) ?_
    wp_done

theorem protoPqRatchetState_to_memcpy (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (src dst : BitVec 64) (st : PqRatchetState) :
    protoPqRatchetStateAt H_inner A src st ∗ memRegion dst 352 ⊢
      ∃∗ srcBs : List (BitVec 8),
        ⌜srcBs.length = 352⌝ ∗
        (src ↦ₛ srcBs) ∗ memRegion dst srcBs.length ∗
        (relocProtoPqRatchetStateAt H_inner A st).1 srcBs := by
  refine Entails.trans (sepConj_mono_left ((relocProtoPqRatchetStateAt H_inner A st).2.to_bytes src)) ?_
  simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro srcBs
  refine Entails.sepExists_right srcBs ?_
  rw [sepConj_assoc, sepConj_assoc]
  apply Entails.pure_left; intro hsrc
  refine Entails.pure_right hsrc ?_
  rw [hsrc]
  exact Entails.of_eq (by ac_rfl)

theorem protoPqRatchetState_of_memcpy (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (src dst : BitVec 64) (st : PqRatchetState) {srcBs : List (BitVec 8)} (hsrc : srcBs.length = 352) :
    (dst ↦ₛ srcBs) ∗ (src ↦ₛ srcBs) ∗ (relocProtoPqRatchetStateAt H_inner A st).1 srcBs ⊢
      protoPqRatchetStateAt H_inner A dst st ∗ memRegion src 352 := by
  have h1 := (relocProtoPqRatchetStateAt H_inner A st).2.of_bytes dst srcBs hsrc
  have h2 : (src ↦ₛ srcBs) ⊢ memRegion src 352 := by
    rw [← hsrc]; exact pointsToBytes_entails_memRegion src srcBs
  have hreord :
      (dst ↦ₛ srcBs) ∗ (src ↦ₛ srcBs) ∗ (relocProtoPqRatchetStateAt H_inner A st).1 srcBs =
      ((dst ↦ₛ srcBs) ∗ (relocProtoPqRatchetStateAt H_inner A st).1 srcBs) ∗ (src ↦ₛ srcBs) := by ac_rfl
  rw [hreord]
  exact sepConj_mono h1 h2

theorem frame_4chunks_to_1296 (sp : BitVec 64) :
    memRegion (sp - 1392#64) 352 ∗
      memRegion (sp - 1040#64) 352 ∗
      memRegion (sp - 688#64) 352 ∗
      memRegion (sp - 336#64) 240 ⊢
      memRegion (sp - 1392#64) 1296 := by
  have h1 : memRegion (sp - 1392#64) 1296 =
      memRegion (sp - 1392#64) 352 ∗ memRegion (sp - 1040#64) 944 :=
    ProofLib.memRegion_split' (b := sp - 1392#64) (n := 352) (k := 944)
      (b' := sp - 1040#64) rfl (by bv_omega) (by decide)
  have h2 : memRegion (sp - 1040#64) 944 =
      memRegion (sp - 1040#64) 352 ∗ memRegion (sp - 688#64) 592 :=
    ProofLib.memRegion_split' (b := sp - 1040#64) (n := 352) (k := 592)
      (b' := sp - 688#64) rfl (by bv_omega) (by decide)
  have h3 : memRegion (sp - 688#64) 592 =
      memRegion (sp - 688#64) 352 ∗ memRegion (sp - 336#64) 240 :=
    ProofLib.memRegion_split' (b := sp - 688#64) (n := 352) (k := 240)
      (b' := sp - 336#64) rfl (by bv_omega) (by decide)
  rw [h1, h2, h3]
  exact Entails.of_eq (by ac_rfl)

theorem scratch_688_split_8 (sp : BitVec 64) :
    memRegion (sp - 688#64) 352 ⊢
      memRegion (sp - 680#64) 344 ∗
      (∃∗ w0 : BitVec 64, (sp - 688#64) ↦₆₄ w0) := by
  rw [ProofLib.memRegion_split' (b := sp - 688#64) (n := 8) (k := 344)
      (b' := sp - 680#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight (sp - 688#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.of_eq (by ac_rfl)

theorem scratch_688_fold_8 (sp w0 : BitVec 64) :
    ((sp - 688#64) ↦₆₄ w0) ∗ memRegion (sp - 680#64) 344 ⊢
      memRegion (sp - 688#64) 352 := by
  rw [ProofLib.memRegion_split' (b := sp - 688#64) (n := 8) (k := 344)
      (b' := sp - 680#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (sp - 688#64) w0)

theorem scratch_688_split_48 (sp : BitVec 64) :
    memRegion (sp - 688#64) 352 ⊢
      memRegion (sp - 680#64) 40 ∗
      memRegion (sp - 640#64) 304 ∗
      (∃∗ w0 : BitVec 64, (sp - 688#64) ↦₆₄ w0) := by
  rw [ProofLib.memRegion_split' (b := sp - 688#64) (n := 8) (k := 344)
      (b' := sp - 680#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 680#64) (n := 40) (k := 304)
      (b' := sp - 640#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight (sp - 688#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

theorem scratch_688_fold_48 (sp w0 : BitVec 64) :
    ((sp - 688#64) ↦₆₄ w0) ∗ memRegion (sp - 680#64) 40 ∗ memRegion (sp - 640#64) 304 ⊢
      memRegion (sp - 688#64) 352 := by
  rw [ProofLib.memRegion_split' (b := sp - 688#64) (n := 8) (k := 344)
      (b' := sp - 680#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 680#64) (n := 40) (k := 304)
      (b' := sp - 640#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (sp - 688#64) w0)

/-- Error tail (`0x53df4..0x53e7c`, offsets `2392..2532`):
copies the partially-decoded `proto::PqRatchetState` at `[sp + 0x160]` (`s0.sp - 1040#64`) into
`[sp + 0x2c0]` (`s0.sp - 688#64`) via `memcpy(..., 352)`, drops it via
`drop_in_place<proto::PqRatchetState>`, and executes `decodeState_err_drop_53e0c` on the boxed
`DecodeError` in `x20`. -/
theorem decodeState_err_tail_53df4 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decodeStateSpecX H_inner b A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2392#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P =
      decodeErrorAtStackLen A (s.readReg64 .x20) n ∗
      v1StateJumpTablesAt b ∗
      x.st.at A ∗
      memRegion x.outPtr 352 ∗
      A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 352 ∗
      protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 688#64) 352 ∗
      memRegion (s0.sp - 336#64) 240 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post := by
  have hmemcpy := hc.session_memcpy_at allocHookStack
  simp only [sessionMemcpySpec] at hmemcpy
  have hdrop := hc.dropProtoPqRatchetState_at
  simp only [dropProtoPqRatchetStateSpec] at hdrop
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName] at hpc hmemcpy hdrop ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2392 24
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  refine SepWP.fold (protoPqRatchetState_to_memcpy H_inner A (s0.sp - 1040#64) (s0.sp - 688#64) curSt)
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro srcBs
  wp_focus_pure; intro hsrc_len
  refine SepWP.fold (stackAt_to_callee (s0.sp - 1392#64) allocHookStack (by decide)) (by sep_focus) ?_
  wp_steps
  wp_apply
  wp_conv_pre => simp only [*]
  refine SepWP.fold (protoPqRatchetState_of_memcpy H_inner A (s0.sp - 1040#64) (s0.sp - 688#64) curSt hsrc_len)
    (by sep_focus) ?_
  refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide)) (by sep_focus) ?_
  refine SepWP.fold (stackAt_to_callee (s0.sp - 1392#64) dropOptProtoInnerStateStack (by decide))
    (by sep_focus) ?_
  wp_steps
  wp_apply
  wp_conv_pre => simp only [*]
  refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) dropOptProtoInnerStateStack (by decide))
    (by sep_focus) ?_
  refine SepWP.fold (frame_4chunks_to_1296 s0.sp) (by sep_focus) ?_
  exact decodeState_err_drop_53e0c hc x n s0 _ _ R post hpost herr
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    hs0A
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]; ac_rfl)

/-! ## 4. Panic-Aware Call Helpers (`DecodeError::push`, `DecodeError::from`) & `0x53cdc..0x53df0` -/

theorem SepWPp.call_decodeErrorPush {H_inner : V1InnerHeapPred} {b : BitVec 64} {A : RustAlloc}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (decodeErrorPushSpec A))
    (d e : BitVec 64) (n : Nat) {x_outer : DecodeStateGhost} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = d)
    (hn : n < 2 ^ 32)
    (hP : P = ((d ↦₆₄ e) ∗ decodeErrorAtStackLen A e n ∗ A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      SepWPp prog ret sf
        (((d ↦₆₄ e) ∗ decodeErrorAtStackLen A e (n + 1) ∗ A.pool ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q (decodeStatePanicPost H_inner b A x_outer s0 R)) :
    SepWPp prog ret s P Q (decodeStatePanicPost H_inner b A x_outer s0 R) := by
  let sp_cur := s0.sp - 1392#64
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - decodeErrorHookStack) ∗ F
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  refine SepWPp.call (x := (d, e, n)) (F := F_ext) hcall hpc hrun halign hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [decodeErrorPushSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hn⟩, ?_⟩
    rw [hP] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur decodeErrorHookStack (by decide))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; ac_rfl
  · intro sm _ R' _ hpost
    dsimp only [decodeErrorPushSpec] at hpost
    exact allowPanic_not_exited hpost
  · intro sm _ hm'
    dsimp only [decodeStatePanicPost, decodeStateSpecX, decodeErrorPushSpec] at hm' ⊢
    exact allowPanic_frame (allocFailedIn_trans htr) hm'
  · intro sm hpcm hrunm hspm hcsm R' hpost hL
    rw [sepConj_assoc] at hpost
    dsimp only [decodeErrorPushSpec] at hpost
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrm, hpost⟩
    rw [hsp] at hspm
    have hpost1 : sm.mem ⊨
        (((d ↦₆₄ e) ∗ decodeErrorAtStackLen A e (n + 1) ∗ A.pool ∗
          (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
            (v1StateMergeStack - decodeErrorHookStack) ∗
            stackAt sp_cur decodeErrorHookStack)) ∗ F) ∗ R' := by
      refine Satisfies.mono (Entails.of_eq ?_) hpost
      dsimp only [sp_cur, F_ext]; ac_rfl
    have hpost2 : sm.mem ⊨
        (((d ↦₆₄ e) ∗ decodeErrorAtStackLen A e (n + 1) ∗ A.pool ∗
          stackAt sp_cur v1StateMergeStack) ∗ F) ∗ R' :=
      Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (stackAt_of_callee sp_cur decodeErrorHookStack (by decide))))))) hpost1
    exact hnext sm hpcm hrunm hspm (htr.step htrm hcsm) hcsm R' hpost2 hL
  · intro sm R' _ hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

theorem SepWPp.call_decodeErrorFrom {H_inner : V1InnerHeapPred} {b : BitVec 64} {A : RustAlloc}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (decodeErrorFromSpec A))
    (k w : BitVec 64) {x_outer : DecodeStateGhost} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = k)
    (hw : KindNoHeap w)
    (hP : P = ((k ↦₆₄ w) ∗ memRegion (k + 8#64) 40 ∗ A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hnext : ∀ (sf : State) (v_k : BitVec 64),
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 →
      SepWPp prog ret sf
        ((decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗ (k ↦₆₄ v_k) ∗ memRegion (k + 8#64) 40 ∗
          A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q (decodeStatePanicPost H_inner b A x_outer s0 R)) :
    SepWPp prog ret s P Q (decodeStatePanicPost H_inner b A x_outer s0 R) := by
  let sp_cur := s0.sp - 1392#64
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - decodeErrorHookStack) ∗ F
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  refine SepWPp.call (x := (k, w)) (F := F_ext) hcall hpc hrun halign hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [decodeErrorFromSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hw⟩, ?_⟩
    rw [hP] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur decodeErrorHookStack (by decide))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; ac_rfl
  · intro sm _ R' _ hpost
    dsimp only [decodeErrorFromSpec] at hpost
    exact allowPanic_not_exited hpost
  · intro sm _ hm'
    dsimp only [decodeStatePanicPost, decodeStateSpecX, decodeErrorFromSpec] at hm' ⊢
    exact allowPanic_frame (allocFailedIn_trans htr) hm'
  · intro sm hpcm hrunm hspm hcsm R' hpost hL
    rw [sepConj_assoc] at hpost
    dsimp only [decodeErrorFromSpec] at hpost
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0_ne, htrm⟩, hpost⟩
    rw [hsp] at hspm
    rw [ProofLib.memRegion_split' (b := k) (n := 8) (k := 40)
        (b' := k + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight k] at hpost
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
    rcases hpost with ⟨v_k, hpost⟩
    have hpost1 : sm.mem ⊨
        ((decodeErrorAtStackLen A (sm.readReg64 .x0) 0 ∗ (k ↦₆₄ v_k) ∗ memRegion (k + 8#64) 40 ∗
          A.pool ∗
          (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
            (v1StateMergeStack - decodeErrorHookStack) ∗
            stackAt sp_cur decodeErrorHookStack)) ∗ F) ∗ R' := by
      refine Satisfies.mono (Entails.of_eq ?_) hpost
      dsimp only [sp_cur, F_ext]; ac_rfl
    have hpost2 : sm.mem ⊨
        ((decodeErrorAtStackLen A (sm.readReg64 .x0) 0 ∗ (k ↦₆₄ v_k) ∗ memRegion (k + 8#64) 40 ∗
          A.pool ∗ stackAt sp_cur v1StateMergeStack) ∗ F) ∗ R' :=
      Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (stackAt_of_callee sp_cur decodeErrorHookStack (by decide)))))))) hpost1
    exact hnext sm v_k hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_ne R' hpost2 hL
  · intro sm R' _ hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

/-- Error push at `0x53dec..0x53df0` (`+2384..+2388`, 2 instructions) followed by `decodeState_err_tail_53df4`:
calls `DecodeError::push` on `x0 = s0.sp - 688#64` holding `errBox`, loads `x20 := [sp + 0x2c0]`,
and drops `curSt` and `errBox`. -/
theorem decodeState_err_push_53dec {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (errBox : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hn : n < 2 ^ 32)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2384#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = s0.sp - 688#64)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P =
      ((s0.sp - 688#64) ↦₆₄ errBox) ∗
      decodeErrorAtStackLen A errBox n ∗
      v1StateJumpTablesAt b ∗
      x.st.at A ∗
      memRegion x.outPtr 352 ∗
      A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 352 ∗
      protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      memRegion (s0.sp - 336#64) 240 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hpush := hc.decodeErrorPush_at
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName] at hpc hpush ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2384 8
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP
    (mid := entry + (bv% (ls_off% "<prost::error::DecodeError>::push") - bv% (ls_off% "spqr::decode_state")))
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  refine SepWPp.call_decodeErrorPush hpush (s0.sp - 688#64) errBox n
    (ret_pc := entry + 2388#64)
    (hpc := by simp only [arm64_norm])
    (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp])
    (hs0A := hs0A)
    (hlr := by simp only [arm64_norm])
    (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx0])
    (hn := hn)
    (hP := by sep_focus) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hcs1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1
  apply SepWPp.of_sepWP_ret
  wp_steps 1
  refine SepWP.fold (scratch_688_fold_48 s0.sp errBox) (by sep_focus) ?_
  exact decodeState_err_tail_53df4 hc x curSt (n + 1) s0 _ _ R post hpost herr
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    hs0A
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]; ac_rfl)

/-- Error push at `0x53dcc..0x53df0` (`+2352..+2388`, 10 instructions):
stores `x1` (`errBox`) at `[sp + 0x2c0]` (`s0.sp - 688#64`), sets `("PqRatchetState", "version_negotiation")`,
and delegates to `decodeState_err_push_53dec`. -/
theorem decodeState_err_push_53dcc {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hn : n < 2 ^ 32)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2352#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P =
      ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeErrorAtStackLen A (s.readReg64 .x1) n ∗
      v1StateJumpTablesAt b ∗
      x.st.at A ∗
      memRegion x.outPtr 352 ∗
      A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 352 ∗
      protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      memRegion (s0.sp - 336#64) 240 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2352 32
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2384#64)
  wp_steps 8
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53dec hc x curSt (s.readReg64 .x1) n s0 _ _ R post hpost herr hn
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun])
    (by simp only [arm64_norm, hsp])
    hs0A
    (by simp only [arm64_norm, htr])
    (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, hx19])
    (by simp only [arm64_norm])

/-- Error push at `0x53cdc..0x53cfc` (`+2112..+2144`, 9 instructions):
stores `x1` (`errBox`) at `[sp + 0x2c0]` (`s0.sp - 688#64`), sets `("PqRatchetState", "chain")`,
and jumps to `0x53dec` (`decodeState_err_push_53dec`). -/
theorem decodeState_err_push_53cdc {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hn : n < 2 ^ 32)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2112#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P =
      ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeErrorAtStackLen A (s.readReg64 .x1) n ∗
      v1StateJumpTablesAt b ∗
      x.st.at A ∗
      memRegion x.outPtr 352 ∗
      A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 352 ∗
      protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      memRegion (s0.sp - 336#64) 240 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2112 36
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2384#64)
  wp_steps 9
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53dec hc x curSt (s.readReg64 .x1) n s0 _ _ R post hpost herr hn
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun])
    (by simp only [arm64_norm, hsp])
    hs0A
    (by simp only [arm64_norm, htr])
    (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, hx19])
    (by simp only [arm64_norm])

end CryptoVerification.SpqrV1.Top.DecodeState
