/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Verification of `spqr::chain_from_version_negotiation` (`0x545e4`, 18 Instructions)

Proves `chainFromVersionNegotiation_ok_of_contracts_x` and `chainFromVersionNegotiation_ok_of_contracts_ext`
from `ChainNewOkX` / `ChainNewOkExt`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout

gen_decodes libsignalSessionCode_tree libsignalSessionBin [0x4f1ec → 0x4f230]

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace ChainFromVNNorm

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

theorem chainFromVN_fnOff :
    libsignalSessionCode.fnOff chainFromVersionNegotiationName = 0x4f1ec :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) libsignalSessionCode_fnOff_0x4f1ec

theorem chainNew_fnOff :
    libsignalSessionCode.fnOff chainNewName = 0x5aaac :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) libsignalSessionCode_fnOff_0x5aaac

theorem memRegion_88_err_split (out : BitVec 64) :
    memRegion out 88 =
      (∃∗ w0 : BitVec 64, out ↦₆₄ w0) ∗
      (∃∗ b0 : BitVec 8, (out + 8#64) ↦₈ b0) ∗
      (∃∗ bs7 : List (BitVec 8), ⌜bs7.length = 7⌝ ∗ ((out + 9#64) ↦ₛ bs7)) ∗
      (∃∗ w1 : BitVec 64, (out + 16#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (out + 24#64) ↦₆₄ w2) ∗
      memRegion (out + 32#64) 56 := by
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 80)
      (b' := out + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 8#64) (n := 1) (k := 79)
      (b' := out + 9#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 9#64) (n := 7) (k := 72)
      (b' := out + 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 64)
      (b' := out + 24#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 24#64) (n := 8) (k := 56)
      (b' := out + 32#64) rfl (by bv_omega) (by decide)]
  rw [ProofLib.memRegion_eight out,
    ProofLib.memRegion_one (out + 8#64),
    ProofLib.memRegion_eq_exists_bytes (out + 9#64) 7 (by decide),
    ProofLib.memRegion_eight (out + 16#64),
    ProofLib.memRegion_eight (out + 24#64)]

theorem byte_bs7_word_to_pointsTo128 (a : BitVec 64) (b0 : BitVec 8)
    {bs7 : List (BitVec 8)} (hbs7 : bs7.length = 7) (w1 : BitVec 64) :
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦ₛ bs7) ∗ ((a + 8#64) ↦₆₄ w1)) ⊢
      ∃∗ q0 : BitVec 128, ⌜BitVec.truncate 8 q0 = b0⌝ ∗ (a ↦₁₂₈ q0) := by
  have hlen8 : (b0 :: bs7).length = 8 := by simp [hbs7]
  obtain ⟨w0, hw0_bytes⟩ := exists_unpack64_of_length_8 hlen8
  have hcons : ((a ↦₈ b0) ∗ ((a + 1#64) ↦ₛ bs7)) = (a ↦₆₄ w0) := by
    rw [← pointsToBytes_cons, hw0_bytes, ← pointsTo64_eq_pointsToBytes]
  have hb0 : BitVec.truncate 8 (w1 ++ w0) = b0 := by
    have hhead : (b0 :: bs7).head? = (unpack64 w0).head? := congrArg List.head? hw0_bytes
    simp only [unpack64, List.head?_cons, Option.some.injEq] at hhead
    have htr : BitVec.truncate 8 (w1 ++ w0) = BitVec.extractLsb' 0 8 w0 := by bv_kernel
    rw [htr, ← hhead]
  have hp128 : ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) = (a ↦₁₂₈ (w1 ++ w0)) := by
    unfold pointsTo128
    have hlo : (w1 ++ w0).extractLsb' 0 64 = w0 := by bv_kernel
    have hhi : (w1 ++ w0).extractLsb' 64 64 = w1 := by bv_kernel
    rw [hlo, hhi]
  rw [← sepConj_assoc, hcons, hp128]
  exact Entails.sepExists_right (w1 ++ w0) (Entails.pure_right hb0 (Entails.refl _))

theorem fold_chainErrorAt (out : BitVec 64) (err : Error) (tag : BitVec 8)
    (htag : tag = spqrErrorTag err)
    {bs7 : List (BitVec 8)} (hbs7 : bs7.length = 7) (w1 w2 : BitVec 64) :
    (out ↦₆₄ 18446744073709551615#64) ∗ ((out + 8#64) ↦₈ tag) ∗ ((out + 9#64) ↦ₛ bs7) ∗
      ((out + 16#64) ↦₆₄ w1) ∗ ((out + 24#64) ↦₆₄ w2) ∗ memRegion (out + 32#64) 56 ⊢
      chainErrorAt out err := by
  subst htag
  change (out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ spqrErrorTag err) ∗ ((out + 9#64) ↦ₛ bs7) ∗
      ((out + 16#64) ↦₆₄ w1) ∗ ((out + 24#64) ↦₆₄ w2) ∗ memRegion (out + 32#64) 56 ⊢
      chainErrorAt out err
  have h1 := byte_bs7_word_to_pointsTo128 (out + 8#64) (spqrErrorTag err) hbs7 w1
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
  have h2 : (out ↦₆₄ noneCap) ∗
      (((out + 8#64) ↦₈ spqrErrorTag err) ∗ ((out + 9#64) ↦ₛ bs7) ∗ ((out + 16#64) ↦₆₄ w1)) ∗
      ((out + 24#64) ↦₆₄ w2) ∗ memRegion (out + 32#64) 56 ⊢
      (out ↦₆₄ noneCap) ∗
      (∃∗ q0 : BitVec 128, ⌜BitVec.truncate 8 q0 = spqrErrorTag err⌝ ∗ ((out + 8#64) ↦₁₂₈ q0)) ∗
      ((out + 24#64) ↦₆₄ w2) ∗ memRegion (out + 32#64) 56 :=
    sepConj_mono_right (sepConj_mono_left h1)
  have h3 : (out ↦₆₄ noneCap) ∗
      (∃∗ q0 : BitVec 128, ⌜BitVec.truncate 8 q0 = spqrErrorTag err⌝ ∗ ((out + 8#64) ↦₁₂₈ q0)) ∗
      ((out + 24#64) ↦₆₄ w2) ∗ memRegion (out + 32#64) 56 ⊢
      chainErrorAt out err := by
    simp only [chainErrorAt, sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro q0
    refine Entails.sepExists_right q0 (Entails.sepExists_right w2 ?_)
    have heq :
        (out ↦₆₄ noneCap) ∗ (⌜BitVec.truncate 8 q0 = spqrErrorTag err⌝ ∗ ((out + 8#64) ↦₁₂₈ q0)) ∗
          ((out + 24#64) ↦₆₄ w2) ∗ memRegion (out + 32#64) 56 =
        ⌜BitVec.truncate 8 q0 = spqrErrorTag err⌝ ∗ (out ↦₆₄ noneCap) ∗
          ((out + 0x08#64) ↦₁₂₈ q0) ∗ ((out + 0x18#64) ↦₆₄ w2) ∗
          memRegion (out + 0x20#64) 56 := by ac_rfl
    rw [heq]
    exact Entails.refl _
  have hassoc :
      (out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ spqrErrorTag err) ∗ ((out + 9#64) ↦ₛ bs7) ∗
        ((out + 16#64) ↦₆₄ w1) ∗ ((out + 24#64) ↦₆₄ w2) ∗ memRegion (out + 32#64) 56 =
      (out ↦₆₄ noneCap) ∗
        (((out + 8#64) ↦₈ spqrErrorTag err) ∗ ((out + 9#64) ↦ₛ bs7) ∗ ((out + 16#64) ↦₆₄ w1)) ∗
        ((out + 24#64) ↦₆₄ w2) ∗ memRegion (out + 32#64) 56 := by ac_rfl
  rw [hassoc]
  exact Entails.trans h2 h3

def vecU8BufRest (A : RustAlloc) (cap ptr : BitVec 64) (len : Nat) : SepProp :=
  ⌜len ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ memRegion (ptr + BitVec.ofNat 64 len) (cap.toNat - len))

theorem vecU8At_entails_header_bytesAt_rest (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs ⊢
      ⌜bs.length < 2 ^ 63⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      bytesAt false ptr bs ∗ vecU8BufRest A cap ptr bs.length := by
  unfold vecU8At vecHeader vecU8BufRest bytesAt
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show ((v ↦₆₄ cap ∗ (v + 8#64) ↦₆₄ ptr ∗ (v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗ ptr ↦ₛ bs ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
    ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (if cap = 0 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) by ac_rfl]
  refine Entails.pure_left fun ⟨hle, hlt, hptr⟩ => ?_
  have hlen64 : bs.length < 2 ^ 63 := by omega
  refine Entails.pure_right hlen64 ?_
  by_cases hcap : cap = 0
  · subst hcap
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hbs
    simp only [↓reduceIte, pointsToBytes_nil, emp_sepConj, sepConj_emp]
    rw [show ((v ↦₆₄ (0 : BitVec 64)) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 ([] : List (BitVec 8)).length) ∗
        ⌜([] : List (BitVec 8)).length ≤ (0 : BitVec 64).toNat ∧
          (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝) =
      ⌜([] : List (BitVec 8)).length ≤ (0 : BitVec 64).toNat ∧
        (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ (0 : BitVec 64)) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 ([] : List (BitVec 8)).length)) by ac_rfl]
    exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)
  · simp only [hcap, ↓reduceIte]
    rw [show (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (ptr ↦ₛ bs) ∗
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) by ac_rfl]
    exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)

theorem header_bytesAt_rest_entails_vecU8At (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      bytesAt false ptr bs ∗ vecU8BufRest A cap ptr bs.length ⊢
      vecU8At A v cap ptr bs := by
  unfold vecU8At vecHeader vecU8BufRest bytesAt
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
    ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗
        (if cap = 0 then emp
         else A.live ptr cap.toNat 1 ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) by ac_rfl]
  refine Entails.pure_left fun ⟨hle, hlt, hptr⟩ => ?_
  rw [show ((v ↦₆₄ cap ∗ (v + 8#64) ↦₆₄ ptr ∗ (v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗ ptr ↦ₛ bs ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
    ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (if cap = 0 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) by ac_rfl]
  refine Entails.pure_right ⟨hle, hlt, hptr⟩ ?_
  by_cases hcap : cap = 0
  · subst hcap
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hbs
    simp only [↓reduceIte, pointsToBytes_nil, sepConj_emp]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

/-- `Direction.fromI32? d` characterization via unsigned comparison `(1#32).ult d`. -/
theorem direction_fromI32_or (d : BitVec 32) :
    (∃ dir : Direction,
      d = dir.toI32 ∧
      Direction.fromI32? d = some dir ∧
      (1#32).ult d = false) ∨
    (Direction.fromI32? d = none ∧
      (1#32).ult d = true) := by
  by_cases h0 : d = 0#32
  · subst h0
    exact Or.inl ⟨.a2b, rfl, rfl, rfl⟩
  · by_cases h1 : d = 1#32
    · subst h1
      exact Or.inl ⟨.b2a, rfl, rfl, rfl⟩
    · refine Or.inr ⟨by simp [Direction.fromI32?, h0, h1], ?_⟩
      rw [BitVec.ult_eq_decide, decide_eq_true_eq]
      have h0' : d.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
      have h1' : d.toNat ≠ 1 := fun h => h1 (BitVec.eq_of_toNat_eq h)
      change 1 < d.toNat
      omega

@[local simp, local arm64_norm, local wp_norm]
theorem ult_one_toI32 (dir : Direction) : (1#32).ult dir.toI32 = false := by
  cases dir <;> rfl

theorem onPanic_entails_of_trace_eq {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  unfold allocFailedIn
  rw [htr, sepConj_assoc]
  exact sepConj_mono_right (entails_anyHeap _)

theorem SepWPp.pure_left_focus {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} (φ : Prop)
    (hf : P = ⌜φ⌝ ∗ P')
    (h : φ → SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hf, sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

theorem chainNew_post_entails_chainRepr (A : RustAlloc) (out : BitVec 64) (ch : Chain) :
    (∃∗ G : ChainGhost, ⌜G.linksCap = 4#64 ∧ G.linksHead = 0#64⌝ ∗ chainAt A out G ch) ⊢
      chainRepr A out ch := by
  unfold chainRepr
  refine Entails.sepExists_elim fun G => ?_
  refine Entails.pure_left fun _ => ?_
  exact Entails.sepExists_right G (Entails.refl _)

/-- Framed tail-call (`Operation.B`) rule for `SepWPp` with an `.inImage img` callee contract. -/
theorem SepWPp.tail_call_frame_inImage {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (x : α) {s : State} {φ : Prop} {P T F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hF : ImgCallInv img s)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = ⌜φ⌝ ∗ T)
    (hφ : φ)
    (hP : P = T ∗ F)
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog ret_pc sf (spec.post x s sf ∗ F) post) :
    SepWPp prog ret_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine ProofLib.SepWPp.call_inImage_frame (x := x) (F := F) hcall hF.1 hF.2 hpc hrun hsp_align hlr
    hspec hφ hP
    (fun sf code R' _ hpost => by
      rw [hexit_eq] at hpost
      exact not_satisfies_false_sepConj hpost)
    (fun sf _ hm' => Satisfies.mono (sepConj_mono_left (hpan sf)) hm')
    (fun sm hpcm hrunm hspm hcsm _ _ => SepWPp.of_sepWP_ret (hnext sm hpcm hrunm hspm hcsm))
    (fun sf R' _ hpost => by
      rw [hoom_eq] at hpost
      exact (not_satisfies_false_sepConj hpost).elim)

theorem sub_ok_at_rebase {α : Type} {b : BitVec 64} {hooks : String → Option (State → State)}
    {name callee : String} {k : Nat} {spec : Spec α}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff callee)
    (hok : subroutine_ok (libsignalSessionCode.rebase b hooks)
      ((libsignalSessionCode.rebase b hooks).fnAddr callee) spec) :
    subroutine_ok (libsignalSessionCode.rebase b hooks)
      ((libsignalSessionCode.rebase b hooks).fnAddr name + BitVec.ofNat 64 k) spec := by
  have haddr : (libsignalSessionCode.rebase b hooks).fnAddr name + BitVec.ofNat 64 k =
      (libsignalSessionCode.rebase b hooks).fnAddr callee := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, ← hk, BitVec.ofNat_add, ← BitVec.add_assoc]
  exact haddr ▸ hok

theorem SepWPp.rw_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} (heq : P = P')
    (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  heq ▸ h

end ChainFromVNNorm

open ChainFromVNNorm

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  ult_one_toI32
  chainFromVN_fnOff chainNew_fnOff
  libsignalSessionCode_fnOff_0x4f1ec
  libsignalSessionCode_fnOff_0x5aaac

set_option maxHeartbeats 800000 in
/-- `spqr::chain_from_version_negotiation` (`0x545e4`, 18 instructions) meets
`(chainFromVersionNegotiationSpecX hkdf A).inImage img` on `tripleRatchetProgAtExt img.base ext`
assuming `ChainNewOkX img hkdf A ext`. -/
theorem chainFromVersionNegotiation_ok_of_contracts_x {img : Obj.Image} {hkdf : HkdfFn}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hnew : ChainNewOkX img hkdf A ext) :
    ChainFromVersionNegotiationOkX img hkdf A ext := by
  unfold ChainFromVersionNegotiationOkX tripleRatchetProgAtExt
  wpp_init x s0
  have hfn : libsignalSessionCode.fnOff chainFromVersionNegotiationName = 0x4f1ec :=
    chainFromVN_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x4f1ec 72
  have h_new := sub_ok_at_rebase (name := chainFromVersionNegotiationName) (callee := chainNewName)
    (k := num% (0x5aaac - 0x4f1ec)) (by rw [chainFromVN_fnOff, chainNew_fnOff]) hnew
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
        chainFromVersionNegotiationName :=
    hpc.trans (by rw [Program.fnAddr_rebase, hfn])
  clear hnew hfn
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      chainFromVersionNegotiationName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  rcases x with ⟨out, vPtr, pin, v⟩
  dsimp only [versionNegotiationPBAt] at *
  have hinv0 : ImgCallInv img s0 := ⟨h_2, h_1⟩
  subst h_3 h
  rcases direction_fromI32_or v.direction with
    ⟨dir, hdir_val, hdir_opt, hcond_hi⟩ | ⟨hdir_opt, hcond_hi⟩
  · cases hcp : v.chainParams with
    | none =>
      have hres : chainFromVersionNegotiation hkdf v = .error .chainNotAvailable := by
        simp [chainFromVersionNegotiation, hdir_opt, hcp]; rfl
      dsimp only [optChainParamsPBAt]
      refine SepWPp.rw_pre (by
        simp only [memRegion_88_err_split (s0.readReg64 (.gpr 8#5)),
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        rfl) ?_
      apply SepWPp.exists_elim; intro w2
      apply SepWPp.exists_elim; intro w1
      apply SepWPp.exists_elim; intro bs7
      apply SepWPp.exists_elim; intro b0
      apply SepWPp.exists_elim; intro w0
      refine SepWPp.pure_left_focus _ (by sep_focus) fun hbs7 => ?_
      apply SepWPp.of_sepWP_ret
      wp_steps
      rw [hres]
      dsimp only [chainResultAt]
      refine SepWP.fold (fold_chainErrorAt (s0.readReg64 (.gpr 8#5)) .chainNotAvailable 15#8 rfl hbs7 w1 w2)
        (by sep_focus) ?_
      wp_done
    | some cp =>
      have hres : chainFromVersionNegotiation hkdf v =
          .ok (chainNewVal hkdf v.authKey dir cp) := by
        simp [chainFromVersionNegotiation, hdir_opt, hcp]; rfl
      dsimp only [optChainParamsPBAt]
      refine SepWPp.fold (vecU8At_entails_header_bytesAt_rest A
        (s0.readReg64 (.gpr 0#5)) pin.cap pin.ptr v.authKey) (by sep_focus) ?_
      refine SepWPp.pure_left_focus _ (by sep_focus) fun hlen64 => ?_
      refine SepWPp.of_sepWP_inImage (mid := entry + bv% (0x5aaac - 0x4f1ec)) hinv0 ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv1
      apply (SepWPp.tail_call_frame_inImage h_new
        (⟨s0.readReg64 (.gpr 8#5), false, pin.ptr, v.authKey, dir, cp⟩ : ChainNewGhost)
        hinv1)
      · wp_focus_close wp_norm_goal
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · rfl
      · refine ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hlen64⟩
      · rw [show (((((((((s0.writeReg64 (.gpr 3#5) (BitVec.zeroExtend 64 dir.toI32)).writeReg64
            (.gpr 9#5) 1#64).writeReg64 (.gpr 1#5) pin.ptr).writeReg64
            (.gpr 2#5) (BitVec.ofNat 64 v.authKey.length)).writeReg64
            (.gpr 4#5) (BitVec.zeroExtend 64 cp.maxJump)).writeReg64
            (.gpr 5#5) (BitVec.zeroExtend 64 cp.maxOooKeys)).writeReg64
            (.gpr 0#5) (s0.readReg64 (.gpr 8#5))).setPState
            (subsPState32 dir.toI32 1#32)).setPC (entry + 47296#64)).sp = s0.sp by wp_norm_lhs]
        sep_focus
      · intro sf
        exact onPanic_entails_of_trace_eq (by wp_norm_lhs)
      · intro _ _; rfl
      · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
        dsimp only [chainNewSpecX]
        refine SepWP.focus_pure (by sep_focus) fun htr_sf => ?_
        rw [hres]
        dsimp only [chainResultAt]
        refine SepWP.fold (chainNew_post_entails_chainRepr A (s0.readReg64 (.gpr 8#5)) _)
          (by sep_focus) ?_
        refine SepWP.fold (header_bytesAt_rest_entails_vecU8At A
          (s0.readReg64 (.gpr 0#5)) pin.cap pin.ptr v.authKey) (by sep_focus) ?_
        wp_done
  · have hres : chainFromVersionNegotiation hkdf v = .error .stateDecode := by
      simp [chainFromVersionNegotiation, hdir_opt]; rfl
    refine SepWPp.rw_pre (by
      simp only [memRegion_88_err_split (s0.readReg64 (.gpr 8#5)),
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      rfl) ?_
    apply SepWPp.exists_elim; intro w2
    apply SepWPp.exists_elim; intro w1
    apply SepWPp.exists_elim; intro bs7
    apply SepWPp.exists_elim; intro b0
    apply SepWPp.exists_elim; intro w0
    refine SepWPp.pure_left_focus _ (by sep_focus) fun hbs7 => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    rw [hres]
    dsimp only [chainResultAt]
    refine SepWP.fold (fold_chainErrorAt (s0.readReg64 (.gpr 8#5)) .stateDecode 0#8 rfl hbs7 w1 w2)
      (by sep_focus) ?_
    wp_done

set_option maxHeartbeats 800000 in
/-- Contract-backed (`*Ext`) verification of `spqr::chain_from_version_negotiation` (`0x545e4`,
18 instructions) at `chainFromVersionNegotiationStackExt` (`17840` B), assuming
`ChainNewOkExt img hkdf A ext`. -/
theorem chainFromVersionNegotiation_ok_of_contracts_ext {img : Obj.Image} {hkdf : HkdfFn}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hnew : ChainNewOkExt img hkdf A ext) :
    ChainFromVersionNegotiationOkExt img hkdf A ext := by
  unfold ChainFromVersionNegotiationOkExt tripleRatchetProgAtExt
  wpp_init x s0
  have hfn : libsignalSessionCode.fnOff chainFromVersionNegotiationName = 0x4f1ec :=
    chainFromVN_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x4f1ec 72
  have h_new := sub_ok_at_rebase (name := chainFromVersionNegotiationName) (callee := chainNewName)
    (k := num% (0x5aaac - 0x4f1ec)) (by rw [chainFromVN_fnOff, chainNew_fnOff]) hnew
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
        chainFromVersionNegotiationName :=
    hpc.trans (by rw [Program.fnAddr_rebase, hfn])
  clear hnew hfn
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      chainFromVersionNegotiationName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  rcases x with ⟨out, vPtr, pin, v⟩
  dsimp only [versionNegotiationPBAt] at *
  have hinv0 : ImgCallInv img s0 := ⟨h_2, h_1⟩
  subst h_3 h
  rcases direction_fromI32_or v.direction with
    ⟨dir, hdir_val, hdir_opt, hcond_hi⟩ | ⟨hdir_opt, hcond_hi⟩
  · cases hcp : v.chainParams with
    | none =>
      have hres : chainFromVersionNegotiation hkdf v = .error .chainNotAvailable := by
        simp [chainFromVersionNegotiation, hdir_opt, hcp]; rfl
      dsimp only [optChainParamsPBAt]
      refine SepWPp.rw_pre (by
        simp only [memRegion_88_err_split (s0.readReg64 (.gpr 8#5)),
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        rfl) ?_
      apply SepWPp.exists_elim; intro w2
      apply SepWPp.exists_elim; intro w1
      apply SepWPp.exists_elim; intro bs7
      apply SepWPp.exists_elim; intro b0
      apply SepWPp.exists_elim; intro w0
      refine SepWPp.pure_left_focus _ (by sep_focus) fun hbs7 => ?_
      apply SepWPp.of_sepWP_ret
      wp_steps
      rw [hres]
      dsimp only [chainResultAt]
      refine SepWP.fold (fold_chainErrorAt (s0.readReg64 (.gpr 8#5)) .chainNotAvailable 15#8 rfl hbs7 w1 w2)
        (by sep_focus) ?_
      wp_done
    | some cp =>
      have hres : chainFromVersionNegotiation hkdf v =
          .ok (chainNewVal hkdf v.authKey dir cp) := by
        simp [chainFromVersionNegotiation, hdir_opt, hcp]; rfl
      dsimp only [optChainParamsPBAt]
      refine SepWPp.fold (vecU8At_entails_header_bytesAt_rest A
        (s0.readReg64 (.gpr 0#5)) pin.cap pin.ptr v.authKey) (by sep_focus) ?_
      refine SepWPp.pure_left_focus _ (by sep_focus) fun hlen64 => ?_
      refine SepWPp.of_sepWP_inImage (mid := entry + bv% (0x5aaac - 0x4f1ec)) hinv0 ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv1
      apply (SepWPp.tail_call_frame_inImage h_new
        (⟨s0.readReg64 (.gpr 8#5), false, pin.ptr, v.authKey, dir, cp⟩ : ChainNewGhost)
        hinv1)
      · wp_focus_close wp_norm_goal
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · rfl
      · refine ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hlen64, Or.inl Bool.noConfusion⟩
      · rw [show (((((((((s0.writeReg64 (.gpr 3#5) (BitVec.zeroExtend 64 dir.toI32)).writeReg64
            (.gpr 9#5) 1#64).writeReg64 (.gpr 1#5) pin.ptr).writeReg64
            (.gpr 2#5) (BitVec.ofNat 64 v.authKey.length)).writeReg64
            (.gpr 4#5) (BitVec.zeroExtend 64 cp.maxJump)).writeReg64
            (.gpr 5#5) (BitVec.zeroExtend 64 cp.maxOooKeys)).writeReg64
            (.gpr 0#5) (s0.readReg64 (.gpr 8#5))).setPState
            (subsPState32 dir.toI32 1#32)).setPC (entry + 47296#64)).sp = s0.sp by wp_norm_lhs]
        sep_focus
      · intro sf
        exact onPanic_entails_of_trace_eq (by wp_norm_lhs)
      · intro _ _; rfl
      · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
        dsimp only [chainNewSpecExt]
        refine SepWP.focus_pure (by sep_focus) fun htr_sf => ?_
        rw [hres]
        dsimp only [chainResultAt]
        refine SepWP.fold (chainNew_post_entails_chainRepr A (s0.readReg64 (.gpr 8#5)) _)
          (by sep_focus) ?_
        refine SepWP.fold (header_bytesAt_rest_entails_vecU8At A
          (s0.readReg64 (.gpr 0#5)) pin.cap pin.ptr v.authKey) (by sep_focus) ?_
        wp_done
  · have hres : chainFromVersionNegotiation hkdf v = .error .stateDecode := by
      simp [chainFromVersionNegotiation, hdir_opt]; rfl
    refine SepWPp.rw_pre (by
      simp only [memRegion_88_err_split (s0.readReg64 (.gpr 8#5)),
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      rfl) ?_
    apply SepWPp.exists_elim; intro w2
    apply SepWPp.exists_elim; intro w1
    apply SepWPp.exists_elim; intro bs7
    apply SepWPp.exists_elim; intro b0
    apply SepWPp.exists_elim; intro w0
    refine SepWPp.pure_left_focus _ (by sep_focus) fun hbs7 => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    rw [hres]
    dsimp only [chainResultAt]
    refine SepWP.fold (fold_chainErrorAt (s0.readReg64 (.gpr 8#5)) .stateDecode 0#8 rfl hbs7 w1 w2)
      (by sep_focus) ?_
    wp_done

abbrev chainFromVersionNegotiation_ok_ext := @chainFromVersionNegotiation_ok_of_contracts_ext

end CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
