/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Defs
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodeToVecCodeSym
import ProofLib.SepLogic.WPp

/-!
# `PqRatchetState::encode_to_vec` (Block `426`): Placed Specifications and `StepInv` Bridges

Relocatable `[LibsignalPlacement]` `.rodata` jump-table assertions, pinned/unpinned specifications,
and `StepInv` combinators for `PqRatchetState::encode_to_vec` (`Block 426`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr

theorem StepInv.codeLoaded {s0 s : State} (hinv : StepInv s0 s) {prog : Program}
    (hL : prog.CodeLoaded s0.mem) : prog.CodeLoaded s.mem := by
  let img : Obj.Image := {
    base := prog.base
    code := prog.code
    dataAddr := 0
    data := []
    roData := []
    externData := []
    gotAddr := 0
    got := []
    symbols := []
    stubs := []
  }
  have hfl0 : img.FrozenLoaded s0 := by
    refine Obj.Image.frozenLoaded_iff.2 ⟨hL.of_base_code rfl rfl, ?_, ?_⟩
    · intro i hi; simp [img] at hi
    · intro i hi; simp [Obj.Image.gotBytes, img] at hi
  exact (Obj.Image.frozenLoaded_iff.1 (hinv.1 img hfl0)).1.of_base_code rfl rfl

theorem StepInv.holdsBytes_ro {s0 s : State} (hinv : StepInv s0 s) {a : BitVec 64}
    {bs : List (BitVec 8)} (hro : Obj.HoldsBytes s0.mem a bs (fun _ => Perm.ro)) :
    Obj.HoldsBytes s.mem a bs (fun _ => Perm.ro) := by
  let img : Obj.Image := {
    base := 0
    code := []
    dataAddr := a
    data := bs
    roData := [(a, 2 ^ 64)]
    externData := []
    gotAddr := 0
    got := []
    symbols := []
    stubs := []
  }
  have hfl0 : img.FrozenLoaded s0 := by
    refine Obj.Image.frozenLoaded_iff.2 ⟨?_, ?_, ?_⟩
    · refine Program.CodeLoaded.intro (by simp [Program.ofImage, img]) (by simp [Program.ofImage, img]) (fun i hi => ?_)
      simp [Program.ofImage, img] at hi
    · intro i hi
      dsimp only [img]
      intro _
      exact hro i hi
    · intro i hi; simp [Obj.Image.gotBytes, img] at hi
  have hrod := (Obj.Image.frozenLoaded_iff.1 (hinv.1 img hfl0)).2.1
  intro i hi
  apply hrod i hi
  simp only [Obj.Image.isRoData, img, List.any_cons, List.any_nil, Bool.or_false,
    decide_eq_true_eq]
  exact BitVec.isLt _

theorem StepInv.libsignalCodeLoaded {s0 s : State} (hinv : StepInv s0 s) {pl : MultiPlacement}
    (hcl : LibsignalCodeLoaded pl s0.mem) : LibsignalCodeLoaded pl s.mem :=
  fun i hi hunmut X O svc => hinv.codeLoaded (hcl i hi hunmut X O svc)

theorem StepInv.libsignalRoLoaded {s0 s : State} (hinv : StepInv s0 s) {pl : MultiPlacement}
    (hro : LibsignalRoLoaded pl s0.mem) : LibsignalRoLoaded pl s.mem :=
  fun d hd hrd => hinv.holdsBytes_ro (hro d hd hrd)

theorem subroutine_ok_withStepInv_lscl {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : MultiPlacement} {spec : Spec α} {s0 : State}
    (hcl0 : LibsignalCodeLoaded pl s0.mem)
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec)) :
    subroutine_ok prog entry (withStepInv s0 spec) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  rw [withStepInv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hinv, hpre⟩ := hpre
  have hpre' : s.mem ⊨ (withLsCodeLoaded pl spec).pre x s ∗ R := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hinv.libsignalCodeLoaded hcl0, hpre⟩
  exact h.mono_outcome x R s hpc hrun hpre' hsp fun _ hout => hout

open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (ule_self_64 ult_self_64
   ofNat_length_beq_zero_of_lt bv_u32VarintField_nonzero bv_bytesField_nonempty
   bv_add_ofNat_comm bv_add_ofNat_eq adds_no_overflow_of_eq cmp_ls_false_of_lt)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

theorem step_encodeToVec_vn_authKey_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (a : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (hlen : vn.authKey.length < 2 ^ 64)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_426).base + 52#64) (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = versionNegotiationRest A g a vn ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = (blkPl_426).base + 88#64 → s1.status = .Running → s1.sp = s.sp → s1.trace = s.trace →
      s1.readReg64 .x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey) →
      s1.readReg64 .x20 = a → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 s1 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s1 (versionNegotiationRest A g a vn ∗ F) Q Qp) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp := by
  subst hP
  dsimp only [versionNegotiationRest]
  obtain ⟨hbeqz, hbnez⟩ := EncodedLen.ofNat_length_beq_zero_of_lt hlen
  cases hemp : vn.authKey.isEmpty
  · have hstep := EncodedLen.bv_bytesField_nonempty hemp
    simp only [hemp, Bool.not_false] at hbeqz hbnez
    apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 88#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (hinv0.trans hinv)
  · simp only [hemp, Bool.not_true] at hbeqz hbnez
    have hzero : bytesFieldEncodedLen vn.authKey = vn.authKey.length := by
      unfold bytesFieldEncodedLen
      cases h : vn.authKey with
      | nil => rfl
      | cons _ _ => rw [h] at hemp; cases hemp
    apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 88#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hzero, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (hinv0.trans hinv)

end CryptoVerification.SpqrV1.Prost.EncodeToVec
