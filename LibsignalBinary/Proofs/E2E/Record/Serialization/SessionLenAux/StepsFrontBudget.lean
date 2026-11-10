/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.StepsFront
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.Decode
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `VmPreserved`-threaded front step lemmas for `SessionStructure::encoded_len`

Relocatable `[LibsignalPlacement]` front step lemmas for block `86` (tags 1–5 and `Chain::encoded_len`
call wrappers against `DefsBudget.chainLenSpec`), threading `VmPreserved`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.StepsFrontBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (ReceiverChain)
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (
  LibsignalPlacement LibsignalCodeLoaded lsmpl withLsCodeLoaded sepWP_mono_lscl
)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  optU32Tag_beq_one optU32Tag_bne_one zext64_optU32Tag_truncate32
  ult_ofNat_add_of_lt ule_ofNat_add_of_lt bv_add_ofNat_comm
)
open CryptoVerification.E2E.Record (bytesField uint32Field)
open CryptoVerification.E2E.Record.Placed (blkPl_86 blkPl_88 lsProg_86)
open CryptoVerification.E2E.Record.Serialization (chainLenStack encChainMem protoChainAt)
open CryptoVerification.E2E.Record.Serialization.SessionLenAux (
  sessHwVarintLen_eq_encodeVarint_length sessHwVarintLen_bvShift_eq_encodeVarint_length
  sess_truncate32_zext64_lsr6
  sessHwVarintLen_w32_eq_encodeVarint_length sessHwVarintLen_w32_natShift_eq_encodeVarint_length
  sess_ule_zero_64 sess_ult_zero_64
  ofNat64_length_beq_zero_of_bytesField_lt ofNat64_length_bne_zero_of_bytesField_lt
  bv_bytesField_nonempty_length bv_uint32Field_nonzero_length bytesField_rootKey_length
  chainAt_eq_protoChainAt tags1to5Cells frameCells SessLenCalleeSaved add_neg64_eq_sub64
  sepWPp_of_sepWP_lscl
)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (chainLenSpec)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm]
  bv_sub_add_lit BitVec.toNat_zero
  sessHwVarintLen_eq_encodeVarint_length
  sessHwVarintLen_bvShift_eq_encodeVarint_length
  ofNat_countLeadingZeros_64
  ofNat_countLeadingZeros_32
  CryptoVerification.LibsignalTripleRatchet.Prost.truncate32_ofNat64
  sess_truncate32_zext64_lsr6
  sessHwVarintLen_w32_eq_encodeVarint_length
  sessHwVarintLen_w32_natShift_eq_encodeVarint_length
  noneCap_add_one_beq_zero
  noneCap_add_one_bne_zero
  optU32Tag_beq_one
  optU32Tag_bne_one
  zext64_optU32Tag_truncate32
  sess_ule_zero_64
  sess_ult_zero_64
attribute [local simp, local arm64_norm] add_neg64_eq_sub64

theorem sepWPp_of_sepWP_lscl_vm {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {pl : Obj.MultiPlacement} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      VmPreserved s sm ∧ (VmPreserved s sm → LibsignalCodeLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp))) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (sepWP_mono_lscl hcl h (fun _ _ _ _ hclm ⟨hvm, hnext⟩ => hnext hvm hclm))

theorem call_protoChainLen_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hchain : subroutine_ok (lsProg_86 H) (blkPl_88).base
      (withLsCodeLoaded lsmpl (chainLenSpec A)))
    (a ret_pc : BitVec 64) (gc : ChainGhost × ReceiverChain)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_88).base)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = a)
    (hfit : (encChainMem gc).length < 2 ^ 32)
    (hP : P = (protoChainAt A gc a ∗ stackAt s.sp chainLenStack) ∗ F)
    (hnext : ∀ sf : State,
      VmPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (encChainMem gc).length →
      CalleeSavedPreserved s sf →
      SepWPp (lsProg_86 H) ret sf P Q Qp) :
    SepWPp (lsProg_86 H) ret s P Q Qp := by
  refine sepWPp_of_sepWP_lscl (mid := ret_pc) hcl ?_
  refine SepWP.call_subroutine_frame hchain (x := ⟨a, gc⟩) (F := F) hpc hrun hsp hlr
    (fun R hm => ?_)
    (fun _ _ _ hpost => by dsimp only [withLsCodeLoaded, chainLenSpec] at hpost; exact not_satisfies_false_sepConj hpost)
    (fun _ _ _ _ hpost => by dsimp only [withLsCodeLoaded, chainLenSpec] at hpost; exact not_satisfies_false_sepConj hpost)
    (fun sm hpcm hrunm hspm hcsm => ProofLib.SepWP.done hpcm hrunm fun hclm => ?_)
    (fun _ _ _ hpost => by dsimp only [withLsCodeLoaded, chainLenSpec] at hpost; exact (not_satisfies_false_sepConj hpost).elim)
  · dsimp only [withLsCodeLoaded, chainLenSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hfit⟩, ?_⟩
    rw [← sepConj_assoc, ← sepConj_assoc, ← hP]
    exact hm
  · dsimp only [withLsCodeLoaded, chainLenSpec]
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨hx0_m, htr_m, hvm_m⟩ => ?_
    refine SepWPp.congr_pre ?_ (hnext sm hvm_m hclm hpcm hrunm hspm htr_m hx0_m hcsm)
    rw [hP, sepConj_assoc]

theorem call_chainLen_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hchain : subroutine_ok (lsProg_86 H) (blkPl_88).base
      (withLsCodeLoaded lsmpl (chainLenSpec A)))
    (a ret_pc : BitVec 64) (gc : ChainGhost × ReceiverChain)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_88).base)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = a)
    (hfit : (encChainMem gc).length < 2 ^ 32)
    (hP : P = (chainAt A gc a ∗ stackAt s.sp chainLenStack) ∗ F)
    (hnext : ∀ sf : State,
      VmPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (encChainMem gc).length →
      CalleeSavedPreserved s sf →
      SepWPp (lsProg_86 H) ret sf P Q Qp) :
    SepWPp (lsProg_86 H) ret s P Q Qp := by
  have hP' : P = (protoChainAt A gc a ∗ stackAt s.sp chainLenStack) ∗
      (⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗ F) := by
    rw [hP, chainAt_eq_protoChainAt A gc a]; sep_ac_rfl
  exact call_protoChainLen_placed A H hchain a ret_pc gc
    hcl hpc hrun hsp hlr hx0 hfit hP' hnext

theorem step_sessLen_f1_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (ss sp v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64)
    (G : SessionGhost) (m : Session (List (BitVec 8)))
    (hloc_fit : (bytesField 2 G.localIk.bytes).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_86).base)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = ss)
    (hP : P = (tags1to5Cells ss G m ∗ frameCells sp v64 v56 v48 v40 v32 v24 v16 v8) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = (if G.localIk.bytes = [] then
        (blkPl_86).base + 248#64
      else
        (blkPl_86).base + 68#64) →
      sm.status = .Running →
      sm.sp = sp - 64#64 →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64 (uint32Field 1 m.state.sessionVersion).length →
      sm.readReg64 .x9 = BitVec.ofNat 64 G.localIk.bytes.length →
      SessLenCalleeSaved s sm →
      SepWPp (lsProg_86 H) ret sm
        ((tags1to5Cells ss G m ∗
          frameCells sp (s.readReg64 .fp) (s.readReg64 .lr)
            (s.readReg64 .x24) (s.readReg64 .x23)
            (s.readReg64 .x22) (s.readReg64 .x21)
            (s.readReg64 .x20) (s.readReg64 .x19)) ∗ F) Q Qp) :
    SepWPp (lsProg_86 H) ret s P Q Qp := by
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
    by_cases hloc : G.localIk.bytes = []
    · have hloc_b : (G.localIk.bytes == []) = true := beq_iff_eq.mpr hloc
      have hloc_bn : (G.localIk.bytes != []) = false := bne_eq_false_iff_eq.mpr hloc
      apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_86).base + bv% (248))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], fun hvm hclm => ?_⟩
        rw [← hT, ← hFr1]
        exact hnext _ hvm hclm (by simp_all) (by simp_all) (by simp_all)
          (by simp_all) (by simp_all) (by simp_all [uint32Field]) (by simp_all)
          (by simp_all [SessLenCalleeSaved])
    · have hloc_b : (G.localIk.bytes == []) = false := beq_eq_false_iff_ne.mpr hloc
      have hloc_bn : (G.localIk.bytes != []) = true := bne_iff_ne.mpr hloc
      apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_86).base + bv% (68))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], fun hvm hclm => ?_⟩
        rw [← hT, ← hFr1]
        exact hnext _ hvm hclm (by simp_all) (by simp_all) (by simp_all)
          (by simp_all) (by simp_all) (by simp_all [uint32Field]) (by simp_all)
          (by simp_all [SessLenCalleeSaved])
  · have hver_beq : (m.state.sessionVersion == 0#32) = false := beq_eq_false_iff_ne.mpr hver
    have henc := bv_uint32Field_nonzero_length (t := 1) hver rfl
    by_cases hloc : G.localIk.bytes = []
    · have hloc_b : (G.localIk.bytes == []) = true := beq_iff_eq.mpr hloc
      have hloc_bn : (G.localIk.bytes != []) = false := bne_eq_false_iff_eq.mpr hloc
      apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_86).base + bv% (248))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], fun hvm hclm => ?_⟩
        rw [← hT, ← hFr1]
        exact hnext _ hvm hclm (by simp_all) (by simp_all) (by simp_all)
          (by simp_all) (by simp_all) (by simp_all) (by simp_all)
          (by simp_all [SessLenCalleeSaved])
    · have hloc_b : (G.localIk.bytes == []) = false := beq_eq_false_iff_ne.mpr hloc
      have hloc_bn : (G.localIk.bytes != []) = true := bne_iff_ne.mpr hloc
      apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_86).base + bv% (68))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], fun hvm hclm => ?_⟩
        rw [← hT, ← hFr1]
        exact hnext _ hvm hclm (by simp_all) (by simp_all) (by simp_all)
          (by simp_all) (by simp_all) (by simp_all) (by simp_all)
          (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_f2_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (ss : BitVec 64) (G : SessionGhost) (m : Session (List (BitVec 8))) (s1 : Nat)
    (hrem_fit : (bytesField 3 G.remoteIk.bytes).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (if G.localIk.bytes = [] then
      (blkPl_86).base + 248#64
    else
      (blkPl_86).base + 68#64))
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 G.localIk.bytes.length)
    (hP : P = tags1to5Cells ss G m ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = (if G.remoteIk.bytes = [] then
        (blkPl_86).base + 144#64
      else
        (blkPl_86).base + 108#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1 + (bytesField 2 G.localIk.bytes).length) →
      sm.readReg64 .x9 = BitVec.ofNat 64 G.remoteIk.bytes.length →
      SessLenCalleeSaved s sm →
      SepWPp (lsProg_86 H) ret sm P Q Qp) :
    SepWPp (lsProg_86 H) ret s P Q Qp := by
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
      apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_86).base + bv% (144))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], fun hvm hclm => ?_⟩
        rw [← hT]
        exact hnext _ hvm hclm (by simp_all) (by simp_all) (by simp_all)
          (by simp_all) (by simp_all) (by simp_all [bytesField]) (by simp_all)
          (by simp_all [SessLenCalleeSaved])
    · have hrem_b : (G.remoteIk.bytes == []) = false := beq_eq_false_iff_ne.mpr hrem
      have hrem_bn : (G.remoteIk.bytes != []) = true := bne_iff_ne.mpr hrem
      apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_86).base + bv% (108))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], fun hvm hclm => ?_⟩
        rw [← hT]
        exact hnext _ hvm hclm (by simp_all) (by simp_all) (by simp_all)
          (by simp_all) (by simp_all) (by simp_all [bytesField]) (by simp_all)
          (by simp_all [SessLenCalleeSaved])
  · simp only [hloc, ↓reduceIte] at hpc
    have henc := bv_bytesField_nonempty_length (t := 2) hloc rfl
    have hadd := bv_add_ofNat_comm s1 (bytesField 2 G.localIk.bytes).length
    by_cases hrem : G.remoteIk.bytes = []
    · have hrem_b : (G.remoteIk.bytes == []) = true := beq_iff_eq.mpr hrem
      have hrem_bn : (G.remoteIk.bytes != []) = false := bne_eq_false_iff_eq.mpr hrem
      apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_86).base + bv% (144))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], fun hvm hclm => ?_⟩
        rw [← hT]
        exact hnext _ hvm hclm (by simp_all) (by simp_all) (by simp_all)
          (by simp_all) (by simp_all) (by simp_all) (by simp_all)
          (by simp_all [SessLenCalleeSaved])
    · have hrem_b : (G.remoteIk.bytes == []) = false := beq_eq_false_iff_ne.mpr hrem
      have hrem_bn : (G.remoteIk.bytes != []) = true := bne_iff_ne.mpr hrem
      apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_86).base + bv% (108))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], fun hvm hclm => ?_⟩
        rw [← hT]
        exact hnext _ hvm hclm (by simp_all) (by simp_all) (by simp_all)
          (by simp_all) (by simp_all) (by simp_all) (by simp_all)
          (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_f3_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (ss : BitVec 64) (G : SessionGhost) (m : Session (List (BitVec 8))) (s12 : Nat)
    (hfit : s12 + (bytesField 3 G.remoteIk.bytes).length +
      (bytesField 4 (keyToBytes32 m.state.rootKey)).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (if G.remoteIk.bytes = [] then
      (blkPl_86).base + 144#64
    else
      (blkPl_86).base + 108#64))
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s12)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 G.remoteIk.bytes.length)
    (hP : P = tags1to5Cells ss G m ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = (blkPl_86).base + 188#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64
        (s12 + (bytesField 3 G.remoteIk.bytes).length +
         (bytesField 4 (keyToBytes32 m.state.rootKey)).length) →
      SessLenCalleeSaved s sm →
      SepWPp (lsProg_86 H) ret sm P Q Qp) :
    SepWPp (lsProg_86 H) ret s P Q Qp := by
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
    apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_86).base + bv% (188))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], fun hvm hclm => ?_⟩
      rw [← hT]
      exact hnext _ hvm hclm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all [bytesField]) (by simp_all [SessLenCalleeSaved])
  · simp only [hrem, ↓reduceIte] at hpc
    have henc3 := bv_bytesField_nonempty_length (t := 3) hrem rfl
    have hcc3 := ult_ofNat_add_of_lt hfit3
    have hadd3 := bv_add_ofNat_comm s12 (bytesField 3 G.remoteIk.bytes).length
    apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_86).base + bv% (188))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], fun hvm hclm => ?_⟩
      rw [← hT]
      exact hnext _ hvm hclm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_f4_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (ss : BitVec 64) (G : SessionGhost) (m : Session (List (BitVec 8))) (s1234 : Nat)
    (hfit : s1234 + (uint32Field 5 m.state.previousCounter).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_86).base + 188#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1234)
    (hP : P = tags1to5Cells ss G m ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = (blkPl_86).base + 272#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x20 = BitVec.ofNat 64 (s1234 + (uint32Field 5 m.state.previousCounter).length) →
      SessLenCalleeSaved s sm →
      SepWPp (lsProg_86 H) ret sm P Q Qp) :
    SepWPp (lsProg_86 H) ret s P Q Qp := by
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
    apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_86).base + bv% (272))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], fun hvm hclm => ?_⟩
      rw [← hT]
      exact hnext _ hvm hclm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all [uint32Field]) (by simp_all [SessLenCalleeSaved])
  · have hprev_beq : (m.state.previousCounter == 0#32) = false := beq_eq_false_iff_ne.mpr hprev
    have henc := bv_uint32Field_nonzero_length (t := 5) hprev rfl
    have hcc := ule_ofNat_add_of_lt hfit
    have hcc_ult := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s1234 (uint32Field 5 m.state.previousCounter).length
    apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_86).base + bv% (272))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], fun hvm hclm => ?_⟩
      rw [← hT]
      exact hnext _ hvm hclm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])

end LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.StepsFrontBudget
