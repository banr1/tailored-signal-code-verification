/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.VersionNegPhase
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhasePlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MessageEncodeCodeSym
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLenBase
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncode
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Relocatable `spqr::send::<HookRng>` Phase 3c (`+4996..+5604`): `Option<VersionNegotiation>` Encoding

Verifies the inlined `Option<VersionNegotiation>` encoding phase (`+4996..+5604`) inside
Block 124 (`spqr::send::<libsignal_session::HookRng>`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Top.Send.Placed

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64
  spqrSendPlacedEntry

/-! ## Call Wrappers -/

theorem step_send_encode_varint_call_placed {resStack : Nat}
    {prog : Program} (A : RustAlloc)
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok prog call_pc
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (val v cap ptr sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeVarint val).length ≤ cap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (vecU8At A v cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        ((vecU8At A v cap ptr (bs ++ Proto.encodeVarint val) ∗ A.pool ∗
          stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_encode_varint_call_prog A henc val v cap ptr (sp + 144#64) ret_pc bs hfit
    hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hx0 hx1 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hcsm hinvm)

theorem step_send_memcpy_call_placed
    {prog : Program}
    {call_pc : BitVec 64} {s0 s : State}
    (hmemcpy : subroutine_ok prog call_pc etvMemcpyRegionSpec)
    (dst src sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hinv0 : StepInv s0 s)
    (hP : P = (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  refine step_etv_memcpy_call_prog hmemcpy dst src (sp + 144#64) ret_pc bs
    hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hx0 hx1 hx2 hinv0 hP ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm
  rw [sp_add_144_sub_144] at hspm
  exact hnext sm hpcm hrunm hspm htrm hcsm hinvm

theorem step_send_encode_chainParams_call_placed {resStack : Nat}
    {prog : Program} (A : RustAlloc)
    {call_pc : BitVec 64} {s0 s : State}
    (hcp : subroutine_ok prog call_pc
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A)))
    (tag : BitVec 32) (p : ChainParamsPB) (v cap ptr sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    (htag1 : 1 ≤ tag.toNat) (htag2 : tag.toNat < 2 ^ 29)
    (hfit : bs.length + (Proto.encodeMessage ChainParamsPB.encodeRaw tag p).length ≤ cap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hw0 : s.readReg32 .x0 = tag)
    (hw1 : s.readReg32 .x1 = p.maxJump)
    (hw2 : s.readReg32 .x2 = p.maxOooKeys)
    (hx3 : s.readReg64 .x3 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (vecU8At A v cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        ((vecU8At A v cap ptr (bs ++ Proto.encodeMessage ChainParamsPB.encodeRaw tag p) ∗ A.pool ∗
          stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_encode_chainParams_call_prog A hcp tag p v cap ptr (sp + 144#64) ret_pc bs
    htag1 htag2 hfit hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hw0 hw1 hw2 hx3 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hcsm hinvm)

/-! ## `VersionNegotiationPB` Encoding Sub-Steps (`+4996..+5604`) -/

/-- Step `spqrSendPlacedEntry + 4996#64 .. spqrSendPlacedEntry + 5020#64`: writes outer
`VersionNegotiation` tag `0x0a#8` into `vecU8At A (sp + 1424#64) cap ptr []` and loads
`x26 = BitVec.ofNat 64 vn.authKey.length`. -/
theorem step_send_vn_push_tag_31be0_placed (A : RustAlloc)
    (ext : String → Option (State → State))
    (sp cap ptr : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (hpos : 0 < cap.toNat) (halign : sp &&& 15#64 = 0#64)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 4996#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hx0 : s.readReg64 .x0 = ptr) (hinv0 : StepInv s0 s)
    (hP : P = (versionNegotiationRest A g (sp + 4704#64) vn ∗ vecU8At A (sp + 1424#64) cap ptr []) ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = spqrSendPlacedEntry + 5020#64 → s1.status = .Running → s1.sp = sp → s1.trace = s.trace →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 → s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = BitVec.ofNat 64 vn.authKey.length →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .fp = s.readReg64 .fp → StepInv s0 s1 →
      SepWPp (spqrSendPlacedProg ext) ret s1
        ((versionNegotiationRest A g (sp + 4704#64) vn ∗
          vecU8At A (sp + 1424#64) cap ptr [0x0a#8]) ∗ F) Q Qp) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := [])
    (F := versionNegotiationRest A g (sp + 4704#64) vn ∗ F) (by ac_rfl) fun _ hcap hptr => ?_
  rw [vecU8At_expose_one A (sp + 1424#64) cap ptr [] (by simpa using hpos) hcap hptr]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  dsimp only [versionNegotiationRest, List.length_nil, BitVec.ofNat_eq_ofNat]
  have h1432 : (sp + 1424#64) + 8#64 = sp + 1432#64 := by bv_omega
  have h1440 : (sp + 1424#64) + 16#64 = sp + 1440#64 := by bv_omega
  have h4720 : (sp + 4704#64) + 16#64 = sp + 4720#64 := by bv_omega
  have hptr0 : ptr + 0#64 = ptr := by bv_omega
  rw [h1432, h1440, h4720, hptr0]
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at hpc ⊢
  apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 5020#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  refine SepWPp.weaken_pre ?_
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (hinv0.trans hinv))
  have hpack := vecU8At_pack_one A (sp + 1424#64) cap ptr [] 0x0a#8 (by simpa using hpos) hcap hptr
  dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat, List.nil_append] at hpack
  have h01 : (0#64 : BitVec 64) + 1#64 = 1#64 := rfl
  rw [h1432, h1440, hptr0, h01] at hpack; rw [← hpack]
  dsimp only [versionNegotiationRest]; rw [h4720]; exact Entails.of_eq (by ac_rfl)

/-- Step `spqrSendPlacedEntry + 5020#64 .. spqrSendPlacedEntry + 5136#64`: computes
`x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey)` and loads `x25 = vn.direction.signExtend 64`. -/
theorem step_send_vn_authKey_len_31bf8_placed (A : RustAlloc)
    (ext : String → Option (State → State))
    (sp : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (hlen : vn.authKey.length < 2 ^ 64) (halign : sp &&& 15#64 = 0#64)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 5020#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 vn.authKey.length)
    (hinv0 : StepInv s0 s) (hP : P = versionNegotiationRest A g (sp + 4704#64) vn ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = spqrSendPlacedEntry + 5136#64 → s1.status = .Running → s1.sp = sp → s1.trace = s.trace →
      s1.readReg64 .x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey) →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 → s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = vn.direction.signExtend 64 →
      s1.readReg64 .x26 = BitVec.ofNat 64 vn.authKey.length →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .fp = s.readReg64 .fp → StepInv s0 s1 →
      SepWPp (spqrSendPlacedProg ext) ret s1
        (versionNegotiationRest A g (sp + 4704#64) vn ∗ F) Q Qp) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp := by
  subst hP; dsimp only [versionNegotiationRest]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  obtain ⟨hbeqz, hbnez⟩ := EncodedLen.ofNat_length_beq_zero_of_lt hlen
  cases hemp : vn.authKey.isEmpty
  · have hstep := EncodedLen.bv_bytesField_nonempty hemp
    simp only [hemp, Bool.not_false] at hbeqz hbnez
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 5136#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by dsimp only [versionNegotiationRest]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv))
  · simp only [hemp, Bool.not_true] at hbeqz hbnez
    have hzero : bytesFieldEncodedLen vn.authKey = 0 := by unfold bytesFieldEncodedLen; simp [hemp]
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 5136#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by dsimp only [versionNegotiationRest]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hzero, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv))

/-- Step `spqrSendPlacedEntry + 5136#64 .. spqrSendPlacedEntry + 5180#64`: computes
`x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction)` and loads `x24 = vn.minVersion.signExtend 64`. -/
theorem step_send_vn_dir_len_31c6c_placed (A : RustAlloc)
    (ext : String → Option (State → State))
    (sp : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (halign : sp &&& 15#64 = 0#64)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 5136#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hx25 : s.readReg64 .x25 = vn.direction.signExtend 64)
    (hinv0 : StepInv s0 s) (hP : P = versionNegotiationRest A g (sp + 4704#64) vn ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = spqrSendPlacedEntry + 5180#64 → s1.status = .Running → s1.sp = sp → s1.trace = s.trace →
      s1.readReg64 .x8 = s.readReg64 .x8 →
      s1.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction) →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = vn.minVersion.signExtend 64 →
      s1.readReg64 .x25 = vn.direction.signExtend 64 →
      s1.readReg64 .x26 = s.readReg64 .x26 → s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 → s1.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 s1 →
      SepWPp (spqrSendPlacedProg ext) ret s1
        (versionNegotiationRest A g (sp + 4704#64) vn ∗ F) Q Qp) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp := by
  subst hP; dsimp only [versionNegotiationRest]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hw25 : s.readReg32 .x25 = vn.direction := by simp only [State.readReg32, hx25, ProtoRepr.sext64_truncate32]
  by_cases hdir : vn.direction = 0#32
  · have hdir_eq : i32VarintFieldEncodedLen vn.direction = 0 := by simp [i32VarintFieldEncodedLen, hdir]
    have hbeq_d : (vn.direction == 0#32) = true := beq_iff_eq.mpr hdir
    have hbne_d : (vn.direction != 0#32) = false := by simp [hdir]
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 5180#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by dsimp only [versionNegotiationRest]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hdir_eq, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hinv0.trans hinv))
  · have hbeq_d : (vn.direction == 0#32) = false := beq_eq_false_iff_ne.mpr hdir
    have hbne_d : (vn.direction != 0#32) = true := bne_iff_ne.mpr hdir
    have hstep_d := ProtoRepr.bv_i32VarintField_nonzero hdir
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 5180#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by dsimp only [versionNegotiationRest]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hinv0.trans hinv))

/-- Step `spqrSendPlacedEntry + 5180#64 .. spqrSendPlacedEntry + 5220#64`: computes
`x10 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion)`. -/
theorem step_send_vn_minVer_len_31c98_placed
    (ext : String → Option (State → State))
    (vn : VersionNegotiationPB)
    {s0 s : State} {ret : BitVec 64} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 5180#64) (hrun : s.status = .Running)
    (hx24 : s.readReg64 .x24 = vn.minVersion.signExtend 64)
    (hinv0 : StepInv s0 s)
    (hnext : ∀ s1 : State,
      s1.pc = spqrSendPlacedEntry + 5220#64 → s1.status = .Running → s1.sp = s.sp → s1.trace = s.trace →
      s1.readReg64 .x8 = s.readReg64 .x8 → s1.readReg64 .x9 = s.readReg64 .x9 →
      s1.readReg64 .x10 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion) →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = vn.minVersion.signExtend 64 →
      s1.readReg64 .x25 = s.readReg64 .x25 → s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .fp = s.readReg64 .fp → StepInv s0 s1 →
      SepWPp (spqrSendPlacedProg ext) ret s1 P Q Qp) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp := by
  have hw24 : s.readReg32 .x24 = vn.minVersion := by simp only [State.readReg32, hx24, ProtoRepr.sext64_truncate32]
  by_cases hmv : vn.minVersion = 0#32
  · have hmv_eq : i32VarintFieldEncodedLen vn.minVersion = 0 := by simp [i32VarintFieldEncodedLen, hmv]
    have hbeq_m : (vn.minVersion == 0#32) = true := beq_iff_eq.mpr hmv
    have hbne_m : (vn.minVersion != 0#32) = false := by simp [hmv]
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 5220#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hmv_eq, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv)
  · have hbeq_m : (vn.minVersion == 0#32) = false := beq_eq_false_iff_ne.mpr hmv
    have hbne_m : (vn.minVersion != 0#32) = true := bne_iff_ne.mpr hmv
    have hstep_m := ProtoRepr.bv_i32VarintField_nonzero hmv
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 5220#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv)

/-- Step `spqrSendPlacedEntry + 5220#64 .. spqrSendPlacedEntry + 5348#64`: computes
`x0 = BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn)`, sets `x1 = sp + 1424#64` and
`x22 = (optChainParamsTag vn.chainParams).zeroExtend 64`, and steps `bl encode_varint [local#2]` to
`lsmpl.base 148` with `lr = spqrSendPlacedEntry + 5352#64`. -/
theorem step_send_vn_chainParams_len_31cc0_placed (A : RustAlloc)
    (ext : String → Option (State → State))
    (sp : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (halign : sp &&& 15#64 = 0#64)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 5220#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction))
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion))
    (hinv0 : StepInv s0 s)
    (hP : P = versionNegotiationRest A g (sp + 4704#64) vn ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = lsmpl.base 148 → s1.status = .Running → s1.sp = sp → s1.trace = s.trace →
      s1.readReg64 .x0 = BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn) →
      s1.readReg64 .x1 = sp + 1424#64 →
      s1.readReg64 .lr = spqrSendPlacedEntry + 5352#64 →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = (optChainParamsTag vn.chainParams).zeroExtend 64 →
      s1.readReg64 .x23 = s.readReg64 .x23 → s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 → s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .fp = s.readReg64 .fp → StepInv s0 s1 →
      SepWPp (spqrSendPlacedProg ext) ret s1
        (versionNegotiationRest A g (sp + 4704#64) vn ∗ F) Q Qp) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp := by
  subst hP; dsimp only [versionNegotiationRest]
  cases hcp : vn.chainParams with
  | none =>
    dsimp only [optChainParamsPBAt, optChainParamsTag]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have hcomb := bv_versionNegLen_none_combine vn hcp
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *; apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by dsimp only [versionNegotiationRest]; rw [hcp]; dsimp only [optChainParamsPBAt]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [← hcomb]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [hcp]; simp only [optChainParamsTag, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv0.trans hinv))
  | some cp =>
    simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
    have hcomb := bv_versionNegLen_some_combine vn
    by_cases hmj : cp.maxJump = 0#32 <;> by_cases hmo : cp.maxOooKeys = 0#32
    · have hmj_eq : u32VarintFieldEncodedLen cp.maxJump = 0 := by simp [u32VarintFieldEncodedLen, hmj]
      have hmo_eq : u32VarintFieldEncodedLen cp.maxOooKeys = 0 := by simp [u32VarintFieldEncodedLen, hmo]
      have hbeq_mj : (cp.maxJump == 0#32) = true := beq_iff_eq.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = false := by simp [hmj]
      have hbeq_mo : (cp.maxOooKeys == 0#32) = true := beq_iff_eq.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = false := by simp [hmo]
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *; apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
      refine SepWPp.weaken_pre
        (by dsimp only [versionNegotiationRest]; rw [hcp]
            simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.of_eq (by ac_rfl))
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [← hcomb, hcp, ← bv_optChainParams_some_combine]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [hcp]; simp only [optChainParamsTag, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv0.trans hinv))
    · have hmj_eq : u32VarintFieldEncodedLen cp.maxJump = 0 := by simp [u32VarintFieldEncodedLen, hmj]
      have hbeq_mj : (cp.maxJump == 0#32) = true := beq_iff_eq.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = false := by simp [hmj]
      have hbeq_mo : (cp.maxOooKeys == 0#32) = false := beq_eq_false_iff_ne.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = true := bne_iff_ne.mpr hmo
      have hstep_mo := EncodedLen.bv_u32VarintField_nonzero hmo
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *; apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
      refine SepWPp.weaken_pre
        (by dsimp only [versionNegotiationRest]; rw [hcp]
            simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.of_eq (by ac_rfl))
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [← hcomb, hcp, ← bv_optChainParams_some_combine]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [hcp]; simp only [optChainParamsTag, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv0.trans hinv))
    · have hmo_eq : u32VarintFieldEncodedLen cp.maxOooKeys = 0 := by simp [u32VarintFieldEncodedLen, hmo]
      have hbeq_mj : (cp.maxJump == 0#32) = false := beq_eq_false_iff_ne.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = true := bne_iff_ne.mpr hmj
      have hstep_mj := bv_chainParams_maxJump_nonzero hmj
      have hbeq_mo : (cp.maxOooKeys == 0#32) = true := beq_iff_eq.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = false := by simp [hmo]
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *; apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
      refine SepWPp.weaken_pre
        (by dsimp only [versionNegotiationRest]; rw [hcp]
            simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.of_eq (by ac_rfl))
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [← hcomb, hcp, ← bv_optChainParams_some_combine]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [hcp]; simp only [optChainParamsTag, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv0.trans hinv))
    · have hbeq_mj : (cp.maxJump == 0#32) = false := beq_eq_false_iff_ne.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = true := bne_iff_ne.mpr hmj
      have hstep_mj := bv_chainParams_maxJump_nonzero hmj
      have hbeq_mo : (cp.maxOooKeys == 0#32) = false := beq_eq_false_iff_ne.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = true := bne_iff_ne.mpr hmo
      have hstep_mo := EncodedLen.bv_u32VarintField_nonzero hmo
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *; apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
      refine SepWPp.weaken_pre
        (by dsimp only [versionNegotiationRest]; rw [hcp]
            simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.of_eq (by ac_rfl))
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [← hcomb, hcp, ← bv_optChainParams_some_combine]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [hcp]; simp only [optChainParamsTag, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv0.trans hinv))

/-- Step `spqrSendPlacedEntry + 5352#64 .. spqrSendPlacedEntry + 5472#64`: encodes `vn.authKey`
(`Proto.encodeBytesField 1#32 vn.authKey`). -/
theorem step_send_vn_encode_authKey_31d44_placed {resStack : Nat}
    (A : RustAlloc) (ext : String → Option (State → State))
    {s0 s : State}
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 148)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (sp cap ptr v0 : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (bs : List (BitVec 8))
    (hlen : vn.authKey.length < 2 ^ 64)
    (hfit : bs.length + (Proto.encodeBytesField 1#32 vn.authKey).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 5352#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (htr : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = (optChainParamsTag vn.chainParams).zeroExtend 64)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 vn.authKey.length)
    (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (hinv0 : StepInv s0 s)
    (hP : P = (versionNegotiationRest A g (sp + 4704#64) vn ∗
      vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗
      stackAt sp (encodeToVecCalleeStackOf resStack) ∗
      (sp ↦₆₄ v0)) ∗ F)
    (hnext : ∀ (sm : State) (w0 : BitVec 64),
      sm.pc = spqrSendPlacedEntry + 5472#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = (optChainParamsTag vn.chainParams).zeroExtend 64 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x24 = s.readReg64 .x24 →
      sm.readReg64 .x25 = s.readReg64 .x25 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = sp + 4192#64 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((versionNegotiationRest A g (sp + 4704#64) vn ∗
          vecU8At A (sp + 1424#64) cap ptr (bs ++ Proto.encodeBytesField 1#32 vn.authKey) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗
          (sp ↦₆₄ w0)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  obtain ⟨hbeqz, hbnez⟩ := EncodedLen.ofNat_length_beq_zero_of_lt hlen
  cases hemp : vn.authKey.isEmpty
  · simp only [hemp, Bool.not_false] at hbeqz hbnez
    have h1432 : (sp + 1424#64) + 8#64 = sp + 1432#64 := by bv_omega
    have h1440 : (sp + 1424#64) + 16#64 = sp + 1440#64 := by bv_omega
    have h4712 : (sp + 4704#64) + 8#64 = sp + 4712#64 := by bv_omega
    have h4720 : (sp + 4704#64) + 16#64 = sp + 4720#64 := by bv_omega
    have h4192 : (sp + 4096#64) + 96#64 = sp + 4192#64 := by bv_omega
    have hw22 : s.readReg32 .x22 = optChainParamsTag vn.chainParams := by
      simp only [State.readReg32, hx22, EncodedLen.zext64_truncate32]
    have hpos_ak : 0 < vn.authKey.length := List.length_pos_of_ne_nil (List.isEmpty_eq_false_iff.mp hemp)
    have hne_ak : vn.authKey ≠ [] := List.isEmpty_eq_false_iff.mp hemp
    have henc_eq : Proto.encodeBytesField 1#32 vn.authKey =
        [0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 vn.authKey.length) ++ vn.authKey := by
      rw [encodeBytesField_1_eq, hemp]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hfit_all :
        bs.length + 1 + (Proto.encodeVarint (BitVec.ofNat 64 vn.authKey.length)).length +
          vn.authKey.length ≤ cap.toNat := by
      rw [henc_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit; omega
    have hlt_tag : bs.length < cap.toNat := by omega
    refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := versionNegotiationRest A g (sp + 4704#64) vn ∗ A.pool ∗
        stackAt sp (encodeToVecCalleeStackOf resStack) ∗
        (sp ↦₆₄ v0) ∗ F) (by ac_rfl) fun _ hcap hptr => ?_
    refine sepWPp_extract_pure
      (vn.authKey.length ≤ g.authKey.cap.toNat ∧ g.authKey.cap.toNat < 2 ^ 63)
      (fun R' hm => by
        dsimp only [versionNegotiationRest] at hm
        have hm' : s.mem ⊨ EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey ∗
            (((sp + 4704#64 + 8#64) ↦₆₄ g.authKey.ptr) ∗
             ((sp + 4704#64 + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
             optChainParamsPBAt (sp + 4704#64 + 24#64) vn.chainParams ∗
             ((sp + 4704#64 + 36#64) ↦₃₂ vn.direction) ∗
             ((sp + 4704#64 + 40#64) ↦₃₂ vn.minVersion) ∗
             memRegion (sp + 4704#64 + 44#64) 4 ∗
             vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗
             stackAt sp (encodeToVecCalleeStackOf resStack) ∗
             (sp ↦₆₄ v0) ∗ F ∗ R') := by
          convert hm using 1; ac_rfl
        exact EncodedLen.vecU8Buf_bounds hm')
      fun ⟨hak_le, hak_cap⟩ => ?_
    have hcmp_tag := cap_beq_len_false_of_lt hlt_tag hcap
    refine sepWPp_split_pointsTo64 sp v0
      (vecU8At A (sp + 1424#64) cap ptr bs ∗ versionNegotiationRest A g (sp + 4704#64) vn ∗ A.pool ∗
        stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
      (by ac_rfl) fun v0_lo v0_hi => ?_
    rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt_tag hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    dsimp only [versionNegotiationRest]
    rw [h4712, h4720]
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *; apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    have hpack_tag := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x0a#8 hlt_tag hcap hptr
    simp only [arm64_norm, h1432, h1440] at hpack_tag
    refine step_send_encode_varint_call_placed A hvarint
      (BitVec.ofNat 64 vn.authKey.length) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 5412#64) (bs ++ [0x0a#8])
      (by simp only [List.length_append, List.length_singleton]; omega)
      (F := versionNegotiationRest A g (sp + 4704#64) vn ∗ (sp ↦₃₂ v0_lo) ∗
        ((sp + 4#64) ↦₃₂ optChainParamsTag vn.chainParams) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
      (by rw [← hpack_tag]; dsimp only [versionNegotiationRest]; rw [h4712, h4720]; ac_rfl) ?_
    intro s1 hpcs1 hruns1 hsps1 htrs1 hcss1 hinv_s1
    rcases hcss1 with ⟨hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_24, hs1_25, hs1_26, hs1_27, hs1_28, hs1_fp, _⟩
    simp only [arm64_norm, hx26] at hs1_19 hs1_20 hs1_21 hs1_22 hs1_23 hs1_24 hs1_25 hs1_26 hs1_27 hs1_28 hs1_fp
    let bs1 := (bs ++ [0x0a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 vn.authKey.length)
    have hfit_mc : bs1.length + vn.authKey.length ≤ cap.toNat := by
      dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
    have hcmp_mc := elem_len_ult_spare_false_of_le hfit_mc hcap
    rw [vecU8At_expose_slice A (sp + 1424#64) cap ptr bs1 vn.authKey.length hfit_mc hcap hptr hpos_ak, h1432, h1440]
    dsimp only [versionNegotiationRest]; rw [h4712, h4720]
    rw [vecU8Buf_eq_of_nonempty A g.authKey.cap g.authKey.ptr vn.authKey hemp hak_le]
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *; apply SepWPp.of_sepWP_cs (mid := lsρ "memcpy"); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
    have hlen_ak_toNat : (BitVec.ofNat 64 vn.authKey.length).toNat = vn.authKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine step_send_memcpy_call_placed hmemcpy
      (ptr + BitVec.ofNat 64 bs1.length) g.authKey.ptr sp (spqrSendPlacedEntry + 5452#64) vn.authKey
      (F := ((sp + 1424#64) ↦₆₄ cap) ∗ ((sp + 1432#64) ↦₆₄ ptr) ∗
        ((sp + 1440#64) ↦₆₄ BitVec.ofNat 64 bs1.length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs1) ∗
        memRegion (ptr + BitVec.ofNat 64 bs1.length + BitVec.ofNat 64 vn.authKey.length)
          (cap.toNat - bs1.length - vn.authKey.length) ∗
        A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗
        ((sp + 4712#64) ↦₆₄ g.authKey.ptr) ∗ ((sp + 4720#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
        (⌜vn.authKey.length ≤ g.authKey.cap.toNat ∧ g.authKey.cap.toNat < 2 ^ 63 ∧ g.authKey.ptr ≠ 0⌝ ∗
          A.live g.authKey.ptr g.authKey.cap.toNat 1 ∗
          memRegion (g.authKey.ptr + BitVec.ofNat 64 vn.authKey.length)
            (g.authKey.cap.toNat - vn.authKey.length)) ∗
        optChainParamsPBAt (sp + 4704#64 + 24#64) vn.chainParams ∗
        ((sp + 4704#64 + 36#64) ↦₃₂ vn.direction) ∗
        ((sp + 4704#64 + 40#64) ↦₃₂ vn.minVersion) ∗
        memRegion (sp + 4704#64 + 44#64) 4 ∗
        (sp ↦₃₂ v0_lo) ∗ ((sp + 4#64) ↦₃₂ optChainParamsTag vn.chainParams) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hlen_ak_toNat, *]) (hinv_s1.trans hinv2) (by ac_rfl) ?_
    intro s2 hpcs2 hruns2 hsps2 htrs2 hcss2 hinv_s2
    rcases hcss2 with ⟨hs2_19, hs2_20, hs2_21, hs2_22, hs2_23, hs2_24, hs2_25, hs2_26, hs2_27, hs2_28, hs2_fp, _⟩
    simp only [arm64_norm, hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_24, hs1_25, hs1_26, hs1_27, hs1_fp]
      at hs2_19 hs2_20 hs2_21 hs2_22 hs2_23 hs2_24 hs2_25 hs2_26 hs2_27 hs2_28 hs2_fp
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *; apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 5472#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
    have hpack_mc := vecU8At_pack_slice A (sp + 1424#64) cap ptr bs1 vn.authKey hfit_mc hcap hptr hne_ak
    have hbs_eq : bs1 ++ vn.authKey = bs ++ Proto.encodeBytesField 1#32 vn.authKey := by
      dsimp only [bs1]; rw [henc_eq]; simp only [List.append_assoc]
    rw [h1432, h1440, hbs_eq] at hpack_mc
    refine sepWPp_merge_pointsTo32 sp v0_lo (optChainParamsTag vn.chainParams)
      (versionNegotiationRest A g (sp + 4704#64) vn ∗
        vecU8At A (sp + 1424#64) cap ptr (bs ++ Proto.encodeBytesField 1#32 vn.authKey) ∗
        A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
      (by rw [← hpack_mc]; dsimp only [versionNegotiationRest]; rw [h4712, h4720]
          rw [vecU8Buf_eq_of_nonempty A g.authKey.cap g.authKey.ptr vn.authKey hemp hak_le]; ac_rfl)
      fun w0 => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext _ w0
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, h4192, *]) (by simp only [arm64_norm, *]) (hinv_s2.trans hinv3))
  · simp only [hemp, Bool.not_true] at hbeqz hbnez
    have henc_nil : Proto.encodeBytesField 1#32 vn.authKey = [] := by
      rw [encodeBytesField_1_eq, hemp]; simp only [↓reduceIte]
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *; apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 5472#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by rw [henc_nil, List.append_nil]; exact Entails.of_eq (by ac_rfl))
      (hnext _ v0
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv))

/-- Step `spqrSendPlacedEntry + 5472#64 .. spqrSendPlacedEntry + 5524#64`: encodes `vn.direction`
(`Proto.encodeInt32Field 2#32 vn.direction`). -/
theorem step_send_vn_encode_dir_31dbc_placed {resStack : Nat}
    (A : RustAlloc) (ext : String → Option (State → State))
    {s0 s : State}
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 148)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (sp cap ptr : BitVec 64) (vn : VersionNegotiationPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeInt32Field 2#32 vn.direction).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 5472#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = vn.direction.signExtend 64) (hinv0 : StepInv s0 s)
    (hP : P = (vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 5524#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x24 = s.readReg64 .x24 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((vecU8At A (sp + 1424#64) cap ptr (bs ++ Proto.encodeInt32Field 2#32 vn.direction) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  have h1432 : (sp + 1424#64) + 8#64 = sp + 1432#64 := by bv_omega
  have h1440 : (sp + 1424#64) + 16#64 = sp + 1440#64 := by bv_omega
  have hw25 : s.readReg32 .x25 = vn.direction := by simp only [State.readReg32, hx25, ProtoRepr.sext64_truncate32]
  by_cases hdir : vn.direction = 0#32
  · have hbeq_d : (vn.direction == 0#32) = true := beq_iff_eq.mpr hdir
    have hbne_d : (vn.direction != 0#32) = false := by simp [hdir]
    have henc_nil : Proto.encodeInt32Field 2#32 vn.direction = [] := by
      rw [encodeInt32Field_2_eq, hbeq_d]; simp only [↓reduceIte]
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *; apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 5524#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by rw [henc_nil, List.append_nil]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv0.trans hinv))
  · have hbeq_d : (vn.direction == 0#32) = false := beq_eq_false_iff_ne.mpr hdir
    have hbne_d : (vn.direction != 0#32) = true := bne_iff_ne.mpr hdir
    have henc_eq : Proto.encodeInt32Field 2#32 vn.direction =
        [0x10#8] ++ Proto.encodeVarint (vn.direction.signExtend 64) := by
      rw [encodeInt32Field_2_eq, hbeq_d]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hvpos := encodeVarint_length_pos (vn.direction.signExtend 64)
    have hfit' : bs.length + 1 + (Proto.encodeVarint (vn.direction.signExtend 64)).length ≤ cap.toNat := by
      rw [henc_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit; omega
    have hlt : bs.length < cap.toNat := by omega
    refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F) (by ac_rfl)
      fun _ hcap hptr => ?_
    have hcmp := cap_beq_len_false_of_lt hlt hcap
    rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *; apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    have hpack := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x10#8 hlt hcap hptr
    simp only [arm64_norm, h1432, h1440] at hpack
    refine step_send_encode_varint_call_placed A hvarint
      (vn.direction.signExtend 64) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 5524#64) (bs ++ [0x10#8])
      (by simp only [List.length_append, List.length_singleton]; omega) (F := F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
      (by rw [← hpack]) ?_
    intro sm hpcm hrunm hspm htrm hcsm hinv_m
    rcases hcsm with ⟨hm19, hm20, hm21, hm22, hm23, hm24, _, _, hm27, hm28, hmfp, _⟩
    simp only [arm64_norm] at hm19 hm20 hm21 hm22 hm23 hm24 hm27 hm28 hmfp
    refine SepWPp.weaken_pre
      (by rw [henc_eq, ← List.append_assoc]; exact Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm htrm hm19 hm20 hm21 hm22 hm23 hm24 hm27 hm28 hmfp hinv_m)

/-- Step `spqrSendPlacedEntry + 5524#64 .. spqrSendPlacedEntry + 5580#64`: reloads `x25 = v16`
from `[sp + 16#64]` and encodes `vn.minVersion` (`Proto.encodeInt32Field 3#32 vn.minVersion`). -/
theorem step_send_vn_encode_minVer_31df0_placed {resStack : Nat}
    (A : RustAlloc) (ext : String → Option (State → State))
    {s0 s : State}
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 148)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (sp cap ptr v16 : BitVec 64) (vn : VersionNegotiationPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeInt32Field 3#32 vn.minVersion).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 5524#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = vn.minVersion.signExtend 64) (hinv0 : StepInv s0 s)
    (hP : P = (vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗
      stackAt sp (encodeToVecCalleeStackOf resStack) ∗
      ((sp + 16#64) ↦₆₄ v16)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 5580#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = v16 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((vecU8At A (sp + 1424#64) cap ptr (bs ++ Proto.encodeInt32Field 3#32 vn.minVersion) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗
          ((sp + 16#64) ↦₆₄ v16)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  have h1432 : (sp + 1424#64) + 8#64 = sp + 1432#64 := by bv_omega
  have h1440 : (sp + 1424#64) + 16#64 = sp + 1440#64 := by bv_omega
  have hw24 : s.readReg32 .x24 = vn.minVersion := by simp only [State.readReg32, hx24, ProtoRepr.sext64_truncate32]
  by_cases hmv : vn.minVersion = 0#32
  · have hbeq_m : (vn.minVersion == 0#32) = true := beq_iff_eq.mpr hmv
    have hbne_m : (vn.minVersion != 0#32) = false := by simp [hmv]
    have henc_nil : Proto.encodeInt32Field 3#32 vn.minVersion = [] := by
      rw [encodeInt32Field_3_eq, hbeq_m]; simp only [↓reduceIte]
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *; apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 5580#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by rw [henc_nil, List.append_nil]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv0.trans hinv))
  · have hbeq_m : (vn.minVersion == 0#32) = false := beq_eq_false_iff_ne.mpr hmv
    have hbne_m : (vn.minVersion != 0#32) = true := bne_iff_ne.mpr hmv
    have henc_eq : Proto.encodeInt32Field 3#32 vn.minVersion =
        [0x18#8] ++ Proto.encodeVarint (vn.minVersion.signExtend 64) := by
      rw [encodeInt32Field_3_eq, hbeq_m]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hvpos := encodeVarint_length_pos (vn.minVersion.signExtend 64)
    have hfit' : bs.length + 1 + (Proto.encodeVarint (vn.minVersion.signExtend 64)).length ≤ cap.toNat := by
      rw [henc_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit; omega
    have hlt : bs.length < cap.toNat := by omega
    refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ ((sp + 16#64) ↦₆₄ v16) ∗ F) (by ac_rfl)
      fun _ hcap hptr => ?_
    have hcmp := cap_beq_len_false_of_lt hlt hcap
    rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *; apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    have hpack := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x18#8 hlt hcap hptr
    simp only [arm64_norm, h1432, h1440] at hpack
    refine step_send_encode_varint_call_placed A hvarint
      (vn.minVersion.signExtend 64) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 5580#64) (bs ++ [0x18#8])
      (by simp only [List.length_append, List.length_singleton]; omega)
      (F := ((sp + 16#64) ↦₆₄ v16) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
      (by rw [← hpack]; ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm hinv_m
    rcases hcsm with ⟨hm19, hm20, hm21, hm22, hm23, _, hm25, _, hm27, hm28, hmfp, _⟩
    simp only [arm64_norm] at hm19 hm20 hm21 hm22 hm23 hm25 hm27 hm28 hmfp
    refine SepWPp.weaken_pre
      (by rw [henc_eq, ← List.append_assoc]; exact Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm htrm hm19 hm20 hm21 hm22 hm23 hm25 hm27 hm28 hmfp hinv_m)

/-- Step `spqrSendPlacedEntry + 5580#64 .. spqrSendPlacedEntry + 5604#64`: encodes `vn.chainParams`
(`Proto.encodeOptMessage ChainParamsPB.encodeRaw 4#32 vn.chainParams`). -/
theorem step_send_vn_encode_chainParams_31e28_placed {resStack : Nat}
    (A : RustAlloc) (ext : String → Option (State → State))
    {s0 s : State}
    (hcp_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 150)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A)))
    (sp cap ptr : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeOptMessage ChainParamsPB.encodeRaw 4#32 vn.chainParams).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 5580#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = (optChainParamsTag vn.chainParams).zeroExtend 64)
    (hinv0 : StepInv s0 s)
    (hP : P = (versionNegotiationRest A g (sp + 4704#64) vn ∗
      vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 5604#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x25 = s.readReg64 .x25 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((versionNegotiationRest A g (sp + 4704#64) vn ∗
          vecU8At A (sp + 1424#64) cap ptr
            (bs ++ Proto.encodeOptMessage ChainParamsPB.encodeRaw 4#32 vn.chainParams) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP; dsimp only [versionNegotiationRest]
  cases hcp : vn.chainParams with
  | none =>
    rw [hcp] at hx22
    dsimp only [optChainParamsTag, optChainParamsPBAt, Proto.encodeOptMessage] at hx22 ⊢
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *; apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 5604#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by dsimp only [versionNegotiationRest]; rw [hcp]; dsimp only [optChainParamsPBAt, Proto.encodeOptMessage]
          rw [List.append_nil]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv))
  | some cp =>
    rw [hcp] at hx22 hfit
    dsimp only [optChainParamsTag, Proto.encodeOptMessage] at hx22 hfit
    simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *; apply SepWPp.of_sepWP_cs (mid := lsmpl.base 150); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    refine step_send_encode_chainParams_call_placed A hcp_call
      4#32 cp (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 5604#64) bs
      (by decide) (by decide) hfit
      (F := ((sp + 4712#64) ↦₆₄ g.authKey.ptr) ∗ ((sp + 4720#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
        EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey ∗
        ((sp + 4728#64) ↦₃₂ 1#32) ∗ ((sp + 4732#64) ↦₃₂ cp.maxJump) ∗ ((sp + 4736#64) ↦₃₂ cp.maxOooKeys) ∗
        ((sp + 4740#64) ↦₃₂ vn.direction) ∗ ((sp + 4744#64) ↦₃₂ vn.minVersion) ∗
        memRegion (sp + 4748#64) 4 ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1) (by ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm hinv_m
    rcases hcsm with ⟨hm19, hm20, hm21, _, hm23, _, hm25, _, hm27, hm28, hmfp, _⟩
    simp only [arm64_norm] at hm19 hm20 hm21 hm23 hm25 hm27 hm28 hmfp
    refine SepWPp.weaken_pre
      (by dsimp only [versionNegotiationRest]; rw [hcp]
          simp only [optChainParamsPBAt, chainParamsPBAt, Proto.encodeOptMessage,
            BitVec.add_assoc, BitVec.reduceAdd]
          exact Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm htrm hm19 hm20 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)

/-! ## Full Phase 3c Step (`step_send_versionNeg_31be0_placed`) -/

/-- Step `spqrSendPlacedEntry + 4996#64 / spqrSendPlacedEntry + 5604#64 .. spqrSendPlacedEntry + 5604#64`:
encodes `st.versionNegotiation` into
`vecU8At A (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
  (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation)`. -/
theorem step_send_versionNeg_31be0_placed {resStack : Nat}
    (A : RustAlloc) (ext : String → Option (State → State))
    {s0 s : State}
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 148)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (hcp_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 150)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A)))
    (sp ptr v0 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (if st.versionNegotiation.isSome then spqrSendPlacedEntry + 4996#64 else spqrSendPlacedEntry + 5604#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx0 : st.versionNegotiation.isSome → s.readReg64 .x0 = ptr)
    (hx25 : s.readReg64 .x25 = optChainCap g.chain st.chain)
    (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
      vecU8At A (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr [] ∗
      A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain)) ∗ F)
    (hnext : ∀ (sm : State) (w0 : BitVec 64),
      sm.pc = spqrSendPlacedEntry + 5604#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x25 = optChainCap g.chain st.chain →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = sp + 4192#64 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
          vecU8At A (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
            (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗
          (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  cases hvn : st.versionNegotiation with
  | none =>
    rw [hvn] at hpc; simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    refine SepWPp.weaken_pre (by rw [hvn]; exact Entails.refl _)
      (hnext s v0 hpc hrun hsp htr rfl rfl rfl rfl hx25 rfl hx28 rfl hinv0)
  | some vn =>
    rw [hvn] at hpc hx0; simp only [Option.isSome_some, ↓reduceIte] at hpc hx0
    have hx0' := hx0 trivial
    let cap := BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)
    have hcap_toNat : cap.toNat = pqRatchetStatePBEncodedLen st := by
      dsimp only [cap]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hvn_len_le :
        (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 (some vn)).length ≤ cap.toNat := by
      rw [hcap_toNat, ← hvn]; exact optVersionNegotiationPB_encode_len_le st
    rw [encodeOptMessage_versionNeg_some vn] at hvn_len_le
    simp only [List.length_append, List.length_singleton] at hvn_len_le
    have hpos : 0 < cap.toNat := by
      have := encodeVarint_length_pos (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn)); omega
    have hak_lt : vn.authKey.length < 2 ^ 64 := vn_authKey_len_lt_of_state hvn hlen
    let F_rest : SepProp :=
      ((sp + 4704#64) ↦₆₄ g.vn.authKey.cap) ∗
        optChainPBPinnedAt A g.chain (sp + 4704#64 + 48#64) st.chain ∗
        optPqRatchetInnerPBPinnedAt A g.inner (sp + 4704#64 + 128#64) st.inner ∗ F
    refine step_send_vn_push_tag_31be0_placed A ext sp cap ptr g.vn vn hpos halign
      (F := A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗
        (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗ F_rest)
      hpc hrun hsp hx0' hinv0
      (by unfold pqRatchetStatePBPinnedAt
          rw [hvn, optVersionNegotiationPBPinnedAt_eq A g.vn (sp + 4704#64) (some vn)]
          dsimp only [optVersionNegCap, optVersionNegRest, cap, F_rest]; ac_rfl) ?_
    intro s1 hpcs1 hruns1 hsps1 htrs1 hs1_19 hs1_20 hs1_21 hs1_22 hs1_23 hs1_24 hs1_25 hs1_26 hs1_27 hs1_28 hs1_fp hinv1
    refine step_send_vn_authKey_len_31bf8_placed A ext sp g.vn vn hak_lt halign
      (F := vecU8At A (sp + 1424#64) cap ptr [0x0a#8] ∗ A.pool ∗
        stackAt sp (encodeToVecCalleeStackOf resStack) ∗
        (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗ F_rest)
      hpcs1 hruns1 hsps1 hs1_26 hinv1 (by ac_rfl) ?_
    intro s2 hpcs2 hruns2 hsps2 htrs2 hs2_8 hs2_19 hs2_20 hs2_21 hs2_22 hs2_23 hs2_24 hs2_25 hs2_26 hs2_27 hs2_28 hs2_fp hinv2
    refine step_send_vn_dir_len_31c6c_placed A ext sp g.vn vn halign
      (F := vecU8At A (sp + 1424#64) cap ptr [0x0a#8] ∗ A.pool ∗
        stackAt sp (encodeToVecCalleeStackOf resStack) ∗
        (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗ F_rest)
      hpcs2 hruns2 hsps2 hs2_25 hinv2 (by ac_rfl) ?_
    intro s3 hpcs3 hruns3 hsps3 htrs3 hs3_8 hs3_9 hs3_19 hs3_20 hs3_21 hs3_22 hs3_23 hs3_24 hs3_25 hs3_26 hs3_27 hs3_28 hs3_fp hinv3
    refine step_send_vn_minVer_len_31c98_placed ext vn hpcs3 hruns3 hs3_24 hinv3 ?_
    intro s4 hpcs4 hruns4 hsps4 htrs4 hs4_8 hs4_9 hs4_10 hs4_19 hs4_20 hs4_21 hs4_22 hs4_23 hs4_24 hs4_25 hs4_26 hs4_27 hs4_28 hs4_fp hinv4
    have hsps4' : s4.sp = sp := by rw [hsps4, hsps3]
    have hs4_8' : s4.readReg64 .x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey) := by rw [hs4_8, hs3_8, hs2_8]
    have hs4_9' : s4.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction) := by rw [hs4_9, hs3_9]
    refine step_send_vn_chainParams_len_31cc0_placed A ext sp g.vn vn halign
      (F := vecU8At A (sp + 1424#64) cap ptr [0x0a#8] ∗ A.pool ∗
        stackAt sp (encodeToVecCalleeStackOf resStack) ∗
        (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗ F_rest)
      hpcs4 hruns4 hsps4' hs4_8' hs4_9' hs4_10 hinv4 (by ac_rfl) ?_
    intro s5 hpcs5 hruns5 hsps5 htrs5 hs5_0 hs5_1 hs5_lr hs5_19 hs5_20 hs5_21 hs5_22 hs5_23 hs5_24 hs5_25 hs5_26 hs5_27 hs5_28 hs5_fp hinv5
    have htrs5' : s5.trace = s0.trace := by rw [htrs5, htrs4, htrs3, htrs2, htrs1, htr]
    refine step_send_encode_varint_call_placed A hvarint
      (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn)) (sp + 1424#64) cap ptr sp
      (spqrSendPlacedEntry + 5352#64) [0x0a#8]
      (by simp only [List.length_singleton]; omega)
      (F := versionNegotiationRest A g.vn (sp + 4704#64) vn ∗
        (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗ F_rest)
      hpcs5 hruns5 hsps5 halign htrs5' hs5_lr hs5_0 hs5_1 hinv5 (by ac_rfl) ?_
    intro s6 hpcs6 hruns6 hsps6 htrs6 hcsm6 hinv6
    have hs6_19 : s6.readReg64 .x19 = s.readReg64 .x19 := by
      rw [hcsm6.1, hs5_19, hs4_19, hs3_19, hs2_19, hs1_19]
    have hs6_20 : s6.readReg64 .x20 = s.readReg64 .x20 := by
      rw [hcsm6.2.1, hs5_20, hs4_20, hs3_20, hs2_20, hs1_20]
    have hs6_21 : s6.readReg64 .x21 = s.readReg64 .x21 := by
      rw [hcsm6.2.2.1, hs5_21, hs4_21, hs3_21, hs2_21, hs1_21]
    have hs6_22 : s6.readReg64 .x22 = (optChainParamsTag vn.chainParams).zeroExtend 64 := by
      rw [hcsm6.2.2.2.1, hs5_22]
    have hs6_23 : s6.readReg64 .x23 = s.readReg64 .x23 := by
      rw [hcsm6.2.2.2.2.1, hs5_23, hs4_23, hs3_23, hs2_23, hs1_23]
    have hs6_24 : s6.readReg64 .x24 = vn.minVersion.signExtend 64 := by
      rw [hcsm6.2.2.2.2.2.1, hs5_24, hs4_24]
    have hs6_25 : s6.readReg64 .x25 = vn.direction.signExtend 64 := by
      rw [hcsm6.2.2.2.2.2.2.1, hs5_25, hs4_25, hs3_25]
    have hs6_26 : s6.readReg64 .x26 = BitVec.ofNat 64 vn.authKey.length := by
      rw [hcsm6.2.2.2.2.2.2.2.1, hs5_26, hs4_26, hs3_26, hs2_26]
    have hs6_27 : s6.readReg64 .x27 = s.readReg64 .x27 := by
      rw [hcsm6.2.2.2.2.2.2.2.2.1, hs5_27, hs4_27, hs3_27, hs2_27, hs1_27]
    have hs6_28 : s6.readReg64 .x28 = sp + 4192#64 := by
      rw [hcsm6.2.2.2.2.2.2.2.2.2.1, hs5_28, hs4_28, hs3_28, hs2_28, hs1_28, hx28]
    have hs6_fp : s6.readReg64 .fp = s.readReg64 .fp := by
      rw [hcsm6.2.2.2.2.2.2.2.2.2.2.1, hs5_fp, hs4_fp, hs3_fp, hs2_fp, hs1_fp]
    refine step_send_vn_encode_authKey_31d44_placed A ext hvarint hmemcpy
      sp cap ptr v0 g.vn vn
      ([0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn)))
      hak_lt (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗ F_rest)
      hpcs6 hruns6 hsps6 htrs6 hs6_22 hs6_26 hs6_28 hinv6 (by ac_rfl) ?_
    intro s7 w0 hpcs7 hruns7 hsps7 htrs7 hs7_19 hs7_20 hs7_21 hs7_22 hs7_23 hs7_24 hs7_25 hs7_27 hs7_28 hs7_fp hinv7
    rw [hs6_19] at hs7_19; rw [hs6_20] at hs7_20; rw [hs6_21] at hs7_21
    rw [hs6_23] at hs7_23; rw [hs6_24] at hs7_24; rw [hs6_25] at hs7_25
    rw [hs6_27] at hs7_27; rw [hs6_fp] at hs7_fp
    refine step_send_vn_encode_dir_31dbc_placed A ext hvarint sp cap ptr vn
      (([0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn))) ++
        Proto.encodeBytesField 1#32 vn.authKey)
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := versionNegotiationRest A g.vn (sp + 4704#64) vn ∗ (sp ↦₆₄ w0) ∗
        ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗ F_rest)
      hpcs7 hruns7 hsps7 htrs7 hs7_25 hinv7 (by ac_rfl) ?_
    intro s8 hpcs8 hruns8 hsps8 htrs8 hs8_19 hs8_20 hs8_21 hs8_22 hs8_23 hs8_24 hs8_27 hs8_28 hs8_fp hinv8
    rw [hs7_19] at hs8_19; rw [hs7_20] at hs8_20; rw [hs7_21] at hs8_21; rw [hs7_22] at hs8_22
    rw [hs7_23] at hs8_23; rw [hs7_24] at hs8_24; rw [hs7_27] at hs8_27
    rw [hs7_28] at hs8_28; rw [hs7_fp] at hs8_fp
    refine step_send_vn_encode_minVer_31df0_placed A ext hvarint sp cap ptr (optChainCap g.chain st.chain) vn
      ((([0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn))) ++
        Proto.encodeBytesField 1#32 vn.authKey) ++ Proto.encodeInt32Field 2#32 vn.direction)
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := versionNegotiationRest A g.vn (sp + 4704#64) vn ∗ (sp ↦₆₄ w0) ∗ F_rest)
      hpcs8 hruns8 hsps8 htrs8 hs8_24 hinv8 (by ac_rfl) ?_
    intro s9 hpcs9 hruns9 hsps9 htrs9 hs9_19 hs9_20 hs9_21 hs9_22 hs9_23 hs9_25 hs9_27 hs9_28 hs9_fp hinv9
    rw [hs8_19] at hs9_19; rw [hs8_20] at hs9_20; rw [hs8_21] at hs9_21; rw [hs8_22] at hs9_22
    rw [hs8_23] at hs9_23; rw [hs8_27] at hs9_27; rw [hs8_28] at hs9_28; rw [hs8_fp] at hs9_fp
    refine step_send_vn_encode_chainParams_31e28_placed A ext hcp_call sp cap ptr g.vn vn
      (((([0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn))) ++
        Proto.encodeBytesField 1#32 vn.authKey) ++
        Proto.encodeInt32Field 2#32 vn.direction) ++ Proto.encodeInt32Field 3#32 vn.minVersion)
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗ F_rest)
      hpcs9 hruns9 hsps9 htrs9 hs9_22 hinv9 (by ac_rfl) ?_
    intro s10 hpcs10 hruns10 hsps10 htrs10 hs10_19 hs10_20 hs10_21 hs10_23 hs10_25 hs10_27 hs10_28 hs10_fp hinv10
    rw [hs9_19] at hs10_19; rw [hs9_20] at hs10_20; rw [hs9_21] at hs10_21; rw [hs9_23] at hs10_23
    rw [hs9_25] at hs10_25; rw [hs9_27] at hs10_27; rw [hs9_28] at hs10_28; rw [hs9_fp] at hs10_fp
    refine SepWPp.weaken_pre ?_
      (hnext s10 w0 hpcs10 hruns10 hsps10 htrs10 hs10_19 hs10_20 hs10_21 hs10_23 hs10_25 hs10_27 hs10_28 hs10_fp hinv10)
    unfold pqRatchetStatePBPinnedAt
    rw [hvn, optVersionNegotiationPBPinnedAt_eq A g.vn (sp + 4704#64) (some vn), encodeOptMessage_versionNeg_some vn]
    dsimp only [optVersionNegCap, optVersionNegRest, cap, F_rest]
    simp only [List.append_assoc]
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Top.Send
