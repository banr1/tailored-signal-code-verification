/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesInnerHeader
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.EncodedLenCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.DefsPlaced
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhasePlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateHeader
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MessageEncodeCodeSym
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLen
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1State
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncode
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncodePlaced
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Relocatable `spqr::send::<HookRng>` Phase 3e Header (Block 124)

Verifies the `[LibsignalPlacement]` Phase 3e header steps (`+6140..+6216`, `+6592..+6616`)
for encoding `Option<pq_ratchet_state::Inner>` and `Option<v1_state::InnerState>` up to
the jump-table dispatch at `+6616` (`StepSendInnerStateAt6616Placed`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.Poly.NextChunk (AllocContractsPlaced)
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Auth (authEncodeLocal1Name authEncodePinnedSpecOf)
open CryptoVerification.SpqrV1.Prost.MessageEncode
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Top.Send.Placed

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable [LibsignalPlacement]

/-! ## Unpacked `.rodata` Jump Table at `lsρ spqrSendRoSym + 22#64` -/

theorem spqrSendEncodeJumpTablePlacedAt_eq_bytes :
    spqrSendEncodeJumpTablePlacedAt =
      spqrSendEncodeJumpTableBytesAt (lsρ spqrSendRoSym + 22#64) :=
  spqrSendEncodeJumpTableBytes_eq (lsρ spqrSendRoSym + 22#64)

/-! ## `[local#1]` Callee `subroutine_ok` Bridges -/

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero spqrSendPlacedEntry
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  Prost.EncodeToVec.noneCap2_add_two_beq_zero Prost.EncodeToVec.noneCap2_add_two_bne_zero
  ProtoRepr.noneCap_add_two_beq_zero ProtoRepr.noneCap_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

/-- Transfer a plain block `j` `subroutine_ok` into `withStepInv s0 spec` on `spqrSendPlacedProg ext` (Block `124`). -/
theorem spqrSend_subroutine_ok_placed_of_plain {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee_prog : IsLsBlockProg calleeProg j H]
    {spec : Spec α} {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hcallee : subroutine_ok calleeProg (lsmpl.base j) spec)
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok ((blkPC_124).rebase (blkPl_124).base H) (lsmpl.base j)
      (withStepInv s0 spec) :=
  subroutine_ok_withStepInv_lscl hcl0
    (ls_subroutine_ok_of_block (subroutine_ok_withLsCodeLoaded_of_plain hcallee) (by decide) hj hj_unmut)

/-- Transfer a `withLsCodeLoaded lsmpl spec` block `j` `subroutine_ok` into `withStepInv s0 spec` on `spqrSendPlacedProg ext` (Block `124`). -/
theorem spqrSend_subroutine_ok_placed_of_lscl {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee_prog : IsLsBlockProg calleeProg j H]
    {spec : Spec α} {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hcallee : subroutine_ok calleeProg (lsmpl.base j) (withLsCodeLoaded lsmpl spec))
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok ((blkPC_124).rebase (blkPl_124).base H) (lsmpl.base j)
      (withStepInv s0 spec) :=
  subroutine_ok_withStepInv_lscl hcl0
    (ls_subroutine_ok_of_block hcallee (by decide) hj hj_unmut)

theorem spqrSend_etvMemcpy_ok_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec := by
  have h0 : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") (sessionMemcpySpec 0) :=
    ls_hook_ok_of_mem (hA.session_memcpy 0)
  refine subroutine_ok_mono h0 ?_ ?_
  · intro ⟨dst, src, srcBytes⟩ R s hm
    dsimp only [etvMemcpyRegionSpec, sessionMemcpyRegionSpec, memcpyRegionSpec, sessionMemcpySpec, libcMemcpySpec, stackAt] at hm ⊢
    rw [ProofLib.memRegion_zero]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro ⟨dst, src, srcBytes⟩ R s0 sf hm
    dsimp only [etvMemcpyRegionSpec, sessionMemcpyRegionSpec, sessionMemcpySpec, stackAt] at hm ⊢
    rw [ProofLib.memRegion_zero] at hm
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm

theorem spqrSend_chainEncodedLen1_ok_placed (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 178)
      (withStepInv s0 (chainEncodedLenPinnedSpec A)) :=
  spqrSend_subroutine_ok_placed_of_lscl hcl0 (chainEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem spqrSend_v1StateEncodedLen1_ok_placed (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 177)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A (lsρ v1StateJtSymLocal1))) :=
  spqrSend_subroutine_ok_placed_of_lscl hcl0 (v1StateEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem spqrSend_epochEncodedLen1_ok_placed {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 171)
      (withStepInv s0 (epochEncLenStackSpecOf resStack A)) := by
  have hep : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 171) (withLsCodeLoaded lsmpl (epochEncodedLenPinnedSpec A)) :=
    ls_subroutine_ok_of_block
      (subroutine_ok_withLsCodeLoaded_of_plain (epochEncodedLen_local1_pinned_placed_ok_ext A ext))
      (by decide) (by decide) (by decide)
  apply subroutine_ok_withStepInv_lscl hcl0
  refine subroutine_ok_outcome_intro fun ⟨a, g, ep⟩ R s hpc hrun hpre hal => ?_
  obtain ⟨hcl_s, hpre⟩ := extract_withLsCodeLoaded hpre
  dsimp only [epochEncLenStackSpecOf] at hpre
  rw [stackAt_callee_eq_unchunkedEncodedLen hres s.sp] at hpre
  let F_rem := memRegion (s.sp - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (160 + resStack)
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hfit⟩, hm⟩
  have hpre' : s.mem ⊨ (withLsCodeLoaded lsmpl (epochEncodedLenPinnedSpec A)).pre ⟨a, g, ep⟩ s ∗ (F_rem ∗ R) := by
    dsimp only [withLsCodeLoaded, epochEncodedLenPinnedSpec, EpochEncodedLenFits]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl_s, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem, epochEncodedLenStack, unchunkedEncodedLenStack]; ac_rfl)) hm
  refine hep.mono_outcome ⟨a, g, ep⟩ (F_rem ∗ R) s hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, epochEncodedLenPinnedSpec, epochEncLenStackSpecOf] at hpost ⊢
    rw [stackAt_callee_eq_unchunkedEncodedLen hres s.sp]
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem, epochEncodedLenStack, unchunkedEncodedLenStack]; ac_rfl)) hpost
  · exact (ProofLib.allowPanic_not_exited hpan).elim
  · exact (ProofLib.allowPanic_not_exited hex).elim
  · exact (ProofLib.allowPanic_not_exited hoom).elim

/-! ## Call Wrappers for `V1State` Encoding -/

theorem step_send_v1State_encLen_call_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State))
    {roV1 call_pc : BitVec 64} {s0 s : State}
    (hv1Len : subroutine_ok (spqrSendPlacedProg ext) call_pc
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A roV1)))
    (v1A sp ret_pc : BitVec 64) (g : V1StatePBGhost) (v1 : V1State)
    (hfit : v1StatePBEncodedLen v1 < 2 ^ 64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = v1A) (hinv0 : StepInv s0 s)
    (hP : P = (v1StatePBPinnedAt A g v1A v1 ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen v1) →
      CalleeSavedPreserved s sm → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((v1StatePBPinnedAt A g v1A v1 ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (v1StatePBPinnedAt A g v1A v1 ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_v1State_encLen_call_placed hres A hv1Len v1A (sp + 144#64) ret_pc
    g v1 hfit hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hx0 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hx0m hcsm hinvm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hx0m hcsm hinvm)

theorem step_send_leaf_encLen16_call_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {G M : Type} (ext : String → Option (State → State))
    (reprAt : G → BitVec 64 → M → SepProp) (encLen : M → Nat)
    {call_pc : BitVec 64} {s0 s : State}
    (hcallee : subroutine_ok (spqrSendPlacedProg ext) call_pc
      (withStepInv s0 (leafEncLen16Spec reprAt encLen)))
    (msgA sp ret_pc : BitVec 64) (g : G) (m : M) (hfit : encLen m < 2 ^ 64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = msgA) (hinv0 : StepInv s0 s)
    (hP : P = (reprAt g msgA m ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (encLen m) →
      CalleeSavedPreserved s sm → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((reprAt g msgA m ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (reprAt g msgA m ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_leaf_encLen16_call_placed hres reprAt encLen hcallee msgA (sp + 144#64) ret_pc
    g m hfit hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hx0 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hx0m hcsm hinvm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hx0m hcsm hinvm)

theorem step_send_chunked_encLen48_call_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {G M : Type} (ext : String → Option (State → State))
    (reprAt : G → BitVec 64 → M → SepProp) (encLen : M → Nat)
    {call_pc : BitVec 64} {s0 s : State}
    (hcallee : subroutine_ok (spqrSendPlacedProg ext) call_pc
      (withStepInv s0 (leafEncLen48Spec reprAt encLen)))
    (msgA sp ret_pc : BitVec 64) (g : G) (m : M) (hfit : encLen m < 2 ^ 64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = msgA) (hinv0 : StepInv s0 s)
    (hP : P = (reprAt g msgA m ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (encLen m) →
      CalleeSavedPreserved s sm → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((reprAt g msgA m ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (reprAt g msgA m ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_chunked_encLen48_call_placed hres reprAt encLen hcallee msgA (sp + 144#64) ret_pc
    g m hfit hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hx0 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hx0m hcsm hinvm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hx0m hcsm hinvm)

theorem step_send_encode_auth_call_placed {resStack : Nat}
    (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hauth : subroutine_ok (spqrSendPlacedProg ext) call_pc
      (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (authA v cap ptr sp ret_pc : BitVec 64)
    (g : AuthenticatorPBGhost) (auth : AuthenticatorPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth).length ≤ cap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = authA)
    (hx1 : s.readReg64 .x1 = v) (hinv0 : StepInv s0 s)
    (hP : P = (authenticatorPBPinnedAt A g authA auth ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((authenticatorPBPinnedAt A g authA auth ∗
          vecU8At A v cap ptr (bs ++ Proto.encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (authenticatorPBPinnedAt A g authA auth ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_encode_auth_call_prog A hauth authA v cap ptr (sp + 144#64) ret_pc g auth bs
    hfit hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hx0 hx1 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hcsm hinvm)

theorem step_send_encode_polyEncoder_call_placed {resStack : Nat}
    (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hpe : subroutine_ok (spqrSendPlacedProg ext) call_pc
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (encA v cap ptr sp ret_pc : BitVec 64)
    (g : PolynomialEncoderPBGhost) (enc : PolynomialEncoder) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = encA)
    (hx1 : s.readReg64 .x1 = v) (hinv0 : StepInv s0 s)
    (hP : P = (ProtoRepr.polynomialEncoderPBPinnedAt A g encA enc ∗
      vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((ProtoRepr.polynomialEncoderPBPinnedAt A g encA enc ∗
          vecU8At A v cap ptr (bs ++ Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 enc) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (ProtoRepr.polynomialEncoderPBPinnedAt A g encA enc ∗
      vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_encode_polyEncoder_call_placed A hpe encA v cap ptr (sp + 144#64) ret_pc g enc bs
    hfit hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hx0 hx1 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hcsm hinvm)

theorem step_send_encode_polyDecoder_call_placed {resStack : Nat}
    (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hpd : subroutine_ok (spqrSendPlacedProg ext) call_pc
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (tag : BitVec 32) (decA v cap ptr sp ret_pc : BitVec 64)
    (g : PolynomialDecoderPBGhost) (dec : PolynomialDecoder) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw tag dec).length ≤ cap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hw0 : s.readReg32 .x0 = tag)
    (hx1 : s.readReg64 .x1 = decA) (hx2 : s.readReg64 .x2 = v) (hinv0 : StepInv s0 s)
    (hP : P = (ProtoRepr.polynomialDecoderPBPinnedAt A g decA dec ∗
      vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((ProtoRepr.polynomialDecoderPBPinnedAt A g decA dec ∗
          vecU8At A v cap ptr (bs ++ Proto.encodeMessage PolynomialDecoder.encodeRaw tag dec) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (ProtoRepr.polynomialDecoderPBPinnedAt A g decA dec ∗
      vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_encode_polyDecoder_call_placed A hpd tag decA v cap ptr (sp + 144#64) ret_pc g dec bs
    hfit hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hw0 hx1 hx2 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hcsm hinvm)

theorem step_send_encode_ekSentCt1Received_call_placed {resStack : Nat}
    (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hek : subroutine_ok (spqrSendPlacedProg ext) call_pc
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf resStack A)))
    (msgA v cap ptr sp ret_pc : BitVec 64)
    (g : Unchunked4PBGhost) (m : V1State.Unchunked.EkSentCt1Received) (bs : List (BitVec 8))
    (hfit : bs.length +
      (Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m).length ≤ cap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = msgA)
    (hx1 : s.readReg64 .x1 = v) (hinv0 : StepInv s0 s)
    (hP : P = (ekSentCt1ReceivedPBPinnedAt A g msgA m ∗
      vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((ekSentCt1ReceivedPBPinnedAt A g msgA m ∗
          vecU8At A v cap ptr
            (bs ++ Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (ekSentCt1ReceivedPBPinnedAt A g msgA m ∗
      vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_encode_ekSentCt1Received_call_placed A hek msgA v cap ptr (sp + 144#64) ret_pc g m bs
    hfit hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hx0 hx1 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hcsm hinvm)

theorem step_send_encode_ct1Sent_call_placed {resStack : Nat}
    (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hct1 : subroutine_ok (spqrSendPlacedProg ext) call_pc
      (withStepInv s0 (etvCt1SentEncodeSpecOf resStack A)))
    (msgA v cap ptr sp ret_pc : BitVec 64)
    (g : Unchunked5PBGhost) (m : V1State.Unchunked.Ct1Sent) (bs : List (BitVec 8))
    (hfit : bs.length +
      (Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m).length ≤ cap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = msgA)
    (hx1 : s.readReg64 .x1 = v) (hinv0 : StepInv s0 s)
    (hP : P = (ct1SentPBPinnedAt A g msgA m ∗
      vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((ct1SentPBPinnedAt A g msgA m ∗
          vecU8At A v cap ptr
            (bs ++ Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (ct1SentPBPinnedAt A g msgA m ∗
      vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_encode_ct1Sent_call_placed A hct1 msgA v cap ptr (sp + 144#64) ret_pc g m bs
    hfit hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hx0 hx1 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hcsm hinvm)

/-! ## `V1State` Length Computation (`+4844..+4920`) -/

/-- `spqrSendPlacedEntry + 4844#64 -> spqrSendPlacedEntry + 4920#64` parameterized over `roV1`. -/
theorem step_send_inner_len_31b48_ro_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State))
    {roV1 : BitVec 64} {s0 s2 : State}
    (hV1StateLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 177)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A roV1)))
    (sp : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s2.pc = spqrSendPlacedEntry + 4844#64) (hrun : s2.status = .Running)
    (hsp : s2.sp = sp) (htr : s2.trace = s0.trace)
    (hx22 : s2.readReg64 .x22 =
      BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
        optChainPBFieldEncodedLen st.chain))
    (hx24 : s2.readReg64 .x24 = sp + 4704#64) (hinv2 : StepInv s0 s2)
    (hP : P = (pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ s3 : State,
      s3.pc = spqrSendPlacedEntry + 4920#64 → s3.status = .Running → s3.sp = sp → s3.trace = s0.trace →
      s3.readReg64 .x19 = s2.readReg64 .x19 →
      s3.readReg64 .x20 = optPqRatchetInnerCap g.inner st.inner →
      s3.readReg64 .x21 = s2.readReg64 .x21 → s3.readReg64 .x22 = s2.readReg64 .x22 →
      s3.readReg64 .x23 = s2.readReg64 .x23 →
      s3.readReg64 .x24 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st) →
      s3.readReg64 .x25 = s2.readReg64 .x25 → s3.readReg64 .x26 = s2.readReg64 .x26 →
      s3.readReg64 .x27 = s2.readReg64 .x27 → s3.readReg64 .x28 = s2.readReg64 .x28 →
      s3.readReg64 .fp = s2.readReg64 .fp → StepInv s0 s3 →
      SepWPp (spqrSendPlacedProg ext) ret s3
        ((pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s2 P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_pure
    ((optPqRatchetInnerCap g.inner st.inner + 3#64 == 0#64) = !st.inner.isSome ∧
     (optPqRatchetInnerCap g.inner st.inner + 3#64 != 0#64) = st.inner.isSome)
    (fun R' hm => ?_) (fun hin_cap => ?_)
  · apply optPqRatchetInnerPBPinnedAt_cap_bounds (A := A) (p := (sp + 4704#64) + 0x80#64)
      (R := optVersionNegotiationPBPinnedAt A g.vn (sp + 4704#64) st.versionNegotiation ∗
        optChainPBPinnedAt A g.chain ((sp + 4704#64) + 0x30#64) st.chain ∗
        (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
        stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
    rw [pqRatchetStatePBPinnedAt] at hm
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · rw [pqRatchetStatePBPinnedAt, optPqRatchetInnerPBPinnedAt_eq]
    cases hin : st.inner with
    | none =>
      rw [hin] at hin_cap
      simp only [Option.isSome_none, Bool.not_false] at hin_cap
      have ⟨hadd1, hadd2⟩ := EncodedLen.adds_no_overflow_of_eq (a := 0)
        (b := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
          optChainPBFieldEncodedLen st.chain)
        (c := pqRatchetStatePBEncodedLen st)
        (by unfold pqRatchetStatePBEncodedLen; rw [hin]; dsimp [optPqRatchetInnerPBFieldEncodedLen])
        (by omega)
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply SepWPp.of_sepWP_cs (mid := (blkPl_124).base + 4920#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
      refine SepWPp.weaken_pre ?_
        (hnext _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by rw [hin]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv2.trans hinv))
      rw [pqRatchetStatePBPinnedAt, optPqRatchetInnerPBPinnedAt_eq, hin]
      exact Entails.of_eq (by ac_rfl)
    | some innerVal =>
      cases innerVal with
      | v1 v1s =>
        rw [hin] at hin_cap
        simp only [Option.isSome_some, Bool.not_true] at hin_cap
        have ⟨hfit, hopt_lt, hvar_lt⟩ := v1StatePBEncodedLen_lt_of_state hin hlen
        have hls := EncodedLen.cmp_ls_false_of_lt hvar_lt hopt_lt
        have hopt_in := bv_optInner_some_eq v1s
        have ⟨hadd1, hadd2⟩ := EncodedLen.adds_no_overflow_of_eq
          (a := optPqRatchetInnerPBFieldEncodedLen (some (.v1 v1s)))
          (b := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
            optChainPBFieldEncodedLen st.chain)
          (c := pqRatchetStatePBEncodedLen st)
          (by unfold pqRatchetStatePBEncodedLen; rw [hin])
          (by omega)
        dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
        apply SepWPp.of_sepWP_cs (mid := lsmpl.base 177)
        wp_steps
        apply SepWP.done
          (by simp only [arm64_norm, blkPl_124_ρ, ls_resolve_blk_177, *])
          (by simp only [arm64_norm, *]); intro hinv_bl
        have hres176 : resStack + 176 < 2 ^ 64 := by omega
        refine SepWPp.call_cs (x := PinnedEncLenGhost.mk ((sp + 4704#64) + 0x80#64) g.inner v1s)
          (F := optVersionNegotiationPBPinnedAt A g.vn (sp + 4704#64) st.versionNegotiation ∗
            optChainPBPinnedAt A g.chain ((sp + 4704#64) + 0x30#64) st.chain ∗
            memRegion (sp - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (96 + resStack) ∗ F)
          hV1StateLen
          (by simp only [arm64_norm, blkPl_124_ρ, ls_resolve_blk_177])
          (by simp only [arm64_norm, *])
          (by simp only [State.spAligned, arm64_norm, hsp, beq_iff_eq]; exact halign)
          (ret_pc := (blkPl_124).base + 4872#64) (by simp only [arm64_norm]) ?_ ?_ ?_ ?_
        · intro R' hm
          rw [← optPqRatchetInnerPBPinnedAt_eq A g.inner ((sp + 4704#64) + 0x80#64) (some (.v1 v1s)),
            optPqRatchetInnerPBPinnedAt,
            stackAt_callee_eq_v1StateEncodedLen hres176 sp] at hm
          simp only [arm64_norm] at hm
          simp only [withStepInv, v1StateEncodedLenRoPinnedSpec, arm64_norm, hsp, hx24,
            sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hinv2.trans hinv_bl, hfit⟩, ?_⟩
          exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
        · intro sf code R' _ hm; exact ProofLib.allowPanic_not_exited hm
        · intro sf _ hm
          simp only [withStepInv, v1StateEncodedLenRoPinnedSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
          exact hm.1.elim
        · intro sm hpcm hrunm hspm hcsm hinv_call
          simp only [arm64_norm, hsp] at hspm
          dsimp only [withStepInv, v1StateEncodedLenRoPinnedSpec]
          rw [sepConj_assoc]
          refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
          simp only [arm64_norm, htr] at htrm
          rcases hcsm with ⟨hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx25m, hx26m, hx27m, hx28m, hfpm, _⟩
          simp only [arm64_norm, hx22, hx24] at hx19m hx20m hx21m hx22m hx23m hx24m hx25m hx26m hx27m hx28m hfpm
          apply SepWPp.of_sepWP_cs (mid := (blkPl_124).base + 4920#64); wp_steps
          apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_post
          refine SepWPp.weaken_pre ?_
            (hnext _
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by rw [hin]; simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *])
              (((hinv2.trans hinv_bl).trans hinv_call).trans hinv_post))
          rw [pqRatchetStatePBPinnedAt, hin, optPqRatchetInnerPBPinnedAt,
            stackAt_callee_eq_v1StateEncodedLen hres176 sp]
          simp only [arm64_norm, hsp]
          exact Entails.of_eq (by ac_rfl)

/-! ## Header Steps (`+6140..+6216` and `+6592..+6616`) -/

/-- Step `spqrSendPlacedEntry + 6140#64 .. spqrSendPlacedEntry + 6216#64` when `st.inner = none`
(`x20 = noneCap3`). -/
theorem step_send_inner_none_32058_placed
    (ext : String → Option (State → State))
    {s0 s : State} (sp : BitVec 64)
    {R : SepProp} {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 6140#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = noneCap3) (hinv0 : StepInv s0 s)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm P
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply SepWPp.of_sepWP_cs (mid := (blkPl_124).base + 6216#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (hinv0.trans hinv)

/-- Step `spqrSendPlacedEntry + 6140#64 .. spqrSendPlacedEntry + 6208#64` when `st.inner = some (.v1 v1)`:
writes outer tag `0x1a#8`, calls `V1State::encoded_len [local#1]` (Block `177`), and calls
`encode_varint` (Block `148`). -/
theorem step_send_inner_some_hdr_32058_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State))
    {roV1 : BitVec 64} {s0 s : State}
    (hv1Len : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 177)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A roV1)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 148)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (sp cap ptr : BitVec 64) (g : V1StatePBGhost) (v1 : V1State) (bs : List (BitVec 8))
    (hv1_len : v1StatePBEncodedLen v1 < 2 ^ 64)
    (hfit : bs.length + 1 +
      (Proto.encodeVarint (BitVec.ofNat 64 (v1StatePBEncodedLen v1))).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 6140#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = optPqRatchetInnerCap g (some (.v1 v1))) (hinv0 : StepInv s0 s)
    (hP : P = (v1StatePBPinnedAt A g (sp + 4832#64) v1 ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6208#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = optPqRatchetInnerCap g (some (.v1 v1)) →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x25 = s.readReg64 .x25 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((v1StatePBPinnedAt A g (sp + 4832#64) v1 ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          vecU8At A (sp + 1424#64) cap ptr
            ((bs ++ [0x1a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StatePBEncodedLen v1))) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_pure
    ((optPqRatchetInnerCap g (some (.v1 v1)) + 3#64 == 0#64) = false ∧
      (optPqRatchetInnerCap g (some (.v1 v1)) + 3#64 != 0#64) = true)
    (fun R' hm => by
      have hm' : s.mem ⊨ optPqRatchetInnerPBPinnedAt A g (sp + 4832#64) (some (.v1 v1)) ∗
          ((roV1 ↦ᵣ v1StateJumpTableBytes) ∗
           vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗
           stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R') := by
        dsimp only [optPqRatchetInnerPBPinnedAt]; convert hm using 1; ac_rfl
      exact optPqRatchetInnerPBPinnedAt_cap_bounds hm')
    fun ⟨hw_beq3, hw_bne3⟩ => ?_
  have hlt1 : bs.length < cap.toNat := by omega
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := v1StatePBPinnedAt A g (sp + 4832#64) v1 ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗ A.pool ∗
      stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by ac_rfl) fun _ hcap hptr => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt1 hcap hptr]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  have h1432 : (sp + 1424#64) + 8#64 = sp + 1432#64 := by bv_omega
  have h1440 : (sp + 1424#64) + 16#64 = sp + 1440#64 := by bv_omega
  rw [h1432, h1440]
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply SepWPp.of_sepWP_cs (mid := lsmpl.base 177); wp_steps
  apply SepWP.done
    (by simp only [arm64_norm, blkPl_124_ρ, ls_resolve_blk_177, *])
    (by simp only [arm64_norm, *]); intro hinv1
  have hpack := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x1a#8 hlt1 hcap hptr
  simp only [arm64_norm, h1432, h1440] at hpack
  refine step_send_v1State_encLen_call_placed hres A ext hv1Len
    (sp + 4832#64) sp ((blkPl_124).base + 6200#64) g v1 hv1_len
    (F := vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x1a#8]) ∗ A.pool ∗ F)
    (by simp only [arm64_norm, blkPl_124_ρ, ls_resolve_blk_177])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by rw [← hpack]; ac_rfl) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1
  rcases hcsm1 with ⟨hm19, hm20, hm21, _, hm23, _, hm25, _, hm27, hm28, hmfp, _⟩
  simp only [arm64_norm, hx20] at hm19 hm20 hm21 hm23 hm25 hm27 hm28 hmfp
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps
  apply SepWP.done
    (by simp only [arm64_norm, blkPl_124_ρ, ls_resolve_blk_148, *])
    (by simp only [arm64_norm, *]); intro hinv2
  refine step_send_encode_varint_call_placed A hvarint
    (BitVec.ofNat 64 (v1StatePBEncodedLen v1)) (sp + 1424#64) cap ptr sp ((blkPl_124).base + 6208#64)
    (bs ++ [0x1a#8]) (by simpa only [List.length_append, List.length_singleton] using hfit)
    (F := v1StatePBPinnedAt A g (sp + 4832#64) v1 ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗ F)
    (by simp only [arm64_norm, blkPl_124_ρ, ls_resolve_blk_148])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hinv_m1.trans hinv2) (by ac_rfl) ?_
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hcsm2 hinv_m2
  rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, _, hm2_23, _, hm2_25, _, hm2_27, hm2_28, hm2_fp, _⟩
  simp only [arm64_norm, hm19, hm20, hm21, hm23, hm25, hm27, hm28, hmfp]
    at hm2_19 hm2_20 hm2_21 hm2_23 hm2_25 hm2_27 hm2_28 hm2_fp
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext sm2 hpcm2 hrunm2 hspm2 htrm2 hm2_19 hm2_20 hm2_21 hm2_23 hm2_25 hm2_27 hm2_28 hm2_fp hinv_m2)

/-- Step `spqrSendPlacedEntry + 6208#64 .. spqrSendPlacedEntry + 6216#64` when `v1.innerState = none`
(`x20 = noneCap2`). -/
theorem step_send_inner_v1_none_32094_placed
    (A : RustAlloc) (ext : String → Option (State → State))
    {s0 s : State} (sp cap ptr : BitVec 64) (bs : List (BitVec 8))
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 6208#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = noneCap2) (hinv0 : StepInv s0 s)
    (hP : P = vecU8At A (sp + 1424#64) cap ptr bs ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        (vecU8At A (sp + 1424#64) cap ptr bs ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply SepWPp.of_sepWP_cs (mid := (blkPl_124).base + 6216#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (hinv0.trans hinv)

/-- Step `spqrSendPlacedEntry + 6208#64 .. spqrSendPlacedEntry + 6616#64` when `v1.innerState = some is`:
branches to `+6592`, computes jump-table index in `x8`, and loads `.rodata`
jump-table base address `lsρ spqrSendRoSym + 22#64` into `x9`. -/
theorem step_send_inner_to_6616_placed
    (ext : String → Option (State → State))
    {s0 s : State} (sp w : BitVec 64)
    (hw_beq : (w + 2#64 == 0#64) = false) (hw_bne : (w + 2#64 != 0#64) = true)
    {R : SepProp} {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 6208#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = w) (hinv0 : StepInv s0 s)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6616#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x8 =
        (if BitVec.ult (w ^^^ 0x8000000000000000#64) 11#64
         then w ^^^ 0x8000000000000000#64 else 7#64) →
      sm.readReg64 .x9 = lsρ spqrSendRoSym + 22#64 →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = w →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x25 = s.readReg64 .x25 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm P
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply SepWPp.of_sepWP_cs (mid := (blkPl_124).base + 6616#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, blkPl_124_ρ, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hinv0.trans hinv)

/-! ## `StepSendInnerStateAt6616Placed` and `step_send_inner_32058_placed` -/

/-- Unified stepping obligation from `spqrSendPlacedEntry + 6616#64` (jump-table dispatch)
to `spqrSendPlacedEntry + 6216#64` (post-encode join) for a `V1State.InnerState` value `is`. -/
def StepSendInnerStateAt6616Placed (resStack : Nat) (A : RustAlloc)
    (ext : String → Option (State → State)) (roBase : BitVec 64)
    (s0 : State) (is : V1State.InnerState) : Prop :=
  ∀ (sp cap ptr w25 : BitVec 64) (g : V1StatePBGhost) (bs : List (BitVec 8)),
    v1StatePBEncodedLen ⟨some is⟩ < 2 ^ 64 →
    bs.length + (V1State.InnerState.encode is).length ≤ cap.toNat →
    sp &&& 15#64 = 0#64 →
    ∀ {R : SepProp} {ret : BitVec 64} {s : State} {P F : SepProp} {Q : State → SepProp → Prop},
      s.pc = spqrSendPlacedEntry + 6616#64 →
      s.status = .Running →
      s.sp = sp →
      s.trace = s0.trace →
      s.readReg64 .x8 =
        (if BitVec.ult (v1StateInnerCap g is ^^^ 0x8000000000000000#64) 11#64
         then v1StateInnerCap g is ^^^ 0x8000000000000000#64 else 7#64) →
      s.readReg64 .x9 = roBase →
      s.readReg64 .x20 = v1StateInnerCap g is →
      s.readReg64 .x25 = w25 →
      StepInv s0 s →
      P = (v1StateInnerPBPinnedAt A g (sp + 4832#64) is ∗
        ((sp + 16#64) ↦₆₄ w25) ∗
        (roBase ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
        vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗
        stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F →
      (∀ sm : State,
        sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
        sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
        sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
        sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
        sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
        SepWPp (spqrSendPlacedProg ext) ret sm
          ((v1StateInnerPBPinnedAt A g (sp + 4832#64) is ∗
            ((sp + 16#64) ↦₆₄ w25) ∗
            (roBase ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
            vecU8At A (sp + 1424#64) cap ptr (bs ++ V1State.InnerState.encode is) ∗ A.pool ∗
            stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) →
      SepWPp (spqrSendPlacedProg ext) ret s P Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))

/-- Step `spqrSendPlacedEntry + 6140#64 .. spqrSendPlacedEntry + 6216#64`: encodes `st.inner`
into `vecU8At A (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr`,
producing `PqRatchetState.encodeRaw st`. -/
theorem step_send_inner_32058_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State))
    {roV1 : BitVec 64} {s0 s : State}
    (hv1Len : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 177)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A roV1)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 148)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hInnerAt6616 : ∀ is : V1State.InnerState,
      StepSendInnerStateAt6616Placed resStack A ext (lsρ spqrSendRoSym + 22#64) s0 is)
    (sp ptr w25 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 6140#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = optPqRatchetInnerCap g.inner st.inner)
    (hx25 : s.readReg64 .x25 = w25) (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
      ((sp + 16#64) ↦₆₄ w25) ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      vecU8At A (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
        (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation ++
          Proto.encodeOptMessage ChainPB.encodeRaw 2#32 st.chain) ∗
      A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
          ((sp + 16#64) ↦₆₄ w25) ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
          vecU8At A (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
            (PqRatchetState.encodeRaw st) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  have h4832 : (sp + 4704#64) + 128#64 = sp + 4832#64 := by bv_omega
  let cap := BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)
  let bs0 := Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation ++
    Proto.encodeOptMessage ChainPB.encodeRaw 2#32 st.chain
  have hcap_toNat : cap.toNat = pqRatchetStatePBEncodedLen st := by
    dsimp only [cap]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  cases hin : st.inner with
  | none =>
    rw [hin] at hx20
    refine step_send_inner_none_32058_placed ext sp hpc hrun hsp htr hx20 hinv0 ?_
    intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m
    rw [hx25] at hm25
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
    have henc : PqRatchetState.encodeRaw st = bs0 := by
      unfold PqRatchetState.encodeRaw
      rw [hin]; simp only [bs0, List.append_nil]
    rw [henc]
    exact Entails.of_eq (by ac_rfl)
  | some inner =>
    cases inner with
    | v1 v1 =>
      rw [hin] at hx20
      have ⟨hv1_len64, _, _⟩ := v1StatePBEncodedLen_lt_of_state hin hlen
      have hv1_all : bs0.length + (PqRatchetState.Inner.encode (.v1 v1)).length ≤ cap.toNat := by
        rw [hcap_toNat, ← pqRatchetStatePBEncodedLen_eq_proto st]
        unfold PqRatchetState.encodeRaw
        rw [hin]; simp only [bs0, List.length_append]
        exact Nat.le_refl _
      rw [encodeInner_v1_eq v1] at hv1_all
      simp only [List.length_append, List.length_singleton,
        show (V1State.encodeRaw v1).length = v1StatePBEncodedLen v1 from v1StatePBEncodedLen_eq_proto v1] at hv1_all
      let F_outer : SepProp :=
        optVersionNegotiationPBPinnedAt A g.vn (sp + 4704#64) st.versionNegotiation ∗
          optChainPBPinnedAt A g.chain ((sp + 4704#64) + 48#64) st.chain ∗
          ((sp + 16#64) ↦₆₄ w25) ∗
          ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗ F
      refine step_send_inner_some_hdr_32058_placed hres A ext hv1Len hvarint
        sp cap ptr g.inner v1 bs0 hv1_len64 (by omega) halign
        (F := F_outer)
        hpc hrun hsp htr hx20 hinv0
        (by unfold pqRatchetStatePBPinnedAt; rw [hin, h4832]
            dsimp only [optPqRatchetInnerPBPinnedAt, cap, bs0, F_outer]; ac_rfl) ?_
      intro s1 hpcs1 hruns1 hsps1 htrs1 hs1_19 hs1_20 hs1_21 hs1_23 hs1_25 hs1_27 hs1_28 hs1_fp hinv_s1
      rw [hx25] at hs1_25
      let bs_hdr := (bs0 ++ [0x1a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StatePBEncodedLen v1))
      cases his : v1.innerState with
      | none =>
        have hx20_none : s1.readReg64 .x20 = noneCap2 := by
          rw [hs1_20]; dsimp only [optPqRatchetInnerCap]; rw [his]
        refine step_send_inner_v1_none_32094_placed A ext sp cap ptr bs_hdr halign
          (F := v1StatePBPinnedAt A g.inner (sp + 4832#64) v1 ∗
            (roV1 ↦ᵣ v1StateJumpTableBytes) ∗ A.pool ∗
            stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F_outer)
          hpcs1 hruns1 hsps1 htrs1 hx20_none hinv_s1 (by dsimp only [bs_hdr]; ac_rfl) ?_
        intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m
        rw [hs1_19] at hm19; rw [hs1_21] at hm21; rw [hs1_23] at hm23; rw [hs1_25] at hm25
        rw [hs1_27] at hm27; rw [hs1_28] at hm28; rw [hs1_fp] at hmfp
        refine SepWPp.weaken_pre ?_
          (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
        have henc : PqRatchetState.encodeRaw st = bs_hdr := by
          unfold PqRatchetState.encodeRaw
          rw [hin]; dsimp only
          rw [encodeInner_v1_eq v1]
          dsimp only [V1State.encodeRaw]
          rw [his]
          simp only [List.append_nil, bs0, bs_hdr, List.append_assoc]
        rw [henc]
        unfold pqRatchetStatePBPinnedAt
        rw [hin, h4832]
        dsimp only [optPqRatchetInnerPBPinnedAt, cap, bs_hdr, F_outer]
        exact Entails.of_eq (by ac_rfl)
      | some is =>
        have hx20_some : s1.readReg64 .x20 = v1StateInnerCap g.inner is := by
          rw [hs1_20]; dsimp only [optPqRatchetInnerCap]; rw [his]
        refine sepWPp_extract_pure
          ((v1StateInnerCap g.inner is + 2#64 == 0#64) = false ∧
            (v1StateInnerCap g.inner is + 2#64 != 0#64) = true)
          (fun R' hm => by
            dsimp only [v1StatePBPinnedAt] at hm
            rw [his] at hm
            dsimp only at hm
            have hm' : s1.mem ⊨ v1StateInnerPBPinnedAt A g.inner (sp + 4832#64) is ∗
                ((roV1 ↦ᵣ v1StateJumpTableBytes) ∗
                 vecU8At A (sp + 1424#64) cap ptr bs_hdr ∗ A.pool ∗
                 stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F_outer ∗ R') := by
              convert hm using 1; dsimp only [bs_hdr]; ac_rfl
            exact v1StateInnerCap_add_two_bounds hm')
          fun ⟨hw_beq2, hw_bne2⟩ => ?_
        refine step_send_inner_to_6616_placed ext sp (v1StateInnerCap g.inner is)
          hw_beq2 hw_bne2 hpcs1 hruns1 hsps1 htrs1 hx20_some hinv_s1 ?_
        intro s2 hpcs2 hruns2 hsps2 htrs2 hs2_8 hs2_9 hs2_19 hs2_20 hs2_21 hs2_23 hs2_25 hs2_27 hs2_28 hs2_fp hinv_s2
        rw [hs1_19] at hs2_19; rw [hs1_21] at hs2_21; rw [hs1_23] at hs2_23; rw [hs1_25] at hs2_25
        rw [hs1_27] at hs2_27; rw [hs1_28] at hs2_28; rw [hs1_fp] at hs2_fp
        have hv_len64' : v1StatePBEncodedLen ⟨some is⟩ < 2 ^ 64 := by
          have : v1 = ⟨some is⟩ := by cases v1; subst his; rfl
          rw [← this]; exact hv1_len64
        have his_fit : bs_hdr.length + (V1State.InnerState.encode is).length ≤ cap.toNat := by
          have hlen_is : (V1State.InnerState.encode is).length = v1StatePBEncodedLen v1 := by
            rw [← v1StatePBEncodedLen_eq_proto v1]
            dsimp only [V1State.encodedLen, V1State.encodeRaw]; rw [his]
          simp only [bs_hdr, List.length_append, List.length_singleton, hlen_is]
          omega
        refine hInnerAt6616 is sp cap ptr w25 g.inner bs_hdr hv_len64' his_fit halign
          hpcs2 hruns2 hsps2 htrs2 hs2_8 hs2_9 hs2_20 hs2_25 hinv_s2
          (F := optVersionNegotiationPBPinnedAt A g.vn (sp + 4704#64) st.versionNegotiation ∗
            optChainPBPinnedAt A g.chain ((sp + 4704#64) + 48#64) st.chain ∗
            (roV1 ↦ᵣ v1StateJumpTableBytes) ∗ F)
          (by dsimp only [v1StatePBPinnedAt, bs_hdr, F_outer]; rw [his]; dsimp only; ac_rfl) ?_
        intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m
        rw [hs2_19] at hm19; rw [hs2_21] at hm21; rw [hs2_23] at hm23
        rw [hs2_27] at hm27; rw [hs2_28] at hm28; rw [hs2_fp] at hmfp
        refine SepWPp.weaken_pre ?_
          (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
        have henc : PqRatchetState.encodeRaw st = bs_hdr ++ V1State.InnerState.encode is := by
          unfold PqRatchetState.encodeRaw
          rw [hin]; dsimp only
          rw [encodeInner_v1_eq v1]
          dsimp only [V1State.encodeRaw]
          rw [his]
          simp only [bs0, bs_hdr, List.append_assoc]
        rw [henc]
        unfold pqRatchetStatePBPinnedAt
        rw [hin, h4832]
        dsimp only [optPqRatchetInnerPBPinnedAt, v1StatePBPinnedAt, cap]
        rw [his]
        exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Top.Send
