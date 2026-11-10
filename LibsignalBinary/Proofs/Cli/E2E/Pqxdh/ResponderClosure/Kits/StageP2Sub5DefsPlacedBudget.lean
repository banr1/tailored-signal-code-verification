/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Relocatable Stage P2 Substage P2.5 V1 Bundle and Combinators

Defines `p2BobSessV1At` over `RustCliAllocBudget M`, `LibsignalCodeRoLoaded` / `StageP2MemInv` call
combinators, `VmPreserved` `is_same_account` bridges, and stack-parameterized
`initializeBobSessionErrOwned` contracts on Block `518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (
  LibsignalPlacement lsLogFilterAddr lsmpl withLsCodeLoaded
)
open CryptoVerification.RustHeap (RustAlloc allocFailedIn)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.E2E.Pqxdh.Initiator (
  AcceptKeysInput Bytes DRKey Primitives WellSizedAcceptKeysInput
  bytesToBv8 encodeEC pqxdhEntryStack pqxdhEntryStackExt
)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys)
open CryptoVerification.E2E.Pqxdh.WireEntries (
  IsSameAccountDistinctGhost isSameAccountDistinctStack
)
open CryptoVerification.E2E.Pqxdh.ResponderCore (
  InitBobCallGhost bobParamsFieldsAt initBobErrAt
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (PanicOomProp stageP2bStack)
open CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq (isSameAccountDistinctStackExt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  p2BobSession344Bv8V1 p2_bind_sepWP_qp_frame_placed
  p2_call_nopanic_rocl_steps_frame_placed p2_stackAt_split_of_le
)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded extract_withLsCodeRoLoaded speWordsAt
  subroutine_ok_rocl_of_withLsCodeRoLoaded withLsCodeRoLoaded withLsRoCl
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget (
  isSameAccountDistinctAtSpec isSameAccountDistinctSpec isSameAccountDistinctSpecExt
  p2BobSpqrVecBufBudget
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  initializeBobSessionErrOwned4KInnerPlacedSpec p2_call_frame_cro_nopanic_placed
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget (
  initializeBobSessionErrOwnedInnerPlacedSpec initializeBobSessionErrOwnedPlacedSpec
)

/-! ## 1. Budget-Threaded V1 Session Bundle & Substage-5 Stack / Error Helpers -/

/-- The `0x700` stack bytes `initialize_bob_session` at SPQR V1 needs below `stageP2bStack`. -/
def p2BobV1StackExtra (sp : BitVec 64) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2BobV1StackExtra sp

theorem p2BobV1StackExtra_join (sp : BitVec 64) :
    stackAt sp (stageP2bStack + 0x700) = p2BobV1StackExtra sp ∗ stackAt sp stageP2bStack :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2BobV1StackExtra_join sp

/-- Bob's 344-byte V1 `SessionState` at `outPtr`, its SPQR vec buffer, and its 7 heap boxes over
`A : RustCliAllocBudget M` (`A.repAlloc`). -/
def p2BobSessV1At {M : AllocCostModel} (A : RustCliAllocBudget M) (outPtr : BitVec 64)
    (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes) (drKey : DRKey)
    (pq : List (BitVec 8)) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2BobSessV1At
    A.repAlloc outPtr inp ikBPk spkBPk drKey pq

abbrev p2BobSessV1AtBudget := @p2BobSessV1At

theorem p2BobSessV1At_intro {M : AllocCostModel} (A : RustCliAllocBudget M) (outPtr : BitVec 64)
    (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes) (drKey : DRKey) (pq : List (BitVec 8))
    (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr ratchetPubBoxPtr ratchetPrivBoxPtr
      chainKeyBoxPtr spqrCap spqrBufPtr : BitVec 64) (pad_f4 : BitVec 32)
    (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64)
    (h1 : localIkBoxPtr ≠ 0#64) (h2 : remoteIkBoxPtr ≠ 0#64) (h3 : rootKeyBoxPtr ≠ 0#64)
    (h4 : baseKeyBoxPtr ≠ 0#64) (h5 : ratchetPubBoxPtr ≠ 0#64) (h6 : ratchetPrivBoxPtr ≠ 0#64)
    (h7 : chainKeyBoxPtr ≠ 0#64) :
    (outPtr ↦ₛ p2BobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
      spqrCap spqrBufPtr (BitVec.ofNat 64 pq.length) ratchetPubBoxPtr ratchetPrivBoxPtr
      chainKeyBoxPtr pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
    p2BobSpqrVecBufBudget A spqrCap spqrBufPtr pq ∗
    (localIkBoxPtr ↦ₛ bytesToBv8 (encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
    (remoteIkBoxPtr ↦ₛ bytesToBv8 (encodeEC inp.hdr.ikAPk)) ∗
      A.live remoteIkBoxPtr 33 1 ∗
    (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
    (baseKeyBoxPtr ↦ₛ bytesToBv8 (encodeEC inp.hdr.ekAPk)) ∗
      A.live baseKeyBoxPtr 33 1 ∗
    (ratchetPubBoxPtr ↦ₛ bytesToBv8 (encodeEC spkBPk)) ∗
      A.live ratchetPubBoxPtr 33 1 ∗
    (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
    (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ⊢
      p2BobSessV1At A outPtr inp ikBPk spkBPk drKey pq :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2BobSessV1At_intro
    A.repAlloc outPtr inp ikBPk spkBPk drKey pq
    localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr ratchetPubBoxPtr ratchetPrivBoxPtr
    chainKeyBoxPtr spqrCap spqrBufPtr pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
    h1 h2 h3 h4 h5 h6 h7

theorem p2_entails_frame_v1 {P P₁ P₂ F Q : SepProp} (hent : P₁ ⊢ P₂) (hP : P = P₁ ∗ F)
    (h : P₂ ∗ F ⊢ Q) : P ⊢ Q :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2_entails_frame_v1 hent hP h

theorem p2_initBobErrAt_entails_speWordsAt (sp : BitVec 64) :
    initBobErrAt (sp + 0x3e0#64) ⊢
      ∃∗ errTag : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
        ⌜errTag ≠ 0xfffffffffffffffe#64 ∧ errTag ≠ 0xfffffffffffffffd#64⌝ ∗
        ((sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
        speWordsAt (sp + 0x3e8#64) errTag w2 w3 w4 w5 w6 ∗
        memRegion (sp + 0x418#64) 288 :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2_initBobErrAt_entails_speWordsAt sp

theorem p2_stageP2bStack_le_bobV1 :
    stageP2bStack ≤ stageP2bStack + 0x700 :=
  Nat.le_add_right _ _

theorem p2_isSameAccount_le_bobV1 :
    isSameAccountDistinctStack ≤ stageP2bStack + 0x700 := by
  decide

theorem p2_isSameAccountExt_le_bobExt :
    isSameAccountDistinctStackExt ≤ 768 + pqxdhEntryStackExt := by
  decide

theorem p2_bobErr4K_le_bobExt :
    768 + pqxdhEntryStackExt ≤ 768 + pqxdhEntryStackExt :=
  Nat.le_refl _

/-! ## 2. Placed `LibsignalCodeRoLoaded` Sequencing and Call Combinators -/

/-- Bind a `SepWPp` segment ending at `mid` into a `Qp₂` continuation via `hpan : Qp₁ -> Qp₂`,
threading `LibsignalCodeRoLoaded lsmpl`. -/
theorem p2_bind_loaded_cro_sub5 [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {Qm post Qp₁ Qp₂ : State → SepProp → Prop}
    (hpan : ∀ sf Pf, Qp₁ sf Pf → Qp₂ sf Pf)
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWPp prog mid s P Qm Qp₁)
    (h2 : ∀ sm Pm, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → Qm sm Pm →
      SepWPp prog target sm Pm post Qp₂) :
    SepWPp prog target s P post Qp₂ := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hQ⟩ | ⟨hp, Pm, hmm, hqp⟩ | hoom⟩ := h1 R hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      h2 sm Pm hsteps hpcm hrunm (hCode.of_keepsFrozen hsteps.keepsFrozen) hQ
        R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hp, Pm, hmm, hpan sm Pm hqp⟩)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

/-- Bind a `SepWPp` segment under `PanicOomProp s0` into a `Qp` continuation, threading
`LibsignalCodeRoLoaded lsmpl`. -/
theorem p2_bind_loaded_cro_sub5_qpan [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s0 s : State} {P : SepProp} {Qm post Qp : State → SepProp → Prop}
    (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWPp prog mid s P Qm (PanicOomProp s0))
    (h2 : ∀ sm Pm, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → Qm sm Pm →
      SepWPp prog target sm Pm post Qp) :
    SepWPp prog target s P post Qp :=
  p2_bind_loaded_cro_sub5 hpan hCode h1 h2

/-- Bind a `SepWP` basic block (constant spatial postcondition) into a `SepWPp` continuation,
threading `LibsignalCodeRoLoaded lsmpl`. -/
theorem p2_bind_sepWP_steps_cro_sub5_qpan [LibsignalPlacement] {prog : Program}
    {mid ret : BitVec 64} {s : State} {P P_seg F P_seg_post : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem)
    (hseg : SepWP prog mid s P_seg (fun sm P_m => (P_m ⊢ P_seg_post) ∧ Q_regs sm))
    (hP : P = P_seg ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_seg_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  p2_bind_sepWP_qp_frame_placed hCode hseg hP hnext

/-- State-indexed postcondition variant of `p2_bind_sepWP_steps_cro_sub5_qpan` for budget-threaded
`SepWP` segments whose spatial postcondition contains `A.pool lim st' sm`. -/
theorem p2_bind_sepWP_steps_cro_sub5_state [LibsignalPlacement] {prog : Program}
    {mid ret : BitVec 64} {s : State} {P P_seg F : SepProp} {P_seg_post : State → SepProp}
    {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem)
    (hseg : SepWP prog mid s P_seg (fun sm P_m => (P_m ⊢ P_seg_post sm) ∧ Q_regs sm))
    (hP : P = P_seg ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_seg_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hseg.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_seg_post sm ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
  have hCodem : LibsignalCodeRoLoaded lsmpl sm.mem :=
    hCode.of_keepsFrozen hsteps.keepsFrozen
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hsteps hpcm hrunm hCodem hregs R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

/-- Bind a panic-free (`Qp = fun _ _ => False`) `SepWPp` stage into any `Qp` continuation,
threading `LibsignalCodeRoLoaded lsmpl`. -/
theorem p2_bind_sepWPp_cro_sub5_nopanic [LibsignalPlacement] {prog : Program}
    {mid ret : BitVec 64} {s : State} {P P_stage F : SepProp}
    {P_stage_post : State → SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem)
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post sm) ∧ Q_regs sm)
      (fun _ _ => False))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_stage_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨_, _, _, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm (hCode.of_keepsFrozen hsteps.keepsFrozen) hregs
        R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact False.elim hpanm
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Bind a `SepWPp` stage under `PanicOomProp s0` into a `Qp` continuation, threading
`LibsignalCodeRoLoaded lsmpl`. -/
theorem p2_bind_sepWPp_cro_sub5_qpan [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s0 s : State} {P P_stage F : SepProp} {P_stage_post : State → SepProp}
    {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem)
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post sm) ∧ Q_regs sm)
      (PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_stage_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2_bind_sepWPp_cro_sub5_qpan
    hpan hCode hstage hP hnext

/-- Call a panic-free (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`) `withLsRoCl lsmpl spec` subroutine
from entailment `P_spec ⊢ spec.pre x s`, threading `LibsignalCodeRoLoaded lsmpl` into any `Qp`. -/
theorem p2_call_nopanic_rocl_sub5 [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State}
    {P P_spec F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsRoCl lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : P_spec ⊢ spec.pre x s)
    (hP : P = P_spec ∗ F)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  rw [hP]
  refine SepWPp.weaken_pre (sepConj_mono_left hpre) ?_
  exact p2_call_frame_cro_nopanic_placed hcrl hcall hpc hrun hsp hlr
    (φ := LibsignalCodeRoLoaded lsmpl s.mem) (T := spec.pre x s) (F := F)
    (by dsimp only [withLsRoCl]; rw [sepConj_comm])
    hcrl rfl hpan_false hexit_false
    (fun sf hpcm hrunm hspm hsp_alm hcsm hcrl' hsteps =>
      SepWPp.weaken_pre
        (sepConj_mono_left (Entails.pure_left fun _ => Entails.refl _))
        (hnext sf hsteps hpcm hrunm hspm hsp_alm hcsm hcrl'))
    hoom_false

/-- Call a panic-free (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`) `withLsCodeRoLoaded lsmpl spec`
subroutine (`spec.pre x s = ⌜φ⌝ ∗ T`), threading `LibsignalCodeRoLoaded lsmpl` into any `Qp`. -/
theorem p2_call_cro_nopanic_steps_frame_sub5 [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp :=
  p2_call_nopanic_rocl_steps_frame_placed hcrl
    (subroutine_ok_rocl_of_withLsCodeRoLoaded hcall)
    hpc hrun hsp hlr hspec hφ hP hnext hpan_false hexit_false hoom_false

/-- `PanicOomProp s0`-forwarding `withLsRoCl` call combinator (compatibility bridge). -/
theorem p2_call_oom_rocl_sub5_qpan [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    {P P_spec F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpan_qp : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s0.trace <+: s.trace)
    (hcall : subroutine_ok prog entry (withLsRoCl lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : P_spec ⊢ spec.pre x s)
    (hP : P = P_spec ∗ F)
    (hpan : ∀ sf, spec.onPanic x s sf ⊢ ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2_call_oom_rocl_sub5_qpan
    hpan_qp hcrl htr hcall hpc hrun hsp hlr hpre hP hpan hnext hexit_false hoom_false

/-! ## 3. Placed `VmPreserved`-Augmented `isSameAccountDistinct` Bridges & Error Equalities -/

theorem isSameAccountDistinctSpec_to_at_placed [LibsignalPlacement] {prog : Program}
    {entry : BitVec 64} {A : RustAlloc} {parse : UuidParser}
    (h : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A parse))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (isSameAccountDistinctAtSpec A parse isSameAccountDistinctStack)) := by
  refine subroutine_ok_map h ?_
  rintro ⟨lIkA, lIk, locA, loc, rIkA, rIk, remA, rem⟩ R s0 hpre
  dsimp only [withLsCodeLoaded, isSameAccountDistinctAtSpec, withVmPreserved,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.isSameAccountDistinctAtSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨({ localIkA := lIkA, localIk := lIk, locA := locA, loc := loc,
             remoteIkA := rIkA, remoteIk := rIk, remA := remA, rem := rem } :
             IsSameAccountDistinctGhost), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [withLsCodeLoaded, isSameAccountDistinctSpec, withVmPreserved,
      CryptoVerification.E2E.Pqxdh.WireEntries.isSameAccountDistinctSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by sep_ac_rfl)⟩
  · dsimp only [withLsCodeLoaded, isSameAccountDistinctSpec, isSameAccountDistinctAtSpec,
      withVmPreserved,
      CryptoVerification.E2E.Pqxdh.WireEntries.isSameAccountDistinctSpec,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.isSameAccountDistinctAtSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, hpost.2.1, Satisfies.of_eq hpost.2.2 (by sep_ac_rfl)⟩

theorem isSameAccountDistinctSpecExt_to_at_placed [LibsignalPlacement] {prog : Program}
    {entry : BitVec 64} {A : RustAlloc} {parse : UuidParser}
    (h : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpecExt A parse))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        (isSameAccountDistinctAtSpec A parse isSameAccountDistinctStackExt)) :=
  h

theorem pqxdhAcceptErrPayloadAt_eq_kits (A : RustAlloc) (errTag w2 w3 w4 : BitVec 64) :
    CryptoVerification.E2E.Pqxdh.ResponderCore.pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 =
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.pqxdhAcceptErrPayloadAt_eq_kits
    A errTag w2 w3 w4

theorem initBobErrOwnedAt_eq_kits (A : RustAlloc) (outPtr : BitVec 64) :
    CryptoVerification.E2E.Pqxdh.ResponderCore.initBobErrOwnedAt A outPtr =
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.initBobErrOwnedAt A outPtr :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.initBobErrOwnedAt_eq_kits A outPtr

/-! ## 4. Stack-Parameterized Budget-Threaded `initializeBobSessionErrOwned` (`Sub5Placed`) -/

namespace Sub5Placed

/-- Stack-parameterized placed `initializeBobSessionErrOwned` inner contract over
`A : RustCliAllocBudget M` (`Kits.initBobErrOwnedAt A.repAlloc`, `onPanic = ⌜False⌝`,
`onOom = ⌜False⌝` under `FitsEnv M lim st (AcceptErrEnv g.inp)`). -/
def initializeBobSessionErrOwnedAtInnerPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) (stk : Nat) :
    Spec (InitBobCallGhost × M.σ) where
  pre := fun (g, st) s =>
    ⌜s.readReg64 .x0 = g.argPtr ∧
      s.readReg64 .x1 = g.ratchetKeyPairPtr ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inp.trustedPeer = true ∧
      g.inp.replayOk = true ∧
      g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧
      WellSizedAcceptKeysInput g.inp ∧
      g.ikBPk.length = 32 ∧
      g.spkBPk.length = 32 ∧
      acceptKeys P g.inp = none ∧
      FitsEnv M lim st (AcceptErrEnv g.inp)⌝ ∗
    bobParamsFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
      g.inp g.ikBPk g.spkBPk g.sameAccountByte ∗
    memRegion g.outPtr 344 ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗
    stackAt s.sp stk ∗
    A.pool lim st s
  post := fun (g, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AcceptErrEnv g.inp evs⌝ ∗
      bobParamsFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
        g.inp g.ikBPk g.spkBPk g.sameAccountByte ∗
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.initBobErrOwnedAt
        A.repAlloc g.outPtr ∗ anyHeap) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      stackAt s0.sp stk ∗
      A.pool lim (M.stepEvents evs st) sf

abbrev initializeBobSessionErrOwnedAtPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) (stk : Nat) :
    Spec (InitBobCallGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl
    (initializeBobSessionErrOwnedAtInnerPlacedSpec P A lim AcceptErrEnv stk)

abbrev initializeBobSessionErrOwned4KPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (InitBobCallGhost × M.σ) :=
  initializeBobSessionErrOwnedAtPlacedSpec P A lim AcceptErrEnv (768 + pqxdhEntryStackExt)

theorem of_responderCore_errOwned_placed [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (h : subroutine_ok prog entry
      (initializeBobSessionErrOwnedPlacedSpec P A lim AcceptErrEnv)) :
    subroutine_ok prog entry
      (initializeBobSessionErrOwnedAtPlacedSpec P A lim AcceptErrEnv (768 + pqxdhEntryStack)) := by
  refine subroutine_ok_map h ?_
  rintro ⟨g, st⟩ R s0 hpre
  refine ⟨(g, st), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [initializeBobSessionErrOwnedAtPlacedSpec,
      initializeBobSessionErrOwnedAtInnerPlacedSpec, withLsCodeRoLoaded,
      initializeBobSessionErrOwnedPlacedSpec,
      initializeBobSessionErrOwnedInnerPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded] at hpre ⊢
    have hcro : LibsignalCodeRoLoaded lsmpl s0.mem =
        CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem := rfl
    simpa only [hcro] using hpre
  · dsimp only [initializeBobSessionErrOwnedAtPlacedSpec,
      initializeBobSessionErrOwnedAtInnerPlacedSpec, withLsCodeRoLoaded,
      initializeBobSessionErrOwnedPlacedSpec,
      initializeBobSessionErrOwnedInnerPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded] at hpost ⊢
    simpa only [initBobErrOwnedAt_eq_kits] using hpost

theorem of_stageP2Defs_errOwned4K_placed [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (h : subroutine_ok prog entry
      (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget.initializeBobSessionErrOwned4KPlacedSpec
        P A lim AcceptErrEnv)) :
    subroutine_ok prog entry
      (initializeBobSessionErrOwned4KPlacedSpec P A lim AcceptErrEnv) := by
  refine subroutine_ok_map h ?_
  rintro ⟨g, st⟩ R s0 hpre
  refine ⟨(g, st), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [initializeBobSessionErrOwned4KPlacedSpec,
      initializeBobSessionErrOwnedAtPlacedSpec,
      initializeBobSessionErrOwnedAtInnerPlacedSpec, withLsCodeRoLoaded,
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget.initializeBobSessionErrOwned4KPlacedSpec,
      initializeBobSessionErrOwned4KInnerPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded] at hpre ⊢
    have hcro : LibsignalCodeRoLoaded lsmpl s0.mem =
        CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem := rfl
    simpa only [hcro] using hpre
  · dsimp only [initializeBobSessionErrOwned4KPlacedSpec,
      initializeBobSessionErrOwnedAtPlacedSpec,
      initializeBobSessionErrOwnedAtInnerPlacedSpec, withLsCodeRoLoaded,
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget.initializeBobSessionErrOwned4KPlacedSpec,
      initializeBobSessionErrOwned4KInnerPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded] at hpost ⊢
    simpa only [initBobErrOwnedAt_eq_kits] using hpost

theorem initializeBobSessionErrOwnedAtPlacedSpec_mono_stack [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {stk₁ stk₂ : Nat} (hle : stk₁ ≤ stk₂) (hbound : stk₂ ≤ 2 ^ 64)
    (h : subroutine_ok prog entry
      (initializeBobSessionErrOwnedAtPlacedSpec P A lim AcceptErrEnv stk₁)) :
    subroutine_ok prog entry
      (initializeBobSessionErrOwnedAtPlacedSpec P A lim AcceptErrEnv stk₂) := by
  refine subroutine_ok_map h ?_
    (fun _ _ _ _ _ hp => not_satisfies_false_sepConj
      (by dsimp only [initializeBobSessionErrOwnedAtPlacedSpec,
            initializeBobSessionErrOwnedAtInnerPlacedSpec, withLsCodeRoLoaded] at hp; exact hp))
    (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj
      (by dsimp only [initializeBobSessionErrOwnedAtPlacedSpec,
            initializeBobSessionErrOwnedAtInnerPlacedSpec, withLsCodeRoLoaded] at he; exact he))
    (fun _ _ _ _ _ _ _ ho => False.elim (not_satisfies_false_sepConj
      (by dsimp only [initializeBobSessionErrOwnedAtPlacedSpec,
            initializeBobSessionErrOwnedAtInnerPlacedSpec, withLsCodeRoLoaded] at ho; exact ho)))
  rintro ⟨g, st⟩ R s0 hpre
  let F_stk : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk₂) (stk₂ - stk₁)
  obtain ⟨hro, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [initializeBobSessionErrOwnedAtInnerPlacedSpec] at hpre
  rw [p2_stackAt_split_of_le s0.sp stk₂ stk₁ hle hbound] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨(g, st), F_stk ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [initializeBobSessionErrOwnedAtPlacedSpec, withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hro, ?_⟩
    dsimp only [initializeBobSessionErrOwnedAtInnerPlacedSpec, F_stk]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by sep_ac_rfl)⟩
  · dsimp only [initializeBobSessionErrOwnedAtPlacedSpec,
      initializeBobSessionErrOwnedAtInnerPlacedSpec, withLsCodeRoLoaded, F_stk] at hpost ⊢
    rw [sepExists_sepConj_left] at hpost ⊢
    refine Satisfies.of_eq hpost ?_
    congr 1; funext evs
    rw [p2_stackAt_split_of_le s0.sp stk₂ stk₁ hle hbound]
    sep_ac_rfl

theorem of_responderCore_errOwned_to_4K_placed [LibsignalPlacement] {prog : Program}
    {entry : BitVec 64} {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (h : subroutine_ok prog entry
      (initializeBobSessionErrOwnedPlacedSpec P A lim AcceptErrEnv)) :
    subroutine_ok prog entry
      (initializeBobSessionErrOwned4KPlacedSpec P A lim AcceptErrEnv) :=
  initializeBobSessionErrOwnedAtPlacedSpec_mono_stack (by decide) (by decide)
    (of_responderCore_errOwned_placed h)

theorem initializeBobSessionErrOwnedAtPlacedSpec_mono_env [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env₁ Env₂ : AcceptKeysInput → List AllocEvent → Prop} {stk : Nat}
    (himp : ∀ inp evs, Env₁ inp evs → Env₂ inp evs)
    (h : subroutine_ok prog entry
      (initializeBobSessionErrOwnedAtPlacedSpec P A lim Env₁ stk)) :
    subroutine_ok prog entry
      (initializeBobSessionErrOwnedAtPlacedSpec P A lim Env₂ stk) := by
  refine subroutine_ok_map h ?_
    (fun _ _ _ _ _ hp => not_satisfies_false_sepConj
      (by dsimp only [initializeBobSessionErrOwnedAtPlacedSpec,
            initializeBobSessionErrOwnedAtInnerPlacedSpec, withLsCodeRoLoaded] at hp; exact hp))
    (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj
      (by dsimp only [initializeBobSessionErrOwnedAtPlacedSpec,
            initializeBobSessionErrOwnedAtInnerPlacedSpec, withLsCodeRoLoaded] at he; exact he))
    (fun _ _ _ _ _ _ _ ho => False.elim (not_satisfies_false_sepConj
      (by dsimp only [initializeBobSessionErrOwnedAtPlacedSpec,
            initializeBobSessionErrOwnedAtInnerPlacedSpec, withLsCodeRoLoaded] at ho; exact ho)))
  rintro ⟨g, st⟩ R s0 hpre
  obtain ⟨hro, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [initializeBobSessionErrOwnedAtInnerPlacedSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hfits⟩, hmem⟩
  have hfits₁ : FitsEnv M lim st (Env₁ g.inp) :=
    fun evs hevs => hfits evs (himp g.inp evs hevs)
  refine ⟨(g, st), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [initializeBobSessionErrOwnedAtPlacedSpec, withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hro, ?_⟩
    dsimp only [initializeBobSessionErrOwnedAtInnerPlacedSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hfits₁⟩, hmem⟩
  · dsimp only [initializeBobSessionErrOwnedAtPlacedSpec,
      initializeBobSessionErrOwnedAtInnerPlacedSpec, withLsCodeRoLoaded] at hpost ⊢
    refine Arm64.Satisfies.mono (sepConj_mono_left ?_) hpost
    refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
    simp only [sepConj_assoc]
    exact Entails.pure_left fun ⟨htr, hev⟩ =>
      Entails.pure_right ⟨htr, himp g.inp evs hev⟩ (Entails.refl _)

end Sub5Placed

export Sub5Placed (
  initializeBobSessionErrOwnedAtInnerPlacedSpec
  initializeBobSessionErrOwnedAtPlacedSpec
  initializeBobSessionErrOwned4KPlacedSpec
  of_responderCore_errOwned_placed
  initializeBobSessionErrOwnedAtPlacedSpec_mono_stack
)

/-! ## 5. `StageP2MemInv` Bind/Call Combinators & `Sub5Placed` Frozen Specs -/

theorem p2_bind_loaded_memInv_sub5 [LibsignalPlacement] {Φ : Memory → Prop}
    (hInv : StageP2DefsPlacedBudget.StageP2MemInv Φ) {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {Qm post Qp₁ Qp₂ : State → SepProp → Prop}
    (hpan : ∀ sf Pf, Qp₁ sf Pf → Qp₂ sf Pf)
    (hCode : Φ s.mem)
    (h1 : SepWPp prog mid s P Qm Qp₁)
    (h2 : ∀ sm Pm, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Φ sm.mem → Qm sm Pm →
      SepWPp prog target sm Pm post Qp₂) :
    SepWPp prog target s P post Qp₂ := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hQ⟩ | ⟨hp, Pm, hmm, hqp⟩ | hoom⟩ := h1 R hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      h2 sm Pm hsteps hpcm hrunm (hInv.of_keepsFrozen hCode hsteps.keepsFrozen) hQ
        R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hp, Pm, hmm, hpan sm Pm hqp⟩)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem p2_bind_loaded_memInv_sub5_qpan [LibsignalPlacement] {Φ : Memory → Prop}
    (hInv : StageP2DefsPlacedBudget.StageP2MemInv Φ) {prog : Program} {mid target : BitVec 64}
    {s0 s : State} {P : SepProp} {Qm post Qp : State → SepProp → Prop}
    (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (hCode : Φ s.mem)
    (h1 : SepWPp prog mid s P Qm (PanicOomProp s0))
    (h2 : ∀ sm Pm, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Φ sm.mem → Qm sm Pm →
      SepWPp prog target sm Pm post Qp) :
    SepWPp prog target s P post Qp := by
  exact p2_bind_loaded_memInv_sub5 hInv hpan hCode h1 h2

theorem p2_bind_sepWP_steps_memInv_sub5_qpan [LibsignalPlacement] {Φ : Memory → Prop}
    (hInv : StageP2DefsPlacedBudget.StageP2MemInv Φ) {prog : Program}
    {mid ret : BitVec 64} {s : State} {P P_seg F P_seg_post : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hCode : Φ s.mem)
    (hseg : SepWP prog mid s P_seg (fun sm P_m => (P_m ⊢ P_seg_post) ∧ Q_regs sm))
    (hP : P = P_seg ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Φ sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_seg_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hseg.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_seg_post ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hsteps hpcm hrunm (hInv.of_keepsFrozen hCode hsteps.keepsFrozen) hregs
      R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

theorem p2_bind_sepWP_steps_memInv_sub5_state [LibsignalPlacement] {Φ : Memory → Prop}
    (hInv : StageP2DefsPlacedBudget.StageP2MemInv Φ) {prog : Program}
    {mid ret : BitVec 64} {s : State} {P P_seg F : SepProp} {P_seg_post : State → SepProp}
    {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hCode : Φ s.mem)
    (hseg : SepWP prog mid s P_seg (fun sm P_m => (P_m ⊢ P_seg_post sm) ∧ Q_regs sm))
    (hP : P = P_seg ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Φ sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_seg_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hseg.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_seg_post sm ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hsteps hpcm hrunm (hInv.of_keepsFrozen hCode hsteps.keepsFrozen) hregs
      R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

theorem p2_bind_sepWPp_memInv_sub5_nopanic [LibsignalPlacement] {Φ : Memory → Prop}
    (hInv : StageP2DefsPlacedBudget.StageP2MemInv Φ) {prog : Program}
    {mid ret : BitVec 64} {s : State} {P P_stage F : SepProp}
    {P_stage_post : State → SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hCode : Φ s.mem)
    (hstage :
      SepWPp prog mid s P_stage
        (fun sm P_m => (P_m ⊢ P_stage_post sm) ∧ Q_regs sm)
        (fun _ _ => False))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Φ sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_stage_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨_, _, _, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm (hInv.of_keepsFrozen hCode hsteps.keepsFrozen) hregs
        R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact False.elim hpanm
  · exact (not_satisfies_false_sepConj hoom).elim

theorem p2_call_nopanic_rocl_memInv_sub5 [LibsignalPlacement] {Φ : Memory → Prop}
    (hInv : StageP2DefsPlacedBudget.StageP2MemInv Φ) {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State}
    {P P_spec F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcrl : Φ s.mem)
    (hcall : subroutine_ok prog entry (withLsRoCl lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : P_spec ⊢ spec.pre x s)
    (hP : P = P_spec ∗ F)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      Φ sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  rw [hP]
  refine SepWPp.weaken_pre (sepConj_mono_left hpre) ?_
  exact p2_call_frame_cro_nopanic_placed (hInv.toCodeRo hcrl) hcall hpc hrun hsp hlr
    (φ := LibsignalCodeRoLoaded lsmpl s.mem) (T := spec.pre x s) (F := F)
    (by dsimp only [withLsRoCl]; rw [sepConj_comm])
    (hInv.toCodeRo hcrl) rfl hpan_false hexit_false
    (fun sf hpcm hrunm hspm hsp_alm hcsm _ hsteps =>
      SepWPp.weaken_pre
        (sepConj_mono_left (Entails.pure_left fun _ => Entails.refl _))
        (hnext sf hsteps hpcm hrunm hspm hsp_alm hcsm
          (hInv.of_keepsFrozen hcrl hsteps.keepsFrozen)))
    hoom_false

theorem p2_call_nopanic_lscl_memInv_steps_frame_placed [LibsignalPlacement] {Φ : Memory → Prop}
    (hInv : StageP2DefsPlacedBudget.StageP2MemInv Φ) {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {R_pure : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcrl : Φ s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜R_pure⌝ ∗ T)) (hR : R_pure) (hP : P = T ∗ F)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      Φ sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  have hmid :
      SepWPp prog ret_pc s P
        (fun sm P_m => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ P_m = spec.post x s sm ∗ F)
        Qp := by
    refine ProofLib.SepWPp.call_wpp (x := x) (F := F) hcall hpc hrun hsp hlr ?_
      (fun sf code _ _ hex => by
        dsimp only [withLsCodeLoaded] at hex
        rw [hexit_false code sf] at hex
        exact not_satisfies_false_sepConj hex)
      (fun sf _ ⟨_, hpan⟩ => by
        dsimp only [withLsCodeLoaded] at hpan
        rw [hpan_false sf] at hpan
        exact (not_satisfies_false_sepConj hpan).elim)
      (fun sm hpcm hrunm hspm hcsm => ProofLib.SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sm _ _ hoom_post => by
        dsimp only [withLsCodeLoaded] at hoom_post
        rw [hoom_false sm] at hoom_post
        exact (not_satisfies_false_sepConj hoom_post).elim)
    intro R hm
    rw [hP, sepConj_assoc] at hm
    have hm0 : s.mem ⊨ spec.pre x s ∗ (F ∗ R) :=
      Arm64.Satisfies.mono
        (sepConj_mono_left (by rw [hspec]; exact Entails.pure_right hR (Entails.refl T))) hm
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨(hInv.toCodeRo hcrl).1, hm0⟩
  intro R hm hL
  obtain ⟨sm, hsteps, hout⟩ := hmid R hm hL
  rcases hout with ⟨hpcm, hrunm, _, hpost, hspm, hcsm, rfl⟩ | hpan | hoom_out
  · have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm (hInv.of_keepsFrozen hcrl hsteps.keepsFrozen)
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom_out)⟩

theorem p2_call_memInv_nopanic_steps_frame_sub5 [LibsignalPlacement] {Φ : Memory → Prop}
    (hInv : StageP2DefsPlacedBudget.StageP2MemInv Φ) {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcrl : Φ s.mem)
    (hcall : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (StageP2DefsPlacedBudget.withBobMemInv Φ spec)))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      Φ sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  have hmid :
      SepWPp prog ret_pc s P
        (fun sm P_m => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ P_m = spec.post x s sm ∗ F)
        Qp := by
    refine ProofLib.SepWPp.call_wpp (x := x) (F := F) hcall hpc hrun hsp hlr ?_
      (fun sf code _ _ hex => by
        dsimp only [withLsCodeRoLoaded, StageP2DefsPlacedBudget.withBobMemInv] at hex
        rw [hexit_false code sf] at hex
        exact not_satisfies_false_sepConj hex)
      (fun sf _ ⟨_, hpan⟩ => by
        dsimp only [withLsCodeRoLoaded, StageP2DefsPlacedBudget.withBobMemInv] at hpan
        rw [hpan_false sf] at hpan
        exact (not_satisfies_false_sepConj hpan).elim)
      (fun sm hpcm hrunm hspm hcsm => ProofLib.SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sm _ _ hoom_post => by
        dsimp only [withLsCodeRoLoaded, StageP2DefsPlacedBudget.withBobMemInv] at hoom_post
        rw [hoom_false sm] at hoom_post
        exact (not_satisfies_false_sepConj hoom_post).elim)
    intro R hm
    rw [hP, sepConj_assoc] at hm
    have hm0 : s.mem ⊨ spec.pre x s ∗ (F ∗ R) :=
      Arm64.Satisfies.mono
        (sepConj_mono_left (by rw [hspec]; exact Entails.pure_right hφ (Entails.refl T))) hm
    dsimp only [withLsCodeRoLoaded, StageP2DefsPlacedBudget.withBobMemInv]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hInv.toCodeRo hcrl, ?_⟩
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcrl, hm0⟩
  intro R hm hL
  obtain ⟨sm, hsteps, hout⟩ := hmid R hm hL
  rcases hout with ⟨hpcm, hrunm, _, hpost, hspm, hcsm, rfl⟩ | hpan | hoom_out
  · have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm (hInv.of_keepsFrozen hcrl hsteps.keepsFrozen)
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom_out)⟩

namespace Sub5Placed

def initializeBobSessionErrOwnedMemInvAtPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (Φ : Memory → Prop) (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) (stk : Nat) :
    Spec (InitBobCallGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl
    (StageP2DefsPlacedBudget.withBobMemInv Φ
      (initializeBobSessionErrOwnedAtInnerPlacedSpec P A lim AcceptErrEnv stk))

abbrev initializeBobSessionErrOwnedFrozenAtPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) (stk : Nat) :
    Spec (InitBobCallGhost × M.σ) :=
  initializeBobSessionErrOwnedMemInvAtPlacedSpec (CryptoVerification.LibsignalFrozen lsmpl)
    P A lim AcceptErrEnv stk

abbrev initializeBobSessionErrOwnedFrozen4KPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (InitBobCallGhost × M.σ) :=
  initializeBobSessionErrOwnedFrozenAtPlacedSpec P A lim AcceptErrEnv (768 + pqxdhEntryStackExt)

theorem of_cro_errOwned_at_placed [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop} {stk : Nat}
    (h : subroutine_ok prog entry
      (initializeBobSessionErrOwnedAtPlacedSpec P A lim AcceptErrEnv stk)) :
    subroutine_ok prog entry
      (initializeBobSessionErrOwnedMemInvAtPlacedSpec
        (LibsignalCodeRoLoaded lsmpl) P A lim AcceptErrEnv stk) := by
  refine subroutine_ok_map h ?_
  rintro ⟨g, st⟩ R s0 hpre
  refine ⟨(g, st), R, ?_, fun _ hpost => hpost⟩
  dsimp only [initializeBobSessionErrOwnedAtPlacedSpec,
    initializeBobSessionErrOwnedMemInvAtPlacedSpec,
    StageP2DefsPlacedBudget.withBobMemInv, withLsCodeRoLoaded] at hpre ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  exact hpre.2

theorem of_responderCore_errOwned_frozen_placed [LibsignalPlacement] {prog : Program}
    {entry : BitVec 64} {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (h : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget.initializeBobSessionErrOwnedFrozenPlacedSpec
          P A lim AcceptErrEnv))) :
    subroutine_ok prog entry
      (initializeBobSessionErrOwnedFrozenAtPlacedSpec P A lim AcceptErrEnv
        (768 + pqxdhEntryStack)) := by
  refine subroutine_ok_map h ?_
  rintro ⟨g, st⟩ R s0 hpre
  refine ⟨(g, st), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [initializeBobSessionErrOwnedFrozenAtPlacedSpec,
      initializeBobSessionErrOwnedMemInvAtPlacedSpec,
      StageP2DefsPlacedBudget.withBobMemInv,
      initializeBobSessionErrOwnedAtInnerPlacedSpec, withLsCodeRoLoaded,
      LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget.initializeBobSessionErrOwnedFrozenPlacedSpec,
      initializeBobSessionErrOwnedInnerPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsFrozen] at hpre ⊢
    exact hpre
  · dsimp only [initializeBobSessionErrOwnedFrozenAtPlacedSpec,
      initializeBobSessionErrOwnedMemInvAtPlacedSpec,
      StageP2DefsPlacedBudget.withBobMemInv,
      initializeBobSessionErrOwnedAtInnerPlacedSpec, withLsCodeRoLoaded,
      LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget.initializeBobSessionErrOwnedFrozenPlacedSpec,
      initializeBobSessionErrOwnedInnerPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsFrozen] at hpost ⊢
    simpa only [initBobErrOwnedAt_eq_kits] using hpost

theorem of_stageP2Defs_errOwned4K_frozen_placed [LibsignalPlacement] {prog : Program}
    {entry : BitVec 64} {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (h : subroutine_ok prog entry
      (StageP2DefsPlacedBudget.initializeBobSessionErrOwnedFrozen4KPlacedSpec
        P A lim AcceptErrEnv)) :
    subroutine_ok prog entry
      (initializeBobSessionErrOwnedFrozen4KPlacedSpec P A lim AcceptErrEnv) := by
  refine subroutine_ok_map h ?_
  rintro ⟨g, st⟩ R s0 hpre
  refine ⟨(g, st), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [initializeBobSessionErrOwnedFrozen4KPlacedSpec,
      initializeBobSessionErrOwnedFrozenAtPlacedSpec,
      initializeBobSessionErrOwnedMemInvAtPlacedSpec,
      StageP2DefsPlacedBudget.withBobMemInv,
      initializeBobSessionErrOwnedAtInnerPlacedSpec, withLsCodeRoLoaded,
      StageP2DefsPlacedBudget.initializeBobSessionErrOwnedFrozen4KPlacedSpec,
      StageP2DefsPlacedBudget.initializeBobSessionErrOwnedMemInv4KPlacedSpec,
      StageP2DefsPlacedBudget.initializeBobSessionErrOwned4KInnerPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded] at hpre ⊢
    have hcro : LibsignalCodeRoLoaded lsmpl s0.mem =
        CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem := rfl
    simpa only [hcro] using hpre
  · dsimp only [initializeBobSessionErrOwnedFrozen4KPlacedSpec,
      initializeBobSessionErrOwnedFrozenAtPlacedSpec,
      initializeBobSessionErrOwnedMemInvAtPlacedSpec,
      StageP2DefsPlacedBudget.withBobMemInv,
      initializeBobSessionErrOwnedAtInnerPlacedSpec, withLsCodeRoLoaded,
      StageP2DefsPlacedBudget.initializeBobSessionErrOwnedFrozen4KPlacedSpec,
      StageP2DefsPlacedBudget.initializeBobSessionErrOwnedMemInv4KPlacedSpec,
      StageP2DefsPlacedBudget.initializeBobSessionErrOwned4KInnerPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded] at hpost ⊢
    simpa only [initBobErrOwnedAt_eq_kits] using hpost

theorem initializeBobSessionErrOwnedMemInvAtPlacedSpec_mono_stack [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel} {Φ : Memory → Prop}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {stk₁ stk₂ : Nat} (hle : stk₁ ≤ stk₂) (hbound : stk₂ ≤ 2 ^ 64)
    (h : subroutine_ok prog entry
      (initializeBobSessionErrOwnedMemInvAtPlacedSpec Φ P A lim AcceptErrEnv stk₁)) :
    subroutine_ok prog entry
      (initializeBobSessionErrOwnedMemInvAtPlacedSpec Φ P A lim AcceptErrEnv stk₂) := by
  refine subroutine_ok_map h ?_
    (fun _ _ _ _ _ hp => not_satisfies_false_sepConj
      (by dsimp only [initializeBobSessionErrOwnedMemInvAtPlacedSpec,
            StageP2DefsPlacedBudget.withBobMemInv,
            initializeBobSessionErrOwnedAtInnerPlacedSpec, withLsCodeRoLoaded] at hp; exact hp))
    (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj
      (by dsimp only [initializeBobSessionErrOwnedMemInvAtPlacedSpec,
            StageP2DefsPlacedBudget.withBobMemInv,
            initializeBobSessionErrOwnedAtInnerPlacedSpec, withLsCodeRoLoaded] at he; exact he))
    (fun _ _ _ _ _ _ _ ho => False.elim (not_satisfies_false_sepConj
      (by dsimp only [initializeBobSessionErrOwnedMemInvAtPlacedSpec,
            StageP2DefsPlacedBudget.withBobMemInv,
            initializeBobSessionErrOwnedAtInnerPlacedSpec, withLsCodeRoLoaded] at ho; exact ho)))
  rintro ⟨g, st⟩ R s0 hpre
  let F_stk : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stk₂) (stk₂ - stk₁)
  dsimp only [initializeBobSessionErrOwnedMemInvAtPlacedSpec, withLsCodeRoLoaded,
    StageP2DefsPlacedBudget.withBobMemInv, initializeBobSessionErrOwnedAtInnerPlacedSpec] at hpre
  rw [p2_stackAt_split_of_le s0.sp stk₂ stk₁ hle hbound] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcro, hpre⟩
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hΦ, hpre⟩
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨(g, st), F_stk ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [initializeBobSessionErrOwnedMemInvAtPlacedSpec, withLsCodeRoLoaded,
      StageP2DefsPlacedBudget.withBobMemInv, initializeBobSessionErrOwnedAtInnerPlacedSpec, F_stk]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro, ?_⟩
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hΦ, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by sep_ac_rfl)⟩
  · dsimp only [initializeBobSessionErrOwnedMemInvAtPlacedSpec, withLsCodeRoLoaded,
      StageP2DefsPlacedBudget.withBobMemInv, initializeBobSessionErrOwnedAtInnerPlacedSpec,
      F_stk] at hpost ⊢
    rw [sepExists_sepConj_left] at hpost ⊢
    refine Satisfies.of_eq hpost ?_
    congr 1; funext evs
    rw [p2_stackAt_split_of_le s0.sp stk₂ stk₁ hle hbound]
    sep_ac_rfl

theorem of_responderCore_errOwned_to_4K_frozen_placed [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (h : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget.initializeBobSessionErrOwnedFrozenPlacedSpec
          P A lim AcceptErrEnv))) :
    subroutine_ok prog entry
      (initializeBobSessionErrOwnedFrozen4KPlacedSpec P A lim AcceptErrEnv) := by
  exact initializeBobSessionErrOwnedMemInvAtPlacedSpec_mono_stack (by decide) (by decide)
    (of_responderCore_errOwned_frozen_placed h)

theorem initializeBobSessionErrOwnedMemInvAtPlacedSpec_mono_env [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel} {Φ : Memory → Prop}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env₁ Env₂ : AcceptKeysInput → List AllocEvent → Prop} {stk : Nat}
    (hsub : ∀ inp evs, Env₁ inp evs → Env₂ inp evs)
    (h : subroutine_ok prog entry
      (initializeBobSessionErrOwnedMemInvAtPlacedSpec Φ P A lim Env₁ stk)) :
    subroutine_ok prog entry
      (initializeBobSessionErrOwnedMemInvAtPlacedSpec Φ P A lim Env₂ stk) := by
  refine subroutine_ok_map h ?_
    (fun _ _ _ _ _ hp => not_satisfies_false_sepConj
      (by dsimp only [initializeBobSessionErrOwnedMemInvAtPlacedSpec,
            StageP2DefsPlacedBudget.withBobMemInv,
            initializeBobSessionErrOwnedAtInnerPlacedSpec, withLsCodeRoLoaded] at hp; exact hp))
    (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj
      (by dsimp only [initializeBobSessionErrOwnedMemInvAtPlacedSpec,
            StageP2DefsPlacedBudget.withBobMemInv,
            initializeBobSessionErrOwnedAtInnerPlacedSpec, withLsCodeRoLoaded] at he; exact he))
    (fun _ _ _ _ _ _ _ ho => False.elim (not_satisfies_false_sepConj
      (by dsimp only [initializeBobSessionErrOwnedMemInvAtPlacedSpec,
            StageP2DefsPlacedBudget.withBobMemInv,
            initializeBobSessionErrOwnedAtInnerPlacedSpec, withLsCodeRoLoaded] at ho; exact ho)))
  rintro ⟨g, st⟩ R s0 hpre
  refine ⟨(g, st), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [initializeBobSessionErrOwnedMemInvAtPlacedSpec, withLsCodeRoLoaded,
      StageP2DefsPlacedBudget.withBobMemInv, initializeBobSessionErrOwnedAtInnerPlacedSpec] at hpre ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre ⊢
    refine ⟨hpre.1, ?_⟩
    have hpre2 := hpre.2
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre2 ⊢
    refine ⟨hpre2.1, ?_⟩
    have hpre3 := hpre2.2
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre3 ⊢
    rcases hpre3 with ⟨⟨h0, h1, h8, htr, hrep, hopk, hwell, hik, hspk, hacc, hfits⟩, hmem⟩
    exact ⟨⟨h0, h1, h8, htr, hrep, hopk, hwell, hik, hspk, hacc,
      fun evs hevs => hfits evs (hsub g.inp evs hevs)⟩, hmem⟩
  · dsimp only [initializeBobSessionErrOwnedMemInvAtPlacedSpec, withLsCodeRoLoaded,
      StageP2DefsPlacedBudget.withBobMemInv,
      initializeBobSessionErrOwnedAtInnerPlacedSpec] at hpost ⊢
    refine Arm64.Satisfies.mono (sepConj_mono_left ?_) hpost
    refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
    simp only [sepConj_assoc]
    exact Entails.pure_left fun ⟨htr, hev⟩ =>
      Entails.pure_right ⟨htr, hsub g.inp evs hev⟩ (Entails.refl _)

end Sub5Placed

export Sub5Placed (
  initializeBobSessionErrOwnedMemInvAtPlacedSpec
  initializeBobSessionErrOwnedFrozenAtPlacedSpec
  initializeBobSessionErrOwnedFrozen4KPlacedSpec
  of_cro_errOwned_at_placed
  of_responderCore_errOwned_frozen_placed
  of_stageP2Defs_errOwned4K_frozen_placed
  initializeBobSessionErrOwnedMemInvAtPlacedSpec_mono_stack
  of_responderCore_errOwned_to_4K_frozen_placed
  initializeBobSessionErrOwnedMemInvAtPlacedSpec_mono_env
)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget
