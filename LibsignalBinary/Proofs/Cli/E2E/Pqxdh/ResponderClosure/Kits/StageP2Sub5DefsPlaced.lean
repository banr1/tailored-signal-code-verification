/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Qpan
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsAPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2bAux

/-!
# Relocatable Stage P2 Substage P2.5 V1 Bundle and Combinators

Defines placed `StageP2MemInv` sequencing/call combinators and stack-parameterized
`initializeBobSessionErrOwned` contracts (`Sub5Placed`) on Block `518`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue)

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

/-- Bind a `SepWPp` segment ending at `mid` into a `Qp` continuation, threading
`StoreKit.LibsignalCodeRoLoaded lsmpl`. -/
theorem p2_bind_loaded_cro_sub5_qpan [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s0 s : State} {P : SepProp} {Qm post Qp : State → SepProp → Prop}
    (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWPp prog mid s P Qm (PanicOomProp s0))
    (h2 : ∀ sm Pm, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → Qm sm Pm →
      SepWPp prog target sm Pm post Qp) :
    SepWPp prog target s P post Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hQ⟩ | ⟨hp, Pm, hmm, hqp⟩ | hoom⟩ := h1 R hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      h2 sm Pm hsteps hpcm hrunm (hCode.of_keepsFrozen hsteps.keepsFrozen) hQ
        R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hp, Pm, hmm, hpan sm Pm hqp⟩)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

/-- Bind a `SepWP` basic block into a `SepWPp` continuation, threading `LibsignalCodeRoLoaded`. -/
theorem p2_bind_sepWP_steps_cro_sub5_qpan [LibsignalPlacement] {prog : Program}
    {mid ret : BitVec 64} {s : State} {P P_seg F P_seg_post : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hseg : SepWP prog mid s P_seg (fun sm P_m => (P_m ⊢ P_seg_post) ∧ Q_regs sm))
    (hP : P = P_seg ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_seg_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  p2_bind_sepWP_qp_frame_placed hCode hseg hP hnext

/-- Bind a `SepWPp` stage under `PanicOomProp s0` into a `Qp` continuation, threading
`StoreKit.LibsignalCodeRoLoaded lsmpl`. -/
theorem p2_bind_sepWPp_cro_sub5_qpan [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s0 s : State} {P P_stage F : SepProp} {P_stage_post : State → SepProp}
    {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post sm) ∧ Q_regs sm)
      (PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_stage_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  p2_bind_sepWPp_oom_frame_qpan hpan hstage hP fun sm hsteps hpcm hrunm hregs =>
    hnext sm hsteps hpcm hrunm (hCode.of_keepsFrozen hsteps.keepsFrozen) hregs

/-- Call a `StoreKit.withLsRoCl lsmpl spec` subroutine whose `onPanic` entails OOM, threading
`StoreKit.LibsignalCodeRoLoaded lsmpl` into a `Qp` continuation. -/
theorem p2_call_oom_rocl_sub5_qpan [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    {P P_spec F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpan_qp : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s0.trace <+: s.trace)
    (hcall : subroutine_ok prog entry (StoreKit.withLsRoCl lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : P_spec ⊢ spec.pre x s)
    (hP : P = P_spec ∗ F)
    (hpan : ∀ sf, spec.onPanic x s sf ⊢ ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by
      intro _ _; repeat (first | simp only [StoreKit.withLsLogOff] | simp only [withLogOff] | simp only [withEnvPre]); rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro _; repeat (first | simp only [StoreKit.withLsLogOff] | simp only [withLogOff] | simp only [withEnvPre]); rfl) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  have hm0 : s.mem ⊨ spec.pre x s ∗ (F ∗ R) :=
    Arm64.Satisfies.mono (sepConj_mono_left hpre) hm
  have hm' : s.mem ⊨ (StoreKit.withLsRoCl lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [StoreKit.withLsRoCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcrl, hm0⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpanm, hpost⟩ |
    ⟨code, _, hpost⟩ | ⟨_, _hoom_post⟩
  rotate_right
  · dsimp only [StoreKit.withLsRoCl] at _hoom_post
    rw [hoom_false] at _hoom_post
    exact (not_satisfies_false_sepConj _hoom_post).elim
  · dsimp only [StoreKit.withLsRoCl] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hcrl', hpost⟩ := hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm hcrl' R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [StoreKit.withLsRoCl] at hpost
    have hpost' : sm.mem ⊨ ((⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap) ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left (hpan sm)) hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpanm,
      (⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap) ∗ F, hpost',
      hpan_qp sm _ (p2_allowPanic_oom_of_trace_prefix htr)⟩)⟩
  · dsimp only [StoreKit.withLsRoCl] at hpost
    rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

/-- Call a `StoreKit.withLsCodeRoLoaded lsmpl spec` subroutine whose `onPanic` equals OOM,
threading `StoreKit.LibsignalCodeRoLoaded lsmpl` into a `Qp` continuation. -/
theorem p2_call_cro_oom_steps_frame_sub5_qpan [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpan_qp : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s0.trace <+: s.trace)
    (hcall : subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_eq : ∀ sf, spec.onPanic x s sf =
      (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  p2_call_oom_rocl_sub5_qpan hpan_qp hcrl htr
    (StoreKit.subroutine_ok_rocl_of_withLsCodeRoLoaded hcall)
    hpc hrun hsp hlr
    (by rw [hspec]; exact Entails.pure_right hφ (Entails.refl T))
    hP
    (fun sf => by rw [hpan_eq sf]; exact Entails.refl _)
    hnext hexit_false hoom_false

theorem p2_bind_loaded_memInv_sub5_qpan [LibsignalPlacement] {Φ : Memory → Prop}
    (hInv : StageP2MemInv Φ) {prog : Program} {mid target : BitVec 64}
    {s0 s : State} {P : SepProp} {Qm post Qp : State → SepProp → Prop}
    (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (hΦ : Φ s.mem)
    (h1 : SepWPp prog mid s P Qm (PanicOomProp s0))
    (h2 : ∀ sm Pm, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Φ sm.mem → Qm sm Pm → SepWPp prog target sm Pm post Qp) :
    SepWPp prog target s P post Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hQ⟩ | ⟨hp, Pm, hmm, hqp⟩ | hoom⟩ := h1 R hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      h2 sm Pm hsteps hpcm hrunm (hInv.of_keepsFrozen hΦ hsteps.keepsFrozen) hQ
        R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hp, Pm, hmm, hpan sm Pm hqp⟩)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem p2_bind_sepWP_steps_memInv_sub5_qpan [LibsignalPlacement] {Φ : Memory → Prop}
    (hInv : StageP2MemInv Φ) {prog : Program}
    {mid ret : BitVec 64} {s : State} {P P_seg F P_seg_post : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hΦ : Φ s.mem)
    (hseg : SepWP prog mid s P_seg (fun sm P_m => (P_m ⊢ P_seg_post) ∧ Q_regs sm))
    (hP : P = P_seg ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Φ sm.mem → Q_regs sm → SepWPp prog ret sm (P_seg_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  p2_bind_sepWP_qp_frame_placed (hInv.toCodeRo hΦ) hseg hP fun sm hsteps hpcm hrunm _ hregs =>
    hnext sm hsteps hpcm hrunm (hInv.of_keepsFrozen hΦ hsteps.keepsFrozen) hregs

theorem p2_call_oom_rocl_memInv_sub5_qpan [LibsignalPlacement] {Φ : Memory → Prop}
    (hInv : StageP2MemInv Φ) {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    {P P_spec F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpan_qp : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (hΦ : Φ s.mem)
    (htr : s0.trace <+: s.trace)
    (hcall : subroutine_ok prog entry (StoreKit.withLsRoCl lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : P_spec ⊢ spec.pre x s)
    (hP : P = P_spec ∗ F)
    (hpan : ∀ sf, spec.onPanic x s sf ⊢ ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      Φ sf.mem → SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by
      intro _ _; repeat (first | simp only [StoreKit.withLsLogOff] | simp only [withLogOff] | simp only [withEnvPre]); rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro _; repeat (first | simp only [StoreKit.withLsLogOff] | simp only [withLogOff] | simp only [withEnvPre]); rfl) :
    SepWPp prog ret s P Q Qp :=
  p2_call_oom_rocl_sub5_qpan hpan_qp (hInv.toCodeRo hΦ) htr hcall hpc hrun hsp hlr hpre hP hpan
    (fun sf hsteps hpcm hrunm hspm hspal hcsm _ =>
      hnext sf hsteps hpcm hrunm hspm hspal hcsm (hInv.of_keepsFrozen hΦ hsteps.keepsFrozen))
    hexit_false hoom_false

/-- Call a `withBobMemInv Φ spec` subroutine whose `onPanic` equals OOM, threading `Φ` via
`StageP2MemInv Φ` into a `Qp` continuation. -/
theorem p2_call_memInv_oom_steps_frame_sub5_qpan [LibsignalPlacement] {Φ : Memory → Prop}
    (hInv : StageP2MemInv Φ) {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpan_qp : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (hΦ : Φ s.mem)
    (htr : s0.trace <+: s.trace)
    (hcall : subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded lsmpl (withBobMemInv Φ spec)))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_eq : ∀ sf, spec.onPanic x s sf =
      (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      Φ sf.mem → SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  have hm0 : s.mem ⊨ spec.pre x s ∗ (F ∗ R) :=
    Arm64.Satisfies.mono (sepConj_mono_left (by rw [hspec]; exact Entails.pure_right hφ (Entails.refl T))) hm
  have hm' : s.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (withBobMemInv Φ spec)).pre x s ∗ (F ∗ R) := by
    dsimp only [StoreKit.withLsCodeRoLoaded, withBobMemInv]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hInv.toCodeRo hΦ, ?_⟩
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hΦ, hm0⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpanm, hpost⟩ |
    ⟨code, _, hpost⟩ | ⟨_, _hoom_post⟩
  rotate_right
  · dsimp only [StoreKit.withLsCodeRoLoaded, withBobMemInv] at _hoom_post
    rw [hoom_false] at _hoom_post
    exact (not_satisfies_false_sepConj _hoom_post).elim
  · dsimp only [StoreKit.withLsCodeRoLoaded, withBobMemInv] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm (hInv.of_keepsFrozen hΦ hsteps.keepsFrozen)
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [StoreKit.withLsCodeRoLoaded, withBobMemInv] at hpost
    rw [hpan_eq sm, ← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpanm,
      (⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap) ∗ F, hpost,
      hpan_qp sm _ (p2_allowPanic_oom_of_trace_prefix htr)⟩)⟩
  · dsimp only [StoreKit.withLsCodeRoLoaded, withBobMemInv] at hpost
    rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

theorem isSameAccountDistinctSpec_to_at_placed [LibsignalPlacement] {prog : Program}
    {entry : BitVec 64} {A : RustAlloc} {parse : UuidParser}
    (h : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A parse))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (isSameAccountDistinctAtSpec A parse isSameAccountDistinctStack)) := by
  refine subroutine_ok_map h ?_
  rintro ⟨lIkA, lIk, locA, loc, rIkA, rIk, remA, rem⟩ R s0 hpre
  dsimp only [withLsCodeLoaded, isSameAccountDistinctAtSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨({ localIkA := lIkA, localIk := lIk, locA := locA, loc := loc,
             remoteIkA := rIkA, remoteIk := rIk, remA := remA, rem := rem } :
             IsSameAccountDistinctGhost), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [withLsCodeLoaded, isSameAccountDistinctSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [withLsCodeLoaded, isSameAccountDistinctSpec, isSameAccountDistinctAtSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, Satisfies.of_eq hpost.2 (by ac_rfl)⟩

theorem isSameAccountDistinctSpecExt_to_at_placed [LibsignalPlacement] {prog : Program}
    {entry : BitVec 64} {A : RustAlloc} {parse : UuidParser}
    (h : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctSpecExt A parse))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        (isSameAccountDistinctAtSpec A parse
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt)) :=
  h

theorem pqxdhAcceptErrPayloadAt_eq_kits (A : RustAlloc) (errTag w2 w3 w4 : BitVec 64) :
    ResponderCore.pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 =
      Kits.pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 := by
  unfold ResponderCore.pqxdhAcceptErrPayloadAt Kits.pqxdhAcceptErrPayloadAt
  rfl

theorem initBobErrOwnedAt_eq_kits (A : RustAlloc) (outPtr : BitVec 64) :
    ResponderCore.initBobErrOwnedAt A outPtr = Kits.initBobErrOwnedAt A outPtr := by
  unfold ResponderCore.initBobErrOwnedAt Kits.initBobErrOwnedAt
  simp only [pqxdhAcceptErrPayloadAt_eq_kits]

namespace Sub5Placed

/-- Stack-parameterized placed `initializeBobSessionErrOwned` inner contract (`Kits.initBobErrOwnedAt`). -/
def initializeBobSessionErrOwnedAtInnerPlacedSpec [LibsignalPlacement]
    (P : Primitives) (A : RustAlloc) (stk : Nat) : Spec InitBobCallGhost where
  pre := fun (g : InitBobCallGhost) s =>
    ⌜s.readReg64 .x0 = g.argPtr ∧
      s.readReg64 .x1 = g.ratchetKeyPairPtr ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inp.trustedPeer = true ∧
      g.inp.replayOk = true ∧
      g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧
      WellSizedAcceptKeysInput g.inp ∧
      g.ikBPk.length = 32 ∧
      g.spkBPk.length = 32 ∧
      Model.acceptKeys P g.inp = none⌝ ∗
    bobParamsFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
      g.inp g.ikBPk g.spkBPk g.sameAccountByte ∗
    memRegion g.outPtr 344 ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗
    stackAt s.sp stk ∗
    A.pool
  post := fun (g : InitBobCallGhost) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    bobParamsFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
      g.inp g.ikBPk g.spkBPk g.sameAccountByte ∗
    (Kits.initBobErrOwnedAt A g.outPtr ∗ anyHeap) ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗
    stackAt s0.sp stk ∗
    A.pool
  onPanic := rustPanicOnOomPlaced

def initializeBobSessionErrOwnedAtPlacedSpec [LibsignalPlacement]
    (P : Primitives) (A : RustAlloc) (stk : Nat) : Spec InitBobCallGhost :=
  StoreKit.withLsCodeRoLoaded lsmpl (initializeBobSessionErrOwnedAtInnerPlacedSpec P A stk)

abbrev initializeBobSessionErrOwned4KPlacedSpec [LibsignalPlacement]
    (P : Primitives) (A : RustAlloc) : Spec InitBobCallGhost :=
  initializeBobSessionErrOwnedAtPlacedSpec P A (768 + Initiator.pqxdhEntryStackExt)

theorem of_responderCore_errOwned_placed [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {P : Primitives} {A : RustAlloc}
    (h : subroutine_ok prog entry (ResponderCore.initializeBobSessionErrOwnedPlacedSpec P A)) :
    subroutine_ok prog entry
      (initializeBobSessionErrOwnedAtPlacedSpec P A (768 + pqxdhEntryStack)) := by
  refine subroutine_ok_map_panic h ?_
    (fun _ _ _ _ _ _ he => by
      dsimp only [ResponderCore.initializeBobSessionErrOwnedPlacedSpec,
        ResponderCore.initializeBobSessionErrOwnedInnerPlacedSpec,
        LibsignalTripleRatchet.withLsCodeRoLoaded] at he
      exact not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ _ ho => by
      dsimp only [ResponderCore.initializeBobSessionErrOwnedPlacedSpec,
        ResponderCore.initializeBobSessionErrOwnedInnerPlacedSpec,
        LibsignalTripleRatchet.withLsCodeRoLoaded] at ho
      exact (not_satisfies_false_sepConj ho).elim)
  intro g R s0 hpre
  refine ⟨g, R, ?_, fun sf hpost => ?_, fun sf hpan => hpan⟩
  · dsimp only [initializeBobSessionErrOwnedAtPlacedSpec,
      initializeBobSessionErrOwnedAtInnerPlacedSpec, StoreKit.withLsCodeRoLoaded,
      ResponderCore.initializeBobSessionErrOwnedPlacedSpec,
      ResponderCore.initializeBobSessionErrOwnedInnerPlacedSpec,
      LibsignalTripleRatchet.withLsCodeRoLoaded] at hpre ⊢
    have hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem =
        LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem := rfl
    simpa only [hcro] using hpre
  · dsimp only [initializeBobSessionErrOwnedAtPlacedSpec,
      initializeBobSessionErrOwnedAtInnerPlacedSpec, StoreKit.withLsCodeRoLoaded,
      ResponderCore.initializeBobSessionErrOwnedPlacedSpec,
      ResponderCore.initializeBobSessionErrOwnedInnerPlacedSpec,
      LibsignalTripleRatchet.withLsCodeRoLoaded] at hpost ⊢
    simpa only [initBobErrOwnedAt_eq_kits] using hpost

theorem initializeBobSessionErrOwnedAtPlacedSpec_mono_stack [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {P : Primitives} {A : RustAlloc}
    {stk₁ stk₂ : Nat} (hle : stk₁ ≤ stk₂) (hbound : stk₂ ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (initializeBobSessionErrOwnedAtPlacedSpec P A stk₁)) :
    subroutine_ok prog entry (initializeBobSessionErrOwnedAtPlacedSpec P A stk₂) := by
  refine subroutine_ok_map_panic h ?_
    (fun _ _ _ _ _ _ he => by
      dsimp only [initializeBobSessionErrOwnedAtPlacedSpec,
        initializeBobSessionErrOwnedAtInnerPlacedSpec, StoreKit.withLsCodeRoLoaded] at he
      exact not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ _ ho => by
      dsimp only [initializeBobSessionErrOwnedAtPlacedSpec,
        initializeBobSessionErrOwnedAtInnerPlacedSpec, StoreKit.withLsCodeRoLoaded] at ho
      exact (not_satisfies_false_sepConj ho).elim)
  intro g R s0 hpre
  let F_stk : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk₂) (stk₂ - stk₁)
  dsimp only [initializeBobSessionErrOwnedAtPlacedSpec,
    initializeBobSessionErrOwnedAtInnerPlacedSpec, StoreKit.withLsCodeRoLoaded] at hpre
  rw [p2_stackAt_split_of_le s0.sp stk₂ stk₁ hle hbound] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨g, F_stk ∗ R, ?_, fun sf hpost => ?_, fun sf hpan => ?_⟩
  · dsimp only [initializeBobSessionErrOwnedAtPlacedSpec,
      initializeBobSessionErrOwnedAtInnerPlacedSpec, StoreKit.withLsCodeRoLoaded, F_stk]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [initializeBobSessionErrOwnedAtPlacedSpec,
      initializeBobSessionErrOwnedAtInnerPlacedSpec, StoreKit.withLsCodeRoLoaded, F_stk] at hpost ⊢
    rw [p2_stackAt_split_of_le s0.sp stk₂ stk₁ hle hbound]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, Satisfies.of_eq hpost.2 (by ac_rfl)⟩
  · dsimp only [initializeBobSessionErrOwnedAtPlacedSpec,
      initializeBobSessionErrOwnedAtInnerPlacedSpec, StoreKit.withLsCodeRoLoaded,
      rustPanicOnOomPlaced, F_stk] at hpan ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpan ⊢
    rcases hpan with ⟨hp, hmem_pan⟩
    exact ⟨hp, Arm64.Satisfies.mono (Entails.trans
      (Entails.of_eq (show anyHeap ∗ (memRegion _ _ ∗ R) =
        (anyHeap ∗ memRegion _ _) ∗ R by ac_rfl))
      (sepConj_mono_left (entails_anyHeap _))) hmem_pan⟩

theorem of_responderCore_errOwned_to_4K_placed [LibsignalPlacement] {prog : Program}
    {entry : BitVec 64} {P : Primitives} {A : RustAlloc}
    (h : subroutine_ok prog entry (ResponderCore.initializeBobSessionErrOwnedPlacedSpec P A)) :
    subroutine_ok prog entry (initializeBobSessionErrOwned4KPlacedSpec P A) :=
  initializeBobSessionErrOwnedAtPlacedSpec_mono_stack (by decide) (by decide)
    (of_responderCore_errOwned_placed h)

def initializeBobSessionErrOwnedMemInvAtPlacedSpec [LibsignalPlacement]
    (Φ : Memory → Prop) (P : Primitives) (A : RustAlloc) (stk : Nat) : Spec InitBobCallGhost :=
  StoreKit.withLsCodeRoLoaded lsmpl
    (withBobMemInv Φ (initializeBobSessionErrOwnedAtInnerPlacedSpec P A stk))

abbrev initializeBobSessionErrOwnedFrozenAtPlacedSpec [LibsignalPlacement]
    (P : Primitives) (A : RustAlloc) (stk : Nat) : Spec InitBobCallGhost :=
  initializeBobSessionErrOwnedMemInvAtPlacedSpec (LibsignalFrozen lsmpl) P A stk

abbrev initializeBobSessionErrOwnedFrozen4KPlacedSpec [LibsignalPlacement]
    (P : Primitives) (A : RustAlloc) : Spec InitBobCallGhost :=
  StoreKit.withLsCodeRoLoaded lsmpl
    (withBobMemInv (LibsignalFrozen lsmpl)
      (initializeBobSessionErrOwnedAtInnerPlacedSpec P A (768 + Initiator.pqxdhEntryStackExt)))

theorem of_responderCore_errOwned_frozen_placed [LibsignalPlacement] {prog : Program}
    {entry : BitVec 64} {P : Primitives} {A : RustAlloc}
    (h : subroutine_ok prog entry
      (StoreKit.withLsCodeRoLoaded lsmpl
        (ResponderCore.initializeBobSessionErrOwnedFrozenPlacedSpec P A))) :
    subroutine_ok prog entry
      (initializeBobSessionErrOwnedFrozenAtPlacedSpec P A (768 + pqxdhEntryStack)) := by
  refine subroutine_ok_map_panic h ?_
    (fun _ _ _ _ _ _ he => by
      dsimp only [StoreKit.withLsCodeRoLoaded,
        ResponderCore.initializeBobSessionErrOwnedFrozenPlacedSpec,
        ResponderCore.initializeBobSessionErrOwnedInnerPlacedSpec,
        withLsFrozen] at he
      exact not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ _ ho => by
      dsimp only [StoreKit.withLsCodeRoLoaded,
        ResponderCore.initializeBobSessionErrOwnedFrozenPlacedSpec,
        ResponderCore.initializeBobSessionErrOwnedInnerPlacedSpec,
        withLsFrozen] at ho
      exact (not_satisfies_false_sepConj ho).elim)
  intro g R s0 hpre
  refine ⟨g, R, ?_, fun sf hpost => ?_, fun sf hpan => hpan⟩
  · dsimp only [initializeBobSessionErrOwnedFrozenAtPlacedSpec,
      initializeBobSessionErrOwnedMemInvAtPlacedSpec, StoreKit.withLsCodeRoLoaded, withBobMemInv,
      initializeBobSessionErrOwnedAtInnerPlacedSpec,
      ResponderCore.initializeBobSessionErrOwnedFrozenPlacedSpec,
      ResponderCore.initializeBobSessionErrOwnedInnerPlacedSpec,
      withLsFrozen] at hpre ⊢
    exact hpre
  · dsimp only [initializeBobSessionErrOwnedFrozenAtPlacedSpec,
      initializeBobSessionErrOwnedMemInvAtPlacedSpec, StoreKit.withLsCodeRoLoaded, withBobMemInv,
      initializeBobSessionErrOwnedAtInnerPlacedSpec,
      ResponderCore.initializeBobSessionErrOwnedFrozenPlacedSpec,
      ResponderCore.initializeBobSessionErrOwnedInnerPlacedSpec,
      withLsFrozen] at hpost ⊢
    simpa only [initBobErrOwnedAt_eq_kits] using hpost

theorem initializeBobSessionErrOwnedMemInvAtPlacedSpec_mono_stack [LibsignalPlacement]
    {Φ : Memory → Prop} {prog : Program} {entry : BitVec 64} {P : Primitives} {A : RustAlloc}
    {stk₁ stk₂ : Nat} (hle : stk₁ ≤ stk₂) (hbound : stk₂ ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (initializeBobSessionErrOwnedMemInvAtPlacedSpec Φ P A stk₁)) :
    subroutine_ok prog entry (initializeBobSessionErrOwnedMemInvAtPlacedSpec Φ P A stk₂) := by
  refine subroutine_ok_map_panic h ?_
    (fun _ _ _ _ _ _ he => by
      dsimp only [initializeBobSessionErrOwnedMemInvAtPlacedSpec, StoreKit.withLsCodeRoLoaded,
        withBobMemInv, initializeBobSessionErrOwnedAtInnerPlacedSpec] at he
      exact not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ _ ho => by
      dsimp only [initializeBobSessionErrOwnedMemInvAtPlacedSpec, StoreKit.withLsCodeRoLoaded,
        withBobMemInv, initializeBobSessionErrOwnedAtInnerPlacedSpec] at ho
      exact (not_satisfies_false_sepConj ho).elim)
  intro g R s0 hpre
  let F_stk : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk₂) (stk₂ - stk₁)
  dsimp only [initializeBobSessionErrOwnedMemInvAtPlacedSpec, StoreKit.withLsCodeRoLoaded,
    withBobMemInv, initializeBobSessionErrOwnedAtInnerPlacedSpec] at hpre
  rw [p2_stackAt_split_of_le s0.sp stk₂ stk₁ hle hbound] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcro, hpre⟩
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hΦ, hpre⟩
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨g, F_stk ∗ R, ?_, fun sf hpost => ?_, fun sf hpan => ?_⟩
  · dsimp only [initializeBobSessionErrOwnedMemInvAtPlacedSpec, StoreKit.withLsCodeRoLoaded,
      withBobMemInv, initializeBobSessionErrOwnedAtInnerPlacedSpec, F_stk]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro, ?_⟩
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hΦ, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [initializeBobSessionErrOwnedMemInvAtPlacedSpec, StoreKit.withLsCodeRoLoaded,
      withBobMemInv, initializeBobSessionErrOwnedAtInnerPlacedSpec, F_stk] at hpost ⊢
    rw [p2_stackAt_split_of_le s0.sp stk₂ stk₁ hle hbound]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, Satisfies.of_eq hpost.2 (by ac_rfl)⟩
  · dsimp only [initializeBobSessionErrOwnedMemInvAtPlacedSpec, StoreKit.withLsCodeRoLoaded,
      withBobMemInv, initializeBobSessionErrOwnedAtInnerPlacedSpec, rustPanicOnOomPlaced,
      F_stk] at hpan ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpan ⊢
    rcases hpan with ⟨hp, hmem_pan⟩
    exact ⟨hp, Arm64.Satisfies.mono (Entails.trans
      (Entails.of_eq (show anyHeap ∗ (memRegion _ _ ∗ R) =
        (anyHeap ∗ memRegion _ _) ∗ R by ac_rfl))
      (sepConj_mono_left (entails_anyHeap _))) hmem_pan⟩

theorem of_responderCore_errOwned_to_4K_frozen_placed [LibsignalPlacement] {prog : Program}
    {entry : BitVec 64} {P : Primitives} {A : RustAlloc}
    (h : subroutine_ok prog entry
      (StoreKit.withLsCodeRoLoaded lsmpl
        (ResponderCore.initializeBobSessionErrOwnedFrozenPlacedSpec P A))) :
    subroutine_ok prog entry (initializeBobSessionErrOwnedFrozen4KPlacedSpec P A) :=
  initializeBobSessionErrOwnedMemInvAtPlacedSpec_mono_stack (by decide) (by decide)
    (of_responderCore_errOwned_frozen_placed h)

end Sub5Placed

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
