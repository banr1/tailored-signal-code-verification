/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsAPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Qpan
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2bAux
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs

/-!
# Relocatable Stage P2 Substage P2.1 and Call Combinators

Provides placed `withLsRoCl` / `withLsCodeLoaded` OOM call combinators and proves placed Substage
P2.1 (`stageP2_sub1_kits_ext_placed` / `stageP2_sub1_kits_placed`, `+0x0868 → +0x0f14`) on
Block `518`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore hiding sessionRecordEmptyHeaderAt
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  protocolAddressAt decryptPrekeySavedRegsAt

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

/-! ## 1. Placed `cro_qpan` & `withLsRoCl` / `withLsCodeLoaded` OOM Call Combinators -/

abbrev p2_bind_sepWP_cro_frame_qpan := @p2_bind_sepWP_qp_frame_placed

theorem p2_bind_loaded_cro_qpan [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
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
      h2 sm Pm hsteps hpcm hrunm (hCode.of_keepsFrozen hsteps.keepsFrozen) hQ R hmm
        (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hp, Pm, hmm, hpan sm Pm hqp⟩)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem p2_bind_sepWPp_cro_frame_qpan [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
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

theorem p2_call_oom_rocl_steps_frame_qpan [LibsignalPlacement] {α : Type} {prog : Program}
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
      intro _ _; first | rfl | dsimp only [StoreKit.withLsLogOff, withLogOff, withEnvPre]; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro _; first | rfl | dsimp only [StoreKit.withLsLogOff, withLogOff, withEnvPre]; rfl) :
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

theorem p2_call_oom_rocl_steps_frame_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    {P P_spec F : SepProp} {Q : State → SepProp → Prop}
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
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (PanicOomProp s0))
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by
      intro _ _; first | rfl | dsimp only [StoreKit.withLsLogOff, withLogOff, withEnvPre]; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro _; first | rfl | dsimp only [StoreKit.withLsLogOff, withLogOff, withEnvPre]; rfl) :
    SepWPp prog ret s P Q (PanicOomProp s0) :=
  p2_call_oom_rocl_steps_frame_qpan (fun _ _ h => h) hcrl htr hcall hpc hrun hsp hlr hpre hP hpan
    hnext hexit_false hoom_false

theorem p2_call_oom_lscl_steps_frame_qpan [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    {P P_spec F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpan_qp : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s0.trace <+: s.trace)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
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
      intro _ _; first | rfl | dsimp only [StoreKit.withLsLogOff, withLogOff, withEnvPre]; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro _; first | rfl | dsimp only [StoreKit.withLsLogOff, withLogOff, withEnvPre]; rfl) :
    SepWPp prog ret s P Q Qp :=
  p2_call_oom_rocl_steps_frame_qpan hpan_qp hcrl htr
    (StoreKit.subroutine_ok_rocl_of_withLsCodeRoLoaded
      (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hcall))
    hpc hrun hsp hlr hpre hP hpan hnext hexit_false hoom_false

theorem p2_call_oom_lscl_steps_frame_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    {P P_spec F : SepProp} {Q : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s0.trace <+: s.trace)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : P_spec ⊢ spec.pre x s)
    (hP : P = P_spec ∗ F)
    (hpan : ∀ sf, spec.onPanic x s sf ⊢ ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (PanicOomProp s0))
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by
      intro _ _; first | rfl | dsimp only [StoreKit.withLsLogOff, withLogOff, withEnvPre]; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro _; first | rfl | dsimp only [StoreKit.withLsLogOff, withLogOff, withEnvPre]; rfl) :
    SepWPp prog ret s P Q (PanicOomProp s0) :=
  p2_call_oom_lscl_steps_frame_qpan (fun _ _ h => h) hcrl htr hcall hpc hrun hsp hlr hpre hP hpan
    hnext hexit_false hoom_false

theorem p2_spkGetShim_pre_intro_placed {A : RustAlloc}
    {spkKit : SignedPreKeyStoreSpec A 0#64} {x : PreKeyShimCall} {s : State}
    (hx0 : s.readReg64 .x0 = x.self) (hx1 : s.readReg32 .x1 = x.id) :
    A.pool ∗ stackAt s.sp spkKit.getShimStack ⊢
      (kitSpkGetShimSpec spkKit).pre x s := by
  dsimp only [kitSpkGetShimSpec]
  exact Entails.pure_right ⟨rfl, hx0, hx1⟩ (Entails.refl _)

theorem p2_spkGetPoll_pre_intro_placed {A : RustAlloc}
    {spkKit : SignedPreKeyStoreSpec A 0#64}
    {x : PreKeyPollCall} {st0 : spkKit.SpkState} {s : State}
    (henv : spkKit.envOk s.fs.files)
    (hx0 : s.readReg64 .x0 = x.fut) (hx8 : s.readReg64 .x8 = x.out)
    (hid : spkKit.idOk x.id) :
    spkKit.getBoxAt x.fut x.self x.id 0#8 ∗ spkKit.storeAt x.self st0 ∗
      memRegion x.out 88 ∗ A.pool ∗ stackAt s.sp spkKit.getPollStack ⊢
        (kitSpkGetPollSpecE spkKit).pre (x, st0) s := by
  dsimp only [kitSpkGetPollSpecE, withEnvPre, kitSpkGetPollSpec]
  exact Entails.pure_right henv (Entails.pure_right ⟨rfl, hx0, hx8, hid⟩ (Entails.refl _))

theorem p2_kpkGetShim_pre_intro_placed {A : RustAlloc}
    {kpkKit : KyberPreKeyStoreSpec A 0#64} {x : PreKeyShimCall} {s : State}
    (hx0 : s.readReg64 .x0 = x.self) (hx1 : s.readReg32 .x1 = x.id) :
    A.pool ∗ stackAt s.sp kpkKit.getShimStack ⊢
      (kitKpkGetShimSpec kpkKit).pre x s := by
  dsimp only [kitKpkGetShimSpec]
  exact Entails.pure_right ⟨rfl, hx0, hx1⟩ (Entails.refl _)

theorem p2_rocl_of_lscl_ro [LibsignalPlacement] {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α}
    (h : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (LibsignalTripleRatchet.Getters.withLsRoLoaded lsmpl spec))) :
    subroutine_ok prog entry (StoreKit.withLsRoCl lsmpl spec) := by
  refine StoreKit.subroutine_ok_rocl_of_withLsCodeRoLoaded ?_
  refine subroutine_ok_mono h (fun x R s0 hp => ?_) (fun _ _ _ _ hq => hq)
  obtain ⟨hcrl, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hp
  dsimp only [withLsCodeLoaded, LibsignalTripleRatchet.Getters.withLsRoLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  refine ⟨hcrl.1, ?_⟩
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hcrl.2, hpre⟩

theorem promoteStateEmptySpec_lscl_to_4K [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl promoteStateEmptySpec)) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl promoteStateEmpty4KSpec) := by
  refine subroutine_ok_map h ?_
  rintro ⟨recPtr, srcPtr, bs⟩ R s0 hpre
  dsimp only [withLsCodeLoaded, promoteStateEmpty4KSpec] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl, hpre⟩ := hpre
  rw [stackAt_promote_state_eq s0.sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨(recPtr, srcPtr, bs), stackAt (s0.sp - 96#64) (allocHookStack - 96) ∗ R,
    ?_, fun sf hpost => ?_⟩
  · dsimp only [withLsCodeLoaded, promoteStateEmptySpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [withLsCodeLoaded, promoteStateEmptySpec, promoteStateEmpty4KSpec] at hpost ⊢
    rw [stackAt_promote_state_eq s0.sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, Satisfies.of_eq hpost.2 (by ac_rfl)⟩

theorem isSameAccountDistinctSpec_lscl_to_ext [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {A : RustAlloc} {parse : UuidParser}
    (h : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (WireEntries.isSameAccountDistinctSpec A parse))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctSpecExt A parse)) := by
  refine subroutine_ok_map h ?_
  rintro ⟨lIkA, lIk, locA, loc, rIkA, rIk, remA, rem⟩ R s0 hpre
  dsimp only [withLsCodeLoaded,
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctSpecExt] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl, hpre⟩ := hpre
  rw [p2_stackAt_split_of_le s0.sp
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt
    WireEntries.isSameAccountDistinctStack (by decide) (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨({ localIkA := lIkA, localIk := lIk, locA := locA, loc := loc,
             remoteIkA := rIkA, remoteIk := rIk, remA := remA, rem := rem } :
            WireEntries.IsSameAccountDistinctGhost),
    memRegion (s0.sp - BitVec.ofNat 64
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt -
        WireEntries.isSameAccountDistinctStack) ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [withLsCodeLoaded, WireEntries.isSameAccountDistinctSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [withLsCodeLoaded, WireEntries.isSameAccountDistinctSpec,
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctSpecExt] at hpost ⊢
    rw [p2_stackAt_split_of_le s0.sp
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt
      WireEntries.isSameAccountDistinctStack (by decide) (by decide)]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, Satisfies.of_eq hpost.2 (by ac_rfl)⟩

theorem StageP2PureCalleesPlaced.to_4K [LibsignalPlacement] {P : Primitives} {A : RustAlloc}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (h : StageP2PureCalleesPlaced P A F ext) :
    StageP2PureCalleesPlaced4K P A F ext where
  publicKeySerialize := h.publicKeySerialize
  promoteMatchingSessionEmpty := h.promoteMatchingSessionEmpty
  curveKeyPairSerde := h.curveKeyPairSerde
  kemKeyPairSerde := h.kemKeyPairSerde
  preKeyRecordKeyPair := h.preKeyRecordKeyPair
  dropSpe2 := h.dropSpe2
  isSameAccount := isSameAccountDistinctSpec_lscl_to_ext h.isSameAccount
  initializeBobV1 := h.initializeBobV1.to_4K
  initializeBobErr := initializeBobSessionErrPlacedSpec_to_4K h.initializeBobErr
  promoteStateEmpty := promoteStateEmptySpec_lscl_to_4K h.promoteStateEmpty
  dropProcessPrekeyImplState1 := h.dropProcessPrekeyImplState1
  dropSessionStructure3 := h.dropSessionStructure3

/-! ## 2. Substage P2.1 (`+0x0868 -> +0x0f14`) -/

set_option maxHeartbeats 1200000 in
/-- Placed Kit-generic Substage P2.1 (`+0x0868 -> +0x0f14`) on `stageP1ProgPlaced ext`:
Serializes `baseKey` (`PublicKey::serialize`), calls `SessionRecord::promote_matching_session`
on an empty `SessionRecord`, deallocates the serialized key buffer, and calls `spkKit.getShim`. -/
theorem stageP2_sub1_kits_ext_placed [LibsignalPlacement]
    {A : RustAlloc}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A ext)
    (hPure : StageP2BaseCalleesPlaced4K A ext)
    (spkKit : SignedPreKeyStoreSpec A 0#64)
    (hspkOk : SignedPreKeyStoreKitPlacedOk spkKit ext)
    (stk : Nat)
    (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_shim : spkKit.getShimStack ≤ stk)
    (hstk_lt : stk ≤ 2 ^ 64)
    (s0 s : State)
    (coroPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
     spkStorePtr kyberStorePtr kyberStoreVt : BitVec 64)
    (baseKey : PublicKey) (spkId : BitVec 32) (b_4f1 : BitVec 8)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = stageP1EntryPlaced + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx8 : s.readReg64 .x8 = kyberStorePtr)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr)
    (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr)
    (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkKit.spk_vt) :
    SepWPp (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0xf14#64) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
       ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
       ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
       memRegion (s.sp + 0x3e0#64) 9 ∗
       ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + spkKit.getShimOff)) ∗
       A.pool ∗
       stackAt s.sp stk)
      (fun sf P_f =>
        (P_f ⊢
          ∃∗ spkFutPtr : BitVec 64,
            ⌜sf.readReg64 .x0 = spkFutPtr ∧
              sf.readReg64 .x1 = 0#64 + spkKit.getFutVtOff ∧
              spkFutPtr ≠ 0#64 ∧
              spkFutPtr.toNat % 8 = 0⌝ ∗
            processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
              idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
              kyberStorePtr kyberStoreVt ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
            sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
            ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
            ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
            ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
            memRegion (s.sp + 0x3e0#64) 9 ∗
            ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + spkKit.getShimOff)) ∗
            A.live spkFutPtr spkKit.getBoxSize 8 ∗
            spkKit.getBoxAt spkFutPtr spkStorePtr spkId 0#8 ∗
            A.pool ∗
            stackAt s.sp stk) ∧
        sf.sp = s.sp ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x19 = coroPtr ∧
        sf.readReg64 .x22 = spkStorePtr ∧
        sf.readReg64 .x23 = 0#64 ∧
        sf.readReg64 .x24 = spkKit.spk_vt ∧
        sf.readReg64 .x25 = s.sp + 0x210#64 ∧
        sf.readReg64 .x26 = 33#64 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      (PanicOomProp s0) := by
  have hstep1 := p2_seg1a_ext_placed_wp ext s coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkKit.spk_vt kyberStorePtr kyberStoreVt b_4f1
    hpc hrun hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24
  refine p2_bind_sepWP_qp_frame_placed hCode hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, _, hx22_1, hx23_1, hx24_1, hx25_1, _, hx27_1,
    hx28_1, hx29_1, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have hstk_ser := p2_stackAt_split_of_le s.sp stk publicKeySerializeStack
    (Nat.le_trans p2_pkSerStack_le_pure hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_ser) (by sep_focus) ?_
  sep_norm
  refine p2_call_oom_lscl_steps_frame_placed
    (x := ⟨msgPtr + 0xa8#64, baseKey⟩)
    (P_spec := ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗ A.pool ∗
      stackAt s.sp publicKeySerializeStack)
    hCode1 (htr1 ▸ htr) hPure.publicKeySerialize hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [publicKeySerializeSpec]; rw [hsp1]; exact Entails.pure_right hx0_1 (Entails.refl _))
    (by sep_focus) (fun _ => Entails.refl _)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hCode2 => ?_)
  dsimp only [publicKeySerializeSpec]
  rcases hcs2 with ⟨hcs2_19, _, _, hcs2_22, hcs2_23, hcs2_24, hcs2_25, _, hcs2_27, hcs2_28,
    hcs2_29, hvregs2_1⟩
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hcs2_19.trans hx19_1
  have hx22_2 : s2.readReg64 .x22 = spkStorePtr := hcs2_22.trans hx22_1
  have hx23_2 : s2.readReg64 .x23 = coroPtr + 0xe0#64 := hcs2_23.trans hx23_1
  have hx24_2 : s2.readReg64 .x24 = spkKit.spk_vt := hcs2_24.trans hx24_1
  have hx25_2 : s2.readReg64 .x25 = 4#64 := hcs2_25.trans hx25_1
  have hx27_2 : s2.readReg64 .x27 = s.readReg64 .x27 := hcs2_27.trans hx27_1
  have hx28_2 : s2.readReg64 .x28 = s.readReg64 .x28 := hcs2_28.trans hx28_1
  have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hcs2_29.trans hx29_1
  rw [hsp1]
  sep_norm
  refine SepWPp.pure_elim fun ⟨hx1_2, htr2⟩ => ?_
  refine SepWPp.weaken_frame (boxU8Buf_pk_serialize_entails A (s2.readReg64 .x0) baseKey)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_ser.symm) (by sep_focus) ?_
  have hstep3 := p2_seg1b_ext_placed_wp ext s2 coroPtr (s2.readReg64 .x0) spkStorePtr
    spkKit.spk_vt hpc2 hrun2 rfl hx1_2 hx19_2 hx22_2 hx23_2 hx24_2 hx25_2
  rw [hsp2] at hstep3
  refine p2_bind_sepWP_qp_frame_placed hCode2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hCode3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3, htr3, hx0_3, _, _, _, hx8_3, hx19_3, hx21_3, hx22_3, _, hx24_3, _,
    hx26_3, hx27_3, hx28_3, hx29_3, hx30_3, hvregs3_2⟩
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
  have hstk_prom1 := p2_stackAt_split_of_le s.sp stk 1248
    (Nat.le_trans p2_prom1248_le_pure hstk_pure) hstk_lt
  have hstk_prom2 := stackAt_1248_promote_eq s.sp
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom1) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom2) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (memRegion_9_sp3e0_eq s.sp)) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine p2_call_nopanic_lscl_steps_frame_placed hCode3 hPure.promoteMatchingSessionEmpty
    hpc3 hrun3 hsp3_al hx30_3
    (x := (coroPtr + 0xe0#64, s.sp + 0x3e0#64))
    (R_pure := s3.readReg64 .x0 = coroPtr + 0xe0#64 ∧ s3.readReg64 .x8 = s.sp + 0x3e0#64)
    (T := sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
      (∃∗ w0 : BitVec 64, (s.sp + 0x3e0#64) ↦₆₄ w0) ∗
      (∃∗ b8 : BitVec 8, (s.sp + 0x3e8#64) ↦₈ b8) ∗
      cells (s.sp - 1248#64) 8 ∗
      cells (s.sp - 1184#64) 10 ∗
      (∃∗ w2e0 : BitVec 64, (s.sp - 448#64) ↦₆₄ w2e0) ∗
      cells (s.sp - 96#64) 12)
    (by
      dsimp only [ResponderStore.promoteMatchingSessionEmptySpec]
      rw [hsp3, show (s.sp + 0x3e0#64) + 8#64 = s.sp + 0x3e8#64 by bv_omega]
      rfl)
    ⟨hx0_3, hx8_3⟩ (by sep_focus)
    (hnext := fun s4 _ hpc4 hrun4 hsp4_3 _ hcs4 hCode4 => ?_)
  dsimp only [ResponderStore.promoteMatchingSessionEmptySpec]
  rcases hcs4 with ⟨hcs4_19, _, hcs4_21, hcs4_22, _, hcs4_24, _, hcs4_26, hcs4_27, hcs4_28,
    hcs4_29, hvregs4_3⟩
  have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4]; exact hsp_align
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hcs4_19.trans hx19_3
  have hx21_4 : s4.readReg64 .x21 = s2.readReg64 .x0 := hcs4_21.trans hx21_3
  have hx22_4 : s4.readReg64 .x22 = spkStorePtr := hcs4_22.trans hx22_3
  have hx24_4 : s4.readReg64 .x24 = spkKit.spk_vt := hcs4_24.trans hx24_3
  have hx26_4 : s4.readReg64 .x26 = 33#64 := hcs4_26.trans hx26_3
  have hx27_4 : s4.readReg64 .x27 = s.readReg64 .x27 := hcs4_27.trans (hx27_3.trans hx27_2)
  have hx28_4 : s4.readReg64 .x28 = s.readReg64 .x28 := hcs4_28.trans (hx28_3.trans hx28_2)
  have hx29_4 : s4.readReg64 .x29 = s.readReg64 .x29 := hcs4_29.trans (hx29_3.trans hx29_2)
  rw [hsp3, show (s.sp + 0x3e0#64) + 8#64 = s.sp + 0x3e8#64 by bv_omega,
    show ResponderStore.sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) =
      sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) from rfl]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr4 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom2.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom1.symm) (by sep_focus) ?_
  have hstk_alloc := p2_stackAt_split_of_le s.sp stk allocHookStack
    (Nat.le_trans p2_alloc_le_pure hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
  have hAct_split :
      processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt kyberStorePtr kyberStoreVt =
      ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
      (((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗
       ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
       ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗
       ((coroPtr + 0x410#64) ↦₆₄ preKeyStoreVt) ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
       ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64))) := by
    unfold processPrekeyActive10At; ac_rfl
  refine SepWPp.weaken_frame (Entails.of_eq hAct_split) (by sep_focus) ?_
  have hstep5 := p2_seg1c_hooks_placed_wp ext hH s4 coroPtr msgPtr (s2.readReg64 .x0)
    spkStorePtr spkKit.spk_vt (0#64 + spkKit.getShimOff) spkId
    hpc4 hrun4 hsp4_align hx19_4 hx21_4 hx22_4 hx24_4 hx26_4
  rw [hsp4] at hstep5
  refine p2_bind_sepWP_qp_frame_placed hCode4 hstep5 (by sep_focus)
    fun s5 _ hpc5 hrun5 hCode5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5, htr5, hx0_5, hx1_5, hx19_5, _, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5,
    hx27_5, hx28_5, hx29_5, hx30_5, hvregs5_4⟩
  have hsp5_al : s5.spAligned = true := by simpa only [State.spAligned, hsp5] using hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq hAct_split.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (sp3e0_9_entails_memRegion s.sp 0#64 0#8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  have hstk_shim' := p2_stackAt_split_of_le s.sp stk spkKit.getShimStack hstk_shim hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_shim') (by sep_focus) ?_
  sep_norm
  have htr5_eq : s5.trace = s.trace := by rw [htr5, htr4, htr3, htr2, htr1]
  have hx1_5_32 : s5.readReg32 .x1 = spkId := by
    change (s5.readReg64 .x1).setWidth 32 = spkId
    rw [hx1_5, p2_zext64_trunc32_id]
  refine p2_call_oom_rocl_steps_frame_placed
    (x := ({ self := spkStorePtr, id := spkId } : PreKeyShimCall))
    hCode5 (htr5_eq ▸ htr) (hspkOk.getShim (by decide)) hpc5 hrun5 hsp5_al hx30_5
    (hsp5 ▸ p2_spkGetShim_pre_intro_placed hx0_5 hx1_5_32)
    (by sep_focus)
    (fun _ => Entails.refl _)
    (hnext := fun sf _ hpcf hrunf hspf_5 _ hcsf hCodef => ?_)
  dsimp only [kitSpkGetShimSpec]
  rcases hcsf with ⟨hcsf_19, _, _, hcsf_22, hcsf_23, hcsf_24, hcsf_25, hcsf_26, hcsf_27, hcsf_28,
    hcsf_29, hvregsf_5⟩
  rw [hsp5]
  sep_norm
  refine SepWPp.pure_elim fun ⟨hx1_f, hfut_nz, hfut_al, htrf_5⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_shim'.symm) (by sep_focus) ?_
  have hvregs_full : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    rw [hvregsf_5, hvregs5_4, hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]
  refine SepWPp.done hpcf hrunf ⟨?_, hspf_5.trans hsp5, htrf_5.trans htr5_eq,
    hcsf_19.trans hx19_5, hcsf_22.trans hx22_5, hcsf_23.trans hx23_5,
    hcsf_24.trans hx24_5, hcsf_25.trans hx25_5, hcsf_26.trans hx26_5,
    hcsf_27.trans (hx27_5.trans hx27_4), hcsf_28.trans (hx28_5.trans hx28_4),
    hcsf_29.trans (hx29_5.trans hx29_4), hvregs_full, hCodef⟩
  refine Entails.sepExists_right (sf.readReg64 .x0) ?_
  rw [← sepConj_assoc]
  refine Entails.pure_right ⟨rfl, hx1_f, hfut_nz, hfut_al⟩ ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

abbrev stageP2_sub1_kits_4k_placed := @stageP2_sub1_kits_ext_placed
abbrev stageP2_sub1_kits_hooks_placed := @stageP2_sub1_kits_ext_placed

theorem stageP2_sub1_kits_placed [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A ext)
    (hPure : StageP2PureCalleesPlaced P A F ext)
    (spkKit : SignedPreKeyStoreSpec A 0#64)
    (hspkOk : SignedPreKeyStoreKitPlacedOk spkKit ext)
    (stk : Nat)
    (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_shim : spkKit.getShimStack ≤ stk)
    (hstk_lt : stk ≤ 2 ^ 64)
    (s0 s : State)
    (coroPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
     spkStorePtr kyberStorePtr kyberStoreVt : BitVec 64)
    (baseKey : PublicKey) (spkId : BitVec 32) (b_4f1 : BitVec 8)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = stageP1EntryPlaced + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx8 : s.readReg64 .x8 = kyberStorePtr) (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt) (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr) (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr) (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr) (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkKit.spk_vt) :
    SepWPp (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0xf14#64) s
      (cells (coroPtr + 0x3f8#64) 6 ∗ cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗ sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗ ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
       ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗ memRegion (s.sp + 0x3e0#64) 9 ∗
       ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + spkKit.getShimOff)) ∗
       A.pool ∗ stackAt s.sp stk)
      (fun sf P_f =>
        (P_f ⊢
          ∃∗ spkFutPtr : BitVec 64,
            ⌜sf.readReg64 .x0 = spkFutPtr ∧
              sf.readReg64 .x1 = 0#64 + spkKit.getFutVtOff ∧
              spkFutPtr ≠ 0#64 ∧ spkFutPtr.toNat % 8 = 0⌝ ∗
            processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
              idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt kyberStorePtr kyberStoreVt ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
            ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗ ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
            ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗ memRegion (s.sp + 0x3e0#64) 9 ∗
            ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + spkKit.getShimOff)) ∗
            A.live spkFutPtr spkKit.getBoxSize 8 ∗
            spkKit.getBoxAt spkFutPtr spkStorePtr spkId 0#8 ∗ A.pool ∗ stackAt s.sp stk) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧ sf.readReg64 .x19 = coroPtr ∧
        sf.readReg64 .x22 = spkStorePtr ∧ sf.readReg64 .x23 = 0#64 ∧
        sf.readReg64 .x24 = spkKit.spk_vt ∧ sf.readReg64 .x25 = s.sp + 0x210#64 ∧
        sf.readReg64 .x26 = 33#64 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      (PanicOomProp s0) :=
  stageP2_sub1_kits_ext_placed ext hH hPure.to_4K.toStageP2BaseCalleesPlaced4K spkKit hspkOk
    stk hstk_pure hstk_shim hstk_lt s0 s coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr kyberStorePtr kyberStoreVt
    baseKey spkId b_4f1 hCode hpc hrun hsp_align htr hvregs
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

