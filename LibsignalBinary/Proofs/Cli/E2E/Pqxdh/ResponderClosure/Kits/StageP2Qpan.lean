/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBob
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKit
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs

/-!
# Stage P2 Panic-Postcondition (`Qp`) Combinators

Polymorphic `{Qp : State → SepProp → Prop}` variants of the Stage P2 `SepWPp` sequencing and
subroutine-call combinators, lifting `(∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)` across stage
boundaries.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure

theorem p2_mono_panic {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp₁ Qp₂ : State → SepProp → Prop}
    (hpan : ∀ sf Pf, Qp₁ sf Pf → Qp₂ sf Pf)
    (h : SepWPp prog ret s P Q Qp₁) :
    SepWPp prog ret s P Q Qp₂ := by
  intro R hm hL
  obtain ⟨sf, hst, ⟨hpc, hrun, P_f, hmf, hq⟩ | ⟨hp, P_f, hmf, hqp⟩ | hoom⟩ := h R hm hL
  · exact ⟨sf, hst, Or.inl ⟨hpc, hrun, P_f, hmf, hq⟩⟩
  · exact ⟨sf, hst, Or.inr (Or.inl ⟨hp, P_f, hmf, hpan sf P_f hqp⟩)⟩
  · exact ⟨sf, hst, Or.inr (Or.inr hoom)⟩

theorem p2_cut_qpan {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {Pre : SepProp} {Q Qp : State → SepProp → Prop}
    (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (h : SepWPp prog mid s Pre (fun sm Pm => SepWPp prog ret sm Pm Q Qp) (PanicOomProp s0)) :
    SepWPp prog ret s Pre Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨_, _, Pm, hmm, hnext⟩ | ⟨hp, Pm, hmm, hqp⟩ | hoom⟩ := h R hm hL
  · obtain ⟨sf, hsteps', hout'⟩ := hnext R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hp, Pm, hmm, hpan sm Pm hqp⟩)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem p2_bind_loaded_qpan {prog : Program} {img : Obj.Image} {mid target : BitVec 64}
    {s0 s : State} {P : SepProp} {Qm post Qp : State → SepProp → Prop}
    (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h1 : SepWPp prog mid s P Qm (PanicOomProp s0))
    (h2 : ∀ sm Pm, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      img.FrozenLoaded sm → sm.symtab = img.symtab → Qm sm Pm →
      SepWPp prog target sm Pm post Qp) :
    SepWPp prog target s P post Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hQ⟩ | ⟨hp, Pm, hmm, hqp⟩ | hoom⟩ := h1 R hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      h2 sm Pm hsteps hpcm hrunm (hF.of_keepsFrozen hsteps.keepsFrozen)
        (hsteps.symtab_eq.trans hsym) hQ R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hp, Pm, hmm, hpan sm Pm hqp⟩)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem p2_bind_sepWP_steps_frame_qpan {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P P_seg F P_seg_post : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hseg : SepWP prog mid s P_seg (fun sm P_m => (P_m ⊢ P_seg_post) ∧ Q_regs sm))
    (hP : P = P_seg ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      img.FrozenLoaded sm → sm.symtab = img.symtab → Q_regs sm →
      SepWPp prog ret sm (P_seg_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  rcases hseg.elim hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨_, hmo⟩⟩
  · have hmm' : sm.mem ⊨ (P_seg_post ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm (hF.of_keepsFrozen hsteps.keepsFrozen)
        (hsteps.symtab_eq.trans hsym) hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact (not_satisfies_false_sepConj hmo).elim

theorem p2_bind_sepWPp_oom_frame_qpan {prog : Program} {mid ret : BitVec 64}
    {s0 s : State} {P P_stage F : SepProp} {P_stage_post : State → SepProp}
    {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post sm) ∧ Q_regs sm)
      (PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Q_regs sm →
      SepWPp prog ret sm (P_stage_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨hp, P_m, hmm, hpanm⟩ |
    ⟨_, hoom⟩⟩ := hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    refine ⟨sm, hsteps, Or.inr (Or.inl ⟨hp, P_m ∗ F, hmm, hpan sm (P_m ∗ F) (fun R' hmR' => ?_)⟩)⟩
    rw [sepConj_assoc] at hmR'
    have h1 := hpanm (F ∗ R') hmR'
    rw [← sepConj_assoc] at h1
    exact allowPanic_frame id h1
  · exact (not_satisfies_false_sepConj hoom).elim

theorem p2_call_oom_steps_frame_qpan {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    {P P_spec F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpan_qp : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s0.trace <+: s.trace)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : P_spec ⊢ spec.pre x s)
    (hP : P = P_spec ∗ F)
    (hpan : ∀ sf, spec.onPanic x s sf ⊢ ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by
      intro _ _; repeat (first | simp only [Spec.inImage] | simp only [withLogOff] | simp only [withEnvPre]); rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro _; repeat (first | simp only [Spec.inImage] | simp only [withLogOff] | simp only [withEnvPre]); rfl) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  have hm' : s.mem ⊨ spec.pre x s ∗ (F ∗ R) :=
    Arm64.Satisfies.mono (sepConj_mono_left hpre) hm
  obtain ⟨sm, hsteps, hout, -⟩ :=
    subroutine_ok.no_fault_before_outcome hcall x (F ∗ R) s hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpanm, hpost⟩ |
    ⟨code, _, hpost⟩ | ⟨_, _hoom_post⟩
  rotate_right; · rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm
        (hF.of_keepsFrozen hsteps.keepsFrozen) (hsteps.symtab_eq.trans hsym)
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · have hpost' : sm.mem ⊨ ((⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap) ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left (hpan sm)) hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpanm,
      (⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap) ∗ F, hpost',
      hpan_qp sm _ (p2_allowPanic_oom_of_trace_prefix htr)⟩)⟩
  · rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

theorem p2_call_frame_frozen_oom_prefix_qpan {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpan_qp : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s0.trace <+: s.trace)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_eq : ∀ sf, spec.onPanic x s sf =
      (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      Steps prog s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro sf; first | rfl | simp only [Spec.inImage]) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    subroutine_ok.no_fault_before_outcome hcall x (F ∗ R) s hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hpost⟩ |
    ⟨_hoom_st, _hoom_post⟩
  rotate_right; · rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm
        (hF.of_keepsFrozen hsteps.keepsFrozen) (hsteps.symtab_eq.trans hsym) hsteps
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [hpan_eq, ← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost,
      hpan_qp sm _ (p2_allowPanic_oom_of_trace_prefix htr)⟩)⟩
  · rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

theorem p2_call_inImage_oom_steps_frame_qpan {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpan_qp : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s0.trace <+: s.trace)
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_eq : ∀ sf, spec.onPanic x s sf =
      (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ (spec.inImage img).pre x s ∗ (F ∗ R) := by
    dsimp only [Spec.inImage]
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj,
      ← sepConj_assoc, ← hP]
    exact ⟨⟨hF, hsym⟩, hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    subroutine_ok.no_fault_before_outcome hcall x (F ∗ R) s hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hpost⟩ |
    ⟨_hoom_st, _hoom_post⟩
  rotate_right
  · dsimp only [Spec.inImage] at _hoom_post
    rw [hoom_false] at _hoom_post
    exact (not_satisfies_false_sepConj _hoom_post).elim
  · dsimp only [Spec.inImage] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm
        (hF.of_keepsFrozen hsteps.keepsFrozen) (hsteps.symtab_eq.trans hsym)
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [Spec.inImage] at hpost
    rw [hpan_eq, ← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost,
      hpan_qp sm _ (p2_allowPanic_oom_of_trace_prefix htr)⟩)⟩
  · dsimp only [Spec.inImage] at hpost
    rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

section InitBobErrOwned

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

/-- Owned heap payload of the `SignalProtocolError` returned by `pqxdhAccept` when
`Model.acceptKeys P inp = none`:
- `isStr = true`: tag 24 (`InvalidMessage`, `0x8000000000000018#64`) with heap `String` buffer at
  `(cap = w2, ptr = w3, len = w4)`,
- `isStr = false`: tag 10 (`InvalidKeyAgreement`, `0x800000000000000a#64`), plain payload. -/
def pqxdhAcceptErrPayloadAt (A : RustAlloc) (errTag w2 w3 w4 : BitVec 64) : SepProp :=
  ∃∗ isStr : Bool,
    if isStr then
      ⌜errTag = 0x8000000000000018#64⌝ ∗
      ∃∗ bs : List (BitVec 8),
        ⌜BitVec.ofNat 64 bs.length = w4 ∧ bs.length ≤ w2.toNat ∧ w2.toNat < 2 ^ 63 ∧ w3 ≠ 0#64⌝ ∗
        (if w2 = 0#64 then emp
         else A.live w3 w2.toNat 1 ∗ (w3 ↦ₛ bs) ∗
           memRegion (w3 + BitVec.ofNat 64 bs.length) (w2.toNat - bs.length))
    else ⌜errTag = 0x800000000000000a#64⌝

/-- Owned-payload refinement of `initBobErrAt` for the 344-byte
`Result<SessionState, SignalProtocolError>` sret slot `outPtr` of `initialize_bob_session`:
`Result::Err` discriminant (`-1`) at `outPtr`, 48-byte `SignalProtocolError` at `outPtr + 8#64`,
its `pqxdhAcceptErrPayloadAt`, and 288 trailing bytes at `outPtr + 56#64`. -/
def initBobErrOwnedAt (A : RustAlloc) (outPtr : BitVec 64) : SepProp :=
  (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
  ∃∗ errTag : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
  ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
    ⌜errTag ≠ pollReadyOkWord ∧ errTag ≠ 0xfffffffffffffffd#64⌝ ∗
    speWordsAt (outPtr + 8#64) errTag w2 w3 w4 w5 w6 ∗
    pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
    memRegion (outPtr + 56#64) 288

/-- `initializeBobSessionErrInnerSpec` strengthened so the `none` postcondition exposes
`initBobErrOwnedAt A g.outPtr` (retaining the tag-24 heap buffer or tag-10 witness) instead of
forgetting it into `initBobErrAt g.outPtr`. -/
def initializeBobSessionErrOwnedInnerSpec (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec InitBobCallGhost where
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
    (logFilterAddr img ↦₆₄ 0#64) ∗
    stackAt s.sp (768 + pqxdhEntryStack) ∗
    A.pool
  post := fun (g : InitBobCallGhost) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    bobParamsFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
      g.inp g.ikBPk g.spkBPk g.sameAccountByte ∗
    (initBobErrOwnedAt A g.outPtr ∗ anyHeap) ∗
    (logFilterAddr img ↦₆₄ 0#64) ∗
    stackAt s0.sp (768 + pqxdhEntryStack) ∗
    A.pool
  onPanic := rustPanicOnOom img

def initializeBobSessionErrOwnedSpec (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec InitBobCallGhost :=
  (initializeBobSessionErrOwnedInnerSpec P A img).inImage img

/-- Stack-parameterized `initializeBobSessionErrOwnedInnerSpec` (`stk = 768 + pqxdhEntryStack` for 0-stack, `stk = 768 + Initiator.pqxdhEntryStackExt` for 4K/`Ext`). -/
def initializeBobSessionErrOwnedAtInnerSpec (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (stk : Nat) : Spec InitBobCallGhost where
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
    (logFilterAddr img ↦₆₄ 0#64) ∗
    stackAt s.sp stk ∗
    A.pool
  post := fun (g : InitBobCallGhost) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    bobParamsFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
      g.inp g.ikBPk g.spkBPk g.sameAccountByte ∗
    (initBobErrOwnedAt A g.outPtr ∗ anyHeap) ∗
    (logFilterAddr img ↦₆₄ 0#64) ∗
    stackAt s0.sp stk ∗
    A.pool
  onPanic := rustPanicOnOom img

def initializeBobSessionErrOwnedAtSpec (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (stk : Nat) : Spec InitBobCallGhost :=
  (initializeBobSessionErrOwnedAtInnerSpec P A img stk).inImage img

/-- 4K/`Ext` variant of `initializeBobSessionErrOwnedInnerSpec` using
`768 + Initiator.pqxdhEntryStackExt` (`33536` B) stack budget. -/
def initializeBobSessionErrOwned4KInnerSpec (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec InitBobCallGhost :=
  initializeBobSessionErrOwnedAtInnerSpec P A img (768 + Initiator.pqxdhEntryStackExt)

def initializeBobSessionErrOwned4KSpec (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec InitBobCallGhost :=
  (initializeBobSessionErrOwned4KInnerSpec P A img).inImage img

abbrev initializeBobSessionErrOwnedExtSpec := initializeBobSessionErrOwned4KSpec

theorem initializeBobSessionErrOwnedSpec_to_4K {prog : Program} {entry : BitVec 64}
    {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    (h : subroutine_ok prog entry (initializeBobSessionErrOwnedSpec P A img)) :
    subroutine_ok prog entry (initializeBobSessionErrOwned4KSpec P A img) := by
  refine subroutine_ok_map_panic h ?_
    (fun _ _ _ _ _ _ he => by
      dsimp only [initializeBobSessionErrOwnedSpec, initializeBobSessionErrOwnedInnerSpec,
        Spec.inImage] at he
      exact not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ _ ho => by
      dsimp only [initializeBobSessionErrOwnedSpec, initializeBobSessionErrOwnedInnerSpec,
        Spec.inImage] at ho
      exact (not_satisfies_false_sepConj ho).elim)
  intro g R s0 hpre
  let F_stk : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 (768 + Initiator.pqxdhEntryStackExt))
      ((768 + Initiator.pqxdhEntryStackExt) - (768 + pqxdhEntryStack))
  refine ⟨g, F_stk ∗ R, ?_, fun sf hpost => ?_, fun sf hpan => ?_⟩
  · dsimp only [initializeBobSessionErrOwned4KSpec, initializeBobSessionErrOwned4KInnerSpec,
      initializeBobSessionErrOwnedAtInnerSpec, initializeBobSessionErrOwnedSpec,
      initializeBobSessionErrOwnedInnerSpec, Spec.inImage, F_stk] at hpre ⊢
    rw [p2_stackAt_split_of_le s0.sp (768 + Initiator.pqxdhEntryStackExt)
      (768 + pqxdhEntryStack) (by decide) (by decide)] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, hpure, hmem⟩
    exact ⟨hinv, hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [initializeBobSessionErrOwned4KSpec, initializeBobSessionErrOwned4KInnerSpec,
      initializeBobSessionErrOwnedAtInnerSpec, initializeBobSessionErrOwnedSpec,
      initializeBobSessionErrOwnedInnerSpec, Spec.inImage, F_stk] at hpost ⊢
    rw [p2_stackAt_split_of_le s0.sp (768 + Initiator.pqxdhEntryStackExt)
      (768 + pqxdhEntryStack) (by decide) (by decide)]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, Satisfies.of_eq hpost.2 (by ac_rfl)⟩
  · dsimp only [initializeBobSessionErrOwned4KSpec, initializeBobSessionErrOwned4KInnerSpec,
      initializeBobSessionErrOwnedAtInnerSpec, initializeBobSessionErrOwnedSpec,
      initializeBobSessionErrOwnedInnerSpec, Spec.inImage, rustPanicOnOom, F_stk] at hpan ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpan ⊢
    rcases hpan with ⟨hp, hmem_pan⟩
    exact ⟨hp, Arm64.Satisfies.mono (Entails.trans
      (Entails.of_eq (show anyHeap ∗ (memRegion _ _ ∗ R) =
        (anyHeap ∗ memRegion _ _) ∗ R by ac_rfl))
      (sepConj_mono_left (entails_anyHeap _))) hmem_pan⟩

end InitBobErrOwned

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

