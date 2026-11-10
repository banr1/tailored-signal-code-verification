/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP1
public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Specs
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.OneKeyStoreBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.IdentityKeyStoreImpl.Defs
import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RemoteIdBytes -- shake: keep

/-!
# Stage P4 Framing and Store-Persistence Helpers for `message_decrypt_prekey::{closure#0}`

Shared `SepWPp` combinators, coroutine/stack memory splitting helpers, and callee-saved register
preservation lemmas for Stage P4 (`save_identity`, `mark_kyber_pre_key_used`, `remove_pre_key`, and
`store_session`).
-/

@[expose] public section

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.E2E.InMem
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.HashbrownBin
open CryptoVerification.E2E.InMem.IdentityKeyStoreImpl
open CryptoVerification.E2E.Record.Serialization (CanonSession)
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")

namespace P3P4

/-! ## 1. Shared `SepWPp` Combinators and Memory Splitting / Folding Helpers -/

def PanicOomProp (s0 sf : State) (Pf : SepProp) : Prop :=
  ∀ R : SepProp, (sf.mem ⊨ Pf ∗ R) →
    (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)

theorem allowPanic_oom_of_trace_eq {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    PanicOomProp s0 sf ((⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) := by
  intro R hm
  have himp : allocFailedIn s sf ∧ s.trace <+: sf.trace →
      allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
    rintro ⟨ha, hp⟩
    unfold allocFailedIn at ha ⊢
    rw [← htr]
    exact ⟨ha, hp⟩
  exact allowPanic_frame himp hm

theorem eq_of_sep_emp {P Q : SepProp} (h : P = Q ∗ emp) : P = Q := by
  rwa [sepConj_emp] at h

theorem SepWPp.weaken_frame {prog : Program} {ret : BitVec 64} {s : State}
    {P P₁ P₂ F : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P₁ ⊢ P₂) (hP : P = P₁ ∗ F)
    (h : SepWPp prog ret s (P₂ ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  rw [hP]
  exact SepWPp.weaken_pre (sepConj_mono_left hent) h

theorem SepWPp.bind_sepWP_frame {prog : Program} {img : Obj.Image} {mid ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      img.FrozenLoaded sm → sm.symtab = img.symtab → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpc hrun (hF.of_keepsFrozen hsteps.keepsFrozen)
      (hsteps.symtab_eq.trans hsym) hregs R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

theorem SepWPp.ret_sepWP_frame {prog : Program} {img : Obj.Image} {ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hstep : SepWP prog ret s P_step
      (fun sf P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sf))
    (hP : P = P_step ∗ F)
    (hret : ∀ sf : State, sf.pc = ret → sf.status = .Running →
      img.FrozenLoaded sf → sf.symtab = img.symtab → Q_regs sf →
      Q sf (P_step_post ∗ F)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.bind_sepWP_frame hF hsym hstep hP fun sf hpc hrun hF' hsym' hregs =>
    SepWPp.done hpc hrun (hret sf hpc hrun hF' hsym' hregs)

theorem SepWPp.bind_sepWPp_frame {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P_stage P_stage_post F : SepProp} {Q_regs : State → Prop}
    {Q : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post) ∧ Q_regs sm)
      (PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q_regs sm →
      SepWPp prog ret sm (P_stage_post ∗ F) Q (PanicOomProp s0)) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨hpan, P_m, hmm, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, fun R' hmR' => by
      rw [sepConj_assoc] at hmR'
      have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1
      exact allowPanic_frame id h1⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem SepWPp.bind_sepWPp_frame_dep {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P_stage F : SepProp} {P_stage_post : State → SepProp} {Q_regs : State → Prop}
    {Q : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post sm) ∧ Q_regs sm)
      (PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q_regs sm →
      SepWPp prog ret sm (P_stage_post sm ∗ F) Q (PanicOomProp s0)) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨hpan, P_m, hmm, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, fun R' hmR' => by
      rw [sepConj_assoc] at hmR'
      have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1
      exact allowPanic_frame id h1⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem SepWPp.ret_sepWPp_frame {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P P_stage P_stage_post F : SepProp} {Q_regs : State → Prop}
    {Q : State → SepProp → Prop}
    (hstage : SepWPp prog ret s P_stage
      (fun sf P_m => (P_m ⊢ P_stage_post) ∧ Q_regs sf)
      (PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hret : ∀ sf : State, sf.pc = ret → sf.status = .Running → Q_regs sf →
      Q sf (P_stage_post ∗ F)) :
    SepWPp prog ret s P Q (PanicOomProp s0) :=
  SepWPp.bind_sepWPp_frame hstage hP fun sf hpc hrun hregs =>
    SepWPp.done hpc hrun (hret sf hpc hrun hregs)

theorem SepWPp.call_frame_frozen_nopanic {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro sf; first | rfl | simp only [Spec.inImage]) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call_wpp_frozen hcall (x := x) (F := F) hF hsym hpc hrun hsp hlr ?_ ?_ ?_ ?_ ?_
  · intro R hm
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  · intro sf code R' _ hex
    rw [hexit_false] at hex
    exact allowPanic_not_exited hex
  · intro sf _ ⟨R', hpan⟩
    rw [hpan_false] at hpan
    exact (allowPanic_not_exited hpan).elim
  · intro sf hpcm hrunm hspm hcsm hFm hsymm
    have hsp_alm : sf.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    exact hnext sf hpcm hrunm hspm hsp_alm hcsm hFm hsymm
  · intro sf R' _ hoom
    rw [hoom_false] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

theorem SepWPp.call_frame_frozen_oom {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State} {φ : Prop}
    {P T F : SepProp} {Q : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
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
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (PanicOomProp s0))
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro sf; first | rfl | simp only [Spec.inImage]) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  refine SepWPp.call_wpp_frozen hcall (x := x) (F := F) hF hsym hpc hrun hsp hlr ?_ ?_ ?_ ?_ ?_
  · intro R hm
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  · intro sf code R' _ hex
    rw [hexit_false] at hex
    exact allowPanic_not_exited hex
  · intro sf _ _
    rw [hpan_eq]
    exact allowPanic_oom_of_trace_eq htr
  · intro sf hpcm hrunm hspm hcsm hFm hsymm
    have hsp_alm : sf.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    exact hnext sf hpcm hrunm hspm hsp_alm hcsm hFm hsymm
  · intro sf R' _ hoom
    rw [hoom_false] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

theorem stackAt_sub_eq (sp : BitVec 64) (big small : Nat)
    (h1 : small ≤ big := by decide) (h2 : big ≤ 2 ^ 64 := by decide) :
    stackAt sp big =
      memRegion (sp - BitVec.ofNat 64 big) (big - small) ∗ stackAt sp small := by
  have h := ProofLib.stackAt_split_bottom sp small (big - small) (by omega)
  rwa [Nat.add_sub_of_le h1] at h

theorem decryptPrekeySavedRegsAt_add_cd0 (sp : BitVec 64) (s0 : State) :
    decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 =
      ((sp + 0xc70#64) ↦₆₄ s0.readReg64 .x29) ∗
      ((sp + 0xc78#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((sp + 0xc80#64) ↦₆₄ s0.readReg64 .x28) ∗
      ((sp + 0xc88#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((sp + 0xc90#64) ↦₆₄ s0.readReg64 .x26) ∗
      ((sp + 0xc98#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((sp + 0xca0#64) ↦₆₄ s0.readReg64 .x24) ∗
      ((sp + 0xca8#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((sp + 0xcb0#64) ↦₆₄ s0.readReg64 .x22) ∗
      ((sp + 0xcb8#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((sp + 0xcc0#64) ↦₆₄ s0.readReg64 .x20) ∗
      ((sp + 0xcc8#64) ↦₆₄ s0.readReg64 .x19) := by
  unfold decryptPrekeySavedRegsAt
  have h0 : sp + 0xcd0#64 - 0x60#64 = sp + 0xc70#64 := by bv_omega
  have h1 : 8#64 + (sp + 0xc70#64) = sp + 0xc78#64 := by bv_omega
  have h2 : 16#64 + (sp + 0xc70#64) = sp + 0xc80#64 := by bv_omega
  have h3 : 24#64 + (sp + 0xc70#64) = sp + 0xc88#64 := by bv_omega
  have h4 : 32#64 + (sp + 0xc70#64) = sp + 0xc90#64 := by bv_omega
  have h5 : 40#64 + (sp + 0xc70#64) = sp + 0xc98#64 := by bv_omega
  have h6 : 48#64 + (sp + 0xc70#64) = sp + 0xca0#64 := by bv_omega
  have h7 : 56#64 + (sp + 0xc70#64) = sp + 0xca8#64 := by bv_omega
  have h8 : 64#64 + (sp + 0xc70#64) = sp + 0xcb0#64 := by bv_omega
  have h9 : 72#64 + (sp + 0xc70#64) = sp + 0xcb8#64 := by bv_omega
  have h10 : 80#64 + (sp + 0xc70#64) = sp + 0xcc0#64 := by bv_omega
  have h11 : 88#64 + (sp + 0xc70#64) = sp + 0xcc8#64 := by bv_omega
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

theorem outPtr48_split_eq (outPtr : BitVec 64) :
    memRegion outPtr 48 =
      (∃∗ u2c : BitVec 32, ∃∗ u24 : BitVec 64, ∃∗ u1c : BitVec 64,
       ∃∗ u14 : BitVec 64, ∃∗ u0c : BitVec 64, ∃∗ u8 : BitVec 32,
       ∃∗ u0 : BitVec 64,
        ((outPtr + 0x0#64) ↦₆₄ u0) ∗
        ((outPtr + 0x8#64) ↦₃₂ u8) ∗
        ((outPtr + 0xc#64) ↦₆₄ u0c) ∗
        ((outPtr + 0x14#64) ↦₆₄ u14) ∗
        ((outPtr + 0x1c#64) ↦₆₄ u1c) ∗
        ((outPtr + 0x24#64) ↦₆₄ u24) ∗
        ((outPtr + 0x2c#64) ↦₃₂ u2c)) := by
  rw [ProofLib.memRegion_split' (b := outPtr) (n := 8) (k := 40)
        (b' := outPtr + 0x8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outPtr + 0x8#64) (n := 4) (k := 36)
        (b' := outPtr + 0xc#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outPtr + 0xc#64) (n := 8) (k := 28)
        (b' := outPtr + 0x14#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outPtr + 0x14#64) (n := 8) (k := 20)
        (b' := outPtr + 0x1c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outPtr + 0x1c#64) (n := 8) (k := 12)
        (b' := outPtr + 0x24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outPtr + 0x24#64) (n := 8) (k := 4)
        (b' := outPtr + 0x2c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight outPtr,
      ProofLib.memRegion_four (outPtr + 0x8#64),
      ProofLib.memRegion_eight (outPtr + 0xc#64),
      ProofLib.memRegion_eight (outPtr + 0x14#64),
      ProofLib.memRegion_eight (outPtr + 0x1c#64),
      ProofLib.memRegion_eight (outPtr + 0x24#64),
      ProofLib.memRegion_four (outPtr + 0x2c#64),
      show (outPtr + 0x0#64) = outPtr from BitVec.add_zero outPtr]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem outPtr48_err_fold (outPtr errTag w0c w14 w1c w24 : BitVec 64) (w8 w2c : BitVec 32) :
    ((outPtr + 0x0#64) ↦₆₄ errTag) ∗
    ((outPtr + 0x8#64) ↦₃₂ w8) ∗
    ((outPtr + 0xc#64) ↦₆₄ w0c) ∗
    ((outPtr + 0x14#64) ↦₆₄ w14) ∗
    ((outPtr + 0x1c#64) ↦₆₄ w1c) ∗
    ((outPtr + 0x24#64) ↦₆₄ w24) ∗
    ((outPtr + 0x2c#64) ↦₃₂ w2c) ⊢
      (outPtr ↦₆₄ errTag) ∗ memRegion (outPtr + 8#64) 40 := by
  rw [BitVec.add_zero,
      ProofLib.memRegion_split' (b := outPtr + 8#64) (n := 4) (k := 36)
        (b' := outPtr + 0xc#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outPtr + 0xc#64) (n := 8) (k := 28)
        (b' := outPtr + 0x14#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outPtr + 0x14#64) (n := 8) (k := 20)
        (b' := outPtr + 0x1c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outPtr + 0x1c#64) (n := 8) (k := 12)
        (b' := outPtr + 0x24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outPtr + 0x24#64) (n := 8) (k := 4)
        (b' := outPtr + 0x2c#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo32_entails_memRegion _ _))))))

theorem memRegion20_split_eq (a : BitVec 64) :
    memRegion a 20 =
      (∃∗ u10 : BitVec 32, ∃∗ u8 : BitVec 64, ∃∗ u0 : BitVec 64,
        (a ↦₆₄ u0) ∗ ((a + 0x8#64) ↦₆₄ u8) ∗ ((a + 0x10#64) ↦₃₂ u10)) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 12)
        (b' := a + 0x8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 0x8#64) (n := 8) (k := 4)
        (b' := a + 0x10#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a,
      ProofLib.memRegion_eight (a + 0x8#64),
      ProofLib.memRegion_four (a + 0x10#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem memRegion20_fold (a u0 u8 : BitVec 64) (u10 : BitVec 32) :
    (a ↦₆₄ u0) ∗ ((a + 0x8#64) ↦₆₄ u8) ∗ ((a + 0x10#64) ↦₃₂ u10) ⊢ memRegion a 20 := by
  rw [memRegion20_split_eq a]
  exact Entails.sepExists_right u10
    (Entails.sepExists_right u8 (Entails.sepExists_right u0 (Entails.refl _)))

theorem memRegion24_coro280_split_eq (coroPtr : BitVec 64) :
    memRegion (coroPtr + 0x280#64) 24 =
      (∃∗ u_294 : BitVec 32, ∃∗ u_28c : BitVec 64, ∃∗ u_284 : BitVec 64, ∃∗ u_280 : BitVec 32,
        ((coroPtr + 0x280#64) ↦₃₂ u_280) ∗
        ((coroPtr + 0x284#64) ↦₆₄ u_284) ∗
        ((coroPtr + 0x28c#64) ↦₆₄ u_28c) ∗
        ((coroPtr + 0x294#64) ↦₃₂ u_294)) := by
  rw [ProofLib.memRegion_split' (b := coroPtr + 0x280#64) (n := 4) (k := 20)
        (b' := coroPtr + 0x284#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x284#64) (n := 8) (k := 12)
        (b' := coroPtr + 0x28c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x28c#64) (n := 8) (k := 4)
        (b' := coroPtr + 0x294#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_four (coroPtr + 0x280#64),
      ProofLib.memRegion_eight (coroPtr + 0x284#64),
      ProofLib.memRegion_eight (coroPtr + 0x28c#64),
      ProofLib.memRegion_four (coroPtr + 0x294#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem memRegion24_coro280_fold (coroPtr u_284 u_28c : BitVec 64) (u_280 u_294 : BitVec 32) :
    ((coroPtr + 0x280#64) ↦₃₂ u_280) ∗
    ((coroPtr + 0x284#64) ↦₆₄ u_284) ∗
    ((coroPtr + 0x28c#64) ↦₆₄ u_28c) ∗
    ((coroPtr + 0x294#64) ↦₃₂ u_294) ⊢ memRegion (coroPtr + 0x280#64) 24 := by
  rw [memRegion24_coro280_split_eq coroPtr]
  exact Entails.sepExists_right u_294
    (Entails.sepExists_right u_28c
      (Entails.sepExists_right u_284
        (Entails.sepExists_right u_280 (Entails.refl _))))

theorem memRegion36_split_eq (a : BitVec 64) :
    memRegion a 36 =
      (∃∗ u20 : BitVec 32, ∃∗ u18 : BitVec 64, ∃∗ u10 : BitVec 64,
       ∃∗ u8 : BitVec 64, ∃∗ u0 : BitVec 64,
        (a ↦₆₄ u0) ∗ ((a + 0x8#64) ↦₆₄ u8) ∗ ((a + 0x10#64) ↦₆₄ u10) ∗
        ((a + 0x18#64) ↦₆₄ u18) ∗ ((a + 0x20#64) ↦₃₂ u20)) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 28)
        (b' := a + 0x8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 0x8#64) (n := 8) (k := 20)
        (b' := a + 0x10#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 0x10#64) (n := 8) (k := 12)
        (b' := a + 0x18#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 0x18#64) (n := 8) (k := 4)
        (b' := a + 0x20#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a,
      ProofLib.memRegion_eight (a + 0x8#64),
      ProofLib.memRegion_eight (a + 0x10#64),
      ProofLib.memRegion_eight (a + 0x18#64),
      ProofLib.memRegion_four (a + 0x20#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem memRegion36_fold (a u0 u8 u10 u18 : BitVec 64) (u20 : BitVec 32) :
    (a ↦₆₄ u0) ∗ ((a + 0x8#64) ↦₆₄ u8) ∗ ((a + 0x10#64) ↦₆₄ u10) ∗
    ((a + 0x18#64) ↦₆₄ u18) ∗ ((a + 0x20#64) ↦₃₂ u20) ⊢ memRegion a 36 := by
  rw [memRegion36_split_eq a]
  exact Entails.sepExists_right u20
    (Entails.sepExists_right u18
      (Entails.sepExists_right u10
        (Entails.sepExists_right u8
          (Entails.sepExists_right u0 (Entails.refl _)))))

theorem sp3e0_48_split_eq (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 48 =
      (∃∗ w_40c : BitVec 32, ∃∗ w_404 : BitVec 64, ∃∗ w_3fc : BitVec 64,
       ∃∗ w_3f4 : BitVec 64, ∃∗ w_3ec : BitVec 64, ∃∗ w_3e8 : BitVec 32,
       ∃∗ w_3e0 : BitVec 64,
        ((sp + 0x3e0#64) ↦₆₄ w_3e0) ∗
        ((sp + 0x3e8#64) ↦₃₂ w_3e8) ∗
        ((sp + 0x3ec#64) ↦₆₄ w_3ec) ∗
        ((sp + 0x3f4#64) ↦₆₄ w_3f4) ∗
        ((sp + 0x3fc#64) ↦₆₄ w_3fc) ∗
        ((sp + 0x404#64) ↦₆₄ w_404) ∗
        ((sp + 0x40c#64) ↦₃₂ w_40c)) := by
  have h := outPtr48_split_eq (sp + 0x3e0#64)
  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h

theorem sp3e0_48_fold (sp w_3e0 w_3ec w_3f4 w_3fc w_404 : BitVec 64) (w_3e8 w_40c : BitVec 32) :
    ((sp + 0x3e0#64) ↦₆₄ w_3e0) ∗
    ((sp + 0x3e8#64) ↦₃₂ w_3e8) ∗
    ((sp + 0x3ec#64) ↦₆₄ w_3ec) ∗
    ((sp + 0x3f4#64) ↦₆₄ w_3f4) ∗
    ((sp + 0x3fc#64) ↦₆₄ w_3fc) ∗
    ((sp + 0x404#64) ↦₆₄ w_404) ∗
    ((sp + 0x40c#64) ↦₃₂ w_40c) ⊢ memRegion (sp + 0x3e0#64) 48 := by
  rw [sp3e0_48_split_eq sp]
  exact Entails.sepExists_right w_40c
    (Entails.sepExists_right w_404
      (Entails.sepExists_right w_3fc
        (Entails.sepExists_right w_3f4
          (Entails.sepExists_right w_3ec
            (Entails.sepExists_right w_3e8
              (Entails.sepExists_right w_3e0 (Entails.refl _)))))))

theorem pollIdentityChangeFalse_split_eq (sp : BitVec 64) :
    pollIdentityChangeResultAt (sp + 0x3e0#64) false =
      (∃∗ w_40c : BitVec 32, ∃∗ w_404 : BitVec 64, ∃∗ w_3fc : BitVec 64,
       ∃∗ w_3f4 : BitVec 64, ∃∗ w_3ec : BitVec 64,
        ((sp + 0x3e0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
        ((sp + 0x3e8#64) ↦₃₂ 0#32) ∗
        ((sp + 0x3ec#64) ↦₆₄ w_3ec) ∗
        ((sp + 0x3f4#64) ↦₆₄ w_3f4) ∗
        ((sp + 0x3fc#64) ↦₆₄ w_3fc) ∗
        ((sp + 0x404#64) ↦₆₄ w_404) ∗
        ((sp + 0x40c#64) ↦₃₂ w_40c)) := by
  simp only [pollIdentityChangeResultAt, Bool.false_eq_true, ↓reduceIte]
  rw [show (sp + 0x3e0#64) + 8#64 = sp + 0x3e8#64 by bv_omega,
      show (sp + 0x3e0#64) + 12#64 = sp + 0x3ec#64 by bv_omega,
      memRegion36_split_eq (sp + 0x3ec#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc]

theorem pollUnitResult_split_eq (sp : BitVec 64) :
    pollUnitResultAt (sp + 0x3e0#64) =
      (∃∗ w_40c : BitVec 32, ∃∗ w_404 : BitVec 64, ∃∗ w_3fc : BitVec 64,
       ∃∗ w_3f4 : BitVec 64, ∃∗ w_3ec : BitVec 64, ∃∗ w_3e8 : BitVec 32,
        ((sp + 0x3e0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
        ((sp + 0x3e8#64) ↦₃₂ w_3e8) ∗
        ((sp + 0x3ec#64) ↦₆₄ w_3ec) ∗
        ((sp + 0x3f4#64) ↦₆₄ w_3f4) ∗
        ((sp + 0x3fc#64) ↦₆₄ w_3fc) ∗
        ((sp + 0x404#64) ↦₆₄ w_404) ∗
        ((sp + 0x40c#64) ↦₃₂ w_40c)) := by
  unfold pollUnitResultAt
  rw [show (sp + 0x3e0#64) + 8#64 = sp + 0x3e8#64 by bv_omega,
      ProofLib.memRegion_split' (b := sp + 0x3e8#64) (n := 4) (k := 36)
        (b' := sp + 0x3ec#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_four (sp + 0x3e8#64),
      memRegion36_split_eq (sp + 0x3ec#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc]

theorem saveBox1_entails_memRegion (futPtr mp qAddrPtr qKeyPtr : BitVec 64) :
    (futPtr ↦₆₄ mp) ∗ ((futPtr + 8#64) ↦₆₄ qAddrPtr) ∗ ((futPtr + 16#64) ↦₆₄ qKeyPtr) ∗
    ((futPtr + 24#64) ↦₈ 1#8) ∗ memRegion (futPtr + 0x19#64) 7 ⊢ memRegion futPtr 32 :=
  inMemSaveBoxAt_memRegion futPtr mp qAddrPtr qKeyPtr 1#8

theorem words3_repack_w32_2w64_w32 (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) =
      (a ↦₃₂ w0.extractLsb' 0 32) ∗
      ((a + 4#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
      ((a + 12#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
      ((a + 20#64) ↦₃₂ w2.extractLsb' 32 32) := by
  rw [← pointsTo32_pair (a + 4#64), ← pointsTo32_pair (a + 12#64)]
  simp only [pointsTo64_split32, BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

/-! ## 2. Substage P4.2 Helpers -/

theorem add_49ce0_ne_zero {b : BitVec 64} (hb : b &&& 0xfff#64 = 0#64) :
    b + 0x70c20#64 ≠ 0#64 := by
  intro h
  have hb' : b = 0xfffffffffff8f3e0#64 := by bv_omega
  rw [hb'] at hb
  nomatch hb

theorem oneKeyFutNoopDropSpec_pre_eq (s : State) :
    oneKeyFutNoopDropSpec.pre () s = (⌜True⌝ ∗ emp) := by
  simp [oneKeyFutNoopDropSpec]

theorem zeroExtend64_setWidth32 (x : BitVec 32) :
    (x.zeroExtend 64).setWidth 32 = x :=
  _root_.BitVec.setWidth_setWidth_of_le x (_root_.Nat.le_add_left 32 32)

/-! ## 3. Callee-Saved Register Preservation -/

/-- Callee-saved GPR preservation (`x19`–`x29`) across `decryptPrekeyClosure` Stage P4,
with a 12th `True` conjunct matching the shape of `CalleeSavedPreserved`. -/
def ClosureCalleeSavedP4 (s0 sf : State) : Prop :=
  sf.readReg64 .x19 = s0.readReg64 .x19 ∧
  sf.readReg64 .x20 = s0.readReg64 .x20 ∧
  sf.readReg64 .x21 = s0.readReg64 .x21 ∧
  sf.readReg64 .x22 = s0.readReg64 .x22 ∧
  sf.readReg64 .x23 = s0.readReg64 .x23 ∧
  sf.readReg64 .x24 = s0.readReg64 .x24 ∧
  sf.readReg64 .x25 = s0.readReg64 .x25 ∧
  sf.readReg64 .x26 = s0.readReg64 .x26 ∧
  sf.readReg64 .x27 = s0.readReg64 .x27 ∧
  sf.readReg64 .x28 = s0.readReg64 .x28 ∧
  sf.readReg64 .fp = s0.readReg64 .fp ∧
  True

end P3P4

end CryptoVerification.E2E.Pqxdh.ResponderClosure
