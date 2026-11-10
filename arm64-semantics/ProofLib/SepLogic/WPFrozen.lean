/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP
public import ProofLib.Invariant
import ProofLib.SepLogic.Model
import ProofLib.Hoare.Model

/-!
# Frozen-Memory Cut and Cross-Program Call Rules for `SepWP`

Provides `SepWP.seq_frozen` and `SepWP.mono_frozen` for propagating `Memory.KeepsFrozen`-stable
facts across `SepWP` segments, and `Steps.of_sameHooks` and `SepWP.call_subroutine_frame_other`
for calling subroutines verified against another `Program` with matching hooks and `svc` handler.
-/

@[expose] public section

namespace ProofLib

open Arm64

/-- Run `SepWP` to an intermediate PC `mid`; at `mid`, a `KeepsFrozen`-stable fact `Φ` that held
    for the start memory holds again (it is preserved along the trace), and the proof continues
    to `target`. -/
theorem SepWP.seq_frozen {prog : Program} {mid target : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {Φ : Memory → Prop}
    (hst : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m') (hΦ : Φ s.mem)
    (h : SepWP prog mid s P (fun sm Pm => Φ sm.mem → SepWP prog target sm Pm post oom) oom) :
    SepWP prog target s P post oom := by
  unfold SepWP reaches_pc at *
  intro R hm hL
  rcases h R hm hL with ⟨sm, hst1, ⟨_, _, Pm, hmm, hcont⟩ | hoom⟩
  · obtain ⟨sf, hst2, hout⟩ :=
      hcont (hst _ _ hΦ hst1.keepsFrozen) R hmm (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hout⟩
  · exact ⟨sm, hst1, Or.inr hoom⟩

/-- Postcondition weakening that may use a `KeepsFrozen`-stable fact `Φ` of the start memory, which
    still holds for the memory of the state reaching `target`. -/
theorem SepWP.mono_frozen {prog : Program} {target : BitVec 64} {s : State} {P : SepProp}
    {post post' : State → SepProp → Prop} {oom : State → SepProp} {Φ : Memory → Prop}
    (hst : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m') (hΦ : Φ s.mem)
    (h : SepWP prog target s P post oom)
    (himp : ∀ sf Pf, sf.pc = target → sf.status = .Running → Φ sf.mem → post sf Pf → post' sf Pf) :
    SepWP prog target s P post' oom := by
  unfold SepWP reaches_pc at *
  intro R hm hL
  rcases h R hm hL with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hp⟩ | hoom⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf,
      himp sf Pf hpc hrun (hst _ _ hΦ hsteps.keepsFrozen) hp⟩⟩
  · exact ⟨sf, hsteps, Or.inr hoom⟩

/-! ## Calls into code verified over another `Program` -/

/-- `Step` sees the program only through `externAt?` and `svc`, so a run of `Q` is a run of `P`
    when both have the same hooks and `svc` handler. -/
theorem Steps.of_sameHooks {P Q : Program} (hext : ∀ pc, Q.externAt? pc = P.externAt? pc)
    (hsvc : Q.svc = P.svc) {s sf : State} (h : Steps Q s sf) : Steps P s sf := by
  induction h with
  | refl => exact .refl _
  | @step s1 s2 s3 h1 _ ih =>
    refine .step ?_ ih
    have hf : Q.fetchMem s1.mem s1.pc = P.fetchMem s1.mem s1.pc := by
      unfold Program.fetchMem; rw [hext]
    have hev : ∀ inst, Q.evalInst inst s1 = P.evalInst inst s1 := fun inst => by
      unfold Program.evalInst; rw [hsvc]
    cases h1 with
    | @exec inst hr hfe => rw [hev inst]; exact .exec hr (hf ▸ hfe)
    | halt_unmapped hr hfe he => exact .halt_unmapped hr (hf ▸ hfe) (hext _ ▸ he)
    | extern hr he hk hsy => exact .extern hr (hext _ ▸ he) hk hsy
    | extern_fault hr he hn => exact .extern_fault hr (hext _ ▸ he) hn

/-- Framed call, inside a `SepWP` proof over `P`, of a subroutine verified over another program
    `Q` (e.g. code of a second loaded image) with the same hooks and `svc` handler. The caller
    supplies `Q.CodeLoaded` at the call site; the continuation gets it back at the return site. -/
theorem SepWP.call_subroutine_frame_other {α : Type} {P Q : Program} {entry target_pc : BitVec 64}
    {spec : Spec α}
    (hcall : subroutine_ok Q entry spec)
    (hext : ∀ pc, Q.externAt? pc = P.externAt? pc) (hsvc : Q.svc = P.svc)
    {x : α} {s : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp} {ret_pc : BitVec 64}
    (hQL : Q.CodeLoaded s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (h_no_panic : ∀ R' sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s sf ∗ R'))
    (h_no_exit : ∀ R' code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s sf ∗ R'))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → Q.CodeLoaded sf.mem →
      SepWP P target_pc sf (spec.post x s sf ∗ F) post oom)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWP P target_pc s Pre post oom := by
  unfold SepWP reaches_pc
  intro R hm hL
  obtain ⟨sm, hsteps, hout⟩ :=
    reaches_outcome_iff.1
      (subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun (hpre R hm) hsp_align) hQL
  have hstepsP := Steps.of_sameHooks hext hsvc hsteps
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpostM⟩ | ⟨hpan, hpostM⟩ |
      ⟨code, hex, hpostM⟩ | ⟨hoom_st, hpostM⟩
  · rw [← sepConj_assoc] at hpostM
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      SepWP.elim (hnext sm hpcm hrunm hspm hcsm (hsteps.codeLoaded hQL)) hpostM
        (hsteps.codeLoaded hL)
    exact ⟨sf, hstepsP.trans hsteps', hout'⟩
  · exact (h_no_panic (F ∗ R) sm hpan hpostM).elim
  · exact (h_no_exit (F ∗ R) code sm hex hpostM).elim
  · exact ⟨sm, hstepsP, Or.inr ⟨hoom_st, h_oom R sm hoom_st hpostM⟩⟩

end ProofLib
