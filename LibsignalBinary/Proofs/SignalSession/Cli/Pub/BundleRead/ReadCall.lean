/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.PublicSpecs
public import LibsignalBinary.Proofs.CodeLayout
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Fs
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.Decode
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.BundleRead.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit

/-!
# `read_file` Call-Site Lemma for `read_bundle::{closure#0}`

Isolates the `bl signal_session::io::read_file` call step at offset `+40` (`0x28`), preserving
`FsInv F0 T0`.
-/

/-- Subroutine hypothesis for `read_file` under `readFileSpec`. -/
abbrev ReadCallHyp (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (readStk : Nat) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr readFileName)
    (readFileSpec rd pathOk A img readStk)

theorem readFile_addr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr bundleReadName +
      bv% (ls_rel% bundleReadName readFileName) =
      (tripleRatchetProgAtExt b ext).fnAddr readFileName := by
  have hk : BitVec.ofNat 64 (libsignalSessionCode.fnOff bundleReadName) +
      bv% (ls_rel% bundleReadName readFileName) =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff readFileName) := by
    rw [bundleRead_fnOff, readFile_fnOff]; rfl
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, BitVec.add_assoc, hk]

theorem allocFailedIn_of_eq_trace {s0 s1 sf : State}
    (htr : s1.trace = s0.trace) (h : allocFailedIn s1 sf) :
    allocFailedIn s0 sf := by
  unfold allocFailedIn at *
  rwa [htr] at h

/-- Executes `bl signal_session::io::read_file` at offset `+40`, preserving `FsInv F0 T0` and pinning `s.fs.files = F0`. -/
theorem readCall_step {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop} {readStk : Nat}
    (hRead : ReadCallHyp img A ext rd pathOk readStk)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (F0 : FsFiles) (T0 : List TraceEvent)
    {ret : BitVec 64} {s0 s : State}
    {pathPtr retSlot : BitVec 64} {p : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hPC : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr bundleReadName + bv% (40))
    (hRun : s.status = .Running)
    (hAl : s.spAligned = true)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hinv : FsInv F0 T0 s)
    (htr : s.trace = T0)
    (hs0_tr : s0.trace = T0)
    (hx0 : s.readReg64 .x0 = pathPtr)
    (hx1 : (s.readReg64 .x1).toNat = p.length)
    (hx8 : s.readReg64 .x8 = retSlot)
    (hlen : p.length < 2 ^ 32)
    (hpOk : pathOk p)
    (hnext : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr bundleReadName + bv% (44) →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.spAligned = true →
      CalleeSavedPreserved s sf →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      FsInv F0 T0 sf →
      ∀ r : Except Unit (List (BitVec 8)),
      (r = rd F0 p ∧ sf.trace = T0) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        (ioVecAt A retSlot r ∗ (pathPtr ↦ₛ p) ∗ stackAt s.sp readStk ∗ A.pool ∗ F) Q Qp)
    (hpanic : ∀ sf : State, sf.status = .Panicked → allocFailedIn s0 sf → T0 <+: sf.trace →
      ∃ P_f, (anyHeap ∗ F ⊢ P_f) ∧ Qp sf P_f) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (((pathPtr ↦ₛ p) ∗ memRegion retSlot 24 ∗ stackAt s.sp readStk ∗ A.pool) ∗ F) Q Qp := by
  code_fetches_range libsignalSessionCode bundleReadBin img.base (Rust.withPanics ext)
    bundleRead_fnOff (num% (ls_off% bundleReadName)) 40 4
  apply SepWPp.seq_frozen (mid := (tripleRatchetProgAtExt img.base ext).fnAddr readFileName)
    (Φ := fun _ => True) (fun _ _ _ _ => trivial) trivial
  wp_steps
  refine SepWP.done ?_ ?_ ?_
  · simp [arm64_norm, Program.fnAddr_rebase]
  · simp [arm64_norm, hRun]
  · intro _ R hm1 hL
    let s1 : State :=
      (s.writeReg64 (Reg.gpr 30#5) (img.base + bv% (ls_off% bundleReadName + 44))).setPC
        (img.base + bv% (ls_off% readFileName))
    have hpc1 : s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr readFileName := by
      simp only [s1, arm64_norm, Program.fnAddr_rebase, readFile_fnOff]
    have hlr1 : s1.readReg64 .lr =
        (tripleRatchetProgAtExt img.base ext).fnAddr bundleReadName + bv% (44) := by
      simp only [s1, arm64_norm, Program.fnAddr_rebase, bundleRead_fnOff, BitVec.add_assoc]
    have hs_files : s.fs.files = F0 :=
      hinv.files_eq (by simp [htr] : s.trace = T0 ++ []) (by simp [NoFsEv])
    have hLift : subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr readFileName)
        (withFsInv (readFileSpec rd pathOk A img readStk) F0 T0) :=
      subroutine_ok_withFsInv hFs hRead F0 T0
    let g : ReadFileGhost := { pathA := pathPtr, path := p, ret := retSlot }
    obtain ⟨sm, hsteps_call, hout, -⟩ :=
      hLift.no_fault_before_outcome g (F ∗ R) s1
        hpc1
        (by simp [s1, arm64_norm, hRun])
        (withFsInv_pre_intro
          ⟨[], by simp [s1, arm64_norm, htr], fun _ => by simpa [s1, arm64_norm] using hs_files⟩
          (by
            dsimp only [readFileSpec, Spec.inImage]
            rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
            refine ⟨⟨by simpa [s1, arm64_norm] using hF, by simpa [s1, arm64_norm] using hsym⟩,
              ⟨by simpa [s1, g, arm64_norm] using hx0,
               by simpa [s1, g, arm64_norm] using hx1,
               by simpa [s1, g, arm64_norm] using hx8, hlen, hpOk⟩,
              by simpa [s1, g, sepConj_assoc] using hm1⟩))
        (by simpa [State.spAligned, s1, arm64_norm] using hAl)
        hL
    rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hpost⟩ |
      ⟨_, hpost⟩
    · obtain ⟨hinv_sm, hpost_rf⟩ := withFsInv_post_elim hpost
      dsimp only [readFileSpec, Spec.inImage] at hpost_rf
      rw [sepConj_assoc, sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hpost_rf
      obtain ⟨r, hpost_r⟩ := hpost_rf
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_r
      obtain ⟨⟨hr1, hr2⟩, hmem_sm⟩ := hpost_r
      have hr_out : r = rd F0 p ∧ sm.trace = T0 :=
        ⟨hr1.trans (by simp [s1, g, arm64_norm, hs_files]),
          hr2.trans (by simpa [s1, arm64_norm] using htr)⟩
      rw [hlr1] at hpcm
      have hsp_eq : sm.sp = s.sp := hspm.trans (by simp [s1, arm64_norm])
      have hsp_al_sm : sm.spAligned = true := by simpa [State.spAligned, hsp_eq] using hAl
      have hcs_s : CalleeSavedPreserved s sm := by
        simpa [CalleeSavedPreserved, s1, arm64_norm] using hcsm
      have hmem_sm' : sm.mem ⊨
          (ioVecAt A retSlot r ∗ (pathPtr ↦ₛ p) ∗ stackAt s.sp readStk ∗ A.pool ∗ F) ∗ R := by
        simpa [g, s1, arm64_norm, sepConj_assoc] using hmem_sm
      obtain ⟨sf, hsteps_rest, hout_rest⟩ :=
        hnext sm hpcm hrunm hsp_eq hsp_al_sm hcs_s
          ((by simpa [s1, arm64_norm] using hF : img.FrozenLoaded s1).of_keepsFrozen hsteps_call.keepsFrozen)
          (hsteps_call.symtab_eq.trans (by simpa [s1, arm64_norm] using hsym))
          hinv_sm r hr_out R hmem_sm' (hsteps_call.codeLoaded hL)
      exact ⟨sf, hsteps_call.trans hsteps_rest, hout_rest⟩
    · dsimp only [withFsInv, readFileSpec, Spec.inImage] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost
      obtain ⟨_, ⟨haf, hpfx⟩, hm⟩ := hpost
      have htr1 : s1.trace = T0 := by simpa [s1, arm64_norm] using htr
      obtain ⟨P_f, hent, hQp⟩ := hpanic sm hpan
        (allocFailedIn_of_eq_trace (htr1.trans hs0_tr.symm) haf) (htr1 ▸ hpfx)
      rw [← sepConj_assoc] at hm
      exact ⟨sm, hsteps_call, Or.inr (Or.inl ⟨hpan, P_f, Satisfies.mono (sepConj_mono_left hent) hm,
        hQp⟩)⟩
    · dsimp only [withFsInv, readFileSpec, Spec.inImage] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      exact (not_satisfies_false_sepConj hpost.2).elim
    · dsimp only [withFsInv, readFileSpec, Spec.inImage] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      exact (not_satisfies_false_sepConj hpost.2).elim

end CryptoVerification.SignalSession.Cli.BundleRead.Helpers
