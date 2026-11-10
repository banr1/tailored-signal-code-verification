/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymC
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Base
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section

set_option autoImplicit false

/-!
# Relocatable Base Helpers for `signal_session::address` (`[LibsignalPlacement]`, Block `580`)

Block-`580` `SepWPp`, call, and panic helpers (`sepWPp_of_sepWP_lscro`, `addr_call_rocl`) for the
relocatable proof of `signal_session::address`.
-/

namespace CryptoVerification.SignalSession.Cli.MainHops.Address.Helpers

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed

abbrev lsHandleErrorSym580 : String := "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"

theorem lscro_of_keepsFrozen {pl : Obj.MultiPlacement} {m m' : Memory}
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded pl m)
    (hkf : Memory.KeepsFrozen m m') :
    LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded pl m' :=
  hcrl.of_keepsFrozen hkf

theorem sepWPp_of_sepWP_lscro {prog : Program} {pl : Obj.MultiPlacement}
    {mid ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded pl sm.mem →
        SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q (Qp) := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, hfalse⟩⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout'⟩ :=
      hnext (lscro_of_keepsFrozen hcrl hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact (not_satisfies_false_sepConj hfalse).elim

theorem addr_panic_handle_error_placed [LibsignalPlacement] {H : LibsignalHooks}
    (hpan : H lsHandleErrorSym580 = some Rust.panicked) :
    (lsProg_580 H).externAt? (lsρ lsHandleErrorSym580) = some Rust.panicked := by
  rw [ls_externAt?_of_mem (prog := lsProg_580 H) (i := 580) (H := H)
    (sym := lsHandleErrorSym580)]
  exact hpan

theorem addr_call_rocl {prog : Program} {pl : Obj.MultiPlacement}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    {α : Type} {callee_pc ret_pc : BitVec 64} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog callee_pc (LibsignalPublicApi.StoreKit.withLsRoCl pl spec))
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (htr : s.trace = s0.trace)
    (hpc : s.pc = callee_pc)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ ho; exact not_satisfies_false_sepConj ho)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') →
      allocFailedIn s sf := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hnext : ∀ sf : State,
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded pl sf.mem →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (AddrPanicAllow s0)) :
    SepWPp prog ret s P Q (AddrPanicAllow s0) := by
  intro R hm hL
  have hm_pre : s.mem ⊨ (spec.pre x s ∗ F) ∗ R :=
    Satisfies.mono (sepConj_mono_left hP) hm
  have hpre : s.mem ⊨ (LibsignalPublicApi.StoreKit.withLsRoCl pl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl]
    rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcrl, by simpa only [sepConj_assoc] using hm_pre⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hpre hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ |
      ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hcrl_m, hpost⟩
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hcrl_m hpcm hrunm hspm hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl] at hpost
    have halloc := hpanic sm (F ∗ R) hpan hpost
    have halloc0 : allocFailedIn s0 sm := by simpa [allocFailedIn, htr] using halloc
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, spec.onPanic x s sm ∗ F,
      by simpa only [sepConj_assoc] using hpost, addrPanicAllow_of_eq halloc0⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hpost).elim
  · exact (hoom sm (F ∗ R) hoom_s hpost).elim

end CryptoVerification.SignalSession.Cli.MainHops.Address.Helpers
