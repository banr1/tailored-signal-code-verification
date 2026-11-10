/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.Frame
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Frame & Call Helpers for `get_kyber_pre_key::{closure#0}`

Provides relocatable stack-frame partitions and `SepWPp` call helpers for Block `576` under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.KpkGetPoll.Helpers

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

open CliKpkGetPollNorm

theorem kpk_call_lscro [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    {α : Type} {callee_pc ret_pc : BitVec 64} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog callee_pc (StoreKit.withLsCodeRoLoaded lsmpl spec))
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
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
      allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hnext : ∀ sf : State,
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (KpkPanicAllow s0)) :
    SepWPp prog ret s P Q (KpkPanicAllow s0) := by
  intro R hm hL
  have hm_pre : s.mem ⊨ (spec.pre x s ∗ F) ∗ R :=
    Satisfies.mono (sepConj_mono_left hP) hm
  have hpre : s.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F ∗ R) :=
    satisfies_lscro_pre hcrl (by simpa only [sepConj_assoc] using hm_pre)
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hpre hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ |
      ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · dsimp only [StoreKit.withLsCodeRoLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm (hcrl.of_keepsFrozen hsteps.keepsFrozen) hpcm hrunm hspm hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [StoreKit.withLsCodeRoLoaded] at hpost
    have halloc0 := hpanic sm (F ∗ R) hpan hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, spec.onPanic x s sm ∗ F,
      by simpa only [sepConj_assoc] using hpost,
      kpkPanicAllow_of_eq halloc0⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hpost).elim
  · exact (hoom sm (F ∗ R) hoom_s hpost).elim

end CryptoVerification.SignalSession.Cli.Store.KpkGetPoll.Helpers
