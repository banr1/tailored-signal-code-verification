/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2IfacePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.Helpers
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Call and Frame Helpers for `main_m2` Dispatch

Provides `.keepsFs` callee corollaries from `MainCalleesBlk617` and the `main_call_keepsFs_placed`
combinator preserving `InMainPlaced` and `sf.fs = s.fs` on Block `617`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.MainHops.Proofs

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli.MainHops

/-! ## 1. `.keepsFs` callee corollaries from `MainCalleesBlk617` -/

theorem address_keepsFs_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {uuidParse : UuidParser}
    {hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpec A uuidParse resStack).keepsFs) := by
  intro x R s1 hpc hrun hpre hsp hL
  obtain ⟨sm, hsteps, hout⟩ := subroutine_ok_apply_outcome hc.address x R hpc hrun hpre hsp hL
  refine ⟨sm, hsteps, ?_⟩
  rcases hout with ⟨hret, hcs, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcs, ?_⟩
    dsimp only [withLsRoCl, Spec.keepsFs, addressSpec] at hpost ⊢
    let tail : SepProp :=
      (x.p ↦ₛ x.bs) ∗ A.pool ∗ stackAt s1.sp resStack ∗
        (match addrParse uuidParse x.bs with
         | none => (x.out ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.out + 8#64) 24
         | some a => ∃∗ g : AddrGhost,
             ⌜g.name.bytes = a.name ∧ g.name.cap = BitVec.ofNat 64 a.name.length ∧
               g.device = a.device⌝ ∗ protocolAddressAt A g x.out)
    change sm.mem ⊨ (⌜LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗
      ⌜sm.trace = s1.trace ∧ sm.fs = s1.fs⌝ ∗ tail) ∗ R at hpost
    change sm.mem ⊨ (⌜LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗
      ⌜sm.fs = s1.fs⌝ ∗ ⌜sm.trace = s1.trace ∧ sm.fs = s1.fs⌝ ∗ tail) ∗ R
    have ha1 : (⌜LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗
        ⌜sm.trace = s1.trace ∧ sm.fs = s1.fs⌝ ∗ tail) ∗ R =
        ⌜sm.trace = s1.trace ∧ sm.fs = s1.fs⌝ ∗
          (⌜LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗ tail ∗ R) := by ac_rfl
    have ha2 : (⌜LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗
        ⌜sm.fs = s1.fs⌝ ∗ ⌜sm.trace = s1.trace ∧ sm.fs = s1.fs⌝ ∗ tail) ∗ R =
        ⌜sm.fs = s1.fs⌝ ∗ (⌜sm.trace = s1.trace ∧ sm.fs = s1.fs⌝ ∗
          (⌜LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗ tail ∗ R)) := by ac_rfl
    rw [ha1, satisfies_pure_sepConj] at hpost
    rw [ha2, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨hpost.1.2, hpost.1, hpost.2⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem dealloc_keepsFs_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {uuidParse : UuidParser}
    {hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustDeallocSymCli)
      (withLsRoCl lsmpl (rustDeallocExternSpecWithStack A extHookStack).keepsFs) :=
  main_dealloc_fs_placed_ok hc.allocFs

theorem memcpy_keepsFs_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {uuidParse : UuidParser}
    {hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ memcpyName)
      (withLsRoCl lsmpl session2MemcpySpecX.keepsFs) :=
  main_memcpy2_fs_placed_ok hc.allocFs

/-! ## 2. `SepWPp` call combinator preserving `InMainPlaced` and `sf.fs = s.fs` -/

theorem main_call_keepsFs_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {α : Type} {H : LibsignalHooks}
    {entry ret : BitVec 64} {k_ret : Nat} {spec : Spec α} {s0 s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp} (x : α)
    (hcall : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) entry
      (withLsRoCl lsmpl spec.keepsFs))
    (hinv : CodeOk s.mem) (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize) (hfp_eq : s.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (hsp0 : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = (blkPl_617).base + BitVec.ofNat 64 k_ret)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F) := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sf : State, InMainPlaced CodeOk s0 sf k_ret → CalleeSavedPreserved s sf → sf.fs = s.fs →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret sf (spec.post x s sf ∗ F) Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s P Q Qp oom := by
  have hspA : s.spAligned = true := by
    simp only [State.spAligned, hsp_eq, mainFrameSize]
    exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hsp0
  refine main_call_rocl (s0 := s0) (CodeOk := CodeOk) (spec := spec.keepsFs)
    x hcall hinv hpc hrun hspA hlr hP hpanic hexit hoom ?_
  intro sf hinv' hpcm hrunm hspm hcsm
  have hin : InMainPlaced CodeOk s0 sf k_ret :=
    ⟨by simpa only [mPcPlaced_eq] using hpcm,
     hrunm, hspm.trans hsp_eq, hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hfp_eq, hinv',
     hcsm.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, hsp0⟩
  intro R hm hL
  dsimp only [Spec.keepsFs] at hm
  have hassoc : ((⌜sf.fs = s.fs⌝ ∗ spec.post x s sf) ∗ F) ∗ R =
      ⌜sf.fs = s.fs⌝ ∗ ((spec.post x s sf ∗ F) ∗ R) := by ac_rfl
  rw [hassoc, satisfies_pure_sepConj] at hm
  exact hnext sf hin hcsm hm.1 R hm.2 hL

end CryptoVerification.SignalSession.Cli.MainHops.Proofs
