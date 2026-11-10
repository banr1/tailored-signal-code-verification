/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.ModelAndLayout
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Stage 1 Control, Call, and Vtable Combinators

Provides `[LibsignalPlacement]` control-invariant, `withFsInv` / `withLsCodeRoLoaded` call
combinators (`initCallPlaced`, `initCallLscro`, `sepWPp_step_lscro`), and `.rodata` vtable slot
introduction lemmas for `cliIdentityVtSym`, `idTrustFutVtSym`, `cliSessionVtSym`, and
`sessLoadFutVtSym`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas

open Arm64 Arm64.Obj Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunGlue
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

/-! ## Control invariant and call combinators -/

theorem InInitiatePlaced.spAligned_cur [LibsignalPlacement] {s0 s : State} {k : Nat}
    (h : InInitiatePlaced s0 s k) : s.spAligned = true := by
  have hal := h.spAligned
  simp only [State.spAligned, beq_iff_eq] at hal ⊢
  rw [h.sp, show cliInitiateFrame = 7408 from rfl]
  have hmod0 : s0.sp.toNat % 16 = 0 := by
    have ht := congrArg BitVec.toNat hal
    rw [BitVec.toNat_and, show (15#64).toNat = 2 ^ 4 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show (0#64).toNat = 0 from rfl] at ht
    exact ht
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (15#64).toNat = 2 ^ 4 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, show (0#64).toNat = 0 from rfl, BitVec.toNat_sub,
    show (7408#64).toNat = 7408 from rfl]
  have hlt : s0.sp.toNat < 2 ^ 64 := s0.sp.isLt
  omega

theorem InInitiatePlaced.of_call [LibsignalPlacement] {s0 s sm : State}
    {k k' : Nat} (h : InInitiatePlaced s0 s k)
    (hpc : sm.pc = initPcPlaced k')
    (hrun : sm.status = .Running)
    (hsp : sm.sp = s.sp)
    (hcs : CalleeSavedPreserved s sm)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem)
    (hfs : sm.fs.files = s0.fs.files) :
    InInitiatePlaced s0 sm k' where
  pc := hpc
  run := hrun
  sp := hsp.trans h.sp
  fp := hcs.2.2.2.2.2.2.2.2.2.2.1.trans h.fp
  x19 := hcs.1.trans h.x19
  files0 := hfs
  inv := hinv
  vregs := hcs.2.2.2.2.2.2.2.2.2.2.2.trans h.vregs
  spAligned := h.spAligned

theorem pure_sepConj_right_intro {φ : Prop} {P Q : SepProp} (hφ : φ) (h : P ⊢ Q) :
    P ⊢ Q ∗ ⌜φ⌝ := by
  rw [sepConj_comm]
  exact pure_sepConj_intro hφ h

theorem initCallPlaced [LibsignalPlacement] {α : Type} {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State} {callee_pc ret_pc : BitVec 64}
    {spec : Spec α} {gx : α} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) callee_pc spec)
    (hpc : s.pc = callee_pc)
    (hrun : s.status = .Running)
    (hal : s.spAligned = true)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hfs : s.fs.files = s0.fs.files)
    (hlr : s.readReg64 .lr = ret_pc)
    (hpre : P ⊢ spec.pre gx s ∗ F)
    (hpan : ∀ sf, spec.onPanic gx s sf ⊢ ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = s.sp →
      CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      (sm.trace = s0.trace → sm.fs.files = s0.fs.files) →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm (spec.post gx s sm ∗ F) Q Qp (initOom s0))
    (hexit : ∀ code sf, spec.onExit gx code s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, spec.onOom gx s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  intro R hm hL
  have hfsInv0 : FsInv s0.fs.files s0.trace s := by
    rw [← hfs, ← htr]
    exact withFsInv_entry s
  have hcallFs := subroutine_ok_withFsInv (hh.fs (prog := initProgPlaced mmpl gh W)) hcall s0.fs.files s0.trace
  have hmPre : s.mem ⊨ (withFsInv spec s0.fs.files s0.trace).pre gx s ∗ (F ∗ R) := by
    refine withFsInv_pre_intro hfsInv0 ?_
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hpre) hm
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcallFs gx (F ∗ R) hpc hrun hmPre hal hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · obtain ⟨hfsInvm, hpost'⟩ := withFsInv_post_elim hpost
    rw [← sepConj_assoc] at hpost'
    rw [hlr] at hpcm
    have hinvm : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem :=
      hinv.of_keepsFrozen hsteps.keepsFrozen
    have hfsm : sm.trace = s0.trace → sm.fs.files = s0.fs.files := fun htm =>
      hfsInvm.files_eq (evs := []) (by simp [htm]) NoFsEv.nil
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm hinvm hfsm R hpost' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · change sm.mem ⊨ (⌜FsInv s0.fs.files s0.trace sm⌝ ∗ spec.onPanic gx s sm) ∗ (F ∗ R) at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨_, hpanMem⟩ := hpost
    have hm1 : sm.mem ⊨ (⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap) ∗ (F ∗ R) :=
      Satisfies.mono (sepConj_mono_left (hpan sm)) hpanMem
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1
    obtain ⟨⟨hA, _⟩, hmAny⟩ := hm1
    have hA0 : allocFailedIn s0 sm := by
      unfold allocFailedIn at hA ⊢
      rwa [htr] at hA
    have hmFinal : sm.mem ⊨ ((initSlotSpecPlaced A S stk).onPanic x s0 sm) ∗ R := by
      dsimp only [initSlotSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨Or.inr hA0,
        Satisfies.mono (by rw [← sepConj_assoc]; exact sepConj_mono_left (entails_anyHeap _)) hmAny⟩
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, (initSlotSpecPlaced A S stk).onPanic x s0 sm, hmFinal,
      hpanic sm _ (Entails.refl _)⟩)⟩
  · change sm.mem ⊨ (⌜FsInv s0.fs.files s0.trace sm⌝ ∗ spec.onExit gx code s sm) ∗ (F ∗ R) at hpost
    rw [hexit, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact (not_satisfies_false_sepConj hpost.2).elim
  · change sm.mem ⊨ (⌜FsInv s0.fs.files s0.trace sm⌝ ∗ spec.onOom gx s sm) ∗ (F ∗ R) at hpost
    rw [hoom, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact (not_satisfies_false_sepConj hpost.2).elim

/-- Calls a `StoreKit.withLsCodeRoLoaded lsmpl inner` callee inside `initProgPlaced`. -/
theorem initCallLscro [LibsignalPlacement] {α : Type} {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State} {callee_pc ret_pc : BitVec 64}
    {inner : Spec α} {gx : α} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) callee_pc
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl inner))
    (hpc : s.pc = callee_pc)
    (hrun : s.status = .Running)
    (hal : s.spAligned = true)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hfs : s.fs.files = s0.fs.files)
    (hlr : s.readReg64 .lr = ret_pc)
    (hpre : P ⊢ inner.pre gx s ∗ F)
    (hpan : ∀ sf, inner.onPanic gx s sf ⊢
      ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap := by intros; exact false_entails _)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = s.sp →
      CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      (sm.trace = s0.trace → sm.fs.files = s0.fs.files) →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm (inner.post gx s sm ∗ F) Q Qp (initOom s0))
    (hexit : ∀ code sf, inner.onExit gx code s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, inner.onOom gx s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp (initOom s0) :=
  initCallPlaced hh hpanic hcall hpc hrun hal hinv htr hfs hlr
    (Entails.trans hpre (sepConj_mono_left (pure_sepConj_right_intro hinv (Entails.refl _))))
    hpan hnext hexit hoom

/-- Steps a `SepWP` segment inside `SepWPp` while threading `StoreKit.LibsignalCodeRoLoaded`. -/
theorem sepWPp_step_lscro {prog : Program} {pl : MultiPlacement} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (h : SepWP prog mid s P
      (fun sm Pm => LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded pl sm.mem →
        SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext (hinv.of_keepsFrozen hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

/-! ## Read-only vtable slot introduction lemmas -/

theorem rodata_idVt_trustSlot_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {stk : Nat} {s : State}
    (hStore : InitStoreCalleesPlaced A mmpl gh W B stk)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ ((lsρ cliIdentityVtSym + 48#64) ↦₆₄ᵣ lsmpl.base 601) ∗ R) :=
  fun _ hR => hStore.rodata_idVt_trustSlot hinv.2 hR

theorem rodata_idTrustFut_drop_placed' [LibsignalPlacement] {s : State}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ ((lsρ idTrustFutVtSym) ↦₆₄ᵣ lsmpl.base 547) ∗ R) :=
  fun _ hR => StoreCalleesProofs.rodata_idTrustFut_drop_placed hinv.2 hR

theorem rodata_idTrustFut_size_placed' [LibsignalPlacement] {s : State}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ (((lsρ idTrustFutVtSym) + 8#64) ↦₆₄ᵣ 32#64) ∗ R) :=
  fun _ hR => StoreCalleesProofs.rodata_idTrustFut_size_placed hinv.2 hR

theorem rodata_idTrustFut_align_placed' [LibsignalPlacement] {s : State}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ (((lsρ idTrustFutVtSym) + 16#64) ↦₆₄ᵣ 8#64) ∗ R) :=
  fun _ hR => StoreCalleesProofs.rodata_idTrustFut_align_placed hinv.2 hR

theorem rodata_idTrustFut_poll_placed' [LibsignalPlacement] {s : State}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ (((lsρ idTrustFutVtSym) + 24#64) ↦₆₄ᵣ lsmpl.base 566) ∗ R) :=
  fun _ hR => StoreCalleesProofs.rodata_idTrustFut_poll_placed hinv.2 hR

theorem rodata_sessVt_loadSlot_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {stk : Nat} {s : State}
    (hStore : InitStoreCalleesPlaced A mmpl gh W B stk)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ ((lsρ cliSessionVtSym + 24#64) ↦₆₄ᵣ lsmpl.base 604) ∗ R) :=
  fun _ hR => hStore.rodata_sessVt_loadSlot hinv.2 hR

theorem rodata_sessLoadFut_drop_placed' [LibsignalPlacement] {s : State}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ ((lsρ sessLoadFutVtSym) ↦₆₄ᵣ lsmpl.base 547) ∗ R) :=
  fun _ hR => StoreCalleesProofs.rodata_sessLoadFut_drop_placed hinv.2 hR

theorem rodata_sessLoadFut_size_placed' [LibsignalPlacement] {s : State}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ (((lsρ sessLoadFutVtSym) + 8#64) ↦₆₄ᵣ 24#64) ∗ R) :=
  fun _ hR => StoreCalleesProofs.rodata_sessLoadFut_size_placed hinv.2 hR

theorem rodata_sessLoadFut_align_placed' [LibsignalPlacement] {s : State}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ (((lsρ sessLoadFutVtSym) + 16#64) ↦₆₄ᵣ 8#64) ∗ R) :=
  fun _ hR => StoreCalleesProofs.rodata_sessLoadFut_align_placed hinv.2 hR

theorem rodata_sessLoadFut_poll_placed' [LibsignalPlacement] {s : State}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ (((lsρ sessLoadFutVtSym) + 24#64) ↦₆₄ᵣ lsmpl.base 569) ∗ R) :=
  fun _ hR => StoreCalleesProofs.rodata_sessLoadFut_poll_placed hinv.2 hR

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
