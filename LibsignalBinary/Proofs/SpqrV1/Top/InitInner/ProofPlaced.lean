/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.Proof
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5Placed
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.TopLeafCodeSym
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbOuter
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.StepsPlaced
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply

/-!
# `spqr::init_inner` (`Block 324`): Relocatable `[LibsignalPlacement]` Verification

Proves the relocatable `[LibsignalPlacement]` verification theorems for `spqr::init_inner` (`Block 324`):
- `init_inner_placed_ok_ext` against `initInnerPlacedSpec A F`
- `init_inner_placed_ok_x` against `withLsCodeLoaded lsmpl (initInnerPlacedSpecX A F)`
- `init_inner_placed_ok_blockProgram` (`InitInnerPlacedOkX A F ext`)
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.InitInner

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.Placed
open CryptoVerification.SpqrV1.States.IntoPb.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'

/-! ## 1. Subroutine Call Wrappers (`SepWPp`) on `Block 324` -/

/-- Return postcondition of relocatable `spqr::init_inner` (`Block 324`) for `SepWPp`. -/
def InitInnerPlacedPost [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (s0 : State) (x : InitInnerGhost) : State → SepProp → Prop :=
  fun sf Pf =>
    (Pf ⊢
      initInnerResultAt A (F := F) x.out x.v x.d x.authKey ∗
      (x.akPtr ↦ₛ x.authKey) ∗ statesIntoPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp initInnerStack) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace

theorem sepWPp_of_init_inner_placed_wpp [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (s0 s : State) (x : InitInnerGhost) (P R : SepProp)
    (hwpp : SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (InitInnerPlacedPost A F s0 x) (InitInnerPanic s0 R)) :
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (initInnerPlacedSpec A F).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (initInnerPlacedSpec A F).onPanic x s0 sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, ⟨hent, hspf, hcsf, htrf⟩⟩ | ⟨hpan, P_f, hmf, hqp⟩ | hoom⟩ :=
    hwpp R' hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, ⟨?_, hspf, hcsf⟩⟩⟩
    intro hmR; dsimp only [initInnerPlacedSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htrf, by simpa [sepConj_assoc] using Satisfies.mono (sepConj_mono_left hent) hmR⟩
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hmf, ?_⟩)⟩
    intro hmR; dsimp only [initInnerPlacedSpec, initInnerOnPanic]
    simpa [sepConj_assoc] using hqp hmR
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem sepWPp_of_sepWP_keepLsInv [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun sm Pm =>
      (LibsignalCodeLoaded lsmpl s.mem → LibsignalCodeLoaded lsmpl sm.mem) →
      (LsCallInv lsmpl s.mem → LsCallInv lsmpl sm.mem) →
      SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | hoom⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ := hnext
      (fun hcl => hcl.of_keepsFrozen hsteps.keepsFrozen)
      (fun hinv => hinv.of_steps hsteps)
      R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem initInner_seq_sepWP_lsInv [LibsignalPlacement] {prog : Program} {ret mid : BitVec 64} {s : State}
    {P P' : SepProp} {Post : State → Prop} {Q Qp : State → SepProp → Prop}
    (hstep : SepWP prog mid s P (fun s' P1 => (P1 ⊢ P') ∧ Post s'))
    (hnext : ∀ s' : State, s'.pc = mid → s'.status = .Running →
      (LibsignalCodeLoaded lsmpl s.mem → LibsignalCodeLoaded lsmpl s'.mem) →
      (LsCallInv lsmpl s.mem → LsCallInv lsmpl s'.mem) → Post s' →
      SepWPp prog ret s' P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine sepWPp_of_sepWP_keepLsInv (mid := mid) ?_
  refine SepWP.mono hstep fun s' P1 hpc' hrun' ⟨hent, hpost⟩ hcode' hinv' =>
    SepWPp.weaken_pre hent (hnext s' hpc' hrun' hcode' hinv' hpost)

theorem sepWPp_call_keepLsInv [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F : SepProp}
    {post Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ code sf R, sf.status = .Exited code → ¬ (sf.mem ⊨ spec.onExit x code s sf ∗ (F ∗ R)))
    (hpan : ∀ sf, Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      (LibsignalCodeLoaded lsmpl s.mem → LibsignalCodeLoaded lsmpl sf.mem) →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro sf; first | rfl | simp only [withLsCallInv, withLsCodeLoaded]) :
    SepWPp prog target_pc s P post Qp := by
  let spec' : Spec α :=
    { pre := fun a st => spec.pre a st ∗ F
      post := fun a st sf => spec.post a st sf ∗ F
      onPanic := fun a st sf => spec.onPanic a st sf ∗ F
      onExit := fun a code st sf => spec.onExit a code st sf ∗ F
      onOom := fun a st sf => spec.onOom a st sf ∗ F }
  have hcall' : subroutine_ok prog entry spec' := by
    apply subroutine_ok_outcome_intro
    intro a R0 s0 hpc0 hrun0 hpre0 hsp0
    dsimp only [spec'] at hpre0
    rw [sepConj_assoc] at hpre0
    refine subroutine_ok.mono_outcome hcall a (F ∗ R0) s0 hpc0 hrun0 hpre0 hsp0 ?_
    rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan0, hpost⟩ | ⟨code, hex0, hpost⟩ | ⟨hoom0, hpost⟩)
    · dsimp only [spec']; rw [← sepConj_assoc] at hpost; exact Or.inl ⟨hret, hcc, hpost⟩
    · dsimp only [spec']; rw [← sepConj_assoc] at hpost; exact Or.inr (Or.inl ⟨hpan0, hpost⟩)
    · dsimp only [spec']; rw [← sepConj_assoc] at hpost; exact Or.inr (Or.inr (Or.inl ⟨code, hex0, hpost⟩))
    · dsimp only [spec']; rw [← sepConj_assoc] at hpost; exact Or.inr (Or.inr (Or.inr ⟨hoom0, hpost⟩))
  have h1 : SepWPp prog ret_pc s P
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ Pm = (spec.post x s sm ∗ F) ∗ emp)
      Qp := by
    refine SepWPp.call (x := x) (F := emp) hcall' hpc hrun hsp_align hlr
      (fun R0 hm0 => by
        dsimp only [spec']
        rw [emp_sepConj]
        have hm1 := hpre R0 hm0
        rwa [← sepConj_assoc] at hm1)
      (fun sf code R0 hex_st hpost => by
        dsimp only [spec'] at hpost
        rw [sepConj_assoc] at hpost
        exact hexit code sf R0 hex_st hpost)
      (fun sm _ => by
        dsimp only [spec']
        rw [sepConj_emp]
        exact hpan sm)
      (fun sm hpcm hrunm hspm hcsm => SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sf R0 _ hpost => by
        dsimp only [spec'] at hpost
        rw [hoom_false sf, emp_sepConj, sepConj_assoc] at hpost
        exact (not_satisfies_false_sepConj hpost).elim)
  intro R' hm hL
  rcases h1 R' hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hpost, hspm, hcsm, rfl⟩ | hpan_out | hoom_out⟩
  · rw [sepConj_emp] at hpost
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (fun hcl => hcl.of_keepsFrozen hsteps.keepsFrozen) R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan_out)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom_out)⟩

theorem call_authNew_placed_ext [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hauth_raw : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) (authNewSpec F A))
    (authKey : Bytes) (hlt : 32 + authKey.length < 2 ^ 63)
    {Q : State → SepProp → Prop}
    (s0 s : State) (ret_pc : BitVec 64) (P Frame R : SepProp)
    (hpc : s.pc = lsmpl.base 340)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1040#64)
    (hsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = s0.sp - 104#64) (hx1 : s.readReg64 .x1 = s0.sp - 1032#64)
    (hsplit : P = (memRegion (s0.sp - 104#64) authenticatorSize ∗
      vecU8 A (s0.sp - 1032#64) authKey ∗ A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackX) ∗ Frame)
    (hnext : ∀ (sf : State) (a0 a1 a2 a3 a4 a5 : BitVec 64),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp - 1040#64 →
      (LibsignalCodeLoaded lsmpl s.mem → LibsignalCodeLoaded lsmpl sf.mem) →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (((((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗ ((s0.sp - 88#64) ↦₆₄ a2) ∗
           ((s0.sp - 80#64) ↦₆₄ a3) ∗ ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
          authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
          memRegion (s0.sp - 1032#64) 24 ∗ A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackX) ∗ Frame)
        Q (InitInnerPanic s0 R)) :
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P Q (InitInnerPanic s0 R) := by
  refine sepWPp_call_keepLsInv hauth_raw (x := ⟨s0.sp - 104#64, s0.sp - 1032#64, authKey⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h) (fun sf => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm; rw [hsplit] at hm; dsimp only [authNewSpec]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢; exact ⟨⟨hx0, hx1, hlt⟩, hm⟩
  · change (sf.mem ⊨ ((authNewSpec F A).onPanic ⟨s0.sp - 104#64, s0.sp - 1032#64, authKey⟩ s sf ∗ Frame) ∗ R) →
      (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)
    intro hmem; dsimp only [authNewSpec] at hmem; rw [← sepConj_assoc]
    have hpan := allowPanic_frame (φ := allocFailedIn s sf ∧ s.trace <+: sf.trace)
      (ψ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      (fun ⟨haf, htr_sub⟩ => by unfold allocFailedIn at haf ⊢; rw [htrace] at haf htr_sub; exact ⟨haf, htr_sub⟩) hmem
    simpa only [sepConj_assoc] using hpan
  · dsimp only [authNewSpec]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    refine SepWPp.weaken_pre (authenticatorAt_expose_frame A F s0.sp authKey Frame) ?_
    refine SepWPp.exists_elim fun a0 => SepWPp.exists_elim fun a1 =>
      SepWPp.exists_elim fun a2 => SepWPp.exists_elim fun a3 =>
      SepWPp.exists_elim fun a4 => SepWPp.exists_elim fun a5 => ?_
    exact hnext sf a0 a1 a2 a3 a4 a5 hpc_sf hrun_sf (by rw [hsp_sf, hsp])
      hinv_sf hcs_sf (by rw [htr, htrace])

theorem call_authNew_placed_x [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hauth_raw : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) (withLsCallInv lsmpl (authNewSpec F A)))
    (authKey : Bytes) (hlt : 32 + authKey.length < 2 ^ 63)
    {Q : State → SepProp → Prop}
    (s0 s : State) (ret_pc : BitVec 64) (P Frame R : SepProp) (hinv : LsCallInv lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 340)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1040#64)
    (hsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = s0.sp - 104#64) (hx1 : s.readReg64 .x1 = s0.sp - 1032#64)
    (hsplit : P = (memRegion (s0.sp - 104#64) authenticatorSize ∗
      vecU8 A (s0.sp - 1032#64) authKey ∗ A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackX) ∗ Frame)
    (hnext : ∀ (sf : State) (a0 a1 a2 a3 a4 a5 : BitVec 64),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp - 1040#64 →
      (LibsignalCodeLoaded lsmpl s.mem → LibsignalCodeLoaded lsmpl sf.mem) →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (((((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗ ((s0.sp - 88#64) ↦₆₄ a2) ∗
           ((s0.sp - 80#64) ↦₆₄ a3) ∗ ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
          authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
          memRegion (s0.sp - 1032#64) 24 ∗ A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackX) ∗ Frame)
        Q (InitInnerPanic s0 R)) :
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P Q (InitInnerPanic s0 R) := by
  refine sepWPp_call_keepLsInv hauth_raw (x := ⟨s0.sp - 104#64, s0.sp - 1032#64, authKey⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h) (fun sf => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm; rw [hsplit] at hm; dsimp only [withLsCallInv, authNewSpec]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢; exact ⟨hinv, ⟨hx0, hx1, hlt⟩, hm⟩
  · change (sf.mem ⊨ ((withLsCallInv lsmpl (authNewSpec F A)).onPanic ⟨s0.sp - 104#64, s0.sp - 1032#64, authKey⟩ s sf ∗ Frame) ∗ R) →
      (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)
    intro hmem; dsimp only [withLsCallInv, authNewSpec] at hmem; rw [← sepConj_assoc]
    have hpan := allowPanic_frame (φ := allocFailedIn s sf ∧ s.trace <+: sf.trace)
      (ψ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      (fun ⟨haf, htr_sub⟩ => by unfold allocFailedIn at haf ⊢; rw [htrace] at haf htr_sub; exact ⟨haf, htr_sub⟩) hmem
    simpa only [sepConj_assoc] using hpan
  · dsimp only [withLsCallInv, authNewSpec]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    refine SepWPp.weaken_pre (authenticatorAt_expose_frame A F s0.sp authKey Frame) ?_
    refine SepWPp.exists_elim fun a0 => SepWPp.exists_elim fun a1 =>
      SepWPp.exists_elim fun a2 => SepWPp.exists_elim fun a3 =>
      SepWPp.exists_elim fun a4 => SepWPp.exists_elim fun a5 => ?_
    exact hnext sf a0 a1 a2 a3 a4 a5 hpc_sf hrun_sf (by rw [hsp_sf, hsp])
      hinv_sf hcs_sf (by rw [htr, htrace])

theorem call_statesIntoPb_placed_ext [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)} {st : States spqrPolyApi (spqrAuthApi F)}
    (hinto_raw : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 334) (statesIntoPbPlacedSpec A F))
    (out : BitVec 64) {s0 s : State} {ret_pc : BitVec 64} {P Frame R : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 334)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1040#64)
    (hsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc) (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = out) (hx0 : s.readReg64 .x0 = s0.sp - 1032#64)
    (hsplit : P = (memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A (s0.sp - 1032#64) st ∗ statesIntoPbJumpTablePlacedAt ∗ A.pool ∗
      stackAt (s0.sp - 1040#64) statesIntoPbStack) ∗ Frame)
    (hnext : ∀ (sf : State),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp - 1040#64 →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        ((optProtoInnerStateAt A out st.into_pb.innerState ∗
          memRegion (s0.sp - 1032#64) chunkedStatesSize ∗ statesIntoPbJumpTablePlacedAt ∗
          A.pool ∗ stackAt (s0.sp - 1040#64) statesIntoPbStack) ∗ Frame)
        Q (InitInnerPanic s0 R)) :
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P Q (InitInnerPanic s0 R) := by
  refine SepWPp.call hinto_raw (x := ⟨out, s0.sp - 1032#64, st⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h) (fun sf _ => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm; rw [hsplit] at hm; dsimp only [statesIntoPbPlacedSpec]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢; exact ⟨⟨hx8, hx0⟩, hm⟩
  · change (sf.mem ⊨ ((statesIntoPbPlacedSpec A F).onPanic ⟨out, s0.sp - 1032#64, st⟩ s sf ∗ Frame) ∗ R) →
      (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)
    intro hmem; dsimp only [statesIntoPbPlacedSpec, statesIntoPbOnPanic] at hmem; rw [← sepConj_assoc]
    have hpan := allowPanic_frame (φ := allocFailedIn s sf ∧ s.trace <+: sf.trace)
      (ψ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      (fun ⟨haf, htr_sub⟩ => by unfold allocFailedIn at haf ⊢; rw [htrace] at haf htr_sub; exact ⟨haf, htr_sub⟩) hmem
    simpa only [sepConj_assoc] using hpan
  · dsimp only [statesIntoPbPlacedSpec]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    have hnext' := hnext sf hpc_sf hrun_sf (by rw [hsp_sf, hsp]) hcs_sf (by rw [htr, htrace])
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) hnext'

theorem call_statesIntoPb_placed_x [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)} {st : States spqrPolyApi (spqrAuthApi F)}
    (hinto_raw : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 334) (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpec A F)))
    (out : BitVec 64) {s0 s : State} {ret_pc : BitVec 64} {P Frame R : SepProp}
    {Q : State → SepProp → Prop} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 334)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1040#64)
    (hsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc) (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = out) (hx0 : s.readReg64 .x0 = s0.sp - 1032#64)
    (hsplit : P = (memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A (s0.sp - 1032#64) st ∗ statesIntoPbJumpTablePlacedAt ∗ A.pool ∗
      stackAt (s0.sp - 1040#64) statesIntoPbStack) ∗ Frame)
    (hnext : ∀ (sf : State),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp - 1040#64 →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        ((optProtoInnerStateAt A out st.into_pb.innerState ∗
          memRegion (s0.sp - 1032#64) chunkedStatesSize ∗ statesIntoPbJumpTablePlacedAt ∗
          A.pool ∗ stackAt (s0.sp - 1040#64) statesIntoPbStack) ∗ Frame)
        Q (InitInnerPanic s0 R)) :
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P Q (InitInnerPanic s0 R) := by
  refine SepWPp.call hinto_raw (x := ⟨out, s0.sp - 1032#64, st⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h) (fun sf _ => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm; rw [hsplit] at hm; dsimp only [withLsCodeLoaded, statesIntoPbPlacedSpec]; rw [hsp]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢; exact ⟨⟨hx8, hx0⟩, hm⟩
  · change (sf.mem ⊨ ((withLsCodeLoaded lsmpl (statesIntoPbPlacedSpec A F)).onPanic ⟨out, s0.sp - 1032#64, st⟩ s sf ∗ Frame) ∗ R) →
      (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)
    intro hmem; dsimp only [withLsCodeLoaded, statesIntoPbPlacedSpec, statesIntoPbOnPanic] at hmem; rw [← sepConj_assoc]
    have hpan := allowPanic_frame (φ := allocFailedIn s sf ∧ s.trace <+: sf.trace)
      (ψ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      (fun ⟨haf, htr_sub⟩ => by unfold allocFailedIn at haf ⊢; rw [htrace] at haf htr_sub; exact ⟨haf, htr_sub⟩) hmem
    simpa only [sepConj_assoc] using hpan
  · dsimp only [withLsCodeLoaded, statesIntoPbPlacedSpec]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    have hnext' := hnext sf hpc_sf hrun_sf (by rw [hsp_sf, hsp]) hcs_sf (by rw [htr, htrace])
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) hnext'

/-- OOM panic block of `spqr::init_inner` (`Block 324`) at `+436` (`mov w0, #1; mov x1, x20; bl handle_error`). -/
theorem init_inner_panic_436_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_324).base + 436#64)
    (hrun : s.status = .Running) (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q (InitInnerPanic s0 R) := by
  have hpanic : ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)).externAt?
      (lsmpl.ρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked :=
    (ls_externAt?_of_mem (prog := (blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (i := 324) (H := Rust.withPanics ext) (sym := "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")).trans
      h_panic
  apply SepWPp.of_sepWP (mid := lsmpl.ρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [InitInnerPanic, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

/-- `.a2b` slice-clone (`+36 -> +364`) on `Block 324`. -/
theorem init_inner_clone_a2b_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (h_panic : (Rust.withPanics ext) "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" = some Rust.panicked)
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpySpec)
    (s0 s : State) (out akPtr : BitVec 64) (authKey : Bytes) (Frame R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hlt : authKey.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_324).base + 36#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 authKey.length)
    (hw2 : s.readReg32 .x2 = Direction.a2b.toI32) (hx3 : s.readReg64 .x3 = akPtr)
    (hcs_hi : s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htrace : s.trace = s0.trace)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_324).base + 364#64 →
      sm.status = .Running →
      (LibsignalCodeLoaded lsmpl s.mem → LibsignalCodeLoaded lsmpl sm.mem) →
      (LsCallInv lsmpl s.mem → LsCallInv lsmpl sm.mem) →
      sm.sp = s0.sp - 1040#64 → sm.readReg64 .x29 = s0.sp - 48#64 →
      sm.readReg64 .x19 = out → sm.readReg64 .x0 = s0.sp - 104#64 →
      sm.readReg64 .x1 = s0.sp - 1032#64 →
      (sm.readReg64 .x22 = s0.readReg64 .x22 ∧ sm.readReg64 .x23 = s0.readReg64 .x23 ∧
       sm.readReg64 .x24 = s0.readReg64 .x24 ∧ sm.readReg64 .x25 = s0.readReg64 .x25 ∧
       sm.readReg64 .x26 = s0.readReg64 .x26 ∧ sm.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs sm = calleeSavedVRegs s0) →
      sm.trace = s0.trace →
      SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) sm
        (vecU8 A (s0.sp - 1032#64) authKey ∗ (akPtr ↦ₛ authKey) ∗
         A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
        Q (InitInnerPanic s0 R)) :
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (cells (s0.sp - 1032#64) 3 ∗ (akPtr ↦ₛ authKey) ∗
       A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
      Q (InitInnerPanic s0 R) := by
  have hfsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  by_cases hlen_zero : authKey.length = 0
  · have hnil : authKey = [] := List.eq_nil_of_length_eq_zero hlen_zero
    subst hnil
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx20 hnext ⊢
    refine initInner_seq_sepWP_lsInv
      (init_inner_a2b_empty_to_364_placed (A := A) s0 s out
        ((akPtr ↦ₛ ([] : Bytes)) ∗ A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
        hsp0_align hpc hrun hsp hx29 hx19 hx20 hw2 hcs_hi htrace) ?_
    intro sm hpcm hrunm hcodem hinvm ⟨hspm, hx29m, hx19m, hx0m, hx1m, hcsm, htrm⟩
    exact hnext sm hpcm hrunm hcodem hinvm hspm hx29m hx19m hx0m hx1m hcsm htrm
  · refine SepWPp.weaken_pre (cells_1032_3_expose s0.sp _) ?_
    refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 => SepWPp.exists_elim fun w2 => ?_
    have hpos : 0 < authKey.length := Nat.pos_of_ne_zero hlen_zero
    have hbeq0 : (BitVec.ofNat 64 authKey.length == 0#64) = false := ofNat_beq_zero_false' hpos (by omega)
    have hne0 : (BitVec.ofNat 64 authKey.length != 0#64) = true := ofNat_ne_zero_true hpos (by omega)
    have htoNat_len : (BitVec.ofNat 64 authKey.length).toNat = authKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk authKey.length 1 := ⟨hpos, hpow2, by omega⟩
    have hpanic : ∀ (sm : State) (P_mid : SepProp),
        sm.pc = (blkPl_324).base + 436#64 →
        sm.status = .Running → sm.trace = s0.trace ++ [allocFailedEvent] →
        SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) sm P_mid Q (InitInnerPanic s0 R) :=
      fun sm P_mid hpcm hrunm htrm => init_inner_panic_436_placed h_panic s0 sm P_mid R hpcm hrunm htrm
    simp only [noAllocShimSpec] at hshim
    simp only [rustAllocSpec] at halloc
    simp only [framelessMemcpySpec] at hmemcpy
    rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
    dsimp only [Direction.toI32,
      State.readReg32, Reg.x2, BitVec.ofNat_eq_ofNat] at hpc hw2 hshim halloc hmemcpy hpanic ⊢
    refine sepWPp_of_sepWP_keepLsInv (mid := (blkPl_324).base + 144#64) ?_
    wp_steps; wp_apply; wp_steps; wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcode_sf1 hinv_sf1
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom, ↓reduceIte]
      refine CryptoVerification.SpqrV1.Poly.DecoderPb.sepWPp_pure_mid fun htr_oom => ?_
      refine CryptoVerification.SpqrV1.Poly.DecoderPb.SepWPp.seq_clean (mid := (blkPl_324).base + 436#64)
        (P_mid := A.pool ∗ stackAt sf.sp allocHookStack ∗ ((s0.sp - 1032#64) ↦₆₄ w0) ∗
          ((s0.sp - 1024#64) ↦₆₄ w1) ∗ ((s0.sp - 1016#64) ↦₆₄ w2) ∗ (akPtr ↦ₛ authKey) ∗ Frame)
        (Q_mid := fun sm => sm.trace = s0.trace ++ [allocFailedEvent]) ?_ ?_
      · wp_steps; wp_done
      · intro sm hpcm hrunm htrm; exact hpanic sm _ hpcm hrunm htrm
    · have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
      have hoom_bne : (sf_1.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hoom
      conv => arg 4; simp only [hoom, ↓reduceIte, htoNat_len]; simp only [sepConj_assoc]
      refine CryptoVerification.SpqrV1.Poly.DecoderPb.sepWPp_pure_mid fun ⟨_, htr_ok⟩ => ?_
      let ptr_c := sf_1.readReg64 (Reg.gpr 0#5)
      refine initInner_seq_sepWP_lsInv (mid := (blkPl_324).base + 364#64)
        (P' := vecU8 A (s0.sp - 1032#64) authKey ∗ (akPtr ↦ₛ authKey) ∗
          A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
        (Post := fun sm => sm.sp = s0.sp - 1040#64 ∧ sm.readReg64 .x29 = s0.sp - 48#64 ∧
          sm.readReg64 .x19 = out ∧ sm.readReg64 .x0 = s0.sp - 104#64 ∧
          sm.readReg64 .x1 = s0.sp - 1032#64 ∧
          (sm.readReg64 .x22 = s0.readReg64 .x22 ∧ sm.readReg64 .x23 = s0.readReg64 .x23 ∧
           sm.readReg64 .x24 = s0.readReg64 .x24 ∧ sm.readReg64 .x25 = s0.readReg64 .x25 ∧
           sm.readReg64 .x26 = s0.readReg64 .x26 ∧ sm.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs sm = calleeSavedVRegs s0) ∧
          sm.trace = s0.trace) ?_ ?_
      · wp_steps; wp_apply; wp_steps
        have hvec := vecU8_nonempty_of_cells A (s0.sp - 1032#64) ptr_c authKey hpos hlt hoom
        simp only [arm64_norm] at hvec
        have hent :
            (ptr_c ↦ₛ authKey) ∗ (akPtr ↦ₛ authKey) ∗ A.pool ∗ stackAt sf.sp allocHookStack ∗
            A.live ptr_c authKey.length 1 ∗ ((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
            ((s0.sp - 1024#64) ↦₆₄ ptr_c) ∗ ((s0.sp - 1016#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗ Frame ⊢
            vecU8 A (s0.sp - 1032#64) authKey ∗ (akPtr ↦ₛ authKey) ∗
            A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame := by
          rw [‹sf.sp = s.sp›, hsp]
          refine Entails.trans (Entails.of_eq (show _ =
            (((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗ ((s0.sp - 1024#64) ↦₆₄ ptr_c) ∗
             ((s0.sp - 1016#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗ A.live ptr_c authKey.length 1 ∗
             (ptr_c ↦ₛ authKey)) ∗
            ((akPtr ↦ₛ authKey) ∗ A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame) by ac_rfl)) ?_
          exact sepConj_mono_left hvec
        exact SepWP.weaken_pre hent (by wp_done)
      · intro sm hpcm hrunm hcodem hinvm ⟨hspm, hx29m, hx19m, hx0m, hx1m, hcsm, htrm⟩
        exact hnext sm hpcm hrunm (fun hc => hcodem (hcode_sf1 hc)) (fun hi => hinvm (hinv_sf1 hi))
          hspm hx29m hx19m hx0m hx1m hcsm htrm

/-- `.b2a` slice-clone (`+36 -> +192`) on `Block 324`. -/
theorem init_inner_clone_b2a_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (h_panic : (Rust.withPanics ext) "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" = some Rust.panicked)
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpySpec)
    (s0 s : State) (out akPtr : BitVec 64) (authKey : Bytes) (Frame R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hlt : authKey.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_324).base + 36#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 authKey.length)
    (hw2 : s.readReg32 .x2 = Direction.b2a.toI32) (hx3 : s.readReg64 .x3 = akPtr)
    (hcs_hi : s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htrace : s.trace = s0.trace)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_324).base + 192#64 →
      sm.status = .Running →
      (LibsignalCodeLoaded lsmpl s.mem → LibsignalCodeLoaded lsmpl sm.mem) →
      (LsCallInv lsmpl s.mem → LsCallInv lsmpl sm.mem) →
      sm.sp = s0.sp - 1040#64 → sm.readReg64 .x29 = s0.sp - 48#64 →
      sm.readReg64 .x19 = out → sm.readReg64 .x0 = s0.sp - 104#64 →
      sm.readReg64 .x1 = s0.sp - 1032#64 →
      (sm.readReg64 .x22 = s0.readReg64 .x22 ∧ sm.readReg64 .x23 = s0.readReg64 .x23 ∧
       sm.readReg64 .x24 = s0.readReg64 .x24 ∧ sm.readReg64 .x25 = s0.readReg64 .x25 ∧
       sm.readReg64 .x26 = s0.readReg64 .x26 ∧ sm.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs sm = calleeSavedVRegs s0) →
      sm.trace = s0.trace →
      SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) sm
        (vecU8 A (s0.sp - 1032#64) authKey ∗ (akPtr ↦ₛ authKey) ∗
         A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
        Q (InitInnerPanic s0 R)) :
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (cells (s0.sp - 1032#64) 3 ∗ (akPtr ↦ₛ authKey) ∗
       A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
      Q (InitInnerPanic s0 R) := by
  have hfsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  by_cases hlen_zero : authKey.length = 0
  · have hnil : authKey = [] := List.eq_nil_of_length_eq_zero hlen_zero
    subst hnil
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx20 hnext ⊢
    refine initInner_seq_sepWP_lsInv
      (init_inner_b2a_empty_to_192_placed (A := A) s0 s out
        ((akPtr ↦ₛ ([] : Bytes)) ∗ A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
        hsp0_align hpc hrun hsp hx29 hx19 hx20 hw2 hcs_hi htrace) ?_
    intro sm hpcm hrunm hcodem hinvm ⟨hspm, hx29m, hx19m, hx0m, hx1m, hcsm, htrm⟩
    exact hnext sm hpcm hrunm hcodem hinvm hspm hx29m hx19m hx0m hx1m hcsm htrm
  · refine SepWPp.weaken_pre (cells_1032_3_expose s0.sp _) ?_
    refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 => SepWPp.exists_elim fun w2 => ?_
    have hpos : 0 < authKey.length := Nat.pos_of_ne_zero hlen_zero
    have hbeq0 : (BitVec.ofNat 64 authKey.length == 0#64) = false := ofNat_beq_zero_false' hpos (by omega)
    have hne0 : (BitVec.ofNat 64 authKey.length != 0#64) = true := ofNat_ne_zero_true hpos (by omega)
    have htoNat_len : (BitVec.ofNat 64 authKey.length).toNat = authKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk authKey.length 1 := ⟨hpos, hpow2, by omega⟩
    have hpanic : ∀ (sm : State) (P_mid : SepProp),
        sm.pc = (blkPl_324).base + 436#64 →
        sm.status = .Running → sm.trace = s0.trace ++ [allocFailedEvent] →
        SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) sm P_mid Q (InitInnerPanic s0 R) :=
      fun sm P_mid hpcm hrunm htrm => init_inner_panic_436_placed h_panic s0 sm P_mid R hpcm hrunm htrm
    simp only [noAllocShimSpec] at hshim
    simp only [rustAllocSpec] at halloc
    simp only [framelessMemcpySpec] at hmemcpy
    rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
    dsimp only [Direction.toI32,
      State.readReg32, Reg.x2, BitVec.ofNat_eq_ofNat] at hpc hw2 hshim halloc hmemcpy hpanic ⊢
    refine sepWPp_of_sepWP_keepLsInv (mid := (blkPl_324).base + 64#64) ?_
    wp_steps; wp_apply; wp_steps; wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcode_sf1 hinv_sf1
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom, ↓reduceIte]
      refine CryptoVerification.SpqrV1.Poly.DecoderPb.sepWPp_pure_mid fun htr_oom => ?_
      refine CryptoVerification.SpqrV1.Poly.DecoderPb.SepWPp.seq_clean (mid := (blkPl_324).base + 436#64)
        (P_mid := A.pool ∗ stackAt sf.sp allocHookStack ∗ ((s0.sp - 1032#64) ↦₆₄ w0) ∗
          ((s0.sp - 1024#64) ↦₆₄ w1) ∗ ((s0.sp - 1016#64) ↦₆₄ w2) ∗ (akPtr ↦ₛ authKey) ∗ Frame)
        (Q_mid := fun sm => sm.trace = s0.trace ++ [allocFailedEvent]) ?_ ?_
      · wp_steps; wp_done
      · intro sm hpcm hrunm htrm; exact hpanic sm _ hpcm hrunm htrm
    · have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
      have hoom_bne : (sf_1.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hoom
      conv => arg 4; simp only [hoom, ↓reduceIte, htoNat_len]; simp only [sepConj_assoc]
      refine CryptoVerification.SpqrV1.Poly.DecoderPb.sepWPp_pure_mid fun ⟨_, htr_ok⟩ => ?_
      let ptr_c := sf_1.readReg64 (Reg.gpr 0#5)
      refine initInner_seq_sepWP_lsInv (mid := (blkPl_324).base + 192#64)
        (P' := vecU8 A (s0.sp - 1032#64) authKey ∗ (akPtr ↦ₛ authKey) ∗
          A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
        (Post := fun sm => sm.sp = s0.sp - 1040#64 ∧ sm.readReg64 .x29 = s0.sp - 48#64 ∧
          sm.readReg64 .x19 = out ∧ sm.readReg64 .x0 = s0.sp - 104#64 ∧
          sm.readReg64 .x1 = s0.sp - 1032#64 ∧
          (sm.readReg64 .x22 = s0.readReg64 .x22 ∧ sm.readReg64 .x23 = s0.readReg64 .x23 ∧
           sm.readReg64 .x24 = s0.readReg64 .x24 ∧ sm.readReg64 .x25 = s0.readReg64 .x25 ∧
           sm.readReg64 .x26 = s0.readReg64 .x26 ∧ sm.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs sm = calleeSavedVRegs s0) ∧
          sm.trace = s0.trace) ?_ ?_
      · wp_steps; wp_apply; wp_steps
        have hvec := vecU8_nonempty_of_cells A (s0.sp - 1032#64) ptr_c authKey hpos hlt hoom
        simp only [arm64_norm] at hvec
        have hent :
            (ptr_c ↦ₛ authKey) ∗ (akPtr ↦ₛ authKey) ∗ A.pool ∗ stackAt sf.sp allocHookStack ∗
            A.live ptr_c authKey.length 1 ∗ ((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
            ((s0.sp - 1024#64) ↦₆₄ ptr_c) ∗ ((s0.sp - 1016#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗ Frame ⊢
            vecU8 A (s0.sp - 1032#64) authKey ∗ (akPtr ↦ₛ authKey) ∗
            A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame := by
          rw [‹sf.sp = s.sp›, hsp]
          refine Entails.trans (Entails.of_eq (show _ =
            (((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗ ((s0.sp - 1024#64) ↦₆₄ ptr_c) ∗
             ((s0.sp - 1016#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗ A.live ptr_c authKey.length 1 ∗
             (ptr_c ↦ₛ authKey)) ∗
            ((akPtr ↦ₛ authKey) ∗ A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame) by ac_rfl)) ?_
          exact sepConj_mono_left hvec
        exact SepWP.weaken_pre hent (by wp_done)
      · intro sm hpcm hrunm hcodem hinvm ⟨hspm, hx29m, hx19m, hx0m, hx1m, hcsm, htrm⟩
        exact hnext sm hpcm hrunm (fun hc => hcodem (hcode_sf1 hc)) (fun hi => hinvm (hinv_sf1 hi))
          hspm hx29m hx19m hx0m hx1m hcsm htrm

theorem init_inner_bl_364_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (blkPl_324).base + 364#64)
    (hrun : s.status = .Running) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) s P
      (fun s' P1 => (P1 ⊢ P) ∧ s'.sp = s.sp ∧
        s'.readReg64 .x30 = (blkPl_324).base + 368#64 ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        CalleeSavedPreserved s s' ∧ s'.trace = s.trace) := by
  wp_steps; wp_done

theorem init_inner_bl_192_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (blkPl_324).base + 192#64)
    (hrun : s.status = .Running) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) s P
      (fun s' P1 => (P1 ⊢ P) ∧ s'.sp = s.sp ∧
        s'.readReg64 .x30 = (blkPl_324).base + 196#64 ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        CalleeSavedPreserved s s' ∧ s'.trace = s.trace) := by
  wp_steps; wp_done

theorem init_inner_bl_412_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (blkPl_324).base + 412#64)
    (hrun : s.status = .Running) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 334) s P
      (fun s' P1 => (P1 ⊢ P) ∧ s'.sp = s.sp ∧
        s'.readReg64 .x30 = (blkPl_324).base + 416#64 ∧
        s'.readReg64 .x8 = s.readReg64 .x8 ∧ s'.readReg64 .x0 = s.readReg64 .x0 ∧
        CalleeSavedPreserved s s' ∧ s'.trace = s.trace) := by
  wp_steps; wp_done

/-- Abstract call interface for `<States>::into_pb` at `lsmpl.base 334` on `Block 324`. -/
def IntoPbCallAtPlaced [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State))
    (s0 : State) (out : BitVec 64) (d : Direction) (authKey : Bytes)
    (Q : State → SepProp → Prop) (R : SepProp) : Prop :=
  ∀ (s : State) (ret_pc : BitVec 64) (P Frame : SepProp),
    (LibsignalCodeLoaded lsmpl s0.mem → LibsignalCodeLoaded lsmpl s.mem) →
    s.pc = lsmpl.base 334 →
    s.status = .Running → s.sp = s0.sp - 1040#64 →
    s.readReg64 .x30 = ret_pc → s.trace = s0.trace →
    s.readReg64 .x8 = out → s.readReg64 .x0 = s0.sp - 1032#64 →
    P = (memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A (s0.sp - 1032#64) (initV1State F d authKey) ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool ∗
      stackAt (s0.sp - 1040#64) statesIntoPbStack) ∗ Frame →
    (∀ (sf : State),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp - 1040#64 →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        ((optProtoInnerStateAt A out (initV1State F d authKey).into_pb.innerState ∗
          memRegion (s0.sp - 1032#64) chunkedStatesSize ∗ statesIntoPbJumpTablePlacedAt ∗
          A.pool ∗ stackAt (s0.sp - 1040#64) statesIntoPbStack) ∗ Frame)
        Q (InitInnerPanic s0 R)) →
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P Q (InitInnerPanic s0 R)

/-- Tail of `spqr::init_inner` (`Block 324`) for `v = .v1` (`+412 -> +416 -> ret`). -/
theorem init_inner_from_412_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s : State) (out akPtr : BitVec 64) (d : Direction) (authKey : Bytes) (R : SepProp)
    (hcall_into : IntoPbCallAtPlaced A F ext s0 out d authKey
      (InitInnerPlacedPost A F s0 ⟨out, .v1, d, akPtr, authKey⟩) R)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcode : LibsignalCodeLoaded lsmpl s0.mem → LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_324).base + 412#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1040#64)
    (hx8 : s.readReg64 .x8 = out) (hx0 : s.readReg64 .x0 = s0.sp - 1032#64)
    (hcs_hi : s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (chunkedStatesAt A (s0.sp - 1032#64) (initV1State F d authKey) ∗
       memRegion (s0.sp - 104#64) 56 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       stackAt (s0.sp - 1040#64) authNewStackX ∗ initInnerSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
       statesIntoPbJumpTablePlacedAt ∗ A.pool)
      (InitInnerPlacedPost A F s0 ⟨out, .v1, d, akPtr, authKey⟩) (InitInnerPanic s0 R) := by
  have hfsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  refine initInner_seq_sepWP_lsInv (init_inner_bl_412_placed s _ hpc hrun) ?_
  intro s1 hpc1 hrun1 hcode1 _ ⟨hsp1, hlr1, hx8_1, hx0_1, hcs1, htr1⟩
  have hcs_hi1 := calleeSaved_chain_hi hcs_hi hcs1
  have hsplit_pb :
      chunkedStatesAt A (s0.sp - 1032#64) (initV1State F d authKey) ∗
      memRegion (s0.sp - 104#64) 56 ∗ memRegion (s0.sp - 1040#64) 8 ∗
      stackAt (s0.sp - 1040#64) authNewStackX ∗ initInnerSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool =
      (memRegion out optProtoInnerStateSize ∗
       chunkedStatesAt A (s0.sp - 1032#64) (initV1State F d authKey) ∗
       statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt (s0.sp - 1040#64) statesIntoPbStack) ∗
      (memRegion (s0.sp - 1040#64 - 16640#64) 10768 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       memRegion (s0.sp - 104#64) 56 ∗ initInnerSavedCells s0 ∗ (akPtr ↦ₛ authKey)) := by
    rw [stackAt_authNew_split_statesIntoPb (s0.sp - 1040#64)]; ac_rfl
  refine hcall_into s1 ((blkPl_324).base + 416#64) _ _
    (fun hc0 => hcode1 (hcode hc0)) hpc1 hrun1 (hsp1.trans hsp) hlr1 (htr1.trans htr)
    (hx8_1.trans hx8) (hx0_1.trans hx0) hsplit_pb ?_
  intro s2 hpc2 hrun2 hsp2 hcs2 htr2
  have hcs_hi2 := calleeSaved_chain_hi hcs_hi1 hcs2
  have hrejoin_ep :
      (optProtoInnerStateAt A out (initV1State F d authKey).into_pb.innerState ∗
       memRegion (s0.sp - 1032#64) chunkedStatesSize ∗ statesIntoPbJumpTablePlacedAt ∗ A.pool ∗
       stackAt (s0.sp - 1040#64) statesIntoPbStack) ∗
      (memRegion (s0.sp - 1040#64 - 16640#64) 10768 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       memRegion (s0.sp - 104#64) 56 ∗ initInnerSavedCells s0 ∗ (akPtr ↦ₛ authKey)) ⊢
      stackAt (s0.sp - 1040#64) authNewStackX ∗ memRegion (s0.sp - 1040#64) 992 ∗
      initInnerSavedCells s0 ∗ (initInnerResultAt A (F := F) out .v1 d authKey ∗
       (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTablePlacedAt ∗ A.pool) := by
    dsimp only [initInnerResultAt]
    rw [← memRegion_992_rejoin_b2a s0.sp, stackAt_authNew_split_statesIntoPb (s0.sp - 1040#64)]
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hrejoin_ep ?_
  refine initInner_seq_sepWP_lsInv
    (init_inner_epilogue_placed s0 s2
      (initInnerResultAt A (F := F) out .v1 d authKey ∗
       (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTablePlacedAt ∗ A.pool)
      hsp0_align hpc2 hrun2 hsp2 hcs_hi2 htr2) ?_
  intro sf hpcf hrunf _ _ ⟨hspf, hcsf, htrf⟩
  exact SepWPp.done hpcf hrunf ⟨Entails.of_eq (by ac_rfl), hspf, hcsf, htrf⟩

/-- Abstract call interface for `<Authenticator>::new` at `lsmpl.base 340` on `Block 324`. -/
def AuthCallAtPlaced [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State))
    (s0 : State) (authKey : Bytes) (Q : State → SepProp → Prop) (R : SepProp) : Prop :=
  ∀ (s : State) (ret_pc : BitVec 64) (P Frame : SepProp),
    (LsCallInv lsmpl s0.mem → LsCallInv lsmpl s.mem) →
    s.pc = lsmpl.base 340 →
    s.status = .Running → s.sp = s0.sp - 1040#64 →
    s.readReg64 .x30 = ret_pc → s.trace = s0.trace →
    s.readReg64 .x0 = s0.sp - 104#64 → s.readReg64 .x1 = s0.sp - 1032#64 →
    P = (memRegion (s0.sp - 104#64) authenticatorSize ∗
      vecU8 A (s0.sp - 1032#64) authKey ∗ A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackX) ∗ Frame →
    (∀ (sf : State) (a0 a1 a2 a3 a4 a5 : BitVec 64),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp - 1040#64 →
      (LibsignalCodeLoaded lsmpl s.mem → LibsignalCodeLoaded lsmpl sf.mem) →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (((((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗
           ((s0.sp - 88#64) ↦₆₄ a2) ∗ ((s0.sp - 80#64) ↦₆₄ a3) ∗
           ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
          authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
          memRegion (s0.sp - 1032#64) 24 ∗ A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackX) ∗ Frame)
        Q (InitInnerPanic s0 R)) →
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P Q (InitInnerPanic s0 R)

/-- `.v1, .a2b` path from `+36` to return on `Block 324`. -/
theorem init_inner_v1_a2b_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" = some Rust.panicked)
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpySpec)
    (s0 s1 : State) (out akPtr : BitVec 64) (authKey : Bytes) (R : SepProp)
    (hcall_auth : AuthCallAtPlaced A F ext s0 authKey
      (InitInnerPlacedPost A F s0 ⟨out, .v1, .a2b, akPtr, authKey⟩) R)
    (hcall_into : IntoPbCallAtPlaced A F ext s0 out .a2b authKey
      (InitInnerPlacedPost A F s0 ⟨out, .v1, .a2b, akPtr, authKey⟩) R)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlt : authKey.length < 2 ^ 63)
    (hcode1 : LibsignalCodeLoaded lsmpl s0.mem → LibsignalCodeLoaded lsmpl s1.mem)
    (hinv1 : LsCallInv lsmpl s0.mem → LsCallInv lsmpl s1.mem)
    (hpc1 : s1.pc = (blkPl_324).base + 36#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 1040#64)
    (hx29_1 : s1.readReg64 .x29 = s0.sp - 48#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 authKey.length)
    (hw2_1 : s1.readReg32 .x2 = Direction.a2b.toI32) (hx3_1 : s1.readReg64 .x3 = akPtr)
    (hcs1 : s1.readReg64 .x22 = s0.readReg64 .x22 ∧ s1.readReg64 .x23 = s0.readReg64 .x23 ∧
      s1.readReg64 .x24 = s0.readReg64 .x24 ∧ s1.readReg64 .x25 = s0.readReg64 .x25 ∧
      s1.readReg64 .x26 = s0.readReg64 .x26 ∧ s1.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (htr1 : s1.trace = s0.trace) :
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (initInnerSavedCells s0 ∗ (memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
        statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackX ∗
        memRegion (s0.sp - 1040#64) 992))
      (InitInnerPlacedPost A F s0 ⟨out, .v1, .a2b, akPtr, authKey⟩) (InitInnerPanic s0 R) := by
  have hpre_split :
      initInnerSavedCells s0 ∗ (memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
       statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackX ∗
       memRegion (s0.sp - 1040#64) 992) ⊢
      cells (s0.sp - 1032#64) 3 ∗ (akPtr ↦ₛ authKey) ∗ A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗
      (memRegion (s0.sp - 1040#64 - 16640#64) 12544 ∗ memRegion (s0.sp - 104#64) authenticatorSize ∗
       cells (s0.sp - 1008#64) 5 ∗ memRegion (s0.sp - 968#64) 864 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       memRegion (s0.sp - 56#64) 8 ∗ initInnerSavedCells s0 ∗ memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTablePlacedAt) := by
    rw [memRegion_992_split_a2b s0.sp, stackAt_authNew_split_allocHook (s0.sp - 1040#64)]
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre_split ?_
  refine init_inner_clone_a2b_placed h_panic hshim halloc hmemcpy s0 s1 out akPtr authKey _ R
    hsp0_align hlt hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hw2_1 hx3_1 hcs1 htr1 ?_
  intro s2 hpc2 hrun2 hcode2 hinv2 hsp2 hx29_2 hx19_2 hx0_2 hx1_2 hcs2 htr2
  refine initInner_seq_sepWP_lsInv (init_inner_bl_364_placed s2 _ hpc2 hrun2) ?_
  intro s3 hpc3 hrun3 hcode3 hinv3 ⟨hsp3, hlr3, hx0_3, hx1_3, hcs3, htr3⟩
  have hcs_hi3 := calleeSaved_chain_hi hcs2 hcs3
  have hx29_3 := calleeSaved_x29 hx29_2 hcs3
  have hx19_3 := calleeSaved_x19 hx19_2 hcs3
  have hsplit_auth :
      vecU8 A (s0.sp - 1032#64) authKey ∗ (akPtr ↦ₛ authKey) ∗ A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗
      (memRegion (s0.sp - 1040#64 - 16640#64) 12544 ∗ memRegion (s0.sp - 104#64) authenticatorSize ∗
       cells (s0.sp - 1008#64) 5 ∗ memRegion (s0.sp - 968#64) 864 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       memRegion (s0.sp - 56#64) 8 ∗ initInnerSavedCells s0 ∗ memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTablePlacedAt) =
      (memRegion (s0.sp - 104#64) authenticatorSize ∗ vecU8 A (s0.sp - 1032#64) authKey ∗
       A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackX) ∗
      (cells (s0.sp - 1008#64) 5 ∗ memRegion (s0.sp - 968#64) 864 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       memRegion (s0.sp - 56#64) 8 ∗ initInnerSavedCells s0 ∗ memRegion out optProtoInnerStateSize ∗
       (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTablePlacedAt) := by
    rw [stackAt_authNew_split_allocHook (s0.sp - 1040#64)]; ac_rfl
  refine hcall_auth s3 ((blkPl_324).base + 368#64) _ _
    (fun h0 => hinv3 (hinv2 (hinv1 h0)))
    hpc3 hrun3 (hsp3.trans hsp2) hlr3 (htr3.trans htr2)
    (hx0_3.trans hx0_2) (hx1_3.trans hx1_2) hsplit_auth ?_
  intro s4 a0 a1 a2 a3 a4 a5 hpc4 hrun4 hsp4 hcode4 hcs4 htr4
  have hcs_hi4 := calleeSaved_chain_hi hcs_hi3 hcs4
  have hx29_4 := calleeSaved_x29 hx29_3 hcs4
  have hx19_4 := calleeSaved_x19 hx19_3 hcs4
  have hpre_post_auth :
      (((((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗ ((s0.sp - 88#64) ↦₆₄ a2) ∗
         ((s0.sp - 80#64) ↦₆₄ a3) ∗ ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
        memRegion (s0.sp - 1032#64) 24 ∗ A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackX) ∗
       (cells (s0.sp - 1008#64) 5 ∗ memRegion (s0.sp - 968#64) 864 ∗ memRegion (s0.sp - 1040#64) 8 ∗
        memRegion (s0.sp - 56#64) 8 ∗ initInnerSavedCells s0 ∗ memRegion out optProtoInnerStateSize ∗
        (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTablePlacedAt)) ⊢
      (((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗ ((s0.sp - 88#64) ↦₆₄ a2) ∗
       ((s0.sp - 80#64) ↦₆₄ a3) ∗ ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
      authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
      cells (s0.sp - 1032#64) 8 ∗ memRegion (s0.sp - 968#64) 864 ∗
      (memRegion (s0.sp - 56#64) 8 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       stackAt (s0.sp - 1040#64) authNewStackX ∗ initInnerSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
       statesIntoPbJumpTablePlacedAt ∗ A.pool) := by
    rw [← memRegion_24_and_cells_5_eq_cells_8 s0.sp]; exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre_post_auth ?_
  refine sepWPp_of_sepWP_keepLsInv (mid := (blkPl_324).base + 412#64) ?_
  refine SepWP.mono
    (init_inner_a2b_post_auth_placed s0 s4 out authKey a0 a1 a2 a3 a4 a5 _
      hsp0_align hpc4 hrun4 hsp4 hx29_4 hx19_4 hcs_hi4 htr4) ?_
  intro s5 P5 hpc5 hrun5 ⟨hent5, hsp5, hx8_5, hx0_5, hcs5, htr5⟩ hcode5 _
  refine SepWPp.weaken_pre hent5 ?_
  have h56 :
      chunkedStatesAt A (s0.sp - 1032#64) (initV1State F .a2b authKey) ∗
      memRegion (s0.sp - 104#64) 48 ∗
      (memRegion (s0.sp - 56#64) 8 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       stackAt (s0.sp - 1040#64) authNewStackX ∗ initInnerSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
       statesIntoPbJumpTablePlacedAt ∗ A.pool) ⊢
      chunkedStatesAt A (s0.sp - 1032#64) (initV1State F .a2b authKey) ∗
      memRegion (s0.sp - 104#64) 56 ∗ memRegion (s0.sp - 1040#64) 8 ∗
      stackAt (s0.sp - 1040#64) authNewStackX ∗ initInnerSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool := by
    rw [← memRegion_48_and_8_eq_56 s0.sp]; exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre h56 ?_
  exact init_inner_from_412_placed s0 s5 out akPtr .a2b authKey R hcall_into hsp0_align
    (fun hc0 => hcode5 (hcode4 (hcode3 (hcode2 (hcode1 hc0)))))
    hpc5 hrun5 hsp5 hx8_5 hx0_5 hcs5 htr5

/-- `.v1, .b2a` path from `+36` to return on `Block 324`. -/
theorem init_inner_v1_b2a_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" = some Rust.panicked)
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpySpec)
    (s0 s1 : State) (out akPtr : BitVec 64) (authKey : Bytes) (R : SepProp)
    (hcall_auth : AuthCallAtPlaced A F ext s0 authKey
      (InitInnerPlacedPost A F s0 ⟨out, .v1, .b2a, akPtr, authKey⟩) R)
    (hcall_into : IntoPbCallAtPlaced A F ext s0 out .b2a authKey
      (InitInnerPlacedPost A F s0 ⟨out, .v1, .b2a, akPtr, authKey⟩) R)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlt : authKey.length < 2 ^ 63)
    (hcode1 : LibsignalCodeLoaded lsmpl s0.mem → LibsignalCodeLoaded lsmpl s1.mem)
    (hinv1 : LsCallInv lsmpl s0.mem → LsCallInv lsmpl s1.mem)
    (hpc1 : s1.pc = (blkPl_324).base + 36#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 1040#64)
    (hx29_1 : s1.readReg64 .x29 = s0.sp - 48#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 authKey.length)
    (hw2_1 : s1.readReg32 .x2 = Direction.b2a.toI32) (hx3_1 : s1.readReg64 .x3 = akPtr)
    (hcs1 : s1.readReg64 .x22 = s0.readReg64 .x22 ∧ s1.readReg64 .x23 = s0.readReg64 .x23 ∧
      s1.readReg64 .x24 = s0.readReg64 .x24 ∧ s1.readReg64 .x25 = s0.readReg64 .x25 ∧
      s1.readReg64 .x26 = s0.readReg64 .x26 ∧ s1.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (htr1 : s1.trace = s0.trace) :
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (initInnerSavedCells s0 ∗ (memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
        statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackX ∗
        memRegion (s0.sp - 1040#64) 992))
      (InitInnerPlacedPost A F s0 ⟨out, .v1, .b2a, akPtr, authKey⟩) (InitInnerPanic s0 R) := by
  have hpre_split :
      initInnerSavedCells s0 ∗ (memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
       statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackX ∗
       memRegion (s0.sp - 1040#64) 992) ⊢
      cells (s0.sp - 1032#64) 3 ∗ (akPtr ↦ₛ authKey) ∗ A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗
      (memRegion (s0.sp - 1040#64 - 16640#64) 12544 ∗ memRegion (s0.sp - 104#64) authenticatorSize ∗
       cells (s0.sp - 56#64) 1 ∗ cells (s0.sp - 1008#64) 17 ∗ cells (s0.sp - 872#64) 20 ∗
       cells (s0.sp - 712#64) 17 ∗ (∃∗ b0 : BitVec 8, (s0.sp - 576#64) ↦₈ b0) ∗
       memRegion (s0.sp - 575#64) 7 ∗ memRegion (s0.sp - 568#64) 464 ∗
       memRegion (s0.sp - 1040#64) 8 ∗ initInnerSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTablePlacedAt) := by
    rw [memRegion_992_split_b2a s0.sp, stackAt_authNew_split_allocHook (s0.sp - 1040#64)]
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre_split ?_
  refine init_inner_clone_b2a_placed h_panic hshim halloc hmemcpy s0 s1 out akPtr authKey _ R
    hsp0_align hlt hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hw2_1 hx3_1 hcs1 htr1 ?_
  intro s2 hpc2 hrun2 hcode2 hinv2 hsp2 hx29_2 hx19_2 hx0_2 hx1_2 hcs2 htr2
  refine initInner_seq_sepWP_lsInv (init_inner_bl_192_placed s2 _ hpc2 hrun2) ?_
  intro s3 hpc3 hrun3 hcode3 hinv3 ⟨hsp3, hlr3, hx0_3, hx1_3, hcs3, htr3⟩
  have hcs_hi3 := calleeSaved_chain_hi hcs2 hcs3
  have hx29_3 := calleeSaved_x29 hx29_2 hcs3
  have hx19_3 := calleeSaved_x19 hx19_2 hcs3
  have hsplit_auth :
      vecU8 A (s0.sp - 1032#64) authKey ∗ (akPtr ↦ₛ authKey) ∗ A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗
      (memRegion (s0.sp - 1040#64 - 16640#64) 12544 ∗ memRegion (s0.sp - 104#64) authenticatorSize ∗
       cells (s0.sp - 56#64) 1 ∗ cells (s0.sp - 1008#64) 17 ∗ cells (s0.sp - 872#64) 20 ∗
       cells (s0.sp - 712#64) 17 ∗ (∃∗ b0 : BitVec 8, (s0.sp - 576#64) ↦₈ b0) ∗
       memRegion (s0.sp - 575#64) 7 ∗ memRegion (s0.sp - 568#64) 464 ∗
       memRegion (s0.sp - 1040#64) 8 ∗ initInnerSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTablePlacedAt) =
      (memRegion (s0.sp - 104#64) authenticatorSize ∗ vecU8 A (s0.sp - 1032#64) authKey ∗
       A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackX) ∗
      (cells (s0.sp - 56#64) 1 ∗ cells (s0.sp - 1008#64) 17 ∗ cells (s0.sp - 872#64) 20 ∗
       cells (s0.sp - 712#64) 17 ∗ (∃∗ b0 : BitVec 8, (s0.sp - 576#64) ↦₈ b0) ∗
       memRegion (s0.sp - 575#64) 7 ∗ memRegion (s0.sp - 568#64) 464 ∗
       memRegion (s0.sp - 1040#64) 8 ∗ initInnerSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTablePlacedAt) := by
    rw [stackAt_authNew_split_allocHook (s0.sp - 1040#64)]; ac_rfl
  refine hcall_auth s3 ((blkPl_324).base + 196#64) _ _
    (fun h0 => hinv3 (hinv2 (hinv1 h0)))
    hpc3 hrun3 (hsp3.trans hsp2) hlr3 (htr3.trans htr2)
    (hx0_3.trans hx0_2) (hx1_3.trans hx1_2) hsplit_auth ?_
  intro s4 a0 a1 a2 a3 a4 a5 hpc4 hrun4 hsp4 hcode4 hcs4 htr4
  have hcs_hi4 := calleeSaved_chain_hi hcs_hi3 hcs4
  have hx29_4 := calleeSaved_x29 hx29_3 hcs4
  have hx19_4 := calleeSaved_x19 hx19_3 hcs4
  have hpre_post_auth :
      (((((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗ ((s0.sp - 88#64) ↦₆₄ a2) ∗
         ((s0.sp - 80#64) ↦₆₄ a3) ∗ ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
        memRegion (s0.sp - 1032#64) 24 ∗ A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackX) ∗
       (cells (s0.sp - 56#64) 1 ∗ cells (s0.sp - 1008#64) 17 ∗ cells (s0.sp - 872#64) 20 ∗
        cells (s0.sp - 712#64) 17 ∗ (∃∗ b0 : BitVec 8, (s0.sp - 576#64) ↦₈ b0) ∗
        memRegion (s0.sp - 575#64) 7 ∗ memRegion (s0.sp - 568#64) 464 ∗
        memRegion (s0.sp - 1040#64) 8 ∗ initInnerSavedCells s0 ∗
        memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTablePlacedAt)) ⊢
      (((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗ ((s0.sp - 88#64) ↦₆₄ a2) ∗
       ((s0.sp - 80#64) ↦₆₄ a3) ∗ ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
      authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
      cells (s0.sp - 56#64) 1 ∗ cells (s0.sp - 1032#64) 20 ∗
      cells (s0.sp - 872#64) 20 ∗ cells (s0.sp - 712#64) 17 ∗
      (∃∗ b0 : BitVec 8, (s0.sp - 576#64) ↦₈ b0) ∗
      memRegion (s0.sp - 575#64) 7 ∗ memRegion (s0.sp - 568#64) 464 ∗
      (memRegion (s0.sp - 1040#64) 8 ∗ stackAt (s0.sp - 1040#64) authNewStackX ∗
       initInnerSavedCells s0 ∗ memRegion out optProtoInnerStateSize ∗
       (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTablePlacedAt ∗ A.pool) := by
    rw [← memRegion_24_and_cells_17_eq_cells_20 s0.sp]; exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre_post_auth ?_
  refine initInner_seq_sepWP_lsInv
    (init_inner_b2a_post_auth_placed s0 s4 out authKey a0 a1 a2 a3 a4 a5 _
      hsp0_align hpc4 hrun4 hsp4 hx29_4 hx19_4 hcs_hi4 htr4) ?_
  intro s5 hpc5 hrun5 hcode5 _ ⟨hsp5, hx8_5, hx0_5, hcs5, htr5⟩
  exact init_inner_from_412_placed s0 s5 out akPtr .b2a authKey R hcall_into hsp0_align
    (fun hc0 => hcode5 (hcode4 (hcode3 (hcode2 (hcode1 hc0)))))
    hpc5 hrun5 hsp5 hx8_5 hx0_5 hcs5 htr5

/-- Unified body of `spqr::init_inner` (`Block 324`) for all `(v, d)` given `AuthCallAtPlaced` and `IntoPbCallAtPlaced`. -/
theorem init_inner_body_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" = some Rust.panicked)
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpySpec)
    (s0 : State) (x : InitInnerGhost) (R : SepProp)
    (hcall_auth : AuthCallAtPlaced A F ext s0 x.authKey (InitInnerPlacedPost A F s0 x) R)
    (hcall_into_a2b : IntoPbCallAtPlaced A F ext s0 x.out .a2b x.authKey
      (InitInnerPlacedPost A F s0 ⟨x.out, .v1, .a2b, x.akPtr, x.authKey⟩) R)
    (hcall_into_b2a : IntoPbCallAtPlaced A F ext s0 x.out .b2a x.authKey
      (InitInnerPlacedPost A F s0 ⟨x.out, .v1, .b2a, x.akPtr, x.authKey⟩) R)
    (hpc : s0.pc = (blkPl_324).base)
    (hrun : s0.status = .Running)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpure :
      s0.readReg64 .x0 = x.out ∧ s0.readReg32 .x1 = x.v.toI32 ∧
      s0.readReg32 .x2 = x.d.toI32 ∧ s0.readReg64 .x3 = x.akPtr ∧
      s0.readReg64 .x4 = BitVec.ofNat 64 x.authKey.length ∧
      x.akPtr ≠ 0#64 ∧ 32 + x.authKey.length < 2 ^ 63) :
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s0
      (memRegion x.out optProtoInnerStateSize ∗ (x.akPtr ↦ₛ x.authKey) ∗
       statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp initInnerStack)
      (InitInnerPlacedPost A F s0 x)
      (InitInnerPanic s0 R) := by
  rcases x with ⟨out, v, d, akPtr, authKey⟩
  rcases hpure with ⟨hx0, hw1, hw2, hx3, hx4, _, hlt32⟩
  cases v
  · have hpre_v0 :
        memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
        statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp initInnerStack ⊢
        memRegion out optProtoInnerStateSize ∗ stackAt s0.sp initInnerStack ∗
        ((akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTablePlacedAt ∗ A.pool) :=
      Entails.of_eq (by ac_rfl)
    refine SepWPp.weaken_pre hpre_v0 ?_
    refine initInner_seq_sepWP_lsInv
      (init_inner_v0_placed (A := A) (F := F) s0 out d authKey
        ((akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTablePlacedAt ∗ A.pool)
        hsp0_align hpc hrun hx0 hw1) ?_
    intro sf hpcf hrunf _ _ ⟨hspf, hcsf, htrf⟩
    exact SepWPp.done hpcf hrunf ⟨Entails.of_eq (by ac_rfl), hspf, hcsf, htrf⟩
  · have hpre_v1 :
        memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
        statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp initInnerStack ⊢
        cells (s0.sp - 48#64) 6 ∗
        (memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
         statesIntoPbJumpTablePlacedAt ∗ A.pool ∗
         stackAt (s0.sp - 1040#64) authNewStackX ∗ memRegion (s0.sp - 1040#64) 992) := by
      rw [stackAt_initInner_split s0.sp]
      exact Entails.of_eq (by ac_rfl)
    refine SepWPp.weaken_pre hpre_v1 ?_
    refine initInner_seq_sepWP_lsInv
      (init_inner_prologue_v1_placed s0 out akPtr d authKey _
        hsp0_align hpc hrun hx0 hw1 hw2 hx3 hx4) ?_
    intro s1 hpc1 hrun1 hcode1 hinv1 ⟨hsp1, hx29_1, hx19_1, hx20_1, hw2_1, hx3_1, hcs1, htr1⟩
    cases d
    · exact init_inner_v1_a2b_placed h_panic hshim halloc hmemcpy s0 s1 out akPtr authKey R
        hcall_auth hcall_into_a2b hsp0_align
        (by dsimp at hlt32; omega) hcode1 hinv1 hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hw2_1 hx3_1 hcs1 htr1
    · exact init_inner_v1_b2a_placed h_panic hshim halloc hmemcpy s0 s1 out akPtr authKey R
        hcall_auth hcall_into_b2a hsp0_align
        (by dsimp at hlt32; omega) hcode1 hinv1 hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hw2_1 hx3_1 hcs1 htr1

/-- Top-level verification of `spqr::init_inner` on `(blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)`
    against `withLsCodeLoaded lsmpl (initInnerPlacedSpecX A F)`. -/
theorem init_inner_placed_ok_ext [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" = some Rust.panicked)
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpySpec)
    (hauth : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) (authNewSpec F A))
    (hinto : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 334) (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpec A F))) :
    subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (blkPl_324).base (withLsCodeLoaded lsmpl (initInnerPlacedSpecX A F)) := by
  apply withLsCodeLoaded_initInnerPlacedSpecX_of_initInnerPlacedSpec
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp0_align
  have hfsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  obtain ⟨hcode0, hpre⟩ := extract_withLsCodeLoaded hpre
  dsimp only [initInnerPlacedSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hm⟩
  have hlt32 : 32 + x.authKey.length < 2 ^ 63 := hpure.2.2.2.2.2.2
  have hcall_auth : AuthCallAtPlaced A F ext s0 x.authKey (InitInnerPlacedPost A F s0 x) R :=
    fun s ret_pc P Frame _ hpcs hruns hsps hlrs htrs hx0s hx1s hsplits hnext =>
      call_authNew_placed_ext hauth x.authKey hlt32 s0 s ret_pc P Frame R
        hpcs hruns hsps hfsp_align hlrs htrs hx0s hx1s hsplits hnext
  have hcall_into_a2b : IntoPbCallAtPlaced A F ext s0 x.out .a2b x.authKey
      (InitInnerPlacedPost A F s0 ⟨x.out, .v1, .a2b, x.akPtr, x.authKey⟩) R :=
    fun s ret_pc P Frame hcs hpcs hruns hsps hlrs htrs hx8s hx0s hsplits hnext =>
      call_statesIntoPb_placed_x hinto x.out (hcs hcode0) hpcs hruns hsps hfsp_align hlrs htrs hx8s hx0s hsplits hnext
  have hcall_into_b2a : IntoPbCallAtPlaced A F ext s0 x.out .b2a x.authKey
      (InitInnerPlacedPost A F s0 ⟨x.out, .v1, .b2a, x.akPtr, x.authKey⟩) R :=
    fun s ret_pc P Frame hcs hpcs hruns hsps hlrs htrs hx8s hx0s hsplits hnext =>
      call_statesIntoPb_placed_x hinto x.out (hcs hcode0) hpcs hruns hsps hfsp_align hlrs htrs hx8s hx0s hsplits hnext
  refine ⟨_, R, hm, sepWPp_of_init_inner_placed_wpp s0 s0 x _ R
    (init_inner_body_placed h_panic hshim halloc hmemcpy s0 x R hcall_auth hcall_into_a2b hcall_into_b2a
      hpc hrun hsp0_align hpure)⟩

/-- Top-level verification of `spqr::init_inner` on `(blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)`
    against `withLsCallInv lsmpl (initInnerPlacedSpecX A F)`. -/
theorem init_inner_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" = some Rust.panicked)
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpySpec)
    (hauth : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) (withLsCallInv lsmpl (authNewSpec F A)))
    (hinto : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 334) (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpec A F))) :
    subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (blkPl_324).base (withLsCallInv lsmpl (initInnerPlacedSpecX A F)) := by
  have hspec_base :
      subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
        (blkPl_324).base (withLsCallInv lsmpl (initInnerPlacedSpec A F)) := by
    apply subroutine_ok_of_sepWPp
    intro x R s0 hpc hrun hpre hsp0_align
    have hfsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
      ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
    dsimp only [withLsCallInv, initInnerPlacedSpec] at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨hinv0, hpre⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨hpure, hm⟩
    have hcode0 : LibsignalCodeLoaded lsmpl s0.mem := hinv0.2
    have hlt32 : 32 + x.authKey.length < 2 ^ 63 := hpure.2.2.2.2.2.2
    have hcall_auth : AuthCallAtPlaced A F ext s0 x.authKey (InitInnerPlacedPost A F s0 x) R :=
      fun s ret_pc P Frame hinv_s hpcs hruns hsps hlrs htrs hx0s hx1s hsplits hnext =>
        call_authNew_placed_x hauth x.authKey hlt32 s0 s ret_pc P Frame R
          (hinv_s hinv0) hpcs hruns hsps hfsp_align hlrs htrs hx0s hx1s hsplits hnext
    have hcall_into_a2b : IntoPbCallAtPlaced A F ext s0 x.out .a2b x.authKey
        (InitInnerPlacedPost A F s0 ⟨x.out, .v1, .a2b, x.akPtr, x.authKey⟩) R :=
      fun s ret_pc P Frame hcs hpcs hruns hsps hlrs htrs hx8s hx0s hsplits hnext =>
        call_statesIntoPb_placed_x hinto x.out (hcs hcode0) hpcs hruns hsps hfsp_align hlrs htrs hx8s hx0s hsplits hnext
    have hcall_into_b2a : IntoPbCallAtPlaced A F ext s0 x.out .b2a x.authKey
        (InitInnerPlacedPost A F s0 ⟨x.out, .v1, .b2a, x.akPtr, x.authKey⟩) R :=
      fun s ret_pc P Frame hcs hpcs hruns hsps hlrs htrs hx8s hx0s hsplits hnext =>
        call_statesIntoPb_placed_x hinto x.out (hcs hcode0) hpcs hruns hsps hfsp_align hlrs htrs hx8s hx0s hsplits hnext
    refine ⟨_, R, hm, sepWPp_of_init_inner_placed_wpp s0 s0 x _ R
      (init_inner_body_placed h_panic hshim halloc hmemcpy s0 x R hcall_auth hcall_into_a2b hcall_into_b2a
        hpc hrun hsp0_align hpure)⟩
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  dsimp only [withLsCallInv] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, hpre⟩
  have hle : initInnerStack ≤ initInnerStackX := by decide
  have hsplit : stackAt s0.sp initInnerStackX =
      memRegion (s0.sp - BitVec.ofNat 64 initInnerStackX)
        (initInnerStackX - initInnerStack) ∗
        stackAt s0.sp initInnerStack := by
    have h1 := stackAt_split_bottom s0.sp initInnerStack
      (initInnerStackX - initInnerStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 initInnerStackX)
      (initInnerStackX - initInnerStack) ∗ R
  have hpre' : s0.mem ⊨ (withLsCallInv lsmpl (initInnerPlacedSpec A F)).pre x s0 ∗ R' := by
    dsimp only [withLsCallInv]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ?_⟩
    dsimp only [initInnerPlacedSpecX, initInnerPlacedSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine subroutine_ok.mono_outcome hspec_base x R' s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCallInv, initInnerPlacedSpecX, initInnerPlacedSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withLsCallInv, initInnerPlacedSpecX, initInnerPlacedSpec, initInnerOnPanic, R'] at hpost ⊢
    have h1 : ((⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗
        (memRegion (s0.sp - BitVec.ofNat 64 initInnerStackX) (initInnerStackX - initInnerStack) ∗ R)) ⊢
        (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
      rw [sepConj_assoc (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝) anyHeap _,
          ← sepConj_assoc anyHeap _ R,
          sepConj_assoc (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝) anyHeap R]
      exact sepConj_mono_right (sepConj_mono_left (entails_anyHeap _))
    exact Satisfies.mono h1 hpost
  · dsimp only [withLsCallInv, initInnerPlacedSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-- Top-level verification of `spqr::init_inner` (`Block 324`) on `libsignalSessionLib.blockProgram lsmpl 324`
    at `lsmpl.base 324` (`InitInnerPlacedOkX A F ext`), parameterized by `hIntoPb : StatesIntoPbPlacedOkExt A F ext`. -/
theorem init_inner_placed_ok_blockProgram [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" = some Rust.panicked)
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpySpec)
    (hauth : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) (authNewSpec F A))
    (hIntoPb : StatesIntoPbPlacedOkExt A F ext) :
    InitInnerPlacedOkX A F ext := by
  have hinto_324 :
      subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
        (lsmpl.base 334) (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpec A F)) :=
    subroutine_ok_mono
      (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
        hIntoPb)
      (fun _ _ _ h => h)
      (fun _ _ _ _ h => by
        dsimp only [withLsCl, withLsCodeLoaded] at h ⊢
        rw [sepConj_assoc, satisfies_pure_sepConj] at h
        exact h.2)
  have hok := init_inner_placed_ok_ext h_panic hshim halloc hmemcpy hauth hinto_324
  dsimp only [InitInnerPlacedOkX]
  rwa [← IsLsBlockProg.eq_blockProgram (prog := (blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))]

/-- Unconditional wiring of `InitInner.StatesIntoPbPlacedOkX A F ext` from
    `States.IntoPb.states_into_pb_placed_ro_ok_x`. -/
theorem states_into_pb_placed_ok_x_blockProgram [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : States.IntoPb.StatesIntoPbAllocPlaced A ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec A))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec A))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec) :
    StatesIntoPbPlacedOkX A F ext := by
  have hro :
      subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
        (lsmpl.base 334) (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecX A F)) :=
    subroutine_ok_withLsCodeLoaded_of_plain
      (States.IntoPb.states_into_pb_placed_ro_ok_x hA henc_raw hdec_raw hmemcpy_raw)
  dsimp only [StatesIntoPbPlacedOkX]
  rwa [← IsLsBlockProg.eq_blockProgram (prog := (blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))]

/-- Top-level verification of `spqr::init_inner` (`Block 324`) wired through
    `States.IntoPb.states_into_pb_placed_ok_ext`. -/
theorem init_inner_placed_ok_unconditional [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpySpec)
    (hauth : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) (authNewSpec F A))
    (hA_into : States.IntoPb.StatesIntoPbAllocPlaced A ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec A))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec A))
    (hmemcpy_into : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec) :
    InitInnerPlacedOkX A F ext :=
  init_inner_placed_ok_blockProgram hA_into.panic_ok hshim halloc hmemcpy hauth
    (States.IntoPb.states_into_pb_placed_ok_ext hA_into henc_raw hdec_raw hmemcpy_into)

end CryptoVerification.SpqrV1.Top.InitInner
