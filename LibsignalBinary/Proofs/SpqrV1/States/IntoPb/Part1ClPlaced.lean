/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Placed
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`) — Part 1 `withLsCodeLoaded`: Arm 0 & Call Helpers

Lifts Arm 0 (`States.keysUnsampled`) to `withLsCodeLoaded` and provides shared `SepWPp` sequencing
and `<PolyEncoder>::into_pb` / `<PolyDecoder>::into_pb` call combinators threading `LibsignalCodeLoaded`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.IntoPb

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.States.IntoPb.Placed
open LibsignalPublicApi.StoreKit

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Arm 0 (`States.keysUnsampled`) makes zero cross-block calls and lifts directly to `withLsCodeLoaded`. -/
theorem states_into_pb_keysUnsampled_cl_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (s : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpec A F (.keysUnsampled s))) :=
  subroutine_ok_withLsCodeLoaded_of_plain (states_into_pb_keysUnsampled_placed s)

/-- Sequence an intra-block `SepWP` step inside `SepWPp` while threading `LibsignalCodeLoaded lsmpl`. -/
theorem statesIntoPb_seq_sepWP_cl [LibsignalPlacement] {prog : Program}
    {ret mid : BitVec 64} {s : State} {P P' : SepProp} {Post : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P (fun s' P1 => (P1 ⊢ P') ∧ Post s'))
    (hnext : ∀ s' : State, s'.pc = mid → s'.status = .Running →
      LibsignalCodeLoaded lsmpl s'.mem → Post s' →
      SepWPp prog ret s' P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.seq_frozen (mid := mid) (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl ?_
  refine SepWP.mono hstep fun s' P1 hpc' hrun' ⟨hent, hpost⟩ hcl' =>
    SepWPp.weaken_pre hent (hnext s' hpc' hrun' hcl' hpost)

/-- Call combinator inside `SepWPp` that threads `LibsignalCodeLoaded lsmpl` to the return state `sf`. -/
theorem sepWPp_call_keepLsCl_pub [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F : SepProp}
    {post Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ code sf R, sf.status = .Exited code → ¬ (sf.mem ⊨ spec.onExit x code s sf ∗ (F ∗ R)))
    (hpan : ∀ sf, Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro sf; first | rfl | simp only [withLsCodeLoaded]) :
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
      hnext sm hpcm hrunm hspm hcsm (hcl.of_keepsFrozen hsteps.keepsFrozen) R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan_out)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom_out)⟩

/-- Call `<PolyEncoder>::into_pb` (Block `375`, `lsmpl.base 375`) with `withLsCodeLoaded`,
    exposing `e0..e6` and threading `LibsignalCodeLoaded lsmpl sf.mem` to `hnext`. -/
theorem call_encoderIntoPb_expose_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375)
      (withLsCodeLoaded lsmpl (encoderIntoPbSpec A)))
    (outEncA encA : BitVec 64) (enc : PolyEncoder)
    {s0 s : State} {ret_pc : BitVec 64} {P Frame R : SepProp}
    {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 375)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = outEncA)
    (hx1 : s.readReg64 .x1 = encA)
    (hsplit : P = (memRegion outEncA protoPolynomialEncoderSize ∗
      polyEncoderAt A encA enc ∗
      A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
    (hnext : ∀ (sf : State) (e0 e1 e2 e3 e4 e5 e6 : BitVec 64),
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      TraceCalleeSaved sf s0 →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (((outEncA ↦₆₄ e0) ∗ ((outEncA + 8#64) ↦₆₄ e1) ∗ ((outEncA + 16#64) ↦₆₄ e2) ∗
          ((outEncA + 24#64) ↦₆₄ e3) ∗ ((outEncA + 32#64) ↦₆₄ e4) ∗ ((outEncA + 40#64) ↦₆₄ e5) ∗
          ((outEncA + 48#64) ↦₆₄ e6) ∗
          protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 enc.intoPb ∗
          memRegion encA polyEncoderSize ∗
          A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
        Q (StatesIntoPbPanic s0 R)) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      Q (StatesIntoPbPanic s0 R) := by
  refine sepWPp_call_keepLsCl_pub henc_cl (x := ⟨outEncA, encA, enc⟩) (F := Frame)
    hcl hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => by
      dsimp only [withLsCodeLoaded] at h
      exact allowPanic_not_exited h)
    (fun sf hmem => by
      dsimp only [withLsCodeLoaded, encoderIntoPbSpec] at hmem
      rw [← sepConj_assoc]
      have hpan := allowPanic_frame (φ := allocFailedIn s sf ∧ s.trace <+: sf.trace)
        (ψ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
        (fun ⟨haf, htr_sub⟩ => by
          unfold allocFailedIn at haf ⊢
          rw [htrace.1] at haf htr_sub
          exact ⟨haf, htr_sub⟩) hmem
      simpa only [sepConj_assoc] using hpan)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcl_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, encoderIntoPbSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    refine ⟨⟨hx0, hx1⟩, ?_⟩
    have hm1 : s.mem ⊨ ⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗
        (memRegion outEncA protoPolynomialEncoderSize ∗
         polyEncoderAt A encA enc ∗
         A.pool ∗
         stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
         Frame ∗ R') := by
      rw [satisfies_pure_sepConj]
      exact ⟨hcl, Satisfies.mono (Entails.of_eq (by ac_rfl)) hm⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm1
  · dsimp only [withLsCodeLoaded, encoderIntoPbSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    have hexp :
        (protoPolynomialEncoderAt A outEncA enc.intoPb ∗
          memRegion encA polyEncoderSize ∗
          A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame ⊢
        ∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64,
        ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ e5 : BitVec 64, ∃∗ e6 : BitVec 64,
          (((outEncA ↦₆₄ e0) ∗ ((outEncA + 8#64) ↦₆₄ e1) ∗ ((outEncA + 16#64) ↦₆₄ e2) ∗
            ((outEncA + 24#64) ↦₆₄ e3) ∗ ((outEncA + 32#64) ↦₆₄ e4) ∗ ((outEncA + 40#64) ↦₆₄ e5) ∗
            ((outEncA + 48#64) ↦₆₄ e6) ∗
            protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 enc.intoPb ∗
            memRegion encA polyEncoderSize ∗
            A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame) := by
      refine Entails.trans (sepConj_mono_left (sepConj_mono_left (protoPolynomialEncoder_expose A outEncA enc.intoPb))) ?_
      simp only [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro e0
      apply Entails.sepExists_elim; intro e1
      apply Entails.sepExists_elim; intro e2
      apply Entails.sepExists_elim; intro e3
      apply Entails.sepExists_elim; intro e4
      apply Entails.sepExists_elim; intro e5
      apply Entails.sepExists_elim; intro e6
      refine Entails.sepExists_right e0 (Entails.sepExists_right e1
        (Entails.sepExists_right e2 (Entails.sepExists_right e3
          (Entails.sepExists_right e4 (Entails.sepExists_right e5
            (Entails.sepExists_right e6 ?_))))))
      exact Entails.of_eq (by ac_rfl)
    refine SepWPp.weaken_pre hexp ?_
    refine SepWPp.exists_elim fun e0 => SepWPp.exists_elim fun e1 =>
      SepWPp.exists_elim fun e2 => SepWPp.exists_elim fun e3 =>
      SepWPp.exists_elim fun e4 => SepWPp.exists_elim fun e5 =>
      SepWPp.exists_elim fun e6 => ?_
    exact hnext sf e0 e1 e2 e3 e4 e5 e6 hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hcl_sf

end CryptoVerification.SpqrV1.States.IntoPb
