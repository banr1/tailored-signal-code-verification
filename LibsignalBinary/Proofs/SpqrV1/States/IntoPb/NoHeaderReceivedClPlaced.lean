/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aPlaced
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4Placed
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4a
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`) — Arm 5 (`States.noHeaderReceived`) with `withLsCodeLoaded`

Proves `states_into_pb_noHeaderReceived_cl_placed` (`withLsCodeLoaded`-guarded contract on Arm 5
of Block `334`) from `withLsCodeLoaded`-guarded `<PolyDecoder>::into_pb` (`Block 377`), reusing
all `SepWP` segments from `Part4aPlaced.lean` without re-stepping.
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
  bv_sub_sub_lit' bv_add_add_lit'
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

private theorem statesIntoPb_seq_sepWP_cl_placed [LibsignalPlacement] {prog : Program}
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

private theorem sepWPp_call_keepLsCl [LibsignalPlacement] {α : Type} {prog : Program}
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

private theorem call_memcpy_keep_relocate_cl_placed [LibsignalPlacement] {memcpy_pc : BitVec 64}
    {ext : String → Option (State → State)}
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      memcpy_pc
      sessionMemcpyRegionSpec)
    {k m n : Nat} {off : BitVec 64}
    {F G : BitVec 64 → SepProp}
    (hoff : off = BitVec.ofNat 64 k)
    (hkm : k + m = n)
    (hF : Relocatable k F)
    (hG : Relocatable m G)
    (dst src : BitVec 64)
    {s0 s : State} {ret_pc : BitVec 64} {P Frame R : SepProp}
    {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = memcpy_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ (F src ∗ G (src + off))) ∗ Frame)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      TraceCalleeSaved sf s0 →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (((memRegion dst k ∗ G (dst + off)) ∗
          (F src ∗ memRegion (src + off) m)) ∗ Frame)
        Q (StatesIntoPbPanic s0 R)) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      Q (StatesIntoPbPanic s0 R) := by
  have hpre_split :
      P ⊢ ∃∗ bs1 : List (BitVec 8), ∃∗ bs2 : List (BitVec 8),
        ⌜bs1.length = k ∧ bs2.length = m ∧ (bs1 ++ bs2).length = n⌝ ∗
        (memRegion dst n ∗ (src ↦ₛ (bs1 ++ bs2))) ∗
        (relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ Frame) := by
    rw [hsplit]
    refine Entails.trans (sepConj_mono_left (sepConj_mono_right
      (memcpy_keep_relocate_split hoff hkm hF hG dst src))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs1
    apply Entails.sepExists_elim; intro bs2
    rw [sepConj_left_comm (memRegion dst n), sepConj_assoc (⌜_⌝)]
    apply Entails.pure_left; intro hpure
    refine Entails.sepExists_right bs1 (Entails.sepExists_right bs2 ?_)
    refine Entails.pure_right hpure ?_
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre_split ?_
  refine SepWPp.exists_elim fun bs1 => SepWPp.exists_elim fun bs2 => ?_
  refine SepWPp.pure_left fun ⟨hlen1, hlen2, hlen12⟩ => ?_
  refine sepWPp_call_keepLsCl hmemcpy_raw (x := (dst, src, bs1 ++ bs2))
    (F := relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ Frame)
    hcl hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => by
      dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at h
      simp only [sepConj_assoc, satisfies_pure_sepConj] at h
      exact h.1.elim)
    (fun _ h => by
      dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at h
      simp only [sepConj_assoc, satisfies_pure_sepConj] at h
      exact h.1.elim)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcl_sf => ?_)
  · intro R' hm
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen12]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2⟩, hm⟩
  · dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨_, htr⟩ => ?_
    have hrec := memcpy_keep_relocate_recombine (F := F) (G := G) hoff hlen1 hlen2 dst src
    have hpost_ent :
        (((dst ↦ₛ (bs1 ++ bs2)) ∗ (src ↦ₛ (bs1 ++ bs2))) ∗
          (relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ Frame)) ⊢
        (((memRegion dst k ∗ G (dst + off)) ∗
          (F src ∗ memRegion (src + off) m)) ∗ Frame) := by
      have hreord :
          (((dst ↦ₛ (bs1 ++ bs2)) ∗ (src ↦ₛ (bs1 ++ bs2))) ∗
            (relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ Frame)) =
          ((dst ↦ₛ (bs1 ++ bs2)) ∗ (src ↦ₛ (bs1 ++ bs2)) ∗
            relocatedHeap F bs1 ∗ relocatedHeap G bs2) ∗ Frame := by ac_rfl
      rw [hreord]
      exact sepConj_mono_left hrec
    refine SepWPp.weaken_pre hpost_ent ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hcl_sf

theorem call_decoderIntoPb_expose_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377)
      (withLsCodeLoaded lsmpl (decoderIntoPbSpec A)))
    (outDecA decA : BitVec 64) (dec : PolyDecoder)
    {s0 s : State} {ret_pc : BitVec 64} {P Frame R : SepProp}
    {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 377)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = outDecA)
    (hx1 : s.readReg64 .x1 = decA)
    (hsplit : P = (memRegion outDecA protoPolynomialDecoderSize ∗
      polyDecoderAt A decA dec ∗
      A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
    (hnext : ∀ (sf : State) (d0 d1 d2 d3 d4 : BitVec 64),
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      TraceCalleeSaved sf s0 →
      SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (((outDecA ↦₆₄ d0) ∗ ((outDecA + 8#64) ↦₆₄ d1) ∗ ((outDecA + 16#64) ↦₆₄ d2) ∗
          ((outDecA + 24#64) ↦₆₄ d3) ∗ ((outDecA + 32#64) ↦₆₄ d4) ∗
          protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 dec.intoPb ∗
          memRegion decA polyDecoderSize ∗
          A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
        Q (StatesIntoPbPanic s0 R)) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      Q (StatesIntoPbPanic s0 R) := by
  refine SepWPp.call hdec_cl (x := ⟨outDecA, decA, dec⟩)
    (F := memRegion ((s0.sp - 1520#64) - 4352#64) 64 ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => by
      dsimp only [withLsCodeLoaded] at h
      exact allowPanic_not_exited h)
    (fun sf _ => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
    (fun _ _ _ h => by
      dsimp only [withLsCodeLoaded, decoderIntoPbSpec] at h
      simp only [sepConj_assoc, satisfies_pure_sepConj] at h
      exact h.1.elim)
  · intro R' hm
    rw [hsplit, stackAt_encoderIntoPb_eq_decoderIntoPb (s0.sp - 1520#64)] at hm
    dsimp only [withLsCodeLoaded, decoderIntoPbSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    refine ⟨⟨hx0, hx1⟩, ?_⟩
    have hm1 : s.mem ⊨ ⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗
        (memRegion outDecA protoPolynomialDecoderSize ∗
         polyDecoderAt A decA dec ∗
         A.pool ∗
         stackAt (s0.sp - 1520#64) decoderIntoPbStack ∗
         memRegion ((s0.sp - 1520#64) - 4352#64) 64 ∗ Frame ∗ R') := by
      rw [satisfies_pure_sepConj]
      exact ⟨hcl, Satisfies.mono (Entails.of_eq (by ac_rfl)) hm⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm1
  · change (sf.mem ⊨ ((withLsCodeLoaded lsmpl (decoderIntoPbSpec A)).onPanic ⟨outDecA, decA, dec⟩ s sf ∗
      (memRegion ((s0.sp - 1520#64) - 4352#64) 64 ∗ Frame)) ∗ R) →
      (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)
    intro hmem
    dsimp only [withLsCodeLoaded, decoderIntoPbSpec] at hmem
    rw [← sepConj_assoc]
    have hpan := allowPanic_frame (φ := allocFailedIn s sf ∧ s.trace <+: sf.trace)
      (ψ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      (fun ⟨haf, htr_sub⟩ => by
        unfold allocFailedIn at haf ⊢
        rw [htrace.1] at haf htr_sub
        exact ⟨haf, htr_sub⟩) hmem
    simpa only [sepConj_assoc] using hpan
  · dsimp only [withLsCodeLoaded, decoderIntoPbSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    have hexp :
        (protoPolynomialDecoderAt A outDecA dec.intoPb ∗
          memRegion decA polyDecoderSize ∗
          A.pool ∗ stackAt (s0.sp - 1520#64) decoderIntoPbStack) ∗
          (memRegion ((s0.sp - 1520#64) - 4352#64) 64 ∗ Frame) ⊢
        ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
        ∃∗ d3 : BitVec 64, ∃∗ d4 : BitVec 64,
          (((outDecA ↦₆₄ d0) ∗ ((outDecA + 8#64) ↦₆₄ d1) ∗ ((outDecA + 16#64) ↦₆₄ d2) ∗
            ((outDecA + 24#64) ↦₆₄ d3) ∗ ((outDecA + 32#64) ↦₆₄ d4) ∗
            protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 dec.intoPb ∗
            memRegion decA polyDecoderSize ∗
            A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame) := by
      refine Entails.trans (sepConj_mono_left (sepConj_mono_left (protoPolynomialDecoder_expose A outDecA dec.intoPb))) ?_
      simp only [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro d0
      apply Entails.sepExists_elim; intro d1
      apply Entails.sepExists_elim; intro d2
      apply Entails.sepExists_elim; intro d3
      apply Entails.sepExists_elim; intro d4
      refine Entails.sepExists_right d0 (Entails.sepExists_right d1
        (Entails.sepExists_right d2 (Entails.sepExists_right d3
          (Entails.sepExists_right d4 ?_))))
      rw [stackAt_encoderIntoPb_eq_decoderIntoPb (s0.sp - 1520#64)]
      exact Entails.of_eq (by ac_rfl)
    refine SepWPp.weaken_pre hexp ?_
    refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
      SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 =>
      SepWPp.exists_elim fun d4 => ?_
    exact hnext sf d0 d1 d2 d3 d4 hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

set_option maxHeartbeats 800000 in
/-- Complete proof of `<States>::into_pb` (Block `334`) on `.noHeaderReceived s` (Arm 5, tag `7`)
    with `withLsCodeLoaded` on both `<PolyDecoder>::into_pb` (`Block 377`) and Block `334`. -/
theorem states_into_pb_noHeaderReceived_cl_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec A)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec)
    (s : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpec A F (.noHeaderReceived s))) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨out, stA⟩ R s0 hpc hrun hpre hsp0_align
  simp only [withLsCodeLoaded, statesIntoPbVariantPlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0⟩, hmem0⟩
  have hmem1 : s0.mem ⊨ ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
      ((memRegion out optProtoInnerStateSize ∗
        chunkedStatesAt A stA (.noHeaderReceived s) ∗
        statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem0
  rw [satisfies_pure_sepConj] at hmem1
  rcases hmem1 with ⟨hcl0, hmem⟩
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A stA (.noHeaderReceived s) ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack,
    R, hmem, ?_⟩
  refine sepWPp_of_states_into_pb_wpp_placed s0 s0 out stA (.noHeaderReceived s) _ R ?_
  refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (chunkedNoHeaderReceived_expose A stA s))) ?_
  have hpull :
      memRegion out optProtoInnerStateSize ∗
        (∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
         ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
          (stA ↦₆₄ 7#64) ∗
          (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
           ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
           ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5)) ∗
          (((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
           polyDecoderAt A (stA + 64#64) s.receiving_hdr) ∗
          authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
          memRegion (stA + 464#64) 464) ∗
        statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
        stackAt s0.sp statesIntoPbStack ∗
        (stA ↦₆₄ 7#64) ∗
        ((((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
          ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
          ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5)) ∗
         (((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
          polyDecoderAt A (stA + 64#64) s.receiving_hdr) ∗
         authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
         memRegion (stA + 464#64) 464 ∗
         memRegion out optProtoInnerStateSize ∗
         statesIntoPbJumpTablePlacedAt ∗ A.pool) := by
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro a0
    apply Entails.sepExists_elim; intro a1
    apply Entails.sepExists_elim; intro a2
    apply Entails.sepExists_elim; intro a3
    apply Entails.sepExists_elim; intro a4
    apply Entails.sepExists_elim; intro a5
    refine Entails.sepExists_right a0 (Entails.sepExists_right a1
      (Entails.sepExists_right a2 (Entails.sepExists_right a3
        (Entails.sepExists_right a4 (Entails.sepExists_right a5 ?_)))))
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpull ?_
  refine SepWPp.exists_elim fun a0 => SepWPp.exists_elim fun a1 =>
    SepWPp.exists_elim fun a2 => SepWPp.exists_elim fun a3 =>
    SepWPp.exists_elim fun a4 => SepWPp.exists_elim fun a5 => ?_
  have hpro := states_into_pb_prologue_60_placed (ext := ext) s0 out stA 7#64
    ((((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
      ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
      ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5)) ∗
     (((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A (stA + 64#64) s.receiving_hdr) ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     memRegion (stA + 464#64) 464 ∗
     memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTablePlacedAt ∗ A.pool)
    hsp0_align hpc hrun hx8 hx0
  refine statesIntoPb_seq_sepWP_cl_placed hcl0 hpro fun s1 hpc1 hrun1 hcl1
    ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1⟩ => ?_
  rw [stack_1416_split_noHeaderReceived s0.sp]
  have hpre1 := states_into_pb_noHeaderReceived_pre1_placed (ext := ext) s0 s1 out stA
    hsp0_align hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
    (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
     cells (s0.sp - 1512#64) 19 ∗
     memRegion (s0.sp - 1360#64) 456 ∗
     memRegion (s0.sp - 904#64) 424 ∗
     memRegion (s0.sp - 480#64) protoPolynomialDecoderSize ∗
     cells (s0.sp - 440#64) 6 ∗
     memRegion (s0.sp - 392#64) 88 ∗
     cells (s0.sp - 304#64) 6 ∗
     cells (s0.sp - 256#64) 6 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 7#64) ∗
     (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
      ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
      ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5)) ∗
     (((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A (stA + 64#64) s.receiving_hdr) ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     memRegion (stA + 464#64) 464 ∗
     memRegion out optProtoInnerStateSize ∗
     A.pool)
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (statesIntoPb_seq_sepWP_cl_placed hcl1 hpre1 fun s2 hpc2 hrun2 hcl2
      ⟨hsp2, hlr2, hx0_2, hx1_2, hx2_2, hx29_2, hx28_2, hx26_2, hx21_2, hx20_2, hx19_2, htr2⟩ => ?_)
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  let F_words : BitVec 64 → SepProp := fun a =>
    (a ↦₆₄ a0) ∗ ((a + 8#64) ↦₆₄ a1) ∗ ((a + 16#64) ↦₆₄ a2) ∗
    ((a + 24#64) ↦₆₄ a3) ∗ ((a + 32#64) ↦₆₄ a4) ∗ ((a + 40#64) ↦₆₄ a5)
  let G_dec : BitVec 64 → SepProp := fun a =>
    (a ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A (a + 8#64) s.receiving_hdr
  have hF_src : F_words (stA + 8#64) =
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
       ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
       ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5)) := by
    dsimp only [F_words]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_src : G_dec ((stA + 8#64) + 48#64) =
      (((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
       polyDecoderAt A (stA + 64#64) s.receiving_hdr) := by
    dsimp only [G_dec]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_dst : G_dec ((s0.sp - 1360#64) + 48#64) =
      (((s0.sp - 1312#64) ↦₆₄ s.uc.epoch) ∗
       polyDecoderAt A (s0.sp - 1304#64) s.receiving_hdr) := by
    dsimp only [G_dec]
    simp only [arm64_norm]
  have hsrc_off : (stA + 8#64) + 48#64 = stA + 56#64 := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine call_memcpy_keep_relocate_cl_placed hmemcpy_raw
    (k := 48) (m := 408) (n := 456) (off := 48#64)
    (F := F_words) (G := G_dec)
    rfl rfl
    (Relocatable.words6 a0 a1 a2 a3 a4 a5)
    (Relocatable.epoch_polyDecoderAt A s.uc.epoch s.receiving_hdr)
    (s0.sp - 1360#64) (stA + 8#64)
    (Frame :=
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      cells (s0.sp - 1512#64) 19 ∗
      memRegion (s0.sp - 904#64) 424 ∗
      memRegion (s0.sp - 480#64) protoPolynomialDecoderSize ∗
      cells (s0.sp - 440#64) 6 ∗
      memRegion (s0.sp - 392#64) 88 ∗
      cells (s0.sp - 304#64) 6 ∗
      cells (s0.sp - 256#64) 6 ∗
      memRegion (s0.sp - 208#64) 112 ∗
      statesIntoPbSavedCells s0 ∗
      (stA ↦₆₄ 7#64) ∗
      authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      memRegion (stA + 464#64) 464 ∗
      memRegion out optProtoInnerStateSize ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool)
    hcl2 hpc2 hrun2 hsp2 hfsp_align hlr2 htr2 hx0_2 hx1_2 hx2_2
    (by rw [hF_src, hG_src]; ac_rfl)
    fun s3 hpc3 hrun3 hsp3 hcs3 htr3 hcl3 => ?_
  rw [hF_src, hG_dst, hsrc_off]
  have hx19_3 : s3.readReg64 .x19 = out := hcs3.1.trans hx19_2
  have hx20_3 : s3.readReg64 .x20 = stA := hcs3.2.1.trans hx20_2
  have hx21_3 : s3.readReg64 .x21 = s0.sp - 1360#64 := hcs3.2.2.1.trans hx21_2
  have hx26_3 : s3.readReg64 .x26 = s0.sp - 480#64 := hcs3.2.2.2.2.2.2.2.1.trans hx26_2
  have hx28_3 : s3.readReg64 .x28 = s0.sp - 256#64 := hcs3.2.2.2.2.2.2.2.2.2.1.trans hx28_2
  have hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64 := hcs3.2.2.2.2.2.2.2.2.2.2.1.trans hx29_2
  have hpre2 := states_into_pb_noHeaderReceived_pre2_placed (ext := ext) s0 s3 out stA
    a0 a1 a2 a3 a4 a5 s.uc.epoch
    hsp0_align hpc3 hrun3 hsp3 hx29_3 hx28_3 hx26_3 hx21_3 hx20_3 hx19_3 htr3
    (memRegion (s0.sp - 1360#64) 48 ∗
     polyDecoderAt A (s0.sp - 1304#64) s.receiving_hdr ∗
     memRegion (stA + 56#64) 408 ∗
     stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
     cells (s0.sp - 1512#64) 19 ∗
     memRegion (s0.sp - 904#64) 424 ∗
     memRegion (s0.sp - 480#64) protoPolynomialDecoderSize ∗
     cells (s0.sp - 440#64) 6 ∗
     memRegion (s0.sp - 392#64) 88 ∗
     cells (s0.sp - 304#64) 6 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 7#64) ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     memRegion (stA + 464#64) 464 ∗
     memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTablePlacedAt ∗ A.pool)
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (statesIntoPb_seq_sepWP_cl_placed hcl3 hpre2 fun s4 hpc4 hrun4 hcl4
      ⟨hsp4, hlr4, hx0_4, hx1_4, hx29_4, hx26_4, hx20_4, hx19_4, htr4⟩ => ?_)
  refine call_decoderIntoPb_expose_cl_placed hdec_cl (s0.sp - 480#64) (s0.sp - 1304#64) s.receiving_hdr
    (Frame :=
      cells (s0.sp - 1512#64) 19 ∗
      cells (s0.sp - 440#64) 6 ∗
      cells (s0.sp - 304#64) 6 ∗
      (((s0.sp - 256#64) ↦₆₄ a0) ∗ ((s0.sp - 248#64) ↦₆₄ a1) ∗
       ((s0.sp - 240#64) ↦₆₄ a2) ∗ ((s0.sp - 232#64) ↦₆₄ a3) ∗
       ((s0.sp - 224#64) ↦₆₄ a4) ∗ ((s0.sp - 216#64) ↦₆₄ a5)) ∗
      memRegion (s0.sp - 208#64) 112 ∗
      ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      memRegion (s0.sp - 1360#64) 48 ∗
      ((s0.sp - 1312#64) ↦₆₄ s.uc.epoch) ∗
      memRegion (s0.sp - 904#64) 424 ∗
      memRegion (s0.sp - 392#64) 88 ∗
      statesIntoPbSavedCells s0 ∗
      (stA ↦₆₄ 7#64) ∗
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
       ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
       ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5)) ∗
      memRegion (stA + 56#64) 408 ∗
      authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      memRegion (stA + 464#64) 464 ∗
      memRegion out optProtoInnerStateSize ∗
      statesIntoPbJumpTablePlacedAt)
    hcl4 hpc4 hrun4 hsp4 hfsp_align hlr4 htr4 hx0_4 hx1_4
    (by ac_rfl)
    fun sf d0 d1 d2 d3 d4 hpcf hrunf hspf hcsf htrf => ?_
  have hx19_f : sf.readReg64 .x19 = out := hcsf.1.trans hx19_4
  have hx20_f : sf.readReg64 .x20 = s.uc.epoch := hcsf.2.1.trans hx20_4
  have hx26_f : sf.readReg64 .x26 = s0.sp - 480#64 := hcsf.2.2.2.2.2.2.2.1.trans hx26_4
  have hx29_f : sf.readReg64 .x29 = s0.sp - 96#64 := hcsf.2.2.2.2.2.2.2.2.2.2.1.trans hx29_4
  apply SepWPp.of_sepWP_ret
  have hpost_step := states_into_pb_noHeaderReceived_post_placed (ext := ext) A F s0 sf out stA s
    a0 a1 a2 a3 a4 a5 d0 d1 d2 d3 d4
    hsp0_align hpcf hrunf hspf hx29_f hx26_f hx20_f hx19_f htrf
  refine SepWP.weaken_pre (Entails.of_eq ?_) hpost_step
  simp only [arm64_norm]
  ac_rfl

end CryptoVerification.SpqrV1.States.IntoPb
