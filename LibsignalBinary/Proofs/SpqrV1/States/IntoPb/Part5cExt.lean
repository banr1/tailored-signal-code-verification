/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Defs
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bExt
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 5c (`AllocContracts4K`: Arm 9 `ct1Acknowledged`)

Lifts `states_into_pb_ct1Acknowledged` from `AllocContracts` and stackless `sessionMemcpyRegionSpec`
to `SpqrV1.Alloc.AllocContracts4K`.
-/

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cExt

open Arm64 ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification.CodeLayout
open scoped CryptoVerification.SpqrV1.States.IntoPb
open scoped CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.LibsignalTripleRatchet
  (tripleRatchetProgAtExt withStack sessionMemcpyRegionSpec)
open CryptoVerification.LibsignalSpqrV1 (spqrPolyApi spqrAuthApi)
open CryptoVerification.SpqrV1.Alloc (AllocContracts4K)
open CryptoVerification.SpqrV1.Poly (polyDecoderAt polyDecoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.Poly.DecoderPb (DecoderIntoPbOkExt)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize optProtoInnerStateSize sub_ok_of_addr_eq
   none2Cap_add_two_beq_zero noneCap_add_two_beq_zero)
open CryptoVerification.SpqrV1.States.IntoPb
  (statesIntoPbName statesIntoPb_fnOff libsignalSessionCode_fnOff_memcpy fnAddr_fwd_eq
   statesIntoPbStack statesIntoPbVariantSpec statesIntoPbJumpTableAt statesIntoPbSavedCells
   StatesIntoPbPanic StatesIntoPbPost TraceCalleeSaved
   sepWPp_of_states_into_pb_wpp states_into_pb_prologue_60 states_into_pb_epilogue
   sub_ok_decoderIntoPb_raw call_decoderIntoPb_expose stackAt_encoderIntoPb_eq_allocHook
   epilogueStagingCells memRegion_1424_split_epilogue outWords28
   Relocatable relocatedHeap memcpy_keep_relocate_split memcpy_keep_relocate_recombine
   vecU8Heap vecU8CloneTail authenticatorHeap protoPolynomialDecoderHeap
   chunkedCt1Acknowledged_expose ct1AcknowledgedScratchCells
   memRegion_ct1Acknowledged_scratch_split ct1AcknowledgedScratchCells_entails_memRegions
   stA_ct1Acknowledged_entails_928 outWords28_entails_ct1Acknowledged
   ct1Acknowledged_step_60_to_372 ct1Acknowledged_step_376_to_424
   ct1Acknowledged_step_424_to_1812_4k ct1Acknowledged_step_1812_to_1900_4k
   ct1Acknowledged_step_1904_to_1544 bv_sub_sub_lit' bv_add_add_lit')

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

private theorem sub_ok_memcpy_4k_raw_5c {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "memcpy"))
      (withStack sessionMemcpyRegionSpec encoderIntoPbStack) :=
  sub_ok_of_addr_eq
    (fnAddr_fwd_eq
      (d := num% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "memcpy"))
      (b := b) (X := Rust.withPanics ext)
      statesIntoPb_fnOff libsignalSessionCode_fnOff_memcpy (by decide)).symm
    (hA.session_memcpy_region encoderIntoPbStack (by decide) (by decide))

private theorem call_memcpy_keep_relocate_4k_5c {b memcpy_pc : BitVec 64}
    {ext : String → Option (State → State)}
    (hmemcpy_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      memcpy_pc
      (withStack sessionMemcpyRegionSpec encoderIntoPbStack))
    {k m n : Nat} {off : BitVec 64}
    {F G : BitVec 64 → SepProp}
    (hoff : off = BitVec.ofNat 64 k)
    (hkm : k + m = n)
    (hF : Relocatable k F)
    (hG : Relocatable m G)
    (dst src : BitVec 64)
    {s0 s : State} {ret_pc : BitVec 64} {P Frame R : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s.pc = memcpy_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ (F src ∗ G (src + off))) ∗
      (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame))
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      TraceCalleeSaved sf s0 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        (((memRegion dst k ∗ G (dst + off)) ∗
          (F src ∗ memRegion (src + off) m)) ∗
          (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame))
        Q (StatesIntoPbPanic s0 R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      Q (StatesIntoPbPanic s0 R) := by
  have hpre_split :
      P ⊢ ∃∗ bs1 : List (BitVec 8), ∃∗ bs2 : List (BitVec 8),
        ⌜bs1.length = k ∧ bs2.length = m ∧ (bs1 ++ bs2).length = n⌝ ∗
        (memRegion dst n ∗ (src ↦ₛ (bs1 ++ bs2)) ∗ stackAt s.sp encoderIntoPbStack) ∗
        (relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ Frame) := by
    rw [hsplit, ← hsp]
    refine Entails.trans (sepConj_mono_left (sepConj_mono_right
      (memcpy_keep_relocate_split hoff hkm hF hG dst src))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs1
    apply Entails.sepExists_elim; intro bs2
    rw [sepConj_left_comm (memRegion dst n), sepConj_assoc (⌜_⌝)]
    apply Entails.pure_left; intro hpure
    refine Entails.sepExists_right bs1 (Entails.sepExists_right bs2 ?_)
    refine Entails.pure_right hpure ?_
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hpre_split ?_
  refine SepWPp.exists_elim fun bs1 => SepWPp.exists_elim fun bs2 => ?_
  refine SepWPp.pure_left fun ⟨hlen1, hlen2, hlen12⟩ => ?_
  refine SepWPp.call hmemcpy_raw (x := (dst, src, bs1 ++ bs2))
    (F := relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => by
      dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at h
      simp only [sepConj_assoc, satisfies_pure_sepConj] at h
      exact h.1.elim)
    (fun _ _ h => by
      dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at h
      simp only [sepConj_assoc, satisfies_pure_sepConj] at h
      exact h.1.elim)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen12]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2⟩, hm⟩
  · dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
    simp only [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨_, htr⟩ => ?_
    rw [hsp]
    have hrec := memcpy_keep_relocate_recombine (F := F) (G := G) hoff hlen1 hlen2 dst src
    have hpost_ent :
        ((dst ↦ₛ (bs1 ++ bs2)) ∗ (src ↦ₛ (bs1 ++ bs2)) ∗
          stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ Frame) ⊢
        (((memRegion dst k ∗ G (dst + off)) ∗
          (F src ∗ memRegion (src + off) m)) ∗
          (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)) := by
      have hreord :
          ((dst ↦ₛ (bs1 ++ bs2)) ∗ (src ↦ₛ (bs1 ++ bs2)) ∗
            stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
            relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ Frame) =
          ((dst ↦ₛ (bs1 ++ bs2)) ∗ (src ↦ₛ (bs1 ++ bs2)) ∗
            relocatedHeap F bs1 ∗ relocatedHeap G bs2) ∗
          (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame) := by sep_ac_rfl
      rw [hreord]
      exact sepConj_mono_left hrec
    refine SepWPp.weaken_pre hpost_ent ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

set_option maxHeartbeats 800000 in
/-- Arm 9 (`States.ct1Acknowledged`, tag `11`, jump table index `9` -> `+360`)
    under `AllocContracts4K`. -/
theorem states_into_pb_ct1Acknowledged_4k
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (hdec : DecoderIntoPbOkExt b A ext)
    (s : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Acknowledged
      spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpec A F b (.ct1Acknowledged s)) := by
  have hdec_raw := sub_ok_decoderIntoPb_raw hdec
  have hmemcpy_raw := sub_ok_memcpy_4k_raw_5c hA
  apply subroutine_ok_of_sepWPp
  intro ⟨out, stA⟩ R s0 hpc hrun hpre hsp0_align
  simp only [statesIntoPbVariantSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hb_align⟩, hmem⟩
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A stA (.ct1Acknowledged s) ∗
      statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_wpp s0 s0 out stA (.ct1Acknowledged s) _ R ?_
  refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (chunkedCt1Acknowledged_expose A stA s))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro a0
  apply SepWPp.exists_elim; intro a1
  apply SepWPp.exists_elim; intro a2
  apply SepWPp.exists_elim; intro a3
  apply SepWPp.exists_elim; intro a4
  apply SepWPp.exists_elim; intro a5
  apply SepWPp.exists_elim; intro hdr0
  apply SepWPp.exists_elim; intro hdr1
  apply SepWPp.exists_elim; intro hdr2
  apply SepWPp.exists_elim; intro es0
  apply SepWPp.exists_elim; intro es1
  apply SepWPp.exists_elim; intro es2
  apply SepWPp.exists_elim; intro cap_ct1
  apply SepWPp.exists_elim; intro ptr_ct1
  rw [show memRegion out optProtoInnerStateSize ∗
      ⌜s.uc.ct1.length < 2 ^ 63⌝ ∗
      (stA ↦₆₄ 11#64) ∗
      ((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
      ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
      ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2) ∗
      ((stA + 104#64) ↦₆₄ cap_ct1) ∗ ((stA + 112#64) ↦₆₄ ptr_ct1) ∗
      ((stA + 120#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
      ((stA + 128#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A (stA + 136#64) s.receiving_ek ∗
      (ptr_ct1 ↦ₛ s.uc.ct1) ∗
      vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
      authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
      vecU8Heap A es0 es1 es2 s.uc.es ∗
      memRegion (stA + 536#64) 392 ∗
      statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack =
      ⌜s.uc.ct1.length < 2 ^ 63⌝ ∗
      (stackAt s0.sp statesIntoPbStack ∗ (stA ↦₆₄ 11#64) ∗
       (statesIntoPbJumpTableAt b ∗
        memRegion out optProtoInnerStateSize ∗
        (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
         ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
         ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
         ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
        (((stA + 104#64) ↦₆₄ cap_ct1) ∗ ((stA + 112#64) ↦₆₄ ptr_ct1) ∗
         ((stA + 120#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
         ((stA + 128#64) ↦₆₄ s.uc.epoch) ∗
         polyDecoderAt A (stA + 136#64) s.receiving_ek) ∗
        (ptr_ct1 ↦ₛ s.uc.ct1) ∗
        vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
        vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
        vecU8Heap A es0 es1 es2 s.uc.es ∗
        memRegion (stA + 536#64) 392 ∗ A.pool)) by sep_ac_rfl]
  apply SepWPp.pure_elim; intro hlen
  have hpro := states_into_pb_prologue_60 s0 out stA 11#64
    (statesIntoPbJumpTableAt b ∗
     memRegion out optProtoInnerStateSize ∗
     (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
      ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
      ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
     (((stA + 104#64) ↦₆₄ cap_ct1) ∗ ((stA + 112#64) ↦₆₄ ptr_ct1) ∗
      ((stA + 120#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
      ((stA + 128#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A (stA + 136#64) s.receiving_ek) ∗
     (ptr_ct1 ↦ₛ s.uc.ct1) ∗
     vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A es0 es1 es2 s.uc.es ∗
     memRegion (stA + 536#64) 392 ∗ A.pool)
    hsp0_align hpc hrun hx8 hx0
  refine CryptoVerification.SpqrV1.States.IntoPb.DecoderPb.SepWPp.seq_clean hpro ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1⟩
  have h1424 :
      ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 1512#64) 1416 ⊢
      memRegion (s0.sp - 1520#64) 1424 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 1520#64) (n := 8) (k := 1416)
          (b' := s0.sp - 1512#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (pointsTo64_entails_memRegion (s0.sp - 1520#64) 0#64)
  refine SepWPp.weaken_pre
    (by
      rw [show stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 1512#64) 1416 ∗
          statesIntoPbSavedCells s0 ∗
          (stA ↦₆₄ 11#64) ∗
          (statesIntoPbJumpTableAt b ∗
           memRegion out optProtoInnerStateSize ∗
           (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
            ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
            ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
            ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
           (((stA + 104#64) ↦₆₄ cap_ct1) ∗ ((stA + 112#64) ↦₆₄ ptr_ct1) ∗
            ((stA + 120#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
            ((stA + 128#64) ↦₆₄ s.uc.epoch) ∗
            polyDecoderAt A (stA + 136#64) s.receiving_ek) ∗
           (ptr_ct1 ↦ₛ s.uc.ct1) ∗
           vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
           authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
           vecU8Heap A es0 es1 es2 s.uc.es ∗
           memRegion (stA + 536#64) 392 ∗ A.pool) =
          (((s0.sp - 1520#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 1512#64) 1416) ∗
          (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
           statesIntoPbSavedCells s0 ∗
           (stA ↦₆₄ 11#64) ∗
           statesIntoPbJumpTableAt b ∗
           memRegion out optProtoInnerStateSize ∗
           (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
            ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
            ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
            ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
           (((stA + 104#64) ↦₆₄ cap_ct1) ∗ ((stA + 112#64) ↦₆₄ ptr_ct1) ∗
            ((stA + 120#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
            ((stA + 128#64) ↦₆₄ s.uc.epoch) ∗
            polyDecoderAt A (stA + 136#64) s.receiving_ek) ∗
           (ptr_ct1 ↦ₛ s.uc.ct1) ∗
           vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
           authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
           vecU8Heap A es0 es1 es2 s.uc.es ∗
           memRegion (stA + 536#64) 392 ∗ A.pool) by sep_ac_rfl]
      exact sepConj_mono_left (Entails.trans h1424 (memRegion_1424_split_epilogue s0.sp))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro w8
  apply SepWPp.exists_elim; intro w16
  apply SepWPp.exists_elim; intro w24
  apply SepWPp.exists_elim; intro w32
  apply SepWPp.exists_elim; intro w40
  apply SepWPp.exists_elim; intro w48
  apply SepWPp.exists_elim; intro w64
  apply SepWPp.exists_elim; intro w72
  apply SepWPp.exists_elim; intro w80
  apply SepWPp.exists_elim; intro w88
  apply SepWPp.exists_elim; intro w96
  apply SepWPp.exists_elim; intro w104
  apply SepWPp.exists_elim; intro w112
  apply SepWPp.exists_elim; intro w120
  apply SepWPp.exists_elim; intro w128
  apply SepWPp.exists_elim; intro w136
  apply SepWPp.exists_elim; intro w144
  apply SepWPp.exists_elim; intro w152
  apply SepWPp.exists_elim; intro w160
  apply SepWPp.exists_elim; intro w168
  apply SepWPp.exists_elim; intro w176
  apply SepWPp.exists_elim; intro w184
  apply SepWPp.exists_elim; intro w192
  apply SepWPp.exists_elim; intro w200
  apply SepWPp.exists_elim; intro w208
  apply SepWPp.exists_elim; intro w216
  have hscratch_split :
      ∀ (Rest : SepProp),
        epilogueStagingCells s0.sp
          w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
          w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
        memRegion (s0.sp - 1360#64) 880 ∗
        memRegion (s0.sp - 480#64) 176 ∗
        memRegion (s0.sp - 256#64) 160 ∗ Rest ⊢
        epilogueStagingCells s0.sp
          w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
          w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
        (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
         ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
         ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
         ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
         ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64, ∃∗ v8 : BitVec 64,
         ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
         ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
         ∃∗ y0 : BitVec 64, ∃∗ y1 : BitVec 64, ∃∗ y2 : BitVec 64,
         ∃∗ y3 : BitVec 64, ∃∗ y4 : BitVec 64, ∃∗ y5 : BitVec 64,
           ct1AcknowledgedScratchCells s0.sp
             u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 v6 v7 v8
             w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
           memRegion (s0.sp - 1360#64) 528 ∗
           memRegion (s0.sp - 832#64) 352 ∗
           memRegion (s0.sp - 432#64) 8 ∗
           memRegion (s0.sp - 352#64) 40 ∗
           memRegion (s0.sp - 312#64) 8 ∗
           memRegion (s0.sp - 208#64) 48 ∗
           memRegion (s0.sp - 112#64) 16) ∗ Rest := by
    intro Rest
    refine Entails.trans (Entails.of_eq (show _ =
      epilogueStagingCells s0.sp
        w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
        w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
      (memRegion (s0.sp - 1360#64) 880 ∗
       memRegion (s0.sp - 480#64) 176 ∗
       memRegion (s0.sp - 256#64) 160) ∗ Rest by sep_ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_left (memRegion_ct1Acknowledged_scratch_split s0.sp))
  refine SepWPp.weaken_pre (hscratch_split _) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro u0
  apply SepWPp.exists_elim; intro u1
  apply SepWPp.exists_elim; intro u2
  apply SepWPp.exists_elim; intro u3
  apply SepWPp.exists_elim; intro u4
  apply SepWPp.exists_elim; intro u5
  apply SepWPp.exists_elim; intro v0
  apply SepWPp.exists_elim; intro v1
  apply SepWPp.exists_elim; intro v2
  apply SepWPp.exists_elim; intro v3
  apply SepWPp.exists_elim; intro v4
  apply SepWPp.exists_elim; intro v5
  apply SepWPp.exists_elim; intro v6
  apply SepWPp.exists_elim; intro v7
  apply SepWPp.exists_elim; intro v8
  apply SepWPp.exists_elim; intro w0
  apply SepWPp.exists_elim; intro w1
  apply SepWPp.exists_elim; intro w2
  apply SepWPp.exists_elim; intro w3
  apply SepWPp.exists_elim; intro w4
  apply SepWPp.exists_elim; intro w5
  apply SepWPp.exists_elim; intro y0
  apply SepWPp.exists_elim; intro y1
  apply SepWPp.exists_elim; intro y2
  apply SepWPp.exists_elim; intro y3
  apply SepWPp.exists_elim; intro y4
  apply SepWPp.exists_elim; intro y5
  have hpre1 := ct1Acknowledged_step_60_to_372 s0 s1 out stA
    (epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     ct1AcknowledgedScratchCells s0.sp
       u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 v6 v7 v8
       w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
     memRegion (s0.sp - 1360#64) 528 ∗
     memRegion (s0.sp - 832#64) 352 ∗
     memRegion (s0.sp - 432#64) 8 ∗
     memRegion (s0.sp - 352#64) 40 ∗
     memRegion (s0.sp - 312#64) 8 ∗
     memRegion (s0.sp - 208#64) 48 ∗
     memRegion (s0.sp - 112#64) 16 ∗
     stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 11#64) ∗
     memRegion out optProtoInnerStateSize ∗
     (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
      ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
      ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
     (((stA + 104#64) ↦₆₄ cap_ct1) ∗ ((stA + 112#64) ↦₆₄ ptr_ct1) ∗
      ((stA + 120#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
      ((stA + 128#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A (stA + 136#64) s.receiving_ek) ∗
     (ptr_ct1 ↦ₛ s.uc.ct1) ∗
     vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A es0 es1 es2 s.uc.es ∗
     memRegion (stA + 536#64) 392 ∗ A.pool)
    hb_align hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
  refine CryptoVerification.SpqrV1.States.IntoPb.DecoderPb.SepWPp.seq_clean
    (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hpre1) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hlr2, hx0_2, hx1_2, hx2_2, hx29_2, hx28_2, hx26_2, hx20_2, hx19_2, htr2⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  let F_words : BitVec 64 → SepProp := fun a =>
    (a ↦₆₄ a0) ∗ ((a + 8#64) ↦₆₄ a1) ∗ ((a + 16#64) ↦₆₄ a2) ∗
    ((a + 24#64) ↦₆₄ a3) ∗ ((a + 32#64) ↦₆₄ a4) ∗ ((a + 40#64) ↦₆₄ a5) ∗
    ((a + 48#64) ↦₆₄ hdr0) ∗ ((a + 56#64) ↦₆₄ hdr1) ∗ ((a + 64#64) ↦₆₄ hdr2) ∗
    ((a + 72#64) ↦₆₄ es0) ∗ ((a + 80#64) ↦₆₄ es1) ∗ ((a + 88#64) ↦₆₄ es2)
  let G_dec : BitVec 64 → SepProp := fun a =>
    (a ↦₆₄ cap_ct1) ∗ ((a + 8#64) ↦₆₄ ptr_ct1) ∗
    ((a + 16#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
    ((a + 24#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A (a + 32#64) s.receiving_ek
  have hF_src : F_words (stA + 8#64) =
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
       ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
       ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) := by
    dsimp only [F_words]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_src : G_dec ((stA + 8#64) + 96#64) =
      (((stA + 104#64) ↦₆₄ cap_ct1) ∗ ((stA + 112#64) ↦₆₄ ptr_ct1) ∗
       ((stA + 120#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((stA + 128#64) ↦₆₄ s.uc.epoch) ∗
       polyDecoderAt A (stA + 136#64) s.receiving_ek) := by
    dsimp only [G_dec]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_dst : G_dec ((s0.sp - 1360#64) + 96#64) =
      (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
       ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((s0.sp - 1240#64) ↦₆₄ s.uc.epoch) ∗
       polyDecoderAt A (s0.sp - 1232#64) s.receiving_ek) := by
    dsimp only [G_dec]
    simp only [arm64_norm]
  have hsrc_off : (stA + 8#64) + 96#64 = stA + 104#64 := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine call_memcpy_keep_relocate_4k_5c hmemcpy_raw
    (k := 96) (m := 432) (n := 528) (off := 96#64)
    (F := F_words) (G := G_dec)
    rfl rfl
    (Relocatable.words12 a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2)
    (Relocatable.words4_polyDecoderAt A cap_ct1 ptr_ct1
      (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch s.receiving_ek)
    (s0.sp - 1360#64) (stA + 8#64)
    (Frame :=
      statesIntoPbJumpTableAt b ∗
      epilogueStagingCells s0.sp
        w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
        w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
      ct1AcknowledgedScratchCells s0.sp
        u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 v6 v7 v8
        w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
      memRegion (s0.sp - 832#64) 352 ∗
      memRegion (s0.sp - 432#64) 8 ∗
      memRegion (s0.sp - 352#64) 40 ∗
      memRegion (s0.sp - 312#64) 8 ∗
      memRegion (s0.sp - 208#64) 48 ∗
      memRegion (s0.sp - 112#64) 16 ∗
      statesIntoPbSavedCells s0 ∗
      (stA ↦₆₄ 11#64) ∗
      memRegion out optProtoInnerStateSize ∗
      (ptr_ct1 ↦ₛ s.uc.ct1) ∗
      vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
      authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
      vecU8Heap A es0 es1 es2 s.uc.es ∗
      memRegion (stA + 536#64) 392 ∗ A.pool)
    hpc2 hrun2 hsp2 hfsp_align hlr2 htr2 hx0_2 hx1_2 hx2_2
    (by rw [hF_src, hG_src]; sep_ac_rfl)
    fun s3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_
  rw [hF_src, hG_dst, hsrc_off]
  have hx19_3 : s3.readReg64 .x19 = out := hcs3.1.trans hx19_2
  have hx20_3 : s3.readReg64 .x20 = stA := hcs3.2.1.trans hx20_2
  have hx26_3 : s3.readReg64 .x26 = s0.sp - 480#64 := hcs3.2.2.2.2.2.2.2.1.trans hx26_2
  have hx28_3 : s3.readReg64 .x28 = s0.sp - 256#64 := hcs3.2.2.2.2.2.2.2.2.2.1.trans hx28_2
  have hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64 := hcs3.2.2.2.2.2.2.2.2.2.2.1.trans hx29_2
  have hstep2 := ct1Acknowledged_step_376_to_424 s0 s3 out stA
    a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2 cap_ct1 ptr_ct1 s.uc.epoch s.uc.ct1.length
    u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 v6 v7 v8
    w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5
    (memRegion (s0.sp - 1360#64) 96 ∗
     polyDecoderAt A (s0.sp - 1232#64) s.receiving_ek ∗
     memRegion (stA + 104#64) 432 ∗
     statesIntoPbJumpTableAt b ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     memRegion (s0.sp - 832#64) 352 ∗
     memRegion (s0.sp - 432#64) 8 ∗
     memRegion (s0.sp - 352#64) 40 ∗
     memRegion (s0.sp - 312#64) 8 ∗
     memRegion (s0.sp - 208#64) 48 ∗
     memRegion (s0.sp - 112#64) 16 ∗
     stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 11#64) ∗
     memRegion out optProtoInnerStateSize ∗
     (ptr_ct1 ↦ₛ s.uc.ct1) ∗
     vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A es0 es1 es2 s.uc.es ∗
     memRegion (stA + 536#64) 392 ∗ A.pool)
    hsp0_align hlen hpc3 hrun3 hsp3 hx29_3 hx28_3 hx26_3 hx20_3 hx19_3 htr3
  refine CryptoVerification.SpqrV1.States.IntoPb.DecoderPb.SepWPp.seq_clean
    (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep2) ?_
  intro s4 hpc4 hrun4 ⟨hsp4, hx29_4, hx28_4, hx27_4, hx26_4, hx24_4, hx23_4,
    hx21_4, hx20_4, hx19_4, htr4⟩
  rw [stackAt_encoderIntoPb_eq_allocHook (s0.sp - 1520#64)]
  refine SepWPp.weaken_pre ?_
    (ct1Acknowledged_step_424_to_1812_4k hA s0 s4 out stA cap_ct1 ptr_ct1 s.uc.epoch s.uc.ct1
      ((((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
        ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
        ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
       (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
        ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
        ((s0.sp - 1240#64) ↦₆₄ s.uc.epoch)) ∗
       ct1AcknowledgedScratchCells s0.sp
         a0 a1 a2 a3 a4 a5 v0 v1 v2 v3 v4 v5 v6 v7 v8
         w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
       memRegion (s0.sp - 1360#64) 96 ∗
       polyDecoderAt A (s0.sp - 1232#64) s.receiving_ek ∗
       memRegion (stA + 104#64) 432 ∗
       statesIntoPbJumpTableAt b ∗
       epilogueStagingCells s0.sp
         w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
         w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
       memRegion (s0.sp - 832#64) 352 ∗
       memRegion (s0.sp - 432#64) 8 ∗
       memRegion (s0.sp - 352#64) 40 ∗
       memRegion (s0.sp - 312#64) 8 ∗
       memRegion (s0.sp - 208#64) 48 ∗
       memRegion (s0.sp - 112#64) 16 ∗
       memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 11#64) ∗
       memRegion out optProtoInnerStateSize ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
       vecU8Heap A es0 es1 es2 s.uc.es ∗
       memRegion (stA + 536#64) 392)
      R hsp0_align hlen hpc4 hrun4 hsp4 hx29_4 hx28_4 hx27_4 hx26_4 hx24_4 hx23_4
      hx21_4 hx20_4 hx19_4 htr4 ?_)
  · exact Entails.of_eq (by sep_ac_rfl)
  intro s5 ptr_new hpc5 hrun5 hsp5 hx29_5 hx28_5 hx27_5 hx26_5 hx24_5 hx23_5
    hx22_5 hx21_5 hx20_5 hx19_5 htr5
  have hstep4 := ct1Acknowledged_step_1812_to_1900_4k hA s0 s5 out stA
    cap_ct1 ptr_ct1 ptr_new (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
    a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2
    v0 v1 v2 v3 v4 v5 v6 v7 v8
    w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5
    (vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
      ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
      ((s0.sp - 1240#64) ↦₆₄ s.uc.epoch)) ∗
     memRegion (s0.sp - 1360#64) 96 ∗
     polyDecoderAt A (s0.sp - 1232#64) s.receiving_ek ∗
     memRegion (stA + 104#64) 432 ∗
     statesIntoPbJumpTableAt b ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     memRegion (s0.sp - 832#64) 352 ∗
     memRegion (s0.sp - 432#64) 8 ∗
     memRegion (s0.sp - 352#64) 40 ∗
     memRegion (s0.sp - 312#64) 8 ∗
     memRegion (s0.sp - 208#64) 48 ∗
     memRegion (s0.sp - 112#64) 16 ∗
     memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 11#64) ∗
     memRegion out optProtoInnerStateSize ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A es0 es1 es2 s.uc.es ∗
     memRegion (stA + 536#64) 392)
    hsp0_align hpc5 hrun5 hsp5 hx29_5 hx28_5 hx27_5 hx26_5 hx24_5 hx23_5
    hx22_5 hx21_5 hx20_5 hx19_5 htr5
  refine CryptoVerification.SpqrV1.States.IntoPb.DecoderPb.SepWPp.seq_clean
    (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep4) ?_
  intro s6 hpc6 hrun6 ⟨hsp6, hlr6, hx0_6, hx1_6, hx29_6, hx27_6, hx26_6, hx22_6, hx21_6, hx19_6, htr6⟩
  have hrecomb_stack :
      memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗ stackAt (s0.sp - 1520#64) allocHookStack =
      stackAt (s0.sp - 1520#64) encoderIntoPbStack :=
    (stackAt_encoderIntoPb_eq_allocHook (s0.sp - 1520#64)).symm
  refine call_decoderIntoPb_expose hdec_raw (s0.sp - 352#64) (s0.sp - 1232#64) s.receiving_ek
    (Frame :=
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
       ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
       ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
      ct1AcknowledgedScratchCells s0.sp
        a0 a1 a2 a3 a4 a5 v0 v1 v2 v3 v4 v5 v6 v7 v8
        hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
      vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
        (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
      (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
       ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((s0.sp - 1240#64) ↦₆₄ s.uc.epoch)) ∗
      memRegion (s0.sp - 1360#64) 96 ∗
      memRegion (stA + 104#64) 432 ∗
      statesIntoPbJumpTableAt b ∗
      epilogueStagingCells s0.sp
        w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
        w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
      memRegion (s0.sp - 832#64) 352 ∗
      memRegion (s0.sp - 432#64) 8 ∗
      memRegion (s0.sp - 312#64) 8 ∗
      memRegion (s0.sp - 208#64) 48 ∗
      memRegion (s0.sp - 112#64) 16 ∗
      statesIntoPbSavedCells s0 ∗
      (stA ↦₆₄ 11#64) ∗
      memRegion out optProtoInnerStateSize ∗
      authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
      vecU8Heap A es0 es1 es2 s.uc.es ∗
      memRegion (stA + 536#64) 392)
    hpc6 hrun6 hsp6 hfsp_align hlr6 htr6 hx0_6 hx1_6
    (by
      rw [← hrecomb_stack]
      change _ = (memRegion (s0.sp - 352#64) 40 ∗
        polyDecoderAt A (s0.sp - 1232#64) s.receiving_ek ∗
        A.pool ∗
        (memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗
         stackAt (s0.sp - 1520#64) allocHookStack)) ∗ _
      sep_ac_rfl)
    fun s7 d0 d1 d2 d3 d4 hpc7 hrun7 hsp7 hcs7 htr7 => ?_
  have hx19_7 : s7.readReg64 .x19 = out := hcs7.1.trans hx19_6
  have hx21_7 : s7.readReg64 .x21 = BitVec.ofNat 64 s.uc.ct1.length := hcs7.2.2.1.trans hx21_6
  have hx22_7 : s7.readReg64 .x22 = ptr_new := hcs7.2.2.2.1.trans hx22_6
  have hx26_7 : s7.readReg64 .x26 = s0.sp - 480#64 := hcs7.2.2.2.2.2.2.2.1.trans hx26_6
  have hx27_7 : s7.readReg64 .x27 = s.uc.epoch := hcs7.2.2.2.2.2.2.2.2.1.trans hx27_6
  have hx29_7 : s7.readReg64 .x29 = s0.sp - 96#64 := hcs7.2.2.2.2.2.2.2.2.2.2.1.trans hx29_6
  simp only [arm64_norm]
  have hstep5 := ct1Acknowledged_step_1904_to_1544 s0 s7 out ptr_new
    (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
    a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2
    d0 d1 d2 d3 d4
    v0 v1 v2 v3 v4 v5 v6 v7 v8
    w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
    w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216
    (protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
     memRegion (s0.sp - 1232#64) polyDecoderSize ∗
     A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
      ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
      ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
     vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
      ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
      ((s0.sp - 1240#64) ↦₆₄ s.uc.epoch)) ∗
     memRegion (s0.sp - 1360#64) 96 ∗
     memRegion (stA + 104#64) 432 ∗
     statesIntoPbJumpTableAt b ∗
     memRegion (s0.sp - 832#64) 352 ∗
     memRegion (s0.sp - 432#64) 8 ∗
     memRegion (s0.sp - 312#64) 8 ∗
     memRegion (s0.sp - 208#64) 48 ∗
     memRegion (s0.sp - 112#64) 16 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 11#64) ∗
     memRegion out optProtoInnerStateSize ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A es0 es1 es2 s.uc.es ∗
     memRegion (stA + 536#64) 392)
    hsp0_align hpc7 hrun7 hsp7 hx29_7 hx27_7 hx26_7 hx22_7 hx21_7 hx19_7 htr7
  refine CryptoVerification.SpqrV1.States.IntoPb.DecoderPb.SepWPp.seq_clean
    (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep5) ?_
  intro s8 hpc8 hrun8 ⟨hsp8, hx29_8, hx19_8, hx21_8, hx22_8, htr8⟩
  have hscratch := ct1AcknowledgedScratchCells_entails_memRegions s0.sp
    hdr0 hdr1 hdr2 es0 es1 es2
    ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5 s.uc.epoch
    hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5
    cap_ct1 ptr_ct1 (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
    d0 d1 d2 d3 d4
  have hstA := stA_ct1Acknowledged_entails_928 stA
    a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2
  have hpre_epi :
      ct1AcknowledgedScratchCells s0.sp
        hdr0 hdr1 hdr2 es0 es1 es2
        ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5 s.uc.epoch
        hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
      (((s0.sp - 352#64) ↦₆₄ d0) ∗ ((s0.sp - 344#64) ↦₆₄ d1) ∗
       ((s0.sp - 336#64) ↦₆₄ d2) ∗ ((s0.sp - 328#64) ↦₆₄ d3) ∗
       ((s0.sp - 320#64) ↦₆₄ d4)) ∗
      epilogueStagingCells s0.sp
        hdr0 hdr1 hdr2 es0 es1 es2
        ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
        s.uc.epoch d0 d1 d2 d3 d4 w176 w184
        w192 w200 w208 w216 ∗
      (protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
       memRegion (s0.sp - 1232#64) polyDecoderSize ∗
       A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
        ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
        ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
       vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
        ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
        ((s0.sp - 1240#64) ↦₆₄ s.uc.epoch)) ∗
       memRegion (s0.sp - 1360#64) 96 ∗
       memRegion (stA + 104#64) 432 ∗
       statesIntoPbJumpTableAt b ∗
       memRegion (s0.sp - 832#64) 352 ∗
       memRegion (s0.sp - 432#64) 8 ∗
       memRegion (s0.sp - 312#64) 8 ∗
       memRegion (s0.sp - 208#64) 48 ∗
       memRegion (s0.sp - 112#64) 16 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 11#64) ∗
       memRegion out optProtoInnerStateSize ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
       vecU8Heap A es0 es1 es2 s.uc.es ∗
       memRegion (stA + 536#64) 392) ⊢
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      epilogueStagingCells s0.sp
        hdr0 hdr1 hdr2 es0 es1 es2
        ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
        s.uc.epoch d0 d1 d2 d3 d4 w176 w184
        w192 w200 w208 w216 ∗
      memRegion (s0.sp - 1360#64) 880 ∗
      memRegion (s0.sp - 480#64) 176 ∗
      memRegion (s0.sp - 256#64) 160 ∗
      statesIntoPbSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗
      (protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
       vecU8Heap A es0 es1 es2 s.uc.es ∗
       vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       memRegion stA chunkedStatesSize ∗
       statesIntoPbJumpTableAt b ∗ A.pool) := by
    dsimp only [polyDecoderSize] at *
    refine Entails.trans (Entails.of_eq (show _ =
      (ct1AcknowledgedScratchCells s0.sp
         hdr0 hdr1 hdr2 es0 es1 es2
         ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5 s.uc.epoch
         hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
       (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
        ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
        ((s0.sp - 1240#64) ↦₆₄ s.uc.epoch)) ∗
       (((s0.sp - 352#64) ↦₆₄ d0) ∗ ((s0.sp - 344#64) ↦₆₄ d1) ∗
        ((s0.sp - 336#64) ↦₆₄ d2) ∗ ((s0.sp - 328#64) ↦₆₄ d3) ∗
        ((s0.sp - 320#64) ↦₆₄ d4)) ∗
       memRegion (s0.sp - 1360#64) 96 ∗
       memRegion (s0.sp - 1232#64) 400 ∗
       memRegion (s0.sp - 832#64) 352 ∗
       memRegion (s0.sp - 432#64) 8 ∗
       memRegion (s0.sp - 312#64) 8 ∗
       memRegion (s0.sp - 208#64) 48 ∗
       memRegion (s0.sp - 112#64) 16) ∗
      ((stA ↦₆₄ 11#64) ∗
       (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
        ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
        ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
       memRegion (stA + 104#64) 432 ∗
       memRegion (stA + 536#64) 392) ∗
      (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       epilogueStagingCells s0.sp
         hdr0 hdr1 hdr2 es0 es1 es2
         ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
         s.uc.epoch d0 d1 d2 d3 d4 w176 w184
         w192 w200 w208 w216 ∗
       statesIntoPbSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗
       protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
       vecU8Heap A es0 es1 es2 s.uc.es ∗
       vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       statesIntoPbJumpTableAt b ∗ A.pool) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hscratch (sepConj_mono hstA (Entails.refl _))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  apply SepWPp.of_sepWP_ret
  have hep := states_into_pb_epilogue s0 s8 out
    hdr0 hdr1 hdr2 es0 es1 es2
    ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
    s.uc.epoch d0 d1 d2 d3 d4 w176 w184
    w192 w200 w208 w216
    (protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A es0 es1 es2 s.uc.es ∗
     vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTableAt b ∗ A.pool)
    hsp0_align hpc8 hrun8 hsp8 hx29_8 hx19_8 htr8
  rw [hx22_8, hx21_8] at hep
  unfold StatesIntoPbPost
  refine SepWP.strengthen_entails_const ?_ (SepWP.weaken_pre hpre_epi hep)
  have hout := outWords28_entails_ct1Acknowledged A out
    hdr0 hdr1 hdr2 es0 es1 es2
    (BitVec.ofNat 64 s.uc.ct1.length) ptr_new (BitVec.ofNat 64 s.uc.ct1.length)
    a0 a1 a2 a3 a4 a5
    d0 d1 d2 d3 d4
    w176 w184 w192 w200 w208 w216 s
  refine Entails.trans (Entails.of_eq (show _ =
    (outWords28 out
       9223372036854775817#64
       hdr0 hdr1 hdr2 es0 es1 es2
       (BitVec.ofNat 64 s.uc.ct1.length) ptr_new (BitVec.ofNat 64 s.uc.ct1.length)
       a0 a1 a2 a3 a4 a5 s.uc.epoch
       d0 d1 d2 d3 d4 w176 w184
       w192 w200 w208 w216 ∗
     protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A es0 es1 es2 s.uc.es ∗
     vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1) ∗
    (memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack) by sep_ac_rfl)) ?_
  exact sepConj_mono_left hout

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cExt

-- AUTO-BRIDGE BEGIN
namespace CryptoVerification.SpqrV1.States.IntoPb
export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cExt
  (states_into_pb_ct1Acknowledged_4k)
end CryptoVerification.SpqrV1.States.IntoPb
-- AUTO-BRIDGE END
