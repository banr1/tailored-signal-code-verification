/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroAPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import ProofLib.SepLogic.WPp

/-!
# `VerNe.Chain3` (Block `516`) Part B (`Srk` and `ChainKey`) under `LibsignalCodeRoLoaded`

Verifies the `Srk` (`tag = 1`, `tag = 2`) and `ChainKey` (`tag = 3`) field slices of
`message::merge<Chain> [local#4]` (Block `516`) under `StoreKit.LibsignalCodeRoLoaded`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib SepProp ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains
open Proofs.libsignal.Hooks2
open Proofs.libsignal.Stage1X (growOneChainSpecX)
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalPlacement
open CryptoVerification.CliHandshake.Placed
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  Arm64.calleeSavedVRegs_advancePC Arm64.calleeSavedVRegs_setPC Arm64.calleeSavedVRegs_setMem
  Arm64.calleeSavedVRegs_setPState Arm64.calleeSavedVRegs_writeReg64 Arm64.calleeSavedVRegs_writeReg32
  Arm64.calleeSavedVRegs_writeReg Arm64.calleeSavedVRegs_writeVReg128_ite Arm64.isCalleeSavedVReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.calleeSavedVRegs_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.sp_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg64_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg32_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain
attribute [local simp, local arm64_norm]
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.getLsbD_63_eq_seedChain

/-! ## Unified `bl bytes::merge [local#5]` Call Helper -/

theorem c3_bm_call_cro [LibsignalPlacement] {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW ext)
    (v ptr0 bufRef slot curPtr sp0 ret_pc : BitVec 64) (b rest : List (BitVec 8))
    (hb : b.length < 128)
    (hlen_lt : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 514) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : (s.readReg64 .x0).setWidth 8 = 2#8)
    (hx1 : s.readReg64 .x1 = v) (hx2 : s.readReg64 .x2 = bufRef)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → sm.readReg64 .x0 = 0#64 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        ((vecU8At A0 v cap' ptr' b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      ((vecU8At A0 v 0#64 ptr0 [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R)) := by
  have hlen_lt63 : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 63 := by omega
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_240_aligned_c3_cro halign
  refine SepWPp.call_lscl_c3
    (x := BytesMergeGhost.mk .lengthDelimited v 0#64 ptr0 [] bufRef slot curPtr
      ([BitVec.ofNat 8 b.length] ++ b ++ rest))
    (F := F) hC.bm hpc hrun hsp_aligned hcl hlr ?_ ?_ ?_ ?_
  · intro R' hm
    refine intro_withLsCodeRoLoaded_c3 hcro ?_
    rw [stackAt_c3Sub_eq_bytesMerge (sp0 - 240#64)] at hm
    dsimp only [bytesMerge3RawSpec]
    rw [show A0.pool = emp from rfl, hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen_lt63, bytesMergeCapOk_zero⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro _ _ _ _ hm; exact allowPanic_not_exited hm
  · intro _ _ hm
    dsimp only [StoreKit.withLsCodeRoLoaded, bytesMerge3RawSpec, chainMerge3PlacedSpecW,
      chainMerge3RawSpecW, Serialization.allocPanic] at hm ⊢
    simp only [allocFailedIn] at hm ⊢; rw [htr] at hm; exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hclm hcsm
    rw [hsp] at hspm
    dsimp only [StoreKit.withLsCodeRoLoaded, bytesMerge3RawSpec]
    rw [mergeBytes_lt128_seedChain b rest hb, hsp]; dsimp only
    rw [show A0.pool = emp from rfl]; simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepConj_pure_left_comm]; refine SepWPp.pure_elim fun hx0m => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_elim fun _ => ?_
    have hcur := sliceCursorAfter_append_eq_seedChain slot curPtr ([BitVec.ofNat 8 b.length] ++ b) rest
    rw [show ([BitVec.ofNat 8 b.length] ++ b).length = b.length + 1 by simp] at hcur
    refine SepWPp.mono_pre_seedChain ?_
      (hnext sm cap' ptr' hpcm hrunm hspm hclm (htrm.trans htr) hcsm hx0m)
    rw [hcur, ← stackAt_c3Sub_eq_bytesMerge (sp0 - 240#64)]
    refine sep_ac_seedChain ?_; simp only [emp_sepConj]; ac_rfl

theorem c3_bm_call_srk_cro [LibsignalPlacement] {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW ext)
    (v bufRef slot curPtr sp0 ret_pc : BitVec 64) (b rest : List (BitVec 8))
    (hb : b.length < 128) (hb_ne : b ≠ [])
    (hlen_lt : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 514) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : (s.readReg64 .x0).setWidth 8 = 2#8)
    (hx1 : s.readReg64 .x1 = v) (hx2 : s.readReg64 .x2 = bufRef)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → sm.readReg64 .x0 = 0#64 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        ((chain3VecAt A0 v b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      ((chain3VecAt A0 v [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R)) := by
  refine SepWPp.mono_pre_seedChain
    (sepConj_mono_left (sepConj_mono_left (chain3VecAt_nil_elim A0 v))) ?_
  simp only [sepExists_sepConj_left]; refine SepWPp.exists_elim fun ptr0 => ?_
  refine c3_bm_call_cro hC v ptr0 bufRef slot curPtr sp0 ret_pc b rest hb hlen_lt
    hcro hpc hrun hsp halign hcl htr hlr hx0 hx1 hx2 ?_
  intro sm cap' ptr' hpcm hrunm hspm hclm htrm hcsm hx0m
  refine SepWPp.mono_pre_seedChain ?_ (hnext sm hpcm hrunm hspm hclm htrm hcsm hx0m)
  exact sepConj_mono_left (sepConj_mono_left (chain3VecAt_of_ne_nil A0 v cap' ptr' hb_ne))

/-! ## `Srk` Slice (`tag = 1` and `tag = 2`) -/

theorem step_chain3Tag1_cro [LibsignalPlacement] {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW ext)
    (a bufRef slot ptr sp0 : BitVec 64) (srk rest tail : List (BitVec 8))
    (hsrk_lt : srk.length < 128) (hsrk_ne : srk ≠ [])
    (hlen_lt : (pbBytes 1 srk ++ rest ++ tail).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem)
    (hpc : s0.pc = lsmpl.base 516 + 168#64) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (htr : s0.trace = s_init.trace)
    (hx19 : s0.readReg64 .x19 = bufRef) (hx20 : s0.readReg64 .x20 = a)
    (hx21 : s0.readReg64 .x21 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = lsmpl.base 516 + 168#64 → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s_init.trace →
      Chain3LoopRegsPreserved s0 sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ chain3VecAt A0 a srk ∗ (ptr ↦ₛ pbBytes 1 srk) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 1 srk).length) (rest ++ tail) ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s_init sf ∗ R))) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s0
      (((bufRef ↦₆₄ slot) ∗ chain3VecAt A0 a [] ∗
        sliceCursorAt slot ptr (pbBytes 1 srk ++ (rest ++ tail)) ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s_init sf ∗ R)) := by
  have hpb : pbBytes 1 srk = 0x0a#8 :: BitVec.ofNat 8 srk.length :: srk :=
    DeserializeGeneral.pbBytes_lt128_eq_seedChain 1 (by decide) srk hsrk_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 srk.length] ++ srk ++ (rest ++ tail)
  have hcons_eq : pbBytes 1 srk ++ (rest ++ tail) = 0x0a#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : tail.length < (0x0a#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x0a#8 :: rem1).length < 2 ^ 62 := by
    rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
  refine SepWPp.bind_lscro (mid := lsmpl.base 514)
    (Q1 := fun s3 P3 => s3.sp = sp0 - 240#64 ∧ LibsignalCodeLoaded lsmpl s3.mem ∧
      s3.trace = s_init.trace ∧ s3.readReg64 .lr = lsmpl.base 516 + 496#64 ∧
      (s3.readReg64 .x0).setWidth 8 = 2#8 ∧ s3.readReg64 .x1 = a ∧ s3.readReg64 .x2 = bufRef ∧
      Chain3LoopRegsPreserved s0 s3 ∧
      (P3 ⊢ (chain3VecAt A0 a [] ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAt slot (ptr + 1#64) rem1 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ ((ptr ↦₈ 0x0a#8) ∗ F))) hcro ?_ ?_
  · change s0.pc = (blkPl_516).base + 168#64 at hpc
    have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
    have h21 : s0.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := hx21
    refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 515) hcl ?_
    rw [hcons_eq]; unfold sliceCursorAt; simp only [sepConj_assoc]
    iterate 6 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hcl1
    refine SepWPp.mono_pre_seedChain
      (P' := (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr ([0x0a#8] ++ rem1) ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ (chain3VecAt A0 a [] ∗ F)))
      (by unfold sliceCursorAt; exact sep_ac_seedChain (by ac_rfl)) ?_
    refine c3_dv_call_cro hC bufRef slot ptr sp0 (lsmpl.base 516 + 192#64) 0x0a#64 [0x0a#8] rem1
      (decodeVarint_0a_cons rem1) hlen_cons_lt
      (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      (by simp only [hsp, arm64_norm]) halign hcl1 (by simp only [htr, arm64_norm])
      (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]) ?_
    intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hcs2 hx0_2 hx1_2
    have hregs2 : Chain3LoopRegsPreserved s0 s2 :=
      Chain3LoopRegsPreserved.trans
        ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm]⟩ (.of_calleeSaved hcs2)
    change s2.pc = (blkPl_516).base + 192#64 at hpc2
    have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    have h1_2 : s2.readReg64 (Reg.gpr 1#5) = 0x0a#64 := hx1_2
    have h19_2 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hregs2.1.trans hx19
    have h20_2 : s2.readReg64 (Reg.gpr 20#5) = a := hregs2.2.1.trans hx20
    refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 514) hcl2 ?_
    iterate 18 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_; intro hcl3
    refine SepWPp.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
      ⟨by simp only [hsp2, arm64_norm], hcl3, by simp only [htr2, arm64_norm],
       by simp only [arm64_norm]; rfl, by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm],
       hregs2.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm]⟩, ?_⟩
    rw [show BitVec.ofNat 64 ([0x0a#8] : List (BitVec 8)).length = 1#64 from rfl]
    simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
    unfold sliceCursorAt; exact sep_ac_seedChain (by ac_rfl)
  · intro s3 P3 hpc3 hrun3 hcro3 ⟨hsp3, hcl3, htr3, hlr3, hx0_3, hx1_3, hx2_3, hregs3, hent3⟩
    refine SepWPp.mono_pre_seedChain hent3 ?_
    have hrem1_lt : ([BitVec.ofNat 8 srk.length] ++ srk ++ (rest ++ tail)).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine c3_bm_call_srk_cro hC a bufRef slot (ptr + 1#64) sp0 (lsmpl.base 516 + 496#64)
      srk (rest ++ tail) hsrk_lt hsrk_ne hrem1_lt hcro3 hpc3 hrun3 hsp3 halign hcl3 htr3
      hlr3 hx0_3 hx1_3 hx2_3 ?_
    intro s4 hpc4 hrun4 hsp4 hcl4 htr4 hcs4 hx0_4
    change s4.pc = (blkPl_516).base + 496#64 at hpc4
    have h0_4 : s4.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_4
    refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 516 + 168#64) hcl4 ?_
    iterate 2 wp_step
    refine SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [hrun4, arm64_norm]) ?_; intro hcl5
    have hregs4 : Chain3LoopRegsPreserved s0 s4 := hregs3.trans (.of_calleeSaved hcs4)
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]; rfl)
      (by simp only [hrun4, arm64_norm]) (by simp only [hsp4, arm64_norm]) hcl5
      (by simp only [htr4, arm64_norm])
      (hregs4.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    rw [DeserializeGeneral.pbBytes_ptr_advance_seedChain 1 (by decide) ptr srk hsrk_lt,
      ← DeserializeGeneral.pbBytes_pointsTo_combine_seedChain 1 (by decide) ptr srk hsrk_lt]
    exact sep_ac_seedChain (by ac_rfl)

theorem step_chain3Tag2_cro [LibsignalPlacement] {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW ext)
    (a bufRef slot ptr sp0 : BitVec 64) (priv rest tail : List (BitVec 8))
    (hpriv_lt : priv.length < 128) (hpriv_ne : priv ≠ [])
    (hlen_lt : (pbBytes 2 priv ++ rest ++ tail).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem)
    (hpc : s0.pc = lsmpl.base 516 + 168#64) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (htr : s0.trace = s_init.trace)
    (hx19 : s0.readReg64 .x19 = bufRef) (hx20 : s0.readReg64 .x20 = a)
    (hx21 : s0.readReg64 .x21 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = lsmpl.base 516 + 168#64 → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s_init.trace →
      Chain3LoopRegsPreserved s0 sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ chain3VecAt A0 (a + 24#64) priv ∗ (ptr ↦ₛ pbBytes 2 priv) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 2 priv).length) (rest ++ tail) ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s_init sf ∗ R))) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s0
      (((bufRef ↦₆₄ slot) ∗ chain3VecAt A0 (a + 24#64) [] ∗
        sliceCursorAt slot ptr (pbBytes 2 priv ++ (rest ++ tail)) ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s_init sf ∗ R)) := by
  have hpb : pbBytes 2 priv = 0x12#8 :: BitVec.ofNat 8 priv.length :: priv :=
    DeserializeGeneral.pbBytes_lt128_eq_seedChain 2 (by decide) priv hpriv_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 priv.length] ++ priv ++ (rest ++ tail)
  have hcons_eq : pbBytes 2 priv ++ (rest ++ tail) = 0x12#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : tail.length < (0x12#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x12#8 :: rem1).length < 2 ^ 62 := by
    rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
  refine SepWPp.bind_lscro (mid := lsmpl.base 514)
    (Q1 := fun s3 P3 => s3.sp = sp0 - 240#64 ∧ LibsignalCodeLoaded lsmpl s3.mem ∧
      s3.trace = s_init.trace ∧ s3.readReg64 .lr = lsmpl.base 516 + 272#64 ∧
      (s3.readReg64 .x0).setWidth 8 = 2#8 ∧ s3.readReg64 .x1 = a + 24#64 ∧
      s3.readReg64 .x2 = bufRef ∧ Chain3LoopRegsPreserved s0 s3 ∧
      (P3 ⊢ (chain3VecAt A0 (a + 24#64) [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot (ptr + 1#64) rem1 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ ((ptr ↦₈ 0x12#8) ∗ F))) hcro ?_ ?_
  · change s0.pc = (blkPl_516).base + 168#64 at hpc
    have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
    have h21 : s0.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := hx21
    refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 515) hcl ?_
    rw [hcons_eq]; unfold sliceCursorAt; simp only [sepConj_assoc]
    iterate 6 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hcl1
    refine SepWPp.mono_pre_seedChain
      (P' := (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr ([0x12#8] ++ rem1) ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ (chain3VecAt A0 (a + 24#64) [] ∗ F)))
      (by unfold sliceCursorAt; exact sep_ac_seedChain (by ac_rfl)) ?_
    refine c3_dv_call_cro hC bufRef slot ptr sp0 (lsmpl.base 516 + 192#64) 0x12#64 [0x12#8] rem1
      (decodeVarint_12_cons rem1) hlen_cons_lt
      (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      (by simp only [hsp, arm64_norm]) halign hcl1 (by simp only [htr, arm64_norm])
      (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]) ?_
    intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hcs2 hx0_2 hx1_2
    have hregs2 : Chain3LoopRegsPreserved s0 s2 :=
      Chain3LoopRegsPreserved.trans
        ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm]⟩ (.of_calleeSaved hcs2)
    change s2.pc = (blkPl_516).base + 192#64 at hpc2
    have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    have h1_2 : s2.readReg64 (Reg.gpr 1#5) = 0x12#64 := hx1_2
    have h19_2 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hregs2.1.trans hx19
    have h20_2 : s2.readReg64 (Reg.gpr 20#5) = a := hregs2.2.1.trans hx20
    refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 514) hcl2 ?_
    iterate 20 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_; intro hcl3
    refine SepWPp.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
      ⟨by simp only [hsp2, arm64_norm], hcl3, by simp only [htr2, arm64_norm],
       by simp only [arm64_norm]; rfl, by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm],
       hregs2.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm]⟩, ?_⟩
    rw [show BitVec.ofNat 64 ([0x12#8] : List (BitVec 8)).length = 1#64 from rfl]
    simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
    unfold sliceCursorAt; exact sep_ac_seedChain (by ac_rfl)
  · intro s3 P3 hpc3 hrun3 hcro3 ⟨hsp3, hcl3, htr3, hlr3, hx0_3, hx1_3, hx2_3, hregs3, hent3⟩
    refine SepWPp.mono_pre_seedChain hent3 ?_
    have hrem1_lt : ([BitVec.ofNat 8 priv.length] ++ priv ++ (rest ++ tail)).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine c3_bm_call_srk_cro hC (a + 24#64) bufRef slot (ptr + 1#64) sp0 (lsmpl.base 516 + 272#64)
      priv (rest ++ tail) hpriv_lt hpriv_ne hrem1_lt hcro3 hpc3 hrun3 hsp3 halign hcl3 htr3
      hlr3 hx0_3 hx1_3 hx2_3 ?_
    intro s4 hpc4 hrun4 hsp4 hcl4 htr4 hcs4 hx0_4
    change s4.pc = (blkPl_516).base + 272#64 at hpc4
    have h0_4 : s4.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_4
    refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 516 + 168#64) hcl4 ?_
    iterate 2 wp_step
    refine SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [hrun4, arm64_norm]) ?_; intro hcl5
    have hregs4 : Chain3LoopRegsPreserved s0 s4 := hregs3.trans (.of_calleeSaved hcs4)
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]; rfl)
      (by simp only [hrun4, arm64_norm]) (by simp only [hsp4, arm64_norm]) hcl5
      (by simp only [htr4, arm64_norm])
      (hregs4.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    rw [DeserializeGeneral.pbBytes_ptr_advance_seedChain 2 (by decide) ptr priv hpriv_lt,
      ← DeserializeGeneral.pbBytes_pointsTo_combine_seedChain 2 (by decide) ptr priv hpriv_lt]
    exact sep_ac_seedChain (by ac_rfl)

private def tailFields_cro (c : ChainG) : List ChainField :=
  (match c.ck with | some (i, key) => [ChainField.ck i key] | none => []) ++ c.keys.map ChainField.key

private theorem fields_eq_tailFields_cro (c : ChainG) :
    c.fields = (if c.srk = [] then [] else [ChainField.srk c.srk]) ++
      ((if c.priv = [] then [] else [ChainField.priv c.priv]) ++ tailFields_cro c) := by
  unfold ChainG.fields tailFields_cro; cases c.ck <;> simp [List.append_assoc]

private theorem getElem?_tailFields_ne_srk_cro (c : ChainG) (j : Nat) (b : List (BitVec 8)) :
    (tailFields_cro c)[j]? ≠ some (ChainField.srk b) := by
  unfold tailFields_cro
  cases c.ck with
  | none => simp only [List.nil_append, List.getElem?_map]; cases c.keys[j]? <;> simp
  | some ik =>
    rcases ik with ⟨_, _⟩
    cases j with
    | zero => simp
    | succ j' =>
      simp only [List.singleton_append, List.getElem?_cons_succ, List.getElem?_map]
      cases c.keys[j']? <;> simp

private theorem getElem?_tailFields_ne_priv_cro (c : ChainG) (j : Nat) (b : List (BitVec 8)) :
    (tailFields_cro c)[j]? ≠ some (ChainField.priv b) := by
  unfold tailFields_cro
  cases c.ck with
  | none => simp only [List.nil_append, List.getElem?_map]; cases c.keys[j]? <;> simp
  | some ik =>
    rcases ik with ⟨_, _⟩
    cases j with
    | zero => simp
    | succ j' =>
      simp only [List.singleton_append, List.getElem?_cons_succ, List.getElem?_map]
      cases c.keys[j']? <;> simp

private theorem mem_fields_srk_ne_nil_cro {c : ChainG} {b : List (BitVec 8)}
    (hmem : ChainField.srk b ∈ c.fields) : b ≠ [] := by
  unfold ChainG.fields at hmem; rcases c with ⟨srk, priv, ck, keys⟩
  by_cases h1 : srk = [] <;> by_cases h2 : priv = [] <;> cases ck <;>
    simp [h1, h2] at hmem <;> subst hmem <;> exact h1

private theorem mem_fields_priv_ne_nil_cro {c : ChainG} {b : List (BitVec 8)}
    (hmem : ChainField.priv b ∈ c.fields) : b ≠ [] := by
  unfold ChainG.fields at hmem; rcases c with ⟨srk, priv, ck, keys⟩
  by_cases h1 : srk = [] <;> by_cases h2 : priv = [] <;> cases ck <;>
    simp [h1, h2] at hmem <;> subst hmem <;> exact h2

private theorem chainGAfter_srk_eq_nil_cro {c : ChainG} {k : Nat}
    (hk : k < c.fields.length) {b : List (BitVec 8)}
    (hfl : c.fields[k]'hk = .srk b) : (chainGAfter c k).srk = [] := by
  have hfl? : c.fields[k]? = some (.srk b) := by rw [List.getElem?_eq_getElem hk, hfl]
  rw [fields_eq_tailFields_cro c] at hfl?
  by_cases hs : c.srk = [] <;> by_cases hp : c.priv = []
  · simp only [hs, hp, ↓reduceIte, List.nil_append] at hfl?
    exact absurd hfl? (getElem?_tailFields_ne_srk_cro c k b)
  · simp only [hs, hp, ↓reduceIte, List.nil_append, List.singleton_append] at hfl?
    cases k with
    | zero => simp at hfl?
    | succ k' => exact absurd (by simpa using hfl?) (getElem?_tailFields_ne_srk_cro c k' b)
  · simp only [hs, hp, ↓reduceIte, List.nil_append, List.singleton_append] at hfl?
    cases k with
    | zero => rfl
    | succ k' => exact absurd (by simpa using hfl?) (getElem?_tailFields_ne_srk_cro c k' b)
  · simp only [hs, hp, ↓reduceIte, List.singleton_append] at hfl?
    rcases k with _ | _ | k'
    · rfl
    · simp at hfl?
    · exact absurd (by simpa using hfl?) (getElem?_tailFields_ne_srk_cro c k' b)

private theorem chainGAfter_priv_eq_nil_cro {c : ChainG} {k : Nat}
    (hk : k < c.fields.length) {b : List (BitVec 8)}
    (hfl : c.fields[k]'hk = .priv b) : (chainGAfter c k).priv = [] := by
  have hfl? : c.fields[k]? = some (.priv b) := by rw [List.getElem?_eq_getElem hk, hfl]
  rw [fields_eq_tailFields_cro c] at hfl?
  by_cases hs : c.srk = [] <;> by_cases hp : c.priv = []
  · simp only [hs, hp, ↓reduceIte, List.nil_append] at hfl?
    exact absurd hfl? (getElem?_tailFields_ne_priv_cro c k b)
  · simp only [hs, hp, ↓reduceIte, List.nil_append, List.singleton_append] at hfl?
    cases k with
    | zero => rfl
    | succ k' => exact absurd (by simpa using hfl?) (getElem?_tailFields_ne_priv_cro c k' b)
  · simp only [hs, hp, ↓reduceIte, List.nil_append, List.singleton_append] at hfl?
    cases k with
    | zero => simp at hfl?
    | succ k' => exact absurd (by simpa using hfl?) (getElem?_tailFields_ne_priv_cro c k' b)
  · simp only [hs, hp, ↓reduceIte, List.singleton_append] at hfl?
    rcases k with _ | _ | k'
    · simp at hfl?
    · unfold chainGAfter; rw [fields_eq_tailFields_cro c]; simp [hs, hp, ChainG.empty, ChainG.apply]
    · exact absurd (by simpa using hfl?) (getElem?_tailFields_ne_priv_cro c k' b)

theorem chain3Srk_cro_placed_ok [LibsignalPlacement] (ext : LibsignalHooks) :
    Chain3SrkCroStmt ext := by
  intro hC x R s0 k s hk htag ⟨hcro, hs⟩
  refine segStepG_keep_cro hcro ?_
  intro hL
  rcases hs with ⟨hpc, hrun, htr, hvregs, hcl, hsp, hal, hx29, hx19, hx20, hx21,
    hx22, hx23, hx24, hx26, hx27, hx28, hcOk, hlen, hmem⟩
  have hpc' : s.pc = lsmpl.base 516 + 168#64 := hpc
  have hsp_sub_align : (s0.sp - 240#64) &&& 15#64 = 0#64 := by
    have h1 : s.sp &&& 15#64 = 0#64 := by simpa [State.spAligned, beq_iff_eq] using hal
    rwa [hsp] at h1
  have hsp0_align : s0.sp &&& 15#64 = 0#64 := sp0_aligned_of_sub_240_c3 hsp_sub_align
  let rest : List (BitVec 8) := (x.c.fields.drop (k + 1)).flatMap ChainField.enc
  have hlen_rem : ((x.c.fields[k]'hk).enc ++ rest ++ x.tail).length < 2 ^ 62 := by
    have h1 := hlen
    rw [payload_append_eq_preBytes x.c x.tail k, drop_flatMap_enc hk] at h1
    simp only [rest, List.length_append] at h1 ⊢; omega
  generalize hfl_eq : x.c.fields[k]'hk = fl
  cases fl with
  | ck _ _ => rw [hfl_eq] at htag; simp [ChainField.tag] at htag
  | key _ => rw [hfl_eq] at htag; simp [ChainField.tag] at htag
  | srk b =>
    have hb_mem : ChainField.srk b ∈ x.c.fields := hfl_eq ▸ List.getElem_mem hk
    have hb_lt : b.length < 128 := mem_fields_srk_length_lt hcOk hb_mem
    have hb_ne : b ≠ [] := mem_fields_srk_ne_nil_cro hb_mem
    have henc : (x.c.fields[k]'hk).enc = pbBytes 1 b := by
      rw [hfl_eq]; exact lenField_eq_pbBytes 1 (Or.inl rfl) b hb_lt
    have hlen_pb : (pbBytes 1 b ++ rest ++ x.tail).length < 2 ^ 62 := by rwa [← henc]
    let ck := chainGAfter x.c k
    have hck_srk : ck.srk = [] := chainGAfter_srk_eq_nil_cro hk hfl_eq
    let F : SepProp := (x.ptr ↦ₛ preBytes x.c k) ∗ chain3VecAt A0 (x.a + 24#64) ck.priv ∗
      chainGRest A0 x.a ck ∗ chain3SavedRegs s0.sp s0
    have hmem_pre : s.mem ⊨ (((x.bufRef ↦₆₄ x.slot) ∗ chain3VecAt A0 x.a [] ∗
        sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 1 b ++ (rest ++ x.tail)) ∗
        stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗ F) ∗ R := by
      rw [chain3GAt, hck_srk, sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail k,
        drop_flatMap_enc hk, henc] at hmem
      dsimp only [ck, F, rest] at hmem ⊢; simp only [List.append_assoc, sepConj_assoc] at hmem ⊢
      exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
    have hwp : SepWPp (lsProg_516 (Rust.withPanics ext)) (chain3PCPlacedAtW ext 168#64) s
        (((x.bufRef ↦₆₄ x.slot) ∗ chain3VecAt A0 x.a [] ∗
          sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 1 b ++ (rest ++ x.tail)) ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗ F)
        (fun sm Pm => (sm.mem ⊨ Pm ∗ R) → Chain3LoopPlacedAtW ext x R s0 (k + 1) sm)
        (fun sf Pf => (sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R)) := by
      refine step_chain3Tag1_cro hC x.a x.bufRef x.slot (curPtr x.ptr x.c k) s0.sp
        b rest x.tail hb_lt hb_ne hlen_pb hcro hpc' hrun hsp hsp0_align hcl htr hx19 hx20 hx21 ?_
      intro sm hpcm hrunm hspm hclm htrm hregsm
      refine SepWPp.done hpcm hrunm fun hmem_m => ?_
      refine ⟨hpcm, hrunm, htrm, hregsm.2.2.2.2.2.2.2.2.2.2.trans hvregs, hclm, hspm,
        by simp only [State.spAligned, hspm, ← hsp]; exact hal,
        hregsm.2.2.2.2.2.2.2.2.2.1.trans hx29, hregsm.1.trans hx19, hregsm.2.1.trans hx20,
        hregsm.2.2.1.trans hx21, hregsm.2.2.2.1.trans hx22, hregsm.2.2.2.2.1.trans hx23,
        hregsm.2.2.2.2.2.1.trans hx24, hregsm.2.2.2.2.2.2.1.trans hx26,
        hregsm.2.2.2.2.2.2.2.1.trans hx27, hregsm.2.2.2.2.2.2.2.2.1.trans hx28, hcOk, hlen, ?_⟩
      have hpost_eq :
          (((x.bufRef ↦₆₄ x.slot) ∗ chain3VecAt A0 x.a b ∗ (curPtr x.ptr x.c k ↦ₛ pbBytes 1 b) ∗
            sliceCursorAt x.slot (curPtr x.ptr x.c k + BitVec.ofNat 64 (pbBytes 1 b).length) (rest ++ x.tail) ∗
            stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗ F) =
          (chain3GAt A0 x.a (chainGAfter x.c (k + 1)) ∗ (x.bufRef ↦₆₄ x.slot) ∗
            sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) (rest ++ x.tail) ∗
            stackAt (s0.sp - 240#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0) := by
        rw [chainGAfter_succ hk, hfl_eq, chain3GAt_apply_srk A0 x.a ck b, ← henc,
          ← curPtr_succ x.ptr hk, sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail (k + 1),
          ← pointsToBytes_preBytes_succ x.ptr hk]
        dsimp only [ck, F, rest]; ac_rfl
      rw [hpost_eq] at hmem_m; simpa only [sepConj_assoc] using hmem_m
    obtain ⟨sf, hsteps, ⟨_, _, _, hmf, hloop⟩ | ⟨hpan, _, hmf, hpan_mem⟩ | ⟨_, hoom⟩⟩ := hwp R hmem_pre hL
    · exact ⟨sf, hsteps, Or.inl (hloop hmf)⟩
    · exact ⟨sf, hsteps, Or.inr ⟨hpan, hpan_mem hmf⟩⟩
    · exact (not_satisfies_false_sepConj hoom).elim
  | priv b =>
    have hb_mem : ChainField.priv b ∈ x.c.fields := hfl_eq ▸ List.getElem_mem hk
    have hb_lt : b.length < 128 := mem_fields_priv_length_lt hcOk hb_mem
    have hb_ne : b ≠ [] := mem_fields_priv_ne_nil_cro hb_mem
    have henc : (x.c.fields[k]'hk).enc = pbBytes 2 b := by
      rw [hfl_eq]; exact lenField_eq_pbBytes 2 (Or.inr rfl) b hb_lt
    have hlen_pb : (pbBytes 2 b ++ rest ++ x.tail).length < 2 ^ 62 := by rwa [← henc]
    let ck := chainGAfter x.c k
    have hck_priv : ck.priv = [] := chainGAfter_priv_eq_nil_cro hk hfl_eq
    let F : SepProp := (x.ptr ↦ₛ preBytes x.c k) ∗ chain3VecAt A0 x.a ck.srk ∗
      chainGRest A0 x.a ck ∗ chain3SavedRegs s0.sp s0
    have hmem_pre : s.mem ⊨ (((x.bufRef ↦₆₄ x.slot) ∗ chain3VecAt A0 (x.a + 24#64) [] ∗
        sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 2 b ++ (rest ++ x.tail)) ∗
        stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗ F) ∗ R := by
      rw [chain3GAt, hck_priv, sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail k,
        drop_flatMap_enc hk, henc] at hmem
      dsimp only [ck, F, rest] at hmem ⊢; simp only [List.append_assoc, sepConj_assoc] at hmem ⊢
      exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
    have hwp : SepWPp (lsProg_516 (Rust.withPanics ext)) (chain3PCPlacedAtW ext 168#64) s
        (((x.bufRef ↦₆₄ x.slot) ∗ chain3VecAt A0 (x.a + 24#64) [] ∗
          sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 2 b ++ (rest ++ x.tail)) ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗ F)
        (fun sm Pm => (sm.mem ⊨ Pm ∗ R) → Chain3LoopPlacedAtW ext x R s0 (k + 1) sm)
        (fun sf Pf => (sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R)) := by
      refine step_chain3Tag2_cro hC x.a x.bufRef x.slot (curPtr x.ptr x.c k) s0.sp
        b rest x.tail hb_lt hb_ne hlen_pb hcro hpc' hrun hsp hsp0_align hcl htr hx19 hx20 hx21 ?_
      intro sm hpcm hrunm hspm hclm htrm hregsm
      refine SepWPp.done hpcm hrunm fun hmem_m => ?_
      refine ⟨hpcm, hrunm, htrm, hregsm.2.2.2.2.2.2.2.2.2.2.trans hvregs, hclm, hspm,
        by simp only [State.spAligned, hspm, ← hsp]; exact hal,
        hregsm.2.2.2.2.2.2.2.2.2.1.trans hx29, hregsm.1.trans hx19, hregsm.2.1.trans hx20,
        hregsm.2.2.1.trans hx21, hregsm.2.2.2.1.trans hx22, hregsm.2.2.2.2.1.trans hx23,
        hregsm.2.2.2.2.2.1.trans hx24, hregsm.2.2.2.2.2.2.1.trans hx26,
        hregsm.2.2.2.2.2.2.2.1.trans hx27, hregsm.2.2.2.2.2.2.2.2.1.trans hx28, hcOk, hlen, ?_⟩
      have hpost_eq :
          (((x.bufRef ↦₆₄ x.slot) ∗ chain3VecAt A0 (x.a + 24#64) b ∗ (curPtr x.ptr x.c k ↦ₛ pbBytes 2 b) ∗
            sliceCursorAt x.slot (curPtr x.ptr x.c k + BitVec.ofNat 64 (pbBytes 2 b).length) (rest ++ x.tail) ∗
            stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗ F) =
          (chain3GAt A0 x.a (chainGAfter x.c (k + 1)) ∗ (x.bufRef ↦₆₄ x.slot) ∗
            sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) (rest ++ x.tail) ∗
            stackAt (s0.sp - 240#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0) := by
        rw [chainGAfter_succ hk, hfl_eq, chain3GAt_apply_priv A0 x.a ck b, ← henc,
          ← curPtr_succ x.ptr hk, sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail (k + 1),
          ← pointsToBytes_preBytes_succ x.ptr hk]
        dsimp only [ck, F, rest]; ac_rfl
      rw [hpost_eq] at hmem_m; simpa only [sepConj_assoc] using hmem_m
    obtain ⟨sf, hsteps, ⟨_, _, _, hmf, hloop⟩ | ⟨hpan, _, hmf, hpan_mem⟩ | ⟨_, hoom⟩⟩ := hwp R hmem_pre hL
    · exact ⟨sf, hsteps, Or.inl (hloop hmf)⟩
    · exact ⟨sf, hsteps, Or.inr ⟨hpan, hpan_mem hmf⟩⟩
    · exact (not_satisfies_false_sepConj hoom).elim

/-! ## `ChainKey` Slice (`tag = 3`) -/

section ChainKeySlice

open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG

private theorem c3_bm_call_vec_cro [LibsignalPlacement] {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW ext)
    (v bufRef slot curPtr sp0 ret_pc : BitVec 64) (b rest : List (BitVec 8))
    (hb : b.length < 128)
    (hlen_lt : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 514) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : (s.readReg64 .x0).setWidth 8 = 2#8)
    (hx1 : s.readReg64 .x1 = v) (hx2 : s.readReg64 .x2 = bufRef)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → sm.readReg64 .x0 = 0#64 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        ((vecU8 A0 v b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      ((chain3VecAt A0 v [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R)) := by
  refine SepWPp.mono_pre_seedChain
    (sepConj_mono_left (sepConj_mono_left (chain3VecAt_nil_elim A0 v))) ?_
  simp only [sepExists_sepConj_left]; refine SepWPp.exists_elim fun ptr0 => ?_
  refine c3_bm_call_cro hC v ptr0 bufRef slot curPtr sp0 ret_pc b rest hb hlen_lt
    hcro hpc hrun hsp halign hcl htr hlr hx0 hx1 hx2 ?_
  intro sm cap' ptr' hpcm hrunm hspm hclm htrm hcsm hx0m
  refine SepWPp.mono_pre_seedChain ?_ (hnext sm hpcm hrunm hspm hclm htrm hcsm hx0m)
  exact sepConj_mono_left (sepConj_mono_left
    (Entails.sepExists_right cap' (Entails.sepExists_right ptr' (Entails.refl _))))

private theorem c3a_dv_cro [LibsignalPlacement] {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW ext)
    (bufRef slot curPtr sp0 ret_pc v : BitVec 64) (b0 : BitVec 8) (rem1 : List (BitVec 8))
    (hdv : decodeVarint (b0 :: rem1) = some (v, rem1))
    (hlen_lt : (b0 :: rem1).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 515) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (htr : s.trace = s_init.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = bufRef)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s_init.trace →
      CalleeSavedPreserved s sm → sm.readReg64 .x0 = 0#64 → sm.readReg64 .x1 = v →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ (curPtr ↦₈ b0) ∗ sliceCursorAt slot (curPtr + 1#64) rem1 ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s_init sf ∗ R))) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot curPtr (b0 :: rem1) ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s_init sf ∗ R)) := by
  refine c3_dv_call_cro hC bufRef slot curPtr sp0 ret_pc v [b0] rem1 hdv hlen_lt
    hpc hrun hsp halign hcl htr hlr hx0 ?_
  intro sm hpcm hrunm hspm hclm htrm hcsm hx0m hx1m
  refine SepWPp.mono_pre_seedChain ?_ (hnext sm hpcm hrunm hspm hclm htrm hcsm hx0m hx1m)
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, List.length_singleton]
  exact Entails.refl _

private theorem step_seg3a_cro [LibsignalPlacement] {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW ext)
    (a bufRef slot ptr sp0 : BitVec 64)
    (ck_body afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (hck_lt : ck_body.length < 128) (houter_le : outerTailLen ≤ afterCk.length)
    (hlen_lt : 2 + (ck_body.length + afterCk.length) < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s0.pc = lsmpl.base 516 + 168#64) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx29 : s0.readReg64 .x29 = sp0 - 80#64) (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a) (hx21 : s0.readReg64 .x21 = BitVec.ofNat 64 outerTailLen)
    (hx22 : s0.readReg64 .x22 = sp0 - 232#64) (hx23 : s0.readReg64 .x23 = 1#64)
    (hx24 : s0.readReg64 .x24 = 104#64) (hx26 : s0.readReg64 .x26 = s_init.readReg64 .x26)
    (hx27 : s0.readReg64 .x27 = s_init.readReg64 .x27)
    (hx28 : s0.readReg64 .x28 = s_init.readReg64 .x28)
    (hnext : ∀ (sm : State),
      sm.pc = lsmpl.base 516 + 872#64 → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ chain3VecAt A0 (a + 72#64) [] ∗ ((a + 96#64) ↦₃₂ 0#32) ∗
          memRegion (a + 100#64) 4 ∗ (ptr ↦ₛ [0x1a#8, BitVec.ofNat 8 ck_body.length]) ∗
          sliceCursorAt slot (ptr + 2#64) (ck_body ++ afterCk) ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s_init sf ∗ R))) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s0
      (((bufRef ↦₆₄ slot) ∗ ((a + 72#64) ↦₆₄ noneCap) ∗ memRegion (a + 80#64) 24 ∗
        sliceCursorAt slot ptr (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s_init sf ∗ R)) := by
  have hlenA : (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)).length < 2 ^ 62 := by
    simp only [List.length_cons, List.length_append]; omega
  have hgtA : outerTailLen < (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)).length := by
    simp only [List.length_cons, List.length_append]; omega
  have hlenB : (BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)).length < 2 ^ 62 := by
    simp only [List.length_cons, List.length_append]; omega
  have hlenE : ck_body.length + afterCk.length < 2 ^ 62 := by omega
  refine SepWPp.mono_pre_seedChain (sep_ac_seedChain (Q :=
    ((bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
      stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
      ((((a + 72#64) ↦₆₄ noneCap) ∗ memRegion (a + 80#64) 24) ∗ F)) (by ac_rfl)) ?_
  refine c3a_phaseA_placed bufRef slot ptr sp0 _ outerTailLen hgtA hlenA
    hpc hrun hsp hcl htr hx19 hx21 ?_
  intro s1 hpc1 hrun1 hsp1 hcl1 htr1 hlr1 hx0_1 hk1
  refine c3a_dv_cro hC bufRef slot ptr sp0 (lsmpl.base 516 + 192#64) 0x1a#64 0x1a#8
    (BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) (c3a_decodeVarint_1a _) hlenA
    hpc1 hrun1 hsp1 halign hcl1 htr1 hlr1 hx0_1 ?_
  intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hcs2 hx0_2 hx1_2
  have hk2 : C3aKeep s0 s2 := hk1.trans (.of_calleeSaved hcs2)
  refine SepWPp.mono_pre_seedChain (sep_ac_seedChain (Q :=
    (((a + 72#64) ↦₆₄ noneCap) ∗ memRegion (a + 80#64) 24) ∗
      (((bufRef ↦₆₄ slot) ∗ (ptr ↦₈ 0x1a#8) ∗
        sliceCursorAt slot (ptr + 1#64) (BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)) (by ac_rfl)) ?_
  refine c3a_phaseC_placed a bufRef sp0 hpc2 hrun2 hsp2 hcl2 htr2 hx0_2 hx1_2
    (hk2.1.trans hx19) (hk2.2.1.trans hx20) (hk2.2.2.2.2.1.trans hx23) ?_
  intro s3 hpc3 hrun3 hsp3 hcl3 htr3 hlr3 hx0_3 hk3'
  have hk3 : C3aKeep s0 s3 := hk2.trans hk3'
  refine SepWPp.mono_pre_seedChain (sep_ac_seedChain (Q :=
    ((bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot (ptr + 1#64) (BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
      stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
      ((ptr ↦₈ 0x1a#8) ∗ (chain3VecAt A0 (a + 72#64) [] ∗ ((a + 96#64) ↦₃₂ 0#32) ∗
        memRegion (a + 100#64) 4) ∗ F)) (by ac_rfl)) ?_
  refine c3a_dv_cro hC bufRef slot (ptr + 1#64) sp0 (lsmpl.base 516 + 548#64)
    (BitVec.ofNat 64 ck_body.length) (BitVec.ofNat 8 ck_body.length) (ck_body ++ afterCk)
    (c3a_decodeVarint_lt128 ck_body.length hck_lt _) hlenB
    hpc3 hrun3 hsp3 halign hcl3 htr3 hlr3 hx0_3 ?_
  intro s4 hpc4 hrun4 hsp4 hcl4 htr4 hcs4 hx0_4 hx1_4
  have hk4 : C3aKeep s0 s4 := hk3.trans (.of_calleeSaved hcs4)
  refine SepWPp.mono_pre_seedChain (sep_ac_seedChain (Q :=
    ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot (ptr + 1#64 + 1#64) (ck_body ++ afterCk)) ∗
      (((ptr + 1#64) ↦₈ BitVec.ofNat 8 ck_body.length) ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX ∗
        (ptr ↦₈ 0x1a#8) ∗ (chain3VecAt A0 (a + 72#64) [] ∗ ((a + 96#64) ↦₃₂ 0#32) ∗
          memRegion (a + 100#64) 4) ∗ F)) (by ac_rfl)) ?_
  refine c3a_phaseE_placed bufRef slot (ptr + 1#64 + 1#64) ck_body afterCk hlenE
    hpc4 hrun4 hcl4 htr4 hx0_4 hx1_4 (hk4.1.trans hx19) ?_
  intro s5 hpc5 hrun5 hsp5 hcl5 htr5 hx25_5 hk5'
  have hk5 : C3aKeep s0 s5 := hk4.trans hk5'
  obtain ⟨k19, k20, k21, k22, k23, k24, k26, k27, k28, k29, kv⟩ := hk5
  refine SepWPp.mono_pre_seedChain ?_ (hnext s5 hpc5 hrun5 hcl5 htr5 (kv.trans hvregs)
    ⟨hsp5.trans hsp4, k29.trans hx29, k19.trans hx19, k20.trans hx20, k21.trans hx21,
     k22.trans hx22, k23.trans hx23, k24.trans hx24, hx25_5, k26.trans hx26, k27.trans hx27,
     k28.trans hx28⟩)
  have hptr2 : ptr + 1#64 + 1#64 = ptr + 2#64 := by bv_omega
  rw [hptr2, ← c3a_hdr_combine ptr ck_body.length]
  exact sep_ac_seedChain (by ac_rfl)

private theorem step_seg3b_cro [LibsignalPlacement] {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW ext)
    (a bufRef slot ptr sp0 : BitVec 64)
    (i : BitVec 32) (rest afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (hlen_lt : (pbVarint 1 i.toNat ++ rest ++ afterCk).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s0.pc = lsmpl.base 516 + 872#64) (hrun : s0.status = .Running)
    (halign : sp0 &&& 15#64 = 0#64) (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hregs : Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init s0)
    (hnext : ∀ (sm : State),
      sm.pc = lsmpl.base 516 + 872#64 → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ ((a + 96#64) ↦₃₂ i) ∗ (ptr ↦ₛ pbVarint 1 i.toNat) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbVarint 1 i.toNat).length) (rest ++ afterCk) ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s_init sf ∗ R))) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s0
      (((bufRef ↦₆₄ slot) ∗ ((a + 96#64) ↦₃₂ 0#32) ∗
        sliceCursorAt slot ptr (pbVarint 1 i.toNat ++ (rest ++ afterCk)) ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s_init sf ∗ R)) := by
  by_cases hi0 : i = 0#32
  · subst hi0
    have hpb0 : pbVarint 1 (0#32).toNat = [] := rfl
    have hlen0 : BitVec.ofNat 64 ([] : List (BitVec 8)).length = 0#64 := rfl
    rw [hpb0, List.nil_append]
    refine SepWPp.mono_pre_seedChain ?_ (hnext s0 hpc hrun hcl htr hvregs hregs)
    rw [hpb0, pointsToBytes_nil, hlen0, BitVec.add_zero]; simp only [emp_sepConj]
    exact sep_ac_seedChain (by ac_rfl)
  · have hi_pos : i.toNat ≠ 0 := by
      intro h; apply hi0; apply BitVec.eq_of_toNat_eq; simpa using h
    let rem1 : List (BitVec 8) := pbVarintBody 5 i.toNat ++ (rest ++ afterCk)
    have hcons_eq : pbVarint 1 i.toNat ++ (rest ++ afterCk) = 0x08#8 :: rem1 := by
      rw [c3ck_pbVarint1_eq i.toNat hi_pos]; simp [rem1, List.cons_append]
    have hlen_gt : afterCk.length < (0x08#8 :: rem1).length := by
      simp only [rem1, List.length_cons, List.length_append]; omega
    have hlen_cons_lt : (0x08#8 :: rem1).length < 2 ^ 62 := by
      rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
    rw [hcons_eq]
    refine SepWPp.focus_pre (step_c3ck_ihead_placed sp0 bufRef a slot ptr outerTailLen 0x08#8 rem1
      afterCk hlen_gt hlen_cons_lt hpc hrun hcl htr hvregs hregs ?_)
    intro s1 hpc1 hrun1 hcl1 htr1 hvregs1 hlr1 hx0_1 hregs1
    rw [show (0x08#8 :: rem1) = [0x08#8] ++ rem1 from rfl]
    refine SepWPp.focus_pre (c3_dv_call_cro hC bufRef slot ptr sp0 (lsmpl.base 516 + 896#64)
      0x08#64 [0x08#8] rem1 rfl hlen_cons_lt hpc1 hrun1 hregs1.1 halign hcl1 htr1 hlr1 hx0_1 ?_)
    intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hcs2 hx0_2 hx1_2
    obtain ⟨hregs2, hvregs2⟩ := c3ck_regs_after_call hregs1 hvregs1 hsp2 hcs2
    refine step_c3ck_key1_placed sp0 bufRef a outerTailLen afterCk.length
      hpc2 hrun2 hcl2 htr2 hvregs2 hregs2 hx0_2 hx1_2 ?_
    intro s3 hpc3 hrun3 hcl3 htr3 hvregs3 hlr3 hx0_3 hregs3
    have hrem1_lt : (pbVarintBody 5 i.toNat ++ (rest ++ afterCk)).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    have hdv2 : decodeVarint (pbVarintBody 5 i.toNat ++ (rest ++ afterCk)) =
        some (i.zeroExtend 64, rest ++ afterCk) := by
      rw [pbVarintBody_u32_eq_encodeVarint_seedChain i]
      exact decodeVarint_encodeVarint (i.zeroExtend 64) (rest ++ afterCk)
    rw [show BitVec.ofNat 64 ([0x08#8] : List (BitVec 8)).length = 1#64 from rfl]
    refine SepWPp.focus_pre (c3_dv_call_cro hC bufRef slot (ptr + 1#64) sp0
      (lsmpl.base 516 + 976#64) (i.zeroExtend 64) (pbVarintBody 5 i.toNat) (rest ++ afterCk)
      hdv2 hrem1_lt hpc3 hrun3 hregs3.1 halign hcl3 htr3 hlr3 hx0_3 ?_)
    intro s4 hpc4 hrun4 hsp4 hcl4 htr4 hcs4 hx0_4 hx1_4
    obtain ⟨hregs4, hvregs4⟩ := c3ck_regs_after_call hregs3 hvregs3 hsp4 hcs4
    refine SepWPp.focus_pre (step_c3ck_store_placed sp0 bufRef a outerTailLen afterCk.length
      (i.zeroExtend 64) 0#32 hpc4 hrun4 hcl4 htr4 hvregs4 hregs4 hx0_4 hx1_4 ?_)
    intro s5 hpc5 hrun5 hcl5 htr5 hvregs5 hregs5
    refine SepWPp.mono_pre_seedChain ?_ (hnext s5 hpc5 hrun5 hcl5 htr5 hvregs5 hregs5)
    rw [c3ck_zeroExtend64_setWidth32 i, c3ck_pbVarint1_ptr_advance ptr i.toNat hi_pos,
      ← c3ck_pointsTo_08_combine ptr i.toNat hi_pos]
    exact sep_ac_seedChain (by ac_rfl)

private theorem step_seg3c_cro [LibsignalPlacement] {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW ext)
    (a bufRef slot ptr sp0 : BitVec 64)
    (k afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (hk_lt : k.length < 128) (hlen_lt : (pbBytes 2 k ++ afterCk).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem)
    (hpc : s0.pc = lsmpl.base 516 + 872#64) (hrun : s0.status = .Running)
    (halign : sp0 &&& 15#64 = 0#64) (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hregs : Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init s0)
    (hnext : ∀ (sm : State),
      sm.pc = lsmpl.base 516 + 872#64 → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ vecU8 A0 (a + 72#64) k ∗ (ptr ↦ₛ pbBytes 2 k) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 2 k).length) afterCk ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s_init sf ∗ R))) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s0
      (((bufRef ↦₆₄ slot) ∗ chain3VecAt A0 (a + 72#64) [] ∗
        sliceCursorAt slot ptr (pbBytes 2 k ++ afterCk) ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s_init sf ∗ R)) := by
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 k.length] ++ k ++ afterCk
  have hcons_eq : pbBytes 2 k ++ afterCk = 0x12#8 :: rem1 := by
    rw [DeserializeGeneral.pbBytes_lt128_eq_seedChain 2 (by decide) k hk_lt]
    simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : afterCk.length < (0x12#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x12#8 :: rem1).length < 2 ^ 62 := by rw [← hcons_eq]; exact hlen_lt
  refine SepWPp.bind_lscro (mid := lsmpl.base 514)
    (Q1 := fun s3 P3 => LibsignalCodeLoaded lsmpl s3.mem ∧ s3.trace = s_init.trace ∧
      calleeSavedVRegs s3 = calleeSavedVRegs s_init ∧
      s3.readReg64 .lr = lsmpl.base 516 + 956#64 ∧ (s3.readReg64 .x0).setWidth 8 = 2#8 ∧
      s3.readReg64 .x1 = a + 72#64 ∧ s3.readReg64 .x2 = bufRef ∧
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init s3 ∧
      (P3 ⊢ (chain3VecAt A0 (a + 72#64) [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot (ptr + 1#64) rem1 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ ((ptr ↦ₛ [0x12#8]) ∗ F))) hcro ?_ ?_
  · rw [hcons_eq]
    refine SepWPp.focus_pre (step_c3ck_ihead_placed sp0 bufRef a slot ptr outerTailLen 0x12#8 rem1
      afterCk hlen_gt hlen_cons_lt hpc hrun hcl htr hvregs hregs ?_)
    intro s1 hpc1 hrun1 hcl1 htr1 hvregs1 hlr1 hx0_1 hregs1
    rw [show (0x12#8 :: rem1) = [0x12#8] ++ rem1 from rfl]
    refine SepWPp.focus_pre (c3_dv_call_cro hC bufRef slot ptr sp0 (lsmpl.base 516 + 896#64)
      0x12#64 [0x12#8] rem1 rfl hlen_cons_lt hpc1 hrun1 hregs1.1 halign hcl1 htr1 hlr1 hx0_1 ?_)
    intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hcs2 hx0_2 hx1_2
    obtain ⟨hregs2, hvregs2⟩ := c3ck_regs_after_call hregs1 hvregs1 hsp2 hcs2
    refine step_c3k3c_dispatch_placed sp0 bufRef a outerTailLen afterCk.length
      hpc2 hrun2 hcl2 htr2 hvregs2 hregs2 hx0_2 hx1_2 ?_
    intro s3 hpc3 hrun3 hcl3 htr3 hvregs3 hlr3 hx0_3 hx1_3 hx2_3 hregs3
    refine SepWPp.done hpc3 hrun3 ⟨hcl3, htr3, hvregs3, hlr3, hx0_3, hx1_3, hx2_3, hregs3, ?_⟩
    rw [show BitVec.ofNat 64 ([0x12#8] : List (BitVec 8)).length = 1#64 from rfl]
    exact sep_ac_seedChain (by ac_rfl)
  · intro s3 P3 hpc3 hrun3 hcro3 ⟨hcl3, htr3, hvregs3, hlr3, hx0_3, hx1_3, hx2_3, hregs3, hent3⟩
    refine SepWPp.mono_pre_seedChain hent3 ?_
    have hrem1_lt : ([BitVec.ofNat 8 k.length] ++ k ++ afterCk).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine c3_bm_call_vec_cro hC (a + 72#64) bufRef slot (ptr + 1#64) sp0 (lsmpl.base 516 + 956#64)
      k afterCk hk_lt hrem1_lt hcro3 hpc3 hrun3 hregs3.1 halign hcl3 htr3 hlr3 hx0_3 hx1_3 hx2_3 ?_
    intro s4 hpc4 hrun4 hsp4 hcl4 htr4 hcs4 hx0_4
    obtain ⟨hregs4, hvregs4⟩ := c3ck_regs_after_call hregs3 hvregs3 hsp4 hcs4
    refine step_c3k3c_ret_placed sp0 bufRef a outerTailLen afterCk.length
      hpc4 hrun4 hcl4 htr4 hvregs4 hregs4 hx0_4 ?_
    intro s5 hpc5 hrun5 hcl5 htr5 hvregs5 hregs5
    refine SepWPp.mono_pre_seedChain ?_ (hnext s5 hpc5 hrun5 hcl5 htr5 hvregs5 hregs5)
    rw [DeserializeGeneral.pbBytes_ptr_advance_seedChain 2 (by decide) ptr k hk_lt,
      ← c3k3c_pointsTo_12_combine ptr k hk_lt]
    exact sep_ac_seedChain (by ac_rfl)

theorem chain3ChainKey_cro_placed_ok [LibsignalPlacement] (ext : LibsignalHooks) :
    Chain3ChainKeyCroStmt ext := by
  intro hC x R s0 k s hk htag ⟨hcro, hs⟩
  refine segStepG_keep_cro hcro ?_
  rcases hs with ⟨hpc, hrun, htr, hvregs, hcl, hsp, hal, hx29, hx19, hx20, hx21,
    hx22, hx23, hx24, hx26, hx27, hx28, hcOk, hlen_lt, hmem⟩
  intro hL
  have hsp_sub_align : (s0.sp - 240#64) &&& 15#64 = 0#64 := by
    have : s.sp &&& 15#64 = 0#64 := by simpa [State.spAligned, beq_iff_eq] using hal
    simpa [hsp] using this
  have hsp0_align : s0.sp &&& 15#64 = 0#64 := sp0_aligned_of_sub_240_aligned hsp_sub_align
  obtain ⟨⟨i, key, hck_some, hfl_eq⟩, hck_none⟩ := chainField_tag_three_info x.c k hk htag
  have hkey_len : key.length = 32 := hcOk.2.2.1 (i, key) hck_some
  have hkey_lt : key.length < 128 := by omega
  have hck_bounds := ckEnc_length_bounds_seedChain i hkey_len
  let b3b : List (BitVec 8) := pbVarint 1 i.toNat
  let b3c : List (BitVec 8) := pbBytes 2 key
  let ck_body : List (BitVec 8) := b3b ++ b3c
  have hck_lt : ck_body.length < 128 := by dsimp [ck_body, b3b, b3c]; omega
  let b3a : List (BitVec 8) := [0x1a#8, BitVec.ofNat 8 ck_body.length]
  let pfx : List (BitVec 8) := pfx_k x.c k
  let afterCk : List (BitVec 8) := rem_k x.c (k + 1) x.tail
  have hfl_enc : (x.c.fields[k]'hk).enc = b3a ++ (b3b ++ b3c) := by
    rw [hfl_eq]; exact chainField_ck_enc_eq i hkey_len
  have hrem_k : rem_k x.c k x.tail = 0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk) := by
    rw [rem_k_eq_cons x.c k x.tail hk, hfl_enc]; dsimp [b3a, ck_body]
  have hpay_eq : x.c.payload ++ x.tail = pfx ++ rem_k x.c k x.tail :=
    payload_append_eq_pfx_rem x.c k x.tail
  have houter_le : x.tail.length ≤ afterCk.length := by
    dsimp [afterCk, rem_k]; simp only [List.length_append]; omega
  have hlen_lt3a : 2 + (ck_body.length + afterCk.length) < 2 ^ 62 := by
    have h1 := hlen_lt; rw [hpay_eq, hrem_k] at h1
    simp only [List.length_append, List.length_cons] at h1; omega
  have hlen_lt3b : (b3b ++ b3c ++ afterCk).length < 2 ^ 62 := by
    have h1 : (b3b ++ b3c ++ afterCk).length = ck_body.length + afterCk.length := List.length_append
    omega
  have hlen_lt3c : (b3c ++ afterCk).length < 2 ^ 62 := by
    simp only [List.length_append] at hlen_lt3b ⊢; omega
  let c0 : ChainG := chainGAfter x.c k
  let ptr3a : BitVec 64 := x.ptr + BitVec.ofNat 64 pfx.length
  let ptr3b : BitVec 64 := ptr3a + 2#64
  let ptr3c : BitVec 64 := ptr3b + BitVec.ofNat 64 b3b.length
  let ptrEnd : BitVec 64 := ptr3c + BitVec.ofNat 64 b3c.length
  have hcur_init :
      sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
        (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) =
      (x.ptr ↦ₛ pfx) ∗
        sliceCursorAt x.slot ptr3a (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) := by
    change sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) (rem_k x.c k x.tail) = _
    rw [hpay_eq, sliceCursorAfter_append_eq_seedChain x.slot x.ptr pfx (rem_k x.c k x.tail), hrem_k]
  have hmem_init : s.mem ⊨
      (((x.bufRef ↦₆₄ x.slot) ∗ ((x.a + 72#64) ↦₆₄ noneCap) ∗ memRegion (x.a + 80#64) 24 ∗
        sliceCursorAt x.slot ptr3a (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
        (chain3VecAt A0 x.a c0.srk ∗ chain3VecAt A0 (x.a + 24#64) c0.priv ∗
          vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (x.a + 48#64) c0.keys ∗
          (x.ptr ↦ₛ pfx) ∗ chain3SavedRegs s0.sp s0)) ∗ R := by
    change s.mem ⊨ chain3GAt A0 x.a c0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
        (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) ∗
      stackAt (s0.sp - 240#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0 ∗ R at hmem
    rw [chain3GAt_ck_none_eq x.a c0 hck_none, hcur_init] at hmem
    exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
  have hfull : SepWPp (lsProg_516 (Rust.withPanics ext)) (chain3PCPlacedAtW ext 168#64) s
      (((x.bufRef ↦₆₄ x.slot) ∗ ((x.a + 72#64) ↦₆₄ noneCap) ∗ memRegion (x.a + 80#64) 24 ∗
        sliceCursorAt x.slot ptr3a (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
        (chain3VecAt A0 x.a c0.srk ∗ chain3VecAt A0 (x.a + 24#64) c0.priv ∗
          vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (x.a + 48#64) c0.keys ∗
          (x.ptr ↦ₛ pfx) ∗ chain3SavedRegs s0.sp s0))
      (fun sf Pf => LibsignalCodeLoaded lsmpl sf.mem ∧ sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        Chain3InnerLoopRegs s0.sp x.bufRef x.a x.tail.length afterCk.length s0 sf ∧
        (Pf ⊢ chain3GAt A0 x.a (chainGAfter x.c (k + 1)) ∗ (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
            (((x.c.fields.drop (k + 1)).flatMap ChainField.enc) ++ x.tail) ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0))
      (fun sf Pf => (sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R)) := by
    refine SepWPp.bind_lscro (mid := lsmpl.base 516 + 872#64)
      (Q1 := fun s5 P5 => LibsignalCodeLoaded lsmpl s5.mem ∧ s5.trace = s0.trace ∧
        calleeSavedVRegs s5 = calleeSavedVRegs s0 ∧
        Chain3InnerLoopRegs s0.sp x.bufRef x.a x.tail.length afterCk.length s0 s5 ∧
        (P5 ⊢ (((x.bufRef ↦₆₄ x.slot) ∗ chain3VecAt A0 (x.a + 72#64) [] ∗
          sliceCursorAt x.slot ptr3c (b3c ++ afterCk) ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
          ((ptr3a ↦ₛ b3a) ∗ (ptr3b ↦ₛ b3b) ∗ ((x.a + 96#64) ↦₃₂ i) ∗ memRegion (x.a + 100#64) 4 ∗
            chain3VecAt A0 x.a c0.srk ∗ chain3VecAt A0 (x.a + 24#64) c0.priv ∗
            vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (x.a + 48#64) c0.keys ∗
            (x.ptr ↦ₛ pfx) ∗ chain3SavedRegs s0.sp s0)))) hcro ?_ ?_
    · refine step_seg3a_cro hC x.a x.bufRef x.slot ptr3a s0.sp ck_body afterCk x.tail.length
        hck_lt houter_le hlen_lt3a hpc hrun hsp hsp0_align hcl htr hvregs
        hx29 hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27 hx28 ?_
      intro s4 hpc4 hrun4 hcl4 htr4 hvregs4 hregs4
      refine SepWPp.mono_pre_seedChain
        (P' := (((x.bufRef ↦₆₄ x.slot) ∗ ((x.a + 96#64) ↦₃₂ 0#32) ∗
          sliceCursorAt x.slot ptr3b (b3b ++ (b3c ++ afterCk)) ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
          ((ptr3a ↦ₛ b3a) ∗ chain3VecAt A0 (x.a + 72#64) [] ∗ memRegion (x.a + 100#64) 4 ∗
            chain3VecAt A0 x.a c0.srk ∗ chain3VecAt A0 (x.a + 24#64) c0.priv ∗
            vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (x.a + 48#64) c0.keys ∗
            (x.ptr ↦ₛ pfx) ∗ chain3SavedRegs s0.sp s0)))
        (by
          have hck_eq : ck_body ++ afterCk = b3b ++ (b3c ++ afterCk) := by
            simp [ck_body, b3b, b3c, List.append_assoc]
          dsimp only [ptr3b, b3a]; rw [hck_eq]; exact sep_ac_seedChain (by ac_rfl)) ?_
      refine step_seg3b_cro hC x.a x.bufRef x.slot ptr3b s0.sp i b3c afterCk x.tail.length
        hlen_lt3b hpc4 hrun4 hsp0_align hcl4 htr4 hvregs4 hregs4 ?_
      intro s5 hpc5 hrun5 hcl5 htr5 hvregs5 hregs5
      refine SepWPp.done hpc5 hrun5 ⟨hcl5, htr5, hvregs5, hregs5, ?_⟩
      dsimp only [ptr3c, b3b]; exact sep_ac_seedChain (by ac_rfl)
    · intro s5 P5 hpc5 hrun5 hcro5 ⟨hcl5, htr5, hvregs5, hregs5, hent5⟩
      refine SepWPp.mono_pre_seedChain hent5 ?_
      refine step_seg3c_cro hC x.a x.bufRef x.slot ptr3c s0.sp key afterCk x.tail.length
        hkey_lt hlen_lt3c hcro5 hpc5 hrun5 hsp0_align hcl5 htr5 hvregs5 hregs5 ?_
      intro s6 hpc6 hrun6 hcl6 htr6 hvregs6 hregs6
      refine SepWPp.mono_pre_seedChain
        (P' := (((x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot ptrEnd afterCk ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
          ((ptr3a ↦ₛ b3a) ∗ (ptr3b ↦ₛ b3b) ∗ (ptr3c ↦ₛ b3c) ∗ vecU8 A0 (x.a + 72#64) key ∗
            ((x.a + 96#64) ↦₃₂ i) ∗ memRegion (x.a + 100#64) 4 ∗ chain3VecAt A0 x.a c0.srk ∗
            chain3VecAt A0 (x.a + 24#64) c0.priv ∗
            vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (x.a + 48#64) c0.keys ∗
            (x.ptr ↦ₛ pfx) ∗ chain3SavedRegs s0.sp s0)))
        (by dsimp only [ptrEnd, b3c]; exact sep_ac_seedChain (by ac_rfl)) ?_
      refine step_chain3_seg3d_placed ext x.a x.bufRef x.slot ptrEnd s0.sp afterCk x.tail.length
        hpc6 hrun6 hcl6 htr6 hvregs6 hregs6 ?_
      intro sf hpcf hrunf hclf htrf hvregsf hregsf
      refine SepWPp.done hpcf hrunf ⟨hclf, htrf, hvregsf, hregsf, ?_⟩
      have hc_succ : chainGAfter x.c (k + 1) = c0.apply (ChainField.ck i key) := by
        rw [chainGAfter_succ x.c k hk, hfl_eq]
      rw [hc_succ, chain3GAt_apply_ck_eq x.a c0 i key]
      have hcur_end := combine_tag3_cursor x.slot x.ptr pfx b3a b3b b3c afterCk rfl
      dsimp only at hcur_end
      have htotal_end : (pfx ++ (b3a ++ (b3b ++ b3c))) ++ afterCk = x.c.payload ++ x.tail := by
        rw [← hfl_enc, ← pfx_k_succ x.c k hk]
        exact (payload_append_eq_pfx_rem x.c (k + 1) x.tail).symm
      rw [htotal_end] at hcur_end
      change _ ⊢ (chain3VecAt A0 x.a c0.srk ∗ chain3VecAt A0 (x.a + 24#64) c0.priv ∗
          vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (x.a + 48#64) c0.keys ∗
          vecU8 A0 (x.a + 72#64) key ∗ ((x.a + 96#64) ↦₃₂ i) ∗ memRegion (x.a + 100#64) 4) ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) afterCk ∗
        stackAt (s0.sp - 240#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0
      rw [← hcur_end]; dsimp only [ptr3a, ptr3b, ptr3c, ptrEnd]; exact sep_ac_seedChain (by ac_rfl)
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem_init hL
  rcases hex with ⟨hpcf, hrunf, Pf, hmf, hclf, htrf, hvregsf, hregsf, hentf⟩ | ⟨hpan, Pf, hmf, htrf⟩ | ⟨_, hoom⟩
  · rcases hregsf with ⟨hspf, hx29f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, _, hx26f, hx27f, hx28f⟩
    have half : sf.spAligned = true := by rw [State.spAligned, hspf, ← hsp]; exact hal
    have hmemf := Satisfies.mono (sepConj_mono_left hentf) hmf
    simp only [sepConj_assoc] at hmemf
    exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, htrf, hvregsf, hclf, hspf, half, hx29f, hx19f, hx20f,
      hx21f, hx22f, hx23f, hx24f, hx26f, hx27f, hx28f, hcOk, hlen_lt, hmemf⟩⟩
  · exact ⟨sf, hsteps, Or.inr ⟨hpan, htrf hmf⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

end ChainKeySlice

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
