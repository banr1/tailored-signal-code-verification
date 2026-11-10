/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroBPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPush
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPushAPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.ChainKeyEpilogue
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Steps
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.ChainMessageKeysGExt
import ProofLib.SepLogic.WPp

/-!
# `VerNe.Chain3` (Block `516`) Part C (`MessageKeys` and Top-Level Closure)

Completes the `MessageKeys` (`tag = 4`) slice of `message::merge<Chain> [local#4]` (Block `516`)
under `StoreKit.withLsCodeRoLoaded` and derives `chainMerge5_cro_of_block_hooks` on arbitrary
caller blocks from standard `HookSat` hypotheses.
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

/-! ## `MessageKeys` Slice (`tag = 4`) under `LibsignalCodeRoLoaded` -/

private theorem c3_bm_call_vec1_cro [LibsignalPlacement] {ext : LibsignalHooks}
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
      ((vecU8At A0 v 0#64 1#64 [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R)) := by
  refine c3_bm_call_cro hC v 1#64 bufRef slot curPtr sp0 ret_pc b rest hb hlen_lt
    hcro hpc hrun hsp halign hcl htr hlr hx0 hx1 hx2 ?_
  intro sm cap' ptr' hpcm hrunm hspm hclm htrm hcsm hx0m
  refine SepWPp.mono_pre_seedChain ?_ (hnext sm hpcm hrunm hspm hclm htrm hcsm hx0m)
  exact sepConj_mono_left (sepConj_mono_left
    (Entails.sepExists_right cap' (Entails.sepExists_right ptr' (Entails.refl _))))

private theorem step_mkHead_cro [LibsignalPlacement] {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW ext)
    (bufRef slot ptr sp0 : BitVec 64) (body rest tail : List (BitVec 8))
    {x : ChainMergeGenGhost} {R : SepProp} {s0 s : State} {F : SepProp}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hbody : body.length < 128) (htail : tail.length ≤ rest.length)
    (hlen_lt : 2 + (body.length + rest.length) < 2 ^ 62)
    (hpc : s.pc = chain3PCPlacedAtW ext 168#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = bufRef) (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 tail.length)
    (hx22 : s.readReg64 .x22 = sp0 - 232#64) (hx23 : s.readReg64 .x23 = 1#64)
    (hnext : ∀ (sm : State),
      sm.pc = chain3PCPlacedAtW ext 580#64 → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace →
      sm.readReg64 .x25 = BitVec.ofNat 64 rest.length → Chain3MkRegs s sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 (sp0 - 232#64) [] ∗ vecU8 A0 (sp0 - 208#64) [] ∗ vecU8 A0 (sp0 - 184#64) [] ∗
          vecU8At A0 (sp0 - 160#64) 0#64 1#64 [] ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
          memRegion (sp0 - 132#64) 4 ∗
          (ptr ↦ₛ [0x22#8, BitVec.ofNat 8 body.length]) ∗
          sliceCursorAt slot (ptr + 2#64) (body ++ rest) ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ memRegion (sp0 - 232#64) 104 ∗
        sliceCursorAt slot ptr (0x22#8 :: BitVec.ofNat 8 body.length :: (body ++ rest)) ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R)) := by
  let rem1 : List (BitVec 8) := BitVec.ofNat 8 body.length :: (body ++ rest)
  have hlen_gt : tail.length < (0x22#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x22#8 :: rem1).length < 2 ^ 62 := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_rem1_lt : ([BitVec.ofNat 8 body.length] ++ (body ++ rest)).length < 2 ^ 62 := by
    simp only [List.singleton_append, List.length_cons, List.length_append]; omega
  have hlen_body_rest_lt : (body ++ rest).length < 2 ^ 62 := by
    simp only [List.length_append]; omega
  have hdv_L : decodeVarint ([BitVec.ofNat 8 body.length] ++ (body ++ rest)) =
      some (BitVec.ofNat 64 body.length, body ++ rest) := by
    rw [← encodeVarint_lt128_seedChain body.length hbody]
    exact decodeVarint_encodeVarint (BitVec.ofNat 64 body.length) (body ++ rest)
  dsimp only [chain3PCPlacedAtW] at hpc hnext
  refine SepWPp.mono_pre_seedChain
    (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (0x22#8 :: rem1)) ∗
      (memRegion (sp0 - 232#64) 104 ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX ∗ F))
    (sep_ac_seedChain (by ac_rfl)) ?_
  refine step_c3hd_head_placed bufRef slot ptr 0x22#8 rem1 tail hlen_gt hlen_cons_lt
    hpc hrun hcl hx19 hx21 ?_
  intro s1 hpc1 hrun1 hsp1 hcl1 htr1 hlr1 hx0_1 hregs1
  refine SepWPp.mono_pre_seedChain
    (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr ([0x22#8] ++ rem1) ∗
      stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ (memRegion (sp0 - 232#64) 104 ∗ F))
    (sep_ac_seedChain (by ac_rfl)) ?_
  refine c3_dv_call_cro hC bufRef slot ptr sp0 (lsmpl.base 516 + 192#64) 0x22#64 [0x22#8] rem1
    rfl hlen_cons_lt hpc1 hrun1 (hsp1.trans hsp) halign hcl1 (htr1.trans htr) hlr1 hx0_1 ?_
  intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hcs2 hx0_2 hx1_2
  have hregs2 : Chain3MkRegs s s2 := hregs1.trans (.of_calleeSaved hcs2)
  refine SepWPp.mono_pre_seedChain
    (P' := memRegion (sp0 - 232#64) 104 ∗ ((bufRef ↦₆₄ slot) ∗ (ptr ↦ₛ [0x22#8]) ∗
      sliceCursorAt slot (ptr + 1#64) rem1 ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX ∗ F))
    (sep_ac_seedChain (by ac_rfl)) ?_
  refine step_c3hd_key4_placed bufRef sp0 hpc2 hrun2 hsp2 halign hcl2 hx0_2 hx1_2
    (hregs2.1.trans hx19) (hregs2.2.2.2.1.trans hx22) (hregs2.2.2.2.2.1.trans hx23) ?_
  intro s3 hpc3 hrun3 hsp3 hcl3 htr3 hlr3 hx0_3 hregs23
  have hregs3 : Chain3MkRegs s s3 := hregs2.trans hregs23
  refine SepWPp.mono_pre_seedChain
    (P' := ((bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot (ptr + 1#64) ([BitVec.ofNat 8 body.length] ++ (body ++ rest)) ∗
      stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
      (vecU8 A0 (sp0 - 232#64) [] ∗ vecU8 A0 (sp0 - 208#64) [] ∗ vecU8 A0 (sp0 - 184#64) [] ∗
        vecU8At A0 (sp0 - 160#64) 0#64 1#64 [] ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
        memRegion (sp0 - 132#64) 4 ∗ (ptr ↦ₛ [0x22#8]) ∗ F))
    (sep_ac_seedChain (by ac_rfl)) ?_
  refine c3_dv_call_cro hC bufRef slot (ptr + 1#64) sp0 (lsmpl.base 516 + 344#64)
    (BitVec.ofNat 64 body.length) [BitVec.ofNat 8 body.length] (body ++ rest)
    hdv_L hlen_rem1_lt hpc3 hrun3 hsp3 halign hcl3 (htr3.trans htr2) hlr3 hx0_3 ?_
  intro s4 hpc4 hrun4 hsp4 hcl4 htr4 hcs4 hx0_4 hx1_4
  have hregs4 : Chain3MkRegs s s4 := hregs3.trans (.of_calleeSaved hcs4)
  refine SepWPp.mono_pre_seedChain
    (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot (ptr + 2#64) (body ++ rest)) ∗
      (vecU8 A0 (sp0 - 232#64) [] ∗ vecU8 A0 (sp0 - 208#64) [] ∗ vecU8 A0 (sp0 - 184#64) [] ∗
        vecU8At A0 (sp0 - 160#64) 0#64 1#64 [] ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
        memRegion (sp0 - 132#64) 4 ∗ (ptr ↦ₛ [0x22#8]) ∗
        ((ptr + 1#64) ↦ₛ [BitVec.ofNat 8 body.length]) ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX ∗ F))
    (by dsimp only [List.length]; rw [c3hd_ptr_add_one_add_one ptr]; exact sep_ac_seedChain (by ac_rfl)) ?_
  refine step_c3hd_len_placed bufRef slot (ptr + 2#64) body rest hlen_body_rest_lt
    hpc4 hrun4 hcl4 hx0_4 hx1_4 (hregs4.1.trans hx19) ?_
  intro s5 hpc5 hrun5 hsp5 hcl5 htr5 hx25_5 hregs45
  refine SepWPp.mono_pre_seedChain ?_
    (hnext s5 hpc5 hrun5 (hsp5.trans hsp4) hcl5 (htr5.trans htr4) hx25_5 (hregs4.trans hregs45))
  rw [← c3hd_pointsTo_hdr_combine ptr (BitVec.ofNat 8 body.length)]
  exact sep_ac_seedChain (by ac_rfl)

private theorem step_mkCnt_cro [LibsignalPlacement] {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW ext)
    (bufRef slot ptr sp0 : BitVec 64) (i : BitVec 32) (rest_mk rest : List (BitVec 8))
    {x : ChainMergeGenGhost} {R : SepProp} {s0 s : State} {F : SepProp}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hlen_lt : (pbVarint 1 i.toNat ++ (rest_mk ++ rest)).length < 2 ^ 62)
    (hpc : s.pc = chain3PCPlacedAtW ext 580#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = bufRef) (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 rest.length)
    (hnext : ∀ (sm : State),
      sm.pc = chain3PCPlacedAtW ext 580#64 → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace →
      sm.readReg64 .x25 = BitVec.ofNat 64 rest.length → Chain3MkRegs s sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ ((sp0 - 136#64) ↦₃₂ i) ∗ (ptr ↦ₛ pbVarint 1 i.toNat) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbVarint 1 i.toNat).length) (rest_mk ++ rest) ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
        sliceCursorAt slot ptr (pbVarint 1 i.toNat ++ (rest_mk ++ rest)) ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R)) := by
  by_cases hi0 : i = 0#32
  · subst hi0
    have hpb0 : pbVarint 1 (0#32).toNat = [] := rfl
    have hlen0 : BitVec.ofNat 64 ([] : List (BitVec 8)).length = 0#64 := rfl
    rw [hpb0, List.nil_append]
    refine SepWPp.mono_pre_seedChain ?_ (hnext s hpc hrun hsp hcl htr hx25 (.refl s))
    rw [hpb0, pointsToBytes_nil, hlen0, BitVec.add_zero]; simp only [emp_sepConj]
    exact sep_ac_seedChain (by ac_rfl)
  · have hi_pos : i.toNat ≠ 0 := by
      intro h; apply hi0; apply BitVec.eq_of_toNat_eq; simpa using h
    have hpb : pbVarint 1 i.toNat = 0x08#8 :: pbVarintBody 5 i.toNat := by
      unfold pbVarint; simp [hi_pos]; rfl
    let rem1 : List (BitVec 8) := pbVarintBody 5 i.toNat ++ (rest_mk ++ rest)
    have hcons_eq : pbVarint 1 i.toNat ++ (rest_mk ++ rest) = 0x08#8 :: rem1 := by
      rw [hpb]; simp [rem1, List.cons_append]
    have hlen_gt : rest.length < (0x08#8 :: rem1).length := by
      simp only [rem1, List.length_cons, List.length_append]; omega
    have hlen_cons_lt : (0x08#8 :: rem1).length < 2 ^ 62 := by rw [← hcons_eq]; exact hlen_lt
    rw [hcons_eq]
    refine SepWPp.focus_pre (step_c3cnt_ihead_placed bufRef slot ptr 0x08#8 rem1 rest
      hlen_gt hlen_cons_lt hpc hrun hcl hx19 hx25 ?_)
    intro s1 hpc1 hrun1 hsp1 hcl1 htr1 hlr1 hx0_1 hx25_1 hregs1
    rw [show (0x08#8 :: rem1) = [0x08#8] ++ rem1 from rfl]
    refine SepWPp.focus_pre (c3_dv_call_cro hC bufRef slot ptr sp0 (lsmpl.base 516 + 604#64)
      0x08#64 [0x08#8] rem1 rfl hlen_cons_lt hpc1 hrun1 (hsp1.trans hsp) halign hcl1
      (htr1.trans htr) hlr1 hx0_1 ?_)
    intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hcs2 hx0_2 hx1_2
    have hregs2 : Chain3MkRegs s s2 := hregs1.trans (.of_calleeSaved hcs2)
    have hx25_2 : s2.readReg64 .x25 = BitVec.ofNat 64 rest.length :=
      hcs2.2.2.2.2.2.2.1.trans hx25_1
    refine step_c3cnt_key_placed bufRef hpc2 hrun2 hcl2 hx0_2 hx1_2 (hregs2.1.trans hx19) ?_
    intro s3 hpc3 hrun3 hsp3 hcl3 htr3 hlr3 hx0_3 hx25_3 hregs3
    have hregs3' : Chain3MkRegs s s3 := hregs2.trans hregs3
    have hx25_3' : s3.readReg64 .x25 = BitVec.ofNat 64 rest.length := hx25_3.trans hx25_2
    have hrem1_lt : (pbVarintBody 5 i.toNat ++ (rest_mk ++ rest)).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    have hdv2 : decodeVarint (pbVarintBody 5 i.toNat ++ (rest_mk ++ rest)) =
        some (i.zeroExtend 64, rest_mk ++ rest) := by
      rw [pbVarintBody_u32_eq_encodeVarint_seedChain i]
      exact decodeVarint_encodeVarint (i.zeroExtend 64) (rest_mk ++ rest)
    rw [show BitVec.ofNat 64 ([0x08#8] : List (BitVec 8)).length = 1#64 from rfl]
    refine SepWPp.focus_pre (c3_dv_call_cro hC bufRef slot (ptr + 1#64) sp0
      (lsmpl.base 516 + 776#64) (i.zeroExtend 64) (pbVarintBody 5 i.toNat) (rest_mk ++ rest)
      hdv2 hrem1_lt hpc3 hrun3 (hsp3.trans hsp2) halign hcl3 (htr3.trans htr2) hlr3 hx0_3 ?_)
    intro s4 hpc4 hrun4 hsp4 hcl4 htr4 hcs4 hx0_4 hx1_4
    have hregs4 : Chain3MkRegs s s4 := hregs3'.trans (.of_calleeSaved hcs4)
    have hx25_4 : s4.readReg64 .x25 = BitVec.ofNat 64 rest.length :=
      hcs4.2.2.2.2.2.2.1.trans hx25_3'
    refine SepWPp.focus_pre (step_c3cnt_store_placed sp0 (i.zeroExtend 64) 0#32
      hpc4 hrun4 hsp4 halign hcl4 hx0_4 hx1_4 ?_)
    intro s5 hpc5 hrun5 hsp5 hcl5 htr5 hx25_5 hregs5
    refine SepWPp.mono_pre_seedChain ?_
      (hnext s5 hpc5 hrun5 (hsp5.trans hsp4) hcl5 (htr5.trans htr4)
        (hx25_5.trans hx25_4) (hregs4.trans hregs5))
    rw [c3cnt_zeroExtend64_setWidth32 i, pbVarint1_ptr_advance_seedChain ptr i.toNat hi_pos,
      ← c3cnt_pointsTo_08_combine ptr i.toNat hi_pos]
    exact sep_ac_seedChain (by ac_rfl)

private theorem step_mkSeed_cro [LibsignalPlacement] {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW ext)
    (bufRef slot ptr sp0 : BitVec 64) (seed rest : List (BitVec 8))
    {x : ChainMergeGenGhost} {R : SepProp} {s0 s : State} {F : SepProp}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hseed_lt : seed.length < 128) (hlen_lt : (pbBytes 5 seed ++ rest).length < 2 ^ 62)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = chain3PCPlacedAtW ext 580#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = bufRef) (hx22 : s.readReg64 .x22 = sp0 - 232#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 rest.length)
    (hnext : ∀ (sm : State),
      sm.pc = chain3PCPlacedAtW ext 580#64 → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace →
      sm.readReg64 .x25 = BitVec.ofNat 64 rest.length → Chain3MkRegs s sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ vecU8 A0 (sp0 - 160#64) seed ∗ (ptr ↦ₛ pbBytes 5 seed) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 5 seed).length) rest ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ vecU8At A0 (sp0 - 160#64) 0#64 1#64 [] ∗
        sliceCursorAt slot ptr (pbBytes 5 seed ++ rest) ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R)) := by
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 seed.length] ++ seed ++ rest
  have hcons_eq : pbBytes 5 seed ++ rest = 0x2a#8 :: rem1 := by
    rw [CryptoVerification.E2E.Record.DeserializeSeed.pbBytes_lt128_eq_seedChain 5 (by decide) seed hseed_lt]
    simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : rest.length < (0x2a#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x2a#8 :: rem1).length < 2 ^ 62 := by rw [← hcons_eq]; exact hlen_lt
  refine SepWPp.bind_lscro (mid := lsmpl.base 514)
    (Q1 := fun s3 P3 => s3.sp = sp0 - 240#64 ∧ LibsignalCodeLoaded lsmpl s3.mem ∧
      s3.trace = s0.trace ∧ s3.readReg64 .lr = lsmpl.base 516 + 680#64 ∧
      (s3.readReg64 .x0).setWidth 8 = 2#8 ∧ s3.readReg64 .x1 = sp0 - 160#64 ∧
      s3.readReg64 .x2 = bufRef ∧ s3.readReg64 .x25 = BitVec.ofNat 64 rest.length ∧
      Chain3MkRegs s s3 ∧
      (P3 ⊢ (vecU8At A0 (sp0 - 160#64) 0#64 1#64 [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot (ptr + 1#64) rem1 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ ((ptr ↦ₛ [0x2a#8]) ∗ F))) hcro ?_ ?_
  · rw [hcons_eq]
    refine SepWPp.focus_pre (step_c3seed_ihead_placed bufRef slot ptr 0x2a#8 rem1 rest
      hlen_gt hlen_cons_lt hpc hrun hcl hx19 hx25 ?_)
    intro s1 hpc1 hrun1 hsp1 hcl1 htr1 hlr1 hx0_1 hx25_1 hregs1
    rw [show (0x2a#8 :: rem1) = [0x2a#8] ++ rem1 from rfl]
    refine SepWPp.focus_pre (c3_dv_call_cro hC bufRef slot ptr sp0 (lsmpl.base 516 + 604#64)
      0x2a#64 [0x2a#8] rem1 rfl hlen_cons_lt hpc1 hrun1 (hsp1.trans hsp) halign hcl1
      (htr1.trans htr) hlr1 hx0_1 ?_)
    intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hcs2 hx0_2 hx1_2
    have hregs2 : Chain3MkRegs s s2 := hregs1.trans (.of_calleeSaved hcs2)
    have hx25_2 : s2.readReg64 .x25 = BitVec.ofNat 64 rest.length :=
      hcs2.2.2.2.2.2.2.1.trans hx25_1
    refine step_c3seed_key_placed bufRef sp0 hpc2 hrun2 hcl2 hx0_2 hx1_2
      (hregs2.1.trans hx19) (hregs2.2.2.2.1.trans hx22) ?_
    intro s3 hpc3 hrun3 hsp3 hcl3 htr3 hlr3 hx0_3 hx1_3 hx2_3 hx25_3 hregs3
    refine SepWPp.done hpc3 hrun3 ⟨hsp3.trans hsp2, hcl3, htr3.trans htr2, hlr3,
      hx0_3, hx1_3, hx2_3, hx25_3.trans hx25_2, hregs2.trans hregs3, ?_⟩
    rw [show BitVec.ofNat 64 ([0x2a#8] : List (BitVec 8)).length = 1#64 from rfl]
    exact sep_ac_seedChain (by ac_rfl)
  · intro s3 P3 hpc3 hrun3 hcro3 ⟨hsp3, hcl3, htr3, hlr3, hx0_3, hx1_3, hx2_3, hx25_3, hregs3, hent3⟩
    refine SepWPp.mono_pre_seedChain hent3 ?_
    have hrem1_lt : ([BitVec.ofNat 8 seed.length] ++ seed ++ rest).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine c3_bm_call_vec1_cro hC (sp0 - 160#64) bufRef slot (ptr + 1#64) sp0
      (lsmpl.base 516 + 680#64) seed rest hseed_lt hrem1_lt hcro3 hpc3 hrun3 hsp3 halign hcl3
      htr3 hlr3 hx0_3 hx1_3 hx2_3 ?_
    intro s4 hpc4 hrun4 hsp4 hcl4 htr4 hcs4 hx0_4
    have hregs4 : Chain3MkRegs s s4 := hregs3.trans (.of_calleeSaved hcs4)
    have hx25_4 : s4.readReg64 .x25 = BitVec.ofNat 64 rest.length :=
      hcs4.2.2.2.2.2.2.1.trans hx25_3
    refine step_c3seed_icont_placed hpc4 hrun4 hcl4 hx0_4 ?_
    intro s5 hpc5 hrun5 hsp5 hcl5 htr5 hx25_5 hregs5
    refine SepWPp.mono_pre_seedChain ?_
      (hnext s5 hpc5 hrun5 (hsp5.trans hsp4) hcl5 (htr5.trans htr4)
        (hx25_5.trans hx25_4) (hregs4.trans hregs5))
    rw [CryptoVerification.E2E.Record.DeserializeSeed.pbBytes_ptr_advance_seedChain
        5 (by decide) ptr seed hseed_lt, ← c3seed_pointsTo_2a_combine ptr seed hseed_lt]
    exact sep_ac_seedChain (by ac_rfl)

private theorem call_frame_lscl_keys_cro [LibsignalPlacement] {α : Type}
    {prog : Program} {entry ret_pc ret : BitVec 64}
    {spec : Spec α} {x : α} {φ : Prop} {P T F : SepProp} {s : State}
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsCl lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call_lscl_c3 (F := F) x hcall hpc hrun hsp hcl hlr ?_ ?_ ?_ ?_ hoom
  · intro R' hm; refine intro_withLsCl_c3 hcl ?_
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]; exact ⟨hφ, hm⟩
  · intro sf code R' hex hm; dsimp only [withLsCl] at hm; exact hexit sf code R' hex hm
  · intro sf hpan; dsimp only [withLsCl]; exact hpanic sf hpan
  · intro sm hpcm hrunm hspm hclm hcsm; dsimp only [withLsCl]; rw [sepConj_assoc]
    refine SepWPp.pure_elim fun _ => hnext sm hpcm hrunm hspm hcsm hclm

private theorem step_c3mk_push4d_cro [LibsignalPlacement] {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW ext)
    (a bufRef slot ptr_rest sp0 : BitVec 64) (keys : List MessageKeyGenerator) (rest : List (BitVec 8))
    (hbound : keys.length ≤ maxMessageKeys)
    {x : ChainMergeGenGhost} {R : SepProp} {ret : BitVec 64} {s0 s : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 580#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp0 - 240#64) (hsp_align : s.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = bufRef) (hx20 : s.readReg64 .x20 = a)
    (hx24 : s.readReg64 .x24 = 104#64) (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 rest.length)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      keys.length + 1 ≤ cap'.toNat → cap'.toNat * 104 < 2 ^ 63 → ptr' ≠ 0#64 →
      sm.pc = lsmpl.base 516 + 376#64 →
      sm.status = .Running → sm.sp = sp0 - 240#64 → sm.spAligned = true →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace → Chain3MkRegs s sm →
      sm.readReg64 .x20 = a → sm.readReg64 .x24 = 104#64 →
      sm.readReg64 .x25 = BitVec.ofNat 64 keys.length →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
          ((a + 48#64) ↦₆₄ cap') ∗ ((a + 56#64) ↦₆₄ ptr') ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
          arrayAt (fun m b => prostMsgKeyAt A0 m b) 104 ptr' keys ∗
          memRegion (ptr' + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
          memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap'.toNat - (keys.length + 1)) * 104) ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
        vecOf A0 104 8 (fun m b => prostMsgKeyAt A0 m b) (a + 48#64) keys ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R)) := by
  have hG' := hC.grow
  have hule_r : BitVec.ule (BitVec.ofNat 64 rest.length) (BitVec.ofNat 64 rest.length) = true := by
    simp [BitVec.ule]
  have hbne_r : (BitVec.ofNat 64 rest.length != BitVec.ofNat 64 rest.length) = false :=
    bne_self_eq_false _
  change s.pc = (blkPl_516).base + 580#64 at hpc
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h24 : s.readReg64 (Reg.gpr 24#5) = 104#64 := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 rest.length := hx25
  apply SepWPp.fold (vecOf_keys_open a keys) (by sep_frame)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap; apply SepWPp.exists_elim; intro ptr
  apply SepWPp.pure_left; rintro ⟨hcap_le, hcap_lt, hptr⟩
  by_cases hfull : keys.length = cap.toNat
  · have hbeq_cap : (BitVec.ofNat 64 keys.length == cap) = true := by rw [hfull]; simp
    rw [memRegion_spare_eq_emp_of_full cap ptr keys.length hfull, stackAt_c3Sub_to_growOne (sp0 - 240#64)]
    simp only [emp_sepConj]
    apply SepWPp.fold (arrayAt_prostMsgKeyAt_move_bytes A0 keys ptr) (by sep_frame)
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.exists_elim; intro bs; apply SepWPp.exists_elim; intro H
    apply SepWPp.pure_left; rintro ⟨hbs_len, hmov⟩
    have hbs_cap : bs.length = cap.toNat * 104 := by rw [hbs_len, hfull]
    have hmax_le : 8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63 := by unfold maxMessageKeys at hbound; omega
    refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 43) hcl ?_
    unfold sliceCursorAt; iterate 11 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hcl1
    refine call_frame_lscl_keys_cro (x := (a + 48#64, cap, ptr, bs))
      (ret_pc := lsmpl.base 516 + 376#64) hcl1 hG'
      (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      (spAligned_of_sp_eq (by simp only [arm64_norm]) hsp_align) (by simp only [arm64_norm]; rfl)
      (growOne_placed_pre_eq_extW_keys a cap ptr (sp0 - 240#64) bs _ (by simp only [hsp, arm64_norm]) hbs_cap)
      ⟨hbs_cap, by simp only [arm64_norm], hptr, hmax_le⟩ (by sep_frame)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans_receiverChains (by simp only [htr, arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hclm
    have hregs_m : Chain3MkRegs s sm :=
      Chain3MkRegs.trans
        ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm]⟩ (.of_calleeSaved hcsm)
    have h25_m : sm.readReg64 .x25 = BitVec.ofNat 64 keys.length := by
      have h25_cs := hcsm.2.2.2.2.2.2.1; simp only [arm64_norm] at h25_cs
      change sm.readReg64 (Reg.gpr 25#5) = _; rw [h25_cs, hfull, BitVec.ofNat_toNat]; rfl
    have hspm' : sm.sp = sp0 - 240#64 := by simpa only [hsp, arm64_norm] using hspm
    have hsp_align_m : sm.spAligned = true := spAligned_of_sp_eq (hspm'.trans hsp.symm) hsp_align
    refine SepWPp.fold (growOne_placed_post_elim_sp_extW_keys a cap ptr (sp0 - 240#64) bs keys.length _ sm
      (by simp only [hsp, arm64_norm]) hfull hbs_len hbound) rfl ?_
    simp only [sepConj_assoc]; apply SepWPp.pure_left; intro htr_m
    have htr_m' : sm.trace = s0.trace := by simpa only [htr, arm64_norm] using htr_m
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.exists_elim; intro cap'; apply SepWPp.exists_elim; intro ptr'
    apply SepWPp.pure_left; rintro ⟨hcap'_le, hcap'_lt, hptr'⟩
    apply SepWPp.fold (hmov ptr') (by sep_frame)
    apply SepWPp.fold (Entails.of_eq (stackAt_c3Sub_to_growOne (sp0 - 240#64)).symm) (by sep_frame)
    refine SepWPp.mono_pre_seedChain ?_ (hnext sm cap' ptr' hcap'_le hcap'_lt hptr'
      hpcm hrunm hspm' hsp_align_m hclm htr_m' hregs_m (hregs_m.2.1.trans hx20)
      (hregs_m.2.2.2.2.2.1.trans hx24) h25_m)
    unfold sliceCursorAt; exact sep_ac_seedChain (by ac_rfl)
  · have hcap_le' : keys.length + 1 ≤ cap.toNat := by omega
    have hbeq_cap : (BitVec.ofNat 64 keys.length == cap) = false := beq_ofNat_cap_false hcap_le hfull
    have hbne_cap : (BitVec.ofNat 64 keys.length != cap) = true := by
      rw [bne_iff_ne, ne_eq, ← beq_iff_eq, hbeq_cap]; decide
    rw [memRegion_spare_split_of_lt cap ptr keys.length hcap_le' hcap_lt]
    refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 516 + 376#64) hcl ?_
    unfold sliceCursorAt; iterate 9 wp_step
    refine SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [hrun, arm64_norm]) ?_; intro hcl1
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ cap ptr hcap_le' hcap_lt hptr
      (by simp only [arm64_norm]; rfl) (by simp only [hrun, arm64_norm])
      (by simp only [hsp, arm64_norm]) (spAligned_of_sp_eq (by simp only [arm64_norm]) hsp_align)
      hcl1 (by simp only [htr, arm64_norm])
      ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm]⟩
      (by simp only [h20, arm64_norm]) (by simp only [h24, arm64_norm])
      (by simp only [arm64_norm]))
    unfold sliceCursorAt; exact sep_ac_seedChain (by ac_rfl)

private theorem step_mkPush_cro [LibsignalPlacement] {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW ext)
    (a bufRef slot ptr_rest sp0 : BitVec 64) (keys : List MessageKeyGenerator)
    (mk : MessageKeyGenerator) (rest : List (BitVec 8))
    {x : ChainMergeGenGhost} {R : SepProp} {s0 s : State} {F : SepProp}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hbound : keys.length ≤ maxMessageKeys)
    (hpc : s.pc = chain3PCPlacedAtW ext 580#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = bufRef) (hx20 : s.readReg64 .x20 = a)
    (hx24 : s.readReg64 .x24 = 104#64) (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 rest.length)
    (hnext : ∀ (sm : State),
      sm.pc = chain3PCPlacedAtW ext 168#64 → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace → Chain3MkRegs s sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
          vecOf A0 104 8 (fun m b => prostMsgKeyAt A0 m b) (a + 48#64) (keys ++ [mk]) ∗
          memRegion (sp0 - 232#64) 104 ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
        vecOf A0 104 8 (fun m b => prostMsgKeyAt A0 m b) (a + 48#64) keys ∗
        prostMsgKeyAt A0 mk (sp0 - 232#64) ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R)) := by
  have hsp_align : s.spAligned = true := c3mk_push_spAligned hsp halign
  refine SepWPp.focus_pre (step_c3mk_push4d_cro hC a bufRef slot ptr_rest sp0 keys rest hbound
    hpc hrun hsp hsp_align hcl htr hx19 hx20 hx24 hx25 ?_)
  intro s4 cap' ptr' hcap'_le hcap'_lt hptr' hpc4 hrun4 hsp4 hsp_align4 hcl4 htr4 hregs4 hx20_4 hx24_4 hx25_4
  refine SepWPp.focus_pre (step_c3mk_push4e_placed a cap' ptr' sp0 keys mk hcap'_le hcap'_lt hptr'
    hpc4 hrun4 hsp4 hsp_align4 hcl4 htr4 hx20_4 hx24_4 hx25_4 ?_)
  intro s5 hpc5 hrun5 hsp5 hcl5 htr5 hregs5
  refine SepWPp.mono_pre_seedChain ?_ (hnext s5 hpc5 hrun5 hsp5 hcl5 htr5 (hregs4.trans hregs5))
  exact sep_ac_seedChain (by ac_rfl)

theorem chain3MessageKeys_cro_placed_ok [LibsignalPlacement] (ext : LibsignalHooks) :
    Chain3MessageKeysCroStmt ext := by
  intro hC x R s0 k s hk htag ⟨hcro, hs⟩
  refine segStepG_keep_cro hcro ?_
  rcases hs with ⟨hpc, hrun, htr, hvregs, hcl, hsp, hal, hx29, hx19, hx20, hx21,
    hx22, hx23, hx24, hx26, hx27, hx28, hOk, hlen_pay, hmem⟩
  obtain ⟨mk, hfl⟩ := chainField_eq_key_of_tag4 htag
  have hmk_mem : mk ∈ x.c.keys := mem_keys_of_key_mem_fields (hfl ▸ List.getElem_mem hk)
  have hseed : mk.seed.length = 32 := hOk.2.2.2.1 mk hmk_mem
  have hbound : (chainGAfter x.c k).keys.length ≤ maxMessageKeys :=
    le_trans (chainGAfter_keys_length_le x.c k) hOk.2.2.2.2
  have halign : s0.sp &&& 15#64 = 0#64 := c3mk_sp0_aligned_of_sub_240
    (by have h1 : s.sp &&& 15#64 = 0#64 := by simpa [State.spAligned, beq_iff_eq] using hal
        rwa [hsp] at h1)
  let pfx : List (BitVec 8) :=
    encodeVarint (BitVec.ofNat 64 x.c.enc.length) ++ (x.c.fields.take k).flatMap ChainField.enc
  let rest : List (BitVec 8) := (x.c.fields.drop (k + 1)).flatMap ChainField.enc ++ x.tail
  let body : List (BitVec 8) := pbVarint 1 mk.counter.toNat ++ pbBytes 5 mk.seed
  have hpay_eq : x.c.payload ++ x.tail =
      pfx ++ (0x22#8 :: BitVec.ofNat 8 body.length :: (body ++ rest)) := by
    dsimp only [body]; rw [chainG_payload_split x.c k x.tail, drop_fields_flatMap_enc_of_key hk hfl x.tail,
      lenField_4_encMessageKey_eq hseed, encMessageKey_eq_pb hseed]; rfl
  have hcur_open : sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
      ((x.c.fields.drop k).flatMap ChainField.enc ++ x.tail) =
      (x.ptr ↦ₛ pfx) ∗ sliceCursorAt x.slot (x.ptr + BitVec.ofNat 64 pfx.length)
        (0x22#8 :: BitVec.ofNat 8 body.length :: (body ++ rest)) := by
    have hrem : (x.c.fields.drop k).flatMap ChainField.enc ++ x.tail =
        0x22#8 :: BitVec.ofNat 8 body.length :: (body ++ rest) := by
      dsimp only [body]; rw [drop_fields_flatMap_enc_of_key hk hfl x.tail,
        lenField_4_encMessageKey_eq hseed, encMessageKey_eq_pb hseed]; rfl
    rw [hrem, hpay_eq, sliceCursorAfter_append_eq_seedChain]
  have hmk_lt : body.length < 128 := by
    dsimp only [body]; rw [← encMessageKey_eq_pb hseed]; exact encMessageKey_length_lt128 hseed
  have htail_le : x.tail.length ≤ rest.length := by simp [rest]
  have hlen_a : 2 + (body.length + rest.length) < 2 ^ 62 := by
    have h := hlen_pay; rw [hpay_eq] at h; simp only [List.length_append, List.length_cons] at h ⊢; omega
  have hlen_b : (pbVarint 1 mk.counter.toNat ++ (pbBytes 5 mk.seed ++ rest)).length < 2 ^ 62 := by
    dsimp only [body] at hlen_a; simp only [List.length_append] at hlen_a ⊢; omega
  have hlen_c : (pbBytes 5 mk.seed ++ rest).length < 2 ^ 62 := by
    simp only [List.length_append] at hlen_b ⊢; omega
  have hk_lt : mk.seed.length < 128 := by omega
  let savedRest : SepProp :=
    memRegion (s0.sp - 240#64) 8 ∗ memRegion (s0.sp - 128#64) 48 ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ memRegion (s0.sp - 56#64) 8 ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
  have hmem' : s.mem ⊨
      ((x.bufRef ↦₆₄ x.slot) ∗ memRegion (s0.sp - 232#64) 104 ∗
        sliceCursorAt x.slot (x.ptr + BitVec.ofNat 64 pfx.length)
          (0x22#8 :: BitVec.ofNat 8 body.length :: (body ++ rest)) ∗
        stackAt (s0.sp - 240#64) chainMerge3SubStackX ∗
        vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (x.a + 48#64) (chainGAfter x.c k).keys ∗
        c3mkChainNoKeys A0 x.a (chainGAfter x.c k) ∗ (x.ptr ↦ₛ pfx) ∗ savedRest) ∗ R := by
    rw [chain3GAt_keys_split, hcur_open, chain3SavedRegs_c3mk_split] at hmem
    dsimp only [savedRest]; exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
  refine segStepG_of_sepWPp (ret := chain3PCPlacedAtW ext 168#64) hmem' ?_
  refine SepWPp.bind_lscro (mid := chain3PCPlacedAtW ext 580#64)
    (Q1 := fun s2 P2 => s2.sp = s0.sp - 240#64 ∧ LibsignalCodeLoaded lsmpl s2.mem ∧
      s2.trace = s0.trace ∧ s2.readReg64 .x25 = BitVec.ofNat 64 rest.length ∧ Chain3MkRegs s s2 ∧
      (P2 ⊢ ((x.bufRef ↦₆₄ x.slot) ∗ vecU8At A0 (s0.sp - 160#64) 0#64 1#64 [] ∗
        sliceCursorAt x.slot
          (x.ptr + BitVec.ofNat 64 pfx.length + 2#64 + BitVec.ofNat 64 (pbVarint 1 mk.counter.toNat).length)
          (pbBytes 5 mk.seed ++ rest) ∗
        stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
        (vecU8 A0 (s0.sp - 232#64) [] ∗ vecU8 A0 (s0.sp - 208#64) [] ∗ vecU8 A0 (s0.sp - 184#64) [] ∗
          ((s0.sp - 136#64) ↦₃₂ mk.counter) ∗ memRegion (s0.sp - 132#64) 4 ∗
          ((x.ptr + BitVec.ofNat 64 pfx.length) ↦ₛ [0x22#8, BitVec.ofNat 8 body.length]) ∗
          ((x.ptr + BitVec.ofNat 64 pfx.length + 2#64) ↦ₛ pbVarint 1 mk.counter.toNat) ∗
          vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (x.a + 48#64) (chainGAfter x.c k).keys ∗
          c3mkChainNoKeys A0 x.a (chainGAfter x.c k) ∗ (x.ptr ↦ₛ pfx) ∗ savedRest))) hcro ?_ ?_
  · refine SepWPp.focus_pre (step_mkHead_cro hC x.bufRef x.slot (x.ptr + BitVec.ofNat 64 pfx.length)
      s0.sp body rest x.tail hmk_lt htail_le hlen_a hpc hrun hsp halign hcl htr hx19 hx21 hx22 hx23 ?_)
    intro s1 hpc1 hrun1 hsp1 hcl1 htr1 hx25_1 hregs1
    dsimp only [body]
    rw [List.append_assoc (pbVarint 1 mk.counter.toNat) (pbBytes 5 mk.seed) rest]
    refine SepWPp.focus_pre (step_mkCnt_cro hC x.bufRef x.slot
      (x.ptr + BitVec.ofNat 64 pfx.length + 2#64) s0.sp mk.counter (pbBytes 5 mk.seed) rest
      hlen_b hpc1 hrun1 hsp1 halign hcl1 htr1 (hregs1.1.trans hx19) hx25_1 ?_)
    intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hx25_2 hregs2
    refine SepWPp.done hpc2 hrun2 ⟨hsp2, hcl2, htr2, hx25_2, hregs1.trans hregs2, ?_⟩
    exact sep_ac_seedChain (by ac_rfl)
  · intro s2 P2 hpc2 hrun2 hcro2 ⟨hsp2, hcl2, htr2, hx25_2, hregs12, hent2⟩
    refine SepWPp.mono_pre_seedChain hent2 ?_
    refine step_mkSeed_cro hC x.bufRef x.slot
      (x.ptr + BitVec.ofNat 64 pfx.length + 2#64 + BitVec.ofNat 64 (pbVarint 1 mk.counter.toNat).length)
      s0.sp mk.seed rest hk_lt hlen_c hcro2 hpc2 hrun2 hsp2 halign hcl2 htr2
      (hregs12.1.trans hx19) (hregs12.2.2.2.1.trans hx22) hx25_2 ?_
    intro s3 hpc3 hrun3 hsp3 hcl3 htr3 hx25_3 hregs3
    have hregs13 : Chain3MkRegs s s3 := hregs12.trans hregs3
    apply SepWPp.fold (Entails.of_eq (c3mk_prostMsgKeyAt_fold s0.sp mk)) (by sep_focus)
    refine SepWPp.focus_pre (step_mkPush_cro hC x.a x.bufRef x.slot
      (x.ptr + BitVec.ofNat 64 pfx.length + 2#64 +
        BitVec.ofNat 64 (pbVarint 1 mk.counter.toNat).length + BitVec.ofNat 64 (pbBytes 5 mk.seed).length)
      s0.sp (chainGAfter x.c k).keys mk rest hbound hpc3 hrun3 hsp3 halign hcl3 htr3
      (hregs13.1.trans hx19) (hregs13.2.1.trans hx20) (hregs13.2.2.2.2.2.1.trans hx24) hx25_3 ?_)
    intro s4 hpc4 hrun4 hsp4 hcl4 htr4 hregs4
    have hregs : Chain3MkRegs s s4 := hregs13.trans hregs4
    refine SepWPp.done hpc4 hrun4 fun hmem4 => ?_
    refine ⟨hpc4, hrun4, htr4, hregs.2.2.2.2.2.2.2.2.2.2.trans hvregs, hcl4, hsp4,
      by simp only [State.spAligned, hsp4, ← hsp]; exact hal,
      hregs.2.2.2.2.2.2.2.2.2.1.trans hx29, hregs.1.trans hx19, hregs.2.1.trans hx20,
      hregs.2.2.1.trans hx21, hregs.2.2.2.1.trans hx22, hregs.2.2.2.2.1.trans hx23,
      hregs.2.2.2.2.2.1.trans hx24, hregs.2.2.2.2.2.2.1.trans hx26,
      hregs.2.2.2.2.2.2.2.1.trans hx27, hregs.2.2.2.2.2.2.2.2.1.trans hx28, hOk, hlen_pay, ?_⟩
    rw [chainGAfter_succ_of_key hk hfl, chain3GAt_push_key, chain3SavedRegs_c3mk_split,
      ← sliceCursorAfter_tag4_combine x.slot x.ptr (x.c.payload ++ x.tail) pfx
        (pbVarint 1 mk.counter.toNat) (pbBytes 5 mk.seed) rest hpay_eq]
    dsimp only [body, savedRest] at hmem4 ⊢
    exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem4

/-- `message::merge<Chain> [local#4]` (Block `516`) under `StoreKit.withLsCodeRoLoaded` on any `callerProg` over `ext`, discharged from the 7 standard `HookSat`/panic hypotheses. -/
theorem chainMerge5_cro_of_block_hooks [LibsignalPlacement] {ext : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk ext]
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat ext lsRustAllocSym (rustAllocSpec A0))
    (hrealloc : HookSat ext lsRustReallocSym (rustReallocSpec A0))
    (hdealloc : HookSat ext lsRustDeallocSym (rustDeallocSpec A0))
    (hmc : HookSat ext lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : ext lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok callerProg (lsmpl.base 516)
      (StoreKit.withLsCodeRoLoaded lsmpl VerNe.Chain3.chainMerge3RawSpecW) :=
  chainMerge5_cro_of_block
    (chainMerge3W_cro_placed_ok ext
      (chain3CalleesCro_of_hooks hshim halloc hrealloc hdealloc hmc hpanic_alloc hpanic_raw)
      (chain3Entry_cro_placed_ok ext) (chain3Srk_cro_placed_ok ext)
      (chain3ChainKey_cro_placed_ok ext) (chain3MessageKeys_cro_placed_ok ext))

section RecvSegBSteps
open CryptoVerification.CliHandshake.RespClosurePlaced

set_option maxHeartbeats 400000 in
theorem step_2114_to_2160_top_placed [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (g : OverDecG) (ptr' len w_len : BitVec 64)
    (q0 q1 q2 q3 q4 q5 d0 d1 d2 d3 d4 d5 : BitVec 128) (w6 dw6 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x2114#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (hal : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = g.r19)
    (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64)
    (hx22 : s.readReg64 .x22 = len)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr)
    (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext)
      ((blkPl_518).base + 0x2160#64) s
      (((g.q + 0x980#64) ↦₆₄ ptr') ∗
       ((g.q + 0x988#64) ↦₆₄ w_len) ∗
       RawByteMove.chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
       RawByteMove.chunks104_6QWAt (ptr' + len * 104#64) d0 d1 d2 d3 d4 d5 dw6)
      (fun s1 P_f =>
        (P_f ⊢
          ((g.q + 0x980#64) ↦₆₄ ptr') ∗
          ((g.q + 0x988#64) ↦₆₄ (len + 1#64)) ∗
          RawByteMove.chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
          RawByteMove.chunks104_6QWAt (ptr' + len * 104#64) q0 q1 q2 q3 q4 q5 w6) ∧
        s1.sp = g.q ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = g.r19 ∧
        s1.readReg64 .x20 = g.r20 ∧
        s1.readReg64 .x21 = g.q + 0x930#64 ∧
        s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x26 = g.r26 ∧
        s1.readReg64 .x27 = g.prevPtr ∧
        s1.readReg64 .x28 = g.q + 0xa90#64 ∧
        s1.readReg64 .x29 = g.q + 0xc70#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = len := hx22
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  conv =>
    arg 4
    rw [chunks104_6QWAt_read_a90_eq_rc g.q q0 q1 q2 q3 q4 q5 w6,
        chunks104_6QWAt_write_eq_rc (ptr' + len * 104#64) d0 d1 d2 d3 d4 d5 dw6]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq ?_, hsp, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm, isCalleeSavedVReg]⟩
  rw [chunks104_6QWAt_read_a90_eq_rc g.q q0 q1 q2 q3 q4 q5 w6,
      chunks104_6QWAt_write_eq_rc (ptr' + len * 104#64) q0 q1 q2 q3 q4 q5 w6]

set_option maxHeartbeats 400000 in
theorem step_2310_to_2114_of_ne_top_placed [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (g : OverDecG) (cap len : BitVec 64)
    (q0 q1 q2 q3 q4 q5 d0 d1 d2 d3 d4 d5 : BitVec 128) (w6 dw6 : BitVec 64)
    (hne : len ≠ cap)
    (hpc : s.pc = (blkPl_518).base + 0x2310#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (hal : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx19 : s.readReg64 .x19 = g.r19)
    (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr)
    (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext)
      ((blkPl_518).base + 0x2114#64) s
      (((g.q + 0x978#64) ↦₆₄ cap) ∗
       ((g.q + 0x988#64) ↦₆₄ len) ∗
       RawByteMove.chunks104_6QWAt (g.q + 0xbf0#64) q0 q1 q2 q3 q4 q5 w6 ∗
       RawByteMove.chunks104_6QWAt (g.q + 0xa90#64) d0 d1 d2 d3 d4 d5 dw6)
      (fun s1 P_f =>
        (P_f ⊢
          ((g.q + 0x978#64) ↦₆₄ cap) ∗
          ((g.q + 0x988#64) ↦₆₄ len) ∗
          RawByteMove.chunks104_6QWAt (g.q + 0xbf0#64) q0 q1 q2 q3 q4 q5 w6 ∗
          RawByteMove.chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6) ∧
        s1.sp = g.q ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = g.r19 ∧
        s1.readReg64 .x20 = g.r20 ∧
        s1.readReg64 .x21 = g.q + 0x930#64 ∧
        s1.readReg64 .x22 = len ∧
        s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x26 = g.r26 ∧
        s1.readReg64 .x27 = g.prevPtr ∧
        s1.readReg64 .x28 = g.q + 0xa90#64 ∧
        s1.readReg64 .x29 = g.q + 0xc70#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have hx0_32 : s.readReg32 (Reg.gpr 0#5) = 0#32 := by simp only [State.readReg32, hx0']; rfl
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  conv =>
    arg 4
    rw [chunks104_6QWAt_read_bf0_eq_rc g.q q0 q1 q2 q3 q4 q5 w6,
        chunks104_6QWAt_write_a90_eq_rc g.q d0 d1 d2 d3 d4 d5 dw6]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq ?_, hsp, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm, isCalleeSavedVReg]⟩
  rw [chunks104_6QWAt_read_bf0_eq_rc g.q q0 q1 q2 q3 q4 q5 w6,
      chunks104_6QWAt_write_a90_eq_rc g.q q0 q1 q2 q3 q4 q5 w6]

set_option maxHeartbeats 400000 in
theorem step_2310_to_growOne_of_eq_top_placed [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (g : OverDecG) (cap : BitVec 64)
    (q0 q1 q2 q3 q4 q5 d0 d1 d2 d3 d4 d5 : BitVec 128) (w6 dw6 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x2310#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (hal : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx19 : s.readReg64 .x19 = g.r19)
    (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr)
    (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext)
      (lsmpl.base 43) s
      (((g.q + 0x978#64) ↦₆₄ cap) ∗
       ((g.q + 0x988#64) ↦₆₄ cap) ∗
       RawByteMove.chunks104_6QWAt (g.q + 0xbf0#64) q0 q1 q2 q3 q4 q5 w6 ∗
       RawByteMove.chunks104_6QWAt (g.q + 0xa90#64) d0 d1 d2 d3 d4 d5 dw6)
      (fun s1 P_f =>
        (P_f ⊢
          ((g.q + 0x978#64) ↦₆₄ cap) ∗
          ((g.q + 0x988#64) ↦₆₄ cap) ∗
          RawByteMove.chunks104_6QWAt (g.q + 0xbf0#64) q0 q1 q2 q3 q4 q5 w6 ∗
          RawByteMove.chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6) ∧
        s1.sp = g.q ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = g.q + 0x978#64 ∧
        s1.readReg64 Reg.lr = (blkPl_518).base + 0x234c#64 ∧
        s1.readReg64 .x19 = g.r19 ∧
        s1.readReg64 .x20 = g.r20 ∧
        s1.readReg64 .x21 = g.q + 0x930#64 ∧
        s1.readReg64 .x22 = cap ∧
        s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x26 = g.r26 ∧
        s1.readReg64 .x27 = g.prevPtr ∧
        s1.readReg64 .x28 = g.q + 0xa90#64 ∧
        s1.readReg64 .x29 = g.q + 0xc70#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have hx0_32 : s.readReg32 (Reg.gpr 0#5) = 0#32 := by simp only [State.readReg32, hx0']; rfl
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  conv =>
    arg 4
    rw [chunks104_6QWAt_read_bf0_eq_rc g.q q0 q1 q2 q3 q4 q5 w6,
        chunks104_6QWAt_write_a90_eq_rc g.q d0 d1 d2 d3 d4 d5 dw6]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq ?_, hsp, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm, isCalleeSavedVReg]⟩
  rw [chunks104_6QWAt_read_bf0_eq_rc g.q q0 q1 q2 q3 q4 q5 w6,
      chunks104_6QWAt_write_a90_eq_rc g.q q0 q1 q2 q3 q4 q5 w6]

set_option maxHeartbeats 400000 in
theorem step_234c_to_2114_top_placed [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (g : OverDecG) (len : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x234c#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (hx19 : s.readReg64 .x19 = g.r19)
    (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64)
    (hx22 : s.readReg64 .x22 = len)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr)
    (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext)
      ((blkPl_518).base + 0x2114#64) s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = g.q ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = g.r19 ∧
        s1.readReg64 .x20 = g.r20 ∧
        s1.readReg64 .x21 = g.q + 0x930#64 ∧
        s1.readReg64 .x22 = len ∧
        s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x26 = g.r26 ∧
        s1.readReg64 .x27 = g.prevPtr ∧
        s1.readReg64 .x28 = g.q + 0xa90#64 ∧
        s1.readReg64 .x29 = g.q + 0xc70#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = len := hx22
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact ⟨Entails.refl _, hsp, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

end RecvSegBSteps

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
