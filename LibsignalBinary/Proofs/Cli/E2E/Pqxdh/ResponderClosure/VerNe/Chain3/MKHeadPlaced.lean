/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MKHead
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.CodePlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MKDefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.EntryPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Base
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import ProofLib.SepLogic.WPp

/-!
# Placed `message::merge<Chain> [local#4]`: MessageKeys Head (`Chain3MkHeadPlacedStmt`)

`[LibsignalPlacement]` Block-`516` counterpart of `VerNe.Chain3.MKHead`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
  (sliceCursorAt sliceCursorAfter DecodeVarintSlowGhost)
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalPlacement
open CryptoVerification.CliHandshake.Placed

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
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

/-! ## 1. Callee step (`decode_varint [local#4]`) -/

set_option maxHeartbeats 400000 in
theorem c3hd_dv_call_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (hC : Chain3CalleesPlacedW ext)
    (bufRef slot curPtr sp0 ret_pc v : BitVec 64) (enc rest : List (BitVec 8))
    (hdv : decodeVarint (enc ++ rest) = some (v, rest))
    (hlen_lt : (enc ++ rest).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 515)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 0xf0#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = bufRef)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp0 - 0xf0#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → sm.readReg64 .x0 = 0#64 → sm.readReg64 .x1 = v →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ (curPtr ↦ₛ enc) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 enc.length) rest ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot curPtr (enc ++ rest) ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R)) := by
  have hcall := hC.dv
  have hlen_lt63 : (enc ++ rest).length < 2 ^ 63 := by omega
  refine SepWPp.call_lscl_c3
    (x := DecodeVarintSlowGhost.mk bufRef slot curPtr (enc ++ rest))
    (F := memRegion (sp0 - 0xf0#64 - BitVec.ofNat 64 chainMerge3SubStackX)
      (chainMerge3SubStackX - decodeVarint2StackX) ∗ F)
    hcall hpc hrun (c3hd_spAligned hsp halign) hcl hlr ?_ ?_ ?_ ?_
  · intro R' hm
    refine intro_withLsCl_c3 hcl ?_
    rw [stackAt_c3Sub_to_decodeVarint (sp0 - 0xf0#64)] at hm
    dsimp only [decodeVarint2SpecX]
    have hpool : A0.pool = emp := rfl
    rw [hpool, hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hlen_lt63⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withLsCl, decodeVarint2SpecX, chainMerge3PlacedSpecW, chainMerge3RawSpecW,
      Serialization.allocPanic] at hm ⊢
    simp only [allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hclm hcsm
    rw [hsp] at hspm
    dsimp only [withLsCl, decodeVarint2SpecX]
    rw [hdv, hsp]
    dsimp only
    have hpool : A0.pool = emp := rfl
    rw [hpool]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun _ => ?_
    refine SepWPp.pure_elim fun ⟨hx0m, hx1m⟩ => ?_
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.mono_pre_seedChain ?_
      (hnext sm hpcm hrunm hspm hclm (htrm.trans htr) hcsm hx0m hx1m)
    rw [sliceCursorAfter_append_eq_seedChain slot curPtr enc rest,
      stackAt_c3Sub_to_decodeVarint (sp0 - 0xf0#64)]
    exact sep_ac_seedChain (by ac_rfl)

/-! ## 2. Straight-line segments -/

set_option maxHeartbeats 400000 in
theorem step_c3hd_head_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (bufRef slot ptr : BitVec 64) (b0 : BitVec 8) (rem1 tail : List (BitVec 8))
    (hlen_gt : tail.length < (b0 :: rem1).length) (hlen_lt : (b0 :: rem1).length < 2 ^ 62)
    {ret : BitVec 64} {s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 0xa8#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = bufRef)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 515 →
      s1.status = .Running → s1.sp = s.sp → LibsignalCodeLoaded lsmpl s1.mem →
      s1.trace = s.trace →
      s1.readReg64 .lr = lsmpl.base 516 + 0xc0#64 →
      s1.readReg64 .x0 = bufRef → Chain3MkRegs s s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1
        (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (b0 :: rem1)) ∗ F) Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (b0 :: rem1)) ∗ F) Q Qp := by
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_lt
  change s.pc = (blkPl_516).base + 0xa8#64 at hpc
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := hx21
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 515) hcl ?_
  unfold sliceCursorAt
  simp only [sepConj_assoc]
  iterate 6 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hcl1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [arm64_norm]) hcl1 (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  unfold sliceCursorAt
  exact sep_ac_seedChain (by ac_rfl)

set_option maxHeartbeats 400000 in
theorem step_c3hd_key4_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (bufRef sp0 : BitVec 64)
    {ret : BitVec 64} {s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 0xc0#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 0xf0#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx1 : s.readReg64 .x1 = 0x22#64)
    (hx19 : s.readReg64 .x19 = bufRef)
    (hx22 : s.readReg64 .x22 = sp0 - 232#64)
    (hx23 : s.readReg64 .x23 = 1#64)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 515 →
      s1.status = .Running → s1.sp = sp0 - 0xf0#64 → LibsignalCodeLoaded lsmpl s1.mem →
      s1.trace = s.trace →
      s1.readReg64 .lr = lsmpl.base 516 + 0x158#64 →
      s1.readReg64 .x0 = bufRef → Chain3MkRegs s s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1
        ((vecU8 A0 (sp0 - 232#64) [] ∗ vecU8 A0 (sp0 - 208#64) [] ∗ vecU8 A0 (sp0 - 184#64) [] ∗
          vecU8At A0 (sp0 - 160#64) 0#64 1#64 [] ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
          memRegion (sp0 - 132#64) 4) ∗ F) Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s (memRegion (sp0 - 232#64) 104 ∗ F) Q Qp := by
  have hal0 : (sp0 &&& 15#64 == 0#64) = true := beq_iff_eq.mpr halign
  have hal1 : ((sp0 - 0xf0#64) &&& 15#64 == 0#64) = true :=
    beq_iff_eq.mpr (c3hd_sp_sub_240_aligned halign)
  change s.pc = (blkPl_516).base + 0xc0#64 at hpc
  have h0 : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s.readReg64 (Reg.gpr 1#5) = 0x22#64 := hx1
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h22 : s.readReg64 (Reg.gpr 22#5) = sp0 - 232#64 := hx22
  have h23 : s.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 515) hcl ?_
  rw [memRegion104_c3hd_split sp0, memRegion80_chainInit_eq_cells10_receiverChains sp0]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro c0
  apply SepWP.exists_elim; intro c1
  apply SepWP.exists_elim; intro c2
  apply SepWP.exists_elim; intro c3
  apply SepWP.exists_elim; intro c4
  apply SepWP.exists_elim; intro c5
  apply SepWP.exists_elim; intro c6
  apply SepWP.exists_elim; intro c7
  apply SepWP.exists_elim; intro c8
  apply SepWP.exists_elim; intro c9
  apply SepWP.exists_elim; intro c10
  apply SepWP.exists_elim; intro c11
  apply SepWP.exists_elim; intro wc
  iterate 28 wp_step
  apply SepWP.fold (c3hd_default_of_cells sp0) (by sep_focus)
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hcl1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm])
    (by simp only [hrun, arm64_norm]) (by simp only [hsp, arm64_norm]) hcl1
    (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  exact sep_ac_seedChain (by ac_rfl)

set_option maxHeartbeats 400000 in
theorem step_c3hd_len_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (bufRef slot ptr : BitVec 64) (body rest : List (BitVec 8))
    (hlen_lt : (body ++ rest).length < 2 ^ 62)
    {ret : BitVec 64} {s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 0x158#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 body.length)
    (hx19 : s.readReg64 .x19 = bufRef)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 516 + 0x244#64 →
      s1.status = .Running → s1.sp = s.sp → LibsignalCodeLoaded lsmpl s1.mem →
      s1.trace = s.trace →
      s1.readReg64 .x25 = BitVec.ofNat 64 rest.length → Chain3MkRegs s s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1
        (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (body ++ rest)) ∗ F) Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (body ++ rest)) ∗ F) Q Qp := by
  have hlen_app : (body ++ rest).length = body.length + rest.length := List.length_append
  have hult := ult_ofNat_add_right_false_seedChain (m := body.length) (k := rest.length) (by omega)
  have hsub := CryptoVerification.E2E.Record.DeserializeSeed.bv_ofNat_add_sub_left_seedChain
    body.length rest.length
  change s.pc = (blkPl_516).base + 0x158#64 at hpc
  have h0 : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 body.length := hx1
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 516 + 0x244#64) hcl ?_
  unfold sliceCursorAt
  rw [hlen_app]
  simp only [sepConj_assoc]
  iterate 5 wp_step
  refine SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [hrun, arm64_norm]) ?_
  intro hcl1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]; rfl)
    (by simp only [hrun, arm64_norm]) (by simp only [arm64_norm]) hcl1
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  unfold sliceCursorAt
  rw [hlen_app]
  exact sep_ac_seedChain (by ac_rfl)

/-! ## 3. Proof of `Chain3MkHeadPlacedStmt` -/

set_option maxHeartbeats 400000 in
theorem chain3MkHead_placed_ok [LibsignalPlacement] (ext : String → Option (State → State)) :
    Chain3MkHeadPlacedStmt ext := by
  intro hC bufRef slot ptr sp0 body rest tail x R s0 s F ret Q hbody htail hlen_lt
    hpc hrun hsp halign hcl htr hx19 hx21 hx22 hx23 hnext
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
    (show (((bufRef ↦₆₄ slot) ∗ memRegion (sp0 - 0xe8#64) 104 ∗
        sliceCursorAt slot ptr (0x22#8 :: rem1) ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F) ⊢
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (0x22#8 :: rem1)) ∗
        (memRegion (sp0 - 0xe8#64) 104 ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX ∗ F)) from
      sep_ac_seedChain (by ac_rfl)) ?_
  refine step_c3hd_head_placed bufRef slot ptr 0x22#8 rem1 tail hlen_gt hlen_cons_lt
    hpc hrun hcl hx19 hx21 ?_
  intro s1 hpc1 hrun1 hsp1 hcl1 htr1 hlr1 hx0_1 hregs1
  refine SepWPp.mono_pre_seedChain
    (show (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr ([0x22#8] ++ rem1)) ∗
        (memRegion (sp0 - 0xe8#64) 104 ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX ∗ F)) ⊢
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr ([0x22#8] ++ rem1) ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗
        (memRegion (sp0 - 0xe8#64) 104 ∗ F)) from
      sep_ac_seedChain (by ac_rfl)) ?_
  refine c3hd_dv_call_placed hC bufRef slot ptr sp0
    (lsmpl.base 516 + 0xc0#64)
    0x22#64 [0x22#8] rem1 rfl hlen_cons_lt
    hpc1 hrun1 (hsp1.trans hsp) halign hcl1 (htr1.trans htr) hlr1 hx0_1 ?_
  intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hcs2 hx0_2 hx1_2
  have hregs2 : Chain3MkRegs s s2 := hregs1.trans (Chain3MkRegs.of_calleeSaved hcs2)
  have hx19_2 : s2.readReg64 .x19 = bufRef := hregs2.1.trans hx19
  have hx22_2 : s2.readReg64 .x22 = sp0 - 232#64 := hregs2.2.2.2.1.trans hx22
  have hx23_2 : s2.readReg64 .x23 = 1#64 := hregs2.2.2.2.2.1.trans hx23
  refine SepWPp.mono_pre_seedChain
    (show (((bufRef ↦₆₄ slot) ∗ (ptr ↦ₛ [0x22#8]) ∗
        sliceCursorAt slot (ptr + 1#64) rem1 ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗
        (memRegion (sp0 - 232#64) 104 ∗ F)) ⊢
      (memRegion (sp0 - 232#64) 104 ∗
        ((bufRef ↦₆₄ slot) ∗ (ptr ↦ₛ [0x22#8]) ∗
          sliceCursorAt slot (ptr + 1#64) rem1 ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX ∗ F)) from
      sep_ac_seedChain (by ac_rfl)) ?_
  refine step_c3hd_key4_placed bufRef sp0 hpc2 hrun2 hsp2 halign hcl2
    hx0_2 hx1_2 hx19_2 hx22_2 hx23_2 ?_
  intro s3 hpc3 hrun3 hsp3 hcl3 htr3 hlr3 hx0_3 hregs23
  have hregs3 : Chain3MkRegs s s3 := hregs2.trans hregs23
  refine SepWPp.mono_pre_seedChain
    (show ((vecU8 A0 (sp0 - 232#64) [] ∗ vecU8 A0 (sp0 - 208#64) [] ∗ vecU8 A0 (sp0 - 184#64) [] ∗
        vecU8At A0 (sp0 - 160#64) 0#64 1#64 [] ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
        memRegion (sp0 - 132#64) 4) ∗
        ((bufRef ↦₆₄ slot) ∗ (ptr ↦ₛ [0x22#8]) ∗
          sliceCursorAt slot (ptr + 1#64) ([BitVec.ofNat 8 body.length] ++ (body ++ rest)) ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX ∗ F)) ⊢
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot (ptr + 1#64) ([BitVec.ofNat 8 body.length] ++ (body ++ rest)) ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗
        (vecU8 A0 (sp0 - 232#64) [] ∗ vecU8 A0 (sp0 - 208#64) [] ∗ vecU8 A0 (sp0 - 184#64) [] ∗
          vecU8At A0 (sp0 - 160#64) 0#64 1#64 [] ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
          memRegion (sp0 - 132#64) 4 ∗ (ptr ↦ₛ [0x22#8]) ∗ F)) from
      sep_ac_seedChain (by ac_rfl)) ?_
  refine c3hd_dv_call_placed hC bufRef slot (ptr + 1#64) sp0
    (lsmpl.base 516 + 0x158#64)
    (BitVec.ofNat 64 body.length) [BitVec.ofNat 8 body.length] (body ++ rest)
    hdv_L hlen_rem1_lt
    hpc3 hrun3 hsp3 halign hcl3 (htr3.trans htr2) hlr3 hx0_3 ?_
  intro s4 hpc4 hrun4 hsp4 hcl4 htr4 hcs4 hx0_4 hx1_4
  have hregs4 : Chain3MkRegs s s4 := hregs3.trans (Chain3MkRegs.of_calleeSaved hcs4)
  have hx19_4 : s4.readReg64 .x19 = bufRef := hregs4.1.trans hx19
  refine SepWPp.mono_pre_seedChain
    (show (((bufRef ↦₆₄ slot) ∗ ((ptr + 1#64) ↦ₛ [BitVec.ofNat 8 body.length]) ∗
        sliceCursorAt slot (ptr + 1#64 + 1#64) (body ++ rest) ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗
        (vecU8 A0 (sp0 - 232#64) [] ∗ vecU8 A0 (sp0 - 208#64) [] ∗ vecU8 A0 (sp0 - 184#64) [] ∗
          vecU8At A0 (sp0 - 160#64) 0#64 1#64 [] ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
          memRegion (sp0 - 132#64) 4 ∗ (ptr ↦ₛ [0x22#8]) ∗ F)) ⊢
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot (ptr + 2#64) (body ++ rest)) ∗
        (vecU8 A0 (sp0 - 232#64) [] ∗ vecU8 A0 (sp0 - 208#64) [] ∗ vecU8 A0 (sp0 - 184#64) [] ∗
          vecU8At A0 (sp0 - 160#64) 0#64 1#64 [] ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
          memRegion (sp0 - 132#64) 4 ∗ (ptr ↦ₛ [0x22#8]) ∗
          ((ptr + 1#64) ↦ₛ [BitVec.ofNat 8 body.length]) ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX ∗ F)) by
      rw [c3hd_ptr_add_one_add_one ptr]
      exact sep_ac_seedChain (by ac_rfl)) ?_
  refine step_c3hd_len_placed bufRef slot (ptr + 2#64) body rest hlen_body_rest_lt
    hpc4 hrun4 hcl4 hx0_4 hx1_4 hx19_4 ?_
  intro s5 hpc5 hrun5 hsp5 hcl5 htr5 hx25_5 hregs45
  have hregs5 : Chain3MkRegs s s5 := hregs4.trans hregs45
  refine SepWPp.mono_pre_seedChain ?_
    (hnext s5 hpc5 hrun5 (hsp5.trans hsp4) hcl5 (htr5.trans htr4) hx25_5 hregs5)
  rw [← c3hd_pointsTo_hdr_combine ptr (BitVec.ofNat 8 body.length)]
  exact sep_ac_seedChain (by ac_rfl)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
