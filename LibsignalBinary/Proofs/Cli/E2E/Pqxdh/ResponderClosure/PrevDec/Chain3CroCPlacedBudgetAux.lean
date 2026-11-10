/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroBPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroCPlaced
public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.ChainKeyEpilogue
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Base
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `VerNe.Chain3` (Block `516`) `MessageKeys` Head, Counter, and Seed

Budget-arithmetic lemmas and VM-preserving sub-slice steppers (`step_mkHead_cro`,
`step_mkCnt_cro`, `step_mkSeed_cro`) for tag 4 (`message_keys`) of `message::merge<Chain> [local#4]`
(Block `516`) under `StoreKit.LibsignalCodeRoLoaded`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroCPlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open CryptoGames.LibsignalSession (MessageKeyGenerator maxMessageKeys)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalHooks LibsignalPlacement lsmpl
)
open CryptoVerification.RustHeap (RustAlloc vecU8 vecU8At)
open CryptoVerification.LibsignalProtoCodec (
  WireType decodeVarint decodeVarint_encodeVarint encodeKey
)
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAfter sliceCursorAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.E2E.Record (encMessageKey lenField pbBytes pbVarint pbVarintBody)
open CryptoVerification.E2E.Record.DeserializeSeed (
  bv_ofNat_add_sub_left_seedChain encodeVarint_lt128_seedChain
  memRegion80_chainInit_eq_cells10_receiverChains pbVarint1_ptr_advance_seedChain
  pbVarintBody_u32_eq_encodeVarint_seedChain sep_ac_seedChain
  sp_sub_240_aligned_receiverChains
)
open Proofs.libsignal.Hooks2 (
  ule_ofNat_of_gt_false_seedChain62 ult_ofNat_of_gt_true_seedChain62
)
open CryptoVerification.E2E.Record.DeserializeGeneral (
  ChainField ChainG ChainMergeGenGhost chainGAfter
)
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG (
  chainFieldKeys encMessageKey_eq_pb foldl_chainG_apply_keys
  lenField_4_encMessageKey_eq ult_ofNat_add_right_false_seedChain
)
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG (
  chainG_enc_eq_fields_local
)
open CryptoVerification.CliHandshake.Placed (blkLib_eq_516 blkPl_516 lsProg_516)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3 (
  Chain3MkRegs SepWPp.of_sepWP_lscl_c3
  c3cnt_pointsTo_08_combine c3cnt_zeroExtend64_setWidth32
  c3hd_default_of_cells c3hd_pointsTo_hdr_combine c3hd_ptr_add_one_add_one
  c3hd_sp_sub_240_aligned c3seed_pointsTo_2a_combine
  chain3PCPlacedAtW chainMerge3SubStackX memRegion104_c3hd_split
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (BoundedRustEvs)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsXBudget (flatMap_take_length_le)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroAPlacedBudgetAux (
  sepWPp_mono_pre_c3
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroAPlacedBudget (
  Chain3CalleesCroPlacedW SepWPp.bind_lscro c3_dv_call_cro
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroBPlacedBudget (
  c3_bm_call_cro pool_eq_of_vm_c3 sepWPp_focus_pre_false_c3
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg
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

/-! ## Tag-4 (`MessageKeys`) Budget-Arithmetic Lemmas -/

theorem chainFieldKeys_length_le_enc (fl : ChainField) :
    (chainFieldKeys fl).length ≤ fl.enc.length := by
  cases fl with
  | srk _ => simp [chainFieldKeys]
  | priv _ => simp [chainFieldKeys]
  | ck _ _ => simp [chainFieldKeys]
  | key mk =>
    unfold chainFieldKeys ChainField.enc lenField
    have hk4 : encodeKey 4 WireType.lengthDelimited = [0x22#8] := rfl
    rw [hk4]
    simp only [List.length_singleton, List.singleton_append, List.cons_append, List.length_cons,
      List.length_nil, List.length_append]
    omega

theorem flatMap_chainFieldKeys_length_le_enc (fs : List ChainField) :
    (fs.flatMap chainFieldKeys).length ≤ (fs.flatMap ChainField.enc).length := by
  induction fs with
  | nil => simp
  | cons fl fs ih =>
    simp only [List.flatMap_cons, List.length_append]
    have hfl := chainFieldKeys_length_le_enc fl
    omega

theorem chainGAfter_keys_length_le_payload (c : ChainG) (k : Nat) :
    (chainGAfter c k).keys.length ≤ c.payload.length := by
  unfold chainGAfter
  rw [foldl_chainG_apply_keys]
  dsimp only [ChainG.empty]
  rw [List.nil_append]
  have h1 := flatMap_chainFieldKeys_length_le_enc (c.fields.take k)
  have h2 := flatMap_take_length_le ChainField.enc c.fields k
  have h3 : (c.fields.flatMap ChainField.enc).length = c.enc.length := by
    rw [← chainG_enc_eq_fields_local c]
  unfold ChainG.payload
  rw [List.length_append]
  omega

theorem tag4_field_enc_length_ge {c : ChainG} {k : Nat} (hk : k < c.fields.length)
    {mk : MessageKeyGenerator} (hfl : c.fields[k]'hk = .key mk) (hseed : mk.seed.length = 32) :
    36 ≤ (c.fields[k]'hk).enc.length := by
  rw [hfl]
  change 36 ≤ (lenField 4 (encMessageKey mk)).length
  rw [lenField_4_encMessageKey_eq hseed, encMessageKey_eq_pb hseed]
  have hs : (pbBytes 5 mk.seed).length = 34 := by
    rw [CryptoVerification.E2E.Record.DeserializeSeed.pbBytes_lt128_eq_seedChain
      5 (by decide) mk.seed (by omega)]
    simp [hseed]
  simp only [List.length_cons, List.length_append, hs]
  omega

theorem growOne104_req_le_payload {c : ChainG} {k : Nat} {cap : BitVec 64}
    (hfull : (chainGAfter c k).keys.length = cap.toNat) :
    max (2 * cap.toNat) 4 * 104 ≤ 256 * (c.payload.length + 16) := by
  have hle := chainGAfter_keys_length_le_payload c k
  omega

theorem growOne104_req_le_mallocMax {cap : BitVec 64} (hbound : cap.toNat ≤ maxMessageKeys) :
    max (2 * cap.toNat) 4 * 104 ≤ MallocngMaxAllocSize := by
  unfold maxMessageKeys at hbound
  unfold MallocngMaxAllocSize
  omega

/-! ## VM-Preserving Straight-Line Segments for Tag-4 Head, Counter, and Seed -/

theorem step_c3hd_head_placed_vm [LibsignalPlacement] {ext : String → Option (State → State)}
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
      VmPreserved s s1 → s1.trace = s.trace →
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
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 515)
  intro m_strip
  unfold sliceCursorAt
  simp only [sepConj_assoc]
  iterate 6 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl1
  refine sepWPp_mono_pre_c3 ?_ (hnext _ (by simp only [wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) hcl1 hvm
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [wp_norm, arm64_norm])
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm]⟩)
  unfold sliceCursorAt
  exact sep_ac_seedChain (by ac_rfl)

theorem step_c3hd_key4_placed_vm [LibsignalPlacement] {ext : String → Option (State → State)}
    (A_rep : RustAlloc) (bufRef sp0 : BitVec 64)
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
      VmPreserved s s1 → s1.trace = s.trace →
      s1.readReg64 .lr = lsmpl.base 516 + 0x158#64 →
      s1.readReg64 .x0 = bufRef → Chain3MkRegs s s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1
        ((vecU8 A_rep (sp0 - 232#64) [] ∗ vecU8 A_rep (sp0 - 208#64) [] ∗
          vecU8 A_rep (sp0 - 184#64) [] ∗
          vecU8At A_rep (sp0 - 160#64) 0#64 1#64 [] ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
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
  rw [memRegion104_c3hd_split sp0, memRegion80_chainInit_eq_cells10_receiverChains sp0]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro c0
  apply SepWPp.exists_elim; intro c1
  apply SepWPp.exists_elim; intro c2
  apply SepWPp.exists_elim; intro c3
  apply SepWPp.exists_elim; intro c4
  apply SepWPp.exists_elim; intro c5
  apply SepWPp.exists_elim; intro c6
  apply SepWPp.exists_elim; intro c7
  apply SepWPp.exists_elim; intro c8
  apply SepWPp.exists_elim; intro c9
  apply SepWPp.exists_elim; intro c10
  apply SepWPp.exists_elim; intro c11
  apply SepWPp.exists_elim; intro wc
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 515) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 515)
  intro m_strip
  iterate 28 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl1
  refine sepWPp_mono_pre_c3 ?_ (hnext _ (by simp only [wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm]) (by simp only [hsp, wp_norm, arm64_norm]) hcl1 hvm
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [wp_norm, arm64_norm])
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm]⟩)
  refine Entails.trans
    (Q := (((sp0 - 232#64) ↦₆₄ 0#64) ∗ ((sp0 - 224#64) ↦₆₄ 1#64) ∗ ((sp0 - 216#64) ↦₆₄ 0#64) ∗
      ((sp0 - 208#64) ↦₆₄ 0#64) ∗ ((sp0 - 200#64) ↦₆₄ 1#64) ∗ ((sp0 - 192#64) ↦₆₄ 0#64) ∗
      ((sp0 - 184#64) ↦₆₄ 0#64) ∗ ((sp0 - 176#64) ↦₆₄ 1#64) ∗ ((sp0 - 168#64) ↦₆₄ 0#64) ∗
      ((sp0 - 160#64) ↦₆₄ 0#64) ∗ ((sp0 - 152#64) ↦₆₄ 1#64) ∗ ((sp0 - 144#64) ↦₆₄ 0#64)) ∗
      (((sp0 - 136#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 132#64) 4 ∗ F))
    (sep_ac_seedChain (by ac_rfl))
    (Entails.trans (sepConj_mono_left (@c3hd_default_of_cells A_rep sp0))
      (sep_ac_seedChain (by ac_rfl)))

theorem step_c3hd_len_placed_vm [LibsignalPlacement] {ext : String → Option (State → State)}
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
      VmPreserved s s1 → s1.trace = s.trace →
      s1.readReg64 .x25 = BitVec.ofNat 64 rest.length → Chain3MkRegs s s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1
        (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (body ++ rest)) ∗ F) Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (body ++ rest)) ∗ F) Q Qp := by
  have hlen_app : (body ++ rest).length = body.length + rest.length := List.length_append
  have hult := ult_ofNat_add_right_false_seedChain (m := body.length) (k := rest.length) (by omega)
  have hsub := bv_ofNat_add_sub_left_seedChain body.length rest.length
  change s.pc = (blkPl_516).base + 0x158#64 at hpc
  have h0 : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 body.length := hx1
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 516 + 0x244#64) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 516 + 0x244#64)
  intro m_strip
  unfold sliceCursorAt
  rw [hlen_app]
  simp only [sepConj_assoc]
  iterate 5 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl1
  refine sepWPp_mono_pre_c3 ?_ (hnext _ (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) hcl1 hvm
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm]⟩)
  unfold sliceCursorAt
  rw [hlen_app]
  exact sep_ac_seedChain (by ac_rfl)

theorem step_c3ihead_placed_vm [LibsignalPlacement] {ext : String → Option (State → State)}
    (bufRef slot ptr : BitVec 64) (b0 : BitVec 8) (rem1 rest : List (BitVec 8))
    (hlen_gt : rest.length < (b0 :: rem1).length) (hlen_lt : (b0 :: rem1).length < 2 ^ 62)
    {ret : BitVec 64} {s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 0x244#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = bufRef)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 rest.length)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 515 →
      s1.status = .Running → s1.sp = s.sp → LibsignalCodeLoaded lsmpl s1.mem →
      VmPreserved s s1 → s1.trace = s.trace →
      s1.readReg64 .lr = lsmpl.base 516 + 0x25c#64 →
      s1.readReg64 .x0 = bufRef → s1.readReg64 .x25 = BitVec.ofNat 64 rest.length →
      Chain3MkRegs s s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1
        (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (b0 :: rem1)) ∗ F) Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (b0 :: rem1)) ∗ F) Q Qp := by
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_lt
  change s.pc = (blkPl_516).base + 0x244#64 at hpc
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 rest.length := hx25
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 515) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 515)
  intro m_strip
  unfold sliceCursorAt
  simp only [sepConj_assoc]
  iterate 6 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl1
  refine sepWPp_mono_pre_c3 ?_ (hnext _ (by simp only [wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) hcl1 hvm
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [wp_norm, arm64_norm]) (by simp only [h25, wp_norm, arm64_norm])
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm]⟩)
  unfold sliceCursorAt
  exact sep_ac_seedChain (by ac_rfl)

theorem step_c3cnt_key_placed_vm [LibsignalPlacement] {ext : String → Option (State → State)}
    (bufRef : BitVec 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 0x25c#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx1 : s.readReg64 .x1 = 0x08#64)
    (hx19 : s.readReg64 .x19 = bufRef)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 515 →
      s1.status = .Running → s1.sp = s.sp → LibsignalCodeLoaded lsmpl s1.mem →
      VmPreserved s s1 → s1.trace = s.trace →
      s1.readReg64 .lr = lsmpl.base 516 + 0x308#64 →
      s1.readReg64 .x0 = bufRef → s1.readReg64 .x25 = s.readReg64 .x25 →
      Chain3MkRegs s s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1 P Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s P Q Qp := by
  change s.pc = (blkPl_516).base + 0x25c#64 at hpc
  have h0 : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s.readReg64 (Reg.gpr 1#5) = 0x08#64 := hx1
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 515) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 515)
  intro m_strip
  iterate 15 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl1
  exact hnext _ (by simp only [wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) hcl1 hvm
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm]⟩

theorem step_c3cnt_store_placed_vm [LibsignalPlacement] {ext : String → Option (State → State)}
    (sp0 v : BitVec 64) (w : BitVec 32)
    {ret : BitVec 64} {s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 0x308#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 0xf0#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx1 : s.readReg64 .x1 = v)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 516 + 0x244#64 →
      s1.status = .Running → s1.sp = s.sp → LibsignalCodeLoaded lsmpl s1.mem →
      VmPreserved s s1 → s1.trace = s.trace →
      s1.readReg64 .x25 = s.readReg64 .x25 → Chain3MkRegs s s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1
        (((sp0 - 136#64) ↦₃₂ v.setWidth 32) ∗ F) Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s (((sp0 - 136#64) ↦₃₂ w) ∗ F) Q Qp := by
  have hsp_align_bv : s.sp &&& 15#64 = 0#64 := hsp ▸ sp_sub_240_aligned_receiverChains halign
  change s.pc = (blkPl_516).base + 0x308#64 at hpc
  have h0 : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s.readReg64 (Reg.gpr 1#5) = v := hx1
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 516 + 0x244#64) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 516 + 0x244#64)
  intro m_strip
  iterate 6 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl1
  refine sepWPp_mono_pre_c3 ?_ (hnext _ (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) hcl1 hvm
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm]⟩)
  exact sep_ac_seedChain (by ac_rfl)

theorem step_c3seed_key_placed_vm [LibsignalPlacement] {ext : String → Option (State → State)}
    (bufRef sp0 : BitVec 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 0x25c#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx1 : s.readReg64 .x1 = 0x2a#64)
    (hx19 : s.readReg64 .x19 = bufRef)
    (hx22 : s.readReg64 .x22 = sp0 - 0xe8#64)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 514 →
      s1.status = .Running → s1.sp = s.sp → LibsignalCodeLoaded lsmpl s1.mem →
      VmPreserved s s1 → s1.trace = s.trace →
      s1.readReg64 .lr = lsmpl.base 516 + 0x2a8#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 → s1.readReg64 .x1 = sp0 - 160#64 →
      s1.readReg64 .x2 = bufRef →
      s1.readReg64 .x25 = s.readReg64 .x25 → Chain3MkRegs s s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1 P Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s P Q Qp := by
  change s.pc = (blkPl_516).base + 0x25c#64 at hpc
  have h0 : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s.readReg64 (Reg.gpr 1#5) = 0x2a#64 := hx1
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h22 : s.readReg64 (Reg.gpr 22#5) = sp0 - 0xe8#64 := hx22
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 514) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 514)
  intro m_strip
  iterate 19 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl1
  exact hnext _ (by simp only [wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) hcl1 hvm
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm]⟩

theorem step_c3seed_icont_placed_vm [LibsignalPlacement] {ext : String → Option (State → State)}
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 0x2a8#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 516 + 0x244#64 →
      s1.status = .Running → s1.sp = s.sp → LibsignalCodeLoaded lsmpl s1.mem →
      VmPreserved s s1 → s1.trace = s.trace →
      s1.readReg64 .x25 = s.readReg64 .x25 → Chain3MkRegs s s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1 P Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s P Q Qp := by
  change s.pc = (blkPl_516).base + 0x2a8#64 at hpc
  have h0 : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 516 + 0x244#64) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 516 + 0x244#64)
  intro m_strip
  iterate 3 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl1
  exact hnext _ (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) hcl1 hvm
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm]⟩

/-! ## Budget-Threaded Sub-Slice Steppers (`step_mkHead_cro`, `step_mkCnt_cro`, `step_mkSeed_cro`) -/

theorem c3_bm_call_vec1_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (v bufRef slot curPtr sp0 ret_pc : BitVec 64) (b rest : List (BitVec 8))
    (hb : b.length < 128)
    (hlen_lt : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 62)
    {st_cur : M.σ} {ret : BitVec 64} {s0 s : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfit : FitsEnv M lim st_cur (BoundedRustEvs 3 (2 * b.length + 8)))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 514) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : (s.readReg64 .x0).setWidth 8 = 2#8)
    (hx1 : s.readReg64 .x1 = v) (hx2 : s.readReg64 .x2 = bufRef)
    (hnext : ∀ (sm : State) (evs_bm : List AllocEvent),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → sm.readReg64 .x0 = 0#64 →
      BoundedRustEvs 3 (2 * b.length + 8) evs_bm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        ((vecU8 A.repAlloc v b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          A.pool lim (M.stepEvents evs_bm st_cur) sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      ((vecU8At A.repAlloc v 0#64 1#64 [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) ∗
        A.pool lim st_cur s ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q Qp := by
  refine c3_bm_call_cro hC v 1#64 bufRef slot curPtr sp0 ret_pc b rest hb hlen_lt hfit
    hcro hpc hrun hsp halign hcl htr hlr hx0 hx1 hx2 ?_
  intro sm cap' ptr' evs_bm hpcm hrunm hspm hclm htrm hcsm hx0m hevs_bm
  refine sepWPp_mono_pre_c3 ?_ (hnext sm evs_bm hpcm hrunm hspm hclm htrm hcsm hx0m hevs_bm)
  exact sepConj_mono_left (sepConj_mono_left
    (Entails.sepExists_right cap' (Entails.sepExists_right ptr' (Entails.refl _))))

theorem step_mkHead_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (bufRef slot ptr sp0 : BitVec 64) (body rest tail : List (BitVec 8))
    {st_cur : M.σ} {s0 s : State} {F : SepProp}
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
          vecU8 A.repAlloc (sp0 - 232#64) [] ∗ vecU8 A.repAlloc (sp0 - 208#64) [] ∗
          vecU8 A.repAlloc (sp0 - 184#64) [] ∗
          vecU8At A.repAlloc (sp0 - 160#64) 0#64 1#64 [] ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
          memRegion (sp0 - 132#64) 4 ∗
          (ptr ↦ₛ [0x22#8, BitVec.ofNat 8 body.length]) ∗
          sliceCursorAt slot (ptr + 2#64) (body ++ rest) ∗
          A.pool lim st_cur sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q (fun _ _ => False)) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ memRegion (sp0 - 232#64) 104 ∗
        sliceCursorAt slot ptr (0x22#8 :: BitVec.ofNat 8 body.length :: (body ++ rest)) ∗
        A.pool lim st_cur s ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q (fun _ _ => False) := by
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
  refine sepWPp_mono_pre_c3
    (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (0x22#8 :: rem1)) ∗
      (memRegion (sp0 - 232#64) 104 ∗ A.pool lim st_cur s ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX ∗ F))
    (sep_ac_seedChain (by ac_rfl)) ?_
  refine step_c3hd_head_placed_vm bufRef slot ptr 0x22#8 rem1 tail hlen_gt hlen_cons_lt
    hpc hrun hcl hx19 hx21 ?_
  intro s1 hpc1 hrun1 hsp1 hcl1 hvm1 htr1 hlr1 hx0_1 hregs1
  refine sepWPp_mono_pre_c3
    (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr ([0x22#8] ++ rem1) ∗
      A.pool lim st_cur s1 ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
      (memRegion (sp0 - 232#64) 104 ∗ F))
    (by rw [pool_eq_of_vm_c3 A lim st_cur hvm1]; exact sep_ac_seedChain (by ac_rfl)) ?_
  refine c3_dv_call_cro hC bufRef slot ptr sp0 (lsmpl.base 516 + 192#64) 0x22#64 [0x22#8] rem1
    rfl hlen_cons_lt hpc1 hrun1 (hsp1.trans hsp) halign hcl1 (htr1.trans htr) hlr1 hx0_1 ?_
  intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hcs2 hx0_2 hx1_2
  have hregs2 : Chain3MkRegs s s2 := hregs1.trans (.of_calleeSaved hcs2)
  refine sepWPp_mono_pre_c3
    (P' := memRegion (sp0 - 232#64) 104 ∗ ((bufRef ↦₆₄ slot) ∗ (ptr ↦ₛ [0x22#8]) ∗
      sliceCursorAt slot (ptr + 1#64) rem1 ∗ A.pool lim st_cur s2 ∗
      stackAt (sp0 - 240#64) chainMerge3SubStackX ∗ F))
    (sep_ac_seedChain (by ac_rfl)) ?_
  refine step_c3hd_key4_placed_vm A.repAlloc bufRef sp0 hpc2 hrun2 hsp2 halign hcl2 hx0_2 hx1_2
    (hregs2.1.trans hx19) (hregs2.2.2.2.1.trans hx22) (hregs2.2.2.2.2.1.trans hx23) ?_
  intro s3 hpc3 hrun3 hsp3 hcl3 hvm3 htr3 hlr3 hx0_3 hregs23
  have hregs3 : Chain3MkRegs s s3 := hregs2.trans hregs23
  refine sepWPp_mono_pre_c3
    (P' := ((bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot (ptr + 1#64) ([BitVec.ofNat 8 body.length] ++ (body ++ rest)) ∗
      A.pool lim st_cur s3 ∗
      stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
      (vecU8 A.repAlloc (sp0 - 232#64) [] ∗ vecU8 A.repAlloc (sp0 - 208#64) [] ∗
        vecU8 A.repAlloc (sp0 - 184#64) [] ∗
        vecU8At A.repAlloc (sp0 - 160#64) 0#64 1#64 [] ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
        memRegion (sp0 - 132#64) 4 ∗ (ptr ↦ₛ [0x22#8]) ∗ F))
    (by rw [pool_eq_of_vm_c3 A lim st_cur hvm3]; exact sep_ac_seedChain (by ac_rfl)) ?_
  refine c3_dv_call_cro hC bufRef slot (ptr + 1#64) sp0 (lsmpl.base 516 + 344#64)
    (BitVec.ofNat 64 body.length) [BitVec.ofNat 8 body.length] (body ++ rest)
    hdv_L hlen_rem1_lt hpc3 hrun3 hsp3 halign hcl3 (htr3.trans htr2) hlr3 hx0_3 ?_
  intro s4 hpc4 hrun4 hsp4 hcl4 htr4 hcs4 hx0_4 hx1_4
  have hregs4 : Chain3MkRegs s s4 := hregs3.trans (.of_calleeSaved hcs4)
  refine sepWPp_mono_pre_c3
    (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot (ptr + 2#64) (body ++ rest)) ∗
      (vecU8 A.repAlloc (sp0 - 232#64) [] ∗ vecU8 A.repAlloc (sp0 - 208#64) [] ∗
        vecU8 A.repAlloc (sp0 - 184#64) [] ∗
        vecU8At A.repAlloc (sp0 - 160#64) 0#64 1#64 [] ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
        memRegion (sp0 - 132#64) 4 ∗ (ptr ↦ₛ [0x22#8]) ∗
        ((ptr + 1#64) ↦ₛ [BitVec.ofNat 8 body.length]) ∗
        A.pool lim st_cur s4 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX ∗ F))
    (by dsimp only [List.length]; rw [c3hd_ptr_add_one_add_one ptr]; exact sep_ac_seedChain (by ac_rfl)) ?_
  refine step_c3hd_len_placed_vm bufRef slot (ptr + 2#64) body rest hlen_body_rest_lt
    hpc4 hrun4 hcl4 hx0_4 hx1_4 (hregs4.1.trans hx19) ?_
  intro s5 hpc5 hrun5 hsp5 hcl5 hvm5 htr5 hx25_5 hregs45
  refine sepWPp_mono_pre_c3 ?_
    (hnext s5 hpc5 hrun5 (hsp5.trans hsp4) hcl5 (htr5.trans htr4) hx25_5 (hregs4.trans hregs45))
  rw [pool_eq_of_vm_c3 A lim st_cur hvm5,
    ← c3hd_pointsTo_hdr_combine ptr (BitVec.ofNat 8 body.length)]
  exact sep_ac_seedChain (by ac_rfl)

theorem step_mkCnt_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (bufRef slot ptr sp0 : BitVec 64) (i : BitVec 32) (rest_mk rest : List (BitVec 8))
    {st_cur : M.σ} {s0 s : State} {F : SepProp}
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
          A.pool lim st_cur sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q (fun _ _ => False)) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
        sliceCursorAt slot ptr (pbVarint 1 i.toNat ++ (rest_mk ++ rest)) ∗
        A.pool lim st_cur s ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q (fun _ _ => False) := by
  by_cases hi0 : i = 0#32
  · subst hi0
    have hpb0 : pbVarint 1 (0#32).toNat = [] := rfl
    have hlen0 : BitVec.ofNat 64 ([] : List (BitVec 8)).length = 0#64 := rfl
    rw [hpb0, List.nil_append]
    refine sepWPp_mono_pre_c3 ?_ (hnext s hpc hrun hsp hcl htr hx25 (.refl s))
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
    dsimp only [chain3PCPlacedAtW] at hpc hnext
    rw [hcons_eq]
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (0x08#8 :: rem1)) ∗
        (((sp0 - 136#64) ↦₃₂ 0#32) ∗ A.pool lim st_cur s ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX ∗ F))
      (sep_ac_seedChain (by ac_rfl)) ?_
    refine step_c3ihead_placed_vm bufRef slot ptr 0x08#8 rem1 rest
      hlen_gt hlen_cons_lt hpc hrun hcl hx19 hx25 ?_
    intro s1 hpc1 hrun1 hsp1 hcl1 hvm1 htr1 hlr1 hx0_1 hx25_1 hregs1
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr ([0x08#8] ++ rem1) ∗
        A.pool lim st_cur s1 ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
        (((sp0 - 136#64) ↦₃₂ 0#32) ∗ F))
      (by rw [pool_eq_of_vm_c3 A lim st_cur hvm1]; exact sep_ac_seedChain (by ac_rfl)) ?_
    refine c3_dv_call_cro hC bufRef slot ptr sp0 (lsmpl.base 516 + 604#64)
      0x08#64 [0x08#8] rem1 rfl hlen_cons_lt hpc1 hrun1 (hsp1.trans hsp) halign hcl1
      (htr1.trans htr) hlr1 hx0_1 ?_
    intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hcs2 hx0_2 hx1_2
    have hregs2 : Chain3MkRegs s s2 := hregs1.trans (.of_calleeSaved hcs2)
    have hx25_2 : s2.readReg64 .x25 = BitVec.ofNat 64 rest.length :=
      hcs2.2.2.2.2.2.2.1.trans hx25_1
    refine step_c3cnt_key_placed_vm bufRef hpc2 hrun2 hcl2 hx0_2 hx1_2 (hregs2.1.trans hx19) ?_
    intro s3 hpc3 hrun3 hsp3 hcl3 hvm3 htr3 hlr3 hx0_3 hx25_3 hregs3
    have hregs3' : Chain3MkRegs s s3 := hregs2.trans hregs3
    have hx25_3' : s3.readReg64 .x25 = BitVec.ofNat 64 rest.length := hx25_3.trans hx25_2
    have hrem1_lt : (pbVarintBody 5 i.toNat ++ (rest_mk ++ rest)).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    have hdv2 : decodeVarint (pbVarintBody 5 i.toNat ++ (rest_mk ++ rest)) =
        some (i.zeroExtend 64, rest_mk ++ rest) := by
      rw [pbVarintBody_u32_eq_encodeVarint_seedChain i]
      exact decodeVarint_encodeVarint (i.zeroExtend 64) (rest_mk ++ rest)
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot (ptr + 1#64) (pbVarintBody 5 i.toNat ++ (rest_mk ++ rest)) ∗
        A.pool lim st_cur s3 ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
        ((ptr ↦ₛ [0x08#8]) ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗ F))
      (by
        rw [pool_eq_of_vm_c3 A lim st_cur hvm3,
          show BitVec.ofNat 64 ([0x08#8] : List (BitVec 8)).length = 1#64 from rfl]
        exact sep_ac_seedChain (by ac_rfl)) ?_
    refine c3_dv_call_cro hC bufRef slot (ptr + 1#64) sp0
      (lsmpl.base 516 + 776#64) (i.zeroExtend 64) (pbVarintBody 5 i.toNat) (rest_mk ++ rest)
      hdv2 hrem1_lt hpc3 hrun3 (hsp3.trans hsp2) halign hcl3 (htr3.trans htr2) hlr3 hx0_3 ?_
    intro s4 hpc4 hrun4 hsp4 hcl4 htr4 hcs4 hx0_4 hx1_4
    have hregs4 : Chain3MkRegs s s4 := hregs3'.trans (.of_calleeSaved hcs4)
    have hx25_4 : s4.readReg64 .x25 = BitVec.ofNat 64 rest.length :=
      hcs4.2.2.2.2.2.2.1.trans hx25_3'
    refine sepWPp_mono_pre_c3
      (P' := ((sp0 - 136#64) ↦₃₂ 0#32) ∗
        ((bufRef ↦₆₄ slot) ∗ (ptr ↦ₛ [0x08#8]) ∗ ((ptr + 1#64) ↦ₛ pbVarintBody 5 i.toNat) ∗
          sliceCursorAt slot (ptr + 1#64 + BitVec.ofNat 64 (pbVarintBody 5 i.toNat).length)
            (rest_mk ++ rest) ∗
          A.pool lim st_cur s4 ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX ∗ F))
      (sep_ac_seedChain (by ac_rfl)) ?_
    refine step_c3cnt_store_placed_vm sp0 (i.zeroExtend 64) 0#32
      hpc4 hrun4 hsp4 halign hcl4 hx0_4 hx1_4 ?_
    intro s5 hpc5 hrun5 hsp5 hcl5 hvm5 htr5 hx25_5 hregs5
    refine sepWPp_mono_pre_c3 ?_
      (hnext s5 hpc5 hrun5 (hsp5.trans hsp4) hcl5 (htr5.trans htr4)
        (hx25_5.trans hx25_4) (hregs4.trans hregs5))
    rw [pool_eq_of_vm_c3 A lim st_cur hvm5, c3cnt_zeroExtend64_setWidth32 i,
      pbVarint1_ptr_advance_seedChain ptr i.toNat hi_pos,
      ← c3cnt_pointsTo_08_combine ptr i.toNat hi_pos]
    exact sep_ac_seedChain (by ac_rfl)

theorem step_mkSeed_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (bufRef slot ptr sp0 : BitVec 64) (seed rest : List (BitVec 8))
    {st_cur : M.σ} {s0 s : State} {F : SepProp}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hseed_lt : seed.length < 128) (hlen_lt : (pbBytes 5 seed ++ rest).length < 2 ^ 62)
    (hfit : FitsEnv M lim st_cur (BoundedRustEvs 3 (2 * seed.length + 8)))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = chain3PCPlacedAtW ext 580#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = bufRef) (hx22 : s.readReg64 .x22 = sp0 - 232#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 rest.length)
    (hnext : ∀ (sm : State) (evs_bm : List AllocEvent),
      sm.pc = chain3PCPlacedAtW ext 580#64 → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace →
      sm.readReg64 .x25 = BitVec.ofNat 64 rest.length → Chain3MkRegs s sm →
      BoundedRustEvs 3 (2 * seed.length + 8) evs_bm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ vecU8 A.repAlloc (sp0 - 160#64) seed ∗ (ptr ↦ₛ pbBytes 5 seed) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 5 seed).length) rest ∗
          A.pool lim (M.stepEvents evs_bm st_cur) sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q (fun _ _ => False)) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ vecU8At A.repAlloc (sp0 - 160#64) 0#64 1#64 [] ∗
        sliceCursorAt slot ptr (pbBytes 5 seed ++ rest) ∗
        A.pool lim st_cur s ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q (fun _ _ => False) := by
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 seed.length] ++ seed ++ rest
  have hcons_eq : pbBytes 5 seed ++ rest = 0x2a#8 :: rem1 := by
    rw [CryptoVerification.E2E.Record.DeserializeSeed.pbBytes_lt128_eq_seedChain
      5 (by decide) seed hseed_lt]
    simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : rest.length < (0x2a#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x2a#8 :: rem1).length < 2 ^ 62 := by rw [← hcons_eq]; exact hlen_lt
  dsimp only [chain3PCPlacedAtW] at hpc hnext
  refine SepWPp.bind_lscro (mid := lsmpl.base 514)
    (Q1 := fun s3 P3 => s3.sp = sp0 - 240#64 ∧ LibsignalCodeLoaded lsmpl s3.mem ∧
      s3.trace = s0.trace ∧ s3.readReg64 .lr = lsmpl.base 516 + 680#64 ∧
      (s3.readReg64 .x0).setWidth 8 = 2#8 ∧ s3.readReg64 .x1 = sp0 - 160#64 ∧
      s3.readReg64 .x2 = bufRef ∧ s3.readReg64 .x25 = BitVec.ofNat 64 rest.length ∧
      Chain3MkRegs s s3 ∧
      (P3 ⊢ (vecU8At A.repAlloc (sp0 - 160#64) 0#64 1#64 [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot (ptr + 1#64) rem1 ∗
        A.pool lim st_cur s3 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ ((ptr ↦ₛ [0x2a#8]) ∗ F))) hcro ?_ ?_
  · rw [hcons_eq]
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (0x2a#8 :: rem1)) ∗
        (vecU8At A.repAlloc (sp0 - 160#64) 0#64 1#64 [] ∗ A.pool lim st_cur s ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX ∗ F))
      (sep_ac_seedChain (by ac_rfl)) ?_
    refine step_c3ihead_placed_vm bufRef slot ptr 0x2a#8 rem1 rest
      hlen_gt hlen_cons_lt hpc hrun hcl hx19 hx25 ?_
    intro s1 hpc1 hrun1 hsp1 hcl1 hvm1 htr1 hlr1 hx0_1 hx25_1 hregs1
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr ([0x2a#8] ++ rem1) ∗
        A.pool lim st_cur s1 ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
        (vecU8At A.repAlloc (sp0 - 160#64) 0#64 1#64 [] ∗ F))
      (by rw [pool_eq_of_vm_c3 A lim st_cur hvm1]; exact sep_ac_seedChain (by ac_rfl)) ?_
    refine c3_dv_call_cro hC bufRef slot ptr sp0 (lsmpl.base 516 + 604#64)
      0x2a#64 [0x2a#8] rem1 rfl hlen_cons_lt hpc1 hrun1 (hsp1.trans hsp) halign hcl1
      (htr1.trans htr) hlr1 hx0_1 ?_
    intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hcs2 hx0_2 hx1_2
    have hregs2 : Chain3MkRegs s s2 := hregs1.trans (.of_calleeSaved hcs2)
    have hx25_2 : s2.readReg64 .x25 = BitVec.ofNat 64 rest.length :=
      hcs2.2.2.2.2.2.2.1.trans hx25_1
    refine step_c3seed_key_placed_vm bufRef sp0 hpc2 hrun2 hcl2 hx0_2 hx1_2
      (hregs2.1.trans hx19) (hregs2.2.2.2.1.trans hx22) ?_
    intro s3 hpc3 hrun3 hsp3 hcl3 hvm3 htr3 hlr3 hx0_3 hx1_3 hx2_3 hx25_3 hregs3
    refine SepWPp.done hpc3 hrun3 ⟨hsp3.trans hsp2, hcl3, htr3.trans htr2, hlr3,
      hx0_3, hx1_3, hx2_3, hx25_3.trans hx25_2, hregs2.trans hregs3, ?_⟩
    rw [pool_eq_of_vm_c3 A lim st_cur hvm3,
      show BitVec.ofNat 64 ([0x2a#8] : List (BitVec 8)).length = 1#64 from rfl]
    exact sep_ac_seedChain (by ac_rfl)
  · intro s3 P3 hpc3 hrun3 hcro3 ⟨hsp3, hcl3, htr3, hlr3, hx0_3, hx1_3, hx2_3, hx25_3, hregs3, hent3⟩
    refine sepWPp_mono_pre_c3 hent3 ?_
    have hrem1_lt : ([BitVec.ofNat 8 seed.length] ++ seed ++ rest).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine c3_bm_call_vec1_cro hC (sp0 - 160#64) bufRef slot (ptr + 1#64) sp0
      (lsmpl.base 516 + 680#64) seed rest hseed_lt hrem1_lt hfit hcro3 hpc3 hrun3 hsp3 halign hcl3
      htr3 hlr3 hx0_3 hx1_3 hx2_3 ?_
    intro s4 evs_bm hpc4 hrun4 hsp4 hcl4 htr4 hcs4 hx0_4 hevs_bm
    have hregs4 : Chain3MkRegs s s4 := hregs3.trans (.of_calleeSaved hcs4)
    have hx25_4 : s4.readReg64 .x25 = BitVec.ofNat 64 rest.length :=
      hcs4.2.2.2.2.2.2.1.trans hx25_3
    refine step_c3seed_icont_placed_vm hpc4 hrun4 hcl4 hx0_4 ?_
    intro s5 hpc5 hrun5 hsp5 hcl5 hvm5 htr5 hx25_5 hregs5
    refine sepWPp_mono_pre_c3 ?_
      (hnext s5 evs_bm hpc5 hrun5 (hsp5.trans hsp4) hcl5 (htr5.trans htr4)
        (hx25_5.trans hx25_4) (hregs4.trans hregs5) hevs_bm)
    rw [pool_eq_of_vm_c3 A lim (M.stepEvents evs_bm st_cur) hvm5,
      CryptoVerification.E2E.Record.DeserializeSeed.pbBytes_ptr_advance_seedChain
        5 (by decide) ptr seed hseed_lt, ← c3seed_pointsTo_2a_combine ptr seed hseed_lt]
    exact sep_ac_seedChain (by ac_rfl)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroCPlacedBudgetAux
