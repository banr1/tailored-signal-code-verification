/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroAPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroBPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `VerNe.Chain3` (Block `516`) `bytes::merge` Helpers and `Srk` Slice

Pool-transport and `ChainPrefixEnv` stepping helpers, budget-threaded `bytes::merge [local#5]` call
wrappers, and total-correctness verification of the `Srk` (`tag = 1`, `tag = 2`) slice
(`chain3Srk_cro_placed_ok`) of `message::merge<Chain> [local#4]` (Block `516`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroBPlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalHooks LibsignalPlacement lsmpl
)
open CryptoVerification.RustHeap (RustAlloc vecU8 vecU8At)
open CryptoVerification.LibsignalProtoCodec (decodeVarint mergeBytes)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  BytesMergeCapOk BytesMergeGhost bytesMergeCapOk_zero sliceCursorAfter sliceCursorAt
)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded withLsCodeRoLoaded
)
open CryptoVerification.E2E.Record (pbBytes)
open CryptoVerification.E2E.Record.DeserializeSeed (
  mergeBytes_lt128_seedChain sep_ac_seedChain sliceCursorAfter_append_eq_seedChain
)
open Proofs.libsignal.Hooks2 (
  ule_ofNat_of_gt_false_seedChain62 ult_ofNat_of_gt_true_seedChain62
)
open CryptoVerification.E2E.Record.DeserializeGeneral (
  ChainField ChainG ChainMergeGenGhost chainGAfter
  pbBytes_lt128_eq_seedChain pbBytes_pointsTo_combine_seedChain pbBytes_ptr_advance_seedChain
)
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG (
  chainGAfter_succ chainG_enc_eq_fields_local curPtr curPtr_succ drop_flatMap_enc
  lenField_eq_pbBytes mem_fields_priv_length_lt mem_fields_srk_length_lt
  payload_append_eq_preBytes pointsToBytes_preBytes_succ preBytes sliceCursorAfter_eq_preBytes
)
open CryptoVerification.CliHandshake.Placed (blkLib_eq_516 blkPl_516 lsProg_516)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3 (
  Chain3LoopRegsPreserved SepWPp.of_sepWP_lscl_c3
  chain3GAt chain3PCPlacedAtW chain3SavedRegs chain3VecAt chain3VecAt_nil_elim
  chain3VecAt_of_ne_nil chainGRest chainMerge3SubStackX
  decodeVarint_0a_cons decodeVarint_12_cons libsignalCodeLoaded_preserve_c3
  sp0_aligned_of_sub_240_c3 stackAt_c3Sub_eq_bytesMerge
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (bytesMerge3Stack)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (BoundedRustEvs)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (BytesMergeEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsXBudget (
  ChainMergeGenEnv ChainPrefixEnv
  boundedRustEvs_bytesMergeEnv_of_some fitsEnv_bytesMerge_of_some fitsEnv_step_boundedRustEvs
  flatMap_take_length_le flatMap_take_succ_length
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefsBudget (
  bytesMerge3RawSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroAPlacedBudgetAux (
  Chain3LoopPlacedAtW chainMerge3PlacedSpecW sepWPp_mono_pre_c3
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroAPlacedBudget (
  Chain3CalleesCroPlacedW Chain3SrkCroStmt SepWPp.bind_lscro
  c3_dv_call_cro intro_withLsCodeRoLoaded_c3 segStepG_keep_cro sp_sub_240_aligned_c3_cro
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

/-! ## Pool Transport, `SepWPp` Focus, and `ChainPrefixEnv` Helpers -/

theorem pool_eq_of_vm_c3 {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st_cur : M.σ) {s sm : State} (hvm : VmPreserved s sm) :
    A.pool lim st_cur s = A.pool lim st_cur sm :=
  (congrArg CryptoVerification.RustHeap.RustAlloc.pool
    (A.atState_eq_of_vmPreserved lim st_cur hvm)).symm

theorem sepWPp_focus_pre_false_c3 {prog : Program} {ret : BitVec 64} {s : State}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (h : SepWPp prog ret s P
      (fun sm Pm => SepWPp prog ret sm (Pm ∗ F) Q (fun _ _ => False))
      (fun _ _ => False)) :
    SepWPp prog ret s (P ∗ F) Q (fun _ _ => False) := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨sm, hst1, ⟨_, _, Pm, hmm, hcont⟩ | ⟨_, _, _, hf⟩ | ⟨_, hoom⟩⟩ := h (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmm
    obtain ⟨sf, hst2, hout⟩ := hcont R hmm (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hout⟩
  · exact hf.elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem chainPrefixEnv_enc_le_payload {c : ChainG} {k : Nat} (hk : k < c.fields.length) :
    ((c.fields.take k).flatMap ChainField.enc).length + (c.fields[k]'hk).enc.length ≤
      c.payload.length := by
  have h1 := flatMap_take_succ_length ChainField.enc c.fields hk
  have h2 := flatMap_take_length_le ChainField.enc c.fields (k + 1)
  have h3 : (c.fields.flatMap ChainField.enc).length = c.enc.length := by
    rw [← chainG_enc_eq_fields_local c]
  unfold ChainG.payload
  rw [List.length_append]
  omega

theorem fitsEnv_rem_at_field {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {x : ChainMergeGenGhost} {k : Nat} (hk : k < x.c.fields.length)
    {evs : List AllocEvent}
    (hevs : ChainPrefixEnv x.c k evs)
    (hFit : FitsEnv M lim st (ChainMergeGenEnv x)) :
    FitsEnv M lim (M.stepEvents evs st)
      (BoundedRustEvs (8 * (x.c.fields[k]'hk).enc.length)
        (256 * (x.c.payload.length + 16))) := by
  unfold ChainPrefixEnv at hevs
  unfold ChainMergeGenEnv at hFit
  have hle := chainPrefixEnv_enc_le_payload hk
  exact fitsEnv_step_boundedRustEvs hevs (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit

theorem chainPrefixEnv_step_field {c : ChainG} {k : Nat} (hk : k < c.fields.length)
    {evs evs_step : List AllocEvent}
    (hevs : ChainPrefixEnv c k evs)
    (hstep : BoundedRustEvs (8 * (c.fields[k]'hk).enc.length)
      (256 * (c.payload.length + 16)) evs_step) :
    ChainPrefixEnv c (k + 1) (evs ++ evs_step) := by
  unfold ChainPrefixEnv at hevs ⊢
  have h1 := flatMap_take_succ_length ChainField.enc c.fields hk
  have happ := BoundedRustEvs.append hevs hstep
  rw [Nat.max_self] at happ
  exact BoundedRustEvs.mono (by omega) (Nat.le_refl _) happ

theorem chain3GAt_apply_srk_c3 (A_rep : RustAlloc) (a : BitVec 64) (c : ChainG)
    (b : List (BitVec 8)) :
    chain3GAt A_rep a (c.apply (.srk b)) =
      chain3VecAt A_rep a b ∗ chain3VecAt A_rep (a + 24#64) c.priv ∗ chainGRest A_rep a c :=
  rfl

theorem chain3GAt_apply_priv_c3 (A_rep : RustAlloc) (a : BitVec 64) (c : ChainG)
    (b : List (BitVec 8)) :
    chain3GAt A_rep a (c.apply (.priv b)) =
      chain3VecAt A_rep a c.srk ∗ chain3VecAt A_rep (a + 24#64) b ∗ chainGRest A_rep a c :=
  rfl

/-! ## Budget-Threaded `bytes::merge [local#5]` and `decode_varint` Call Helpers -/

theorem c3_bm_call_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (v ptr0 bufRef slot curPtr sp0 ret_pc : BitVec 64) (b rest : List (BitVec 8))
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
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs_bm : List AllocEvent),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → sm.readReg64 .x0 = 0#64 →
      BoundedRustEvs 3 (2 * b.length + 8) evs_bm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        ((vecU8At A.repAlloc v cap' ptr' b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          A.pool lim (M.stepEvents evs_bm st_cur) sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      ((vecU8At A.repAlloc v 0#64 ptr0 [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) ∗
        A.pool lim st_cur s ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q Qp := by
  have hlen_lt63 : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 63 := by omega
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_240_aligned_c3_cro halign
  let gbm : BytesMergeGhost :=
    ⟨.lengthDelimited, v, 0#64, ptr0, [], bufRef, slot, curPtr,
      [BitVec.ofNat 8 b.length] ++ b ++ rest⟩
  have hmB : mergeBytes gbm.wt gbm.bs = some (b, rest) :=
    mergeBytes_lt128_seedChain b rest hb
  have hb_max : 2 * b.length + 8 ≤ MallocngMaxAllocSize := by
    unfold MallocngMaxAllocSize; omega
  have hfit_bm : FitsEnv M lim st_cur (BytesMergeEnv gbm) :=
    fitsEnv_bytesMerge_of_some hmB hb_max (Nat.le_refl 3) (Nat.le_refl _) hfit
  intro R' hm hL
  have hm_call : s.mem ⊨
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)).pre (gbm, st_cur) s ∗ (F ∗ R') := by
    refine intro_withLsCodeRoLoaded_c3 hcro ?_
    rw [stackAt_c3Sub_eq_bytesMerge (sp0 - 240#64)] at hm
    unfold bytesMerge3RawSpec; dsimp only [gbm]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen_lt63, bytesMergeCapOk_zero, hfit_bm⟩, ?_⟩
    exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hm
  obtain ⟨sm, hst1,
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hm_post⟩ | ⟨_, hm_pan⟩ | ⟨_, _, hm_ex⟩ | ⟨_, hm_oom⟩, _⟩ :=
    (hC.bm).no_fault_before_outcome (gbm, st_cur) (F ∗ R') s hpc hrun hm_call hsp_aligned hL
  · rw [hlr] at hpcm
    rw [hsp] at hspm
    have hclm : LibsignalCodeLoaded lsmpl sm.mem := libsignalCodeLoaded_preserve_c3 hcl hst1
    dsimp only [withLsCodeRoLoaded, bytesMerge3RawSpec] at hm_post
    rw [hmB, hsp] at hm_post
    dsimp only [gbm] at hm_post
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_post
    rcases hm_post with ⟨cap', ptr', evs_bm, hm_post⟩
    have hm_pure : sm.mem ⊨
        ⌜sm.trace = s.trace⌝ ∗
        (⌜BytesMergeEnv gbm evs_bm⌝ ∗
          (⌜sm.readReg64 .x0 = 0#64⌝ ∗
            (⌜BytesMergeCapOk cap' rest.length⌝ ∗
              ((vecU8At A.repAlloc v cap' ptr' b ∗ (bufRef ↦₆₄ slot) ∗
                sliceCursorAfter slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) rest ∗
                A.pool lim (M.stepEvents evs_bm st_cur) sm ∗
                stackAt (sp0 - 240#64) bytesMerge3Stack ∗ F) ∗ R')))) :=
      Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hm_post
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj,
      satisfies_pure_sepConj, satisfies_pure_sepConj] at hm_pure
    rcases hm_pure with ⟨htrm, hevs_bm, hx0m, _hcapOk, hm_rest⟩
    have hbnd_bm : BoundedRustEvs 3 (2 * b.length + 8) evs_bm :=
      boundedRustEvs_bytesMergeEnv_of_some hmB hb_max hevs_bm
    have hcur := sliceCursorAfter_append_eq_seedChain slot curPtr ([BitVec.ofNat 8 b.length] ++ b) rest
    rw [show ([BitVec.ofNat 8 b.length] ++ b).length = b.length + 1 by simp] at hcur
    rw [hcur, ← stackAt_c3Sub_eq_bytesMerge (sp0 - 240#64)] at hm_rest
    have hm_next : sm.mem ⊨
        ((vecU8At A.repAlloc v cap' ptr' b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          A.pool lim (M.stepEvents evs_bm st_cur) sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F) ∗ R' :=
      Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hm_rest
    obtain ⟨sf, hst2, hout2⟩ :=
      hnext sm cap' ptr' evs_bm hpcm hrunm hspm hclm (htrm.trans htr) hcsm hx0m hbnd_bm
        R' hm_next (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hout2⟩
  · dsimp only [withLsCodeRoLoaded, bytesMerge3RawSpec] at hm_pan
    exact False.elim (not_satisfies_false_sepConj hm_pan)
  · exact False.elim (not_satisfies_false_sepConj hm_ex)
  · exact False.elim (not_satisfies_false_sepConj hm_oom)

theorem c3_bm_call_srk_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (v bufRef slot curPtr sp0 ret_pc : BitVec 64) (b rest : List (BitVec 8))
    (hb : b.length < 128) (hb_ne : b ≠ [])
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
        ((chain3VecAt A.repAlloc v b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          A.pool lim (M.stepEvents evs_bm st_cur) sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      ((chain3VecAt A.repAlloc v [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) ∗
        A.pool lim st_cur s ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q Qp := by
  refine sepWPp_mono_pre_c3
    (sepConj_mono_left (sepConj_mono_left (chain3VecAt_nil_elim A.repAlloc v))) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun ptr0 => ?_
  refine c3_bm_call_cro hC v ptr0 bufRef slot curPtr sp0 ret_pc b rest hb hlen_lt
    hfit hcro hpc hrun hsp halign hcl htr hlr hx0 hx1 hx2 ?_
  intro sm cap' ptr' evs_bm hpcm hrunm hspm hclm htrm hcsm hx0m hbnd_bm
  refine sepWPp_mono_pre_c3 ?_ (hnext sm evs_bm hpcm hrunm hspm hclm htrm hcsm hx0m hbnd_bm)
  exact sepConj_mono_left (sepConj_mono_left (chain3VecAt_of_ne_nil A.repAlloc v cap' ptr' hb_ne))

theorem c3_bm_call_vec_cro [LibsignalPlacement] {M : AllocCostModel}
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
      ((chain3VecAt A.repAlloc v [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) ∗
        A.pool lim st_cur s ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q Qp := by
  refine sepWPp_mono_pre_c3
    (sepConj_mono_left (sepConj_mono_left (chain3VecAt_nil_elim A.repAlloc v))) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun ptr0 => ?_
  refine c3_bm_call_cro hC v ptr0 bufRef slot curPtr sp0 ret_pc b rest hb hlen_lt
    hfit hcro hpc hrun hsp halign hcl htr hlr hx0 hx1 hx2 ?_
  intro sm cap' ptr' evs_bm hpcm hrunm hspm hclm htrm hcsm hx0m hbnd_bm
  refine sepWPp_mono_pre_c3 ?_ (hnext sm evs_bm hpcm hrunm hspm hclm htrm hcsm hx0m hbnd_bm)
  exact sepConj_mono_left (sepConj_mono_left
    (Entails.sepExists_right cap' (Entails.sepExists_right ptr' (Entails.refl _))))

theorem c3a_dv_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (bufRef slot curPtr sp0 ret_pc v : BitVec 64) (b0 : BitVec 8) (rem1 : List (BitVec 8))
    (hdv : decodeVarint (b0 :: rem1) = some (v, rem1))
    (hlen_lt : (b0 :: rem1).length < 2 ^ 62)
    {st_cur : M.σ} {ret : BitVec 64} {s_init s : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
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
          A.pool lim st_cur sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot curPtr (b0 :: rem1) ∗
        A.pool lim st_cur s ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q Qp := by
  refine c3_dv_call_cro hC bufRef slot curPtr sp0 ret_pc v [b0] rem1 hdv hlen_lt
    hpc hrun hsp halign hcl htr hlr hx0 ?_
  intro sm hpcm hrunm hspm hclm htrm hcsm hx0m hx1m
  refine sepWPp_mono_pre_c3 ?_ (hnext sm hpcm hrunm hspm hclm htrm hcsm hx0m hx1m)
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, List.length_singleton]
  exact Entails.refl _

/-! ## VM-Preserving `Srk` Steppers and `chain3Srk_cro_placed_ok` (`tag = 1`, `tag = 2`) -/

theorem c3_outer_head_vm [LibsignalPlacement] {ext : String → Option (State → State)}
    (bufRef slot ptr sp0 : BitVec 64) (bs : List (BitVec 8)) (outer : Nat)
    (hgt : outer < bs.length) (hlen : bs.length < 2 ^ 62)
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = lsmpl.base 516 + 168#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 240#64)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx21 : s0.readReg64 .x21 = BitVec.ofNat 64 outer)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 515 → s1.status = .Running → s1.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl s1.mem → VmPreserved s0 s1 → s1.trace = s_init.trace →
      s1.readReg64 .lr = lsmpl.base 516 + 192#64 → s1.readReg64 .x0 = bufRef →
      Chain3LoopRegsPreserved s0 s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1
        (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr bs ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F) Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s0
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr bs ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F) Q Qp := by
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hgt hlen
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hgt hlen
  change s0.pc = (blkPl_516).base + 168#64 at hpc
  have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h21 : s0.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 outer := hx21
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 515) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 515)
  intro m_strip
  unfold sliceCursorAt
  simp only [sepConj_assoc]
  iterate 6 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s0 _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl1
  refine sepWPp_mono_pre_c3 ?_ (hnext _ (by simp only [wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm]) (by simp only [hsp, wp_norm, arm64_norm])
    hcl1 hvm (by simp only [htr, wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]; rfl) (by simp only [wp_norm, arm64_norm])
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm]⟩)
  unfold sliceCursorAt
  exact sep_ac_seedChain (by ac_rfl)

private theorem c3_tag1_dispatch_vm [LibsignalPlacement] {ext : String → Option (State → State)}
    (a bufRef sp0 : BitVec 64)
    {ret : BitVec 64} {s_init s2 : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s2.pc = lsmpl.base 516 + 192#64) (hrun : s2.status = .Running)
    (hsp : s2.sp = sp0 - 240#64) (hcl : LibsignalCodeLoaded lsmpl s2.mem)
    (htr : s2.trace = s_init.trace) (hx0 : s2.readReg64 .x0 = 0#64)
    (hx1 : s2.readReg64 .x1 = 0x0a#64) (hx19 : s2.readReg64 .x19 = bufRef)
    (hx20 : s2.readReg64 .x20 = a)
    (hnext : ∀ (s3 : State),
      s3.pc = lsmpl.base 514 → s3.status = .Running → s3.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl s3.mem → VmPreserved s2 s3 → s3.trace = s_init.trace →
      s3.readReg64 .lr = lsmpl.base 516 + 496#64 →
      (s3.readReg64 .x0).setWidth 8 = 2#8 → s3.readReg64 .x1 = a → s3.readReg64 .x2 = bufRef →
      Chain3LoopRegsPreserved s2 s3 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s3 P Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s2 P Q Qp := by
  change s2.pc = (blkPl_516).base + 192#64 at hpc
  have h0 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s2.readReg64 (Reg.gpr 1#5) = 0x0a#64 := hx1
  have h19 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s2.readReg64 (Reg.gpr 20#5) = a := hx20
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 514) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 514)
  intro m_strip
  iterate 18 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s2 _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl3
  exact hnext _ (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm])
    (by simp only [hsp, wp_norm, arm64_norm]) hcl3 hvm (by simp only [htr, wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]; rfl) (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm]⟩

private theorem c3_tag1_ret_vm [LibsignalPlacement] {ext : String → Option (State → State)}
    (sp0 : BitVec 64) {ret : BitVec 64} {s_init s4 : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s4.pc = lsmpl.base 516 + 496#64) (hrun : s4.status = .Running)
    (hsp : s4.sp = sp0 - 240#64) (hcl : LibsignalCodeLoaded lsmpl s4.mem)
    (htr : s4.trace = s_init.trace) (hx0 : s4.readReg64 .x0 = 0#64)
    (hnext : ∀ (s5 : State),
      s5.pc = lsmpl.base 516 + 168#64 → s5.status = .Running → s5.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl s5.mem → VmPreserved s4 s5 → s5.trace = s_init.trace →
      Chain3LoopRegsPreserved s4 s5 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s5 P Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s4 P Q Qp := by
  change s4.pc = (blkPl_516).base + 496#64 at hpc
  have h0 : s4.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 516 + 168#64) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 516 + 168#64)
  intro m_strip
  iterate 2 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s4 _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl5
  exact hnext _ (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) (by simp only [hsp, wp_norm, arm64_norm])
    hcl5 hvm (by simp only [htr, wp_norm, arm64_norm])
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm]⟩

private theorem c3_tag2_dispatch_vm [LibsignalPlacement] {ext : String → Option (State → State)}
    (a bufRef sp0 : BitVec 64)
    {ret : BitVec 64} {s_init s2 : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s2.pc = lsmpl.base 516 + 192#64) (hrun : s2.status = .Running)
    (hsp : s2.sp = sp0 - 240#64) (hcl : LibsignalCodeLoaded lsmpl s2.mem)
    (htr : s2.trace = s_init.trace) (hx0 : s2.readReg64 .x0 = 0#64)
    (hx1 : s2.readReg64 .x1 = 0x12#64) (hx19 : s2.readReg64 .x19 = bufRef)
    (hx20 : s2.readReg64 .x20 = a)
    (hnext : ∀ (s3 : State),
      s3.pc = lsmpl.base 514 → s3.status = .Running → s3.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl s3.mem → VmPreserved s2 s3 → s3.trace = s_init.trace →
      s3.readReg64 .lr = lsmpl.base 516 + 272#64 →
      (s3.readReg64 .x0).setWidth 8 = 2#8 →
      s3.readReg64 .x1 = a + 24#64 → s3.readReg64 .x2 = bufRef →
      Chain3LoopRegsPreserved s2 s3 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s3 P Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s2 P Q Qp := by
  change s2.pc = (blkPl_516).base + 192#64 at hpc
  have h0 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s2.readReg64 (Reg.gpr 1#5) = 0x12#64 := hx1
  have h19 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s2.readReg64 (Reg.gpr 20#5) = a := hx20
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 514) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 514)
  intro m_strip
  iterate 20 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s2 _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl3
  exact hnext _ (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm])
    (by simp only [hsp, wp_norm, arm64_norm]) hcl3 hvm (by simp only [htr, wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]; rfl) (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm]⟩

private theorem c3_tag2_ret_vm [LibsignalPlacement] {ext : String → Option (State → State)}
    (sp0 : BitVec 64) {ret : BitVec 64} {s_init s4 : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s4.pc = lsmpl.base 516 + 272#64) (hrun : s4.status = .Running)
    (hsp : s4.sp = sp0 - 240#64) (hcl : LibsignalCodeLoaded lsmpl s4.mem)
    (htr : s4.trace = s_init.trace) (hx0 : s4.readReg64 .x0 = 0#64)
    (hnext : ∀ (s5 : State),
      s5.pc = lsmpl.base 516 + 168#64 → s5.status = .Running → s5.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl s5.mem → VmPreserved s4 s5 → s5.trace = s_init.trace →
      Chain3LoopRegsPreserved s4 s5 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s5 P Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s4 P Q Qp := by
  change s4.pc = (blkPl_516).base + 272#64 at hpc
  have h0 : s4.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 516 + 168#64) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 516 + 168#64)
  intro m_strip
  iterate 2 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s4 _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl5
  exact hnext _ (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) (by simp only [hsp, wp_norm, arm64_norm])
    hcl5 hvm (by simp only [htr, wp_norm, arm64_norm])
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm]⟩

theorem step_chain3Tag1_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (a bufRef slot ptr sp0 : BitVec 64) (srk rest tail : List (BitVec 8))
    (hsrk_lt : srk.length < 128) (hsrk_ne : srk ≠ [])
    (hlen_lt : (pbBytes 1 srk ++ rest ++ tail).length < 2 ^ 62)
    {st_cur : M.σ} {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfit : FitsEnv M lim st_cur (BoundedRustEvs 3 (2 * srk.length + 8)))
    (hcro : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hpc : s0.pc = lsmpl.base 516 + 168#64) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (htr : s0.trace = s_init.trace)
    (hx19 : s0.readReg64 .x19 = bufRef) (hx20 : s0.readReg64 .x20 = a)
    (hx21 : s0.readReg64 .x21 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State) (evs_bm : List AllocEvent),
      sm.pc = lsmpl.base 516 + 168#64 → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s_init.trace →
      Chain3LoopRegsPreserved s0 sm →
      BoundedRustEvs 3 (2 * srk.length + 8) evs_bm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ chain3VecAt A.repAlloc a srk ∗ (ptr ↦ₛ pbBytes 1 srk) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 1 srk).length) (rest ++ tail) ∗
          A.pool lim (M.stepEvents evs_bm st_cur) sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s0
      (((bufRef ↦₆₄ slot) ∗ chain3VecAt A.repAlloc a [] ∗
        sliceCursorAt slot ptr (pbBytes 1 srk ++ (rest ++ tail)) ∗
        A.pool lim st_cur s0 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q Qp := by
  have hpb : pbBytes 1 srk = 0x0a#8 :: BitVec.ofNat 8 srk.length :: srk :=
    pbBytes_lt128_eq_seedChain 1 (by decide) srk hsrk_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 srk.length] ++ srk ++ (rest ++ tail)
  have hcons_eq : pbBytes 1 srk ++ (rest ++ tail) = 0x0a#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : tail.length < (0x0a#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x0a#8 :: rem1).length < 2 ^ 62 := by
    rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
  refine SepWPp.bind_lscro (mid := lsmpl.base 514)
    (Q1 := fun s3 P3 => s3.sp = sp0 - 240#64 ∧ LibsignalCodeLoaded lsmpl s3.mem ∧
      s3.trace = s_init.trace ∧ s3.readReg64 .lr = lsmpl.base 516 + 496#64 ∧
      (s3.readReg64 .x0).setWidth 8 = 2#8 ∧ s3.readReg64 .x1 = a ∧ s3.readReg64 .x2 = bufRef ∧
      Chain3LoopRegsPreserved s0 s3 ∧
      (P3 ⊢ (chain3VecAt A.repAlloc a [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot (ptr + 1#64) rem1 ∗
        A.pool lim st_cur s3 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ ((ptr ↦₈ 0x0a#8) ∗ F))) hcro ?_ ?_
  · rw [hcons_eq]
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (0x0a#8 :: rem1) ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
        (chain3VecAt A.repAlloc a [] ∗ A.pool lim st_cur s0 ∗ F))
      (sep_ac_seedChain (by ac_rfl)) ?_
    refine c3_outer_head_vm bufRef slot ptr sp0 (0x0a#8 :: rem1) tail.length hlen_gt hlen_cons_lt
      hpc hrun hsp hcl htr hx19 hx21 ?_
    intro s1 hpc1 hrun1 hsp1 hcl1 hvm1 htr1 hlr1 hx0_1 hregs1
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (0x0a#8 :: rem1) ∗
        A.pool lim st_cur s1 ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
        (chain3VecAt A.repAlloc a [] ∗ F))
      (by rw [pool_eq_of_vm_c3 A lim st_cur hvm1]; exact sep_ac_seedChain (by ac_rfl)) ?_
    refine c3a_dv_cro hC bufRef slot ptr sp0 (lsmpl.base 516 + 192#64) 0x0a#64 0x0a#8 rem1
      (decodeVarint_0a_cons rem1) hlen_cons_lt hpc1 hrun1 hsp1 halign hcl1 htr1 hlr1 hx0_1 ?_
    intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hcs2 hx0_2 hx1_2
    have hregs2 : Chain3LoopRegsPreserved s0 s2 := hregs1.trans (.of_calleeSaved hcs2)
    refine c3_tag1_dispatch_vm a bufRef sp0 hpc2 hrun2 hsp2 hcl2 htr2 hx0_2 hx1_2
      (hregs2.1.trans hx19) (hregs2.2.1.trans hx20) ?_
    intro s3 hpc3 hrun3 hsp3 hcl3 hvm3 htr3 hlr3 hx0_3 hx1_3 hx2_3 hregs3'
    refine SepWPp.done hpc3 hrun3
      ⟨hsp3, hcl3, htr3, hlr3, hx0_3, hx1_3, hx2_3, hregs2.trans hregs3', ?_⟩
    rw [pool_eq_of_vm_c3 A lim st_cur hvm3]
    exact sep_ac_seedChain (by ac_rfl)
  · intro s3 P3 hpc3 hrun3 hcro3 ⟨hsp3, hcl3, htr3, hlr3, hx0_3, hx1_3, hx2_3, hregs3, hent3⟩
    refine sepWPp_mono_pre_c3 hent3 ?_
    have hrem1_lt : ([BitVec.ofNat 8 srk.length] ++ srk ++ (rest ++ tail)).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine c3_bm_call_srk_cro hC a bufRef slot (ptr + 1#64) sp0 (lsmpl.base 516 + 496#64)
      srk (rest ++ tail) hsrk_lt hsrk_ne hrem1_lt hfit hcro3 hpc3 hrun3 hsp3 halign hcl3 htr3
      hlr3 hx0_3 hx1_3 hx2_3 ?_
    intro s4 evs_bm hpc4 hrun4 hsp4 hcl4 htr4 hcs4 hx0_4 hbnd_bm
    have hregs4 : Chain3LoopRegsPreserved s0 s4 := hregs3.trans (.of_calleeSaved hcs4)
    refine c3_tag1_ret_vm sp0 hpc4 hrun4 hsp4 hcl4 htr4 hx0_4 ?_
    intro s5 hpc5 hrun5 hsp5 hcl5 hvm5 htr5 hregs5'
    refine sepWPp_mono_pre_c3 ?_
      (hnext s5 evs_bm hpc5 hrun5 hsp5 hcl5 htr5 (hregs4.trans hregs5') hbnd_bm)
    rw [pool_eq_of_vm_c3 A lim (M.stepEvents evs_bm st_cur) hvm5,
      pbBytes_ptr_advance_seedChain 1 (by decide) ptr srk hsrk_lt,
      ← pbBytes_pointsTo_combine_seedChain 1 (by decide) ptr srk hsrk_lt]
    exact sep_ac_seedChain (by ac_rfl)

theorem step_chain3Tag2_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (a bufRef slot ptr sp0 : BitVec 64) (priv rest tail : List (BitVec 8))
    (hpriv_lt : priv.length < 128) (hpriv_ne : priv ≠ [])
    (hlen_lt : (pbBytes 2 priv ++ rest ++ tail).length < 2 ^ 62)
    {st_cur : M.σ} {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfit : FitsEnv M lim st_cur (BoundedRustEvs 3 (2 * priv.length + 8)))
    (hcro : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hpc : s0.pc = lsmpl.base 516 + 168#64) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (htr : s0.trace = s_init.trace)
    (hx19 : s0.readReg64 .x19 = bufRef) (hx20 : s0.readReg64 .x20 = a)
    (hx21 : s0.readReg64 .x21 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State) (evs_bm : List AllocEvent),
      sm.pc = lsmpl.base 516 + 168#64 → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s_init.trace →
      Chain3LoopRegsPreserved s0 sm →
      BoundedRustEvs 3 (2 * priv.length + 8) evs_bm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ chain3VecAt A.repAlloc (a + 24#64) priv ∗
          (ptr ↦ₛ pbBytes 2 priv) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 2 priv).length) (rest ++ tail) ∗
          A.pool lim (M.stepEvents evs_bm st_cur) sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s0
      (((bufRef ↦₆₄ slot) ∗ chain3VecAt A.repAlloc (a + 24#64) [] ∗
        sliceCursorAt slot ptr (pbBytes 2 priv ++ (rest ++ tail)) ∗
        A.pool lim st_cur s0 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q Qp := by
  have hpb : pbBytes 2 priv = 0x12#8 :: BitVec.ofNat 8 priv.length :: priv :=
    pbBytes_lt128_eq_seedChain 2 (by decide) priv hpriv_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 priv.length] ++ priv ++ (rest ++ tail)
  have hcons_eq : pbBytes 2 priv ++ (rest ++ tail) = 0x12#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : tail.length < (0x12#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x12#8 :: rem1).length < 2 ^ 62 := by
    rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
  refine SepWPp.bind_lscro (mid := lsmpl.base 514)
    (Q1 := fun s3 P3 => s3.sp = sp0 - 240#64 ∧ LibsignalCodeLoaded lsmpl s3.mem ∧
      s3.trace = s_init.trace ∧ s3.readReg64 .lr = lsmpl.base 516 + 272#64 ∧
      (s3.readReg64 .x0).setWidth 8 = 2#8 ∧ s3.readReg64 .x1 = a + 24#64 ∧
      s3.readReg64 .x2 = bufRef ∧ Chain3LoopRegsPreserved s0 s3 ∧
      (P3 ⊢ (chain3VecAt A.repAlloc (a + 24#64) [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot (ptr + 1#64) rem1 ∗
        A.pool lim st_cur s3 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ ((ptr ↦₈ 0x12#8) ∗ F))) hcro ?_ ?_
  · rw [hcons_eq]
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (0x12#8 :: rem1) ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
        (chain3VecAt A.repAlloc (a + 24#64) [] ∗ A.pool lim st_cur s0 ∗ F))
      (sep_ac_seedChain (by ac_rfl)) ?_
    refine c3_outer_head_vm bufRef slot ptr sp0 (0x12#8 :: rem1) tail.length hlen_gt hlen_cons_lt
      hpc hrun hsp hcl htr hx19 hx21 ?_
    intro s1 hpc1 hrun1 hsp1 hcl1 hvm1 htr1 hlr1 hx0_1 hregs1
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (0x12#8 :: rem1) ∗
        A.pool lim st_cur s1 ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
        (chain3VecAt A.repAlloc (a + 24#64) [] ∗ F))
      (by rw [pool_eq_of_vm_c3 A lim st_cur hvm1]; exact sep_ac_seedChain (by ac_rfl)) ?_
    refine c3a_dv_cro hC bufRef slot ptr sp0 (lsmpl.base 516 + 192#64) 0x12#64 0x12#8 rem1
      (decodeVarint_12_cons rem1) hlen_cons_lt hpc1 hrun1 hsp1 halign hcl1 htr1 hlr1 hx0_1 ?_
    intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hcs2 hx0_2 hx1_2
    have hregs2 : Chain3LoopRegsPreserved s0 s2 := hregs1.trans (.of_calleeSaved hcs2)
    refine c3_tag2_dispatch_vm a bufRef sp0 hpc2 hrun2 hsp2 hcl2 htr2 hx0_2 hx1_2
      (hregs2.1.trans hx19) (hregs2.2.1.trans hx20) ?_
    intro s3 hpc3 hrun3 hsp3 hcl3 hvm3 htr3 hlr3 hx0_3 hx1_3 hx2_3 hregs3'
    refine SepWPp.done hpc3 hrun3
      ⟨hsp3, hcl3, htr3, hlr3, hx0_3, hx1_3, hx2_3, hregs2.trans hregs3', ?_⟩
    rw [pool_eq_of_vm_c3 A lim st_cur hvm3]
    exact sep_ac_seedChain (by ac_rfl)
  · intro s3 P3 hpc3 hrun3 hcro3 ⟨hsp3, hcl3, htr3, hlr3, hx0_3, hx1_3, hx2_3, hregs3, hent3⟩
    refine sepWPp_mono_pre_c3 hent3 ?_
    have hrem1_lt : ([BitVec.ofNat 8 priv.length] ++ priv ++ (rest ++ tail)).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine c3_bm_call_srk_cro hC (a + 24#64) bufRef slot (ptr + 1#64) sp0 (lsmpl.base 516 + 272#64)
      priv (rest ++ tail) hpriv_lt hpriv_ne hrem1_lt hfit hcro3 hpc3 hrun3 hsp3 halign hcl3 htr3
      hlr3 hx0_3 hx1_3 hx2_3 ?_
    intro s4 evs_bm hpc4 hrun4 hsp4 hcl4 htr4 hcs4 hx0_4 hbnd_bm
    have hregs4 : Chain3LoopRegsPreserved s0 s4 := hregs3.trans (.of_calleeSaved hcs4)
    refine c3_tag2_ret_vm sp0 hpc4 hrun4 hsp4 hcl4 htr4 hx0_4 ?_
    intro s5 hpc5 hrun5 hsp5 hcl5 hvm5 htr5 hregs5'
    refine sepWPp_mono_pre_c3 ?_
      (hnext s5 evs_bm hpc5 hrun5 hsp5 hcl5 htr5 (hregs4.trans hregs5') hbnd_bm)
    rw [pool_eq_of_vm_c3 A lim (M.stepEvents evs_bm st_cur) hvm5,
      pbBytes_ptr_advance_seedChain 2 (by decide) ptr priv hpriv_lt,
      ← pbBytes_pointsTo_combine_seedChain 2 (by decide) ptr priv hpriv_lt]
    exact sep_ac_seedChain (by ac_rfl)

private def tailFields_cro (c : ChainG) : List ChainField :=
  (match c.ck with | some (i, key) => [ChainField.ck i key] | none => []) ++
    c.keys.map ChainField.key

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

theorem chain3Srk_cro_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (ext : LibsignalHooks) :
    Chain3SrkCroStmt M A lim ext := by
  intro hC x st R s0 k s hk htag ⟨hcro, hs⟩
  refine segStepG_keep_cro hcro ?_
  intro hL
  rcases hs with ⟨hpc, hrun, htr, hvregs, hcl, hsp, hal, hx29, hx19, hx20, hx21,
    hx22, hx23, hx24, hx26, hx27, hx28, hcOk, hlen, hfit, evs, hevs_pfx, hmem⟩
  have hfit_fld := fitsEnv_rem_at_field hk hevs_pfx hfit
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
    have h3_le : 3 ≤ 8 * (x.c.fields[k]'hk).enc.length := by
      rw [henc, pbBytes_lt128_eq_seedChain 1 (by decide) b hb_lt]
      simp only [List.length_cons]; omega
    have hsz_le : 2 * b.length + 8 ≤ 256 * (x.c.payload.length + 16) := by omega
    have hfit_bm : FitsEnv M lim (M.stepEvents evs st) (BoundedRustEvs 3 (2 * b.length + 8)) :=
      FitsEnv.mono (fun _ h => BoundedRustEvs.mono h3_le hsz_le h) hfit_fld
    let ck := chainGAfter x.c k
    have hck_srk : ck.srk = [] := chainGAfter_srk_eq_nil_cro hk hfl_eq
    let F : SepProp := (x.ptr ↦ₛ preBytes x.c k) ∗ chain3VecAt A.repAlloc (x.a + 24#64) ck.priv ∗
      chainGRest A.repAlloc x.a ck ∗ chain3SavedRegs s0.sp s0
    have hmem_pre : s.mem ⊨ (((x.bufRef ↦₆₄ x.slot) ∗ chain3VecAt A.repAlloc x.a [] ∗
        sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 1 b ++ (rest ++ x.tail)) ∗
        A.pool lim (M.stepEvents evs st) s ∗
        stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗ F) ∗ R := by
      rw [chain3GAt, hck_srk, sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail k,
        drop_flatMap_enc hk, henc] at hmem
      dsimp only [ck, F, rest] at hmem ⊢; simp only [List.append_assoc, sepConj_assoc] at hmem ⊢
      exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
    have hwp : SepWPp (lsProg_516 (Rust.withPanics ext)) (chain3PCPlacedAtW ext 168#64) s
        (((x.bufRef ↦₆₄ x.slot) ∗ chain3VecAt A.repAlloc x.a [] ∗
          sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 1 b ++ (rest ++ x.tail)) ∗
          A.pool lim (M.stepEvents evs st) s ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗ F)
        (fun sm Pm => (sm.mem ⊨ Pm ∗ R) → Chain3LoopPlacedAtW M A lim ext x st R s0 (k + 1) sm)
        (fun _ _ => False) := by
      refine step_chain3Tag1_cro hC x.a x.bufRef x.slot (curPtr x.ptr x.c k) s0.sp
        b rest x.tail hb_lt hb_ne hlen_pb hfit_bm hcro hpc' hrun hsp hsp0_align hcl htr
        hx19 hx20 hx21 ?_
      intro sm evs_bm hpcm hrunm hspm hclm htrm hregsm hbnd_bm
      refine SepWPp.done hpcm hrunm fun hmem_m => ?_
      have hevs_next : ChainPrefixEnv x.c (k + 1) (evs ++ evs_bm) :=
        chainPrefixEnv_step_field hk hevs_pfx (BoundedRustEvs.mono h3_le hsz_le hbnd_bm)
      refine ⟨hpcm, hrunm, htrm, hregsm.2.2.2.2.2.2.2.2.2.2.trans hvregs, hclm, hspm,
        by simp only [State.spAligned, hspm, ← hsp]; exact hal,
        hregsm.2.2.2.2.2.2.2.2.2.1.trans hx29, hregsm.1.trans hx19, hregsm.2.1.trans hx20,
        hregsm.2.2.1.trans hx21, hregsm.2.2.2.1.trans hx22, hregsm.2.2.2.2.1.trans hx23,
        hregsm.2.2.2.2.2.1.trans hx24, hregsm.2.2.2.2.2.2.1.trans hx26,
        hregsm.2.2.2.2.2.2.2.1.trans hx27, hregsm.2.2.2.2.2.2.2.2.1.trans hx28,
        hcOk, hlen, hfit, evs ++ evs_bm, hevs_next, ?_⟩
      have hpost_eq :
          (((x.bufRef ↦₆₄ x.slot) ∗ chain3VecAt A.repAlloc x.a b ∗
            (curPtr x.ptr x.c k ↦ₛ pbBytes 1 b) ∗
            sliceCursorAt x.slot (curPtr x.ptr x.c k + BitVec.ofNat 64 (pbBytes 1 b).length)
              (rest ++ x.tail) ∗
            A.pool lim (M.stepEvents evs_bm (M.stepEvents evs st)) sm ∗
            stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗ F) =
          (chain3GAt A.repAlloc x.a (chainGAfter x.c (k + 1)) ∗ (x.bufRef ↦₆₄ x.slot) ∗
            sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) (rest ++ x.tail) ∗
            A.pool lim (M.stepEvents (evs ++ evs_bm) st) sm ∗
            stackAt (s0.sp - 240#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0) := by
        rw [← M.stepEvents_append evs evs_bm st,
          chainGAfter_succ hk, hfl_eq, chain3GAt_apply_srk_c3 A.repAlloc x.a ck b, ← henc,
          ← curPtr_succ x.ptr hk, sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail (k + 1),
          ← pointsToBytes_preBytes_succ x.ptr hk]
        dsimp only [ck, F, rest]; ac_rfl
      rw [hpost_eq] at hmem_m; simpa only [sepConj_assoc] using hmem_m
    obtain ⟨sf, hsteps, ⟨_, _, _, hmf, hloop⟩ | ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩⟩ := hwp R hmem_pre hL
    · exact ⟨sf, hsteps, Or.inl (hloop hmf)⟩
    · exact hpan.elim
    · exact (not_satisfies_false_sepConj hoom).elim
  | priv b =>
    have hb_mem : ChainField.priv b ∈ x.c.fields := hfl_eq ▸ List.getElem_mem hk
    have hb_lt : b.length < 128 := mem_fields_priv_length_lt hcOk hb_mem
    have hb_ne : b ≠ [] := mem_fields_priv_ne_nil_cro hb_mem
    have henc : (x.c.fields[k]'hk).enc = pbBytes 2 b := by
      rw [hfl_eq]; exact lenField_eq_pbBytes 2 (Or.inr rfl) b hb_lt
    have hlen_pb : (pbBytes 2 b ++ rest ++ x.tail).length < 2 ^ 62 := by rwa [← henc]
    have h3_le : 3 ≤ 8 * (x.c.fields[k]'hk).enc.length := by
      rw [henc, pbBytes_lt128_eq_seedChain 2 (by decide) b hb_lt]
      simp only [List.length_cons]; omega
    have hsz_le : 2 * b.length + 8 ≤ 256 * (x.c.payload.length + 16) := by omega
    have hfit_bm : FitsEnv M lim (M.stepEvents evs st) (BoundedRustEvs 3 (2 * b.length + 8)) :=
      FitsEnv.mono (fun _ h => BoundedRustEvs.mono h3_le hsz_le h) hfit_fld
    let ck := chainGAfter x.c k
    have hck_priv : ck.priv = [] := chainGAfter_priv_eq_nil_cro hk hfl_eq
    let F : SepProp := (x.ptr ↦ₛ preBytes x.c k) ∗ chain3VecAt A.repAlloc x.a ck.srk ∗
      chainGRest A.repAlloc x.a ck ∗ chain3SavedRegs s0.sp s0
    have hmem_pre : s.mem ⊨ (((x.bufRef ↦₆₄ x.slot) ∗ chain3VecAt A.repAlloc (x.a + 24#64) [] ∗
        sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 2 b ++ (rest ++ x.tail)) ∗
        A.pool lim (M.stepEvents evs st) s ∗
        stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗ F) ∗ R := by
      rw [chain3GAt, hck_priv, sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail k,
        drop_flatMap_enc hk, henc] at hmem
      dsimp only [ck, F, rest] at hmem ⊢; simp only [List.append_assoc, sepConj_assoc] at hmem ⊢
      exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
    have hwp : SepWPp (lsProg_516 (Rust.withPanics ext)) (chain3PCPlacedAtW ext 168#64) s
        (((x.bufRef ↦₆₄ x.slot) ∗ chain3VecAt A.repAlloc (x.a + 24#64) [] ∗
          sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 2 b ++ (rest ++ x.tail)) ∗
          A.pool lim (M.stepEvents evs st) s ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗ F)
        (fun sm Pm => (sm.mem ⊨ Pm ∗ R) → Chain3LoopPlacedAtW M A lim ext x st R s0 (k + 1) sm)
        (fun _ _ => False) := by
      refine step_chain3Tag2_cro hC x.a x.bufRef x.slot (curPtr x.ptr x.c k) s0.sp
        b rest x.tail hb_lt hb_ne hlen_pb hfit_bm hcro hpc' hrun hsp hsp0_align hcl htr
        hx19 hx20 hx21 ?_
      intro sm evs_bm hpcm hrunm hspm hclm htrm hregsm hbnd_bm
      refine SepWPp.done hpcm hrunm fun hmem_m => ?_
      have hevs_next : ChainPrefixEnv x.c (k + 1) (evs ++ evs_bm) :=
        chainPrefixEnv_step_field hk hevs_pfx (BoundedRustEvs.mono h3_le hsz_le hbnd_bm)
      refine ⟨hpcm, hrunm, htrm, hregsm.2.2.2.2.2.2.2.2.2.2.trans hvregs, hclm, hspm,
        by simp only [State.spAligned, hspm, ← hsp]; exact hal,
        hregsm.2.2.2.2.2.2.2.2.2.1.trans hx29, hregsm.1.trans hx19, hregsm.2.1.trans hx20,
        hregsm.2.2.1.trans hx21, hregsm.2.2.2.1.trans hx22, hregsm.2.2.2.2.1.trans hx23,
        hregsm.2.2.2.2.2.1.trans hx24, hregsm.2.2.2.2.2.2.1.trans hx26,
        hregsm.2.2.2.2.2.2.2.1.trans hx27, hregsm.2.2.2.2.2.2.2.2.1.trans hx28,
        hcOk, hlen, hfit, evs ++ evs_bm, hevs_next, ?_⟩
      have hpost_eq :
          (((x.bufRef ↦₆₄ x.slot) ∗ chain3VecAt A.repAlloc (x.a + 24#64) b ∗
            (curPtr x.ptr x.c k ↦ₛ pbBytes 2 b) ∗
            sliceCursorAt x.slot (curPtr x.ptr x.c k + BitVec.ofNat 64 (pbBytes 2 b).length)
              (rest ++ x.tail) ∗
            A.pool lim (M.stepEvents evs_bm (M.stepEvents evs st)) sm ∗
            stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗ F) =
          (chain3GAt A.repAlloc x.a (chainGAfter x.c (k + 1)) ∗ (x.bufRef ↦₆₄ x.slot) ∗
            sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) (rest ++ x.tail) ∗
            A.pool lim (M.stepEvents (evs ++ evs_bm) st) sm ∗
            stackAt (s0.sp - 240#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0) := by
        rw [← M.stepEvents_append evs evs_bm st,
          chainGAfter_succ hk, hfl_eq, chain3GAt_apply_priv_c3 A.repAlloc x.a ck b, ← henc,
          ← curPtr_succ x.ptr hk, sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail (k + 1),
          ← pointsToBytes_preBytes_succ x.ptr hk]
        dsimp only [ck, F, rest]; ac_rfl
      rw [hpost_eq] at hmem_m; simpa only [sepConj_assoc] using hmem_m
    obtain ⟨sf, hsteps, ⟨_, _, _, hmf, hloop⟩ | ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩⟩ := hwp R hmem_pre hL
    · exact ⟨sf, hsteps, Or.inl (hloop hmf)⟩
    · exact hpan.elim
    · exact (not_satisfies_false_sepConj hoom).elim

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroBPlacedBudgetAux
