/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.SenderReceiverChains
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.SenderReceiverChainsBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SenderReceiverChainsX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PrologueVersionLocalIdentity
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `SessionStructure::encode_raw` Tags 6 and 7 (`460` → `536`)

Verifies relocatable protobuf tag 6 (`sender_chain`, `460..488`) and the protobuf tag 7
`receiver_chains` loop (`488..536`) in Block `14` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SenderReceiverChainsXBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (SenderChain ReceiverChain)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks lsmpl withLsCodeLoaded
)
open CryptoVerification.RustHeap (vecU8At arrayAt vecBuf vecAt)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt)
open CryptoVerification.LibsignalTripleRatchetRepr (
  noneCap SenderChainGhost optSenderChainAt
)
open CryptoVerification.LibsignalTripleRatchet.Prost (vecU8Buf)
open CryptoVerification.E2E.Record (lenField)
open CryptoVerification.E2E.Record.Placed (blkPl_12 lsProg_12 blkPl_14 lsProg_14)
open CryptoVerification.E2E.Record.Serialization (
  senderAsChain senderGhostAsChain encSenderFieldMem encChainMem protoChainAt
  encodeRawSubStackX bv_add_neg80_2_x
)
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux (
  entails_of_sep_focus EncRawUpperSaved sp_sub_80_spAligned
  vecSrcRest vecCopyDone optSenderChainAt_some_eq_chainAt_er
  chainRest chainAt_open_cap
  cmn1_beq_zero_false cap_beq_noneCap_false
  vecChainsRest vecAt_chains_open vecAt_chains_nil
  bv_len_mul_104 bv_cons_len_mul_104_sub bv_mul_104_beq_zero_false
  bv_cons_len_mul_104_beq_104_false bv_cons_len_mul_104_bne_104_true
  ofNat64_chains_len_beq_zero_false
  mul_104_cons_lt len_head_lt_of_cons len_rest_lt_of_cons
)
open Proofs.libsignal.Hooks2 (SepWPpLsCl)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget (
  EncRawSegEnv encRawSegEnv_nil encRawSegEnv_append
  fitsEnv_encRawSeg_left fitsEnv_encRawSeg_right
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  EncodeChainPlacedOkX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget (
  sepWPpLsCl_of_sepWP_vm sepWPpLsCl_transport_budgetPool
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseXBudget (
  encodeChainSpecWithEnvX
  encraw_call_protoEncodeChain_env_placed_x
  encraw_call_encodeChain_env_placed_x
  encraw_call_protoEncodeChain_placed_x
)

abbrev sepWPpLsCl_extract_chainAt_cap :=
  @CryptoVerification.E2E.Record.Serialization.sepWPpLsCl_extract_chainAt_cap
abbrev sepWPpLsCl_extract_vecAt_chains_bounds :=
  @CryptoVerification.E2E.Record.Serialization.sepWPpLsCl_extract_vecAt_chains_bounds
abbrev encodeChainSegEnv :=
  LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.SenderReceiverChainsBudget.encodeChainSegEnv
abbrev encodeChainSegEnv_sub_encodeChainEnv :=
  @LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.SenderReceiverChainsBudget.encodeChainSegEnv_sub_encodeChainEnv
abbrev SenderTag6Env :=
  LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.SenderReceiverChainsBudget.SenderTag6Env

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
  stackAt vecU8Buf vecSrcRest vecCopyDone chainRest vecChainsRest vecBuf protoChainAt

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_add_neg80_2_x

/-- Relocatable Tag 6 (`sender_chain`, offsets `460..488`) under
    `encodeChainSpecWithEnvX M A lim encodeChainSegEnv`. -/
theorem step_encraw_tag6_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hEC : subroutine_ok (lsProg_12 H) (blkPl_12).base
      (withLsCodeLoaded lsmpl (encodeChainSpecWithEnvX M A lim encodeChainSegEnv)))
    (ss v sp0 cap ptr : BitVec 64)
    (senderG : Option SenderChainGhost) (sender : Option SenderChain)
    (bs : List (BitVec 8)) (st : M.σ)
    (hlen_lt : bs.length + (encSenderFieldMem senderG sender).length < 2 ^ 32)
    (hfit : FitsEnv M lim st (EncRawSegEnv bs.length (encSenderFieldMem senderG sender).length))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 460#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (optSenderChainAt A.repAlloc (ss + 0x90#64) senderG sender ∗
      vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_14).base + 488#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      EncRawSegEnv bs.length (encSenderFieldMem senderG sender).length evs →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((optSenderChainAt A.repAlloc (ss + 0x90#64) senderG sender ∗
          vecU8At A.repAlloc v cap' ptr' (bs ++ encSenderFieldMem senderG sender) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallEC := @encraw_call_protoEncodeChain_env_placed_x _ M A lim encodeChainSegEnv H hEC
  rw [hP]
  cases senderG with
  | none =>
    cases sender with
    | none =>
      simp only [optSenderChainAt, noneCap, sepConj_assoc]
      apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 488#64)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm =>
            sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm (by sep_focus) ?_⟩
        refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap ptr []
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
          (encRawSegEnv_nil _ _))
        simp only [optSenderChainAt, noneCap, encSenderFieldMem, List.append_nil, sepConj_assoc]
        exact entails_of_sep_focus (by sep_focus)
    | some sc =>
      simp only [optSenderChainAt, sepConj_assoc]
      exact SepWPpLsCl.pure_elim fun h => False.elim h
  | some g =>
    cases sender with
    | none =>
      simp only [optSenderChainAt, sepConj_assoc]
      exact SepWPpLsCl.pure_elim fun h => False.elim h
    | some sc =>
      rw [optSenderChainAt_some_eq_chainAt_er A.repAlloc (ss + 0x90#64) g sc]
      simp only [sepConj_assoc]
      refine SepWPpLsCl.pure_elim fun hpriv => ?_
      refine sepWPpLsCl_extract_chainAt_cap (A := A.repAlloc)
        (gc := (senderGhostAsChain g, senderAsChain sc))
        (a := ss + 0x90#64) (hfocus := by sep_focus) (h := fun hcap => ?_)
      have hcmn1 := cmn1_beq_zero_false hcap
      have hcmn2 := cap_beq_noneCap_false hcap
      rw [chainAt_open_cap A.repAlloc (senderGhostAsChain g, senderAsChain sc) (ss + 0x90#64)]
      simp only [sepConj_assoc]
      apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 12)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm0 =>
            sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
        refine SepWPpLsCl.weaken_pre (P' :=
            (protoChainAt A.repAlloc (senderGhostAsChain g, senderAsChain sc) (ss + 0x90#64) ∗
              vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st _ ∗
              stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
          (by
            rw [chainAt_open_cap A.repAlloc (senderGhostAsChain g, senderAsChain sc) (ss + 0x90#64)]
            simp only [sepConj_assoc]
            exact entails_of_sep_focus (by sep_focus)) ?_
        refine hCallEC 6 sp0 (ss + 0x90#64) v cap ptr ((blkPl_14).base + 488#64)
          (senderGhostAsChain g, senderAsChain sc) bs st (Or.inl rfl) hlen_lt hfit (s0 := s0)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by sep_focus) ?_
        intro sm cap' ptr' evs hpcm hrunm hspm htrm hcsm hevs
        have hx19m : sm.readReg64 .x19 = v := by
          have := hcsm.1; simp only [arm64_norm, *] at this; exact this
        have hx20m : sm.readReg64 .x20 = ss := by
          have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
        have hcsm' : EncRawUpperSaved s0 sm :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
        refine SepWPpLsCl.weaken_pre ?_
          (hnext sm cap' ptr' evs hpcm hrunm hspm htrm hx19m hx20m hcsm' hevs)
        rw [optSenderChainAt_some_eq_chainAt_er A.repAlloc (ss + 0x90#64) g sc, eq_true hpriv,
            pure_true, emp_sepConj]
        exact entails_of_sep_focus (by sep_focus)

/-- Relocatable Tag 6 (`sender_chain`, offsets `460..488`) directly under `EncodeChainPlacedOkX`. -/
theorem step_encraw_tag6_direct_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hEC : EncodeChainPlacedOkX M A lim H)
    (ss v sp0 cap ptr : BitVec 64)
    (senderG : Option SenderChainGhost) (sender : Option SenderChain)
    (bs : List (BitVec 8)) (st : M.σ)
    (hlen_lt : bs.length + (encSenderFieldMem senderG sender).length < 2 ^ 32)
    (hfit : FitsEnv M lim st (SenderTag6Env senderG sender (ss + 0x90#64) v cap ptr bs))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 460#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (optSenderChainAt A.repAlloc (ss + 0x90#64) senderG sender ∗
      vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_14).base + 488#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SenderTag6Env senderG sender (ss + 0x90#64) v cap ptr bs evs →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((optSenderChainAt A.repAlloc (ss + 0x90#64) senderG sender ∗
          vecU8At A.repAlloc v cap' ptr' (bs ++ encSenderFieldMem senderG sender) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallEC := @encraw_call_protoEncodeChain_placed_x _ M A lim H hEC
  rw [hP]
  cases senderG with
  | none =>
    cases sender with
    | none =>
      simp only [optSenderChainAt, noneCap, sepConj_assoc]
      apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 488#64)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm =>
            sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm (by sep_focus) ?_⟩
        refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap ptr []
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
          rfl)
        simp only [optSenderChainAt, noneCap, encSenderFieldMem, List.append_nil, sepConj_assoc]
        exact entails_of_sep_focus (by sep_focus)
    | some sc =>
      simp only [optSenderChainAt, sepConj_assoc]
      exact SepWPpLsCl.pure_elim fun h => False.elim h
  | some g =>
    cases sender with
    | none =>
      simp only [optSenderChainAt, sepConj_assoc]
      exact SepWPpLsCl.pure_elim fun h => False.elim h
    | some sc =>
      rw [optSenderChainAt_some_eq_chainAt_er A.repAlloc (ss + 0x90#64) g sc]
      simp only [sepConj_assoc]
      refine SepWPpLsCl.pure_elim fun hpriv => ?_
      refine sepWPpLsCl_extract_chainAt_cap (A := A.repAlloc)
        (gc := (senderGhostAsChain g, senderAsChain sc))
        (a := ss + 0x90#64) (hfocus := by sep_focus) (h := fun hcap => ?_)
      have hcmn1 := cmn1_beq_zero_false hcap
      have hcmn2 := cap_beq_noneCap_false hcap
      rw [chainAt_open_cap A.repAlloc (senderGhostAsChain g, senderAsChain sc) (ss + 0x90#64)]
      simp only [sepConj_assoc]
      apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 12)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm0 =>
            sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
        refine SepWPpLsCl.weaken_pre (P' :=
            (protoChainAt A.repAlloc (senderGhostAsChain g, senderAsChain sc) (ss + 0x90#64) ∗
              vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st _ ∗
              stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
          (by
            rw [chainAt_open_cap A.repAlloc (senderGhostAsChain g, senderAsChain sc) (ss + 0x90#64)]
            simp only [sepConj_assoc]
            exact entails_of_sep_focus (by sep_focus)) ?_
        refine hCallEC 6 sp0 (ss + 0x90#64) v cap ptr ((blkPl_14).base + 488#64)
          (senderGhostAsChain g, senderAsChain sc) bs st (Or.inl rfl) hlen_lt hfit (s0 := s0)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by sep_focus) ?_
        intro sm cap' ptr' evs hpcm hrunm hspm htrm hcsm hevs
        have hx19m : sm.readReg64 .x19 = v := by
          have := hcsm.1; simp only [arm64_norm, *] at this; exact this
        have hx20m : sm.readReg64 .x20 = ss := by
          have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
        have hcsm' : EncRawUpperSaved s0 sm :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
        refine SepWPpLsCl.weaken_pre ?_
          (hnext sm cap' ptr' evs hpcm hrunm hspm htrm hx19m hx20m hcsm' hevs)
        rw [optSenderChainAt_some_eq_chainAt_er A.repAlloc (ss + 0x90#64) g sc, eq_true hpriv,
            pure_true, emp_sepConj]
        exact entails_of_sep_focus (by sep_focus)

/-- Relocatable inner loop of Tag 7 (`+0x1fc..+0x218`, offsets `508..536`). -/
theorem step_encraw_tag7_loop_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hEC : subroutine_ok (lsProg_12 H) (blkPl_12).base
      (withLsCodeLoaded lsmpl (encodeChainSpecWithEnvX M A lim encodeChainSegEnv)))
    (gcs : List (ChainGhost × ReceiverChain))
    (hne : gcs ≠ [])
    (ss v sp0 curPtr cap ptr : BitVec 64) (bs : List (BitVec 8)) (st : M.σ)
    (hmul_lt : gcs.length * 104 < 2 ^ 63)
    (hlen_lt : bs.length + ((gcs.map fun gc => lenField 7 (encChainMem gc)).flatten).length < 2 ^ 32)
    (hfit : FitsEnv M lim st
      (EncRawSegEnv bs.length ((gcs.map fun gc => lenField 7 (encChainMem gc)).flatten).length))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 508#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = curPtr)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (gcs.length * 104))
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (arrayAt (chainAt A.repAlloc) 104 curPtr gcs ∗ vecU8At A.repAlloc v cap ptr bs ∗
      A.pool lim st s ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_14).base + 536#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      EncRawSegEnv bs.length ((gcs.map fun gc => lenField 7 (encChainMem gc)).flatten).length evs →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((arrayAt (chainAt A.repAlloc) 104 curPtr gcs ∗
          vecU8At A.repAlloc v cap' ptr'
            (bs ++ (gcs.map fun gc => lenField 7 (encChainMem gc)).flatten) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  induction gcs generalizing curPtr cap ptr bs st s P F with
  | nil => exact False.elim (hne rfl)
  | cons gc rest ih =>
    have hCallEC := @encraw_call_encodeChain_env_placed_x _ M A lim encodeChainSegEnv H hEC
    rw [hP]
    simp only [arrayAt, sepConj_assoc]
    have hlen_head := len_head_lt_of_cons hlen_lt
    have hfit_split : FitsEnv M lim st
        (EncRawSegEnv bs.length
          ((lenField 7 (encChainMem gc)).length +
            ((rest.map fun gc => lenField 7 (encChainMem gc)).flatten).length)) := by
      simpa only [List.map_cons, List.flatten_cons, List.length_append] using hfit
    have hfit_head : FitsEnv M lim st
        (encodeChainSegEnv ⟨7, curPtr, gc, v, cap, ptr, bs⟩) :=
      fitsEnv_encRawSeg_left hfit_split
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 12)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
      refine hCallEC 7 sp0 curPtr v cap ptr ((blkPl_14).base + 524#64) gc bs st
        (Or.inr rfl) hlen_head hfit_head (s0 := s0)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by sep_focus) ?_
      intro s1 cap1 ptr1 evs1 hpc1 hrun1 hsp1 htr1 hcs1 hevs1
      have hx19_1 : s1.readReg64 .x19 = v := by
        have := hcs1.1; simp only [arm64_norm, *] at this; exact this
      have hx20_1 : s1.readReg64 .x20 = ss := by
        have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 ((gc :: rest).length * 104) := by
        have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx22_1 : s1.readReg64 .x22 = curPtr + 104#64 := by
        have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcs_1 : EncRawUpperSaved s0 s1 :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
      cases rest with
      | nil =>
        simp only [List.length_singleton, Nat.one_mul] at hx21_1
        change s1.readReg64 .x21 = 104#64 at hx21_1
        have hevs1' : EncRawSegEnv bs.length
            ((([gc]).map fun gc => lenField 7 (encChainMem gc)).flatten).length evs1 := by
          simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
            List.append_nil]
          exact hevs1
        apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 536#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], fun hvm2 =>
              sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := M.stepEvents evs1 st) hvm2 (by sep_focus) ?_⟩
          refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap1 ptr1 evs1
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
            hevs1')
          simp only [arrayAt, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
            List.append_nil, emp_sepConj, sepConj_emp, sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus)
      | cons gc2 rest' =>
        have hne_rest : (gc2 :: rest') ≠ [] := List.cons_ne_nil _ _
        have hsub := bv_cons_len_mul_104_sub gc (gc2 :: rest')
        have hmul_rest := mul_104_cons_lt hmul_lt
        have hbeq0 := bv_mul_104_beq_zero_false hne_rest hmul_rest
        have hbeq104 := bv_cons_len_mul_104_beq_104_false gc hne_rest hmul_lt
        have hbne104 := bv_cons_len_mul_104_bne_104_true gc hne_rest hmul_lt
        have hfit_rest : FitsEnv M lim (M.stepEvents evs1 st)
            (EncRawSegEnv (bs ++ lenField 7 (encChainMem gc)).length
              (((gc2 :: rest').map fun gc => lenField 7 (encChainMem gc)).flatten).length) := by
          have h := fitsEnv_encRawSeg_right hfit_split hevs1
          rwa [← List.length_append] at h
        apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 508#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], fun hvm2 =>
              sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := M.stepEvents evs1 st) hvm2 (by sep_focus) ?_⟩
          have hlen_rest := len_rest_lt_of_cons hlen_lt
          refine ih (F := chainAt A.repAlloc gc curPtr ∗ F) hne_rest (curPtr + 104#64) cap1 ptr1
            (bs ++ lenField 7 (encChainMem gc)) (M.stepEvents evs1 st) hmul_rest hlen_rest hfit_rest
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
            (by sep_focus) ?_
          intro sm cap' ptr' evs2 hpcm hrunm hspm htrm hx19m hx20m hcsm' hevs2
          have hevs_all : EncRawSegEnv bs.length
              (((gc :: gc2 :: rest').map fun gc => lenField 7 (encChainMem gc)).flatten).length
              (evs1 ++ evs2) := by
            rw [List.map_cons, List.flatten_cons, List.length_append]
            refine encRawSegEnv_append hevs1 ?_
            rwa [List.length_append] at hevs2
          refine SepWPpLsCl.weaken_pre ?_
            (hnext sm cap' ptr' (evs1 ++ evs2) hpcm hrunm hspm htrm hx19m hx20m hcsm' hevs_all)
          simp only [← M.stepEvents_append, arrayAt, List.map_cons, List.flatten_cons,
            List.append_assoc, sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus)

/-- Relocatable Tag 7 (`receiver_chains`, offsets `488..536`) of Block `14` (`encode_raw`). -/
theorem step_encraw_tag7_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hEC : subroutine_ok (lsProg_12 H) (blkPl_12).base
      (withLsCodeLoaded lsmpl (encodeChainSpecWithEnvX M A lim encodeChainSegEnv)))
    (ss v sp0 cCap cPtr cap ptr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (bs : List (BitVec 8)) (st : M.σ)
    (hlen_lt : bs.length + ((gcs.map fun gc => lenField 7 (encChainMem gc)).flatten).length < 2 ^ 32)
    (hfit : FitsEnv M lim st
      (EncRawSegEnv bs.length ((gcs.map fun gc => lenField 7 (encChainMem gc)).flatten).length))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 488#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (ss + 0x48#64) cCap cPtr gcs ∗
      vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_14).base + 536#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      EncRawSegEnv bs.length ((gcs.map fun gc => lenField 7 (encChainMem gc)).flatten).length evs →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (ss + 0x48#64) cCap cPtr gcs ∗
          vecU8At A.repAlloc v cap' ptr'
            (bs ++ (gcs.map fun gc => lenField 7 (encChainMem gc)).flatten) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hLoop := @step_encraw_tag7_loop_placed_x _ M A lim H hEC
  rw [hP]
  refine sepWPpLsCl_extract_vecAt_chains_bounds (A := A.repAlloc) (a := ss + 0x48#64)
    (cap := cCap) (ptr := cPtr) (gcs := gcs) (hfocus := by sep_focus) (h := fun hle hcap_mul => ?_)
  by_cases hgcs : gcs = []
  · subst hgcs
    rw [vecAt_chains_nil A.repAlloc ss cCap cPtr]
    simp only [sepConj_assoc]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 536#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm (by sep_focus) ?_⟩
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap ptr []
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
        (encRawSegEnv_nil _ _))
      rw [vecAt_chains_nil A.repAlloc ss cCap cPtr]
      simp only [List.map_nil, List.flatten_nil, List.append_nil, sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)
  · have hbeq0 := ofNat64_chains_len_beq_zero_false hgcs (by omega)
    have hmul := bv_len_mul_104 gcs.length
    rw [vecAt_chains_open A.repAlloc ss cCap cPtr gcs hgcs hle]
    simp only [sepConj_assoc]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 508#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
      refine hLoop gcs hgcs ss v sp0 cPtr cap ptr bs st (by omega) hlen_lt hfit
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
        (by sep_focus) ?_
      intro sm cap' ptr' evs hpcm hrunm hspm htrm hx19m hx20m hcsm' hevs
      refine SepWPpLsCl.weaken_pre ?_
        (hnext sm cap' ptr' evs hpcm hrunm hspm htrm hx19m hx20m hcsm' hevs)
      rw [vecAt_chains_open A.repAlloc ss cCap cPtr gcs hgcs hle]
      simp only [sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SenderReceiverChainsXBudget
