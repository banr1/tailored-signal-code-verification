/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.SenderReceiverChains
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SenderReceiverChainsX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SpareBaseXBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PrologueVersionLocalIdentity
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Pre-Reserved `SessionStructure::encode_raw` Tags 6 and 7 (`460` → `536`)

Proves zero-allocation (`VmPreserved`-preserving) relocatable step lemmas for protobuf tag 6
(`sender_chain`) and the protobuf tag 7 `receiver_chains` loop in Block `14` (`460..536`) when the
output buffer has sufficient spare capacity.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SpareChainsXBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (SenderChain ReceiverChain)
open CryptoVerification (LibsignalPlacement LibsignalHooks lsmpl)
open CryptoVerification.RustHeap (RustAlloc vecU8At arrayAt vecBuf vecAt)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt)
open CryptoVerification.LibsignalTripleRatchetRepr (
  noneCap SenderChainGhost optSenderChainAt
)
open CryptoVerification.LibsignalTripleRatchet.Prost (vecU8Buf)
open CryptoVerification.E2E.Record (lenField)
open CryptoVerification.E2E.Record.Placed (blkPl_14 lsProg_14)
open CryptoVerification.E2E.Record.Serialization (
  senderAsChain senderGhostAsChain encSenderFieldMem encChainMem protoChainAt
  encodeRawSubStackX bv_add_neg80_2_x
  sepWPpLsCl_extract_chainAt_cap sepWPpLsCl_extract_vecAt_chains_bounds
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
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget (
  sepWPpLsCl_of_sepWP_vm
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SpareBaseXBudget (
  EncodeChainPreallocPlacedOkX'
  encraw_call_protoEncodeChain_prealloc_placed_x
  encraw_call_encodeChain_prealloc_placed_x
)

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
  stackAt vecU8Buf vecSrcRest vecCopyDone chainRest vecChainsRest vecBuf protoChainAt

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_add_neg80_2_x

/-- Pre-reserved (`0`-allocation, `VmPreserved`) Tag 6 (`sender_chain`, offsets `460..488`)
    under `EncodeChainPreallocPlacedOkX' A H`. -/
theorem step_encraw_tag6_prealloc_placed_x [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (hEC : EncodeChainPreallocPlacedOkX' A H)
    (ss v sp0 cap ptr : BitVec 64)
    (senderG : Option SenderChainGhost) (sender : Option SenderChain)
    (bs : List (BitVec 8))
    (hspare : bs.length + (encSenderFieldMem senderG sender).length ≤ cap.toNat)
    (hlen_lt : bs.length + (encSenderFieldMem senderG sender).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 460#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (optSenderChainAt A (ss + 0x90#64) senderG sender ∗
      vecU8At A v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 488#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((optSenderChainAt A (ss + 0x90#64) senderG sender ∗
          vecU8At A v cap ptr (bs ++ encSenderFieldMem senderG sender) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallEC := @encraw_call_protoEncodeChain_prealloc_placed_x _ A H hEC
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
          ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
        refine SepWPpLsCl.weaken_pre ?_ (hnext _ hvm
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
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
      rw [optSenderChainAt_some_eq_chainAt_er A (ss + 0x90#64) g sc]
      simp only [sepConj_assoc]
      refine SepWPpLsCl.pure_elim fun hpriv => ?_
      refine sepWPpLsCl_extract_chainAt_cap (A := A)
        (gc := (senderGhostAsChain g, senderAsChain sc))
        (a := ss + 0x90#64) (hfocus := by sep_focus) (h := fun hcap => ?_)
      have hcmn1 := cmn1_beq_zero_false hcap
      have hcmn2 := cap_beq_noneCap_false hcap
      rw [chainAt_open_cap A (senderGhostAsChain g, senderAsChain sc) (ss + 0x90#64)]
      simp only [sepConj_assoc]
      apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 12)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
        refine SepWPpLsCl.weaken_pre (P' :=
            (protoChainAt A (senderGhostAsChain g, senderAsChain sc) (ss + 0x90#64) ∗
              vecU8At A v cap ptr bs ∗
              stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
          (by
            rw [chainAt_open_cap A (senderGhostAsChain g, senderAsChain sc) (ss + 0x90#64)]
            simp only [sepConj_assoc]
            exact entails_of_sep_focus (by sep_focus)) ?_
        refine hCallEC 6 sp0 (ss + 0x90#64) v cap ptr ((blkPl_14).base + 488#64)
          (senderGhostAsChain g, senderAsChain sc) bs (Or.inl rfl) hspare hlen_lt (s0 := s0)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by sep_focus) ?_
        intro sm hvm1 hpcm hrunm hspm htrm hcsm
        have hx19m : sm.readReg64 .x19 = v := by
          have := hcsm.1; simp only [arm64_norm, *] at this; exact this
        have hx20m : sm.readReg64 .x20 = ss := by
          have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
        have hcsm' : EncRawUpperSaved s0 sm :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
        refine SepWPpLsCl.weaken_pre ?_
          (hnext sm (hvm0.trans hvm1) hpcm hrunm hspm htrm hx19m hx20m hcsm')
        rw [optSenderChainAt_some_eq_chainAt_er A (ss + 0x90#64) g sc, eq_true hpriv,
            pure_true, emp_sepConj]
        exact entails_of_sep_focus (by sep_focus)

/-- Pre-reserved (`0`-allocation, `VmPreserved`) inner loop of Tag 7 (`+0x1fc..+0x218`,
    offsets `508..536`). -/
theorem step_encraw_tag7_loop_prealloc_placed_x [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (hEC : EncodeChainPreallocPlacedOkX' A H)
    (gcs : List (ChainGhost × ReceiverChain))
    (hne : gcs ≠ [])
    (ss v sp0 curPtr cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hmul_lt : gcs.length * 104 < 2 ^ 63)
    (hspare : bs.length + ((gcs.map fun gc => lenField 7 (encChainMem gc)).flatten).length ≤ cap.toNat)
    (hlen_lt : bs.length + ((gcs.map fun gc => lenField 7 (encChainMem gc)).flatten).length < 2 ^ 32)
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
    (hP : P = (arrayAt (chainAt A) 104 curPtr gcs ∗ vecU8At A v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 536#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((arrayAt (chainAt A) 104 curPtr gcs ∗
          vecU8At A v cap ptr
            (bs ++ (gcs.map fun gc => lenField 7 (encChainMem gc)).flatten) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  induction gcs generalizing curPtr bs s P F with
  | nil => exact False.elim (hne rfl)
  | cons gc rest ih =>
    have hCallEC := @encraw_call_encodeChain_prealloc_placed_x _ A H hEC
    rw [hP]
    simp only [arrayAt, sepConj_assoc]
    have hlen_head := len_head_lt_of_cons hlen_lt
    have hspare_split : bs.length +
        ((lenField 7 (encChainMem gc)).length +
          ((rest.map fun gc => lenField 7 (encChainMem gc)).flatten).length) ≤ cap.toNat := by
      simpa only [List.map_cons, List.flatten_cons, List.length_append] using hspare
    have hspare_head : bs.length + (lenField 7 (encChainMem gc)).length ≤ cap.toNat := by omega
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 12)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
      refine hCallEC 7 sp0 curPtr v cap ptr ((blkPl_14).base + 524#64) gc bs
        (Or.inr rfl) hspare_head hlen_head (s0 := s0)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by sep_focus) ?_
      intro s1 hvm1 hpc1 hrun1 hsp1 htr1 hcs1
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
        apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 536#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
          refine SepWPpLsCl.weaken_pre ?_ (hnext _ ((hvm0.trans hvm1).trans hvm2)
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
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
        have hspare_rest :
            (bs ++ lenField 7 (encChainMem gc)).length +
              (((gc2 :: rest').map fun gc => lenField 7 (encChainMem gc)).flatten).length ≤ cap.toNat := by
          rw [List.length_append]
          omega
        apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 508#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
          have hlen_rest := len_rest_lt_of_cons hlen_lt
          refine ih (F := chainAt A gc curPtr ∗ F) hne_rest (curPtr + 104#64)
            (bs ++ lenField 7 (encChainMem gc)) hmul_rest hspare_rest hlen_rest
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
            (by sep_focus) ?_
          intro sm hvm3 hpcm hrunm hspm htrm hx19m hx20m hcsm'
          refine SepWPpLsCl.weaken_pre ?_
            (hnext sm (((hvm0.trans hvm1).trans hvm2).trans hvm3)
              hpcm hrunm hspm htrm hx19m hx20m hcsm')
          simp only [arrayAt, List.map_cons, List.flatten_cons, List.append_assoc, sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus)

/-- Pre-reserved (`0`-allocation, `VmPreserved`) Tag 7 (`receiver_chains`, offsets `488..536`)
    of Block `14` (`encode_raw`). -/
theorem step_encraw_tag7_prealloc_placed_x [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (hEC : EncodeChainPreallocPlacedOkX' A H)
    (ss v sp0 cCap cPtr cap ptr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (bs : List (BitVec 8))
    (hspare : bs.length + ((gcs.map fun gc => lenField 7 (encChainMem gc)).flatten).length ≤ cap.toNat)
    (hlen_lt : bs.length + ((gcs.map fun gc => lenField 7 (encChainMem gc)).flatten).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 488#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecAt A 104 8 (chainAt A) (ss + 0x48#64) cCap cPtr gcs ∗
      vecU8At A v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 536#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecAt A 104 8 (chainAt A) (ss + 0x48#64) cCap cPtr gcs ∗
          vecU8At A v cap ptr
            (bs ++ (gcs.map fun gc => lenField 7 (encChainMem gc)).flatten) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hLoop := @step_encraw_tag7_loop_prealloc_placed_x _ A H hEC
  rw [hP]
  refine sepWPpLsCl_extract_vecAt_chains_bounds (A := A) (a := ss + 0x48#64)
    (cap := cCap) (ptr := cPtr) (gcs := gcs) (hfocus := by sep_focus) (h := fun hle hcap_mul => ?_)
  by_cases hgcs : gcs = []
  · subst hgcs
    rw [vecAt_chains_nil A ss cCap cPtr]
    simp only [sepConj_assoc]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 536#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ hvm
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [vecAt_chains_nil A ss cCap cPtr]
      simp only [List.map_nil, List.flatten_nil, List.append_nil, sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)
  · have hbeq0 := ofNat64_chains_len_beq_zero_false hgcs (by omega)
    have hmul := bv_len_mul_104 gcs.length
    rw [vecAt_chains_open A ss cCap cPtr gcs hgcs hle]
    simp only [sepConj_assoc]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 508#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
      refine hLoop gcs hgcs ss v sp0 cPtr cap ptr bs (by omega) hspare hlen_lt
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
        (by sep_focus) ?_
      intro sm hvm1 hpcm hrunm hspm htrm hx19m hx20m hcsm'
      refine SepWPpLsCl.weaken_pre ?_
        (hnext sm (hvm0.trans hvm1) hpcm hrunm hspm htrm hx19m hx20m hcsm')
      rw [vecAt_chains_open A ss cCap cPtr gcs hgcs hle]
      simp only [sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SpareChainsXBudget
