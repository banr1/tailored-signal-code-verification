/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PrologueVersionLocalIdentity
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.SenderReceiverChains
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `SessionStructure::encode_raw` Tags 6 and 7: `sender_chain` and `receiver_chains` (`+0x1cc` → `+0x218`)

Verifies protobuf tag 6 (`sender_chain`, `460..488`) and the protobuf tag 7 `receiver_chains` slice
loop (`488..536`) of `SessionStructure::encode_raw` (`0x4d38`, Block `14`) on `SP2Ext` and under
relocatable `[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap hiding vecU8Buf vecU8At_eq_header_sep_buf
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open Proofs.libsignal.Hooks2
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

set_option allowUnsafeReducibility true
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local irreducible] stackAt vecRest vecU8Buf vecSrcRest vecCopyDone protoChainAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm]
theorem bv_add_neg80_2_x (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 :=
  (BitVec.sub_eq_add_neg x 80#64).symm

theorem sepWPpIn_extract_chainAt_cap {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {gc : ChainGhost × ReceiverChain} {a : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfocus : P = protoChainAt A gc a ∗ F := by sep_frame)
    (h : gc.1.srk.cap.toNat < 2 ^ 63 → SepWPpIn img prog ret s P Q Qp) :
    SepWPpIn img prog ret s P Q Qp := by
  intro hF hsym
  exact sepWPp_extract_chainAt_cap hfocus fun h1 => h h1 hF hsym

theorem sepWPpIn_extract_vecAt_chains_bounds {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {a cap ptr : BitVec 64} {gcs : List (ChainGhost × ReceiverChain)}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hfocus : P = vecAt A 104 8 (chainAt A) a cap ptr gcs ∗ F := by sep_frame)
    (h : gcs.length ≤ cap.toNat → cap.toNat * 104 < 2 ^ 63 → SepWPpIn img prog ret s P Q Qp) :
    SepWPpIn img prog ret s P Q Qp := by
  intro hF hsym
  exact sepWPp_extract_vecAt_chains_bounds hfocus fun hle hmul => h hle hmul hF hsym

theorem L1_EncodeRawSenderReceiverChainsX : True := trivial

/-! ## Tag 6 (`sender_chain`, `+0x1cc → +0x1e8`) -/

/-- Tag 6 (`+0x1cc..+0x1e8`): encodes `sender_chain` (`optSenderChainAt` at `ss + 0x90`) via
`encode::<Chain>` with tag `6` when `Some`, or skips when `None` (`noneCap`). -/
theorem step_encraw_tag6_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hEC : EncodeChainOkX img A ext)
    (ss v sp0 cap ptr : BitVec 64)
    (senderG : Option SenderChainGhost) (sender : Option SenderChain)
    (bs : List (BitVec 8))
    (hlen_lt : bs.length + (encSenderFieldMem senderG sender).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeRawName + 460#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (optSenderChainAt A (ss + 0x90#64) senderG sender ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr encodeRawName + 488#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((optSenderChainAt A (ss + 0x90#64) senderG sender ∗
          vecU8At A v cap' ptr' (bs ++ encSenderFieldMem senderG sender) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hCallEC := @encraw_call_protoEncodeChain_x img A ext hEC
  encraw_fetches_range img.base (Rust.withPanics ext) 460 488
  generalize_entry (SP2Ext img.base ext).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  cases senderG with
  | none =>
    cases sender with
    | none =>
      simp only [optSenderChainAt, noneCap, sepConj_assoc]
      apply SepWPpIn.of_sepWP (mid := entry + bv% (488))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hPost :
          ((ss + 144#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ memRegion (ss + 144#64 + 8#64) 96 ∗
          vecU8At A v cap ptr bs ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX ∗ F =
          (optSenderChainAt A (ss + 0x90#64) none none ∗
            vecU8At A v cap ptr (bs ++ encSenderFieldMem none none) ∗
            A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by
        simp only [optSenderChainAt, noneCap, encSenderFieldMem, List.append_nil, sepConj_assoc]
      rw [hPost]
      exact hnext _ cap ptr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
    | some sc =>
      simp only [optSenderChainAt, sepConj_assoc]
      exact SepWPpIn.pure_elim fun h => False.elim h
  | some g =>
    cases sender with
    | none =>
      simp only [optSenderChainAt, sepConj_assoc]
      exact SepWPpIn.pure_elim fun h => False.elim h
    | some sc =>
      rw [optSenderChainAt_some_eq_chainAt_er A (ss + 0x90#64) g sc]
      simp only [sepConj_assoc]
      refine SepWPpIn.pure_elim fun hpriv => ?_
      refine sepWPpIn_extract_chainAt_cap (A := A) (gc := (senderGhostAsChain g, senderAsChain sc))
        (a := ss + 0x90#64) (h := fun hcap => ?_)
      have hcmn1 := cmn1_beq_zero_false hcap
      have hcmn2 := cap_beq_noneCap_false hcap
      rw [chainAt_open_cap A (senderGhostAsChain g, senderAsChain sc) (ss + 0x90#64)]
      simp only [sepConj_assoc]
      apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [chainAt_close_cap A (senderGhostAsChain g, senderAsChain sc) (ss + 0x90#64)]
      refine hCallEC 6 sp0 (ss + 0x90#64) v cap ptr (entry + bv% (488))
        (senderGhostAsChain g, senderAsChain sc) bs (Or.inl rfl) hlen_lt
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · intro sm cap' ptr' hpcm hrunm hspm htrm hcsm
        have hx19m : sm.readReg64 .x19 = v := by
          have := hcsm.1; simp only [arm64_norm, *] at this; exact this
        have hx20m : sm.readReg64 .x20 = ss := by
          have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
        have hcsm' : EncRawUpperSaved s0 sm :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
        have hRestore :
            (protoChainAt A (senderGhostAsChain g, senderAsChain sc) (ss + 0x90#64) ∗
              vecU8At A v cap' ptr' (bs ++ lenField 6 (encChainMem (senderGhostAsChain g, senderAsChain sc))) ∗
              A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F =
            (optSenderChainAt A (ss + 0x90#64) (some g) (some sc) ∗
              vecU8At A v cap' ptr' (bs ++ encSenderFieldMem (some g) (some sc)) ∗
              A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by
          rw [optSenderChainAt_some_eq_chainAt_er A (ss + 0x90#64) g sc, eq_true hpriv,
              pure_true, emp_sepConj]
          rfl
        rw [hRestore]
        exact hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm'

/-! ## Tag 7 (`receiver_chains` loop, `+0x1e8 → +0x218`) -/

theorem step_encraw_tag7_loop_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hEC : EncodeChainOkX img A ext)
    (gcs : List (ChainGhost × ReceiverChain))
    (hne : gcs ≠ [])
    (ss v sp0 curPtr cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hmul_lt : gcs.length * 104 < 2 ^ 63)
    (hlen_lt : bs.length + ((gcs.map fun gc => lenField 7 (encChainMem gc)).flatten).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeRawName + 508#64)
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
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr encodeRawName + 536#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((arrayAt (chainAt A) 104 curPtr gcs ∗
          vecU8At A v cap' ptr' (bs ++ (gcs.map fun gc => lenField 7 (encChainMem gc)).flatten) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q (PanicAllocPost s0) := by
  induction gcs generalizing curPtr cap ptr bs s P F with
  | nil => exact False.elim (hne rfl)
  | cons gc rest ih =>
    have hCallEC := @encraw_call_encodeChain_x img A ext hEC
    encraw_fetches_range img.base (Rust.withPanics ext) 508 536
    generalize_entry (SP2Ext img.base ext).fnAddr encodeRawName = entry
    examples_hide_fetches
    rw [hP]
    simp only [arrayAt, sepConj_assoc]
    have hlen_head := len_head_lt_of_cons hlen_lt
    apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine hCallEC 7 sp0 curPtr v cap ptr (entry + bv% (524)) gc bs (Or.inr rfl) hlen_head
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hcs1
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
        apply SepWPpIn.of_sepWP (mid := entry + bv% (536))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine SepWPpIn.weaken_pre ?_ (hnext _ cap1 ptr1
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        simp only [arrayAt, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
          List.append_nil, emp_sepConj, sepConj_emp, sepConj_assoc]
        exact (by sep_frame)
      | cons gc2 rest' =>
        have hne_rest : (gc2 :: rest') ≠ [] := List.cons_ne_nil _ _
        have hsub := bv_cons_len_mul_104_sub gc (gc2 :: rest')
        have hmul_rest := mul_104_cons_lt hmul_lt
        have hbeq0 := bv_mul_104_beq_zero_false hne_rest hmul_rest
        have hbeq104 := bv_cons_len_mul_104_beq_104_false gc hne_rest hmul_lt
        have hbne104 := bv_cons_len_mul_104_bne_104_true gc hne_rest hmul_lt
        apply SepWPpIn.of_sepWP (mid := entry + bv% (508))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        have hlen_rest := len_rest_lt_of_cons hlen_lt
        refine ih (F := chainAt A gc curPtr ∗ F) hne_rest (curPtr + 104#64) cap1 ptr1
          (bs ++ lenField 7 (encChainMem gc)) hmul_rest hlen_rest
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
          (by sep_frame) ?_
        intro sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm'
        refine SepWPpIn.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm')
        simp only [arrayAt, List.map_cons, List.flatten_cons, List.append_assoc, sepConj_assoc]
        exact (by sep_frame)

/-- Tag 7 (`+0x1e8..+0x218`, `488..536`): encodes all receiver chains in
`vecAt A 104 8 (chainAt A) (ss + 0x48#64) cCap cPtr gcs` with tag `7` into `v`. -/
theorem step_encraw_tag7_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hEC : EncodeChainOkX img A ext)
    (ss v sp0 cCap cPtr cap ptr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (bs : List (BitVec 8))
    (hlen_lt : bs.length + ((gcs.map fun gc => lenField 7 (encChainMem gc)).flatten).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeRawName + 488#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecAt A 104 8 (chainAt A) (ss + 0x48#64) cCap cPtr gcs ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr encodeRawName + 536#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecAt A 104 8 (chainAt A) (ss + 0x48#64) cCap cPtr gcs ∗
          vecU8At A v cap' ptr' (bs ++ (gcs.map fun gc => lenField 7 (encChainMem gc)).flatten) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hLoop := @step_encraw_tag7_loop_x img A ext hEC
  encraw_fetches_range img.base (Rust.withPanics ext) 488 508
  generalize_entry (SP2Ext img.base ext).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  refine sepWPpIn_extract_vecAt_chains_bounds (A := A) (a := ss + 0x48#64)
    (cap := cCap) (ptr := cPtr) (gcs := gcs) (h := fun hle hcap_mul => ?_)
  by_cases hgcs : gcs = []
  · subst hgcs
    rw [vecAt_chains_nil A ss cCap cPtr]
    simp only [sepConj_assoc]
    apply SepWPpIn.of_sepWP (mid := entry + bv% (536))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [show
        ((ss + 72#64) ↦₆₄ cCap) ∗ ((ss + 80#64) ↦₆₄ cPtr) ∗ ((ss + 88#64) ↦₆₄ 0#64) ∗
        vecBuf A 104 8 (chainAt A) cCap cPtr [] ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
        stackAt (sp0 - 80#64) encodeRawSubStackX ∗ F =
        (vecAt A 104 8 (chainAt A) (ss + 0x48#64) cCap cPtr [] ∗ vecU8At A v cap ptr bs ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F by
      rw [vecAt_chains_nil A ss cCap cPtr]; simp only [sepConj_assoc]]
    simpa only [List.map_nil, List.flatten_nil, List.append_nil] using
      hnext _ cap ptr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  · have hbeq0 := ofNat64_chains_len_beq_zero_false hgcs (by omega)
    have hmul := bv_len_mul_104 gcs.length
    rw [vecAt_chains_open A ss cCap cPtr gcs hgcs hle]
    simp only [sepConj_assoc]
    apply SepWPpIn.of_sepWP (mid := entry + bv% (508))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine hLoop gcs hgcs ss v sp0 cPtr cap ptr bs (by omega) hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
      (by sep_frame) ?_
    intro sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm'
    refine SepWPpIn.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm')
    rw [vecAt_chains_open A ss cCap cPtr gcs hgcs hle]
    exact (by sep_frame)

/-! ## Relocatable `[LibsignalPlacement]` proofs (Block `14`, Tags 6 and 7) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem sepWPpLsCl_extract_chainAt_cap {pl : MultiPlacement} {prog : Program} {ret : BitVec 64}
    {s : State} {A : RustAlloc} {gc : ChainGhost × ReceiverChain} {a : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfocus : P = protoChainAt A gc a ∗ F := by sep_frame)
    (h : gc.1.srk.cap.toNat < 2 ^ 63 → SepWPpLsCl pl prog ret s P Q Qp) :
    SepWPpLsCl pl prog ret s P Q Qp := by
  intro hcl
  exact sepWPp_extract_chainAt_cap hfocus fun h1 => h h1 hcl

theorem sepWPpLsCl_extract_vecAt_chains_bounds {pl : MultiPlacement} {prog : Program}
    {ret : BitVec 64} {s : State} {A : RustAlloc} {a cap ptr : BitVec 64}
    {gcs : List (ChainGhost × ReceiverChain)} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hfocus : P = vecAt A 104 8 (chainAt A) a cap ptr gcs ∗ F := by sep_frame)
    (h : gcs.length ≤ cap.toNat → cap.toNat * 104 < 2 ^ 63 → SepWPpLsCl pl prog ret s P Q Qp) :
    SepWPpLsCl pl prog ret s P Q Qp := by
  intro hcl
  exact sepWPp_extract_vecAt_chains_bounds hfocus fun hle hmul => h hle hmul hcl

theorem step_encraw_tag6_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hEC : EncodeChainPlacedOkX A H)
    (ss v sp0 cap ptr : BitVec 64)
    (senderG : Option SenderChainGhost) (sender : Option SenderChain)
    (bs : List (BitVec 8))
    (hlen_lt : bs.length + (encSenderFieldMem senderG sender).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 460#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (optSenderChainAt A (ss + 0x90#64) senderG sender ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_14).base + 488#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((optSenderChainAt A (ss + 0x90#64) senderG sender ∗
          vecU8At A v cap' ptr' (bs ++ encSenderFieldMem senderG sender) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hCallEC := @encraw_call_protoEncodeChain_placed_x _ A H hEC
  rw [hP]
  cases senderG with
  | none =>
    cases sender with
    | none =>
      simp only [optSenderChainAt, noneCap, sepConj_assoc]
      apply SepWPpLsCl.of_sepWP (mid := (blkPl_14).base + 488#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hPost :
          ((ss + 144#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ memRegion (ss + 144#64 + 8#64) 96 ∗
          vecU8At A v cap ptr bs ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX ∗ F =
          (optSenderChainAt A (ss + 0x90#64) none none ∗
            vecU8At A v cap ptr (bs ++ encSenderFieldMem none none) ∗
            A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by
        simp only [optSenderChainAt, noneCap, encSenderFieldMem, List.append_nil, sepConj_assoc]
      rw [hPost]
      exact hnext _ cap ptr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
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
      refine sepWPpLsCl_extract_chainAt_cap (A := A) (gc := (senderGhostAsChain g, senderAsChain sc))
        (a := ss + 0x90#64) (h := fun hcap => ?_)
      have hcmn1 := cmn1_beq_zero_false hcap
      have hcmn2 := cap_beq_noneCap_false hcap
      rw [chainAt_open_cap A (senderGhostAsChain g, senderAsChain sc) (ss + 0x90#64)]
      simp only [sepConj_assoc]
      apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 12)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [chainAt_close_cap A (senderGhostAsChain g, senderAsChain sc) (ss + 0x90#64)]
      refine hCallEC 6 sp0 (ss + 0x90#64) v cap ptr ((blkPl_14).base + 488#64)
        (senderGhostAsChain g, senderAsChain sc) bs (Or.inl rfl) hlen_lt
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · intro sm cap' ptr' hpcm hrunm hspm htrm hcsm
        have hx19m : sm.readReg64 .x19 = v := by
          have := hcsm.1; simp only [arm64_norm, *] at this; exact this
        have hx20m : sm.readReg64 .x20 = ss := by
          have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
        have hcsm' : EncRawUpperSaved s0 sm :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
        have hRestore :
            (protoChainAt A (senderGhostAsChain g, senderAsChain sc) (ss + 0x90#64) ∗
              vecU8At A v cap' ptr' (bs ++ lenField 6 (encChainMem (senderGhostAsChain g, senderAsChain sc))) ∗
              A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F =
            (optSenderChainAt A (ss + 0x90#64) (some g) (some sc) ∗
              vecU8At A v cap' ptr' (bs ++ encSenderFieldMem (some g) (some sc)) ∗
              A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by
          rw [optSenderChainAt_some_eq_chainAt_er A (ss + 0x90#64) g sc, eq_true hpriv,
              pure_true, emp_sepConj]
          rfl
        rw [hRestore]
        exact hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm'

theorem step_encraw_tag7_loop_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hEC : EncodeChainPlacedOkX A H)
    (gcs : List (ChainGhost × ReceiverChain))
    (hne : gcs ≠ [])
    (ss v sp0 curPtr cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hmul_lt : gcs.length * 104 < 2 ^ 63)
    (hlen_lt : bs.length + ((gcs.map fun gc => lenField 7 (encChainMem gc)).flatten).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
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
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_14).base + 536#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((arrayAt (chainAt A) 104 curPtr gcs ∗
          vecU8At A v cap' ptr' (bs ++ (gcs.map fun gc => lenField 7 (encChainMem gc)).flatten) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  induction gcs generalizing curPtr cap ptr bs s P F with
  | nil => exact False.elim (hne rfl)
  | cons gc rest ih =>
    have hCallEC := @encraw_call_encodeChain_placed_x _ A H hEC
    rw [hP]
    simp only [arrayAt, sepConj_assoc]
    have hlen_head := len_head_lt_of_cons hlen_lt
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 12)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine hCallEC 7 sp0 curPtr v cap ptr ((blkPl_14).base + 524#64) gc bs (Or.inr rfl) hlen_head
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hcs1
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
        apply SepWPpLsCl.of_sepWP (mid := (blkPl_14).base + 536#64)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap1 ptr1
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        simp only [arrayAt, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
          List.append_nil, emp_sepConj, sepConj_emp, sepConj_assoc]
        exact (by sep_frame)
      | cons gc2 rest' =>
        have hne_rest : (gc2 :: rest') ≠ [] := List.cons_ne_nil _ _
        have hsub := bv_cons_len_mul_104_sub gc (gc2 :: rest')
        have hmul_rest := mul_104_cons_lt hmul_lt
        have hbeq0 := bv_mul_104_beq_zero_false hne_rest hmul_rest
        have hbeq104 := bv_cons_len_mul_104_beq_104_false gc hne_rest hmul_lt
        have hbne104 := bv_cons_len_mul_104_bne_104_true gc hne_rest hmul_lt
        apply SepWPpLsCl.of_sepWP (mid := (blkPl_14).base + 508#64)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        have hlen_rest := len_rest_lt_of_cons hlen_lt
        refine ih (F := chainAt A gc curPtr ∗ F) hne_rest (curPtr + 104#64) cap1 ptr1
          (bs ++ lenField 7 (encChainMem gc)) hmul_rest hlen_rest
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
          (by sep_frame) ?_
        intro sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm'
        refine SepWPpLsCl.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm')
        simp only [arrayAt, List.map_cons, List.flatten_cons, List.append_assoc, sepConj_assoc]
        exact (by sep_frame)

theorem step_encraw_tag7_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hEC : EncodeChainPlacedOkX A H)
    (ss v sp0 cCap cPtr cap ptr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (bs : List (BitVec 8))
    (hlen_lt : bs.length + ((gcs.map fun gc => lenField 7 (encChainMem gc)).flatten).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 488#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecAt A 104 8 (chainAt A) (ss + 0x48#64) cCap cPtr gcs ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_14).base + 536#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecAt A 104 8 (chainAt A) (ss + 0x48#64) cCap cPtr gcs ∗
          vecU8At A v cap' ptr' (bs ++ (gcs.map fun gc => lenField 7 (encChainMem gc)).flatten) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hLoop := @step_encraw_tag7_loop_placed_x _ A H hEC
  rw [hP]
  refine sepWPpLsCl_extract_vecAt_chains_bounds (A := A) (a := ss + 0x48#64)
    (cap := cCap) (ptr := cPtr) (gcs := gcs) (h := fun hle _ => ?_)
  by_cases hgcs : gcs = []
  · subst hgcs
    rw [vecAt_chains_nil A ss cCap cPtr]
    simp only [sepConj_assoc]
    apply SepWPpLsCl.of_sepWP (mid := (blkPl_14).base + 536#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [show
        ((ss + 72#64) ↦₆₄ cCap) ∗ ((ss + 80#64) ↦₆₄ cPtr) ∗ ((ss + 88#64) ↦₆₄ 0#64) ∗
        vecBuf A 104 8 (chainAt A) cCap cPtr [] ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
        stackAt (sp0 - 80#64) encodeRawSubStackX ∗ F =
        (vecAt A 104 8 (chainAt A) (ss + 0x48#64) cCap cPtr [] ∗ vecU8At A v cap ptr bs ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F by
      rw [vecAt_chains_nil A ss cCap cPtr]; simp only [sepConj_assoc]]
    simpa only [List.map_nil, List.flatten_nil, List.append_nil] using
      hnext _ cap ptr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  · have hbeq0 := ofNat64_chains_len_beq_zero_false hgcs (by omega)
    have hmul := bv_len_mul_104 gcs.length
    rw [vecAt_chains_open A ss cCap cPtr gcs hgcs hle]
    simp only [sepConj_assoc]
    apply SepWPpLsCl.of_sepWP (mid := (blkPl_14).base + 508#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine hLoop gcs hgcs ss v sp0 cPtr cap ptr bs (by omega) hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
      (by sep_frame) ?_
    intro sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm'
    refine SepWPpLsCl.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm')
    rw [vecAt_chains_open A ss cCap cPtr gcs hgcs hle]
    exact (by sep_frame)

end Placed

end CryptoVerification.E2E.Record.Serialization
