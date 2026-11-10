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
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymF
public import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.MessageKeyLoopBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.SenderReceiverChainsBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.MsgKeyLenBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DefsBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.ChainKeyFieldXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.MessageKeyLoopBodyXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.MessageKeyLoopX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.PrologueSenderRatchetKeyXABudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.PrologueSenderRatchetKeyXBBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseXBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `encode::<Chain, Vec<u8>>` `message_keys` Loop and Top-Level Contract

Verifies the inductive `message_keys` loop (`+600 → +1648`), epilogue (`+1648 → ret`), and
top-level Block `12` specifications (`EncodeChainSegPlacedOkX` and `EncodeChainPlacedOkX`) under
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.MessageKeyLoopXBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (PublicKey MessageKeyGenerator ReceiverChain maxMessageKeys)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg lsmpl withLsCodeLoaded withLsCl
  subroutine_ok_withLsCodeLoaded_of_plain
)
open CryptoVerification.RustHeap (RustAlloc vecAt vecBuf vecU8At arrayAt)
open CryptoVerification.LibsignalSessionRepr (
  ChainGhost MessageKeyGhost messageKeyAt vecGhostAt optChainKeyAt
)
open CryptoVerification.LibsignalProtoCodec (encodeKey encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (ls_subroutine_ok_cl_of_callee)
open CryptoVerification.E2E.Record (bytesField msgField lenField encChainKey encMessageKey)
open CryptoVerification.E2E.Record.Placed (blkPl_12 lsProg_12 blkPl_88 lsProg_88 blkPl_118 lsProg_118)
open CryptoVerification.E2E.Record.Serialization (
  EncodeChainGhost encChainMem protoChainAt encChainSubStackX encChainSavedRegs
  stackAt_encodeChainStackX_split sp_sub_96_aligned MkLoopRegs
  mk_endPtr_step mk_endPtr_ne_of_pos zip_length_eq_right zip_map_snd_eq_encChain
  chainMkUnusedAt chainAt_eq_mk_cells vecMkRest vecBuf_mk_eq_open
  sepWPpLsCl_extract_chain_mk_bounds_x sepWPpLsCl_extract_vecBuf_mk_le_x
)
open Proofs.libsignal.Hooks2 (SepWPpLsCl)
open LibsignalBinary.Heap (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv)
open LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenBudget (chainLen_placed_ok)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (
  EncodeChainEnv chainLenSpec msgKeyLenSpec
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.MsgKeyLenBudget (msgKeyLen_placed_ok)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget (
  EncRawSegEnv encRawSegEnv_nil encRawSegEnv_append fitsEnv_encRawSeg_left fitsEnv_encRawSeg_right
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.SenderReceiverChainsBudget (
  encodeChainSegEnv encodeChainSegEnv_sub_encodeChainEnv
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.MessageKeyLoopBudget (
  step_encChain_mk_next_eq_placed step_encChain_mk_next_ne_placed
  step_encChain_seg4_empty_placed step_encChain_seg4_init_placed
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DefsBudget (
  subroutine_ok_withLsCodeLoaded_map_oom'
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  encodeChainStackX SerContractsXPlaced encodeChainSpecX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  EncodeVarintPlacedOkX DoReservePlacedOkX EncodeChainPlacedOkX
  subroutine_ok_withLsCodeLoaded_of_sepWPpLsCl
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget (
  sepWPpLsCl_of_sepWP_vm sepWPpLsCl_transport_budgetPool
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.PrologueSenderRatchetKeyXABudget (
  step_encChain_seg0_raw_placed_x step_encChain_seg1_placed_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.PrologueSenderRatchetKeyXBBudget (
  step_encChain_seg2_placed_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.ChainKeyFieldXBudget (
  step_encChain_seg3_placed_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.MessageKeyLoopBodyXBudget (
  step_encChain_mk_elem_placed_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseXBudget (
  encodeChainSpecWithEnvX encodeChainSpecWithEnvX_eq
)

private theorem bv_sub_add_lit (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Pure bounds helpers -/

private theorem mk_len_tl_lt {α : Type} (x : α) (xs : List α)
    (h : (x :: xs).length * 104 < 2 ^ 32) :
    xs.length * 104 < 2 ^ 32 := by
  simp only [List.length_cons] at h
  omega

private theorem mk_bound_head (curBs : List (BitVec 8))
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (tl : List (MessageKeyGhost × MessageKeyGenerator))
    (hbound : curBs.length +
      (((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length < 2 ^ 32) :
    curBs.length + (lenField 4 (encMessageKey gk.2)).length < 2 ^ 32 := by
  simp only [List.map_cons, List.flatten_cons, List.length_append] at hbound
  omega

private theorem mk_bound_tail (curBs : List (BitVec 8))
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (tl : List (MessageKeyGhost × MessageKeyGenerator))
    (hbound : curBs.length +
      (((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length < 2 ^ 32) :
    (curBs ++ lenField 4 (encMessageKey gk.2)).length +
      ((tl.map (fun p => lenField 4 (encMessageKey p.2))).flatten).length < 2 ^ 32 := by
  simp only [List.map_cons, List.flatten_cons, List.length_append] at hbound ⊢
  omega

private theorem mk_flatten_nil_len (gk : MessageKeyGhost × MessageKeyGenerator) :
    ((([gk]).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length =
      (lenField 4 (encMessageKey gk.2)).length := by
  simp

private theorem mk_flatten_cons_len (gk : MessageKeyGhost × MessageKeyGenerator)
    (tl : List (MessageKeyGhost × MessageKeyGenerator)) :
    (((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length =
      (lenField 4 (encMessageKey gk.2)).length +
        ((tl.map (fun p => lenField 4 (encMessageKey p.2))).flatten).length := by
  simp [List.length_append]

private def chainAtRest (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) : SepProp :=
  ⌜PublicKey.deserialize gc.1.srk.bytes = Except.ok gc.2.senderRatchetKey ∧
    gc.2.messageKeys.length ≤ maxMessageKeys ∧ gc.1.keys.length = gc.2.messageKeys.length⌝ ∗
    vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
      (gc.1.keys.zip gc.2.messageKeys)

private theorem chainAt_eq_fields (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    protoChainAt A gc a =
      vecGhostAt A gc.1.srk a ∗
      vecGhostAt A gc.1.priv (a + 24#64) ∗
      optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64) ∗
      chainAtRest A gc a := by
  unfold protoChainAt chainAtRest
  sep_ac_rfl

private theorem encChain_encodeKey_len {tag : Nat} (htag : tag = 6 ∨ tag = 7) :
    (encodeKey tag .lengthDelimited).length = 1 := by
  rcases htag with rfl | rfl <;> decide

private theorem encChain_bound_seg1 (x : EncodeChainGhost)
    (hlen : x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32) :
    (x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)).length +
      (bytesField 1 x.gc.1.srk.bytes).length < 2 ^ 32 := by
  simp only [lenField, encChainMem, List.length_append] at hlen ⊢
  omega

private theorem encChain_bound_seg2 (x : EncodeChainGhost)
    (hlen : x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32) :
    ((x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ++
      bytesField 1 x.gc.1.srk.bytes).length +
      (bytesField 2 x.gc.1.priv.bytes).length < 2 ^ 32 := by
  simp only [lenField, encChainMem, List.length_append] at hlen ⊢
  omega

private theorem encChain_bound_seg3 (x : EncodeChainGhost)
    (hlen : x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32) :
    (((x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ++
      bytesField 1 x.gc.1.srk.bytes) ++
      bytesField 2 x.gc.1.priv.bytes).length +
      (msgField 3 (x.gc.2.chainKey.map encChainKey)).length < 2 ^ 32 := by
  simp only [lenField, encChainMem, List.length_append] at hlen ⊢
  omega

private theorem encChain_bound_seg4 (x : EncodeChainGhost)
    (hlen : x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32) :
    ((((x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ++
      bytesField 1 x.gc.1.srk.bytes) ++
      bytesField 2 x.gc.1.priv.bytes) ++
      msgField 3 (x.gc.2.chainKey.map encChainKey)).length +
      ((x.gc.2.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten).length < 2 ^ 32 := by
  simp only [lenField, encChainMem, List.length_append] at hlen ⊢
  omega

private theorem encChain_final_bytes_eq (x : EncodeChainGhost) :
    (((((x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ++
      bytesField 1 x.gc.1.srk.bytes) ++
      bytesField 2 x.gc.1.priv.bytes) ++
      msgField 3 (x.gc.2.chainKey.map encChainKey)) ++
      (x.gc.2.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten) =
    x.bs ++ lenField x.tag (encChainMem x.gc) := by
  simp only [lenField, encChainMem, List.append_assoc]

/-! ## Loop back-edge and inductive `message_keys` loop (`+668..+1648`) -/

theorem step_encChain_mk_next_eq_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (v cur endPtr sp0 : BitVec 64) (st : M.σ)
    (heq : ((cur + 104#64) == endPtr) = true)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 668#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = A.pool lim st s ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_12).base + 1648#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm (A.pool lim st sm ∗ F) Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp :=
  fun hcl => step_encChain_mk_next_eq_placed A lim H v cur endPtr sp0 st heq
    hpc hrun hcl hsp htr hregs hP
    fun sm hpcm hrunm hclm hspm htrm => hnext sm hpcm hrunm hspm htrm hclm

theorem step_encChain_mk_next_ne_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (v cur endPtr sp0 : BitVec 64) (st : M.σ)
    (hne : ((cur + 104#64) == endPtr) = false)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 668#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = A.pool lim st s ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_12).base + 680#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v (cur + 104#64) endPtr →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm (A.pool lim st sm ∗ F) Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp :=
  fun hcl => step_encChain_mk_next_ne_placed A lim H v cur endPtr sp0 st hne
    hpc hrun hcl hsp htr hregs hP
    fun sm hpcm hrunm hclm hspm htrm hregsm => hnext sm hpcm hrunm hspm htrm hregsm hclm

theorem step_encChain_mk_loop_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (hC : SerContractsXPlaced M A lim H)
    (hmk : subroutine_ok (lsProg_118 H) (blkPl_118).base
      (withLsCodeLoaded lsmpl (msgKeyLenSpec A.repAlloc)))
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (tl : List (MessageKeyGhost × MessageKeyGenerator))
    (v cur endPtr curCap curPtr sp0 : BitVec 64)
    (curBs : List (BitVec 8)) (st : M.σ)
    (hend : endPtr = cur + BitVec.ofNat 64 ((gk :: tl).length * 104))
    (hlen_mk : (gk :: tl).length * 104 < 2 ^ 32)
    (hbound : curBs.length +
      (((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length < 2 ^ 32)
    (hfit : FitsEnv M lim st
      (EncRawSegEnv curBs.length
        (((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 680#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗
      arrayAt (messageKeyAt A.repAlloc) 104 cur (gk :: tl) ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (capOut ptrOut : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_12).base + 1648#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      EncRawSegEnv curBs.length
        (((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length evs →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc v capOut ptrOut
          (curBs ++ ((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten) ∗
          arrayAt (messageKeyAt A.repAlloc) 104 cur (gk :: tl) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  induction tl generalizing gk cur curCap curPtr curBs st s P F with
  | nil =>
    have hbound1 := mk_bound_head curBs gk [] hbound
    have hfit1 : FitsEnv M lim st
        (EncRawSegEnv curBs.length (lenField 4 (encMessageKey gk.2)).length) := by
      rwa [mk_flatten_nil_len] at hfit
    have heq_end : ((cur + 104#64) == endPtr) = true := by
      rw [hend]; simp
    refine step_encChain_mk_elem_placed_x A lim H hC hmk hEV hDR
      v cur endPtr curCap curPtr sp0 gk curBs st hbound1 hfit1
      (s0 := s0) (F := F) hpc hrun hsp halign htr hregs
      (by rw [hP]; simp only [arrayAt, sepConj_emp]) ?_
    intro s1 cap1 ptr1 evs1 hpc1 hrun1 hsp1 htr1 hregs1 hevs1
    refine step_encChain_mk_next_eq_placed_x A lim H v cur endPtr sp0 (M.stepEvents evs1 st) heq_end
      (s0 := s0)
      (F := vecU8At A.repAlloc v cap1 ptr1 (curBs ++ lenField 4 (encMessageKey gk.2)) ∗
        messageKeyAt A.repAlloc gk cur ∗
        stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
      hpc1 hrun1 hsp1 htr1 hregs1 (by sep_ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm
    have hevs_out : EncRawSegEnv curBs.length
        ((([gk]).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length evs1 := by
      rwa [mk_flatten_nil_len]
    refine SepWPpLsCl.congr_pre ?_ (hnext sm cap1 ptr1 evs1 hpcm hrunm hspm htrm hevs_out)
    simp only [arrayAt, sepConj_emp, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil]
    sep_ac_rfl
  | cons gk2 tl2 ih =>
    have hbound1 := mk_bound_head curBs gk (gk2 :: tl2) hbound
    have hlen_tl := mk_len_tl_lt gk (gk2 :: tl2) hlen_mk
    have hbound_tl := mk_bound_tail curBs gk (gk2 :: tl2) hbound
    have hfit12 : FitsEnv M lim st
        (EncRawSegEnv curBs.length
          ((lenField 4 (encMessageKey gk.2)).length +
            (((gk2 :: tl2).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length)) := by
      rwa [mk_flatten_cons_len] at hfit
    have hfit1 : FitsEnv M lim st
        (EncRawSegEnv curBs.length (lenField 4 (encMessageKey gk.2)).length) :=
      fitsEnv_encRawSeg_left hfit12
    refine step_encChain_mk_elem_placed_x A lim H hC hmk hEV hDR
      v cur endPtr curCap curPtr sp0 gk curBs st hbound1 hfit1
      (s0 := s0)
      (F := arrayAt (messageKeyAt A.repAlloc) 104 (cur + 104#64) (gk2 :: tl2) ∗ F)
      hpc hrun hsp halign htr hregs
      (by rw [hP]; simp only [arrayAt]; sep_ac_rfl) ?_
    intro s1 cap1 ptr1 evs1 hpc1 hrun1 hsp1 htr1 hregs1 hevs1
    have hend_step : endPtr = (cur + 104#64) + BitVec.ofNat 64 ((gk2 :: tl2).length * 104) := by
      rw [hend]
      exact mk_endPtr_step cur (gk2 :: tl2).length
    have hne_end : ((cur + 104#64) == endPtr) = false := by
      rw [hend_step]
      exact mk_endPtr_ne_of_pos cur (gk2 :: tl2).length (by simp) hlen_tl
    have hfit_tl : FitsEnv M lim (M.stepEvents evs1 st)
        (EncRawSegEnv (curBs ++ lenField 4 (encMessageKey gk.2)).length
          (((gk2 :: tl2).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length) := by
      rw [List.length_append]
      exact fitsEnv_encRawSeg_right hfit12 hevs1
    refine step_encChain_mk_next_ne_placed_x A lim H v cur endPtr sp0 (M.stepEvents evs1 st) hne_end
      (s0 := s0)
      (F := vecU8At A.repAlloc v cap1 ptr1 (curBs ++ lenField 4 (encMessageKey gk.2)) ∗
        messageKeyAt A.repAlloc gk cur ∗
        stackAt (sp0 - 96#64) encChainSubStackX ∗
        arrayAt (messageKeyAt A.repAlloc) 104 (cur + 104#64) (gk2 :: tl2) ∗ F)
      hpc1 hrun1 hsp1 htr1 hregs1 (by sep_ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hregs2
    refine ih gk2 (cur + 104#64) cap1 ptr1 (curBs ++ lenField 4 (encMessageKey gk.2))
      (M.stepEvents evs1 st) hend_step hlen_tl hbound_tl hfit_tl
      (F := messageKeyAt A.repAlloc gk cur ∗ F)
      hpc2 hrun2 hsp2 htr2 hregs2
      (by sep_ac_rfl) ?_
    intro sm capOut ptrOut evs2 hpcm hrunm hspm htrm hevs2
    have hevs2' : EncRawSegEnv (curBs.length + (lenField 4 (encMessageKey gk.2)).length)
        (((gk2 :: tl2).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length evs2 := by
      rwa [List.length_append] at hevs2
    have hevs_all : EncRawSegEnv curBs.length
        (((gk :: gk2 :: tl2).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length
        (evs1 ++ evs2) := by
      rw [mk_flatten_cons_len]
      exact encRawSegEnv_append hevs1 hevs2'
    refine SepWPpLsCl.congr_pre ?_
      (hnext sm capOut ptrOut (evs1 ++ evs2) hpcm hrunm hspm htrm hevs_all)
    simp only [arrayAt, List.map_cons, List.flatten_cons, List.append_assoc, M.stepEvents_append]
    sep_ac_rfl

/-! ## Segment 4 (`+600 → +1648`) and epilogue (`+1648 → ret`) -/

theorem step_encChain_seg4_empty_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (a sp0 : BitVec 64) (st : M.σ)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 600#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (((a + 64#64) ↦₆₄ 0#64) ∗ A.pool lim st s) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_12).base + 1648#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm ((((a + 64#64) ↦₆₄ 0#64) ∗ A.pool lim st sm) ∗ F) Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp :=
  fun hcl => step_encChain_seg4_empty_placed A lim H a sp0 st hpc hrun hcl hsp htr hx20 hP
    fun sm hpcm hrunm hclm hspm htrm => hnext sm hpcm hrunm hspm htrm hclm

theorem step_encChain_seg4_init_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (v a mkPtr sp0 : BitVec 64) (n : Nat) (st : M.σ)
    (hpos : 0 < n) (hlt : n < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 600#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (((a + 56#64) ↦₆₄ mkPtr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 n) ∗ A.pool lim st s) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_12).base + 680#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v mkPtr (mkPtr + BitVec.ofNat 64 (n * 104)) →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((((a + 56#64) ↦₆₄ mkPtr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 n) ∗ A.pool lim st sm) ∗ F) Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp :=
  fun hcl => step_encChain_seg4_init_placed A lim H v a mkPtr sp0 n st hpos hlt
    hpc hrun hcl hsp htr hx19 hx20 hP
    fun sm hpcm hrunm hclm hspm htrm hregsm => hnext sm hpcm hrunm hspm htrm hregsm hclm

theorem step_encChain_seg4_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (hC : SerContractsXPlaced M A lim H)
    (hmk : subroutine_ok (lsProg_118 H) (blkPl_118).base
      (withLsCodeLoaded lsmpl (msgKeyLenSpec A.repAlloc)))
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (v a curCap curPtr sp0 : BitVec 64) (gc : ChainGhost × ReceiverChain)
    (curBs : List (BitVec 8)) (st : M.σ)
    (hbound : curBs.length +
      ((gc.2.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten).length < 2 ^ 32)
    (hfit : FitsEnv M lim st
      (EncRawSegEnv curBs.length
        ((gc.2.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten).length))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 600#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗
      protoChainAt A.repAlloc gc a ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (capOut ptrOut : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_12).base + 1648#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      EncRawSegEnv curBs.length
        ((gc.2.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten).length evs →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc v capOut ptrOut
          (curBs ++ (gc.2.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten) ∗
          protoChainAt A.repAlloc gc a ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  refine sepWPpLsCl_extract_chain_mk_bounds_x (A := A.repAlloc) (gc := gc) (a := a)
    (F := vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim st s ∗
      stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by sep_ac_rfl) fun hmk_max hkeys_len => ?_
  have hzip_len : (gc.1.keys.zip gc.2.messageKeys).length = gc.2.messageKeys.length :=
    zip_length_eq_right gc.1.keys gc.2.messageKeys hkeys_len
  have hzip_map :
      (gc.1.keys.zip gc.2.messageKeys).map (fun p => lenField 4 (encMessageKey p.2)) =
      gc.2.messageKeys.map (fun mk => lenField 4 (encMessageKey mk)) :=
    zip_map_snd_eq_encChain gc.1.keys gc.2.messageKeys (fun mk => lenField 4 (encMessageKey mk)) hkeys_len
  rw [chainAt_eq_mk_cells A.repAlloc gc a]
  rcases hmks : gc.1.keys.zip gc.2.messageKeys with _ | ⟨gk, tl⟩
  · have hmks_len : gc.2.messageKeys.length = 0 := by
      rw [← hzip_len, hmks]; rfl
    have hmks_nil : gc.2.messageKeys = [] := List.eq_nil_of_length_eq_zero hmks_len
    refine step_encChain_seg4_empty_placed_x A lim H a sp0 st (s0 := s0)
      (F := vecU8At A.repAlloc v curCap curPtr curBs ∗
        ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
        ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
        vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc) gc.1.mkCap gc.1.mkPtr [] ∗
        chainMkUnusedAt A.repAlloc gc a ∗
        stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
      hpc hrun hsp htr hx20 (by simp only [List.length_nil]; sep_ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm
    refine SepWPpLsCl.congr_pre ?_
      (hnext sm curCap curPtr [] hpcm hrunm hspm htrm
        (encRawSegEnv_nil curBs.length _))
    rw [chainAt_eq_mk_cells A.repAlloc gc a, hmks, hmks_nil]
    simp only [List.length_nil, List.map_nil, List.flatten_nil, List.append_nil, M.stepEvents_nil]
    sep_ac_rfl
  · rw [hmks] at hzip_len hzip_map
    have hlen_le : (gk :: tl).length ≤ 2000 := by
      have : maxMessageKeys = 2000 := rfl
      omega
    have hlen_pos : 0 < (gk :: tl).length := by simp
    have hlen_lt : (gk :: tl).length < 2 ^ 32 := by omega
    have hlen_mk : (gk :: tl).length * 104 < 2 ^ 32 := by omega
    refine sepWPpLsCl_extract_vecBuf_mk_le_x (A := A.repAlloc) (cap := gc.1.mkCap) (ptr := gc.1.mkPtr)
      (mks := gk :: tl)
      (F := vecU8At A.repAlloc v curCap curPtr curBs ∗
        ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
        ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
        ((a + 64#64) ↦₆₄ BitVec.ofNat 64 (gk :: tl).length) ∗
        chainMkUnusedAt A.repAlloc gc a ∗
        A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
      (by sep_ac_rfl) fun hle_cap => ?_
    rw [vecBuf_mk_eq_open A.repAlloc gc.1.mkCap gc.1.mkPtr (gk :: tl) hlen_pos hle_cap]
    refine step_encChain_seg4_init_placed_x A lim H v a gc.1.mkPtr sp0 (gk :: tl).length st
      hlen_pos hlen_lt (s0 := s0)
      (F := vecU8At A.repAlloc v curCap curPtr curBs ∗
        ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
        arrayAt (messageKeyAt A.repAlloc) 104 gc.1.mkPtr (gk :: tl) ∗
        vecMkRest A.repAlloc gc.1.mkCap gc.1.mkPtr (gk :: tl) ∗
        chainMkUnusedAt A.repAlloc gc a ∗
        stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
      hpc hrun hsp htr hx19 hx20 (by sep_ac_rfl) ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hregs1
    have hbound_mks :
        curBs.length +
          (((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length < 2 ^ 32 := by
      rw [hzip_map]
      exact hbound
    have hfit_mks : FitsEnv M lim st
        (EncRawSegEnv curBs.length
          (((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length) := by
      rw [hzip_map]
      exact hfit
    refine step_encChain_mk_loop_placed_x A lim H hC hmk hEV hDR
      gk tl v gc.1.mkPtr (gc.1.mkPtr + BitVec.ofNat 64 ((gk :: tl).length * 104))
      curCap curPtr sp0 curBs st rfl hlen_mk hbound_mks hfit_mks
      (s0 := s0)
      (F := ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
        ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
        ((a + 64#64) ↦₆₄ BitVec.ofNat 64 (gk :: tl).length) ∗
        vecMkRest A.repAlloc gc.1.mkCap gc.1.mkPtr (gk :: tl) ∗
        chainMkUnusedAt A.repAlloc gc a ∗ F)
      hpc1 hrun1 hsp1 halign htr1 hregs1 (by sep_ac_rfl) ?_
    intro sm capOut ptrOut evs hpcm hrunm hspm htrm hevs
    have hevs' : EncRawSegEnv curBs.length
        ((gc.2.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten).length evs := by
      rwa [← hzip_map]
    refine SepWPpLsCl.congr_pre ?_ (hnext sm capOut ptrOut evs hpcm hrunm hspm htrm hevs')
    rw [chainAt_eq_mk_cells A.repAlloc gc a, hmks,
        vecBuf_mk_eq_open A.repAlloc gc.1.mkCap gc.1.mkPtr (gk :: tl) hlen_pos hle_cap,
        hzip_map]
    sep_ac_rfl

/-- Envelope-parameterized epilogue (`+1648 → ret`) for `encodeChainSpecWithEnvX`. -/
theorem step_encChain_epilogue_env_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (chainEnv : EncodeChainGhost → List AllocEvent → Prop)
    (H : LibsignalHooks)
    (capOut ptrOut : BitVec 64) (st0 : M.σ) (evs : List AllocEvent)
    {x : EncodeChainGhost} {R : SepProp}
    {s0 s : State} {P : SepProp} {Qp : State → SepProp → Prop}
    (hevs : chainEnv x evs)
    (hpc : s.pc = (blkPl_12).base + 1648#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (vecU8At A.repAlloc x.v capOut ptrOut (x.bs ++ lenField x.tag (encChainMem x.gc)) ∗
      protoChainAt A.repAlloc x.gc x.a ∗
      A.pool lim (M.stepEvents evs st0) s ∗ stackAt (s0.sp - 96#64) encChainSubStackX ∗
      encChainSavedRegs s0.sp s0)) :
    SepWPpLsCl lsmpl (lsProg_12 H) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (encodeChainSpecWithEnvX M A lim chainEnv).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf)
      Qp := by
  subst hP
  unfold encChainSavedRegs
  have hsp_align96 := sp_sub_96_aligned halign
  apply sepWPpLsCl_of_sepWP_vm (mid := s0.readReg64 .lr)
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm =>
        sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := M.stepEvents evs st0)
          hvm (by sep_focus) ?_⟩
    apply SepWPpLsCl.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine ⟨?_, by simp only [arm64_norm, *],
      ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, htr.2]⟩⟩
    intro hm
    dsimp only [encodeChainSpecWithEnvX]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by (try simp only [wp_norm, arm64_norm]); exact htr.1, hevs⟩, ?_⟩
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨capOut, ptrOut, ?_⟩
    rw [stackAt_encodeChainStackX_split s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 28#5), s0.readReg64 (Reg.gpr 27#5),
      s0.readReg64 (Reg.gpr 26#5), s0.readReg64 (Reg.gpr 25#5),
      s0.readReg64 (Reg.gpr 24#5), s0.readReg64 (Reg.gpr 23#5),
      s0.readReg64 (Reg.gpr 22#5), s0.readReg64 (Reg.gpr 21#5),
      s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5), ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm

theorem step_encChain_epilogue_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (capOut ptrOut : BitVec 64) (st0 : M.σ) (evs : List AllocEvent)
    {x : EncodeChainGhost} {R : SepProp}
    {s0 s : State} {P : SepProp} {Qp : State → SepProp → Prop}
    (hevs : EncodeChainEnv x evs)
    (hpc : s.pc = (blkPl_12).base + 1648#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (vecU8At A.repAlloc x.v capOut ptrOut (x.bs ++ lenField x.tag (encChainMem x.gc)) ∗
      protoChainAt A.repAlloc x.gc x.a ∗
      A.pool lim (M.stepEvents evs st0) s ∗ stackAt (s0.sp - 96#64) encChainSubStackX ∗
      encChainSavedRegs s0.sp s0)) :
    SepWPpLsCl lsmpl (lsProg_12 H) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX M A lim).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf)
      Qp := by
  rw [← encodeChainSpecWithEnvX_eq M A lim]
  exact step_encChain_epilogue_env_placed_x A lim EncodeChainEnv H capOut ptrOut st0 evs
    hevs hpc hrun hsp halign htr hP

/-! ## Top-level Block `12` (`encode::<Chain, Vec<u8>>`) contracts -/

/-- Segment-level Block `12` (`encode::<Chain, Vec<u8>>`) contract under `encodeChainSegEnv`. -/
abbrev EncodeChainSegPlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_12 H) (blkPl_12).base
    (withLsCodeLoaded lsmpl (encodeChainSpecWithEnvX M A lim encodeChainSegEnv))

/-- Block `12` (`prost::encoding::message::encode::<Chain, Vec<u8>>`) meets
    `EncodeChainSegPlacedOkX M A lim H` (`encodeChainSpecWithEnvX ... encodeChainSegEnv`). -/
theorem encodeChain_seg_placed_ok_ext [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (hC : SerContractsXPlaced M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (hchain : subroutine_ok (lsProg_88 H) (blkPl_88).base
      (withLsCodeLoaded lsmpl (chainLenSpec A.repAlloc)))
    (hmk : subroutine_ok (lsProg_118 H) (blkPl_118).base
      (withLsCodeLoaded lsmpl (msgKeyLenSpec A.repAlloc))) :
    EncodeChainSegPlacedOkX M A lim H := by
  apply subroutine_ok_withLsCodeLoaded_of_sepWPpLsCl
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre halign_bool
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using halign_bool
  refine ⟨(encodeChainSpecWithEnvX M A lim encodeChainSegEnv).pre (x, st0) s0, R, hpre, ?_⟩
  dsimp only [encodeChainSpecWithEnvX]
  refine SepWPpLsCl.pure_elim fun ⟨hx0, hx1, hx2, htag, hlen, hfit⟩ => ?_
  have hkey_len : (encodeKey x.tag .lengthDelimited).length = 1 :=
    encChain_encodeKey_len htag
  let L0 := (encodeKey x.tag .lengthDelimited ++
    encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)).length
  let L1 := (bytesField 1 x.gc.1.srk.bytes).length
  let L2 := (bytesField 2 x.gc.1.priv.bytes).length
  let L3 := (msgField 3 (x.gc.2.chainKey.map encChainKey)).length
  let L4 := ((x.gc.2.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten).length
  have hlenField_split :
      (lenField x.tag (encChainMem x.gc)).length = L0 + (L1 + (L2 + (L3 + L4))) := by
    simp only [lenField, encChainMem, L0, L1, L2, L3, L4, List.length_append]
    omega
  have hfit_all : FitsEnv M lim st0
      (EncRawSegEnv x.bs.length (L0 + (L1 + (L2 + (L3 + L4))))) := by
    change FitsEnv M lim st0 (EncRawSegEnv x.bs.length (lenField x.tag (encChainMem x.gc)).length) at hfit
    rwa [hlenField_split] at hfit
  refine step_encChain_seg0_raw_placed_x A lim H hEV hchain x st0 htag hlen
    (fitsEnv_encRawSeg_left hfit_all) (F := emp)
    hpc hrun halign hx0 hx1 hx2 (by sep_ac_rfl) ?_
  intro s1 cap1 ptr1 evs0 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hevs0
  let bs1 := x.bs ++ encodeKey x.tag .lengthDelimited ++
    encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)
  have hbs1_len : bs1.length = x.bs.length + L0 := by
    simp only [bs1, L0, List.length_append, Nat.add_assoc]
  have hfit_r0 : FitsEnv M lim (M.stepEvents evs0 st0)
      (EncRawSegEnv bs1.length (L1 + (L2 + (L3 + L4)))) := by
    rw [hbs1_len]
    exact fitsEnv_encRawSeg_right hfit_all hevs0
  refine step_encChain_seg1_placed_x A lim H hC hEV hDR
    x.v x.a cap1 ptr1 s0.sp x.gc.1.srk bs1 (M.stepEvents evs0 st0)
    (encChain_bound_seg1 x hlen)
    (fitsEnv_encRawSeg_left hfit_r0)
    (s0 := s0)
    (F := vecGhostAt A.repAlloc x.gc.1.priv (x.a + 24#64) ∗
      optChainKeyAt A.repAlloc x.gc.1.ck x.gc.2.chainKey (x.a + 72#64) ∗
      chainAtRest A.repAlloc x.gc x.a ∗ encChainSavedRegs s0.sp s0)
    hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1
    (by rw [chainAt_eq_fields]; dsimp only [bs1]; sep_ac_rfl) ?_
  intro s2 cap2 ptr2 evs1 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hevs1
  let bs2 := bs1 ++ bytesField 1 x.gc.1.srk.bytes
  have hbs2_len : bs2.length = bs1.length + L1 := by
    simp only [bs2, L1, List.length_append]
  have hfit_r1 : FitsEnv M lim (M.stepEvents evs1 (M.stepEvents evs0 st0))
      (EncRawSegEnv bs2.length (L2 + (L3 + L4))) := by
    rw [hbs2_len]
    exact fitsEnv_encRawSeg_right hfit_r0 hevs1
  refine step_encChain_seg2_placed_x A lim H hC hEV hDR
    x.v x.a cap2 ptr2 s0.sp x.gc.1.priv bs2
    (M.stepEvents evs1 (M.stepEvents evs0 st0))
    (encChain_bound_seg2 x hlen)
    (fitsEnv_encRawSeg_left hfit_r1)
    (s0 := s0)
    (F := vecGhostAt A.repAlloc x.gc.1.srk x.a ∗
      optChainKeyAt A.repAlloc x.gc.1.ck x.gc.2.chainKey (x.a + 72#64) ∗
      chainAtRest A.repAlloc x.gc x.a ∗ encChainSavedRegs s0.sp s0)
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2
    (by dsimp only [bs2]; sep_ac_rfl) ?_
  intro s3 cap3 ptr3 evs2 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hevs2
  let bs3 := bs2 ++ bytesField 2 x.gc.1.priv.bytes
  have hbs3_len : bs3.length = bs2.length + L2 := by
    simp only [bs3, L2, List.length_append]
  have hfit_r2 : FitsEnv M lim
      (M.stepEvents evs2 (M.stepEvents evs1 (M.stepEvents evs0 st0)))
      (EncRawSegEnv bs3.length (L3 + L4)) := by
    rw [hbs3_len]
    exact fitsEnv_encRawSeg_right hfit_r1 hevs2
  refine step_encChain_seg3_placed_x A lim H hC hEV hDR
    x.v x.a cap3 ptr3 s0.sp x.gc.1.ck x.gc.2.chainKey bs3
    (M.stepEvents evs2 (M.stepEvents evs1 (M.stepEvents evs0 st0)))
    (encChain_bound_seg3 x hlen)
    (fitsEnv_encRawSeg_left hfit_r2)
    (s0 := s0)
    (F := vecGhostAt A.repAlloc x.gc.1.srk x.a ∗
      vecGhostAt A.repAlloc x.gc.1.priv (x.a + 24#64) ∗
      chainAtRest A.repAlloc x.gc x.a ∗ encChainSavedRegs s0.sp s0)
    hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3
    (by dsimp only [bs3]; sep_ac_rfl) ?_
  intro s4 cap4 ptr4 evs3 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hevs3
  let bs4 := bs3 ++ msgField 3 (x.gc.2.chainKey.map encChainKey)
  have hbs4_len : bs4.length = bs3.length + L3 := by
    simp only [bs4, L3, List.length_append]
  have hfit_r3 : FitsEnv M lim
      (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 (M.stepEvents evs0 st0))))
      (EncRawSegEnv bs4.length L4) := by
    rw [hbs4_len]
    exact fitsEnv_encRawSeg_right hfit_r2 hevs3
  refine step_encChain_seg4_placed_x A lim H hC hmk hEV hDR
    x.v x.a cap4 ptr4 s0.sp x.gc bs4
    (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 (M.stepEvents evs0 st0))))
    (encChain_bound_seg4 x hlen)
    hfit_r3
    (s0 := s0)
    (F := encChainSavedRegs s0.sp s0)
    hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4
    (by rw [chainAt_eq_fields]; dsimp only [bs4]; sep_ac_rfl) ?_
  intro s5 cap5 ptr5 evs4 hpc5 hrun5 hsp5 htr5 hevs4
  let evs_tot := (((evs0 ++ evs1) ++ evs2) ++ evs3) ++ evs4
  have hevs01 : EncRawSegEnv x.bs.length (L0 + L1) (evs0 ++ evs1) :=
    encRawSegEnv_append hevs0 (hbs1_len ▸ hevs1)
  have hevs02 : EncRawSegEnv x.bs.length ((L0 + L1) + L2) ((evs0 ++ evs1) ++ evs2) :=
    encRawSegEnv_append hevs01 (by simpa only [hbs2_len, hbs1_len, Nat.add_assoc] using hevs2)
  have hevs03 : EncRawSegEnv x.bs.length (((L0 + L1) + L2) + L3) (((evs0 ++ evs1) ++ evs2) ++ evs3) :=
    encRawSegEnv_append hevs02 (by simpa only [hbs3_len, hbs2_len, hbs1_len, Nat.add_assoc] using hevs3)
  have hevs04 : EncRawSegEnv x.bs.length ((((L0 + L1) + L2) + L3) + L4) evs_tot :=
    encRawSegEnv_append hevs03 (by simpa only [hbs4_len, hbs3_len, hbs2_len, hbs1_len, Nat.add_assoc] using hevs4)
  have hlenField_eq : ((((L0 + L1) + L2) + L3) + L4) = (lenField x.tag (encChainMem x.gc)).length := by
    rw [hlenField_split]; omega
  have hevs_seg : encodeChainSegEnv x evs_tot := by
    change EncRawSegEnv x.bs.length (lenField x.tag (encChainMem x.gc)).length evs_tot
    rwa [← hlenField_eq]
  have hst_tot :
      M.stepEvents evs4
        (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 (M.stepEvents evs0 st0)))) =
      M.stepEvents evs_tot st0 := by
    simp only [evs_tot, M.stepEvents_append]
  exact step_encChain_epilogue_env_placed_x A lim encodeChainSegEnv H cap5 ptr5 st0 evs_tot
    hevs_seg hpc5 hrun5 hsp5 halign htr5
    (by
      dsimp only [bs4, bs3, bs2, bs1]
      rw [encChain_final_bytes_eq x, hst_tot]
      sep_ac_rfl)

theorem encodeChain_seg_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (hC : SerContractsXPlaced M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H) :
    EncodeChainSegPlacedOkX M A lim H :=
  encodeChain_seg_placed_ok_ext A lim H hC hEV hDR
    (chainLen_placed_ok A.repAlloc H)
    (subroutine_ok_withLsCodeLoaded_of_plain (msgKeyLen_placed_ok A.repAlloc H))

theorem encodeChainPlacedOkX_of_seg [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h : EncodeChainSegPlacedOkX M A lim H) :
    EncodeChainPlacedOkX M A lim H := by
  refine subroutine_ok_withLsCodeLoaded_map_oom' h ?_
  rintro ⟨x, st⟩ R s0 hpre
  dsimp only [encodeChainSpecX, encodeChainSpecWithEnvX] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, htag, hlen, hfit⟩, hmem⟩ := hpre
  have hfit_seg : FitsEnv M lim st (encodeChainSegEnv x) :=
    fun evs he => hfit evs (encodeChainSegEnv_sub_encodeChainEnv x he)
  refine ⟨(x, st), R, ?_, ?_, fun _ hoom => hoom⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, htag, hlen, hfit_seg⟩, hmem⟩
  · intro sf hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    obtain ⟨evs, hevs⟩ := hpost
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hevs ⊢
    exact ⟨⟨hevs.1.1, encodeChainSegEnv_sub_encodeChainEnv x hevs.1.2⟩, hevs.2⟩

/-- Top-level `EncodeChainPlacedOkX` (`encodeChainSpecX M A lim`) from `chainLen`/`msgKeyLen` contracts. -/
theorem encodeChain_placed_ok_ext [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (hC : SerContractsXPlaced M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (hchain : subroutine_ok (lsProg_88 H) (blkPl_88).base
      (withLsCodeLoaded lsmpl (chainLenSpec A.repAlloc)))
    (hmk : subroutine_ok (lsProg_118 H) (blkPl_118).base
      (withLsCodeLoaded lsmpl (msgKeyLenSpec A.repAlloc))) :
    EncodeChainPlacedOkX M A lim H :=
  encodeChainPlacedOkX_of_seg (encodeChain_seg_placed_ok_ext A lim H hC hEV hDR hchain hmk)

/-- Top-level `EncodeChainPlacedOkX` instantiating `chainLen_placed_ok` and `msgKeyLen_placed_ok`. -/
theorem encodeChain_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (hC : SerContractsXPlaced M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H) :
    EncodeChainPlacedOkX M A lim H :=
  encodeChainPlacedOkX_of_seg (encodeChain_seg_placed_ok A lim H hC hEV hDR)

theorem encodeChain_placed_ok_cl [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (hchain : subroutine_ok (lsProg_88 H) (blkPl_88).base
      (withLsCodeLoaded lsmpl (chainLenSpec A.repAlloc)))
    (hmk : subroutine_ok (lsProg_118 H) (blkPl_118).base
      (withLsCodeLoaded lsmpl (msgKeyLenSpec A.repAlloc))) :
    subroutine_ok callerProg (lsmpl.base 12)
      (withLsCl lsmpl (encodeChainSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (encodeChain_placed_ok_ext A lim H hC hEV hDR hchain hmk)

theorem encodeChain_placed_cl [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H) :
    subroutine_ok callerProg (lsmpl.base 12)
      (withLsCl lsmpl (encodeChainSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (encodeChain_placed_ok A lim H hC hEV hDR)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.MessageKeyLoopXBudget
