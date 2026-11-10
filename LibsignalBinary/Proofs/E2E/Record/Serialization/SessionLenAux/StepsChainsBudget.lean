/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.StepsChains
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.StepsFrontBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymA
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.Decode
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# `VmPreserved`-threaded chain step lemmas for `SessionStructure::encoded_len`

Relocatable `[LibsignalPlacement]` chain step lemmas for block `86` (tags 6–7: `sender_chain` and
`receiver_chains` loop against `DefsBudget.chainLenSpec`), threading `VmPreserved`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.StepsChainsBudget

open Arm64 ProofLib SepProp
open CryptoGames.Ratchet (clampScalar)
open CryptoGames.LibsignalSession (SenderChain ReceiverChain)
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (LibsignalPlacement LibsignalCodeLoaded lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc arrayAt vecBuf)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SenderChainGhost SessionGhost noneCap optSenderChainAt
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  optU32Tag_beq_one optU32Tag_bne_one zext64_optU32Tag_truncate32
  cap_add_one_beq_zero_false ult_ofNat_add_of_lt ule_ofNat_add_of_lt bv_add_ofNat_comm
)
open CryptoVerification.E2E.Record (lenField)
open CryptoVerification.E2E.Record.Placed (blkPl_86 blkPl_88 lsProg_86)
open CryptoVerification.E2E.Record.Serialization (
  chainLenStack encChainMem senderAsChain senderGhostAsChain encSenderFieldMem protoChainAt
)
open CryptoVerification.E2E.Record.Serialization.SessionLenAux (
  sessHwVarintLen_eq_encodeVarint_length sessHwVarintLen_bvShift_eq_encodeVarint_length
  sess_truncate32_zext64_lsr6
  sessHwVarintLen_w32_eq_encodeVarint_length sessHwVarintLen_w32_natShift_eq_encodeVarint_length
  sess_ule_zero_64 sess_ult_zero_64
  chainAt_srk_cap_lt chainAt_expose_cap optSenderChainAt_some_eq_sessLen
  lenField_length bv_lenField_length ule_lenField_varint_false ult_varint_lenField
  chainNoKeyLen chainsNoKeySum chainsTotalLen chainsNoKeySum_add_length
  ofNat64_beq_zero_of_lt ofNat64_bne_zero_of_lt SessLenCalleeSaved
  add_neg52_eq_sub52 add_neg80_eq_sub80
  bv_sub_one_ofNat_succ bv_add_neg1_ofNat_succ ofNat64_succ_beq_one_of_lt
)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (chainLenSpec)
open LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.StepsFrontBudget (
  sepWPp_of_sepWP_lscl_vm call_protoChainLen_placed call_chainLen_placed
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm]
  bv_sub_add_lit BitVec.toNat_zero
  sessHwVarintLen_eq_encodeVarint_length
  sessHwVarintLen_bvShift_eq_encodeVarint_length
  ofNat_countLeadingZeros_64
  ofNat_countLeadingZeros_32
  CryptoVerification.LibsignalTripleRatchet.Prost.truncate32_ofNat64
  sess_truncate32_zext64_lsr6
  sessHwVarintLen_w32_eq_encodeVarint_length
  sessHwVarintLen_w32_natShift_eq_encodeVarint_length
  noneCap_add_one_beq_zero
  noneCap_add_one_bne_zero
  optU32Tag_beq_one
  optU32Tag_bne_one
  zext64_optU32Tag_truncate32
  sess_ule_zero_64
  sess_ult_zero_64
attribute [local simp, local arm64_norm] add_neg52_eq_sub52 add_neg80_eq_sub80

private theorem sepWPp_of_sepWP_vm {prog : Program} {mid ret : BitVec 64}
    {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s Pre
      (fun sm Pm => VmPreserved s sm ∧ (VmPreserved s sm → SepWPp prog ret sm Pm Q Qp))) :
    SepWPp prog ret s Pre Q Qp :=
  SepWPp.of_sepWP (mid := mid) (SepWP.mono h (fun _ _ _ _ ⟨hvm, hk⟩ => hk hvm))

theorem step_sessLen_sender_pre_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (ss : BitVec 64) (g : SenderChainGhost) (sc : SenderChain)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_86).base + 272#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hP : P = protoChainAt A (senderGhostAsChain g, senderAsChain sc) (ss + 144#64) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = (blkPl_88).base →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = ss + 144#64 →
      sm.readReg64 .lr = (blkPl_86).base + 292#64 →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      SessLenCalleeSaved s sm →
      SepWPp (lsProg_86 H) ret sm P Q Qp) :
    SepWPp (lsProg_86 H) ret s P Q Qp := by
  intro R hm hL
  have hm_cap : s.mem ⊨ protoChainAt A (senderGhostAsChain g, senderAsChain sc) (ss + 144#64) ∗ (F ∗ R) := by
    rw [← sepConj_assoc, ← hP]; exact hm
  have hcap_lt : (senderGhostAsChain g).srk.cap.toNat < 2 ^ 63 := chainAt_srk_cap_lt hm_cap
  have hcap_beq : (g.srk.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hcap_lt
  clear hm_cap
  revert R hm hL
  change SepWPp (lsProg_86 H) ret s P Q Qp
  subst hP
  have hexp := chainAt_expose_cap A (senderGhostAsChain g, senderAsChain sc) (ss + 144#64)
  conv at hexp => rhs; dsimp only [senderGhostAsChain]
  rw [hexp]
  apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_88).base)
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp_all; rfl) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], fun hvm hclm => ?_⟩
    rw [← hexp]
    exact hnext _ hvm hclm (by simp_all; rfl) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_sender_post_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (ss : BitVec 64) (gc : ChainGhost × ReceiverChain) (s1_5 : Nat)
    (hfit_sum : s1_5 + (lenField 6 (encChainMem gc)).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_86).base + 292#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 (encChainMem gc).length)
    (hx19 : s.readReg64 .x19 = ss)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 s1_5)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = (blkPl_86).base + 352#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x21 = BitVec.ofNat 64 (s1_5 + (lenField 6 (encChainMem gc)).length) →
      SessLenCalleeSaved s sm →
      SepWPp (lsProg_86 H) ret sm P Q Qp) :
    SepWPp (lsProg_86 H) ret s P Q Qp := by
  have hfit_v : (encChainMem gc).length +
      (encodeVarint (BitVec.ofNat 64 (encChainMem gc).length)).length + 1 < 2 ^ 64 := by
    have := lenField_length (t := 6) (encChainMem gc) rfl; omega
  have henc := bv_lenField_length (t := 6) (bs := encChainMem gc) rfl
  have hls := ule_lenField_varint_false hfit_v
  have hult := ult_varint_lenField hfit_v
  rw [show (encChainMem gc).length +
      (encodeVarint (BitVec.ofNat 64 (encChainMem gc).length)).length + 1 =
      (lenField 6 (encChainMem gc)).length by
    rw [lenField_length (t := 6) (encChainMem gc) rfl]; omega] at hls hult
  have hcc := ule_ofNat_add_of_lt hfit_sum
  have hcc_ult := ult_ofNat_add_of_lt hfit_sum
  have hadd := bv_add_ofNat_comm s1_5 (lenField 6 (encChainMem gc)).length
  apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_86).base + bv% (352))
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], fun hvm hclm => ?_⟩
    exact hnext _ hvm hclm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_f5_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hchain : subroutine_ok (lsProg_86 H) (blkPl_88).base
      (withLsCodeLoaded lsmpl (chainLenSpec A)))
    (ss : BitVec 64) (G : SessionGhost) (m : Session (List (BitVec 8))) (s1_5 : Nat)
    (hfit_sender : (encSenderFieldMem G.sender m.state.senderChain).length < 2 ^ 32)
    (hfit_sum : s1_5 + (encSenderFieldMem G.sender m.state.senderChain).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_86).base + 272#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = ss)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 s1_5)
    (hP : P = (optSenderChainAt A (ss + 144#64) G.sender m.state.senderChain ∗
      stackAt s.sp chainLenStack) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = (blkPl_86).base + 352#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x21 = BitVec.ofNat 64
        (s1_5 + (encSenderFieldMem G.sender m.state.senderChain).length) →
      SessLenCalleeSaved s sm →
      SepWPp (lsProg_86 H) ret sm P Q Qp) :
    SepWPp (lsProg_86 H) ret s P Q Qp := by
  cases hgs : G.sender with
  | none =>
    cases hsc : m.state.senderChain with
    | none =>
      have hP0 : P = (((ss + 144#64) ↦₆₄ noneCap ∗ memRegion (ss + 144#64 + 8#64) 96) ∗
          stackAt s.sp chainLenStack) ∗ F := by
        rw [hP, hgs, hsc]; rfl
      rw [hP0]
      apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_86).base + bv% (352))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], fun hvm hclm => ?_⟩
        rw [← hP0]
        exact hnext _ hvm hclm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
          (by simp_all) (by simp_all [encSenderFieldMem]) (by simp_all [SessLenCalleeSaved])
    | some sc =>
      intro R hm _
      rw [hP, hgs, hsc] at hm
      dsimp only [optSenderChainAt] at hm
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
      exact hm.1.elim
  | some g =>
    cases hsc : m.state.senderChain with
    | none =>
      intro R hm _
      rw [hP, hgs, hsc] at hm
      dsimp only [optSenderChainAt] at hm
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
      exact hm.1.elim
    | some sc =>
      have hopt_eq := optSenderChainAt_some_eq_sessLen A (ss + 144#64) g sc
      have hP' : P = protoChainAt A (senderGhostAsChain g, senderAsChain sc) (ss + 144#64) ∗
          (⌜g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
            clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
            g.srk.bytes.length = 33⌝ ∗
           stackAt s.sp chainLenStack ∗ F) := by
        rw [hP, hgs, hsc, hopt_eq]; sep_ac_rfl
      simp only [hgs, hsc, encSenderFieldMem] at hfit_sender hfit_sum
      have hfit_chain : (encChainMem (senderGhostAsChain g, senderAsChain sc)).length < 2 ^ 32 := by
        have hle : (encChainMem (senderGhostAsChain g, senderAsChain sc)).length ≤
            (lenField 6 (encChainMem (senderGhostAsChain g, senderAsChain sc))).length := by
          rw [lenField_length (encChainMem (senderGhostAsChain g, senderAsChain sc)) rfl]; omega
        omega
      refine step_sessLen_sender_pre_placed A H ss g sc hcl hpc hrun hx19 hP' ?_
      intro s1 hvm1 hcl1 hpc1 hrun1 hsp1 htr1 hx0_1 hlr1 hx19_1 hx20_1 hcs1
      have hsp1_align : s1.spAligned = true := by
        simpa only [State.spAligned, hsp1] using hsp
      have hP1 : P = (protoChainAt A (senderGhostAsChain g, senderAsChain sc) (ss + 144#64) ∗
          stackAt s1.sp chainLenStack) ∗
          (⌜g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
            clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
            g.srk.bytes.length = 33⌝ ∗ F) := by
        rw [hsp1, hP']; sep_ac_rfl
      refine call_protoChainLen_placed A H hchain (ss + 144#64)
        ((blkPl_86).base + 292#64)
        (senderGhostAsChain g, senderAsChain sc)
        hcl1 hpc1 hrun1 hsp1_align hlr1 hx0_1 hfit_chain hP1 ?_
      intro s2 hvm2 hcl2 hpc2 hrun2 hsp2 htr2 hx0_2 hcs2
      refine step_sessLen_sender_post_placed H ss
        (senderGhostAsChain g, senderAsChain sc) s1_5
        hfit_sum hcl2 hpc2 hrun2 hx0_2 (by reg_chain) (by reg_chain) ?_
      intro s3 hvm3 hcl3 hpc3 hrun3 hsp3 htr3 hx19_3 hx21_3 hcs3
      refine hnext s3 (hvm1.trans (hvm2.trans hvm3)) hcl3 hpc3 hrun3
        (by reg_chain) (by reg_chain) hx19_3 ?_ (by reg_chain)
      simpa only [hgs, hsc, encSenderFieldMem] using hx21_3

theorem step_sessLen_loop_pre_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (ptr : BitVec 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_86).base + 372#64)
    (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = ptr)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = (blkPl_88).base →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = ptr →
      sm.readReg64 .lr = (blkPl_86).base + 380#64 →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = ptr →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x24 = s.readReg64 .x24 →
      SessLenCalleeSaved s sm →
      SepWPp (lsProg_86 H) ret sm P Q Qp) :
    SepWPp (lsProg_86 H) ret s P Q Qp := by
  apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_88).base)
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp_all; rfl) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], fun hvm hclm => ?_⟩
    exact hnext _ hvm hclm (by simp_all; rfl) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_loop_post_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (ptr : BitVec 64) (gc : ChainGhost × ReceiverChain) (acc n_rem : Nat)
    (hfit_acc : acc + chainNoKeyLen gc < 2 ^ 64)
    (hn_rem : n_rem + 1 < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_86).base + 380#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 (encChainMem gc).length)
    (hx20 : s.readReg64 .x20 = ptr)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 acc)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (n_rem + 1))
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = (if n_rem = 0 then
        (blkPl_86).base + 428#64
      else
        (blkPl_86).base + 372#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = ptr + 104#64 →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = BitVec.ofNat 64 (acc + chainNoKeyLen gc) →
      sm.readReg64 .x24 = BitVec.ofNat 64 n_rem →
      SessLenCalleeSaved s sm →
      SepWPp (lsProg_86 H) ret sm P Q Qp) :
    SepWPp (lsProg_86 H) ret s P Q Qp := by
  have hfit_c : (encChainMem gc).length +
      (encodeVarint (BitVec.ofNat 64 (encChainMem gc).length)).length < 2 ^ 64 := by
    have : chainNoKeyLen gc = (encChainMem gc).length +
        (encodeVarint (BitVec.ofNat 64 (encChainMem gc).length)).length := rfl
    omega
  have hadd_c : BitVec.ofNat 64 (encChainMem gc).length +
      BitVec.ofNat 64 (encodeVarint (BitVec.ofNat 64 (encChainMem gc).length)).length =
      BitVec.ofNat 64 (chainNoKeyLen gc) := by
    rw [← BitVec.ofNat_add]; rfl
  have hcc_c : BitVec.ult (BitVec.ofNat 64 (chainNoKeyLen gc))
      (BitVec.ofNat 64 (encChainMem gc).length) = false := by
    have h := ult_ofNat_add_of_lt (a := (encodeVarint (BitVec.ofNat 64 (encChainMem gc).length)).length)
      (b := (encChainMem gc).length) (by omega)
    rwa [Nat.add_comm] at h
  have hadd_acc := bv_add_ofNat_comm acc (chainNoKeyLen gc)
  have hcc_acc := ult_ofNat_add_of_lt hfit_acc
  have hsub1 := bv_sub_one_ofNat_succ n_rem
  have hadd_neg1 := bv_add_neg1_ofNat_succ n_rem
  have hrem_beq1 := ofNat64_succ_beq_one_of_lt hn_rem
  have hrem_beq := ofNat64_beq_zero_of_lt (n := n_rem) (by omega)
  have hrem_bne := ofNat64_bne_zero_of_lt (n := n_rem) (by omega)
  cases n_rem with
  | zero =>
    apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_86).base + bv% (428))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], fun hvm hclm => ?_⟩
      exact hnext _ hvm hclm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all [SessLenCalleeSaved])
  | succ m =>
    apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_86).base + bv% (372))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], fun hvm hclm => ?_⟩
      exact hnext _ hvm hclm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_chains_loop_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hchain : subroutine_ok (lsProg_86 H) (blkPl_88).base
      (withLsCodeLoaded lsmpl (chainLenSpec A)))
    : ∀ (rest : List (ChainGhost × ReceiverChain)) (gc : ChainGhost × ReceiverChain)
        (ptr : BitVec 64) (acc : Nat)
        {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop},
      LibsignalCodeLoaded lsmpl s.mem →
      acc + chainsNoKeySum (gc :: rest) < 2 ^ 32 →
      rest.length + 1 < 2 ^ 64 →
      s.pc = (blkPl_86).base + 372#64 →
      s.status = .Running →
      s.spAligned = true →
      s.readReg64 .x20 = ptr →
      s.readReg64 .x23 = BitVec.ofNat 64 acc →
      s.readReg64 .x24 = BitVec.ofNat 64 (rest.length + 1) →
      P = (arrayAt (chainAt A) 104 ptr (gc :: rest) ∗ stackAt s.sp chainLenStack) ∗ F →
      (∀ sm : State,
        VmPreserved s sm →
        LibsignalCodeLoaded lsmpl sm.mem →
        sm.pc = (blkPl_86).base + 428#64 →
        sm.status = .Running →
        sm.sp = s.sp →
        sm.trace = s.trace →
        sm.readReg64 .x19 = s.readReg64 .x19 →
        sm.readReg64 .x21 = s.readReg64 .x21 →
        sm.readReg64 .x22 = s.readReg64 .x22 →
        sm.readReg64 .x23 = BitVec.ofNat 64 (acc + chainsNoKeySum (gc :: rest)) →
        SessLenCalleeSaved s sm →
        SepWPp (lsProg_86 H) ret sm P Q Qp) →
      SepWPp (lsProg_86 H) ret s P Q Qp
  | [], gc, ptr, acc, ret, s, P, F, Q, Qp,
      hcl, hfit, hlen, hpc, hrun, hsp, hx20, hx23, hx24, hP, hnext => by
    simp only [chainsNoKeySum, Nat.add_zero] at hfit
    have hfit_c : (encChainMem gc).length < 2 ^ 32 := by
      have : (encChainMem gc).length ≤ chainNoKeyLen gc := by unfold chainNoKeyLen; omega
      omega
    refine step_sessLen_loop_pre_placed H ptr hcl hpc hrun hx20 ?_
    intro s1 hvm1 hcl1 hpc1 hrun1 hsp1 htr1 hx0_1 hlr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hcs1
    have hsp1_align : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp
    have hP1 : P = (chainAt A gc ptr ∗ stackAt s1.sp chainLenStack) ∗
        (arrayAt (chainAt A) 104 (ptr + 104#64) [] ∗ F) := by
      rw [hsp1, hP]; dsimp only [arrayAt]; sep_ac_rfl
    refine call_chainLen_placed A H hchain ptr
      ((blkPl_86).base + 380#64) gc
      hcl1 hpc1 hrun1 hsp1_align hlr1 hx0_1 hfit_c hP1 ?_
    intro s2 hvm2 hcl2 hpc2 hrun2 hsp2 htr2 hx0_2 hcs2
    refine step_sessLen_loop_post_placed H ptr gc acc 0 (by omega) hlen
      hcl2 hpc2 hrun2 hx0_2 (by reg_chain) (by reg_chain) ((hcs2.2.2.2.2.2.1.trans hx24_1).trans hx24) ?_
    intro s3 hvm3 hcl3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hcs3
    simp only [↓reduceIte] at hpc3
    refine hnext s3 (hvm1.trans (hvm2.trans hvm3)) hcl3 hpc3 hrun3 (by reg_chain) (by reg_chain)
      (by reg_chain) (by reg_chain) (by reg_chain) ?_ (by reg_chain)
    simpa only [chainsNoKeySum, Nat.add_zero] using hx23_3
  | gc' :: rest', gc, ptr, acc, ret, s, P, F, Q, Qp,
      hcl, hfit, hlen, hpc, hrun, hsp, hx20, hx23, hx24, hP, hnext => by
    simp only [chainsNoKeySum] at hfit
    have hfit_c : (encChainMem gc).length < 2 ^ 32 := by
      have : (encChainMem gc).length ≤ chainNoKeyLen gc := by unfold chainNoKeyLen; omega
      omega
    refine step_sessLen_loop_pre_placed H ptr hcl hpc hrun hx20 ?_
    intro s1 hvm1 hcl1 hpc1 hrun1 hsp1 htr1 hx0_1 hlr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hcs1
    have hsp1_align : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp
    have hP1 : P = (chainAt A gc ptr ∗ stackAt s1.sp chainLenStack) ∗
        (arrayAt (chainAt A) 104 (ptr + 104#64) (gc' :: rest') ∗ F) := by
      rw [hsp1, hP]; dsimp only [arrayAt]; sep_ac_rfl
    refine call_chainLen_placed A H hchain ptr
      ((blkPl_86).base + 380#64) gc
      hcl1 hpc1 hrun1 hsp1_align hlr1 hx0_1 hfit_c hP1 ?_
    intro s2 hvm2 hcl2 hpc2 hrun2 hsp2 htr2 hx0_2 hcs2
    refine step_sessLen_loop_post_placed H ptr gc acc (gc' :: rest').length (by omega) hlen
      hcl2 hpc2 hrun2 hx0_2 (by reg_chain) (by reg_chain) (by reg_chain) ?_
    intro s3 hvm3 hcl3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hcs3
    simp only [List.length_cons, Nat.succ_ne_zero, ↓reduceIte] at hpc3 hx24_3
    have hsp3_eq : s3.sp = s.sp := by reg_chain
    have hsp3_align : s3.spAligned = true := by simpa only [State.spAligned, hsp3_eq] using hsp
    have hP3 : P = (arrayAt (chainAt A) 104 (ptr + 104#64) (gc' :: rest') ∗ stackAt s3.sp chainLenStack) ∗
        (chainAt A gc ptr ∗ F) := by
      rw [hsp3_eq, hP]; dsimp only [arrayAt]; sep_ac_rfl
    have hfit' : (acc + chainNoKeyLen gc) + chainsNoKeySum (gc' :: rest') < 2 ^ 32 := by
      simp only [chainsNoKeySum]; omega
    refine step_sessLen_chains_loop_placed A H hchain rest' gc' (ptr + 104#64)
      (acc + chainNoKeyLen gc) hcl3 hfit' (by simp only [List.length_cons] at hlen; omega)
      hpc3 hrun3 hsp3_align hx20_3 hx23_3 hx24_3 hP3 ?_
    intro s4 hvm4 hcl4 hpc4 hrun4 hsp4 htr4 hx19_4 hx21_4 hx22_4 hx23_4 hcs4
    refine hnext s4 ((hvm1.trans hvm2).trans (hvm3.trans hvm4)) hcl4 hpc4 hrun4
      (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) ?_ (by reg_chain)
    simpa only [chainsNoKeySum, Nat.add_assoc] using hx23_4

theorem step_sessLen_chains_enter_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (ss ptr : BitVec 64) (n : Nat)
    (hn_pos : n ≠ 0) (hn_lt : n < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_86).base + 352#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hP : P = (((ss + 80#64) ↦₆₄ ptr) ∗ ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 n)) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = (blkPl_86).base + 372#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x20 = ptr →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = BitVec.ofNat 64 n →
      sm.readReg64 .x23 = 0#64 →
      sm.readReg64 .x24 = BitVec.ofNat 64 n →
      SessLenCalleeSaved s sm →
      SepWPp (lsProg_86 H) ret sm P Q Qp) :
    SepWPp (lsProg_86 H) ret s P Q Qp := by
  have hn_beq : (BitVec.ofNat 64 n == 0#64) = false := by
    rw [ofNat64_beq_zero_of_lt hn_lt]
    exact beq_eq_false_iff_ne.mpr hn_pos
  subst hP
  apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_86).base + bv% (372))
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], fun hvm hclm => ?_⟩
    exact hnext _ hvm hclm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_chains_exit_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (cs : List (ChainGhost × ReceiverChain)) (s1_6 : Nat)
    (hfit : s1_6 + chainsTotalLen cs < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_86).base + 428#64)
    (hrun : s.status = .Running)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 s1_6)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 cs.length)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (chainsNoKeySum cs))
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_86).base + 444#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1_6 + chainsTotalLen cs) →
      SessLenCalleeSaved s sm →
      SepWPp (lsProg_86 H) ret sm P Q Qp) :
    SepWPp (lsProg_86 H) ret s P Q Qp := by
  have hsum_eq := chainsNoKeySum_add_length cs
  have hfit1 : chainsNoKeySum cs + cs.length < 2 ^ 64 := by omega
  have hadd1 : BitVec.ofNat 64 (chainsNoKeySum cs) + BitVec.ofNat 64 cs.length =
      BitVec.ofNat 64 (chainsTotalLen cs) := by
    rw [← BitVec.ofNat_add, hsum_eq]
  have hcc1 : BitVec.ult (BitVec.ofNat 64 (chainsTotalLen cs))
      (BitVec.ofNat 64 (chainsNoKeySum cs)) = false := by
    have h := ult_ofNat_add_of_lt (a := cs.length) (b := chainsNoKeySum cs) (by omega)
    rwa [Nat.add_comm, hsum_eq] at h
  have hadd2 := bv_add_ofNat_comm s1_6 (chainsTotalLen cs)
  have hcc2 : BitVec.ult (BitVec.ofNat 64 (s1_6 + chainsTotalLen cs))
      (BitVec.ofNat 64 (chainsTotalLen cs)) = false :=
    ult_ofNat_add_of_lt hfit
  apply sepWPp_of_sepWP_vm (mid := (blkPl_86).base + bv% (444))
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    exact hnext _ hvm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_f6_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hchain : subroutine_ok (lsProg_86 H) (blkPl_88).base
      (withLsCodeLoaded lsmpl (chainLenSpec A)))
    (ss : BitVec 64) (G : SessionGhost) (m : Session (List (BitVec 8))) (s1_6 : Nat)
    (hfit : s1_6 + chainsTotalLen (G.chains.zip m.state.receiverChains) < 2 ^ 32)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_86).base + 352#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = ss)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 s1_6)
    (hP : P = (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
      ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip m.state.receiverChains).length) ∗
      vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip m.state.receiverChains) ∗
      stackAt s.sp chainLenStack) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_86).base + 444#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64
        (s1_6 + chainsTotalLen (G.chains.zip m.state.receiverChains)) →
      SessLenCalleeSaved s sm →
      SepWPp (lsProg_86 H) ret sm P Q Qp) :
    SepWPp (lsProg_86 H) ret s P Q Qp := by
  intro R hm hL
  have hm_pure : s.mem ⊨
      ⌜(G.chains.zip m.state.receiverChains).length ≤ G.chainsCap.toNat ∧
        G.chainsCap.toNat * 104 < 2 ^ 63 ∧ G.chainsPtr ≠ 0⌝ ∗
      ((if G.chainsCap = 0 then emp
        else A.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
          arrayAt (chainAt A) 104 G.chainsPtr (G.chains.zip m.state.receiverChains) ∗
          memRegion (G.chainsPtr + BitVec.ofNat 64 ((G.chains.zip m.state.receiverChains).length * 104))
            ((G.chainsCap.toNat - (G.chains.zip m.state.receiverChains).length) * 104)) ∗
       ((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
       ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip m.state.receiverChains).length) ∗
       stackAt s.sp chainLenStack ∗ F ∗ R) := by
    rw [hP] at hm
    dsimp only [vecBuf] at hm
    convert hm using 1; sep_ac_rfl
  rw [satisfies_pure_sepConj] at hm_pure
  rcases hm_pure.1 with ⟨hlen_le, hcap_lt, _⟩
  clear hm_pure
  revert R hm hL
  change SepWPp (lsProg_86 H) ret s P Q Qp
  cases hcs : G.chains.zip m.state.receiverChains with
  | nil =>
    subst hP
    have hlen0 : (G.chains.zip m.state.receiverChains).length = 0 := by rw [hcs]; rfl
    have htot0 : chainsTotalLen (G.chains.zip m.state.receiverChains) = 0 := by rw [hcs]; rfl
    have hP0 : (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
        ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip m.state.receiverChains).length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip m.state.receiverChains) ∗
        stackAt s.sp chainLenStack) ∗ F =
        ((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
        ((ss + 88#64) ↦₆₄ 0#64) ∗
        (vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip m.state.receiverChains) ∗
         stackAt s.sp chainLenStack ∗ F) := by
      simp only [hlen0, sepConj_assoc]
    rw [hP0]
    apply sepWPp_of_sepWP_vm (mid := (blkPl_86).base + bv% (444))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
      rw [← hP0]
      exact hnext _ hvm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])
  | cons gc rest =>
    rw [hcs] at hlen_le
    have hcap_ne : G.chainsCap ≠ 0 := by
      intro h0
      have hcap0 : G.chainsCap.toNat = 0 := by simp [h0]
      simp only [List.length_cons, hcap0] at hlen_le
      omega
    have hV : P = (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
        ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (gc :: rest).length)) ∗
        ((⌜(gc :: rest).length ≤ G.chainsCap.toNat ∧
            G.chainsCap.toNat * 104 < 2 ^ 63 ∧ G.chainsPtr ≠ 0⌝ ∗
          A.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
          arrayAt (chainAt A) 104 G.chainsPtr (gc :: rest) ∗
          memRegion (G.chainsPtr + BitVec.ofNat 64 ((gc :: rest).length * 104))
            ((G.chainsCap.toNat - (gc :: rest).length) * 104)) ∗
          stackAt s.sp chainLenStack ∗ F) := by
      rw [hP, hcs]
      dsimp only [vecBuf]
      simp only [hcap_ne, ↓reduceIte]
      sep_ac_rfl
    refine step_sessLen_chains_enter_placed H ss G.chainsPtr
      (gc :: rest).length (by simp) (by omega) hcl hpc hrun hx19 hV ?_
    intro s1 hvm1 hcl1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hcs1
    have hsp1_align : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp
    have hP1 : P = (arrayAt (chainAt A) 104 G.chainsPtr (gc :: rest) ∗ stackAt s1.sp chainLenStack) ∗
        (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
         ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (gc :: rest).length) ∗
         ⌜(gc :: rest).length ≤ G.chainsCap.toNat ∧
           G.chainsCap.toNat * 104 < 2 ^ 63 ∧ G.chainsPtr ≠ 0⌝ ∗
         A.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
         memRegion (G.chainsPtr + BitVec.ofNat 64 ((gc :: rest).length * 104))
           ((G.chainsCap.toNat - (gc :: rest).length) * 104) ∗ F) := by
      rw [hsp1, hV]; sep_ac_rfl
    have hfit_loop : 0 + chainsNoKeySum (gc :: rest) < 2 ^ 32 := by
      rw [hcs] at hfit
      have := chainsNoKeySum_add_length (gc :: rest)
      omega
    refine step_sessLen_chains_loop_placed A H hchain rest gc G.chainsPtr 0
      hcl1 hfit_loop (by simp only [List.length_cons] at hlen_le; omega)
      hpc1 hrun1 hsp1_align hx20_1 hx23_1 hx24_1 hP1 ?_
    intro s2 hvm2 _hcl2 hpc2 hrun2 hsp2 htr2 hx19_2 hx21_2 hx22_2 hx23_2 hcs2
    simp only [Nat.zero_add] at hx23_2
    have hfit_exit : s1_6 + chainsTotalLen (gc :: rest) < 2 ^ 64 := by
      rw [hcs] at hfit; omega
    refine step_sessLen_chains_exit_placed H (gc :: rest) s1_6 hfit_exit
      hpc2 hrun2 (by reg_chain) (by reg_chain) hx23_2 ?_
    intro s3 hvm3 hpc3 hrun3 hsp3 htr3 hx19_3 hx8_3 hcs3
    refine hnext s3 (hvm1.trans (hvm2.trans hvm3)) hpc3 hrun3
      (by reg_chain) (by reg_chain) (by reg_chain) ?_ (by reg_chain)
    simpa only [hcs] using hx8_3

end LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.StepsChainsBudget
