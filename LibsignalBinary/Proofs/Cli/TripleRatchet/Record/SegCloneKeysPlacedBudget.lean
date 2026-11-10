/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneBasePlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneKeysPlacedBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneKeysPlaced
public meta import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneKeys -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import ProofLib.RegChain
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable CLI `SegClone` Entry and Sub-Segments 1–4

Re-exports entry and fields 1–3 from `SegCloneKeysPlacedBudgetAux`, proves `sender_chain` cloning
(`+0x290 → +0x544 / +0x300`), and assembles combined entry and fields 1–4 cloning on CLI Block `463`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneKeysPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (keyToBytes32)
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (allocHookStack vecU8At vecU8Buf)
open CryptoVerification.LibsignalSessionRepr (VecGhost vecGhostAt)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SenderChainGhost noneCap protocolAddressAt signalMessageAt optSenderChainAt
)
open CryptoVerification.LibsignalTripleRatchet (RecordDecryptGhost rootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (chainCloneStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (
  OptSenderChainInline bytes104OfW6Q chunks96_6QAt memRegion_96_eq_exists_chunks96_6QAt
  optSenderChainHeap optSenderChainAt_entails_chunks104W6Q
)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps (
  SpillVals DstVals dstSlotsAt spillSlotsAt
  cap_add_one_ne_zero cap_add_one_beq_zero_eq_false
  ofNat_ne_zero_of_pos beq_ofNat_zero_eq_false eq_nil_or_length_pos entails_pure_2nd
  vecU8Buf_pure_extract optSenderChainAt_some_eq_cap optSenderChainSomeRest
  chunks96_6QAt_sp_0xb40 chunks104W6QAt_sp_0x5f0 chunks104W6QAt_entails_memRegion
  pointsTo128_eq_pointsTo64 cat128_extractLsb
  segClone_memRegion_0xa0_eq segClone_memRegion_0x4b0_0x950_eq memRegion_0x5f0_0x6b0_eq
  signalMessageAt_eq_ver signalMessageRestAt stackAt_root_eq_chainClone stackAt_chainClone_eq_alloc
  segClone_vecGhostAt_0x138_eq segClone_vecGhostAt_0x150_eq segClone_vecU8At_0x168_root_eq
  memRegion_0x80_entails_spillSlotsAt memRegion_0x80_0x20_entails
  memRegion_0x5b0_0x40_entails memRegion_344_entails_dstSlotsAt
)
open CryptoVerification.CliRatchet.DecPlaced (blkPC_463 blkPl_463)
open CryptoVerification.Cli.CoinsTape (cliTapeAt)
open CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps (SepWPpCl sepWPpCl_pure_2nd)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
  FitsEvents FitsEnv fitsEvents_append rustAllocEvents
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (
  SenderChainCloneEnv senderChainCloneEvents senderChainCloneSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (vecCloneEvents)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneBasePlacedBudget (
  SegCloneHooks SepWPpCl_of_sepWP_vm segClone_fixedRestPlaced
)

export LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneKeysPlacedBudgetAux (
  senderChainOptCloneEvents fields1To4Events seg_entry_to_0x1fc_placed
)
export LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneKeysPlacedBudgetAux (
  seg_localIk_placed seg_remoteIk_placed seg_rootKey_placed
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Clone `sender_chain` (`+0x290 → +0x544 / +0x300`), threading `A.pool` across
    `senderChainOptCloneEvents x.G.sender x.st.senderChain`. -/
theorem seg_senderChain_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : String → Option (State → State)}
    (hsenderClone : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468)
      (withLsCodeLoaded lsmpl (senderChainCloneSpec M A lim)))
    {x : RecordDecryptGhost} {s0 s : State} {ret : BitVec 64}
    {Q Qp : State → SepProp → Prop}
    (hQp_false : ∀ sf P_p, sf.status = .Panicked → Qp sf ((⌜False⌝ : SepProp) ∗ P_p))
    {localIk' remoteIk' : VecGhost}
    {v40 v58 v60 v68 v70 v78 : BitVec 64} {v54 : BitVec 32}
    {bq0 bq1 bq2 bq3 bq4 bq5 : BitVec 128} {F : SepProp}
    (hfits : FitsEvents M lim st (senderChainOptCloneEvents x.G.sender x.st.senderChain))
    (hpc : s.pc = (blkPl_463).base + 0x290#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = localIk'.cap) (hx21 : s.readReg64 .x21 = localIk'.ptr)
    (hx22 : s.readReg64 .x22 = remoteIk'.cap) (hx26 : s.readReg64 .x26 = remoteIk'.ptr)
    (hx23 : s.readReg64 .x23 = s.sp + 0x5f0#64)
    (hx28 : s.readReg64 .x28 = 32#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrc_lt : x.st.receiverChains.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (sender' : Option SenderChainGhost) (scCap' : BitVec 64)
      (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128),
      s1.pc = (if x.st.receiverChains = []
        then (blkPl_463).base + 0x544#64
        else (blkPl_463).base + 0x300#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x23 = s.sp + 0x5f0#64 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = BitVec.ofNat 64 x.st.receiverChains.length →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      OptSenderChainInline sender' x.st.senderChain (bytes104OfW6Q scCap' sq0 sq1 sq2 sq3 sq4 sq5) →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (A.pool lim (M.stepEvents (senderChainOptCloneEvents x.G.sender x.st.senderChain) st) s1 ∗
          optSenderChainAt A.repAlloc (s.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
          optSenderChainHeap A.repAlloc sender' x.st.senderChain ∗
          chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          memRegion (s.sp + 0x5f0#64) 104 ∗
          ((s.sp + 0x40#64) ↦₆₄ scCap') ∗
          ((s.sp + 0x54#64) ↦₃₂ x.st.previousCounter) ∗
          ((s.sp + 0x58#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0x60#64) ↦₆₄ remoteIk'.ptr) ∗
          ((s.sp + 0x68#64) ↦₆₄ remoteIk'.cap) ∗
          ((s.sp + 0x70#64) ↦₆₄ localIk'.ptr) ∗
          ((s.sp + 0x78#64) ↦₆₄ localIk'.cap) ∗
          ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
          ((s.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
          stackAt s.sp chainCloneStack ∗ F)
        Q Qp) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (A.pool lim st s ∗
        optSenderChainAt A.repAlloc (s.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
        chunks96_6QAt (s.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
        memRegion (s.sp + 0x5f0#64) 104 ∗
        ((s.sp + 0x40#64) ↦₆₄ v40) ∗
        ((s.sp + 0x54#64) ↦₃₂ v54) ∗
        ((s.sp + 0x58#64) ↦₆₄ v58) ∗
        ((s.sp + 0x60#64) ↦₆₄ v60) ∗
        ((s.sp + 0x68#64) ↦₆₄ v68) ∗
        ((s.sp + 0x70#64) ↦₆₄ v70) ∗
        ((s.sp + 0x78#64) ↦₆₄ v78) ∗
        ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
        ((s.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
        stackAt s.sp chainCloneStack ∗ F)
      Q Qp := by
  have hcall := hsenderClone
  cases hscG : x.G.sender with
  | none =>
    cases hscM : x.st.senderChain with
    | none =>
      dsimp only [optSenderChainAt]
      have hnone_cmn : noneCap + 1#64 = 0#64 := by decide
      clear hcall
      have hpc_rc :
          (if ¬(BitVec.ofNat 64 x.st.receiverChains.length == 0#64) = true then (blkPl_463).base + bv% (768) else (blkPl_463).base + bv% (1348)) =
          (if x.st.receiverChains = [] then (blkPl_463).base + bv% (1348) else (blkPl_463).base + bv% (768)) := by
        rcases eq_nil_or_length_pos x.st.receiverChains with hrc | hrc
        · simp [hrc]
        · have hne : x.st.receiverChains ≠ [] := List.ne_nil_of_length_pos hrc
          have hbeq : (BitVec.ofNat 64 x.st.receiverChains.length == 0#64) = false :=
            beq_ofNat_zero_eq_false hrc (by omega)
          simp [hne, hbeq]
      apply SepWPpCl_of_sepWP_vm
        (mid := if x.st.receiverChains = [] then (blkPl_463).base + bv% (1348) else (blkPl_463).base + bv% (768))
      by_vm_steps
        wp_steps
        refine SepWP.done (by segCloneKeys_close) hrun
          ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
        let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm
        have hpool := A.pool_transport lim st s s_end hvm
        have hinl : OptSenderChainInline none x.st.senderChain
            (bytes104OfW6Q noneCap bq0 bq1 bq2 bq3 bq4 bq5) := by
          rw [hscM]
          exact OptSenderChainInline.none_of_chunks96 bq0 bq1 bq2 bq3 bq4 bq5
        refine SepWPpCl.weaken_pre ?_
          (hnext s_end none noneCap bq0 bq1 bq2 bq3 bq4 bq5
            (by dsimp only [s_end]; segCloneKeys_close) hrun rfl hsp hx23 rfl rfl rfl rfl htr hinl)
        rw [hscG, hscM]
        dsimp only [senderChainOptCloneEvents, AllocCostModel.stepEvents, List.foldl,
          optSenderChainAt, optSenderChainHeap]
        rw [hpool]
        simp only [emp_sepConj, sepConj_emp, hx20, hx21, hx22, hx26, hx28]
        exact Entails.of_eq (by sep_ac_rfl)
    | some sc =>
      dsimp only [optSenderChainAt]
      exact sepWPpCl_pure_2nd fun h => False.elim h
  | some sg =>
    cases hscM : x.st.senderChain with
    | none =>
      dsimp only [optSenderChainAt]
      exact sepWPpCl_pure_2nd fun h => False.elim h
    | some sc =>
      have hfit_sc : FitsEvents M lim st (senderChainCloneEvents sg sc) := by
        simpa [senderChainOptCloneEvents, hscG, hscM] using hfits
      have hfit_env : FitsEnv M lim st (SenderChainCloneEnv sg sc) :=
        fun _ he => he ▸ hfit_sc
      rw [optSenderChainAt_some_eq_cap A.repAlloc (s.sp + 0x1c8#64) sg sc]
      simp only [sepConj_assoc]
      refine sepWPpCl_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
      have hcap_ne : sg.srk.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcap_beq : (sg.srk.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      apply SepWPpCl_of_sepWP_vm (mid := lsmpl.base 468)
      by_vm_steps
        wp_steps
        refine SepWP.done rfl hrun
          ⟨by simp only [wp_norm, arm64_norm], fun hvm_call => ?_⟩
        let s_call := (fun {a b : State} (_ : VmPreserved a b) => b) hvm_call
        have hpool_call := A.pool_transport lim st s s_call hvm_call
        have h_sp_call : s_call.sp = s.sp := rfl
        have h1c8 : s.sp + 160#64 + 296#64 = s.sp + 0x1c8#64 := by bv_arith
        refine SepWPpCl.weaken_pre
          (P' := (memRegion (s.sp + 0x5f0#64) 104 ∗
              optSenderChainAt A.repAlloc (s.sp + 0x1c8#64) (some sg) (some sc) ∗
              A.pool lim st s_call ∗ stackAt s_call.sp chainCloneStack) ∗
            (chunks96_6QAt (s.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
              ((s.sp + 0x40#64) ↦₆₄ v40) ∗
              ((s.sp + 0x54#64) ↦₃₂ x.st.previousCounter) ∗
              ((s.sp + 0x58#64) ↦₆₄ v58) ∗
              ((s.sp + 0x60#64) ↦₆₄ remoteIk'.ptr) ∗
              ((s.sp + 0x68#64) ↦₆₄ remoteIk'.cap) ∗
              ((s.sp + 0x70#64) ↦₆₄ v70) ∗
              ((s.sp + 0x78#64) ↦₆₄ v78) ∗
              ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
              ((s.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗ F))
          ?_ ?_
        · rw [hpool_call, h_sp_call,
              optSenderChainAt_some_eq_cap A.repAlloc (s.sp + 0x1c8#64) sg sc]
          simp only [sepConj_assoc]
          rw [show (memRegion (s.sp + 0x5f0#64) 104 ∗
              ⌜sg.srk.bytes.length ≤ sg.srk.cap.toNat ∧ sg.srk.cap.toNat < 2 ^ 63 ∧ sg.srk.ptr ≠ 0⌝ ∗
              ((s.sp + 0x1c8#64) ↦₆₄ sg.srk.cap) ∗
              optSenderChainSomeRest A.repAlloc (s.sp + 0x1c8#64) sg sc ∗
              A.pool lim st s ∗ stackAt s.sp chainCloneStack ∗
              chunks96_6QAt (s.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
              ((s.sp + 0x40#64) ↦₆₄ v40) ∗
              ((s.sp + 0x54#64) ↦₃₂ x.st.previousCounter) ∗
              ((s.sp + 0x58#64) ↦₆₄ v58) ∗
              ((s.sp + 0x60#64) ↦₆₄ remoteIk'.ptr) ∗
              ((s.sp + 0x68#64) ↦₆₄ remoteIk'.cap) ∗
              ((s.sp + 0x70#64) ↦₆₄ v70) ∗
              ((s.sp + 0x78#64) ↦₆₄ v78) ∗
              ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
              ((s.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗ F) =
            (A.pool lim st s ∗
              ⌜sg.srk.bytes.length ≤ sg.srk.cap.toNat ∧ sg.srk.cap.toNat < 2 ^ 63 ∧ sg.srk.ptr ≠ 0⌝ ∗
              ((s.sp + 0x1c8#64) ↦₆₄ sg.srk.cap) ∗
              optSenderChainSomeRest A.repAlloc (s.sp + 0x1c8#64) sg sc ∗
              chunks96_6QAt (s.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
              memRegion (s.sp + 0x5f0#64) 104 ∗
              ((s.sp + 0x40#64) ↦₆₄ v40) ∗
              ((s.sp + 0x54#64) ↦₃₂ x.st.previousCounter) ∗
              ((s.sp + 0x58#64) ↦₆₄ v58) ∗
              ((s.sp + 0x60#64) ↦₆₄ remoteIk'.ptr) ∗
              ((s.sp + 0x68#64) ↦₆₄ remoteIk'.cap) ∗
              ((s.sp + 0x70#64) ↦₆₄ v70) ∗
              ((s.sp + 0x78#64) ↦₆₄ v78) ∗
              ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
              ((s.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
              stackAt s.sp chainCloneStack ∗ F) by sep_ac_rfl]
          exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by sep_ac_rfl)
        · refine SepWPpCl.call_frame_cl
            (x := (⟨s.sp + 0x5f0#64, s.sp + 0x1c8#64, sg, sc⟩, st))
            hcall rfl hrun hsp
            (ret_pc := (blkPl_463).base + bv% (696)) rfl
            rfl ⟨by segCloneKeys_close, by segCloneKeys_close, hfit_env⟩ rfl
            (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
            (fun sf hp => hQp_false sf _ hp)
            fun sf hpcf hrunf hspf hcsm => ?_
          clear hcall
          obtain ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29⟩ := hcsm
          dsimp only [senderChainCloneSpec]
          simp only [sepConj_assoc, sepExists_sepConj_left]
          refine SepWPpCl.exists_elim fun evs_sc => ?_
          refine SepWPpCl.pure_elim fun ⟨htr_sf, hevs_sc⟩ => ?_
          dsimp only [SenderChainCloneEnv] at hevs_sc
          subst hevs_sc
          refine SepWPpCl.exists_elim fun g' => ?_
          refine SepWPpCl.pure_elim fun ⟨hsrk', hpriv'⟩ => ?_
          rw [h_sp_call] at hspf ⊢
          have hsf_sp : sf.sp = s.sp := hspf
          have hsf23 : sf.readReg64 (Reg.gpr 23#5) = sf.sp + 0x5f0#64 := by
            rw [hcs23, hsf_sp]; exact hx23
          have hsf20 : sf.readReg64 (Reg.gpr 20#5) = localIk'.cap := hcs20.trans hx20
          have hsf21 : sf.readReg64 (Reg.gpr 21#5) = localIk'.ptr := hcs21.trans hx21
          have hsf28 : sf.readReg64 (Reg.gpr 28#5) = 32#64 := hcs28.trans hx28
          have hsf24 : sf.readReg64 (Reg.gpr 24#5) = s.readReg64 .x24 := hcs24
          have hsf25 : sf.readReg64 (Reg.gpr 25#5) = s.readReg64 .x25 := hcs25
          have hsf29 : sf.readReg64 Reg.fp = s.readReg64 .x29 := hcs29.1
          have hsf_tr : sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 :=
            ⟨htr_sf.trans htr.1, hcs29.2.trans htr.2⟩
          have hsf_spA : sf.spAligned = true := by
            unfold State.spAligned at hsp ⊢; rw [hsf_sp]; exact hsp
          clear hspf hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29 htr_sf
          refine SepWPpCl.weaken_pre
            (sepConj_mono_left (optSenderChainAt_entails_chunks104W6Q A.repAlloc (s.sp + 0x5f0#64) (some g') (some sc))) ?_
          simp only [sepExists_sepConj_left]
          refine SepWPpCl.exists_elim fun scCap' =>
            SepWPpCl.exists_elim fun sq0 => SepWPpCl.exists_elim fun sq1 =>
            SepWPpCl.exists_elim fun sq2 => SepWPpCl.exists_elim fun sq3 =>
            SepWPpCl.exists_elim fun sq4 => SepWPpCl.exists_elim fun sq5 => ?_
          simp only [sepConj_assoc]
          refine SepWPpCl.pure_elim fun hsc_inl => ?_
          have hinl : OptSenderChainInline (some g') x.st.senderChain
              (bytes104OfW6Q scCap' sq0 sq1 sq2 sq3 sq4 sq5) := by
            rw [hscM]; exact hsc_inl
          rw [chunks104W6QAt_sp_0x5f0 s.sp scCap' sq0 sq1 sq2 sq3 sq4 sq5,
              chunks96_6QAt_sp_0xb40 s.sp bq0 bq1 bq2 bq3 bq4 bq5]
          simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
          have hpc_rc :
              (if (BitVec.ofNat 64 x.st.receiverChains.length == 0#64) = true then (blkPl_463).base + bv% (1348) else (blkPl_463).base + bv% (768)) =
              (if x.st.receiverChains = [] then (blkPl_463).base + bv% (1348) else (blkPl_463).base + bv% (768)) := by
            rcases eq_nil_or_length_pos x.st.receiverChains with hrc | hrc
            · simp [hrc]
            · have hne : x.st.receiverChains ≠ [] := List.ne_nil_of_length_pos hrc
              have hne0 : BitVec.ofNat 64 x.st.receiverChains.length ≠ 0#64 :=
                ofNat_ne_zero_of_pos hrc (by omega)
              have hbeq : (BitVec.ofNat 64 x.st.receiverChains.length == 0#64) = false :=
                beq_false_of_ne hne0
              simp [hne, hbeq]
          apply SepWPpCl_of_sepWP_vm
            (mid := if x.st.receiverChains = [] then (blkPl_463).base + bv% (1348) else (blkPl_463).base + bv% (768))
          by_vm_steps
            wp_steps
            refine SepWP.done (by segCloneKeys_close) hrunf
              ⟨by simp only [wp_norm, arm64_norm], fun hvm_post => ?_⟩
            let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm_post
            have hpool_post := A.pool_transport lim
              (M.stepEvents (senderChainCloneEvents sg sc) st) sf s_end hvm_post
            refine SepWPpCl.weaken_pre ?_
              (hnext s_end (some g') scCap' sq0 sq1 sq2 sq3 sq4 sq5
                (by dsimp only [s_end]; segCloneKeys_close) hrunf hsf_sp hsf_spA
                (by dsimp only [s_end]; segCloneKeys_close)
                hsf24 hsf25 rfl hsf29 hsf_tr hinl)
            simp only [hscG, hscM, senderChainOptCloneEvents, hpool_post,
                hsf23, hsf_sp, hsf20, hsf21, hsf28,
                ← chunks96_6QAt_sp_0xb40 s.sp sq0 sq1 sq2 sq3 sq4 sq5,
                pointsTo128_eq_pointsTo64, cat128_extractLsb, BitVec.add_assoc, BitVec.reduceAdd]
            have h104 : ∀ R_tail : SepProp,
                ((s.sp + 0x5f0#64) ↦₆₄ scCap') ∗
                  ((s.sp + 1528#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp + 1536#64) ↦₆₄ sq0.extractLsb' 64 64) ∗
                  ((s.sp + 1544#64) ↦₆₄ sq1.extractLsb' 0 64) ∗ ((s.sp + 1552#64) ↦₆₄ sq1.extractLsb' 64 64) ∗
                  ((s.sp + 1560#64) ↦₆₄ sq2.extractLsb' 0 64) ∗ ((s.sp + 1568#64) ↦₆₄ sq2.extractLsb' 64 64) ∗
                  ((s.sp + 1576#64) ↦₆₄ sq3.extractLsb' 0 64) ∗ ((s.sp + 1584#64) ↦₆₄ sq3.extractLsb' 64 64) ∗
                  ((s.sp + 1592#64) ↦₆₄ sq4.extractLsb' 0 64) ∗ ((s.sp + 1600#64) ↦₆₄ sq4.extractLsb' 64 64) ∗
                  ((s.sp + 1608#64) ↦₆₄ sq5.extractLsb' 0 64) ∗ ((s.sp + 1616#64) ↦₆₄ sq5.extractLsb' 64 64) ∗
                  R_tail ⊢
                memRegion (s.sp + 0x5f0#64) 104 ∗ R_tail := by
              intro R_tail
              have h104_eq := congrArg (· ∗ R_tail) (chunks104W6QAt_sp_0x5f0 s.sp scCap' sq0 sq1 sq2 sq3 sq4 sq5)
              simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h104_eq
              rw [← h104_eq]
              exact sepConj_mono_left (chunks104W6QAt_entails_memRegion _ _ _ _ _ _ _ _)
            refine Entails.trans (h104 _) ?_
            exact Entails.of_eq (by
              simp only [chunks96_6QAt_sp_0xb40, pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd]
              sep_ac_rfl)

/-- Combined entry frame initialization (`+0x1a8 → +0x1fc`), threading `VmPreserved s s1` and
    polymorphic in `{Q Qp}`. -/
theorem segClone_entry_combined_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {ctl : BitVec 64}
    {H : String → Option (State → State)}
    {x : RecordDecryptGhost} {s0 s : State}
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop} {F : SepProp}
    (hpc : s.pc = (blkPl_463).base + 0x1a8#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (h19 : s.readReg64 .x19 = x.remA) (h27 : s.readReg64 .x27 = x.sret)
    (h23 : s.readReg64 .x23 = s.sp + 0x5f0#64) (h24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (sv : SpillVals) (dv : DstVals)
      (bq0 bq1 bq2 bq3 bq4 bq5 : BitVec 128),
      VmPreserved s s1 →
      s1.pc = (blkPl_463).base + 0x1fc#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x23 = s.sp + 0x5f0#64 → s1.readReg64 .x24 = s.sp + 0xca0#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (vecGhostAt A.repAlloc x.G.localIk (s.sp + 0x138#64) ∗
          dstSlotsAt s.sp dv ∗
          spillSlotsAt s.sp sv.v00 sv.v08 sv.v14 sv.v18 sv.v24 sv.v28 sv.v2c
            sv.v30 sv.v3c sv.v40 sv.v48 sv.v54 sv.v58 sv.v60 sv.v68 sv.v70 sv.v78 ∗
          chunks96_6QAt (s.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
          memRegion (s.sp + 0x5f0#64) 104 ∗
          ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
          memRegion (s.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗
          stackAt s.sp allocHookStack ∗
          segClone_fixedRestPlaced A ctl x s.sp ∗ F)
        Q Qp) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (memRegion s.sp 0xa0 ∗
        ((s.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s.sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((s.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
        vecGhostAt A.repAlloc x.G.localIk (s.sp + 0x138#64) ∗
        memRegion (s.sp + 0x4b0#64) 0x950 ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
        signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
        cliTapeAt ctl x.cur x.rest ∗ lsLogOff ∗ stackAt s.sp rootStack ∗ F)
      Q Qp := by
  rw [segClone_memRegion_0xa0_eq s.sp, segClone_memRegion_0x4b0_0x950_eq s.sp,
      memRegion_0x5f0_0x6b0_eq s.sp, signalMessageAt_eq_ver A.repAlloc x.msgG x.msgA x.msg,
      stackAt_root_eq_chainClone s.sp, stackAt_chainClone_eq_alloc s.sp,
      segClone_vecGhostAt_0x138_eq A.repAlloc x.G.localIk s.sp,
      vecU8Buf_pure_extract A.repAlloc x.G.localIk.cap x.G.localIk.ptr x.G.localIk.bytes]
  simp only [sepConj_assoc]
  refine SepWPpCl.weaken_pre
    (sepConj_mono (memRegion_0x80_entails_spillSlotsAt s.sp)
      (sepConj_mono_left (memRegion_0x80_0x20_entails s.sp))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPpCl.exists_elim fun v80 => SepWPpCl.exists_elim fun v88 =>
    SepWPpCl.exists_elim fun v90 => SepWPpCl.exists_elim fun v9c =>
    SepWPpCl.exists_elim fun sv => ?_
  refine SepWPpCl.weaken_pre
    (P' := ⌜x.G.localIk.bytes.length ≤ x.G.localIk.cap.toNat ∧
              x.G.localIk.cap.toNat < 2 ^ 63 ∧ x.G.localIk.ptr ≠ 0⌝ ∗
            memRegion (s.sp + 0x5b0#64) 0x40 ∗
            memRegion (s.sp + 0xca0#64) 344 ∗
            memRegion (s.sp + 0xb40#64) 96 ∗
            (((s.sp + 0x80#64) ↦₆₄ v80) ∗ ((s.sp + 0x88#64) ↦₆₄ v88) ∗
              ((s.sp + 0x90#64) ↦₆₄ v90) ∗ ((s.sp + 0x9c#64) ↦₃₂ v9c) ∗
              ((s.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s.sp + 0xf0#64) ↦₆₄ x.locA) ∗
              ((s.sp + 0x138#64) ↦₆₄ x.G.localIk.cap) ∗
              ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗
              ((s.sp + 0x140#64) ↦₆₄ x.G.localIk.ptr) ∗
              ((s.sp + 0x148#64) ↦₆₄ BitVec.ofNat 64 x.G.localIk.bytes.length) ∗
              vecU8Buf A.repAlloc x.G.localIk.cap x.G.localIk.ptr x.G.localIk.bytes ∗
              spillSlotsAt s.sp sv.v00 sv.v08 sv.v14 sv.v18 sv.v24 sv.v28 sv.v2c
                sv.v30 sv.v3c sv.v40 sv.v48 sv.v54 sv.v58 sv.v60 sv.v68 sv.v70 sv.v78 ∗
              memRegion (s.sp + 0x5f0#64) 104 ∗
              memRegion (s.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗
              stackAt s.sp allocHookStack ∗
              memRegion (s.sp + 0x98#64) 4 ∗
              ((s.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
              memRegion (s.sp + 0x4b0#64) 48 ∗ memRegion (s.sp + 0x4e0#64) 0xd0 ∗
              memRegion (s.sp + 0x658#64) 0x4e8 ∗ memRegion (s.sp + 0xba0#64) 0x100 ∗
              memRegion (s.sp + 0xdf8#64) 8 ∗
              protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
              signalMessageRestAt A.repAlloc x.msgG x.msgA x.msg ∗
              cliTapeAt ctl x.cur x.rest ∗ lsLogOff ∗
              memRegion (s.sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack) ∗ F))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWPpCl.pure_elim fun ⟨_, hcap_lt, _⟩ => ?_
  refine SepWPpCl.weaken_pre
    (sepConj_mono (memRegion_0x5b0_0x40_entails s.sp)
      (sepConj_mono (memRegion_344_entails_dstSlotsAt s.sp)
        (sepConj_mono_left (Entails.of_eq (memRegion_96_eq_exists_chunks96_6QAt (s.sp + 0xb40#64)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPpCl.exists_elim fun bq0 => SepWPpCl.exists_elim fun bq1 =>
    SepWPpCl.exists_elim fun bq2 => SepWPpCl.exists_elim fun bq3 =>
    SepWPpCl.exists_elim fun bq4 => SepWPpCl.exists_elim fun bq5 =>
    SepWPpCl.exists_elim fun dv =>
    SepWPpCl.exists_elim fun v5b0 => SepWPpCl.exists_elim fun v5bc =>
    SepWPpCl.exists_elim fun v5c0 => SepWPpCl.exists_elim fun v5c8 =>
    SepWPpCl.exists_elim fun v5d0 => SepWPpCl.exists_elim fun v5d8 =>
    SepWPpCl.exists_elim fun v5e0 => SepWPpCl.exists_elim fun v5e8 => ?_
  refine SepWPpCl.weaken_pre
    (P' := ((s.sp + 0x80#64) ↦₆₄ v80) ∗ ((s.sp + 0x88#64) ↦₆₄ v88) ∗
            ((s.sp + 0x90#64) ↦₆₄ v90) ∗ ((s.sp + 0x9c#64) ↦₃₂ v9c) ∗
            ((s.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s.sp + 0xf0#64) ↦₆₄ x.locA) ∗
            ((s.sp + 0x138#64) ↦₆₄ x.G.localIk.cap) ∗
            ((s.sp + 0x5b0#64) ↦₆₄ v5b0) ∗ ((s.sp + 0x5bc#64) ↦₈ v5bc) ∗
            ((s.sp + 0x5c0#64) ↦₆₄ v5c0) ∗ ((s.sp + 0x5c8#64) ↦₆₄ v5c8) ∗
            ((s.sp + 0x5d0#64) ↦₆₄ v5d0) ∗ ((s.sp + 0x5d8#64) ↦₆₄ v5d8) ∗
            ((s.sp + 0x5e0#64) ↦₆₄ v5e0) ∗ ((s.sp + 0x5e8#64) ↦₆₄ v5e8) ∗
            ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗
            (((s.sp + 0x140#64) ↦₆₄ x.G.localIk.ptr) ∗
              ((s.sp + 0x148#64) ↦₆₄ BitVec.ofNat 64 x.G.localIk.bytes.length) ∗
              vecU8Buf A.repAlloc x.G.localIk.cap x.G.localIk.ptr x.G.localIk.bytes ∗
              dstSlotsAt s.sp dv ∗
              spillSlotsAt s.sp sv.v00 sv.v08 sv.v14 sv.v18 sv.v24 sv.v28 sv.v2c
                sv.v30 sv.v3c sv.v40 sv.v48 sv.v54 sv.v58 sv.v60 sv.v68 sv.v70 sv.v78 ∗
              chunks96_6QAt (s.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
              memRegion (s.sp + 0x5f0#64) 104 ∗
              memRegion (s.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗
              stackAt s.sp allocHookStack ∗
              memRegion (s.sp + 0x98#64) 4 ∗
              ((s.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
              memRegion (s.sp + 0x4b0#64) 48 ∗ memRegion (s.sp + 0x4e0#64) 0xd0 ∗
              memRegion (s.sp + 0x5b8#64) 4 ∗ memRegion (s.sp + 0x5bd#64) 3 ∗
              memRegion (s.sp + 0x658#64) 0x4e8 ∗ memRegion (s.sp + 0xba0#64) 0x100 ∗
              memRegion (s.sp + 0xdf8#64) 8 ∗
              protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
              signalMessageRestAt A.repAlloc x.msgG x.msgA x.msg ∗
              cliTapeAt ctl x.cur x.rest ∗ lsLogOff ∗
              memRegion (s.sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack) ∗ F))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine seg_entry_to_0x1fc_placed (A := A) hpc hrun hsp h19 h27 h23 h24 htr hcap_lt
    fun s1 hvm1 hpc1 hrun1 hsp1 hspA1 hx23_1 hx24_1 hx29_1 htr1 => ?_
  refine SepWPpCl.weaken_pre ?_
    (hnext s1 sv dv bq0 bq1 bq2 bq3 bq4 bq5 hvm1 hpc1 hrun1 hsp1 hspA1 hx23_1 hx24_1 hx29_1 htr1)
  unfold segClone_fixedRestPlaced
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_fixedRestPlaced
  rw [segClone_vecGhostAt_0x138_eq A.repAlloc x.G.localIk s.sp,
      signalMessageAt_eq_ver A.repAlloc x.msgG x.msgA x.msg]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Clone fields 1–4 (`+0x1fc → +0x544 / +0x300`), threading `A.pool` across
    `fields1To4Events x.G x.st`. -/
theorem segClone_fields_1_to_4_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : String → Option (State → State)} (hA : SegCloneHooks A lim H)
    (hsenderClone : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468)
      (withLsCodeLoaded lsmpl (senderChainCloneSpec M A lim)))
    {x : RecordDecryptGhost} {s0 s : State}
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    (hQp_false : ∀ sf P_p, sf.status = .Panicked → Qp sf ((⌜False⌝ : SepProp) ∗ P_p))
    {bq0 bq1 bq2 bq3 bq4 bq5 : BitVec 128}
    {v40 v48 v58 v60 v68 v70 v78 : BitVec 64} {v54 : BitVec 32} {F : SepProp}
    (hfits : FitsEvents M lim st (fields1To4Events x.G x.st))
    (hpc : s.pc = (blkPl_463).base + 0x1fc#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx23 : s.readReg64 .x23 = s.sp + 0x5f0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrc_lt : x.st.receiverChains.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
      (sender' : Option SenderChainGhost) (scCap' : BitVec 64)
      (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128),
      s1.pc = (if x.st.receiverChains = []
        then (blkPl_463).base + 0x544#64
        else (blkPl_463).base + 0x300#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x23 = s.sp + 0x5f0#64 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = x.st.sessionVersion.setWidth 64 →
      s1.readReg64 .x26 = BitVec.ofNat 64 x.st.receiverChains.length →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      localIk'.bytes = x.G.localIk.bytes →
      localIk'.cap = BitVec.ofNat 64 x.G.localIk.bytes.length →
      remoteIk'.bytes = x.G.remoteIk.bytes →
      remoteIk'.cap = BitVec.ofNat 64 x.G.remoteIk.bytes.length →
      OptSenderChainInline sender' x.st.senderChain
        (bytes104OfW6Q scCap' sq0 sq1 sq2 sq3 sq4 sq5) →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (A.pool lim (M.stepEvents (fields1To4Events x.G x.st) st) s1 ∗
          vecGhostAt A.repAlloc x.G.localIk (s.sp + 0x138#64) ∗
          vecGhostAt A.repAlloc x.G.remoteIk (s.sp + 0x150#64) ∗
          vecU8At A.repAlloc (s.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
          optSenderChainAt A.repAlloc (s.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
          vecU8Buf A.repAlloc localIk'.cap localIk'.ptr localIk'.bytes ∗
          vecU8Buf A.repAlloc remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
          vecU8Buf A.repAlloc 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗
          optSenderChainHeap A.repAlloc sender' x.st.senderChain ∗
          chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          memRegion (s.sp + 0x5f0#64) 104 ∗
          ((s.sp + 0x40#64) ↦₆₄ scCap') ∗
          ((s.sp + 0x48#64) ↦₆₄ rootPtr') ∗
          ((s.sp + 0x54#64) ↦₃₂ x.st.previousCounter) ∗
          ((s.sp + 0x58#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0x60#64) ↦₆₄ remoteIk'.ptr) ∗
          ((s.sp + 0x68#64) ↦₆₄ remoteIk'.cap) ∗
          ((s.sp + 0x70#64) ↦₆₄ localIk'.ptr) ∗
          ((s.sp + 0x78#64) ↦₆₄ localIk'.cap) ∗
          ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
          ((s.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
          ((s.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
          stackAt s.sp chainCloneStack ∗ F)
        Q Qp) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (A.pool lim st s ∗
        vecGhostAt A.repAlloc x.G.localIk (s.sp + 0x138#64) ∗
        vecGhostAt A.repAlloc x.G.remoteIk (s.sp + 0x150#64) ∗
        vecU8At A.repAlloc (s.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        optSenderChainAt A.repAlloc (s.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
        chunks96_6QAt (s.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
        memRegion (s.sp + 0x5f0#64) 104 ∗
        ((s.sp + 0x40#64) ↦₆₄ v40) ∗
        ((s.sp + 0x48#64) ↦₆₄ v48) ∗
        ((s.sp + 0x54#64) ↦₃₂ v54) ∗
        ((s.sp + 0x58#64) ↦₆₄ v58) ∗
        ((s.sp + 0x60#64) ↦₆₄ v60) ∗
        ((s.sp + 0x68#64) ↦₆₄ v68) ∗
        ((s.sp + 0x70#64) ↦₆₄ v70) ∗
        ((s.sp + 0x78#64) ↦₆₄ v78) ∗
        ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
        ((s.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
        ((s.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
        stackAt s.sp chainCloneStack ∗ F)
      Q Qp := by
  have hfits' : FitsEvents M lim st
      (vecCloneEvents x.G.localIk ++
        (vecCloneEvents x.G.remoteIk ++
          (rustAllocEvents 32 1 ++ senderChainOptCloneEvents x.G.sender x.st.senderChain))) := by
    simpa [fields1To4Events, List.append_assoc] using hfits
  obtain ⟨hfit1, hfit234⟩ := (fitsEvents_append M lim _ _ st).mp hfits'
  obtain ⟨hfit2, hfit34⟩ := (fitsEvents_append M lim _ _ _).mp hfit234
  obtain ⟨hfit3, hfit4⟩ := (fitsEvents_append M lim _ _ _).mp hfit34
  let st1 := M.stepEvents (vecCloneEvents x.G.localIk) st
  let st2 := M.stepEvents (vecCloneEvents x.G.remoteIk) st1
  let st3 := M.stepEvents (rustAllocEvents 32 1) st2
  rw [segClone_vecGhostAt_0x150_eq A.repAlloc x.G.remoteIk s.sp,
      vecU8Buf_pure_extract A.repAlloc x.G.remoteIk.cap x.G.remoteIk.ptr x.G.remoteIk.bytes,
      segClone_vecU8At_0x168_root_eq A.repAlloc s.sp x.G.root.cap x.G.root.ptr x.st.rootKey,
      stackAt_chainClone_eq_alloc s.sp]
  refine SepWPpCl.weaken_pre
    (P' := ⌜x.G.remoteIk.bytes.length ≤ x.G.remoteIk.cap.toNat ∧
              x.G.remoteIk.cap.toNat < 2 ^ 63 ∧ x.G.remoteIk.ptr ≠ 0⌝ ∗
            A.pool lim st s ∗ vecGhostAt A.repAlloc x.G.localIk (s.sp + 0x138#64) ∗
            ((s.sp + 0x160#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
            ((s.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
            stackAt s.sp allocHookStack ∗
            (((s.sp + 0x150#64) ↦₆₄ x.G.remoteIk.cap) ∗
              ((s.sp + 0x158#64) ↦₆₄ x.G.remoteIk.ptr) ∗
              vecU8Buf A.repAlloc x.G.remoteIk.cap x.G.remoteIk.ptr x.G.remoteIk.bytes ∗
              ((s.sp + 0x168#64) ↦₆₄ x.G.root.cap) ∗
              ((s.sp + 0x170#64) ↦₆₄ x.G.root.ptr) ∗
              ((s.sp + 0x178#64) ↦₆₄ 32#64) ∗
              vecU8Buf A.repAlloc x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
              optSenderChainAt A.repAlloc (s.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
              chunks96_6QAt (s.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
              memRegion (s.sp + 0x5f0#64) 104 ∗
              ((s.sp + 0x40#64) ↦₆₄ v40) ∗ ((s.sp + 0x48#64) ↦₆₄ v48) ∗
              ((s.sp + 0x54#64) ↦₃₂ v54) ∗ ((s.sp + 0x58#64) ↦₆₄ v58) ∗
              ((s.sp + 0x60#64) ↦₆₄ v60) ∗ ((s.sp + 0x68#64) ↦₆₄ v68) ∗
              ((s.sp + 0x70#64) ↦₆₄ v70) ∗ ((s.sp + 0x78#64) ↦₆₄ v78) ∗
              ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
              ((s.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
              memRegion (s.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWPpCl.pure_elim fun ⟨hlen_rem, hcap_rem, _⟩ => ?_
  have hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63 := by omega
  refine seg_localIk_placed hA hfit1 hpc hrun hsp htr hrem_lt
    fun s1 localIk' hpc1 hrun1 hsp1 hspA1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 htr1 hloc_b hloc_c => ?_
  rw [← hsp1]
  refine SepWPpCl.weaken_pre
    (P' := A.pool lim st1 s1 ∗ vecGhostAt A.repAlloc x.G.remoteIk (s1.sp + 0x150#64) ∗
            ((s1.sp + 0x178#64) ↦₆₄ 32#64) ∗
            stackAt s1.sp allocHookStack ∗
            (vecGhostAt A.repAlloc x.G.localIk (s1.sp + 0x138#64) ∗
              vecU8Buf A.repAlloc localIk'.cap localIk'.ptr localIk'.bytes ∗
              ((s1.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
              ((s1.sp + 0x168#64) ↦₆₄ x.G.root.cap) ∗
              ((s1.sp + 0x170#64) ↦₆₄ x.G.root.ptr) ∗
              vecU8Buf A.repAlloc x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
              optSenderChainAt A.repAlloc (s1.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
              chunks96_6QAt (s1.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
              memRegion (s1.sp + 0x5f0#64) 104 ∗
              ((s1.sp + 0x40#64) ↦₆₄ v40) ∗ ((s1.sp + 0x48#64) ↦₆₄ v48) ∗
              ((s1.sp + 0x54#64) ↦₃₂ v54) ∗ ((s1.sp + 0x58#64) ↦₆₄ v58) ∗
              ((s1.sp + 0x60#64) ↦₆₄ v60) ∗ ((s1.sp + 0x68#64) ↦₆₄ v68) ∗
              ((s1.sp + 0x70#64) ↦₆₄ v70) ∗ ((s1.sp + 0x78#64) ↦₆₄ v78) ∗
              ((s1.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
              ((s1.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
              memRegion (s1.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (by rw [segClone_vecGhostAt_0x150_eq A.repAlloc x.G.remoteIk s1.sp]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine seg_remoteIk_placed hA hfit2 hpc1 hrun1 hspA1 hx22_1 htr1
    fun s2 remoteIk' hpc2 hrun2 hsp2 hspA2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx28_2 hx29_2 htr2 hrem_b hrem_c => ?_
  rw [← hsp2]
  refine SepWPpCl.weaken_pre
    (P' := A.pool lim st2 s2 ∗
            vecU8At A.repAlloc (s2.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
            ((s2.sp + 0x48#64) ↦₆₄ v48) ∗
            stackAt s2.sp allocHookStack ∗
            (vecGhostAt A.repAlloc x.G.localIk (s2.sp + 0x138#64) ∗
              vecGhostAt A.repAlloc x.G.remoteIk (s2.sp + 0x150#64) ∗
              vecU8Buf A.repAlloc localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A.repAlloc remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              optSenderChainAt A.repAlloc (s2.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
              chunks96_6QAt (s2.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
              memRegion (s2.sp + 0x5f0#64) 104 ∗
              ((s2.sp + 0x40#64) ↦₆₄ v40) ∗ ((s2.sp + 0x54#64) ↦₃₂ v54) ∗
              ((s2.sp + 0x58#64) ↦₆₄ v58) ∗ ((s2.sp + 0x60#64) ↦₆₄ v60) ∗
              ((s2.sp + 0x68#64) ↦₆₄ v68) ∗ ((s2.sp + 0x70#64) ↦₆₄ v70) ∗
              ((s2.sp + 0x78#64) ↦₆₄ v78) ∗
              ((s2.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
              ((s2.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
              ((s2.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
              memRegion (s2.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (by rw [segClone_vecU8At_0x168_root_eq A.repAlloc s2.sp x.G.root.cap x.G.root.ptr x.st.rootKey]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine seg_rootKey_placed hA hfit3 hpc2 hrun2 hspA2 hx28_2 htr2
    fun s3 rootPtr' hpc3 hrun3 hsp3 hspA3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx28_3 hx29_3 htr3 => ?_
  rw [← hsp3]
  refine SepWPpCl.weaken_pre
    (P' := A.pool lim st3 s3 ∗
            optSenderChainAt A.repAlloc (s3.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
            chunks96_6QAt (s3.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
            memRegion (s3.sp + 0x5f0#64) 104 ∗
            ((s3.sp + 0x40#64) ↦₆₄ v40) ∗ ((s3.sp + 0x54#64) ↦₃₂ v54) ∗
            ((s3.sp + 0x58#64) ↦₆₄ v58) ∗ ((s3.sp + 0x60#64) ↦₆₄ v60) ∗
            ((s3.sp + 0x68#64) ↦₆₄ v68) ∗ ((s3.sp + 0x70#64) ↦₆₄ v70) ∗
            ((s3.sp + 0x78#64) ↦₆₄ v78) ∗
            ((s3.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
            ((s3.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
            stackAt s3.sp chainCloneStack ∗
            (vecGhostAt A.repAlloc x.G.localIk (s3.sp + 0x138#64) ∗
              vecGhostAt A.repAlloc x.G.remoteIk (s3.sp + 0x150#64) ∗
              vecU8At A.repAlloc (s3.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
              vecU8Buf A.repAlloc localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A.repAlloc remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A.repAlloc 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗
              ((s3.sp + 0x48#64) ↦₆₄ rootPtr') ∗
              ((s3.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗ F))
    (by rw [stackAt_chainClone_eq_alloc s3.sp]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  have hx20_3' : s3.readReg64 .x20 = localIk'.cap := by reg_chain
  have hx21_3' : s3.readReg64 .x21 = localIk'.ptr := by reg_chain
  have hx22_3' : s3.readReg64 .x22 = remoteIk'.cap := by reg_chain
  have hx26_3' : s3.readReg64 .x26 = remoteIk'.ptr := by reg_chain
  have hx23_3' : s3.readReg64 .x23 = s3.sp + 0x5f0#64 := by reg_chain
  refine seg_senderChain_placed hsenderClone hQp_false hfit4 hpc3 hrun3 hspA3
    hx20_3' hx21_3' hx22_3' hx26_3' hx23_3' hx28_3 htr3 hrc_lt
    fun s4 sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5 hpc4 hrun4 hsp4 hspA4 hx23_4 hx24_4 hx25_4 hx26_4 hx29_4 htr4 hinl => ?_
  have hsp_eq : s3.sp = s.sp := by reg_chain
  have hst_eq :
      M.stepEvents (senderChainOptCloneEvents x.G.sender x.st.senderChain) st3 =
        M.stepEvents (fields1To4Events x.G x.st) st := by
    dsimp only [st3, st2, st1, fields1To4Events]
    rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append]
  rw [hsp_eq] at hx23_4 ⊢
  rw [hst_eq]
  refine SepWPpCl.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hnext s4 localIk' remoteIk' rootPtr' sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5
      hpc4 hrun4 (by reg_chain) hspA4 hx23_4
      (by reg_chain)
      (by reg_chain)
      hx26_4
      (by reg_chain)
      htr4 hloc_b hloc_c hrem_b hrem_c hinl)

end LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneKeysPlacedBudget
