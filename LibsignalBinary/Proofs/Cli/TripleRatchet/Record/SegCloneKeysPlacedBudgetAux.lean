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
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget
public meta import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneKeysPlaced
public meta import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneKeys -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable CLI `SegClone` Entry and Fields 1–3

Proves entry frame initialization (`+0x1a8 → +0x1fc`) and cloning of `local_identity_key`,
`remote_identity_key`, and `root_key` (`+0x1fc → +0x290`) on CLI Block `463`, threading
`RustCliAllocBudget M` and `VmPreserved`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneKeysPlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open scoped LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (SenderChain SessionState)
open CryptoVerification (
  LibsignalPlacement lsmpl lsRustNoAllocShimSym lsRustAllocSym
)
open CryptoVerification.RustHeap (allocHookStack vecU8At vecU8Buf)
open CryptoVerification.LibsignalSessionRepr (VecGhost msgTypeByte vecGhostAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost SenderChainGhost)
open CryptoVerification.LibsignalTripleRatchet (
  RecordDecryptGhost sessionShimSpec sessionMemcpyRegionSpec
)
open CryptoVerification.LibsignalTripleRatchet.Record (errsAt)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps (
  cap_add_one_ne_zero cap_add_one_beq_zero_eq_false
  ofNat_ne_zero_of_pos beq_ofNat_zero_eq_false eq_nil_or_length_pos entails_pure_2nd
  vecU8At_eq_of_pos vecGhostAt_eq_of_nil vecGhostAt_eq_of_pos
  vecU8Buf_nil_eq vecU8Buf_pos_eq
)
open CryptoVerification.CliRatchet.DecPlaced (blkPC_463 blkPl_463)
open CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps (SepWPpCl sepWPpCl_pure_2nd)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved AllocCallPreserved
  RustLayoutOk FitsEvents rustAllocEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionShimBudgetSpec sessionMemcpyRegionBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (
  senderChainCloneEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (vecCloneEvents)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneBasePlacedBudget (
  SegCloneHooks SepWPpCl_of_sepWP_vm
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget (sepWP_cut_here)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Optional sender-chain clone `AllocEvent` sequence matching `segCloneEvents`. -/
def senderChainOptCloneEvents : Option SenderChainGhost → Option SenderChain → List AllocEvent
  | some gs, some sc => senderChainCloneEvents gs sc
  | _, _ => []

/-- Combined `AllocEvent` sequence for `SegClone` fields 1–4 (`localIk`, `remoteIk`, `rootKey`,
    `senderChain`), matching the prefix of `segCloneEvents`. -/
def fields1To4Events (G : SessionGhost) (st : SessionState (List (BitVec 8))) : List AllocEvent :=
  vecCloneEvents G.localIk ++
  vecCloneEvents G.remoteIk ++
  rustAllocEvents 32 1 ++
  senderChainOptCloneEvents G.sender st.senderChain

/-- Entry frame initialization (`+0x1a8 → +0x1fc`), threading `VmPreserved s s1` and polymorphic in
    `{Q Qp}`. -/
theorem seg_entry_to_0x1fc_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {H : String → Option (State → State)}
    {x : RecordDecryptGhost} {s0 s : State} {ret : BitVec 64}
    {Q Qp : State → SepProp → Prop}
    {v80 v88 v90 : BitVec 64} {v9c : BitVec 32}
    {v5b0 : BitVec 64} {v5bc : BitVec 8} {v5c0 v5c8 v5d0 v5d8 v5e0 v5e8 : BitVec 64}
    {F : SepProp}
    (hpc : s.pc = (blkPl_463).base + 0x1a8#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (h19 : s.readReg64 .x19 = x.remA) (h27 : s.readReg64 .x27 = x.sret)
    (h23 : s.readReg64 .x23 = s.sp + 0x5f0#64) (h24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcap : x.G.localIk.cap < 2 ^ 63)
    (hnext : ∀ s1 : State,
      VmPreserved s s1 →
      s1.pc = (blkPl_463).base + 0x1fc#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x23 = s.sp + 0x5f0#64 → s1.readReg64 .x24 = s.sp + 0xca0#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (((s.sp + 0x80#64) ↦₆₄ x.sret) ∗ ((s.sp + 0x88#64) ↦₆₄ x.locA) ∗
          ((s.sp + 0x90#64) ↦₆₄ x.msgA) ∗
          ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
          ((s.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s.sp + 0xf0#64) ↦₆₄ x.locA) ∗
          ((s.sp + 0x138#64) ↦₆₄ x.G.localIk.cap) ∗
          ((s.sp + 0x5b0#64) ↦₆₄ x.remA) ∗
          ((s.sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗
          ((s.sp + 0x5c0#64) ↦₆₄ (s.sp + 0x5bc#64)) ∗
          ((s.sp + 0x5c8#64) ↦₆₄ x.msgA) ∗
          ((s.sp + 0x5d0#64) ↦₆₄ (s.sp + 0x5b0#64)) ∗
          errsAt A.repAlloc (s.sp + 0x5d8#64) [] ∗
          ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗ F)
        Q Qp) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (((s.sp + 0x80#64) ↦₆₄ v80) ∗ ((s.sp + 0x88#64) ↦₆₄ v88) ∗
        ((s.sp + 0x90#64) ↦₆₄ v90) ∗ ((s.sp + 0x9c#64) ↦₃₂ v9c) ∗
        ((s.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s.sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((s.sp + 0x138#64) ↦₆₄ x.G.localIk.cap) ∗
        ((s.sp + 0x5b0#64) ↦₆₄ v5b0) ∗ ((s.sp + 0x5bc#64) ↦₈ v5bc) ∗
        ((s.sp + 0x5c0#64) ↦₆₄ v5c0) ∗ ((s.sp + 0x5c8#64) ↦₆₄ v5c8) ∗
        ((s.sp + 0x5d0#64) ↦₆₄ v5d0) ∗ ((s.sp + 0x5d8#64) ↦₆₄ v5d8) ∗
        ((s.sp + 0x5e0#64) ↦₆₄ v5e0) ∗ ((s.sp + 0x5e8#64) ↦₆₄ v5e8) ∗
        ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗ F)
      Q Qp := by
  have hcmn : x.G.localIk.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap
  have hcmn_beq : (x.G.localIk.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap
  apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (508))
  by_vm_steps
    wp_steps
    refine SepWP.done (by segCloneKeys_close) hrun
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    refine SepWPpCl.weaken_pre ?_
      (hnext _ hvm (by segCloneKeys_close) hrun rfl hsp h23 h24 rfl htr)
    dsimp only [errsAt, msgTypeByte, BitVec.zeroExtend]
    have h5e0 : s.sp + 0x5d8#64 + 8#64 = s.sp + 0x5e0#64 := by bv_arith
    have h5e8 : s.sp + 0x5d8#64 + 16#64 = s.sp + 0x5e8#64 := by bv_arith
    rw [h5e0, h5e8]
    exact Entails.of_eq (by sep_ac_rfl)

/-- Clone `local_identity_key` (`+0x1fc → +0x504 / +0x238`), threading `A.pool` across
    `vecCloneEvents x.G.localIk`. -/
theorem seg_localIk_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : String → Option (State → State)} (hA : SegCloneHooks A lim H)
    {x : RecordDecryptGhost} {s0 s : State} {ret : BitVec 64}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (hfits : FitsEvents M lim st (vecCloneEvents x.G.localIk))
    (hpc : s.pc = (blkPl_463).base + 0x1fc#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (localIk' : VecGhost),
      s1.pc = (if x.G.remoteIk.bytes = []
        then (blkPl_463).base + 0x504#64
        else (blkPl_463).base + 0x238#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x20 = localIk'.cap →
      s1.readReg64 .x21 = localIk'.ptr →
      s1.readReg64 .x22 = BitVec.ofNat 64 x.G.remoteIk.bytes.length →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = x.st.sessionVersion.setWidth 64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      localIk'.bytes = x.G.localIk.bytes →
      localIk'.cap = BitVec.ofNat 64 x.G.localIk.bytes.length →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (A.pool lim (M.stepEvents (vecCloneEvents x.G.localIk) st) s1 ∗
          vecGhostAt A.repAlloc x.G.localIk (s.sp + 0x138#64) ∗
          vecU8Buf A.repAlloc localIk'.cap localIk'.ptr localIk'.bytes ∗
          ((s.sp + 0x160#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
          ((s.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
          stackAt s.sp allocHookStack ∗ F)
        Q Qp) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (A.pool lim st s ∗ vecGhostAt A.repAlloc x.G.localIk (s.sp + 0x138#64) ∗
        ((s.sp + 0x160#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
        ((s.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q Qp := by
  have h140 : s.sp + 0x138#64 + 8#64 = s.sp + 0x140#64 := by bv_arith
  have h148 : s.sp + 0x138#64 + 16#64 = s.sp + 0x148#64 := by bv_arith
  rcases eq_nil_or_length_pos x.G.localIk.bytes with hloc | hloc
  · have hevs : vecCloneEvents x.G.localIk = [] := by simp [vecCloneEvents, hloc]
    rw [vecGhostAt_eq_of_nil A.repAlloc x.G.localIk (s.sp + 0x138#64) hloc, h140, h148]
    simp only [sepConj_assoc]
    refine sepWPpCl_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
    have hpc_rem :
        (if ¬(BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = true then (blkPl_463).base + bv% (568) else (blkPl_463).base + bv% (1284)) =
        (if x.G.remoteIk.bytes = [] then (blkPl_463).base + bv% (1284) else (blkPl_463).base + bv% (568)) := by
      rcases eq_nil_or_length_pos x.G.remoteIk.bytes with hrem | hrem
      · simp [hrem]
      · have hne : x.G.remoteIk.bytes ≠ [] := List.ne_nil_of_length_pos hrem
        have hbeq : (BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = false :=
          beq_ofNat_zero_eq_false hrem (by omega)
        simp [hne, hbeq]
    apply SepWPpCl_of_sepWP_vm
      (mid := if x.G.remoteIk.bytes = [] then (blkPl_463).base + bv% (1284) else (blkPl_463).base + bv% (568))
    by_vm_steps
      wp_steps
      refine SepWP.done (by segCloneKeys_close) hrun
        ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
      let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm
      have hpool := A.pool_transport lim st s s_end hvm
      refine SepWPpCl.weaken_pre ?_
        (hnext s_end ⟨0#64, 1#64, []⟩ (by segCloneKeys_close) hrun rfl hsp
          rfl rfl rfl rfl rfl rfl rfl htr hloc.symm (by simp [hloc]))
      rw [hevs, M.stepEvents_nil, hpool,
          vecGhostAt_eq_of_nil A.repAlloc x.G.localIk (s.sp + 0x138#64) hloc, h140, h148,
          vecU8Buf_nil_eq A.repAlloc]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact entails_pure_2nd ⟨hcap_lt, hptr⟩ (by sep_ac_rfl)
  · have hevs : vecCloneEvents x.G.localIk = rustAllocEvents x.G.localIk.bytes.length 1 := by
      simp [vecCloneEvents, Nat.ne_of_gt hloc]
    have hfit_alloc : FitsEvents M lim st (rustAllocEvents x.G.localIk.bytes.length 1) :=
      hevs ▸ hfits
    rw [vecGhostAt_eq_of_pos A.repAlloc x.G.localIk (s.sp + 0x138#64) hloc, h140, h148]
    simp only [sepConj_assoc]
    refine sepWPpCl_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hshim := hA.shim_ok
    have halloc := hA.allocNoOom_ok
    have hmemcpy := hA.memcpy_ok
    dsimp only [sessionShimBudgetSpec, sessionShimSpec] at hshim
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec] at hmemcpy
    have hloc_lt : x.G.localIk.bytes.length < 2 ^ 63 := by omega
    have hloc_le63 : x.G.localIk.bytes.length + 1 ≤ 2 ^ 63 := by omega
    have hloc_le64 : x.G.localIk.bytes.length ≤ 2 ^ 64 := by omega
    have hloc_ne : BitVec.ofNat 64 x.G.localIk.bytes.length ≠ 0#64 :=
      ofNat_ne_zero_of_pos hloc (by omega)
    have hloc_beq : (BitVec.ofNat 64 x.G.localIk.bytes.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hloc (by omega)
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : RustLayoutOk x.G.localIk.bytes.length 1 := ⟨⟨hloc, hpow2, hloc_le63⟩, by decide⟩
    have htoNat : (BitVec.ofNat 64 x.G.localIk.bytes.length).toNat = x.G.localIk.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpc_rem :
        (if (BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = true then (blkPl_463).base + bv% (1284) else (blkPl_463).base + bv% (568)) =
        (if x.G.remoteIk.bytes = [] then (blkPl_463).base + bv% (1284) else (blkPl_463).base + bv% (568)) := by
      rcases eq_nil_or_length_pos x.G.remoteIk.bytes with hrem | hrem
      · simp [hrem]
      · have hne : x.G.remoteIk.bytes ≠ [] := List.ne_nil_of_length_pos hrem
        have hbeq : (BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = false :=
          beq_ofNat_zero_eq_false hrem (by omega)
        simp [hne, hbeq]
    apply SepWPpCl.of_sepWP
      (mid := if x.G.remoteIk.bytes = [] then (blkPl_463).base + bv% (1284) else (blkPl_463).base + bv% (568))
    apply sepWP_cut_here (mid := lsmpl.ρ lsRustNoAllocShimSym)
    by_vm_open (
      wp_steps
      refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close)
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩
      intro hvm1
      refine SepWP.transport_budgetPool hvm1 (hnext := ?_); clear hvm1
      wp_call hshim ()
      clear hshim
      refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
      have htr_sf : sf.trace = s0.trace :=
        (‹sf.trace = _›).trans (by simp only [wp_norm, arm64_norm, htr.1])
      have hsp_sf : sf.sp = s.sp := (‹sf.sp = _›).trans (by segCloneKeys_close)
      rw [show stackAt s.sp allocHookStack = stackAt sf.sp allocHookStack from
        congrArg (stackAt · allocHookStack) hsp_sf.symm]
      apply sepWP_cut_here (mid := lsmpl.ρ lsRustAllocSym)
      by_vm_open (
        wp_steps
        refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close)
          ⟨by simp only [wp_norm, arm64_norm], ?_⟩
        intro hvm2
        refine SepWP.transport_budgetPool hvm2 (hnext := ?_); clear hvm2
        wp_call halloc (x.G.localIk.bytes.length, 1, st)
        clear halloc
        have hacp : AllocCallPreserved sf sf_1 := by assumption
        have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹sf_1.readReg64 .x0 ≠ 0#64›
        have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
          beq_eq_false_iff_ne.mpr hoom64
        have htr_sf1 : sf_1.trace = s0.trace :=
          hacp.2.1.trans (by simp only [wp_norm, arm64_norm, htr_sf])
        try dsimp only [Bool.false_eq_true, ↓reduceIte]
        apply sepWP_cut_here (mid := lsmpl.ρ "memcpy")
        by_vm_open (
          wp_steps
          refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close)
            ⟨by simp only [wp_norm, arm64_norm], ?_⟩
          intro hvm3
          wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.localIk.ptr, x.G.localIk.bytes)
          clear hmemcpy
          refine SepWP.transport_budgetPool (hvm3.trans (by assumption)) (hnext := ?_); clear hvm3
          have htr_sf2 : sf_2.trace = s0.trace :=
            (‹sf_2.trace = _›).trans (by simp only [wp_norm, arm64_norm, htr_sf1])
          by_vm_open (
            wp_steps
            refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close)
              ⟨by simp only [wp_norm, arm64_norm], ?_⟩
            intro hvm4
            let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm4
            have hpool4 := A.pool_transport lim
              (M.stepEvents (rustAllocEvents x.G.localIk.bytes.length 1) st) sf_2 s_end hvm4
            refine SepWPpCl.weaken_pre ?_
              (hnext s_end ⟨BitVec.ofNat 64 x.G.localIk.bytes.length, sf_1.readReg64 (Reg.gpr 0#5), x.G.localIk.bytes⟩
                (by dsimp only [s_end]; segCloneKeys_close) (by dsimp only [s_end]; segCloneKeys_close)
                (by dsimp only [s_end]; segCloneKeys_close) (by dsimp only [s_end]; segCloneKeys_close)
                (by dsimp only [s_end]; segCloneKeys_close) (by dsimp only [s_end]; segCloneKeys_close)
                (by dsimp only [s_end]; segCloneKeys_close) (by dsimp only [s_end]; segCloneKeys_close)
                (by dsimp only [s_end]; segCloneKeys_close) (by dsimp only [s_end]; segCloneKeys_close)
                (by dsimp only [s_end]; segCloneKeys_close)
                ⟨by simp only [s_end, wp_norm, arm64_norm, htr_sf2], by dsimp only [s_end]; segCloneKeys_close⟩ rfl rfl)
            rw [hevs, hpool4,
                vecGhostAt_eq_of_pos A.repAlloc x.G.localIk (s.sp + 0x138#64) hloc, h140, h148,
                vecU8Buf_pos_eq A.repAlloc (sf_1.readReg64 (Reg.gpr 0#5)) x.G.localIk.bytes hloc hloc_lt hoom64]
            dsimp only [RustCliAllocBudget.repAlloc]
            simp only [sepConj_assoc, hsp_sf]
            exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by sep_ac_rfl)
          )
        )
      )
    )

/-- Clone `remote_identity_key` (`+0x504 / +0x238 → +0x268`), threading `A.pool` across
    `vecCloneEvents x.G.remoteIk`. -/
theorem seg_remoteIk_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : String → Option (State → State)} (hA : SegCloneHooks A lim H)
    {x : RecordDecryptGhost} {s0 s : State} {ret : BitVec 64}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (hfits : FitsEvents M lim st (vecCloneEvents x.G.remoteIk))
    (hpc : s.pc = (if x.G.remoteIk.bytes = []
      then (blkPl_463).base + 0x504#64
      else (blkPl_463).base + 0x238#64))
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 x.G.remoteIk.bytes.length)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (remoteIk' : VecGhost),
      s1.pc = (blkPl_463).base + 0x268#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = remoteIk'.cap →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = remoteIk'.ptr →
      s1.readReg64 .x28 = 32#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      remoteIk'.bytes = x.G.remoteIk.bytes →
      remoteIk'.cap = BitVec.ofNat 64 x.G.remoteIk.bytes.length →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (A.pool lim (M.stepEvents (vecCloneEvents x.G.remoteIk) st) s1 ∗
          vecGhostAt A.repAlloc x.G.remoteIk (s.sp + 0x150#64) ∗
          vecU8Buf A.repAlloc remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
          ((s.sp + 0x178#64) ↦₆₄ 32#64) ∗
          stackAt s.sp allocHookStack ∗ F)
        Q Qp) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (A.pool lim st s ∗ vecGhostAt A.repAlloc x.G.remoteIk (s.sp + 0x150#64) ∗
        ((s.sp + 0x178#64) ↦₆₄ 32#64) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q Qp := by
  have h158 : s.sp + 0x150#64 + 8#64 = s.sp + 0x158#64 := by bv_arith
  have h160 : s.sp + 0x150#64 + 16#64 = s.sp + 0x160#64 := by bv_arith
  rcases eq_nil_or_length_pos x.G.remoteIk.bytes with hrem | hrem
  · have hevs : vecCloneEvents x.G.remoteIk = [] := by simp [vecCloneEvents, hrem]
    simp only [hrem, ↓reduceIte] at hpc
    rw [hrem] at hx22
    rw [vecGhostAt_eq_of_nil A.repAlloc x.G.remoteIk (s.sp + 0x150#64) hrem, h158, h160]
    simp only [sepConj_assoc]
    refine sepWPpCl_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
    apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (616))
    by_vm_steps
      wp_steps
      refine SepWP.done rfl hrun
        ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
      let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm
      have hpool := A.pool_transport lim st s s_end hvm
      refine SepWPpCl.weaken_pre ?_
        (hnext s_end ⟨0#64, 1#64, []⟩ rfl hrun rfl hsp
          rfl rfl hx22 rfl rfl rfl rfl rfl rfl htr
          hrem.symm (by simp [hrem]))
      rw [hevs, M.stepEvents_nil, hpool,
          vecGhostAt_eq_of_nil A.repAlloc x.G.remoteIk (s.sp + 0x150#64) hrem, h158, h160,
          vecU8Buf_nil_eq A.repAlloc]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact entails_pure_2nd ⟨hcap_lt, hptr⟩ (by sep_ac_rfl)
  · have hevs : vecCloneEvents x.G.remoteIk = rustAllocEvents x.G.remoteIk.bytes.length 1 := by
      simp [vecCloneEvents, Nat.ne_of_gt hrem]
    have hfit_alloc : FitsEvents M lim st (rustAllocEvents x.G.remoteIk.bytes.length 1) :=
      hevs ▸ hfits
    have hrem_ne_nil : x.G.remoteIk.bytes ≠ [] := List.ne_nil_of_length_pos hrem
    simp only [hrem_ne_nil, ↓reduceIte] at hpc
    rw [vecGhostAt_eq_of_pos A.repAlloc x.G.remoteIk (s.sp + 0x150#64) hrem, h158, h160]
    simp only [sepConj_assoc]
    refine sepWPpCl_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hshim := hA.shim_ok
    have halloc := hA.allocNoOom_ok
    have hmemcpy := hA.memcpy_ok
    dsimp only [sessionShimBudgetSpec, sessionShimSpec] at hshim
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec] at hmemcpy
    have hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63 := by omega
    have hrem_le63 : x.G.remoteIk.bytes.length + 1 ≤ 2 ^ 63 := by omega
    have hrem_le64 : x.G.remoteIk.bytes.length ≤ 2 ^ 64 := by omega
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : RustLayoutOk x.G.remoteIk.bytes.length 1 := ⟨⟨hrem, hpow2, hrem_le63⟩, by decide⟩
    have htoNat : (BitVec.ofNat 64 x.G.remoteIk.bytes.length).toNat = x.G.remoteIk.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (616))
    apply sepWP_cut_here (mid := lsmpl.ρ lsRustNoAllocShimSym)
    by_vm_open (
      wp_steps
      refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close)
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩
      intro hvm1
      refine SepWP.transport_budgetPool hvm1 (hnext := ?_); clear hvm1
      wp_call hshim ()
      clear hshim
      refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
      have htr_sf : sf.trace = s0.trace :=
        (‹sf.trace = _›).trans (by simp only [wp_norm, arm64_norm, htr.1])
      have hsp_sf : sf.sp = s.sp := (‹sf.sp = _›).trans (by segCloneKeys_close)
      rw [show stackAt s.sp allocHookStack = stackAt sf.sp allocHookStack from
        congrArg (stackAt · allocHookStack) hsp_sf.symm]
      apply sepWP_cut_here (mid := lsmpl.ρ lsRustAllocSym)
      by_vm_open (
        wp_steps
        refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close)
          ⟨by simp only [wp_norm, arm64_norm], ?_⟩
        intro hvm2
        refine SepWP.transport_budgetPool hvm2 (hnext := ?_); clear hvm2
        wp_call halloc (x.G.remoteIk.bytes.length, 1, st)
        clear halloc
        have hacp : AllocCallPreserved sf sf_1 := by assumption
        have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹sf_1.readReg64 .x0 ≠ 0#64›
        have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
          beq_eq_false_iff_ne.mpr hoom64
        have htr_sf1 : sf_1.trace = s0.trace :=
          hacp.2.1.trans (by simp only [wp_norm, arm64_norm, htr_sf])
        try dsimp only [Bool.false_eq_true, ↓reduceIte]
        apply sepWP_cut_here (mid := lsmpl.ρ "memcpy")
        by_vm_open (
          wp_steps
          refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close)
            ⟨by simp only [wp_norm, arm64_norm], ?_⟩
          intro hvm3
          wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.remoteIk.ptr, x.G.remoteIk.bytes)
          clear hmemcpy
          refine SepWP.transport_budgetPool (hvm3.trans (by assumption)) (hnext := ?_); clear hvm3
          have htr_sf2 : sf_2.trace = s0.trace :=
            (‹sf_2.trace = _›).trans (by simp only [wp_norm, arm64_norm, htr_sf1])
          by_vm_open (
            wp_steps
            refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close)
              ⟨by simp only [wp_norm, arm64_norm], ?_⟩
            intro hvm4
            let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm4
            have hpool4 := A.pool_transport lim
              (M.stepEvents (rustAllocEvents x.G.remoteIk.bytes.length 1) st) sf_2 s_end hvm4
            refine SepWPpCl.weaken_pre ?_
              (hnext s_end ⟨BitVec.ofNat 64 x.G.remoteIk.bytes.length, sf_1.readReg64 (Reg.gpr 0#5), x.G.remoteIk.bytes⟩
                (by dsimp only [s_end]; segCloneKeys_close) (by dsimp only [s_end]; segCloneKeys_close)
                (by dsimp only [s_end]; segCloneKeys_close) (by dsimp only [s_end]; segCloneKeys_close)
                (by dsimp only [s_end]; segCloneKeys_close) (by dsimp only [s_end]; segCloneKeys_close)
                (by dsimp only [s_end]; segCloneKeys_close) (by dsimp only [s_end]; segCloneKeys_close)
                (by dsimp only [s_end]; segCloneKeys_close) (by dsimp only [s_end]; segCloneKeys_close)
                (by dsimp only [s_end]; segCloneKeys_close) (by dsimp only [s_end]; segCloneKeys_close)
                (by dsimp only [s_end]; segCloneKeys_close)
                ⟨by simp only [s_end, wp_norm, arm64_norm, htr_sf2], by dsimp only [s_end]; segCloneKeys_close⟩ rfl rfl)
            rw [hevs, hpool4,
                vecGhostAt_eq_of_pos A.repAlloc x.G.remoteIk (s.sp + 0x150#64) hrem, h158, h160,
                vecU8Buf_pos_eq A.repAlloc (sf_1.readReg64 (Reg.gpr 0#5)) x.G.remoteIk.bytes hrem hrem_lt hoom64]
            dsimp only [RustCliAllocBudget.repAlloc]
            simp only [sepConj_assoc, hsp_sf]
            exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by sep_ac_rfl)
          )
        )
      )
    )

/-- Clone `root_key` (`+0x268 → +0x290`, 32 bytes) and store the new pointer at `[sp + 0x48]`,
    threading `A.pool` across `rustAllocEvents 32 1`. -/
theorem seg_rootKey_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : String → Option (State → State)} (hA : SegCloneHooks A lim H)
    {x : RecordDecryptGhost} {s0 s : State} {ret : BitVec 64}
    {Q Qp : State → SepProp → Prop} {v48 : BitVec 64} {F : SepProp}
    (hfits : FitsEvents M lim st (rustAllocEvents 32 1))
    (hpc : s.pc = (blkPl_463).base + 0x268#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx28 : s.readReg64 .x28 = 32#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (rootPtr' : BitVec 64),
      s1.pc = (blkPl_463).base + 0x290#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x28 = 32#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (A.pool lim (M.stepEvents (rustAllocEvents 32 1) st) s1 ∗
          vecU8At A.repAlloc (s.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
          vecU8Buf A.repAlloc 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗
          ((s.sp + 0x48#64) ↦₆₄ rootPtr') ∗
          stackAt s.sp allocHookStack ∗ F)
        Q Qp) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (A.pool lim st s ∗
        vecU8At A.repAlloc (s.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        ((s.sp + 0x48#64) ↦₆₄ v48) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q Qp := by
  have hshim := hA.shim_ok
  have halloc := hA.allocNoOom_ok
  have hmemcpy := hA.memcpy_ok
  dsimp only [sessionShimBudgetSpec, sessionShimSpec] at hshim
  dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec] at hmemcpy
  have h170 : s.sp + 0x168#64 + 8#64 = s.sp + 0x170#64 := by bv_arith
  have h178 : s.sp + 0x168#64 + 16#64 = s.sp + 0x178#64 := by bv_arith
  have hroot_len : (keyToBytes32 x.st.rootKey).length = 32 := by simp [keyToBytes32]
  have hroot_pos : 0 < (keyToBytes32 x.st.rootKey).length := by omega
  have hroot_lt : (keyToBytes32 x.st.rootKey).length < 2 ^ 63 := by omega
  have hroot_le64 : (keyToBytes32 x.st.rootKey).length ≤ 2 ^ 64 := by omega
  rw [vecU8At_eq_of_pos A.repAlloc (s.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) hroot_pos,
      h170, h178]
  simp only [sepConj_assoc]
  refine sepWPpCl_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
  have h32_pos : 0 < 32 := by decide
  have h32_le63 : 32 + 1 ≤ 2 ^ 63 := by decide
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : RustLayoutOk 32 1 := ⟨⟨h32_pos, hpow2, h32_le63⟩, by decide⟩
  obtain ⟨⟨hwmax, henf, hram, hva⟩, _⟩ := hfits
  apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (656))
  apply sepWP_cut_here (mid := lsmpl.ρ lsRustNoAllocShimSym)
  by_vm_open (
    wp_steps
    refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close)
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩
    intro hvm1
    refine SepWP.transport_budgetPool hvm1 (hnext := ?_); clear hvm1
    wp_call hshim ()
    clear hshim
    refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
    have htr_sf : sf.trace = s0.trace :=
      (‹sf.trace = _›).trans (by simp only [wp_norm, arm64_norm, htr.1])
    have hsp_sf : sf.sp = s.sp := (‹sf.sp = _›).trans (by segCloneKeys_close)
    rw [show stackAt s.sp allocHookStack = stackAt sf.sp allocHookStack from
      congrArg (stackAt · allocHookStack) hsp_sf.symm]
    apply sepWP_cut_here (mid := lsmpl.ρ lsRustAllocSym)
    by_vm_open (
      wp_steps
      refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close)
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩
      intro hvm2
      refine SepWP.transport_budgetPool hvm2 (hnext := ?_); clear hvm2
      wp_call halloc (32, 1, st)
      clear halloc
      have hacp : AllocCallPreserved sf sf_1 := by assumption
      have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹sf_1.readReg64 .x0 ≠ 0#64›
      have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hoom64
      have htr_sf1 : sf_1.trace = s0.trace :=
        hacp.2.1.trans (by simp only [wp_norm, arm64_norm, htr_sf])
      try dsimp only [Bool.false_eq_true, ↓reduceIte]
      have hmem32 :
          memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
            memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (keyToBytes32 x.st.rootKey).length := by
        rw [hroot_len]
      rw [hmem32]
      apply sepWP_cut_here (mid := lsmpl.ρ "memcpy")
      by_vm_open (
        wp_steps
        refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close)
          ⟨by simp only [wp_norm, arm64_norm], ?_⟩
        intro hvm3
        refine SepWP.transport_budgetPool hvm3 (hnext := ?_); clear hvm3
        wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.root.ptr, keyToBytes32 x.st.rootKey)
        clear hmemcpy
        refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
        have htr_sf2 : sf_2.trace = s0.trace :=
          (‹sf_2.trace = _›).trans (by simp only [wp_norm, arm64_norm, htr_sf1])
        refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close) ?_
        refine SepWPpCl.weaken_pre ?_
          (hnext sf_2 (sf_1.readReg64 (Reg.gpr 0#5))
            (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close)
            (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close)
            (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close)
            (by segCloneKeys_close) (by segCloneKeys_close) ⟨htr_sf2, by segCloneKeys_close⟩)
        have hbuf32 :
            vecU8Buf A.repAlloc 32#64 (sf_1.readReg64 (Reg.gpr 0#5)) (keyToBytes32 x.st.rootKey) =
              A.live (sf_1.readReg64 (Reg.gpr 0#5)) 32 1 ∗
                (sf_1.readReg64 (Reg.gpr 0#5) ↦ₛ keyToBytes32 x.st.rootKey) := by
          have h := vecU8Buf_pos_eq A.repAlloc (sf_1.readReg64 (Reg.gpr 0#5)) (keyToBytes32 x.st.rootKey)
            hroot_pos hroot_lt hoom64
          rwa [hroot_len] at h
        rw [vecU8At_eq_of_pos A.repAlloc (s.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) hroot_pos,
            h170, h178, hbuf32]
        dsimp only [RustCliAllocBudget.repAlloc]
        simp only [sepConj_assoc, hsp_sf]
        exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by sep_ac_rfl)
      )
    )
  )

end LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneKeysPlacedBudgetAux
