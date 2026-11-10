/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone4PlacedAuxBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneEpilogueBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import ProofLib.ProgramReflection
import ProofLib.RegChain
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `Chain::clone` (Block `524`)

Budget-threaded (`RustCliAllocBudget M` / `VmPreserved`) relocatable contracts on Block `524`
(`(blkPC_524).rebase (blkPl_524).base H`), proving `protoChain_clone_placed_ok`,
`chain_clone_placed_ok`, and `senderChain_clone_placed_ok` (plus hook and VM-hook variants).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone4PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (PublicKey maxMessageKeys)
open CryptoVerification (
  LibsignalPlacement lsρ lsRustNoAllocShimSym lsRustAllocSym lsMemcpySym ls_hook_ok_of_mem
)
open CryptoVerification.RustHeap (LayoutOk allocHookStack vecU8Buf)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (
  ChainCloneGhost chainCloneStack
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone.ChainCloneRegReadSimp (
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
)
open CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainCloneDefs (
  protoChainAt spillSlotsExist savedRegsOnStack sepWPp_pure_second
  vecU8Buf_pos_eq beq_ofNat_zero_eq_false srk_length_pos
  chainAt_eq_pure_sep chainSrkPosFrame chainAt_eq_srk_pos
  deadStackSlots stackAt_chainClone_eq_entry
)
open CryptoVerification.CliHandshake.Placed (blkPC_524 blkPl_524 blkLib_eq_524)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget RustLayoutOk VmPreserved allocMemcpyVmSpec
  fitsEvents_append rustAllocEvents
  rustCliAllocBudgetSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionShimBudgetSpec sessionMemcpyRegionBudgetSpec
  subroutine_ok_sessionShimBudget_of_rustAllocShimVm
  subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (
  ChainCloneEnv chainCloneEvents chainCloneSpec senderChainCloneSpec
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.ClonePlacedDefsBudget (
  protoChainCloneSpec sessionMemcpySpec sessionShimSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone4PlacedAuxBudget (
  chainCloneFromPrivEvents chainCloneEvents_of_srk_pos spAligned_sub_208
  chain_clone_placed_priv_nil chain_clone_placed_priv_pos
)
open LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneEpilogueBudget (
  chainClone_of_protoChainClone_gen senderChainClone_of_chainClone_gen
)

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## 1. Hook Bridges to `ClonePlacedDefsBudget.{sessionShimSpec, sessionMemcpySpec}` -/

theorem subroutine_ok_cloneShim_of_sessionShimBudget {P : Program} {a : BitVec 64}
    (h : subroutine_ok P a sessionShimBudgetSpec) :
    subroutine_ok P a sessionShimSpec := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec,
    sessionShimSpec] at hq ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.2.1, hq.1⟩, hq.2.2⟩

theorem subroutine_ok_cloneMemcpy_of_sessionMemcpyRegionBudget {P : Program} {a : BitVec 64}
    (h : subroutine_ok P a sessionMemcpyRegionBudgetSpec) :
    subroutine_ok P a sessionMemcpySpec := by
  refine subroutine_ok_mono h ?_ ?_
  · rintro ⟨dst, src, bs⟩ R s0 hp
    dsimp only [sessionMemcpySpec, sessionMemcpyRegionBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec, memcpyRegionSpec] at hp ⊢
    simpa only [sepConj_assoc] using hp
  · rintro ⟨dst, src, bs⟩ R s0 sf hq
    dsimp only [sessionMemcpySpec, sessionMemcpyRegionBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec, memcpyRegionSpec] at hq ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.2.1.1, hq.2.1.2, hq.1⟩, hq.2.2⟩

/-! ## 2. Entry Proof (`+0 → ret` on Block `524`) -/

set_option maxHeartbeats 1200000 in
theorem chain_clone_placed_entry [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (hshim : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsMemcpySym) sessionMemcpySpec)
    (x : ChainCloneGhost) (st : M.σ) (s0 : State) (hs0_align : s0.spAligned = true)
    (hfits_env : FitsEnv M lim st (ChainCloneEnv x.gc))
    (hpc : s0.pc = (blkPl_524).base)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x.dst)
    (hx1 : s0.readReg64 .x1 = x.src) :
    SepWPp ((blkPC_524).rebase (blkPl_524).base H) (s0.readReg64 (Reg.gpr 30#5)) s0
      (memRegion x.dst 104 ∗
        protoChainAt A.repAlloc x.gc x.src ∗
        A.pool lim st s0 ∗
        stackAt s0.sp chainCloneStack)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec M A lim).post (x, st) s0 sf))
      Qp := by
  have halloc_nooom := subroutine_ok_allocNoOom_of_budget halloc
  let evs_srk := rustAllocEvents x.gc.1.srk.bytes.length 1
  have hpriv_nil_lem := fun s' srkPtr' v8 v9 v10 v13
      (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
      (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
      (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
      (hpriv : x.gc.1.priv.bytes = [])
      (hevs_full : ChainCloneEnv x.gc (evs_srk ++ chainCloneFromPrivEvents x.gc))
      (hfits_rem : FitsEvents M lim (M.stepEvents evs_srk st) (chainCloneFromPrivEvents x.gc)) =>
    chain_clone_placed_priv_nil (M := M) (A := A) (lim := lim) (H := H) (Qp := Qp)
      hshim halloc hmemcpy x st evs_srk s0 s' hs0_align
      srkPtr' v8 v9 v10 v13 hsrk hmax hsrc_klen hpriv hevs_full hfits_rem
  have hpriv_pos_lem := fun s' srkPtr' v8 v9 v10 v13
      (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
      (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
      (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
      (hpriv_pos : 0 < x.gc.1.priv.bytes.length)
      (hevs_full : ChainCloneEnv x.gc (evs_srk ++ chainCloneFromPrivEvents x.gc))
      (hfits_rem : FitsEvents M lim (M.stepEvents evs_srk st) (chainCloneFromPrivEvents x.gc)) =>
    chain_clone_placed_priv_pos (M := M) (A := A) (lim := lim) (H := H) (Qp := Qp)
      hshim halloc hmemcpy x st evs_srk s0 s' hs0_align
      srkPtr' v8 v9 v10 v13 hsrk hmax hsrc_klen hpriv_pos hevs_full hfits_rem
  dsimp only [sessionShimSpec] at hshim
  dsimp only [sessionMemcpySpec] at hmemcpy
  generalize (fun sf P_f =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
      (P_f ⊢ (protoChainCloneSpec M A lim).post (x, st) s0 sf)) =
    postPred at hpriv_nil_lem hpriv_pos_lem ⊢
  have hx0' : s0.readReg64 (Reg.gpr 0#5) = x.dst := hx0
  have hx1' : s0.readReg64 (Reg.gpr 1#5) = x.src := hx1
  have hsp_sub_align : ((s0.sp - 208#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub_208 s0.sp hs0_align
  rw [chainAt_eq_pure_sep A.repAlloc x.gc x.src]
  simp only [sepConj_assoc]
  refine sepWPp_pure_second fun ⟨hsrk, hmax, hsrc_klen⟩ => ?_
  have hsrk_pos : 0 < x.gc.1.srk.bytes.length := srk_length_pos hsrk
  have hevs_eq : chainCloneEvents x.gc = evs_srk ++ chainCloneFromPrivEvents x.gc :=
    chainCloneEvents_of_srk_pos hsrk_pos
  have hevs_full : ChainCloneEnv x.gc (evs_srk ++ chainCloneFromPrivEvents x.gc) :=
    hevs_eq.symm
  have hfits_cat : FitsEvents M lim st (evs_srk ++ chainCloneFromPrivEvents x.gc) :=
    hevs_eq ▸ hfits_env (chainCloneEvents x.gc) rfl
  obtain ⟨hfits_srk, hfits_rem⟩ :=
    (fitsEvents_append M lim evs_srk (chainCloneFromPrivEvents x.gc) st).mp hfits_cat
  rw [chainAt_eq_srk_pos A.repAlloc x.gc x.src hsrk hmax hsrc_klen,
      stackAt_chainClone_eq_entry s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun v8 => SepWPp.exists_elim fun v9 =>
    SepWPp.exists_elim fun v10 => SepWPp.exists_elim fun v13 =>
    SepWPp.exists_elim fun v14 => SepWPp.exists_elim fun v15 =>
    SepWPp.exists_elim fun v16 => SepWPp.exists_elim fun v17 =>
    SepWPp.exists_elim fun v18 => SepWPp.exists_elim fun v19 =>
    SepWPp.exists_elim fun v20 => SepWPp.exists_elim fun v21 =>
    SepWPp.exists_elim fun v22 => SepWPp.exists_elim fun v23 =>
    SepWPp.exists_elim fun v24 => SepWPp.exists_elim fun v25 => ?_
  refine sepWPp_pure_second fun ⟨hsrk_le, hsrk_cap_lt, hsrk_ptr⟩ => ?_
  have hsrk_lt63 : x.gc.1.srk.bytes.length < 2 ^ 63 := by omega
  have hsrk_toNat : (BitVec.ofNat 64 x.gc.1.srk.bytes.length).toNat = x.gc.1.srk.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsrk_beq0 : (BitVec.ofNat 64 x.gc.1.srk.bytes.length == 0#64) = false :=
    beq_ofNat_zero_eq_false hsrk_pos (by omega)
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hsrk_lay : LayoutOk x.gc.1.srk.bytes.length 1 := ⟨hsrk_pos, hpow1, by omega⟩
  have hsrk_rlay : RustLayoutOk x.gc.1.srk.bytes.length 1 := ⟨hsrk_lay, by omega⟩
  apply SepWPp.of_sepWP (mid := (blkPl_524).base + 68#64)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_call hshim ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  have htr_sf : sf.trace = s0.trace := by reg_chain
  wp_compact
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_call halloc_nooom (x.gc.1.srk.bytes.length, 1, st)
  have htrace1 : sf_1.trace = s0.trace :=
    (‹AllocCallPreserved _ sf_1›).2.1.trans htr_sf
  rw [‹sf.sp = s0.sp - 208#64›]
  wp_compact
  apply SepWP.done ‹_› ‹_›
  have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹sf_1.readReg64 Reg.x0 ≠ 0#64›
  let srkPtr' := sf_1.readReg64 (Reg.gpr 0#5)
  have hfold_srk_post : ∀ (sPool : State),
      (A.pool lim (M.stepEvents evs_srk st) sPool ∗
        (srkPtr' ↦ₛ x.gc.1.srk.bytes) ∗
        (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        A.live srkPtr' x.gc.1.srk.bytes.length 1 ∗
        memRegion x.dst 104 ∗
        ((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
        ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        chainSrkPosFrame A.repAlloc x.gc x.src ∗
        spillSlotsExist s0.sp ∗
        deadStackSlots s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v25) ∗
        ((s0.sp - 136#64) ↦₆₄ v24) ∗
        ((s0.sp - 128#64) ↦₆₄ v23) ∗
        ((s0.sp - 104#64) ↦₆₄ v22) ∗
        ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) ⊢
      (memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        protoChainAt A.repAlloc x.gc x.src ∗
        A.pool lim (M.stepEvents evs_srk st) sPool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v25) ∗
        ((s0.sp - 136#64) ↦₆₄ v24) ∗
        ((s0.sp - 128#64) ↦₆₄ v23) ∗
        ((s0.sp - 104#64) ↦₆₄ v22) ∗
        savedRegsOnStack s0) := by
    intro sPool
    have hlive : A.repAlloc.live srkPtr' x.gc.1.srk.bytes.length 1 =
        A.live srkPtr' x.gc.1.srk.bytes.length 1 := rfl
    rw [vecU8Buf_pos_eq A.repAlloc srkPtr' x.gc.1.srk.bytes hsrk_pos hsrk_lt63 hoom64,
        hlive,
        chainAt_eq_srk_pos A.repAlloc x.gc x.src hsrk hmax hsrc_klen]
    unfold savedRegsOnStack deadStackSlots
    have hsrc_ent :
        (((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
          ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
          (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
          chainSrkPosFrame A.repAlloc x.gc x.src) ⊢
        (⌜x.gc.1.srk.bytes.length ≤ x.gc.1.srk.cap.toNat ∧
            x.gc.1.srk.cap.toNat < 2 ^ 63 ∧
            x.gc.1.srk.ptr ≠ 0⌝ ∗
          ((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
          ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
          (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
          chainSrkPosFrame A.repAlloc x.gc x.src) :=
      Entails.pure_right ⟨hsrk_le, hsrk_cap_lt, hsrk_ptr⟩ (Entails.refl _)
    have hgroup :
        (A.pool lim (M.stepEvents evs_srk st) sPool ∗
          (srkPtr' ↦ₛ x.gc.1.srk.bytes) ∗
          (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          A.live srkPtr' x.gc.1.srk.bytes.length 1 ∗
          memRegion x.dst 104 ∗
          ((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
          ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
          chainSrkPosFrame A.repAlloc x.gc x.src ∗
          spillSlotsExist s0.sp ∗
          ((∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
            (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
            (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b)) ∗
          ((s0.sp - 144#64) ↦₆₄ v25) ∗
          ((s0.sp - 136#64) ↦₆₄ v24) ∗
          ((s0.sp - 128#64) ↦₆₄ v23) ∗
          ((s0.sp - 104#64) ↦₆₄ v22) ∗
          ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
          ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
          ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) =
        (memRegion x.dst 104 ∗
          (A.live srkPtr' x.gc.1.srk.bytes.length 1 ∗ (srkPtr' ↦ₛ x.gc.1.srk.bytes)) ∗
          (((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
            ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
            (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
            chainSrkPosFrame A.repAlloc x.gc x.src) ∗
          A.pool lim (M.stepEvents evs_srk st) sPool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v25) ∗
          ((s0.sp - 136#64) ↦₆₄ v24) ∗
          ((s0.sp - 128#64) ↦₆₄ v23) ∗
          ((s0.sp - 104#64) ↦₆₄ v22) ∗
          (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
            ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
            ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
            ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
            ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
            ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
            ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
            ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
            ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
            (∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
            (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
            (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b))) := by
      sep_ac_rfl
    rw [hgroup]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hsrc_ent))
  apply SepWPp.of_sepWP (mid := (blkPl_524).base + 88#64)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  wp_call hmemcpy (sf_1.readReg64 Reg.x0, x.gc.1.srk.ptr, x.gc.1.srk.bytes)
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
  have htr_sf2 : sf_2.trace = s0.trace := by reg_chain
  wp_compact
  have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
  refine SepWP.done ‹_› ‹_› ?_
  refine SepWPp.weaken_pre (hfold_srk_post sf_2) ?_
  by_cases hpriv_nil : x.gc.1.priv.bytes = []
  · refine hpriv_nil_lem _ srkPtr' v25 v24 v23 v22 hsrk hmax hsrc_klen hpriv_nil hevs_full hfits_rem
      ‹_› ‹_› hsp_sf2 ?_ ‹_› ‹_› ‹_› ‹_› ‹_› htr_sf2 ‹_›
    rw [State.spAligned, hsp_sf2]
    exact hsp_sub_align
  · have hpriv_pos : 0 < x.gc.1.priv.bytes.length := List.length_pos_of_ne_nil hpriv_nil
    refine hpriv_pos_lem _ srkPtr' v25 v24 v23 v22 hsrk hmax hsrc_klen hpriv_pos hevs_full hfits_rem
      ‹_› ‹_› hsp_sf2 ?_ ‹_› ‹_› ‹_› ‹_› ‹_› htr_sf2 ‹_›
    rw [State.spAligned, hsp_sf2]
    exact hsp_sub_align

/-! ## 3. Top-Level `subroutine_ok` Contracts (`protoChainCloneSpec`, `chainCloneSpec`, `senderChainCloneSpec`) -/

theorem protoChain_clone_placed_ok_of_cloneHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsMemcpySym) sessionMemcpySpec) :
    subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (blkPl_524).base
      (protoChainCloneSpec M A lim) := by
  refine Arm64.subroutine_ok.of_codeLoaded fun ⟨x, st⟩ R s0 hpc hrun hpre hs0_align hloaded => ?_
  simp only [protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfits_env⟩, hmem⟩
  obtain ⟨sf, hsteps,
      ⟨hret, hrun_f, P_f, hmem_f, hsp_f, hcc_f, hpost_f⟩ |
      ⟨_, _, _, hpan_post⟩ |
      ⟨_, hfalse⟩⟩ :=
    chain_clone_placed_entry (Qp := fun _ _ => False) hshim halloc hmemcpy
      x st s0 hs0_align hfits_env hpc hrun hx0 hx1 R
      (by simpa [sepConj_assoc] using hmem) hloaded
  · exact Arm64.reaches_outcome_steps hsteps (reaches_outcome.of_outcome
      (Or.inl ⟨⟨hret, hsp_f, hrun_f⟩, ⟨hsp_f, hcc_f⟩,
        Satisfies.mono (sepConj_mono_left hpost_f) hmem_f⟩))
  · exact hpan_post.elim
  · exact (not_satisfies_false_sepConj hfalse).elim

theorem protoChain_clone_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (blkPl_524).base
      (protoChainCloneSpec M A lim) :=
  protoChain_clone_placed_ok_of_cloneHooks
    (subroutine_ok_cloneShim_of_sessionShimBudget hshim)
    halloc
    (subroutine_ok_cloneMemcpy_of_sessionMemcpyRegionBudget hmemcpy)

theorem protoChain_clone_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (blkPl_524).base
      (protoChainCloneSpec M A lim) :=
  protoChain_clone_placed_ok_of_hooks
    (ls_hook_ok_of_mem hshim)
    (ls_hook_ok_of_mem halloc)
    (ls_hook_ok_of_mem hmemcpy)

theorem chain_clone_placed_ok_of_cloneHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsMemcpySym) sessionMemcpySpec) :
    subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (blkPl_524).base
      (chainCloneSpec M A lim) :=
  chainClone_of_protoChainClone_gen
    (protoChain_clone_placed_ok_of_cloneHooks hshim halloc hmemcpy)

theorem chain_clone_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (blkPl_524).base
      (chainCloneSpec M A lim) :=
  chainClone_of_protoChainClone_gen
    (protoChain_clone_placed_ok_of_hooks hshim halloc hmemcpy)

theorem chain_clone_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (blkPl_524).base
      (chainCloneSpec M A lim) :=
  chainClone_of_protoChainClone_gen
    (protoChain_clone_placed_ok hshim halloc hmemcpy)

theorem chain_clone_placed_ok_of_vmHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (blkPl_524).base
      (chainCloneSpec M A lim) :=
  chain_clone_placed_ok_of_hooks
    (subroutine_ok_sessionShimBudget_of_rustAllocShimVm (ls_hook_ok_of_mem hshim))
    (ls_hook_ok_of_mem halloc)
    (subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm (ls_hook_ok_of_mem hmemcpy))

theorem senderChain_clone_placed_ok_of_cloneHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsMemcpySym) sessionMemcpySpec) :
    subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (blkPl_524).base
      (senderChainCloneSpec M A lim) :=
  senderChainClone_of_chainClone_gen
    (protoChain_clone_placed_ok_of_cloneHooks hshim halloc hmemcpy)

theorem senderChain_clone_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (blkPl_524).base
      (senderChainCloneSpec M A lim) :=
  senderChainClone_of_chainClone_gen
    (protoChain_clone_placed_ok_of_hooks hshim halloc hmemcpy)

theorem senderChain_clone_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (blkPl_524).base
      (senderChainCloneSpec M A lim) :=
  senderChainClone_of_chainClone_gen
    (protoChain_clone_placed_ok hshim halloc hmemcpy)

theorem senderChain_clone_placed_ok_of_vmHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (blkPl_524).base
      (senderChainCloneSpec M A lim) :=
  senderChain_clone_placed_ok_of_hooks
    (subroutine_ok_sessionShimBudget_of_rustAllocShimVm (ls_hook_ok_of_mem hshim))
    (ls_hook_ok_of_mem halloc)
    (subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm (ls_hook_ok_of_mem hmemcpy))

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone4PlacedBudget
