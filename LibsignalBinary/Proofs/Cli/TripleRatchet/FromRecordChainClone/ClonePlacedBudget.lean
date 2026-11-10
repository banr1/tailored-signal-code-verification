/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.ClonePlacedPrefixBudget
public import LibsignalBinary.Heap.SpecBudget
public meta import Lean
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import ProofLib.ProgramReflection
import ProofLib.RegChain
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `session_structure::Chain::clone` Proof

Proves `chainCloneSpec M A lim` and `senderChainCloneSpec M A lim` for
`<session_structure::Chain as Clone>::clone` (block `468`) under `[LibsignalPlacement]` and
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.ClonePlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.Ratchet (clampScalar)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (
  ChainKey PublicKey ReceiverChain SenderChain maxMessageKeys
)
open CryptoVerification (
  LibsignalPlacement lsρ lsRustNoAllocShimSym lsRustAllocSym lsMemcpySym
  ls_hook_ok_of_mem
)
open CryptoVerification.CliRatchet.Placed (blkPC_468 blkPl_468 blkLib_eq_468)
open CryptoVerification.RustHeap (
  RustAlloc allocHookStack vecU8Buf
)
open CryptoVerification.LibsignalSessionRepr (
  ChainGhost chainAt optChainKeyAt
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SenderChainGhost optSenderChainAt
)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpyRegionSpec)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (
  ChainCloneGhost SenderChainCloneGhost chainCloneStack
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone.ChainCloneRegReadSimp (
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget RustLayoutOk
  FitsEvents FitsEnv fitsEvents_append rustAllocEvents
  rustCliAllocBudgetSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (
  chainCloneEvents ChainCloneEnv fitsEvents_chainClone_of_fitsEnv
  chainCloneSpec SenderChainCloneEnv senderChainCloneSpec
)
open CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainCloneDefs (
  protoChainAt clonedOptChainKeyBuf spillSlotsExist savedRegsOnStack
  srk_length_pos vecU8Buf_nil_eq vecU8Buf_pos_eq
  beq_ofNat_zero_eq_false chainAt_eq_ck_some chainCkSomeFrame
  cap_add_one_beq_zero_false chainAt_eq_ck_none_cap chainAt_eq_ck_some_cap chainCkSomeCapFrame
  chainAt_eq_priv_len chainPrivLenFrame chainAt_eq_priv_pos chainPrivPosFrame
  sepWPp_pure_second chainAt_eq_pure_sep chainAt_eq_srk_pos chainSrkPosFrame
  deadStackSlots stackAt_chainClone_eq_entry
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.ClonePlacedDefsBudget (
  protoChainCloneSpec sessionShimSpec sessionMemcpySpec
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.ClonePlacedMidBudget (
  chainCloneMkEvents chain_clone_placed_mks_nil chain_clone_placed_mks_nonempty
  chain_clone_placed_ck_none
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.ClonePlacedPrefixBudget (
  srkEvents privEvents ckEvents chainCloneEvents_decomp
  srkEvents_of_pos privEvents_of_nil privEvents_of_pos ckEvents_of_none ckEvents_of_some
  chain_clone_placed_ck_some chain_clone_placed_priv_nil chain_clone_placed_priv_pos
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

private theorem subroutine_ok_sessionShimSpec_of_withVmPreserved {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      (withVmPreserved CryptoVerification.LibsignalTripleRatchet.sessionShimSpec)) :
    subroutine_ok prog entry sessionShimSpec := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withVmPreserved, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec,
    sessionShimSpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  rcases hq with ⟨hvm, hq⟩
  rw [satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1, hvm⟩, hq.2⟩

private theorem subroutine_ok_sessionMemcpySpec_of_withVmPreserved {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withVmPreserved sessionMemcpyRegionSpec)) :
    subroutine_ok prog entry sessionMemcpySpec := by
  refine subroutine_ok_mono h
    (fun (dst, src, bs) _ _ hp => by
      dsimp only [withVmPreserved, sessionMemcpyRegionSpec, memcpyRegionSpec,
        sessionMemcpySpec] at hp ⊢
      exact hp)
    (fun (dst, src, bs) _ _ _ hq => ?_)
  dsimp only [withVmPreserved, sessionMemcpyRegionSpec, memcpyRegionSpec,
    sessionMemcpySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  rcases hq with ⟨hvm, hq⟩
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1, hq.1.2, hvm⟩, hq.2⟩

/-! ## Full `Chain::clone` Entry Proof (Block `468`) -/

set_option maxHeartbeats 1200000 in
theorem chain_clone_placed_entry [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (hshim : subroutine_ok ((blkPC_468).rebase (blkPl_468).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_468).rebase (blkPl_468).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_468).rebase (blkPl_468).base H)
      (lsρ lsMemcpySym) sessionMemcpySpec)
    (x : ChainCloneGhost) (st_init : M.σ) (s0 : State) (hs0_align : s0.spAligned = true)
    (hfits_env : FitsEnv M lim st_init (ChainCloneEnv x.gc))
    (hpc : s0.pc = (blkPl_468).base)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x.dst)
    (hx1 : s0.readReg64 .x1 = x.src) :
    SepWPp ((blkPC_468).rebase (blkPl_468).base H) (s0.readReg64 (Reg.gpr 30#5)) s0
      (memRegion x.dst 104 ∗
        protoChainAt A.repAlloc x.gc x.src ∗
        A.pool lim st_init s0 ∗
        stackAt s0.sp chainCloneStack)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec M A lim).post (x, st_init) s0 sf))
      Qp := by
  have halloc_nooom := subroutine_ok_allocNoOom_of_budget halloc
  dsimp only [sessionShimSpec] at hshim
  dsimp only [sessionMemcpySpec] at hmemcpy
  have hx0' : s0.readReg64 (Reg.gpr 0#5) = x.dst := hx0
  have hx1' : s0.readReg64 (Reg.gpr 1#5) = x.src := hx1
  have hsp_sub_align : ((s0.sp - 208#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 208 hs0_align (by decide)
  rw [chainAt_eq_pure_sep A.repAlloc x.gc x.src]
  simp only [sepConj_assoc]
  refine sepWPp_pure_second fun ⟨hsrk, hmax, hsrc_klen⟩ => ?_
  have hsrk_pos : 0 < x.gc.1.srk.bytes.length := srk_length_pos hsrk
  have hfits_all := fitsEvents_chainClone_of_fitsEnv M lim st_init x.gc hfits_env
  rw [chainCloneEvents_decomp, srkEvents_of_pos hsrk_pos] at hfits_all
  have ⟨hfit_srk, hfit_after_srk⟩ :=
    (fitsEvents_append M lim (rustAllocEvents x.gc.1.srk.bytes.length 1)
      (privEvents x.gc ++ (ckEvents x.gc ++ chainCloneMkEvents x.gc.2.messageKeys)) st_init).mp hfits_all
  have hevs_all :
      ChainCloneEnv x.gc
        (rustAllocEvents x.gc.1.srk.bytes.length 1 ++
          (privEvents x.gc ++ (ckEvents x.gc ++ chainCloneMkEvents x.gc.2.messageKeys))) := by
    change _ = chainCloneEvents x.gc
    rw [chainCloneEvents_decomp, srkEvents_of_pos hsrk_pos]
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
  have hsrk_lay : RustLayoutOk x.gc.1.srk.bytes.length 1 :=
    ⟨⟨hsrk_pos, hpow1, by omega⟩, by decide⟩
  apply SepWPp.of_sepWP (mid := (blkPl_468).base + 68#64)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_call hshim ()
  refine SepWP.transport_budgetPool ‹LibsignalBinary.Heap.VmPreserved _ sf› (hnext := ?_)
  have htr_sf0 : sf.trace = s0.trace := ‹sf.trace = s0.trace›
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_call halloc_nooom (x.gc.1.srk.bytes.length, 1, st_init)
  have htrace1 : sf_1.trace = s0.trace :=
    (‹LibsignalBinary.Heap.AllocCallPreserved _ sf_1›).2.1.trans htr_sf0
  rw [‹sf.sp = s0.sp - 208#64›]
  wp_compact
  apply SepWP.done ‹_› ‹_›
  have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹sf_1.readReg64 Reg.x0 ≠ 0#64›
  let srkPtr' := sf_1.readReg64 (Reg.gpr 0#5)
  have hfold_srk_post (st_post : State) :
      ((srkPtr' ↦ₛ x.gc.1.srk.bytes) ∗
        (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
        A.pool lim (M.stepEvents (rustAllocEvents x.gc.1.srk.bytes.length 1) st_init) st_post ∗
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
        A.pool lim (M.stepEvents (rustAllocEvents x.gc.1.srk.bytes.length 1) st_init) st_post ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v25) ∗
        ((s0.sp - 136#64) ↦₆₄ v24) ∗
        ((s0.sp - 128#64) ↦₆₄ v23) ∗
        ((s0.sp - 104#64) ↦₆₄ v22) ∗
        savedRegsOnStack s0) := by
    rw [← A.repAlloc_live,
        vecU8Buf_pos_eq A.repAlloc srkPtr' x.gc.1.srk.bytes hsrk_pos hsrk_lt63 hoom64,
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
        ((srkPtr' ↦ₛ x.gc.1.srk.bytes) ∗
          (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
          A.pool lim (M.stepEvents (rustAllocEvents x.gc.1.srk.bytes.length 1) st_init) st_post ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          A.repAlloc.live srkPtr' x.gc.1.srk.bytes.length 1 ∗
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
          (A.repAlloc.live srkPtr' x.gc.1.srk.bytes.length 1 ∗ (srkPtr' ↦ₛ x.gc.1.srk.bytes)) ∗
          (((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
            ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
            (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
            chainSrkPosFrame A.repAlloc x.gc x.src) ∗
          A.pool lim (M.stepEvents (rustAllocEvents x.gc.1.srk.bytes.length 1) st_init) st_post ∗
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
  apply SepWPp.of_sepWP (mid := (blkPl_468).base + 88#64)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  wp_call hmemcpy (sf_1.readReg64 Reg.x0, x.gc.1.srk.ptr, x.gc.1.srk.bytes)
  refine SepWP.transport_budgetPool ‹LibsignalBinary.Heap.VmPreserved _ sf_2› (hnext := ?_)
  have htr_sf2 : sf_2.trace = s0.trace := (‹sf_2.trace = _›).trans htrace1
  wp_compact
  have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
  refine SepWP.done ‹_› ‹_› ?_
  have hswap_m3 (P0 P1 P2 R : SepProp) : P0 ∗ P1 ∗ P2 ∗ R = P1 ∗ P2 ∗ P0 ∗ R := by sep_ac_rfl
  rw [hswap_m3]
  refine SepWPp.weaken_pre (hfold_srk_post _) ?_
  by_cases hpriv_nil : x.gc.1.priv.bytes = []
  · have hevs_p0 :
        ChainCloneEnv x.gc
          (rustAllocEvents x.gc.1.srk.bytes.length 1 ++
            (ckEvents x.gc ++ chainCloneMkEvents x.gc.2.messageKeys)) := by
      simpa [privEvents_of_nil hpriv_nil] using hevs_all
    have hfits_p0 :
        FitsEvents M lim (M.stepEvents (rustAllocEvents x.gc.1.srk.bytes.length 1) st_init)
          (ckEvents x.gc ++ chainCloneMkEvents x.gc.2.messageKeys) := by
      simpa [privEvents_of_nil hpriv_nil] using hfit_after_srk
    refine chain_clone_placed_priv_nil (M := M) (A := A) (lim := lim) (H := H) (Qp := Qp)
      hshim halloc hmemcpy x st_init (rustAllocEvents x.gc.1.srk.bytes.length 1)
      s0 _ hs0_align srkPtr' v25 v24 v23 v22
      hsrk hmax hsrc_klen hpriv_nil hevs_p0 hfits_p0
      ‹_› ‹_› hsp_sf2 ?_ ‹_› ‹_› ‹_› ‹_› ‹_› htr_sf2 ‹_›
    rw [State.spAligned, hsp_sf2]
    exact hsp_sub_align
  · have hpriv_pos : 0 < x.gc.1.priv.bytes.length := List.length_pos_of_ne_nil hpriv_nil
    have hevs_p1 :
        ChainCloneEnv x.gc
          ((rustAllocEvents x.gc.1.srk.bytes.length 1 ++
              rustAllocEvents x.gc.1.priv.bytes.length 1) ++
            (ckEvents x.gc ++ chainCloneMkEvents x.gc.2.messageKeys)) := by
      simpa [privEvents_of_pos hpriv_pos, List.append_assoc] using hevs_all
    have hfits_p1 :
        FitsEvents M lim (M.stepEvents (rustAllocEvents x.gc.1.srk.bytes.length 1) st_init)
          (rustAllocEvents x.gc.1.priv.bytes.length 1 ++
            (ckEvents x.gc ++ chainCloneMkEvents x.gc.2.messageKeys)) := by
      simpa [privEvents_of_pos hpriv_pos] using hfit_after_srk
    refine chain_clone_placed_priv_pos (M := M) (A := A) (lim := lim) (H := H) (Qp := Qp)
      hshim halloc hmemcpy x st_init (rustAllocEvents x.gc.1.srk.bytes.length 1)
      s0 _ hs0_align srkPtr' v25 v24 v23 v22
      hsrk hmax hsrc_klen hpriv_pos hevs_p1 hfits_p1
      ‹_› ‹_› hsp_sf2 ?_ ‹_› ‹_› ‹_› ‹_› ‹_› htr_sf2 ‹_›
    rw [State.spAligned, hsp_sf2]
    exact hsp_sub_align

/-! ## `chainAt` and `optSenderChainAt` Bridges -/

theorem chainAt_eq_protoChainAt (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    chainAt A gc a =
      (⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗ protoChainAt A gc a) := by
  simp only [chainAt, protoChainAt, ← sepConj_assoc, pure_sepConj_pure]
  have hp :
      (PublicKey.deserialize gc.1.srk.bytes = Except.ok gc.2.senderRatchetKey ∧
        gc.2.messageKeys.length ≤ maxMessageKeys ∧
        gc.1.keys.length = gc.2.messageKeys.length ∧
        gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []) =
      ((gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []) ∧
        PublicKey.deserialize gc.1.srk.bytes = Except.ok gc.2.senderRatchetKey ∧
        gc.2.messageKeys.length ≤ maxMessageKeys ∧
        gc.1.keys.length = gc.2.messageKeys.length) := by
    exact propext ⟨fun ⟨h1, h2, h3, h4, h5⟩ => ⟨⟨h4, h5⟩, h1, h2, h3⟩,
      fun ⟨⟨h4, h5⟩, h1, h2, h3⟩ => ⟨h1, h2, h3, h4, h5⟩⟩
  rw [hp]

theorem optSenderChainAt_some_eq_chainAt (A : RustAlloc) (a : BitVec 64)
    (g : SenderChainGhost) (sc : SenderChain) :
    optSenderChainAt A a (some g) (some sc) =
      (⌜g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
        clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
        g.srk.bytes.length = 33⌝ ∗
        protoChainAt A (⟨g.srk, g.priv, g.mkCap, g.mkPtr, [], g.ck⟩,
          ⟨sc.ratchetKey.publicKey, some sc.chainKey, []⟩) a) := by
  simp only [optSenderChainAt, protoChainAt, optChainKeyAt, List.length_nil, Nat.zero_le,
    true_and, and_true, ← sepConj_assoc, pure_sepConj_pure]
  have hp :
      (PublicKey.deserialize g.srk.bytes = Except.ok sc.ratchetKey.publicKey ∧
        g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
        clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
        g.srk.bytes.length = 33) =
      ((g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
        clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
        g.srk.bytes.length = 33) ∧
        PublicKey.deserialize g.srk.bytes = Except.ok sc.ratchetKey.publicKey) := by
    exact propext ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h2, h3, h4⟩, h1⟩,
      fun ⟨⟨h2, h3, h4⟩, h1⟩ => ⟨h1, h2, h3, h4⟩⟩
  rw [hp]; rfl

theorem chainClone_of_protoChainClone_gen {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hclone : subroutine_ok prog entry (protoChainCloneSpec M A lim)) :
    subroutine_ok prog entry (chainCloneSpec M A lim) := by
  apply subroutine_ok_outcome_intro
  intro ⟨x, st⟩ R s0 hpc hrun hpre hsp
  simp only [chainCloneSpec, chainAt_eq_protoChainAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfits⟩, hmem⟩
  set P_rc : Prop := x.gc.1.srk.bytes.length = 33 ∧ x.gc.1.priv.bytes = []
  change s0.mem ⊨ memRegion x.dst 104 ∗ ⌜P_rc⌝ ∗ protoChainAt A.repAlloc x.gc x.src ∗
    A.pool lim st s0 ∗ stackAt s0.sp chainCloneStack ∗ R at hmem
  have hmem_rearr :
      s0.mem ⊨
        memRegion x.dst 104 ∗ protoChainAt A.repAlloc x.gc x.src ∗
        A.pool lim st s0 ∗ stackAt s0.sp chainCloneStack ∗ (⌜P_rc⌝ ∗ R) := by
    have heq :
        (memRegion x.dst 104 ∗ ⌜P_rc⌝ ∗ protoChainAt A.repAlloc x.gc x.src ∗
          A.pool lim st s0 ∗ stackAt s0.sp chainCloneStack ∗ R) =
        (memRegion x.dst 104 ∗ protoChainAt A.repAlloc x.gc x.src ∗
          A.pool lim st s0 ∗ stackAt s0.sp chainCloneStack ∗ (⌜P_rc⌝ ∗ R)) := by
      sep_ac_rfl
    rwa [← heq]
  have hpre_clone :
      s0.mem ⊨ (protoChainCloneSpec M A lim).pre (x, st) s0 ∗ (⌜P_rc⌝ ∗ R) := by
    simp only [protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hfits⟩, hmem_rearr⟩
  refine (hclone.to_outcome (x, st) (⌜P_rc⌝ ∗ R) s0 hpc hrun hpre_clone hsp).mono_outcome
    (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [protoChainCloneSpec] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨htrace, hevs⟩, hmem_f⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hmem_f
    rcases hmem_f with ⟨g', hmem_f⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hmem_f
    rcases hmem_f with ⟨⟨hsrk', hpriv', hkeys'⟩, hmem_f⟩
    have hpure_front :
        sf.mem ⊨
          ⌜P_rc⌝ ∗
          (protoChainAt A.repAlloc (g', x.gc.2) x.dst ∗
            protoChainAt A.repAlloc x.gc x.src ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack ∗ R) := by
      have heq :
          (protoChainAt A.repAlloc (g', x.gc.2) x.dst ∗
            protoChainAt A.repAlloc x.gc x.src ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack ∗ ⌜P_rc⌝ ∗ R) =
          (⌜P_rc⌝ ∗
            (protoChainAt A.repAlloc (g', x.gc.2) x.dst ∗
              protoChainAt A.repAlloc x.gc x.src ∗
              A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack ∗ R)) := by
        sep_ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hpure_front
    rcases hpure_front with ⟨⟨hsrk33, hpriv_nil⟩, hrest_f⟩
    dsimp only [chainCloneSpec]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htrace, hevs⟩, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨g', ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hsrk', hpriv', hkeys'⟩, ?_⟩
    rw [chainAt_eq_protoChainAt A.repAlloc (g', x.gc.2) x.dst,
        chainAt_eq_protoChainAt A.repAlloc x.gc x.src]
    have hsrk33' : g'.srk.bytes.length = 33 := by rw [hsrk', hsrk33]
    have hpriv_nil' : g'.priv.bytes = [] := hpriv'.trans hpriv_nil
    set P_rc' : Prop := g'.srk.bytes.length = 33 ∧ g'.priv.bytes = []
    change sf.mem ⊨
      (⌜P_rc'⌝ ∗ protoChainAt A.repAlloc (g', x.gc.2) x.dst) ∗
      (⌜P_rc⌝ ∗ protoChainAt A.repAlloc x.gc x.src) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack ∗ R
    have heq2 :
        ((⌜P_rc'⌝ ∗ protoChainAt A.repAlloc (g', x.gc.2) x.dst) ∗
          (⌜P_rc⌝ ∗ protoChainAt A.repAlloc x.gc x.src) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack ∗ R) =
        (⌜P_rc'⌝ ∗ (⌜P_rc⌝ ∗
          (protoChainAt A.repAlloc (g', x.gc.2) x.dst ∗
            protoChainAt A.repAlloc x.gc x.src ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack ∗ R))) := by
      sep_ac_rfl
    rw [heq2, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨⟨hsrk33', hpriv_nil'⟩, ⟨hsrk33, hpriv_nil⟩, hrest_f⟩
  · simp only [protoChainCloneSpec, sepConj_assoc] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · simp only [protoChainCloneSpec, sepConj_assoc] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · simp only [protoChainCloneSpec, sepConj_assoc] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

theorem senderChainClone_of_chainClone_gen {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hclone : subroutine_ok prog entry (protoChainCloneSpec M A lim)) :
    subroutine_ok prog entry (senderChainCloneSpec M A lim) := by
  apply subroutine_ok_outcome_intro
  intro ⟨x, st⟩ R s0 hpc hrun hpre hsp
  simp only [senderChainCloneSpec, optSenderChainAt_some_eq_chainAt, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfits⟩, hmem⟩
  let P_sc : Prop :=
    x.g.priv.bytes = x.sc.ratchetKey.privateKey.bytes.toList ∧
      clampScalar x.sc.ratchetKey.privateKey.bytes = x.sc.ratchetKey.privateKey.bytes ∧
      x.g.srk.bytes.length = 33
  let gc0 : ChainGhost × ReceiverChain :=
    (⟨x.g.srk, x.g.priv, x.g.mkCap, x.g.mkPtr, [], x.g.ck⟩,
      ⟨x.sc.ratchetKey.publicKey, some x.sc.chainKey, []⟩)
  change s0.mem ⊨ memRegion x.dst 104 ∗ ⌜P_sc⌝ ∗ protoChainAt A.repAlloc gc0 x.src ∗
    A.pool lim st s0 ∗ stackAt s0.sp chainCloneStack ∗ R at hmem
  have hmem_rearr :
      s0.mem ⊨
        memRegion x.dst 104 ∗ protoChainAt A.repAlloc gc0 x.src ∗
        A.pool lim st s0 ∗ stackAt s0.sp chainCloneStack ∗ (⌜P_sc⌝ ∗ R) := by
    have heq :
        (memRegion x.dst 104 ∗ ⌜P_sc⌝ ∗ protoChainAt A.repAlloc gc0 x.src ∗
          A.pool lim st s0 ∗ stackAt s0.sp chainCloneStack ∗ R) =
        (memRegion x.dst 104 ∗ protoChainAt A.repAlloc gc0 x.src ∗
          A.pool lim st s0 ∗ stackAt s0.sp chainCloneStack ∗ (⌜P_sc⌝ ∗ R)) := by
      sep_ac_rfl
    rwa [← heq]
  have hpre_clone :
      s0.mem ⊨ (protoChainCloneSpec M A lim).pre (⟨x.dst, x.src, gc0⟩, st) s0 ∗ (⌜P_sc⌝ ∗ R) := by
    simp only [protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hfits⟩, hmem_rearr⟩
  refine (hclone.to_outcome (⟨x.dst, x.src, gc0⟩, st) (⌜P_sc⌝ ∗ R) s0 hpc hrun hpre_clone hsp).mono_outcome
    (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [protoChainCloneSpec] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨htrace, hevs⟩, hmem_f⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hmem_f
    rcases hmem_f with ⟨g', hmem_f⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hmem_f
    rcases hmem_f with ⟨⟨hsrk', hpriv', hkeys'⟩, hmem_f⟩
    have hkeys_nil : g'.keys = [] := List.eq_nil_of_length_eq_zero hkeys'
    have hpure_front :
        sf.mem ⊨
          ⌜P_sc⌝ ∗
          (protoChainAt A.repAlloc (g', gc0.2) x.dst ∗
            protoChainAt A.repAlloc gc0 x.src ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack ∗ R) := by
      have heq :
          (protoChainAt A.repAlloc (g', gc0.2) x.dst ∗
            protoChainAt A.repAlloc gc0 x.src ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack ∗ ⌜P_sc⌝ ∗ R) =
          (⌜P_sc⌝ ∗
            (protoChainAt A.repAlloc (g', gc0.2) x.dst ∗
              protoChainAt A.repAlloc gc0 x.src ∗
              A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack ∗ R)) := by
        sep_ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hpure_front
    rcases hpure_front with ⟨⟨hpriv_eq, hclamp, hsrk33⟩, hrest_f⟩
    let sg' : SenderChainGhost := ⟨g'.srk, g'.priv, g'.mkCap, g'.mkPtr, g'.ck⟩
    have hg'_eq : g' = ⟨sg'.srk, sg'.priv, sg'.mkCap, sg'.mkPtr, [], sg'.ck⟩ := by
      cases g'; dsimp [sg'] at hkeys_nil ⊢; subst hkeys_nil; rfl
    rw [hg'_eq] at hrest_f
    dsimp only [senderChainCloneSpec]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htrace, hevs⟩, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨sg', ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hsrk', hpriv'⟩, ?_⟩
    rw [optSenderChainAt_some_eq_chainAt A.repAlloc x.dst sg' x.sc,
        optSenderChainAt_some_eq_chainAt A.repAlloc x.src x.g x.sc]
    have hpriv'_eq : sg'.priv.bytes = x.sc.ratchetKey.privateKey.bytes.toList :=
      hpriv'.trans hpriv_eq
    have hsrk33' : sg'.srk.bytes.length = 33 := by
      change g'.srk.bytes.length = 33
      rw [hsrk', hsrk33]
    let P_sc' : Prop :=
      sg'.priv.bytes = x.sc.ratchetKey.privateKey.bytes.toList ∧
        clampScalar x.sc.ratchetKey.privateKey.bytes = x.sc.ratchetKey.privateKey.bytes ∧
        sg'.srk.bytes.length = 33
    let gc' : ChainGhost × ReceiverChain :=
      (⟨sg'.srk, sg'.priv, sg'.mkCap, sg'.mkPtr, [], sg'.ck⟩, gc0.2)
    change sf.mem ⊨
      (⌜P_sc'⌝ ∗ protoChainAt A.repAlloc gc' x.dst) ∗
      (⌜P_sc⌝ ∗ protoChainAt A.repAlloc gc0 x.src) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack ∗ R
    have heq2 :
        ((⌜P_sc'⌝ ∗ protoChainAt A.repAlloc gc' x.dst) ∗
          (⌜P_sc⌝ ∗ protoChainAt A.repAlloc gc0 x.src) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack ∗ R) =
        (⌜P_sc'⌝ ∗ (⌜P_sc⌝ ∗
          (protoChainAt A.repAlloc gc' x.dst ∗
            protoChainAt A.repAlloc gc0 x.src ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack ∗ R))) := by
      sep_ac_rfl
    rw [heq2, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨⟨hpriv'_eq, hclamp, hsrk33'⟩, ⟨hpriv_eq, hclamp, hsrk33⟩, hrest_f⟩
  · simp only [protoChainCloneSpec, sepConj_assoc] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · simp only [protoChainCloneSpec, sepConj_assoc] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · simp only [protoChainCloneSpec, sepConj_assoc] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

theorem protoChain_clone_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_468).rebase (blkPl_468).base H)
      (lsρ lsRustNoAllocShimSym)
      (withVmPreserved CryptoVerification.LibsignalTripleRatchet.sessionShimSpec))
    (halloc : subroutine_ok ((blkPC_468).rebase (blkPl_468).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_468).rebase (blkPl_468).base H)
      (lsρ lsMemcpySym) (withVmPreserved sessionMemcpyRegionSpec)) :
    subroutine_ok ((blkPC_468).rebase (blkPl_468).base H) (blkPl_468).base
      (protoChainCloneSpec M A lim) := by
  have hshim' := subroutine_ok_sessionShimSpec_of_withVmPreserved hshim
  have hmemcpy' := subroutine_ok_sessionMemcpySpec_of_withVmPreserved hmemcpy
  apply subroutine_ok_of_sepWPp
  intro ⟨x, st_init⟩ R s0 hpc hrun hpre hs0_align
  simp only [protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfits_env⟩, hmem⟩
  refine ⟨memRegion x.dst 104 ∗ protoChainAt A.repAlloc x.gc x.src ∗
      A.pool lim st_init s0 ∗ stackAt s0.sp chainCloneStack,
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, fun R' hm' hloaded => ?_⟩
  rcases chain_clone_placed_entry hshim' halloc hmemcpy' x st_init s0 hs0_align hfits_env
      hpc hrun hx0 hx1 R' hm' hloaded with
    ⟨sf, hsteps, ⟨hret, hrun_f, P_f, hmem_f, hsp_f, hcc_f, hpost_f⟩ | hpan | hoom⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hret, hrun_f, P_f, hmem_f,
      ⟨fun hm_R => Satisfies.mono (sepConj_mono_left hpost_f) hm_R, hsp_f, hcc_f⟩⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem protoChain_clone_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym
      (withVmPreserved CryptoVerification.LibsignalTripleRatchet.sessionShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym (withVmPreserved sessionMemcpyRegionSpec)) :
    subroutine_ok ((blkPC_468).rebase (blkPl_468).base H) (blkPl_468).base
      (protoChainCloneSpec M A lim) :=
  protoChain_clone_placed_ok_of_hooks
    (ls_hook_ok_of_mem hshim)
    (ls_hook_ok_of_mem halloc)
    (ls_hook_ok_of_mem hmemcpy)

theorem chain_clone_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_468).rebase (blkPl_468).base H)
      (lsρ lsRustNoAllocShimSym)
      (withVmPreserved CryptoVerification.LibsignalTripleRatchet.sessionShimSpec))
    (halloc : subroutine_ok ((blkPC_468).rebase (blkPl_468).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_468).rebase (blkPl_468).base H)
      (lsρ lsMemcpySym) (withVmPreserved sessionMemcpyRegionSpec)) :
    subroutine_ok ((blkPC_468).rebase (blkPl_468).base H) (blkPl_468).base
      (chainCloneSpec M A lim) :=
  chainClone_of_protoChainClone_gen (protoChain_clone_placed_ok_of_hooks hshim halloc hmemcpy)

theorem chain_clone_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym
      (withVmPreserved CryptoVerification.LibsignalTripleRatchet.sessionShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym (withVmPreserved sessionMemcpyRegionSpec)) :
    subroutine_ok ((blkPC_468).rebase (blkPl_468).base H) (blkPl_468).base
      (chainCloneSpec M A lim) :=
  chainClone_of_protoChainClone_gen (protoChain_clone_placed_ok hshim halloc hmemcpy)

theorem senderChain_clone_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_468).rebase (blkPl_468).base H)
      (lsρ lsRustNoAllocShimSym)
      (withVmPreserved CryptoVerification.LibsignalTripleRatchet.sessionShimSpec))
    (halloc : subroutine_ok ((blkPC_468).rebase (blkPl_468).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_468).rebase (blkPl_468).base H)
      (lsρ lsMemcpySym) (withVmPreserved sessionMemcpyRegionSpec)) :
    subroutine_ok ((blkPC_468).rebase (blkPl_468).base H) (blkPl_468).base
      (senderChainCloneSpec M A lim) :=
  senderChainClone_of_chainClone_gen (protoChain_clone_placed_ok_of_hooks hshim halloc hmemcpy)

theorem senderChain_clone_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym
      (withVmPreserved CryptoVerification.LibsignalTripleRatchet.sessionShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym (withVmPreserved sessionMemcpyRegionSpec)) :
    subroutine_ok ((blkPC_468).rebase (blkPl_468).base H) (blkPl_468).base
      (senderChainCloneSpec M A lim) :=
  senderChainClone_of_chainClone_gen (protoChain_clone_placed_ok hshim halloc hmemcpy)

end LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.ClonePlacedBudget
