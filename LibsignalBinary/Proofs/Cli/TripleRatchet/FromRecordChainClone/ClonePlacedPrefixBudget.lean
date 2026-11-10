/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.ClonePlacedMidBudget
public meta import Lean
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Heap.SpecBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import ProofLib.ProgramReflection
import ProofLib.RegChain
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable Prefix Segments for CLI `Chain::clone [local#2]`

Threads `RustCliAllocBudget M` and `VmPreserved` across the `chain_key`, `priv`, and `srk` entry
segments of CLI `Chain::clone [local#2]` (Block `468`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.ClonePlacedPrefixBudget

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

/-! ## Prefix Event-List Helpers -/

def srkEvents (gc : ChainGhost × ReceiverChain) : List AllocEvent :=
  if gc.1.srk.bytes.length = 0 then [] else rustAllocEvents gc.1.srk.bytes.length 1

def privEvents (gc : ChainGhost × ReceiverChain) : List AllocEvent :=
  if gc.1.priv.bytes.length = 0 then [] else rustAllocEvents gc.1.priv.bytes.length 1

def ckEvents (gc : ChainGhost × ReceiverChain) : List AllocEvent :=
  match gc.2.chainKey with
  | none => []
  | some _ => rustAllocEvents 32 1

theorem chainCloneEvents_decomp (gc : ChainGhost × ReceiverChain) :
    chainCloneEvents gc =
      srkEvents gc ++ (privEvents gc ++ (ckEvents gc ++ chainCloneMkEvents gc.2.messageKeys)) := by
  simp only [chainCloneEvents, srkEvents, privEvents, ckEvents, chainCloneMkEvents,
    List.append_assoc]
  rfl

theorem srkEvents_of_pos {gc : ChainGhost × ReceiverChain} (h : 0 < gc.1.srk.bytes.length) :
    srkEvents gc = rustAllocEvents gc.1.srk.bytes.length 1 := by
  simp [srkEvents, Nat.ne_of_gt h]

theorem privEvents_of_nil {gc : ChainGhost × ReceiverChain} (h : gc.1.priv.bytes = []) :
    privEvents gc = [] := by
  simp [privEvents, h]

theorem privEvents_of_pos {gc : ChainGhost × ReceiverChain} (h : 0 < gc.1.priv.bytes.length) :
    privEvents gc = rustAllocEvents gc.1.priv.bytes.length 1 := by
  simp [privEvents, Nat.ne_of_gt h]

theorem ckEvents_of_none {gc : ChainGhost × ReceiverChain} (h : gc.2.chainKey = none) :
    ckEvents gc = [] := by
  simp [ckEvents, h]

theorem ckEvents_of_some {gc : ChainGhost × ReceiverChain} {ck : ChainKey}
    (h : gc.2.chainKey = some ck) :
    ckEvents gc = rustAllocEvents 32 1 := by
  simp [ckEvents, h]

/-! ## `chain_key`, `priv`, and Entry Segments -/

set_option maxHeartbeats 1200000 in
theorem chain_clone_placed_ck_some [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (hshim : subroutine_ok ((blkPC_468).rebase (blkPl_468).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_468).rebase (blkPl_468).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_468).rebase (blkPl_468).base H)
      (lsρ lsMemcpySym) sessionMemcpySpec)
    (x : ChainCloneGhost) (ck : ChainKey) (st_init : M.σ) (evs_pre_ck : List AllocEvent)
    (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' privPtr' v8 v9 v10 v13 : BitVec 64)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hck : x.gc.2.chainKey = some ck)
    (hevs_full : ChainCloneEnv x.gc
      ((evs_pre_ck ++ rustAllocEvents 32 1) ++ chainCloneMkEvents x.gc.2.messageKeys))
    (hfits : FitsEvents M lim (M.stepEvents evs_pre_ck st_init)
      (rustAllocEvents 32 1 ++ chainCloneMkEvents x.gc.2.messageKeys))
    (hpc : s.pc = (blkPl_468).base + 148#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (_hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp ((blkPC_468).rebase (blkPl_468).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        protoChainAt A.repAlloc x.gc x.src ∗
        A.pool lim (M.stepEvents evs_pre_ck st_init) s ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec M A lim).post (x, st_init) s0 sf))
      Qp := by
  have halloc_nooom := subroutine_ok_allocNoOom_of_budget halloc
  have ⟨hfit_ck, hfit_mk0⟩ :=
    (fitsEvents_append M lim (rustAllocEvents 32 1)
      (chainCloneMkEvents x.gc.2.messageKeys) (M.stepEvents evs_pre_ck st_init)).mp hfits
  have hfe_ck_raw : FitsEvents M lim (M.stepEvents evs_pre_ck st_init) [.alloc 32] := by
    simpa [rustAllocEvents] using hfit_ck
  rcases hfe_ck_raw with ⟨⟨_hwma_ck, _henf_ck, _hram_ck, _hva_ck⟩, -⟩
  have hfit_mk :
      FitsEvents M lim (M.stepEvents (evs_pre_ck ++ rustAllocEvents 32 1) st_init)
        (chainCloneMkEvents x.gc.2.messageKeys) := by
    rwa [M.stepEvents_append]
  have hmks_nil := fun s' ckPtr' (hnil : x.gc.2.messageKeys = []) =>
    chain_clone_placed_mks_nil (M := M) (A := A) (lim := lim) (H := H) (Qp := Qp)
      x st_init (evs_pre_ck ++ rustAllocEvents 32 1) s0 s'
      srkPtr' privPtr' 32#64 ckPtr'
      v9 v10 v13 ck.index ⟨32#64, ckPtr'⟩
      hsrk hmax hsrc_klen hnil
      (by simpa [chainCloneMkEvents, hnil] using hevs_full)
  have hmks_ne := fun s' ckPtr' (hpos : 0 < x.gc.2.messageKeys.length) =>
    chain_clone_placed_mks_nonempty (M := M) (A := A) (lim := lim) (H := H) (Qp := Qp)
      hshim halloc hmemcpy x st_init (evs_pre_ck ++ rustAllocEvents 32 1) s0 s' hs0_align
      srkPtr' privPtr' 32#64 ckPtr'
      v9 v10 v13 ck.index ⟨32#64, ckPtr'⟩
      hsrk hmax hsrc_klen hpos hevs_full hfit_mk
  dsimp only [sessionShimSpec] at hshim
  dsimp only [sessionMemcpySpec] at hmemcpy
  rw [chainAt_eq_ck_some A.repAlloc x.gc ck x.src hsrk hmax hsrc_klen hck]
  simp only [sepConj_assoc]
  rw [show (memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        ⌜32 ≤ x.gc.1.ck.cap.toNat ∧ x.gc.1.ck.cap.toNat < 2 ^ 63 ∧ x.gc.1.ck.ptr ≠ 0⌝ ∗
        ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
        ((x.src + 88#64) ↦₆₄ 32#64) ∗
        ((x.src + 96#64) ↦₃₂ ck.index) ∗
        (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
        chainCkSomeFrame A.repAlloc x.gc x.src ∗
        A.pool lim (M.stepEvents evs_pre_ck st_init) s ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) =
      (⌜32 ≤ x.gc.1.ck.cap.toNat ∧ x.gc.1.ck.cap.toNat < 2 ^ 63 ∧ x.gc.1.ck.ptr ≠ 0⌝ ∗
        memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
        ((x.src + 88#64) ↦₆₄ 32#64) ∗
        ((x.src + 96#64) ↦₃₂ ck.index) ∗
        (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
        chainCkSomeFrame A.repAlloc x.gc x.src ∗
        A.pool lim (M.stepEvents evs_pre_ck st_init) s ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) by sep_ac_rfl]
  refine SepWPp.pure_elim fun ⟨hck_le, hck_lt, hck_ptr⟩ => ?_
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hck_lay : RustLayoutOk 32 1 := ⟨⟨by decide, hpow1, by decide⟩, by decide⟩
  have hck_len : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  have htrunc32_ck : BitVec.truncate 32 (BitVec.zeroExtend 64 ck.index) = ck.index :=
    (BitVec.setWidth_setWidth_of_le ck.index (by decide)).trans (BitVec.setWidth_eq ck.index)
  apply SepWPp.of_sepWP (mid := (blkPl_468).base + 180#64)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_call hshim ()
  refine SepWP.transport_budgetPool ‹LibsignalBinary.Heap.VmPreserved _ sf› (hnext := ?_)
  have htr_sf0 : sf.trace = s0.trace := (‹sf.trace = s.trace›).trans htrace
  wp_compact
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_call halloc_nooom (32, 1, M.stepEvents evs_pre_ck st_init)
  have htrace1 : sf_1.trace = s0.trace :=
    (‹LibsignalBinary.Heap.AllocCallPreserved _ sf_1›).2.1.trans htr_sf0
  rw [‹sf.sp = s0.sp - 208#64›]
  wp_compact
  apply SepWP.done ‹_› ‹_›
  have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹sf_1.readReg64 Reg.x0 ≠ 0#64›
  let ckPtr' := sf_1.readReg64 (Reg.gpr 0#5)
  have hfold_ck_post (st_post : State) :
      ((ckPtr' ↦ₛ keyToBytes32 ck.key) ∗
        (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
        A.pool lim (M.stepEvents (rustAllocEvents 32 1) (M.stepEvents evs_pre_ck st_init)) st_post ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        A.live ckPtr' 32 1 ∗
        memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
        ((x.src + 88#64) ↦₆₄ 32#64) ∗
        ((x.src + 96#64) ↦₃₂ ck.index) ∗
        chainCkSomeFrame A.repAlloc x.gc x.src ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) ⊢
      (memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A.repAlloc ⟨32#64, ckPtr'⟩ 32#64 ckPtr' ck.index x.gc.2.chainKey ∗
        protoChainAt A.repAlloc x.gc x.src ∗
        A.pool lim (M.stepEvents (evs_pre_ck ++ rustAllocEvents 32 1) st_init) st_post ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) := by
    rw [← M.stepEvents_append, ← A.repAlloc_live]
    have hck_buf_eq :
        clonedOptChainKeyBuf A.repAlloc ⟨32#64, ckPtr'⟩ 32#64 ckPtr' ck.index x.gc.2.chainKey =
          A.repAlloc.live ckPtr' 32 1 ∗ (ckPtr' ↦ₛ keyToBytes32 ck.key) := by
      rw [hck]
      simp only [clonedOptChainKeyBuf, and_self, pure_true, emp_sepConj]
      have hpos32 : 0 < (keyToBytes32 ck.key).length := by rw [hck_len]; decide
      have hlt32 : (keyToBytes32 ck.key).length < 2 ^ 63 := by rw [hck_len]; decide
      have hv := vecU8Buf_pos_eq A.repAlloc ckPtr' (keyToBytes32 ck.key) hpos32 hlt32 hoom64
      rw [hck_len] at hv
      exact hv
    rw [hck_buf_eq,
        chainAt_eq_ck_some A.repAlloc x.gc ck x.src hsrk hmax hsrc_klen hck]
    have hsrc_ent :
        (((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
          ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
          ((x.src + 88#64) ↦₆₄ 32#64) ∗
          ((x.src + 96#64) ↦₃₂ ck.index) ∗
          (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          chainCkSomeFrame A.repAlloc x.gc x.src) ⊢
        (⌜32 ≤ x.gc.1.ck.cap.toNat ∧ x.gc.1.ck.cap.toNat < 2 ^ 63 ∧ x.gc.1.ck.ptr ≠ 0⌝ ∗
          ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
          ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
          ((x.src + 88#64) ↦₆₄ 32#64) ∗
          ((x.src + 96#64) ↦₃₂ ck.index) ∗
          (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          chainCkSomeFrame A.repAlloc x.gc x.src) :=
      Entails.pure_right ⟨hck_le, hck_lt, hck_ptr⟩ (Entails.refl _)
    have hgroup :
        ((ckPtr' ↦ₛ keyToBytes32 ck.key) ∗
          (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          A.pool lim (M.stepEvents (evs_pre_ck ++ rustAllocEvents 32 1) st_init) st_post ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          A.repAlloc.live ckPtr' 32 1 ∗
          memRegion x.dst 104 ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
          ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
          ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
          ((x.src + 88#64) ↦₆₄ 32#64) ∗
          ((x.src + 96#64) ↦₃₂ ck.index) ∗
          chainCkSomeFrame A.repAlloc x.gc x.src ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) =
        (memRegion x.dst 104 ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
          (A.repAlloc.live ckPtr' 32 1 ∗ (ckPtr' ↦ₛ keyToBytes32 ck.key)) ∗
          (((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
            ((x.src + 88#64) ↦₆₄ 32#64) ∗
            ((x.src + 96#64) ↦₃₂ ck.index) ∗
            (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
            chainCkSomeFrame A.repAlloc x.gc x.src) ∗
          A.pool lim (M.stepEvents (evs_pre_ck ++ rustAllocEvents 32 1) st_init) st_post ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) := by
      sep_ac_rfl
    rw [hgroup]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hsrc_ent))))
  by_cases hmk_nil : x.gc.2.messageKeys = []
  · have hlen0 : BitVec.ofNat 64 x.gc.2.messageKeys.length = 0#64 := by simp [hmk_nil]
    apply SepWPp.of_sepWP (mid := (blkPl_468).base + 732#64)
    wp_steps_sync_pool (lsρ lsMemcpySym)
    wp_call hmemcpy (ckPtr', x.gc.1.ck.ptr, keyToBytes32 ck.key)
    refine SepWP.transport_budgetPool ‹LibsignalBinary.Heap.VmPreserved _ sf_2› (hnext := ?_)
    have htr_sf2 : sf_2.trace = s0.trace := (‹sf_2.trace = _›).trans htrace1
    wp_compact
    have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
    have hx27_sf2 : sf_2.readReg64 (Reg.gpr 27#5) = BitVec.zeroExtend 64 ck.index := ‹_›
    wp_steps_sync_pool ((blkPl_468).base + 732#64)
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm]; assumption
    · refine SepWPp.weaken_pre
        (Entails.trans (by rw [hlen0]; dsimp only [ckPtr']; exact Entails.of_eq (by sep_ac_rfl))
          (hfold_ck_post _))
        (hmks_nil _ ckPtr' hmk_nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · simp only [wp_norm, arm64_norm]
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · rw [State.spAligned] at hs0_align ⊢; simp only [wp_norm, arm64_norm, hsp_sf2]
        exact hs0_align
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · unfold State.readReg32; simp only [wp_norm, arm64_norm]; rw [hx27_sf2, htrunc32_ck]
      · simp only [wp_norm, arm64_norm]; exact htr_sf2
      · simp only [wp_norm, arm64_norm]; assumption
  · have hpos : 0 < x.gc.2.messageKeys.length := List.length_pos_of_ne_nil hmk_nil
    have hbeq0 : (BitVec.ofNat 64 x.gc.2.messageKeys.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hpos (by unfold maxMessageKeys at hmax; omega)
    apply SepWPp.of_sepWP (mid := (blkPl_468).base + 260#64)
    wp_steps_sync_pool (lsρ lsMemcpySym)
    wp_call hmemcpy (ckPtr', x.gc.1.ck.ptr, keyToBytes32 ck.key)
    refine SepWP.transport_budgetPool ‹LibsignalBinary.Heap.VmPreserved _ sf_2› (hnext := ?_)
    have htr_sf2 : sf_2.trace = s0.trace := (‹sf_2.trace = _›).trans htrace1
    wp_compact
    have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
    have hx27_sf2 : sf_2.readReg64 (Reg.gpr 27#5) = BitVec.zeroExtend 64 ck.index := ‹_›
    wp_steps_sync_pool ((blkPl_468).base + 260#64)
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm, arm64_norm, hbeq0, Bool.not_false, ↓reduceIte]
    · simp only [wp_norm, arm64_norm]; assumption
    · refine SepWPp.weaken_pre
        (Entails.trans (by dsimp only [ckPtr']; exact Entails.of_eq (by sep_ac_rfl))
          (hfold_ck_post _))
        (hmks_ne _ ckPtr' hpos ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · simp only [wp_norm, arm64_norm, hbeq0, Bool.not_false, ↓reduceIte]
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · rw [State.spAligned] at hs0_align ⊢; simp only [wp_norm, arm64_norm, hsp_sf2]
        exact hs0_align
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · unfold State.readReg32; simp only [wp_norm, arm64_norm]; rw [hx27_sf2, htrunc32_ck]
      · simp only [wp_norm, arm64_norm]; exact htr_sf2
      · simp only [wp_norm, arm64_norm]; assumption

set_option maxHeartbeats 1200000 in
theorem chain_clone_placed_priv_nil [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (hshim : subroutine_ok ((blkPC_468).rebase (blkPl_468).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_468).rebase (blkPl_468).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_468).rebase (blkPl_468).base H)
      (lsρ lsMemcpySym) sessionMemcpySpec)
    (x : ChainCloneGhost) (st_init : M.σ) (evs_pre_priv : List AllocEvent)
    (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' v8 v9 v10 v13 : BitVec 64)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpriv : x.gc.1.priv.bytes = [])
    (hevs_full : ChainCloneEnv x.gc
      (evs_pre_priv ++ (ckEvents x.gc ++ chainCloneMkEvents x.gc.2.messageKeys)))
    (hfits : FitsEvents M lim (M.stepEvents evs_pre_priv st_init)
      (ckEvents x.gc ++ chainCloneMkEvents x.gc.2.messageKeys))
    (hpc : s.pc = (blkPl_468).base + 88#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp ((blkPC_468).rebase (blkPl_468).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        protoChainAt A.repAlloc x.gc x.src ∗
        A.pool lim (M.stepEvents evs_pre_priv st_init) s ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec M A lim).post (x, st_init) s0 sf))
      Qp := by
  have hpriv_buf :
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) 1#64 x.gc.1.priv.bytes = emp := by
    simpa [hpriv] using vecU8Buf_nil_eq A.repAlloc
  have hpriv_len0 : BitVec.ofNat 64 x.gc.1.priv.bytes.length = 0#64 := by
    simp [hpriv]
  rw [chainAt_eq_priv_len A.repAlloc x.gc x.src hsrk hmax hsrc_klen, hpriv_len0]
  simp only [sepConj_assoc]
  apply SepWPp.of_sepWP (mid := (blkPl_468).base + 232#64)
  wp_steps_sync_pool ((blkPl_468).base + 232#64)
  refine SepWP.done ?_ ?_ ?_
  · simp only [wp_norm, arm64_norm]
  · simp only [wp_norm, arm64_norm]; assumption
  · have hfold_priv (st_mid : State) :
        (memRegion x.dst 104 ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          ((x.src + 40#64) ↦₆₄ 0#64) ∗
          chainPrivLenFrame A.repAlloc x.gc x.src ∗
          A.pool lim (M.stepEvents evs_pre_priv st_init) st_mid ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) =
        (memRegion x.dst 104 ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          protoChainAt A.repAlloc x.gc x.src ∗
          A.pool lim (M.stepEvents evs_pre_priv st_init) st_mid ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) := by
      rw [chainAt_eq_priv_len A.repAlloc x.gc x.src hsrk hmax hsrc_klen, hpriv_len0]
      sep_ac_rfl
    have hswap_pool (P1 P2 P3 P4 P5 R : SepProp) :
        P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ R = P2 ∗ P3 ∗ P4 ∗ P5 ∗ P1 ∗ R := by
      sep_ac_rfl
    rw [hswap_pool, hfold_priv]
    cases hck : x.gc.2.chainKey with
    | none =>
      have hevs_none : ChainCloneEnv x.gc (evs_pre_priv ++ chainCloneMkEvents x.gc.2.messageKeys) := by
        simpa [ckEvents_of_none hck] using hevs_full
      have hfits_none : FitsEvents M lim (M.stepEvents evs_pre_priv st_init)
          (chainCloneMkEvents x.gc.2.messageKeys) := by
        simpa [ckEvents_of_none hck] using hfits
      rw [chainAt_eq_ck_none_cap A.repAlloc x.gc x.src hsrk hmax hsrc_klen hck]
      simp only [sepConj_assoc]
      apply SepWPp.of_sepWP (mid := (blkPl_468).base + 244#64)
      wp_steps_sync_pool ((blkPl_468).base + 244#64)
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm, arm64_norm]
      · simp only [wp_norm, arm64_norm]; assumption
      · refine SepWPp.weaken_pre ?_
          (chain_clone_placed_ck_none (M := M) (A := A) (lim := lim) (H := H) (Qp := Qp)
            hshim halloc hmemcpy x st_init evs_pre_priv s0 _ hs0_align
            srkPtr' 1#64 v8 v9 v10 v13 hsrk hmax hsrc_klen hck hevs_none hfits_none
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · rw [hpriv_buf, emp_sepConj,
              chainAt_eq_ck_none_cap A.repAlloc x.gc x.src hsrk hmax hsrc_klen hck]
          exact Entails.of_eq (by sep_ac_rfl)
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm]; assumption
        · simp only [wp_norm, arm64_norm]; assumption
        · rw [State.spAligned] at hsp_align ⊢; simp only [wp_norm, arm64_norm]; exact hsp_align
        · simp only [wp_norm, arm64_norm]; assumption
        · simp only [wp_norm, arm64_norm]; assumption
        · simp only [wp_norm, arm64_norm]; assumption
        · simp only [wp_norm, arm64_norm]; assumption
        · simp only [wp_norm, arm64_norm, hpriv_len0]
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm]; assumption
        · simp only [wp_norm, arm64_norm]; exact htrace
        · simp only [wp_norm, arm64_norm]; assumption
    | some ck =>
      have hevs_some : ChainCloneEnv x.gc
          ((evs_pre_priv ++ rustAllocEvents 32 1) ++ chainCloneMkEvents x.gc.2.messageKeys) := by
        simpa [ckEvents_of_some hck, List.append_assoc] using hevs_full
      have hfits_some : FitsEvents M lim (M.stepEvents evs_pre_priv st_init)
          (rustAllocEvents 32 1 ++ chainCloneMkEvents x.gc.2.messageKeys) := by
        simpa [ckEvents_of_some hck] using hfits
      rw [chainAt_eq_ck_some_cap A.repAlloc x.gc ck x.src hsrk hmax hsrc_klen hck]
      simp only [sepConj_assoc]
      rw [show (memRegion x.dst 104 ∗
            vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            ⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
            ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
            chainCkSomeCapFrame A.repAlloc x.gc ck x.src ∗
            A.pool lim (M.stepEvents evs_pre_priv st_init) _ ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) =
          (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
            memRegion x.dst 104 ∗
            vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
            chainCkSomeCapFrame A.repAlloc x.gc ck x.src ∗
            A.pool lim (M.stepEvents evs_pre_priv st_init) _ ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) by sep_ac_rfl]
      refine SepWPp.pure_elim fun hck_lt => ?_
      have hcap_ne := cap_add_one_beq_zero_false hck_lt
      apply SepWPp.of_sepWP (mid := (blkPl_468).base + 148#64)
      wp_steps_sync_pool
        (if (x.gc.1.ck.cap + 1#64 != 0#64) = true then (blkPl_468).base + 148#64
         else (blkPl_468).base + 244#64)
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm, arm64_norm, bne, hcap_ne, Bool.not_false, ↓reduceIte]
      · simp only [wp_norm, arm64_norm]; assumption
      · refine SepWPp.weaken_pre ?_
          (chain_clone_placed_ck_some (M := M) (A := A) (lim := lim) (H := H) (Qp := Qp)
            hshim halloc hmemcpy x ck st_init evs_pre_priv s0 _ hs0_align
            srkPtr' 1#64 v8 v9 v10 v13 hsrk hmax hsrc_klen hck hevs_some hfits_some
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · rw [hpriv_buf, emp_sepConj,
              chainAt_eq_ck_some_cap A.repAlloc x.gc ck x.src hsrk hmax hsrc_klen hck]
          have hsrc_ent :
              (((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A.repAlloc x.gc ck x.src) ⊢
              (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
                ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A.repAlloc x.gc ck x.src) :=
            Entails.pure_right hck_lt (Entails.refl _)
          have hgroup (st_s : State) :
              (A.pool lim (M.stepEvents evs_pre_priv st_init) st_s ∗
                memRegion x.dst 104 ∗
                vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A.repAlloc x.gc ck x.src ∗
                stackAt (s0.sp - 208#64) allocHookStack ∗
                spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗
                ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗
                ((s0.sp - 104#64) ↦₆₄ v13) ∗
                savedRegsOnStack s0) =
              (memRegion x.dst 104 ∗
                vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                (((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                  chainCkSomeCapFrame A.repAlloc x.gc ck x.src) ∗
                A.pool lim (M.stepEvents evs_pre_priv st_init) st_s ∗
                stackAt (s0.sp - 208#64) allocHookStack ∗
                spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗
                ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗
                ((s0.sp - 104#64) ↦₆₄ v13) ∗
                savedRegsOnStack s0) := by
            sep_ac_rfl
          rw [hgroup]
          exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hsrc_ent))
        · simp only [wp_norm, arm64_norm, bne, hcap_ne, Bool.not_false, ↓reduceIte]
        · simp only [wp_norm, arm64_norm]; assumption
        · simp only [wp_norm, arm64_norm]; assumption
        · rw [State.spAligned] at hsp_align ⊢; simp only [wp_norm, arm64_norm]; exact hsp_align
        · simp only [wp_norm, arm64_norm]; assumption
        · simp only [wp_norm, arm64_norm]; assumption
        · simp only [wp_norm, arm64_norm]; assumption
        · simp only [wp_norm, arm64_norm]; assumption
        · simp only [wp_norm, arm64_norm, hpriv_len0]
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm]; assumption
        · simp only [wp_norm, arm64_norm]; exact htrace
        · simp only [wp_norm, arm64_norm]; assumption

set_option maxHeartbeats 1200000 in
theorem chain_clone_placed_priv_pos [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (hshim : subroutine_ok ((blkPC_468).rebase (blkPl_468).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_468).rebase (blkPl_468).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_468).rebase (blkPl_468).base H)
      (lsρ lsMemcpySym) sessionMemcpySpec)
    (x : ChainCloneGhost) (st_init : M.σ) (evs_pre_priv : List AllocEvent)
    (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' v8 v9 v10 v13 : BitVec 64)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpriv_pos : 0 < x.gc.1.priv.bytes.length)
    (hevs_full : ChainCloneEnv x.gc
      ((evs_pre_priv ++ rustAllocEvents x.gc.1.priv.bytes.length 1) ++
        (ckEvents x.gc ++ chainCloneMkEvents x.gc.2.messageKeys)))
    (hfits : FitsEvents M lim (M.stepEvents evs_pre_priv st_init)
      (rustAllocEvents x.gc.1.priv.bytes.length 1 ++
        (ckEvents x.gc ++ chainCloneMkEvents x.gc.2.messageKeys)))
    (hpc : s.pc = (blkPl_468).base + 88#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (_hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp ((blkPC_468).rebase (blkPl_468).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        protoChainAt A.repAlloc x.gc x.src ∗
        A.pool lim (M.stepEvents evs_pre_priv st_init) s ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec M A lim).post (x, st_init) s0 sf))
      Qp := by
  have halloc_nooom := subroutine_ok_allocNoOom_of_budget halloc
  have ⟨hfit_priv, hfit_rest0⟩ :=
    (fitsEvents_append M lim (rustAllocEvents x.gc.1.priv.bytes.length 1)
      (ckEvents x.gc ++ chainCloneMkEvents x.gc.2.messageKeys)
      (M.stepEvents evs_pre_priv st_init)).mp hfits
  have hfit_rest :
      FitsEvents M lim (M.stepEvents (evs_pre_priv ++ rustAllocEvents x.gc.1.priv.bytes.length 1) st_init)
        (ckEvents x.gc ++ chainCloneMkEvents x.gc.2.messageKeys) := by
    rwa [M.stepEvents_append]
  let evs_after_priv := evs_pre_priv ++ rustAllocEvents x.gc.1.priv.bytes.length 1
  dsimp only [sessionShimSpec] at hshim
  dsimp only [sessionMemcpySpec] at hmemcpy
  rw [chainAt_eq_priv_pos A.repAlloc x.gc x.src hsrk hmax hsrc_klen hpriv_pos]
  simp only [sepConj_assoc]
  rw [show (memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        ⌜x.gc.1.priv.bytes.length ≤ x.gc.1.priv.cap.toNat ∧
          x.gc.1.priv.cap.toNat < 2 ^ 63 ∧
          x.gc.1.priv.ptr ≠ 0⌝ ∗
        ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
        ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
        chainPrivPosFrame A.repAlloc x.gc x.src ∗
        A.pool lim (M.stepEvents evs_pre_priv st_init) s ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) =
      (⌜x.gc.1.priv.bytes.length ≤ x.gc.1.priv.cap.toNat ∧
          x.gc.1.priv.cap.toNat < 2 ^ 63 ∧
          x.gc.1.priv.ptr ≠ 0⌝ ∗
        memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
        ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
        chainPrivPosFrame A.repAlloc x.gc x.src ∗
        A.pool lim (M.stepEvents evs_pre_priv st_init) s ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) by sep_ac_rfl]
  refine SepWPp.pure_elim fun ⟨hpriv_le, hpriv_cap_lt, hpriv_ptr⟩ => ?_
  have hpriv_lt63 : x.gc.1.priv.bytes.length < 2 ^ 63 := by omega
  have hpriv_toNat : (BitVec.ofNat 64 x.gc.1.priv.bytes.length).toNat = x.gc.1.priv.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpriv_beq0 : (BitVec.ofNat 64 x.gc.1.priv.bytes.length == 0#64) = false :=
    beq_ofNat_zero_eq_false hpriv_pos (by omega)
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpriv_lay : RustLayoutOk x.gc.1.priv.bytes.length 1 :=
    ⟨⟨hpriv_pos, hpow1, by omega⟩, by decide⟩
  apply SepWPp.of_sepWP (mid := (blkPl_468).base + 116#64)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_call hshim ()
  refine SepWP.transport_budgetPool ‹LibsignalBinary.Heap.VmPreserved _ sf› (hnext := ?_)
  have htr_sf0 : sf.trace = s0.trace := (‹sf.trace = s.trace›).trans htrace
  wp_compact
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_call halloc_nooom (x.gc.1.priv.bytes.length, 1, M.stepEvents evs_pre_priv st_init)
  have htrace1 : sf_1.trace = s0.trace :=
    (‹LibsignalBinary.Heap.AllocCallPreserved _ sf_1›).2.1.trans htr_sf0
  rw [‹sf.sp = s0.sp - 208#64›]
  wp_compact
  apply SepWP.done ‹_› ‹_›
  have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹sf_1.readReg64 Reg.x0 ≠ 0#64›
  let privPtr' := sf_1.readReg64 (Reg.gpr 0#5)
  have hfold_priv_post (st_post : State) :
      ((privPtr' ↦ₛ x.gc.1.priv.bytes) ∗
        (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
        A.pool lim (M.stepEvents (rustAllocEvents x.gc.1.priv.bytes.length 1)
          (M.stepEvents evs_pre_priv st_init)) st_post ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        A.live privPtr' x.gc.1.priv.bytes.length 1 ∗
        memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
        ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        chainPrivPosFrame A.repAlloc x.gc x.src ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) ⊢
      (memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        protoChainAt A.repAlloc x.gc x.src ∗
        A.pool lim (M.stepEvents evs_after_priv st_init) st_post ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) := by
    dsimp only [evs_after_priv]
    rw [← M.stepEvents_append, ← A.repAlloc_live,
        vecU8Buf_pos_eq A.repAlloc privPtr' x.gc.1.priv.bytes hpriv_pos hpriv_lt63 hoom64,
        chainAt_eq_priv_pos A.repAlloc x.gc x.src hsrk hmax hsrc_klen hpriv_pos]
    have hsrc_ent :
        (((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
          ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
          (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
          chainPrivPosFrame A.repAlloc x.gc x.src) ⊢
        (⌜x.gc.1.priv.bytes.length ≤ x.gc.1.priv.cap.toNat ∧
            x.gc.1.priv.cap.toNat < 2 ^ 63 ∧
            x.gc.1.priv.ptr ≠ 0⌝ ∗
          ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
          ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
          (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
          chainPrivPosFrame A.repAlloc x.gc x.src) :=
      Entails.pure_right ⟨hpriv_le, hpriv_cap_lt, hpriv_ptr⟩ (Entails.refl _)
    have hgroup :
        ((privPtr' ↦ₛ x.gc.1.priv.bytes) ∗
          (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
          A.pool lim (M.stepEvents (evs_pre_priv ++ rustAllocEvents x.gc.1.priv.bytes.length 1) st_init) st_post ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          A.repAlloc.live privPtr' x.gc.1.priv.bytes.length 1 ∗
          memRegion x.dst 104 ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
          ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
          chainPrivPosFrame A.repAlloc x.gc x.src ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) =
        (memRegion x.dst 104 ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          (A.repAlloc.live privPtr' x.gc.1.priv.bytes.length 1 ∗ (privPtr' ↦ₛ x.gc.1.priv.bytes)) ∗
          (((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
            ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
            (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
            chainPrivPosFrame A.repAlloc x.gc x.src) ∗
          A.pool lim (M.stepEvents (evs_pre_priv ++ rustAllocEvents x.gc.1.priv.bytes.length 1) st_init) st_post ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) := by
      sep_ac_rfl
    rw [hgroup]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left hsrc_ent)))
  apply SepWPp.of_sepWP (mid := (blkPl_468).base + 136#64)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  wp_call hmemcpy (sf_1.readReg64 Reg.x0, x.gc.1.priv.ptr, x.gc.1.priv.bytes)
  refine SepWP.transport_budgetPool ‹LibsignalBinary.Heap.VmPreserved _ sf_2› (hnext := ?_)
  have htr_sf2 : sf_2.trace = s0.trace := (‹sf_2.trace = _›).trans htrace1
  wp_compact
  have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
  refine SepWP.done ‹_› ‹_› ?_
  have hswap_m2 (P0 P1 P2 R : SepProp) : P0 ∗ P1 ∗ P2 ∗ R = P1 ∗ P2 ∗ P0 ∗ R := by sep_ac_rfl
  rw [hswap_m2]
  refine SepWPp.weaken_pre (hfold_priv_post _) ?_
  change SepWPp ((blkPC_468).rebase (blkPl_468).base H) (s0.readReg64 (Reg.gpr 30#5)) _ _
    (fun sf P_f =>
      sf.sp = s0.sp ∧
      CalleeSavedPreserved s0 sf ∧
      (P_f ⊢ (protoChainCloneSpec M A lim).post (x, st_init) s0 sf))
    Qp
  generalize hpost_eq :
    (fun sf P_f =>
      sf.sp = s0.sp ∧
      CalleeSavedPreserved s0 sf ∧
      (P_f ⊢ (protoChainCloneSpec M A lim).post (x, st_init) s0 sf)) = postPred
  cases hck : x.gc.2.chainKey with
  | none =>
    have hevs_none : ChainCloneEnv x.gc (evs_after_priv ++ chainCloneMkEvents x.gc.2.messageKeys) := by
      simpa [evs_after_priv, ckEvents_of_none hck] using hevs_full
    have hfits_none : FitsEvents M lim (M.stepEvents evs_after_priv st_init)
        (chainCloneMkEvents x.gc.2.messageKeys) := by
      simpa [evs_after_priv, ckEvents_of_none hck] using hfit_rest
    rw [chainAt_eq_ck_none_cap A.repAlloc x.gc x.src hsrk hmax hsrc_klen hck]
    simp only [sepConj_assoc]
    apply SepWPp.of_sepWP (mid := (blkPl_468).base + 244#64)
    wp_steps_sync_pool ((blkPl_468).base + 244#64)
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm]; assumption
    · subst hpost_eq
      refine SepWPp.weaken_pre ?_
        (chain_clone_placed_ck_none (M := M) (A := A) (lim := lim) (H := H) (Qp := Qp)
          hshim halloc hmemcpy x st_init evs_after_priv s0 _ hs0_align
          srkPtr' privPtr' v8 v9 v10 v13 hsrk hmax hsrc_klen hck hevs_none hfits_none
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · rw [chainAt_eq_ck_none_cap A.repAlloc x.gc x.src hsrk hmax hsrc_klen hck]
        exact Entails.of_eq (by sep_ac_rfl)
      · simp only [wp_norm, arm64_norm]
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · rw [State.spAligned] at hs0_align ⊢; simp only [wp_norm, arm64_norm, hsp_sf2]
        exact hs0_align
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; exact htr_sf2
      · simp only [wp_norm, arm64_norm]; assumption
  | some ck =>
    have hevs_some : ChainCloneEnv x.gc
        ((evs_after_priv ++ rustAllocEvents 32 1) ++ chainCloneMkEvents x.gc.2.messageKeys) := by
      simpa [evs_after_priv, ckEvents_of_some hck, List.append_assoc] using hevs_full
    have hfits_some : FitsEvents M lim (M.stepEvents evs_after_priv st_init)
        (rustAllocEvents 32 1 ++ chainCloneMkEvents x.gc.2.messageKeys) := by
      simpa [evs_after_priv, ckEvents_of_some hck] using hfit_rest
    rw [chainAt_eq_ck_some_cap A.repAlloc x.gc ck x.src hsrk hmax hsrc_klen hck]
    simp only [sepConj_assoc]
    rw [show (memRegion x.dst 104 ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
          ⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
          ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
          chainCkSomeCapFrame A.repAlloc x.gc ck x.src ∗
          A.pool lim (M.stepEvents evs_after_priv st_init) sf_2 ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) =
        (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
          memRegion x.dst 104 ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
          ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
          chainCkSomeCapFrame A.repAlloc x.gc ck x.src ∗
          A.pool lim (M.stepEvents evs_after_priv st_init) sf_2 ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) by sep_ac_rfl]
    refine SepWPp.pure_elim fun hck_lt => ?_
    have hcap_ne := cap_add_one_beq_zero_false hck_lt
    apply SepWPp.of_sepWP (mid := (blkPl_468).base + 148#64)
    wp_steps_sync_pool ((blkPl_468).base + 148#64)
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm, arm64_norm, hcap_ne, Bool.false_eq_true, ↓reduceIte]
    · simp only [wp_norm, arm64_norm]; assumption
    · subst hpost_eq
      refine SepWPp.weaken_pre ?_
        (chain_clone_placed_ck_some (M := M) (A := A) (lim := lim) (H := H) (Qp := Qp)
          hshim halloc hmemcpy x ck st_init evs_after_priv s0 _ hs0_align
          srkPtr' privPtr' v8 v9 v10 v13 hsrk hmax hsrc_klen hck hevs_some hfits_some
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · rw [chainAt_eq_ck_some_cap A.repAlloc x.gc ck x.src hsrk hmax hsrc_klen hck]
        have hsrc_ent :
            (((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
              chainCkSomeCapFrame A.repAlloc x.gc ck x.src) ⊢
            (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
              ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
              chainCkSomeCapFrame A.repAlloc x.gc ck x.src) :=
          Entails.pure_right hck_lt (Entails.refl _)
        have hgroup (st_s : State) :
            (A.pool lim (M.stepEvents evs_after_priv st_init) st_s ∗
              memRegion x.dst 104 ∗
              vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
              vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
              ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
              chainCkSomeCapFrame A.repAlloc x.gc ck x.src ∗
              stackAt (s0.sp - 208#64) allocHookStack ∗
              spillSlotsExist s0.sp ∗
              ((s0.sp - 144#64) ↦₆₄ v8) ∗
              ((s0.sp - 136#64) ↦₆₄ v9) ∗
              ((s0.sp - 128#64) ↦₆₄ v10) ∗
              ((s0.sp - 104#64) ↦₆₄ v13) ∗
              savedRegsOnStack s0) =
            (memRegion x.dst 104 ∗
              vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
              vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
              (((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A.repAlloc x.gc ck x.src) ∗
              A.pool lim (M.stepEvents evs_after_priv st_init) st_s ∗
              stackAt (s0.sp - 208#64) allocHookStack ∗
              spillSlotsExist s0.sp ∗
              ((s0.sp - 144#64) ↦₆₄ v8) ∗
              ((s0.sp - 136#64) ↦₆₄ v9) ∗
              ((s0.sp - 128#64) ↦₆₄ v10) ∗
              ((s0.sp - 104#64) ↦₆₄ v13) ∗
              savedRegsOnStack s0) := by
          sep_ac_rfl
        rw [hgroup]
        exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left hsrc_ent)))
      · simp only [wp_norm, arm64_norm, hcap_ne, Bool.false_eq_true, ↓reduceIte]
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · rw [State.spAligned] at hs0_align ⊢; simp only [wp_norm, arm64_norm, hsp_sf2]
        exact hs0_align
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; assumption
      · simp only [wp_norm, arm64_norm]; exact htr_sf2
      · simp only [wp_norm, arm64_norm]; assumption

end LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.ClonePlacedPrefixBudget
