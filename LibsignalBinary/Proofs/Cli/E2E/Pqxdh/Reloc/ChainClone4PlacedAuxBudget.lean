/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone4PlacedMidBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import ProofLib.ProgramReflection
import ProofLib.RegChain
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `ck_some` and `priv` Stage Proofs for `Chain::clone` (Block `524`)

Budget-threaded (`RustCliAllocBudget M` / `VmPreserved`) stage proofs for Block `524`
(`(blkPC_524).rebase (blkPl_524).base H`):
- Stage-tail event lists `chainCloneFromCkEvents` and `chainCloneFromPrivEvents`;
- `chain_clone_placed_ck_some` (`+148 → ret`), `chain_clone_placed_priv_nil` (`+88 → ret`),
  and `chain_clone_placed_priv_pos` (`+88 → ret`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone4PlacedAuxBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (
  ChainKey PublicKey ReceiverChain maxMessageKeys
)
open CryptoVerification (
  LibsignalPlacement lsρ lsRustNoAllocShimSym lsRustAllocSym lsMemcpySym
)
open CryptoVerification.RustHeap (
  LayoutOk allocHookStack arrayAt vecBuf vecU8Buf
)
open CryptoVerification.LibsignalSessionRepr (ChainGhost)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (
  ChainCloneGhost
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone.ChainCloneRegReadSimp (
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
)
open CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainCloneDefs (
  protoChainAt clonedOptChainKeyBuf spillSlotsExist savedRegsOnStack
  vecU8Buf_pos_eq beq_ofNat_zero_eq_false cap_add_one_beq_zero_false
  chainCkSomeFrame chainAt_eq_ck_some
  chainAt_eq_ck_none_cap
  chainCkSomeCapFrame chainAt_eq_ck_some_cap
  chainPrivLenFrame chainAt_eq_priv_len
  chainPrivPosFrame chainAt_eq_priv_pos
)
open CryptoVerification.CliHandshake.Placed (blkPC_524 blkPl_524 blkLib_eq_524)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEvents
  RustCliAllocBudget RustLayoutOk VmPreserved
  fitsEvents_append rustAllocEvents
  rustCliAllocBudgetSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (
  ChainCloneEnv chainCloneEvents
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.ClonePlacedDefsBudget (
  protoChainCloneSpec sessionMemcpySpec sessionShimSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone4PlacedMidBudget (
  chainCloneMkEvents chain_clone_placed_ck_none
  chain_clone_placed_mks_nil chain_clone_placed_mks_nonempty
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

/-! ## 1. Stage-Tail Event Helpers for `chainCloneEvents` -/

/-- Suffix of `chainCloneEvents gc` emitted from the `chain_key` stage onward. -/
def chainCloneFromCkEvents (gc : ChainGhost × ReceiverChain) : List AllocEvent :=
  (match gc.2.chainKey with
   | none => []
   | some _ => rustAllocEvents 32 1) ++
  chainCloneMkEvents gc.2.messageKeys

/-- Suffix of `chainCloneEvents gc` emitted from the `priv` stage onward. -/
def chainCloneFromPrivEvents (gc : ChainGhost × ReceiverChain) : List AllocEvent :=
  (if gc.1.priv.bytes = [] then [] else rustAllocEvents gc.1.priv.bytes.length 1) ++
  chainCloneFromCkEvents gc

theorem chainCloneFromCkEvents_of_none {gc : ChainGhost × ReceiverChain}
    (hck : gc.2.chainKey = none) :
    chainCloneFromCkEvents gc = chainCloneMkEvents gc.2.messageKeys := by
  simp [chainCloneFromCkEvents, hck]

theorem chainCloneFromCkEvents_of_some {gc : ChainGhost × ReceiverChain} {ck : ChainKey}
    (hck : gc.2.chainKey = some ck) :
    chainCloneFromCkEvents gc = rustAllocEvents 32 1 ++ chainCloneMkEvents gc.2.messageKeys := by
  simp [chainCloneFromCkEvents, hck]

theorem chainCloneFromPrivEvents_of_nil {gc : ChainGhost × ReceiverChain}
    (hpriv : gc.1.priv.bytes = []) :
    chainCloneFromPrivEvents gc = chainCloneFromCkEvents gc := by
  simp [chainCloneFromPrivEvents, hpriv]

theorem chainCloneFromPrivEvents_of_pos {gc : ChainGhost × ReceiverChain}
    (hpos : 0 < gc.1.priv.bytes.length) :
    chainCloneFromPrivEvents gc =
      rustAllocEvents gc.1.priv.bytes.length 1 ++ chainCloneFromCkEvents gc := by
  simp [chainCloneFromPrivEvents, List.ne_nil_of_length_pos hpos]

theorem chainCloneEvents_of_srk_pos {gc : ChainGhost × ReceiverChain}
    (hsrk_pos : 0 < gc.1.srk.bytes.length) :
    chainCloneEvents gc =
      rustAllocEvents gc.1.srk.bytes.length 1 ++ chainCloneFromPrivEvents gc := by
  rcases gc with ⟨g, c⟩
  dsimp only at hsrk_pos
  cases hck : c.chainKey <;>
    simp [chainCloneEvents, chainCloneFromPrivEvents, chainCloneFromCkEvents,
      chainCloneMkEvents, hck, List.ne_nil_of_length_pos hsrk_pos, List.append_assoc]

theorem spAligned_sub_208 (sp : BitVec 64) (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp - 208#64) &&& 15#64 == 0#64) = true :=
  spAligned_sub sp 208 h (by decide)

/-! ## 2. `chain_key = some ck` Path (`+148 → ret`) -/

set_option maxHeartbeats 1200000 in
theorem chain_clone_placed_ck_some [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (hshim : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsMemcpySym) sessionMemcpySpec)
    (x : ChainCloneGhost) (ck : ChainKey) (st_init : M.σ) (evs_pre : List AllocEvent)
    (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' privPtr' v8 v9 v10 v13 : BitVec 64)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hck : x.gc.2.chainKey = some ck)
    (hevs_full : ChainCloneEnv x.gc (evs_pre ++ chainCloneFromCkEvents x.gc))
    (hfits : FitsEvents M lim (M.stepEvents evs_pre st_init) (chainCloneFromCkEvents x.gc))
    (hpc : s.pc = (blkPl_524).base + 148#64)
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
    SepWPp ((blkPC_524).rebase (blkPl_524).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        protoChainAt A.repAlloc x.gc x.src ∗
        A.pool lim (M.stepEvents evs_pre st_init) s ∗
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
  rw [chainCloneFromCkEvents_of_some hck] at hevs_full hfits
  obtain ⟨hfits_ck, hfits_mks_raw⟩ :=
    (fitsEvents_append M lim (rustAllocEvents 32 1)
      (chainCloneMkEvents x.gc.2.messageKeys) (M.stepEvents evs_pre st_init)).mp hfits
  obtain ⟨⟨hck_max, hck_enf, hck_ram, hck_va⟩, -⟩ :
      FitsEvents M lim (M.stepEvents evs_pre st_init) [.alloc 32] := hfits_ck
  let evs_after_ck := evs_pre ++ rustAllocEvents 32 1
  have hevs_after :
      ChainCloneEnv x.gc (evs_after_ck ++ chainCloneMkEvents x.gc.2.messageKeys) := by
    simpa [evs_after_ck, List.append_assoc] using hevs_full
  have hst_after :
      M.stepEvents (rustAllocEvents 32 1) (M.stepEvents evs_pre st_init) =
        M.stepEvents evs_after_ck st_init := by
    simp [evs_after_ck, M.stepEvents_append]
  have hfits_mks :
      FitsEvents M lim (M.stepEvents evs_after_ck st_init)
        (chainCloneMkEvents x.gc.2.messageKeys) := by
    rwa [← hst_after]
  have hmks_nil := fun s' ckPtr' (hnil : x.gc.2.messageKeys = []) =>
    chain_clone_placed_mks_nil (M := M) (A := A) (lim := lim) (H := H) (Qp := Qp)
      x st_init evs_after_ck s0 s' srkPtr' privPtr' 32#64 ckPtr'
      v9 v10 v13 ck.index ⟨32#64, ckPtr'⟩
      hsrk hmax hsrc_klen hnil
      (by simpa [chainCloneMkEvents, hnil] using hevs_after)
  have hmks_ne := fun s' ckPtr' (hpos : 0 < x.gc.2.messageKeys.length) =>
    chain_clone_placed_mks_nonempty (M := M) (A := A) (lim := lim) (H := H) (Qp := Qp)
      hshim halloc hmemcpy x st_init evs_after_ck s0 s' hs0_align
      srkPtr' privPtr' 32#64 ckPtr'
      v9 v10 v13 ck.index ⟨32#64, ckPtr'⟩
      hsrk hmax hsrc_klen hpos hevs_after hfits_mks
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
        A.pool lim (M.stepEvents evs_pre st_init) s ∗
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
        A.pool lim (M.stepEvents evs_pre st_init) s ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) by sep_ac_rfl]
  refine SepWPp.pure_elim fun ⟨hck_le, hck_lt, hck_ptr⟩ => ?_
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hck_lay : LayoutOk 32 1 := ⟨by decide, hpow1, by decide⟩
  have hck_rlay : RustLayoutOk 32 1 := ⟨hck_lay, by decide⟩
  have hck_len : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  have htrunc32_ck : BitVec.truncate 32 (BitVec.zeroExtend 64 ck.index) = ck.index :=
    (BitVec.setWidth_setWidth_of_le ck.index (by decide)).trans (BitVec.setWidth_eq ck.index)
  apply SepWPp.of_sepWP (mid := (blkPl_524).base + 180#64)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_call hshim ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  have htr_sf : sf.trace = s0.trace := (‹sf.trace = s.trace›).trans htrace
  wp_compact
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_call halloc_nooom (32, 1, M.stepEvents evs_pre st_init)
  have htrace1 : sf_1.trace = s0.trace :=
    (‹AllocCallPreserved _ sf_1›).2.1.trans htr_sf
  rw [‹sf.sp = s0.sp - 208#64›]
  wp_compact
  apply SepWP.done ‹_› ‹_›
  have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹sf_1.readReg64 Reg.x0 ≠ 0#64›
  let ckPtr' := sf_1.readReg64 (Reg.gpr 0#5)
  have hfold_ck_post : ∀ (sPool : State),
      (A.pool lim (M.stepEvents (rustAllocEvents 32 1) (M.stepEvents evs_pre st_init)) sPool ∗
        (ckPtr' ↦ₛ keyToBytes32 ck.key) ∗
        (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
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
        A.pool lim (M.stepEvents evs_after_ck st_init) sPool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) := by
    intro sPool
    have hck_buf_eq :
        clonedOptChainKeyBuf A.repAlloc ⟨32#64, ckPtr'⟩ 32#64 ckPtr' ck.index x.gc.2.chainKey =
          A.live ckPtr' 32 1 ∗ (ckPtr' ↦ₛ keyToBytes32 ck.key) := by
      rw [hck]
      simp only [clonedOptChainKeyBuf, and_self, pure_true, emp_sepConj]
      have hpos32 : 0 < (keyToBytes32 ck.key).length := by rw [hck_len]; decide
      have hlt32 : (keyToBytes32 ck.key).length < 2 ^ 63 := by rw [hck_len]; decide
      have hv := vecU8Buf_pos_eq A.repAlloc ckPtr' (keyToBytes32 ck.key) hpos32 hlt32 hoom64
      rw [hck_len] at hv
      exact hv
    rw [hst_after, hck_buf_eq,
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
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left hsrc_ent)))))
    exact Entails.of_eq (by dsimp only [RustCliAllocBudget.repAlloc]; sep_ac_rfl)
  by_cases hmk_nil : x.gc.2.messageKeys = []
  · have hlen0 : BitVec.ofNat 64 x.gc.2.messageKeys.length = 0#64 := by simp [hmk_nil]
    apply SepWPp.of_sepWP (mid := (blkPl_524).base + 732#64)
    wp_steps_sync_pool (lsρ lsMemcpySym)
    wp_call hmemcpy (ckPtr', x.gc.1.ck.ptr, keyToBytes32 ck.key)
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
    have htr_sf2 : sf_2.trace = s0.trace := (‹sf_2.trace = _›).trans htrace1
    wp_compact
    have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
    have hx27_sf2 : sf_2.readReg64 (Reg.gpr 27#5) = BitVec.zeroExtend 64 ck.index := ‹_›
    wp_steps_sync_pool ((blkPl_524).base + 732#64)
    refine SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm]; assumption) ?_
    refine SepWPp.weaken_pre
      (Entails.trans (by rw [hlen0]; exact Entails.of_eq rfl)
        (hfold_ck_post _))
      (hmks_nil _ ckPtr' hmk_nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · rw [State.spAligned] at hs0_align ⊢; simp only [wp_norm, hsp_sf2]
      exact spAligned_sub_208 s0.sp hs0_align
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · unfold State.readReg32; simp only [wp_norm]; rw [hx27_sf2, htrunc32_ck]
    · simp only [wp_norm]; exact htr_sf2
    · simp only [wp_norm]; assumption
  · have hpos : 0 < x.gc.2.messageKeys.length := List.length_pos_of_ne_nil hmk_nil
    have hbeq0 : (BitVec.ofNat 64 x.gc.2.messageKeys.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hpos (by unfold maxMessageKeys at hmax; omega)
    apply SepWPp.of_sepWP (mid := (blkPl_524).base + 260#64)
    wp_steps_sync_pool (lsρ lsMemcpySym)
    wp_call hmemcpy (ckPtr', x.gc.1.ck.ptr, keyToBytes32 ck.key)
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
    have htr_sf2 : sf_2.trace = s0.trace := (‹sf_2.trace = _›).trans htrace1
    wp_compact
    have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
    have hx27_sf2 : sf_2.readReg64 (Reg.gpr 27#5) = BitVec.zeroExtend 64 ck.index := ‹_›
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := Program.rebase blkPC_524 (blkPl_524).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H) (fun _ => none))
      blkLib_eq_524
      (mid := (blkPl_524).base + 260#64)
    intro _m_strip
    wp_steps
    refine SepWP.done (by simp only [wp_norm, hbeq0, Bool.not_false, ↓reduceIte])
      (by simp only [wp_norm]; assumption) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
    refine SepWP.done (by simp only [wp_norm, hbeq0, Bool.not_false, ↓reduceIte])
      (by simp only [wp_norm]; assumption) ?_
    refine SepWPp.weaken_pre
      (hfold_ck_post _)
      (hmks_ne _ ckPtr' hpos ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · simp only [wp_norm, hbeq0, Bool.not_false, ↓reduceIte]
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · rw [State.spAligned] at hs0_align ⊢; simp only [wp_norm, hsp_sf2]
      exact spAligned_sub_208 s0.sp hs0_align
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · unfold State.readReg32; simp only [wp_norm]; rw [hx27_sf2, htrunc32_ck]
    · simp only [wp_norm]; exact htr_sf2
    · simp only [wp_norm]; assumption

/-! ## 3. `priv = []` Path (`+88 → ret`) -/

set_option maxHeartbeats 1200000 in
theorem chain_clone_placed_priv_nil [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (hshim : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsMemcpySym) sessionMemcpySpec)
    (x : ChainCloneGhost) (st_init : M.σ) (evs_pre : List AllocEvent)
    (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' v8 v9 v10 v13 : BitVec 64)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpriv : x.gc.1.priv.bytes = [])
    (hevs_full : ChainCloneEnv x.gc (evs_pre ++ chainCloneFromPrivEvents x.gc))
    (hfits : FitsEvents M lim (M.stepEvents evs_pre st_init) (chainCloneFromPrivEvents x.gc))
    (hpc : s.pc = (blkPl_524).base + 88#64)
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
    SepWPp ((blkPC_524).rebase (blkPl_524).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        protoChainAt A.repAlloc x.gc x.src ∗
        A.pool lim (M.stepEvents evs_pre st_init) s ∗
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
  rw [chainCloneFromPrivEvents_of_nil hpriv] at hevs_full hfits
  have hck_none := fun s' (hck : x.gc.2.chainKey = none) =>
    chain_clone_placed_ck_none (M := M) (A := A) (lim := lim) (H := H) (Qp := Qp)
      hshim halloc hmemcpy x st_init evs_pre s0 s' hs0_align
      srkPtr' 1#64 v8 v9 v10 v13 hsrk hmax hsrc_klen hck
      (by simpa [chainCloneFromCkEvents_of_none hck] using hevs_full)
      (by simpa [chainCloneFromCkEvents_of_none hck] using hfits)
  have hck_some := fun s' ck (hck : x.gc.2.chainKey = some ck) =>
    chain_clone_placed_ck_some (M := M) (A := A) (lim := lim) (H := H) (Qp := Qp)
      hshim halloc hmemcpy x ck st_init evs_pre s0 s' hs0_align
      srkPtr' 1#64 v8 v9 v10 v13 hsrk hmax hsrc_klen hck hevs_full hfits
  generalize (fun sf P_f =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
      (P_f ⊢ (protoChainCloneSpec M A lim).post (x, st_init) s0 sf)) =
    postPred at hck_none hck_some ⊢
  have hpriv_buf :
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) 1#64 x.gc.1.priv.bytes = emp := by
    rw [hpriv]; simp [vecU8Buf, vecBuf, arrayAt]
  have hpriv_len0 : BitVec.ofNat 64 x.gc.1.priv.bytes.length = 0#64 := by
    simp [hpriv]
  rw [chainAt_eq_priv_len A.repAlloc x.gc x.src hsrk hmax hsrc_klen, hpriv_len0]
  simp only [sepConj_assoc]
  wp_steps_sync_pool ((blkPl_524).base + 232#64)
  have hfold_priv : ∀ (sPool : State),
      (A.pool lim (M.stepEvents evs_pre st_init) sPool ∗
        memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        ((x.src + 40#64) ↦₆₄ 0#64) ∗
        chainPrivLenFrame A.repAlloc x.gc x.src ∗
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
        A.pool lim (M.stepEvents evs_pre st_init) sPool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) := by
    intro sPool
    rw [chainAt_eq_priv_len A.repAlloc x.gc x.src hsrk hmax hsrc_klen, hpriv_len0]
    sep_ac_rfl
  rw [hfold_priv _]
  cases hck : x.gc.2.chainKey with
  | none =>
    rw [chainAt_eq_ck_none_cap A.repAlloc x.gc x.src hsrk hmax hsrc_klen hck]
    simp only [sepConj_assoc]
    wp_steps_sync_pool ((blkPl_524).base + 244#64)
    refine SepWPp.weaken_pre ?_
      (hck_none _ hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · rw [hpriv_buf, emp_sepConj,
          chainAt_eq_ck_none_cap A.repAlloc x.gc x.src hsrk hmax hsrc_klen hck]
      exact Entails.of_eq (by sep_ac_rfl)
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · rw [State.spAligned] at hsp_align ⊢; simp only [wp_norm]; exact hsp_align
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm, hpriv_len0]
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · exact htrace
    · simp only [wp_norm]; assumption
  | some ck =>
    rw [chainAt_eq_ck_some_cap A.repAlloc x.gc ck x.src hsrk hmax hsrc_klen hck]
    simp only [sepConj_assoc]
    rw [show (memRegion x.dst 104 ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          ⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
          ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
          chainCkSomeCapFrame A.repAlloc x.gc ck x.src ∗
          A.pool lim (M.stepEvents evs_pre st_init) _ ∗
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
          A.pool lim (M.stepEvents evs_pre st_init) _ ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) by sep_ac_rfl]
    refine SepWPp.pure_elim fun hck_lt => ?_
    have hcap_ne := cap_add_one_beq_zero_false hck_lt
    apply SepWPp.of_sepWP (mid := (blkPl_524).base + 148#64)
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := Program.rebase blkPC_524 (blkPl_524).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H) (fun _ => none))
      blkLib_eq_524
      (mid := (blkPl_524).base + 148#64)
    intro _m_strip
    wp_steps
    refine SepWP.done (by simp only [wp_norm, bne, hcap_ne, Bool.not_false, ↓reduceIte])
      (by simp only [wp_norm]; assumption) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
    refine SepWP.done (by simp only [wp_norm, bne, hcap_ne, Bool.not_false, ↓reduceIte])
      (by simp only [wp_norm]; assumption) ?_
    refine SepWPp.weaken_pre ?_
      (hck_some _ ck hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · rw [hpriv_buf, emp_sepConj,
          chainAt_eq_ck_some_cap A.repAlloc x.gc ck x.src hsrk hmax hsrc_klen hck]
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (Entails.pure_right hck_lt (Entails.refl _)))))
      exact Entails.of_eq (by sep_ac_rfl)
    · simp only [wp_norm, bne, hcap_ne, Bool.not_false, ↓reduceIte]
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · rw [State.spAligned] at hsp_align ⊢; simp only [wp_norm]; exact hsp_align
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm, hpriv_len0]
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · exact htrace
    · simp only [wp_norm]; assumption

/-! ## 4. `0 < priv.length` Path (`+88 → ret`) -/

set_option maxHeartbeats 1200000 in
theorem chain_clone_placed_priv_pos [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (hshim : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (lsρ lsMemcpySym) sessionMemcpySpec)
    (x : ChainCloneGhost) (st_init : M.σ) (evs_pre : List AllocEvent)
    (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' v8 v9 v10 v13 : BitVec 64)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpriv_pos : 0 < x.gc.1.priv.bytes.length)
    (hevs_full : ChainCloneEnv x.gc (evs_pre ++ chainCloneFromPrivEvents x.gc))
    (hfits : FitsEvents M lim (M.stepEvents evs_pre st_init) (chainCloneFromPrivEvents x.gc))
    (hpc : s.pc = (blkPl_524).base + 88#64)
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
    SepWPp ((blkPC_524).rebase (blkPl_524).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        protoChainAt A.repAlloc x.gc x.src ∗
        A.pool lim (M.stepEvents evs_pre st_init) s ∗
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
  rw [chainCloneFromPrivEvents_of_pos hpriv_pos] at hevs_full hfits
  obtain ⟨hfits_priv, hfits_ck_raw⟩ :=
    (fitsEvents_append M lim (rustAllocEvents x.gc.1.priv.bytes.length 1)
      (chainCloneFromCkEvents x.gc) (M.stepEvents evs_pre st_init)).mp hfits
  let evs_after_priv := evs_pre ++ rustAllocEvents x.gc.1.priv.bytes.length 1
  have hevs_after :
      ChainCloneEnv x.gc (evs_after_priv ++ chainCloneFromCkEvents x.gc) := by
    simpa [evs_after_priv, List.append_assoc] using hevs_full
  have hst_after :
      M.stepEvents (rustAllocEvents x.gc.1.priv.bytes.length 1) (M.stepEvents evs_pre st_init) =
        M.stepEvents evs_after_priv st_init := by
    simp [evs_after_priv, M.stepEvents_append]
  have hfits_ck :
      FitsEvents M lim (M.stepEvents evs_after_priv st_init) (chainCloneFromCkEvents x.gc) := by
    rwa [← hst_after]
  have hck_none := fun s' privPtr' (hck : x.gc.2.chainKey = none) =>
    chain_clone_placed_ck_none (M := M) (A := A) (lim := lim) (H := H) (Qp := Qp)
      hshim halloc hmemcpy x st_init evs_after_priv s0 s' hs0_align
      srkPtr' privPtr' v8 v9 v10 v13 hsrk hmax hsrc_klen hck
      (by simpa [chainCloneFromCkEvents_of_none hck] using hevs_after)
      (by simpa [chainCloneFromCkEvents_of_none hck] using hfits_ck)
  have hck_some := fun s' privPtr' ck (hck : x.gc.2.chainKey = some ck) =>
    chain_clone_placed_ck_some (M := M) (A := A) (lim := lim) (H := H) (Qp := Qp)
      hshim halloc hmemcpy x ck st_init evs_after_priv s0 s' hs0_align
      srkPtr' privPtr' v8 v9 v10 v13 hsrk hmax hsrc_klen hck hevs_after hfits_ck
  dsimp only [sessionShimSpec] at hshim
  dsimp only [sessionMemcpySpec] at hmemcpy
  generalize (fun sf P_f =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
      (P_f ⊢ (protoChainCloneSpec M A lim).post (x, st_init) s0 sf)) =
    postPred at hck_none hck_some ⊢
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
        A.pool lim (M.stepEvents evs_pre st_init) s ∗
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
        A.pool lim (M.stepEvents evs_pre st_init) s ∗
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
  have hpriv_lay : LayoutOk x.gc.1.priv.bytes.length 1 := ⟨hpriv_pos, hpow1, by omega⟩
  have hpriv_rlay : RustLayoutOk x.gc.1.priv.bytes.length 1 := ⟨hpriv_lay, by decide⟩
  apply SepWPp.of_sepWP (mid := (blkPl_524).base + 116#64)
  apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
    (Q := Program.rebase blkPC_524 (blkPl_524).base
      (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H) (fun _ => none))
    blkLib_eq_524
    (mid := (lsρ lsRustNoAllocShimSym))
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp only [wp_norm, hpriv_beq0, Bool.false_eq_true, ↓reduceIte])
    (by simp only [wp_norm]; assumption) fun _m_real _hnsp => ?_
  refine SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  wp_call hshim ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  have htr_sf : sf.trace = s0.trace := (‹sf.trace = _›).trans htrace
  wp_compact
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_call halloc_nooom (x.gc.1.priv.bytes.length, 1, M.stepEvents evs_pre st_init)
  have htrace1 : sf_1.trace = s0.trace :=
    (‹AllocCallPreserved _ sf_1›).2.1.trans htr_sf
  rw [‹sf.sp = s0.sp - 208#64›]
  wp_compact
  apply SepWP.done ‹_› ‹_›
  have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹sf_1.readReg64 Reg.x0 ≠ 0#64›
  let privPtr' := sf_1.readReg64 (Reg.gpr 0#5)
  have hfold_priv_post : ∀ (sPool : State),
      (A.pool lim (M.stepEvents (rustAllocEvents x.gc.1.priv.bytes.length 1)
          (M.stepEvents evs_pre st_init)) sPool ∗
        (privPtr' ↦ₛ x.gc.1.priv.bytes) ∗
        (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
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
        A.pool lim (M.stepEvents evs_after_priv st_init) sPool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) := by
    intro sPool
    rw [hst_after,
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
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left hsrc_ent))))
    exact Entails.of_eq (by dsimp only [RustCliAllocBudget.repAlloc]; sep_ac_rfl)
  apply SepWPp.of_sepWP (mid := (blkPl_524).base + 136#64)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  wp_call hmemcpy (privPtr', x.gc.1.priv.ptr, x.gc.1.priv.bytes)
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
  have htr_sf2 : sf_2.trace = s0.trace := (‹sf_2.trace = _›).trans htrace1
  wp_compact
  have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
  refine SepWP.done ‹_› ‹_› ?_
  refine SepWPp.weaken_pre (hfold_priv_post _) ?_
  cases hck : x.gc.2.chainKey with
  | none =>
    rw [chainAt_eq_ck_none_cap A.repAlloc x.gc x.src hsrk hmax hsrc_klen hck]
    simp only [sepConj_assoc]
    wp_steps_sync_pool ((blkPl_524).base + 244#64)
    refine SepWPp.weaken_pre ?_
      (hck_none _ privPtr' hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · rw [chainAt_eq_ck_none_cap A.repAlloc x.gc x.src hsrk hmax hsrc_klen hck]
      exact Entails.of_eq (by sep_ac_rfl)
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · rw [State.spAligned] at hs0_align ⊢; simp only [wp_norm, hsp_sf2]
      exact spAligned_sub_208 s0.sp hs0_align
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · exact htr_sf2
    · simp only [wp_norm]; assumption
  | some ck =>
    rw [chainAt_eq_ck_some_cap A.repAlloc x.gc ck x.src hsrk hmax hsrc_klen hck]
    simp only [sepConj_assoc]
    rw [show (memRegion x.dst 104 ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
          ⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
          ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
          chainCkSomeCapFrame A.repAlloc x.gc ck x.src ∗
          A.pool lim (M.stepEvents evs_after_priv st_init) _ ∗
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
          A.pool lim (M.stepEvents evs_after_priv st_init) _ ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) by sep_ac_rfl]
    refine SepWPp.pure_elim fun hck_lt => ?_
    have hcap_ne := cap_add_one_beq_zero_false hck_lt
    apply SepWPp.of_sepWP (mid := (blkPl_524).base + 148#64)
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := Program.rebase blkPC_524 (blkPl_524).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H) (fun _ => none))
      blkLib_eq_524
      (mid := (blkPl_524).base + 148#64)
    intro _m_strip
    wp_steps
    refine SepWP.done (by simp only [wp_norm, hcap_ne, Bool.false_eq_true, ↓reduceIte])
      (by simp only [wp_norm]; assumption) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
    refine SepWP.done (by simp only [wp_norm, hcap_ne, Bool.false_eq_true, ↓reduceIte])
      (by simp only [wp_norm]; assumption) ?_
    refine SepWPp.weaken_pre ?_
      (hck_some _ privPtr' ck hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · rw [chainAt_eq_ck_some_cap A.repAlloc x.gc ck x.src hsrk hmax hsrc_klen hck]
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (Entails.pure_right hck_lt (Entails.refl _))))))
      exact Entails.of_eq (by sep_ac_rfl)
    · simp only [wp_norm, hcap_ne, Bool.false_eq_true, ↓reduceIte]
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · rw [State.spAligned] at hs0_align ⊢; simp only [wp_norm, hsp_sf2]
      exact spAligned_sub_208 s0.sp hs0_align
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · exact htr_sf2
    · simp only [wp_norm]; assumption

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone4PlacedAuxBudget
