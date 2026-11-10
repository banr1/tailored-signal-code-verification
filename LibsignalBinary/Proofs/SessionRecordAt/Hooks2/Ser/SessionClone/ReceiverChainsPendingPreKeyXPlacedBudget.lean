/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.BaseBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.BaseX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneBaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.PrologueFields1To4
meta import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.PrologueFields1To4
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ReceiverChainsPendingPreKey
meta import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ReceiverChainsPendingPreKey
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ReceiverChainsPendingPreKeyXPlaced
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `SessionStructure::clone` Fields 5–6: `receiver_chains` and `pending_pre_key` (Block `80`)

Verifies the relocatable `receiver_chains` loop (`+572 / +336 → +576 / +476`) and `pending_pre_key`
cloning (`+576 / +476 → +592 ∨ +648`) in Block `80` under `RustCliAllocBudget M` and `FitsEvents`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ReceiverChainsPendingPreKeyXPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ReceiverChain)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded lsmpl lsρ
  lsRustNoAllocShimSym lsRustAllocSym lsMemcpySym
  withLsCl withLsCodeLoaded withMemEq
)
open CryptoVerification.RustHeap (
  vecU8At vecU8Buf vecBuf arrayAt arrayAt_nil arrayAt_cons
)
open CryptoVerification.E2E.Record (lenField)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt vecGhostAt)
open CryptoVerification.LibsignalTripleRatchetRepr (TailVecGhost optTailVecAt noneCap)
open CryptoVerification.LibsignalTripleRatchet (extHookStack sessionMemcpySpec)
open CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1 (chainCloneStackX)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (
  chainHeap chainAt_entails_chunks104_6QW chainAt_of_chunks104_6QW
  chunks104_6QWAt
)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps (
  pointsTo128_eq_pointsTo64
  chunks104_6QWAt_entails_memRegion memRegion_104_entails_chunks104_6QWAt
  vecGhostAt_eq_of_nil vecGhostAt_eq_of_pos
  vecU8Buf_nil_eq vecU8Buf_pos_eq
  eq_nil_or_length_pos ofNat_ne_zero_of_pos beq_ofNat_zero_eq_false
  segClone_pure_eq_emp cap_add_one_ne_zero cap_add_one_beq_zero_eq_false
  exists_tail24_decomp segClone_vecBuf_expose_arrayAt segClone_vecBuf_reassemble_arrayAt
  segClone_vecBuf_chain_of_arrayAt segClone_vecBuf_chain_nil_eq segClone_vecBufRest
  segClone_bv_ofNat_mul_104_toNat segClone_bv_ofNat_mul_104_beq_zero
  segClone_bv_ofNat_succ_sub_one segClone_off_add_succ_mul_104
)
open CryptoVerification.E2E.Record.Placed (lsProg_80 blkPC_80 blkPl_80 blkPl_82 blkLib_eq_80)
open CryptoVerification.E2E.Record.Serialization (SessionCloneGhost encChainMem)
open CryptoVerification.E2E.Record.Serialization.SessionCloneAux (
  sepWPp_of_sepWP_lscl_sc chunks104_6QWAt_sp_0xf8 ScOptPendClone
  sc_chainClone_placed_ok_at_x
)
open Proofs.libsignal.Stage1X (lscall_of_withLsCl)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits FitsEvents FitsEnv fitsEvents_append
  RustCliAllocBudget RustLayoutOk VmPreserved AllocCallPreserved rustAllocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (session2ShimBudgetSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (optTailCloneEvents)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (SepWPpLsCl)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneBaseXBudget (
  chainCloneEvents ChainCloneEnv chainCloneSpecX ChainCloneLocal1PlacedOkX
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg
  updateCalleeSavedVRegs
  Arm64.State.calleeSavedVRegs_writeReg64_gpr
  Arm64.State.calleeSavedVRegs_writeReg32_gpr
  Arm64.State.calleeSavedVRegs_setPC
  Arm64.State.calleeSavedVRegs_setPState

/-! ## Call adapters and event abbreviations -/

private theorem sepWPpLsCl_pure_2nd_rc {pl : Obj.MultiPlacement} {prog : Program}
    {ret : BitVec 64} {s : State} {P1 P2 : SepProp} {φ : Prop}
    {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPpLsCl pl prog ret s (P1 ∗ P2) Q Qp) :
    SepWPpLsCl pl prog ret s (P1 ∗ ⌜φ⌝ ∗ P2) Q Qp := by
  intro hcl
  rw [← sepConj_assoc, sepConj_comm P1 ⌜φ⌝, sepConj_assoc]
  exact SepWPp.pure_elim fun hφ => h hφ hcl

private theorem sepWPpLsCl_pure_3rd_rc {pl : Obj.MultiPlacement} {prog : Program}
    {ret : BitVec 64} {s : State} {P1 P2 P3 : SepProp} {φ : Prop}
    {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPpLsCl pl prog ret s (P1 ∗ P2 ∗ P3) Q Qp) :
    SepWPpLsCl pl prog ret s (P1 ∗ P2 ∗ (⌜φ⌝ ∗ P3)) Q Qp := by
  intro hcl
  refine SepWPp.weaken_pre (P' := ⌜φ⌝ ∗ (P1 ∗ P2 ∗ P3))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  exact SepWPp.pure_elim fun hφ => h hφ hcl

private theorem shim_vm_ok_at_stateX {pl : Obj.MultiPlacement} {prog : Program}
    {entry : BitVec 64} {s : State}
    (hshim : subroutine_ok prog entry (withLsCl pl session2ShimBudgetSpecX))
    (hcl : LibsignalCodeLoaded pl s.mem) :
    subroutine_ok prog entry
      { pre := fun (_ : Unit) s' =>
          ⌜s'.mem = s.mem⌝ ∗ stackAt s'.sp extHookStack
        post := fun (_ : Unit) s0 sf =>
          ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗ stackAt s0.sp extHookStack } := by
  have h0 := lscall_of_withLsCl hshim hcl
  refine subroutine_ok_mono h0 (fun _ _ s0 hp => ?_) (fun _ _ _ _ hq => ?_)
  · dsimp only [withMemEq, session2ShimBudgetSpecX, sessionShimBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec, Spec.withHookStack] at hp ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hp
  · dsimp only [withMemEq, session2ShimBudgetSpecX, sessionShimBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec, Spec.withHookStack] at hq ⊢
    exact hq

private theorem memcpy_vm_ok_at_stateX {pl : Obj.MultiPlacement} {prog : Program}
    {entry : BitVec 64} {s : State}
    (hmemcpy : subroutine_ok prog entry
      (withLsCl pl (withVmPreserved (sessionMemcpySpec extHookStack))))
    (hcl : LibsignalCodeLoaded pl s.mem) :
    subroutine_ok prog entry
      { pre := fun (dst, src, bs) s' =>
          ⌜s'.mem = s.mem ∧ s'.readReg64 .x0 = dst ∧ s'.readReg64 .x1 = src ∧
            (s'.readReg64 .x2).toNat = bs.length⌝ ∗
          memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s'.sp extHookStack
        post := fun (dst, src, bs) s0 sf =>
          ⌜VmPreserved s0 sf⌝ ∗ (sessionMemcpySpec extHookStack).post (dst, src, bs) s0 sf } := by
  have h0 := lscall_of_withLsCl hmemcpy hcl
  refine subroutine_ok_mono h0 (fun _ _ s0 hp => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [withMemEq, withVmPreserved, sessionMemcpySpec, libcMemcpySpec] at hp ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hm, hrest⟩, hsp⟩
  rw [sepConj_assoc, sepConj_left_comm _ ⌜s0.mem = s.mem⌝, satisfies_pure_sepConj]
  refine ⟨hm, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hrest, hsp⟩

private theorem allocNoOom_ok_at_stateX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsPlaced M A lim H)
    {s : State} (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    subroutine_ok (lsProg_80 H) (lsρ lsRustAllocSym)
      { pre := fun (size, align, st) s' =>
          ⌜s'.mem = s.mem ∧
            (s'.readReg64 .x0).toNat = size ∧ (s'.readReg64 .x1).toNat = align ∧
            RustLayoutOk size align ∧ FitsEvents M lim st (rustAllocEvents size align) ∧
            LsRetAddr624 (s'.readReg64 .lr)⌝ ∗
          A.pool lim st s' ∗ stackAt s'.sp extHookStack
        post := (rustCliAllocNoOomSpecWithStack M A lim false extHookStack).post } := by
  have h0 := hA.allocNoOom_call (callerProg := lsProg_80 H) hcl
  refine subroutine_ok_mono h0 (fun _ _ s0 hp => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [withMemEq, rustCliAllocNoOomSpecWithStack] at hp ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hm, hrest⟩, hsp⟩
  rw [sepConj_assoc, sepConj_left_comm _ ⌜s0.mem = s.mem⌝, satisfies_pure_sepConj]
  refine ⟨hm, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hrest, hsp⟩

private theorem stackAt_chainClone_eq_alloc_rc (sp : BitVec 64) :
    stackAt sp chainCloneStackX =
      memRegion (sp - BitVec.ofNat 64 chainCloneStackX) 208 ∗ stackAt sp extHookStack := by
  have h := stackAt_split_bottom sp extHookStack 208 (by decide)
  rwa [show extHookStack + 208 = chainCloneStackX by decide] at h

/-- Allocation events emitted by Field 5 (`receiver_chains`). -/
def scReceiverChainsEvents (x : SessionCloneGhost) : List AllocEvent :=
  if x.s.state.receiverChains = [] then []
  else rustAllocEvents (104 * x.s.state.receiverChains.length) 8 ++
    (x.G.chains.zip x.s.state.receiverChains).flatMap chainCloneEvents

/-! ## Field 5: `receiver_chains` (`+572 / +336 → +576 / +476`) -/

/-- Copy the 104-byte cloned receiver chain from `sp + 0xf8` to `dst = x28` (`+420 → +476 / +392`),
advancing `A.pool lim st` to the target state. -/
theorem sc_receiverChains_copy_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {st : M.σ} {s0 s : State}
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    (rem : Nat) (src dst off : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 : BitVec 128)
    (sw6 dw6 : BitVec 64) (F : SepProp)
    (hpc : s.pc = (blkPl_80).base + 420#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = off)
    (hx21 : s.readReg64 .x21 = s.sp + 0xf8#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 rem)
    (hx24 : s.readReg64 .x24 = src + 0x68#64)
    (hx28 : s.readReg64 .x28 = dst)
    (hx29 : s.readReg64 .x29 = s.sp + 0x170#64)
    (htr : s.trace = s0.trace)
    (hrem_lt : rem < 2 ^ 63)
    (hnext : ∀ s1 : State,
      s1.pc = (if rem = 0 then (blkPl_80).base + 476#64 else (blkPl_80).base + 392#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x1 = src + 0x68#64 →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = off + 0x68#64 →
      s1.readReg64 .x21 = s.sp + 0xf8#64 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = BitVec.ofNat 64 rem →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x29 = s.sp + 0x170#64 →
      s1.trace = s0.trace →
      s1.calleeSavedVRegs = s.calleeSavedVRegs →
      SepWPpLsCl lsmpl (lsProg_80 H) ret s1
        (A.pool lim st s1 ∗
          chunks104_6QWAt (s.sp + 0xf8#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
          chunks104_6QWAt dst sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s
      (A.pool lim st s ∗
        chunks104_6QWAt (s.sp + 0xf8#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
        chunks104_6QWAt dst dq0 dq1 dq2 dq3 dq4 dq5 dw6 ∗ F)
      Q Qp := by
  intro hcl
  have hpc_rem :
      (if !(BitVec.ofNat 64 rem == 0#64) = true then (blkPl_80).base + 392#64 else (blkPl_80).base + 476#64) =
      (if rem = 0 then (blkPl_80).base + 476#64 else (blkPl_80).base + 392#64) := by
    by_cases hr : rem = 0
    · simp [hr]
    · have hpos : 0 < rem := Nat.pos_of_ne_zero hr
      have hbeq : (BitVec.ofNat 64 rem == 0#64) = false := beq_ofNat_zero_eq_false hpos (by omega)
      simp [hr, hbeq]
  rw [chunks104_6QWAt_sp_0xf8 s.sp sq0 sq1 sq2 sq3 sq4 sq5 sw6] at hnext ⊢
  unfold chunks104_6QWAt at hnext ⊢
  simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hnext ⊢
  apply sepWPp_of_sepWP_lscl_sc hcl
    (mid := if !(BitVec.ofNat 64 rem == 0#64) = true then (blkPl_80).base + 392#64 else (blkPl_80).base + 476#64)
  apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
    (Q := (blkPC_80).rebase (blkPl_80).base (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H))
    blkLib_eq_80
    (mid := if !(BitVec.ofNat 64 rem == 0#64) = true then (blkPl_80).base + 392#64 else (blkPl_80).base + 476#64)
  intro _m_strip
  wp_steps
  apply SepWP.done (by sc_close2) (by sc_close2)
  intro _m_real _hnsp
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by sc_close2))
    (hnext := ?_)
  apply SepWP.done (by sc_close2) (by sc_close2)
  intro hcl1
  exact hnext _
    (by rw [← hpc_rem]; sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
    (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
    (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
    (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2) hcl1

/-- Single budget-threaded iteration of the `receiver_chains` clone loop (`+392 → +476 / +392`). -/
theorem sc_receiverChains_iter_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hcc : ChainCloneLocal1PlacedOkX M A lim H)
    {st : M.σ} {s0 s : State}
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    (g : ChainGhost) (rc : ReceiverChain) (rem : Nat)
    (src dst_base off : BitVec 64)
    (F : SepProp)
    (hfits : FitsEvents M lim st (chainCloneEvents (g, rc)))
    (hqp_false : ∀ sf F', sf.status = .Panicked → Qp sf (⌜False⌝ ∗ F'))
    (hpc : s.pc = (blkPl_80).base + 392#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx1 : s.readReg64 .x1 = src)
    (hx20 : s.readReg64 .x20 = off)
    (hx21 : s.readReg64 .x21 = s.sp + 0xf8#64)
    (hx22 : s.readReg64 .x22 = off + BitVec.ofNat 64 (rem + 1) * 104#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (rem + 1))
    (hx27 : s.readReg64 .x27 = dst_base)
    (hx29 : s.readReg64 .x29 = s.sp + 0x170#64)
    (htr : s.trace = s0.trace)
    (hmul_lt : (rem + 1) * 104 < 2 ^ 63)
    (hnext : ∀ (s1 : State) (g' : ChainGhost),
      lenField 7 (encChainMem (g', rc)) = lenField 7 (encChainMem (g, rc)) →
      s1.pc = (if rem = 0 then (blkPl_80).base + 476#64 else (blkPl_80).base + 392#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x1 = src + 0x68#64 →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = off + 0x68#64 →
      s1.readReg64 .x21 = s.sp + 0xf8#64 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = BitVec.ofNat 64 rem →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = dst_base →
      s1.readReg64 .x29 = s.sp + 0x170#64 →
      s1.trace = s0.trace →
      s1.calleeSavedVRegs = s.calleeSavedVRegs →
      SepWPpLsCl lsmpl (lsProg_80 H) ret s1
        (A.pool lim (M.stepEvents (chainCloneEvents (g, rc)) st) s1 ∗
          chainAt A.repAlloc (g, rc) src ∗
          chainAt A.repAlloc (g', rc) (dst_base + off) ∗
          memRegion (s.sp + 0xf8#64) 104 ∗
          stackAt s.sp chainCloneStackX ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s
      (A.pool lim st s ∗
        chainAt A.repAlloc (g, rc) src ∗
        memRegion (dst_base + off) 104 ∗
        memRegion (s.sp + 0xf8#64) 104 ∗
        stackAt s.sp chainCloneStackX ∗ F)
      Q Qp := by
  have hcall := sc_chainClone_placed_ok_at_x (chainCloneSpecX M A lim) hcc
  clear hcc
  have hfits_env : FitsEnv M lim st (ChainCloneEnv (g, rc)) := by
    intro evs hevs
    dsimp only [ChainCloneEnv] at hevs
    rwa [hevs]
  have hsub_off : off + BitVec.ofNat 64 (rem + 1) * 104#64 - off =
      BitVec.ofNat 64 (rem + 1) * 104#64 := by bv_arith
  have hmul_beq : (BitVec.ofNat 64 (rem + 1) * 104#64 == 0#64) = false :=
    segClone_bv_ofNat_mul_104_beq_zero (Nat.succ_pos rem) hmul_lt
  have hrem_lt : rem < 2 ^ 63 := by omega
  clear hmul_lt
  suffices h_at_call : ∀ sm : State,
      sm.pc = (blkPl_82).base →
      sm.status = .Running → sm.sp = s.sp → sm.spAligned = true →
      sm.readReg64 .x0 = s.sp + 0xf8#64 →
      sm.readReg64 .x1 = src →
      sm.readReg64 .x30 = (blkPl_80).base + 420#64 →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = off →
      sm.readReg64 .x21 = s.sp + 0xf8#64 →
      sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = BitVec.ofNat 64 rem →
      sm.readReg64 .x24 = src + 0x68#64 →
      sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x26 = s.readReg64 .x26 →
      sm.readReg64 .x27 = dst_base →
      sm.readReg64 .x28 = dst_base + off →
      sm.readReg64 .x29 = s.sp + 0x170#64 →
      sm.trace = s0.trace →
      sm.calleeSavedVRegs = s.calleeSavedVRegs →
      SepWPpLsCl lsmpl (lsProg_80 H) ret sm
        ((memRegion (sm.sp + 0xf8#64) 104 ∗ chainAt A.repAlloc (g, rc) src ∗
            A.pool lim st sm ∗ stackAt sm.sp chainCloneStackX) ∗
          (memRegion (dst_base + off) 104 ∗ F))
        Q Qp by
    intro hcl
    apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_82).base)
    wp_steps_sync_pool ((blkPl_82).base)
    refine SepWP.done (by sc_close2) (by sc_close2) fun hcl_call => ?_
    refine SepWPp.weaken_pre ?_
      (h_at_call _ (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
        (by rw [segClone_bv_ofNat_succ_sub_one]; sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) hcl_call)
    simp only [State.sp_setMem, State.sp_setPC, State.sp_setPState, State.sp_writeReg64_gpr, sepConj_assoc]
    exact Entails.of_eq (by sep_ac_rfl)
  intro sm hsm_pc hsm_run hsm_sp hsm_spA hsm_x0 hsm_x1 hsm_lr
    hsm_19 hsm_20 hsm_21 hsm_22 hsm_23 hsm_24 hsm_25 hsm_26 hsm_27 hsm_28 hsm_29 hsm_tr hsm_vregs
  refine SepWPpLsCl.call_noPanic_withLsCodeLoaded (spec := chainCloneSpecX M A lim)
    (x := (⟨sm.sp + 0xf8#64, src, (g, rc)⟩, st))
    hcall hsm_pc hsm_run hsm_spA hsm_lr
    (hspec := rfl)
    ⟨by rw [hsm_sp]; exact hsm_x0, hsm_x1, hfits_env⟩ rfl
    (fun sf hpcf_raw hrunf hspf hcsm => ?_)
    (hqp_false := fun sf hpan => hqp_false sf _ hpan)
  have hpcf : sf.pc = (blkPl_80).base + 420#64 := hpcf_raw
  clear hpcf_raw hcall
  obtain ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29, hcsv⟩ := hcsm
  dsimp only [chainCloneSpecX]
  rw [sepExists_sepConj_left]
  refine SepWPpLsCl.exists_elim fun evs => ?_
  simp only [sepConj_assoc]
  refine SepWPpLsCl.pure_elim fun ⟨htr_sf, hevs⟩ => ?_
  dsimp only [ChainCloneEnv] at hevs
  subst hevs
  rw [sepExists_sepConj_left]
  refine SepWPpLsCl.exists_elim fun g' => ?_
  simp only [sepConj_assoc]
  refine SepWPpLsCl.pure_elim fun ⟨hsrk', hpriv', _⟩ => ?_
  have henc_g' : lenField 7 (encChainMem (g', rc)) = lenField 7 (encChainMem (g, rc)) := by
    simp only [encChainMem, hsrk', hpriv']
  have hsf_sp : sf.sp = s.sp := hspf.trans hsm_sp
  have hsf19 : sf.readReg64 .x19 = s.readReg64 .x19 := hcs19.trans hsm_19
  have hsf20 : sf.readReg64 .x20 = off := hcs20.trans hsm_20
  have hsf21 : sf.readReg64 .x21 = sf.sp + 0xf8#64 := by rw [hcs21, hsf_sp]; exact hsm_21
  have hsf22 : sf.readReg64 .x22 = s.readReg64 .x22 := hcs22.trans hsm_22
  have hsf23 : sf.readReg64 .x23 = BitVec.ofNat 64 rem := hcs23.trans hsm_23
  have hsf24 : sf.readReg64 .x24 = src + 0x68#64 := hcs24.trans hsm_24
  have hsf25 : sf.readReg64 .x25 = s.readReg64 .x25 := hcs25.trans hsm_25
  have hsf26 : sf.readReg64 .x26 = s.readReg64 .x26 := hcs26.trans hsm_26
  have hsf27 : sf.readReg64 .x27 = dst_base := hcs27.trans hsm_27
  have hsf28 : sf.readReg64 .x28 = dst_base + off := hcs28.trans hsm_28
  have hsf29 : sf.readReg64 .x29 = sf.sp + 0x170#64 := by rw [hcs29, hsf_sp]; exact hsm_29
  have hsf_tr : sf.trace = s0.trace := htr_sf.trans hsm_tr
  have hsf_vregs : sf.calleeSavedVRegs = s.calleeSavedVRegs := hcsv.trans hsm_vregs
  have hsf_spA : sf.spAligned = true := by
    unfold State.spAligned at hsp ⊢; rw [hsf_sp]; exact hsp
  rw [← hspf]
  clear hspf hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29 hcsv htr_sf
  refine SepWPpLsCl.weaken_pre
    (sepConj_mono_left (chainAt_entails_chunks104_6QW A.repAlloc (g', rc) (sf.sp + 0xf8#64))) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPpLsCl.exists_elim fun sq0 => SepWPpLsCl.exists_elim fun sq1 =>
    SepWPpLsCl.exists_elim fun sq2 => SepWPpLsCl.exists_elim fun sq3 =>
    SepWPpLsCl.exists_elim fun sq4 => SepWPpLsCl.exists_elim fun sq5 =>
    SepWPpLsCl.exists_elim fun sw6 => ?_
  simp only [sepConj_assoc]
  refine SepWPpLsCl.pure_elim fun hch_inl => ?_
  refine SepWPpLsCl.weaken_pre
    (P' := memRegion (dst_base + off) 104 ∗
            chunks104_6QWAt (sf.sp + 0xf8#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
            chainHeap A.repAlloc (g', rc) ∗ chainAt A.repAlloc (g, rc) src ∗
            A.pool lim (M.stepEvents (chainCloneEvents (g, rc)) st) sf ∗
            stackAt sf.sp chainCloneStackX ∗ F)
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWPpLsCl.weaken_pre
    (sepConj_mono_left (memRegion_104_entails_chunks104_6QWAt (dst_base + off))) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPpLsCl.exists_elim fun dq0 => SepWPpLsCl.exists_elim fun dq1 =>
    SepWPpLsCl.exists_elim fun dq2 => SepWPpLsCl.exists_elim fun dq3 =>
    SepWPpLsCl.exists_elim fun dq4 => SepWPpLsCl.exists_elim fun dq5 =>
    SepWPpLsCl.exists_elim fun dw6 => ?_
  refine SepWPpLsCl.weaken_pre
    (P' := A.pool lim (M.stepEvents (chainCloneEvents (g, rc)) st) sf ∗
            chunks104_6QWAt (sf.sp + 0xf8#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
            chunks104_6QWAt (dst_base + off) dq0 dq1 dq2 dq3 dq4 dq5 dw6 ∗
            (chainHeap A.repAlloc (g', rc) ∗ chainAt A.repAlloc (g, rc) src ∗
              stackAt sf.sp chainCloneStackX ∗ F))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine sc_receiverChains_copy_placed_x rem src (dst_base + off) off
    sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 sw6 dw6 _
    hpcf hrunf hsf_spA hsf20 hsf21 hsf23 hsf24 hsf28 hsf29 hsf_tr hrem_lt
    fun s1 hpc1 hrun1 hsp1 hspA1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx26_1 hx27_1 hx29_1 htr1 hvregs1 => ?_
  rw [hsf_sp] at hx21_1 hx29_1 ⊢
  refine SepWPpLsCl.weaken_pre ?_
    (hnext s1 g' henc_g'
      hpc1 hrun1 (hsp1.trans hsf_sp) hspA1
      hx1_1 (hx19_1.trans hsf19) hx20_1 hx21_1 (hx22_1.trans hsf22)
      hx23_1 (hx25_1.trans hsf25) (hx26_1.trans hsf26) (hx27_1.trans hsf27)
      hx29_1 htr1 (hvregs1.trans hsf_vregs))
  have h104 := chunks104_6QWAt_entails_memRegion (s.sp + 0xf8#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6
  have hdst_chain := chainAt_of_chunks104_6QW A.repAlloc (g', rc) (dst_base + off) hch_inl
  refine Entails.trans
    (Q := chunks104_6QWAt (s.sp + 0xf8#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
          (chunks104_6QWAt (dst_base + off) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗ chainHeap A.repAlloc (g', rc)) ∗
          A.pool lim (M.stepEvents (chainCloneEvents (g, rc)) st) s1 ∗
          chainAt A.repAlloc (g, rc) src ∗ stackAt s.sp chainCloneStackX ∗ F)
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine Entails.trans (sepConj_mono h104 (sepConj_mono_left hdst_chain)) ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-- Induction over `rcs_tl` for the budget-threaded `receiver_chains` clone loop (`+392 → +476`). -/
theorem sc_receiverChains_loop_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hcc : ChainCloneLocal1PlacedOkX M A lim H)
    (s0 : State) (ret : BitVec 64) (Q Qp : State → SepProp → Prop)
    (hqp_false : ∀ sf F', sf.status = .Panicked → Qp sf (⌜False⌝ ∗ F'))
    (dst_base : BitVec 64)
    (rcs_tl : List ReceiverChain) :
    ∀ (s : State) (st : M.σ) (rc : ReceiverChain) (g : ChainGhost) (gs_tl : List ChainGhost)
      (src off : BitVec 64) (F : SepProp),
      FitsEvents M lim st (((g :: gs_tl).zip (rc :: rcs_tl)).flatMap chainCloneEvents) →
      gs_tl.length = rcs_tl.length →
      (rcs_tl.length + 1) * 104 < 2 ^ 63 →
      (rcs_tl.length + 1) * 104 ≤ 2 ^ 64 →
      s.pc = (blkPl_80).base + 392#64 →
      s.status = .Running → s.spAligned = true →
      s.readReg64 .x1 = src → s.readReg64 .x20 = off →
      s.readReg64 .x21 = s.sp + 0xf8#64 →
      s.readReg64 .x22 = off + BitVec.ofNat 64 (rcs_tl.length + 1) * 104#64 →
      s.readReg64 .x23 = BitVec.ofNat 64 (rcs_tl.length + 1) →
      s.readReg64 .x27 = dst_base →
      s.readReg64 .x29 = s.sp + 0x170#64 →
      s.trace = s0.trace →
      (∀ (s1 : State) (gs' : List ChainGhost),
        gs'.length = (rc :: rcs_tl).length →
        ((gs'.zip (rc :: rcs_tl)).map fun gc => lenField 7 (encChainMem gc)) =
          (((g :: gs_tl).zip (rc :: rcs_tl)).map fun gc => lenField 7 (encChainMem gc)) →
        s1.pc = (blkPl_80).base + 476#64 →
        s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
        s1.readReg64 .x19 = s.readReg64 .x19 →
        s1.readReg64 .x21 = s.sp + 0xf8#64 →
        s1.readReg64 .x25 = s.readReg64 .x25 →
        s1.readReg64 .x26 = s.readReg64 .x26 →
        s1.readReg64 .x27 = dst_base →
        s1.readReg64 .x29 = s.sp + 0x170#64 →
        s1.trace = s0.trace →
        s1.calleeSavedVRegs = s.calleeSavedVRegs →
        SepWPpLsCl lsmpl (lsProg_80 H) ret s1
          (A.pool lim (M.stepEvents (((g :: gs_tl).zip (rc :: rcs_tl)).flatMap chainCloneEvents) st) s1 ∗
            arrayAt (chainAt A.repAlloc) 104 src ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
            arrayAt (chainAt A.repAlloc) 104 (dst_base + off) (gs'.zip (rc :: rcs_tl)) ∗
            memRegion (s.sp + 0xf8#64) 104 ∗
            stackAt s.sp chainCloneStackX ∗ F)
          Q Qp) →
      SepWPpLsCl lsmpl (lsProg_80 H) ret s
        (A.pool lim st s ∗
          arrayAt (chainAt A.repAlloc) 104 src ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
          memRegion (dst_base + off) ((rcs_tl.length + 1) * 104) ∗
          memRegion (s.sp + 0xf8#64) 104 ∗
          stackAt s.sp chainCloneStackX ∗ F)
        Q Qp := by
  induction rcs_tl with
  | nil =>
    intro s st rc g gs_tl src off F hfits hgs hmul_lt _ hpc hrun hsp hx1 hx20 hx21 hx22 hx23 hx27 hx29 htr hnext
    cases gs_tl with
    | cons _ _ => simp at hgs
    | nil =>
      simp only [List.zip_cons_cons, List.zip_nil_right, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, arrayAt_cons, arrayAt_nil, sepConj_emp, List.length_nil, Nat.zero_add,
        Nat.one_mul] at *
      refine sc_receiverChains_iter_placed_x hcc g rc 0 src dst_base off F hfits hqp_false
        hpc hrun hsp hx1 hx20 hx21 hx22 hx23 hx27 hx29 htr hmul_lt
        fun s1 g' henc_g' hpc1 hrun1 hsp1 hspA1 _ hx19_1 _ hx21_1 _ _ hx25_1 hx26_1 hx27_1 hx29_1 htr1 hvregs1 => ?_
      simp only [↓reduceIte] at hpc1
      have h1 := hnext s1 [g'] rfl (by simp [henc_g']) hpc1 hrun1 hsp1 hspA1
        hx19_1 hx21_1 hx25_1 hx26_1 hx27_1 hx29_1 htr1 hvregs1
      simpa only [List.zip_cons_cons, List.zip_nil_right, arrayAt_cons, arrayAt_nil, sepConj_emp]
        using h1
  | cons rc2 rcs2 ih =>
    intro s st rc g gs_tl src off F hfits hgs hmul_lt hsz_le hpc hrun hsp hx1 hx20 hx21 hx22 hx23 hx27 hx29 htr hnext
    cases gs_tl with
    | nil => simp at hgs
    | cons g2 gs2 =>
      have hgs2 : gs2.length = rcs2.length := by simpa using hgs
      have hmul2_lt : (rcs2.length + 1) * 104 < 2 ^ 63 := by simp [Nat.add_mul] at hmul_lt; omega
      have hsz2_le : (rcs2.length + 1) * 104 ≤ 2 ^ 64 := by simp [Nat.add_mul] at hsz_le; omega
      simp only [List.zip_cons_cons, List.flatMap_cons] at hfits
      rcases (fitsEvents_append M lim _ _ _).mp hfits with ⟨hfits_hd, hfits_tl⟩
      have hsplit_mr :
          memRegion (dst_base + off) (((rc2 :: rcs2).length + 1) * 104) =
            memRegion (dst_base + off) 104 ∗
              memRegion (dst_base + (off + 0x68#64)) ((rcs2.length + 1) * 104) := by
        refine memRegion_split' (n := 104) (k := (rcs2.length + 1) * 104) ?_
          (by bv_arith) hsz_le
        simp [List.length_cons, Nat.add_mul]; omega
      rw [List.zip_cons_cons, arrayAt_cons, hsplit_mr]
      refine SepWPpLsCl.weaken_pre
        (P' := A.pool lim st s ∗
                chainAt A.repAlloc (g, rc) src ∗
                memRegion (dst_base + off) 104 ∗
                memRegion (s.sp + 0xf8#64) 104 ∗
                stackAt s.sp chainCloneStackX ∗
                (arrayAt (chainAt A.repAlloc) 104 (src + 0x68#64) ((g2 :: gs2).zip (rc2 :: rcs2)) ∗
                  memRegion (dst_base + (off + 0x68#64)) ((rcs2.length + 1) * 104) ∗ F))
        (Entails.of_eq (by sep_ac_rfl)) ?_
      refine sc_receiverChains_iter_placed_x hcc g rc (rcs2.length + 1) src dst_base off _
        hfits_hd hqp_false
        hpc hrun hsp hx1 hx20 hx21 hx22 hx23 hx27 hx29 htr hmul_lt
        fun s1 g' henc_g' hpc1 hrun1 hsp1 hspA1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx26_1 hx27_1 hx29_1 htr1 hvregs1 => ?_
      have hne0 : rcs2.length + 1 ≠ 0 := Nat.succ_ne_zero _
      simp only [hne0, ↓reduceIte] at hpc1
      have hx22_next : s1.readReg64 .x22 =
          (off + 0x68#64) + BitVec.ofNat 64 (rcs2.length + 1) * 104#64 := by
        rw [hx22_1, hx22, List.length_cons]
        exact segClone_off_add_succ_mul_104 off (rcs2.length + 1)
      rw [← hsp1] at hx21_1 hx29_1 ⊢
      refine SepWPpLsCl.weaken_pre
        (P' := A.pool lim (M.stepEvents (chainCloneEvents (g, rc)) st) s1 ∗
                arrayAt (chainAt A.repAlloc) 104 (src + 0x68#64) ((g2 :: gs2).zip (rc2 :: rcs2)) ∗
                memRegion (dst_base + (off + 0x68#64)) ((rcs2.length + 1) * 104) ∗
                memRegion (s1.sp + 0xf8#64) 104 ∗
                stackAt s1.sp chainCloneStackX ∗
                (chainAt A.repAlloc (g, rc) src ∗ chainAt A.repAlloc (g', rc) (dst_base + off) ∗ F))
        (Entails.of_eq (by sep_ac_rfl)) ?_
      refine ih s1 (M.stepEvents (chainCloneEvents (g, rc)) st) rc2 g2 gs2
        (src + 0x68#64) (off + 0x68#64) _
        hfits_tl hgs2 hmul2_lt hsz2_le hpc1 hrun1 hspA1 hx1_1 hx20_1 hx21_1 hx22_next hx23_1 hx27_1 hx29_1 htr1
        fun s2 gs2' hgs2' henc2' hpc2 hrun2 hsp2 hspA2 hx19_2 hx21_2 hx25_2 hx26_2 hx27_2 hx29_2 htr2 hvregs2 => ?_
      rw [hsp1] at hx21_2 hx29_2 ⊢
      have hstep_cons :
          M.stepEvents (((g2 :: gs2).zip (rc2 :: rcs2)).flatMap chainCloneEvents)
            (M.stepEvents (chainCloneEvents (g, rc)) st) =
          M.stepEvents (((g :: g2 :: gs2).zip (rc :: rc2 :: rcs2)).flatMap chainCloneEvents) st := by
        simp only [List.zip_cons_cons, List.flatMap_cons, M.stepEvents_append]
      rw [hstep_cons]
      refine SepWPpLsCl.weaken_pre ?_
        (hnext s2 (g' :: gs2') (by simp [hgs2']) (by simp [henc_g', henc2'])
          hpc2 hrun2 (hsp2.trans hsp1) hspA2
          (hx19_2.trans hx19_1) hx21_2 (hx25_2.trans hx25_1) (hx26_2.trans hx26_1)
          hx27_2 hx29_2 htr2 (hvregs2.trans hvregs1))
      simp only [List.zip_cons_cons, arrayAt_cons]
      have hd_add : dst_base + off + BitVec.ofNat 64 104 = dst_base + (off + 0x68#64) := by
        bv_arith
      rw [hd_add]
      exact Entails.of_eq (by sep_ac_rfl)

/-- Budget-threaded Field 5 (`+572 / +336 → +576 / +476`) on `lsProg_80 H`. -/
theorem sc_receiverChains_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsPlaced M A lim H)
    (hcc : ChainCloneLocal1PlacedOkX M A lim H)
    {x : SessionCloneGhost} {st : M.σ} {s0 s : State}
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    {F : SepProp}
    (hfits : FitsEvents M lim st (scReceiverChainsEvents x))
    (hqp_false : ∀ sf F', sf.status = .Panicked → Qp sf (⌜False⌝ ∗ F'))
    (hpc : s.pc = (if x.s.state.receiverChains = [] then
                     (blkPl_80).base + 572#64
                   else
                     (blkPl_80).base + 336#64))
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx21 : s.readReg64 .x21 = s.sp + 0xf8#64)
    (hx25 : s.readReg64 .x25 = x.src)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.s.state.receiverChains.length)
    (hx29 : s.readReg64 .x29 = s.sp + 0x170#64)
    (htr : s.trace = s0.trace)
    (hchains_len : x.G.chains.length = x.s.state.receiverChains.length)
    (hnext : ∀ (s1 : State) (chainsCap' chainsPtr' : BitVec 64) (chains' : List ChainGhost),
      chains'.length = x.s.state.receiverChains.length →
      chainsCap' = BitVec.ofNat 64 x.s.state.receiverChains.length →
      ((chains'.zip x.s.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)) =
        ((x.G.chains.zip x.s.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)) →
      s1.pc = (if x.s.state.receiverChains = [] then
                 (blkPl_80).base + 576#64
               else
                 (blkPl_80).base + 476#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x21 = s.sp + 0xf8#64 →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = chainsCap' →
      s1.readReg64 .x27 = chainsPtr' →
      s1.readReg64 .x29 = s.sp + 0x170#64 →
      s1.trace = s0.trace →
      s1.calleeSavedVRegs = s.calleeSavedVRegs →
      SepWPpLsCl lsmpl (lsProg_80 H) ret s1
        (A.pool lim (M.stepEvents (scReceiverChainsEvents x) st) s1 ∗
          ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
          vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) x.G.chainsCap x.G.chainsPtr
            (x.G.chains.zip x.s.state.receiverChains) ∗
          vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap' chainsPtr'
            (chains'.zip x.s.state.receiverChains) ∗
          memRegion (s.sp + 0xf8#64) 104 ∗
          stackAt s.sp chainCloneStackX ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s
      (A.pool lim st s ∗
        ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
        vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) x.G.chainsCap x.G.chainsPtr
          (x.G.chains.zip x.s.state.receiverChains) ∗
        memRegion (s.sp + 0xf8#64) 104 ∗
        stackAt s.sp chainCloneStackX ∗ F)
      Q Qp := by
  cases hrc_eq : x.s.state.receiverChains with
  | nil =>
    have hev_nil : scReceiverChainsEvents x = [] := by simp [scReceiverChainsEvents, hrc_eq]
    rw [hev_nil, M.stepEvents_nil] at hnext
    simp only [hrc_eq, ↓reduceIte] at hpc
    intro hcl
    apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_80).base + 576#64)
    wp_steps_sync_pool ((blkPl_80).base + 576#64)
    refine SepWP.done (by sc_close2) (by sc_close2) fun hcl1 => ?_
    refine SepWPp.weaken_pre ?_
      (hnext _ 0#64 8#64 [] (by simp [hrc_eq]) (by simp [hrc_eq]) (by simp [hrc_eq])
        (by simp only [hrc_eq, ↓reduceIte]; sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2) hcl1)
    simp only [hrc_eq, List.zip_nil_right, segClone_vecBuf_chain_nil_eq, sepConj_assoc]
    exact Entails.of_eq (by sep_ac_rfl)
  | cons rc rcs_tl =>
    have hsub := sc_receiverChains_loop_placed_x hcc s0 ret Q Qp hqp_false
    clear hcc
    have hne : x.s.state.receiverChains ≠ [] := by simp [hrc_eq]
    simp only [hne, ↓reduceIte] at hpc hnext
    rw [hrc_eq] at hx26
    cases hgs_eq : x.G.chains with
    | nil => rw [hgs_eq, hrc_eq] at hchains_len; simp at hchains_len
    | cons g gs_tl =>
      have hgs_tl : gs_tl.length = rcs_tl.length := by
        rw [hgs_eq, hrc_eq] at hchains_len; simpa using hchains_len
      have hev_cons : scReceiverChainsEvents x =
          rustAllocEvents ((rc :: rcs_tl).length * 104) 8 ++
            ((g :: gs_tl).zip (rc :: rcs_tl)).flatMap chainCloneEvents := by
        simp [scReceiverChainsEvents, hrc_eq, hgs_eq, Nat.mul_comm]
      rw [hev_cons] at hfits
      rcases (fitsEvents_append M lim _ _ _).mp hfits with ⟨hfits_alloc, hfits_loop⟩
      have hexpose :=
        segClone_vecBuf_expose_arrayAt A.repAlloc (stride := 104) 8 (chainAt A.repAlloc)
          x.G.chainsCap x.G.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl))
      refine SepWPpLsCl.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (hexpose _))) ?_
      refine sepWPpLsCl_pure_3rd_rc fun hmul_lt => ?_
      have hzip_len : ((g :: gs_tl).zip (rc :: rcs_tl)).length = (rc :: rcs_tl).length := by
        simp [hgs_tl]
      rw [hzip_len] at hmul_lt
      have hpos : 0 < (rc :: rcs_tl).length := by simp
      have hpos_mul : 0 < (rc :: rcs_tl).length * 104 := by simp [List.length_cons]
      have hsz_le : (rcs_tl.length + 1) * 104 ≤ 2 ^ 64 := by simp [List.length_cons] at hmul_lt; omega
      have hsz_le63 : (rc :: rcs_tl).length * 104 + 8 ≤ 2 ^ 63 := by
        simp [List.length_cons] at hmul_lt ⊢; omega
      have htoNat_mul : (BitVec.ofNat 64 (rc :: rcs_tl).length * 104#64).toNat =
          (rc :: rcs_tl).length * 104 :=
        segClone_bv_ofNat_mul_104_toNat hmul_lt
      have hpow2 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
      have hlay : RustLayoutOk ((rc :: rcs_tl).length * 104) 8 :=
        ⟨⟨hpos_mul, hpow2, hsz_le63⟩, by decide⟩
      rw [stackAt_chainClone_eq_alloc_rc s.sp]
      intro hcl
      apply sepWPp_of_sepWP_lscl_sc hcl (mid := lsρ lsRustNoAllocShimSym)
      wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
      apply SepWP.done (by rfl) (by sc_close2)
      intro hcl_shim
      have hshim_state := shim_vm_ok_at_stateX (hA.shim (callerProg := lsProg_80 H)) hcl_shim
      apply sepWPp_of_sepWP_lscl_sc hcl_shim (mid := lsρ lsRustAllocSym)
      wp_call hshim_state ()
      refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
      wp_steps_sync_pool (lsρ lsRustAllocSym)
      apply SepWP.done (by rfl) (by sc_close2)
      intro hcl_alloc
      have halloc_state := allocNoOom_ok_at_stateX hA hcl_alloc
      apply sepWPp_of_sepWP_lscl_sc hcl_alloc (mid := (blkPl_80).base + 392#64)
      wp_call halloc_state ((rc :: rcs_tl).length * 104, 8, st)
      clear halloc_state
      have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹_›
      have hoom : ¬ (sf_1.readReg64 (Reg.gpr 0#5) = 0) := hoom64
      wp_steps_sync_pool ((blkPl_80).base + 392#64)
      refine SepWP.done (by sc_close2) (by sc_close2) fun hcl2 => ?_
      have hsf_sp : sf.sp = s.sp := by sc_close2
      have hsf1_sp : sf_1.sp = s.sp := by sc_close2
      have htr_sf1 : sf_1.trace = s0.trace := by
        have htr1 : sf_1.trace = sf.trace := (‹AllocCallPreserved sf sf_1›).2.1
        have htr0 : sf.trace = s.trace := ‹_›
        exact htr1.trans (htr0.trans htr)
      set ptr' := sf_1.readReg64 (Reg.gpr 0#5)
      have hptr_zero : ptr' + 0#64 = ptr' := by bv_arith
      have hsz_eq : (rc :: rcs_tl).length * 104 = (rcs_tl.length + 1) * 104 := rfl
      refine SepWPp.weaken_pre
        (P' := A.pool lim (M.stepEvents (rustAllocEvents ((rc :: rcs_tl).length * 104) 8) st) _ ∗
                arrayAt (chainAt A.repAlloc) 104 x.G.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
                memRegion (ptr' + 0#64) ((rcs_tl.length + 1) * 104) ∗
                memRegion (sf_1.sp + 0xf8#64) 104 ∗
                stackAt sf_1.sp chainCloneStackX ∗
                (A.live ptr' ((rc :: rcs_tl).length * 104) 8 ∗
                  ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
                  segClone_vecBufRest A.repAlloc 104 8 x.G.chainsCap x.G.chainsPtr
                    ((g :: gs_tl).zip (rc :: rcs_tl)) ∗ F))
        (by
          rw [hsf1_sp, hsf_sp, hptr_zero, ← hsz_eq, stackAt_chainClone_eq_alloc_rc s.sp]
          simp only [sepConj_assoc]
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      refine hsub ptr' rcs_tl _ (M.stepEvents (rustAllocEvents ((rc :: rcs_tl).length * 104) 8) st)
        rc g gs_tl x.G.chainsPtr 0#64 _
        hfits_loop hgs_tl (by simpa [List.length_cons] using hmul_lt) hsz_le
        (by sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2)
        (by dsimp only [ptr']; sc_close2)
        (by sc_close2)
        (by simp [wp_norm, arm64_norm, htr_sf1])
        (fun s2 gs' hgs' henc' hpc2 hrun2 hsp2 hspA2 hx19_2 hx21_2 hx25_2 hx26_2 hx27_2 hx29_2 htr2 hvregs2 => ?_)
        hcl2
      clear hsub
      dsimp only [Reg.x19, Reg.x25, Reg.x26] at hx19_2 hx25_2 hx26_2
      simp (config := { decide := true }) only [State.sp_setMem, State.sp_setPC,
        State.sp_writeReg64_gpr, State.readReg64_setMem, State.readReg64_setPC,
        State.readReg64_writeReg64, reduceStateReadReg64] at hsp2 hx19_2 hx21_2 hx25_2 hx26_2 hx29_2
      rw [hsf1_sp] at hsp2 hx21_2 hx29_2
      rw [hptr_zero]
      have hstep_full :
          M.stepEvents (((g :: gs_tl).zip (rc :: rcs_tl)).flatMap chainCloneEvents)
            (M.stepEvents (rustAllocEvents ((rc :: rcs_tl).length * 104) 8) st) =
          M.stepEvents (scReceiverChainsEvents x) st := by
        rw [← M.stepEvents_append, ← hev_cons]
      rw [hstep_full]
      refine SepWPpLsCl.weaken_pre ?_
        (hnext s2 (BitVec.ofNat 64 (rc :: rcs_tl).length) ptr' gs'
          (by rw [hrc_eq]; exact hgs') (by rw [hrc_eq])
          (by rw [hgs_eq, hrc_eq]; exact henc')
          hpc2 hrun2 hsp2 hspA2
          (by rw [hx19_2]; sc_close2) hx21_2 (by rw [hx25_2]; sc_close2)
          (by rw [hx26_2]; sc_close2) hx27_2 hx29_2 htr2
          (by rw [hvregs2]; sc_close2))
      dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64]
      simp only [hgs_eq, hrc_eq, hsf1_sp]
      have hreasm :=
        segClone_vecBuf_reassemble_arrayAt A.repAlloc 104 8 (chainAt A.repAlloc)
          x.G.chainsCap x.G.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl))
      have hnew_len : (gs'.zip (rc :: rcs_tl)).length = (rc :: rcs_tl).length := by
        simp [hgs']
      have hnew_pos : 0 < (gs'.zip (rc :: rcs_tl)).length := by rw [hnew_len]; exact hpos
      have hnew_lt : (gs'.zip (rc :: rcs_tl)).length * 104 < 2 ^ 63 := by rw [hnew_len]; exact hmul_lt
      have hnew_buf := segClone_vecBuf_chain_of_arrayAt A.repAlloc ptr'
        (gs'.zip (rc :: rcs_tl)) hnew_pos hnew_lt hoom64
      rw [hnew_len] at hnew_buf
      refine Entails.trans
        (Q := (arrayAt (chainAt A.repAlloc) 104 x.G.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
                segClone_vecBufRest A.repAlloc 104 8 x.G.chainsCap x.G.chainsPtr
                  ((g :: gs_tl).zip (rc :: rcs_tl))) ∗
              (A.live ptr' ((rc :: rcs_tl).length * 104) 8 ∗
                arrayAt (chainAt A.repAlloc) 104 ptr' (gs'.zip (rc :: rcs_tl))) ∗
              A.pool lim (M.stepEvents (scReceiverChainsEvents x) st) s2 ∗
              ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
              memRegion (s.sp + 0xf8#64) 104 ∗ stackAt s.sp chainCloneStackX ∗ F)
        (Entails.of_eq (by sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono hreasm (sepConj_mono_left hnew_buf)) ?_
      exact Entails.of_eq (by sep_ac_rfl)

/-! ## Field 6: `pending_pre_key` (`+576 / +476 → +592 ∨ +648`) -/

theorem sc_pendingPreKey_200_pos_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsPlaced M A lim H)
    (hmemcpy : subroutine_ok (lsProg_80 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (withVmPreserved (sessionMemcpySpec extHookStack))))
    {x : SessionCloneGhost} {st : M.σ} {s0 s : State}
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    {gp : TailVecGhost} {tw0 tw1 tw3 tw4 : BitVec 32} {td2 : BitVec 64}
    {v18 v20 : BitVec 64} {F : SepProp}
    (htail : gp.tail.length = 48 - 24)
    (htail_eq : ((x.src + 0xf8#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail) =
      (((x.src + 0x110#64) ↦₃₂ tw0) ∗ ((x.src + 0x114#64) ↦₃₂ tw1) ∗
        ((x.src + 0x118#64) ↦₆₄ td2) ∗ ((x.src + 0x120#64) ↦₃₂ tw3) ∗
        ((x.src + 0x124#64) ↦₃₂ tw4)))
    (htail_val : gp.tail = unpack32 tw0 ++ unpack32 tw1 ++ unpack64 td2 ++ unpack32 tw3 ++ unpack32 tw4)
    (hpos : 0 < gp.vec.bytes.length)
    (hlen_le : gp.vec.bytes.length ≤ gp.vec.cap.toNat)
    (hcap_lt : gp.vec.cap.toNat < 2 ^ 63)
    (hptr : gp.vec.ptr ≠ 0)
    (hfits : FitsEvents M lim st (rustAllocEvents gp.vec.bytes.length 1))
    (hpc : s.pc = (blkPl_80).base + 512#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx23 : (s.readReg64 .x23).truncate 32 = tw0)
    (hx24 : (s.readReg64 .x24).truncate 32 = tw1)
    (hx25 : s.readReg64 .x25 = x.src)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 gp.vec.bytes.length)
    (htr : s.trace = s0.trace)
    (hnext : ∀ (s1 : State) (pendCap' pendPtr' v18' : BitVec 64) (w23' w24' v2c' : BitVec 32),
      (s1.pc = (blkPl_80).base + 592#64 ∨
       s1.pc = (blkPl_80).base + 648#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      (s1.readReg64 .x23).truncate 32 = w23' →
      (s1.readReg64 .x24).truncate 32 = w24' →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = pendCap' →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace →
      s1.calleeSavedVRegs = s.calleeSavedVRegs →
      SepWPpLsCl lsmpl (lsProg_80 H) ret s1
        (A.pool lim (M.stepEvents (rustAllocEvents gp.vec.bytes.length 1) st) s1 ∗
          (⌜gp.tail.length = 48 - 24⌝ ∗
            vecGhostAt A.repAlloc gp.vec (x.src + 0xf8#64) ∗
            ((x.src + 0xf8#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail)) ∗
          (⌜pendCap' = BitVec.ofNat 64 gp.vec.bytes.length ∧
              ∃ tw4' : BitVec 32,
                gp.tail = unpack32 w23' ++ unpack32 w24' ++ unpack64 v18' ++ unpack32 v2c' ++ unpack32 tw4'⌝ ∗
            vecU8Buf A.repAlloc pendCap' pendPtr' gp.vec.bytes) ∗
          ((s.sp + 0x18#64) ↦₆₄ v18') ∗ ((s.sp + 0x20#64) ↦₆₄ pendPtr') ∗
          ((s.sp + 0x2c#64) ↦₃₂ v2c') ∗ stackAt s.sp extHookStack ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s
      (A.pool lim st s ∗
        ((x.src + 0xf8#64) ↦₆₄ gp.vec.cap) ∗ ((x.src + 0x100#64) ↦₆₄ gp.vec.ptr) ∗
        ((x.src + 0x108#64) ↦₆₄ BitVec.ofNat 64 gp.vec.bytes.length) ∗ (gp.vec.ptr ↦ₛ gp.vec.bytes) ∗
        A.live gp.vec.ptr gp.vec.cap.toNat 1 ∗
        memRegion (gp.vec.ptr + BitVec.ofNat 64 gp.vec.bytes.length)
          (gp.vec.cap.toNat - gp.vec.bytes.length) ∗
        ((x.src + 0x110#64) ↦₃₂ tw0) ∗ ((x.src + 0x114#64) ↦₃₂ tw1) ∗
        ((x.src + 0x118#64) ↦₆₄ td2) ∗ ((x.src + 0x120#64) ↦₃₂ tw3) ∗
        ((x.src + 0x124#64) ↦₃₂ tw4) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗
        ((s.sp + 0x20#64) ↦₆₄ v20) ∗ ((s.sp + 0x2c#64) ↦₃₂ tw3) ∗
        stackAt s.sp extHookStack ∗ F)
      Q Qp := by
  intro hcl
  have h100 : x.src + 0xf8#64 + 8#64 = x.src + 0x100#64 := by bv_arith
  have h108 : x.src + 0xf8#64 + 16#64 = x.src + 0x108#64 := by bv_arith
  have hlen_lt : gp.vec.bytes.length < 2 ^ 63 := by omega
  have hlen_le63 : gp.vec.bytes.length + 1 ≤ 2 ^ 63 := by omega
  have hlen_le64 : gp.vec.bytes.length ≤ 2 ^ 64 := by omega
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : RustLayoutOk gp.vec.bytes.length 1 := ⟨⟨hpos, hpow2, hlen_le63⟩, by decide⟩
  have htoNat : (BitVec.ofNat 64 gp.vec.bytes.length).toNat = gp.vec.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply sepWPp_of_sepWP_lscl_sc hcl (mid := lsρ lsRustNoAllocShimSym)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  apply SepWP.done (by rfl) (by sc_close2)
  intro hcl_shim
  have hshim_state := shim_vm_ok_at_stateX (hA.shim (callerProg := lsProg_80 H)) hcl_shim
  apply sepWPp_of_sepWP_lscl_sc hcl_shim (mid := lsρ lsRustAllocSym)
  wp_call hshim_state ()
  refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  apply SepWP.done (by rfl) (by sc_close2)
  intro hcl_alloc
  have halloc_state := allocNoOom_ok_at_stateX hA hcl_alloc
  apply sepWPp_of_sepWP_lscl_sc hcl_alloc (mid := lsρ lsMemcpySym)
  wp_call halloc_state (gp.vec.bytes.length, 1, st)
  clear halloc_state
  have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹_›
  have hoom : ¬ (sf_1.readReg64 (Reg.gpr 0#5) = 0) := hoom64
  wp_steps_sync_pool (lsρ lsMemcpySym)
  apply SepWP.done (by rfl) (by sc_close2)
  intro hcl_memcpy
  have hmemcpy_state := memcpy_vm_ok_at_stateX hmemcpy hcl_memcpy
  apply sepWPp_of_sepWP_lscl_sc hcl_memcpy (mid := (blkPl_80).base + 648#64)
  wp_call hmemcpy_state (sf_1.readReg64 (Reg.gpr 0#5), gp.vec.ptr, gp.vec.bytes)
  clear hmemcpy_state
  refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
  wp_steps_sync_pool ((blkPl_80).base + 648#64)
  refine SepWP.done (by sc_close2) (by sc_close2) fun hcl_end => ?_
  have hsp_eq : sf_2.sp = s.sp := by sc_close2
  have hsf1_sp : sf_1.sp = s.sp := by sc_close2
  have htr_sf2 : sf_2.trace = s0.trace := by
    have htr1 : sf_1.trace = sf.trace := (‹AllocCallPreserved sf sf_1›).2.1
    have htr0 : sf.trace = s.trace := ‹_›
    have htr2 : sf_2.trace = sf_1.trace := ‹_›
    exact htr2.trans (htr1.trans (htr0.trans htr))
  refine SepWPp.weaken_pre ?_
    (hnext _ (BitVec.ofNat 64 gp.vec.bytes.length) (sf_1.readReg64 (Reg.gpr 0#5)) td2 tw0 tw1 tw3
      (Or.inr (by sc_close2)) (by sc_close2) (by sc_close2) (by sc_close2)
      (by sc_close2) (by sc_close2) (by sc_close2)
      (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
      (by sc_close2) (by simp [wp_norm, arm64_norm, htr_sf2]) (by sc_close2) hcl_end)
  have h_rfl : (⌜BitVec.ofNat 64 gp.vec.bytes.length = BitVec.ofNat 64 gp.vec.bytes.length ∧
      ∃ tw4' : BitVec 32,
        gp.tail = unpack32 tw0 ++ unpack32 tw1 ++ unpack64 td2 ++ unpack32 tw3 ++ unpack32 tw4'⌝ : SepProp) = emp :=
    segClone_pure_eq_emp ⟨rfl, tw4, htail_val⟩
  have h_pure1 : (⌜gp.tail.length = 48 - 24⌝ : SepProp) = emp :=
    segClone_pure_eq_emp htail
  have h_pure2 : (⌜gp.vec.bytes.length ≤ gp.vec.cap.toNat ∧ gp.vec.cap.toNat < 2 ^ 63 ∧ gp.vec.ptr ≠ 0⌝ : SepProp) = emp :=
    segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
  rw [vecGhostAt_eq_of_pos A.repAlloc gp.vec (x.src + 0xf8#64) hpos, h100, h108,
      htail_eq,
      vecU8Buf_pos_eq A.repAlloc (sf_1.readReg64 (Reg.gpr 0#5)) gp.vec.bytes hpos hlen_lt hoom64,
      h_rfl, h_pure1, h_pure2]
  simp only [sepConj_assoc, hsp_eq, hsf1_sp, emp_sepConj, sepConj_emp]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Budget-threaded Field 6 (`+576 / +476 → +592 ∨ +648`) on `lsProg_80 H`. -/
theorem sc_pendingPreKey_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsPlaced M A lim H)
    (hmemcpy : subroutine_ok (lsProg_80 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (withVmPreserved (sessionMemcpySpec extHookStack))))
    {x : SessionCloneGhost} {st : M.σ} {s0 s : State}
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    {v18 v20 : BitVec 64} {v2c : BitVec 32} {F : SepProp}
    (hfits : FitsEvents M lim st (optTailCloneEvents x.G.pending))
    (hpc : s.pc = (if x.s.state.receiverChains = [] then
                     (blkPl_80).base + 576#64
                   else
                     (blkPl_80).base + 476#64))
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace)
    (hnext : ∀ (s1 : State) (pendCap' pendPtr' v18' : BitVec 64) (w23' w24' v2c' : BitVec 32),
      (s1.pc = (blkPl_80).base + 592#64 ∨
       s1.pc = (blkPl_80).base + 648#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      (s1.readReg64 .x23).truncate 32 = w23' →
      (s1.readReg64 .x24).truncate 32 = w24' →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = pendCap' →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace →
      s1.calleeSavedVRegs = s.calleeSavedVRegs →
      SepWPpLsCl lsmpl (lsProg_80 H) ret s1
        (A.pool lim (M.stepEvents (optTailCloneEvents x.G.pending) st) s1 ∗
          optTailVecAt A.repAlloc 48 (x.src + 0xf8#64) x.G.pending ∗
          ScOptPendClone A.repAlloc x.G.pending pendCap' pendPtr' w23' w24' v18' v2c' ∗
          ((s.sp + 0x18#64) ↦₆₄ v18') ∗ ((s.sp + 0x20#64) ↦₆₄ pendPtr') ∗
          ((s.sp + 0x2c#64) ↦₃₂ v2c') ∗ stackAt s.sp extHookStack ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s
      (A.pool lim st s ∗ optTailVecAt A.repAlloc 48 (x.src + 0xf8#64) x.G.pending ∗
        ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x20#64) ↦₆₄ v20) ∗
        ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ stackAt s.sp extHookStack ∗ F)
      Q Qp := by
  cases hpend : x.G.pending with
  | none =>
    clear hA hmemcpy hfits
    rw [hpend] at hnext
    dsimp only [optTailVecAt, ScOptPendClone, noneCap, optTailCloneEvents] at hnext ⊢
    rw [M.stepEvents_nil] at hnext
    simp only [sepConj_assoc]
    have h_rfl : (⌜(0xffffffffffffffff#64 : BitVec 64) = 0xffffffffffffffff#64⌝ : SepProp) = emp :=
      segClone_pure_eq_emp rfl
    by_cases hrc : x.s.state.receiverChains = []
    · simp only [hrc, ↓reduceIte] at hpc
      intro hcl
      apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_80).base + 592#64)
      wp_steps_sync_pool ((blkPl_80).base + 592#64)
      refine SepWP.done (by sc_close2) (by sc_close2) fun hcl1 => ?_
      refine SepWPp.weaken_pre ?_
        (hnext _ 0xffffffffffffffff#64 v20 v18
          ((s.readReg64 .x23).truncate 32) ((s.readReg64 .x24).truncate 32) v2c
          (Or.inl (by sc_close2)) (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2) (by sc_close2) hcl1)
      rw [h_rfl]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by sep_ac_rfl)
    · simp only [hrc, ↓reduceIte] at hpc
      intro hcl
      apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_80).base + 592#64)
      wp_steps_sync_pool ((blkPl_80).base + 592#64)
      refine SepWP.done (by sc_close2) (by sc_close2) fun hcl1 => ?_
      refine SepWPp.weaken_pre ?_
        (hnext _ 0xffffffffffffffff#64 v20 v18
          ((s.readReg64 .x23).truncate 32) ((s.readReg64 .x24).truncate 32) v2c
          (Or.inl (by sc_close2)) (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2) (by sc_close2) hcl1)
      rw [h_rfl]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by sep_ac_rfl)
  | some gp =>
    rw [hpend] at hfits hnext
    dsimp only [optTailVecAt, ScOptPendClone, optTailCloneEvents] at hfits hnext ⊢
    simp only [sepConj_assoc]
    refine sepWPpLsCl_pure_2nd_rc fun htail => ?_
    obtain ⟨tw0, tw1, td2, tw3, tw4, htail_val, htail_pts⟩ := exists_tail24_decomp htail
    have h100 : x.src + 0xf8#64 + 8#64 = x.src + 0x100#64 := by bv_arith
    have h108 : x.src + 0xf8#64 + 16#64 = x.src + 0x108#64 := by bv_arith
    have h110 : x.src + 0xf8#64 + BitVec.ofNat 64 24 = x.src + 0x110#64 := by bv_arith
    have h114 : x.src + 0x110#64 + 4#64 = x.src + 0x114#64 := by bv_arith
    have h118 : x.src + 0x110#64 + 8#64 = x.src + 0x118#64 := by bv_arith
    have h120 : x.src + 0x110#64 + 16#64 = x.src + 0x120#64 := by bv_arith
    have h124 : x.src + 0x110#64 + 20#64 = x.src + 0x124#64 := by bv_arith
    have htail_eq : ((x.src + 0xf8#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail) =
        (((x.src + 0x110#64) ↦₃₂ tw0) ∗ ((x.src + 0x114#64) ↦₃₂ tw1) ∗
          ((x.src + 0x118#64) ↦₆₄ td2) ∗ ((x.src + 0x120#64) ↦₃₂ tw3) ∗
          ((x.src + 0x124#64) ↦₃₂ tw4)) := by
      rw [h110, htail_pts (x.src + 0x110#64), h114, h118, h120, h124]
    rw [htail_eq]
    rcases eq_nil_or_length_pos gp.vec.bytes with hnil | hpos
    · clear hA hmemcpy hfits
      have hev_nil : LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.vecCloneEvents gp.vec = [] := by
        simp [LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.vecCloneEvents, hnil]
      rw [hev_nil, M.stepEvents_nil] at hnext
      rw [vecGhostAt_eq_of_nil A.repAlloc gp.vec (x.src + 0xf8#64) hnil, h100, h108]
      simp only [sepConj_assoc]
      refine sepWPpLsCl_pure_2nd_rc fun ⟨hcap_lt, hptr⟩ => ?_
      have hcmn : gp.vec.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcmn_beq : (gp.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      have h_rfl : (⌜(0#64 : BitVec 64) = BitVec.ofNat 64 ([] : List (BitVec 8)).length ∧
          ∃ tw4' : BitVec 32,
            gp.tail = unpack32 tw0 ++ unpack32 tw1 ++ unpack64 td2 ++ unpack32 tw3 ++ unpack32 tw4'⌝ : SepProp) = emp :=
        segClone_pure_eq_emp ⟨rfl, tw4, htail_val⟩
      have h_pure1 : (⌜gp.tail.length = 48 - 24⌝ : SepProp) = emp :=
        segClone_pure_eq_emp htail
      have h_pure2 : (⌜gp.vec.cap.toNat < 2 ^ 63 ∧ gp.vec.ptr ≠ 0⌝ : SepProp) = emp :=
        segClone_pure_eq_emp ⟨hcap_lt, hptr⟩
      by_cases hrc : x.s.state.receiverChains = []
      · simp only [hrc, ↓reduceIte] at hpc
        intro hcl
        apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_80).base + 648#64)
        wp_steps_sync_pool ((blkPl_80).base + 648#64)
        refine SepWP.done (by sc_close2) (by sc_close2) fun hcl1 => ?_
        refine SepWPp.weaken_pre ?_
          (hnext _ 0#64 1#64 td2 tw0 tw1 tw3
            (Or.inr (by sc_close2)) (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2) hcl1)
        rw [vecGhostAt_eq_of_nil A.repAlloc gp.vec (x.src + 0xf8#64) hnil, h100, h108,
            htail_eq, hnil, vecU8Buf_nil_eq A.repAlloc, h_rfl, h_pure1, h_pure2]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by sep_ac_rfl)
      · simp only [hrc, ↓reduceIte] at hpc
        intro hcl
        apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_80).base + 648#64)
        wp_steps_sync_pool ((blkPl_80).base + 648#64)
        refine SepWP.done (by sc_close2) (by sc_close2) fun hcl1 => ?_
        refine SepWPp.weaken_pre ?_
          (hnext _ 0#64 1#64 td2 tw0 tw1 tw3
            (Or.inr (by sc_close2)) (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2) hcl1)
        rw [vecGhostAt_eq_of_nil A.repAlloc gp.vec (x.src + 0xf8#64) hnil, h100, h108,
            htail_eq, hnil, vecU8Buf_nil_eq A.repAlloc, h_rfl, h_pure1, h_pure2]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by sep_ac_rfl)
    · have hev_pos : LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.vecCloneEvents gp.vec =
          rustAllocEvents gp.vec.bytes.length 1 := by
        simp [LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.vecCloneEvents, Nat.ne_of_gt hpos]
      rw [hev_pos] at hfits hnext
      rw [vecGhostAt_eq_of_pos A.repAlloc gp.vec (x.src + 0xf8#64) hpos, h100, h108]
      simp only [sepConj_assoc]
      refine sepWPpLsCl_pure_2nd_rc fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
      have hcmn : gp.vec.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcmn_beq : (gp.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      have hlen_lt : gp.vec.bytes.length < 2 ^ 63 := by omega
      have hlen_ne : BitVec.ofNat 64 gp.vec.bytes.length ≠ 0#64 :=
        ofNat_ne_zero_of_pos hpos (by omega)
      have hlen_beq : (BitVec.ofNat 64 gp.vec.bytes.length == 0#64) = false :=
        beq_ofNat_zero_eq_false hpos (by omega)
      have hsub := fun (s_200 : State) =>
        sc_pendingPreKey_200_pos_placed_x hA hmemcpy (x := x) (st := st) (s0 := s0) (s := s_200)
          (ret := ret) (Q := Q) (Qp := Qp)
          (gp := gp) (tw0 := tw0) (tw1 := tw1) (tw3 := tw3) (tw4 := tw4) (td2 := td2)
          (v18 := v18) (v20 := v20) (F := F)
          htail htail_eq htail_val hpos hlen_le hcap_lt hptr hfits
      clear hA hmemcpy
      suffices h_at_200 : ∀ s_200 : State,
          s_200.pc = (blkPl_80).base + 512#64 →
          s_200.status = .Running → s_200.sp = s.sp → s_200.spAligned = true →
          s_200.readReg64 .x19 = s.readReg64 .x19 →
          (s_200.readReg64 .x23).truncate 32 = tw0 →
          (s_200.readReg64 .x24).truncate 32 = tw1 →
          s_200.readReg64 .x25 = x.src →
          s_200.readReg64 .x26 = s.readReg64 .x26 →
          s_200.readReg64 .x27 = s.readReg64 .x27 →
          s_200.readReg64 .x28 = BitVec.ofNat 64 gp.vec.bytes.length →
          s_200.readReg64 .x29 = s.readReg64 .x29 →
          s_200.trace = s0.trace →
          s_200.calleeSavedVRegs = s.calleeSavedVRegs →
          SepWPpLsCl lsmpl (lsProg_80 H) ret s_200
            (A.pool lim st s_200 ∗
              ((x.src + 0xf8#64) ↦₆₄ gp.vec.cap) ∗ ((x.src + 0x100#64) ↦₆₄ gp.vec.ptr) ∗
              ((x.src + 0x108#64) ↦₆₄ BitVec.ofNat 64 gp.vec.bytes.length) ∗
              (gp.vec.ptr ↦ₛ gp.vec.bytes) ∗ A.live gp.vec.ptr gp.vec.cap.toNat 1 ∗
              memRegion (gp.vec.ptr + BitVec.ofNat 64 gp.vec.bytes.length)
                (gp.vec.cap.toNat - gp.vec.bytes.length) ∗
              ((x.src + 0x110#64) ↦₃₂ tw0) ∗ ((x.src + 0x114#64) ↦₃₂ tw1) ∗
              ((x.src + 0x118#64) ↦₆₄ td2) ∗ ((x.src + 0x120#64) ↦₃₂ tw3) ∗
              ((x.src + 0x124#64) ↦₃₂ tw4) ∗ ((s_200.sp + 0x18#64) ↦₆₄ v18) ∗
              ((s_200.sp + 0x20#64) ↦₆₄ v20) ∗ ((s_200.sp + 0x2c#64) ↦₃₂ tw3) ∗
              stackAt s_200.sp extHookStack ∗ F)
            Q Qp by
        clear hsub
        by_cases hrc : x.s.state.receiverChains = []
        · simp only [hrc, ↓reduceIte] at hpc
          intro hcl
          apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_80).base + 512#64)
          wp_steps_sync_pool ((blkPl_80).base + 512#64)
          refine SepWP.done (by sc_close2) (by sc_close2) fun hcl1 => ?_
          exact h_at_200 _ (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2) hcl1
        · simp only [hrc, ↓reduceIte] at hpc
          intro hcl
          apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_80).base + 512#64)
          wp_steps_sync_pool ((blkPl_80).base + 512#64)
          refine SepWP.done (by sc_close2) (by sc_close2) fun hcl1 => ?_
          exact h_at_200 _ (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2) hcl1
      intro s_200 hpc200 hrun200 hsp200 hspA200 hx19_200 hx23_200 hx24_200 hx25_200 hx26_200 hx27_200 hx28_200 hx29_200 htr200 hvregs200
      refine hsub s_200 hpc200 hrun200 hspA200 hx23_200 hx24_200 hx25_200 hx28_200 htr200
        fun s1 pendCap' pendPtr' v18' w23' w24' v2c' hpc1 hrun1 hsp1 hspA1 hx19_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 htr1 hvregs1 => ?_
      clear hsub
      rw [hsp200]
      exact hnext s1 pendCap' pendPtr' v18' w23' w24' v2c'
        hpc1 hrun1 (hsp1.trans hsp200) hspA1
        (hx19_1.trans hx19_200) hx23_1 hx24_1 hx25_1
        (hx26_1.trans hx26_200) (hx27_1.trans hx27_200) hx28_1 (hx29_1.trans hx29_200)
        htr1 (hvregs1.trans hvregs200)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ReceiverChainsPendingPreKeyXPlacedBudget
