/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysBasePlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFrontPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologue
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Step & Loop Helpers for Placed Segment 2 (Block `518`)

Representation decompositions, Block `524 → 518` `Chain::clone` bridge, `VmPreserved` basic-block
steps (`+0x19b0 .. +0x1a5c`), and budget-threaded `__rust_alloc` / loop theorems
(`rc_alloc_call_placed_budget_ok`, `rc_iter_placed_budget_ok`, `rc_loop_placed_budget_ok`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (PublicKey ReceiverChain SessionState)
open CryptoVerification (LibsignalPlacement ls_subroutine_ok_of_block lsmpl lsρ subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1 (call_lscl_nopanic_placed call_raw_nopanic_placed lsAllocSym lsShimSym)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkLib_eq_518 blkPl_518 lsProg_518)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt vecGhostAt)
open CryptoVerification.LibsignalTripleRatchet (sessionShimSpec)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (ChainCloneGhost chainCloneStack)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (chainAt_entails_chunks104_6QW chainAt_of_chunks104_6QW chainHeap chunks104_6QWAt)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps (chunks104_6QWAt_entails_memRegion memRegion_104_entails_chunks104_6QWAt ofNat_ne_zero_of_pos pointsTo128_eq_pointsTo64 segClone_bv_ofNat_mul_104_beq_zero segClone_bv_ofNat_succ_sub_one segClone_off_add_succ_mul_104)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost optSenderChainAt optTailVecAt sessionStateAt)
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt vecAt vecBuf vecHeader vecU8At)

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneChainsPlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
  VmPreserved fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec
  subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget (
  ChainClone3OkPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFrontPlacedBudgetAux (
  bind_sepWP_vm_pool_placed sepWPp_done_any sepWPp_exists_elim_any sepWPp_pure_elim_any
  sepWPp_weaken_pre_any
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget (
  blkLib_518_noSvc0
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (
  LsRetAddr624 lsRetAddr624_blockPlacement_base_add
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (
  ChainCloneEnv chainCloneEvents chainCloneSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

/-! ## 1. Representation Decompositions & Block `524 → 518` Callee Bridge -/

def m3a2SessionStatePure (G : SessionGhost) (st : SessionState (List (BitVec 8))) : Prop :=
  PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧
    G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧
    (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)

def m3a2SessionStateRestAt' (A : RustAlloc) (coroPtr : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  vecGhostAt A G.localIk (coroPtr + 0xf8#64) ∗
    vecGhostAt A G.remoteIk (coroPtr + 0x110#64) ∗
    vecU8At A (coroPtr + 0x128#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
    vecGhostAt A G.alice (coroPtr + 0x158#64) ∗
    vecU8At A (coroPtr + 0x170#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
    optSenderChainAt A (coroPtr + 0x188#64) G.sender st.senderChain ∗
    optTailVecAt A 48 (coroPtr + 0x1f0#64) G.pending ∗
    optTailVecAt A 32 (coroPtr + 0x220#64) G.kyber ∗
    ((coroPtr + 0x240#64) ↦₃₂ st.sessionVersion) ∗
    ((coroPtr + 0x244#64) ↦₃₂ st.previousCounter) ∗
    ((coroPtr + 0x248#64) ↦ₛ G.regIds)

theorem sessionStateAt_coro_placed_eq (A : RustAlloc) (coroPtr : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A (coroPtr + 0xf8#64) G st =
      ⌜m3a2SessionStatePure G st⌝ ∗
        ((coroPtr + 0x140#64) ↦₆₄ G.chainsCap) ∗
        ((coroPtr + 0x148#64) ↦₆₄ G.chainsPtr) ∗
        ((coroPtr + 0x150#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip st.receiverChains).length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
        m3a2SessionStateRestAt' A coroPtr G st := by
  unfold sessionStateAt vecAt vecHeader m3a2SessionStatePure m3a2SessionStateRestAt'
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  ac_rfl

theorem chunks104_6QWAt_sp_0x3e0_placed (sp : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    chunks104_6QWAt (sp + 0x3e0#64) q0 q1 q2 q3 q4 q5 w6 =
      ((sp + 0x3e0#64) ↦₆₄ q0.extractLsb' 0 64) ∗
        ((sp + 0x3e8#64) ↦₆₄ q0.extractLsb' 64 64) ∗
        ((sp + 0x3f0#64) ↦₆₄ q1.extractLsb' 0 64) ∗
        ((sp + 0x3f8#64) ↦₆₄ q1.extractLsb' 64 64) ∗
        ((sp + 0x400#64) ↦₆₄ q2.extractLsb' 0 64) ∗
        ((sp + 0x408#64) ↦₆₄ q2.extractLsb' 64 64) ∗
        ((sp + 0x410#64) ↦₆₄ q3.extractLsb' 0 64) ∗
        ((sp + 0x418#64) ↦₆₄ q3.extractLsb' 64 64) ∗
        ((sp + 0x420#64) ↦₆₄ q4.extractLsb' 0 64) ∗
        ((sp + 0x428#64) ↦₆₄ q4.extractLsb' 64 64) ∗
        ((sp + 0x430#64) ↦₆₄ q5.extractLsb' 0 64) ∗
        ((sp + 0x438#64) ↦₆₄ q5.extractLsb' 64 64) ∗
        ((sp + 0x440#64) ↦₆₄ w6) := by
  unfold chunks104_6QWAt
  simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem chainClone3_at_518_budget [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hcc : ChainClone3OkPlaced A lim ext) :
    subroutine_ok (lsProg_518 ext) (lsmpl.base 524)
      (withLsCodeLoaded lsmpl (chainCloneSpec M A lim)) :=
  ls_subroutine_ok_of_block (callerProg := lsProg_518 ext)
    (subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl) hcc) (by decide)

/-! ## 2. `VmPreserved` Step Helpers on Block `518` (`+0x19b0 .. +0x1a5c`) -/

set_option maxHeartbeats 400000 in
theorem rc_prebranch_placed_wp_vm [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr rcsLen newLocIdPtr remIdLen newRemIdPtr u_60 u_68 u_70 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x19b0#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx23 : s.readReg64 .x23 = newLocIdPtr)
    (hx24 : s.readReg64 .x24 = remIdLen)
    (hx25 : s.readReg64 .x25 = newRemIdPtr) :
    SepWP (lsProg_518 ext)
      (if (rcsLen == 0#64) = true then
         (blkPl_518).base + 0x1a58#64
       else
         (blkPl_518).base + 0x19c4#64)
      s
      (((coroPtr + 0x150#64) ↦₆₄ rcsLen) ∗
        ((s.sp + 0x60#64) ↦₆₄ u_60) ∗
        ((s.sp + 0x68#64) ↦₆₄ u_68) ∗
        ((s.sp + 0x70#64) ↦₆₄ u_70) ∗
        ((s.sp + 0x98#64) ↦₆₄ 32#64))
      (fun s1 P_f =>
        VmPreserved s s1 ∧
        (P_f ⊢
          ((coroPtr + 0x150#64) ↦₆₄ rcsLen) ∗
          ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗
          ((s.sp + 0x68#64) ↦₆₄ remIdLen) ∗
          ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗
          ((s.sp + 0x98#64) ↦₆₄ 32#64)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x23 = rcsLen ∧
        s1.readReg64 .x25 = newRemIdPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 32#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx23' : s.readReg64 (Reg.gpr 23#5) = newLocIdPtr := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = remIdLen := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = newRemIdPtr := hx25
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨by simp_all [arm64_norm], Entails.of_eq (by sep_ac_rfl), rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
theorem rc_empty_placed_wp_vm [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State)
    (hpc : s.pc = (blkPl_518).base + 0x1a58#64)
    (hrun : s.status = .Running) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1a5c#64) s emp
      (fun s1 P_f =>
        VmPreserved s s1 ∧
        (P_f ⊢ emp) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = 8#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨by simp_all [arm64_norm], Entails.refl _, rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
theorem rc_alloc_prep_placed_wp_vm [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hshim_raw : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) sessionShimBudgetSpec)
    (s : State) (coroPtr chainsPtr rcsLen : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x19c4#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx23 : s.readReg64 .x23 = rcsLen) :
    SepWP (lsProg_518 ext) (lsρ lsAllocSym) s
      ((coroPtr + 0x148#64) ↦₆₄ chainsPtr)
      (fun s1 P_f =>
        VmPreserved s s1 ∧
        (P_f ⊢ (coroPtr + 0x148#64) ↦₆₄ chainsPtr) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = rcsLen * 104#64 ∧
        s1.readReg64 .x1 = 8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = rcsLen * 104#64 ∧
        s1.readReg64 .x23 = rcsLen ∧
        s1.readReg64 .x24 = chainsPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x19e0#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hshim := hshim_raw
  dsimp only [sessionShimBudgetSpec, sessionShimSpec] at hshim
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx23' : s.readReg64 (Reg.gpr 23#5) = rcsLen := hx23
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException ext)) blkLib_eq_518 blkLib_518_noSvc0
    (mid := lsρ lsShimSym)
  intro m_strip
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun m_real hnsp => ?_
  have hvmp0 : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  simp only [State.setMem_setMem] at hvmp0 ⊢
  wp_call hshim ()
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp only [arm64_norm]; exact hvmp0.trans (by assumption),
    Entails.of_eq (by sep_ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
theorem rc_alloc_prehdr_placed_wp_vm [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (ptr' rcsLen chainsPtr : BitVec 64)
    (hptr : ptr' ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x19e0#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ptr')
    (hx23 : s.readReg64 .x23 = rcsLen)
    (hx24 : s.readReg64 .x24 = chainsPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x19fc#64) s emp
      (fun s1 P_f =>
        VmPreserved s s1 ∧
        (P_f ⊢ emp) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x1 = chainsPtr ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x20 = rcsLen ∧
        s1.readReg64 .x21 = 0#64 ∧
        s1.readReg64 .x22 = rcsLen * 104#64 ∧
        s1.readReg64 .x23 = rcsLen ∧
        s1.readReg64 .x25 = ptr' ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hptr_beq : (ptr' == 0#64) = false := beq_eq_false_iff_ne.mpr hptr
  have hx0' : s.readReg64 (Reg.gpr 0#5) = ptr' := hx0
  have hx23' : s.readReg64 (Reg.gpr 23#5) = rcsLen := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = chainsPtr := hx24
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨by simp_all [arm64_norm], Entails.refl _, rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
theorem rc_loop_head_placed_wp_vm [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (rem : Nat) (src dst_base off : BitVec 64)
    (hmul_lt : (rem + 1) * 104 < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x19fc#64)
    (hrun : s.status = .Running)
    (hx1 : s.readReg64 .x1 = src)
    (hx21 : s.readReg64 .x21 = off)
    (hx22 : s.readReg64 .x22 = off + BitVec.ofNat 64 (rem + 1) * 104#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (rem + 1))
    (hx25 : s.readReg64 .x25 = dst_base) :
    SepWP (lsProg_518 ext) (lsmpl.base 524) s emp
      (fun s1 P_f =>
        VmPreserved s s1 ∧
        (P_f ⊢ emp) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x1 = src ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = off ∧
        s1.readReg64 .x22 = off + BitVec.ofNat 64 (rem + 1) * 104#64 ∧
        s1.readReg64 .x23 = BitVec.ofNat 64 rem ∧
        s1.readReg64 .x24 = src + 0x68#64 ∧
        s1.readReg64 .x25 = dst_base ∧
        s1.readReg64 .x26 = dst_base + off ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x1a18#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsub_eq : (off + BitVec.ofNat 64 (rem + 1) * 104#64) - off =
      BitVec.ofNat 64 (rem + 1) * 104#64 := by bv_arith
  have hmul_beq : (BitVec.ofNat 64 (rem + 1) * 104#64 == 0#64) = false :=
    segClone_bv_ofNat_mul_104_beq_zero (Nat.succ_pos rem) hmul_lt
  have hx1' : s.readReg64 (Reg.gpr 1#5) = src := hx1
  have hx21' : s.readReg64 (Reg.gpr 21#5) = off := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = off + BitVec.ofNat 64 (rem + 1) * 104#64 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 (rem + 1) := hx23
  have hx25' : s.readReg64 (Reg.gpr 25#5) = dst_base := hx25
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨by simp_all [arm64_norm], Entails.refl _, rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by rw [← segClone_bv_ofNat_succ_sub_one rem]; simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
theorem rc_copy_placed_wp_vm [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (rem : Nat) (nextSrc dst off : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 : BitVec 128)
    (sw6 dw6 : BitVec 64)
    (hrem_lt : rem < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x1a18#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx21 : s.readReg64 .x21 = off)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 rem)
    (hx24 : s.readReg64 .x24 = nextSrc)
    (hx26 : s.readReg64 .x26 = dst)
    (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) :
    SepWP (lsProg_518 ext)
      (if rem = 0 then
         (blkPl_518).base + 0x1a4c#64
       else
         (blkPl_518).base + 0x19fc#64)
      s
      (chunks104_6QWAt (s.sp + 0x3e0#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
        chunks104_6QWAt dst dq0 dq1 dq2 dq3 dq4 dq5 dw6)
      (fun s1 P_f =>
        VmPreserved s s1 ∧
        (P_f ⊢
          chunks104_6QWAt (s.sp + 0x3e0#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
            chunks104_6QWAt dst sq0 sq1 sq2 sq3 sq4 sq5 sw6) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x1 = nextSrc ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = off + 0x68#64 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = BitVec.ofNat 64 rem ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.sp + 0x370#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hpc_rem :
      (if !(BitVec.ofNat 64 rem == 0#64) = true then (blkPl_518).base + 0x19fc#64 else (blkPl_518).base + 0x1a4c#64) =
      (if rem = 0 then (blkPl_518).base + 0x1a4c#64 else (blkPl_518).base + 0x19fc#64) := by
    rcases Nat.eq_zero_or_pos rem with rfl | hpos
    · simp
    · have hne : rem ≠ 0 := Nat.ne_of_gt hpos
      have hne0 : BitVec.ofNat 64 rem ≠ 0#64 := ofNat_ne_zero_of_pos hpos (by omega)
      have hbeq : (BitVec.ofNat 64 rem == 0#64) = false := beq_false_of_ne hne0
      simp [hne, hbeq]
  rw [chunks104_6QWAt_sp_0x3e0_placed s.sp sq0 sq1 sq2 sq3 sq4 sq5 sw6]
  unfold chunks104_6QWAt
  simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have hx21' : s.readReg64 (Reg.gpr 21#5) = off := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 rem := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = nextSrc := hx24
  have hx26' : s.readReg64 (Reg.gpr 26#5) = dst := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = s.sp + 0x370#64 := hx27
  by_vm_steps
    wp_steps
    refine SepWP.done (by rw [← hpc_rem]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    have htrunc128 : ∀ x : BitVec 128, BitVec.extractLsb' 0 64 x = BitVec.truncate 64 x :=
      fun _ => rfl
    refine ⟨by simp_all [arm64_norm],
      Entails.of_eq (by simp only [htrunc128]), rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
theorem rc_epilogue_placed_wp_vm [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State)
    (hpc : s.pc = (blkPl_518).base + 0x1a4c#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1a5c#64) s
      ((s.sp + 0x98#64) ↦₆₄ 32#64)
      (fun s1 P_f =>
        VmPreserved s s1 ∧
        (P_f ⊢ (s.sp + 0x98#64) ↦₆₄ 32#64) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x23 = s.readReg64 .x20 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 32#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨by simp_all [arm64_norm], Entails.of_eq (by sep_ac_rfl), rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm]⟩

/-! ## 3. Budget-Threaded `__rust_alloc(sz, 8)` & Receiver-Chain Loop (`+0x19fc → +0x1a4c`) -/

set_option maxHeartbeats 400000 in
theorem rc_alloc_call_placed_budget_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (s : State) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_le63 : sz + 8 ≤ 2 ^ 63)
    (hfits : FitsEvents M lim stB (rustAllocEvents sz 8))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = lsρ lsAllocSym)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx0_nat : (s.readReg64 .x0).toNat = sz)
    (hx1 : s.readReg64 .x1 = 8#64)
    (hlr : s.readReg64 .x30 = (blkPl_518).base + 0x19e0#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x19e0#64) s
      ((A.pool lim stB s ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢
          (A.live (s2.readReg64 .x0) sz 8 ∗ memRegion (s2.readReg64 .x0) sz ∗
           A.pool lim (M.stepEvents (rustAllocEvents sz 8) stB) s2 ∗
           stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ LibsignalCodeRoLoaded lsmpl s2.mem)
      Qp := by
  have halloc_no := subroutine_ok_allocNoOom_of_budget halloc
  have hlay : RustLayoutOk sz 8 := ⟨⟨hsz_pos, ⟨3, rfl⟩, hsz_le63⟩, by decide⟩
  have hφ : (s.readReg64 .x0).toNat = sz ∧ (s.readReg64 .x1).toNat = 8 ∧
      RustLayoutOk sz 8 ∧ FitsEvents M lim stB (rustAllocEvents sz 8) ∧
      LsRetAddr624 (s.readReg64 .lr) :=
    ⟨hx0_nat, by rw [hx1]; rfl, hlay, hfits,
     by rw [show s.readReg64 .lr = (blkPl_518).base + 0x19e0#64 from hlr]
        exact lsRetAddr624_blockPlacement_base_add 518 0x19e0#64 (by decide) (by decide)⟩
  refine call_raw_nopanic_placed (spec := rustCliAllocNoOomSpec M A lim false)
    (x := (sz, 8, stB))
    (T := A.pool lim stB s ∗ stackAt s.sp allocHookStack) (F := F)
    hcro halloc_no hpc hrun hsp_align hlr
    (by dsimp only [rustCliAllocNoOomSpec])
    hφ (by simp only [emp_sepConj, sepConj_assoc])
    (hnext := fun s2 hpc2 hrun2 hsp2 _ hcs2 hcro2 => ?_)
  dsimp only [rustCliAllocNoOomSpec]
  simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
  refine sepWPp_pure_elim_any fun ⟨hacp, hnz, _⟩ => ?_
  exact sepWPp_done_any hpc2 hrun2
    ⟨Entails.of_eq (by sep_ac_rfl), hnz, hsp2, hacp.2.1, hcs2, hcro2⟩

set_option maxHeartbeats 400000 in
theorem rc_iter_placed_budget_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hcc : ChainClone3OkPlaced A lim ext)
    (s0 s : State) (ret : BitVec 64) (Q : State → SepProp → Prop)
    (g : ChainGhost) (rc : ReceiverChain) (rem : Nat)
    (coroPtr totalLen src dst_base off fp : BitVec 64) (F : SepProp)
    (hmul_lt : (rem + 1) * 104 < 2 ^ 63)
    (hfits : FitsEvents M lim stB (chainCloneEvents (g, rc)))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x19fc#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = src)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = totalLen)
    (hx21 : s.readReg64 .x21 = off)
    (hx22 : s.readReg64 .x22 = off + BitVec.ofNat 64 (rem + 1) * 104#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (rem + 1))
    (hx25 : s.readReg64 .x25 = dst_base)
    (hx27 : s.readReg64 .x27 = s.sp + 0x370#64)
    (hx29 : s.readReg64 .x29 = fp)
    (hnext : ∀ (s1 : State) (g' : ChainGhost),
      s1.pc = (if rem = 0 then (blkPl_518).base + 0x1a4c#64
               else (blkPl_518).base + 0x19fc#64) →
      s1.status = .Running →
      LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.trace = s0.trace →
      s1.readReg64 .x1 = src + 0x68#64 →
      s1.readReg64 .x19 = coroPtr →
      s1.readReg64 .x20 = totalLen →
      s1.readReg64 .x21 = off + 0x68#64 →
      s1.readReg64 .x22 = off + BitVec.ofNat 64 (rem + 1) * 104#64 →
      s1.readReg64 .x23 = BitVec.ofNat 64 rem →
      s1.readReg64 .x25 = dst_base →
      s1.readReg64 .x27 = s.sp + 0x370#64 →
      s1.readReg64 .x29 = fp →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      SepWPp (lsProg_518 ext) ret s1
        (A.pool lim (M.stepEvents (chainCloneEvents (g, rc)) stB) s1 ∗
          chainAt A.repAlloc (g, rc) src ∗
          chainAt A.repAlloc (g', rc) (dst_base + off) ∗
          memRegion (s.sp + 0x3e0#64) 104 ∗
          stackAt s.sp chainCloneStack ∗
          F)
        Q Qp) :
    SepWPp (lsProg_518 ext) ret s
      (A.pool lim stB s ∗
        chainAt A.repAlloc (g, rc) src ∗
        memRegion (dst_base + off) 104 ∗
        memRegion (s.sp + 0x3e0#64) 104 ∗
        stackAt s.sp chainCloneStack ∗
        F)
      Q Qp := by
  have hrem_lt : rem < 2 ^ 63 := by omega
  have hfits_env : FitsEnv M lim stB (ChainCloneEnv (g, rc)) :=
    fun _ hevs => hevs ▸ hfits
  have hhead := rc_loop_head_placed_wp_vm ext s rem src dst_base off hmul_lt
    hpc hrun hx1 hx21 hx22 hx23 hx25
  refine bind_sepWP_vm_pool_placed (A := A) (lim := lim) (st := stB) hcro hhead
    (by simp only [emp_sepConj]; sep_focus)
    fun s1 hpc1 hrun1 hcro1 _ hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hx22_1,
    hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx29_1, hx30_1, hvregs1⟩
  rw [emp_sepConj]
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp
  have htr1_0 : s1.trace = s0.trace := htr1.trans htr
  refine call_lscl_nopanic_placed
    (spec := chainCloneSpec M A lim)
    (x := ((⟨s.sp + 0x3e0#64, src, (g, rc)⟩ : ChainCloneGhost), stB))
    (φ := s1.readReg64 .x0 = s.sp + 0x3e0#64 ∧ s1.readReg64 .x1 = src ∧
      FitsEnv M lim stB (ChainCloneEnv (g, rc)))
    (T := memRegion (s.sp + 0x3e0#64) 104 ∗ chainAt A.repAlloc (g, rc) src ∗
            A.pool lim stB s1 ∗ stackAt s1.sp chainCloneStack)
    (F := memRegion (dst_base + off) 104 ∗ F)
    hcro1 (chainClone3_at_518_budget ext hcc) hpc1 hrun1 hsp1_al hx30_1
    rfl ⟨hx0_1, hx1_1, hfits_env⟩ (by rw [hsp1]; sep_focus)
    (hnext := fun sf hpcf hrunf hspf hsp_alf hcsf hcrof => ?_)
  dsimp only [chainCloneSpec]
  rw [hsp1]
  rw [sepExists_sepConj_left]
  refine sepWPp_exists_elim_any fun evs => ?_
  simp only [sepConj_assoc]
  refine sepWPp_pure_elim_any fun ⟨htr_sf, hevs⟩ => ?_
  change evs = chainCloneEvents (g, rc) at hevs
  subst hevs
  rw [sepExists_sepConj_left]
  refine sepWPp_exists_elim_any fun g' => ?_
  simp only [sepConj_assoc]
  refine sepWPp_pure_elim_any fun _ => ?_
  have hsf_sp : sf.sp = s.sp := hspf.trans hsp1
  have hsf_tr : sf.trace = s0.trace := htr_sf.trans htr1_0
  rcases hcsf with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, _, hcs29, hvregsf_1⟩
  have hsf19 : sf.readReg64 .x19 = coroPtr := by rw [hcs19, hx19_1, hx19]
  have hsf20 : sf.readReg64 .x20 = totalLen := by rw [hcs20, hx20_1, hx20]
  have hsf21 : sf.readReg64 .x21 = off := hcs21.trans hx21_1
  have hsf22 : sf.readReg64 .x22 = off + BitVec.ofNat 64 (rem + 1) * 104#64 :=
    hcs22.trans hx22_1
  have hsf23 : sf.readReg64 .x23 = BitVec.ofNat 64 rem := hcs23.trans hx23_1
  have hsf24 : sf.readReg64 .x24 = src + 0x68#64 := hcs24.trans hx24_1
  have hsf25 : sf.readReg64 .x25 = dst_base := hcs25.trans hx25_1
  have hsf26 : sf.readReg64 .x26 = dst_base + off := hcs26.trans hx26_1
  have hsf27 : sf.readReg64 .x27 = sf.sp + 0x370#64 := by rw [hcs27, hx27_1, hx27, hsf_sp]
  have hsf29 : sf.readReg64 .x29 = fp := by rw [hcs29, hx29_1, hx29]
  rw [← hsf_sp]
  refine sepWPp_weaken_pre_any
    (sepConj_mono_left (chainAt_entails_chunks104_6QW A.repAlloc (g', rc) (sf.sp + 0x3e0#64))) ?_
  simp only [sepExists_sepConj_left]
  refine sepWPp_exists_elim_any fun sq0 => sepWPp_exists_elim_any fun sq1 =>
    sepWPp_exists_elim_any fun sq2 => sepWPp_exists_elim_any fun sq3 =>
    sepWPp_exists_elim_any fun sq4 => sepWPp_exists_elim_any fun sq5 =>
    sepWPp_exists_elim_any fun sw6 => ?_
  simp only [sepConj_assoc]
  refine sepWPp_pure_elim_any fun hch_inl => ?_
  refine sepWPp_weaken_pre_any
    (P' := memRegion (dst_base + off) 104 ∗
            chunks104_6QWAt (sf.sp + 0x3e0#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
            chainHeap A.repAlloc (g', rc) ∗ chainAt A.repAlloc (g, rc) src ∗
            A.pool lim (M.stepEvents (chainCloneEvents (g, rc)) stB) sf ∗
            stackAt sf.sp chainCloneStack ∗ F)
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine sepWPp_weaken_pre_any
    (sepConj_mono_left (memRegion_104_entails_chunks104_6QWAt (dst_base + off))) ?_
  simp only [sepExists_sepConj_left]
  refine sepWPp_exists_elim_any fun dq0 => sepWPp_exists_elim_any fun dq1 =>
    sepWPp_exists_elim_any fun dq2 => sepWPp_exists_elim_any fun dq3 =>
    sepWPp_exists_elim_any fun dq4 => sepWPp_exists_elim_any fun dq5 =>
    sepWPp_exists_elim_any fun dw6 => ?_
  have hcopy := rc_copy_placed_wp_vm ext sf rem (src + 0x68#64) (dst_base + off) off
    sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 sw6 dw6
    hrem_lt hpcf hrunf hsp_alf hsf21 hsf23 hsf24 hsf26 hsf27
  refine bind_sepWP_vm_pool_placed (A := A) (lim := lim)
    (st := M.stepEvents (chainCloneEvents (g, rc)) stB)
    (F := chainHeap A.repAlloc (g', rc) ∗ chainAt A.repAlloc (g, rc) src ∗
            stackAt sf.sp chainCloneStack ∗ F)
    hcrof hcopy
    (by sep_ac_rfl)
    fun s2 hpc2 hrun2 hcro2 _ hregs2 => ?_
  rcases hregs2 with ⟨hsp2, htr2, hx1_2, hx19_2, hx20_2, hx21_2, hx22_2,
    hx23_2, hx25_2, hx27_2, hx29_2, hvregs2⟩
  rw [hsf_sp] at hsp2 hx27_2 ⊢
  have hsp2_al : s2.spAligned = true := by simpa only [State.spAligned, hsp2] using hsp
  refine sepWPp_weaken_pre_any ?_
    (hnext s2 g' hpc2 hrun2 hcro2 hsp2 hsp2_al (htr2.trans hsf_tr)
      hx1_2 (hx19_2.trans hsf19) (hx20_2.trans hsf20) hx21_2 (hx22_2.trans hsf22)
      hx23_2 (hx25_2.trans hsf25) hx27_2 (hx29_2.trans hsf29)
      (hvregs2.trans (hvregsf_1.trans hvregs1)))
  have h104 := chunks104_6QWAt_entails_memRegion (s.sp + 0x3e0#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6
  have hdst_chain := chainAt_of_chunks104_6QW A.repAlloc (g', rc) (dst_base + off) hch_inl
  refine Entails.trans
    (Q := chunks104_6QWAt (s.sp + 0x3e0#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
          (chunks104_6QWAt (dst_base + off) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗ chainHeap A.repAlloc (g', rc)) ∗
          chainAt A.repAlloc (g, rc) src ∗
          A.pool lim (M.stepEvents (chainCloneEvents (g, rc)) stB) s2 ∗
          stackAt s.sp chainCloneStack ∗ F)
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine Entails.trans (sepConj_mono h104 (sepConj_mono_left hdst_chain)) ?_
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 400000 in
theorem rc_loop_placed_budget_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hcc : ChainClone3OkPlaced A lim ext)
    (s0 : State) (ret : BitVec 64) (Q : State → SepProp → Prop)
    (coroPtr totalLen dst_base fp : BitVec 64)
    (rcs_tl : List ReceiverChain) :
    ∀ (stB : M.σ) (s : State) (rc : ReceiverChain) (g : ChainGhost) (gs_tl : List ChainGhost)
      (src off : BitVec 64) (F : SepProp),
      gs_tl.length = rcs_tl.length →
      (rcs_tl.length + 1) * 104 < 2 ^ 63 →
      (rcs_tl.length + 1) * 104 ≤ 2 ^ 64 →
      FitsEvents M lim stB (((g :: gs_tl).zip (rc :: rcs_tl)).flatMap chainCloneEvents) →
      LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = (blkPl_518).base + 0x19fc#64 →
      s.status = .Running →
      s.spAligned = true →
      s.trace = s0.trace →
      s.readReg64 .x1 = src →
      s.readReg64 .x19 = coroPtr →
      s.readReg64 .x20 = totalLen →
      s.readReg64 .x21 = off →
      s.readReg64 .x22 = off + BitVec.ofNat 64 (rcs_tl.length + 1) * 104#64 →
      s.readReg64 .x23 = BitVec.ofNat 64 (rcs_tl.length + 1) →
      s.readReg64 .x25 = dst_base →
      s.readReg64 .x27 = s.sp + 0x370#64 →
      s.readReg64 .x29 = fp →
      (∀ (s1 : State) (gs' : List ChainGhost),
        gs'.length = (rc :: rcs_tl).length →
        s1.pc = (blkPl_518).base + 0x1a4c#64 →
        s1.status = .Running →
        LibsignalCodeRoLoaded lsmpl s1.mem →
        s1.sp = s.sp →
        s1.spAligned = true →
        s1.trace = s0.trace →
        s1.readReg64 .x19 = coroPtr →
        s1.readReg64 .x20 = totalLen →
        s1.readReg64 .x25 = dst_base →
        s1.readReg64 .x27 = s.sp + 0x370#64 →
        s1.readReg64 .x29 = fp →
        calleeSavedVRegs s1 = calleeSavedVRegs s →
        SepWPp (lsProg_518 ext) ret s1
          (A.pool lim (M.stepEvents (((g :: gs_tl).zip (rc :: rcs_tl)).flatMap chainCloneEvents) stB) s1 ∗
            arrayAt (chainAt A.repAlloc) 104 src ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
            arrayAt (chainAt A.repAlloc) 104 (dst_base + off) (gs'.zip (rc :: rcs_tl)) ∗
            memRegion (s.sp + 0x3e0#64) 104 ∗
            stackAt s.sp chainCloneStack ∗
            F)
          Q Qp) →
      SepWPp (lsProg_518 ext) ret s
        (A.pool lim stB s ∗
          arrayAt (chainAt A.repAlloc) 104 src ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
          memRegion (dst_base + off) ((rcs_tl.length + 1) * 104) ∗
          memRegion (s.sp + 0x3e0#64) 104 ∗
          stackAt s.sp chainCloneStack ∗
          F)
        Q Qp := by
  induction rcs_tl with
  | nil =>
    intro stB s rc g gs_tl src off F hgs hmul_lt _ hfits hcro hpc hrun hsp htr
      hx1 hx19 hx20 hx21 hx22 hx23 hx25 hx27 hx29 hnext
    cases gs_tl with
    | cons _ _ => simp at hgs
    | nil =>
      simp only [List.zip_cons_cons, List.zip_nil_right, arrayAt, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, sepConj_emp, List.length_nil, Nat.zero_add,
        Nat.one_mul] at *
      refine rc_iter_placed_budget_ok (stB := stB) ext hcc s0 s ret Q g rc 0
        coroPtr totalLen src dst_base off fp F
        hmul_lt hfits hcro hpc hrun hsp htr hx1 hx19 hx20 hx21 hx22 hx23 hx25 hx27 hx29
        fun s1 g' hpc1 hrun1 hcro1 hsp1 hspA1 htr1 _ hx19_1 hx20_1 _ _ _
          hx25_1 hx27_1 hx29_1 hvregs1 => ?_
      simp only [↓reduceIte] at hpc1
      have h1 := hnext s1 [g'] rfl hpc1 hrun1 hcro1 hsp1 hspA1 htr1
        hx19_1 hx20_1 hx25_1 hx27_1 hx29_1 hvregs1
      simpa only [List.zip_cons_cons, List.zip_nil_right, arrayAt, sepConj_emp]
        using h1
  | cons rc2 rcs2 ih =>
    intro stB s rc g gs_tl src off F hgs hmul_lt hsz_le hfits hcro hpc hrun hsp htr
      hx1 hx19 hx20 hx21 hx22 hx23 hx25 hx27 hx29 hnext
    cases gs_tl with
    | nil => simp at hgs
    | cons g2 gs2 =>
      have hgs2 : gs2.length = rcs2.length := by simpa using hgs
      have hmul2_lt : (rcs2.length + 1) * 104 < 2 ^ 63 := by simp [Nat.add_mul] at hmul_lt; omega
      have hsz2_le : (rcs2.length + 1) * 104 ≤ 2 ^ 64 := by simp [Nat.add_mul] at hsz_le; omega
      have hfits_split :
          FitsEvents M lim stB (chainCloneEvents (g, rc)) ∧
          FitsEvents M lim (M.stepEvents (chainCloneEvents (g, rc)) stB)
            (((g2 :: gs2).zip (rc2 :: rcs2)).flatMap chainCloneEvents) := by
        simpa only [List.zip_cons_cons, List.flatMap_cons] using
          (fitsEvents_append M lim (chainCloneEvents (g, rc))
            (((g2 :: gs2).zip (rc2 :: rcs2)).flatMap chainCloneEvents) stB).mp
            (by simpa only [List.zip_cons_cons, List.flatMap_cons] using hfits)
      rcases hfits_split with ⟨hfits_hd, hfits_tl⟩
      have hsplit_mr :
          memRegion (dst_base + off) (((rc2 :: rcs2).length + 1) * 104) =
            memRegion (dst_base + off) 104 ∗
              memRegion (dst_base + (off + 0x68#64)) ((rcs2.length + 1) * 104) := by
        refine memRegion_split' (n := 104) (k := (rcs2.length + 1) * 104) ?_
          (by bv_arith) hsz_le
        simp [List.length_cons, Nat.add_mul]; omega
      rw [List.zip_cons_cons, arrayAt, hsplit_mr]
      refine sepWPp_weaken_pre_any
        (P' := A.pool lim stB s ∗
                chainAt A.repAlloc (g, rc) src ∗
                memRegion (dst_base + off) 104 ∗
                memRegion (s.sp + 0x3e0#64) 104 ∗
                stackAt s.sp chainCloneStack ∗
                (arrayAt (chainAt A.repAlloc) 104 (src + 0x68#64) ((g2 :: gs2).zip (rc2 :: rcs2)) ∗
                  memRegion (dst_base + (off + 0x68#64)) ((rcs2.length + 1) * 104) ∗ F))
        (Entails.of_eq (by sep_ac_rfl)) ?_
      refine rc_iter_placed_budget_ok (stB := stB) ext hcc s0 s ret Q g rc (rcs2.length + 1)
        coroPtr totalLen src dst_base off fp _
        hmul_lt hfits_hd hcro hpc hrun hsp htr hx1 hx19 hx20 hx21 hx22 hx23 hx25 hx27 hx29
        fun s1 g' hpc1 hrun1 hcro1 hsp1 hspA1 htr1 hx1_1 hx19_1 hx20_1 hx21_1
          hx22_1 hx23_1 hx25_1 hx27_1 hx29_1 hvregs1 => ?_
      have hne0 : rcs2.length + 1 ≠ 0 := Nat.succ_ne_zero _
      simp only [hne0, ↓reduceIte] at hpc1
      have hx22_next : s1.readReg64 .x22 =
          (off + 0x68#64) + BitVec.ofNat 64 (rcs2.length + 1) * 104#64 := by
        rw [hx22_1]
        exact segClone_off_add_succ_mul_104 off (rcs2.length + 1)
      have hx27_1' : s1.readReg64 .x27 = s1.sp + 0x370#64 := by rw [hsp1]; exact hx27_1
      rw [← hsp1]
      refine sepWPp_weaken_pre_any
        (P' := A.pool lim (M.stepEvents (chainCloneEvents (g, rc)) stB) s1 ∗
                arrayAt (chainAt A.repAlloc) 104 (src + 0x68#64) ((g2 :: gs2).zip (rc2 :: rcs2)) ∗
                memRegion (dst_base + (off + 0x68#64)) ((rcs2.length + 1) * 104) ∗
                memRegion (s1.sp + 0x3e0#64) 104 ∗
                stackAt s1.sp chainCloneStack ∗
                (chainAt A.repAlloc (g, rc) src ∗ chainAt A.repAlloc (g', rc) (dst_base + off) ∗ F))
        (Entails.of_eq (by sep_ac_rfl)) ?_
      refine ih (M.stepEvents (chainCloneEvents (g, rc)) stB) s1 rc2 g2 gs2
        (src + 0x68#64) (off + 0x68#64) _
        hgs2 hmul2_lt hsz2_le hfits_tl hcro1 hpc1 hrun1 hspA1 htr1
        hx1_1 hx19_1 hx20_1 hx21_1 hx22_next hx23_1 hx25_1 hx27_1' hx29_1
        fun s2 gs2' hgs2' hpc2 hrun2 hcro2 hsp2 hspA2 htr2
          hx19_2 hx20_2 hx25_2 hx27_2 hx29_2 hvregs2 => ?_
      rw [hsp1] at hsp2 hx27_2 ⊢
      refine sepWPp_weaken_pre_any ?_
        (hnext s2 (g' :: gs2') (by simp [hgs2']) hpc2 hrun2 hcro2 hsp2 hspA2 htr2
          hx19_2 hx20_2 hx25_2 hx27_2 hx29_2 (hvregs2.trans hvregs1))
      simp only [List.zip_cons_cons, List.flatMap_cons, arrayAt,
        ← LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      have hd_add : dst_base + off + BitVec.ofNat 64 104 = dst_base + (off + 0x68#64) := by
        bv_arith
      rw [hd_add]
      exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneChainsPlacedBudgetAux
