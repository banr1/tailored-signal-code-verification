/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFrontPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePendingPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePendingStepsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Segment 3: `pending_pre_key` & `pending_kyber_pre_key` (Block `518`)

Deterministic allocation-event traces (`clonePendingKyberEvents`, `clonePendingEvents`) and
budget-threaded (`RustCliAllocBudget M`) Segment 3 proofs (`clonePending_vregs_placed_ok`,
`+0x1a5c → +0x1b20`, `genP3J2PlacedBudget → genP3J3PlacedBudget`) on Block `518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePendingPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (SessionState SignalMessage)
open CryptoVerification (LibsignalPlacement lsMemcpySym lsmpl lsρ)
open CryptoVerification.RustHeap (LayoutOk allocHookStack vecBuf vecU8Buf)
open CryptoVerification.LibsignalSessionRepr (chainAt)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost TailVecGhost noneCap optTailVecAt sessionStateAt
)
open CryptoVerification.LibsignalTripleRatchet (
  rootStack sessionMemcpyRegionSpec sessionMemcpySpec
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (chainCloneStack)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (
  OptSenderChainInline bytes104OfW6Q optSenderChainHeap
)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps (
  OptKybClone OptPendClone beq_ofNat_zero_eq_false cap_add_one_beq_zero_eq_false
  cap_add_one_ne_zero exists_unpack32_pair_of_length_8 ofNat_ne_zero_of_pos
  segClone_pure_eq_emp stackAt_chainClone_eq_alloc
  vecGhostAt_eq_of_nil vecGhostAt_eq_of_pos vecU8Buf_nil_eq vecU8Buf_pos_eq
)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkLib_eq_518 blkPl_518 lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  dpClosureEntryM3Placed genP3CallFramePlaced
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (
  GenP3J2Witness GenP3J3Witness OptSenderChainCloneRel
  genP3PendSpillScratch genP3SenderInlineWords genP3TailSpillScratch
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1 (
  call_raw_nopanic_placed lsAllocSym lsShimSym lscro_of_steps_placed
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a3 (
  list_eq_nil_or_length_pos m3a3SessionStateRestAt pure_elim_3 sepWPp_done
  sessionStateAt_coro_pending_eq
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget RustLayoutOk VmPreserved allocMemcpyVmSpec fitsEvents_append
  rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (
  LsRetAddr624 lsRetAddr624_blockPlacement_base_add
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget (
  blkLib_518_noSvc0
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePendingStepsPlacedBudget (
  ClonePendingPreKeyEnv clonePendingPreKeyEvents
  clonePendingPreKey_placed_ok_4k clonePendingPreKey_placed_ok_of_sessionShim
  fitsEnv_clonePendingPreKey_iff
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  noAllocShimBudgetSpec subroutine_ok_noAllocShim_of_sessionShimBudget
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
  subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm
  subroutine_ok_sessionShimBudget_of_rustAllocShimVm
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg

/-! ## 1. Exact Allocator Event Lists & Envelopes (`pending_kyber_pre_key` & Segment 3) -/

/-- Exact allocator event sequence emitted while cloning `pending_kyber_pre_key : Option TailVecGhost`
(`+0x1ac8 → +0x1b20`): `[]` when `kyber = none` or `gk.vec.bytes = []`, else
`rustAllocEvents gk.vec.bytes.length 1`. -/
def clonePendingKyberEvents (kyber : Option TailVecGhost) : List AllocEvent :=
  match kyber with
  | none => []
  | some gk =>
    if gk.vec.bytes = [] then []
    else rustAllocEvents gk.vec.bytes.length 1

/-- Exact allocator event envelope for `clonePendingKyber_placed_ok`. -/
def ClonePendingKyberEnv (kyber : Option TailVecGhost) (evs : List AllocEvent) : Prop :=
  evs = clonePendingKyberEvents kyber

@[simp]
theorem fitsEnv_clonePendingKyber_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (kyber : Option TailVecGhost) :
    FitsEnv M lim st (ClonePendingKyberEnv kyber) ↔
      FitsEvents M lim st (clonePendingKyberEvents kyber) :=
  FitsEnv.eq_iff

/-- Exact allocator event sequence emitted across Stage P3 Segment 3 (`+0x1a5c → +0x1b20`):
`pending_pre_key` followed by `pending_kyber_pre_key`. -/
def clonePendingEvents (recG : SessionGhost) : List AllocEvent :=
  clonePendingPreKeyEvents recG.pending ++ clonePendingKyberEvents recG.kyber

/-- Exact allocator event envelope for Stage P3 Segment 3 (`clonePending_vregs_placed_ok`). -/
def ClonePendingEnv (recG : SessionGhost) (evs : List AllocEvent) : Prop :=
  evs = clonePendingEvents recG

theorem clonePendingEnv_events (recG : SessionGhost) :
    ClonePendingEnv recG (clonePendingEvents recG) := rfl

@[simp]
theorem fitsEnv_clonePending_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (recG : SessionGhost) :
    FitsEnv M lim st (ClonePendingEnv recG) ↔
      FitsEvents M lim st (clonePendingEvents recG) :=
  FitsEnv.eq_iff

theorem fitsEvents_clonePending_of_fitsEnv (M : AllocCostModel) (lim : BudgetLimits)
    (stB : M.σ) (recG : SessionGhost)
    (h : FitsEnv M lim stB (ClonePendingEnv recG)) :
    FitsEvents M lim stB (clonePendingEvents recG) :=
  h (clonePendingEvents recG) rfl

/-! ## 2. Budget-Threaded Relocatable Junction Predicates (`genP3J2PlacedBudget`, `genP3J3PlacedBudget`) -/

/-- Budget-threaded relocatable `[LibsignalPlacement]` Junction 2 predicate at `+0x1a5c`. -/
def genP3J2PlacedBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) : SepProp :=
  ∃∗ w : GenP3J2Witness,
    ⌜s.sp = sp ∧
      s.readReg64 .x19 = coroPtr ∧
      s.readReg64 .x23 = BitVec.ofNat 64 st.receiverChains.length ∧
      s.readReg64 .x25 = w.newRcPtr ∧
      s.readReg64 .x27 = sp + 0x370#64 ∧
      s.readReg64 .x28 = 32#64 ∧
      s.readReg64 .x29 = fp ∧
      w.chains'.length = st.receiverChains.length ∧
      OptSenderChainCloneRel recG.sender st.senderChain w.sender' ∧
      OptSenderChainInline w.sender' st.senderChain
        (bytes104OfW6Q w.c0 w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5)⌝ ∗
      sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
      A.pool lim stB s ∗
      stackAt sp chainCloneStack ∗
      memRegion (sp + 0x3e0#64) 104 ∗
      ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      genP3CallFramePlaced A.repAlloc sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
        rem loc msgG msg ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr recG.localIk.bytes ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr recG.remoteIk.bytes ∗
      vecU8Buf A.repAlloc 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
      optSenderChainHeap A.repAlloc w.sender' st.senderChain ∗
      vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) (BitVec.ofNat 64 st.receiverChains.length)
        w.newRcPtr (w.chains'.zip st.receiverChains) ∗
      genP3PendSpillScratch sp ∗
      genP3TailSpillScratch sp ∗
      ((sp + 0x48#64) ↦₆₄ w.c0) ∗
      ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
      ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗
      ((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
      ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
      ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗
      ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
      ((sp + 0x98#64) ↦₆₄ 32#64) ∗
      ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
      genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5

/-- Budget-threaded relocatable `[LibsignalPlacement]` Junction 3 predicate at `+0x1b20`. -/
def genP3J3PlacedBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) : SepProp :=
  ∃∗ w : GenP3J3Witness,
    ⌜s.sp = sp ∧
      s.readReg64 .x19 = coroPtr ∧
      s.readReg64 .x22 = w.pendCap' ∧
      s.readReg64 .x23 = BitVec.ofNat 64 st.receiverChains.length ∧
      s.readReg64 .x25 = w.newRcPtr ∧
      s.readReg64 .x26 = w.kybCap' ∧
      s.readReg64 .x27 = ctxPtr ∧
      s.readReg64 .x28 = 32#64 ∧
      s.readReg64 .x29 = fp ∧
      w.chains'.length = st.receiverChains.length ∧
      OptSenderChainCloneRel recG.sender st.senderChain w.sender' ∧
      OptSenderChainInline w.sender' st.senderChain
        (bytes104OfW6Q w.c0 w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5)⌝ ∗
      sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
      A.pool lim stB s ∗
      stackAt sp chainCloneStack ∗
      memRegion (sp + 0x3e0#64) 104 ∗
      ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      genP3CallFramePlaced A.repAlloc sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
        rem loc msgG msg ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr recG.localIk.bytes ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr recG.remoteIk.bytes ∗
      vecU8Buf A.repAlloc 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
      optSenderChainHeap A.repAlloc w.sender' st.senderChain ∗
      vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) (BitVec.ofNat 64 st.receiverChains.length)
        w.newRcPtr (w.chains'.zip st.receiverChains) ∗
      OptPendClone A.repAlloc recG.pending w.pendCap' w.pendPtr' ∗
      OptKybClone A.repAlloc recG.kyber w.kybCap' w.kybPtr' ∗
      genP3TailSpillScratch sp ∗
      ((sp + 0x8#64) ↦₆₄ w.kybPtr') ∗
      ((sp + 0x10#64) ↦₆₄ w.d10) ∗
      ((sp + 0x18#64) ↦₆₄ w.pendPtr') ∗
      ((sp + 0x24#64) ↦₃₂ w.w24) ∗
      ((sp + 0x28#64) ↦₃₂ w.w28) ∗
      ((sp + 0x2c#64) ↦₃₂ w.w2c) ∗
      ((sp + 0x48#64) ↦₆₄ w.c0) ∗
      ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
      ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗
      ((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
      ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
      ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗
      ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
      ((sp + 0x98#64) ↦₆₄ 32#64) ∗
      ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
      genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5

/-! ## 3. Block-518 Budget-Synchronized Step Helpers for Sub-Segment 3B (`+0x1ac8 → +0x1b20`) -/

local macro "wp_steps_sync_518 " h:term:max mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException $h))
    blkLib_eq_518 blkLib_518_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

private def memcpy4kBudgetSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s0.sp allocHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp allocHookStack

private theorem memcpy4kBudget_of_region {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr sessionMemcpyRegionBudgetSpec) :
    subroutine_ok P addr memcpy4kBudgetSpec := by
  refine subroutine_ok_map h ?_
  rintro ⟨dst, src, bs⟩ R s0 hp
  dsimp only [memcpy4kBudgetSpec] at hp
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨hpure, hmem⟩
  refine ⟨(dst, src, bs), stackAt s0.sp allocHookStack ∗ R, ?_, fun sf hq => ?_⟩
  · dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpy4kBudgetSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hq
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hq.2.1.1, hq.2.1.2, hq.1⟩, Satisfies.of_eq hq.2.2 (by ac_rfl)⟩

private theorem memcpy4kBudget_of_4k {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr (sessionMemcpyBudgetSpec allocHookStack)) :
    subroutine_ok P addr memcpy4kBudgetSpec := by
  refine subroutine_ok_mono h (fun ⟨dst, src, bs⟩ R s0 hp => ?_)
    (fun ⟨dst, src, bs⟩ R s0 sf hq => ?_)
  · dsimp only [sessionMemcpyBudgetSpec, sessionMemcpySpec, libcMemcpySpec,
      memcpy4kBudgetSpec] at hp ⊢
    simpa only [sepConj_assoc] using hp
  · dsimp only [sessionMemcpyBudgetSpec, sessionMemcpySpec, libcMemcpySpec,
      memcpy4kBudgetSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hq
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hq.2.1.1, hq.2.1.2, hq.1⟩, hq.2.2⟩

private theorem bind_sepWP_lscro_state_placed [LibsignalPlacement] {prog : Program}
    {mid ret : BitVec 64} {s : State} {P P_step F : SepProp} {P_step_post : State → SepProp}
    {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step (fun sm P_m => (P_m ⊢ P_step_post sm) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨_, hoom⟩⟩ := hstep.elim hm hL
  rotate_left
  · exact False.elim (not_satisfies_false_sepConj hoom)
  have hmm' : sm.mem ⊨ (P_step_post sm ∗ F) ∗ R := by
    rw [sepConj_assoc]; exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpcm hrunm (lscro_of_steps_placed hsteps hcro) hregs R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem sepWPp_weaken_post {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Q' Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp)
    (himp : ∀ s1 P_f, Q s1 P_f → Q' s1 P_f) :
    SepWPp prog ret s P Q' Qp := by
  intro R hm hne
  obtain ⟨sf, hsteps, hpost⟩ := h R hm hne
  refine ⟨sf, hsteps, ?_⟩
  rcases hpost with ⟨hpc, hrun, P_f, hm', hQ⟩ | hp
  · exact Or.inl ⟨hpc, hrun, P_f, hm', himp sf P_f hQ⟩
  · exact Or.inr hp

private theorem kyb_none_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (sp coroPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x1ac8#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1b20#64) s
      (A.pool lim st s ∗ ((coroPtr + 0x220#64) ↦₆₄ noneCap))
      (fun s1 P_f =>
        (P_f ⊢ A.pool lim st s1 ∗ ((coroPtr + 0x220#64) ↦₆₄ noneCap)) ∧
        s1.sp = sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = noneCap ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsp_bv : (s.sp : BitVec 64) = sp := hsp_eq
  subst hsp_bv
  dsimp only [noneCap] at *
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps_sync_518 ext ((blkPl_518).base + 0x1b20#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

private theorem kyb_some_nil_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (sp coroPtr cap v08 : BitVec 64) (kw0 v24 : BitVec 32)
    (hcap_lt : cap.toNat < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x1ac8#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1b20#64) s
      (A.pool lim st s ∗
        ((coroPtr + 0x220#64) ↦₆₄ cap) ∗
        ((coroPtr + 0x230#64) ↦₆₄ 0#64) ∗
        ((coroPtr + 0x238#64) ↦₃₂ kw0) ∗
        ((sp + 0x8#64) ↦₆₄ v08) ∗
        ((sp + 0x24#64) ↦₃₂ v24))
      (fun s1 P_f =>
        (P_f ⊢
          A.pool lim st s1 ∗
            ((coroPtr + 0x220#64) ↦₆₄ cap) ∗
            ((coroPtr + 0x230#64) ↦₆₄ 0#64) ∗
            ((coroPtr + 0x238#64) ↦₃₂ kw0) ∗
            ((sp + 0x8#64) ↦₆₄ 1#64) ∗
            ((sp + 0x24#64) ↦₃₂ kw0)) ∧
        s1.sp = sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = 0#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsp_bv : (s.sp : BitVec 64) = sp := hsp_eq
  subst hsp_bv
  have hcmn : cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
  have hcmn_beq : (cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps_sync_518 ext ((blkPl_518).base + 0x1b20#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

private theorem kyb_some_pos_prep_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimBudgetSpec)
    (st : M.σ) (s : State) (sp coroPtr cap srcPtr : BitVec 64) (len : Nat) (kw0 v24 : BitVec 32)
    (hcap_lt : cap.toNat < 2 ^ 63)
    (hpos : 0 < len)
    (hlen_lt : len < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x1ac8#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (lsρ lsAllocSym) s
      (A.pool lim st s ∗
        ((coroPtr + 0x220#64) ↦₆₄ cap) ∗
        ((coroPtr + 0x228#64) ↦₆₄ srcPtr) ∗
        ((coroPtr + 0x230#64) ↦₆₄ BitVec.ofNat 64 len) ∗
        ((coroPtr + 0x238#64) ↦₃₂ kw0) ∗
        ((sp + 0x24#64) ↦₃₂ v24))
      (fun s1 P_f =>
        (P_f ⊢
          A.pool lim st s1 ∗
            ((coroPtr + 0x220#64) ↦₆₄ cap) ∗
            ((coroPtr + 0x228#64) ↦₆₄ srcPtr) ∗
            ((coroPtr + 0x230#64) ↦₆₄ BitVec.ofNat 64 len) ∗
            ((coroPtr + 0x238#64) ↦₃₂ kw0) ∗
            ((sp + 0x24#64) ↦₃₂ kw0)) ∧
        s1.sp = sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = BitVec.ofNat 64 len ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = srcPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = BitVec.ofNat 64 len ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x1af8#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsp_bv : (s.sp : BitVec 64) = sp := hsp_eq
  subst hsp_bv
  have hcmn : cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
  have hcmn_beq : (cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
  have hlen_ne : BitVec.ofNat 64 len ≠ 0#64 :=
    ofNat_ne_zero_of_pos hpos (Nat.lt_trans hlen_lt (by decide))
  have hlen_beq : (BitVec.ofNat 64 len == 0#64) = false :=
    beq_ofNat_zero_eq_false hpos (Nat.lt_trans hlen_lt (by decide))
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps_sync_518 ext (lsρ lsShimSym)
  wp_call hshim ()
  refine ProofLib.SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_518 ext (lsρ lsAllocSym)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

private theorem kyb_some_pos_copy_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) memcpy4kBudgetSpec)
    (st : M.σ) (s : State) (sp ptr' srcPtr v08 : BitVec 64) (bs : List (BitVec 8))
    (hptr : ptr' ≠ 0#64)
    (hlen_lt : bs.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x1af8#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = ptr')
    (hx21 : s.readReg64 .x21 = srcPtr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 bs.length) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1b20#64) s
      (A.pool lim st s ∗
        memRegion ptr' bs.length ∗
        (srcPtr ↦ₛ bs) ∗
        stackAt sp allocHookStack ∗
        ((sp + 0x8#64) ↦₆₄ v08))
      (fun s1 P_f =>
        (P_f ⊢
          A.pool lim st s1 ∗
            (ptr' ↦ₛ bs) ∗
            (srcPtr ↦ₛ bs) ∗
            stackAt sp allocHookStack ∗
            ((sp + 0x8#64) ↦₆₄ ptr')) ∧
        s1.sp = sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = BitVec.ofNat 64 bs.length ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsp_bv : (s.sp : BitVec 64) = sp := hsp_eq
  subst hsp_bv
  have hptr_beq : (ptr' == 0#64) = false := beq_eq_false_iff_ne.mpr hptr
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx0' : s.readReg64 (Reg.gpr 0#5) = ptr' := hx0
  have hx21' : s.readReg64 (Reg.gpr 21#5) = srcPtr := hx21
  have hx26' : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 bs.length := hx26
  wp_steps_sync_518 ext (lsρ lsMemcpySym)
  wp_call hmemcpy (ptr', srcPtr, bs)
  refine ProofLib.SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_518 ext ((blkPl_518).base + 0x1b20#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

/-! ## 4. Budget-Threaded CPS Sub-Segment 3B: `pending_kyber_pre_key` (`+0x1ac8 → +0x1b20`) -/

private theorem clonePendingKyber_core_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) memcpy4kBudgetSpec)
    (st : M.σ) (s0 s : State) (ret : BitVec 64) (Q : State → SepProp → Prop)
    (sp coroPtr v08 : BitVec 64) (v24 : BitVec 32)
    (kyber : Option TailVecGhost) (F : SepProp)
    (hfit : FitsEnv M lim st (ClonePendingKyberEnv kyber))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1ac8#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_al : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hnext : ∀ (s1 : State) (kybCap' kybPtr' : BitVec 64) (w24 : BitVec 32),
      s1.pc = (blkPl_518).base + 0x1b20#64 → s1.status = .Running →
      LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.sp = sp → s1.spAligned = true → s1.trace = s0.trace →
      s1.readReg64 .x19 = coroPtr → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = kybCap' → s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 → s1.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      SepWPp (lsProg_518 ext) ret s1
        (A.pool lim (M.stepEvents (clonePendingKyberEvents kyber) st) s1 ∗
          stackAt sp chainCloneStack ∗
          optTailVecAt A.repAlloc 32 (coroPtr + 0x220#64) kyber ∗
          OptKybClone A.repAlloc kyber kybCap' kybPtr' ∗
          ((sp + 0x8#64) ↦₆₄ kybPtr') ∗
          ((sp + 0x24#64) ↦₃₂ w24) ∗ F)
        Q Qp) :
    SepWPp (lsProg_518 ext) ret s
      (A.pool lim st s ∗ stackAt sp chainCloneStack ∗
        optTailVecAt A.repAlloc 32 (coroPtr + 0x220#64) kyber ∗
        ((sp + 0x8#64) ↦₆₄ v08) ∗ ((sp + 0x24#64) ↦₃₂ v24) ∗ F)
      Q Qp := by
  cases kyber with
  | none =>
    dsimp only [optTailVecAt, OptKybClone, clonePendingKyberEvents,
      AllocCostModel.stepEvents] at hnext ⊢
    simp only [sepConj_assoc]
    have hnone := kyb_none_placed_wp (A := A) (lim := lim) ext st s sp coroPtr hpc hrun hsp_eq hx19
    refine bind_sepWP_lscro_state_placed hcro hnone (by sep_focus)
      fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
    rcases hregs1 with ⟨hsp1, htr1_s, hx19_1, hx22_1, hx23_1, hx25_1,
      hx26_1, hx27_1, hx28_1, hx29_1, hvregs1⟩
    have hsp1_al : s1.spAligned = true := by
      simpa only [State.spAligned, hsp1, ← hsp_eq] using hsp_al
    have h_rfl : (⌜noneCap = noneCap⌝ : SepProp) = emp := segClone_pure_eq_emp rfl
    refine SepWPp.weaken_pre ?_
      (hnext s1 noneCap v08 v24 hpc1 hrun1 hcro1 hsp1 hsp1_al
        (htr1_s.trans htr) hx19_1 hx22_1 hx23_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs1)
    rw [h_rfl]
    simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)
  | some gk =>
    dsimp only [optTailVecAt, OptKybClone] at hnext ⊢
    simp only [sepConj_assoc]
    refine pure_elim_3 fun htail => ?_
    obtain ⟨kw0, kw1, _, htail_pts⟩ := exists_unpack32_pair_of_length_8 htail
    have h228 : coroPtr + 0x220#64 + 8#64 = coroPtr + 0x228#64 := by bv_arith
    have h230 : coroPtr + 0x220#64 + 16#64 = coroPtr + 0x230#64 := by bv_arith
    have h238 : coroPtr + 0x220#64 + BitVec.ofNat 64 24 = coroPtr + 0x238#64 := by bv_arith
    have h23c : coroPtr + 0x238#64 + 4#64 = coroPtr + 0x23c#64 := by bv_arith
    rw [h238, htail_pts (coroPtr + 0x238#64), h23c]
    rcases list_eq_nil_or_length_pos gk.vec.bytes with hnil | hpos
    · have hevs : clonePendingKyberEvents (some gk) = [] := by
        simp [clonePendingKyberEvents, hnil]
      rw [vecGhostAt_eq_of_nil A.repAlloc gk.vec (coroPtr + 0x220#64) hnil, h228, h230]
      simp only [sepConj_assoc]
      refine pure_elim_3 fun ⟨hcap_lt, hptr⟩ => ?_
      have hnil_wp := kyb_some_nil_placed_wp (A := A) (lim := lim) ext st s sp coroPtr gk.vec.cap
        v08 kw0 v24 hcap_lt hpc hrun hsp_eq hsp_al hx19
      refine bind_sepWP_lscro_state_placed hcro hnil_wp (by sep_focus)
        fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
      rcases hregs1 with ⟨hsp1, htr1_s, hx19_1, hx22_1, hx23_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hx29_1, hvregs1⟩
      have hsp1_al : s1.spAligned = true := by
        simpa only [State.spAligned, hsp1, ← hsp_eq] using hsp_al
      have h_rfl :
          (⌜(0#64 : BitVec 64) = BitVec.ofNat 64 ([] : List (BitVec 8)).length⌝ : SepProp) = emp :=
        segClone_pure_eq_emp rfl
      have h_pure1 : (⌜gk.tail.length = 32 - 24⌝ : SepProp) = emp := segClone_pure_eq_emp htail
      have h_pure2 : (⌜gk.vec.cap.toNat < 2 ^ 63 ∧ gk.vec.ptr ≠ 0⌝ : SepProp) = emp :=
        segClone_pure_eq_emp ⟨hcap_lt, hptr⟩
      refine SepWPp.weaken_pre ?_
        (hnext s1 0#64 1#64 kw0 hpc1 hrun1 hcro1 hsp1 hsp1_al
          (htr1_s.trans htr) hx19_1 hx22_1 hx23_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs1)
      rw [hevs, AllocCostModel.stepEvents,
          vecGhostAt_eq_of_nil A.repAlloc gk.vec (coroPtr + 0x220#64) hnil, h228, h230,
          h238, htail_pts (coroPtr + 0x238#64), h23c,
          hnil, vecU8Buf_nil_eq A.repAlloc, h_rfl, h_pure1, h_pure2]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
    · have hne : gk.vec.bytes ≠ [] := List.ne_nil_of_length_pos hpos
      have hevs : clonePendingKyberEvents (some gk) = rustAllocEvents gk.vec.bytes.length 1 := by
        simp [clonePendingKyberEvents, hne]
      have hfit_alloc : FitsEvents M lim st (rustAllocEvents gk.vec.bytes.length 1) :=
        hevs ▸ (fitsEnv_clonePendingKyber_iff (some gk)).mp hfit
      have hallocNoOom := subroutine_ok_allocNoOom_of_budget halloc
      rw [vecGhostAt_eq_of_pos A.repAlloc gk.vec (coroPtr + 0x220#64) hpos, h228, h230]
      simp only [sepConj_assoc]
      refine pure_elim_3 fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
      have hlen_lt : gk.vec.bytes.length < 2 ^ 63 := by omega
      have hlen_le63 : gk.vec.bytes.length + 1 ≤ 2 ^ 63 := by omega
      have hlay : LayoutOk gk.vec.bytes.length 1 := ⟨hpos, ⟨0, rfl⟩, hlen_le63⟩
      have hrlo : RustLayoutOk gk.vec.bytes.length 1 := ⟨hlay, by decide⟩
      have htoNat : (BitVec.ofNat 64 gk.vec.bytes.length).toNat = gk.vec.bytes.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hprep := kyb_some_pos_prep_placed_wp (A := A) (lim := lim) ext hshim st s sp coroPtr
        gk.vec.cap gk.vec.ptr gk.vec.bytes.length kw0 v24 hcap_lt hpos hlen_lt hpc hrun
        hsp_eq hsp_al hx19
      refine bind_sepWP_lscro_state_placed hcro hprep (by sep_focus)
        fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
      rcases hregs1 with ⟨hsp1, htr1_s, hx0_1, hx1_1, hx19_1, hx21_1, hx22_1,
        hx23_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs1_s⟩
      have hsp1_al : s1.spAligned = true := by
        simpa only [State.spAligned, hsp1, ← hsp_eq] using hsp_al
      have htr1 : s1.trace = s0.trace := htr1_s.trans htr
      rw [stackAt_chainClone_eq_alloc sp]
      simp only [sepConj_assoc]
      have hφ : (s1.readReg64 .x0).toNat = gk.vec.bytes.length ∧
          (s1.readReg64 .x1).toNat = 1 ∧
          RustLayoutOk gk.vec.bytes.length 1 ∧
          FitsEvents M lim st (rustAllocEvents gk.vec.bytes.length 1) ∧
          LsRetAddr624 (s1.readReg64 .lr) :=
        ⟨by rw [hx0_1, htoNat], by rw [hx1_1]; rfl, hrlo, hfit_alloc,
         by rw [show s1.readReg64 .lr = (blkPl_518).base + 0x1af8#64 from hx30_1]
            exact lsRetAddr624_blockPlacement_base_add 518 0x1af8#64 (by decide) (by decide)⟩
      refine call_raw_nopanic_placed
        (spec := rustCliAllocNoOomSpec M A lim false)
        (x := (gk.vec.bytes.length, 1, st))
        (T := A.pool lim st s1 ∗ stackAt sp allocHookStack)
        hcro1 hallocNoOom hpc1 hrun1 hsp1_al hx30_1
        (by dsimp only [rustCliAllocNoOomSpec]; rw [hsp1])
        hφ (by sep_focus)
        (hnext := fun s2 hpc2 hrun2 hsp2_1 hsp2_al hcs2 hcro2 => ?_)
      have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
      rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, hx22_cs2, hx23_cs2, _, hx25_cs2,
        hx26_cs2, hx27_cs2, hx28_cs2, hx29_cs2, hvregs2_1⟩
      have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
      have hx21_2 : s2.readReg64 .x21 = gk.vec.ptr := hx21_cs2.trans hx21_1
      have hx22_2 : s2.readReg64 .x22 = s.readReg64 .x22 := hx22_cs2.trans hx22_1
      have hx23_2 : s2.readReg64 .x23 = s.readReg64 .x23 := hx23_cs2.trans hx23_1
      have hx25_2 : s2.readReg64 .x25 = s.readReg64 .x25 := hx25_cs2.trans hx25_1
      have hx26_2 : s2.readReg64 .x26 = BitVec.ofNat 64 gk.vec.bytes.length :=
        hx26_cs2.trans hx26_1
      have hx27_2 : s2.readReg64 .x27 = s.readReg64 .x27 := hx27_cs2.trans hx27_1
      have hx28_2 : s2.readReg64 .x28 = s.readReg64 .x28 := hx28_cs2.trans hx28_1
      have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hx29_cs2.trans hx29_1
      dsimp only [rustCliAllocNoOomSpec]
      simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      rw [hsp1, ← hevs]
      refine SepWPp.pure_elim fun ⟨hacp2, hoom, _⟩ => ?_
      have htr2_1 : s2.trace = s1.trace := hacp2.2.1
      have htr2 : s2.trace = s0.trace := htr2_1.trans htr1
      set ptr' := s2.readReg64 .x0
      let st' := M.stepEvents (clonePendingKyberEvents (some gk)) st
      have hcopy := kyb_some_pos_copy_placed_wp (A := A) (lim := lim) ext hmemcpy st' s2 sp
        ptr' gk.vec.ptr v08 gk.vec.bytes hoom hlen_lt hpc2 hrun2 hsp2 hsp2_al rfl hx21_2 hx26_2
      refine bind_sepWP_lscro_state_placed hcro2 hcopy (by sep_focus)
        fun s3 hpc3 hrun3 hcro3 hregs3 => ?_
      rcases hregs3 with ⟨hsp3, htr3_2, hx19_3, hx22_3, hx23_3, hx25_3,
        hx26_3, hx27_3, hx28_3, hx29_3, hvregs3_2⟩
      refine CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4.SepWPp.weaken_frame
        (Entails.of_eq (stackAt_chainClone_eq_alloc sp).symm) (by sep_focus) ?_
      have hsp3_al : s3.spAligned = true := by
        simpa only [State.spAligned, hsp3, ← hsp2] using hsp2_al
      have h_rfl :
          (⌜BitVec.ofNat 64 gk.vec.bytes.length =
              BitVec.ofNat 64 gk.vec.bytes.length⌝ : SepProp) = emp :=
        segClone_pure_eq_emp rfl
      have h_pure1 : (⌜gk.tail.length = 32 - 24⌝ : SepProp) = emp := segClone_pure_eq_emp htail
      have h_pure2 :
          (⌜gk.vec.bytes.length ≤ gk.vec.cap.toNat ∧ gk.vec.cap.toNat < 2 ^ 63 ∧
              gk.vec.ptr ≠ 0⌝ : SepProp) = emp :=
        segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
      refine SepWPp.weaken_pre ?_
        (hnext s3 (BitVec.ofNat 64 gk.vec.bytes.length) ptr' kw0
          hpc3 hrun3 hcro3 hsp3 hsp3_al (htr3_2.trans htr2)
          (hx19_3.trans hx19_2) (hx22_3.trans hx22_2) (hx23_3.trans hx23_2)
          (hx25_3.trans hx25_2) hx26_3 (hx27_3.trans hx27_2)
          (hx28_3.trans hx28_2) (hx29_3.trans hx29_2)
          (hvregs3_2.trans (hvregs2_1.trans hvregs1_s)))
      have hlive_eq : A.live ptr' gk.vec.bytes.length 1 =
          A.repAlloc.live ptr' gk.vec.bytes.length 1 := rfl
      rw [vecGhostAt_eq_of_pos A.repAlloc gk.vec (coroPtr + 0x220#64) hpos, h228, h230,
          h238, htail_pts (coroPtr + 0x238#64), h23c,
          vecU8Buf_pos_eq A.repAlloc ptr' gk.vec.bytes hpos hlen_lt hoom,
          hlive_eq, h_rfl, h_pure1, h_pure2]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)

/-- Budget-threaded CPS sub-segment 3B (`+0x1ac8 → +0x1b20`, `pending_kyber_pre_key`) on
`lsProg_518 ext` from `noAllocShimBudgetSpec`, `rustCliAllocBudgetSpec M A lim false`, and
`sessionMemcpyRegionBudgetSpec`. -/
theorem clonePendingKyber_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (st : M.σ) (s0 s : State) (ret : BitVec 64) (Q : State → SepProp → Prop)
    (sp coroPtr v08 : BitVec 64) (v24 : BitVec 32)
    (kyber : Option TailVecGhost) (F : SepProp)
    (hfit : FitsEnv M lim st (ClonePendingKyberEnv kyber))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1ac8#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_al : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hnext : ∀ (s1 : State) (kybCap' kybPtr' : BitVec 64) (w24 : BitVec 32),
      s1.pc = (blkPl_518).base + 0x1b20#64 → s1.status = .Running →
      LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.sp = sp → s1.spAligned = true → s1.trace = s0.trace →
      s1.readReg64 .x19 = coroPtr → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = kybCap' → s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 → s1.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      SepWPp (lsProg_518 ext) ret s1
        (A.pool lim (M.stepEvents (clonePendingKyberEvents kyber) st) s1 ∗
          stackAt sp chainCloneStack ∗
          optTailVecAt A.repAlloc 32 (coroPtr + 0x220#64) kyber ∗
          OptKybClone A.repAlloc kyber kybCap' kybPtr' ∗
          ((sp + 0x8#64) ↦₆₄ kybPtr') ∗
          ((sp + 0x24#64) ↦₃₂ w24) ∗ F)
        Q Qp) :
    SepWPp (lsProg_518 ext) ret s
      (A.pool lim st s ∗ stackAt sp chainCloneStack ∗
        optTailVecAt A.repAlloc 32 (coroPtr + 0x220#64) kyber ∗
        ((sp + 0x8#64) ↦₆₄ v08) ∗ ((sp + 0x24#64) ↦₃₂ v24) ∗ F)
      Q Qp :=
  clonePendingKyber_core_placed_ok ext hshim halloc (memcpy4kBudget_of_region hmemcpy) st s0 s
    ret Q sp coroPtr v08 v24 kyber F hfit hcro hpc hrun hsp_eq hsp_al htr hx19 hnext

/-- Variant of `clonePendingKyber_placed_ok` accepting `sessionShimBudgetSpec` directly. -/
theorem clonePendingKyber_placed_ok_of_sessionShim [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (st : M.σ) (s0 s : State) (ret : BitVec 64) (Q : State → SepProp → Prop)
    (sp coroPtr v08 : BitVec 64) (v24 : BitVec 32)
    (kyber : Option TailVecGhost) (F : SepProp)
    (hfit : FitsEnv M lim st (ClonePendingKyberEnv kyber))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1ac8#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_al : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hnext : ∀ (s1 : State) (kybCap' kybPtr' : BitVec 64) (w24 : BitVec 32),
      s1.pc = (blkPl_518).base + 0x1b20#64 → s1.status = .Running →
      LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.sp = sp → s1.spAligned = true → s1.trace = s0.trace →
      s1.readReg64 .x19 = coroPtr → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = kybCap' → s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 → s1.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      SepWPp (lsProg_518 ext) ret s1
        (A.pool lim (M.stepEvents (clonePendingKyberEvents kyber) st) s1 ∗
          stackAt sp chainCloneStack ∗
          optTailVecAt A.repAlloc 32 (coroPtr + 0x220#64) kyber ∗
          OptKybClone A.repAlloc kyber kybCap' kybPtr' ∗
          ((sp + 0x8#64) ↦₆₄ kybPtr') ∗
          ((sp + 0x24#64) ↦₃₂ w24) ∗ F)
        Q Qp) :
    SepWPp (lsProg_518 ext) ret s
      (A.pool lim st s ∗ stackAt sp chainCloneStack ∗
        optTailVecAt A.repAlloc 32 (coroPtr + 0x220#64) kyber ∗
        ((sp + 0x8#64) ↦₆₄ v08) ∗ ((sp + 0x24#64) ↦₃₂ v24) ∗ F)
      Q Qp :=
  clonePendingKyber_placed_ok ext (subroutine_ok_noAllocShim_of_sessionShimBudget hshim)
    halloc hmemcpy st s0 s ret Q sp coroPtr v08 v24 kyber F hfit hcro hpc hrun hsp_eq hsp_al
    htr hx19 hnext

/-- Variant of `clonePendingKyber_placed_ok` accepting `sessionShimBudgetSpec` and
`sessionMemcpyBudgetSpec allocHookStack` (matching `AllocContractsMem4KBudget` directly). -/
theorem clonePendingKyber_placed_ok_4k [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym)
      (sessionMemcpyBudgetSpec allocHookStack))
    (st : M.σ) (s0 s : State) (ret : BitVec 64) (Q : State → SepProp → Prop)
    (sp coroPtr v08 : BitVec 64) (v24 : BitVec 32)
    (kyber : Option TailVecGhost) (F : SepProp)
    (hfit : FitsEnv M lim st (ClonePendingKyberEnv kyber))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1ac8#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_al : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hnext : ∀ (s1 : State) (kybCap' kybPtr' : BitVec 64) (w24 : BitVec 32),
      s1.pc = (blkPl_518).base + 0x1b20#64 → s1.status = .Running →
      LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.sp = sp → s1.spAligned = true → s1.trace = s0.trace →
      s1.readReg64 .x19 = coroPtr → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = kybCap' → s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 → s1.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      SepWPp (lsProg_518 ext) ret s1
        (A.pool lim (M.stepEvents (clonePendingKyberEvents kyber) st) s1 ∗
          stackAt sp chainCloneStack ∗
          optTailVecAt A.repAlloc 32 (coroPtr + 0x220#64) kyber ∗
          OptKybClone A.repAlloc kyber kybCap' kybPtr' ∗
          ((sp + 0x8#64) ↦₆₄ kybPtr') ∗
          ((sp + 0x24#64) ↦₃₂ w24) ∗ F)
        Q Qp) :
    SepWPp (lsProg_518 ext) ret s
      (A.pool lim st s ∗ stackAt sp chainCloneStack ∗
        optTailVecAt A.repAlloc 32 (coroPtr + 0x220#64) kyber ∗
        ((sp + 0x8#64) ↦₆₄ v08) ∗ ((sp + 0x24#64) ↦₃₂ v24) ∗ F)
      Q Qp :=
  clonePendingKyber_core_placed_ok ext (subroutine_ok_noAllocShim_of_sessionShimBudget hshim)
    halloc (memcpy4kBudget_of_4k hmemcpy) st s0 s ret Q sp coroPtr v08 v24 kyber F hfit hcro hpc
    hrun hsp_eq hsp_al htr hx19 hnext

/-! ## 5. Budget-Threaded Placed Segment 3 (`+0x1a5c → +0x1b20`, `genP3J2PlacedBudget → genP3J3PlacedBudget`) -/

private abbrev genP3M3a3TailFrame [LibsignalPlacement] (A : CryptoVerification.RustHeap.RustAlloc)
    (sp coroPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (w : GenP3J2Witness) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) : SepProp :=
  m3a3SessionStateRestAt A coroPtr recG st ∗ memRegion (sp + 0x3e0#64) 104 ∗
    genP3CallFramePlaced A sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest rem loc msgG msg ∗
    vecU8Buf A (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr recG.localIk.bytes ∗
    vecU8Buf A (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr recG.remoteIk.bytes ∗
    vecU8Buf A 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
    optSenderChainHeap A w.sender' st.senderChain ∗
    vecBuf A 104 8 (chainAt A) (BitVec.ofNat 64 st.receiverChains.length) w.newRcPtr
      (w.chains'.zip st.receiverChains) ∗
    genP3TailSpillScratch sp ∗ ((sp + 0x48#64) ↦₆₄ w.c0) ∗ ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
    ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗ ((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
    ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
    ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗ ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
    ((sp + 0x98#64) ↦₆₄ 32#64) ∗ ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
    genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5

set_option maxHeartbeats 800000 in
/-- Budget-threaded Placed Segment 3 (`stepEvents` form, `+0x1a5c → +0x1b20`): Advances `genP3J2PlacedBudget` to `genP3J3PlacedBudget` on `lsProg_518 ext` with exact event
folding `M.stepEvents (clonePendingEvents recG) stB` and polymorphic `Qp`. -/
theorem clonePending_vregs_placed_ok_stepEvents [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop} (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (s0 s : State) (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (_hrc_len : st.receiverChains.length < 2 ^ 32) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (_hsp_root : rootStack ≤ sp.toNat) (hfits : FitsEvents M lim stB (clonePendingEvents recG))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem) (hpc : s.pc = dpClosureEntryM3Placed + 0x1a5c#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace) :
    SepWPp (lsProg_518 ext) (dpClosureEntryM3Placed + 0x1b20#64) s
      (genP3J2PlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
        msgVer rest recG st rem loc msgG msg s)
      (fun s1 P_f =>
        (P_f ⊢ genP3J3PlacedBudget A lim (M.stepEvents (clonePendingEvents recG) stB)
          sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
          recG st rem loc msgG msg s1) ∧
        s1.trace = s0.trace ∧ LibsignalCodeRoLoaded lsmpl s1.mem ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s)
      Qp := by
  have ⟨hfit_pend_ev, hfit_kyb_ev⟩ :=
    (fitsEvents_append M lim (clonePendingPreKeyEvents recG.pending)
      (clonePendingKyberEvents recG.kyber) stB).mp hfits
  have hfit_pend : FitsEnv M lim stB (ClonePendingPreKeyEnv recG.pending) :=
    (fitsEnv_clonePendingPreKey_iff recG.pending).mpr hfit_pend_ev
  let st1 := M.stepEvents (clonePendingPreKeyEvents recG.pending) stB
  have hfit_kyb : FitsEnv M lim st1 (ClonePendingKyberEnv recG.kyber) :=
    (fitsEnv_clonePendingKyber_iff recG.kyber).mpr hfit_kyb_ev
  have hst_eq : M.stepEvents (clonePendingKyberEvents recG.kyber) st1 =
      M.stepEvents (clonePendingEvents recG) stB :=
    (M.stepEvents_append (clonePendingPreKeyEvents recG.pending)
      (clonePendingKyberEvents recG.kyber) stB).symm
  dsimp only [genP3J2PlacedBudget, genP3PendSpillScratch]
  refine SepWPp.exists_elim fun w => SepWPp.pure_elim
    fun ⟨hsp, hx19, hx23, hx25, _hx27, hx28, hx29, hch_len, hsc_rel, hsc_inl⟩ => ?_
  have hsp_al : s.spAligned = true := by simpa only [State.spAligned, hsp] using hsp_align
  rw [sessionStateAt_coro_pending_eq A.repAlloc coroPtr recG st]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ps => SepWPp.pure_elim fun hpure => ?_
  refine SepWPp.weaken_pre
    (P' := A.pool lim stB s ∗ stackAt sp chainCloneStack ∗
            optTailVecAt A.repAlloc 48 (coroPtr + 0x1f0#64) recG.pending ∗
            ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0x10#64) ↦₆₄ ps.v10) ∗ ((sp + 0x18#64) ↦₆₄ ps.v18) ∗
            ((sp + 0x28#64) ↦₃₂ ps.v28) ∗ ((sp + 0x2c#64) ↦₃₂ ps.v2c) ∗
            (optTailVecAt A.repAlloc 32 (coroPtr + 0x220#64) recG.kyber ∗
              ((sp + 0x8#64) ↦₆₄ ps.v08) ∗ ((sp + 0x24#64) ↦₃₂ ps.v24) ∗
              genP3M3a3TailFrame A.repAlloc sp coroPtr remAddrPtr locAddrPtr whisperMsgPtr cur
                msgVer rest w recG st rem loc msgG msg))
    (Entails.of_eq (by dsimp only [genP3M3a3TailFrame]; ac_rfl)) ?_
  refine clonePendingPreKey_placed_ok_of_sessionShim ext hshim halloc hmemcpy stB s0 s _ _
    sp coroPtr ctxPtr ps.v10 ps.v18 ps.v28 ps.v2c recG.pending _ hfit_pend hcro hpc hrun
    hsp hsp_al htr hx19
    fun s1 pendCap' pendPtr' d10 w28 w2c hpc1 hrun1 hcro1 hsp1 hsp1_al htr1
      hx19_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs1 => ?_
  refine SepWPp.weaken_pre
    (P' := A.pool lim st1 s1 ∗ stackAt sp chainCloneStack ∗
            optTailVecAt A.repAlloc 32 (coroPtr + 0x220#64) recG.kyber ∗
            ((sp + 0x8#64) ↦₆₄ ps.v08) ∗ ((sp + 0x24#64) ↦₃₂ ps.v24) ∗
            (optTailVecAt A.repAlloc 48 (coroPtr + 0x1f0#64) recG.pending ∗
              OptPendClone A.repAlloc recG.pending pendCap' pendPtr' ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              ((sp + 0x10#64) ↦₆₄ d10) ∗ ((sp + 0x18#64) ↦₆₄ pendPtr') ∗
              ((sp + 0x28#64) ↦₃₂ w28) ∗ ((sp + 0x2c#64) ↦₃₂ w2c) ∗
              genP3M3a3TailFrame A.repAlloc sp coroPtr remAddrPtr locAddrPtr whisperMsgPtr cur
                msgVer rest w recG st rem loc msgG msg))
    (Entails.of_eq (by dsimp only [genP3M3a3TailFrame]; ac_rfl)) ?_
  refine clonePendingKyber_placed_ok_of_sessionShim ext hshim halloc hmemcpy st1 s0 s1 _ _
    sp coroPtr ps.v08 ps.v24 recG.kyber _ hfit_kyb hcro1 hpc1 hrun1 hsp1 hsp1_al htr1 hx19_1
    fun sf kybCap' kybPtr' w24 hpcf hrunf hcrof hspf _hspf_al htrf
      hx19_f hx22_f hx23_f hx25_f hx26_f hx27_f hx28_f hx29_f hvregsf => ?_
  refine sepWPp_done hpcf hrunf ⟨?_, htrf, hcrof, hvregsf.trans hvregs1⟩
  rw [hst_eq]
  let w' : GenP3J3Witness :=
    { toGenP3J2Witness := w, pendCap' := pendCap', pendPtr' := pendPtr',
      kybCap' := kybCap', kybPtr' := kybPtr', d10 := d10, w24 := w24, w28 := w28, w2c := w2c }
  refine Entails.sepExists_right w' ?_
  apply Entails.pure_right
    ⟨hspf, hx19_f, hx22_f.trans hx22_1, hx23_f.trans (hx23_1.trans hx23),
     hx25_f.trans (hx25_1.trans hx25), hx26_f, hx27_f.trans hx27_1,
     hx28_f.trans (hx28_1.trans hx28), hx29_f.trans (hx29_1.trans hx29),
     hch_len, hsc_rel, hsc_inl⟩
  dsimp only [genP3J3PlacedBudget, genP3M3a3TailFrame, w']
  rw [sessionStateAt_coro_pending_eq A.repAlloc coroPtr recG st]
  simp only [sepConj_assoc]
  apply Entails.pure_right hpure
  exact Entails.of_eq (by ac_rfl)

/-- Budget-threaded Placed Segment 3 with `calleeSavedVRegs` (`+0x1a5c → +0x1b20`,
`genP3J2PlacedBudget → genP3J3PlacedBudget`): envelope form (`ClonePendingEnv`). -/
theorem clonePending_vregs_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop} (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (s0 s : State) (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (hrc_len : st.receiverChains.length < 2 ^ 32) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hsp_root : rootStack ≤ sp.toNat) (hfits : FitsEnv M lim stB (ClonePendingEnv recG))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem) (hpc : s.pc = dpClosureEntryM3Placed + 0x1a5c#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace) :
    SepWPp (lsProg_518 ext) (dpClosureEntryM3Placed + 0x1b20#64) s
      (genP3J2PlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
        msgVer rest recG st rem loc msgG msg s)
      (fun s1 P_f =>
        ∃ evs : List AllocEvent, ClonePendingEnv recG evs ∧
          (P_f ⊢ genP3J3PlacedBudget A lim (M.stepEvents evs stB)
            sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
            recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧ LibsignalCodeRoLoaded lsmpl s1.mem ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
      Qp :=
  sepWPp_weaken_post
    (clonePending_vregs_placed_ok_stepEvents ext hshim halloc hmemcpy s0 s sp fp coroPtr ctxPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg hrc_len
      hsp_align hsp_root (fitsEvents_clonePending_of_fitsEnv M lim stB recG hfits) hcro hpc hrun
      htr)
    fun _ _ ⟨hent1, htr1, hcro1, hv1⟩ => ⟨clonePendingEvents recG, rfl, hent1, htr1, hcro1, hv1⟩

set_option maxHeartbeats 800000 in
/-- 4K-stack variant of `clonePending_vregs_placed_ok` accepting
`sessionMemcpyBudgetSpec allocHookStack` directly. -/
theorem clonePending_vregs_4k_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop} (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) (sessionMemcpyBudgetSpec allocHookStack))
    (s0 s : State) (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (_hrc_len : st.receiverChains.length < 2 ^ 32) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (_hsp_root : rootStack ≤ sp.toNat) (hfits : FitsEnv M lim stB (ClonePendingEnv recG))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem) (hpc : s.pc = dpClosureEntryM3Placed + 0x1a5c#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace) :
    SepWPp (lsProg_518 ext) (dpClosureEntryM3Placed + 0x1b20#64) s
      (genP3J2PlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
        msgVer rest recG st rem loc msgG msg s)
      (fun s1 P_f =>
        ∃ evs : List AllocEvent, ClonePendingEnv recG evs ∧
          (P_f ⊢ genP3J3PlacedBudget A lim (M.stepEvents evs stB)
            sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
            recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧ LibsignalCodeRoLoaded lsmpl s1.mem ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
      Qp := by
  have ⟨hfit_pend_ev, hfit_kyb_ev⟩ :=
    (fitsEvents_append M lim (clonePendingPreKeyEvents recG.pending)
      (clonePendingKyberEvents recG.kyber) stB).mp
      (fitsEvents_clonePending_of_fitsEnv M lim stB recG hfits)
  have hfit_pend : FitsEnv M lim stB (ClonePendingPreKeyEnv recG.pending) :=
    (fitsEnv_clonePendingPreKey_iff recG.pending).mpr hfit_pend_ev
  let st1 := M.stepEvents (clonePendingPreKeyEvents recG.pending) stB
  have hfit_kyb : FitsEnv M lim st1 (ClonePendingKyberEnv recG.kyber) :=
    (fitsEnv_clonePendingKyber_iff recG.kyber).mpr hfit_kyb_ev
  have hst_eq : M.stepEvents (clonePendingKyberEvents recG.kyber) st1 =
      M.stepEvents (clonePendingEvents recG) stB :=
    (M.stepEvents_append (clonePendingPreKeyEvents recG.pending)
      (clonePendingKyberEvents recG.kyber) stB).symm
  dsimp only [genP3J2PlacedBudget, genP3PendSpillScratch]
  refine SepWPp.exists_elim fun w => SepWPp.pure_elim
    fun ⟨hsp, hx19, hx23, hx25, _hx27, hx28, hx29, hch_len, hsc_rel, hsc_inl⟩ => ?_
  have hsp_al : s.spAligned = true := by simpa only [State.spAligned, hsp] using hsp_align
  rw [sessionStateAt_coro_pending_eq A.repAlloc coroPtr recG st]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ps => SepWPp.pure_elim fun hpure => ?_
  refine SepWPp.weaken_pre
    (P' := A.pool lim stB s ∗ stackAt sp chainCloneStack ∗
            optTailVecAt A.repAlloc 48 (coroPtr + 0x1f0#64) recG.pending ∗
            ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0x10#64) ↦₆₄ ps.v10) ∗ ((sp + 0x18#64) ↦₆₄ ps.v18) ∗
            ((sp + 0x28#64) ↦₃₂ ps.v28) ∗ ((sp + 0x2c#64) ↦₃₂ ps.v2c) ∗
            (optTailVecAt A.repAlloc 32 (coroPtr + 0x220#64) recG.kyber ∗
              ((sp + 0x8#64) ↦₆₄ ps.v08) ∗ ((sp + 0x24#64) ↦₃₂ ps.v24) ∗
              genP3M3a3TailFrame A.repAlloc sp coroPtr remAddrPtr locAddrPtr whisperMsgPtr cur
                msgVer rest w recG st rem loc msgG msg))
    (Entails.of_eq (by dsimp only [genP3M3a3TailFrame]; ac_rfl)) ?_
  refine clonePendingPreKey_placed_ok_4k ext hshim halloc hmemcpy stB s0 s _ _
    sp coroPtr ctxPtr ps.v10 ps.v18 ps.v28 ps.v2c recG.pending _ hfit_pend hcro hpc hrun
    hsp hsp_al htr hx19
    fun s1 pendCap' pendPtr' d10 w28 w2c hpc1 hrun1 hcro1 hsp1 hsp1_al htr1
      hx19_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs1 => ?_
  refine SepWPp.weaken_pre
    (P' := A.pool lim st1 s1 ∗ stackAt sp chainCloneStack ∗
            optTailVecAt A.repAlloc 32 (coroPtr + 0x220#64) recG.kyber ∗
            ((sp + 0x8#64) ↦₆₄ ps.v08) ∗ ((sp + 0x24#64) ↦₃₂ ps.v24) ∗
            (optTailVecAt A.repAlloc 48 (coroPtr + 0x1f0#64) recG.pending ∗
              OptPendClone A.repAlloc recG.pending pendCap' pendPtr' ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              ((sp + 0x10#64) ↦₆₄ d10) ∗ ((sp + 0x18#64) ↦₆₄ pendPtr') ∗
              ((sp + 0x28#64) ↦₃₂ w28) ∗ ((sp + 0x2c#64) ↦₃₂ w2c) ∗
              genP3M3a3TailFrame A.repAlloc sp coroPtr remAddrPtr locAddrPtr whisperMsgPtr cur
                msgVer rest w recG st rem loc msgG msg))
    (Entails.of_eq (by dsimp only [genP3M3a3TailFrame]; ac_rfl)) ?_
  refine clonePendingKyber_placed_ok_4k ext hshim halloc hmemcpy st1 s0 s1 _ _
    sp coroPtr ps.v08 ps.v24 recG.kyber _ hfit_kyb hcro1 hpc1 hrun1 hsp1 hsp1_al htr1 hx19_1
    fun sf kybCap' kybPtr' w24 hpcf hrunf hcrof hspf _hspf_al htrf
      hx19_f hx22_f hx23_f hx25_f hx26_f hx27_f hx28_f hx29_f hvregsf => ?_
  refine sepWPp_done hpcf hrunf
    ⟨clonePendingEvents recG, rfl, ?_, htrf, hcrof, hvregsf.trans hvregs1⟩
  rw [hst_eq]
  let w' : GenP3J3Witness :=
    { toGenP3J2Witness := w, pendCap' := pendCap', pendPtr' := pendPtr',
      kybCap' := kybCap', kybPtr' := kybPtr', d10 := d10, w24 := w24, w28 := w28, w2c := w2c }
  refine Entails.sepExists_right w' ?_
  apply Entails.pure_right
    ⟨hspf, hx19_f, hx22_f.trans hx22_1, hx23_f.trans (hx23_1.trans hx23),
     hx25_f.trans (hx25_1.trans hx25), hx26_f, hx27_f.trans hx27_1,
     hx28_f.trans (hx28_1.trans hx28), hx29_f.trans (hx29_1.trans hx29),
     hch_len, hsc_rel, hsc_inl⟩
  dsimp only [genP3J3PlacedBudget, genP3M3a3TailFrame, w']
  rw [sessionStateAt_coro_pending_eq A.repAlloc coroPtr recG st]
  simp only [sepConj_assoc]
  apply Entails.pure_right hpure
  exact Entails.of_eq (by ac_rfl)

/-- VM-hook entry variant accepting `rustAllocShimVmSpec` and `allocMemcpyVmSpec` directly. -/
theorem clonePending_vregs_vmHooks_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) allocMemcpyVmSpec)
    (s0 s : State)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (hrc_len : st.receiverChains.length < 2 ^ 32)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hsp_root : rootStack ≤ sp.toNat)
    (hfits : FitsEnv M lim stB (ClonePendingEnv recG))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1a5c#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace) :
    SepWPp (lsProg_518 ext) (dpClosureEntryM3Placed + 0x1b20#64) s
      (genP3J2PlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
        msgVer rest recG st rem loc msgG msg s)
      (fun s1 P_f =>
        ∃ evs : List AllocEvent,
          ClonePendingEnv recG evs ∧
          (P_f ⊢ genP3J3PlacedBudget A lim (M.stepEvents evs stB)
            sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
            recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧
          LibsignalCodeRoLoaded lsmpl s1.mem ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
      Qp :=
  clonePending_vregs_placed_ok ext
    (subroutine_ok_sessionShimBudget_of_rustAllocShimVm hshim)
    halloc
    (subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm hmemcpy)
    s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
    recG st rem loc msgG msg hrc_len hsp_align hsp_root hfits hcro hpc hrun htr

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePendingPlacedBudget
