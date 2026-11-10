/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysTailPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePendingPlacedBudget
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
# Budget-Threaded Placed Segment 4: `alice_base_key` & `pq_ratchet_state` (Block `518`)

Deterministic allocation-event traces (`cloneAliceEvents`, `clonePqEvents`, `cloneKeysTailEvents`)
and budget-threaded (`RustCliAllocBudget M`) Segment 4 proofs (`cloneKeysTail_vregs_placed_ok`,
`+0x1b20 → +0x1bac`, `genP3J3PlacedBudget → genP3J4PlacedBudget`) on Block `518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysTailPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (SessionState SignalMessage)
open CryptoVerification (LibsignalPlacement lsMemcpySym lsmpl lsρ)
open CryptoVerification.RustHeap (LayoutOk allocHookStack vecBuf vecU8At vecU8Buf)
open CryptoVerification.LibsignalSessionRepr (VecGhost chainAt vecGhostAt)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost sessionStateAt
)
open CryptoVerification.LibsignalTripleRatchet (
  rootStack sessionMemcpyRegionSpec sessionMemcpySpec
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (chainCloneStack)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (
  OptSenderChainInline bytes104OfW6Q optSenderChainHeap
)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps (
  OptKybClone OptPendClone beq_ofNat_zero_eq_false exists_unpack32_pair_of_length_8
  ofNat_ne_zero_of_pos segClone_pure_eq_emp stackAt_chainClone_eq_alloc
  vecGhostAt_eq_of_nil vecGhostAt_eq_of_pos vecU8At_eq_of_nil vecU8At_eq_of_pos
  vecU8Buf_nil_eq vecU8Buf_pos_eq
)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkLib_eq_518 blkPl_518 lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  dpClosureEntryM3Placed genP3CallFramePlaced
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (
  GenP3J3Witness GenP3J4Witness OptSenderChainCloneRel
  genP3J4Placed genP3SenderInlineWords genP3TailSpillScratch
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1 (
  call_raw_nopanic_placed lsAllocSym lsShimSym lscro_of_steps_placed
  sessionStateAt_tail_eq tailSessionRestAt
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a3 (
  list_eq_nil_or_length_pos pure_elim_3 sepWPp_done
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
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePendingPlacedBudget (
  genP3J3PlacedBudget
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

/-! ## 1. Exact Allocator Event Lists & Envelopes (`alice_base_key`, `pq_ratchet_state`, & Segment 4) -/

/-- Exact allocator event sequence emitted while cloning `alice_base_key : VecGhost`
(`+0x1b20 → +0x1b68`): `[]` when `alice.bytes = []`, else `rustAllocEvents alice.bytes.length 1`. -/
def cloneAliceEvents (alice : VecGhost) : List AllocEvent :=
  if alice.bytes = [] then []
  else rustAllocEvents alice.bytes.length 1

/-- Exact allocator event envelope for `cloneAlice_placed_ok`. -/
def CloneAliceEnv (alice : VecGhost) (evs : List AllocEvent) : Prop :=
  evs = cloneAliceEvents alice

@[simp]
theorem fitsEnv_cloneAlice_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (alice : VecGhost) :
    FitsEnv M lim st (CloneAliceEnv alice) ↔ FitsEvents M lim st (cloneAliceEvents alice) :=
  FitsEnv.eq_iff

/-- Exact allocator event sequence emitted while cloning `pq_ratchet_state : List (BitVec 8)`
(`+0x1b68 → +0x1bac`): `[]` when `pqBytes = []`, else `rustAllocEvents pqBytes.length 1`. -/
def clonePqEvents (pqBytes : List (BitVec 8)) : List AllocEvent :=
  if pqBytes = [] then []
  else rustAllocEvents pqBytes.length 1

/-- Exact allocator event envelope for `clonePq_placed_ok`. -/
def ClonePqEnv (pqBytes : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  evs = clonePqEvents pqBytes

@[simp]
theorem fitsEnv_clonePq_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (pqBytes : List (BitVec 8)) :
    FitsEnv M lim st (ClonePqEnv pqBytes) ↔ FitsEvents M lim st (clonePqEvents pqBytes) :=
  FitsEnv.eq_iff

/-- Exact allocator event sequence emitted across Stage P3 Segment 4 (`+0x1b20 → +0x1bac`):
`alice_base_key` followed by `pq_ratchet_state`. -/
def cloneKeysTailEvents (recG : SessionGhost) (st : SessionState (List (BitVec 8))) :
    List AllocEvent :=
  cloneAliceEvents recG.alice ++ clonePqEvents st.pqRatchetState

/-- Exact allocator event envelope for Stage P3 Segment 4 (`cloneKeysTail_vregs_placed_ok`). -/
def CloneKeysTailEnv (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  evs = cloneKeysTailEvents recG st

theorem cloneKeysTailEnv_events (recG : SessionGhost) (st : SessionState (List (BitVec 8))) :
    CloneKeysTailEnv recG st (cloneKeysTailEvents recG st) := rfl

@[simp]
theorem fitsEnv_cloneKeysTail_iff {M : AllocCostModel} {lim : BudgetLimits} {stB : M.σ}
    (recG : SessionGhost) (st : SessionState (List (BitVec 8))) :
    FitsEnv M lim stB (CloneKeysTailEnv recG st) ↔
      FitsEvents M lim stB (cloneKeysTailEvents recG st) :=
  FitsEnv.eq_iff

theorem fitsEvents_cloneKeysTail_of_fitsEnv (M : AllocCostModel) (lim : BudgetLimits)
    (stB : M.σ) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (h : FitsEnv M lim stB (CloneKeysTailEnv recG st)) :
    FitsEvents M lim stB (cloneKeysTailEvents recG st) :=
  h (cloneKeysTailEvents recG st) rfl

/-! ## 2. Budget-Threaded Relocatable Junction 4 Predicate (`genP3J4PlacedBudget`) -/

/-- Budget-threaded relocatable `[LibsignalPlacement]` Junction 4 predicate at `+0x1bac`. -/
def genP3J4PlacedBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) : SepProp :=
  ∃∗ w : GenP3J4Witness,
    ⌜s.sp = sp ∧
      s.readReg64 .x19 = coroPtr ∧
      s.readReg64 .x21 = w.newPqPtr ∧
      s.readReg64 .x22 = w.pendCap' ∧
      s.readReg64 .x23 = w.newAlicePtr ∧
      s.readReg64 .x24 = BitVec.ofNat 64 recG.alice.bytes.length ∧
      s.readReg64 .x25 = w.newRcPtr ∧
      s.readReg64 .x26 = BitVec.ofNat 64 st.pqRatchetState.length ∧
      s.readReg64 .x27 = ctxPtr ∧
      s.readReg64 .x28 = 32#64 ∧
      s.readReg64 .x29 = fp ∧
      recG.regIds = unpack32 w.regW0 ++ unpack32 w.regW1 ∧
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
      vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.alice.bytes.length) w.newAlicePtr recG.alice.bytes ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 st.pqRatchetState.length) w.newPqPtr st.pqRatchetState ∗
      ((sp + 0x8#64) ↦₆₄ w.kybPtr') ∗
      ((sp + 0x10#64) ↦₆₄ w.d10) ∗
      ((sp + 0x18#64) ↦₆₄ w.pendPtr') ∗
      ((sp + 0x24#64) ↦₃₂ w.w24) ∗
      ((sp + 0x28#64) ↦₃₂ w.w28) ∗
      ((sp + 0x2c#64) ↦₃₂ w.w2c) ∗
      ((sp + 0x30#64) ↦₃₂ w.regW0) ∗
      ((sp + 0x34#64) ↦₃₂ w.regW1) ∗
      ((sp + 0x38#64) ↦₆₄ w.kybCap') ∗
      ((sp + 0x40#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
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

theorem genP3J4PlacedBudget_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stB : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) :
    genP3J4PlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
      msgVer rest recG st rem loc msgG msg s =
    genP3J4Placed (A.atState lim stB s) sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
      cur msgVer rest recG st rem loc msgG msg s := rfl

/-! ## 3. Block-518 Budget-Synchronized Step Helpers for Segment 4 (`+0x1b20 → +0x1bac`) -/

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
    exact ⟨hpure, Satisfies.of_eq hmem (by sep_ac_rfl)⟩
  · dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpy4kBudgetSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hq
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hq.2.1.1, hq.2.1.2, hq.1⟩, Satisfies.of_eq hq.2.2 (by sep_ac_rfl)⟩

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

private theorem alice_nil_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (st : M.σ) (s : State)
    (sp coroPtr v23 v26 u_38 u_40 : BitVec 64) (f248 f24c u_30 u_34 : BitVec 32)
    (hpc : s.pc = (blkPl_518).base + 0x1b20#64) (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp) (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx23 : s.readReg64 .x23 = v23)
    (hx26 : s.readReg64 .x26 = v26) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1b68#64) s
      (A.pool lim st s ∗ ((coroPtr + 0x168#64) ↦₆₄ 0#64) ∗
        ((coroPtr + 0x248#64) ↦₃₂ f248) ∗ ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
        ((sp + 0x30#64) ↦₃₂ u_30) ∗ ((sp + 0x34#64) ↦₃₂ u_34) ∗
        ((sp + 0x38#64) ↦₆₄ u_38) ∗ ((sp + 0x40#64) ↦₆₄ u_40))
      (fun s1 P_f =>
        (P_f ⊢ A.pool lim st s1 ∗ ((coroPtr + 0x168#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0x248#64) ↦₃₂ f248) ∗ ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
          ((sp + 0x30#64) ↦₃₂ f248) ∗ ((sp + 0x34#64) ↦₃₂ f24c) ∗
          ((sp + 0x38#64) ↦₆₄ v26) ∗ ((sp + 0x40#64) ↦₆₄ v23)) ∧
        s1.sp = sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧ s1.readReg64 .x23 = 1#64 ∧
        s1.readReg64 .x24 = 0#64 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsp_bv : (s.sp : BitVec 64) = sp := hsp_eq; subst hsp_bv
  have hsp_al15 : (s.sp &&& 15#64 == 0#64) = true := hsp_align
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx23' : s.readReg64 (Reg.gpr 23#5) = v23 := hx23
  have hx26' : s.readReg64 (Reg.gpr 26#5) = v26 := hx26
  wp_steps_sync_518 ext ((blkPl_518).base + 0x1b68#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame, by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

private theorem alice_pos_prep_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimBudgetSpec)
    (st : M.σ) (s : State) (sp coroPtr srcPtr v23 v26 u_38 u_40 : BitVec 64) (len : Nat)
    (f248 f24c u_30 u_34 : BitVec 32) (hpos : 0 < len) (hlen_lt : len < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x1b20#64) (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp) (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx23 : s.readReg64 .x23 = v23)
    (hx26 : s.readReg64 .x26 = v26) :
    SepWP (lsProg_518 ext) (lsρ lsAllocSym) s
      (A.pool lim st s ∗ ((coroPtr + 0x160#64) ↦₆₄ srcPtr) ∗
        ((coroPtr + 0x168#64) ↦₆₄ BitVec.ofNat 64 len) ∗
        ((coroPtr + 0x248#64) ↦₃₂ f248) ∗ ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
        ((sp + 0x30#64) ↦₃₂ u_30) ∗ ((sp + 0x34#64) ↦₃₂ u_34) ∗
        ((sp + 0x38#64) ↦₆₄ u_38) ∗ ((sp + 0x40#64) ↦₆₄ u_40))
      (fun s1 P_f =>
        (P_f ⊢ A.pool lim st s1 ∗ ((coroPtr + 0x160#64) ↦₆₄ srcPtr) ∗
          ((coroPtr + 0x168#64) ↦₆₄ BitVec.ofNat 64 len) ∗
          ((coroPtr + 0x248#64) ↦₃₂ f248) ∗ ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
          ((sp + 0x30#64) ↦₃₂ f248) ∗ ((sp + 0x34#64) ↦₃₂ f24c) ∗
          ((sp + 0x38#64) ↦₆₄ v26) ∗ ((sp + 0x40#64) ↦₆₄ v23)) ∧
        s1.sp = sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = BitVec.ofNat 64 len ∧
        s1.readReg64 .x1 = 1#64 ∧ s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = srcPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧ s1.readReg64 .x24 = BitVec.ofNat 64 len ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x1b4c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsp_bv : (s.sp : BitVec 64) = sp := hsp_eq; subst hsp_bv
  have hsp_al15 : (s.sp &&& 15#64 == 0#64) = true := hsp_align
  have hlen_ne : BitVec.ofNat 64 len ≠ 0#64 :=
    ofNat_ne_zero_of_pos hpos (Nat.lt_trans hlen_lt (by decide))
  have hlen_beq : (BitVec.ofNat 64 len == 0#64) = false :=
    beq_ofNat_zero_eq_false hpos (Nat.lt_trans hlen_lt (by decide))
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx23' : s.readReg64 (Reg.gpr 23#5) = v23 := hx23
  have hx26' : s.readReg64 (Reg.gpr 26#5) = v26 := hx26
  wp_steps_sync_518 ext (lsρ lsShimSym)
  wp_call hshim ()
  refine ProofLib.SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_518 ext (lsρ lsAllocSym)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame, by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

private theorem alice_pos_copy_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) memcpy4kBudgetSpec)
    (st : M.σ) (s : State) (sp coroPtr srcPtr ptr' : BitVec 64) (bs : List (BitVec 8))
    (hptr : ptr' ≠ 0#64) (hlen_lt : bs.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x1b4c#64) (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp) (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = ptr') (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = srcPtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 bs.length) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1b68#64) s
      (A.pool lim st s ∗ memRegion ptr' bs.length ∗ (srcPtr ↦ₛ bs) ∗ stackAt sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢ A.pool lim st s1 ∗ (ptr' ↦ₛ bs) ∗ (srcPtr ↦ₛ bs) ∗ stackAt sp allocHookStack) ∧
        s1.sp = sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧ s1.readReg64 .x23 = ptr' ∧
        s1.readReg64 .x24 = BitVec.ofNat 64 bs.length ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsp_bv : (s.sp : BitVec 64) = sp := hsp_eq; subst hsp_bv
  have hsp_al15 : (s.sp &&& 15#64 == 0#64) = true := hsp_align
  have hptr_beq : (ptr' == 0#64) = false := beq_eq_false_iff_ne.mpr hptr
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx0' : s.readReg64 (Reg.gpr 0#5) = ptr' := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = srcPtr := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 bs.length := hx24
  wp_steps_sync_518 ext (lsρ lsMemcpySym)
  wp_call hmemcpy (ptr', srcPtr, bs)
  refine ProofLib.SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_518 ext ((blkPl_518).base + 0x1b68#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame, by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

private theorem pq_nil_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (st : M.σ) (s : State) (sp coroPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x1b68#64) (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp) (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1bac#64) s
      (A.pool lim st s ∗ ((coroPtr + 0x180#64) ↦₆₄ 0#64))
      (fun s1 P_f =>
        (P_f ⊢ A.pool lim st s1 ∗ ((coroPtr + 0x180#64) ↦₆₄ 0#64)) ∧
        s1.sp = sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = 1#64 ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧ s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = 0#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsp_bv : (s.sp : BitVec 64) = sp := hsp_eq; subst hsp_bv
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps_sync_518 ext ((blkPl_518).base + 0x1bac#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame, by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

private theorem pq_pos_prep_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimBudgetSpec)
    (st : M.σ) (s : State) (sp coroPtr srcPtr : BitVec 64) (len : Nat)
    (hpos : 0 < len) (hlen_lt : len < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x1b68#64) (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp) (hsp_align : s.spAligned = true) (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (lsρ lsAllocSym) s
      (A.pool lim st s ∗ ((coroPtr + 0x178#64) ↦₆₄ srcPtr) ∗
        ((coroPtr + 0x180#64) ↦₆₄ BitVec.ofNat 64 len))
      (fun s1 P_f =>
        (P_f ⊢ A.pool lim st s1 ∗ ((coroPtr + 0x178#64) ↦₆₄ srcPtr) ∗
          ((coroPtr + 0x180#64) ↦₆₄ BitVec.ofNat 64 len)) ∧
        s1.sp = sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = BitVec.ofNat 64 len ∧
        s1.readReg64 .x1 = 1#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧ s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = BitVec.ofNat 64 len ∧ s1.readReg64 .x27 = srcPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x27 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x1b88#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsp_bv : (s.sp : BitVec 64) = sp := hsp_eq; subst hsp_bv
  have hsp_al15 : (s.sp &&& 15#64 == 0#64) = true := hsp_align
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
  refine ⟨by sep_frame, by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

private theorem pq_pos_copy_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) memcpy4kBudgetSpec)
    (st : M.σ) (s : State) (sp coroPtr srcPtr ptr' rootKeyLen : BitVec 64) (bs : List (BitVec 8))
    (hptr : ptr' ≠ 0#64) (hlen_lt : bs.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x1b88#64) (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp) (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = ptr') (hx19 : s.readReg64 .x19 = coroPtr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 bs.length) (hx27 : s.readReg64 .x27 = srcPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1bac#64) s
      (A.pool lim st s ∗ ((sp + 0x98#64) ↦₆₄ rootKeyLen) ∗
        memRegion ptr' bs.length ∗ (srcPtr ↦ₛ bs) ∗ stackAt sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢ A.pool lim st s1 ∗ ((sp + 0x98#64) ↦₆₄ rootKeyLen) ∗
          (ptr' ↦ₛ bs) ∗ (srcPtr ↦ₛ bs) ∗ stackAt sp allocHookStack) ∧
        s1.sp = sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = ptr' ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧ s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = BitVec.ofNat 64 bs.length ∧
        s1.readReg64 .x27 = s.readReg64 .x28 ∧ s1.readReg64 .x28 = rootKeyLen ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsp_bv : (s.sp : BitVec 64) = sp := hsp_eq; subst hsp_bv
  have hsp_al15 : (s.sp &&& 15#64 == 0#64) = true := hsp_align
  have hptr_beq : (ptr' == 0#64) = false := beq_eq_false_iff_ne.mpr hptr
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx0' : s.readReg64 (Reg.gpr 0#5) = ptr' := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx26' : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 bs.length := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = srcPtr := hx27
  wp_steps_sync_518 ext (lsρ lsMemcpySym)
  wp_call hmemcpy (ptr', srcPtr, bs)
  refine ProofLib.SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_518 ext ((blkPl_518).base + 0x1bac#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame, by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

/-! ## 4. Budget-Threaded CPS Sub-Segments 4A (`alice_base_key`) & 4B (`pq_ratchet_state`) -/

private theorem cloneAlice_core_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) memcpy4kBudgetSpec)
    (st : M.σ) (s0 s : State) (ret : BitVec 64) (Q : State → SepProp → Prop)
    (sp coroPtr v23 v26 u_38 u_40 : BitVec 64)
    (f248 f24c u_30 u_34 : BitVec 32)
    (alice : VecGhost) (F : SepProp)
    (hfit : FitsEnv M lim st (CloneAliceEnv alice))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1b20#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_al : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx23 : s.readReg64 .x23 = v23)
    (hx26 : s.readReg64 .x26 = v26)
    (hnext : ∀ (s1 : State) (newAlicePtr : BitVec 64),
      s1.pc = (blkPl_518).base + 0x1b68#64 → s1.status = .Running →
      LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.sp = sp → s1.spAligned = true → s1.trace = s0.trace →
      s1.readReg64 .x19 = coroPtr → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = newAlicePtr →
      s1.readReg64 .x24 = BitVec.ofNat 64 alice.bytes.length →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      SepWPp (lsProg_518 ext) ret s1
        (A.pool lim (M.stepEvents (cloneAliceEvents alice) st) s1 ∗
          stackAt sp allocHookStack ∗
          vecGhostAt A.repAlloc alice (coroPtr + 0x158#64) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 alice.bytes.length) newAlicePtr alice.bytes ∗
          ((coroPtr + 0x248#64) ↦₃₂ f248) ∗
          ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
          ((sp + 0x30#64) ↦₃₂ f248) ∗
          ((sp + 0x34#64) ↦₃₂ f24c) ∗
          ((sp + 0x38#64) ↦₆₄ v26) ∗
          ((sp + 0x40#64) ↦₆₄ v23) ∗ F)
        Q Qp) :
    SepWPp (lsProg_518 ext) ret s
      (A.pool lim st s ∗ stackAt sp allocHookStack ∗
        vecGhostAt A.repAlloc alice (coroPtr + 0x158#64) ∗
        ((coroPtr + 0x248#64) ↦₃₂ f248) ∗
        ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
        ((sp + 0x30#64) ↦₃₂ u_30) ∗
        ((sp + 0x34#64) ↦₃₂ u_34) ∗
        ((sp + 0x38#64) ↦₆₄ u_38) ∗
        ((sp + 0x40#64) ↦₆₄ u_40) ∗ F)
      Q Qp := by
  have h160 : coroPtr + 0x158#64 + 8#64 = coroPtr + 0x160#64 := by bv_arith
  have h168 : coroPtr + 0x158#64 + 16#64 = coroPtr + 0x168#64 := by bv_arith
  rcases list_eq_nil_or_length_pos alice.bytes with hnil | hpos
  · have hevs : cloneAliceEvents alice = [] := by simp [cloneAliceEvents, hnil]
    rw [vecGhostAt_eq_of_nil A.repAlloc alice (coroPtr + 0x158#64) hnil, h160, h168]
    simp only [sepConj_assoc]
    refine pure_elim_3 fun halice_pure => ?_
    have hnil_wp := alice_nil_placed_wp (A := A) (lim := lim) ext st s sp coroPtr
      v23 v26 u_38 u_40 f248 f24c u_30 u_34 hpc hrun hsp_eq hsp_al hx19 hx23 hx26
    refine bind_sepWP_lscro_state_placed hcro hnil_wp (by sep_focus)
      fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
    rcases hregs1 with ⟨hsp1, htr1_s, hx19_1, hx22_1, hx23_1, hx24_1,
      hx25_1, hx27_1, hx28_1, hx29_1, hvregs1⟩
    have hsp1_al : s1.spAligned = true := by
      simpa only [State.spAligned, hsp1, ← hsp_eq] using hsp_al
    refine SepWPp.weaken_pre ?_
      (hnext s1 1#64 hpc1 hrun1 hcro1 hsp1 hsp1_al (htr1_s.trans htr)
        hx19_1 hx22_1 hx23_1 (by simpa [hnil] using hx24_1)
        hx25_1 hx27_1 hx28_1 hx29_1 hvregs1)
    rw [hevs, AllocCostModel.stepEvents, List.foldl_nil,
        vecGhostAt_eq_of_nil A.repAlloc alice (coroPtr + 0x158#64) hnil, h160, h168,
        segClone_pure_eq_emp halice_pure]
    simp only [hnil, List.length_nil, BitVec.ofNat_eq_ofNat, vecU8Buf_nil_eq A.repAlloc,
      sepConj_assoc, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by sep_ac_rfl)
  · have hne : alice.bytes ≠ [] := List.ne_nil_of_length_pos hpos
    have hevs : cloneAliceEvents alice = rustAllocEvents alice.bytes.length 1 := by
      simp [cloneAliceEvents, hne]
    have hfit_alloc : FitsEvents M lim st (rustAllocEvents alice.bytes.length 1) :=
      hevs ▸ (fitsEnv_cloneAlice_iff alice).mp hfit
    have hallocNoOom := subroutine_ok_allocNoOom_of_budget halloc
    rw [vecGhostAt_eq_of_pos A.repAlloc alice (coroPtr + 0x158#64) hpos, h160, h168]
    simp only [sepConj_assoc]
    refine pure_elim_3 fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hlen_lt : alice.bytes.length < 2 ^ 63 := by omega
    have hlen_le63 : alice.bytes.length + 1 ≤ 2 ^ 63 := by omega
    have hlay : LayoutOk alice.bytes.length 1 := ⟨hpos, ⟨0, rfl⟩, hlen_le63⟩
    have hrlo : RustLayoutOk alice.bytes.length 1 := ⟨hlay, by decide⟩
    have htoNat : (BitVec.ofNat 64 alice.bytes.length).toNat = alice.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hprep := alice_pos_prep_placed_wp (A := A) (lim := lim) ext hshim st s sp coroPtr
      alice.ptr v23 v26 u_38 u_40 alice.bytes.length f248 f24c u_30 u_34
      hpos hlen_lt hpc hrun hsp_eq hsp_al hx19 hx23 hx26
    refine bind_sepWP_lscro_state_placed hcro hprep (by sep_focus)
      fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
    rcases hregs1 with ⟨hsp1, htr1_s, hx0_1, hx1_1, hx19_1, hx21_1, hx22_1,
      hx24_1, hx25_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs1_s⟩
    have hsp1_al : s1.spAligned = true := by
      simpa only [State.spAligned, hsp1, ← hsp_eq] using hsp_al
    have htr1 : s1.trace = s0.trace := htr1_s.trans htr
    have hφ : (s1.readReg64 .x0).toNat = alice.bytes.length ∧
        (s1.readReg64 .x1).toNat = 1 ∧
        RustLayoutOk alice.bytes.length 1 ∧
        FitsEvents M lim st (rustAllocEvents alice.bytes.length 1) ∧
        LsRetAddr624 (s1.readReg64 .lr) :=
      ⟨by rw [hx0_1, htoNat], by rw [hx1_1]; rfl, hrlo, hfit_alloc,
       by rw [show s1.readReg64 .lr = (blkPl_518).base + 0x1b4c#64 from hx30_1]
          exact lsRetAddr624_blockPlacement_base_add 518 0x1b4c#64 (by decide) (by decide)⟩
    refine call_raw_nopanic_placed
      (spec := rustCliAllocNoOomSpec M A lim false)
      (x := (alice.bytes.length, 1, st))
      (T := A.pool lim st s1 ∗ stackAt sp allocHookStack)
      hcro1 hallocNoOom hpc1 hrun1 hsp1_al hx30_1
      (by dsimp only [rustCliAllocNoOomSpec]; rw [hsp1])
      hφ (by sep_focus)
      (hnext := fun s2 hpc2 hrun2 hsp2_1 hsp2_al hcs2 hcro2 => ?_)
    have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
    rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, hx22_cs2, _, hx24_cs2, hx25_cs2,
      _, hx27_cs2, hx28_cs2, hx29_cs2, hvregs2_1⟩
    have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
    have hx21_2 : s2.readReg64 .x21 = alice.ptr := hx21_cs2.trans hx21_1
    have hx22_2 : s2.readReg64 .x22 = s.readReg64 .x22 := hx22_cs2.trans hx22_1
    have hx24_2 : s2.readReg64 .x24 = BitVec.ofNat 64 alice.bytes.length :=
      hx24_cs2.trans hx24_1
    have hx25_2 : s2.readReg64 .x25 = s.readReg64 .x25 := hx25_cs2.trans hx25_1
    have hx27_2 : s2.readReg64 .x27 = s.readReg64 .x27 := hx27_cs2.trans hx27_1
    have hx28_2 : s2.readReg64 .x28 = s.readReg64 .x28 := hx28_cs2.trans hx28_1
    have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hx29_cs2.trans hx29_1
    dsimp only [rustCliAllocNoOomSpec]
    simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    rw [hsp1, ← hevs]
    refine SepWPp.pure_elim fun ⟨hacp2, hoom, _⟩ => ?_
    have htr2 : s2.trace = s0.trace := hacp2.2.1.trans htr1
    set ptr' := s2.readReg64 .x0
    let st' := M.stepEvents (cloneAliceEvents alice) st
    have hcopy := alice_pos_copy_placed_wp (A := A) (lim := lim) ext hmemcpy st' s2 sp coroPtr
      alice.ptr ptr' alice.bytes hoom hlen_lt hpc2 hrun2 hsp2 hsp2_al rfl hx19_2 hx21_2 hx24_2
    refine bind_sepWP_lscro_state_placed hcro2 hcopy (by sep_focus)
      fun s3 hpc3 hrun3 hcro3 hregs3 => ?_
    rcases hregs3 with ⟨hsp3, htr3_2, hx19_3, hx22_3, hx23_3, hx24_3,
      hx25_3, hx27_3, hx28_3, hx29_3, hvregs3_2⟩
    have hsp3_al : s3.spAligned = true := by
      simpa only [State.spAligned, hsp3, ← hsp2] using hsp2_al
    have h_pure :
        (⌜alice.bytes.length ≤ alice.cap.toNat ∧ alice.cap.toNat < 2 ^ 63 ∧
            alice.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
    refine SepWPp.weaken_pre ?_
      (hnext s3 ptr' hpc3 hrun3 hcro3 hsp3 hsp3_al (htr3_2.trans htr2)
        hx19_3 (hx22_3.trans hx22_2) hx23_3 hx24_3 (hx25_3.trans hx25_2)
        (hx27_3.trans hx27_2) (hx28_3.trans hx28_2) (hx29_3.trans hx29_2)
        (hvregs3_2.trans (hvregs2_1.trans hvregs1_s)))
    have hlive_eq : A.live ptr' alice.bytes.length 1 =
        A.repAlloc.live ptr' alice.bytes.length 1 := rfl
    rw [vecGhostAt_eq_of_pos A.repAlloc alice (coroPtr + 0x158#64) hpos, h160, h168,
        vecU8Buf_pos_eq A.repAlloc ptr' alice.bytes hpos hlen_lt hoom,
        hlive_eq, h_pure]
    simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by sep_ac_rfl)

private theorem clonePq_core_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) memcpy4kBudgetSpec)
    (st : M.σ) (s0 s : State) (ret : BitVec 64) (Q : State → SepProp → Prop)
    (sp coroPtr pqCap pqPtr ctxPtr : BitVec 64)
    (pqBytes : List (BitVec 8)) (F : SepProp)
    (hfit : FitsEnv M lim st (ClonePqEnv pqBytes))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1b68#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_al : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 32#64)
    (hnext : ∀ (s1 : State) (newPqPtr : BitVec 64),
      s1.pc = (blkPl_518).base + 0x1bac#64 → s1.status = .Running →
      LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.sp = sp → s1.spAligned = true → s1.trace = s0.trace →
      s1.readReg64 .x19 = coroPtr → s1.readReg64 .x21 = newPqPtr →
      s1.readReg64 .x22 = s.readReg64 .x22 → s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = BitVec.ofNat 64 pqBytes.length →
      s1.readReg64 .x27 = ctxPtr → s1.readReg64 .x28 = 32#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      SepWPp (lsProg_518 ext) ret s1
        (A.pool lim (M.stepEvents (clonePqEvents pqBytes) st) s1 ∗
          stackAt sp allocHookStack ∗
          vecU8At A.repAlloc (coroPtr + 0x170#64) pqCap pqPtr pqBytes ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 pqBytes.length) newPqPtr pqBytes ∗
          ((sp + 0x98#64) ↦₆₄ 32#64) ∗ F)
        Q Qp) :
    SepWPp (lsProg_518 ext) ret s
      (A.pool lim st s ∗ stackAt sp allocHookStack ∗
        vecU8At A.repAlloc (coroPtr + 0x170#64) pqCap pqPtr pqBytes ∗
        ((sp + 0x98#64) ↦₆₄ 32#64) ∗ F)
      Q Qp := by
  have h178 : coroPtr + 0x170#64 + 8#64 = coroPtr + 0x178#64 := by bv_arith
  have h180 : coroPtr + 0x170#64 + 16#64 = coroPtr + 0x180#64 := by bv_arith
  rcases list_eq_nil_or_length_pos pqBytes with hnil | hpos
  · subst hnil
    have hevs : clonePqEvents [] = [] := rfl
    rw [vecU8At_eq_of_nil A.repAlloc (coroPtr + 0x170#64) pqCap pqPtr, h178, h180]
    simp only [sepConj_assoc]
    refine pure_elim_3 fun hpq_pure => ?_
    have hnil_wp := pq_nil_placed_wp (A := A) (lim := lim) ext st s sp coroPtr hpc hrun hsp_eq hx19
    refine bind_sepWP_lscro_state_placed hcro hnil_wp (by sep_focus)
      fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
    rcases hregs1 with ⟨hsp1, htr1_s, hx19_1, hx21_1, hx22_1, hx23_1, hx24_1,
      hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1⟩
    have hsp1_al : s1.spAligned = true := by
      simpa only [State.spAligned, hsp1, ← hsp_eq] using hsp_al
    refine SepWPp.weaken_pre ?_
      (hnext s1 1#64 hpc1 hrun1 hcro1 hsp1 hsp1_al (htr1_s.trans htr)
        hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1
        (hx27_1.trans hx27) (hx28_1.trans hx28) hx29_1 hvregs1)
    rw [hevs, AllocCostModel.stepEvents, List.foldl_nil,
        vecU8At_eq_of_nil A.repAlloc (coroPtr + 0x170#64) pqCap pqPtr, h178, h180,
        segClone_pure_eq_emp hpq_pure]
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat, vecU8Buf_nil_eq A.repAlloc,
      sepConj_assoc, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by sep_ac_rfl)
  · have hne : pqBytes ≠ [] := List.ne_nil_of_length_pos hpos
    have hevs : clonePqEvents pqBytes = rustAllocEvents pqBytes.length 1 := by
      simp [clonePqEvents, hne]
    have hfit_alloc : FitsEvents M lim st (rustAllocEvents pqBytes.length 1) :=
      hevs ▸ (fitsEnv_clonePq_iff pqBytes).mp hfit
    have hallocNoOom := subroutine_ok_allocNoOom_of_budget halloc
    rw [vecU8At_eq_of_pos A.repAlloc (coroPtr + 0x170#64) pqCap pqPtr pqBytes hpos, h178, h180]
    simp only [sepConj_assoc]
    refine pure_elim_3 fun hpq_pure => ?_
    have hlen_le := hpq_pure.1
    have hcap_lt := hpq_pure.2.1
    have hlen_lt : pqBytes.length < 2 ^ 63 := by omega
    have hlen_le63 : pqBytes.length + 1 ≤ 2 ^ 63 := by omega
    have hlay : LayoutOk pqBytes.length 1 := ⟨hpos, ⟨0, rfl⟩, hlen_le63⟩
    have hrlo : RustLayoutOk pqBytes.length 1 := ⟨hlay, by decide⟩
    have htoNat : (BitVec.ofNat 64 pqBytes.length).toNat = pqBytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hprep := pq_pos_prep_placed_wp (A := A) (lim := lim) ext hshim st s sp coroPtr
      pqPtr pqBytes.length hpos hlen_lt hpc hrun hsp_eq hsp_al hx19
    refine bind_sepWP_lscro_state_placed hcro hprep (by sep_focus)
      fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
    rcases hregs1 with ⟨hsp1, htr1_s, hx0_1, hx1_1, hx19_1, hx22_1, hx23_1,
      hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs1_s⟩
    have hsp1_al : s1.spAligned = true := by
      simpa only [State.spAligned, hsp1, ← hsp_eq] using hsp_al
    have htr1 : s1.trace = s0.trace := htr1_s.trans htr
    have hφ : (s1.readReg64 .x0).toNat = pqBytes.length ∧
        (s1.readReg64 .x1).toNat = 1 ∧
        RustLayoutOk pqBytes.length 1 ∧
        FitsEvents M lim st (rustAllocEvents pqBytes.length 1) ∧
        LsRetAddr624 (s1.readReg64 .lr) :=
      ⟨by rw [hx0_1, htoNat], by rw [hx1_1]; rfl, hrlo, hfit_alloc,
       by rw [show s1.readReg64 .lr = (blkPl_518).base + 0x1b88#64 from hx30_1]
          exact lsRetAddr624_blockPlacement_base_add 518 0x1b88#64 (by decide) (by decide)⟩
    refine call_raw_nopanic_placed
      (spec := rustCliAllocNoOomSpec M A lim false)
      (x := (pqBytes.length, 1, st))
      (T := A.pool lim st s1 ∗ stackAt sp allocHookStack)
      hcro1 hallocNoOom hpc1 hrun1 hsp1_al hx30_1
      (by dsimp only [rustCliAllocNoOomSpec]; rw [hsp1])
      hφ (by sep_focus)
      (hnext := fun s2 hpc2 hrun2 hsp2_1 hsp2_al hcs2 hcro2 => ?_)
    have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
    rcases hcs2 with ⟨hx19_cs2, _, _, hx22_cs2, hx23_cs2, hx24_cs2, hx25_cs2,
      hx26_cs2, hx27_cs2, hx28_cs2, hx29_cs2, hvregs2_1⟩
    have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
    have hx22_2 : s2.readReg64 .x22 = s.readReg64 .x22 := hx22_cs2.trans hx22_1
    have hx23_2 : s2.readReg64 .x23 = s.readReg64 .x23 := hx23_cs2.trans hx23_1
    have hx24_2 : s2.readReg64 .x24 = s.readReg64 .x24 := hx24_cs2.trans hx24_1
    have hx25_2 : s2.readReg64 .x25 = s.readReg64 .x25 := hx25_cs2.trans hx25_1
    have hx26_2 : s2.readReg64 .x26 = BitVec.ofNat 64 pqBytes.length := hx26_cs2.trans hx26_1
    have hx27_2 : s2.readReg64 .x27 = pqPtr := hx27_cs2.trans hx27_1
    have hx28_2 : s2.readReg64 .x28 = ctxPtr := hx28_cs2.trans (hx28_1.trans hx27)
    have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hx29_cs2.trans hx29_1
    dsimp only [rustCliAllocNoOomSpec]
    simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    rw [hsp1, ← hevs]
    refine SepWPp.pure_elim fun ⟨hacp2, hoom, _⟩ => ?_
    have htr2 : s2.trace = s0.trace := hacp2.2.1.trans htr1
    set ptr' := s2.readReg64 .x0
    let st' := M.stepEvents (clonePqEvents pqBytes) st
    have hcopy := pq_pos_copy_placed_wp (A := A) (lim := lim) ext hmemcpy st' s2 sp coroPtr
      pqPtr ptr' 32#64 pqBytes hoom hlen_lt hpc2 hrun2 hsp2 hsp2_al rfl hx19_2 hx26_2 hx27_2
    refine bind_sepWP_lscro_state_placed hcro2 hcopy (by sep_focus)
      fun s3 hpc3 hrun3 hcro3 hregs3 => ?_
    rcases hregs3 with ⟨hsp3, htr3_2, hx19_3, hx21_3, hx22_3, hx23_3,
      hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs3_2⟩
    have hsp3_al : s3.spAligned = true := by
      simpa only [State.spAligned, hsp3, ← hsp2] using hsp2_al
    refine SepWPp.weaken_pre ?_
      (hnext s3 ptr' hpc3 hrun3 hcro3 hsp3 hsp3_al (htr3_2.trans htr2)
        hx19_3 hx21_3 (hx22_3.trans hx22_2) (hx23_3.trans hx23_2)
        (hx24_3.trans hx24_2) (hx25_3.trans hx25_2) hx26_3
        (hx27_3.trans hx28_2) hx28_3 (hx29_3.trans hx29_2)
        (hvregs3_2.trans (hvregs2_1.trans hvregs1_s)))
    have hlive_eq : A.live ptr' pqBytes.length 1 =
        A.repAlloc.live ptr' pqBytes.length 1 := rfl
    rw [vecU8At_eq_of_pos A.repAlloc (coroPtr + 0x170#64) pqCap pqPtr pqBytes hpos, h178, h180,
        vecU8Buf_pos_eq A.repAlloc ptr' pqBytes hpos hlen_lt hoom,
        hlive_eq, segClone_pure_eq_emp hpq_pure]
    simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by sep_ac_rfl)

/-! ## 5. Budget-Threaded Placed Segment 4 (`+0x1b20 → +0x1bac`, `genP3J3PlacedBudget → genP3J4PlacedBudget`) -/

private abbrev genP3TailRestFrame [LibsignalPlacement] (A : CryptoVerification.RustHeap.RustAlloc)
    (sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (w : GenP3J3Witness) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) : SepProp :=
  tailSessionRestAt A coroPtr recG st ∗
    memRegion (sp - BitVec.ofNat 64 chainCloneStack) 208 ∗
    memRegion (sp + 0x3e0#64) 104 ∗
    ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
    genP3CallFramePlaced A sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest rem loc msgG msg ∗
    vecU8Buf A (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr recG.localIk.bytes ∗
    vecU8Buf A (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr recG.remoteIk.bytes ∗
    vecU8Buf A 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
    optSenderChainHeap A w.sender' st.senderChain ∗
    vecBuf A 104 8 (chainAt A) (BitVec.ofNat 64 st.receiverChains.length) w.newRcPtr
      (w.chains'.zip st.receiverChains) ∗
    OptPendClone A recG.pending w.pendCap' w.pendPtr' ∗
    OptKybClone A recG.kyber w.kybCap' w.kybPtr' ∗
    ((sp + 0x8#64) ↦₆₄ w.kybPtr') ∗ ((sp + 0x10#64) ↦₆₄ w.d10) ∗
    ((sp + 0x18#64) ↦₆₄ w.pendPtr') ∗ ((sp + 0x24#64) ↦₃₂ w.w24) ∗
    ((sp + 0x28#64) ↦₃₂ w.w28) ∗ ((sp + 0x2c#64) ↦₃₂ w.w2c) ∗
    ((sp + 0x48#64) ↦₆₄ w.c0) ∗ ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
    ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗ ((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
    ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
    ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗ ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
    ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
    genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5

set_option maxHeartbeats 800000 in
private theorem cloneKeysTail_core_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop} (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) memcpy4kBudgetSpec)
    (s0 s : State) (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hfits : FitsEvents M lim stB (cloneKeysTailEvents recG st))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem) (hpc : s.pc = dpClosureEntryM3Placed + 0x1b20#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace) :
    SepWPp (lsProg_518 ext) (dpClosureEntryM3Placed + 0x1bac#64) s
      (genP3J3PlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
        msgVer rest recG st rem loc msgG msg s)
      (fun s1 P_f =>
        (P_f ⊢ genP3J4PlacedBudget A lim (M.stepEvents (cloneKeysTailEvents recG st) stB)
          sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
          recG st rem loc msgG msg s1) ∧
        s1.trace = s0.trace ∧ LibsignalCodeRoLoaded lsmpl s1.mem ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s)
      Qp := by
  have ⟨hfit_alice_ev, hfit_pq_ev⟩ :=
    (fitsEvents_append M lim (cloneAliceEvents recG.alice)
      (clonePqEvents st.pqRatchetState) stB).mp hfits
  have hfit_alice : FitsEnv M lim stB (CloneAliceEnv recG.alice) :=
    (fitsEnv_cloneAlice_iff recG.alice).mpr hfit_alice_ev
  let st1 := M.stepEvents (cloneAliceEvents recG.alice) stB
  have hfit_pq : FitsEnv M lim st1 (ClonePqEnv st.pqRatchetState) :=
    (fitsEnv_clonePq_iff st.pqRatchetState).mpr hfit_pq_ev
  have hst_eq : M.stepEvents (clonePqEvents st.pqRatchetState) st1 =
      M.stepEvents (cloneKeysTailEvents recG st) stB :=
    (M.stepEvents_append (cloneAliceEvents recG.alice)
      (clonePqEvents st.pqRatchetState) stB).symm
  dsimp only [genP3J3PlacedBudget, genP3TailSpillScratch]
  refine SepWPp.exists_elim fun w => SepWPp.pure_elim
    fun ⟨hsp, hx19, hx22, hx23, hx25, hx26, hx27, hx28, hx29, hch_len, hsc_rel, hsc_inl⟩ => ?_
  have hsp_al : s.spAligned = true := by simpa only [State.spAligned, hsp] using hsp_align
  rw [sessionStateAt_tail_eq A.repAlloc coroPtr recG st, stackAt_chainClone_eq_alloc sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun wt => SepWPp.pure_elim fun hss_pure => ?_
  obtain ⟨regW0, regW1, hreg_eq, hreg_pts⟩ := exists_unpack32_pair_of_length_8 hss_pure.2.2.2.2.1
  have h24c : coroPtr + 0x248#64 + 4#64 = coroPtr + 0x24c#64 := by bv_arith
  rw [hreg_pts (coroPtr + 0x248#64), h24c]
  simp only [sepConj_assoc]
  refine SepWPp.weaken_pre
    (P' := A.pool lim stB s ∗ stackAt sp allocHookStack ∗
            vecGhostAt A.repAlloc recG.alice (coroPtr + 0x158#64) ∗
            ((coroPtr + 0x248#64) ↦₃₂ regW0) ∗ ((coroPtr + 0x24c#64) ↦₃₂ regW1) ∗
            ((sp + 0x30#64) ↦₃₂ wt.u_30) ∗ ((sp + 0x34#64) ↦₃₂ wt.u_34) ∗
            ((sp + 0x38#64) ↦₆₄ wt.u_38) ∗ ((sp + 0x40#64) ↦₆₄ wt.u_40) ∗
            (vecU8At A.repAlloc (coroPtr + 0x170#64) recG.pq.cap recG.pq.ptr st.pqRatchetState ∗
              ((sp + 0x98#64) ↦₆₄ 32#64) ∗
              genP3TailRestFrame A.repAlloc sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
                cur msgVer rest w recG st rem loc msgG msg))
    (Entails.of_eq (by dsimp only [genP3TailRestFrame]; sep_ac_rfl)) ?_
  refine cloneAlice_core_placed_ok ext hshim halloc hmemcpy stB s0 s _ _
    sp coroPtr (BitVec.ofNat 64 st.receiverChains.length) w.kybCap' wt.u_38 wt.u_40
    regW0 regW1 wt.u_30 wt.u_34 recG.alice _ hfit_alice hcro hpc hrun hsp hsp_al htr
    hx19 hx23 hx26
    fun s1 newAlicePtr hpc1 hrun1 hcro1 hsp1 hsp1_al htr1
      hx19_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs1 => ?_
  refine SepWPp.weaken_pre
    (P' := A.pool lim st1 s1 ∗ stackAt sp allocHookStack ∗
            vecU8At A.repAlloc (coroPtr + 0x170#64) recG.pq.cap recG.pq.ptr st.pqRatchetState ∗
            ((sp + 0x98#64) ↦₆₄ 32#64) ∗
            (vecGhostAt A.repAlloc recG.alice (coroPtr + 0x158#64) ∗
              vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.alice.bytes.length) newAlicePtr
                recG.alice.bytes ∗
              ((coroPtr + 0x248#64) ↦₃₂ regW0) ∗ ((coroPtr + 0x24c#64) ↦₃₂ regW1) ∗
              ((sp + 0x30#64) ↦₃₂ regW0) ∗ ((sp + 0x34#64) ↦₃₂ regW1) ∗
              ((sp + 0x38#64) ↦₆₄ w.kybCap') ∗
              ((sp + 0x40#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
              genP3TailRestFrame A.repAlloc sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
                cur msgVer rest w recG st rem loc msgG msg))
    (Entails.of_eq (by dsimp only [genP3TailRestFrame]; sep_ac_rfl)) ?_
  refine clonePq_core_placed_ok ext hshim halloc hmemcpy st1 s0 s1 _ _
    sp coroPtr recG.pq.cap recG.pq.ptr ctxPtr st.pqRatchetState _ hfit_pq hcro1 hpc1 hrun1
    hsp1 hsp1_al htr1 hx19_1 (hx27_1.trans hx27) (hx28_1.trans hx28)
    fun sf newPqPtr hpcf hrunf hcrof hspf _hspf_al htrf
      hx19_f hx21_f hx22_f hx23_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f hvregsf => ?_
  refine sepWPp_done hpcf hrunf ⟨?_, htrf, hcrof, hvregsf.trans hvregs1⟩
  rw [hst_eq]
  let w' : GenP3J4Witness :=
    { toGenP3J3Witness := w, newAlicePtr := newAlicePtr, newPqPtr := newPqPtr,
      regW0 := regW0, regW1 := regW1 }
  refine Entails.sepExists_right w' ?_
  apply Entails.pure_right
    ⟨hspf, hx19_f, hx21_f,
     hx22_f.trans (hx22_1.trans hx22),
     hx23_f.trans hx23_1,
     hx24_f.trans hx24_1,
     hx25_f.trans (hx25_1.trans hx25),
     hx26_f, hx27_f, hx28_f,
     hx29_f.trans (hx29_1.trans hx29),
     hreg_eq, hch_len, hsc_rel, hsc_inl⟩
  dsimp only [genP3J4PlacedBudget, genP3TailRestFrame, w']
  rw [sessionStateAt_tail_eq A.repAlloc coroPtr recG st, hreg_pts (coroPtr + 0x248#64), h24c,
      stackAt_chainClone_eq_alloc sp]
  simp only [sepConj_assoc]
  apply Entails.pure_right hss_pure
  exact Entails.of_eq (by sep_ac_rfl)

/-- Budget-threaded Placed Segment 4 (`stepEvents` form, `+0x1b20 → +0x1bac`): Advances `genP3J3PlacedBudget` to `genP3J4PlacedBudget` on `lsProg_518 ext` with exact event
folding `M.stepEvents (cloneKeysTailEvents recG st) stB` and polymorphic `Qp`. -/
theorem cloneKeysTail_vregs_placed_ok_stepEvents [LibsignalPlacement]
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
    (_hsp_root : rootStack ≤ sp.toNat)
    (hfits : FitsEvents M lim stB (cloneKeysTailEvents recG st))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem) (hpc : s.pc = dpClosureEntryM3Placed + 0x1b20#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace) :
    SepWPp (lsProg_518 ext) (dpClosureEntryM3Placed + 0x1bac#64) s
      (genP3J3PlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
        msgVer rest recG st rem loc msgG msg s)
      (fun s1 P_f =>
        (P_f ⊢ genP3J4PlacedBudget A lim (M.stepEvents (cloneKeysTailEvents recG st) stB)
          sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
          recG st rem loc msgG msg s1) ∧
        s1.trace = s0.trace ∧ LibsignalCodeRoLoaded lsmpl s1.mem ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s)
      Qp :=
  cloneKeysTail_core_placed_ok ext (subroutine_ok_noAllocShim_of_sessionShimBudget hshim) halloc
    (memcpy4kBudget_of_region hmemcpy) s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
    whisperMsgPtr cur msgVer rest recG st rem loc msgG msg hsp_align hfits hcro hpc hrun htr

/-- Budget-threaded Placed Segment 4 with `calleeSavedVRegs` (`+0x1b20 → +0x1bac`,
`genP3J3PlacedBudget → genP3J4PlacedBudget`): envelope form (`CloneKeysTailEnv`). -/
theorem cloneKeysTail_vregs_placed_ok [LibsignalPlacement]
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
    (hsp_root : rootStack ≤ sp.toNat)
    (hfits : FitsEnv M lim stB (CloneKeysTailEnv recG st))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem) (hpc : s.pc = dpClosureEntryM3Placed + 0x1b20#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace) :
    SepWPp (lsProg_518 ext) (dpClosureEntryM3Placed + 0x1bac#64) s
      (genP3J3PlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
        msgVer rest recG st rem loc msgG msg s)
      (fun s1 P_f =>
        ∃ evs : List AllocEvent, CloneKeysTailEnv recG st evs ∧
          (P_f ⊢ genP3J4PlacedBudget A lim (M.stepEvents evs stB)
            sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
            recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧ LibsignalCodeRoLoaded lsmpl s1.mem ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
      Qp :=
  sepWPp_weaken_post
    (cloneKeysTail_vregs_placed_ok_stepEvents ext hshim halloc hmemcpy s0 s sp fp coroPtr ctxPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg hrc_len
      hsp_align hsp_root (fitsEvents_cloneKeysTail_of_fitsEnv M lim stB recG st hfits) hcro hpc
      hrun htr)
    fun _ _ ⟨hent1, htr1, hcro1, hv1⟩ => ⟨cloneKeysTailEvents recG st, rfl, hent1, htr1, hcro1, hv1⟩

/-- 4K-stack variant of `cloneKeysTail_vregs_placed_ok` accepting
`sessionMemcpyBudgetSpec allocHookStack` directly. -/
theorem cloneKeysTail_vregs_4k_placed_ok [LibsignalPlacement]
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
    (_hsp_root : rootStack ≤ sp.toNat)
    (hfits : FitsEnv M lim stB (CloneKeysTailEnv recG st))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem) (hpc : s.pc = dpClosureEntryM3Placed + 0x1b20#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace) :
    SepWPp (lsProg_518 ext) (dpClosureEntryM3Placed + 0x1bac#64) s
      (genP3J3PlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
        msgVer rest recG st rem loc msgG msg s)
      (fun s1 P_f =>
        ∃ evs : List AllocEvent, CloneKeysTailEnv recG st evs ∧
          (P_f ⊢ genP3J4PlacedBudget A lim (M.stepEvents evs stB)
            sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
            recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧ LibsignalCodeRoLoaded lsmpl s1.mem ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
      Qp :=
  sepWPp_weaken_post
    (cloneKeysTail_core_placed_ok ext (subroutine_ok_noAllocShim_of_sessionShimBudget hshim) halloc
      (memcpy4kBudget_of_4k hmemcpy) s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
      cur msgVer rest recG st rem loc msgG msg hsp_align
      (fitsEvents_cloneKeysTail_of_fitsEnv M lim stB recG st hfits) hcro hpc hrun htr)
    fun _ _ ⟨hent1, htr1, hcro1, hv1⟩ => ⟨cloneKeysTailEvents recG st, rfl, hent1, htr1, hcro1, hv1⟩

/-- VM-hook entry variant accepting `rustAllocShimVmSpec` and `allocMemcpyVmSpec` directly. -/
theorem cloneKeysTail_vregs_vmHooks_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop} (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) allocMemcpyVmSpec)
    (s0 s : State) (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (hrc_len : st.receiverChains.length < 2 ^ 32) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hsp_root : rootStack ≤ sp.toNat)
    (hfits : FitsEnv M lim stB (CloneKeysTailEnv recG st))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem) (hpc : s.pc = dpClosureEntryM3Placed + 0x1b20#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace) :
    SepWPp (lsProg_518 ext) (dpClosureEntryM3Placed + 0x1bac#64) s
      (genP3J3PlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
        msgVer rest recG st rem loc msgG msg s)
      (fun s1 P_f =>
        ∃ evs : List AllocEvent, CloneKeysTailEnv recG st evs ∧
          (P_f ⊢ genP3J4PlacedBudget A lim (M.stepEvents evs stB)
            sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
            recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧ LibsignalCodeRoLoaded lsmpl s1.mem ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
      Qp :=
  cloneKeysTail_vregs_placed_ok ext
    (subroutine_ok_sessionShimBudget_of_rustAllocShimVm hshim) halloc
    (subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm hmemcpy)
    s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
    recG st rem loc msgG msg hrc_len hsp_align hsp_root hfits hcro hpc hrun htr

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysTailPlacedBudget
