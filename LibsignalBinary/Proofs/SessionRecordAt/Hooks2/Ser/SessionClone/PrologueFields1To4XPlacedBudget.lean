/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.BaseBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.BaseX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneBaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneEpilogue
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.PrologueFields1To4
meta import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.PrologueFields1To4
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.PrologueFields1To4XPlaced
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `SessionStructure::clone`: Prologue and Fields 1–4 (Block `80`)

Verifies the prologue (`+0 → +32`) and cloning of `local_identity_public`,
`remote_identity_public`, `root_key`, and `sender_chain` (`+32 → +572 / +336`) in Block `80` under
`RustCliAllocBudget M` and `FitsEvents`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.PrologueFields1To4XPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp ProofLib.ProgramReflection
open CryptoGames.HMAC (keyToBytes32)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded lsmpl lsρ
  lsRustNoAllocShimSym lsRustAllocSym lsMemcpySym
  withLsCl withLsCodeLoaded withMemEq
)
open CryptoVerification.RustHeap (vecU8At vecU8Buf)
open CryptoVerification.LibsignalSessionRepr (VecGhost vecGhostAt)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SenderChainGhost optSenderChainAt noneCap
)
open CryptoVerification.LibsignalTripleRatchet (extHookStack sessionMemcpySpec)
open CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1 (chainCloneStackX)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (
  OptSenderChainInline bytes104OfW6Q optSenderChainHeap chunks96_6QAt
  optSenderChainAt_entails_chunks104W6Q
)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps (
  vecGhostAt_eq_of_nil vecGhostAt_eq_of_pos
  vecU8Buf_nil_eq vecU8Buf_pos_eq vecU8At_eq_of_pos vecU8Buf_pure_extract
  eq_nil_or_length_pos ofNat_ne_zero_of_pos beq_ofNat_zero_eq_false
  segClone_pure_eq_emp segClone_setWidth_64_truncate_32
  optSenderChainAt_some_eq_cap optSenderChainSomeRest cat128_extractLsb
  cap_add_one_ne_zero cap_add_one_beq_zero_eq_false
  pointsTo128_eq_pointsTo64 chunks104W6QAt_entails_memRegion
)
open CryptoVerification.E2E.Record.Placed (lsProg_80 blkPl_80 blkPl_82)
open CryptoVerification.E2E.Record.Serialization (
  SessionCloneGhost encSenderFieldMem encChainMem senderGhostAsChain
)
open CryptoVerification.E2E.Record.Serialization.SessionCloneAux (
  ScSavedVals scSavedRegsAt sepWPp_of_sepWP_lscl_sc
  chunks96_6QAt_sp_0x90 chunks104W6QAt_sp_0xf8
  sc_vecGhostAt_0x18_eq sc_vecU8At_0x30_root_eq
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
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (vecCloneEvents)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (SepWPpLsCl)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneBaseXBudget (
  senderChainCloneEvents SenderChainCloneEnv senderChainCloneSpecX
  SenderChainCloneLocal1PlacedOkX
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

private theorem sepWPp_pure_2nd_pf {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {P Q_post : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (P ∗ Q_post) Q Qp) :
    SepWPp prog ret s (P ∗ ⌜φ⌝ ∗ Q_post) Q Qp := by
  refine SepWPp.weaken_pre (P' := ⌜φ⌝ ∗ (P ∗ Q_post))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  exact SepWPp.pure_elim h

private theorem sepWPpLsCl_pure_2nd_pf {pl : Obj.MultiPlacement} {prog : Program}
    {ret : BitVec 64} {s : State}
    {φ : Prop} {P Q_post : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPpLsCl pl prog ret s (P ∗ Q_post) Q Qp) :
    SepWPpLsCl pl prog ret s (P ∗ ⌜φ⌝ ∗ Q_post) Q Qp :=
  fun hcl => sepWPp_pure_2nd_pf fun hφ => h hφ hcl

private theorem shim_vm_ok_at_stateX {pl : Obj.MultiPlacement} {prog : Program}
    {entry : BitVec 64} {s : State}
    (hshim : subroutine_ok prog entry (withLsCl pl session2ShimBudgetSpecX))
    (hcl : LibsignalCodeLoaded pl s.mem) :
    subroutine_ok prog entry
      { pre := fun (_ : Unit) s' => ⌜s'.mem = s.mem⌝ ∗ stackAt s'.sp extHookStack
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
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = dst ∧ s'.readReg64 .x1 = src ∧
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

/-- Allocation events emitted by Field 4 (`sender_chain`). -/
def scSenderEvents (x : SessionCloneGhost) : List AllocEvent :=
  match x.G.sender, x.s.state.senderChain with
  | some gs, some sc => senderChainCloneEvents gs sc
  | _, _ => []

/-- Allocation events emitted across Fields 1–4 (`local_identity_public`,
`remote_identity_public`, `root_key`, `sender_chain`). -/
def scFields1To4Events (x : SessionCloneGhost) : List AllocEvent :=
  vecCloneEvents x.G.localIk ++ vecCloneEvents x.G.remoteIk ++
    rustAllocEvents 32 1 ++ scSenderEvents x

private theorem fitsEvents_split {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {e1 e2 : List AllocEvent} (h : FitsEvents M lim st (e1 ++ e2)) :
    FitsEvents M lim st e1 ∧ FitsEvents M lim (M.stepEvents e1 st) e2 :=
  (fitsEvents_append M lim e1 e2 st).mp h

/-! ## Prologue (`+0 → +32`) -/

/-- Budget-threaded prologue (`+0 → +32`) on `lsProg_80 H`. -/
theorem sc_prologue_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {x : SessionCloneGhost} {st : M.σ} {s0 : State} {ret : BitVec 64}
    {Q Qp : State → SepProp → Prop} {rv : ScSavedVals} {F : SepProp}
    (hpc : s0.pc = (blkPl_80).base)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.dst) (hx1 : s0.readReg64 .x1 = x.src)
    (hnext : ∀ s1 : State,
      s1.pc = (blkPl_80).base + 32#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 0x1d0#64 →
      s1.spAligned = true →
      s1.readReg64 .x0 = x.dst →
      s1.readReg64 .x1 = x.src →
      s1.readReg64 .x29 = s1.sp + 0x170#64 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPpLsCl lsmpl (lsProg_80 H) ret s1
        (A.pool lim st s1 ∗
          scSavedRegsAt (s0.sp - 0x1d0#64)
            (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
            (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
            (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s0
      (A.pool lim st s0 ∗
        scSavedRegsAt (s0.sp - 0x1d0#64)
          rv.r29 rv.r30 rv.r28 rv.r27 rv.r26 rv.r25 rv.r24 rv.r23 rv.r22 rv.r21 rv.r20 rv.r19 ∗ F)
      Q Qp := by
  intro hcl
  dsimp only [scSavedRegsAt]
  simp only [sepConj_assoc]
  apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_80).base + 32#64)
  wp_steps_sync_pool ((blkPl_80).base + 32#64)
  refine SepWP.done (by sc_close) (by sc_close) fun hcl1 => ?_
  refine SepWPp.weaken_pre ?_
    (hnext _ (by sc_close) (by sc_close) (by sc_close) (by sc_close)
      (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close) hcl1)
  dsimp only [scSavedRegsAt, Reg.x29, Reg.x30, Reg.x28, Reg.x27, Reg.x26, Reg.x25,
    Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]
  simp only [sepConj_assoc]
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## Field 1: `local_identity_public` (`+32 → +208 / +100`) -/

/-- Budget-threaded `local_identity_public` clone (`+32 → +208 / +100`) on `lsProg_80 H`. -/
theorem sc_localIk_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsPlaced M A lim H)
    (hmemcpy : subroutine_ok (lsProg_80 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (withVmPreserved (sessionMemcpySpec extHookStack))))
    {x : SessionCloneGhost} {st : M.σ} {s0 s : State} {ret : BitVec 64}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (hfits : FitsEvents M lim st (vecCloneEvents x.G.localIk))
    (hpc : s.pc = (blkPl_80).base + 32#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = x.dst) (hx1 : s.readReg64 .x1 = x.src)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (localIk' : VecGhost),
      s1.pc = (if x.G.remoteIk.bytes = []
        then (blkPl_80).base + 208#64
        else (blkPl_80).base + 100#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = x.dst →
      s1.readReg64 .x21 = localIk'.cap →
      s1.readReg64 .x22 = x.s.state.sessionVersion.setWidth 64 →
      s1.readReg64 .x23 = localIk'.ptr →
      s1.readReg64 .x24 = BitVec.ofNat 64 x.G.remoteIk.bytes.length →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      localIk'.bytes = x.G.localIk.bytes →
      localIk'.cap = BitVec.ofNat 64 x.G.localIk.bytes.length →
      SepWPpLsCl lsmpl (lsProg_80 H) ret s1
        (A.pool lim (M.stepEvents (vecCloneEvents x.G.localIk) st) s1 ∗
          vecGhostAt A.repAlloc x.G.localIk x.src ∗
          vecU8Buf A.repAlloc localIk'.cap localIk'.ptr localIk'.bytes ∗
          ((x.src + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
          ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
          stackAt s.sp extHookStack ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s
      (A.pool lim st s ∗ vecGhostAt A.repAlloc x.G.localIk x.src ∗
        ((x.src + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
        ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
        stackAt s.sp extHookStack ∗ F)
      Q Qp := by
  intro hcl
  rcases eq_nil_or_length_pos x.G.localIk.bytes with hloc | hloc
  · have hev : vecCloneEvents x.G.localIk = [] := by simp [vecCloneEvents, hloc]
    rw [hev, M.stepEvents_nil] at hnext
    rw [vecGhostAt_eq_of_nil A.repAlloc x.G.localIk x.src hloc]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd_pf fun ⟨hcap_lt, hptr⟩ => ?_
    have hpc_rem :
        (if ¬(BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = true then (blkPl_80).base + 100#64 else (blkPl_80).base + 208#64) =
        (if x.G.remoteIk.bytes = [] then (blkPl_80).base + 208#64 else (blkPl_80).base + 100#64) := by
      rcases eq_nil_or_length_pos x.G.remoteIk.bytes with hrem | hrem
      · simp [hrem]
      · have hne : x.G.remoteIk.bytes ≠ [] := List.ne_nil_of_length_pos hrem
        have hbeq : (BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = false :=
          beq_ofNat_zero_eq_false hrem (by omega)
        simp [hne, hbeq]
    apply sepWPp_of_sepWP_lscl_sc hcl
      (mid := if x.G.remoteIk.bytes = [] then (blkPl_80).base + 208#64 else (blkPl_80).base + 100#64)
    wp_steps_sync_pool (if x.G.remoteIk.bytes = [] then (blkPl_80).base + 208#64 else (blkPl_80).base + 100#64)
    refine SepWP.done (by sc_close) (by sc_close) fun hcl1 => ?_
    refine SepWPp.weaken_pre ?_
      (hnext _ ⟨0#64, 1#64, []⟩ (by sc_close) (by sc_close) rfl hsp
        rfl rfl rfl rfl rfl rfl rfl htr (by sc_close) hloc.symm (by simp [hloc]) hcl1)
    have hpure : (⌜x.G.localIk.cap.toNat < 2 ^ 63 ∧ x.G.localIk.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hcap_lt, hptr⟩
    rw [vecGhostAt_eq_of_nil A.repAlloc x.G.localIk x.src hloc, vecU8Buf_nil_eq A.repAlloc, hpure]
    simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by sep_ac_rfl)
  · have hev : vecCloneEvents x.G.localIk = rustAllocEvents x.G.localIk.bytes.length 1 := by
      simp [vecCloneEvents, Nat.ne_of_gt hloc]
    rw [hev] at hfits hnext
    rw [vecGhostAt_eq_of_pos A.repAlloc x.G.localIk x.src hloc]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd_pf fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
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
    apply sepWPp_of_sepWP_lscl_sc hcl (mid := lsρ lsRustNoAllocShimSym)
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
    apply SepWP.done (by rfl) (by sc_close)
    intro hcl_shim
    have hshim_state := shim_vm_ok_at_stateX (hA.shim (callerProg := lsProg_80 H)) hcl_shim
    apply sepWPp_of_sepWP_lscl_sc hcl_shim (mid := lsρ lsRustAllocSym)
    wp_call hshim_state ()
    refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
    wp_steps_sync_pool (lsρ lsRustAllocSym)
    apply SepWP.done (by rfl) (by sc_close)
    intro hcl_alloc
    have halloc_state := allocNoOom_ok_at_stateX hA hcl_alloc
    apply sepWPp_of_sepWP_lscl_sc hcl_alloc (mid := lsρ lsMemcpySym)
    wp_call halloc_state (x.G.localIk.bytes.length, 1, st)
    clear halloc_state
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹_›
    have hoom : ¬ (sf_1.readReg64 (Reg.gpr 0#5) = 0) := hoom64
    wp_steps_sync_pool (lsρ lsMemcpySym)
    apply SepWP.done (by rfl) (by sc_close)
    intro hcl_memcpy
    have hpc_rem :
        (if (BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = true then (blkPl_80).base + 208#64 else (blkPl_80).base + 100#64) =
        (if x.G.remoteIk.bytes = [] then (blkPl_80).base + 208#64 else (blkPl_80).base + 100#64) := by
      rcases eq_nil_or_length_pos x.G.remoteIk.bytes with hrem | hrem
      · simp [hrem]
      · have hne : x.G.remoteIk.bytes ≠ [] := List.ne_nil_of_length_pos hrem
        have hbeq : (BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = false :=
          beq_ofNat_zero_eq_false hrem (by omega)
        simp [hne, hbeq]
    have hmemcpy_state := memcpy_vm_ok_at_stateX hmemcpy hcl_memcpy
    apply sepWPp_of_sepWP_lscl_sc hcl_memcpy
      (mid := if x.G.remoteIk.bytes = [] then (blkPl_80).base + 208#64 else (blkPl_80).base + 100#64)
    wp_call hmemcpy_state (sf_1.readReg64 (Reg.gpr 0#5), x.G.localIk.ptr, x.G.localIk.bytes)
    clear hmemcpy_state
    refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
    wp_steps_sync_pool (if x.G.remoteIk.bytes = [] then (blkPl_80).base + 208#64 else (blkPl_80).base + 100#64)
    refine SepWP.done (by sc_close) (by sc_close) fun hcl_done => ?_
    have htr_sf2 : sf_2.trace = s0.trace := by
      have htr1 : sf_1.trace = sf.trace := (‹AllocCallPreserved sf sf_1›).2.1
      have htr0 : sf.trace = s.trace := ‹_›
      have htr2 : sf_2.trace = sf_1.trace := ‹_›
      exact htr2.trans (htr1.trans (htr0.trans htr))
    refine SepWPp.weaken_pre ?_
      (hnext _ ⟨BitVec.ofNat 64 x.G.localIk.bytes.length, sf_1.readReg64 (Reg.gpr 0#5), x.G.localIk.bytes⟩
        (by sc_close) (by sc_close) (by sc_close) (by sc_close)
        (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close)
        (by sc_close) (by simp [wp_norm, arm64_norm, htr_sf2]) (by sc_close) rfl rfl hcl_done)
    have hpure : (⌜x.G.localIk.bytes.length ≤ x.G.localIk.cap.toNat ∧
        x.G.localIk.cap.toNat < 2 ^ 63 ∧ x.G.localIk.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
    rw [vecGhostAt_eq_of_pos A.repAlloc x.G.localIk x.src hloc,
        vecU8Buf_pos_eq A.repAlloc (sf_1.readReg64 (Reg.gpr 0#5)) x.G.localIk.bytes hloc hloc_lt hoom64,
        hpure]
    have hsp_eq : sf_1.sp = s.sp := by sc_close
    simp only [sepConj_assoc, hsp_eq, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by sep_ac_rfl)

/-! ## Field 2: `remote_identity_public` (`+208 / +100 → +152`) -/

/-- Budget-threaded `remote_identity_public` clone (`+208 / +100 → +152`) on `lsProg_80 H`. -/
theorem sc_remoteIk_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsPlaced M A lim H)
    (hmemcpy : subroutine_ok (lsProg_80 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (withVmPreserved (sessionMemcpySpec extHookStack))))
    {x : SessionCloneGhost} {st : M.σ} {s0 s : State} {ret : BitVec 64}
    {Q Qp : State → SepProp → Prop} {v88 : BitVec 64} {F : SepProp}
    (hfits : FitsEvents M lim st (vecCloneEvents x.G.remoteIk))
    (hpc : s.pc = (if x.G.remoteIk.bytes = []
      then (blkPl_80).base + 208#64
      else (blkPl_80).base + 100#64))
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 x.G.remoteIk.bytes.length)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (remoteIk' : VecGhost),
      s1.pc = (blkPl_80).base + 152#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = remoteIk'.cap →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = remoteIk'.ptr →
      s1.readReg64 .x27 = 32#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      remoteIk'.bytes = x.G.remoteIk.bytes →
      remoteIk'.cap = BitVec.ofNat 64 x.G.remoteIk.bytes.length →
      SepWPpLsCl lsmpl (lsProg_80 H) ret s1
        (A.pool lim (M.stepEvents (vecCloneEvents x.G.remoteIk) st) s1 ∗
          vecGhostAt A.repAlloc x.G.remoteIk (x.src + 0x18#64) ∗
          vecU8Buf A.repAlloc remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
          ((x.src + 0x40#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0x88#64) ↦₆₄ s.readReg64 .x21) ∗
          stackAt s.sp extHookStack ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s
      (A.pool lim st s ∗ vecGhostAt A.repAlloc x.G.remoteIk (x.src + 0x18#64) ∗
        ((x.src + 0x40#64) ↦₆₄ 32#64) ∗
        ((s.sp + 0x88#64) ↦₆₄ v88) ∗
        stackAt s.sp extHookStack ∗ F)
      Q Qp := by
  intro hcl
  have h20 : x.src + 0x18#64 + 8#64 = x.src + 0x20#64 := by bv_arith
  have h28 : x.src + 0x18#64 + 16#64 = x.src + 0x28#64 := by bv_arith
  rcases eq_nil_or_length_pos x.G.remoteIk.bytes with hrem | hrem
  · have hev : vecCloneEvents x.G.remoteIk = [] := by simp [vecCloneEvents, hrem]
    rw [hev, M.stepEvents_nil] at hnext
    simp only [hrem, ↓reduceIte] at hpc
    rw [hrem] at hx24
    rw [vecGhostAt_eq_of_nil A.repAlloc x.G.remoteIk (x.src + 0x18#64) hrem, h20, h28]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd_pf fun ⟨hcap_lt, hptr⟩ => ?_
    apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_80).base + 152#64)
    wp_steps_sync_pool ((blkPl_80).base + 152#64)
    refine SepWP.done rfl (by sc_close) fun hcl1 => ?_
    refine SepWPp.weaken_pre ?_
      (hnext _ ⟨0#64, 1#64, []⟩ rfl (by sc_close) rfl hsp
        rfl rfl rfl rfl hx24 hx25 rfl rfl rfl htr (by sc_close)
        hrem.symm (by simp [hrem]) hcl1)
    have hpure : (⌜x.G.remoteIk.cap.toNat < 2 ^ 63 ∧ x.G.remoteIk.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hcap_lt, hptr⟩
    rw [vecGhostAt_eq_of_nil A.repAlloc x.G.remoteIk (x.src + 0x18#64) hrem, h20, h28,
        vecU8Buf_nil_eq A.repAlloc, hpure]
    simp only [sepConj_assoc, emp_sepConj, sepConj_emp, Reg.x21]
    exact Entails.of_eq (by sep_ac_rfl)
  · have hrem_ne_nil : x.G.remoteIk.bytes ≠ [] := List.ne_nil_of_length_pos hrem
    have hev : vecCloneEvents x.G.remoteIk = rustAllocEvents x.G.remoteIk.bytes.length 1 := by
      simp [vecCloneEvents, Nat.ne_of_gt hrem]
    rw [hev] at hfits hnext
    simp only [hrem_ne_nil, ↓reduceIte] at hpc
    rw [vecGhostAt_eq_of_pos A.repAlloc x.G.remoteIk (x.src + 0x18#64) hrem, h20, h28]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd_pf fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63 := by omega
    have hrem_le63 : x.G.remoteIk.bytes.length + 1 ≤ 2 ^ 63 := by omega
    have hrem_le64 : x.G.remoteIk.bytes.length ≤ 2 ^ 64 := by omega
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : RustLayoutOk x.G.remoteIk.bytes.length 1 := ⟨⟨hrem, hpow2, hrem_le63⟩, by decide⟩
    have htoNat : (BitVec.ofNat 64 x.G.remoteIk.bytes.length).toNat = x.G.remoteIk.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    apply sepWPp_of_sepWP_lscl_sc hcl (mid := lsρ lsRustNoAllocShimSym)
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
    apply SepWP.done (by rfl) (by sc_close)
    intro hcl_shim
    have hshim_state := shim_vm_ok_at_stateX (hA.shim (callerProg := lsProg_80 H)) hcl_shim
    apply sepWPp_of_sepWP_lscl_sc hcl_shim (mid := lsρ lsRustAllocSym)
    wp_call hshim_state ()
    refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
    wp_steps_sync_pool (lsρ lsRustAllocSym)
    apply SepWP.done (by rfl) (by sc_close)
    intro hcl_alloc
    have halloc_state := allocNoOom_ok_at_stateX hA hcl_alloc
    apply sepWPp_of_sepWP_lscl_sc hcl_alloc (mid := lsρ lsMemcpySym)
    wp_call halloc_state (x.G.remoteIk.bytes.length, 1, st)
    clear halloc_state
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹_›
    have hoom : ¬ (sf_1.readReg64 (Reg.gpr 0#5) = 0) := hoom64
    wp_steps_sync_pool (lsρ lsMemcpySym)
    apply SepWP.done (by rfl) (by sc_close)
    intro hcl_memcpy
    have hmemcpy_state := memcpy_vm_ok_at_stateX hmemcpy hcl_memcpy
    apply sepWPp_of_sepWP_lscl_sc hcl_memcpy (mid := (blkPl_80).base + 152#64)
    wp_call hmemcpy_state (sf_1.readReg64 (Reg.gpr 0#5), x.G.remoteIk.ptr, x.G.remoteIk.bytes)
    clear hmemcpy_state
    refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
    wp_steps_sync_pool ((blkPl_80).base + 152#64)
    refine SepWP.done (by sc_close) (by sc_close) fun hcl_done => ?_
    have htr_sf2 : sf_2.trace = s0.trace := by
      have htr1 : sf_1.trace = sf.trace := (‹AllocCallPreserved sf sf_1›).2.1
      have htr0 : sf.trace = s.trace := ‹_›
      have htr2 : sf_2.trace = sf_1.trace := ‹_›
      exact htr2.trans (htr1.trans (htr0.trans htr))
    have h21_eq : sf.readReg64 (Reg.gpr 21#5) = s.readReg64 .x21 := by sc_close
    refine SepWPp.weaken_pre ?_
      (hnext _ ⟨BitVec.ofNat 64 x.G.remoteIk.bytes.length, sf_1.readReg64 (Reg.gpr 0#5), x.G.remoteIk.bytes⟩
        (by sc_close) (by sc_close) (by sc_close) (by sc_close)
        (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close)
        (by sc_close) (by sc_close) (by sc_close) (by simp [wp_norm, arm64_norm, htr_sf2]) (by sc_close) rfl rfl hcl_done)
    have hpure : (⌜x.G.remoteIk.bytes.length ≤ x.G.remoteIk.cap.toNat ∧
        x.G.remoteIk.cap.toNat < 2 ^ 63 ∧ x.G.remoteIk.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
    rw [vecGhostAt_eq_of_pos A.repAlloc x.G.remoteIk (x.src + 0x18#64) hrem, h20, h28,
        vecU8Buf_pos_eq A.repAlloc (sf_1.readReg64 (Reg.gpr 0#5)) x.G.remoteIk.bytes hrem hrem_lt hoom64,
        hpure]
    have hsp_eq : sf_1.sp = s.sp := by sc_close
    simp only [sepConj_assoc, hsp_eq, h21_eq, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by sep_ac_rfl)

/-! ## Field 3: `root_key` (`+152 → +232`) -/

/-- Budget-threaded `root_key` clone (`+152 → +232`) on `lsProg_80 H`. -/
theorem sc_rootKey_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsPlaced M A lim H)
    (hmemcpy : subroutine_ok (lsProg_80 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (withVmPreserved (sessionMemcpySpec extHookStack))))
    {x : SessionCloneGhost} {st : M.σ} {s0 s : State} {ret : BitVec 64}
    {Q Qp : State → SepProp → Prop} {v58 : BitVec 64} {F : SepProp}
    (hfits : FitsEvents M lim st (rustAllocEvents 32 1))
    (hpc : s.pc = (blkPl_80).base + 152#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = x.src) (hx27 : s.readReg64 .x27 = 32#64)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (rootPtr' : BitVec 64),
      s1.pc = (blkPl_80).base + 232#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = 32#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPpLsCl lsmpl (lsProg_80 H) ret s1
        (A.pool lim (M.stepEvents (rustAllocEvents 32 1) st) s1 ∗
          vecU8At A.repAlloc (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
          vecU8Buf A.repAlloc 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
          ((s.sp + 0x58#64) ↦₆₄ rootPtr') ∗
          stackAt s.sp extHookStack ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s
      (A.pool lim st s ∗
        vecU8At A.repAlloc (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
        ((s.sp + 0x58#64) ↦₆₄ v58) ∗
        stackAt s.sp extHookStack ∗ F)
      Q Qp := by
  intro hcl
  have h38 : x.src + 0x30#64 + 8#64 = x.src + 0x38#64 := by bv_arith
  have h40 : x.src + 0x30#64 + 16#64 = x.src + 0x40#64 := by bv_arith
  have hroot_len : (keyToBytes32 x.s.state.rootKey).length = 32 := by simp [keyToBytes32]
  have hroot_pos : 0 < (keyToBytes32 x.s.state.rootKey).length := by omega
  have hroot_lt : (keyToBytes32 x.s.state.rootKey).length < 2 ^ 63 := by omega
  have hroot_le64 : (keyToBytes32 x.s.state.rootKey).length ≤ 2 ^ 64 := by omega
  rw [vecU8At_eq_of_pos A.repAlloc (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) hroot_pos,
      h38, h40]
  simp only [sepConj_assoc]
  refine sepWPp_pure_2nd_pf fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
  have h32_pos : 0 < 32 := by decide
  have h32_le63 : 32 + 1 ≤ 2 ^ 63 := by decide
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : RustLayoutOk 32 1 := ⟨⟨h32_pos, hpow2, h32_le63⟩, by decide⟩
  have ⟨⟨_, henf, hcap_fit, hva_fit⟩, _⟩ := hfits
  apply sepWPp_of_sepWP_lscl_sc hcl (mid := lsρ lsRustNoAllocShimSym)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  apply SepWP.done (by rfl) (by sc_close)
  intro hcl_shim
  have hshim_state := shim_vm_ok_at_stateX (hA.shim (callerProg := lsProg_80 H)) hcl_shim
  apply sepWPp_of_sepWP_lscl_sc hcl_shim (mid := lsρ lsRustAllocSym)
  wp_call hshim_state ()
  refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  apply SepWP.done (by rfl) (by sc_close)
  intro hcl_alloc
  have halloc_state := allocNoOom_ok_at_stateX hA hcl_alloc
  apply sepWPp_of_sepWP_lscl_sc hcl_alloc (mid := lsρ lsMemcpySym)
  wp_call halloc_state (32, 1, st)
  clear halloc_state
  have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹_›
  have hoom : ¬ (sf_1.readReg64 (Reg.gpr 0#5) = 0) := hoom64
  have hmem32 :
      memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
        memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (keyToBytes32 x.s.state.rootKey).length := by
    rw [hroot_len]
  rw [hmem32]
  wp_steps_sync_pool (lsρ lsMemcpySym)
  apply SepWP.done (by rfl) (by sc_close)
  intro hcl_memcpy
  have hmemcpy_state := memcpy_vm_ok_at_stateX hmemcpy hcl_memcpy
  apply sepWPp_of_sepWP_lscl_sc hcl_memcpy (mid := (blkPl_80).base + 232#64)
  wp_call hmemcpy_state (sf_1.readReg64 (Reg.gpr 0#5), x.G.root.ptr, keyToBytes32 x.s.state.rootKey)
  clear hmemcpy_state
  refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
  wp_steps_sync_pool ((blkPl_80).base + 232#64)
  refine SepWP.done (by sc_close) (by sc_close) fun hcl_done => ?_
  have htr_sf2 : sf_2.trace = s0.trace := by
    have htr1 : sf_1.trace = sf.trace := (‹AllocCallPreserved sf sf_1›).2.1
    have htr0 : sf.trace = s.trace := ‹_›
    have htr2 : sf_2.trace = sf_1.trace := ‹_›
    exact htr2.trans (htr1.trans (htr0.trans htr))
  refine SepWPp.weaken_pre ?_
    (hnext _ (sf_1.readReg64 (Reg.gpr 0#5))
      (by sc_close) (by sc_close) (by sc_close) (by sc_close)
      (by sc_close) (by sc_close) (by sc_close) (by sc_close)
      (by sc_close) (by sc_close) (by sc_close) (by sc_close)
      (by simp [wp_norm, arm64_norm, htr_sf2]) (by sc_close) hcl_done)
  have hbuf32 :
      vecU8Buf A.repAlloc 32#64 (sf_1.readReg64 (Reg.gpr 0#5)) (keyToBytes32 x.s.state.rootKey) =
        A.live (sf_1.readReg64 (Reg.gpr 0#5)) 32 1 ∗
          (sf_1.readReg64 (Reg.gpr 0#5) ↦ₛ keyToBytes32 x.s.state.rootKey) := by
    have h := vecU8Buf_pos_eq A.repAlloc (sf_1.readReg64 (Reg.gpr 0#5)) (keyToBytes32 x.s.state.rootKey)
      hroot_pos hroot_lt hoom64
    rwa [hroot_len] at h
  have hpure : (⌜(keyToBytes32 x.s.state.rootKey).length ≤ x.G.root.cap.toNat ∧
      x.G.root.cap.toNat < 2 ^ 63 ∧ x.G.root.ptr ≠ 0⌝ : SepProp) = emp :=
    segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
  rw [vecU8At_eq_of_pos A.repAlloc (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) hroot_pos,
      h38, h40, hbuf32, hpure]
  have hsp1_eq : sf_1.sp = s.sp := by sc_close
  have hsp_eq : sf.sp = s.sp := by sc_close
  simp only [sepConj_assoc, hsp1_eq, hsp_eq, emp_sepConj, sepConj_emp]
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## Field 4: `sender_chain` (`+232 → +572 / +336`) -/

/-- Budget-threaded `sender_chain` clone (`+232 → +572 / +336`) on `lsProg_80 H`. -/
theorem sc_senderChain_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hscc : SenderChainCloneLocal1PlacedOkX M A lim H)
    {x : SessionCloneGhost} {st : M.σ} {s0 s : State} {ret : BitVec 64}
    {Q Qp : State → SepProp → Prop}
    {localIk' remoteIk' : VecGhost}
    {v48 v60 v68 v70 v78 : BitVec 64} {v54 v84 : BitVec 32}
    {bq0 bq1 bq2 bq3 bq4 bq5 : BitVec 128} {F : SepProp}
    (hfits : FitsEvents M lim st (scSenderEvents x))
    (hqp_false : ∀ sf F', sf.status = .Panicked → Qp sf (⌜False⌝ ∗ F'))
    (hpc : s.pc = (blkPl_80).base + 232#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = x.s.state.sessionVersion.setWidth 64)
    (hx23 : s.readReg64 .x23 = localIk'.ptr)
    (hx24 : s.readReg64 .x24 = remoteIk'.cap)
    (hx25 : s.readReg64 .x25 = x.src)
    (hx26 : s.readReg64 .x26 = remoteIk'.ptr)
    (hx27 : s.readReg64 .x27 = 32#64)
    (hx29 : s.readReg64 .x29 = s.sp + 0x170#64)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrc_lt : x.s.state.receiverChains.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (sender' : Option SenderChainGhost) (scCap' : BitVec 64)
      (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128),
      s1.pc = (if x.s.state.receiverChains = []
        then (blkPl_80).base + 572#64
        else (blkPl_80).base + 336#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x21 = s.sp + 0xf8#64 →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = BitVec.ofNat 64 x.s.state.receiverChains.length →
      s1.readReg64 .x29 = s.sp + 0x170#64 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      OptSenderChainInline sender' x.s.state.senderChain (bytes104OfW6Q scCap' sq0 sq1 sq2 sq3 sq4 sq5) →
      encSenderFieldMem sender' x.s.state.senderChain = encSenderFieldMem x.G.sender x.s.state.senderChain →
      SepWPpLsCl lsmpl (lsProg_80 H) ret s1
        (A.pool lim (M.stepEvents (scSenderEvents x) st) s1 ∗
          optSenderChainAt A.repAlloc (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
          optSenderChainHeap A.repAlloc sender' x.s.state.senderChain ∗
          chunks96_6QAt (s.sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          memRegion (s.sp + 0xf8#64) 104 ∗
          ((s.sp + 0x48#64) ↦₆₄ scCap') ∗
          ((s.sp + 0x54#64) ↦₃₂ x.s.state.previousCounter) ∗
          ((s.sp + 0x60#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0x68#64) ↦₆₄ remoteIk'.ptr) ∗
          ((s.sp + 0x70#64) ↦₆₄ remoteIk'.cap) ∗
          ((s.sp + 0x78#64) ↦₆₄ localIk'.ptr) ∗
          ((s.sp + 0x84#64) ↦₃₂ x.s.state.sessionVersion) ∗
          ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
          ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
          stackAt s.sp chainCloneStackX ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s
      (A.pool lim st s ∗
        optSenderChainAt A.repAlloc (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
        chunks96_6QAt (s.sp + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
        memRegion (s.sp + 0xf8#64) 104 ∗
        ((s.sp + 0x48#64) ↦₆₄ v48) ∗
        ((s.sp + 0x54#64) ↦₃₂ v54) ∗
        ((s.sp + 0x60#64) ↦₆₄ v60) ∗
        ((s.sp + 0x68#64) ↦₆₄ v68) ∗
        ((s.sp + 0x70#64) ↦₆₄ v70) ∗
        ((s.sp + 0x78#64) ↦₆₄ v78) ∗
        ((s.sp + 0x84#64) ↦₃₂ v84) ∗
        ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
        ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
        stackAt s.sp chainCloneStackX ∗ F)
      Q Qp := by
  have hcall := sc_chainClone_placed_ok_at_x (senderChainCloneSpecX M A lim) hscc
  have hw22 : (s.readReg64 (Reg.gpr 22#5)).truncate 32 = x.s.state.sessionVersion := by
    change (s.readReg64 .x22).truncate 32 = x.s.state.sessionVersion
    rw [hx22]; exact segClone_setWidth_64_truncate_32 _
  cases hscG : x.G.sender with
  | none =>
    cases hscM : x.s.state.senderChain with
    | none =>
      have hev : scSenderEvents x = [] := by simp [scSenderEvents, hscG, hscM]
      rw [hev, M.stepEvents_nil] at hnext
      dsimp only [optSenderChainAt]
      have hnone_cmn : noneCap + 1#64 = 0#64 := by decide
      clear hcall
      have hpc_rc :
          (if ¬(BitVec.ofNat 64 x.s.state.receiverChains.length == 0#64) = true then (blkPl_80).base + 336#64 else (blkPl_80).base + 572#64) =
          (if x.s.state.receiverChains = [] then (blkPl_80).base + 572#64 else (blkPl_80).base + 336#64) := by
        rcases eq_nil_or_length_pos x.s.state.receiverChains with hrc | hrc
        · simp [hrc]
        · have hne : x.s.state.receiverChains ≠ [] := List.ne_nil_of_length_pos hrc
          have hbeq : (BitVec.ofNat 64 x.s.state.receiverChains.length == 0#64) = false :=
            beq_ofNat_zero_eq_false hrc (by omega)
          simp [hne, hbeq]
      intro hcl
      apply sepWPp_of_sepWP_lscl_sc hcl
        (mid := if x.s.state.receiverChains = [] then (blkPl_80).base + 572#64 else (blkPl_80).base + 336#64)
      wp_steps_sync_pool (if x.s.state.receiverChains = [] then (blkPl_80).base + 572#64 else (blkPl_80).base + 336#64)
      refine SepWP.done (by sc_close) (by sc_close) fun hcl1 => ?_
      have hinl : OptSenderChainInline none x.s.state.senderChain
          (bytes104OfW6Q noneCap bq0 bq1 bq2 bq3 bq4 bq5) := by
        rw [hscM]
        exact OptSenderChainInline.none_of_chunks96 bq0 bq1 bq2 bq3 bq4 bq5
      have henc : encSenderFieldMem none x.s.state.senderChain =
          encSenderFieldMem x.G.sender x.s.state.senderChain := by
        rw [hscG]
      refine SepWPp.weaken_pre ?_
        (hnext _ none noneCap bq0 bq1 bq2 bq3 bq4 bq5
          (by sc_close) (by sc_close) (by sc_close) (by sc_close)
          (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close)
          (by sc_close) (by sc_close) hinl henc hcl1)
      rw [hscG, hscM]
      dsimp only [optSenderChainAt, optSenderChainHeap]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp, hx23, hx24, hx26, hx27, hw22]
      exact Entails.of_eq (by sep_ac_rfl)
    | some sc =>
      dsimp only [optSenderChainAt]
      intro _
      exact sepWPp_pure_2nd_pf fun h => False.elim h
  | some sg =>
    cases hscM : x.s.state.senderChain with
    | none =>
      dsimp only [optSenderChainAt]
      intro _
      exact sepWPp_pure_2nd_pf fun h => False.elim h
    | some sc =>
      have hev : scSenderEvents x = senderChainCloneEvents sg sc := by
        simp [scSenderEvents, hscG, hscM]
      rw [hev] at hfits hnext
      have hfits_env : FitsEnv M lim st (SenderChainCloneEnv sg sc) :=
        fun evs hevs => hevs ▸ hfits
      rw [optSenderChainAt_some_eq_cap A.repAlloc (x.src + 0x90#64) sg sc]
      simp only [sepConj_assoc]
      refine sepWPpLsCl_pure_2nd_pf fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
      have hcap_ne : sg.srk.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcap_beq : (sg.srk.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      suffices h_at_call : ∀ sm : State,
          sm.pc = (blkPl_82).base →
          sm.status = .Running →
          sm.sp = s.sp →
          sm.spAligned = true →
          sm.readReg64 .x0 = s.sp + 0xf8#64 →
          sm.readReg64 .x1 = x.src + 0x90#64 →
          sm.readReg64 Reg.lr = (blkPl_80).base + 280#64 →
          sm.readReg64 .x19 = s.readReg64 .x19 →
          sm.readReg64 .x21 = s.sp + 0xf8#64 →
          sm.readReg64 .x25 = x.src →
          sm.readReg64 .x27 = 32#64 →
          sm.readReg64 .x29 = s.sp + 0x170#64 →
          sm.trace = s.trace →
          calleeSavedVRegs sm = calleeSavedVRegs s →
          SepWPpLsCl lsmpl (lsProg_80 H) ret sm
            ((memRegion (sm.sp + 0xf8#64) 104 ∗
                optSenderChainAt A.repAlloc (x.src + 0x90#64) (some sg) (some sc) ∗
                A.pool lim st sm ∗ stackAt sm.sp chainCloneStackX) ∗
              (chunks96_6QAt (s.sp + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
                ((s.sp + 0x48#64) ↦₆₄ v48) ∗
                ((s.sp + 0x54#64) ↦₃₂ x.s.state.previousCounter) ∗
                ((s.sp + 0x60#64) ↦₆₄ v60) ∗
                ((s.sp + 0x68#64) ↦₆₄ remoteIk'.ptr) ∗
                ((s.sp + 0x70#64) ↦₆₄ remoteIk'.cap) ∗
                ((s.sp + 0x78#64) ↦₆₄ localIk'.ptr) ∗
                ((s.sp + 0x84#64) ↦₃₂ x.s.state.sessionVersion) ∗
                ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
                ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗ F))
            Q Qp by
        intro hcl
        apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_82).base)
        wp_steps_sync_pool ((blkPl_82).base)
        refine SepWP.done rfl (by sc_close) fun hcl_call => ?_
        refine SepWPp.weaken_pre ?_
          (h_at_call _ (by sc_close) (by sc_close) (by sc_close) (by sc_close)
            (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close)
            (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close) hcl_call)
        have hpure : (⌜sg.srk.bytes.length ≤ sg.srk.cap.toNat ∧
            sg.srk.cap.toNat < 2 ^ 63 ∧ sg.srk.ptr ≠ 0⌝ : SepProp) = emp :=
          segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
        rw [optSenderChainAt_some_eq_cap A.repAlloc (x.src + 0x90#64) sg sc, hpure]
        simp only [State.sp_setMem, State.sp_setPC, State.sp_writeReg64_gpr,
          sepConj_assoc, emp_sepConj, sepConj_emp, hx23, hx24, hx26, hw22]
        exact Entails.of_eq (by sep_ac_rfl)
      intro sm hsm_pc hsm_run hsm_sp hsm_spA hsm_x0 hsm_x1 hsm_lr hsm_19 hsm_21 hsm_25 hsm_27 hsm_29 hsm_tr hsm_vregs
      refine SepWPpLsCl.call_noPanic_withLsCodeLoaded (spec := senderChainCloneSpecX M A lim)
        (x := (⟨sm.sp + 0xf8#64, x.src + 0x90#64, sg, sc⟩, st))
        hcall hsm_pc hsm_run hsm_spA hsm_lr
        (hspec := rfl)
        ⟨by rw [hsm_sp]; exact hsm_x0, hsm_x1, hfits_env⟩ rfl
        (fun sf hpcf_raw hrunf hspf hcsm => ?_)
        (hqp_false := fun sf hpan => hqp_false sf _ hpan)
      have hpcf : sf.pc = (blkPl_80).base + 280#64 := hpcf_raw
      clear hpcf_raw hcall
      obtain ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29, hcsv⟩ := hcsm
      dsimp only [senderChainCloneSpecX]
      rw [sepExists_sepConj_left]
      refine SepWPpLsCl.exists_elim fun evs => ?_
      simp only [sepConj_assoc]
      refine SepWPpLsCl.pure_elim fun ⟨htr_sf, hevs⟩ => ?_
      dsimp only [SenderChainCloneEnv] at hevs
      subst hevs
      rw [sepExists_sepConj_left]
      refine SepWPpLsCl.exists_elim fun g' => ?_
      simp only [sepConj_assoc]
      refine SepWPpLsCl.pure_elim fun ⟨hsrk', hpriv'⟩ => ?_
      have hsf_sp : sf.sp = s.sp := hspf.trans hsm_sp
      have hsf19 : sf.readReg64 (Reg.gpr 19#5) = s.readReg64 .x19 := hcs19.trans hsm_19
      have hsf21 : sf.readReg64 (Reg.gpr 21#5) = sf.sp + 0xf8#64 := by
        rw [hcs21, hsf_sp]; exact hsm_21
      have hsf25 : sf.readReg64 (Reg.gpr 25#5) = x.src := hcs25.trans hsm_25
      have hsf27 : sf.readReg64 (Reg.gpr 27#5) = 32#64 := hcs27.trans hsm_27
      have hsf29 : sf.readReg64 Reg.fp = sf.sp + 0x170#64 := by
        rw [hcs29, hsf_sp]; exact hsm_29
      have hsf29' : sf.readReg64 (Reg.gpr 29#5) = sf.sp + 0x170#64 := hsf29
      have hsf_tr : sf.trace = s0.trace := htr_sf.trans (hsm_tr.trans htr)
      have hsf_vregs : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        hcsv.trans (hsm_vregs.trans hvregs)
      have hsf_spA : sf.spAligned = true := by
        unfold State.spAligned at hsp ⊢; rw [hsf_sp]; exact hsp
      clear hspf hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29 hcsv htr_sf
      rw [hsm_sp]
      refine SepWPpLsCl.weaken_pre
        (sepConj_mono_left (optSenderChainAt_entails_chunks104W6Q A.repAlloc (s.sp + 0xf8#64) (some g') (some sc))) ?_
      simp only [sepExists_sepConj_left]
      refine SepWPpLsCl.exists_elim fun scCap' =>
        SepWPpLsCl.exists_elim fun sq0 => SepWPpLsCl.exists_elim fun sq1 =>
        SepWPpLsCl.exists_elim fun sq2 => SepWPpLsCl.exists_elim fun sq3 =>
        SepWPpLsCl.exists_elim fun sq4 => SepWPpLsCl.exists_elim fun sq5 => ?_
      simp only [sepConj_assoc]
      refine SepWPpLsCl.pure_elim fun hsc_inl => ?_
      have hinl : OptSenderChainInline (some g') x.s.state.senderChain
          (bytes104OfW6Q scCap' sq0 sq1 sq2 sq3 sq4 sq5) := by
        rw [hscM]; exact hsc_inl
      have henc : encSenderFieldMem (some g') x.s.state.senderChain =
          encSenderFieldMem x.G.sender x.s.state.senderChain := by
        simp only [hscG, hscM, encSenderFieldMem, encChainMem, senderGhostAsChain, hsrk', hpriv']
      rw [chunks104W6QAt_sp_0xf8 s.sp scCap' sq0 sq1 sq2 sq3 sq4 sq5,
          chunks96_6QAt_sp_0x90 s.sp bq0 bq1 bq2 bq3 bq4 bq5]
      simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      refine SepWPpLsCl.weaken_pre
        (P' := A.pool lim (M.stepEvents (senderChainCloneEvents sg sc) st) sf ∗
          (((s.sp + 248#64) ↦₆₄ scCap') ∗
            ((s.sp + 256#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp + 264#64) ↦₆₄ sq0.extractLsb' 64 64) ∗
            ((s.sp + 272#64) ↦₆₄ sq1.extractLsb' 0 64) ∗ ((s.sp + 280#64) ↦₆₄ sq1.extractLsb' 64 64) ∗
            ((s.sp + 288#64) ↦₆₄ sq2.extractLsb' 0 64) ∗ ((s.sp + 296#64) ↦₆₄ sq2.extractLsb' 64 64) ∗
            ((s.sp + 304#64) ↦₆₄ sq3.extractLsb' 0 64) ∗ ((s.sp + 312#64) ↦₆₄ sq3.extractLsb' 64 64) ∗
            ((s.sp + 320#64) ↦₆₄ sq4.extractLsb' 0 64) ∗ ((s.sp + 328#64) ↦₆₄ sq4.extractLsb' 64 64) ∗
            ((s.sp + 336#64) ↦₆₄ sq5.extractLsb' 0 64) ∗ ((s.sp + 344#64) ↦₆₄ sq5.extractLsb' 64 64) ∗
            optSenderChainHeap A.repAlloc (some g') (some sc) ∗
            optSenderChainAt A.repAlloc (x.src + 144#64) (some sg) (some sc) ∗
            stackAt s.sp chainCloneStackX ∗
            ((s.sp + 144#64) ↦₆₄ bq0.extractLsb' 0 64) ∗ ((s.sp + 152#64) ↦₆₄ bq0.extractLsb' 64 64) ∗
            ((s.sp + 160#64) ↦₆₄ bq1.extractLsb' 0 64) ∗ ((s.sp + 168#64) ↦₆₄ bq1.extractLsb' 64 64) ∗
            ((s.sp + 176#64) ↦₆₄ bq2.extractLsb' 0 64) ∗ ((s.sp + 184#64) ↦₆₄ bq2.extractLsb' 64 64) ∗
            ((s.sp + 192#64) ↦₆₄ bq3.extractLsb' 0 64) ∗ ((s.sp + 200#64) ↦₆₄ bq3.extractLsb' 64 64) ∗
            ((s.sp + 208#64) ↦₆₄ bq4.extractLsb' 0 64) ∗ ((s.sp + 216#64) ↦₆₄ bq4.extractLsb' 64 64) ∗
            ((s.sp + 224#64) ↦₆₄ bq5.extractLsb' 0 64) ∗ ((s.sp + 232#64) ↦₆₄ bq5.extractLsb' 64 64) ∗
            ((s.sp + 72#64) ↦₆₄ v48) ∗
            ((s.sp + 84#64) ↦₃₂ x.s.state.previousCounter) ∗
            ((s.sp + 96#64) ↦₆₄ v60) ∗
            ((s.sp + 104#64) ↦₆₄ remoteIk'.ptr) ∗
            ((s.sp + 112#64) ↦₆₄ remoteIk'.cap) ∗
            ((s.sp + 120#64) ↦₆₄ localIk'.ptr) ∗
            ((s.sp + 132#64) ↦₃₂ x.s.state.sessionVersion) ∗
            ((x.src + 88#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
            ((x.src + 332#64) ↦₃₂ x.s.state.previousCounter) ∗ F))
        (Entails.of_eq (by sep_ac_rfl)) ?_
      have hpc_rc :
          (if (BitVec.ofNat 64 x.s.state.receiverChains.length == 0#64) = true then (blkPl_80).base + 572#64 else (blkPl_80).base + 336#64) =
          (if x.s.state.receiverChains = [] then (blkPl_80).base + 572#64 else (blkPl_80).base + 336#64) := by
        rcases eq_nil_or_length_pos x.s.state.receiverChains with hrc | hrc
        · simp [hrc]
        · have hne : x.s.state.receiverChains ≠ [] := List.ne_nil_of_length_pos hrc
          have hbeq : (BitVec.ofNat 64 x.s.state.receiverChains.length == 0#64) = false :=
            beq_ofNat_zero_eq_false hrc (by omega)
          simp [hne, hbeq]
      intro hcl_sf
      apply sepWPp_of_sepWP_lscl_sc hcl_sf
        (mid := if x.s.state.receiverChains = [] then (blkPl_80).base + 572#64 else (blkPl_80).base + 336#64)
      wp_steps_sync_pool (if x.s.state.receiverChains = [] then (blkPl_80).base + 572#64 else (blkPl_80).base + 336#64)
      refine SepWP.done (by sc_close) (by sc_close) fun hcl_end => ?_
      refine SepWPp.weaken_pre ?_
        (hnext _ (some g') scCap' sq0 sq1 sq2 sq3 sq4 sq5
          (by sc_close) (by sc_close) (by sc_close) (by sc_close)
          (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close)
          (by sc_close) (by sc_close) hinl henc hcl_end)
      simp only [hscG, hscM, hsf21, hsf_sp, hsf27,
          ← chunks96_6QAt_sp_0x90 s.sp sq0 sq1 sq2 sq3 sq4 sq5,
          pointsTo128_eq_pointsTo64, cat128_extractLsb, BitVec.add_assoc, BitVec.reduceAdd,
          sepConj_assoc]
      have h104 : ∀ R_tail : SepProp,
          ((s.sp + 0xf8#64) ↦₆₄ scCap') ∗
            ((s.sp + 256#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp + 264#64) ↦₆₄ sq0.extractLsb' 64 64) ∗
            ((s.sp + 272#64) ↦₆₄ sq1.extractLsb' 0 64) ∗ ((s.sp + 280#64) ↦₆₄ sq1.extractLsb' 64 64) ∗
            ((s.sp + 288#64) ↦₆₄ sq2.extractLsb' 0 64) ∗ ((s.sp + 296#64) ↦₆₄ sq2.extractLsb' 64 64) ∗
            ((s.sp + 304#64) ↦₆₄ sq3.extractLsb' 0 64) ∗ ((s.sp + 312#64) ↦₆₄ sq3.extractLsb' 64 64) ∗
            ((s.sp + 320#64) ↦₆₄ sq4.extractLsb' 0 64) ∗ ((s.sp + 328#64) ↦₆₄ sq4.extractLsb' 64 64) ∗
            ((s.sp + 336#64) ↦₆₄ sq5.extractLsb' 0 64) ∗ ((s.sp + 344#64) ↦₆₄ sq5.extractLsb' 64 64) ∗
            R_tail ⊢
          memRegion (s.sp + 0xf8#64) 104 ∗ R_tail := by
        intro R_tail
        have h104_eq := congrArg (· ∗ R_tail) (chunks104W6QAt_sp_0xf8 s.sp scCap' sq0 sq1 sq2 sq3 sq4 sq5)
        simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h104_eq
        rw [← h104_eq]
        exact sepConj_mono_left (chunks104W6QAt_entails_memRegion _ _ _ _ _ _ _ _)
      refine Entails.trans
        (Q := ((s.sp + 0xf8#64) ↦₆₄ scCap') ∗
            ((s.sp + 256#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp + 264#64) ↦₆₄ sq0.extractLsb' 64 64) ∗
            ((s.sp + 272#64) ↦₆₄ sq1.extractLsb' 0 64) ∗ ((s.sp + 280#64) ↦₆₄ sq1.extractLsb' 64 64) ∗
            ((s.sp + 288#64) ↦₆₄ sq2.extractLsb' 0 64) ∗ ((s.sp + 296#64) ↦₆₄ sq2.extractLsb' 64 64) ∗
            ((s.sp + 304#64) ↦₆₄ sq3.extractLsb' 0 64) ∗ ((s.sp + 312#64) ↦₆₄ sq3.extractLsb' 64 64) ∗
            ((s.sp + 320#64) ↦₆₄ sq4.extractLsb' 0 64) ∗ ((s.sp + 328#64) ↦₆₄ sq4.extractLsb' 64 64) ∗
            ((s.sp + 336#64) ↦₆₄ sq5.extractLsb' 0 64) ∗ ((s.sp + 344#64) ↦₆₄ sq5.extractLsb' 64 64) ∗
            (A.pool lim (M.stepEvents (senderChainCloneEvents sg sc) st) _ ∗
              optSenderChainAt A.repAlloc (x.src + 0x90#64) (some sg) (some sc) ∗
              optSenderChainHeap A.repAlloc (some g') (some sc) ∗
              chunks96_6QAt (s.sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
              ((s.sp + 0x48#64) ↦₆₄ scCap') ∗ ((s.sp + 0x54#64) ↦₃₂ x.s.state.previousCounter) ∗
              ((s.sp + 0x60#64) ↦₆₄ 32#64) ∗ ((s.sp + 0x68#64) ↦₆₄ remoteIk'.ptr) ∗
              ((s.sp + 0x70#64) ↦₆₄ remoteIk'.cap) ∗ ((s.sp + 0x78#64) ↦₆₄ localIk'.ptr) ∗
              ((s.sp + 0x84#64) ↦₃₂ x.s.state.sessionVersion) ∗
              ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
              ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
              stackAt s.sp chainCloneStackX ∗ F))
        (Entails.of_eq (by
          simp only [chunks96_6QAt_sp_0x90, pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
          sep_ac_rfl)) ?_
      refine Entails.trans (h104 _) ?_
      exact Entails.of_eq (by sep_ac_rfl)

private theorem stackAt_chainClone_eq_alloc_x_c7_placed (sp : BitVec 64) :
    stackAt sp chainCloneStackX =
      memRegion (sp - BitVec.ofNat 64 chainCloneStackX) 208 ∗ stackAt sp extHookStack := by
  have h := stackAt_split_bottom sp extHookStack 208 (by decide)
  rwa [show extHookStack + 208 = chainCloneStackX by decide] at h

/-! ## Combined fields 1–4 (`+32 → +572 / +336`) -/

/-- Budget-threaded combined fields 1–4 (`+32 → +572 / +336`) on `lsProg_80 H`. -/
theorem sc_fields_1_to_4_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsPlaced M A lim H)
    (hmemcpy : subroutine_ok (lsProg_80 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (withVmPreserved (sessionMemcpySpec extHookStack))))
    (hscc : SenderChainCloneLocal1PlacedOkX M A lim H)
    {x : SessionCloneGhost} {st : M.σ} {s0 s : State}
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    {bq0 bq1 bq2 bq3 bq4 bq5 : BitVec 128}
    {v48 v58 v60 v68 v70 v78 v88 : BitVec 64} {v54 v84 : BitVec 32} {F : SepProp}
    (hfits : FitsEvents M lim st (scFields1To4Events x))
    (hqp_false : ∀ sf F', sf.status = .Panicked → Qp sf (⌜False⌝ ∗ F'))
    (hpc : s.pc = (blkPl_80).base + 32#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = x.dst) (hx1 : s.readReg64 .x1 = x.src)
    (hx29 : s.readReg64 .x29 = s.sp + 0x170#64)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrc_lt : x.s.state.receiverChains.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
      (sender' : Option SenderChainGhost) (scCap' : BitVec 64)
      (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128),
      s1.pc = (if x.s.state.receiverChains = []
        then (blkPl_80).base + 572#64 else (blkPl_80).base + 336#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = x.dst → s1.readReg64 .x21 = s.sp + 0xf8#64 →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = BitVec.ofNat 64 x.s.state.receiverChains.length →
      s1.readReg64 .x29 = s.sp + 0x170#64 →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      localIk'.bytes = x.G.localIk.bytes →
      localIk'.cap = BitVec.ofNat 64 x.G.localIk.bytes.length →
      remoteIk'.bytes = x.G.remoteIk.bytes →
      remoteIk'.cap = BitVec.ofNat 64 x.G.remoteIk.bytes.length →
      OptSenderChainInline sender' x.s.state.senderChain
        (bytes104OfW6Q scCap' sq0 sq1 sq2 sq3 sq4 sq5) →
      encSenderFieldMem sender' x.s.state.senderChain = encSenderFieldMem x.G.sender x.s.state.senderChain →
      SepWPpLsCl lsmpl (lsProg_80 H) ret s1
        (A.pool lim (M.stepEvents (scFields1To4Events x) st) s1 ∗
          vecGhostAt A.repAlloc x.G.localIk x.src ∗
          vecGhostAt A.repAlloc x.G.remoteIk (x.src + 0x18#64) ∗
          vecU8At A.repAlloc (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
          optSenderChainAt A.repAlloc (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
          vecU8Buf A.repAlloc localIk'.cap localIk'.ptr localIk'.bytes ∗
          vecU8Buf A.repAlloc remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
          vecU8Buf A.repAlloc 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
          optSenderChainHeap A.repAlloc sender' x.s.state.senderChain ∗
          chunks96_6QAt (s.sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          memRegion (s.sp + 0xf8#64) 104 ∗
          ((s.sp + 0x48#64) ↦₆₄ scCap') ∗ ((s.sp + 0x54#64) ↦₃₂ x.s.state.previousCounter) ∗
          ((s.sp + 0x58#64) ↦₆₄ rootPtr') ∗ ((s.sp + 0x60#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0x68#64) ↦₆₄ remoteIk'.ptr) ∗ ((s.sp + 0x70#64) ↦₆₄ remoteIk'.cap) ∗
          ((s.sp + 0x78#64) ↦₆₄ localIk'.ptr) ∗ ((s.sp + 0x84#64) ↦₃₂ x.s.state.sessionVersion) ∗
          ((s.sp + 0x88#64) ↦₆₄ localIk'.cap) ∗
          ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
          ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
          ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
          stackAt s.sp chainCloneStackX ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s
      (A.pool lim st s ∗
        vecGhostAt A.repAlloc x.G.localIk x.src ∗
        vecGhostAt A.repAlloc x.G.remoteIk (x.src + 0x18#64) ∗
        vecU8At A.repAlloc (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
        optSenderChainAt A.repAlloc (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
        chunks96_6QAt (s.sp + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
        memRegion (s.sp + 0xf8#64) 104 ∗
        ((s.sp + 0x48#64) ↦₆₄ v48) ∗ ((s.sp + 0x54#64) ↦₃₂ v54) ∗
        ((s.sp + 0x58#64) ↦₆₄ v58) ∗ ((s.sp + 0x60#64) ↦₆₄ v60) ∗
        ((s.sp + 0x68#64) ↦₆₄ v68) ∗ ((s.sp + 0x70#64) ↦₆₄ v70) ∗
        ((s.sp + 0x78#64) ↦₆₄ v78) ∗ ((s.sp + 0x84#64) ↦₃₂ v84) ∗
        ((s.sp + 0x88#64) ↦₆₄ v88) ∗
        ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
        ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
        ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
        stackAt s.sp chainCloneStackX ∗ F)
      Q Qp := by
  have h1234 : scFields1To4Events x =
      vecCloneEvents x.G.localIk ++
        (vecCloneEvents x.G.remoteIk ++ (rustAllocEvents 32 1 ++ scSenderEvents x)) := by
    simp [scFields1To4Events, List.append_assoc]
  have hfits0 := h1234 ▸ hfits
  obtain ⟨hfits_loc, hfits_r1⟩ := fitsEvents_split hfits0
  obtain ⟨hfits_rem, hfits_r2⟩ := fitsEvents_split hfits_r1
  obtain ⟨hfits_root, hfits_sc⟩ := fitsEvents_split hfits_r2
  rw [sc_vecGhostAt_0x18_eq A.repAlloc x.G.remoteIk x.src,
      vecU8Buf_pure_extract A.repAlloc x.G.remoteIk.cap x.G.remoteIk.ptr x.G.remoteIk.bytes,
      sc_vecU8At_0x30_root_eq A.repAlloc x.src x.G.root.cap x.G.root.ptr x.s.state.rootKey,
      stackAt_chainClone_eq_alloc_x_c7_placed s.sp]
  refine SepWPpLsCl.weaken_pre
    (P' := ⌜x.G.remoteIk.bytes.length ≤ x.G.remoteIk.cap.toNat ∧
              x.G.remoteIk.cap.toNat < 2 ^ 63 ∧ x.G.remoteIk.ptr ≠ 0⌝ ∗
            A.pool lim st s ∗ vecGhostAt A.repAlloc x.G.localIk x.src ∗
            ((x.src + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
            ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
            stackAt s.sp extHookStack ∗
            (((x.src + 0x18#64) ↦₆₄ x.G.remoteIk.cap) ∗
              ((x.src + 0x20#64) ↦₆₄ x.G.remoteIk.ptr) ∗
              vecU8Buf A.repAlloc x.G.remoteIk.cap x.G.remoteIk.ptr x.G.remoteIk.bytes ∗
              ((x.src + 0x30#64) ↦₆₄ x.G.root.cap) ∗ ((x.src + 0x38#64) ↦₆₄ x.G.root.ptr) ∗
              ((x.src + 0x40#64) ↦₆₄ 32#64) ∗
              vecU8Buf A.repAlloc x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
              optSenderChainAt A.repAlloc (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
              chunks96_6QAt (s.sp + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗ memRegion (s.sp + 0xf8#64) 104 ∗
              ((s.sp + 0x48#64) ↦₆₄ v48) ∗ ((s.sp + 0x54#64) ↦₃₂ v54) ∗
              ((s.sp + 0x58#64) ↦₆₄ v58) ∗ ((s.sp + 0x60#64) ↦₆₄ v60) ∗
              ((s.sp + 0x68#64) ↦₆₄ v68) ∗ ((s.sp + 0x70#64) ↦₆₄ v70) ∗
              ((s.sp + 0x78#64) ↦₆₄ v78) ∗ ((s.sp + 0x84#64) ↦₃₂ v84) ∗ ((s.sp + 0x88#64) ↦₆₄ v88) ∗
              ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
              ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
              memRegion (s.sp - BitVec.ofNat 64 chainCloneStackX) 208 ∗ F))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWPpLsCl.pure_elim fun ⟨hlen_rem, hcap_rem, _⟩ => ?_
  have hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63 := by omega
  refine sc_localIk_placed_x hA hmemcpy hfits_loc hpc hrun hsp hx0 hx1 htr hvregs hrem_lt
    fun s1 localIk' hpc1 hrun1 hsp1 hspA1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 htr1 hvregs1 hloc_b hloc_c => ?_
  rw [← hsp1]
  refine SepWPpLsCl.weaken_pre
    (P' := A.pool lim (M.stepEvents (vecCloneEvents x.G.localIk) st) s1 ∗
            vecGhostAt A.repAlloc x.G.remoteIk (x.src + 0x18#64) ∗
            ((x.src + 0x40#64) ↦₆₄ 32#64) ∗ ((s1.sp + 0x88#64) ↦₆₄ v88) ∗ stackAt s1.sp extHookStack ∗
            (vecGhostAt A.repAlloc x.G.localIk x.src ∗
              vecU8Buf A.repAlloc localIk'.cap localIk'.ptr localIk'.bytes ∗
              ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
              ((x.src + 0x30#64) ↦₆₄ x.G.root.cap) ∗ ((x.src + 0x38#64) ↦₆₄ x.G.root.ptr) ∗
              vecU8Buf A.repAlloc x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
              optSenderChainAt A.repAlloc (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
              chunks96_6QAt (s1.sp + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗ memRegion (s1.sp + 0xf8#64) 104 ∗
              ((s1.sp + 0x48#64) ↦₆₄ v48) ∗ ((s1.sp + 0x54#64) ↦₃₂ v54) ∗
              ((s1.sp + 0x58#64) ↦₆₄ v58) ∗ ((s1.sp + 0x60#64) ↦₆₄ v60) ∗
              ((s1.sp + 0x68#64) ↦₆₄ v68) ∗ ((s1.sp + 0x70#64) ↦₆₄ v70) ∗
              ((s1.sp + 0x78#64) ↦₆₄ v78) ∗ ((s1.sp + 0x84#64) ↦₃₂ v84) ∗
              ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
              ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
              memRegion (s1.sp - BitVec.ofNat 64 chainCloneStackX) 208 ∗ F))
    (by rw [sc_vecGhostAt_0x18_eq A.repAlloc x.G.remoteIk x.src]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine sc_remoteIk_placed_x hA hmemcpy hfits_rem hpc1 hrun1 hspA1 hx24_1 hx25_1 htr1 hvregs1
    fun s2 remoteIk' hpc2 hrun2 hsp2 hspA2 hx19_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx29_2 htr2 hvregs2 hrem_b hrem_c => ?_
  rw [← hsp2, hx21_1]
  refine SepWPpLsCl.weaken_pre
    (P' := A.pool lim (M.stepEvents (vecCloneEvents x.G.remoteIk) (M.stepEvents (vecCloneEvents x.G.localIk) st)) s2 ∗
            vecU8At A.repAlloc (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
            ((s2.sp + 0x58#64) ↦₆₄ v58) ∗ stackAt s2.sp extHookStack ∗
            (vecGhostAt A.repAlloc x.G.localIk x.src ∗ vecGhostAt A.repAlloc x.G.remoteIk (x.src + 0x18#64) ∗
              vecU8Buf A.repAlloc localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A.repAlloc remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              optSenderChainAt A.repAlloc (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
              chunks96_6QAt (s2.sp + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗ memRegion (s2.sp + 0xf8#64) 104 ∗
              ((s2.sp + 0x48#64) ↦₆₄ v48) ∗ ((s2.sp + 0x54#64) ↦₃₂ v54) ∗
              ((s2.sp + 0x60#64) ↦₆₄ v60) ∗ ((s2.sp + 0x68#64) ↦₆₄ v68) ∗
              ((s2.sp + 0x70#64) ↦₆₄ v70) ∗ ((s2.sp + 0x78#64) ↦₆₄ v78) ∗
              ((s2.sp + 0x84#64) ↦₃₂ v84) ∗ ((s2.sp + 0x88#64) ↦₆₄ localIk'.cap) ∗
              ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
              ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
              ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
              memRegion (s2.sp - BitVec.ofNat 64 chainCloneStackX) 208 ∗ F))
    (by rw [sc_vecU8At_0x30_root_eq A.repAlloc x.src x.G.root.cap x.G.root.ptr x.s.state.rootKey]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine sc_rootKey_placed_x hA hmemcpy hfits_root hpc2 hrun2 hspA2 hx25_2 hx27_2 htr2 hvregs2
    fun s3 rootPtr' hpc3 hrun3 hsp3 hspA3 hx19_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx29_3 htr3 hvregs3 => ?_
  rw [← hsp3]
  refine SepWPpLsCl.weaken_pre
    (P' := A.pool lim (M.stepEvents (rustAllocEvents 32 1)
              (M.stepEvents (vecCloneEvents x.G.remoteIk) (M.stepEvents (vecCloneEvents x.G.localIk) st))) s3 ∗
            optSenderChainAt A.repAlloc (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
            chunks96_6QAt (s3.sp + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗ memRegion (s3.sp + 0xf8#64) 104 ∗
            ((s3.sp + 0x48#64) ↦₆₄ v48) ∗ ((s3.sp + 0x54#64) ↦₃₂ v54) ∗
            ((s3.sp + 0x60#64) ↦₆₄ v60) ∗ ((s3.sp + 0x68#64) ↦₆₄ v68) ∗
            ((s3.sp + 0x70#64) ↦₆₄ v70) ∗ ((s3.sp + 0x78#64) ↦₆₄ v78) ∗ ((s3.sp + 0x84#64) ↦₃₂ v84) ∗
            ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
            ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗ stackAt s3.sp chainCloneStackX ∗
            (vecGhostAt A.repAlloc x.G.localIk x.src ∗ vecGhostAt A.repAlloc x.G.remoteIk (x.src + 0x18#64) ∗
              vecU8At A.repAlloc (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
              vecU8Buf A.repAlloc localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A.repAlloc remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A.repAlloc 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
              ((s3.sp + 0x58#64) ↦₆₄ rootPtr') ∗ ((s3.sp + 0x88#64) ↦₆₄ localIk'.cap) ∗
              ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗ F))
    (by rw [stackAt_chainClone_eq_alloc_x_c7_placed s3.sp]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  have hx19_3' : s3.readReg64 .x19 = x.dst := by rw [hx19_3, hx19_2, hx19_1]
  have hx22_3' : s3.readReg64 .x22 = x.s.state.sessionVersion.setWidth 64 := by rw [hx22_3, hx22_2, hx22_1]
  have hx23_3' : s3.readReg64 .x23 = localIk'.ptr := by rw [hx23_3, hx23_2, hx23_1]
  have hx24_3' : s3.readReg64 .x24 = remoteIk'.cap := by rw [hx24_3, hx24_2]
  have hx26_3' : s3.readReg64 .x26 = remoteIk'.ptr := by rw [hx26_3, hx26_2]
  have hx29_3' : s3.readReg64 .x29 = s3.sp + 0x170#64 := by rw [hx29_3, hx29_2, hx29_1, hx29, hsp3, hsp2, hsp1]
  refine sc_senderChain_placed_x hscc hfits_sc hqp_false hpc3 hrun3 hspA3 hx22_3' hx23_3' hx24_3' hx25_3 hx26_3' hx27_3 hx29_3' htr3 hvregs3 hrc_lt
    fun s4 sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5 hpc4 hrun4 hsp4 hspA4 hx19_4 hx21_4 hx25_4 hx26_4 hx29_4 htr4 hvregs4 hinl henc => ?_
  have hsp_eq : s3.sp = s.sp := by rw [hsp3, hsp2, hsp1]
  have hstep_eq :
      M.stepEvents (scSenderEvents x)
        (M.stepEvents (rustAllocEvents 32 1)
          (M.stepEvents (vecCloneEvents x.G.remoteIk)
            (M.stepEvents (vecCloneEvents x.G.localIk) st))) =
      M.stepEvents (scFields1To4Events x) st := by
    simp only [scFields1To4Events, M.stepEvents_append]
  rw [hsp_eq] at hx21_4 hx29_4 ⊢
  rw [hstep_eq]
  refine SepWPpLsCl.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hnext s4 localIk' remoteIk' rootPtr' sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5
      hpc4 hrun4 (by rw [hsp4, hsp_eq]) hspA4
      (by rw [hx19_4, hx19_3']) hx21_4 hx25_4 hx26_4 hx29_4
      htr4 hvregs4 hloc_b hloc_c hrem_b hrem_c hinl henc)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.PrologueFields1To4XPlacedBudget
