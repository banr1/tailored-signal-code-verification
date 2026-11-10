/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1StepsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1Placed
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Inlined `States::send` Immediate Arms and Leaf-Call Combinators

Provides `VmPreserved`-forwarding `memcpy` relocation helpers, verifies the three immediate
arms with `RustCliAllocBudget` pool transport, and provides budget-threaded leaf-call
combinators on `spqrSendPlacedProg`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open scoped CryptoVerification.SpqrV1.Top.Send.Placed
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement libsignalSessionCode lsmpl)
open CryptoVerification.LibsignalSpqrV1
  (Chunk Message MessagePayload States spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (Ct1Acknowledged NoHeaderReceived)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk (EkSentCt1Received)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded sessionMemcpyRegionSpec withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop (chunkedStatesAt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (chunkAt chunkSize)
open CryptoVerification.SpqrV1.States.Leaves
  (Relocatable relocate_post_entails relocate_pre_entails relocatedHeap)
open CryptoVerification.SpqrV1.Top.Send
  (SpqrSendJoinStatePlaced chunkedStatesAt_eq_word0_tail920 chunkedStatesTail920At
   chunkedStatesWord0 expose_epoch_ct1Acknowledged expose_epoch_ekSentCt1Received
   expose_epoch_noHeaderReceived finish_sepWP finish_sepWP_lscro imm_arm_post_entails
   of_sepWP_lscro scratch_and_chunk_entails_memRegion spqrSendCalleeStack spqrSendKeySlotAt
   spqrSendPayloadSlotAt spqrSendPlacedEntry spqrSendPlacedProg stackAt_spqrSendCallee_split
   word0_sz_pad_entails_memRegion_928)
open CryptoVerification.SpqrV1.Top.Send.Placed (blkPl_124)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget (sepWP_seq_lscro)
open LibsignalBinary.Proofs.SpqrV1.Top.Send.DefsPlacedBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1StepsPlacedBudget
  (spqrSend_session_memcpy_region_ok_placed)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)

export CryptoVerification.SpqrV1.Top.Send
  (SpqrSendJoinStatePlaced of_sepWP_lscro finish_sepWP_lscro)
export LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget (sepWP_seq_lscro)

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

/-! ## `VmPreserved`-Forwarding `memcpy` Relocation and Continuation Helpers -/

/-- Framed `memcpy` call rule under `sessionMemcpyRegionBudgetSpec` that relocates any
    `Relocatable n F` predicate from `src` to `dst` while forwarding `VmPreserved s sf`. -/
theorem call_memcpy_relocate {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionBudgetSpec)
    {n : Nat} {F : BitVec 64 → SepProp} (hrel : Relocatable n F) (dst src : BitVec 64)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = dst) (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n) (hsplit : P = (memRegion dst n ∗ F src) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call → sf.trace = s0.trace →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s → VmPreserved s sf →
      SepWP prog target_pc sf ((F dst ∗ memRegion src n) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.fold (relocate_pre_entails hrel dst src Frame) (sepConj_emp _).symm ?_
  rw [sepConj_emp]; wp_pull_exists; rename_i bs
  refine SepWP.pure_elim fun hlen => ?_
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs)) (F := relocatedHeap F bs ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec]
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun hvm_sf => ?_
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    refine SepWP.fold (relocate_post_entails dst src hlen Frame) (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) (htr.trans htrace)
      hcs_sf.1 hcs_sf.2.1 hcs_sf.2.2.1 hcs_sf.2.2.2.1 hcs_sf.2.2.2.2.1
      hcs_sf.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.1
      hcs_sf.2.2.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.2.2.2.2
      hvm_sf

/-- Pool-transporting `memcpy` relocation call rule under `sessionMemcpyRegionBudgetSpec`:
    relocates `Relocatable n F` from `src` to `dst` and rewrites `A.pool lim bSt s` to
    `A.pool lim bSt sf` via `A.pool_transport`. -/
theorem call_memcpy_relocate_pool {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {bSt : M.σ} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionBudgetSpec)
    {n : Nat} {F : BitVec 64 → SepProp} (hrel : Relocatable n F) (dst src : BitVec 64)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = dst) (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ F src ∗ A.pool lim bSt s) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call → sf.trace = s0.trace →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s → VmPreserved s sf →
      SepWP prog target_pc sf ((F dst ∗ memRegion src n ∗ A.pool lim bSt sf) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  have hsplit' : P = (memRegion dst n ∗ F src) ∗ (A.pool lim bSt s ∗ Frame) := by
    rw [hsplit]; sep_ac_rfl
  refine call_memcpy_relocate hcall hrel dst src hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2
    hsplit' (fun sf hpc_sf hrun_sf hsp_sf htr_sf hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs hvm_sf => ?_)
  have hpool : (F dst ∗ memRegion src n) ∗ (A.pool lim bSt s ∗ Frame) =
      (F dst ∗ memRegion src n ∗ A.pool lim bSt sf) ∗ Frame := by
    rw [A.pool_transport lim bSt s sf hvm_sf]; sep_ac_rfl
  rw [hpool]
  exact hnext sf hpc_sf hrun_sf hsp_sf htr_sf hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs hvm_sf

variable [LibsignalPlacement]

/-- Expose `VmPreserved s sm` to an `of_sepWP_lscro` continuation so `by_vm_steps` can transport
    `A.pool lim bSt s` across basic blocks containing `STR`/`STP`. -/
theorem sepWP_vm_lscro {P : Program} {b target_pc ret : BitVec 64}
    {Hk : String → Option (State → State)} {s : State} {Pre : SepProp}
    {Q onPanic : State → SepProp → Prop}
    (hwp : SepWP (P.rebase b Hk) target_pc s Pre
      (fun sm Pm => VmPreserved s sm ∧
        (VmPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
          SepWPp (P.rebase b Hk) ret sm Pm Q onPanic))) :
    SepWP (P.rebase b Hk) target_pc s Pre
      (fun sm Pm => LibsignalCodeRoLoaded lsmpl sm.mem →
        SepWPp (P.rebase b Hk) ret sm Pm Q onPanic) :=
  SepWP.mono hwp fun _ _ _ _ ⟨hvm, hcont⟩ hcrl => hcont hvm hcrl

/-- Close a `by_vm_steps` basic block prepared by `sepWP_vm_lscro`, supplying `VmPreserved s0 s`
    to both the spatial entailment and the `SepWPp` continuation. -/
theorem finish_sepWP_lscro_vm {prog prog_ret : Program} {mid ret : BitVec 64} {s0 s : State}
    {P : SepProp} {P' : State → SepProp} {Q onPanic : State → SepProp → Prop}
    (hpc : s.pc = mid) (hrun : s.status = .Running) (htp : s.tpidrEl0 = s0.tpidrEl0)
    (hnext : VmPreserved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
      SepWPp prog_ret ret s (P' s) Q onPanic)
    (hent : VmPreserved s0 s → (P ⊢ P' s)) :
    SepWP prog mid s P
      (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧
        (VmPreserved s0 sm → LibsignalCodeRoLoaded lsmpl sm.mem →
          SepWPp prog_ret ret sm Pm Q onPanic)) :=
  SepWP.done hpc hrun ⟨htp, fun hvm hcrl R hm hL =>
    hnext hvm hcrl R (Satisfies.mono (sepConj_mono_left (hent hvm)) hm) hL⟩

/-- Total-correctness `SepWP` counterpart of `sepWP_vm_lscro` (for use under `sepWP_seq_lscro`). -/
theorem sepWP_vm_lscro_total {P : Program} {b target_pc ret : BitVec 64}
    {Hk : String → Option (State → State)} {s : State} {Pre : SepProp}
    {Q : State → SepProp → Prop}
    (hwp : SepWP (P.rebase b Hk) target_pc s Pre
      (fun sm Pm => VmPreserved s sm ∧
        (VmPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
          SepWP (P.rebase b Hk) ret sm Pm Q))) :
    SepWP (P.rebase b Hk) target_pc s Pre
      (fun sm Pm => LibsignalCodeRoLoaded lsmpl sm.mem →
        SepWP (P.rebase b Hk) ret sm Pm Q) :=
  SepWP.mono hwp fun _ _ _ _ ⟨hvm, hcont⟩ hcrl => hcont hvm hcrl

/-- Total-correctness `SepWP` counterpart of `finish_sepWP_lscro_vm`. -/
theorem finish_sepWP_lscro_vm_total {prog prog_ret : Program} {mid ret : BitVec 64} {s0 s : State}
    {P : SepProp} {P' : State → SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = mid) (hrun : s.status = .Running) (htp : s.tpidrEl0 = s0.tpidrEl0)
    (hnext : VmPreserved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
      SepWP prog_ret ret s (P' s) Q)
    (hent : VmPreserved s0 s → (P ⊢ P' s)) :
    SepWP prog mid s P
      (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧
        (VmPreserved s0 sm → LibsignalCodeRoLoaded lsmpl sm.mem →
          SepWP prog_ret ret sm Pm Q)) :=
  SepWP.done hpc hrun ⟨htp, fun hvm hcrl => SepWP.weaken_pre (hent hvm) (hnext hvm hcrl)⟩

/-! ## Relocatable Immediate Arms -/

/-- Relocatable immediate arm 1: `.ekSentCt1Received st` (`+924 -> +3064 -> +3068`), forwarding
    `VmPreserved s sf`. -/
theorem step_send_arm_ekSentCt1Received_placed {F : ShaCompress} {M : AllocCostModel}
    (A : RustCliAllocBudget M) {lim : BudgetLimits} (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext) {s0 s : State} (sp : BitVec 64)
    (st : EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 924#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = 6#64) (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx25 : s.readReg64 .x25 = sp + 0x550#64) (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (chunkedStatesAt A.repAlloc (sp + 0x950#64) (.ekSentCt1Received st) ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920) ∗ Frame)
    (hnext : ∀ sf : State, SpqrSendJoinStatePlaced sp ext s0 sf
        { epoch := st.uc.epoch, payload := .ct1Ack true } (.ekSentCt1Received st) →
      VmPreserved s sf →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) sf
        ((memRegion (sp + 0x950#64) 928 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct1Ack true) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ekSentCt1Received st)) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) s P post := by
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  subst hP
  rw [chunkedStatesAt_eq_word0_tail920 A.repAlloc (sp + 0x950#64) (.ekSentCt1Received st),
      show (sp + 0x950#64) + 8#64 = sp + 0x958#64 by rw [BitVec.add_assoc]; rfl]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_ekSentCt1Received A.repAlloc sp st
  rw [h_ep]; wp_steps; rw [← h_ep]
  refine call_memcpy_relocate hmemcpy
    (CryptoVerification.SpqrV1.Top.Send.Relocatable.of_chunkedStatesTail920At A.repAlloc (.ekSentCt1Received st))
    (sp + 0x590#64) (sp + 0x958#64) (s0 := s0) (sp_call := sp)
    (Frame := ((sp + 0x950#64) ↦₆₄ 6#64) ∗ memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_124).base + 944#64) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by dsimp only [chunkedStatesWord0]; sep_ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf hvm_sf
  have hvm_s_sf : VmPreserved s sf := (by simp only [arm64_norm] : VmPreserved s _).trans hvm_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf
  wp_steps
  refine finish_sepWP
    (hnext _ ⟨by simp only [spqrSendPlacedEntry, arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, chunkedStatesWord0, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *]⟩
      (hvm_s_sf.trans (by simp only [arm64_norm])))
    (imm_arm_post_entails A.repAlloc sp 6#64 _ _ _ (.ct1Ack true) (.ekSentCt1Received st) Frame
      (by simp only [arm64_norm]; rfl) (by dsimp only [spqrSendPayloadSlotAt]; simp only [arm64_norm]))

theorem step_send_arm_ekSentCt1Received_pool_placed {F : ShaCompress} {M : AllocCostModel}
    (A : RustCliAllocBudget M) {lim : BudgetLimits} (bSt : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext) {s0 s : State} (sp : BitVec 64)
    (st : EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 924#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = 6#64) (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx25 : s.readReg64 .x25 = sp + 0x550#64) (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (A.pool lim bSt s ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.ekSentCt1Received st) ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920) ∗ Frame)
    (hnext : ∀ sf : State, SpqrSendJoinStatePlaced sp ext s0 sf
        { epoch := st.uc.epoch, payload := .ct1Ack true } (.ekSentCt1Received st) →
      VmPreserved s sf →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) sf
        ((A.pool lim bSt sf ∗ memRegion (sp + 0x950#64) 928 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct1Ack true) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ekSentCt1Received st)) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) s P post := by
  have hP' : P = (chunkedStatesAt A.repAlloc (sp + 0x950#64) (.ekSentCt1Received st) ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920) ∗
      (A.pool lim bSt s ∗ Frame) := by
    rw [hP]; sep_ac_rfl
  refine step_send_arm_ekSentCt1Received_placed A ext hA sp st hpc hrun hsp hsp_align
    htr hx19 hx20 hx24 hx25 hx26 hx28 hvregs hP' (fun sf hjoin hvm => ?_)
  have hpool :
      (memRegion (sp + 0x950#64) 928 ∗
        spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct1Ack true) ∗
        spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
        chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ekSentCt1Received st)) ∗
        (A.pool lim bSt s ∗ Frame) =
      (A.pool lim bSt sf ∗ memRegion (sp + 0x950#64) 928 ∗
        spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct1Ack true) ∗
        spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
        chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ekSentCt1Received st)) ∗ Frame := by
    rw [A.pool_transport lim bSt s sf hvm]; sep_ac_rfl
  rw [hpool]
  exact hnext sf hjoin hvm

/-- Relocatable immediate arm 2: `.noHeaderReceived st` (`+1284 -> +3064 -> +3068`), forwarding
    `VmPreserved s sf`. -/
theorem step_send_arm_noHeaderReceived_placed {F : ShaCompress} {M : AllocCostModel}
    (A : RustCliAllocBudget M) {lim : BudgetLimits} (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext) {s0 s : State} (sp : BitVec 64)
    (st : NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 1284#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = 7#64) (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx25 : s.readReg64 .x25 = sp + 0x550#64) (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (chunkedStatesAt A.repAlloc (sp + 0x950#64) (.noHeaderReceived st) ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920) ∗ Frame)
    (hnext : ∀ sf : State, SpqrSendJoinStatePlaced sp ext s0 sf
        { epoch := st.uc.epoch, payload := .none } (.noHeaderReceived st) →
      VmPreserved s sf →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) sf
        ((memRegion (sp + 0x950#64) 928 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) .none ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.noHeaderReceived st)) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) s P post := by
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  subst hP
  rw [chunkedStatesAt_eq_word0_tail920 A.repAlloc (sp + 0x950#64) (.noHeaderReceived st),
      show (sp + 0x950#64) + 8#64 = sp + 0x958#64 by rw [BitVec.add_assoc]; rfl]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_noHeaderReceived A.repAlloc sp st
  rw [h_ep]; wp_steps; rw [← h_ep]
  refine call_memcpy_relocate hmemcpy
    (CryptoVerification.SpqrV1.Top.Send.Relocatable.of_chunkedStatesTail920At A.repAlloc (.noHeaderReceived st))
    (sp + 0x590#64) (sp + 0x958#64) (s0 := s0) (sp_call := sp)
    (Frame := ((sp + 0x950#64) ↦₆₄ 7#64) ∗ memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_124).base + 1304#64) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by dsimp only [chunkedStatesWord0]; sep_ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf hvm_sf
  have hvm_s_sf : VmPreserved s sf := (by simp only [arm64_norm] : VmPreserved s _).trans hvm_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf
  wp_steps
  refine finish_sepWP
    (hnext _ ⟨by simp only [spqrSendPlacedEntry, arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, chunkedStatesWord0, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *]⟩
      (hvm_s_sf.trans (by simp only [arm64_norm])))
    (imm_arm_post_entails A.repAlloc sp 7#64 _ _ _ .none (.noHeaderReceived st) Frame
      (by simp only [arm64_norm]; rfl) (by dsimp only [spqrSendPayloadSlotAt]; simp only [arm64_norm]))

theorem step_send_arm_noHeaderReceived_pool_placed {F : ShaCompress} {M : AllocCostModel}
    (A : RustCliAllocBudget M) {lim : BudgetLimits} (bSt : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext) {s0 s : State} (sp : BitVec 64)
    (st : NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 1284#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = 7#64) (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx25 : s.readReg64 .x25 = sp + 0x550#64) (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (A.pool lim bSt s ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.noHeaderReceived st) ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920) ∗ Frame)
    (hnext : ∀ sf : State, SpqrSendJoinStatePlaced sp ext s0 sf
        { epoch := st.uc.epoch, payload := .none } (.noHeaderReceived st) →
      VmPreserved s sf →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) sf
        ((A.pool lim bSt sf ∗ memRegion (sp + 0x950#64) 928 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) .none ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.noHeaderReceived st)) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) s P post := by
  have hP' : P = (chunkedStatesAt A.repAlloc (sp + 0x950#64) (.noHeaderReceived st) ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920) ∗
      (A.pool lim bSt s ∗ Frame) := by
    rw [hP]; sep_ac_rfl
  refine step_send_arm_noHeaderReceived_placed A ext hA sp st hpc hrun hsp hsp_align
    htr hx19 hx20 hx24 hx25 hx26 hx28 hvregs hP' (fun sf hjoin hvm => ?_)
  have hpool :
      (memRegion (sp + 0x950#64) 928 ∗
        spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) .none ∗
        spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
        chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.noHeaderReceived st)) ∗
        (A.pool lim bSt s ∗ Frame) =
      (A.pool lim bSt sf ∗ memRegion (sp + 0x950#64) 928 ∗
        spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) .none ∗
        spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
        chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.noHeaderReceived st)) ∗ Frame := by
    rw [A.pool_transport lim bSt s sf hvm]; sep_ac_rfl
  rw [hpool]
  exact hnext sf hjoin hvm

/-- Relocatable immediate arm 3: `.ct1Acknowledged st` (`+952 -> +1288 -> +3064 -> +3068`), forwarding
    `VmPreserved s sf`. -/
theorem step_send_arm_ct1Acknowledged_placed {F : ShaCompress} {M : AllocCostModel}
    (A : RustCliAllocBudget M) {lim : BudgetLimits} (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext) {s0 s : State} (sp : BitVec 64)
    (st : Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 952#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = 11#64) (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx25 : s.readReg64 .x25 = sp + 0x550#64) (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (chunkedStatesAt A.repAlloc (sp + 0x950#64) (.ct1Acknowledged st) ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920) ∗ Frame)
    (hnext : ∀ sf : State, SpqrSendJoinStatePlaced sp ext s0 sf
        { epoch := st.uc.epoch, payload := .none } (.ct1Acknowledged st) →
      VmPreserved s sf →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) sf
        ((memRegion (sp + 0x950#64) 928 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) .none ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ct1Acknowledged st)) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) s P post := by
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  subst hP
  rw [chunkedStatesAt_eq_word0_tail920 A.repAlloc (sp + 0x950#64) (.ct1Acknowledged st),
      show (sp + 0x950#64) + 8#64 = sp + 0x958#64 by rw [BitVec.add_assoc]; rfl]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_ct1Acknowledged A.repAlloc sp st
  rw [h_ep]; wp_steps; rw [← h_ep]
  refine call_memcpy_relocate hmemcpy
    (CryptoVerification.SpqrV1.Top.Send.Relocatable.of_chunkedStatesTail920At A.repAlloc (.ct1Acknowledged st))
    (sp + 0x590#64) (sp + 0x958#64) (s0 := s0) (sp_call := sp)
    (Frame := ((sp + 0x950#64) ↦₆₄ 11#64) ∗ memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_124).base + 1304#64) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by dsimp only [chunkedStatesWord0]; sep_ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf hvm_sf
  have hvm_s_sf : VmPreserved s sf := (by simp only [arm64_norm] : VmPreserved s _).trans hvm_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf
  wp_steps
  refine finish_sepWP
    (hnext _ ⟨by simp only [spqrSendPlacedEntry, arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, chunkedStatesWord0, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *]⟩
      (hvm_s_sf.trans (by simp only [arm64_norm])))
    (imm_arm_post_entails A.repAlloc sp 11#64 _ _ _ .none (.ct1Acknowledged st) Frame
      (by simp only [arm64_norm]; rfl) (by dsimp only [spqrSendPayloadSlotAt]; simp only [arm64_norm]))

theorem step_send_arm_ct1Acknowledged_pool_placed {F : ShaCompress} {M : AllocCostModel}
    (A : RustCliAllocBudget M) {lim : BudgetLimits} (bSt : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext) {s0 s : State} (sp : BitVec 64)
    (st : Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 952#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = 11#64) (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx25 : s.readReg64 .x25 = sp + 0x550#64) (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (A.pool lim bSt s ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.ct1Acknowledged st) ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920) ∗ Frame)
    (hnext : ∀ sf : State, SpqrSendJoinStatePlaced sp ext s0 sf
        { epoch := st.uc.epoch, payload := .none } (.ct1Acknowledged st) →
      VmPreserved s sf →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) sf
        ((A.pool lim bSt sf ∗ memRegion (sp + 0x950#64) 928 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) .none ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ct1Acknowledged st)) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) s P post := by
  have hP' : P = (chunkedStatesAt A.repAlloc (sp + 0x950#64) (.ct1Acknowledged st) ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920) ∗
      (A.pool lim bSt s ∗ Frame) := by
    rw [hP]; sep_ac_rfl
  refine step_send_arm_ct1Acknowledged_placed A ext hA sp st hpc hrun hsp hsp_align
    htr hx19 hx20 hx24 hx25 hx26 hx28 hvregs hP' (fun sf hjoin hvm => ?_)
  have hpool :
      (memRegion (sp + 0x950#64) 928 ∗
        spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) .none ∗
        spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
        chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ct1Acknowledged st)) ∗
        (A.pool lim bSt s ∗ Frame) =
      (A.pool lim bSt sf ∗ memRegion (sp + 0x950#64) 928 ∗
        spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) .none ∗
        spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
        chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ct1Acknowledged st)) ∗ Frame := by
    rw [A.pool_transport lim bSt s sf hvm]; sep_ac_rfl
  rw [hpool]
  exact hnext sf hjoin hvm

/-! ## Budget Leaf-Call Combinators with `LibsignalCodeRoLoaded` -/

private theorem panic_frame_anyHeap {m : Memory} {φ₁ φ₂ : Prop} {F Fr : SepProp}
    (himp : φ₁ → φ₂) (hm : m ⊨ ((⌜φ₁⌝ ∗ anyHeap) ∗ F) ∗ Fr) :
    m ⊨ (⌜φ₂⌝ ∗ anyHeap) ∗ Fr := by
  have h1 : ((⌜φ₁⌝ ∗ anyHeap) ∗ F) ∗ Fr ⊢ ⌜φ₁⌝ ∗ ((anyHeap ∗ F) ∗ Fr) :=
    Entails.of_eq (by sep_ac_rfl)
  have hm' := Satisfies.mono h1 hm
  rw [satisfies_pure_sepConj] at hm'
  exact Satisfies.mono (sepConj_mono_left (Entails.pure_right (himp hm'.1) (entails_anyHeap _))) hm'.2

/-- Call a non-panicking budget subroutine (`withLsCodeRoLoaded lsmpl spec`) inside `SepWPp`
    (with arbitrary `Q`, `Qp`, `oom`) that uses `n ≤ spqrSendCalleeStack` bytes of stack and
    returns `∃∗ evs : List AllocEvent` in `spec.post`. -/
theorem call_lscro_calleeStack {α : Type} {prog : Program}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {s : State}
    (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide)
    {P T_pre : SepProp} {T_post : List AllocEvent → State → SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp} {F : SepProp}
    {φ_pre : Prop} {φ_post : List AllocEvent → State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec_pre : spec.pre x s = (⌜φ_pre⌝ ∗ T_pre ∗ stackAt s.sp n)) (hφ : φ_pre)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ T_pre) ∗ F)
    (hspec_post : ∀ sf, spec.post x s sf =
      (∃∗ evs : List AllocEvent, ⌜φ_post evs sf⌝ ∗ T_post evs sf ∗ stackAt s.sp n))
    (hnext : ∀ (evs : List AllocEvent) (sf : State),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      φ_post evs sf → LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp prog ret sf ((stackAt sp spqrSendCalleeStack ∗ T_post evs sf) ∗ F) Q Qp oom)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q Qp oom := by
  let F_ext := memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F
  have hsp_al : s.spAligned = true := by unfold State.spAligned; rw [hsp]; exact hsp_align
  intro R' hm hL
  have hpre : s.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F_ext ∗ R') := by
    change s.mem ⊨ (spec.pre x s ∗ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗ (F_ext ∗ R')
    rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [hspec_pre, hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hφ, ?_⟩
    rw [hP, stackAt_spqrSendCallee_split sp n hle] at hm
    exact Satisfies.mono (Entails.of_eq (by dsimp only [F_ext]; sep_ac_rfl)) hm
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F_ext ∗ R') s hpc hrun hpre hsp_al hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · change sm.mem ⊨ spec.post x s sm ∗ (F_ext ∗ R') at hpost
    rw [hspec_post sm, hsp, sepExists_sepConj_left] at hpost
    rcases (satisfies_sepExists _ _).mp hpost with ⟨evs, hpost⟩
    have hpost' : sm.mem ⊨ ⌜φ_post evs sm⌝ ∗
        (((stackAt sp spqrSendCalleeStack ∗ T_post evs sm) ∗ F) ∗ R') := by
      rw [stackAt_spqrSendCallee_split sp n hle]
      exact Satisfies.mono (Entails.of_eq (by dsimp only [F_ext]; sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hpost'
    rcases hpost' with ⟨hφ_post, hpost_mem⟩
    rw [hlr] at hpcm
    rw [hsp] at hspm
    rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, _, hvregs⟩
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext evs sm hpcm hrunm hspm hφ_post (hcrl.of_keepsFrozen hsteps.keepsFrozen)
        hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs R' hpost_mem (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeRoLoaded] at hpost
    rw [hpan_eq sm] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCodeRoLoaded] at hpost
    rw [hexit_eq code sm] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCodeRoLoaded] at hpost
    rw [hoom_eq sm] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

/-- Total-correctness `SepWP` counterpart of `call_lscro_calleeStack` (for use under
    `sepWP_seq_lscro`). -/
theorem call_lscro_calleeStack_sepWP {α : Type} {prog : Program}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {s : State}
    (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide)
    {P T_pre : SepProp} {T_post : List AllocEvent → State → SepProp}
    {Q : State → SepProp → Prop} {oom : State → SepProp} {F : SepProp}
    {φ_pre : Prop} {φ_post : List AllocEvent → State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec_pre : spec.pre x s = (⌜φ_pre⌝ ∗ T_pre ∗ stackAt s.sp n)) (hφ : φ_pre)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ T_pre) ∗ F)
    (hspec_post : ∀ sf, spec.post x s sf =
      (∃∗ evs : List AllocEvent, ⌜φ_post evs sf⌝ ∗ T_post evs sf ∗ stackAt s.sp n))
    (hnext : ∀ (evs : List AllocEvent) (sf : State),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      φ_post evs sf → LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP prog ret sf ((stackAt sp spqrSendCalleeStack ∗ T_post evs sf) ∗ F) Q oom)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWP prog ret s P Q oom := by
  let F_ext := memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F
  have hcall' : subroutine_ok prog entry
      { withLsCodeRoLoaded lsmpl spec with
        post := fun x' s0' sf => ⌜LibsignalCodeRoLoaded lsmpl sf.mem⌝ ∗ spec.post x' s0' sf } := by
    refine Arm64.subroutine_ok.of_codeLoaded fun x' R s0' hpc0 hrun0 hpre0 hsp0 hL0 => ?_
    have hcrl0 : LibsignalCodeRoLoaded lsmpl s0'.mem := by
      change s0'.mem ⊨ (spec.pre x' s0' ∗ ⌜LibsignalCodeRoLoaded lsmpl s0'.mem⌝) ∗ R at hpre0
      rw [sepConj_comm (spec.pre x' s0'), sepConj_assoc, satisfies_pure_sepConj] at hpre0
      exact hpre0.1
    obtain ⟨sf, hsteps, hout, -⟩ := hcall.no_fault_before_outcome x' R s0' hpc0 hrun0 hpre0 hsp0 hL0
    refine Arm64.reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
    rcases hout with ⟨hret, hcc, hpost⟩ | hrest
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hcrl0.of_keepsFrozen hsteps.keepsFrozen, hpost⟩
    · exact Or.inr hrest
  have hsp_al : s.spAligned = true := by unfold State.spAligned; rw [hsp]; exact hsp_align
  refine SepWP.call_subroutine_frame hcall' (x := x) (F := F_ext) hpc hrun hsp_al hlr
    (fun R' hm => by
      change s.mem ⊨ (spec.pre x s ∗ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗ (F_ext ∗ R')
      rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hcrl, ?_⟩
      rw [hspec_pre, hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hφ, ?_⟩
      rw [hP, stackAt_spqrSendCallee_split sp n hle] at hm
      exact Satisfies.mono (Entails.of_eq (by dsimp only [F_ext]; sep_ac_rfl)) hm)
    (fun R' sm _ hpost => by
      dsimp only [withLsCodeRoLoaded] at hpost
      rw [hpan_eq sm] at hpost
      exact not_satisfies_false_sepConj hpost)
    (fun R' code sm _ hpost => by
      dsimp only [withLsCodeRoLoaded] at hpost
      rw [hexit_eq code sm] at hpost
      exact not_satisfies_false_sepConj hpost)
    (fun sm hpcm hrunm hspm hcsm => ?_)
    (fun R' sm _ hpost => by
      dsimp only [withLsCodeRoLoaded] at hpost
      rw [hoom_eq sm] at hpost
      exact False.elim (not_satisfies_false_sepConj hpost))
  dsimp only
  rw [hsp] at hspm
  rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, _, hvregs⟩
  rw [sepConj_assoc]
  refine SepWP.pure_elim fun hcrl_m => ?_
  rw [hspec_post sm, hsp, sepExists_sepConj_left]
  refine SepWP.exists_elim fun evs => ?_
  have hpeq : (⌜φ_post evs sm⌝ ∗ T_post evs sm ∗ stackAt sp n) ∗ F_ext =
      ⌜φ_post evs sm⌝ ∗ ((stackAt sp spqrSendCalleeStack ∗ T_post evs sm) ∗ F) := by
    rw [stackAt_spqrSendCallee_split sp n hle]
    dsimp only [F_ext]
    sep_ac_rfl
  rw [hpeq]
  exact SepWP.pure_elim fun hφ_post =>
    hnext evs sm hpcm hrunm hspm hφ_post hcrl_m hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs

/-- Panic-forwarding variant of `call_lscro_calleeStack` for callees with
    `spec.onPanic x s sf = ⌜φ_pan sf⌝ ∗ anyHeap` (`φ_pan sm → φ_out sm`). -/
theorem call_lscro_calleeStack_anyPanic {α : Type} {prog : Program}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {s : State}
    (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide)
    {P T_pre : SepProp} {T_post : List AllocEvent → State → SepProp}
    {Q : State → SepProp → Prop} {oom : State → SepProp} {Fr F : SepProp}
    {φ_pre : Prop} {φ_post : List AllocEvent → State → Prop} {φ_pan φ_out : State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec_pre : spec.pre x s = (⌜φ_pre⌝ ∗ T_pre ∗ stackAt s.sp n)) (hφ : φ_pre)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ T_pre) ∗ F)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = (⌜φ_pan sf⌝ ∗ anyHeap))
    (hpan_imp : ∀ sm : State, φ_pan sm → φ_out sm)
    (hspec_post : ∀ sf, spec.post x s sf =
      (∃∗ evs : List AllocEvent, ⌜φ_post evs sf⌝ ∗ T_post evs sf ∗ stackAt s.sp n))
    (hnext : ∀ (evs : List AllocEvent) (sf : State),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      φ_post evs sf → LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp prog ret sf ((stackAt sp spqrSendCalleeStack ∗ T_post evs sf) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_out sf⌝ ∗ anyHeap) ∗ Fr)) oom)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_out sf⌝ ∗ anyHeap) ∗ Fr)) oom := by
  let F_ext := memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F
  have hsp_al : s.spAligned = true := by unfold State.spAligned; rw [hsp]; exact hsp_align
  intro R' hm hL
  have hpre : s.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F_ext ∗ R') := by
    change s.mem ⊨ (spec.pre x s ∗ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗ (F_ext ∗ R')
    rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [hspec_pre, hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hφ, ?_⟩
    rw [hP, stackAt_spqrSendCallee_split sp n hle] at hm
    exact Satisfies.mono (Entails.of_eq (by dsimp only [F_ext]; sep_ac_rfl)) hm
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F_ext ∗ R') s hpc hrun hpre hsp_al hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · change sm.mem ⊨ spec.post x s sm ∗ (F_ext ∗ R') at hpost
    rw [hspec_post sm, hsp, sepExists_sepConj_left] at hpost
    rcases (satisfies_sepExists _ _).mp hpost with ⟨evs, hpost⟩
    have hpost' : sm.mem ⊨ ⌜φ_post evs sm⌝ ∗
        (((stackAt sp spqrSendCalleeStack ∗ T_post evs sm) ∗ F) ∗ R') := by
      rw [stackAt_spqrSendCallee_split sp n hle]
      exact Satisfies.mono (Entails.of_eq (by dsimp only [F_ext]; sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hpost'
    rcases hpost' with ⟨hφ_post, hpost_mem⟩
    rw [hlr] at hpcm
    rw [hsp] at hspm
    rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, _, hvregs⟩
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext evs sm hpcm hrunm hspm hφ_post (hcrl.of_keepsFrozen hsteps.keepsFrozen)
        hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs R' hpost_mem (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · change sm.mem ⊨ spec.onPanic x s sm ∗ (F_ext ∗ R') at hpost
    rw [← sepConj_assoc] at hpost
    refine ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, spec.onPanic x s sm ∗ F_ext, hpost, fun hmFr => ?_⟩)⟩
    rw [hpan_eq sm] at hmFr
    exact panic_frame_anyHeap (hpan_imp sm) hmFr
  · dsimp only [withLsCodeRoLoaded] at hpost
    rw [hexit_eq code sm] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCodeRoLoaded] at hpost
    rw [hoom_eq sm] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

/-- Total-correctness `SepWP` counterpart of `finish_sepWP_lscro`. -/
theorem finish_sepWP_lscro_total {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = mid) (hrun : s.status = .Running)
    (hnext : LibsignalCodeRoLoaded lsmpl s.mem → SepWP prog ret s P' Q) (hent : P ⊢ P') :
    SepWP prog mid s P (fun sm Pm => LibsignalCodeRoLoaded lsmpl sm.mem → SepWP prog ret sm Pm Q) := by
  refine SepWP.fold hent (sepConj_emp _).symm ?_
  rw [sepConj_emp]
  exact SepWP.done hpc hrun hnext

/-- Budget-threaded spatial reassembly entailment at the `+3068` join point after a leaf-call arm. -/
theorem leaf_arm_post_entails_placed {F : ShaCompress} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (bSt : M.σ) (sf : State)
    (sp w0 x21 x27 : BitVec 64) (x24_8 : BitVec 8) (sz : Nat)
    (P F_out : SepProp) (chunk : Chunk)
    (pay : MessagePayload spqrPolyApi) (nextSt : States spqrPolyApi (spqrAuthApi F))
    (Frame : SepProp) (hsz : sz ≤ 920 := by decide) (hx21 : x21 = noneCap)
    (hpay : chunkAt (sp + 0x550#64) chunk ∗ memRegion (sp + 0x572#64) 4 ⊢ spqrSendPayloadSlotAt sp x24_8 pay)
    (htail : F_out ∗ memRegion ((sp + 0x590#64) + BitVec.ofNat 64 sz) (920 - sz) =
      chunkedStatesTail920At A.repAlloc (sp + 0x590#64) nextSt)
    (hP_eq : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim bSt sf ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        (((sp + 0x950#64) ↦₆₄ w0) ∗ memRegion (sp + 0x958#64) sz ∗
          memRegion ((sp + 0x958#64) + BitVec.ofNat 64 sz) (920 - sz)) ∗
        (memRegion (sp + 0x1260#64) sz ∗ chunkAt ((sp + 0x1260#64) + BitVec.ofNat 64 sz) chunk) ∗
        (chunkAt (sp + 0x550#64) chunk ∗ memRegion (sp + 0x572#64) 4) ∗ memRegion (sp + 0x580#64) 16 ∗
        (F_out ∗ memRegion ((sp + 0x590#64) + BitVec.ofNat 64 sz) (920 - sz))) ∗ Frame) :
    P ⊢ (stackAt sp spqrSendCalleeStack ∗ A.pool lim bSt sf ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (sz + chunkSize) ∗
        spqrSendPayloadSlotAt sp x24_8 pay ∗ spqrSendKeySlotAt A.repAlloc sp x21 x27 none ∗
        chunkedStatesTail920At A.repAlloc (sp + 0x590#64) nextSt) ∗ Frame := by
  have hkey : memRegion (sp + 0x580#64) 16 ⊢ spqrSendKeySlotAt A.repAlloc sp x21 x27 none := by
    dsimp only [spqrSendKeySlotAt]; exact Entails.pure_right hx21 (Entails.refl _)
  have h1 := word0_sz_pad_entails_memRegion_928 sp w0 sz hsz
  have h2 := scratch_and_chunk_entails_memRegion sp sz chunk (by omega)
  rw [hP_eq, htail]
  exact sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono hpay (sepConj_mono_left hkey))))))))

end LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1PlacedBudget
