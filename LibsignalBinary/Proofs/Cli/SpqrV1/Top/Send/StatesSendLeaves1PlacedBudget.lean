/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves1Placed
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1StepsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base

/-!
# Budget-Threaded Relocatable Immediate Arms & Leaf-Call Helpers (Block `427`)

Proves `VmPreserved` immediate arms (`ekSentCt1Received`, `noHeaderReceived`, `ct1Acknowledged`)
and budget-preserving leaf-call tail helpers in Block `427`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves1PlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement libsignalSessionCode lsmpl lsρ)
open CryptoVerification.Cli.SpqrV1.Top.Send (SpqrSendJoinStatePlaced)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPC_427 blkPl_427)
open CryptoVerification.LibsignalSpqrV1
  (Chunk Message MessagePayload States spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (Ct1Acknowledged NoHeaderReceived)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk (EkSentCt1Received)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded extract_withLsCodeRoLoaded sepWP_seq_lscro sessionMemcpyRegionSpec
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop (chunkedStatesAt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (chunkAt chunkSize)
open CryptoVerification.SpqrV1.States.Leaves (Relocatable relocatedHeap)
open CryptoVerification.SpqrV1.Top.Send
  (chunkedStatesAt_eq_word0_tail920 chunkedStatesTail920At chunkedStatesWord0
   expose_epoch_ct1Acknowledged expose_epoch_ekSentCt1Received expose_epoch_noHeaderReceived
   finish_sepWP imm_arm_post_entails relocate_post_entails relocate_pre_entails
   scratch_and_chunk_entails_memRegion spqrSendCalleeStack spqrSendKeySlotAt spqrSendPayloadSlotAt
   stackAt_spqrSendCallee_split word0_sz_pad_entails_memRegion_928)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced spqrSendPlacedEntry spqrSendPlacedProg)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1StepsPlacedBudget
  (spqrSend_session_memcpy_region_ok_placed)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)

export CryptoVerification.Cli.SpqrV1.Top.Send
  (SpqrSendJoinStatePlaced of_sepWP_lscro finish_sepWP_lscro)

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
run_cmd Lean.Elab.Command.liftCoreM do
  for nm in [
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp] do
    Lean.Attribute.erase nm `arm64_norm
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

omit [LibsignalPlacement] in
private theorem sp_950_add_8 (sp : BitVec 64) : (sp + 0x950#64) + 8#64 = sp + 0x958#64 := by
  bv_omega

/-! ## 1. `VmPreserved`-Propagating `memcpy` Relocation & Relocatable Immediate Arms -/

omit [LibsignalPlacement] in
/-- Framed `memcpy` call rule on `sessionMemcpyRegionBudgetSpec` that relocates any
    `Relocatable n F` predicate from `src` to `dst` while propagating `VmPreserved s sf`. -/
theorem call_memcpy_relocate_vm {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionBudgetSpec)
    {n : Nat} {F : BitVec 64 → SepProp} (hrel : Relocatable n F) (dst src : BitVec 64)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = dst) (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n) (hsplit : P = (memRegion dst n ∗ F src) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call → sf.trace = s0.trace →
      VmPreserved s sf →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
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
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) (htr.trans htrace) hvm_sf
      hcs_sf.1 hcs_sf.2.1 hcs_sf.2.2.1 hcs_sf.2.2.2.1 hcs_sf.2.2.2.2.1
      hcs_sf.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.1
      hcs_sf.2.2.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.2.2.2.2

/-- VM-preserving relocatable immediate arm 1: `.ekSentCt1Received s` (`+924 -> +3064 -> +3068`). -/
theorem step_send_arm_ekSentCt1Received_placed_vm {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
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
  rw [chunkedStatesAt_eq_word0_tail920 A.repAlloc (sp + 0x950#64) (.ekSentCt1Received st), sp_950_add_8 sp]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_ekSentCt1Received A.repAlloc sp st; rw [h_ep]; wp_steps; rw [← h_ep]
  refine call_memcpy_relocate_vm hmemcpy (CryptoVerification.SpqrV1.Top.Send.Relocatable.of_chunkedStatesTail920At A.repAlloc (.ekSentCt1Received st))
    (sp + 0x590#64) (sp + 0x958#64) (s0 := s0) (sp_call := sp)
    (Frame := ((sp + 0x950#64) ↦₆₄ 6#64) ∗ memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_427).base + 944#64) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by dsimp only [chunkedStatesWord0]; sep_ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hvm_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf
  have hvm_s_sf : VmPreserved s sf := VmPreserved.trans (by simp only [arm64_norm, wp_norm]) hvm_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf; wp_steps
  refine finish_sepWP
    (hnext _ ⟨by simp only [spqrSendPlacedEntry, arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, chunkedStatesWord0, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *]⟩
      (hvm_s_sf.trans (by simp only [arm64_norm, wp_norm])))
    (imm_arm_post_entails A.repAlloc sp 6#64 _ _ _ (.ct1Ack true) (.ekSentCt1Received st) Frame
      (by simp only [arm64_norm]; rfl) (by dsimp only [spqrSendPayloadSlotAt]; simp only [arm64_norm]))

/-- Pool-threading relocatable immediate arm 1: `.ekSentCt1Received s` (`+924 -> +3064 -> +3068`). -/
theorem step_send_arm_ekSentCt1Received_placed {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
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
    (hP : P = (chunkedStatesAt A.repAlloc (sp + 0x950#64) (.ekSentCt1Received st) ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      A.pool lim st0 s) ∗ Frame)
    (hnext : ∀ sf : State, SpqrSendJoinStatePlaced sp ext s0 sf
        { epoch := st.uc.epoch, payload := .ct1Ack true } (.ekSentCt1Received st) →
      VmPreserved s sf →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) sf
        ((memRegion (sp + 0x950#64) 928 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct1Ack true) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ekSentCt1Received st) ∗
          A.pool lim st0 sf) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) s P post := by
  refine step_send_arm_ekSentCt1Received_placed_vm A lim ext hA sp st
    (Frame := A.pool lim st0 s ∗ Frame)
    hpc hrun hsp hsp_align htr hx19 hx20 hx24 hx25 hx26 hx28 hvregs
    (by rw [hP]; sep_ac_rfl) fun sf hjoin hvm => ?_
  refine finish_sepWP (hnext sf hjoin hvm) ?_
  rw [A.pool_of_vmPreserved hvm]
  exact Entails.of_eq (by sep_ac_rfl)

/-- VM-preserving relocatable immediate arm 2: `.noHeaderReceived s` (`+1284 -> +3064 -> +3068`). -/
theorem step_send_arm_noHeaderReceived_placed_vm {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
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
  rw [chunkedStatesAt_eq_word0_tail920 A.repAlloc (sp + 0x950#64) (.noHeaderReceived st), sp_950_add_8 sp]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_noHeaderReceived A.repAlloc sp st; rw [h_ep]; wp_steps; rw [← h_ep]
  refine call_memcpy_relocate_vm hmemcpy (CryptoVerification.SpqrV1.Top.Send.Relocatable.of_chunkedStatesTail920At A.repAlloc (.noHeaderReceived st))
    (sp + 0x590#64) (sp + 0x958#64) (s0 := s0) (sp_call := sp)
    (Frame := ((sp + 0x950#64) ↦₆₄ 7#64) ∗ memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_427).base + 1304#64) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by dsimp only [chunkedStatesWord0]; sep_ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hvm_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf
  have hvm_s_sf : VmPreserved s sf := VmPreserved.trans (by simp only [arm64_norm, wp_norm]) hvm_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf; wp_steps
  refine finish_sepWP
    (hnext _ ⟨by simp only [spqrSendPlacedEntry, arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, chunkedStatesWord0, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *]⟩
      (hvm_s_sf.trans (by simp only [arm64_norm, wp_norm])))
    (imm_arm_post_entails A.repAlloc sp 7#64 _ _ _ .none (.noHeaderReceived st) Frame
      (by simp only [arm64_norm]; rfl) (by dsimp only [spqrSendPayloadSlotAt]; simp only [arm64_norm]))

/-- Pool-threading relocatable immediate arm 2: `.noHeaderReceived s` (`+1284 -> +3064 -> +3068`). -/
theorem step_send_arm_noHeaderReceived_placed {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
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
    (hP : P = (chunkedStatesAt A.repAlloc (sp + 0x950#64) (.noHeaderReceived st) ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      A.pool lim st0 s) ∗ Frame)
    (hnext : ∀ sf : State, SpqrSendJoinStatePlaced sp ext s0 sf
        { epoch := st.uc.epoch, payload := .none } (.noHeaderReceived st) →
      VmPreserved s sf →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) sf
        ((memRegion (sp + 0x950#64) 928 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) .none ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.noHeaderReceived st) ∗
          A.pool lim st0 sf) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) s P post := by
  refine step_send_arm_noHeaderReceived_placed_vm A lim ext hA sp st
    (Frame := A.pool lim st0 s ∗ Frame)
    hpc hrun hsp hsp_align htr hx19 hx20 hx24 hx25 hx26 hx28 hvregs
    (by rw [hP]; sep_ac_rfl) fun sf hjoin hvm => ?_
  refine finish_sepWP (hnext sf hjoin hvm) ?_
  rw [A.pool_of_vmPreserved hvm]
  exact Entails.of_eq (by sep_ac_rfl)

/-- VM-preserving relocatable immediate arm 3: `.ct1Acknowledged s` (`+952 -> +1288 -> +3064 -> +3068`). -/
theorem step_send_arm_ct1Acknowledged_placed_vm {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
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
  rw [chunkedStatesAt_eq_word0_tail920 A.repAlloc (sp + 0x950#64) (.ct1Acknowledged st), sp_950_add_8 sp]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_ct1Acknowledged A.repAlloc sp st; rw [h_ep]; wp_steps; rw [← h_ep]
  refine call_memcpy_relocate_vm hmemcpy (CryptoVerification.SpqrV1.Top.Send.Relocatable.of_chunkedStatesTail920At A.repAlloc (.ct1Acknowledged st))
    (sp + 0x590#64) (sp + 0x958#64) (s0 := s0) (sp_call := sp)
    (Frame := ((sp + 0x950#64) ↦₆₄ 11#64) ∗ memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_427).base + 1304#64) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by dsimp only [chunkedStatesWord0]; sep_ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hvm_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf
  have hvm_s_sf : VmPreserved s sf := VmPreserved.trans (by simp only [arm64_norm, wp_norm]) hvm_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf; wp_steps
  refine finish_sepWP
    (hnext _ ⟨by simp only [spqrSendPlacedEntry, arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, chunkedStatesWord0, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *]⟩
      (hvm_s_sf.trans (by simp only [arm64_norm, wp_norm])))
    (imm_arm_post_entails A.repAlloc sp 11#64 _ _ _ .none (.ct1Acknowledged st) Frame
      (by simp only [arm64_norm]; rfl) (by dsimp only [spqrSendPayloadSlotAt]; simp only [arm64_norm]))

/-- Pool-threading relocatable immediate arm 3: `.ct1Acknowledged s` (`+952 -> +1288 -> +3064 -> +3068`). -/
theorem step_send_arm_ct1Acknowledged_placed {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
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
    (hP : P = (chunkedStatesAt A.repAlloc (sp + 0x950#64) (.ct1Acknowledged st) ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      A.pool lim st0 s) ∗ Frame)
    (hnext : ∀ sf : State, SpqrSendJoinStatePlaced sp ext s0 sf
        { epoch := st.uc.epoch, payload := .none } (.ct1Acknowledged st) →
      VmPreserved s sf →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) sf
        ((memRegion (sp + 0x950#64) 928 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) .none ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ct1Acknowledged st) ∗
          A.pool lim st0 sf) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) s P post := by
  refine step_send_arm_ct1Acknowledged_placed_vm A lim ext hA sp st
    (Frame := A.pool lim st0 s ∗ Frame)
    hpc hrun hsp hsp_align htr hx19 hx20 hx24 hx25 hx26 hx28 hvregs
    (by rw [hP]; sep_ac_rfl) fun sf hjoin hvm => ?_
  refine finish_sepWP (hnext sf hjoin hvm) ?_
  rw [A.pool_of_vmPreserved hvm]
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## 2. Budget-Ready Leaf-Call Combinators with `LibsignalCodeRoLoaded lsmpl s.mem` -/

/-- Run a non-panicking `SepWP` segment to `mid`, propagating `LibsignalCodeRoLoaded lsmpl`
    to a non-panicking `SepWP` continuation. -/
theorem of_sepWP_lscro_plain {prog : Program} {tgt mid : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm => LibsignalCodeRoLoaded lsmpl sm.mem → SepWP prog tgt sm Pm post)) :
    SepWP prog tgt s P post :=
  sepWP_seq_lscro hcrl h

theorem finish_sepWP_lscro_plain {prog : Program} {mid tgt : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = mid) (hrun : s.status = .Running)
    (hnext : LibsignalCodeRoLoaded lsmpl s.mem → SepWP prog tgt s P' post) (hent : P ⊢ P') :
    SepWP prog mid s P (fun sm Pm => LibsignalCodeRoLoaded lsmpl sm.mem → SepWP prog tgt sm Pm post) := by
  refine SepWP.fold hent (sepConj_emp _).symm ?_
  rw [sepConj_emp]
  exact SepWP.done hpc hrun hnext

omit [LibsignalPlacement] in
/-- Extract a leading existential `∃∗ a, P a` from the precondition of `SepWPp`. -/
theorem sepWPp_exists_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ a : α, SepWPp prog ret s (P a) Q Qp) :
    SepWPp prog ret s (∃∗ a : α, P a) Q Qp := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, hma⟩ := hm
  exact h a R hma hL

private theorem lift_subroutine_ok_lscro_post {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok prog entry
      { withLsCodeRoLoaded lsmpl spec with
        post := fun x' s0' sf => ⌜LibsignalCodeRoLoaded lsmpl sf.mem⌝ ∗ spec.post x' s0' sf } := by
  refine Arm64.subroutine_ok.of_codeLoaded fun x' R s0' hpc0 hrun0 hpre0 hsp0 hL0 => ?_
  have ⟨hcrl0, _⟩ := extract_withLsCodeRoLoaded hpre0
  obtain ⟨sf, hsteps, hout, -⟩ := hcall.no_fault_before_outcome x' R s0' hpc0 hrun0 hpre0 hsp0 hL0
  refine Arm64.reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcrl0.of_keepsFrozen hsteps.keepsFrozen, hpost⟩
  · exact Or.inr hrest

/-- Call a panic-capable budget subroutine (`withLsCodeRoLoaded lsmpl spec`) that uses
    `n ≤ spqrSendCalleeStack` bytes of stack, generalized over any panic proposition `Pan`. -/
theorem call_lscro_calleeStack {α : Type} {prog : Program}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide)
    {P T_pre : SepProp} {T_post : State → SepProp} {Q : State → SepProp → Prop} {Fr F : SepProp}
    {Pan φ_pre : Prop} {φ_post : State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec_pre : spec.pre x s = (⌜φ_pre⌝ ∗ T_pre ∗ stackAt s.sp n)) (hφ : φ_pre)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ T_pre) ∗ F)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hpan : ∀ sf, spec.onPanic x s sf ⊢ ⌜Pan ∧ s.trace <+: sf.trace⌝ ∗ anyHeap)
    (hspec_post : ∀ sf, spec.post x s sf = (⌜φ_post sf⌝ ∗ T_post sf ∗ stackAt s.sp n))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      φ_post sf → LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp prog ret sf ((stackAt sp spqrSendCalleeStack ∗ T_post sf) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
          (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  have hcall' := lift_subroutine_ok_lscro_post hcall
  have hsp_al : s.spAligned = true := by unfold State.spAligned; rw [hsp]; exact hsp_align
  refine SepWPp.call_wpp (x := x)
    (F := memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F)
    hcall' hpc hrun hsp_al hlr
    (fun R' hm => by
      change s.mem ⊨ (spec.pre x s ∗ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗
        ((memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F) ∗ R')
      rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
      rw [hspec_pre, hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hφ, ?_⟩
      rw [hP, stackAt_spqrSendCallee_split sp n hle] at hm
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)
    (fun sm code R' _ hpost => by
      dsimp only [withLsCodeRoLoaded] at hpost; rw [hexit_eq code sm] at hpost
      exact allowPanic_not_exited hpost)
    (fun sm _ _ hmFr => by
      dsimp only [withLsCodeRoLoaded] at hmFr
      have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left (hpan sm))) hmFr
      rw [htr] at hm1
      have hassoc :
          ((⌜Pan ∧ s0.trace <+: sm.trace⌝ ∗ anyHeap) ∗
            (memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F)) =
          (⌜Pan ∧ s0.trace <+: sm.trace⌝ ∗
            (anyHeap ∗
              (memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F))) := by
        sep_ac_rfl
      rw [hassoc] at hm1
      exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (entails_anyHeap _))) hm1)
    (fun sm hpcm hrunm hspm hcsm => ?_)
    (fun sm R' _ hpost => by
      dsimp only [withLsCodeRoLoaded] at hpost; rw [hoom_eq sm] at hpost
      exact (allowPanic_not_exited hpost).elim)
  rw [hsp] at hspm
  rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, _, hvregs⟩
  have hpeq : (⌜LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗ spec.post x s sm) ∗
      (memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F) =
      ⌜LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗
        (⌜φ_post sm⌝ ∗ ((stackAt sp spqrSendCalleeStack ∗ T_post sm) ∗ F)) := by
    rw [hspec_post sm, hsp, stackAt_spqrSendCallee_split sp n hle]; sep_ac_rfl
  dsimp only
  exact SepWPp.congr_pre hpeq (SepWPp.pure_left fun hcrl_m => SepWPp.pure_left fun hφ_post =>
    hnext sm hpcm hrunm hspm hφ_post hcrl_m hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs)

/-- Companion of `call_lscro_calleeStack` for budget specs whose postcondition carries an outer
    `∃∗ evs : List AllocEvent, ⌜φ_post evs sf⌝ ∗ T_post evs sf ∗ stackAt s.sp n`. -/
theorem call_lscro_calleeStack_evs {α : Type} {prog : Program}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide)
    {P T_pre : SepProp} {T_post : List AllocEvent → State → SepProp}
    {Q : State → SepProp → Prop} {Fr F : SepProp}
    {Pan φ_pre : Prop} {φ_post : List AllocEvent → State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec_pre : spec.pre x s = (⌜φ_pre⌝ ∗ T_pre ∗ stackAt s.sp n)) (hφ : φ_pre)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ T_pre) ∗ F)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hpan : ∀ sf, spec.onPanic x s sf ⊢ ⌜Pan ∧ s.trace <+: sf.trace⌝ ∗ anyHeap)
    (hspec_post : ∀ sf,
      spec.post x s sf = (∃∗ evs : List AllocEvent, ⌜φ_post evs sf⌝ ∗ T_post evs sf ∗ stackAt s.sp n))
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      φ_post evs sf → LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp prog ret sf ((stackAt sp spqrSendCalleeStack ∗ T_post evs sf) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
          (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  have hcall' := lift_subroutine_ok_lscro_post hcall
  have hsp_al : s.spAligned = true := by unfold State.spAligned; rw [hsp]; exact hsp_align
  refine SepWPp.call_wpp (x := x)
    (F := memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F)
    hcall' hpc hrun hsp_al hlr
    (fun R' hm => by
      change s.mem ⊨ (spec.pre x s ∗ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗
        ((memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F) ∗ R')
      rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
      rw [hspec_pre, hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hφ, ?_⟩
      rw [hP, stackAt_spqrSendCallee_split sp n hle] at hm
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)
    (fun sm code R' _ hpost => by
      dsimp only [withLsCodeRoLoaded] at hpost; rw [hexit_eq code sm] at hpost
      exact allowPanic_not_exited hpost)
    (fun sm _ _ hmFr => by
      dsimp only [withLsCodeRoLoaded] at hmFr
      have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left (hpan sm))) hmFr
      rw [htr] at hm1
      have hassoc :
          ((⌜Pan ∧ s0.trace <+: sm.trace⌝ ∗ anyHeap) ∗
            (memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F)) =
          (⌜Pan ∧ s0.trace <+: sm.trace⌝ ∗
            (anyHeap ∗
              (memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F))) := by
        sep_ac_rfl
      rw [hassoc] at hm1
      exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (entails_anyHeap _))) hm1)
    (fun sm hpcm hrunm hspm hcsm => ?_)
    (fun sm R' _ hpost => by
      dsimp only [withLsCodeRoLoaded] at hpost; rw [hoom_eq sm] at hpost
      exact (allowPanic_not_exited hpost).elim)
  rw [hsp] at hspm
  rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, _, hvregs⟩
  dsimp only
  have hcrl_eq :
      (⌜LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗ spec.post x s sm) ∗
        (memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F) =
      ⌜LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗
        (spec.post x s sm ∗
          (memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F)) :=
    sepConj_assoc _ _ _
  refine SepWPp.congr_pre hcrl_eq (SepWPp.pure_left fun hcrl_m => ?_)
  have hex_eq :
      spec.post x s sm ∗
        (memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F) =
      (∃∗ evs : List AllocEvent,
        (⌜φ_post evs sm⌝ ∗ T_post evs sm ∗ stackAt s.sp n) ∗
          (memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F)) := by
    rw [hspec_post sm, sepExists_sepConj_left]
  refine SepWPp.congr_pre hex_eq (sepWPp_exists_left fun evs => ?_)
  have hpeq :
      (⌜φ_post evs sm⌝ ∗ T_post evs sm ∗ stackAt s.sp n) ∗
        (memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F) =
      ⌜φ_post evs sm⌝ ∗ ((stackAt sp spqrSendCalleeStack ∗ T_post evs sm) ∗ F) := by
    rw [hsp, stackAt_spqrSendCallee_split sp n hle]; sep_ac_rfl
  exact SepWPp.congr_pre hpeq (SepWPp.pure_left fun hφ_post =>
    hnext sm evs hpcm hrunm hspm hφ_post hcrl_m
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs)

/-- Non-panicking `SepWP` companion of `call_lscro_calleeStack` for budget callees with
    `spec.onPanic x s sf ⊢ ⌜False⌝`. -/
theorem call_lscro_calleeStack_sepWP {α : Type} {prog : Program}
    {entry ret_pc tgt : BitVec 64} {spec : Spec α} {x : α} {s : State}
    (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide)
    {P T_pre : SepProp} {T_post : State → SepProp} {Q : State → SepProp → Prop} {F : SepProp}
    {φ_pre : Prop} {φ_post : State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec_pre : spec.pre x s = (⌜φ_pre⌝ ∗ T_pre ∗ stackAt s.sp n)) (hφ : φ_pre)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ T_pre) ∗ F)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hpan_false : ∀ sf, spec.onPanic x s sf ⊢ ⌜False⌝)
    (hspec_post : ∀ sf, spec.post x s sf = (⌜φ_post sf⌝ ∗ T_post sf ∗ stackAt s.sp n))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      φ_post sf → LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP prog tgt sf ((stackAt sp spqrSendCalleeStack ∗ T_post sf) ∗ F) Q)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWP prog tgt s P Q := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  have hwpp : SepWPp prog tgt s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜False ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) :=
    call_lscro_calleeStack (s0 := s) (Fr := R) (Pan := False) sp n hle
      hcall hcrl hpc hrun hsp hsp_align rfl hlr hspec_pre hφ hP hexit_eq
      (fun sf => Entails.trans (hpan_false sf) (Entails.trans (Entails.of_eq (sepConj_emp ⌜False⌝).symm) (Entails.pure_left False.elim)))
      hspec_post
      (fun sf hpcm hrunm hspm hφm hcrlm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs => by
        intro R' hm' hL'
        rcases (SepWP.to_reaches_pc (hnext sf hpcm hrunm hspm hφm hcrlm
          hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs) hm' hL') with
          ⟨sf', hst, ⟨hpc', hrun', P_f, hmf', hq'⟩ | hoom'⟩
        · exact ⟨sf', hst, Or.inl ⟨hpc', hrun', P_f, hmf', hq'⟩⟩
        · exact ⟨sf', hst, Or.inr (Or.inr hoom')⟩)
      hoom_eq
  obtain ⟨sf, hsteps, hout⟩ := hwpp R hm hL
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, hq⟩ | ⟨_, P_f, hmf, hqp⟩ | hoom
  · exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, hq⟩⟩
  · have hfalse := hqp hmf
    rw [sepConj_assoc, satisfies_pure_sepConj] at hfalse
    exact hfalse.1.1.elim
  · exact ⟨sf, hsteps, Or.inr hoom⟩

/-- Non-panicking `SepWP` companion of `call_lscro_calleeStack_evs` for budget callees with
    `spec.onPanic x s sf ⊢ ⌜False⌝` and outer `∃∗ evs : List AllocEvent` postcondition. -/
theorem call_lscro_calleeStack_evs_sepWP {α : Type} {prog : Program}
    {entry ret_pc tgt : BitVec 64} {spec : Spec α} {x : α} {s : State}
    (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide)
    {P T_pre : SepProp} {T_post : List AllocEvent → State → SepProp}
    {Q : State → SepProp → Prop} {F : SepProp}
    {φ_pre : Prop} {φ_post : List AllocEvent → State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec_pre : spec.pre x s = (⌜φ_pre⌝ ∗ T_pre ∗ stackAt s.sp n)) (hφ : φ_pre)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ T_pre) ∗ F)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hpan_false : ∀ sf, spec.onPanic x s sf ⊢ ⌜False⌝)
    (hspec_post : ∀ sf,
      spec.post x s sf = (∃∗ evs : List AllocEvent, ⌜φ_post evs sf⌝ ∗ T_post evs sf ∗ stackAt s.sp n))
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      φ_post evs sf → LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP prog tgt sf ((stackAt sp spqrSendCalleeStack ∗ T_post evs sf) ∗ F) Q)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWP prog tgt s P Q := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  have hwpp : SepWPp prog tgt s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜False ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) :=
    call_lscro_calleeStack_evs (s0 := s) (Fr := R) (Pan := False) sp n hle
      hcall hcrl hpc hrun hsp hsp_align rfl hlr hspec_pre hφ hP hexit_eq
      (fun sf => Entails.trans (hpan_false sf) (Entails.trans (Entails.of_eq (sepConj_emp ⌜False⌝).symm) (Entails.pure_left False.elim)))
      hspec_post
      (fun sf evs hpcm hrunm hspm hφm hcrlm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs => by
        intro R' hm' hL'
        rcases (SepWP.to_reaches_pc (hnext sf evs hpcm hrunm hspm hφm hcrlm
          hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs) hm' hL') with
          ⟨sf', hst, ⟨hpc', hrun', P_f, hmf', hq'⟩ | hoom'⟩
        · exact ⟨sf', hst, Or.inl ⟨hpc', hrun', P_f, hmf', hq'⟩⟩
        · exact ⟨sf', hst, Or.inr (Or.inr hoom')⟩)
      hoom_eq
  obtain ⟨sf, hsteps, hout⟩ := hwpp R hm hL
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, hq⟩ | ⟨_, P_f, hmf, hqp⟩ | hoom
  · exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, hq⟩⟩
  · have hfalse := hqp hmf
    rw [sepConj_assoc, satisfies_pure_sepConj] at hfalse
    exact hfalse.1.1.elim
  · exact ⟨sf, hsteps, Or.inr hoom⟩

/-- Budget-threaded post-entailment at the post-`States::send` join point (`spqrSendPlacedEntry + 3068#64`). -/
theorem leaf_arm_post_entails_placed {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (sp w0 x21 x27 : BitVec 64) (x24_8 : BitVec 8) (sz : Nat)
    (P F_out : SepProp) (chunk : Chunk)
    (pay : MessagePayload spqrPolyApi) (nextSt : States spqrPolyApi (spqrAuthApi F))
    (Frame : SepProp) (hsz : sz ≤ 920 := by decide) (hx21 : x21 = noneCap)
    (hpay : chunkAt (sp + 0x550#64) chunk ∗ memRegion (sp + 0x572#64) 4 ⊢ spqrSendPayloadSlotAt sp x24_8 pay)
    (htail : F_out ∗ memRegion ((sp + 0x590#64) + BitVec.ofNat 64 sz) (920 - sz) =
      chunkedStatesTail920At A.repAlloc (sp + 0x590#64) nextSt)
    (hP_eq : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        (((sp + 0x950#64) ↦₆₄ w0) ∗ memRegion (sp + 0x958#64) sz ∗
          memRegion ((sp + 0x958#64) + BitVec.ofNat 64 sz) (920 - sz)) ∗
        (memRegion (sp + 0x1260#64) sz ∗ chunkAt ((sp + 0x1260#64) + BitVec.ofNat 64 sz) chunk) ∗
        (chunkAt (sp + 0x550#64) chunk ∗ memRegion (sp + 0x572#64) 4) ∗ memRegion (sp + 0x580#64) 16 ∗
        (F_out ∗ memRegion ((sp + 0x590#64) + BitVec.ofNat 64 sz) (920 - sz))) ∗ Frame) :
    P ⊢ (stackAt sp spqrSendCalleeStack ∗ A.pool lim st s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
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

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves1PlacedBudget
