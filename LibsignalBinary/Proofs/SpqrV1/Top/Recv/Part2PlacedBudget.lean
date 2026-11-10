/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.States2Budget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Proof
import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Varint
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable Prologue & Drop Tail for `spqr::recv`

Shared `FreeOnlyEvs` drop/dealloc contract bundle (`SpqrRecvDropContractsBudget`), prologue and
`msg_preamble` entry (`+0..+312`), and inlined `PqRatchetState` drop tail (`+952..+1036`) for
`spqr::recv` (Block `329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement lsmpl lsρ sepWP_seq_lscl withLsCodeLoaded withMemEq)
open CryptoVerification.LibsignalSpqrV1
  (MsgPreamble PqRatchetState SpqrRecvModel decodeVarint decodeVarintLoop msgPreamble
   recvResultExactKeyAt)
open CryptoVerification.LibsignalTripleRatchet (VecArg spqrRecvStack)
open CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty
  (csel_rest1_min_10 msg_cons_cons_of_len_ge_two msg_expose_byte msg_expose_hdr
   msg_nil_of_len_zero msg_singleton_of_len_one msg_unexpose_byte msg_unexpose_hdr)
open CryptoVerification.RustHeap (allocHookStack arrayAt)
open CryptoVerification.SpqrV1.Drop
  (cap_add_one_beq_zero_false cap_lsl7_sub_lsl4 chainPBAt_entails_dealloc
   chainPBHeaders_entails_memRegion_80 dropStack32 dropStack96 none3Cap'
   optChainPBAt_none_entails_memRegion_80 optProtoInnerStateSize optProtoPqRatchetInnerAt
   optProtoPqRatchetInnerAt_none_entails_memRegion_224 vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Prost.MessageMerge (v1StateJumpTablesPlacedAt)
open CryptoVerification.SpqrV1.ProtoRepr (chainEpochPBAt chainEpochPBSize optChainPBAt)
open CryptoVerification.SpqrV1.Top.DecodeState (TraceVRegs decodeStateSavedAt)
open CryptoVerification.SpqrV1.Top.Recv
  (InnerWordInv MsgRemValid msgPreamble_cons_cons msgPreamble_singleton
   ownFrame_join_352_4544 prologue_frame_split prologue_frame_unsplit sp_sub_4192_aligned
   sp_sub_4992_aligned sp_sub_96_aligned spqrRecvCalleeStackX spqrRecvPlacedEntry
   spqrRecvPlacedProg spqrRecvRoPlacedAt spqrRecvSavedRegs spqrRecvSavedRegs_eq_decodeStateSavedAt
   stackAt_spqrRecvCallee_split stackAt_spqrRecv_eq_callee_and_frame
   subroutine_ok_withMemEq_of_lscl)
open CryptoVerification.SpqrV1.Top.Recv.Placed (blkPC_329 blkPl_329)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget (dropSpqrChainSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget
  (dropOptProtoSpqrChainSpec dropProtoEpochSliceSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
  (dropOptProtoInnerStatePlacedSpec dropProtoPqRatchetStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.States2Budget (dropChunkedStatesLocal2PlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
  (PreamblePlacedErrTail PreamblePlacedOkTail SpqrRecvEnv spqrRecvPlacedPost0
   spqrRecvPlacedPost0OfEnv spqrRecvPlacedPreambleFrame step_epilogue_placed_ofEnv
   step_epoch_loop_placed)

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg

/-! ## 1. Shared Budget Drop Contracts & Sequencing Helpers for Block `329` -/

/-- `SpqrRecvEnv` is closed under appending `FreeOnlyEvs` deallocation tails. -/
theorem SpqrRecvEnv.append_freeOnly {st msg : VecArg} {evs0 evs_d : List AllocEvent}
    (h0 : SpqrRecvEnv st msg evs0) (hd : FreeOnlyEvs evs_d) :
    SpqrRecvEnv st msg (evs0 ++ evs_d) :=
  SpqrBoundedEvs.mono (by omega) (by omega)
    (SpqrBoundedEvs.append h0 (SpqrBoundedEvs.of_freeOnly hd))

/-- Simplified `__rust_dealloc` budget contract retaining `AllocCallPreserved` and deterministic
    `rustDeallocEvents size align` cost update. -/
def deallocFreeOnlySpec (MC : AllocCostModel) (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × MC.σ) where
  pre := (rustCliDeallocBudgetSpec MC A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (MC.stepEvents (rustDeallocEvents size align) st) sf ∗
      stackAt s0.sp allocHookStack

theorem subroutine_ok_deallocFreeOnly {MC : AllocCostModel} {A : RustCliAllocBudget MC}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec MC A lim)) :
    subroutine_ok prog entry (deallocFreeOnlySpec MC A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustCliDeallocBudgetSpec, deallocFreeOnlySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.1⟩, hq.2⟩

/-- Relocatable bundle of budget-threaded drop/dealloc `subroutine_ok` contracts for Block `329`
    (`spqr::recv`). -/
structure SpqrRecvDropContractsBudget {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (F : ShaCompress) (ext : String → Option (State → State)) : Prop where
  dealloc_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec MC A lim)
  dropEpochSlice_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 288)
      (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec MC A lim))
  dropOptProtoInnerState_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 267)
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec MC A lim))
  dropOptProtoChain_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 266)
      (withLsCodeLoaded lsmpl (dropOptProtoSpqrChainSpec MC A lim))
  dropChain_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 269)
      (withLsCodeLoaded lsmpl (dropSpqrChainSpec MC A lim))
  dropPqRatchetState_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 270)
      (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec MC A lim))
  dropStates_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 273)
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedSpec MC A lim F))

/-- Extract the underlying `List AllocEvent` witness from a `FreeOnlyEvs` proof without naming
    hygienic existential binders. -/
abbrev freeOnlyWitness {evs : List AllocEvent} (_ : FreeOnlyEvs evs) : List AllocEvent := evs

theorem seq_vm_clean {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

theorem seq_vm_lscl {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _ hp hr ⟨hvm, hPm, hQ⟩ hcl' =>
    SepWP.weaken_pre hPm (h2 sm hp hr hcl' hvm hQ))

theorem seq_free {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm))
    (h2 : ∀ (evs : List AllocEvent) (sm : State),
      FreeOnlyEvs evs → sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_evs evs sm) post) :
    SepWP prog target s P post :=
  SepWP.seq h1 fun sm _ hp hr ⟨evs, hevs, hPm, hQ⟩ =>
    SepWP.weaken_pre hPm (h2 evs sm hevs hp hr hQ)

theorem seq_free_lscl {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm))
    (h2 : ∀ (evs : List AllocEvent) (sm : State),
      FreeOnlyEvs evs → sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm →
      SepWP prog target sm (P_evs evs sm) post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _ hp hr ⟨evs, hevs, hPm, hQ⟩ hcl' =>
    SepWP.weaken_pre hPm (h2 evs sm hevs hp hr hcl' hQ))

theorem close_free_step {prog : Program} {mid : BitVec 64} {s : State}
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (evs : List AllocEvent) (hevs : FreeOnlyEvs evs)
    (hpc : s.pc = mid) (hrun : s.status = .Running)
    (hent : P ⊢ P_evs evs s) (hQ : Q s) :
    SepWP prog mid s P (fun sm Pm =>
      ∃ evs', FreeOnlyEvs evs' ∧ (Pm ⊢ P_evs evs' sm) ∧ Q sm) :=
  ProofLib.SepWP.done hpc hrun ⟨evs, hevs, hent, hQ⟩

/-! ## 2. Empty-Message Preamble Path (`+292 .. +308 -> +312`) -/

/-- Relocatable budget-threaded steps `+292 .. +308` when `msg.bytes = []`, setting `pre = {
    version := 0#8, epoch := 0#64, index := 0#32, remaining := [] }` and `remPtr = 1#64`, and
    continuing via `hok_tail` at `+312`. -/
theorem step_ok_empty_placed {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret target_pc : BitVec 64)
    (s0 s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hok_tail : PreamblePlacedOkTail A lim st_cost ext st msg ret target_pc s0 post)
    (hmsg_nil : msg.bytes = [])
    (hpc : s.pc = spqrRecvPlacedEntry + 292#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = st.v)
    (hx19 : s.readReg64 .x19 = ret)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = spqrRecvPlacedPreambleFrame A lim st_cost st msg ret s0 s) :
    SepWP (spqrRecvPlacedProg ext) target_pc s P post := by
  have hok : msgPreamble msg.bytes =
      .ok { version := 0#8, epoch := 0#64, index := 0#32, remaining := [] } := by
    rw [hmsg_nil]; rfl
  have hvalid : MsgRemValid msg 1#64 [] := Or.inl ⟨rfl, hmsg_nil⟩
  dsimp only [PreamblePlacedOkTail, spqrRecvPlacedProg, spqrRecvPlacedEntry,
    BitVec.ofNat_eq_ofNat] at hpc hok_tail ⊢
  wp_steps 5
  exact hok_tail
    { version := 0#8, epoch := 0#64, index := 0#32, remaining := [] }
    1#64 _ P hok hvalid
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
    (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [hx29, arm64_norm])
    (by rw [hP]; simp only [spqrRecvPlacedPreambleFrame, arm64_norm])

/-! ## 3. Prologue + `msg_preamble` Entry (`+0 .. +312`) -/

private def HideProp (P : Prop) : Prop := P

set_option maxHeartbeats 1600000 in
/-- Relocatable budget-threaded steps from function entry `+0` through the prologue and
    `msg_preamble` (`+0 .. +312`), branching to `herr_tail` at `+276` when `msgPreamble
    msg.bytes = .error .msgDecode` and to `hok_tail` at `+312` when `msgPreamble msg.bytes = .ok
    pre`. -/
theorem step_prologue_preamble_placed {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret target_pc : BitVec 64)
    (s0 : State) (P : SepProp) (post : State → SepProp → Prop)
    (herr_tail : PreamblePlacedErrTail A lim st_cost ext st msg ret target_pc s0 post)
    (hok_tail : PreamblePlacedOkTail A lim st_cost ext st msg ret target_pc s0 post)
    (hpc : s0.pc = spqrRecvPlacedEntry)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = st.v)
    (hx1 : s0.readReg64 .x1 = msg.v)
    (hx8 : s0.readReg64 .x8 = ret)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim st_cost s0 ∗
      stackAt s0.sp spqrRecvStack) :
    SepWP (spqrRecvPlacedProg ext) target_pc s0 P post := by
  have hok_empty := step_ok_empty_placed A lim st_cost ext st msg ret target_pc s0
  have hep_loop := step_epoch_loop_placed A lim st_cost ext st msg ret target_pc
  have hsp96A : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true := sp_sub_96_aligned s0 hsp_align
  have hsp4192A : ((s0.sp - 4192#64) &&& 15#64 == 0#64) = true := sp_sub_4192_aligned s0 hsp_align
  have hsp4992A : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true := sp_sub_4992_aligned s0 hsp_align
  have hunsplit :
      memRegion (s0.sp - 4992#64) 0x320 ∗
        ((s0.sp - 4192#64) ↦₆₄ 0#64) ∗
        memRegion (s0.sp - 4184#64) 0xff8 ⊢
      memRegion (s0.sp - 4992#64) 0x1320 := by
    simpa (disch := decide) only [bv_sub_add_lit, Nat.reduceSub, BitVec.ofNat_eq_ofNat] using
      prologue_frame_unsplit (s0.sp - 4992#64) 0#64
  obtain hmsg_nil | ⟨version, hmsg_one⟩ | ⟨version, b₀, rest0', hmsg_two⟩ :
      msg.bytes = [] ∨ (∃ v, msg.bytes = [v]) ∨ (∃ v b₀ r, msg.bytes = v :: b₀ :: r) := by
    cases msg.bytes with
    | nil => exact Or.inl rfl
    | cons v tl =>
      cases tl with
      | nil => exact Or.inr (Or.inl ⟨v, rfl⟩)
      | cons b₀ r => exact Or.inr (Or.inr ⟨v, b₀, r, rfl⟩)
  · subst hP
    have hhide : HideProp (msg.bytes = []) := hmsg_nil
    clear hmsg_nil
    dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
    refine seq_vm_clean (mid := (blkPl_329).base + 292#64)
      (P_mid := spqrRecvPlacedPreambleFrame A lim st_cost st msg ret s0 s0)
      (Q := fun sm => sm.sp = s0.sp - 4992#64 ∧ TraceVRegs sm s0 ∧
        sm.readReg64 .x0 = st.v ∧ sm.readReg64 .x19 = ret ∧ sm.readReg64 .x29 = s0.sp - 96#64)
      ?_ ?_
    · by_vm_steps (
        rw [stackAt_spqrRecv_eq_callee_and_frame s0.sp]
        refine SepWP.fold (prologue_frame_split (s0.sp - 4992#64)) (by sep_focus) ?_
        wp_pull_exists
        rename_i s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s30 s29 probe
        wp_simp_pre only [bv_sub_add_lit, Nat.reduceSub]
        refine SepWP.fold (msg_expose_hdr A.repAlloc msg) (by sep_focus) ?_
        refine SepWP.focus_pure (by sep_focus) fun hlen_lt => ?_
        generalize hsp0 : s0.sp = sp0 at hsp96A hsp4192A hsp4992A ⊢
        wp_steps
        subst hsp0
        refine SepWP.fold hunsplit (by sep_focus) ?_
        wp_if hlen0
        · refine SepWP.fold (msg_unexpose_hdr A.repAlloc msg) (by sep_focus) ?_
          refine ProofLib.SepWP.done (by simp [wp_norm, arm64_norm])
            (by simp [hrun, wp_norm, arm64_norm])
            ⟨by simp [wp_norm, arm64_norm],
             Entails.of_eq (by
               dsimp only [spqrRecvPlacedPreambleFrame]
               rw [spqrRecvSavedRegs_eq_decodeStateSavedAt s0.sp s0]
               unfold decodeStateSavedAt
               sep_ac_rfl),
             by simp [arm64_norm], by simp [arm64_norm], by simp [hx0, arm64_norm],
             by simp [hx8, arm64_norm], by simp [arm64_norm]⟩
        · wp_steps
          wp_if hlen1
          · obtain ⟨v, hv⟩ := msg_singleton_of_len_one hlen_lt hlen1
            have hmsg_nil : msg.bytes = [] := hhide
            simp [hmsg_nil] at hv
          · obtain ⟨v, b, r, hge2⟩ := msg_cons_cons_of_len_ge_two hlen_lt hlen0 hlen1
            have hmsg_nil : msg.bytes = [] := hhide
            simp [hmsg_nil] at hge2
      )
    · intro s1 hpc1 hrun1 hvm ⟨hsp1, htr1, hx0_1, hx19_1, hx29_1⟩
      have hmsg_nil : msg.bytes = [] := hhide
      exact hok_empty s1 _ post hok_tail hmsg_nil hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx29_1
        (by dsimp only [spqrRecvPlacedPreambleFrame]; rw [A.pool_transport lim st_cost s0 s1 hvm])
  · subst hP
    have hhide : HideProp (msg.bytes = [version]) := hmsg_one
    clear hmsg_one
    dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
    refine seq_vm_clean (mid := (blkPl_329).base + 276#64)
      (P_mid := spqrRecvPlacedPreambleFrame A lim st_cost st msg ret s0 s0)
      (Q := fun sm => sm.sp = s0.sp - 4992#64 ∧ TraceVRegs sm s0 ∧ sm.readReg64 .x19 = ret)
      ?_ ?_
    · by_vm_steps (
        rw [stackAt_spqrRecv_eq_callee_and_frame s0.sp]
        refine SepWP.fold (prologue_frame_split (s0.sp - 4992#64)) (by sep_focus) ?_
        wp_pull_exists
        rename_i s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s30 s29 probe
        wp_simp_pre only [bv_sub_add_lit, Nat.reduceSub]
        refine SepWP.fold (msg_expose_hdr A.repAlloc msg) (by sep_focus) ?_
        refine SepWP.focus_pure (by sep_focus) fun hlen_lt => ?_
        generalize hsp0 : s0.sp = sp0 at hsp96A hsp4192A hsp4992A ⊢
        wp_steps
        subst hsp0
        refine SepWP.fold hunsplit (by sep_focus) ?_
        wp_if hlen0
        · have hnil := msg_nil_of_len_zero hlen_lt hlen0
          have hmsg_one : msg.bytes = [version] := hhide
          simp [hmsg_one] at hnil
        · wp_steps
          wp_if hlen1
          · refine SepWP.fold (msg_unexpose_hdr A.repAlloc msg) (by sep_focus) ?_
            refine ProofLib.SepWP.done (by simp [wp_norm, arm64_norm])
              (by simp [hrun, wp_norm, arm64_norm])
              ⟨by simp [wp_norm, arm64_norm],
               Entails.of_eq (by
                 dsimp only [spqrRecvPlacedPreambleFrame]
                 rw [spqrRecvSavedRegs_eq_decodeStateSavedAt s0.sp s0]
                 unfold decodeStateSavedAt
                 sep_ac_rfl),
               by simp [arm64_norm], by simp [arm64_norm], by simp [hx8, arm64_norm]⟩
          · obtain ⟨v, b, r, hge2⟩ := msg_cons_cons_of_len_ge_two hlen_lt hlen0 hlen1
            have hmsg_one : msg.bytes = [version] := hhide
            simp [hmsg_one] at hge2
      )
    · intro s1 hpc1 hrun1 hvm ⟨hsp1, htr1, hx19_1⟩
      have hmsg_one : msg.bytes = [version] := hhide
      have herr : msgPreamble msg.bytes = .error .msgDecode := by
        rw [hmsg_one, msgPreamble_singleton]
      exact herr_tail s1 _ herr hpc1 hrun1 hsp1 htr1 hx19_1
        (by dsimp only [spqrRecvPlacedPreambleFrame]; rw [A.pool_transport lim st_cost s0 s1 hvm])
  · subst hP
    have hhide : HideProp (msg.bytes = version :: b₀ :: rest0') := hmsg_two
    clear hmsg_two
    dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
    refine seq_vm_clean (mid := (blkPl_329).base + 96#64)
      (P_mid := spqrRecvPlacedPreambleFrame A lim st_cost st msg ret s0 s0)
      (Q := fun sm =>
        msg.bytes.length < 2 ^ 63 ∧
        sm.sp = s0.sp - 4992#64 ∧
        TraceVRegs sm s0 ∧
        sm.readReg64 .x0 = st.v ∧
        sm.readReg64 .x19 = ret ∧
        sm.readReg64 .x25 = version.zeroExtend 64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x8 = msg.ptr + 1#64 ∧
        sm.readReg64 .x9 = BitVec.ofNat 64 msg.bytes.length ∧
        sm.readReg64 .x10 = BitVec.ofNat 64 (7 * 0) ∧
        sm.readReg64 .x11 = msg.ptr ∧
        sm.readReg64 .x12 = BitVec.ofNat 64 (min (b₀ :: rest0').length 10) ∧
        sm.readReg64 .x14 = BitVec.ofNat 64 (0 + 1) ∧
        sm.readReg64 .x22 = 0#64)
      ?_ ?_
    · by_vm_steps (
        rw [stackAt_spqrRecv_eq_callee_and_frame s0.sp]
        refine SepWP.fold (prologue_frame_split (s0.sp - 4992#64)) (by sep_focus) ?_
        wp_pull_exists
        rename_i s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s30 s29 probe
        wp_simp_pre only [bv_sub_add_lit, Nat.reduceSub]
        refine SepWP.fold (msg_expose_hdr A.repAlloc msg) (by sep_focus) ?_
        refine SepWP.focus_pure (by sep_focus) fun hlen_lt => ?_
        generalize hsp0 : s0.sp = sp0 at hsp96A hsp4192A hsp4992A ⊢
        wp_steps
        subst hsp0
        refine SepWP.fold hunsplit (by sep_focus) ?_
        wp_if hlen0
        · have hnil := msg_nil_of_len_zero hlen_lt hlen0
          have hmsg_two : msg.bytes = version :: b₀ :: rest0' := hhide
          simp [hmsg_two] at hnil
        · wp_steps
          wp_if hlen1
          · obtain ⟨v, hv⟩ := msg_singleton_of_len_one hlen_lt hlen1
            have hmsg_two : msg.bytes = version :: b₀ :: rest0' := hhide
            simp [hmsg_two] at hv
          · wp_steps
            refine SepWP.fold (msg_unexpose_hdr A.repAlloc msg) (by sep_focus) ?_
            have hmsg_eq : msg.bytes = version :: b₀ :: rest0' := hhide
            have hsplit0 : msg.bytes = ([] : List (BitVec 8)) ++ version :: (b₀ :: rest0') := hmsg_eq
            have hoff0 : msg.ptr = msg.ptr + BitVec.ofNat 64 ([] : List (BitVec 8)).length := by
              simp [List.length_nil]
            have hexp0 := msg_expose_byte A.repAlloc msg [] (b₀ :: rest0') version msg.ptr hsplit0 hoff0
            have hunexp0 := msg_unexpose_byte A.repAlloc msg [] (b₀ :: rest0') version msg.ptr hsplit0 hoff0
            clear hoff0 hsplit0
            have hmsg_symm := hmsg_eq.symm
            clear hmsg_eq
            refine SepWP.fold hexp0 (by sep_focus) ?_
            wp_steps 4
            refine SepWP.fold hunexp0 (by sep_focus) ?_
            have hlen_eq : msg.bytes.length = 1 + 0 + (b₀ :: rest0').length := by
              rw [← hmsg_symm, List.length_cons]
              omega
            refine ProofLib.SepWP.done (by simp [wp_norm, arm64_norm])
              (by simp [hrun, wp_norm, arm64_norm])
              ⟨by simp [wp_norm, arm64_norm],
               Entails.of_eq (by
                 dsimp only [spqrRecvPlacedPreambleFrame]
                 rw [spqrRecvSavedRegs_eq_decodeStateSavedAt s0.sp s0]
                 unfold decodeStateSavedAt
                 sep_ac_rfl),
               hlen_lt,
               by simp [arm64_norm], by simp [arm64_norm],
               by simp [hx0, arm64_norm], by simp [hx8, arm64_norm],
               by simp [arm64_norm], by simp [arm64_norm],
               by simp [arm64_norm], by simp [arm64_norm],
               by simp [arm64_norm], by simp [arm64_norm],
               by simp [arm64_norm]; exact csel_rest1_min_10 hlen_eq hlen_lt,
               by simp [arm64_norm], by simp [arm64_norm]⟩
      )
    · intro s1 hpc1 hrun1 hvm
        ⟨hlen_lt, hsp1, htr1, hx0_1, hx19_1, hx25_1, hx29_1,
         hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx14_1, hx22_1⟩
      have hmsg_two : msg.bytes = version :: b₀ :: rest0' := hhide
      have hpre0 : msgPreamble msg.bytes =
          match decodeVarintLoop 0 0#64 (b₀ :: rest0') with
          | none => .error .msgDecode
          | some (epoch, rest1) =>
            if epoch == 0#64 then .error .msgDecode
            else
              match decodeVarint rest1 with
              | .error e => .error e
              | .ok (index, rest2) =>
                if index.toNat < 2 ^ 32 then
                  .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest2 }
                else .error .msgDecode := by
        rw [hmsg_two]; exact msgPreamble_cons_cons version b₀ rest0'
      exact hep_loop version (b₀ :: rest0') s0 post herr_tail hok_tail hlen_lt
        10 0 0#64 [] rest0' b₀ s1 _
        (by omega) (by omega) hmsg_two rfl rfl hpre0
        hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx25_1 hx29_1
        hx8_1 hx9_1 hx10_1 hx11_1 hx12_1 hx14_1 hx22_1
        (by dsimp only [spqrRecvPlacedPreambleFrame]; rw [A.pool_transport lim st_cost s0 s1 hvm])

/-! ## 4. Relocatable Budget-Threaded `PqRatchetState` Drop Tail (`+952 .. +1036`) -/

/-- Envelope-parametric relocatable inlined `drop_glue::<PqRatchetState>` tail at `+952 ..
    +1036` followed by `step_epilogue_placed_ofEnv` (`+1040 .. +1072`). -/
theorem step_drop_pre_952_placed_ofEnv {MC : AllocCostModel} {F : ShaCompress}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w26 : BitVec 64)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0OfEnv A lim st_cost Env M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 952#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx26 : s.readReg64 .x26 = w26)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 48 ∗
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  rcases htr with ⟨htr, hvregs⟩
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hC.dealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry,
    LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
  let st0 := MC.stepEvents evs0 st_cost
  refine seq_free_lscl hcl (mid := (blkPl_329).base + 1020#64)
    (P_evs := fun evs_2 sm =>
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs_2 st0) sm ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 128 ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun sm => sm.sp = s0.sp - 4992#64 ∧ TraceVRegs sm s0 ∧ sm.readReg64 .x26 = w26)
    ?_ ?_
  · have hjoin128 : memRegion (s0.sp - 4992#64) 48 ∗ memRegion (s0.sp - 4944#64) 80 ⊢
        memRegion (s0.sp - 4992#64) 128 := by
      rw [ProofLib.memRegion_split' (b := s0.sp - 4992#64) (n := 48) (k := 80)
          (b' := s0.sp - 4944#64) rfl (by bv_omega) (by decide)]
      exact Entails.refl _
    cases hch : pre_pb.chain with
    | none =>
      dsimp only [optChainPBAt]
      wp_steps
      refine SepWP.focus_weaken (optChainPBAt_none_entails_memRegion_80 (s0.sp - 4944#64)) (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin128 (by sep_focus) ?_
      refine close_free_step [] FreeOnlyEvs.nil
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, *])
        (Entails.of_eq (by
          simp only [AllocCostModel.stepEvents_nil, wp_norm, arm64_norm]
          sep_ac_rfl))
        ?_
      refine ⟨?_, ⟨?_, ?_⟩, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]
    | some ch =>
      dsimp only [optChainPBAt]
      refine SepWP.focus_weaken (chainPBAt_entails_dealloc A.repAlloc (s0.sp - 4944#64) ch) (by sep_focus) ?_
      wp_pull_exists; rename_i g
      wp_focus_pure; rintro ⟨hlen_le, hcap_lt, hptr_ne⟩
      have hcap_lt_pow : g.links.cap.toNat < 2 ^ 63 := by omega
      have hlen_lt : ch.links.length * 112 < 2 ^ 63 := by
        have : ch.links.length * 112 ≤ g.links.cap.toNat * 112 := Nat.mul_le_mul_right 112 hlen_le
        omega
      have hne_none := cap_add_one_beq_zero_false hcap_lt_pow
      have h56 : (s0.sp - 4944#64) + 8#64 = s0.sp - 4936#64 := bv_sub_add_lit s0.sp 4944 8
      have h64 : (s0.sp - 4944#64) + 16#64 = s0.sp - 4928#64 := bv_sub_add_lit s0.sp 4944 16
      have h72 : (s0.sp - 4944#64) + 24#64 = s0.sp - 4920#64 := bv_sub_add_lit s0.sp 4944 24
      have h80 : (s0.sp - 4944#64) + 32#64 = s0.sp - 4912#64 := bv_sub_add_lit s0.sp 4944 32
      have h88 : (s0.sp - 4944#64) + 40#64 = s0.sp - 4904#64 := bv_sub_add_lit s0.sp 4944 40
      have hslice_mem := subroutine_ok_withMemEq_of_lscl hC.dropEpochSlice_ok hcl
      simp only [withMemEq, dropProtoEpochSliceSpec] at hslice_mem
      dsimp only [spqrRecvPlacedProg, chainEpochPBSize, BitVec.ofNat_eq_ofNat] at hslice_mem
      refine seq_free (mid := (blkPl_329).base + 1000#64)
        (P_evs := fun evs_2a sm =>
          spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗
          recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
          A.pool lim (MC.stepEvents evs_2a st0) sm ∗
          stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
          memRegion (s0.sp - 4992#64) 48 ∗
          ((s0.sp - 4944#64) ↦₆₄ g.links.cap) ∗ ((s0.sp - 4936#64) ↦₆₄ g.links.ptr) ∗
          ((s0.sp - 4928#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
          ((s0.sp - 4920#64) ↦₆₄ g.nextRoot.cap) ∗ ((s0.sp - 4912#64) ↦₆₄ g.nextRoot.ptr) ∗
          memRegion (s0.sp - 4904#64) 40 ∗
          vecCapPtrDealloc A.repAlloc g.nextRoot.cap g.nextRoot.ptr ∗
          optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
          memRegion (s0.sp - 4640#64) 4544 ∗
          spqrRecvSavedRegs (s0.sp - 4992#64) s0)
        (Q := fun sm => sm.sp = s0.sp - 4992#64 ∧ TraceVRegs sm s0 ∧ sm.readReg64 .x26 = w26)
        ?_ ?_
      · by_cases hc : g.links.cap = 0
        · have hnil : ch.links = [] := by
            rw [hc] at hlen_le; simp at hlen_le; exact hlen_le
          have hc_beq : (g.links.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
          have h0 : arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 g.links.ptr [] = emp := rfl
          simp only [hc, hnil, List.length_nil, Nat.zero_mul, BitVec.ofNat_eq_ofNat, ↓reduceIte,
            emp_sepConj, sepConj_emp]
          wp_steps
          rw [← sepConj_emp ((s0.sp - 4944#64) ↦₆₄ 0#64), ← h0]
          refine SepWP.focus_weaken
            (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack32 (by decide)))
            (by sep_focus) ?_
          wp_call hslice_mem (⟨g.links.ptr, []⟩, st0)
          have hevs_sl := ‹FreeOnlyEvs _›
          have hsp_eq : stackAt s.sp dropStack32 = stackAt (s0.sp - 4992#64) dropStack32 := by rw [hsp]
          refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
          refine SepWP.focus_weaken
            (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack32 (by decide)).symm)
            (by sep_focus) ?_
          wp_steps
          refine close_free_step (freeOnlyWitness hevs_sl) hevs_sl
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm, *])
            (Entails.of_eq (by
              simp only [freeOnlyWitness, memRegion_zero, emp_sepConj, sepConj_emp, wp_norm, arm64_norm, *]
              sep_ac_rfl))
            ?_
          refine ⟨?_, ⟨?_, ?_⟩, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]
        · have hc_beq : ¬((g.links.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
          have hlsl := cap_lsl7_sub_lsl4 hcap_lt
          have hsplit : g.links.cap.toNat * 112 =
              ch.links.length * 112 + (g.links.cap.toNat - ch.links.length) * 112 := by
            rw [← Nat.add_mul]; congr 1; omega
          have hbound : ch.links.length * 112 + (g.links.cap.toNat - ch.links.length) * 112 ≤ 2 ^ 64 := by
            rw [← hsplit]; omega
          have hrejoin :
              memRegion g.links.ptr (ch.links.length * 112) ∗
                memRegion (g.links.ptr + BitVec.ofNat 64 (ch.links.length * 112))
                  ((g.links.cap.toNat - ch.links.length) * 112) ⊢
              memRegion g.links.ptr (g.links.cap.toNat * 112) := by
            rw [hsplit, ProofLib.memRegion_split g.links.ptr (ch.links.length * 112)
                  ((g.links.cap.toNat - ch.links.length) * 112) hbound]
            exact Entails.refl _
          simp only [hc, ↓reduceIte, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          wp_steps
          refine SepWP.focus_weaken
            (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack32 (by decide)))
            (by sep_focus) ?_
          wp_call hslice_mem (⟨g.links.ptr, ch.links⟩, st0)
          have hevs_sl := ‹FreeOnlyEvs _›
          have hsp_eq : stackAt s.sp dropStack32 = stackAt (s0.sp - 4992#64) dropStack32 := by rw [hsp]
          refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
          refine SepWP.focus_weaken
            (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack32 (by decide)).symm)
            (by sep_focus) ?_
          refine SepWP.focus_weaken hrejoin (by sep_focus) ?_
          refine SepWP.focus_weaken
            (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide)))
            (by sep_focus) ?_
          wp_steps
          wp_call hdealloc_fo
            (g.links.ptr, g.links.cap.toNat * 112, 8, MC.stepEvents (freeOnlyWitness hevs_sl) st0)
          conv in (stackAt _ allocHookStack) =>
            arg 1
            simp only [hsp, *]
          refine SepWP.focus_weaken
            (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide)).symm)
            (by sep_focus) ?_
          refine close_free_step
            (freeOnlyWitness hevs_sl ++ rustDeallocEvents (g.links.cap.toNat * 112) 8)
            (hevs_sl.append (FreeOnlyEvs.singleton 8 (g.links.cap.toNat * 112)))
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (Entails.of_eq (by
              rw [MC.stepEvents_append]
              simp only [freeOnlyWitness, wp_norm, arm64_norm, *]
              sep_ac_rfl))
            ?_
          refine ⟨?_, ⟨?_, ?_⟩, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]
      · intro evs_2a s2 hevs_2a hpc2 hrun2 ⟨hsp2, ⟨htr2, hvregs2⟩, hx26_2⟩
        have hhdr80 : ((s0.sp - 4944#64) ↦₆₄ g.links.cap) ∗ ((s0.sp - 4936#64) ↦₆₄ g.links.ptr) ∗
            ((s0.sp - 4928#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
            ((s0.sp - 4920#64) ↦₆₄ g.nextRoot.cap) ∗ ((s0.sp - 4912#64) ↦₆₄ g.nextRoot.ptr) ∗
            memRegion (s0.sp - 4904#64) 40 ⊢ memRegion (s0.sp - 4944#64) 80 := by
          rw [← h56, ← h64, ← h72, ← h80, ← h88]
          exact chainPBHeaders_entails_memRegion_80 (s0.sp - 4944#64) g.links.cap g.links.ptr
            (BitVec.ofNat 64 ch.links.length) g.nextRoot.cap g.nextRoot.ptr
        dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hnr : (g.nextRoot.cap == 0#64) = true <;>
          simp only [hnr, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
        · wp_steps
          refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin128 (by sep_focus) ?_
          refine close_free_step evs_2a hevs_2a
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm, *])
            (Entails.of_eq (by
              simp only [wp_norm, arm64_norm, *]
              sep_ac_rfl))
            ?_
          refine ⟨?_, ⟨?_, ?_⟩, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]
        · refine SepWP.focus_weaken
            (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide)))
            (by sep_focus) ?_
          wp_steps
          wp_call hdealloc_fo
            (g.nextRoot.ptr, g.nextRoot.cap.toNat, 1, MC.stepEvents evs_2a st0)
          have hsp_eq2 : stackAt s2.sp allocHookStack = stackAt (s0.sp - 4992#64) allocHookStack := by rw [hsp2]
          refine SepWP.focus_weaken (Entails.of_eq hsp_eq2) (by sep_focus) ?_
          refine SepWP.focus_weaken
            (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide)).symm)
            (by sep_focus) ?_
          refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin128 (by sep_focus) ?_
          refine close_free_step
            (evs_2a ++ rustDeallocEvents g.nextRoot.cap.toNat 1)
            (hevs_2a.append (FreeOnlyEvs.singleton 1 g.nextRoot.cap.toNat))
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (Entails.of_eq (by
              rw [MC.stepEvents_append]
              sep_ac_rfl))
            ?_
          refine ⟨?_, ⟨?_, ?_⟩, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]
  · intro evs_2 s3 hevs_2 hpc3 hrun3 hcl3 ⟨hsp3, ⟨htr3, hvregs3⟩, hx26_3⟩
    have hjoin352 : memRegion (s0.sp - 4992#64) 128 ∗ memRegion (s0.sp - 4864#64) 224 ⊢
        memRegion (s0.sp - 4992#64) 352 := by
      rw [ProofLib.memRegion_split' (b := s0.sp - 4992#64) (n := 128) (k := 224)
          (b' := s0.sp - 4864#64) rfl (by bv_omega) (by decide)]
      exact Entails.refl _
    refine seq_free (mid := (blkPl_329).base + 1040#64)
      (P_evs := fun evs_tot sm =>
        spqrRecvRoPlacedAt ∗
        st.at A.repAlloc ∗
        msg.at A.repAlloc ∗
        recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
        A.pool lim (MC.stepEvents evs_tot st0) sm ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
        memRegion (s0.sp - 4992#64) 0x1320 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0)
      (Q := fun sm => sm.sp = s0.sp - 4992#64 ∧ TraceVRegs sm s0)
      ?_ ?_
    · cases hinner : pre_pb.inner with
      | none =>
        rw [hinner] at hw26
        dsimp only [InnerWordInv] at hw26
        subst hw26
        have hnone3 : (none3Cap' + 3#64 == 0#64) = true := rfl
        dsimp only [optProtoPqRatchetInnerAt]
        wp_steps
        refine SepWP.focus_weaken (optProtoPqRatchetInnerAt_none_entails_memRegion_224 (s0.sp - 4864#64)) (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin352 (by sep_focus) ?_
        refine SepWP.focus_weaken (ownFrame_join_352_4544 s0.sp) (by sep_focus) ?_
        refine close_free_step evs_2 hevs_2
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, *])
          (Entails.of_eq (by
            simp only [wp_norm, arm64_norm, *]
            sep_ac_rfl))
          ?_
        refine ⟨?_, ⟨?_, ?_⟩⟩ <;> simp only [wp_norm, arm64_norm, *]
      | some innerVal =>
        cases innerVal with
        | v1 v1 =>
          rw [hinner] at hw26
          dsimp only [InnerWordInv] at hw26
          dsimp only [optProtoPqRatchetInnerAt]
          have hinner_mem := subroutine_ok_withMemEq_of_lscl hC.dropOptProtoInnerState_ok hcl3
          simp only [withMemEq, dropOptProtoInnerStatePlacedSpec] at hinner_mem
          dsimp only [spqrRecvPlacedProg, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hinner_mem
          unfold spqrRecvRoPlacedAt v1StateJumpTablesPlacedAt
          wp_steps
          refine SepWP.focus_weaken
            (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack96 (by decide)))
            (by sep_focus) ?_
          wp_call hinner_mem (⟨s0.sp - 4864#64, v1.innerState⟩, MC.stepEvents evs_2 st0)
          have hevs_in := ‹FreeOnlyEvs _›
          have hsp_eq3 : stackAt s3.sp dropStack96 = stackAt (s0.sp - 4992#64) dropStack96 := by rw [hsp3]
          refine SepWP.focus_weaken (Entails.of_eq hsp_eq3) (by sep_focus) ?_
          refine SepWP.focus_weaken
            (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack96 (by decide)).symm)
            (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin352 (by sep_focus) ?_
          refine SepWP.focus_weaken (ownFrame_join_352_4544 s0.sp) (by sep_focus) ?_
          refine close_free_step
            (evs_2 ++ freeOnlyWitness hevs_in)
            (hevs_2.append hevs_in)
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (Entails.of_eq (by
              rw [MC.stepEvents_append]
              sep_ac_rfl))
            ?_
          refine ⟨?_, ⟨?_, ?_⟩⟩ <;> simp only [wp_norm, arm64_norm, *]
    · intro evs_tot s4 hevs_tot hpc4 hrun4 ⟨hsp4, htr4⟩
      have heq_pool : MC.stepEvents evs_tot st0 = MC.stepEvents (evs0 ++ evs_tot) st_cost := by
        dsimp only [st0]
        exact (MC.stepEvents_append evs0 evs_tot st_cost).symm
      rw [heq_pool]
      exact step_epilogue_placed_ofEnv A lim st_cost Env (evs0 ++ evs_tot)
        (hevs_free evs_tot hevs_tot) M ext st msg ret s0 s4 _ R post hpost
        hpc4 hrun4 hsp4 hs0_align htr4 rfl

theorem step_drop_pre_952_placed {MC : AllocCostModel} {F : ShaCompress}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (pre_pb : PqRatchetState) (w26 : BitVec 64)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A lim st_cost M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 952#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx26 : s.readReg64 .x26 = w26)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 48 ∗
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post :=
  step_drop_pre_952_placed_ofEnv A lim st_cost (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    M ext hC st msg ret pre_pb w26 hw26 s0 s P R post hpost hs0_align
    hpc hrun hsp htr hx26 hP hcl

end LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
