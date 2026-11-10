/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 0 (`KeysUnsampled`, `+156`)

Total-correctness relocatable Block-`333` theorems and `subroutine_ok` contracts for
`InnerState.keysUnsampled` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped CryptoVerification.RustHeap
open CryptoVerification (LibsignalPlacement blkLib_333 blkLib_eq_333 blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (ProtoAuthenticator spqrAuthApi spqrPolyApi)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Drop (cap_add_one_beq_zero_false chunkedKeysUnsampledAt chunkedStatesAt chunkedStatesSize optProtoAuthenticatorAt optProtoInnerStateAt optProtoInnerStateSize optProtoUnchunkedKeysUnsampledAt protoChunkedKeysUnsampledAt protoInnerStateAt protoUnchunkedKeysUnsampledAt unchunkedKeysUnsampledAt vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.ProtoRepr (AuthenticatorPBGhost authenticatorPBAt_eq_exists_pinned authenticatorPBPinnedAt)
open CryptoVerification.SpqrV1.States.FromPb (TraceCalleeSaved authenticatorAt_8_pack authenticatorPBPinnedAt_8_eq_cap_tail memRegion_152_8_48_entails_208 memRegion_2304_split_152_208 ofNat_beq_zero_false optProtoInnerStateAt_keysUnsampled_some_eq resultChunkedStatesAt sp_sub_2400_align stackAt_encoderFromPb_split_allocHook statesFromPbJumpTablePlacedAt statesFromPbSavedCells statesFromPbStack states_from_pb_keysUnsampled_some_eq vecU8Payload_extract_len_lt63 vecU8Payload_of_nil vecU8Payload_pos vecU8Payload_pos_dealloc vecU8Payload_pos_unpack)
open CryptoVerification.SpqrV1.Unchunked (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload vecU8Payload_entails_dealloc)

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   RustCliAllocBudget RustLayoutOk VmPreserved
   fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec
   rustCliDeallocBudgetSpec rustDeallocEvents subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (allocMemcpyVmSpec rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
  (AuthFromPbEnv authFromPbEvents authKeyCloneEvents fitsEvents_of_fitsEnv_authFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget StatesFromPbEnv sepWPp_of_states_exit_placed
   spqrRustDeallocSym statesFromPbVariantPlacedSpec statesFromPbVariantPlacedSpecOfEnv
   states_from_pb_prologue_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
  (states_from_pb_dispatch_tagged_placed_budget states_from_pb_epilogue_8176_keysUnsampled_placed
   states_from_pb_keysUnsampled_auth_none_placed
   states_from_pb_keysUnsampled_step0_156_200_placed_budget
   states_from_pb_keysUnsampled_uc_none_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (KeysUnsampledFromPbAllocEnv KeysUnsampledFromPbEnv StatesFromPbVariantStepPlaced
   align_pre_st deallocFreeOnlySpec fitsEnv_alloc_of_keysUnsampledEnv
   fitsEnv_alloc_of_statesFromPbEnv keysUnsampledFromPbEnv_sub_statesFromPbEnv
   sepWP_evs_dealloc sepWP_evs_nil seq_clean_evs seq_clean_st
   sfpProof_tagged_ok_of_step_placed sfpProof_tagged_ok_of_step_placed_raw
   subroutine_ok_deallocFreeOnly)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

private theorem blk333_noSvc0 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_333.text = true := by
  decide +kernel

local macro "wp_steps_sync_333 " mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm
    (Q := (blkPC_333).rebase (blkPl_333).base (hooksException _))
    blkLib_eq_333 blk333_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

private theorem entails_pre_st {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (hent : ∀ sc : State, sc = s → P ⊢ P_mid sc)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) :=
  SepWP.weaken_pre (hent s rfl) h

/-! ## Budget-Threaded `KeysUnsampled` Clone & Dealloc Steps (`+200 -> +5476 -> +5600 -> ret`) -/

/-- Segment (`+200 -> +5476`): clone `auth.rootKey` under
    `FitsEvents M lim st (authKeyCloneEvents auth.rootKey)` with zero OOM/panic branches. -/
theorem states_from_pb_keysUnsampled_step1_200_5476_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out w208 : BitVec 64)
    (ga : AuthenticatorPBGhost) (auth : ProtoAuthenticator)
    (Frame : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents auth.rootKey))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 200#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx22 : s.readReg64 .x22 = ga.rootKey.cap) (hx24 : s.readReg64 .x24 = ga.rootKey.ptr)
    (hx20 : s.readReg64 .x20 = ga.macKey.cap) (hx21 : s.readReg64 .x21 = ga.macKey.ptr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length)
    (hx13 : s.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 5476#64) s
      (stackAt fsp encoderFromPbStack ∗ ((fsp + 208#64) ↦₆₄ w208) ∗
       vecU8Payload A.repAlloc ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
       A.pool lim st s ∗ Frame)
      (fun s1 P1 =>
        ∃ pa1 : BitVec 64,
          (P1 ⊢
            stackAt fsp encoderFromPbStack ∗ ((fsp + 208#64) ↦₆₄ pa1) ∗
            vecCapPtrDealloc A.repAlloc ga.rootKey.cap ga.rootKey.ptr ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
            A.pool lim (M.stepEvents (authKeyCloneEvents auth.rootKey) st) s1 ∗ Frame) ∧
          s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
          s1.readReg64 .x22 = ga.rootKey.cap ∧ s1.readReg64 .x24 = ga.rootKey.ptr ∧
          s1.readReg64 .x20 = ga.macKey.cap ∧ s1.readReg64 .x21 = ga.macKey.ptr ∧
          s1.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
          s1.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
          s1.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length ∧
          TraceCalleeSaved s1 s0) := by
  have hr_cases : auth.rootKey = [] ∨ 0 < auth.rootKey.length := by cases auth.rootKey <;> simp
  rcases hr_cases with hr_nil | hr_pos
  · have hevs : authKeyCloneEvents auth.rootKey = [] := by simp [authKeyCloneEvents, hr_nil]
    rw [hevs, M.stepEvents_nil]
    rw [hr_nil] at hx26 ⊢
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx26 ⊢
    change s.pc = (blkPl_333).base + 200#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5476#64) s _ _
    refine SepWP.mono
      (P := stackAt fsp encoderFromPbStack ∗ ((fsp + 208#64) ↦₆₄ w208) ∗
        vecU8Payload A.repAlloc ga.rootKey.cap ga.rootKey.ptr [] ∗ A.pool lim st s ∗ Frame)
      (post := fun s1 P1 =>
        (P1 ⊢
          stackAt fsp encoderFromPbStack ∗ ((fsp + 208#64) ↦₆₄ 1#64) ∗
          vecCapPtrDealloc A.repAlloc ga.rootKey.cap ga.rootKey.ptr ∗
          vecU8Payload A.repAlloc 0#64 1#64 [] ∗
          A.pool lim st s1 ∗ Frame) ∧
        s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x22 = ga.rootKey.cap ∧ s1.readReg64 .x24 = ga.rootKey.ptr ∧
        s1.readReg64 .x20 = ga.macKey.cap ∧ s1.readReg64 .x21 = ga.macKey.ptr ∧
        s1.readReg64 .x26 = 0#64 ∧
        s1.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
        s1.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length ∧
        TraceCalleeSaved s1 s0) ?_
      fun s1 P1 _ _ ⟨hP1, hregs⟩ => ⟨1#64, hP1, hregs⟩
    wp_steps_sync_333 ((blkPl_333).base + 5476#64)
    simp only [State.setMem_setMem]
    have hd := vecU8Payload_entails_dealloc A.repAlloc ga.rootKey.cap ga.rootKey.ptr []
    have hn := vecU8Payload_of_nil A.repAlloc
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
    refine entails_pre_st ?_ ?_
    · intro sc hsc; rw [← hsc]
      refine Entails.trans (Entails.of_eq (show _ =
        vecU8Payload A.repAlloc ga.rootKey.cap ga.rootKey.ptr [] ∗ emp ∗
        stackAt fsp encoderFromPbStack ∗ ((fsp + 208#64) ↦₆₄ 1#64) ∗
        A.pool lim st sc ∗ Frame by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hn)) (Entails.of_eq (by sep_ac_rfl))
    · wp_done
  · have hne_nil : auth.rootKey.isEmpty = false := by
      cases h : auth.rootKey with | nil => simp [h] at hr_pos | cons => rfl
    have hevs : authKeyCloneEvents auth.rootKey = rustAllocEvents auth.rootKey.length 1 := by
      simp [authKeyCloneEvents, hne_nil]
    rw [hevs] at hfits ⊢
    refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left
        (vecU8Payload_pos_unpack A.repAlloc ga.rootKey.cap ga.rootKey.ptr auth.rootKey hr_pos)))) ?_
    refine SepWP.weaken_pre (Entails.of_eq (show
          stackAt fsp encoderFromPbStack ∗ ((fsp + 208#64) ↦₆₄ w208) ∗
          (⌜auth.rootKey.length ≤ ga.rootKey.cap.toNat ∧ ga.rootKey.cap.toNat < 2 ^ 63 ∧
            ga.rootKey.ptr ≠ 0#64 ∧ ga.rootKey.cap ≠ 0#64⌝ ∗
           (A.repAlloc.live ga.rootKey.ptr ga.rootKey.cap.toNat 1 ∗ (ga.rootKey.ptr ↦ₛ auth.rootKey) ∗
            memRegion (ga.rootKey.ptr + BitVec.ofNat 64 auth.rootKey.length)
              (ga.rootKey.cap.toNat - auth.rootKey.length))) ∗
          A.pool lim st s ∗ Frame =
        ⌜auth.rootKey.length ≤ ga.rootKey.cap.toNat ∧ ga.rootKey.cap.toNat < 2 ^ 63 ∧
          ga.rootKey.ptr ≠ 0#64 ∧ ga.rootKey.cap ≠ 0#64⌝ ∗
        (memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗ ((fsp + 208#64) ↦₆₄ w208) ∗
         A.live ga.rootKey.ptr ga.rootKey.cap.toNat 1 ∗ (ga.rootKey.ptr ↦ₛ auth.rootKey) ∗
         memRegion (ga.rootKey.ptr + BitVec.ofNat 64 auth.rootKey.length)
           (ga.rootKey.cap.toNat - auth.rootKey.length) ∗
         A.pool lim st s ∗ Frame) by
      rw [stackAt_encoderFromPb_split_allocHook fsp]; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl)) ?_
    apply SepWP.pure_elim
    rintro ⟨hr_le, hr_cap, hptr0, hcap0_ne⟩
    have hr_lt63 : auth.rootKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hr_le hr_cap
    have hr_lt64 : auth.rootKey.length < 2 ^ 64 := by omega
    have hr_toNat : (BitVec.ofNat 64 auth.rootKey.length).toNat = auth.rootKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt64]
    have hr_ne0 : (BitVec.ofNat 64 auth.rootKey.length == 0#64) = false :=
      ofNat_beq_zero_false hr_pos hr_lt64
    have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
    have hrlay : RustLayoutOk auth.rootKey.length 1 := ⟨⟨hr_pos, hpow1, hr_lt63⟩, by decide⟩
    have hshim := hA.shim_ok
    dsimp only [rustAllocShimVmSpec] at hshim
    have halloc := subroutine_ok_allocNoOom_of_budget hA.alloc_ok
    dsimp only [rustCliAllocNoOomSpec] at halloc
    have hmc := hA.memcpy_ok
    dsimp only [allocMemcpyVmSpec] at hmc
    clear hA
    change s.pc = (blkPl_333).base + 200#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5476#64) s _ _
    wp_steps_sync_333 (lsρ spqrRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp_shim : AllocCallPreserved s sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
    wp_steps_sync_333 (lsρ spqrRustAllocSym)
    simp only [State.setMem_setMem]
    wp_call halloc (auth.rootKey.length, 1, st)
    have hoom0 : sf_1.readReg64 .x0 ≠ 0#64 := ‹_›
    have hoom0_beq : (sf_1.readReg64 .x0 == 0#64) = false := beq_false_of_ne hoom0
    have hacp_alloc : AllocCallPreserved s sf_1 :=
      hacp_shim.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_1›)
    wp_steps_sync_333 (lsρ "memcpy")
    simp only [State.setMem_setMem]
    wp_call hmc (sf_1.readReg64 .x0, ga.rootKey.ptr, auth.rootKey)
    have hacp_mc : AllocCallPreserved s sf_2 :=
      hacp_alloc.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_2›)
    have hsp_sf : sf.sp = fsp := ‹sf.sp = s.sp›.trans hsp
    have htr_sf2 : sf_2.trace = s0.trace := hacp_mc.2.1.trans htr.1
    have hvregs_sf2 : calleeSavedVRegs sf_2 = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf_2 = calleeSavedVRegs sf_1›.trans
        (‹calleeSavedVRegs sf_1 = calleeSavedVRegs sf›.trans
          (‹calleeSavedVRegs sf = calleeSavedVRegs s›.trans htr.2))
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
    refine SepWP.mono
      (post := fun s1 P1 =>
        (P1 ⊢
          stackAt fsp encoderFromPbStack ∗ ((fsp + 208#64) ↦₆₄ sf_1.readReg64 .x0) ∗
          vecCapPtrDealloc A.repAlloc ga.rootKey.cap ga.rootKey.ptr ∗
          vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length)
            (sf_1.readReg64 .x0) auth.rootKey ∗
          A.pool lim (M.stepEvents (rustAllocEvents auth.rootKey.length 1) st) s1 ∗ Frame) ∧
        s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x22 = ga.rootKey.cap ∧ s1.readReg64 .x24 = ga.rootKey.ptr ∧
        s1.readReg64 .x20 = ga.macKey.cap ∧ s1.readReg64 .x21 = ga.macKey.ptr ∧
        s1.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
        s1.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
        s1.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length ∧
        TraceCalleeSaved s1 s0) ?_
      fun s1 P1 _ _ ⟨hP1, hregs⟩ => ⟨sf_1.readReg64 .x0, hP1, hregs⟩
    wp_steps_sync_333 ((blkPl_333).base + 5476#64)
    simp only [State.setMem_setMem]
    have hd := vecU8Payload_pos_dealloc A.repAlloc ga.rootKey.cap ga.rootKey.ptr auth.rootKey
      hr_le hr_cap hptr0 hcap0_ne
    have hp := vecU8Payload_pos A.repAlloc (sf_1.readReg64 .x0) auth.rootKey
      hr_pos hr_lt63 hoom0
    refine entails_pre_st ?_ ?_
    · intro sc hsc; rw [← hsc, hsp_sf, stackAt_encoderFromPb_split_allocHook fsp]
      refine Entails.trans (Entails.of_eq (show _ =
        (A.repAlloc.live ga.rootKey.ptr ga.rootKey.cap.toNat 1 ∗ (ga.rootKey.ptr ↦ₛ auth.rootKey) ∗
         memRegion (ga.rootKey.ptr + BitVec.ofNat 64 auth.rootKey.length)
           (ga.rootKey.cap.toNat - auth.rootKey.length)) ∗
        (A.repAlloc.live (sf_1.readReg64 .x0) auth.rootKey.length 1 ∗
         (sf_1.readReg64 .x0 ↦ₛ auth.rootKey)) ∗
        memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
        ((fsp + 208#64) ↦₆₄ sf_1.readReg64 .x0) ∗
        A.pool lim (M.stepEvents (rustAllocEvents auth.rootKey.length 1) st) sc ∗ Frame by
          dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hp)) (Entails.of_eq (by sep_ac_rfl))
    · wp_done

/-- Segment (`+5476 -> +5600`): clone `auth.macKey` under
    `FitsEvents M lim st (authKeyCloneEvents auth.macKey)` with zero OOM/panic branches. -/
theorem states_from_pb_keysUnsampled_step2_5476_5600_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out : BitVec 64)
    (ga : AuthenticatorPBGhost) (auth : ProtoAuthenticator)
    (Frame : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents auth.macKey))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 5476#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx22 : s.readReg64 .x22 = ga.rootKey.cap) (hx24 : s.readReg64 .x24 = ga.rootKey.ptr)
    (hx20 : s.readReg64 .x20 = ga.macKey.cap) (hx21 : s.readReg64 .x21 = ga.macKey.ptr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length)
    (hx13 : s.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 5600#64) s
      (stackAt fsp encoderFromPbStack ∗
       vecU8Payload A.repAlloc ga.macKey.cap ga.macKey.ptr auth.macKey ∗
       A.pool lim st s ∗ Frame)
      (fun s2 P2 =>
        (P2 ⊢
          stackAt fsp encoderFromPbStack ∗
          vecCapPtrDealloc A.repAlloc ga.macKey.cap ga.macKey.ptr ∗
          vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length)
            (s2.readReg64 .x25) auth.macKey ∗
          A.pool lim (M.stepEvents (authKeyCloneEvents auth.macKey) st) s2 ∗ Frame) ∧
        s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧ s2.readReg64 .x23 = fsp + 848#64 ∧
        s2.readReg64 .x22 = ga.rootKey.cap ∧ s2.readReg64 .x24 = ga.rootKey.ptr ∧
        s2.readReg64 .x20 = ga.macKey.cap ∧ s2.readReg64 .x21 = ga.macKey.ptr ∧
        s2.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
        s2.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
        s2.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length ∧
        TraceCalleeSaved s2 s0) := by
  have hm_cases : auth.macKey = [] ∨ 0 < auth.macKey.length := by cases auth.macKey <;> simp
  rcases hm_cases with hm_nil | hm_pos
  · have hevs : authKeyCloneEvents auth.macKey = [] := by simp [authKeyCloneEvents, hm_nil]
    rw [hevs, M.stepEvents_nil]
    rw [hm_nil] at hx13 hx27 ⊢
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx13 hx27 ⊢
    change s.pc = (blkPl_333).base + 5476#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5600#64) s _ _
    refine SepWP.mono
      (post := fun s2 P2 =>
        (P2 ⊢
          stackAt fsp encoderFromPbStack ∗
          vecCapPtrDealloc A.repAlloc ga.macKey.cap ga.macKey.ptr ∗
          vecU8Payload A.repAlloc 0#64 1#64 [] ∗
          A.pool lim st s2 ∗ Frame) ∧
        s2.readReg64 .x25 = 1#64 ∧
        s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧ s2.readReg64 .x23 = fsp + 848#64 ∧
        s2.readReg64 .x22 = ga.rootKey.cap ∧ s2.readReg64 .x24 = ga.rootKey.ptr ∧
        s2.readReg64 .x20 = ga.macKey.cap ∧ s2.readReg64 .x21 = ga.macKey.ptr ∧
        s2.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
        s2.readReg64 .x13 = 0#64 ∧
        s2.readReg64 .x27 = 0#64 ∧
        TraceCalleeSaved s2 s0) ?_
      fun s2 P2 _ _ ⟨hP2, hx25, hregs⟩ => by rw [hx25]; exact ⟨hP2, hregs⟩
    wp_steps_sync_333 ((blkPl_333).base + 5600#64)
    simp only [State.setMem_setMem]
    have hd := vecU8Payload_entails_dealloc A.repAlloc ga.macKey.cap ga.macKey.ptr []
    have hn := vecU8Payload_of_nil A.repAlloc
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
    refine entails_pre_st ?_ ?_
    · intro sc hsc; rw [← hsc]
      refine Entails.trans (Entails.of_eq (show _ =
        vecU8Payload A.repAlloc ga.macKey.cap ga.macKey.ptr [] ∗ emp ∗
        stackAt fsp encoderFromPbStack ∗
        A.pool lim st sc ∗ Frame by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hn)) (Entails.of_eq (by sep_ac_rfl))
    · wp_done
  · have hne_nil : auth.macKey.isEmpty = false := by
      cases h : auth.macKey with | nil => simp [h] at hm_pos | cons => rfl
    have hevs : authKeyCloneEvents auth.macKey = rustAllocEvents auth.macKey.length 1 := by
      simp [authKeyCloneEvents, hne_nil]
    rw [hevs] at hfits ⊢
    refine SepWP.weaken_pre (sepConj_mono_right
      (sepConj_mono_left
        (vecU8Payload_pos_unpack A.repAlloc ga.macKey.cap ga.macKey.ptr auth.macKey hm_pos))) ?_
    refine SepWP.weaken_pre (Entails.of_eq (show
          stackAt fsp encoderFromPbStack ∗
          (⌜auth.macKey.length ≤ ga.macKey.cap.toNat ∧ ga.macKey.cap.toNat < 2 ^ 63 ∧
            ga.macKey.ptr ≠ 0#64 ∧ ga.macKey.cap ≠ 0#64⌝ ∗
           (A.repAlloc.live ga.macKey.ptr ga.macKey.cap.toNat 1 ∗ (ga.macKey.ptr ↦ₛ auth.macKey) ∗
            memRegion (ga.macKey.ptr + BitVec.ofNat 64 auth.macKey.length)
              (ga.macKey.cap.toNat - auth.macKey.length))) ∗
          A.pool lim st s ∗ Frame =
        ⌜auth.macKey.length ≤ ga.macKey.cap.toNat ∧ ga.macKey.cap.toNat < 2 ^ 63 ∧
          ga.macKey.ptr ≠ 0#64 ∧ ga.macKey.cap ≠ 0#64⌝ ∗
        (memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
         A.live ga.macKey.ptr ga.macKey.cap.toNat 1 ∗ (ga.macKey.ptr ↦ₛ auth.macKey) ∗
         memRegion (ga.macKey.ptr + BitVec.ofNat 64 auth.macKey.length)
           (ga.macKey.cap.toNat - auth.macKey.length) ∗
         A.pool lim st s ∗ Frame) by
      rw [stackAt_encoderFromPb_split_allocHook fsp]; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl)) ?_
    apply SepWP.pure_elim
    rintro ⟨hm_le, hm_cap, hptr1, hcap1_ne⟩
    have hm_lt63 : auth.macKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hm_le hm_cap
    have hm_lt64 : auth.macKey.length < 2 ^ 64 := by omega
    have hm_toNat : (BitVec.ofNat 64 auth.macKey.length).toNat = auth.macKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm_lt64]
    have hm_ne0 : (BitVec.ofNat 64 auth.macKey.length == 0#64) = false :=
      ofNat_beq_zero_false hm_pos hm_lt64
    have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
    have hrlay : RustLayoutOk auth.macKey.length 1 := ⟨⟨hm_pos, hpow1, hm_lt63⟩, by decide⟩
    have hshim := hA.shim_ok
    dsimp only [rustAllocShimVmSpec] at hshim
    have halloc := subroutine_ok_allocNoOom_of_budget hA.alloc_ok
    dsimp only [rustCliAllocNoOomSpec] at halloc
    have hmc := hA.memcpy_ok
    dsimp only [allocMemcpyVmSpec] at hmc
    clear hA
    change s.pc = (blkPl_333).base + 5476#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5600#64) s _ _
    wp_steps_sync_333 (lsρ spqrRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp_shim : AllocCallPreserved s sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
    wp_steps_sync_333 (lsρ spqrRustAllocSym)
    simp only [State.setMem_setMem]
    wp_call halloc (auth.macKey.length, 1, st)
    have hoom1 : sf_1.readReg64 .x0 ≠ 0#64 := ‹_›
    have hoom1_beq : (sf_1.readReg64 .x0 == 0#64) = false := beq_false_of_ne hoom1
    have hacp_alloc : AllocCallPreserved s sf_1 :=
      hacp_shim.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_1›)
    wp_steps_sync_333 (lsρ "memcpy")
    simp only [State.setMem_setMem]
    wp_call hmc (sf_1.readReg64 .x0, ga.macKey.ptr, auth.macKey)
    have hacp_mc : AllocCallPreserved s sf_2 :=
      hacp_alloc.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_2›)
    have hsp_sf : sf.sp = fsp := ‹sf.sp = s.sp›.trans hsp
    have htr_sf2 : sf_2.trace = s0.trace := hacp_mc.2.1.trans htr.1
    have hvregs_sf2 : calleeSavedVRegs sf_2 = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf_2 = calleeSavedVRegs sf_1›.trans
        (‹calleeSavedVRegs sf_1 = calleeSavedVRegs sf›.trans
          (‹calleeSavedVRegs sf = calleeSavedVRegs s›.trans htr.2))
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
    refine SepWP.mono
      (post := fun s2 P2 =>
        (P2 ⊢
          stackAt fsp encoderFromPbStack ∗
          vecCapPtrDealloc A.repAlloc ga.macKey.cap ga.macKey.ptr ∗
          vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length)
            (sf_1.readReg64 .x0) auth.macKey ∗
          A.pool lim (M.stepEvents (rustAllocEvents auth.macKey.length 1) st) s2 ∗ Frame) ∧
        s2.readReg64 .x25 = sf_1.readReg64 .x0 ∧
        s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧ s2.readReg64 .x23 = fsp + 848#64 ∧
        s2.readReg64 .x22 = ga.rootKey.cap ∧ s2.readReg64 .x24 = ga.rootKey.ptr ∧
        s2.readReg64 .x20 = ga.macKey.cap ∧ s2.readReg64 .x21 = ga.macKey.ptr ∧
        s2.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
        s2.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
        s2.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length ∧
        TraceCalleeSaved s2 s0) ?_
      fun s2 P2 _ _ ⟨hP2, hx25, hregs⟩ => by rw [hx25]; exact ⟨hP2, hregs⟩
    wp_steps_sync_333 ((blkPl_333).base + 5600#64)
    simp only [State.setMem_setMem]
    have hd := vecU8Payload_pos_dealloc A.repAlloc ga.macKey.cap ga.macKey.ptr auth.macKey
      hm_le hm_cap hptr1 hcap1_ne
    have hp := vecU8Payload_pos A.repAlloc (sf_1.readReg64 .x0) auth.macKey
      hm_pos hm_lt63 hoom1
    refine entails_pre_st ?_ ?_
    · intro sc hsc; rw [← hsc, hsp_sf, stackAt_encoderFromPb_split_allocHook fsp]
      refine Entails.trans (Entails.of_eq (show _ =
        (A.repAlloc.live ga.macKey.ptr ga.macKey.cap.toNat 1 ∗ (ga.macKey.ptr ↦ₛ auth.macKey) ∗
         memRegion (ga.macKey.ptr + BitVec.ofNat 64 auth.macKey.length)
           (ga.macKey.cap.toNat - auth.macKey.length)) ∗
        (A.repAlloc.live (sf_1.readReg64 .x0) auth.macKey.length 1 ∗
         (sf_1.readReg64 .x0 ↦ₛ auth.macKey)) ∗
        memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
        A.pool lim (M.stepEvents (rustAllocEvents auth.macKey.length 1) st) sc ∗ Frame by
          dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hp)) (Entails.of_eq (by sep_ac_rfl))
    · wp_done

/-- Segment (`+5600 -> +8176 -> ret`): drop input `ga.rootKey` and `ga.macKey` buffers
    (`FreeOnlyEvs`), materialize `States.from_pb` at `out`, and run the shared `Ok` epilogue. -/
theorem states_from_pb_keysUnsampled_step3_5600_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out pbA ep pa1 : BitVec 64)
    (ga : AuthenticatorPBGhost) (auth : ProtoAuthenticator)
    (hr_lt63 : auth.rootKey.length < 2 ^ 63)
    (halign : (s0.sp &&& 15#64 == 0#64) = true) (hfsp : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 5600#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx22 : s.readReg64 .x22 = ga.rootKey.cap) (hx24 : s.readReg64 .x24 = ga.rootKey.ptr)
    (hx20 : s.readReg64 .x20 = ga.macKey.cap) (hx21 : s.readReg64 .x21 = ga.macKey.ptr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length)
    (hx13 : s.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt fsp encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       memRegion fsp 152 ∗ ((fsp + 152#64) ↦₆₄ ep) ∗ memRegion (fsp + 160#64) 48 ∗
       ((fsp + 208#64) ↦₆₄ pa1) ∗ memRegion (fsp + 216#64) 2088 ∗ statesFromPbSavedCells s0 ∗
       vecCapPtrDealloc A.repAlloc ga.rootKey.cap ga.rootKey.ptr ∗
       vecCapPtrDealloc A.repAlloc ga.macKey.cap ga.macKey.ptr ∗
       vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
       vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) (s.readReg64 .x25) auth.macKey ∗
       memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
       A.pool lim st s)
      (fun sf Pf =>
        ∃ evs_free : List AllocEvent,
          FreeOnlyEvs evs_free ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (CryptoVerification.LibsignalSpqrV1.States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.keysUnsampled { uc := some { auth := some auth, epoch := ep } }) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs_free st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp ▸ sp_sub_2400_align s0.sp halign
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ DefsBudget.spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hA.dealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hr_lt64 : auth.rootKey.length < 2 ^ 64 := by omega
  have hr_toNat : (BitVec.ofNat 64 auth.rootKey.length).toNat = auth.rootKey.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt64]
  have hcmn_false : (BitVec.ofNat 64 auth.rootKey.length + 1#64 == 0#64) = false :=
    Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false (by rw [hr_toNat]; exact hr_lt63))
  rw [stackAt_encoderFromPb_split_allocHook fsp]
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 5624#64)
    (P_evs := fun evs1 s1 =>
      memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
      memRegion out chunkedStatesSize ∗ memRegion fsp 152 ∗ ((fsp + 152#64) ↦₆₄ ep) ∗
      memRegion (fsp + 160#64) 48 ∗ ((fsp + 208#64) ↦₆₄ pa1) ∗ memRegion (fsp + 216#64) 2088 ∗
      statesFromPbSavedCells s0 ∗ vecCapPtrDealloc A.repAlloc ga.macKey.cap ga.macKey.ptr ∗
      vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
      vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) (s.readReg64 .x25) auth.macKey ∗
      memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
      A.pool lim (M.stepEvents evs1 st) s1)
    (Q := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
      s1.readReg64 .x20 = ga.macKey.cap ∧ s1.readReg64 .x21 = ga.macKey.ptr ∧
      s1.readReg64 .x25 = s.readReg64 .x25 ∧
      s1.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
      s1.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
      s1.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length ∧ TraceCalleeSaved s1 s0) ?_ ?_
  · clear hfsp
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
    change s.pc = (blkPl_333).base + 5600#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5624#64) s _ _
    by_cases hc1 : (ga.rootKey.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 5624#64); simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_; wp_done
    · apply sepWP_evs_dealloc ga.rootKey.cap.toNat 1
      wp_steps_sync_333 (lsρ DefsBudget.spqrRustDeallocSym); simp only [State.setMem_setMem]
      wp_call hdealloc_fo (ga.rootKey.ptr, ga.rootKey.cap.toNat, 1, st)
      have hacp1 : AllocCallPreserved s sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have htr_sf : sf.trace = s0.trace := hacp1.2.1.trans htr.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s›.trans htr.2
      wp_steps_sync_333 ((blkPl_333).base + 5624#64); simp only [State.setMem_setMem]
      refine align_pre_st (by rw [hsp]; sep_ac_rfl) ?_; wp_done
  · intro evs1 s1 hevs1 hpc1 hrun1
      ⟨hsp1, hx19_1, hx23_1, hx20_1, hx21_1, hx25_1, hx26_1, hx13_1, hx27_1, htr1⟩
    let st1 := M.stepEvents evs1 st
    refine seq_clean_evs
      (mid := lsmpl.base 333 + 5648#64)
      (P_evs := fun evs2 s2 =>
        memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
        memRegion out chunkedStatesSize ∗ memRegion fsp 152 ∗ ((fsp + 152#64) ↦₆₄ ep) ∗
        memRegion (fsp + 160#64) 48 ∗ ((fsp + 208#64) ↦₆₄ pa1) ∗ memRegion (fsp + 216#64) 2088 ∗
        statesFromPbSavedCells s0 ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) (s.readReg64 .x25) auth.macKey ∗
        memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
        A.pool lim (M.stepEvents evs2 st1) s2)
      (Q := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧ s2.readReg64 .x23 = fsp + 848#64 ∧
        s2.readReg64 .x25 = s.readReg64 .x25 ∧
        s2.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
        s2.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧ TraceCalleeSaved s2 s0) ?_ ?_
    · clear hfsp
      dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
      change s1.pc = (blkPl_333).base + 5624#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 5648#64) s1 _ _
      by_cases hc2 : (ga.macKey.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        wp_steps_sync_333 ((blkPl_333).base + 5648#64); simp only [State.setMem_setMem]
        refine align_pre_st (by sep_ac_rfl) ?_; wp_done
      · apply sepWP_evs_dealloc ga.macKey.cap.toNat 1
        wp_steps_sync_333 (lsρ DefsBudget.spqrRustDeallocSym); simp only [State.setMem_setMem]
        wp_call hdealloc_fo (ga.macKey.ptr, ga.macKey.cap.toNat, 1, st1)
        have hacp2 : AllocCallPreserved s1 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        have htr_sf : sf.trace = s0.trace := hacp2.2.1.trans htr1.1
        have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
          ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htr1.2
        wp_steps_sync_333 ((blkPl_333).base + 5648#64); simp only [State.setMem_setMem]
        refine align_pre_st (by rw [hsp1]; sep_ac_rfl) ?_; wp_done
    · intro evs2 s2 hevs2 hpc2 hrun2 ⟨hsp2, hx19_2, hx23_2, hx25_2, hx26_2, hx13_2, htr2⟩
      let st2 := M.stepEvents evs2 st1
      refine seq_clean_st
        (mid := lsmpl.base 333 + 8176#64)
        (P_mid := fun s3 =>
          stackAt fsp encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
          memRegion fsp 208 ∗ ((fsp + 208#64) ↦₆₄ pa1) ∗ memRegion (fsp + 216#64) 2088 ∗
          statesFromPbSavedCells s0 ∗
          (vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
           vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) (s.readReg64 .x25) auth.macKey ∗
           memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) ∗
          A.pool lim st2 s3)
        (Q := fun s3 => s3.sp = fsp ∧ s3.readReg64 .x19 = out ∧ s3.readReg64 .x23 = fsp + 848#64 ∧
          s3.readReg64 .x8 = 2#64 ∧ s3.readReg64 .x15 = BitVec.ofNat 64 auth.rootKey.length ∧
          s3.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
          s3.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
          s3.readReg64 .x25 = s.readReg64 .x25 ∧
          s3.readReg64 .x30 = BitVec.ofNat 64 auth.macKey.length ∧
          s3.readReg64 .x9 = ep ∧ TraceCalleeSaved s3 s0) ?_ ?_
      · clear hfsp
        change s2.pc = (blkPl_333).base + 5648#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 8176#64) s2 _ _
        wp_steps_sync_333 ((blkPl_333).base + 8176#64)
        simp only [State.setMem_setMem]
        refine entails_pre_st ?_ ?_
        · intro sc hsc; rw [← hsc]
          rw [stackAt_encoderFromPb_split_allocHook fsp]
          have h208 := memRegion_152_8_48_entails_208 fsp ep
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion fsp 152 ∗ ((fsp + 152#64) ↦₆₄ ep) ∗ memRegion (fsp + 160#64) 48) ∗
            memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
            memRegion out chunkedStatesSize ∗ ((fsp + 208#64) ↦₆₄ pa1) ∗
            memRegion (fsp + 216#64) 2088 ∗ statesFromPbSavedCells s0 ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) (s.readReg64 .x25) auth.macKey ∗
            memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
            A.pool lim st2 sc by sep_ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left h208) (Entails.of_eq (by sep_ac_rfl))
        · wp_done
      · intro s3 hpc3 hrun3
          ⟨hsp3, hx19_3, hx23_3, hx8_3, hx15_3, hx20_3, hx13_3, hx25_3, hx30_3, hx9_3, htr3⟩
        subst hfsp
        have hep := states_from_pb_epilogue_8176_keysUnsampled_placed A lim st2 hA.memcpy_ok
          s0 s3 out pa1
          (vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
           vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) (s.readReg64 .x25) auth.macKey ∗
           memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
          halign hpc3 hrun3 hsp3 hx19_3 hx23_3 htr3
        rw [hx8_3, hx15_3, hx20_3, hx13_3, hx25_3, hx30_3, hx9_3] at hep
        refine SepWP.mono hep fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f, _⟩ => ?_
        refine ⟨evs1 ++ evs2, LibsignalBinary.Heap.FreeOnlyEvs.append hevs1 hevs2, ?_, hsp_f, hcc_f, htr_f⟩
        have hst_eq : st2 = M.stepEvents (evs1 ++ evs2) st := by
          dsimp only [st2, st1]; rw [M.stepEvents_append]
        rw [← hst_eq]
        refine Entails.trans hPf ?_
        rw [states_from_pb_keysUnsampled_some_eq]
        dsimp only [resultChunkedStatesAt, chunkedStatesAt, chunkedKeysUnsampledAt,
          unchunkedKeysUnsampledAt, CryptoVerification.LibsignalSpqrV1.Authenticator.fromPb]
        have hauth := authenticatorAt_8_pack A.repAlloc out
          (BitVec.ofNat 64 auth.rootKey.length) pa1
          (BitVec.ofNat 64 auth.macKey.length) (s.readReg64 .x25)
          { rootKey := auth.rootKey, macKey := auth.macKey }
        dsimp only at hauth
        have h56 : (out + 8#64) + 48#64 = out + 56#64 := by bv_omega
        rw [h56]
        refine Entails.trans (Entails.of_eq (show _ =
          (((out + 8#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗ ((out + 16#64) ↦₆₄ pa1) ∗
           ((out + 24#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
           ((out + 32#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
           ((out + 40#64) ↦₆₄ s.readReg64 .x25) ∗
           ((out + 48#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
           vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
           vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length)
             (s.readReg64 .x25) auth.macKey) ∗
          (out ↦₆₄ 2#64) ∗ ((out + 56#64) ↦₆₄ ep) ∗ memRegion (out + 64#64) 864 ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
          A.pool lim st2 sf ∗ stackAt s0.sp statesFromPbStack by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hauth) (Entails.of_eq (by sep_ac_rfl))

/-! ## Complete Success Path (`uc = some { auth := some auth, .. }`) & Variant-0 `+156` Theorem -/

/-- Complete total-correctness (`SepWP`) theorem for Variant 0 (`KeysUnsampled`, `+156`) on
    `uc = some { auth := some auth, epoch := ep }`. -/
theorem states_from_pb_keysUnsampled_some_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out pbA ep : BitVec 64)
    (auth : ProtoAuthenticator)
    (hfits : FitsEnv M lim st (AuthFromPbEnv auth))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 156#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000000#64) ∗
        optProtoAuthenticatorAt A.repAlloc (pbA + 8#64) (some auth) ∗
        ((pbA + 56#64) ↦₆₄ ep) ∗ memRegion (pbA + 64#64) 160 ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          KeysUnsampledFromPbEnv { uc := some { auth := some auth, epoch := ep } } evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (CryptoVerification.LibsignalSpqrV1.States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.keysUnsampled { uc := some { auth := some auth, epoch := ep } }) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    sp_sub_2400_align s0.sp hsp0_align
  have hfit_all : FitsEvents M lim st (authFromPbEvents auth) :=
    fitsEvents_of_fitsEnv_authFromPbEnv hfits
  obtain ⟨hfit_r, hfit_m⟩ :=
    (fitsEvents_append M lim (authKeyCloneEvents auth.rootKey) (authKeyCloneEvents auth.macKey) st).mp hfit_all
  rw [show optProtoAuthenticatorAt A.repAlloc (pbA + 8#64) (some auth) =
    ∃∗ ga : AuthenticatorPBGhost, authenticatorPBPinnedAt A.repAlloc ga (pbA + 8#64) auth from
    authenticatorPBAt_eq_exists_pinned A.repAlloc (pbA + 8#64) auth]
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (memRegion_2304_split_152_208 (s0.sp - 2400#64)))) ?_
  refine SepWP.weaken_pre (Entails.of_eq (by
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; rfl)) ?_
  apply ProofLib.SepWP.exists_left; intro ga
  apply ProofLib.SepWP.exists_left; intro w208
  apply ProofLib.SepWP.exists_left; intro w152
  have hcap_ext : authenticatorPBPinnedAt A.repAlloc ga (pbA + 8#64) auth ⊢
      ⌜ga.rootKey.cap.toNat < 2 ^ 63⌝ ∗ authenticatorPBPinnedAt A.repAlloc ga (pbA + 8#64) auth := by
    rw [authenticatorPBPinnedAt_8_eq_cap_tail]
    have h1 : vecU8Payload A.repAlloc ga.rootKey.cap ga.rootKey.ptr auth.rootKey ⊢
        ⌜ga.rootKey.cap.toNat < 2 ^ 63⌝ ∗ vecU8Payload A.repAlloc ga.rootKey.cap ga.rootKey.ptr auth.rootKey := by
      unfold vecU8Payload; apply Entails.pure_left; intro ⟨hle, hlt, hne⟩
      exact Entails.pure_right hlt (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))
    exact Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h1))))
      (Entails.of_eq (by sep_ac_rfl))
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 152 ∗
        ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
        ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗ memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000000#64) ∗
        authenticatorPBPinnedAt A.repAlloc ga (pbA + 8#64) auth ∗
        ((pbA + 56#64) ↦₆₄ ep) ∗ memRegion (pbA + 64#64) 160 ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1 =
      authenticatorPBPinnedAt A.repAlloc ga (pbA + 8#64) auth ∗
      ((pbA ↦₆₄ 0x8000000000000000#64) ∗ ((pbA + 56#64) ↦₆₄ ep) ∗ memRegion (pbA + 64#64) 160 ∗
       ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗
       (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
        memRegion (s0.sp - 2400#64) 152 ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
        ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗ memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗
        statesFromPbSavedCells s0 ∗ statesFromPbJumpTablePlacedAt) ∗
       A.pool lim st s1) by sep_ac_rfl))
    (Entails.trans (sepConj_mono_left hcap_ext) (Entails.of_eq (show _ =
      ⌜ga.rootKey.cap.toNat < 2 ^ 63⌝ ∗
      ((pbA ↦₆₄ 0x8000000000000000#64) ∗
       authenticatorPBPinnedAt A.repAlloc ga (pbA + 8#64) auth ∗
       ((pbA + 56#64) ↦₆₄ ep) ∗ memRegion (pbA + 64#64) 160 ∗
       ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗
       (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
        memRegion (s0.sp - 2400#64) 152 ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
        ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗ memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗
        statesFromPbSavedCells s0 ∗ statesFromPbJumpTablePlacedAt) ∗
       A.pool lim st s1) by sep_ac_rfl)))) ?_
  apply SepWP.pure_elim; intro hcap0
  refine SepWP.seq
    (states_from_pb_keysUnsampled_step0_156_200_placed_budget A lim st (ext := ext)
      s1 (s0.sp - 2400#64) out pbA ep w152 ga auth
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       memRegion (s0.sp - 2400#64) 152 ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
       ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗ memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗
       statesFromPbSavedCells s0 ∗ statesFromPbJumpTablePlacedAt)
      hcap0 hfsp_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx27_1) ?_
  intro s2 P2 hpc2 hrun2
    ⟨hP2, hsp2, hx19_2, hx23_2, hx22_2, hx24_2, hx20_2, hx21_2, hx26_2, hx13_2, hx27_2, htr2_s1, _⟩
  have htr2 : TraceCalleeSaved s2 s0 := htr2_s1.trans htr1
  refine SepWP.weaken_pre (Entails.trans hP2
    (sepConj_mono_right (sepConj_mono_left
      (vecU8Payload_extract_len_lt63 A.repAlloc ga.rootKey.cap ga.rootKey.ptr auth.rootKey)))) ?_
  rw [show ((s0.sp - 2400#64 + 152#64) ↦₆₄ ep) ∗
        (⌜auth.rootKey.length < 2 ^ 63⌝ ∗
          vecU8Payload A.repAlloc ga.rootKey.cap ga.rootKey.ptr auth.rootKey) ∗
        vecU8Payload A.repAlloc ga.macKey.cap ga.macKey.ptr auth.macKey ∗
        memRegion pbA optProtoInnerStateSize ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
         memRegion (s0.sp - 2400#64) 152 ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
         ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗ memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗
         statesFromPbSavedCells s0 ∗ statesFromPbJumpTablePlacedAt) ∗
        A.pool lim st s2 =
      ⌜auth.rootKey.length < 2 ^ 63⌝ ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗
       vecU8Payload A.repAlloc ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
       A.pool lim st s2 ∗
       (vecU8Payload A.repAlloc ga.macKey.cap ga.macKey.ptr auth.macKey ∗
        memRegion out chunkedStatesSize ∗ memRegion (s0.sp - 2400#64) 152 ∗
        ((s0.sp - 2400#64 + 152#64) ↦₆₄ ep) ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
        memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗ statesFromPbSavedCells s0 ∗
        memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)) by sep_ac_rfl]
  apply SepWP.pure_elim; intro hr_lt63
  refine SepWP.seq
    (states_from_pb_keysUnsampled_step1_200_5476_placed hA st s0 s2 (s0.sp - 2400#64) out w208 ga auth
      (vecU8Payload A.repAlloc ga.macKey.cap ga.macKey.ptr auth.macKey ∗
       memRegion out chunkedStatesSize ∗ memRegion (s0.sp - 2400#64) 152 ∗
       ((s0.sp - 2400#64 + 152#64) ↦₆₄ ep) ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
       memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗ statesFromPbSavedCells s0 ∗
       memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
      hfit_r hfsp_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx22_2 hx24_2 hx20_2 hx21_2
      hx26_2 hx13_2 hx27_2 htr2) ?_
  rintro s3 P3 hpc3 hrun3
    ⟨pa1, hP3, hsp3, hx19_3, hx23_3, hx22_3, hx24_3, hx20_3, hx21_3, hx26_3, hx13_3, hx27_3, htr3⟩
  let st_r := M.stepEvents (authKeyCloneEvents auth.rootKey) st
  refine SepWP.weaken_pre (Entails.trans hP3 (Entails.of_eq (show _ =
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
    vecU8Payload A.repAlloc ga.macKey.cap ga.macKey.ptr auth.macKey ∗
    A.pool lim st_r s3 ∗
    (memRegion out chunkedStatesSize ∗ memRegion (s0.sp - 2400#64) 152 ∗
     ((s0.sp - 2400#64 + 152#64) ↦₆₄ ep) ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
     ((s0.sp - 2400#64 + 208#64) ↦₆₄ pa1) ∗ memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗
     statesFromPbSavedCells s0 ∗ vecCapPtrDealloc A.repAlloc ga.rootKey.cap ga.rootKey.ptr ∗
     vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) by sep_ac_rfl))) ?_
  refine SepWP.seq
    (states_from_pb_keysUnsampled_step2_5476_5600_placed hA st_r s0 s3 (s0.sp - 2400#64) out ga auth
      (memRegion out chunkedStatesSize ∗ memRegion (s0.sp - 2400#64) 152 ∗
       ((s0.sp - 2400#64 + 152#64) ↦₆₄ ep) ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
       ((s0.sp - 2400#64 + 208#64) ↦₆₄ pa1) ∗ memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗
       statesFromPbSavedCells s0 ∗ vecCapPtrDealloc A.repAlloc ga.rootKey.cap ga.rootKey.ptr ∗
       vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
       memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
      hfit_m hfsp_align hpc3 hrun3 hsp3 hx19_3 hx23_3 hx22_3 hx24_3 hx20_3 hx21_3
      hx26_3 hx13_3 hx27_3 htr3) ?_
  intro s4 P4 hpc4 hrun4
    ⟨hP4, hsp4, hx19_4, hx23_4, hx22_4, hx24_4, hx20_4, hx21_4, hx26_4, hx13_4, hx27_4, htr4⟩
  have hst_auth : M.stepEvents (authKeyCloneEvents auth.macKey) st_r =
      M.stepEvents (authFromPbEvents auth) st := by
    dsimp only [st_r, authFromPbEvents]; rw [M.stepEvents_append]
  refine SepWP.weaken_pre (Entails.trans hP4 (Entails.of_eq (show _ =
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
    memRegion (s0.sp - 2400#64) 152 ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ ep) ∗
    memRegion (s0.sp - 2400#64 + 160#64) 48 ∗ ((s0.sp - 2400#64 + 208#64) ↦₆₄ pa1) ∗
    memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗ statesFromPbSavedCells s0 ∗
    vecCapPtrDealloc A.repAlloc ga.rootKey.cap ga.rootKey.ptr ∗
    vecCapPtrDealloc A.repAlloc ga.macKey.cap ga.macKey.ptr ∗
    vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
    vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) (s4.readReg64 .x25) auth.macKey ∗
    memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
    A.pool lim (M.stepEvents (authFromPbEvents auth) st) s4 by rw [hst_auth]; sep_ac_rfl))) ?_
  have hstep3 := states_from_pb_keysUnsampled_step3_5600_ret_placed (F := F)
    hA (M.stepEvents (authFromPbEvents auth) st) s0 s4 (s0.sp - 2400#64) out pbA ep pa1
    ga auth hr_lt63 hsp0_align rfl hpc4 hrun4 hsp4 hx19_4 hx23_4
    hx22_4 hx24_4 hx20_4 hx21_4 hx26_4 hx13_4 hx27_4 htr4
  refine SepWP.mono hstep3 fun sf Pf _ _ ⟨evs_free, hfree, hPf, hsp_f, hcc_f, htr_f⟩ => ?_
  refine ⟨⟨authFromPbEvents auth ++ evs_free, ⟨evs_free, hfree, rfl⟩, ?_⟩, hsp_f, hcc_f, htr_f⟩
  rw [M.stepEvents_append]
  exact hPf

/-- Budget-threaded Variant-0 (`KeysUnsampled`, `+156 -> ret`) total-correctness `SepWP` theorem
    across all `uc` / `auth` cases (`none`, `some { auth := none }`, `some { auth := some _ }`). -/
theorem states_from_pb_keysUnsampled_156_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out pbA : BitVec 64)
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysUnsampled)
    (hfits : FitsEnv M lim st (KeysUnsampledFromPbAllocEnv s))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 156#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A.repAlloc pbA (some (.keysUnsampled s)) ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          KeysUnsampledFromPbEnv s evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (CryptoVerification.LibsignalSpqrV1.States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.keysUnsampled s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  cases s with | mk uc =>
  cases uc with
  | none =>
    dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedKeysUnsampledAt,
      optProtoUnchunkedKeysUnsampledAt]
    have h16 : (pbA + 8#64) + 8#64 = pbA + 16#64 := by bv_omega
    rw [h16]; simp only [sepConj_assoc]
    have hstep := states_from_pb_keysUnsampled_uc_none_placed A lim st (F := F) (ext := ext)
      s0 s1 out pbA hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
    refine SepWP.mono hstep fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f, _⟩ =>
      ⟨⟨[], rfl, hPf⟩, hsp_f, hcc_f, htr_f⟩
  | some uc =>
    cases uc with | mk ep auth =>
    cases auth with
    | none =>
      dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedKeysUnsampledAt,
        optProtoUnchunkedKeysUnsampledAt, protoUnchunkedKeysUnsampledAt, optProtoAuthenticatorAt]
      have h16 : (pbA + 8#64) + 8#64 = pbA + 16#64 := by bv_omega
      have h56 : (pbA + 8#64) + 48#64 = pbA + 56#64 := by bv_omega
      rw [h16, h56]; simp only [sepConj_assoc]
      have hstep := states_from_pb_keysUnsampled_auth_none_placed A lim st (F := F) (ext := ext)
        s0 s1 out pbA ep hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
      refine SepWP.mono hstep fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f, _⟩ =>
        ⟨⟨[], rfl, hPf⟩, hsp_f, hcc_f, htr_f⟩
    | some auth =>
      rw [optProtoInnerStateAt_keysUnsampled_some_eq]; simp only [sepConj_assoc]
      exact states_from_pb_keysUnsampled_some_placed hA st s0 s1 out pbA ep auth
        hfits hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx27_1 htr1

/-! ## Complete `subroutine_ok` Theorems for Variant 0 (`KeysUnsampled`) -/

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (StatesFromPbVariantStepPlaced
   sfpProof_tagged_ok_of_step_placed_raw
   sfpProof_tagged_ok_of_step_placed)

/-- Envelope-parametric `subroutine_ok` for Variant 0 (`InnerState.keysUnsampled`) under any `Env`
    with `KeysUnsampledFromPbEnv s ⊆ Env` and `FitsEnv Env → FitsEnv (KeysUnsampledFromPbAllocEnv s)`. -/
theorem states_from_pb_keysUnsampled_placed_ok_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysUnsampled)
    (halloc_fit : ∀ st : M.σ, FitsEnv M lim st Env →
      FitsEnv M lim st (KeysUnsampledFromPbAllocEnv s))
    (hsub : ∀ (st : M.σ) {evs : List AllocEvent},
      FitsEnv M lim st Env → KeysUnsampledFromPbEnv s evs → Env evs) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F
        { innerState := some (.keysUnsampled s) } Env) := by
  refine sfpProof_tagged_ok_of_step_placed_raw CryptoVerification.SpqrV1.States.FromPb.TaggedVariantDispatch.keysUnsampled
    (Tail := fun pbA => protoChunkedKeysUnsampledAt A.repAlloc (pbA + 8#64) s ∗ memRegion (pbA + 64#64) 160)
    (fun _ => rfl) ?_
  intro _ st s0 s1 out pbA R hfits hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx27_1 htr1
  refine DefsBudget.sepWPp_of_states_exit_placed st s0 s1 out pbA
    { innerState := some (.keysUnsampled s) } Env _ R ?_
  have h156 := states_from_pb_keysUnsampled_156_placed (F := F) hA st s0 s1 out pbA s
    (halloc_fit st hfits) hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx27_1 htr1
  refine SepWP.mono h156 fun sf Pf _ _ ⟨⟨evs, hevs, hPf⟩, hsp_f, hcc_f, htr_f⟩ => ?_
  exact ⟨⟨evs, hsub st hfits hevs, hPf⟩, hsp_f, hcc_f, htr_f⟩

/-- `subroutine_ok` for Variant 0 (`InnerState.keysUnsampled`) under its tight envelope
    `KeysUnsampledFromPbEnv s`. -/
theorem states_from_pb_keysUnsampled_placed_ok_tight [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysUnsampled) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F
        { innerState := some (.keysUnsampled s) } (KeysUnsampledFromPbEnv s)) :=
  states_from_pb_keysUnsampled_placed_ok_of_env hA s
    (fun _ h => fitsEnv_alloc_of_keysUnsampledEnv h)
    (fun _ _ _ h => h)

/-- `subroutine_ok` for Variant 0 (`InnerState.keysUnsampled`) under the uniform
    `statesFromPbVariantPlacedSpec` (`StatesFromPbEnv`). -/
theorem states_from_pb_keysUnsampled_placed_ok_raw [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysUnsampled) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (DefsBudget.statesFromPbVariantPlacedSpec M A lim F { innerState := some (.keysUnsampled s) }) :=
  states_from_pb_keysUnsampled_placed_ok_of_env hA s
    (fun _ h => fitsEnv_alloc_of_statesFromPbEnv s h)
    (fun _ _ hfits hevs => keysUnsampledFromPbEnv_sub_statesFromPbEnv s hfits hevs)

/-- `subroutine_ok` for Variant 0 (`InnerState.keysUnsampled`) with `withLsCodeLoaded`. -/
theorem states_from_pb_keysUnsampled_ok_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysUnsampled) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F { innerState := some (.keysUnsampled s) })) :=
  subroutine_ok_withLsCodeLoaded_of_plain (states_from_pb_keysUnsampled_placed_ok_raw hA s)

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudget
